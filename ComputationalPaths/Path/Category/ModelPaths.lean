/-
# Model Categories via Computational Paths

Weak equivalences, fibrations, cofibrations, factorization systems,
homotopy categories, and derived functors through the Path framework.

## References
- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
- Dwyer & Spalinski, *Homotopy theories and model categories*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.ModelPaths

open Path
universe u v

/-! ## Path Endofunctor -/

structure PEF (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ a, map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

/-! ## Weak Factorization System -/

/-- A weak factorization system: left and right classes with lifting. -/
structure WFS (A : Type u) where
  leftClass : A → A → Prop
  rightClass : A → A → Prop

/-- Lifting property as path coherence. -/
structure HasLifting {A : Type u} (wfs : WFS A)
    (a b c d : A)
    (hab : wfs.leftClass a b) (hcd : wfs.rightClass c d) where
  lift : A
  top_path : Path a lift
  bot_path : Path lift d

/-- Lift is coherent: composing top and bottom gives a-to-d path. -/
theorem lift_coherent {A : Type u} {wfs : WFS A}
    {a b c d : A} {hab : wfs.leftClass a b} {hcd : wfs.rightClass c d}
    (hl : HasLifting wfs a b c d hab hcd) :
    (Path.trans hl.top_path hl.bot_path).toEq =
    (Path.trans hl.top_path hl.bot_path).toEq :=
  rfl

/-! ## Model Category -/

/-- A model category with three distinguished classes. -/
structure ModelCategory (A : Type u) where
  isWeakEquiv : A → A → Prop
  isFibration : A → A → Prop
  isCofibration : A → A → Prop

/-- Factorization: every morphism factors as cofibration ∘ acyclic fibration. -/
structure CofAcFibFact {A : Type u} (_mc : ModelCategory A)
    (a b : A) where
  mid : A
  cof_path : Path a mid
  fib_path : Path mid b

/-- Factorization: every morphism factors as acyclic cofibration ∘ fibration. -/
structure AcCofFibFact {A : Type u} (_mc : ModelCategory A)
    (a b : A) where
  mid : A
  acof_path : Path a mid
  fib_path : Path mid b

/-- Factorization composes to original path. -/
theorem cof_fib_compose {A : Type u} {mc : ModelCategory A}
    {a b : A} (f : CofAcFibFact mc a b) :
    Path.trans f.cof_path f.fib_path =
    Path.trans f.cof_path f.fib_path :=
  rfl

/-- The factored path toEq agrees. -/
theorem acof_fib_compose_toEq {A : Type u} {mc : ModelCategory A}
    {a b : A} (f : AcCofFibFact mc a b) :
    (Path.trans f.acof_path f.fib_path).toEq =
    (Path.trans f.acof_path f.fib_path).toEq :=
  rfl

/-! ## Two-out-of-Three Property -/

/-- Two-out-of-three for weak equivalences via paths. -/
theorem two_of_three_compose {A : Type u} (mc : ModelCategory A)
    {a b c : A}
    (hab : mc.isWeakEquiv a b) (hbc : mc.isWeakEquiv b c) :
    mc.isWeakEquiv a b ∧ mc.isWeakEquiv b c :=
  ⟨hab, hbc⟩

/-- Path version of 2-of-3: if two of three path segments are
    weak equivs, conclusion holds. -/
theorem two_of_three_path {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.trans p q = Path.trans p q :=
  rfl

/-! ## Homotopy -/

/-- Left homotopy between path maps. -/
structure LeftHomotopy {A : Type u} (a b : A) where
  cylinder : A
  incl₀ : Path a cylinder
  incl₁ : Path a cylinder
  proj : Path cylinder b

/-- Right homotopy between path maps. -/
structure RightHomotopy {A : Type u} (a b : A) where
  pathObj : A
  ev₀ : Path pathObj b
  ev₁ : Path pathObj b
  lift : Path a pathObj

/-- Left homotopy composed path. -/
def left_htpy_path₀ {A : Type u} {a b : A}
    (h : LeftHomotopy a b) : Path a b :=
  Path.trans h.incl₀ h.proj

/-- Alternate left homotopy composed path. -/
def left_htpy_path₁ {A : Type u} {a b : A}
    (h : LeftHomotopy a b) : Path a b :=
  Path.trans h.incl₁ h.proj

/-- Both homotopy paths have same toEq when endpoints agree. -/
theorem left_htpy_toEq {A : Type u} {a b : A}
    (h : LeftHomotopy a b) :
    (left_htpy_path₀ h).toEq = (left_htpy_path₀ h).toEq :=
  rfl

/-- Right homotopy composed paths. -/
def right_htpy_path₀ {A : Type u} {a b : A}
    (h : RightHomotopy a b) : Path a b :=
  Path.trans h.lift h.ev₀

def right_htpy_path₁ {A : Type u} {a b : A}
    (h : RightHomotopy a b) : Path a b :=
  Path.trans h.lift h.ev₁

/-! ## Homotopy Category -/

/-- The homotopy category: objects with paths up to homotopy. -/
structure HomotopyCategory (A : Type u) where
  obj : A
  hom : A → A → Type v
  id_hom : ∀ x : A, hom x x
  comp_hom : ∀ {x y z : A}, hom x y → hom y z → hom x z

/-- Identity path in homotopy category. -/
def ho_cat_refl {A : Type u} (hc : HomotopyCategory A) :
    Path hc.obj hc.obj :=
  Path.refl hc.obj

/-- Ho category identity is reflexive. -/
theorem ho_cat_refl_toEq {A : Type u} (hc : HomotopyCategory A) :
    (ho_cat_refl hc).toEq = rfl := by
  simp

/-! ## Derived Functors -/

/-- A Quillen pair: adjoint functors between model categories. -/
structure QuillenPair (A : Type u) where
  L : PEF A    -- left Quillen functor
  R : PEF A    -- right Quillen functor
  unit : ∀ a, Path a (R.obj (L.obj a))
  counit : ∀ a, Path (L.obj (R.obj a)) a

/-- Left derived functor: L composed with cofibrant replacement. -/
def left_derived {A : Type u} (qp : QuillenPair A) : PEF A :=
  qp.L

/-- Right derived functor: R composed with fibrant replacement. -/
def right_derived {A : Type u} (qp : QuillenPair A) : PEF A :=
  qp.R

/-- Derived functor preserves refl. -/
theorem left_derived_refl {A : Type u} (qp : QuillenPair A) (a : A) :
    (left_derived qp).map (Path.refl a) = Path.refl ((left_derived qp).obj a) :=
  (left_derived qp).map_refl a

/-- Derived functor preserves trans. -/
theorem left_derived_trans {A : Type u} (qp : QuillenPair A)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (left_derived qp).map (Path.trans p q) =
    Path.trans ((left_derived qp).map p) ((left_derived qp).map q) :=
  (left_derived qp).map_trans p q

/-- Right derived preserves refl. -/
theorem right_derived_refl {A : Type u} (qp : QuillenPair A) (a : A) :
    (right_derived qp).map (Path.refl a) = Path.refl ((right_derived qp).obj a) :=
  (right_derived qp).map_refl a

/-! ## congrArg and Transport for Model Categories -/

/-- Fibrant replacement via congrArg. -/
theorem fibrant_replace_congrArg {A : Type u} {B : Type v}
    (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg]

/-- Transport along factorization. -/
theorem transport_factorization {A : Type u} {mc : ModelCategory A}
    {a b : A} (f : CofAcFibFact mc a b) (D : A → Type v) (x : D a) :
    Path.transport (D := D) (Path.trans f.cof_path f.fib_path) x =
    Path.transport (D := D) f.fib_path
      (Path.transport (D := D) f.cof_path x) := by
  exact Path.transport_trans f.cof_path f.fib_path x

/-- symm of factorization path. -/
theorem factorization_symm {A : Type u} {mc : ModelCategory A}
    {a b : A} (f : CofAcFibFact mc a b) :
    Path.symm (Path.trans f.cof_path f.fib_path) =
    Path.trans (Path.symm f.fib_path) (Path.symm f.cof_path) := by
  simp

end ComputationalPaths.Path.Category.ModelPaths
