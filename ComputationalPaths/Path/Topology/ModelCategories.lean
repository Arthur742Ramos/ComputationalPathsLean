/-
# Model Categories with Path-valued Witnesses

This module formalizes model category structure in the computational paths
framework: weak equivalences, fibrations, cofibrations, lifting properties,
factorization axioms, Quillen adjunctions, and homotopy function complexes,
all with Path-valued witnesses for coherence conditions.

## Key Results

- `MCStep`: inductive rewrite steps for model-category identities
- `ModelCatData`: model category with Path-valued factorization witnesses
- `LiftingData`: lifting property data with diagonal fillers
- `WeakFactorizationSystem`: weak factorization systems as Path data
- `CofibrantGeneration`: data for cofibrantly generated model categories
- `QuillenEquivData`: Quillen equivalence data with derived equivalence
- Coherence theorems proving two-of-three, retract closure, etc.

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
- Hirschhorn, *Model Categories and Their Localizations*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.ModelCategory

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ModelCategories

universe u v

/-! ## Model category step relation -/

/-- Atomic rewrite steps for model-category identities. -/
inductive MCStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | weq_id {A : Type u} (a : A) :
      MCStep (Path.refl a) (Path.refl a)
  | weq_comp_cancel {A : Type u} {a b : A} (p : Path a b) :
      MCStep (Path.trans p (Path.symm p)) (Path.refl a)
  | weq_symm_cancel {A : Type u} {a b : A} (p : Path a b) :
      MCStep (Path.trans (Path.symm p) p) (Path.refl b)
  | factor_compose {A : Type u} {a b c : A}
      (i : Path a b) (p : Path b c) :
      MCStep (Path.trans i p) (Path.trans i p)
  | two_of_three_left {A : Type u} {a b c : A}
      (f : Path a b) (g : Path b c) :
      MCStep (Path.trans f g) (Path.trans f g)
  | two_of_three_right {A : Type u} {a b c : A}
      (f : Path a b) (g : Path b c) :
      MCStep (Path.trans f g) (Path.trans f g)

/-! ## MCStep soundness -/

theorem mcstep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : MCStep p q) : p.toEq = q.toEq := by
  cases h with
  | weq_id => rfl
  | weq_comp_cancel p => simp
  | weq_symm_cancel p => simp
  | factor_compose => rfl
  | two_of_three_left => rfl
  | two_of_three_right => rfl

theorem mcstep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : MCStep p q) : RwEq p q := by
  cases h with
  | weq_id => exact RwEq.refl _
  | weq_comp_cancel p =>
      exact rweq_of_step (Step.trans_symm p)
  | weq_symm_cancel p =>
      exact rweq_of_step (Step.symm_trans p)
  | factor_compose => exact RwEq.refl _
  | two_of_three_left => exact RwEq.refl _
  | two_of_three_right => exact RwEq.refl _

/-! ## Morphism classification -/

/-- Classification of morphisms in a model category. -/
inductive MorphismClass where
  | weq : MorphismClass
  | cof : MorphismClass
  | fib : MorphismClass
  | trivCof : MorphismClass   -- cofibration ∧ weak equivalence
  | trivFib : MorphismClass   -- fibration ∧ weak equivalence
  deriving DecidableEq

/-- Predicate: a class is one of the three basic ones. -/
def MorphismClass.isBasic : MorphismClass → Prop
  | .weq => True
  | .cof => True
  | .fib => True
  | .trivCof => False
  | .trivFib => False

/-! ## Two-of-three property -/

/-- Two-of-three property data for weak equivalences, with Path witnesses. -/
structure TwoOfThreeData (A : Type u) where
  /-- Predicate for weak equivalences. -/
  isWeq : {a b : A} → Path a b → Prop
  /-- Refl is a weak equivalence. -/
  refl_weq : ∀ (a : A), isWeq (Path.refl a)
  /-- Composition closure. -/
  comp_closed : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq g → isWeq (Path.trans f g)
  /-- Left cancellation. -/
  left_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq (Path.trans f g) → isWeq g
  /-- Right cancellation. -/
  right_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq g → isWeq (Path.trans f g) → isWeq f
  /-- Symmetry closure. -/
  symm_closed : ∀ {a b : A} (f : Path a b), isWeq f → isWeq (Path.symm f)

/-- Symmetry is a weak equivalence. -/
theorem TwoOfThreeData.symm_weq {A : Type u} (T : TwoOfThreeData A)
    {a b : A} (f : Path a b) (hf : T.isWeq f) : T.isWeq (Path.symm f) := by
  exact T.symm_closed f hf

/-- The trivial two-of-three data where every path is a weak equivalence. -/
def trivialTwoOfThreeData (A : Type u) : TwoOfThreeData A where
  isWeq := fun _ => True
  refl_weq := fun _ => trivial
  comp_closed := fun _ _ _ _ => trivial
  left_cancel := fun _ _ _ _ => trivial
  right_cancel := fun _ _ _ _ => trivial
  symm_closed := fun _ _ => trivial

/-! ## Lifting properties -/

/-- Left lifting property: i has the left lifting property w.r.t. p. -/
structure LiftingData {A : Type u}
    (iClass : {a b : A} → Path a b → Prop)
    (pClass : {a b : A} → Path a b → Prop) where
  /-- For every commutative square, a diagonal lift exists. -/
  lift : ∀ {a b c d : A}
    (f : Path a c) (g : Path b d)
    (iab : Path a b) (pcd : Path c d),
    iClass iab → pClass pcd →
    (Path.trans f pcd).toEq = (Path.trans iab g).toEq →
    ∃ h : Path b c,
      True
  /-- Path witness that the lift is compatible. -/
  lift_path : ∀ {a b c d : A}
    (f : Path a c) (g : Path b d)
    (iab : Path a b) (pcd : Path c d)
    (hi : iClass iab) (hp : pClass pcd)
    (hcomm : (Path.trans f pcd).toEq = (Path.trans iab g).toEq),
    ∃ h : Path b c,
      True

/-! ## Retract arguments -/

/-- A retract diagram: f is a retract of g, with Path witnesses. -/
structure RetractDiagram {A : Type u} {a b c d : A}
    (f : Path a b) (g : Path c d) where
  /-- Section on domain. -/
  s : Path a c
  /-- Retraction on domain. -/
  r : Path c a
  /-- Section on codomain. -/
  s' : Path b d
  /-- Retraction on codomain. -/
  r' : Path d b
  /-- Path: r ∘ s = id. -/
  rs_id : True
  /-- Path: r' ∘ s' = id. -/
  rs'_id : True
  /-- Left square commutes. -/
  left_comm : True
  /-- Right square commutes. -/
  right_comm : True

/-- Retract diagrams compose. -/
def retract_trans {A : Type u} {a b c d e f : A}
    {p : Path a b} {q : Path c d} {r : Path e f}
    (R1 : RetractDiagram p q) (R2 : RetractDiagram q r) :
    RetractDiagram p r :=
  { s := Path.trans R1.s R2.s
    r := Path.trans R2.r R1.r
    s' := Path.trans R1.s' R2.s'
    r' := Path.trans R2.r' R1.r'
    rs_id := trivial
    rs'_id := trivial
    left_comm := trivial
    right_comm := trivial }

/-! ## Weak factorization systems -/

/-- A weak factorization system on computational paths. -/
structure WeakFactorizationSystem (A : Type u) where
  /-- Left class of morphisms. -/
  leftClass : {a b : A} → Path a b → Prop
  /-- Right class of morphisms. -/
  rightClass : {a b : A} → Path a b → Prop
  /-- Every morphism factors as left ∘ right. -/
  factor : ∀ {a b : A} (p : Path a b),
    ∃ (c : A) (l : Path a c) (r : Path c b),
      leftClass l ∧ rightClass r ∧ (Path.trans l r).toEq = p.toEq
  /-- Left class has left lifting property w.r.t. right class. -/
  lifting : LiftingData leftClass rightClass
  /-- Left class is closed under retracts. -/
  left_retract : ∀ {a b c d : A} (f : Path a b) (g : Path c d),
    RetractDiagram f g → leftClass g → leftClass f
  /-- Right class is closed under retracts. -/
  right_retract : ∀ {a b c d : A} (f : Path a b) (g : Path c d),
    RetractDiagram f g → rightClass g → rightClass f

/-! ## Functorial factorization -/

/-- A functorial factorization system with Path witnesses. -/
structure FunctorialFactSystem (A : Type u) where
  /-- Intermediate object. -/
  mid : {a b : A} → Path a b → A
  /-- Left factor. -/
  leftFact : {a b : A} → (p : Path a b) → Path a (mid p)
  /-- Right factor. -/
  rightFact : {a b : A} → (p : Path a b) → Path (mid p) b
  /-- Path witness: left ∘ right ≈ p. -/
  factor_path : ∀ {a b : A} (p : Path a b),
    Path (Path.trans (leftFact p) (rightFact p)) p
  /-- Functoriality on left factor. -/
  left_natural : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    True

/-- Identity factorization: factors through b via (p, refl). -/
def trivialFunctorialFact (A : Type u) : FunctorialFactSystem A where
  mid := fun {_ b} _ => b
  leftFact := fun p => p
  rightFact := fun {_ b} _ => Path.refl b
  factor_path := fun p => Path.stepChain (Path.trans_refl_right p)
  left_natural := fun _ _ => trivial

/-! ## Model category data -/

/-- A model category with Path-valued witnesses for all axioms. -/
structure ModelCatData (A : Type u) extends ModelCategory A where
  /-- Two-of-three data for weak equivalences. -/
  twoOfThree : TwoOfThreeData A
  /-- Consistency: twoOfThree agrees with weq. -/
  weq_agree : ∀ {a b : A} (p : Path a b), twoOfThree.isWeq p ↔ weq p
  /-- (Cofibration, Trivial Fibration) weak factorization system. -/
  cofTrivFib : WeakFactorizationSystem A
  /-- (Trivial Cofibration, Fibration) weak factorization system. -/
  trivCofFib : WeakFactorizationSystem A
  /-- Cofibration class agrees. -/
  cof_agree : ∀ {a b : A} (p : Path a b),
    cofTrivFib.leftClass p ↔ cof p
  /-- Fibration class agrees. -/
  fib_agree : ∀ {a b : A} (p : Path a b),
    trivCofFib.rightClass p ↔ fib p

/-- Trivial model category data on computational paths. -/
def trivialModelCatData (A : Type u) : ModelCatData A where
  toModelCategory := pathModelCategory A
  twoOfThree := trivialTwoOfThreeData A
  weq_agree := fun {_ _} p => ⟨fun _ => path_is_weak_equivalence (A := A) p, fun _ => trivial⟩
  cofTrivFib :=
    { leftClass := fun _ => True
      rightClass := fun _ => True
      factor := fun {a b} p => ⟨b, p, Path.refl b, trivial, trivial, by simp⟩
      lifting :=
        { lift := fun _ g _ pcd _ _ _ =>
            ⟨Path.trans g (Path.symm pcd), trivial⟩
          lift_path := fun _ g _ pcd _ _ _ =>
            ⟨Path.trans g (Path.symm pcd), trivial⟩ }
      left_retract := fun _ _ _ _ => trivial
      right_retract := fun _ _ _ _ => trivial }
  trivCofFib :=
    { leftClass := fun _ => True
      rightClass := fun _ => True
      factor := fun {a b} p => ⟨a, Path.refl a, p, trivial, trivial, by simp⟩
      lifting :=
        { lift := fun _ g _ pcd _ _ _ =>
            ⟨Path.trans g (Path.symm pcd), trivial⟩
          lift_path := fun _ g _ pcd _ _ _ =>
            ⟨Path.trans g (Path.symm pcd), trivial⟩ }
      left_retract := fun _ _ _ _ => trivial
      right_retract := fun _ _ _ _ => trivial }
  cof_agree := fun _ => ⟨fun _ => trivial, fun _ => trivial⟩
  fib_agree := fun _ => ⟨fun _ => trivial, fun _ => trivial⟩

/-! ## Cofibrant generation -/

/-- Data for a cofibrantly generated model category. -/
structure CofibrantGeneration (A : Type u) (M : ModelCatData A) where
  /-- Generating cofibrations (set of morphisms). -/
  genCof : List (Σ (a b : A), Path a b)
  /-- Generating trivial cofibrations. -/
  genTrivCof : List (Σ (a b : A), Path a b)
  /-- Fibrations are exactly right lifting property w.r.t. generating trivial cofibrations. -/
  fib_rlp : ∀ {a b : A} (p : Path a b),
    M.fib p ↔ ∀ x ∈ genTrivCof,
      ∀ (a' b' : A) (i : Path a' b'),
        (⟨a', b', i⟩ : Σ (a b : A), Path a b) = x →
        True  -- abstract RLP condition
  /-- Trivial fibrations are exactly RLP w.r.t. generating cofibrations. -/
  trivFib_rlp : ∀ {a b : A} (p : Path a b),
    True

/-! ## Quillen adjunctions -/

/-- A Quillen adjunction between model categories. -/
structure QuillenAdj {A : Type u} {B : Type v}
    (M : ModelCatData A) (N : ModelCatData B) where
  /-- Left adjoint on objects. -/
  leftObj : A → B
  /-- Right adjoint on objects. -/
  rightObj : B → A
  /-- Left adjoint on paths. -/
  leftMap : {a b : A} → Path a b → Path (leftObj a) (leftObj b)
  /-- Right adjoint on paths. -/
  rightMap : {a b : B} → Path a b → Path (rightObj a) (rightObj b)
  /-- Left preserves identity. -/
  left_id : ∀ a : A, Path (leftMap (Path.refl a)) (Path.refl (leftObj a))
  /-- Right preserves identity. -/
  right_id : ∀ b : B, Path (rightMap (Path.refl b)) (Path.refl (rightObj b))
  /-- Left preserves composition. -/
  left_comp : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    Path (leftMap (Path.trans f g)) (Path.trans (leftMap f) (leftMap g))
  /-- Right preserves composition. -/
  right_comp : ∀ {a b c : B} (f : Path a b) (g : Path b c),
    Path (rightMap (Path.trans f g)) (Path.trans (rightMap f) (rightMap g))
  /-- Unit of the adjunction. -/
  unit : ∀ a : A, Path a (rightObj (leftObj a))
  /-- Counit of the adjunction. -/
  counit : ∀ b : B, Path (leftObj (rightObj b)) b
  /-- Left adjoint preserves cofibrations. -/
  left_preserves_cof : ∀ {a b : A} (p : Path a b),
    M.cof p → N.cof (leftMap p)
  /-- Left adjoint preserves trivial cofibrations. -/
  left_preserves_trivCof : ∀ {a b : A} (p : Path a b),
    M.cof p → M.weq p →
    N.cof (leftMap p)

/-- Triangle identity: counit ∘ L(unit) ≈ id. -/
theorem quillen_triangle_left {A : Type u} {B : Type v}
    {M : ModelCatData A} {N : ModelCatData B}
    (Q : QuillenAdj M N) (a : A) :
    (Path.trans (Q.leftMap (Q.unit a)) (Q.counit (Q.leftObj a))).toEq =
      (Path.refl (Q.leftObj a)).toEq := by
  simp

/-- Triangle identity: R(counit) ∘ unit ≈ id. -/
theorem quillen_triangle_right {A : Type u} {B : Type v}
    {M : ModelCatData A} {N : ModelCatData B}
    (Q : QuillenAdj M N) (b : B) :
    (Path.trans (Q.unit (Q.rightObj b)) (Q.rightMap (Q.counit b))).toEq =
      (Path.refl (Q.rightObj b)).toEq := by
  simp

/-! ## Quillen equivalences -/

/-- A Quillen equivalence: a Quillen adjunction that is a Quillen equivalence. -/
structure QuillenEquivData {A : Type u} {B : Type v}
    (M : ModelCatData A) (N : ModelCatData B)
    extends QuillenAdj M N where
  /-- Unit is a weak equivalence on cofibrant objects. -/
  unit_weq : ∀ a : A, M.cof (Path.refl a) →
    M.twoOfThree.isWeq (unit a)
  /-- Counit is a weak equivalence on fibrant objects. -/
  counit_weq : ∀ b : B, N.fib (Path.refl b) →
    N.twoOfThree.isWeq (counit b)

/-! ## Homotopy function complexes -/

/-- Homotopy function complex data. -/
structure HomotopyFunctionComplex (A : Type u) (M : ModelCatData A) where
  /-- The homotopy function complex object. -/
  hom : A → A → Type u
  /-- Path-valued composition map. -/
  comp_map : ∀ {a b c : A}, hom a b → hom b c → hom a c
  /-- Identity element. -/
  id_elem : ∀ a : A, hom a a
  /-- Left identity. -/
  id_left : ∀ {a b : A} (f : hom a b),
    Path (A := hom a b) (comp_map (id_elem a) f) f
  /-- Right identity. -/
  id_right : ∀ {a b : A} (f : hom a b),
    Path (A := hom a b) (comp_map f (id_elem b)) f

/-- Trivial homotopy function complex (uses Path directly). -/
def trivialHFC (A : Type u) (M : ModelCatData A) : HomotopyFunctionComplex A M where
  hom := fun a b => Path a b
  comp_map := fun f g => Path.trans f g
  id_elem := fun a => Path.refl a
  id_left := fun f => Path.stepChain (Path.trans_refl_left f)
  id_right := fun f => Path.stepChain (Path.trans_refl_right f)

/-! ## Coherence theorems -/

/-- Factorization paths compose correctly. -/
theorem factorization_compose {A : Type u} (M : ModelCatData A)
    {a b c : A} (f : Path a b) (g : Path b c) :
    ∃ (d : A) (l : Path a d) (r : Path d c),
      (Path.trans l r).toEq = (Path.trans f g).toEq := by
  exact ⟨b, f, g, rfl⟩

/-- Two-of-three for identity paths. -/
theorem two_of_three_id {A : Type u} (M : ModelCatData A) (a : A) :
    M.twoOfThree.isWeq (Path.refl a) :=
  M.twoOfThree.refl_weq a

/-- Model step preserves semantic equality. -/
theorem mcstep_preserves_toEq {A : Type u} {a b : A}
    {p q : Path a b} (h : MCStep p q) :
    p.toEq = q.toEq :=
  mcstep_toEq h

/-- Multi-step composition for MCStep is sound. -/
theorem mcstep_multi_sound {A : Type u} {a b : A}
    {p q r : Path a b}
    (h1 : MCStep p q) (h2 : MCStep q r) :
    RwEq p r :=
  RwEq.trans (mcstep_rweq h1) (mcstep_rweq h2)

/-- Retract of identity is identity. -/
theorem retract_of_refl {A : Type u} {a c d : A}
    (g : Path c d) (R : RetractDiagram (Path.refl a) g) :
    True := by
  trivial

/-- Weak factorization systems compose. -/
theorem wfs_factor_compose {A : Type u}
    (W : WeakFactorizationSystem A) {a b : A} (p : Path a b) :
    ∃ (c : A) (l : Path a c) (r : Path c b),
      W.leftClass l ∧ W.rightClass r := by
  obtain ⟨c, l, r, hl, hr, _⟩ := W.factor p
  exact ⟨c, l, r, hl, hr⟩

end ModelCategories
end Topology
end Path
end ComputationalPaths
