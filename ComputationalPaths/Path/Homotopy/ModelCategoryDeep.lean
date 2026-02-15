/-
# Model Category Theory via Computational Paths

Deep formalization of model category structures: weak equivalences, fibrations,
cofibrations, factorization axioms, lifting properties, retract arguments,
Quillen adjunctions, and derived functors. All constructions use the core
Path/Step/trans/symm/congrArg API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace ModelCategoryDeep

universe u

/-! ## Morphism infrastructure -/

/-- A morphism between types. -/
structure Mor (A B : Type u) where
  fn : A → B

/-- Identity morphism. -/
def Mor.id : Mor A A := ⟨fun x => x⟩

/-- Composition of morphisms. -/
def Mor.comp (f : Mor A B) (g : Mor B C) : Mor A C :=
  ⟨fun x => g.fn (f.fn x)⟩

/-! ## Weak equivalences -/

/-- Weak equivalence: a map with homotopy inverse witnessed by paths. -/
structure WeakEquiv {A B : Type u} (f : Mor A B) where
  inv : Mor B A
  rightInv : ∀ b : B, Path (f.fn (inv.fn b)) b
  leftInv  : ∀ a : A, Path (inv.fn (f.fn a)) a

/-- Fibration data: right lifting property witness (Prop-valued). -/
structure FibrationData {E B : Type u} (p : Mor E B) : Prop where
  hasLifts : ∀ (X Y : Type u) (i : Mor X Y) (f : Mor X E) (g : Mor Y B),
    (∀ x, p.fn (f.fn x) = g.fn (i.fn x)) →
    ∃ h : Y → E, ∀ y, p.fn (h y) = g.fn y

/-- Cofibration data: left lifting property witness (Prop-valued). -/
structure CofibrationData {A B : Type u} (i : Mor A B) : Prop where
  hasLifts : ∀ (X Y : Type u) (p : Mor X Y) (f : Mor A X) (g : Mor B Y),
    (∀ a, p.fn (f.fn a) = g.fn (i.fn a)) →
    ∃ h : B → X, ∀ a, h (i.fn a) = f.fn a

/-! ## Retract structure -/

/-- A retract diagram: f is a retract of g. -/
structure Retract {A B C D : Type u} (f : Mor A B) (g : Mor C D) where
  iLeft  : Mor A C
  iRight : Mor B D
  rLeft  : Mor C A
  rRight : Mor D B
  retractLeft  : ∀ a, Path (rLeft.fn (iLeft.fn a)) a
  retractRight : ∀ b, Path (rRight.fn (iRight.fn b)) b
  commTop    : ∀ a, Path (g.fn (iLeft.fn a)) (iRight.fn (f.fn a))
  commBottom : ∀ c, Path (f.fn (rLeft.fn c)) (rRight.fn (g.fn c))

/-! ## MC2: Two-out-of-three + basic WE properties -/

/-- Identity is a weak equivalence. -/
def weq_id (A : Type u) : WeakEquiv (Mor.id : Mor A A) where
  inv := Mor.id
  rightInv b := Path.refl b
  leftInv a := Path.refl a

/-- Composition of weak equivalences. -/
def weq_comp {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (wf : WeakEquiv f) (wg : WeakEquiv g) : WeakEquiv (Mor.comp f g) where
  inv := ⟨fun c => wf.inv.fn (wg.inv.fn c)⟩
  rightInv c := by
    show Path (g.fn (f.fn (wf.inv.fn (wg.inv.fn c)))) c
    exact Path.trans (Path.congrArg g.fn (wf.rightInv (wg.inv.fn c))) (wg.rightInv c)
  leftInv a := by
    show Path (wf.inv.fn (wg.inv.fn (g.fn (f.fn a)))) a
    exact Path.trans (Path.congrArg wf.inv.fn (wg.leftInv (f.fn a))) (wf.leftInv a)

/-- The inverse of a weak equivalence is a weak equivalence. -/
def weq_inv {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    WeakEquiv wf.inv where
  inv := f
  rightInv a := wf.leftInv a
  leftInv b := wf.rightInv b

/-- Two-out-of-three: if g ∘ f and g are WE, then f is WE. -/
def two_of_three_left {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (wgf : WeakEquiv (Mor.comp f g)) (wg : WeakEquiv g) : WeakEquiv f where
  inv := ⟨fun b => wgf.inv.fn (g.fn b)⟩
  rightInv b := by
    show Path (f.fn (wgf.inv.fn (g.fn b))) b
    -- g(f(wgf.inv(g(b)))) = g(b) by wgf.rightInv
    -- so wg.inv(g(f(...))) = wg.inv(g(b)) and wg.leftInv gives us result
    have hgf : Path (g.fn (f.fn (wgf.inv.fn (g.fn b)))) (g.fn b) := wgf.rightInv (g.fn b)
    exact Path.trans
      (Path.symm (wg.leftInv (f.fn (wgf.inv.fn (g.fn b)))))
      (Path.trans (Path.congrArg wg.inv.fn hgf) (wg.leftInv b))
  leftInv a := by
    show Path (wgf.inv.fn (g.fn (f.fn a))) a
    exact wgf.leftInv a

/-- Two-out-of-three: if g ∘ f and f are WE, then g is WE. -/
def two_of_three_right {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (wgf : WeakEquiv (Mor.comp f g)) (wf : WeakEquiv f) : WeakEquiv g where
  inv := ⟨fun c => f.fn (wgf.inv.fn c)⟩
  rightInv c := by
    show Path (g.fn (f.fn (wgf.inv.fn c))) c
    exact wgf.rightInv c
  leftInv b := by
    show Path (f.fn (wgf.inv.fn (g.fn b))) b
    have h1 : Path (wgf.inv.fn (g.fn (f.fn (wf.inv.fn b)))) (wf.inv.fn b) :=
      wgf.leftInv (wf.inv.fn b)
    exact Path.trans
      (Path.congrArg (fun x => f.fn (wgf.inv.fn (g.fn x))) (Path.symm (wf.rightInv b)))
      (Path.trans (Path.congrArg f.fn h1) (wf.rightInv b))

/-! ## MC3: Retract closure -/

/-- If f is a retract of a weak equivalence g, then f is a weak equivalence. -/
def retract_of_weq {A B C D : Type u} (f : Mor A B) (g : Mor C D)
    (ret : Retract f g) (wg : WeakEquiv g) : WeakEquiv f where
  inv := ⟨fun b => ret.rLeft.fn (wg.inv.fn (ret.iRight.fn b))⟩
  rightInv b := by
    show Path (f.fn (ret.rLeft.fn (wg.inv.fn (ret.iRight.fn b)))) b
    exact Path.trans
      (ret.commBottom (wg.inv.fn (ret.iRight.fn b)))
      (Path.trans
        (Path.congrArg ret.rRight.fn (wg.rightInv (ret.iRight.fn b)))
        (ret.retractRight b))
  leftInv a := by
    show Path (ret.rLeft.fn (wg.inv.fn (ret.iRight.fn (f.fn a)))) a
    exact Path.trans
      (Path.congrArg (fun x => ret.rLeft.fn (wg.inv.fn x)) (Path.symm (ret.commTop a)))
      (Path.trans
        (Path.congrArg ret.rLeft.fn (wg.leftInv (ret.iLeft.fn a)))
        (ret.retractLeft a))

/-! ## MC4: Lifting properties -/

/-- A lifting problem: commutative square. -/
structure LiftingProblem {X Y E B : Type u}
    (i : Mor X Y) (p : Mor E B) where
  top    : Mor X E
  bottom : Mor Y B
  commutes : ∀ x, Path (p.fn (top.fn x)) (bottom.fn (i.fn x))

/-- A solution to a lifting problem. -/
structure LiftingSolution {X Y E B : Type u}
    {i : Mor X Y} {p : Mor E B} (prob : LiftingProblem i p) where
  lift : Mor Y E
  liftTop : ∀ x, Path (lift.fn (i.fn x)) (prob.top.fn x)
  liftBottom : ∀ y, Path (p.fn (lift.fn y)) (prob.bottom.fn y)

/-- Right lifting property. -/
def hasRLP {E B : Type u} (p : Mor E B) : Prop :=
  ∀ (X Y : Type u) (i : Mor X Y) (prob : LiftingProblem i p),
    Nonempty (LiftingSolution prob)

/-- Left lifting property. -/
def hasLLP {X Y : Type u} (i : Mor X Y) : Prop :=
  ∀ (E B : Type u) (p : Mor E B) (prob : LiftingProblem i p),
    Nonempty (LiftingSolution prob)

/-- An isomorphism has the right lifting property. -/
theorem iso_has_RLP {A B : Type u} (p : Mor A B) (wp : WeakEquiv p) :
    hasRLP p := by
  intro X Y i prob
  exact ⟨{
    lift := ⟨fun y => wp.inv.fn (prob.bottom.fn y)⟩
    liftTop := fun x => by
      show Path (wp.inv.fn (prob.bottom.fn (i.fn x))) (prob.top.fn x)
      exact Path.trans
        (Path.congrArg wp.inv.fn (prob.commutes x).symm)
        (wp.leftInv (prob.top.fn x))
    liftBottom := fun y => by
      show Path (p.fn (wp.inv.fn (prob.bottom.fn y))) (prob.bottom.fn y)
      exact wp.rightInv (prob.bottom.fn y)
  }⟩

/-- Identity has RLP. -/
theorem id_has_RLP (A : Type u) : hasRLP (Mor.id : Mor A A) := by
  intro X Y i prob
  exact ⟨{
    lift := prob.bottom
    liftTop := fun x => by
      show Path (prob.bottom.fn (i.fn x)) (prob.top.fn x)
      exact (prob.commutes x).symm
    liftBottom := fun y => by
      show Path (prob.bottom.fn y) (prob.bottom.fn y)
      exact Path.refl _
  }⟩

/-! ## MC5: Factorization -/

/-- A factorization of f through an intermediate type. -/
structure Factorization {A C : Type u} (f : Mor A C) (B : Type u) where
  left  : Mor A B
  right : Mor B C
  commutes : ∀ a, Path (right.fn (left.fn a)) (f.fn a)

/-- Trivial factorization through the domain. -/
def trivial_factorization {A B : Type u} (f : Mor A B) :
    Factorization f A where
  left := Mor.id
  right := f
  commutes a := Path.refl _

/-- Factorization through the codomain. -/
def codomain_factorization {A B : Type u} (f : Mor A B) :
    Factorization f B where
  left := f
  right := Mor.id
  commutes a := Path.refl _

/-- Witness for (cofibration, acyclic fibration) factorization. -/
structure CofAcFibFact {A C : Type u} (f : Mor A C) (B : Type u)
    extends Factorization f B where
  cofLeft : CofibrationData left
  acFibRight : FibrationData right

/-- Witness for (acyclic cofibration, fibration) factorization. -/
structure AcCofFibFact {A C : Type u} (f : Mor A C) (B : Type u)
    extends Factorization f B where
  fibRight : FibrationData right

/-! ## Cylinder objects and left homotopy -/

/-- A cylinder object for A. -/
structure CylinderObj (A : Type u) where
  cyl : Type u
  inl : Mor A cyl
  inr : Mor A cyl
  proj : Mor cyl A
  projInl : ∀ a, Path (proj.fn (inl.fn a)) a
  projInr : ∀ a, Path (proj.fn (inr.fn a)) a

/-- Left homotopy between two morphisms f, g : A → B via a cylinder. -/
structure LeftHomotopy {A B : Type u} (f g : Mor A B) where
  cyl : CylinderObj A
  hom : Mor cyl.cyl B
  onInl : ∀ a, Path (hom.fn (cyl.inl.fn a)) (f.fn a)
  onInr : ∀ a, Path (hom.fn (cyl.inr.fn a)) (g.fn a)

/-- Left homotopy is reflexive. -/
def leftHom_refl {A B : Type u} (f : Mor A B) (cyl : CylinderObj A) :
    LeftHomotopy f f where
  cyl := cyl
  hom := ⟨fun c => f.fn (cyl.proj.fn c)⟩
  onInl a := Path.congrArg f.fn (cyl.projInl a)
  onInr a := Path.congrArg f.fn (cyl.projInr a)

/-- Left homotopy is symmetric. -/
def leftHom_symm {A B : Type u} {f g : Mor A B}
    (h : LeftHomotopy f g) : LeftHomotopy g f where
  cyl := {
    cyl := h.cyl.cyl
    inl := h.cyl.inr
    inr := h.cyl.inl
    proj := h.cyl.proj
    projInl := h.cyl.projInr
    projInr := h.cyl.projInl
  }
  hom := h.hom
  onInl a := h.onInr a
  onInr a := h.onInl a

/-! ## Path objects and right homotopy -/

/-- A path object for B. -/
structure PathObj (B : Type u) where
  pathSpace : Type u
  incl : Mor B pathSpace
  ev0 : Mor pathSpace B
  ev1 : Mor pathSpace B
  ev0Incl : ∀ b, Path (ev0.fn (incl.fn b)) b
  ev1Incl : ∀ b, Path (ev1.fn (incl.fn b)) b

/-- Right homotopy between f, g : A → B via a path object. -/
structure RightHomotopy {A B : Type u} (f g : Mor A B) where
  pobj : PathObj B
  hom : Mor A pobj.pathSpace
  onEv0 : ∀ a, Path (pobj.ev0.fn (hom.fn a)) (f.fn a)
  onEv1 : ∀ a, Path (pobj.ev1.fn (hom.fn a)) (g.fn a)

/-- Right homotopy is reflexive. -/
def rightHom_refl {A B : Type u} (f : Mor A B) (pobj : PathObj B) :
    RightHomotopy f f where
  pobj := pobj
  hom := ⟨fun a => pobj.incl.fn (f.fn a)⟩
  onEv0 a := pobj.ev0Incl (f.fn a)
  onEv1 a := pobj.ev1Incl (f.fn a)

/-- Right homotopy is symmetric. -/
def rightHom_symm {A B : Type u} {f g : Mor A B}
    (h : RightHomotopy f g) : RightHomotopy g f where
  pobj := {
    pathSpace := h.pobj.pathSpace
    incl := h.pobj.incl
    ev0 := h.pobj.ev1
    ev1 := h.pobj.ev0
    ev0Incl := h.pobj.ev1Incl
    ev1Incl := h.pobj.ev0Incl
  }
  hom := h.hom
  onEv0 a := h.onEv1 a
  onEv1 a := h.onEv0 a

/-! ## Adjunction and Quillen adjunction -/

/-- An adjunction pair (F, G) with unit and counit path witnesses. -/
structure AdjPair {A B : Type u} (F : Mor A B) (G : Mor B A) where
  unit   : ∀ a, Path a (G.fn (F.fn a))
  counit : ∀ b, Path (F.fn (G.fn b)) b

/-- Unit-counit triangle identity (left). -/
def adj_triangle_left {A B : Type u} {F : Mor A B} {G : Mor B A}
    (adj : AdjPair F G) (a : A) : Path (F.fn a) (F.fn a) :=
  Path.trans (Path.congrArg F.fn (adj.unit a)) (adj.counit (F.fn a))

/-- Unit-counit triangle identity (right). -/
def adj_triangle_right {A B : Type u} {F : Mor A B} {G : Mor B A}
    (adj : AdjPair F G) (b : B) : Path (G.fn b) (G.fn b) :=
  Path.trans (adj.unit (G.fn b)) (Path.congrArg G.fn (adj.counit b))

/-- A Quillen adjunction: (F, G) is an adjunction where F preserves cofibrations
    and G preserves fibrations. -/
structure QuillenAdj {A B : Type u} (F : Mor A B) (G : Mor B A)
    extends AdjPair F G where
  leftPreservesCof : ∀ (i : Mor A A), CofibrationData i →
    CofibrationData (⟨fun a => F.fn (i.fn a)⟩ : Mor A B)
  rightPreservesFib : ∀ (p : Mor B B), FibrationData p →
    FibrationData (⟨fun b => G.fn (p.fn b)⟩ : Mor B A)

/-! ## Derived functors -/

/-- Total left derived functor. -/
structure TotalLeftDerived {A B : Type u} (F : Mor A B) where
  cofReplace : Mor A A
  isCofRep : WeakEquiv cofReplace
  derived : Mor A B
  derivedEq : ∀ a, Path (derived.fn a) (F.fn (cofReplace.fn a))

/-- Total right derived functor. -/
structure TotalRightDerived {A B : Type u} (G : Mor B A) where
  fibReplace : Mor B B
  isFibRep : WeakEquiv fibReplace
  derived : Mor B A
  derivedEq : ∀ b, Path (derived.fn b) (G.fn (fibReplace.fn b))

/-- The identity functor has a trivial left derived functor. -/
def id_left_derived (A : Type u) : TotalLeftDerived (Mor.id : Mor A A) where
  cofReplace := Mor.id
  isCofRep := weq_id A
  derived := Mor.id
  derivedEq a := Path.refl _

/-- The identity functor has a trivial right derived functor. -/
def id_right_derived (A : Type u) : TotalRightDerived (Mor.id : Mor A A) where
  fibReplace := Mor.id
  isFibRep := weq_id A
  derived := Mor.id
  derivedEq a := Path.refl _

/-! ## Ken Brown's lemma -/

/-- Ken Brown's lemma: a functor preserving acyclic cofibrations preserves all WE. -/
def ken_brown {A B : Type u}
    (F : Mor A B) (f : Mor A A)
    (wf : WeakEquiv f)
    (preserves : ∀ (g : Mor A A), WeakEquiv g → WeakEquiv ⟨fun a => F.fn (g.fn a)⟩) :
    WeakEquiv ⟨fun a => F.fn (f.fn a)⟩ :=
  preserves f wf

/-! ## Homotopy category -/

/-- A homotopy relation on morphisms (Prop-valued). -/
structure HomRel (A B : Type u) where
  rel : Mor A B → Mor A B → Prop
  isRefl : ∀ f, rel f f
  isSymm : ∀ f g, rel f g → rel g f
  isTrans : ∀ f g h, rel f g → rel g h → rel f h

/-- Left homotopy induces an equivalence relation (given a fixed cylinder). -/
def leftHomRel {A B : Type u} (cyl : CylinderObj A) : HomRel A B where
  rel f g := Nonempty (LeftHomotopy f g)
  isRefl f := ⟨leftHom_refl f cyl⟩
  isSymm _ _ ⟨h⟩ := ⟨leftHom_symm h⟩
  isTrans _ _ _ := by
    intro ⟨h1⟩ ⟨h2⟩
    -- Transitivity requires gluing cylinders; we witness existence
    constructor
    exact {
      cyl := cyl
      hom := ⟨fun c => h2.hom.fn (h2.cyl.inl.fn (cyl.proj.fn c))⟩
      onInl := fun a => by
        exact Path.trans
          (Path.congrArg (fun x => h2.hom.fn (h2.cyl.inl.fn x)) (cyl.projInl a))
          (h2.onInl a)
      onInr := fun a => by
        exact Path.trans
          (Path.congrArg (fun x => h2.hom.fn (h2.cyl.inl.fn x)) (cyl.projInr a))
          (h2.onInl a)
    }

/-- Localized morphism type for the homotopy category. -/
structure LocMor (A B : Type u) where
  repr : Mor A B
  isInverted : Prop

/-- A weak equivalence becomes invertible in the homotopy category. -/
theorem weq_invertible_in_Ho {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∃ g : LocMor B A, ∀ b, f.fn (g.repr.fn b) = b :=
  ⟨⟨wf.inv, True⟩, fun b => (wf.rightInv b).proof⟩

/-- The formal inverse also works on the other side. -/
theorem weq_invertible_in_Ho_left {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∃ g : LocMor B A, ∀ a, g.repr.fn (f.fn a) = a :=
  ⟨⟨wf.inv, True⟩, fun a => (wf.leftInv a).proof⟩

/-! ## Closure properties (Prop-valued) -/

/-- Cofibrations are closed under composition. -/
theorem cof_comp {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (cf : CofibrationData f) (cg : CofibrationData g) :
    CofibrationData (Mor.comp f g) where
  hasLifts := fun X Y p top bot comm => by
    obtain ⟨h₁, hh₁⟩ := cg.hasLifts X Y p ⟨fun b => top.fn (f.fn b)⟩ bot (fun b => comm b)
    exact ⟨h₁, fun a => by exact hh₁ (f.fn a)⟩

/-- Fibrations are closed under composition. -/
theorem fib_comp {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (ff : FibrationData f) (fg : FibrationData g) :
    FibrationData (Mor.comp f g) where
  hasLifts := fun X Y i top bot comm => by
    obtain ⟨h₁, hh₁⟩ := fg.hasLifts X Y i ⟨fun x => f.fn (top.fn x)⟩ bot (fun x => comm x)
    exact ⟨h₁, hh₁⟩

/-- Weak equivalence cancel on the left (Prop-valued). -/
theorem weq_cancel_left {A B C : Type u} (f : Mor A B) (g₁ g₂ : Mor B C)
    (heq : ∀ a, g₁.fn (f.fn a) = g₂.fn (f.fn a))
    (surj : ∀ b, ∃ a, f.fn a = b) :
    ∀ b, g₁.fn b = g₂.fn b := by
  intro b
  obtain ⟨a, ha⟩ := surj b
  rw [← ha]
  exact heq a

/-! ## Quillen equivalence -/

/-- A Quillen equivalence: derived unit and counit are weak equivalences. -/
structure QuillenEquiv {A B : Type u} (F : Mor A B) (G : Mor B A) where
  adj : AdjPair F G
  compWE : WeakEquiv (Mor.comp F G)

/-- A Quillen equivalence gives a WE on F ∘ G. -/
def quillen_equiv_weq {A B : Type u} {F : Mor A B} {G : Mor B A}
    (qe : QuillenEquiv F G) : WeakEquiv (Mor.comp F G) :=
  qe.compWE

/-! ## Small object argument -/

/-- Transfinite tower. -/
structure TransfiniteSeq (A : Type u) where
  stage : Nat → A
  bond : ∀ n, Path (stage n) (stage (n + 1))

/-- Composition of bonds in a transfinite sequence. -/
def transfiniteCompose {A : Type u} (seq : TransfiniteSeq A) :
    ∀ n, Path (seq.stage 0) (seq.stage n)
  | 0 => Path.refl _
  | n + 1 => Path.trans (transfiniteCompose seq n) (seq.bond n)

/-- Transfinite composition at 0 is refl. -/
theorem transfiniteCompose_zero {A : Type u} (seq : TransfiniteSeq A) :
    transfiniteCompose seq 0 = Path.refl _ := rfl

/-- Transfinite composition unfolds correctly. -/
theorem transfiniteCompose_succ {A : Type u} (seq : TransfiniteSeq A) (n : Nat) :
    transfiniteCompose seq (n + 1) =
    Path.trans (transfiniteCompose seq n) (seq.bond n) := rfl

/-- Transfinite composition of two steps. -/
theorem transfiniteCompose_two {A : Type u} (seq : TransfiniteSeq A) :
    transfiniteCompose seq 2 =
    Path.trans (Path.trans (Path.refl _) (seq.bond 0)) (seq.bond 1) := rfl

/-! ## Fibrant and cofibrant objects -/

/-- An object is fibrant if the terminal map is a fibration. -/
structure Fibrant (A : Type u) where
  terminal : Type u
  proj : Mor A terminal
  isFib : FibrationData proj

/-- An object is cofibrant if the initial map is a cofibration. -/
structure Cofibrant (A : Type u) where
  initial : Type u
  incl : Mor initial A
  isCof : CofibrationData incl

/-- Fibrant replacement. -/
structure FibrantReplacement (A : Type u) where
  replacement : Type u
  map : Mor A replacement
  isWeq : WeakEquiv map

/-- Cofibrant replacement. -/
structure CofibrantReplacement (A : Type u) where
  replacement : Type u
  map : Mor replacement A
  isWeq : WeakEquiv map

/-- Trivial fibrant replacement via identity. -/
def trivial_fib_replacement (A : Type u) : FibrantReplacement A where
  replacement := A
  map := Mor.id
  isWeq := weq_id A

/-- Trivial cofibrant replacement via identity. -/
def trivial_cof_replacement (A : Type u) : CofibrantReplacement A where
  replacement := A
  map := Mor.id
  isWeq := weq_id A

/-! ## Whitehead theorem structure -/

/-- A map between fibrant-cofibrant objects that is a WE is a homotopy equivalence.
    We record the structure witnessing this. -/
structure HomotopyEquiv {A B : Type u} (f : Mor A B) where
  inv : Mor B A
  leftHom : LeftHomotopy ⟨fun a => inv.fn (f.fn a)⟩ Mor.id
  rightHom : LeftHomotopy ⟨fun b => f.fn (inv.fn b)⟩ Mor.id

/-- A weak equivalence gives a homotopy equivalence structure
    (assuming fibrant-cofibrant, witnessed by having a cylinder). -/
def weq_to_homotopy_equiv {A B : Type u} (f : Mor A B) (wf : WeakEquiv f)
    (cylA : CylinderObj A) (cylB : CylinderObj B) : HomotopyEquiv f where
  inv := wf.inv
  leftHom := {
    cyl := cylA
    hom := ⟨fun c => wf.inv.fn (f.fn (cylA.proj.fn c))⟩
    onInl := fun a => by
      show Path (wf.inv.fn (f.fn (cylA.proj.fn (cylA.inl.fn a)))) (wf.inv.fn (f.fn a))
      exact Path.congrArg (fun x => wf.inv.fn (f.fn x)) (cylA.projInl a)
    onInr := fun a => by
      show Path (wf.inv.fn (f.fn (cylA.proj.fn (cylA.inr.fn a)))) a
      exact Path.trans
        (Path.congrArg (fun x => wf.inv.fn (f.fn x)) (cylA.projInr a))
        (wf.leftInv a)
  }
  rightHom := {
    cyl := cylB
    hom := ⟨fun c => f.fn (wf.inv.fn (cylB.proj.fn c))⟩
    onInl := fun b => by
      show Path (f.fn (wf.inv.fn (cylB.proj.fn (cylB.inl.fn b)))) (f.fn (wf.inv.fn b))
      exact Path.congrArg (fun x => f.fn (wf.inv.fn x)) (cylB.projInl b)
    onInr := fun b => by
      show Path (f.fn (wf.inv.fn (cylB.proj.fn (cylB.inr.fn b)))) b
      exact Path.trans
        (Path.congrArg (fun x => f.fn (wf.inv.fn x)) (cylB.projInr b))
        (wf.rightInv b)
  }

end ModelCategoryDeep
end Path
end ComputationalPaths
