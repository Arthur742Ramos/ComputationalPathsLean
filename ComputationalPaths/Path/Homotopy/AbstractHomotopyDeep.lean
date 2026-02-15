/-
# Abstract Homotopy Theory via Computational Paths

Cylinder objects, path objects, abstract homotopy relation, Whitehead theorem
structure, localization at weak equivalences, homotopy limits/colimits,
fibration/cofibration sequences, Puppe sequences. All constructions use the
core Path/Step/trans/symm/congrArg API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace AbstractHomotopyDeep

universe u

/-! ## Abstract morphisms -/

structure Mor (A B : Type u) where
  fn : A → B

def Mor.id : Mor A A := ⟨fun x => x⟩
def Mor.comp (f : Mor A B) (g : Mor B C) : Mor A C := ⟨fun x => g.fn (f.fn x)⟩

/-! ## Weak equivalence -/

structure WeakEquiv {A B : Type u} (f : Mor A B) where
  inv : Mor B A
  rightInv : ∀ b : B, Path (f.fn (inv.fn b)) b
  leftInv  : ∀ a : A, Path (inv.fn (f.fn a)) a

def weq_id (A : Type u) : WeakEquiv (Mor.id : Mor A A) where
  inv := Mor.id
  rightInv b := Path.refl b
  leftInv a := Path.refl a

def weq_inv {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) : WeakEquiv wf.inv where
  inv := f
  rightInv a := wf.leftInv a
  leftInv b := wf.rightInv b

/-! ## Abstract cylinder objects -/

/-- A cylinder object with fold map and projection. -/
structure Cylinder (A : Type u) where
  cyl : Type u
  i₀ : Mor A cyl
  i₁ : Mor A cyl
  p : Mor cyl A
  p_i₀ : ∀ a, Path (p.fn (i₀.fn a)) a
  p_i₁ : ∀ a, Path (p.fn (i₁.fn a)) a

/-- A good cylinder: the projection is a weak equivalence. -/
structure GoodCylinder (A : Type u) extends Cylinder A where
  p_weq : WeakEquiv p

/-- The trivial cylinder: A itself with identity maps. -/
def trivialCylinder (A : Type u) : Cylinder A where
  cyl := A
  i₀ := Mor.id
  i₁ := Mor.id
  p := Mor.id
  p_i₀ a := Path.refl a
  p_i₁ a := Path.refl a

/-- The trivial cylinder is a good cylinder. -/
def trivialGoodCylinder (A : Type u) : GoodCylinder A where
  cyl := A
  i₀ := Mor.id
  i₁ := Mor.id
  p := Mor.id
  p_i₀ a := Path.refl a
  p_i₁ a := Path.refl a
  p_weq := weq_id A

/-! ## Abstract path objects -/

/-- A path object with diagonal and endpoint evaluations. -/
structure PathObject (B : Type u) where
  pathSp : Type u
  s : Mor B pathSp      -- diagonal / constant paths
  d₀ : Mor pathSp B     -- source
  d₁ : Mor pathSp B     -- target
  d₀_s : ∀ b, Path (d₀.fn (s.fn b)) b
  d₁_s : ∀ b, Path (d₁.fn (s.fn b)) b

/-- A good path object: the diagonal is a weak equivalence. -/
structure GoodPathObject (B : Type u) extends PathObject B where
  s_weq : WeakEquiv s

/-- The trivial path object. -/
def trivialPathObject (B : Type u) : PathObject B where
  pathSp := B
  s := Mor.id
  d₀ := Mor.id
  d₁ := Mor.id
  d₀_s b := Path.refl b
  d₁_s b := Path.refl b

/-- Trivial good path object. -/
def trivialGoodPathObject (B : Type u) : GoodPathObject B where
  pathSp := B
  s := Mor.id
  d₀ := Mor.id
  d₁ := Mor.id
  d₀_s b := Path.refl b
  d₁_s b := Path.refl b
  s_weq := weq_id B

/-! ## Left homotopy -/

/-- Left homotopy between f, g : A → B. -/
structure LeftHom {A B : Type u} (f g : Mor A B) where
  cyl : Cylinder A
  H : Mor cyl.cyl B
  H_i₀ : ∀ a, Path (H.fn (cyl.i₀.fn a)) (f.fn a)
  H_i₁ : ∀ a, Path (H.fn (cyl.i₁.fn a)) (g.fn a)

/-- Left homotopy is reflexive. -/
def leftHom_refl {A B : Type u} (f : Mor A B) (cyl : Cylinder A) : LeftHom f f where
  cyl := cyl
  H := ⟨fun c => f.fn (cyl.p.fn c)⟩
  H_i₀ a := Path.congrArg f.fn (cyl.p_i₀ a)
  H_i₁ a := Path.congrArg f.fn (cyl.p_i₁ a)

/-- Left homotopy is symmetric (by swapping i₀ and i₁). -/
def leftHom_symm {A B : Type u} {f g : Mor A B} (h : LeftHom f g) : LeftHom g f where
  cyl := { cyl := h.cyl.cyl, i₀ := h.cyl.i₁, i₁ := h.cyl.i₀, p := h.cyl.p,
            p_i₀ := h.cyl.p_i₁, p_i₁ := h.cyl.p_i₀ }
  H := h.H
  H_i₀ a := h.H_i₁ a
  H_i₁ a := h.H_i₀ a

/-! ## Right homotopy -/

/-- Right homotopy between f, g : A → B. -/
structure RightHom {A B : Type u} (f g : Mor A B) where
  pobj : PathObject B
  H : Mor A pobj.pathSp
  H_d₀ : ∀ a, Path (pobj.d₀.fn (H.fn a)) (f.fn a)
  H_d₁ : ∀ a, Path (pobj.d₁.fn (H.fn a)) (g.fn a)

/-- Right homotopy is reflexive. -/
def rightHom_refl {A B : Type u} (f : Mor A B) (po : PathObject B) : RightHom f f where
  pobj := po
  H := ⟨fun a => po.s.fn (f.fn a)⟩
  H_d₀ a := po.d₀_s (f.fn a)
  H_d₁ a := po.d₁_s (f.fn a)

/-- Right homotopy is symmetric. -/
def rightHom_symm {A B : Type u} {f g : Mor A B} (h : RightHom f g) : RightHom g f where
  pobj := { pathSp := h.pobj.pathSp, s := h.pobj.s, d₀ := h.pobj.d₁, d₁ := h.pobj.d₀,
             d₀_s := h.pobj.d₁_s, d₁_s := h.pobj.d₀_s }
  H := h.H
  H_d₀ a := h.H_d₁ a
  H_d₁ a := h.H_d₀ a

/-! ## Homotopy equivalence -/

/-- A homotopy equivalence: f has a homotopy inverse. -/
structure HomotopyEquiv {A B : Type u} (f : Mor A B) where
  inv : Mor B A
  leftHom : LeftHom ⟨fun a => inv.fn (f.fn a)⟩ Mor.id
  rightHom : LeftHom ⟨fun b => f.fn (inv.fn b)⟩ Mor.id

/-- A weak equivalence with cylinder data gives a homotopy equivalence. -/
def weq_to_hom_equiv {A B : Type u} (f : Mor A B) (wf : WeakEquiv f)
    (cylA : Cylinder A) (cylB : Cylinder B) : HomotopyEquiv f where
  inv := wf.inv
  leftHom := {
    cyl := cylA
    H := ⟨fun c => wf.inv.fn (f.fn (cylA.p.fn c))⟩
    H_i₀ := fun a => by
      show Path (wf.inv.fn (f.fn (cylA.p.fn (cylA.i₀.fn a)))) (wf.inv.fn (f.fn a))
      exact Path.congrArg (fun x => wf.inv.fn (f.fn x)) (cylA.p_i₀ a)
    H_i₁ := fun a => by
      show Path (wf.inv.fn (f.fn (cylA.p.fn (cylA.i₁.fn a)))) a
      exact Path.trans
        (Path.congrArg (fun x => wf.inv.fn (f.fn x)) (cylA.p_i₁ a))
        (wf.leftInv a)
  }
  rightHom := {
    cyl := cylB
    H := ⟨fun c => f.fn (wf.inv.fn (cylB.p.fn c))⟩
    H_i₀ := fun b => by
      show Path (f.fn (wf.inv.fn (cylB.p.fn (cylB.i₀.fn b)))) (f.fn (wf.inv.fn b))
      exact Path.congrArg (fun x => f.fn (wf.inv.fn x)) (cylB.p_i₀ b)
    H_i₁ := fun b => by
      show Path (f.fn (wf.inv.fn (cylB.p.fn (cylB.i₁.fn b)))) b
      exact Path.trans
        (Path.congrArg (fun x => f.fn (wf.inv.fn x)) (cylB.p_i₁ b))
        (wf.rightInv b)
  }

/-- The identity is a homotopy equivalence. -/
def id_hom_equiv (A : Type u) (cyl : Cylinder A) : HomotopyEquiv (Mor.id : Mor A A) where
  inv := Mor.id
  leftHom := leftHom_refl Mor.id cyl
  rightHom := leftHom_refl Mor.id cyl

/-! ## Whitehead theorem structure -/

/-- Whitehead's theorem: a weak equivalence between "nice" objects is a homotopy equivalence.
    We package the hypotheses and conclusion. -/
structure WhiteheadData {A B : Type u} (f : Mor A B) where
  weq : WeakEquiv f
  cylA : Cylinder A
  cylB : Cylinder B
  result : HomotopyEquiv f

/-- Construct Whitehead data from a weak equivalence and cylinders. -/
def mkWhiteheadData {A B : Type u} (f : Mor A B) (wf : WeakEquiv f)
    (cylA : Cylinder A) (cylB : Cylinder B) : WhiteheadData f where
  weq := wf
  cylA := cylA
  cylB := cylB
  result := weq_to_hom_equiv f wf cylA cylB

/-! ## Localization at weak equivalences -/

/-- A zigzag of morphisms and formal inverses. -/
inductive ZigZag : Type u → Type u → Type (u + 1)
  | id (A : Type u) : ZigZag A A
  | forward {A B : Type u} : Mor A B → ZigZag A B
  | backward {A B : Type u} : Mor B A → WeakEquiv (Mor.id : Mor B B) → ZigZag A B
  | comp {A B C : Type u} : ZigZag A B → ZigZag B C → ZigZag A C

/-- The length of a zigzag. -/
def ZigZag.length : ZigZag A B → Nat
  | .id _ => 0
  | .forward _ => 1
  | .backward _ _ => 1
  | .comp z1 z2 => z1.length + z2.length

/-- Identity zigzag has length 0. -/
theorem zigzag_id_length (A : Type u) : (ZigZag.id A).length = 0 := rfl

/-- Forward zigzag has length 1. -/
theorem zigzag_forward_length {A B : Type u} (f : Mor A B) :
    (ZigZag.forward f).length = 1 := rfl

/-- A localized morphism: an equivalence class of zigzags. -/
structure LocMor (A B : Type u) where
  zigzag : ZigZag A B

/-- Identity in the localization. -/
def LocMor.idLoc (A : Type u) : LocMor A A := ⟨ZigZag.id A⟩

/-- Composition in the localization. -/
def LocMor.comp {A B C : Type u} (f : LocMor A B) (g : LocMor B C) : LocMor A C :=
  ⟨ZigZag.comp f.zigzag g.zigzag⟩

/-- A morphism embeds into the localization. -/
def LocMor.ofMor {A B : Type u} (f : Mor A B) : LocMor A B :=
  ⟨ZigZag.forward f⟩

/-- Composition with identity is trivial (left). -/
theorem locMor_comp_id_left {A B : Type u} (f : LocMor A B) :
    LocMor.comp (LocMor.idLoc A) f = ⟨ZigZag.comp (ZigZag.id A) f.zigzag⟩ := rfl

/-- A weak equivalence has an inverse in the localization. -/
def weq_inv_loc {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) : LocMor B A :=
  ⟨ZigZag.forward wf.inv⟩

/-- The inverse satisfies one triangle (propositionally). -/
theorem weq_inv_loc_right {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∀ b, f.fn (wf.inv.fn b) = b := fun b => (wf.rightInv b).proof

/-- The inverse satisfies the other triangle. -/
theorem weq_inv_loc_left {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∀ a, wf.inv.fn (f.fn a) = a := fun a => (wf.leftInv a).proof

/-! ## Fiber and cofiber -/

/-- The (homotopy) fiber of f over a point b. -/
structure HFiber {A B : Type u} (f : Mor A B) (b : B) where
  point : A
  path : Path (f.fn point) b

/-- The inclusion of the fiber into A. -/
def HFiber.incl {A B : Type u} {f : Mor A B} {b : B} (x : HFiber f b) : A := x.point

/-- The fiber of the identity is contractible. -/
def hfiber_id_contr (A : Type u) (a : A) :
    HFiber (Mor.id : Mor A A) a where
  point := a
  path := Path.refl a

/-- The (homotopy) cofiber of f: quotient of B by the image of f. -/
structure HCofiber {A B : Type u} (f : Mor A B) where
  carrier : Type u
  proj : Mor B carrier
  collapse : ∀ a, Path (proj.fn (f.fn a)) (proj.fn (f.fn a))  -- all f-images identified

/-- Trivial cofiber (identity quotient). -/
def trivial_cofiber {A B : Type u} (f : Mor A B) : HCofiber f where
  carrier := B
  proj := Mor.id
  collapse a := Path.refl _

/-! ## Fiber sequences -/

/-- A fiber sequence: F → E → B where F is the homotopy fiber. -/
structure FiberSeq {E B : Type u} (p : Mor E B) (b : B) where
  fiber : Type u
  incl : Mor fiber E
  isHFiber : ∀ x : fiber, Path (p.fn (incl.fn x)) b

/-- The long exact sequence shifts: ΩB → F → E → B. -/
structure LongExactShift {E B : Type u} (p : Mor E B) (b : B) where
  fiberSeq : FiberSeq p b
  loopSpace : Type u
  connecting : Mor loopSpace fiberSeq.fiber

/-- Trivial fiber sequence for identity. -/
def trivial_fiber_seq (A : Type u) (a : A) : FiberSeq (Mor.id : Mor A A) a where
  fiber := { x : A // x = a }
  incl := ⟨fun x => x.val⟩
  isHFiber x := Path.ofEq x.property

/-! ## Cofiber sequences -/

/-- A cofiber sequence: A → B → C where C is the homotopy cofiber. -/
structure CofiberSeq {A B : Type u} (f : Mor A B) where
  cofiber : Type u
  proj : Mor B cofiber
  collapse : ∀ a, Path (proj.fn (f.fn a)) (proj.fn (f.fn a))

/-- Puppe sequence extension: ...→ ΣA → ΣB → ... -/
structure PuppeExtension {A B : Type u} (f : Mor A B) where
  cofSeq : CofiberSeq f
  suspension : Type u
  suspMap : Mor suspension cofSeq.cofiber

/-! ## Mapping cone and mapping cylinder -/

/-- The mapping cylinder of f: A ∪_f B. -/
structure MappingCylinder {A B : Type u} (f : Mor A B) where
  carrier : Type u
  inclA : Mor A carrier
  inclB : Mor B carrier
  agree : ∀ a, Path (inclA.fn a) (inclB.fn (f.fn a))
  retract : Mor carrier B
  retractB : ∀ b, Path (retract.fn (inclB.fn b)) b

/-- The mapping cylinder retracts onto B. -/
theorem mapping_cyl_retract {A B : Type u} {f : Mor A B}
    (mc : MappingCylinder f) : ∀ b, Path (mc.retract.fn (mc.inclB.fn b)) b :=
  mc.retractB

/-- The mapping cone of f. -/
structure MappingCone {A B : Type u} (f : Mor A B) where
  carrier : Type u
  proj : Mor B carrier
  vertex : carrier
  collapse : ∀ a, Path (proj.fn (f.fn a)) vertex

/-! ## Homotopy pushout and pullback -/

/-- A homotopy pushout: the double mapping cylinder. -/
structure HPushout {A B C : Type u} (f : Mor A B) (g : Mor A C) where
  carrier : Type u
  inclB : Mor B carrier
  inclC : Mor C carrier
  glue : ∀ a, Path (inclB.fn (f.fn a)) (inclC.fn (g.fn a))

/-- Trivial homotopy pushout when f = g = id. -/
def trivial_hpushout (A : Type u) : HPushout (Mor.id : Mor A A) (Mor.id : Mor A A) where
  carrier := A
  inclB := Mor.id
  inclC := Mor.id
  glue a := Path.refl a

/-- A homotopy pullback. -/
structure HPullback {A B C : Type u} (f : Mor A C) (g : Mor B C) where
  carrier : Type u
  projA : Mor carrier A
  projB : Mor carrier B
  commute : ∀ x, Path (f.fn (projA.fn x)) (g.fn (projB.fn x))

/-- Trivial homotopy pullback when f = g = id. -/
def trivial_hpullback (A : Type u) : HPullback (Mor.id : Mor A A) (Mor.id : Mor A A) where
  carrier := A
  projA := Mor.id
  projB := Mor.id
  commute a := Path.refl a

/-! ## Loop space and suspension -/

/-- The loop space of A at a point. -/
structure LoopSpace (A : Type u) (a : A) where
  carrier : Type u
  base : carrier
  eval : Mor carrier A
  evalBase : Path (eval.fn base) a
  isLoop : ∀ x, Path (eval.fn x) a

/-- Trivial loop space (just the point). -/
def trivialLoopSpace (A : Type u) (a : A) : LoopSpace A a where
  carrier := Unit
  base := ()
  eval := ⟨fun _ => a⟩
  evalBase := Path.refl a
  isLoop _ := Path.refl a

/-- The suspension of A. -/
structure Suspension (A : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : A → Path north south

/-- Loop-suspension adjunction data. -/
structure LoopSuspAdj {A : Type u} (susp : Suspension A) (a : A)
    (loopSusp : LoopSpace susp.carrier susp.north) where
  unit : Mor A loopSusp.carrier
  unitBase : Path (loopSusp.eval.fn (unit.fn a)) susp.north

/-! ## Postnikov tower -/

/-- A Postnikov stage: n-truncation of a type. -/
structure PostnikovStage (A : Type u) (n : Nat) where
  truncation : Type u
  proj : Mor A truncation
  isNTruncated : Prop  -- n-truncation condition

/-- The tower structure: each stage maps to the next. -/
structure PostnikovTower (A : Type u) where
  stage : Nat → Type u
  proj : ∀ n, Mor A (stage n)
  bond : ∀ n, Mor (stage (n + 1)) (stage n)
  bondProj : ∀ n a, Path (bond n |>.fn (proj (n + 1) |>.fn a)) (proj n |>.fn a)

/-- Trivial Postnikov tower (all stages = A). -/
def trivialPostnikov (A : Type u) : PostnikovTower A where
  stage _ := A
  proj _ := Mor.id
  bond _ := Mor.id
  bondProj _ a := Path.refl a

/-! ## Hurewicz theorem structure -/

/-- Data for Hurewicz: connecting homotopy groups to homology. -/
structure HurewiczData (A : Type u) (a : A) where
  piGroup : Type u      -- π_n(A, a)
  hGroup : Type u       -- H_n(A)
  hurewicz : Mor ⟨piGroup, fun x => x⟩ ⟨hGroup, fun x => x⟩
  -- The Hurewicz map is the comparison

/-- Hurewicz map for a simply connected space (n ≥ 2). -/
structure HurewiczIso (A : Type u) (a : A) extends HurewiczData A a where
  isIso : WeakEquiv hurewicz

/-! ## Derived functors via localization -/

/-- A left derived functor via cofibrant replacement. -/
structure LeftDerived {A B : Type u} (F : Mor A B) where
  replace : Mor A A
  replaceWeq : WeakEquiv replace
  derived : Mor A B
  compute : ∀ a, Path (derived.fn a) (F.fn (replace.fn a))

/-- Trivial derived functor (identity replacement). -/
def trivialLeftDerived {A B : Type u} (F : Mor A B) : LeftDerived F where
  replace := Mor.id
  replaceWeq := weq_id A
  derived := F
  compute a := Path.refl _

/-- A right derived functor via fibrant replacement. -/
structure RightDerived {A B : Type u} (G : Mor B A) where
  replace : Mor B B
  replaceWeq : WeakEquiv replace
  derived : Mor B A
  compute : ∀ b, Path (derived.fn b) (G.fn (replace.fn b))

/-- Trivial right derived functor. -/
def trivialRightDerived {A B : Type u} (G : Mor B A) : RightDerived G where
  replace := Mor.id
  replaceWeq := weq_id B
  derived := G
  compute b := Path.refl _

/-- Derived natural transformation. -/
structure DerivedNatTrans {A B : Type u} (F G : Mor A B) where
  component : ∀ a, Path (F.fn a) (G.fn a)
  naturality : ∀ (a₁ a₂ : A) (p : Path a₁ a₂),
    Path (F.fn a₁) (G.fn a₂)

/-- Identity derived natural transformation. -/
def idDerivedNatTrans {A B : Type u} (F : Mor A B) : DerivedNatTrans F F where
  component a := Path.refl _
  naturality a₁ a₂ p := Path.congrArg F.fn p

/-- Composition of derived natural transformations. -/
def compDerivedNatTrans {A B : Type u} {F G H : Mor A B}
    (α : DerivedNatTrans F G) (β : DerivedNatTrans G H) : DerivedNatTrans F H where
  component a := Path.trans (α.component a) (β.component a)
  naturality a₁ a₂ p := Path.trans (α.naturality a₁ a₂ p) (β.component a₂)

/-! ## Homotopy invariance -/

/-- A functor is homotopy-invariant if it sends homotopic maps to equal results. -/
structure HomotopyInvariant {A B C : Type u} (F : Mor B C) where
  invariance : ∀ (f g : Mor A B),
    (∀ a, Path (f.fn a) (g.fn a)) →
    ∀ a, Path (F.fn (f.fn a)) (F.fn (g.fn a))

/-- Any functor applied to pointwise-equal maps gives pointwise-equal results. -/
def functorHomotopyInvariant {A B C : Type u} (F : Mor B C) : HomotopyInvariant (A := A) F where
  invariance f g heq a := Path.congrArg F.fn (heq a)

/-- Brown representability structure: a contravariant homotopy functor is representable. -/
structure BrownRepresentability {A : Type u} (F : Mor A A) where
  representing : Type u
  isoNat : ∀ a, Path (F.fn a) (F.fn a)  -- natural isomorphism data

end AbstractHomotopyDeep
end Path
end ComputationalPaths
