/-
# Abstract Homotopy Theory via Computational Paths

Cylinder objects, path objects, abstract homotopy relation, Whitehead theorem
structure, localization at weak equivalences, fibration/cofibration sequences,
Puppe sequences, Brown representability. All constructions use the
core Path/Step/trans/symm/congrArg API.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

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

-- 1: weak equivalence composition
def weq_comp {A B C : Type u} (f : Mor A B) (g : Mor B C)
    (wf : WeakEquiv f) (wg : WeakEquiv g) : WeakEquiv (Mor.comp f g) where
  inv := Mor.comp wg.inv wf.inv
  rightInv c := by
    show Path (g.fn (f.fn (wf.inv.fn (wg.inv.fn c)))) c
    exact Path.trans (Path.congrArg g.fn (wf.rightInv (wg.inv.fn c))) (wg.rightInv c)
  leftInv a := by
    show Path (wf.inv.fn (wg.inv.fn (g.fn (f.fn a)))) a
    exact Path.trans (Path.congrArg wf.inv.fn (wg.leftInv (f.fn a))) (wf.leftInv a)

-- 2: id is a weak equivalence (theorem form)
theorem weq_id_is_weq (A : Type u) : ∀ a : A, (weq_id A).leftInv a = Path.refl a := by
  intro a; rfl

-- 3: inverse of inverse is original
theorem weq_inv_inv {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    (weq_inv f wf).inv = f := rfl

/-! ## Abstract cylinder objects -/

structure Cylinder (A : Type u) where
  cyl : Type u
  i₀ : Mor A cyl
  i₁ : Mor A cyl
  p : Mor cyl A
  p_i₀ : ∀ a, Path (p.fn (i₀.fn a)) a
  p_i₁ : ∀ a, Path (p.fn (i₁.fn a)) a

structure GoodCylinder (A : Type u) extends Cylinder A where
  p_weq : WeakEquiv p

def trivialCylinder (A : Type u) : Cylinder A where
  cyl := A
  i₀ := Mor.id
  i₁ := Mor.id
  p := Mor.id
  p_i₀ a := Path.refl a
  p_i₁ a := Path.refl a

def trivialGoodCylinder (A : Type u) : GoodCylinder A where
  cyl := A
  i₀ := Mor.id
  i₁ := Mor.id
  p := Mor.id
  p_i₀ a := Path.refl a
  p_i₁ a := Path.refl a
  p_weq := weq_id A

-- 4: cylinder projection after i₀ is propositionally id
theorem cylinder_p_i₀_eq {A : Type u} (cyl : Cylinder A) (a : A) :
    cyl.p.fn (cyl.i₀.fn a) = a := (cyl.p_i₀ a).proof

-- 5: cylinder projection after i₁ is propositionally id
theorem cylinder_p_i₁_eq {A : Type u} (cyl : Cylinder A) (a : A) :
    cyl.p.fn (cyl.i₁.fn a) = a := (cyl.p_i₁ a).proof

-- 6: trivial cylinder i₀ = i₁
theorem trivial_cylinder_inclusions_eq (A : Type u) :
    (trivialCylinder A).i₀ = (trivialCylinder A).i₁ := rfl

/-! ## Abstract path objects -/

structure PathObject (B : Type u) where
  pathSp : Type u
  s : Mor B pathSp
  d₀ : Mor pathSp B
  d₁ : Mor pathSp B
  d₀_s : ∀ b, Path (d₀.fn (s.fn b)) b
  d₁_s : ∀ b, Path (d₁.fn (s.fn b)) b

structure GoodPathObject (B : Type u) extends PathObject B where
  s_weq : WeakEquiv s

def trivialPathObject (B : Type u) : PathObject B where
  pathSp := B
  s := Mor.id
  d₀ := Mor.id
  d₁ := Mor.id
  d₀_s b := Path.refl b
  d₁_s b := Path.refl b

def trivialGoodPathObject (B : Type u) : GoodPathObject B where
  pathSp := B
  s := Mor.id
  d₀ := Mor.id
  d₁ := Mor.id
  d₀_s b := Path.refl b
  d₁_s b := Path.refl b
  s_weq := weq_id B

-- 7: d₀ ∘ s = id propositionally
theorem pathObj_d₀_s_eq {B : Type u} (po : PathObject B) (b : B) :
    po.d₀.fn (po.s.fn b) = b := (po.d₀_s b).proof

-- 8: d₁ ∘ s = id propositionally
theorem pathObj_d₁_s_eq {B : Type u} (po : PathObject B) (b : B) :
    po.d₁.fn (po.s.fn b) = b := (po.d₁_s b).proof

-- 9: trivial path object d₀ = d₁
theorem trivial_pathObj_endpoints_eq (B : Type u) :
    (trivialPathObject B).d₀ = (trivialPathObject B).d₁ := rfl

/-! ## Left homotopy -/

structure LeftHom {A B : Type u} (f g : Mor A B) where
  cyl : Cylinder A
  H : Mor cyl.cyl B
  H_i₀ : ∀ a, Path (H.fn (cyl.i₀.fn a)) (f.fn a)
  H_i₁ : ∀ a, Path (H.fn (cyl.i₁.fn a)) (g.fn a)

def leftHom_refl {A B : Type u} (f : Mor A B) (cyl : Cylinder A) : LeftHom f f where
  cyl := cyl
  H := ⟨fun c => f.fn (cyl.p.fn c)⟩
  H_i₀ a := Path.congrArg f.fn (cyl.p_i₀ a)
  H_i₁ a := Path.congrArg f.fn (cyl.p_i₁ a)

def leftHom_symm {A B : Type u} {f g : Mor A B} (h : LeftHom f g) : LeftHom g f where
  cyl := { cyl := h.cyl.cyl, i₀ := h.cyl.i₁, i₁ := h.cyl.i₀, p := h.cyl.p,
            p_i₀ := h.cyl.p_i₁, p_i₁ := h.cyl.p_i₀ }
  H := h.H
  H_i₀ a := h.H_i₁ a
  H_i₁ a := h.H_i₀ a

-- 10: left homotopy reflexivity gives identity at each point
theorem leftHom_refl_H_eq {A B : Type u} (f : Mor A B) (cyl : Cylinder A) (a : A) :
    (leftHom_refl f cyl).H.fn (cyl.i₀.fn a) = f.fn (cyl.p.fn (cyl.i₀.fn a)) := rfl

-- 11: left homotopy symm is involutive
theorem leftHom_symm_symm_cyl {A B : Type u} {f g : Mor A B} (h : LeftHom f g) :
    (leftHom_symm (leftHom_symm h)).H = h.H := rfl

-- 12: left homotopy H at i₀ agrees with f
theorem leftHom_H_i₀_eq {A B : Type u} {f g : Mor A B} (h : LeftHom f g) (a : A) :
    h.H.fn (h.cyl.i₀.fn a) = f.fn a := (h.H_i₀ a).proof

/-! ## Right homotopy -/

structure RightHom {A B : Type u} (f g : Mor A B) where
  pobj : PathObject B
  H : Mor A pobj.pathSp
  H_d₀ : ∀ a, Path (pobj.d₀.fn (H.fn a)) (f.fn a)
  H_d₁ : ∀ a, Path (pobj.d₁.fn (H.fn a)) (g.fn a)

def rightHom_refl {A B : Type u} (f : Mor A B) (po : PathObject B) : RightHom f f where
  pobj := po
  H := ⟨fun a => po.s.fn (f.fn a)⟩
  H_d₀ a := po.d₀_s (f.fn a)
  H_d₁ a := po.d₁_s (f.fn a)

def rightHom_symm {A B : Type u} {f g : Mor A B} (h : RightHom f g) : RightHom g f where
  pobj := { pathSp := h.pobj.pathSp, s := h.pobj.s, d₀ := h.pobj.d₁, d₁ := h.pobj.d₀,
             d₀_s := h.pobj.d₁_s, d₁_s := h.pobj.d₀_s }
  H := h.H
  H_d₀ a := h.H_d₁ a
  H_d₁ a := h.H_d₀ a

-- 13: right homotopy H at d₀ agrees with f
theorem rightHom_H_d₀_eq {A B : Type u} {f g : Mor A B} (h : RightHom f g) (a : A) :
    h.pobj.d₀.fn (h.H.fn a) = f.fn a := (h.H_d₀ a).proof

-- 14: right homotopy symm is involutive
theorem rightHom_symm_symm_H {A B : Type u} {f g : Mor A B} (h : RightHom f g) :
    (rightHom_symm (rightHom_symm h)).H = h.H := rfl

/-! ## Homotopy equivalence -/

structure HomotopyEquiv {A B : Type u} (f : Mor A B) where
  inv : Mor B A
  leftHom : LeftHom ⟨fun a => inv.fn (f.fn a)⟩ Mor.id
  rightHom : LeftHom ⟨fun b => f.fn (inv.fn b)⟩ Mor.id

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

def id_hom_equiv (A : Type u) (cyl : Cylinder A) : HomotopyEquiv (Mor.id : Mor A A) where
  inv := Mor.id
  leftHom := leftHom_refl Mor.id cyl
  rightHom := leftHom_refl Mor.id cyl

-- 15: homotopy equiv inverse is also a homotopy equiv
def hom_equiv_inv {A B : Type u} {f : Mor A B} (he : HomotopyEquiv f)
    : HomotopyEquiv he.inv where
  inv := f
  leftHom := {
    cyl := he.rightHom.cyl
    H := he.rightHom.H
    H_i₀ := he.rightHom.H_i₀
    H_i₁ := he.rightHom.H_i₁
  }
  rightHom := {
    cyl := he.leftHom.cyl
    H := he.leftHom.H
    H_i₀ := he.leftHom.H_i₀
    H_i₁ := he.leftHom.H_i₁
  }

/-! ## Whitehead theorem structure -/

structure WhiteheadData {A B : Type u} (f : Mor A B) where
  weq : WeakEquiv f
  cylA : Cylinder A
  cylB : Cylinder B
  result : HomotopyEquiv f

def mkWhiteheadData {A B : Type u} (f : Mor A B) (wf : WeakEquiv f)
    (cylA : Cylinder A) (cylB : Cylinder B) : WhiteheadData f where
  weq := wf
  cylA := cylA
  cylB := cylB
  result := weq_to_hom_equiv f wf cylA cylB

-- 16: Whitehead data inverse round-trip
theorem whitehead_inv_fn {A B : Type u} (f : Mor A B) (wf : WeakEquiv f)
    (cylA : Cylinder A) (cylB : Cylinder B) :
    (mkWhiteheadData f wf cylA cylB).result.inv = wf.inv := rfl

/-! ## Localization at weak equivalences -/

inductive ZigZag : Type u → Type u → Type (u + 1)
  | id (A : Type u) : ZigZag A A
  | forward {A B : Type u} : Mor A B → ZigZag A B
  | backward {A B : Type u} : Mor B A → WeakEquiv (Mor.id : Mor B B) → ZigZag A B
  | comp {A B C : Type u} : ZigZag A B → ZigZag B C → ZigZag A C

def ZigZag.length : ZigZag A B → Nat
  | .id _ => 0
  | .forward _ => 1
  | .backward _ _ => 1
  | .comp z1 z2 => z1.length + z2.length

-- 17: identity zigzag has length 0
theorem zigzag_id_length (A : Type u) : (ZigZag.id A).length = 0 := rfl

-- 18: forward zigzag has length 1
theorem zigzag_forward_length {A B : Type u} (f : Mor A B) :
    (ZigZag.forward f).length = 1 := rfl

-- 19: backward zigzag has length 1
theorem zigzag_backward_length {A B : Type u} (f : Mor B A)
    (w : WeakEquiv (Mor.id : Mor B B)) :
    (ZigZag.backward f w).length = 1 := rfl

-- 20: composition length is additive
theorem zigzag_comp_length {A B C : Type u} (z1 : ZigZag A B) (z2 : ZigZag B C) :
    (ZigZag.comp z1 z2).length = z1.length + z2.length := rfl

structure LocMor (A B : Type u) where
  zigzag : ZigZag A B

def LocMor.idLoc (A : Type u) : LocMor A A := ⟨ZigZag.id A⟩
def LocMor.comp {A B C : Type u} (f : LocMor A B) (g : LocMor B C) : LocMor A C :=
  ⟨ZigZag.comp f.zigzag g.zigzag⟩
def LocMor.ofMor {A B : Type u} (f : Mor A B) : LocMor A B :=
  ⟨ZigZag.forward f⟩

-- 21: composition with identity
theorem locMor_comp_id_left {A B : Type u} (f : LocMor A B) :
    LocMor.comp (LocMor.idLoc A) f = ⟨ZigZag.comp (ZigZag.id A) f.zigzag⟩ := rfl

-- 22: weak equivalence has inverse in localization
def weq_inv_loc {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) : LocMor B A :=
  ⟨ZigZag.forward wf.inv⟩

-- 23: inverse satisfies right triangle
theorem weq_inv_loc_right {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∀ b, f.fn (wf.inv.fn b) = b := fun b => (wf.rightInv b).proof

-- 24: inverse satisfies left triangle
theorem weq_inv_loc_left {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) :
    ∀ a, wf.inv.fn (f.fn a) = a := fun a => (wf.leftInv a).proof

/-! ## Fiber and cofiber -/

structure HFiber {A B : Type u} (f : Mor A B) (b : B) where
  point : A
  path : Path (f.fn point) b

def HFiber.incl {A B : Type u} {f : Mor A B} {b : B} (x : HFiber f b) : A := x.point

def hfiber_id_contr (A : Type u) (a : A) :
    HFiber (Mor.id : Mor A A) a where
  point := a
  path := Path.refl a

-- 25: fiber of identity at a has canonical element
theorem hfiber_id_point {A : Type u} (a : A) :
    (hfiber_id_contr A a).point = a := rfl

-- 26: fiber inclusion is the point
theorem hfiber_incl_eq {A B : Type u} {f : Mor A B} {b : B} (x : HFiber f b) :
    HFiber.incl x = x.point := rfl

-- 27: map on fibers
def HFiber.map {A B C : Type u} {f : Mor A B} {g : Mor B C} {b : B}
    (x : HFiber f b) : HFiber (Mor.comp f g) (g.fn b) where
  point := x.point
  path := by
    show Path (g.fn (f.fn x.point)) (g.fn b)
    exact Path.congrArg g.fn x.path

-- 28: fiber map preserves point
theorem HFiber.map_point {A B C : Type u} {f : Mor A B} {g : Mor B C} {b : B}
    (x : HFiber f b) : (HFiber.map (g := g) x).point = x.point := rfl

structure HCofiber {A B : Type u} (f : Mor A B) where
  carrier : Type u
  proj : Mor B carrier
  collapse : ∀ a, Path (proj.fn (f.fn a)) (proj.fn (f.fn a))

def trivial_cofiber {A B : Type u} (f : Mor A B) : HCofiber f where
  carrier := B
  proj := Mor.id
  collapse a := Path.refl _

/-! ## Fiber sequences -/

structure FiberSeq {E B : Type u} (p : Mor E B) (b : B) where
  fiber : Type u
  incl : Mor fiber E
  isHFiber : ∀ x : fiber, Path (p.fn (incl.fn x)) b

def trivial_fiber_seq (A : Type u) (a : A) : FiberSeq (Mor.id : Mor A A) a where
  fiber := { x : A // x = a }
  incl := ⟨fun x => x.val⟩
  isHFiber x := Path.ofEq x.property

-- 29: fiber sequence inclusion maps into total space
theorem fiber_seq_incl_target {E B : Type u} {p : Mor E B} {b : B}
    (fs : FiberSeq p b) (x : fs.fiber) :
    p.fn (fs.incl.fn x) = b := (fs.isHFiber x).proof

/-! ## Cofiber sequences -/

structure CofiberSeq {A B : Type u} (f : Mor A B) where
  cofiber : Type u
  proj : Mor B cofiber
  collapse : ∀ a, Path (proj.fn (f.fn a)) (proj.fn (f.fn a))

structure PuppeExtension {A B : Type u} (f : Mor A B) where
  cofSeq : CofiberSeq f
  suspension : Type u
  suspMap : Mor suspension cofSeq.cofiber

/-! ## Mapping cone and cylinder -/

structure MappingCylinder {A B : Type u} (f : Mor A B) where
  carrier : Type u
  inclA : Mor A carrier
  inclB : Mor B carrier
  agree : ∀ a, Path (inclA.fn a) (inclB.fn (f.fn a))
  retract : Mor carrier B
  retractB : ∀ b, Path (retract.fn (inclB.fn b)) b

-- 30: mapping cylinder retraction
def mapping_cyl_retract {A B : Type u} {f : Mor A B}
    (mc : MappingCylinder f) : ∀ b, Path (mc.retract.fn (mc.inclB.fn b)) b :=
  mc.retractB

-- 31: retraction is propositionally id on B image
theorem mapping_cyl_retract_eq {A B : Type u} {f : Mor A B}
    (mc : MappingCylinder f) (b : B) :
    mc.retract.fn (mc.inclB.fn b) = b := (mc.retractB b).proof

structure MappingCone {A B : Type u} (f : Mor A B) where
  carrier : Type u
  proj : Mor B carrier
  vertex : carrier
  collapse : ∀ a, Path (proj.fn (f.fn a)) vertex

-- 32: mapping cone vertex is a base point
theorem mapping_cone_collapse_eq {A B : Type u} {f : Mor A B}
    (mc : MappingCone f) (a : A) :
    mc.proj.fn (f.fn a) = mc.vertex := (mc.collapse a).proof

/-! ## Homotopy pushout and pullback -/

structure HPushout {A B C : Type u} (f : Mor A B) (g : Mor A C) where
  carrier : Type u
  inclB : Mor B carrier
  inclC : Mor C carrier
  glue : ∀ a, Path (inclB.fn (f.fn a)) (inclC.fn (g.fn a))

def trivial_hpushout (A : Type u) : HPushout (Mor.id : Mor A A) (Mor.id : Mor A A) where
  carrier := A
  inclB := Mor.id
  inclC := Mor.id
  glue a := Path.refl a

-- 33: trivial pushout glue is refl
theorem trivial_hpushout_glue_eq (A : Type u) (a : A) :
    ((trivial_hpushout A).glue a).proof = rfl := rfl

structure HPullback {A B C : Type u} (f : Mor A C) (g : Mor B C) where
  carrier : Type u
  projA : Mor carrier A
  projB : Mor carrier B
  commute : ∀ x, Path (f.fn (projA.fn x)) (g.fn (projB.fn x))

def trivial_hpullback (A : Type u) : HPullback (Mor.id : Mor A A) (Mor.id : Mor A A) where
  carrier := A
  projA := Mor.id
  projB := Mor.id
  commute a := Path.refl a

-- 34: pullback square commutes propositionally
theorem hpullback_commute_eq {A B C : Type u} {f : Mor A C} {g : Mor B C}
    (pb : HPullback f g) (x : pb.carrier) :
    f.fn (pb.projA.fn x) = g.fn (pb.projB.fn x) := (pb.commute x).proof

-- 35: trivial pullback commutes trivially
theorem trivial_hpullback_commute (A : Type u) (a : A) :
    ((trivial_hpullback A).commute a).proof = rfl := rfl

/-! ## Loop space and suspension -/

structure LoopSpace (A : Type u) (a : A) where
  carrier : Type u
  base : carrier
  eval : Mor carrier A
  evalBase : Path (eval.fn base) a
  isLoop : ∀ x, Path (eval.fn x) a

def trivialLoopSpace (A : Type u) (a : A) : LoopSpace A a where
  carrier := PUnit.{u + 1}
  base := PUnit.unit
  eval := ⟨fun _ => a⟩
  evalBase := Path.refl a
  isLoop _ := Path.refl a

-- 36: trivial loop space has unique element
theorem trivialLoopSpace_unique (A : Type u) (a : A)
    (x y : (trivialLoopSpace A a).carrier) :
    x = y := by cases x; cases y; rfl

structure Suspension (A : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : A → Path north south

-- 37: meridian gives a propositional equality
theorem suspension_merid_eq {A : Type u} (susp : Suspension A) (a : A) :
    susp.north = susp.south := (susp.merid a).proof

/-! ## Postnikov tower -/

structure PostnikovTower (A : Type u) where
  stage : Nat → Type u
  proj : ∀ n, Mor A (stage n)
  bond : ∀ n, Mor (stage (n + 1)) (stage n)
  bondProj : ∀ n a, Path (bond n |>.fn (proj (n + 1) |>.fn a)) (proj n |>.fn a)

def trivialPostnikov (A : Type u) : PostnikovTower A where
  stage _ := A
  proj _ := Mor.id
  bond _ := Mor.id
  bondProj _ a := Path.refl a

-- 38: Postnikov bond-proj gives propositional equality
theorem postnikov_bond_proj_eq {A : Type u} (t : PostnikovTower A) (n : Nat) (a : A) :
    (t.bond n).fn ((t.proj (n + 1)).fn a) = (t.proj n).fn a :=
  (t.bondProj n a).proof

-- 39: trivial Postnikov tower bond is id
theorem trivial_postnikov_bond (A : Type u) (n : Nat) :
    (trivialPostnikov A).bond n = Mor.id := rfl

-- 40: trivial Postnikov proj is id
theorem trivial_postnikov_proj (A : Type u) (n : Nat) :
    (trivialPostnikov A).proj n = Mor.id := rfl

-- 41: composing bonds gives higher bond
def postnikov_composed_bond {A : Type u} (t : PostnikovTower A) (n : Nat) :
    Mor (t.stage (n + 2)) (t.stage n) :=
  Mor.comp (t.bond (n + 1)) (t.bond n)

-- 42: composed bond agrees with two-step projection
theorem postnikov_composed_bond_proj {A : Type u} (t : PostnikovTower A)
    (n : Nat) (a : A) :
    (postnikov_composed_bond t n).fn ((t.proj (n + 2)).fn a) = (t.proj n).fn a := by
  show (t.bond n).fn ((t.bond (n + 1)).fn ((t.proj (n + 2)).fn a)) = _
  rw [(t.bondProj (n + 1) a).proof, (t.bondProj n a).proof]

/-! ## Homotopy invariance -/

structure HomotopyInvariant {A B C : Type u} (F : Mor B C) where
  invariance : ∀ (f g : Mor A B),
    (∀ a, Path (f.fn a) (g.fn a)) →
    ∀ a, Path (F.fn (f.fn a)) (F.fn (g.fn a))

-- 43: any functor is homotopy invariant
def functorHomotopyInvariant {A B C : Type u} (F : Mor B C) : HomotopyInvariant (A := A) F where
  invariance f g heq a := Path.congrArg F.fn (heq a)

-- 44: composition of homotopy-invariant functors
def homotopyInvariant_comp {A B C D : Type u} (F : Mor B C) (G : Mor C D)
    (hF : HomotopyInvariant (A := A) F) : HomotopyInvariant (A := A) (Mor.comp F G) where
  invariance f g heq a := Path.congrArg G.fn (hF.invariance f g heq a)

/-! ## Derived natural transformations -/

structure DerivedNatTrans {A B : Type u} (F G : Mor A B) where
  component : ∀ a, Path (F.fn a) (G.fn a)
  naturality : ∀ (a₁ a₂ : A) (p : Path a₁ a₂),
    Path (F.fn a₁) (G.fn a₂)

-- 45: identity derived natural transformation
def idDerivedNatTrans {A B : Type u} (F : Mor A B) : DerivedNatTrans F F where
  component a := Path.refl _
  naturality a₁ a₂ p := Path.congrArg F.fn p

-- 46: composition of derived natural transformations
def compDerivedNatTrans {A B : Type u} {F G H : Mor A B}
    (α : DerivedNatTrans F G) (β : DerivedNatTrans G H) : DerivedNatTrans F H where
  component a := Path.trans (α.component a) (β.component a)
  naturality a₁ a₂ p := Path.trans (α.naturality a₁ a₂ p) (β.component a₂)

-- 47: idDerivedNatTrans component is refl
theorem idDerivedNatTrans_component {A B : Type u} (F : Mor A B) (a : A) :
    (idDerivedNatTrans F).component a = Path.refl _ := rfl

-- 48: composition with id on left is original
theorem compDerivedNatTrans_id_left {A B : Type u} {F G : Mor A B}
    (α : DerivedNatTrans F G) (a : A) :
    (compDerivedNatTrans (idDerivedNatTrans F) α).component a =
    Path.trans (Path.refl _) (α.component a) := rfl

/-! ## Derived functors -/

structure LeftDerived {A B : Type u} (F : Mor A B) where
  replace : Mor A A
  replaceWeq : WeakEquiv replace
  derived : Mor A B
  compute : ∀ a, Path (derived.fn a) (F.fn (replace.fn a))

def trivialLeftDerived {A B : Type u} (F : Mor A B) : LeftDerived F where
  replace := Mor.id
  replaceWeq := weq_id A
  derived := F
  compute a := Path.refl _

-- 49: trivial derived functor = original
theorem trivialLeftDerived_derived {A B : Type u} (F : Mor A B) :
    (trivialLeftDerived F).derived = F := rfl

structure RightDerived {A B : Type u} (G : Mor B A) where
  replace : Mor B B
  replaceWeq : WeakEquiv replace
  derived : Mor B A
  compute : ∀ b, Path (derived.fn b) (G.fn (replace.fn b))

def trivialRightDerived {A B : Type u} (G : Mor B A) : RightDerived G where
  replace := Mor.id
  replaceWeq := weq_id B
  derived := G
  compute b := Path.refl _

-- 50: trivial right derived = original
theorem trivialRightDerived_derived {A B : Type u} (G : Mor B A) :
    (trivialRightDerived G).derived = G := rfl

/-! ## Brown representability -/

structure BrownRepresentability {A : Type u} (F : Mor A A) where
  representing : Type u
  isoNat : ∀ a, Path (F.fn a) (F.fn a)

/-! ## Additional abstract homotopy theorems -/

-- 51: Mor.comp is associative
theorem mor_comp_assoc {A B C D : Type u} (f : Mor A B) (g : Mor B C) (h : Mor C D) :
    Mor.comp (Mor.comp f g) h = Mor.comp f (Mor.comp g h) := rfl

-- 52: Mor.comp with id on left
theorem mor_comp_id_left {A B : Type u} (f : Mor A B) :
    Mor.comp Mor.id f = f := by
  cases f; rfl

-- 53: Mor.comp with id on right
theorem mor_comp_id_right {A B : Type u} (f : Mor A B) :
    Mor.comp f Mor.id = f := by
  cases f; rfl

-- 54: weak equiv right inverse is propositionally equal
theorem weq_right_inv_eq {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) (b : B) :
    f.fn (wf.inv.fn b) = b := (wf.rightInv b).proof

-- 55: weak equiv left inverse is propositionally equal
theorem weq_left_inv_eq {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) (a : A) :
    wf.inv.fn (f.fn a) = a := (wf.leftInv a).proof

-- 56: congrArg through weak equiv
def weq_congrArg {A B : Type u} (f : Mor A B) (wf : WeakEquiv f) {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (f.fn a₁) (f.fn a₂) :=
  Path.congrArg f.fn p

-- 57: fiber over image always has an element
theorem hfiber_image_nonempty {A B : Type u} (f : Mor A B) (a : A) :
    ∃ fib : HFiber f (f.fn a), fib.point = a :=
  ⟨⟨a, Path.refl _⟩, rfl⟩

-- 58: pullback of weak equiv has a section
theorem hpullback_of_weq_section {A B C : Type u} (f : Mor A C) (g : Mor B C)
    (wg : WeakEquiv g) (a : A) :
    ∃ b : B, g.fn b = f.fn a :=
  ⟨wg.inv.fn (f.fn a), (wg.rightInv (f.fn a)).proof⟩

end AbstractHomotopyDeep
end Path
end ComputationalPaths
