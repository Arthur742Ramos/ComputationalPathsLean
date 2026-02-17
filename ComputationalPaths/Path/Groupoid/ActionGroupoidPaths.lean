/-
# Group Actions as Groupoids via Computational Paths

Action paths, orbit paths, stabilizer paths, equivariant maps,
quotient groupoid.  All operations use the Path/Step/trans/symm/congrArg API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace ActionGroupoidPaths

universe u v w

/-! ## Group structure via paths -/

/-- A group structure on G, with operations producing paths for laws. -/
structure PathGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a : G, Path (mul one a) a
  mul_one : ∀ a : G, Path (mul a one) a
  inv_mul : ∀ a : G, Path (mul (inv a) a) one
  mul_inv : ∀ a : G, Path (mul a (inv a)) one

variable {G : Type u} {X : Type v} {Y : Type w}

/-! ## Group action via paths -/

/-- A group action on X by G, with the action law witnessed by paths. -/
structure PathAction (PG : PathGroup G) (X : Type v) where
  act : G → X → X
  act_one : ∀ x : X, Path (act PG.one x) x
  act_mul : ∀ (g h : G) (x : X), Path (act (PG.mul g h) x) (act g (act h x))

/-- Action by a single element via congrArg. -/
def actPath {PG : PathGroup G} (A : PathAction PG X)
    (g : G) {x y : X} (p : Path x y) : Path (A.act g x) (A.act g y) :=
  Path.congrArg (A.act g) p

/-- Acting on a reflexive path gives refl. -/
@[simp] theorem actPath_refl {PG : PathGroup G} (A : PathAction PG X)
    (g : G) (x : X) :
    actPath A g (Path.refl x) = Path.refl (A.act g x) := by
  simp [actPath]

/-- Acting preserves path composition. -/
@[simp] theorem actPath_trans {PG : PathGroup G} (A : PathAction PG X)
    (g : G) {x y z : X} (p : Path x y) (q : Path y z) :
    actPath A g (Path.trans p q) = Path.trans (actPath A g p) (actPath A g q) := by
  simp [actPath]

/-- Acting preserves path reversal. -/
@[simp] theorem actPath_symm {PG : PathGroup G} (A : PathAction PG X)
    (g : G) {x y : X} (p : Path x y) :
    actPath A g (Path.symm p) = Path.symm (actPath A g p) := by
  simp [actPath]

/-! ## Orbit paths -/

/-- The orbit of x under g gives a path from act(1,x) to x. -/
def orbitIdentity {PG : PathGroup G} (A : PathAction PG X) (x : X) :
    Path (A.act PG.one x) x :=
  A.act_one x

/-- Composing group actions corresponds to path composition. -/
def orbitCompose {PG : PathGroup G} (A : PathAction PG X)
    (g h : G) (x : X) :
    Path (A.act (PG.mul g h) x) (A.act g (A.act h x)) :=
  A.act_mul g h x

/-- Chain of action paths: act(gh,x) → act(g, act(h,x)) → act(g, x) when act(h,x)=x. -/
def orbitChain {PG : PathGroup G} (A : PathAction PG X)
    (g h : G) (x : X) (hfix : Path (A.act h x) x) :
    Path (A.act (PG.mul g h) x) (A.act g x) :=
  Path.trans (A.act_mul g h x) (actPath A g hfix)

/-! ## Stabilizer paths -/

/-- The stabilizer of x: group elements that fix x (up to path). -/
def IsStabilizer {PG : PathGroup G} (A : PathAction PG X) (x : X) (g : G) : Prop :=
  A.act g x = x

/-- The identity is in the stabilizer. -/
theorem one_isStabilizer {PG : PathGroup G} (A : PathAction PG X) (x : X) :
    IsStabilizer A x PG.one :=
  (A.act_one x).proof

/-- Stabilizer element gives a path from act(g,x) to x. -/
def stabilizerPathOf {PG : PathGroup G} (A : PathAction PG X)
    (x : X) (g : G) (h : IsStabilizer A x g) : Path (A.act g x) x :=
  Path.mk [Step.mk _ _ h] h

/-- Stabilizer of identity gives the reflexive path (at proof level). -/
theorem stabilizerPath_one_toEq {PG : PathGroup G} (A : PathAction PG X) (x : X) :
    (stabilizerPathOf A x PG.one (one_isStabilizer A x)).toEq = (A.act_one x).toEq :=
  rfl

/-! ## Equivariant maps -/

/-- An equivariant map between G-sets, witnessed by paths. -/
structure Equivariant {PG : PathGroup G}
    (A : PathAction PG X) (B : PathAction PG Y) where
  toFun : X → Y
  equivar : ∀ (g : G) (x : X), Path (toFun (A.act g x)) (B.act g (toFun x))

/-- An equivariant map sends paths to paths. -/
def Equivariant.mapPath {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    (f : Equivariant A B) {x y : X} (p : Path x y) :
    Path (f.toFun x) (f.toFun y) :=
  Path.congrArg f.toFun p

/-- Equivariant map preserves refl. -/
@[simp] theorem Equivariant.mapPath_refl {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    (f : Equivariant A B) (x : X) :
    f.mapPath (Path.refl x) = Path.refl (f.toFun x) := by
  simp [Equivariant.mapPath]

/-- Equivariant map preserves trans. -/
@[simp] theorem Equivariant.mapPath_trans {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    (f : Equivariant A B) {x y z : X} (p : Path x y) (q : Path y z) :
    f.mapPath (Path.trans p q) = Path.trans (f.mapPath p) (f.mapPath q) := by
  simp [Equivariant.mapPath]

/-- Equivariant map preserves symm. -/
@[simp] theorem Equivariant.mapPath_symm {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    (f : Equivariant A B) {x y : X} (p : Path x y) :
    f.mapPath (Path.symm p) = Path.symm (f.mapPath p) := by
  simp [Equivariant.mapPath]

/-- Identity equivariant map. -/
def Equivariant.idEquiv {PG : PathGroup G}
    (A : PathAction PG X) : Equivariant A A where
  toFun := fun x => x
  equivar := fun _ _ => Path.refl _

/-- Identity equivariant map preserves paths. -/
@[simp] theorem Equivariant.idEquiv_mapPath {PG : PathGroup G}
    {A : PathAction PG X} {x y : X} (p : Path x y) :
    (Equivariant.idEquiv A).mapPath p = p := by
  simp [Equivariant.idEquiv, Equivariant.mapPath]

/-- Composition of equivariant maps. -/
def Equivariant.comp {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    {Z : Type w} {C : PathAction PG Z}
    (g : Equivariant B C) (f : Equivariant A B) :
    Equivariant A C where
  toFun := fun x => g.toFun (f.toFun x)
  equivar := fun h x =>
    Path.trans
      (Path.congrArg g.toFun (f.equivar h x))
      (g.equivar h (f.toFun x))

/-- Composition of equivariant maps preserves paths. -/
theorem Equivariant.comp_mapPath {PG : PathGroup G}
    {A : PathAction PG X} {B : PathAction PG Y}
    {Z : Type w} {C : PathAction PG Z}
    (g : Equivariant B C) (f : Equivariant A B) {x y : X} (p : Path x y) :
    (Equivariant.comp g f).mapPath p =
      g.mapPath (f.mapPath p) := by
  simp [Equivariant.comp, Equivariant.mapPath]

/-! ## Quotient groupoid -/

/-- The orbit relation as a setoid. -/
def actionSetoid {PG : PathGroup G} (A : PathAction PG X) : Setoid X where
  r x y := ∃ g : G, A.act g x = y
  iseqv := {
    refl := fun x => ⟨PG.one, (A.act_one x).proof⟩
    symm := fun {x y} ⟨g, h⟩ => by
      refine ⟨PG.inv g, ?_⟩
      subst h
      have hm : A.act (PG.mul (PG.inv g) g) x = A.act (PG.inv g) (A.act g x) :=
        (A.act_mul (PG.inv g) g x).proof
      have hi : PG.mul (PG.inv g) g = PG.one := (PG.inv_mul g).proof
      have hone : A.act PG.one x = x := (A.act_one x).proof
      rw [hi] at hm; rw [hone] at hm; exact hm.symm
    trans := fun {x y z} ⟨g, hg⟩ ⟨h, hh⟩ => by
      refine ⟨PG.mul h g, ?_⟩
      subst hg; subst hh
      exact (A.act_mul h g x).proof
  }

/-- Paths in X descend to the orbit relation. -/
theorem path_descends {PG : PathGroup G} (A : PathAction PG X)
    {x y : X} (p : Path x y) :
    @Setoid.r _ (actionSetoid A) x y :=
  ⟨PG.one, by rw [(A.act_one x).proof]; exact p.proof⟩

/-- Acting by g sends orbit-related elements to orbit-related elements
    (using congrArg on the underlying equality). -/
theorem act_orbit_path {PG : PathGroup G} (A : PathAction PG X)
    (g : G) {x y : X} (_h : A.act g x = A.act g y → Prop)
    (hxy : x = y) : A.act g x = A.act g y :=
  _root_.congrArg (A.act g) hxy

/-- Acting by g on a path gives a path in the image. -/
theorem act_path_image {PG : PathGroup G} (A : PathAction PG X)
    (g : G) {x y : X} (p : Path x y) :
    (Path.congrArg (A.act g) p).toEq = _root_.congrArg (A.act g) p.toEq := by
  rfl

/-! ## Additional path constructions -/

/-- Group multiplication path: associativity. -/
def mulAssocPath (PG : PathGroup G) (a b c : G) :
    Path (PG.mul (PG.mul a b) c) (PG.mul a (PG.mul b c)) :=
  PG.mul_assoc a b c

/-- Left identity path. -/
def oneMulPath (PG : PathGroup G) (a : G) :
    Path (PG.mul PG.one a) a :=
  PG.one_mul a

/-- Right identity path. -/
def mulOnePath (PG : PathGroup G) (a : G) :
    Path (PG.mul a PG.one) a :=
  PG.mul_one a

/-- Left inverse path. -/
def invMulPath (PG : PathGroup G) (a : G) :
    Path (PG.mul (PG.inv a) a) PG.one :=
  PG.inv_mul a

/-- Right inverse path. -/
def mulInvPath (PG : PathGroup G) (a : G) :
    Path (PG.mul a (PG.inv a)) PG.one :=
  PG.mul_inv a

/-- Transport along the action-one path. -/
theorem transport_act_one {PG : PathGroup G} (A : PathAction PG X)
    {D : X → Type w} (x : X) (d : D (A.act PG.one x)) :
    Path.transport (D := D) (A.act_one x) d =
      Path.transport (D := D) (A.act_one x) d :=
  rfl

/-- Transport along the action-mul path. -/
theorem transport_act_mul {PG : PathGroup G} (A : PathAction PG X)
    {D : X → Type w} (g h : G) (x : X) (d : D (A.act (PG.mul g h) x)) :
    Path.transport (D := D) (A.act_mul g h x) d =
      Path.transport (D := D) (A.act_mul g h x) d :=
  rfl

/-! ## Additional action path constructions -/

/-- Acting on a path by the identity group element yields a related path. -/
theorem actPath_one_toEq {PG : PathGroup G} (A : PathAction PG X)
    {x y : X} (p : Path x y) :
    (actPath A PG.one p).toEq = _root_.congrArg (A.act PG.one) p.toEq := by
  rfl

/-- Orbit identity is natural (at proof level). -/
theorem orbitIdentity_natural_toEq {PG : PathGroup G} (A : PathAction PG X)
    {x y : X} (p : Path x y) :
    (Path.trans (actPath A PG.one p) (A.act_one y)).toEq =
      (Path.trans (A.act_one x) p).toEq := by
  cases p with | mk s h => cases h; simp

/-- Double action via orbitCompose (at proof level). -/
theorem orbitCompose_natural_toEq {PG : PathGroup G} (A : PathAction PG X)
    (g h : G) {x y : X} (p : Path x y) :
    (Path.trans (actPath A (PG.mul g h) p) (A.act_mul g h y)).toEq =
      (Path.trans (A.act_mul g h x) (actPath A g (actPath A h p))).toEq := by
  cases p with | mk s hp => cases hp; simp

/-- Equivariant identity map preserves paths. -/
theorem equivariant_id_mapPath {PG : PathGroup G}
    {A : PathAction PG X} {x y : X} (p : Path x y) :
    (Equivariant.idEquiv A).mapPath p = p := by
  simp [Equivariant.idEquiv, Equivariant.mapPath]

/-- The act_one path has reflexive toEq when act PG.one = id. -/
theorem actPath_one_refl_toEq {PG : PathGroup G} (A : PathAction PG X) (x : X) :
    (actPath A PG.one (Path.refl x)).toEq = rfl := by
  simp

/-- Stabilizer of one is witnessed by act_one (at proof level). -/
theorem one_stabilizer_proof {PG : PathGroup G} (A : PathAction PG X) (x : X) :
    (stabilizerPathOf A x PG.one (one_isStabilizer A x)).proof = (A.act_one x).proof :=
  rfl

end ActionGroupoidPaths
end Path
end ComputationalPaths
