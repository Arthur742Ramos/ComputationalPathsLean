import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace CubicalTypeTheory

universe u v

noncomputable def CubicalInterval : Type := Bool
noncomputable def i0 : CubicalInterval := false
noncomputable def i1 : CubicalInterval := true

noncomputable def connAnd (i j : CubicalInterval) : CubicalInterval := i && j
noncomputable def connOr (i j : CubicalInterval) : CubicalInterval := i || j
noncomputable def connNeg (i : CubicalInterval) : CubicalInterval := !i
noncomputable def connDiagLeft (i j : CubicalInterval) : CubicalInterval := connAnd i (connOr i j)
noncomputable def connDiagRight (i j : CubicalInterval) : CubicalInterval := connOr i (connAnd i j)

structure Cube (A : Type u) where
  point : CubicalInterval → A

noncomputable def cubeEndpoint0 {A : Type u} (c : Cube A) : A := c.point i0
noncomputable def cubeEndpoint1 {A : Type u} (c : Cube A) : A := c.point i1
noncomputable def constCube {A : Type u} (a : A) : Cube A := ⟨fun _ => a⟩
noncomputable def cubeMap {A : Type u} {B : Type v} (f : A → B) (c : Cube A) : Cube B :=
  ⟨fun i => f (c.point i)⟩

structure OpenBox (A : Type u) where
  left : A
  right : A

noncomputable def boxLeftToRight {A : Type u} (b : OpenBox A) : A := b.right
noncomputable def boxRightToLeft {A : Type u} (b : OpenBox A) : A := b.left
noncomputable def flipOpenBox {A : Type u} (b : OpenBox A) : OpenBox A := ⟨b.right, b.left⟩

structure KanOperation (A : Type u) where
  fill : OpenBox A → A

noncomputable def trivialKan {A : Type u} (a : A) : KanOperation A := ⟨fun _ => a⟩
noncomputable def composeKan {A : Type u} (K : KanOperation A) (b : OpenBox A) : A := K.fill b

noncomputable def transportConst {A : Type u} {a b : A} (p : Path a b) : Unit :=
  Path.transport (D := fun _ : A => Unit) p ()

structure GlueType (A : Type u) (B : Type u) where
  toFun : A → B
  invFun : B → A
  sec : (b : B) → Path (toFun (invFun b)) b
  ret : (a : A) → Path (invFun (toFun a)) a

noncomputable def glueForward {A : Type u} {B : Type u} (G : GlueType A B) : A → B := G.toFun
noncomputable def glueBackward {A : Type u} {B : Type u} (G : GlueType A B) : B → A := G.invFun
noncomputable def glueRoundTripForward {A : Type u} {B : Type u} (G : GlueType A B) : Prop :=
  ∀ b : B, G.toFun (G.invFun b) = b
noncomputable def glueRoundTripBackward {A : Type u} {B : Type u} (G : GlueType A B) : Prop :=
  ∀ a : A, G.invFun (G.toFun a) = a

structure CubicalUnivalence (A : Type u) (B : Type u) where
  glue : GlueType A B
  ua : A = B

noncomputable def uaRefl (A : Type u) : CubicalUnivalence A A where
  glue := {
    toFun := fun a => a
    invFun := fun a => a
    sec := fun b => Path.refl b
    ret := fun a => Path.refl a
  }
  ua := rfl

noncomputable def connectionSquare (i j : CubicalInterval) : CubicalInterval :=
  connOr (connAnd i j) (connAnd (connNeg i) j)

noncomputable def compositionBoundary {A : Type u} (c : Cube A) : OpenBox A :=
  ⟨cubeEndpoint0 c, cubeEndpoint1 c⟩

theorem connAnd_comm (i j : CubicalInterval) : connAnd i j = connAnd j i := by
  cases i <;> cases j <;> rfl

theorem connOr_comm (i j : CubicalInterval) : connOr i j = connOr j i := by
  cases i <;> cases j <;> rfl

theorem connAnd_assoc (i j k : CubicalInterval) :
    connAnd (connAnd i j) k = connAnd i (connAnd j k) := by
  cases i <;> cases j <;> cases k <;> rfl

theorem connOr_assoc (i j k : CubicalInterval) :
    connOr (connOr i j) k = connOr i (connOr j k) := by
  cases i <;> cases j <;> cases k <;> rfl

theorem connAnd_i0_left (i : CubicalInterval) : connAnd i0 i = i0 := by
  cases i <;> rfl

theorem connAnd_i1_left (i : CubicalInterval) : connAnd i1 i = i := by
  cases i <;> rfl

theorem connOr_i0_left (i : CubicalInterval) : connOr i0 i = i := by
  cases i <;> rfl

theorem connOr_i1_left (i : CubicalInterval) : connOr i1 i = i1 := by
  cases i <;> rfl

theorem connNeg_involutive (i : CubicalInterval) : connNeg (connNeg i) = i := by
  cases i <;> rfl

theorem connDiagLeft_idem (i : CubicalInterval) : connDiagLeft i i = i := by
  cases i <;> rfl

theorem connDiagRight_idem (i : CubicalInterval) : connDiagRight i i = i := by
  cases i <;> rfl

theorem cubeEndpoint0_const {A : Type u} (a : A) : cubeEndpoint0 (constCube a) = a := rfl

theorem cubeEndpoint1_const {A : Type u} (a : A) : cubeEndpoint1 (constCube a) = a := rfl

theorem cubeMap_id {A : Type u} (c : Cube A) : cubeMap (fun x : A => x) c = c := by
  cases c
  rfl

theorem cubeMap_comp {A : Type u} {B : Type v} {C : Type v}
    (f : A → B) (g : B → C) (c : Cube A) :
    cubeMap g (cubeMap f c) = cubeMap (fun x => g (f x)) c := by
  cases c
  rfl

theorem flipOpenBox_involutive {A : Type u} (b : OpenBox A) :
    flipOpenBox (flipOpenBox b) = b := by
  cases b
  rfl

theorem composeKan_trivial {A : Type u} (a : A) (b : OpenBox A) :
    composeKan (trivialKan a) b = a := rfl

theorem transportConst_eq_unit {A : Type u} {a b : A} (p : Path a b) :
    transportConst p = () := by
  cases p
  rfl

theorem glue_forward_backward {A : Type u} {B : Type u} (G : GlueType A B) :
    glueRoundTripForward G := by
  intro b
  exact (G.sec b).toEq

theorem glue_backward_forward {A : Type u} {B : Type u} (G : GlueType A B) :
    glueRoundTripBackward G := by
  intro a
  exact (G.ret a).toEq

theorem uaRefl_toEq (A : Type u) : (uaRefl A).ua = rfl := rfl

theorem connectionSquare_right_zero (i : CubicalInterval) :
    connectionSquare i i0 = i0 := by
  cases i <;> rfl

theorem connectionSquare_right_one (i : CubicalInterval) :
    connectionSquare i i1 = i1 := by
  cases i <;> rfl

theorem compositionBoundary_flip {A : Type u} (c : Cube A) :
    flipOpenBox (compositionBoundary c) = ⟨cubeEndpoint1 c, cubeEndpoint0 c⟩ := by
  cases c
  rfl

end CubicalTypeTheory
end Foundations
end Path
end ComputationalPaths
