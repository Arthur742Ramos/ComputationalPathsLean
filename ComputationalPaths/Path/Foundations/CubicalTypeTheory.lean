import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace CubicalTypeTheory

universe u v

def CubicalInterval : Type := Bool
def i0 : CubicalInterval := false
def i1 : CubicalInterval := true

def connAnd (i j : CubicalInterval) : CubicalInterval := i && j
def connOr (i j : CubicalInterval) : CubicalInterval := i || j
def connNeg (i : CubicalInterval) : CubicalInterval := !i
def connDiagLeft (i j : CubicalInterval) : CubicalInterval := connAnd i (connOr i j)
def connDiagRight (i j : CubicalInterval) : CubicalInterval := connOr i (connAnd i j)

structure Cube (A : Type u) where
  point : CubicalInterval → A

def cubeEndpoint0 {A : Type u} (c : Cube A) : A := c.point i0
def cubeEndpoint1 {A : Type u} (c : Cube A) : A := c.point i1
def constCube {A : Type u} (a : A) : Cube A := ⟨fun _ => a⟩
def cubeMap {A : Type u} {B : Type v} (f : A → B) (c : Cube A) : Cube B :=
  ⟨fun i => f (c.point i)⟩

structure OpenBox (A : Type u) where
  left : A
  right : A

def boxLeftToRight {A : Type u} (b : OpenBox A) : A := b.right
def boxRightToLeft {A : Type u} (b : OpenBox A) : A := b.left
def flipOpenBox {A : Type u} (b : OpenBox A) : OpenBox A := ⟨b.right, b.left⟩

structure KanOperation (A : Type u) where
  fill : OpenBox A → A

def trivialKan {A : Type u} (a : A) : KanOperation A := ⟨fun _ => a⟩
def composeKan {A : Type u} (K : KanOperation A) (b : OpenBox A) : A := K.fill b

def transportConst {A : Type u} {a b : A} (p : Path a b) : Unit :=
  Path.transport (D := fun _ : A => Unit) p ()

structure GlueType (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  sec : (b : B) → Path (toFun (invFun b)) b
  ret : (a : A) → Path (invFun (toFun a)) a

def glueForward {A : Type u} {B : Type v} (G : GlueType A B) : A → B := G.toFun
def glueBackward {A : Type u} {B : Type v} (G : GlueType A B) : B → A := G.invFun
def glueRoundTripForward {A : Type u} {B : Type v} (G : GlueType A B) : Prop :=
  ∀ b : B, G.toFun (G.invFun b) = b
def glueRoundTripBackward {A : Type u} {B : Type v} (G : GlueType A B) : Prop :=
  ∀ a : A, G.invFun (G.toFun a) = a

structure CubicalUnivalence (A : Type u) (B : Type v) where
  glue : GlueType A B
  ua : A = B

def uaRefl (A : Type u) : CubicalUnivalence A A where
  glue := {
    toFun := fun a => a
    invFun := fun a => a
    sec := fun b => Path.refl b
    ret := fun a => Path.refl a
  }
  ua := rfl

def connectionSquare (i j : CubicalInterval) : CubicalInterval :=
  connOr (connAnd i j) (connAnd (connNeg i) j)

def compositionBoundary {A : Type u} (c : Cube A) : OpenBox A :=
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

theorem glue_forward_backward {A : Type u} {B : Type v} (G : GlueType A B) :
    glueRoundTripForward G := by
  intro b
  exact (G.sec b).toEq

theorem glue_backward_forward {A : Type u} {B : Type v} (G : GlueType A B) :
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
