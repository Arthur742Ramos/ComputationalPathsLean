/-
# Cubical Structure on Computational Paths

Cubical type theory structures modeled via computational paths: face maps,
degeneracies, connections, composition, Kan operations for cubes, cubical
identity types, and transport along cubical paths.

## References

- Cohen, Coquand, Huber, Mörtberg, "Cubical Type Theory"
- Bezem, Coquand, Huber, "A model of type theory in cubical sets"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CubicalPaths

universe u v

open ComputationalPaths.Path

/-! ## The cubical interval -/

abbrev Interval : Type := Bool

noncomputable def I0 : Interval := false
noncomputable def I1 : Interval := true
noncomputable def iNeg (i : Interval) : Interval := !i
noncomputable def iMeet (i j : Interval) : Interval := i && j
noncomputable def iJoin (i j : Interval) : Interval := i || j

/-! ## Interval algebra -/

theorem iNeg_I0 : iNeg I0 = I1 := rfl
theorem iNeg_I1 : iNeg I1 = I0 := rfl
theorem iNeg_iNeg (i : Interval) : iNeg (iNeg i) = i := by cases i <;> rfl
theorem iMeet_comm (i j : Interval) : iMeet i j = iMeet j i := by cases i <;> cases j <;> rfl
theorem iJoin_comm (i j : Interval) : iJoin i j = iJoin j i := by cases i <;> cases j <;> rfl
theorem iMeet_assoc (i j k : Interval) : iMeet (iMeet i j) k = iMeet i (iMeet j k) := by
  cases i <;> cases j <;> cases k <;> rfl
theorem iJoin_assoc (i j k : Interval) : iJoin (iJoin i j) k = iJoin i (iJoin j k) := by
  cases i <;> cases j <;> cases k <;> rfl
theorem iMeet_I0 (i : Interval) : iMeet I0 i = I0 := by cases i <;> rfl
theorem iMeet_I1 (i : Interval) : iMeet I1 i = i := by cases i <;> rfl
theorem iJoin_I0 (i : Interval) : iJoin I0 i = i := by cases i <;> rfl
theorem iJoin_I1 (i : Interval) : iJoin I1 i = I1 := by cases i <;> rfl
theorem iMeet_idem (i : Interval) : iMeet i i = i := by cases i <;> rfl
theorem iJoin_idem (i : Interval) : iJoin i i = i := by cases i <;> rfl
theorem iNeg_iMeet (i j : Interval) : iNeg (iMeet i j) = iJoin (iNeg i) (iNeg j) := by
  cases i <;> cases j <;> rfl
theorem iNeg_iJoin (i j : Interval) : iNeg (iJoin i j) = iMeet (iNeg i) (iNeg j) := by
  cases i <;> cases j <;> rfl
theorem iMeet_iJoin_absorb (i j : Interval) : iMeet i (iJoin i j) = i := by
  cases i <;> cases j <;> rfl
theorem iJoin_iMeet_absorb (i j : Interval) : iJoin i (iMeet i j) = i := by
  cases i <;> cases j <;> rfl

/-! ## 1-Cubes as cubical paths -/

/-- A cubical 1-path: a function I → A with specified endpoints. -/
structure CubePath (A : Type u) (a b : A) where
  fn : Interval → A
  at0 : fn I0 = a
  at1 : fn I1 = b
  /-- The underlying propositional equality. -/
  eq : a = b

/-- Constant cubical path. -/
noncomputable def CubePath.refl (A : Type u) (a : A) : CubePath A a a where
  fn := fun _ => a
  at0 := rfl
  at1 := rfl
  eq := rfl

/-- Reverse a cubical path. -/
noncomputable def CubePath.symm {A : Type u} {a b : A} (p : CubePath A a b) : CubePath A b a where
  fn := fun i => p.fn (iNeg i)
  at0 := by show p.fn (iNeg I0) = b; rw [iNeg_I0]; exact p.at1
  at1 := by show p.fn (iNeg I1) = a; rw [iNeg_I1]; exact p.at0
  eq := p.eq.symm

/-- Double reversal recovers original function. -/
theorem CubePath.symm_symm_fn {A : Type u} {a b : A} (p : CubePath A a b) :
    p.symm.symm.fn = p.fn := by
  funext i; simp [CubePath.symm, iNeg_iNeg]

/-- Map a function over a cubical path. -/
noncomputable def CubePath.map {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : CubePath A a b) : CubePath B (f a) (f b) where
  fn := fun i => f (p.fn i)
  at0 := by show f (p.fn I0) = f a; rw [p.at0]
  at1 := by show f (p.fn I1) = f b; rw [p.at1]
  eq := _root_.congrArg f p.eq

/-- Map preserves refl. -/
theorem CubePath.map_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    CubePath.map f (CubePath.refl A a) = CubePath.refl B (f a) := by
  simp [CubePath.map, CubePath.refl]

/-- From a computational path to a cubical path. -/
noncomputable def cubPathOfPath {A : Type u} {a b : A} (p : Path a b) : CubePath A a b where
  fn := fun i => if i = I0 then a else b
  at0 := by simp [I0]
  at1 := by simp [I1, I0]
  eq := p.toEq

/-- Refl endpoint lemmas. -/
theorem CubePath.refl_at0 {A : Type u} (a : A) :
    (CubePath.refl A a).at0 = rfl := rfl
theorem CubePath.refl_at1 {A : Type u} (a : A) :
    (CubePath.refl A a).at1 = rfl := rfl

/-! ## 2-Cubes (squares) -/

/-- A cubical square: function I × I → A with specified corners. -/
structure CubeSquare (A : Type u) (a00 a01 a10 a11 : A) where
  fn : Interval → Interval → A
  c00 : fn I0 I0 = a00
  c01 : fn I0 I1 = a01
  c10 : fn I1 I0 = a10
  c11 : fn I1 I1 = a11

/-- Constant square. -/
noncomputable def CubeSquare.const (A : Type u) (a : A) : CubeSquare A a a a a where
  fn := fun _ _ => a
  c00 := rfl
  c01 := rfl
  c10 := rfl
  c11 := rfl

/-- Map over a square. -/
noncomputable def CubeSquare.map {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : CubeSquare A a00 a01 a10 a11) :
    CubeSquare B (f a00) (f a01) (f a10) (f a11) where
  fn := fun i j => f (s.fn i j)
  c00 := by show f (s.fn I0 I0) = f a00; rw [s.c00]
  c01 := by show f (s.fn I0 I1) = f a01; rw [s.c01]
  c10 := by show f (s.fn I1 I0) = f a10; rw [s.c10]
  c11 := by show f (s.fn I1 I1) = f a11; rw [s.c11]

/-- Map preserves constant square. -/
theorem CubeSquare.map_const {A : Type u} {B : Type v} (f : A → B) (a : A) :
    CubeSquare.map f (CubeSquare.const A a) = CubeSquare.const B (f a) := by
  simp [CubeSquare.map, CubeSquare.const]

/-- Left face of a square (fix first coord to I0). -/
noncomputable def squareFaceLeft {A : Type u} {a00 a01 a10 a11 : A}
    (s : CubeSquare A a00 a01 a10 a11) (heq : a00 = a01) : CubePath A a00 a01 where
  fn := s.fn I0
  at0 := s.c00
  at1 := s.c01
  eq := heq

/-- Right face of a square (fix first coord to I1). -/
noncomputable def squareFaceRight {A : Type u} {a00 a01 a10 a11 : A}
    (s : CubeSquare A a00 a01 a10 a11) (heq : a10 = a11) : CubePath A a10 a11 where
  fn := s.fn I1
  at0 := s.c10
  at1 := s.c11
  eq := heq

/-- Bottom face of a square (fix second coord to I0). -/
noncomputable def squareFaceBot {A : Type u} {a00 a01 a10 a11 : A}
    (s : CubeSquare A a00 a01 a10 a11) (heq : a00 = a10) : CubePath A a00 a10 where
  fn := fun i => s.fn i I0
  at0 := s.c00
  at1 := s.c10
  eq := heq

/-- Top face of a square (fix second coord to I1). -/
noncomputable def squareFaceTop {A : Type u} {a00 a01 a10 a11 : A}
    (s : CubeSquare A a00 a01 a10 a11) (heq : a01 = a11) : CubePath A a01 a11 where
  fn := fun i => s.fn i I1
  at0 := s.c01
  at1 := s.c11
  eq := heq

/-! ## Connection maps -/

/-- Connection via meet: produces a square from a path. -/
noncomputable def connectionMeet {A : Type u} {a b : A} (p : CubePath A a b) :
    CubeSquare A a a a b where
  fn := fun i j => p.fn (iMeet i j)
  c00 := by show p.fn (iMeet I0 I0) = a; rw [show iMeet I0 I0 = I0 from rfl]; exact p.at0
  c01 := by show p.fn (iMeet I0 I1) = a; rw [show iMeet I0 I1 = I0 from rfl]; exact p.at0
  c10 := by show p.fn (iMeet I1 I0) = a; rw [show iMeet I1 I0 = I0 from rfl]; exact p.at0
  c11 := by show p.fn (iMeet I1 I1) = b; rw [show iMeet I1 I1 = I1 from rfl]; exact p.at1

/-- Connection via join: produces a square from a path. -/
noncomputable def connectionJoin {A : Type u} {a b : A} (p : CubePath A a b) :
    CubeSquare A a b b b where
  fn := fun i j => p.fn (iJoin i j)
  c00 := by show p.fn (iJoin I0 I0) = a; rw [show iJoin I0 I0 = I0 from rfl]; exact p.at0
  c01 := by show p.fn (iJoin I0 I1) = b; rw [show iJoin I0 I1 = I1 from rfl]; exact p.at1
  c10 := by show p.fn (iJoin I1 I0) = b; rw [show iJoin I1 I0 = I1 from rfl]; exact p.at1
  c11 := by show p.fn (iJoin I1 I1) = b; rw [show iJoin I1 I1 = I1 from rfl]; exact p.at1

/-! ## Transport -/

/-- The path equality from a cubical path. -/
noncomputable def CubePath.toEq {A : Type u} {a b : A} (p : CubePath A a b) : a = b := p.eq

/-- Transport along a cubical path via the underlying equality. -/
noncomputable def cubeTransport {A : Type u} {P : A → Type v} {a b : A}
    (p : CubePath A a b) (x : P a) : P b :=
  p.eq ▸ x

/-- Transport along refl is identity. -/
theorem cubeTransport_refl {A : Type u} {P : A → Type v} (a : A) (x : P a) :
    cubeTransport (P := P) (CubePath.refl A a) x = x := rfl

/-! ## Composition data -/

/-- Composition data: two composable cubical paths. -/
structure CompData (A : Type u) (a b c : A) where
  p : CubePath A a b
  q : CubePath A b c

/-- Source of composition data. -/
theorem CompData.source {A : Type u} {a b c : A} (d : CompData A a b c) :
    d.p.fn I0 = a := d.p.at0

/-- Target of composition data. -/
theorem CompData.target {A : Type u} {a b c : A} (d : CompData A a b c) :
    d.q.fn I1 = c := d.q.at1

/-- Middle point of composition. -/
theorem CompData.middle_left {A : Type u} {a b c : A} (d : CompData A a b c) :
    d.p.fn I1 = b := d.p.at1

theorem CompData.middle_right {A : Type u} {a b c : A} (d : CompData A a b c) :
    d.q.fn I0 = b := d.q.at0

/-! ## 2-paths (path of paths) -/

/-- A 2-path between computational paths. -/
noncomputable def TwoPath {A : Type u} {a b : A} (p q : Path a b) : Type u := Path p q

noncomputable def TwoPath.refl {A : Type u} {a b : A} (p : Path a b) : TwoPath p p := Path.refl p
noncomputable def TwoPath.symm {A : Type u} {a b : A} {p q : Path a b} (α : TwoPath p q) : TwoPath q p :=
  Path.symm α
noncomputable def TwoPath.trans {A : Type u} {a b : A} {p q r : Path a b}
    (α : TwoPath p q) (β : TwoPath q r) : TwoPath p r := Path.trans α β

/-- 2-path transport. -/
noncomputable def twoPathTransport {A : Type u} {a b : A} {p q : Path a b}
    (α : TwoPath p q) {B : Path a b → Type v} (x : B p) : B q :=
  Path.transport (D := B) α x

/-- Transport along refl 2-path is identity. -/
theorem twoPathTransport_refl {A : Type u} {a b : A} (p : Path a b)
    {B : Path a b → Type v} (x : B p) :
    twoPathTransport (TwoPath.refl p) x = x := rfl

/-- Symm-trans is identity at the eq level. -/
theorem TwoPath.symm_trans_toEq {A : Type u} {a b : A} {p q : Path a b}
    (α : TwoPath p q) :
    (TwoPath.trans (TwoPath.symm α) α).toEq = rfl := by
  simp [TwoPath.trans, TwoPath.symm]

/-- Trans-symm is identity at the eq level. -/
theorem TwoPath.trans_symm_toEq {A : Type u} {a b : A} {p q : Path a b}
    (α : TwoPath p q) :
    (TwoPath.trans α (TwoPath.symm α)).toEq = rfl := by
  simp [TwoPath.trans, TwoPath.symm]

end CubicalPaths
end Homotopy
end Path
end ComputationalPaths
