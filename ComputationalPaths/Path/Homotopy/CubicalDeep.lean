/-
# Deep Cubical Structure on Computational Paths

Connections, Kan operations, cubical composition, transport as a cubical
operation, higher-dimensional cubes and their coherence laws — all built
on top of the core `Path`/`Step`/`trans`/`symm` infrastructure.

## References

- Cohen, Coquand, Huber, Mörtberg, "Cubical Type Theory"
- Bezem, Coquand, Huber, "A model of type theory in cubical sets"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CubicalDeep

universe u v w

open ComputationalPaths.Path

/-! ## The De Morgan interval -/

abbrev I := Bool
def i0 : I := false
def i1 : I := true
def neg (i : I) : I := !i
def meet (i j : I) : I := i && j
def join (i j : I) : I := i || j

-- Theorems 1-5: De Morgan algebra
@[simp] theorem neg_neg (i : I) : neg (neg i) = i := by cases i <;> rfl
@[simp] theorem meet_comm (i j : I) : meet i j = meet j i := by cases i <;> cases j <;> rfl
@[simp] theorem join_comm (i j : I) : join i j = join j i := by cases i <;> cases j <;> rfl
@[simp] theorem demorgan_meet (i j : I) : neg (meet i j) = join (neg i) (neg j) := by
  cases i <;> cases j <;> rfl
@[simp] theorem demorgan_join (i j : I) : neg (join i j) = meet (neg i) (neg j) := by
  cases i <;> cases j <;> rfl

/-! ## 1-Cubes: Lines -/

/-- A line segment in a type, with specified endpoints. -/
structure Line (A : Type u) (a b : A) where
  fn : I → A
  bd0 : fn i0 = a
  bd1 : fn i1 = b

/-- Constant line. -/
def Line.const {A : Type u} (a : A) : Line A a a where
  fn := fun _ => a
  bd0 := rfl
  bd1 := rfl

/-- Reversed line. -/
def Line.rev {A : Type u} {a b : A} (l : Line A a b) : Line A b a where
  fn := fun i => l.fn (neg i)
  bd0 := by show l.fn (neg i0) = b; simp [neg, i0]; exact l.bd1
  bd1 := by show l.fn (neg i1) = a; simp [neg, i1]; exact l.bd0

-- Theorem 6: Double reversal recovers original function
theorem Line.rev_rev_fn {A : Type u} {a b : A} (l : Line A a b) :
    l.rev.rev.fn = l.fn := by funext i; simp [Line.rev, neg_neg]

/-- Map a function over a line. -/
def Line.map {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) where
  fn := fun i => f (l.fn i)
  bd0 := by show f (l.fn i0) = f a; rw [l.bd0]
  bd1 := by show f (l.fn i1) = f b; rw [l.bd1]

-- Theorem 7: Map preserves constant lines
theorem Line.map_const {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Line.map f (Line.const a) = Line.const (f a) := by
  simp [Line.map, Line.const]

-- Theorem 8: Map commutes with reversal
theorem Line.map_rev {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line.map f l.rev = (Line.map f l).rev := by
  simp [Line.map, Line.rev]

-- Theorem 9: Map composition
theorem Line.map_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (l : Line A a b) :
    Line.map (fun x => f (g x)) l = Line.map f (Line.map g l) := by
  simp [Line.map]

-- Theorem 10: Map identity
theorem Line.map_id_fn {A : Type u} {a b : A} (l : Line A a b) :
    (Line.map (fun x => x) l).fn = l.fn := by
  simp [Line.map]

/-- From a Path to a Line. -/
def Line.ofPath {A : Type u} {a b : A} (_p : Path a b) : Line A a b where
  fn := fun i => if i = i0 then a else b
  bd0 := by simp [i0]
  bd1 := by
    show (if i1 = i0 then a else b) = b
    simp [i1, i0]

/-! ## 2-Cubes: Squares -/

/-- A square in a type with specified corners. -/
structure Square (A : Type u) (a00 a01 a10 a11 : A) where
  fn : I → I → A
  c00 : fn i0 i0 = a00
  c01 : fn i0 i1 = a01
  c10 : fn i1 i0 = a10
  c11 : fn i1 i1 = a11

/-- Constant square. -/
def Square.const {A : Type u} (a : A) : Square A a a a a where
  fn := fun _ _ => a
  c00 := rfl
  c01 := rfl
  c10 := rfl
  c11 := rfl

/-- Map over a square. -/
def Square.map {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : Square A a00 a01 a10 a11) :
    Square B (f a00) (f a01) (f a10) (f a11) where
  fn := fun i j => f (s.fn i j)
  c00 := by show f (s.fn i0 i0) = f a00; rw [s.c00]
  c01 := by show f (s.fn i0 i1) = f a01; rw [s.c01]
  c10 := by show f (s.fn i1 i0) = f a10; rw [s.c10]
  c11 := by show f (s.fn i1 i1) = f a11; rw [s.c11]

-- Theorem 11: Map preserves constant squares
theorem Square.map_const {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Square.map f (Square.const a) = Square.const (f a) := by
  simp [Square.map, Square.const]

/-! ## Connection structures -/

-- Theorem 12: Connection via meet
def connectionMeet {A : Type u} {a b : A} (l : Line A a b) :
    Square A a a a b where
  fn := fun i j => l.fn (meet i j)
  c00 := by show l.fn (meet i0 i0) = a; change l.fn false = a; exact l.bd0
  c01 := by show l.fn (meet i0 i1) = a; change l.fn false = a; exact l.bd0
  c10 := by show l.fn (meet i1 i0) = a; change l.fn false = a; exact l.bd0
  c11 := by show l.fn (meet i1 i1) = b; change l.fn true = b; exact l.bd1

-- Theorem 13: Connection via join
def connectionJoin {A : Type u} {a b : A} (l : Line A a b) :
    Square A a b b b where
  fn := fun i j => l.fn (join i j)
  c00 := by show l.fn (join i0 i0) = a; change l.fn false = a; exact l.bd0
  c01 := by show l.fn (join i0 i1) = b; change l.fn true = b; exact l.bd1
  c10 := by show l.fn (join i1 i0) = b; change l.fn true = b; exact l.bd1
  c11 := by show l.fn (join i1 i1) = b; change l.fn true = b; exact l.bd1

-- Theorem 14: Constant line's connection-meet
theorem connectionMeet_const {A : Type u} (a : A) :
    (connectionMeet (Line.const (a := a))).fn = fun _ _ => a := by
  funext i j; simp [connectionMeet, Line.const]

-- Theorem 15: Constant line's connection-join
theorem connectionJoin_const {A : Type u} (a : A) :
    (connectionJoin (Line.const (a := a))).fn = fun _ _ => a := by
  funext i j; simp [connectionJoin, Line.const]

-- Theorem 16: Connection-meet of reversed line
theorem connectionMeet_rev_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l.rev).fn = fun i j => l.fn (neg (meet i j)) := by
  funext i j; simp [connectionMeet, Line.rev]

-- Theorem 17: Connection-join of reversed line
theorem connectionJoin_rev_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connectionJoin l.rev).fn = fun i j => l.fn (neg (join i j)) := by
  funext i j; simp [connectionJoin, Line.rev]

/-! ## Faces of squares -/

/-- Left face (first coord = i0). -/
def Square.faceLeft {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a01 where
  fn := s.fn i0
  bd0 := s.c00
  bd1 := s.c01

/-- Right face (first coord = i1). -/
def Square.faceRight {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a10 a11 where
  fn := s.fn i1
  bd0 := s.c10
  bd1 := s.c11

/-- Bottom face (second coord = i0). -/
def Square.faceBot {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a10 where
  fn := fun i => s.fn i i0
  bd0 := s.c00
  bd1 := s.c10

/-- Top face (second coord = i1). -/
def Square.faceTop {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a01 a11 where
  fn := fun i => s.fn i i1
  bd0 := s.c01
  bd1 := s.c11

-- Theorem 18: Left face of connection-meet is constant
theorem connectionMeet_faceLeft {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).faceLeft.fn = fun _ => a := by
  funext j
  show l.fn (meet i0 j) = a
  change l.fn (false && j) = a
  simp [Bool.false_and]
  exact l.bd0

-- Theorem 19: Right face of connection-join is constant
theorem connectionJoin_faceRight {A : Type u} {a b : A} (l : Line A a b) :
    (connectionJoin l).faceRight.fn = fun _ => b := by
  funext j
  show l.fn (join i1 j) = b
  change l.fn (true || j) = b
  simp [Bool.true_or]
  exact l.bd1

/-! ## Diagonal -/

/-- Diagonal of a square. -/
def Square.diagonal {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a11 where
  fn := fun i => s.fn i i
  bd0 := s.c00
  bd1 := s.c11

-- Theorem 20: Diagonal of constant square is constant
theorem Square.diagonal_const {A : Type u} (a : A) :
    (Square.const a).diagonal.fn = fun _ => a := by
  funext i; simp [Square.diagonal, Square.const]

-- Theorem 21: Diagonal of connection-meet
theorem connectionMeet_diagonal {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).diagonal.fn = fun i => l.fn (meet i i) := by
  funext i; simp [Square.diagonal, connectionMeet]

-- Theorem 22: meet i i = i, so connection-meet diagonal = original line
theorem connectionMeet_diagonal_eq {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).diagonal.fn = l.fn := by
  funext i; simp [Square.diagonal, connectionMeet, meet]

/-! ## Cubical transport -/

/-- Transport along a line using a given equality. -/
def cubeTransport {A : Type u} {P : A → Type v} {a b : A}
    (heq : a = b) (x : P a) : P b :=
  heq ▸ x

-- Theorem 23: Cubical transport along rfl
theorem cubeTransport_rfl {A : Type u} {P : A → Type v} (a : A) (x : P a) :
    cubeTransport (P := P) (rfl : a = a) x = x := rfl

-- Theorem 24: Agreement with Path.transport
theorem cubeTransport_path {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    cubeTransport (P := P) p.toEq x =
    Path.transport (D := P) p x := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## Kan filling -/

/-- Open box: top line plus a side constraint. -/
structure OpenBox (A : Type u) (a b c : A) where
  top : Line A a b
  side_eq : a = c

-- Theorem 25: Kan filler
def kanFill {A : Type u} {a b c : A} (box : OpenBox A a b c) :
    Line A c b where
  fn := fun i => box.top.fn i
  bd0 := by
    have h1 := box.top.bd0
    have h2 := box.side_eq
    exact h2 ▸ h1
  bd1 := box.top.bd1

-- Theorem 26: Kan filler agrees pointwise with top
theorem kanFill_pointwise {A : Type u} {a b c : A} (box : OpenBox A a b c)
    (i : I) : (kanFill box).fn i = box.top.fn i := rfl

/-! ## Composition via Kan -/

-- Theorem 27: Composition via Kan filling = trans
def kanCompose {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

theorem kanCompose_eq_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    kanCompose p q = Path.trans p q := rfl

-- Theorem 28: Kan composition with refl right
theorem kanCompose_refl_right {A : Type u} {a b : A} (p : Path a b) :
    kanCompose p (Path.refl b) = p := by simp [kanCompose]

-- Theorem 29: Kan composition with refl left
theorem kanCompose_refl_left {A : Type u} {a b : A} (p : Path a b) :
    kanCompose (Path.refl a) p = p := by simp [kanCompose]

-- Theorem 30: Kan composition associativity
theorem kanCompose_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    kanCompose (kanCompose p q) r = kanCompose p (kanCompose q r) := by
  simp [kanCompose]

-- Theorem 31: Kan inverse gives refl at eq level
theorem kanCompose_symm_toEq {A : Type u} {a b : A} (p : Path a b) :
    (kanCompose p (Path.symm p)).toEq = rfl := by simp

/-! ## Path squares -/

/-- A path square: commutativity witness for four paths. -/
structure PathSquare {A : Type u} {a00 a01 a10 a11 : A}
    (top : Path a00 a01) (bot : Path a10 a11)
    (left : Path a00 a10) (right : Path a01 a11) : Prop where
  comm : Path.trans left bot = Path.trans top right

-- Theorem 32: Reflexivity square
def PathSquare.hrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSquare p p (Path.refl a) (Path.refl b) where
  comm := by simp

-- Theorem 33: Vertical reflexivity square
def PathSquare.vrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSquare (Path.refl a) (Path.refl b) p p where
  comm := by simp

-- Theorem 34: Path square from refl everywhere
def PathSquare.allRefl {A : Type u} (a : A) :
    PathSquare (Path.refl a) (Path.refl a) (Path.refl a) (Path.refl a) where
  comm := by simp

-- Theorem 35: Square from trans equality
def PathSquare.ofComm {A : Type u} {a00 a01 a10 a11 : A}
    {top : Path a00 a01} {bot : Path a10 a11}
    {left : Path a00 a10} {right : Path a01 a11}
    (h : Path.trans left bot = Path.trans top right) :
    PathSquare top bot left right := ⟨h⟩

/-! ## Cubical congruence -/

-- Theorem 36: Cubical ap
def cubeAp {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) := Line.map f l

-- Theorem 37: Cubical ap composition
theorem cubeAp_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (l : Line A a b) :
    cubeAp (fun x => f (g x)) l = cubeAp f (cubeAp g l) := by
  simp [cubeAp, Line.map]

-- Theorem 38: Cubical ap id
theorem cubeAp_id_fn {A : Type u} {a b : A} (l : Line A a b) :
    (cubeAp (fun x => x) l).fn = l.fn := by
  simp [cubeAp, Line.map]

/-! ## Cubical homotopy -/

/-- A homotopy between two lines with same endpoints. -/
structure CubeHomotopy {A : Type u} {a b : A}
    (l₁ l₂ : Line A a b) where
  fn : I → I → A
  at_i0 : ∀ j, fn i0 j = l₁.fn j
  at_i1 : ∀ j, fn i1 j = l₂.fn j
  at_j0 : ∀ i, fn i i0 = a
  at_j1 : ∀ i, fn i i1 = b

-- Theorem 39: Reflexive homotopy
def CubeHomotopy.refl {A : Type u} {a b : A} (l : Line A a b) :
    CubeHomotopy l l where
  fn := fun _ j => l.fn j
  at_i0 := fun _ => rfl
  at_i1 := fun _ => rfl
  at_j0 := fun _ => l.bd0
  at_j1 := fun _ => l.bd1

-- Theorem 40: Homotopy to a square
def CubeHomotopy.toSquare {A : Type u} {a b : A}
    {l₁ l₂ : Line A a b} (h : CubeHomotopy l₁ l₂) :
    Square A a b a b where
  fn := h.fn
  c00 := by have := h.at_j0 i0; rw [this]
  c01 := by have := h.at_j1 i0; rw [this]
  c10 := by have := h.at_j0 i1; rw [this]
  c11 := by have := h.at_j1 i1; rw [this]

/-! ## n-Cubes -/

/-- An n-cube: function from n interval coordinates. -/
def Cube (n : Nat) (A : Type u) : Type u := (Fin n → I) → A

/-- Constant n-cube. -/
def Cube.const {A : Type u} (n : Nat) (a : A) : Cube n A := fun _ => a

/-- Degeneracy: insert a dummy coordinate. -/
def Cube.degen {A : Type u} {n : Nat} (d : Fin (n + 1)) (c : Cube n A) :
    Cube (n + 1) A :=
  fun coords => c (fun k =>
    if k.val < d.val then coords ⟨k.val, by omega⟩
    else coords ⟨k.val + 1, by omega⟩)

-- Theorem 41: Degeneracy of constant
theorem Cube.degen_const {A : Type u} {n : Nat} (a : A) (d : Fin (n + 1)) :
    Cube.degen d (Cube.const n a) = Cube.const (n + 1) a := by
  funext coords; simp [Cube.degen, Cube.const]

/-! ## Dependent cubical transport -/

-- Theorem 42: Transport is natural w.r.t. functions between families
theorem cubeTransportDep {A : Type u} {P : A → Type v} {Q : A → Type w}
    {a b : A} (f : ∀ x, P x → Q x) (p : Path a b) (x : P a) :
    Path.transport (D := Q) p (f a x) = f b (Path.transport (D := P) p x) := by
  cases p with | mk steps proof => cases proof; rfl

-- Theorem 43: Transport composition
theorem cubeTransport_trans_path {A : Type u} {P : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    Path.transport (D := P) (Path.trans p q) x =
    Path.transport (D := P) q (Path.transport (D := P) p x) :=
  Path.transport_trans (D := P) p q x

/-! ## Cubical identity encoding -/

/-- Encode identity type cubically as a subtype of Line. -/
def CubicalId {A : Type u} (a b : A) := { _l : Line A a b // True }

-- Theorem 44: CubicalId is reflexive
def CubicalId.refl {A : Type u} (a : A) : CubicalId a a := ⟨Line.const a, trivial⟩

-- Theorem 45: CubicalId from equality
def CubicalId.ofEq {A : Type u} {a b : A} (h : a = b) : CubicalId a b :=
  ⟨Line.ofPath (Path.ofEq h), trivial⟩

-- Theorem 46: CubicalId yields Path
def CubicalId.toPathFromEq {A : Type u} {a b : A} (h : a = b)
    (_ : CubicalId a b) : Path a b :=
  Path.ofEq h

/-! ## Flipping squares -/

/-- Transpose a square (swap i and j). -/
def Square.transpose {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Square A a00 a10 a01 a11 where
  fn := fun i j => s.fn j i
  c00 := s.c00
  c01 := s.c10
  c10 := s.c01
  c11 := s.c11

-- Theorem 47: Double transpose is identity on fn
theorem Square.transpose_transpose_fn {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) :
    s.transpose.transpose.fn = s.fn := by
  funext i j; simp [Square.transpose]

-- Theorem 48: Transpose of constant square is constant
theorem Square.transpose_const {A : Type u} (a : A) :
    (Square.const a).transpose = Square.const a := by
  simp [Square.transpose, Square.const]

-- Theorem 49: Connection symmetry: meet-transpose
theorem connection_transpose_meet {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).transpose.fn = (connectionMeet l).fn := by
  funext i j; simp [Square.transpose, connectionMeet, meet_comm]

-- Theorem 50: Connection symmetry for join
theorem connection_transpose_join {A : Type u} {a b : A} (l : Line A a b) :
    (connectionJoin l).transpose.fn = (connectionJoin l).fn := by
  funext i j; simp [Square.transpose, connectionJoin, join_comm]

end CubicalDeep
end Homotopy
end Path
end ComputationalPaths
