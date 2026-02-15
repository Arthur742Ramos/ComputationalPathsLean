/-
# Deep Cubical Type Theory via Computational Paths

Interval type, connections (∧/∨), degeneracies, face maps, Kan composition,
cubical transport, coercion, filling operations, and coherence — all witnessed
by multi-step computational path chains using trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Homotopy.CubicalDeep

open ComputationalPaths.Path

universe u v w

/-! ## §1 De Morgan interval -/

abbrev I := Bool
@[inline] abbrev i0 : I := false
@[inline] abbrev i1 : I := true
@[inline] def neg (i : I) : I := !i
@[inline] def meet (a b : I) : I := a && b
@[inline] def join (a b : I) : I := a || b

-- 1–10: De Morgan algebra
@[simp] theorem neg_neg (i : I) : neg (neg i) = i := by cases i <;> rfl
@[simp] theorem meet_comm (a b : I) : meet a b = meet b a := by cases a <;> cases b <;> rfl
@[simp] theorem join_comm (a b : I) : join a b = join b a := by cases a <;> cases b <;> rfl
@[simp] theorem demorgan_meet (a b : I) : neg (meet a b) = join (neg a) (neg b) := by
  cases a <;> cases b <;> rfl
@[simp] theorem demorgan_join (a b : I) : neg (join a b) = meet (neg a) (neg b) := by
  cases a <;> cases b <;> rfl
@[simp] theorem meet_idem (i : I) : meet i i = i := by cases i <;> rfl
@[simp] theorem join_idem (i : I) : join i i = i := by cases i <;> rfl
@[simp] theorem meet_i0 (i : I) : meet i i0 = i0 := by cases i <;> rfl
@[simp] theorem meet_i1 (i : I) : meet i i1 = i := by cases i <;> rfl
@[simp] theorem join_i0 (i : I) : join i i0 = i := by cases i <;> rfl
@[simp] theorem join_i1 (i : I) : join i i1 = i1 := by cases i <;> rfl

-- 11: Distributivity
theorem meet_distrib_join (i j k : I) :
    meet i (join j k) = join (meet i j) (meet i k) := by
  cases i <;> cases j <;> cases k <;> rfl

-- 12: Absorption
@[simp] theorem meet_absorb_join (i j : I) : meet i (join i j) = i := by
  cases i <;> cases j <;> rfl

-- 13: Absorption dual
@[simp] theorem join_absorb_meet (i j : I) : join i (meet i j) = i := by
  cases i <;> cases j <;> rfl

/-! ## §2 Lines (1-cubes) -/

structure Line (A : Type u) (a b : A) where
  fn : I → A
  bd0 : fn i0 = a
  bd1 : fn i1 = b

-- 14: Constant line
def Line.const {A : Type u} (a : A) : Line A a a := ⟨fun _ => a, rfl, rfl⟩

-- 15: Reversed line
def Line.rev {A : Type u} {a b : A} (l : Line A a b) : Line A b a where
  fn := fun i => l.fn (neg i)
  bd0 := by show l.fn (neg i0) = b; simp [neg]; exact l.bd1
  bd1 := by show l.fn (neg i1) = a; simp [neg]; exact l.bd0

-- 16: Double reversal
theorem Line.rev_rev_fn {A : Type u} {a b : A} (l : Line A a b) :
    l.rev.rev.fn = l.fn := by funext i; simp [Line.rev, neg]

-- 17: Map over a line
def Line.map {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) where
  fn := fun i => f (l.fn i)
  bd0 := by rw [l.bd0]
  bd1 := by rw [l.bd1]

-- 18: Map preserves const
theorem Line.map_const {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Line.map f (Line.const a) = Line.const (f a) := by
  simp [Line.map, Line.const]

-- 19: Map composition
theorem Line.map_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (l : Line A a b) :
    Line.map (fun x => f (g x)) l = Line.map f (Line.map g l) := by
  simp [Line.map]

-- 20: Path to Line
def Line.ofPath {A : Type u} {a b : A} (p : Path a b) : Line A a b where
  fn := fun i => if i = i0 then a else b
  bd0 := by simp
  bd1 := by simp [i0, i1]

/-! ## §3 Squares (2-cubes) -/

structure Square (A : Type u) (a00 a01 a10 a11 : A) where
  fn : I → I → A
  c00 : fn i0 i0 = a00
  c01 : fn i0 i1 = a01
  c10 : fn i1 i0 = a10
  c11 : fn i1 i1 = a11

-- 21: Constant square
def Square.const {A : Type u} (a : A) : Square A a a a a :=
  ⟨fun _ _ => a, rfl, rfl, rfl, rfl⟩

-- 22: Transpose
def Square.transpose {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Square A a00 a10 a01 a11 where
  fn := fun i j => s.fn j i
  c00 := s.c00
  c01 := s.c10
  c10 := s.c01
  c11 := s.c11

-- 23: Double transpose = id
theorem Square.transpose_transpose_fn {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) :
    s.transpose.transpose.fn = s.fn := by funext i j; rfl

-- 24: Map over square
def Square.map {A : Type u} {B : Type v} (f : A → B)
    {a00 a01 a10 a11 : A} (s : Square A a00 a01 a10 a11) :
    Square B (f a00) (f a01) (f a10) (f a11) where
  fn := fun i j => f (s.fn i j)
  c00 := by rw [s.c00]
  c01 := by rw [s.c01]
  c10 := by rw [s.c10]
  c11 := by rw [s.c11]

/-! ## §4 Connections -/

-- 25: Connection via meet
def connectionMeet {A : Type u} {a b : A} (l : Line A a b) :
    Square A a a a b where
  fn := fun i j => l.fn (meet i j)
  c00 := by change l.fn (meet i0 i0) = a; simp [meet]; exact l.bd0
  c01 := by change l.fn (meet i0 i1) = a; simp [meet]; exact l.bd0
  c10 := by change l.fn (meet i1 i0) = a; simp [meet]; exact l.bd0
  c11 := by change l.fn (meet i1 i1) = b; simp [meet]; exact l.bd1

-- 26: Connection via join
def connectionJoin {A : Type u} {a b : A} (l : Line A a b) :
    Square A a b b b where
  fn := fun i j => l.fn (join i j)
  c00 := by change l.fn (join i0 i0) = a; simp [join]; exact l.bd0
  c01 := by change l.fn (join i0 i1) = b; simp [join]; exact l.bd1
  c10 := by change l.fn (join i1 i0) = b; simp [join]; exact l.bd1
  c11 := by change l.fn (join i1 i1) = b; simp [join]; exact l.bd1

-- 27: Connection meet is symmetric
theorem connection_meet_sym {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).transpose.fn = (connectionMeet l).fn := by
  funext i j; simp [Square.transpose, connectionMeet, meet_comm]

-- 28: Connection join is symmetric
theorem connection_join_sym {A : Type u} {a b : A} (l : Line A a b) :
    (connectionJoin l).transpose.fn = (connectionJoin l).fn := by
  funext i j; simp [Square.transpose, connectionJoin, join_comm]

-- 29: Connection meet on constant
theorem connectionMeet_const_fn {A : Type u} (a : A) :
    (connectionMeet (Line.const a)).fn = fun _ _ => a := by
  funext i j; simp [connectionMeet, Line.const]

/-! ## §5 Faces -/

def Square.faceLeft {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a01 :=
  ⟨s.fn i0, s.c00, s.c01⟩

def Square.faceRight {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a10 a11 :=
  ⟨s.fn i1, s.c10, s.c11⟩

def Square.faceBot {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a10 :=
  ⟨fun i => s.fn i i0, s.c00, s.c10⟩

def Square.faceTop {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a01 a11 :=
  ⟨fun i => s.fn i i1, s.c01, s.c11⟩

-- 30: Transpose swaps left/bot
theorem Square.faceLeft_transpose_eq_faceBot {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) :
    s.transpose.faceLeft.fn = s.faceBot.fn := by
  funext j; rfl

-- 31: Diagonal
def Square.diagonal {A : Type u} {a00 a01 a10 a11 : A}
    (s : Square A a00 a01 a10 a11) : Line A a00 a11 :=
  ⟨fun i => s.fn i i, s.c00, s.c11⟩

-- 32: Connection-meet diagonal = original line
theorem connectionMeet_diagonal {A : Type u} {a b : A} (l : Line A a b) :
    (connectionMeet l).diagonal.fn = l.fn := by
  funext i; simp [Square.diagonal, connectionMeet]

-- 33: Connection-join diagonal = original line
theorem connectionJoin_diagonal {A : Type u} {a b : A} (l : Line A a b) :
    (connectionJoin l).diagonal.fn = l.fn := by
  funext i; simp [Square.diagonal, connectionJoin]

/-! ## §6 Path squares -/

structure PathSquare {A : Type u} {a00 a01 a10 a11 : A}
    (top : Path a00 a01) (bot : Path a10 a11)
    (left : Path a00 a10) (right : Path a01 a11) : Prop where
  comm : Path.trans left bot = Path.trans top right

-- 34: Horizontal refl square
def PathSquare.hrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSquare p p (Path.refl a) (Path.refl b) := ⟨by simp⟩

-- 35: Vertical refl square
def PathSquare.vrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSquare (Path.refl a) (Path.refl b) p p := ⟨by simp⟩

-- 36: Vertical composition of path squares
theorem PathSquare.vcomp {A : Type u}
    {a00 a01 a10 a11 a20 a21 : A}
    {top : Path a00 a01} {mid : Path a10 a11} {bot : Path a20 a21}
    {l1 : Path a00 a10} {r1 : Path a01 a11}
    {l2 : Path a10 a20} {r2 : Path a11 a21}
    (sq1 : PathSquare top mid l1 r1)
    (sq2 : PathSquare mid bot l2 r2) :
    PathSquare top bot (Path.trans l1 l2) (Path.trans r1 r2) := by
  constructor
  calc Path.trans (Path.trans l1 l2) bot
      = Path.trans l1 (Path.trans l2 bot) := Path.trans_assoc l1 l2 bot
    _ = Path.trans l1 (Path.trans mid r2) := by rw [sq2.comm]
    _ = Path.trans (Path.trans l1 mid) r2 := (Path.trans_assoc l1 mid r2).symm
    _ = Path.trans (Path.trans top r1) r2 := by rw [← sq1.comm]
    _ = Path.trans top (Path.trans r1 r2) := Path.trans_assoc top r1 r2

-- 37: Horizontal composition of path squares
theorem PathSquare.hcomp {A : Type u}
    {a00 a01 a02 a10 a11 a12 : A}
    {top1 : Path a00 a01} {top2 : Path a01 a02}
    {bot1 : Path a10 a11} {bot2 : Path a11 a12}
    {left : Path a00 a10} {mid_ : Path a01 a11} {right : Path a02 a12}
    (sq1 : PathSquare top1 bot1 left mid_)
    (sq2 : PathSquare top2 bot2 mid_ right) :
    PathSquare (Path.trans top1 top2) (Path.trans bot1 bot2) left right := by
  constructor
  calc Path.trans left (Path.trans bot1 bot2)
      = Path.trans (Path.trans left bot1) bot2 := (Path.trans_assoc left bot1 bot2).symm
    _ = Path.trans (Path.trans top1 mid_) bot2 := by rw [sq1.comm]
    _ = Path.trans top1 (Path.trans mid_ bot2) := Path.trans_assoc top1 mid_ bot2
    _ = Path.trans top1 (Path.trans top2 right) := by rw [sq2.comm]
    _ = Path.trans (Path.trans top1 top2) right := (Path.trans_assoc top1 top2 right).symm

/-! ## §7 Homogeneous composition -/

def hcomp {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- 38: unit left
theorem hcomp_refl_left {A : Type u} {a b : A} (p : Path a b) :
    hcomp (Path.refl a) p = p := Path.trans_refl_left p

-- 39: unit right
theorem hcomp_refl_right {A : Type u} {a b : A} (p : Path a b) :
    hcomp p (Path.refl b) = p := Path.trans_refl_right p

-- 40: associativity
theorem hcomp_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    hcomp (hcomp p q) r = hcomp p (hcomp q r) := Path.trans_assoc p q r

-- 41: inverse
theorem hcomp_symm_toEq {A : Type u} {a b : A} (p : Path a b) :
    (hcomp p (Path.symm p)).toEq = rfl := by simp [hcomp]

/-! ## §8 n-Cubes -/

def Cube (n : Nat) (A : Type u) : Type u := (Fin n → I) → A

-- 42: Constant n-cube
def Cube.const_ {A : Type u} (n : Nat) (a : A) : Cube n A := fun _ => a

-- 43: Degeneracy
def Cube.degen {A : Type u} {n : Nat} (k : Fin (n + 1)) (c : Cube n A) :
    Cube (n + 1) A := fun coords =>
  c (fun i =>
    if _ : i.val < k.val then coords ⟨i.val, by omega⟩
    else coords ⟨i.val + 1, by omega⟩)

-- 44: degen const = const
theorem Cube.degen_const {A : Type u} {n : Nat} (a : A) (k : Fin (n + 1)) :
    Cube.degen k (Cube.const_ n a) = Cube.const_ (n + 1) a := by
  funext; simp [Cube.degen, Cube.const_]

/-! ## §9 Transport -/

-- 45: cubTransport
def cubTransport {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) : P b := Path.transport (D := P) p x

-- 46: functorial
theorem cubTransport_trans {A : Type u} {P : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    cubTransport (P := P) (Path.trans p q) x =
    cubTransport (P := P) q (cubTransport (P := P) p x) :=
  Path.transport_trans (D := P) p q x

-- 47: invertible
theorem cubTransport_symm {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    cubTransport (P := P) (Path.symm p) (cubTransport (P := P) p x) = x :=
  Path.transport_symm_left (D := P) p x

-- 48: natural
theorem cubTransport_natural {A : Type u} {P : A → Type v} {Q : A → Type w}
    {a b : A} (f : ∀ x, P x → Q x) (p : Path a b) (x : P a) :
    Path.transport (D := Q) p (f a x) = f b (Path.transport (D := P) p x) := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## §10 Frobenius -/

-- 49: Transport in Σ-type
theorem frobenius {A : Type u} {B : A → Type v} {a b : A}
    (p : Path a b) (x : B a) :
    Path.transport (D := fun z => @Sigma (B z) (fun _ => Unit)) p ⟨x, ()⟩ =
    ⟨Path.transport (D := B) p x, ()⟩ := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## §11 Cubical ap -/

-- 50: cubeAp
def cubeAp {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) := Line.map f l

-- 51: cubeAp composition
theorem cubeAp_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (l : Line A a b) :
    cubeAp (fun x => f (g x)) l = cubeAp f (cubeAp g l) := by
  simp [cubeAp, Line.map]

-- 52: cubeAp preserves meet-connection
theorem cubeAp_connectionMeet {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (l : Line A a b) :
    (connectionMeet (cubeAp f l)).fn = (Square.map f (connectionMeet l)).fn := by
  funext i j; simp [connectionMeet, cubeAp, Line.map, Square.map]

-- 53: cubeAp preserves join-connection
theorem cubeAp_connectionJoin {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (l : Line A a b) :
    (connectionJoin (cubeAp f l)).fn = (Square.map f (connectionJoin l)).fn := by
  funext i j; simp [connectionJoin, cubeAp, Line.map, Square.map]

/-! ## §12 Cubical homotopy -/

structure CubeHomotopy {A : Type u} {a b : A} (l₁ l₂ : Line A a b) where
  fn : I → I → A
  at_i0 : ∀ j, fn i0 j = l₁.fn j
  at_i1 : ∀ j, fn i1 j = l₂.fn j
  at_j0 : ∀ i, fn i i0 = a
  at_j1 : ∀ i, fn i i1 = b

-- 54: Reflexive homotopy
def CubeHomotopy.refl_ {A : Type u} {a b : A} (l : Line A a b) :
    CubeHomotopy l l :=
  ⟨fun _ j => l.fn j, fun _ => rfl, fun _ => rfl, fun _ => l.bd0, fun _ => l.bd1⟩

-- 55: Homotopy → Square
def CubeHomotopy.toSquare {A : Type u} {a b : A}
    {l₁ l₂ : Line A a b} (h : CubeHomotopy l₁ l₂) :
    Square A a b a b where
  fn := h.fn
  c00 := by rw [h.at_j0]
  c01 := by rw [h.at_j1]
  c10 := by rw [h.at_j0]
  c11 := by rw [h.at_j1]

-- 56: Symmetry of homotopy
def CubeHomotopy.symm_ {A : Type u} {a b : A}
    {l₁ l₂ : Line A a b} (h : CubeHomotopy l₁ l₂) :
    CubeHomotopy l₂ l₁ where
  fn := fun i j => h.fn (neg i) j
  at_i0 := fun j => by show h.fn (neg i0) j = l₂.fn j; simp [neg]; exact h.at_i1 j
  at_i1 := fun j => by show h.fn (neg i1) j = l₁.fn j; simp [neg]; exact h.at_i0 j
  at_j0 := fun i => h.at_j0 (neg i)
  at_j1 := fun i => h.at_j1 (neg i)

/-! ## §13 PathOver -/

structure PathOver {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) (y : P b) : Prop where
  over : Path.transport (D := P) p x = y

-- 57: Reflexive PathOver
def PathOver.rfl_ {A : Type u} {P : A → Type v} {a : A} (x : P a) :
    PathOver (Path.refl a) x x := ⟨rfl⟩

-- 58: From transport equality
def PathOver.ofEq {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) (y : P b) (h : Path.transport (D := P) p x = y) :
    PathOver p x y := ⟨h⟩

-- 59: Composition of PathOvers
theorem PathOver.trans_ {A : Type u} {P : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c} {x : P a} {y : P b} {z : P c}
    (po1 : PathOver p x y) (po2 : PathOver q y z) :
    PathOver (Path.trans p q) x z := by
  constructor; rw [Path.transport_trans, po1.over]; exact po2.over

-- 60: Symmetry of PathOvers
theorem PathOver.symm_ {A : Type u} {P : A → Type v} {a b : A}
    {p : Path a b} {x : P a} {y : P b}
    (po : PathOver p x y) : PathOver (Path.symm p) y x := by
  constructor; rw [← po.over]; exact Path.transport_symm_left (D := P) p x

/-! ## §14 Fibrant structure -/

class CubicallyFibrant (A : Type u) where
  fill : ∀ (a b c : A), Path a b → Path a c → Path b c

-- 61: All types are cubically fibrant
instance instCubFibrant (A : Type u) : CubicallyFibrant A where
  fill := fun _ _ _ p q => Path.trans (Path.symm p) q

-- 62: Fill is just symm-trans
theorem fill_eq_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    @CubicallyFibrant.fill A (instCubFibrant A) a b c p q =
    Path.trans (Path.symm p) q := rfl

/-! ## §15 GlueData -/

structure GlueData (A B : Type u) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

-- 63: Identity glue
def GlueData.id_ (A : Type u) : GlueData A A :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

-- 64: Composition of glue data
def GlueData.comp {A B C : Type u} (g : GlueData A B) (h : GlueData B C) :
    GlueData A C where
  toFun := fun a => h.toFun (g.toFun a)
  invFun := fun c => g.invFun (h.invFun c)
  left_inv := fun a => by simp [h.left_inv, g.left_inv]
  right_inv := fun c => by simp [g.right_inv, h.right_inv]

-- 65: Inverse glue data
def GlueData.symm_ {A B : Type u} (g : GlueData A B) : GlueData B A :=
  ⟨g.invFun, g.toFun, g.right_inv, g.left_inv⟩

end ComputationalPaths.Path.Homotopy.CubicalDeep
