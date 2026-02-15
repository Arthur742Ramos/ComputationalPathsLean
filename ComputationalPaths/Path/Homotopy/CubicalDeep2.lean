/-
# Deep Cubical Homotopy Theory via Computational Paths
-/
import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Homotopy.CubicalDeep2

open ComputationalPaths.Path

universe u v w

abbrev I := Bool

-- 1-13: De Morgan interval algebra
@[simp] theorem neg_neg (i : I) : (!!i) = i := by cases i <;> rfl
@[simp] theorem and_comm' (a b : I) : (a && b) = (b && a) := by cases a <;> cases b <;> rfl
@[simp] theorem or_comm' (a b : I) : (a || b) = (b || a) := by cases a <;> cases b <;> rfl
@[simp] theorem and_assoc' (a b c : I) : ((a && b) && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] theorem or_assoc' (a b c : I) : ((a || b) || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] theorem and_false' (i : I) : (false && i) = false := by rfl
@[simp] theorem or_true' (i : I) : (true || i) = true := by rfl
@[simp] theorem and_true' (i : I) : (true && i) = i := by cases i <;> rfl
@[simp] theorem or_false' (i : I) : (false || i) = i := by cases i <;> rfl
@[simp] theorem dm_and (a b : I) : (!(a && b)) = (!a || !b) := by cases a <;> cases b <;> rfl
@[simp] theorem dm_or (a b : I) : (!(a || b)) = (!a && !b) := by cases a <;> cases b <;> rfl
@[simp] theorem and_idem (i : I) : (i && i) = i := by cases i <;> rfl
@[simp] theorem or_idem (i : I) : (i || i) = i := by cases i <;> rfl

-- §2 Lines (1-cubes)
structure Line (A : Type u) (a₀ a₁ : A) where
  fn : I → A
  bd0 : fn false = a₀
  bd1 : fn true  = a₁

-- 14
def Line.const {A : Type u} (a : A) : Line A a a where
  fn := fun _ => a; bd0 := rfl; bd1 := rfl

-- 15
def Line.rev {A : Type u} {a b : A} (l : Line A a b) : Line A b a where
  fn := fun i => l.fn (!i)
  bd0 := by simp; exact l.bd1
  bd1 := by simp; exact l.bd0

-- 16
theorem Line.rev_rev_fn {A : Type u} {a b : A} (l : Line A a b) :
    l.rev.rev.fn = l.fn := by funext i; simp [Line.rev]

-- 17
def Line.mapf {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) where
  fn := fun i => f (l.fn i)
  bd0 := by rw [l.bd0]
  bd1 := by rw [l.bd1]

-- 18
theorem Line.mapf_const {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Line.mapf f (Line.const a) = Line.const (f a) := by
  simp [Line.mapf, Line.const]

-- 19
def Line.ofPath {A : Type u} {a b : A} (_p : Path a b) : Line A a b where
  fn := fun i => match i with | false => a | true => b
  bd0 := rfl; bd1 := rfl

-- §3 Squares
structure Sq (A : Type u) (c00 c01 c10 c11 : A) where
  fn : I → I → A
  b00 : fn false false = c00
  b01 : fn false true  = c01
  b10 : fn true  false = c10
  b11 : fn true  true  = c11

-- 20
def Sq.const {A : Type u} (a : A) : Sq A a a a a where
  fn := fun _ _ => a; b00 := rfl; b01 := rfl; b10 := rfl; b11 := rfl

-- 21
def connMin {A : Type u} {a b : A} (l : Line A a b) : Sq A a a a b where
  fn := fun i j => l.fn (i && j)
  b00 := by simp; exact l.bd0
  b01 := by simp; exact l.bd0
  b10 := by simp; exact l.bd0
  b11 := by simp; exact l.bd1

-- 22
def connMax {A : Type u} {a b : A} (l : Line A a b) : Sq A a b b b where
  fn := fun i j => l.fn (i || j)
  b00 := by simp; exact l.bd0
  b01 := by simp; exact l.bd1
  b10 := by simp; exact l.bd1
  b11 := by simp; exact l.bd1

-- 23
theorem connMin_const_fn {A : Type u} (a : A) :
    (connMin (Line.const a)).fn = fun _ _ => a := by
  funext i j; simp [connMin, Line.const]

-- 24
theorem connMax_const_fn {A : Type u} (a : A) :
    (connMax (Line.const a)).fn = fun _ _ => a := by
  funext i j; simp [connMax, Line.const]

-- 25
def Sq.transpose {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Sq A c00 c10 c01 c11 where
  fn := fun i j => s.fn j i
  b00 := s.b00; b01 := s.b10; b10 := s.b01; b11 := s.b11

-- 26
theorem Sq.transpose_transpose_fn {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : s.transpose.transpose.fn = s.fn := by
  funext i j; rfl

-- 27
theorem connMin_symm_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connMin l).transpose.fn = (connMin l).fn := by
  funext i j; simp [Sq.transpose, connMin, and_comm']

-- 28
theorem connMax_symm_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connMax l).transpose.fn = (connMax l).fn := by
  funext i j; simp [Sq.transpose, connMax, or_comm']

-- §4 Face maps & diagonal
def Sq.faceL {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Line A c00 c01 where
  fn := fun j => s.fn false j; bd0 := s.b00; bd1 := s.b01

def Sq.faceR {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Line A c10 c11 where
  fn := fun j => s.fn true j; bd0 := s.b10; bd1 := s.b11

def Sq.faceB {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Line A c00 c10 where
  fn := fun i => s.fn i false; bd0 := s.b00; bd1 := s.b10

def Sq.faceT {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Line A c01 c11 where
  fn := fun i => s.fn i true; bd0 := s.b01; bd1 := s.b11

-- 29
def Sq.diag {A : Type u} {c00 c01 c10 c11 : A}
    (s : Sq A c00 c01 c10 c11) : Line A c00 c11 where
  fn := fun i => s.fn i i; bd0 := s.b00; bd1 := s.b11

-- 30
theorem connMin_diag_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connMin l).diag.fn = l.fn := by
  funext i; simp [Sq.diag, connMin]

-- 31
theorem connMax_diag_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connMax l).diag.fn = l.fn := by
  funext i; simp [Sq.diag, connMax]

-- 32
theorem connMin_faceL_fn {A : Type u} {a b : A} (l : Line A a b) :
    (connMin l).faceL.fn = fun _ => a := by
  funext j; simp [Sq.faceL, connMin]; exact l.bd0

-- §5 Kan composition
def kanComp {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- 33
theorem kanComp_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    kanComp (kanComp p q) r = kanComp p (kanComp q r) := by simp [kanComp]
-- 34
theorem kanComp_refl_left {A : Type u} {a b : A} (p : Path a b) :
    kanComp (Path.refl a) p = p := by simp [kanComp]
-- 35
theorem kanComp_refl_right {A : Type u} {a b : A} (p : Path a b) :
    kanComp p (Path.refl b) = p := by simp [kanComp]
-- 36
theorem kanComp_symm_toEq {A : Type u} {a b : A} (p : Path a b) :
    (kanComp p (Path.symm p)).toEq = rfl := by simp [kanComp]

-- §6 Cubical transport
def cubeTr {A : Type u} (P : A → Type v) {a b : A} (h : a = b) (x : P a) : P b := h ▸ x

-- 37
theorem cubeTr_rfl {A : Type u} {P : A → Type v} {a : A} (x : P a) :
    cubeTr P rfl x = x := rfl
-- 38
theorem cubeTr_eq_transport {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    cubeTr P p.toEq x = Path.transport (D := P) p x := by
  cases p with | mk s h => cases h; rfl
-- 39
theorem cubeTr_comp {A : Type u} {P : A → Type v} {a b c : A}
    (h₁ : a = b) (h₂ : b = c) (x : P a) :
    cubeTr P h₂ (cubeTr P h₁ x) = cubeTr P (h₁.trans h₂) x := by
  cases h₁; cases h₂; rfl
-- 40
theorem cubeTr_natural {A : Type u} {P Q : A → Type v}
    (f : ∀ x, P x → Q x) {a b : A} (h : a = b) (x : P a) :
    cubeTr Q h (f a x) = f b (cubeTr P h x) := by cases h; rfl

-- §7 Cubical ap
def cubeAp {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (l : Line A a b) : Line B (f a) (f b) := Line.mapf f l

-- 41
theorem cubeAp_const_line {A : Type u} {B : Type v} (f : A → B) (a : A) :
    cubeAp f (Line.const a) = Line.const (f a) := Line.mapf_const f a
-- 42
theorem cubeAp_id_fn {A : Type u} {a b : A} (l : Line A a b) :
    (cubeAp id l).fn = l.fn := by funext i; rfl
-- 43
theorem cubeAp_comp_fn {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (l : Line A a b) :
    (cubeAp (f ∘ g) l).fn = (cubeAp f (cubeAp g l)).fn := by funext i; rfl

-- §8 Cubical homotopy
structure CubeHtpy {A : Type u} {a b : A} (l₁ l₂ : Line A a b) where
  fn : I → I → A
  fi0 : ∀ j, fn false j = l₁.fn j
  fi1 : ∀ j, fn true  j = l₂.fn j
  fj0 : ∀ i, fn i false = a
  fj1 : ∀ i, fn i true  = b

-- 44
def CubeHtpy.refl {A : Type u} {a b : A} (l : Line A a b) : CubeHtpy l l where
  fn := fun _ j => l.fn j
  fi0 := fun _ => rfl
  fi1 := fun _ => rfl
  fj0 := fun _ => l.bd0
  fj1 := fun _ => l.bd1

-- 45
def CubeHtpy.toSq {A : Type u} {a b : A} {l₁ l₂ : Line A a b}
    (h : CubeHtpy l₁ l₂) : Sq A a b a b where
  fn := h.fn
  b00 := by rw [h.fj0]
  b01 := by rw [h.fj1]
  b10 := by rw [h.fj0]
  b11 := by rw [h.fj1]

-- §9 Path-squares
structure PathSq {A : Type u} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (top : Path a₀₀ a₀₁) (bot : Path a₁₀ a₁₁)
    (left : Path a₀₀ a₁₀) (right : Path a₀₁ a₁₁) : Prop where
  comm : Path.trans left bot = Path.trans top right

-- 46
def PathSq.hrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSq p p (Path.refl a) (Path.refl b) where
  comm := by simp
-- 47
def PathSq.vrefl {A : Type u} {a b : A} (p : Path a b) :
    PathSq (Path.refl a) (Path.refl b) p p where
  comm := by simp

-- §10 n-cubes
def NCube (n : Nat) (A : Type u) : Type u := (Fin n → I) → A

-- 48
def NCube.const (n : Nat) {A : Type u} (a : A) : NCube n A := fun _ => a

-- 49
def NCube.degen {A : Type u} {n : Nat} (d : Fin (n + 1)) (c : NCube n A) :
    NCube (n + 1) A :=
  fun coords => c (fun k =>
    if k.val < d.val then coords ⟨k.val, by omega⟩
    else coords ⟨k.val + 1, by omega⟩)

-- 50
theorem NCube.degen_const {A : Type u} {n : Nat} (a : A) (d : Fin (n + 1)) :
    NCube.degen d (NCube.const n a) = NCube.const (n + 1) a := by
  funext coords; simp [NCube.degen, NCube.const]

-- §11 Dependent transport
-- 51
def lineTr {A : Type u} {P : A → Type v} {a b : A} (p : Path a b) (x : P a) : P b :=
  Path.transport (D := P) p x

-- 52
theorem lineTr_refl {A : Type u} {P : A → Type v} {a : A} (x : P a) :
    lineTr (P := P) (Path.refl a) x = x := rfl

-- 53
theorem lineTr_trans {A : Type u} {P : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    lineTr (P := P) (Path.trans p q) x = lineTr (P := P) q (lineTr (P := P) p x) :=
  Path.transport_trans (D := P) p q x

-- 54
theorem lineTr_symm_cancel {A : Type u} {P : A → Type v} {a b : A}
    (p : Path a b) (x : P a) :
    lineTr (P := P) (Path.symm p) (lineTr (P := P) p x) = x :=
  Path.transport_symm_left (D := P) p x

-- 55
theorem dep_cube_nat {A : Type u} {P Q : A → Type v}
    (f : ∀ x, P x → Q x) {a b : A} (p : Path a b) (x : P a) :
    lineTr (P := Q) p (f a x) = f b (lineTr (P := P) p x) := by
  cases p with | mk s h => cases h; rfl

end ComputationalPaths.Path.Homotopy.CubicalDeep2
