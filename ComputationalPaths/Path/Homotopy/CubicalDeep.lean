/-
# Deep Cubical Type Theory via Computational Paths

Cubical structures modeled through Path/Step/trans/symm: abstract interval,
face maps, degeneracies, connections, Kan operations, coercion, transport.

## References
- Cohen–Coquand–Huber–Mörtberg, "Cubical Type Theory" (2018)
- Bezem–Coquand–Huber, "A model of type theory in cubical sets" (2014)
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace CubicalDeep

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Abstract Interval -/

inductive Iv where
  | i0 : Iv
  | i1 : Iv
deriving DecidableEq, Repr

def Iv.neg : Iv → Iv
  | .i0 => .i1
  | .i1 => .i0

def Iv.min : Iv → Iv → Iv
  | .i0, _ => .i0
  | _, .i0 => .i0
  | .i1, .i1 => .i1

def Iv.max : Iv → Iv → Iv
  | .i1, _ => .i1
  | _, .i1 => .i1
  | .i0, .i0 => .i0

-- 1: neg involution
theorem Iv.neg_neg (i : Iv) : i.neg.neg = i := by cases i <;> rfl

-- 2: De Morgan
theorem Iv.neg_min (i j : Iv) : (Iv.min i j).neg = Iv.max i.neg j.neg := by
  cases i <;> cases j <;> rfl

-- 3: De Morgan dual
theorem Iv.neg_max (i j : Iv) : (Iv.max i j).neg = Iv.min i.neg j.neg := by
  cases i <;> cases j <;> rfl

-- 4
theorem Iv.min_comm (i j : Iv) : Iv.min i j = Iv.min j i := by
  cases i <;> cases j <;> rfl

-- 5
theorem Iv.max_comm (i j : Iv) : Iv.max i j = Iv.max j i := by
  cases i <;> cases j <;> rfl

-- 6
theorem Iv.min_assoc (i j k : Iv) : Iv.min (Iv.min i j) k = Iv.min i (Iv.min j k) := by
  cases i <;> cases j <;> cases k <;> rfl

-- 7
theorem Iv.max_assoc (i j k : Iv) : Iv.max (Iv.max i j) k = Iv.max i (Iv.max j k) := by
  cases i <;> cases j <;> cases k <;> rfl

-- 8
theorem Iv.min_max_absorb (i j : Iv) : Iv.min i (Iv.max i j) = i := by
  cases i <;> cases j <;> rfl

-- 9
theorem Iv.max_min_absorb (i j : Iv) : Iv.max i (Iv.min i j) = i := by
  cases i <;> cases j <;> rfl

-- 10
theorem Iv.min_self (i : Iv) : Iv.min i i = i := by cases i <;> rfl

-- 11
theorem Iv.max_self (i : Iv) : Iv.max i i = i := by cases i <;> rfl

-- 12
theorem Iv.min_max_distrib (i j k : Iv) :
    Iv.min i (Iv.max j k) = Iv.max (Iv.min i j) (Iv.min i k) := by
  cases i <;> cases j <;> cases k <;> rfl

-- 13
theorem Iv.max_min_distrib (i j k : Iv) :
    Iv.max i (Iv.min j k) = Iv.min (Iv.max i j) (Iv.max i k) := by
  cases i <;> cases j <;> cases k <;> rfl

/-! ## Lines -/

structure Line (A : Type u) where
  atI0 : A
  atI1 : A
  path  : Path atI0 atI1

def Line.const (a : A) : Line A := ⟨a, a, Path.refl a⟩
def Line.rev (l : Line A) : Line A := ⟨l.atI1, l.atI0, Path.symm l.path⟩

def Line.eval (l : Line A) : Iv → A
  | .i0 => l.atI0
  | .i1 => l.atI1

-- 14
theorem Line.eval_const (a : A) (i : Iv) : (Line.const a).eval i = a := by
  cases i <;> rfl

-- 15
theorem Line.eval_rev_swap (l : Line A) :
    l.rev.eval .i0 = l.eval .i1 ∧ l.rev.eval .i1 = l.eval .i0 :=
  ⟨rfl, rfl⟩

/-! ## Squares -/

structure Square {A : Type u} (a₀₀ a₀₁ a₁₀ a₁₁ : A) where
  top    : Path a₀₀ a₀₁
  bottom : Path a₁₀ a₁₁
  left   : Path a₀₀ a₁₀
  right  : Path a₀₁ a₁₁
  coh    : Path.trans top right = Path.trans left bottom

/-! ## Connections -/

def connectionMin {a b : A} (p : Path a b) :
    Square a a a b where
  top    := Path.refl a
  bottom := p
  left   := Path.refl a
  right  := p
  coh    := by simp

def connectionMax {a b : A} (p : Path a b) :
    Square a b b b where
  top    := p
  bottom := Path.refl b
  left   := p
  right  := Path.refl b
  coh    := by simp

-- 16
theorem connectionMin_top {a b : A} (p : Path a b) :
    (connectionMin p).top = Path.refl a := rfl

-- 17
theorem connectionMax_bottom {a b : A} (p : Path a b) :
    (connectionMax p).bottom = Path.refl b := rfl

-- 18
theorem connectionMin_right {a b : A} (p : Path a b) :
    (connectionMin p).right = p := rfl

-- 19
theorem connectionMax_left {a b : A} (p : Path a b) :
    (connectionMax p).left = p := rfl

/-! ## Kan Composition -/

def kanComp {a b c : A} (p : Path a b) (q : Path a c) : Path b c :=
  Path.trans (Path.symm p) q

-- 20
theorem kanComp_refl_left {a b : A} (p : Path a b) :
    kanComp (Path.refl a) p = p := by simp [kanComp]

-- 21
theorem kanComp_refl_right {a b : A} (p : Path a b) :
    kanComp p (Path.refl a) = Path.symm p := by simp [kanComp]

-- 22
theorem kanComp_assoc {a b c d : A} (p : Path a b) (q : Path a c) (r : Path c d) :
    kanComp p (Path.trans q r) = Path.trans (kanComp p q) r := by
  unfold kanComp; exact (Path.trans_assoc _ _ _).symm

/-! ## Coercion and Transport -/

def coe' {a b : A} (P : A → Type v) (p : Path a b) (x : P a) : P b :=
  Path.cast (D := P) p x

-- 23
theorem coe_refl' (P : A → Type v) (a : A) (x : P a) :
    coe' P (Path.refl a) x = x := rfl

-- 24
theorem coe_trans' {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (x : P a) :
    coe' P (Path.trans p q) x = coe' P q (coe' P p x) := by
  cases p with | mk sp pp => cases q with | mk sq pq => cases pp; cases pq; rfl

-- 25
theorem coe_symm_trans' {a b : A} (P : A → Type v) (p : Path a b) (x : P a) :
    coe' P (Path.symm p) (coe' P p x) = x := by
  cases p with | mk s pr => cases pr; rfl

-- 26
theorem coe_trans_symm' {a b : A} (P : A → Type v) (p : Path a b) (y : P b) :
    coe' P p (coe' P (Path.symm p) y) = y := by
  cases p with | mk s pr => cases pr; rfl

-- 27: transport in constant family
theorem transport_const' {a b : A} (P : Type v) (p : Path a b) (x : P) :
    coe' (fun _ => P) p x = x := by
  cases p with | mk s pr => cases pr; rfl

-- 28: transport in product family
theorem transport_prod' {a b : A} (P Q : A → Type v) (p : Path a b) (x : P a × Q a) :
    coe' (fun z => P z × Q z) p x = (coe' P p x.1, coe' Q p x.2) := by
  cases p with | mk s pr => cases pr; rfl

-- 29: transport along kanComp
theorem coe_kanComp {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path a c) (x : P b) :
    coe' P (kanComp p q) x = coe' P q (coe' P (Path.symm p) x) :=
  coe_trans' P (Path.symm p) q x

/-! ## PathOver -/

structure PathOver {A : Type u} (P : A → Type v) {a b : A}
    (p : Path a b) (u : P a) (v : P b) : Prop where
  over : coe' P p u = v

-- 30
theorem pathOver_refl_iff (P : A → Type v) (a : A) (u v : P a) :
    PathOver P (Path.refl a) u v ↔ u = v :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

-- 31: PathOver composition
theorem pathOver_comp {P : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c} {u : P a} {v : P b} {w : P c}
    (po₁ : PathOver P p u v) (po₂ : PathOver P q v w) :
    PathOver P (Path.trans p q) u w := by
  constructor; rw [coe_trans']; rw [po₁.over]; exact po₂.over

-- 32: PathOver symmetry
theorem pathOver_inv {P : A → Type v} {a b : A}
    {p : Path a b} {u : P a} {v : P b}
    (po : PathOver P p u v) : PathOver P (Path.symm p) v u := by
  constructor; rw [← po.over]; exact coe_symm_trans' P p u

/-! ## Square Constructions -/

def Square.const (a : A) : Square a a a a where
  top    := Path.refl a
  bottom := Path.refl a
  left   := Path.refl a
  right  := Path.refl a
  coh    := rfl

def pathToSquare {a b : A} (p : Path a b) :
    Square a b a b where
  top    := p
  bottom := p
  left   := Path.refl a
  right  := Path.refl b
  coh    := by simp

-- 33
theorem pathToSquare_top {a b : A} (p : Path a b) :
    (pathToSquare p).top = p := rfl

-- 34
theorem pathToSquare_left {a b : A} (p : Path a b) :
    (pathToSquare p).left = Path.refl a := rfl

/-- Square with compatible faces for horizontal composition. -/
def Square.hcomp {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
    (s₁ : Square a₀₀ a₀₁ a₁₀ a₁₁)
    (s₂ : Square a₀₁ a₀₂ a₁₁ a₁₂)
    (hface : s₁.right = s₂.left) :
    Square a₀₀ a₀₂ a₁₀ a₁₂ where
  top    := Path.trans s₁.top s₂.top
  bottom := Path.trans s₁.bottom s₂.bottom
  left   := s₁.left
  right  := s₂.right
  coh    := by
    rw [Path.trans_assoc s₁.top s₂.top s₂.right]
    rw [s₂.coh, ← hface]
    rw [← Path.trans_assoc s₁.top s₁.right s₂.bottom]
    rw [s₁.coh]
    exact Path.trans_assoc s₁.left s₁.bottom s₂.bottom

-- 35
theorem Square.hcomp_left {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
    (s₁ : Square a₀₀ a₀₁ a₁₀ a₁₁) (s₂ : Square a₀₁ a₀₂ a₁₁ a₁₂)
    (hf : s₁.right = s₂.left) :
    (s₁.hcomp s₂ hf).left = s₁.left := rfl

-- 36
theorem Square.hcomp_right {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
    (s₁ : Square a₀₀ a₀₁ a₁₀ a₁₁) (s₂ : Square a₀₁ a₀₂ a₁₁ a₁₂)
    (hf : s₁.right = s₂.left) :
    (s₁.hcomp s₂ hf).right = s₂.right := rfl

/-! ## Glue Data / Equivalences -/

structure GlueData (A : Type u) (B : Type v) where
  fwd : A → B
  bwd : B → A
  sec : ∀ b, fwd (bwd b) = b
  ret : ∀ a, bwd (fwd a) = a

-- 37
def GlueData.identity (A : Type u) : GlueData A A where
  fwd := _root_.id; bwd := _root_.id; sec := fun _ => rfl; ret := fun _ => rfl

-- 38
def GlueData.inv (g : GlueData A B) : GlueData B A where
  fwd := g.bwd; bwd := g.fwd; sec := g.ret; ret := g.sec

-- 39
theorem GlueData.inv_inv (g : GlueData A B) : g.inv.inv = g := by cases g; rfl

-- 40: transport along a path gives a glue data
def GlueData.ofPath {a b : A} (P : A → Type v) (p : Path a b) :
    GlueData (P a) (P b) where
  fwd := coe' P p
  bwd := coe' P (Path.symm p)
  sec := coe_trans_symm' P p
  ret := coe_symm_trans' P p

-- 41: glue data of refl path is identity
theorem GlueData.ofPath_refl (P : A → Type v) (a : A) :
    GlueData.ofPath P (Path.refl a) = GlueData.identity (P a) := by
  simp [ofPath, identity]
  constructor <;> rfl

/-! ## Contractibility -/

structure IsContr (A : Type u) where
  center : A
  contract : ∀ x : A, Path center x

-- 42: Unit is contractible
def unitContr : IsContr Unit where
  center := ()
  contract := fun _ => Path.refl ()

-- 43: contractible → any two equality proofs between same endpoints agree
theorem isContr_paths_eq (hc : IsContr A) {a b : A} (p q : Path a b) :
    p.proof = q.proof := Subsingleton.elim _ _

/-! ## Composition Structures -/

structure CompStr (A : Type u) where
  comp : {a b c : A} → Path a b → Path b c → Path a c
  lid_left : ∀ {a b : A} (p : Path a b), comp (Path.refl a) p = p
  lid_right : ∀ {a b : A} (p : Path a b), comp p (Path.refl b) = p
  assoc' : ∀ {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d),
    comp (comp p q) r = comp p (comp q r)

-- 44
def stdCompStr : CompStr A where
  comp := Path.trans
  lid_left := Path.trans_refl_left
  lid_right := Path.trans_refl_right
  assoc' := Path.trans_assoc

-- 45
theorem stdCompStr_comp_eq {a b c : A} (p : Path a b) (q : Path b c) :
    (stdCompStr (A := A)).comp p q = Path.trans p q := rfl

/-! ## Homotopy Between Functions -/

@[ext]
structure Htpy (f g : A → B) where
  at_ : ∀ x : A, Path (f x) (g x)

-- 46
def Htpy.rfl' (f : A → B) : Htpy f f where
  at_ := fun x => Path.refl (f x)

-- 47
def Htpy.inv (H : Htpy f g) : Htpy g f where
  at_ := fun x => Path.symm (H.at_ x)

-- 48
def Htpy.comp {f g h : A → B} (H₁ : Htpy f g) (H₂ : Htpy g h) : Htpy f h where
  at_ := fun x => Path.trans (H₁.at_ x) (H₂.at_ x)

-- 49: inv-inv
theorem Htpy.inv_inv (H : Htpy f g) : H.inv.inv = H := by
  ext x; exact Path.symm_symm (H.at_ x)

-- 50: rfl-comp
theorem Htpy.rfl_comp {f g : A → B} (H : Htpy f g) :
    (Htpy.rfl' f).comp H = H := by
  ext x; exact Path.trans_refl_left (H.at_ x)

-- 51: comp-rfl
theorem Htpy.comp_rfl {f g : A → B} (H : Htpy f g) :
    H.comp (Htpy.rfl' g) = H := by
  ext x; exact Path.trans_refl_right (H.at_ x)

-- 52: comp associativity
theorem Htpy.comp_assoc {f g h k : A → B}
    (H₁ : Htpy f g) (H₂ : Htpy g h) (H₃ : Htpy h k) :
    (H₁.comp H₂).comp H₃ = H₁.comp (H₂.comp H₃) := by
  ext x; exact Path.trans_assoc (H₁.at_ x) (H₂.at_ x) (H₃.at_ x)

/-! ## Function Extensionality via Homotopy -/

def happly {f g : A → B} (p : Path f g) : Htpy f g where
  at_ := fun x => Path.mk
    (p.steps.map (Step.map (· x)))
    (congrFun p.proof x)

-- 53
theorem happly_refl (f : A → B) :
    happly (Path.refl f) = Htpy.rfl' f := by
  simp [happly, Htpy.rfl', Path.refl]

/-! ## Filling and Degeneracy -/

def horizDegen {a b : A} (p : Path a b) :
    Square a b a b where
  top    := p
  bottom := p
  left   := Path.refl a
  right  := Path.refl b
  coh    := by simp

def vertDegen {a b : A} (p : Path a b) :
    Square a a b b where
  top    := Path.refl a
  bottom := Path.refl b
  left   := p
  right  := p
  coh    := by simp

-- 54
theorem horizDegen_top {a b : A} (p : Path a b) :
    (horizDegen p).top = p := rfl

-- 55
theorem vertDegen_left {a b : A} (p : Path a b) :
    (vertDegen p).left = p := rfl

/-! ## Square Symmetry -/

def Square.transpose {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) :
    Square a₀₀ a₁₀ a₀₁ a₁₁ where
  top    := s.left
  bottom := s.right
  left   := s.top
  right  := s.bottom
  coh    := s.coh.symm

-- 56
theorem Square.transpose_top {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) :
    s.transpose.top = s.left := rfl

-- 57
theorem Square.transpose_left {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) :
    s.transpose.left = s.top := rfl

-- 58: transpose involution
theorem Square.transpose_transpose {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) :
    s.transpose.transpose = s := by
  cases s; simp [transpose]

-- 59: connectionMin transpose
theorem connectionMin_transpose_coh {a b : A} (p : Path a b) :
    (connectionMin p).transpose.top = Path.refl a := rfl

/-! ## Dependent Kan -/

def depKanFill {a b : A} (P : A → Type v)
    (p : Path a b) (u : P a) : P b :=
  coe' P p u

-- 60
theorem depKanFill_refl (P : A → Type v) (a : A) (u : P a) :
    depKanFill P (Path.refl a) u = u := rfl

-- 61
theorem depKanFill_trans {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (u : P a) :
    depKanFill P (Path.trans p q) u = depKanFill P q (depKanFill P p u) :=
  coe_trans' P p q u

/-! ## Cubical Path Operations -/

def kanTransp {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- 62
theorem kanTransp_eq_trans {a b c : A} (p : Path a b) (q : Path b c) :
    kanTransp p q = Path.trans p q := rfl

-- 63
theorem kanTransp_refl_left {a b : A} (p : Path a b) :
    kanTransp (Path.refl a) p = p := Path.trans_refl_left p

-- 64
theorem kanTransp_refl_right {a b : A} (p : Path a b) :
    kanTransp p (Path.refl b) = p := Path.trans_refl_right p

-- 65
theorem kanTransp_assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    kanTransp (kanTransp p q) r = kanTransp p (kanTransp q r) :=
  Path.trans_assoc p q r

-- 66: kanComp via kanTransp
theorem kanComp_eq_kanTransp {a b c : A} (p : Path a b) (q : Path a c) :
    kanComp p q = kanTransp (Path.symm p) q := rfl

end CubicalDeep
end Path
end ComputationalPaths
