/-
# Deep Cubical Type Theory via Computational Paths

Abstract interval, De Morgan algebra, connections, face maps,
degeneracies, Kan composition, coercion/transport coherence,
PathOver, Glue data, squares, and cube algebra — all using
`Path`/`Step`/`trans`/`symm` from Core.

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

/-! ## §1 Abstract interval with De Morgan algebra -/

inductive Iv where
  | i0 : Iv
  | i1 : Iv
deriving DecidableEq, Repr

namespace Iv

def neg : Iv → Iv | .i0 => .i1 | .i1 => .i0
def min : Iv → Iv → Iv | .i0, _ => .i0 | _, .i0 => .i0 | .i1, .i1 => .i1
def max : Iv → Iv → Iv | .i1, _ => .i1 | _, .i1 => .i1 | .i0, .i0 => .i0

-- 1: involution
theorem neg_neg (i : Iv) : i.neg.neg = i := by cases i <;> rfl
-- 2: De Morgan for min
theorem neg_min (i j : Iv) : (min i j).neg = max i.neg j.neg := by
  cases i <;> cases j <;> rfl
-- 3: De Morgan for max
theorem neg_max (i j : Iv) : (max i j).neg = min i.neg j.neg := by
  cases i <;> cases j <;> rfl
-- 4: commutativity of min
theorem min_comm (i j : Iv) : min i j = min j i := by cases i <;> cases j <;> rfl
-- 5: commutativity of max
theorem max_comm (i j : Iv) : max i j = max j i := by cases i <;> cases j <;> rfl
-- 6: associativity of min
theorem min_assoc (i j k : Iv) : min (min i j) k = min i (min j k) := by
  cases i <;> cases j <;> cases k <;> rfl
-- 7: associativity of max
theorem max_assoc (i j k : Iv) : max (max i j) k = max i (max j k) := by
  cases i <;> cases j <;> cases k <;> rfl
-- 8: absorption
theorem min_max_absorb (i j : Iv) : min i (max i j) = i := by cases i <;> cases j <;> rfl
-- 9: absorption dual
theorem max_min_absorb (i j : Iv) : max i (min i j) = i := by cases i <;> cases j <;> rfl
-- 10: idempotence
theorem min_self (i : Iv) : min i i = i := by cases i <;> rfl
-- 11: idempotence dual
theorem max_self (i : Iv) : max i i = i := by cases i <;> rfl
-- 12: distributivity
theorem min_max_distrib (i j k : Iv) :
    min i (max j k) = max (min i j) (min i k) := by cases i <;> cases j <;> cases k <;> rfl
-- 13: identity elements
theorem min_i1 (i : Iv) : min i .i1 = i := by cases i <;> rfl
-- 14: identity elements dual
theorem max_i0 (i : Iv) : max i .i0 = i := by cases i <;> rfl
-- 15: complement
theorem min_neg (i : Iv) : min i i.neg = .i0 := by cases i <;> rfl
-- 16: complement dual
theorem max_neg (i : Iv) : max i i.neg = .i1 := by cases i <;> rfl

end Iv

/-! ## §2 Lines and face maps -/

structure Line (A : Type u) where
  atI0 : A
  atI1 : A
  path  : Path atI0 atI1

def Line.const (a : A) : Line A := ⟨a, a, Path.refl a⟩
def Line.rev (l : Line A) : Line A := ⟨l.atI1, l.atI0, Path.symm l.path⟩
def Line.eval (l : Line A) : Iv → A | .i0 => l.atI0 | .i1 => l.atI1

-- 17: eval const
theorem Line.eval_const (a : A) (i : Iv) : (Line.const a).eval i = a := by
  cases i <;> rfl

-- 18: rev swaps endpoints
theorem Line.eval_rev_i0 (l : Line A) : l.rev.eval .i0 = l.eval .i1 := rfl
theorem Line.eval_rev_i1 (l : Line A) : l.rev.eval .i1 = l.eval .i0 := rfl

/-! ## §3 Squares -/

structure Square {A : Type u} (a₀₀ a₀₁ a₁₀ a₁₁ : A) where
  top    : Path a₀₀ a₀₁
  bottom : Path a₁₀ a₁₁
  left   : Path a₀₀ a₁₀
  right  : Path a₀₁ a₁₁
  coh    : Path.trans top right = Path.trans left bottom

def Square.const (a : A) : Square a a a a :=
  ⟨Path.refl a, Path.refl a, Path.refl a, Path.refl a, rfl⟩

/-! ## §4 Connections -/

def connectionMin {a b : A} (p : Path a b) : Square a a a b where
  top := Path.refl a; bottom := p; left := Path.refl a; right := p
  coh := by simp

def connectionMax {a b : A} (p : Path a b) : Square a b b b where
  top := p; bottom := Path.refl b; left := p; right := Path.refl b
  coh := by simp

-- 19: connectionMin top is refl
theorem connectionMin_top {a b : A} (p : Path a b) :
    (connectionMin p).top = Path.refl a := rfl

-- 20: connectionMax right is refl
theorem connectionMax_right {a b : A} (p : Path a b) :
    (connectionMax p).right = Path.refl b := rfl

-- 21: connectionMin on refl
theorem connectionMin_refl (a : A) :
    connectionMin (Path.refl a) = Square.const a := by
  simp [connectionMin, Square.const]

-- 22: connectionMax on refl
theorem connectionMax_refl (a : A) :
    connectionMax (Path.refl a) = Square.const a := by
  simp [connectionMax, Square.const]

/-! ## §5 Square transpose -/

def Square.transpose {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) : Square a₀₀ a₁₀ a₀₁ a₁₁ where
  top := s.left; bottom := s.right; left := s.top; right := s.bottom
  coh := s.coh.symm

-- 23: transpose involution
theorem Square.transpose_transpose {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (s : Square a₀₀ a₀₁ a₁₀ a₁₁) : s.transpose.transpose = s := by
  cases s; simp [transpose]

-- 24: transpose of const
theorem Square.transpose_const (a : A) :
    (Square.const a).transpose = Square.const a := by
  simp [Square.const, Square.transpose]

/-! ## §6 Degeneracy squares -/

def horizDegen {a b : A} (p : Path a b) : Square a b a b where
  top := p; bottom := p; left := Path.refl a; right := Path.refl b
  coh := by simp

def vertDegen {a b : A} (p : Path a b) : Square a a b b where
  top := Path.refl a; bottom := Path.refl b; left := p; right := p
  coh := by simp

-- 25: horizDegen is transpose of vertDegen
theorem horizDegen_eq_transpose_vertDegen {a b : A} (p : Path a b) :
    horizDegen p = (vertDegen p).transpose := by
  simp [horizDegen, vertDegen, Square.transpose]

-- 26: vertDegen of refl is const
theorem vertDegen_refl (a : A) : vertDegen (Path.refl a) = Square.const a := by
  simp [vertDegen, Square.const]

-- 27: horizDegen of refl is const
theorem horizDegen_refl (a : A) : horizDegen (Path.refl a) = Square.const a := by
  simp [horizDegen, Square.const]

/-! ## §7 Kan composition -/

def kanComp {a b c : A} (p : Path a b) (q : Path a c) : Path b c :=
  Path.trans (Path.symm p) q

-- 28: kanComp refl left
theorem kanComp_refl_left {a b : A} (p : Path a b) :
    kanComp (Path.refl a) p = p := by simp [kanComp]

-- 29: kanComp refl right
theorem kanComp_refl_right {a b : A} (p : Path a b) :
    kanComp p (Path.refl a) = Path.symm p := by simp [kanComp]

-- 30: kanComp associativity
theorem kanComp_assoc {a b c d : A}
    (p : Path a b) (q : Path a c) (r : Path c d) :
    kanComp p (Path.trans q r) = Path.trans (kanComp p q) r := by
  unfold kanComp; exact (Path.trans_assoc (Path.symm p) q r).symm

/-! ## §8 Coercion / transport -/

def coe' {a b : A} (P : A → Type v) (p : Path a b) (x : P a) : P b :=
  Path.cast (D := P) p x

-- 31: refl transport
theorem coe_refl' (P : A → Type v) (a : A) (x : P a) :
    coe' P (Path.refl a) x = x := rfl

-- 32: trans transport
theorem coe_trans' {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (x : P a) :
    coe' P (Path.trans p q) x = coe' P q (coe' P p x) := by
  cases p with | mk sp pp => cases q with | mk sq pq => cases pp; cases pq; rfl

-- 33: round-trip
theorem coe_symm_trans' {a b : A} (P : A → Type v) (p : Path a b) (x : P a) :
    coe' P (Path.symm p) (coe' P p x) = x := by
  cases p with | mk s pr => cases pr; rfl

-- 34: round-trip dual
theorem coe_trans_symm' {a b : A} (P : A → Type v) (p : Path a b) (y : P b) :
    coe' P p (coe' P (Path.symm p) y) = y := by
  cases p with | mk s pr => cases pr; rfl

-- 35: constant family
theorem transport_const' {a b : A} (P : Type v) (p : Path a b) (x : P) :
    coe' (fun _ => P) p x = x := by
  cases p with | mk s pr => cases pr; rfl

-- 36: product family
theorem transport_prod' {a b : A} (P Q : A → Type v) (p : Path a b)
    (x : P a × Q a) :
    coe' (fun z => P z × Q z) p x = (coe' P p x.1, coe' Q p x.2) := by
  cases p with | mk s pr => cases pr; rfl

-- 37: function family
theorem transport_fun {a b : A} (P Q : A → Type v) (p : Path a b)
    (f : P a → Q a) (y : P b) :
    coe' (fun z => P z → Q z) p f y =
    coe' Q p (f (coe' P (Path.symm p) y)) := by
  cases p with | mk s pr => cases pr; rfl

-- 38: triple composition
theorem coe_trans_triple {a b c d : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (r : Path c d) (x : P a) :
    coe' P (Path.trans (Path.trans p q) r) x =
    coe' P r (coe' P q (coe' P p x)) := by
  rw [coe_trans', coe_trans']

-- 39: triple roundtrip
theorem coe_triple_roundtrip {a b : A} (P : A → Type v)
    (p : Path a b) (x : P a) :
    coe' P p (coe' P (Path.symm p) (coe' P p x)) = coe' P p x := by
  rw [coe_symm_trans']

-- 40: symm-then-self is identity
theorem coe_symm_then_self {a b : A} (P : A → Type v) (p : Path a b) (y : P b) :
    coe' P (Path.trans (Path.symm p) p) y = y := by
  rw [coe_trans']; exact coe_trans_symm' P p y

/-! ## §9 PathOver -/

structure PathOver {A : Type u} (P : A → Type v) {a b : A}
    (p : Path a b) (u : P a) (v : P b) : Prop where
  over : coe' P p u = v

-- 41: refl characterisation
theorem pathOver_refl_iff (P : A → Type v) (a : A) (u v : P a) :
    PathOver P (Path.refl a) u v ↔ u = v := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

-- 42: composition of PathOvers
theorem pathOver_trans {P : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c} {u : P a} {v : P b} {w : P c}
    (po₁ : PathOver P p u v) (po₂ : PathOver P q v w) :
    PathOver P (Path.trans p q) u w := by
  constructor; rw [coe_trans']; rw [po₁.over]; exact po₂.over

-- 43: symmetry of PathOver
theorem pathOver_symm {P : A → Type v} {a b : A}
    {p : Path a b} {u : P a} {v : P b}
    (po : PathOver P p u v) : PathOver P (Path.symm p) v u := by
  constructor; rw [← po.over]; exact coe_symm_trans' P p u

/-! ## §10 Glue data -/

structure GlueData (A : Type u) (B : Type v) where
  fwd : A → B
  bwd : B → A
  sec : ∀ b, fwd (bwd b) = b
  ret : ∀ a, bwd (fwd a) = a

def GlueData.identity (A : Type u) : GlueData A A :=
  ⟨_root_.id, _root_.id, fun _ => rfl, fun _ => rfl⟩

def GlueData.inv (g : GlueData A B) : GlueData B A :=
  ⟨g.bwd, g.fwd, g.ret, g.sec⟩

-- 44: inv involution
theorem GlueData.inv_inv (g : GlueData A B) : g.inv.inv = g := by cases g; rfl

-- 45: transport gives glue data
def GlueData.ofPath {a b : A} (P : A → Type v) (p : Path a b) :
    GlueData (P a) (P b) where
  fwd := coe' P p
  bwd := coe' P (Path.symm p)
  sec := coe_trans_symm' P p
  ret := coe_symm_trans' P p

-- 46: ofPath refl is identity
theorem GlueData.ofPath_refl (P : A → Type v) (a : A) :
    GlueData.ofPath P (Path.refl a) = GlueData.identity (P a) := by
  simp [GlueData.ofPath, GlueData.identity]; constructor <;> rfl

-- 47: GlueData composition
def GlueData.comp (g₁ : GlueData A B) (g₂ : GlueData B C) : GlueData A C where
  fwd := g₂.fwd ∘ g₁.fwd
  bwd := g₁.bwd ∘ g₂.bwd
  sec := fun c => by simp [Function.comp]; rw [g₁.sec]; exact g₂.sec c
  ret := fun a => by simp [Function.comp]; rw [g₂.ret]; exact g₁.ret a

-- 48: comp with identity
theorem GlueData.comp_identity (g : GlueData A B) :
    g.comp (GlueData.identity B) = g := by
  simp [GlueData.comp, GlueData.identity]

-- 49: identity comp
theorem GlueData.identity_comp (g : GlueData A B) :
    (GlueData.identity A).comp g = g := by
  simp [GlueData.comp, GlueData.identity]

/-! ## §11 Contractibility -/

structure IsContr (A : Type u) where
  center : A
  contract : ∀ x, Path center x

-- 50: Unit is contractible
def unitContr : IsContr Unit := ⟨(), fun _ => Path.refl ()⟩

-- 51: contractible implies path proofs equal
theorem isContr_paths_eq (_hc : IsContr A) {a b : A} (p q : Path a b) :
    p.proof = q.proof := Subsingleton.elim _ _

/-! ## §12 Homotopy between functions -/

@[ext]
structure Htpy (f g : A → B) where
  at_ : ∀ x : A, Path (f x) (g x)

def Htpy.rfl' (f : A → B) : Htpy f f := ⟨fun x => Path.refl (f x)⟩
def Htpy.inv' {f g : A → B} (H : Htpy f g) : Htpy g f :=
  ⟨fun x => Path.symm (H.at_ x)⟩
def Htpy.comp' {f g h : A → B} (H₁ : Htpy f g) (H₂ : Htpy g h) : Htpy f h :=
  ⟨fun x => Path.trans (H₁.at_ x) (H₂.at_ x)⟩

-- 52: left unit
theorem Htpy.rfl_comp {f g : A → B} (H : Htpy f g) :
    Htpy.mk (fun x => Path.trans (Path.refl (f x)) (H.at_ x)) = H := by
  ext x; exact Path.trans_refl_left (H.at_ x)

-- 53: right unit
theorem Htpy.comp_rfl {f g : A → B} (H : Htpy f g) :
    Htpy.mk (fun x => Path.trans (H.at_ x) (Path.refl (g x))) = H := by
  ext x; exact Path.trans_refl_right (H.at_ x)

-- 54: associativity
theorem Htpy.comp_assoc {f g h k : A → B}
    (H₁ : Htpy f g) (H₂ : Htpy g h) (H₃ : Htpy h k) :
    Htpy.mk (fun x => Path.trans (Path.trans (H₁.at_ x) (H₂.at_ x)) (H₃.at_ x)) =
    Htpy.mk (fun x => Path.trans (H₁.at_ x) (Path.trans (H₂.at_ x) (H₃.at_ x))) := by
  ext x; exact Path.trans_assoc (H₁.at_ x) (H₂.at_ x) (H₃.at_ x)

/-! ## §13 happly -/

def happly {f g : A → B} (p : Path f g) : Htpy f g :=
  ⟨fun x => Path.mk (p.steps.map (Step.map (· x))) (congrFun p.proof x)⟩

-- 55: happly refl
theorem happly_refl (f : A → B) :
    happly (Path.refl f) = Htpy.rfl' f := by
  simp [happly, Htpy.rfl', Path.refl]

/-! ## §14 Dependent Kan filling -/

def depKanFill {a b : A} (P : A → Type v) (p : Path a b) (u : P a) : P b :=
  coe' P p u

-- 56: refl filling
theorem depKanFill_refl (P : A → Type v) (a : A) (u : P a) :
    depKanFill P (Path.refl a) u = u := rfl

-- 57: transitivity
theorem depKanFill_trans {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (u : P a) :
    depKanFill P (Path.trans p q) u = depKanFill P q (depKanFill P p u) :=
  coe_trans' P p q u

-- 58: symm cancel
theorem depKanFill_symm_cancel {a b : A} (P : A → Type v)
    (p : Path a b) (u : P a) :
    depKanFill P (Path.symm p) (depKanFill P p u) = u :=
  coe_symm_trans' P p u

/-! ## §15 Composition structure -/

structure CompStr (A : Type u) where
  comp : {a b c : A} → Path a b → Path b c → Path a c
  lid  : ∀ {a b : A} (p : Path a b), comp (Path.refl a) p = p
  rid  : ∀ {a b : A} (p : Path a b), comp p (Path.refl b) = p
  assoc' : ∀ {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d),
    comp (comp p q) r = comp p (comp q r)

-- 59: standard composition structure
def stdCompStr : CompStr A :=
  ⟨Path.trans, Path.trans_refl_left, Path.trans_refl_right, Path.trans_assoc⟩

-- 60: std comp is trans
theorem stdCompStr_comp_eq {a b c : A} (p : Path a b) (q : Path b c) :
    (stdCompStr (A := A)).comp p q = Path.trans p q := rfl

/-! ## §16 Cube2 -/

structure Cube2 (A : Type u) where
  line0 : Line A
  line1 : Line A
  side0 : Path line0.atI0 line1.atI0
  side1 : Path line0.atI1 line1.atI1

def Cube2.degen (l : Line A) : Cube2 A :=
  ⟨l, l, Path.refl l.atI0, Path.refl l.atI1⟩

-- 61: degen side0
theorem Cube2.degen_side0 (l : Line A) :
    (Cube2.degen l).side0 = Path.refl l.atI0 := rfl

-- 62: degen side1
theorem Cube2.degen_side1 (l : Line A) :
    (Cube2.degen l).side1 = Path.refl l.atI1 := rfl

/-! ## §17 Dependent action on paths (apd) -/

def apd {P : A → Type v} (f : ∀ x : A, P x) {a b : A} (p : Path a b) :
    PathOver P p (f a) (f b) := by
  constructor
  cases p with | mk s pr => cases pr; rfl

-- 63: apd on refl
theorem apd_refl {P : A → Type v} (f : ∀ x : A, P x) (a : A) :
    apd f (Path.refl a) = ⟨rfl⟩ := rfl

/-! ## §18 Line functoriality -/

def Line.map (f : A → B) (l : Line A) : Line B where
  atI0 := f l.atI0
  atI1 := f l.atI1
  path := Path.mk (l.path.steps.map (Step.map f)) (_root_.congrArg f l.path.proof)

-- 64: map preserves const
theorem Line.map_const (f : A → B) (a : A) :
    Line.map f (Line.const a) = Line.const (f a) := by
  simp [Line.map, Line.const, Path.refl]

-- 65: map commutes with eval
theorem Line.map_eval (f : A → B) (l : Line A) (i : Iv) :
    f (l.eval i) = (l.map f).eval i := by
  cases i <;> rfl

/-! ## §19 Square coherence extras -/

-- 66: connectionMin coherence at refl
theorem connectionMin_coh_refl (a : A) :
    (connectionMin (Path.refl a)).coh = rfl := by apply Subsingleton.elim

-- 67: connectionMax coherence at refl
theorem connectionMax_coh_refl (a : A) :
    (connectionMax (Path.refl a)).coh = rfl := by apply Subsingleton.elim

-- 68: const square coherence
theorem Square.const_coh (a : A) : (Square.const a).coh = rfl := by
  apply Subsingleton.elim

/-! ## §20 Kan transport = trans -/

def kanTransp {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- 69: kanTransp is trans
theorem kanTransp_eq_trans {a b c : A} (p : Path a b) (q : Path b c) :
    kanTransp p q = Path.trans p q := rfl

-- 70: kanTransp distributes over symm
theorem kanTransp_symm {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (kanTransp p q) = kanTransp (Path.symm q) (Path.symm p) := by
  unfold kanTransp; exact Path.symm_trans p q

-- 71: kanComp equals kanTransp with symm
theorem kanComp_eq_kanTransp {a b c : A} (p : Path a b) (q : Path a c) :
    kanComp p q = kanTransp (Path.symm p) q := rfl

/-! ## §21 GlueData round-trip -/

-- 72: comp_inv_fwd
theorem GlueData.comp_inv_fwd (g : GlueData A B) (a : A) :
    (g.comp g.inv).fwd a = a := by
  simp [GlueData.comp, GlueData.inv, Function.comp]; exact g.ret a

-- 73: inv_comp_fwd
theorem GlueData.inv_comp_fwd (g : GlueData A B) (b : B) :
    (g.inv.comp g).fwd b = b := by
  simp [GlueData.comp, GlueData.inv, Function.comp]; exact g.sec b

/-! ## §22 Transport along kanComp -/

-- 74: transport along kanComp
theorem coe_kanComp {a b c : A} (P : A → Type v)
    (p : Path a b) (q : Path a c) (x : P b) :
    coe' P (kanComp p q) x = coe' P q (coe' P (Path.symm p) x) :=
  coe_trans' P (Path.symm p) q x

-- 75: four-fold transport
theorem coe_four_assoc {a b c d e : A} (P : A → Type v)
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (x : P a) :
    coe' P (Path.trans (Path.trans (Path.trans p q) r) s) x =
    coe' P s (coe' P r (coe' P q (coe' P p x))) := by
  rw [coe_trans', coe_trans', coe_trans']

end CubicalDeep
end Path
end ComputationalPaths
