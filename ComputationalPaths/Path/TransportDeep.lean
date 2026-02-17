/-
# Deep Path Transport Algebra — Dependent Rewriting via Computational Paths

Transport, dependent paths, ap/apd, fiber transport, naturality,
NatTrans — all via the concrete Path type.

90+ theorems/defs. ZERO sorry, ZERO Path.mk [Step.mk _ _ h] h.
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.TransportDeep

open ComputationalPaths.Path

universe u

variable {α : Type u}

/-! ## 1-3. Transport foundations -/

def transport {P : α → Type u} {a b : α} (p : Path a b) (x : P a) : P b :=
  p.toEq ▸ x

theorem transport_refl {P : α → Type u} {a : α} (x : P a) :
    transport (Path.refl a) x = x := by
  simp [transport, Path.refl]

theorem transport_eq {P : α → Type u} {a b : α} (p : Path a b) (x : P a) :
    transport p x = p.toEq ▸ x := rfl

/-! ## 4-6. Transport under symm -/

theorem transport_symm_cancel {P : α → Type u} {a b : α}
    (p : Path a b) (x : P a) :
    transport (Path.symm p) (transport p x) = x := by
  simp [transport]; cases p with | mk _ proof => cases proof; rfl

theorem transport_symm_cancel' {P : α → Type u} {a b : α}
    (p : Path a b) (y : P b) :
    transport p (transport (Path.symm p) y) = y := by
  simp [transport]; cases p with | mk _ proof => cases proof; rfl

theorem transport_const {B : Type u} {a b : α} (p : Path a b) (x : B) :
    transport (P := fun _ => B) p x = x := by
  simp [transport]; cases p with | mk _ proof => cases proof; rfl

/-! ## 7-9. ap (non-dependent map) -/

def ap {β : Type u} (f : α → β) {a b : α} (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

theorem ap_trans {β : Type u} (f : α → β) {a b c : α}
    (p : Path a b) (q : Path b c) :
    ap f (Path.trans p q) = Path.trans (ap f p) (ap f q) :=
  Path.congrArg_trans f p q

theorem ap_symm {β : Type u} (f : α → β) {a b : α} (p : Path a b) :
    ap f (Path.symm p) = Path.symm (ap f p) :=
  Path.congrArg_symm f p

theorem ap_refl_toEq {β : Type u} (f : α → β) (a : α) :
    (ap f (Path.refl a)).toEq = (Path.refl (f a)).toEq :=
  Subsingleton.elim _ _

/-! ## 10-12. ap composition -/

theorem ap_compose_toEq {β γ : Type u} (f : α → β) (g : β → γ) {a b : α}
    (p : Path a b) :
    (ap g (ap f p)).toEq = (ap (g ∘ f) p).toEq :=
  Subsingleton.elim _ _

theorem ap_const_toEq {β : Type u} (b₀ : β) {a b : α} (p : Path a b) :
    (ap (fun _ => b₀) p).toEq = (Path.refl b₀).toEq :=
  Subsingleton.elim _ _

theorem ap_id_toEq {a b : α} (p : Path a b) :
    (ap id p).toEq = p.toEq := Subsingleton.elim _ _

/-! ## 13-15. Dependent map -/

def apd {P : α → Type u} (f : ∀ x, P x) {a b : α} (p : Path a b) :
    transport p (f a) = f b := by
  cases p with | mk _ proof => cases proof; rfl

theorem apd_refl_eq {P : α → Type u} (f : ∀ x, P x) (a : α) :
    apd f (Path.refl a) = rfl := rfl

theorem apd_irrel {P : α → Type u} (f : ∀ x, P x) {a b : α}
    (p q : Path a b) : apd f p = apd f q := by
  simp [apd]

/-! ## 16-18. Fiber transport -/

def fiberFwd {P : α → Type u} {a b : α} (p : Path a b) : P a → P b :=
  transport p

def fiberBwd {P : α → Type u} {a b : α} (p : Path a b) : P b → P a :=
  transport (Path.symm p)

theorem fiber_roundtrip {P : α → Type u} {a b : α} (p : Path a b) (x : P a) :
    fiberBwd p (fiberFwd p x) = x :=
  transport_symm_cancel p x

theorem fiber_roundtrip' {P : α → Type u} {a b : α} (p : Path a b) (y : P b) :
    fiberFwd p (fiberBwd p y) = y :=
  transport_symm_cancel' p y

/-! ## 19-21. PathOver -/

def PathOver {P : α → Type u} {a b : α} (p : Path a b) (u : P a) (v : P b) :
    Prop := transport p u = v

theorem pathOver_refl {P : α → Type u} {a : α} (u : P a) :
    PathOver (Path.refl a) u u := transport_refl u

theorem pathOver_const_iff {B : Type u} {a b : α} {p : Path a b} {x y : B} :
    PathOver (P := fun _ => B) p x y ↔ x = y := by
  constructor
  · intro h; simp [PathOver] at h; rw [transport_const] at h; exact h
  · intro h; simp [PathOver]; rw [transport_const]; exact h

/-! ## 22-24. Transport path irrel -/

theorem transport_path_irrel {P : α → Type u} {a b : α}
    (p q : Path a b) (x : P a) : transport p x = transport q x := by
  simp [transport]

theorem pathOver_path_irrel {P : α → Type u} {a b : α}
    {p q : Path a b} {u : P a} {v : P b}
    (h : PathOver p u v) : PathOver q u v := by
  rw [PathOver] at *; rw [transport_path_irrel q p]; exact h

theorem transport_ap_eq {β : Type u} {P : β → Type u} (f : α → β) {a b : α}
    (p : Path a b) (x : P (f a)) :
    transport (P := P) (ap f p) x = transport (P := P ∘ f) p x := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## 25-27. Horizontal composition -/

def hcomp {a b c : α} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

theorem hcomp_assoc {a b c d : α} (p : Path a b) (q : Path b c)
    (r : Path c d) :
    hcomp (hcomp p q) r = hcomp p (hcomp q r) :=
  Path.trans_assoc p q r

theorem hcomp_refl_left {a b : α} (p : Path a b) :
    hcomp (Path.refl a) p = p := Path.trans_refl_left p

theorem hcomp_refl_right {a b : α} (p : Path a b) :
    hcomp p (Path.refl b) = p := Path.trans_refl_right p

/-! ## 28-30. Symm and hcomp -/

theorem symm_hcomp {a b c : α} (p : Path a b) (q : Path b c) :
    Path.symm (hcomp p q) = hcomp (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem hcomp_symm_cancel_toEq {a b : α} (p : Path a b) :
    (hcomp p (Path.symm p)).toEq = (Path.refl a).toEq :=
  Subsingleton.elim _ _

theorem symm_hcomp_cancel_toEq {a b : α} (p : Path a b) :
    (hcomp (Path.symm p) p).toEq = (Path.refl b).toEq :=
  Subsingleton.elim _ _

/-! ## 31-33. ap on hcomp -/

theorem ap_hcomp {β : Type u} (f : α → β) {a b c : α}
    (p : Path a b) (q : Path b c) :
    ap f (hcomp p q) = hcomp (ap f p) (ap f q) :=
  Path.congrArg_trans f p q

theorem ap_symm_symm {β : Type u} (f : α → β) {a b : α} (p : Path a b) :
    ap f (Path.symm (Path.symm p)) = ap f p := by rw [Path.symm_symm]

theorem ap_hcomp_symm {β : Type u} (f : α → β) {a b : α} (p : Path a b) :
    ap f (Path.symm p) = Path.symm (ap f p) :=
  Path.congrArg_symm f p

/-! ## 34-36. Whiskering -/

def whiskerLeft {a b c : α} (p : Path a b) {q r : Path b c}
    (_ : q = r) : Path a c := Path.trans p r

def whiskerRight {a b c : α} {p q : Path a b}
    (_ : p = q) (r : Path b c) : Path a c := Path.trans q r

theorem whiskerLeft_id {a b c : α} (p : Path a b) (q : Path b c) :
    whiskerLeft p (rfl : q = q) = Path.trans p q := rfl

theorem whiskerRight_id {a b c : α} (p : Path a b) (r : Path b c) :
    whiskerRight (rfl : p = p) r = Path.trans p r := rfl

/-! ## 37-39. NatTransPath -/

structure NatTransPath {β : Type u} (f g : α → β) where
  component : ∀ a, Path (f a) (g a)

def natTransComp {β : Type u} {f g h : α → β}
    (η : NatTransPath f g) (ε : NatTransPath g h) : NatTransPath f h :=
  { component := fun a => Path.trans (η.component a) (ε.component a) }

def natTransInv {β : Type u} {f g : α → β}
    (η : NatTransPath f g) : NatTransPath g f :=
  { component := fun a => Path.symm (η.component a) }

/-! ## 40-42. NatTrans algebra -/

theorem natTrans_comp_assoc {β : Type u} {f g h k : α → β}
    (η : NatTransPath f g) (ε : NatTransPath g h) (μ : NatTransPath h k)
    (a : α) :
    (natTransComp (natTransComp η ε) μ).component a =
    (natTransComp η (natTransComp ε μ)).component a :=
  Path.trans_assoc _ _ _

theorem natTrans_id_left {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    (natTransComp ⟨fun a => Path.refl (f a)⟩ η).component a =
    η.component a :=
  Path.trans_refl_left _

theorem natTrans_id_right {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    (natTransComp η ⟨fun a => Path.refl (g a)⟩).component a =
    η.component a :=
  Path.trans_refl_right _

/-! ## 43-45. NatTrans inverse -/

theorem natTrans_inv_comp_toEq {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    ((natTransComp (natTransInv η) η).component a).toEq =
    (Path.refl (g a)).toEq :=
  Subsingleton.elim _ _

theorem natTrans_comp_inv_toEq {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    ((natTransComp η (natTransInv η)).component a).toEq =
    (Path.refl (f a)).toEq :=
  Subsingleton.elim _ _

theorem natTrans_inv_inv {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    (natTransInv (natTransInv η)).component a = η.component a :=
  Path.symm_symm _

/-! ## 46-48. Naturality -/

theorem naturality_square {β : Type u} (f g : α → β)
    (η : NatTransPath f g) {a b : α} (p : Path a b) :
    (Path.trans (ap f p) (η.component b)).toEq =
    (Path.trans (η.component a) (ap g p)).toEq :=
  Subsingleton.elim _ _

def natTransWhisker {β γ : Type u} {f g : α → β} (h : β → γ)
    (η : NatTransPath f g) : NatTransPath (h ∘ f) (h ∘ g) :=
  { component := fun a => Path.congrArg h (η.component a) }

def natTransPrecomp {β γ : Type u} {f g : β → γ} (h : α → β)
    (η : NatTransPath f g) : NatTransPath (f ∘ h) (g ∘ h) :=
  { component := fun a => η.component (h a) }

/-! ## 49-51. Three/four step -/

def threeStep (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans p (Path.trans q r)

def fourStep {e : α} (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) : Path a e :=
  Path.trans p (Path.trans q (Path.trans r s))

theorem threeStep_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = threeStep p q r :=
  Path.trans_assoc p q r

/-! ## 52-54. Four-step associativity -/

theorem fourStep_assoc1 {e : α} (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s = fourStep p q r s := by
  simp [fourStep]

theorem fourStep_assoc2 {e : α} (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.trans p (Path.trans (Path.trans q r) s) = fourStep p q r s := by
  simp [fourStep]

theorem fourStep_congrArg_toEq {β : Type u} {e : α} (f : α → β) (p : Path a b)
    (q : Path b c) (r : Path c d) (s : Path d e) :
    (ap f (fourStep p q r s)).toEq =
    (fourStep (ap f p) (ap f q) (ap f r) (ap f s)).toEq :=
  Subsingleton.elim _ _

/-! ## 55-57. Path algebra -/

theorem symm_trans_self_toEq {a b : α} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq :=
  Subsingleton.elim _ _

theorem self_trans_symm_toEq {a b : α} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq :=
  Subsingleton.elim _ _

theorem symm_involution {a b : α} (p : Path a b) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-! ## 58-60. All paths equal -/

theorem all_paths_same_toEq {a b : α} (p q : Path a b) : p.toEq = q.toEq :=
  Subsingleton.elim _ _

theorem hcomp_toEq {a b c : α} (p : Path a b) (q : Path b c) :
    (hcomp p q).toEq = p.toEq.trans q.toEq :=
  Subsingleton.elim _ _

theorem threeStep_toEq (p : Path a b) (q : Path b c) (r : Path c d) :
    (threeStep p q r).toEq = (Path.trans (Path.trans p q) r).toEq :=
  Subsingleton.elim _ _

/-! ## 61-63. CongrArg NatTrans -/

def congrArgNT {β : Type u} (f : α → β) : NatTransPath f f :=
  { component := fun a => Path.refl (f a) }

theorem congrArgNT_is_id {β : Type u} (f : α → β) (a : α) :
    (congrArgNT f).component a = Path.refl (f a) := rfl

def constNT {β : Type u} (x y : β) (p : Path x y) :
    NatTransPath (fun _ : α => x) (fun _ => y) :=
  { component := fun _ => p }

theorem constNT_component {β : Type u} (x y : β) (p : Path x y) (a : α) :
    (constNT x y p).component a = p := rfl

/-! ## 64-66. Encode-decode -/

structure EncDec {a : α} (Code : α → Type u) where
  encode : ∀ b, Path a b → Code b
  decode : ∀ b, Code b → Path a b
  center : Code a

theorem encdec_coherent {a : α} {Code : α → Type u} (ed : EncDec Code)
    (b : α) (p : Path a b) :
    (ed.decode b (ed.encode b p)).toEq = p.toEq :=
  Subsingleton.elim _ _

theorem encdec_center_coherent {a : α} {Code : α → Type u} (ed : EncDec Code) :
    (ed.decode a ed.center).toEq = (Path.refl a).toEq :=
  Subsingleton.elim _ _

/-! ## 67-69. Fiber -/

structure Fiber {β : Type u} (f : α → β) (b : β) where
  point : α
  over : f point = b

theorem fiber_path_irrel {β : Type u} {f : α → β} {b : β}
    (x y : Fiber f b) (p q : Path x.point y.point) :
    p.toEq = q.toEq :=
  Subsingleton.elim _ _

def fiberPathBase {β : Type u} {f : α → β} {b : β}
    (x y : Fiber f b) (p : Path x.point y.point) :
    Path (f x.point) (f y.point) :=
  ap f p

theorem fiberPathBase_toEq {β : Type u} {f : α → β} {b : β}
    (x y : Fiber f b) (p : Path x.point y.point) :
    (fiberPathBase x y p).toEq = x.over.trans y.over.symm :=
  Subsingleton.elim _ _

/-! ## 70-72. Transport equiv witnesses -/

def transportFwd {P : α → Type u} {a b : α} (p : Path a b) : P a → P b :=
  transport p

def transportBwd {P : α → Type u} {a b : α} (p : Path a b) : P b → P a :=
  transport (Path.symm p)

theorem transport_fwd_bwd {P : α → Type u} {a b : α} (p : Path a b)
    (y : P b) :
    transportFwd p (transportBwd p y) = y := transport_symm_cancel' p y

theorem transport_bwd_fwd {P : α → Type u} {a b : α} (p : Path a b)
    (x : P a) :
    transportBwd p (transportFwd p x) = x := transport_symm_cancel p x

/-! ## 73-75. Path naturality -/

theorem path_naturality {β : Type u} (f g : α → β)
    (η : ∀ x, Path (f x) (g x)) {a b : α} (p : Path a b) :
    (Path.trans (η a) (ap g p)).toEq = (Path.trans (ap f p) (η b)).toEq :=
  Subsingleton.elim _ _

theorem path_naturality_id (f : α → α) (η : ∀ x, Path (f x) x)
    {a b : α} (p : Path a b) :
    (Path.trans (η a) p).toEq = (Path.trans (ap f p) (η b)).toEq :=
  Subsingleton.elim _ _

theorem path_naturality_from_id (f : α → α) (η : ∀ x, Path x (f x))
    {a b : α} (p : Path a b) :
    (Path.trans p (η b)).toEq = (Path.trans (η a) (ap f p)).toEq :=
  Subsingleton.elim _ _

/-! ## 76-78. Transport-ap interaction -/

theorem transport_ap_commute {β : Type u} {P : β → Type u} (f : α → β)
    {a b : α} (p : Path a b) (x : P (f a)) :
    transport (P := P) (ap f p) x = transport (P := P ∘ f) p x := by
  cases p with | mk _ proof => cases proof; rfl

theorem transport_congrArg_toEq {β : Type u} (f : α → β) {a b : α}
    (p : Path a b) :
    (ap f p).toEq = _root_.congrArg f p.toEq :=
  Subsingleton.elim _ _

theorem transport_twice {P : α → Type u} {a b : α}
    (p : Path a b) (q : Path b a) (x : P a) :
    transport q (transport p x) = transport (Path.trans p q) x := by
  cases p with | mk _ pf1 => cases q with | mk _ pf2 =>
    cases pf1; cases pf2; rfl

/-! ## 79-81. Symm composition -/

theorem symm_trans_eq {a b c : α} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem trans_symm_left_toEq {a b : α} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq :=
  Subsingleton.elim _ _

theorem trans_symm_right_toEq {a b : α} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq :=
  Subsingleton.elim _ _

/-! ## 82-84. NatTrans congrArg -/

def natTransCongrArg {β γ : Type u} {f g : α → β} (h : β → γ)
    (η : NatTransPath f g) : NatTransPath (h ∘ f) (h ∘ g) :=
  { component := fun a => Path.congrArg h (η.component a) }

theorem natTransCongrArg_comp {β γ δ : Type u} {f g : α → β}
    (h : β → γ) (k : γ → δ) (η : NatTransPath f g) (a : α) :
    ((natTransCongrArg k (natTransCongrArg h η)).component a).toEq =
    ((natTransCongrArg (k ∘ h) η).component a).toEq :=
  Subsingleton.elim _ _

theorem natTransCongrArg_trans {β γ : Type u} {f g h : α → β}
    (k : β → γ) (η : NatTransPath f g) (ε : NatTransPath g h) (a : α) :
    ((natTransCongrArg k (natTransComp η ε)).component a).toEq =
    ((natTransComp (natTransCongrArg k η) (natTransCongrArg k ε)).component a).toEq :=
  Subsingleton.elim _ _

/-! ## 85-87. SigmaPath -/

structure SigmaPath {P : α → Type u} {x y : (a : α) × P a} where
  basePath : Path x.1 y.1
  fiberEq : transport basePath x.2 = y.2

def sigmaPathRefl {P : α → Type u} {a : α} {x : P a} :
    SigmaPath (P := P) (x := ⟨a, x⟩) (y := ⟨a, x⟩) :=
  { basePath := Path.refl a, fiberEq := transport_refl x }

def liftPath {P : α → Type u} {a b : α} (p : Path a b) (u : P a) :
    SigmaPath (P := P) (x := ⟨a, u⟩) (y := ⟨b, transport p u⟩) :=
  { basePath := p, fiberEq := rfl }

/-! ## 88-90. Final: NatTrans ↔ pointwise path -/

theorem natTransPath_ext {β : Type u} {f g : α → β}
    (η ε : NatTransPath f g) (h : ∀ a, η.component a = ε.component a) :
    η = ε := by
  cases η; cases ε; congr; funext a; exact h a

theorem natTransComp_comm_toEq {β : Type u} {f g h k : α → β}
    (η : NatTransPath f g) (ε : NatTransPath g h)
    (μ : NatTransPath h k) (a : α) :
    ((natTransComp (natTransComp η ε) μ).component a).toEq =
    ((natTransComp η (natTransComp ε μ)).component a).toEq :=
  Subsingleton.elim _ _

theorem natTransInv_symm_law {β : Type u} {f g : α → β}
    (η : NatTransPath f g) (a : α) :
    (natTransInv η).component a = Path.symm (η.component a) := rfl

end ComputationalPaths.Path.TransportDeep
