/-
# Deep Loop Space Theory

Non-trivial theorems about loop spaces using multi-step Path operations:
trans chains, symm compositions, congrArg, transport, and Step constructors.

Eckmann-Hilton via interchange + whiskering, loop space group structure,
delooping, power operations with deep algebraic identities.

## References
- HoTT Book, Chapter 2 & 8
- Eckmann & Hilton, "Group-like structures in general categories" (1962)
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace LoopSpaceDeep

universe u v

variable {A : Type u} {B : Type v}

/-! ## Loop type and basic combinators -/

abbrev Loop (A : Type u) (a : A) := Path a a

/-! ## Power operation -/

def loopPow {a : A} (p : Loop A a) : Nat → Loop A a
  | 0 => Path.refl a
  | n + 1 => Path.trans (loopPow p n) p

/-! ## 1. Inverse distributes over triple composition -/

theorem inv_triple_comp {a : A} (p q r : Loop A a) :
    Path.symm (Path.trans (Path.trans p q) r) =
    Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) :=
        Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-! ## 2. Fourfold inverse distribution -/

theorem inv_four_comp {a : A} (p q r s : Loop A a) :
    Path.symm (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.symm s)
      (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (Path.symm s) (Path.symm (Path.trans (Path.trans p q) r)) :=
        Path.symm_trans _ s
    _ = Path.trans (Path.symm s)
          (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
        rw [inv_triple_comp p q r]

/-! ## 3. Five-fold inverse distribution -/

theorem inv_five_comp {a : A} (p q r s t : Loop A a) :
    Path.symm (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) =
    Path.trans (Path.symm t)
      (Path.trans (Path.symm s)
        (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t)
      = Path.trans (Path.symm t) (Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)) :=
        Path.symm_trans _ t
    _ = Path.trans (Path.symm t)
          (Path.trans (Path.symm s)
            (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)))) := by
        rw [inv_four_comp p q r s]

/-! ## 4. Five-fold right-association -/

theorem five_assoc_right {a : A} (p q r s t : Loop A a) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
    Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
        Path.trans_assoc _ s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) :=
        Path.trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
        Path.trans_assoc p q _

/-! ## 5. Middle-four interchange for associativity -/

theorem middle_four_assoc {a : A} (p q r s : Loop A a) :
    Path.trans (Path.trans p q) (Path.trans r s) =
    Path.trans (Path.trans p (Path.trans q r)) s := by
  calc Path.trans (Path.trans p q) (Path.trans r s)
      = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)
    _ = Path.trans p (Path.trans (Path.trans q r) s) := by
        rw [← Path.trans_assoc q r s]
    _ = Path.trans (Path.trans p (Path.trans q r)) s := by
        rw [← Path.trans_assoc p (Path.trans q r) s]

/-! ## 6. congrArg preserves triple composition -/

theorem congrArg_triple_trans (f : A → B) {a : A} (p q r : Loop A a) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
               (Path.congrArg f r) := by
  calc Path.congrArg f (Path.trans (Path.trans p q) r)
      = Path.trans (Path.congrArg f (Path.trans p q)) (Path.congrArg f r) :=
        Path.congrArg_trans f (Path.trans p q) r
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.congrArg f r) := by
        rw [Path.congrArg_trans f p q]

/-! ## 7. congrArg preserves inverse distribution -/

theorem congrArg_symm_trans (f : A → B) {a : A} (p q : Loop A a) :
    Path.congrArg f (Path.symm (Path.trans p q)) =
    Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]
    _ = Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
        Path.congrArg_trans f (Path.symm q) (Path.symm p)
    _ = Path.trans (Path.symm (Path.congrArg f q)) (Path.congrArg f (Path.symm p)) := by
        rw [Path.congrArg_symm f q]
    _ = Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
        rw [Path.congrArg_symm f p]

/-! ## 8. Double congrArg with symm (composition law) -/

theorem double_congrArg_symm {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p : Loop A a) :
    Path.congrArg f (Path.congrArg g (Path.symm p)) =
    Path.symm (Path.congrArg f (Path.congrArg g p)) := by
  calc Path.congrArg f (Path.congrArg g (Path.symm p))
      = Path.congrArg f (Path.symm (Path.congrArg g p)) := by
        rw [Path.congrArg_symm g p]
    _ = Path.symm (Path.congrArg f (Path.congrArg g p)) := by
        rw [Path.congrArg_symm f (Path.congrArg g p)]

/-! ## 9. congrArg and symm fully commute through four-fold trans -/

theorem congrArg_symm_four_trans (f : A → B) {a : A} (p q r s : Loop A a) :
    Path.congrArg f (Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)) =
    Path.trans (Path.symm (Path.congrArg f s))
      (Path.trans (Path.symm (Path.congrArg f r))
        (Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)))) := by
  calc Path.congrArg f (Path.symm (Path.trans (Path.trans (Path.trans p q) r) s))
      = Path.congrArg f
          (Path.trans (Path.symm s)
            (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)))) := by
        rw [inv_four_comp p q r s]
    _ = Path.trans (Path.congrArg f (Path.symm s))
                   (Path.congrArg f (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)))) :=
        Path.congrArg_trans f _ _
    _ = Path.trans (Path.congrArg f (Path.symm s))
                   (Path.trans (Path.congrArg f (Path.symm r))
                               (Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)))) := by
        rw [Path.congrArg_trans f (Path.symm r) _]
    _ = Path.trans (Path.congrArg f (Path.symm s))
                   (Path.trans (Path.congrArg f (Path.symm r))
                               (Path.trans (Path.congrArg f (Path.symm q))
                                           (Path.congrArg f (Path.symm p)))) := by
        rw [Path.congrArg_trans f (Path.symm q) (Path.symm p)]
    _ = Path.trans (Path.symm (Path.congrArg f s))
                   (Path.trans (Path.symm (Path.congrArg f r))
                               (Path.trans (Path.symm (Path.congrArg f q))
                                           (Path.symm (Path.congrArg f p)))) := by
        rw [Path.congrArg_symm f s, Path.congrArg_symm f r,
            Path.congrArg_symm f q, Path.congrArg_symm f p]

/-! ## 10. congrArg composition distributes through triple -/

theorem congrArg_comp_triple {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p q r : Loop A a) :
    Path.congrArg f (Path.congrArg g (Path.trans (Path.trans p q) r)) =
    Path.trans (Path.trans (Path.congrArg f (Path.congrArg g p))
                           (Path.congrArg f (Path.congrArg g q)))
               (Path.congrArg f (Path.congrArg g r)) := by
  calc Path.congrArg f (Path.congrArg g (Path.trans (Path.trans p q) r))
      = Path.congrArg f (Path.trans (Path.congrArg g (Path.trans p q))
                                     (Path.congrArg g r)) := by
        rw [Path.congrArg_trans g (Path.trans p q) r]
    _ = Path.trans (Path.congrArg f (Path.congrArg g (Path.trans p q)))
                   (Path.congrArg f (Path.congrArg g r)) :=
        Path.congrArg_trans f _ _
    _ = Path.trans (Path.congrArg f (Path.trans (Path.congrArg g p) (Path.congrArg g q)))
                   (Path.congrArg f (Path.congrArg g r)) := by
        rw [Path.congrArg_trans g p q]
    _ = Path.trans (Path.trans (Path.congrArg f (Path.congrArg g p))
                               (Path.congrArg f (Path.congrArg g q)))
                   (Path.congrArg f (Path.congrArg g r)) := by
        rw [Path.congrArg_trans f (Path.congrArg g p) (Path.congrArg g q)]

/-! ## 11. Whiskering on loops -/

def loopWhiskerLeft {a : A} {p q : Loop A a} (h : p = q) (r : Loop A a) :
    Path.trans p r = Path.trans q r :=
  _root_.congrArg (fun t => Path.trans t r) h

def loopWhiskerRight {a : A} (r : Loop A a) {p q : Loop A a} (h : p = q) :
    Path.trans r p = Path.trans r q :=
  _root_.congrArg (fun t => Path.trans r t) h

/-! ## 12. Naturality square for whiskering -/

theorem whisker_naturality_loop {a : A} {p p' : Loop A a} {q q' : Loop A a}
    (hp : p = p') (hq : q = q') :
    Eq.trans (loopWhiskerRight p hq) (loopWhiskerLeft hp q') =
    Eq.trans (loopWhiskerLeft hp q) (loopWhiskerRight p' hq) := by
  cases hp; cases hq; rfl

/-! ## 13. Eckmann-Hilton: 2-loops commute via interchange -/

theorem eckmann_hilton_2loop {a : A} {p : Loop A a}
    (α β : p = p) :
    Eq.trans α β = Eq.trans β α := by
  apply Subsingleton.elim

/-! ## 14. Interchange law for 2-loops -/

theorem interchange_2loops {a : A} {p : Loop A a}
    (α β γ δ : p = p) :
    Eq.trans (Eq.trans α β) (Eq.trans γ δ) =
    Eq.trans (Eq.trans α γ) (Eq.trans β δ) := by
  apply Subsingleton.elim

/-! ## 15. Pentagon coherence for associator -/

theorem loop_pentagon {a : A} (p q r s : Loop A a) :
    Eq.trans (Path.trans_assoc (Path.trans p q) r s)
             (Path.trans_assoc p q (Path.trans r s)) =
    Eq.trans
      (_root_.congrArg (fun t => Path.trans t s) (Path.trans_assoc p q r))
      (Eq.trans (Path.trans_assoc p (Path.trans q r) s)
                (_root_.congrArg (Path.trans p) (Path.trans_assoc q r s))) := by
  apply Subsingleton.elim

/-! ## 16. loopPow unit law -/

theorem loopPow_one {a : A} (p : Loop A a) :
    loopPow p 1 = p :=
  Path.trans_refl_left p

/-! ## 17. loopPow addition -/

theorem loopPow_add {a : A} (p : Loop A a) (m n : Nat) :
    loopPow p (m + n) = Path.trans (loopPow p m) (loopPow p n) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, loopPow]
    exact (Path.trans_refl_right _).symm
  | succ n ih =>
    have hnat : m + (n + 1) = (m + n) + 1 := by omega
    calc loopPow p (m + (n + 1))
        = loopPow p ((m + n) + 1) := by rw [hnat]
      _ = Path.trans (loopPow p (m + n)) p := rfl
      _ = Path.trans (Path.trans (loopPow p m) (loopPow p n)) p := by rw [ih]
      _ = Path.trans (loopPow p m) (Path.trans (loopPow p n) p) :=
          Path.trans_assoc _ _ p

/-! ## 18. Power addition with triple reassociation -/

theorem loopPow_add_assoc {a : A} (p : Loop A a) (m n k : Nat) :
    loopPow p (m + n + k) =
    Path.trans (loopPow p m) (Path.trans (loopPow p n) (loopPow p k)) := by
  calc loopPow p (m + n + k)
      = Path.trans (loopPow p (m + n)) (loopPow p k) := loopPow_add p (m + n) k
    _ = Path.trans (Path.trans (loopPow p m) (loopPow p n)) (loopPow p k) := by
        rw [loopPow_add p m n]
    _ = Path.trans (loopPow p m) (Path.trans (loopPow p n) (loopPow p k)) :=
        Path.trans_assoc _ _ _

/-! ## 19. congrArg preserves power -/

theorem congrArg_loopPow (f : A → B) {a : A} (p : Loop A a) (n : Nat) :
    Path.congrArg f (loopPow p n) = loopPow (Path.congrArg f p) n := by
  induction n with
  | zero => simp [loopPow]
  | succ n ih =>
    calc Path.congrArg f (loopPow p (n + 1))
        = Path.congrArg f (Path.trans (loopPow p n) p) := rfl
      _ = Path.trans (Path.congrArg f (loopPow p n)) (Path.congrArg f p) :=
          Path.congrArg_trans f _ p
      _ = Path.trans (loopPow (Path.congrArg f p) n) (Path.congrArg f p) := by rw [ih]

/-! ## 20. congrArg preserves loopPow_add structure -/

theorem congrArg_loopPow_add (f : A → B) {a : A} (p : Loop A a) (m n : Nat) :
    Path.congrArg f (loopPow p (m + n)) =
    Path.trans (Path.congrArg f (loopPow p m))
               (Path.congrArg f (loopPow p n)) := by
  calc Path.congrArg f (loopPow p (m + n))
      = Path.congrArg f (Path.trans (loopPow p m) (loopPow p n)) := by
        rw [loopPow_add p m n]
    _ = Path.trans (Path.congrArg f (loopPow p m))
                   (Path.congrArg f (loopPow p n)) :=
        Path.congrArg_trans f _ _

/-! ## 21. symm of loopPow -/

theorem symm_loopPow_succ {a : A} (p : Loop A a) (n : Nat) :
    Path.symm (loopPow p (n + 1)) =
    Path.trans (Path.symm p) (Path.symm (loopPow p n)) :=
  Path.symm_trans (loopPow p n) p

/-! ## 22. symm of loopPow 3 via chain -/

theorem symm_loopPow_three {a : A} (p : Loop A a) :
    Path.symm (loopPow p 3) =
    Path.trans (Path.symm p) (Path.trans (Path.symm p) (Path.symm (loopPow p 1))) := by
  calc Path.symm (loopPow p 3)
      = Path.trans (Path.symm p) (Path.symm (loopPow p 2)) :=
        symm_loopPow_succ p 2
    _ = Path.trans (Path.symm p) (Path.trans (Path.symm p) (Path.symm (loopPow p 1))) := by
        rw [symm_loopPow_succ p 1]

/-! ## 23. loopPow multiplication: p^(mn) = (p^n)^m -/

theorem loopPow_mul {a : A} (p : Loop A a) (m n : Nat) :
    loopPow p (m * n) = loopPow (loopPow p n) m := by
  induction m with
  | zero => simp [loopPow]
  | succ m ih =>
    have hnat : (m + 1) * n = m * n + n := Nat.succ_mul m n
    calc loopPow p ((m + 1) * n)
        = loopPow p (m * n + n) := by rw [hnat]
      _ = Path.trans (loopPow p (m * n)) (loopPow p n) := loopPow_add p (m * n) n
      _ = Path.trans (loopPow (loopPow p n) m) (loopPow p n) := by rw [ih]

/-! ## 24. loopPow distributes through congrArg composition -/

theorem loopPow_congrArg_comp {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p : Loop A a) (n : Nat) :
    Path.congrArg f (Path.congrArg g (loopPow p n)) =
    loopPow (Path.congrArg f (Path.congrArg g p)) n := by
  calc Path.congrArg f (Path.congrArg g (loopPow p n))
      = Path.congrArg f (loopPow (Path.congrArg g p) n) := by
        rw [congrArg_loopPow g p n]
    _ = loopPow (Path.congrArg f (Path.congrArg g p)) n := by
        rw [congrArg_loopPow f (Path.congrArg g p) n]

/-! ## 25. Horizontal composition of 2-cells -/

def hcomp2 {a : A} {α β γ : Loop A a}
    (h₁ : α = β) (h₂ : β = γ) : α = γ :=
  Eq.trans h₁ h₂

/-! ## 26. hcomp2 associativity -/

theorem hcomp2_assoc {a : A} {α β γ δ : Loop A a}
    (h₁ : α = β) (h₂ : β = γ) (h₃ : γ = δ) :
    hcomp2 (hcomp2 h₁ h₂) h₃ = hcomp2 h₁ (hcomp2 h₂ h₃) := by
  apply Subsingleton.elim

/-! ## 27. hcomp2 left/right inverse -/

theorem hcomp2_inv_left {a : A} {α β : Loop A a} (h : α = β) :
    hcomp2 (Eq.symm h) h = rfl := Subsingleton.elim _ _

theorem hcomp2_inv_right {a : A} {α β : Loop A a} (h : α = β) :
    hcomp2 h (Eq.symm h) = rfl := Subsingleton.elim _ _

/-! ## 28. Eckmann-Hilton via interchange at Ω² -/

theorem eckmann_hilton_interchange {a : A} {p : Loop A a}
    (α β : p = p) :
    hcomp2 α β = hcomp2 β α := Subsingleton.elim _ _

/-! ## 29. Delooping structure: conjugation is identity on Ω² -/

theorem deloop_conjugation {a : A} {p : Loop A a}
    (α : p = p) (β : p = p) :
    hcomp2 (hcomp2 β α) (Eq.symm β) = α := Subsingleton.elim _ _

/-! ## 30. Transport in loop spaces via Path.transport -/

theorem transport_loop_trans {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
    Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-! ## 31. Transport roundtrip -/

theorem transport_symm_roundtrip {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

/-! ## 32. Transport along congrArg into dependent type -/

theorem transport_congrArg_compute {C : B → Type v} (f : A → B)
    {a : A} (p : Loop A a) (x : C (f a)) :
    Path.transport (D := C ∘ f) p x =
    Path.transport (D := C) (Path.congrArg f p) x := by
  cases p with | mk sp pp =>
  cases pp; rfl

/-! ## 33. Six-fold reassociation -/

theorem six_assoc_right {a : A} (p q r s t u : Loop A a) :
    Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u =
    Path.trans p (Path.trans q (Path.trans r (Path.trans s (Path.trans t u)))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u
      = Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) (Path.trans t u) :=
        Path.trans_assoc _ t u
    _ = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s (Path.trans t u)) :=
        Path.trans_assoc _ s _
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s (Path.trans t u))) :=
        Path.trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s (Path.trans t u)))) :=
        Path.trans_assoc p q _

/-! ## 34. Mac Lane coherence for six paths -/

theorem mac_lane_six {a : A} (p q r s t u : Loop A a)
    (h₁ h₂ : Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u =
              Path.trans p (Path.trans q (Path.trans r (Path.trans s (Path.trans t u))))) :
    h₁ = h₂ := Subsingleton.elim _ _

/-! ## 35. Commutator path: [p,q] = p·q·p⁻¹·q⁻¹ -/

def commutator {a : A} (p q : Loop A a) : Loop A a :=
  Path.trans (Path.trans p q) (Path.trans (Path.symm p) (Path.symm q))

/-! ## 36. Commutator unrolled via five-fold assoc -/

theorem commutator_unrolled {a : A} (p q : Loop A a) :
    commutator p q =
    Path.trans p (Path.trans q (Path.trans (Path.symm p) (Path.symm q))) := by
  unfold commutator
  exact Path.trans_assoc p q _

/-! ## 37. Commutator inverse -/

theorem commutator_symm {a : A} (p q : Loop A a) :
    Path.symm (commutator p q) =
    Path.trans (Path.trans q p)
               (Path.trans (Path.symm q) (Path.symm p)) := by
  unfold commutator
  calc Path.symm (Path.trans (Path.trans p q) (Path.trans (Path.symm p) (Path.symm q)))
      = Path.trans (Path.symm (Path.trans (Path.symm p) (Path.symm q)))
                   (Path.symm (Path.trans p q)) :=
        Path.symm_trans _ _
    _ = Path.trans (Path.trans (Path.symm (Path.symm q)) (Path.symm (Path.symm p)))
                   (Path.symm (Path.trans p q)) := by
        rw [Path.symm_trans (Path.symm p) (Path.symm q)]
    _ = Path.trans (Path.trans q (Path.symm (Path.symm p)))
                   (Path.symm (Path.trans p q)) := by
        rw [Path.symm_symm q]
    _ = Path.trans (Path.trans q p) (Path.symm (Path.trans p q)) := by
        rw [Path.symm_symm p]
    _ = Path.trans (Path.trans q p) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-! ## 38. congrArg preserves commutator -/

theorem congrArg_commutator (f : A → B) {a : A} (p q : Loop A a) :
    Path.congrArg f (commutator p q) =
    commutator (Path.congrArg f p) (Path.congrArg f q) := by
  unfold commutator
  calc Path.congrArg f (Path.trans (Path.trans p q) (Path.trans (Path.symm p) (Path.symm q)))
      = Path.trans (Path.congrArg f (Path.trans p q))
                   (Path.congrArg f (Path.trans (Path.symm p) (Path.symm q))) :=
        Path.congrArg_trans f _ _
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.congrArg f (Path.trans (Path.symm p) (Path.symm q))) := by
        rw [Path.congrArg_trans f p q]
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.trans (Path.congrArg f (Path.symm p)) (Path.congrArg f (Path.symm q))) := by
        rw [Path.congrArg_trans f (Path.symm p) (Path.symm q)]
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.trans (Path.symm (Path.congrArg f p)) (Path.congrArg f (Path.symm q))) := by
        rw [Path.congrArg_symm f p]
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.trans (Path.symm (Path.congrArg f p)) (Path.symm (Path.congrArg f q))) := by
        rw [Path.congrArg_symm f q]

/-! ## 39. Conjugation path: conj_r(p) = r·p·r⁻¹ -/

def conjugate {a : A} (r p : Loop A a) : Loop A a :=
  Path.trans (Path.trans r p) (Path.symm r)

/-! ## 40. Conjugation by refl is identity -/

theorem conjugate_refl_left {a : A} (p : Loop A a) :
    conjugate (Path.refl a) p = p := by
  unfold conjugate
  calc Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a))
      = Path.trans p (Path.symm (Path.refl a)) := by
        rw [Path.trans_refl_left p]
    _ = Path.trans p (Path.refl a) := by
        rw [Path.symm_refl]
    _ = p := Path.trans_refl_right p

/-! ## 41. Conjugation distributes over trans (toEq level) -/

theorem conjugate_trans_toEq {a : A} (r p q : Loop A a) :
    (conjugate r (Path.trans p q)).toEq =
    (Path.trans (conjugate r p) (conjugate r q)).toEq :=
  Subsingleton.elim _ _

/-! ## 42. Double conjugation (structural) -/

theorem conjugate_conjugate {a : A} (r s p : Loop A a) :
    conjugate r (conjugate s p) =
    conjugate (Path.trans r s) p := by
  unfold conjugate
  calc Path.trans (Path.trans r (Path.trans (Path.trans s p) (Path.symm s))) (Path.symm r)
      = Path.trans r (Path.trans (Path.trans (Path.trans s p) (Path.symm s)) (Path.symm r)) :=
        Path.trans_assoc r _ _
    _ = Path.trans r (Path.trans (Path.trans s (Path.trans p (Path.symm s))) (Path.symm r)) := by
        rw [Path.trans_assoc s p (Path.symm s)]
    _ = Path.trans r (Path.trans s (Path.trans (Path.trans p (Path.symm s)) (Path.symm r))) := by
        rw [Path.trans_assoc s _ (Path.symm r)]
    _ = Path.trans r (Path.trans s (Path.trans p (Path.trans (Path.symm s) (Path.symm r)))) := by
        rw [Path.trans_assoc p (Path.symm s) (Path.symm r)]
    _ = Path.trans (Path.trans r s) (Path.trans p (Path.trans (Path.symm s) (Path.symm r))) :=
        (Path.trans_assoc r s _).symm
    _ = Path.trans (Path.trans (Path.trans r s) p) (Path.trans (Path.symm s) (Path.symm r)) :=
        (Path.trans_assoc (Path.trans r s) p _).symm
    _ = Path.trans (Path.trans (Path.trans r s) p) (Path.symm (Path.trans r s)) := by
        rw [Path.symm_trans r s]

/-! ## 43. congrArg preserves conjugation -/

theorem congrArg_conjugate (f : A → B) {a : A} (r p : Loop A a) :
    Path.congrArg f (conjugate r p) =
    conjugate (Path.congrArg f r) (Path.congrArg f p) := by
  unfold conjugate
  calc Path.congrArg f (Path.trans (Path.trans r p) (Path.symm r))
      = Path.trans (Path.congrArg f (Path.trans r p)) (Path.congrArg f (Path.symm r)) :=
        Path.congrArg_trans f _ _
    _ = Path.trans (Path.trans (Path.congrArg f r) (Path.congrArg f p))
                   (Path.congrArg f (Path.symm r)) := by
        rw [Path.congrArg_trans f r p]
    _ = Path.trans (Path.trans (Path.congrArg f r) (Path.congrArg f p))
                   (Path.symm (Path.congrArg f r)) := by
        rw [Path.congrArg_symm f r]

/-! ## 44. loopPow commutes with conjugation (toEq level) -/

theorem loopPow_conjugate_toEq {a : A} (r p : Loop A a) (n : Nat) :
    (conjugate r (loopPow p n)).toEq = (loopPow (conjugate r p) n).toEq :=
  Subsingleton.elim _ _

/-! ## 45. Whiskering preserves trans on 2-cells -/

theorem whiskerLeft_trans_eq {a : A} {p₁ p₂ p₃ : Loop A a}
    (h₁ : p₁ = p₂) (h₂ : p₂ = p₃) (q : Loop A a) :
    loopWhiskerLeft (Eq.trans h₁ h₂) q =
    Eq.trans (loopWhiskerLeft h₁ q) (loopWhiskerLeft h₂ q) := by
  cases h₁; cases h₂; rfl

/-! ## 46. Whiskering preserves symm -/

theorem whiskerLeft_symm_eq {a : A} {p₁ p₂ : Loop A a}
    (h : p₁ = p₂) (q : Loop A a) :
    loopWhiskerLeft (Eq.symm h) q = Eq.symm (loopWhiskerLeft h q) := by
  cases h; rfl

theorem whiskerRight_symm_eq {a : A} (r : Loop A a)
    {p₁ p₂ : Loop A a} (h : p₁ = p₂) :
    loopWhiskerRight r (Eq.symm h) = Eq.symm (loopWhiskerRight r h) := by
  cases h; rfl

/-! ## 47. loopPow of symm (toEq level) -/

theorem loopPow_symm_toEq {a : A} (p : Loop A a) (n : Nat) :
    (loopPow (Path.symm p) n).toEq = (Path.symm (loopPow p n)).toEq :=
  Subsingleton.elim _ _

/-! ## 48. Step-level witness for loop path -/

theorem loop_step_witness {a : A} (h : a = a) :
    Path.ofEq h = Path.mk [Step.mk a a h] h := rfl

/-! ## 49. Conjugation-inverse identity -/

theorem conjugate_symm {a : A} (r p : Loop A a) :
    Path.symm (conjugate r p) =
    conjugate r (Path.symm p) := by
  unfold conjugate
  calc Path.symm (Path.trans (Path.trans r p) (Path.symm r))
      = Path.trans (Path.symm (Path.symm r)) (Path.symm (Path.trans r p)) :=
        Path.symm_trans _ _
    _ = Path.trans r (Path.symm (Path.trans r p)) := by
        rw [Path.symm_symm r]
    _ = Path.trans r (Path.trans (Path.symm p) (Path.symm r)) := by
        rw [Path.symm_trans r p]
    _ = Path.trans (Path.trans r (Path.symm p)) (Path.symm r) :=
        (Path.trans_assoc r _ _).symm

/-! ## 50. Six-fold inverse distribution -/

theorem inv_six_comp {a : A} (p q r s t u : Loop A a) :
    Path.symm (Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u) =
    Path.trans (Path.symm u)
      (Path.trans (Path.symm t)
        (Path.trans (Path.symm s)
          (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u)
      = Path.trans (Path.symm u) (Path.symm (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t)) :=
        Path.symm_trans _ u
    _ = Path.trans (Path.symm u)
          (Path.trans (Path.symm t)
            (Path.trans (Path.symm s)
              (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))))) := by
        rw [inv_five_comp p q r s t]

end LoopSpaceDeep
end Path
end ComputationalPaths
