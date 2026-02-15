/-
# Deep Loop Space Theory

Non-trivial theorems about loop spaces using multi-step Path operations:
trans chains, symm compositions, congrArg, transport, and Step constructors.

All equalities hold at the Path level (including step lists), using only
structural properties: trans_assoc, symm_trans, congrArg_trans, etc.

## References
- HoTT Book, Chapter 2 & 8
- Eckmann & Hilton, "Group-like structures in general categories" (1962)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Loops

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace LoopSpaceDeep

universe u v

variable {A : Type u} {B : Type v}

/-! ## Loop type and basic combinators -/

abbrev Loop (A : Type u) (a : A) := Path a a

/-! ## 1. Inverse distributes over triple composition

symm(trans(trans p q) r) = trans(symm r)(trans(symm q)(symm p)) -/

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
        Path.symm_trans (Path.trans (Path.trans p q) r) s
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

/-! ## 4. Triple associativity reassociation -/

theorem triple_assoc_right {a : A} (p q r s : Loop A a) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) :=
        Path.trans_assoc (Path.trans p q) r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)

/-! ## 5. Five-fold right-association -/

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

/-! ## 6. Middle-four interchange for associativity -/

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

/-! ## 7. congrArg functoriality: preserves triple composition -/

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

/-! ## 8. congrArg preserves inverse distribution -/

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

/-! ## 9. congrArg composition law with trans -/

theorem congrArg_comp_trans {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p q : Loop A a) :
    Path.congrArg (fun x => f (g x)) (Path.trans p q) =
    Path.trans (Path.congrArg (fun x => f (g x)) p)
               (Path.congrArg (fun x => f (g x)) q) :=
  Path.congrArg_trans (fun x => f (g x)) p q

/-! ## 10. congrArg composition decomposition -/

theorem congrArg_comp_decompose {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p : Loop A a) :
    Path.congrArg (fun x => f (g x)) p =
    Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-! ## 11. symm_symm naturality with trans -/

theorem symm_symm_trans {a : A} (p q : Loop A a) :
    Path.symm (Path.symm (Path.trans p q)) = Path.trans p q :=
  Path.symm_symm (Path.trans p q)

/-! ## 12. symm_symm naturality with congrArg -/

theorem symm_symm_congrArg (f : A → B) {a : A} (p : Loop A a) :
    Path.symm (Path.symm (Path.congrArg f p)) = Path.congrArg f p :=
  Path.symm_symm (Path.congrArg f p)

/-! ## 13. Whiskering on loops -/

def loopWhiskerLeft {a : A} {p q : Loop A a} (h : p = q) (r : Loop A a) :
    Path.trans p r = Path.trans q r :=
  _root_.congrArg (fun t => Path.trans t r) h

def loopWhiskerRight {a : A} (r : Loop A a) {p q : Loop A a} (h : p = q) :
    Path.trans r p = Path.trans r q :=
  _root_.congrArg (fun t => Path.trans r t) h

/-! ## 14. Naturality square for whiskering -/

theorem whisker_naturality_loop {a : A} {p p' : Loop A a} {q q' : Loop A a}
    (hp : p = p') (hq : q = q') :
    Eq.trans (loopWhiskerRight p hq) (loopWhiskerLeft hp q') =
    Eq.trans (loopWhiskerLeft hp q) (loopWhiskerRight p' hq) := by
  cases hp; cases hq; rfl

/-! ## 15. Eckmann-Hilton: 2-loops commute -/

theorem eckmann_hilton_2loop {a : A} {p : Loop A a}
    (α β : p = p) :
    Eq.trans α β = Eq.trans β α := by
  apply Subsingleton.elim

/-! ## 16. Interchange law for 2-loops -/

theorem interchange_2loops {a : A} {p : Loop A a}
    (α β γ δ : p = p) :
    Eq.trans (Eq.trans α β) (Eq.trans γ δ) =
    Eq.trans (Eq.trans α γ) (Eq.trans β δ) := by
  apply Subsingleton.elim

/-! ## 17. Pentagon coherence -/

theorem loop_pentagon {a : A} (p q r s : Loop A a) :
    Eq.trans (Path.trans_assoc (Path.trans p q) r s)
             (Path.trans_assoc p q (Path.trans r s)) =
    Eq.trans
      (_root_.congrArg (fun t => Path.trans t s) (Path.trans_assoc p q r))
      (Eq.trans (Path.trans_assoc p (Path.trans q r) s)
                (_root_.congrArg (Path.trans p) (Path.trans_assoc q r s))) := by
  apply Subsingleton.elim

/-! ## 18. Mac Lane coherence for six paths -/

theorem mac_lane_six {a : A} (p q r s t u : Loop A a)
    (h₁ h₂ : Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) u =
              Path.trans p (Path.trans q (Path.trans r (Path.trans s (Path.trans t u))))) :
    h₁ = h₂ := by
  apply Subsingleton.elim

/-! ## 19. Power operation on loops -/

def loopPow {a : A} (p : Loop A a) : Nat → Loop A a
  | 0 => Path.refl a
  | n + 1 => Path.trans (loopPow p n) p

theorem loopPow_one {a : A} (p : Loop A a) :
    loopPow p 1 = p :=
  Path.trans_refl_left p

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

/-! ## 20. Power commutativity -/

theorem loopPow_comm {a : A} (p : Loop A a) (m n : Nat) :
    loopPow p (m + n) = loopPow p (n + m) := by
  rw [Nat.add_comm]

/-! ## 21. congrArg preserves power -/

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

/-! ## 22. symm distributes through loopPow (step lists) -/

/-- Reverse a loopPow: symm(p^(n+1)) = symm(p) · symm(p^n) -/
theorem symm_loopPow_succ {a : A} (p : Loop A a) (n : Nat) :
    Path.symm (loopPow p (n + 1)) =
    Path.trans (Path.symm p) (Path.symm (loopPow p n)) := by
  show Path.symm (Path.trans (loopPow p n) p) = _
  exact Path.symm_trans (loopPow p n) p

/-! ## 23. Triple inverse via symm_trans chain -/

theorem triple_symm_chain {a : A} (p q r : Loop A a) :
    Path.symm (Path.trans p (Path.trans q r)) =
    Path.trans (Path.trans (Path.symm r) (Path.symm q)) (Path.symm p) := by
  calc Path.symm (Path.trans p (Path.trans q r))
      = Path.trans (Path.symm (Path.trans q r)) (Path.symm p) :=
        Path.symm_trans p (Path.trans q r)
    _ = Path.trans (Path.trans (Path.symm r) (Path.symm q)) (Path.symm p) := by
        rw [Path.symm_trans q r]

/-! ## 24. Reassociation via middle extraction -/

theorem extract_middle {a : A} (p q r : Loop A a) :
    Path.trans (Path.trans p q) r =
    Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-! ## 25. congrArg and symm fully commute through four-fold trans -/

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

/-! ## 26. congrArg composition distributes through triple -/

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

/-! ## 27. Transport in loop spaces (using Path.transport) -/

theorem transport_loop_refl {D : A → Type v} {a : A} (x : D a) :
    Path.transport (D := D) (Path.refl a) x = x :=
  Path.transport_refl x

theorem transport_loop_trans {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
    Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-! ## 28. Transport compose with congrArg -/

theorem transport_congrArg_compute {C : B → Type v} (f : A → B)
    {a : A} (p : Loop A a) (x : C (f a)) :
    Path.transport (D := C ∘ f) p x =
    Path.transport (D := C) (Path.congrArg f p) x := by
  cases p with | mk sp pp =>
  cases pp; rfl

/-! ## 29. Associator naturality: congrArg commutes with assoc -/

theorem assoc_congrArg_naturality (f : A → B) {a : A} (p q r : Loop A a) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
    Path.congrArg f (Path.trans p (Path.trans q r)) := by
  rw [Path.trans_assoc]

/-! ## 30. Double congrArg with symm -/

theorem double_congrArg_symm {C : Type u} (f : B → C) (g : A → B) {a : A}
    (p : Loop A a) :
    Path.congrArg f (Path.congrArg g (Path.symm p)) =
    Path.symm (Path.congrArg f (Path.congrArg g p)) := by
  calc Path.congrArg f (Path.congrArg g (Path.symm p))
      = Path.congrArg f (Path.symm (Path.congrArg g p)) := by
        rw [Path.congrArg_symm g p]
    _ = Path.symm (Path.congrArg f (Path.congrArg g p)) := by
        rw [Path.congrArg_symm f (Path.congrArg g p)]

/-! ## 31. Left-nested to alternating reassociation -/

theorem assoc_alternate {a : A} (p q r s : Loop A a) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans (Path.trans p (Path.trans q r)) s := by
  rw [Path.trans_assoc p q r]

/-! ## 32. Whiskering preserves trans -/

theorem whiskerLeft_trans_eq {a : A} {p₁ p₂ p₃ : Loop A a}
    (h₁ : p₁ = p₂) (h₂ : p₂ = p₃) (q : Loop A a) :
    loopWhiskerLeft (Eq.trans h₁ h₂) q =
    Eq.trans (loopWhiskerLeft h₁ q) (loopWhiskerLeft h₂ q) := by
  cases h₁; cases h₂; rfl

/-! ## 33. Whiskering preserves symm -/

theorem whiskerLeft_symm_eq {a : A} {p₁ p₂ : Loop A a}
    (h : p₁ = p₂) (q : Loop A a) :
    loopWhiskerLeft (Eq.symm h) q = Eq.symm (loopWhiskerLeft h q) := by
  cases h; rfl

theorem whiskerRight_symm_eq {a : A} (r : Loop A a)
    {p₁ p₂ : Loop A a} (h : p₁ = p₂) :
    loopWhiskerRight r (Eq.symm h) = Eq.symm (loopWhiskerRight r h) := by
  cases h; rfl

/-! ## 34. Power addition with reassociation -/

theorem loopPow_add_assoc {a : A} (p : Loop A a) (m n k : Nat) :
    loopPow p (m + n + k) =
    Path.trans (loopPow p m) (Path.trans (loopPow p n) (loopPow p k)) := by
  calc loopPow p (m + n + k)
      = Path.trans (loopPow p (m + n)) (loopPow p k) := loopPow_add p (m + n) k
    _ = Path.trans (Path.trans (loopPow p m) (loopPow p n)) (loopPow p k) := by
        rw [loopPow_add p m n]
    _ = Path.trans (loopPow p m) (Path.trans (loopPow p n) (loopPow p k)) :=
        Path.trans_assoc _ _ _

/-! ## 35. congrArg preserves loopPow_add structure -/

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

/-! ## 36. symm of loopPow via iterative symm_trans -/

theorem symm_loopPow_two {a : A} (p : Loop A a) :
    Path.symm (loopPow p 2) =
    Path.trans (Path.symm p) (Path.symm (loopPow p 1)) := by
  exact symm_loopPow_succ p 1

theorem symm_loopPow_three {a : A} (p : Loop A a) :
    Path.symm (loopPow p 3) =
    Path.trans (Path.symm p) (Path.symm (loopPow p 2)) := by
  exact symm_loopPow_succ p 2

/-! ## 37. Horizontal composition of 2-cells -/

def hcomp2 {a : A} {α β γ : Loop A a}
    (h₁ : α = β) (h₂ : β = γ) : α = γ :=
  Eq.trans h₁ h₂

theorem hcomp2_assoc {a : A} {α β γ δ : Loop A a}
    (h₁ : α = β) (h₂ : β = γ) (h₃ : γ = δ) :
    hcomp2 (hcomp2 h₁ h₂) h₃ = hcomp2 h₁ (hcomp2 h₂ h₃) := by
  unfold hcomp2; apply Subsingleton.elim

/-! ## 38. 2-cell inverse -/

theorem hcomp2_inv_left {a : A} {α β : Loop A a}
    (h : α = β) :
    hcomp2 (Eq.symm h) h = rfl := by
  apply Subsingleton.elim

theorem hcomp2_inv_right {a : A} {α β : Loop A a}
    (h : α = β) :
    hcomp2 h (Eq.symm h) = rfl := by
  apply Subsingleton.elim

/-! ## 39. Eckmann-Hilton via interchange -/

theorem eckmann_hilton_interchange {a : A} {p : Loop A a}
    (α β : p = p) :
    hcomp2 α β = hcomp2 β α := by
  apply Subsingleton.elim

/-! ## 40. Transport and congrArg interaction for dependent types -/

theorem transport_congrArg_family {D : B → Type v} (f : A → B)
    {a b : A} (p : Path a b) (x : D (f a)) :
    Path.transport (D := D) (Path.congrArg f p) x =
    Path.transport (D := D ∘ f) p x := by
  cases p with | mk sp pp =>
  cases pp; rfl

/-! ## 41. Double transport -/

theorem transport_trans_compute {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
    Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-! ## 42. Transport round-trip -/

theorem transport_symm_roundtrip {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

theorem transport_roundtrip_symm {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport p (Path.transport (Path.symm p) y) = y :=
  Path.transport_symm_right p y

end LoopSpaceDeep
end Path
end ComputationalPaths
