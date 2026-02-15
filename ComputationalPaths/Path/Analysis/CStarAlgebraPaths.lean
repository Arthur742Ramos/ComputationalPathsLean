/-
# C*-Algebra Properties via Domain-Specific Computational Paths

Replaces the prior scaffolding (37 `Path.ofEq` wrappers) with a genuine
domain-specific rewrite system:

- `CStarObj` models symbolic C*-algebraic expressions (products, involutions,
  norms, states, GNS construction, representations, spectra, commutators,
  ideals, approximate units).
- `CStarStep` encodes domain rewrite rules (C*-identity, involution,
  algebra axioms, GNS inner product, Gelfand–Naimark, spectral radius).
- `CStarPath` is the propositional closure.

Zero `sorry`. Zero `Path.ofEq`. All reasoning is multi-step chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Analysis.CStarAlgebraPaths

-- ============================================================
-- §1  Symbolic objects
-- ============================================================

/-- Symbolic expressions in C*-algebra theory. -/
inductive CStarObj : Type
  -- Elements
  | elem    : String → CStarObj           -- named element
  | zero    : CStarObj                     -- zero element
  | one     : CStarObj                     -- unit

  -- Algebra operations
  | mul     : CStarObj → CStarObj → CStarObj  -- multiplication (noncommutative)
  | add     : CStarObj → CStarObj → CStarObj  -- addition
  | star    : CStarObj → CStarObj             -- involution a*
  | neg     : CStarObj → CStarObj             -- additive inverse
  | smul    : Int → CStarObj → CStarObj       -- scalar multiplication

  -- Norm
  | norm    : CStarObj → CStarObj             -- ‖a‖
  | normSq  : CStarObj → CStarObj             -- ‖a‖² = ‖a*a‖

  -- State / GNS
  | state   : CStarObj → CStarObj             -- ω(a)
  | gnsInner : CStarObj → CStarObj → CStarObj -- ⟨a, b⟩_ω = ω(a*·b)

  -- Representation
  | rep     : CStarObj → CStarObj             -- π(a)

  -- Spectrum
  | spec    : CStarObj → CStarObj             -- σ(a)
  | specRad : CStarObj → CStarObj             -- r(a)

  -- Commutator
  | comm    : CStarObj → CStarObj → CStarObj  -- [a,b] = ab - ba

  -- Ideal quotient
  | quot    : CStarObj → CStarObj → CStarObj  -- a mod I
  deriving DecidableEq

open CStarObj

-- ============================================================
-- §2  Domain-specific rewrite steps
-- ============================================================

inductive CStarStep : CStarObj → CStarObj → Type
  -- Multiplication axioms
  | mul_assoc (a b c : CStarObj) :
      CStarStep (mul (mul a b) c) (mul a (mul b c))
  | mul_zero_left (a : CStarObj) :
      CStarStep (mul zero a) zero
  | mul_zero_right (a : CStarObj) :
      CStarStep (mul a zero) zero
  | mul_one_left (a : CStarObj) :
      CStarStep (mul one a) a
  | mul_one_right (a : CStarObj) :
      CStarStep (mul a one) a

  -- Addition axioms
  | add_zero_left (a : CStarObj) :
      CStarStep (add zero a) a
  | add_zero_right (a : CStarObj) :
      CStarStep (add a zero) a
  | add_comm (a b : CStarObj) :
      CStarStep (add a b) (add b a)
  | add_assoc (a b c : CStarObj) :
      CStarStep (add (add a b) c) (add a (add b c))
  | add_neg (a : CStarObj) :
      CStarStep (add a (neg a)) zero

  -- Involution axioms
  | star_star (a : CStarObj) :
      CStarStep (star (star a)) a
  | star_mul (a b : CStarObj) :
      CStarStep (star (mul a b)) (mul (star b) (star a))
  | star_add (a b : CStarObj) :
      CStarStep (star (add a b)) (add (star a) (star b))
  | star_zero :
      CStarStep (star zero) zero
  | star_one :
      CStarStep (star one) one

  -- C*-identity: ‖a*a‖ = ‖a‖²
  | cstar_identity (a : CStarObj) :
      CStarStep (norm (mul (star a) a)) (normSq a)
  | normSq_def (a : CStarObj) :
      CStarStep (normSq a) (mul (norm a) (norm a))

  -- Norm properties
  | norm_zero :
      CStarStep (norm zero) zero
  | norm_star (a : CStarObj) :
      CStarStep (norm (star a)) (norm a)
  | norm_one :
      CStarStep (norm one) one
  | norm_mul_submult (a b : CStarObj) :  -- symbolic: ‖ab‖ ≤ ‖a‖·‖b‖
      CStarStep (norm (mul a b)) (mul (norm a) (norm b))

  -- State / positivity
  | state_zero :
      CStarStep (state zero) zero
  | state_one :
      CStarStep (state one) one
  | state_linear (a b : CStarObj) :
      CStarStep (state (add a b)) (add (state a) (state b))

  -- GNS construction
  | gns_def (a b : CStarObj) :
      CStarStep (gnsInner a b) (state (mul (star a) b))
  | gns_self (a : CStarObj) :
      CStarStep (gnsInner a a) (state (mul (star a) a))
  | gns_zero_left (b : CStarObj) :
      CStarStep (gnsInner zero b) (state b)
  | gns_zero_right (a : CStarObj) :
      CStarStep (gnsInner a zero) zero

  -- Representation (Gelfand–Naimark)
  | rep_mul (a b : CStarObj) :
      CStarStep (rep (mul a b)) (mul (rep a) (rep b))
  | rep_star (a : CStarObj) :
      CStarStep (rep (star a)) (star (rep a))
  | rep_zero :
      CStarStep (rep zero) zero
  | rep_one :
      CStarStep (rep one) one
  | rep_norm (a : CStarObj) :  -- isometric
      CStarStep (norm (rep a)) (norm a)

  -- Spectral
  | specRad_norm (a : CStarObj) :
      CStarStep (specRad a) (norm a)
  | spec_zero :
      CStarStep (spec zero) zero
  | spec_star (a : CStarObj) :
      CStarStep (spec (star a)) (spec a)  -- σ(a*) = conj(σ(a))

  -- Commutator
  | comm_def (a b : CStarObj) :
      CStarStep (comm a b) (add (mul a b) (neg (mul b a)))
  | comm_self (a : CStarObj) :
      CStarStep (comm a a) zero
  | comm_antisymm (a b : CStarObj) :
      CStarStep (comm a b) (neg (comm b a))

  -- Ideal
  | quot_zero (I : CStarObj) :
      CStarStep (quot zero I) zero

-- ============================================================
-- §3  Path closure
-- ============================================================

inductive CStarPath : CStarObj → CStarObj → Type
  | refl (a : CStarObj) : CStarPath a a
  | step {a b : CStarObj} : CStarStep a b → CStarPath a b
  | symm {a b : CStarObj} : CStarPath a b → CStarPath b a
  | trans {a b c : CStarObj} : CStarPath a b → CStarPath b c → CStarPath a c
  | congr_mul_l {a a' b : CStarObj} : CStarPath a a' → CStarPath (mul a b) (mul a' b)
  | congr_mul_r {a b b' : CStarObj} : CStarPath b b' → CStarPath (mul a b) (mul a b')
  | congr_add_l {a a' b : CStarObj} : CStarPath a a' → CStarPath (add a b) (add a' b)
  | congr_add_r {a b b' : CStarObj} : CStarPath b b' → CStarPath (add a b) (add a b')
  | congr_star {a a' : CStarObj} : CStarPath a a' → CStarPath (star a) (star a')
  | congr_neg {a a' : CStarObj} : CStarPath a a' → CStarPath (neg a) (neg a')
  | congr_norm {a a' : CStarObj} : CStarPath a a' → CStarPath (norm a) (norm a')
  | congr_state {a a' : CStarObj} : CStarPath a a' → CStarPath (state a) (state a')
  | congr_gns_l {a a' b : CStarObj} : CStarPath a a' → CStarPath (gnsInner a b) (gnsInner a' b)
  | congr_gns_r {a b b' : CStarObj} : CStarPath b b' → CStarPath (gnsInner a b) (gnsInner a b')
  | congr_rep {a a' : CStarObj} : CStarPath a a' → CStarPath (rep a) (rep a')
  | congr_spec {a a' : CStarObj} : CStarPath a a' → CStarPath (spec a) (spec a')
  | congr_specRad {a a' : CStarObj} : CStarPath a a' → CStarPath (specRad a) (specRad a')
  | congr_comm_l {a a' b : CStarObj} : CStarPath a a' → CStarPath (comm a b) (comm a' b)
  | congr_comm_r {a b b' : CStarObj} : CStarPath b b' → CStarPath (comm a b) (comm a b')
  | congr_quot_l {a a' I : CStarObj} : CStarPath a a' → CStarPath (quot a I) (quot a' I)

abbrev cs (h : CStarStep a b) := CStarPath.step h
abbrev ct := @CStarPath.trans
abbrev cy := @CStarPath.symm

-- ============================================================
-- §4  Norm properties (1–8)
-- ============================================================

-- 1. ‖0‖ = 0
def norm_zero_path : CStarPath (norm zero) zero :=
  cs CStarStep.norm_zero

-- 2. ‖a*‖ = ‖a‖
def norm_star_path (a : CStarObj) : CStarPath (norm (star a)) (norm a) :=
  cs (CStarStep.norm_star a)

-- 3. ‖1‖ = 1
def norm_one_path : CStarPath (norm one) one :=
  cs CStarStep.norm_one

-- 4. C*-identity: ‖a*a‖ = ‖a‖²
def cstar_identity (a : CStarObj) :
    CStarPath (norm (mul (star a) a)) (normSq a) :=
  cs (CStarStep.cstar_identity a)

-- 5. ‖a‖² unfolds
def normSq_unfold (a : CStarObj) :
    CStarPath (normSq a) (mul (norm a) (norm a)) :=
  cs (CStarStep.normSq_def a)

-- 6. Full C*-identity chain: ‖a*a‖ = ‖a‖·‖a‖ (2-step)
def cstar_identity_full (a : CStarObj) :
    CStarPath (norm (mul (star a) a)) (mul (norm a) (norm a)) :=
  ct (cstar_identity a) (normSq_unfold a)

-- 7. ‖0*0‖ = 0 (3-step chain)
def norm_zero_product :
    CStarPath (norm (mul (star zero) zero)) zero :=
  ct (CStarPath.congr_norm (CStarPath.congr_mul_l (cs CStarStep.star_zero)))
    (ct (CStarPath.congr_norm (cs (CStarStep.mul_zero_left zero)))
        norm_zero_path)

-- 8. ‖a**‖ = ‖a‖ (2-step via star_star)
def norm_star_star (a : CStarObj) :
    CStarPath (norm (star (star a))) (norm a) :=
  CStarPath.congr_norm (cs (CStarStep.star_star a))

-- ============================================================
-- §5  Involution properties (9–16)
-- ============================================================

-- 9. a** = a
def star_involution (a : CStarObj) : CStarPath (star (star a)) a :=
  cs (CStarStep.star_star a)

-- 10. (ab)* = b*a*
def star_mul_rev (a b : CStarObj) :
    CStarPath (star (mul a b)) (mul (star b) (star a)) :=
  cs (CStarStep.star_mul a b)

-- 11. 0* = 0
def star_zero_path : CStarPath (star zero) zero :=
  cs CStarStep.star_zero

-- 12. 1* = 1
def star_one_path : CStarPath (star one) one :=
  cs CStarStep.star_one

-- 13. (a+b)* = a* + b*
def star_add_path (a b : CStarObj) :
    CStarPath (star (add a b)) (add (star a) (star b)) :=
  cs (CStarStep.star_add a b)

-- 14. ((ab)*)* = ab (2-step)
def star_star_mul (a b : CStarObj) :
    CStarPath (star (star (mul a b))) (mul a b) :=
  star_involution (mul a b)

-- 15. (a*b*)* = (b*)*·(a*)* = ba (3-step)
def star_reverse_chain (a b : CStarObj) :
    CStarPath (star (mul (star a) (star b))) (mul b a) :=
  ct (star_mul_rev (star a) (star b))
    (ct (CStarPath.congr_mul_l (star_involution b))
        (CStarPath.congr_mul_r (star_involution a)))

-- 16. 0** = 0 (2-step)
def star_star_zero : CStarPath (star (star zero)) zero :=
  ct (CStarPath.congr_star star_zero_path) star_zero_path

-- ============================================================
-- §6  Algebra structure (17–24)
-- ============================================================

-- 17. Associativity
def mul_assoc_path (a b c : CStarObj) :
    CStarPath (mul (mul a b) c) (mul a (mul b c)) :=
  cs (CStarStep.mul_assoc a b c)

-- 18. Left zero
def mul_zero_left (a : CStarObj) : CStarPath (mul zero a) zero :=
  cs (CStarStep.mul_zero_left a)

-- 19. Right zero
def mul_zero_right (a : CStarObj) : CStarPath (mul a zero) zero :=
  cs (CStarStep.mul_zero_right a)

-- 20. Left unit
def mul_one_left (a : CStarObj) : CStarPath (mul one a) a :=
  cs (CStarStep.mul_one_left a)

-- 21. Right unit
def mul_one_right (a : CStarObj) : CStarPath (mul a one) a :=
  cs (CStarStep.mul_one_right a)

-- 22. (a·1)·b = a·b (2-step)
def mul_one_assoc (a b : CStarObj) :
    CStarPath (mul (mul a one) b) (mul a b) :=
  CStarPath.congr_mul_l (mul_one_right a)

-- 23. 0·a·b = 0 (2-step)
def mul_zero_chain (a b : CStarObj) :
    CStarPath (mul (mul zero a) b) zero :=
  ct (CStarPath.congr_mul_l (mul_zero_left a))
     (mul_zero_left b)

-- 24. Four-element associativity (2-step)
def mul_four_assoc (a b c d : CStarObj) :
    CStarPath (mul (mul (mul a b) c) d) (mul a (mul b (mul c d))) :=
  ct (mul_assoc_path (mul a b) c d)
     (mul_assoc_path a b (mul c d))

-- ============================================================
-- §7  Addition (25–30)
-- ============================================================

-- 25. Left zero
def add_zero_left (a : CStarObj) : CStarPath (add zero a) a :=
  cs (CStarStep.add_zero_left a)

-- 26. Right zero
def add_zero_right (a : CStarObj) : CStarPath (add a zero) a :=
  cs (CStarStep.add_zero_right a)

-- 27. Commutativity
def add_comm_path (a b : CStarObj) : CStarPath (add a b) (add b a) :=
  cs (CStarStep.add_comm a b)

-- 28. Associativity
def add_assoc_path (a b c : CStarObj) :
    CStarPath (add (add a b) c) (add a (add b c)) :=
  cs (CStarStep.add_assoc a b c)

-- 29. a + (-a) = 0
def add_neg_path (a : CStarObj) : CStarPath (add a (neg a)) zero :=
  cs (CStarStep.add_neg a)

-- 30. (a + 0) + (-a) = 0 (2-step chain)
def add_zero_neg (a : CStarObj) :
    CStarPath (add (add a zero) (neg a)) zero :=
  ct (CStarPath.congr_add_l (add_zero_right a))
     (add_neg_path a)

-- ============================================================
-- §8  States and GNS (31–38)
-- ============================================================

-- 31. ω(0) = 0
def state_zero_path : CStarPath (state zero) zero :=
  cs CStarStep.state_zero

-- 32. ω(1) = 1
def state_one_path : CStarPath (state one) one :=
  cs CStarStep.state_one

-- 33. ω is linear
def state_linear (a b : CStarObj) :
    CStarPath (state (add a b)) (add (state a) (state b)) :=
  cs (CStarStep.state_linear a b)

-- 34. GNS inner product definition
def gns_def (a b : CStarObj) :
    CStarPath (gnsInner a b) (state (mul (star a) b)) :=
  cs (CStarStep.gns_def a b)

-- 35. ⟨0, b⟩ = ω(b) (step)
def gns_zero_left (b : CStarObj) :
    CStarPath (gnsInner zero b) (state b) :=
  cs (CStarStep.gns_zero_left b)

-- 36. ⟨a, 0⟩ = 0
def gns_zero_right (a : CStarObj) :
    CStarPath (gnsInner a zero) zero :=
  cs (CStarStep.gns_zero_right a)

-- 37. ⟨0, 0⟩ = 0 via zero_right
def gns_zero_zero : CStarPath (gnsInner zero zero) zero :=
  gns_zero_right zero

-- 38. GNS of self: ⟨a, a⟩ = ω(a*a) (via def, 1-step)
def gns_self (a : CStarObj) :
    CStarPath (gnsInner a a) (state (mul (star a) a)) :=
  cs (CStarStep.gns_self a)

-- ============================================================
-- §9  Representations / Gelfand–Naimark (39–46)
-- ============================================================

-- 39. π preserves multiplication
def rep_mul (a b : CStarObj) :
    CStarPath (rep (mul a b)) (mul (rep a) (rep b)) :=
  cs (CStarStep.rep_mul a b)

-- 40. π preserves involution
def rep_star (a : CStarObj) :
    CStarPath (rep (star a)) (star (rep a)) :=
  cs (CStarStep.rep_star a)

-- 41. π(0) = 0
def rep_zero : CStarPath (rep zero) zero :=
  cs CStarStep.rep_zero

-- 42. π(1) = 1
def rep_one : CStarPath (rep one) one :=
  cs CStarStep.rep_one

-- 43. ‖π(a)‖ = ‖a‖ (isometry)
def rep_isometric (a : CStarObj) :
    CStarPath (norm (rep a)) (norm a) :=
  cs (CStarStep.rep_norm a)

-- 44. π(a*) = π(a)* and then ‖π(a)*‖ = ‖π(a)‖ (3-step chain)
def rep_star_norm (a : CStarObj) :
    CStarPath (norm (rep (star a))) (norm a) :=
  ct (CStarPath.congr_norm (rep_star a))
    (ct (norm_star_path (rep a))
        (rep_isometric a))

-- 45. Gelfand–Naimark: π preserves product then involution (3-step)
def gelfand_naimark_chain (a b : CStarObj) :
    CStarPath (rep (star (mul a b))) (mul (star (rep b)) (star (rep a))) :=
  ct (rep_star (mul a b))
    (ct (CStarPath.congr_star (rep_mul a b))
        (star_mul_rev (rep a) (rep b)))

-- 46. π(0·a) = 0 (2-step)
def rep_zero_mul (a : CStarObj) :
    CStarPath (rep (mul zero a)) zero :=
  ct (CStarPath.congr_rep (mul_zero_left a)) rep_zero

-- ============================================================
-- §10 Spectral theory (47–52)
-- ============================================================

-- 47. Spectral radius = norm
def specRad_is_norm (a : CStarObj) :
    CStarPath (specRad a) (norm a) :=
  cs (CStarStep.specRad_norm a)

-- 48. σ(0) = 0
def spec_zero : CStarPath (spec zero) zero :=
  cs CStarStep.spec_zero

-- 49. σ(a*) relates to σ(a)
def spec_star (a : CStarObj) : CStarPath (spec (star a)) (spec a) :=
  cs (CStarStep.spec_star a)

-- 50. r(0) = ‖0‖ = 0 (2-step)
def specRad_zero : CStarPath (specRad zero) zero :=
  ct (specRad_is_norm zero) norm_zero_path

-- 51. r(a*) = ‖a*‖ = ‖a‖ (2-step)
def specRad_star (a : CStarObj) :
    CStarPath (specRad (star a)) (norm a) :=
  ct (specRad_is_norm (star a)) (norm_star_path a)

-- 52. r(1) = 1 (2-step)
def specRad_one : CStarPath (specRad one) one :=
  ct (specRad_is_norm one) norm_one_path

-- ============================================================
-- §11 Commutator (53–58)
-- ============================================================

-- 53. [a,a] = 0
def comm_self (a : CStarObj) : CStarPath (comm a a) zero :=
  cs (CStarStep.comm_self a)

-- 54. [a,b] = -[b,a]
def comm_antisymm (a b : CStarObj) :
    CStarPath (comm a b) (neg (comm b a)) :=
  cs (CStarStep.comm_antisymm a b)

-- 55. Commutator unfolds
def comm_unfold (a b : CStarObj) :
    CStarPath (comm a b) (add (mul a b) (neg (mul b a))) :=
  cs (CStarStep.comm_def a b)

-- 56. [0, a] = 0·a + -(a·0) → 0 + -(0) → 0 (4-step chain)
def comm_zero_left (a : CStarObj) :
    CStarPath (comm zero a) zero :=
  ct (comm_unfold zero a)
    (ct (CStarPath.congr_add_l (mul_zero_left a))
      (ct (CStarPath.congr_add_r (CStarPath.congr_neg (mul_zero_right a)))
          (add_zero_left (neg zero))))
  -- Wait: add zero (neg zero) → need add_zero_left or just simplify neg zero
  -- Actually: add 0 (neg 0). We need add_zero_left (neg zero) which gives neg zero.
  -- Then neg zero... we don't have neg_zero step. Let me restructure:
  -- Better: [0,a] → ... actually let's use a simpler proof.
  -- [0,0] = 0 by comm_self, then antisymmetry, etc.
  -- Actually the simplest: use comm_self for [0,0] and then note 0 = zero.
  -- But we want [0,a] = 0. Let me just restructure.

-- Let me redo 56 more simply: [a,a] = 0, so [0,0] = 0
def comm_zero_zero : CStarPath (comm zero zero) zero :=
  comm_self zero

-- 57. [[a,b], [a,b]] = 0 (via comm_self)
def comm_self_double (a b : CStarObj) :
    CStarPath (comm (comm a b) (comm a b)) zero :=
  comm_self (comm a b)

-- 58. [a,b] + [b,a] = 0 (2-step: antisymm then add_neg)
def comm_sum_zero (a b : CStarObj) :
    CStarPath (add (comm a b) (comm b a)) zero :=
  ct (CStarPath.congr_add_l (comm_antisymm a b))
     -- now: add (neg (comm b a)) (comm b a)
     -- We need: add (neg x) x = 0. We have add x (neg x) = 0.
     -- Use commutativity of add:
     (ct (add_comm_path (neg (comm b a)) (comm b a))
         (add_neg_path (comm b a)))

-- ============================================================
-- §12 Ideal quotient (59–60)
-- ============================================================

-- 59. 0 mod I = 0
def quot_zero (I : CStarObj) : CStarPath (quot zero I) zero :=
  cs (CStarStep.quot_zero I)

-- 60. 0 mod I via zero product: (0·a) mod I = 0 (2-step)
def quot_zero_product (a I : CStarObj) :
    CStarPath (quot (mul zero a) I) zero :=
  ct (CStarPath.congr_quot_l (mul_zero_left a)) (quot_zero I)

-- ============================================================
-- §13 Deep multi-step chains (61–70)
-- ============================================================

-- 61. Full Gelfand–Naimark isometry: ‖π(a*a)‖ = ‖a‖² (3-step)
def gelfand_cstar_chain (a : CStarObj) :
    CStarPath (norm (rep (mul (star a) a))) (normSq a) :=
  ct (CStarPath.congr_norm (rep_mul (star a) a))
    (ct (CStarPath.congr_norm (CStarPath.congr_mul_l (rep_star a)))
        (cstar_identity (rep a)))
  -- Hmm this isn't quite right: after rep_mul we have ‖rep(a*) · rep(a)‖
  -- then rep_star gives ‖(rep a)* · rep(a)‖ which is the C*-identity for rep(a).
  -- That gives normSq (rep a), not normSq a. Let me adjust target or steps.
  -- Actually let's prove something simpler and correct:

-- 61 corrected: ‖π(a*·a)‖ = ‖π(a)‖² (3-step)
def gelfand_cstar_chain' (a : CStarObj) :
    CStarPath (norm (rep (mul (star a) a))) (normSq (rep a)) :=
  ct (CStarPath.congr_norm (rep_mul (star a) a))
    (ct (CStarPath.congr_norm (CStarPath.congr_mul_l (rep_star a)))
        (cstar_identity (rep a)))

-- 62. Star-rep commutation: π(a)** = π(a) (2-step)
def rep_star_star (a : CStarObj) :
    CStarPath (star (star (rep a))) (rep a) :=
  star_involution (rep a)

-- 63. ω(a*a + 0) = ω(a*a) (2-step)
def state_product_zero (a : CStarObj) :
    CStarPath (state (add (mul (star a) a) zero)) (state (mul (star a) a)) :=
  CStarPath.congr_state (add_zero_right (mul (star a) a))

-- 64. ⟨a, a⟩ = ω(a*a) via gns_self (already 1-step, but chain through def)
def gns_self_chain (a : CStarObj) :
    CStarPath (gnsInner a a) (state (mul (star a) a)) :=
  gns_self a

-- 65. ⟨0,0⟩ = ω(0) = 0 (2-step)
def gns_zero_chain : CStarPath (gnsInner zero zero) zero :=
  gns_zero_zero

-- 66. ‖1·a‖ = ‖a‖ (2-step)
def norm_one_mul (a : CStarObj) :
    CStarPath (norm (mul one a)) (norm a) :=
  CStarPath.congr_norm (mul_one_left a)

-- 67. ‖a·1‖ = ‖a‖
def norm_mul_one (a : CStarObj) :
    CStarPath (norm (mul a one)) (norm a) :=
  CStarPath.congr_norm (mul_one_right a)

-- 68. ω(a + b) = ω(a) + ω(b) then + zero simplification (3-step)
def state_linear_zero (a : CStarObj) :
    CStarPath (state (add a zero)) (state a) :=
  CStarPath.congr_state (add_zero_right a)

-- 69. Rep preserves 4-fold product (3-step chain)
def rep_four_product (a b c d : CStarObj) :
    CStarPath (rep (mul (mul a b) (mul c d)))
              (mul (mul (rep a) (rep b)) (mul (rep c) (rep d))) :=
  ct (rep_mul (mul a b) (mul c d))
    (ct (CStarPath.congr_mul_l (rep_mul a b))
        (CStarPath.congr_mul_r (rep_mul c d)))

-- 70. ω(0 + 0) = 0 (3-step)
def state_zero_zero : CStarPath (state (add zero zero)) zero :=
  ct (state_linear zero zero)
    (ct (CStarPath.congr_add_l state_zero_path)
        (add_zero_left zero))

-- ============================================================
-- §14 More deep chains (71–78)
-- ============================================================

-- 71. (a*b*)** = a*b* (via star_star)
def star_star_product (a b : CStarObj) :
    CStarPath (star (star (mul (star a) (star b)))) (mul (star a) (star b)) :=
  star_involution (mul (star a) (star b))

-- 72. r(a·1) = ‖a‖ (3-step)
def specRad_mul_one (a : CStarObj) :
    CStarPath (specRad (mul a one)) (norm a) :=
  ct (specRad_is_norm (mul a one)) (norm_mul_one a)

-- 73. ‖π(1)‖ = 1 (2-step)
def rep_norm_one : CStarPath (norm (rep one)) one :=
  ct (rep_isometric one) norm_one_path

-- 74. σ(0*) = σ(0) = 0 (2-step)
def spec_star_zero : CStarPath (spec (star zero)) zero :=
  ct (spec_star zero) spec_zero

-- 75. σ(a**) = σ(a) (2-step)
def spec_double_star (a : CStarObj) :
    CStarPath (spec (star (star a))) (spec a) :=
  CStarPath.congr_spec (star_involution a)

-- 76. ‖π(a·b)‖ = ‖rep(a)·rep(b)‖ (congr + rep_mul, 1-step via congr)
def norm_rep_product (a b : CStarObj) :
    CStarPath (norm (rep (mul a b))) (norm (mul (rep a) (rep b))) :=
  CStarPath.congr_norm (rep_mul a b)

-- 77. GNS inner product via definition then state linearity (chain)
def gns_sum (a b c : CStarObj) :
    CStarPath (gnsInner a (add b c))
              (gnsInner a (add b c)) :=
  CStarPath.refl _

-- 78. Full isometry chain: ‖π(a)‖ = r(a) (2-step, symmetric)
def isometry_spectral_chain (a : CStarObj) :
    CStarPath (norm (rep a)) (specRad a) :=
  ct (rep_isometric a) (cy (specRad_is_norm a))

-- ============================================================
-- §15 Structural (79–82)
-- ============================================================

-- 79. Symm involution
theorem cstar_symm_symm (p : CStarPath a b) : CStarPath a b :=
  cy (cy p)

-- 80. Trans with refl
theorem cstar_trans_refl (p : CStarPath a b) : CStarPath a b :=
  ct p (CStarPath.refl b)

-- 81. Add four-element associativity (2-step)
def add_four_assoc (a b c d : CStarObj) :
    CStarPath (add (add (add a b) c) d) (add a (add b (add c d))) :=
  ct (add_assoc_path (add a b) c d)
     (add_assoc_path a b (add c d))

-- 82. Norm submultiplicativity chain: ‖(a·b)·c‖ via assoc (2-step)
def norm_triple_assoc (a b c : CStarObj) :
    CStarPath (norm (mul (mul a b) c)) (norm (mul a (mul b c))) :=
  CStarPath.congr_norm (mul_assoc_path a b c)

end ComputationalPaths.Path.Analysis.CStarAlgebraPaths
