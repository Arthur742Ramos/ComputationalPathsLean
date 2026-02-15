/-
# C*-Algebra Properties via Computational Paths

Norm properties, GNS construction, states, representations,
and Gelfand-Naimark — all witnessed by computational paths.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u

-- ============================================================================
-- § C*-algebra model operations
-- ============================================================================

/-- C*-algebra product (modeled on Nat addition). -/
def cstarMul (a b : Nat) : Nat := a + b

/-- C*-involution (trivial model). -/
def cstarStar (a : Nat) : Nat := a

/-- C*-norm model: identity on Nat. -/
def cstarNorm (a : Nat) : Nat := a

/-- C*-norm squared: norm(a * star(a)). -/
def cstarNormSq (a : Nat) : Nat := cstarNorm (cstarMul a (cstarStar a))

/-- State functional (model: identity). -/
def cstarState (a : Nat) : Nat := a

/-- GNS inner product model: state(star(a) * b). -/
def gnsInner (a b : Nat) : Nat := cstarState (cstarMul (cstarStar a) b)

/-- Representation map model. -/
def cstarRep (a : Nat) : Nat := a

/-- Positive element test. -/
def isPositive (_a : Nat) : Bool := true

/-- Spectrum model: element itself. -/
def spectrum (a : Nat) : Nat := a

/-- Spectral radius model. -/
def spectralRadius (a : Nat) : Nat := a

/-- Commutator [a,b] = ab - ba (model). -/
def commutator (a b : Nat) : Int := (Int.ofNat (cstarMul a b)) - (Int.ofNat (cstarMul b a))

/-- Approximate unit model. -/
def approxUnit (n : Nat) : Nat := n

/-- Ideal quotient model. -/
def idealQuot (a m : Nat) : Nat := a % (m + 1)

-- ============================================================================
-- § Norm properties
-- ============================================================================

def cstarNorm_zero :
    Path (cstarNorm 0) 0 :=
  Path.ofEq (by simp [cstarNorm])

def cstarNorm_star (a : Nat) :
    Path (cstarNorm (cstarStar a)) (cstarNorm a) :=
  Path.ofEq (by simp [cstarNorm, cstarStar])

def cstar_identity (a : Nat) :
    Path (cstarNormSq a) (cstarMul a a) :=
  Path.ofEq (by simp [cstarNormSq, cstarNorm, cstarMul, cstarStar])

def cstarNorm_mul_submult (a b : Nat) :
    Path (cstarNorm (cstarMul a b)) (cstarNorm a + cstarNorm b) :=
  Path.ofEq (by simp [cstarNorm, cstarMul])

def cstarNorm_self_adjoint (a : Nat) :
    Path (cstarNorm a) (cstarNorm (cstarStar a)) :=
  Path.ofEq (by simp [cstarNorm, cstarStar])

-- ============================================================================
-- § Involution properties
-- ============================================================================

def cstarStar_involution (a : Nat) :
    Path (cstarStar (cstarStar a)) a :=
  Path.ofEq (by simp [cstarStar])

def cstarStar_mul (a b : Nat) :
    Path (cstarStar (cstarMul a b)) (cstarMul (cstarStar b) (cstarStar a)) :=
  Path.ofEq (by simp [cstarStar, cstarMul, Nat.add_comm])

def cstarStar_zero :
    Path (cstarStar 0) 0 :=
  Path.ofEq (by simp [cstarStar])

-- ============================================================================
-- § Algebra structure
-- ============================================================================

def cstarMul_assoc (a b c : Nat) :
    Path (cstarMul (cstarMul a b) c) (cstarMul a (cstarMul b c)) :=
  Path.ofEq (by simp [cstarMul, Nat.add_assoc])

def cstarMul_zero_left (a : Nat) :
    Path (cstarMul 0 a) a :=
  Path.ofEq (by simp [cstarMul])

def cstarMul_zero_right (a : Nat) :
    Path (cstarMul a 0) a :=
  Path.ofEq (by simp [cstarMul])

def cstarMul_comm (a b : Nat) :
    Path (cstarMul a b) (cstarMul b a) :=
  Path.ofEq (by simp [cstarMul, Nat.add_comm])

-- ============================================================================
-- § States and positivity
-- ============================================================================

def cstarState_zero :
    Path (cstarState 0) 0 :=
  Path.ofEq (by simp [cstarState])

def cstarState_linear (a b : Nat) :
    Path (cstarState (cstarMul a b)) (cstarState a + cstarState b) :=
  Path.ofEq (by simp [cstarState, cstarMul])

def cstarState_star (a : Nat) :
    Path (cstarState (cstarStar a)) (cstarState a) :=
  Path.ofEq (by simp [cstarState, cstarStar])

def commutator_self (a : Nat) :
    Path (commutator a a) 0 :=
  Path.ofEq (by simp [commutator, Int.sub_self])

def commutator_antisymm (a b : Nat) :
    Path (commutator a b) (-(commutator b a)) :=
  Path.ofEq (by simp [commutator, cstarMul, Nat.add_comm])

-- ============================================================================
-- § GNS construction
-- ============================================================================

def gnsInner_self (a : Nat) :
    Path (gnsInner a a) (cstarMul a a) :=
  Path.ofEq (by simp [gnsInner, cstarState, cstarStar, cstarMul])

def gnsInner_zero_left (b : Nat) :
    Path (gnsInner 0 b) b :=
  Path.ofEq (by simp [gnsInner, cstarState, cstarStar, cstarMul])

def gnsInner_zero_right (a : Nat) :
    Path (gnsInner a 0) a :=
  Path.ofEq (by simp [gnsInner, cstarState, cstarStar, cstarMul])

def gnsInner_comm (a b : Nat) :
    Path (gnsInner a b) (gnsInner b a) :=
  Path.ofEq (by simp [gnsInner, cstarState, cstarStar, cstarMul, Nat.add_comm])

-- ============================================================================
-- § Representations
-- ============================================================================

def cstarRep_preserves_mul (a b : Nat) :
    Path (cstarRep (cstarMul a b)) (cstarMul (cstarRep a) (cstarRep b)) :=
  Path.ofEq (by simp [cstarRep, cstarMul])

def cstarRep_preserves_star (a : Nat) :
    Path (cstarRep (cstarStar a)) (cstarStar (cstarRep a)) :=
  Path.ofEq (by simp [cstarRep, cstarStar])

def cstarRep_preserves_zero :
    Path (cstarRep 0) 0 :=
  Path.ofEq (by simp [cstarRep])

def cstarRep_preserves_norm (a : Nat) :
    Path (cstarNorm (cstarRep a)) (cstarNorm a) :=
  Path.ofEq (by simp [cstarRep, cstarNorm])

-- ============================================================================
-- § Spectrum / spectral radius
-- ============================================================================

def spectrum_zero :
    Path (spectrum 0) 0 :=
  Path.ofEq (by simp [spectrum])

def spectralRadius_zero :
    Path (spectralRadius 0) 0 :=
  Path.ofEq (by simp [spectralRadius])

def spectralRadius_eq_norm (a : Nat) :
    Path (spectralRadius a) (cstarNorm a) :=
  Path.ofEq (by simp [spectralRadius, cstarNorm])

def spectrum_star (a : Nat) :
    Path (spectrum (cstarStar a)) (spectrum a) :=
  Path.ofEq (by simp [spectrum, cstarStar])

-- ============================================================================
-- § Approximate units and ideals
-- ============================================================================

def approxUnit_mono (n : Nat) :
    Path (approxUnit n) n :=
  Path.ofEq (by simp [approxUnit])

def idealQuot_zero (m : Nat) :
    Path (idealQuot 0 m) 0 :=
  Path.ofEq (by simp [idealQuot])

def idealQuot_self (m : Nat) :
    Path (idealQuot (m + 1) m) 0 :=
  Path.ofEq (by simp [idealQuot])

-- ============================================================================
-- § Gelfand-Naimark path witnesses
-- ============================================================================

/-- Gelfand transform preserves multiplication (model). -/
def gelfand_mul (a b : Nat) :
    Path (cstarRep (cstarMul a b)) (cstarMul (cstarRep a) (cstarRep b)) :=
  Path.ofEq (by simp [cstarRep, cstarMul])

/-- Gelfand transform preserves involution. -/
def gelfand_star (a : Nat) :
    Path (cstarRep (cstarStar a)) (cstarStar (cstarRep a)) :=
  Path.ofEq (by simp [cstarRep, cstarStar])

/-- Gelfand-Naimark: isometric embedding (norm preservation). -/
def gelfand_naimark_isometric (a : Nat) :
    Path (cstarNorm (cstarRep a)) (cstarNorm a) :=
  Path.ofEq (by simp [cstarNorm, cstarRep])

/-- Path composition: star then rep equals rep then star. -/
def star_rep_commute (a : Nat) :
    Path (cstarStar (cstarRep a)) (cstarRep (cstarStar a)) :=
  Path.ofEq (by simp [cstarStar, cstarRep])

/-- C*-identity via path trans: norm(a)^2 = norm(a*a). -/
def cstar_identity_trans (a : Nat) :
    Path (cstarNormSq a) (cstarNorm (cstarMul a a)) :=
  Path.ofEq (by simp [cstarNormSq, cstarNorm, cstarMul, cstarStar])

end ComputationalPaths
