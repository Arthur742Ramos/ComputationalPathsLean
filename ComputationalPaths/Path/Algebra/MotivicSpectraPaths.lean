/-
# Motivic Spectra via Computational Paths

Motivic spectra, motivic Eilenberg-MacLane spectrum, algebraic K-theory spectrum,
motivic Adams spectral sequence, eta-periodic phenomena.

## References

- Morel-Voevodsky, "A¹-homotopy theory of schemes"
- Voevodsky, "Motivic cohomology with Z/2-coefficients"
- Isaksen, "Stable Stems"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Motivic Spectra -/

/-- A motivic spectrum: bigraded with both simplicial and algebraic shifts. -/
structure MotivicSpectrum (E : Type u) where
  smash : E → E → E
  wedge : E → E → E
  zero : E
  shift_s : E → E  -- simplicial suspension
  shift_a : E → E  -- algebraic (Tate twist) suspension
  unshift_s : E → E
  unshift_a : E → E
  shift_s_unshift_s : ∀ (e : E), Path (shift_s (unshift_s e)) e
  unshift_s_shift_s : ∀ (e : E), Path (unshift_s (shift_s e)) e
  shift_a_unshift_a : ∀ (e : E), Path (shift_a (unshift_a e)) e
  unshift_a_shift_a : ∀ (e : E), Path (unshift_a (shift_a e)) e
  smash_comm : ∀ (a b : E), Path (smash a b) (smash b a)
  smash_assoc : ∀ (a b c : E), Path (smash (smash a b) c) (smash a (smash b c))
  wedge_comm : ∀ (a b : E), Path (wedge a b) (wedge b a)
  wedge_assoc : ∀ (a b c : E), Path (wedge (wedge a b) c) (wedge a (wedge b c))
  wedge_zero : ∀ (a : E), Path (wedge a zero) a
  shift_smash : ∀ (a b : E), Path (shift_s (smash a b)) (smash (shift_s a) b)

namespace MotivicSpectrum

variable {E : Type u} (MS : MotivicSpectrum E)

theorem shift_s_unshift_s_eq (e : E) : MS.shift_s (MS.unshift_s e) = e := (MS.shift_s_unshift_s e).toEq
theorem unshift_s_shift_s_eq (e : E) : MS.unshift_s (MS.shift_s e) = e := (MS.unshift_s_shift_s e).toEq
theorem shift_a_unshift_a_eq (e : E) : MS.shift_a (MS.unshift_a e) = e := (MS.shift_a_unshift_a e).toEq
theorem unshift_a_shift_a_eq (e : E) : MS.unshift_a (MS.shift_a e) = e := (MS.unshift_a_shift_a e).toEq
theorem smash_comm_eq (a b : E) : MS.smash a b = MS.smash b a := (MS.smash_comm a b).toEq
theorem smash_assoc_eq (a b c : E) : MS.smash (MS.smash a b) c = MS.smash a (MS.smash b c) := (MS.smash_assoc a b c).toEq
theorem wedge_comm_eq (a b : E) : MS.wedge a b = MS.wedge b a := (MS.wedge_comm a b).toEq
theorem wedge_assoc_eq (a b c : E) : MS.wedge (MS.wedge a b) c = MS.wedge a (MS.wedge b c) := (MS.wedge_assoc a b c).toEq
theorem wedge_zero_eq (a : E) : MS.wedge a MS.zero = a := (MS.wedge_zero a).toEq
theorem shift_smash_eq (a b : E) : MS.shift_s (MS.smash a b) = MS.smash (MS.shift_s a) b := (MS.shift_smash a b).toEq

/-- Double shift-unshift (simplicial). -/
noncomputable def double_shift_s (e : E) :
    Path (MS.shift_s (MS.unshift_s (MS.shift_s (MS.unshift_s e)))) e :=
  Path.trans (congrArg MS.shift_s (congrArg MS.unshift_s (MS.shift_s_unshift_s e))) (MS.shift_s_unshift_s e)

theorem double_shift_s_eq (e : E) : MS.shift_s (MS.unshift_s (MS.shift_s (MS.unshift_s e))) = e :=
  (MS.double_shift_s e).toEq

/-- Double shift-unshift (algebraic). -/
noncomputable def double_shift_a (e : E) :
    Path (MS.shift_a (MS.unshift_a (MS.shift_a (MS.unshift_a e)))) e :=
  Path.trans (congrArg MS.shift_a (congrArg MS.unshift_a (MS.shift_a_unshift_a e))) (MS.shift_a_unshift_a e)

theorem double_shift_a_eq (e : E) : MS.shift_a (MS.unshift_a (MS.shift_a (MS.unshift_a e))) = e :=
  (MS.double_shift_a e).toEq

/-- Triple smash assoc. -/
noncomputable def triple_smash (a b c d : E) :
    Path (MS.smash (MS.smash (MS.smash a b) c) d) (MS.smash a (MS.smash b (MS.smash c d))) :=
  Path.trans (MS.smash_assoc (MS.smash a b) c d) (MS.smash_assoc a b (MS.smash c d))

theorem triple_smash_eq (a b c d : E) :
    MS.smash (MS.smash (MS.smash a b) c) d = MS.smash a (MS.smash b (MS.smash c d)) :=
  (MS.triple_smash a b c d).toEq

/-- Wedge with zero on both sides. -/
noncomputable def wedge_zero_zero (a : E) :
    Path (MS.wedge (MS.wedge a MS.zero) MS.zero) a :=
  Path.trans (MS.wedge_zero (MS.wedge a MS.zero)) (MS.wedge_zero a)

theorem wedge_zero_zero_eq (a : E) : MS.wedge (MS.wedge a MS.zero) MS.zero = a :=
  (MS.wedge_zero_zero a).toEq

end MotivicSpectrum

/-! ## Motivic Eilenberg-MacLane Spectrum -/

/-- The motivic Eilenberg-MacLane spectrum HZ. -/
structure MotivicEilenbergMacLane (HZ : Type u) where
  spectrum : MotivicSpectrum HZ
  cup : HZ → HZ → HZ
  unit : HZ
  cup_assoc : ∀ (a b c : HZ), Path (cup (cup a b) c) (cup a (cup b c))
  cup_unit : ∀ (a : HZ), Path (cup a unit) a
  unit_cup : ∀ (a : HZ), Path (cup unit a) a
  cup_comm : ∀ (a b : HZ), Path (cup a b) (cup b a)

namespace MotivicEilenbergMacLane

variable {HZ : Type u} (MEM : MotivicEilenbergMacLane HZ)

theorem cup_assoc_eq (a b c : HZ) : MEM.cup (MEM.cup a b) c = MEM.cup a (MEM.cup b c) :=
  (MEM.cup_assoc a b c).toEq
theorem cup_unit_eq (a : HZ) : MEM.cup a MEM.unit = a := (MEM.cup_unit a).toEq
theorem unit_cup_eq (a : HZ) : MEM.cup MEM.unit a = a := (MEM.unit_cup a).toEq
theorem cup_comm_eq (a b : HZ) : MEM.cup a b = MEM.cup b a := (MEM.cup_comm a b).toEq

/-- Triple cup. -/
noncomputable def triple_cup (a b c d : HZ) :
    Path (MEM.cup (MEM.cup (MEM.cup a b) c) d) (MEM.cup a (MEM.cup b (MEM.cup c d))) :=
  Path.trans (MEM.cup_assoc (MEM.cup a b) c d) (MEM.cup_assoc a b (MEM.cup c d))

theorem triple_cup_eq (a b c d : HZ) :
    MEM.cup (MEM.cup (MEM.cup a b) c) d = MEM.cup a (MEM.cup b (MEM.cup c d)) :=
  (MEM.triple_cup a b c d).toEq

/-- Unit absorbed on both sides. -/
noncomputable def unit_cup_unit (a : HZ) :
    Path (MEM.cup MEM.unit (MEM.cup a MEM.unit)) a :=
  Path.trans (MEM.unit_cup (MEM.cup a MEM.unit)) (MEM.cup_unit a)

theorem unit_cup_unit_eq (a : HZ) : MEM.cup MEM.unit (MEM.cup a MEM.unit) = a :=
  (MEM.unit_cup_unit a).toEq

end MotivicEilenbergMacLane

/-! ## Algebraic K-Theory Spectrum -/

/-- The algebraic K-theory spectrum KGL. -/
structure AlgebraicKTheorySpectrum (KGL : Type u) where
  spectrum : MotivicSpectrum KGL
  bott : KGL → KGL  -- Bott element action
  bott_inv : KGL → KGL
  bott_periodic : ∀ (e : KGL), Path (bott (bott_inv e)) e
  bott_inv_periodic : ∀ (e : KGL), Path (bott_inv (bott e)) e
  mul : KGL → KGL → KGL
  one : KGL
  mul_assoc : ∀ (a b c : KGL), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : KGL), Path (mul a one) a
  one_mul : ∀ (a : KGL), Path (mul one a) a
  mul_comm : ∀ (a b : KGL), Path (mul a b) (mul b a)

namespace AlgebraicKTheorySpectrum

variable {KGL : Type u} (K : AlgebraicKTheorySpectrum KGL)

theorem bott_periodic_eq (e : KGL) : K.bott (K.bott_inv e) = e := (K.bott_periodic e).toEq
theorem bott_inv_periodic_eq (e : KGL) : K.bott_inv (K.bott e) = e := (K.bott_inv_periodic e).toEq
theorem mul_assoc_eq (a b c : KGL) : K.mul (K.mul a b) c = K.mul a (K.mul b c) := (K.mul_assoc a b c).toEq
theorem mul_one_eq (a : KGL) : K.mul a K.one = a := (K.mul_one a).toEq
theorem one_mul_eq (a : KGL) : K.mul K.one a = a := (K.one_mul a).toEq
theorem mul_comm_eq (a b : KGL) : K.mul a b = K.mul b a := (K.mul_comm a b).toEq

/-- Double Bott periodicity. -/
noncomputable def double_bott (e : KGL) :
    Path (K.bott (K.bott_inv (K.bott (K.bott_inv e)))) e :=
  Path.trans (congrArg K.bott (congrArg K.bott_inv (K.bott_periodic e))) (K.bott_periodic e)

theorem double_bott_eq (e : KGL) : K.bott (K.bott_inv (K.bott (K.bott_inv e))) = e :=
  (K.double_bott e).toEq

/-- Triple mul assoc. -/
noncomputable def triple_mul (a b c d : KGL) :
    Path (K.mul (K.mul (K.mul a b) c) d) (K.mul a (K.mul b (K.mul c d))) :=
  Path.trans (K.mul_assoc (K.mul a b) c d) (K.mul_assoc a b (K.mul c d))

theorem triple_mul_eq (a b c d : KGL) :
    K.mul (K.mul (K.mul a b) c) d = K.mul a (K.mul b (K.mul c d)) :=
  (K.triple_mul a b c d).toEq

end AlgebraicKTheorySpectrum

/-! ## Motivic Adams Spectral Sequence -/

/-- Motivic Adams spectral sequence. -/
structure MotivicAdamsSS (E : Nat → Nat → Nat → Type u) where
  zero : ∀ s t w, E s t w
  differential : ∀ r s t w, E s t w → E (s + r) (t + r - 1) w
  d_squared : ∀ r s t w (x : E s t w),
    Path (differential r (s + r) (t + r - 1) w (differential r s t w x))
         (zero (s + 2*r) (t + 2*r - 2) w)
  convergence : ∀ s t w, E s t w  -- E^∞

namespace MotivicAdamsSS

variable {E : Nat → Nat → Nat → Type u} (MASS : MotivicAdamsSS E)

theorem d_squared_eq (r s t w : Nat) (x : E s t w) :
    MASS.differential r (s + r) (t + r - 1) w (MASS.differential r s t w x) =
    MASS.zero (s + 2*r) (t + 2*r - 2) w :=
  (MASS.d_squared r s t w x).toEq

end MotivicAdamsSS

/-! ## Eta-Periodic Phenomena -/

/-- Eta element and periodicity in motivic homotopy theory. -/
structure EtaPeriodic (E : Type u) where
  spectrum : MotivicSpectrum E
  eta : E  -- the element η in π_{1,1}
  mul_eta : E → E  -- multiplication by η
  eta_nilp : Nat  -- η^n = 0 for n ≥ nilp
  eta_periodic_part : E → E  -- η-periodic localization
  eta_complete_part : E → E  -- η-completion
  localize : E → E
  complete : E → E
  loc_comp : ∀ (e : E), Path (localize (complete e)) (eta_periodic_part e)
  comp_loc : ∀ (e : E), Path (complete (localize e)) (eta_complete_part e)
  mul_eta_shift : ∀ (e : E),
    Path (mul_eta e) (spectrum.shift_a (spectrum.shift_s e))  -- η shifts bidegree

namespace EtaPeriodic

variable {E : Type u} (EP : EtaPeriodic E)

theorem loc_comp_eq (e : E) : EP.localize (EP.complete e) = EP.eta_periodic_part e :=
  (EP.loc_comp e).toEq
theorem comp_loc_eq (e : E) : EP.complete (EP.localize e) = EP.eta_complete_part e :=
  (EP.comp_loc e).toEq
theorem mul_eta_shift_eq (e : E) :
    EP.mul_eta e = EP.spectrum.shift_a (EP.spectrum.shift_s e) :=
  (EP.mul_eta_shift e).toEq

end EtaPeriodic

/-! ## Motivic Steenrod Algebra -/

/-- The motivic Steenrod algebra. -/
structure MotivicSteenrod (A : Type u) where
  mul : A → A → A
  add : A → A → A
  zero : A
  one : A
  sq : Nat → A  -- Sq^i
  tau : A       -- τ element
  rho : A       -- ρ element
  mul_assoc : ∀ (a b c : A), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : A), Path (mul a one) a
  one_mul : ∀ (a : A), Path (mul one a) a
  add_assoc : ∀ (a b c : A), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : A), Path (add a b) (add b a)
  add_zero : ∀ (a : A), Path (add a zero) a
  left_distrib : ∀ (a b c : A), Path (mul a (add b c)) (add (mul a b) (mul a c))
  adem : ∀ (i j : Nat), i < 2 * j →
    Path (mul (sq i) (sq j)) (add (sq (i + j)) (mul (sq (i + j - 1)) (sq 1)))  -- simplified Adem

namespace MotivicSteenrod

variable {A : Type u} (MSt : MotivicSteenrod A)

theorem mul_assoc_eq (a b c : A) : MSt.mul (MSt.mul a b) c = MSt.mul a (MSt.mul b c) := (MSt.mul_assoc a b c).toEq
theorem mul_one_eq (a : A) : MSt.mul a MSt.one = a := (MSt.mul_one a).toEq
theorem one_mul_eq (a : A) : MSt.mul MSt.one a = a := (MSt.one_mul a).toEq
theorem add_assoc_eq (a b c : A) : MSt.add (MSt.add a b) c = MSt.add a (MSt.add b c) := (MSt.add_assoc a b c).toEq
theorem add_comm_eq (a b : A) : MSt.add a b = MSt.add b a := (MSt.add_comm a b).toEq
theorem add_zero_eq (a : A) : MSt.add a MSt.zero = a := (MSt.add_zero a).toEq

/-- Triple mul. -/
noncomputable def triple_mul (a b c d : A) :
    Path (MSt.mul (MSt.mul (MSt.mul a b) c) d) (MSt.mul a (MSt.mul b (MSt.mul c d))) :=
  Path.trans (MSt.mul_assoc (MSt.mul a b) c d) (MSt.mul_assoc a b (MSt.mul c d))

theorem triple_mul_eq (a b c d : A) :
    MSt.mul (MSt.mul (MSt.mul a b) c) d = MSt.mul a (MSt.mul b (MSt.mul c d)) := (MSt.triple_mul a b c d).toEq

/-- Unit absorbed. -/
noncomputable def one_mul_one (a : A) :
    Path (MSt.mul MSt.one (MSt.mul a MSt.one)) a :=
  Path.trans (MSt.one_mul (MSt.mul a MSt.one)) (MSt.mul_one a)

theorem one_mul_one_eq (a : A) : MSt.mul MSt.one (MSt.mul a MSt.one) = a := (MSt.one_mul_one a).toEq

end MotivicSteenrod

/-! ## Slice Filtration -/

/-- Slice filtration on motivic spectra. -/
structure SliceFiltration (E : Type u) where
  spectrum : MotivicSpectrum E
  slice : Nat → E → E  -- s_q(E)
  f_above : Nat → E → E  -- f^q(E) = part above slice q
  f_below : Nat → E → E  -- f_q(E) = part below
  cofiber_seq : ∀ q (e : E),
    Path (spectrum.wedge (f_above q e) (f_below q e)) e  -- fiber sequence
  slice_is_layer : ∀ q (e : E),
    Path (slice q e) (f_above q (f_below (q + 1) e))

namespace SliceFiltration

variable {E : Type u} (SF : SliceFiltration E)

theorem cofiber_seq_eq (q : Nat) (e : E) :
    SF.spectrum.wedge (SF.f_above q e) (SF.f_below q e) = e :=
  (SF.cofiber_seq q e).toEq

theorem slice_is_layer_eq (q : Nat) (e : E) :
    SF.slice q e = SF.f_above q (SF.f_below (q + 1) e) :=
  (SF.slice_is_layer q e).toEq

end SliceFiltration

end Algebra
end Path
end ComputationalPaths
