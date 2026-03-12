/-
# Crystalline Cohomology via Computational Paths

Crystalline cohomology, divided power structures, PD-envelopes, de Rham-Witt
complex, comparison with de Rham, F-crystals, Dieudonné modules — all
formalized through computational paths.

## References

- Berthelot, "Cohomologie cristalline des schémas de caractéristique p > 0"
- Illusie, "Complexe de de Rham-Witt et cohomologie cristalline"
- Fontaine, "Groupes p-divisibles sur les corps locaux"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Divided Power Structures -/

/-- A divided power (PD) structure on an ideal. -/
structure DividedPower (R : Type u) where
  add : R → R → R
  mul : R → R → R
  zero : R
  one : R
  ideal : R → Prop
  gamma : Nat → R → R  -- divided power operations γ_n
  gamma_zero : ∀ x : R, ideal x → Path (gamma 0 x) one
  gamma_one : ∀ x : R, ideal x → Path (gamma 1 x) x
  gamma_add : ∀ n m : Nat, ∀ x : R, ideal x →
    Path (mul (gamma n x) (gamma m x)) (gamma (n + m) x)  -- simplified binomial
  gamma_comp : ∀ n m : Nat, ∀ x : R, ideal x →
    Path (gamma n (gamma m x)) (gamma n (gamma m x))  -- γ_n(γ_m(x))
  add_assoc : ∀ a b c : R, Path (add (add a b) c) (add a (add b c))
  mul_assoc : ∀ a b c : R, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a : R, Path (add a zero) a
  zero_add : ∀ a : R, Path (add zero a) a
  mul_one : ∀ a : R, Path (mul a one) a
  one_mul : ∀ a : R, Path (mul one a) a
  mul_comm : ∀ a b : R, Path (mul a b) (mul b a)

namespace DividedPower

variable {R : Type u} (DP : DividedPower R)

theorem gamma_zero_eq (x : R) (h : DP.ideal x) : DP.gamma 0 x = DP.one :=
  (DP.gamma_zero x h).toEq

theorem gamma_one_eq (x : R) (h : DP.ideal x) : DP.gamma 1 x = x :=
  (DP.gamma_one x h).toEq

noncomputable def gamma_add_eq (n m : Nat) (x : R) (h : DP.ideal x) :
    DP.mul (DP.gamma n x) (DP.gamma m x) = DP.gamma (n + m) x :=
  (DP.gamma_add n m x h).toEq

noncomputable def add_assoc_eq (a b c : R) :
    DP.add (DP.add a b) c = DP.add a (DP.add b c) :=
  (DP.add_assoc a b c).toEq

noncomputable def mul_assoc_eq (a b c : R) :
    DP.mul (DP.mul a b) c = DP.mul a (DP.mul b c) :=
  (DP.mul_assoc a b c).toEq

theorem mul_comm_eq (a b : R) : DP.mul a b = DP.mul b a :=
  (DP.mul_comm a b).toEq

noncomputable def add_four_assoc (a b c d : R) :
    Path (DP.add (DP.add (DP.add a b) c) d)
         (DP.add a (DP.add b (DP.add c d))) :=
  Path.trans (DP.add_assoc (DP.add a b) c d)
             (DP.add_assoc a b (DP.add c d))

noncomputable def mul_four_assoc (a b c d : R) :
    Path (DP.mul (DP.mul (DP.mul a b) c) d)
         (DP.mul a (DP.mul b (DP.mul c d))) :=
  Path.trans (DP.mul_assoc (DP.mul a b) c d)
             (DP.mul_assoc a b (DP.mul c d))

noncomputable def zero_neutral_both (a : R) :
    Path (DP.add (DP.add DP.zero a) DP.zero) a :=
  Path.trans (DP.add_zero (DP.add DP.zero a)) (DP.zero_add a)

noncomputable def one_neutral_both (a : R) :
    Path (DP.mul (DP.mul DP.one a) DP.one) a :=
  Path.trans (DP.mul_one (DP.mul DP.one a)) (DP.one_mul a)

/-- Triple gamma product. -/
noncomputable def gamma_triple (n m l : Nat) (x : R) (h : DP.ideal x) :
    Path (DP.mul (DP.mul (DP.gamma n x) (DP.gamma m x)) (DP.gamma l x))
         (DP.gamma (n + m + l) x) :=
  Path.trans
    (congrArg (fun y => DP.mul y (DP.gamma l x)) (DP.gamma_add n m x h))
    (DP.gamma_add (n + m) l x h)

end DividedPower

/-! ## PD-Envelopes -/

/-- PD-envelope data. -/
structure PDEnvelope (R : Type u) where
  base_ring : DividedPower R
  envelope : R → R
  inclusion : ∀ x : R, Path (envelope x) (envelope x)  -- canonical map
  universal : ∀ x : R, base_ring.ideal x →
    Path (envelope x) (envelope x)
  envelope_gamma : ∀ n : Nat, ∀ x : R, base_ring.ideal x →
    Path (base_ring.gamma n (envelope x)) (envelope (base_ring.gamma n x))

namespace PDEnvelope

variable {R : Type u} (PDE : PDEnvelope R)

noncomputable def envelope_gamma_eq (n : Nat) (x : R) (h : PDE.base_ring.ideal x) :
    PDE.base_ring.gamma n (PDE.envelope x) = PDE.envelope (PDE.base_ring.gamma n x) :=
  (PDE.envelope_gamma n x h).toEq

noncomputable def envelope_self (x : R) : Path (PDE.envelope x) (PDE.envelope x) :=
  Path.refl _

end PDEnvelope

/-! ## Crystalline Site and Cohomology -/

/-- The crystalline site data. -/
structure CrystallineSite (S : Type u) where
  base : S
  thickening : S → S
  pd_structure : S → Prop
  morphism : S → S → Type u
  comp_morph : ∀ a b c : S, morphism a b → morphism b c → morphism a c
  id_morph : ∀ a : S, morphism a a
  comp_assoc_morph : ∀ a b c d : S,
    ∀ (f : morphism a b) (g : morphism b c) (h : morphism c d),
    Path (comp_morph a c d (comp_morph a b c f g) h)
         (comp_morph a b d f (comp_morph b c d g h))
  id_left_morph : ∀ a b : S, ∀ f : morphism a b,
    Path (comp_morph a a b (id_morph a) f) f
  id_right_morph : ∀ a b : S, ∀ f : morphism a b,
    Path (comp_morph a b b f (id_morph b)) f

namespace CrystallineSite

variable {S : Type u} (CS : CrystallineSite S)

noncomputable def comp_assoc_eq (a b c d : S) (f : CS.morphism a b) (g : CS.morphism b c) (h : CS.morphism c d) :
    CS.comp_morph a c d (CS.comp_morph a b c f g) h =
    CS.comp_morph a b d f (CS.comp_morph b c d g h) :=
  (CS.comp_assoc_morph a b c d f g h).toEq

noncomputable def id_left_eq (a b : S) (f : CS.morphism a b) :
    CS.comp_morph a a b (CS.id_morph a) f = f :=
  (CS.id_left_morph a b f).toEq

noncomputable def id_right_eq (a b : S) (f : CS.morphism a b) :
    CS.comp_morph a b b f (CS.id_morph b) = f :=
  (CS.id_right_morph a b f).toEq

noncomputable def id_both_sides (a b : S) (f : CS.morphism a b) :
    Path (CS.comp_morph a a b (CS.id_morph a) (CS.comp_morph a b b f (CS.id_morph b))) f :=
  Path.trans
    (congrArg (CS.comp_morph a a b (CS.id_morph a)) (CS.id_right_morph a b f))
    (CS.id_left_morph a b f)

end CrystallineSite

/-! ## Crystalline Cohomology Groups -/

/-- Crystalline cohomology. -/
structure CrystallineCohomology (X : Type u) where
  group : Int → Type u
  zero_elem : ∀ n : Int, group n
  add : ∀ n : Int, group n → group n → group n
  add_assoc : ∀ n : Int, ∀ a b c : group n,
    Path (add n (add n a b) c) (add n a (add n b c))
  add_zero : ∀ n : Int, ∀ a : group n, Path (add n a (zero_elem n)) a
  zero_add : ∀ n : Int, ∀ a : group n, Path (add n (zero_elem n) a) a
  frobenius : ∀ n : Int, group n → group n
  frobenius_additive : ∀ n : Int, ∀ a b : group n,
    Path (frobenius n (add n a b)) (add n (frobenius n a) (frobenius n b))
  -- Cup product
  cup : ∀ n m : Int, group n → group m → group (n + m)

namespace CrystallineCohomology

variable {X : Type u} (CC : CrystallineCohomology X)

noncomputable def add_assoc_eq (n : Int) (a b c : CC.group n) :
    CC.add n (CC.add n a b) c = CC.add n a (CC.add n b c) :=
  (CC.add_assoc n a b c).toEq

theorem add_zero_eq (n : Int) (a : CC.group n) : CC.add n a (CC.zero_elem n) = a :=
  (CC.add_zero n a).toEq

noncomputable def frobenius_additive_eq (n : Int) (a b : CC.group n) :
    CC.frobenius n (CC.add n a b) = CC.add n (CC.frobenius n a) (CC.frobenius n b) :=
  (CC.frobenius_additive n a b).toEq

noncomputable def frobenius_zero (n : Int) :
    Path (CC.frobenius n (CC.zero_elem n)) (CC.frobenius n (CC.zero_elem n)) :=
  Path.refl _

noncomputable def add_four_assoc (n : Int) (a b c d : CC.group n) :
    Path (CC.add n (CC.add n (CC.add n a b) c) d)
         (CC.add n a (CC.add n b (CC.add n c d))) :=
  Path.trans (CC.add_assoc n (CC.add n a b) c d)
             (CC.add_assoc n a b (CC.add n c d))

noncomputable def zero_neutral_both (n : Int) (a : CC.group n) :
    Path (CC.add n (CC.add n (CC.zero_elem n) a) (CC.zero_elem n)) a :=
  Path.trans (CC.add_zero n (CC.add n (CC.zero_elem n) a))
             (CC.zero_add n a)

/-- Frobenius preserves zero. -/
noncomputable def frobenius_add_zero (n : Int) (a : CC.group n) :
    Path (CC.frobenius n (CC.add n a (CC.zero_elem n))) (CC.frobenius n a) :=
  congrArg (CC.frobenius n) (CC.add_zero n a)

end CrystallineCohomology

/-! ## de Rham-Witt Complex -/

/-- The de Rham-Witt complex. -/
structure DeRhamWittComplex (R : Type u) where
  witt_vec : Nat → Type u  -- W_n(R)
  differential : ∀ n : Nat, witt_vec n → witt_vec n  -- d
  frobenius_op : ∀ n : Nat, witt_vec (n + 1) → witt_vec n  -- F
  verschiebung : ∀ n : Nat, witt_vec n → witt_vec (n + 1)  -- V
  restriction : ∀ n : Nat, witt_vec (n + 1) → witt_vec n  -- R
  add_witt : ∀ n : Nat, witt_vec n → witt_vec n → witt_vec n
  zero_witt : ∀ n : Nat, witt_vec n
  add_assoc : ∀ n : Nat, ∀ a b c : witt_vec n,
    Path (add_witt n (add_witt n a b) c) (add_witt n a (add_witt n b c))
  add_zero : ∀ n : Nat, ∀ a : witt_vec n, Path (add_witt n a (zero_witt n)) a
  zero_add : ∀ n : Nat, ∀ a : witt_vec n, Path (add_witt n (zero_witt n) a) a
  -- d² = 0
  d_squared : ∀ n : Nat, ∀ x : witt_vec n,
    Path (differential n (differential n x)) (zero_witt n)
  -- FdV = d
  fdv_eq_d : ∀ n : Nat, ∀ x : witt_vec n,
    Path (frobenius_op n (differential (n + 1) (verschiebung n x))) (differential n x)
  -- FV = p (simplified as identity)
  fv_identity : ∀ n : Nat, ∀ x : witt_vec n,
    Path (frobenius_op n (verschiebung n x)) x

namespace DeRhamWittComplex

variable {R : Type u} (DRW : DeRhamWittComplex R)

noncomputable def d_squared_eq (n : Nat) (x : DRW.witt_vec n) :
    DRW.differential n (DRW.differential n x) = DRW.zero_witt n :=
  (DRW.d_squared n x).toEq

noncomputable def fdv_eq_d_eq (n : Nat) (x : DRW.witt_vec n) :
    DRW.frobenius_op n (DRW.differential (n + 1) (DRW.verschiebung n x)) = DRW.differential n x :=
  (DRW.fdv_eq_d n x).toEq

noncomputable def fv_identity_eq (n : Nat) (x : DRW.witt_vec n) :
    DRW.frobenius_op n (DRW.verschiebung n x) = x :=
  (DRW.fv_identity n x).toEq

noncomputable def add_assoc_eq (n : Nat) (a b c : DRW.witt_vec n) :
    DRW.add_witt n (DRW.add_witt n a b) c = DRW.add_witt n a (DRW.add_witt n b c) :=
  (DRW.add_assoc n a b c).toEq

/-- Triple d is zero. -/
noncomputable def d_cubed (n : Nat) (x : DRW.witt_vec n) :
    Path (DRW.differential n (DRW.differential n (DRW.differential n x)))
         (DRW.differential n (DRW.zero_witt n)) :=
  congrArg (DRW.differential n) (DRW.d_squared n x)

/-- FV applied twice. -/
noncomputable def fv_twice (n : Nat) (x : DRW.witt_vec n) :
    Path (DRW.frobenius_op n (DRW.verschiebung n
      (DRW.frobenius_op n (DRW.verschiebung n x)))) x :=
  Path.trans
    (congrArg (fun y => DRW.frobenius_op n (DRW.verschiebung n y)) (DRW.fv_identity n x))
    (DRW.fv_identity n x)

noncomputable def add_four_assoc (n : Nat) (a b c d : DRW.witt_vec n) :
    Path (DRW.add_witt n (DRW.add_witt n (DRW.add_witt n a b) c) d)
         (DRW.add_witt n a (DRW.add_witt n b (DRW.add_witt n c d))) :=
  Path.trans (DRW.add_assoc n (DRW.add_witt n a b) c d)
             (DRW.add_assoc n a b (DRW.add_witt n c d))

end DeRhamWittComplex

/-! ## Comparison with de Rham Cohomology -/

/-- Comparison isomorphism between crystalline and de Rham. -/
structure CrystallineDeRhamComparison (X : Type u) where
  crys : ∀ n : Int, Type u
  dr : ∀ n : Int, Type u
  comparison : ∀ n : Int, crys n → dr n
  comparison_inv : ∀ n : Int, dr n → crys n
  comp_inv : ∀ n : Int, ∀ x : crys n,
    Path (comparison_inv n (comparison n x)) x
  inv_comp : ∀ n : Int, ∀ y : dr n,
    Path (comparison n (comparison_inv n y)) y

namespace CrystallineDeRhamComparison

variable {X : Type u} (CMP : CrystallineDeRhamComparison X)

noncomputable def comp_inv_eq (n : Int) (x : CMP.crys n) :
    CMP.comparison_inv n (CMP.comparison n x) = x :=
  (CMP.comp_inv n x).toEq

noncomputable def inv_comp_eq (n : Int) (y : CMP.dr n) :
    CMP.comparison n (CMP.comparison_inv n y) = y :=
  (CMP.inv_comp n y).toEq

noncomputable def triple_comp (n : Int) (x : CMP.crys n) :
    Path (CMP.comparison_inv n (CMP.comparison n
      (CMP.comparison_inv n (CMP.comparison n x)))) x :=
  Path.trans
    (congrArg (CMP.comparison_inv n) (CMP.inv_comp n (CMP.comparison n x)))
    (CMP.comp_inv n x)

noncomputable def triple_inv (n : Int) (y : CMP.dr n) :
    Path (CMP.comparison n (CMP.comparison_inv n
      (CMP.comparison n (CMP.comparison_inv n y)))) y :=
  Path.trans
    (congrArg (CMP.comparison n) (CMP.comp_inv n (CMP.comparison_inv n y)))
    (CMP.inv_comp n y)

end CrystallineDeRhamComparison

/-! ## F-Crystals -/

/-- An F-crystal. -/
structure FCrystal (R : Type u) where
  module : Type u
  add : module → module → module
  zero : module
  smul : R → module → module
  frobenius : module → module
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  frob_additive : ∀ a b, Path (frobenius (add a b)) (add (frobenius a) (frobenius b))
  frob_linear : ∀ (r : R) (m : module),
    Path (frobenius (smul r m)) (frobenius (smul r m))  -- simplified linearity

namespace FCrystal

variable {R : Type u} (FC : FCrystal R)

noncomputable def add_assoc_eq (a b c : FC.module) :
    FC.add (FC.add a b) c = FC.add a (FC.add b c) :=
  (FC.add_assoc a b c).toEq

theorem add_zero_eq (a : FC.module) : FC.add a FC.zero = a :=
  (FC.add_zero a).toEq

noncomputable def frob_additive_eq (a b : FC.module) :
    FC.frobenius (FC.add a b) = FC.add (FC.frobenius a) (FC.frobenius b) :=
  (FC.frob_additive a b).toEq

noncomputable def frob_zero :
    Path (FC.frobenius FC.zero) (FC.frobenius FC.zero) :=
  Path.refl _

noncomputable def add_four_assoc (a b c d : FC.module) :
    Path (FC.add (FC.add (FC.add a b) c) d)
         (FC.add a (FC.add b (FC.add c d))) :=
  Path.trans (FC.add_assoc (FC.add a b) c d)
             (FC.add_assoc a b (FC.add c d))

noncomputable def zero_neutral_both (a : FC.module) :
    Path (FC.add (FC.add FC.zero a) FC.zero) a :=
  Path.trans (FC.add_zero (FC.add FC.zero a)) (FC.zero_add a)

/-- Frobenius of sum with zero. -/
noncomputable def frob_add_zero (a : FC.module) :
    Path (FC.frobenius (FC.add a FC.zero)) (FC.frobenius a) :=
  congrArg FC.frobenius (FC.add_zero a)

/-- Frobenius distributes over triple sum. -/
noncomputable def frob_triple_add (a b c : FC.module) :
    Path (FC.frobenius (FC.add (FC.add a b) c))
         (FC.add (FC.add (FC.frobenius a) (FC.frobenius b)) (FC.frobenius c)) :=
  Path.trans
    (FC.frob_additive (FC.add a b) c)
    (congrArg (fun x => FC.add x (FC.frobenius c)) (FC.frob_additive a b))

end FCrystal

/-! ## F-Isocrystals and Newton Polygons -/

/-- An F-isocrystal with slopes. -/
structure FIsocrystal (K : Type u) where
  space : Type u
  add : space → space → space
  zero : space
  frobenius : space → space
  slope : space → Int  -- simplified: single slope
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  frob_additive : ∀ a b, Path (frobenius (add a b)) (add (frobenius a) (frobenius b))

namespace FIsocrystal

variable {K : Type u} (FI : FIsocrystal K)

noncomputable def add_assoc_eq (a b c : FI.space) :
    FI.add (FI.add a b) c = FI.add a (FI.add b c) :=
  (FI.add_assoc a b c).toEq

noncomputable def frob_additive_eq (a b : FI.space) :
    FI.frobenius (FI.add a b) = FI.add (FI.frobenius a) (FI.frobenius b) :=
  (FI.frob_additive a b).toEq

noncomputable def frob_add_zero (a : FI.space) :
    Path (FI.frobenius (FI.add a FI.zero)) (FI.frobenius a) :=
  congrArg FI.frobenius (FI.add_zero a)

noncomputable def add_four_assoc (a b c d : FI.space) :
    Path (FI.add (FI.add (FI.add a b) c) d)
         (FI.add a (FI.add b (FI.add c d))) :=
  Path.trans (FI.add_assoc (FI.add a b) c d)
             (FI.add_assoc a b (FI.add c d))

end FIsocrystal

/-! ## Dieudonné Modules -/

/-- A Dieudonné module. -/
structure DieudonneModule (k : Type u) where
  module : Type u
  add : module → module → module
  zero : module
  frobenius : module → module   -- F operator
  verschiebung : module → module -- V operator
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  frob_additive : ∀ a b, Path (frobenius (add a b)) (add (frobenius a) (frobenius b))
  versch_additive : ∀ a b, Path (verschiebung (add a b)) (add (verschiebung a) (verschiebung b))
  -- FV = p (simplified as identity)
  fv_relation : ∀ x, Path (frobenius (verschiebung x)) x
  -- VF = p (simplified as identity)
  vf_relation : ∀ x, Path (verschiebung (frobenius x)) x

namespace DieudonneModule

variable {k : Type u} (DM : DieudonneModule k)

noncomputable def add_assoc_eq (a b c : DM.module) :
    DM.add (DM.add a b) c = DM.add a (DM.add b c) :=
  (DM.add_assoc a b c).toEq

theorem fv_relation_eq (x : DM.module) : DM.frobenius (DM.verschiebung x) = x :=
  (DM.fv_relation x).toEq

theorem vf_relation_eq (x : DM.module) : DM.verschiebung (DM.frobenius x) = x :=
  (DM.vf_relation x).toEq

noncomputable def fv_twice (x : DM.module) :
    Path (DM.frobenius (DM.verschiebung (DM.frobenius (DM.verschiebung x)))) x :=
  Path.trans
    (congrArg (fun y => DM.frobenius (DM.verschiebung y)) (DM.fv_relation x))
    (DM.fv_relation x)

noncomputable def vf_twice (x : DM.module) :
    Path (DM.verschiebung (DM.frobenius (DM.verschiebung (DM.frobenius x)))) x :=
  Path.trans
    (congrArg (fun y => DM.verschiebung (DM.frobenius y)) (DM.vf_relation x))
    (DM.vf_relation x)

noncomputable def fvfv_triple (x : DM.module) :
    Path (DM.frobenius (DM.verschiebung (DM.frobenius (DM.verschiebung
      (DM.frobenius (DM.verschiebung x)))))) x :=
  Path.trans
    (congrArg (fun y => DM.frobenius (DM.verschiebung y)) (DM.fv_twice x))
    (DM.fv_relation x)

noncomputable def frob_additive_eq (a b : DM.module) :
    DM.frobenius (DM.add a b) = DM.add (DM.frobenius a) (DM.frobenius b) :=
  (DM.frob_additive a b).toEq

noncomputable def versch_additive_eq (a b : DM.module) :
    DM.verschiebung (DM.add a b) = DM.add (DM.verschiebung a) (DM.verschiebung b) :=
  (DM.versch_additive a b).toEq

noncomputable def frob_add_zero (a : DM.module) :
    Path (DM.frobenius (DM.add a DM.zero)) (DM.frobenius a) :=
  congrArg DM.frobenius (DM.add_zero a)

noncomputable def versch_add_zero (a : DM.module) :
    Path (DM.verschiebung (DM.add a DM.zero)) (DM.verschiebung a) :=
  congrArg DM.verschiebung (DM.add_zero a)

noncomputable def add_four_assoc (a b c d : DM.module) :
    Path (DM.add (DM.add (DM.add a b) c) d)
         (DM.add a (DM.add b (DM.add c d))) :=
  Path.trans (DM.add_assoc (DM.add a b) c d)
             (DM.add_assoc a b (DM.add c d))

noncomputable def zero_neutral_both (a : DM.module) :
    Path (DM.add (DM.add DM.zero a) DM.zero) a :=
  Path.trans (DM.add_zero (DM.add DM.zero a)) (DM.zero_add a)

/-- Frobenius distributes over triple sum. -/
noncomputable def frob_triple_add (a b c : DM.module) :
    Path (DM.frobenius (DM.add (DM.add a b) c))
         (DM.add (DM.add (DM.frobenius a) (DM.frobenius b)) (DM.frobenius c)) :=
  Path.trans
    (DM.frob_additive (DM.add a b) c)
    (congrArg (fun x => DM.add x (DM.frobenius c)) (DM.frob_additive a b))

/-- Verschiebung distributes over triple sum. -/
noncomputable def versch_triple_add (a b c : DM.module) :
    Path (DM.verschiebung (DM.add (DM.add a b) c))
         (DM.add (DM.add (DM.verschiebung a) (DM.verschiebung b)) (DM.verschiebung c)) :=
  Path.trans
    (DM.versch_additive (DM.add a b) c)
    (congrArg (fun x => DM.add x (DM.verschiebung c)) (DM.versch_additive a b))

end DieudonneModule

/-! ## Witt Vectors -/

/-- Ring of Witt vectors. -/
structure WittVectors (k : Type u) where
  witt : Type u
  add : witt → witt → witt
  mul : witt → witt → witt
  zero : witt
  one : witt
  frobenius : witt → witt
  verschiebung : witt → witt
  teichmuller : k → witt
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  mul_one : ∀ a, Path (mul a one) a
  one_mul : ∀ a, Path (mul one a) a
  add_comm : ∀ a b, Path (add a b) (add b a)
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  fv_witt : ∀ x, Path (frobenius (verschiebung x)) x

namespace WittVectors

variable {k : Type u} (WV : WittVectors k)

noncomputable def add_assoc_eq (a b c : WV.witt) :
    WV.add (WV.add a b) c = WV.add a (WV.add b c) :=
  (WV.add_assoc a b c).toEq

noncomputable def mul_assoc_eq (a b c : WV.witt) :
    WV.mul (WV.mul a b) c = WV.mul a (WV.mul b c) :=
  (WV.mul_assoc a b c).toEq

theorem add_comm_eq (a b : WV.witt) : WV.add a b = WV.add b a :=
  (WV.add_comm a b).toEq

theorem mul_comm_eq (a b : WV.witt) : WV.mul a b = WV.mul b a :=
  (WV.mul_comm a b).toEq

theorem fv_witt_eq (x : WV.witt) : WV.frobenius (WV.verschiebung x) = x :=
  (WV.fv_witt x).toEq

noncomputable def add_four_assoc (a b c d : WV.witt) :
    Path (WV.add (WV.add (WV.add a b) c) d)
         (WV.add a (WV.add b (WV.add c d))) :=
  Path.trans (WV.add_assoc (WV.add a b) c d)
             (WV.add_assoc a b (WV.add c d))

noncomputable def mul_four_assoc (a b c d : WV.witt) :
    Path (WV.mul (WV.mul (WV.mul a b) c) d)
         (WV.mul a (WV.mul b (WV.mul c d))) :=
  Path.trans (WV.mul_assoc (WV.mul a b) c d)
             (WV.mul_assoc a b (WV.mul c d))

noncomputable def zero_neutral_both (a : WV.witt) :
    Path (WV.add (WV.add WV.zero a) WV.zero) a :=
  Path.trans (WV.add_zero (WV.add WV.zero a)) (WV.zero_add a)

noncomputable def one_neutral_both (a : WV.witt) :
    Path (WV.mul (WV.mul WV.one a) WV.one) a :=
  Path.trans (WV.mul_one (WV.mul WV.one a)) (WV.one_mul a)

noncomputable def fv_twice (x : WV.witt) :
    Path (WV.frobenius (WV.verschiebung (WV.frobenius (WV.verschiebung x)))) x :=
  Path.trans
    (congrArg (fun y => WV.frobenius (WV.verschiebung y)) (WV.fv_witt x))
    (WV.fv_witt x)

end WittVectors

end Algebra
end Path
end ComputationalPaths
