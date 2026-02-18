/-
# Deep Homological Algebra Paths: Advanced Topics

Triangulated categories, t-structures, Serre duality, Grothendieck duality,
Verdier quotient, tilting theory, Hochschild cohomology, derived tensor/RHom,
Grothendieck groups, perverse sheaves, dualizing complexes, Euler characteristic,
homotopy categories — all via computational paths.
-/

import ComputationalPaths.Homological.PathInfrastructure

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace HomologicalDeep

open Path Homological

universe u v w

/-! ## Triangulated Category Structure -/

/-- Triangulated category data. -/
structure TriangulatedData (A : Type u) where
  shift : A → A
  shiftInv : A → A
  shiftInvPath : ∀ x : A, Path (shift (shiftInv x)) x
  invShiftPath : ∀ x : A, Path (shiftInv (shift x)) x

namespace TriangulatedData

variable {A : Type u} (Tr : TriangulatedData A)

/-- Shift is an equivalence. -/
def shift_equiv (x : A) : Path (Tr.shift (Tr.shiftInv x)) x :=
  Tr.shiftInvPath x

/-- Double shift roundtrip. -/
def double_shift_roundtrip (x : A) :
    Path (Tr.shiftInv (Tr.shift (Tr.shiftInv (Tr.shift x)))) x :=
  Path.trans
    (Path.congrArg Tr.shiftInv (Tr.shiftInvPath (Tr.shift x)))
    (Tr.invShiftPath x)

/-- Shift roundtrip coherence. -/
theorem shift_roundtrip_rweq (x : A) :
    RwEq
      (Path.trans (Tr.shiftInvPath x) (Path.refl _))
      (Tr.shiftInvPath x) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Inverse shift roundtrip coherence. -/
theorem inv_shift_roundtrip_rweq (x : A) :
    RwEq
      (Path.trans (Tr.invShiftPath x) (Path.refl _))
      (Tr.invShiftPath x) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Shift-unshift cancellation via RwEq. -/
theorem shift_cancel_rweq (x : A) :
    RwEq
      (Path.trans (Tr.shiftInvPath x) (Path.symm (Tr.shiftInvPath x)))
      (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel _)

end TriangulatedData

/-! ## t-Structure -/

/-- t-structure on a triangulated category. -/
structure TStructureData (A : Type u) where
  leZero : A → Prop
  geZero : A → Prop
  tauLeq : A → A
  tauGeq : A → A
  tauLeqIdPath : ∀ x : A, leZero x → Path (tauLeq x) x
  tauGeqIdPath : ∀ x : A, geZero x → Path (tauGeq x) x
  heart : A → Prop
  heartPath : ∀ x : A, heart x ↔ (leZero x ∧ geZero x)

namespace TStructureData

variable {A : Type u} (T : TStructureData A)

/-- Heart objects are fixed by τ≤0. -/
def heart_fixed_leq (x : A) (hx : T.heart x) :
    Path (T.tauLeq x) x :=
  T.tauLeqIdPath x ((T.heartPath x).mp hx).1

/-- Heart objects are fixed by τ≥0. -/
def heart_fixed_geq (x : A) (hx : T.heart x) :
    Path (T.tauGeq x) x :=
  T.tauGeqIdPath x ((T.heartPath x).mp hx).2

/-- Heart truncation is idempotent on heart objects. -/
def heart_idemp (x : A) (hx : T.heart x)
    (hleq : T.leZero (T.tauLeq x)) :
    Path (T.tauLeq (T.tauLeq x)) x :=
  Path.trans (T.tauLeqIdPath (T.tauLeq x) hleq) (T.tauLeqIdPath x ((T.heartPath x).mp hx).1)

end TStructureData

/-! ## Serre Duality -/

/-- Serre duality data. -/
structure SerreDualityData (A : Type u) where
  dim : Nat
  omega : A
  ext : Nat → A → A → A
  dual : A → A
  tensorOmega : A → A
  serrePath : ∀ (i : Nat) (f g : A),
    Path (ext i f g) (dual (ext (dim - i) g (tensorOmega f)))

namespace SerreDualityData

variable {A : Type u} (S : SerreDualityData A)

/-- Serre duality at degree i. -/
def serre_dual (i : Nat) (f g : A) :
    Path (S.ext i f g) (S.dual (S.ext (S.dim - i) g (S.tensorOmega f))) :=
  S.serrePath i f g

/-- Serre duality at top degree. -/
def serre_top (f : A) :
    Path (S.ext S.dim f S.omega) (S.dual (S.ext (S.dim - S.dim) S.omega (S.tensorOmega f))) :=
  S.serrePath S.dim f S.omega

/-- Serre duality at degree 0. -/
def serre_bottom (f g : A) :
    Path (S.ext 0 f g) (S.dual (S.ext (S.dim - 0) g (S.tensorOmega f))) :=
  S.serrePath 0 f g

/-- Serre duality coherence. -/
theorem serre_rweq (i : Nat) (f g : A) :
    RwEq
      (Path.trans (S.serrePath i f g) (Path.refl _))
      (S.serrePath i f g) :=
  rweq_of_hom_step (HomStep.right_unit _)

end SerreDualityData

/-! ## Verdier Quotient -/

/-- Verdier quotient data. -/
structure VerdierQuotientData (A : Type u) where
  zero : A
  inThick : A → Prop
  quotient : A → A
  quotientThickPath : ∀ x : A, inThick x → Path (quotient x) zero

namespace VerdierQuotientData

variable {A : Type u} (V : VerdierQuotientData A)

def quotient_kills_thick (x : A) (hx : V.inThick x) :
    Path (V.quotient x) V.zero :=
  V.quotientThickPath x hx

end VerdierQuotientData

/-! ## Tilting Theory -/

/-- Tilting object data. -/
structure TiltingData (A : Type u) where
  tiltObj : A
  derivedEquiv : A → A
  derivedEquivInv : A → A
  equivRoundtrip1 : ∀ x : A, Path (derivedEquiv (derivedEquivInv x)) x
  equivRoundtrip2 : ∀ x : A, Path (derivedEquivInv (derivedEquiv x)) x

namespace TiltingData

variable {A : Type u} (T : TiltingData A)

/-- Derived equivalence roundtrip. -/
def tilting_roundtrip (x : A) :
    Path (T.derivedEquiv (T.derivedEquivInv x)) x :=
  T.equivRoundtrip1 x

/-- Inverse roundtrip. -/
def tilting_inv_roundtrip (x : A) :
    Path (T.derivedEquivInv (T.derivedEquiv x)) x :=
  T.equivRoundtrip2 x

/-- Tilting roundtrip coherence. -/
theorem tilting_roundtrip_rweq (x : A) :
    RwEq
      (Path.trans (T.equivRoundtrip1 x) (Path.refl _))
      (T.equivRoundtrip1 x) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Double roundtrip via two applications of equivRoundtrip. -/
def tilting_double_roundtrip (x : A) :
    Path (T.derivedEquiv (T.derivedEquivInv (T.derivedEquiv (T.derivedEquivInv x)))) x :=
  Path.trans
    (Path.congrArg T.derivedEquiv (T.equivRoundtrip2 (T.derivedEquivInv x)))
    (T.equivRoundtrip1 x)

/-- Tilting cancellation via RwEq. -/
theorem tilting_cancel_rweq (x : A) :
    RwEq
      (Path.trans (T.equivRoundtrip1 x) (Path.symm (T.equivRoundtrip1 x)))
      (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel _)

end TiltingData

/-! ## Grothendieck Group K_0 -/

/-- K_0 of an abelian category. -/
structure K0Data (A : Type u) where
  classOf : A → A
  add : A → A → A
  zero : A
  /-- [B] = [A] + [C] from a SES -/
  sesRelPath : ∀ (a b c : A),
    Path (classOf b) (add (classOf a) (classOf c))
  addCommPath : ∀ x y : A, Path (add x y) (add y x)
  addAssocPath : ∀ x y z : A, Path (add (add x y) z) (add x (add y z))
  addZeroPath : ∀ x : A, Path (add x zero) x

namespace K0Data

variable {A : Type u} (K : K0Data A)

/-- SES relation in K_0. -/
def k0_ses (a b c : A) :
    Path (K.classOf b) (K.add (K.classOf a) (K.classOf c)) :=
  K.sesRelPath a b c

/-- K_0 commutativity. -/
def k0_comm (x y : A) : Path (K.add x y) (K.add y x) :=
  K.addCommPath x y

/-- K_0 associativity. -/
def k0_assoc (x y z : A) :
    Path (K.add (K.add x y) z) (K.add x (K.add y z)) :=
  K.addAssocPath x y z

/-- K_0 zero identity. -/
def k0_zero (x : A) : Path (K.add x K.zero) x :=
  K.addZeroPath x

/-- K_0 assoc coherence. -/
theorem k0_assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (K.addAssocPath x y z) (Path.refl _))
      (K.addAssocPath x y z) :=
  rweq_of_hom_step (HomStep.right_unit _)

end K0Data

/-! ## Hochschild Cohomology -/

/-- Hochschild cohomology data. -/
structure HochschildData (A : Type u) where
  alg : A
  bimod : A
  hh : Nat → A
  hh0Path : Path (hh 0) alg
  hh1Path : Path (hh 1) bimod
  cup : Nat → Nat → A → A → A
  cupAssocPath : ∀ (p q r : Nat) (x y z : A),
    Path (cup p (q + r) x (cup q r y z))
         (cup (p + q) r (cup p q x y) z)
  cupCommPath : ∀ (p q : Nat) (x y : A),
    Path (cup p q x y) (cup q p y x)

namespace HochschildData

variable {A : Type u} (H : HochschildData A)

/-- HH^0 is the center. -/
def hh_zero_center : Path (H.hh 0) H.alg := H.hh0Path

/-- HH^1 is outer derivations. -/
def hh_one_deriv : Path (H.hh 1) H.bimod := H.hh1Path

/-- Cup product associativity. -/
def cup_assoc (p q r : Nat) (x y z : A) :
    Path (H.cup p (q + r) x (H.cup q r y z))
         (H.cup (p + q) r (H.cup p q x y) z) :=
  H.cupAssocPath p q r x y z

/-- Cup product commutativity. -/
def cup_comm (p q : Nat) (x y : A) :
    Path (H.cup p q x y) (H.cup q p y x) :=
  H.cupCommPath p q x y

/-- Cup assoc coherence. -/
theorem cup_assoc_rweq (p q r : Nat) (x y z : A) :
    RwEq
      (Path.trans (H.cupAssocPath p q r x y z) (Path.refl _))
      (H.cupAssocPath p q r x y z) :=
  rweq_of_hom_step (HomStep.right_unit _)

end HochschildData

/-! ## Derived Tensor Product -/

/-- Derived tensor product ⊗^L. -/
structure DerivedTensorData (A : Type u) where
  tensorL : Nat → A → A → A
  assocPath : ∀ (n : Nat) (x y z : A),
    Path (tensorL n x (tensorL n y z)) (tensorL n (tensorL n x y) z)
  commPath : ∀ (n : Nat) (x y : A),
    Path (tensorL n x y) (tensorL n y x)
  unitObj : A
  unitPath : ∀ (n : Nat) (x : A), Path (tensorL n unitObj x) x

namespace DerivedTensorData

variable {A : Type u} (D : DerivedTensorData A)

/-- Associativity. -/
def derived_tensor_assoc (n : Nat) (x y z : A) :
    Path (D.tensorL n x (D.tensorL n y z)) (D.tensorL n (D.tensorL n x y) z) :=
  D.assocPath n x y z

/-- Commutativity. -/
def derived_tensor_comm (n : Nat) (x y : A) :
    Path (D.tensorL n x y) (D.tensorL n y x) :=
  D.commPath n x y

/-- Left unit. -/
def derived_tensor_unit (n : Nat) (x : A) :
    Path (D.tensorL n D.unitObj x) x :=
  D.unitPath n x

/-- Right unit via commutativity. -/
def derived_tensor_unit_right (n : Nat) (x : A) :
    Path (D.tensorL n x D.unitObj) x :=
  Path.trans (D.commPath n x D.unitObj) (D.unitPath n x)

/-- Assoc coherence. -/
theorem derived_tensor_assoc_rweq (n : Nat) (x y z : A) :
    RwEq
      (Path.trans (D.assocPath n x y z) (Path.refl _))
      (D.assocPath n x y z) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Comm + unit composes correctly. -/
theorem derived_tensor_unit_right_rweq (n : Nat) (x : A) :
    RwEq
      (Path.trans (D.derived_tensor_unit_right n x) (Path.refl _))
      (D.derived_tensor_unit_right n x) :=
  rweq_of_hom_step (HomStep.right_unit _)

end DerivedTensorData

/-! ## RHom -/

/-- RHom: derived internal hom. -/
structure RHomData (A : Type u) where
  rhom : Nat → A → A → A
  adjPath : ∀ (n : Nat) (x y z : A) (tensorL : Nat → A → A → A),
    Path (rhom n (tensorL n x y) z) (rhom n x (rhom n y z))

namespace RHomData

variable {A : Type u} (R : RHomData A)

/-- Tensor-Hom adjunction. -/
def tensor_hom_adj (n : Nat) (x y z : A) (tensorL : Nat → A → A → A) :
    Path (R.rhom n (tensorL n x y) z) (R.rhom n x (R.rhom n y z)) :=
  R.adjPath n x y z tensorL

/-- Adjunction coherence. -/
theorem adj_rweq (n : Nat) (x y z : A) (tensorL : Nat → A → A → A) :
    RwEq
      (Path.trans (R.adjPath n x y z tensorL) (Path.refl _))
      (R.adjPath n x y z tensorL) :=
  rweq_of_hom_step (HomStep.right_unit _)

end RHomData

/-! ## Dualizing Complex -/

/-- Dualizing complex for Grothendieck duality. -/
structure DualizingData (A : Type u) where
  dualizing : A
  dualFunctor : A → A
  involutionPath : ∀ x : A, Path (dualFunctor (dualFunctor x)) x

namespace DualizingData

variable {A : Type u} (D : DualizingData A)

/-- Duality involution. -/
def duality_involution (x : A) :
    Path (D.dualFunctor (D.dualFunctor x)) x :=
  D.involutionPath x

/-- Triple duality reduces to single. -/
def triple_duality (x : A) :
    Path (D.dualFunctor (D.dualFunctor (D.dualFunctor x))) (D.dualFunctor x) :=
  Path.congrArg D.dualFunctor (D.involutionPath x)

/-- Duality involution coherence. -/
theorem duality_rweq (x : A) :
    RwEq
      (Path.trans (D.involutionPath x) (Path.refl _))
      (D.involutionPath x) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Duality cancellation. -/
theorem duality_cancel_rweq (x : A) :
    RwEq
      (Path.trans (D.involutionPath x) (Path.symm (D.involutionPath x)))
      (Path.refl _) :=
  rweq_of_hom_step (HomStep.inverse_cancel _)

end DualizingData

/-! ## Euler Characteristic -/

/-- Euler characteristic. -/
structure EulerCharData (A : Type u) where
  k0 : K0Data A
  euler : A → A
  eulerSESPath : ∀ (a b c : A),
    Path (euler b) (k0.add (euler a) (euler c))

namespace EulerCharData

variable {A : Type u} (E : EulerCharData A)

def euler_additive (a b c : A) :
    Path (E.euler b) (E.k0.add (E.euler a) (E.euler c)) :=
  E.eulerSESPath a b c

/-- Euler additivity coherence. -/
theorem euler_rweq (a b c : A) :
    RwEq
      (Path.trans (E.eulerSESPath a b c) (Path.refl _))
      (E.eulerSESPath a b c) :=
  rweq_of_hom_step (HomStep.right_unit _)

end EulerCharData

/-! ## Homotopy Category -/

/-- Homotopy category data. -/
structure HomotopyCatData (A : Type u) where
  comp : A → A → A
  idMor : A → A
  compIdPath : ∀ x : A, Path (comp x (idMor x)) x
  idCompPath : ∀ x : A, Path (comp (idMor x) x) x
  compAssocPath : ∀ x y z : A, Path (comp (comp x y) z) (comp x (comp y z))

namespace HomotopyCatData

variable {A : Type u} (H : HomotopyCatData A)

/-- Associativity. -/
def homotopy_comp_assoc (x y z : A) :
    Path (H.comp (H.comp x y) z) (H.comp x (H.comp y z)) :=
  H.compAssocPath x y z

/-- Right identity. -/
def homotopy_comp_id (x : A) : Path (H.comp x (H.idMor x)) x :=
  H.compIdPath x

/-- Left identity. -/
def homotopy_id_comp (x : A) : Path (H.comp (H.idMor x) x) x :=
  H.idCompPath x

/-- Associativity coherence. -/
theorem homotopy_assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (H.compAssocPath x y z) (Path.refl _))
      (H.compAssocPath x y z) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Right id coherence. -/
theorem homotopy_comp_id_rweq (x : A) :
    RwEq
      (Path.trans (H.compIdPath x) (Path.refl _))
      (H.compIdPath x) :=
  rweq_of_hom_step (HomStep.right_unit _)

/-- Associativity of four terms. -/
def homotopy_comp_assoc4 (w x y z : A) :
    Path (H.comp (H.comp (H.comp w x) y) z) (H.comp w (H.comp x (H.comp y z))) := by
  -- ((wx)y)z → (wx)(yz) → w(x(yz))
  exact Path.trans (H.compAssocPath (H.comp w x) y z) (H.compAssocPath w x (H.comp y z))

end HomotopyCatData

/-! ## Perverse Sheaves -/

/-- Perverse t-structure data. -/
structure PerverseData (A : Type u) where
  perversity : Nat → Nat
  tStr : TStructureData A
  pTau : Nat → A → A
  pTauIdempPath : ∀ (n : Nat) (x : A),
    Path (pTau n (pTau n x)) (pTau n x)

namespace PerverseData

variable {A : Type u} (P : PerverseData A)

/-- Perverse truncation is idempotent. -/
def perverse_tau_idemp (n : Nat) (x : A) :
    Path (P.pTau n (P.pTau n x)) (P.pTau n x) :=
  P.pTauIdempPath n x

/-- Idempotency coherence. -/
theorem perverse_idemp_rweq (n : Nat) (x : A) :
    RwEq
      (Path.trans (P.pTauIdempPath n x) (Path.refl _))
      (P.pTauIdempPath n x) :=
  rweq_of_hom_step (HomStep.right_unit _)

end PerverseData

/-! ## Homological Dimension -/

/-- Homological dimension data. -/
structure HomDimData (A : Type u) where
  projDim : Nat
  injDim : Nat
  dimIneqPath : projDim ≤ injDim

namespace HomDimData

variable {A : Type u} (H : HomDimData A)

theorem projDim_bound : H.projDim ≤ H.injDim := H.dimIneqPath

end HomDimData

/-! ## Filtered Derived Category -/

/-- Filtered object data. -/
structure FilteredData (A : Type u) where
  filt : Nat → A
  graded : Nat → A

/-- Filtered quasi-isomorphism. -/
structure FilteredQIso (A : Type u) where
  srcFilt : FilteredData A
  tgtFilt : FilteredData A
  gradedIsoPath : ∀ p : Nat, Path (srcFilt.graded p) (tgtFilt.graded p)

namespace FilteredQIso

variable {A : Type u} (F : FilteredQIso A)

def graded_iso (p : Nat) : Path (F.srcFilt.graded p) (F.tgtFilt.graded p) :=
  F.gradedIsoPath p

/-- Graded iso coherence. -/
theorem graded_iso_rweq (p : Nat) :
    RwEq
      (Path.trans (F.gradedIsoPath p) (Path.refl _))
      (F.gradedIsoPath p) :=
  rweq_of_hom_step (HomStep.right_unit _)

end FilteredQIso

end HomologicalDeep
end Path
end ComputationalPaths
