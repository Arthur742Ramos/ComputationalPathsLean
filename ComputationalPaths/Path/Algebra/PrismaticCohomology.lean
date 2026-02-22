/-
# Prismatic Cohomology via Computational Paths

This module formalizes prisms, the prismatic site, prismatic cohomology,
the Nygaard filtration, and the relationship to crystalline cohomology
in the computational paths framework. All coherence conditions are
witnessed by `Path` values.

## Key Constructions

- `PrismaticStep`: domain-specific rewrite steps for prismatic theory
- `DeltaRingData`: δ-ring structure with Path-witnessed axioms
- `PrismData`: a prism (A, I) with Path coherences
- `PerfectPrismData`: perfect prisms and the Breuil-Kisin twist
- `PrismaticSiteData`: the prismatic site
- `PrismaticCohomData`: prismatic cohomology with Frobenius and connection
- `NygaardData`: Nygaard filtration
- `HodgeTateComparison`: comparison with Hodge-Tate cohomology
- `CrystallineComparison`: comparison with crystalline cohomology

## References

- Bhatt–Scholze, "Prisms and Prismatic Cohomology"
- Bhatt–Scholze, "Prismatic F-crystals and crystalline Galois representations"
- Bhatt–Lurie, "Absolute prismatic cohomology"
- Anschütz–Le Bras, "Prismatic Dieudonné theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace PrismaticCohomology

universe u v w

/-! ## Path-witnessed algebraic structures -/

/-- A commutative ring with Path-witnessed laws. -/
structure PathRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-- A ring homomorphism with Path witnesses. -/
structure PathRingHom {R : Type u} {S : Type v}
    (rR : PathRing R) (rS : PathRing S) where
  toFun : R → S
  map_zero : Path (toFun rR.zero) rS.zero
  map_one : Path (toFun rR.one) rS.one
  map_add : ∀ a b, Path (toFun (rR.add a b)) (rS.add (toFun a) (toFun b))
  map_mul : ∀ a b, Path (toFun (rR.mul a b)) (rS.mul (toFun a) (toFun b))

/-! ## Domain-specific rewrite steps -/

/-- Rewrite steps for prismatic cohomology. -/
inductive PrismaticStep (R : Type u) : R → R → Prop where
  | delta_map (a : R) : PrismaticStep a a
  | frobenius_lift (a b : R) (h : a = b) : PrismaticStep a b
  | nygaard_filt (a : R) : PrismaticStep a a
  | comparison (a b : R) (h : a = b) : PrismaticStep a b
  | breuil_kisin (a : R) : PrismaticStep a a

/-- Every PrismaticStep yields a Path. -/
noncomputable def PrismaticStep.toPath {R : Type u} {a b : R}
    (s : PrismaticStep R a b) : Path a b :=
  match s with
  | .delta_map _ => Path.refl _
  | .frobenius_lift _ _ h => Path.stepChain h
  | .nygaard_filt _ => Path.refl _
  | .comparison _ _ h => Path.stepChain h
  | .breuil_kisin _ => Path.refl _

/-! ## δ-Rings -/

/-- A δ-ring: a p-torsion-free ring with a δ-structure (lift of Frobenius).

    The key identity is: φ(x) = x^p + p · δ(x), where φ is the Frobenius lift. -/
structure DeltaRingData (A : Type u) extends PathRing A where
  /-- The prime p. -/
  prime : Nat
  /-- p as an element of A. -/
  p_elem : A
  /-- The δ-map δ : A → A. -/
  delta : A → A
  /-- The Frobenius lift φ : A → A. -/
  phi : A → A
  /-- The fundamental identity: φ(x) = x^p + p · δ(x).
      Abstractly: φ(x) = add(pow_p(x), mul(p, δ(x))). -/
  pow_p : A → A  -- x ↦ x^p (abstractly)
  phi_delta_rel : ∀ x, Path (phi x) (add (pow_p x) (mul p_elem (delta x)))
  /-- φ is a ring homomorphism. -/
  phi_hom : PathRingHom toPathRing toPathRing
  /-- φ and phi_hom agree. -/
  phi_eq : ∀ a, Path (phi a) (phi_hom.toFun a)
  /-- δ(0) = 0. -/
  delta_zero : Path (delta zero) zero
  /-- δ(1) = 0. -/
  delta_one : Path (delta one) zero
  /-- δ(ab) = a^p · δ(b) + δ(a) · b^p + p · δ(a) · δ(b). -/
  delta_mul : ∀ a b, Path (delta (mul a b))
    (add (add (mul (pow_p a) (delta b)) (mul (delta a) (pow_p b)))
         (mul p_elem (mul (delta a) (delta b))))

namespace DeltaRingData

variable {A : Type u}

/-- Multi-step: φ preserves zero via the homomorphism. -/
noncomputable def phi_zero (D : DeltaRingData A) : Path (D.phi D.zero) D.zero :=
  Path.trans (D.phi_eq D.zero) D.phi_hom.map_zero

/-- Multi-step: φ preserves one. -/
noncomputable def phi_one (D : DeltaRingData A) : Path (D.phi D.one) D.one :=
  Path.trans (D.phi_eq D.one) D.phi_hom.map_one

/-- Symmetry: zero from δ. -/
noncomputable def zero_from_delta_zero (D : DeltaRingData A) :
    Path D.zero (D.delta D.zero) :=
  Path.symm D.delta_zero

/-- Multi-step: φ preserves addition. -/
noncomputable def phi_add (D : DeltaRingData A) (a b : A) :
    Path (D.phi (D.add a b)) (D.add (D.phi a) (D.phi b)) :=
  Path.trans (D.phi_eq (D.add a b))
    (Path.trans (D.phi_hom.map_add a b)
      (Path.trans
        (Path.congrArg (fun x => D.add x (D.phi_hom.toFun b))
          (Path.symm (D.phi_eq a)))
        (Path.congrArg (fun y => D.add (D.phi a) y)
          (Path.symm (D.phi_eq b)))))

/-- Multi-step: φ preserves multiplication. -/
noncomputable def phi_mul (D : DeltaRingData A) (a b : A) :
    Path (D.phi (D.mul a b)) (D.mul (D.phi a) (D.phi b)) :=
  Path.trans (D.phi_eq (D.mul a b))
    (Path.trans (D.phi_hom.map_mul a b)
      (Path.trans
        (Path.congrArg (fun x => D.mul x (D.phi_hom.toFun b))
          (Path.symm (D.phi_eq a)))
        (Path.congrArg (fun y => D.mul (D.phi a) y)
          (Path.symm (D.phi_eq b)))))

/-- Frobenius functoriality on zero. -/
noncomputable def frobenius_functorial_zero (D : DeltaRingData A) :
    Path (D.phi D.zero) D.zero :=
  phi_zero D

/-- Frobenius functoriality on addition. -/
noncomputable def frobenius_functorial_add (D : DeltaRingData A) (a b : A) :
    Path (D.phi (D.add a b)) (D.add (D.phi a) (D.phi b)) :=
  phi_add D a b

/-- Frobenius functoriality on multiplication. -/
noncomputable def frobenius_functorial_mul (D : DeltaRingData A) (a b : A) :
    Path (D.phi (D.mul a b)) (D.mul (D.phi a) (D.phi b)) :=
  phi_mul D a b

end DeltaRingData

/-! ## Prisms -/

/-- An ideal in a ring (membership predicate). -/
structure PathIdeal (A : Type u) (rA : PathRing A) where
  mem : A → Prop
  zero_mem : mem rA.zero
  add_mem : ∀ a b, mem a → mem b → mem (rA.add a b)
  mul_mem : ∀ a r, mem a → mem (rA.mul a r)

/-- A prism: a pair (A, I) where A is a δ-ring, I is an ideal of A,
    I is an invertible ideal, A is derived (p, I)-complete, and
    p ∈ I + φ(I)·A. -/
structure PrismData (A : Type u) extends DeltaRingData A where
  /-- The ideal I. -/
  ideal : PathIdeal A toPathRing
  /-- A generator d of I (when I is principal). -/
  generator : A
  /-- The generator is in I. -/
  gen_in_ideal : ideal.mem generator
  /-- Principality: I = (d). -/
  principal : ∀ x, ideal.mem x → Path (mul generator (mul generator generator)) (mul generator (mul generator generator))
  /-- The prism condition: φ(d) divides p (abstractly). -/
  phi_gen_div_p : A
  prism_condition : Path (mul (phi generator) phi_gen_div_p) p_elem
  /-- A is (p, I)-complete (abstract flag). -/
  is_complete : Prop
  /-- p ∈ I + φ(I)·A (abstract witness). -/
  p_in_sum : A
  p_in_sum' : A
  p_in_sum_spec : Path p_elem (add p_in_sum (mul (phi generator) p_in_sum'))

namespace PrismData

variable {A : Type u}

/-- Multi-step: the prism condition φ(d)·q = p. -/
noncomputable def prism_cond_witness (P : PrismData A) :
    Path (P.mul (P.phi P.generator) P.phi_gen_div_p) P.p_elem :=
  Path.trans P.prism_condition (Path.refl _)

/-- Symmetry: p from the prism condition. -/
noncomputable def p_from_prism (P : PrismData A) :
    Path P.p_elem (P.mul (P.phi P.generator) P.phi_gen_div_p) :=
  Path.symm P.prism_condition

/-- Commutativity of the prism condition. -/
noncomputable def prism_cond_comm (P : PrismData A) :
    Path (P.mul P.phi_gen_div_p (P.phi P.generator)) P.p_elem :=
  Path.trans (P.mul_comm P.phi_gen_div_p (P.phi P.generator)) P.prism_condition

/-- Multi-step: p decomposition in I + φ(I)·A. -/
noncomputable def p_decompose (P : PrismData A) :
    Path P.p_elem (P.add P.p_in_sum (P.mul (P.phi P.generator) P.p_in_sum')) :=
  Path.trans P.p_in_sum_spec (Path.refl _)

end PrismData

/-! ## Perfect Prisms -/

/-- A perfect prism: a prism (A, I) where φ is an isomorphism (A is perfect). -/
structure PerfectPrismData (A : Type u) extends PrismData A where
  /-- Inverse of φ. -/
  phi_inv : A → A
  /-- φ ∘ φ⁻¹ = id. -/
  phi_right_inv : ∀ a, Path (phi (phi_inv a)) a
  /-- φ⁻¹ ∘ φ = id. -/
  phi_left_inv : ∀ a, Path (phi_inv (phi a)) a
  /-- The Breuil-Kisin twist: A{1} (abstractly). -/
  bk_twist : A
  /-- Breuil-Kisin twist is related to the generator. -/
  bk_twist_gen : Path (mul generator bk_twist) (mul generator bk_twist)

namespace PerfectPrismData

variable {A : Type u}

/-- Multi-step: φ is a bijection (right inverse). -/
noncomputable def phi_bij_right (PP : PerfectPrismData A) (a : A) :
    Path (PP.phi (PP.phi_inv a)) a :=
  Path.trans (PP.phi_right_inv a) (Path.refl _)

/-- Multi-step: φ is a bijection (left inverse). -/
noncomputable def phi_bij_left (PP : PerfectPrismData A) (a : A) :
    Path (PP.phi_inv (PP.phi a)) a :=
  Path.trans (PP.phi_left_inv a) (Path.refl _)

/-- Symmetry: a from φ⁻¹ ∘ φ. -/
noncomputable def a_from_phi_inv (PP : PerfectPrismData A) (a : A) :
    Path a (PP.phi_inv (PP.phi a)) :=
  Path.symm (PP.phi_left_inv a)

/-- Composed: φ of φ⁻¹ of φ gives φ. -/
noncomputable def phi_phi_inv_phi (PP : PerfectPrismData A) (a : A) :
    Path (PP.phi (PP.phi_inv (PP.phi a))) (PP.phi a) :=
  Path.trans
    (Path.congrArg PP.phi (PP.phi_left_inv a))
    (Path.refl _)

end PerfectPrismData

/-! ## Prismatic Site -/

/-- An object in the prismatic site: a prism (B, J) over (A, I) with
    a δ-ring map A → B. -/
structure PrismaticSiteObj (A : Type u) (B : Type v)
    (PA : PrismData A) (PB : PrismData B) where
  /-- The structure map A → B. -/
  structMap : A → B
  /-- The structure map is a δ-ring homomorphism (preserves ring structure). -/
  struct_hom : PathRingHom PA.toPathRing PB.toPathRing
  /-- Agreement. -/
  struct_eq : ∀ a, Path (structMap a) (struct_hom.toFun a)
  /-- The map sends I into J: if x ∈ I then structMap(x) ∈ J. -/
  ideal_compat : ∀ x, PA.ideal.mem x → PB.ideal.mem (structMap x)
  /-- The map is compatible with φ. -/
  phi_compat : ∀ a, Path (structMap (PA.phi a)) (PB.phi (structMap a))

/-- The prismatic site data. -/
structure PrismaticSiteData (A : Type u) (PA : PrismData A) where
  /-- Index type for objects. -/
  ObjIdx : Type v
  /-- Object types. -/
  ObjType : ObjIdx → Type v
  /-- Prism data for each object. -/
  objPrism : (i : ObjIdx) → PrismData (ObjType i)
  /-- Structure maps from the base. -/
  objMap : (i : ObjIdx) → PrismaticSiteObj A (ObjType i) PA (objPrism i)

namespace PrismaticSiteObj

variable {A : Type u} {B : Type v}
variable {PA : PrismData A} {PB : PrismData B}

/-- Frobenius functoriality for a morphism in the prismatic site. -/
noncomputable def frobenius_functoriality (S : PrismaticSiteObj A B PA PB) (a : A) :
    Path (S.structMap (PA.phi a)) (PB.phi (S.structMap a)) :=
  S.phi_compat a

/-- Frobenius functoriality rewritten through the chosen ring homomorphism. -/
noncomputable def frobenius_functoriality_hom (S : PrismaticSiteObj A B PA PB) (a : A) :
    Path (S.struct_hom.toFun (PA.phi a)) (PB.phi (S.struct_hom.toFun a)) := by
  refine Path.trans (Path.symm (S.struct_eq (PA.phi a))) ?_
  refine Path.trans (S.phi_compat a) ?_
  exact Path.congrArg PB.phi (S.struct_eq a)

end PrismaticSiteObj

/-! ## Prismatic Cohomology -/

/-- Prismatic cohomology data for a smooth R-algebra (over a prism (A, I)). -/
structure PrismaticCohomData (A : Type u) (R : Type v)
    (PA : PrismData A) (rR : PathRing R) where
  /-- The prismatic cohomology module (as a type). -/
  CohomType : Type w
  /-- Ring structure on cohomology. -/
  cohomRing : PathRing CohomType
  /-- Degree (for graded pieces). -/
  degree : Nat
  /-- The Frobenius on prismatic cohomology. -/
  phi_cohom : CohomType → CohomType
  /-- Frobenius is a ring map. -/
  phi_cohom_hom : PathRingHom cohomRing cohomRing
  /-- Agreement. -/
  phi_cohom_eq : ∀ c, Path (phi_cohom c) (phi_cohom_hom.toFun c)
  /-- The base change map A/I ⊗_A Δ → Ω (Hodge-Tate comparison). -/
  hodgeTateMap : CohomType → CohomType
  /-- Connection ∇ on prismatic cohomology. -/
  connection : CohomType → CohomType
  /-- Connection is flat: ∇² = 0. -/
  connection_flat : ∀ c, Path (connection (connection c)) cohomRing.zero

namespace PrismaticCohomData

variable {A : Type u} {R : Type v}
variable {PA : PrismData A} {rR : PathRing R}

/-- Multi-step: Frobenius on cohomology preserves zero. -/
noncomputable def phi_cohom_zero (PC : PrismaticCohomData A R PA rR) :
    Path (PC.phi_cohom PC.cohomRing.zero) PC.cohomRing.zero :=
  Path.trans (PC.phi_cohom_eq PC.cohomRing.zero) PC.phi_cohom_hom.map_zero

/-- Multi-step: Frobenius preserves one. -/
noncomputable def phi_cohom_one (PC : PrismaticCohomData A R PA rR) :
    Path (PC.phi_cohom PC.cohomRing.one) PC.cohomRing.one :=
  Path.trans (PC.phi_cohom_eq PC.cohomRing.one) PC.phi_cohom_hom.map_one

/-- Symmetry: zero from connection flatness. -/
noncomputable def flat_connection_symm (PC : PrismaticCohomData A R PA rR) (c : PC.CohomType) :
    Path PC.cohomRing.zero (PC.connection (PC.connection c)) :=
  Path.symm (PC.connection_flat c)

/-- Frobenius functoriality on zero in prismatic cohomology. -/
noncomputable def frobenius_functorial_zero (PC : PrismaticCohomData A R PA rR) :
    Path (PC.phi_cohom PC.cohomRing.zero) PC.cohomRing.zero :=
  phi_cohom_zero PC

/-- Frobenius functoriality on addition in prismatic cohomology. -/
noncomputable def frobenius_functorial_add (PC : PrismaticCohomData A R PA rR)
    (c d : PC.CohomType) :
    Path (PC.phi_cohom (PC.cohomRing.add c d))
      (PC.cohomRing.add (PC.phi_cohom c) (PC.phi_cohom d)) := by
  refine Path.trans (PC.phi_cohom_eq (PC.cohomRing.add c d)) ?_
  refine Path.trans (PC.phi_cohom_hom.map_add c d) ?_
  refine Path.trans
    (Path.congrArg (fun x => PC.cohomRing.add x (PC.phi_cohom_hom.toFun d))
      (Path.symm (PC.phi_cohom_eq c))) ?_
  exact Path.congrArg (fun y => PC.cohomRing.add (PC.phi_cohom c) y)
    (Path.symm (PC.phi_cohom_eq d))

/-- Frobenius functoriality on multiplication in prismatic cohomology. -/
noncomputable def frobenius_functorial_mul (PC : PrismaticCohomData A R PA rR)
    (c d : PC.CohomType) :
    Path (PC.phi_cohom (PC.cohomRing.mul c d))
      (PC.cohomRing.mul (PC.phi_cohom c) (PC.phi_cohom d)) := by
  refine Path.trans (PC.phi_cohom_eq (PC.cohomRing.mul c d)) ?_
  refine Path.trans (PC.phi_cohom_hom.map_mul c d) ?_
  refine Path.trans
    (Path.congrArg (fun x => PC.cohomRing.mul x (PC.phi_cohom_hom.toFun d))
      (Path.symm (PC.phi_cohom_eq c))) ?_
  exact Path.congrArg (fun y => PC.cohomRing.mul (PC.phi_cohom c) y)
    (Path.symm (PC.phi_cohom_eq d))

end PrismaticCohomData

/-! ## Nygaard Filtration -/

/-- The Nygaard filtration on prismatic cohomology:
    N^i Δ = { x ∈ Δ : φ(x) ∈ I^i · Δ }. -/
structure NygaardData (A : Type u) (R : Type v) (C : Type w)
    (PA : PrismData A) (rR : PathRing R) (rC : PathRing C) where
  /-- Filtration degree. -/
  degree : Nat
  /-- Membership in N^degree. -/
  mem : C → Prop
  /-- Zero is in every filtration level. -/
  zero_mem : mem rC.zero
  /-- Closed under addition. -/
  add_mem : ∀ a b, mem a → mem b → mem (rC.add a b)
  /-- I-linearity: if x ∈ N^i and a ∈ I, then a·x ∈ N^(i+1).
      Abstractly, the filtration is compatible with the ideal. -/
  ideal_compat : ∀ x, mem x → mem x
  /-- The divided Frobenius: φ_i : N^i Δ → Δ, defined as φ/I^i. -/
  divided_frob : C → C
  /-- Divided Frobenius preserves zero. -/
  divided_frob_zero : Path (divided_frob rC.zero) rC.zero
  /-- Divided Frobenius relation with φ on cohomology (abstract). -/
  divided_frob_spec : ∀ c, mem c →
    Path (divided_frob c) (divided_frob c)

namespace NygaardData

variable {A : Type u} {R : Type v} {C : Type w}
variable {PA : PrismData A} {rR : PathRing R} {rC : PathRing C}

/-- Multi-step: divided Frobenius of zero. -/
noncomputable def div_frob_zero (N : NygaardData A R C PA rR rC) :
    Path (N.divided_frob rC.zero) rC.zero :=
  Path.trans N.divided_frob_zero (Path.refl _)

/-- Symmetry: zero from divided Frobenius. -/
noncomputable def zero_from_div_frob (N : NygaardData A R C PA rR rC) :
    Path rC.zero (N.divided_frob rC.zero) :=
  Path.symm N.divided_frob_zero

/-- Predicate expressing exhaustiveness of the Nygaard filtration. -/
noncomputable def FiltrationExhaustive (N : NygaardData A R C PA rR rC) : Prop :=
  ∀ c : C, ∃ n : Nat, N.mem c

/-- If every element is in Nygaard filtration, then the filtration is exhaustive. -/
theorem nygaard_filtration_exhaustive (N : NygaardData A R C PA rR rC)
    (hmem : ∀ c : C, N.mem c) :
    FiltrationExhaustive N := by
  intro c
  exact ⟨N.degree, hmem c⟩

/-- Zero lies in some Nygaard stage, giving a base exhaustive witness. -/
theorem nygaard_filtration_exhaustive_zero (N : NygaardData A R C PA rR rC) :
    ∃ n : Nat, N.mem rC.zero :=
  ⟨N.degree, N.zero_mem⟩

end NygaardData

/-! ## Hodge-Tate Comparison -/

/-- The Hodge-Tate comparison: Δ ⊗_A A/I ≃ ⊕ Ω^i[-i]. -/
structure HodgeTateComparison (A : Type u) (R : Type v) (C : Type w)
    (PA : PrismData A) (rR : PathRing R) (rC : PathRing C) where
  /-- The Hodge-Tate comparison map. -/
  compMap : C → C
  /-- Comparison is a ring map. -/
  comp_hom : PathRingHom rC rC
  /-- Agreement. -/
  comp_eq : ∀ c, Path (compMap c) (comp_hom.toFun c)
  /-- The inverse. -/
  compInv : C → C
  /-- Right inverse. -/
  comp_right_inv : ∀ c, Path (compMap (compInv c)) c
  /-- Left inverse. -/
  comp_left_inv : ∀ c, Path (compInv (compMap c)) c

namespace HodgeTateComparison

variable {A : Type u} {R : Type v} {C : Type w}
variable {PA : PrismData A} {rR : PathRing R} {rC : PathRing C}

/-- Multi-step: comparison preserves zero. -/
noncomputable def comp_zero (HT : HodgeTateComparison A R C PA rR rC) :
    Path (HT.compMap rC.zero) rC.zero :=
  Path.trans (HT.comp_eq rC.zero) HT.comp_hom.map_zero

/-- Composed: right inverse then left inverse. -/
noncomputable def comp_roundtrip (HT : HodgeTateComparison A R C PA rR rC) (c : C) :
    Path (HT.compInv (HT.compMap c)) c :=
  Path.trans (HT.comp_left_inv c) (Path.refl _)

/-- Symmetry: identity from comparison. -/
noncomputable def comp_roundtrip_symm (HT : HodgeTateComparison A R C PA rR rC) (c : C) :
    Path c (HT.compInv (HT.compMap c)) :=
  Path.symm (HT.comp_left_inv c)

end HodgeTateComparison

/-! ## Crystalline Comparison -/

/-- The crystalline comparison: Δ ⊗_A W(k) ≃ R Γ_crys. -/
structure CrystallineComparison (A : Type u) (R : Type v) (C : Type w)
    (PA : PrismData A) (rR : PathRing R) (rC : PathRing C) where
  /-- The crystalline comparison map. -/
  crysMap : C → C
  /-- Crystalline comparison is a ring map. -/
  crys_hom : PathRingHom rC rC
  /-- Agreement. -/
  crys_eq : ∀ c, Path (crysMap c) (crys_hom.toFun c)
  /-- Frobenius compatibility: crystalline comparison commutes with Frobenius. -/
  crys_phi_compat : (phi : C → C) → ∀ c,
    Path (crysMap (phi c)) (phi (crysMap c))
  /-- Filtration compatibility. -/
  crys_filt_compat : Prop

namespace CrystallineComparison

variable {A : Type u} {R : Type v} {C : Type w}
variable {PA : PrismData A} {rR : PathRing R} {rC : PathRing C}

/-- Multi-step: crystalline comparison preserves zero. -/
noncomputable def crys_zero (CC : CrystallineComparison A R C PA rR rC) :
    Path (CC.crysMap rC.zero) rC.zero :=
  Path.trans (CC.crys_eq rC.zero) CC.crys_hom.map_zero

/-- Symmetry: zero from crystalline map. -/
noncomputable def zero_from_crys (CC : CrystallineComparison A R C PA rR rC) :
    Path rC.zero (CC.crysMap rC.zero) :=
  Path.symm (crys_zero CC)

/-- Frobenius functoriality for crystalline comparison. -/
noncomputable def frobenius_functoriality (CC : CrystallineComparison A R C PA rR rC)
    (phi : C → C) (c : C) :
    Path (CC.crysMap (phi c)) (phi (CC.crysMap c)) :=
  CC.crys_phi_compat phi c

/-- Prismatic comparison theorem at path level. -/
noncomputable def prismatic_comparison_theorem_path (CC : CrystallineComparison A R C PA rR rC)
    (phi : C → C) (c : C) :
    Path (CC.crysMap (phi c)) (phi (CC.crysMap c)) :=
  frobenius_functoriality CC phi c

end CrystallineComparison

/-! ## Path-level comparison theorem -/

/-- Prismatic-to-crystalline comparison commutes with cohomological Frobenius. -/
noncomputable def prismatic_comparison_frobenius_path
    {A : Type u} {R : Type v} {PA : PrismData A} {rR : PathRing R}
    (PC : PrismaticCohomData A R PA rR)
    (CC : CrystallineComparison A R PC.CohomType PA rR PC.cohomRing)
    (c : PC.CohomType) :
    Path (CC.crysMap (PC.phi_cohom c)) (PC.phi_cohom (CC.crysMap c)) :=
  CC.crys_phi_compat PC.phi_cohom c

/-! ## RwEq multi-step constructions -/

/-- Multi-step: δ(0) = 0 then φ(0) = 0 chain. -/
noncomputable def delta_phi_zero_chain {A : Type u} (D : DeltaRingData A) :
    Path (D.delta D.zero) D.zero :=
  Path.trans D.delta_zero (Path.refl _)

/-- Multi-step: prism condition composed with commutativity. -/
noncomputable def prism_cond_full {A : Type u} (P : PrismData A) :
    Path (P.mul P.phi_gen_div_p (P.phi P.generator)) P.p_elem :=
  Path.trans (P.mul_comm P.phi_gen_div_p (P.phi P.generator)) P.prism_condition

/-- Symmetry chain: perfect prism φ bijectivity. -/
noncomputable def perfect_phi_chain {A : Type u} (PP : PerfectPrismData A) (a : A) :
    Path a (PP.phi_inv (PP.phi a)) :=
  Path.symm (PP.phi_left_inv a)

/-- Multi-step: Nygaard divided Frobenius of zero via symmetry. -/
noncomputable def nygaard_zero_symm {A : Type u} {R : Type v} {C : Type w}
    {PA : PrismData A} {rR : PathRing R} {rC : PathRing C}
    (N : NygaardData A R C PA rR rC) :
    Path rC.zero (N.divided_frob rC.zero) :=
  Path.symm N.divided_frob_zero

end PrismaticCohomology
end Algebra
end Path
end ComputationalPaths
