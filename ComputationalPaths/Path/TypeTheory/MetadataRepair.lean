/-
# Universal quotient repair for equality metadata

This module strengthens the metadata-fiber classification with a complete
repair theory.  Metadata fibers are quotiented by explicit `Setoid`s.  A
quotient is contractible exactly when its carrier is inhabited and its setoid
relates every pair; for a chosen metadata value, this reduces to totality of
the reflexivity-fiber setoid.  The indiscrete relation is the relation-theoretic
maximal, information-minimal repair, and is terminal for maps that preserve the
canonical quotient maps.

The second half treats arbitrary relations equipped with a reflexive projection
to ambient equality.  Their based total spaces are classified by the kernel
over reflexivity.  Applying this to `PathRwQuot.toEq` gives the exact local
K/trivial-loop criterion.  Finally, concrete `RwEq` witnesses separate raw
trace observability from quotient observability and expose the distinction
between the repository's genuine loop quotient and its synthetic circle and
torus winding presentations.
-/

import ComputationalPaths.Path.TypeTheory.MetadataJ
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.CompPath.CircleStep
import ComputationalPaths.Path.CompPath.TorusStep

namespace ComputationalPaths
namespace Path
namespace MetadataRepair

open MetadataJ
open CompPath

universe u v w

/-! ## Setoid quotient families -/

/-- A setoid chosen separately on every equality-indexed metadata fiber. -/
abbrev MetadataSetoidFamily {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) : Type (max u v) :=
  (b : A) → (h : a = b) → Setoid (M b h)

/-- Equality metadata after quotienting each fiber by its chosen setoid. -/
abbrev QuotientMetadata {A : Type u} {a : A}
    {M : (b : A) → a = b → Type v}
    (S : MetadataSetoidFamily a M) (b : A) (h : a = b) : Type v :=
  Quotient (S b h)

/-- A setoid is total when every pair of carrier elements is related. -/
def SetoidTotal {X : Type u} (S : Setoid X) : Prop :=
  ∀ x y : X, S.r x y

/-- A quotient is inhabited exactly when its carrier is inhabited.  This is
the missing condition in the empty-carrier case: totality alone is then
vacuous, while contractibility is impossible. -/
theorem quotient_nonempty_iff {X : Type u} (S : Setoid X) :
    Nonempty (Quotient S) ↔ Nonempty X := by
  constructor
  · rintro ⟨q⟩
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x⟩
  · rintro ⟨x⟩
    exact ⟨Quotient.mk S x⟩

/-- Totality says exactly that all canonical quotient images are equal. -/
theorem setoidTotal_iff_quotient_mk_eq {X : Type u} (S : Setoid X) :
    SetoidTotal S ↔
      ∀ x y : X, Quotient.mk S x = Quotient.mk S y := by
  constructor
  · intro total x y
    exact Quotient.sound (total x y)
  · intro allImages x y
    exact Quotient.exact (allImages x y)

/-- General quotient classification, including the empty-carrier edge case. -/
theorem quotient_contractible_iff_nonempty_and_setoidTotal
    {X : Type u} (S : Setoid X) :
    IsContractible (Quotient S) ↔ Nonempty X ∧ SetoidTotal S := by
  constructor
  · intro contraction
    obtain ⟨center, contracts⟩ := contraction
    refine ⟨quotient_nonempty_iff S |>.mp ⟨center⟩, ?_⟩
    intro x y
    apply Quotient.exact
    exact IsContractible.all_eq ⟨center, contracts⟩
      (Quotient.mk S x) (Quotient.mk S y)
  · rintro ⟨⟨center⟩, total⟩
    refine ⟨Quotient.mk S center, ?_⟩
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact Quotient.sound (total center x)

/-- For an explicitly inhabited carrier, the quotient is contractible exactly
when the setoid is total.  Sufficiency uses `Quotient.sound`; necessity uses
`Quotient.exact`. -/
theorem quotient_contractible_iff_setoidTotal
    {X : Type u} (S : Setoid X) (center : X) :
    IsContractible (Quotient S) ↔ SetoidTotal S := by
  constructor
  · intro contraction
    exact
      (quotient_contractible_iff_nonempty_and_setoidTotal S).mp
        contraction |>.2
  · intro total
    exact
      (quotient_contractible_iff_nonempty_and_setoidTotal S).mpr
        ⟨⟨center⟩, total⟩

/-- A quotient of an empty carrier is not contractible, even though its setoid
relation is vacuously total. -/
theorem quotient_not_contractible_of_isEmpty
    {X : Type u} (S : Setoid X) (empty : X → False) :
    ¬ IsContractible (Quotient S) := by
  intro contraction
  obtain ⟨x⟩ :=
    (quotient_contractible_iff_nonempty_and_setoidTotal S).mp
      contraction |>.1
  exact empty x

/-- Equality induction transports an inhabitant of the reflexivity metadata
fiber to every equality-indexed fiber. -/
theorem metadata_fibers_nonempty {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) (m₀ : M a rfl) :
    ∀ (b : A) (h : a = b), Nonempty (M b h) := by
  intro b h
  cases h
  exact ⟨m₀⟩

/-- Equality induction transports reflexivity-fiber totality to every
equality-indexed metadata setoid. -/
theorem metadata_setoid_total_all_fibers
    {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M)
    (total₀ : SetoidTotal (S a rfl)) :
    ∀ (b : A) (h : a = b), SetoidTotal (S b h) := by
  intro b h
  cases h
  simpa using total₀

/-- With a reflexivity inhabitant, reflexivity totality contracts every
quotiented metadata fiber, not only the chosen one. -/
theorem metadata_quotient_fibers_contractible
    {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M) (m₀ : M a rfl)
    (total₀ : SetoidTotal (S a rfl)) :
    ∀ (b : A) (h : a = b), IsContractible (Quotient (S b h)) := by
  intro b h
  obtain ⟨m⟩ := metadata_fibers_nonempty a M m₀ b h
  exact
    (quotient_contractible_iff_setoidTotal (S b h) m).mpr
      (metadata_setoid_total_all_fibers a M S total₀ b h)

/-- The chosen center of the equality refinement after setoid quotienting. -/
def quotientMetadataCenter {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M) (m₀ : M a rfl) :
    MetadataTotal a (QuotientMetadata S) :=
  metadataCenter a (QuotientMetadata S) (Quotient.mk (S a rfl) m₀)

/-- Universal setoid-repair criterion: quotient-repaired unrestricted based
elimination with propositional beta exists exactly when the setoid on the
reflexivity metadata fiber is total. -/
theorem metadata_quotient_repair_criterion
    {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M) (m₀ : M a rfl) :
    Nonempty
        (UnrestrictedBasedEliminator.{max u v, w}
          (quotientMetadataCenter a M S m₀)) ↔
      SetoidTotal (S a rfl) := by
  exact
    (metadata_fiber_criterion a (QuotientMetadata S)
      (Quotient.mk (S a rfl) m₀)).trans
      (quotient_contractible_iff_setoidTotal (S a rfl) m₀)

/-- Any setoid repair supporting unrestricted elimination must relate every
pair of original reflexivity metadata values. -/
theorem elimination_forces_all_reflexivity_metadata_related
    {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M) (m₀ : M a rfl)
    (J : Nonempty
      (UnrestrictedBasedEliminator.{max u v, w}
        (quotientMetadataCenter a M S m₀)))
    (x y : M a rfl) :
    (S a rfl).r x y :=
  (metadata_quotient_repair_criterion a M S m₀).mp J x y

/-- Consequently no set-level quotient repair supporting unrestricted
elimination can retain two distinct visible quotient classes at reflexivity. -/
theorem elimination_forces_reflexivity_quotient_identification
    {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v)
    (S : MetadataSetoidFamily a M) (m₀ : M a rfl)
    (J : Nonempty
      (UnrestrictedBasedEliminator.{max u v, w}
        (quotientMetadataCenter a M S m₀)))
    (x y : M a rfl) :
    Quotient.mk (S a rfl) x = Quotient.mk (S a rfl) y :=
  Quotient.sound
    (elimination_forces_all_reflexivity_metadata_related
      a M S m₀ J x y)

/-! ## The indiscrete repair and its terminal factorization -/

/-- The indiscrete (total) setoid.  It is maximal as a relation and therefore
retains the least information among ordinary setoid quotients. -/
def indiscreteSetoid (X : Type u) : Setoid X where
  r := fun _ _ => True
  iseqv := by
    constructor
    · intro x
      trivial
    · intro x y _
      trivial
    · intro x y z _ _
      trivial

/-- The indiscrete relation is total. -/
theorem indiscrete_setoid_total (X : Type u) :
    SetoidTotal (indiscreteSetoid X) := by
  intro x y
  trivial

/-- The indiscrete quotient of an inhabited type is contractible. -/
theorem indiscrete_quotient_contractible {X : Type u} (center : X) :
    IsContractible (Quotient (indiscreteSetoid X)) :=
  (quotient_contractible_iff_setoidTotal
    (indiscreteSetoid X) center).mpr (indiscrete_setoid_total X)

/-- Inclusion of setoid relations, oriented in the direction in which the
identity-on-representatives map descends between quotients. -/
def RelationIncluded {X : Type u} (S T : Setoid X) : Prop :=
  ∀ ⦃x y : X⦄, S.r x y → T.r x y

/-- A factor map between quotients that preserves their canonical quotient
maps from the common carrier. -/
structure QuotientMapFactor {X : Type u} (S T : Setoid X) where
  toFun : Quotient S → Quotient T
  commutes :
    ∀ x : X, toFun (Quotient.mk S x) = Quotient.mk T x

/-- Relation inclusion constructs the canonical quotient-map-preserving
factorization. -/
def quotientMapFactorOfIncluded {X : Type u} {S T : Setoid X}
    (included : RelationIncluded S T) :
    QuotientMapFactor S T where
  toFun :=
    Quotient.lift
      (fun x : X => Quotient.mk T x)
      (fun _ _ h => Quotient.sound (included h))
  commutes := fun _ => rfl

/-- Any quotient-map-preserving factor forces inclusion of the source relation
in the target relation. -/
theorem relationIncludedOfQuotientMapFactor
    {X : Type u} {S T : Setoid X}
    (factor : QuotientMapFactor S T) :
    RelationIncluded S T := by
  intro x y related
  apply Quotient.exact
  calc
    Quotient.mk T x = factor.toFun (Quotient.mk S x) :=
      (factor.commutes x).symm
    _ = factor.toFun (Quotient.mk S y) := by
      exact _root_.congrArg factor.toFun (Quotient.sound related)
    _ = Quotient.mk T y := factor.commutes y

/-- Exact factorization criterion for quotients of a common carrier. -/
theorem quotient_map_factor_iff_relationIncluded
    {X : Type u} (S T : Setoid X) :
    Nonempty (QuotientMapFactor S T) ↔ RelationIncluded S T := by
  constructor
  · rintro ⟨factor⟩
    exact relationIncludedOfQuotientMapFactor factor
  · intro included
    exact ⟨quotientMapFactorOfIncluded included⟩

/-- Quotient-map-preserving factors are unique as functions. -/
theorem quotient_map_factor_unique
    {X : Type u} {S T : Setoid X}
    (f g : QuotientMapFactor S T) :
    f.toFun = g.toFun := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact (f.commutes x).trans (g.commutes x).symm

/-- Every setoid quotient has its canonical factor to the indiscrete quotient. -/
def factorToIndiscrete {X : Type u} (S : Setoid X) :
    QuotientMapFactor S (indiscreteSetoid X) :=
  quotientMapFactorOfIncluded (by
    intro x y related
    trivial)

/-- The factor to the indiscrete quotient is the unique map preserving the
canonical quotient maps.  Thus the indiscrete quotient is terminal, not
initial, for this factorization direction. -/
theorem factorToIndiscrete_unique
    {X : Type u} (S : Setoid X)
    (factor : QuotientMapFactor S (indiscreteSetoid X)) :
    factor.toFun = (factorToIndiscrete S).toFun :=
  quotient_map_factor_unique factor (factorToIndiscrete S)

/-- A total relation also receives the reverse quotient-map-preserving factor
from the indiscrete quotient. -/
def factorFromIndiscreteOfTotal {X : Type u} (S : Setoid X)
    (total : SetoidTotal S) :
    QuotientMapFactor (indiscreteSetoid X) S :=
  quotientMapFactorOfIncluded (by
    intro x y _
    exact total x y)

/-- Every total setoid quotient is canonically equivalent to the indiscrete
quotient, with both maps preserving representatives. -/
def quotientEquivIndiscreteOfTotal {X : Type u} (S : Setoid X)
    (total : SetoidTotal S) :
    SimpleEquiv (Quotient S) (Quotient (indiscreteSetoid X)) where
  toFun := (factorToIndiscrete S).toFun
  invFun := (factorFromIndiscreteOfTotal S total).toFun
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    calc
      (factorFromIndiscreteOfTotal S total).toFun
          ((factorToIndiscrete S).toFun (Quotient.mk S x)) =
        (factorFromIndiscreteOfTotal S total).toFun
          (Quotient.mk (indiscreteSetoid X) x) := by
            exact _root_.congrArg
              (factorFromIndiscreteOfTotal S total).toFun
              ((factorToIndiscrete S).commutes x)
      _ = Quotient.mk S x :=
        (factorFromIndiscreteOfTotal S total).commutes x
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    calc
      (factorToIndiscrete S).toFun
          ((factorFromIndiscreteOfTotal S total).toFun
            (Quotient.mk (indiscreteSetoid X) x)) =
        (factorToIndiscrete S).toFun (Quotient.mk S x) := by
          exact _root_.congrArg (factorToIndiscrete S).toFun
            ((factorFromIndiscreteOfTotal S total).commutes x)
      _ = Quotient.mk (indiscreteSetoid X) x :=
        (factorToIndiscrete S).commutes x

/-! ## Equality projections and their reflexivity kernels -/

/-- A based relation equipped with a projection to ambient equality and a
chosen reflexive element.  The explicit base equation records the intended
pointing even though ambient equality proofs are proof-irrelevant in Lean. -/
structure ReflexiveEqualityProjection {A : Type u} (a : A)
    (R : A → Type v) : Type (max u v) where
  base : R a
  toEq : {b : A} → R b → a = b
  base_toEq : toEq base = rfl

/-- The chosen point in the based total space of a reflexive equality
projection. -/
def projectionCenter {A : Type u} {a : A} {R : A → Type v}
    (q : ReflexiveEqualityProjection a R) :
    BasedTotal R :=
  ⟨a, q.base⟩

/-- The kernel over reflexivity: relation witnesses at the base whose equality
projection is reflexivity. -/
abbrev ReflexivityKernel {A : Type u} {a : A} {R : A → Type v}
    (q : ReflexiveEqualityProjection a R) : Type v :=
  {r : R a // q.toEq r = rfl}

/-- The distinguished reflexivity-kernel element. -/
def reflexivityKernelCenter
    {A : Type u} {a : A} {R : A → Type v}
    (q : ReflexiveEqualityProjection a R) :
    ReflexivityKernel q :=
  ⟨q.base, q.base_toEq⟩

/-- Equality induction identifies the whole based total space with the
reflexivity kernel of any equality projection. -/
def projectionKernelEquiv
    {A : Type u} {a : A} {R : A → Type v}
    (q : ReflexiveEqualityProjection a R) :
    SimpleEquiv (BasedTotal R) (ReflexivityKernel q) where
  toFun := by
    rintro ⟨b, r⟩
    have h : a = b := q.toEq r
    cases h
    exact ⟨r, Subsingleton.elim _ _⟩
  invFun := fun r => ⟨a, r.1⟩
  left_inv := by
    rintro ⟨b, r⟩
    have h : a = b := q.toEq r
    cases h
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl

/-- The projection/kernel classification: unrestricted based elimination with
propositional beta exists exactly when the reflexivity kernel is contractible. -/
theorem projection_kernel_criterion
    {A : Type u} {a : A} {R : A → Type v}
    (q : ReflexiveEqualityProjection a R) :
    Nonempty
        (UnrestrictedBasedEliminator.{max u v, w}
          (projectionCenter q)) ↔
      IsContractible (ReflexivityKernel q) := by
  exact
    unrestricted_based_elimination_iff_contractible.trans
      (contractible_iff_of_equiv (projectionKernelEquiv q))

/-! ## The exact `PathRwQuot`/K criterion -/

/-- The based row of rewrite-quotiented computational paths from `a`. -/
abbrev PathRwQuotRow (A : Type u) (a : A) : A → Type u :=
  fun b => PathRwQuot A a b

/-- `PathRwQuot.toEq` as a reflexive equality projection. -/
noncomputable def pathRwQuotEqualityProjection (A : Type u) (a : A) :
    ReflexiveEqualityProjection a (PathRwQuotRow A a) where
  base := PathRwQuot.refl a
  toEq := fun x => PathRwQuot.toEq x
  base_toEq := PathRwQuot.toEq_refl a

/-- The chosen point of the based total space of `PathRwQuot`. -/
noncomputable def pathRwQuotCenter (A : Type u) (a : A) :
    BasedTotal (PathRwQuotRow A a) :=
  projectionCenter (pathRwQuotEqualityProjection A a)

/-- For loops, the equation `toEq x = rfl` is proof-irrelevant, so the
projection kernel is equivalent to the entire genuine loop quotient. -/
def pathRwQuotKernelEquivLoopQuot (A : Type u) (a : A) :
    SimpleEquiv
      (ReflexivityKernel (pathRwQuotEqualityProjection A a))
      (PathRwQuot A a a) where
  toFun := fun x => x.1
  invFun := fun x => ⟨x, Subsingleton.elim _ _⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    rfl

/-- Exact loop-quotient form of the projection/kernel criterion. -/
theorem pathRwQuot_elimination_iff_loop_quotient_contractible
    (A : Type u) (a : A) :
    Nonempty
        (UnrestrictedBasedEliminator.{max u u, w}
          (pathRwQuotCenter A a)) ↔
      IsContractible (PathRwQuot A a a) := by
  exact
    (projection_kernel_criterion
      (pathRwQuotEqualityProjection A a)).trans
      (contractible_iff_of_equiv
        (pathRwQuotKernelEquivLoopQuot A a))

/-- Local quotient-level axiom K at `a`: every `RwEq` loop class is the
reflexive class.  This is deliberately not a claim about raw paths, nor merely
ambient proof irrelevance. -/
def PathRwQuotLocalAxiomK (A : Type u) (a : A) : Prop :=
  ∀ x : PathRwQuot A a a, x = PathRwQuot.refl a

/-- Contractibility of the genuine loop quotient is exactly local
quotient-level axiom K. -/
theorem loop_quotient_contractible_iff_local_axiomK
    (A : Type u) (a : A) :
    IsContractible (PathRwQuot A a a) ↔
      PathRwQuotLocalAxiomK A a := by
  constructor
  · intro contraction x
    obtain ⟨center, contracts⟩ := contraction
    exact (contracts x).symm.trans (contracts (PathRwQuot.refl a))
  · intro localK
    refine ⟨PathRwQuot.refl a, ?_⟩
    intro x
    exact (localK x).symm

/-- Main `PathRwQuot` result: unrestricted based elimination with
propositional beta exists exactly when local quotient-level axiom K holds.  The
theorem neither asserts that `RwEq` always repairs metadata nor that it always
fails. -/
theorem pathRwQuot_elimination_iff_local_axiomK
    (A : Type u) (a : A) :
    Nonempty
        (UnrestrictedBasedEliminator.{max u u, w}
          (pathRwQuotCenter A a)) ↔
      PathRwQuotLocalAxiomK A a :=
  (pathRwQuot_elimination_iff_loop_quotient_contractible
    A a).trans
    (loop_quotient_contractible_iff_local_axiomK A a)

/-- Global quotient-level axiom K means local K at every point. -/
def PathRwQuotAxiomK (A : Type u) : Prop :=
  ∀ a : A, PathRwQuotLocalAxiomK A a

/-- Family-wide unrestricted based elimination for `PathRwQuot` is equivalent
to global quotient-level axiom K. -/
theorem pathRwQuot_global_elimination_iff_axiomK (A : Type u) :
    (∀ a : A,
      Nonempty
        (UnrestrictedBasedEliminator.{max u u, w}
          (pathRwQuotCenter A a))) ↔
      PathRwQuotAxiomK A := by
  constructor
  · intro elimination a
    exact (pathRwQuot_elimination_iff_local_axiomK
      A a).mp (elimination a)
  · intro axiomK a
    exact (pathRwQuot_elimination_iff_local_axiomK
      A a).mpr (axiomK a)

/-! ## Raw traces versus `RwEq` classes -/

/-- The raw reflexive path with no recorded step. -/
noncomputable def rawEmptyReflexivePath {A : Type u} (a : A) : Path a a :=
  Path.refl a

/-- The raw reflexive path with one explicit reflexivity step. -/
noncomputable def rawSingletonReflexivePath {A : Type u} (a : A) :
    Path a a :=
  Path.stepChain (rfl : a = a)

/-- Empty and singleton reflexive paths are distinct as raw `Path` records. -/
theorem raw_empty_ne_singleton_reflexive_path
    {A : Type u} (a : A) :
    rawEmptyReflexivePath a ≠ rawSingletonReflexivePath a := by
  exact Path.refl_ne_ofEq (A := A) a

/-- The singleton reflexivity trace rewrites to the empty trace.  This is an
actual primitive `transport_refl_beta` certificate, not an appeal to the
current normalization function. -/
noncomputable def raw_singleton_rweq_empty_reflexive_path
    {A : Type u} (a : A) :
    RwEq (rawSingletonReflexivePath a)
      (rawEmptyReflexivePath a) := by
  simpa [rawEmptyReflexivePath, rawSingletonReflexivePath] using
    (RwEq.step <|
      Step.transport_refl_beta
        (A := PUnit) (B := fun _ : PUnit => A)
        (a := PUnit.unit) (x := a))

/-- The same equivalence in empty-to-singleton orientation. -/
noncomputable def raw_empty_rweq_singleton_reflexive_path
    {A : Type u} (a : A) :
    RwEq (rawEmptyReflexivePath a)
      (rawSingletonReflexivePath a) :=
  rweq_symm (raw_singleton_rweq_empty_reflexive_path a)

/-- The raw distinction disappears under the canonical `RwEq` quotient map. -/
theorem raw_empty_singleton_same_pathRwQuot_class
    {A : Type u} (a : A) :
    (Quot.mk _ (rawEmptyReflexivePath a) :
        PathRwQuot A a a) =
      Quot.mk _ (rawSingletonReflexivePath a) := by
  exact Quot.sound
    (rweqProp_of_rweq
      (raw_empty_rweq_singleton_reflexive_path a))

/-! ## Pointed subsingletons and genuine loop quotients -/

/-- On a pointed type whose every point is the base, every raw loop is
`RwEq`-equivalent to reflexivity.  The proof inspects the stored trace, turns
each step into an explicit reflexivity step by the point hypothesis, and erases
it with the primitive `transport_refl_beta` rewrite. -/
noncomputable def raw_loop_rweq_refl_of_all_eq
    {A : Type u} (a : A) (all_eq : ∀ x : A, x = a)
    (p : Path a a) :
    RwEq p (Path.refl a) := by
  cases p with
  | mk steps proof =>
      cases proof
      have eraseSingleton :
          RwEq (Path.stepChain (rfl : a = a)) (Path.refl a) := by
        simpa using
          (RwEq.step <|
            Step.transport_refl_beta
              (A := PUnit) (B := fun _ : PUnit => A)
              (a := PUnit.unit) (x := a))
      induction steps with
      | nil =>
          exact RwEq.refl (Path.refl a)
      | cons step tail ih =>
          cases step with
          | mk src tgt stepProof =>
              have src_eq : src = a := all_eq src
              have tgt_eq : tgt = a := all_eq tgt
              cases src_eq
              cases tgt_eq
              have proof_eq : stepProof = (rfl : a = a) :=
                Subsingleton.elim _ _
              cases proof_eq
              have split :
                  Path.mk
                      (_root_.ComputationalPaths.Step.mk a a rfl :: tail)
                      rfl =
                    Path.trans
                      (Path.stepChain (rfl : a = a))
                      (Path.mk tail rfl) := by
                rfl
              exact
                rweq_trans (rweq_of_eq split)
                  (rweq_trans
                    (rweq_trans
                      (rweq_trans_congr_left _ eraseSingleton)
                      (rweq_of_step (Step.trans_refl_left _)))
                    ih)

/-- The genuine loop quotient of a pointed subsingleton is contractible. -/
theorem loop_quotient_contractible_of_all_eq
    {A : Type u} (a : A) (all_eq : ∀ x : A, x = a) :
    IsContractible (PathRwQuot A a a) := by
  refine ⟨PathRwQuot.refl a, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  exact
    (Quotient.sound
      (rweqProp_of_rweq
        (raw_loop_rweq_refl_of_all_eq a all_eq p))).symm

/-- Every point of the current one-constructor circle is its base. -/
theorem current_circle_all_eq (x : Circle.{u}) :
    x = circleBase := by
  cases x
  rfl

/-- Every point of the current torus representation, a product of two
one-constructor circles, is its base. -/
theorem current_torus_all_eq (x : Torus.{u}) :
    x = torusBase := by
  obtain ⟨x₁, x₂⟩ := x
  cases x₁
  cases x₂
  rfl

/-- The genuine `PathRwQuot` fundamental group of the current
one-constructor circle is contractible. -/
theorem genuine_circle_piOne_contractible :
    IsContractible
      (PathRwQuot Circle.{u} circleBase circleBase) :=
  loop_quotient_contractible_of_all_eq
    circleBase current_circle_all_eq

/-- The genuine `PathRwQuot` fundamental group of the current product torus
representation is contractible. -/
theorem genuine_torus_piOne_contractible :
    IsContractible
      (PathRwQuot Torus.{u} torusBase torusBase) :=
  loop_quotient_contractible_of_all_eq
    torusBase current_torus_all_eq

/-- Hence the current genuine circle quotient satisfies local quotient-level
axiom K. -/
theorem genuine_circle_local_axiomK :
    PathRwQuotLocalAxiomK Circle.{u} circleBase :=
  (loop_quotient_contractible_iff_local_axiomK
    Circle circleBase).mp genuine_circle_piOne_contractible

/-- Hence the current genuine torus quotient satisfies local quotient-level
axiom K. -/
theorem genuine_torus_local_axiomK :
    PathRwQuotLocalAxiomK Torus.{u} torusBase :=
  (loop_quotient_contractible_iff_local_axiomK
    Torus torusBase).mp genuine_torus_piOne_contractible

/-! ## Synthetic winding quotients and no-bridge theorems -/

/-- Accurate public name for the synthetic circle expression quotient by
winding number. -/
abbrev SyntheticCircleWindingQuotient : Type u :=
  circleCompPathPiOne.{u}

/-- Accurate public name for the synthetic product of two circle winding
quotients used by the torus presentation. -/
abbrev SyntheticTorusWindingQuotient : Type u :=
  torusPiOne.{u}

/-- Accurate public name for the genuine circle `PathRwQuot` loop fiber. -/
abbrev GenuineCirclePathRwQuot : Type u :=
  PathRwQuot Circle.{u} circleBase circleBase

/-- Accurate public name for the genuine torus `PathRwQuot` loop fiber. -/
abbrev GenuineTorusPathRwQuot : Type u :=
  PathRwQuot Torus.{u} torusBase torusBase

/-- Integers are not contractible. -/
theorem int_not_contractible : ¬ IsContractible Int := by
  intro contraction
  have zero_eq_one : (0 : Int) = 1 :=
    IsContractible.all_eq contraction 0 1
  have zero_ne_one : (0 : Int) ≠ 1 := by decide
  exact zero_ne_one zero_eq_one

/-- Integer pairs are not contractible. -/
theorem int_prod_not_contractible :
    ¬ IsContractible (Int × Int) := by
  intro contraction
  have zero_eq_one : ((0, 0) : Int × Int) = (1, 0) :=
    IsContractible.all_eq contraction (0, 0) (1, 0)
  have zero_ne_one : ((0, 0) : Int × Int) ≠ (1, 0) := by decide
  exact zero_ne_one zero_eq_one

/-- The synthetic circle winding quotient is noncontractible because it is
equivalent to `Int`. -/
theorem synthetic_circle_winding_quotient_not_contractible :
    ¬ IsContractible SyntheticCircleWindingQuotient.{u} := by
  intro contraction
  exact int_not_contractible
    ((contractible_iff_of_equiv
      circleCompPathPiOneEquivInt).mp contraction)

/-- The synthetic torus winding quotient is noncontractible because it is
equivalent to `Int × Int`. -/
theorem synthetic_torus_winding_quotient_not_contractible :
    ¬ IsContractible SyntheticTorusWindingQuotient.{u} := by
  intro contraction
  exact int_prod_not_contractible
    ((contractible_iff_of_equiv
      torusPiOneEquivIntProdSimple).mp contraction)

/-- No equivalence can bridge the current genuine circle `PathRwQuot` and the
nontrivial synthetic winding quotient.  This is the strongest exact statement
for the repository's `SimpleEquiv` interface; arbitrary noninvertible functions
are not excluded. -/
theorem no_circle_genuine_synthetic_bridge :
    ¬ Nonempty
      (SimpleEquiv GenuineCirclePathRwQuot.{u}
        SyntheticCircleWindingQuotient.{u}) := by
  rintro ⟨bridge⟩
  exact synthetic_circle_winding_quotient_not_contractible
    ((contractible_iff_of_equiv bridge).mp
      genuine_circle_piOne_contractible)

/-- No equivalence can bridge the current genuine torus `PathRwQuot` and the
nontrivial synthetic product winding quotient. -/
theorem no_torus_genuine_synthetic_bridge :
    ¬ Nonempty
      (SimpleEquiv GenuineTorusPathRwQuot.{u}
        SyntheticTorusWindingQuotient.{u}) := by
  rintro ⟨bridge⟩
  exact synthetic_torus_winding_quotient_not_contractible
    ((contractible_iff_of_equiv bridge).mp
      genuine_torus_piOne_contractible)

end MetadataRepair
end Path
end ComputationalPaths
