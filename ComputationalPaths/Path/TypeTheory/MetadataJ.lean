/-
# Equality refinements, metadata fibers, and based elimination

This module isolates the abstract obstruction behind trace-sensitive path
induction.  An equality refinement stores an ambient equality together with
observable metadata.  Unrestricted based elimination with propositional beta
is classified by contractibility of the based total space, and that total
space is equivalent to the metadata fiber over reflexivity.

The final sections instantiate the classification with the step lists carried
by `Path`, and with a subtype enforcing composability.  Empty and singleton
reflexive traces remain distinct in both cases.  Thus the obstruction is
visible noncanonical metadata, not failure of composability.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace MetadataJ

universe u v w

/-! ## Equality refinements and their based total spaces -/

/-- Equality from `a` to `b`, decorated by metadata that may depend on the
endpoint and on the equality proof. -/
abbrev EqualityRefinement {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) (b : A) : Type v :=
  PSigma (fun h : a = b => M b h)

/-- The total space of a based relation row `R`. -/
abbrev BasedTotal {A : Type u} (R : A → Type v) : Type (max u v) :=
  Σ b : A, R b

/-- The based total space of equality decorated by `M`. -/
abbrev MetadataTotal {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) : Type (max u v) :=
  BasedTotal (EqualityRefinement a M)

/-- The chosen reflexive point of a metadata total space. -/
def metadataCenter {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) (m₀ : M a rfl) :
    MetadataTotal a M :=
  ⟨a, rfl, m₀⟩

/-! ## Based elimination and contractibility -/

/-- Unrestricted elimination from a chosen base point into every motive in
`Type v`, together with a propositional beta equation at that point. -/
structure UnrestrictedBasedEliminator {X : Type u} (base : X) where
  eliminate : (C : X → Type v) → C base → (x : X) → C x
  beta : ∀ (C : X → Type v) (d : C base), eliminate C d base = d

/-- A contraction with a specified center. -/
def ContractsAt {X : Type u} (center : X) : Prop :=
  ∀ x : X, center = x

/-- Contractibility with an unspecified center. -/
def IsContractible (X : Type u) : Prop :=
  ∃ center : X, ContractsAt center

namespace IsContractible

variable {X : Type u}

/-- Every two points of a contractible type are equal. -/
theorem all_eq (h : IsContractible X) (x y : X) : x = y := by
  obtain ⟨center, contraction⟩ := h
  exact (contraction x).symm.trans (contraction y)

end IsContractible

/-- An unrestricted eliminator contracts its domain to its base point.  The
contraction motive is the standard one; the beta field additionally records
its value at the center. -/
def contractionOfEliminator {X : Type u} {base : X}
    (J : UnrestrictedBasedEliminator.{u, v} base) : ContractsAt base :=
  fun x =>
    (J.eliminate
      (fun y => ULift.{v, 0} (PLift (base = y)))
      (ULift.up (PLift.up rfl)) x).down.down

/-- A specified contraction defines unrestricted based elimination by
transport.  Proof irrelevance for equality yields propositional beta even when
the supplied contraction does not compute judgmentally at its center. -/
noncomputable def eliminatorOfContraction {X : Type u} {base : X}
    (contraction : ContractsAt base) :
    UnrestrictedBasedEliminator.{u, v} base where
  eliminate := fun C d x => contraction x ▸ d
  beta := by
    intro C d
    have hcenter : contraction base = (rfl : base = base) :=
      Subsingleton.elim _ _
    rw [hcenter]

/-- Unrestricted based elimination with propositional beta exists exactly when
the chosen point contracts the whole domain. -/
theorem unrestricted_based_elimination_iff_contracts_at
    {X : Type u} {base : X} :
    Nonempty (UnrestrictedBasedEliminator.{u, v} base) ↔ ContractsAt base := by
  constructor
  · rintro ⟨J⟩
    exact contractionOfEliminator J
  · intro contraction
    exact ⟨eliminatorOfContraction contraction⟩

/-- Unrestricted based elimination with propositional beta exists exactly when
the inhabited domain is contractible. -/
theorem unrestricted_based_elimination_iff_contractible
    {X : Type u} {base : X} :
    Nonempty (UnrestrictedBasedEliminator.{u, v} base) ↔ IsContractible X := by
  constructor
  · rintro ⟨J⟩
    exact ⟨base, contractionOfEliminator J⟩
  · rintro ⟨center, contraction⟩
    have based : ContractsAt base :=
      fun x => (contraction base).symm.trans (contraction x)
    exact ⟨eliminatorOfContraction based⟩

/-! ## Equivalences and the metadata-fiber criterion -/

/-- Contractibility is invariant under a specified equivalence. -/
theorem contractible_iff_of_equiv {X : Type u} {Y : Type v}
    (e : SimpleEquiv X Y) :
    IsContractible X ↔ IsContractible Y := by
  constructor
  · rintro ⟨center, contraction⟩
    refine ⟨e center, ?_⟩
    intro y
    exact (_root_.congrArg e.toFun (contraction (e.invFun y))).trans
      (e.right_inv y)
  · rintro ⟨center, contraction⟩
    refine ⟨e.invFun center, ?_⟩
    intro x
    exact (_root_.congrArg e.invFun (contraction (e.toFun x))).trans
      (e.left_inv x)

/-- The total space of equality decorated by `M` is equivalent to the
reflexivity metadata fiber. -/
def metadataTotalEquiv {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) :
    SimpleEquiv (MetadataTotal a M) (M a rfl) where
  toFun := fun ⟨b, h, m⟩ => by
    cases h
    exact m
  invFun := fun m => ⟨a, rfl, m⟩
  left_inv := by
    intro x
    obtain ⟨b, h, m⟩ := x
    cases h
    rfl
  right_inv := by
    intro m
    rfl

/-- Named metadata-fiber criterion: unrestricted based elimination with
propositional beta exists precisely when the metadata over reflexivity is
contractible. -/
theorem metadata_fiber_criterion {A : Type u} (a : A)
    (M : (b : A) → a = b → Type v) (m₀ : M a rfl) :
    Nonempty
        (UnrestrictedBasedEliminator.{max u v, w}
          (metadataCenter a M m₀)) ↔
      IsContractible (M a rfl) := by
  exact
    unrestricted_based_elimination_iff_contractible.trans
      (contractible_iff_of_equiv (metadataTotalEquiv a M))

/-- Move unrestricted based elimination along a pointed equivalence. -/
noncomputable def eliminatorAlongEquiv
    {X : Type u} {Y : Type v} {x₀ : X} {y₀ : Y}
    (e : SimpleEquiv X Y) (base_eq : e x₀ = y₀)
    (J : UnrestrictedBasedEliminator.{u, w} x₀) :
    UnrestrictedBasedEliminator.{v, w} y₀ := by
  apply eliminatorOfContraction
  intro y
  exact base_eq.symm.trans
    ((_root_.congrArg e.toFun
      (contractionOfEliminator J (e.invFun y))).trans (e.right_inv y))

/-! ## Motives factoring through equality -/

/-- Elimination data for one specified motive, with propositional beta. -/
structure BasedMotiveEliminator {X : Type u} (base : X)
    (C : X → Type v) where
  eliminate : C base → (x : X) → C x
  beta : ∀ d : C base, eliminate d base = d

/-- A motive on an equality refinement factors through the equality projection
when each fiber is equipped with an equivalence to a motive depending only on
the endpoint and equality proof. -/
structure EqualityMotiveFactorization {A : Type u} {a : A}
    {M : (b : A) → a = b → Type v}
    (C : MetadataTotal a M → Type w) where
  motive : (b : A) → a = b → Type w
  fiberEquiv :
    ∀ x : MetadataTotal a M,
      SimpleEquiv (C x) (motive x.1 x.2.1)

/-- Ordinary equality elimination, written separately so the factorization
theorem makes clear that metadata is never inspected. -/
def equalityProjectionEliminate {A : Type u} {a : A}
    (D : (b : A) → a = b → Type w) (d : D a rfl)
    {b : A} (h : a = b) : D b h := by
  cases h
  exact d

@[simp] theorem equalityProjectionEliminate_beta
    {A : Type u} {a : A}
    (D : (b : A) → a = b → Type w) (d : D a rfl) :
    equalityProjectionEliminate D d (rfl : a = a) = d :=
  rfl

/-- Every motive factoring through the equality projection admits based
elimination with propositional beta, independently of whether unrestricted
metadata-sensitive elimination exists. -/
noncomputable def factorized_motive_eliminator
    {A : Type u} {a : A}
    {M : (b : A) → a = b → Type v} {m₀ : M a rfl}
    {C : MetadataTotal a M → Type w}
    (factorization : EqualityMotiveFactorization C) :
    BasedMotiveEliminator (metadataCenter a M m₀) C where
  eliminate := fun c x =>
    (factorization.fiberEquiv x).invFun
      (equalityProjectionEliminate factorization.motive
        ((factorization.fiberEquiv (metadataCenter a M m₀)).toFun c)
        x.2.1)
  beta := by
    intro c
    change
      (factorization.fiberEquiv (metadataCenter a M m₀)).invFun
          ((factorization.fiberEquiv (metadataCenter a M m₀)).toFun c) = c
    exact
      (factorization.fiberEquiv (metadataCenter a M m₀)).left_inv c

/-- The strict pullback of an equality motive is a factorized motive. -/
noncomputable def strictEqualityMotiveFactorization
    {A : Type u} {a : A}
    {M : (b : A) → a = b → Type v}
    (D : (b : A) → a = b → Type w) :
    EqualityMotiveFactorization
      (fun x : MetadataTotal a M => D x.1 x.2.1) where
  motive := D
  fiberEquiv := fun _ => SimpleEquiv.refl _

/-! ## `Path` as list-valued equality metadata -/

/-- The visible metadata carried by a computational path: an arbitrary list of
elementary steps. -/
abbrev TraceMetadata {A : Type u} {a : A}
    (_b : A) (_h : a = _b) : Type u :=
  List (_root_.ComputationalPaths.Step A)

/-- `Path a b` and equality decorated by a list of steps contain exactly the
same fields, in opposite order. -/
def pathRefinementEquiv {A : Type u} (a b : A) :
    SimpleEquiv (Path a b) (EqualityRefinement a TraceMetadata b) where
  toFun := fun p => ⟨p.proof, p.steps⟩
  invFun := fun p => Path.mk p.2 p.1
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- The based total space of `Path` is equivalent to the metadata-refinement
total space. -/
def pathBasedTotalEquiv {A : Type u} (a : A) :
    SimpleEquiv
      (BasedTotal (fun b => Path a b))
      (MetadataTotal a TraceMetadata) where
  toFun := fun ⟨b, p⟩ => ⟨b, (pathRefinementEquiv a b).toFun p⟩
  invFun := fun ⟨b, p⟩ => ⟨b, (pathRefinementEquiv a b).invFun p⟩
  left_inv := by
    intro x
    obtain ⟨b, p⟩ := x
    simp only [SimpleEquiv.left_inv]
  right_inv := by
    intro x
    obtain ⟨b, p⟩ := x
    simp only [SimpleEquiv.right_inv]

/-- The empty reflexive computational path is the chosen center. -/
noncomputable def pathCenter {A : Type u} (a : A) :
    BasedTotal (fun b => Path a b) :=
  ⟨a, Path.refl a⟩

@[simp] theorem pathBasedTotalEquiv_center {A : Type u} (a : A) :
    pathBasedTotalEquiv a (pathCenter a) =
      metadataCenter a TraceMetadata ([] :
        List (_root_.ComputationalPaths.Step A)) :=
  rfl

/-- Empty trace metadata and a singleton reflexive step are distinct. -/
theorem empty_ne_singleton_reflexive_step {A : Type u} (a : A) :
    ([] : List (_root_.ComputationalPaths.Step A)) ≠
      [_root_.ComputationalPaths.Step.mk a a rfl] := by
  simp

/-- The reflexivity trace-metadata fiber is not contractible. -/
theorem trace_metadata_not_contractible {A : Type u} (a : A) :
    ¬ IsContractible
      (TraceMetadata (a := a) a (rfl : a = a)) := by
  intro contraction
  exact empty_ne_singleton_reflexive_step a
    (IsContractible.all_eq contraction [] [
      _root_.ComputationalPaths.Step.mk a a rfl])

/-- The no-`J` result for `Path`, derived by transporting a hypothetical
eliminator to the equality refinement and applying the generic metadata-fiber
criterion. -/
theorem path_no_unrestricted_based_eliminator
    {A : Type u} (a : A) :
    ¬ Nonempty
      (UnrestrictedBasedEliminator.{max u u, w} (pathCenter a)) := by
  rintro ⟨pathJ⟩
  let refinementJ :
      UnrestrictedBasedEliminator.{max u u, w}
        (metadataCenter a TraceMetadata
          ([] : List (_root_.ComputationalPaths.Step A))) :=
    eliminatorAlongEquiv (pathBasedTotalEquiv a)
      (pathBasedTotalEquiv_center a) pathJ
  have fiberContr :
      IsContractible
        (TraceMetadata (a := a) a (rfl : a = a)) :=
    (metadata_fiber_criterion a TraceMetadata
      ([] : List (_root_.ComputationalPaths.Step A))).mp
      ⟨refinementJ⟩
  exact trace_metadata_not_contractible a fiberContr

/-! ## Composability does not remove the obstruction -/

/-- A list of steps is composable from `start` to `finish` when each visible
source is the current endpoint and the final endpoint is `finish`. -/
def ListComposableFrom {A : Type u} (start : A) :
    List (_root_.ComputationalPaths.Step A) → A → Prop
  | [], finish => start = finish
  | step :: rest, finish =>
      step.src = start ∧ ListComposableFrom step.tgt rest finish

/-- Visible trace lists satisfying the intrinsic chain condition. -/
abbrev ComposableTrace {A : Type u} (start finish : A) : Type u :=
  {steps : List (_root_.ComputationalPaths.Step A) //
    ListComposableFrom start steps finish}

/-- The empty well-formed reflexive trace. -/
def emptyComposableTrace {A : Type u} (a : A) :
    ComposableTrace a a :=
  ⟨[], rfl⟩

/-- The singleton reflexive step is also a well-formed composable trace. -/
def singletonComposableRefl {A : Type u} (a : A) :
    ComposableTrace a a :=
  ⟨[_root_.ComputationalPaths.Step.mk a a rfl], by
    simp [ListComposableFrom]⟩

/-- The two well-formed reflexive traces are observably distinct. -/
theorem empty_composable_ne_singleton {A : Type u} (a : A) :
    emptyComposableTrace a ≠ singletonComposableRefl a := by
  intro h
  have listsEqual := _root_.congrArg Subtype.val h
  simp [emptyComposableTrace, singletonComposableRefl] at listsEqual

/-- Even the composable reflexivity fiber is noncontractible. -/
theorem composable_trace_not_contractible {A : Type u} (a : A) :
    ¬ IsContractible (ComposableTrace a a) := by
  intro contraction
  exact empty_composable_ne_singleton a
    (IsContractible.all_eq contraction
      (emptyComposableTrace a) (singletonComposableRefl a))

/-- Equality metadata restricted to intrinsically composable traces. -/
abbrev ComposableTraceMetadata {A : Type u} (a : A)
    (b : A) (_h : a = b) : Type u :=
  ComposableTrace a b

/-- Enforcing composability alone still does not permit unrestricted
metadata-sensitive based elimination with propositional beta. -/
theorem composable_trace_no_unrestricted_based_eliminator
    {A : Type u} (a : A) :
    ¬ Nonempty
      (UnrestrictedBasedEliminator.{max u u, w}
        (metadataCenter a (ComposableTraceMetadata a)
          (emptyComposableTrace a))) := by
  intro J
  have fiberContr : IsContractible (ComposableTrace a a) :=
    (metadata_fiber_criterion a (ComposableTraceMetadata a)
      (emptyComposableTrace a)).mp J
  exact composable_trace_not_contractible a fiberContr

/-! ## Substantive computational-path certificate -/

/-- A genuine arithmetic reassociation step. -/
noncomputable def metadataAssocPath (x y z : Nat) :
    Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Nat.add_assoc x y z)

/-- A genuine inner commutation under the context `x + -`. -/
noncomputable def metadataInnerPath (x y z : Nat) :
    Path (x + (y + z)) (x + (z + y)) :=
  Path.congrArg (fun t => x + t) (Path.ofEq (Nat.add_comm y z))

/-- A two-step computational trace: reassociate, then commute the inner
summands. -/
noncomputable def metadataTwoStepPath (x y z : Nat) :
    Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (metadataAssocPath x y z) (metadataInnerPath x y z)

@[simp] theorem metadataTwoStepPath_length (x y z : Nat) :
    (metadataTwoStepPath x y z).steps.length = 2 := by
  simp [metadataTwoStepPath, metadataAssocPath, metadataInnerPath,
    Path.congrArg]

/-- Inverse cancellation of the two-step trace is a genuine `RwEq`
certificate from the LND_EQ-TRS system. -/
noncomputable def metadataTwoStep_cancel (x y z : Nat) :
    RwEq
      (Path.trans (metadataTwoStepPath x y z)
        (Path.symm (metadataTwoStepPath x y z)))
      (Path.refl ((x + y) + z)) :=
  rweq_cmpA_inv_right (metadataTwoStepPath x y z)

/-- Concrete data and nontrivial computational-path evidence packaged for the
metadata case study. -/
structure MetadataTraceCertificate where
  x : Nat
  y : Nat
  z : Nat
  route : Path ((x + y) + z) (x + (z + y))
  routeLength : route.steps.length = 2
  cancellation :
    RwEq (Path.trans route (Path.symm route)) (Path.refl ((x + y) + z))

/-- Build the certificate from the genuine two-step route. -/
noncomputable def MetadataTraceCertificate.build
    (x y z : Nat) : MetadataTraceCertificate where
  x := x
  y := y
  z := z
  route := metadataTwoStepPath x y z
  routeLength := metadataTwoStepPath_length x y z
  cancellation := metadataTwoStep_cancel x y z

/-- A concrete certificate used by the companion artifact. -/
noncomputable def metadataTraceCertificate345 :
    MetadataTraceCertificate :=
  MetadataTraceCertificate.build 3 4 5

end MetadataJ
end Path
end ComputationalPaths
