# Full weak omega-groupoid construction: live obligations

Status: in progress. The completed associativity certificate remains in
`ASSOCIATIVITY_HIGHER_COHERENCE.md`; it is not the theorem specified here.

Current milestone: the normalized native endomorphism operad now has a
verified contraction and an actual algebra action on the native tower.
Contraction-selected adjacent operations now have coinductive invertibility
and explicit comparison cells to the earlier native operations. The full
associativity/pentagon/interchange certificate comparisons and the standard
free-category definition bridge remain completion gates.

## Mathematical target

Use a precise globular-operadic definition, with an algebra over an appropriate
contractible globular operad and weak invertibility in every positive
dimension. The exact normalization/contraction and invertibility conventions
must be taken from the selected definition, not reconstructed from the name
"weak omega-groupoid".

Primary references:

- van den Berg and Garner, [Types are weak omega-groupoids](https://arxiv.org/abs/0812.0298).
- Raftogianis, [Operations in Leinster's Weak omega-Category Operad](https://arxiv.org/abs/1711.07958).

The second reference describes Leinster's initial operad with contraction and
how composition and coherence arise from its operations. The first concerns
iterated identity types. Applying its conclusion directly to our trace type
would require a comparison theorem; it is not an imported result about our
`Path`/`RwEq` syntax.

## Non-negotiable boundary

The construction must include:

1. A genuine globular set: every successor cell has boundaries in the
   immediately preceding dimension, with both globularity equations.
2. Explicit correspondence with the actual computational-path two-skeleton.
   `RealizesPathSkeleton` currently requires equivalences at dimensions 0, 1
   and 2 and preservation of all four boundary maps. Thus a thin quotient or
   unrelated generic completion cannot silently stand in for the raw traces.
3. The chosen globular operad, its arities/pasting diagrams, lawful substitution
   and units, and the required contraction structure over arities.
4. An action of that operad on the constructed carrier, satisfying its actual
   algebra laws. A list of binary composition functions is insufficient.
5. All-dimensional weak invertibility, including coherent inverse witnesses
   according to the selected framework.
6. Low-dimensional correspondence for identity, composition, associators,
   unitors, cancellation, pentagon and interchange; the existing higher
   associativity certificate should be reused or compared explicitly.

Operadic contraction is not a licence to fill every pair of parallel cells
in the carrier. Any freely adjoined coherence cells must be identified as
part of the construction, and all action/substitution laws must still be
proved. A finite-dimensional package does not complete this objective.

## Current verified foundation

`ComputationalPaths/Path/OmegaGroupoid/GlobularFoundations.lean` defines:

- `GlobularSet` with source/target maps and both globularity laws;
- dimension-sensitive parallel pairs, boundary objects and cell fibres;
- globular maps, identity/composition and preservation of parallelism;
- a lawful Mathlib category instance for globular sets, iterated boundary
  preservation, and valid composition boundaries in every dimension;
- boundary/arity lifting problems and contractions on globular maps, with
  explicit identity and composition constructions for contractions;
- the concrete `PathOne`/`PathTwo` two-skeleton with genuine `Path` and `RwEq`
  data, its boundary laws, an associator cell and vertical composition;
- `RealizesPathSkeleton`, the required correspondence interface.

These definitions and lemmas build without proof holes. The candidate native
carrier described below now instantiates the correspondence interface and
has coinductive invertibility for its specified adjacent operations. The
endomorphism operad action is now proved below, along with selected adjacent
operations, invertibility for them, and comparison cells to those specified
native operations. Full coherence compatibility remains unproved.

```sh
lake build ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
lake build ComputationalPaths.Path.OmegaGroupoid.NativeGlobularTower
lake env lean scripts/FullOmegaAudit.lean
```

The lifting interface follows the elementwise positive-dimensional square
in Raftogianis, Definition 4.5 (pp. 35–36). It requires a specified arity cell
and both commuting-boundary equations; it is not a general filler for domain
parallel pairs. The labelled-pasting monad is now constructed below. Its free
strict-category characterization, globular operad and
algebra action still require verification. The audit is not a completion
certificate for the full weak omega-groupoid objective.

The subsequent `GlobularPasting.lean` constructs a genuinely recursive labelled
pasting carrier: objects at dimension zero, then composable chains of smaller
diagrams in hom globular sets. Its adjacent boundaries, both globularity laws,
and identities in every dimension are checked. The hom construction preserves
the original cells with fixed zero-dimensional endpoints and lowers dimension
at every recursion. This carrier now has a proved labelled-pasting monad.
Relabelling forms the checked Mathlib endofunctor
`Pasting.pastingFunctor`, preserving both boundaries and respecting identity
and composite maps. The singleton inclusion `Pasting.singletonGlobular` is now
a boundary-preserving globular map, natural in the original globular set
(`singleton_natural`) and injective at every dimension (`singleton_injective`).
The partial extractor `atom?` recovers original cells from these singleton
diagrams; it rejects empty and composite chains. This provides the candidate
unit without erasing original cells. Flattening is now constructed as
described below, with the full monad laws; the free strict-category universal
property remains to be established.

The natural unit is now verified cartesian. `atom_map` proves that relabelling
commutes with extraction of a generator, and `singleton_of_atom` proves that
successful extraction characterizes singleton diagrams. Consequently
`singleton_cartesian` provides the unique cell lift for every unit naturality
square, without assuming the relabelling map is injective.
`singleton_globular_pullback` assembles these lifts into a globular map,
checks both adjacent boundaries, and proves the unique lifting property for
arbitrary globular cones. This establishes the actual universal property of
the unit squares. Pullback preservation is established below; cartesianness
of multiplication is now established by `flatten_globular_pullback` below.

`GlobularSet.pullback` now constructs matched pairs of original cells with
componentwise boundaries, both globularity laws, and no added fillers.
Its projections, choice-free cone lift, and `pullback_universal` establish
the unique globular lifting property. `Pasting.pullbackComparison` is the
canonical map from pastings of matched labels to matched pastings; its two
projection equations and exact action on singleton labels are checked.
Its invertibility is now proved below; the comparison's existence and these
projection equations alone would not establish pullback preservation.

For the dimension-recursive inverse, `pullbackHomForward` and
`pullbackHomBackward` now identify a fixed-endpoint hom of the pullback with
the pullback of the two fixed-endpoint homs over the shifted common target.
Both are globular maps; both inverse equations and the two backward
projection equations are proved. The use of the shifted target avoids
silently identifying distinct endpoint fibres.

`Chain.zipAlong` now matches chains over different vertex sets, deriving
internal vertex matches and heterogeneous label equalities from the common
relabelled chain. Its two projection theorems recover the original chains.
`pullback_pasting_exists` uses this zipper and the hom-pullback inverse by
dimension recursion to reconstruct a pasting from any two matching pastings.
`pullbackComparison_surjective` therefore proves surjectivity at every
dimension, including empty chains. `Chain.mapAlong_joint_injective` and the
dimension-recursive `pullback_pasting_ext` now prove that the two projections
jointly determine the entire pasting. `pullbackComparison_injective` completes
the cellwise bijection; `pullbackComparisonInverse` checks both globular
boundaries of the inverse, and `pullbackComparisonIso` is an actual Mathlib
isomorphism. Finally, `pasting_pullback_universal` proves the full unique
globular lifting property for each image pullback cone. Thus the pasting
functor preserves the constructed globular pullbacks, not merely their
zero-dimensional vertices. Multiplication cartesianness is established below.

For multiplication, the chain-segmentation ingredient is now verified.
`Chain.split_mapAlong` lifts any specified split of a relabelled chain;
`split_mapAlong_unique` determines its actual cut vertex and original
segments without an injectivity assumption. `lift_bind_mapAlong` lifts an
entire nested-chain segmentation, retaining empty inner chains explicitly.
`bind_mapAlong_joint_injective` and `bind_cartesian` prove uniqueness of this
chain-level multiplication lift. These are not yet a proof about the full
globular `flattenGlobular` by themselves.

The exact interface to that multiplication is now checked:
`recursive_fold_pack` and `recursive_fold_unpack` identify the implemented
root-context evaluator's fold with chain substitution. `flattenHom` names
its actual hom-context evaluator, and `flatten_horizontal_segments` expresses
`flattenGlobular` in every positive dimension as concatenation of unpacked,
evaluated hom labels. `flattenHom_natural`, `unpackFibre_map_hom`, and
`flattenHom_segments_natural` check relabelling of these exact segments.
This does not replace the hom of the pasting carrier with a different
hom-pasting type. Unique lifting for these recursive hom evaluations is now
proved by `evaluate_unique_lift`, as described below.

`flattenHom_factor` now identifies that hom evaluator with the restriction
of `flattenGlobular` along `homPastingInclusion`; the inclusion itself is
verified injective in every dimension and natural under relabelling.
`HomFlattenCartesianAt f n` states the exact unique-lifting property
with both the output hom cell and relabelled nested diagram prescribed.
Its dimension-zero case is proved by the identity evaluator, and
`homFlattenCartesianAt` now establishes every dimension using the actual
hom-context instance of `evaluate_unique_lift`.

The bottom-cut primitives now have verified unique lifts in every positive
dimension. `horizontal_unit_cartesian` reflects the actual empty-chain
`cutUnit .bottom`, and `horizontal_cut_cartesian` reconstructs the original
intermediate vertex and both horizontal factors from a specified factorization
after relabelling. These proofs allow non-injective relabellings and preserve
empty factors. Higher-cut composition lifting is now established below;
the resulting positive-dimensional hom-evaluation lifting theorem remains open.

Unit lifting now extends to every cut. `cutUnit_retract_of_map` proves that
if a relabelled diagram is a cut unit, the original diagram is the cut unit
on its own cut source. It descends through actual hom globular sets using
`Chain.map_retract_of_mapAlong`, including the matching endpoint equations.
`cutUnit_cartesian` gives the unique prescribed lift for arbitrary `Cut n`,
with `cutSource c p` as its explicit preimage. No injectivity hypothesis or
general filler is assumed. This completes the primitive unit part, not the
globular multiplication part.

The higher-cut factor representation is now checked. `CutPair` retains both
prescribed factors and their actual matching equation. `cutPairChain` aligns
these pairs through the shared boundary chain; its left/right projections and
`cutPairChain_roundtrip` recover the original data exactly.
`cutCompose_lift_pairs` proves that the implemented lifted-cut composition is
the chainwise composition of these retained pairs. This supplies the precise
representation for the recursive lifting proof described below.

`cutPairMap` now relabels both factors and their matching witness, and
`cutPairMap_compose` verifies compatibility with their actual composition.
`CutCompositionCartesian` states the uniform unique-lifting obligation for
a prescribed output and target factor pair. `cutCompositionCartesian_bottom`
proves this exact interface for every horizontal dimension.
`Chain.lift_mapAlong_square` assembles lifts of labels into a chain while
retaining its original vertices and prescribed relabelled labels.

That induction is now complete for primitive compositions.
`packCutPairChain` assembles higher-cut pairs, with verified composition,
round-trip, injectivity, and relabelling equations.
`cutComposition_lift_exists` constructs lifts through all cuts by descending
into actual homs and applying the chain assembly lemma.
`cutComposition_lift_unique` compares factor chains through both their
composites and their prescribed relabelled pairs, using the lower-cut
uniqueness theorem on each label. `cutComposition_cartesian` combines these
into the full unique-lifting statement for arbitrary `Cut n` and arbitrary
globular relabellings. Recursive evaluation and monad multiplication
cartesianness still require their own proof from these primitive results.

`CutOperations.Cartesian` now packages preservation and unique lifts of
primitive units and composable pairs for general cut-operation targets.
`mapGlobular_cartesian` instantiates it on the actual pasting relabellings
using the proved cut-unit and cut-composition theorems, with explicit
conversion between canonical-boundary and pasting-boundary factor pairs.
`Cartesian.unit_lift_hom` and `Cartesian.compose_lift_hom` derive the lifted
cells' fixed endpoints from the unit/composite equations.
`Cartesian.hom` therefore proves closure under genuine hom restriction,
including both existence and uniqueness; it does not postulate endpoint
fillers. This supplies the hom-stable premise needed for recursive-evaluation
lifting. Both that lifting theorem and multiplication cartesianness are now
proved below.

The evaluator's horizontal lifting steps are now explicit.
`Cartesian.horizontal_factor_lift` recovers a unique original intermediate
object and both fixed-endpoint factors from a prescribed factorization.
Their endpoint equations follow from the primitive composite's boundary
laws, and both raw relabelling equations are retained.
`Cartesian.horizontal_unit_lift` handles an empty fold by proving the
original endpoints coincide and identifying the actual original unit.
These supply the binary and empty cases for a fold-lifting induction;
the recursive-evaluation lifting proof now uses these cases below.

Arbitrary finite horizontal chains now have unique lifts:
`Cartesian.fold_lift` proves existence with explicit endpoint equations,
`Cartesian.fold_joint_injective` recovers a chain from its fold and relabelled
image, and `Cartesian.fold_unique_lift` combines these into the fixed-endpoint
pullback property. All three quantify over arbitrary dimension and require
the proved primitive `Cartesian` interface and compatible cut operations;
they do not require an injective object map.

`evaluate_lift` now lifts entire recursively labelled pastings by dimension
induction in arbitrary actual hom contexts. The induction combines the
horizontal fold lift with `Chain.lift_mapAlong_square`, applying its lower-
dimensional hypothesis to each original label. `evaluate_joint_injective`
proves uniqueness using the fold's joint injectivity and the lower-dimensional
label uniqueness; `evaluate_unique_lift` combines them. The exact naturality
helper `evaluate_map_id` connects the two evaluators and relabelling.

Instantiating this theorem with `mapGlobular_cartesian` gives
`flatten_cartesian`: the implemented multiplication has unique lifts in
every dimension. `flatten_globular_pullback` assembles these lifts into a
globular map, proves both boundary equations by cellwise uniqueness, and
establishes the unique lift for arbitrary globular cones. Together with the
existing monad laws, unit pullbacks, and functor pullback preservation, this
establishes the cartesian properties of this concrete labelled-pasting monad.
The standard free-strict-category identification, globular operad/action,
and compatibility with the native weak operations remain completion gates.

The collection construction now follows the slice presentation in
[Raftogianis, Definition 3.1 and Proposition 3.2, pp. 23–24](https://arxiv.org/pdf/1711.07958).
`GlobularSet.terminal` has a unique cell at every dimension and a unique map
from each globular set. `GlobularCollection` consists of an operation carrier
and an arity map into pastings of that terminal object. Its `application G`
is the actual pullback of the operation arity and the shape map from labelled
pastings of `G`; hence it retains both the operation and every input label.
`functor` and `arityTransformation` verify relabelling and naturality.
`arity_globular_pullback` proves that arity naturality is cartesian, while
`application_pullback_universal` proves that the induced collection functor
preserves globular pullbacks. `applicationTerminalIso` recovers the original
operation carrier at the terminal globular set, with `atTerminal_arity`
identifying its arity exactly. These are verified collection data, not an
operad: substitution, its monad laws, contraction, and the native algebra
action still need to be constructed. No equivalence of entire categories of
collections is asserted by the object-level terminal isomorphism alone.

`GlobularCollection.identity` selects singleton arities in all dimensions.
`identityApplication_lift` uses the proved singleton globular pullback to
recover an original cell from an identity-labelled operation.
`identityApplicationIso` proves both inverse equations as globular maps, and
`identityApplicationOut_natural` proves compatibility with every relabelling.
Thus the proposed substitution unit acts as the identity on globular sets.
The collection-level unit isomorphisms are now proved below; associativity
and the coherence laws remain separate obligations.

`GlobularCollection.substitute C D` now has the carrier of outer operations
labelled by inner operations. Its arity uses the actual pasting monad
multiplication on the inner arities. `substitution_match` checks the arity
equation for nested labelled applications, so `substitutionComparison` is a
globular map into the substituted collection's application. Its two
projection equations retain the nested operations and flatten only their
input diagrams; `substitutionComparison_natural` proves compatibility with
relabelling. `substitutionComparison_unique_lift` now recovers the complete
nested labelled operation uniquely: multiplication cartesianness recovers its
nested inputs, and pasting pullback preservation recovers its inner-operation
labels. `substitutionComparisonInverse` respects both globular boundaries by
uniqueness, and `substitutionComparisonIso` proves both inverse equations.
`substitutionFunctorIso` packages the existing naturality law into an actual
natural isomorphism between composed application functors and application of
the substituted collection. Substitution coherence, associativity, and the
eventual operad multiplication remain unproved.

`GlobularCollection.Hom` now requires a globular operation map preserving
the full arity map. Identity and composition form a lawful category.
`Hom.application` changes operations while retaining all input labels;
`Hom.transformation` is its natural transformation between application
functors. The application construction preserves identities, composition,
and the input projection. `Hom.application_cartesian` proves unique lifts
for its naturality squares at every dimension. These maps provide the typed
interface for the future operad unit and multiplication; neither map nor
its operad laws are assumed to exist merely from this interface.

`Hom.substitute` applies collection maps in both operation positions,
preserving the complete arity. `substitute_id` and `substitute_comp` establish
its identity and composition laws, and `substitute_comparison` proves that
the application comparison commutes with maps of both collections.
`leftUnitIso` and `rightUnitIso` are now isomorphisms of collections, not just
underlying carriers: the former uses the identity-application inverse and the
latter terminal recovery, with their arity equations proved from the two
pasting multiplication unit laws. `Hom.leftUnit_natural` and
`Hom.rightUnit_natural` prove naturality of both unitors. The arity-preserving
`associatorIso` now reassociates three substituted collections; its arity
equation uses `flatten_natural` and the actual `flatten_assoc` theorem.
`Hom.application_faithful` proves that terminal-labelled applications detect
equality of collection maps, providing a faithful check for future coherence
proofs. `Hom.associateInv_natural` now proves naturality in all three
collections by the comparison's naturality in operations and inputs.
`Hom.triangle_inv` proves triangle coherence in inverse-associator form,
using the actual singleton-input flattening law. `Hom.pentagon_inv` now proves
pentagon coherence for four collections in the same inverse-associator
orientation. Its proof separately preserves both operation layers and the
flattened inputs using relabelling composition, flattening naturality, and
flattening associativity. These verified structural equations alone still
do not construct the requested contractible operad or its native
computational-path action; the concrete construction is now supplied below.

The collection category now instantiates Mathlib's actual
`MonoidalCategory`. `substituteIso` transports isomorphisms through the
verified tensor map. `associate_natural`, `triangle`, and `pentagon` convert
the inverse-oriented equations into the standard forward orientation by
the proved isomorphism laws. `monoidalCategory` packages substitution as
tensor, the singleton collection as unit, and the verified associator and
unitors, including every required coherence field. This supplies a standard
lawful setting for an operad as a monoid in collections. The concrete
endomorphism monoid and its native action are now supplied below.

For any actual Mathlib `MonObj C` in this substitution category,
`operadUnit` and `operadMul` now construct labelled unit and multiplication
maps. They use the monoid's operation maps, the identity-application inclusion,
and the verified substitution comparison. `operadUnitTransformation` and
`operadMulTransformation` prove naturality under every input relabelling.
`operadUnit_arity` and `operadMul_arity` identify their input projections
with the singleton and flattening maps of the concrete pasting monad.
`operad_left_unit` and `operad_right_unit` now prove the two application-level
unit laws. Each checks operation equality using the actual `MonObj` unit law
and input equality using the corresponding singleton/flattening law, so no
input labels are discarded. `operad_assoc_operations` transports the monoid's
associativity equation through the actual inverse associator; `operad_assoc`
then proves application-level associativity, separately checking operations
and complete input diagrams. `operadMonad` packages these proved maps and
laws as a Mathlib monad. `operadArityMonadHom` is an actual monad morphism to
`Pasting.pastingMonad`, using the verified arity transformation. Its arity
naturality pullbacks are already covered by `arity_globular_pullback`.
`operadUnit_cartesian` now uniquely recovers an original cell using singleton
recovery and the retained operation. `operadMul_cartesian` uniquely recovers
the complete nested operation using the cartesian monoid multiplication map
and substitution comparison isomorphism. The two `_globular_pullback`
theorems establish unique lifts for arbitrary globular cones; the shared
`GlobularSet.square_globular_pullback` proof forces both boundary equations
by cellwise uniqueness. Together with application pullback preservation,
these prove the cartesian properties of the induced monad. The concrete
contractible operad/native action is now constructed below; this conditional
bridge alone is not the full weak omega-groupoid theorem.

`evaluate` now evaluates labelled diagrams by dimension recursion into a
target equipped with horizontal operations in all its iterated hom contexts
(`RecursiveComposition`). The evaluator is implemented, not a field assumed
in that interface: `evaluateGlobular` proves both boundary laws, and
`evaluate_singleton` recovers the original labels exactly under the explicit
right-unit law. No associativity or algebra law is inferred from this alone.
The actual pasting carrier has `horizontalComposition` at its root context;
`packFibre`/`unpackFibre` identify its horizontal chains with its genuine hom
cells in both directions. `horizontalComposition_fold` proves that this
concrete fold is precisely chain substitution in every dimension. These
operations now extend through every nested hom context using higher cuts;
the full multiplication laws are now verified below.

The hom-restriction mechanism is now proved for all cuts on arbitrary
globular sets. `CutBoundary` defines canonical boundaries by shifting the
actual tower and proves their naturality and compatibility with hom
inclusion. `CutOperations.hom` inherits composition and units one cut higher
from the parent, with checked fixed endpoints; `hom_compose_val` and
`hom_unit_val` show that the underlying cells are unchanged. `inContext`
iterates this restriction to any hom depth.

`canonical_source_eq_cutSource` and `canonical_target_eq_cutTarget` now prove
that the existing pasting boundaries agree with the canonical cuts on every
diagram. The proof identifies the shifted pasting carrier with chains of
hom-pasting labels and retains all those labels. `cutOperations` instantiates
the interface with the actual `cutCompose` and `cutUnit`; source and target
laws and both unit laws are checked for all cuts. These concrete operations
therefore restrict through arbitrary hom depth. `CutOperations.Compatible`
now records adjacent-boundary laws, proved for the actual pasting operations
by `cutOperations_compatible` and inherited through all hom contexts.
`recursiveComposition` supplies the concrete evaluator target with no
remaining composition-data hypothesis.

`flattenGlobular` is now an actual globular map from doubly nested labelled
pasting diagrams to ordinary labelled pasting diagrams, in every dimension.
`flatten_singleton` proves the first multiplication unit equation on all
diagrams, including empty and composite ones. Its proof uses the actual
right-unit law inherited through all hom contexts; it does not erase labels
or postulate an evaluator. `flatten_natural` now proves that relabelling and
flattening commute in every dimension, and `flattenNatTrans` packages this
as a Mathlib natural transformation from the doubled pasting functor to the
pasting functor. The proof uses actual preservation of cut composition and
units (`mapGlobular_preserves`), their inheritance to hom sets, and the
implemented evaluator's pre- and postcomposition laws.

`flatten_map_singleton` now proves the other unit equation on every labelled
diagram. The proof uses `homPastingInclusion`, a boundary- and
cut-operation-preserving map from the pasting carrier of a hom set into
the corresponding hom set of the original pasting carrier. Its singleton
factorization is exact. `evaluate_singletonLabels` and
`recursive_fold_single` recover all the original labels and chain structure,
including empty chains. `singletonNatTrans` packages the unit naturally;
`flatten_unit_left` and `flatten_unit_right` are both equations of globular
maps. `flatten_assoc` now proves multiplication associativity on triply
nested diagrams, and `pastingMonad` packages the endofunctor, natural unit,
natural multiplication, and all three equations as a Mathlib monad. The free
strict-category universal property and cartesian properties needed by the
chosen globular-operadic framework are not yet verified. A lawful monad
alone does not establish the required globular operad or its native action.

The algebraic extension property is now verified:
`existsUnique_preserving_extension` extends every globular labelling uniquely
to a map preserving all cut compositions and identities, for targets with
explicit compatibility, left/right unit, associativity, interchange,
unit-idempotence, and unit-compatibility laws. `preserves_recovered` derives
any preserving map by evaluation of its restriction to generators, and
`preserves_ext` proves uniqueness in every dimension. This is not yet an
identification of those target laws with an established strict omega-category
presentation, nor a proof of cartesianness or a native weak operadic action.

`evaluate_multiplication` now proves that evaluating a flattened diagram
agrees with evaluating its evaluated labels. Together with the generator unit
law, `cutOperationsAlgebra` packages every target satisfying the stated cut
laws as a Mathlib Eilenberg-Moore algebra for `pastingMonad`.
`preserves_evaluation` proves that cut-preserving maps intertwine these
actions. The audit instantiates this bridge on the actual labelled-pasting
cut operations. The reverse reconstruction of cut laws from arbitrary monad
algebras is not yet proved; this bridge does not give the native tower a weak
operadic action.

The multiplication associativity proof uses strict cut-operation
associativity and interchange inherited through every hom context, alongside
both unit laws. `CutOperations.fold_append` proves the evaluator's chain fold
respects concatenation; `evaluate_horizontal` applies this in every dimension
and hom context. `flatten_cutCompose_bottom` specializes it to the actual
flattening map. `CutOperations.fold_zipOver` now distributes higher-cut
composition through the horizontal fold. Its label and subchain matching
witnesses are supplied by `map_cut_composable` applied to the proved globular
evaluator, not postulated by the concrete theorem. The empty-chain case uses
`cutCompose_unit_idempotent`, proved for actual pasting identities and
inherited through all hom contexts. `evaluate_cutCompose` and
`flatten_cutCompose` therefore establish composition preservation at every
cut and dimension. `UnitCompatible` adds the explicit cross-dimensional
identity laws, proved by `cutUnit_compose` and `cutUnit_unit_reindex` and
inherited through hom contexts. `fold_unit` and `evaluate_cutUnit` then prove
identity preservation. `flatten_preserves` packages both preservation laws.
Finally, evaluation's pre- and postcomposition equations identify both
associativity composites with evaluation of the same labels. This proves
the actual multiplication equation rather than just binary associativity.

Endpoint-indexed chain substitution now has proved left/right unit and
associativity laws (`Chain.bind_single`, `Chain.bind_id`, `Chain.bind_assoc`).
Its interpretation by actual computational paths respects substitution
(`evalPathChain_bind`). These are ingredients for flattening nested diagrams,
and are separate from the now-verified full globular monad laws.

Horizontal composition along the zero-dimensional boundary is now defined
for diagrams in every positive dimension (`Pasting.horizontal`). Its exposed
endpoint fibres are exactly the chains in the existing pasting carrier;
`sourceZero_pack` and `targetZero_pack` verify their iterated globular endpoints.
Associativity, left/right units, adjacent-boundary compatibility, identity
compatibility and compatibility with relabelling are proved. The all-cut
operations and interchange laws are supplied below; these horizontal laws
alone do not give the free strict-category characterization.

Adjacent-boundary composition is now constructed separately by dimension
recursion (`Pasting.vertical`). Dimension one concatenates chains; higher
dimensions align the common boundary chain and recursively compose its labels
in hom globular sets. `Chain.zipOver` derives individual label compatibility
and intermediate-vertex equality from the supplied equality of boundary chains;
it does not assume fillers or erase labels. The checked source and target laws
package the result in its exact composite-boundary fibre (`verticalCell`).
Alignment distributes over concatenation (`Chain.zipOver_append`), an ingredient
for interchange. Both unit laws and associativity for this vertical operation
are now proved in every positive dimension (`vertical_left_unit`,
`vertical_right_unit`, `vertical_assoc`). Their equalities compare the complete
diagrams, not just boundary projections. The proofs lift the corresponding
label laws through boundary-aligned chains (`zipOver_map_left`,
`zipOver_map_right`, `zipOver_assoc`). The general intermediate-boundary
operations are described below, together with full interchange and monad laws.
The extreme-boundary interchange law is now checked separately:
`vertical_horizontal_interchange` commutes zero-boundary concatenation with
adjacent-boundary composition in all dimensions at least two. Its endpoint
fibre operation is identified with `vertical` by `pack_verticalFibre`; it is
not a disconnected replacement operation. This still leaves interchange
between arbitrary intermediate-dimensional compositions to construct.

`composeAt k n` now constructs composition in dimension `n+k+1` along a
boundary of dimension `k`, with no bound on either parameter. Its boundary
maps `sourceAt`/`targetAt` recursively truncate labels through hom globular
sets; at dimension gap one they agree with the existing adjacent boundary
maps (`sourceAt_adjacent`, `targetAt_adjacent`). The general operation has
proved source/target laws, identities (`identityAt`), both unit laws and
associativity. The audit checks arbitrary parameters and a dimension-nine
composition along dimension four. `sourceAt_eq_sourceIter` and
`targetAt_eq_targetIter` now identify the truncations directly with the existing
globular tower's iterated source and target, for arbitrary parameters. The
arithmetic transport `reindex` changes only the dimension expression, never the
diagram. One-step recursion, globularity and consecutive-lower-boundary laws
are also checked. Identification of the general composition/identity operations
with the previous special cases, their compatibility across truncation levels,
and interchange between every pair of distinct composition dimensions are
established below. The free strict omega-category characterization remains
a separate obligation from the verified monad equations.

Relabelling now preserves all arbitrary-boundary maps, identities and
compositions (`sourceAt_map`, `targetAt_map`, `map_identityAt`,
`map_composeAt_natural`). The latter derives composability after relabelling
from the original boundary equality; no injectivity or boundary-equality
reflection is assumed. The chain-level transport laws cover maps that change
both vertices and labels (`mapAlong_zipOver`) as well as label-only maps
(`map_zipOver`). These naturality laws alone do not imply cross-dimensional laws.

Taking adjacent source and target now preserves composition at every strictly
lower boundary (`dropSource_composeAt_boundary`, `dropTarget_composeAt_boundary`).
The lower-dimensional composability proof is derived from the original one.
The dimension-indexed `dropSource`/`dropTarget` operations are proved equal to
the existing source/target after arithmetic reindexing (`dropSource_eq`,
`dropTarget_eq`), and preserve the corresponding identity diagrams. All four
combinations of lower source/target with either adjacent boundary are checked.
The special-case identifications are now proved: `composeAt_horizontal` recovers
horizontal composition, `composeAt_adjacent_eq` recovers vertical composition
with its composability proof derived from the general one, and
`identityAt_adjacent`/`identityAt_step` identify the general identities with
iterates of the existing identity operation. `composeAt_horizontal_interchange`
extends interchange with the zero boundary to every higher boundary; its fibre
operation packs to the same general composition (`pack_composeAtFibre`).
Interchange now also holds between arbitrary positive boundaries:
`cutCompose_interchange` covers every strictly ordered pair of dimension-indexed
cuts, and `Cut.below_iff_height` identifies this order with numerical boundary
order. Cuts only index the same existing `Pasting` carrier. `cutSource_at`,
`cutTarget_at` and `cutCompose_at_eq` identify their operations with the existing
arbitrary-boundary API, deriving the translated composability proof.
`cutGrid_composable` now derives both outer composability witnesses from the
four inner ones, and `cutCompose_interchange_grid` proves interchange using
only those four hypotheses. This covers arbitrary ordered boundary dimensions;
the outer composites are not assumed to exist independently. The chain proof
retains the actual labels through `zipOver_grid`. The monad is now constructed;
its standard free-category comparison remains incomplete. Cartesian
verification and the native endomorphism action are now supplied separately. Native/coskeletal
coinductive invertibility is proved separately below, not yet linked to an
operadic action.

## Semantic audit and completion gates

`NativeGlobularTower.lean` now constructs a candidate recursive carrier whose
first three levels are exactly the original objects, raw `Path` traces and
Type-valued `RwEq` syntax, with universe lifts only where necessary.
`NativeTower.realizes` instantiates all equivalences and boundary equations in
`RealizesPathSkeleton`. The existing primitive associator is retained literally;
`distinct_rewrite_cells` proves that reflexivity and its syntactic composite
remain different two-cells.

Above dimension two this candidate explicitly adjoins a cell for each parallel
pair, recursively: it is a coskeletal extension of the raw two-skeleton. These
cells are not asserted to be native higher rewrite derivations. The limitation
is proved by `higher_ext`: cells of dimension at least three are determined by
their boundaries. Identities and globularity are checked at every dimension.
This carrier construction alone does not establish an operadic action,
and does not replace the independent, presentation-sensitive associativity
certificate. The endomorphism action and algebra laws are now verified below;
the required operation and certificate comparisons are still outstanding.

The candidate now has adjacent composition and reversal at every positive
dimension, with verified source/target laws. `compose_paths` and
`compose_rewrites` retain `Path.trans` and `RwEq.trans` exactly; reversal uses
the native `Path.symm` and `RwEq.symm` constructors. `cancelRight` and
`cancelLeft` supply cancellation cells in every positive dimension. Their
one-cell witnesses are exactly `Step.trans_symm` and `Step.symm_trans`, as
checked by the corresponding `_paths` theorems. Higher cancellation uses the
explicit coskeletal extension.

`WeaklyInvertible` now defines the greatest postfixed point of the cancellation
operator on predicates over all positive dimensions. `weaklyInvertible_unfold`
proves its fixed-point equation, and `weaklyInvertible_coinduction` supplies the
coinduction principle. `all_cells_weaklyInvertible` proves every positive cell
invertible by a single postfixed predicate containing the cancellation cells
at all higher dimensions, without a finite depth bound. This follows
[Fujii--Hoshino--Maehara, Definition 3.1.1 and Remark 3.1.2](https://higher-structures.math.cas.cz/api/files/issues/Vol8Iss2/FujHosMae),
whose operator is defined already for omega-precategories. The theorem is
about the specified native/coskeletal omega-precategory; its operations are
not asserted to be identical to the contraction-selected operadic operations.
The latter now have their own invertibility proof and comparison cells below.

`composeAssociator`, `leftUnitor`, and `rightUnitor` supply correctly bounded
coherence cells for adjacent composition in every positive dimension.
`composeAssociator_paths` identifies its first-dimensional instance with the
existing `associatorCell` literally; the unitor `_paths` equations expose the
exact `Step.trans_refl_left` and `Step.trans_refl_right` derivations. Higher
instances use the declared coskeletal extension. The audit checks that all
these coherence cells are themselves coinductively weakly invertible, at an
arbitrary dimension. These are actual operations of the candidate tower,
but their operadic origin and the required pentagon/interchange comparison
with the independent associativity certificate remain to be established.

The current rewrite theory has a totality theorem for `RwEq` on parallel
paths. A structural weak omega-groupoid theorem does not automatically give a
model of arbitrary homotopy types or nontrivial fundamental groups. Establish
the resulting truncations and state this limitation alongside the theorem.

`NativeTower.fillPositiveBoundary` now provides fillers for every parallel
boundary of positive-dimensional native cells. Its dimension-two case is
literally the existing `QuotientPathInduction.rweqAny` derivation
(`fillPositive_paths`); higher cases use the explicitly adjoined coskeletal
cells. This asserts inhabitation, not equality of raw rewrite derivations,
and does not fill arbitrary pairs of objects. It is used in the native
operation construction below, not an operadic contraction by itself.
The primitive trace-collapse definitions were moved without renaming into
the dependency-light `Rewrite.TraceCollapse` module and re-exported by the
original quotient-path-induction module. The latter still has pre-existing
build failures in its `MetadataRepair` dependency under the active toolchain;
the trace-collapse module and native tower are checked independently.

`NativeTower.TwoSkeletonInterpretation.existsUnique_extension` now extends
any boundary-compatible interpretation of objects, paths, and raw rewrite
cells uniquely to a globular map into the native tower. The supplied
two-cell derivations are preserved literally. `map_ext_twoSkeleton` reduces
equality of maps into this tower to equality in dimensions zero through two;
the audit checks that extending the identity two-skeleton recovers the
identity map. This can support future action-law checks but supplies neither
an operation collection nor substitution compatibility by itself.

`GlobularEndomorphism.lean` constructs a concrete normalized endomorphism
collection. Its operations recursively carry a pasting arity, parallel
boundary operations, and an evaluation function on inputs of that arity
which preserves both boundaries. Dimension zero is the identity operation.
`Endomorphism.evaluation` is a globular map on the actual collection
application. For the native tower, `nativeContraction` supplies all the
specified lifts over arities, including dimension-one empty diagrams.
Those one-dimensional lifts fold actual `Path.trans` traces; the higher
lifts evaluate the given boundary operations and use `fillPositive`.
`existsUnique_abstraction` proves that every normalized globular evaluation
is represented by a unique map into this collection. `evaluation_injective`
detects collection-map equality by actual evaluation on all labelled inputs.
This universal property now constructs concrete unit and multiplication
maps: units extract singleton inputs, and multiplication recovers nested
inputs through the substitution comparison and performs nested evaluation.
`evaluation_unit_input` and `evaluation_multiplication_nested` prove those
action equations in all dimensions; the audit also checks that the unit
preserves a raw `Path` cell literally.
`one_mul`, `mul_one`, and `mul_assoc_inv` now prove all three operadic laws
as equalities of collection maps. The associativity proof retains the full
nested input diagrams through `associateInv_comparison`; it does not use
native higher fillers to replace an operadic equality.
`Endomorphism.operad` packages the actual Mathlib `MonObj`, and
`Endomorphism.algebra` packages the actual algebra for its induced monad.
Together with `nativeContraction`, these give a normalized contractible
endomorphism operad over the implemented pasting monad acting on the native
tower. The audit instantiates both structures on that tower.
`NativeOperadicOperations.lean` now constructs the recursive standard
pasting-instruction convention of Fujii--Hoshino--Maehara, Definition 2.5.1.
`shape_boundary` proves that a shape has equal source and target.
`instruction_singleton` selects the operadic unit on singleton arities;
`instruction_contraction` lifts every other arity using the recursively
selected boundary instruction. `instructions` is a globular section of the
arity map, and `instructions_unit` proves compatibility with singleton units
as an equality of globular maps.
`standardEvaluation` pairs complete labelled diagrams with these instructions
and applies the actual algebra. It preserves singleton cells literally in
every dimension, including raw `RwEq` witnesses checked by the audit.
The adjacent binary inputs are vertical composites of singleton diagrams;
identity inputs are identity diagrams over singletons. Both operations now
use this full standard evaluation, and their boundary and invertibility
proofs have been rechecked with these definitions. The earlier specialized
unit-boundary `input` helper remains available but is not substituted for the
standard instruction recursion.
`NativeOperadic.WeaklyInvertible` uses these operations in the greatest
postfixed-point definition; `weaklyInvertible_unfold` and
`all_cells_weaklyInvertible` verify its fixed-point equation and all-cell
invertibility. This follows the adjacent-operation/coinduction formulation
in [Fujii--Hoshino--Maehara, Definitions 2.5.2 and 3.1.1 and Remark 3.1.2](https://higher-structures.math.cas.cz/api/files/issues/Vol8Iss2/FujHosMae).
It no longer relies solely on invertibility for the independent native
omega-precategory. `compareCompose` and `compareIdentity` provide explicit
comparison cells, not equality of raw `RwEq` witnesses. Their invertibility,
and that of the retained primitive native associator, is checked by the audit.

This is not yet the full weak omega-groupoid theorem: the standard free
strict-category monad comparison and the independent associativity/pentagon
and interchange certificate comparisons still require verification. The
standard instruction recursion is now verified over the implemented monad;
that does not by itself discharge the monad comparison.

`NativeAssociativityBridge.lean` now reuses the unchanged independent
`AssocHigherBridge.evalHigher` interpretation. `certificate` retains the exact
raw `evalTrace` two-cell boundaries; pentagon and interchange map through
their existing named native certificates. `pentagon_traces_distinct` checks
that the two- and three-step histories remain distinct in the tower itself.
`three` translates structural composition and inversion recursively, while
primitive meta-steps enter the declared coskeletal layer.
`three_parallel_images` explicitly records the loss of three-cell information
in that target; it does not identify the original source certificates.

`NativeOperadic.compose_paths` now proves that standard one-dimensional
composition is exactly `Path.trans`. Consequently `operadicAssociator`
retains the literal `Step.trans_assoc` witness with standard operadic
boundaries, including heterogeneously composable paths. Invertible
`twoCompositionComparison` and `compositionComparison` cells relate native
certificate composition to standard operadic composition at the next two
levels. The original independent audit is rerun separately. This establishes
the explicit certificate-image and composition comparisons, but does not yet
provide a complete comparison of horizontal whiskering and every selected
operadic pentagon/interchange coherence operation.

Completion requires the mathematical target above to be instantiated, all
proof dependencies audited, the relevant modules built, and preservation of
the existing associativity artifact checked. Merely defining interfaces,
declaring filler constructors, or obtaining a green build of the foundations
does not establish completion. External submission is a separate action.

The strict cut-law comparison now includes a bundled category `CutModel`
and a fully faithful functor into the actual pasting-monad algebras.
`algebraHom_preserves` recovers preservation of every cut composition and
identity from the algebra-homomorphism equation, by evaluating diagrams
of singleton generators. `algebraHomEquiv` gives the explicit two-sided
morphism correspondence. This closes the morphism-level comparison for
the implemented cut laws; it does not yet identify all algebra objects or
identify that cut-law presentation with the standard strict omega-category
definition. No extra higher filler assumption is used in this comparison.
