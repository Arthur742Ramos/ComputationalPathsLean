# Full weak omega-groupoid construction: live obligations

Status: in progress. The completed associativity certificate remains in
`ASSOCIATIVITY_HIGHER_COHERENCE.md`; it is not the theorem specified here.

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
has coinductive invertibility for its specified adjacent operations; an
operadic action and its compatibility with those operations remain unproved.

```sh
lake build ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
lake build ComputationalPaths.Path.OmegaGroupoid.NativeGlobularTower
lake env lean scripts/FullOmegaAudit.lean
```

The lifting interface follows the elementwise positive-dimensional square
in Raftogianis, Definition 4.5 (pp. 35–36). It requires a specified arity cell
and both commuting-boundary equations; it is not a general filler for domain
parallel pairs. The strict-pasting monad, globular operad and algebra action
are still unconstructed. The audit above checks only the current foundations.

The subsequent `GlobularPasting.lean` constructs a genuinely recursive labelled
pasting carrier: objects at dimension zero, then composable chains of smaller
diagrams in hom globular sets. Its adjacent boundaries, both globularity laws,
and identities in every dimension are checked. The hom construction preserves
the original cells with fixed zero-dimensional endpoints and lowers dimension
at every recursion. This is a candidate carrier for the strict-pasting monad,
not yet a monad. Relabelling now forms the checked Mathlib endofunctor
`Pasting.pastingFunctor`, preserving both boundaries and respecting identity
and composite maps. The singleton inclusion `Pasting.singletonGlobular` is now
a boundary-preserving globular map, natural in the original globular set
(`singleton_natural`) and injective at every dimension (`singleton_injective`).
The partial extractor `atom?` recovers original cells from these singleton
diagrams; it rejects empty and composite chains. This provides the candidate
unit without erasing original cells. Flattening is now constructed as
described below; the full monad laws and free strict-category universal
property remain to be established.

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
the full multiplication laws remain unfinished.

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
implemented evaluator's pre- and postcomposition laws. The other unit
equation, associativity, and the free universal property remain unfinished.
Consequently this is not yet a proved monad or globular operad.

Endpoint-indexed chain substitution now has proved left/right unit and
associativity laws (`Chain.bind_single`, `Chain.bind_id`, `Chain.bind_assoc`).
Its interpretation by actual computational paths respects substitution
(`evalPathChain_bind`). These are ingredients for flattening nested diagrams,
not a substitute for the full globular monad laws.

Horizontal composition along the zero-dimensional boundary is now defined
for diagrams in every positive dimension (`Pasting.horizontal`). Its exposed
endpoint fibres are exactly the chains in the existing pasting carrier;
`sourceZero_pack` and `targetZero_pack` verify their iterated globular endpoints.
Associativity, left/right units, adjacent-boundary compatibility, identity
compatibility and compatibility with relabelling are proved. This does not
yet supply composition along every intermediate-dimensional boundary or the
interchange laws required for the strict-pasting monad.

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
operations are described below; full interchange and monad laws remain outstanding.
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
and interchange between every pair of distinct composition dimensions still
require proofs before claiming a free strict omega-category or its monad.

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
retains the actual labels through `zipOver_grid`. Constructing the monad and
its universal property, and supplying the eventual weak-groupoid action and
invertibility, remain incomplete.

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
certificate. The action must still be constructed and its algebra laws verified
before this candidate can support the requested theorem.

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
not yet identified with those of a proved operadic action. That remains a
required completion gate, not a consequence of invertibility alone.

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

Completion requires the mathematical target above to be instantiated, all
proof dependencies audited, the relevant modules built, and preservation of
the existing associativity artifact checked. Merely defining interfaces,
declaring filler constructors, or obtaining a green build of the foundations
does not establish completion. External submission is a separate action.
