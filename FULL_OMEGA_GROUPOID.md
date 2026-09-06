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

These definitions and lemmas build without proof holes. They do **not** yet
instantiate the full carrier or prove an operadic action or invertibility.

```sh
lake build ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
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
unit without erasing original cells. Flattening, monad laws and the free
strict-category universal property remain to be established.

Endpoint-indexed chain substitution now has proved left/right unit and
associativity laws (`Chain.bind_single`, `Chain.bind_id`, `Chain.bind_assoc`).
Its interpretation by actual computational paths respects substitution
(`evalPathChain_bind`). These are ingredients for flattening nested diagrams,
not a substitute for the missing globular monad multiplication.

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
Interchange between two positive boundary dimensions, monad construction,
and the eventual weak-groupoid action and invertibility remain incomplete.

## Semantic audit and completion gates

The current rewrite theory has a totality theorem for `RwEq` on parallel
paths. A structural weak omega-groupoid theorem does not automatically give a
model of arbitrary homotopy types or nontrivial fundamental groups. Establish
the resulting truncations and state this limitation alongside the theorem.

Completion requires the mathematical target above to be instantiated, all
proof dependencies audited, the relevant modules built, and preservation of
the existing associativity artifact checked. Merely defining interfaces,
declaring filler constructors, or obtaining a green build of the foundations
does not establish completion. External submission is a separate action.
