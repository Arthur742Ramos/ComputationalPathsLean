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
and composite maps. The monad unit, flattening, monad laws and the free
strict-category universal property remain to be established.

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
