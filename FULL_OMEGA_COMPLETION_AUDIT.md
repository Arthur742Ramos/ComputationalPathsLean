# Native weak omega-groupoid: completion audit

## Exact result

`NativeWeakOmega.category A` is an algebra for a normalized contractible
globular operad. `NativeWeakOmega.fullWeakOmegaGroupoid A` proves that its
actual carrier realizes the raw computational-path two-skeleton and that
every positive cell is weakly invertible for every operadic composition
system. Both the carrier and the action are identified with the constructed
native tower and its endomorphism evaluation, by definitional equality.

The entry point is
`ComputationalPaths/Path/OmegaGroupoid/NativeWeakOmegaGroupoid.lean`.
Import this module explicitly; the repository-wide umbrella import is not
the build or audit boundary for this result.

## Definition correspondence

The convention is van den Berg--Garner,
[Types are weak omega-groupoids, Definitions 2.1.1--2.1.4](https://arxiv.org/pdf/0812.0298):
an algebra for a normalized contractible globular operad, with invertibility
for every system of compositions. This is not an invocation of their theorem
about intensional identity types, and no initial-operad universal property is
asserted for the chosen endomorphism operad.

| Obligation | Checked implementation |
| --- | --- |
| Recursive globular carrier, all dimensions | `NativeTower.Cell`, `NativeTower.globular` in `NativeGlobularTower.lean` |
| Raw objects, `Path`, and `RwEq`, with boundary preservation | `NativeWeakOmega.realizes : RealizesPathSkeleton ...` |
| Free strict-category monad rather than an arbitrary pasting functor | `Pasting.StrictModel.freeForget_monad` in `GlobularPasting.lean`; the preceding strict presentation, free construction, and adjunction supply its definition bridge |
| Lawful operadic substitution and units | `Endomorphism.operad`; `GlobularCollection.operadMonad` |
| Actual cartesian arity monad map | `NormalizedContractibleOperad.arityMonadHom`, `arity_globular_pullback`, `arity_cartesian` |
| Normalization at objects | `objectsEquiv`, natural in the input globular set |
| Contraction of the terminal component of the arity map | `terminalContraction`, transferred through `applicationTerminalIso` from the stored operation contraction |
| Algebra on this carrier, not an unrelated completion | `NativeWeakOmega.category_carrier`, `category_action`; actual Mathlib monad algebra laws |
| Invertibility at every positive dimension | `NativeUniversal.BoundaryOperations.WeaklyInvertible`, a greatest-postfixed-point definition with a proved unfolding equivalence |
| Every operadic composition system, nonvacuously | `NativeWeakOmega.all_systems_invertible`; existence and universal quantification are both included |
| Exact path identity and composition | `NativeWeakOmega.identity_objects`, `NativeOperadic.compose_paths` |
| Primitive unitors and cancellation | `NativeTower.leftUnitor_paths`, `rightUnitor_paths`, `cancelRight_paths`, `cancelLeft_paths`; the four `NativeWeakOmega.*_operadic_boundary` theorems connect them to selected operadic operations |
| Associator, pentagon, and interchange | `NativeOperadic` operation-level contractions and concrete applications; `NativeAssociativity` comparisons with the preserved independent certificate |

The unit and cancellation boundary correspondences do not claim that every
contraction choice is literally the same raw rewrite derivation. Comparison
cells and definitional equalities are distinguished throughout. In particular,
the independent associativity certificate is not replaced with the new
carrier's generic higher fillers: its original derivations are retained and
explicitly compared by the bridge module.

## Semantic scope and collapse

The cells in dimensions zero, one, and two are the original objects, raw
paths, and raw rewrite derivations (up to the explicit universe lifts).
Above them is the declared recursive coskeletal extension. This is not a
formalization of independently specified higher rewrite syntax.

The following are proved in `NativeWeakOmega.Semantics`:

- `pathComponentsEquiv`: quotienting paths by inhabited actual `RwEq` gives
  exactly `PLift (a = b)`.
- `loopClassesUnique`: based loop classes have exactly one element in every
  dimension, using existence of actual next-dimensional cells as the relation.
- `higher_cells_determined_by_boundary`: cells in dimensions three and above
  are determined by their immediate source and target.
- `raw_rewrites_still_distinct`: reflexivity and a two-step composition of
  reflexivities remain distinct raw two-cells.

These quotients are separate diagnostics, not replacements for the carrier.
The structural theorem does not establish nontrivial homotopy groups, HoTT
semantics, or faithfulness of an unrestricted higher rewriting theory.

## Reproduction and delivery boundary

Use the checked-in toolchain (`leanprover/lean4:v4.33.0` at this audit), rather
than the older version stated in the introductory project instructions.

```sh
lake build ComputationalPaths.Path.OmegaGroupoid.NativeWeakOmegaGroupoid
lake env lean scripts/FullOmegaAudit.lean
lake env lean scripts/AssocHigherAudit.lean
git diff --check
```

The dedicated CI job builds this same entry point and runs the full audit.
The local entry-point build passed (719 jobs), both audit commands exited
successfully, and `git diff --check` passed. The final package's printed
dependencies are only `propext`, `Classical.choice`, and `Quot.sound`;
the semantic diagnostic theorems require only the applicable subset.
The audited construction sources contain no `sorry`, custom axiom declaration,
`unsafe` definition, `implemented_by`, or `native_decide` proof shortcut.
Local verification and hosted CI are separate claims: this completion audit
does not report a new hosted run, a pull request, a remote merge, publication,
or an independently checked external certificate for the full construction.
It also does not certify unrelated repository-wide modules.

`FULL_OMEGA_GROUPOID.md` retains the incremental development record. Its older
milestone descriptions are historical; this document is the final scope and
definition-obligation map.
