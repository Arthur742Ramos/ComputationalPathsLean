# Pre-submission mathematical audit

Date: 2026-09-04. Audited artifact:
`Arthur742Ramos/ComputationalPathsLean`, commit
`c5b35d854c4271f5216d33539526a28648d7dde9`, Comparator path
`palomar/weak-omega-groupoid/comparator.json`.

## Decision: do not submit this snapshot as the paper's omega-groupoid result

The selected Lean statements are kernel-checkable. They do not yet establish
the advertised mathematical structure. Earlier readiness language was too
confident. These findings concern the encoding, not inconsistency of Lean or
a demonstrated refutation of the accepted paper. No intake was attempted during
this audit, and no existing submission was modified.

## Verified mechanical evidence

The exact SHA has a successful [hosted workflow](https://github.com/Arthur742Ramos/ComputationalPathsLean/actions/runs/33834916781).
Its logs explicitly report acceptance by Comparator, Lean, and NanoDa.
The artifact gate reports 346 Challenge lines and 15,622 bytes.
This is hosted repository verification, not Palomar intake or editorial review.

The unchanged Solution was also rebuilt locally with Lean 4.33.0 using an
existing dependency environment whose Mathlib SHA is exactly the package's
`db584cd6d46c92f209a44c0f1c829460d327499d`. This was not a fresh dependency
download or another local NanoDa run. The additional `scripts/SemanticAudit.lean`
imports that compiled Solution; it is not part of the recorded Comparator surface.

## Blocking semantic findings

1. **The record does not constrain its cell family.** Solution lines 326-345:
   no coherence field refers to `cells`. A field default is not a law.
   `emptyCellsAllowed` constructs a boundary on Unit whose cells are Empty at
   every dimension. The headline existence theorem therefore cannot certify
   the intended underlying globular object. Fixing only the default does not
   supply missing source, target, composition, or compatibility laws.

2. **The tail is not recursive in dimension.** Solution lines 309-319:
   every dimension at least five uses endpoints in Derivation4. In particular,
   six-cells are not presented as cells between parallel five-cells. The audit
   includes a definitional-equality check exposing exactly those endpoints.
   An indexed family alone is not an iterated globular structure.

3. **The filler is installed by the generator.** MetaStep3 accepts equality
   of two proofs of the same Nonempty proposition. This premise is automatic
   for every pair of parallel derivations. `automaticPrimitive` constructs the
   generator without examining their rewrite content. This is a legitimate
   syntactic completion rule, but its use must not be sold as proving intrinsic
   coherence of an independently specified rewrite calculus. The same mechanism
   gives `DerivationHigh n true false`; it does not reflect equality of the
   underlying witnesses. `truncationEqualityDoesNotReflect` proves the latter
   distinction without additional axioms. Native ContractibilityIrrelevance
   explicitly documents that the generator's premise always holds, so this is
   not solely an extraction error.

4. **Trace validity is not encoded.** `disconnectedTrace : Path Nat 0 0`
   has trace `[(1,2)]`. The list is unconstrained decoration of endpoint Eq,
   not a certified sequence of equality rewrites. This can be an intentional
   model, but needs accurate terminology and a proved correspondence before
   claiming a deep embedding of the paper's computational paths. The local
   seven-constructor Step fragment is not the full native rewrite system.

5. **No standard-structure bridge or substantive replacement theorem is supplied.**
   Distinct pentagon route lengths preserve syntax but do not close the above
   gaps. Four coherence witnesses plus chosen universal fillers are not by
   themselves a full weak omega-groupoid definition. A smaller structural slice
   may be useful, but its research value needs an independent mathematical
   result, not merely a name associated with the paper.

## Research comparison and editorial implications

[Lumsdaine](https://arxiv.org/abs/0812.0409) constructs a contractible globular
operad of definable composition laws and an action on the identity-type tower.
[Van den Berg and Garner](https://arxiv.org/abs/0812.0298) establish a weak
omega-category structure on an iterated identity-type tower and its groupoid
property. Contractibility of an operad of operations must not be confused with
contractibility of every higher hom-type of an arbitrary type. No equivalence
with those constructions has been checked here.

[Palomar's policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
separates kernel correctness from research interest and statement alignment.
The current encoding risks its prohibitions on manufactured conclusions and
substituting convenient surrogate notions. This is an audit judgment, not a
prediction or a claim that Palomar has rejected this artifact.

## Provenance and review corrections required

- The original attachment path is absent, but a matching local manuscript was
  subsequently recovered: 49 pages, 703,617 bytes, created 2026-06-27.
  SHA-256: `f53d7b1241de79a216d4cd2c37a17f173142d21cf96204115c2535b1dd0a6109`.
  Its title, size, creation timestamp, and page count match the previously
  inspected attachment. The public arXiv version is not silently substituted.
- Metadata says an accepted manuscript is attached to the submission; an
  attachment in a conversation is not automatically a repository attachment.
  Record a stable source/version and precise theorem mapping.
- The `manual` automation entry describes work performed by an agent in the
  recorded workflow. Correct the method disclosure; do not imply independent
  human review. Preserve the user-requested four-author attribution.
- NATIVE_CORRESPONDENCE is a prose correspondence account, not a checked
  interpretation preserving the selected structures.
- The current shell gate checks syntax, declarations, and kernels. Requiring
  named coherences to call the universal filler does not test mathematical
  independence from that filler or standard-definition adequacy.

## Repair acceptance criteria

1. Fix the intended mathematical semantics against the accepted source: either
   an explicit chosen completion, or coherence of a fixed rewrite calculus.
   These are different claims and cannot silently replace one another.
2. Construct a genuinely recursive parallel-cell tower, with source/target,
   globularity, identity, composition and inversion at the advertised levels.
   Tie every bundled law to the actual recorded family.
3. Prove the advertised standard weak-groupoid structure or a precise bridge
   to a published definition. If pursuing a completion theorem, establish
   meaningful preservation/universal properties rather than just filler existence.
4. Supply a checked interpretation connecting the paper/native syntax and the
   submitted fragment; state hypotheses and exclusions at the theorem boundary.
5. Correct provenance/automation, independently audit the repaired statements,
   rerun pinned mechanical verification at the new immutable SHA, and only then
   use a Palomar intake attempt. No amount of prose polish substitutes for 1-4.

## Implemented repair after manuscript recovery

`GlobularCompletion.lean` now gives a genuinely recursive completion of the
submitted 2-skeleton. Every generator carries a parallel-boundary condition;
induction proves it for every derivation, including intermediate compositions.
Successive cells have endpoints in the immediately preceding dimension.
Source/target globularity, all-dimensional identity and inverse boundary laws,
higher vertical composition with boundary laws, higher associativity/unit/inverse
comparisons, chosen higher filling, and an explicit pentagon embedding compile.
These constructions retain the declared universal-filler choice; they do not
claim that proof irrelevance alone reflects equality of Type-valued witnesses.

The repair is a separate module, not a silent replacement of the old Comparator
statement. It is not yet a complete operadic weak omega-groupoid construction.
Whiskering across all dimensions, the full published-definition bridge, and
a satisfactory research-interest justification remain outstanding. The native
2-skeleton and existing checked declarations have not been changed.

`bash scripts/check-repair.sh` passed locally with Lean 4.33.0 and the package's
pinned Mathlib. All reported repair and obstruction declarations use no axioms;
the repair/test sources contain no holes or custom axiom declarations. The
local build reuses an existing matching dependency cache, not a clean download.
No new hosted Comparator/NanoDa result is claimed for the repair.

## Additional source-alignment obstruction: accepted Theorem 10.2

The accepted manuscript, pages 38-39, claims a dimension-two correspondence
between rewrite equivalence and identity of paths. For the retained Lean Path
records this implication is false, even on Unit. Let p be the one-entry reflexive
path. The primitive inverse rule rewrites `p.trans p.symm` to empty reflexivity,
but the two traces have lengths two and zero. Therefore there is a rewrite
witness while the identity type of those Path records is empty.

`SemanticAudit.rewriteDoesNotReflectIdentity` and
`SemanticAudit.noUnrestrictedRewriteToIdentity` verify this counterexample in Lean
without axioms. This refutes that unrestricted comparison for these retained
definitions, not every possible alternative model of the paper. It rules out
advertising Theorem 10.2 as covered by this artifact without changing semantics
and proving an appropriate bridge. Pages 20-21 explicitly include the universal
filler generator and recursive higher boundaries, supporting the scope of the
current repair. Theorem 10.1's claimed correspondence to the traditional
definition still needs an actual formal argument.
