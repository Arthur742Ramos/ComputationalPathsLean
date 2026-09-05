# Pre-submission review

This is an agent review of the scoped relative completion, not independent
specialist review, Palomar editorial clearance, or a prediction of registration.
The author approved excluding the manuscript's Theorem 10.2 and proceeding
with a corrected completion theorem.

## Mathematical checks

| Concern from the preceding artifact | Resolution in this statement |
| --- | --- |
| A bundle admitted an unrelated empty cell family | No arbitrary family field: Cell is explicitly built from the fixed skeleton and recursive extensions |
| Every high dimension reused four-cell endpoints | Each extension uses the preceding layer's arrows as its objects; dimension-six regression targets dimension five |
| A filler constructor was advertised as intrinsic coherence | The constructor is disclosed as a completion choice; the principal interpretation theorem characterizes its syntax |
| Intermediate higher derivations could leave a parallel fiber | CellDerivation.parallel is proved by induction for every constructor |
| Claimed identity-type comparison | Explicitly excluded; an axiom-free regression exhibits a rewrite between unequal trace records |
| Possible collapse of proof-relevant data | The pentagon routes remain unequal; higher loop syntax is not a subsingleton; maps preserve node counts |
| Interpretation theorem could be vacuous | Regression instantiates its hypotheses with integer-valued hom types, nonzero generators, negation and addition |
| Full weak omega-groupoid label exceeded the statement | Removed; no operadic action, global infinite-tower initiality, or full horizontal structure is claimed |

The unique interpretation property has explicit hypotheses: the target supplies
all four typed operations, including generators for parallel pairs. It does
not manufacture those operations in a target lacking them. The proof is a
structural recursion/induction argument. The extension identity/composition
laws and exact parallel-boundary characterization are separately selected.

The tower preserves the specified extracted 2-skeleton, not the entirety of
the much larger native rewrite system. Its Path records have unconstrained
metadata. Neither a deep embedding nor normalization completeness is inferred.

## Completed local verification

`bash scripts/check.sh` passes on Lean 4.33.0 with the manifest's Mathlib
revision. It builds both standalone modules and runs all regressions.
The local run reused an existing matching dependency cache.

There are 16 selected theorems. Eleven use no axioms, four use only Quot.sound
(the extensionality proofs), and the pentagon distinction uses only propext.
The exact per-declaration inventory is checked against the metadata. No
Classical.choice, custom axiom, proof hole, or evaluator bypass is used.

The statement is about 500 lines and 21 KiB, below Palomar's hard bounds but
above the preferred line-count envelope. All definitions are visible; no
undefined value selects a convenient cell family. Both modules contain the
same complete development. Their duplication is disclosed and checked, not
presented as independent verification.

The local source-dependency check inspects direct imports. Canonical transitive
dependency verification belongs to the submission verifier; do not mislabel
the direct-import list as a complete dependency-graph audit. The separately
pinned GitHub workflow performs Comparator and independent NanoDa replay.
Its result must be checked at the exact commit before claiming it passed.

## Research-interest assessment

The plausible audience is researchers mechanizing higher rewrite systems and
proof-relevant equality syntax. The contribution is a precisely scoped,
reusable completion with an interpretation property, a corrected recursive
implementation, and a concrete separation of higher connectedness from raw
identity. The artifact does not claim that the generic free-syntax technique
is new, that proof length establishes significance, or that the accepted
paper's status transfers to this adaptation.

The scope and alignment objections identified in the earlier audit are
addressed for this narrower statement. Editorial research-interest judgment
remains uncertain and should not be represented as guaranteed. No Palomar
intake or registration is recorded by this document.
