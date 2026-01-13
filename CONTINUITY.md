# CONTINUITY.md

## Goal
Audit axioms/assumptions in the repo and discharge (prove/replace or quarantine) any that are derivable; keep builds warning-free and avoid `sorry`.

## Constraints/Assumptions
- Run `lake build` after non-trivial edits; keep build warning-free.
- No `sorry`.

## Key Decisions
- Basepoint-independence: prove conjugation respects π₁ operations (`conjugateByPath_comp`, `conjugateByPath_inv`).
- Non-HIT axioms quarantined behind opt-in imports (not kernel axioms by default).
- HIT axioms remain as kernel axioms (necessary for the theory).
- Higher homotopy groups (n ≥ 3): PiN returns PUnit, so non-trivial results use typeclasses.
- **Nielsen-Schreier derivation**: Created typeclass-based alternative to axioms.

## State
- **Done**:
  - Quarantined `sphere_HSpace_only` → `HIT/HopfInvariantOneAxiom.lean`
  - Quarantined `covering_equiv_subgroup` → `Homotopy/CoveringClassificationAxiom.lean`
  - Quarantined `local_confluence_prop` and `step_strip_prop` → `Rewrite/ConfluenceConstructiveAxiom.lean`
  - Kernel axiom count reduced: **40 → 36** (all HIT-related now)
  - **Octonionic Hopf fibration**: Complete formalization in `OctonionicHopf.lean`
  - **Stable homotopy stems complete**: πₛ₁ through πₛ₇ in `JamesConstruction.lean`
  - **Nielsen-Schreier Derivation** (NEW):
    - Created `Algebra/GraphHIT.lean`: Graph realization as quotient type with edge paths typeclass
    - Created `Algebra/NielsenSchreierDerived.lean`: Derives Nielsen-Schreier from covering space theory
    - `deriveNielsenSchreierData`: Replaces `nielsenSchreierData` axiom with typeclass-based derivation
    - `deriveSchreierRankFormula`: Proves Schreier rank formula from covering degree
    - Key typeclasses: `HasEdgePaths`, `HasGraphPi1Equiv`, `HasSubgroupCovering`
    - Original axioms remain for backward compatibility; new modules provide derivation pathway
  - Build succeeds with no errors
  - Documentation updated (`docs/axioms.md`)
- **Now**: All tasks complete
- **Next**: Consider migrating users of original axioms to derived versions
- **GitHub Copilot Instructions**: Added `.github/copilot/instructions.md` and skills
  - Skills: lean-build, aristotle, ci-and-releases, lean-hit-development, path-tactics, quotients-and-lifts, rweq-proofs

## Open Questions
- None - major results complete
- Future: Could some HIT axioms (e.g., Cylinder) be derived from others?
- Future: Extend PiN infrastructure to compute non-trivial higher groups?
- Future: Deprecate original Nielsen-Schreier axioms in favor of derived versions?

## Working Set
- Files:
  - `ComputationalPaths/Path/Algebra/GraphHIT.lean` (new)
  - `ComputationalPaths/Path/Algebra/NielsenSchreierDerived.lean` (new)
  - `ComputationalPaths/Path.lean` (updated with Algebra imports)
- Commands:
  - `lake build`
