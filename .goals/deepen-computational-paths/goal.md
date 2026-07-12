# Goal: Deepen Computational-Path Proofs

## User Request

Improve substantially every project and proof that can be improved, using
computational paths as the building block.

## Refined Goal

Perform a substantial hardening pass over the complete non-core tranche
identified by the repository audit: every Lean file that contains shallow
proof signatures (`Path.ofEq`, `Path.mk`, `True`, `trivial`, or `by rfl`) but
contains neither literal `RwEq` nor literal `Path.trans` after Lean comments
are removed. Deepen all 43 target modules with mathematically meaningful,
domain-specific computational-path evidence while preserving their public
APIs and intended statements. Replace scaffold proofs rather than adding
decorative witnesses, and keep the entire repository axiom-free,
`sorry`-free, and buildable.

## Acceptance Criteria

- [ ] Criterion 1: Every one of the 43 target files listed below contains
  genuine, domain-relevant computational-path integration: at least one
  `RwEq` coherence and at least one multi-step `Path.trans` construction that
  participate in a public theorem, definition, or certificate rather than an
  unused/decorative declaration.
- [ ] Criterion 2: In the 43 target files, no public theorem or certificate
  field remains a scaffold whose mathematical conclusion is only `True`,
  `P ↔ True`, `P → True`, or is discharged solely by `trivial`; replace each
  such scaffold with typed domain data and meaningful `Path`/`RwEq` evidence.
- [ ] Criterion 3: In the 43 target files, no public proof remains merely a
  bare one-step `Path.mk [Step.mk _ _ h] h` wrapper or a bare `Path.ofEq`
  wrapper when a computational-path construction can express the result.
  Necessary endpoint bridges may remain only when incorporated into a deeper
  multi-step path or an `RwEq` coherence.
- [ ] Criterion 4: Existing public names and theorem intent are preserved.
  No theorem is weakened, no target module is deleted, and no new custom
  axiom, `sorry`, `admit`, `native_decide`, or unsound escape hatch is added.
- [ ] Criterion 5: `python3 scripts/check_invariants.py` reports
  `invariants OK`, every edited target module builds, and the full
  `lake build` succeeds.
- [ ] Criterion 6: The final diff is limited to the target modules, their
  directly required import/root wiring, and `.goals/deepen-computational-paths/`
  process artifacts. Any dependency edit must be necessary for a target
  module and documented in the Builder summary.

## Scope Boundaries

**In scope:**

- `ComputationalPaths/Path/Algebra/ConfluenceStructuresDeep.lean`
- `ComputationalPaths/Path/Algebra/DiophantinePaths.lean`
- `ComputationalPaths/Path/Algebra/RewritingSystemsDeep.lean`
- `ComputationalPaths/Path/Rewrite/Benchmark.lean`
- `ComputationalPaths/Path/Algebra/GrothendieckDuality.lean`
- `ComputationalPaths/Path/Algebra/LieAlgebras.lean`
- `ComputationalPaths/Path/GrayCategory.lean`
- `ComputationalPaths/Path/Algebra/MotivicPaths.lean`
- `ComputationalPaths/Path/CompPath/EilenbergMacLaneSpaces.lean`
- `ComputationalPaths/Path/Tricategory.lean`
- `ComputationalPaths/Path/Algebra/ConcurrencyTheoryDeep.lean`
- `ComputationalPaths/Path/Topology/DiscreteTopology.lean`
- `ComputationalPaths/Path/Algebra/SymmetricMonoidalDeep.lean`
- `ComputationalPaths/Path/Computation/ConstraintPaths.lean`
- `ComputationalPaths/Path/Logic/RealizabilityPaths.lean`
- `ComputationalPaths/Path/Algebra/GarsidesDeep.lean`
- `ComputationalPaths/Path/Polygraph/ThreeCells.lean`
- `ComputationalPaths/Path/Algebra/DerivedCategoryPaths.lean`
- `ComputationalPaths/Path/Algebra/GroupStructures.lean`
- `ComputationalPaths/Path/Algebra/OpetopicSetsDeep.lean`
- `ComputationalPaths/Path/Category/PresheafPaths.lean`
- `ComputationalPaths/Path/Computation/DenotationalPaths.lean`
- `ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean`
- `ComputationalPaths/Path/Rewrite/StringRewriting.lean`
- `ComputationalPaths/Path/Topology/StratifiedSpaceDeep.lean`
- `ComputationalPaths/Path/Algebra/AdjunctionCoherenceDeep.lean`
- `ComputationalPaths/Path/Algebra/GaloisDeep2.lean`
- `ComputationalPaths/Path/Algebra/PetriNetRewritingDeep.lean`
- `ComputationalPaths/Path/Homotopy/PathSpaceFibration.lean`
- `ComputationalPaths/Path/Homotopy/SerreModC.lean`
- `ComputationalPaths/Path/Homotopy/SmashProduct.lean`
- `ComputationalPaths/Path/InfinityGroupoid.lean`
- `ComputationalPaths/Path/Logic/ModalPathDeep.lean`
- `ComputationalPaths/Path/Algebra/FieldPaths.lean`
- `ComputationalPaths/Path/Algebra/HopfAlgebraPaths.lean`
- `ComputationalPaths/Path/Algebra/QuantumGroupDeep2.lean`
- `ComputationalPaths/Path/Homotopy/CoveringFibrationAlgebra.lean`
- `ComputationalPaths/Path/Homotopy/FiberBundle.lean`
- `ComputationalPaths/Path/Homotopy/LocalizationHomotopy.lean`
- `ComputationalPaths/Path/Homotopy/MooreSpace.lean`
- `ComputationalPaths/Path/Homotopy/ObstructionTheoryDeep.lean`
- `ComputationalPaths/Path/Polygraph/RwEqDerivation.lean`
- `ComputationalPaths/SieveTheory.lean`
- Directly required import/root wiring for those modules.

**Out of scope:**

- `ComputationalPaths/Path/Basic/Core.lean`, which is an intentional
  foundational false positive from the audit heuristic.
- Other Lean modules, including scaffold-heavy files that already contain
  some literal `RwEq` or `Path.trans`; they require later criterion-driven
  tranches.
- Broad API redesigns, unrelated refactors, mass file deletion, dependency
  upgrades, paper changes, or generated documentation changes.
- Formalizing external mathematics beyond what is needed to replace the
  target modules' current scaffolds.

## Applicable Project Conventions

**Quality gate commands:**

- `python3 scripts/check_invariants.py`
- Targeted `lake build <module>` for every edited target module.
- `lake build`
- `git diff --check`

**Commit convention:**

- `type(scope): [B/I] description`, imperative and at most 72 characters.
- Builder trailer: `Assisted-by: OpenAI:GPT-5.6-Sol`
- Inspector trailer: `Assisted-by: OpenAI:GPT-5.6-Luna`
- Also include
  `Co-authored-by: Copilot App <223556219+Copilot@users.noreply.github.com>`.
- One Builder commit and one Inspector commit per iteration; never amend.

**Guidelines:**

- `AGENTS.md`
- `README.md`
- `docs/axioms.md`
- `.github/workflows/lean.yml`
- `.github/workflows/lean_action_ci.yml`

**Rules:**

- Zero `sorry`, zero `admit`, and zero custom `axiom` declarations.
- Use `Path` for equality evidence and integrate `RwEq` or multi-step
  `Path.trans` genuinely in each target file.
- Prefer domain-specific `Step` types and typed certificate records where
  appropriate.
- Preserve public APIs where possible and never weaken theorem statements.
- Keep abstract `True` only for explicitly documented, genuinely
  unformalized external mathematics; this goal's target scaffolds must be
  replaced rather than relabeled.
- Follow the existing import, naming, formatting, and proof style of each
  module.
