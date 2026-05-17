import Lake
open Lake DSL

package «computational_paths» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib ComputationalPaths where
  /-
  Keep the comprehensive `ComputationalPaths` root together with selected
  historical umbrella roots.  The extra roots are intentionally redundant with
  the full hub import, but preserve direct `lake build ComputationalPaths.X`
  entrypoints used for targeted validation and downstream smoke checks.
  -/
  roots := #[
    `ComputationalPaths,
    -- Path and foundational umbrella targets.
    `ComputationalPaths.Path.Algebra,
    `ComputationalPaths.Path.Category,
    `ComputationalPaths.Coherence,
    `ComputationalPaths.Comparison,
    `ComputationalPaths.Path.Confluence,
    `ComputationalPaths.Path.Context,
    `ComputationalPaths.Path.CoveringSpace,
    `ComputationalPaths.CwF,
    `ComputationalPaths.DeformationTheory,
    `ComputationalPaths.Examples,
    `ComputationalPaths.Path.HIT,
    `ComputationalPaths.Path.Homotopy,
    `ComputationalPaths.Path.OmegaGroupoidCompPaths,
    `ComputationalPaths.Path.Rewriting,
    `ComputationalPaths.Path.Transport,
    -- Top-level companion umbrella targets.
    `ComputationalPaths.TypeFormers]

-- Default smoke executable; library consumers should import one of the roots above.
@[default_target]
lean_exe computational_paths where
  root := `Main
