import Lake
open Lake DSL

package «computational_paths» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib ComputationalPaths where
  roots := #[`ComputationalPaths,
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
    `ComputationalPaths.TypeFormers]

@[default_target]
lean_exe computational_paths where
  root := `Main
