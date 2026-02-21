import Lake
open Lake DSL

package «computational_paths» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib ComputationalPaths where
  roots := #[`ComputationalPaths]

@[default_target]
lean_lib CompPaths where
  roots := #[`CompPaths,
    `CompPaths.Confluence.ConfluenceDeep,
    `CompPaths.Confluence.WordProblem,
    `CompPaths.Rewriting.KnuthBendix,
    `CompPaths.Coherence.AssociativityCoherence,
    `CompPaths.Coherence.UnitCoherence,
    `CompPaths.Coherence.InverseCoherence,
    `CompPaths.Coherence.InterchangeLaw,
    `CompPaths.DeformationTheory.DeformationPaths,
    `CompPaths.DeformationTheory.ObstructionPaths,
    `CompPaths.OmegaGroupoid.WeakGroupoidPaths,
    `CompPaths.OmegaGroupoid.CoherencePaths,
    `CompPaths.OmegaGroupoid.HigherCellPaths,
    `CompPaths.Examples.FundamentalGroupCircle,
    `CompPaths.Examples.FundamentalGroupTorus]

@[default_target]
lean_exe computational_paths where
  root := `Main
