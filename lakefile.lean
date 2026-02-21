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
    `CompPaths.Coherence.AssociativityCoherence,
    `CompPaths.Coherence.UnitCoherence,
    `CompPaths.Coherence.InverseCoherence,
    `CompPaths.Coherence.InterchangeLaw,
    `CompPaths.DeformationTheory.DeformationPaths,
    `CompPaths.DeformationTheory.ObstructionPaths,
    `CompPaths.OmegaGroupoid.WeakGroupoidPaths,
    `CompPaths.OmegaGroupoid.CoherencePaths,
    `CompPaths.Examples.FundamentalGroupCircle,
    `CompPaths.Examples.FundamentalGroupTorus,
    `CompPaths.Rewriting.KnuthBendix,
    `CompPaths.Rewriting.CriticalPairs,
    `CompPaths.Rewriting.TerminationProofs]

@[default_target]
lean_exe computational_paths where
  root := `Main
