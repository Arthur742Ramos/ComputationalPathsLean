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
    `CompPaths.Comparison.HoTTComparison,
    `CompPaths.Category.EnrichedCategory,
    `CompPaths.Context.CongruenceClosure,
    `CompPaths.Confluence.ConfluenceDeep,
    `CompPaths.Coherence.AssociativityCoherence,
    `CompPaths.Coherence.UnitCoherence,
    `CompPaths.Coherence.InverseCoherence,
    `CompPaths.Coherence.InterchangeLaw,
    `CompPaths.Context.ContextDeep,
    `CompPaths.DeformationTheory.DeformationPaths,
    `CompPaths.DeformationTheory.ObstructionPaths,
    `CompPaths.Transport.PathOverPath,
    `CompPaths.Transport.TransportDeep,
    `CompPaths.TypeFormers.UniversalProperties,
    `CompPaths.OmegaGroupoid.WeakGroupoidPaths,
    `CompPaths.OmegaGroupoid.CoherencePaths,
    `CompPaths.OmegaGroupoid.TwoCategoryStructure,
    `CompPaths.OmegaGroupoid.GroupoidProofs,
    `CompPaths.Examples.FundamentalGroupTorus,
    `CompPaths.Homotopy.VanKampen,
    `CompPaths.Homotopy.VanKampenApplications,
    `CompPaths.Homotopy.FibrationSequence,
    `CompPaths.HIT.SuspensionDeep,
    `CompPaths.Rewriting.KnuthBendix,
    `CompPaths.Rewriting.CriticalPairs,
    `CompPaths.Rewriting.TerminationProofs,
    `CompPaths.CoveringSpace.CoveringDeep,
    `CompPaths.CoveringSpace.PathLifting,
    `CompPaths.Algebra.FreeGroupoid,
    `CompPaths.Algebra.PathAlgebra,
    `CompPaths.Algebra.Presentation,
    `CompPaths.Algebra.HomologicalAlgebra,
    `CompPaths.Algebra.SpectralSequence]

@[default_target]
lean_exe computational_paths where
  root := `Main
