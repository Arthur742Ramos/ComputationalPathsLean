/- 
# Atiyah-Hirzebruch spectral sequence paths

This module assembles pages, differentials, and convergence into an
Atiyah-Hirzebruch package with explicit computational-path witnesses for edge
maps, Chern-character style comparison paths, and filtration stabilization.
-/

import ComputationalPaths.SpectralSequence.Convergence

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- A computational-path package for an Atiyah-Hirzebruch style spectral sequence. -/
structure AtiyahHirzebruchSequence where
  /-- Underlying page system. -/
  pages : Pages.{u}
  /-- Differential data with `d² = 0` witnesses. -/
  differentials : Differentials pages
  /-- Convergence data into limiting terms. -/
  convergence : Convergence pages differentials
  /-- Skeletal filtration action on `(0,0)` terms. -/
  skeletalFiltration : Nat → Nat → pages.term 0 0 → pages.term 0 0
  /-- Generalized cohomology filtration action on `(0,0)` terms. -/
  kFiltration : Nat → Nat → pages.term 0 0 → pages.term 0 0
  /-- Edge-map witness from generalized cohomology to skeletal filtration. -/
  edgePath :
    ∀ (n r : Nat),
      Path (kFiltration n r (pages.base 0 0))
        (skeletalFiltration n r (pages.base 0 0))
  /-- Primitive rewrite witness for left-unit normalization on edge paths. -/
  edgeStep :
    ∀ (n r : Nat),
      Path.Step
        (Path.trans
          (Path.refl (kFiltration n r (pages.base 0 0)))
          (edgePath n r))
        (edgePath n r)
  /-- Chern-character style witness relating successive filtrations. -/
  chernPath :
    ∀ (n r : Nat),
      Path (kFiltration (n + 1) r (pages.base 0 0))
        (skeletalFiltration n r (pages.base 0 0))
  /-- Primitive rewrite witness for right-unit normalization on Chern paths. -/
  chernStep :
    ∀ (n r : Nat),
      Path.Step
        (Path.trans
          (chernPath n r)
          (Path.refl (skeletalFiltration n r (pages.base 0 0))))
        (chernPath n r)
  /-- Stabilization witness for skeletal filtration classes in the limit. -/
  skeletalStabilizePath :
    ∀ (n r : Nat),
      Path
        (convergence.embed 0 0
          (pages.shift r 0 0 (skeletalFiltration n r (pages.base 0 0))))
        (convergence.embed 0 0 (skeletalFiltration n r (pages.base 0 0)))
  /-- Stabilization witness for generalized cohomology filtration classes. -/
  kStabilizePath :
    ∀ (n r : Nat),
      Path
        (convergence.embed 0 0
          (pages.shift r 0 0 (kFiltration n r (pages.base 0 0))))
        (convergence.embed 0 0 (kFiltration n r (pages.base 0 0)))

namespace AtiyahHirzebruchSequence

variable (A : AtiyahHirzebruchSequence.{u})

/-- Distinguished `E₂` representative at bidegree `(0,0)`. -/
noncomputable def e2Base : A.pages.term 0 0 :=
  A.pages.base 0 0

/-- Skeletal filtration class extracted from the distinguished representative. -/
noncomputable def skeletalClass (n r : Nat) : A.pages.term 0 0 :=
  A.skeletalFiltration n r A.e2Base

/-- Generalized cohomology filtration class extracted from the distinguished representative. -/
noncomputable def kClass (n r : Nat) : A.pages.term 0 0 :=
  A.kFiltration n r A.e2Base

/-- Edge-map witness at filtration level `n` and page `r`. -/
noncomputable def edge (n r : Nat) :
    Path (A.kClass n r) (A.skeletalClass n r) :=
  A.edgePath n r

noncomputable def edge_rweq (n r : Nat) :
    RwEq
      (Path.trans (Path.refl (A.kClass n r)) (A.edge n r))
      (A.edge n r) :=
  rweq_of_step (A.edgeStep n r)

/-- Chern-character style witness at filtration level `n` and page `r`. -/
noncomputable def chernCharacter (n r : Nat) :
    Path (A.kClass (n + 1) r) (A.skeletalClass n r) :=
  A.chernPath n r

noncomputable def chern_rweq (n r : Nat) :
    RwEq
      (Path.trans (A.chernCharacter n r) (Path.refl (A.skeletalClass n r)))
      (A.chernCharacter n r) :=
  rweq_of_step (A.chernStep n r)

/-- Loop induced by the edge-map witness and its inverse. -/
noncomputable def edgeLoop (n r : Nat) :
    Path (A.kClass n r) (A.kClass n r) :=
  Path.trans (A.edge n r) (Path.symm (A.edge n r))

noncomputable def edgeLoop_contracts (n r : Nat) :
    RwEq (A.edgeLoop n r) (Path.refl (A.kClass n r)) := by
  unfold edgeLoop
  exact rweq_cmpA_inv_right (A.edge n r)

/-- Shifted edge-map witness mapped into the limiting term. -/
noncomputable def shiftedEdge (n r : Nat) :
    Path
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 (A.kClass n r)))
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 (A.skeletalClass n r))) :=
  Path.congrArg
    (fun x => A.convergence.embed 0 0 (A.pages.shift r 0 0 x))
    (A.edge n r)

/-- Edge-map witness after stabilization in the skeletal filtration. -/
noncomputable def edgeToSkeletalLimit (n r : Nat) :
    Path
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 (A.kClass n r)))
      (A.convergence.embed 0 0 (A.skeletalClass n r)) :=
  Path.trans (A.shiftedEdge n r) (A.skeletalStabilizePath n r)

noncomputable def edgeToSkeletalLimit_rweq (n r : Nat) :
    RwEq
      (Path.trans
        (A.edgeToSkeletalLimit n r)
        (Path.refl (A.convergence.embed 0 0 (A.skeletalClass n r))))
      (A.edgeToSkeletalLimit n r) :=
  rweq_cmpA_refl_right (A.edgeToSkeletalLimit n r)

/-- `d² = 0` transported through the generalized cohomology filtration at `(0,0)`. -/
noncomputable def kBoundaryCompression (n r : Nat) :
    Path
      (A.kFiltration n r
        (A.differentials.d r 0 0 (A.differentials.d r 0 0 A.e2Base)))
      (A.kClass n r) :=
  Path.congrArg (A.kFiltration n r) (A.differentials.dSquaredPath r 0 0)

/-- Shifted generalized-cohomology boundary compression mapped into the limit. -/
noncomputable def shiftedKBoundaryCompression (n r : Nat) :
    Path
      (A.convergence.embed 0 0
        (A.pages.shift r 0 0
          (A.kFiltration n r
            (A.differentials.d r 0 0 (A.differentials.d r 0 0 A.e2Base)))))
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 (A.kClass n r))) :=
  Path.congrArg
    (fun x => A.convergence.embed 0 0 (A.pages.shift r 0 0 x))
    (A.kBoundaryCompression n r)

/-- Shifted generalized-cohomology boundaries converge to the stabilized class. -/
noncomputable def kBoundaryToLimit (n r : Nat) :
    Path
      (A.convergence.embed 0 0
        (A.pages.shift r 0 0
          (A.kFiltration n r
            (A.differentials.d r 0 0 (A.differentials.d r 0 0 A.e2Base)))))
      (A.convergence.embed 0 0 (A.kClass n r)) :=
  Path.trans (A.shiftedKBoundaryCompression n r) (A.kStabilizePath n r)

noncomputable def kBoundaryToLimit_rweq (n r : Nat) :
    RwEq
      (Path.trans
        (A.kBoundaryToLimit n r)
        (Path.refl (A.convergence.embed 0 0 (A.kClass n r))))
      (A.kBoundaryToLimit n r) :=
  rweq_cmpA_refl_right (A.kBoundaryToLimit n r)

end AtiyahHirzebruchSequence

/-- Canonical trivial Atiyah-Hirzebruch package. -/
noncomputable def trivialAtiyahHirzebruchSequence : AtiyahHirzebruchSequence where
  pages := trivialPages
  differentials := trivialDifferentials
  convergence := trivialConvergence
  skeletalFiltration := fun _ _ _ => PUnit.unit
  kFiltration := fun _ _ _ => PUnit.unit
  edgePath := fun _ _ => Path.refl PUnit.unit
  edgeStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)
  chernPath := fun _ _ => Path.refl PUnit.unit
  chernStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  skeletalStabilizePath := fun _ _ => Path.refl PUnit.unit
  kStabilizePath := fun _ _ => Path.refl PUnit.unit

end SpectralSequence
end ComputationalPaths
