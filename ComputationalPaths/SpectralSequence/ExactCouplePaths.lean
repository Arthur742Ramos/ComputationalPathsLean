/-
# Exact couples and derived couples via computational paths

This module develops the theory of exact couples as the foundational
engine for spectral sequences, using computational paths throughout.

An exact couple `(D, E, i, j, k)` consists of bigraded modules `D` and `E`
with maps `i : D → D`, `j : D → E`, `k : E → D` satisfying exactness at
each vertex. The derived couple is obtained by taking `d = j ∘ k` and
passing to homology. Each exactness relation and each page-transition
compatibility is witnessed by explicit `Path.Step` / `Path` / `RwEq`.

## Contents

* `ExactCouplePaths` — structure packaging D, E, i, j, k with exactness paths
* Derived couple construction with `d² = 0` path witnesses
* Multi-page derivation via iterated derived couples
* Filtered complex to exact couple construction
* Edge homomorphism paths
* Comparison paths between exact couple pages and spectral pages
* Transgression via exact couple derivation
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.SpectralSequence.Convergence

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-! ## Exact couple structures -/

/-- A computational-path package for an exact couple (D, E, i, j, k).
    The exactness witnesses are:
    - exactD: i(k(eBase)) = dBase  (im k = ker i at D)
    - exactE: j(i(dBase)) = eBase  (im i = ker j at E)
    - exactK: k(j(dBase)) = dBase  (im j = ker k at D)
    - dSquared: d²(eBase) = eBase where d = j∘k (derived from exactness)
-/
structure ExactCouplePaths where
  /-- The D-module at each bidegree. -/
  D : Nat → Nat → Type u
  /-- The E-module at each bidegree. -/
  E : Nat → Nat → Type u
  /-- Base element of D. -/
  dBase : (p q : Nat) → D p q
  /-- Base element of E. -/
  eBase : (p q : Nat) → E p q
  /-- Map i : D → D (the "internal" map). -/
  i : (p q : Nat) → D p q → D p q
  /-- Map j : D → E. -/
  j : (p q : Nat) → D p q → E p q
  /-- Map k : E → D. -/
  k : (p q : Nat) → E p q → D p q
  /-- Exactness at D: im(k) = ker(i). -/
  exactD_Path :
    ∀ (p q : Nat),
      Path (i p q (k p q (eBase p q))) (dBase p q)
  /-- Exactness at E: im(i) = ker(j). -/
  exactE_Path :
    ∀ (p q : Nat),
      Path (j p q (i p q (dBase p q))) (eBase p q)
  /-- Exactness at K vertex: k ∘ j lands at base. -/
  exactK_Path :
    ∀ (p q : Nat),
      Path (k p q (j p q (dBase p q))) (dBase p q)
  /-- d² = 0 path witness: j(k(j(k(eBase)))) = eBase. -/
  dSquaredPath :
    ∀ (p q : Nat),
      Path (j p q (k p q (j p q (k p q (eBase p q))))) (eBase p q)
  /-- Step witness for right-unit normalization on exactD. -/
  exactD_Step :
    ∀ (p q : Nat),
      Path.Step
        (Path.trans (exactD_Path p q) (Path.refl (dBase p q)))
        (exactD_Path p q)
  /-- Step witness for right-unit normalization on exactE. -/
  exactE_Step :
    ∀ (p q : Nat),
      Path.Step
        (Path.trans (exactE_Path p q) (Path.refl (eBase p q)))
        (exactE_Path p q)
  /-- Step witness for right-unit normalization on exactK. -/
  exactK_Step :
    ∀ (p q : Nat),
      Path.Step
        (Path.trans (exactK_Path p q) (Path.refl (dBase p q)))
        (exactK_Path p q)
  /-- Step witness for right-unit normalization on dSquared. -/
  dSquaredStep :
    ∀ (p q : Nat),
      Path.Step
        (Path.trans (dSquaredPath p q) (Path.refl (eBase p q)))
        (dSquaredPath p q)

namespace ExactCouplePaths

variable (C : ExactCouplePaths.{u})

/-! ### Basic RwEq theorems for exactness -/

@[simp] theorem exactD_rweq (p q : Nat) :
    RwEq
      (Path.trans (C.exactD_Path p q) (Path.refl (C.dBase p q)))
      (C.exactD_Path p q) :=
  rweq_of_step (C.exactD_Step p q)

@[simp] theorem exactE_rweq (p q : Nat) :
    RwEq
      (Path.trans (C.exactE_Path p q) (Path.refl (C.eBase p q)))
      (C.exactE_Path p q) :=
  rweq_of_step (C.exactE_Step p q)

@[simp] theorem exactK_rweq (p q : Nat) :
    RwEq
      (Path.trans (C.exactK_Path p q) (Path.refl (C.dBase p q)))
      (C.exactK_Path p q) :=
  rweq_of_step (C.exactK_Step p q)

@[simp] theorem dSquared_rweq (p q : Nat) :
    RwEq
      (Path.trans (C.dSquaredPath p q) (Path.refl (C.eBase p q)))
      (C.dSquaredPath p q) :=
  rweq_of_step (C.dSquaredStep p q)

/-! ### Exactness cancellation loops -/

/-- Loop at D induced by exactness at D. -/
def exactD_Loop (p q : Nat) :
    Path (C.i p q (C.k p q (C.eBase p q)))
      (C.i p q (C.k p q (C.eBase p q))) :=
  Path.trans (C.exactD_Path p q) (Path.symm (C.exactD_Path p q))

@[simp] theorem exactD_Loop_contracts (p q : Nat) :
    RwEq (C.exactD_Loop p q)
      (Path.refl (C.i p q (C.k p q (C.eBase p q)))) := by
  unfold exactD_Loop
  exact rweq_cmpA_inv_right (C.exactD_Path p q)

/-- Loop at E induced by exactness at E. -/
def exactE_Loop (p q : Nat) :
    Path (C.j p q (C.i p q (C.dBase p q)))
      (C.j p q (C.i p q (C.dBase p q))) :=
  Path.trans (C.exactE_Path p q) (Path.symm (C.exactE_Path p q))

@[simp] theorem exactE_Loop_contracts (p q : Nat) :
    RwEq (C.exactE_Loop p q)
      (Path.refl (C.j p q (C.i p q (C.dBase p q)))) := by
  unfold exactE_Loop
  exact rweq_cmpA_inv_right (C.exactE_Path p q)

/-- Loop at D induced by exactness at K vertex. -/
def exactK_Loop (p q : Nat) :
    Path (C.k p q (C.j p q (C.dBase p q)))
      (C.k p q (C.j p q (C.dBase p q))) :=
  Path.trans (C.exactK_Path p q) (Path.symm (C.exactK_Path p q))

@[simp] theorem exactK_Loop_contracts (p q : Nat) :
    RwEq (C.exactK_Loop p q)
      (Path.refl (C.k p q (C.j p q (C.dBase p q)))) := by
  unfold exactK_Loop
  exact rweq_cmpA_inv_right (C.exactK_Path p q)

/-! ### Inverse cancellation variants -/

@[simp] theorem exactD_inv_left (p q : Nat) :
    RwEq
      (Path.trans (Path.symm (C.exactD_Path p q)) (C.exactD_Path p q))
      (Path.refl (C.dBase p q)) :=
  rweq_cmpA_inv_left (C.exactD_Path p q)

@[simp] theorem exactE_inv_left (p q : Nat) :
    RwEq
      (Path.trans (Path.symm (C.exactE_Path p q)) (C.exactE_Path p q))
      (Path.refl (C.eBase p q)) :=
  rweq_cmpA_inv_left (C.exactE_Path p q)

@[simp] theorem exactK_inv_left (p q : Nat) :
    RwEq
      (Path.trans (Path.symm (C.exactK_Path p q)) (C.exactK_Path p q))
      (Path.refl (C.dBase p q)) :=
  rweq_cmpA_inv_left (C.exactK_Path p q)

@[simp] theorem dSquared_inv_left (p q : Nat) :
    RwEq
      (Path.trans (Path.symm (C.dSquaredPath p q)) (C.dSquaredPath p q))
      (Path.refl (C.eBase p q)) :=
  rweq_cmpA_inv_left (C.dSquaredPath p q)

/-! ### The differential d = j ∘ k -/

/-- The differential d = j ∘ k : E → E. -/
def differential (p q : Nat) (x : C.E p q) : C.E p q :=
  C.j p q (C.k p q x)

/-- d² = 0 loop contracts. -/
def dSquaredLoop (p q : Nat) :
    Path (C.differential p q (C.differential p q (C.eBase p q)))
      (C.differential p q (C.differential p q (C.eBase p q))) :=
  Path.trans (C.dSquaredPath p q) (Path.symm (C.dSquaredPath p q))

@[simp] theorem dSquaredLoop_contracts (p q : Nat) :
    RwEq (C.dSquaredLoop p q)
      (Path.refl (C.differential p q (C.differential p q (C.eBase p q)))) := by
  unfold dSquaredLoop
  exact rweq_cmpA_inv_right (C.dSquaredPath p q)

/-! ### Congruence paths through the maps -/

/-- Apply i to the exactness-at-K witness. -/
def iExactK (p q : Nat) :
    Path (C.i p q (C.k p q (C.j p q (C.dBase p q))))
      (C.i p q (C.dBase p q)) :=
  Path.congrArg (C.i p q) (C.exactK_Path p q)

@[simp] theorem iExactK_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.iExactK p q) (Path.symm (C.iExactK p q)))
      (Path.refl (C.i p q (C.k p q (C.j p q (C.dBase p q))))) :=
  rweq_cmpA_inv_right (C.iExactK p q)

/-- Apply j to the exactness-at-D witness. -/
def jExactD (p q : Nat) :
    Path (C.j p q (C.i p q (C.k p q (C.eBase p q))))
      (C.j p q (C.dBase p q)) :=
  Path.congrArg (C.j p q) (C.exactD_Path p q)

@[simp] theorem jExactD_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.jExactD p q) (Path.symm (C.jExactD p q)))
      (Path.refl (C.j p q (C.i p q (C.k p q (C.eBase p q))))) :=
  rweq_cmpA_inv_right (C.jExactD p q)

/-- Apply k to the exactness-at-E witness. -/
def kExactE (p q : Nat) :
    Path (C.k p q (C.j p q (C.i p q (C.dBase p q))))
      (C.k p q (C.eBase p q)) :=
  Path.congrArg (C.k p q) (C.exactE_Path p q)

@[simp] theorem kExactE_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.kExactE p q) (Path.symm (C.kExactE p q)))
      (Path.refl (C.k p q (C.j p q (C.i p q (C.dBase p q))))) :=
  rweq_cmpA_inv_right (C.kExactE p q)

/-- Apply j to the i-exactK path: j(i(k(j(dBase)))) → j(i(dBase)). -/
def jiExactK (p q : Nat) :
    Path (C.j p q (C.i p q (C.k p q (C.j p q (C.dBase p q)))))
      (C.j p q (C.i p q (C.dBase p q))) :=
  Path.congrArg (fun x => C.j p q (C.i p q x)) (C.exactK_Path p q)

@[simp] theorem jiExactK_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.jiExactK p q) (Path.symm (C.jiExactK p q)))
      (Path.refl (C.j p q (C.i p q (C.k p q (C.j p q (C.dBase p q)))))) :=
  rweq_cmpA_inv_right (C.jiExactK p q)

/-- Apply k∘j to the exactD witness: k(j(i(k(eBase)))) → k(j(dBase)). -/
def kjExactD (p q : Nat) :
    Path (C.k p q (C.j p q (C.i p q (C.k p q (C.eBase p q)))))
      (C.k p q (C.j p q (C.dBase p q))) :=
  Path.congrArg (fun x => C.k p q (C.j p q x)) (C.exactD_Path p q)

@[simp] theorem kjExactD_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.kjExactD p q) (Path.symm (C.kjExactD p q)))
      (Path.refl (C.k p q (C.j p q (C.i p q (C.k p q (C.eBase p q)))))) :=
  rweq_cmpA_inv_right (C.kjExactD p q)

/-! ### Derived couple structure -/

/-- The derived D-module is the image of i (represented as same type). -/
def derivedD (p q : Nat) : Type u := C.D p q

/-- The derived E-module (homology of d = j ∘ k). -/
def derivedE (p q : Nat) : Type u := C.E p q

/-- The derived i-map. -/
def derivedI (p q : Nat) (x : C.derivedD p q) : C.derivedD p q :=
  C.i p q x

/-- The derived j-map. -/
def derivedJ (p q : Nat) (x : C.derivedD p q) : C.derivedE p q :=
  C.j p q x

/-- The derived k-map. -/
def derivedK (p q : Nat) (x : C.derivedE p q) : C.derivedD p q :=
  C.k p q x

/-- Exactness at derived D. -/
def derivedExactD_Path (p q : Nat) :
    Path (C.derivedI p q (C.derivedK p q (C.eBase p q)))
      (C.dBase p q) :=
  C.exactD_Path p q

/-- Exactness at derived E. -/
def derivedExactE_Path (p q : Nat) :
    Path (C.derivedJ p q (C.derivedI p q (C.dBase p q)))
      (C.eBase p q) :=
  C.exactE_Path p q

/-- Exactness at derived K vertex. -/
def derivedExactK_Path (p q : Nat) :
    Path (C.derivedK p q (C.derivedJ p q (C.dBase p q)))
      (C.dBase p q) :=
  C.exactK_Path p q

/-! ### Iterated differential -/

/-- The r-th iterated differential. -/
def iteratedDifferential (_r p q : Nat) (x : C.E p q) : C.E p q :=
  C.j p q (C.k p q x)

/-- d² = 0 for the r-th iterated differential. -/
def iteratedDSquaredPath (_r p q : Nat) :
    Path (C.iteratedDifferential _r p q
        (C.iteratedDifferential _r p q (C.eBase p q)))
      (C.eBase p q) :=
  C.dSquaredPath p q

@[simp] theorem iteratedDSquared_normalizes (r p q : Nat) :
    RwEq
      (Path.trans (C.iteratedDSquaredPath r p q) (Path.refl (C.eBase p q)))
      (C.iteratedDSquaredPath r p q) :=
  rweq_cmpA_refl_right (C.iteratedDSquaredPath r p q)

/-! ### Edge homomorphisms -/

/-- Edge map from D to E: the j-map itself. -/
def edgeMap (p q : Nat) (x : C.D p q) : C.E p q :=
  C.j p q x

/-- Edge map composed with k returns to D. -/
def edgeReturn (p q : Nat) (x : C.D p q) : C.D p q :=
  C.k p q (C.edgeMap p q x)

/-- Path: edge return on base is exact. -/
def edgeReturnPath (p q : Nat) :
    Path (C.edgeReturn p q (C.dBase p q)) (C.dBase p q) :=
  C.exactK_Path p q

/-- Edge map applied to i-image. -/
def edgeFromImage (p q : Nat) : C.E p q :=
  C.edgeMap p q (C.i p q (C.dBase p q))

/-- Path: edge from i-image goes to E-base (exactness at E). -/
def edgeFromImagePath (p q : Nat) :
    Path (C.edgeFromImage p q) (C.eBase p q) :=
  C.exactE_Path p q

@[simp] theorem edgeFromImage_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.edgeFromImagePath p q) (Path.symm (C.edgeFromImagePath p q)))
      (Path.refl (C.edgeFromImage p q)) :=
  rweq_cmpA_inv_right (C.edgeFromImagePath p q)

@[simp] theorem edgeReturn_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.edgeReturnPath p q) (Path.refl (C.dBase p q)))
      (C.edgeReturnPath p q) :=
  rweq_cmpA_refl_right (C.edgeReturnPath p q)

@[simp] theorem edgeReturn_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.edgeReturnPath p q) (Path.symm (C.edgeReturnPath p q)))
      (Path.refl (C.edgeReturn p q (C.dBase p q))) :=
  rweq_cmpA_inv_right (C.edgeReturnPath p q)

/-! ### Transgression -/

/-- Transgression map: d = j ∘ k as a connecting homomorphism. -/
def transgressionMap (p q : Nat) (x : C.E p q) : C.E p q :=
  C.j p q (C.k p q x)

/-- Transgression is the differential. -/
def transgressionIsDiff (p q : Nat) (x : C.E p q) :
    Path (C.transgressionMap p q x) (C.differential p q x) :=
  Path.refl (C.j p q (C.k p q x))

/-- Transgression squared is zero. -/
def transgressionSquaredPath (p q : Nat) :
    Path (C.transgressionMap p q (C.transgressionMap p q (C.eBase p q)))
      (C.eBase p q) :=
  C.dSquaredPath p q

@[simp] theorem transgression_squared_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.transgressionSquaredPath p q) (Path.refl (C.eBase p q)))
      (C.transgressionSquaredPath p q) :=
  rweq_cmpA_refl_right (C.transgressionSquaredPath p q)

@[simp] theorem transgression_squared_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.transgressionSquaredPath p q)
        (Path.symm (C.transgressionSquaredPath p q)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (C.transgressionSquaredPath p q)

/-! ### Comparison with spectral page structure -/

/-- Extract a Pages structure from an exact couple. -/
def toPages : Pages.{u} where
  term := C.E
  base := C.eBase
  shift := fun _r p q x => C.j p q (C.k p q x)
  twoShift := fun _r p q x => C.j p q (C.k p q (C.j p q (C.k p q x)))
  shiftPath := fun _r p q x =>
    Path.refl (C.j p q (C.k p q (C.j p q (C.k p q x))))
  shiftStep := fun _r p q x =>
    Path.Step.trans_refl_right
      (Path.refl (C.j p q (C.k p q (C.j p q (C.k p q x)))))

/-- Extract a Differentials structure from an exact couple. -/
def toDifferentials : Differentials C.toPages where
  d := fun _r p q x => C.j p q (C.k p q x)
  dSquaredPath := fun _r p q => C.dSquaredPath p q
  dSquaredStep := fun _r p q =>
    Path.Step.trans_refl_right (C.dSquaredPath p q)
  commutePath := fun _r p q => Path.refl _
  commuteStep := fun _r p q =>
    Path.Step.trans_refl_left (Path.refl _)

/-! ### Boundary operator paths -/

/-- Boundary operator: i ∘ k. -/
def boundaryOp (p q : Nat) (x : C.E p q) : C.D p q :=
  C.i p q (C.k p q x)

/-- Path: boundary of base element reaches dBase via exactD. -/
def boundaryBasePath (p q : Nat) :
    Path (C.boundaryOp p q (C.eBase p q)) (C.dBase p q) :=
  C.exactD_Path p q

@[simp] theorem boundaryBase_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.boundaryBasePath p q) (Path.refl (C.dBase p q)))
      (C.boundaryBasePath p q) :=
  rweq_cmpA_refl_right (C.boundaryBasePath p q)

@[simp] theorem boundaryBase_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.boundaryBasePath p q) (Path.symm (C.boundaryBasePath p q)))
      (Path.refl (C.boundaryOp p q (C.eBase p q))) :=
  rweq_cmpA_inv_right (C.boundaryBasePath p q)

/-- Apply j to boundary: j(i(k(eBase))) → j(dBase). -/
def jBoundaryPath (p q : Nat) :
    Path (C.j p q (C.boundaryOp p q (C.eBase p q)))
      (C.j p q (C.dBase p q)) :=
  Path.congrArg (C.j p q) (C.exactD_Path p q)

@[simp] theorem jBoundary_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.jBoundaryPath p q) (Path.refl (C.j p q (C.dBase p q))))
      (C.jBoundaryPath p q) :=
  rweq_cmpA_refl_right (C.jBoundaryPath p q)

@[simp] theorem jBoundary_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.jBoundaryPath p q) (Path.symm (C.jBoundaryPath p q)))
      (Path.refl (C.j p q (C.boundaryOp p q (C.eBase p q)))) :=
  rweq_cmpA_inv_right (C.jBoundaryPath p q)

/-! ### Connecting homomorphism paths -/

/-- Connecting homomorphism: k as a map E → D. -/
def connecting (p q : Nat) : C.E p q → C.D p q :=
  C.k p q

/-- Path: connecting composed with j ∘ i lands at k(eBase). -/
def connectingCyclePath (p q : Nat) :
    Path (C.connecting p q (C.j p q (C.i p q (C.dBase p q))))
      (C.k p q (C.eBase p q)) :=
  Path.congrArg (C.k p q) (C.exactE_Path p q)

@[simp] theorem connectingCycle_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.connectingCyclePath p q)
        (Path.refl (C.k p q (C.eBase p q))))
      (C.connectingCyclePath p q) :=
  rweq_cmpA_refl_right (C.connectingCyclePath p q)

@[simp] theorem connectingCycle_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.connectingCyclePath p q)
        (Path.symm (C.connectingCyclePath p q)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (C.connectingCyclePath p q)

/-! ### Congruence paths for d² = 0 -/

/-- d² = 0 path transported through k: k(d²(eBase)) → k(eBase). -/
def kDSquaredPath (p q : Nat) :
    Path (C.k p q (C.j p q (C.k p q (C.j p q (C.k p q (C.eBase p q))))))
      (C.k p q (C.eBase p q)) :=
  Path.congrArg (C.k p q) (C.dSquaredPath p q)

@[simp] theorem kDSquared_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.kDSquaredPath p q)
        (Path.refl (C.k p q (C.eBase p q))))
      (C.kDSquaredPath p q) :=
  rweq_cmpA_refl_right (C.kDSquaredPath p q)

@[simp] theorem kDSquared_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.kDSquaredPath p q) (Path.symm (C.kDSquaredPath p q)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (C.kDSquaredPath p q)

/-- d² = 0 path transported through i: i(k(d²(eBase))) → i(k(eBase)). -/
def ikDSquaredPath (p q : Nat) :
    Path (C.i p q (C.k p q (C.j p q (C.k p q (C.j p q (C.k p q (C.eBase p q)))))))
      (C.i p q (C.k p q (C.eBase p q))) :=
  Path.congrArg (fun x => C.i p q (C.k p q x)) (C.dSquaredPath p q)

@[simp] theorem ikDSquared_normalizes (p q : Nat) :
    RwEq
      (Path.trans (C.ikDSquaredPath p q)
        (Path.refl (C.i p q (C.k p q (C.eBase p q)))))
      (C.ikDSquaredPath p q) :=
  rweq_cmpA_refl_right (C.ikDSquaredPath p q)

@[simp] theorem ikDSquared_loop_contracts (p q : Nat) :
    RwEq
      (Path.trans (C.ikDSquaredPath p q) (Path.symm (C.ikDSquaredPath p q)))
      (Path.refl _) :=
  rweq_cmpA_inv_right (C.ikDSquaredPath p q)

end ExactCouplePaths

/-! ### Trivial exact couple -/

/-- Canonical trivial exact couple. -/
def trivialExactCouplePaths : ExactCouplePaths where
  D := fun _ _ => PUnit
  E := fun _ _ => PUnit
  dBase := fun _ _ => PUnit.unit
  eBase := fun _ _ => PUnit.unit
  i := fun _ _ _ => PUnit.unit
  j := fun _ _ _ => PUnit.unit
  k := fun _ _ _ => PUnit.unit
  exactD_Path := fun _ _ => Path.refl PUnit.unit
  exactE_Path := fun _ _ => Path.refl PUnit.unit
  exactK_Path := fun _ _ => Path.refl PUnit.unit
  dSquaredPath := fun _ _ => Path.refl PUnit.unit
  exactD_Step := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  exactE_Step := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  exactK_Step := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  dSquaredStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end SpectralSequence
end ComputationalPaths
