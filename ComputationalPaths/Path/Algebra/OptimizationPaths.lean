/-
# Optimization via Computational Paths

Objective functions, feasible sets, optimality conditions as path equalities,
convexity as path midpoint property, gradient descent as path iteration,
duality — using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (22 theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.OptimizationPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Objective functions and feasibility -/

/-- An optimization problem: objective function, feasibility predicate,
    and optimality witnessed by paths. -/
structure OptProblem (A : Type u) where
  objective : A → A
  feasible  : A → Prop
  optPath : ∀ {a b : A}, feasible a → feasible b →
    Path (objective a) (objective b) → Prop

/-- A feasible solution with its witness -/
structure FeasibleSol (P : OptProblem A) where
  point : A
  isFeasible : P.feasible point

/-- Path between objective values of two feasible solutions -/
def objectivePath (P : OptProblem A) (s₁ s₂ : FeasibleSol P)
    (h : P.objective s₁.point = P.objective s₂.point) :
    Path (P.objective s₁.point) (P.objective s₂.point) :=
  Path.ofEq h

/-- Objective path steps are a singleton -/
theorem objectivePath_steps (P : OptProblem A) (s₁ s₂ : FeasibleSol P)
    (h : P.objective s₁.point = P.objective s₂.point) :
    (objectivePath P s₁ s₂ h).steps =
    [Step.mk (P.objective s₁.point) (P.objective s₂.point) h] := by
  simp [objectivePath]

/-! ## Convexity via path midpoints -/

/-- A convex structure: midpoint operation satisfying path commutativity -/
structure PathConvex (A : Type u) where
  mid : A → A → A
  mid_comm : ∀ a b : A, Path (mid a b) (mid b a)
  mid_idem : ∀ a : A, Path (mid a a) a

/-- Midpoint commutativity composes with its inverse to give rfl proof -/
theorem mid_comm_symm_trans (C : PathConvex A) (a b : A) :
    (Path.trans (C.mid_comm a b) (Path.symm (C.mid_comm a b))).proof = rfl := by
  simp

/-- CongrArg distributes over midpoint idempotence followed by symm -/
theorem congrArg_mid_idem_symm (C : PathConvex A) (f : A → B) (a : A) :
    Path.congrArg f (Path.symm (C.mid_idem a)) =
    Path.symm (Path.congrArg f (C.mid_idem a)) := by
  simp

/-- CongrArg distributes over trans of midpoint paths -/
theorem congrArg_mid_trans (C : PathConvex A) (f : A → B) (a : A) :
    Path.congrArg f (Path.trans (C.mid_comm a a) (C.mid_idem a)) =
    Path.trans (Path.congrArg f (C.mid_comm a a)) (Path.congrArg f (C.mid_idem a)) := by
  simp

/-- Midpoint idempotence and symm compose to rfl at proof level -/
theorem mid_idem_roundtrip_proof (C : PathConvex A) (a : A) :
    (Path.trans (C.mid_idem a) (Path.symm (C.mid_idem a))).proof = rfl := by
  simp

/-- Transport along midpoint idempotence and back is identity -/
theorem transport_mid_idem_roundtrip {P : A → Type v} (C : PathConvex A) (a : A)
    (x : P (C.mid a a)) :
    transport (symm (C.mid_idem a)) (transport (C.mid_idem a) x) = x :=
  transport_symm_left (C.mid_idem a) x

/-! ## Gradient descent as path iteration -/

/-- An iterative descent structure: a step map with fixed-point path -/
structure DescentIter (A : Type u) where
  step : A → A
  fixedPt : A
  isFixed : step fixedPt = fixedPt

/-- Path witnessing the fixed point -/
def fixedPath (D : DescentIter A) : Path (D.step D.fixedPt) D.fixedPt :=
  Path.ofEq D.isFixed

/-- The n-fold iteration of the step map -/
def iterStep (D : DescentIter A) : Nat → A → A
  | 0, a => a
  | n+1, a => D.step (iterStep D n a)

/-- Iteration at 0 is the identity -/
theorem iterStep_zero (D : DescentIter A) (a : A) :
    iterStep D 0 a = a := rfl

/-- Iteration at 1 is a single step -/
theorem iterStep_one (D : DescentIter A) (a : A) :
    iterStep D 1 a = D.step a := rfl

/-- Fixed point is preserved by iteration -/
theorem iterStep_fixedPt (D : DescentIter A) (n : Nat) :
    iterStep D n D.fixedPt = D.fixedPt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterStep, ih, D.isFixed]

/-- Path from iterated fixed point to fixed point -/
def iterFixedPath (D : DescentIter A) (n : Nat) :
    Path (iterStep D n D.fixedPt) D.fixedPt :=
  Path.ofEq (iterStep_fixedPt D n)

/-- CongrArg applied to fixed path -/
theorem congrArg_fixedPath (D : DescentIter A) (f : A → B) :
    Path.congrArg f (fixedPath D) =
    Path.ofEq (_root_.congrArg f D.isFixed) := by
  simp [fixedPath, Path.congrArg, Path.ofEq, Step.map]

/-- Transport along iterated fixed path at 0 is identity -/
theorem transport_iterFixed_zero {P : A → Type v} (D : DescentIter A)
    (x : P D.fixedPt) :
    transport (iterFixedPath D 0) x = x := by
  unfold iterFixedPath iterStep_fixedPt; rfl

/-! ## Duality via path symmetry -/

/-- A dual pair: primal and dual problems related by path symmetry -/
structure DualPair (A : Type u) where
  primal : A → A
  dual   : A → A
  duality : ∀ a : A, Path (primal (dual a)) (dual (primal a))

/-- Weak duality: symmetric of the duality path -/
def weakDualPath (D : DualPair A) (a : A) :
    Path (D.dual (D.primal a)) (D.primal (D.dual a)) :=
  Path.symm (D.duality a)

/-- Strong duality: duality followed by its inverse is reflexive at proof level -/
theorem strong_duality_proof (D : DualPair A) (a : A) :
    (trans (D.duality a) (weakDualPath D a)).proof = rfl := by
  simp

/-- Transport along duality and back is identity -/
theorem transport_duality_roundtrip {P : A → Type v} (D : DualPair A) (a : A)
    (x : P (D.primal (D.dual a))) :
    transport (symm (D.duality a)) (transport (D.duality a) x) = x :=
  transport_symm_left (D.duality a) x

/-- CongrArg distributes over duality followed by symm -/
theorem congrArg_duality_symm (D : DualPair A) (f : A → B) (a : A) :
    Path.congrArg f (weakDualPath D a) =
    Path.symm (Path.congrArg f (D.duality a)) := by
  simp [weakDualPath]

/-! ## Optimality conditions as path equalities -/

/-- KKT-like condition: stationarity witnessed by a path -/
structure KKTCondition (A : Type u) where
  gradient : A → A
  constraint : A → A
  multiplier : A → A
  stationarity : ∀ a : A,
    Path (gradient a) (constraint (multiplier a))

/-- Symm of stationarity gives reverse direction -/
def kkt_reverse (K : KKTCondition A) (a : A) :
    Path (K.constraint (K.multiplier a)) (K.gradient a) :=
  Path.symm (K.stationarity a)

/-- Stationarity roundtrip proof is rfl -/
theorem kkt_roundtrip_proof (K : KKTCondition A) (a : A) :
    (Path.trans (K.stationarity a) (kkt_reverse K a)).proof = rfl := by
  simp

/-- Transport along stationarity and back is identity -/
theorem kkt_transport_roundtrip {P : A → Type v} (K : KKTCondition A) (a : A)
    (x : P (K.gradient a)) :
    transport (kkt_reverse K a) (transport (K.stationarity a) x) = x :=
  transport_symm_left (K.stationarity a) x

/-- CongrArg of stationarity and its reverse -/
theorem kkt_congrArg_reverse (K : KKTCondition A) (f : A → B) (a : A) :
    Path.congrArg f (kkt_reverse K a) =
    Path.symm (Path.congrArg f (K.stationarity a)) := by
  unfold kkt_reverse; simp

/-! ## Pareto optimality -/

/-- Path from applying a function to equal points -/
def paretoObjectivePath (f : A → A)
    (a b : A) (h : f a = f b) :
    Path (f a) (f b) :=
  Path.ofEq h

/-- Symmetry of Pareto paths -/
theorem pareto_symm (f : A → A)
    (a b : A) (h : f a = f b) :
    Path.symm (paretoObjectivePath f a b h) =
    paretoObjectivePath f b a h.symm := by
  simp [paretoObjectivePath]

/-- Step structure of a Pareto path -/
theorem pareto_steps (f : A → A)
    (a b : A) (h : f a = f b) :
    (paretoObjectivePath f a b h).steps =
    [Step.mk (f a) (f b) h] := by
  simp [paretoObjectivePath]

/-- CongrArg applied to Pareto path -/
theorem pareto_congrArg (f : A → A) (g : A → B)
    (a b : A) (h : f a = f b) :
    Path.congrArg g (paretoObjectivePath f a b h) =
    Path.ofEq (_root_.congrArg g h) := by
  simp [paretoObjectivePath, Path.congrArg, Path.ofEq, Step.map]

/-- Transport along Pareto path -/
theorem pareto_transport {P : A → Type v} (f : A → A)
    (a b : A) (h : f a = f b) (x : P (f a)) :
    Path.transport (paretoObjectivePath f a b h) x = h ▸ x := by
  simp [Path.transport]

end ComputationalPaths.Path.Algebra.OptimizationPaths
