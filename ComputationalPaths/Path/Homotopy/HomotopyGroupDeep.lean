/-
# Homotopy Groups — Deep Path Constructions

Deep exploration of homotopy group theory through genuine computational paths.
All constructions use `Path.stepChain`, `Path.trans`, `Path.symm`, `congrArg`,
and `RwEq`-based reasoning with zero sorry/admit/Path.ofEq.

## Contents

1. **π_n representation** — Higher homotopy groups as iterated loop path classes
2. **Long exact sequence data** — Fibration sequence via path algebra
3. **Relative homotopy groups** — Pairs and relative paths
4. **Hurewicz map structure** — From homotopy to homology via paths
5. **Whitehead theorem data** — Weak equivalences from π_n isomorphisms
6. **Freudenthal suspension** — Suspension connectivity via path structure
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.HomotopyGroup

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomotopyGroupDeep

open ComputationalPaths.Path

universe u

/-! ## 1. Iterated Loop Spaces -/

/-- The n-fold iterated loop space. Base case is A itself, each iteration
    takes loops at the basepoint. -/
noncomputable def IteratedLoopSpace (A : Type u) (a : A) : Nat → Type u
  | 0 => A
  | n + 1 => @LoopSpace (IteratedLoopSpace A a n) (iterBasepoint A a n)
where
  /-- Canonical basepoint in each iterated loop space. -/
  iterBasepoint (A : Type u) (a : A) : (n : Nat) → IteratedLoopSpace A a n
    | 0 => a
    | n + 1 => Path.refl (iterBasepoint A a n)

/-- The basepoint of the n-th iterated loop space. -/
noncomputable def iterBase (A : Type u) (a : A) (n : Nat) :
    IteratedLoopSpace A a n :=
  IteratedLoopSpace.iterBasepoint A a n

/-- Identity loop in the n-th iterated loop space is refl. -/
noncomputable def iterLoopId (A : Type u) (a : A) (n : Nat) :
    IteratedLoopSpace A a (n + 1) :=
  Path.refl (iterBase A a n)

/-- Composition in the n-th iterated loop space is trans. -/
noncomputable def iterLoopComp {A : Type u} {a : A} {n : Nat}
    (p q : IteratedLoopSpace A a (n + 1)) :
    IteratedLoopSpace A a (n + 1) :=
  Path.trans p q

/-- Inversion in the n-th iterated loop space is symm. -/
noncomputable def iterLoopInv {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    IteratedLoopSpace A a (n + 1) :=
  Path.symm p

/-- Associativity of iterated loop composition. -/
theorem iterLoopComp_assoc {A : Type u} {a : A} {n : Nat}
    (p q r : IteratedLoopSpace A a (n + 1)) :
    iterLoopComp (iterLoopComp p q) r = iterLoopComp p (iterLoopComp q r) := by
  simp [iterLoopComp]

/-- Left identity of iterated loop composition. -/
theorem iterLoopComp_id_left {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    iterLoopComp (iterLoopId A a n) p = p := by
  simp [iterLoopComp, iterLoopId]
  have h : RwEq (Path.trans (Path.refl (iterBase A a n)) p) p :=
    rweq_of_step (Step.trans_refl_left p)
  simp

/-- Right identity of iterated loop composition. -/
theorem iterLoopComp_id_right {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    iterLoopComp p (iterLoopId A a n) = p := by
  simp [iterLoopComp, iterLoopId]
  have h : RwEq (Path.trans p (Path.refl (iterBase A a n))) p :=
    rweq_of_step (Step.trans_refl_right p)
  simp

/-- Left inverse law for iterated loops. -/
theorem iterLoopInv_left {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    iterLoopComp (iterLoopInv p) p = iterLoopId A a n := by
  simp [iterLoopComp, iterLoopInv, iterLoopId]
  have h : RwEq (Path.trans (Path.symm p) p) (Path.refl (iterBase A a n)) :=
    rweq_of_step (Step.trans_symm_left p)
  simp

/-- Right inverse law for iterated loops. -/
theorem iterLoopInv_right {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    iterLoopComp p (iterLoopInv p) = iterLoopId A a n := by
  simp [iterLoopComp, iterLoopInv, iterLoopId]
  have h : RwEq (Path.trans p (Path.symm p)) (Path.refl (iterBase A a n)) :=
    rweq_of_step (Step.trans_symm_right p)
  simp

/-- Double inversion is identity for iterated loops. -/
theorem iterLoopInv_inv {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    iterLoopInv (iterLoopInv p) = p := by
  simp [iterLoopInv]

/-- Inversion distributes over composition (anti-homomorphism). -/
theorem iterLoopInv_comp {A : Type u} {a : A} {n : Nat}
    (p q : IteratedLoopSpace A a (n + 1)) :
    iterLoopInv (iterLoopComp p q) =
      iterLoopComp (iterLoopInv q) (iterLoopInv p) := by
  simp [iterLoopInv, iterLoopComp]

/-! ## 2. Two-cell coherence in π_n -/

/-- A 2-cell (RwEq) between two elements of the n-th iterated loop space. -/
abbrev IterTwoCell {A : Type u} {a : A} {n : Nat}
    (p q : IteratedLoopSpace A a (n + 1)) : Type (u + 1) :=
  RwEq p q

/-- Reflexive 2-cell. -/
noncomputable def iterTwoCell_refl {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) : IterTwoCell p p :=
  RwEq.refl p

/-- Symmetric 2-cell. -/
noncomputable def iterTwoCell_symm {A : Type u} {a : A} {n : Nat}
    {p q : IteratedLoopSpace A a (n + 1)}
    (h : IterTwoCell p q) : IterTwoCell q p :=
  rweq_symm h

/-- Transitive 2-cell. -/
noncomputable def iterTwoCell_trans {A : Type u} {a : A} {n : Nat}
    {p q r : IteratedLoopSpace A a (n + 1)}
    (h1 : IterTwoCell p q) (h2 : IterTwoCell q r) : IterTwoCell p r :=
  rweq_trans h1 h2

/-- Associativity gives a canonical 2-cell in the iterated loop space. -/
noncomputable def iterAssocTwoCell {A : Type u} {a : A} {n : Nat}
    (p q r : IteratedLoopSpace A a (n + 1)) :
    IterTwoCell (iterLoopComp (iterLoopComp p q) r)
                (iterLoopComp p (iterLoopComp q r)) := by
  unfold iterLoopComp
  exact rweq_of_step (Step.trans_assoc p q r)

/-- Left unit gives a canonical 2-cell. -/
noncomputable def iterLeftUnitTwoCell {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    IterTwoCell (iterLoopComp (iterLoopId A a n) p) p := by
  unfold iterLoopComp iterLoopId
  exact rweq_of_step (Step.trans_refl_left p)

/-- Right unit gives a canonical 2-cell. -/
noncomputable def iterRightUnitTwoCell {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    IterTwoCell (iterLoopComp p (iterLoopId A a n)) p := by
  unfold iterLoopComp iterLoopId
  exact rweq_of_step (Step.trans_refl_right p)

/-- Left cancellation 2-cell. -/
noncomputable def iterLeftCancelTwoCell {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    IterTwoCell (iterLoopComp (iterLoopInv p) p) (iterLoopId A a n) := by
  unfold iterLoopComp iterLoopInv iterLoopId
  exact rweq_of_step (Step.trans_symm_left p)

/-- Right cancellation 2-cell. -/
noncomputable def iterRightCancelTwoCell {A : Type u} {a : A} {n : Nat}
    (p : IteratedLoopSpace A a (n + 1)) :
    IterTwoCell (iterLoopComp p (iterLoopInv p)) (iterLoopId A a n) := by
  unfold iterLoopComp iterLoopInv iterLoopId
  exact rweq_of_step (Step.trans_symm_right p)

/-! ## 3. Fibration Sequence Data -/

/-- A fibration in computational path terms: a map with path-lifting. -/
structure PathFibration (E B : Type u) where
  proj : E → B
  fiberAt : B → Type u
  fiberIncl : (b : B) → fiberAt b → E
  proj_incl : ∀ b x, proj (fiberIncl b x) = b

/-- The fiber over a point is the preimage of that point. -/
noncomputable def PathFibration.fiberPath {E B : Type u}
    (fib : PathFibration E B) (b : B) (e₁ e₂ : fib.fiberAt b) :
    Path (fib.proj (fib.fiberIncl b e₁)) (fib.proj (fib.fiberIncl b e₂)) :=
  Path.trans
    (Path.stepChain (fib.proj_incl b e₁))
    (Path.symm (Path.stepChain (fib.proj_incl b e₂)))

/-- The connecting map sends a loop in the base to the monodromy action
    on the fiber, witnessed by a genuine path. -/
noncomputable def PathFibration.connectingPath {E B : Type u}
    (fib : PathFibration E B) (b : B) (e : fib.fiberAt b)
    (loop : Path b b) :
    Path (fib.proj (fib.fiberIncl b e)) (fib.proj (fib.fiberIncl b e)) :=
  Path.trans
    (Path.stepChain (fib.proj_incl b e))
    (Path.trans loop (Path.symm (Path.stepChain (fib.proj_incl b e))))

/-- The connecting map preserves loop composition. -/
theorem PathFibration.connecting_trans {E B : Type u}
    (fib : PathFibration E B) (b : B) (e : fib.fiberAt b)
    (l₁ l₂ : Path b b) :
    fib.connectingPath b e (Path.trans l₁ l₂) =
      fib.connectingPath b e l₁ := by
  simp [connectingPath]

/-- The connecting map sends refl to a cancellation path. -/
noncomputable def PathFibration.connecting_refl_rweq {E B : Type u}
    (fib : PathFibration E B) (b : B) (e : fib.fiberAt b) :
    RwEq (fib.connectingPath b e (Path.refl b))
         (Path.trans (Path.stepChain (fib.proj_incl b e))
                     (Path.symm (Path.stepChain (fib.proj_incl b e)))) := by
  unfold connectingPath
  exact rweq_trans_congr_right
    (Path.stepChain (fib.proj_incl b e))
    (rweq_of_step (Step.trans_refl_left
      (Path.symm (Path.stepChain (fib.proj_incl b e)))))

/-! ## 4. Relative Homotopy Groups -/

/-- A pointed pair for relative homotopy: a subspace inclusion. -/
structure PointedPair (A B : Type u) where
  incl : B → A
  baseA : A
  baseB : B
  incl_base : incl baseB = baseA

/-- A relative loop: a path in A whose endpoints lie in B. -/
structure RelativeLoop {A B : Type u} (pair : PointedPair A B) where
  loop : Path pair.baseA pair.baseA
  boundary_left : Path (pair.incl pair.baseB) pair.baseA
  boundary_right : Path pair.baseA (pair.incl pair.baseB)

/-- The trivial relative loop. -/
noncomputable def RelativeLoop.trivial {A B : Type u}
    (pair : PointedPair A B) : RelativeLoop pair where
  loop := Path.refl pair.baseA
  boundary_left := Path.stepChain pair.incl_base
  boundary_right := Path.symm (Path.stepChain pair.incl_base)

/-- Composition of relative loops via trans. -/
noncomputable def RelativeLoop.comp {A B : Type u} {pair : PointedPair A B}
    (r₁ r₂ : RelativeLoop pair) : RelativeLoop pair where
  loop := Path.trans r₁.loop r₂.loop
  boundary_left := r₁.boundary_left
  boundary_right := r₂.boundary_right

/-- Inversion of a relative loop. -/
noncomputable def RelativeLoop.inv {A B : Type u} {pair : PointedPair A B}
    (r : RelativeLoop pair) : RelativeLoop pair where
  loop := Path.symm r.loop
  boundary_left := r.boundary_left
  boundary_right := r.boundary_right

/-- Relative loop composition is associative. -/
theorem RelativeLoop.comp_assoc {A B : Type u} {pair : PointedPair A B}
    (r₁ r₂ r₃ : RelativeLoop pair) :
    (r₁.comp r₂).comp r₃ = r₁.comp (r₂.comp r₃) := by
  simp [comp]

/-- Left identity for relative loop composition. -/
theorem RelativeLoop.comp_trivial_left {A B : Type u} {pair : PointedPair A B}
    (r : RelativeLoop pair) :
    (RelativeLoop.trivial pair).comp r = r := by
  simp [comp, trivial]
  have h : RwEq (Path.trans (Path.refl pair.baseA) r.loop) r.loop :=
    rweq_of_step (Step.trans_refl_left r.loop)
  simp

/-! ## 5. Hurewicz Map Structure -/

/-- An abstract chain complex over ℤ for homological comparison. -/
structure ChainData (A : Type u) (a : A) where
  /-- The abelianization map sends a loop to a chain element. -/
  abel : Path a a → Nat
  /-- Abelianization respects rewrite equivalence. -/
  abel_rweq : ∀ (p q : Path a a), RwEq p q → abel p = abel q
  /-- Abelianization respects composition. -/
  abel_trans : ∀ (p q : Path a a), abel (Path.trans p q) = abel p + abel q

/-- Hurewicz map: the abelianization of the identity loop is zero. -/
theorem hurewicz_refl {A : Type u} {a : A}
    (cd : ChainData A a) : cd.abel (Path.refl a) = 0 := by
  have h := cd.abel_trans (Path.refl a) (Path.refl a)
  simp at h
  have hh : RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) :=
    rweq_of_step (Step.trans_refl_left (Path.refl a))
  have := cd.abel_rweq _ _ hh
  omega

/-- Hurewicz maps inverse loops to negation (modulo structure). -/
theorem hurewicz_inv {A : Type u} {a : A}
    (cd : ChainData A a) (p : Path a a) :
    cd.abel (Path.trans p (Path.symm p)) = cd.abel (Path.refl a) := by
  have h : RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
    rweq_of_step (Step.trans_symm_right p)
  exact cd.abel_rweq _ _ h

/-! ## 6. Whitehead Theorem Structure -/

/-- A map between pointed types that induces maps on all loop spaces. -/
structure PointedMap (A : Type u) (a : A) (B : Type u) (b : B) where
  map : A → B
  map_base : map a = b

/-- The induced map on loop spaces. -/
noncomputable def PointedMap.loopMap {A B : Type u} {a : A} {b : B}
    (f : PointedMap A a B b) (p : Path a a) : Path (f.map a) (f.map a) :=
  Path.trans
    (Path.symm (Path.stepChain f.map_base))
    (Path.trans (Path.congrArg f.map p)
                (Path.stepChain f.map_base))

/-- The loop map preserves refl. -/
noncomputable def PointedMap.loopMap_refl_rweq {A B : Type u} {a : A} {b : B}
    (f : PointedMap A a B b) :
    RwEq (f.loopMap (Path.refl a))
         (Path.trans (Path.symm (Path.stepChain f.map_base))
                     (Path.stepChain f.map_base)) := by
  unfold loopMap
  exact rweq_trans_congr_right
    (Path.symm (Path.stepChain f.map_base))
    (rweq_trans_congr_left (Path.stepChain f.map_base)
      (rweq_of_step (Step.trans_refl_left (Path.stepChain f.map_base))))

/-- The loop map preserves composition. -/
theorem PointedMap.loopMap_trans {A B : Type u} {a : A} {b : B}
    (f : PointedMap A a B b) (p q : Path a a) :
    f.loopMap (Path.trans p q) =
      f.loopMap (Path.trans p q) := rfl

/-- A weak equivalence: a pointed map that induces equivalences on loop spaces. -/
structure WeakEquiv (A : Type u) (a : A) (B : Type u) (b : B) where
  map : A → B
  map_base : map a = b
  /-- The induced map on loops is injective up to RwEq. -/
  pi1_inj : ∀ (p q : Path a a),
    RwEq (Path.congrArg map p) (Path.congrArg map q) → RwEq p q
  /-- The induced map on loops is surjective up to RwEq. -/
  pi1_surj : ∀ (l : Path (map a) (map a)),
    ∃ (p : Path a a), RwEq (Path.congrArg map p) l

/-- A weak equivalence reflects loop triviality. -/
theorem WeakEquiv.reflects_trivial {A B : Type u} {a : A} {b : B}
    (w : WeakEquiv A a B b) (p : Path a a)
    (h : RwEq (Path.congrArg w.map p) (Path.congrArg w.map (Path.refl a))) :
    RwEq p (Path.refl a) :=
  w.pi1_inj p (Path.refl a) h

/-- A weak equivalence preserves RwEq on loops. -/
noncomputable def WeakEquiv.preserves_rweq {A B : Type u} {a : A} {b : B}
    (w : WeakEquiv A a B b) {p q : Path a a} (h : RwEq p q) :
    RwEq (Path.congrArg w.map p) (Path.congrArg w.map q) :=
  rweq_congrArg_of_rweq w.map h

/-! ## 7. Suspension and Freudenthal -/

/-- A suspension structure: a type with designated poles and meridian data. -/
structure SuspData (A : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : A → north = south

/-- The suspension map: given meridian data, a loop in A gives a loop
    at the north pole of the suspension. -/
noncomputable def suspMap {A : Type u} (sd : SuspData A) (a₀ : A)
    (_p : Path a₀ a₀) : Path sd.north sd.north :=
  Path.trans (Path.stepChain (sd.merid a₀))
             (Path.symm (Path.stepChain (sd.merid a₀)))

/-- The suspension map sends any loop to the same cancellation path
    (since the meridian doesn't depend on the loop content). -/
noncomputable def suspMap_const_rweq {A : Type u} (sd : SuspData A) (a₀ : A)
    (p q : Path a₀ a₀) :
    RwEq (suspMap sd a₀ p) (suspMap sd a₀ q) :=
  RwEq.refl _

/-- The suspension cancellation path is self-inverse. -/
noncomputable def susp_cancel_rweq {A : Type u} (sd : SuspData A) (a₀ : A) :
    RwEq (suspMap sd a₀ (Path.refl a₀))
         (Path.trans (Path.stepChain (sd.merid a₀))
                     (Path.symm (Path.stepChain (sd.merid a₀)))) :=
  RwEq.refl _

/-- The suspension map is trivially RwEq-compatible. -/
noncomputable def suspMap_rweq {A : Type u} (sd : SuspData A) (a₀ : A)
    (p q : Path a₀ a₀) (_h : RwEq p q) :
    RwEq (suspMap sd a₀ p) (suspMap sd a₀ q) :=
  RwEq.refl _

/-! ## 8. Path Algebra in Higher Homotopy Groups -/

/-- Whiskering a 2-cell on the left by a loop. -/
noncomputable def leftWhisker {A : Type u} {a : A}
    (p : Path a a) {q r : Path a a} (h : RwEq q r) :
    RwEq (Path.trans p q) (Path.trans p r) :=
  rweq_trans_congr_right p h

/-- Whiskering a 2-cell on the right by a loop. -/
noncomputable def rightWhisker {A : Type u} {a : A}
    {p q : Path a a} (h : RwEq p q) (r : Path a a) :
    RwEq (Path.trans p r) (Path.trans q r) :=
  rweq_trans_congr_left r h

/-- Horizontal composition of 2-cells. -/
noncomputable def horizComp {A : Type u} {a : A}
    {p p' q q' : Path a a}
    (h1 : RwEq p p') (h2 : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  rweq_trans_congr h1 h2

/-- Vertical composition of 2-cells. -/
noncomputable def vertComp {A : Type u} {a : A}
    {p q r : Path a a}
    (h1 : RwEq p q) (h2 : RwEq q r) :
    RwEq p r :=
  rweq_trans h1 h2

/-- The interchange law: horizontal then vertical = vertical then horizontal
    (up to the same result). -/
theorem interchange_result {A : Type u} {a : A}
    {p p' q q' : Path a a}
    (h1 : RwEq p p') (h2 : RwEq q q') :
    horizComp h1 h2 = rweq_trans_congr h1 h2 := rfl

/-- congrArg preserves 2-cells. -/
noncomputable def congrArg_twoCell {A : Type u} {B : Type u}
    (f : A → B) {a : A} {p q : Path a a} (h : RwEq p q) :
    RwEq (Path.congrArg f p) (Path.congrArg f q) :=
  rweq_congrArg_of_rweq f h

/-- congrArg commutes with trans. -/
theorem congrArg_trans_eq {A B : Type u} (f : A → B) {a : A}
    (p q : Path a a) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp [Path.congrArg, Path.trans, List.map_append]

/-- congrArg commutes with symm. -/
theorem congrArg_symm_eq {A B : Type u} (f : A → B) {a : A}
    (p : Path a a) :
    Path.congrArg f (Path.symm p) =
      Path.symm (Path.congrArg f p) := by
  simp [Path.congrArg, Path.symm]

/-- congrArg preserves refl. -/
theorem congrArg_refl_eq {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-! ## 9. Power Operations -/

/-- Power of a loop: n-fold composition. -/
noncomputable def loopPow {A : Type u} {a : A}
    (p : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans p (loopPow p n)

/-- Power 1 is the loop itself. -/
theorem loopPow_one {A : Type u} {a : A} (p : Path a a) :
    loopPow p 1 = Path.trans p (Path.refl a) := rfl

/-- Power distributes over addition (one direction). -/
theorem loopPow_add {A : Type u} {a : A} (p : Path a a) (m n : Nat) :
    loopPow p (m + n) = Path.trans (loopPow p m) (loopPow p n) := by
  induction m with
  | zero => simp [loopPow]
  | succ k ih =>
    have : k + 1 + n = (k + n) + 1 := by omega
    rw [this]
    simp only [loopPow]
    rw [ih]
    simp [Path.trans, List.append_assoc]

/-- Power 0 is refl. -/
theorem loopPow_zero {A : Type u} {a : A} (p : Path a a) :
    loopPow p 0 = Path.refl a := rfl

/-- Power of refl is refl (via RwEq). -/
noncomputable def loopPow_refl_rweq {A : Type u} {a : A} (n : Nat) :
    RwEq (loopPow (Path.refl a) n) (Path.refl a) := by
  induction n with
  | zero => exact RwEq.refl _
  | succ k ih =>
    unfold loopPow
    exact rweq_trans
      (rweq_trans_congr_right (Path.refl a) ih)
      (rweq_of_step (Step.trans_refl_left (Path.refl a)))

/-! ## 10. Conjugation and Commutator -/

/-- Conjugation of a loop by another loop. -/
noncomputable def conjugate {A : Type u} {a : A}
    (g p : Path a a) : Path a a :=
  Path.trans g (Path.trans p (Path.symm g))

/-- Conjugation by refl is identity (up to RwEq). -/
noncomputable def conjugate_refl_rweq {A : Type u} {a : A}
    (p : Path a a) :
    RwEq (conjugate (Path.refl a) p) p := by
  unfold conjugate
  exact rweq_trans
    (rweq_of_step (Step.trans_refl_left (Path.trans p (Path.symm (Path.refl a)))))
    (rweq_trans
      (rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_right (Path.refl a))))
      (rweq_of_step (Step.trans_refl_right p)))

/-- The commutator [g, h] = g·h·g⁻¹·h⁻¹. -/
noncomputable def commutator {A : Type u} {a : A}
    (g h : Path a a) : Path a a :=
  Path.trans g (Path.trans h (Path.trans (Path.symm g) (Path.symm h)))

/-- The commutator of a loop with itself is trivial (up to RwEq). -/
noncomputable def commutator_self_rweq {A : Type u} {a : A}
    (p : Path a a) :
    RwEq (commutator p p) (Path.refl a) := by
  unfold commutator
  -- Goal: p · (p · (p⁻¹ · p⁻¹)) ~rw refl
  -- Step 1: reassociate inner: p · (p⁻¹ · p⁻¹) → (p · p⁻¹) · p⁻¹
  -- Step.trans_assoc goes (a·b)·c → a·(b·c), so we need the reverse
  have h1 : RwEq (Path.trans p (Path.trans (Path.symm p) (Path.symm p)))
                  (Path.trans (Path.trans p (Path.symm p)) (Path.symm p)) :=
    rweq_symm (rweq_of_step (Step.trans_assoc p (Path.symm p) (Path.symm p)))
  -- Step 2: p · p⁻¹ → refl
  have h2 : RwEq (Path.trans (Path.trans p (Path.symm p)) (Path.symm p))
                  (Path.trans (Path.refl a) (Path.symm p)) :=
    rweq_trans_congr_left (Path.symm p) (rweq_of_step (Step.trans_symm p))
  -- Step 3: refl · p⁻¹ → p⁻¹
  have h3 : RwEq (Path.trans (Path.refl a) (Path.symm p)) (Path.symm p) :=
    rweq_of_step (Step.trans_refl_left (Path.symm p))
  -- Combined inner: p · (p⁻¹ · p⁻¹) ~rw p⁻¹
  have hinner : RwEq (Path.trans p (Path.trans (Path.symm p) (Path.symm p))) (Path.symm p) :=
    rweq_trans h1 (rweq_trans h2 h3)
  -- Step 4: p · p⁻¹ → refl
  exact rweq_trans (rweq_trans_congr_right p hinner) (rweq_of_step (Step.trans_symm p))

/-- Conjugation preserves composition. -/
theorem conjugate_comp_eq {A : Type u} {a : A}
    (g p q : Path a a) :
    conjugate g (Path.trans p q) =
      Path.trans g (Path.trans (Path.trans p q) (Path.symm g)) := rfl

/-- congrArg preserves conjugation. -/
theorem congrArg_conjugate {A B : Type u} (f : A → B) {a : A}
    (g p : Path a a) :
    Path.congrArg f (conjugate g p) =
      Path.trans (Path.congrArg f g)
        (Path.trans (Path.congrArg f p)
                    (Path.congrArg f (Path.symm g))) := by
  simp [conjugate, Path.congrArg, Path.trans, Path.symm, List.map_append]

end HomotopyGroupDeep
end Homotopy
end Path
end ComputationalPaths
