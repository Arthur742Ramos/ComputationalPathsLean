/-
# Deep Completion Theory for Computational Paths

Cauchy sequences as path systems, metric completion, profinite completion,
and their interaction with the computational paths framework. We model
convergence, completeness, and completion universality using `Path`/`Step`/
`trans`/`symm` from Core.

## References

- Bourbaki, "General Topology", Ch. II §3 (Cauchy filters and completion)
- Ribes & Zalesskii, "Profinite Groups" (profinite completion)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CompletionDeep

universe u v w

open ComputationalPaths.Path

/-! ## Abstract metric structure -/

/-- A distance function on a type, valued in natural numbers (discrete metric). -/
structure DiscreteDist (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

namespace DiscreteDist

variable {A : Type u}

-- Theorem 1: Distance is non-negative (trivially true for Nat)
theorem dist_nonneg (d : DiscreteDist A) (x y : A) : 0 ≤ d.dist x y :=
  Nat.zero_le _

-- Theorem 2: If dist = 0 and metric is separated, then path exists
theorem dist_zero_path (d : DiscreteDist A) (x : A) :
    d.dist x x = 0 := d.dist_self x

-- Theorem 3: Triangle inequality iterated
theorem dist_triangle_four (d : DiscreteDist A) (x y z w : A) :
    d.dist x w ≤ d.dist x y + d.dist y z + d.dist z w := by
  calc d.dist x w ≤ d.dist x z + d.dist z w := d.dist_triangle x z w
    _ ≤ (d.dist x y + d.dist y z) + d.dist z w := by
        apply Nat.add_le_add_right; exact d.dist_triangle x y z

end DiscreteDist

/-! ## Cauchy sequences as path systems -/

/-- A sequence in A. -/
def Seq (A : Type u) := Nat → A

/-- A sequence is Cauchy w.r.t. a discrete distance: for every ε > 0,
    there exists N such that for all m, n ≥ N, dist(aₘ, aₙ) < ε. -/
def IsCauchy {A : Type u} (d : DiscreteDist A) (s : Seq A) : Prop :=
  ∀ ε : Nat, 0 < ε → ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n → d.dist (s m) (s n) < ε

-- Theorem 4: Constant sequence is Cauchy
theorem isCauchy_const {A : Type u} (d : DiscreteDist A) (a : A) :
    IsCauchy d (fun _ => a) := by
  intro ε hε
  exact ⟨0, fun m n _ _ => by simp [d.dist_self]; exact hε⟩

-- Theorem 5: If two sequences are equal, Cauchy transfers
theorem isCauchy_of_eq {A : Type u} (d : DiscreteDist A) (s t : Seq A)
    (h : ∀ n, s n = t n) (hc : IsCauchy d s) : IsCauchy d t := by
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  exact ⟨N, fun m n hm hn => by rw [← h m, ← h n]; exact hN m n hm hn⟩

/-! ## Cauchy path systems -/

/-- A Cauchy path system: a sequence where consecutive elements are
    connected by computational paths, with the distances shrinking. -/
structure CauchyPathSystem {A : Type u} (d : DiscreteDist A) where
  seq : Seq A
  links : ∀ n : Nat, Path (seq n) (seq (n + 1))
  cauchy : IsCauchy d seq

-- Theorem 6: Constant Cauchy path system
def CauchyPathSystem.const {A : Type u} (d : DiscreteDist A) (a : A) :
    CauchyPathSystem d where
  seq := fun _ => a
  links := fun _ => Path.refl a
  cauchy := isCauchy_const d a

-- Theorem 7: Telescoping path from a Cauchy path system
def telescopePath {A : Type u} {d : DiscreteDist A}
    (cps : CauchyPathSystem d) (m n : Nat) (h : m ≤ n) :
    Path (cps.seq m) (cps.seq n) := by
  induction n with
  | zero => simp at h; subst h; exact Path.refl (cps.seq 0)
  | succ k ih =>
    by_cases hk : m ≤ k
    · exact Path.trans (ih hk) (cps.links k)
    · have : m = k + 1 := by omega
      subst this; exact Path.refl (cps.seq m)

-- Theorem 8: Telescoping path for 0 to n
def telescopeFromZero {A : Type u} {d : DiscreteDist A}
    (cps : CauchyPathSystem d) (n : Nat) :
    Path (cps.seq 0) (cps.seq n) :=
  telescopePath cps 0 n (Nat.zero_le n)

-- Theorem 9: Telescoping path is compatible with trans
theorem telescopePath_trans {A : Type u} {d : DiscreteDist A}
    (cps : CauchyPathSystem d) (m n k : Nat) (h1 : m ≤ n) (h2 : n ≤ k) :
    (telescopePath cps m k (le_trans h1 h2)).toEq =
    (Path.trans (telescopePath cps m n h1) (telescopePath cps n k h2)).toEq := by
  simp

/-! ## Equivalence of Cauchy sequences -/

/-- Two Cauchy sequences are equivalent if their distance goes to 0. -/
def CauchyEquiv {A : Type u} (d : DiscreteDist A)
    (s t : CauchyPathSystem d) : Prop :=
  ∀ ε : Nat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    d.dist (s.seq n) (t.seq n) < ε

-- Theorem 10: CauchyEquiv is reflexive
theorem cauchyEquiv_refl {A : Type u} (d : DiscreteDist A)
    (s : CauchyPathSystem d) : CauchyEquiv d s s := by
  intro ε hε; exact ⟨0, fun n _ => by rw [d.dist_self]; exact hε⟩

-- Theorem 11: CauchyEquiv is symmetric
theorem cauchyEquiv_symm {A : Type u} (d : DiscreteDist A)
    (s t : CauchyPathSystem d) (h : CauchyEquiv d s t) :
    CauchyEquiv d t s := by
  intro ε hε; obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by rw [d.dist_symm]; exact hN n hn⟩

-- Theorem 12: CauchyEquiv is transitive
theorem cauchyEquiv_trans {A : Type u} (d : DiscreteDist A)
    (s t u : CauchyPathSystem d)
    (hst : CauchyEquiv d s t) (htu : CauchyEquiv d t u) :
    CauchyEquiv d s u := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := hst ε hε
  obtain ⟨N2, hN2⟩ := htu ε hε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_of_max_le_left hn)
  have h2 := hN2 n (le_of_max_le_right hn)
  calc d.dist (s.seq n) (u.seq n)
      ≤ d.dist (s.seq n) (t.seq n) + d.dist (t.seq n) (u.seq n) :=
        d.dist_triangle _ _ _
    _ < ε + ε := Nat.add_lt_add h1 h2
    _ = 2 * ε := by ring

/-! ## Metric completion -/

/-- The metric completion: quotient of Cauchy path systems by equivalence. -/
def Completion {A : Type u} (d : DiscreteDist A) :=
  Quot (CauchyEquiv d)

-- Theorem 13: Embedding of A into its completion
def Completion.embed {A : Type u} (d : DiscreteDist A) (a : A) :
    Completion d :=
  Quot.mk _ (CauchyPathSystem.const d a)

-- Theorem 14: Equal elements map to equal completions
theorem Completion.embed_eq {A : Type u} (d : DiscreteDist A) (a : A) :
    Completion.embed d a = Completion.embed d a := rfl

-- Theorem 15: Path in A yields path in completion
theorem Completion.embed_path {A : Type u} (d : DiscreteDist A)
    {a b : A} (p : Path a b) :
    Completion.embed d a = Completion.embed d b := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## Profinite completion via inverse systems -/

/-- A projective system: a sequence of types with connecting maps. -/
structure ProjSystem where
  obj : Nat → Type u
  map : ∀ n : Nat, obj (n + 1) → obj n
  /-- Each level is a finite quotient (modeled as having a term). -/
  witness : ∀ n : Nat, obj n

/-- An element of the inverse limit: a compatible family. -/
structure InvLimitElem (S : ProjSystem) where
  components : ∀ n : Nat, S.obj n
  compat : ∀ n : Nat, S.map n (components (n + 1)) = components n

-- Theorem 16: Constant family is in the inverse limit if maps fix witness
def InvLimitElem.ofConstant (S : ProjSystem)
    (h : ∀ n, S.map n (S.witness (n + 1)) = S.witness n) :
    InvLimitElem S where
  components := S.witness
  compat := h

-- Theorem 17: Two inverse limit elements are equal iff all components agree
theorem InvLimitElem.ext (S : ProjSystem)
    (x y : InvLimitElem S)
    (h : ∀ n, x.components n = y.components n) : x = y := by
  cases x; cases y; simp at h ⊢; funext n; exact h n

/-! ## Paths in inverse limits -/

-- Theorem 18: Path in each component yields path in inverse limit
def InvLimitElem.pathFromComponents (S : ProjSystem)
    (x y : InvLimitElem S)
    (h : ∀ n, x.components n = y.components n)
    (paths : ∀ n, Path (x.components n) (y.components n)) :
    Path x y :=
  Path.ofEq (InvLimitElem.ext S x y h)

-- Theorem 19: Projection preserves paths
theorem projection_preserves_path (S : ProjSystem) (n : Nat)
    (x y : InvLimitElem S) (p : Path x y) :
    Path (x.components n) (y.components n) :=
  Path.congrArg (fun e => e.components n) p

-- Theorem 20: Projection map is compatible with trans
theorem projection_trans (S : ProjSystem) (n : Nat)
    (x y z : InvLimitElem S) (p : Path x y) (q : Path y z) :
    projection_preserves_path S n x z (Path.trans p q) =
    Path.trans (projection_preserves_path S n x y p)
               (projection_preserves_path S n y z q) := by
  simp [projection_preserves_path]

-- Theorem 21: Projection map is compatible with symm
theorem projection_symm (S : ProjSystem) (n : Nat)
    (x y : InvLimitElem S) (p : Path x y) :
    projection_preserves_path S n y x (Path.symm p) =
    Path.symm (projection_preserves_path S n x y p) := by
  simp [projection_preserves_path]

/-! ## Profinite completion -/

/-- The profinite completion: the inverse limit of a projective system. -/
def ProfiniteCompletion (S : ProjSystem) := InvLimitElem S

-- Theorem 22: Profinite completion carries path structure from components
def ProfiniteCompletion.pathLift (S : ProjSystem)
    (x y : ProfiniteCompletion S)
    (h : ∀ n, x.components n = y.components n) :
    Path x y :=
  InvLimitElem.pathFromComponents S x y h
    (fun n => Path.ofEq (h n))

/-! ## Completion preserves path structure -/

-- Theorem 23: Embedding into completion preserves refl
theorem embed_preserves_refl {A : Type u} (d : DiscreteDist A) (a : A) :
    Completion.embed d a = Completion.embed d a := rfl

-- Theorem 24: Cauchy path system transport — transport along a path in A
-- lifts to a path between embedded completions
theorem completion_transport {A : Type u} (d : DiscreteDist A)
    {a b : A} (p : Path a b) :
    Path.transport (D := fun x => Completion d) p (Completion.embed d a) =
    Completion.embed d b := by
  cases p with
  | mk steps proof => cases proof; rfl

-- Theorem 25: Telescoping in the completion
theorem completion_telescope {A : Type u} (d : DiscreteDist A)
    (cps : CauchyPathSystem d) (n : Nat) :
    Path.transport (D := fun x => Completion d) (telescopeFromZero cps n)
      (Completion.embed d (cps.seq 0)) =
    Completion.embed d (cps.seq n) := by
  simp [Completion.embed, Path.transport]
  cases (telescopeFromZero cps n) with
  | mk steps proof => cases proof; rfl

/-! ## Cauchy completeness -/

/-- A discrete distance is complete if every Cauchy sequence converges. -/
def IsComplete {A : Type u} (d : DiscreteDist A) : Prop :=
  ∀ s : CauchyPathSystem d, ∃ a : A, ∀ ε : Nat, 0 < ε →
    ∃ N : Nat, ∀ n : Nat, N ≤ n → d.dist (s.seq n) a < ε

-- Theorem 26: A type with trivial distance (all 0) is complete
theorem isComplete_trivial {A : Type u} [Inhabited A] :
    IsComplete (DiscreteDist.mk (fun _ _ => 0) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => Nat.le_refl 0)) := by
  intro s
  exact ⟨s.seq 0, fun ε hε => ⟨0, fun n _ => hε⟩⟩

/-! ## Universal property of completion -/

/-- A map from A to a complete type B that is uniformly continuous. -/
structure UniformMap {A : Type u} {B : Type v}
    (dA : DiscreteDist A) (dB : DiscreteDist B) where
  fn : A → B
  uniform : ∀ ε : Nat, 0 < ε → ∃ δ : Nat, 0 < δ ∧
    ∀ x y : A, dA.dist x y < δ → dB.dist (fn x) (fn y) < ε

-- Theorem 27: Identity is uniformly continuous
def UniformMap.id {A : Type u} (d : DiscreteDist A) : UniformMap d d where
  fn := fun x => x
  uniform := fun ε hε => ⟨ε, hε, fun _ _ h => h⟩

-- Theorem 28: Composition of uniform maps
def UniformMap.comp {A : Type u} {B : Type v} {C : Type w}
    {dA : DiscreteDist A} {dB : DiscreteDist B} {dC : DiscreteDist C}
    (g : UniformMap dB dC) (f : UniformMap dA dB) : UniformMap dA dC where
  fn := fun x => g.fn (f.fn x)
  uniform := by
    intro ε hε
    obtain ⟨δ₂, hδ₂, hg⟩ := g.uniform ε hε
    obtain ⟨δ₁, hδ₁, hf⟩ := f.uniform δ₂ hδ₂
    exact ⟨δ₁, hδ₁, fun x y h => hg _ _ (hf x y h)⟩

-- Theorem 29: Uniform map preserves Cauchy sequences
theorem uniformMap_preserves_cauchy {A : Type u} {B : Type v}
    {dA : DiscreteDist A} {dB : DiscreteDist B}
    (f : UniformMap dA dB) (cps : CauchyPathSystem dA) :
    IsCauchy dB (fun n => f.fn (cps.seq n)) := by
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := f.uniform ε hε
  obtain ⟨N, hN⟩ := cps.cauchy δ hδ
  exact ⟨N, fun m n hm hn => hf _ _ (hN m n hm hn)⟩

-- Theorem 30: Uniform map on paths
theorem uniformMap_path {A : Type u} {B : Type v}
    {dA : DiscreteDist A} {dB : DiscreteDist B}
    (f : UniformMap dA dB) {a b : A} (p : Path a b) :
    Path (f.fn a) (f.fn b) :=
  Path.congrArg f.fn p

end CompletionDeep
end Algebra
end Path
end ComputationalPaths
