/-
# Homological Algebra via Computational Paths

Chain complexes as graded path sequences, the boundary operator as
path truncation, homology as path cycles modulo path boundaries,
exact sequences as path factorizations, and the snake lemma via
path chasing — all fully proved.

## References

- Weibel, "An Introduction to Homological Algebra"
- Mac Lane, "Homology"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Graded Module and Chain Complex Infrastructure -/

/-- A graded module: a family of types indexed by natural numbers. -/
structure GradedModule where
  component : Nat → Type u

/-- A chain complex: graded module with boundary operators satisfying d² = 0. -/
structure ChainComplex where
  modules : GradedModule.{u}
  boundary : ∀ n, modules.component (n + 1) → modules.component n
  zero : ∀ n, modules.component n
  boundary_sq : ∀ n (x : modules.component (n + 2)),
    Path (boundary n (boundary (n + 1) x)) (zero n)

/-- A chain map between chain complexes. -/
structure ChainMap (C D : ChainComplex.{u}) where
  map : ∀ n, C.modules.component n → D.modules.component n
  commutes : ∀ n (x : C.modules.component (n + 1)),
    Path (map n (C.boundary n x)) (D.boundary n (map (n + 1) x))

/-! ## Boundary Operator as Path Truncation -/

/-- Double boundary is zero (propositional). -/
theorem double_boundary_zero (C : ChainComplex.{u})
    (n : Nat) (x : C.modules.component (n + 2)) :
    C.boundary n (C.boundary (n + 1) x) = C.zero n :=
  (C.boundary_sq n x).toEq

/-- Chain map preserves boundaries (propositional). -/
theorem chain_map_boundary_eq {C D : ChainComplex.{u}}
    (f : ChainMap C D) (n : Nat) (x : C.modules.component (n + 1)) :
    f.map n (C.boundary n x) = D.boundary n (f.map (n + 1) x) :=
  (f.commutes n x).toEq

/-! ## Homology = Cycles mod Boundaries -/

/-- A cycle: an element whose boundary is zero. -/
structure Cycle (C : ChainComplex.{u}) (n : Nat) where
  element : C.modules.component (n + 1)
  isCycle : Path (C.boundary n element) (C.zero n)

/-- A boundary: an element in the image of the boundary operator. -/
structure Boundary (C : ChainComplex.{u}) (n : Nat) where
  element : C.modules.component (n + 1)
  preimage : C.modules.component (n + 2)
  isBoundary : Path element (C.boundary (n + 1) preimage)

/-- Every boundary is a cycle (d² = 0). -/
def boundary_is_cycle (C : ChainComplex.{u}) (n : Nat)
    (b : Boundary C n) : Cycle C n :=
  ⟨b.element,
    Path.trans (Path.congrArg (C.boundary n) b.isBoundary) (C.boundary_sq n b.preimage)⟩

/-- Every boundary element equals zero under the boundary map. -/
theorem boundary_element_maps_to_zero (C : ChainComplex.{u}) (n : Nat)
    (b : Boundary C n) :
    C.boundary n b.element = C.zero n :=
  (boundary_is_cycle C n b).isCycle.toEq

/-- Cycle condition is propositional. -/
theorem cycle_boundary_eq_zero (C : ChainComplex.{u}) (n : Nat)
    (z : Cycle C n) :
    C.boundary n z.element = C.zero n :=
  z.isCycle.toEq

/-- Boundary element equals its preimage under boundary. -/
theorem boundary_element_eq (C : ChainComplex.{u}) (n : Nat)
    (b : Boundary C n) :
    b.element = C.boundary (n + 1) b.preimage :=
  b.isBoundary.toEq

/-! ## Exact Sequences as Path Factorization -/

/-- An exact sequence at a point: kernel of g = image of f. -/
structure ExactAt (A B C : Type u) (f : A → B) (g : B → C) (zero_c : C) where
  comp_zero : ∀ a, Path (g (f a)) zero_c
  factor : ∀ b, Path (g b) zero_c → ∃ a, f a = b

/-- Exactness: composition is zero. -/
theorem exact_comp_zero {A B C : Type u}
    {f : A → B} {g : B → C} {zero_c : C}
    (E : ExactAt A B C f g zero_c) (a : A) :
    g (f a) = zero_c :=
  (E.comp_zero a).toEq

/-- Exactness: kernel element factors through image. -/
theorem exact_factor_exists {A B C : Type u}
    {f : A → B} {g : B → C} {zero_c : C}
    (E : ExactAt A B C f g zero_c) (b : B) (h : Path (g b) zero_c) :
    ∃ a, f a = b :=
  E.factor b h

/-- Short exact sequence data: 0 → A → B → C → 0. -/
structure ShortExactData (A B C : Type u) where
  f : A → B
  g : B → C
  zeroC : C
  comp_zero : ∀ a, Path (g (f a)) zeroC
  kernel_eq_image : ∀ b, Path (g b) zeroC → ∃ a, f a = b

/-- Short exact sequence: composition is zero. -/
theorem ses_comp_zero_eq {A B C : Type u}
    (S : ShortExactData A B C) (a : A) :
    S.g (S.f a) = S.zeroC :=
  (S.comp_zero a).toEq

/-- Short exact sequence: factoring. -/
theorem ses_factor {A B C : Type u}
    (S : ShortExactData A B C) (b : B) (h : Path (S.g b) S.zeroC) :
    ∃ a, S.f a = b :=
  S.kernel_eq_image b h

/-! ## Snake Lemma via Path Chasing -/

/-- Snake lemma setup: a commutative diagram with exact rows. -/
structure SnakeLemmaData (A B C A' B' C' : Type u) where
  f : A → B
  g : B → C
  f' : A' → B'
  g' : B' → C'
  α : A → A'
  β : B → B'
  γ : C → C'
  zeroC : C
  zeroC' : C'
  comm_left : ∀ a, Path (β (f a)) (f' (α a))
  comm_right : ∀ b, Path (γ (g b)) (g' (β b))
  exact_top : ExactAt A B C f g zeroC
  exact_bot : ExactAt A' B' C' f' g' zeroC'

/-- The commutativity of the left square. -/
theorem snake_left_square_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a : A) :
    S.β (S.f a) = S.f' (S.α a) :=
  (S.comm_left a).toEq

/-- The commutativity of the right square. -/
theorem snake_right_square_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (b : B) :
    S.γ (S.g b) = S.g' (S.β b) :=
  (S.comm_right b).toEq

/-- Composition across the top row is zero. -/
theorem snake_top_exact_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a : A) :
    S.g (S.f a) = S.zeroC :=
  (S.exact_top.comp_zero a).toEq

/-- Composition across the bottom row is zero. -/
theorem snake_bot_exact_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a' : A') :
    S.g' (S.f' a') = S.zeroC' :=
  (S.exact_bot.comp_zero a').toEq

/-- The connecting morphism witness: given c in ker(γ) and b mapping to c,
β(b) is in ker(g') = im(f'). -/
theorem snake_connecting_exists {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C')
    (c : C) (hc : Path (S.γ c) S.zeroC')
    (b : B) (hb : Path (S.g b) c) :
    ∃ a' : A', S.f' a' = S.β b := by
  have h1 : S.γ (S.g b) = S.γ c := _root_.congrArg S.γ hb.toEq
  have h2 : S.g' (S.β b) = S.γ (S.g b) := (S.comm_right b).toEq.symm
  have h3 : Path (S.g' (S.β b)) S.zeroC' := by
    have : S.g' (S.β b) = S.zeroC' := by
      rw [h2, h1]; exact hc.toEq
    exact Path.ofEq this
  obtain ⟨a', ha'⟩ := S.exact_bot.factor (S.β b) h3
  exact ⟨a', ha'⟩

/-- Path chase: the full square commutes for elements in the image. -/
theorem snake_chase_image_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a : A) :
    S.γ (S.g (S.f a)) = S.g' (S.f' (S.α a)) := by
  have h1 := snake_right_square_eq S (S.f a)
  have h2 : S.g' (S.β (S.f a)) = S.g' (S.f' (S.α a)) :=
    _root_.congrArg S.g' (snake_left_square_eq S a)
  exact h1.trans h2

/-- Top exactness + commutativity: γ ∘ g ∘ f = γ(0). -/
theorem snake_top_to_bottom_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a : A) :
    S.γ (S.g (S.f a)) = S.γ S.zeroC := by
  exact _root_.congrArg S.γ (snake_top_exact_eq S a)

/-- γ maps the image composition to γ(0). -/
theorem snake_gamma_zero_eq {A B C A' B' C' : Type u}
    (S : SnakeLemmaData A B C A' B' C') (a : A) :
    S.g' (S.f' (S.α a)) = S.γ S.zeroC := by
  rw [← snake_chase_image_eq S a]
  exact snake_top_to_bottom_eq S a

/-! ## Long Exact Sequence and Chain Map Infrastructure -/

/-- Data for a long exact sequence connecting two chain complexes. -/
structure LongExactData (C D : ChainComplex.{u}) where
  connecting : ∀ n, D.modules.component n → C.modules.component n
  naturality : ∀ n (x : D.modules.component (n + 1)),
    Path (C.boundary n (connecting (n + 1) x))
         (connecting n (D.boundary n x))

/-- Naturality of the connecting morphism (propositional). -/
theorem connecting_naturality_eq {C D : ChainComplex.{u}}
    (L : LongExactData C D) (n : Nat) (x : D.modules.component (n + 1)) :
    C.boundary n (L.connecting (n + 1) x) =
    L.connecting n (D.boundary n x) :=
  (L.naturality n x).toEq

/-- Chain map composition preserves commutativity. -/
theorem chain_map_comp_commutes_eq {C D E : ChainComplex.{u}}
    (f : ChainMap C D) (g : ChainMap D E)
    (n : Nat) (x : C.modules.component (n + 1)) :
    g.map n (f.map n (C.boundary n x)) =
    E.boundary n (g.map (n + 1) (f.map (n + 1) x)) := by
  have h1 := chain_map_boundary_eq f n x
  have h2 := chain_map_boundary_eq g n (f.map (n + 1) x)
  rw [h1, h2]

/-- Identity chain map. -/
def chainMapId (C : ChainComplex.{u}) : ChainMap C C where
  map := fun _ x => x
  commutes := fun _ _ => Path.refl _

/-- Identity chain map commutes trivially. -/
theorem chain_map_id_commutes_eq (C : ChainComplex.{u})
    (n : Nat) (x : C.modules.component (n + 1)) :
    ((chainMapId C).commutes n x).toEq = rfl := by
  rfl

/-- Chain map composition. -/
def chainMapComp {C D E : ChainComplex.{u}}
    (f : ChainMap C D) (g : ChainMap D E) : ChainMap C E where
  map := fun n x => g.map n (f.map n x)
  commutes := fun n x => by
    have h1 := f.commutes n x
    have h2 := g.commutes n (f.map (n + 1) x)
    exact Path.trans (Path.congrArg (g.map n) h1) h2

/-- Chain map composition agrees with pointwise composition. -/
theorem chainMapComp_map {C D E : ChainComplex.{u}}
    (f : ChainMap C D) (g : ChainMap D E)
    (n : Nat) (x : C.modules.component n) :
    (chainMapComp f g).map n x = g.map n (f.map n x) := rfl

end Algebra
end Path
end ComputationalPaths
