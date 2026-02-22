/-
# Path Space Monad

This module formalizes the monad structure on the path space endofunctor.
Given a type `A`, the endofunctor sends `A` to the type of all equality-pairs
`Σ a b, a = b`.  We define unit (diagonal embedding), multiplication
(transitivity), and prove the three monad laws.  We also package the
associated Kleisli category.

## Key Results

- `PSM`: the path space endofunctor carrier
- `PSM.fmap`: functorial action
- `PSM.eta`: monad unit
- `PSM.mu`: monad multiplication
- `mu_eta_left`, `mu_eta_right`, `mu_assoc`: monad laws
- `Kleisli`, `kleisli_left_id`, `kleisli_right_id`, `kleisli_assoc`

## References

- Mac Lane, "Categories for the Working Mathematician" (monads)
- HoTT Book, Chapter 2 (path spaces)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace PathSpaceMonad

universe u

/-! ## The path-space endofunctor -/

/-- `PSM A` packages a source, a target, and a propositional equality. -/
structure PSM (A : Type u) : Type u where
  fst : A
  snd : A
  eq  : fst = snd

variable {A B C : Type u}

/-! ## Functorial action -/

/-- Lift a function through the path space. -/
noncomputable def PSM.fmap (f : A → B) : PSM A → PSM B
  | ⟨a, b, h⟩ => ⟨f a, f b, _root_.congrArg f h⟩

@[simp] theorem PSM.fmap_fst (f : A → B) (x : PSM A) :
    (PSM.fmap f x).fst = f x.fst := by cases x; rfl

@[simp] theorem PSM.fmap_snd (f : A → B) (x : PSM A) :
    (PSM.fmap f x).snd = f x.snd := by cases x; rfl

@[simp] theorem PSM.fmap_id (x : PSM A) :
    PSM.fmap (fun a : A => a) x = x := by
  cases x with | mk a b h => cases h; rfl

@[simp] theorem PSM.fmap_comp (f : A → B) (g : B → C) (x : PSM A) :
    PSM.fmap (fun a => g (f a)) x = PSM.fmap g (PSM.fmap f x) := by
  cases x with | mk a b h => cases h; rfl

/-! ## Monad unit (η) -/

/-- Diagonal embedding: `a ↦ (a, a, rfl)`. -/
noncomputable def PSM.eta (a : A) : PSM A := ⟨a, a, rfl⟩

@[simp] theorem PSM.fmap_eta (f : A → B) (a : A) :
    PSM.fmap f (PSM.eta a) = PSM.eta (f a) := rfl

/-! ## Monad multiplication (μ) -/

/-- Multiplication: flatten a nested path space by composing equalities. -/
noncomputable def PSM.mu : PSM (PSM A) → PSM A
  | ⟨s, t, h⟩ => by cases h; exact ⟨s.fst, s.snd, s.eq⟩

/-! ## Monad laws -/

/-- Left unit: `μ ∘ η = id`. -/
@[simp] theorem PSM.mu_eta_left (x : PSM A) :
    PSM.mu (PSM.eta x) = x := by
  cases x with | mk a b h => cases h; rfl

/-- Right unit: `μ ∘ fmap η = id`. -/
@[simp] theorem PSM.mu_eta_right (x : PSM A) :
    PSM.mu (PSM.fmap PSM.eta x) = x := by
  cases x with | mk a b h => cases h; rfl

/-- Associativity: `μ ∘ μ = μ ∘ fmap μ`. -/
@[simp] theorem PSM.mu_assoc (x : PSM (PSM (PSM A))) :
    PSM.mu (PSM.mu x) = PSM.mu (PSM.fmap PSM.mu x) := by
  cases x with | mk s t h => cases h; cases s with | mk a b h => cases h; rfl

/-! ## Kleisli category -/

/-- Kleisli arrow. -/
abbrev Kleisli (A B : Type u) := A → PSM B

/-- Kleisli composition. -/
noncomputable def kleisliComp (g : Kleisli B C) (f : Kleisli A B) : Kleisli A C :=
  fun a => PSM.mu (PSM.fmap g (f a))

/-- Left identity. -/
@[simp] theorem kleisli_left_id (f : Kleisli A B) :
    kleisliComp f PSM.eta = f := by
  funext a
  simp only [kleisliComp, PSM.eta, PSM.fmap, PSM.mu]

/-- Right identity. -/
@[simp] theorem kleisli_right_id (f : Kleisli A B) :
    kleisliComp PSM.eta f = f := by
  funext a
  simp only [kleisliComp]
  cases f a with | mk s t h => cases h; rfl

/-- Associativity. -/
@[simp] theorem kleisli_assoc (h : Kleisli C A) (g : Kleisli B C)
    (f : Kleisli A B) :
    kleisliComp h (kleisliComp g f) =
      kleisliComp (fun b => PSM.mu (PSM.fmap h (g b))) f := by
  funext a
  simp only [kleisliComp]
  cases f a with | mk s t p => cases p; rfl

end PathSpaceMonad
end Path
end ComputationalPaths
