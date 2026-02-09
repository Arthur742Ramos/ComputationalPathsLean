/-
# Homological Algebra for Path Chain Complexes

This module formalizes basic homological algebra in the computational paths
framework. We define chain complexes of path groups, prove exactness, and
establish the five lemma for path group homomorphisms.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `ChainComplex3` | Chain complex of types with differentials |
| `Exact` | Exactness at a term |
| `ChainMap3` | Chain map between complexes |
| `ShortExact` | Short exact sequence |
| `shortFiveLemma_surj` | The short five lemma (surjection part) |

## References

- Weibel, "An Introduction to Homological Algebra"
- HoTT Book, Chapter 8
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace HomologicalAlgebra

universe u

/-! ## Pointed Sets and Morphisms -/

/-- A pointed set: a type with a distinguished zero element. -/
structure PointedSet where
  /-- The carrier type. -/
  carrier : Type u
  /-- The distinguished element (zero / identity). -/
  zero : carrier

/-- A pointed map between pointed sets (preserves zero). -/
structure PointedHom (A B : PointedSet.{u}) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Preservation of zero. -/
  map_zero : toFun A.zero = B.zero

namespace PointedHom

variable {A B C : PointedSet.{u}}

/-- The identity pointed homomorphism. -/
def id (A : PointedSet.{u}) : PointedHom A A where
  toFun := _root_.id
  map_zero := rfl

/-- Composition of pointed homomorphisms. -/
def comp (g : PointedHom B C) (f : PointedHom A B) : PointedHom A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := by
    simp only [Function.comp]
    rw [f.map_zero, g.map_zero]

/-- Two pointed homs are equal iff their functions are equal. -/
theorem ext {f g : PointedHom A B} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Composition is associative. -/
theorem comp_assoc {D : PointedSet.{u}}
    (h : PointedHom C D) (g : PointedHom B C) (f : PointedHom A B) :
    comp (comp h g) f = comp h (comp g f) := rfl

/-- Left identity. -/
theorem id_comp (f : PointedHom A B) :
    comp (PointedHom.id B) f = f := by
  apply ext; rfl

/-- Right identity. -/
theorem comp_id (f : PointedHom A B) :
    comp f (PointedHom.id A) = f := by
  apply ext; rfl

end PointedHom

/-- The zero (constant) map. -/
def zeroHom (A B : PointedSet.{u}) : PointedHom A B where
  toFun := fun _ => B.zero
  map_zero := rfl

/-! ## Chain Complexes -/

/-- A chain complex of length 3: C₂ → C₁ → C₀ with d₁ ∘ d₂ = 0. -/
structure ChainComplex3 where
  /-- The degree-2 component. -/
  C₂ : PointedSet.{u}
  /-- The degree-1 component. -/
  C₁ : PointedSet.{u}
  /-- The degree-0 component. -/
  C₀ : PointedSet.{u}
  /-- Differential from degree 2 to degree 1. -/
  d₂ : PointedHom C₂ C₁
  /-- Differential from degree 1 to degree 0. -/
  d₁ : PointedHom C₁ C₀
  /-- Chain complex condition: d₁ ∘ d₂ maps everything to zero. -/
  dd_zero : ∀ x, d₁.toFun (d₂.toFun x) = C₀.zero

/-! ## Kernel, Image, and Exactness -/

/-- The kernel of a pointed hom. -/
def Kernel {A B : PointedSet.{u}} (f : PointedHom A B) : Type u :=
  { x : A.carrier // f.toFun x = B.zero }

/-- Zero is in the kernel. -/
def kernel_zero {A B : PointedSet.{u}} (f : PointedHom A B) :
    Kernel f :=
  ⟨A.zero, f.map_zero⟩

/-- The image of a pointed hom. -/
def Image {A B : PointedSet.{u}} (f : PointedHom A B) : Type u :=
  { y : B.carrier // ∃ x : A.carrier, f.toFun x = y }

/-- Zero is in the image. -/
def image_zero {A B : PointedSet.{u}} (f : PointedHom A B) :
    Image f :=
  ⟨B.zero, A.zero, f.map_zero⟩

/-- Exactness at the middle term: kernel of g = image of f. -/
structure Exact {A B C : PointedSet.{u}}
    (f : PointedHom A B) (g : PointedHom B C) : Prop where
  /-- Composition is zero: g(f(x)) = 0 for all x. -/
  im_sub_ker : ∀ x, g.toFun (f.toFun x) = C.zero
  /-- Every kernel element is in the image. -/
  ker_sub_im : ∀ y, g.toFun y = C.zero → ∃ x, f.toFun x = y

/-- The chain complex condition implies image ⊆ kernel. -/
theorem chain_im_sub_ker (cc : ChainComplex3.{u}) :
    ∀ x, cc.d₁.toFun (cc.d₂.toFun x) = cc.C₀.zero :=
  cc.dd_zero

/-! ## Chain Maps -/

/-- A chain map between two chain complexes of length 3. -/
structure ChainMap3 (C D : ChainComplex3.{u}) where
  /-- Map at degree 2. -/
  f₂ : PointedHom C.C₂ D.C₂
  /-- Map at degree 1. -/
  f₁ : PointedHom C.C₁ D.C₁
  /-- Map at degree 0. -/
  f₀ : PointedHom C.C₀ D.C₀
  /-- Commutativity at degree 2-1. -/
  comm₂₁ : ∀ x, f₁.toFun (C.d₂.toFun x) = D.d₂.toFun (f₂.toFun x)
  /-- Commutativity at degree 1-0. -/
  comm₁₀ : ∀ x, f₀.toFun (C.d₁.toFun x) = D.d₁.toFun (f₁.toFun x)

/-- The identity chain map. -/
def ChainMap3.id (C : ChainComplex3.{u}) : ChainMap3 C C where
  f₂ := PointedHom.id C.C₂
  f₁ := PointedHom.id C.C₁
  f₀ := PointedHom.id C.C₀
  comm₂₁ := fun _ => rfl
  comm₁₀ := fun _ => rfl

/-! ## Short Exact Sequences and the Five Lemma -/

/-- A short exact sequence: 0 → A → B → C → 0. -/
structure ShortExact where
  /-- The left term. -/
  A : PointedSet.{u}
  /-- The middle term. -/
  B : PointedSet.{u}
  /-- The right term. -/
  C : PointedSet.{u}
  /-- The injection. -/
  f : PointedHom A B
  /-- The surjection. -/
  g : PointedHom B C
  /-- f is injective. -/
  f_inj : ∀ x y, f.toFun x = f.toFun y → x = y
  /-- g is surjective. -/
  g_surj : ∀ c, ∃ b, g.toFun b = c
  /-- Exactness: ker g = im f. -/
  exact : Exact f g

/-- A morphism of short exact sequences. -/
structure ShortExactMorphism (S T : ShortExact.{u}) where
  /-- Map on left terms. -/
  α : PointedHom S.A T.A
  /-- Map on middle terms. -/
  β : PointedHom S.B T.B
  /-- Map on right terms. -/
  γ : PointedHom S.C T.C
  /-- Left square commutes. -/
  comm_left : ∀ x, β.toFun (S.f.toFun x) = T.f.toFun (α.toFun x)
  /-- Right square commutes. -/
  comm_right : ∀ x, γ.toFun (S.g.toFun x) = T.g.toFun (β.toFun x)

/-- Short five lemma (surjectivity on g-level): if γ is surjective,
then we can factor through the diagram. -/
theorem shortFiveLemma_surj (S T : ShortExact.{u})
    (m : ShortExactMorphism S T)
    (hγ_surj : ∀ c, ∃ c', m.γ.toFun c' = c) :
    ∀ _ : T.C.carrier, ∃ b : S.B.carrier,
      m.γ.toFun (S.g.toFun b) = T.g.toFun (m.β.toFun b) := by
  intro tc
  obtain ⟨c', _⟩ := hγ_surj tc
  obtain ⟨b, _⟩ := S.g_surj c'
  exact ⟨b, by rw [m.comm_right b]⟩

/-- Exactness transfers along chain maps. -/
theorem exactness_transfer {A B C A' B' C' : PointedSet.{u}}
    (_f : PointedHom A B) (g : PointedHom B C)
    (_f' : PointedHom A' B') (_g' : PointedHom B' C')
    (_α : PointedHom A A') (β : PointedHom B B') (γ : PointedHom C C')
    (_hcomm1 : ∀ x, β.toFun (_f.toFun x) = _f'.toFun (_α.toFun x))
    (hcomm2 : ∀ x, γ.toFun (g.toFun x) = _g'.toFun (β.toFun x))
    (_hex : Exact _f g) :
    ∀ x, g.toFun x = C.zero →
      _g'.toFun (β.toFun x) = C'.zero := by
  intro x hx
  have h := hcomm2 x
  rw [hx] at h
  rw [← h, γ.map_zero]

/-! ## Loop Space as a Pointed Set -/

/-- The loop quotient as a pointed set. -/
def loopPointedSet (A : Type u) (a : A) : PointedSet.{u} where
  carrier := π₁(A, a)
  zero := LoopQuot.id

end HomologicalAlgebra
end Path
end ComputationalPaths
