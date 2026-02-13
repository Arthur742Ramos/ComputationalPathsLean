/-
# Configuration spaces via computational paths

Defines ordered configuration spaces as families of points indexed by `Fin n`
with a path-based collision predicate. Two indices are forbidden to coincide
whenever a `Path` connects the corresponding points.

We develop: the basic configuration space, the unordered configuration space,
the single-point and two-point configurations, restriction maps,
the forgetful map, and transport of configurations along maps.

## Key Results

- `NoCollision`: path-based distinctness predicate.
- `ConfigurationSpace`: ordered configurations of `n` points in a type.
- `ConfigurationSpace.points` / `ConfigurationSpace.noCollision`: projections.
- `configurationSpaceEmpty`: the empty configuration (n = 0).
- `configurationSpaceSingleton`: single-point configurations.
- `configurationSpacePair`: two-point configurations.
- `UConfigurationSpace`: unordered configuration space.
- `ConfigurationSpace.forget`: forgetful map from (n+1) to n particles.
- `ConfigurationSpace.mapConfig`: transport of configurations along maps.

## References

- Fadell & Neuwirth, "Configuration spaces"
- HoTT Book (path-based distinctness)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Collision predicates -/

/-- Path-based collision predicate for a family of points.
    Two distinct indices must not be connected by a path.
    Since `Path` lives in `Type u`, we use function to `False`. -/
def NoCollision {A : Type u} {n : Nat} (f : Fin n → A) : Prop :=
  ∀ {i j : Fin n}, i ≠ j → Path (f i) (f j) → False

/-- NoCollision is preserved under composition with injective-on-paths functions. -/
theorem noCollision_comp {A B : Type u} {n : Nat}
    (g : A → B) (f : Fin n → A)
    (hg : ∀ {a₁ a₂ : A}, Path (g a₁) (g a₂) → Path a₁ a₂)
    (hf : NoCollision f) : NoCollision (fun i => g (f i)) :=
  fun h p => hf h (hg p)

/-- NoCollision for a subfamily obtained by restricting indices. -/
theorem noCollision_restrict {A : Type u} {n m : Nat}
    (f : Fin n → A) (r : Fin m → Fin n)
    (hr : ∀ {i j : Fin m}, i ≠ j → r i ≠ r j)
    (hf : NoCollision f) : NoCollision (fun i => f (r i)) :=
  fun h p => hf (hr h) p

/-! ## Configuration spaces -/

/-- Ordered configuration space of `n` points in `A`. -/
def ConfigurationSpace (A : Type u) (n : Nat) : Type u :=
  {f : Fin n → A // NoCollision f}

namespace ConfigurationSpace

variable {A : Type u} {n : Nat}

/-- Underlying family of points. -/
@[simp] def points (c : ConfigurationSpace A n) : Fin n → A := c.1

/-- Collision-free property for configurations. -/
theorem noCollision (c : ConfigurationSpace A n) {i j : Fin n} (h : i ≠ j)
    (p : Path (points c i) (points c j)) : False :=
  c.2 h p

/-- The i-th particle of a configuration. -/
def particle (c : ConfigurationSpace A n) (i : Fin n) : A := c.1 i

/-- Two distinct particles are not path-connected. -/
theorem particle_distinct (c : ConfigurationSpace A n)
    {i j : Fin n} (h : i ≠ j) (p : Path (particle c i) (particle c j)) : False :=
  c.2 h p

end ConfigurationSpace

/-! ## Empty configuration -/

/-- The unique empty configuration. -/
def configurationSpaceEmpty (A : Type u) : ConfigurationSpace A 0 :=
  ⟨(fun i => nomatch i), fun {i} => nomatch i⟩

/-- The empty configuration is the only configuration of 0 points. -/
theorem configurationSpace_zero_unique (A : Type u) (c : ConfigurationSpace A 0) :
    c = configurationSpaceEmpty A := by
  cases c with
  | mk f hf =>
    congr
    funext i
    exact nomatch i

/-- Path witness of uniqueness of the empty configuration. -/
def configurationSpace_zero_unique_path (A : Type u) (c : ConfigurationSpace A 0) :
    Path c (configurationSpaceEmpty A) :=
  Path.stepChain (configurationSpace_zero_unique A c)

/-! ## Singleton configuration -/

/-- A single-point configuration is trivially collision-free. -/
def configurationSpaceSingleton {A : Type u} (a : A) : ConfigurationSpace A 1 :=
  ⟨fun _ => a, fun {i j} h _ => by
    have : i = j := by
      have hi := i.isLt
      have hj := j.isLt
      exact Fin.ext (by omega)
    exact absurd this h⟩

/-- The unique point of a singleton configuration. -/
theorem configurationSpaceSingleton_point {A : Type u} (a : A) :
    ConfigurationSpace.particle (configurationSpaceSingleton a) ⟨0, by omega⟩ = a := rfl

/-! ## Pair configuration -/

/-- Helper: given a Fin 2 whose val is known to be 0 or 1, decide which. -/
private theorem fin2_cases (i : Fin 2) : i.val = 0 ∨ i.val = 1 := by
  omega

/-- Two-point configuration from a pair of path-distinct points. -/
def configurationSpacePair {A : Type u} (a b : A)
    (hdist : Path a b → False) : ConfigurationSpace A 2 :=
  ⟨fun i => if i.val = 0 then a else b,
   fun {i j} h p => by
     rcases fin2_cases i with hi | hi <;> rcases fin2_cases j with hj | hj
     · exact absurd (Fin.ext (by omega)) h
     · simp only [hi, hj] at p; exact hdist p
     · simp only [hi, hj] at p; exact hdist (Path.symm p)
     · exact absurd (Fin.ext (by omega)) h⟩

/-- The first particle of a pair configuration. -/
theorem configurationSpacePair_first {A : Type u} (a b : A)
    (hdist : Path a b → False) :
    ConfigurationSpace.particle (configurationSpacePair a b hdist) ⟨0, by omega⟩ = a := rfl

/-- The second particle of a pair configuration. -/
theorem configurationSpacePair_second {A : Type u} (a b : A)
    (hdist : Path a b → False) :
    ConfigurationSpace.particle (configurationSpacePair a b hdist) ⟨1, by omega⟩ = b := rfl

/-! ## Forgetful map -/

/-- Forget the last particle: Conf_{n+1}(A) → Conf_n(A). -/
def ConfigurationSpace.forget {A : Type u} {n : Nat}
    (c : ConfigurationSpace A (n + 1)) : ConfigurationSpace A n :=
  ⟨fun i => c.1 ⟨i.val, by omega⟩,
   fun {i j} h p => c.2
     (by intro heq; exact h (Fin.ext (by
           have := _root_.congrArg Fin.val heq; simpa))) p⟩

/-- The forgetful map preserves the i-th particle for i < n. -/
theorem ConfigurationSpace.forget_particle {A : Type u} {n : Nat}
    (c : ConfigurationSpace A (n + 1)) (i : Fin n) :
    (c.forget).particle i = c.particle ⟨i.val, by omega⟩ := rfl

/-! ## Restriction to a subset of indices -/

/-- Restrict a configuration to a subset of indices given by an injection. -/
def ConfigurationSpace.restrict {A : Type u} {n m : Nat}
    (c : ConfigurationSpace A n) (r : Fin m → Fin n)
    (hr : ∀ {i j : Fin m}, i ≠ j → r i ≠ r j) :
    ConfigurationSpace A m :=
  ⟨fun i => c.1 (r i), noCollision_restrict c.1 r hr c.2⟩

/-- Restriction preserves the particle at the embedded index. -/
theorem ConfigurationSpace.restrict_particle {A : Type u} {n m : Nat}
    (c : ConfigurationSpace A n) (r : Fin m → Fin n)
    (hr : ∀ {i j : Fin m}, i ≠ j → r i ≠ r j) (i : Fin m) :
    (c.restrict r hr).particle i = c.particle (r i) := rfl

/-! ## Transport of configurations along maps -/

/-- Transport a configuration along a function g : A → B that reflects paths. -/
def ConfigurationSpace.mapConfig {A B : Type u} {n : Nat}
    (g : A → B)
    (hg : ∀ {a₁ a₂ : A}, Path (g a₁) (g a₂) → Path a₁ a₂)
    (c : ConfigurationSpace A n) : ConfigurationSpace B n :=
  ⟨fun i => g (c.1 i), noCollision_comp g c.1 hg c.2⟩

/-- The mapped configuration has the expected particles. -/
theorem ConfigurationSpace.mapConfig_particle {A B : Type u} {n : Nat}
    (g : A → B)
    (hg : ∀ {a₁ a₂ : A}, Path (g a₁) (g a₂) → Path a₁ a₂)
    (c : ConfigurationSpace A n) (i : Fin n) :
    (c.mapConfig g hg).particle i = g (c.particle i) := rfl

/-! ## Unordered configuration space -/

/-- The relation identifying configurations that differ by a permutation of indices. -/
def ConfigurationSpace.PermRelated {A : Type u} {n : Nat}
    (c₁ c₂ : ConfigurationSpace A n) : Prop :=
  ∃ σ : Fin n → Fin n,
    (∀ {i j}, σ i = σ j → i = j) ∧ (∀ i, c₂.1 i = c₁.1 (σ i))

/-- Unordered configuration space: quotient by the symmetric group. -/
def UConfigurationSpace (A : Type u) (n : Nat) : Type u :=
  Quot (@ConfigurationSpace.PermRelated A n)

/-- Projection from ordered to unordered configuration space. -/
def UConfigurationSpace.mk {A : Type u} {n : Nat}
    (c : ConfigurationSpace A n) : UConfigurationSpace A n :=
  Quot.mk _ c

/-- The unordered configuration space of 0 points is essentially unique. -/
theorem uConfigurationSpace_zero_unique (A : Type u)
    (x y : UConfigurationSpace A 0) : x = y := by
  refine Quot.inductionOn x ?_
  intro cx
  refine Quot.inductionOn y ?_
  intro cy
  have hcx := configurationSpace_zero_unique A cx
  have hcy := configurationSpace_zero_unique A cy
  rw [hcx, hcy]

/-- Path witness that the unordered 0-configuration space has a unique element. -/
def uConfigurationSpace_zero_unique_path (A : Type u)
    (x y : UConfigurationSpace A 0) :
    Path x y :=
  Path.stepChain (uConfigurationSpace_zero_unique A x y)

/-! ## Diagonal detection -/

/-- The diagonal map (constant function) does NOT yield a valid configuration
    for n ≥ 2 (the points would all be path-equal). -/
theorem diagonal_not_collision_free {A : Type u} (a : A) :
    ¬ NoCollision (fun (_ : Fin 2) => a) := by
  intro h
  have h0 : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := by
    intro heq
    have := _root_.congrArg Fin.val heq
    simp at this
  exact h h0 (Path.refl a)

/-! ## Configuration space of the empty type -/

/-- If A is empty, then ConfigurationSpace A n is empty for n ≥ 1. -/
theorem configurationSpace_empty_type (n : Nat) (hn : n ≥ 1)
    (c : ConfigurationSpace PEmpty n) : False :=
  PEmpty.elim (c.1 ⟨0, by omega⟩)

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
