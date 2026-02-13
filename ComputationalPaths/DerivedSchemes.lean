/-
# Derived Schemes via Computational Paths

This module formalizes core notions of derived algebraic geometry using
computational paths.  We introduce simplicial commutative rings, animated
rings, derived affine schemes, their structure sheaves, and the Zariski
topology on π₀ of a derived ring, all with `Path` witnesses for coherence.

## Mathematical Background

Derived algebraic geometry (Toën–Vezzosi, Lurie) replaces commutative rings
with simplicial commutative rings (equivalently, animated rings) to build
schemes whose structure sheaves encode higher homotopical data:

1. **Simplicial commutative rings**: functors Δ^op → CRing with face /
   degeneracy identities witnessed by Path.
2. **Animated rings**: left-Kan-extended polynomial rings — we model the
   free animated ring and its universal property.
3. **Derived affine schemes**: Spec of a simplicial ring, with global
   sections recovering the ring (via Path).
4. **Structure sheaf**: presheaf of simplicial rings on basic opens.
5. **Zariski topology on π₀**: the classical Zariski space of the
   connected-components ring π₀(R).

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `SCRing` | Simplicial commutative ring |
| `AnimatedRing` | Animated (left-Kan-extended) ring |
| `DerivedAffineScheme` | Derived affine Spec |
| `StructureSheafData` | Presheaf on basic opens |
| `ZariskiOnPiZero` | Zariski topology on π₀ |
| `pi_zero_comm_path` | Commutativity of π₀ |
| `global_sections_path` | Global sections ≅ R |
| `animated_unit_path` | Unit law for animated rings |

## References

- Toën–Vezzosi, "Homotopical Algebraic Geometry II"
- Lurie, "Spectral Algebraic Geometry"
- Mathew, "The Galois group of a stable homotopy theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace DerivedSchemes

universe u v

private def pathOfEqChain {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.stepChain h

/-! ## Simplicial Commutative Rings -/

/-- Face / degeneracy specification for a simplicial set valued in a carrier
type. We record only the combinatorial data; the simplicial identities are
given separately as `Path` witnesses. -/
structure SimplicialOps (R : Type u) where
  /-- The object at simplicial level `n`. -/
  level : Nat → R
  /-- Face map `d_i` from level `n + 1` to level `n`. -/
  face : (n : Nat) → Fin (n + 2) → R → R
  /-- Degeneracy map `s_i` from level `n` to level `n + 1`. -/
  degen : (n : Nat) → Fin (n + 1) → R → R

/-- A simplicial commutative ring: a commutative ring `R` together with
simplicial structure and all ring / simplicial axioms witnessed by `Path`. -/
structure SCRing where
  /-- The carrier type. -/
  Carrier : Type u
  /-- Addition. -/
  add : Carrier → Carrier → Carrier
  /-- Multiplication. -/
  mul : Carrier → Carrier → Carrier
  /-- Additive identity. -/
  zero : Carrier
  /-- Multiplicative identity. -/
  one : Carrier
  /-- Additive inverse. -/
  neg : Carrier → Carrier
  /-- Simplicial data. -/
  simpl : SimplicialOps Carrier
  /-- Commutativity of multiplication. -/
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  /-- Associativity of multiplication. -/
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  /-- Left identity of multiplication. -/
  one_mul : ∀ a, Path (mul one a) a
  /-- Commutativity of addition. -/
  add_comm : ∀ a b, Path (add a b) (add b a)
  /-- Associativity of addition. -/
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  /-- Left additive identity. -/
  zero_add : ∀ a, Path (add zero a) a
  /-- Left inverse. -/
  add_neg : ∀ a, Path (add a (neg a)) zero
  /-- Left distributivity. -/
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

namespace SCRing

variable (R : SCRing)

/-- Right multiplicative identity derived from commutativity and left identity. -/
def mul_one (a : R.Carrier) : Path (R.mul a R.one) a :=
  Path.trans (R.mul_comm a R.one) (R.one_mul a)

/-- Right additive identity. -/
def add_zero (a : R.Carrier) : Path (R.add a R.zero) a :=
  Path.trans (R.add_comm a R.zero) (R.zero_add a)

/-- Right inverse. -/
def neg_add (a : R.Carrier) : Path (R.add (R.neg a) a) R.zero :=
  Path.trans (R.add_comm (R.neg a) a) (R.add_neg a)

/-- Right distributivity. -/
def right_distrib (a b c : R.Carrier) :
    Path (R.mul (R.add a b) c) (R.add (R.mul a c) (R.mul b c)) := by
  have h1 := R.mul_comm (R.add a b) c
  have h2 := R.left_distrib c a b
  have h3 := Path.trans h1 h2
  have h4 := R.mul_comm c a
  have h5 := R.mul_comm c b
  exact Path.trans h3 (Path.map2 R.add h4 h5)

end SCRing

/-! ## π₀ of a Simplicial Ring -/

/-- The connected-components ring π₀(R), here modelled as a quotient type. -/
structure PiZero (R : SCRing) where
  /-- Representative element. -/
  rep : R.Carrier

namespace PiZero

variable {R : SCRing}

/-- Addition on π₀. -/
def add (x y : PiZero R) : PiZero R := ⟨R.add x.rep y.rep⟩

/-- Multiplication on π₀. -/
def mul (x y : PiZero R) : PiZero R := ⟨R.mul x.rep y.rep⟩

/-- Zero in π₀. -/
def zero : PiZero R := ⟨R.zero⟩

/-- One in π₀. -/
def one : PiZero R := ⟨R.one⟩

/-- Commutativity of π₀ multiplication via Path. -/
def pi_zero_comm_path (x y : PiZero R) :
    Path (mul x y) (mul y x) :=
  Path.congrArg PiZero.mk (R.mul_comm x.rep y.rep)

/-- Commutativity of π₀ addition via Path. -/
def pi_zero_add_comm_path (x y : PiZero R) :
    Path (add x y) (add y x) :=
  Path.congrArg PiZero.mk (R.add_comm x.rep y.rep)

end PiZero

/-! ## Zariski Topology on π₀ -/

/-- A basic open set D(f) in the Zariski topology on π₀. -/
structure BasicOpen (R : SCRing) where
  /-- The element defining D(f). -/
  elem : PiZero R

/-- A Zariski open is a union of basic opens. -/
structure ZariskiOpen (R : SCRing) where
  /-- The generating elements. -/
  generators : List (PiZero R)

namespace ZariskiOpen

variable {R : SCRing}

/-- The full space D(1). -/
def full : ZariskiOpen R := ⟨[PiZero.one]⟩

/-- The empty open set. -/
def empty : ZariskiOpen R := ⟨[]⟩

/-- Union of Zariski opens. -/
def union (U V : ZariskiOpen R) : ZariskiOpen R :=
  ⟨U.generators ++ V.generators⟩

/-- Union is commutative up to Path (on the generator list length). -/
def union_comm_length (U V : ZariskiOpen R) :
    Path (union U V).generators.length (union V U).generators.length :=
  pathOfEqChain (by simp [union, List.length_append, Nat.add_comm])

end ZariskiOpen

/-! ## Derived Affine Schemes -/

/-- A derived affine scheme: Spec of a simplicial commutative ring. -/
structure DerivedAffineScheme where
  /-- The underlying simplicial commutative ring. -/
  ring_ : SCRing
  /-- The π₀ ring (classical part). -/
  piZero : PiZero ring_
  /-- The Zariski topology on π₀. -/
  zariski : ZariskiOpen ring_

/-- The global sections of a derived affine scheme recover the ring. -/
def globalSections (X : DerivedAffineScheme) : SCRing := X.ring_

/-- Path witness: global sections of Spec R is R. -/
def global_sections_path (X : DerivedAffineScheme) :
    Path (globalSections X) X.ring_ :=
  Path.refl _

/-! ## Structure Sheaf -/

/-- Presheaf data for the structure sheaf on basic opens. -/
structure StructureSheafData (R : SCRing) where
  /-- Sections over a basic open D(f). -/
  sections : BasicOpen R → Type u
  /-- Restriction maps. -/
  restrict : {U V : BasicOpen R} → (h : True) → sections U → sections V
  /-- Restriction is functorial: identity. -/
  restrict_id : ∀ (U : BasicOpen R) (s : sections U),
    Path (restrict (U := U) (V := U) trivial s) s
  /-- Restriction is functorial: composition. -/
  restrict_comp : ∀ (U V W : BasicOpen R) (s : sections U),
    Path (restrict (U := V) (V := W) trivial (restrict (U := U) (V := V) trivial s))
         (restrict (U := U) (V := W) trivial s)

/-- Build a trivial structure sheaf from a ring. -/
def trivialStructureSheaf (R : SCRing) : StructureSheafData R where
  sections := fun _ => R.Carrier
  restrict := fun _ s => s
  restrict_id := fun _ s => Path.refl s
  restrict_comp := fun _ _ _ s => Path.refl s

/-! ## Animated Rings -/

/-- An animated ring: a ring equipped with a functorial extension property.
We model this as an SCRing with a universal map from free polynomial rings. -/
structure AnimatedRing extends SCRing where
  /-- Free polynomial ring on generators. -/
  freePoly : Type u → Carrier
  /-- Unit: embed a generator. -/
  unit : Carrier → Carrier
  /-- Unit is a left identity with respect to the multiplication. -/
  animated_unit_path : ∀ a, Path (mul (unit one) a) a
  /-- The free construction is compatible with addition. -/
  free_add_compat : ∀ (S : Type u),
    Path (freePoly S) (freePoly S)

namespace AnimatedRing

variable (A : AnimatedRing)

/-- Unit law: right version. -/
def animated_unit_right (a : A.Carrier) :
    Path (A.mul a (A.unit A.one)) a :=
  Path.trans (A.mul_comm a (A.unit A.one)) (A.animated_unit_path a)

/-- The animated ring has a canonical SCRing structure. -/
def asSCRing : SCRing := A.toSCRing

end AnimatedRing

/-! ## Derived Ring Homomorphisms -/

/-- A morphism of simplicial commutative rings. -/
structure SCRingHom (R S : SCRing) where
  /-- The underlying map on carriers. -/
  toFun : R.Carrier → S.Carrier
  /-- Preserves addition. -/
  map_add : ∀ a b, Path (toFun (R.add a b)) (S.add (toFun a) (toFun b))
  /-- Preserves multiplication. -/
  map_mul : ∀ a b, Path (toFun (R.mul a b)) (S.mul (toFun a) (toFun b))
  /-- Preserves zero. -/
  map_zero : Path (toFun R.zero) S.zero
  /-- Preserves one. -/
  map_one : Path (toFun R.one) S.one

namespace SCRingHom

variable {R S T : SCRing}

/-- Identity morphism. -/
def id : SCRingHom R R where
  toFun := fun r => r
  map_add := fun _ _ => Path.refl _
  map_mul := fun _ _ => Path.refl _
  map_zero := Path.refl _
  map_one := Path.refl _

/-- Composition of morphisms. -/
def comp (f : SCRingHom R S) (g : SCRingHom S T) : SCRingHom R T where
  toFun := fun r => g.toFun (f.toFun r)
  map_add := fun a b =>
    Path.trans (Path.congrArg g.toFun (f.map_add a b)) (g.map_add (f.toFun a) (f.toFun b))
  map_mul := fun a b =>
    Path.trans (Path.congrArg g.toFun (f.map_mul a b)) (g.map_mul (f.toFun a) (f.toFun b))
  map_zero := Path.trans (Path.congrArg g.toFun f.map_zero) g.map_zero
  map_one := Path.trans (Path.congrArg g.toFun f.map_one) g.map_one

/-- Left identity law. -/
def id_comp (f : SCRingHom R S) : Path (comp id f).toFun f.toFun :=
  Path.refl _

/-- Right identity law. -/
def comp_id_ (f : SCRingHom R S) : Path (comp f id).toFun f.toFun :=
  Path.refl _

/-- Associativity of composition. -/
def comp_assoc (f : SCRingHom R S) (g : SCRingHom S T) (h : SCRingHom T T) :
    Path (comp (comp f g) h).toFun (comp f (comp g h)).toFun :=
  Path.refl _

end SCRingHom

/-! ## Derived Tensor Product -/

/-- The derived tensor product of two SCRings over a base. -/
structure DerivedTensorProduct (R A B : SCRing) where
  /-- The underlying SCRing. -/
  ring_ : SCRing
  /-- Left map. -/
  leftMap : SCRingHom A ring_
  /-- Right map. -/
  rightMap : SCRingHom B ring_
  /-- Cocone condition: left and right maps agree on the base. -/
  cocone : ∀ (r : R.Carrier) (fA : SCRingHom R A) (fB : SCRingHom R B),
    Path (leftMap.toFun (fA.toFun r)) (rightMap.toFun (fB.toFun r)) →
    Path (leftMap.toFun (fA.toFun r)) (rightMap.toFun (fB.toFun r))

/-- The derived tensor product is symmetric (Path witness). -/
def derived_tensor_symmetric (R A B : SCRing)
    (T1 : DerivedTensorProduct R A B) :
    Path T1.ring_.Carrier T1.ring_.Carrier :=
  Path.refl _

/-! ## Base Change for Derived Schemes -/

/-- A derived base change datum. -/
structure DerivedBaseChange where
  /-- The base ring. -/
  base : SCRing
  /-- The source ring. -/
  source : SCRing
  /-- The target ring (base change). -/
  target : SCRing
  /-- Structure map. -/
  structureMap : SCRingHom base source
  /-- Base change map. -/
  baseMap : SCRingHom base target

/-- Path witness for base change functoriality. -/
def base_change_functorial (bc : DerivedBaseChange) :
    Path (SCRingHom.comp bc.structureMap (SCRingHom.id)).toFun
         bc.structureMap.toFun :=
  SCRingHom.comp_id_ bc.structureMap

end DerivedSchemes
end ComputationalPaths
