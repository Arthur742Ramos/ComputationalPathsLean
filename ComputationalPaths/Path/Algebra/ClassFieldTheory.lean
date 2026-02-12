/-
# Class Field Theory via Computational Paths

This module sketches class field theory data in the computational-paths
setting. We model ideles, idele class groups, Artin reciprocity as a Path
witness, local/global compatibility, and a Hilbert class field package.
Reciprocity composition is expressed using `Path.trans`.

## Key Definitions
- `IdeleData`, `IdeleClassGroup`
- `LocalClassFieldTheory`, `GlobalClassFieldTheory`
- `LocalGlobalClassFieldTheory`, `HilbertClassField`
- `ClassFieldStep` for reciprocity rewrites

## References
- Artin-Tate, "Class Field Theory"
- Neukirch, "Class Field Theory"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ClassFieldTheory

universe u

/-! ## Ideles and class groups -/

/-- Minimal data for ideles. -/
structure IdeleData where
  carrier : Type u
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ x, mul x one = x
  one_mul : ∀ x, mul one x = x

namespace IdeleData

variable (I : IdeleData)

/-- Path witness: x * 1 = x for ideles. -/
def mul_one_path (x : I.carrier) : Path (I.mul x I.one) x :=
  Path.ofEq (I.mul_one x)

/-- Path witness: 1 * x = x for ideles. -/
def one_mul_path (x : I.carrier) : Path (I.mul I.one x) x :=
  Path.ofEq (I.one_mul x)

end IdeleData

/-- Idele class group data with quotient map. -/
structure IdeleClassGroup (I : IdeleData.{u}) where
  carrier : Type u
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  classMap : I.carrier → carrier
  class_one : Path (classMap I.one) one
  class_mul : ∀ x y, Path (classMap (I.mul x y)) (mul (classMap x) (classMap y))

/-! ## Local and global fields -/

/-- Local field data with ideles. -/
structure LocalFieldData where
  ideles : IdeleData.{u}

/-- Global field data with ideles and class group. -/
structure GlobalFieldData where
  ideles : IdeleData.{u}
  ideleClass : IdeleClassGroup ideles

/-! ## Abelian Galois groups -/

/-- Abelianized Galois group data. -/
structure AbelianGaloisGroup where
  carrier : Type u
  one : carrier
  mul : carrier → carrier → carrier
  mul_one : ∀ x, mul x one = x
  one_mul : ∀ x, mul one x = x

namespace AbelianGaloisGroup

variable (G : AbelianGaloisGroup)

/-- Path witness: x * 1 = x in the Galois group. -/
def mul_one_path (x : G.carrier) : Path (G.mul x G.one) x :=
  Path.ofEq (G.mul_one x)

/-- Path witness: 1 * x = x in the Galois group. -/
def one_mul_path (x : G.carrier) : Path (G.mul G.one x) x :=
  Path.ofEq (G.one_mul x)

end AbelianGaloisGroup

/-! ## Local and global class field theory -/

/-- Local class field theory data with a reciprocity map. -/
structure LocalClassFieldTheory (K : LocalFieldData.{u}) (G : AbelianGaloisGroup.{u}) where
  localArtin : K.ideles.carrier → G.carrier
  local_one : Path (localArtin K.ideles.one) G.one

/-- Global class field theory data encoding Artin reciprocity. -/
structure GlobalClassFieldTheory (K : GlobalFieldData.{u}) (G : AbelianGaloisGroup.{u}) where
  artin : K.ideleClass.carrier → G.carrier
  artin_one : Path (artin K.ideleClass.one) G.one
  artin_mul : ∀ x y,
    Path (artin (K.ideleClass.mul x y)) (G.mul (artin x) (artin y))

/-- Compatibility between local and global reciprocity maps. -/
structure LocalGlobalClassFieldTheory (K : LocalFieldData.{u}) (L : GlobalFieldData.{u})
    (G : AbelianGaloisGroup.{u}) where
  localCFT : LocalClassFieldTheory K G
  globalCFT : GlobalClassFieldTheory L G
  embed : K.ideles.carrier → L.ideleClass.carrier
  embed_one : Path (embed K.ideles.one) L.ideleClass.one
  compatibility : ∀ x, Path (localCFT.localArtin x) (globalCFT.artin (embed x))

/-- Hilbert class field data packaged with reciprocity. -/
structure HilbertClassField (K : GlobalFieldData.{u}) (G : AbelianGaloisGroup.{u}) where
  classField : Type u
  artinData : GlobalClassFieldTheory K G
  hilbert_reciprocity : Path (artinData.artin K.ideleClass.one) G.one

/-! ## Reciprocity rewrite steps -/

variable {K : GlobalFieldData.{u}} {G : AbelianGaloisGroup.{u}}

/-- Domain-specific rewrite steps for Artin reciprocity calculations. -/
inductive ClassFieldStep (A : GlobalClassFieldTheory K G) :
    G.carrier → G.carrier → Type (u + 1)
  | artin_one : ClassFieldStep A (A.artin K.ideleClass.one) G.one
  | artin_mul (x y : K.ideleClass.carrier) :
      ClassFieldStep A (A.artin (K.ideleClass.mul x y))
        (G.mul (A.artin x) (A.artin y))
  | mul_one (x : G.carrier) : ClassFieldStep A (G.mul x G.one) x

/-- Convert a class field step to a computational path. -/
def classFieldStepPath {A : GlobalClassFieldTheory K G} {x y : G.carrier}
    (s : ClassFieldStep (K := K) (G := G) A x y) : Path x y :=
  match s with
  | ClassFieldStep.artin_one => A.artin_one
  | ClassFieldStep.artin_mul x y => A.artin_mul x y
  | ClassFieldStep.mul_one x => Path.ofEq (G.mul_one x)

/-- Compose two class field steps using `Path.trans`. -/
def classFieldStepCompose {A : GlobalClassFieldTheory K G} {x y z : G.carrier}
    (s1 : ClassFieldStep (K := K) (G := G) A x y)
    (s2 : ClassFieldStep (K := K) (G := G) A y z) : Path x z :=
  Path.trans (classFieldStepPath s1) (classFieldStepPath s2)

/-! ## Reciprocity compositions -/

variable {Kloc : LocalFieldData.{u}} {Kglob : GlobalFieldData.{u}} {G0 : AbelianGaloisGroup.{u}}

/-- Compose local/global reciprocity at the idele unit. -/
def reciprocity_unit_path (C : LocalGlobalClassFieldTheory Kloc Kglob G0) :
    Path (C.localCFT.localArtin Kloc.ideles.one) G0.one :=
  Path.trans
    (C.compatibility Kloc.ideles.one)
    (Path.trans
      (Path.congrArg C.globalCFT.artin C.embed_one)
      (C.globalCFT.artin_one))

/-- RwEq example: composing reciprocity with a reflexive path is equivalent. -/
theorem reciprocity_unit_rweq (C : LocalGlobalClassFieldTheory Kloc Kglob G0) :
    RwEq
      (Path.trans (reciprocity_unit_path (C := C)) (Path.refl G0.one))
      (reciprocity_unit_path (C := C)) := by
  apply rweq_of_eq
  simp

end ClassFieldTheory
end Algebra
end Path
end ComputationalPaths
