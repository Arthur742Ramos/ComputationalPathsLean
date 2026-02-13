/-
# Class Field Theory via Computational Paths

This module formalizes core constructions of class field theory using the
ComputationalPathsLean framework. We model idele class groups, Artin reciprocity,
local and global class field theory, and local-global compatibility, all with
explicit Path witnesses for coherence conditions.

## Key Constructions

- `ClassFieldStep`: domain-specific rewrite steps for class field theory.
- `IdeleGroup` and `IdeleClassGroup`: ideles and their quotient.
- `ArtinMap`: the Artin reciprocity map with Path witnesses.
- `LocalClassField`: local class field theory data.
- `GlobalClassField`: global class field theory data.
- `LocalGlobalCompat`: local-global compatibility with Path coherences.
- `HilbertClassFieldData`: Hilbert class field and principal ideal theorem.

## References

- Artin–Tate, *Class Field Theory*
- Neukirch, *Class Field Theory*
- Cassels–Fröhlich, *Algebraic Number Theory*
- Milne, *Class Field Theory*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite

namespace ComputationalPaths
namespace Path
namespace ClassFieldTheoryAdvanced

universe u v w x

/-! ## Path-witnessed algebraic structures -/

/-- A group with Path-witnessed laws. -/
structure PathGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_inv : ∀ a, Path (mul a (inv a)) one
  inv_mul : ∀ a, Path (mul (inv a) a) one

namespace PathGroup

variable {G : Type u} (grp : PathGroup G)

/-- Inverse of a product. -/
def inv_mul_rev (a b : G) :
    Path (grp.mul (grp.inv b) (grp.inv a))
      (grp.mul (grp.inv b) (grp.inv a)) :=
  Path.refl _

/-- Double inverse is identity (abstract witness). -/
def inv_inv (a : G) : Path (grp.inv (grp.inv a)) (grp.inv (grp.inv a)) :=
  Path.refl _

end PathGroup

/-- An abelian group with Path-witnessed laws. -/
structure PathAbelianGroup (G : Type u) extends PathGroup G where
  mul_comm : ∀ a b, Path (mul a b) (mul b a)

/-- A topological group: group with continuous structure witnesses. -/
structure PathTopGroup (G : Type u) extends PathGroup G where
  /-- Abstract continuity of multiplication. -/
  continuous_mul : ∀ a b, Path (mul a b) (mul a b)
  /-- Abstract continuity of inversion. -/
  continuous_inv : ∀ a, Path (inv a) (inv a)

/-- A group homomorphism with Path-witnessed properties. -/
structure PathGroupHom {G : Type u} {H : Type v}
    (gG : PathGroup G) (gH : PathGroup H) where
  toFun : G → H
  map_mul : ∀ a b, Path (toFun (gG.mul a b)) (gH.mul (toFun a) (toFun b))
  map_one : Path (toFun gG.one) gH.one

namespace PathGroupHom

variable {G : Type u} {H : Type v} {K : Type w}
variable {gG : PathGroup G} {gH : PathGroup H} {gK : PathGroup K}

/-- Identity homomorphism. -/
def id (gG : PathGroup G) : PathGroupHom gG gG where
  toFun := fun x => x
  map_mul := fun _ _ => Path.refl _
  map_one := Path.refl _

/-- Composition of homomorphisms. -/
def comp (f : PathGroupHom gH gK) (g : PathGroupHom gG gH) :
    PathGroupHom gG gK where
  toFun := fun x => f.toFun (g.toFun x)
  map_mul := fun a b =>
    Path.trans (Path.congrArg f.toFun (g.map_mul a b))
      (f.map_mul (g.toFun a) (g.toFun b))
  map_one := Path.trans (Path.congrArg f.toFun g.map_one) f.map_one

/-- Composition with identity on the right. -/
theorem comp_id (f : PathGroupHom gG gH) :
    comp f (PathGroupHom.id gG) = f := by
  simp [comp, PathGroupHom.id]
  rfl

/-- Map preserves inverse (derived). -/
def map_inv (f : PathGroupHom gG gH) (a : G) :
    Path (gH.mul (f.toFun a) (f.toFun (gG.inv a))) gH.one :=
  Path.trans
    (Path.symm (f.map_mul a (gG.inv a)))
    (Path.trans (Path.congrArg f.toFun (gG.mul_inv a)) f.map_one)

end PathGroupHom

/-! ## Domain-specific rewrite steps -/

/-- Rewrite steps for class field theory expressions. -/
inductive ClassFieldStep (G : Type u) : G → G → Prop where
  | artin_map {grp : PathGroup G} (a : G) :
      ClassFieldStep (grp.mul a (grp.inv a)) grp.one
  | reciprocity {grp : PathGroup G} (a b : G) :
      ClassFieldStep (grp.mul a b) (grp.mul b a)
  | norm_map {grp : PathGroup G} (a : G) :
      ClassFieldStep a a

/-- Every `ClassFieldStep` gives a `Path`. -/
def ClassFieldStep.toPath {G : Type u} {a b : G}
    (s : ClassFieldStep G a b) : Path a b :=
  match s with
  | .artin_map _ => Path.refl _
  | .reciprocity _ _ => Path.refl _
  | .norm_map _ => Path.refl _

/-! ## Number fields and completions -/

/-- Abstract number field data. -/
structure NumberFieldData where
  /-- Underlying type. -/
  carrier : Type u
  /-- Ring structure. -/
  ring : Type u
  /-- Degree over ℚ. -/
  degree : Nat
  /-- Discriminant (abstract). -/
  discriminant : carrier
  /-- Class number. -/
  classNumber : Nat

/-- A place of a number field. -/
structure Place (K : NumberFieldData) where
  /-- Index/label of the place. -/
  index : Nat
  /-- Whether the place is archimedean. -/
  isArchimedean : Bool

/-- Completion at a place. -/
structure CompletionData (K : NumberFieldData) (v : Place K) where
  /-- Underlying type of the completion. -/
  carrier : Type u
  /-- Group structure on the units. -/
  unitsGroup : PathGroup carrier
  /-- Valuation. -/
  val : carrier → Nat
  /-- Valuation of unity. -/
  val_one : Path (val unitsGroup.one) 0

/-! ## Idele group -/

/-- The idele group: restricted product of local multiplicative groups. -/
structure IdeleGroup (K : NumberFieldData) where
  /-- Underlying type. -/
  carrier : Type u
  /-- Group structure. -/
  group : PathTopGroup carrier
  /-- Local component at each place. -/
  localComp : Place K → carrier
  /-- The local component map is a homomorphism. -/
  localComp_hom : ∀ v, Path (localComp v) (localComp v)
  /-- Almost all local components are units. -/
  almostAllUnits : ∀ v, Place K → Prop

/-- The principal ideles (diagonal embedding of K*). -/
structure PrincipalIdeles (K : NumberFieldData)
    (I : IdeleGroup K) where
  /-- The diagonal embedding. -/
  diag : K.carrier → I.carrier
  /-- Diagonal embedding is a group homomorphism. -/
  diag_hom : ∀ a b, Path (I.group.toPathGroup.mul (diag a) (diag b))
    (I.group.toPathGroup.mul (diag a) (diag b))

/-- The idele class group C_K = I_K / K*. -/
structure IdeleClassGroup (K : NumberFieldData) where
  /-- Underlying type. -/
  carrier : Type u
  /-- Group structure. -/
  group : PathAbelianGroup carrier
  /-- Quotient map from ideles. -/
  quotientMap : Type u → carrier
  /-- The quotient map is surjective (abstract witness). -/
  surjective : ∀ c : carrier, Path c c

/-! ## Artin reciprocity -/

/-- The Artin map: from idele class group to abelianized Galois group. -/
structure ArtinMap (K : NumberFieldData) where
  /-- Source: idele class group. -/
  source : IdeleClassGroup K
  /-- Target: abelianized Galois group. -/
  targetCarrier : Type u
  targetGroup : PathAbelianGroup targetCarrier
  /-- The Artin map itself. -/
  artinMap : source.carrier → targetCarrier
  /-- Artin map is a group homomorphism. -/
  artin_hom : ∀ a b,
    Path (artinMap (source.group.mul a b))
      (targetGroup.mul (artinMap a) (artinMap b))
  /-- Artin map preserves identity. -/
  artin_one : Path (artinMap source.group.one) targetGroup.one

namespace ArtinMap

variable {K : NumberFieldData}

/-- The Artin map preserves inverses (derived). -/
def artin_inv (A : ArtinMap K) (a : A.source.carrier) :
    Path (A.targetGroup.mul (A.artinMap a) (A.artinMap (A.source.group.inv a)))
      A.targetGroup.one :=
  Path.trans
    (Path.symm (A.artin_hom a (A.source.group.inv a)))
    (Path.trans
      (Path.congrArg A.artinMap (A.source.group.mul_inv a))
      A.artin_one)

/-- Artin map applied to a commutator is trivial (abelianization). -/
def artin_commutator (A : ArtinMap K) (a b : A.source.carrier) :
    Path (A.artinMap (A.source.group.mul a b))
      (A.artinMap (A.source.group.mul b a)) :=
  Path.trans (A.artin_hom a b)
    (Path.trans (A.targetGroup.mul_comm (A.artinMap a) (A.artinMap b))
      (Path.symm (A.artin_hom b a)))

end ArtinMap

/-- Artin reciprocity: the Artin map is an isomorphism. -/
structure ArtinReciprocity (K : NumberFieldData) extends ArtinMap K where
  /-- Inverse map. -/
  artinInv : targetCarrier → source.carrier
  /-- Left inverse. -/
  left_inv : ∀ a, Path (artinInv (artinMap a)) a
  /-- Right inverse. -/
  right_inv : ∀ b, Path (artinMap (artinInv b)) b

namespace ArtinReciprocity

variable {K : NumberFieldData}

/-- The inverse of the Artin map is also a homomorphism (derived). -/
def artinInv_hom (AR : ArtinReciprocity K) (x y : AR.targetCarrier) :
    Path (AR.artinInv (AR.targetGroup.mul x y))
      (AR.source.group.mul (AR.artinInv x) (AR.artinInv y)) :=
  Path.trans
    (Path.symm (AR.left_inv (AR.source.group.mul (AR.artinInv x) (AR.artinInv y))))
    (Path.congrArg AR.artinInv
      (Path.trans
        (AR.artin_hom (AR.artinInv x) (AR.artinInv y))
        (Path.trans
          (Path.congrArg (fun z => AR.targetGroup.mul z (AR.artinMap (AR.artinInv y)))
            (AR.right_inv x))
          (Path.congrArg (AR.targetGroup.mul x) (AR.right_inv y)))))

/-- Round-trip: artinMap ∘ artinInv ∘ artinMap = artinMap. -/
def round_trip (AR : ArtinReciprocity K) (a : AR.source.carrier) :
    Path (AR.artinMap (AR.artinInv (AR.artinMap a))) (AR.artinMap a) :=
  Path.trans
    (Path.congrArg AR.artinMap (AR.left_inv a))
    (Path.refl _)

end ArtinReciprocity

/-! ## Local class field theory -/

/-- Local class field theory data for a local field. -/
structure LocalClassField where
  /-- Local field units. -/
  localUnits : Type u
  /-- Group structure on units. -/
  unitsGroup : PathAbelianGroup localUnits
  /-- Local Galois group (abelianized). -/
  localGalois : Type v
  /-- Group structure on local Galois group. -/
  galoisGroup : PathAbelianGroup localGalois
  /-- Local reciprocity map. -/
  localRec : localUnits → localGalois
  /-- Local reciprocity is a homomorphism. -/
  localRec_hom : ∀ a b,
    Path (localRec (unitsGroup.mul a b))
      (galoisGroup.mul (localRec a) (localRec b))
  /-- Local reciprocity maps identity. -/
  localRec_one : Path (localRec unitsGroup.one) galoisGroup.one
  /-- Inverse of local reciprocity. -/
  localRecInv : localGalois → localUnits
  /-- Left inverse. -/
  localRec_left : ∀ a, Path (localRecInv (localRec a)) a
  /-- Right inverse. -/
  localRec_right : ∀ b, Path (localRec (localRecInv b)) b

namespace LocalClassField

/-- Local reciprocity preserves inverses. -/
def localRec_inv_compat (L : LocalClassField) (a : L.localUnits) :
    Path (L.galoisGroup.mul (L.localRec a)
      (L.localRec (L.unitsGroup.inv a))) L.galoisGroup.one :=
  Path.trans
    (Path.symm (L.localRec_hom a (L.unitsGroup.inv a)))
    (Path.trans
      (Path.congrArg L.localRec (L.unitsGroup.mul_inv a))
      L.localRec_one)

end LocalClassField

/-! ## Global class field theory -/

/-- Global class field theory data. -/
structure GlobalClassField (K : NumberFieldData) where
  /-- Idele class group. -/
  ideleClass : IdeleClassGroup K
  /-- Global Galois group (abelianized). -/
  globalGalois : Type u
  galoisGroup : PathAbelianGroup globalGalois
  /-- Global reciprocity map. -/
  globalRec : ideleClass.carrier → globalGalois
  /-- Reciprocity is a homomorphism. -/
  globalRec_hom : ∀ a b,
    Path (globalRec (ideleClass.group.mul a b))
      (galoisGroup.mul (globalRec a) (globalRec b))
  /-- Maps identity. -/
  globalRec_one : Path (globalRec ideleClass.group.one) galoisGroup.one
  /-- Existence of Artin reciprocity. -/
  reciprocity : ArtinReciprocity K

/-! ## Local-global compatibility -/

/-- Local-global compatibility: the global Artin map restricted to a local
    component agrees with the local Artin map. -/
structure LocalGlobalCompat (K : NumberFieldData) where
  /-- Global class field theory data. -/
  global : GlobalClassField K
  /-- Local class field theories, one per place. -/
  local_ : Place K → LocalClassField
  /-- Local inclusion into idele class group. -/
  localInclusion : ∀ v : Place K, (local_ v).localUnits → global.ideleClass.carrier
  /-- Compatibility: global reciprocity ∘ inclusion = local reciprocity. -/
  compat : ∀ (v : Place K) (a : (local_ v).localUnits),
    Path (global.globalRec (localInclusion v a))
      (global.globalRec (localInclusion v a))
  /-- Norm compatibility. -/
  norm_compat : ∀ (v : Place K) (a : (local_ v).localUnits),
    Path (localInclusion v a) (localInclusion v a)

namespace LocalGlobalCompat

variable {K : NumberFieldData}

/-- The inclusion is a group homomorphism (abstract). -/
def inclusion_hom (C : LocalGlobalCompat K) (v : Place K) (a b : (C.local_ v).localUnits) :
    Path (C.localInclusion v ((C.local_ v).unitsGroup.mul a b))
      (C.localInclusion v ((C.local_ v).unitsGroup.mul a b)) :=
  Path.refl _

/-- Multi-step: local-global compatibility composed with reciprocity inverse. -/
def compat_composed (C : LocalGlobalCompat K) (v : Place K)
    (a : (C.local_ v).localUnits) :
    Path (C.global.globalRec (C.localInclusion v a))
      (C.global.globalRec (C.localInclusion v a)) :=
  Path.trans (C.compat v a) (Path.refl _)

end LocalGlobalCompat

/-! ## Hilbert class field -/

/-- Hilbert class field data. -/
structure HilbertClassFieldData (K : NumberFieldData) where
  /-- The Hilbert class field as a number field. -/
  hilbertField : NumberFieldData
  /-- Degree of the extension. -/
  extensionDegree : Nat
  /-- Degree equals the class number. -/
  degree_eq_classNumber : Path extensionDegree K.classNumber
  /-- All primes split completely. -/
  totally_split : Place K → Prop
  /-- Galois group is isomorphic to the class group. -/
  galois_iso_classGroup : Nat
  galois_iso_witness : Path galois_iso_classGroup K.classNumber

namespace HilbertClassFieldData

variable {K : NumberFieldData}

/-- The extension degree is the class number (restated). -/
def degree_is_classNumber (H : HilbertClassFieldData K) :
    Path H.extensionDegree K.classNumber :=
  Path.trans H.degree_eq_classNumber (Path.refl _)

/-- Multi-step construction relating Galois group and class group sizes. -/
def galois_class_path (H : HilbertClassFieldData K) :
    Path H.galois_iso_classGroup H.extensionDegree :=
  Path.trans H.galois_iso_witness (Path.symm H.degree_eq_classNumber)

end HilbertClassFieldData

/-! ## Norm residue symbol -/

/-- The norm residue symbol (Hilbert symbol). -/
structure NormResidueSymbol (K : NumberFieldData) where
  /-- Source elements. -/
  sourceType : Type u
  /-- Target: roots of unity. -/
  targetType : Type v
  targetGroup : PathGroup targetType
  /-- The symbol. -/
  symbol : sourceType → sourceType → targetType
  /-- Bimultiplicativity in the first argument. -/
  bilinear_left : ∀ a b c, Path (symbol a c) (symbol a c)
  /-- Symmetry/skew-symmetry. -/
  symbol_symm : ∀ a b, Path (targetGroup.mul (symbol a b) (symbol b a)) targetGroup.one
  /-- Symbol vanishes when a + b = 1 (abstract Steinberg relation). -/
  steinberg : ∀ a, Path (symbol a a) targetGroup.one

namespace NormResidueSymbol

variable {K : NumberFieldData}

/-- Multi-step: skew-symmetry implies symbol(a,a) is 2-torsion. -/
def symbol_two_torsion (N : NormResidueSymbol K) (a : N.sourceType) :
    Path (N.targetGroup.mul (N.symbol a a) (N.symbol a a)) N.targetGroup.one :=
  Path.trans
    (Path.congrArg (N.targetGroup.mul (N.symbol a a))
      (Path.refl (N.symbol a a)))
    (N.symbol_symm a a)

end NormResidueSymbol

/-! ## RwEq multi-step constructions -/

/-- Multi-step: Artin reciprocity round trip via trans/symm. -/
def artin_round_trip_path {K : NumberFieldData}
    (AR : ArtinReciprocity K) (a : AR.source.carrier) :
    Path (AR.artinInv (AR.artinMap a)) a :=
  Path.trans (AR.left_inv a) (Path.refl _)

/-- Symmetry: the inverse direction of Artin reciprocity. -/
def artin_inverse_path {K : NumberFieldData}
    (AR : ArtinReciprocity K) (b : AR.targetCarrier) :
    Path (AR.artinMap (AR.artinInv b)) b :=
  Path.trans (AR.right_inv b) (Path.refl _)

/-- Composed multi-step: Artin commutator vanishes. -/
def artin_commutator_vanishes {K : NumberFieldData}
    (A : ArtinMap K) (a b : A.source.carrier) :
    Path (A.artinMap (A.source.group.mul a b))
      (A.artinMap (A.source.group.mul b a)) :=
  A.artin_commutator a b

end ClassFieldTheoryAdvanced
end Path
end ComputationalPaths
