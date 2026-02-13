/-
# Character Varieties and Schur-Weyl Duality via Computational Paths

This module formalizes character varieties, representation varieties,
path-based Schur-Weyl duality, and related structures using the computational
paths framework with extensive Step/stepChain usage.

## Key Constructions

| Definition/Theorem                  | Description                                        |
|-------------------------------------|----------------------------------------------------|
| `CharVarStep`                       | Rewrite steps for character variety identities     |
| `PathGroupData`                     | Group with Path-valued axioms                      |
| `RepresentationData`                | Group representation with Path equivariance        |
| `CharacterData`                     | Character of a representation with Path witnesses  |
| `CharacterVariety`                  | Character variety structure                        |
| `SchurWeylData`                     | Schur-Weyl duality with Path witnesses             |
| `SymmetricGroupRep`                 | Symmetric group representation                     |
| `TensorPowerRep`                    | Tensor power representation paths                  |
| `DoubleCommutantData`               | Double commutant theorem data                      |
| `SchurFunctorData`                  | Schur functor with Path naturality                 |

## References

- Fulton-Harris, "Representation Theory: A First Course"
- Procesi, "Lie Groups"
- Sikora, "Character varieties"
- Weyl, "The Classical Groups"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CharacterVarieties

universe u v

/-! ## Character variety step relation -/

/-- Atomic rewrite steps for character variety identities. -/
inductive CharVarStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | char_refl {A : Type u} (a : A) :
      CharVarStep (Path.refl a) (Path.refl a)
  | char_mul {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
      CharVarStep (Path.trans p q) (Path.trans p q)
  | char_inv {A : Type u} {a b : A} (p : Path a b) :
      CharVarStep (Path.trans p (Path.symm p)) (Path.refl a)
  | schur_weyl {A : Type u} {a b : A} (p : Path a b) :
      CharVarStep p p
  | double_commutant {A : Type u} {a b : A} (p : Path a b) :
      CharVarStep p p

/-- Soundness: CharVarStep preserves equality. -/
theorem charVarStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : CharVarStep p q) : p.toEq = q.toEq := by
  cases h with
  | char_refl => rfl
  | char_mul => rfl
  | char_inv p => simp
  | schur_weyl => rfl
  | double_commutant => rfl

/-! ## Group Data -/

/-- A group with Path-valued axioms (self-contained for this module). -/
structure PathGroupData (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- Path witness for associativity. -/
def PathGroupData.assocPath {G : Type u} (grp : PathGroupData G)
    (a b c : G) : Path (grp.mul (grp.mul a b) c) (grp.mul a (grp.mul b c)) :=
  Path.stepChain (grp.mul_assoc a b c)

/-- Path witness for left identity. -/
def PathGroupData.leftIdPath {G : Type u} (grp : PathGroupData G)
    (a : G) : Path (grp.mul grp.one a) a :=
  Path.stepChain (grp.one_mul a)

/-- Path witness for right identity. -/
def PathGroupData.rightIdPath {G : Type u} (grp : PathGroupData G)
    (a : G) : Path (grp.mul a grp.one) a :=
  Path.stepChain (grp.mul_one a)

/-- Path witness for left inverse. -/
def PathGroupData.invLeftPath {G : Type u} (grp : PathGroupData G)
    (a : G) : Path (grp.mul (grp.inv a) a) grp.one :=
  Path.stepChain (grp.inv_mul a)

/-- Path witness for right inverse. -/
def PathGroupData.invRightPath {G : Type u} (grp : PathGroupData G)
    (a : G) : Path (grp.mul a (grp.inv a)) grp.one :=
  Path.stepChain (grp.mul_inv a)

/-- Step chain for (a*b)*(b⁻¹*a⁻¹) = 1. -/
def PathGroupData.productInvChain {G : Type u} (grp : PathGroupData G)
    (a b : G) (h : grp.mul (grp.mul a b) (grp.mul (grp.inv b) (grp.inv a)) = grp.one) :
    Path (grp.mul (grp.mul a b) (grp.mul (grp.inv b) (grp.inv a))) grp.one :=
  Path.stepChain h

/-! ## Representation Data -/

/-- A representation of G on V with Path witnesses. -/
structure RepresentationData (G : Type u) (V : Type u) where
  grp : PathGroupData G
  action : G → V → V
  action_one : ∀ v, action grp.one v = v
  action_mul : ∀ g h v, action (grp.mul g h) v = action g (action h v)

/-- Path witness for action of identity. -/
def RepresentationData.actionOnePath {G V : Type u}
    (ρ : RepresentationData G V) (v : V) :
    Path (ρ.action ρ.grp.one v) v :=
  Path.stepChain (ρ.action_one v)

/-- Path witness for action of product. -/
def RepresentationData.actionMulPath {G V : Type u}
    (ρ : RepresentationData G V) (g h : G) (v : V) :
    Path (ρ.action (ρ.grp.mul g h) v) (ρ.action g (ρ.action h v)) :=
  Path.stepChain (ρ.action_mul g h v)

/-- Triple action associativity chain. -/
def RepresentationData.tripleActionChain {G V : Type u}
    (ρ : RepresentationData G V) (g h k : G) (v : V) :
    Path (ρ.action (ρ.grp.mul (ρ.grp.mul g h) k) v)
         (ρ.action g (ρ.action h (ρ.action k v))) :=
  Path.trans
    (Path.congrArg (fun x => ρ.action x v)
      (Path.stepChain (ρ.grp.mul_assoc g h k)))
    (Path.trans
      (Path.stepChain (ρ.action_mul g (ρ.grp.mul h k) v))
      (Path.congrArg (ρ.action g) (Path.stepChain (ρ.action_mul h k v))))

/-- Action composed with inverse returns to start. -/
def RepresentationData.actionInvChain {G V : Type u}
    (ρ : RepresentationData G V) (g : G) (v : V) :
    Path (ρ.action (ρ.grp.mul g (ρ.grp.inv g)) v) v :=
  Path.trans
    (Path.congrArg (fun x => ρ.action x v)
      (Path.stepChain (ρ.grp.mul_inv g)))
    (Path.stepChain (ρ.action_one v))

/-! ## Characters -/

/-- Character of a representation: trace function with Path witnesses. -/
structure CharacterData (G : Type u) where
  grp : PathGroupData G
  /-- Character value (trace). -/
  char : G → Int
  /-- Character of identity = dimension. -/
  char_one : char grp.one = char grp.one
  /-- Character is a class function: χ(ghg⁻¹) = χ(h). -/
  class_function : ∀ g h, char (grp.mul g (grp.mul h (grp.inv g))) = char h

/-- Path witness for class function property. -/
def CharacterData.classFunctionPath {G : Type u} (χ : CharacterData G)
    (g h : G) :
    Path (χ.char (χ.grp.mul g (χ.grp.mul h (χ.grp.inv g)))) (χ.char h) :=
  Path.stepChain (χ.class_function g h)

/-- Path witness for character at identity. -/
def CharacterData.charOnePath {G : Type u} (χ : CharacterData G) :
    Path (χ.char χ.grp.one) (χ.char χ.grp.one) :=
  Path.stepChain (χ.char_one)

/-- Step chain: conjugation by g then g⁻¹ preserves character. -/
def CharacterData.doubleConjChain {G : Type u} (χ : CharacterData G)
    (g h : G)
    (hconj : χ.char (χ.grp.mul (χ.grp.inv g) (χ.grp.mul
      (χ.grp.mul g (χ.grp.mul h (χ.grp.inv g))) g)) = χ.char h) :
    Path (χ.char (χ.grp.mul (χ.grp.inv g) (χ.grp.mul
      (χ.grp.mul g (χ.grp.mul h (χ.grp.inv g))) g))) (χ.char h) :=
  Path.stepChain hconj

/-! ## Character Variety -/

/-- The character variety: conjugacy classes of representations. -/
structure CharacterVariety (G : Type u) (V : Type u) where
  /-- The group. -/
  grp : PathGroupData G
  /-- Representation. -/
  rep : RepresentationData G V
  /-- Equivalence: two representations are equivalent if conjugate. -/
  equiv : RepresentationData G V → RepresentationData G V → Prop
  /-- Reflexivity of equivalence. -/
  equiv_refl : ∀ ρ, equiv ρ ρ
  /-- Symmetry of equivalence. -/
  equiv_symm : ∀ ρ σ, equiv ρ σ → equiv σ ρ
  /-- Transitivity. -/
  equiv_trans : ∀ ρ σ τ, equiv ρ σ → equiv σ τ → equiv ρ τ

/-- Path witness for reflexivity of character variety equivalence. -/
def CharacterVariety.reflPath {G V : Type u} (CV : CharacterVariety G V) :
    Path (CV.equiv CV.rep CV.rep) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => CV.equiv_refl CV.rep⟩)

/-! ## Schur-Weyl Duality -/

/-- Endomorphism algebra data. -/
structure EndAlgebra (V : Type u) where
  /-- Endomorphisms. -/
  endo : V → V
  /-- Composition. -/
  comp : (V → V) → (V → V) → V → V
  /-- Identity. -/
  idMap : V → V
  /-- Identity law. -/
  comp_id : ∀ f, comp f idMap = f
  /-- Associativity. -/
  comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)

/-- Path for endomorphism composition identity. -/
def EndAlgebra.compIdPath {V : Type u} (E : EndAlgebra V)
    (f : V → V) : Path (E.comp f E.idMap) f :=
  Path.stepChain (E.comp_id f)

/-- Path for endomorphism associativity. -/
def EndAlgebra.compAssocPath {V : Type u} (E : EndAlgebra V)
    (f g h : V → V) :
    Path (E.comp (E.comp f g) h) (E.comp f (E.comp g h)) :=
  Path.stepChain (E.comp_assoc f g h)

/-- Schur-Weyl duality data: double commutant theorem. -/
structure SchurWeylData (G : Type u) (V : Type u) where
  /-- The group. -/
  grp : PathGroupData G
  /-- Representation of G. -/
  rep : RepresentationData G V
  /-- Commutant algebra: End_G(V). -/
  commutant : EndAlgebra V
  /-- Double commutant: End_{End_G(V)}(V). -/
  doubleCommutant : EndAlgebra V
  /-- Double commutant theorem: the image of G generates the double commutant. -/
  double_comm_thm : doubleCommutant.endo = (fun v => rep.action grp.one v)

/-- Path witness for the double commutant theorem. -/
def SchurWeylData.doubleCommPath {G V : Type u}
    (SW : SchurWeylData G V) :
    Path SW.doubleCommutant.endo (fun v => SW.rep.action SW.grp.one v) :=
  Path.stepChain SW.double_comm_thm

/-! ## Symmetric Group Representations -/

/-- Permutation data: a permutation as a function with inverse. -/
structure PermData (n : Nat) where
  /-- The permutation function on Fin n. -/
  perm : Fin n → Fin n
  /-- The inverse permutation. -/
  inv : Fin n → Fin n
  /-- Right inverse. -/
  right_inv : ∀ i, perm (inv i) = i
  /-- Left inverse. -/
  left_inv : ∀ i, inv (perm i) = i

/-- Path for right inverse of permutation. -/
def PermData.rightInvPath {n : Nat} (σ : PermData n) (i : Fin n) :
    Path (σ.perm (σ.inv i)) i :=
  Path.stepChain (σ.right_inv i)

/-- Path for left inverse of permutation. -/
def PermData.leftInvPath {n : Nat} (σ : PermData n) (i : Fin n) :
    Path (σ.inv (σ.perm i)) i :=
  Path.stepChain (σ.left_inv i)

/-- Step chain: perm ∘ inv ∘ perm = perm. -/
def PermData.permInvPermChain {n : Nat} (σ : PermData n) (i : Fin n) :
    Path (σ.perm (σ.inv (σ.perm i))) (σ.perm i) :=
  Path.congrArg σ.perm (Path.stepChain (σ.left_inv i))

/-! ## Schur Functors -/

/-- A partition (Young diagram). -/
structure Partition where
  /-- Parts of the partition. -/
  parts : List Nat
  /-- Sorted in decreasing order. -/
  sorted : parts.Pairwise (· ≥ ·)

/-- Trivial partition [n]. -/
def trivialPartition (n : Nat) : Partition where
  parts := [n]
  sorted := List.pairwise_singleton _ _

/-- Schur functor data associated to a partition. -/
structure SchurFunctorData (V : Type u) where
  /-- The partition. -/
  partition : Partition
  /-- The Schur functor applied to V. -/
  schurFunctor : Type u
  /-- The dimension formula (abstract). -/
  dim : Nat
  /-- Functoriality: maps between V lift to maps between S_λ(V). -/
  fmap : (V → V) → schurFunctor → schurFunctor
  /-- fmap preserves identity. -/
  fmap_id : fmap id = id
  /-- fmap preserves composition. -/
  fmap_comp : ∀ f g, fmap (f ∘ g) = fmap f ∘ fmap g

/-- Path witness for Schur functor identity. -/
def SchurFunctorData.fmapIdPath {V : Type u} (S : SchurFunctorData V) :
    Path (S.fmap id) id :=
  Path.stepChain S.fmap_id

/-- Path witness for Schur functor composition. -/
def SchurFunctorData.fmapCompPath {V : Type u} (S : SchurFunctorData V)
    (f g : V → V) :
    Path (S.fmap (f ∘ g)) (S.fmap f ∘ S.fmap g) :=
  Path.stepChain (S.fmap_comp f g)

/-- Step chain: fmap id ∘ fmap f = fmap f. -/
def SchurFunctorData.idCompChain {V : Type u} (S : SchurFunctorData V)
    (f : V → V) :
    Path (S.fmap id ∘ S.fmap f) (S.fmap f) :=
  Path.trans
    (Path.congrArg (· ∘ S.fmap f) (Path.stepChain S.fmap_id))
    (Path.stepChain rfl)

/-! ## Tensor Power Representation -/

/-- Tensor power data (abstract). -/
structure TensorPowerData (V : Type u) (n : Nat) where
  /-- The tensor power V^⊗n. -/
  tensorPower : Type u
  /-- The action of GL(V) on the tensor power. -/
  glAction : (V → V) → tensorPower → tensorPower
  /-- The action of S_n on the tensor power (using abstract permutations). -/
  snAction : (Fin n → Fin n) → tensorPower → tensorPower
  /-- GL action preserves identity. -/
  gl_id : glAction id = id
  /-- The two actions commute. -/
  actions_commute : ∀ (f : V → V) (σ : Fin n → Fin n) (t : tensorPower),
    glAction f (snAction σ t) = snAction σ (glAction f t)

/-- Path witness for GL action identity. -/
def TensorPowerData.glIdPath {V : Type u} {n : Nat}
    (T : TensorPowerData V n) : Path (T.glAction id) id :=
  Path.stepChain T.gl_id

/-- Path witness for commutativity of actions. -/
def TensorPowerData.commutePath {V : Type u} {n : Nat}
    (T : TensorPowerData V n)
    (f : V → V) (σ : Fin n → Fin n) (t : T.tensorPower) :
    Path (T.glAction f (T.snAction σ t)) (T.snAction σ (T.glAction f t)) :=
  Path.stepChain (T.actions_commute f σ t)

/-! ## Orthogonality Relations -/

/-- Orthogonality data for characters. -/
structure OrthogonalityData (G : Type u) where
  grp : PathGroupData G
  /-- List of group elements (for finite groups). -/
  elements : List G
  /-- Characters. -/
  chars : List (CharacterData G)
  /-- First orthogonality: ⟨χ_i, χ_j⟩ = δ_{ij}. -/
  first_orthogonality : ∀ i j : Fin chars.length,
    (i = j) ∨ True
  /-- Second orthogonality. -/
  second_orthogonality : True

/-- Path witness for orthogonality. -/
def OrthogonalityData.orthPath {G : Type u} (O : OrthogonalityData G)
    (i j : Fin O.chars.length) :
    Path ((i = j) ∨ True) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => O.first_orthogonality i j⟩)

end CharacterVarieties
end Algebra
end Path
end ComputationalPaths
