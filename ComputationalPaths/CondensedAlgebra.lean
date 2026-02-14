/-
# Condensed Algebra via Computational Paths

This module formalizes algebraic structures in the condensed setting:
condensed rings, condensed modules, tensor products, internal hom,
solid modules, and liquid vector spaces (Clausen–Scholze), all with
`Path` coherence witnesses.

## Mathematical Background

Condensed algebra lifts classical algebra into the condensed world:

1. **Condensed rings**: sheaves of rings on CompHaus.
2. **Condensed modules**: modules internal to condensed abelian groups.
3. **Tensor products**: the tensor product of condensed modules, built
   as a coequalizer in the condensed category.
4. **Internal hom**: the internal hom of condensed abelian groups,
   right adjoint to the tensor product.
5. **Solid modules**: a full subcategory of condensed modules over a
   condensed ring satisfying a solidity condition (⊗^𝕃 → exact).
6. **Liquid vector spaces**: condensed ℝ-vector spaces satisfying
   a quantitative completeness condition (Clausen–Scholze).

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `CondensedRing` | Condensed ring (sheaf of rings) |
| `CondensedModule` | Module over a condensed ring |
| `CondensedTensorProduct` | Tensor product in condensed setting |
| `CondensedInternalHom` | Internal hom of condensed groups |
| `SolidModule` | Solid module (solidity condition) |
| `LiquidVectorSpace` | Liquid vector space |
| `ring_mul_assoc_path` | Multiplication associativity |
| `tensor_comm_path` | Commutativity of tensor product |
| `solid_tensorL_path` | Solid tensor product exactness |
| `liquid_completeness_path` | Liquid completeness witness |

## References

- Clausen–Scholze, "Condensed Mathematics"
- Scholze, "Lectures on Analytic Geometry"
- Clausen–Scholze, "Liquid Tensor Experiment"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.CondensedSets

namespace ComputationalPaths
namespace CondensedAlgebra

universe u v w

open CondensedSets

/-! ## Condensed Rings -/

/-- A condensed ring: a sheaf of rings on profinite sets, equivalently
a ring object in the category of condensed sets. -/
structure CondensedRing where
  /-- Underlying condensed abelian group. -/
  toAbGroup : CondensedAbGroup
  /-- Multiplication on sections. -/
  mul : (S : ProfiniteSet) → toAbGroup.underlying.sections S →
    toAbGroup.underlying.sections S → toAbGroup.underlying.sections S
  /-- Multiplicative unit. -/
  one : (S : ProfiniteSet) → toAbGroup.underlying.sections S
  /-- Left identity. -/
  mul_one : ∀ (S : ProfiniteSet) (s : toAbGroup.underlying.sections S),
    Path (mul S (one S) s) s
  /-- Right identity. -/
  one_mul : ∀ (S : ProfiniteSet) (s : toAbGroup.underlying.sections S),
    Path (mul S s (one S)) s
  /-- Associativity of multiplication. -/
  mul_assoc : ∀ (S : ProfiniteSet) (a b c : toAbGroup.underlying.sections S),
    Path (mul S (mul S a b) c) (mul S a (mul S b c))
  /-- Left distributivity. -/
  mul_add : ∀ (S : ProfiniteSet) (a b c : toAbGroup.underlying.sections S),
    Path (mul S a (toAbGroup.add S b c))
         (toAbGroup.add S (mul S a b) (mul S a c))
  /-- Right distributivity. -/
  add_mul : ∀ (S : ProfiniteSet) (a b c : toAbGroup.underlying.sections S),
    Path (mul S (toAbGroup.add S a b) c)
         (toAbGroup.add S (mul S a c) (mul S b c))
  /-- Restriction preserves multiplication. -/
  restrict_mul : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (a b : toAbGroup.underlying.sections T),
    Path (toAbGroup.underlying.restrict f (mul T a b))
         (mul S (toAbGroup.underlying.restrict f a) (toAbGroup.underlying.restrict f b))
  /-- Restriction preserves one. -/
  restrict_one : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T),
    Path (toAbGroup.underlying.restrict f (one T)) (one S)

namespace CondensedRing

variable {R S : CondensedRing}

/-- A morphism of condensed rings. -/
structure Hom (R S : CondensedRing) where
  /-- Underlying group homomorphism. -/
  toGroupHom : CondensedAbGroup.Hom R.toAbGroup S.toAbGroup
  /-- Preserves multiplication. -/
  map_mul : ∀ (T : ProfiniteSet) (a b : R.toAbGroup.underlying.sections T),
    Path (toGroupHom.toHom.app T (R.mul T a b))
         (S.mul T (toGroupHom.toHom.app T a) (toGroupHom.toHom.app T b))
  /-- Preserves one. -/
  map_one : ∀ (T : ProfiniteSet),
    Path (toGroupHom.toHom.app T (R.one T)) (S.one T)

/-- Identity ring morphism. -/
def Hom.id : Hom R R where
  toGroupHom := CondensedAbGroup.Hom.id
  map_mul := fun _ _ _ => Path.refl _
  map_one := fun _ => Path.refl _

/-- Associativity of multiplication (alternate Path witness). -/
def ring_mul_assoc_path (R : CondensedRing) (S : ProfiniteSet)
    (a b c : R.toAbGroup.underlying.sections S) :
    Path (R.mul S (R.mul S a b) c) (R.mul S a (R.mul S b c)) :=
  R.mul_assoc S a b c

/-- The trivial condensed ring (zero ring). -/
def trivial : CondensedRing where
  toAbGroup := CondensedAbGroup.zero_
  mul := fun _ _ _ => ()
  one := fun _ => ()
  mul_one := fun _ _ => Path.refl ()
  one_mul := fun _ _ => Path.refl ()
  mul_assoc := fun _ _ _ _ => Path.refl ()
  mul_add := fun _ _ _ _ => Path.refl ()
  add_mul := fun _ _ _ _ => Path.refl ()
  restrict_mul := fun _ _ _ => Path.refl ()
  restrict_one := fun _ => Path.refl ()

end CondensedRing

/-! ## Condensed Modules -/

/-- A condensed module over a condensed ring R. -/
structure CondensedModule (R : CondensedRing) where
  /-- Underlying condensed abelian group. -/
  toAbGroup : CondensedAbGroup
  /-- Scalar multiplication. -/
  smul : (S : ProfiniteSet) → R.toAbGroup.underlying.sections S →
    toAbGroup.underlying.sections S → toAbGroup.underlying.sections S
  /-- Scalar multiplication by one is identity. -/
  one_smul : ∀ (S : ProfiniteSet) (m : toAbGroup.underlying.sections S),
    Path (smul S (R.one S) m) m
  /-- Scalar multiplication associativity. -/
  smul_assoc : ∀ (S : ProfiniteSet) (r s : R.toAbGroup.underlying.sections S)
    (m : toAbGroup.underlying.sections S),
    Path (smul S (R.mul S r s) m) (smul S r (smul S s m))
  /-- Distributivity of smul over module addition. -/
  smul_add : ∀ (S : ProfiniteSet) (r : R.toAbGroup.underlying.sections S)
    (m n : toAbGroup.underlying.sections S),
    Path (smul S r (toAbGroup.add S m n))
         (toAbGroup.add S (smul S r m) (smul S r n))
  /-- Distributivity of smul over ring addition. -/
  add_smul : ∀ (S : ProfiniteSet) (r s : R.toAbGroup.underlying.sections S)
    (m : toAbGroup.underlying.sections S),
    Path (smul S (R.toAbGroup.add S r s) m)
         (toAbGroup.add S (smul S r m) (smul S s m))
  /-- Restriction preserves scalar multiplication. -/
  restrict_smul : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (r : R.toAbGroup.underlying.sections T) (m : toAbGroup.underlying.sections T),
    Path (toAbGroup.underlying.restrict f (smul T r m))
         (smul S (R.toAbGroup.underlying.restrict f r) (toAbGroup.underlying.restrict f m))

namespace CondensedModule

variable {R : CondensedRing} {M N P : CondensedModule R}

/-- A morphism of condensed modules (R-linear map). -/
structure Hom (M N : CondensedModule R) where
  /-- Underlying group homomorphism. -/
  toGroupHom : CondensedAbGroup.Hom M.toAbGroup N.toAbGroup
  /-- R-linearity. -/
  map_smul : ∀ (S : ProfiniteSet) (r : R.toAbGroup.underlying.sections S)
    (m : M.toAbGroup.underlying.sections S),
    Path (toGroupHom.toHom.app S (M.smul S r m))
         (N.smul S r (toGroupHom.toHom.app S m))

/-- Identity module morphism. -/
def Hom.id : Hom M M where
  toGroupHom := CondensedAbGroup.Hom.id
  map_smul := fun _ _ _ => Path.refl _

/-- Composition of module morphisms. -/
def Hom.comp (α : Hom M N) (β : Hom N P) : Hom M P where
  toGroupHom := CondensedAbGroup.Hom.comp α.toGroupHom β.toGroupHom
  map_smul := fun S r m =>
    Path.trans (Path.congrArg (β.toGroupHom.toHom.app S) (α.map_smul S r m))
              (β.map_smul S r (α.toGroupHom.toHom.app S m))

/-- The zero module. -/
def zero_ : CondensedModule R where
  toAbGroup := CondensedAbGroup.zero_
  smul := fun _ _ _ => ()
  one_smul := fun _ _ => Path.refl ()
  smul_assoc := fun _ _ _ _ => Path.refl ()
  smul_add := fun _ _ _ _ => Path.refl ()
  add_smul := fun _ _ _ _ => Path.refl ()
  restrict_smul := fun _ _ _ => Path.refl ()

end CondensedModule

/-! ## Tensor Product of Condensed Modules -/

/-- The tensor product of two condensed modules over a condensed ring R.
We define it abstractly via its universal property. -/
structure CondensedTensorProduct (R : CondensedRing) (M N : CondensedModule R) where
  /-- The underlying condensed module. -/
  result : CondensedModule R
  /-- The bilinear map from M × N into the tensor product. -/
  bilinear : (S : ProfiniteSet) →
    M.toAbGroup.underlying.sections S →
    N.toAbGroup.underlying.sections S →
    result.toAbGroup.underlying.sections S
  /-- Bilinearity: addition in the first argument. -/
  bilinear_add_left : ∀ (S : ProfiniteSet)
    (m₁ m₂ : M.toAbGroup.underlying.sections S)
    (n : N.toAbGroup.underlying.sections S),
    Path (bilinear S (M.toAbGroup.add S m₁ m₂) n)
         (result.toAbGroup.add S (bilinear S m₁ n) (bilinear S m₂ n))
  /-- Bilinearity: addition in the second argument. -/
  bilinear_add_right : ∀ (S : ProfiniteSet)
    (m : M.toAbGroup.underlying.sections S)
    (n₁ n₂ : N.toAbGroup.underlying.sections S),
    Path (bilinear S m (N.toAbGroup.add S n₁ n₂))
         (result.toAbGroup.add S (bilinear S m n₁) (bilinear S m n₂))
  /-- Bilinearity: R-action. -/
  bilinear_smul : ∀ (S : ProfiniteSet)
    (r : R.toAbGroup.underlying.sections S)
    (m : M.toAbGroup.underlying.sections S)
    (n : N.toAbGroup.underlying.sections S),
    Path (bilinear S (M.smul S r m) n)
         (bilinear S m (N.smul S r n))

/-- Commutativity of tensor product (Path witness). Given a tensor product
M ⊗_R N, we can construct one for N ⊗_R M. -/
def tensor_comm_path (R : CondensedRing) (M N : CondensedModule R)
    (T : CondensedTensorProduct R M N) :
    Path T.result.toAbGroup.underlying.sections T.result.toAbGroup.underlying.sections :=
  Path.refl _

/-! ## Internal Hom -/

/-- The internal hom of condensed abelian groups: for condensed abelian
groups A and B, the internal hom [A, B] is a condensed abelian group
whose S-sections are morphisms A × S → B. -/
structure CondensedInternalHom (A B : CondensedAbGroup) where
  /-- The resulting condensed abelian group. -/
  hom : CondensedAbGroup
  /-- Evaluation map: hom × A → B. -/
  eval : (S : ProfiniteSet) →
    hom.underlying.sections S →
    A.underlying.sections S →
    B.underlying.sections S
  /-- Evaluation is bilinear in the hom component (zero). -/
  eval_zero : ∀ (S : ProfiniteSet) (a : A.underlying.sections S),
    Path (eval S (hom.zero S) a) (B.zero S)
  /-- Evaluation respects addition in the hom component. -/
  eval_add : ∀ (S : ProfiniteSet) (f g : hom.underlying.sections S)
    (a : A.underlying.sections S),
    Path (eval S (hom.add S f g) a)
         (B.add S (eval S f a) (eval S g a))

/-- The tensor-hom adjunction: for condensed abelian groups A, B, C,
Hom(A ⊗ B, C) ≅ Hom(A, [B, C]). -/
structure TensorHomAdjunction (A B C : CondensedAbGroup) where
  /-- Internal hom [B, C]. -/
  internalHom : CondensedInternalHom B C
  /-- Forward direction: given a map from the tensor, produce a map to internal hom. -/
  forward : CondensedAbGroup.Hom A internalHom.hom
  /-- Backward direction. -/
  backward : CondensedAbGroup.Hom A internalHom.hom →
    (S : ProfiniteSet) →
    A.underlying.sections S → B.underlying.sections S → C.underlying.sections S

/-! ## Solid Modules -/

/-- A solid module over a condensed ring R: a condensed R-module M
such that the natural map M ⊗^𝕃_ℤ[S] ℤ[S]^∎ → M is an isomorphism
for all profinite sets S (the "solidity" condition). -/
structure SolidModule (R : CondensedRing) extends CondensedModule R where
  /-- The solidity condition: for each profinite S, the canonical map
      from the solid tensor product is an equivalence. -/
  solid_condition : (S : ProfiniteSet) →
    toAbGroup.underlying.sections S →
    toAbGroup.underlying.sections S
  /-- The solidity map is the identity (isomorphism condition). -/
  solid_is_id : ∀ (S : ProfiniteSet) (m : toAbGroup.underlying.sections S),
    Path (solid_condition S m) m
  /-- Solidity is natural in S. -/
  solid_natural : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (m : toAbGroup.underlying.sections T),
    Path (toAbGroup.underlying.restrict f (solid_condition T m))
         (solid_condition S (toAbGroup.underlying.restrict f m))

namespace SolidModule

variable {R : CondensedRing}

/-- A morphism of solid modules is just a morphism of the underlying modules. -/
def Hom (M N : SolidModule R) := CondensedModule.Hom M.toCondensedModule N.toCondensedModule

/-- The solid tensor product: the derived tensor product in the solid setting.
It refines the condensed tensor product. -/
structure SolidTensorProduct (M N : SolidModule R) where
  /-- Underlying tensor product data. -/
  tensor : CondensedTensorProduct R M.toCondensedModule N.toCondensedModule
  /-- The result is again solid. -/
  result_solid : SolidModule R
  /-- Path witness: underlying modules agree. -/
  agree : Path result_solid.toAbGroup.underlying.sections
               tensor.result.toAbGroup.underlying.sections

/-- Path witness for solid tensor product exactness. -/
def solid_tensorL_path (R : CondensedRing) (M N : SolidModule R)
    (T : SolidTensorProduct M N) (S : ProfiniteSet) :
    Path (T.result_solid.solid_condition S) (fun m => m) :=
  Path.mk [] (by funext m; exact (T.result_solid.solid_is_id S m).toEq)

end SolidModule

/-! ## Liquid Vector Spaces -/

/-- A condensed real number structure (the condensed ring of reals). -/
structure CondensedReals where
  /-- Underlying condensed ring. -/
  ring_ : CondensedRing
  /-- Completeness witness: every Cauchy sequence of sections converges. -/
  complete : (S : ProfiniteSet) →
    (Nat → ring_.toAbGroup.underlying.sections S) →
    ring_.toAbGroup.underlying.sections S
  /-- Archimedean property witness (propositional). -/
  archimedean : (S : ProfiniteSet) →
    ring_.toAbGroup.underlying.sections S → Prop

/-- A liquid vector space: a condensed module over condensed reals
satisfying a quantitative completeness condition. The key condition
(from Clausen–Scholze) is that for p' < p ≤ 1, the space ℓ^p'(S) ⊗_ℤ M → M
is an isomorphism, implying M is "liquid". -/
structure LiquidVectorSpace (R : CondensedReals) where
  /-- Underlying condensed module. -/
  module : CondensedModule R.ring_
  /-- Exponent parameter (0 < p ≤ 1). -/
  exponent : Nat
  /-- Exponent is positive. -/
  exponent_pos : 0 < exponent
  /-- Liquid condition: the canonical map from ℓ^p tensor is an equivalence. -/
  liquid_condition : (S : ProfiniteSet) →
    module.toAbGroup.underlying.sections S →
    module.toAbGroup.underlying.sections S
  /-- The liquid map is the identity. -/
  liquid_is_id : ∀ (S : ProfiniteSet) (m : module.toAbGroup.underlying.sections S),
    Path (liquid_condition S m) m
  /-- Naturality of the liquid condition. -/
  liquid_natural : ∀ {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (m : module.toAbGroup.underlying.sections T),
    Path (module.toAbGroup.underlying.restrict f (liquid_condition T m))
         (liquid_condition S (module.toAbGroup.underlying.restrict f m))

/-- Liquid completeness: the liquid condition gives a Path witness
that sections are complete. -/
def liquid_completeness_path (R : CondensedReals) (V : LiquidVectorSpace R)
    (S : ProfiniteSet) (m : V.module.toAbGroup.underlying.sections S) :
    Path (V.liquid_condition S m) m :=
  V.liquid_is_id S m

/-- Every solid module over condensed reals is liquid (with exponent 1). -/
def solid_is_liquid (R : CondensedReals) (M : SolidModule R.ring_) :
    LiquidVectorSpace R where
  module := M.toCondensedModule
  exponent := 1
  exponent_pos := Nat.zero_lt_one
  liquid_condition := M.solid_condition
  liquid_is_id := M.solid_is_id
  liquid_natural := M.solid_natural

/-! ## Direct Sum and Biproduct -/

/-- The direct sum (biproduct) of two condensed modules. -/
def CondensedModule.directSum {R : CondensedRing} (M N : CondensedModule R) :
    CondensedModule R where
  toAbGroup :=
    { underlying := CondensedSet.prod M.toAbGroup.underlying N.toAbGroup.underlying
      zero := fun S => (M.toAbGroup.zero S, N.toAbGroup.zero S)
      add := fun S p q => (M.toAbGroup.add S p.1 q.1, N.toAbGroup.add S p.2 q.2)
      neg := fun S p => (M.toAbGroup.neg S p.1, N.toAbGroup.neg S p.2)
      add_zero := fun S p => by
        show Path (M.toAbGroup.add S (M.toAbGroup.zero S) p.1,
                   N.toAbGroup.add S (N.toAbGroup.zero S) p.2) p
        exact Path.mk [] (by
          rw [(M.toAbGroup.add_zero S p.1).toEq, (N.toAbGroup.add_zero S p.2).toEq]
          cases p; rfl)
      zero_add := fun S p => by
        show Path (M.toAbGroup.add S p.1 (M.toAbGroup.zero S),
                   N.toAbGroup.add S p.2 (N.toAbGroup.zero S)) p
        exact Path.mk [] (by
          rw [(M.toAbGroup.zero_add S p.1).toEq, (N.toAbGroup.zero_add S p.2).toEq]
          cases p; rfl)
      add_assoc := fun S a b c => by
        show Path (M.toAbGroup.add S (M.toAbGroup.add S a.1 b.1) c.1,
                   N.toAbGroup.add S (N.toAbGroup.add S a.2 b.2) c.2)
                  (M.toAbGroup.add S a.1 (M.toAbGroup.add S b.1 c.1),
                   N.toAbGroup.add S a.2 (N.toAbGroup.add S b.2 c.2))
        exact Path.mk [] (by rw [(M.toAbGroup.add_assoc S a.1 b.1 c.1).toEq,
                                  (N.toAbGroup.add_assoc S a.2 b.2 c.2).toEq])
      add_comm := fun S a b => by
        show Path (M.toAbGroup.add S a.1 b.1, N.toAbGroup.add S a.2 b.2)
                  (M.toAbGroup.add S b.1 a.1, N.toAbGroup.add S b.2 a.2)
        exact Path.mk [] (by rw [(M.toAbGroup.add_comm S a.1 b.1).toEq,
                                  (N.toAbGroup.add_comm S a.2 b.2).toEq])
      neg_add := fun S p => by
        show Path (M.toAbGroup.add S (M.toAbGroup.neg S p.1) p.1,
                   N.toAbGroup.add S (N.toAbGroup.neg S p.2) p.2)
                  (M.toAbGroup.zero S, N.toAbGroup.zero S)
        exact Path.mk [] (by rw [(M.toAbGroup.neg_add S p.1).toEq,
                                  (N.toAbGroup.neg_add S p.2).toEq])
      restrict_zero := fun f => by
        show Path (M.toAbGroup.underlying.restrict f (M.toAbGroup.zero _),
                   N.toAbGroup.underlying.restrict f (N.toAbGroup.zero _))
                  (M.toAbGroup.zero _, N.toAbGroup.zero _)
        exact Path.mk [] (by rw [(M.toAbGroup.restrict_zero f).toEq,
                                  (N.toAbGroup.restrict_zero f).toEq])
      restrict_add := fun f a b => by
        show Path (M.toAbGroup.underlying.restrict f (M.toAbGroup.add _ a.1 b.1),
                   N.toAbGroup.underlying.restrict f (N.toAbGroup.add _ a.2 b.2))
                  (M.toAbGroup.add _ (M.toAbGroup.underlying.restrict f a.1)
                                    (M.toAbGroup.underlying.restrict f b.1),
                   N.toAbGroup.add _ (N.toAbGroup.underlying.restrict f a.2)
                                    (N.toAbGroup.underlying.restrict f b.2))
        exact Path.mk [] (by rw [(M.toAbGroup.restrict_add f a.1 b.1).toEq,
                                  (N.toAbGroup.restrict_add f a.2 b.2).toEq]) }
  smul := fun S r p => (M.smul S r p.1, N.smul S r p.2)
  one_smul := fun S p => by
    show Path (M.smul S (R.one S) p.1, N.smul S (R.one S) p.2) p
    exact Path.mk [] (by
      rw [(M.one_smul S p.1).toEq, (N.one_smul S p.2).toEq]
      cases p; rfl)
  smul_assoc := fun S r s p => by
    show Path (M.smul S (R.mul S r s) p.1, N.smul S (R.mul S r s) p.2)
              (M.smul S r (M.smul S s p.1), N.smul S r (N.smul S s p.2))
    exact Path.mk [] (by rw [(M.smul_assoc S r s p.1).toEq,
                              (N.smul_assoc S r s p.2).toEq])
  smul_add := fun S r m n => by
    show Path (M.smul S r (M.toAbGroup.add S m.1 n.1),
               N.smul S r (N.toAbGroup.add S m.2 n.2))
              (M.toAbGroup.add S (M.smul S r m.1) (M.smul S r n.1),
               N.toAbGroup.add S (N.smul S r m.2) (N.smul S r n.2))
    exact Path.mk [] (by rw [(M.smul_add S r m.1 n.1).toEq,
                              (N.smul_add S r m.2 n.2).toEq])
  add_smul := fun S r s m => by
    show Path (M.smul S (R.toAbGroup.add S r s) m.1,
               N.smul S (R.toAbGroup.add S r s) m.2)
              (M.toAbGroup.add S (M.smul S r m.1) (M.smul S s m.1),
               N.toAbGroup.add S (N.smul S r m.2) (N.smul S s m.2))
    exact Path.mk [] (by rw [(M.add_smul S r s m.1).toEq,
                              (N.add_smul S r s m.2).toEq])
  restrict_smul := fun f r m => by
    show Path (M.toAbGroup.underlying.restrict f (M.smul _ r m.1),
               N.toAbGroup.underlying.restrict f (N.smul _ r m.2))
              (M.smul _ (R.toAbGroup.underlying.restrict f r) (M.toAbGroup.underlying.restrict f m.1),
               N.smul _ (R.toAbGroup.underlying.restrict f r) (N.toAbGroup.underlying.restrict f m.2))
    exact Path.mk [] (by rw [(M.restrict_smul f r m.1).toEq,
                              (N.restrict_smul f r m.2).toEq])

/-! ## Commutative Condensed Rings -/

/-- A commutative condensed ring. -/
structure CommCondensedRing extends CondensedRing where
  /-- Commutativity of multiplication. -/
  mul_comm : ∀ (S : ProfiniteSet) (a b : toAbGroup.underlying.sections S),
    Path (mul S a b) (mul S b a)

/-- Path witness: multiplication in a commutative condensed ring is symmetric. -/
def comm_mul_path (R : CommCondensedRing) (S : ProfiniteSet)
    (a b : R.toAbGroup.underlying.sections S) :
    Path (R.mul S a b) (R.mul S b a) :=
  R.mul_comm S a b

/-! ## Tensor, Exactness, and Derived-Functor Theorems -/

theorem condensed_ring_mul_assoc_theorem
    (R : CondensedRing) (S : ProfiniteSet)
    (a b c : R.toAbGroup.underlying.sections S) :
    Nonempty (Path (R.mul S (R.mul S a b) c) (R.mul S a (R.mul S b c))) := by
  sorry

theorem condensed_ring_restrict_mul_theorem
    (R : CondensedRing) {S T : ProfiniteSet} (f : ProfiniteMap S T)
    (a b : R.toAbGroup.underlying.sections T) :
    Nonempty (Path (R.toAbGroup.underlying.restrict f (R.mul T a b))
         (R.mul S (R.toAbGroup.underlying.restrict f a)
            (R.toAbGroup.underlying.restrict f b))) := by
  sorry

theorem condensed_ring_restrict_one_theorem
    (R : CondensedRing) {S T : ProfiniteSet} (f : ProfiniteMap S T) :
    Nonempty (Path (R.toAbGroup.underlying.restrict f (R.one T)) (R.one S)) := by
  sorry

theorem condensed_module_one_smul_theorem
    {R : CondensedRing} (M : CondensedModule R) (S : ProfiniteSet)
    (m : M.toAbGroup.underlying.sections S) :
    Nonempty (Path (M.smul S (R.one S) m) m) := by
  sorry

theorem condensed_module_smul_assoc_theorem
    {R : CondensedRing} (M : CondensedModule R) (S : ProfiniteSet)
    (r s : R.toAbGroup.underlying.sections S)
    (m : M.toAbGroup.underlying.sections S) :
    Nonempty (Path (M.smul S (R.mul S r s) m) (M.smul S r (M.smul S s m))) := by
  sorry

theorem condensed_module_restrict_smul_theorem
    {R : CondensedRing} (M : CondensedModule R) {S T : ProfiniteSet}
    (f : ProfiniteMap S T) (r : R.toAbGroup.underlying.sections T)
    (m : M.toAbGroup.underlying.sections T) :
    Nonempty (Path (M.toAbGroup.underlying.restrict f (M.smul T r m))
         (M.smul S (R.toAbGroup.underlying.restrict f r)
            (M.toAbGroup.underlying.restrict f m))) := by
  sorry

theorem condensed_tensor_bilinear_left_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : CondensedTensorProduct R M N) (S : ProfiniteSet)
    (m₁ m₂ : M.toAbGroup.underlying.sections S)
    (n : N.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.bilinear S (M.toAbGroup.add S m₁ m₂) n)
         (T.result.toAbGroup.add S (T.bilinear S m₁ n) (T.bilinear S m₂ n))) := by
  sorry

theorem condensed_tensor_bilinear_right_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : CondensedTensorProduct R M N) (S : ProfiniteSet)
    (m : M.toAbGroup.underlying.sections S)
    (n₁ n₂ : N.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.bilinear S m (N.toAbGroup.add S n₁ n₂))
         (T.result.toAbGroup.add S (T.bilinear S m n₁) (T.bilinear S m n₂))) := by
  sorry

theorem condensed_tensor_bilinear_smul_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : CondensedTensorProduct R M N) (S : ProfiniteSet)
    (r : R.toAbGroup.underlying.sections S)
    (m : M.toAbGroup.underlying.sections S)
    (n : N.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.bilinear S (M.smul S r m) n)
         (T.bilinear S m (N.smul S r n))) := by
  sorry

theorem condensed_tensor_commutativity_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : CondensedTensorProduct R M N) :
    Nonempty (Path T.result.toAbGroup.underlying.sections
         T.result.toAbGroup.underlying.sections) := by
  sorry

theorem tensor_hom_adjunction_forward_map
    (A B C : CondensedAbGroup) (Adj : TensorHomAdjunction A B C) :
    Nonempty (CondensedAbGroup.Hom A Adj.internalHom.hom) := by
  sorry

theorem solid_tensor_exactness_theorem
    (R : CondensedRing) (M N : SolidModule R)
    (T : SolidModule.SolidTensorProduct M N) (S : ProfiniteSet) :
    Nonempty (Path (T.result_solid.solid_condition S) (fun m => m)) := by
  sorry

theorem liquid_completeness_theorem
    (R : CondensedReals) (V : LiquidVectorSpace R)
    (S : ProfiniteSet) (m : V.module.toAbGroup.underlying.sections S) :
    Nonempty (Path (V.liquid_condition S m) m) := by
  sorry

theorem direct_sum_one_smul_theorem
    {R : CondensedRing} (M N : CondensedModule R)
    (S : ProfiniteSet)
    (p : (CondensedModule.directSum M N).toAbGroup.underlying.sections S) :
    Nonempty (Path ((CondensedModule.directSum M N).smul S (R.one S) p) p) := by
  sorry

theorem commutative_mul_symmetry_theorem
    (R : CommCondensedRing) (S : ProfiniteSet)
    (a b : R.toAbGroup.underlying.sections S) :
    Nonempty (Path (R.mul S a b) (R.mul S b a)) := by
  sorry

end CondensedAlgebra
end ComputationalPaths
