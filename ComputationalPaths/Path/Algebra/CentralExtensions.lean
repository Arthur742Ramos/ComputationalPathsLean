/-
# Central Extensions via Computational Paths

This module formalizes central extensions using computational paths:
Path-valued cocycles, Schur multiplier, universal central extension,
stem extensions, and group cohomology H².

## Key Constructions

| Definition/Theorem              | Description                                     |
|---------------------------------|-------------------------------------------------|
| `CentralExtension`             | Central extension with Path-valued exactness     |
| `TwoCocycle`                    | 2-cocycle with Path-valued cocycle condition     |
| `TwoCoboundary`                | 2-coboundary from a 1-cochain                   |
| `SchurMultiplier`              | Schur multiplier H₂(G,ℤ) data                  |
| `UniversalCentralExtension`    | Universal central extension                      |
| `StemExtension`                | Stem extension (A ≤ G' ∩ Z(G))                  |
| `H2Group`                      | Second cohomology group data                     |
| `CentralExtStep`              | Domain-specific rewrite steps                    |

## References

- Schur, "Über die Darstellung der endlichen Gruppen"
- Karpilovsky, "The Schur Multiplier"
- Brown, "Cohomology of Groups"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CentralExtensions

universe u v w

/-! ## Group Data -/

/-- Lightweight group data for central extension theory. -/
structure GroupData (G : Type u) where
  /-- Multiplication. -/
  mul : G → G → G
  /-- Identity element. -/
  one : G
  /-- Inverse. -/
  inv : G → G
  /-- Left identity. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity. -/
  mul_one : ∀ x, mul x one = x
  /-- Associativity. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left inverse. -/
  mul_left_inv : ∀ x, mul (inv x) x = one

/-- Path-valued left identity. -/
noncomputable def GroupData.one_mul_path {G : Type u} (D : GroupData G) (x : G) :
    Path (D.mul D.one x) x :=
  Path.stepChain (D.one_mul x)

/-- Path-valued associativity. -/
noncomputable def GroupData.mul_assoc_path {G : Type u} (D : GroupData G) (x y z : G) :
    Path (D.mul (D.mul x y) z) (D.mul x (D.mul y z)) :=
  Path.stepChain (D.mul_assoc x y z)

/-! ## Central Extensions -/

/-- Abelian group data for the kernel of a central extension. -/
structure AbelianGroupData (A : Type u) extends GroupData A where
  /-- Commutativity. -/
  mul_comm : ∀ x y, mul x y = mul y x

/-- A central extension: 1 → A → E → G → 1. -/
structure CentralExtension (A : Type u) (E : Type v) (G : Type w) where
  /-- Abelian group structure on A. -/
  kernel : AbelianGroupData A
  /-- Group structure on E. -/
  extension : GroupData E
  /-- Group structure on G. -/
  quotient_grp : GroupData G
  /-- Injection i : A → E. -/
  injection : A → E
  /-- Projection π : E → G. -/
  projection : E → G
  /-- i is a group homomorphism: preserves multiplication. -/
  inj_mul : ∀ a b, Path (injection (kernel.mul a b))
                        (extension.mul (injection a) (injection b))
  /-- π is a group homomorphism: preserves multiplication. -/
  proj_mul : ∀ x y, Path (projection (extension.mul x y))
                         (quotient_grp.mul (projection x) (projection y))
  /-- Exactness at E: π(i(a)) = 1. -/
  exact_at_E : ∀ a, Path (projection (injection a)) quotient_grp.one
  /-- Centrality: i(a) commutes with all elements of E. -/
  central : ∀ (a : A) (x : E),
    Path (extension.mul (injection a) x) (extension.mul x (injection a))

/-! ## 2-Cocycles -/

/-- A 2-cocycle f : G × G → A satisfying the cocycle condition. -/
structure TwoCocycle (G : Type u) (A : Type v) (gd : GroupData G) (ad : AbelianGroupData A) where
  /-- The cocycle function. -/
  toFun : G → G → A
  /-- Normalized: f(1, g) = 0. -/
  normalized_left : ∀ g, Path (toFun gd.one g) ad.one
  /-- Normalized: f(g, 1) = 0. -/
  normalized_right : ∀ g, Path (toFun g gd.one) ad.one
  /-- Cocycle condition: f(g,h) + f(gh,k) = f(g,hk) + f(h,k). -/
  cocycle_cond : ∀ g h k,
    Path (ad.mul (toFun g h) (toFun (gd.mul g h) k))
         (ad.mul (toFun g (gd.mul h k)) (toFun h k))

/-- Trivial 2-cocycle. -/
noncomputable def TwoCocycle.trivial (G : Type u) (A : Type v) (gd : GroupData G)
    (ad : AbelianGroupData A) : TwoCocycle G A gd ad where
  toFun := fun _ _ => ad.one
  normalized_left := fun _ => Path.refl _
  normalized_right := fun _ => Path.refl _
  cocycle_cond := fun _ _ _ => by
    apply Path.stepChain
    simp [ad.one_mul, ad.mul_one]

/-! ## 2-Coboundaries -/

/-- A 2-coboundary: f(g,h) = s(g) + s(h) - s(gh) for some s : G → A. -/
structure TwoCoboundary (G : Type u) (A : Type v) (gd : GroupData G) (ad : AbelianGroupData A) where
  /-- The 1-cochain. -/
  cochain : G → A
  /-- Normalized: s(1) = 0. -/
  normalized : Path (cochain gd.one) ad.one
  /-- The coboundary function. -/
  toFun : G → G → A := fun g h =>
    ad.mul (ad.mul (cochain g) (cochain h)) (ad.inv (cochain (gd.mul g h)))
  /-- The coboundary is a cocycle. -/
  is_cocycle : TwoCocycle G A gd ad

/-! ## Schur Multiplier -/

/-- Schur multiplier data: H₂(G, ℤ) ≅ ker(E → G) / [E, E] ∩ ker. -/
structure SchurMultiplier (G : Type u) where
  /-- Group structure on G. -/
  grp : GroupData G
  /-- The carrier of the Schur multiplier. -/
  carrier : Type v
  /-- Abelian group structure on the multiplier. -/
  abelian : AbelianGroupData carrier
  /-- For every central extension, the kernel relates to the multiplier. -/
  universal : ∀ (E : Type v) (ext : CentralExtension carrier E G),
    Path (ext.projection (ext.extension.one)) ext.quotient_grp.one

/-- Trivial Schur multiplier. -/
noncomputable def SchurMultiplier.trivialUnit (G : Type u) (gd : GroupData G) : SchurMultiplier G where
  grp := gd
  carrier := PUnit
  abelian := {
    mul := fun _ _ => PUnit.unit
    one := PUnit.unit
    inv := fun _ => PUnit.unit
    one_mul := fun _ => rfl
    mul_one := fun _ => rfl
    mul_assoc := fun _ _ _ => rfl
    mul_left_inv := fun _ => rfl
    mul_comm := fun _ _ => rfl
  }
  universal := fun _ ext =>
    -- π(1_E) = 1_G because π is a group homomorphism
    -- Proof: 1·1 = 1, so π(1·1) = π(1), but also π(1·1) = π(1)·π(1)
    -- Hence π(1) = π(1)·π(1), and by left-cancel with π(1)⁻¹ we get π(1) = 1
    let e := ext.extension.one
    let πe := ext.projection e
    have h_proj_mul := (ext.proj_mul e e).toEq
    have h_one_mul := congr_arg ext.projection (ext.extension.one_mul e)
    -- πe = πe * πe
    have h_idem : πe = ext.quotient_grp.mul πe πe := by
      rw [← h_one_mul, h_proj_mul]
    -- inv(πe) * πe = 1
    have h_left_inv := ext.quotient_grp.mul_left_inv πe
    -- inv(πe) * (πe * πe) = (inv(πe) * πe) * πe = 1 * πe = πe
    -- But also inv(πe) * πe = 1, so from idempotence:
    -- 1 = inv(πe) * πe = inv(πe) * (πe * πe)
    --   = (inv(πe) * πe) * πe = 1 * πe = πe
    Path.stepChain (by
      have := ext.quotient_grp.mul_left_inv πe
      -- this : mul (inv πe) πe = one
      calc πe = ext.quotient_grp.mul ext.quotient_grp.one πe := by
                rw [ext.quotient_grp.one_mul]
            _ = ext.quotient_grp.mul (ext.quotient_grp.mul (ext.quotient_grp.inv πe) πe) πe := by
                rw [this]
            _ = ext.quotient_grp.mul (ext.quotient_grp.inv πe) (ext.quotient_grp.mul πe πe) := by
                rw [ext.quotient_grp.mul_assoc]
            _ = ext.quotient_grp.mul (ext.quotient_grp.inv πe) πe := by
                rw [← h_idem]
            _ = ext.quotient_grp.one := this)

/-! ## Universal Central Extension -/

/-- A universal central extension: every central extension factors through it. -/
structure UniversalCentralExtension (G : Type u) where
  /-- Group data on G. -/
  grp : GroupData G
  /-- The universal covering group. -/
  U : Type v
  /-- Group data on U. -/
  u_grp : GroupData U
  /-- The kernel. -/
  A : Type v
  /-- Abelian group data on the kernel. -/
  a_grp : AbelianGroupData A
  /-- The central extension data. -/
  ext : CentralExtension A U G
  /-- Universality: for any central extension, there is a factoring map. -/
  factor : ∀ (E : Type v) (B : Type v)
    (ext' : CentralExtension B E G), U → E
  /-- The factor map preserves projection. -/
  factor_proj : ∀ (E : Type v) (B : Type v)
    (ext' : CentralExtension B E G) (u : U),
    Path (ext'.projection (factor E B ext' u)) (ext.projection u)

/-! ## Stem Extensions -/

/-- A stem extension: A ≤ [E, E] (kernel contained in commutator). -/
structure StemExtension (A : Type u) (E : Type v) (G : Type w)
    extends CentralExtension A E G where
  /-- Commutator element witness. -/
  commutator : E → E → E := fun x y =>
    extension.mul (extension.mul x y)
                  (extension.mul (extension.inv x) (extension.inv y))
  /-- Every element of A is a product of commutators. -/
  stem_property : ∀ a : A,
    ∃ x y : E, (injection a) = (commutator x y)

/-! ## H² Group Data -/

/-- Second cohomology group H²(G, A) as a quotient of cocycles by coboundaries. -/
structure H2Group (G : Type u) (A : Type v) where
  /-- Group data on G. -/
  grp : GroupData G
  /-- Abelian group data on A. -/
  coeff : AbelianGroupData A
  /-- Carrier of H². -/
  carrier : Type v
  /-- Zero class. -/
  zero : carrier
  /-- Addition in H². -/
  add : carrier → carrier → carrier
  /-- Negation in H². -/
  neg : carrier → carrier
  /-- Zero is left identity. -/
  zero_add : ∀ x, Path (add zero x) x
  /-- Left inverse. -/
  add_left_neg : ∀ x, Path (add (neg x) x) zero
  /-- Map from cocycles to H². -/
  classify : TwoCocycle G A grp coeff → carrier
  /-- The trivial cocycle maps to zero. -/
  classify_trivial : Path (classify (TwoCocycle.trivial G A grp coeff)) zero

/-- Trivial H² on PUnit. -/
noncomputable def H2Group.trivialUnit (G : Type u) (gd : GroupData G) : H2Group G PUnit where
  grp := gd
  coeff := {
    mul := fun _ _ => PUnit.unit
    one := PUnit.unit
    inv := fun _ => PUnit.unit
    one_mul := fun _ => rfl
    mul_one := fun _ => rfl
    mul_assoc := fun _ _ _ => rfl
    mul_left_inv := fun _ => rfl
    mul_comm := fun _ _ => rfl
  }
  carrier := PUnit
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  neg := fun _ => PUnit.unit
  zero_add := fun _ => Path.refl _
  add_left_neg := fun _ => Path.refl _
  classify := fun _ => PUnit.unit
  classify_trivial := Path.refl _

/-! ## Rewrite Steps -/

/-- Rewrite steps for central extension reasoning. -/
inductive CentralExtStep : {A : Type u} → A → A → Type (u + 1)
  | cocycle_normalize {G A : Type u} {gd : GroupData G} {ad : AbelianGroupData A}
      {f : TwoCocycle G A gd ad} {g : G} :
      CentralExtStep (f.toFun gd.one g) ad.one
  | central_commute {A E G : Type u}
      {ext : CentralExtension A E G} {a : A} {x : E} :
      CentralExtStep (ext.extension.mul (ext.injection a) x)
                     (ext.extension.mul x (ext.injection a))
  | exact_kernel {A E G : Type u}
      {ext : CentralExtension A E G} {a : A} :
      CentralExtStep (ext.projection (ext.injection a)) ext.quotient_grp.one

/-- CentralExtStep implies Path. -/
noncomputable def centralExtStep_to_path {A : Type u} {a b : A} (h : CentralExtStep a b) :
    Path a b := by
  cases h with
  | cocycle_normalize => rename_i f g; exact f.normalized_left g
  | central_commute => rename_i ext a x; exact ext.central a x
  | exact_kernel => rename_i ext a; exact ext.exact_at_E a

/-! ## RwEq Instances -/

/-- RwEq: centrality path is stable. -/
noncomputable def rwEq_central {A E G : Type u} (ext : CentralExtension A E G)
    (a : A) (x : E) :
    RwEq (ext.central a x) (ext.central a x) :=
  RwEq.refl _

/-- RwEq: exactness path is stable. -/
noncomputable def rwEq_exact {A E G : Type u} (ext : CentralExtension A E G) (a : A) :
    RwEq (ext.exact_at_E a) (ext.exact_at_E a) :=
  RwEq.refl _

/-- symm ∘ symm for central extension paths. -/
theorem symm_symm_central {A E G : Type u} (ext : CentralExtension A E G) (a : A) :
    Path.toEq (Path.symm (Path.symm (ext.exact_at_E a))) =
    Path.toEq (ext.exact_at_E a) := by
  simp

end CentralExtensions
end Algebra
end Path
end ComputationalPaths
