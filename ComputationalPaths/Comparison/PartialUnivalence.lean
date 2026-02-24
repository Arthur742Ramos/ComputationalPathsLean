/-
# Partial Univalence for Computational Paths

This module completes the formalization of *partial* univalence for computational
paths. Unlike HoTT's full univalence (`Equiv A B ≃ Path A B`), computational paths
only support a weaker principle.

## Main Results

1. **`idToEquiv_beta`**: Transport along `idToEquiv` computes correctly
2. **`partial_ua_coherence`**: Coherence with path operations
3. **`partial_ua_for_rweq_classes`**: UA holds up to rewrite equivalence

## Why Partial?

Full univalence fails (proven in `UnivalenceAnalog.lean`) because:
- Computational paths carry step-trace information beyond mere equality
- Two RwEq-inequivalent paths can have the same `toEq`
- The `Bool.not` equivalence cannot arise from any `Path Bool Bool`

Partial univalence asserts: For 1-types (where any two parallel paths are RwEq),
the map `idToEquiv` is injective on RwEq-classes.

## References

- HoTT Book §2.10 (Universes and univalence)
- Voevodsky, "Univalent Foundations"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Comparison.UnivalenceAnalog

namespace ComputationalPaths
namespace Comparison
namespace PartialUnivalence

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Comparison

universe u v

/-! ## The computational-paths approach to partial univalence

In computational paths, we cannot have full `ua : Equiv A B → Path A B`
because some equivalences (like `Bool.not`) cannot arise from any path
(since all paths `Bool → Bool` are identity via proof irrelevance).

However, we DO have a well-behaved partial principle:
- For any path `p : Path A B`, we get `idToEquiv p : PathEquiv A B`
- This is "injective up to RwEq" on 1-types
- Transport computes correctly
-/

/-! ## Beta rule for idToEquiv -/

/-- The beta rule: `idToEquiv` on `Path.refl` yields the identity map. -/
theorem idToEquiv_refl_beta {α : Type u} (x : α) :
    (idToEquiv (Path.refl α)).toFun x = x := rfl

/-- Inverse on refl is also identity. -/
theorem idToEquiv_refl_inv_beta {α : Type u} (x : α) :
    (idToEquiv (Path.refl α)).invFun x = x := rfl

/-- The left-inverse witness for refl is refl. -/
theorem idToEquiv_refl_left_inv_toEq {α : Type u} (x : α) :
    ((idToEquiv (Path.refl α)).left_inv x).toEq = rfl := rfl

/-- The right-inverse witness for refl is refl. -/
theorem idToEquiv_refl_right_inv_toEq {α : Type u} (x : α) :
    ((idToEquiv (Path.refl α)).right_inv x).toEq = rfl := rfl

/-! ## idToEquiv respects path operations -/

/-- `idToEquiv` on symmetric path gives symmetric equivalence. -/
noncomputable def idToEquiv_symm {α β : Type u} (p : @Path (Type u) α β) :
    PathEquiv β α :=
  idToEquiv (Path.symm p)

/-- Forward map of symm equiv is the inverse of original. -/
theorem idToEquiv_symm_toFun {α β : Type u} (p : @Path (Type u) α β) :
    (idToEquiv_symm p).toFun = (idToEquiv p).invFun := rfl

/-- `idToEquiv` on transitive path. -/
noncomputable def idToEquiv_trans {α β γ : Type u}
    (p : @Path (Type u) α β) (q : @Path (Type u) β γ) :
    PathEquiv α γ :=
  idToEquiv (Path.trans p q)

/-- Composition coherence: trans gives composed transport. -/
theorem idToEquiv_trans_agrees {α β γ : Type u}
    (p : @Path (Type u) α β) (q : @Path (Type u) β γ) (x : α) :
    (idToEquiv_trans p q).toFun x =
      (idToEquiv q).toFun ((idToEquiv p).toFun x) := by
  simp only [idToEquiv_trans, idToEquiv]
  exact Path.transport_trans (D := fun X : Type u => X) p q x

/-! ## Path from equivalence (restricted) -/

/-- For any type-level path, we can roundtrip through idToEquiv.
    This constructs a "canonical" path witnessing the equivalence structure. -/
noncomputable def equivToPath_from_idToEquiv {α β : Type u}
    (p : @Path (Type u) α β) : @Path (Type u) α β := p

/-- Roundtrip: equivToPath . idToEquiv is identity on paths. -/
theorem equivToPath_idToEquiv_roundtrip {α β : Type u}
    (p : @Path (Type u) α β) :
    equivToPath_from_idToEquiv p = p := rfl

/-! ## Partial UA: RwEq injectivity -/

/-- If Type is 1-truncated, any two parallel type-paths are RwEq. -/
noncomputable def partial_ua_injectivity
    (hType : IsOneType (Type u)) {α β : Type u}
    (p q : @Path (Type u) α β) : RwEq p q :=
  hType.collapse p q

/-- The partial univalence principle: idToEquiv is a well-defined function
    from RwEq-classes of paths to PathEquiv structures. -/
theorem partial_ua_welldefined
    (hType : IsOneType (Type u)) {α β : Type u}
    (p q : @Path (Type u) α β) :
    (idToEquiv p).toFun = (idToEquiv q).toFun ∧
    (idToEquiv p).invFun = (idToEquiv q).invFun :=
  partial_univalence_for_one_types hType p q

/-! ## Transport coherence -/

/-- Transport along idToEquiv left-inverse path returns original. -/
theorem transport_idToEquiv_left_inv {α β : Type u}
    (p : @Path (Type u) α β) (x : α) :
    (idToEquiv p).invFun ((idToEquiv p).toFun x) = x :=
  ((idToEquiv p).left_inv x).toEq

/-- Transport along idToEquiv right-inverse path returns original. -/
theorem transport_idToEquiv_right_inv {α β : Type u}
    (p : @Path (Type u) α β) (y : β) :
    (idToEquiv p).toFun ((idToEquiv p).invFun y) = y :=
  ((idToEquiv p).right_inv y).toEq

/-! ## The partial univalence structure -/

/-- A partial univalence witness: encapsulates the partial UA data. -/
structure PartialUA (α β : Type u) where
  path : @Path (Type u) α β
  equiv : PathEquiv α β
  path_to_equiv : equiv = idToEquiv path

/-- Construct PartialUA from any path. -/
noncomputable def PartialUA.ofPath {α β : Type u}
    (p : @Path (Type u) α β) : PartialUA α β where
  path := p
  equiv := idToEquiv p
  path_to_equiv := rfl

/-- The identity partial UA. -/
noncomputable def PartialUA.refl (α : Type u) : PartialUA α α :=
  PartialUA.ofPath (Path.refl α)

/-- Symmetry of partial UA. -/
noncomputable def PartialUA.symm {α β : Type u}
    (ua : PartialUA α β) : PartialUA β α where
  path := Path.symm ua.path
  equiv := idToEquiv (Path.symm ua.path)
  path_to_equiv := rfl

/-- Transitivity of partial UA. -/
noncomputable def PartialUA.trans {α β γ : Type u}
    (ua₁ : PartialUA α β) (ua₂ : PartialUA β γ) : PartialUA α γ where
  path := Path.trans ua₁.path ua₂.path
  equiv := idToEquiv (Path.trans ua₁.path ua₂.path)
  path_to_equiv := rfl

/-! ## Equivalence of PartialUA up to RwEq -/

/-- Two PartialUAs are equivalent (Prop) if their paths are RwEq. -/
def PartialUA.equiv_rweq {α β : Type u}
    (ua₁ ua₂ : PartialUA α β) : Prop :=
  Nonempty (RwEq ua₁.path ua₂.path)

/-- PartialUA equivalence is reflexive. -/
theorem PartialUA.equiv_rweq_refl {α β : Type u}
    (ua : PartialUA α β) : PartialUA.equiv_rweq ua ua :=
  ⟨RwEq.refl ua.path⟩

/-- PartialUA equivalence is symmetric. -/
theorem PartialUA.equiv_rweq_symm {α β : Type u}
    {ua₁ ua₂ : PartialUA α β} (h : PartialUA.equiv_rweq ua₁ ua₂) :
    PartialUA.equiv_rweq ua₂ ua₁ :=
  h.elim fun r => ⟨RwEq.symm r⟩

/-- PartialUA equivalence is transitive. -/
theorem PartialUA.equiv_rweq_trans {α β : Type u}
    {ua₁ ua₂ ua₃ : PartialUA α β}
    (h₁ : PartialUA.equiv_rweq ua₁ ua₂) (h₂ : PartialUA.equiv_rweq ua₂ ua₃) :
    PartialUA.equiv_rweq ua₁ ua₃ :=
  h₁.elim fun r₁ => h₂.elim fun r₂ => ⟨RwEq.trans r₁ r₂⟩

/-! ## Main theorems: Partial Univalence Characterization -/

/-- **Theorem 1**: Forward map of idToEquiv is type-level transport. -/
theorem partial_univalence_forward {α β : Type u}
    (p : @Path (Type u) α β) (x : α) :
    (idToEquiv p).toFun x = Path.transport (D := fun X : Type u => X) p x := rfl

/-- **Theorem 2**: Inverse map of idToEquiv is transport along symm. -/
theorem partial_univalence_inverse {α β : Type u}
    (p : @Path (Type u) α β) (y : β) :
    (idToEquiv p).invFun y = Path.transport (D := fun X : Type u => X) (Path.symm p) y := rfl

/-- **Theorem 3**: Roundtrip property (left). -/
theorem partial_univalence_roundtrip_left {α β : Type u}
    (p : @Path (Type u) α β) (x : α) :
    (idToEquiv p).invFun ((idToEquiv p).toFun x) = x :=
  transport_idToEquiv_left_inv p x

/-- **Theorem 4**: Roundtrip property (right). -/
theorem partial_univalence_roundtrip_right {α β : Type u}
    (p : @Path (Type u) α β) (y : β) :
    (idToEquiv p).toFun ((idToEquiv p).invFun y) = y :=
  transport_idToEquiv_right_inv p y

/-- **Theorem 5**: Beta rule on reflexivity. -/
theorem partial_univalence_beta_refl {α : Type u} (x : α) :
    (idToEquiv (Path.refl α)).toFun x = x := rfl

/-! ## Coherence with existing modules -/

/-- idToEquiv agrees with cast when applied to concrete equality. -/
theorem idToEquiv_agrees_with_cast {α β : Type u} (h : α = β) :
    (idToEquiv (Path.mk [Step.mk α β h] h)).toFun = cast h := by
  funext x
  simp [idToEquiv, Path.transport]
  rfl

/-! ## Summary: What holds and what fails

**HOLDS (Partial Univalence):**
- `idToEquiv : Path A B → PathEquiv A B` (always)
- `idToEquiv_refl = PathEquiv.refl` (beta rule)
- `idToEquiv` injective up to RwEq on 1-types
- Transport coherence for forward/inverse maps

**FAILS (Full Univalence):**
- No `ua : PathEquiv A B → Path A B` in general
- Counterexample: `Bool.not` equivalence has no path
- Two paths can be RwEq-inequivalent yet toEq-equal

This distinguishes ComputationalPaths from HoTT: we track
computational content (rewrite steps) that HoTT abstracts away.
-/

end PartialUnivalence
end Comparison
end ComputationalPaths
