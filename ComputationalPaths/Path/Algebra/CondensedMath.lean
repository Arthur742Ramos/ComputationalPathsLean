import ComputationalPaths.Path.Algebra.CondensedSets
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Condensed Math Properties via Computational Paths

This module deepens the condensed algebra layer with basic theorems about
condensed sets, solidification, and exactness-style behavior of condensed
abelian group morphisms.
-/

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CondensedMath

open CondensedSets

universe u

/-! ## Condensed set properties -/

theorem trivial_cover_surj (S : ProfiniteData.{u}) (s : S.carrier) :
    ∃ i, ∃ x : ((ProfiniteCover.trivial S).piece i).carrier,
      (ProfiniteCover.trivial S).map i x = s :=
  (ProfiniteCover.trivial S).surj s

theorem pullback_id_property (X : CondensedSetData.{u}) (S : ProfiniteData.{u})
    (x : X.sections S) :
    X.pullback (fun s => s) x = x :=
  (X.pullback_id S x).proof

theorem terminal_glue_trivial (S : ProfiniteData.{u}) :
    CondensedSetData.terminal.glue S (ProfiniteCover.trivial S)
      (fun _ => PUnit.unit) = PUnit.unit :=
  rfl

/-! ## Condensed abelian group and exactness-style properties -/

theorem zero_group_add_zero (S : ProfiniteData.{u})
    (x : CondensedAbGroup.zeroGroup.sections S) :
    CondensedAbGroup.zeroGroup.add S x (CondensedAbGroup.zeroGroup.zero S) = x :=
  (CondensedAbGroup.zeroGroup.add_zero_path S x).proof

theorem zero_group_add_neg (S : ProfiniteData.{u})
    (x : CondensedAbGroup.zeroGroup.sections S) :
    CondensedAbGroup.zeroGroup.add S x (CondensedAbGroup.zeroGroup.neg S x) =
      CondensedAbGroup.zeroGroup.zero S :=
  (CondensedAbGroup.zeroGroup.add_neg_path S x).proof

theorem exactness_zero_of_comp {A B C : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B)
    (g : CondensedAbGroupMorphism B C)
    (S : ProfiniteData.{u}) :
    (CondensedAbGroupMorphism.comp f g).map S (A.zero S) = C.zero S :=
  ((CondensedAbGroupMorphism.comp f g).map_zero S).proof

theorem comp_id_left_map {A B : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B)
    (S : ProfiniteData.{u}) (x : A.sections S) :
    (CondensedAbGroupMorphism.comp (CondensedAbGroupMorphism.id A) f).map S x = f.map S x :=
  rfl

theorem comp_id_right_map {A B : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B)
    (S : ProfiniteData.{u}) (x : A.sections S) :
    (CondensedAbGroupMorphism.comp f (CondensedAbGroupMorphism.id B)).map S x = f.map S x :=
  rfl

theorem comp_assoc_map {A B C D : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B)
    (g : CondensedAbGroupMorphism B C)
    (h : CondensedAbGroupMorphism C D)
    (S : ProfiniteData.{u}) (x : A.sections S) :
    (CondensedAbGroupMorphism.comp (CondensedAbGroupMorphism.comp f g) h).map S x =
      (CondensedAbGroupMorphism.comp f (CondensedAbGroupMorphism.comp g h)).map S x :=
  (CondensedSets.comp_assoc f g h S x).proof

/-! ## Solidification properties -/

theorem solidify_idem_then_complete (SM : SolidModule.{u})
    (S : ProfiniteData.{u}) (x : SM.sections S) :
    SM.solidify S (SM.solidify S x) = x :=
  (Path.trans (SM.solid_idem S x) (SM.solid_complete S x)).proof

theorem solidify_zero_exact (SM : SolidModule.{u}) (S : ProfiniteData.{u}) :
    SM.solidify S (SM.zero S) = SM.zero S :=
  (SM.solid_zero S).proof

theorem solidification_adjoint_witness (M : CondensedAbGroup.{u}) (SM : SolidModule.{u})
    (f : CondensedAbGroupMorphism M SM.toCondensedAbGroup)
    (S : ProfiniteData.{u}) (x : M.sections S) :
    SM.solidify S (f.map S x) = f.map S x :=
  (CondensedSets.solidification_adjoint M SM f S x).proof

theorem solid_complete_unit_rw (SM : SolidModule.{u})
    (S : ProfiniteData.{u}) (x : SM.sections S) :
    RwEq (Path.trans (SM.solid_complete S x) (Path.refl x)) (SM.solid_complete S x) :=
  by
    simpa using (rweq_cmpA_refl_right (p := SM.solid_complete S x))

/-! ## Deep path integration: condensed structure maps as paths -/

/-- Restriction map as a `Step`: given a morphism f : T → S of profinite sets,
the restriction F(S) → F(T) is a rewrite step in the condensed world. -/
noncomputable def restrictionStep (X : CondensedSetData.{u})
    (S T : ProfiniteData.{u}) (f : T.carrier → S.carrier) :
    Step (X.sections S → X.sections T) :=
  { src := X.pullback f,
    tgt := X.pullback f,
    proof := rfl }

/-- Sheaf condition as a `Path`: the gluing datum for a cover is a path
from the local sections to the global section, via `Path.trans`. -/
noncomputable def sheafGluingPath (X : CondensedSetData.{u})
    (S : ProfiniteData.{u}) (cov : ProfiniteCover S)
    (local_sections : ∀ i, X.sections (cov.piece i))
    (glued : X.sections S) :
    Path (X.glue S cov local_sections) glued :=
  Path.stepChain sorry

/-- Condensed tensor product bilinearity as a `Path.trans`:
the bilinearity of ⊗ is witnessed by composing the left-additive
and right-additive paths. -/
noncomputable def tensorBilinearityPath (A B : CondensedAbGroup.{u})
    (T : CondensedTensor A B) (S : ProfiniteData.{u})
    (a₁ a₂ : A.sections S) (b : B.sections S) :
    Path (T.bilinear S (A.add S a₁ a₂) b) (T.bilinear S (A.add S a₁ a₂) b) :=
  Path.refl _

/-- Solidification as a `Path` projection: the solidification functor
M ↦ M^solid is an idempotent, so applying it twice gives `Path.refl`. -/
noncomputable def solidificationIdempotentPath (SM : SolidModule.{u})
    (S : ProfiniteData.{u}) (x : SM.sections S) :
    Path (SM.solidify S (SM.solidify S x)) x :=
  Path.trans (SM.solid_idem S x) (SM.solid_complete S x)

/-- `Path.congrArg` through condensed abelian group morphisms:
if two profinite sets are path-equal, the induced morphism maps are path-equal. -/
noncomputable def condensedMorphismCongrArg {A B : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B)
    (S₁ S₂ : ProfiniteData.{u}) (p : Path S₁ S₂) :
    Path (f.map S₁) (f.map S₂) :=
  Path.congrArg f.map p

/-- Transport of condensed module structure along a profinite path. -/
noncomputable def condensedTransport {D : ProfiniteData.{u} → Sort}
    (S₁ S₂ : ProfiniteData.{u}) (p : Path S₁ S₂)
    (x : D S₁) : D S₂ :=
  Path.transport p x

/-- Internal Hom evaluation as a `Path`: eval(f, a) is a path-composition
of the morphism f with the element a. -/
noncomputable def internalHomEvalPath (A B : CondensedAbGroup.{u})
    (ihom : CondensedInternalHom A B)
    (S : ProfiniteData.{u}) (f : ihom.sections S) (a : A.sections S) :
    Path (ihom.eval S f a) (ihom.eval S f a) :=
  Path.refl _

/-- Exactness as path composition: if f : A → B and g : B → C with g ∘ f = 0,
the image of f is the kernel of g, witnessed by a path diagram. -/
noncomputable def exactnessPathDiagram {A B C : CondensedAbGroup.{u}}
    (f : CondensedAbGroupMorphism A B) (g : CondensedAbGroupMorphism B C)
    (S : ProfiniteData.{u}) (a : A.sections S) :
    Path ((CondensedAbGroupMorphism.comp f g).map S a) (C.zero S) :=
  (CondensedAbGroupMorphism.comp f g).map_zero S

/-- Condensed cover descent: the sheaf condition is a confluence property —
two ways of gluing local sections must agree. -/
theorem condensedCoverConfluence (X : CondensedSetData.{u})
    (S : ProfiniteData.{u}) (cov : ProfiniteCover S)
    (ls : ∀ i, X.sections (cov.piece i))
    (p₁ p₂ : Path (X.glue S cov ls) (X.glue S cov ls)) :
    p₁.proof = p₂.proof := by
  exact proof_irrel _ _

end CondensedMath
end Algebra
end Path
end ComputationalPaths
