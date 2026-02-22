/-
# CwF universe structure and contextual morphism coherence

Builds CwF comprehension coherences, CwF morphism algebra, and
dependent-path groupoid laws at the CwF level, all witnessed by
explicit `Path.Step` / `RwEq` rewriting.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.CwF.CwFDeep

namespace ComputationalPaths.CwF

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Comprehension coherences with Path witnesses -/

/-- Projection–extension β-law: proj ∘ ext(σ,t) = σ. -/
theorem proj_ext_beta {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySub A σ)) :
    subComp (projSub A) (extSub σ t) = σ := rfl

/-- Variable–extension β-law: var[ext(σ,t)] = t. -/
theorem var_ext_beta {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySub A σ)) :
    tmSub (varTm A) (extSub σ t) = t := rfl

/-- Extension η-law: ext(proj, var) = id. -/
theorem ext_eta {Γ : Ctx} {A : Ty Γ} :
    extSub (projSub A) (varTm A) = subId (ctxExt Γ A) := by
  funext ⟨γ, a⟩; rfl

/-- Extension naturality: ext(σ∘τ, t[τ]) = ext(σ,t) ∘ τ. -/
theorem ext_naturality {Γ Δ Θ : Ctx} {A : Ty Γ}
    (σ : Sub Δ Γ) (t : Tm Δ (tySub A σ)) (τ : Sub Θ Δ) :
    extSub (subComp σ τ) (tmSub t τ) = subComp (extSub σ t) τ := rfl

/-! ## A strict CwF morphism and its algebra -/

/-- A strict CwF morphism between contexts. -/
structure CwFMorphism (Γ Δ : Ctx) where
  sub : Sub Γ Δ

/-- The identity CwF morphism. -/
noncomputable def cwfMorphId (Γ : Ctx) : CwFMorphism Γ Γ where
  sub := subId Γ

/-- Composition of CwF morphisms. -/
noncomputable def cwfMorphComp {Γ Δ Θ : Ctx}
    (F : CwFMorphism Γ Δ) (G : CwFMorphism Δ Θ) : CwFMorphism Γ Θ where
  sub := subComp G.sub F.sub

theorem cwfMorphComp_assoc {Γ Δ Θ Ξ : Ctx}
    (F : CwFMorphism Γ Δ) (G : CwFMorphism Δ Θ) (H : CwFMorphism Θ Ξ) :
    (cwfMorphComp (cwfMorphComp F G) H).sub = (cwfMorphComp F (cwfMorphComp G H)).sub := rfl

theorem cwfMorphComp_id_left {Γ Δ : Ctx} (F : CwFMorphism Γ Δ) :
    (cwfMorphComp (cwfMorphId Γ) F).sub = F.sub := rfl

theorem cwfMorphComp_id_right {Γ Δ : Ctx} (F : CwFMorphism Γ Δ) :
    (cwfMorphComp F (cwfMorphId Δ)).sub = F.sub := rfl

/-! ## Substitution coherences -/

theorem subComp_assoc {Γ Δ Θ Ξ : Ctx} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ρ : Sub Ξ Θ) :
    subComp (subComp σ τ) ρ = subComp σ (subComp τ ρ) := rfl

theorem subComp_id_left {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    subComp (subId Γ) σ = σ := rfl

theorem subComp_id_right {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    subComp σ (subId Δ) = σ := rfl

theorem tySub_id {Γ : Ctx} (A : Ty Γ) :
    tySub A (subId Γ) = A := rfl

theorem tySub_comp {Γ Δ Θ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tySub (tySub A σ) τ = tySub A (subComp σ τ) := rfl

theorem tmSub_id {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) :
    tmSub t (subId Γ) = t := rfl

theorem tmSub_comp {Γ Δ Θ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tmSub (tmSub t σ) τ = tmSub t (subComp σ τ) := rfl

/-! ## Weakening and projection -/

/-- Weakening a type by a fresh type variable. -/
noncomputable def weaken {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) : Ty (ctxExt Γ A) :=
  tySub B (projSub A)

/-- Weakening a term by a fresh type variable. -/
noncomputable def weakenTm {Γ : Ctx} {A : Ty Γ} {B : Ty Γ}
    (t : Tm Γ B) : Tm (ctxExt Γ A) (weaken A B) :=
  tmSub t (projSub A)

/-- Substituting the projection into a weakened type recovers the original. -/
theorem weaken_proj_subst_id {Γ : Ctx} {A B : Ty Γ} (a : Tm Γ A) :
    tySub (weaken A B) (extSub (subId Γ) a) = B := rfl

/-- The variable term in extended context is the second projection. -/
theorem varTm_is_snd {Γ : Ctx} {A : Ty Γ} :
    varTm A = Sigma.snd := rfl

/-! ## Dependent-path coherences for the CwF identity type -/

/-- Transport along an identity path at the CwF level. -/
noncomputable def idTransport {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (C : Ty (ctxExt Γ A)) (p : Tm Γ (IdTy a b))
    (t : Tm Γ (fun γ => C ⟨γ, a γ⟩)) : Tm Γ (fun γ => C ⟨γ, b γ⟩) :=
  fun γ => Path.cast (A := A γ) (D := fun x => C ⟨γ, x⟩) (p γ) (t γ)

/-- Transport along refl is the identity. -/
theorem idTransport_refl {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A)
    (C : Ty (ctxExt Γ A)) (t : Tm Γ (fun γ => C ⟨γ, a γ⟩)) :
    idTransport C (idRefl a) t = t := by
  funext γ; simp [idTransport, idRefl]
  rfl

/-! ## Σ-type and Π-type substitution coherences -/

theorem sigmaTy_subst {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)} (σ : Sub Δ Γ) :
    tySub (SigmaTy A B) σ = SigmaTy (tySub A σ) (tySub B (fun ⟨δ, a⟩ => ⟨σ δ, a⟩)) := rfl

theorem piTy_subst {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)} (σ : Sub Δ Γ) :
    tySub (PiTy A B) σ = PiTy (tySub A σ) (tySub B (fun ⟨δ, a⟩ => ⟨σ δ, a⟩)) := rfl

/-! ## Identity type groupoid laws as RwEq witnesses -/

noncomputable def groupoid_pentagon {Γ : Ctx} {A : Ty Γ}
    {a b c d e : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c))
    (r : Tm Γ (IdTy c d)) (s : Tm Γ (IdTy d e)) (γ : Γ) :
    RwEq (Path.trans (Path.trans (Path.trans (p γ) (q γ)) (r γ)) (s γ))
         (Path.trans (p γ) (Path.trans (q γ) (Path.trans (r γ) (s γ)))) := by
  exact RwEq.trans
    (RwEq.step (Path.Step.trans_assoc (Path.trans (p γ) (q γ)) (r γ) (s γ)))
    (RwEq.step (Path.Step.trans_assoc (p γ) (q γ) (Path.trans (r γ) (s γ))))

noncomputable def groupoid_right_whisker {Γ : Ctx} {A : Ty Γ}
    {a b c : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (γ : Γ) :
    RwEq (Path.trans (Path.trans (p γ) (q γ)) (Path.symm (q γ)))
         (Path.trans (p γ) (Path.refl (b γ))) :=
  RwEq.trans
    (RwEq.step (Path.Step.trans_assoc (p γ) (q γ) (Path.symm (q γ))))
    (rweq_trans_congr_right (p γ)
      (RwEq.step (Path.Step.trans_symm (q γ))))

noncomputable def groupoid_left_whisker {Γ : Ctx} {A : Ty Γ}
    {a b c : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (γ : Γ) :
    RwEq (Path.trans (Path.symm (p γ)) (Path.trans (p γ) (q γ)))
         (Path.trans (Path.refl (b γ)) (q γ)) := by
  have h1 : RwEq (Path.trans (Path.symm (p γ)) (Path.trans (p γ) (q γ)))
                  (Path.trans (Path.trans (Path.symm (p γ)) (p γ)) (q γ)) :=
    RwEq.symm (RwEq.step (Path.Step.trans_assoc (Path.symm (p γ)) (p γ) (q γ)))
  have h2 : RwEq (Path.trans (Path.trans (Path.symm (p γ)) (p γ)) (q γ))
                  (Path.trans (Path.refl (b γ)) (q γ)) :=
    rweq_trans_congr_left (q γ) (RwEq.step (Path.Step.symm_trans (p γ)))
  exact RwEq.trans h1 h2

/-! ## Double-inverse and triple-composition coherences -/

noncomputable def double_inverse_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (Path.symm (Path.symm (p γ))) (p γ) :=
  RwEq.step (Path.Step.symm_symm (p γ))

noncomputable def triple_trans_rweq {Γ : Ctx} {A : Ty Γ} {a b c d : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (r : Tm Γ (IdTy c d)) (γ : Γ) :
    RwEq (Path.trans (Path.trans (p γ) (q γ)) (r γ))
         (Path.trans (p γ) (Path.trans (q γ) (r γ))) :=
  RwEq.step (Path.Step.trans_assoc (p γ) (q γ) (r γ))

/-! ## Product type former in CwF -/

noncomputable def ProdTy {Γ : Ctx} (A B : Ty Γ) : Ty Γ :=
  fun γ => A γ × B γ

noncomputable def pairTm {Γ : Ctx} {A B : Ty Γ}
    (a : Tm Γ A) (b : Tm Γ B) : Tm Γ (ProdTy A B) :=
  fun γ => (a γ, b γ)

noncomputable def fstTm {Γ : Ctx} {A B : Ty Γ}
    (t : Tm Γ (ProdTy A B)) : Tm Γ A :=
  fun γ => (t γ).1

noncomputable def sndTm {Γ : Ctx} {A B : Ty Γ}
    (t : Tm Γ (ProdTy A B)) : Tm Γ B :=
  fun γ => (t γ).2

theorem fstTm_pairTm {Γ : Ctx} {A B : Ty Γ} (a : Tm Γ A) (b : Tm Γ B) :
    fstTm (pairTm a b) = a := rfl

theorem sndTm_pairTm {Γ : Ctx} {A B : Ty Γ} (a : Tm Γ A) (b : Tm Γ B) :
    sndTm (pairTm a b) = b := rfl

theorem pairTm_eta {Γ : Ctx} {A B : Ty Γ} (t : Tm Γ (ProdTy A B)) :
    pairTm (fstTm t) (sndTm t) = t := rfl

theorem prodTy_subst {Γ Δ : Ctx} {A B : Ty Γ} (σ : Sub Δ Γ) :
    tySub (ProdTy A B) σ = ProdTy (tySub A σ) (tySub B σ) := rfl

/-! ## CongrArg coherences through CwF -/

noncomputable def congrArg_trans_path {Γ : Ctx} {A B : Ty Γ}
    (f : (γ : Γ) → A γ → B γ)
    {a b c : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (γ : Γ) :
    Path (Path.congrArg (f γ) (Path.trans (p γ) (q γ)))
         (Path.trans (Path.congrArg (f γ) (p γ)) (Path.congrArg (f γ) (q γ))) := by
  simp [Path.congrArg, Path.trans]; exact Path.stepChain (by simp)

noncomputable def congrArg_refl_path {Γ : Ctx} {A B : Ty Γ}
    (f : (γ : Γ) → A γ → B γ) (a : Tm Γ A) (γ : Γ) :
    Path (Path.congrArg (f γ) (Path.refl (a γ))) (Path.refl (f γ (a γ))) := by
  simp [Path.congrArg, Path.refl]; exact Path.refl _

end ComputationalPaths.CwF
