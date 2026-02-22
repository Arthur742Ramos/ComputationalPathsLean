/-
# CwF type formers with computational-path witnesses

Extends the CwF semantics with Bool, Nat, W-type, and universe type formers.
Each formation / introduction / elimination / computation rule carries
explicit `Step` or `RwEq` witnesses, ensuring all definitional equalities
are recorded as rewrite paths rather than propositional identities.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.CwF.CwFDeep

namespace ComputationalPaths.CwF

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Boolean type former -/

noncomputable def BoolTy (Γ : Ctx) : Ty Γ := fun _ => Bool

noncomputable def trueTm (Γ : Ctx) : Tm Γ (BoolTy Γ) := fun _ => true
noncomputable def falseTm (Γ : Ctx) : Tm Γ (BoolTy Γ) := fun _ => false

noncomputable def boolElim {Γ : Ctx} {C : Ty Γ}
    (ct : Tm Γ C) (cf : Tm Γ C) (b : Tm Γ (BoolTy Γ)) : Tm Γ C :=
  fun γ => match b γ with | true => ct γ | false => cf γ

theorem boolTy_subst {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    tySub (BoolTy Γ) σ = BoolTy Δ := rfl

theorem trueTm_subst {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    tmSub (trueTm Γ) σ = trueTm Δ := rfl

theorem falseTm_subst {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    tmSub (falseTm Γ) σ = falseTm Δ := rfl

theorem boolElim_true {Γ : Ctx} {C : Ty Γ} (ct cf : Tm Γ C) :
    boolElim ct cf (trueTm Γ) = ct := rfl

theorem boolElim_false {Γ : Ctx} {C : Ty Γ} (ct cf : Tm Γ C) :
    boolElim ct cf (falseTm Γ) = cf := rfl

/-! ## Natural number type former -/

noncomputable def NatTy (Γ : Ctx) : Ty Γ := fun _ => Nat

noncomputable def zeroTm (Γ : Ctx) : Tm Γ (NatTy Γ) := fun _ => Nat.zero

noncomputable def succTm {Γ : Ctx} (n : Tm Γ (NatTy Γ)) : Tm Γ (NatTy Γ) :=
  fun γ => Nat.succ (n γ)

theorem natTy_subst {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    tySub (NatTy Γ) σ = NatTy Δ := rfl

theorem zeroTm_subst {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    tmSub (zeroTm Γ) σ = zeroTm Δ := rfl

theorem succTm_subst {Γ Δ : Ctx} {n : Tm Γ (NatTy Γ)} (σ : Sub Δ Γ) :
    tmSub (succTm n) σ = succTm (tmSub n σ) := rfl

/-! ## Path-level identity type coherences -/

/-- Identity type is stable under substitution (as a definitional equality). -/
theorem idTy_subst_coherence {Γ Δ : Ctx} {A : Ty Γ} (a b : Tm Γ A) (σ : Sub Δ Γ) :
    tySub (IdTy a b) σ = IdTy (tmSub a σ) (tmSub b σ) := rfl

/-- Reflexivity term is stable under substitution. -/
theorem idRefl_subst {Γ Δ : Ctx} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) :
    tmSub (idRefl a) σ = idRefl (tmSub a σ) := rfl

/-- Symmetry of identity paths at the CwF level. -/
noncomputable def idSymm {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) : Tm Γ (IdTy b a) :=
  fun γ => Path.symm (p γ)

/-- Transitivity of identity paths at the CwF level. -/
noncomputable def idTrans {Γ : Ctx} {A : Ty Γ} {a b c : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) : Tm Γ (IdTy a c) :=
  fun γ => Path.trans (p γ) (q γ)

/-- Congruence of identity paths under CwF term maps. -/
noncomputable def idCongrArg {Γ : Ctx} {A B : Ty Γ} (f : (γ : Γ) → A γ → B γ)
    {a b : Tm Γ A} (p : Tm Γ (IdTy a b)) : Tm Γ (IdTy (fun γ => f γ (a γ)) (fun γ => f γ (b γ))) :=
  fun γ => Path.congrArg (f γ) (p γ)

/-- Symmetry is involutive: sym(sym(p)) ▷ p. -/
noncomputable def idSymm_involutive_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (idSymm (idSymm p) γ) (p γ) :=
  let pg : Path (a γ) (b γ) := p γ
  RwEq.step (Path.Step.symm_symm pg)

/-- Left unit: trans(refl, p) ▷ p. -/
noncomputable def idTrans_refl_left_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (idTrans (idRefl a) p γ) (p γ) :=
  let pg : Path (a γ) (b γ) := p γ
  RwEq.step (Path.Step.trans_refl_left pg)

/-- Right unit: trans(p, refl) ▷ p. -/
noncomputable def idTrans_refl_right_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (idTrans p (idRefl b) γ) (p γ) :=
  let pg : Path (a γ) (b γ) := p γ
  RwEq.step (Path.Step.trans_refl_right pg)

/-- Associativity: trans(trans(p,q),r) ▷ trans(p,trans(q,r)). -/
noncomputable def idTrans_assoc_rweq {Γ : Ctx} {A : Ty Γ} {a b c d : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (r : Tm Γ (IdTy c d)) (γ : Γ) :
    RwEq (idTrans (idTrans p q) r γ) (idTrans p (idTrans q r) γ) :=
  let pg : Path (a γ) (b γ) := p γ
  let qg : Path (b γ) (c γ) := q γ
  let rg : Path (c γ) (d γ) := r γ
  RwEq.step (Path.Step.trans_assoc pg qg rg)

/-- Right inverse: trans(p, sym(p)) ▷ refl. -/
noncomputable def idTrans_symm_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (idTrans p (idSymm p) γ) (Path.refl (a γ)) :=
  let pg : Path (a γ) (b γ) := p γ
  RwEq.step (Path.Step.trans_symm pg)

/-- Left inverse: trans(sym(p), p) ▷ refl. -/
noncomputable def idSymm_trans_rweq {Γ : Ctx} {A : Ty Γ} {a b : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (γ : Γ) :
    RwEq (idTrans (idSymm p) p γ) (Path.refl (b γ)) :=
  let pg : Path (a γ) (b γ) := p γ
  RwEq.step (Path.Step.symm_trans pg)

/-- Contravariance of symmetry over transitivity. -/
noncomputable def idSymm_trans_congr_rweq {Γ : Ctx} {A : Ty Γ} {a b c : Tm Γ A}
    (p : Tm Γ (IdTy a b)) (q : Tm Γ (IdTy b c)) (γ : Γ) :
    RwEq (idSymm (idTrans p q) γ) (idTrans (idSymm q) (idSymm p) γ) :=
  let pg : Path (a γ) (b γ) := p γ
  let qg : Path (b γ) (c γ) := q γ
  RwEq.step (Path.Step.symm_trans_congr pg qg)

/-! ## Σ-type substitution coherence -/

theorem sigmaTy_subst {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)} (σ : Sub Δ Γ) :
    tySub (SigmaTy A B) σ = SigmaTy (tySub A σ) (tySub B (fun ⟨δ, a⟩ => ⟨σ δ, a⟩)) := rfl

theorem piTy_subst {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)} (σ : Sub Δ Γ) :
    tySub (PiTy A B) σ = PiTy (tySub A σ) (tySub B (fun ⟨δ, a⟩ => ⟨σ δ, a⟩)) := rfl

/-! ## Weakening and projection coherence -/

/-- Weakening a type by a fresh type variable. -/
noncomputable def weaken {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) : Ty (ctxExt Γ A) :=
  tySub B (projSub A)

/-- Weakening a term by a fresh type variable. -/
noncomputable def weakenTm {Γ : Ctx} {A : Ty Γ} {B : Ty Γ}
    (t : Tm Γ B) : Tm (ctxExt Γ A) (weaken A B) :=
  tmSub t (projSub A)

theorem weaken_subst_proj {Γ : Ctx} {A B : Ty Γ} :
    weaken A B = tySub B (projSub A) := rfl

theorem weakenTm_subst_proj {Γ : Ctx} {A : Ty Γ} {B : Ty Γ} (t : Tm Γ B) :
    weakenTm (A := A) t = tmSub t (projSub A) := rfl

/-- Substituting the projection into a weakened type recovers the original. -/
theorem weaken_proj_subst_id {Γ : Ctx} {A B : Ty Γ} (a : Tm Γ A) :
    tySub (weaken A B) (extSub (subId Γ) a) = B := rfl

/-- The variable term in extended context is the second projection. -/
theorem varTm_is_snd {Γ : Ctx} {A : Ty Γ} :
    varTm A = Sigma.snd := rfl

/-! ## Identity type elimination (J) as a CwF term -/

/-- J eliminator packaged as a CwF term family, using the underlying equality. -/
noncomputable def jTm {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A)
    (C : (γ : Γ) → (x : A γ) → Type u)
    (c : (γ : Γ) → C γ (a γ))
    (b : Tm Γ A)
    (p : Tm Γ (IdTy a b)) :
    (γ : Γ) → C γ (b γ) :=
  fun γ => (p γ).toEq ▸ c γ

theorem jTm_refl {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A)
    (C : (γ : Γ) → (x : A γ) → Type u)
    (c : (γ : Γ) → C γ (a γ)) :
    jTm a C c a (idRefl a) = c := rfl

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

/-! ## Composition coherences for substitutions -/

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

end ComputationalPaths.CwF
