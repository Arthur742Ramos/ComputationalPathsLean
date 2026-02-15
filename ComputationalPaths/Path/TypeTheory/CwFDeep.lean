/-
# Categories with Families via Computational Paths (Deep)

Contexts as types, substitution as transport, type formers (Σ, Π) as
path operations, comprehension, weakening, and deep substitution lemmas
proved via multi-step trans/symm/congrArg/transport chains.

## References

- Dybjer, "Internal type theory"
- Hofmann, "Syntax and semantics of dependent types"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace CwFDeep

open ComputationalPaths.Path

universe u v w

/-! ## Contexts and Types -/

abbrev Ctx := Type u
abbrev Ty (Γ : Ctx) := Γ → Type v
abbrev Tm (Γ : Ctx) (A : Ty Γ) := (γ : Γ) → A γ
abbrev Sub (Δ Γ : Ctx) := Δ → Γ

/-- Action of substitution on types. -/
def tySubst {Γ Δ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) : Ty Δ :=
  fun δ => A (σ δ)

/-- Action of substitution on terms. -/
def tmSubst {Γ Δ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ) :
    Tm Δ (tySubst A σ) :=
  fun δ => t (σ δ)

def idSub (Γ : Ctx) : Sub Γ Γ := id

def compSub {Γ Δ Θ : Ctx} (σ : Sub Δ Γ) (τ : Sub Θ Δ) : Sub Θ Γ :=
  fun θ => σ (τ θ)

/-- 1. tySubst preserves identity. -/
theorem tySubst_id {Γ : Ctx} (A : Ty Γ) :
    tySubst A (idSub Γ) = A := rfl

/-- 2. tySubst distributes over composition. -/
theorem tySubst_comp {Γ Δ Θ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tySubst A (compSub σ τ) = tySubst (tySubst A σ) τ := rfl

/-- 3. tmSubst preserves identity. -/
theorem tmSubst_id {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) :
    tmSubst t (idSub Γ) = t := rfl

/-- 4. tmSubst distributes over composition. -/
theorem tmSubst_comp {Γ Δ Θ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tmSubst t (compSub σ τ) = tmSubst (tmSubst t σ) τ := rfl

/-! ## Context comprehension -/

def ctxExt (Γ : Ctx) (A : Ty Γ) : Ctx := (γ : Γ) × A γ

def projSub {Γ : Ctx} (A : Ty Γ) : Sub (ctxExt Γ A) Γ := Sigma.fst

def varTm {Γ : Ctx} (A : Ty Γ) : Tm (ctxExt Γ A) (tySubst A (projSub A)) :=
  Sigma.snd

def extPair {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    Sub Δ (ctxExt Γ A) :=
  fun δ => ⟨σ δ, t δ⟩

/-- 5. Projection after pairing. -/
theorem proj_extPair {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    compSub (projSub A) (extPair σ t) = σ := rfl

/-- 6. Variable after pairing. -/
theorem var_extPair {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    tmSubst (varTm A) (extPair σ t) = t := rfl

/-- 7. Surjective pairing (eta for comprehension). -/
theorem extPair_eta {Γ : Ctx} {A : Ty Γ} :
    extPair (projSub A) (varTm A) = idSub (ctxExt Γ A) := by
  funext ⟨_, _⟩; rfl

/-! ## Weakening -/

def wkSub {Γ : Ctx} (A : Ty Γ) : Sub (ctxExt Γ A) Γ := projSub A

def wkTy {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) : Ty (ctxExt Γ A) :=
  tySubst B (wkSub A)

def wkTm {Γ : Ctx} {B : Ty Γ} (A : Ty Γ) (t : Tm Γ B) :
    Tm (ctxExt Γ A) (wkTy A B) :=
  tmSubst t (wkSub A)

/-- 8. Weakening a type composes with projection. -/
theorem wk_ty_comp {Γ : Ctx} (A B : Ty Γ) :
    wkTy A B = tySubst B (projSub A) := rfl

/-! ## Transport-based substitution with paths -/

/-- 9. Transport along a path in the context yields substitution. -/
theorem transport_is_subst {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := A) p x = transport (D := fun X => X) (congrArg A p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 10. Transport along a path chain via trans decomposes. -/
theorem transport_chain {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (x : A γ₁) :
    transport (D := A) (trans p q) x =
      transport (D := A) q (transport (D := A) p x) :=
  transport_trans p q x

/-- 11. Transport along symm ∘ path cancels (left). -/
theorem transport_cancel_left {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := A) (symm p) (transport (D := A) p x) = x :=
  transport_symm_left p x

/-- 12. Transport along path ∘ symm cancels (right). -/
theorem transport_cancel_right {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (y : A γ₂) :
    transport (D := A) p (transport (D := A) (symm p) y) = y :=
  transport_symm_right p y

/-! ## Σ-type operations -/

def CtxSigma {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => (a : A γ) × B ⟨γ, a⟩

/-- 13. Substitution commutes with Σ-formation. -/
theorem sigma_subst {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Sub Δ Γ) :
    tySubst (CtxSigma A B) σ =
      fun δ => (a : A (σ δ)) × B ⟨σ δ, a⟩ := by
  rfl

def sigmaPair {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    Tm Γ (CtxSigma A B) :=
  fun γ => ⟨a γ, b γ⟩

def sigmaFst {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (CtxSigma A B)) : Tm Γ A :=
  fun γ => (t γ).1

def sigmaSnd {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (CtxSigma A B)) : Tm Γ (fun γ => B ⟨γ, (t γ).1⟩) :=
  fun γ => (t γ).2

/-- 14. β-rule for Σ first projection. -/
theorem sigma_beta_fst {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    sigmaFst (sigmaPair a b) = a := rfl

/-- 15. β-rule for Σ second projection. -/
theorem sigma_beta_snd {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    sigmaSnd (sigmaPair a b) = b := rfl

/-- 16. η-rule for Σ. -/
theorem sigma_eta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (CtxSigma A B)) :
    sigmaPair (sigmaFst t) (sigmaSnd t) = t := by
  funext γ
  show (⟨(t γ).fst, (t γ).snd⟩ : (a : A γ) × B ⟨γ, a⟩) = t γ
  cases t γ; rfl

/-! ## Π-type operations -/

def CtxPi {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => (a : A γ) → B ⟨γ, a⟩

/-- 17. Substitution commutes with Π-formation. -/
theorem pi_subst {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Sub Δ Γ) :
    tySubst (CtxPi A B) σ =
      fun δ => (a : A (σ δ)) → B ⟨σ δ, a⟩ := by
  rfl

def ctxLam {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) : Tm Γ (CtxPi A B) :=
  fun γ a => body ⟨γ, a⟩

def ctxApp {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) (a : Tm Γ A) : Tm Γ (fun γ => B ⟨γ, a γ⟩) :=
  fun γ => f γ (a γ)

/-- 18. β-rule for Π. -/
theorem pi_beta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) (a : Tm Γ A) :
    ctxApp (ctxLam body) a = (fun γ => body ⟨γ, a γ⟩) := rfl

/-- 19. η-rule for Π. -/
theorem pi_eta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) :
    ctxLam (fun ⟨γ, a⟩ => f γ a) = f := rfl

/-! ## Deep multi-step transport chains -/

/-- 20. Triple transport decomposes via two-step chain. -/
theorem transport_triple {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (x : A γ₁) :
    transport (D := A) (trans (trans p q) r) x =
      transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
  calc transport (D := A) (trans (trans p q) r) x
      = transport (D := A) r (transport (D := A) (trans p q) x) :=
        transport_trans (trans p q) r x
    _ = transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
        rw [transport_trans p q x]

/-- 21. Four-fold transport decomposition. -/
theorem transport_quad {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ γ₅ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (s : Path γ₄ γ₅) (x : A γ₁) :
    transport (D := A) (trans (trans (trans p q) r) s) x =
      transport (D := A) s (transport (D := A) r (transport (D := A) q (transport (D := A) p x))) := by
  calc transport (D := A) (trans (trans (trans p q) r) s) x
      = transport (D := A) s (transport (D := A) (trans (trans p q) r) x) :=
        transport_trans (trans (trans p q) r) s x
    _ = transport (D := A) s (transport (D := A) r (transport (D := A) (trans p q) x)) := by
        rw [transport_trans (trans p q) r x]
    _ = transport (D := A) s (transport (D := A) r (transport (D := A) q (transport (D := A) p x))) := by
        rw [transport_trans p q x]

/-- 22. Transport along a congruence path in a nested family. -/
theorem transport_congrArg_nested {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (f : Γ → Γ) (p : Path γ₁ γ₂) (x : A (f γ₁)) :
    transport (D := A ∘ f) p x =
      transport (D := A) (congrArg f p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 23. Transport roundtrip: symm q ∘ symm p ∘ p ∘ q = id. -/
theorem transport_roundtrip {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (x : A γ₃) :
    transport (D := A) q (transport (D := A) p
      (transport (D := A) (symm p) (transport (D := A) (symm q) x))) = x := by
  calc transport (D := A) q (transport (D := A) p
        (transport (D := A) (symm p) (transport (D := A) (symm q) x)))
      = transport (D := A) q (transport (D := A) (symm q) x) := by
        rw [transport_symm_right p (transport (D := A) (symm q) x)]
    _ = x := by
        rw [transport_symm_right q x]

/-- 24. Substitution–weakening interaction. -/
theorem subst_wk_interaction {Γ Δ : Ctx} {B : Ty Γ} {A : Ty Δ}
    (t : Tm Γ B) (σ : Sub Δ Γ) :
    wkTm A (tmSubst t σ) = tmSubst t (compSub σ (wkSub A)) := rfl

/-- 25. Double substitution identity chain. -/
theorem double_subst_id {Γ Δ Θ : Ctx} {A : Ty Γ}
    (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tmSubst (tmSubst t σ) τ = tmSubst t (compSub σ τ) := rfl

/-- 26. Transport in a constant family is identity. -/
theorem transport_const_family {Γ : Ctx} {B : Type v} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : B) :
    transport (D := fun _ : Γ => B) p x = x :=
  transport_const p x

/-- 27. Transport along a composite path equals sequential transport (3-step). -/
theorem transport_assoc_chain {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (x : A γ₁) :
    transport (D := A) (trans p (trans q r)) x =
      transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
  calc transport (D := A) (trans p (trans q r)) x
      = transport (D := A) (trans q r) (transport (D := A) p x) :=
        transport_trans p (trans q r) x
    _ = transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
        rw [transport_trans q r (transport (D := A) p x)]

/-- 28. CongrArg preserves trans for context morphisms. -/
theorem congrArg_trans_ctx {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) :
    congrArg σ (trans p q) = trans (congrArg σ p) (congrArg σ q) :=
  congrArg_trans σ p q

/-- 29. CongrArg preserves symm for context morphisms. -/
theorem congrArg_symm_ctx {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) :
    congrArg σ (symm p) = symm (congrArg σ p) :=
  congrArg_symm σ p

/-- 30. Transport along congruence = transport in pullback family. -/
theorem transport_pullback {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ Δ) {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : A (σ γ₁)) :
    transport (D := tySubst A σ) p x =
      transport (D := A) (congrArg σ p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 31. Naturality of substitution: transport then apply = apply then transport. -/
theorem subst_transport_natural {Γ : Ctx} {A B : Ty Γ}
    (f : ∀ γ, A γ → B γ) {γ₁ γ₂ : Γ} (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := B) p (f γ₁ x) = f γ₂ (transport (D := A) p x) := by
  cases p with | mk steps proof => cases proof; rfl

/-- 32. Triple congrArg chain. -/
theorem congrArg_triple {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) :
    congrArg σ (trans (trans p q) r) =
      trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r) := by
  calc congrArg σ (trans (trans p q) r)
      = trans (congrArg σ (trans p q)) (congrArg σ r) :=
        congrArg_trans σ (trans p q) r
    _ = trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r) := by
        rw [congrArg_trans σ p q]

/-- 33. Weakening preserves path structure (same fiber). -/
theorem wk_preserves_path {Γ : Ctx} {A B : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : B γ₁) (a₁ : A γ₁) :
    transport (D := wkTy A B) (Path.ofEq (show (⟨γ₁, a₁⟩ : ctxExt Γ A) = ⟨γ₂, transport (D := A) p a₁⟩ from by
      cases p with | mk s pf => cases pf; rfl)) x =
      transport (D := B) p x := by
  cases p with | mk s pf => cases pf; rfl

/-- 34. Sigma pair construction is natural in substitution. -/
theorem sigmaPair_natural {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) (σ : Sub Δ Γ) :
    tmSubst (sigmaPair a b) σ = (fun δ => (⟨a (σ δ), b (σ δ)⟩ : CtxSigma A B (σ δ))) := rfl

/-- 35. Application is natural in substitution. -/
theorem ctxApp_natural {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) (a : Tm Γ A) (σ : Sub Δ Γ) :
    tmSubst (ctxApp f a) σ = (fun δ => f (σ δ) (a (σ δ))) := rfl

end CwFDeep
end TypeTheory
end Path
end ComputationalPaths
