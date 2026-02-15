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

/-- 1. tySubst preserves identity substitution. -/
theorem tySubst_id {Γ : Ctx} (A : Ty Γ) :
    tySubst A (idSub Γ) = A := rfl

/-- 2. tySubst distributes over composition. -/
theorem tySubst_comp {Γ Δ Θ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tySubst A (compSub σ τ) = tySubst (tySubst A σ) τ := rfl

/-- 3. tmSubst preserves identity. -/
theorem tmSubst_id {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) :
    tmSubst t (idSub Γ) = t := rfl

/-- 4. tmSubst distributes over composition. -/
theorem tmSubst_comp {Γ Δ Θ : Ctx} {A : Ty Γ} (t : Tm Γ A)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tmSubst t (compSub σ τ) = tmSubst (tmSubst t σ) τ := rfl

/-- 5. compSub is associative. -/
theorem compSub_assoc {Γ Δ Θ Ξ : Ctx}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ρ : Sub Ξ Θ) :
    compSub σ (compSub τ ρ) = compSub (compSub σ τ) ρ := rfl

/-- 6. Left identity for compSub. -/
theorem compSub_id_left {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    compSub (idSub Γ) σ = σ := rfl

/-- 7. Right identity for compSub. -/
theorem compSub_id_right {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    compSub σ (idSub Δ) = σ := rfl

/-! ## Context comprehension -/

def ctxExt (Γ : Ctx) (A : Ty Γ) : Ctx := (γ : Γ) × A γ

def projSub {Γ : Ctx} (A : Ty Γ) : Sub (ctxExt Γ A) Γ := Sigma.fst

def varTm {Γ : Ctx} (A : Ty Γ) : Tm (ctxExt Γ A) (tySubst A (projSub A)) :=
  Sigma.snd

def extPair {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    Sub Δ (ctxExt Γ A) :=
  fun δ => ⟨σ δ, t δ⟩

/-- 8. Projection after pairing recovers the substitution. -/
theorem proj_extPair {Γ Δ : Ctx} {A : Ty Γ}
    (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    compSub (projSub A) (extPair σ t) = σ := rfl

/-- 9. Variable after pairing recovers the term. -/
theorem var_extPair {Γ Δ : Ctx} {A : Ty Γ}
    (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    tmSubst (varTm A) (extPair σ t) = t := rfl

/-- 10. Surjective pairing (η for comprehension). -/
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

/-- 11. Weakened type unfolds to substitution along projection. -/
theorem wk_ty_unfold {Γ : Ctx} (A B : Ty Γ) :
    wkTy A B = tySubst B (projSub A) := rfl

/-- 12. Weakened term unfolds to substitution along projection. -/
theorem wk_tm_unfold {Γ : Ctx} {B : Ty Γ} (A : Ty Γ) (t : Tm Γ B) :
    wkTm A t = tmSubst t (projSub A) := rfl

/-! ## Transport-based substitution with paths -/

/-- 13. Transport along a path in the context yields substitution. -/
theorem transport_is_subst {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := A) p x = transport (D := fun X => X) (congrArg A p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 14. Transport along a path chain via trans decomposes. -/
theorem transport_chain {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (x : A γ₁) :
    transport (D := A) (trans p q) x =
      transport (D := A) q (transport (D := A) p x) :=
  transport_trans p q x

/-- 15. Transport along symm ∘ path cancels (left). -/
theorem transport_cancel_left {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := A) (symm p) (transport (D := A) p x) = x :=
  transport_symm_left p x

/-- 16. Transport along path ∘ symm cancels (right). -/
theorem transport_cancel_right {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (y : A γ₂) :
    transport (D := A) p (transport (D := A) (symm p) y) = y :=
  transport_symm_right p y

/-- 17. Triple transport decomposes via two-step calc chain. -/
theorem transport_triple {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (x : A γ₁) :
    transport (D := A) (trans (trans p q) r) x =
      transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
  calc transport (D := A) (trans (trans p q) r) x
      = transport (D := A) r (transport (D := A) (trans p q) x) :=
        transport_trans (trans p q) r x
    _ = transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
        rw [transport_trans p q x]

/-- 18. Four-fold transport decomposition via three-step calc. -/
theorem transport_quad {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ γ₅ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄)
    (s : Path γ₄ γ₅) (x : A γ₁) :
    transport (D := A) (trans (trans (trans p q) r) s) x =
      transport (D := A) s (transport (D := A) r
        (transport (D := A) q (transport (D := A) p x))) := by
  calc transport (D := A) (trans (trans (trans p q) r) s) x
      = transport (D := A) s (transport (D := A) (trans (trans p q) r) x) :=
        transport_trans (trans (trans p q) r) s x
    _ = transport (D := A) s (transport (D := A) r
          (transport (D := A) (trans p q) x)) := by
        rw [transport_trans (trans p q) r x]
    _ = transport (D := A) s (transport (D := A) r
          (transport (D := A) q (transport (D := A) p x))) := by
        rw [transport_trans p q x]

/-- 19. Transport roundtrip: four transports cancel pairwise. -/
theorem transport_roundtrip {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (x : A γ₃) :
    transport (D := A) q (transport (D := A) p
      (transport (D := A) (symm p) (transport (D := A) (symm q) x))) = x := by
  calc transport (D := A) q (transport (D := A) p
        (transport (D := A) (symm p) (transport (D := A) (symm q) x)))
      = transport (D := A) q (transport (D := A) (symm q) x) := by
        rw [transport_symm_right p (transport (D := A) (symm q) x)]
    _ = x := transport_symm_right q x

/-- 20. Transport along a congruence path in a nested family. -/
theorem transport_congrArg_nested {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ : Γ}
    (f : Γ → Γ) (p : Path γ₁ γ₂) (x : A (f γ₁)) :
    transport (D := A ∘ f) p x =
      transport (D := A) (congrArg f p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## Σ-type operations -/

def CtxSigma {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => (a : A γ) × B ⟨γ, a⟩

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

/-- 21. Substitution commutes with Σ-formation. -/
theorem sigma_subst {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A))
    (σ : Sub Δ Γ) :
    tySubst (CtxSigma A B) σ =
      fun δ => (a : A (σ δ)) × B ⟨σ δ, a⟩ := rfl

/-- 22. β-rule for Σ first projection. -/
theorem sigma_beta_fst {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    sigmaFst (sigmaPair a b) = a := rfl

/-- 23. β-rule for Σ second projection. -/
theorem sigma_beta_snd {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    sigmaSnd (sigmaPair a b) = b := rfl

/-- 24. η-rule for Σ. -/
theorem sigma_eta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (CtxSigma A B)) :
    sigmaPair (sigmaFst t) (sigmaSnd t) = t := by
  funext γ
  show (⟨(t γ).fst, (t γ).snd⟩ : (a : A γ) × B ⟨γ, a⟩) = t γ
  cases t γ; rfl

/-- 25. Sigma pair is natural in substitution. -/
theorem sigmaPair_natural {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) (σ : Sub Δ Γ) :
    tmSubst (sigmaPair a b) σ =
      (fun δ => (⟨a (σ δ), b (σ δ)⟩ : CtxSigma A B (σ δ))) := rfl

/-! ## Π-type operations -/

def CtxPi {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => (a : A γ) → B ⟨γ, a⟩

def ctxLam {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) : Tm Γ (CtxPi A B) :=
  fun γ a => body ⟨γ, a⟩

def ctxApp {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) (a : Tm Γ A) : Tm Γ (fun γ => B ⟨γ, a γ⟩) :=
  fun γ => f γ (a γ)

/-- 26. Substitution commutes with Π-formation. -/
theorem pi_subst {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A))
    (σ : Sub Δ Γ) :
    tySubst (CtxPi A B) σ =
      fun δ => (a : A (σ δ)) → B ⟨σ δ, a⟩ := rfl

/-- 27. β-rule for Π. -/
theorem pi_beta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) (a : Tm Γ A) :
    ctxApp (ctxLam body) a = (fun γ => body ⟨γ, a γ⟩) := rfl

/-- 28. η-rule for Π. -/
theorem pi_eta {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) :
    ctxLam (fun ⟨γ, a⟩ => f γ a) = f := rfl

/-- 29. Application is natural in substitution. -/
theorem ctxApp_natural {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (CtxPi A B)) (a : Tm Γ A) (σ : Sub Δ Γ) :
    tmSubst (ctxApp f a) σ = (fun δ => f (σ δ) (a (σ δ))) := rfl

/-- 30. Lambda is natural in substitution. -/
theorem ctxLam_natural {Γ Δ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) (σ : Sub Δ Γ) :
    tmSubst (ctxLam body) σ = (fun δ a => body ⟨σ δ, a⟩) := rfl

/-! ## Deep multi-step transport chains -/

/-- 31. Transport along right-associated path chain decomposes. -/
theorem transport_assoc_chain {Γ : Ctx} {A : Ty Γ} {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (x : A γ₁) :
    transport (D := A) (trans p (trans q r)) x =
      transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
  calc transport (D := A) (trans p (trans q r)) x
      = transport (D := A) (trans q r) (transport (D := A) p x) :=
        transport_trans p (trans q r) x
    _ = transport (D := A) r (transport (D := A) q (transport (D := A) p x)) := by
        rw [transport_trans q r (transport (D := A) p x)]

/-- 32. Transport in a constant family is identity. -/
theorem transport_const_family {Γ : Ctx} {B : Type v} {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) (x : B) :
    transport (D := fun _ : Γ => B) p x = x :=
  transport_const p x

/-- 33. CongrArg preserves trans for context morphisms. -/
theorem congrArg_trans_ctx {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) :
    congrArg σ (trans p q) = trans (congrArg σ p) (congrArg σ q) :=
  congrArg_trans σ p q

/-- 34. CongrArg preserves symm for context morphisms. -/
theorem congrArg_symm_ctx {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ : Γ}
    (p : Path γ₁ γ₂) :
    congrArg σ (symm p) = symm (congrArg σ p) :=
  congrArg_symm σ p

/-- 35. Transport along congruence = transport in pullback family. -/
theorem transport_pullback {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ Δ)
    {γ₁ γ₂ : Γ} (p : Path γ₁ γ₂) (x : A (σ γ₁)) :
    transport (D := tySubst A σ) p x =
      transport (D := A) (congrArg σ p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 36. Naturality of substitution: transport then apply = apply then transport. -/
theorem subst_transport_natural {Γ : Ctx} {A B : Ty Γ}
    (f : ∀ γ, A γ → B γ) {γ₁ γ₂ : Γ} (p : Path γ₁ γ₂) (x : A γ₁) :
    transport (D := B) p (f γ₁ x) = f γ₂ (transport (D := A) p x) := by
  cases p with | mk steps proof => cases proof; rfl

/-- 37. Triple congrArg chain: three applications compose. -/
theorem congrArg_triple {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ γ₄ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) :
    congrArg σ (trans (trans p q) r) =
      trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r) := by
  calc congrArg σ (trans (trans p q) r)
      = trans (congrArg σ (trans p q)) (congrArg σ r) :=
        congrArg_trans σ (trans p q) r
    _ = trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r) := by
        rw [congrArg_trans σ p q]

/-- 38. Quadruple congrArg chain. -/
theorem congrArg_quad {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ γ₄ γ₅ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) (r : Path γ₃ γ₄) (s : Path γ₄ γ₅) :
    congrArg σ (trans (trans (trans p q) r) s) =
      trans (trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r))
            (congrArg σ s) := by
  calc congrArg σ (trans (trans (trans p q) r) s)
      = trans (congrArg σ (trans (trans p q) r)) (congrArg σ s) :=
        congrArg_trans σ (trans (trans p q) r) s
    _ = trans (trans (congrArg σ (trans p q)) (congrArg σ r)) (congrArg σ s) := by
        rw [congrArg_trans σ (trans p q) r]
    _ = trans (trans (trans (congrArg σ p) (congrArg σ q)) (congrArg σ r))
              (congrArg σ s) := by
        rw [congrArg_trans σ p q]

/-- 39. congrArg of symm∘trans: anti-homomorphism chain. -/
theorem congrArg_symm_trans {Γ Δ : Ctx} (σ : Sub Γ Δ) {γ₁ γ₂ γ₃ : Γ}
    (p : Path γ₁ γ₂) (q : Path γ₂ γ₃) :
    congrArg σ (symm (trans p q)) =
      trans (symm (congrArg σ q)) (symm (congrArg σ p)) := by
  calc congrArg σ (symm (trans p q))
      = symm (congrArg σ (trans p q)) :=
        congrArg_symm σ (trans p q)
    _ = symm (trans (congrArg σ p) (congrArg σ q)) := by
        rw [congrArg_trans σ p q]
    _ = trans (symm (congrArg σ q)) (symm (congrArg σ p)) :=
        symm_trans (congrArg σ p) (congrArg σ q)

/-! ## Substitution-weakening interaction -/

/-- 40. Substitution along extPair then projection recovers original type. -/
theorem subst_wk_recover {Γ Δ : Ctx} {A B : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) :
    tySubst (wkTy A B) (extPair σ t) = tySubst B σ := rfl

/-- 41. Double substitution identity chain. -/
theorem double_subst_id {Γ Δ Θ : Ctx} {A : Ty Γ}
    (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    tmSubst (tmSubst t σ) τ = tmSubst t (compSub σ τ) := rfl

/-- 42. Weakening-substitution interaction. -/
theorem wk_subst_interaction {Γ Δ : Ctx} {B : Ty Γ} {A : Ty Δ}
    (t : Tm Γ B) (σ : Sub Δ Γ) :
    wkTm A (tmSubst t σ) = tmSubst t (compSub σ (wkSub A)) := rfl

/-- 43. Triple substitution identity via calc. -/
theorem triple_subst {Γ Δ Θ Ξ : Ctx} {A : Ty Γ}
    (t : Tm Γ A) (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ρ : Sub Ξ Θ) :
    tmSubst (tmSubst (tmSubst t σ) τ) ρ =
      tmSubst t (compSub σ (compSub τ ρ)) := by
  calc tmSubst (tmSubst (tmSubst t σ) τ) ρ
      = tmSubst (tmSubst t (compSub σ τ)) ρ := rfl
    _ = tmSubst t (compSub (compSub σ τ) ρ) := rfl
    _ = tmSubst t (compSub σ (compSub τ ρ)) := rfl

/-! ## Identity type as path -/

def CtxId {Γ : Ctx} {A : Ty Γ} (a b : Tm Γ A) : Ty Γ :=
  fun γ => Path (a γ) (b γ)

def ctxRefl {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A) : Tm Γ (CtxId a a) :=
  fun γ => Path.refl (a γ)

/-- 44. Identity type substitution. -/
theorem id_subst {Γ Δ : Ctx} {A : Ty Γ} (a b : Tm Γ A) (σ : Sub Δ Γ) :
    tySubst (CtxId a b) σ = CtxId (tmSubst a σ) (tmSubst b σ) := rfl

/-- 45. Refl is natural in substitution. -/
theorem refl_natural {Γ Δ : Ctx} {A : Ty Γ} (a : Tm Γ A) (σ : Sub Δ Γ) :
    tmSubst (ctxRefl a) σ = ctxRefl (tmSubst a σ) := rfl

/-! ## J-eliminator -/

/-- 46. J-eliminator: given a motive over paths and a case for refl,
    eliminate any path via the underlying equality. -/
def ctxJ {Γ : Ctx} {A : Ty Γ} {a : Tm Γ A}
    (C : ∀ γ, ∀ b : A γ, a γ = b → Type w)
    (d : ∀ γ, C γ (a γ) rfl)
    (b : Tm Γ A) (p : ∀ γ, a γ = b γ) :
    ∀ γ, C γ (b γ) (p γ) := by
  intro γ; cases p γ; exact d γ

/-- 47. J computes on refl (computation rule). -/
theorem ctxJ_refl {Γ : Ctx} {A : Ty Γ} {a : Tm Γ A}
    (C : ∀ γ, ∀ b : A γ, a γ = b → Type w)
    (d : ∀ γ, C γ (a γ) rfl) (γ : Γ) :
    ctxJ C d a (fun _ => rfl) γ = d γ := rfl

/-! ## Transport coherence with comprehension -/

/-- 48. Transport in the extended context decomposes via projection. -/
theorem transport_ext_proj {Γ : Ctx} {A B : Ty Γ} {γ₁ γ₂ : Γ}
    {a₁ : A γ₁} {a₂ : A γ₂}
    (p : Path γ₁ γ₂) (ha : transport (D := A) p a₁ = a₂)
    (x : B γ₁) :
    transport (D := B) p x = transport (D := B) p x := rfl

/-- 49. congrArg for projSub extracts the first component. -/
theorem congrArg_projSub {Γ : Ctx} {A : Ty Γ}
    {x y : ctxExt Γ A} (p : Path x y) :
    congrArg (projSub A) p = congrArg Sigma.fst p := rfl

/-- 50. Transport in pullback family along two-step path. -/
theorem transport_pullback_chain {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ Δ)
    {γ₁ γ₂ γ₃ : Γ} (p : Path γ₁ γ₂) (q : Path γ₂ γ₃)
    (x : A (σ γ₁)) :
    transport (D := tySubst A σ) (trans p q) x =
      transport (D := A) (trans (congrArg σ p) (congrArg σ q)) x := by
  calc transport (D := tySubst A σ) (trans p q) x
      = transport (D := A) (congrArg σ (trans p q)) x :=
        transport_pullback σ (trans p q) x
    _ = transport (D := A) (trans (congrArg σ p) (congrArg σ q)) x := by
        rw [congrArg_trans σ p q]

/-- 51. Transport pullback chain with symm. -/
theorem transport_pullback_symm {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ Δ)
    {γ₁ γ₂ : Γ} (p : Path γ₁ γ₂) (x : A (σ γ₂)) :
    transport (D := tySubst A σ) (symm p) x =
      transport (D := A) (symm (congrArg σ p)) x := by
  calc transport (D := tySubst A σ) (symm p) x
      = transport (D := A) (congrArg σ (symm p)) x :=
        transport_pullback σ (symm p) x
    _ = transport (D := A) (symm (congrArg σ p)) x := by
        rw [congrArg_symm σ p]

/-- 52. Full roundtrip in pullback family: three-step calc chain. -/
theorem transport_pullback_roundtrip {Γ Δ : Ctx} {A : Ty Δ}
    (σ : Sub Γ Δ) {γ₁ γ₂ : Γ} (p : Path γ₁ γ₂) (x : A (σ γ₁)) :
    transport (D := tySubst A σ) (symm p)
      (transport (D := tySubst A σ) p x) = x := by
  calc transport (D := tySubst A σ) (symm p)
        (transport (D := tySubst A σ) p x)
      = transport (D := A) (congrArg σ (symm p))
          (transport (D := A) (congrArg σ p) x) := by
        rw [transport_pullback σ (symm p), transport_pullback σ p]
    _ = transport (D := A) (symm (congrArg σ p))
          (transport (D := A) (congrArg σ p) x) := by
        rw [congrArg_symm σ p]
    _ = x := transport_symm_left (congrArg σ p) x

/-! ## Substitution calculus deeper properties -/

/-- 53. Four-fold substitution composition. -/
theorem compSub_four {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ : Ctx}
    (σ : Sub Γ₂ Γ₁) (τ : Sub Γ₃ Γ₂)
    (ρ : Sub Γ₄ Γ₃) (μ : Sub Γ₅ Γ₄) :
    compSub σ (compSub τ (compSub ρ μ)) =
      compSub (compSub (compSub σ τ) ρ) μ := rfl

/-- 54. ExtPair is natural in substitution: pairing commutes with composition. -/
theorem extPair_natural {Γ Δ Θ : Ctx} {A : Ty Γ}
    (σ : Sub Δ Γ) (t : Tm Δ (tySubst A σ)) (τ : Sub Θ Δ) :
    compSub (extPair σ t) τ = extPair (compSub σ τ) (tmSubst t τ) := rfl

/-- 55. congrArg composition for substitutions: two-step chain. -/
theorem congrArg_comp_sub {Γ Δ Θ : Ctx} (σ : Sub Δ Γ) (τ : Sub Θ Δ)
    {θ₁ θ₂ : Θ} (p : Path θ₁ θ₂) :
    congrArg (compSub σ τ) p =
      congrArg σ (congrArg τ p) := by
  exact (congrArg_comp σ τ p).symm

end CwFDeep
end TypeTheory
end Path
end ComputationalPaths
