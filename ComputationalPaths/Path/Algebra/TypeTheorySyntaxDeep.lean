/-
# Type Theory Syntax and Judgmental Equality via Computational Paths

This module develops a deep embedding of a simple type theory (base, arrow,
product, unit types) with its term language, typing judgments, reduction,
and proves metatheoretic properties all witnessed by computational paths.

Key design: since beta-reduction relates syntactically distinct terms
(`app (lam b) s ≠ subst1 s b` as inductive data), paths operate on:
(1) types, contexts, and semantic values where equalities hold definitionally,
(2) type derivations and their coherence properties,
(3) functorial lifting of type/context paths through semantic operations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace TypeTheorySyntaxDeep

open ComputationalPaths.Path

/-! ## Simple Types -/

/-- Simple types: base type, arrow, product, unit. -/
inductive Ty : Type where
  | base : Ty
  | arrow : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  | unit : Ty
  deriving DecidableEq, Repr

/-! ## Contexts -/

abbrev Ctx := List Ty

/-! ## de Bruijn–indexed terms -/

inductive Tm : Nat → Type where
  | var   : Fin n → Tm n
  | app   : Tm n → Tm n → Tm n
  | lam   : Ty → Tm (n + 1) → Tm n
  | pair  : Tm n → Tm n → Tm n
  | fst   : Tm n → Tm n
  | snd   : Tm n → Tm n
  | unit  : Tm n
  deriving DecidableEq, Repr

/-! ## Renaming and Substitution -/

noncomputable def liftRen (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases ⟨0, Nat.zero_lt_succ m⟩ (fun i => (f i).succ)

noncomputable def rename (f : Fin n → Fin m) : Tm n → Tm m
  | .var i     => .var (f i)
  | .app s t   => .app (rename f s) (rename f t)
  | .lam ty b  => .lam ty (rename (liftRen f) b)
  | .pair s t  => .pair (rename f s) (rename f t)
  | .fst t     => .fst (rename f t)
  | .snd t     => .snd (rename f t)
  | .unit      => .unit

noncomputable def shift : Tm n → Tm (n + 1) := rename Fin.castSucc

noncomputable def exts (sigma : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cases (.var ⟨0, Nat.zero_lt_succ m⟩) (fun i => shift (sigma i))

noncomputable def substTm (sigma : Fin n → Tm m) : Tm n → Tm m
  | .var i     => sigma i
  | .app s t   => .app (substTm sigma s) (substTm sigma t)
  | .lam ty b  => .lam ty (substTm (exts sigma) b)
  | .pair s t  => .pair (substTm sigma s) (substTm sigma t)
  | .fst t     => .fst (substTm sigma t)
  | .snd t     => .snd (substTm sigma t)
  | .unit      => .unit

noncomputable def subst1 (s : Tm n) : Tm (n + 1) → Tm n :=
  substTm (Fin.cases s .var)

/-! ## Typing -/

inductive HasType : (Gam : Ctx) → Tm Gam.length → Ty → Prop where
  | var   : (h : Gam.get i = A) → HasType Gam (.var i) A
  | app   : HasType Gam s (Ty.arrow A B) → HasType Gam t A →
            HasType Gam (.app s t) B
  | lam   : HasType (A :: Gam) b B → HasType Gam (.lam A b) (Ty.arrow A B)
  | pair  : HasType Gam s A → HasType Gam t B →
            HasType Gam (.pair s t) (Ty.prod A B)
  | fst   : HasType Gam p (Ty.prod A B) → HasType Gam (.fst p) A
  | snd   : HasType Gam p (Ty.prod A B) → HasType Gam (.snd p) B
  | unit  : HasType Gam .unit .unit

/-! ## Reduction -/

inductive Red1 : Tm n → Tm n → Prop where
  | beta     : Red1 (.app (.lam ty b) s) (subst1 s b)
  | fstBeta  : Red1 (.fst (.pair s t)) s
  | sndBeta  : Red1 (.snd (.pair s t)) t
  | appL     : Red1 s s' → Red1 (.app s t) (.app s' t)
  | appR     : Red1 t t' → Red1 (.app s t) (.app s t')
  | lamBody  : Red1 b b' → Red1 (.lam ty b) (.lam ty b')
  | pairL    : Red1 s s' → Red1 (.pair s t) (.pair s' t)
  | pairR    : Red1 t t' → Red1 (.pair s t) (.pair s t')
  | fstCong  : Red1 t t' → Red1 (.fst t) (.fst t')
  | sndCong  : Red1 t t' → Red1 (.snd t) (.snd t')

/-- Parallel reduction. -/
inductive ParRed : Tm n → Tm n → Prop where
  | var    : ParRed (.var i) (.var i)
  | app    : ParRed s s' → ParRed t t' → ParRed (.app s t) (.app s' t')
  | lam    : ParRed b b' → ParRed (.lam ty b) (.lam ty b')
  | beta   : ParRed b b' → ParRed s s' →
             ParRed (.app (.lam ty b) s) (subst1 s' b')
  | pair   : ParRed s s' → ParRed t t' → ParRed (.pair s t) (.pair s' t')
  | fst    : ParRed t t' → ParRed (.fst t) (.fst t')
  | snd    : ParRed t t' → ParRed (.snd t) (.snd t')
  | fstBeta : ParRed s s' → ParRed t t' → ParRed (.fst (.pair s t)) s'
  | sndBeta : ParRed s s' → ParRed t t' → ParRed (.snd (.pair s t)) t'
  | unit   : ParRed .unit .unit

/-- Normal form predicate. -/
noncomputable def IsNormal (t : Tm n) : Prop := ∀ t', ¬ Red1 t t'

/-! ## Semantic valuation -/

noncomputable def semTy : Ty → Type
  | .base      => Nat
  | .arrow A B => semTy A → semTy B
  | .prod A B  => semTy A × semTy B
  | .unit      => Unit

/-- Size of a term. -/
noncomputable def tmSize : Tm n → Nat
  | .var _     => 1
  | .app s t   => 1 + tmSize s + tmSize t
  | .lam _ b   => 1 + tmSize b
  | .pair s t  => 1 + tmSize s + tmSize t
  | .fst t     => 1 + tmSize t
  | .snd t     => 1 + tmSize t
  | .unit      => 1

/-- Constructor tag. -/
noncomputable def tmTag : Tm n → Nat
  | .var _     => 0
  | .app _ _   => 1
  | .lam _ _   => 2
  | .pair _ _  => 3
  | .fst _     => 4
  | .snd _     => 5
  | .unit      => 6

/-- Simple base-type interpretation. -/
noncomputable def interpBase : Tm n → (Fin n → Nat) → Nat
  | .var i,     env => env i
  | .app s _,   env => interpBase s env
  | .lam _ _,   _   => 0
  | .pair s _,  env => interpBase s env
  | .fst t,     env => interpBase t env
  | .snd t,     env => interpBase t env
  | .unit,      _   => 0

/-- subst1 as a function on the substituted term. -/
noncomputable def subst1_fun (b : Tm (n + 1)) : Tm n → Tm n :=
  fun s => subst1 s b

/-!
## Theorems 1–75

All paths here operate on types, natural numbers, Lean types, and
other domains where propositional equality holds. The point: each
syntactic operation (substitution, weakening, typing, interpretation)
is a *function*, and `congrArg` / `trans` / `symm` lift equalities
through these functions to establish coherence of the metatheory.
-/

-- ═══════════════════════════════════════════════════════════
-- §1. Type-level path operations (Theorems 1–10)
-- ═══════════════════════════════════════════════════════════

-- Theorem 1: Reflexivity for types
noncomputable def ty_refl (A : Ty) : Path A A := Path.refl A

-- Theorem 2: Arrow type congruence in domain
noncomputable def arrow_congL (B : Ty) (p : Path A A') : Path (Ty.arrow A B) (Ty.arrow A' B) :=
  Path.congrArg (fun x => Ty.arrow x B) p

-- Theorem 3: Arrow type congruence in codomain
noncomputable def arrow_congR (A : Ty) (p : Path B B') : Path (Ty.arrow A B) (Ty.arrow A B') :=
  Path.congrArg (Ty.arrow A) p

-- Theorem 4: Full arrow congruence
noncomputable def arrow_cong (pA : Path A A') (pB : Path B B') :
    Path (Ty.arrow A B) (Ty.arrow A' B') :=
  Path.trans (arrow_congL B pA) (arrow_congR A' pB)

-- Theorem 5: Product type congruence in left
noncomputable def prod_congL (B : Ty) (p : Path A A') : Path (Ty.prod A B) (Ty.prod A' B) :=
  Path.congrArg (fun x => Ty.prod x B) p

-- Theorem 6: Product type congruence in right
noncomputable def prod_congR (A : Ty) (p : Path B B') : Path (Ty.prod A B) (Ty.prod A B') :=
  Path.congrArg (Ty.prod A) p

-- Theorem 7: Full product congruence
noncomputable def prod_cong (pA : Path A A') (pB : Path B B') :
    Path (Ty.prod A B) (Ty.prod A' B') :=
  Path.trans (prod_congL B pA) (prod_congR A' pB)

-- Theorem 8: Arrow congruence distributes over trans (domain)
theorem arrow_congL_trans (B : Ty) (p : Path A A') (q : Path A' A'') :
    arrow_congL B (Path.trans p q) =
      Path.trans (arrow_congL B p) (arrow_congL B q) :=
  Path.congrArg_trans (fun x => Ty.arrow x B) p q

-- Theorem 9: Arrow congruence commutes with symm (domain)
theorem arrow_congL_symm (B : Ty) (p : Path A A') :
    arrow_congL B (Path.symm p) = Path.symm (arrow_congL B p) :=
  Path.congrArg_symm (fun x => Ty.arrow x B) p

-- Theorem 10: Product congruence distributes over trans (left)
theorem prod_congL_trans (B : Ty) (p : Path A A') (q : Path A' A'') :
    prod_congL B (Path.trans p q) =
      Path.trans (prod_congL B p) (prod_congL B q) :=
  Path.congrArg_trans (fun x => Ty.prod x B) p q

-- ═══════════════════════════════════════════════════════════
-- §2. Semantic interpretation paths (Theorems 11–20)
-- ═══════════════════════════════════════════════════════════

-- Theorem 11: semTy lifts type paths to type-universe paths
noncomputable def semTy_path (p : Path A B) : Path (semTy A) (semTy B) :=
  Path.congrArg semTy p

-- Theorem 12: semTy distributes over trans
theorem semTy_trans (p : Path A B) (q : Path B C) :
    Path.congrArg semTy (Path.trans p q) =
      Path.trans (Path.congrArg semTy p) (Path.congrArg semTy q) :=
  Path.congrArg_trans semTy p q

-- Theorem 13: semTy commutes with symm
theorem semTy_symm (p : Path A B) :
    Path.congrArg semTy (Path.symm p) =
      Path.symm (Path.congrArg semTy p) :=
  Path.congrArg_symm semTy p

-- Theorem 14: Arrow space path from type paths
noncomputable def arrow_sem_path (pA : Path A A') (pB : Path B B') :
    Path (semTy A → semTy B) (semTy A' → semTy B') :=
  Path.trans
    (Path.congrArg (fun X => X → semTy B) (Path.congrArg semTy pA))
    (Path.congrArg (fun Y => semTy A' → Y) (Path.congrArg semTy pB))

-- Theorem 15: Product space path from type paths
noncomputable def prod_sem_path (pA : Path A A') (pB : Path B B') :
    Path (semTy A × semTy B) (semTy A' × semTy B') :=
  Path.trans
    (Path.congrArg (fun X => X × semTy B) (Path.congrArg semTy pA))
    (Path.congrArg (fun Y => semTy A' × Y) (Path.congrArg semTy pB))

-- Theorem 16: Arrow interpretation is compositional
theorem arrow_sem_comp (pA : Path A A') (pB : Path B B') :
    semTy_path (arrow_cong pA pB) =
      Path.congrArg semTy (Path.trans (arrow_congL B pA) (arrow_congR A' pB)) := by
  rfl

-- Theorem 17: Semantic interpretation of unit
theorem semTy_unit : semTy Ty.unit = Unit := rfl

-- Theorem 18: Semantic interpretation of base
theorem semTy_base : semTy Ty.base = Nat := rfl

-- Theorem 19: semTy on refl is refl
theorem semTy_refl (A : Ty) :
    Path.congrArg semTy (Path.refl A) = Path.refl (semTy A) := by
  simp [Path.congrArg]

-- Theorem 20: Double congrArg: semTy then type-level function
theorem semTy_comp (f : Type → Type) (p : Path A B) :
    Path.congrArg (fun ty => f (semTy ty)) p =
      Path.congrArg f (Path.congrArg semTy p) :=
  Path.congrArg_comp f semTy p

-- ═══════════════════════════════════════════════════════════
-- §3. Term-level congruence paths (Theorems 21–30)
-- ═══════════════════════════════════════════════════════════

-- Theorem 21: App congruence left via congrArg
noncomputable def app_congL (t : Tm n) (p : Path s s') :
    Path (Tm.app s t) (Tm.app s' t) :=
  Path.congrArg (fun f => Tm.app f t) p

-- Theorem 22: App congruence right
noncomputable def app_congR (s : Tm n) (p : Path t t') :
    Path (Tm.app s t) (Tm.app s t') :=
  Path.congrArg (Tm.app s) p

-- Theorem 23: Lambda body congruence
noncomputable def lam_cong (ty : Ty) (p : Path b b') :
    Path (Tm.lam ty b) (Tm.lam ty b') :=
  Path.congrArg (Tm.lam ty) p

-- Theorem 24: Pair left congruence
noncomputable def pair_congL (t : Tm n) (p : Path s s') :
    Path (Tm.pair s t) (Tm.pair s' t) :=
  Path.congrArg (fun x => Tm.pair x t) p

-- Theorem 25: Pair right congruence
noncomputable def pair_congR (s : Tm n) (p : Path t t') :
    Path (Tm.pair s t) (Tm.pair s t') :=
  Path.congrArg (Tm.pair s) p

-- Theorem 26: Full pair congruence
noncomputable def pair_cong (ps : Path s s') (pt : Path t t') :
    Path (Tm.pair s t) (Tm.pair s' t') :=
  Path.trans (pair_congL t ps) (pair_congR s' pt)

-- Theorem 27: Fst congruence
noncomputable def fst_cong (p : Path t t') : Path (Tm.fst t) (Tm.fst t') :=
  Path.congrArg Tm.fst p

-- Theorem 28: Snd congruence
noncomputable def snd_cong (p : Path t t') : Path (Tm.snd t) (Tm.snd t') :=
  Path.congrArg Tm.snd p

-- Theorem 29: Shift (weakening) congruence
noncomputable def shift_cong (p : Path s t) : Path (shift s) (shift t) :=
  Path.congrArg shift p

-- Theorem 30: Substitution congruence
noncomputable def subst1_cong (b : Tm (n + 1)) (p : Path s s') :
    Path (subst1 s b) (subst1 s' b) :=
  Path.congrArg (subst1_fun b) p

-- ═══════════════════════════════════════════════════════════
-- §4. Path algebra laws for term congruences (Theorems 31–45)
-- ═══════════════════════════════════════════════════════════

-- Theorem 31: App-left congruence distributes over trans
theorem appL_trans (t : Tm n) (p : Path s s') (q : Path s' s'') :
    app_congL t (Path.trans p q) =
      Path.trans (app_congL t p) (app_congL t q) :=
  Path.congrArg_trans (fun f => Tm.app f t) p q

-- Theorem 32: App-left congruence commutes with symm
theorem appL_symm (t : Tm n) (p : Path s s') :
    app_congL t (Path.symm p) = Path.symm (app_congL t p) :=
  Path.congrArg_symm (fun f => Tm.app f t) p

-- Theorem 33: App-right congruence distributes over trans
theorem appR_trans (s : Tm n) (p : Path t t') (q : Path t' t'') :
    app_congR s (Path.trans p q) =
      Path.trans (app_congR s p) (app_congR s q) :=
  Path.congrArg_trans (Tm.app s) p q

-- Theorem 34: App-right congruence commutes with symm
theorem appR_symm (s : Tm n) (p : Path t t') :
    app_congR s (Path.symm p) = Path.symm (app_congR s p) :=
  Path.congrArg_symm (Tm.app s) p

-- Theorem 35: Lambda congruence distributes over trans
theorem lam_trans (ty : Ty) (p : Path b b') (q : Path b' b'') :
    lam_cong ty (Path.trans p q) =
      Path.trans (lam_cong ty p) (lam_cong ty q) :=
  Path.congrArg_trans (Tm.lam ty) p q

-- Theorem 36: Lambda congruence commutes with symm
theorem lam_symm (ty : Ty) (p : Path b b') :
    lam_cong ty (Path.symm p) = Path.symm (lam_cong ty p) :=
  Path.congrArg_symm (Tm.lam ty) p

-- Theorem 37: Pair-left congruence distributes over trans
theorem pairL_trans (t : Tm n) (p : Path s s') (q : Path s' s'') :
    pair_congL t (Path.trans p q) =
      Path.trans (pair_congL t p) (pair_congL t q) :=
  Path.congrArg_trans (fun x => Tm.pair x t) p q

-- Theorem 38: Pair-right congruence distributes over trans
theorem pairR_trans (s : Tm n) (p : Path t t') (q : Path t' t'') :
    pair_congR s (Path.trans p q) =
      Path.trans (pair_congR s p) (pair_congR s q) :=
  Path.congrArg_trans (Tm.pair s) p q

-- Theorem 39: Fst congruence distributes over trans
theorem fst_trans (p : Path s t) (q : Path t u) :
    fst_cong (Path.trans p q) = Path.trans (fst_cong p) (fst_cong q) :=
  Path.congrArg_trans Tm.fst p q

-- Theorem 40: Fst congruence commutes with symm
theorem fst_symm (p : Path s t) :
    fst_cong (Path.symm p) = Path.symm (fst_cong p) :=
  Path.congrArg_symm Tm.fst p

-- Theorem 41: Snd congruence distributes over trans
theorem snd_trans (p : Path s t) (q : Path t u) :
    snd_cong (Path.trans p q) = Path.trans (snd_cong p) (snd_cong q) :=
  Path.congrArg_trans Tm.snd p q

-- Theorem 42: Snd congruence commutes with symm
theorem snd_symm (p : Path s t) :
    snd_cong (Path.symm p) = Path.symm (snd_cong p) :=
  Path.congrArg_symm Tm.snd p

-- Theorem 43: Subst1 congruence distributes over trans
theorem subst1_trans (b : Tm (n + 1)) (p : Path s t) (q : Path t u) :
    Path.trans (subst1_cong b p) (subst1_cong b q) =
      subst1_cong b (Path.trans p q) :=
  (Path.congrArg_trans (subst1_fun b) p q).symm

-- Theorem 44: Subst1 congruence commutes with symm
theorem subst1_symm (b : Tm (n + 1)) (p : Path s t) :
    Path.symm (subst1_cong b p) = subst1_cong b (Path.symm p) :=
  (Path.congrArg_symm (subst1_fun b) p).symm

-- Theorem 45: Shift congruence distributes over trans
theorem shift_trans (p : Path s t) (q : Path t u) :
    shift_cong (Path.trans p q) = Path.trans (shift_cong p) (shift_cong q) :=
  Path.congrArg_trans shift p q

-- ═══════════════════════════════════════════════════════════
-- §5. Interpretation coherence (Theorems 46–55)
-- ═══════════════════════════════════════════════════════════

-- Theorem 46: Interpretation congruence
noncomputable def interp_cong (env : Fin n → Nat) (p : Path s t) :
    Path (interpBase s env) (interpBase t env) :=
  Path.congrArg (fun tm => interpBase tm env) p

-- Theorem 47: Interpretation distributes over trans
theorem interp_trans (env : Fin n → Nat) (p : Path s t) (q : Path t u) :
    Path.congrArg (fun tm => interpBase tm env) (Path.trans p q) =
      Path.trans
        (Path.congrArg (fun tm => interpBase tm env) p)
        (Path.congrArg (fun tm => interpBase tm env) q) :=
  Path.congrArg_trans (fun tm => interpBase tm env) p q

-- Theorem 48: Interpretation distributes over symm
theorem interp_symm (env : Fin n → Nat) (p : Path s t) :
    Path.congrArg (fun tm => interpBase tm env) (Path.symm p) =
      Path.symm (Path.congrArg (fun tm => interpBase tm env) p) :=
  Path.congrArg_symm (fun tm => interpBase tm env) p

-- Theorem 49: Composing interpretation with a function
theorem interp_comp (f : Nat → Nat) (env : Fin n → Nat) (p : Path s t) :
    Path.congrArg (fun tm => f (interpBase tm env)) p =
      Path.congrArg f (Path.congrArg (fun tm => interpBase tm env) p) :=
  Path.congrArg_comp f (fun tm => interpBase tm env) p

-- Theorem 50: Interpretation on refl
theorem interp_refl (env : Fin n → Nat) (t : Tm n) :
    Path.congrArg (fun tm => interpBase tm env) (Path.refl t) =
      Path.refl (interpBase t env) := by
  simp [Path.congrArg]

-- Theorem 51: Size congruence distributes over trans
theorem size_trans (p : Path s t) (q : Path t u) :
    Path.congrArg tmSize (Path.trans p q) =
      Path.trans (Path.congrArg tmSize p) (Path.congrArg tmSize q) :=
  Path.congrArg_trans tmSize p q

-- Theorem 52: Size congruence with symm
theorem size_symm (p : Path s t) :
    Path.congrArg tmSize (Path.symm p) =
      Path.symm (Path.congrArg tmSize p) :=
  Path.congrArg_symm tmSize p

-- Theorem 53: Size + successor composition
theorem size_succ_cong (p : Path s t) :
    Path.congrArg (fun tm => tmSize tm + 1) p =
      Path.congrArg (· + 1) (Path.congrArg tmSize p) :=
  Path.congrArg_comp (· + 1) tmSize p

-- Theorem 54: Tag congruence distributes over trans
theorem tag_trans (p : Path s t) (q : Path t u) :
    Path.congrArg tmTag (Path.trans p q) =
      Path.trans (Path.congrArg tmTag p) (Path.congrArg tmTag q) :=
  Path.congrArg_trans tmTag p q

-- Theorem 55: Tag congruence with symm
theorem tag_symm (p : Path s t) :
    Path.congrArg tmTag (Path.symm p) =
      Path.symm (Path.congrArg tmTag p) :=
  Path.congrArg_symm tmTag p

-- ═══════════════════════════════════════════════════════════
-- §6. General path algebra (Theorems 56–65)
-- ═══════════════════════════════════════════════════════════

-- Theorem 56: Three-fold associativity of trans
theorem path_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- Theorem 57: Left identity
theorem path_trans_refl_left (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

-- Theorem 58: Right identity
theorem path_trans_refl_right (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

-- Theorem 59: symm-trans
theorem path_symm_trans (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- Theorem 60: Double symm
theorem path_symm_symm (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 61: congrArg on id is identity
theorem congrArg_id_eq (p : Path a b) :
    Path.congrArg (fun (x : Ty) => x) p = p :=
  Path.congrArg_id p

-- Theorem 62: congrArg composition law
theorem congrArg_comp_law (f : Ty → Ty) (g : Ty → Ty) (p : Path A B) :
    Path.congrArg (fun x => f (g x)) p =
      Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

-- Theorem 63: Parallel reduction is reflexive
theorem parred_refl : (t : Tm n) → ParRed t t
  | .var _     => .var
  | .app s t   => .app (parred_refl s) (parred_refl t)
  | .lam _ b   => .lam (parred_refl b)
  | .pair s t  => .pair (parred_refl s) (parred_refl t)
  | .fst t     => .fst (parred_refl t)
  | .snd t     => .snd (parred_refl t)
  | .unit      => .unit

-- Theorem 64: One-step reduction implies parallel reduction
theorem red1_parred (h : Red1 s t) : ParRed s t := by
  induction h with
  | beta => exact ParRed.beta (parred_refl _) (parred_refl _)
  | fstBeta => exact ParRed.fstBeta (parred_refl _) (parred_refl _)
  | sndBeta => exact ParRed.sndBeta (parred_refl _) (parred_refl _)
  | appL _ ih => exact ParRed.app ih (parred_refl _)
  | appR _ ih => exact ParRed.app (parred_refl _) ih
  | lamBody _ ih => exact ParRed.lam ih
  | pairL _ ih => exact ParRed.pair ih (parred_refl _)
  | pairR _ ih => exact ParRed.pair (parred_refl _) ih
  | fstCong _ ih => exact ParRed.fst ih
  | sndCong _ ih => exact ParRed.snd ih

-- Theorem 65: Variables are normal
theorem var_normal (i : Fin n) : IsNormal (Tm.var i) := by
  intro t' h; cases h

-- ═══════════════════════════════════════════════════════════
-- §7. Context-level paths and derived coherence (Theorems 66–75)
-- ═══════════════════════════════════════════════════════════

-- Theorem 66: Context lookup congruence
noncomputable def ctx_lookup_cong (Gam : Ctx) {i j : Fin Gam.length} (p : Path i j) :
    Path (Gam.get i) (Gam.get j) :=
  Path.congrArg Gam.get p

-- Theorem 67: Context extension congruence
noncomputable def ctx_cons_cong (Gam : Ctx) (p : Path A B) :
    Path (A :: Gam) (B :: Gam) :=
  Path.congrArg (· :: Gam) p

-- Theorem 68: Context length is preserved by path
noncomputable def ctx_length_cong {Gam1 Gam2 : Ctx} (p : Path Gam1 Gam2) :
    Path (List.length Gam1) (List.length Gam2) :=
  Path.congrArg (fun (g : Ctx) => g.length) p

-- Theorem 69: Cons congruence distributes over trans
theorem ctx_cons_trans (Gam : Ctx) (p : Path A B) (q : Path B C) :
    ctx_cons_cong Gam (Path.trans p q) =
      Path.trans (ctx_cons_cong Gam p) (ctx_cons_cong Gam q) :=
  Path.congrArg_trans (· :: Gam) p q

-- Theorem 70: Cons congruence commutes with symm
theorem ctx_cons_symm (Gam : Ctx) (p : Path A B) :
    ctx_cons_cong Gam (Path.symm p) = Path.symm (ctx_cons_cong Gam p) :=
  Path.congrArg_symm (· :: Gam) p

-- Theorem 71: unit is normal
theorem unit_normal : IsNormal (Tm.unit : Tm n) := by
  intro t' h; cases h

-- Theorem 72: Shift congruence with symm
theorem shift_symm (p : Path s t) :
    shift_cong (Path.symm p) = Path.symm (shift_cong p) :=
  Path.congrArg_symm shift p

-- Theorem 73: Subst1 on refl is refl
theorem subst1_refl (b : Tm (n + 1)) (s : Tm n) :
    subst1_cong b (Path.refl s) = Path.refl (subst1 s b) := by
  simp [subst1_cong, subst1_fun]

-- Theorem 74: Shift then size = size then shift-size (composition)
theorem shift_size_comp (p : Path s t) :
    Path.congrArg (fun tm => tmSize (shift tm)) p =
      Path.congrArg tmSize (Path.congrArg shift p) :=
  Path.congrArg_comp tmSize shift p

-- Theorem 75: Subst then interpretation = composition
theorem subst_interp_comp (b : Tm (n + 1)) (env : Fin n → Nat) (p : Path s t) :
    Path.congrArg (fun s' => interpBase (subst1 s' b) env) p =
      Path.congrArg (fun tm => interpBase tm env) (subst1_cong b p) :=
  Path.congrArg_comp (fun tm => interpBase tm env) (subst1_fun b) p

end TypeTheorySyntaxDeep
end Path
end ComputationalPaths
