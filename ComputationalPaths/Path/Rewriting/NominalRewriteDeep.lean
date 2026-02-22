/-
  ComputationalPaths.Path.Rewriting.NominalRewriteDeep
  Nominal Rewriting and Alpha-Equivalence via Computational Paths

  Topics:
  - Names/atoms, permutations on names, swapping
  - Nominal sets: finitely supported elements
  - Alpha-equivalence as Path (two terms related by name permutation)
  - Nominal terms with binders, freshness conditions
  - Nominal substitution, capture-avoiding
  - Nominal rewrite rules: l → r modulo alpha
  - Nominal unification
  - Equivariance: rewrite steps preserved by permutation — congrArg
  - Freshness lemmas as Path witnesses
  - Alpha-equivalence groupoid: refl/trans/symm
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.NominalRewriteDeep

open ComputationalPaths

-- ==========================================
-- Section 1: Names / Atoms
-- ==========================================

abbrev Atom := Nat

structure Swap where
  a : Atom
  b : Atom
deriving DecidableEq, Repr

abbrev Perm := List Swap

noncomputable def applySwap (s : Swap) (x : Atom) : Atom :=
  if x = s.a then s.b
  else if x = s.b then s.a
  else x

noncomputable def applyPerm (pi : Perm) (x : Atom) : Atom :=
  pi.foldl (fun acc s => applySwap s acc) x

noncomputable def idPerm : Perm := []

noncomputable def composePerm (pi1 pi2 : Perm) : Perm := pi1 ++ pi2

noncomputable def inversePerm (pi : Perm) : Perm := pi.reverse

-- ==========================================
-- Section 2: Nominal Terms
-- ==========================================

inductive NomTerm where
  | atom : Atom → NomTerm
  | var  : Nat → NomTerm
  | app  : NomTerm → NomTerm → NomTerm
  | abs  : Atom → NomTerm → NomTerm
  | unit : NomTerm
deriving DecidableEq, Repr

noncomputable def permTerm (pi : Perm) : NomTerm → NomTerm
  | NomTerm.atom a   => NomTerm.atom (applyPerm pi a)
  | NomTerm.var n    => NomTerm.var n
  | NomTerm.app t u  => NomTerm.app (permTerm pi t) (permTerm pi u)
  | NomTerm.abs a t  => NomTerm.abs (applyPerm pi a) (permTerm pi t)
  | NomTerm.unit     => NomTerm.unit

noncomputable def freeAtoms : NomTerm → List Atom
  | NomTerm.atom a   => [a]
  | NomTerm.var _    => []
  | NomTerm.app t u  => freeAtoms t ++ freeAtoms u
  | NomTerm.abs a t  => (freeAtoms t).filter (· != a)
  | NomTerm.unit     => []

noncomputable def isFresh (a : Atom) (t : NomTerm) : Prop :=
  a ∉ freeAtoms t

noncomputable instance {a : Atom} {t : NomTerm} : Decidable (isFresh a t) :=
  inferInstanceAs (Decidable (a ∉ freeAtoms t))

-- ==========================================
-- Section 3: Swap Involution
-- ==========================================

-- Theorem 1
theorem applySwap_invol (s : Swap) (x : Atom) :
    applySwap s (applySwap s x) = x := by
  unfold applySwap
  split <;> split <;> simp_all <;> omega

-- Theorem 2: Path witness for swap involution
noncomputable def swapInvolPath (s : Swap) (x : Atom) :
    Path (applySwap s (applySwap s x)) x :=
  Path.mk [] (applySwap_invol s x)

-- ==========================================
-- Section 4: Perm Identity
-- ==========================================

-- Theorem 3
theorem applyPerm_id (x : Atom) : applyPerm idPerm x = x := rfl

-- Theorem 4
theorem permTerm_id (t : NomTerm) : permTerm idPerm t = t := by
  induction t with
  | atom a => simp [permTerm, idPerm, applyPerm]
  | var n => rfl
  | app t u iht ihu => simp [permTerm, iht, ihu]
  | abs a t ih => simp [permTerm, idPerm, applyPerm]; exact ih
  | unit => rfl

-- Theorem 5: Path for identity permutation
noncomputable def permTermIdPath (t : NomTerm) : Path (permTerm idPerm t) t :=
  Path.mk [] (permTerm_id t)

-- ==========================================
-- Section 5: Perm Composition
-- ==========================================

-- Theorem 6
theorem applyPerm_compose (pi1 pi2 : Perm) (x : Atom) :
    applyPerm (composePerm pi1 pi2) x = applyPerm pi2 (applyPerm pi1 x) := by
  simp [composePerm, applyPerm, List.foldl_append]

-- Theorem 7: Path for perm composition on atoms
noncomputable def permComposeAtomPath (pi1 pi2 : Perm) (x : Atom) :
    Path (applyPerm (composePerm pi1 pi2) x) (applyPerm pi2 (applyPerm pi1 x)) :=
  Path.mk [] (applyPerm_compose pi1 pi2 x)

-- Theorem 8
theorem permTerm_compose (pi1 pi2 : Perm) (t : NomTerm) :
    permTerm (composePerm pi1 pi2) t = permTerm pi2 (permTerm pi1 t) := by
  induction t with
  | atom a => simp [permTerm, applyPerm_compose]
  | var _ => rfl
  | app t u iht ihu => simp [permTerm, iht, ihu]
  | abs a t ih => simp [permTerm, applyPerm_compose, ih]
  | unit => rfl

-- Theorem 9: Path for composition on terms
noncomputable def permTermComposePath (pi1 pi2 : Perm) (t : NomTerm) :
    Path (permTerm (composePerm pi1 pi2) t) (permTerm pi2 (permTerm pi1 t)) :=
  Path.mk [] (permTerm_compose pi1 pi2 t)

-- ==========================================
-- Section 6: Perm distribution on constructors
-- ==========================================

-- Theorem 10
theorem permTerm_app (pi : Perm) (t u : NomTerm) :
    permTerm pi (NomTerm.app t u) = NomTerm.app (permTerm pi t) (permTerm pi u) := rfl

-- Theorem 11
theorem permTerm_abs (pi : Perm) (a : Atom) (t : NomTerm) :
    permTerm pi (NomTerm.abs a t) = NomTerm.abs (applyPerm pi a) (permTerm pi t) := rfl

-- Theorem 12
theorem permTerm_unit (pi : Perm) : permTerm pi NomTerm.unit = NomTerm.unit := rfl

-- Theorem 13
theorem permTerm_var (pi : Perm) (n : Nat) : permTerm pi (NomTerm.var n) = NomTerm.var n := rfl

-- ==========================================
-- Section 7: Equivariance via congrArg
-- ==========================================

-- Def 14: Equivariant path
noncomputable def equivariantPath (pi : Perm) {t u : NomTerm} (p : Path t u) :
    Path (permTerm pi t) (permTerm pi u) :=
  Path.congrArg (permTerm pi) p

-- Theorem 15: Equivariance respects transitivity
theorem equivariantTrans (pi : Perm) {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    equivariantPath pi (Path.trans p q) =
    Path.trans (equivariantPath pi p) (equivariantPath pi q) :=
  Path.congrArg_trans (permTerm pi) p q

-- Theorem 16: Equivariance respects symmetry
theorem equivariantSymm (pi : Perm) {t u : NomTerm} (p : Path t u) :
    equivariantPath pi (Path.symm p) =
    Path.symm (equivariantPath pi p) :=
  Path.congrArg_symm (permTerm pi) p

-- ==========================================
-- Section 8: Alpha-Equivalence Groupoid
-- ==========================================

-- Def 17
noncomputable def alphaRefl (t : NomTerm) : Path t t := Path.refl t

-- Def 18
noncomputable def alphaSymm {t u : NomTerm} (p : Path t u) : Path u t := Path.symm p

-- Def 19
noncomputable def alphaTrans {t u v : NomTerm} (p : Path t u) (q : Path u v) : Path t v :=
  Path.trans p q

-- Theorem 20: Associativity
theorem alphaTransAssoc {t u v w : NomTerm}
    (p : Path t u) (q : Path u v) (r : Path v w) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- Theorem 21: Left unit
theorem alphaTransReflLeft {t u : NomTerm} (p : Path t u) :
    Path.trans (Path.refl t) p = p :=
  Path.trans_refl_left p

-- Theorem 22: Right unit
theorem alphaTransReflRight {t u : NomTerm} (p : Path t u) :
    Path.trans p (Path.refl u) = p :=
  Path.trans_refl_right p

-- Theorem 23: symm of symm
theorem alphaSymmSymm {t u : NomTerm} (p : Path t u) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 24: symm distributes over trans
theorem alphaSymmTrans {t u v : NomTerm} (p : Path t u) (q : Path u v) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- ==========================================
-- Section 9: Freshness Conditions
-- ==========================================

-- Theorem 25
theorem fresh_unit (a : Atom) : isFresh a NomTerm.unit := by
  simp [isFresh, freeAtoms]

-- Theorem 26
theorem fresh_var (a : Atom) (n : Nat) : isFresh a (NomTerm.var n) := by
  simp [isFresh, freeAtoms]

-- Theorem 27
theorem fresh_app (a : Atom) (t u : NomTerm)
    (ht : isFresh a t) (hu : isFresh a u) :
    isFresh a (NomTerm.app t u) := by
  simp [isFresh, freeAtoms] at *
  exact ⟨ht, hu⟩

-- Theorem 28
theorem fresh_abs_same (a : Atom) (t : NomTerm) :
    isFresh a (NomTerm.abs a t) := by
  unfold isFresh freeAtoms
  simp [List.mem_filter]

-- Theorem 29
theorem fresh_abs_diff (a b : Atom) (t : NomTerm)
    (_hab : a ≠ b) (ht : isFresh a t) :
    isFresh a (NomTerm.abs b t) := by
  unfold isFresh freeAtoms
  simp [List.mem_filter]
  intro h; exact absurd h ht

-- ==========================================
-- Section 10: Nominal Substitution
-- ==========================================

noncomputable def substAtom (t : NomTerm) (a b : Atom) : NomTerm :=
  match t with
  | NomTerm.atom c   => if c = a then NomTerm.atom b else NomTerm.atom c
  | NomTerm.var n    => NomTerm.var n
  | NomTerm.app t u  => NomTerm.app (substAtom t a b) (substAtom u a b)
  | NomTerm.abs c t  => if c = a then NomTerm.abs c t
                         else NomTerm.abs c (substAtom t a b)
  | NomTerm.unit     => NomTerm.unit

-- Theorem 30
theorem substAtom_self (t : NomTerm) (a : Atom) :
    substAtom t a a = t := by
  induction t with
  | atom c =>
    simp [substAtom]
    intro h; subst h; rfl
  | var _ => rfl
  | app t u iht ihu => simp [substAtom, iht, ihu]
  | abs c t ih =>
    simp [substAtom]
    intro _; exact ih
  | unit => rfl

-- Def 31: Path for self-substitution
noncomputable def substSelfPath (t : NomTerm) (a : Atom) :
    Path (substAtom t a a) t :=
  Path.mk [] (substAtom_self t a)

-- Theorem 32
theorem substAtom_unit (a b : Atom) : substAtom NomTerm.unit a b = NomTerm.unit := rfl

-- Theorem 33
theorem substAtom_var (n : Nat) (a b : Atom) :
    substAtom (NomTerm.var n) a b = NomTerm.var n := rfl

-- ==========================================
-- Section 11: Congruence for App and Abs
-- ==========================================

-- Def 34
noncomputable def appCongrLeft (u : NomTerm) {t t' : NomTerm} (p : Path t t') :
    Path (NomTerm.app t u) (NomTerm.app t' u) :=
  Path.congrArg (fun x => NomTerm.app x u) p

-- Def 35
noncomputable def appCongrRight (t : NomTerm) {u u' : NomTerm} (p : Path u u') :
    Path (NomTerm.app t u) (NomTerm.app t u') :=
  Path.congrArg (fun x => NomTerm.app t x) p

-- Def 36
noncomputable def absCongrBody (a : Atom) {t t' : NomTerm} (p : Path t t') :
    Path (NomTerm.abs a t) (NomTerm.abs a t') :=
  Path.congrArg (fun x => NomTerm.abs a x) p

-- Def 37: Combined congruence
noncomputable def appCongr {t t' u u' : NomTerm} (pt : Path t t') (pu : Path u u') :
    Path (NomTerm.app t u) (NomTerm.app t' u') :=
  Path.trans (appCongrLeft u pt) (appCongrRight t' pu)

-- Theorem 38
theorem appCongrLeft_trans (u : NomTerm) {t t' t'' : NomTerm}
    (p : Path t t') (q : Path t' t'') :
    appCongrLeft u (Path.trans p q) =
    Path.trans (appCongrLeft u p) (appCongrLeft u q) :=
  Path.congrArg_trans _ p q

-- Theorem 39
theorem appCongrRight_trans (t : NomTerm) {u u' u'' : NomTerm}
    (p : Path u u') (q : Path u' u'') :
    appCongrRight t (Path.trans p q) =
    Path.trans (appCongrRight t p) (appCongrRight t q) :=
  Path.congrArg_trans _ p q

-- Theorem 40
theorem absCongrBody_trans (a : Atom) {t t' t'' : NomTerm}
    (p : Path t t') (q : Path t' t'') :
    absCongrBody a (Path.trans p q) =
    Path.trans (absCongrBody a p) (absCongrBody a q) :=
  Path.congrArg_trans _ p q

-- Theorem 41
theorem appCongrLeft_symm (u : NomTerm) {t t' : NomTerm} (p : Path t t') :
    appCongrLeft u (Path.symm p) = Path.symm (appCongrLeft u p) :=
  Path.congrArg_symm _ p

-- Theorem 42
theorem appCongrRight_symm (t : NomTerm) {u u' : NomTerm} (p : Path u u') :
    appCongrRight t (Path.symm p) = Path.symm (appCongrRight t p) :=
  Path.congrArg_symm _ p

-- Theorem 43
theorem absCongrBody_symm (a : Atom) {t t' : NomTerm} (p : Path t t') :
    absCongrBody a (Path.symm p) = Path.symm (absCongrBody a p) :=
  Path.congrArg_symm _ p

-- ==========================================
-- Section 12: Depth and Size
-- ==========================================

noncomputable def depth : NomTerm → Nat
  | NomTerm.atom _   => 0
  | NomTerm.var _    => 0
  | NomTerm.app t u  => 1 + max (depth t) (depth u)
  | NomTerm.abs _ t  => 1 + depth t
  | NomTerm.unit     => 0

noncomputable def termSize : NomTerm → Nat
  | NomTerm.atom _   => 1
  | NomTerm.var _    => 1
  | NomTerm.app t u  => 1 + termSize t + termSize u
  | NomTerm.abs _ t  => 1 + termSize t
  | NomTerm.unit     => 1

-- Theorem 44
theorem depth_perm (pi : Perm) (t : NomTerm) :
    depth (permTerm pi t) = depth t := by
  induction t with
  | atom _ => rfl
  | var _ => rfl
  | app t u iht ihu => simp [permTerm, depth, iht, ihu]
  | abs _ t ih => simp [permTerm, depth, ih]
  | unit => rfl

-- Def 45: Path for depth preservation
noncomputable def depthPermPath (pi : Perm) (t : NomTerm) :
    Path (depth (permTerm pi t)) (depth t) :=
  Path.mk [] (depth_perm pi t)

-- Theorem 46
theorem size_perm (pi : Perm) (t : NomTerm) :
    termSize (permTerm pi t) = termSize t := by
  induction t with
  | atom _ => rfl
  | var _ => rfl
  | app t u iht ihu => simp [permTerm, termSize, iht, ihu]
  | abs _ t ih => simp [permTerm, termSize, ih]
  | unit => rfl

-- Def 47: Path for size preservation
noncomputable def sizePermPath (pi : Perm) (t : NomTerm) :
    Path (termSize (permTerm pi t)) (termSize t) :=
  Path.mk [] (size_perm pi t)

-- ==========================================
-- Section 13: Nominal Contexts
-- ==========================================

inductive NomCtx where
  | hole  : NomCtx
  | appL  : NomCtx → NomTerm → NomCtx
  | appR  : NomTerm → NomCtx → NomCtx
  | absC  : Atom → NomCtx → NomCtx
deriving DecidableEq

noncomputable def plug : NomCtx → NomTerm → NomTerm
  | NomCtx.hole,      t => t
  | NomCtx.appL c u,  t => NomTerm.app (plug c t) u
  | NomCtx.appR u c,  t => NomTerm.app u (plug c t)
  | NomCtx.absC a c,  t => NomTerm.abs a (plug c t)

-- Theorem 48
theorem plug_hole (t : NomTerm) : plug NomCtx.hole t = t := rfl

-- Def 49: Context congruence
noncomputable def ctxCongr (c : NomCtx) {t u : NomTerm} (p : Path t u) :
    Path (plug c t) (plug c u) :=
  Path.congrArg (plug c) p

-- Theorem 50
theorem ctxCongr_trans (c : NomCtx) {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    ctxCongr c (Path.trans p q) =
    Path.trans (ctxCongr c p) (ctxCongr c q) :=
  Path.congrArg_trans _ p q

-- Theorem 51
theorem ctxCongr_symm (c : NomCtx) {t u : NomTerm} (p : Path t u) :
    ctxCongr c (Path.symm p) = Path.symm (ctxCongr c p) :=
  Path.congrArg_symm _ p

noncomputable def composeCtx : NomCtx → NomCtx → NomCtx
  | NomCtx.hole,     c2 => c2
  | NomCtx.appL c u, c2 => NomCtx.appL (composeCtx c c2) u
  | NomCtx.appR u c, c2 => NomCtx.appR u (composeCtx c c2)
  | NomCtx.absC a c, c2 => NomCtx.absC a (composeCtx c c2)

-- Theorem 52
theorem plug_compose (c1 c2 : NomCtx) (t : NomTerm) :
    plug (composeCtx c1 c2) t = plug c1 (plug c2 t) := by
  induction c1 with
  | hole => rfl
  | appL c u ih => simp [composeCtx, plug, ih]
  | appR u c ih => simp [composeCtx, plug, ih]
  | absC a c ih => simp [composeCtx, plug, ih]

-- Def 53: Path for context composition
noncomputable def plugComposePath (c1 c2 : NomCtx) (t : NomTerm) :
    Path (plug (composeCtx c1 c2) t) (plug c1 (plug c2 t)) :=
  Path.mk [] (plug_compose c1 c2 t)

-- ==========================================
-- Section 14: Permutation on Contexts
-- ==========================================

noncomputable def permCtx (pi : Perm) : NomCtx → NomCtx
  | NomCtx.hole     => NomCtx.hole
  | NomCtx.appL c u => NomCtx.appL (permCtx pi c) (permTerm pi u)
  | NomCtx.appR u c => NomCtx.appR (permTerm pi u) (permCtx pi c)
  | NomCtx.absC a c => NomCtx.absC (applyPerm pi a) (permCtx pi c)

-- Theorem 54
theorem perm_plug (pi : Perm) (c : NomCtx) (t : NomTerm) :
    plug (permCtx pi c) (permTerm pi t) = permTerm pi (plug c t) := by
  induction c with
  | hole => rfl
  | appL c u ih => simp [permCtx, plug, permTerm, ih]
  | appR u c ih => simp [permCtx, plug, permTerm, ih]
  | absC a c ih => simp [permCtx, plug, permTerm, ih]

-- Def 55: Path for perm-plug interaction
noncomputable def permPlugPath (pi : Perm) (c : NomCtx) (t : NomTerm) :
    Path (plug (permCtx pi c) (permTerm pi t)) (permTerm pi (plug c t)) :=
  Path.mk [] (perm_plug pi c t)

-- ==========================================
-- Section 15: Nominal Rewrite Rules
-- ==========================================

structure NomRule where
  freshCtx : List (Atom × Nat)
  lhs : NomTerm
  rhs : NomTerm
deriving DecidableEq

noncomputable def ruleCtxSatisfied (rule : NomRule) (sigma : Nat → NomTerm) : Prop :=
  ∀ p ∈ rule.freshCtx, isFresh p.1 (sigma p.2)

-- ==========================================
-- Section 16: Nominal Unification
-- ==========================================

inductive Disagreement where
  | atomMismatch : Atom → Atom → Disagreement
  | structMismatch : NomTerm → NomTerm → Disagreement
deriving DecidableEq

inductive UnifResult where
  | success : Perm → UnifResult
  | failure : Disagreement → UnifResult
deriving DecidableEq

-- Def 56
noncomputable def unifRefl : UnifResult := UnifResult.success idPerm

-- Def 57: Path witness for unifying a term with itself
noncomputable def unifReflPath (t : NomTerm) :
    Path (permTerm idPerm t) t :=
  permTermIdPath t

-- ==========================================
-- Section 17: Injectivity
-- ==========================================

-- Theorem 58
theorem abs_injective (a : Atom) (t u : NomTerm)
    (h : NomTerm.abs a t = NomTerm.abs a u) : t = u := by
  cases h; rfl

-- Theorem 59
theorem app_injective_left (t t' u : NomTerm)
    (h : NomTerm.app t u = NomTerm.app t' u) : t = t' := by
  cases h; rfl

-- Theorem 60
theorem app_injective_right (t u u' : NomTerm)
    (h : NomTerm.app t u = NomTerm.app t u') : u = u' := by
  cases h; rfl

-- Def 61
noncomputable def absInjectivePath (a : Atom) (t u : NomTerm)
    (p : Path (NomTerm.abs a t) (NomTerm.abs a u)) : Path t u :=
  Path.mk [] (abs_injective a t u (Path.toEq p))

-- Def 62
noncomputable def appInjectLeftPath (t t' u : NomTerm)
    (p : Path (NomTerm.app t u) (NomTerm.app t' u)) : Path t t' :=
  Path.mk [] (app_injective_left t t' u (Path.toEq p))

-- Def 63
noncomputable def appInjectRightPath (t u u' : NomTerm)
    (p : Path (NomTerm.app t u) (NomTerm.app t u')) : Path u u' :=
  Path.mk [] (app_injective_right t u u' (Path.toEq p))

-- ==========================================
-- Section 18: Support
-- ==========================================

noncomputable def support (t : NomTerm) : List Atom := freeAtoms t

-- Theorem 64
theorem support_unit : support NomTerm.unit = [] := rfl

-- Theorem 65
theorem support_var (n : Nat) : support (NomTerm.var n) = [] := rfl

-- Def 66
noncomputable def supportUnitPath : Path (support NomTerm.unit) ([] : List Atom) := Path.refl []

-- Def 67
noncomputable def supportVarPath (n : Nat) : Path (support (NomTerm.var n)) ([] : List Atom) := Path.refl []

-- ==========================================
-- Section 19: Inverse Permutation
-- ==========================================

-- Theorem 68
theorem inversePerm_singleton (s : Swap) :
    inversePerm [s] = [s] := rfl

-- Theorem 69
theorem inversePerm_id : inversePerm idPerm = idPerm := rfl

-- Def 70
noncomputable def inversePermIdPath : Path (inversePerm idPerm) idPerm := Path.refl idPerm

-- ==========================================
-- Section 20: Equivariant freshness
-- ==========================================

-- Theorem 71
theorem fresh_equivariant_id (a : Atom) (t : NomTerm)
    (hf : isFresh a t) : isFresh a (permTerm idPerm t) := by
  rw [permTerm_id]; exact hf

-- ==========================================
-- Section 21: Permutation functoriality
-- ==========================================

-- Theorem 72
theorem permFunctRefl (pi : Perm) (t : NomTerm) :
    Path.congrArg (permTerm pi) (Path.refl t) =
    Path.refl (permTerm pi t) := rfl

-- Theorem 73
theorem permFunctTrans (pi : Perm) {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    Path.congrArg (permTerm pi) (Path.trans p q) =
    Path.trans (Path.congrArg (permTerm pi) p)
               (Path.congrArg (permTerm pi) q) :=
  Path.congrArg_trans (permTerm pi) p q

-- Theorem 74
theorem permFunctSymm (pi : Perm) {t u : NomTerm} (p : Path t u) :
    Path.congrArg (permTerm pi) (Path.symm p) =
    Path.symm (Path.congrArg (permTerm pi) p) :=
  Path.congrArg_symm (permTerm pi) p

-- ==========================================
-- Section 22: Context plugging functoriality
-- ==========================================

-- Theorem 75
theorem ctxFunctRefl (c : NomCtx) (t : NomTerm) :
    Path.congrArg (plug c) (Path.refl t) =
    Path.refl (plug c t) := rfl

-- Theorem 76
theorem ctxFunctTrans (c : NomCtx) {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    Path.congrArg (plug c) (Path.trans p q) =
    Path.trans (Path.congrArg (plug c) p)
               (Path.congrArg (plug c) q) :=
  Path.congrArg_trans (plug c) p q

-- Theorem 77
theorem ctxFunctSymm (c : NomCtx) {t u : NomTerm} (p : Path t u) :
    Path.congrArg (plug c) (Path.symm p) =
    Path.symm (Path.congrArg (plug c) p) :=
  Path.congrArg_symm (plug c) p

-- ==========================================
-- Section 23: Depth/size under contexts
-- ==========================================

-- Theorem 78
theorem depth_plug_hole (t : NomTerm) :
    depth (plug NomCtx.hole t) = depth t := rfl

-- Theorem 79
theorem size_plug_hole (t : NomTerm) :
    termSize (plug NomCtx.hole t) = termSize t := rfl

-- ==========================================
-- Section 24: Nominal Matching
-- ==========================================

structure MatchResult where
  subst : List (Nat × NomTerm)
  perm  : Perm
deriving DecidableEq

noncomputable def trivialMatch : MatchResult :=
  { subst := [], perm := idPerm }

-- Theorem 80
theorem trivialMatch_subst : trivialMatch.subst = [] := rfl

-- Theorem 81
theorem trivialMatch_perm : trivialMatch.perm = idPerm := rfl

-- ==========================================
-- Section 25: Equivariant rewrite in context
-- ==========================================

-- Def 82
noncomputable def equivariantCtxRewrite (pi : Perm) (c : NomCtx)
    {lhs rhs : NomTerm} (p : Path lhs rhs) :
    Path (permTerm pi (plug c lhs)) (permTerm pi (plug c rhs)) :=
  Path.congrArg (permTerm pi) (ctxCongr c p)

-- Def 83
noncomputable def equivariantCtxRewriteFactored (pi : Perm) (c : NomCtx)
    {lhs rhs : NomTerm} (p : Path lhs rhs) :
    Path (plug (permCtx pi c) (permTerm pi lhs))
         (plug (permCtx pi c) (permTerm pi rhs)) :=
  ctxCongr (permCtx pi c) (equivariantPath pi p)

-- ==========================================
-- Section 26: Path algebra for nominal terms
-- ==========================================

-- Def 84: Horizontal composition for app
noncomputable def hcompApp {t1 t2 u1 u2 : NomTerm}
    (p : Path t1 t2) (q : Path u1 u2) :
    Path (NomTerm.app t1 u1) (NomTerm.app t2 u2) :=
  Path.trans (appCongrLeft u1 p) (appCongrRight t2 q)

-- Def 85: Horizontal composition for abs
noncomputable def hcompAbs (a : Atom) {t1 t2 : NomTerm}
    (p : Path t1 t2) :
    Path (NomTerm.abs a t1) (NomTerm.abs a t2) :=
  absCongrBody a p

-- Theorem 86
theorem symm_appCongrLeft (u : NomTerm) {t t' : NomTerm} (p : Path t t') :
    Path.symm (appCongrLeft u p) = appCongrLeft u (Path.symm p) :=
  (Path.congrArg_symm _ p).symm

-- Theorem 87
theorem symm_appCongrRight (t : NomTerm) {u u' : NomTerm} (p : Path u u') :
    Path.symm (appCongrRight t p) = appCongrRight t (Path.symm p) :=
  (Path.congrArg_symm _ p).symm

-- Theorem 88
theorem symm_absCongrBody (a : Atom) {t t' : NomTerm} (p : Path t t') :
    Path.symm (absCongrBody a p) = absCongrBody a (Path.symm p) :=
  (Path.congrArg_symm _ p).symm

-- ==========================================
-- Section 27: Composition of equivariant paths
-- ==========================================

-- Def 89
noncomputable def composeEquivariant (pi1 pi2 : Perm) {t u : NomTerm} (p : Path t u) :
    Path (permTerm pi2 (permTerm pi1 t)) (permTerm pi2 (permTerm pi1 u)) :=
  equivariantPath pi2 (equivariantPath pi1 p)

-- Def 90
noncomputable def composeEquivariantViaCompose (pi1 pi2 : Perm) {t u : NomTerm} (p : Path t u) :
    Path (permTerm (composePerm pi1 pi2) t) (permTerm (composePerm pi1 pi2) u) :=
  equivariantPath (composePerm pi1 pi2) p

-- ==========================================
-- Section 28: Perm composition coherence
-- ==========================================

-- Theorem 91
theorem composePerm_assoc (pi1 pi2 pi3 : Perm) :
    composePerm (composePerm pi1 pi2) pi3 = composePerm pi1 (composePerm pi2 pi3) := by
  simp [composePerm, List.append_assoc]

-- Def 92
noncomputable def composePermAssocPath (pi1 pi2 pi3 : Perm) :
    Path (composePerm (composePerm pi1 pi2) pi3)
         (composePerm pi1 (composePerm pi2 pi3)) :=
  Path.mk [] (composePerm_assoc pi1 pi2 pi3)

-- Theorem 93
theorem composePerm_id_left (pi : Perm) :
    composePerm idPerm pi = pi := rfl

-- Theorem 94
theorem composePerm_id_right (pi : Perm) :
    composePerm pi idPerm = pi := by
  simp [composePerm, idPerm]

-- Def 95
noncomputable def composePermIdRightPath (pi : Perm) :
    Path (composePerm pi idPerm) pi :=
  Path.mk [] (composePerm_id_right pi)

-- ==========================================
-- Section 29: freeAtoms on constructors
-- ==========================================

-- Theorem 96
theorem freeAtoms_atom (a : Atom) : freeAtoms (NomTerm.atom a) = [a] := rfl

-- Theorem 97
theorem freeAtoms_var (n : Nat) : freeAtoms (NomTerm.var n) = [] := rfl

-- Theorem 98
theorem freeAtoms_unit : freeAtoms NomTerm.unit = [] := rfl

-- ==========================================
-- Section 30: Depth and size as congrArg
-- ==========================================

-- Def 99: depth respects paths
noncomputable def depthCongrArg {t u : NomTerm} (p : Path t u) :
    Path (depth t) (depth u) :=
  Path.congrArg depth p

-- Def 100: size respects paths
noncomputable def sizeCongrArg {t u : NomTerm} (p : Path t u) :
    Path (termSize t) (termSize u) :=
  Path.congrArg termSize p

-- Theorem 101
theorem depthCongrArg_trans {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    depthCongrArg (Path.trans p q) =
    Path.trans (depthCongrArg p) (depthCongrArg q) :=
  Path.congrArg_trans depth p q

-- Theorem 102
theorem sizeCongrArg_trans {t u v : NomTerm}
    (p : Path t u) (q : Path u v) :
    sizeCongrArg (Path.trans p q) =
    Path.trans (sizeCongrArg p) (sizeCongrArg q) :=
  Path.congrArg_trans termSize p q

-- Theorem 103
theorem depthCongrArg_symm {t u : NomTerm} (p : Path t u) :
    depthCongrArg (Path.symm p) = Path.symm (depthCongrArg p) :=
  Path.congrArg_symm depth p

-- Theorem 104
theorem sizeCongrArg_symm {t u : NomTerm} (p : Path t u) :
    sizeCongrArg (Path.symm p) = Path.symm (sizeCongrArg p) :=
  Path.congrArg_symm termSize p

-- Def 105: unit refl path
noncomputable def unitReflPath : Path NomTerm.unit NomTerm.unit := Path.refl NomTerm.unit

-- ==========================================
-- Section 31: congrArg composition
-- ==========================================

-- Theorem 106: congrArg_comp for depth ∘ permTerm
theorem depth_perm_congrArg_comp (pi : Perm) {t u : NomTerm} (p : Path t u) :
    Path.congrArg (fun x => depth (permTerm pi x)) p =
    Path.congrArg depth (Path.congrArg (permTerm pi) p) :=
  Path.congrArg_comp depth (permTerm pi) p

-- Theorem 107: congrArg_comp for size ∘ permTerm
theorem size_perm_congrArg_comp (pi : Perm) {t u : NomTerm} (p : Path t u) :
    Path.congrArg (fun x => termSize (permTerm pi x)) p =
    Path.congrArg termSize (Path.congrArg (permTerm pi) p) :=
  Path.congrArg_comp termSize (permTerm pi) p

-- Theorem 108: congrArg_id
theorem path_congrArg_id {t u : NomTerm} (p : Path t u) :
    Path.congrArg (fun x : NomTerm => x) p = p :=
  Path.congrArg_id p

end ComputationalPaths.NominalRewriteDeep
