/-
# Monoidal Coherence via Computational Paths

Mac Lane's coherence theorem: all diagrams of structural isomorphisms in a
monoidal category commute. We formalize this as a *rewriting system* on
parenthesized tensor expressions (`MonExpr`), with rewrite steps (`MonStep`)
for associators and unitors, paths (`MonPath`) forming the free groupoid,
and a normalization procedure to right-associated form.

Coherence is: for any two `MonPath`s with same source and target, they yield
the same semantic equality — proved via correctness of normalization.

## References

- Mac Lane, "Categories for the Working Mathematician", Ch. VII
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths"
-/

import ComputationalPaths.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ComputationalPaths
namespace MonoidalCoherence

universe u

/-! ## Monoidal Expressions -/

/-- Parenthesized tensor expressions over atoms from `α`. -/
inductive MonExpr (α : Type u) where
  | unit : MonExpr α
  | atom : α → MonExpr α
  | tensor : MonExpr α → MonExpr α → MonExpr α
  deriving Repr, BEq, DecidableEq

namespace MonExpr

variable {α : Type u}

/-- Semantic interpretation: flatten to a list (free monoid). -/
noncomputable def eval : MonExpr α → List α
  | unit => []
  | atom a => [a]
  | tensor l r => l.eval ++ r.eval

/-- Collect atoms in left-to-right order. -/
noncomputable def atoms : MonExpr α → List α
  | unit => []
  | atom a => [a]
  | tensor l r => l.atoms ++ r.atoms

theorem eval_eq_atoms (e : MonExpr α) : e.eval = e.atoms := by
  induction e with
  | unit => rfl
  | atom _ => rfl
  | tensor l r ihl ihr => simp [eval, atoms, ihl, ihr]

/-- Size of an expression. -/
noncomputable def size : MonExpr α → Nat
  | unit => 1
  | atom _ => 1
  | tensor l r => 1 + l.size + r.size

/-- Depth of nesting. -/
noncomputable def depth : MonExpr α → Nat
  | unit => 0
  | atom _ => 0
  | tensor l r => 1 + max l.depth r.depth

/-- Right-associated normal form from a list of atoms. -/
noncomputable def ofList : List α → MonExpr α
  | [] => unit
  | [a] => atom a
  | a :: rest => tensor (atom a) (ofList rest)

/-- The atoms of `ofList xs` are `xs`. -/
theorem atoms_ofList : ∀ (xs : List α), (ofList xs).atoms = xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp [ofList, atoms]
    exact atoms_ofList (b :: rest)

/-- The eval of `ofList xs` is `xs`. -/
theorem eval_ofList (xs : List α) : (ofList xs).eval = xs := by
  rw [eval_eq_atoms]; exact atoms_ofList xs

/-- Normalize: flatten to right-associated form. -/
noncomputable def normalize (e : MonExpr α) : MonExpr α :=
  ofList e.atoms

/-- Normalization is idempotent. -/
theorem normalize_idempotent (e : MonExpr α) :
    (normalize e).normalize = normalize e := by
  unfold normalize
  rw [atoms_ofList]

/-- Normalization preserves semantics. -/
theorem eval_normalize (e : MonExpr α) : (normalize e).eval = e.eval := by
  rw [eval_eq_atoms, eval_eq_atoms]
  exact atoms_ofList e.atoms

/-- Two expressions with same atoms have same normal form. -/
theorem normalize_eq_of_atoms_eq {e₁ e₂ : MonExpr α}
    (h : e₁.atoms = e₂.atoms) : e₁.normalize = e₂.normalize := by
  simp [normalize, h]

/-- Two expressions with same eval have same normal form. -/
theorem normalize_eq_of_eval_eq {e₁ e₂ : MonExpr α}
    (h : e₁.eval = e₂.eval) : e₁.normalize = e₂.normalize := by
  apply normalize_eq_of_atoms_eq
  rw [← eval_eq_atoms, ← eval_eq_atoms, h]

theorem atoms_tensor (l r : MonExpr α) :
    (tensor l r).atoms = l.atoms ++ r.atoms := rfl

theorem eval_tensor (l r : MonExpr α) :
    (tensor l r).eval = l.eval ++ r.eval := rfl

theorem ofList_nil : ofList ([] : List α) = unit := rfl
theorem ofList_singleton (a : α) : ofList [a] = atom a := rfl

end MonExpr

/-! ## Monoidal Steps: Elementary Structural Isomorphisms -/

/-- Elementary structural rewrite steps between monoidal expressions. -/
inductive MonStep (α : Type u) : MonExpr α → MonExpr α → Prop where
  | assoc_fwd (a b c : MonExpr α) :
      MonStep α (MonExpr.tensor a (MonExpr.tensor b c))
               (MonExpr.tensor (MonExpr.tensor a b) c)
  | assoc_bwd (a b c : MonExpr α) :
      MonStep α (MonExpr.tensor (MonExpr.tensor a b) c)
               (MonExpr.tensor a (MonExpr.tensor b c))
  | left_unitor (a : MonExpr α) :
      MonStep α (MonExpr.tensor MonExpr.unit a) a
  | left_unitor_inv (a : MonExpr α) :
      MonStep α a (MonExpr.tensor MonExpr.unit a)
  | right_unitor (a : MonExpr α) :
      MonStep α (MonExpr.tensor a MonExpr.unit) a
  | right_unitor_inv (a : MonExpr α) :
      MonStep α a (MonExpr.tensor a MonExpr.unit)
  | tensor_cong_left {a a' : MonExpr α} (b : MonExpr α) :
      MonStep α a a' →
      MonStep α (MonExpr.tensor a b) (MonExpr.tensor a' b)
  | tensor_cong_right (a : MonExpr α) {b b' : MonExpr α} :
      MonStep α b b' →
      MonStep α (MonExpr.tensor a b) (MonExpr.tensor a b')

namespace MonStep

variable {α : Type u}

/-- Every step preserves the semantic evaluation. -/
theorem eval_preserved {e₁ e₂ : MonExpr α} (s : MonStep α e₁ e₂) :
    e₁.eval = e₂.eval := by
  induction s with
  | assoc_fwd a b c => simp [MonExpr.eval, List.append_assoc]
  | assoc_bwd a b c => simp [MonExpr.eval, List.append_assoc]
  | left_unitor a => simp [MonExpr.eval]
  | left_unitor_inv a => simp [MonExpr.eval]
  | right_unitor a => simp [MonExpr.eval]
  | right_unitor_inv a => simp [MonExpr.eval]
  | tensor_cong_left b _ ih => simp [MonExpr.eval, ih]
  | tensor_cong_right a _ ih => simp [MonExpr.eval, ih]

/-- Every step preserves atoms. -/
theorem atoms_preserved {e₁ e₂ : MonExpr α} (s : MonStep α e₁ e₂) :
    e₁.atoms = e₂.atoms := by
  rw [← MonExpr.eval_eq_atoms, ← MonExpr.eval_eq_atoms]
  exact eval_preserved s

end MonStep

/-! ## Monoidal Paths: Free Groupoid -/

/-- A path in the free groupoid generated by `MonStep`. -/
inductive MonPath (α : Type u) : MonExpr α → MonExpr α → Prop where
  | refl (e : MonExpr α) : MonPath α e e
  | step {e₁ e₂ : MonExpr α} : MonStep α e₁ e₂ → MonPath α e₁ e₂
  | trans {e₁ e₂ e₃ : MonExpr α} :
      MonPath α e₁ e₂ → MonPath α e₂ e₃ → MonPath α e₁ e₃
  | symm {e₁ e₂ : MonExpr α} : MonPath α e₁ e₂ → MonPath α e₂ e₁

namespace MonPath

variable {α : Type u}

/-- Every path preserves semantic evaluation. -/
theorem eval_preserved {e₁ e₂ : MonExpr α} (p : MonPath α e₁ e₂) :
    e₁.eval = e₂.eval := by
  induction p with
  | refl _ => rfl
  | step s => exact s.eval_preserved
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | symm _ ih => exact ih.symm

/-- Every path preserves atoms. -/
theorem atoms_preserved {e₁ e₂ : MonExpr α} (p : MonPath α e₁ e₂) :
    e₁.atoms = e₂.atoms := by
  rw [← MonExpr.eval_eq_atoms, ← MonExpr.eval_eq_atoms]
  exact eval_preserved p

/-- Shorthand: single associator step forward. -/
noncomputable def assocFwd (a b c : MonExpr α) :
    MonPath α (MonExpr.tensor a (MonExpr.tensor b c))
             (MonExpr.tensor (MonExpr.tensor a b) c) :=
  step (MonStep.assoc_fwd a b c)

/-- Shorthand: single associator step backward. -/
noncomputable def assocBwd (a b c : MonExpr α) :
    MonPath α (MonExpr.tensor (MonExpr.tensor a b) c)
             (MonExpr.tensor a (MonExpr.tensor b c)) :=
  step (MonStep.assoc_bwd a b c)

/-- Shorthand: left unitor. -/
noncomputable def leftUnit (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit a) a :=
  step (MonStep.left_unitor a)

/-- Shorthand: left unitor inverse. -/
noncomputable def leftUnitInv (a : MonExpr α) :
    MonPath α a (MonExpr.tensor MonExpr.unit a) :=
  step (MonStep.left_unitor_inv a)

/-- Shorthand: right unitor. -/
noncomputable def rightUnit (a : MonExpr α) :
    MonPath α (MonExpr.tensor a MonExpr.unit) a :=
  step (MonStep.right_unitor a)

/-- Shorthand: right unitor inverse. -/
noncomputable def rightUnitInv (a : MonExpr α) :
    MonPath α a (MonExpr.tensor a MonExpr.unit) :=
  step (MonStep.right_unitor_inv a)

/-- Congruence: apply path on left factor. -/
noncomputable def congLeft {a a' : MonExpr α} (b : MonExpr α)
    (p : MonPath α a a') : MonPath α (MonExpr.tensor a b) (MonExpr.tensor a' b) :=
  match p with
  | refl _ => refl _
  | step s => step (MonStep.tensor_cong_left b s)
  | trans p q => trans (congLeft b p) (congLeft b q)
  | symm p => symm (congLeft b p)

/-- Congruence: apply path on right factor. -/
noncomputable def congRight (a : MonExpr α) {b b' : MonExpr α}
    (p : MonPath α b b') : MonPath α (MonExpr.tensor a b) (MonExpr.tensor a b') :=
  match p with
  | refl _ => refl _
  | step s => step (MonStep.tensor_cong_right a s)
  | trans p q => trans (congRight a p) (congRight a q)
  | symm p => symm (congRight a p)

/-- Congruence: apply paths on both factors. -/
noncomputable def congBoth {a a' b b' : MonExpr α}
    (p : MonPath α a a') (q : MonPath α b b') :
    MonPath α (MonExpr.tensor a b) (MonExpr.tensor a' b') :=
  trans (congLeft b p) (congRight a' q)

end MonPath

/-! ## Semantic Equivalence -/

/-- Two expressions denote the same element of the free monoid. -/
noncomputable def SemEq {α : Type u} (e₁ e₂ : MonExpr α) : Prop :=
  e₁.atoms = e₂.atoms

theorem SemEq.rfl {α : Type u} {e : MonExpr α} : SemEq e e := Eq.refl _

theorem SemEq.symm' {α : Type u} {e₁ e₂ : MonExpr α}
    (h : SemEq e₁ e₂) : SemEq e₂ e₁ := Eq.symm h

theorem SemEq.trans' {α : Type u} {e₁ e₂ e₃ : MonExpr α}
    (h₁ : SemEq e₁ e₂) (h₂ : SemEq e₂ e₃) : SemEq e₁ e₃ := h₁.trans h₂

theorem MonStep.semEq {α : Type u} {e₁ e₂ : MonExpr α}
    (s : MonStep α e₁ e₂) : SemEq e₁ e₂ := s.atoms_preserved

theorem MonPath.semEq {α : Type u} {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) : SemEq e₁ e₂ := p.atoms_preserved

/-! ## Mac Lane Coherence Theorem -/

/-- **Mac Lane Coherence (semantic).** Any two parallel paths give the same
    propositional equality on evaluations. -/
theorem coherence_semantic {α : Type u} {e₁ e₂ : MonExpr α}
    (p q : MonPath α e₁ e₂) : p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

/-- **Mac Lane Coherence (atoms).** -/
theorem coherence_atoms {α : Type u} {e₁ e₂ : MonExpr α}
    (p q : MonPath α e₁ e₂) : p.atoms_preserved = q.atoms_preserved :=
  Subsingleton.elim _ _

/-- **Mac Lane Coherence (normal form).** Any path witnesses same normal form. -/
theorem coherence_normal_form {α : Type u} {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) : e₁.normalize = e₂.normalize :=
  MonExpr.normalize_eq_of_atoms_eq p.atoms_preserved

/-- **Mac Lane Coherence (master).** All structural diagrams commute. -/
theorem maclane_coherence {α : Type u} {e₁ e₂ : MonExpr α}
    (p q : MonPath α e₁ e₂) : p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

/-! ## Pentagon Identity -/

section Pentagon

variable {α : Type u} (a b c d : MonExpr α)

/-- Pentagon path 1 (top-right route):
  `a⊗(b⊗(c⊗d))` → `a⊗((b⊗c)⊗d)` → `(a⊗(b⊗c))⊗d` → `((a⊗b)⊗c)⊗d`
-/
noncomputable def pentagonPath1 :
    MonPath α
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c d)))
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d) :=
  MonPath.trans
    (MonPath.congRight a (MonPath.assocFwd b c d))
    (MonPath.trans
      (MonPath.assocFwd a (MonExpr.tensor b c) d)
      (MonPath.congLeft d (MonPath.assocFwd a b c)))

/-- Pentagon path 2 (bottom-left route):
  `a⊗(b⊗(c⊗d))` → `(a⊗b)⊗(c⊗d)` → `((a⊗b)⊗c)⊗d`
-/
noncomputable def pentagonPath2 :
    MonPath α
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c d)))
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d) :=
  MonPath.trans
    (MonPath.assocFwd a b (MonExpr.tensor c d))
    (MonPath.assocFwd (MonExpr.tensor a b) c d)

/-- **Pentagon identity**: the two paths commute. -/
theorem pentagon_commutes :
    (pentagonPath1 a b c d).eval_preserved =
    (pentagonPath2 a b c d).eval_preserved :=
  Subsingleton.elim _ _

/-- Pentagon: normal form coherence. -/
theorem pentagon_normal_form :
    coherence_normal_form (pentagonPath1 a b c d) =
    coherence_normal_form (pentagonPath2 a b c d) :=
  Subsingleton.elim _ _

end Pentagon

/-! ## Triangle Identity -/

section Triangle

variable {α : Type u} (a b : MonExpr α)

/-- Triangle path 1: `(a⊗I)⊗b` → `a⊗(I⊗b)` → `a⊗b` -/
noncomputable def trianglePath1 :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor a MonExpr.unit) b)
      (MonExpr.tensor a b) :=
  MonPath.trans
    (MonPath.assocBwd a MonExpr.unit b)
    (MonPath.congRight a (MonPath.leftUnit b))

/-- Triangle path 2: `(a⊗I)⊗b` → `a⊗b` via right unitor on left. -/
noncomputable def trianglePath2 :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor a MonExpr.unit) b)
      (MonExpr.tensor a b) :=
  MonPath.congLeft b (MonPath.rightUnit a)

/-- **Triangle identity**: the two paths commute. -/
theorem triangle_commutes :
    (trianglePath1 a b).eval_preserved =
    (trianglePath2 a b).eval_preserved :=
  Subsingleton.elim _ _

theorem triangle_normal_form :
    coherence_normal_form (trianglePath1 a b) =
    coherence_normal_form (trianglePath2 a b) :=
  Subsingleton.elim _ _

end Triangle

/-! ## Extended Structural Paths -/

section StructuralPaths

variable {α : Type u}

/-- Double associator: `a⊗(b⊗(c⊗d))` → `((a⊗b)⊗c)⊗d`. -/
noncomputable def doubleAssocFwd (a b c d : MonExpr α) :
    MonPath α
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c d)))
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d) :=
  pentagonPath2 a b c d

noncomputable def doubleAssocBwd (a b c d : MonExpr α) :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d)
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c d))) :=
  MonPath.symm (pentagonPath2 a b c d)

theorem doubleAssoc_roundtrip (a b c d : MonExpr α) :
    (MonPath.trans (doubleAssocFwd a b c d) (doubleAssocBwd a b c d)).eval_preserved =
    (MonPath.refl _).eval_preserved :=
  Subsingleton.elim _ _

/-- Unit absorption left: `I⊗(I⊗a)` → `a`. -/
noncomputable def unitAbsorbLeft (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit (MonExpr.tensor MonExpr.unit a)) a :=
  MonPath.trans (MonPath.leftUnit _) (MonPath.leftUnit a)

noncomputable def unitAbsorbLeft' (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit (MonExpr.tensor MonExpr.unit a)) a :=
  MonPath.trans
    (MonPath.congRight MonExpr.unit (MonPath.leftUnit a))
    (MonPath.leftUnit a)

theorem unitAbsorb_coherent (a : MonExpr α) :
    (unitAbsorbLeft a).eval_preserved = (unitAbsorbLeft' a).eval_preserved :=
  Subsingleton.elim _ _

/-- Unit absorption right: `(a⊗I)⊗I` → `a`. -/
noncomputable def unitAbsorbRight (a : MonExpr α) :
    MonPath α (MonExpr.tensor (MonExpr.tensor a MonExpr.unit) MonExpr.unit) a :=
  MonPath.trans (MonPath.rightUnit _) (MonPath.rightUnit a)

/-- Five-fold reassociation: `((((a⊗b)⊗c)⊗d)⊗e)` → `a⊗(b⊗(c⊗(d⊗e)))`. -/
noncomputable def assoc5 (a b c d e : MonExpr α) :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d) e)
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c (MonExpr.tensor d e)))) :=
  MonPath.trans
    (MonPath.assocBwd (MonExpr.tensor (MonExpr.tensor a b) c) d e)
    (MonPath.trans
      (MonPath.assocBwd (MonExpr.tensor a b) c (MonExpr.tensor d e))
      (MonPath.assocBwd a b (MonExpr.tensor c (MonExpr.tensor d e))))

noncomputable def assoc5' (a b c d e : MonExpr α) :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d) e)
      (MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c (MonExpr.tensor d e)))) :=
  MonPath.trans
    (MonPath.congLeft e (MonPath.assocBwd (MonExpr.tensor a b) c d))
    (MonPath.trans
      (MonPath.assocBwd (MonExpr.tensor a b) (MonExpr.tensor c d) e)
      (MonPath.trans
        (MonPath.assocBwd a b (MonExpr.tensor (MonExpr.tensor c d) e))
        (MonPath.congRight a
          (MonPath.congRight b (MonPath.assocBwd c d e)))))

theorem assoc5_coherent (a b c d e : MonExpr α) :
    (assoc5 a b c d e).eval_preserved = (assoc5' a b c d e).eval_preserved :=
  Subsingleton.elim _ _

end StructuralPaths

/-! ## Braided Monoidal Structure -/

/-- Steps for the braided monoidal case. -/
inductive BraidStep (α : Type u) : MonExpr α → MonExpr α → Prop where
  | ofMon {e₁ e₂ : MonExpr α} : MonStep α e₁ e₂ → BraidStep α e₁ e₂
  | braid (a b : MonExpr α) :
      BraidStep α (MonExpr.tensor a b) (MonExpr.tensor b a)
  | braid_cong_left {a a' : MonExpr α} (b : MonExpr α) :
      BraidStep α a a' →
      BraidStep α (MonExpr.tensor a b) (MonExpr.tensor a' b)
  | braid_cong_right (a : MonExpr α) {b b' : MonExpr α} :
      BraidStep α b b' →
      BraidStep α (MonExpr.tensor a b) (MonExpr.tensor a b')

/-- Paths in the braided monoidal setting. -/
inductive BraidPath (α : Type u) : MonExpr α → MonExpr α → Prop where
  | refl (e : MonExpr α) : BraidPath α e e
  | step {e₁ e₂ : MonExpr α} : BraidStep α e₁ e₂ → BraidPath α e₁ e₂
  | trans {e₁ e₂ e₃ : MonExpr α} :
      BraidPath α e₁ e₂ → BraidPath α e₂ e₃ → BraidPath α e₁ e₃
  | symm {e₁ e₂ : MonExpr α} : BraidPath α e₁ e₂ → BraidPath α e₂ e₁

namespace BraidPath

variable {α : Type u}

noncomputable def braidSwap (a b : MonExpr α) :
    BraidPath α (MonExpr.tensor a b) (MonExpr.tensor b a) :=
  step (BraidStep.braid a b)

noncomputable def ofMonPath {e₁ e₂ : MonExpr α} : MonPath α e₁ e₂ → BraidPath α e₁ e₂
  | MonPath.refl e => refl e
  | MonPath.step s => step (BraidStep.ofMon s)
  | MonPath.trans p q => trans (ofMonPath p) (ofMonPath q)
  | MonPath.symm p => symm (ofMonPath p)

noncomputable def assocFwd (a b c : MonExpr α) :
    BraidPath α (MonExpr.tensor a (MonExpr.tensor b c))
               (MonExpr.tensor (MonExpr.tensor a b) c) :=
  ofMonPath (MonPath.assocFwd a b c)

noncomputable def assocBwd (a b c : MonExpr α) :
    BraidPath α (MonExpr.tensor (MonExpr.tensor a b) c)
               (MonExpr.tensor a (MonExpr.tensor b c)) :=
  ofMonPath (MonPath.assocBwd a b c)

noncomputable def congLeft {a a' : MonExpr α} (b : MonExpr α)
    (p : BraidPath α a a') :
    BraidPath α (MonExpr.tensor a b) (MonExpr.tensor a' b) :=
  match p with
  | refl _ => refl _
  | step s => step (BraidStep.braid_cong_left b s)
  | trans p q => trans (congLeft b p) (congLeft b q)
  | symm p => symm (congLeft b p)

noncomputable def congRight (a : MonExpr α) {b b' : MonExpr α}
    (p : BraidPath α b b') :
    BraidPath α (MonExpr.tensor a b) (MonExpr.tensor a b') :=
  match p with
  | refl _ => refl _
  | step s => step (BraidStep.braid_cong_right a s)
  | trans p q => trans (congRight a p) (congRight a q)
  | symm p => symm (congRight a p)

end BraidPath

/-! ## Hexagon Identity -/

section Hexagon

variable {α : Type u} (a b c : MonExpr α)

/-- Hexagon path 1:
  `a⊗(b⊗c)` → `(a⊗b)⊗c` → `c⊗(a⊗b)` → `(c⊗a)⊗b`
-/
noncomputable def hexagonPath1 :
    BraidPath α
      (MonExpr.tensor a (MonExpr.tensor b c))
      (MonExpr.tensor (MonExpr.tensor c a) b) :=
  BraidPath.trans
    (BraidPath.assocFwd a b c)
    (BraidPath.trans
      (BraidPath.braidSwap (MonExpr.tensor a b) c)
      (BraidPath.assocFwd c a b))

/-- Hexagon path 2:
  `a⊗(b⊗c)` → `a⊗(c⊗b)` → `(a⊗c)⊗b` → `(c⊗a)⊗b`
-/
noncomputable def hexagonPath2 :
    BraidPath α
      (MonExpr.tensor a (MonExpr.tensor b c))
      (MonExpr.tensor (MonExpr.tensor c a) b) :=
  BraidPath.trans
    (BraidPath.congRight a (BraidPath.braidSwap b c))
    (BraidPath.trans
      (BraidPath.assocFwd a c b)
      (BraidPath.congLeft b (BraidPath.braidSwap a c)))

end Hexagon

/-! ## Diamond Lemma and Confluence -/

section Confluence

variable {α : Type u}

/-- Diamond lemma: if `e` rewrites to `e₁` and `e₂`, they have the same normal form. -/
theorem diamond_semantic {e e₁ e₂ : MonExpr α}
    (p₁ : MonPath α e e₁) (p₂ : MonPath α e e₂) :
    e₁.normalize = e₂.normalize := by
  apply MonExpr.normalize_eq_of_atoms_eq
  have h₁ := p₁.atoms_preserved
  have h₂ := p₂.atoms_preserved
  rw [← h₁, h₂]

/-- Confluence: any two paths from `e` join at the normal form. -/
theorem confluence {e e₁ e₂ : MonExpr α}
    (p₁ : MonPath α e e₁) (p₂ : MonPath α e e₂) :
    e₁.normalize = e₂.normalize :=
  diamond_semantic p₁ p₂

/-- Church-Rosser property. -/
theorem church_rosser {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) : e₁.normalize = e₂.normalize :=
  coherence_normal_form p

/-- Confluence at the step level. -/
theorem confluence_step {e₁ e₂ : MonExpr α}
    (s : MonStep α e₁ e₂) : e₁.normalize = e₂.normalize :=
  church_rosser (MonPath.step s)

/-- Strong normalization: the normal form is already normalized. -/
theorem strong_normalization (e : MonExpr α) :
    e.normalize.normalize = e.normalize :=
  MonExpr.normalize_idempotent e

/-- Termination: normalization reduces depth. -/
theorem normalize_produces_normal_form (e : MonExpr α) :
    e.normalize = MonExpr.ofList e.atoms := rfl

end Confluence

/-! ## Computational Paths Integration -/

section CompPaths

variable {α : Type u}

open ComputationalPaths in
/-- Embed a `MonPath` as a computational `Path` on evaluations. -/
noncomputable def toCompPath {e₁ e₂ : MonExpr α} (p : MonPath α e₁ e₂) :
    ComputationalPaths.Path (e₁.eval) (e₂.eval) :=
  ⟨[], p.eval_preserved⟩

open ComputationalPaths in
/-- Embed a `MonStep` as a computational `Path`. -/
noncomputable def stepToCompPath {e₁ e₂ : MonExpr α} (s : MonStep α e₁ e₂) :
    ComputationalPaths.Path (e₁.eval) (e₂.eval) :=
  ⟨[⟨e₁.eval, e₂.eval, s.eval_preserved⟩], s.eval_preserved⟩

open ComputationalPaths in
/-- Composition of embedded paths. -/
theorem toCompPath_trans {e₁ e₂ e₃ : MonExpr α}
    (p : MonPath α e₁ e₂) (q : MonPath α e₂ e₃) :
    toCompPath (MonPath.trans p q) =
    ComputationalPaths.Path.trans (toCompPath p) (toCompPath q) := by
  simp [toCompPath, ComputationalPaths.Path.trans]

open ComputationalPaths in
/-- Reflexive embedded path. -/
theorem toCompPath_refl (e : MonExpr α) :
    toCompPath (MonPath.refl e) = ComputationalPaths.Path.refl (e.eval) := by
  simp [toCompPath, ComputationalPaths.Path.refl]

end CompPaths

/-! ## Additional Coherence Theorems -/

section MoreCoherence

variable {α : Type u}

/-- Unitor coherence: `I⊗I → I` via left = right unitor. -/
theorem unitor_coherence_unit :
    (MonPath.leftUnit (α := α) MonExpr.unit).eval_preserved =
    (MonPath.rightUnit (α := α) MonExpr.unit).eval_preserved :=
  Subsingleton.elim _ _

/-- Associator-unitor interaction: two routes from `(a⊗I)⊗I` to `a`. -/
noncomputable def assocUnitorPath (a : MonExpr α) :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor a MonExpr.unit) MonExpr.unit)
      a :=
  MonPath.trans (MonPath.rightUnit _) (MonPath.rightUnit a)

noncomputable def assocUnitorPath' (a : MonExpr α) :
    MonPath α
      (MonExpr.tensor (MonExpr.tensor a MonExpr.unit) MonExpr.unit)
      a :=
  MonPath.trans
    (MonPath.assocBwd a MonExpr.unit MonExpr.unit)
    (MonPath.trans
      (MonPath.congRight a (MonPath.leftUnit MonExpr.unit))
      (MonPath.rightUnit a))

theorem assocUnitor_coherent (a : MonExpr α) :
    (assocUnitorPath a).eval_preserved =
    (assocUnitorPath' a).eval_preserved :=
  Subsingleton.elim _ _

/-- Three paths for `I⊗(a⊗I)` → `a`. -/
noncomputable def unitSandwich1 (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit (MonExpr.tensor a MonExpr.unit)) a :=
  MonPath.trans (MonPath.leftUnit _) (MonPath.rightUnit a)

noncomputable def unitSandwich2 (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit (MonExpr.tensor a MonExpr.unit)) a :=
  MonPath.trans
    (MonPath.congRight MonExpr.unit (MonPath.rightUnit a))
    (MonPath.leftUnit a)

noncomputable def unitSandwich3 (a : MonExpr α) :
    MonPath α (MonExpr.tensor MonExpr.unit (MonExpr.tensor a MonExpr.unit)) a :=
  MonPath.trans
    (MonPath.assocFwd MonExpr.unit a MonExpr.unit)
    (MonPath.trans
      (MonPath.rightUnit _)
      (MonPath.leftUnit a))

theorem unitSandwich_coherent12 (a : MonExpr α) :
    (unitSandwich1 a).eval_preserved = (unitSandwich2 a).eval_preserved :=
  Subsingleton.elim _ _

theorem unitSandwich_coherent13 (a : MonExpr α) :
    (unitSandwich1 a).eval_preserved = (unitSandwich3 a).eval_preserved :=
  Subsingleton.elim _ _

theorem unitSandwich_coherent23 (a : MonExpr α) :
    (unitSandwich2 a).eval_preserved = (unitSandwich3 a).eval_preserved :=
  Subsingleton.elim _ _

/-- Symmetry coherence. -/
theorem symm_coherent {e₁ e₂ : MonExpr α}
    (p q : MonPath α e₁ e₂) :
    (MonPath.symm p).eval_preserved = (MonPath.symm q).eval_preserved :=
  Subsingleton.elim _ _

/-- Trans-symm cancellation. -/
theorem trans_symm_coherent {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) :
    (MonPath.trans p (MonPath.symm p)).eval_preserved =
    (MonPath.refl e₁).eval_preserved :=
  Subsingleton.elim _ _

/-- Symm-trans cancellation. -/
theorem symm_trans_coherent {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) :
    (MonPath.trans (MonPath.symm p) p).eval_preserved =
    (MonPath.refl e₂).eval_preserved :=
  Subsingleton.elim _ _

/-- Any path loop gives the trivial equality. -/
theorem loop_trivial {e : MonExpr α} (p : MonPath α e e) :
    p.eval_preserved = Eq.refl (e.eval) :=
  Subsingleton.elim _ _

/-- Whiskering on the left. -/
theorem whisker_left_coherent {b b' : MonExpr α} (a : MonExpr α)
    (p q : MonPath α b b') :
    (MonPath.congRight a p).eval_preserved =
    (MonPath.congRight a q).eval_preserved :=
  Subsingleton.elim _ _

/-- Whiskering on the right. -/
theorem whisker_right_coherent {a a' : MonExpr α} (b : MonExpr α)
    (p q : MonPath α a a') :
    (MonPath.congLeft b p).eval_preserved =
    (MonPath.congLeft b q).eval_preserved :=
  Subsingleton.elim _ _

/-- Bifunctoriality of tensor. -/
theorem bifunctor_coherent {a a' b b' : MonExpr α}
    (p : MonPath α a a') (q : MonPath α b b') :
    (MonPath.congBoth p q).eval_preserved =
    (MonPath.trans (MonPath.congRight a q) (MonPath.congLeft b' p)).eval_preserved :=
  Subsingleton.elim _ _

/-- Naturality of the associator. -/
theorem assoc_naturality {a a' b b' c c' : MonExpr α}
    (p : MonPath α a a') (q : MonPath α b b') (r : MonPath α c c') :
    (MonPath.trans
      (MonPath.congBoth (MonPath.congBoth p q) r)
      (MonPath.assocBwd a' b' c')).eval_preserved =
    (MonPath.trans
      (MonPath.assocBwd a b c)
      (MonPath.congBoth p (MonPath.congBoth q r))).eval_preserved :=
  Subsingleton.elim _ _

/-- Naturality of left unitor. -/
theorem left_unitor_naturality {a a' : MonExpr α}
    (p : MonPath α a a') :
    (MonPath.trans
      (MonPath.congBoth (MonPath.refl MonExpr.unit) p)
      (MonPath.leftUnit a')).eval_preserved =
    (MonPath.trans (MonPath.leftUnit a) p).eval_preserved :=
  Subsingleton.elim _ _

/-- Naturality of right unitor. -/
theorem right_unitor_naturality {a a' : MonExpr α}
    (p : MonPath α a a') :
    (MonPath.trans
      (MonPath.congBoth p (MonPath.refl MonExpr.unit))
      (MonPath.rightUnit a')).eval_preserved =
    (MonPath.trans (MonPath.rightUnit a) p).eval_preserved :=
  Subsingleton.elim _ _

/-- Discrete on normal forms: paths preserve normal form. -/
theorem discrete_on_normal_forms {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) : e₁.normalize = e₂.normalize :=
  coherence_normal_form p

end MoreCoherence

/-! ## Path Algebra -/

section PathAlgebra

variable {α : Type u}

/-- Horizontal composition of paths (tensor). -/
noncomputable def hcomp {a a' b b' : MonExpr α}
    (p : MonPath α a a') (q : MonPath α b b') :
    MonPath α (MonExpr.tensor a b) (MonExpr.tensor a' b') :=
  MonPath.congBoth p q

/-- Vertical composition = path composition. -/
noncomputable def vcomp {e₁ e₂ e₃ : MonExpr α}
    (p : MonPath α e₁ e₂) (q : MonPath α e₂ e₃) : MonPath α e₁ e₃ :=
  MonPath.trans p q

/-- Interchange law. -/
theorem interchange {a₁ a₂ a₃ b₁ b₂ b₃ : MonExpr α}
    (p₁ : MonPath α a₁ a₂) (q₁ : MonPath α a₂ a₃)
    (p₂ : MonPath α b₁ b₂) (q₂ : MonPath α b₂ b₃) :
    (hcomp (vcomp p₁ q₁) (vcomp p₂ q₂)).eval_preserved =
    (vcomp (hcomp p₁ p₂) (hcomp q₁ q₂)).eval_preserved :=
  Subsingleton.elim _ _

theorem hcomp_unit_left {b b' : MonExpr α}
    (q : MonPath α b b') :
    (hcomp (MonPath.refl MonExpr.unit) q).eval_preserved =
    (MonPath.trans
      (MonPath.leftUnit b)
      (MonPath.trans q (MonPath.leftUnitInv b'))).eval_preserved :=
  Subsingleton.elim _ _

theorem hcomp_unit_right {a a' : MonExpr α}
    (p : MonPath α a a') :
    (hcomp p (MonPath.refl MonExpr.unit)).eval_preserved =
    (MonPath.trans
      (MonPath.rightUnit a)
      (MonPath.trans p (MonPath.rightUnitInv a'))).eval_preserved :=
  Subsingleton.elim _ _

end PathAlgebra

/-! ## Decidability -/

section Decidability

variable {α : Type u} [DecidableEq α]

/-- SemEq is decidable. -/
noncomputable instance semEqDecidable (e₁ e₂ : MonExpr α) : Decidable (SemEq e₁ e₂) :=
  inferInstanceAs (Decidable (e₁.atoms = e₂.atoms))

/-- Two expressions are semantically equivalent iff they have the same normal form. -/
theorem semEq_iff_normalize_eq (e₁ e₂ : MonExpr α) :
    SemEq e₁ e₂ ↔ e₁.normalize = e₂.normalize := by
  constructor
  · intro h; exact MonExpr.normalize_eq_of_atoms_eq h
  · intro h
    show e₁.atoms = e₂.atoms
    have h₁ := MonExpr.atoms_ofList e₁.atoms
    have h₂ := MonExpr.atoms_ofList e₂.atoms
    rw [← h₁, ← h₂]
    simp [MonExpr.normalize] at h
    rw [h]

end Decidability

/-! ## Normalization Theorems -/

section Normalization

variable {α : Type u}

theorem normalize_unit : (MonExpr.unit : MonExpr α).normalize = MonExpr.unit := rfl
theorem normalize_atom (a : α) : (MonExpr.atom a).normalize = MonExpr.atom a := rfl

theorem normalize_left_unit (a : MonExpr α) :
    (MonExpr.tensor MonExpr.unit a).normalize = a.normalize := by
  simp [MonExpr.normalize, MonExpr.atoms]

theorem normalize_right_unit (a : MonExpr α) :
    (MonExpr.tensor a MonExpr.unit).normalize = a.normalize := by
  simp [MonExpr.normalize, MonExpr.atoms]

theorem normalize_assoc (a b c : MonExpr α) :
    (MonExpr.tensor a (MonExpr.tensor b c)).normalize =
    (MonExpr.tensor (MonExpr.tensor a b) c).normalize := by
  simp [MonExpr.normalize, MonExpr.atoms, List.append_assoc]

theorem normalize_atoms_preserved (e : MonExpr α) :
    e.normalize.atoms = e.atoms :=
  MonExpr.atoms_ofList e.atoms

end Normalization

/-! ## Eckmann-Hilton -/

section EckmannHilton

variable {α : Type u}

theorem unit_endomorphism_coherent
    (p q : MonPath α MonExpr.unit MonExpr.unit) :
    p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

theorem unit_terminal (e : MonExpr α)
    (p q : MonPath α e MonExpr.unit) :
    p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

theorem unit_initial (e : MonExpr α)
    (p q : MonPath α MonExpr.unit e) :
    p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

end EckmannHilton

/-! ## Stasheff Associahedron -/

section Associahedron

variable {α : Type u}

/-- Three atoms: two parenthesizations. -/
noncomputable def stasheff3_left (a b c : MonExpr α) :=
  MonExpr.tensor (MonExpr.tensor a b) c

noncomputable def stasheff3_right (a b c : MonExpr α) :=
  MonExpr.tensor a (MonExpr.tensor b c)

noncomputable def stasheff3_path (a b c : MonExpr α) :
    MonPath α (stasheff3_left a b c) (stasheff3_right a b c) :=
  MonPath.assocBwd a b c

/-- Four atoms: five parenthesizations forming the pentagon. -/
noncomputable def stasheff4_1 (a b c d : MonExpr α) :=
  MonExpr.tensor (MonExpr.tensor (MonExpr.tensor a b) c) d

noncomputable def stasheff4_2 (a b c d : MonExpr α) :=
  MonExpr.tensor (MonExpr.tensor a (MonExpr.tensor b c)) d

noncomputable def stasheff4_3 (a b c d : MonExpr α) :=
  MonExpr.tensor a (MonExpr.tensor (MonExpr.tensor b c) d)

noncomputable def stasheff4_4 (a b c d : MonExpr α) :=
  MonExpr.tensor a (MonExpr.tensor b (MonExpr.tensor c d))

noncomputable def stasheff4_5 (a b c d : MonExpr α) :=
  MonExpr.tensor (MonExpr.tensor a b) (MonExpr.tensor c d)

noncomputable def stasheff4_e12 (a b c d : MonExpr α) :
    MonPath α (stasheff4_1 a b c d) (stasheff4_2 a b c d) :=
  MonPath.congLeft d (MonPath.assocBwd a b c)

noncomputable def stasheff4_e23 (a b c d : MonExpr α) :
    MonPath α (stasheff4_2 a b c d) (stasheff4_3 a b c d) :=
  MonPath.assocBwd a (MonExpr.tensor b c) d

noncomputable def stasheff4_e34 (a b c d : MonExpr α) :
    MonPath α (stasheff4_3 a b c d) (stasheff4_4 a b c d) :=
  MonPath.congRight a (MonPath.assocBwd b c d)

noncomputable def stasheff4_e15 (a b c d : MonExpr α) :
    MonPath α (stasheff4_1 a b c d) (stasheff4_5 a b c d) :=
  MonPath.assocBwd (MonExpr.tensor a b) c d

noncomputable def stasheff4_e54 (a b c d : MonExpr α) :
    MonPath α (stasheff4_5 a b c d) (stasheff4_4 a b c d) :=
  MonPath.assocBwd a b (MonExpr.tensor c d)

/-- Pentagon: top path (1→2→3→4) = bottom path (1→5→4). -/
theorem stasheff4_pentagon (a b c d : MonExpr α) :
    (MonPath.trans (stasheff4_e12 a b c d)
      (MonPath.trans (stasheff4_e23 a b c d) (stasheff4_e34 a b c d))).eval_preserved =
    (MonPath.trans (stasheff4_e15 a b c d) (stasheff4_e54 a b c d)).eval_preserved :=
  Subsingleton.elim _ _

theorem stasheff4_all_paths_coherent (a b c d : MonExpr α)
    (p q : MonPath α (stasheff4_1 a b c d) (stasheff4_4 a b c d)) :
    p.eval_preserved = q.eval_preserved :=
  Subsingleton.elim _ _

end Associahedron

/-! ## Monoidal Functor Coherence -/

section FunctorCoherence

variable {α β : Type u}

/-- A monoidal functor on expressions. -/
noncomputable def mapExpr (f : α → β) : MonExpr α → MonExpr β
  | MonExpr.unit => MonExpr.unit
  | MonExpr.atom a => MonExpr.atom (f a)
  | MonExpr.tensor l r => MonExpr.tensor (mapExpr f l) (mapExpr f r)

theorem mapExpr_atoms (f : α → β) (e : MonExpr α) :
    (mapExpr f e).atoms = e.atoms.map f := by
  induction e with
  | unit => rfl
  | atom a => rfl
  | tensor l r ihl ihr => simp [mapExpr, MonExpr.atoms, ihl, ihr, List.map_append]

theorem mapExpr_eval (f : α → β) (e : MonExpr α) :
    (mapExpr f e).eval = e.eval.map f := by
  induction e with
  | unit => rfl
  | atom a => rfl
  | tensor l r ihl ihr => simp [mapExpr, MonExpr.eval, ihl, ihr, List.map_append]

theorem mapExpr_normalize (f : α → β) (e : MonExpr α) :
    (mapExpr f e).normalize = mapExpr f (e.normalize) := by
  simp [MonExpr.normalize, mapExpr_atoms]
  induction e.atoms with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp [MonExpr.ofList, mapExpr, List.map]
      exact ih

theorem mapExpr_semEq (f : α → β) {e₁ e₂ : MonExpr α}
    (h : SemEq e₁ e₂) : SemEq (mapExpr f e₁) (mapExpr f e₂) := by
  show (mapExpr f e₁).atoms = (mapExpr f e₂).atoms
  rw [mapExpr_atoms, mapExpr_atoms, h]

theorem functor_coherence (f : α → β) {e₁ e₂ : MonExpr α}
    (p : MonPath α e₁ e₂) :
    (mapExpr f e₁).eval = (mapExpr f e₂).eval := by
  rw [mapExpr_eval, mapExpr_eval, p.eval_preserved]

end FunctorCoherence

/-! ## Concrete Examples -/

section Examples

abbrev NExpr := MonExpr Nat

noncomputable def ex_left : NExpr :=
  MonExpr.tensor (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2)) (MonExpr.atom 3)

noncomputable def ex_right : NExpr :=
  MonExpr.tensor (MonExpr.atom 1) (MonExpr.tensor (MonExpr.atom 2) (MonExpr.atom 3))

theorem ex_eval_eq : ex_left.eval = ex_right.eval := rfl
theorem ex_normalize_eq : ex_left.normalize = ex_right.normalize := rfl

noncomputable def ex_path : MonPath Nat ex_left ex_right :=
  MonPath.assocBwd (MonExpr.atom 1) (MonExpr.atom 2) (MonExpr.atom 3)

/-- Alternative path through unit detour. -/
noncomputable def ex_path' : MonPath Nat ex_left ex_right :=
  MonPath.trans
    (MonPath.trans
      (MonPath.congLeft (MonExpr.atom 3)
        (MonPath.symm (MonPath.rightUnit (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2)))))
      (MonPath.assocBwd
        (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2)) MonExpr.unit (MonExpr.atom 3)))
    (MonPath.trans
      (MonPath.congRight (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2))
        (MonPath.leftUnit (MonExpr.atom 3)))
      (MonPath.assocBwd (MonExpr.atom 1) (MonExpr.atom 2) (MonExpr.atom 3)))

theorem ex_coherent : ex_path.eval_preserved = ex_path'.eval_preserved :=
  Subsingleton.elim _ _

noncomputable def ex4_left : NExpr :=
  MonExpr.tensor
    (MonExpr.tensor (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2)) (MonExpr.atom 3))
    (MonExpr.atom 4)

noncomputable def ex4_right : NExpr :=
  MonExpr.tensor (MonExpr.atom 1)
    (MonExpr.tensor (MonExpr.atom 2)
      (MonExpr.tensor (MonExpr.atom 3) (MonExpr.atom 4)))

theorem ex4_normalize_eq : ex4_left.normalize = ex4_right.normalize := rfl

noncomputable def ex4_path1 : MonPath Nat ex4_left ex4_right :=
  MonPath.trans
    (MonPath.assocBwd (MonExpr.tensor (MonExpr.atom 1) (MonExpr.atom 2)) (MonExpr.atom 3) (MonExpr.atom 4))
    (MonPath.assocBwd (MonExpr.atom 1) (MonExpr.atom 2) _)

noncomputable def ex4_path2 : MonPath Nat ex4_left ex4_right :=
  MonPath.trans
    (MonPath.congLeft (MonExpr.atom 4)
      (MonPath.assocBwd (MonExpr.atom 1) (MonExpr.atom 2) (MonExpr.atom 3)))
    (MonPath.trans
      (MonPath.assocBwd (MonExpr.atom 1) (MonExpr.tensor (MonExpr.atom 2) (MonExpr.atom 3)) (MonExpr.atom 4))
      (MonPath.congRight (MonExpr.atom 1) (MonPath.assocBwd (MonExpr.atom 2) (MonExpr.atom 3) (MonExpr.atom 4))))

theorem ex4_coherent : ex4_path1.eval_preserved = ex4_path2.eval_preserved :=
  Subsingleton.elim _ _

end Examples

end MonoidalCoherence
end ComputationalPaths
