/- 
# Type-valued derivation trees for Expr-level rewrite equivalence

This module records rewrite-equivalence derivations on
`Rewrite.GroupoidConfluence.Expr` as data in `Type`, so different derivation
trees remain distinguishable.
-/

import ComputationalPaths.Path.Rewrite.GroupoidConfluence

namespace ComputationalPaths
namespace Path
namespace Polygraph

abbrev Expr := Rewrite.GroupoidTRS.Expr
local notation "eRefl" => Rewrite.GroupoidTRS.Expr.refl
local notation "eSymm" => Rewrite.GroupoidTRS.Expr.symm
local notation "eTrans" => Rewrite.GroupoidTRS.Expr.trans

/-- Type-valued derivation tree for Expr-level rewrite equivalence.
Each constructor mirrors a `CStep` rule or the symmetric/transitive closure. -/
inductive RwEqDeriv : Expr → Expr → Type where
  | symm_refl : RwEqDeriv (eSymm eRefl) eRefl
  | symm_symm (p : Expr) : RwEqDeriv (eSymm (eSymm p)) p
  | trans_refl_left (p : Expr) : RwEqDeriv (eTrans eRefl p) p
  | trans_refl_right (p : Expr) : RwEqDeriv (eTrans p eRefl) p
  | trans_symm (p : Expr) : RwEqDeriv (eTrans p (eSymm p)) eRefl
  | symm_trans (p : Expr) : RwEqDeriv (eTrans (eSymm p) p) eRefl
  | symm_trans_congr (p q : Expr) :
      RwEqDeriv (eSymm (eTrans p q)) (eTrans (eSymm q) (eSymm p))
  | trans_assoc (p q r : Expr) :
      RwEqDeriv (eTrans (eTrans p q) r) (eTrans p (eTrans q r))
  | trans_cancel_left (p q : Expr) :
      RwEqDeriv (eTrans p (eTrans (eSymm p) q)) q
  | trans_cancel_right (p q : Expr) :
      RwEqDeriv (eTrans (eSymm p) (eTrans p q)) q
  | symm_congr {p q : Expr} :
      RwEqDeriv p q → RwEqDeriv (eSymm p) (eSymm q)
  | trans_congr_left (r : Expr) {p q : Expr} :
      RwEqDeriv p q → RwEqDeriv (eTrans p r) (eTrans q r)
  | trans_congr_right (p : Expr) {q r : Expr} :
      RwEqDeriv q r → RwEqDeriv (eTrans p q) (eTrans p r)
  | symm {p q : Expr} : RwEqDeriv p q → RwEqDeriv q p
  | trans {p q r : Expr} : RwEqDeriv p q → RwEqDeriv q r → RwEqDeriv p r

namespace RwEqDeriv

/-- Vertical composition of derivations. -/
@[simp] noncomputable def vcomp {p q r : Expr}
    (d₁ : RwEqDeriv p q) (d₂ : RwEqDeriv q r) : RwEqDeriv p r :=
  .trans d₁ d₂

/-- Horizontal transport under `symm`. -/
@[simp] noncomputable def hsymm {p q : Expr} (d : RwEqDeriv p q) :
    RwEqDeriv (eSymm p) (eSymm q) :=
  match d with
  | .trans d₁ d₂ => .trans (hsymm d₁) (hsymm d₂)
  | d' => .symm_congr d'

/-- Horizontal transport under right composition (`trans _ t`). -/
@[simp] noncomputable def htransLeft (t : Expr) {p q : Expr} (d : RwEqDeriv p q) :
    RwEqDeriv (eTrans p t) (eTrans q t) :=
  match d with
  | .trans d₁ d₂ => .trans (htransLeft t d₁) (htransLeft t d₂)
  | d' => .trans_congr_left t d'

/-- Horizontal transport under left composition (`trans t _`). -/
@[simp] noncomputable def htransRight (t : Expr) {p q : Expr} (d : RwEqDeriv p q) :
    RwEqDeriv (eTrans t p) (eTrans t q) :=
  match d with
  | .trans d₁ d₂ => .trans (htransRight t d₁) (htransRight t d₂)
  | d' => .trans_congr_right t d'

/-- Horizontal composition in a `trans` context. -/
@[simp] noncomputable def hcomp {p p' q q' : Expr}
    (dp : RwEqDeriv p p') (dq : RwEqDeriv q q') :
    RwEqDeriv (eTrans p q) (eTrans p' q') :=
  vcomp (htransLeft q dp) (htransRight p' dq)

/-- Two distinct derivations of the same rewrite fact. -/
noncomputable def deriv_refl_left : RwEqDeriv (eTrans eRefl eRefl) eRefl :=
  .trans_refl_left eRefl

/-- A second derivation of the same rewrite fact. -/
noncomputable def deriv_refl_right : RwEqDeriv (eTrans eRefl eRefl) eRefl :=
  .trans_refl_right eRefl

theorem deriv_refl_left_ne_right : deriv_refl_left ≠ deriv_refl_right := by
  intro h
  have h' :
      (RwEqDeriv.trans_refl_left eRefl :
        RwEqDeriv (eTrans eRefl eRefl) eRefl) =
      (RwEqDeriv.trans_refl_right eRefl :
        RwEqDeriv (eTrans eRefl eRefl) eRefl) := by
    simpa [deriv_refl_left, deriv_refl_right] using h
  cases h'

theorem distinct_derivations_exist :
    ∃ d₁ d₂ : RwEqDeriv (eTrans eRefl eRefl) eRefl, d₁ ≠ d₂ :=
  ⟨deriv_refl_left, deriv_refl_right, deriv_refl_left_ne_right⟩

@[simp] theorem hsymm_vcomp {p q r : Expr}
    (d₁ : RwEqDeriv p q) (d₂ : RwEqDeriv q r) :
    hsymm (vcomp d₁ d₂) = vcomp (hsymm d₁) (hsymm d₂) := rfl

@[simp] theorem htransLeft_vcomp {p q r : Expr} (t : Expr)
    (d₁ : RwEqDeriv p q) (d₂ : RwEqDeriv q r) :
    htransLeft t (vcomp d₁ d₂) = vcomp (htransLeft t d₁) (htransLeft t d₂) := rfl

@[simp] theorem htransRight_vcomp {p q r : Expr} (t : Expr)
    (d₁ : RwEqDeriv p q) (d₂ : RwEqDeriv q r) :
    htransRight t (vcomp d₁ d₂) = vcomp (htransRight t d₁) (htransRight t d₂) := rfl

/-- Interchange law: horizontal transport through nested `trans` contexts
distributes over vertical composition. -/
theorem interchange {p q r : Expr} (l t : Expr)
    (d₁ : RwEqDeriv p q) (d₂ : RwEqDeriv q r) :
    htransRight l (htransLeft t (vcomp d₁ d₂)) =
      vcomp (htransRight l (htransLeft t d₁))
            (htransRight l (htransLeft t d₂)) := by
  rfl

end RwEqDeriv

end Polygraph
end Path
end ComputationalPaths
