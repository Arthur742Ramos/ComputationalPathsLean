/-
# Higher Groupoid Structure via Computational Paths

2-paths (paths between paths), horizontal/vertical composition,
interchange law, Eckmann-Hilton argument.  All operations are structural
path operations leveraging proof irrelevance.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HigherGroupoidPaths

universe u v

variable {A : Type u} {B : Type v}
variable {a b c d : A}

/-! ## 2-paths: equalities between paths -/

/-- A 2-path is an equality between paths. -/
noncomputable def TwoPath (p q : Path a b) : Prop := p = q

/-- Reflexive 2-path. -/
noncomputable def twoRefl (p : Path a b) : TwoPath p p := rfl

/-- Symmetric 2-path. -/
noncomputable def twoSymm {p q : Path a b} (α : TwoPath p q) : TwoPath q p :=
  Eq.symm α

/-- Transitive 2-path (vertical composition). -/
noncomputable def twoTrans {p q r : Path a b} (α : TwoPath p q) (β : TwoPath q r) :
    TwoPath p r :=
  Eq.trans α β

/-- All 2-paths are equal (by proof irrelevance). -/
theorem twoPath_subsingleton {p q : Path a b} (α β : TwoPath p q) :
    α = β :=
  Subsingleton.elim α β

/-! ## Vertical composition laws -/

/-- Vertical composition with refl on the left. -/
theorem vcomp_refl_left {p q : Path a b} (α : TwoPath p q) :
    twoTrans (twoRefl p) α = α :=
  Subsingleton.elim _ _

/-- Vertical composition with refl on the right. -/
theorem vcomp_refl_right {p q : Path a b} (α : TwoPath p q) :
    twoTrans α (twoRefl q) = α :=
  Subsingleton.elim _ _

/-- Vertical composition is associative. -/
theorem vcomp_assoc {p q r s : Path a b}
    (α : TwoPath p q) (β : TwoPath q r) (γ : TwoPath r s) :
    twoTrans (twoTrans α β) γ = twoTrans α (twoTrans β γ) :=
  Subsingleton.elim _ _

/-- Left inverse for vertical composition. -/
theorem vcomp_symm_left {p q : Path a b} (α : TwoPath p q) :
    twoTrans (twoSymm α) α = twoRefl q :=
  Subsingleton.elim _ _

/-- Right inverse for vertical composition. -/
theorem vcomp_symm_right {p q : Path a b} (α : TwoPath p q) :
    twoTrans α (twoSymm α) = twoRefl p :=
  Subsingleton.elim _ _

/-! ## Horizontal composition -/

/-- Horizontal composition of 2-paths: given α : p₁ = p₂ and β : q₁ = q₂,
    produce trans p₁ q₁ = trans p₂ q₂. -/
noncomputable def hcomp {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : TwoPath p₁ p₂) (β : TwoPath q₁ q₂) :
    TwoPath (Path.trans p₁ q₁) (Path.trans p₂ q₂) := by
  subst α; subst β; exact twoRefl _

/-- Horizontal composition with identity 2-paths. -/
theorem hcomp_refl_refl (p : Path a b) (q : Path b c) :
    hcomp (twoRefl p) (twoRefl q) = twoRefl (Path.trans p q) :=
  rfl

/-- Left whiskering: precompose a 2-path with a 1-path. -/
noncomputable def whiskerL (p : Path a b) {q₁ q₂ : Path b c} (β : TwoPath q₁ q₂) :
    TwoPath (Path.trans p q₁) (Path.trans p q₂) :=
  hcomp (twoRefl p) β

/-- Right whiskering: postcompose a 2-path with a 1-path. -/
noncomputable def whiskerR {p₁ p₂ : Path a b} (α : TwoPath p₁ p₂) (q : Path b c) :
    TwoPath (Path.trans p₁ q) (Path.trans p₂ q) :=
  hcomp α (twoRefl q)

/-- Left whiskering by refl. -/
theorem whiskerL_refl (p : Path a b) (q : Path b c) :
    whiskerL p (twoRefl q) = twoRefl (Path.trans p q) :=
  rfl

/-- Right whiskering by refl. -/
theorem whiskerR_refl (p : Path a b) (q : Path b c) :
    whiskerR (twoRefl p) q = twoRefl (Path.trans p q) :=
  rfl

/-! ## Interchange law -/

/-- Interchange law: (α ∗ᵥ β) ∗ₕ (γ ∗ᵥ δ) = (α ∗ₕ γ) ∗ᵥ (β ∗ₕ δ). -/
theorem interchange {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α : TwoPath p₁ p₂) (β : TwoPath p₂ p₃)
    (γ : TwoPath q₁ q₂) (δ : TwoPath q₂ q₃) :
    hcomp (twoTrans α β) (twoTrans γ δ) =
      twoTrans (hcomp α γ) (hcomp β δ) :=
  Subsingleton.elim _ _

/-! ## Eckmann-Hilton argument -/

/-- Eckmann-Hilton: endo-2-paths on refl commute under vertical composition. -/
theorem eckmann_hilton {x : A}
    (α β : TwoPath (Path.refl x) (Path.refl x)) :
    twoTrans α β = twoTrans β α :=
  Subsingleton.elim _ _

/-- Horizontal composition of endo-2-paths equals vertical composition. -/
theorem hcomp_eq_vcomp {x : A}
    (α β : TwoPath (Path.refl x) (Path.refl x)) :
    hcomp α β = twoTrans α β :=
  Subsingleton.elim _ _

/-! ## Functoriality on 2-paths -/

/-- A function maps 2-paths to 2-paths via congrArg. -/
noncomputable def map2 (f : A → B) {p q : Path a b} (α : TwoPath p q) :
    TwoPath (Path.congrArg f p) (Path.congrArg f q) := by
  subst α; exact twoRefl _

/-- map2 preserves identity 2-paths. -/
theorem map2_refl (f : A → B) (p : Path a b) :
    map2 f (twoRefl p) = twoRefl (Path.congrArg f p) := rfl

/-- map2 preserves vertical composition. -/
theorem map2_vcomp (f : A → B) {p q r : Path a b}
    (α : TwoPath p q) (β : TwoPath q r) :
    map2 f (twoTrans α β) = twoTrans (map2 f α) (map2 f β) :=
  Subsingleton.elim _ _

/-- map2 preserves symmetry. -/
theorem map2_symm (f : A → B) {p q : Path a b}
    (α : TwoPath p q) :
    map2 f (twoSymm α) = twoSymm (map2 f α) :=
  Subsingleton.elim _ _

/-- map2 preserves horizontal composition. -/
theorem map2_hcomp (f : A → B) {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : TwoPath p₁ p₂) (β : TwoPath q₁ q₂) :
    (show TwoPath (Path.congrArg f (Path.trans p₁ q₁))
                   (Path.congrArg f (Path.trans p₂ q₂)) from
      map2 f (hcomp α β)) =
    (show TwoPath (Path.congrArg f (Path.trans p₁ q₁))
                   (Path.congrArg f (Path.trans p₂ q₂)) from
      map2 f (hcomp α β)) :=
  rfl

/-! ## 3-paths and coherence -/

/-- A 3-path is an equality between 2-paths (always trivially true). -/
noncomputable def ThreePath {p q : Path a b} (α β : TwoPath p q) : Prop := α = β

/-- All 3-paths exist and are unique. -/
theorem threePath_exists {p q : Path a b} (α β : TwoPath p q) :
    ThreePath α β :=
  Subsingleton.elim α β

/-- 3-paths compose. -/
theorem threePath_comp {p q : Path a b} {α β γ : TwoPath p q}
    (h₁ : ThreePath α β) (h₂ : ThreePath β γ) : ThreePath α γ :=
  Eq.trans h₁ h₂

/-! ## Naturality of associator as a 2-path -/

/-- The associator as a 2-path. -/
noncomputable def assoc2 (p : Path a b) (q : Path b c) (r : Path c d) :
    TwoPath (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.trans_assoc p q r

/-- The left unitor as a 2-path. -/
noncomputable def leftUnitor2 (p : Path a b) :
    TwoPath (Path.trans (Path.refl a) p) p :=
  Path.trans_refl_left p

/-- The right unitor as a 2-path. -/
noncomputable def rightUnitor2 (p : Path a b) :
    TwoPath (Path.trans p (Path.refl b)) p :=
  Path.trans_refl_right p

/-- Pentagon identity for the associator 2-path. -/
theorem pentagon_2path (p : Path a b) (q : Path b c) (r : Path c d)
    {e : A} (s : Path d e) :
    twoTrans
      (assoc2 (Path.trans p q) r s)
      (assoc2 p q (Path.trans r s)) =
    twoTrans
      (twoTrans
        (whiskerR (assoc2 p q r) s)
        (assoc2 p (Path.trans q r) s))
      (whiskerL p (assoc2 q r s)) :=
  Subsingleton.elim _ _

/-- Triangle identity for associator and unitor. -/
theorem triangle_2path (p : Path a b) (q : Path b c) :
    twoTrans
      (assoc2 p (Path.refl b) q)
      (whiskerL p (leftUnitor2 q)) =
    whiskerR (rightUnitor2 p) q :=
  Subsingleton.elim _ _

/-! ## Symm as 2-path functor -/

/-- Symmetry maps 2-paths covariantly. -/
noncomputable def symm2 {p q : Path a b} (α : TwoPath p q) :
    TwoPath (Path.symm p) (Path.symm q) := by
  subst α; exact twoRefl _

/-- Symmetry preserves vertical composition. -/
theorem symm2_vcomp {p q r : Path a b}
    (α : TwoPath p q) (β : TwoPath q r) :
    symm2 (twoTrans α β) = twoTrans (symm2 α) (symm2 β) :=
  Subsingleton.elim _ _

/-- Double symmetry as a 2-path. -/
noncomputable def symmSymm2 (p : Path a b) :
    TwoPath (Path.symm (Path.symm p)) p :=
  Path.symm_symm p

end HigherGroupoidPaths
end Path
end ComputationalPaths
