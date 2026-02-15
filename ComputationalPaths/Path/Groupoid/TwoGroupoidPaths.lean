/-
# Strict 2-Groupoid via Computational Paths

0-cells are elements, 1-morphisms are paths, 2-morphisms are paths-between-paths
(equalities of paths). Composition is trans, inverses are symm.
Interchange law, coherence, and bicategory aspects.
All constructions use the core Path/Step/trans/symm/congrArg/transport API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace TwoGroupoidPaths

universe u v w

variable {A : Type u} {B : Type v}
variable {a b c d e : A}

/-! ## 0-cells, 1-cells, 2-cells -/

/-- A 0-cell is an element of A. -/
abbrev ZeroCell (A : Type u) := A

/-- A 1-cell (1-morphism) from a to b is a computational path. -/
abbrev OneCell (a b : A) := Path a b

/-- A 2-cell (2-morphism) between two 1-cells is an equality of paths. -/
def TwoCell (p q : OneCell a b) : Prop := p = q

/-! ## 1-cell operations -/

/-- Identity 1-cell. -/
def oneId (a : A) : OneCell a a := Path.refl a

/-- Composition of 1-cells. -/
def oneComp (f : OneCell a b) (g : OneCell b c) : OneCell a c :=
  Path.trans f g

/-- Inverse of a 1-cell. -/
def oneInv (f : OneCell a b) : OneCell b a :=
  Path.symm f

/-- Left identity for 1-cell composition. -/
theorem oneComp_id_left (f : OneCell a b) :
    oneComp (oneId a) f = f := by
  unfold oneComp oneId; simp

/-- Right identity for 1-cell composition. -/
theorem oneComp_id_right (f : OneCell a b) :
    oneComp f (oneId b) = f := by
  unfold oneComp oneId; simp

/-- Associativity of 1-cell composition. -/
theorem oneComp_assoc (f : OneCell a b) (g : OneCell b c) (h : OneCell c d) :
    oneComp (oneComp f g) h = oneComp f (oneComp g h) := by
  unfold oneComp; exact Path.trans_assoc f g h

/-- Inverse of inverse. -/
theorem oneInv_oneInv (f : OneCell a b) :
    oneInv (oneInv f) = f := by
  unfold oneInv; exact Path.symm_symm f

/-- Inverse reverses composition. -/
theorem oneInv_oneComp (f : OneCell a b) (g : OneCell b c) :
    oneInv (oneComp f g) = oneComp (oneInv g) (oneInv f) := by
  unfold oneInv oneComp; simp

/-- Inverse of identity. -/
theorem oneInv_oneId (a : A) :
    oneInv (oneId a) = oneId a := by
  unfold oneInv oneId; simp

/-! ## 2-cell operations -/

/-- Identity 2-cell. -/
def twoId (f : OneCell a b) : TwoCell f f := rfl

/-- Vertical composition of 2-cells. -/
def twoVComp {f g h : OneCell a b}
    (α : TwoCell f g) (β : TwoCell g h) : TwoCell f h :=
  Eq.trans α β

/-- Inverse of a 2-cell. -/
def twoInv {f g : OneCell a b} (α : TwoCell f g) : TwoCell g f :=
  Eq.symm α

/-- All 2-cells between the same 1-cells are equal (proof irrelevance). -/
theorem twoCell_unique {f g : OneCell a b} (α β : TwoCell f g) :
    α = β :=
  Subsingleton.elim α β

/-! ## Vertical composition laws -/

/-- Vertical composition: left identity. -/
theorem twoVComp_id_left {f g : OneCell a b} (α : TwoCell f g) :
    twoVComp (twoId f) α = α :=
  Subsingleton.elim _ _

/-- Vertical composition: right identity. -/
theorem twoVComp_id_right {f g : OneCell a b} (α : TwoCell f g) :
    twoVComp α (twoId g) = α :=
  Subsingleton.elim _ _

/-- Vertical composition: associativity. -/
theorem twoVComp_assoc {f g h k : OneCell a b}
    (α : TwoCell f g) (β : TwoCell g h) (γ : TwoCell h k) :
    twoVComp (twoVComp α β) γ = twoVComp α (twoVComp β γ) :=
  Subsingleton.elim _ _

/-- Vertical composition: left inverse. -/
theorem twoVComp_inv_left {f g : OneCell a b} (α : TwoCell f g) :
    twoVComp (twoInv α) α = twoId g :=
  Subsingleton.elim _ _

/-- Vertical composition: right inverse. -/
theorem twoVComp_inv_right {f g : OneCell a b} (α : TwoCell f g) :
    twoVComp α (twoInv α) = twoId f :=
  Subsingleton.elim _ _

/-- Double inverse of 2-cell. -/
theorem twoInv_twoInv {f g : OneCell a b} (α : TwoCell f g) :
    twoInv (twoInv α) = α :=
  Subsingleton.elim _ _

/-! ## Horizontal composition -/

/-- Horizontal composition of 2-cells. -/
def twoHComp {f₁ f₂ : OneCell a b} {g₁ g₂ : OneCell b c}
    (α : TwoCell f₁ f₂) (β : TwoCell g₁ g₂) :
    TwoCell (oneComp f₁ g₁) (oneComp f₂ g₂) := by
  unfold TwoCell oneComp; subst α; subst β; rfl

/-- Horizontal composition with identity 2-cells. -/
theorem twoHComp_id_id (f : OneCell a b) (g : OneCell b c) :
    twoHComp (twoId f) (twoId g) = twoId (oneComp f g) :=
  Subsingleton.elim _ _

/-- Left whiskering: 2-cell postcomposed with a 1-cell. -/
def whiskerL (f : OneCell a b) {g₁ g₂ : OneCell b c}
    (β : TwoCell g₁ g₂) : TwoCell (oneComp f g₁) (oneComp f g₂) :=
  twoHComp (twoId f) β

/-- Right whiskering: 2-cell precomposed with a 1-cell. -/
def whiskerR {f₁ f₂ : OneCell a b} (α : TwoCell f₁ f₂)
    (g : OneCell b c) : TwoCell (oneComp f₁ g) (oneComp f₂ g) :=
  twoHComp α (twoId g)

/-- Left whiskering with identity. -/
theorem whiskerL_id (f : OneCell a b) (g : OneCell b c) :
    whiskerL f (twoId g) = twoId (oneComp f g) :=
  Subsingleton.elim _ _

/-- Right whiskering with identity. -/
theorem whiskerR_id (f : OneCell a b) (g : OneCell b c) :
    whiskerR (twoId f) g = twoId (oneComp f g) :=
  Subsingleton.elim _ _

/-! ## Interchange law -/

/-- The interchange law: horizontal composition distributes over vertical. -/
theorem interchange {f₁ f₂ f₃ : OneCell a b} {g₁ g₂ g₃ : OneCell b c}
    (α₁ : TwoCell f₁ f₂) (α₂ : TwoCell f₂ f₃)
    (β₁ : TwoCell g₁ g₂) (β₂ : TwoCell g₂ g₃) :
    twoHComp (twoVComp α₁ α₂) (twoVComp β₁ β₂) =
      twoVComp (twoHComp α₁ β₁) (twoHComp α₂ β₂) :=
  Subsingleton.elim _ _

/-- Eckmann-Hilton: horizontal and vertical composition agree on endo-2-cells. -/
theorem eckmann_hilton {f : OneCell a a}
    (α β : TwoCell f f) :
    twoVComp α β = twoVComp β α :=
  Subsingleton.elim _ _

/-! ## Coherence -/

/-- Associator 2-cell: witnessing associativity of 1-cell composition. -/
def associator (f : OneCell a b) (g : OneCell b c) (h : OneCell c d) :
    TwoCell (oneComp (oneComp f g) h) (oneComp f (oneComp g h)) :=
  oneComp_assoc f g h

/-- Left unitor 2-cell. -/
def leftUnitor (f : OneCell a b) :
    TwoCell (oneComp (oneId a) f) f :=
  oneComp_id_left f

/-- Right unitor 2-cell. -/
def rightUnitor (f : OneCell a b) :
    TwoCell (oneComp f (oneId b)) f :=
  oneComp_id_right f

/-- Pentagon coherence: any two reassociations agree. -/
theorem pentagon (f : OneCell a b) (g : OneCell b c)
    (h : OneCell c d) (k : OneCell d e) :
    twoVComp (associator (oneComp f g) h k) (associator f g (oneComp h k)) =
      twoVComp (twoHComp (associator f g h) (twoId k))
        (twoVComp (associator f (oneComp g h) k)
          (twoHComp (twoId f) (associator g h k))) :=
  Subsingleton.elim _ _

/-- Triangle coherence: left unitor, right unitor, and associator commute. -/
theorem triangle (f : OneCell a b) (g : OneCell b c) :
    twoVComp (associator f (oneId b) g)
      (twoHComp (twoId f) (leftUnitor g)) =
      twoHComp (rightUnitor f) (twoId g) :=
  Subsingleton.elim _ _

/-! ## Functoriality (1-cell maps via congrArg) -/

/-- A function induces a 2-functor on the 2-groupoid. -/
def functorOneCell (f : A → B) (p : OneCell a b) : OneCell (f a) (f b) :=
  Path.congrArg f p

/-- The functor preserves identity 1-cells. -/
theorem functor_oneId (f : A → B) (a : A) :
    functorOneCell f (oneId a) = oneId (f a) := by
  unfold functorOneCell oneId; simp

/-- The functor preserves 1-cell composition. -/
theorem functor_oneComp (f : A → B) (p : OneCell a b) (q : OneCell b c) :
    functorOneCell f (oneComp p q) =
      oneComp (functorOneCell f p) (functorOneCell f q) := by
  unfold functorOneCell oneComp; simp

/-- The functor preserves 1-cell inverse. -/
theorem functor_oneInv (f : A → B) (p : OneCell a b) :
    functorOneCell f (oneInv p) = oneInv (functorOneCell f p) := by
  exact Path.congrArg_symm f p

/-- The functor sends 2-cells to 2-cells. -/
def functorTwoCell (f : A → B) {p q : OneCell a b}
    (α : TwoCell p q) : TwoCell (functorOneCell f p) (functorOneCell f q) := by
  unfold TwoCell at *
  unfold functorOneCell
  have h : p = q := α
  subst h; rfl

/-- The 2-cell functor preserves identity 2-cells. -/
theorem functor_twoId (f : A → B) (p : OneCell a b) :
    functorTwoCell f (twoId p) = twoId (functorOneCell f p) :=
  Subsingleton.elim _ _

/-- The 2-cell functor preserves vertical composition. -/
theorem functor_twoVComp (f : A → B) {p q r : OneCell a b}
    (α : TwoCell p q) (β : TwoCell q r) :
    functorTwoCell f (twoVComp α β) =
      twoVComp (functorTwoCell f α) (functorTwoCell f β) :=
  Subsingleton.elim _ _

end TwoGroupoidPaths
end Path
end ComputationalPaths
