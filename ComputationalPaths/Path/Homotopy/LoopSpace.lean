/-
# Loop Space — Deep Homotopical Path Theory

This module develops the loop space `Ω(A, a)` as the type of computational paths
from a point to itself, together with its algebraic structure:

- Loop concatenation = path trans
- Loop inverse = path symm
- Loop space group (proved via LoopQuot from Loops.lean)
- Iterated loop spaces and Eckmann–Hilton commutativity
- Based vs free loop spaces
- Higher loop operations and coherence

All theorems have complete proofs — zero sorry.
-/

import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpace

universe u v

variable {A : Type u} {B : Type v}

/-! ## Loop space definition and basic operations -/

/-- Local alias for the loop space at a basepoint. -/
abbrev BaseLoop (A : Type u) (a : A) : Type u :=
  ComputationalPaths.Path.LoopSpace A a

/-- A 2-cell between parallel computational paths. -/
abbrev TwoCell {A : Type u} {x y : A} (p q : Path x y) : Prop := RwEq p q

/-! ## Loop concatenation = path trans -/

/-- Loop concatenation is definitionally path trans. -/
theorem loop_concat_eq_trans {a : A} (p q : BaseLoop A a) :
    LoopSpace.comp p q = Path.trans p q := rfl

/-- Loop inverse is definitionally path symm. -/
theorem loop_inv_eq_symm {a : A} (p : BaseLoop A a) :
    LoopSpace.inv p = Path.symm p := rfl

/-- Loop identity is definitionally path refl. -/
theorem loop_id_eq_refl (a : A) :
    LoopSpace.id (A := A) (a := a) = Path.refl a := rfl

/-! ## Groupoid laws for loops (propositional level) -/

/-- Left identity for loop composition. -/
theorem loop_trans_refl_left {a : A} (p : BaseLoop A a) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Right identity for loop composition. -/
theorem loop_trans_refl_right {a : A} (p : BaseLoop A a) :
    Path.trans p (Path.refl a) = p :=
  Path.trans_refl_right p

/-- Associativity of loop composition. -/
theorem loop_trans_assoc {a : A} (p q r : BaseLoop A a) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Double symmetry is identity for loops. -/
theorem loop_symm_symm {a : A} (p : BaseLoop A a) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symmetry distributes over trans in reverse order. -/
theorem loop_symm_trans {a : A} (p q : BaseLoop A a) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-! ## Loop space is a group (via LoopQuot) -/

/-- The loop group at a basepoint, witnessing that LoopQuot forms a group. -/
def loopGroupAt (A : Type u) (a : A) : LoopGroup A a :=
  loopGroup A a

/-- Loop group multiplication is associative. -/
theorem loopGroup_mul_assoc (A : Type u) (a : A)
    (x y z : LoopQuot A a) :
    LoopQuot.comp (LoopQuot.comp x y) z = LoopQuot.comp x (LoopQuot.comp y z) :=
  LoopQuot.comp_assoc x y z

/-- Loop group has left identity. -/
theorem loopGroup_id_comp (A : Type u) (a : A)
    (x : LoopQuot A a) :
    LoopQuot.comp LoopQuot.id x = x :=
  LoopQuot.id_comp x

/-- Loop group has right identity. -/
theorem loopGroup_comp_id (A : Type u) (a : A)
    (x : LoopQuot A a) :
    LoopQuot.comp x LoopQuot.id = x :=
  LoopQuot.comp_id x

/-- Loop group has left inverses. -/
theorem loopGroup_inv_comp (A : Type u) (a : A)
    (x : LoopQuot A a) :
    LoopQuot.comp (LoopQuot.inv x) x = LoopQuot.id :=
  LoopQuot.inv_comp x

/-- Loop group has right inverses. -/
theorem loopGroup_comp_inv (A : Type u) (a : A)
    (x : LoopQuot A a) :
    LoopQuot.comp x (LoopQuot.inv x) = LoopQuot.id :=
  LoopQuot.comp_inv x

/-- Double inverse in the loop group. -/
theorem loopGroup_inv_inv (A : Type u) (a : A)
    (x : LoopQuot A a) :
    LoopQuot.inv (LoopQuot.inv x) = x :=
  LoopQuot.inv_inv x

/-- Inverse of product in loop group reverses order. -/
theorem loopGroup_inv_comp_rev (A : Type u) (a : A)
    (x y : LoopQuot A a) :
    LoopQuot.inv (LoopQuot.comp x y) = LoopQuot.comp (LoopQuot.inv y) (LoopQuot.inv x) :=
  LoopQuot.inv_comp_rev x y

/-! ## RwEq-level 2-cells for loops -/

/-- Left-associated route through four loop composites. -/
def routeLeft {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans (Path.trans (Path.trans p q) r) s

/-- Middle route through four loop composites. -/
def routeMiddle {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.trans (Path.trans q r) s)

/-- Right-associated route through four loop composites. -/
def routeRight {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.trans q (Path.trans r s))

/-- The first rerouting step (left to middle) is a 2-cell. -/
theorem left_to_middle_two_cell {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeLeft p q r s) (routeMiddle p q r s) := by
  exact RwEq.trans
    (rweq_trans_congr_left s (rweq_tt p q r))
    (rweq_tt p (Path.trans q r) s)

/-- The second rerouting step (middle to right) is a 2-cell. -/
theorem middle_to_right_two_cell {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeMiddle p q r s) (routeRight p q r s) :=
  rweq_trans_congr_right p (rweq_tt q r s)

/-- Any two standard routes from left-associated to right-associated coincide up to a 2-cell. -/
theorem left_to_right_two_cell {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeLeft p q r s) (routeRight p q r s) := by
  exact RwEq.trans (left_to_middle_two_cell p q r s) (middle_to_right_two_cell p q r s)

/-! ## Unit, inverse, and iterated-path routes -/

/-- Left-unit route for loops. -/
def leftUnitRoute {a : A} (p : BaseLoop A a) : BaseLoop A a :=
  Path.trans (Path.refl a) p

/-- Right-unit route for loops. -/
def rightUnitRoute {a : A} (p : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.refl a)

/-- Left unit contraction is a 2-cell. -/
theorem left_unit_two_cell {a : A} (p : BaseLoop A a) :
    TwoCell (leftUnitRoute p) p :=
  rweq_cmpA_refl_left p

/-- Right unit contraction is a 2-cell. -/
theorem right_unit_two_cell {a : A} (p : BaseLoop A a) :
    TwoCell (rightUnitRoute p) p :=
  rweq_cmpA_refl_right p

/-- Left inverse cancellation is a 2-cell. -/
theorem inverse_left_two_cell {a : A} (p : BaseLoop A a) :
    TwoCell (Path.trans (Path.symm p) p) (Path.refl a) :=
  rweq_cmpA_inv_left p

/-- Right inverse cancellation is a 2-cell. -/
theorem inverse_right_two_cell {a : A} (p : BaseLoop A a) :
    TwoCell (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

/-! ## Iterated loop spaces -/

/-- Pointed data for iterated loop/path spaces. -/
def iteratedLoopPointedData (a : A) : Nat → Sigma fun X : Type u => X
  | 0 => ⟨A, a⟩
  | n + 1 =>
      let prev := iteratedLoopPointedData a n
      ⟨ComputationalPaths.Path.LoopSpace prev.1 prev.2, Path.refl prev.2⟩

/-- The `n`-fold iterated loop space type. -/
abbrev iteratedPathSpace (a : A) (n : Nat) : Type u :=
  (iteratedLoopPointedData a n).1

/-- The basepoint of the `n`-fold iterated loop space. -/
def iteratedBasepoint (a : A) (n : Nat) : iteratedPathSpace a n :=
  (iteratedLoopPointedData a n).2

/-- The 0-th iterated loop space is just A. -/
theorem iteratedPathSpace_zero (a : A) :
    iteratedPathSpace a 0 = A := rfl

/-- The 1st iterated loop space is the loop space. -/
theorem iteratedPathSpace_one (a : A) :
    iteratedPathSpace a 1 = ComputationalPaths.Path.LoopSpace A a := rfl

/-- The basepoint at level 0 is just `a`. -/
theorem iteratedBasepoint_zero (a : A) :
    iteratedBasepoint a 0 = a := rfl

/-- The basepoint at level 1 is `refl a`. -/
theorem iteratedBasepoint_one (a : A) :
    iteratedBasepoint a 1 = Path.refl a := rfl

/-! ## Eckmann–Hilton for 2-path loops

In a UIP setting, 2-paths `p = q` for `p q : Path a b` live in Prop,
so they are all equal by proof irrelevance. This gives us Eckmann–Hilton
for free: any two such 2-paths commute. -/

/-- Eckmann–Hilton commutativity for 2-path loops (proof irrelevance). -/
theorem eckmann_hilton_two_paths {a b : A} {p : Path a b}
    (α β : p = p) :
    Eq.trans α β = Eq.trans β α := by
  apply Subsingleton.elim

/-- Interchange law for 2-path loops (proof irrelevance). -/
theorem two_path_interchange {a b : A} {p : Path a b}
    (α β γ δ : p = p) :
    Eq.trans (Eq.trans α β) (Eq.trans γ δ) =
      Eq.trans (Eq.trans α γ) (Eq.trans β δ) := by
  apply Subsingleton.elim

/-- All 2-loops at a path are trivial (UIP collapse). -/
theorem two_loop_trivial {a b : A} {p : Path a b}
    (α : p = p) : α = rfl := by
  apply Subsingleton.elim

/-! ## Free loop space -/

/-- The free loop space: pairs of a point and a loop at that point. -/
def FreeLoopSpace (A : Type u) : Type u :=
  Σ a : A, ComputationalPaths.Path.LoopSpace A a

/-- Inclusion of the based loop space into the free loop space. -/
def basedToFree (a : A) : BaseLoop A a → FreeLoopSpace A :=
  fun p => ⟨a, p⟩

/-- Projection from the free loop space to the base type. -/
def freeLoopProj : FreeLoopSpace A → A :=
  Sigma.fst

/-- The constant section of the free loop space. -/
def freeLoopConst : A → FreeLoopSpace A :=
  fun a => ⟨a, Path.refl a⟩

/-- The constant section is a section of the projection. -/
theorem freeLoopConst_section (a : A) :
    freeLoopProj (freeLoopConst a) = a := rfl

/-- Based-to-free preserves the basepoint. -/
theorem basedToFree_proj (a : A) (p : BaseLoop A a) :
    freeLoopProj (basedToFree a p) = a := rfl

/-! ## Induced maps on loop spaces -/

/-- A function f : A → B induces a map on loop spaces. -/
def loopMap (f : A → B) (a : A) : BaseLoop A a → BaseLoop B (f a) :=
  fun p => Path.congrArg f p

/-- The induced loop map preserves the identity loop. -/
theorem loopMap_id (f : A → B) (a : A) :
    loopMap f a (Path.refl a) = Path.refl (f a) := by
  simp [loopMap, Path.congrArg]

/-- The induced loop map preserves loop composition. -/
theorem loopMap_trans (f : A → B) (a : A) (p q : BaseLoop A a) :
    loopMap f a (Path.trans p q) = Path.trans (loopMap f a p) (loopMap f a q) := by
  simp [loopMap]

/-- The induced loop map preserves loop inversion. -/
theorem loopMap_symm (f : A → B) (a : A) (p : BaseLoop A a) :
    loopMap f a (Path.symm p) = Path.symm (loopMap f a p) := by
  simp [loopMap]

/-- The identity function induces the identity on loop spaces. -/
theorem loopMap_idFun (a : A) (p : BaseLoop A a) :
    loopMap id a p = p := by
  unfold loopMap id
  exact Path.congrArg_id p

/-- Composition of functions commutes with loop map. -/
theorem loopMap_comp {C : Type u} (f : A → B) (g : B → C) (a : A)
    (p : BaseLoop A a) :
    loopMap g (f a) (loopMap f a p) = loopMap (g ∘ f) a p := by
  simp [loopMap]

/-- A function induces a map on free loop spaces. -/
def freeLoopMap (f : A → B) : FreeLoopSpace A → FreeLoopSpace B :=
  fun ⟨a, p⟩ => ⟨f a, loopMap f a p⟩

/-- Free loop map commutes with projection. -/
theorem freeLoopMap_proj (f : A → B) (l : FreeLoopSpace A) :
    freeLoopProj (freeLoopMap f l) = f (freeLoopProj l) := rfl

/-! ## Power operations on loop quotients -/

/-- Positive integer power coincides with iterated composition. -/
theorem loopQuot_pow_succ_comp (a : A) (x : LoopQuot A a) (n : Nat) :
    LoopQuot.pow x (n + 1) = LoopQuot.comp (LoopQuot.pow x n) x :=
  rfl

/-- Power is additive. -/
theorem loopQuot_pow_add (a : A) (x : LoopQuot A a) (m n : Nat) :
    LoopQuot.pow x (m + n) = LoopQuot.comp (LoopQuot.pow x m) (LoopQuot.pow x n) :=
  LoopQuot.pow_add x m n

/-- Integer power is additive. -/
theorem loopQuot_zpow_add (a : A) (x : LoopQuot A a) (m n : Int) :
    LoopQuot.zpow x (m + n) = LoopQuot.comp (LoopQuot.zpow x m) (LoopQuot.zpow x n) :=
  LoopQuot.zpow_add x m n

/-- Integer power negation is inversion. -/
theorem loopQuot_zpow_neg (a : A) (x : LoopQuot A a) (z : Int) :
    LoopQuot.zpow x (-z) = LoopQuot.inv (LoopQuot.zpow x z) :=
  LoopQuot.zpow_neg x z

end LoopSpace
end Homotopy
end Path
end ComputationalPaths
