/-
# Factorization systems: lifting properties and orthogonality

Develops the right/left lifting property, orthogonality classes,
small-object-argument structure, and functorial factorizations,
all with `Step` / `RwEq` witnesses on the computational-path data.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Factorization.PathInfrastructure

namespace ComputationalPaths
namespace Factorization

open Path

universe u

variable {A : Type u}

/-! ## Lifting problems and solutions -/

/-- A lifting problem consists of a commutative square. -/
structure LiftingProblem {a b c d : A}
    (i : Path a b) (p : Path c d)
    (top : Path a c) (bot : Path b d) where
  commutes : Path (Path.trans i bot) (Path.trans top p)

/-- A lift (diagonal filler) for a lifting problem. -/
structure LiftSolution {a b c d : A}
    (i : Path a b) (p : Path c d)
    (top : Path a c) (bot : Path b d) where
  lift : Path b c
  upper_triangle : Path (Path.trans i lift) top
  lower_triangle : Path (Path.trans lift p) bot

/-- The left lifting property: `i` has LLP w.r.t. `p`. -/
def HasLLP {a b c d : A} (i : Path a b) (p : Path c d) : Prop :=
  ∀ (top : Path a c) (bot : Path b d),
    LiftingProblem i p top bot →
    Nonempty (LiftSolution i p top bot)

/-- The right lifting property: `p` has RLP w.r.t. `i`. -/
def HasRLP {a b c d : A} (p : Path c d) (i : Path a b) : Prop :=
  HasLLP i p

/-! ## Orthogonality classes -/

/-- The left orthogonal complement: all paths having LLP w.r.t. every element of S. -/
def leftPerp (S : {x y : A} → Path x y → Prop) : {x y : A} → Path x y → Prop :=
  fun {a b} i => ∀ {c d : A} (p : Path c d), S p → HasLLP i p

/-- The right orthogonal complement: all paths having RLP w.r.t. every element of S. -/
def rightPerp (S : {x y : A} → Path x y → Prop) : {x y : A} → Path x y → Prop :=
  fun {c d} p => ∀ {a b : A} (i : Path a b), S i → HasRLP p i

/-- Double right perp contains the original class. -/
theorem rightPerp_rightPerp_contains
    (S : {x y : A} → Path x y → Prop) {a b : A} (f : Path a b)
    (hf : S f) : rightPerp (leftPerp S) f :=
  fun i hi => hi f hf

/-- Double left perp contains the original class. -/
theorem leftPerp_leftPerp_contains
    (S : {x y : A} → Path x y → Prop) {a b : A} (f : Path a b)
    (hf : S f) : leftPerp (rightPerp S) f :=
  fun p hp => hp f hf

/-! ## Closure properties of lifting classes -/

/-- The left class is closed under composition with refl (left unit). -/
theorem llp_refl_left {a b c d : A} (i : Path a b) (p : Path c d)
    (h : HasLLP i p) :
    HasLLP (Path.trans (Path.refl a) i) p := by
  intro top bot prob
  have : Path.trans (Path.refl a) i = i := Path.trans_refl_left i
  rw [this] at prob ⊢
  exact h top bot prob

/-- The left class is closed under composition with refl (right unit). -/
theorem llp_refl_right {a b c d : A} (i : Path a b) (p : Path c d)
    (h : HasLLP i p) :
    HasLLP (Path.trans i (Path.refl b)) p := by
  intro top bot prob
  have : Path.trans i (Path.refl b) = i := Path.trans_refl_right i
  rw [this] at prob ⊢
  exact h top bot prob

/-- Reflexivity paths lift trivially: the lift is just `top`. -/
noncomputable def refl_lift_solution {a : A} {c d : A} (p : Path c d)
    (top : Path a c) (bot : Path a d)
    (comm : Path (Path.trans (Path.refl a) bot) (Path.trans top p)) :
    LiftSolution (Path.refl a) p top bot where
  lift := top
  upper_triangle := Path.stepChain (Path.trans_refl_left top)
  lower_triangle := by
    have h1 : Path.trans (Path.refl a) bot = bot := Path.trans_refl_left bot
    have h2 := comm.toEq
    rw [h1] at h2
    exact Path.stepChain h2.symm

/-! ## Functorial factorization -/

/-- A functorial factorization assigns to each path a factorization
    that is natural w.r.t. path composition. -/
structure FunctorialFactorization where
  leftClass  : {a b : A} → Path a b → Prop
  rightClass : {a b : A} → Path a b → Prop
  mid        : {a b : A} → Path a b → A
  leftPart   : {a b : A} → (f : Path a b) → Path a (mid f)
  rightPart  : {a b : A} → (f : Path a b) → Path (mid f) b
  factor_eq  : {a b : A} → (f : Path a b) →
    Path (Path.trans (leftPart f) (rightPart f)) f
  left_mem   : {a b : A} → (f : Path a b) → leftClass (leftPart f)
  right_mem  : {a b : A} → (f : Path a b) → rightClass (rightPart f)
  left_unit  : {a b : A} → (f : Path a b) →
    Path.Step (Path.trans (Path.refl a) (leftPart f)) (leftPart f)
  right_unit : {a b : A} → (f : Path a b) →
    Path.Step (Path.trans (rightPart f) (Path.refl b)) (rightPart f)

namespace FunctorialFactorization

variable (F : @FunctorialFactorization A)

/-- Left unit law as RwEq. -/
noncomputable def left_unit_rweq {a b : A} (f : Path a b) :
    RwEq (Path.trans (Path.refl a) (F.leftPart f)) (F.leftPart f) :=
  rweq_of_step (F.left_unit f)

/-- Right unit law as RwEq. -/
noncomputable def right_unit_rweq {a b : A} (f : Path a b) :
    RwEq (Path.trans (F.rightPart f) (Path.refl b)) (F.rightPart f) :=
  rweq_of_step (F.right_unit f)

/-- Associativity of the factored composite with a third path. -/
noncomputable def factor_assoc_rweq {a b c : A} (f : Path a b) (g : Path b c) :
    RwEq (Path.trans (Path.trans (F.leftPart f) (F.rightPart f)) g)
         (Path.trans (F.leftPart f) (Path.trans (F.rightPart f) g)) :=
  rweq_of_step (Step.trans_assoc (F.leftPart f) (F.rightPart f) g)

end FunctorialFactorization

/-! ## Retract closure -/

/-- A retract diagram: `f` is a retract of `g` in the arrow category. -/
structure IsRetract {a b c d : A}
    (f : Path a b) (g : Path c d) where
  topSec  : Path a c
  topRet  : Path c a
  botSec  : Path b d
  botRet  : Path d b
  sec_ret_top : Path (Path.trans topSec topRet) (Path.refl a)
  sec_ret_bot : Path (Path.trans botSec botRet) (Path.refl b)
  sq_left  : Path (Path.trans topSec g) (Path.trans f botSec)
  sq_right : Path (Path.trans topRet f) (Path.trans g botRet)

/-- Identity is a retract of itself. -/
noncomputable def isRetract_self {a b : A} (f : Path a b) : IsRetract f f where
  topSec  := Path.refl a
  topRet  := Path.refl a
  botSec  := Path.refl b
  botRet  := Path.refl b
  sec_ret_top := Path.stepChain (Path.trans_refl_left (Path.refl a))
  sec_ret_bot := Path.stepChain (Path.trans_refl_left (Path.refl b))
  sq_left  := Path.trans
    (Path.stepChain (Path.trans_refl_left f))
    (Path.symm (Path.stepChain (Path.trans_refl_right f)))
  sq_right := Path.trans
    (Path.stepChain (Path.trans_refl_left f))
    (Path.symm (Path.stepChain (Path.trans_refl_right f)))

/-- A WFS left class is closed under composition with retract data. -/
theorem wfs_left_comp_closed (W : WeakFactorizationSystemPaths A)
    {a b c d : A} {g : Path c d}
    (f₁ : Path a c) (f₂ : Path d b)
    (hg : W.leftClass g)
    (hf₁ : W.leftClass f₁) (hf₂ : W.leftClass f₂) :
    W.leftClass (Path.trans (Path.trans f₁ g) f₂) :=
  W.left_closed_trans (Path.trans f₁ g) f₂
    (W.left_closed_trans f₁ g hf₁ hg)
    hf₂

/-! ## Cylinder and cocylinder factorizations -/

/-- A cylinder factorization on `f` records i₀, i₁ : A → Cyl and p : Cyl → B. -/
structure CylinderFactorization {a b : A} (f : Path a b) where
  cyl    : A
  i₀     : Path a cyl
  i₁     : Path a cyl
  proj   : Path cyl b
  factor : Path (Path.trans i₀ proj) f
  unit_i₀ : Path.Step (Path.trans (Path.refl a) i₀) i₀
  unit_proj : Path.Step (Path.trans proj (Path.refl b)) proj

/-- A cocylinder (path-object) factorization. -/
structure CocylinderFactorization {a b : A} (f : Path a b) where
  cocyl  : A
  inc    : Path a cocyl
  ev₀    : Path cocyl b
  ev₁    : Path cocyl b
  factor : Path (Path.trans inc ev₀) f
  unit_inc : Path.Step (Path.trans (Path.refl a) inc) inc
  unit_ev₀ : Path.Step (Path.trans ev₀ (Path.refl b)) ev₀

/-- The trivial cylinder factorization using identity paths. -/
noncomputable def trivialCylinder {a b : A} (f : Path a b) :
    CylinderFactorization f where
  cyl    := a
  i₀     := Path.refl a
  i₁     := Path.refl a
  proj   := f
  factor := Path.stepChain (Path.trans_refl_left f)
  unit_i₀ := Step.trans_refl_left (Path.refl a)
  unit_proj := Step.trans_refl_right f

/-- RwEq coherences for cylinder factorizations. -/
noncomputable def cylinder_unit_i₀_rweq {a b : A} (f : Path a b)
    (C : CylinderFactorization f) :
    RwEq (Path.trans (Path.refl a) C.i₀) C.i₀ :=
  rweq_of_step C.unit_i₀

noncomputable def cylinder_unit_proj_rweq {a b : A} (f : Path a b)
    (C : CylinderFactorization f) :
    RwEq (Path.trans C.proj (Path.refl b)) C.proj :=
  rweq_of_step C.unit_proj

/-- Cylinder associativity with external composition. -/
noncomputable def cylinder_assoc_rweq {a b c : A} (f : Path a b) (g : Path b c)
    (C : CylinderFactorization f) :
    RwEq (Path.trans (Path.trans C.i₀ C.proj) g)
         (Path.trans C.i₀ (Path.trans C.proj g)) :=
  rweq_of_step (Step.trans_assoc C.i₀ C.proj g)

end Factorization
end ComputationalPaths
