import ComputationalPaths.Path.Basic.Univalence

/-!
This script demonstrates that `ComputationalPaths.Path.HasUnivalence` (as currently
axiomatised via Lean `Eq` + `Path.transport`) is inconsistent with Lean's built-in
proof irrelevance for `Prop`.

In particular, any `SimpleEquiv Bool Bool` would be forced to act as the identity
because `Bool = Bool` is definitionally reflexive, so `transport` must be the
identity map. Taking the negation equivalence yields a contradiction.

This file is intentionally *not* imported by the library; it is a diagnostic
tool for axiom audits.
-/

namespace ComputationalPaths.Scripts

open ComputationalPaths
open ComputationalPaths.Path
open SimpleEquiv

private def boolNotEquiv : SimpleEquiv Bool Bool where
  toFun := fun b => !b
  invFun := fun b => !b
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

theorem hasUnivalence_is_inconsistent [HasUnivalence.{0}] : False := by
  -- `ua_beta` says transport along the univalence path is `boolNotEquiv.toFun` (= not).
  have hβ := ua_beta (A := Bool) (B := Bool) boolNotEquiv (x := true)

  -- But `Bool = Bool` is a proposition, so any equality proof is equal to `rfl`,
  -- hence transport along `ua boolNotEquiv` agrees with transport along `refl`.
  have ht :
      (ua (A := Bool) (B := Bool) boolNotEquiv).toEq =
        (Path.refl (A := Type 0) Bool).toEq := by
    exact Subsingleton.elim _ _

  have hTransport :
      Path.transport (A := Type 0) (D := fun X => X)
          (ua (A := Bool) (B := Bool) boolNotEquiv) true =
        Path.transport (A := Type 0) (D := fun X => X)
          (Path.refl (A := Type 0) Bool) true := by
    simpa using
      (Path.transport_of_toEq_eq (A := Type 0) (D := fun X => X)
        (p := ua (A := Bool) (B := Bool) boolNotEquiv)
        (q := Path.refl (A := Type 0) Bool) ht true)

  have hFixed : boolNotEquiv.toFun true = true := by
    calc
      boolNotEquiv.toFun true
          = Path.transport (A := Type 0) (D := fun X => X)
              (ua (A := Bool) (B := Bool) boolNotEquiv) true := by
              simpa using hβ.symm
      _ = Path.transport (A := Type 0) (D := fun X => X)
              (Path.refl (A := Type 0) Bool) true := hTransport
      _ = true := rfl

  have hContra : (false : Bool) = true := by
    have h := hFixed
    dsimp [boolNotEquiv] at h
    exact h

  have hNe : (false : Bool) ≠ true := by decide
  exact hNe hContra

end ComputationalPaths.Scripts
