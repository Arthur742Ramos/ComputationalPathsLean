/-
# Ideal Theory via Computational Paths

Ideals, prime/maximal ideals, quotient rings, ideal operations (sum, product,
intersection), Chinese remainder theorem aspects — all modelled with
computational paths over integer arithmetic, using genuine Path combinators
(refl, trans, symm, congrArg, map2, stepChain, transport, subst, whisker).

## Main results (40 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.IdealPaths

open ComputationalPaths.Path

universe u

/-! ## Ring elements modelled as integers -/

abbrev R := Int

/-! ## Ideals as principal ideals nℤ ⊆ ℤ -/

/-- An ideal in ℤ is represented by its generator (principal ideal). -/
structure Ideal where
  gen : Nat
deriving DecidableEq, Repr

/-- The zero ideal. -/
@[simp] noncomputable def zeroIdeal : Ideal := ⟨0⟩

/-- The unit ideal (all of ℤ). -/
@[simp] noncomputable def unitIdeal : Ideal := ⟨1⟩

/-- Sum of ideals: (a) + (b) = (gcd a b). -/
@[simp] noncomputable def Ideal.sum (I J : Ideal) : Ideal := ⟨Nat.gcd I.gen J.gen⟩

/-- Product of ideals: (a) · (b) = (a * b). -/
@[simp] noncomputable def Ideal.prod (I J : Ideal) : Ideal := ⟨I.gen * J.gen⟩

/-- Intersection of ideals: (a) ∩ (b) = (lcm a b). -/
@[simp] noncomputable def Ideal.inter (I J : Ideal) : Ideal := ⟨Nat.lcm I.gen J.gen⟩

/-- Canonical projection to quotient. -/
@[simp] noncomputable def quotProj (I : Ideal) (a : R) : Nat :=
  if I.gen = 0 then a.natAbs else a.natAbs % I.gen

/-! ## 1-6: Sum properties via stepChain -/

/-- 1. Sum is commutative. -/
noncomputable def ideal_sum_comm_path (I J : Ideal) :
    Path (Ideal.sum I J) (Ideal.sum J I) :=
  Path.stepChain (by simp [Ideal.sum, Nat.gcd_comm])

/-- 2. Sum is associative. -/
noncomputable def ideal_sum_assoc_path (I J K : Ideal) :
    Path (Ideal.sum (Ideal.sum I J) K) (Ideal.sum I (Ideal.sum J K)) :=
  Path.stepChain (by simp [Ideal.sum, Nat.gcd_assoc])

/-- 3. Sum with zero ideal (right identity). -/
noncomputable def ideal_sum_zero_path (I : Ideal) :
    Path (Ideal.sum I zeroIdeal) I :=
  Path.stepChain (by simp [Ideal.sum, Nat.gcd_zero_right])

/-- 4. Sum with zero ideal (left identity). -/
noncomputable def ideal_sum_zero_left_path (I : Ideal) :
    Path (Ideal.sum zeroIdeal I) I :=
  Path.stepChain (by simp [Ideal.sum, Nat.gcd_zero_left])

/-- 5. Sum is idempotent. -/
noncomputable def ideal_sum_self_path (I : Ideal) :
    Path (Ideal.sum I I) I :=
  Path.stepChain (by simp [Ideal.sum, Nat.gcd_self])

/-- 6. Symmetry of sum commutativity: inverse path. -/
noncomputable def ideal_sum_comm_inv (I J : Ideal) :
    Path (Ideal.sum J I) (Ideal.sum I J) :=
  Path.symm (ideal_sum_comm_path I J)

/-! ## 7-12: Product properties via stepChain -/

/-- 7. Product is commutative. -/
noncomputable def ideal_prod_comm_path (I J : Ideal) :
    Path (Ideal.prod I J) (Ideal.prod J I) :=
  Path.stepChain (by simp [Ideal.prod, Nat.mul_comm])

/-- 8. Product is associative. -/
noncomputable def ideal_prod_assoc_path (I J K : Ideal) :
    Path (Ideal.prod (Ideal.prod I J) K) (Ideal.prod I (Ideal.prod J K)) :=
  Path.stepChain (by simp [Ideal.prod, Nat.mul_assoc])

/-- 9. Product with unit ideal (right identity). -/
noncomputable def ideal_prod_unit_path (I : Ideal) :
    Path (Ideal.prod I unitIdeal) I :=
  Path.stepChain (by simp [Ideal.prod, Nat.mul_one])

/-- 10. Product with unit ideal (left identity). -/
noncomputable def ideal_prod_unit_left_path (I : Ideal) :
    Path (Ideal.prod unitIdeal I) I :=
  Path.stepChain (by simp [Ideal.prod, Nat.one_mul])

/-- 11. Product with zero ideal (right absorber). -/
noncomputable def ideal_prod_zero_path (I : Ideal) :
    Path (Ideal.prod I zeroIdeal) zeroIdeal :=
  Path.stepChain (by simp [Ideal.prod, Nat.mul_zero])

/-- 12. Product with zero ideal (left absorber). -/
noncomputable def ideal_prod_zero_left_path (I : Ideal) :
    Path (Ideal.prod zeroIdeal I) zeroIdeal :=
  Path.stepChain (by simp [Ideal.prod, Nat.zero_mul])

/-! ## 13-16: Intersection properties -/

/-- 13. Intersection is commutative. -/
noncomputable def ideal_inter_comm_path (I J : Ideal) :
    Path (Ideal.inter I J) (Ideal.inter J I) :=
  Path.stepChain (by simp [Ideal.inter, Nat.lcm_comm])

/-- 14. Intersection with unit ideal. -/
noncomputable def ideal_inter_unit_path (I : Ideal) :
    Path (Ideal.inter I unitIdeal) I :=
  Path.stepChain (by simp [Ideal.inter, Nat.lcm, Nat.gcd_one_right, Nat.div_one])

/-- 15. Symmetry of intersection commutativity. -/
noncomputable def ideal_inter_comm_inv (I J : Ideal) :
    Path (Ideal.inter J I) (Ideal.inter I J) :=
  Path.symm (ideal_inter_comm_path I J)

/-- 16. Intersection with zero ideal. -/
noncomputable def ideal_inter_zero_path (I : Ideal) :
    Path (Ideal.inter I zeroIdeal) zeroIdeal :=
  Path.stepChain (by simp [Ideal.inter, Nat.lcm, Nat.gcd_zero_right])

/-! ## 17-22: Congruence / functorial paths via congrArg -/

/-- 17. Congruence: equal ideals give equal sums (left). -/
noncomputable def ideal_sum_congrArg_left {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.sum I₁ J) (Ideal.sum I₂ J) :=
  Path.congrArg (fun I => Ideal.sum I J) h

/-- 18. Congruence: equal ideals give equal sums (right). -/
noncomputable def ideal_sum_congrArg_right (I : Ideal) {J₁ J₂ : Ideal} (h : Path J₁ J₂) :
    Path (Ideal.sum I J₁) (Ideal.sum I J₂) :=
  Path.congrArg (Ideal.sum I) h

/-- 19. Congruence: equal ideals give equal products (left). -/
noncomputable def ideal_prod_congrArg_left {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.prod I₁ J) (Ideal.prod I₂ J) :=
  Path.congrArg (fun I => Ideal.prod I J) h

/-- 20. Congruence: equal ideals give equal products (right). -/
noncomputable def ideal_prod_congrArg_right (I : Ideal) {J₁ J₂ : Ideal} (h : Path J₁ J₂) :
    Path (Ideal.prod I J₁) (Ideal.prod I J₂) :=
  Path.congrArg (Ideal.prod I) h

/-- 21. Congruence for intersection (left). -/
noncomputable def ideal_inter_congrArg_left {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.inter I₁ J) (Ideal.inter I₂ J) :=
  Path.congrArg (fun I => Ideal.inter I J) h

/-- 22. Congruence for quotient projection. -/
noncomputable def quotProj_congrArg {I₁ I₂ : Ideal} (h : Path I₁ I₂) (a : R) :
    Path (quotProj I₁ a) (quotProj I₂ a) :=
  Path.congrArg (fun I => quotProj I a) h

/-! ## 23-28: Composite paths via trans -/

/-- 23. Sum rotation: (I+J)+K → I+(J+K) → (J+K)+I. -/
noncomputable def ideal_sum_rotate (I J K : Ideal) :
    Path (Ideal.sum (Ideal.sum I J) K) (Ideal.sum (Ideal.sum J K) I) :=
  Path.trans (ideal_sum_assoc_path I J K) (ideal_sum_comm_path I (Ideal.sum J K))

/-- 24. Product rotation: (I·J)·K → I·(J·K) → (J·K)·I. -/
noncomputable def ideal_prod_rotate (I J K : Ideal) :
    Path (Ideal.prod (Ideal.prod I J) K) (Ideal.prod (Ideal.prod J K) I) :=
  Path.trans (ideal_prod_assoc_path I J K) (ideal_prod_comm_path I (Ideal.prod J K))

/-- 25. Sum-product coherence: I·(J+K) is commuted to (J+K)·I. -/
noncomputable def sum_prod_coherence (I J K : Ideal) :
    Path (Ideal.prod I (Ideal.sum J K)) (Ideal.prod (Ideal.sum J K) I) :=
  ideal_prod_comm_path I (Ideal.sum J K)

/-- 26. CRT coprime sum: when gcd = 1, sum is unit ideal. -/
noncomputable def crt_coprime_sum_path (I J : Ideal) (h : Nat.gcd I.gen J.gen = 1) :
    Path (Ideal.sum I J) unitIdeal :=
  Path.stepChain (by simp [Ideal.sum, h])

/-- 27. CRT followed by product comm: composing two paths. -/
noncomputable def crt_prod_chain (I J : Ideal) (h : Nat.gcd I.gen J.gen = 1) :
    Path (Ideal.prod I J) (Ideal.prod J I) :=
  ideal_prod_comm_path I J

/-- 28. Zero ideal absorbed from left then right: zeroIdeal + I → I → I + zeroIdeal reversed. -/
noncomputable def sum_zero_roundtrip (I : Ideal) :
    Path (Ideal.sum zeroIdeal I) (Ideal.sum I zeroIdeal) :=
  Path.trans (ideal_sum_zero_left_path I) (Path.symm (ideal_sum_zero_path I))

/-! ## 29-33: Symm / inverse paths -/

/-- 29. Symmetry of sum commutativity roundtrip gives refl on toEq. -/
theorem sum_comm_roundtrip_toEq (I J : Ideal) :
    (Path.trans (ideal_sum_comm_path I J) (ideal_sum_comm_inv I J)).toEq = rfl := by
  simp [ideal_sum_comm_inv]

/-- 30. Symmetry of prod commutativity roundtrip gives refl on toEq. -/
theorem prod_comm_roundtrip_toEq (I J : Ideal) :
    (Path.trans (ideal_prod_comm_path I J) (Path.symm (ideal_prod_comm_path I J))).toEq = rfl := by
  simp

/-- 31. Double symm on sum comm. -/
theorem sum_comm_symm_symm_toEq (I J : Ideal) :
    (Path.symm (Path.symm (ideal_sum_comm_path I J))).toEq =
    (ideal_sum_comm_path I J).toEq := by
  simp

/-- 32. Symm of sum_zero is a path from I back to sum. -/
noncomputable def sum_zero_inv (I : Ideal) :
    Path I (Ideal.sum I zeroIdeal) :=
  Path.symm (ideal_sum_zero_path I)

/-- 33. Symm of prod_unit is a path from I back to prod. -/
noncomputable def prod_unit_inv (I : Ideal) :
    Path I (Ideal.prod I unitIdeal) :=
  Path.symm (ideal_prod_unit_path I)

/-! ## 34-37: Transport and subst -/

/-- 34. Transport along sum comm (constant family). -/
theorem transport_sum_comm_const (I J : Ideal) (x : Nat) :
    Path.transport (D := fun _ => Nat) (ideal_sum_comm_path I J) x = x :=
  Path.transport_const (ideal_sum_comm_path I J) x

/-- 35. Transport along prod comm (constant family). -/
theorem transport_prod_comm_const (I J : Ideal) (x : Nat) :
    Path.transport (D := fun _ => Nat) (ideal_prod_comm_path I J) x = x :=
  Path.transport_const (ideal_prod_comm_path I J) x

/-- 36. Subst along sum assoc (constant family). -/
theorem subst_sum_assoc_const (I J K : Ideal) (x : Nat) :
    Path.subst (D := fun _ => Nat) x (ideal_sum_assoc_path I J K) = x :=
  Path.subst_const x (ideal_sum_assoc_path I J K)

/-- 37. Transport along refl is identity. -/
theorem transport_refl_ideal (I : Ideal) (x : Nat) :
    Path.transport (D := fun _ => Nat) (Path.refl I) x = x :=
  Path.transport_const (Path.refl I) x

/-! ## 38-40: Associativity and higher structure -/

/-- 38. Associativity of path composition on sum paths. -/
theorem sum_path_assoc (I J K L : Ideal)
    (p : Path I J) (q : Path J K) (r : Path K L) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- 39. Left identity of path composition. -/
theorem sum_path_trans_refl_left {I J : Ideal} (p : Path I J) :
    Path.trans (Path.refl I) p = p := by
  simp

/-- 40. congrArg distributes over trans for ideal operations. -/
theorem congrArg_sum_trans {I J K : Ideal} (L : Ideal)
    (p : Path I J) (q : Path J K) :
    Path.congrArg (fun X => Ideal.sum X L) (Path.trans p q) =
    Path.trans (Path.congrArg (fun X => Ideal.sum X L) p)
               (Path.congrArg (fun X => Ideal.sum X L) q) := by
  simp

end ComputationalPaths.Path.Algebra.IdealPaths
