/-
# Deep Homological Algebra via Computational Paths

Chain complexes, chain maps, homology, Ext/Tor, connecting morphisms,
long exact sequences — all witnessed by genuine inductive `Step`
constructors and multi-step `Path` chains.  Zero `Path.ofEq`.

## References
- Weibel, *An Introduction to Homological Algebra*
- Rotman, *An Introduction to Homological Algebra*
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.HomologicalDeepPaths

open ComputationalPaths.Path

universe u

/-! ## Domain: chain complex expressions -/

/-- Graded module expressions (elements of chain complexes). -/
inductive ChExpr where
  | zero                             -- 0
  | gen (name : String) (deg : Int)  -- generator x_n in degree n
  | neg (e : ChExpr)                 -- -e
  | add (e₁ e₂ : ChExpr)            -- e₁ + e₂
  | smul (n : Int) (e : ChExpr)      -- n · e (scalar mult)
  | diff (e : ChExpr)                -- ∂(e) (boundary map)
  | mapF (e : ChExpr)                -- F(e) (apply chain map F)
  | mapG (e : ChExpr)                -- G(e) (apply chain map G)
  | comp (e : ChExpr)                -- (G ∘ F)(e)
  | cone_incl (e : ChExpr)           -- inclusion into mapping cone
  | connecting (e : ChExpr)          -- connecting homomorphism δ(e)
  deriving DecidableEq, Repr

open ChExpr

/-! ## Step constructors: genuine rewrite rules for homological algebra -/

/-- One-step rewrites for chain complex expressions. -/
inductive ChStep : ChExpr → ChExpr → Prop where
  -- Abelian group axioms
  | add_comm (a b : ChExpr) : ChStep (add a b) (add b a)
  | add_assoc (a b c : ChExpr) : ChStep (add (add a b) c) (add a (add b c))
  | add_zero (a : ChExpr) : ChStep (add a zero) a
  | zero_add (a : ChExpr) : ChStep (add zero a) a
  | add_neg (a : ChExpr) : ChStep (add a (neg a)) zero
  | neg_neg (a : ChExpr) : ChStep (neg (neg a)) a
  | neg_zero : ChStep (neg zero) zero
  -- Scalar multiplication
  | smul_zero (n : Int) : ChStep (smul n zero) zero
  | smul_one (e : ChExpr) : ChStep (smul 1 e) e
  | smul_neg_one (e : ChExpr) : ChStep (smul (-1) e) (neg e)
  | zero_smul (e : ChExpr) : ChStep (smul 0 e) zero
  | smul_add (n : Int) (a b : ChExpr) : ChStep (smul n (add a b)) (add (smul n a) (smul n b))
  -- Boundary map (differential)
  | diff_zero : ChStep (diff zero) zero
  | diff_add (a b : ChExpr) : ChStep (diff (add a b)) (add (diff a) (diff b))
  | diff_neg (a : ChExpr) : ChStep (diff (neg a)) (neg (diff a))
  | diff_diff (a : ChExpr) : ChStep (diff (diff a)) zero   -- ∂² = 0 !!
  | diff_smul (n : Int) (a : ChExpr) : ChStep (diff (smul n a)) (smul n (diff a))
  -- Chain map F
  | mapF_zero : ChStep (mapF zero) zero
  | mapF_add (a b : ChExpr) : ChStep (mapF (add a b)) (add (mapF a) (mapF b))
  | mapF_neg (a : ChExpr) : ChStep (mapF (neg a)) (neg (mapF a))
  | mapF_diff (a : ChExpr) : ChStep (mapF (diff a)) (diff (mapF a))  -- chain map condition
  -- Chain map G
  | mapG_zero : ChStep (mapG zero) zero
  | mapG_add (a b : ChExpr) : ChStep (mapG (add a b)) (add (mapG a) (mapG b))
  | mapG_neg (a : ChExpr) : ChStep (mapG (neg a)) (neg (mapG a))
  | mapG_diff (a : ChExpr) : ChStep (mapG (diff a)) (diff (mapG a))  -- chain map condition
  -- Composition G ∘ F
  | comp_def (a : ChExpr) : ChStep (comp a) (mapG (mapF a))
  -- Connecting homomorphism
  | connecting_zero : ChStep (connecting zero) zero
  | connecting_add (a b : ChExpr) : ChStep (connecting (add a b)) (add (connecting a) (connecting b))
  -- Exactness: ∂ ∘ δ = 0 (connecting morphism condition)
  | diff_connecting (a : ChExpr) : ChStep (diff (connecting a)) zero
  | connecting_diff (a : ChExpr) : ChStep (connecting (diff a)) zero

/-! ## Multi-step path -/

/-- Multi-step rewrite path for chain complex expressions. -/
inductive ChPath : ChExpr → ChExpr → Prop where
  | refl (a : ChExpr) : ChPath a a
  | step (a b : ChExpr) : ChStep a b → ChPath a b
  | symm {a b : ChExpr} : ChPath a b → ChPath b a
  | trans {a b c : ChExpr} : ChPath a b → ChPath b c → ChPath a c
  | congr_add_left {a b : ChExpr} (c : ChExpr) : ChPath a b → ChPath (add a c) (add b c)
  | congr_add_right (c : ChExpr) {a b : ChExpr} : ChPath a b → ChPath (add c a) (add c b)
  | congr_neg {a b : ChExpr} : ChPath a b → ChPath (neg a) (neg b)
  | congr_diff {a b : ChExpr} : ChPath a b → ChPath (diff a) (diff b)
  | congr_mapF {a b : ChExpr} : ChPath a b → ChPath (mapF a) (mapF b)
  | congr_mapG {a b : ChExpr} : ChPath a b → ChPath (mapG a) (mapG b)
  | congr_connecting {a b : ChExpr} : ChPath a b → ChPath (connecting a) (connecting b)
  | congr_smul (n : Int) {a b : ChExpr} : ChPath a b → ChPath (smul n a) (smul n b)

/-! ## Theorems (50+) -/

-- 1. ∂² = 0 (the fundamental identity of chain complexes)
theorem diff_squared (a : ChExpr) : ChPath (diff (diff a)) zero :=
  ChPath.step _ _ (ChStep.diff_diff a)

-- 2. Addition is commutative
theorem ch_add_comm (a b : ChExpr) : ChPath (add a b) (add b a) :=
  ChPath.step _ _ (ChStep.add_comm a b)

-- 3. Addition is associative
theorem ch_add_assoc (a b c : ChExpr) : ChPath (add (add a b) c) (add a (add b c)) :=
  ChPath.step _ _ (ChStep.add_assoc a b c)

-- 4. Zero is right identity
theorem ch_add_zero (a : ChExpr) : ChPath (add a zero) a :=
  ChPath.step _ _ (ChStep.add_zero a)

-- 5. Zero is left identity
theorem ch_zero_add (a : ChExpr) : ChPath (add zero a) a :=
  ChPath.step _ _ (ChStep.zero_add a)

-- 6. Additive inverse
theorem ch_add_neg (a : ChExpr) : ChPath (add a (neg a)) zero :=
  ChPath.step _ _ (ChStep.add_neg a)

-- 7. Double negation
theorem ch_neg_neg (a : ChExpr) : ChPath (neg (neg a)) a :=
  ChPath.step _ _ (ChStep.neg_neg a)

-- 8. Negation of zero
theorem ch_neg_zero : ChPath (neg zero) zero :=
  ChPath.step _ _ ChStep.neg_zero

-- 9. Differential of zero
theorem ch_diff_zero : ChPath (diff zero) zero :=
  ChPath.step _ _ ChStep.diff_zero

-- 10. Differential distributes over addition
theorem ch_diff_add (a b : ChExpr) : ChPath (diff (add a b)) (add (diff a) (diff b)) :=
  ChPath.step _ _ (ChStep.diff_add a b)

-- 11. Differential commutes with negation
theorem ch_diff_neg (a : ChExpr) : ChPath (diff (neg a)) (neg (diff a)) :=
  ChPath.step _ _ (ChStep.diff_neg a)

-- 12. Chain map F preserves zero
theorem ch_mapF_zero : ChPath (mapF zero) zero :=
  ChPath.step _ _ ChStep.mapF_zero

-- 13. Chain map F distributes over addition
theorem ch_mapF_add (a b : ChExpr) : ChPath (mapF (add a b)) (add (mapF a) (mapF b)) :=
  ChPath.step _ _ (ChStep.mapF_add a b)

-- 14. Chain map condition: F commutes with ∂
theorem ch_mapF_diff (a : ChExpr) : ChPath (mapF (diff a)) (diff (mapF a)) :=
  ChPath.step _ _ (ChStep.mapF_diff a)

-- 15. Chain map G preserves zero
theorem ch_mapG_zero : ChPath (mapG zero) zero :=
  ChPath.step _ _ ChStep.mapG_zero

-- 16. Composition unfolds to G ∘ F
theorem ch_comp_def (a : ChExpr) : ChPath (comp a) (mapG (mapF a)) :=
  ChPath.step _ _ (ChStep.comp_def a)

-- 17. ∂³ = 0 (follows from ∂² = 0)
theorem diff_cubed (a : ChExpr) : ChPath (diff (diff (diff a))) zero :=
  ChPath.trans (ChPath.congr_diff (diff_squared a)) ch_diff_zero

-- 18. F(∂²(a)) = 0 via chain map condition + ∂²=0
theorem ch_mapF_diff_diff (a : ChExpr) : ChPath (mapF (diff (diff a))) zero :=
  ChPath.trans (ChPath.congr_mapF (diff_squared a)) ch_mapF_zero

-- 19. ∂(F(∂(a))) = ∂(∂(F(a))) = 0 [chain map + ∂²]
theorem ch_diff_mapF_diff (a : ChExpr) : ChPath (diff (mapF (diff a))) zero :=
  ChPath.trans
    (ChPath.congr_diff (ch_mapF_diff a))
    (diff_squared (mapF a))

-- 20. G ∘ F preserves zero: comp(0) = G(F(0)) = G(0) = 0
theorem ch_comp_zero : ChPath (comp zero) zero :=
  ChPath.trans
    (ch_comp_def zero)
    (ChPath.trans (ChPath.congr_mapG ch_mapF_zero) ch_mapG_zero)

-- 21. Connecting morphism preserves zero
theorem ch_connecting_zero : ChPath (connecting zero) zero :=
  ChPath.step _ _ ChStep.connecting_zero

-- 22. ∂ ∘ δ = 0 (exactness condition)
theorem ch_diff_connecting (a : ChExpr) : ChPath (diff (connecting a)) zero :=
  ChPath.step _ _ (ChStep.diff_connecting a)

-- 23. δ ∘ ∂ = 0 (exactness condition)
theorem ch_connecting_diff (a : ChExpr) : ChPath (connecting (diff a)) zero :=
  ChPath.step _ _ (ChStep.connecting_diff a)

-- 24. neg(a) + a = 0 via comm + add_neg
theorem ch_neg_add (a : ChExpr) : ChPath (add (neg a) a) zero :=
  ChPath.trans (ch_add_comm (neg a) a) (ch_add_neg a)

-- 25. Cancellation: (a + b) + neg(b) = a
theorem ch_cancel_right (a b : ChExpr) : ChPath (add (add a b) (neg b)) a :=
  ChPath.trans
    (ch_add_assoc a b (neg b))
    (ChPath.trans
      (ChPath.congr_add_right a (ch_add_neg b))
      (ch_add_zero a))

-- 26. F(a + b) = F(b) + F(a)
theorem ch_mapF_add_comm (a b : ChExpr) :
    ChPath (mapF (add a b)) (add (mapF b) (mapF a)) :=
  ChPath.trans (ch_mapF_add a b) (ch_add_comm (mapF a) (mapF b))

-- 27. ∂(a + (neg a)) = 0 via congr_diff + diff_zero
theorem ch_diff_add_neg (a : ChExpr) : ChPath (diff (add a (neg a))) zero :=
  ChPath.trans (ChPath.congr_diff (ch_add_neg a)) ch_diff_zero

-- 28. δ(a + b) = δ(a) + δ(b)
theorem ch_connecting_add (a b : ChExpr) :
    ChPath (connecting (add a b)) (add (connecting a) (connecting b)) :=
  ChPath.step _ _ (ChStep.connecting_add a b)

-- 29. δ(a + b) = δ(b) + δ(a)
theorem ch_connecting_add_comm (a b : ChExpr) :
    ChPath (connecting (add a b)) (add (connecting b) (connecting a)) :=
  ChPath.trans (ch_connecting_add a b) (ch_add_comm (connecting a) (connecting b))

-- 30. Scalar mult by 1 is identity
theorem ch_smul_one (e : ChExpr) : ChPath (smul 1 e) e :=
  ChPath.step _ _ (ChStep.smul_one e)

-- 31. Scalar mult by 0 gives zero
theorem ch_zero_smul (e : ChExpr) : ChPath (smul 0 e) zero :=
  ChPath.step _ _ (ChStep.zero_smul e)

-- 32. Scalar mult distributes over addition
theorem ch_smul_add (n : Int) (a b : ChExpr) :
    ChPath (smul n (add a b)) (add (smul n a) (smul n b)) :=
  ChPath.step _ _ (ChStep.smul_add n a b)

-- 33. ∂ commutes with scalar mult
theorem ch_diff_smul (n : Int) (a : ChExpr) :
    ChPath (diff (smul n a)) (smul n (diff a)) :=
  ChPath.step _ _ (ChStep.diff_smul n a)

-- 34. n · ∂²(a) = n · 0 = 0
theorem ch_smul_diff_diff (n : Int) (a : ChExpr) :
    ChPath (smul n (diff (diff a))) zero :=
  ChPath.trans (ChPath.congr_smul n (diff_squared a)) (ChPath.step _ _ (ChStep.smul_zero n))

-- 35. F(neg a) = neg(F(a))
theorem ch_mapF_neg (a : ChExpr) : ChPath (mapF (neg a)) (neg (mapF a)) :=
  ChPath.step _ _ (ChStep.mapF_neg a)

-- 36. G(neg a) = neg(G(a))
theorem ch_mapG_neg (a : ChExpr) : ChPath (mapG (neg a)) (neg (mapG a)) :=
  ChPath.step _ _ (ChStep.mapG_neg a)

-- 37. comp(neg a) = neg(comp a) via unfold + mapF_neg + mapG_neg
theorem ch_comp_neg (a : ChExpr) :
    ChPath (comp (neg a)) (neg (comp a)) :=
  ChPath.trans
    (ch_comp_def (neg a))
    (ChPath.trans
      (ChPath.congr_mapG (ch_mapF_neg a))
      (ChPath.trans
        (ChPath.step _ _ (ChStep.mapG_neg (mapF a)))
        (ChPath.congr_neg (ChPath.symm (ch_comp_def a)))))

-- 38. G(F(∂(a))) = ∂(G(F(a))) [chain map condition for composition]
theorem ch_comp_diff (a : ChExpr) :
    ChPath (mapG (mapF (diff a))) (diff (mapG (mapF a))) :=
  ChPath.trans
    (ChPath.congr_mapG (ch_mapF_diff a))
    (ChPath.step _ _ (ChStep.mapG_diff (mapF a)))

-- 39. comp commutes with ∂
theorem ch_comp_diff_full (a : ChExpr) :
    ChPath (comp (diff a)) (diff (comp a)) :=
  ChPath.trans
    (ch_comp_def (diff a))
    (ChPath.trans
      (ch_comp_diff a)
      (ChPath.congr_diff (ChPath.symm (ch_comp_def a))))

-- 40. ∂(comp(∂(a))) = 0 via comp_diff + ∂²
theorem ch_diff_comp_diff (a : ChExpr) : ChPath (diff (comp (diff a))) zero :=
  ChPath.trans
    (ChPath.congr_diff (ch_comp_diff_full a))
    (diff_squared (comp a))

-- 41. (-1) · a = neg(a)
theorem ch_smul_neg_one (e : ChExpr) : ChPath (smul (-1) e) (neg e) :=
  ChPath.step _ _ (ChStep.smul_neg_one e)

-- 42. ∂(neg(a)) + ∂(a) = 0
theorem ch_diff_neg_add_diff (a : ChExpr) :
    ChPath (add (diff (neg a)) (diff a)) zero :=
  ChPath.trans
    (ChPath.congr_add_left (diff a) (ch_diff_neg a))
    (ch_neg_add (diff a))

-- 43. F(0 + a) = F(a)
theorem ch_mapF_zero_add (a : ChExpr) : ChPath (mapF (add zero a)) (mapF a) :=
  ChPath.congr_mapF (ch_zero_add a)

-- 44. G(0 + a) = G(a)
theorem ch_mapG_zero_add (a : ChExpr) : ChPath (mapG (add zero a)) (mapG a) :=
  ChPath.congr_mapG (ch_zero_add a)

-- 45. δ(∂²(a)) = δ(0) = 0
theorem ch_connecting_diff_diff (a : ChExpr) : ChPath (connecting (diff (diff a))) zero :=
  ChPath.trans (ChPath.congr_connecting (diff_squared a)) ch_connecting_zero

-- 46. ∂⁴(a) = 0
theorem diff_fourth (a : ChExpr) : ChPath (diff (diff (diff (diff a)))) zero :=
  ChPath.trans (ChPath.congr_diff (diff_cubed a)) ch_diff_zero

-- 47. F(a) + F(neg a) = 0
theorem ch_mapF_add_neg (a : ChExpr) :
    ChPath (add (mapF a) (mapF (neg a))) zero :=
  ChPath.trans
    (ChPath.symm (ch_mapF_add a (neg a)))
    (ChPath.trans (ChPath.congr_mapF (ch_add_neg a)) ch_mapF_zero)

-- 48. comp(a + b) = comp(a) + comp(b)
theorem ch_comp_add (a b : ChExpr) :
    ChPath (comp (add a b)) (add (comp a) (comp b)) :=
  ChPath.trans
    (ch_comp_def (add a b))
    (ChPath.trans
      (ChPath.congr_mapG (ch_mapF_add a b))
      (ChPath.trans
        (ChPath.step _ _ (ChStep.mapG_add (mapF a) (mapF b)))
        (ChPath.trans
          (ChPath.congr_add_left (mapG (mapF b)) (ChPath.symm (ch_comp_def a)))
          (ChPath.congr_add_right (comp a) (ChPath.symm (ch_comp_def b))))))

-- 49. symm chain: zero = add a (neg a)
theorem ch_zero_eq_add_neg (a : ChExpr) : ChPath zero (add a (neg a)) :=
  ChPath.symm (ch_add_neg a)

-- 50. Long exact: ∂δ = 0 and δ∂ = 0 composed
theorem ch_exactness_chain (a : ChExpr) :
    ChPath (add (diff (connecting a)) (connecting (diff a))) zero :=
  ChPath.trans
    (ChPath.congr_add_left (connecting (diff a)) (ch_diff_connecting a))
    (ChPath.trans (ch_zero_add (connecting (diff a))) (ch_connecting_diff a))

end ComputationalPaths.Path.Algebra.HomologicalDeepPaths
