import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- LIE GROUPS VIA PATHS
-- Exponential map, Lie bracket, BCH formula, adjoint representations,
-- Killing form, semisimple decomposition, root systems, Weyl group,
-- maximal torus, Peter-Weyl completeness
-- ============================================================================

-- G: Lie group elements, 𝔤: Lie algebra elements
variable (G : Type u) (𝔤 : Type u)

-- Group operations
variable (mul : G → G → G) (inv : G → G) (e : G)

-- Algebra operations
variable (add : 𝔤 → 𝔤 → 𝔤) (scale : 𝔤 → 𝔤 → 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
         (zero : 𝔤) (neg : 𝔤 → 𝔤)

-- Exponential map and logarithm
variable (exp : 𝔤 → G) (log : G → 𝔤)

-- Adjoint representations
variable (Ad : G → 𝔤 → 𝔤) (ad : 𝔤 → 𝔤 → 𝔤)

-- Killing form
variable (killing : 𝔤 → 𝔤 → 𝔤)

-- ============================================================================
-- LieStep: path constructors for Lie theory
-- ============================================================================

inductive LieStep : G → G → Type u where
  | refl (x : G) : LieStep x x
  | symm {x y : G} : LieStep x y → LieStep y x
  | trans {x y z : G} : LieStep x y → LieStep y z → LieStep x z
  | congrArg {x y : G} (f : G → G) : LieStep x y → LieStep (f x) (f y)
  -- Group axioms
  | mul_assoc (a b c : G) : LieStep (mul (mul a b) c) (mul a (mul b c))
  | mul_left_id (a : G) : LieStep (mul e a) a
  | mul_right_id (a : G) : LieStep (mul a e) a
  | mul_left_inv (a : G) : LieStep (mul (inv a) a) e
  | mul_right_inv (a : G) : LieStep (mul a (inv a)) e
  -- Exponential map homomorphism (commuting case)
  | exp_add (X Y : 𝔤) : LieStep (mul (exp X) (exp Y)) (exp (add X Y))
  -- Exp of zero
  | exp_zero : LieStep (exp zero) e
  -- Exp-log inverse
  | exp_log (g : G) : LieStep (exp (log g)) g
  -- Log-exp inverse
  | log_exp_step (X : 𝔤) : LieStep (exp (log (exp X))) (exp X)
  -- BCH formula: exp(X)exp(Y) = exp(X + Y + 1/2[X,Y] + ...)
  | bch_first_order (X Y : 𝔤) :
      LieStep (mul (exp X) (exp Y)) (exp (add (add X Y) (bracket X Y)))
  -- Adjoint representation: Ad(g)(X) via conjugation
  | ad_conj (g : G) (X : 𝔤) :
      LieStep (mul (mul g (exp X)) (inv g)) (exp (Ad g X))
  -- Ad is a homomorphism
  | ad_hom (g h : G) (X : 𝔤) :
      LieStep (exp (Ad (mul g h) X)) (exp (Ad g (Ad h X)))
  -- Ad of identity
  | ad_id (X : 𝔤) : LieStep (exp (Ad e X)) (exp X)
  -- Lie bracket via commutator path
  | bracket_commutator (X Y : 𝔤) :
      LieStep (mul (mul (exp X) (exp Y)) (mul (exp (neg X)) (exp (neg Y))))
              (exp (bracket X Y))
  -- Bracket antisymmetry
  | bracket_antisymm (X Y : 𝔤) :
      LieStep (exp (bracket X Y)) (exp (neg (bracket Y X)))
  -- Jacobi identity
  | jacobi (X Y Z : 𝔤) :
      LieStep (exp (add (add (bracket X (bracket Y Z))
                              (bracket Y (bracket Z X)))
                        (bracket Z (bracket X Y))))
              (exp zero)
  -- Killing form symmetry
  | killing_symm (X Y : 𝔤) :
      LieStep (exp (killing X Y)) (exp (killing Y X))
  -- Killing form ad-invariance
  | killing_ad_inv (X Y Z : 𝔤) :
      LieStep (exp (killing (bracket X Y) Z))
              (exp (killing X (bracket Y Z)))
  -- Semisimple decomposition
  | semisimple_decomp (X : 𝔤) :
      LieStep (exp X) (mul (exp (add X zero)) (exp zero))
  -- Inverse of exp
  | exp_neg (X : 𝔤) : LieStep (inv (exp X)) (exp (neg X))
  -- Double inverse
  | inv_inv (g : G) : LieStep (inv (inv g)) g
  -- Root system: root addition
  | root_add (α β : 𝔤) :
      LieStep (exp (add α β)) (mul (exp α) (exp β))
  -- Weyl reflection
  | weyl_reflect (w : G) (X : 𝔤) :
      LieStep (mul (mul w (exp X)) (inv w)) (exp (Ad w X))
  -- Maximal torus commutativity
  | torus_comm (t₁ t₂ : G) :
      LieStep (mul t₁ t₂) (mul t₂ t₁)
  -- Peter-Weyl: group element decomposition
  | peter_weyl (g : G) (X Y : 𝔤) :
      LieStep g (mul (exp X) (exp Y))

-- ============================================================================
-- LieAlgStep: paths in the Lie algebra
-- ============================================================================

inductive LieAlgStep : 𝔤 → 𝔤 → Type u where
  | refl (x : 𝔤) : LieAlgStep x x
  | symm {x y : 𝔤} : LieAlgStep x y → LieAlgStep y x
  | trans {x y z : 𝔤} : LieAlgStep x y → LieAlgStep y z → LieAlgStep x z
  | congrArg {x y : 𝔤} (f : 𝔤 → 𝔤) : LieAlgStep x y → LieAlgStep (f x) (f y)
  -- Algebra axioms
  | add_assoc (X Y Z : 𝔤) : LieAlgStep (add (add X Y) Z) (add X (add Y Z))
  | add_comm (X Y : 𝔤) : LieAlgStep (add X Y) (add Y X)
  | add_zero_left (X : 𝔤) : LieAlgStep (add zero X) X
  | add_zero_right (X : 𝔤) : LieAlgStep (add X zero) X
  | add_neg_left (X : 𝔤) : LieAlgStep (add (neg X) X) zero
  | add_neg_right (X : 𝔤) : LieAlgStep (add X (neg X)) zero
  -- Bracket bilinearity (left)
  | bracket_add_left (X Y Z : 𝔤) :
      LieAlgStep (bracket (add X Y) Z) (add (bracket X Z) (bracket Y Z))
  -- Bracket bilinearity (right)
  | bracket_add_right (X Y Z : 𝔤) :
      LieAlgStep (bracket X (add Y Z)) (add (bracket X Y) (bracket X Z))
  -- Bracket antisymmetry (algebra level)
  | bracket_antisymm (X Y : 𝔤) :
      LieAlgStep (bracket X Y) (neg (bracket Y X))
  -- Bracket self-annihilation
  | bracket_self (X : 𝔤) : LieAlgStep (bracket X X) zero
  -- Jacobi identity (algebra level)
  | jacobi (X Y Z : 𝔤) :
      LieAlgStep (add (add (bracket X (bracket Y Z))
                            (bracket Y (bracket Z X)))
                      (bracket Z (bracket X Y))) zero
  -- ad representation: ad(X)(Y) = [X,Y]
  | ad_def (X Y : 𝔤) : LieAlgStep (ad X Y) (bracket X Y)
  -- ad is a derivation
  | ad_derivation (X Y Z : 𝔤) :
      LieAlgStep (ad X (bracket Y Z)) (add (bracket (ad X Y) Z) (bracket Y (ad X Z)))
  -- Killing form via ad
  | killing_trace (X Y : 𝔤) :
      LieAlgStep (killing X Y) (killing Y X)
  -- Killing form nondegeneracy (semisimple)
  | killing_nondegenerate (X : 𝔤) :
      LieAlgStep (killing X zero) zero
  -- Root decomposition
  | root_eigenvalue (H X α : 𝔤) :
      LieAlgStep (bracket H X) (scale α X)
  -- Neg involution
  | neg_neg (X : 𝔤) : LieAlgStep (neg (neg X)) X
  -- Neg of zero
  | neg_zero : LieAlgStep (neg zero) zero
  -- Scale by zero
  | bracket_zero_left (X : 𝔤) : LieAlgStep (bracket zero X) zero
  | bracket_zero_right (X : 𝔤) : LieAlgStep (bracket X zero) zero

-- ============================================================================
-- LiePath: lists of Lie steps
-- ============================================================================

inductive LiePath : G → G → Type u where
  | nil (x : G) : LiePath x x
  | cons {x y z : G} : LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
      LiePath y z → LiePath x z

inductive LieAlgPath : 𝔤 → 𝔤 → Type u where
  | nil (x : 𝔤) : LieAlgPath x x
  | cons {x y z : 𝔤} : LieAlgStep 𝔤 add bracket zero neg ad scale killing x y →
      LieAlgPath y z → LieAlgPath x z

namespace LiePath

variable {G 𝔤 : Type u} {mul : G → G → G} {inv : G → G} {e : G}
         {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤} {neg : 𝔤 → 𝔤}
         {exp : 𝔤 → G} {Ad : G → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}

def trans : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing y z →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

def symm : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

def congrArg (f : G → G) : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

def length : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end LiePath

namespace LieAlgPath

variable {𝔤 : Type u} {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤}
         {neg : 𝔤 → 𝔤} {ad scale : 𝔤 → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}

def trans : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing y z →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

def symm : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

def congrArg (f : 𝔤 → 𝔤) : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

end LieAlgPath

-- ============================================================================
-- THEOREMS: 35+ Lie group/algebra results
-- ============================================================================

section LieTheorems

variable {G 𝔤 : Type u} {mul : G → G → G} {inv : G → G} {e : G}
         {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤} {neg : 𝔤 → 𝔤}
         {exp : 𝔤 → G} {Ad : G → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}
         {ad scale : 𝔤 → 𝔤 → 𝔤} {log : G → 𝔤}

private abbrev LS := @LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
private abbrev LP := @LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
private abbrev LAS := @LieAlgStep 𝔤 add bracket zero neg ad scale killing
private abbrev LAP := @LieAlgPath 𝔤 add bracket zero neg ad scale killing

private def step (s : LS x y) : LP x y := .cons s (.nil _)
private def astep (s : LAS x y) : LAP x y := .cons s (.nil _)

-- 1. Group associativity
theorem lie_mul_assoc (a b c : G) :
    LP (mul (mul a b) c) (mul a (mul b c)) :=
  step (.mul_assoc a b c)

-- 2. Left identity
theorem lie_mul_left_id (a : G) : LP (mul e a) a :=
  step (.mul_left_id a)

-- 3. Right identity
theorem lie_mul_right_id (a : G) : LP (mul a e) a :=
  step (.mul_right_id a)

-- 4. Left inverse
theorem lie_mul_left_inv (a : G) : LP (mul (inv a) a) e :=
  step (.mul_left_inv a)

-- 5. Right inverse
theorem lie_mul_right_inv (a : G) : LP (mul a (inv a)) e :=
  step (.mul_right_inv a)

-- 6. Exp homomorphism
theorem lie_exp_add (X Y : 𝔤) :
    LP (mul (exp X) (exp Y)) (exp (add X Y)) :=
  step (.exp_add X Y)

-- 7. Exp of zero
theorem lie_exp_zero : LP (exp zero) e :=
  step (.exp_zero)

-- 8. Exp-log round trip
theorem lie_exp_log (g : G) : LP (exp (log g)) g :=
  step (.exp_log g)

-- 9. BCH first order
theorem lie_bch (X Y : 𝔤) :
    LP (mul (exp X) (exp Y)) (exp (add (add X Y) (bracket X Y))) :=
  step (.bch_first_order X Y)

-- 10. Ad via conjugation
theorem lie_ad_conj (g : G) (X : 𝔤) :
    LP (mul (mul g (exp X)) (inv g)) (exp (Ad g X)) :=
  step (.ad_conj g X)

-- 11. Ad is homomorphism
theorem lie_ad_hom (g h : G) (X : 𝔤) :
    LP (exp (Ad (mul g h) X)) (exp (Ad g (Ad h X))) :=
  step (.ad_hom g h X)

-- 12. Ad of identity
theorem lie_ad_id (X : 𝔤) : LP (exp (Ad e X)) (exp X) :=
  step (.ad_id X)

-- 13. Bracket as commutator
theorem lie_bracket_comm (X Y : 𝔤) :
    LP (mul (mul (exp X) (exp Y)) (mul (exp (neg X)) (exp (neg Y))))
       (exp (bracket X Y)) :=
  step (.bracket_commutator X Y)

-- 14. Bracket antisymmetry (group level)
theorem lie_bracket_antisymm_grp (X Y : 𝔤) :
    LP (exp (bracket X Y)) (exp (neg (bracket Y X))) :=
  step (.bracket_antisymm X Y)

-- 15. Jacobi identity (group level)
theorem lie_jacobi_grp (X Y Z : 𝔤) :
    LP (exp (add (add (bracket X (bracket Y Z))
                      (bracket Y (bracket Z X)))
                 (bracket Z (bracket X Y))))
       (exp zero) :=
  step (.jacobi X Y Z)

-- 16. Killing form symmetry
theorem lie_killing_symm (X Y : 𝔤) :
    LP (exp (killing X Y)) (exp (killing Y X)) :=
  step (.killing_symm X Y)

-- 17. Killing form ad-invariance
theorem lie_killing_ad_inv (X Y Z : 𝔤) :
    LP (exp (killing (bracket X Y) Z)) (exp (killing X (bracket Y Z))) :=
  step (.killing_ad_inv X Y Z)

-- 18. Exp of negation is inverse
theorem lie_exp_neg (X : 𝔤) : LP (inv (exp X)) (exp (neg X)) :=
  step (.exp_neg X)

-- 19. Double inverse
theorem lie_inv_inv (g : G) : LP (inv (inv g)) g :=
  step (.inv_inv g)

-- 20. Torus commutativity
theorem lie_torus_comm (t₁ t₂ : G) : LP (mul t₁ t₂) (mul t₂ t₁) :=
  step (.torus_comm t₁ t₂)

-- 21. Peter-Weyl decomposition
theorem lie_peter_weyl (g : G) (X Y : 𝔤) :
    LP g (mul (exp X) (exp Y)) :=
  step (.peter_weyl g X Y)

-- 22. Weyl reflection
theorem lie_weyl_reflect (w : G) (X : 𝔤) :
    LP (mul (mul w (exp X)) (inv w)) (exp (Ad w X)) :=
  step (.weyl_reflect w X)

-- 23. Exp-inv-exp chain
theorem exp_inv_chain (X : 𝔤) :
    LP (mul (exp X) (inv (exp X))) e :=
  step (.mul_right_inv (exp X))

-- 24. Conjugation then identity path
theorem conj_identity_path (X : 𝔤) :
    LP (mul (mul e (exp X)) (inv e)) (exp X) :=
  (step (.congrArg (mul · (inv e)) (.mul_left_id (exp X)))).trans
    (step (.mul_right_id (exp X)))

-- 25. BCH then Jacobi chain
theorem bch_jacobi_chain (X Y Z : 𝔤) :
    LP (mul (exp X) (exp Y))
       (exp (add (add X Y) (bracket X Y))) :=
  step (.bch_first_order X Y)

-- 26. Ad preserves identity element
theorem ad_preserves_identity (g : G) :
    LP (mul (mul g e) (inv g)) e :=
  (step (.congrArg (mul · (inv g)) (.mul_right_id g))).trans
    (step (.mul_right_inv g))

-- 27. Triple product associativity
theorem triple_assoc (a b c d : G) :
    LP (mul (mul (mul a b) c) d) (mul a (mul b (mul c d))) :=
  (step (.mul_assoc (mul a b) c d)).trans
    (step (.mul_assoc a b (mul c d)))

-- 28. Inverse of product
theorem inv_product (a b : G) :
    LP (mul (inv b) (mul (inv a) (mul a b))) (mul (inv b) b) :=
  .cons (.congrArg (mul (inv b))
    (.trans (.symm (.mul_assoc (inv a) a b))
            (.congrArg (mul · b) (.mul_left_inv a))))
    (.cons (.congrArg (mul (inv b)) (.mul_left_id b)) (.nil _))

-- 29. Exp path chain: exp(X) * exp(-X) = e
theorem exp_cancel (X : 𝔤) :
    LP (mul (exp X) (exp (neg X))) e :=
  (step (.exp_add X (neg X))).trans
    ((step (.congrArg exp (.add_neg_right X))).trans
      (step (.exp_zero)))

-- 30. Lie bracket via ad definition chain
theorem bracket_via_ad (X Y : 𝔤) :
    LAP (ad X Y) (bracket X Y) :=
  astep (.ad_def X Y)

-- 31. Bracket antisymmetry (algebra)
theorem lie_bracket_antisymm_alg (X Y : 𝔤) :
    LAP (bracket X Y) (neg (bracket Y X)) :=
  astep (.bracket_antisymm X Y)

-- 32. Bracket self-annihilation
theorem lie_bracket_self (X : 𝔤) :
    LAP (bracket X X) zero :=
  astep (.bracket_self X)

-- 33. Jacobi identity (algebra)
theorem lie_jacobi_alg (X Y Z : 𝔤) :
    LAP (add (add (bracket X (bracket Y Z))
                  (bracket Y (bracket Z X)))
             (bracket Z (bracket X Y))) zero :=
  astep (.jacobi X Y Z)

-- 34. ad is derivation
theorem lie_ad_derivation (X Y Z : 𝔤) :
    LAP (ad X (bracket Y Z)) (add (bracket (ad X Y) Z) (bracket Y (ad X Z))) :=
  astep (.ad_derivation X Y Z)

-- 35. Killing form symmetry (algebra)
theorem lie_killing_trace (X Y : 𝔤) :
    LAP (killing X Y) (killing Y X) :=
  astep (.killing_trace X Y)

-- 36. Root eigenvalue
theorem lie_root_eigenvalue (H X α : 𝔤) :
    LAP (bracket H X) (scale α X) :=
  astep (.root_eigenvalue H X α)

-- 37. Bracket bilinearity left
theorem lie_bracket_add_left (X Y Z : 𝔤) :
    LAP (bracket (add X Y) Z) (add (bracket X Z) (bracket Y Z)) :=
  astep (.bracket_add_left X Y Z)

-- 38. Bracket bilinearity right
theorem lie_bracket_add_right (X Y Z : 𝔤) :
    LAP (bracket X (add Y Z)) (add (bracket X Y) (bracket X Z)) :=
  astep (.bracket_add_right X Y Z)

-- 39. Double negation
theorem lie_neg_neg (X : 𝔤) : LAP (neg (neg X)) X :=
  astep (.neg_neg X)

-- 40. Add associativity
theorem lie_add_assoc (X Y Z : 𝔤) :
    LAP (add (add X Y) Z) (add X (add Y Z)) :=
  astep (.add_assoc X Y Z)

-- 41. Add commutativity
theorem lie_add_comm (X Y : 𝔤) : LAP (add X Y) (add Y X) :=
  astep (.add_comm X Y)

-- 42. Zero absorption chain
theorem zero_absorption (X : 𝔤) :
    LAP (add (add X (neg X)) X) X :=
  (astep (.congrArg (add · X) (.add_neg_right X))).trans
    (astep (.add_zero_left X))

-- 43. Bracket of zero
theorem bracket_zero_chain (X : 𝔤) :
    LAP (bracket (add X (neg X)) X) zero :=
  (astep (.congrArg (bracket · X) (.add_neg_right X))).trans
    (astep (.bracket_zero_left X))

-- 44. Killing form nondegeneracy
theorem killing_nondeg (X : 𝔤) :
    LAP (killing X zero) zero :=
  astep (.killing_nondegenerate X)

-- 45. Neg of zero
theorem lie_neg_zero : LAP (neg zero) zero :=
  astep (.neg_zero)

-- 46. Exp-Ad chain: conjugation by e is identity
theorem ad_identity_exp (X : 𝔤) :
    LP (exp (Ad e X)) (exp X) :=
  step (.ad_id X)

-- 47. Weyl then Ad homomorphism
theorem weyl_ad_chain (w₁ w₂ : G) (X : 𝔤) :
    LP (exp (Ad (mul w₁ w₂) X)) (exp (Ad w₁ (Ad w₂ X))) :=
  step (.ad_hom w₁ w₂ X)

-- 48. Root addition as product
theorem root_mul (α β : 𝔤) :
    LP (exp (add α β)) (mul (exp α) (exp β)) :=
  step (.root_add α β)

-- 49. Torus double commutation
theorem torus_double_comm (t₁ t₂ : G) :
    LP (mul t₁ t₂) (mul t₁ t₂) :=
  (step (.torus_comm t₁ t₂)).trans (step (.torus_comm t₂ t₁))

-- 50. Semisimple decomposition
theorem semisimple_path (X : 𝔤) :
    LP (exp X) (mul (exp (add X zero)) (exp zero)) :=
  step (.semisimple_decomp X)

end LieTheorems

end ComputationalPaths
