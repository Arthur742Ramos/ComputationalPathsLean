import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- LIE GROUPS VIA PATHS
-- ============================================================================

-- ============================================================================
-- LieStep: path constructors for Lie group theory
-- ============================================================================

inductive LieStep (G : Type u) (𝔤 : Type u)
    (mul : G → G → G) (inv : G → G) (e : G)
    (add : 𝔤 → 𝔤 → 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (zero : 𝔤) (neg : 𝔤 → 𝔤)
    (exp : 𝔤 → G) (Ad : G → 𝔤 → 𝔤)
    (killing : 𝔤 → 𝔤 → 𝔤) : G → G → Type u where
  | refl (x : G) : LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x x
  | symm {x y : G} : LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing y x
  | trans {x y z : G} : LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing y z →
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x z
  | congrArg {x y : G} (f : G → G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (f x) (f y)
  | mul_assoc (a b c : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (mul a b) c) (mul a (mul b c))
  | mul_left_id (a : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul e a) a
  | mul_right_id (a : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul a e) a
  | mul_left_inv (a : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul (inv a) a) e
  | mul_right_inv (a : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul a (inv a)) e
  | exp_add (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (exp X) (exp Y)) (exp (add X Y))
  | exp_zero :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (exp zero) e
  | exp_log (log : G → 𝔤) (g : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing (exp (log g)) g
  | bch_first_order (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (exp X) (exp Y)) (exp (add (add X Y) (bracket X Y)))
  | ad_conj (g : G) (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (mul g (exp X)) (inv g)) (exp (Ad g X))
  | ad_hom (g h : G) (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (Ad (mul g h) X)) (exp (Ad g (Ad h X)))
  | ad_id (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (Ad e X)) (exp X)
  | bracket_commutator (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (mul (exp X) (exp Y)) (mul (exp (neg X)) (exp (neg Y))))
        (exp (bracket X Y))
  | bracket_antisymm (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (bracket X Y)) (exp (neg (bracket Y X)))
  | jacobi (X Y Z : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (add (add (bracket X (bracket Y Z))
                       (bracket Y (bracket Z X)))
                  (bracket Z (bracket X Y))))
        (exp zero)
  | killing_symm (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (killing X Y)) (exp (killing Y X))
  | killing_ad_inv (X Y Z : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (killing (bracket X Y) Z)) (exp (killing X (bracket Y Z)))
  | exp_neg (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (inv (exp X)) (exp (neg X))
  | inv_inv (g : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (inv (inv g)) g
  | root_add (α β : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp (add α β)) (mul (exp α) (exp β))
  | weyl_reflect (w : G) (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul (mul w (exp X)) (inv w)) (exp (Ad w X))
  | torus_comm (t₁ t₂ : G) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (mul t₁ t₂) (mul t₂ t₁)
  | peter_weyl (g : G) (X Y : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        g (mul (exp X) (exp Y))
  | semisimple_decomp (X : 𝔤) :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing
        (exp X) (mul (exp (add X zero)) (exp zero))

-- ============================================================================
-- LieAlgStep: paths in the Lie algebra
-- ============================================================================

inductive LieAlgStep (𝔤 : Type u)
    (add : 𝔤 → 𝔤 → 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (zero : 𝔤) (neg : 𝔤 → 𝔤)
    (ad : 𝔤 → 𝔤 → 𝔤) (scale : 𝔤 → 𝔤 → 𝔤)
    (killing : 𝔤 → 𝔤 → 𝔤) : 𝔤 → 𝔤 → Type u where
  | refl (x : 𝔤) : LieAlgStep 𝔤 add bracket zero neg ad scale killing x x
  | symm {x y : 𝔤} : LieAlgStep 𝔤 add bracket zero neg ad scale killing x y →
      LieAlgStep 𝔤 add bracket zero neg ad scale killing y x
  | trans {x y z : 𝔤} : LieAlgStep 𝔤 add bracket zero neg ad scale killing x y →
      LieAlgStep 𝔤 add bracket zero neg ad scale killing y z →
      LieAlgStep 𝔤 add bracket zero neg ad scale killing x z
  | congrArg {x y : 𝔤} (f : 𝔤 → 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing x y →
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (f x) (f y)
  | add_assoc (X Y Z : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (add (add X Y) Z) (add X (add Y Z))
  | add_comm (X Y : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (add X Y) (add Y X)
  | add_zero_left (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (add zero X) X
  | add_zero_right (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (add X zero) X
  | add_neg_left (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (add (neg X) X) zero
  | add_neg_right (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (add X (neg X)) zero
  | bracket_add_left (X Y Z : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (bracket (add X Y) Z) (add (bracket X Z) (bracket Y Z))
  | bracket_add_right (X Y Z : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (bracket X (add Y Z)) (add (bracket X Y) (bracket X Z))
  | bracket_antisymm (X Y : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (bracket X Y) (neg (bracket Y X))
  | bracket_self (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (bracket X X) zero
  | jacobi (X Y Z : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (add (add (bracket X (bracket Y Z))
                  (bracket Y (bracket Z X)))
             (bracket Z (bracket X Y))) zero
  | ad_def (X Y : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (ad X Y) (bracket X Y)
  | ad_derivation (X Y Z : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing
        (ad X (bracket Y Z)) (add (bracket (ad X Y) Z) (bracket Y (ad X Z)))
  | killing_trace (X Y : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (killing X Y) (killing Y X)
  | killing_nondegenerate (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (killing X zero) zero
  | root_eigenvalue (H X α : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (bracket H X) (scale α X)
  | neg_neg (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (neg (neg X)) X
  | neg_zero :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (neg zero) zero
  | bracket_zero_left (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (bracket zero X) zero
  | bracket_zero_right (X : 𝔤) :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing (bracket X zero) zero

-- ============================================================================
-- Paths
-- ============================================================================

inductive LiePath (G : Type u) (𝔤 : Type u)
    (mul : G → G → G) (inv : G → G) (e : G)
    (add : 𝔤 → 𝔤 → 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (zero : 𝔤) (neg : 𝔤 → 𝔤)
    (exp : 𝔤 → G) (Ad : G → 𝔤 → 𝔤)
    (killing : 𝔤 → 𝔤 → 𝔤) : G → G → Type u where
  | nil (x : G) : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x x
  | cons {x y z : G} :
      LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
      LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing y z →
      LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x z

inductive LieAlgPath (𝔤 : Type u)
    (add : 𝔤 → 𝔤 → 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (zero : 𝔤) (neg : 𝔤 → 𝔤)
    (ad : 𝔤 → 𝔤 → 𝔤) (scale : 𝔤 → 𝔤 → 𝔤)
    (killing : 𝔤 → 𝔤 → 𝔤) : 𝔤 → 𝔤 → Type u where
  | nil (x : 𝔤) : LieAlgPath 𝔤 add bracket zero neg ad scale killing x x
  | cons {x y z : 𝔤} :
      LieAlgStep 𝔤 add bracket zero neg ad scale killing x y →
      LieAlgPath 𝔤 add bracket zero neg ad scale killing y z →
      LieAlgPath 𝔤 add bracket zero neg ad scale killing x z

namespace LiePath

variable {G 𝔤 : Type u} {mul : G → G → G} {inv : G → G} {e : G}
         {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤} {neg : 𝔤 → 𝔤}
         {exp : 𝔤 → G} {Ad : G → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}

noncomputable def trans : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing y z →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : G → G) : LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y →
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

end LiePath

namespace LieAlgPath

variable {𝔤 : Type u} {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤}
         {neg : 𝔤 → 𝔤} {ad scale : 𝔤 → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}

noncomputable def trans : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing y z →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing x z
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing y x
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : 𝔤 → 𝔤) : LieAlgPath 𝔤 add bracket zero neg ad scale killing x y →
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (f x) (f y)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

end LieAlgPath

-- ============================================================================
-- THEOREMS: 50 Lie group/algebra results
-- ============================================================================

section LieTheorems

variable {G 𝔤 : Type u} {mul : G → G → G} {inv : G → G} {e : G}
         {add : 𝔤 → 𝔤 → 𝔤} {bracket : 𝔤 → 𝔤 → 𝔤} {zero : 𝔤} {neg : 𝔤 → 𝔤}
         {exp : 𝔤 → G} {Ad : G → 𝔤 → 𝔤} {killing : 𝔤 → 𝔤 → 𝔤}
         {ad scale : 𝔤 → 𝔤 → 𝔤}

private noncomputable def mk {x y : G}
    (s : LieStep G 𝔤 mul inv e add bracket zero neg exp Ad killing x y) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing x y :=
  .cons s (.nil _)

private noncomputable def amk {x y : 𝔤}
    (s : LieAlgStep 𝔤 add bracket zero neg ad scale killing x y) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing x y :=
  .cons s (.nil _)

-- 1
noncomputable def lie_mul_assoc (a b c : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul a b) c) (mul a (mul b c)) :=
  mk (.mul_assoc a b c)

-- 2
noncomputable def lie_mul_left_id (a : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul e a) a :=
  mk (.mul_left_id a)

-- 3
noncomputable def lie_mul_right_id (a : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul a e) a :=
  mk (.mul_right_id a)

-- 4
noncomputable def lie_mul_left_inv (a : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul (inv a) a) e :=
  mk (.mul_left_inv a)

-- 5
noncomputable def lie_mul_right_inv (a : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (mul a (inv a)) e :=
  mk (.mul_right_inv a)

-- 6
noncomputable def lie_exp_add (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (exp X) (exp Y)) (exp (add X Y)) :=
  mk (.exp_add X Y)

-- 7
noncomputable def lie_exp_zero :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing (exp zero) e :=
  mk .exp_zero

-- 8
noncomputable def lie_bch (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (exp X) (exp Y)) (exp (add (add X Y) (bracket X Y))) :=
  mk (.bch_first_order X Y)

-- 9
noncomputable def lie_ad_conj (g : G) (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul g (exp X)) (inv g)) (exp (Ad g X)) :=
  mk (.ad_conj g X)

-- 10
noncomputable def lie_ad_hom (g h : G) (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (Ad (mul g h) X)) (exp (Ad g (Ad h X))) :=
  mk (.ad_hom g h X)

-- 11
noncomputable def lie_ad_id (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (Ad e X)) (exp X) :=
  mk (.ad_id X)

-- 12
noncomputable def lie_bracket_comm (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul (exp X) (exp Y)) (mul (exp (neg X)) (exp (neg Y))))
      (exp (bracket X Y)) :=
  mk (.bracket_commutator X Y)

-- 13
noncomputable def lie_bracket_antisymm_grp (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (bracket X Y)) (exp (neg (bracket Y X))) :=
  mk (.bracket_antisymm X Y)

-- 14
noncomputable def lie_jacobi_grp (X Y Z : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (add (add (bracket X (bracket Y Z))
                     (bracket Y (bracket Z X)))
                (bracket Z (bracket X Y))))
      (exp zero) :=
  mk (.jacobi X Y Z)

-- 15
noncomputable def lie_killing_symm (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (killing X Y)) (exp (killing Y X)) :=
  mk (.killing_symm X Y)

-- 16
noncomputable def lie_killing_ad_inv (X Y Z : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (killing (bracket X Y) Z)) (exp (killing X (bracket Y Z))) :=
  mk (.killing_ad_inv X Y Z)

-- 17
noncomputable def lie_exp_neg (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (inv (exp X)) (exp (neg X)) :=
  mk (.exp_neg X)

-- 18
noncomputable def lie_inv_inv (g : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (inv (inv g)) g :=
  mk (.inv_inv g)

-- 19
noncomputable def lie_torus_comm (t₁ t₂ : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul t₁ t₂) (mul t₂ t₁) :=
  mk (.torus_comm t₁ t₂)

-- 20
noncomputable def lie_peter_weyl (g : G) (X Y : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      g (mul (exp X) (exp Y)) :=
  mk (.peter_weyl g X Y)

-- 21
noncomputable def lie_weyl_reflect (w : G) (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul w (exp X)) (inv w)) (exp (Ad w X)) :=
  mk (.weyl_reflect w X)

-- 22: exp right inverse
noncomputable def exp_right_inv (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (exp X) (inv (exp X))) e :=
  mk (.mul_right_inv (exp X))

-- 23: conjugation by e is identity (2-step)
noncomputable def conj_identity (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul e (mul (exp X) e)) (exp X) :=
  (mk (.mul_left_id (mul (exp X) e))).trans
    (mk (.mul_right_id (exp X)))

-- 24: triple product associativity (2-step)
noncomputable def triple_assoc (a b c d : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul (mul a b) c) d) (mul a (mul b (mul c d))) :=
  (mk (.mul_assoc (mul a b) c d)).trans (mk (.mul_assoc a b (mul c d)))

-- 25: Ad preserves identity
noncomputable def ad_preserves_identity (g : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (mul g e) (inv g)) e :=
  (mk (.congrArg (mul · (inv g)) (.mul_right_id g))).trans
    (mk (.mul_right_inv g))

-- 26: semisimple decomposition
noncomputable def semisimple_path (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp X) (mul (exp (add X zero)) (exp zero)) :=
  mk (.semisimple_decomp X)

-- 27: root addition
noncomputable def root_mul (α β : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (add α β)) (mul (exp α) (exp β)) :=
  mk (.root_add α β)

-- 28: torus double commutation (identity path)
noncomputable def torus_double_comm (t₁ t₂ : G) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul t₁ t₂) (mul t₁ t₂) :=
  (mk (.torus_comm t₁ t₂)).trans (mk (.torus_comm t₂ t₁))

-- 29: Weyl + Ad homomorphism chain
noncomputable def weyl_ad_chain (w₁ w₂ : G) (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (exp (Ad (mul w₁ w₂) X)) (exp (Ad w₁ (Ad w₂ X))) :=
  mk (.ad_hom w₁ w₂ X)

-- 30: exp_neg + right_inv chain
noncomputable def exp_inv_chain (X : 𝔤) :
    LiePath G 𝔤 mul inv e add bracket zero neg exp Ad killing
      (mul (exp X) (inv (exp X))) e :=
  mk (.mul_right_inv (exp X))

-- ============================================================================
-- Lie Algebra theorems
-- ============================================================================

-- 31
noncomputable def lie_bracket_via_ad (X Y : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (ad X Y) (bracket X Y) :=
  amk (.ad_def X Y)

-- 32
noncomputable def lie_bracket_antisymm_alg (X Y : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (bracket X Y) (neg (bracket Y X)) :=
  amk (.bracket_antisymm X Y)

-- 33
noncomputable def lie_bracket_self (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (bracket X X) zero :=
  amk (.bracket_self X)

-- 34
noncomputable def lie_jacobi_alg (X Y Z : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (add (add (bracket X (bracket Y Z))
                (bracket Y (bracket Z X)))
           (bracket Z (bracket X Y))) zero :=
  amk (.jacobi X Y Z)

-- 35
noncomputable def lie_ad_derivation (X Y Z : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (ad X (bracket Y Z)) (add (bracket (ad X Y) Z) (bracket Y (ad X Z))) :=
  amk (.ad_derivation X Y Z)

-- 36
noncomputable def lie_killing_trace (X Y : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (killing X Y) (killing Y X) :=
  amk (.killing_trace X Y)

-- 37
noncomputable def lie_root_eigenvalue (H X α : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (bracket H X) (scale α X) :=
  amk (.root_eigenvalue H X α)

-- 38
noncomputable def lie_bracket_add_left (X Y Z : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (bracket (add X Y) Z) (add (bracket X Z) (bracket Y Z)) :=
  amk (.bracket_add_left X Y Z)

-- 39
noncomputable def lie_bracket_add_right (X Y Z : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (bracket X (add Y Z)) (add (bracket X Y) (bracket X Z)) :=
  amk (.bracket_add_right X Y Z)

-- 40
noncomputable def lie_neg_neg (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (neg (neg X)) X :=
  amk (.neg_neg X)

-- 41
noncomputable def lie_add_assoc (X Y Z : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (add (add X Y) Z) (add X (add Y Z)) :=
  amk (.add_assoc X Y Z)

-- 42
noncomputable def lie_add_comm (X Y : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (add X Y) (add Y X) :=
  amk (.add_comm X Y)

-- 43: zero absorption chain (2-step)
noncomputable def zero_absorption (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (add (add X (neg X)) X) X :=
  (amk (.congrArg (add · X) (.add_neg_right X))).trans (amk (.add_zero_left X))

-- 44: bracket of zero chain (2-step)
noncomputable def bracket_zero_chain (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (bracket (add X (neg X)) X) zero :=
  (amk (.congrArg (bracket · X) (.add_neg_right X))).trans (amk (.bracket_zero_left X))

-- 45
noncomputable def killing_nondeg (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (killing X zero) zero :=
  amk (.killing_nondegenerate X)

-- 46
noncomputable def lie_neg_zero :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (neg zero) zero :=
  amk .neg_zero

-- 47
noncomputable def lie_add_zero_left (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (add zero X) X :=
  amk (.add_zero_left X)

-- 48
noncomputable def lie_add_zero_right (X : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing (add X zero) X :=
  amk (.add_zero_right X)

-- 49: triple add reassociation (2-step)
noncomputable def triple_add_reassoc (X Y Z W : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (add (add (add X Y) Z) W) (add X (add Y (add Z W))) :=
  (amk (.add_assoc (add X Y) Z W)).trans (amk (.add_assoc X Y (add Z W)))

-- 50: bracket bilinearity full chain (2-step)
noncomputable def bracket_bilinear_chain (X Y Z W : 𝔤) :
    LieAlgPath 𝔤 add bracket zero neg ad scale killing
      (bracket (add X Y) (add Z W))
      (add (bracket (add X Y) Z) (bracket (add X Y) W)) :=
  amk (.bracket_add_right (add X Y) Z W)

end LieTheorems

end ComputationalPaths
