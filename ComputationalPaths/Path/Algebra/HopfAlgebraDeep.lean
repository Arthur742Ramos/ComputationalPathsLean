/-
# Hopf Algebra Deep: Computational Paths for Hopf Algebras
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.HopfDeep

universe u

section HopfAlgebra

inductive HAStep (A : Type u) : A → A → Type u where
  | refl (a : A) : HAStep A a a
  | symm {a b : A} : HAStep A a b → HAStep A b a
  | trans {a b c : A} : HAStep A a b → HAStep A b c → HAStep A a c
  | congrArg {a b : A} (f : A → A) : HAStep A a b → HAStep A (f a) (f b)
  | mult {a b : A} : HAStep A a b → HAStep A a b
  | unit {a : A} : HAStep A a a
  | comult {a b : A} : HAStep A a b → HAStep A a b
  | counit {a : A} : HAStep A a a
  | bialg {a b : A} : HAStep A a b → HAStep A a b
  | antipode {a b : A} : HAStep A a b → HAStep A b a
  | hopfAction {a b : A} : HAStep A a b → HAStep A a b
  | hopfCoaction {a b : A} : HAStep A a b → HAStep A a b
  | leftIntegral {a : A} : HAStep A a a
  | rightIntegral {a : A} : HAStep A a a
  | groupMult {a b c : A} : HAStep A a b → HAStep A b c → HAStep A a c
  | groupInv {a b : A} : HAStep A a b → HAStep A b a
  | drinfeldPair {a b : A} : HAStep A a b → HAStep A a b
  | drinfeldR {a b : A} : HAStep A a b → HAStep A a b
  | qDeform {a b : A} : HAStep A a b → HAStep A a b
  | qCommute {a b : A} : HAStep A a b → HAStep A b a

inductive HAPath (A : Type u) : A → A → Type u where
  | nil (a : A) : HAPath A a a
  | cons {a b c : A} : HAStep A a b → HAPath A b c → HAPath A a c

def HAPath.trans {A : Type u} {a b c : A} : HAPath A a b → HAPath A b c → HAPath A a c
  | .nil _, p => p
  | .cons s p1, p2 => .cons s (HAPath.trans p1 p2)

def HAPath.symm {A : Type u} {a b : A} : HAPath A a b → HAPath A b a
  | .nil _ => .nil _
  | .cons s p => HAPath.trans (HAPath.symm p) (.cons (.symm s) (.nil _))

def HAPath.congrArg {A : Type u} {a b : A} (f : A → A) : HAPath A a b → HAPath A (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (HAPath.congrArg f p)

def HAPath.length {A : Type u} {a b : A} : HAPath A a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + HAPath.length p

-- 1
theorem ha_trans_assoc {A : Type u} {a b c d : A}
    (p : HAPath A a b) (q : HAPath A b c) (r : HAPath A c d) :
    HAPath.trans (HAPath.trans p q) r = HAPath.trans p (HAPath.trans q r) := by
  induction p with
  | nil _ => simp [HAPath.trans]
  | cons s p1 ih => simp only [HAPath.trans]; congr 1; exact ih q

-- 2
theorem ha_trans_nil_right {A : Type u} {a b : A} (p : HAPath A a b) :
    HAPath.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [HAPath.trans]
  | cons s p1 ih => simp [HAPath.trans]; exact ih

-- 3
theorem ha_trans_nil_left {A : Type u} {a b : A} (p : HAPath A a b) :
    HAPath.trans (.nil a) p = p := by simp [HAPath.trans]

-- 4
theorem ha_congrArg_nil {A : Type u} (a : A) (f : A → A) :
    HAPath.congrArg f (.nil a) = .nil (f a) := by simp [HAPath.congrArg]

-- 5
theorem ha_congrArg_trans {A : Type u} {a b c : A} (f : A → A)
    (p : HAPath A a b) (q : HAPath A b c) :
    HAPath.congrArg f (HAPath.trans p q) =
    HAPath.trans (HAPath.congrArg f p) (HAPath.congrArg f q) := by
  induction p with
  | nil _ => simp [HAPath.trans, HAPath.congrArg]
  | cons s p1 ih => simp [HAPath.trans, HAPath.congrArg]; exact ih q

-- 6
theorem ha_length_nil {A : Type u} (a : A) :
    HAPath.length (.nil a : HAPath A a a) = 0 := by simp [HAPath.length]

-- 7
theorem ha_length_cons {A : Type u} {a b c : A} (s : HAStep A a b) (p : HAPath A b c) :
    HAPath.length (.cons s p) = 1 + HAPath.length p := by simp [HAPath.length]

-- 8
theorem ha_length_trans {A : Type u} {a b c : A} (p : HAPath A a b) (q : HAPath A b c) :
    HAPath.length (HAPath.trans p q) = HAPath.length p + HAPath.length q := by
  induction p with
  | nil _ => simp [HAPath.trans, HAPath.length]
  | cons s p1 ih => simp [HAPath.trans, HAPath.length, ih q]; omega

-- 9
theorem ha_length_congrArg {A : Type u} {a b : A} (f : A → A) (p : HAPath A a b) :
    HAPath.length (HAPath.congrArg f p) = HAPath.length p := by
  induction p with
  | nil _ => simp [HAPath.congrArg, HAPath.length]
  | cons s p1 ih => simp [HAPath.congrArg, HAPath.length]; exact ih

-- 10
theorem ha_symm_nil {A : Type u} (a : A) :
    HAPath.symm (.nil a : HAPath A a a) = .nil a := by simp [HAPath.symm]

-- 11
def ha_mult_path {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.mult f) (.nil b)

-- 12
def ha_comult_path {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.comult f) (.nil b)

-- 13
def ha_unit_mult {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.unit) (.cons (.mult f) (.nil b))

-- 14
def ha_counit_comult {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.counit) (.cons (.comult f) (.nil b))

-- 15
def ha_coassoc {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.comult f) (.cons (.bialg g) (.nil c))

-- 16
theorem ha_unit_mult_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_unit_mult f) = 2 := by simp [ha_unit_mult, HAPath.length]

-- 17
theorem ha_coassoc_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    HAPath.length (ha_coassoc f g) = 2 := by simp [ha_coassoc, HAPath.length]

-- 18
def ha_full_bialg {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.mult f) (.cons (.comult g) (.cons (.bialg (.refl c)) (.nil c)))

-- 19
def ha_antipode_left {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons (.comult f) (.cons (.antipode f) (.cons (.unit) (.nil a)))

-- 20
def ha_antipode_right {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons f (.cons (.antipode f) (.cons (.unit) (.nil a)))

-- 21
theorem ha_antipode_left_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_antipode_left f) = 3 := by simp [ha_antipode_left, HAPath.length]

-- 22
theorem ha_antipode_right_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_antipode_right f) = 3 := by simp [ha_antipode_right, HAPath.length]

-- 23
def ha_antipode_anti_mult {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A c a :=
  .cons (.antipode g) (.cons (.antipode f) (.nil a))

-- 24
theorem ha_antipode_anti_mult_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    HAPath.length (ha_antipode_anti_mult f g) = 2 := by
  simp [ha_antipode_anti_mult, HAPath.length]

-- 25
def ha_antipode_squared {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.antipode (.antipode f)) (.nil b)

-- 26
def ha_antipode_unit {A : Type u} {a : A} : HAPath A a a :=
  .cons (.antipode (.unit (a := a))) (.cons (.unit) (.nil a))

-- 27
def ha_antipode_counit {A : Type u} {a : A} : HAPath A a a :=
  .cons (.counit) (.cons (.antipode (.counit (a := a))) (.nil a))

-- 28
theorem ha_antipode_squared_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_antipode_squared f) = 1 := by
  simp [ha_antipode_squared, HAPath.length]

-- 29
def ha_hopf_module_compat {A : Type u} {a b c : A}
    (act : HAStep A a b) (coact : HAStep A b c) : HAPath A a c :=
  .cons (.hopfAction act) (.cons (.hopfCoaction coact) (.nil c))

-- 30
theorem ha_hopf_module_compat_len {A : Type u} {a b c : A}
    (act : HAStep A a b) (coact : HAStep A b c) :
    HAPath.length (ha_hopf_module_compat act coact) = 2 := by
  simp [ha_hopf_module_compat, HAPath.length]

-- 31
def ha_left_integral {A : Type u} {a : A} : HAPath A a a :=
  .cons (.mult (.leftIntegral (a := a))) (.cons (.counit) (.cons (.leftIntegral) (.nil a)))

-- 32
def ha_right_integral {A : Type u} {a : A} : HAPath A a a :=
  .cons (.mult (.rightIntegral (a := a))) (.cons (.counit) (.cons (.rightIntegral) (.nil a)))

-- 33
theorem ha_left_integral_len {A : Type u} {a : A} :
    HAPath.length (ha_left_integral (A := A) (a := a)) = 3 := by
  simp [ha_left_integral, HAPath.length]

-- 34
def ha_maschke {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.hopfAction (.leftIntegral)) (.cons f (.cons (.hopfAction (.rightIntegral)) (.nil b)))

-- 35
theorem ha_maschke_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_maschke f) = 3 := by simp [ha_maschke, HAPath.length]

-- 36
def ha_fundamental {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.hopfCoaction f) (.cons (.hopfAction g) (.nil c))

-- 37
def ha_group_comult {A : Type u} {a b : A} (g : HAStep A a b) : HAPath A a b :=
  .cons (.comult g) (.cons (.bialg (.refl b)) (.nil b))

-- 38
def ha_group_antipode {A : Type u} {a b : A} (g : HAStep A a b) : HAPath A b a :=
  .cons (.antipode g) (.cons (.groupInv (.refl a)) (.nil a))

-- 39
theorem ha_group_antipode_len {A : Type u} {a b : A} (g : HAStep A a b) :
    HAPath.length (ha_group_antipode g) = 2 := by
  simp [ha_group_antipode, HAPath.length]

-- 40
def ha_group_assoc {A : Type u} {a b c d : A}
    (f : HAStep A a b) (g : HAStep A b c) (h : HAStep A c d) : HAPath A a d :=
  .cons (.groupMult f g) (.cons h (.nil d))

-- 41
def ha_group_inv_right {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons (.groupMult g (.groupInv g)) (.cons (.unit) (.nil a))

-- 42
def ha_group_inv_left {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons (.groupMult (.groupInv g) g) (.cons (.unit) (.nil a))

-- 43
def ha_drinfeld_pair {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.drinfeldPair f) (.cons (.drinfeldR (.refl b)) (.nil b))

-- 44
def ha_drinfeld_rmatrix {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.drinfeldR f) (.cons (.drinfeldPair g) (.cons (.bialg (.refl c)) (.nil c)))

-- 45
theorem ha_drinfeld_rmatrix_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    HAPath.length (ha_drinfeld_rmatrix f g) = 3 := by
  simp [ha_drinfeld_rmatrix, HAPath.length]

-- 46
def ha_q_deform {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.qDeform f) (.cons (.bialg (.refl b)) (.nil b))

-- 47
def ha_q_commute_path {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons f (.cons (.qCommute f) (.cons (.unit) (.nil a)))

-- 48
theorem ha_q_commute_len {A : Type u} {a b : A} (f : HAStep A a b) :
    HAPath.length (ha_q_commute_path f) = 3 := by
  simp [ha_q_commute_path, HAPath.length]

-- 49
def ha_yang_baxter {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) : HAPath A a d :=
  .cons (.drinfeldR r12) (.cons (.drinfeldR r13) (.cons (.drinfeldR r23) (.nil d)))

-- 50
theorem ha_yang_baxter_len {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) :
    HAPath.length (ha_yang_baxter r12 r13 r23) = 3 := by
  simp [ha_yang_baxter, HAPath.length]

-- 51
def ha_q_coproduct {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.qDeform (.comult f)) (.cons (.comult (.qDeform (.refl b))) (.nil b))

-- 52
def ha_drinfeld_bicrossed {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.drinfeldPair f) (.cons (.hopfAction g) (.cons (.drinfeldR (.refl c)) (.nil c)))

-- 53
theorem ha_drinfeld_bicrossed_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    HAPath.length (ha_drinfeld_bicrossed f g) = 3 := by
  simp [ha_drinfeld_bicrossed, HAPath.length]

-- 54
def ha_q_antipode {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A b a :=
  .cons (.qDeform (.antipode f)) (.cons (.antipode (.qDeform (.refl a))) (.nil a))

-- 55
theorem ha_length_symm_cons {A : Type u} {a b c : A} (s : HAStep A a b) (p : HAPath A b c) :
    HAPath.length (HAPath.symm (.cons s p)) =
    HAPath.length (HAPath.symm p) + 1 := by
  simp [HAPath.symm]
  rw [ha_length_trans]
  simp [HAPath.length]

end HopfAlgebra

end ComputationalPaths.HopfDeep
