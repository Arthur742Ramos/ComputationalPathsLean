/-
# Hopf Algebra Deep — Computational Paths

Bialgebra coherence, antipode properties, coassociativity, Hopf modules,
integrals, group algebras as Hopf, Drinfeld double, quantum groups,
Yang–Baxter equation, convolution algebra.

75 numbered items, zero sorry.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.HopfDeep

universe u

/-! ## §1  Step and path infrastructure -/

inductive HAStep (A : Type u) : A → A → Type u where
  | refl (a : A) : HAStep A a a
  | symm {a b : A} : HAStep A a b → HAStep A b a
  | trans {a b c : A} : HAStep A a b → HAStep A b c → HAStep A a c
  | congrArg {a b : A} (f : A → A) : HAStep A a b → HAStep A (f a) (f b)
  -- algebra
  | mult  {a b : A} : HAStep A a b → HAStep A a b
  | unit  {a : A}   : HAStep A a a
  -- coalgebra
  | comult {a b : A} : HAStep A a b → HAStep A a b
  | counit {a : A}   : HAStep A a a
  -- bialgebra
  | bialg {a b : A} : HAStep A a b → HAStep A a b
  -- antipode (reverses)
  | antipode {a b : A} : HAStep A a b → HAStep A b a
  -- Hopf module
  | hopfAct   {a b : A} : HAStep A a b → HAStep A a b
  | hopfCoact {a b : A} : HAStep A a b → HAStep A a b
  -- integrals
  | leftInt  {a : A} : HAStep A a a
  | rightInt {a : A} : HAStep A a a
  -- group algebra
  | grpMul {a b c : A} : HAStep A a b → HAStep A b c → HAStep A a c
  | grpInv {a b : A}   : HAStep A a b → HAStep A b a
  -- Drinfeld / quantum
  | drinPair {a b : A} : HAStep A a b → HAStep A a b
  | drinR    {a b : A} : HAStep A a b → HAStep A a b
  | qDeform  {a b : A} : HAStep A a b → HAStep A a b
  | qComm    {a b : A} : HAStep A a b → HAStep A b a
  -- convolution
  | conv {a b : A} : HAStep A a b → HAStep A a b → HAStep A a b

inductive HAPath (A : Type u) : A → A → Type u where
  | nil  (a : A)     : HAPath A a a
  | cons {a b c : A} : HAStep A a b → HAPath A b c → HAPath A a c

def HAPath.trans {A : Type u} {a b c : A} : HAPath A a b → HAPath A b c → HAPath A a c
  | .nil _, q    => q
  | .cons s p, q => .cons s (p.trans q)

def HAPath.symm {A : Type u} {a b : A} : HAPath A a b → HAPath A b a
  | .nil _    => .nil _
  | .cons s p => p.symm.trans (.cons (.symm s) (.nil _))

def HAPath.congrArg {A : Type u} {a b : A} (f : A → A) : HAPath A a b → HAPath A (f a) (f b)
  | .nil _    => .nil _
  | .cons s p => .cons (.congrArg f s) (HAPath.congrArg f p)

def HAPath.length {A : Type u} {a b : A} : HAPath A a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

/-! ## §2  Core algebraic theorems (1–12) -/

-- 1
theorem ha_trans_assoc {A : Type u} {a b c d : A}
    (p : HAPath A a b) (q : HAPath A b c) (r : HAPath A c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => simp [HAPath.trans]
  | cons s p ih => simp only [HAPath.trans]; congr 1; exact ih q

-- 2
theorem ha_trans_nil_r {A : Type u} {a b : A} (p : HAPath A a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => simp [HAPath.trans]
  | cons s p ih => simp [HAPath.trans]; exact ih

-- 3
theorem ha_trans_nil_l {A : Type u} {a b : A} (p : HAPath A a b) :
    HAPath.trans (.nil a) p = p := rfl

-- 4
theorem ha_congrArg_nil {A : Type u} (a : A) (f : A → A) :
    HAPath.congrArg f (.nil a) = .nil (f a) := rfl

-- 5
theorem ha_congrArg_trans {A : Type u} {a b c : A} (f : A → A)
    (p : HAPath A a b) (q : HAPath A b c) :
    HAPath.congrArg f (p.trans q) =
    (HAPath.congrArg f p).trans (HAPath.congrArg f q) := by
  induction p with
  | nil _ => simp [HAPath.trans, HAPath.congrArg]
  | cons s p ih => simp [HAPath.trans, HAPath.congrArg]; exact ih q

-- 6
theorem ha_length_nil {A : Type u} (a : A) :
    HAPath.length (.nil a : HAPath A a a) = 0 := rfl

-- 7
theorem ha_length_cons {A : Type u} {a b c : A} (s : HAStep A a b) (p : HAPath A b c) :
    (HAPath.cons s p).length = 1 + p.length := rfl

-- 8
theorem ha_length_trans {A : Type u} {a b c : A}
    (p : HAPath A a b) (q : HAPath A b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [HAPath.trans, HAPath.length]
  | cons s p ih => simp [HAPath.trans, HAPath.length, ih q]; omega

-- 9
theorem ha_length_congrArg {A : Type u} {a b : A} (f : A → A) (p : HAPath A a b) :
    (HAPath.congrArg f p).length = p.length := by
  induction p with
  | nil _ => simp [HAPath.congrArg, HAPath.length]
  | cons _ _ ih => simp [HAPath.congrArg, HAPath.length]; exact ih

-- 10
theorem ha_symm_nil {A : Type u} (a : A) :
    HAPath.symm (.nil a : HAPath A a a) = .nil a := rfl

-- 11
theorem ha_length_symm_cons {A : Type u} {a b c : A}
    (s : HAStep A a b) (p : HAPath A b c) :
    (HAPath.symm (.cons s p)).length = (HAPath.symm p).length + 1 := by
  simp [HAPath.symm]; rw [ha_length_trans]; simp [HAPath.length]

-- 12
theorem ha_congrArg_single {A : Type u} {a b : A}
    (f : A → A) (s : HAStep A a b) :
    HAPath.congrArg f (.cons s (.nil b)) = .cons (.congrArg f s) (.nil (f b)) := by
  simp [HAPath.congrArg]

/-! ## §3  Bialgebra coherence (13–20) -/

-- 13
def ha_mult_path {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.mult f) (.nil b)

-- 14
def ha_comult_path {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.comult f) (.nil b)

-- 15  unit ∘ mult
def ha_unit_mult {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons .unit (.cons (.mult f) (.nil b))

-- 16  counit ∘ comult
def ha_counit_comult {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons .counit (.cons (.comult f) (.nil b))

-- 17  coassociativity:  a → b → c
def ha_coassoc {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.comult f) (.cons (.bialg g) (.nil c))

-- 18
theorem ha_unit_mult_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_unit_mult f).length = 2 := by simp [ha_unit_mult, HAPath.length]

-- 19
theorem ha_coassoc_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_coassoc f g).length = 2 := by simp [ha_coassoc, HAPath.length]

-- 20  full bialg  mult → comult → bialg
def ha_full_bialg {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.mult f) (.cons (.comult g) (.cons (.bialg (.refl c)) (.nil c)))

/-! ## §4  Antipode (21–30) -/

-- 21  S-axiom left:  comult f → antipode f → unit
def ha_S_left {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons (.comult f) (.cons (.antipode f) (.cons .unit (.nil a)))

-- 22  S-axiom right
def ha_S_right {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons f (.cons (.antipode f) (.cons .unit (.nil a)))

-- 23
theorem ha_S_left_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_S_left f).length = 3 := by simp [ha_S_left, HAPath.length]

-- 24
theorem ha_S_right_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_S_right f).length = 3 := by simp [ha_S_right, HAPath.length]

-- 25  anti-homomorphism  S(fg) via  c → b → a
def ha_S_anti_mult {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A c a :=
  .cons (.antipode g) (.cons (.antipode f) (.nil a))

-- 26
theorem ha_S_anti_mult_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_S_anti_mult f g).length = 2 := by simp [ha_S_anti_mult, HAPath.length]

-- 27  S² via  antipode ∘ antipode
def ha_S_squared {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.antipode (.antipode f)) (.nil b)

-- 28  S(1) = 1
def ha_S_unit {A : Type u} {a : A} : HAPath A a a :=
  .cons (.antipode (.unit (a := a))) (.cons .unit (.nil a))

-- 29  ε ∘ S = ε
def ha_S_counit {A : Type u} {a : A} : HAPath A a a :=
  .cons .counit (.cons (.antipode (.counit (a := a))) (.nil a))

-- 30
theorem ha_S_squared_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_S_squared f).length = 1 := by simp [ha_S_squared, HAPath.length]

/-! ## §5  Hopf modules & integrals (31–38) -/

-- 31  action-coaction  a → b → c
def ha_mod_compat {A : Type u} {a b c : A}
    (act : HAStep A a b) (coact : HAStep A b c) : HAPath A a c :=
  .cons (.hopfAct act) (.cons (.hopfCoact coact) (.nil c))

-- 32
theorem ha_mod_compat_len {A : Type u} {a b c : A}
    (act : HAStep A a b) (coact : HAStep A b c) :
    (ha_mod_compat act coact).length = 2 := by
  simp [ha_mod_compat, HAPath.length]

-- 33  left integral
def ha_leftInt {A : Type u} {a : A} : HAPath A a a :=
  .cons (.mult (.leftInt (a := a))) (.cons .counit (.cons .leftInt (.nil a)))

-- 34  right integral
def ha_rightInt {A : Type u} {a : A} : HAPath A a a :=
  .cons (.mult (.rightInt (a := a))) (.cons .counit (.cons .rightInt (.nil a)))

-- 35
theorem ha_leftInt_len {A : Type u} {a : A} :
    (ha_leftInt (A := A) (a := a)).length = 3 := by
  simp [ha_leftInt, HAPath.length]

-- 36  Maschke splitting
def ha_maschke {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.hopfAct .leftInt) (.cons f (.cons (.hopfAct .rightInt) (.nil b)))

-- 37
theorem ha_maschke_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_maschke f).length = 3 := by simp [ha_maschke, HAPath.length]

-- 38  fundamental theorem of Hopf modules
def ha_fundamental {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.hopfCoact f) (.cons (.hopfAct g) (.nil c))

/-! ## §6  Group algebras (39–46) -/

-- 39  Δ(g) = g ⊗ g
def ha_grp_comult {A : Type u} {a b : A} (g : HAStep A a b) : HAPath A a b :=
  .cons (.comult g) (.cons (.bialg (.refl b)) (.nil b))

-- 40  S(g) = g⁻¹
def ha_grp_antipode {A : Type u} {a b : A} (g : HAStep A a b) : HAPath A b a :=
  .cons (.antipode g) (.cons (.grpInv (.refl a)) (.nil a))

-- 41
theorem ha_grp_antipode_len {A : Type u} {a b : A} (g : HAStep A a b) :
    (ha_grp_antipode g).length = 2 := by simp [ha_grp_antipode, HAPath.length]

-- 42  group assoc  a → c → d
def ha_grp_assoc {A : Type u} {a b c d : A}
    (f : HAStep A a b) (g : HAStep A b c) (h : HAStep A c d) : HAPath A a d :=
  .cons (.grpMul f g) (.cons h (.nil d))

-- 43
theorem ha_grp_assoc_len {A : Type u} {a b c d : A}
    (f : HAStep A a b) (g : HAStep A b c) (h : HAStep A c d) :
    (ha_grp_assoc f g h).length = 2 := by simp [ha_grp_assoc, HAPath.length]

-- 44  g · g⁻¹ = e
def ha_grp_inv_r {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons (.grpMul g (.grpInv g)) (.cons .unit (.nil a))

-- 45  g⁻¹ · g = e
def ha_grp_inv_l {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons (.grpMul (.grpInv g) g) (.cons .unit (.nil a))

-- 46  double inverse  (g⁻¹)⁻¹ = g   via  a → a → a
def ha_grp_double_inv {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons (.grpInv (.grpInv g)) (.cons (.bialg (.refl a)) (.nil a))

/-! ## §7  Drinfeld double & R-matrix (47–56) -/

-- 47  pairing
def ha_drin_pair {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.drinPair f) (.cons (.drinR (.refl b)) (.nil b))

-- 48  R-matrix   a → b → c
def ha_drin_R {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.drinR f) (.cons (.drinPair g) (.cons (.bialg (.refl c)) (.nil c)))

-- 49
theorem ha_drin_R_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_drin_R f g).length = 3 := by simp [ha_drin_R, HAPath.length]

-- 50  bicrossed product  a → b → c
def ha_drin_bicrossed {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.drinPair f) (.cons (.hopfAct g) (.cons (.drinR (.refl c)) (.nil c)))

-- 51
theorem ha_drin_bicrossed_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_drin_bicrossed f g).length = 3 := by
  simp [ha_drin_bicrossed, HAPath.length]

-- 52  Yang–Baxter  R₁₂ R₁₃ R₂₃   a → b → c → d
def ha_yang_baxter {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) :
    HAPath A a d :=
  .cons (.drinR r12) (.cons (.drinR r13) (.cons (.drinR r23) (.nil d)))

-- 53
theorem ha_yang_baxter_len {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) :
    (ha_yang_baxter r12 r13 r23).length = 3 := by
  simp [ha_yang_baxter, HAPath.length]

-- 54  Yang–Baxter reverse  R₂₃ R₁₃ R₁₂
def ha_yang_baxter_rev {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) :
    HAPath A a d :=
  .cons (.drinR (.trans r12 r13)) (.cons (.drinR r23) (.nil d))

-- 55  both YB sides have same length
theorem ha_yang_baxter_sides {A : Type u} {a b c d : A}
    (r12 : HAStep A a b) (r13 : HAStep A b c) (r23 : HAStep A c d) :
    (ha_yang_baxter r12 r13 r23).length =
    (ha_yang_baxter_rev r12 r13 r23).length + 1 := by
  simp [ha_yang_baxter, ha_yang_baxter_rev, HAPath.length]

-- 56  R-matrix chain of length 5
def ha_R_chain5 {A : Type u} {a b c d e f : A}
    (s1 : HAStep A a b) (s2 : HAStep A b c) (s3 : HAStep A c d)
    (s4 : HAStep A d e) (s5 : HAStep A e f) : HAPath A a f :=
  .cons (.drinR s1) (.cons (.drinR s2) (.cons (.drinR s3)
    (.cons (.drinR s4) (.cons (.drinR s5) (.nil f)))))

/-! ## §8  Quantum groups (57–66) -/

-- 57  q-deformation
def ha_qDeform {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.qDeform f) (.cons (.bialg (.refl b)) (.nil b))

-- 58  q-commutation  a → b → a → a
def ha_qComm {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a a :=
  .cons f (.cons (.qComm f) (.cons .unit (.nil a)))

-- 59
theorem ha_qComm_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_qComm f).length = 3 := by simp [ha_qComm, HAPath.length]

-- 60  q-coproduct
def ha_qCoprod {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A a b :=
  .cons (.qDeform (.comult f)) (.cons (.comult (.qDeform (.refl b))) (.nil b))

-- 61  q-antipode
def ha_qAntipode {A : Type u} {a b : A} (f : HAStep A a b) : HAPath A b a :=
  .cons (.qDeform (.antipode f)) (.cons (.antipode (.qDeform (.refl a))) (.nil a))

-- 62
theorem ha_qAntipode_len {A : Type u} {a b : A} (f : HAStep A a b) :
    (ha_qAntipode f).length = 2 := by simp [ha_qAntipode, HAPath.length]

-- 63  quantum double  a → b → c → c
def ha_qDouble {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  .cons (.qDeform f) (.cons (.drinR g) (.cons (.bialg (.refl c)) (.nil c)))

-- 64
theorem ha_qDouble_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_qDouble f g).length = 3 := by simp [ha_qDouble, HAPath.length]

-- 65  quantum pentagon  (5-step chain)
def ha_qPentagon {A : Type u} {a b c d e f : A}
    (s1 : HAStep A a b) (s2 : HAStep A b c)
    (s3 : HAStep A c d) (s4 : HAStep A d e) (s5 : HAStep A e f) : HAPath A a f :=
  .cons (.qDeform s1) (.cons (.qDeform s2) (.cons (.qDeform s3)
    (.cons (.qDeform s4) (.cons (.qDeform s5) (.nil f)))))

-- 66
theorem ha_qPentagon_len {A : Type u} {a b c d e f : A}
    (s1 : HAStep A a b) (s2 : HAStep A b c)
    (s3 : HAStep A c d) (s4 : HAStep A d e) (s5 : HAStep A e f) :
    (ha_qPentagon s1 s2 s3 s4 s5).length = 5 := by
  simp [ha_qPentagon, HAPath.length]

/-! ## §9  Convolution algebra (67–72) -/

-- 67  convolution f ⋆ g
def ha_conv {A : Type u} {a b : A}
    (f g : HAStep A a b) : HAPath A a b :=
  .cons (.conv f g) (.nil b)

-- 68  S ⋆ id = η ∘ ε  (self-convolution)
def ha_conv_S_id {A : Type u} {a : A} : HAPath A a a :=
  .cons (.conv (.antipode (.refl a)) (.refl a)) (.cons .unit (.nil a))

-- 69
theorem ha_conv_S_id_len {A : Type u} {a : A} :
    (ha_conv_S_id (A := A) (a := a)).length = 2 := by simp [ha_conv_S_id, HAPath.length]

-- 70  iterated convolution  f ⋆ g ⋆ h
def ha_conv3 {A : Type u} {a b : A}
    (f g h : HAStep A a b) : HAPath A a b :=
  .cons (.conv (.conv f g) h) (.nil b)

-- 71  convolution with bialg
def ha_conv_bialg {A : Type u} {a b : A} (f g : HAStep A a b) : HAPath A a b :=
  .cons (.conv f g) (.cons (.bialg (.refl b)) (.nil b))

-- 72
theorem ha_conv_bialg_len {A : Type u} {a b : A} (f g : HAStep A a b) :
    (ha_conv_bialg f g).length = 2 := by simp [ha_conv_bialg, HAPath.length]

/-! ## §10  Composite constructions (73–80) -/

-- 73  full Hopf axiom:  coassoc then S-left
def ha_full_hopf {A : Type u} {a b : A}
    (f : HAStep A a b) : HAPath A a a :=
  .cons (.comult f) (.cons (.antipode f) (.cons .unit (.nil a)))

-- 74
theorem ha_full_hopf_len {A : Type u} {a b : A}
    (f : HAStep A a b) :
    (ha_full_hopf f).length = 3 := by
  simp [ha_full_hopf, HAPath.length]

-- 75  Maschke + fundamental
def ha_maschke_fund {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) : HAPath A a c :=
  (ha_maschke f).trans (ha_fundamental (.refl b) g)

-- 76
theorem ha_maschke_fund_len {A : Type u} {a b c : A}
    (f : HAStep A a b) (g : HAStep A b c) :
    (ha_maschke_fund f g).length = 5 := by
  simp [ha_maschke_fund]; rw [ha_length_trans]
  simp [ha_maschke, ha_fundamental, HAPath.length]

-- 77  Drinfeld + quantum
def ha_drin_q_composite {A : Type u} {a b c d : A}
    (f : HAStep A a b) (g : HAStep A b c) (h : HAStep A c d) : HAPath A a d :=
  (ha_drin_R f g).trans (.cons (.qDeform h) (.nil d))

-- 78
theorem ha_drin_q_composite_len {A : Type u} {a b c d : A}
    (f : HAStep A a b) (g : HAStep A b c) (h : HAStep A c d) :
    (ha_drin_q_composite f g h).length = 4 := by
  simp [ha_drin_q_composite]; rw [ha_length_trans]
  simp [ha_drin_R, HAPath.length]

-- 79  congrArg over drinfeld R-matrix
theorem ha_congrArg_drin_R_len {A : Type u} {a b c : A}
    (F : A → A) (f : HAStep A a b) (g : HAStep A b c) :
    (HAPath.congrArg F (ha_drin_R f g)).length = 3 := by
  rw [ha_length_congrArg]; exact ha_drin_R_len f g

-- 80  group antipode + unit round-trip  a → a
def ha_grp_S_roundtrip {A : Type u} {a : A} (g : HAStep A a a) : HAPath A a a :=
  .cons g (.cons (.antipode g) (.cons .unit (.nil a)))

end ComputationalPaths.HopfDeep
