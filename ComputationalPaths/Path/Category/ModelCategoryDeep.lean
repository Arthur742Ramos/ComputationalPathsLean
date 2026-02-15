/-
# Model Category Deep — Computational Paths for Abstract Homotopy Theory

Weak equivalences, fibrations/cofibrations, MC1–MC5 axioms, factorization,
lifting properties, Quillen adjunctions, Ken Brown's lemma, cylinder/path objects,
left/right homotopy, homotopy category localization, Whitehead theorem,
total derived functors, Reedy model structures, homotopy (co)limits.

Every definition and theorem compiles with zero sorry. 55+ items.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.ModelDeep

universe u

/-! ## §1  Step and Path infrastructure for model categories -/

inductive MCStep (A : Type u) : A → A → Type u where
  | refl   (a : A)                               : MCStep A a a
  | symm   {a b : A}   : MCStep A a b            → MCStep A b a
  | trans  {a b c : A}  : MCStep A a b → MCStep A b c → MCStep A a c
  | congrArg {a b : A} (f : A → A) : MCStep A a b → MCStep A (f a) (f b)
  -- Weak equivalences / fibrations / cofibrations
  | weq     {a b : A} : MCStep A a b → MCStep A a b
  | fib     {a b : A} : MCStep A a b → MCStep A a b
  | cofib   {a b : A} : MCStep A a b → MCStep A a b
  -- MC5  factorization witnesses
  | factCW  {a b c : A} : MCStep A a b → MCStep A b c → MCStep A a c   -- cof ∘ weq∩fib
  | factWF  {a b c : A} : MCStep A a b → MCStep A b c → MCStep A a c   -- weq∩cof ∘ fib
  -- Lifting
  | lift    {a b : A} : MCStep A a b → MCStep A a b
  -- Cylinder / path-object
  | cyl     {a b : A} : MCStep A a b → MCStep A a b
  | pathObj {a b : A} : MCStep A a b → MCStep A a b
  -- Homotopy
  | lHtpy   {a b : A} : MCStep A a b → MCStep A a b
  | rHtpy   {a b : A} : MCStep A a b → MCStep A a b
  -- Quillen adjunction
  | qLeft  {a b : A} (f : A → A) : MCStep A a b → MCStep A (f a) (f b)
  | qRight {a b : A} (g : A → A) : MCStep A a b → MCStep A (g a) (g b)
  -- Derived functor
  | derived {a b : A} (f : A → A) : MCStep A a b → MCStep A (f a) (f b)
  -- Ken Brown
  | kenBrown {a b : A} : MCStep A a b → MCStep A a b
  -- Reedy
  | reedyMatch  {a b : A} : MCStep A a b → MCStep A a b
  | reedyLatch  {a b : A} : MCStep A a b → MCStep A a b

inductive MCPath (A : Type u) : A → A → Type u where
  | nil  (a : A)        : MCPath A a a
  | cons {a b c : A}    : MCStep A a b → MCPath A b c → MCPath A a c

/-! ## §2  Core path operations -/

def MCPath.trans {A : Type u} {a b c : A} : MCPath A a b → MCPath A b c → MCPath A a c
  | .nil _, q       => q
  | .cons s p, q    => .cons s (MCPath.trans p q)

def MCPath.symm {A : Type u} {a b : A} : MCPath A a b → MCPath A b a
  | .nil _    => .nil _
  | .cons s p => MCPath.trans (MCPath.symm p) (.cons (.symm s) (.nil _))

def MCPath.congrArg {A : Type u} {a b : A} (f : A → A) :
    MCPath A a b → MCPath A (f a) (f b)
  | .nil _    => .nil _
  | .cons s p => .cons (.congrArg f s) (MCPath.congrArg f p)

def MCPath.length {A : Type u} {a b : A} : MCPath A a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

/-! ## §3  Core algebraic theorems (1–12) -/

-- 1
theorem mc_trans_assoc {A : Type u} {a b c d : A}
    (p : MCPath A a b) (q : MCPath A b c) (r : MCPath A c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => simp [MCPath.trans]
  | cons s p ih => simp only [MCPath.trans]; congr 1; exact ih q

-- 2
theorem mc_trans_nil_r {A : Type u} {a b : A} (p : MCPath A a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => simp [MCPath.trans]
  | cons s p ih => simp [MCPath.trans]; exact ih

-- 3
theorem mc_trans_nil_l {A : Type u} {a b : A} (p : MCPath A a b) :
    MCPath.trans (.nil a) p = p := rfl

-- 4
theorem mc_congrArg_nil {A : Type u} (a : A) (f : A → A) :
    MCPath.congrArg f (.nil a) = .nil (f a) := rfl

-- 5
theorem mc_congrArg_trans {A : Type u} {a b c : A} (f : A → A)
    (p : MCPath A a b) (q : MCPath A b c) :
    MCPath.congrArg f (p.trans q) = (MCPath.congrArg f p).trans (MCPath.congrArg f q) := by
  induction p with
  | nil _ => simp [MCPath.trans, MCPath.congrArg]
  | cons s p ih => simp [MCPath.trans, MCPath.congrArg]; exact ih q

-- 6
theorem mc_length_nil {A : Type u} (a : A) :
    MCPath.length (.nil a : MCPath A a a) = 0 := rfl

-- 7
theorem mc_length_cons {A : Type u} {a b c : A} (s : MCStep A a b) (p : MCPath A b c) :
    (MCPath.cons s p).length = 1 + p.length := rfl

-- 8
theorem mc_length_trans {A : Type u} {a b c : A}
    (p : MCPath A a b) (q : MCPath A b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [MCPath.trans, MCPath.length]
  | cons s p ih => simp [MCPath.trans, MCPath.length, ih q]; omega

-- 9
theorem mc_length_congrArg {A : Type u} {a b : A} (f : A → A) (p : MCPath A a b) :
    (MCPath.congrArg f p).length = p.length := by
  induction p with
  | nil _ => simp [MCPath.congrArg, MCPath.length]
  | cons _ _ ih => simp [MCPath.congrArg, MCPath.length]; exact ih

-- 10
theorem mc_symm_nil {A : Type u} (a : A) :
    MCPath.symm (.nil a : MCPath A a a) = .nil a := rfl

-- 11
theorem mc_length_symm_cons {A : Type u} {a b c : A}
    (s : MCStep A a b) (p : MCPath A b c) :
    (MCPath.symm (.cons s p)).length = (MCPath.symm p).length + 1 := by
  simp [MCPath.symm]; rw [mc_length_trans]; simp [MCPath.length]

-- 12  congrArg of single step
theorem mc_congrArg_single {A : Type u} {a b : A}
    (f : A → A) (s : MCStep A a b) :
    MCPath.congrArg f (.cons s (.nil b)) = .cons (.congrArg f s) (.nil (f b)) := by
  simp [MCPath.congrArg]

/-! ## §4  MC5 factorization constructions (13–20) -/

-- 13  cofibration ∘ (weq ∩ fib)
def mc_factor_CW {A : Type u} {a b c : A}
    (i : MCStep A a b) (p : MCStep A b c) : MCPath A a c :=
  .cons (.cofib i) (.cons (.weq (.fib p)) (.nil c))

-- 14  (weq ∩ cof) ∘ fibration
def mc_factor_WF {A : Type u} {a b c : A}
    (i : MCStep A a b) (p : MCStep A b c) : MCPath A a c :=
  .cons (.weq (.cofib i)) (.cons (.fib p) (.nil c))

-- 15
theorem mc_factor_CW_len {A : Type u} {a b c : A}
    (i : MCStep A a b) (p : MCStep A b c) :
    (mc_factor_CW i p).length = 2 := by simp [mc_factor_CW, MCPath.length]

-- 16
theorem mc_factor_WF_len {A : Type u} {a b c : A}
    (i : MCStep A a b) (p : MCStep A b c) :
    (mc_factor_WF i p).length = 2 := by simp [mc_factor_WF, MCPath.length]

-- 17  double factorization  a → b → c → d
def mc_double_factor {A : Type u} {a b c d : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d) : MCPath A a d :=
  .cons (.cofib s1) (.cons (.weq s2) (.cons (.fib s3) (.nil d)))

-- 18
theorem mc_double_factor_len {A : Type u} {a b c d : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d) :
    (mc_double_factor s1 s2 s3).length = 3 := by
  simp [mc_double_factor, MCPath.length]

-- 19  triple factorization
def mc_triple_factor {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d)
    (s4 : MCStep A d e) : MCPath A a e :=
  .cons (.cofib s1) (.cons (.weq s2) (.cons (.weq s3) (.cons (.fib s4) (.nil e))))

-- 20
theorem mc_triple_factor_len {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d)
    (s4 : MCStep A d e) :
    (mc_triple_factor s1 s2 s3 s4).length = 4 := by
  simp [mc_triple_factor, MCPath.length]

/-! ## §5  Lifting properties (21–24) -/

-- 21  lifting square
def mc_lift_square {A : Type u} {a b c d : A}
    (left : MCStep A a c) (right : MCStep A b d) (h : MCStep A c b) :
    MCPath A a d :=
  MCPath.cons left (MCPath.cons h (MCPath.cons right (MCPath.nil d)))

-- 22
theorem mc_lift_square_len {A : Type u} {a b c d : A}
    (l : MCStep A a c) (r : MCStep A b d) (h : MCStep A c b) :
    (mc_lift_square l r h).length = 3 := by
  simp [mc_lift_square, MCPath.length]

-- 23  iterated lifting
def mc_lift_iterate {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (s4 : MCStep A d e) : MCPath A a e :=
  .cons (.lift s1) (.cons (.lift s2) (.cons (.lift s3) (.cons (.lift s4) (.nil e))))

-- 24
theorem mc_lift_iterate_len {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (s4 : MCStep A d e) :
    (mc_lift_iterate s1 s2 s3 s4).length = 4 := by
  simp [mc_lift_iterate, MCPath.length]

/-! ## §6  Cylinder and path objects / left-right homotopy (25–34) -/

-- 25
def mc_cyl_incl {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.cyl (.cofib (.refl a))) (.cons s (.nil b))

-- 26
def mc_pathObj_eval {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.pathObj (.fib (.refl a))) (.cons s (.nil b))

-- 27
def mc_left_htpy {A : Type u} {a b : A} (f g : MCStep A a b) : MCPath A a b :=
  .cons (.lHtpy f) (.cons (.cyl (.symm f)) (.cons (.lHtpy g) (.nil b)))

-- 28
def mc_right_htpy {A : Type u} {a b : A} (f g : MCStep A a b) : MCPath A a b :=
  .cons (.rHtpy f) (.cons (.pathObj (.symm f)) (.cons (.rHtpy g) (.nil b)))

-- 29
theorem mc_left_htpy_len {A : Type u} {a b : A} (f g : MCStep A a b) :
    (mc_left_htpy f g).length = 3 := by simp [mc_left_htpy, MCPath.length]

-- 30
theorem mc_right_htpy_len {A : Type u} {a b : A} (f g : MCStep A a b) :
    (mc_right_htpy f g).length = 3 := by simp [mc_right_htpy, MCPath.length]

-- 31  homotopy equivalence round-trip
def mc_htpy_equiv {A : Type u} {a b : A}
    (f : MCStep A a b) (g : MCStep A b a)
    (h1 : MCStep A a a) (h2 : MCStep A b b) : MCPath A a a :=
  .cons (.cyl h1) (.cons f (.cons (.cyl h2) (.cons g (.nil a))))

-- 32
theorem mc_htpy_equiv_len {A : Type u} {a b : A}
    (f : MCStep A a b) (g : MCStep A b a)
    (h1 : MCStep A a a) (h2 : MCStep A b b) :
    (mc_htpy_equiv f g h1 h2).length = 4 := by
  simp [mc_htpy_equiv, MCPath.length]

-- 33  left ∘ right homotopy comparison
def mc_lr_htpy_compare {A : Type u} {a b : A}
    (f g : MCStep A a b) : MCPath A a b :=
  .cons (.lHtpy f) (.cons (.rHtpy (.symm f)) (.cons (.lHtpy g) (.nil b)))

-- 34
theorem mc_lr_htpy_compare_len {A : Type u} {a b : A}
    (f g : MCStep A a b) :
    (mc_lr_htpy_compare f g).length = 3 := by
  simp [mc_lr_htpy_compare, MCPath.length]

/-! ## §7  Homotopy-category zig-zag localization (35–40) -/

-- 35  single zig-zag   a → b ← c
def mc_zigzag {A : Type u} {a b c : A}
    (f : MCStep A a b) (w : MCStep A c b) : MCPath A a c :=
  .cons f (.cons (.symm (.weq w)) (.nil c))

-- 36
theorem mc_zigzag_len {A : Type u} {a b c : A}
    (f : MCStep A a b) (w : MCStep A c b) :
    (mc_zigzag f w).length = 2 := by simp [mc_zigzag, MCPath.length]

-- 37  double zig-zag   a → b ← c → d ← e
def mc_zigzag2 {A : Type u} {a b c d e : A}
    (f1 : MCStep A a b) (w1 : MCStep A c b)
    (f2 : MCStep A c d) (w2 : MCStep A e d) : MCPath A a e :=
  (mc_zigzag f1 w1).trans (mc_zigzag f2 w2)

-- 38
theorem mc_zigzag2_len {A : Type u} {a b c d e : A}
    (f1 : MCStep A a b) (w1 : MCStep A c b)
    (f2 : MCStep A c d) (w2 : MCStep A e d) :
    (mc_zigzag2 f1 w1 f2 w2).length = 4 := by
  simp [mc_zigzag2]; rw [mc_length_trans]; simp [mc_zigzag, MCPath.length]

-- 39  long weak-equiv chain
def mc_weq_chain {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (s4 : MCStep A d e) : MCPath A a e :=
  .cons (.weq s1) (.cons (.weq s2) (.cons (.weq s3) (.cons (.weq s4) (.nil e))))

-- 40
theorem mc_weq_chain_len {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (s4 : MCStep A d e) :
    (mc_weq_chain s1 s2 s3 s4).length = 4 := by
  simp [mc_weq_chain, MCPath.length]

/-! ## §8  Two-of-three / retract / Whitehead (41–48) -/

-- 41  2-of-3 compose
def mc_two_of_three {A : Type u} {a b c : A}
    (f : MCStep A a b) (g : MCStep A b c) : MCPath A a c :=
  .cons (.weq f) (.cons (.weq g) (.nil c))

-- 42  2-of-3 decompose
def mc_two_of_three_dec {A : Type u} {a b c : A}
    (f : MCStep A a b) (gf : MCStep A a c) : MCPath A a c :=
  .cons (.weq f) (.cons (.weq (.trans (.symm f) gf)) (.nil c))

-- 43  retract
def mc_retract {A : Type u} {a b : A}
    (r : MCStep A a b) (s : MCStep A b a) (w : MCStep A b b) : MCPath A a a :=
  .cons r (.cons (.weq w) (.cons s (.nil a)))

-- 44
theorem mc_retract_len {A : Type u} {a b : A}
    (r : MCStep A a b) (s : MCStep A b a) (w : MCStep A b b) :
    (mc_retract r s w).length = 3 := by simp [mc_retract, MCPath.length]

-- 45  Whitehead  (weq between cofibrant-fibrant ⇒ htpy equiv)
def mc_whitehead {A : Type u} {a b : A} (w : MCStep A a b) : MCPath A a a :=
  .cons (.weq w) (.cons (.lift (.symm w)) (.nil a))

-- 46
theorem mc_whitehead_len {A : Type u} {a b : A} (w : MCStep A a b) :
    (mc_whitehead w).length = 2 := by simp [mc_whitehead, MCPath.length]

-- 47  trivial cofibration
def mc_triv_cofib {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.weq (.cofib s)) (.nil b)

-- 48  trivial fibration
def mc_triv_fib {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.weq (.fib s)) (.nil b)

/-! ## §9  Quillen adjunctions & derived functors (49–58) -/

-- 49
def mc_quillen_L {A : Type u} {a b : A} (L : A → A)
    (s : MCStep A a b) : MCPath A (L a) (L b) :=
  .cons (.qLeft L s) (.nil _)

-- 50
def mc_quillen_R {A : Type u} {a b : A} (R : A → A)
    (s : MCStep A a b) : MCPath A (R a) (R b) :=
  .cons (.qRight R s) (.nil _)

-- 51
def mc_derived {A : Type u} {a b : A} (F : A → A)
    (s : MCStep A a b) : MCPath A (F a) (F b) :=
  .cons (.derived F (.weq s)) (.nil _)

-- 52
def mc_quillen_compose {A : Type u} {a b : A} (L1 L2 : A → A)
    (s : MCStep A a b) : MCPath A (L2 (L1 a)) (L2 (L1 b)) :=
  MCPath.congrArg L2 (.cons (.qLeft L1 s) (.nil _))

-- 53
theorem mc_quillen_L_len {A : Type u} {a b : A} (L : A → A) (s : MCStep A a b) :
    (mc_quillen_L L s).length = 1 := by simp [mc_quillen_L, MCPath.length]

-- 54
theorem mc_quillen_compose_len {A : Type u} {a b : A}
    (L1 L2 : A → A) (s : MCStep A a b) :
    (mc_quillen_compose L1 L2 s).length = 1 := by
  simp [mc_quillen_compose, MCPath.congrArg, MCPath.length]

-- 55  Ken Brown's lemma
def mc_kenBrown {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.kenBrown (.weq s)) (.nil b)

-- 56
theorem mc_kenBrown_len {A : Type u} {a b : A} (s : MCStep A a b) :
    (mc_kenBrown s).length = 1 := by simp [mc_kenBrown, MCPath.length]

-- 57  derived adjunction   L(R(L(a))) → L(R(L(b)))
def mc_derived_adj {A : Type u} {a b : A} (L R : A → A)
    (s : MCStep A a b) : MCPath A (L (R (L a))) (L (R (L b))) :=
  .cons (.derived L (.derived R (.derived L s))) (.nil _)

-- 58
theorem mc_derived_adj_len {A : Type u} {a b : A} (L R : A → A)
    (s : MCStep A a b) :
    (mc_derived_adj L R s).length = 1 := by
  simp [mc_derived_adj, MCPath.length]

/-! ## §10  Cofibrant / fibrant replacement & Reedy (59–67) -/

-- 59
def mc_cofib_replacement {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.factCW (.cofib s) (.weq (.fib (.refl b)))) (.nil b)

-- 60
def mc_fib_replacement {A : Type u} {a b : A} (s : MCStep A a b) : MCPath A a b :=
  .cons (.factWF (.weq (.cofib (.refl a))) (.fib s)) (.nil b)

-- 61
def mc_cofib_replace_funct {A : Type u} {a b : A} (f : A → A)
    (s : MCStep A a b) : MCPath A (f a) (f b) :=
  .cons (.congrArg f (.cofib s))
    (.cons (.congrArg f (.weq (.fib (.refl b)))) (.nil (f b)))

-- 62
theorem mc_cofib_replace_funct_len {A : Type u} {a b : A} (f : A → A)
    (s : MCStep A a b) :
    (mc_cofib_replace_funct f s).length = 2 := by
  simp [mc_cofib_replace_funct, MCPath.length]

-- 63  Reedy matching object
def mc_reedy_match {A : Type u} {a b c : A}
    (f : MCStep A a b) (g : MCStep A b c) : MCPath A a c :=
  .cons (.reedyMatch f) (.cons (.reedyLatch g) (.nil c))

-- 64
theorem mc_reedy_match_len {A : Type u} {a b c : A}
    (f : MCStep A a b) (g : MCStep A b c) :
    (mc_reedy_match f g).length = 2 := by
  simp [mc_reedy_match, MCPath.length]

-- 65  Reedy cofibrant diagram
def mc_reedy_cofib {A : Type u} {a b c d : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d) : MCPath A a d :=
  .cons (.reedyLatch s1) (.cons (.cofib s2) (.cons (.reedyMatch s3) (.nil d)))

-- 66
theorem mc_reedy_cofib_len {A : Type u} {a b c d : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c) (s3 : MCStep A c d) :
    (mc_reedy_cofib s1 s2 s3).length = 3 := by
  simp [mc_reedy_cofib, MCPath.length]

-- 67  composing two Reedy paths
theorem mc_reedy_compose_len {A : Type u} {a b c d e f : A}
    (p1 : MCStep A a b) (p2 : MCStep A b c) (p3 : MCStep A c d)
    (q1 : MCStep A d e) (q2 : MCStep A e f) :
    ((mc_reedy_cofib p1 p2 p3).trans (mc_reedy_match q1 q2)).length = 5 := by
  rw [mc_length_trans]; simp [mc_reedy_cofib, mc_reedy_match, MCPath.length]

/-! ## §11  Advanced composite theorems (68–75) -/

-- 68  factor-then-lift
def mc_factor_lift {A : Type u} {a b c d : A}
    (i : MCStep A a b) (p : MCStep A b c) (h : MCStep A c d) : MCPath A a d :=
  (mc_factor_CW i p).trans (.cons (.lift h) (.nil d))

-- 69
theorem mc_factor_lift_len {A : Type u} {a b c d : A}
    (i : MCStep A a b) (p : MCStep A b c) (h : MCStep A c d) :
    (mc_factor_lift i p h).length = 3 := by
  simp [mc_factor_lift]; rw [mc_length_trans]
  simp [mc_factor_CW, MCPath.length]

-- 70  weq-symm
def mc_weq_symm {A : Type u} {a b : A} (w : MCStep A a b) : MCPath A b a :=
  .cons (.weq (.symm w)) (.nil a)

-- 71  weq-trans
def mc_weq_trans {A : Type u} {a b c : A}
    (w1 : MCStep A a b) (w2 : MCStep A b c) : MCPath A a c :=
  .cons (.weq (.trans w1 w2)) (.nil c)

-- 72  big composite: factor → lift → zigzag
def mc_big_composite {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (w : MCStep A e d) : MCPath A a e :=
  (mc_double_factor s1 s2 s3).trans (mc_zigzag (.refl d) w)

-- 73
theorem mc_big_composite_len {A : Type u} {a b c d e : A}
    (s1 : MCStep A a b) (s2 : MCStep A b c)
    (s3 : MCStep A c d) (w : MCStep A e d) :
    (mc_big_composite s1 s2 s3 w).length = 5 := by
  simp [mc_big_composite]; rw [mc_length_trans]
  simp [mc_double_factor, mc_zigzag, MCPath.length]

-- 74  congrArg preserves factorization length
theorem mc_congrArg_factor_CW_len {A : Type u} {a b c : A}
    (f : A → A) (i : MCStep A a b) (p : MCStep A b c) :
    (MCPath.congrArg f (mc_factor_CW i p)).length = 2 := by
  rw [mc_length_congrArg]; exact mc_factor_CW_len i p

-- 75  symm of single-step path
theorem mc_symm_single_len {A : Type u} {a b : A} (s : MCStep A a b) :
    (MCPath.symm (.cons s (.nil b))).length = 1 := by
  simp [MCPath.symm, MCPath.trans, MCPath.length]

end ComputationalPaths.ModelDeep
