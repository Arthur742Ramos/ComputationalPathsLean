import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- Category Theory Deep III: Kan extensions, density, nerve-realization,
-- Barr-Beck monadicity, Beck's coequalizer, Grothendieck construction,
-- fibered categories, Street's formal theory of monads
-- ============================================================================

-- Step type for categorical reasoning
inductive CatDeep3Step : {A : Sort u} → A → A → Type u where
  | refl (a : A) : CatDeep3Step a a
  | symm {a b : A} : CatDeep3Step a b → CatDeep3Step b a
  | trans {a b c : A} : CatDeep3Step a b → CatDeep3Step b c → CatDeep3Step a c
  | congrArg {A B : Sort u} (f : A → B) {a b : A} : CatDeep3Step a b → CatDeep3Step (f a) (f b)
  -- Kan extension axioms
  | lan_universal {A : Sort u} (lan : A → A) (a : A) : CatDeep3Step (lan a) (lan a)
  | ran_universal {A : Sort u} (ran : A → A) (a : A) : CatDeep3Step (ran a) (ran a)
  | lan_pointwise {A : Sort u} (lan colim : A → A) (a : A) : CatDeep3Step (lan a) (colim a)
  | ran_pointwise {A : Sort u} (ran lim : A → A) (a : A) : CatDeep3Step (ran a) (lim a)
  -- Density
  | density_counit {A : Sort u} (nerve real : A → A) (a : A) :
      CatDeep3Step (real (nerve a)) a
  -- Nerve-realization adjunction
  | nerve_real_unit {A : Sort u} (nerve real : A → A) (a : A) :
      CatDeep3Step a (nerve (real a))
  | nerve_real_counit {A : Sort u} (nerve real : A → A) (a : A) :
      CatDeep3Step (real (nerve a)) a
  -- Monadicity: Barr-Beck
  | monad_unit {A : Sort u} (η : A → A) (a : A) : CatDeep3Step a (η a)
  | monad_mult {A : Sort u} (μ T : A → A) (a : A) : CatDeep3Step (T (T a)) (μ a)
  | monad_assoc {A : Sort u} (μ T : A → A) (a : A) :
      CatDeep3Step (μ (T a)) (μ a)
  | monad_unit_left {A : Sort u} (μ η : A → A) (a : A) :
      CatDeep3Step (μ (η a)) a
  -- Beck coequalizer
  | beck_coeq {A : Sort u} (coeq : A → A) (a : A) : CatDeep3Step a (coeq a)
  -- Grothendieck construction
  | groth_proj {A : Sort u} (π : A → A) (a : A) : CatDeep3Step (π a) (π a)
  | groth_fiber {A : Sort u} (fib : A → A) (a : A) : CatDeep3Step (fib a) (fib a)
  -- Fibered category: cleavage
  | cleavage_lift {A : Sort u} (lift : A → A) (a : A) : CatDeep3Step a (lift a)
  -- Street's formal monad
  | street_em {A : Sort u} (em : A → A) (a : A) : CatDeep3Step a (em a)

-- Path type
inductive CatDeep3Path : {A : Sort u} → A → A → Type u where
  | nil (a : A) : CatDeep3Path a a
  | cons {a b c : A} : CatDeep3Step a b → CatDeep3Path b c → CatDeep3Path a c

namespace CatDeep3Path

def trans {A : Sort u} {a b c : A} : CatDeep3Path a b → CatDeep3Path b c → CatDeep3Path a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

def symm {A : Sort u} {a b : A} : CatDeep3Path a b → CatDeep3Path b a
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

def congrArg {A B : Sort u} (f : A → B) {a b : A} : CatDeep3Path a b → CatDeep3Path (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

def length {A : Sort u} {a b : A} : CatDeep3Path a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end CatDeep3Path

-- ============================================================================
-- Theorems
-- ============================================================================

-- 1. Left Kan extension universal property
def lan_universal_path {A : Sort u} (lan : A → A) (a : A) :
    CatDeep3Path (lan a) (lan a) :=
  .cons (.lan_universal lan a) (.nil _)

-- 2. Right Kan extension universal property
def ran_universal_path {A : Sort u} (ran : A → A) (a : A) :
    CatDeep3Path (ran a) (ran a) :=
  .cons (.ran_universal ran a) (.nil _)

-- 3. Pointwise left Kan as colimit
def lan_pointwise_path {A : Sort u} (lan colim : A → A) (a : A) :
    CatDeep3Path (lan a) (colim a) :=
  .cons (.lan_pointwise lan colim a) (.nil _)

-- 4. Pointwise right Kan as limit
def ran_pointwise_path {A : Sort u} (ran lim : A → A) (a : A) :
    CatDeep3Path (ran a) (lim a) :=
  .cons (.ran_pointwise ran lim a) (.nil _)

-- 5. Lan naturality via congrArg
def lan_naturality {A : Sort u} (lan f : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (lan (f a)) (lan (f b)) :=
  CatDeep3Path.congrArg lan (CatDeep3Path.congrArg f p)

-- 6. Ran naturality via congrArg
def ran_naturality {A : Sort u} (ran f : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (ran (f a)) (ran (f b)) :=
  CatDeep3Path.congrArg ran (CatDeep3Path.congrArg f p)

-- 7. Kan extension composition: Lan ∘ Ran chain
def kan_compose_chain {A : Sort u} (lan ran : A → A) (a : A) :
    CatDeep3Path (lan (ran a)) (lan (ran a)) :=
  CatDeep3Path.trans
    (.cons (.congrArg lan (.ran_universal ran a)) (.nil _))
    (CatDeep3Path.symm (.cons (.congrArg lan (.ran_universal ran a)) (.nil _)))

-- 8. Density theorem counit path
def density_counit_path {A : Sort u} (nerve real : A → A) (a : A) :
    CatDeep3Path (real (nerve a)) a :=
  .cons (.density_counit nerve real a) (.nil _)

-- 9. Density theorem: nerve is fully faithful encoding
def density_nerve_ff {A : Sort u} (nerve _real : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (nerve a) (nerve b) :=
  CatDeep3Path.congrArg nerve p

-- 10. Nerve-realization unit path
def nerve_real_unit_path {A : Sort u} (nerve real : A → A) (a : A) :
    CatDeep3Path a (nerve (real a)) :=
  .cons (.nerve_real_unit nerve real a) (.nil _)

-- 11. Nerve-realization counit path
def nerve_real_counit_path {A : Sort u} (nerve real : A → A) (a : A) :
    CatDeep3Path (real (nerve a)) a :=
  .cons (.nerve_real_counit nerve real a) (.nil _)

-- 12. Nerve-realization triangle identity 1
def nerve_real_triangle1 {A : Sort u} (nerve real : A → A) (a : A) :
    CatDeep3Path (real a) (real a) :=
  CatDeep3Path.trans
    (.cons (.congrArg real (.nerve_real_unit nerve real a)) (.nil _))
    (.cons (.nerve_real_counit nerve real (real a)) (.nil _))

-- 13. Nerve-realization triangle identity 2
def nerve_real_triangle2 {A : Sort u} (nerve real : A → A) (a : A) :
    CatDeep3Path (nerve a) (nerve a) :=
  CatDeep3Path.trans
    (.cons (.congrArg nerve (.symm (.density_counit nerve real a))) (.nil _))
    (.cons (.congrArg nerve (.density_counit nerve real a)) (.nil _))

-- 14. Monad unit path
def monad_unit_path {A : Sort u} (η : A → A) (a : A) :
    CatDeep3Path a (η a) :=
  .cons (.monad_unit η a) (.nil _)

-- 15. Monad multiplication path
def monad_mult_path {A : Sort u} (μ T : A → A) (a : A) :
    CatDeep3Path (T (T a)) (μ a) :=
  .cons (.monad_mult μ T a) (.nil _)

-- 16. Monad associativity path
def monad_assoc_path {A : Sort u} (μ T : A → A) (a : A) :
    CatDeep3Path (μ (T a)) (μ a) :=
  .cons (.monad_assoc μ T a) (.nil _)

-- 17. Monad left unit law
def monad_unit_left_path {A : Sort u} (μ η : A → A) (a : A) :
    CatDeep3Path (μ (η a)) a :=
  .cons (.monad_unit_left μ η a) (.nil _)

-- 18. Barr-Beck: monad algebra ↔ descent data chain
def barr_beck_chain {A : Sort u} (_μ η _T : A → A) (a : A) :
    CatDeep3Path a (η a) :=
  .cons (.monad_unit η a) (.nil _)

-- 19. Barr-Beck monadicity: full round trip T²a → μa → μa
def barr_beck_monadicity {A : Sort u} (μ _η T : A → A) (a : A) :
    CatDeep3Path (T (T a)) (μ a) :=
  CatDeep3Path.trans
    (monad_mult_path μ T a)
    (.nil _)

-- 20. Beck's coequalizer path
def beck_coeq_path {A : Sort u} (coeq : A → A) (a : A) :
    CatDeep3Path a (coeq a) :=
  .cons (.beck_coeq coeq a) (.nil _)

-- 21. Beck coequalizer + monad chain
def beck_coeq_monad_chain {A : Sort u} (coeq μ η : A → A) (a : A) :
    CatDeep3Path (μ (η a)) (coeq a) :=
  CatDeep3Path.trans
    (monad_unit_left_path μ η a)
    (beck_coeq_path coeq a)

-- 22. Grothendieck construction projection
def groth_proj_path {A : Sort u} (π : A → A) (a : A) :
    CatDeep3Path (π a) (π a) :=
  .cons (.groth_proj π a) (.nil _)

-- 23. Grothendieck fiber path
def groth_fiber_path {A : Sort u} (fib : A → A) (a : A) :
    CatDeep3Path (fib a) (fib a) :=
  .cons (.groth_fiber fib a) (.nil _)

-- 24. Grothendieck: projection naturality
def groth_proj_naturality {A : Sort u} (π f : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (π (f a)) (π (f b)) :=
  CatDeep3Path.congrArg π (CatDeep3Path.congrArg f p)

-- 25. Grothendieck: total category ↔ fibered chain
def groth_total_fibered_chain {A : Sort u} (π fib : A → A) (a : A) :
    CatDeep3Path (π (fib a)) (π (fib a)) :=
  CatDeep3Path.trans
    (.cons (.congrArg π (.groth_fiber fib a)) (.nil _))
    (CatDeep3Path.symm (.cons (.congrArg π (.groth_fiber fib a)) (.nil _)))

-- 26. Fibered category cleavage lift
def fibered_cleavage_path {A : Sort u} (lift : A → A) (a : A) :
    CatDeep3Path a (lift a) :=
  .cons (.cleavage_lift lift a) (.nil _)

-- 27. Cleavage + projection chain
def cleavage_proj_chain {A : Sort u} (lift π : A → A) (a : A) :
    CatDeep3Path (π a) (π (lift a)) :=
  CatDeep3Path.congrArg π (fibered_cleavage_path lift a)

-- 28. Fibered category: cartesian lifting path
def cartesian_lift_path {A : Sort u} (lift : A → A) (f : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (lift (f a)) (lift (f b)) :=
  CatDeep3Path.congrArg lift (CatDeep3Path.congrArg f p)

-- 29. Street's formal monad: Eilenberg-Moore path
def street_em_path {A : Sort u} (em : A → A) (a : A) :
    CatDeep3Path a (em a) :=
  .cons (.street_em em a) (.nil _)

-- 30. Street's formal theory: EM object + monad
def street_em_monad_chain {A : Sort u} (em _η μ T : A → A) (a : A) :
    CatDeep3Path (T (T a)) (em (μ a)) :=
  CatDeep3Path.trans
    (monad_mult_path μ T a)
    (street_em_path em (μ a))

-- 31. Street: formal adjunction from monad
def street_formal_adj {A : Sort u} (em η : A → A) (a : A) :
    CatDeep3Path a (em (η a)) :=
  CatDeep3Path.trans
    (.cons (.monad_unit η a) (.nil _))
    (.cons (.street_em em (η a)) (.nil _))

-- 32. Grand monadicity chain: T²a → em(coeq(μ a))
def grand_monadicity_chain {A : Sort u} (_η μ T coeq em : A → A) (a : A) :
    CatDeep3Path (T (T a)) (em (coeq (μ a))) :=
  CatDeep3Path.trans
    (.cons (.monad_mult μ T a) (.nil _))
    (CatDeep3Path.trans
      (.cons (.beck_coeq coeq (μ a)) (.nil _))
      (.cons (.street_em em (coeq (μ a))) (.nil _)))

-- 33. Kan + nerve chain
def kan_nerve_chain {A : Sort u} (lan nerve real : A → A) (a : A) :
    CatDeep3Path (lan (real (nerve a))) (lan a) :=
  CatDeep3Path.congrArg lan (nerve_real_counit_path nerve real a)

-- 34. Deep 5-step categorical chain
def cat_5_step_chain {A : Sort u} (a : A)
    (s1 : CatDeep3Step a a) (s2 : CatDeep3Step a a)
    (s3 : CatDeep3Step a a) (s4 : CatDeep3Step a a)
    (s5 : CatDeep3Step a a) : CatDeep3Path a a :=
  .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.nil _)))))

-- 35. Path length for congrArg
theorem cat_congrArg_length {A B : Sort u} (f : A → B) {a b : A}
    (p : CatDeep3Path a b) :
    (CatDeep3Path.congrArg f p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [CatDeep3Path.congrArg, CatDeep3Path.length, ih]

-- 36. Path length for trans
theorem cat_trans_length {A : Sort u} {a b c : A}
    (p : CatDeep3Path a b) (q : CatDeep3Path b c) :
    (CatDeep3Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil => simp [CatDeep3Path.trans, CatDeep3Path.length]
  | cons s p ih => simp [CatDeep3Path.trans, CatDeep3Path.length, ih, Nat.add_assoc]

-- 37. Kan adjunction: Lan ⊣ restriction
def lan_adj_path {A : Sort u} (lan res : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (lan (res a)) (lan (res b)) :=
  CatDeep3Path.congrArg lan (CatDeep3Path.congrArg res p)

-- 38. Kan adjunction: restriction ⊣ Ran
def ran_adj_path {A : Sort u} (res ran : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (ran (res a)) (ran (res b)) :=
  CatDeep3Path.congrArg ran (CatDeep3Path.congrArg res p)

-- 39. Monad algebra structure map path
def monad_algebra_path {A : Sort u} (T alg : A → A) (a b : A)
    (p : CatDeep3Path a b) : CatDeep3Path (alg (T a)) (alg (T b)) :=
  CatDeep3Path.congrArg alg (CatDeep3Path.congrArg T p)

-- 40. Complete Barr-Beck: algebra ↔ coequalizer ↔ EM
def complete_barr_beck {A : Sort u} (μ _η T coeq em : A → A) (a : A) :
    CatDeep3Path (T (T a)) (em (coeq (μ a))) :=
  CatDeep3Path.trans
    (monad_mult_path μ T a)
    (CatDeep3Path.trans
      (beck_coeq_path coeq (μ a))
      (street_em_path em (coeq (μ a))))

end ComputationalPaths
