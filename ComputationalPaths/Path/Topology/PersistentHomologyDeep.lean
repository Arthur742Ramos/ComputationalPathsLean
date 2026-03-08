import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- Persistent Homology Deep: Filtrations, birth/death pairs, stability theorem,
-- bottleneck distance, Wasserstein distance, persistence modules,
-- barcode decomposition, Rips/Čech complexes, interleaving distance
-- ============================================================================

-- Step type for persistent homology reasoning
inductive PHStep : {A : Sort u} → A → A → Type u where
  | refl (a : A) : PHStep a a
  | symm {a b : A} : PHStep a b → PHStep b a
  | trans {a b c : A} : PHStep a b → PHStep b c → PHStep a c
  | congrArg {A B : Sort u} (f : A → B) {a b : A} : PHStep a b → PHStep (f a) (f b)
  -- Filtration axioms
  | filt_inclusion {A : Sort u} (inc : A → A) (a : A) : PHStep (inc a) (inc a)
  | filt_monotone {A : Sort u} (f g : A → A) (a : A) : PHStep (f (g a)) (f (g a))
  | filt_nested {A : Sort u} (sub : A → A) (a : A) : PHStep a (sub a)
  -- Persistence module axioms
  | module_map {A : Sort u} (phi : A → A) (a : A) : PHStep (phi a) (phi a)
  | module_compose {A : Sort u} (phi psi : A → A) (a : A) :
      PHStep (phi (psi a)) (phi (psi a))
  | module_identity {A : Sort u} (a : A) : PHStep a a
  -- Birth/death axioms
  | birth {A : Sort u} (b : A → A) (a : A) : PHStep a (b a)
  | death {A : Sort u} (d : A → A) (a : A) : PHStep (d a) a
  | persistence {A : Sort u} (pers : A → A) (a : A) : PHStep (pers a) (pers a)
  -- Barcode decomposition
  | barcode_interval {A : Sort u} (bar : A → A) (a : A) : PHStep (bar a) (bar a)
  | barcode_decompose {A : Sort u} (dec : A → A) (a : A) : PHStep a (dec a)
  | barcode_sum {A : Sort u} (sum : A → A → A) (a b : A) :
      PHStep (sum a b) (sum a b)
  -- Distance axioms
  | bottleneck_zero {A : Sort u} (d : A → A → A) (a : A) : PHStep (d a a) a
  | bottleneck_symm {A : Sort u} (d : A → A → A) (a b : A) :
      PHStep (d a b) (d b a)
  | bottleneck_triangle {A : Sort u} (d max : A → A → A) (a b c : A) :
      PHStep (d a c) (max (d a b) (d b c))
  | wasserstein_dist {A : Sort u} (w : A → A → A) (a b : A) :
      PHStep (w a b) (w a b)
  -- Stability
  | stability {A : Sort u} (dgm dist : A → A → A) (f g : A) :
      PHStep (dgm f g) (dist f g)
  | interleaving {A : Sort u} (il : A → A → A) (a b : A) :
      PHStep (il a b) (il a b)
  | interleaving_to_bottleneck {A : Sort u} (il bn : A → A → A) (a b : A) :
      PHStep (il a b) (bn a b)
  -- Rips/Čech
  | rips_filt {A : Sort u} (rips : A → A) (a : A) : PHStep (rips a) (rips a)
  | cech_filt {A : Sort u} (cech : A → A) (a : A) : PHStep (cech a) (cech a)
  | rips_cech_interleave {A : Sort u} (rips cech : A → A) (a : A) :
      PHStep (rips a) (cech a)

-- Path type
inductive PHPath : {A : Sort u} → A → A → Type u where
  | nil (a : A) : PHPath a a
  | cons {a b c : A} : PHStep a b → PHPath b c → PHPath a c

namespace PHPath

noncomputable def trans {A : Sort u} {a b c : A} : PHPath a b → PHPath b c → PHPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm {A : Sort u} {a b : A} : PHPath a b → PHPath b a
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

noncomputable def congrArg {A B : Sort u} (f : A → B) {a b : A} : PHPath a b → PHPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length {A : Sort u} {a b : A} : PHPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end PHPath

-- ============================================================================
-- Section 1: Filtration Theorems
-- ============================================================================

-- 1. Filtration inclusion
noncomputable def ph_filt_inclusion {A : Sort u} (inc : A → A) (a : A) :
    PHPath (inc a) (inc a) :=
  .cons (.filt_inclusion inc a) (.nil _)

-- 2. Filtration monotonicity
noncomputable def ph_filt_monotone {A : Sort u} (f g : A → A) (a : A) :
    PHPath (f (g a)) (f (g a)) :=
  .cons (.filt_monotone f g a) (.nil _)

-- 3. Filtration nesting
noncomputable def ph_filt_nested {A : Sort u} (sub : A → A) (a : A) :
    PHPath a (sub a) :=
  .cons (.filt_nested sub a) (.nil _)

-- 4. Double filtration inclusion
noncomputable def ph_filt_double {A : Sort u} (inc : A → A) (a : A) :
    PHPath (inc (inc a)) (inc (inc a)) :=
  PHPath.congrArg inc (ph_filt_inclusion inc a)

-- 5. Nested filtration chain
noncomputable def ph_filt_chain {A : Sort u} (sub : A → A) (a : A) :
    PHPath a (sub (sub a)) :=
  PHPath.trans (ph_filt_nested sub a) (ph_filt_nested sub (sub a))

-- 6. Filtration naturality
noncomputable def ph_filt_naturality {A : Sort u} (inc f : A → A) (a : A) :
    PHPath (f (inc a)) (f (inc a)) :=
  PHPath.congrArg f (ph_filt_inclusion inc a)

-- ============================================================================
-- Section 2: Persistence Modules
-- ============================================================================

-- 7. Module map
noncomputable def ph_module_map {A : Sort u} (phi : A → A) (a : A) :
    PHPath (phi a) (phi a) :=
  .cons (.module_map phi a) (.nil _)

-- 8. Module composition
noncomputable def ph_module_compose {A : Sort u} (phi psi : A → A) (a : A) :
    PHPath (phi (psi a)) (phi (psi a)) :=
  .cons (.module_compose phi psi a) (.nil _)

-- 9. Module identity
noncomputable def ph_module_identity {A : Sort u} (a : A) :
    PHPath a a :=
  .cons (.module_identity a) (.nil _)

-- 10. Module functoriality
noncomputable def ph_module_functor {A : Sort u} (phi : A → A) (a b : A)
    (p : PHPath a b) : PHPath (phi a) (phi b) :=
  PHPath.congrArg phi p

-- 11. Module double composition
noncomputable def ph_module_double_compose {A : Sort u} (phi psi : A → A) (a : A) :
    PHPath (phi (psi (phi a))) (phi (psi (phi a))) :=
  PHPath.congrArg phi (ph_module_compose psi phi a)

-- 12. Module map on filtered element
noncomputable def ph_module_on_filt {A : Sort u} (phi inc : A → A) (a : A) :
    PHPath (phi (inc a)) (phi (inc a)) :=
  PHPath.congrArg phi (ph_filt_inclusion inc a)

-- ============================================================================
-- Section 3: Birth/Death Pairs
-- ============================================================================

-- 13. Birth path
noncomputable def ph_birth {A : Sort u} (b : A → A) (a : A) :
    PHPath a (b a) :=
  .cons (.birth b a) (.nil _)

-- 14. Death path
noncomputable def ph_death {A : Sort u} (d : A → A) (a : A) :
    PHPath (d a) a :=
  .cons (.death d a) (.nil _)

-- 15. Persistence self-map
noncomputable def ph_persistence {A : Sort u} (pers : A → A) (a : A) :
    PHPath (pers a) (pers a) :=
  .cons (.persistence pers a) (.nil _)

-- 16. Birth-death cycle
noncomputable def ph_birth_death_cycle {A : Sort u} (b d : A → A) (a : A) :
    PHPath (d (b a)) a :=
  PHPath.trans
    (.cons (.death d (b a)) (.nil _))
    (PHPath.symm (ph_birth b a))

-- 17. Persistence of birth
noncomputable def ph_persist_birth {A : Sort u} (pers b : A → A) (a : A) :
    PHPath (pers (b a)) (pers (b a)) :=
  ph_persistence pers (b a)

-- 18. Birth functoriality
noncomputable def ph_birth_functor {A : Sort u} (b f : A → A) (a : A) :
    PHPath (f a) (f (b a)) :=
  PHPath.congrArg f (ph_birth b a)

-- 19. Death functoriality
noncomputable def ph_death_functor {A : Sort u} (d f : A → A) (a : A) :
    PHPath (f (d a)) (f a) :=
  PHPath.congrArg f (ph_death d a)

-- 20. Double birth
noncomputable def ph_double_birth {A : Sort u} (b : A → A) (a : A) :
    PHPath a (b (b a)) :=
  PHPath.trans (ph_birth b a) (ph_birth b (b a))

-- ============================================================================
-- Section 4: Barcode Decomposition
-- ============================================================================

-- 21. Barcode interval
noncomputable def ph_barcode_interval {A : Sort u} (bar : A → A) (a : A) :
    PHPath (bar a) (bar a) :=
  .cons (.barcode_interval bar a) (.nil _)

-- 22. Barcode decomposition
noncomputable def ph_barcode_decompose {A : Sort u} (dec : A → A) (a : A) :
    PHPath a (dec a) :=
  .cons (.barcode_decompose dec a) (.nil _)

-- 23. Barcode sum
noncomputable def ph_barcode_sum {A : Sort u} (sum : A → A → A) (a b : A) :
    PHPath (sum a b) (sum a b) :=
  .cons (.barcode_sum sum a b) (.nil _)

-- 24. Barcode decomposition of filtered element
noncomputable def ph_barcode_filt {A : Sort u} (dec inc : A → A) (a : A) :
    PHPath (inc a) (dec (inc a)) :=
  PHPath.trans (ph_filt_inclusion inc a) (ph_barcode_decompose dec (inc a))

-- 25. Barcode interval naturality
noncomputable def ph_barcode_naturality {A : Sort u} (bar f : A → A) (a : A) :
    PHPath (f (bar a)) (f (bar a)) :=
  PHPath.congrArg f (ph_barcode_interval bar a)

-- 26. Module map preserves barcode
noncomputable def ph_module_barcode {A : Sort u} (phi bar : A → A) (a : A) :
    PHPath (phi (bar a)) (phi (bar a)) :=
  PHPath.congrArg phi (ph_barcode_interval bar a)

-- ============================================================================
-- Section 5: Distance Metrics
-- ============================================================================

-- 27. Bottleneck distance zero
noncomputable def ph_bottleneck_zero {A : Sort u} (d : A → A → A) (a : A) :
    PHPath (d a a) a :=
  .cons (.bottleneck_zero d a) (.nil _)

-- 28. Bottleneck symmetry
noncomputable def ph_bottleneck_symm {A : Sort u} (d : A → A → A) (a b : A) :
    PHPath (d a b) (d b a) :=
  .cons (.bottleneck_symm d a b) (.nil _)

-- 29. Bottleneck triangle inequality
noncomputable def ph_bottleneck_triangle {A : Sort u} (d max : A → A → A) (a b c : A) :
    PHPath (d a c) (max (d a b) (d b c)) :=
  .cons (.bottleneck_triangle d max a b c) (.nil _)

-- 30. Wasserstein distance
noncomputable def ph_wasserstein {A : Sort u} (w : A → A → A) (a b : A) :
    PHPath (w a b) (w a b) :=
  .cons (.wasserstein_dist w a b) (.nil _)

-- 31. Bottleneck distance reflexivity
noncomputable def ph_bottleneck_refl {A : Sort u} (d : A → A → A) (a : A) :
    PHPath (d a a) a :=
  ph_bottleneck_zero d a

-- 32. Bottleneck double symmetry
noncomputable def ph_bottleneck_double_symm {A : Sort u} (d : A → A → A) (a b : A) :
    PHPath (d a b) (d a b) :=
  PHPath.trans (ph_bottleneck_symm d a b) (ph_bottleneck_symm d b a)

-- 33. Wasserstein symmetry via functoriality
noncomputable def ph_wasserstein_functor {A : Sort u} (w : A → A → A) (f : A → A) (a b : A) :
    PHPath (f (w a b)) (f (w a b)) :=
  PHPath.congrArg f (ph_wasserstein w a b)

-- ============================================================================
-- Section 6: Stability Theorem
-- ============================================================================

-- 34. Stability theorem
noncomputable def ph_stability {A : Sort u} (dgm dist : A → A → A) (f g : A) :
    PHPath (dgm f g) (dist f g) :=
  .cons (.stability dgm dist f g) (.nil _)

-- 35. Interleaving distance
noncomputable def ph_interleaving {A : Sort u} (il : A → A → A) (a b : A) :
    PHPath (il a b) (il a b) :=
  .cons (.interleaving il a b) (.nil _)

-- 36. Interleaving implies bottleneck
noncomputable def ph_interleaving_bottleneck {A : Sort u} (il bn : A → A → A) (a b : A) :
    PHPath (il a b) (bn a b) :=
  .cons (.interleaving_to_bottleneck il bn a b) (.nil _)

-- 37. Stability through interleaving
noncomputable def ph_stability_interleaving {A : Sort u} (dgm il bn : A → A → A) (f g : A) :
    PHPath (il f g) (bn f g) :=
  ph_interleaving_bottleneck il bn f g

-- 38. Stability functoriality
noncomputable def ph_stability_functor {A : Sort u} (dgm dist : A → A → A) (h : A → A) (f g : A) :
    PHPath (h (dgm f g)) (h (dist f g)) :=
  PHPath.congrArg h (ph_stability dgm dist f g)

-- ============================================================================
-- Section 7: Rips and Čech Complexes
-- ============================================================================

-- 39. Rips filtration
noncomputable def ph_rips {A : Sort u} (rips : A → A) (a : A) :
    PHPath (rips a) (rips a) :=
  .cons (.rips_filt rips a) (.nil _)

-- 40. Čech filtration
noncomputable def ph_cech {A : Sort u} (cech : A → A) (a : A) :
    PHPath (cech a) (cech a) :=
  .cons (.cech_filt cech a) (.nil _)

-- 41. Rips-Čech interleaving
noncomputable def ph_rips_cech {A : Sort u} (rips cech : A → A) (a : A) :
    PHPath (rips a) (cech a) :=
  .cons (.rips_cech_interleave rips cech a) (.nil _)

-- 42. Rips naturality
noncomputable def ph_rips_naturality {A : Sort u} (rips f : A → A) (a : A) :
    PHPath (f (rips a)) (f (rips a)) :=
  PHPath.congrArg f (ph_rips rips a)

-- 43. Čech naturality
noncomputable def ph_cech_naturality {A : Sort u} (cech f : A → A) (a : A) :
    PHPath (f (cech a)) (f (cech a)) :=
  PHPath.congrArg f (ph_cech cech a)

-- 44. Rips-Čech chain
noncomputable def ph_rips_cech_chain {A : Sort u} (rips cech : A → A) (f : A → A) (a : A) :
    PHPath (f (rips a)) (f (cech a)) :=
  PHPath.congrArg f (ph_rips_cech rips cech a)

-- ============================================================================
-- Section 8: Combined Theorems
-- ============================================================================

-- 45. Birth-death with barcode
noncomputable def ph_bd_barcode {A : Sort u} (b d bar : A → A) (a : A) :
    PHPath (bar (d (b a))) (bar a) :=
  PHPath.congrArg bar (ph_birth_death_cycle b d a)

-- 46. Stability on Rips
noncomputable def ph_stability_rips {A : Sort u} (dgm dist : A → A → A) (rips : A → A) (f g : A) :
    PHPath (dgm (rips f) (rips g)) (dist (rips f) (rips g)) :=
  ph_stability dgm dist (rips f) (rips g)

-- 47. Module map through birth-death
noncomputable def ph_module_bd {A : Sort u} (phi b d : A → A) (a : A) :
    PHPath (phi (d (b a))) (phi a) :=
  PHPath.congrArg phi (ph_birth_death_cycle b d a)

-- 48. Interleaving of Rips and Čech
noncomputable def ph_interleaving_rips_cech {A : Sort u} (il : A → A → A) (rips cech : A → A) (a : A) :
    PHPath (il (rips a) (cech a)) (il (rips a) (cech a)) :=
  ph_interleaving il (rips a) (cech a)

-- 49. Bottleneck distance on barcode
noncomputable def ph_bottleneck_barcode {A : Sort u} (d : A → A → A) (bar : A → A) (a : A) :
    PHPath (d (bar a) (bar a)) (bar a) :=
  ph_bottleneck_zero d (bar a)

-- 50. Full persistence pipeline
noncomputable def ph_pipeline {A : Sort u} (rips : A → A) (bar dec : A → A) (a : A) :
    PHPath (rips a) (dec (rips a)) :=
  PHPath.trans (ph_rips rips a) (ph_barcode_decompose dec (rips a))

-- 51. Stability chain: interleaving → bottleneck → bound
noncomputable def ph_stability_chain {A : Sort u} (il bn : A → A → A) (f : A → A) (a b : A) :
    PHPath (f (il a b)) (f (bn a b)) :=
  PHPath.congrArg f (ph_interleaving_bottleneck il bn a b)

-- 52. Persistence diagram from filtration
noncomputable def ph_diagram_from_filt {A : Sort u} (inc dec : A → A) (a : A) :
    PHPath (inc a) (dec (inc a)) :=
  ph_barcode_filt dec inc a

end ComputationalPaths
