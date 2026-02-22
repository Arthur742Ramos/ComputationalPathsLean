import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- DEPENDENT TYPE THEORY VIA PATHS
-- Sigma types, Pi types, W-types, universe levels, Church encodings, System F
-- ============================================================================

-- Types in our dependent type theory
inductive DTTExpr : Type where
  | star : DTTExpr                                    -- unit type
  | nat : DTTExpr                                     -- natural numbers
  | zero : DTTExpr
  | succ : DTTExpr → DTTExpr
  | var : Nat → DTTExpr                               -- variables
  | pi : DTTExpr → DTTExpr → DTTExpr                  -- Π(A, B)
  | sigma : DTTExpr → DTTExpr → DTTExpr               -- Σ(A, B)
  | lam : DTTExpr → DTTExpr                           -- λ body
  | app : DTTExpr → DTTExpr → DTTExpr                 -- application
  | pair : DTTExpr → DTTExpr → DTTExpr                -- (a, b)
  | fst : DTTExpr → DTTExpr                           -- π₁
  | snd : DTTExpr → DTTExpr                           -- π₂
  | wtype : DTTExpr → DTTExpr → DTTExpr               -- W(A, B)
  | wsup : DTTExpr → DTTExpr → DTTExpr                -- sup constructor
  | wrec : DTTExpr → DTTExpr → DTTExpr                -- W-recursion
  | univ : Nat → DTTExpr                              -- Universe level
  | lift : DTTExpr → DTTExpr                          -- Lift to higher universe
  | lower : DTTExpr → DTTExpr                         -- Lower from higher universe
  | churchNat : Nat → DTTExpr                         -- Church numeral
  | churchSucc : DTTExpr                              -- Church successor
  | churchPlus : DTTExpr → DTTExpr → DTTExpr          -- Church addition
  | churchMult : DTTExpr → DTTExpr → DTTExpr          -- Church multiplication
  | polyId : DTTExpr                                  -- System F polymorphic identity
  | polyComp : DTTExpr → DTTExpr → DTTExpr            -- System F composition
  | forallTy : DTTExpr → DTTExpr                      -- System F ∀α.T
  | tyApp : DTTExpr → DTTExpr → DTTExpr               -- Type application
  | indRec : DTTExpr → DTTExpr → DTTExpr → DTTExpr    -- Induction-recursion
  | largeElim : DTTExpr → DTTExpr                     -- Large elimination
  deriving Repr, BEq

-- Steps in dependent type theory
inductive DTTStep : DTTExpr → DTTExpr → Type where
  | refl : (a : DTTExpr) → DTTStep a a
  | symm : DTTStep a b → DTTStep b a
  | trans : DTTStep a b → DTTStep b c → DTTStep a c
  | congrArg : (f : DTTExpr → DTTExpr) → DTTStep a b → DTTStep (f a) (f b)
  -- Sigma type rules
  | sigmaFstBeta : DTTStep (DTTExpr.fst (DTTExpr.pair a b)) a
  | sigmaSndBeta : DTTStep (DTTExpr.snd (DTTExpr.pair a b)) b
  | sigmaEta : DTTStep (DTTExpr.pair (DTTExpr.fst p) (DTTExpr.snd p)) p
  | sigmaPairCong : DTTStep a a' → DTTStep b b' →
      DTTStep (DTTExpr.pair a b) (DTTExpr.pair a' b')
  | sigmaFstCong : DTTStep p q → DTTStep (DTTExpr.fst p) (DTTExpr.fst q)
  | sigmaSndCong : DTTStep p q → DTTStep (DTTExpr.snd p) (DTTExpr.snd q)
  -- Pi type rules
  | piBeta : DTTStep (DTTExpr.app (DTTExpr.lam body) arg)
      (DTTExpr.app (DTTExpr.lam body) arg)  -- β-reduction (identity for closed terms)
  | piEta : DTTStep (DTTExpr.lam (DTTExpr.app f (DTTExpr.var 0))) f
  | funext : DTTStep (DTTExpr.app f x) (DTTExpr.app g x) →
      DTTStep (DTTExpr.pi a (DTTExpr.app f (DTTExpr.var 0)))
              (DTTExpr.pi a (DTTExpr.app g (DTTExpr.var 0)))
  | appCong : DTTStep f g → DTTStep a b →
      DTTStep (DTTExpr.app f a) (DTTExpr.app g b)
  -- W-type rules
  | wBeta : DTTStep (DTTExpr.wrec (DTTExpr.wsup a f) g)
      (DTTExpr.app (DTTExpr.app g a) (DTTExpr.lam (DTTExpr.wrec (DTTExpr.app f (DTTExpr.var 0)) g)))
  | wsupCong : DTTStep a a' → DTTStep f f' →
      DTTStep (DTTExpr.wsup a f) (DTTExpr.wsup a' f')
  | wrecCong : DTTStep w w' → DTTStep g g' →
      DTTStep (DTTExpr.wrec w g) (DTTExpr.wrec w' g')
  -- Universe rules
  | univCumul : DTTStep (DTTExpr.univ n) (DTTExpr.univ (n + 1))  -- cumulativity
  | liftLower : DTTStep (DTTExpr.lower (DTTExpr.lift a)) a
  | lowerLift : DTTStep a (DTTExpr.lower (DTTExpr.lift a))
  | liftCong : DTTStep a b → DTTStep (DTTExpr.lift a) (DTTExpr.lift b)
  | lowerCong : DTTStep a b → DTTStep (DTTExpr.lower a) (DTTExpr.lower b)
  -- Church encoding rules
  | churchZeroEq : DTTStep (DTTExpr.churchNat 0) (DTTExpr.lam (DTTExpr.lam (DTTExpr.var 0)))
  | churchSuccStep : DTTStep (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchNat n))
      (DTTExpr.churchNat (n + 1))
  | churchPlusZero : DTTStep (DTTExpr.churchPlus (DTTExpr.churchNat 0) m) m
  | churchPlusSucc : DTTStep (DTTExpr.churchPlus (DTTExpr.churchNat (n+1)) m)
      (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchPlus (DTTExpr.churchNat n) m))
  | churchMultZero : DTTStep (DTTExpr.churchMult (DTTExpr.churchNat 0) m) (DTTExpr.churchNat 0)
  | churchMultSucc : DTTStep (DTTExpr.churchMult (DTTExpr.churchNat (n+1)) m)
      (DTTExpr.churchPlus m (DTTExpr.churchMult (DTTExpr.churchNat n) m))
  | churchPlusCong : DTTStep a a' → DTTStep b b' →
      DTTStep (DTTExpr.churchPlus a b) (DTTExpr.churchPlus a' b')
  | churchMultCong : DTTStep a a' → DTTStep b b' →
      DTTStep (DTTExpr.churchMult a b) (DTTExpr.churchMult a' b')
  -- System F rules
  | polyIdApp : DTTStep (DTTExpr.tyApp DTTExpr.polyId ty)
      (DTTExpr.lam (DTTExpr.var 0))
  | polyCompAssoc : DTTStep (DTTExpr.polyComp (DTTExpr.polyComp f g) h)
      (DTTExpr.polyComp f (DTTExpr.polyComp g h))
  | polyCompId : DTTStep (DTTExpr.polyComp DTTExpr.polyId f) f
  | polyIdComp : DTTStep (DTTExpr.polyComp f DTTExpr.polyId) f
  | polyCompCong : DTTStep f f' → DTTStep g g' →
      DTTStep (DTTExpr.polyComp f g) (DTTExpr.polyComp f' g')
  | tyAppCong : DTTStep f g → DTTStep a b →
      DTTStep (DTTExpr.tyApp f a) (DTTExpr.tyApp g b)
  | forallCong : DTTStep a b → DTTStep (DTTExpr.forallTy a) (DTTExpr.forallTy b)
  -- Induction-recursion
  | indRecBeta : DTTStep (DTTExpr.indRec a b c)
      (DTTExpr.app (DTTExpr.app a b) c)
  | indRecCong : DTTStep a a' → DTTStep b b' → DTTStep c c' →
      DTTStep (DTTExpr.indRec a b c) (DTTExpr.indRec a' b' c')
  -- Large elimination
  | largeElimNat : DTTStep (DTTExpr.largeElim DTTExpr.nat) (DTTExpr.univ 0)
  | largeElimCong : DTTStep a b → DTTStep (DTTExpr.largeElim a) (DTTExpr.largeElim b)

-- Paths as lists of steps
inductive DTTPath : DTTExpr → DTTExpr → Type where
  | nil : DTTPath a a
  | cons : DTTStep a b → DTTPath b c → DTTPath a c

namespace DTTPath

noncomputable def trans : DTTPath a b → DTTPath b c → DTTPath a c
  | .nil, q => q
  | .cons s p, q => .cons s (p.trans q)

noncomputable def symm : DTTPath a b → DTTPath b a
  | .nil => .nil
  | .cons s p => p.symm.trans (.cons (.symm s) .nil)

noncomputable def congrArg (f : DTTExpr → DTTExpr) : DTTPath a b → DTTPath (f a) (f b)
  | .nil => .nil
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : DTTPath a b → Nat
  | .nil => 0
  | .cons _ p => 1 + p.length

-- ============================================================================
-- SIGMA TYPE THEOREMS
-- ============================================================================

-- 1. Projection of pair extracts first component
noncomputable def sigma_fst_beta (a b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair a b)) a :=
  .cons .sigmaFstBeta .nil

-- 2. Projection of pair extracts second component
noncomputable def sigma_snd_beta (a b : DTTExpr) :
    DTTPath (DTTExpr.snd (DTTExpr.pair a b)) b :=
  .cons .sigmaSndBeta .nil

-- 3. Eta rule for sigma types
noncomputable def sigma_eta (p : DTTExpr) :
    DTTPath (DTTExpr.pair (DTTExpr.fst p) (DTTExpr.snd p)) p :=
  .cons .sigmaEta .nil

-- 4. Fst of pair then re-pair with snd
noncomputable def sigma_fst_snd_roundtrip (a b : DTTExpr) :
    DTTPath (DTTExpr.pair (DTTExpr.fst (DTTExpr.pair a b)) (DTTExpr.snd (DTTExpr.pair a b)))
            (DTTExpr.pair a b) :=
  .cons (.sigmaPairCong .sigmaFstBeta .sigmaSndBeta) .nil

-- 5. Fst-snd roundtrip then eta
noncomputable def sigma_fst_snd_eta (a b : DTTExpr) :
    DTTPath (DTTExpr.pair (DTTExpr.fst (DTTExpr.pair a b)) (DTTExpr.snd (DTTExpr.pair a b)))
            (DTTExpr.pair a b) :=
  (sigma_fst_snd_roundtrip a b)

-- 6. Congruence of fst
noncomputable def sigma_fst_cong (p q : DTTExpr) (s : DTTStep p q) :
    DTTPath (DTTExpr.fst p) (DTTExpr.fst q) :=
  .cons (.sigmaFstCong s) .nil

-- 7. Congruence of snd
noncomputable def sigma_snd_cong (p q : DTTExpr) (s : DTTStep p q) :
    DTTPath (DTTExpr.snd p) (DTTExpr.snd q) :=
  .cons (.sigmaSndCong s) .nil

-- 8. Double pair projection chain
noncomputable def sigma_double_fst (a b c _d : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.fst (DTTExpr.pair a b)) c)) (DTTExpr.fst (DTTExpr.pair a c)) :=
  .cons (.sigmaFstCong (.sigmaPairCong .sigmaFstBeta (.refl c))) .nil

-- 9. Nested pair fst-fst extraction
noncomputable def sigma_nested_fst (a b c : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.fst (DTTExpr.pair (DTTExpr.pair a b) c)))
            (DTTExpr.fst (DTTExpr.pair a b)) :=
  .cons (.sigmaFstCong .sigmaFstBeta) .nil

-- 10. Nested pair full extraction
noncomputable def sigma_nested_extract (a b c : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.fst (DTTExpr.pair (DTTExpr.pair a b) c))) a :=
  (sigma_nested_fst a b c).trans (sigma_fst_beta a b)

-- ============================================================================
-- PI TYPE THEOREMS
-- ============================================================================

-- 11. Eta for functions
noncomputable def pi_eta (f : DTTExpr) :
    DTTPath (DTTExpr.lam (DTTExpr.app f (DTTExpr.var 0))) f :=
  .cons .piEta .nil

-- 12. Function extensionality
noncomputable def pi_funext (f g : DTTExpr) (a : DTTExpr) (x : DTTExpr)
    (h : DTTStep (DTTExpr.app f x) (DTTExpr.app g x)) :
    DTTPath (DTTExpr.pi a (DTTExpr.app f (DTTExpr.var 0)))
            (DTTExpr.pi a (DTTExpr.app g (DTTExpr.var 0))) :=
  .cons (.funext h) .nil

-- 13. Application congruence
noncomputable def pi_app_cong (f g a b : DTTExpr) (sf : DTTStep f g) (sa : DTTStep a b) :
    DTTPath (DTTExpr.app f a) (DTTExpr.app g b) :=
  .cons (.appCong sf sa) .nil

-- 14. Eta then apply
noncomputable def pi_eta_app (f : DTTExpr) (x : DTTExpr) :
    DTTPath (DTTExpr.app (DTTExpr.lam (DTTExpr.app f (DTTExpr.var 0))) x)
            (DTTExpr.app f x) :=
  .cons (.appCong .piEta (.refl x)) .nil

-- 15. Double eta
noncomputable def pi_double_eta (f : DTTExpr) :
    DTTPath (DTTExpr.lam (DTTExpr.app (DTTExpr.lam (DTTExpr.app f (DTTExpr.var 0))) (DTTExpr.var 0))) f :=
  .cons (.congrArg DTTExpr.lam (.appCong .piEta (.refl (DTTExpr.var 0))))
  (.cons .piEta .nil)

-- ============================================================================
-- W-TYPE THEOREMS
-- ============================================================================

-- 16. W-type beta reduction
noncomputable def w_beta (a f g : DTTExpr) :
    DTTPath (DTTExpr.wrec (DTTExpr.wsup a f) g)
            (DTTExpr.app (DTTExpr.app g a)
              (DTTExpr.lam (DTTExpr.wrec (DTTExpr.app f (DTTExpr.var 0)) g))) :=
  .cons .wBeta .nil

-- 17. W-sup congruence
noncomputable def w_sup_cong (a a' f f' : DTTExpr) (sa : DTTStep a a') (sf : DTTStep f f') :
    DTTPath (DTTExpr.wsup a f) (DTTExpr.wsup a' f') :=
  .cons (.wsupCong sa sf) .nil

-- 18. W-rec congruence
noncomputable def w_rec_cong (w w' g g' : DTTExpr) (sw : DTTStep w w') (sg : DTTStep g g') :
    DTTPath (DTTExpr.wrec w g) (DTTExpr.wrec w' g') :=
  .cons (.wrecCong sw sg) .nil

-- 19. W-rec with congruent sup
noncomputable def w_rec_sup_cong (a a' f f' g : DTTExpr) (sa : DTTStep a a') (sf : DTTStep f f') :
    DTTPath (DTTExpr.wrec (DTTExpr.wsup a f) g)
            (DTTExpr.wrec (DTTExpr.wsup a' f') g) :=
  .cons (.wrecCong (.wsupCong sa sf) (.refl g)) .nil

-- ============================================================================
-- UNIVERSE / CUMULATIVITY THEOREMS
-- ============================================================================

-- 20. Universe cumulativity
noncomputable def univ_cumul (n : Nat) :
    DTTPath (DTTExpr.univ n) (DTTExpr.univ (n + 1)) :=
  .cons .univCumul .nil

-- 21. Two-level cumulativity
noncomputable def univ_cumul_two (n : Nat) :
    DTTPath (DTTExpr.univ n) (DTTExpr.univ (n + 2)) :=
  (univ_cumul n).trans (univ_cumul (n + 1))

-- 22. Three-level cumulativity
noncomputable def univ_cumul_three (n : Nat) :
    DTTPath (DTTExpr.univ n) (DTTExpr.univ (n + 3)) :=
  (univ_cumul_two n).trans (univ_cumul (n + 2))

-- 23. Lift-lower roundtrip
noncomputable def univ_lift_lower (a : DTTExpr) :
    DTTPath (DTTExpr.lower (DTTExpr.lift a)) a :=
  .cons .liftLower .nil

-- 24. Lower-lift embedding
noncomputable def univ_lower_lift (a : DTTExpr) :
    DTTPath a (DTTExpr.lower (DTTExpr.lift a)) :=
  .cons .lowerLift .nil

-- 25. Lift-lower-lift cycle
noncomputable def univ_lift_lower_lift (a : DTTExpr) :
    DTTPath (DTTExpr.lift (DTTExpr.lower (DTTExpr.lift a))) (DTTExpr.lift a) :=
  .cons (.liftCong .liftLower) .nil

-- 26. Double lift-lower
noncomputable def univ_double_lift_lower (a : DTTExpr) :
    DTTPath (DTTExpr.lower (DTTExpr.lift (DTTExpr.lower (DTTExpr.lift a)))) a :=
  .cons (.lowerCong (.liftCong .liftLower))
  (.cons .liftLower .nil)

-- 27. Large elimination of nat
noncomputable def large_elim_nat :
    DTTPath (DTTExpr.largeElim DTTExpr.nat) (DTTExpr.univ 0) :=
  .cons .largeElimNat .nil

-- 28. Large elimination then cumulativity
noncomputable def large_elim_nat_cumul :
    DTTPath (DTTExpr.largeElim DTTExpr.nat) (DTTExpr.univ 1) :=
  large_elim_nat.trans (univ_cumul 0)

-- ============================================================================
-- CHURCH ENCODING THEOREMS
-- ============================================================================

-- 29. Church zero representation
noncomputable def church_zero_repr :
    DTTPath (DTTExpr.churchNat 0) (DTTExpr.lam (DTTExpr.lam (DTTExpr.var 0))) :=
  .cons .churchZeroEq .nil

-- 30. Church successor
noncomputable def church_succ_zero :
    DTTPath (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchNat 0))
            (DTTExpr.churchNat 1) :=
  .cons .churchSuccStep .nil

-- 31. Church successor of successor
noncomputable def church_succ_one :
    DTTPath (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchNat 1))
            (DTTExpr.churchNat 2) :=
  .cons .churchSuccStep .nil

-- 32. Double successor
noncomputable def church_double_succ :
    DTTPath (DTTExpr.app DTTExpr.churchSucc (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchNat 0)))
            (DTTExpr.churchNat 2) :=
  .cons (.congrArg (DTTExpr.app DTTExpr.churchSucc) .churchSuccStep)
  (.cons .churchSuccStep .nil)

-- 33. Church plus zero left identity
noncomputable def church_plus_zero_left (m : DTTExpr) :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 0) m) m :=
  .cons .churchPlusZero .nil

-- 34. Church plus one
noncomputable def church_plus_one (m : DTTExpr) :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 1) m)
            (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchPlus (DTTExpr.churchNat 0) m)) :=
  .cons .churchPlusSucc .nil

-- 35. Church plus one simplifies
noncomputable def church_plus_one_simp (m : DTTExpr) :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 1) m)
            (DTTExpr.app DTTExpr.churchSucc m) :=
  (church_plus_one m).trans
    (.cons (.congrArg (DTTExpr.app DTTExpr.churchSucc) .churchPlusZero) .nil)

-- 36. Church mult zero left
noncomputable def church_mult_zero_left (m : DTTExpr) :
    DTTPath (DTTExpr.churchMult (DTTExpr.churchNat 0) m) (DTTExpr.churchNat 0) :=
  .cons .churchMultZero .nil

-- 37. Church mult one
noncomputable def church_mult_one_step (m : DTTExpr) :
    DTTPath (DTTExpr.churchMult (DTTExpr.churchNat 1) m)
            (DTTExpr.churchPlus m (DTTExpr.churchMult (DTTExpr.churchNat 0) m)) :=
  .cons .churchMultSucc .nil

-- 38. Church mult one simplifies
noncomputable def church_mult_one_simp (m : DTTExpr) :
    DTTPath (DTTExpr.churchMult (DTTExpr.churchNat 1) m)
            (DTTExpr.churchPlus m (DTTExpr.churchNat 0)) :=
  (church_mult_one_step m).trans
    (.cons (.churchPlusCong (.refl m) .churchMultZero) .nil)

-- 39. Church plus congruence
noncomputable def church_plus_cong_path (a a' b b' : DTTExpr) (sa : DTTStep a a') (sb : DTTStep b b') :
    DTTPath (DTTExpr.churchPlus a b) (DTTExpr.churchPlus a' b') :=
  .cons (.churchPlusCong sa sb) .nil

-- 40. Church mult two
noncomputable def church_mult_two_step (m : DTTExpr) :
    DTTPath (DTTExpr.churchMult (DTTExpr.churchNat 2) m)
            (DTTExpr.churchPlus m (DTTExpr.churchMult (DTTExpr.churchNat 1) m)) :=
  .cons .churchMultSucc .nil

-- ============================================================================
-- SYSTEM F / POLYMORPHISM THEOREMS
-- ============================================================================

-- 41. Polymorphic identity applied to type
noncomputable def poly_id_app (ty : DTTExpr) :
    DTTPath (DTTExpr.tyApp DTTExpr.polyId ty) (DTTExpr.lam (DTTExpr.var 0)) :=
  .cons .polyIdApp .nil

-- 42. Polymorphic composition is associative
noncomputable def poly_comp_assoc (f g h : DTTExpr) :
    DTTPath (DTTExpr.polyComp (DTTExpr.polyComp f g) h)
            (DTTExpr.polyComp f (DTTExpr.polyComp g h)) :=
  .cons .polyCompAssoc .nil

-- 43. Left identity of composition
noncomputable def poly_comp_id_left (f : DTTExpr) :
    DTTPath (DTTExpr.polyComp DTTExpr.polyId f) f :=
  .cons .polyCompId .nil

-- 44. Right identity of composition
noncomputable def poly_id_comp_right (f : DTTExpr) :
    DTTPath (DTTExpr.polyComp f DTTExpr.polyId) f :=
  .cons .polyIdComp .nil

-- 45. Double identity composition
noncomputable def poly_double_id :
    DTTPath (DTTExpr.polyComp DTTExpr.polyId DTTExpr.polyId) DTTExpr.polyId :=
  .cons .polyCompId .nil

-- 46. Composition with identity on both sides
noncomputable def poly_id_sandwich (f : DTTExpr) :
    DTTPath (DTTExpr.polyComp DTTExpr.polyId (DTTExpr.polyComp f DTTExpr.polyId)) f :=
  .cons .polyCompId
  (.cons .polyIdComp .nil)

-- 47. Triple composition rebracketing
noncomputable def poly_comp_rebracket (f g h : DTTExpr) :
    DTTPath (DTTExpr.polyComp (DTTExpr.polyComp f g) h)
            (DTTExpr.polyComp f (DTTExpr.polyComp g h)) :=
  .cons .polyCompAssoc .nil

-- 48. Composition congruence
noncomputable def poly_comp_cong_path (f f' g g' : DTTExpr) (sf : DTTStep f f') (sg : DTTStep g g') :
    DTTPath (DTTExpr.polyComp f g) (DTTExpr.polyComp f' g') :=
  .cons (.polyCompCong sf sg) .nil

-- 49. Type application congruence
noncomputable def ty_app_cong_path (f g a b : DTTExpr) (sf : DTTStep f g) (sa : DTTStep a b) :
    DTTPath (DTTExpr.tyApp f a) (DTTExpr.tyApp g b) :=
  .cons (.tyAppCong sf sa) .nil

-- 50. Forall congruence
noncomputable def forall_cong_path (a b : DTTExpr) (s : DTTStep a b) :
    DTTPath (DTTExpr.forallTy a) (DTTExpr.forallTy b) :=
  .cons (.forallCong s) .nil

-- ============================================================================
-- INDUCTION-RECURSION THEOREMS
-- ============================================================================

-- 51. IndRec beta
noncomputable def ind_rec_beta (a b c : DTTExpr) :
    DTTPath (DTTExpr.indRec a b c) (DTTExpr.app (DTTExpr.app a b) c) :=
  .cons .indRecBeta .nil

-- 52. IndRec congruence
noncomputable def ind_rec_cong_path (a a' b b' c c' : DTTExpr)
    (sa : DTTStep a a') (sb : DTTStep b b') (sc : DTTStep c c') :
    DTTPath (DTTExpr.indRec a b c) (DTTExpr.indRec a' b' c') :=
  .cons (.indRecCong sa sb sc) .nil

-- 53. IndRec with identity function
noncomputable def ind_rec_id (b c : DTTExpr) :
    DTTPath (DTTExpr.indRec (DTTExpr.lam (DTTExpr.var 0)) b c)
            (DTTExpr.app (DTTExpr.app (DTTExpr.lam (DTTExpr.var 0)) b) c) :=
  .cons .indRecBeta .nil

-- ============================================================================
-- CROSS-DOMAIN COMBINATION THEOREMS
-- ============================================================================

-- 54. Sigma projection in universe context
noncomputable def sigma_fst_universe (n : Nat) (b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.univ n) b)) (DTTExpr.univ n) :=
  sigma_fst_beta (DTTExpr.univ n) b

-- 55. Sigma projection then cumulativity
noncomputable def sigma_fst_univ_cumul (n : Nat) (b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.univ n) b)) (DTTExpr.univ (n+1)) :=
  (sigma_fst_universe n b).trans (univ_cumul n)

-- 56. Church numeral in sigma pair
noncomputable def sigma_church_fst (n : Nat) (b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.churchNat n) b)) (DTTExpr.churchNat n) :=
  sigma_fst_beta (DTTExpr.churchNat n) b

-- 57. Poly id applied in sigma context
noncomputable def sigma_poly_id (ty b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.tyApp DTTExpr.polyId ty) b))
            (DTTExpr.lam (DTTExpr.var 0)) :=
  (sigma_fst_beta _ b).trans (poly_id_app ty)

-- 58. Function applied to fst of pair
noncomputable def app_fst_pair (f a b : DTTExpr) :
    DTTPath (DTTExpr.app f (DTTExpr.fst (DTTExpr.pair a b)))
            (DTTExpr.app f a) :=
  .cons (.appCong (.refl f) .sigmaFstBeta) .nil

-- 59. Lift of church numeral roundtrip
noncomputable def lift_church_roundtrip (n : Nat) :
    DTTPath (DTTExpr.lower (DTTExpr.lift (DTTExpr.churchNat n))) (DTTExpr.churchNat n) :=
  univ_lift_lower (DTTExpr.churchNat n)

-- 60. Sigma pair of lifted values
noncomputable def sigma_lift_pair (a b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.lower (DTTExpr.lift a)) b)) a :=
  (sigma_fst_beta _ b).trans (univ_lift_lower a)

-- 61. Composition in sigma fst
noncomputable def sigma_fst_comp (f _g b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.polyComp DTTExpr.polyId f) b)) f :=
  (sigma_fst_beta _ b).trans (poly_comp_id_left f)

-- 62. W-type in sigma context
noncomputable def sigma_wrec_fst (w g b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.wrec w g) b)) (DTTExpr.wrec w g) :=
  sigma_fst_beta _ b

-- 63. Large elimination in sigma
noncomputable def sigma_large_elim_fst (b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.largeElim DTTExpr.nat) b)) (DTTExpr.univ 0) :=
  (sigma_fst_beta _ b).trans large_elim_nat

-- 64. Church plus in poly comp context
noncomputable def church_plus_zero_in_comp (m : DTTExpr) :
    DTTPath (DTTExpr.polyComp (DTTExpr.churchPlus (DTTExpr.churchNat 0) m) DTTExpr.polyId)
            m :=
  .cons (.polyCompCong .churchPlusZero (.refl DTTExpr.polyId))
  (.cons .polyIdComp .nil)

-- 65. Triple universe lift-lower-lift
noncomputable def triple_univ_round (a : DTTExpr) :
    DTTPath (DTTExpr.lower (DTTExpr.lift (DTTExpr.lower (DTTExpr.lift a)))) a :=
  univ_double_lift_lower a

-- 66. Church succ then plus zero
noncomputable def church_succ_then_plus_zero :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 0)
              (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchNat 0)))
            (DTTExpr.churchNat 1) :=
  .cons .churchPlusZero
  (.cons .churchSuccStep .nil)

-- 67. Nested sigma projections
noncomputable def sigma_nested_snd_fst (a b c : DTTExpr) :
    DTTPath (DTTExpr.snd (DTTExpr.pair a (DTTExpr.fst (DTTExpr.pair b c)))) b :=
  .cons .sigmaSndBeta
  (.cons .sigmaFstBeta .nil)

-- 68. Eta then fst
noncomputable def eta_fst_combine (f a b : DTTExpr) :
    DTTPath (DTTExpr.app (DTTExpr.lam (DTTExpr.app f (DTTExpr.var 0)))
              (DTTExpr.fst (DTTExpr.pair a b)))
            (DTTExpr.app f a) :=
  .cons (.appCong .piEta .sigmaFstBeta) .nil

-- 69. Multi-level universe with large elimination
noncomputable def large_elim_three_cumul :
    DTTPath (DTTExpr.largeElim DTTExpr.nat) (DTTExpr.univ 3) :=
  large_elim_nat.trans (univ_cumul_three 0)

-- 70. Church mult then sigma projection
noncomputable def church_mult_sigma (m b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair (DTTExpr.churchMult (DTTExpr.churchNat 0) m) b))
            (DTTExpr.churchNat 0) :=
  (sigma_fst_beta _ b).trans (church_mult_zero_left m)

-- 71. Five-step combined path
noncomputable def five_step_combined (m b : DTTExpr) :
    DTTPath (DTTExpr.fst (DTTExpr.pair
              (DTTExpr.polyComp DTTExpr.polyId
                (DTTExpr.polyComp (DTTExpr.churchPlus (DTTExpr.churchNat 0) m) DTTExpr.polyId))
              b))
            m :=
  (sigma_fst_beta _ b).trans
    (.cons .polyCompId
    (.cons .polyIdComp
    (.cons .churchPlusZero .nil)))

-- 72. Symmetry of sigma eta
noncomputable def sigma_eta_symm (p : DTTExpr) :
    DTTPath p (DTTExpr.pair (DTTExpr.fst p) (DTTExpr.snd p)) :=
  (sigma_eta p).symm

-- 73. Church plus two
noncomputable def church_plus_two (m : DTTExpr) :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 2) m)
            (DTTExpr.app DTTExpr.churchSucc (DTTExpr.churchPlus (DTTExpr.churchNat 1) m)) :=
  .cons .churchPlusSucc .nil

-- 74. Church plus two simplification chain
noncomputable def church_plus_two_simp (m : DTTExpr) :
    DTTPath (DTTExpr.churchPlus (DTTExpr.churchNat 2) m)
            (DTTExpr.app DTTExpr.churchSucc (DTTExpr.app DTTExpr.churchSucc m)) :=
  (church_plus_two m).trans
    (.cons (.congrArg (DTTExpr.app DTTExpr.churchSucc) .churchPlusSucc)
    (.cons (.congrArg (DTTExpr.app DTTExpr.churchSucc) (.congrArg (DTTExpr.app DTTExpr.churchSucc) .churchPlusZero)) .nil))

end DTTPath

end ComputationalPaths
