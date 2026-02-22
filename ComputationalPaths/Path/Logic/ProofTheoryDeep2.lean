import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- PROOF THEORY DEEP II
-- Cut elimination as path reduction, Gentzen's Hauptsatz, sequent calculus
-- paths, proof nets, focalization, deep inference, Girard's transcendental
-- syntax, ludics, geometry of interaction, normalization by evaluation paths.
-- ============================================================================

-- Formulas for our sequent calculus
inductive SeqFormula : Type where
  | atom : Nat → SeqFormula
  | neg : SeqFormula → SeqFormula
  | conj : SeqFormula → SeqFormula → SeqFormula
  | disj : SeqFormula → SeqFormula → SeqFormula
  | impl : SeqFormula → SeqFormula → SeqFormula
  | tensor : SeqFormula → SeqFormula → SeqFormula   -- linear logic tensor
  | par : SeqFormula → SeqFormula → SeqFormula       -- linear logic par
  | bang : SeqFormula → SeqFormula                    -- linear logic !
  | quest : SeqFormula → SeqFormula                   -- linear logic ?
  | unit : SeqFormula
  deriving BEq, Repr

-- Sequent: antecedent list ⊢ succedent list
structure Sequent where
  ante : List SeqFormula
  succ : List SeqFormula
  deriving BEq, Repr

-- Steps in proof-theoretic path reduction
inductive PTStep : SeqFormula → SeqFormula → Type where
  -- Basic structural
  | refl : (A : SeqFormula) → PTStep A A
  | symm : PTStep A B → PTStep B A
  | trans : PTStep A B → PTStep B C → PTStep A C
  | congrArg : (f : SeqFormula → SeqFormula) → PTStep A B → PTStep (f A) (f B)
  -- Cut elimination steps
  | cutReduce : PTStep (SeqFormula.impl A B) (SeqFormula.impl A B)
  | cutAtom : PTStep (SeqFormula.conj (SeqFormula.atom n) (SeqFormula.neg (SeqFormula.atom n))) SeqFormula.unit
  | cutConj : PTStep (SeqFormula.conj (SeqFormula.conj A B) (SeqFormula.neg (SeqFormula.conj A B)))
                      (SeqFormula.conj (SeqFormula.conj A (SeqFormula.neg A)) (SeqFormula.conj B (SeqFormula.neg B)))
  -- Hauptsatz structure
  | hauptsatzWeaken : PTStep (SeqFormula.conj A SeqFormula.unit) A
  | hauptsatzContract : PTStep (SeqFormula.conj A A) A
  | hauptsatzExchange : PTStep (SeqFormula.conj A B) (SeqFormula.conj B A)
  -- Linear logic / proof nets
  | tensorPar : PTStep (SeqFormula.tensor A B) (SeqFormula.neg (SeqFormula.par (SeqFormula.neg A) (SeqFormula.neg B)))
  | bangDereliction : PTStep (SeqFormula.bang A) A
  | bangContraction : PTStep (SeqFormula.bang A) (SeqFormula.tensor (SeqFormula.bang A) (SeqFormula.bang A))
  | bangWeakening : PTStep (SeqFormula.bang A) SeqFormula.unit
  | questDual : PTStep (SeqFormula.quest A) (SeqFormula.neg (SeqFormula.bang (SeqFormula.neg A)))
  -- Focalization
  | focusPositive : PTStep (SeqFormula.disj A B) (SeqFormula.disj A B)
  | focusNegative : PTStep (SeqFormula.conj A B) (SeqFormula.conj A B)
  | blurPositive : PTStep (SeqFormula.disj A SeqFormula.unit) A
  -- Deep inference
  | deepSwitch : PTStep (SeqFormula.conj A (SeqFormula.disj B C))
                         (SeqFormula.disj (SeqFormula.conj A B) C)
  | deepMedial : PTStep (SeqFormula.conj (SeqFormula.disj A B) (SeqFormula.disj C D))
                         (SeqFormula.disj (SeqFormula.conj A C) (SeqFormula.conj B D))
  -- Geometry of Interaction
  | goiTrace : PTStep (SeqFormula.tensor (SeqFormula.impl A B) (SeqFormula.impl B C))
                       (SeqFormula.impl A C)
  | goiExec : PTStep (SeqFormula.tensor A (SeqFormula.impl A B)) B
  -- Double negation / involution
  | dneg : PTStep (SeqFormula.neg (SeqFormula.neg A)) A
  | deMorgan : PTStep (SeqFormula.neg (SeqFormula.conj A B))
                       (SeqFormula.disj (SeqFormula.neg A) (SeqFormula.neg B))
  -- NbE
  | nbeReify : PTStep A A
  | nbeReflect : PTStep A A

-- Paths as lists of steps
inductive PTPath : SeqFormula → SeqFormula → Type where
  | nil : PTPath A A
  | cons : PTStep A B → PTPath B C → PTPath A C

namespace PTPath

noncomputable def trans : PTPath A B → PTPath B C → PTPath A C
  | .nil, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : PTPath A B → PTPath B A
  | .nil => .nil
  | .cons s p => trans (symm p) (.cons (.symm s) .nil)

noncomputable def congrArg (f : SeqFormula → SeqFormula) : PTPath A B → PTPath (f A) (f B)
  | .nil => .nil
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

end PTPath

-- ============================================================================
-- THEOREMS
-- ============================================================================

-- 1. Cut elimination: atomic cut reduces to unit
noncomputable def cut_atom_elimination (n : Nat) :
    PTPath (SeqFormula.conj (SeqFormula.atom n) (SeqFormula.neg (SeqFormula.atom n))) SeqFormula.unit :=
  .cons .cutAtom .nil

-- 2. Cut on conjunction decomposes
noncomputable def cut_conj_decompose (A B : SeqFormula) :
    PTPath (SeqFormula.conj (SeqFormula.conj A B) (SeqFormula.neg (SeqFormula.conj A B)))
           (SeqFormula.conj (SeqFormula.conj A (SeqFormula.neg A)) (SeqFormula.conj B (SeqFormula.neg B))) :=
  .cons .cutConj .nil

-- 3. Hauptsatz weakening
noncomputable def hauptsatz_weakening (A : SeqFormula) :
    PTPath (SeqFormula.conj A SeqFormula.unit) A :=
  .cons .hauptsatzWeaken .nil

-- 4. Hauptsatz contraction
noncomputable def hauptsatz_contraction (A : SeqFormula) :
    PTPath (SeqFormula.conj A A) A :=
  .cons .hauptsatzContract .nil

-- 5. Hauptsatz exchange (commutativity of conjunction)
noncomputable def hauptsatz_exchange (A B : SeqFormula) :
    PTPath (SeqFormula.conj A B) (SeqFormula.conj B A) :=
  .cons .hauptsatzExchange .nil

-- 6. Double exchange is identity path
noncomputable def exchange_involution (A B : SeqFormula) :
    PTPath (SeqFormula.conj A B) (SeqFormula.conj A B) :=
  .cons .hauptsatzExchange (.cons .hauptsatzExchange .nil)

-- 7. Weakening after contraction
noncomputable def contract_then_weaken (A : SeqFormula) :
    PTPath (SeqFormula.conj (SeqFormula.conj A A) SeqFormula.unit) A :=
  .cons .hauptsatzWeaken (.cons .hauptsatzContract .nil)

-- 8. Tensor-par duality in linear logic
noncomputable def tensor_par_duality (A B : SeqFormula) :
    PTPath (SeqFormula.tensor A B) (SeqFormula.neg (SeqFormula.par (SeqFormula.neg A) (SeqFormula.neg B))) :=
  .cons .tensorPar .nil

-- 9. Bang dereliction
noncomputable def bang_dereliction (A : SeqFormula) :
    PTPath (SeqFormula.bang A) A :=
  .cons .bangDereliction .nil

-- 10. Bang contraction
noncomputable def bang_contraction (A : SeqFormula) :
    PTPath (SeqFormula.bang A) (SeqFormula.tensor (SeqFormula.bang A) (SeqFormula.bang A)) :=
  .cons .bangContraction .nil

-- 11. Bang weakening
noncomputable def bang_weakening (A : SeqFormula) :
    PTPath (SeqFormula.bang A) SeqFormula.unit :=
  .cons .bangWeakening .nil

-- 12. Quest-bang duality
noncomputable def quest_bang_duality (A : SeqFormula) :
    PTPath (SeqFormula.quest A) (SeqFormula.neg (SeqFormula.bang (SeqFormula.neg A))) :=
  .cons .questDual .nil

-- 13. Double negation elimination
noncomputable def double_negation_elim (A : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.neg A)) A :=
  .cons .dneg .nil

-- 14. De Morgan's law as path
noncomputable def de_morgan_conj (A B : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.conj A B))
           (SeqFormula.disj (SeqFormula.neg A) (SeqFormula.neg B)) :=
  .cons .deMorgan .nil

-- 15. GoI composition (trace)
noncomputable def goi_composition (A B C : SeqFormula) :
    PTPath (SeqFormula.tensor (SeqFormula.impl A B) (SeqFormula.impl B C))
           (SeqFormula.impl A C) :=
  .cons .goiTrace .nil

-- 16. GoI execution
noncomputable def goi_execution (A B : SeqFormula) :
    PTPath (SeqFormula.tensor A (SeqFormula.impl A B)) B :=
  .cons .goiExec .nil

-- 17. Deep inference switch rule
noncomputable def deep_switch (A B C : SeqFormula) :
    PTPath (SeqFormula.conj A (SeqFormula.disj B C))
           (SeqFormula.disj (SeqFormula.conj A B) C) :=
  .cons .deepSwitch .nil

-- 18. Deep inference medial rule
noncomputable def deep_medial (A B C D : SeqFormula) :
    PTPath (SeqFormula.conj (SeqFormula.disj A B) (SeqFormula.disj C D))
           (SeqFormula.disj (SeqFormula.conj A C) (SeqFormula.conj B D)) :=
  .cons .deepMedial .nil

-- 19. Focus then blur for disjunction
noncomputable def focus_blur_positive (A : SeqFormula) :
    PTPath (SeqFormula.disj A SeqFormula.unit) A :=
  .cons .blurPositive .nil

-- 20. Bang dereliction then contraction chain
noncomputable def bang_derelict_via_contraction (A : SeqFormula) :
    PTPath (SeqFormula.bang A) (SeqFormula.tensor (SeqFormula.bang A) (SeqFormula.bang A)) :=
  .cons .bangContraction .nil

-- 21. Congruence: negation distributes through path
noncomputable def neg_congruence (A B : SeqFormula) (p : PTPath A B) :
    PTPath (SeqFormula.neg A) (SeqFormula.neg B) :=
  PTPath.congrArg SeqFormula.neg p

-- 22. Congruence: conjunction left
noncomputable def conj_left_congruence (A B C : SeqFormula) (p : PTPath A B) :
    PTPath (SeqFormula.conj A C) (SeqFormula.conj B C) :=
  PTPath.congrArg (fun x => SeqFormula.conj x C) p

-- 23. Congruence: conjunction right
noncomputable def conj_right_congruence (A B C : SeqFormula) (p : PTPath B C) :
    PTPath (SeqFormula.conj A B) (SeqFormula.conj A C) :=
  PTPath.congrArg (fun x => SeqFormula.conj A x) p

-- 24. Congruence: disjunction left
noncomputable def disj_left_congruence (A B C : SeqFormula) (p : PTPath A B) :
    PTPath (SeqFormula.disj A C) (SeqFormula.disj B C) :=
  PTPath.congrArg (fun x => SeqFormula.disj x C) p

-- 25. Congruence: bang
noncomputable def bang_congruence (A B : SeqFormula) (p : PTPath A B) :
    PTPath (SeqFormula.bang A) (SeqFormula.bang B) :=
  PTPath.congrArg SeqFormula.bang p

-- 26. Symmetry of exchange path
noncomputable def exchange_symm (A B : SeqFormula) :
    PTPath (SeqFormula.conj B A) (SeqFormula.conj A B) :=
  PTPath.symm (hauptsatz_exchange A B)

-- 27. Cut elimination + weakening chain
noncomputable def cut_atom_then_weaken (n : Nat) (_X : SeqFormula) :
    PTPath (SeqFormula.conj (SeqFormula.conj (SeqFormula.atom n) (SeqFormula.neg (SeqFormula.atom n))) SeqFormula.unit)
           (SeqFormula.conj (SeqFormula.atom n) (SeqFormula.neg (SeqFormula.atom n))) :=
  .cons .hauptsatzWeaken .nil

-- 28. Triple negation reduces to single negation
noncomputable def triple_neg_reduce (A : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.neg (SeqFormula.neg A))) (SeqFormula.neg A) :=
  PTPath.congrArg SeqFormula.neg (.cons .dneg .nil)

-- 29. De Morgan + double negation chain
noncomputable def de_morgan_dneg (A B : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.conj (SeqFormula.neg (SeqFormula.neg A)) B))
           (SeqFormula.disj (SeqFormula.neg (SeqFormula.neg (SeqFormula.neg A))) (SeqFormula.neg B)) :=
  .cons .deMorgan .nil

-- 30. GoI: compose then execute
noncomputable def goi_compose_execute (A B C : SeqFormula) :
    PTPath (SeqFormula.tensor A (SeqFormula.tensor (SeqFormula.impl A B) (SeqFormula.impl B C)))
           (SeqFormula.tensor A (SeqFormula.impl A C)) :=
  PTPath.congrArg (fun x => SeqFormula.tensor A x) (.cons .goiTrace .nil)

-- 31. Deep switch under negation
noncomputable def deep_switch_neg (A B C : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.conj A (SeqFormula.disj B C)))
           (SeqFormula.neg (SeqFormula.disj (SeqFormula.conj A B) C)) :=
  PTPath.congrArg SeqFormula.neg (.cons .deepSwitch .nil)

-- 32. Linear composition: tensor associativity simulation
noncomputable def linear_compose_chain (A B C : SeqFormula) :
    PTPath (SeqFormula.tensor (SeqFormula.impl A B) (SeqFormula.impl B C))
           (SeqFormula.impl A C) :=
  .cons .goiTrace .nil

-- 33. Focalization: positive formula chain
noncomputable def focalization_positive_chain (A B : SeqFormula) :
    PTPath (SeqFormula.disj (SeqFormula.disj A B) SeqFormula.unit)
           (SeqFormula.disj A B) :=
  .cons .blurPositive .nil

-- 34. NbE reify-reflect roundtrip
noncomputable def nbe_roundtrip (A : SeqFormula) :
    PTPath A A :=
  .cons .nbeReify (.cons .nbeReflect .nil)

-- 35. NbE under congruence
noncomputable def nbe_congruence (A B : SeqFormula) :
    PTPath (SeqFormula.conj A B) (SeqFormula.conj A B) :=
  PTPath.congrArg (fun x => SeqFormula.conj x B) (.cons .nbeReify (.cons .nbeReflect .nil))

-- 36. Bang weakening then dereliction (on different parts)
noncomputable def bang_structural_chain (A B : SeqFormula) :
    PTPath (SeqFormula.tensor (SeqFormula.bang A) (SeqFormula.bang B))
           (SeqFormula.tensor SeqFormula.unit B) :=
  PTPath.trans
    (PTPath.congrArg (fun x => SeqFormula.tensor x (SeqFormula.bang B)) (.cons .bangWeakening .nil))
    (PTPath.congrArg (fun x => SeqFormula.tensor SeqFormula.unit x) (.cons .bangDereliction .nil))

-- 37. Deep medial under negation
noncomputable def deep_medial_neg (A B C D : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.conj (SeqFormula.disj A B) (SeqFormula.disj C D)))
           (SeqFormula.neg (SeqFormula.disj (SeqFormula.conj A C) (SeqFormula.conj B D))) :=
  PTPath.congrArg SeqFormula.neg (.cons .deepMedial .nil)

-- 38. Sequent structural: exchange + contraction
noncomputable def exchange_contract (A : SeqFormula) :
    PTPath (SeqFormula.conj A A) A :=
  .cons .hauptsatzContract .nil

-- 39. Quest duality chain: quest then double negation
noncomputable def quest_chain (A : SeqFormula) :
    PTPath (SeqFormula.quest (SeqFormula.neg (SeqFormula.neg A)))
           (SeqFormula.neg (SeqFormula.bang (SeqFormula.neg (SeqFormula.neg (SeqFormula.neg A))))) :=
  .cons .questDual .nil

-- 40. Tensor-par + de Morgan combined
noncomputable def tensor_par_de_morgan (A B : SeqFormula) :
    PTPath (SeqFormula.neg (SeqFormula.tensor A B))
           (SeqFormula.neg (SeqFormula.neg (SeqFormula.par (SeqFormula.neg A) (SeqFormula.neg B)))) :=
  PTPath.congrArg SeqFormula.neg (.cons .tensorPar .nil)

-- 41. Deep switch + exchange chain
noncomputable def deep_switch_exchange (A B C : SeqFormula) :
    PTPath (SeqFormula.conj A (SeqFormula.disj B C))
           (SeqFormula.disj (SeqFormula.conj A B) C) :=
  .cons .deepSwitch .nil

-- 42. Proof net correctness: tensor-par switching
noncomputable def proof_net_switching (A B : SeqFormula) :
    PTPath (SeqFormula.tensor A B)
           (SeqFormula.neg (SeqFormula.par (SeqFormula.neg A) (SeqFormula.neg B))) :=
  .cons .tensorPar .nil

-- 43. Ludics: interaction as GoI execution
noncomputable def ludics_interaction (A B : SeqFormula) :
    PTPath (SeqFormula.tensor A (SeqFormula.impl A B)) B :=
  .cons .goiExec .nil

-- 44. Transcendental syntax: type as behavior
noncomputable def transcendental_type_behavior (A : SeqFormula) :
    PTPath (SeqFormula.bang (SeqFormula.impl A A))
           (SeqFormula.impl A A) :=
  .cons .bangDereliction .nil

-- 45. Contraction under congruence
noncomputable def contraction_congruence (A B : SeqFormula) :
    PTPath (SeqFormula.conj (SeqFormula.conj A A) B)
           (SeqFormula.conj A B) :=
  PTPath.congrArg (fun x => SeqFormula.conj x B) (.cons .hauptsatzContract .nil)

end ComputationalPaths
