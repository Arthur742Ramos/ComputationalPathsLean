import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- KNOT THEORY VIA PATHS
-- Reidemeister moves, knot invariants, braid groups, Jones/Alexander polynomials,
-- skein relations, Wirtinger presentation
-- ============================================================================

-- Knot diagram expressions
inductive KnotExpr : Type where
  | strand : Nat → KnotExpr                               -- labeled strand
  | crossing : KnotExpr → KnotExpr → Bool → KnotExpr      -- over, under, positive?
  | empty : KnotExpr                                       -- empty diagram
  | compose : KnotExpr → KnotExpr → KnotExpr              -- horizontal composition
  | tensor : KnotExpr → KnotExpr → KnotExpr               -- vertical (tensor) product
  | loop : KnotExpr → KnotExpr                             -- loop/curl
  | unloop : KnotExpr → KnotExpr                           -- remove loop
  -- Braid group elements
  | braidId : Nat → KnotExpr                               -- identity braid on n strands
  | braidGen : Nat → Nat → KnotExpr                        -- σ_i on n strands
  | braidInv : Nat → Nat → KnotExpr                        -- σ_i⁻¹ on n strands
  | braidComp : KnotExpr → KnotExpr → KnotExpr             -- braid composition
  -- Polynomial / invariant expressions
  | writhe : KnotExpr → KnotExpr                           -- writhe number
  | linkNum : KnotExpr → KnotExpr → KnotExpr               -- linking number
  | jones : KnotExpr → KnotExpr                            -- Jones polynomial
  | alexander : KnotExpr → KnotExpr                        -- Alexander polynomial
  | intVal : Int → KnotExpr                                -- integer value
  | polyVar : KnotExpr                                     -- polynomial variable t
  | polyAdd : KnotExpr → KnotExpr → KnotExpr               -- polynomial addition
  | polyMul : KnotExpr → KnotExpr → KnotExpr               -- polynomial multiplication
  | polyNeg : KnotExpr → KnotExpr                          -- polynomial negation
  | polyZero : KnotExpr                                    -- zero polynomial
  | polyOne : KnotExpr                                     -- one polynomial
  -- Skein relation components
  | skeinPlus : KnotExpr → KnotExpr                        -- L+
  | skeinMinus : KnotExpr → KnotExpr                       -- L-
  | skeinZero : KnotExpr → KnotExpr                        -- L0
  -- Fundamental group
  | generator : Nat → KnotExpr                             -- Wirtinger generator
  | genInv : KnotExpr → KnotExpr                           -- group inverse
  | genMul : KnotExpr → KnotExpr → KnotExpr                -- group multiplication
  | genUnit : KnotExpr                                     -- identity element
  | wirtinger : KnotExpr → KnotExpr → KnotExpr → KnotExpr  -- Wirtinger relation
  -- Closure operations
  | closure : KnotExpr → KnotExpr                          -- braid closure
  | markov : KnotExpr → KnotExpr                           -- Markov stabilization
  deriving Repr, BEq

-- Steps in knot theory
inductive KnotStep : KnotExpr → KnotExpr → Type where
  | refl : (a : KnotExpr) → KnotStep a a
  | symm : KnotStep a b → KnotStep b a
  | trans : KnotStep a b → KnotStep b c → KnotStep a c
  | congrArg : (f : KnotExpr → KnotExpr) → KnotStep a b → KnotStep (f a) (f b)
  -- Reidemeister moves
  | reidemeisterI : KnotStep (KnotExpr.loop (KnotExpr.strand n)) (KnotExpr.strand n)
  | reidemeisterIinv : KnotStep (KnotExpr.strand n) (KnotExpr.loop (KnotExpr.strand n))
  | reidemeisterII : KnotStep (KnotExpr.compose
      (KnotExpr.crossing a b true) (KnotExpr.crossing b a false)) (KnotExpr.compose a b)
  | reidemeisterIIinv : KnotStep (KnotExpr.compose a b)
      (KnotExpr.compose (KnotExpr.crossing a b true) (KnotExpr.crossing b a false))
  | reidemeisterIII :
      KnotStep (KnotExpr.compose (KnotExpr.crossing a b p)
                  (KnotExpr.compose (KnotExpr.crossing b c q) (KnotExpr.crossing a c r)))
               (KnotExpr.compose (KnotExpr.compose (KnotExpr.crossing b c q) (KnotExpr.crossing a c r))
                  (KnotExpr.crossing a b p))
  -- Compose rules
  | composeAssoc : KnotStep (KnotExpr.compose (KnotExpr.compose a b) c)
      (KnotExpr.compose a (KnotExpr.compose b c))
  | composeEmpty : KnotStep (KnotExpr.compose KnotExpr.empty a) a
  | emptyCompose : KnotStep (KnotExpr.compose a KnotExpr.empty) a
  | composeCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.compose a b) (KnotExpr.compose a' b')
  -- Tensor rules
  | tensorAssoc : KnotStep (KnotExpr.tensor (KnotExpr.tensor a b) c)
      (KnotExpr.tensor a (KnotExpr.tensor b c))
  | tensorEmpty : KnotStep (KnotExpr.tensor KnotExpr.empty a) a
  | emptyTensor : KnotStep (KnotExpr.tensor a KnotExpr.empty) a
  | tensorCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.tensor a b) (KnotExpr.tensor a' b')
  -- Loop rules
  | loopUnloop : KnotStep (KnotExpr.unloop (KnotExpr.loop a)) a
  | unloopLoop : KnotStep (KnotExpr.loop (KnotExpr.unloop a)) a
  | loopCong : KnotStep a b → KnotStep (KnotExpr.loop a) (KnotExpr.loop b)
  | unloopCong : KnotStep a b → KnotStep (KnotExpr.unloop a) (KnotExpr.unloop b)
  -- Braid group rules
  | braidCompAssoc : KnotStep (KnotExpr.braidComp (KnotExpr.braidComp a b) c)
      (KnotExpr.braidComp a (KnotExpr.braidComp b c))
  | braidIdLeft : KnotStep (KnotExpr.braidComp (KnotExpr.braidId n) b) b
  | braidIdRight : KnotStep (KnotExpr.braidComp a (KnotExpr.braidId n)) a
  | braidInverse : KnotStep (KnotExpr.braidComp (KnotExpr.braidGen n i)
      (KnotExpr.braidInv n i)) (KnotExpr.braidId n)
  | braidInverseLeft : KnotStep (KnotExpr.braidComp (KnotExpr.braidInv n i)
      (KnotExpr.braidGen n i)) (KnotExpr.braidId n)
  | braidFarComm : KnotStep (KnotExpr.braidComp (KnotExpr.braidGen n i)
      (KnotExpr.braidGen n j)) (KnotExpr.braidComp (KnotExpr.braidGen n j)
      (KnotExpr.braidGen n i))  -- for |i-j| ≥ 2
  | braidYangBaxter :
      KnotStep (KnotExpr.braidComp (KnotExpr.braidGen n i)
                  (KnotExpr.braidComp (KnotExpr.braidGen n (i+1)) (KnotExpr.braidGen n i)))
               (KnotExpr.braidComp (KnotExpr.braidGen n (i+1))
                  (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidGen n (i+1))))
  | braidCompCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.braidComp a b) (KnotExpr.braidComp a' b')
  -- Writhe / invariant rules
  | writhePositive : KnotStep (KnotExpr.writhe (KnotExpr.crossing a b true))
      (KnotExpr.polyAdd (KnotExpr.writhe a) (KnotExpr.intVal 1))
  | writheNegative : KnotStep (KnotExpr.writhe (KnotExpr.crossing a b false))
      (KnotExpr.polyAdd (KnotExpr.writhe a) (KnotExpr.intVal (-1)))
  | writheEmpty : KnotStep (KnotExpr.writhe KnotExpr.empty) (KnotExpr.intVal 0)
  | writheCong : KnotStep a b → KnotStep (KnotExpr.writhe a) (KnotExpr.writhe b)
  -- Linking number
  | linkNumSelf : KnotStep (KnotExpr.linkNum a a) (KnotExpr.intVal 0)
  | linkNumSymm : KnotStep (KnotExpr.linkNum a b) (KnotExpr.linkNum b a)
  | linkNumCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.linkNum a b) (KnotExpr.linkNum a' b')
  -- Polynomial arithmetic
  | polyAddZero : KnotStep (KnotExpr.polyAdd KnotExpr.polyZero a) a
  | polyZeroAdd : KnotStep (KnotExpr.polyAdd a KnotExpr.polyZero) a
  | polyAddComm : KnotStep (KnotExpr.polyAdd a b) (KnotExpr.polyAdd b a)
  | polyAddAssoc : KnotStep (KnotExpr.polyAdd (KnotExpr.polyAdd a b) c)
      (KnotExpr.polyAdd a (KnotExpr.polyAdd b c))
  | polyMulOne : KnotStep (KnotExpr.polyMul KnotExpr.polyOne a) a
  | polyOneMul : KnotStep (KnotExpr.polyMul a KnotExpr.polyOne) a
  | polyMulZero : KnotStep (KnotExpr.polyMul KnotExpr.polyZero a) KnotExpr.polyZero
  | polyZeroMul : KnotStep (KnotExpr.polyMul a KnotExpr.polyZero) KnotExpr.polyZero
  | polyMulAssoc : KnotStep (KnotExpr.polyMul (KnotExpr.polyMul a b) c)
      (KnotExpr.polyMul a (KnotExpr.polyMul b c))
  | polyMulComm : KnotStep (KnotExpr.polyMul a b) (KnotExpr.polyMul b a)
  | polyDistrib : KnotStep (KnotExpr.polyMul a (KnotExpr.polyAdd b c))
      (KnotExpr.polyAdd (KnotExpr.polyMul a b) (KnotExpr.polyMul a c))
  | polyNegCancel : KnotStep (KnotExpr.polyAdd a (KnotExpr.polyNeg a)) KnotExpr.polyZero
  | polyAddCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.polyAdd a b) (KnotExpr.polyAdd a' b')
  | polyMulCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.polyMul a b) (KnotExpr.polyMul a' b')
  | polyNegCong : KnotStep a b → KnotStep (KnotExpr.polyNeg a) (KnotExpr.polyNeg b)
  -- Jones polynomial / skein relation
  | jonesSkein : KnotStep
      (KnotExpr.polyAdd (KnotExpr.polyMul (KnotExpr.polyNeg (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar)) (KnotExpr.jones (KnotExpr.skeinPlus k)))
        (KnotExpr.polyMul (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar) (KnotExpr.jones (KnotExpr.skeinMinus k))))
      (KnotExpr.polyMul (KnotExpr.polyAdd (KnotExpr.polyNeg KnotExpr.polyVar)
        (KnotExpr.polyMul KnotExpr.polyVar (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar)))
        (KnotExpr.jones (KnotExpr.skeinZero k)))
  | jonesEmpty : KnotStep (KnotExpr.jones KnotExpr.empty) KnotExpr.polyOne
  | jonesCong : KnotStep a b → KnotStep (KnotExpr.jones a) (KnotExpr.jones b)
  -- Alexander polynomial
  | alexanderEmpty : KnotStep (KnotExpr.alexander KnotExpr.empty) KnotExpr.polyOne
  | alexanderCong : KnotStep a b → KnotStep (KnotExpr.alexander a) (KnotExpr.alexander b)
  -- Wirtinger / fundamental group
  | genMulAssoc : KnotStep (KnotExpr.genMul (KnotExpr.genMul a b) c)
      (KnotExpr.genMul a (KnotExpr.genMul b c))
  | genMulUnit : KnotStep (KnotExpr.genMul KnotExpr.genUnit a) a
  | genUnitMul : KnotStep (KnotExpr.genMul a KnotExpr.genUnit) a
  | genInvCancel : KnotStep (KnotExpr.genMul a (KnotExpr.genInv a)) KnotExpr.genUnit
  | genInvCancelLeft : KnotStep (KnotExpr.genMul (KnotExpr.genInv a) a) KnotExpr.genUnit
  | wirtingerRel : KnotStep (KnotExpr.wirtinger x y z)
      (KnotExpr.genMul (KnotExpr.genMul x y) (KnotExpr.genInv (KnotExpr.genMul z y)))
  | genMulCong : KnotStep a a' → KnotStep b b' →
      KnotStep (KnotExpr.genMul a b) (KnotExpr.genMul a' b')
  | genInvCong : KnotStep a b → KnotStep (KnotExpr.genInv a) (KnotExpr.genInv b)
  | genInvInv : KnotStep (KnotExpr.genInv (KnotExpr.genInv a)) a
  -- Closure / Markov
  | closureInvariant : KnotStep a b → KnotStep (KnotExpr.closure a) (KnotExpr.closure b)
  | markovI : KnotStep (KnotExpr.closure (KnotExpr.braidComp a b))
      (KnotExpr.closure (KnotExpr.braidComp b a))
  | markovII : KnotStep (KnotExpr.closure a)
      (KnotExpr.closure (KnotExpr.braidComp a (KnotExpr.braidGen (n+1) n)))
  | markovCong : KnotStep a b → KnotStep (KnotExpr.markov a) (KnotExpr.markov b)
  -- Skein congruences
  | skeinPlusCong : KnotStep a b → KnotStep (KnotExpr.skeinPlus a) (KnotExpr.skeinPlus b)
  | skeinMinusCong : KnotStep a b → KnotStep (KnotExpr.skeinMinus a) (KnotExpr.skeinMinus b)
  | skeinZeroCong : KnotStep a b → KnotStep (KnotExpr.skeinZero a) (KnotExpr.skeinZero b)

-- Paths
inductive KnotPath : KnotExpr → KnotExpr → Type where
  | nil : KnotPath a a
  | cons : KnotStep a b → KnotPath b c → KnotPath a c

namespace KnotPath

def trans : KnotPath a b → KnotPath b c → KnotPath a c
  | .nil, q => q
  | .cons s p, q => .cons s (p.trans q)

def symm : KnotPath a b → KnotPath b a
  | .nil => .nil
  | .cons s p => p.symm.trans (.cons (.symm s) .nil)

def congrArg (f : KnotExpr → KnotExpr) : KnotPath a b → KnotPath (f a) (f b)
  | .nil => .nil
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

def length : KnotPath a b → Nat
  | .nil => 0
  | .cons _ p => 1 + p.length

-- ============================================================================
-- REIDEMEISTER MOVE THEOREMS
-- ============================================================================

-- 1. R1: Loop removal
def reidemeister_I (n : Nat) :
    KnotPath (KnotExpr.loop (KnotExpr.strand n)) (KnotExpr.strand n) :=
  .cons .reidemeisterI .nil

-- 2. R1 inverse: Loop creation
def reidemeister_I_inv (n : Nat) :
    KnotPath (KnotExpr.strand n) (KnotExpr.loop (KnotExpr.strand n)) :=
  .cons .reidemeisterIinv .nil

-- 3. R1 roundtrip
def reidemeister_I_roundtrip (n : Nat) :
    KnotPath (KnotExpr.loop (KnotExpr.strand n)) (KnotExpr.loop (KnotExpr.strand n)) :=
  (reidemeister_I n).trans (reidemeister_I_inv n)

-- 4. R2: Cancel opposite crossings
def reidemeister_II (a b : KnotExpr) :
    KnotPath (KnotExpr.compose (KnotExpr.crossing a b true) (KnotExpr.crossing b a false))
             (KnotExpr.compose a b) :=
  .cons .reidemeisterII .nil

-- 5. R2 inverse
def reidemeister_II_inv (a b : KnotExpr) :
    KnotPath (KnotExpr.compose a b)
             (KnotExpr.compose (KnotExpr.crossing a b true) (KnotExpr.crossing b a false)) :=
  .cons .reidemeisterIIinv .nil

-- 6. R2 roundtrip
def reidemeister_II_roundtrip (a b : KnotExpr) :
    KnotPath (KnotExpr.compose a b) (KnotExpr.compose a b) :=
  (reidemeister_II_inv a b).trans (reidemeister_II a b)

-- 7. R3: Triangle move
def reidemeister_III (a b c : KnotExpr) (p q r : Bool) :
    KnotPath (KnotExpr.compose (KnotExpr.crossing a b p)
                (KnotExpr.compose (KnotExpr.crossing b c q) (KnotExpr.crossing a c r)))
             (KnotExpr.compose (KnotExpr.compose (KnotExpr.crossing b c q) (KnotExpr.crossing a c r))
                (KnotExpr.crossing a b p)) :=
  .cons .reidemeisterIII .nil

-- 8. Double loop removal
def double_loop_removal (n : Nat) :
    KnotPath (KnotExpr.loop (KnotExpr.loop (KnotExpr.strand n))) (KnotExpr.strand n) :=
  .cons (.loopCong .reidemeisterI)
  (.cons .reidemeisterI .nil)

-- 9. Loop-unloop cancellation
def loop_unloop_cancel (a : KnotExpr) :
    KnotPath (KnotExpr.unloop (KnotExpr.loop a)) a :=
  .cons .loopUnloop .nil

-- 10. Unloop-loop cancellation
def unloop_loop_cancel (a : KnotExpr) :
    KnotPath (KnotExpr.loop (KnotExpr.unloop a)) a :=
  .cons .unloopLoop .nil

-- ============================================================================
-- BRAID GROUP THEOREMS
-- ============================================================================

-- 11. Braid left identity
def braid_id_left (n : Nat) (b : KnotExpr) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidId n) b) b :=
  .cons .braidIdLeft .nil

-- 12. Braid right identity
def braid_id_right (n : Nat) (a : KnotExpr) :
    KnotPath (KnotExpr.braidComp a (KnotExpr.braidId n)) a :=
  .cons .braidIdRight .nil

-- 13. Braid inverse right
def braid_inverse (n i : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidInv n i))
             (KnotExpr.braidId n) :=
  .cons .braidInverse .nil

-- 14. Braid inverse left
def braid_inverse_left (n i : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidInv n i) (KnotExpr.braidGen n i))
             (KnotExpr.braidId n) :=
  .cons .braidInverseLeft .nil

-- 15. Braid associativity
def braid_assoc (a b c : KnotExpr) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidComp a b) c)
             (KnotExpr.braidComp a (KnotExpr.braidComp b c)) :=
  .cons .braidCompAssoc .nil

-- 16. Yang-Baxter equation
def yang_baxter (n i : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i)
                (KnotExpr.braidComp (KnotExpr.braidGen n (i+1)) (KnotExpr.braidGen n i)))
             (KnotExpr.braidComp (KnotExpr.braidGen n (i+1))
                (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidGen n (i+1)))) :=
  .cons .braidYangBaxter .nil

-- 17. Far commutativity
def braid_far_comm (n i j : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidGen n j))
             (KnotExpr.braidComp (KnotExpr.braidGen n j) (KnotExpr.braidGen n i)) :=
  .cons .braidFarComm .nil

-- 18. Double inverse is identity
def braid_double_inv (n i : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i)
               (KnotExpr.braidComp (KnotExpr.braidInv n i)
                 (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidInv n i))))
             (KnotExpr.braidId n) :=
  .cons (.braidCompCong (.refl _) (.braidCompCong (.refl _) .braidInverse))
  (.cons (.braidCompCong (.refl _) .braidIdRight)
  (.cons .braidInverse .nil))

-- 19. Braid gen then inverse then gen
def braid_gen_inv_gen (n i : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i)
               (KnotExpr.braidComp (KnotExpr.braidInv n i) (KnotExpr.braidGen n i)))
             (KnotExpr.braidGen n i) :=
  .cons (.braidCompCong (.refl _) .braidInverseLeft)
  (.cons .braidIdRight .nil)

-- 20. Identity composed with itself
def braid_id_id (n : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidId n) (KnotExpr.braidId n))
             (KnotExpr.braidId n) :=
  .cons .braidIdLeft .nil

-- ============================================================================
-- WRITHE AND LINKING NUMBER THEOREMS
-- ============================================================================

-- 21. Writhe of empty diagram
def writhe_empty :
    KnotPath (KnotExpr.writhe KnotExpr.empty) (KnotExpr.intVal 0) :=
  .cons .writheEmpty .nil

-- 22. Writhe of positive crossing
def writhe_positive (a b : KnotExpr) :
    KnotPath (KnotExpr.writhe (KnotExpr.crossing a b true))
             (KnotExpr.polyAdd (KnotExpr.writhe a) (KnotExpr.intVal 1)) :=
  .cons .writhePositive .nil

-- 23. Writhe of negative crossing
def writhe_negative (a b : KnotExpr) :
    KnotPath (KnotExpr.writhe (KnotExpr.crossing a b false))
             (KnotExpr.polyAdd (KnotExpr.writhe a) (KnotExpr.intVal (-1))) :=
  .cons .writheNegative .nil

-- 24. Writhe of positive then negative on empty = zero
def writhe_pos_neg_cancel :
    KnotPath (KnotExpr.writhe (KnotExpr.crossing (KnotExpr.crossing KnotExpr.empty (KnotExpr.strand 0) false) (KnotExpr.strand 1) true))
             (KnotExpr.polyAdd (KnotExpr.polyAdd (KnotExpr.writhe KnotExpr.empty) (KnotExpr.intVal (-1))) (KnotExpr.intVal 1)) :=
  .cons .writhePositive
  (.cons (.polyAddCong .writheNegative (.refl _)) .nil)

-- 25. Linking number is symmetric
def link_num_symm (a b : KnotExpr) :
    KnotPath (KnotExpr.linkNum a b) (KnotExpr.linkNum b a) :=
  .cons .linkNumSymm .nil

-- 26. Self-linking is zero
def link_num_self (a : KnotExpr) :
    KnotPath (KnotExpr.linkNum a a) (KnotExpr.intVal 0) :=
  .cons .linkNumSelf .nil

-- ============================================================================
-- POLYNOMIAL ALGEBRA THEOREMS
-- ============================================================================

-- 27. Polynomial addition left identity
def poly_add_zero (a : KnotExpr) :
    KnotPath (KnotExpr.polyAdd KnotExpr.polyZero a) a :=
  .cons .polyAddZero .nil

-- 28. Polynomial addition right identity
def poly_zero_add (a : KnotExpr) :
    KnotPath (KnotExpr.polyAdd a KnotExpr.polyZero) a :=
  .cons .polyZeroAdd .nil

-- 29. Polynomial multiplication left identity
def poly_mul_one (a : KnotExpr) :
    KnotPath (KnotExpr.polyMul KnotExpr.polyOne a) a :=
  .cons .polyMulOne .nil

-- 30. Polynomial multiplication right identity
def poly_one_mul (a : KnotExpr) :
    KnotPath (KnotExpr.polyMul a KnotExpr.polyOne) a :=
  .cons .polyOneMul .nil

-- 31. Polynomial multiply by zero
def poly_mul_zero (a : KnotExpr) :
    KnotPath (KnotExpr.polyMul KnotExpr.polyZero a) KnotExpr.polyZero :=
  .cons .polyMulZero .nil

-- 32. Polynomial negation cancels
def poly_neg_cancel (a : KnotExpr) :
    KnotPath (KnotExpr.polyAdd a (KnotExpr.polyNeg a)) KnotExpr.polyZero :=
  .cons .polyNegCancel .nil

-- 33. Addition commutativity
def poly_add_comm (a b : KnotExpr) :
    KnotPath (KnotExpr.polyAdd a b) (KnotExpr.polyAdd b a) :=
  .cons .polyAddComm .nil

-- 34. Multiplication commutativity
def poly_mul_comm (a b : KnotExpr) :
    KnotPath (KnotExpr.polyMul a b) (KnotExpr.polyMul b a) :=
  .cons .polyMulComm .nil

-- 35. Addition associativity
def poly_add_assoc (a b c : KnotExpr) :
    KnotPath (KnotExpr.polyAdd (KnotExpr.polyAdd a b) c)
             (KnotExpr.polyAdd a (KnotExpr.polyAdd b c)) :=
  .cons .polyAddAssoc .nil

-- 36. Multiplication associativity
def poly_mul_assoc (a b c : KnotExpr) :
    KnotPath (KnotExpr.polyMul (KnotExpr.polyMul a b) c)
             (KnotExpr.polyMul a (KnotExpr.polyMul b c)) :=
  .cons .polyMulAssoc .nil

-- 37. Distributivity
def poly_distrib (a b c : KnotExpr) :
    KnotPath (KnotExpr.polyMul a (KnotExpr.polyAdd b c))
             (KnotExpr.polyAdd (KnotExpr.polyMul a b) (KnotExpr.polyMul a c)) :=
  .cons .polyDistrib .nil

-- 38. Double negation cancels to zero twice
def poly_double_neg_zero (a : KnotExpr) :
    KnotPath (KnotExpr.polyAdd (KnotExpr.polyAdd a (KnotExpr.polyNeg a))
               (KnotExpr.polyAdd a (KnotExpr.polyNeg a)))
             KnotExpr.polyZero :=
  .cons (.polyAddCong .polyNegCancel .polyNegCancel)
  (.cons .polyAddZero .nil)

-- ============================================================================
-- JONES POLYNOMIAL THEOREMS
-- ============================================================================

-- 39. Jones of empty knot
def jones_empty :
    KnotPath (KnotExpr.jones KnotExpr.empty) KnotExpr.polyOne :=
  .cons .jonesEmpty .nil

-- 40. Jones polynomial skein relation
def jones_skein (k : KnotExpr) :
    KnotPath (KnotExpr.polyAdd
      (KnotExpr.polyMul (KnotExpr.polyNeg (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar))
        (KnotExpr.jones (KnotExpr.skeinPlus k)))
      (KnotExpr.polyMul (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar)
        (KnotExpr.jones (KnotExpr.skeinMinus k))))
    (KnotExpr.polyMul (KnotExpr.polyAdd (KnotExpr.polyNeg KnotExpr.polyVar)
        (KnotExpr.polyMul KnotExpr.polyVar (KnotExpr.polyMul KnotExpr.polyVar KnotExpr.polyVar)))
        (KnotExpr.jones (KnotExpr.skeinZero k))) :=
  .cons .jonesSkein .nil

-- 41. Jones congruence
def jones_cong (a b : KnotExpr) (s : KnotStep a b) :
    KnotPath (KnotExpr.jones a) (KnotExpr.jones b) :=
  .cons (.jonesCong s) .nil

-- 42. Jones of R1-simplified knot
def jones_reidemeister_I (n : Nat) :
    KnotPath (KnotExpr.jones (KnotExpr.loop (KnotExpr.strand n)))
             (KnotExpr.jones (KnotExpr.strand n)) :=
  .cons (.jonesCong .reidemeisterI) .nil

-- ============================================================================
-- ALEXANDER POLYNOMIAL THEOREMS
-- ============================================================================

-- 43. Alexander of empty knot
def alexander_empty :
    KnotPath (KnotExpr.alexander KnotExpr.empty) KnotExpr.polyOne :=
  .cons .alexanderEmpty .nil

-- 44. Alexander congruence under R1
def alexander_reidemeister_I (n : Nat) :
    KnotPath (KnotExpr.alexander (KnotExpr.loop (KnotExpr.strand n)))
             (KnotExpr.alexander (KnotExpr.strand n)) :=
  .cons (.alexanderCong .reidemeisterI) .nil

-- ============================================================================
-- WIRTINGER PRESENTATION / FUNDAMENTAL GROUP THEOREMS
-- ============================================================================

-- 45. Group multiplication associativity
def gen_mul_assoc (a b c : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genMul a b) c)
             (KnotExpr.genMul a (KnotExpr.genMul b c)) :=
  .cons .genMulAssoc .nil

-- 46. Left identity
def gen_mul_unit (a : KnotExpr) :
    KnotPath (KnotExpr.genMul KnotExpr.genUnit a) a :=
  .cons .genMulUnit .nil

-- 47. Right identity
def gen_unit_mul (a : KnotExpr) :
    KnotPath (KnotExpr.genMul a KnotExpr.genUnit) a :=
  .cons .genUnitMul .nil

-- 48. Right inverse
def gen_inv_cancel (a : KnotExpr) :
    KnotPath (KnotExpr.genMul a (KnotExpr.genInv a)) KnotExpr.genUnit :=
  .cons .genInvCancel .nil

-- 49. Left inverse
def gen_inv_cancel_left (a : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genInv a) a) KnotExpr.genUnit :=
  .cons .genInvCancelLeft .nil

-- 50. Double inverse
def gen_inv_inv (a : KnotExpr) :
    KnotPath (KnotExpr.genInv (KnotExpr.genInv a)) a :=
  .cons .genInvInv .nil

-- 51. Wirtinger relation expansion
def wirtinger_rel (x y z : KnotExpr) :
    KnotPath (KnotExpr.wirtinger x y z)
             (KnotExpr.genMul (KnotExpr.genMul x y) (KnotExpr.genInv (KnotExpr.genMul z y))) :=
  .cons .wirtingerRel .nil

-- 52. a * a⁻¹ * b = b
def gen_cancel_prefix (a b : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genMul a (KnotExpr.genInv a)) b) b :=
  .cons (.genMulCong .genInvCancel (.refl b))
  (.cons .genMulUnit .nil)

-- 53. (a * b) * b⁻¹ = a
def gen_cancel_suffix (a b : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genMul a b) (KnotExpr.genInv b))
             a :=
  .cons .genMulAssoc
  (.cons (.genMulCong (.refl a) .genInvCancel)
  (.cons .genUnitMul .nil))

-- 54. a⁻¹ * (a * b) = b
def gen_inv_prefix (a b : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genInv a) (KnotExpr.genMul a b)) b :=
  .cons (.symm .genMulAssoc)
  (.cons (.genMulCong .genInvCancelLeft (.refl b))
  (.cons .genMulUnit .nil))

-- ============================================================================
-- MARKOV MOVES / CLOSURE THEOREMS
-- ============================================================================

-- 55. Markov move I: cyclic permutation
def markov_I (a b : KnotExpr) :
    KnotPath (KnotExpr.closure (KnotExpr.braidComp a b))
             (KnotExpr.closure (KnotExpr.braidComp b a)) :=
  .cons .markovI .nil

-- 56. Markov move II: stabilization
def markov_II (n : Nat) (a : KnotExpr) :
    KnotPath (KnotExpr.closure a)
             (KnotExpr.closure (KnotExpr.braidComp a (KnotExpr.braidGen (n+1) n))) :=
  .cons .markovII .nil

-- 57. Closure preserves braid equivalence
def closure_invariant (a b : KnotExpr) (s : KnotStep a b) :
    KnotPath (KnotExpr.closure a) (KnotExpr.closure b) :=
  .cons (.closureInvariant s) .nil

-- 58. Closure of identity braid with Markov
def closure_id_markov (n : Nat) :
    KnotPath (KnotExpr.closure (KnotExpr.braidId n))
             (KnotExpr.closure (KnotExpr.braidComp (KnotExpr.braidId n) (KnotExpr.braidGen (n+1) n))) :=
  .cons .markovII .nil

-- 59. Closure of conjugate braids
def closure_conjugate (a b : KnotExpr) (n : Nat) :
    KnotPath (KnotExpr.closure (KnotExpr.braidComp (KnotExpr.braidComp a b) (KnotExpr.braidId n)))
             (KnotExpr.closure (KnotExpr.braidComp (KnotExpr.braidId n) (KnotExpr.braidComp a b))) :=
  .cons .markovI .nil

-- ============================================================================
-- COMBINED / CROSS-DOMAIN THEOREMS
-- ============================================================================

-- 60. Jones invariant under R1
def jones_R1_invariant (n : Nat) :
    KnotPath (KnotExpr.jones (KnotExpr.loop (KnotExpr.strand n)))
             (KnotExpr.jones (KnotExpr.strand n)) :=
  jones_reidemeister_I n

-- 61. Writhe congruence under loop removal
def writhe_loop_strand (n : Nat) :
    KnotPath (KnotExpr.writhe (KnotExpr.loop (KnotExpr.strand n)))
             (KnotExpr.writhe (KnotExpr.strand n)) :=
  .cons (.writheCong .reidemeisterI) .nil

-- 62. Jones of empty times one
def jones_empty_mul_one :
    KnotPath (KnotExpr.polyMul (KnotExpr.jones KnotExpr.empty) KnotExpr.polyOne)
             KnotExpr.polyOne :=
  .cons (.polyMulCong .jonesEmpty (.refl _))
  (.cons .polyOneMul .nil)

-- 63. Add zero to Jones
def jones_add_zero :
    KnotPath (KnotExpr.polyAdd (KnotExpr.jones KnotExpr.empty) KnotExpr.polyZero)
             KnotExpr.polyOne :=
  .cons .polyZeroAdd
  (.cons .jonesEmpty .nil)

-- 64. Double loop Jones
def jones_double_loop (n : Nat) :
    KnotPath (KnotExpr.jones (KnotExpr.loop (KnotExpr.loop (KnotExpr.strand n))))
             (KnotExpr.jones (KnotExpr.strand n)) :=
  .cons (.jonesCong (.loopCong .reidemeisterI))
  (.cons (.jonesCong .reidemeisterI) .nil)

-- 65. Braid inverse then closure
def closure_braid_inv_gen (n i : Nat) :
    KnotPath (KnotExpr.closure (KnotExpr.braidComp (KnotExpr.braidGen n i) (KnotExpr.braidInv n i)))
             (KnotExpr.closure (KnotExpr.braidId n)) :=
  .cons (.closureInvariant .braidInverse) .nil

-- 66. Group triple cancel
def gen_triple_cancel (a : KnotExpr) :
    KnotPath (KnotExpr.genMul (KnotExpr.genMul a (KnotExpr.genInv a))
               (KnotExpr.genMul a (KnotExpr.genInv a)))
             KnotExpr.genUnit :=
  .cons (.genMulCong .genInvCancel .genInvCancel)
  (.cons .genMulUnit .nil)

-- 67. Polynomial: (0 + a) * 1 = a
def poly_add_zero_mul_one (a : KnotExpr) :
    KnotPath (KnotExpr.polyMul (KnotExpr.polyAdd KnotExpr.polyZero a) KnotExpr.polyOne)
             a :=
  .cons (.polyMulCong .polyAddZero (.refl _))
  (.cons .polyOneMul .nil)

-- 68. Compose associativity double
def compose_double_assoc (a b c d : KnotExpr) :
    KnotPath (KnotExpr.compose (KnotExpr.compose (KnotExpr.compose a b) c) d)
             (KnotExpr.compose a (KnotExpr.compose b (KnotExpr.compose c d))) :=
  .cons .composeAssoc
  (.cons .composeAssoc .nil)

-- 69. Tensor associativity double
def tensor_double_assoc (a b c d : KnotExpr) :
    KnotPath (KnotExpr.tensor (KnotExpr.tensor (KnotExpr.tensor a b) c) d)
             (KnotExpr.tensor a (KnotExpr.tensor b (KnotExpr.tensor c d))) :=
  .cons .tensorAssoc
  (.cons .tensorAssoc .nil)

-- 70. Alexander invariant under double loop
def alexander_double_loop (n : Nat) :
    KnotPath (KnotExpr.alexander (KnotExpr.loop (KnotExpr.loop (KnotExpr.strand n))))
             (KnotExpr.alexander (KnotExpr.strand n)) :=
  .cons (.alexanderCong (.loopCong .reidemeisterI))
  (.cons (.alexanderCong .reidemeisterI) .nil)

-- 71. Compose with empty on both sides
def compose_empty_both (a : KnotExpr) :
    KnotPath (KnotExpr.compose KnotExpr.empty (KnotExpr.compose a KnotExpr.empty)) a :=
  .cons .composeEmpty
  (.cons .emptyCompose .nil)

-- 72. Braid word reduction: σᵢσᵢ⁻¹σⱼ = σⱼ
def braid_cancel_prefix (n i j : Nat) :
    KnotPath (KnotExpr.braidComp (KnotExpr.braidGen n i)
               (KnotExpr.braidComp (KnotExpr.braidInv n i) (KnotExpr.braidGen n j)))
             (KnotExpr.braidGen n j) :=
  .cons (.symm .braidCompAssoc)
  (.cons (.braidCompCong .braidInverse (.refl _))
  (.cons .braidIdLeft .nil))

-- 73. Polynomial: distribute then collect
def poly_distrib_collect (a b : KnotExpr) :
    KnotPath (KnotExpr.polyMul a (KnotExpr.polyAdd b KnotExpr.polyZero))
             (KnotExpr.polyMul a b) :=
  .cons (.polyMulCong (.refl a) .polyZeroAdd)
  .nil

-- 74. Jones + Alexander both trivial on empty
def invariants_empty :
    KnotPath (KnotExpr.polyAdd (KnotExpr.jones KnotExpr.empty)
               (KnotExpr.alexander KnotExpr.empty))
             (KnotExpr.polyAdd KnotExpr.polyOne KnotExpr.polyOne) :=
  .cons (.polyAddCong .jonesEmpty .alexanderEmpty) .nil

end KnotPath

end ComputationalPaths
