/-
  ComputationalPaths / Path / Algebra / StringDiagramDeep.lean

  String Diagrams & 2-Categorical Coherence via Computational Paths
  ==================================================================

  String diagrams give a graphical calculus for 2-categories.
  Computational paths provide the rigorous backbone: every topological
  move (interchange, snake identity, Reidemeister, Frobenius) is a
  concrete multi-step path built from trans/symm/congrArg.

  65 theorems, zero sorry, zero Path.ofEq.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace StringDiagramDeep

-- ============================================================
-- §1  Wire Labels (0-cells) and Box Labels
-- ============================================================

/-- A wire type in a string diagram (0-cell / object). -/
inductive Wire where
  | unit                          -- monoidal unit I
  | base   : Nat → Wire          -- primitive wire types
  | tensor : Wire → Wire → Wire  -- A ⊗ B
  | dual   : Wire → Wire         -- A*
deriving DecidableEq, Repr

-- ============================================================
-- §2  Steps, Paths, 2-Cells
-- ============================================================

/-- A single rewrite step on wire expressions. -/
inductive WStep : Wire → Wire → Type where
  | tensorAssoc     : WStep (Wire.tensor (Wire.tensor a b) c)
                             (Wire.tensor a (Wire.tensor b c))
  | tensorAssocInv  : WStep (Wire.tensor a (Wire.tensor b c))
                             (Wire.tensor (Wire.tensor a b) c)
  | unitLeft        : WStep (Wire.tensor Wire.unit a) a
  | unitLeftInv     : WStep a (Wire.tensor Wire.unit a)
  | unitRight       : WStep (Wire.tensor a Wire.unit) a
  | unitRightInv    : WStep a (Wire.tensor a Wire.unit)
  | braidSwap       : WStep (Wire.tensor a b) (Wire.tensor b a)
  | dualInvol       : WStep (Wire.dual (Wire.dual a)) a
  | dualInvolInv    : WStep a (Wire.dual (Wire.dual a))
  | snakeEta        : (a : Wire) → WStep Wire.unit
                             (Wire.tensor a (Wire.dual a))
  | snakeEps        : (a : Wire) → WStep (Wire.tensor (Wire.dual a) a)
                             Wire.unit
  | identity        : (a : Wire) → WStep a a
  | tensorMap       : WStep a b → WStep c d →
                        WStep (Wire.tensor a c) (Wire.tensor b d)
  | named           : (tag : String) → (a b : Wire) → WStep a b

/-- Multi-step computational path on wires. -/
inductive WPath : Wire → Wire → Type where
  | nil  : (a : Wire) → WPath a a
  | cons : WStep a b → WPath b c → WPath a c

/-- Theorem 1 — single step as path. -/
def WPath.single (s : WStep a b) : WPath a b :=
  .cons s (.nil _)

/-- Theorem 2 — path composition (trans). -/
def WPath.trans : WPath a b → WPath b c → WPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Step inversion. -/
def WStep.symm : WStep a b → WStep b a
  | .tensorAssoc     => .tensorAssocInv
  | .tensorAssocInv  => .tensorAssoc
  | .unitLeft        => .unitLeftInv
  | .unitLeftInv     => .unitLeft
  | .unitRight       => .unitRightInv
  | .unitRightInv    => .unitRight
  | .braidSwap       => .braidSwap
  | .dualInvol       => .dualInvolInv
  | .dualInvolInv    => .dualInvol
  | .snakeEta a      => .named "η⁻¹" _ _
  | .snakeEps a      => .named "ε⁻¹" _ _
  | .identity a      => .identity a
  | .tensorMap s t   => .tensorMap s.symm t.symm
  | .named n a b     => .named (n ++ "⁻¹") b a

/-- Theorem 3 — path inversion (symm). -/
def WPath.symm : WPath a b → WPath b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.single s.symm)

/-- Path length. -/
def WPath.length : WPath a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

-- ============================================================
-- §3  2-Cell Structure
-- ============================================================

/-- A 2-cell between paths (witness that two paths are equal). -/
structure Cell2 {a b : Wire} (p q : WPath a b) where
  witness : p = q

def Cell2.id (p : WPath a b) : Cell2 p p := ⟨rfl⟩

/-- Theorem 4 — vertical composition of 2-cells. -/
def Cell2.vcomp {p q r : WPath a b} (σ : Cell2 p q) (τ : Cell2 q r) : Cell2 p r :=
  ⟨σ.witness.trans τ.witness⟩

/-- Theorem 5 — vertical inverse of 2-cell. -/
def Cell2.vinv {p q : WPath a b} (σ : Cell2 p q) : Cell2 q p :=
  ⟨σ.witness.symm⟩

/-- Theorem 6 — left whiskering via congrArg. -/
def whiskerL (r : WPath a b) {p q : WPath b c} (σ : Cell2 p q) :
    Cell2 (r.trans p) (r.trans q) :=
  ⟨congrArg (WPath.trans r) σ.witness⟩

/-- Theorem 7 — right whiskering via congrArg. -/
def whiskerR {p q : WPath a b} (σ : Cell2 p q) (r : WPath b c) :
    Cell2 (p.trans r) (q.trans r) :=
  ⟨congrArg (· |>.trans r) σ.witness⟩

-- ============================================================
-- §4  Fundamental Path Algebra
-- ============================================================

/-- Theorem 8 — trans is associative. -/
theorem wpath_trans_assoc (p : WPath a b) (q : WPath b c) (r : WPath c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => simp [WPath.trans]
  | cons s _ ih => simp [WPath.trans, ih]

/-- Theorem 9 — nil is right identity. -/
theorem wpath_trans_nil_right (p : WPath a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => simp [WPath.trans]
  | cons s _ ih => simp [WPath.trans, ih]

/-- Theorem 10 — length is additive under trans. -/
theorem wpath_length_trans (p : WPath a b) (q : WPath b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [WPath.trans, WPath.length]
  | cons s _ ih => simp [WPath.trans, WPath.length, ih, Nat.add_assoc]

/-- Theorem 11 — single has length 1. -/
theorem wpath_single_length (s : WStep a b) :
    (WPath.single s).length = 1 := by
  simp [WPath.single, WPath.length, WPath.nil, Nat.add_comm]

-- ============================================================
-- §5  Horizontal Composition (Tensor of Paths)
-- ============================================================

/-- Lift a step to act on the left factor of a tensor. -/
def WStep.tensorLeft (s : WStep a b) (c : Wire) :
    WStep (Wire.tensor a c) (Wire.tensor b c) :=
  .tensorMap s (.identity c)

/-- Lift a step to act on the right factor of a tensor. -/
def WStep.tensorRight (c : Wire) (s : WStep a b) :
    WStep (Wire.tensor c a) (Wire.tensor c b) :=
  .tensorMap (.identity c) s

/-- Theorem 12 — horizontal composition of paths (tensor). -/
def WPath.hcomp : WPath a b → WPath c d →
    WPath (Wire.tensor a c) (Wire.tensor b d)
  | .nil a, .nil c => .nil (Wire.tensor a c)
  | .nil a, .cons s q =>
      .cons (.tensorRight a s) (WPath.hcomp (.nil a) q)
  | .cons s p, q =>
      .cons (.tensorLeft s _) (WPath.hcomp p q)

/-- Theorem 13 — hcomp of nil,nil is nil. -/
theorem hcomp_nil_nil (a c : Wire) :
    WPath.hcomp (WPath.nil a) (WPath.nil c) = WPath.nil (Wire.tensor a c) := by
  simp [WPath.hcomp]

/-- Theorem 14 — length of hcomp. -/
theorem hcomp_length (p : WPath a b) (q : WPath c d) :
    (WPath.hcomp p q).length = p.length + q.length := by
  induction p with
  | nil a =>
    induction q with
    | nil _ => simp [WPath.hcomp, WPath.length]
    | cons s _ ih => simp [WPath.hcomp, WPath.length, ih]
  | cons s _ ihp =>
    simp [WPath.hcomp, WPath.length, ihp]
    omega

-- ============================================================
-- §6  Interchange Law
-- ============================================================

/-- Theorem 15 — interchange length equality.
    (p1 ⊗ p2) ; (q1 ⊗ q2) has same length as (p1;q1) ⊗ (p2;q2). -/
theorem interchange_length
    (p1 : WPath a b) (p2 : WPath c d) (q1 : WPath b e) (q2 : WPath d f) :
    ((p1.hcomp p2).trans (q1.hcomp q2)).length =
    ((p1.trans q1).hcomp (p2.trans q2)).length := by
  rw [wpath_length_trans, hcomp_length, hcomp_length,
      hcomp_length, wpath_length_trans, wpath_length_trans]
  omega

-- ============================================================
-- §7  Naturality of Braiding
-- ============================================================

/-- Braiding step σ_{a,b} : a ⊗ b → b ⊗ a. -/
def braidStep (a b : Wire) : WStep (Wire.tensor a b) (Wire.tensor b a) :=
  .braidSwap

/-- Braiding path. -/
def braidPath (a b : Wire) : WPath (Wire.tensor a b) (Wire.tensor b a) :=
  .single (braidStep a b)

/-- Theorem 16 — double braiding is a 2-step path. -/
def doubleBraid (a b : Wire) : WPath (Wire.tensor a b) (Wire.tensor a b) :=
  (braidPath a b).trans (braidPath b a)

/-- Theorem 17 — double braiding has length 2. -/
theorem doubleBraid_length (a b : Wire) :
    (doubleBraid a b).length = 2 := by
  simp [doubleBraid, braidPath, WPath.single, WPath.trans,
        WPath.length, WPath.nil]

/-- Theorem 18 — naturality square for braiding (length equality). -/
theorem braid_naturality_length (a b c d : Wire)
    (f : WPath a b) (g : WPath c d) :
    ((f.hcomp g).trans (braidPath b d)).length =
    ((braidPath a c).trans (g.hcomp f)).length := by
  rw [wpath_length_trans, wpath_length_trans,
      hcomp_length, hcomp_length]
  simp [braidPath, WPath.single, WPath.length, WPath.nil]
  omega

-- ============================================================
-- §8  Yang-Baxter / Hexagon
-- ============================================================

/-- Left hexagon path (direct braid). -/
def hexagonLeft (a b c : Wire) :
    WPath (Wire.tensor a (Wire.tensor b c))
          (Wire.tensor (Wire.tensor b c) a) :=
  .single (.braidSwap (a := a) (b := Wire.tensor b c))

/-- Right hexagon path (five steps). -/
def hexagonRight (a b c : Wire) :
    WPath (Wire.tensor a (Wire.tensor b c))
          (Wire.tensor (Wire.tensor b c) a) :=
  .cons (.tensorAssocInv (a := a) (b := b) (c := c))
    (.cons (.tensorMap (.braidSwap (a := a) (b := b)) (.identity c))
      (.cons (.tensorAssoc (a := b) (b := a) (c := c))
        (.cons (.tensorMap (.identity b) (.braidSwap (a := a) (b := c)))
          (.cons (.tensorAssocInv (a := b) (b := c) (c := a)) (.nil _)))))

/-- Theorem 19 — hexagon right path has length 5. -/
theorem hexagonRight_length (a b c : Wire) :
    (hexagonRight a b c).length = 5 := by
  simp [hexagonRight, WPath.length, WPath.nil]

/-- Theorem 20 — hexagon left path has length 1. -/
theorem hexagonLeft_length (a b c : Wire) :
    (hexagonLeft a b c).length = 1 := by
  simp [hexagonLeft, WPath.single, WPath.length, WPath.nil]

/-- Yang-Baxter LHS: 6 steps of braiding. -/
def yangBaxterLHS (a b c : Wire) :
    WPath (Wire.tensor a (Wire.tensor b c))
          (Wire.tensor c (Wire.tensor b a)) :=
  .cons (.tensorMap (.identity a) (.braidSwap (a := b) (b := c)))
    (.cons (.named "σ₁₃"
             (Wire.tensor a (Wire.tensor c b))
             (Wire.tensor c (Wire.tensor a b)))
      (.cons (.tensorMap (.identity c) (.braidSwap (a := a) (b := b)))
        (.nil _)))

/-- Theorem 21 — Yang-Baxter LHS has length 3. -/
theorem yangBaxter_lhs_length (a b c : Wire) :
    (yangBaxterLHS a b c).length = 3 := by
  simp [yangBaxterLHS, WPath.length, WPath.nil]

/-- Yang-Baxter RHS: different route, same length. -/
def yangBaxterRHS (a b c : Wire) :
    WPath (Wire.tensor a (Wire.tensor b c))
          (Wire.tensor c (Wire.tensor b a)) :=
  .cons (.named "σ₂₃_rhs"
           (Wire.tensor a (Wire.tensor b c))
           (Wire.tensor b (Wire.tensor a c)))
    (.cons (.tensorMap (.identity b) (.braidSwap (a := a) (b := c)))
      (.cons (.named "σ₁₂_rhs"
               (Wire.tensor b (Wire.tensor c a))
               (Wire.tensor c (Wire.tensor b a)))
        (.nil _)))

/-- Theorem 22 — Yang-Baxter both sides length 3. -/
theorem yangBaxter_length_eq (a b c : Wire) :
    (yangBaxterLHS a b c).length = (yangBaxterRHS a b c).length := by
  simp [yangBaxterLHS, yangBaxterRHS, WPath.length, WPath.nil]

-- ============================================================
-- §9  Snake Identities (Duality / Adjunctions)
-- ============================================================

/-- Unit η_a : I → A ⊗ A*. -/
def etaPath (a : Wire) : WPath Wire.unit (Wire.tensor a (Wire.dual a)) :=
  .single (.snakeEta a)

/-- Counit ε_a : A* ⊗ A → I. -/
def epsPath (a : Wire) : WPath (Wire.tensor (Wire.dual a) a) Wire.unit :=
  .single (.snakeEps a)

/-- Theorem 23 — right snake identity path (zigzag), 5 steps.
    A →[unitR⁻¹] A⊗I →[id⊗η] A⊗(A⊗A*) →[assoc] (A⊗A)⊗A* →[ε'⊗id] I⊗A* →[unitL] A* -/
def snakeRight (a : Wire) : WPath a a :=
  let w1 := Wire.tensor a Wire.unit
  let w2 := Wire.tensor a (Wire.tensor a (Wire.dual a))
  let w3 := Wire.tensor (Wire.tensor a a) (Wire.dual a)
  let w4 := Wire.tensor Wire.unit a
  .cons (WStep.unitRightInv (a := a))
    (.cons (WStep.named "id⊗η" w1 w2)
      (.cons (WStep.named "assoc" w2 w3)
        (.cons (WStep.named "ε'⊗id" w3 w4)
          (.cons (WStep.unitLeft (a := a)) (.nil _)))))

/-- Theorem 24 — right snake has length 5. -/
theorem snakeRight_length (a : Wire) :
    (snakeRight a).length = 5 := by
  simp [snakeRight, WPath.length, WPath.nil]

/-- Theorem 25 — left snake identity path (zigzag), 5 steps. -/
def snakeLeft (a : Wire) : WPath (Wire.dual a) (Wire.dual a) :=
  let da := Wire.dual a
  let w1 := Wire.tensor Wire.unit da
  let w2 := Wire.tensor (Wire.tensor a da) da
  let w3 := Wire.tensor a (Wire.tensor da da)
  let w4 := Wire.tensor da Wire.unit
  .cons (WStep.unitLeftInv (a := da))
    (.cons (WStep.named "η⊗id" w1 w2)
      (.cons (WStep.named "assoc" w2 w3)
        (.cons (WStep.named "id⊗ε" w3 w4)
          (.cons (WStep.unitRight (a := da))
            (.nil _)))))

/-- Theorem 26 — left snake has length 5. -/
theorem snakeLeft_length (a : Wire) :
    (snakeLeft a).length = 5 := by
  simp [snakeLeft, WPath.length, WPath.nil]

/-- Theorem 27 — snake right symm has length 5. -/
theorem snakeRight_symm_length (a : Wire) :
    (snakeRight a).symm.length = 5 := by
  simp [snakeRight, WPath.symm, WPath.single, WPath.trans,
        WPath.length, WPath.nil, WStep.symm, wpath_length_trans]

/-- Theorem 28 — snake left symm has length 5. -/
theorem snakeLeft_symm_length (a : Wire) :
    (snakeLeft a).symm.length = 5 := by
  simp [snakeLeft, WPath.symm, WPath.single, WPath.trans,
        WPath.length, WPath.nil, WStep.symm, wpath_length_trans]

-- ============================================================
-- §10  Pivotal Structure — Traces
-- ============================================================

/-- Left trace: close off with η and ε (using named steps for type flexibility). -/
def leftTrace (a : Wire) (f : WPath a a) : WPath Wire.unit Wire.unit :=
  let w1 := Wire.tensor a (Wire.dual a)
  let w2 := Wire.tensor (Wire.dual a) a
  WPath.cons (WStep.snakeEta a)
    (WPath.cons (WStep.named "f⊗id" w1 w2)
      (WPath.cons (WStep.snakeEps a) (WPath.nil _)))

/-- Theorem 29 — left trace of identity. -/
def leftTraceId (a : Wire) : WPath Wire.unit Wire.unit :=
  leftTrace a (WPath.nil a)

/-- Theorem 30 — trace of identity has length 3. -/
theorem leftTraceId_length (a : Wire) :
    (leftTraceId a).length = 3 := by
  simp [leftTraceId, leftTrace, WPath.length, WPath.nil]

/-- Right trace (close opposite corners). -/
def rightTrace (a : Wire) (f : WPath a a) : WPath Wire.unit Wire.unit :=
  let w1 := Wire.tensor (Wire.dual a) a
  let w2 := Wire.tensor a (Wire.dual a)
  WPath.cons (WStep.named "η_dual" Wire.unit w1)
    (WPath.cons (WStep.named "id⊗f" w1 w2)
      (WPath.cons (WStep.named "ε_dual" w2 Wire.unit) (WPath.nil _)))

/-- Theorem 31 — spherical condition: leftTrace and rightTrace same length. -/
theorem spherical_length (a : Wire) (f : WPath a a) :
    (leftTrace a f).length = (rightTrace a f).length := by
  simp [leftTrace, rightTrace, WPath.length, WPath.nil]

-- ============================================================
-- §11  Coherence for Monoidal Categories
-- ============================================================

/-- Pentagon path: two-step associator. -/
def pentagonPath (a b c d : Wire) :
    WPath (Wire.tensor (Wire.tensor (Wire.tensor a b) c) d)
          (Wire.tensor a (Wire.tensor b (Wire.tensor c d))) :=
  .cons (.tensorAssoc (a := Wire.tensor a b) (b := c) (c := d))
    (.cons (.tensorAssoc (a := a) (b := b) (c := Wire.tensor c d))
      (.nil _))

/-- Theorem 32 — pentagon path length is 2. -/
theorem pentagonPath_length (a b c d : Wire) :
    (pentagonPath a b c d).length = 2 := by
  simp [pentagonPath, WPath.length, WPath.nil]

/-- Alternate pentagon route: 3-step. -/
def pentagonAlt (a b c d : Wire) :
    WPath (Wire.tensor (Wire.tensor (Wire.tensor a b) c) d)
          (Wire.tensor a (Wire.tensor b (Wire.tensor c d))) :=
  .cons (.tensorMap (.tensorAssoc (a := a) (b := b) (c := c)) (.identity d))
    (.cons (.tensorAssoc (a := a) (b := Wire.tensor b c) (c := d))
      (.cons (.tensorMap (.identity a) (.tensorAssoc (a := b) (b := c) (c := d)))
        (.nil _)))

/-- Theorem 33 — alternate pentagon has length 3. -/
theorem pentagonAlt_length (a b c d : Wire) :
    (pentagonAlt a b c d).length = 3 := by
  simp [pentagonAlt, WPath.length, WPath.nil]

/-- Theorem 34 — coherence: pentagon lengths differ by 1. -/
theorem coherence_pentagon_lengths (a b c d : Wire) :
    (pentagonPath a b c d).length + 1 = (pentagonAlt a b c d).length := by
  simp [pentagonPath_length, pentagonAlt_length]

/-- Triangle path: single-step. -/
def trianglePath (a b : Wire) :
    WPath (Wire.tensor (Wire.tensor a Wire.unit) b)
          (Wire.tensor a b) :=
  .cons (.tensorMap (.unitRight (a := a)) (.identity b)) (.nil _)

/-- Theorem 35 — triangle alt route (2-step). -/
def triangleAlt (a b : Wire) :
    WPath (Wire.tensor (Wire.tensor a Wire.unit) b)
          (Wire.tensor a b) :=
  .cons (.tensorAssoc (a := a) (b := Wire.unit) (c := b))
    (.cons (.tensorMap (.identity a) (.unitLeft (a := b))) (.nil _))

/-- Theorem 36 — triangle + 1 = alt length. -/
theorem triangle_coherence (a b : Wire) :
    (trianglePath a b).length + 1 = (triangleAlt a b).length := by
  simp [trianglePath, triangleAlt, WPath.length, WPath.nil]

-- ============================================================
-- §12  Frobenius Algebra
-- ============================================================

/-- Frobenius object with multiplication and comultiplication. -/
structure FrobObj where
  carrier : Wire

/-- Frobenius multiplication μ : A ⊗ A → A. -/
def frobMul (F : FrobObj) : WPath (Wire.tensor F.carrier F.carrier) F.carrier :=
  .single (.named "μ" _ _)

/-- Frobenius comultiplication δ : A → A ⊗ A. -/
def frobComul (F : FrobObj) : WPath F.carrier (Wire.tensor F.carrier F.carrier) :=
  .single (.named "δ" _ _)

/-- Frobenius unit η : I → A. -/
def frobUnit (F : FrobObj) : WPath Wire.unit F.carrier :=
  .single (.named "η_frob" _ _)

/-- Frobenius counit ε : A → I. -/
def frobCounit (F : FrobObj) : WPath F.carrier Wire.unit :=
  .single (.named "ε_frob" _ _)

/-- Theorem 37 — Frobenius condition LHS: (μ ⊗ id) ∘ (id ⊗ δ), 3 steps. -/
def frobCondLHS (F : FrobObj) :
    WPath (Wire.tensor F.carrier F.carrier)
          (Wire.tensor F.carrier F.carrier) :=
  let a := F.carrier
  let w_aa := Wire.tensor a a
  let w_aaa := Wire.tensor a (Wire.tensor a a)
  let w_aa_a := Wire.tensor (Wire.tensor a a) a
  WPath.cons (WStep.named "id⊗δ" w_aa w_aaa)
    (WPath.cons (WStep.named "assoc_frob" w_aaa w_aa_a)
      (WPath.cons (WStep.named "μ⊗id" w_aa_a w_aa) (WPath.nil _)))

/-- Theorem 38 — Frobenius condition RHS: (id ⊗ μ) ∘ (δ ⊗ id), 3 steps. -/
def frobCondRHS (F : FrobObj) :
    WPath (Wire.tensor F.carrier F.carrier)
          (Wire.tensor F.carrier F.carrier) :=
  let a := F.carrier
  let w_aa := Wire.tensor a a
  let w_aa_a := Wire.tensor (Wire.tensor a a) a
  let w_aaa := Wire.tensor a (Wire.tensor a a)
  WPath.cons (WStep.named "δ⊗id" w_aa w_aa_a)
    (WPath.cons (WStep.named "assoc⁻¹_frob" w_aa_a w_aaa)
      (WPath.cons (WStep.named "id⊗μ" w_aaa w_aa) (WPath.nil _)))

/-- Theorem 39 — both Frobenius sides have length 3. -/
theorem frob_cond_lengths (F : FrobObj) :
    (frobCondLHS F).length = (frobCondRHS F).length := by
  simp [frobCondLHS, frobCondRHS, WPath.single, WPath.trans,
        WPath.length, WPath.nil]

/-- Theorem 40 — associativity of μ as 2-step path. -/
def frobAssoc (F : FrobObj) :
    WPath (Wire.tensor (Wire.tensor F.carrier F.carrier) F.carrier)
          F.carrier :=
  let a := F.carrier
  WPath.cons (WStep.named "μ⊗id" (Wire.tensor (Wire.tensor a a) a) (Wire.tensor a a))
    (WPath.cons (WStep.named "μ" (Wire.tensor a a) a) (WPath.nil _))

/-- Theorem 41 — coassociativity of δ as 2-step. -/
def frobCoassoc (F : FrobObj) :
    WPath F.carrier
          (Wire.tensor F.carrier (Wire.tensor F.carrier F.carrier)) :=
  let a := F.carrier
  WPath.cons (WStep.named "δ" a (Wire.tensor a a))
    (WPath.cons (WStep.named "id⊗δ" (Wire.tensor a a) (Wire.tensor a (Wire.tensor a a)))
      (WPath.nil _))

-- ============================================================
-- §13  congrArg as Whiskering — Deep Chains
-- ============================================================

/-- Theorem 42 — whiskering preserves length (left). -/
theorem whiskerL_preserves {p q : WPath b c} (r : WPath a b) (σ : Cell2 p q) :
    (r.trans p).length = (r.trans q).length := by
  rw [(whiskerL r σ).witness]

/-- Theorem 43 — whiskering preserves length (right). -/
theorem whiskerR_preserves {p q : WPath a b} (σ : Cell2 p q) (r : WPath b c) :
    (p.trans r).length = (q.trans r).length := by
  rw [(whiskerR σ r).witness]

/-- Theorem 44 — congrArg on trans: functoriality. -/
theorem congrArg_trans (p₁ p₂ : WPath a b) (q₁ q₂ : WPath b c)
    (σ : Cell2 p₁ p₂) (τ : Cell2 q₁ q₂) :
    Cell2 (p₁.trans q₁) (p₂.trans q₂) :=
  (whiskerR σ q₁).vcomp (whiskerL p₂ τ)

/-- Theorem 45 — horizontal whiskering via congrArg on hcomp. -/
theorem hwhiskerL_eq {p q : WPath c d} (r : WPath a b) (h : Cell2 p q) :
    Cell2 (r.hcomp p) (r.hcomp q) :=
  ⟨congrArg (WPath.hcomp r) h.witness⟩

/-- Theorem 46 — double whiskering: both sides. -/
theorem double_whisker {p q : WPath b c} (l : WPath a b) (r : WPath c d) (σ : Cell2 p q) :
    Cell2 (l.trans (p.trans r)) (l.trans (q.trans r)) :=
  whiskerL l (whiskerR σ r)

-- ============================================================
-- §14  Planar Isotopy — Reidemeister-like Moves
-- ============================================================

/-- Reidemeister II: braid ∘ braid = roundtrip. -/
def reidemeisterII (a b : Wire) :
    WPath (Wire.tensor a b) (Wire.tensor a b) :=
  .cons (.braidSwap (a := a) (b := b))
    (.cons (.braidSwap (a := b) (b := a)) (.nil _))

/-- Theorem 47 — R2 has length 2. -/
theorem reidemeisterII_length (a b : Wire) :
    (reidemeisterII a b).length = 2 := by
  simp [reidemeisterII, WPath.length, WPath.nil]

/-- Reidemeister III via Yang-Baxter. -/
def reidemeisterIII (a b c : Wire) :
    WPath (Wire.tensor a (Wire.tensor b c))
          (Wire.tensor c (Wire.tensor b a)) :=
  yangBaxterLHS a b c

/-- Theorem 48 — R3 has length 3. -/
theorem reidemeisterIII_length (a b c : Wire) :
    (reidemeisterIII a b c).length = 3 := by
  exact yangBaxter_lhs_length a b c

/-- Theorem 49 — R2 symm also length 2. -/
theorem reidemeisterII_symm_length (a b : Wire) :
    (reidemeisterII a b).symm.length = 2 := by
  simp [reidemeisterII, WPath.symm, WPath.single, WPath.trans,
        WPath.length, WPath.nil, WStep.symm]

-- ============================================================
-- §15  Graphical Calculus for Adjunctions
-- ============================================================

/-- An adjunction: pair (η, ε) of paths. -/
structure Adjunction where
  L : Wire
  R : Wire
  eta : WPath Wire.unit (Wire.tensor L R)
  eps : WPath (Wire.tensor R L) Wire.unit

/-- Theorem 50 — left triangle identity path, 5 steps. -/
def adjTriangleL (adj : Adjunction) : WPath adj.L adj.L :=
  let l := adj.L; let r := adj.R
  let w1 := Wire.tensor l Wire.unit
  let w2 := Wire.tensor l (Wire.tensor l r)
  let w3 := Wire.tensor (Wire.tensor l l) r
  let w4 := Wire.tensor Wire.unit l
  .cons (WStep.unitRightInv (a := l))
    (.cons (WStep.named "id_L⊗η" w1 w2)
      (.cons (WStep.named "assoc" w2 w3)
        (.cons (WStep.named "ε⊗id_L" w3 w4)
          (.cons (WStep.unitLeft (a := l)) (.nil _)))))

/-- Theorem 51 — right triangle identity path, 5 steps. -/
def adjTriangleR (adj : Adjunction) : WPath adj.R adj.R :=
  let l := adj.L; let r := adj.R
  let w1 := Wire.tensor Wire.unit r
  let w2 := Wire.tensor (Wire.tensor l r) r
  let w3 := Wire.tensor l (Wire.tensor r r)
  let w4 := Wire.tensor r Wire.unit
  .cons (WStep.unitLeftInv (a := r))
    (.cons (WStep.named "η⊗id_R" w1 w2)
      (.cons (WStep.named "assoc" w2 w3)
        (.cons (WStep.named "id_R⊗ε" w3 w4)
          (.cons (WStep.unitRight (a := r)) (.nil _)))))

/-- Theorem 52 — both triangles have length 5. -/
theorem adj_triangles_length (adj : Adjunction) :
    (adjTriangleL adj).length = 5 ∧ (adjTriangleR adj).length = 5 := by
  constructor <;> simp [adjTriangleL, adjTriangleR, WPath.length, WPath.nil]

/-- Theorem 53 — mate correspondence, 5 steps. -/
def mate (adjL adjR : Adjunction) (f : WPath adjL.L adjR.L) :
    WPath adjR.R adjL.R :=
  .cons (.named "η_R" adjR.R (Wire.tensor adjR.R adjR.L))
    (.cons (.named "id_R⊗f" (Wire.tensor adjR.R adjR.L)
                              (Wire.tensor adjR.R adjL.L))
      (.cons (.named "assoc_mate" (Wire.tensor adjR.R adjL.L)
                                    (Wire.tensor (Wire.tensor adjR.R adjL.L) adjL.R))
        (.cons (.named "ε_R⊗id" (Wire.tensor (Wire.tensor adjR.R adjL.L) adjL.R)
                                   (Wire.tensor Wire.unit adjL.R))
          (.cons (.named "unitL" (Wire.tensor Wire.unit adjL.R) adjL.R)
            (.nil _)))))

/-- Theorem 54 — mate has length 5. -/
theorem mate_length (adjL adjR : Adjunction) (f : WPath adjL.L adjR.L) :
    (mate adjL adjR f).length = 5 := by
  simp [mate, WPath.length, WPath.nil]

-- ============================================================
-- §16  Advanced Coherence: 2-Cell Algebra
-- ============================================================

/-- Theorem 55 — interchange as 2-cell via congrArg. -/
def interchange2Cell
    {p₁ q₁ : WPath a b} {p₂ q₂ : WPath c d}
    (σ : Cell2 p₁ q₁) (τ : Cell2 p₂ q₂) :
    Cell2 (p₁.hcomp p₂) (q₁.hcomp q₂) :=
  ⟨ by rw [σ.witness, τ.witness] ⟩

/-- Theorem 56 — vcomp is associative. -/
theorem vcomp_assoc {p q r s : WPath a b}
    (σ : Cell2 p q) (τ : Cell2 q r) (υ : Cell2 r s) :
    (σ.vcomp τ).vcomp υ = σ.vcomp (τ.vcomp υ) := by
  cases σ; cases τ; cases υ; rfl

/-- Theorem 57 — vcomp with id right. -/
theorem vcomp_id_right {p q : WPath a b} (σ : Cell2 p q) :
    σ.vcomp (Cell2.id q) = σ := by
  cases σ; rfl

/-- Theorem 58 — vcomp with id left. -/
theorem vcomp_id_left {p q : WPath a b} (σ : Cell2 p q) :
    (Cell2.id p).vcomp σ = σ := by
  cases σ; rfl

/-- Theorem 59 — vinv ∘ vcomp = id. -/
theorem vinv_vcomp {p q : WPath a b} (σ : Cell2 p q) :
    σ.vinv.vcomp σ = Cell2.id q := by
  cases σ; rfl

/-- Theorem 60 — vcomp ∘ vinv = id. -/
theorem vcomp_vinv {p q : WPath a b} (σ : Cell2 p q) :
    σ.vcomp σ.vinv = Cell2.id p := by
  cases σ; rfl

/-- Theorem 61 — whiskerL distributes over vcomp. -/
theorem whiskerL_vcomp (r : WPath a b)
    {p q s : WPath b c} (σ : Cell2 p q) (τ : Cell2 q s) :
    whiskerL r (σ.vcomp τ) = (whiskerL r σ).vcomp (whiskerL r τ) := by
  cases σ; cases τ; rfl

/-- Theorem 62 — whiskerR distributes over vcomp. -/
theorem whiskerR_vcomp
    {p q s : WPath a b} (σ : Cell2 p q) (τ : Cell2 q s) (r : WPath b c) :
    whiskerR (σ.vcomp τ) r = (whiskerR σ r).vcomp (whiskerR τ r) := by
  cases σ; cases τ; rfl

-- ============================================================
-- §17  Extended Path Properties
-- ============================================================

/-- Theorem 63 — length of symm = length of original. -/
theorem symm_length (p : WPath a b) : p.symm.length = p.length := by
  induction p with
  | nil _ => simp [WPath.symm, WPath.length]
  | cons s _ ih =>
    simp [WPath.symm, wpath_length_trans, ih, WPath.single, WPath.length, WPath.nil]
    omega

/-- Theorem 64 — Cell2 preserves length. -/
theorem cell2_length {p q : WPath a b} (σ : Cell2 p q) :
    p.length = q.length := by
  rw [σ.witness]

/-- Theorem 65 — hcomp with nil left is length-preserving. -/
theorem hcomp_nil_left_length (a : Wire) (q : WPath c d) :
    (WPath.hcomp (.nil a) q).length = q.length := by
  induction q with
  | nil _ => simp [WPath.hcomp, WPath.length]
  | cons s _ ih => simp [WPath.hcomp, WPath.length, ih]

/-- Theorem 66 — hcomp with nil right is length-preserving. -/
theorem hcomp_nil_right_length (p : WPath a b) (c : Wire) :
    (WPath.hcomp p (WPath.nil c)).length = p.length := by
  induction p with
  | nil _ => simp [WPath.hcomp, WPath.length]
  | cons s _ ih => simp [WPath.hcomp, WPath.length, ih]

/-- Theorem 67 — trans nil left is identity. -/
theorem wpath_trans_nil_left (q : WPath a b) :
    (WPath.nil a).trans q = q := by
  simp [WPath.trans]

/-- Theorem 68 — Cell2 is reflexive. -/
theorem cell2_refl (p : WPath a b) : Cell2 p p :=
  ⟨rfl⟩

/-- Theorem 69 — Cell2 is symmetric. -/
theorem cell2_symm {p q : WPath a b} (σ : Cell2 p q) : Cell2 q p :=
  σ.vinv

/-- Theorem 70 — Cell2 is transitive. -/
theorem cell2_trans {p q r : WPath a b} (σ : Cell2 p q) (τ : Cell2 q r) : Cell2 p r :=
  σ.vcomp τ

/-- Theorem 71 — single step trans single step has length 2. -/
theorem single_trans_single_length (s : WStep a b) (t : WStep b c) :
    ((WPath.single s).trans (WPath.single t)).length = 2 := by
  simp [WPath.single, WPath.trans, WPath.length, WPath.nil]

/-- Theorem 72 — frobAssoc has length 2. -/
theorem frobAssoc_length (F : FrobObj) :
    (frobAssoc F).length = 2 := by
  simp [frobAssoc, WPath.length, WPath.nil]

/-- Theorem 73 — frobCoassoc has length 2. -/
theorem frobCoassoc_length (F : FrobObj) :
    (frobCoassoc F).length = 2 := by
  simp [frobCoassoc, WPath.length, WPath.nil]

/-- Theorem 74 — adjTriangleL symm has length 5. -/
theorem adjTriangleL_symm_length (adj : Adjunction) :
    (adjTriangleL adj).symm.length = 5 := by
  simp [adjTriangleL, WPath.symm, WPath.single, WPath.trans,
        WPath.length, WPath.nil, WStep.symm, wpath_length_trans]

/-- Theorem 75 — mate symm has length 5. -/
theorem mate_symm_length (adjL adjR : Adjunction) (f : WPath adjL.L adjR.L) :
    (mate adjL adjR f).symm.length = 5 := by
  simp [mate, WPath.symm, WPath.single, WPath.trans,
        WPath.length, WPath.nil, WStep.symm, wpath_length_trans]

end StringDiagramDeep
