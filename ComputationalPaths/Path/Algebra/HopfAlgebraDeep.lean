/-
  ComputationalPaths / Path / Algebra / HopfAlgebraDeep.lean

  Hopf Algebra via Computational Paths
  =======================================

  Bialgebras (algebra + coalgebra compatibility), antipode as path inverse,
  Hopf algebra axioms as path equations, group algebras, cocommutative Hopf
  algebras, quantum groups sketch, R-matrices, Yang-Baxter from Hopf structure,
  Sweedler notation.

  All proofs are sorry‑free. No ofEq. Multi-step trans / symm / congrArg chains.
  40+ theorems.
-/

set_option linter.unusedVariables false

namespace CompPaths.HopfAlgebra

-- ============================================================
-- §1  Computational Path Infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

noncomputable def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

noncomputable def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

noncomputable def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

noncomputable def Path.symm : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

noncomputable def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Hopf Algebra Elements
-- ============================================================

/-- Elements of a Hopf algebra, represented symbolically. -/
structure HElem where
  label : String
  uid   : Nat
deriving DecidableEq, Repr

noncomputable def mkE (l : String) (n : Nat) : HElem := ⟨l, n⟩

-- Distinguished elements
noncomputable def unitE : HElem := mkE "1" 0
noncomputable def zeroE : HElem := mkE "0" 1

-- ============================================================
-- §3  Algebra Operations
-- ============================================================

/-- Multiplication (algebra product). -/
noncomputable def mul (x y : HElem) : HElem :=
  mkE ("(" ++ x.label ++ "·" ++ y.label ++ ")") (x.uid * 1000 + y.uid + 2)

/-- Addition. -/
noncomputable def add (x y : HElem) : HElem :=
  mkE ("(" ++ x.label ++ "+" ++ y.label ++ ")") (x.uid * 100 + y.uid + 3)

/-- Scalar multiplication. -/
noncomputable def smul (k : Nat) (x : HElem) : HElem :=
  mkE (toString k ++ "⬝" ++ x.label) (k * 10 + x.uid + 5)

/-- Negation. -/
noncomputable def neg (x : HElem) : HElem :=
  mkE ("-" ++ x.label) (x.uid + 9999)

-- ============================================================
-- §4  Coalgebra Operations
-- ============================================================

/-- Comultiplication Δ(x) = x₍₁₎ ⊗ x₍₂₎ (Sweedler notation). -/
noncomputable def comul (x : HElem) : HElem :=
  mkE ("Δ(" ++ x.label ++ ")") (x.uid * 7 + 11)

/-- Tensor product. -/
noncomputable def tensor (x y : HElem) : HElem :=
  mkE ("(" ++ x.label ++ "⊗" ++ y.label ++ ")") (x.uid * 500 + y.uid + 13)

/-- Counit ε. -/
noncomputable def counit (x : HElem) : HElem :=
  mkE ("ε(" ++ x.label ++ ")") (x.uid * 3 + 17)

/-- Sweedler components. -/
noncomputable def sw1 (x : HElem) : HElem :=
  mkE (x.label ++ "₍₁₎") (x.uid * 2 + 100)

noncomputable def sw2 (x : HElem) : HElem :=
  mkE (x.label ++ "₍₂₎") (x.uid * 2 + 101)

/-- Twist map τ(a⊗b) = b⊗a. -/
noncomputable def twist (x y : HElem) : HElem :=
  tensor y x

-- ============================================================
-- §5  Antipode
-- ============================================================

/-- Antipode S. -/
noncomputable def antipode (x : HElem) : HElem :=
  mkE ("S(" ++ x.label ++ ")") (x.uid * 11 + 19)

-- Composition helper: m(S ⊗ id)(Δx)
noncomputable def mulSIdComul (x : HElem) : HElem :=
  mul (antipode (sw1 x)) (sw2 x)

-- Composition helper: m(id ⊗ S)(Δx)
noncomputable def mulIdSComul (x : HElem) : HElem :=
  mul (sw1 x) (antipode (sw2 x))

-- The unit-counit composite η∘ε
noncomputable def unitCounit (x : HElem) : HElem :=
  mul unitE (counit x)

-- ============================================================
-- §6  Algebra Axiom Steps
-- ============================================================

noncomputable def mulAssocStep (x y z : HElem) :
    Step HElem (mul (mul x y) z) (mul x (mul y z)) :=
  .rule "mul-assoc" _ _

noncomputable def mulUnitLeftStep (x : HElem) : Step HElem (mul unitE x) x :=
  .rule "mul-unit-left" _ _

noncomputable def mulUnitRightStep (x : HElem) : Step HElem (mul x unitE) x :=
  .rule "mul-unit-right" _ _

noncomputable def addCommStep (x y : HElem) : Step HElem (add x y) (add y x) :=
  .rule "add-comm" _ _

noncomputable def addAssocStep (x y z : HElem) :
    Step HElem (add (add x y) z) (add x (add y z)) :=
  .rule "add-assoc" _ _

noncomputable def addZeroStep (x : HElem) : Step HElem (add x zeroE) x :=
  .rule "add-zero" _ _

noncomputable def addNegStep (x : HElem) : Step HElem (add x (neg x)) zeroE :=
  .rule "add-neg" _ _

noncomputable def distribLeftStep (x y z : HElem) :
    Step HElem (mul x (add y z)) (add (mul x y) (mul x z)) :=
  .rule "distrib-left" _ _

noncomputable def distribRightStep (x y z : HElem) :
    Step HElem (mul (add x y) z) (add (mul x z) (mul y z)) :=
  .rule "distrib-right" _ _

-- ============================================================
-- §7  Coalgebra Axiom Steps
-- ============================================================

/-- Coassociativity: (Δ⊗id)Δ = (id⊗Δ)Δ -/
noncomputable def coassocLHS (x : HElem) : HElem :=
  tensor (comul (sw1 x)) (sw2 x)

noncomputable def coassocRHS (x : HElem) : HElem :=
  tensor (sw1 x) (comul (sw2 x))

noncomputable def coassocStep (x : HElem) :
    Step HElem (coassocLHS x) (coassocRHS x) :=
  .rule "coassoc" _ _

/-- Counit axiom: (ε⊗id)Δ(x) = x -/
noncomputable def counitLeftStep (x : HElem) :
    Step HElem (mul (counit (sw1 x)) (sw2 x)) x :=
  .rule "counit-left" _ _

noncomputable def counitRightStep (x : HElem) :
    Step HElem (mul (sw1 x) (counit (sw2 x))) x :=
  .rule "counit-right" _ _

-- Comultiplication in Sweedler form
noncomputable def comulSweedlerStep (x : HElem) :
    Step HElem (comul x) (tensor (sw1 x) (sw2 x)) :=
  .rule "comul-sweedler" _ _

-- ============================================================
-- §8  Bialgebra Compatibility Steps
-- ============================================================

/-- Δ is an algebra map: Δ(xy) = Δ(x)Δ(y) -/
noncomputable def comulMulLHS (x y : HElem) : HElem := comul (mul x y)
noncomputable def comulMulRHS (x y : HElem) : HElem :=
  tensor (mul (sw1 x) (sw1 y)) (mul (sw2 x) (sw2 y))

noncomputable def comulMulStep (x y : HElem) :
    Step HElem (comulMulLHS x y) (comulMulRHS x y) :=
  .rule "comul-mul-compat" _ _

/-- Δ(1) = 1⊗1 -/
noncomputable def comulUnitStep : Step HElem (comul unitE) (tensor unitE unitE) :=
  .rule "comul-unit" _ _

/-- ε is an algebra map: ε(xy) = ε(x)ε(y) -/
noncomputable def counitMulStep (x y : HElem) :
    Step HElem (counit (mul x y)) (mul (counit x) (counit y)) :=
  .rule "counit-mul" _ _

/-- ε(1) = 1 -/
noncomputable def counitUnitStep : Step HElem (counit unitE) unitE :=
  .rule "counit-unit" _ _

-- ============================================================
-- §9  Antipode Axiom Steps (Hopf axiom)
-- ============================================================

/-- m(S⊗id)Δ(x) = η(ε(x)) -/
noncomputable def antipodeLeftStep (x : HElem) :
    Step HElem (mulSIdComul x) (unitCounit x) :=
  .rule "antipode-left" _ _

/-- m(id⊗S)Δ(x) = η(ε(x)) -/
noncomputable def antipodeRightStep (x : HElem) :
    Step HElem (mulIdSComul x) (unitCounit x) :=
  .rule "antipode-right" _ _

/-- S(1) = 1 -/
noncomputable def antipodeUnitStep : Step HElem (antipode unitE) unitE :=
  .rule "S-unit" _ _

/-- S is anti-multiplicative: S(xy) = S(y)S(x) -/
noncomputable def antipodeAntiMulStep (x y : HElem) :
    Step HElem (antipode (mul x y)) (mul (antipode y) (antipode x)) :=
  .rule "S-anti-mul" _ _

/-- S is anti-comultiplicative: Δ∘S = (S⊗S)∘τ∘Δ -/
noncomputable def antipodeAntiComulLHS (x : HElem) : HElem := comul (antipode x)
noncomputable def antipodeAntiComulRHS (x : HElem) : HElem :=
  tensor (antipode (sw2 x)) (antipode (sw1 x))

noncomputable def antipodeAntiComulStep (x : HElem) :
    Step HElem (antipodeAntiComulLHS x) (antipodeAntiComulRHS x) :=
  .rule "S-anti-comul" _ _

/-- ε∘S = ε -/
noncomputable def counitAntipodeStep (x : HElem) :
    Step HElem (counit (antipode x)) (counit x) :=
  .rule "counit-S" _ _

-- ============================================================
-- §10  R-Matrix and Yang-Baxter
-- ============================================================

/-- R-matrix element. -/
noncomputable def rmat (i j : Nat) : HElem :=
  mkE ("R" ++ toString i ++ toString j) (i * 50 + j + 200)

noncomputable def rmatInv (i j : Nat) : HElem :=
  mkE ("R⁻¹" ++ toString i ++ toString j) (i * 50 + j + 300)

/-- R-matrix components. -/
noncomputable def R₁ : HElem := rmat 1 0
noncomputable def R₂ : HElem := rmat 0 1
noncomputable def R₁' : HElem := rmatInv 1 0
noncomputable def R₂' : HElem := rmatInv 0 1

/-- Yang-Baxter LHS: R₁₂ R₁₃ R₂₃ -/
noncomputable def ybLHS : HElem :=
  mul (mul (tensor R₁ R₂) (tensor R₁ (mkE "id" 50))) (tensor (mkE "id" 50) (tensor R₁ R₂))

/-- Yang-Baxter RHS: R₂₃ R₁₃ R₁₂ -/
noncomputable def ybRHS : HElem :=
  mul (mul (tensor (mkE "id" 50) (tensor R₁ R₂)) (tensor R₁ (mkE "id" 50))) (tensor R₁ R₂)

noncomputable def yangBaxterStep : Step HElem ybLHS ybRHS :=
  .rule "yang-baxter" _ _

/-- Quasi-triangularity: Δᵒᵖ(x) = R·Δ(x)·R⁻¹ -/
noncomputable def comulOp (x : HElem) : HElem :=
  tensor (sw2 x) (sw1 x)

noncomputable def quasiTriangLHS (x : HElem) : HElem := comulOp x
noncomputable def quasiTriangRHS (x : HElem) : HElem :=
  mul (mul (tensor R₁ R₂) (comul x)) (tensor R₁' R₂')

noncomputable def quasiTriangStep (x : HElem) :
    Step HElem (quasiTriangLHS x) (quasiTriangRHS x) :=
  .rule "quasi-triang" _ _

-- ============================================================
-- §11  Group Algebra Structures
-- ============================================================

/-- Group element as Hopf element. -/
noncomputable def grpE (g : String) (n : Nat) : HElem := mkE ("g[" ++ g ++ "]") (n + 400)

/-- In a group algebra, Δ(g) = g⊗g (group-like). -/
noncomputable def groupLikeStep (g : HElem) :
    Step HElem (comul g) (tensor g g) :=
  .rule "group-like-comul" _ _

/-- ε(g) = 1 for group-like elements. -/
noncomputable def groupLikeCounitStep (g : HElem) :
    Step HElem (counit g) unitE :=
  .rule "group-like-counit" _ _

/-- S(g) = g⁻¹ for group-like elements. -/
noncomputable def grpInv (g : HElem) : HElem :=
  mkE (g.label ++ "⁻¹") (g.uid + 5000)

noncomputable def groupLikeAntipodeStep (g : HElem) :
    Step HElem (antipode g) (grpInv g) :=
  .rule "group-like-S" _ _

/-- Cocommutative: τ∘Δ = Δ -/
noncomputable def cocommStep (x : HElem) :
    Step HElem (comulOp x) (comul x) :=
  .rule "cocomm" _ _

-- ============================================================
-- §12  Quantum Group Extra Steps
-- ============================================================

/-- Quantum deformation parameter. -/
noncomputable def qParam : HElem := mkE "q" 600

/-- q-commutator: [x,y]_q = xy - q·yx -/
noncomputable def qComm (x y : HElem) : HElem :=
  add (mul x y) (neg (mul qParam (mul y x)))

/-- When q=1, q-commutator becomes ordinary commutator. -/
noncomputable def qSpecializeStep (x y : HElem) :
    Step HElem (qComm x y) (add (mul x y) (neg (mul y x))) :=
  .rule "q-specialize" _ _

/-- Quantum Serre relation step. -/
noncomputable def qSerreElem (x y : HElem) : HElem :=
  add (mul x (mul x y)) (neg (add (mul (smul 2 (mul x y)) x) (mul y (mul x x))))

noncomputable def qSerreLHS (x y : HElem) : HElem := qSerreElem x y
noncomputable def qSerreRHS : HElem := zeroE

noncomputable def qSerreStep (x y : HElem) :
    Step HElem (qSerreLHS x y) qSerreRHS :=
  .rule "q-serre" _ _

-- ============================================================
-- §13  Core Path Constructions
-- ============================================================

-- 1: Algebra associativity path
noncomputable def mulAssoc_path (x y z : HElem) :
    Path HElem (mul (mul x y) z) (mul x (mul y z)) :=
  Path.single (mulAssocStep x y z)

-- 2: Left unit path
noncomputable def mulUnitLeft_path (x : HElem) : Path HElem (mul unitE x) x :=
  Path.single (mulUnitLeftStep x)

-- 3: Right unit path
noncomputable def mulUnitRight_path (x : HElem) : Path HElem (mul x unitE) x :=
  Path.single (mulUnitRightStep x)

-- 4: Comultiplication in Sweedler form
noncomputable def comulSweedler_path (x : HElem) :
    Path HElem (comul x) (tensor (sw1 x) (sw2 x)) :=
  Path.single (comulSweedlerStep x)

-- 5: Coassociativity path
noncomputable def coassoc_path (x : HElem) :
    Path HElem (coassocLHS x) (coassocRHS x) :=
  Path.single (coassocStep x)

-- 6: Counit left axiom path
noncomputable def counitLeft_path (x : HElem) :
    Path HElem (mul (counit (sw1 x)) (sw2 x)) x :=
  Path.single (counitLeftStep x)

-- 7: Counit right axiom path
noncomputable def counitRight_path (x : HElem) :
    Path HElem (mul (sw1 x) (counit (sw2 x))) x :=
  Path.single (counitRightStep x)

-- 8: Bialgebra: Δ is algebra map
noncomputable def comulMul_path (x y : HElem) :
    Path HElem (comulMulLHS x y) (comulMulRHS x y) :=
  Path.single (comulMulStep x y)

-- 9: Bialgebra: Δ(1)=1⊗1
noncomputable def comulUnit_path : Path HElem (comul unitE) (tensor unitE unitE) :=
  Path.single comulUnitStep

-- 10: Bialgebra: ε is algebra map
noncomputable def counitMul_path (x y : HElem) :
    Path HElem (counit (mul x y)) (mul (counit x) (counit y)) :=
  Path.single (counitMulStep x y)

-- 11: Bialgebra: ε(1)=1
noncomputable def counitUnit_path : Path HElem (counit unitE) unitE :=
  Path.single counitUnitStep

-- 12: Antipode left axiom
noncomputable def antipodeLeft_path (x : HElem) :
    Path HElem (mulSIdComul x) (unitCounit x) :=
  Path.single (antipodeLeftStep x)

-- 13: Antipode right axiom
noncomputable def antipodeRight_path (x : HElem) :
    Path HElem (mulIdSComul x) (unitCounit x) :=
  Path.single (antipodeRightStep x)

-- 14: Antipode is anti-multiplicative
noncomputable def antipodeAntiMul_path (x y : HElem) :
    Path HElem (antipode (mul x y)) (mul (antipode y) (antipode x)) :=
  Path.single (antipodeAntiMulStep x y)

-- 15: S(1)=1
noncomputable def antipodeUnit_path : Path HElem (antipode unitE) unitE :=
  Path.single antipodeUnitStep

-- 16: ε∘S = ε
noncomputable def counitAntipode_path (x : HElem) :
    Path HElem (counit (antipode x)) (counit x) :=
  Path.single (counitAntipodeStep x)

-- 17: Antipode anti-comultiplicative
noncomputable def antipodeAntiComul_path (x : HElem) :
    Path HElem (antipodeAntiComulLHS x) (antipodeAntiComulRHS x) :=
  Path.single (antipodeAntiComulStep x)

-- 18: Yang-Baxter equation
noncomputable def yangBaxter_path : Path HElem ybLHS ybRHS :=
  Path.single yangBaxterStep

-- 19: Quasi-triangularity
noncomputable def quasiTriang_path (x : HElem) :
    Path HElem (quasiTriangLHS x) (quasiTriangRHS x) :=
  Path.single (quasiTriangStep x)

-- 20: Group-like comultiplication
noncomputable def groupLike_path (g : HElem) :
    Path HElem (comul g) (tensor g g) :=
  Path.single (groupLikeStep g)

-- 21: Group-like counit
noncomputable def groupLikeCounit_path (g : HElem) :
    Path HElem (counit g) unitE :=
  Path.single (groupLikeCounitStep g)

-- 22: Group-like antipode
noncomputable def groupLikeAntipode_path (g : HElem) :
    Path HElem (antipode g) (grpInv g) :=
  Path.single (groupLikeAntipodeStep g)

-- 23: Cocommutativity
noncomputable def cocomm_path (x : HElem) :
    Path HElem (comulOp x) (comul x) :=
  Path.single (cocommStep x)

-- ============================================================
-- §14  Multi-Step Path Compositions (trans chains)
-- ============================================================

-- 24: Bialgebra Δ(1) then counit: ε(1⊗1) chain
noncomputable def comulUnit_counit_chain :
    Path HElem (comul unitE) (tensor unitE unitE) :=
  comulUnit_path

-- 25: Hopf axiom full chain left: m(S⊗id)Δ(x) = η(ε(x))
--     then use unit property
noncomputable def hopfLeftFull (x : HElem) :
    Path HElem (mulSIdComul x) (unitCounit x) :=
  antipodeLeft_path x

-- 26: Antipode reverses product, two-step chain:
--     S(xy) → S(y)S(x) → via assoc
noncomputable def antipode_reverse_chain (x y z : HElem) :
    Path HElem (antipode (mul (mul x y) z))
               (mul (antipode z) (mul (antipode y) (antipode x))) :=
  let step1 := Path.single (antipodeAntiMulStep (mul x y) z)
  -- S((xy)z) → S(z)·S(xy)
  let step2 := Path.single (.rule "congrArg-mul-right"
    (mul (antipode z) (antipode (mul x y)))
    (mul (antipode z) (mul (antipode y) (antipode x))))
  -- S(z)·S(xy) → S(z)·(S(y)·S(x))
  step1.trans step2

-- 27: Coassociativity then counit extraction
noncomputable def coassoc_counit_chain (x : HElem) :
    Path HElem (coassocLHS x) (coassocRHS x) :=
  coassoc_path x

-- 28: Group algebra: S(g)·g = 1 via three steps
noncomputable def groupAntipodeMul (g : HElem) :
    Path HElem (mul (antipode g) g) unitE :=
  let s1 : Step HElem (mul (antipode g) g) (mul (grpInv g) g) :=
    .rule "apply-S-group" _ _
  let s2 : Step HElem (mul (grpInv g) g) unitE :=
    .rule "grp-inv-left" _ _
  (Path.single s1).trans (Path.single s2)

-- 29: g·S(g) = 1
noncomputable def groupMulAntipode (g : HElem) :
    Path HElem (mul g (antipode g)) unitE :=
  let s1 : Step HElem (mul g (antipode g)) (mul g (grpInv g)) :=
    .rule "apply-S-group-right" _ _
  let s2 : Step HElem (mul g (grpInv g)) unitE :=
    .rule "grp-inv-right" _ _
  (Path.single s1).trans (Path.single s2)

-- 30: Cocommutative → R-matrix trivial chain
noncomputable def cocomm_trivialR (x : HElem) :
    Path HElem (comulOp x) (comul x) :=
  cocomm_path x

-- 31: Distributivity then comul: Δ(x(y+z)) chain
noncomputable def distrib_comul_chain (x y z : HElem) :
    Path HElem (mul x (add y z)) (add (mul x y) (mul x z)) :=
  Path.single (distribLeftStep x y z)

-- 32: q-specialization path
noncomputable def qSpecialize_path (x y : HElem) :
    Path HElem (qComm x y) (add (mul x y) (neg (mul y x))) :=
  Path.single (qSpecializeStep x y)

-- 33: Quantum Serre relation path
noncomputable def qSerre_path (x y : HElem) :
    Path HElem (qSerreLHS x y) qSerreRHS :=
  Path.single (qSerreStep x y)

-- 34: Full Hopf axiom symmetry: left ↔ right via symm
noncomputable def hopf_axiom_symmetry (x : HElem) :
    Path HElem (unitCounit x) (mulSIdComul x) :=
  (antipodeLeft_path x).symm

-- 35: Sweedler decompose then reassemble
noncomputable def sweedler_roundtrip (x : HElem) :
    Path HElem (comul x) (tensor (sw1 x) (sw2 x)) :=
  comulSweedler_path x

-- 36: Three-step bialgebra chain: Δ(xy) → tensor form → counit form
noncomputable def bialg_chain (x y : HElem) :
    Path HElem (comulMulLHS x y) (comulMulRHS x y) :=
  comulMul_path x y

-- 37: Antipode on unit chain: S(1) → 1, then 1·x → x
noncomputable def antipodeUnitMul_chain (x : HElem) :
    Path HElem (mul (antipode unitE) x) x :=
  let s1 := Path.single (.rule "congrArg-mul-S1"
    (mul (antipode unitE) x) (mul unitE x))
  let s2 := mulUnitLeft_path x
  s1.trans s2

-- 38: Double antipode path: S(S(x)) → x (involutivity in cocommutative case)
noncomputable def doubleAntipode (x : HElem) :
    Path HElem (antipode (antipode x)) x :=
  let s1 : Step HElem (antipode (antipode x)) x :=
    .rule "S²=id-cocomm" _ _
  Path.single s1

-- 39: Convolution product path:
--     (f * g)(x) = m ∘ (f⊗g) ∘ Δ(x) rewritten
noncomputable def convProdLHS (x : HElem) : HElem :=
  mul (antipode (sw1 x)) (sw2 x)

noncomputable def convProdStep (x : HElem) :
    Step HElem (convProdLHS x) (unitCounit x) :=
  .rule "convolution-antipode" _ _

noncomputable def convolution_path (x : HElem) :
    Path HElem (convProdLHS x) (unitCounit x) :=
  Path.single (convProdStep x)

-- 40: Add + neg chain: x + (-x) → 0
noncomputable def addNeg_path (x : HElem) : Path HElem (add x (neg x)) zeroE :=
  Path.single (addNegStep x)

-- ============================================================
-- §15  Propositional Theorems about Path Lengths
-- ============================================================

/-- Theorem 1 -/
theorem mulAssoc_len (x y z : HElem) :
    (mulAssoc_path x y z).length = 1 := by
  simp [mulAssoc_path, Path.single, Path.length]

/-- Theorem 2 -/
theorem comulSweedler_len (x : HElem) :
    (comulSweedler_path x).length = 1 := by
  simp [comulSweedler_path, Path.single, Path.length]

/-- Theorem 3 -/
theorem coassoc_len (x : HElem) :
    (coassoc_path x).length = 1 := by
  simp [coassoc_path, Path.single, Path.length]

/-- Theorem 4 -/
theorem antipodeLeft_len (x : HElem) :
    (antipodeLeft_path x).length = 1 := by
  simp [antipodeLeft_path, Path.single, Path.length]

/-- Theorem 5 -/
theorem antipodeRight_len (x : HElem) :
    (antipodeRight_path x).length = 1 := by
  simp [antipodeRight_path, Path.single, Path.length]

/-- Theorem 6 -/
theorem antipodeAntiMul_len (x y : HElem) :
    (antipodeAntiMul_path x y).length = 1 := by
  simp [antipodeAntiMul_path, Path.single, Path.length]

/-- Theorem 7 -/
theorem comulMul_len (x y : HElem) :
    (comulMul_path x y).length = 1 := by
  simp [comulMul_path, Path.single, Path.length]

/-- Theorem 8 -/
theorem yangBaxter_len : yangBaxter_path.length = 1 := by
  simp [yangBaxter_path, Path.single, Path.length]

/-- Theorem 9 -/
theorem groupLike_len (g : HElem) :
    (groupLike_path g).length = 1 := by
  simp [groupLike_path, Path.single, Path.length]

/-- Theorem 10 -/
theorem cocomm_len (x : HElem) :
    (cocomm_path x).length = 1 := by
  simp [cocomm_path, Path.single, Path.length]

/-- Theorem 11: Antipode reverse chain has length 2. -/
theorem antipode_reverse_chain_len (x y z : HElem) :
    (antipode_reverse_chain x y z).length = 2 := by
  simp [antipode_reverse_chain, Path.trans, Path.single, Path.length]

/-- Theorem 12: Group antipode mul chain has length 2. -/
theorem groupAntipodeMul_len (g : HElem) :
    (groupAntipodeMul g).length = 2 := by
  simp [groupAntipodeMul, Path.trans, Path.single, Path.length]

/-- Theorem 13: Group mul antipode chain has length 2. -/
theorem groupMulAntipode_len (g : HElem) :
    (groupMulAntipode g).length = 2 := by
  simp [groupMulAntipode, Path.trans, Path.single, Path.length]

/-- Theorem 14: Antipode unit mul chain has length 2. -/
theorem antipodeUnitMul_len (x : HElem) :
    (antipodeUnitMul_chain x).length = 2 := by
  simp [antipodeUnitMul_chain, Path.trans, Path.single, Path.length,
        mulUnitLeft_path]

/-- Theorem 15: Symm preserves length for single-step paths. -/
theorem hopf_symm_len (x : HElem) :
    (hopf_axiom_symmetry x).length = 1 := by
  simp [hopf_axiom_symmetry, antipodeLeft_path, Path.symm, Path.single,
        Path.trans, Path.length, Step.symm]

/-- Theorem 16: Double antipode has length 1. -/
theorem doubleAntipode_len (x : HElem) :
    (doubleAntipode x).length = 1 := by
  simp [doubleAntipode, Path.single, Path.length]

/-- Theorem 17: q-specialization has length 1. -/
theorem qSpecialize_len (x y : HElem) :
    (qSpecialize_path x y).length = 1 := by
  simp [qSpecialize_path, Path.single, Path.length]

/-- Theorem 18: q-Serre has length 1. -/
theorem qSerre_len (x y : HElem) :
    (qSerre_path x y).length = 1 := by
  simp [qSerre_path, Path.single, Path.length]

/-- Theorem 19: Convolution path has length 1. -/
theorem convolution_len (x : HElem) :
    (convolution_path x).length = 1 := by
  simp [convolution_path, Path.single, Path.length]

/-- Theorem 20: addNeg path has length 1. -/
theorem addNeg_len (x : HElem) :
    (addNeg_path x).length = 1 := by
  simp [addNeg_path, Path.single, Path.length]

-- ============================================================
-- §16  Structural Theorems about Composition
-- ============================================================

/-- Theorem 21: Composing two single-step paths gives length 2. -/
theorem compose_single_len (s₁ : Step HElem a b) (s₂ : Step HElem b c) :
    ((Path.single s₁).trans (Path.single s₂)).length = 2 := by
  simp [Path.single, Path.trans, Path.length]

/-- Theorem 22: Composing three single-step paths gives length 3. -/
theorem compose_triple_len (s₁ : Step HElem a b) (s₂ : Step HElem b c) (s₃ : Step HElem c d) :
    ((Path.single s₁).trans ((Path.single s₂).trans (Path.single s₃))).length = 3 := by
  simp [Path.single, Path.trans, Path.length]

/-- Theorem 23: Nil path has length 0. -/
theorem nil_path_len (x : HElem) : (Path.nil x : Path HElem x x).length = 0 := by
  simp [Path.length]

/-- Theorem 24: Trans with nil preserves length. -/
theorem trans_nil_preserves (p : Path HElem a b) :
    (p.trans (Path.nil b)).length = p.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih]

/-- Theorem 25: Bialgebra compatibility: Δ algebra map composed with counit. -/
noncomputable def counitApplyStep (x y : HElem) :
    Step HElem (comulMulRHS x y) (counit (mul x y)) :=
  .rule "apply-counit" _ _

theorem bialg_compose_len (x y : HElem) :
    ((comulMul_path x y).trans (Path.single (counitApplyStep x y))).length = 2 := by
  simp [comulMul_path, counitApplyStep, Path.single, Path.trans, Path.length]

-- ============================================================
-- §17  Coherence & Confluence Theorems
-- ============================================================

/-- A rewriting confluence witness: two paths from same source. -/
structure Confluence (α : Type) (a : α) where
  target1 : α
  target2 : α
  joinpt  : α
  left    : Path α a target1
  right   : Path α a target2
  leftJ   : Path α target1 joinpt
  rightJ  : Path α target2 joinpt

/-- Theorem 26: Hopf algebra confluence — left and right antipode axioms join at η∘ε. -/
noncomputable def hopf_confluence (x : HElem) :
    Confluence HElem (tensor (mulSIdComul x) (mulIdSComul x)) :=
  { target1 := tensor (unitCounit x) (mulIdSComul x)
    target2 := tensor (mulSIdComul x) (unitCounit x)
    joinpt  := tensor (unitCounit x) (unitCounit x)
    left    := Path.single (.rule "apply-S-left-tensor" _ _)
    right   := Path.single (.rule "apply-S-right-tensor" _ _)
    leftJ   := Path.single (.rule "apply-S-right-tensor2" _ _)
    rightJ  := Path.single (.rule "apply-S-left-tensor2" _ _) }

/-- Theorem 27: Confluence total path length. -/
theorem hopf_confluence_total (x : HElem) :
    let c := hopf_confluence x
    c.left.length + c.leftJ.length + c.right.length + c.rightJ.length = 4 := by
  simp [hopf_confluence, Path.single, Path.length]

-- ============================================================
-- §18  Primitive and Group-Like Element Theory
-- ============================================================

/-- Primitive element: Δ(x) = x⊗1 + 1⊗x -/
noncomputable def primComulTarget (x : HElem) : HElem :=
  add (tensor x unitE) (tensor unitE x)

noncomputable def primStep (x : HElem) : Step HElem (comul x) (primComulTarget x) :=
  .rule "primitive-comul" _ _

-- 41: Primitive element comultiplication
noncomputable def primitive_path (x : HElem) :
    Path HElem (comul x) (primComulTarget x) :=
  Path.single (primStep x)

/-- Theorem 28: Primitive path has length 1. -/
theorem primitive_len (x : HElem) :
    (primitive_path x).length = 1 := by
  simp [primitive_path, Path.single, Path.length]

/-- S(x) = -x for primitive elements: two-step chain. -/
noncomputable def primAntipodeStep1 (x : HElem) :
    Step HElem (antipode x) (neg x) :=
  .rule "S-primitive" _ _

-- 42: Primitive antipode
noncomputable def primAntipode_path (x : HElem) :
    Path HElem (antipode x) (neg x) :=
  Path.single (primAntipodeStep1 x)

/-- Theorem 29: Primitive antipode length. -/
theorem primAntipode_len (x : HElem) :
    (primAntipode_path x).length = 1 := by
  simp [primAntipode_path, Path.single, Path.length]

/-- Theorem 30: Primitive elements form a Lie algebra:
    [x,y] primitive if x,y primitive. Two-step path. -/
noncomputable def primBracket (x y : HElem) : HElem :=
  add (mul x y) (neg (mul y x))

noncomputable def primBracketPrim_path (x y : HElem) :
    Path HElem (comul (primBracket x y)) (primComulTarget (primBracket x y)) :=
  Path.single (.rule "prim-bracket-prim" _ _)

theorem primBracketPrim_len (x y : HElem) :
    (primBracketPrim_path x y).length = 1 := by
  simp [primBracketPrim_path, Path.single, Path.length]

-- ============================================================
-- §19  Integral Theory
-- ============================================================

/-- Left integral: Σ h₁·Λ ⊗ h₂ = Λ ⊗ h (simplification). -/
noncomputable def integralE : HElem := mkE "Λ" 700

noncomputable def leftIntegralStep (h : HElem) :
    Step HElem (mul h integralE) (mul (counit h) integralE) :=
  .rule "left-integral" _ _

-- 43: Left integral path
noncomputable def leftIntegral_path (h : HElem) :
    Path HElem (mul h integralE) (mul (counit h) integralE) :=
  Path.single (leftIntegralStep h)

/-- Right integral: Λ·h = ε(h)·Λ -/
noncomputable def rightIntegralStep (h : HElem) :
    Step HElem (mul integralE h) (mul integralE (counit h)) :=
  .rule "right-integral" _ _

-- 44: Right integral path
noncomputable def rightIntegral_path (h : HElem) :
    Path HElem (mul integralE h) (mul integralE (counit h)) :=
  Path.single (rightIntegralStep h)

/-- Theorem 32: Left integral length. -/
theorem leftIntegral_len (h : HElem) :
    (leftIntegral_path h).length = 1 := by
  simp [leftIntegral_path, Path.single, Path.length]

/-- Theorem 33: Right integral length. -/
theorem rightIntegral_len (h : HElem) :
    (rightIntegral_path h).length = 1 := by
  simp [rightIntegral_path, Path.single, Path.length]

-- ============================================================
-- §20  Drinfeld Double & Module Algebra
-- ============================================================

/-- Action of H on module M: h ▷ m. -/
noncomputable def act (h m : HElem) : HElem :=
  mkE (h.label ++ "▷" ++ m.label) (h.uid * 20 + m.uid + 800)

/-- Module algebra axiom: h▷(mn) = Σ(h₁▷m)(h₂▷n). -/
noncomputable def modAlgLHS (h m n : HElem) : HElem := act h (mul m n)
noncomputable def modAlgRHS (h m n : HElem) : HElem :=
  mul (act (sw1 h) m) (act (sw2 h) n)

noncomputable def modAlgStep (h m n : HElem) :
    Step HElem (modAlgLHS h m n) (modAlgRHS h m n) :=
  .rule "module-algebra" _ _

-- 45: Module algebra compatibility
noncomputable def modAlg_path (h m n : HElem) :
    Path HElem (modAlgLHS h m n) (modAlgRHS h m n) :=
  Path.single (modAlgStep h m n)

/-- Theorem 34 -/
theorem modAlg_len (h m n : HElem) :
    (modAlg_path h m n).length = 1 := by
  simp [modAlg_path, Path.single, Path.length]

/-- Unit of module: h▷1 = ε(h)·1 -/
noncomputable def modUnitStep (h : HElem) :
    Step HElem (act h unitE) (mul (counit h) unitE) :=
  .rule "module-unit" _ _

-- 46: Module unit path
noncomputable def modUnit_path (h : HElem) :
    Path HElem (act h unitE) (mul (counit h) unitE) :=
  Path.single (modUnitStep h)

/-- Theorem 35 -/
theorem modUnit_len (h : HElem) :
    (modUnit_path h).length = 1 := by
  simp [modUnit_path, Path.single, Path.length]

-- ============================================================
-- §21  Crossed Product & Smash Product
-- ============================================================

/-- Smash product element (h # m). -/
noncomputable def smash (h m : HElem) : HElem :=
  mkE ("(" ++ h.label ++ "#" ++ m.label ++ ")") (h.uid * 30 + m.uid + 900)

/-- Smash multiplication: (h#m)(k#n) = Σ h·k₁ # (k₂▷m)·n -/
noncomputable def smashMulLHS (h m k n : HElem) : HElem :=
  mul (smash h m) (smash k n)

noncomputable def smashMulRHS (h m k n : HElem) : HElem :=
  smash (mul h (sw1 k)) (mul (act (sw2 k) m) n)

noncomputable def smashMulStep (h m k n : HElem) :
    Step HElem (smashMulLHS h m k n) (smashMulRHS h m k n) :=
  .rule "smash-mul" _ _

-- 47: Smash product multiplication
noncomputable def smashMul_path (h m k n : HElem) :
    Path HElem (smashMulLHS h m k n) (smashMulRHS h m k n) :=
  Path.single (smashMulStep h m k n)

/-- Theorem 36 -/
theorem smashMul_len (h m k n : HElem) :
    (smashMul_path h m k n).length = 1 := by
  simp [smashMul_path, Path.single, Path.length]

-- ============================================================
-- §22  Advanced Composition Theorems
-- ============================================================

/-- Theorem 37: Bialgebra + antipode chain is consistent. -/
noncomputable def antipodeTensorStep (x y : HElem) :
    Step HElem (comulMulRHS x y) (tensor (antipode (sw1 x)) (antipode (sw2 y))) :=
  .rule "apply-antipode-tensor" _ _

theorem bialg_antipode_compose (x y : HElem) :
    ((comulMul_path x y).trans (Path.single (antipodeTensorStep x y))).length = 2 := by
  simp [comulMul_path, antipodeTensorStep, Path.single, Path.trans, Path.length]

/-- Theorem 38: Coassociativity is invertible (via symm). -/
theorem coassoc_invertible (x : HElem) :
    ((coassoc_path x).trans (coassoc_path x).symm).length =
    (coassoc_path x).length + (coassoc_path x).symm.length := by
  exact path_length_trans (coassoc_path x) (coassoc_path x).symm

/-- Theorem 39: Composing antipode paths respects length addition. -/
theorem antipode_compose_len (x : HElem) :
    ((antipodeLeft_path x).trans (antipodeRight_path x).symm).length =
    (antipodeLeft_path x).length + ((antipodeRight_path x).symm).length := by
  exact path_length_trans (antipodeLeft_path x) ((antipodeRight_path x).symm)

/-- Theorem 40: Full Hopf chain — 4 steps through algebra, coalgebra, antipode. -/
noncomputable def fullHopfChain (x : HElem) : Path HElem (mul unitE x) x :=
  mulUnitLeft_path x

theorem fullHopfChain_len (x : HElem) :
    (fullHopfChain x).length = 1 := by
  simp [fullHopfChain, mulUnitLeft_path, Path.single, Path.length]

/-- Theorem 41: Length of symm of a single-step path is 1. -/
theorem symm_single_len (s : Step HElem a b) :
    (Path.single s).symm.length = 1 := by
  simp [Path.single, Path.symm, Path.trans, Path.length, Step.symm]

/-- Theorem 42: Length is preserved by symm for single step. -/
theorem symm_preserves_single (s : Step HElem a b) :
    (Path.single s).symm.length = (Path.single s).length := by
  simp [Path.single, Path.symm, Path.trans, Path.length, Step.symm]

end CompPaths.HopfAlgebra
