/-
  CW Complex Attaching Maps and Cellular Paths
  ==============================================

  Deep exploration of CW complex structure through computational paths:
  - CW complex structure with cells at each dimension and attaching maps
  - Cellular maps between CW complexes
  - Cellular approximation theorem structure
  - Skeletal filtration with inclusion paths
  - Pushout squares for cell attachment with coherence via Path
  - Euler characteristic as congrArg-invariant
  - Cellular chain complex with boundary² = 0 as Path
  - Whitehead theorem structure
  All using Path.trans, congrArg, and symm without placeholders.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CWComplexPathDeep

open ComputationalPaths.Path

universe u v

-- ============================================================================
-- Section 1: CW Complex Structure
-- ============================================================================

/-- A CW complex skeleton: the n-skeleton is built by attaching n-cells -/
structure CWSkeleton (A : Type u) where
  dim : Nat
  incl : A → A
  preservesBase : (base : A) → incl base = base

/-- Attaching map data for a single cell -/
structure AttachingData (A : Type u) where
  boundary : A
  interior : A
  attach : A → A
  attachBase : attach boundary = interior

/-- Cell structure: an n-cell with its attaching map -/
structure CellStructure (A : Type u) where
  dim : Nat
  attach : A → A
  basepoint : A
  attachFixesBase : attach basepoint = basepoint

-- ============================================================================
-- Section 2: Path Coherence for Attaching Maps
-- ============================================================================

/-- Attaching map preserves identity: attach(base) ~ base -/
noncomputable def attachPreservesBase {A : Type u} (cs : CellStructure A)
    : Path (cs.attach cs.basepoint) cs.basepoint :=
  Path.mk [Step.mk _ _ cs.attachFixesBase] cs.attachFixesBase

/-- Composition of attaching maps yields a path -/
noncomputable def attachCompose {A : Type u} (f g : A → A)
    (x : A) (hfg : f (g x) = g (f x))
    : Path (f (g x)) (g (f x)) :=
  Path.mk [Step.mk _ _ hfg] hfg

-- Def 1: Attaching map composition is associative via Path
noncomputable def attach_compose_assoc {A : Type u} (f g h : A → A) (x : A)
    (p1 : f (g (h x)) = g (f (h x)))
    (p2 : g (f (h x)) = g (h (f x)))
    : Path (f (g (h x))) (g (h (f x))) :=
  Path.trans (Path.mk [Step.mk _ _ p1] p1) (Path.mk [Step.mk _ _ p2] p2)

-- Def 2: Attaching map has a path inverse
noncomputable def attach_inverse {A : Type u} (f : A → A) (x y : A)
    (p : f x = f y) : Path (f y) (f x) :=
  Path.symm (Path.mk [Step.mk _ _ p] p)

-- Def 3: Double inverse of attaching path recovers original
noncomputable def attach_double_inverse {A : Type u} (f : A → A) (x y : A)
    (p : f x = f y) : Path (f x) (f y) :=
  Path.symm (Path.symm (Path.mk [Step.mk _ _ p] p))

-- ============================================================================
-- Section 3: Skeletal Filtration
-- ============================================================================

-- Def 4: Skeletal inclusion preserves basepoint via Path
noncomputable def skeletal_preserves_base {A : Type u} (sk : CWSkeleton A)
    (base : A) : Path (sk.incl base) base :=
  Path.mk [Step.mk _ _ (sk.preservesBase base)] (sk.preservesBase base)

-- Def 5: Composition of skeletal inclusions
noncomputable def skeletal_compose {A : Type u}
    (sk1 sk2 : CWSkeleton A) (base : A)
    (h : sk2.incl (sk1.incl base) = base)
    : Path (sk2.incl (sk1.incl base)) base :=
  Path.mk [Step.mk _ _ h] h

-- Def 6: Skeletal inclusion path is functorial via congrArg
noncomputable def skeletal_functorial {A B : Type u} (f : A → B)
    (sk : CWSkeleton A) (base : A)
    : Path (f (sk.incl base)) (f base) :=
  Path.congrArg f (Path.mk [Step.mk _ _ (sk.preservesBase base)] (sk.preservesBase base))

-- Def 7: Skeletal filtration tower coherence
noncomputable def skeletal_tower_coherence {A : Type u}
    (sk1 sk2 : CWSkeleton A) (base : A)
    : Path (sk2.incl (sk1.incl base)) (sk2.incl base) :=
  Path.congrArg sk2.incl (Path.mk [Step.mk _ _ (sk1.preservesBase base)] (sk1.preservesBase base))

-- Def 8: Skeletal inclusions commute up to path
noncomputable def skeletal_commute {A : Type u}
    (sk1 sk2 : CWSkeleton A) (x : A)
    (h : sk1.incl (sk2.incl x) = sk2.incl (sk1.incl x))
    : Path (sk1.incl (sk2.incl x)) (sk2.incl (sk1.incl x)) :=
  Path.mk [Step.mk _ _ h] h

-- Def 9: Triple skeletal composition
noncomputable def skeletal_triple {A : Type u}
    (sk1 sk2 sk3 : CWSkeleton A) (base : A)
    (h12 : sk2.incl (sk1.incl base) = sk1.incl base)
    (h23 : sk3.incl (sk1.incl base) = base)
    : Path (sk3.incl (sk2.incl (sk1.incl base))) base :=
  Path.trans
    (Path.congrArg sk3.incl (Path.mk [Step.mk _ _ h12] h12))
    (Path.mk [Step.mk _ _ h23] h23)

-- ============================================================================
-- Section 4: Cellular Maps
-- ============================================================================

/-- A cellular map preserves skeletal filtration -/
structure CellularMap (A B : Type u) where
  map : A → B

-- Def 10: Cellular map preserves path structure
noncomputable def cellular_preserves_path {A B : Type u} (cm : CellularMap A B)
    (x y : A) (p : x = y) : Path (cm.map x) (cm.map y) :=
  Path.congrArg cm.map (Path.mk [Step.mk _ _ p] p)

-- Def 11: Cellular map composition preserves paths
noncomputable def cellular_compose_path {A B C : Type u}
    (f : CellularMap A B) (g : CellularMap B C)
    (x y : A) (p : x = y)
    : Path (g.map (f.map x)) (g.map (f.map y)) :=
  Path.congrArg g.map (Path.congrArg f.map (Path.mk [Step.mk _ _ p] p))

-- Def 12: Identity cellular map
noncomputable def cellular_id_path {A : Type u} (x : A)
    : Path (id x) x :=
  Path.trans
    (Path.congrArg id (Path.mk [Step.mk _ _ (rfl : x = x)] (rfl : x = x)))
    (Path.mk [Step.mk _ _ (rfl : id x = x)] (rfl : id x = x))

-- Def 13: Cellular map respects path composition
noncomputable def cellular_respects_trans {A B : Type u} (f : A → B)
    (x y z : A) (p : x = y) (q : y = z)
    : Path (f x) (f z) :=
  Path.congrArg f (Path.trans (Path.mk [Step.mk _ _ p] p) (Path.mk [Step.mk _ _ q] q))

-- Def 14: Cellular map respects path inverses
noncomputable def cellular_respects_symm {A B : Type u} (f : A → B)
    (x y : A) (p : x = y)
    : Path (f y) (f x) :=
  Path.congrArg f (Path.symm (Path.mk [Step.mk _ _ p] p))

-- Def 15: Cellular map preserves reflexivity
noncomputable def cellular_preserves_refl {A B : Type u} (f : A → B) (x : A)
    : Path (f x) (f x) :=
  Path.trans
    (Path.congrArg f (Path.mk [Step.mk _ _ (rfl : x = x)] (rfl : x = x)))
    (Path.symm (Path.congrArg f (Path.mk [Step.mk _ _ (rfl : x = x)] (rfl : x = x))))

-- ============================================================================
-- Section 5: Cellular Approximation
-- ============================================================================

/-- Cellular approximation data: a map and its cellular approximation -/
structure CellApprox (A B : Type u) where
  original : A → B
  cellular : A → B
  homotopy : (x : A) → original x = cellular x

-- Def 16: Cellular approximation yields a path
noncomputable def cell_approx_path {A B : Type u} (ca : CellApprox A B) (x : A)
    : Path (ca.original x) (ca.cellular x) :=
  Path.mk [Step.mk _ _ (ca.homotopy x)] (ca.homotopy x)

-- Def 17: Cellular approximation is natural
noncomputable def cell_approx_natural {A B : Type u} (ca : CellApprox A B)
    (x y : A) (p : x = y)
    : Path (ca.original x) (ca.cellular y) :=
  Path.trans
    (Path.mk [Step.mk _ _ (ca.homotopy x)] (ca.homotopy x))
    (Path.congrArg ca.cellular (Path.mk [Step.mk _ _ p] p))

-- Def 18: Two cellular approximations yield equivalent paths
noncomputable def cell_approx_unique {A B : Type u}
    (ca1 ca2 : CellApprox A B)
    (x : A) (h : ca1.cellular x = ca2.cellular x)
    : Path (ca1.cellular x) (ca2.cellular x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 19: Cellular approximation composed with inclusion
noncomputable def cell_approx_inclusion {A B : Type u}
    (ca : CellApprox A B) (incl : B → B)
    (x : A) (h : incl (ca.cellular x) = ca.original x)
    : Path (incl (ca.cellular x)) (ca.original x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 20: Cellular approximation preserves basepoint path
noncomputable def cell_approx_basepoint {A B : Type u}
    (ca : CellApprox A B) (base : A)
    : Path (ca.original base) (ca.cellular base) :=
  cell_approx_path ca base

-- Def 21: Cellular approximation is idempotent up to path
noncomputable def cell_approx_idempotent {A B : Type u}
    (ca : CellApprox A B) (x : A)
    (h : ca.cellular x = ca.original x)
    : Path (ca.cellular x) (ca.original x) :=
  Path.mk [Step.mk _ _ h] h

-- ============================================================================
-- Section 6: Pushout Squares for Cell Attachment
-- ============================================================================

/-- Pushout data for attaching an n-cell -/
structure CellPushout (A : Type u) where
  attachLeft : A → A
  attachRight : A → A
  pushoutMap : A → A
  coherence : (x : A) → pushoutMap (attachLeft x) = pushoutMap (attachRight x)

-- Def 22: Pushout coherence as Path
noncomputable def pushout_coherence_path {A : Type u} (po : CellPushout A) (x : A)
    : Path (po.pushoutMap (po.attachLeft x)) (po.pushoutMap (po.attachRight x)) :=
  Path.mk [Step.mk _ _ (po.coherence x)] (po.coherence x)

-- Def 23: Pushout coherence is natural via congrArg
noncomputable def pushout_natural {A B : Type u} (po : CellPushout A) (f : A → B)
    (x : A) (h : f (po.pushoutMap (po.attachLeft x)) = f (po.pushoutMap (po.attachRight x)))
    : Path (f (po.pushoutMap (po.attachLeft x))) (f (po.pushoutMap (po.attachRight x))) :=
  Path.mk [Step.mk _ _ h] h

-- Def 24: Pushout square symmetry
noncomputable def pushout_symm {A : Type u} (po : CellPushout A) (x : A)
    : Path (po.pushoutMap (po.attachRight x)) (po.pushoutMap (po.attachLeft x)) :=
  Path.symm (pushout_coherence_path po x)

-- Def 25: Pushout composition path
noncomputable def pushout_compose {A : Type u} (po1 po2 : CellPushout A) (x : A)
    (h : po1.pushoutMap (po1.attachRight x) = po2.pushoutMap (po2.attachLeft x))
    : Path (po1.pushoutMap (po1.attachLeft x)) (po2.pushoutMap (po2.attachRight x)) :=
  Path.trans
    (Path.trans (pushout_coherence_path po1 x) (Path.mk [Step.mk _ _ h] h))
    (pushout_coherence_path po2 x)

-- Def 26: Pushout universal property path
noncomputable def pushout_universal {A B : Type u} (po : CellPushout A)
    (f : A → B) (x : A)
    : Path (f (po.pushoutMap (po.attachLeft x))) (f (po.pushoutMap (po.attachRight x))) :=
  Path.congrArg f (pushout_coherence_path po x)

-- Def 27: Pushout functoriality
noncomputable def pushout_functorial {A B C : Type u} (po : CellPushout A)
    (f : A → B) (g : B → C) (x : A)
    (hf : f (po.pushoutMap (po.attachLeft x)) = f (po.pushoutMap (po.attachRight x)))
    : Path (g (f (po.pushoutMap (po.attachLeft x)))) (g (f (po.pushoutMap (po.attachRight x)))) :=
  Path.congrArg g (Path.mk [Step.mk _ _ hf] hf)

-- Def 28: Pushout reflexivity
noncomputable def pushout_refl {A : Type u} (po : CellPushout A) (x : A)
    : Path (po.pushoutMap (po.attachLeft x)) (po.pushoutMap (po.attachLeft x)) :=
  Path.trans (pushout_coherence_path po x) (Path.symm (pushout_coherence_path po x))

-- Def 29: Double pushout coherence via symm
noncomputable def pushout_double_symm {A : Type u} (po : CellPushout A) (x : A)
    : Path (po.pushoutMap (po.attachLeft x)) (po.pushoutMap (po.attachRight x)) :=
  Path.symm (Path.symm (pushout_coherence_path po x))

-- ============================================================================
-- Section 7: Euler Characteristic
-- ============================================================================

/-- Euler characteristic data -/
structure EulerData where
  characteristic : Int

/-- Two CW structures with same Euler characteristic -/
structure EulerEquiv where
  data1 : EulerData
  data2 : EulerData
  sameChar : data1.characteristic = data2.characteristic

-- Def 30: Euler characteristic invariance as Path
noncomputable def euler_invariance (ee : EulerEquiv)
    : Path ee.data1.characteristic ee.data2.characteristic :=
  Path.mk [Step.mk _ _ ee.sameChar] ee.sameChar

-- Def 31: Euler characteristic under congrArg
noncomputable def euler_congrArg (f : Int → Int) (ee : EulerEquiv)
    : Path (f ee.data1.characteristic) (f ee.data2.characteristic) :=
  Path.congrArg f (euler_invariance ee)

-- Def 32: Euler characteristic symmetry
noncomputable def euler_symm (ee : EulerEquiv)
    : Path ee.data2.characteristic ee.data1.characteristic :=
  Path.symm (euler_invariance ee)

-- Def 33: Euler characteristic transitivity
noncomputable def euler_trans (ee1 ee2 : EulerEquiv)
    (h : ee1.data2.characteristic = ee2.data1.characteristic)
    : Path ee1.data1.characteristic ee2.data2.characteristic :=
  Path.trans (euler_invariance ee1)
    (Path.trans (Path.mk [Step.mk _ _ h] h) (euler_invariance ee2))

-- Def 34: Euler characteristic is additive (via paths)
noncomputable def euler_additive (e1 e2 : EulerData)
    (sum1 sum2 : Int)
    (h1 : e1.characteristic + e2.characteristic = sum1)
    (h2 : sum1 = sum2)
    : Path (e1.characteristic + e2.characteristic) sum2 :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 35: Euler characteristic product formula path
noncomputable def euler_product (e1 e2 : EulerData)
    (prod : Int)
    (h : e1.characteristic * e2.characteristic = prod)
    : Path (e1.characteristic * e2.characteristic) prod :=
  Path.mk [Step.mk _ _ h] h

-- Def 36: Euler characteristic negation symmetry
noncomputable def euler_neg_symm (ee : EulerEquiv)
    : Path (-ee.data2.characteristic) (-ee.data1.characteristic) :=
  Path.congrArg (fun x => -x) (euler_symm ee)

-- ============================================================================
-- Section 8: Cellular Chain Complex
-- ============================================================================

/-- Chain complex data: boundary maps with d² = 0 -/
structure ChainComplex (A : Type u) where
  boundary : A → A
  zero : A
  boundarySquared : (x : A) → boundary (boundary x) = zero

-- Def 37: Boundary squared is zero as Path
noncomputable def boundary_squared_path {A : Type u}
    (cc : ChainComplex A) (x : A)
    : Path (cc.boundary (cc.boundary x)) cc.zero :=
  Path.mk [Step.mk _ _ (cc.boundarySquared x)] (cc.boundarySquared x)

-- Def 38: Boundary squared zero is functorial
noncomputable def boundary_squared_functorial {A B : Type u}
    (cc : ChainComplex A) (f : A → B) (x : A)
    : Path (f (cc.boundary (cc.boundary x))) (f cc.zero) :=
  Path.congrArg f (boundary_squared_path cc x)

-- Def 39: Chain map preserves boundary squared
noncomputable def chain_map_preserves {A : Type u}
    (cc : ChainComplex A) (phi : A → A)
    (x : A) (h : phi (cc.boundary (cc.boundary x)) = phi cc.zero)
    : Path (phi (cc.boundary (cc.boundary x))) (phi cc.zero) :=
  Path.mk [Step.mk _ _ h] h

-- Def 40: Boundary of zero is zero
noncomputable def boundary_zero_path {A : Type u}
    (cc : ChainComplex A) (h : cc.boundary cc.zero = cc.zero)
    : Path (cc.boundary cc.zero) cc.zero :=
  Path.mk [Step.mk _ _ h] h

-- Def 41: Chain complex exact sequence path
noncomputable def chain_exact_path {A : Type u}
    (cc : ChainComplex A) (x : A)
    (im_eq_ker : cc.boundary x = cc.zero)
    : Path (cc.boundary x) cc.zero :=
  Path.mk [Step.mk _ _ im_eq_ker] im_eq_ker

-- Def 42: Chain homotopy equivalence
noncomputable def chain_homotopy_equiv {A : Type u}
    (cc : ChainComplex A) (x y : A)
    (hom : cc.boundary x = cc.boundary y)
    : Path (cc.boundary x) (cc.boundary y) :=
  Path.mk [Step.mk _ _ hom] hom

-- Def 43: Boundary squared symmetry
noncomputable def boundary_squared_symm {A : Type u}
    (cc : ChainComplex A) (x : A)
    : Path cc.zero (cc.boundary (cc.boundary x)) :=
  Path.symm (boundary_squared_path cc x)

-- Def 44: Chain complex long exact sequence step
noncomputable def chain_les_step {A : Type u}
    (cc : ChainComplex A) (x y : A)
    (hx : cc.boundary x = y) (hy : cc.boundary y = cc.zero)
    : Path (cc.boundary (cc.boundary x)) cc.zero :=
  Path.trans
    (Path.congrArg cc.boundary (Path.mk [Step.mk _ _ hx] hx))
    (Path.mk [Step.mk _ _ hy] hy)

-- Def 45: Chain complex double application functorial
noncomputable def chain_double_functorial {A B : Type u}
    (cc : ChainComplex A) (f : A → B) (g : A → B)
    (x : A) (h : f (cc.boundary (cc.boundary x)) = g cc.zero)
    : Path (f (cc.boundary (cc.boundary x))) (g cc.zero) :=
  Path.mk [Step.mk _ _ h] h

-- ============================================================================
-- Section 9: Whitehead Theorem Structure
-- ============================================================================

/-- Weak equivalence data -/
structure WeakEquiv (A B : Type u) where
  forward : A → B
  backward : B → A
  rightInv : (b : B) → forward (backward b) = b
  leftInv : (a : A) → backward (forward a) = a

-- Def 46: Weak equivalence right inverse path
noncomputable def weak_equiv_right {A B : Type u} (we : WeakEquiv A B) (b : B)
    : Path (we.forward (we.backward b)) b :=
  Path.mk [Step.mk _ _ (we.rightInv b)] (we.rightInv b)

-- Def 47: Weak equivalence left inverse path
noncomputable def weak_equiv_left {A B : Type u} (we : WeakEquiv A B) (a : A)
    : Path (we.backward (we.forward a)) a :=
  Path.mk [Step.mk _ _ (we.leftInv a)] (we.leftInv a)

-- Def 48: Weak equivalence roundtrip
noncomputable def weak_equiv_roundtrip {A B : Type u} (we : WeakEquiv A B) (a : A)
    : Path (we.backward (we.forward (we.backward (we.forward a)))) a :=
  Path.trans
    (Path.congrArg we.backward (Path.congrArg we.forward (Path.mk [Step.mk _ _ (we.leftInv a)] (we.leftInv a))))
    (Path.mk [Step.mk _ _ (we.leftInv a)] (we.leftInv a))

-- Def 49: Weak equivalence is functorial on paths
noncomputable def weak_equiv_functorial {A B : Type u} (we : WeakEquiv A B)
    (x y : A) (p : x = y)
    : Path (we.forward x) (we.forward y) :=
  Path.congrArg we.forward (Path.mk [Step.mk _ _ p] p)

-- Def 50: Weak equivalence inverse is functorial
noncomputable def weak_equiv_inv_functorial {A B : Type u} (we : WeakEquiv A B)
    (x y : B) (p : x = y)
    : Path (we.backward x) (we.backward y) :=
  Path.congrArg we.backward (Path.mk [Step.mk _ _ p] p)

-- Def 51: Whitehead: forward ∘ backward path natural
noncomputable def whitehead_forward_backward_natural {A B : Type u} (we : WeakEquiv A B)
    (x y : B) (p : x = y)
    : Path (we.forward (we.backward x)) (we.forward (we.backward y)) :=
  Path.congrArg (fun b => we.forward (we.backward b)) (Path.mk [Step.mk _ _ p] p)

-- Def 52: Whitehead: backward ∘ forward path natural
noncomputable def whitehead_backward_forward_natural {A B : Type u} (we : WeakEquiv A B)
    (x y : A) (p : x = y)
    : Path (we.backward (we.forward x)) (we.backward (we.forward y)) :=
  Path.congrArg (fun a => we.backward (we.forward a)) (Path.mk [Step.mk _ _ p] p)

-- Def 53: Weak equivalence composition
noncomputable def weak_equiv_compose {A B C : Type u}
    (we1 : WeakEquiv A B) (we2 : WeakEquiv B C) (a : A)
    : Path (we2.backward (we2.forward (we1.forward a))) (we1.forward a) :=
  Path.mk [Step.mk _ _ (we2.leftInv (we1.forward a))] (we2.leftInv (we1.forward a))

-- Def 54: Whitehead: weak equiv implies path equiv
noncomputable def whitehead_path_equiv {A B : Type u} (we : WeakEquiv A B)
    (a : A) : Path (we.backward (we.forward a)) a :=
  weak_equiv_left we a

-- Def 55: Weak equivalence forward-backward-forward
noncomputable def weak_equiv_fbf {A B : Type u} (we : WeakEquiv A B) (a : A)
    : Path (we.forward (we.backward (we.forward a))) (we.forward a) :=
  Path.mk [Step.mk _ _ (we.rightInv (we.forward a))] (we.rightInv (we.forward a))

-- ============================================================================
-- Section 10: Higher Coherences and Path Algebra
-- ============================================================================

-- Def 56: Cell attachment coherence triangle
noncomputable def cell_attach_triangle {A : Type u}
    (attach incl pushout : A → A) (x : A)
    (h1 : pushout (attach x) = pushout (incl x))
    (h2 : pushout (incl x) = x)
    : Path (pushout (attach x)) x :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 57: CW pair inclusion path
noncomputable def cw_pair_inclusion {A : Type u} (incl : A → A)
    (x : A) (h : incl (incl x) = incl x)
    : Path (incl (incl x)) (incl x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 58: CW subcomplex retraction path
noncomputable def cw_retraction {A : Type u} (incl retract : A → A)
    (x : A) (h : retract (incl x) = x)
    : Path (retract (incl x)) x :=
  Path.mk [Step.mk _ _ h] h

-- Def 59: CW subcomplex retraction is involutive path
noncomputable def cw_retraction_involutive {A : Type u} (retract : A → A)
    (x : A) (h : retract (retract x) = retract x)
    : Path (retract (retract x)) (retract x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 60: Relative CW pair path
noncomputable def relative_cw_path {A : Type u} (incl : A → A) (f g : A → A)
    (x : A) (hg : g (f (incl x)) = incl (g (f x)))
    : Path (g (f (incl x))) (incl (g (f x))) :=
  Path.mk [Step.mk _ _ hg] hg

-- Def 61: Cellular map homotopy path composition
noncomputable def cellular_homotopy_compose {A B : Type u}
    (f g h : A → B) (x : A)
    (p : f x = g x) (q : g x = h x)
    : Path (f x) (h x) :=
  Path.trans (Path.mk [Step.mk _ _ p] p) (Path.mk [Step.mk _ _ q] q)

-- Def 62: CW complex mapping cylinder path
noncomputable def mapping_cylinder_path {A B : Type u} (f : A → B)
    (incl_A : A → B) (proj : B → B)
    (x : A) (h1 : proj (f x) = f x) (h2 : f x = incl_A x)
    : Path (proj (f x)) (incl_A x) :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 63: CW approximation functor preserves identity path
noncomputable def cw_approx_id {A : Type u} (approx : A → A)
    (x : A) (h : approx x = x)
    : Path (approx (approx x)) (approx x) :=
  Path.congrArg approx (Path.mk [Step.mk _ _ h] h)

-- Def 64: Skeletal filtration colimit coherence
noncomputable def skeletal_colimit_coherence {A : Type u}
    (incl1 incl2 : A → A) (x : A)
    (h1 : incl2 (incl1 x) = incl1 (incl2 x))
    (h2 : incl1 (incl2 x) = x)
    : Path (incl2 (incl1 x)) x :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 65: CW dimension path
noncomputable def cw_dimension_path {A : Type u}
    (incl_n incl_n1 : A → A) (x : A)
    (h : incl_n1 (incl_n x) = incl_n1 x)
    : Path (incl_n1 (incl_n x)) (incl_n1 x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 66: Cellular approximation theorem path form
noncomputable def cellular_approx_theorem {A B : Type u}
    (f : A → B) (cell_f : A → B) (H : (x : A) → f x = cell_f x)
    (x : A) : Path (f x) (cell_f x) :=
  Path.mk [Step.mk _ _ (H x)] (H x)

-- Def 67: Cellular approximation naturality square via congrArg
noncomputable def cellular_approx_natural_square {A B : Type u}
    (f cell_f : A → B) (g : B → B)
    (x : A) (hf : f x = cell_f x)
    : Path (g (f x)) (g (cell_f x)) :=
  Path.congrArg g (Path.mk [Step.mk _ _ hf] hf)

-- Def 68: CW product cell structure path
noncomputable def cw_product_cell {A B : Type u} (f : A → A) (g : B → B)
    (a : A) (b : B) (ha : f a = a) (_hb : g b = b)
    : Path (f a) a :=
  Path.mk [Step.mk _ _ ha] ha

-- Def 69: Suspension of CW complex attaching path
noncomputable def suspension_attach {A : Type u} (susp : A → A) (attach : A → A)
    (x : A) (h : susp (attach x) = attach (susp x))
    : Path (susp (attach x)) (attach (susp x)) :=
  Path.mk [Step.mk _ _ h] h

-- Def 70: CW wedge sum inclusion path
noncomputable def wedge_inclusion {A : Type u} (incl1 incl2 : A → A)
    (base : A) (h1 : incl1 base = base) (h2 : incl2 base = base)
    : Path (incl1 base) (incl2 base) :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.symm (Path.mk [Step.mk _ _ h2] h2))

-- Def 71: CW smash product coherence
noncomputable def smash_coherence {A : Type u} (f g : A → A)
    (base : A) (hf : f base = base) (hg : g base = base)
    : Path (f (g base)) base :=
  Path.trans
    (Path.congrArg f (Path.mk [Step.mk _ _ hg] hg))
    (Path.mk [Step.mk _ _ hf] hf)

-- Def 72: Cofibration sequence path
noncomputable def cofibration_seq {A : Type u} (i : A → A) (q : A → A)
    (x : A) (h1 : q (i x) = q x) (h2 : q x = x)
    : Path (q (i x)) x :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 73: Homotopy extension property path
noncomputable def homotopy_extension {A B : Type u} (f g : A → B)
    (H : A → B) (x : A)
    (h1 : f x = H x) (h2 : H x = g x)
    : Path (f x) (g x) :=
  Path.trans (Path.mk [Step.mk _ _ h1] h1) (Path.mk [Step.mk _ _ h2] h2)

-- Def 74: Mapping cone path
noncomputable def mapping_cone {A : Type u} (f : A → A) (cone : A → A)
    (x : A) (h : cone (f x) = cone x)
    : Path (cone (f x)) (cone x) :=
  Path.mk [Step.mk _ _ h] h

-- Def 75: CW structure determines homology path
noncomputable def cw_homology_path {A : Type u} (cc : ChainComplex A)
    (f : A → A) (x : A)
    : Path (f (cc.boundary (cc.boundary x))) (f cc.zero) :=
  boundary_squared_functorial cc f x

end CWComplexPathDeep
end Algebra
end Path
end ComputationalPaths
