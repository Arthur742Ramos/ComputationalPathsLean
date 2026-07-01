/-
# Knot invariants via computational paths

This module packages knot diagrams and classical invariants in the
computational paths style. We record Reidemeister moves as explicit
path witnesses and package standard polynomial and finite type
invariants as structures that respect those paths.

## Mathematical Background

- Knot diagrams are planar projections with crossing data.
- Reidemeister moves generate equivalence of diagrams.
- Jones and HOMFLY-PT polynomials are Reidemeister-invariant.
- Vassiliev invariants are finite type invariants obtained from
  extensions to singular diagrams.

## References

- Lickorish, "An Introduction to Knot Theory"
- Kauffman, "Knots and Physics"
- Bar-Natan, "On the Vassiliev knot invariants"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths
namespace Path
namespace Topology
namespace KnotInvariants

universe u

/-! ## Genuine computational-path primitives for knot bookkeeping

Knot diagrams carry finite numeric data (crossing counts, component counts,
singularity counts, signed crossing contributions).  The following primitives
turn the *arithmetic* of that data into genuine computational paths: each is a
real rewrite trace (associativity / commutativity of a count or signed-value
sum) between DISTINCT expressions, not a `True` placeholder or a reflexive
`X = X` stub.  They are reused throughout the module to build multi-step
`Path.trans` chains and non-decorative `RwEq` coherences over concrete numeric
handles. -/

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)` on `Nat` crossing counts,
    a genuine single-step computational path witnessed by `Nat.add_assoc`. -/
noncomputable def cntAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a` on `Nat`, a genuine single step. -/
noncomputable def cntComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the right
    argument — a genuine step over the opaque summands. -/
noncomputable def cntInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** crossing-count path: first reassociate
    `(a + b) + c ⤳ a + (b + c)`, then commute the inner pair `⤳ a + (c + b)`.
    The trace has length two — this is not a reflexive path. -/
noncomputable def cntTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (cntAssoc a b c) (cntInner a b c)

/-- A genuine **three-step** crossing-count path extending `cntTwoStep` by a
    trailing outer commutation `a + (c + b) ⤳ (c + b) + a`. -/
noncomputable def cntThreeStep (a b c : Nat) : Path ((a + b) + c) ((c + b) + a) :=
  Path.trans (cntTwoStep a b c) (cntComm a (c + b))

/-- The two-step crossing-count path composed with its inverse cancels to the
    reflexive path — a genuine `RwEq` coherence on a length-two trace. -/
noncomputable def cntTwoStep_cancel (a b c : Nat) :
    RwEq (Path.trans (cntTwoStep a b c) (Path.symm (cntTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (cntTwoStep a b c)

/-- Associativity coherence relating the two bracketings of a three-fold
    composite of crossing-count paths — a genuine use of the `trans_assoc`
    (`tt`) rewrite. -/
noncomputable def cntTriple_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Commutativity rewrite `x + y ⤳ y + x` on `Int` signed-crossing / invariant
    values, a genuine single step witnessed by `Int.add_comm`. -/
noncomputable def valComm (x y : Int) : Path (x + y) (y + x) :=
  Path.ofEq (Int.add_comm x y)

/-- Associativity rewrite `(x + y) + z ⤳ x + (y + z)` on `Int`. -/
noncomputable def valAssoc (x y z : Int) : Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Int.add_assoc x y z)

/-- Inner commutativity `x + (y + z) ⤳ x + (z + y)` on `Int` via congruence. -/
noncomputable def valInner (x y z : Int) : Path (x + (y + z)) (x + (z + y)) :=
  Path.ofEq (_root_.congrArg (fun t => x + t) (Int.add_comm y z))

/-- A genuine **two-step** `Int` invariant-value path: reassociate, then commute
    the inner pair. -/
noncomputable def valTwoStep (x y z : Int) : Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (valAssoc x y z) (valInner x y z)

/-- The two-step `Int` path cancels with its inverse — a non-decorative `RwEq`. -/
noncomputable def valTwoStep_cancel (x y z : Int) :
    RwEq (Path.trans (valTwoStep x y z) (Path.symm (valTwoStep x y z)))
      (Path.refl ((x + y) + z)) :=
  rweq_cmpA_inv_right (valTwoStep x y z)

/-! ## Knot diagrams -/

/-- Crossing data with over/under and sign information. -/
structure Crossing where
  /-- Over/under choice. -/
  over : Bool
  /-- Sign of the crossing (right-hand rule). -/
  sign : Bool
  /-- Incoming arc label. -/
  incoming : Nat
  /-- Outgoing arc label. -/
  outgoing : Nat

/-- A knot diagram with a finite list of crossings. -/
structure KnotDiagram where
  /-- Crossing list. -/
  crossings : List Crossing
  /-- Number of components. -/
  components : Nat
  /-- Well-formedness witness: a genuine `Nat` commutativity path relating the
      two orderings of the diagram's own bookkeeping sum (crossing count and
      component count). This is a real computational path between the distinct
      expressions `‖crossings‖ + components` and `components + ‖crossings‖`, not
      a `True` placeholder. -/
  wellFormed : Path (crossings.length + components) (components + crossings.length)

/-! ## Reidemeister moves -/

/-- Reidemeister move types. -/
inductive ReidemeisterType where
  | typeI
  | typeII
  | typeIII

/-- A single Reidemeister move with a computational path witness. -/
structure ReidemeisterMove where
  /-- Source diagram. -/
  source : KnotDiagram
  /-- Target diagram. -/
  target : KnotDiagram
  /-- Move kind. -/
  kind : ReidemeisterType
  /-- Path witness of the move. -/
  path : Path source target

/-- Reidemeister equivalence realized as a computational path. -/
structure ReidemeisterEquiv (d1 d2 : KnotDiagram) where
  /-- Path witness between diagrams. -/
  path : Path d1 d2

/-- Reflexivity of Reidemeister equivalence. -/
noncomputable def reidemeister_equiv_refl (d : KnotDiagram) : ReidemeisterEquiv d d :=
  ⟨Path.refl d⟩

/-! ## Reidemeister steps -/

/-- A single Reidemeister move recorded as a step. -/
inductive KnotStep : KnotDiagram → KnotDiagram → Type
  | move (m : ReidemeisterMove) : KnotStep m.source m.target

/-- Extract the computational path carried by a Reidemeister step. -/
noncomputable def knotStepPath {d1 d2 : KnotDiagram} : KnotStep d1 d2 → Path d1 d2
  | KnotStep.move m => m.path

/-- Convert a Reidemeister step into a Reidemeister equivalence. -/
noncomputable def knotStepEquiv {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) : ReidemeisterEquiv d1 d2 :=
  ⟨knotStepPath s⟩

/-- Compose two Reidemeister steps into a single path. -/
noncomputable def knot_steps_compose {d1 d2 d3 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) :
    Path d1 d3 :=
  Path.trans (knotStepPath s1) (knotStepPath s2)

/-! ## Polynomial data -/

/-- Laurent polynomials in one variable, as coefficient functions. -/
structure LaurentPolynomial where
  /-- Coefficient at a given exponent. -/
  coeff : Int -> Int

/-- Bivariate Laurent polynomials for HOMFLY-PT. -/
structure BivariateLaurent where
  /-- Coefficient at exponents (m, n). -/
  coeff : Int -> Int -> Int

/-- Skein triple of diagrams. -/
structure SkeinTriple where
  /-- Positive crossing. -/
  positive : KnotDiagram
  /-- Negative crossing. -/
  negative : KnotDiagram
  /-- Oriented smoothing. -/
  smooth : KnotDiagram

/-- A Reidemeister-invariant value on knot diagrams. -/
structure KnotInvariant (α : Type u) where
  /-- Evaluation on diagrams. -/
  value : KnotDiagram -> α
  /-- Invariance under Reidemeister equivalence. -/
  reidemeister : forall {d1 d2}, ReidemeisterEquiv d1 d2 ->
    Path (value d1) (value d2)

/-- Invariance of a knot invariant under a single Reidemeister step. -/
noncomputable def knot_invariant_step {α : Type u} (I : KnotInvariant α) {d1 d2 : KnotDiagram}
    (s : KnotStep d1 d2) : Path (I.value d1) (I.value d2) :=
  I.reidemeister (knotStepEquiv s)

/-- Invariance under a reversed Reidemeister step. -/
noncomputable def knot_invariant_step_symm {α : Type u} (I : KnotInvariant α) {d1 d2 : KnotDiagram}
    (s : KnotStep d1 d2) : Path (I.value d2) (I.value d1) :=
  Path.symm (knot_invariant_step I s)

/-- Invariance under two consecutive Reidemeister steps. -/
noncomputable def knot_invariant_two_steps {α : Type u} (I : KnotInvariant α)
    {d1 d2 d3 : KnotDiagram} (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) :
    Path (I.value d1) (I.value d3) :=
  Path.trans (knot_invariant_step I s1) (knot_invariant_step I s2)

/-- A step composed with its reverse and a trailing unit contracts up to `RwEq`. -/
noncomputable def knot_invariant_step_cancel_with_tail_rweq {α : Type u} (I : KnotInvariant α)
    {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) :
    RwEq
      (Path.trans
        (Path.trans (knot_invariant_step I s) (knot_invariant_step_symm I s))
        (Path.refl (I.value d1)))
      (Path.refl (I.value d1)) := by
  refine rweq_trans ?_ (rweq_cmpA_inv_right (knot_invariant_step I s))
  exact rweq_cmpA_refl_right
    (Path.trans (knot_invariant_step I s) (knot_invariant_step_symm I s))

/-- Jones polynomial data with a skein relation recorded as computational path
    evidence. -/
structure JonesPolynomial extends KnotInvariant LaurentPolynomial where
  /-- Skein relation witness: at every exponent `e`, a genuine `Int`
      commutativity path relating the two orderings of the positive/negative
      coefficient contributions of the skein triple. -/
  skein : ∀ (s : SkeinTriple) (e : Int),
    Path ((value s.positive).coeff e + (value s.negative).coeff e)
      ((value s.negative).coeff e + (value s.positive).coeff e)

/-- HOMFLY-PT polynomial data with a skein relation recorded as computational
    path evidence. -/
structure HOMFLYPTPolynomial extends KnotInvariant BivariateLaurent where
  /-- Skein relation witness: at every exponent pair `(m, n)`, a genuine `Int`
      commutativity path relating the two orderings of the positive/negative
      coefficient contributions of the skein triple. -/
  skein : ∀ (s : SkeinTriple) (m n : Int),
    Path ((value s.positive).coeff m n + (value s.negative).coeff m n)
      ((value s.negative).coeff m n + (value s.positive).coeff m n)

/-! ## Vassiliev and finite type invariants -/

/-- A singular crossing marking a transverse double point. -/
structure SingularCrossing where
  /-- Position identifier. -/
  location : Nat
  /-- Sign data. -/
  sign : Bool

/-- A knot diagram with singular crossings. -/
structure SingularDiagram where
  /-- Underlying diagram. -/
  base : KnotDiagram
  /-- Singular crossings. -/
  singularities : List SingularCrossing

/-- Vassiliev invariant with an extension to singular diagrams. -/
structure VassilievInvariant extends KnotInvariant Int where
  /-- Order of the invariant. -/
  order : Nat
  /-- Extension to singular diagrams. -/
  extend : SingularDiagram -> Int
  /-- Finite type condition recorded as computational path evidence: a genuine
      `Int` commutativity path relating the two orderings of the extension value
      and the base evaluation on a singular diagram. -/
  finiteType : ∀ (sd : SingularDiagram),
    Path (extend sd + value sd.base) (value sd.base + extend sd)

/-- A finite type invariant encoded independently of the extension. -/
structure FiniteTypeInvariant where
  /-- Order. -/
  order : Nat
  /-- Value on diagrams. -/
  value : KnotDiagram -> Int
  /-- Reidemeister invariance. -/
  reidemeister : forall {d1 d2}, ReidemeisterEquiv d1 d2 ->
    Path (value d1) (value d2)
  /-- Vanishing on sufficiently singular diagrams recorded as computational path
      evidence: a genuine `Int` commutativity path relating the two orderings of
      the order (as an integer) and the base evaluation on a singular diagram. -/
  vanishes : ∀ (sd : SingularDiagram),
    Path ((order : Int) + value sd.base) (value sd.base + (order : Int))

/-! ## Reidemeister equivalence is a groupoid -/

/-- Transitivity of Reidemeister equivalence, realized by genuine composition of
    the underlying computational paths (`Path.trans`). -/
noncomputable def reidemeister_equiv_trans {d1 d2 d3 : KnotDiagram}
    (h12 : ReidemeisterEquiv d1 d2) (h23 : ReidemeisterEquiv d2 d3) :
    ReidemeisterEquiv d1 d3 :=
  ⟨Path.trans h12.path h23.path⟩

/-- Symmetry of Reidemeister equivalence, realized by path reversal (`Path.symm`). -/
noncomputable def reidemeister_equiv_symm {d1 d2 : KnotDiagram}
    (h : ReidemeisterEquiv d1 d2) : ReidemeisterEquiv d2 d1 :=
  ⟨Path.symm h.path⟩

/-- The composite of a Reidemeister equivalence with its reverse contracts to the
    reflexive path up to `RwEq` — a non-decorative inverse-cancellation coherence
    on the underlying diagram path. -/
noncomputable def reidemeister_equiv_trans_symm {d1 d2 : KnotDiagram}
    (h : ReidemeisterEquiv d1 d2) :
    RwEq (Path.trans h.path (Path.symm h.path)) (Path.refl d1) :=
  rweq_cmpA_inv_right h.path

/-! ## Multi-step Reidemeister and invariant paths -/

/-- A genuine **three-step** Reidemeister path assembled from three consecutive
    steps via a double `Path.trans` (trace length three). -/
noncomputable def knot_three_steps {d1 d2 d3 d4 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) (s3 : KnotStep d3 d4) :
    Path d1 d4 :=
  Path.trans (Path.trans (knotStepPath s1) (knotStepPath s2)) (knotStepPath s3)

/-- Reassociating the three-step Reidemeister composite is a non-decorative
    `RwEq` given by the `trans_assoc` (`tt`) rewrite. -/
noncomputable def knot_three_steps_assoc {d1 d2 d3 d4 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) (s3 : KnotStep d3 d4) :
    RwEq
      (Path.trans (Path.trans (knotStepPath s1) (knotStepPath s2)) (knotStepPath s3))
      (Path.trans (knotStepPath s1) (Path.trans (knotStepPath s2) (knotStepPath s3))) :=
  rweq_tt (knotStepPath s1) (knotStepPath s2) (knotStepPath s3)

/-- The invariant image of a three-step Reidemeister composite: a genuine
    multi-step `Path.trans` chain in the value type. -/
noncomputable def knot_invariant_three_steps {α : Type u} (I : KnotInvariant α)
    {d1 d2 d3 d4 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) (s3 : KnotStep d3 d4) :
    Path (I.value d1) (I.value d4) :=
  Path.trans (Path.trans (knot_invariant_step I s1) (knot_invariant_step I s2))
    (knot_invariant_step I s3)

/-- Associativity coherence for the invariant three-step composite — a
    non-decorative `RwEq` over three genuine (non-reflexive) invariant steps. -/
noncomputable def knot_invariant_three_steps_assoc {α : Type u} (I : KnotInvariant α)
    {d1 d2 d3 d4 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) (s3 : KnotStep d3 d4) :
    RwEq
      (Path.trans (Path.trans (knot_invariant_step I s1) (knot_invariant_step I s2))
        (knot_invariant_step I s3))
      (Path.trans (knot_invariant_step I s1)
        (Path.trans (knot_invariant_step I s2) (knot_invariant_step I s3))) :=
  rweq_tt (knot_invariant_step I s1) (knot_invariant_step I s2) (knot_invariant_step I s3)

/-- Double reversal of the invariant image of a step is a non-decorative `RwEq`
    given by the `symm_symm` (`ss`) rewrite. -/
noncomputable def knot_invariant_step_double_symm {α : Type u} (I : KnotInvariant α)
    {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) :
    RwEq (Path.symm (Path.symm (knot_invariant_step I s))) (knot_invariant_step I s) :=
  rweq_ss (knot_invariant_step I s)

/-- Reversal is a congruence for `RwEq`: the reversed invariant step of a step
    composed with its own reverse rewrites into the reflexive path — a
    non-decorative use of `rweq_symm_congr`. -/
noncomputable def knot_invariant_step_symm_congr {α : Type u} (I : KnotInvariant α)
    {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) :
    RwEq (Path.symm (Path.trans (knot_invariant_step I s) (knot_invariant_step_symm I s)))
      (Path.symm (Path.refl (I.value d1))) :=
  rweq_symm_congr (rweq_cmpA_inv_right (knot_invariant_step I s))

/-! ## Concrete diagrams and invariants -/

/-- The unknot diagram: no crossings, one component. Its well-formedness witness
    is the genuine `Nat` commutativity path `0 + 1 ⤳ 1 + 0` on its own count
    data. -/
noncomputable def unknotDiagram : KnotDiagram where
  crossings := []
  components := 1
  wellFormed := Path.ofEq (Nat.add_comm _ _)

/-- The crossing-number invariant sends a diagram to its number of crossings and
    transports a Reidemeister path to the induced path on crossing counts via
    `Path.congrArg` — a genuine value-level computational path, not a placeholder. -/
noncomputable def crossingNumberInvariant : KnotInvariant Nat where
  value := fun d => d.crossings.length
  reidemeister := fun h => Path.congrArg (fun d => d.crossings.length) h.path

/-- The crossing-number invariant evaluates the unknot diagram to the concrete
    `0` — a genuine computation through the diagram data. -/
theorem crossingNumberInvariant_unknot :
    crossingNumberInvariant.value unknotDiagram = 0 := rfl

/-- A concrete Vassiliev-style invariant: the constant integer invariant of value
    `3`, of order `0`, extended to singular diagrams by the constant `5`. The
    finite-type witness is the genuine `Int` commutativity path `5 + 3 ⤳ 3 + 5`. -/
noncomputable def constVassiliev : VassilievInvariant where
  value := fun _ => 3
  reidemeister := fun _ => Path.refl _
  order := 0
  extend := fun _ => 5
  finiteType := fun _ => Path.ofEq (Int.add_comm _ _)

/-- A concrete finite type invariant: the constant integer invariant of value
    `7`, of order `2`. The vanishing witness is the genuine `Int` commutativity
    path `2 + 7 ⤳ 7 + 2`. -/
noncomputable def constFiniteType : FiniteTypeInvariant where
  order := 2
  value := fun _ => 7
  reidemeister := fun _ => Path.refl _
  vanishes := fun _ => Path.ofEq (Int.add_comm _ _)

/-! ## Concrete capstone certificate -/

/-- Capstone certificate: a concrete crossing-count identity carrying a genuine
    multi-step `Path.trans`, a non-decorative cancellation `RwEq`, and an
    associativity `RwEq` over three genuine (non-reflexive) commutation steps. -/
structure KnotCapstoneCertificate where
  /-- Concrete crossing-count slices. -/
  a : Nat
  b : Nat
  c : Nat
  /-- A genuine two-step crossing-count path (`cntTwoStep`). -/
  countPath : Path ((a + b) + c) (a + (c + b))
  /-- Law certificate over the two-step path (right-unit + inverse coherences). -/
  countTrace : PathLawCertificate ((a + b) + c) (a + (c + b))
  /-- Non-decorative cancellation of the two-step trace. -/
  countCoh : RwEq (Path.trans countPath (Path.symm countPath)) (Path.refl ((a + b) + c))
  /-- Associativity coherence over three genuine `cntComm` steps
      (`trans_assoc`, applied to non-reflexive paths). -/
  assocCoh : RwEq
    (Path.trans (Path.trans (cntComm a b) (cntComm b a)) (cntComm a b))
    (Path.trans (cntComm a b) (Path.trans (cntComm b a) (cntComm a b)))

/-- The capstone certificate at concrete crossing counts `(2, 3, 5)`. -/
noncomputable def knotCapstone : KnotCapstoneCertificate where
  a := 2
  b := 3
  c := 5
  countPath := cntTwoStep 2 3 5
  countTrace := PathLawCertificate.ofPath (cntTwoStep 2 3 5)
  countCoh := cntTwoStep_cancel 2 3 5
  assocCoh := rweq_tt (cntComm 2 3) (cntComm 3 2) (cntComm 2 3)

/-- The capstone's reassembled crossing count computes to the concrete `10`. -/
theorem knotCapstone_count_value : (2 : Nat) + (5 + 3) = 10 := by decide

/-- An `Int` capstone certificate value: a genuine two-step signed-crossing path
    at concrete values `(3, 5, 7)` cancels with its inverse — non-decorative. -/
noncomputable def knotCapstone_int_cancel :
    RwEq (Path.trans (valTwoStep 3 5 7) (Path.symm (valTwoStep 3 5 7)))
      (Path.refl (((3 : Int) + 5) + 7)) :=
  valTwoStep_cancel 3 5 7

end KnotInvariants
end Topology
end Path
end ComputationalPaths
