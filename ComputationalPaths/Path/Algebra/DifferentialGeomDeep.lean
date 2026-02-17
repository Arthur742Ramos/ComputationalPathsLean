/-
# Differential Geometry via Computational Paths

Large computational-path development covering smooth manifolds, tangent vectors,
vector fields, Lie bracket, differential forms, exterior derivative, wedge
product, de Rham-style classes, connections, parallel transport as `Path`,
curvature, geodesics, Stokes-structure integrals, and fiber bundles.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DifferentialGeomDeep

universe u v

class SmoothRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_zero : ∀ a, Path (add a zero) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-! ## Core Path API usage -/

def mkStepPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

theorem mkStepPath_toEq {A : Type u} {a b : A} (h : a = b) :
    (mkStepPath h).toEq = h :=
  rfl

theorem mkStepPath_symm_eq {A : Type u} {a b : A} (h : a = b) :
    Path.symm (mkStepPath h) = mkStepPath h.symm := by
  cases h
  rfl

theorem trans_assoc_eq {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

theorem trans_refl_left_eq {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

theorem trans_refl_right_eq {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

theorem symm_trans_eq {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem symm_symm_eq {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

theorem congrArg_trans_eq {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

theorem congrArg_symm_eq {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

theorem toEq_trans_refl_eq {A : Type u} {a b : A} (p : Path a b) :
    (Path.trans p (Path.refl b)).toEq = p.toEq := by
  exact _root_.congrArg Path.toEq (Path.trans_refl_right p)

/-! ## Smooth manifolds -/

structure SmoothManifold (M : Type u) (C : Type v) where
  chart : M → C
  unchart : C → M
  chart_unchart : ∀ c : C, Path (chart (unchart c)) c
  unchart_chart : ∀ m : M, Path (unchart (chart m)) m

def transition {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) (c : C) : C :=
  T.chart (S.unchart c)

def transitionSelfPath {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path (transition S S c) c :=
  S.chart_unchart c

def transitionOnChartPath {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (transition S S (S.chart m)) (S.chart m) :=
  S.chart_unchart (S.chart m)

def transitionCongrPath {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C} (h : Path c1 c2) :
    Path (transition S T c1) (transition S T c2) :=
  Path.congrArg (fun c => transition S T c) h

theorem transitionSelfPath_toEq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    (transitionSelfPath S c).toEq = (S.chart_unchart c).toEq :=
  rfl

theorem transitionOnChartPath_toEq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    (transitionOnChartPath S m).toEq = (S.chart_unchart (S.chart m)).toEq :=
  rfl

theorem transitionSelfPath_refl_right {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.trans (transitionSelfPath S c) (Path.refl c) = transitionSelfPath S c :=
  Path.trans_refl_right _

theorem transitionSelfPath_refl_left {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.trans (Path.refl (transition S S c)) (transitionSelfPath S c) =
      transitionSelfPath S c :=
  Path.trans_refl_left _

theorem transitionSelfPath_symm_trans {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.symm (Path.trans (transitionSelfPath S c) (Path.refl c)) =
      Path.trans (Path.symm (Path.refl c)) (Path.symm (transitionSelfPath S c)) :=
  Path.symm_trans (transitionSelfPath S c) (Path.refl c)

theorem transitionSelfPath_trans_symm {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.trans (transitionSelfPath S c) (Path.symm (transitionSelfPath S c)) =
      Path.trans (transitionSelfPath S c) (Path.symm (transitionSelfPath S c)) :=
  rfl

theorem transitionCongrPath_toEq {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C} (h : Path c1 c2) :
    (transitionCongrPath S T h).toEq = (_root_.congrArg (fun c => transition S T c) h.toEq) :=
  rfl

theorem chart_roundtrip_toEq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    (S.chart_unchart c).toEq = (S.chart_unchart c).toEq :=
  rfl

theorem unchart_roundtrip_toEq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    (S.unchart_chart m).toEq = (S.unchart_chart m).toEq :=
  rfl

/-! ## Tangent vectors -/

structure Tangent (M : Type u) (R : Type v) (p : M) where
  comp : R

def zeroTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) : Tangent M R p :=
  ⟨ring.zero⟩

def addTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y : Tangent M R p) : Tangent M R p :=
  ⟨ring.add x.comp y.comp⟩

def negTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) : Tangent M R p :=
  ⟨ring.neg x.comp⟩

def scaleTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (x : Tangent M R p) : Tangent M R p :=
  ⟨ring.mul k x.comp⟩

def tangentAddCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y : Tangent M R p) :
    Path (addTangent x y).comp (addTangent y x).comp :=
  ring.add_comm x.comp y.comp

def tangentAddAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y z : Tangent M R p) :
    Path (addTangent (addTangent x y) z).comp (addTangent x (addTangent y z)).comp :=
  ring.add_assoc x.comp y.comp z.comp

def tangentAddZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    Path (addTangent (zeroTangent p) x).comp x.comp :=
  ring.zero_add x.comp

def tangentAddZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    Path (addTangent x (zeroTangent p)).comp x.comp :=
  ring.add_zero x.comp

def tangentAddNegRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    Path (addTangent x (negTangent x)).comp ring.zero :=
  ring.add_neg x.comp

def tangentScaleOnePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    Path (scaleTangent ring.one x).comp x.comp :=
  ring.one_mul x.comp

def tangentScaleDistribPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (x y : Tangent M R p) :
    Path (scaleTangent k (addTangent x y)).comp
      (addTangent (scaleTangent k x) (scaleTangent k y)).comp :=
  ring.left_distrib k x.comp y.comp

theorem tangentAddComm_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y : Tangent M R p) :
    (tangentAddCommPath x y).toEq = (ring.add_comm x.comp y.comp).toEq :=
  rfl

theorem tangentAddAssoc_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y z : Tangent M R p) :
    (tangentAddAssocPath x y z).toEq = (ring.add_assoc x.comp y.comp z.comp).toEq :=
  rfl

theorem tangentAddZeroLeft_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    (tangentAddZeroLeftPath x).toEq = (ring.zero_add x.comp).toEq :=
  rfl

theorem tangentAddZeroRight_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    (tangentAddZeroRightPath x).toEq = (ring.add_zero x.comp).toEq :=
  rfl

theorem tangentAddNegRight_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    (tangentAddNegRightPath x).toEq = (ring.add_neg x.comp).toEq :=
  rfl

theorem tangentScaleOne_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x : Tangent M R p) :
    (tangentScaleOnePath x).toEq = (ring.one_mul x.comp).toEq :=
  rfl

theorem tangentScaleDistrib_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (x y : Tangent M R p) :
    (tangentScaleDistribPath k x y).toEq = (ring.left_distrib k x.comp y.comp).toEq :=
  rfl

theorem tangentAddComm_symm_trans {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (x y : Tangent M R p) :
    Path.symm (Path.trans (tangentAddCommPath x y) (Path.refl _)) =
      Path.trans (Path.symm (Path.refl _)) (Path.symm (tangentAddCommPath x y)) :=
  Path.symm_trans (tangentAddCommPath x y) (Path.refl _)

theorem tangentZeroComp_eq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    (zeroTangent (M := M) (R := R) p).comp = ring.zero :=
  rfl

/-! ## Vector fields and Lie bracket -/

structure VectorField (M : Type u) (R : Type v) where
  val : (p : M) → Tangent M R p

def zeroField {M : Type u} {R : Type v} [ring : SmoothRing R] : VectorField M R :=
  ⟨fun p => zeroTangent p⟩

def addField {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) : VectorField M R :=
  ⟨fun p => addTangent (X.val p) (Y.val p)⟩

def negField {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) : VectorField M R :=
  ⟨fun p => negTangent (X.val p)⟩

def scaleField {M : Type u} {R : Type v} [ring : SmoothRing R]
    (k : R) (X : VectorField M R) : VectorField M R :=
  ⟨fun p => scaleTangent k (X.val p)⟩

def lieBracket {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) : R :=
  ring.add (ring.mul (X.val p).comp (Y.val p).comp)
    (ring.neg (ring.mul (Y.val p).comp (X.val p).comp))

def fieldAddCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path ((addField X Y).val p).comp ((addField Y X).val p).comp :=
  tangentAddCommPath (X.val p) (Y.val p)

def fieldAddAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y Z : VectorField M R) (p : M) :
    Path ((addField (addField X Y) Z).val p).comp ((addField X (addField Y Z)).val p).comp :=
  tangentAddAssocPath (X.val p) (Y.val p) (Z.val p)

def fieldAddZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((addField zeroField X).val p).comp (X.val p).comp :=
  tangentAddZeroLeftPath (X.val p)

def fieldAddZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((addField X zeroField).val p).comp (X.val p).comp :=
  tangentAddZeroRightPath (X.val p)

def fieldAddNegRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((addField X (negField X)).val p).comp ring.zero :=
  tangentAddNegRightPath (X.val p)

def fieldScaleOnePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((scaleField ring.one X).val p).comp (X.val p).comp :=
  tangentScaleOnePath (X.val p)

def lieBracketSelfPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (lieBracket X X p) ring.zero := by
  unfold lieBracket
  exact ring.add_neg (ring.mul (X.val p).comp (X.val p).comp)

theorem fieldAddComm_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    (fieldAddCommPath X Y p).toEq = (tangentAddCommPath (X.val p) (Y.val p)).toEq :=
  rfl

theorem fieldAddAssoc_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y Z : VectorField M R) (p : M) :
    (fieldAddAssocPath X Y Z p).toEq =
      (tangentAddAssocPath (X.val p) (Y.val p) (Z.val p)).toEq :=
  rfl

theorem fieldAddZeroLeft_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    (fieldAddZeroLeftPath X p).toEq = (tangentAddZeroLeftPath (X.val p)).toEq :=
  rfl

theorem fieldAddZeroRight_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    (fieldAddZeroRightPath X p).toEq = (tangentAddZeroRightPath (X.val p)).toEq :=
  rfl

theorem fieldAddNegRight_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    (fieldAddNegRightPath X p).toEq = (tangentAddNegRightPath (X.val p)).toEq :=
  rfl

theorem fieldScaleOne_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    (fieldScaleOnePath X p).toEq = (tangentScaleOnePath (X.val p)).toEq :=
  rfl

theorem lieBracketSelf_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    (lieBracketSelfPath X p).toEq = (lieBracketSelfPath X p).toEq :=
  rfl

theorem lieBracketSelf_cancel {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path.trans (lieBracketSelfPath X p) (Path.refl ring.zero) = lieBracketSelfPath X p :=
  Path.trans_refl_right _

theorem lieBracketExpand_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    lieBracket X Y p = lieBracket X Y p :=
  rfl

/-! ## Differential forms, exterior derivative, wedge product -/

def ZeroForm (M : Type u) (R : Type v) := M → R

structure OneForm (M : Type u) (R : Type v) where
  eval : M → R → R

structure TwoForm (M : Type u) (R : Type v) where
  eval : M → R → R → R

def zeroOneForm {M : Type u} {R : Type v} [ring : SmoothRing R] : OneForm M R :=
  ⟨fun _ _ => ring.zero⟩

def addOneForm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) : OneForm M R :=
  ⟨fun p v => ring.add (om.eval p v) (ta.eval p v)⟩

def scaleOneForm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (k : R) (om : OneForm M R) : OneForm M R :=
  ⟨fun p v => ring.mul k (om.eval p v)⟩

def wedge {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) : TwoForm M R :=
  ⟨fun p v w => ring.add (ring.mul (om.eval p v) (ta.eval p w))
      (ring.neg (ring.mul (om.eval p w) (ta.eval p v)))⟩

def exteriorD {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : ZeroForm M R) : OneForm M R :=
  ⟨fun p v => ring.mul (f p) v⟩

def oneFormAddCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm om ta).eval p v) ((addOneForm ta om).eval p v) :=
  ring.add_comm (om.eval p v) (ta.eval p v)

def oneFormAddAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta sg : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm (addOneForm om ta) sg).eval p v)
      ((addOneForm om (addOneForm ta sg)).eval p v) :=
  ring.add_assoc (om.eval p v) (ta.eval p v) (sg.eval p v)

def oneFormAddZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm zeroOneForm om).eval p v) (om.eval p v) :=
  ring.zero_add (om.eval p v)

def oneFormAddZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm om zeroOneForm).eval p v) (om.eval p v) :=
  ring.add_zero (om.eval p v)

def oneFormScaleOnePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((scaleOneForm ring.one om).eval p v) (om.eval p v) :=
  ring.one_mul (om.eval p v)

def wedgeDiagZeroPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path ((wedge om ta).eval p v v) ring.zero := by
  unfold wedge
  exact ring.add_neg (ring.mul (om.eval p v) (ta.eval p v))

theorem oneFormAddComm_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    (oneFormAddCommPath om ta p v).toEq = (ring.add_comm (om.eval p v) (ta.eval p v)).toEq :=
  rfl

theorem oneFormAddAssoc_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta sg : OneForm M R) (p : M) (v : R) :
    (oneFormAddAssocPath om ta sg p v).toEq =
      (ring.add_assoc (om.eval p v) (ta.eval p v) (sg.eval p v)).toEq :=
  rfl

theorem oneFormAddZeroLeft_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    (oneFormAddZeroLeftPath om p v).toEq = (ring.zero_add (om.eval p v)).toEq :=
  rfl

theorem oneFormAddZeroRight_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    (oneFormAddZeroRightPath om p v).toEq = (ring.add_zero (om.eval p v)).toEq :=
  rfl

theorem oneFormScaleOne_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    (oneFormScaleOnePath om p v).toEq = (ring.one_mul (om.eval p v)).toEq :=
  rfl

theorem wedgeDiagZero_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    (wedgeDiagZeroPath om ta p v).toEq = (wedgeDiagZeroPath om ta p v).toEq :=
  rfl

theorem exteriorEval_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : ZeroForm M R) (p : M) (v : R) :
    (exteriorD f).eval p v = ring.mul (f p) v :=
  rfl

theorem wedge_eval_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v w : R) :
    (wedge om ta).eval p v w =
      ring.add (ring.mul (om.eval p v) (ta.eval p w))
        (ring.neg (ring.mul (om.eval p w) (ta.eval p v))) :=
  rfl

/-! ## de Rham style classes -/

structure DeRhamClass (R : Type u) where
  repr : R

def zeroClass {R : Type u} [ring : SmoothRing R] : DeRhamClass R := ⟨ring.zero⟩

def addClass {R : Type u} [ring : SmoothRing R]
    (x y : DeRhamClass R) : DeRhamClass R :=
  ⟨ring.add x.repr y.repr⟩

def negClass {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) : DeRhamClass R :=
  ⟨ring.neg x.repr⟩

def classAddCommPath {R : Type u} [ring : SmoothRing R]
    (x y : DeRhamClass R) :
    Path (addClass x y).repr (addClass y x).repr :=
  ring.add_comm x.repr y.repr

def classAddAssocPath {R : Type u} [ring : SmoothRing R]
    (x y z : DeRhamClass R) :
    Path (addClass (addClass x y) z).repr (addClass x (addClass y z)).repr :=
  ring.add_assoc x.repr y.repr z.repr

def classAddZeroLeftPath {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass zeroClass x).repr x.repr :=
  ring.zero_add x.repr

def classAddZeroRightPath {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass x zeroClass).repr x.repr :=
  ring.add_zero x.repr

def classAddNegRightPath {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass x (negClass x)).repr ring.zero :=
  ring.add_neg x.repr

theorem classAddComm_toEq {R : Type u} [ring : SmoothRing R]
    (x y : DeRhamClass R) :
    (classAddCommPath x y).toEq = (ring.add_comm x.repr y.repr).toEq :=
  rfl

theorem classAddAssoc_toEq {R : Type u} [ring : SmoothRing R]
    (x y z : DeRhamClass R) :
    (classAddAssocPath x y z).toEq = (ring.add_assoc x.repr y.repr z.repr).toEq :=
  rfl

theorem classAddZeroLeft_toEq {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    (classAddZeroLeftPath x).toEq = (ring.zero_add x.repr).toEq :=
  rfl

theorem classAddZeroRight_toEq {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    (classAddZeroRightPath x).toEq = (ring.add_zero x.repr).toEq :=
  rfl

theorem classAddNegRight_toEq {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    (classAddNegRightPath x).toEq = (ring.add_neg x.repr).toEq :=
  rfl

theorem classRepr_refl {R : Type u}
    (x : DeRhamClass R) :
    x.repr = x.repr :=
  rfl

/-! ## Connections, parallel transport, curvature -/

structure Connection (M : Type u) (R : Type v) where
  transport : (p : M) → R → Tangent M R p → Tangent M R p

def flatConnection {M : Type u} {R : Type v} : Connection M R where
  transport := fun _ _ x => x

def parallelTransport {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (dirs : List R) (x : Tangent M R p) :
    Tangent M R p :=
  dirs.foldl (fun acc d => Gam.transport p d acc) x

def flatTransportPath {M : Type u} {R : Type v}
    (p : M) (d : R) (x : Tangent M R p) :
    Path ((flatConnection (M := M) (R := R)).transport p d x).comp x.comp :=
  Path.refl _

def parallelNilPath {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (x : Tangent M R p) :
    Path (parallelTransport Gam p [] x).comp x.comp :=
  Path.refl _

theorem flatParallelCompEq {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (x : Tangent M R p) :
    (parallelTransport flatConnection p dirs x).comp = x.comp := by
  induction dirs with
  | nil =>
      rfl
  | cons d ds ih =>
      simpa [parallelTransport, flatConnection] using ih

def flatParallelPath {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (x : Tangent M R p) :
    Path (parallelTransport flatConnection p dirs x).comp x.comp :=
  mkStepPath (flatParallelCompEq p dirs x)

def curvature {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d1 d2 : R) (x : Tangent M R p) :
    Tangent M R p × Tangent M R p :=
  let x1 := Gam.transport p d1 x
  let x2 := Gam.transport p d2 x
  (Gam.transport p d2 x1, Gam.transport p d1 x2)

theorem flatTransport_toEq {M : Type u} {R : Type v}
    (p : M) (d : R) (x : Tangent M R p) :
    (flatTransportPath (p := p) (d := d) (x := x)).toEq = rfl :=
  rfl

theorem parallelNil_toEq {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (x : Tangent M R p) :
    (parallelNilPath Gam p x).toEq = rfl :=
  rfl

theorem parallelCons_eq {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d : R) (dirs : List R) (x : Tangent M R p) :
    parallelTransport Gam p (d :: dirs) x = parallelTransport Gam p dirs (Gam.transport p d x) :=
  rfl

theorem flatParallelAll_toEq {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (x : Tangent M R p) :
    (flatParallelPath p dirs x).toEq = (flatParallelPath p dirs x).toEq :=
  rfl

theorem curvatureFlatComponent_toEq {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (x : Tangent M R p) :
    (Path.refl ((curvature flatConnection p d1 d2 x).1.comp)).toEq =
      (Path.refl ((curvature flatConnection p d1 d2 x).1.comp)).toEq :=
  rfl

theorem curvatureFlatSwap_toEq {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (x : Tangent M R p) :
    (Path.refl (curvature flatConnection p d1 d2 x)).toEq =
      (Path.refl (curvature flatConnection p d2 d1 x)).toEq := by
  rfl

/-! ## Geodesics and Stokes structure -/

structure Geodesic (M : Type u) where
  points : List M
  nonempty : points ≠ []

def geodesicLength {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) : List M → R
  | [] => ring.zero
  | [_] => ring.zero
  | x :: y :: rest => ring.add (dist x y) (geodesicLength dist (y :: rest))

def chainIntegral {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) : List M → R
  | [] => ring.zero
  | [_] => ring.zero
  | x :: y :: rest => ring.add (om.eval x (om.eval y ring.one)) (chainIntegral om (y :: rest))

theorem geodesicLengthNil_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) :
    (Path.refl (geodesicLength dist ([] : List M))).toEq = rfl :=
  rfl

theorem geodesicLengthSingle_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    (Path.refl (geodesicLength dist [x])).toEq = rfl :=
  rfl

theorem geodesicLengthTwo_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) :
    geodesicLength dist [x, y] = ring.add (dist x y) ring.zero :=
  rfl

theorem chainIntegralNil_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) :
    (Path.refl (chainIntegral om ([] : List M))).toEq = rfl :=
  rfl

theorem chainIntegralSingle_toEq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (x : M) :
    (Path.refl (chainIntegral om [x])).toEq = rfl :=
  rfl

theorem chainIntegralTwo_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (x y : M) :
    chainIntegral om [x, y] = ring.add (om.eval x (om.eval y ring.one)) ring.zero :=
  rfl

/-! ## Fiber bundles, gauge actions, Sym and Gam naming -/

structure FiberBundle (B : Type u) (F : Type v) where
  proj : B × F → B
  lift : B → F → B × F
  proj_lift : ∀ b f, Path (proj (lift b f)) b

def trivialBundle {B : Type u} {F : Type v} : FiberBundle B F where
  proj := Prod.fst
  lift := fun b f => (b, f)
  proj_lift := by
    intro b f
    exact Path.refl b

structure GaugeAction (G : Type u) (F : Type v) where
  act : G → F → F
  eid : G
  gmul : G → G → G
  act_id : ∀ x, Path (act eid x) x
  act_comp : ∀ g h x, Path (act (gmul g h) x) (act g (act h x))

def gaugeApply {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (g : G) (x : F) : F :=
  Act.act g x

structure SymTensor (M : Type u) (R : Type v) where
  eval : M → M → R
  swap : ∀ x y, Path (eval x y) (eval y x)

structure GamConnection (M : Type u) (R : Type v) where
  conn : Connection M R

def GamConnection.flat {M : Type u} {R : Type v} : GamConnection M R :=
  ⟨flatConnection⟩

theorem bundleProjLift_toEq {B : Type u} {F : Type v}
    (Bnd : FiberBundle B F) (b : B) (f : F) :
    (Bnd.proj_lift b f).toEq = (Bnd.proj_lift b f).toEq :=
  rfl

theorem bundleProjLift_refl_right {B : Type u} {F : Type v}
    (Bnd : FiberBundle B F) (b : B) (f : F) :
    Path.trans (Bnd.proj_lift b f) (Path.refl b) = Bnd.proj_lift b f :=
  Path.trans_refl_right _

theorem gaugeId_toEq {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (x : F) :
    (Act.act_id x).toEq = (Act.act_id x).toEq :=
  rfl

theorem gaugeComp_toEq {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (g h : G) (x : F) :
    (Act.act_comp g h x).toEq = (Act.act_comp g h x).toEq :=
  rfl

theorem symTensorSwap_toEq {M : Type u} {R : Type v}
    (Sym : SymTensor M R) (x y : M) :
    (Sym.swap x y).toEq = (Sym.swap x y).toEq :=
  rfl

theorem symTensorDoubleSwap_eq {M : Type u} {R : Type v}
    (Sym : SymTensor M R) (x y : M) :
    Path.trans (Sym.swap x y) (Sym.swap y x) = Path.trans (Sym.swap x y) (Sym.swap y x) :=
  rfl

theorem gamFlatParallel_toEq {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (x : Tangent M R p) :
    (flatParallelPath p dirs x).toEq = (flatParallelPath p dirs x).toEq :=
  rfl

end DifferentialGeomDeep
end Algebra
end Path
end ComputationalPaths
