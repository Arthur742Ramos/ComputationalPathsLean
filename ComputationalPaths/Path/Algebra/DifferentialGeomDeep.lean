/-
# Differential Geometry via Computational Paths

A large, self-contained Lean 4 development sketching differential geometry with
computational paths.  The file covers:
- smooth manifolds and chart transitions
- tangent vectors and vector fields
- Lie bracket (toy algebraic model)
- differential forms and exterior derivative
- connections, parallel transport as `Path`, curvature
- geodesics and simple metric identities

The module explicitly uses:
`Path.refl`, `Path.trans`, `Path.symm`, `Path.congrArg`, `Path.toEq`,
`Path.mk`, and `Step.mk`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DifferentialGeomDeep

universe u v w

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

@[simp] theorem mkStepPath_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (mkStepPath h) = h :=
  rfl

@[simp] theorem mkStepPath_steps {A : Type u} {a b : A} (h : a = b) :
    (mkStepPath h).steps = [Step.mk a b h] :=
  rfl

theorem mkStepPath_symm {A : Type u} {a b : A} (h : a = b) :
    Path.symm (mkStepPath h) = mkStepPath h.symm := by
  cases h
  rfl

theorem path_mk_toEq {A : Type u} {a b : A} (steps : List (Step A)) (h : a = b) :
    Path.toEq (Path.mk steps h) = h :=
  rfl

theorem step_mk_src {A : Type u} (a b : A) (h : a = b) :
    (Step.mk a b h).src = a :=
  rfl

theorem step_mk_tgt {A : Type u} (a b : A) (h : a = b) :
    (Step.mk a b h).tgt = b :=
  rfl

theorem trans_assoc_use {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

theorem trans_refl_left_use {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

theorem trans_refl_right_use {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

theorem symm_trans_use {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem symm_symm_use {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

theorem congrArg_trans_use {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

theorem congrArg_symm_use {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

theorem toEq_trans_refl {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.trans p (Path.refl b)) = Path.toEq p := by
  exact _root_.congrArg Path.toEq (Path.trans_refl_right p)

theorem toEq_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.symm (Path.symm p)) = Path.toEq p := by
  exact _root_.congrArg Path.toEq (Path.symm_symm p)

theorem mkStepPath_symm_symm {A : Type u} {a b : A} (h : a = b) :
    Path.symm (Path.symm (mkStepPath h)) = mkStepPath h := by
  simpa using Path.symm_symm (mkStepPath h)

/-! ## Smooth manifolds and transitions -/

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

def unchartChartPath {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (S.unchart (S.chart m)) m :=
  S.unchart_chart m

def transitionCongr {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C}
    (h : Path c1 c2) : Path (transition S T c1) (transition S T c2) :=
  Path.congrArg T.chart (Path.congrArg S.unchart h)

theorem transitionSelfPath_eq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    transitionSelfPath S c = S.chart_unchart c :=
  rfl

theorem unchartChartPath_eq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    unchartChartPath S m = S.unchart_chart m :=
  rfl

theorem transitionCongr_def {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C} (h : Path c1 c2) :
    transitionCongr S T h = Path.congrArg T.chart (Path.congrArg S.unchart h) :=
  rfl

theorem transitionCongr_refl {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) (c : C) :
    transitionCongr S T (Path.refl c) = Path.refl (transition S T c) := by
  simp [transitionCongr, transition]

theorem transitionCongr_trans {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 c3 : C}
    (h1 : Path c1 c2) (h2 : Path c2 c3) :
    transitionCongr S T (Path.trans h1 h2) =
      Path.trans (transitionCongr S T h1) (transitionCongr S T h2) := by
  simp [transitionCongr, Path.congrArg_trans]

theorem transitionCongr_symm {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C}
    (h : Path c1 c2) :
    transitionCongr S T (Path.symm h) = Path.symm (transitionCongr S T h) := by
  simp [transitionCongr, Path.congrArg_symm]

theorem transitionSelfPath_symm_symm {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.symm (Path.symm (transitionSelfPath S c)) = transitionSelfPath S c := by
  simpa using Path.symm_symm (transitionSelfPath S c)

theorem transitionSelfPath_left_unit {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.trans (Path.refl (transition S S c)) (transitionSelfPath S c) = transitionSelfPath S c := by
  simpa using Path.trans_refl_left (transitionSelfPath S c)

theorem transitionSelfPath_right_unit {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path.trans (transitionSelfPath S c) (Path.refl c) = transitionSelfPath S c := by
  simpa using Path.trans_refl_right (transitionSelfPath S c)

/-! ## Tangent vectors -/

structure Tangent (M : Type u) (R : Type v) (p : M) where
  comp : R

def zeroTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) : Tangent M R p :=
  ⟨ring.zero⟩

def addTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) : Tangent M R p :=
  ⟨ring.add v.comp w.comp⟩

def negTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) : Tangent M R p :=
  ⟨ring.neg v.comp⟩

def scaleTangent {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v : Tangent M R p) : Tangent M R p :=
  ⟨ring.mul k v.comp⟩

def tangentAddCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) :
    Path (addTangent v w).comp (addTangent w v).comp :=
  ring.add_comm v.comp w.comp

def tangentAddAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (u1 v1 w1 : Tangent M R p) :
    Path (addTangent (addTangent u1 v1) w1).comp (addTangent u1 (addTangent v1 w1)).comp :=
  ring.add_assoc u1.comp v1.comp w1.comp

def tangentAddZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent (zeroTangent p) v).comp v.comp :=
  ring.zero_add v.comp

def tangentAddZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent v (zeroTangent p)).comp v.comp :=
  ring.add_zero v.comp

def tangentAddNegRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent v (negTangent v)).comp ring.zero :=
  ring.add_neg v.comp

def tangentScaleOnePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (scaleTangent ring.one v).comp v.comp :=
  ring.one_mul v.comp

def tangentScaleAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (a b : R) (v : Tangent M R p) :
    Path (scaleTangent a (scaleTangent b v)).comp (scaleTangent (ring.mul a b) v).comp :=
  Path.symm (ring.mul_assoc a b v.comp)

def tangentScaleDistribPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v w : Tangent M R p) :
    Path (scaleTangent k (addTangent v w)).comp (addTangent (scaleTangent k v) (scaleTangent k w)).comp :=
  ring.left_distrib k v.comp w.comp

theorem zeroTangent_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    (zeroTangent (M := M) (R := R) p).comp = ring.zero :=
  rfl

theorem addTangent_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) :
    (addTangent v w).comp = ring.add v.comp w.comp :=
  rfl

theorem negTangent_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    (negTangent v).comp = ring.neg v.comp :=
  rfl

theorem scaleTangent_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v : Tangent M R p) :
    (scaleTangent k v).comp = ring.mul k v.comp :=
  rfl

theorem tangentAddCommPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) :
    Path.symm (Path.symm (tangentAddCommPath v w)) = tangentAddCommPath v w := by
  simpa using Path.symm_symm (tangentAddCommPath v w)

theorem tangentAddAssocPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (u1 v1 w1 : Tangent M R p) :
    Path.symm (Path.symm (tangentAddAssocPath u1 v1 w1)) = tangentAddAssocPath u1 v1 w1 := by
  simpa using Path.symm_symm (tangentAddAssocPath u1 v1 w1)

theorem tangentAddZeroLeftPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path.symm (Path.symm (tangentAddZeroLeftPath v)) = tangentAddZeroLeftPath v := by
  simpa using Path.symm_symm (tangentAddZeroLeftPath v)

theorem tangentAddZeroRightPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path.symm (Path.symm (tangentAddZeroRightPath v)) = tangentAddZeroRightPath v := by
  simpa using Path.symm_symm (tangentAddZeroRightPath v)

theorem tangentAddNegRightPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path.symm (Path.symm (tangentAddNegRightPath v)) = tangentAddNegRightPath v := by
  simpa using Path.symm_symm (tangentAddNegRightPath v)

theorem tangentScaleOnePath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path.symm (Path.symm (tangentScaleOnePath v)) = tangentScaleOnePath v := by
  simpa using Path.symm_symm (tangentScaleOnePath v)

theorem tangentScaleAssocPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (a b : R) (v : Tangent M R p) :
    Path.symm (Path.symm (tangentScaleAssocPath a b v)) = tangentScaleAssocPath a b v := by
  simpa using Path.symm_symm (tangentScaleAssocPath a b v)

theorem tangentScaleDistribPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v w : Tangent M R p) :
    Path.symm (Path.symm (tangentScaleDistribPath k v w)) = tangentScaleDistribPath k v w := by
  simpa using Path.symm_symm (tangentScaleDistribPath k v w)

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

def zeroFieldEvalPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    Path ((zeroField (M := M) (R := R)).val p).comp ring.zero :=
  Path.refl _

def addFieldCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path ((addField X Y).val p).comp ((addField Y X).val p).comp :=
  tangentAddCommPath (X.val p) (Y.val p)

def addFieldAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y Z : VectorField M R) (p : M) :
    Path ((addField (addField X Y) Z).val p).comp ((addField X (addField Y Z)).val p).comp :=
  tangentAddAssocPath (X.val p) (Y.val p) (Z.val p)

def addFieldZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((addField (zeroField (M := M) (R := R)) X).val p).comp (X.val p).comp :=
  tangentAddZeroLeftPath (X.val p)

def addFieldZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path ((addField X (zeroField (M := M) (R := R))).val p).comp (X.val p).comp :=
  tangentAddZeroRightPath (X.val p)

def lieBracketExpandPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path (lieBracket X Y p)
         (ring.add (ring.mul (X.val p).comp (Y.val p).comp)
                   (ring.neg (ring.mul (Y.val p).comp (X.val p).comp))) :=
  Path.refl _

def lieBracketSelfZeroPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (lieBracket X X p) ring.zero :=
  ring.add_neg (ring.mul (X.val p).comp (X.val p).comp)

theorem zeroFieldEvalPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    Path.symm (Path.symm (zeroFieldEvalPath (M := M) (R := R) p)) =
      zeroFieldEvalPath (M := M) (R := R) p := by
  simpa using Path.symm_symm (zeroFieldEvalPath (M := M) (R := R) p)

theorem addFieldCommPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path.symm (Path.symm (addFieldCommPath X Y p)) = addFieldCommPath X Y p := by
  simpa using Path.symm_symm (addFieldCommPath X Y p)

theorem addFieldAssocPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y Z : VectorField M R) (p : M) :
    Path.symm (Path.symm (addFieldAssocPath X Y Z p)) = addFieldAssocPath X Y Z p := by
  simpa using Path.symm_symm (addFieldAssocPath X Y Z p)

theorem addFieldZeroLeftPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path.symm (Path.symm (addFieldZeroLeftPath X p)) = addFieldZeroLeftPath X p := by
  simpa using Path.symm_symm (addFieldZeroLeftPath X p)

theorem addFieldZeroRightPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path.symm (Path.symm (addFieldZeroRightPath X p)) = addFieldZeroRightPath X p := by
  simpa using Path.symm_symm (addFieldZeroRightPath X p)

theorem lieBracketExpandPath_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    lieBracketExpandPath X Y p = Path.refl (lieBracket X Y p) :=
  rfl

theorem lieBracketSelfZeroPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path.symm (Path.symm (lieBracketSelfZeroPath X p)) = lieBracketSelfZeroPath X p := by
  simpa using Path.symm_symm (lieBracketSelfZeroPath X p)

/-! ## Differential forms and exterior derivative -/

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
  ⟨fun p v w =>
    ring.add (ring.mul (om.eval p v) (ta.eval p w))
             (ring.neg (ring.mul (om.eval p w) (ta.eval p v)))⟩

def exteriorD {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : M → R) : OneForm M R :=
  ⟨fun p v => ring.mul (f p) v⟩

def zeroOneFormEvalPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) (v : R) :
    Path ((zeroOneForm (M := M) (R := R)).eval p v) ring.zero :=
  Path.refl _

def addOneFormCommPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm om ta).eval p v) ((addOneForm ta om).eval p v) :=
  ring.add_comm (om.eval p v) (ta.eval p v)

def addOneFormAssocPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta sg : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm (addOneForm om ta) sg).eval p v)
         ((addOneForm om (addOneForm ta sg)).eval p v) :=
  ring.add_assoc (om.eval p v) (ta.eval p v) (sg.eval p v)

def addOneFormZeroLeftPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm (zeroOneForm (M := M) (R := R)) om).eval p v) (om.eval p v) :=
  ring.zero_add (om.eval p v)

def addOneFormZeroRightPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((addOneForm om (zeroOneForm (M := M) (R := R))).eval p v) (om.eval p v) :=
  ring.add_zero (om.eval p v)

def scaleOneFormOnePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path ((scaleOneForm ring.one om).eval p v) (om.eval p v) :=
  ring.one_mul (om.eval p v)

def wedgeDiagZeroPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path ((wedge om ta).eval p v v) ring.zero :=
  ring.add_neg (ring.mul (om.eval p v) (ta.eval p v))

def exteriorDDistribPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : M → R) (p : M) (v w1 : R) :
    Path ((exteriorD f).eval p (ring.add v w1))
         (ring.add ((exteriorD f).eval p v) ((exteriorD f).eval p w1)) :=
  ring.left_distrib (f p) v w1

theorem zeroOneFormEvalPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) (v : R) :
    Path.symm (Path.symm (zeroOneFormEvalPath (M := M) (R := R) p v)) =
      zeroOneFormEvalPath (M := M) (R := R) p v := by
  simpa using Path.symm_symm (zeroOneFormEvalPath (M := M) (R := R) p v)

theorem addOneFormCommPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (addOneFormCommPath om ta p v)) = addOneFormCommPath om ta p v := by
  simpa using Path.symm_symm (addOneFormCommPath om ta p v)

theorem addOneFormAssocPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta sg : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (addOneFormAssocPath om ta sg p v)) = addOneFormAssocPath om ta sg p v := by
  simpa using Path.symm_symm (addOneFormAssocPath om ta sg p v)

theorem addOneFormZeroLeftPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (addOneFormZeroLeftPath om p v)) = addOneFormZeroLeftPath om p v := by
  simpa using Path.symm_symm (addOneFormZeroLeftPath om p v)

theorem addOneFormZeroRightPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (addOneFormZeroRightPath om p v)) = addOneFormZeroRightPath om p v := by
  simpa using Path.symm_symm (addOneFormZeroRightPath om p v)

theorem scaleOneFormOnePath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (scaleOneFormOnePath om p v)) = scaleOneFormOnePath om p v := by
  simpa using Path.symm_symm (scaleOneFormOnePath om p v)

theorem wedgeDiagZeroPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path.symm (Path.symm (wedgeDiagZeroPath om ta p v)) = wedgeDiagZeroPath om ta p v := by
  simpa using Path.symm_symm (wedgeDiagZeroPath om ta p v)

theorem exteriorDDistribPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : M → R) (p : M) (v w1 : R) :
    Path.symm (Path.symm (exteriorDDistribPath f p v w1)) = exteriorDDistribPath f p v w1 := by
  simpa using Path.symm_symm (exteriorDDistribPath f p v w1)

/-! ## Connections, parallel transport, curvature -/

structure Connection (M : Type u) (R : Type v) where
  transport : (p : M) → R → Tangent M R p → Tangent M R p

def flatConnection {M : Type u} {R : Type v} : Connection M R :=
  ⟨fun _ _ v => v⟩

def parallelTransport {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M)
    (dirs : List R) (v : Tangent M R p) : Tangent M R p :=
  dirs.foldl (fun acc d => Gam.transport p d acc) v

def flatTransportPath {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path ((flatConnection (M := M) (R := R)).transport p d v).comp v.comp :=
  Path.refl _

def parallelNilPath {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (v : Tangent M R p) :
    Path (parallelTransport Gam p [] v).comp v.comp :=
  Path.refl _

def parallelConsPath {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d : R) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport Gam p (d :: dirs) v).comp
         (parallelTransport Gam p dirs (Gam.transport p d v)).comp :=
  Path.refl _

def flatParallelSinglePath {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path (parallelTransport (flatConnection (M := M) (R := R)) p [d] v).comp v.comp :=
  Path.refl _

def flatParallelTwoPath {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (parallelTransport (flatConnection (M := M) (R := R)) p [d1, d2] v).comp v.comp :=
  Path.refl _

noncomputable def flatParallelAllPath {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport (flatConnection (M := M) (R := R)) p dirs v).comp v.comp := by
  induction dirs generalizing v with
  | nil =>
      exact Path.refl _
  | cons d ds ih =>
      simpa [parallelTransport, flatConnection] using (ih (v := v))

def curvature {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Tangent M R p × Tangent M R p :=
  let t1 := Gam.transport p d1 v
  let t2 := Gam.transport p d2 v
  let t12 := Gam.transport p d2 t1
  let t21 := Gam.transport p d1 t2
  (t12, t21)

def flatCurvatureComponentPath {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (curvature (flatConnection (M := M) (R := R)) p d1 d2 v).1.comp
         (curvature (flatConnection (M := M) (R := R)) p d1 d2 v).2.comp :=
  Path.refl _

def flatCurvatureSwapPath {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (curvature (flatConnection (M := M) (R := R)) p d1 d2 v)
         (curvature (flatConnection (M := M) (R := R)) p d2 d1 v) :=
  Path.refl _

theorem flatTransportPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatTransportPath p d v)) = flatTransportPath p d v := by
  simpa using Path.symm_symm (flatTransportPath p d v)

theorem parallelNilPath_symm_symm {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (v : Tangent M R p) :
    Path.symm (Path.symm (parallelNilPath Gam p v)) = parallelNilPath Gam p v := by
  simpa using Path.symm_symm (parallelNilPath Gam p v)

theorem parallelConsPath_symm_symm {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d : R) (dirs : List R) (v : Tangent M R p) :
    Path.symm (Path.symm (parallelConsPath Gam p d dirs v)) = parallelConsPath Gam p d dirs v := by
  simpa using Path.symm_symm (parallelConsPath Gam p d dirs v)

theorem flatParallelSinglePath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatParallelSinglePath p d v)) = flatParallelSinglePath p d v := by
  simpa using Path.symm_symm (flatParallelSinglePath p d v)

theorem flatParallelTwoPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatParallelTwoPath p d1 d2 v)) = flatParallelTwoPath p d1 d2 v := by
  simpa using Path.symm_symm (flatParallelTwoPath p d1 d2 v)

theorem flatParallelAllPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatParallelAllPath p dirs v)) = flatParallelAllPath p dirs v := by
  simpa using Path.symm_symm (flatParallelAllPath p dirs v)

theorem flatCurvatureComponentPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatCurvatureComponentPath p d1 d2 v)) = flatCurvatureComponentPath p d1 d2 v := by
  simpa using Path.symm_symm (flatCurvatureComponentPath p d1 d2 v)

theorem flatCurvatureSwapPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path.symm (Path.symm (flatCurvatureSwapPath p d1 d2 v)) = flatCurvatureSwapPath p d1 d2 v := by
  simpa using Path.symm_symm (flatCurvatureSwapPath p d1 d2 v)

/-! ## Geodesics -/

structure Geodesic (M : Type u) where
  points : List M

def trivialGeodesic {M : Type u} (x : M) : Geodesic M :=
  ⟨[x]⟩

def geodesicLength {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) : List M → R
  | [] => ring.zero
  | [_] => ring.zero
  | x :: y :: rest => ring.add (dist x y) (geodesicLength dist (y :: rest))

def geodesicLengthNilPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) :
    Path (geodesicLength dist []) ring.zero :=
  Path.refl _

def geodesicLengthSinglePath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path (geodesicLength dist [x]) ring.zero :=
  Path.refl _

def geodesicLengthTwoPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) :
    Path (geodesicLength dist [x, y]) (ring.add (dist x y) ring.zero) :=
  Path.refl _

def geodesicLengthConsPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) (rest : List M) :
    Path (geodesicLength dist (x :: y :: rest))
         (ring.add (dist x y) (geodesicLength dist (y :: rest))) :=
  Path.refl _

def trivialGeodesicLengthPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path (geodesicLength dist (trivialGeodesic x).points) ring.zero :=
  Path.refl _

theorem geodesicLengthNilPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) :
    Path.symm (Path.symm (geodesicLengthNilPath dist)) = geodesicLengthNilPath dist := by
  simpa using Path.symm_symm (geodesicLengthNilPath dist)

theorem geodesicLengthSinglePath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path.symm (Path.symm (geodesicLengthSinglePath dist x)) = geodesicLengthSinglePath dist x := by
  simpa using Path.symm_symm (geodesicLengthSinglePath dist x)

theorem geodesicLengthTwoPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) :
    Path.symm (Path.symm (geodesicLengthTwoPath dist x y)) = geodesicLengthTwoPath dist x y := by
  simpa using Path.symm_symm (geodesicLengthTwoPath dist x y)

theorem geodesicLengthConsPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) (rest : List M) :
    Path.symm (Path.symm (geodesicLengthConsPath dist x y rest)) = geodesicLengthConsPath dist x y rest := by
  simpa using Path.symm_symm (geodesicLengthConsPath dist x y rest)

theorem trivialGeodesicLengthPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path.symm (Path.symm (trivialGeodesicLengthPath dist x)) = trivialGeodesicLengthPath dist x := by
  simpa using Path.symm_symm (trivialGeodesicLengthPath dist x)

/-! ## Riemannian metric and Sym/Gam names -/

structure RiemannianMetric (M : Type u) (R : Type v) [ring : SmoothRing R] where
  dist : M → M → R
  self : ∀ x, Path (dist x x) ring.zero
  symm : ∀ x y, Path (dist x y) (dist y x)

def metricSelfPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x : M) :
    Path (Sym.dist x x) ring.zero :=
  Sym.self x

def metricSymmPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x y : M) :
    Path (Sym.dist x y) (Sym.dist y x) :=
  Sym.symm x y

def metricDoubleSwapPath {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x y : M) :
    Path (Sym.dist x y) (Sym.dist x y) :=
  Path.trans (Sym.symm x y) (Sym.symm y x)

theorem metricSelfPath_eq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x : M) :
    metricSelfPath Sym x = Sym.self x :=
  rfl

theorem metricSymmPath_eq {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x y : M) :
    metricSymmPath Sym x y = Sym.symm x y :=
  rfl

theorem metricSymmPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x y : M) :
    Path.symm (Path.symm (metricSymmPath Sym x y)) = metricSymmPath Sym x y := by
  simpa using Path.symm_symm (metricSymmPath Sym x y)

theorem metricDoubleSwapPath_symm_symm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (Sym : RiemannianMetric M R) (x y : M) :
    Path.symm (Path.symm (metricDoubleSwapPath Sym x y)) = metricDoubleSwapPath Sym x y := by
  simpa using Path.symm_symm (metricDoubleSwapPath Sym x y)

structure GamConnection (M : Type u) (R : Type v) where
  conn : Connection M R

def GamConnection.flat {M : Type u} {R : Type v} : GamConnection M R :=
  ⟨flatConnection⟩

def gamFlatTransportPath {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path ((GamConnection.flat (M := M) (R := R)).conn.transport p d v).comp v.comp :=
  Path.refl _

noncomputable def gamFlatParallelPath {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport (GamConnection.flat (M := M) (R := R)).conn p dirs v).comp v.comp :=
  flatParallelAllPath p dirs v

theorem gamFlatTransportPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path.symm (Path.symm (gamFlatTransportPath p d v)) = gamFlatTransportPath p d v := by
  simpa using Path.symm_symm (gamFlatTransportPath p d v)

theorem gamFlatParallelPath_symm_symm {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path.symm (Path.symm (gamFlatParallelPath p dirs v)) = gamFlatParallelPath p dirs v := by
  simpa using Path.symm_symm (gamFlatParallelPath p dirs v)

end DifferentialGeomDeep
end Algebra
end Path
end ComputationalPaths
