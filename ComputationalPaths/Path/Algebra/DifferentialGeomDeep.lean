/-
# Differential Geometry via Computational Paths

This module gives a large, computational-path-centric skeleton for differential
geometry.  The development includes smooth manifolds, tangent vectors, vector
fields, Lie brackets, differential forms, exterior derivative, wedge products,
de Rham-style classes, connections, parallel transport as `Path`, curvature,
geodesics, Stokes-structure integrals, and fiber bundles.

All equalities are witnessed with `Path`, and the file explicitly uses:
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

/-! ## Path API lemmas and constructors -/

def mkStepPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem mkStepPath_toEq {A : Type u} {a b : A} (h : a = b) :
    (mkStepPath h).toEq = h :=
  rfl

@[simp] theorem mkStepPath_refl {A : Type u} (a : A) :
    mkStepPath (rfl : a = a) = Path.mk [Step.mk a a rfl] rfl :=
  rfl

theorem mkStepPath_symm {A : Type u} {a b : A} (h : a = b) :
    Path.symm (mkStepPath h) = mkStepPath h.symm := by
  cases h
  rfl

theorem use_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

theorem use_trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

theorem use_trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

theorem use_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem use_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

theorem use_congrArg_trans {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

theorem use_congrArg_symm {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

theorem toEq_trans_refl {A : Type u} {a b : A} (p : Path a b) :
    (Path.trans p (Path.refl b)).toEq = p.toEq := by
  exact _root_.congrArg Path.toEq (Path.trans_refl_right p)

/-! ## Smooth manifolds and transitions -/

structure SmoothManifold (M : Type u) (C : Type v) where
  chart : M → C
  unchart : C → M
  chart_unchart : ∀ c : C, Path (chart (unchart c)) c
  unchart_chart : ∀ m : M, Path (unchart (chart m)) m

def transition {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) (c : C) : C :=
  T.chart (S.unchart c)

theorem transition_self {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path (transition S S c) c :=
  S.chart_unchart c

theorem transition_at_chart {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (transition S S (S.chart m)) (S.chart m) :=
  S.chart_unchart (S.chart m)

theorem transition_congr {M : Type u} {C : Type v}
    (S T : SmoothManifold M C) {c1 c2 : C}
    (h : Path c1 c2) :
    Path (transition S T c1) (transition S T c2) :=
  Path.congrArg (fun c => transition S T c) h

theorem unchart_chart_twice {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (S.unchart (S.chart (S.unchart (S.chart m)))) m := by
  exact Path.trans (S.unchart_chart (S.unchart (S.chart m))) (S.unchart_chart m)

theorem chart_unchart_twice {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path (S.chart (S.unchart (S.chart (S.unchart c)))) c := by
  exact Path.trans (S.chart_unchart (S.chart (S.unchart c))) (S.chart_unchart c)

theorem chart_after_unchart_chart {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (S.chart (S.unchart (S.chart m))) (S.chart m) :=
  Path.congrArg S.chart (S.unchart_chart m)

theorem unchart_after_chart_unchart {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path (S.unchart (S.chart (S.unchart c))) (S.unchart c) :=
  Path.congrArg S.unchart (S.chart_unchart c)

theorem roundtrip_cancel_left {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path (S.unchart (S.chart m)) (S.unchart (S.chart m)) := by
  exact Path.trans (S.unchart_chart m) (Path.symm (S.unchart_chart m))

theorem roundtrip_cancel_right {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (m : M) :
    Path m m := by
  exact Path.trans (Path.symm (S.unchart_chart m)) (S.unchart_chart m)

theorem transition_self_toEq {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    (transition_self S c).toEq = (S.chart_unchart c).toEq :=
  rfl

theorem transition_refl {M : Type u} {C : Type v}
    (S : SmoothManifold M C) (c : C) :
    Path (transition S S c) (transition S S c) :=
  Path.refl _

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

theorem tangent_zero_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    Path (zeroTangent (M := M) (R := R) p).comp ring.zero :=
  Path.refl _

theorem tangent_add_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) :
    Path (addTangent v w).comp (ring.add v.comp w.comp) :=
  Path.refl _

theorem tangent_neg_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (negTangent v).comp (ring.neg v.comp) :=
  Path.refl _

theorem tangent_scale_comp {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v : Tangent M R p) :
    Path (scaleTangent k v).comp (ring.mul k v.comp) :=
  Path.refl _

theorem tangent_add_comm {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v w : Tangent M R p) :
    Path (addTangent v w).comp (addTangent w v).comp :=
  ring.add_comm v.comp w.comp

theorem tangent_add_assoc {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (u v w : Tangent M R p) :
    Path (addTangent (addTangent u v) w).comp
         (addTangent u (addTangent v w)).comp :=
  ring.add_assoc u.comp v.comp w.comp

theorem tangent_add_zero_left {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent (zeroTangent p) v).comp v.comp :=
  ring.zero_add v.comp

theorem tangent_add_zero_right {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent v (zeroTangent p)).comp v.comp :=
  ring.add_zero v.comp

theorem tangent_add_neg_right {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (addTangent v (negTangent v)).comp ring.zero :=
  ring.add_neg v.comp

theorem tangent_scale_one {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path (scaleTangent ring.one v).comp v.comp :=
  ring.one_mul v.comp

theorem tangent_scale_assoc {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (a b : R) (v : Tangent M R p) :
    Path (scaleTangent a (scaleTangent b v)).comp
         (scaleTangent (ring.mul a b) v).comp := by
  simpa [scaleTangent] using (ring.mul_assoc a b v.comp).symm

theorem tangent_scale_distrib {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (k : R) (v w : Tangent M R p) :
    Path (scaleTangent k (addTangent v w)).comp
         (addTangent (scaleTangent k v) (scaleTangent k w)).comp :=
  ring.left_distrib k v.comp w.comp

theorem tangent_comp_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    {p : M} (v : Tangent M R p) :
    Path v.comp v.comp :=
  Path.refl _

/-! ## Vector fields and Lie bracket -/

structure VectorField (M : Type u) (R : Type v) where
  val : (p : M) → Tangent M R p

def zeroField {M : Type u} {R : Type v} [ring : SmoothRing R] :
    VectorField M R :=
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

theorem zero_field_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) :
    Path (zeroField (M := M) (R := R)).val p |>.comp ring.zero :=
  Path.refl _

theorem add_field_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path (addField X Y).val p |>.comp
         (ring.add (X.val p).comp (Y.val p).comp) :=
  Path.refl _

theorem neg_field_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (negField X).val p |>.comp (ring.neg (X.val p).comp) :=
  Path.refl _

theorem scale_field_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (k : R) (X : VectorField M R) (p : M) :
    Path (scaleField k X).val p |>.comp (ring.mul k (X.val p).comp) :=
  Path.refl _

theorem field_add_comm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path (addField X Y).val p |>.comp (addField Y X).val p |>.comp :=
  ring.add_comm (X.val p).comp (Y.val p).comp

theorem field_add_assoc {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y Z : VectorField M R) (p : M) :
    Path (addField (addField X Y) Z).val p |>.comp
         (addField X (addField Y Z)).val p |>.comp :=
  ring.add_assoc (X.val p).comp (Y.val p).comp (Z.val p).comp

theorem field_add_zero_left {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (addField zeroField X).val p |>.comp (X.val p).comp :=
  ring.zero_add (X.val p).comp

theorem field_add_zero_right {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (addField X zeroField).val p |>.comp (X.val p).comp :=
  ring.add_zero (X.val p).comp

theorem field_add_neg_right {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (addField X (negField X)).val p |>.comp ring.zero :=
  ring.add_neg (X.val p).comp

theorem field_scale_one {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (scaleField ring.one X).val p |>.comp (X.val p).comp :=
  ring.one_mul (X.val p).comp

theorem lie_bracket_expand {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path (lieBracket X Y p)
      (ring.add (ring.mul (X.val p).comp (Y.val p).comp)
        (ring.neg (ring.mul (Y.val p).comp (X.val p).comp))) :=
  Path.refl _

theorem lie_bracket_self_zero {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X : VectorField M R) (p : M) :
    Path (lieBracket X X p) ring.zero := by
  unfold lieBracket
  exact ring.add_neg (ring.mul (X.val p).comp (X.val p).comp)

theorem lie_bracket_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (X Y : VectorField M R) (p : M) :
    Path (lieBracket X Y p) (lieBracket X Y p) :=
  Path.refl _

/-! ## Differential forms, wedge, and exterior derivative -/

def ZeroForm (M : Type u) (R : Type v) := M → R

structure OneForm (M : Type u) (R : Type v) where
  eval : M → R → R

structure TwoForm (M : Type u) (R : Type v) where
  eval : M → R → R → R

def zeroOneForm {M : Type u} {R : Type v} [ring : SmoothRing R] :
    OneForm M R :=
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
    (f : ZeroForm M R) : OneForm M R :=
  ⟨fun p v => ring.mul (f p) v⟩

theorem zero_one_form_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (p : M) (v : R) :
    Path (zeroOneForm (M := M) (R := R)).eval p v ring.zero :=
  Path.refl _

theorem add_one_form_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path (addOneForm om ta).eval p v (ring.add (om.eval p v) (ta.eval p v)) :=
  Path.refl _

theorem scale_one_form_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (k : R) (om : OneForm M R) (p : M) (v : R) :
    Path (scaleOneForm k om).eval p v (ring.mul k (om.eval p v)) :=
  Path.refl _

theorem add_one_form_zero_left {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path (addOneForm zeroOneForm om).eval p v (om.eval p v) :=
  ring.zero_add (om.eval p v)

theorem add_one_form_zero_right {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path (addOneForm om zeroOneForm).eval p v (om.eval p v) :=
  ring.add_zero (om.eval p v)

theorem add_one_form_comm {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path (addOneForm om ta).eval p v (addOneForm ta om).eval p v :=
  ring.add_comm (om.eval p v) (ta.eval p v)

theorem add_one_form_assoc {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta sg : OneForm M R) (p : M) (v : R) :
    Path (addOneForm (addOneForm om ta) sg).eval p v
         (addOneForm om (addOneForm ta sg)).eval p v :=
  ring.add_assoc (om.eval p v) (ta.eval p v) (sg.eval p v)

theorem scale_one_form_one {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (p : M) (v : R) :
    Path (scaleOneForm ring.one om).eval p v (om.eval p v) :=
  ring.one_mul (om.eval p v)

theorem wedge_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v w : R) :
    Path (wedge om ta).eval p v w
      (ring.add (ring.mul (om.eval p v) (ta.eval p w))
        (ring.neg (ring.mul (om.eval p w) (ta.eval p v)))) :=
  Path.refl _

theorem wedge_diag_zero {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v : R) :
    Path (wedge om ta).eval p v v ring.zero := by
  unfold wedge
  exact ring.add_neg (ring.mul (om.eval p v) (ta.eval p v))

theorem wedge_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om ta : OneForm M R) (p : M) (v w : R) :
    Path (wedge om ta).eval p v w (wedge om ta).eval p v w :=
  Path.refl _

theorem exteriorD_eval {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : ZeroForm M R) (p : M) (v : R) :
    Path (exteriorD f).eval p v (ring.mul (f p) v) :=
  Path.refl _

theorem exteriorD_refl {M : Type u} {R : Type v} [ring : SmoothRing R]
    (f : ZeroForm M R) (p : M) (v : R) :
    Path (exteriorD f).eval p v (exteriorD f).eval p v :=
  Path.refl _

/-! ## de Rham style classes -/

structure DeRhamClass (R : Type u) where
  repr : R

def zeroClass {R : Type u} [ring : SmoothRing R] : DeRhamClass R :=
  ⟨ring.zero⟩

def addClass {R : Type u} [ring : SmoothRing R]
    (x y : DeRhamClass R) : DeRhamClass R :=
  ⟨ring.add x.repr y.repr⟩

def negClass {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) : DeRhamClass R :=
  ⟨ring.neg x.repr⟩

theorem class_add_zero_left {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass zeroClass x).repr x.repr :=
  ring.zero_add x.repr

theorem class_add_zero_right {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass x zeroClass).repr x.repr :=
  ring.add_zero x.repr

theorem class_add_comm {R : Type u} [ring : SmoothRing R]
    (x y : DeRhamClass R) :
    Path (addClass x y).repr (addClass y x).repr :=
  ring.add_comm x.repr y.repr

theorem class_add_assoc {R : Type u} [ring : SmoothRing R]
    (x y z : DeRhamClass R) :
    Path (addClass (addClass x y) z).repr (addClass x (addClass y z)).repr :=
  ring.add_assoc x.repr y.repr z.repr

theorem class_add_neg_right {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path (addClass x (negClass x)).repr ring.zero :=
  ring.add_neg x.repr

theorem class_repr_refl {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path x.repr x.repr :=
  Path.refl _

theorem class_repr_symm {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path.symm (Path.refl x.repr) = Path.refl x.repr := by
  simpa using (Path.symm_refl x.repr)

theorem class_repr_trans {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    Path.trans (Path.refl x.repr) (Path.refl x.repr) = Path.refl x.repr := by
  simpa using (Path.trans_refl_left (p := Path.refl x.repr))

theorem class_toEq_refl {R : Type u} [ring : SmoothRing R]
    (x : DeRhamClass R) :
    (Path.refl x.repr).toEq = rfl :=
  rfl

/-! ## Connections, parallel transport, curvature -/

structure Connection (M : Type u) (R : Type v) where
  transport : (p : M) → R → Tangent M R p → Tangent M R p

def flatConnection {M : Type u} {R : Type v} : Connection M R where
  transport := fun _ _ v => v

def parallelTransport {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (dirs : List R)
    (v : Tangent M R p) : Tangent M R p :=
  dirs.foldl (fun acc d => Gam.transport p d acc) v

def parallelTransportPath {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (dirs : List R)
    (v : Tangent M R p) :
    Path (parallelTransport Gam p dirs v).comp (parallelTransport Gam p dirs v).comp :=
  Path.refl _

theorem flat_transport_eval {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path (flatConnection (M := M) (R := R)).transport p d v |>.comp v.comp :=
  Path.refl _

theorem parallel_nil {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (v : Tangent M R p) :
    Path (parallelTransport Gam p [] v).comp v.comp :=
  Path.refl _

theorem parallel_cons {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d : R) (dirs : List R)
    (v : Tangent M R p) :
    Path (parallelTransport Gam p (d :: dirs) v).comp
      (parallelTransport Gam p dirs (Gam.transport p d v)).comp :=
  Path.refl _

theorem flat_parallel_single {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path (parallelTransport flatConnection p [d] v).comp v.comp :=
  Path.refl _

theorem flat_parallel_two {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (parallelTransport flatConnection p [d1, d2] v).comp v.comp :=
  Path.refl _

theorem flat_parallel_all {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport flatConnection p dirs v).comp v.comp := by
  induction dirs with
  | nil =>
      exact Path.refl _
  | cons d ds ih =>
      simpa [parallelTransport, flatConnection] using ih

theorem flat_parallel_path {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport flatConnection p dirs v).comp v.comp :=
  flat_parallel_all p dirs v

theorem flat_parallel_toEq {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    (flat_parallel_path (p := p) (dirs := dirs) (v := v)).toEq =
      (flat_parallel_path (p := p) (dirs := dirs) (v := v)).toEq :=
  rfl

def curvature {M : Type u} {R : Type v}
    (Gam : Connection M R) (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Tangent M R p × Tangent M R p :=
  let t1 := Gam.transport p d1 v
  let t2 := Gam.transport p d2 v
  (Gam.transport p d2 t1, Gam.transport p d1 t2)

theorem curvature_flat_component {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (curvature flatConnection p d1 d2 v).1.comp
         (curvature flatConnection p d1 d2 v).2.comp :=
  Path.refl _

theorem curvature_flat_swap {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (curvature flatConnection p d1 d2 v)
         (curvature flatConnection p d2 d1 v) :=
  Path.refl _

theorem curvature_flat_pair_refl {M : Type u} {R : Type v}
    (p : M) (d1 d2 : R) (v : Tangent M R p) :
    Path (curvature flatConnection p d1 d2 v)
         (curvature flatConnection p d1 d2 v) :=
  Path.refl _

/-! ## Geodesics and Stokes structure -/

structure Geodesic (M : Type u) where
  points : List M
  nonempty : points ≠ []

def geodesicLength {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) : List M → R
  | [] => ring.zero
  | [_] => ring.zero
  | x :: y :: rest => ring.add (dist x y) (geodesicLength dist (y :: rest))

def trivialGeodesic {M : Type u} (p : M) : Geodesic M :=
  ⟨[p], by simp⟩

theorem geodesic_length_nil {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) :
    Path (geodesicLength dist ([] : List M)) ring.zero :=
  Path.refl _

theorem geodesic_length_single {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path (geodesicLength dist [x]) ring.zero :=
  Path.refl _

theorem geodesic_length_two {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x y : M) :
    Path (geodesicLength dist [x, y]) (ring.add (dist x y) ring.zero) :=
  Path.refl _

theorem geodesic_trivial_length {M : Type u} {R : Type v} [ring : SmoothRing R]
    (dist : M → M → R) (x : M) :
    Path (geodesicLength dist (trivialGeodesic x).points) ring.zero :=
  Path.refl _

def chainIntegral {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) : List M → R
  | [] => ring.zero
  | [_] => ring.zero
  | x :: y :: rest =>
      ring.add (om.eval x (om.eval y ring.one)) (chainIntegral om (y :: rest))

theorem chain_integral_nil {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) :
    Path (chainIntegral om ([] : List M)) ring.zero :=
  Path.refl _

theorem chain_integral_single {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (x : M) :
    Path (chainIntegral om [x]) ring.zero :=
  Path.refl _

theorem chain_integral_two {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (x y : M) :
    Path (chainIntegral om [x, y]) (ring.add (om.eval x (om.eval y ring.one)) ring.zero) :=
  Path.refl _

theorem chain_integral_cons {M : Type u} {R : Type v} [ring : SmoothRing R]
    (om : OneForm M R) (x y : M) (rest : List M) :
    Path (chainIntegral om (x :: y :: rest))
      (ring.add (om.eval x (om.eval y ring.one)) (chainIntegral om (y :: rest))) :=
  Path.refl _

/-! ## Fiber bundles, gauge actions, Sym/Gam naming -/

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

theorem bundle_proj_lift {B : Type u} {F : Type v}
    (bndl : FiberBundle B F) (b : B) (f : F) :
    Path (bndl.proj (bndl.lift b f)) b :=
  bndl.proj_lift b f

theorem bundle_proj_fst {B : Type u} {F : Type v} (x : B × F) :
    Path (trivialBundle (B := B) (F := F)).proj x x.1 :=
  Path.refl _

theorem bundle_lift_refl {B : Type u} {F : Type v} (b : B) (f : F) :
    Path (trivialBundle (B := B) (F := F)).lift b f (b, f) :=
  Path.refl _

structure GaugeAction (G : Type u) (F : Type v) where
  act : G → F → F
  eid : G
  gmul : G → G → G
  act_id : ∀ x, Path (act eid x) x
  act_comp : ∀ g h x, Path (act (gmul g h) x) (act g (act h x))

def gaugeApply {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (g : G) (x : F) : F :=
  Act.act g x

theorem gauge_apply_id {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (x : F) :
    Path (gaugeApply Act Act.eid x) x :=
  Act.act_id x

theorem gauge_apply_comp {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (g h : G) (x : F) :
    Path (gaugeApply Act (Act.gmul g h) x)
         (gaugeApply Act g (gaugeApply Act h x)) :=
  Act.act_comp g h x

theorem gauge_apply_id_symm {G : Type u} {F : Type v}
    (Act : GaugeAction G F) (x : F) :
    Path.symm (gauge_apply_id Act x) =
      Path.symm (Act.act_id x) :=
  Path.refl _

structure SymTensor (M : Type u) (R : Type v) where
  eval : M → M → R
  symm_eval : ∀ x y, Path (eval x y) (eval y x)

theorem sym_tensor_swap {M : Type u} {R : Type v}
    (Sym : SymTensor M R) (x y : M) :
    Path (Sym.eval x y) (Sym.eval y x) :=
  Sym.symm_eval x y

theorem sym_tensor_double_swap {M : Type u} {R : Type v}
    (Sym : SymTensor M R) (x y : M) :
    Path (Sym.eval x y) (Sym.eval x y) := by
  exact Path.trans (Sym.symm_eval x y) (Sym.symm_eval y x)

structure GamConnection (M : Type u) (R : Type v) where
  conn : Connection M R

def GamConnection.flat {M : Type u} {R : Type v} : GamConnection M R :=
  ⟨flatConnection⟩

theorem gam_flat_transport {M : Type u} {R : Type v}
    (p : M) (d : R) (v : Tangent M R p) :
    Path (GamConnection.flat (M := M) (R := R)).conn.transport p d v |>.comp v.comp :=
  Path.refl _

theorem gam_flat_parallel {M : Type u} {R : Type v}
    (p : M) (dirs : List R) (v : Tangent M R p) :
    Path (parallelTransport (GamConnection.flat (M := M) (R := R)).conn p dirs v).comp v.comp :=
  flat_parallel_all p dirs v

end DifferentialGeomDeep
end Algebra
end Path
end ComputationalPaths
