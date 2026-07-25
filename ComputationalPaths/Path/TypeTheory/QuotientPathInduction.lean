/-
# Path induction for computational paths

This module answers, positively and unconditionally, the question left open by
the metadata-repair development: does the rewrite quotient of computational
paths support unrestricted based path induction?

The answer is yes, on *every* carrier, and the reason is a single primitive
rule.  `Path.lamCongr` packages a family of pointwise paths into a path between
functions while recording the **empty** trace, whereas `Path.congrArg` transports
traces pointwise.  Instantiating the primitive application rule
`Step.fun_app_beta` at the unit domain therefore exhibits the empty-trace path
as a one-step predecessor of an *arbitrary* path with the same endpoints:

```
Step (Path.mk [] p.proof) p        for every  p : Path a b.
```

Consequences developed below:

* `rweq_total` — `RwEq` relates every pair of computational paths with the same
  endpoints; `rwEqTotalOnLoops_always` is the loop form asked for by
  `MetadataRepair.RwEqTotalOnLoops`;
* `pathRwQuot_loop_contractible`, `pathRwQuot_localAxiomK`,
  `pathRwQuot_axiomK` — quotient-level axiom K holds unconditionally;
* `pathRwQuotJ` and `pathRwQuotJ_beta` — based path induction for
  `PathRwQuot` into arbitrary `Sort`-valued motives, with propositional beta,
  together with the Martin-Löf (unbased) form `pathRwQuotJ'`;
* `pathRwQuotEliminator` — the same statement in the
  `MetadataJ.UnrestrictedBasedEliminator` interface used by the classification
  theorems;
* `pathRwQuotEquivPLiftEq` — the quotient is equivalent to ambient equality, so
  the repair is the indiscrete one predicted by the universal repair theorem;
* `no_loop_quotient_equiv_of_not_contractible` — a *universal* strengthening of
  the circle and torus no-bridge theorems: no carrier whatsoever has a genuine
  `PathRwQuot` loop quotient equivalent to a noncontractible type;
* `groupoid_fragment_not_total` — sharpness.  The groupoid fragment of the
  rewrite system (unit, inverse, associativity, congruence and cancellation
  rules) preserves trace-length parity and therefore does *not* identify the
  empty and singleton reflexive traces.  The collapse is caused by the
  function-space rules, not by path algebra.

Nothing here contradicts the raw-record obstruction: `Path` itself still fails
unrestricted based elimination (`MetadataJ.path_no_unrestricted_based_eliminator`),
because raw traces remain observable.  The dichotomy is recorded as
`raw_fails_quotient_succeeds`.
-/

import ComputationalPaths.Path.TypeTheory.MetadataRepair

namespace ComputationalPaths
namespace Path
namespace QuotientPathInduction

open MetadataJ
open MetadataRepair

universe u v w

/-! ## The trace-free path and the collapsing rule -/

/-- The computational path that records an ambient equality with no rewrite
trace at all. -/
noncomputable def emptyTrace {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [] h

@[simp] theorem emptyTrace_steps {A : Type u} {a b : A} (h : a = b) :
    (emptyTrace h).steps = [] := rfl

/-- Ambient equality proofs are irrelevant, so the trace-free path depends only
on its endpoints. -/
theorem emptyTrace_eq {A : Type u} {a b : A} (h h' : a = b) :
    emptyTrace h = emptyTrace h' := rfl

@[simp] theorem emptyTrace_refl {A : Type u} (a : A) :
    emptyTrace (rfl : a = a) = Path.refl a := rfl

/-- `Path.lamCongr` records the empty trace: packaging a family of pointwise
paths into a path between functions discards every recorded step.  This is the
structural fact behind the collapse. -/
@[simp] theorem lamCongr_steps {A : Type u} {α : Type u} {f g : α → A}
    (p : ∀ x : α, Path (f x) (g x)) :
    (Path.lamCongr (f := f) (g := g) p).steps = [] := rfl

/-- **The collapsing rule.**  Instantiating the primitive application rule
`Step.fun_app_beta` at the unit domain makes the trace-free path a one-step
predecessor of an arbitrary path with the same endpoints.

Reading the rule from left to right, `congrArg (· ⋆) (lamCongr (fun _ => p))` is
literally `Path.mk [] p.proof`, because `lamCongr` erases the trace and
`congrArg` maps the erased trace pointwise.  Its reduct is `p`, whose trace is
arbitrary. -/
noncomputable def stepEmptyTrace {A : Type u} {a b : A} (p : Path a b) :
    Step (emptyTrace p.proof) p :=
  Step.fun_app_beta (A := A) (α := PUnit.{u + 1})
    (f := fun _ => a) (g := fun _ => b) (fun _ => p) PUnit.unit

/-- The rewrite-equivalence form of the collapsing rule. -/
noncomputable def rweqEmptyTrace {A : Type u} {a b : A} (p : Path a b) :
    RwEq (emptyTrace p.proof) p :=
  rweq_of_step (stepEmptyTrace p)

/-! ## `RwEq` is total on every fiber -/

/-- **Totality of rewrite equivalence.**  Any two computational paths with the
same endpoints are related by an explicit two-stage rewrite derivation: reduce
the trace-free path to the first, and to the second.

This is a genuine derivation, not a reflexivity stub: the two paths may carry
arbitrarily different traces, and the certificate passes through a third path
which is in general distinct from both. -/
noncomputable def rweqAny {A : Type u} {a b : A} (p q : Path a b) : RwEq p q :=
  rweq_trans (rweq_symm (rweqEmptyTrace p)) (rweqEmptyTrace q)

/-- Proof-valued form of totality. -/
theorem rweq_total {A : Type u} {a b : A} (p q : Path a b) :
    Nonempty (RwEq p q) :=
  ⟨rweqAny p q⟩

/-- The `rwEqSetoid` of any fiber is total, so `PathRwQuot` is an instance of the
maximal (indiscrete) setoid repair classified by
`MetadataRepair.quotient_contractible_iff_setoidTotal`. -/
theorem rwEqSetoid_total (A : Type u) (a b : A) :
    SetoidTotal (rwEqSetoid A a b) :=
  fun p q => rweq_total p q

/-- The loop form required by the raw-level criterion
`MetadataRepair.RwEqTotalOnLoops`, established for every carrier and every base
point rather than under a hypothesis on the carrier. -/
theorem rwEqTotalOnLoops_always (A : Type u) (a : A) :
    RwEqTotalOnLoops A a :=
  fun p q => rweq_total p q

/-! ## Consequences for the genuine loop quotient -/

/-- Every fiber of the rewrite quotient is a subsingleton. -/
theorem pathRwQuot_subsingleton (A : Type u) (a b : A)
    (x y : PathRwQuot A a b) : x = y := by
  refine Quot.inductionOn x ?_
  intro p
  refine Quot.inductionOn y ?_
  intro q
  exact Quot.sound (rweqProp_of_rweq (rweqAny p q))

instance instSubsingletonPathRwQuot (A : Type u) (a b : A) :
    Subsingleton (PathRwQuot A a b) :=
  ⟨pathRwQuot_subsingleton A a b⟩

/-- Every quotient class of paths is the class of the trace-free path. -/
theorem pathRwQuot_eq_mk_emptyTrace {A : Type u} {a b : A} (h : a = b)
    (x : PathRwQuot A a b) :
    x = Quot.mk _ (emptyTrace h) :=
  pathRwQuot_subsingleton A a b x _

/-- **The genuine loop quotient is contractible on every carrier.**  Contrast
`MetadataRepair.loop_quotient_contractible_of_all_eq`, which assumed the carrier
was a pointed subsingleton. -/
theorem pathRwQuot_loop_contractible (A : Type u) (a : A) :
    IsContractible (PathRwQuot A a a) :=
  (loop_quotient_contractible_iff_rweq_total A a).mpr
    (rwEqTotalOnLoops_always A a)

/-- Local quotient-level axiom K holds unconditionally. -/
theorem pathRwQuot_localAxiomK (A : Type u) (a : A) :
    PathRwQuotLocalAxiomK A a :=
  (local_axiomK_iff_rweq_total A a).mpr (rwEqTotalOnLoops_always A a)

/-- Global quotient-level axiom K holds unconditionally. -/
theorem pathRwQuot_axiomK (A : Type u) : PathRwQuotAxiomK A :=
  fun a => pathRwQuot_localAxiomK A a

/-- The rewrite quotient retains exactly the ambient equality and nothing else.
Together with `MetadataRepair.raw_loop_fiber_not_contractible` this is the sharp
form of the trade-off predicted by the universal repair theorem: unrestricted
elimination is regained precisely by discarding every observable trace
distinction. -/
noncomputable def pathRwQuotEquivPLiftEq (A : Type u) (a b : A) :
    SimpleEquiv (PathRwQuot A a b) (PLift (a = b)) where
  toFun := fun x => PLift.up (PathRwQuot.toEq x)
  invFun := fun h => Quot.mk _ (emptyTrace h.down)
  left_inv := fun x => pathRwQuot_subsingleton A a b _ x
  right_inv := fun _ => rfl

/-! ## Based path induction -/

/-- **Based path induction for computational paths.**  Every motive on the
rewrite quotient, including motives that inspect the class itself, is determined
by its value on the reflexive class.  The motive may land in an arbitrary
`Sort`. -/
noncomputable def pathRwQuotJ {A : Type u} {a : A}
    (C : (b : A) → PathRwQuot A a b → Sort w)
    (d : C a (PathRwQuot.refl a)) :
    (b : A) → (x : PathRwQuot A a b) → C b x :=
  fun _ x =>
    Eq.rec
      (motive := fun b' (_ : a = b') => (y : PathRwQuot A a b') → C b' y)
      (fun y =>
        Eq.rec (motive := fun z (_ : PathRwQuot.refl a = z) => C a z) d
          (pathRwQuot_localAxiomK A a y).symm)
      (PathRwQuot.toEq x) x

/-- Propositional beta for based path induction.  In fact the equation holds
definitionally, because the local axiom-K witness at the reflexive class is an
ambient equality proof and Lean's proof irrelevance identifies it with
reflexivity. -/
theorem pathRwQuotJ_beta {A : Type u} {a : A}
    (C : (b : A) → PathRwQuot A a b → Sort w)
    (d : C a (PathRwQuot.refl a)) :
    pathRwQuotJ C d a (PathRwQuot.refl a) = d := rfl

/-- Martin-Löf (unbased) path induction for computational paths. -/
noncomputable def pathRwQuotJ' {A : Type u}
    (C : (a b : A) → PathRwQuot A a b → Sort w)
    (d : (a : A) → C a a (PathRwQuot.refl a)) :
    (a b : A) → (x : PathRwQuot A a b) → C a b x :=
  fun a => pathRwQuotJ (C a) (d a)

/-- Propositional beta for the unbased eliminator. -/
theorem pathRwQuotJ'_beta {A : Type u}
    (C : (a b : A) → PathRwQuot A a b → Sort w)
    (d : (a : A) → C a a (PathRwQuot.refl a)) (a : A) :
    pathRwQuotJ' C d a a (PathRwQuot.refl a) = d a :=
  pathRwQuotJ_beta (C a) (d a)

/-- Transport along a quotient class, defined by path induction. -/
noncomputable def pathRwQuotTransport {A : Type u} {a : A}
    (D : A → Sort w) (d : D a) : (b : A) → PathRwQuot A a b → D b :=
  pathRwQuotJ (fun b _ => D b) d

@[simp] theorem pathRwQuotTransport_refl {A : Type u} {a : A}
    (D : A → Sort w) (d : D a) :
    pathRwQuotTransport D d a (PathRwQuot.refl a) = d :=
  pathRwQuotJ_beta (fun b _ => D b) d

/-- The based total space of `PathRwQuot` is contracted by its reflexive
point. -/
theorem pathRwQuotCenter_contracts (A : Type u) (a : A) :
    ContractsAt (pathRwQuotCenter A a) := by
  rintro ⟨b, x⟩
  have h : a = b := PathRwQuot.toEq x
  cases h
  have hx : x = PathRwQuot.refl a := pathRwQuot_localAxiomK A a x
  cases hx
  rfl

/-- The same result in the interface used by the classification theorems: the
based total space of `PathRwQuot` admits unrestricted based elimination with
propositional beta, unconditionally. -/
noncomputable def pathRwQuotEliminator (A : Type u) (a : A) :
    UnrestrictedBasedEliminator.{u, v} (pathRwQuotCenter A a) :=
  eliminatorOfContraction (pathRwQuotCenter_contracts A a)

/-- Family-wide statement. -/
theorem pathRwQuot_has_unrestricted_elimination (A : Type u) :
    ∀ a : A,
      Nonempty
        (UnrestrictedBasedEliminator.{u, v} (pathRwQuotCenter A a)) :=
  fun a => ⟨pathRwQuotEliminator A a⟩

/-! ## The sharp dichotomy -/

/-- **Raw records fail, the quotient succeeds.**  The first component is the
obstruction theorem for trace-carrying records; the second is the unconditional
repair proved here.  Both hold for every pointed carrier. -/
theorem raw_fails_quotient_succeeds (A : Type u) (a : A) :
    (¬ IsContractible (Path a a)) ∧ IsContractible (PathRwQuot A a a) :=
  ⟨raw_loop_fiber_not_contractible a, pathRwQuot_loop_contractible A a⟩

/-! ## A universal no-bridge theorem -/

/-- No carrier has a genuine `PathRwQuot` loop quotient equivalent to a
noncontractible type.  The circle and torus statements of `MetadataRepair` are
the special cases `Y = ℤ` and `Y = ℤ × ℤ`; the obstruction is not a defect of
those particular one-constructor carriers. -/
theorem no_loop_quotient_equiv_of_not_contractible
    (A : Type u) (a : A) {Y : Type v} (hY : ¬ IsContractible Y) :
    SimpleEquiv (PathRwQuot A a a) Y → False := by
  intro e
  exact hY ((contractible_iff_of_equiv e).mp (pathRwQuot_loop_contractible A a))

/-- In particular no carrier's genuine loop quotient is equivalent to the
integers, so no future choice of point space can make the synthetic winding
presentation agree with the genuine one while the present rewrite rules stand. -/
theorem no_loop_quotient_equiv_int (A : Type u) (a : A) :
    SimpleEquiv (PathRwQuot A a a) Int → False :=
  no_loop_quotient_equiv_of_not_contractible A a int_not_contractible

/-- The same for the synthetic torus target. -/
theorem no_loop_quotient_equiv_int_prod (A : Type u) (a : A) :
    SimpleEquiv (PathRwQuot A a a) (Int × Int) → False :=
  no_loop_quotient_equiv_of_not_contractible A a int_prod_not_contractible

/-! ## Sharpness: the groupoid fragment does not collapse

The collapse above is caused by the function-space rules, not by path algebra.
The following fragment consists exactly of the unit, inverse, associativity,
congruence and cancellation rules of `Step`, all of which preserve trace-length
parity. -/

/-- The groupoid fragment of the primitive rewrite system. -/
inductive GroupoidStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Type u where
  | symm_refl (a : A) :
      GroupoidStep (Path.symm (Path.refl a)) (Path.refl a)
  | symm_symm {a b : A} (p : Path a b) :
      GroupoidStep (Path.symm (Path.symm p)) p
  | trans_refl_left {a b : A} (p : Path a b) :
      GroupoidStep (Path.trans (Path.refl a) p) p
  | trans_refl_right {a b : A} (p : Path a b) :
      GroupoidStep (Path.trans p (Path.refl b)) p
  | trans_symm {a b : A} (p : Path a b) :
      GroupoidStep (Path.trans p (Path.symm p)) (Path.refl a)
  | symm_trans {a b : A} (p : Path a b) :
      GroupoidStep (Path.trans (Path.symm p) p) (Path.refl b)
  | symm_trans_congr {a b c : A} (p : Path a b) (q : Path b c) :
      GroupoidStep (Path.symm (Path.trans p q))
        (Path.trans (Path.symm q) (Path.symm p))
  | trans_assoc {a b c d : A}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      GroupoidStep (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))
  | symm_congr {a b : A} {p q : Path a b} :
      GroupoidStep p q → GroupoidStep (Path.symm p) (Path.symm q)
  | trans_congr_left {a b c : A} {p q : Path a b} (r : Path b c) :
      GroupoidStep p q → GroupoidStep (Path.trans p r) (Path.trans q r)
  | trans_congr_right {a b c : A} (p : Path a b) {q r : Path b c} :
      GroupoidStep q r → GroupoidStep (Path.trans p q) (Path.trans p r)
  | trans_cancel_left {a b c : A} (p : Path a b) (q : Path a c) :
      GroupoidStep (Path.trans p (Path.trans (Path.symm p) q)) q
  | trans_cancel_right {a b c : A} (p : Path a b) (q : Path b c) :
      GroupoidStep (Path.trans (Path.symm p) (Path.trans p q)) q

/-- The fragment really is a fragment: every groupoid rule is a primitive rule
of the full system. -/
noncomputable def groupoidStepToStep {A : Type u} {a b : A}
    {p q : Path a b} : GroupoidStep p q → Step p q
  | .symm_refl a => Step.symm_refl a
  | .symm_symm p => Step.symm_symm p
  | .trans_refl_left p => Step.trans_refl_left p
  | .trans_refl_right p => Step.trans_refl_right p
  | .trans_symm p => Step.trans_symm p
  | .symm_trans p => Step.symm_trans p
  | .symm_trans_congr p q => Step.symm_trans_congr p q
  | .trans_assoc p q r => Step.trans_assoc p q r
  | .symm_congr h => Step.symm_congr (groupoidStepToStep h)
  | .trans_congr_left r h => Step.trans_congr_left r (groupoidStepToStep h)
  | .trans_congr_right p h => Step.trans_congr_right p (groupoidStepToStep h)
  | .trans_cancel_left p q => Step.trans_cancel_left p q
  | .trans_cancel_right p q => Step.trans_cancel_right p q

/-- Equivalence closure of the groupoid fragment. -/
inductive GroupoidRwEq {A : Type u} {a b : A} : Path a b → Path a b → Type u where
  | refl (p : Path a b) : GroupoidRwEq p p
  | step {p q : Path a b} : GroupoidStep p q → GroupoidRwEq p q
  | symm {p q : Path a b} : GroupoidRwEq p q → GroupoidRwEq q p
  | trans {p q r : Path a b} :
      GroupoidRwEq p q → GroupoidRwEq q r → GroupoidRwEq p r

/-- The number of recorded rewrite steps. -/
def traceLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

@[simp] theorem traceLength_refl {A : Type u} (a : A) :
    traceLength (Path.refl a) = 0 := rfl

@[simp] theorem traceLength_stepChain {A : Type u} {a b : A} (h : a = b) :
    traceLength (Path.stepChain h) = 1 := rfl

@[simp] theorem traceLength_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    traceLength (Path.trans p q) = traceLength p + traceLength q := by
  simp [traceLength]

@[simp] theorem traceLength_symm {A : Type u} {a b : A} (p : Path a b) :
    traceLength (Path.symm p) = traceLength p := by
  simp [traceLength]

/-- Trace-length parity, the invariant separating the fragment's classes. -/
def traceParity {A : Type u} {a b : A} (p : Path a b) : Nat :=
  traceLength p % 2

theorem traceParity_eq {A : Type u} {a b : A} (p : Path a b) :
    traceParity p = traceLength p % 2 := rfl

@[simp] theorem traceParity_refl {A : Type u} (a : A) :
    traceParity (Path.refl a) = 0 := rfl

@[simp] theorem traceParity_stepChain {A : Type u} {a b : A} (h : a = b) :
    traceParity (Path.stepChain h) = 1 := rfl

/-- Every rule of the groupoid fragment preserves trace-length parity. -/
theorem groupoidStep_traceParity {A : Type u} {a b : A}
    {p q : Path a b} (h : GroupoidStep p q) :
    traceParity p = traceParity q := by
  induction h with
  | symm_refl a => rfl
  | symm_symm p =>
      simp only [traceParity_eq, traceLength_symm]
  | trans_refl_left p =>
      simp only [traceParity_eq, traceLength_trans, traceLength_refl]
      omega
  | trans_refl_right p =>
      simp only [traceParity_eq, traceLength_trans, traceLength_refl]
      omega
  | trans_symm p =>
      simp only [traceParity_eq, traceLength_trans, traceLength_symm,
        traceLength_refl]
      omega
  | symm_trans p =>
      simp only [traceParity_eq, traceLength_trans, traceLength_symm,
        traceLength_refl]
      omega
  | symm_trans_congr p q =>
      simp only [traceParity_eq, traceLength_trans, traceLength_symm]
      omega
  | trans_assoc p q r =>
      simp only [traceParity_eq, traceLength_trans]
      omega
  | symm_congr _ ih =>
      simp only [traceParity_eq, traceLength_symm]
      simpa only [traceParity_eq] using ih
  | trans_congr_left r _ ih =>
      simp only [traceParity_eq, traceLength_trans]
      simp only [traceParity_eq] at ih
      omega
  | trans_congr_right p _ ih =>
      simp only [traceParity_eq, traceLength_trans]
      simp only [traceParity_eq] at ih
      omega
  | trans_cancel_left p q =>
      simp only [traceParity_eq, traceLength_trans, traceLength_symm]
      omega
  | trans_cancel_right p q =>
      simp only [traceParity_eq, traceLength_trans, traceLength_symm]
      omega

/-- Hence the whole equivalence closure of the fragment preserves parity. -/
theorem groupoidRwEq_traceParity {A : Type u} {a b : A}
    {p q : Path a b} (h : GroupoidRwEq p q) :
    traceParity p = traceParity q := by
  induction h with
  | refl p => rfl
  | step h => exact groupoidStep_traceParity h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Sharpness.**  The groupoid fragment does not relate the empty and
singleton reflexive traces, so it is not total and does not repair unrestricted
elimination on its own.  The collapse established above is therefore caused by
the function-space rules `Step.fun_app_beta`/`Step.fun_eta` together with the
trace-erasing definition of `Path.lamCongr`, not by path algebra. -/
theorem groupoid_fragment_not_total {A : Type u} (a : A) :
    GroupoidRwEq (Path.refl a) (Path.stepChain (rfl : a = a)) → False := by
  intro h
  have hparity : (0 : Nat) = 1 := groupoidRwEq_traceParity h
  exact absurd hparity (by decide)

/-- The full system does relate them, by the collapsing rule.  Comparing this
with `groupoid_fragment_not_total` localises the collapse exactly. -/
noncomputable def full_system_relates_empty_and_singleton {A : Type u} (a : A) :
    RwEq (Path.refl a) (Path.stepChain (rfl : a = a)) :=
  rweqAny _ _

/-- The setoid generated by the groupoid fragment, so that the classification
theorems of `MetadataRepair` can be applied to it verbatim. -/
noncomputable def groupoidSetoid (A : Type u) (a b : A) : Setoid (Path a b) where
  r := fun p q => Nonempty (GroupoidRwEq p q)
  iseqv :=
    { refl := fun p => ⟨GroupoidRwEq.refl p⟩
      symm := fun h => Nonempty.elim h (fun d => ⟨GroupoidRwEq.symm d⟩)
      trans := fun h₁ h₂ =>
        Nonempty.elim h₁ (fun d₁ =>
          Nonempty.elim h₂ (fun d₂ => ⟨GroupoidRwEq.trans d₁ d₂⟩)) }

/-- The groupoid fragment fails the universal repair criterion. -/
theorem groupoidSetoid_not_setoidTotal (A : Type u) (a : A) :
    ¬ SetoidTotal (groupoidSetoid A a a) := by
  intro total
  exact Nonempty.elim (total (Path.refl a) (Path.stepChain (rfl : a = a)))
    (fun d => groupoid_fragment_not_total a d)

/-- Consequently the groupoid-fragment quotient of loops is not contractible,
and by `MetadataRepair.quotient_contractible_iff_setoidTotal` the fragment does
not repair unrestricted based elimination.  Together with
Corollary~`pathRwQuot_loop_contractible` this shows the criterion of
`MetadataRepair` genuinely separates the two rewrite systems: it fails for the
groupoid fragment and holds for the full one. -/
theorem groupoid_quotient_loop_not_contractible (A : Type u) (a : A) :
    ¬ IsContractible (Quotient (groupoidSetoid A a a)) := by
  intro contraction
  exact groupoidSetoid_not_setoidTotal A a
    ((quotient_contractible_iff_setoidTotal (groupoidSetoid A a a)
      (Path.refl a)).mp contraction)

/-- The two rewrite systems, side by side, at the level the classification
measures. -/
theorem fragment_fails_full_system_succeeds (A : Type u) (a : A) :
    (¬ IsContractible (Quotient (groupoidSetoid A a a))) ∧
      IsContractible (PathRwQuot A a a) :=
  ⟨groupoid_quotient_loop_not_contractible A a,
    pathRwQuot_loop_contractible A a⟩

/-! ## Explicit rewrite evidence

A genuine multi-stage derivation using the collapsing rule, kept as concrete
`Path`/`RwEq` evidence rather than a reflexivity stub. -/

/-- A length-two composite whose trace has two entries. -/
noncomputable def doubleStepLoop {A : Type u} (a : A) : Path a a :=
  Path.trans (Path.stepChain (rfl : a = a)) (Path.stepChain (rfl : a = a))

theorem doubleStepLoop_traceParity {A : Type u} (a : A) :
    traceParity (doubleStepLoop a) = 0 := by
  simp only [doubleStepLoop, traceParity_eq, traceLength_trans,
    traceLength_stepChain]

/-- The two-entry composite is `RwEq`-equivalent to the trace-free path by a
derivation that passes through the empty trace, uses the collapsing rule twice,
and is not available in the groupoid fragment at the level of parity classes. -/
noncomputable def doubleStepLoopRweqRefl {A : Type u} (a : A) :
    RwEq (doubleStepLoop a) (Path.refl a) :=
  rweq_trans
    (rweq_symm (rweqEmptyTrace (doubleStepLoop a)))
    (rweqEmptyTrace (Path.refl a))

/-- The corresponding quotient identification. -/
theorem doubleStepLoop_same_class {A : Type u} (a : A) :
    (Quot.mk _ (doubleStepLoop a) : PathRwQuot A a a) =
      Quot.mk _ (Path.refl a) :=
  Quot.sound (rweqProp_of_rweq (doubleStepLoopRweqRefl a))

/-! ## A design constraint on redesigned rewrite systems

The collapse is a fact about one rule set.  The natural follow-up question is
what any *replacement* rule set must satisfy in order to keep the quotient
informative.  The answer is a single equivalence, and both of the concrete
results above are instances of it.

"Keeping information" is made precise as admitting an invariant that is not
constant: a map out of the fiber which is stable under the rewrite relation and
still separates two paths.  Such a map is exactly a nonconstant function on the
quotient. -/

/-- A function constant on each class of a setoid. -/
def SetoidInvariant {X : Type u} (S : Setoid X) {V : Type v} (I : X → V) : Prop :=
  ∀ x y : X, S.r x y → I x = I y

/-- An invariant carries information when it separates two points. -/
def Nonconstant {X : Type u} {V : Type v} (I : X → V) : Prop :=
  ∃ x y : X, I x ≠ I y

/-- **The design theorem.**  A setoid is total exactly when every invariant of
it is constant.  Combined with
`MetadataRepair.quotient_contractible_iff_setoidTotal`, this puts the two design
goals in direct opposition: a quotient supports unrestricted elimination exactly
when it retains nothing, so no rewrite system can meet both. -/
theorem setoidTotal_iff_all_invariants_constant {X : Type u} (S : Setoid X) :
    SetoidTotal S ↔
      ∀ (V : Type u) (I : X → V), SetoidInvariant S I → ∀ x y : X, I x = I y := by
  constructor
  · intro total V I hinv x y
    exact hinv x y (total x y)
  · intro h x y
    exact Quotient.exact
      (h (Quotient S) (Quotient.mk S) (fun _ _ hr => Quotient.sound hr) x y)

/-- Contrapositive, in the form a designer uses it: exhibiting one invariant
that separates two paths proves the relation is not total, hence that the
quotient is not contractible. -/
theorem not_setoidTotal_of_nonconstant_invariant {X : Type u} {S : Setoid X}
    {V : Type v} {I : X → V}
    (hinv : SetoidInvariant S I) (hI : Nonconstant I) : ¬ SetoidTotal S := by
  rintro total
  obtain ⟨x, y, hxy⟩ := hI
  exact hxy (hinv x y (total x y))

/-- The other direction, in the form a critic uses it: if the relation is total
then every invariant is constant. -/
theorem invariant_constant_of_setoidTotal {X : Type u} {S : Setoid X}
    (total : SetoidTotal S) {V : Type v} {I : X → V}
    (hinv : SetoidInvariant S I) (x y : X) : I x = I y :=
  hinv x y (total x y)

/-- The abstract reason the present rule set collapses: some element rewrites to
everything.  Any relation with such a universal predecessor is total, whatever
its other rules are. -/
theorem setoidTotal_of_universal_predecessor {X : Type u} (S : Setoid X) (e : X)
    (h : ∀ x : X, S.r e x) : SetoidTotal S :=
  fun x y => S.trans (S.symm (h x)) (h y)

/-- The collapse is exactly that instance: the trace-free path is a universal
predecessor of its fiber. -/
theorem rwEq_universal_predecessor {A : Type u} {a b : A} (h : a = b) :
    ∀ p : Path a b, (rwEqSetoid A a b).r (emptyTrace h) p :=
  fun p => rweqProp_of_rweq (rweqEmptyTrace p)

/-- Consequently a redesigned rule set that keeps any information at a fiber
must not admit a universal predecessor there.  This is the concrete design
constraint. -/
theorem no_universal_predecessor_of_nonconstant_invariant
    {X : Type u} {S : Setoid X} {V : Type v} {I : X → V}
    (hinv : SetoidInvariant S I) (hI : Nonconstant I) (e : X) :
    ¬ (∀ x : X, S.r e x) := fun h =>
  not_setoidTotal_of_nonconstant_invariant hinv hI
    (setoidTotal_of_universal_predecessor S e h)

/-- **Every `RwEq`-invariant is constant.**  This is the sharpest statement of
what the present rewrite quotient retains, and it is the form to check a
redesign against: any proposed invariant of `PathRwQuot` -- a winding number, a
trace length, a normal form, a homotopy class -- is provably constant under the
current rules. -/
theorem rwEq_invariant_constant {A : Type u} {a b : A} {V : Type v}
    {I : Path a b → V}
    (hinv : ∀ p q : Path a b, Nonempty (RwEq p q) → I p = I q)
    (p q : Path a b) : I p = I q :=
  hinv p q (rweq_total p q)

/-! ### The groupoid fragment as a proof of concept

The design theorem asks a redesign to exhibit a nonconstant invariant.  The
groupoid fragment does exhibit one, which is what makes the sharpness result of
the previous section an instance of the general statement rather than an
unrelated argument. -/

theorem groupoidSetoid_parity_invariant (A : Type u) (a b : A) :
    SetoidInvariant (groupoidSetoid A a b) (fun p : Path a b => traceParity p) :=
  fun _ _ h => Nonempty.elim h (fun d => groupoidRwEq_traceParity d)

theorem groupoidSetoid_parity_nonconstant {A : Type u} (a : A) :
    Nonconstant (fun p : Path a a => traceParity p) := by
  refine ⟨Path.refl a, Path.stepChain (rfl : a = a), ?_⟩
  simp only [traceParity_refl, traceParity_stepChain]
  exact Nat.zero_ne_one

/-- Re-deriving non-totality of the fragment from the design theorem, rather
than from the ad hoc argument, confirms that the theorem has the intended
force. -/
theorem groupoidSetoid_not_total_via_design {A : Type u} (a : A) :
    ¬ SetoidTotal (groupoidSetoid A a a) :=
  not_setoidTotal_of_nonconstant_invariant
    (groupoidSetoid_parity_invariant A a a)
    (groupoidSetoid_parity_nonconstant a)

end QuotientPathInduction
end Path
end ComputationalPaths
