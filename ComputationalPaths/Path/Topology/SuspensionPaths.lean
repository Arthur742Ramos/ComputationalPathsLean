/-
# Suspension constructions via computational paths

We model the suspension using computational paths within the UIP framework.
Since `Path a b` requires `a = b` propositionally, we work with the
*algebraic* suspension: a quotient type that identifies all meridian
endpoints, then study the path algebra on this quotient.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

/-! ## Suspension as a quotient -/

/-- Raw suspension data: two poles plus meridian points. -/
inductive SuspRaw (A : Type u) : Type u where
  | north : SuspRaw A
  | south : SuspRaw A
  | merid : A → SuspRaw A

/-- The suspension relation identifies `merid a` with both `north` and `south`.
Since we are in a UIP setting, the quotient collapses to a single point
when `A` is nonempty—this is the correct behaviour: the unreduced suspension
of a nonempty discrete type is contractible in the propositional sense. -/
inductive SuspRel (A : Type u) : SuspRaw A → SuspRaw A → Prop where
  | merid_north : ∀ a : A, SuspRel A (SuspRaw.merid a) SuspRaw.north
  | merid_south : ∀ a : A, SuspRel A (SuspRaw.merid a) SuspRaw.south
  | refl : ∀ x : SuspRaw A, SuspRel A x x
  | symm : ∀ {x y}, SuspRel A x y → SuspRel A y x
  | trans : ∀ {x y z}, SuspRel A x y → SuspRel A y z → SuspRel A x z

/-- The suspension relation generates an equivalence. -/
theorem suspRel_equivalence (A : Type u) : Equivalence (SuspRel A) :=
  ⟨SuspRel.refl, fun h => SuspRel.symm h, fun h₁ h₂ => SuspRel.trans h₁ h₂⟩

/-- Setoid for the suspension quotient. -/
def suspSetoid (A : Type u) : Setoid (SuspRaw A) :=
  ⟨SuspRel A, suspRel_equivalence A⟩

/-- The suspension of `A` as a quotient type. -/
def Susp (A : Type u) : Type u := Quotient (suspSetoid A)

namespace Susp

variable {A : Type u} {B : Type v}

/-- The north pole in the suspension. -/
def north : Susp A := Quotient.mk (suspSetoid A) SuspRaw.north

/-- The south pole in the suspension. -/
def south : Susp A := Quotient.mk (suspSetoid A) SuspRaw.south

/-- The meridian point corresponding to `a`. -/
def merid (a : A) : Susp A := Quotient.mk (suspSetoid A) (SuspRaw.merid a)

/-- In the suspension, `merid a = north`. -/
theorem merid_eq_north (a : A) : merid a = @north A :=
  Quotient.sound (SuspRel.merid_north a)

/-- In the suspension, `merid a = south`. -/
theorem merid_eq_south (a : A) : merid a = @south A :=
  Quotient.sound (SuspRel.merid_south a)

/-- In the suspension, `north = south` (when `A` is nonempty). -/
theorem north_eq_south (a : A) : @north A = @south A :=
  (merid_eq_north a).symm.trans (merid_eq_south a)

/-! ## Path constructions in the suspension -/

/-- Full meridian path from north to south through `a`. -/
def fullMeridian (a : A) : Path (@north A) (@south A) :=
  Path.mk [Step.mk _ _ (north_eq_south a)] (north_eq_south a)

/-- Reverse meridian path. -/
def fullMeridianRev (a : A) : Path (@south A) (@north A) :=
  Path.symm (fullMeridian a)

/-- The meridian path has the expected proof component. -/
theorem fullMeridian_proof (a : A) :
    (fullMeridian a).proof = north_eq_south a :=
  proof_irrel _ _

/-- Two full meridians are propositionally equal (UIP). -/
theorem fullMeridian_eq (a b : A) : fullMeridian a = fullMeridian b := by
  simp [fullMeridian]

/-! ## Loop structure -/

/-- A loop at north built from two meridians. -/
def meridianLoop (a b : A) : Path (@north A) (@north A) :=
  Path.trans (fullMeridian a) (fullMeridianRev b)

theorem meridianLoop_toEq (a b : A) :
    (meridianLoop a b).toEq = rfl := by
  simp [meridianLoop, fullMeridian, fullMeridianRev]

/-- A loop at south. -/
def southLoop (a b : A) : Path (@south A) (@south A) :=
  Path.trans (fullMeridianRev a) (fullMeridian b)

theorem southLoop_toEq (a b : A) :
    (southLoop a b).toEq = rfl := by
  simp [southLoop, fullMeridian, fullMeridianRev]

/-- All loops at north are proof-irrelevant. -/
theorem loop_north_eq (p q : Path (@north A) (@north A)) :
    p.proof = q.proof :=
  proof_irrel _ _

/-- All loops at south are proof-irrelevant. -/
theorem loop_south_eq (p q : Path (@south A) (@south A)) :
    p.proof = q.proof :=
  rfl

/-! ## Suspension functoriality -/

/-- Raw map on suspension data. -/
def mapRaw (f : A → B) : SuspRaw A → SuspRaw B
  | SuspRaw.north => SuspRaw.north
  | SuspRaw.south => SuspRaw.south
  | SuspRaw.merid a => SuspRaw.merid (f a)

/-- The raw map respects the suspension relation. -/
theorem mapRaw_respects (f : A → B) {x y : SuspRaw A} (h : SuspRel A x y) :
    SuspRel B (mapRaw f x) (mapRaw f y) := by
  induction h with
  | merid_north a => exact SuspRel.merid_north (f a)
  | merid_south a => exact SuspRel.merid_south (f a)
  | refl x => exact SuspRel.refl _
  | symm _ ih => exact SuspRel.symm ih
  | trans _ _ ih₁ ih₂ => exact SuspRel.trans ih₁ ih₂

/-- Functorial map on suspensions. -/
def map (f : A → B) : Susp A → Susp B :=
  Quotient.lift (fun x => Quotient.mk (suspSetoid B) (mapRaw f x))
    (fun _ _ h => Quotient.sound (mapRaw_respects f h))

theorem map_north (f : A → B) : map f north = @north B := rfl
theorem map_south (f : A → B) : map f south = @south B := rfl
theorem map_merid (f : A → B) (a : A) : map f (merid a) = merid (f a) := rfl

/-- Identity map on suspension is identity. -/
theorem map_id : map (id : A → A) = id := by
  ext x
  exact Quotient.inductionOn x (fun r => by cases r <;> rfl)

/-- Composition of maps on suspension. -/
theorem map_comp {C : Type w} (f : A → B) (g : B → C) :
    map (g ∘ f) = map g ∘ map f := by
  ext x
  exact Quotient.inductionOn x (fun r => by cases r <;> rfl)

/-! ## Suspension is path-connected -/

/-- Every element of the suspension equals north. -/
theorem eq_north (x : Susp A) [Nonempty A] : x = north := by
  exact Quotient.inductionOn x (fun r => by
    cases r with
    | north => rfl
    | south => exact (north_eq_south (Classical.ofNonempty)).symm
    | merid a => exact merid_eq_north a)

/-- The suspension of a nonempty type is path-connected. -/
def pathConnectedPath [Nonempty A] (x y : Susp A) : Path x y :=
  Path.mk [Step.mk _ _ ((eq_north x).trans (eq_north y).symm)]
    ((eq_north x).trans (eq_north y).symm)

/-! ## Transport across suspension -/

/-- Transport along a full meridian. -/
theorem transport_fullMeridian {D : Susp A → Sort v} (a : A)
    (x : D north) :
    Path.transport (fullMeridian a) x =
      Eq.recOn (north_eq_south a) x :=
  rfl

/-- Transport along a meridian loop is the identity. -/
theorem transport_meridianLoop {D : Susp A → Sort v} (a b : A)
    (x : D north) :
    Path.transport (meridianLoop a b) x = x := by
  unfold meridianLoop fullMeridian fullMeridianRev
  simp [Path.transport]

/-! ## Double suspension -/

/-- The double suspension `Susp (Susp A)`. -/
abbrev Susp2 (A : Type u) := Susp (Susp A)

/-- North pole of double suspension. -/
def north2 : Susp2 A := north

/-- Double suspension of nonempty type: all elements equal. -/
theorem susp2_eq [Nonempty A] (x y : Susp2 A) : x = y := by
  have : Nonempty (Susp A) := ⟨north⟩
  exact (eq_north x).trans (eq_north y).symm

/-! ## Reduced structure: folding -/

/-- Folding map on raw data. -/
def foldRaw : SuspRaw A → SuspRaw A
  | SuspRaw.north => SuspRaw.north
  | SuspRaw.south => SuspRaw.south
  | SuspRaw.merid _ => SuspRaw.south

/-- Fold is idempotent on raw data. -/
theorem foldRaw_idem (x : SuspRaw A) : foldRaw (foldRaw x) = foldRaw x := by
  cases x <;> rfl

/-! ## CongrArg for suspension paths -/

/-- Mapping a path in the suspension through `map f`. -/
theorem congrArg_map (f : A → B) (a : A) :
    Path.congrArg (map f) (fullMeridian a) =
      Path.mk ((fullMeridian a).steps.map (Step.map (map f)))
              (_root_.congrArg (map f) (fullMeridian a).proof) :=
  rfl

/-- Symmetry of fullMeridian is fullMeridianRev. -/
theorem symm_fullMeridian (a : A) :
    Path.symm (fullMeridian a) = fullMeridianRev a :=
  rfl

/-- Trans of meridian and its reverse is proof-trivial. -/
theorem trans_fullMeridian_rev (a : A) :
    (Path.trans (fullMeridian a) (fullMeridianRev a)).toEq = rfl := by
  simp [fullMeridian, fullMeridianRev]

end Susp

end ComputationalPaths
