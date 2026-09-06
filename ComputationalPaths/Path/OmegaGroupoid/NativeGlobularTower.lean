import ComputationalPaths.Path.OmegaGroupoid.GlobularFoundations
import ComputationalPaths.Path.Rewrite.TraceCollapse

/-!
# A recursive globular extension of the raw computational-path two-skeleton

Dimensions zero through two preserve the actual objects, `Path` traces and
Type-valued `RwEq` derivations. Above dimension two we explicitly adjoin one
cell for each parallel pair, recursively. This is a coskeletal extension,
not a theorem that native higher rewrite syntax is complete or that these
added cells are derivable in that syntax.

No operadic action or weak omega-groupoid theorem is asserted in this file.
The eventual action must still be built and its algebra laws verified.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

namespace NativeTower

/-- Two consecutive levels, with the boundary maps at this stage. -/
structure Stage where
  objects : Type (u + 1)
  arrows : Type (u + 1)
  source : arrows → objects
  target : arrows → objects

/-- The next level consists of parallel pairs at the previous level.
The previous arrows, not a fixed type repeated at every dimension, become
the new objects. -/
def Stage.next (S : Stage.{u}) : Stage.{u} where
  objects := S.arrows
  arrows := Σ p : S.arrows, { q : S.arrows // S.source p = S.source q ∧ S.target p = S.target q }
  source d := d.1
  target d := d.2.1

def Stage.grow (S : Stage.{u}) : Nat → Stage.{u}
  | 0 => S
  | n + 1 => (S.grow n).next

/-- The starting stage retains the entire native two-cell derivation. -/
def base (A : Type u) : Stage.{u} where
  objects := ULift.{u + 1} (PathOne A)
  arrows := PathTwo A
  source d := ULift.up (sourceTwo d)
  target d := ULift.up (targetTwo d)

def Cell (A : Type u) : Nat → Type (u + 1)
  | 0 => ULift.{u + 1} A
  | 1 => ULift.{u + 1} (PathOne A)
  | n + 2 => ((base A).grow n).arrows

def source {A : Type u} : {n : Nat} → Cell A (n + 1) → Cell A n
  | 0, p => ULift.up (sourceOne p.down)
  | 1, p => ULift.up (sourceTwo p)
  | _ + 2, p => p.1

def target {A : Type u} : {n : Nat} → Cell A (n + 1) → Cell A n
  | 0, p => ULift.up (targetOne p.down)
  | 1, p => ULift.up (targetTwo p)
  | _ + 2, p => p.2.1

theorem source_source {A : Type u} {n : Nat} (p : Cell A (n + 2)) :
    source (source p) = source (target p) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact p.2.2.1
    | succ n => exact p.2.2.1

theorem target_source {A : Type u} {n : Nat} (p : Cell A (n + 2)) :
    target (source p) = target (target p) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact p.2.2.2
    | succ n => exact p.2.2.2

def globular (A : Type u) : GlobularSet.{u + 1} where
  Cell := Cell A
  source := source
  target := target
  source_source := source_source
  target_source := target_source

/-- Exact equivalences at all three prescribed native levels. -/
def realizes (A : Type u) : RealizesPathSkeleton (globular A) A where
  objects := Equiv.ulift
  paths := Equiv.ulift
  rewrites := Equiv.refl _
  source_paths _ := rfl
  target_paths _ := rfl
  source_rewrites _ := rfl
  target_rewrites _ := rfl

/-- A chosen, explicitly adjoined three-cell between parallel raw rewrites. -/
def thirdCell {A : Type u} (p q : PathTwo A)
    (hs : sourceTwo p = sourceTwo q) (ht : targetTwo p = targetTwo q) : Cell A 3 :=
  ⟨p, q, _root_.congrArg ULift.up hs, _root_.congrArg ULift.up ht⟩

/-- The explicitly adjoined filler at every dimension above the native
two-skeleton. Its boundary consists of the actual preceding cells. -/
def higherCell {A : Type u} : {n : Nat} → (p q : Cell A (n + 2)) →
    source p = source q → target p = target q → Cell A (n + 3)
  | 0, p, q, hs, ht => ⟨p, q, hs, ht⟩
  | _ + 1, p, q, hs, ht => ⟨p, q, hs, ht⟩

theorem source_higherCell {A : Type u} {n : Nat} (p q : Cell A (n + 2))
    (hs : source p = source q) (ht : target p = target q) :
    source (higherCell p q hs ht) = p := by cases n <;> rfl

theorem target_higherCell {A : Type u} {n : Nat} (p q : Cell A (n + 2))
    (hs : source p = source q) (ht : target p = target q) :
    target (higherCell p q hs ht) = q := by cases n <;> rfl

/-- Every parallel pair of positive-dimensional native cells has a chosen
filler. At dimension two this uses the existing rewrite-totality derivation;
above it this uses the explicitly adjoined coskeletal cells. This does not
fill unrelated objects and is not yet an operadic contraction. -/
noncomputable def fillPositive {A : Type u} : {n : Nat} → (p q : Cell A (n + 1)) →
    source p = source q → target p = target q → Cell A (n + 2)
  | 0, p, q, hs, ht => by
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg ULift.down hs
    have hb : b = d := _root_.congrArg ULift.down ht
    cases ha
    cases hb
    exact ⟨a, b, p, q, QuotientPathInduction.rweqAny p q⟩
  | n + 1, p, q, hs, ht => higherCell p q hs ht

theorem fillPositive_boundary {A : Type u} {n : Nat} (p q : Cell A (n + 1))
    (hs : source p = source q) (ht : target p = target q) :
    source (fillPositive p q hs ht) = p ∧ target (fillPositive p q hs ht) = q := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have ha : a = c := _root_.congrArg ULift.down hs
    have hb : b = d := _root_.congrArg ULift.down ht
    cases ha
    cases hb
    exact ⟨rfl, rfl⟩
  | succ n => exact ⟨source_higherCell p q hs ht, target_higherCell p q hs ht⟩

theorem fillPositive_paths {A : Type u} {a b : A} (p q : Path a b) :
    fillPositive (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
      (ULift.up (⟨a, b, q⟩ : PathOne A)) rfl rfl =
      (⟨a, b, p, q, QuotientPathInduction.rweqAny p q⟩ : Cell A 2) := rfl

/-- Fill an actual globular boundary above dimension zero. The full
raw derivations remain in the carrier; only inhabitation is asserted. -/
noncomputable def fillPositiveBoundary {A : Type u} {n : Nat}
    (b : (globular A).Boundary (n + 1)) : (globular A).CellOver b := by
  have hh : source b.left = source b.right ∧ target b.left = target b.right := by
    cases b.parallel with
    | cells hs ht => exact ⟨hs, ht⟩
  exact ⟨fillPositive b.left b.right hh.1 hh.2,
    (fillPositive_boundary b.left b.right hh.1 hh.2).1,
    (fillPositive_boundary b.left b.right hh.1 hh.2).2⟩

/-- Semantic limitation: in this chosen extension, cells of dimension at
least three are uniquely determined by their two boundaries. This is not a
claim about the native higher-derivation syntax. -/
theorem higher_ext {A : Type u} {n : Nat} (p q : Cell A (n + 3))
    (hs : source p = source q) (ht : target p = target q) : p = q := by
  rcases p with ⟨p, p', hp⟩
  rcases q with ⟨q, q', hq⟩
  change p = q at hs
  cases hs
  apply _root_.congrArg (Sigma.mk p)
  exact Subtype.ext ht

noncomputable def identity {A : Type u} : {n : Nat} → Cell A n → Cell A (n + 1)
  | 0, a => ULift.up ⟨a.down, a.down, Path.refl a.down⟩
  | 1, p => ⟨p.down.1, p.down.2.1, p.down.2.2, p.down.2.2, RwEq.refl _⟩
  | _ + 2, p => higherCell p p rfl rfl

theorem source_identity {A : Type u} {n : Nat} (p : Cell A n) : source (identity p) = p := by
  cases n with
  | zero => cases p; rfl
  | succ n =>
    cases n with
    | zero => cases p; rfl
    | succ n => exact source_higherCell p p rfl rfl

theorem target_identity {A : Type u} {n : Nat} (p : Cell A n) : target (identity p) = p := by
  cases n with
  | zero => cases p; rfl
  | succ n =>
    cases n with
    | zero => cases p; rfl
    | succ n => exact target_higherCell p p rfl rfl

noncomputable def identities (A : Type u) : GlobularSet.Identities (globular A) where
  identity := identity
  source_identity := source_identity
  target_identity := target_identity

/-- Reversal retains the native path/derivation constructors in dimensions
one and two. Higher reversal uses the explicitly chosen extension. -/
noncomputable def reverse {A : Type u} : {n : Nat} → Cell A (n + 1) → Cell A (n + 1)
  | 0, p => ULift.up ⟨p.down.2.1, p.down.1, Path.symm p.down.2.2⟩
  | 1, p => ⟨p.1, p.2.1, p.2.2.2.1, p.2.2.1, RwEq.symm p.2.2.2.2⟩
  | _ + 2, p => higherCell (target p) (source p) (source_source p).symm (target_source p).symm

theorem source_reverse {A : Type u} {n : Nat} (p : Cell A (n + 1)) : source (reverse p) = target p := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact source_higherCell _ _ _ _

theorem target_reverse {A : Type u} {n : Nat} (p : Cell A (n + 1)) : target (reverse p) = source p := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact target_higherCell _ _ _ _

/-- Adjacent composition keeps `Path.trans` and `RwEq.trans` literally.
Only dimensions above the raw two-skeleton use adjoined higher cells. -/
noncomputable def compose {A : Type u} {n : Nat} (p q : Cell A (n + 1))
    (h : target p = source q) : Cell A (n + 1) := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have hc : b = c := _root_.congrArg ULift.down h
    cases hc
    exact ULift.up ⟨a, d, Path.trans p q⟩
  | succ n =>
    cases n with
    | zero =>
      rcases p with ⟨a, b, p, p', hp⟩
      rcases q with ⟨c, d, q, q', hq⟩
      have he : (⟨a, b, p'⟩ : PathOne A) = ⟨c, d, q⟩ := _root_.congrArg ULift.down h
      have ha : a = c := _root_.congrArg Sigma.fst he
      cases ha
      have hb : b = d := _root_.congrArg (fun z => z.2.1) he
      cases hb
      have hpq : p' = q := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
      cases hpq
      exact ⟨a, b, p, q', RwEq.trans hp hq⟩
    | succ n =>
      exact higherCell (source p) (target q)
        ((source_source p).trans ((_root_.congrArg source h).trans (source_source q)))
        ((target_source p).trans ((_root_.congrArg target h).trans (target_source q)))

theorem compose_boundary {A : Type u} {n : Nat} (p q : Cell A (n + 1))
    (h : target p = source q) : source (compose p q h) = source p ∧ target (compose p q h) = target q := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    have hc : b = c := _root_.congrArg ULift.down h
    cases hc
    exact ⟨rfl, rfl⟩
  | succ n =>
    cases n with
    | zero =>
      rcases p with ⟨a, b, p, p', hp⟩
      rcases q with ⟨c, d, q, q', hq⟩
      have he : (⟨a, b, p'⟩ : PathOne A) = ⟨c, d, q⟩ := _root_.congrArg ULift.down h
      have ha : a = c := _root_.congrArg Sigma.fst he
      cases ha
      have hb : b = d := _root_.congrArg (fun z => z.2.1) he
      cases hb
      have hpq : p' = q := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
      cases hpq
      exact ⟨rfl, rfl⟩
    | succ n => exact ⟨source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

theorem source_compose {A : Type u} {n : Nat} (p q : Cell A (n + 1))
    (h : target p = source q) : source (compose p q h) = source p := (compose_boundary p q h).1

theorem target_compose {A : Type u} {n : Nat} (p q : Cell A (n + 1))
    (h : target p = source q) : target (compose p q h) = target q := (compose_boundary p q h).2

theorem compose_paths {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    compose (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl =
      ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) := rfl

theorem compose_rewrites {A : Type u} {a b : A} {p q r : Path a b} (h : RwEq p q) (k : RwEq q r) :
    compose (A := A) (n := 1) (⟨a, b, p, q, h⟩ : Cell A 2) (⟨a, b, q, r, k⟩ : Cell A 2) rfl =
      (⟨a, b, p, r, RwEq.trans h k⟩ : Cell A 2) := rfl

/-- Cancellation at every positive dimension. At dimension one the witness
is a native primitive rewrite; higher witnesses belong to the declared
coskeletal extension. Used below to prove coinductive invertibility. -/
noncomputable def cancelRight {A : Type u} {n : Nat} (p : Cell A (n + 1)) :
    { c : Cell A (n + 2) // source c = compose p (reverse p) (source_reverse p).symm ∧
      target c = identity (source p) } := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ⟨⟨a, a, Path.trans p (Path.symm p), Path.refl a, RwEq.step (Step.trans_symm p)⟩, rfl, rfl⟩
  | succ n =>
    let l := compose p (reverse p) (source_reverse p).symm
    let r := identity (source p)
    have hs : source l = source r :=
      (source_compose p (reverse p) _).trans (source_identity (source p)).symm
    have ht : target l = target r :=
      (target_compose p (reverse p) _).trans ((target_reverse p).trans (target_identity (source p)).symm)
    exact ⟨higherCell l r hs ht, source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

noncomputable def cancelLeft {A : Type u} {n : Nat} (p : Cell A (n + 1)) :
    { c : Cell A (n + 2) // source c = compose (reverse p) p (target_reverse p) ∧
      target c = identity (target p) } := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ⟨⟨b, b, Path.trans (Path.symm p) p, Path.refl b, RwEq.step (Step.symm_trans p)⟩, rfl, rfl⟩
  | succ n =>
    let l := compose (reverse p) p (target_reverse p)
    let r := identity (target p)
    have hs : source l = source r :=
      (source_compose (reverse p) p _).trans ((source_reverse p).trans (source_identity (target p)).symm)
    have ht : target l = target r :=
      (target_compose (reverse p) p _).trans (target_identity (target p)).symm
    exact ⟨higherCell l r hs ht, source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

theorem cancelRight_paths {A : Type u} {a b : A} (p : Path a b) :
    (cancelRight (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))).val.2.2.2.2 =
      RwEq.step (Step.trans_symm p) := rfl

theorem cancelLeft_paths {A : Type u} {a b : A} (p : Path a b) :
    (cancelLeft (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))).val.2.2.2.2 =
      RwEq.step (Step.symm_trans p) := rfl

/-- Associativity is witnessed one dimension higher, not imposed as equality
of the raw derivation syntax. At dimension one the witness is the primitive
native associator. -/
noncomputable def composeAssociator {A : Type u} {n : Nat}
    (p q r : Cell A (n + 1)) (hpq : target p = source q) (hqr : target q = source r) :
    { c : Cell A (n + 2) //
      source c = compose (compose p q hpq) r ((target_compose p q hpq).trans hqr) ∧
      target c = compose p (compose q r hqr) (hpq.trans (source_compose q r hqr).symm) } := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    rcases q with ⟨c, d, q⟩
    rcases r with ⟨e, f, r⟩
    have hbc : b = c := _root_.congrArg ULift.down hpq
    have hde : d = e := _root_.congrArg ULift.down hqr
    cases hbc
    cases hde
    exact ⟨associatorCell p q r, rfl, rfl⟩
  | succ n =>
    let l := compose (compose p q hpq) r ((target_compose p q hpq).trans hqr)
    let t := compose p (compose q r hqr) (hpq.trans (source_compose q r hqr).symm)
    have hs : source l = source t :=
      ((source_compose _ _ _).trans (source_compose p q hpq)).trans
        (source_compose p (compose q r hqr) _).symm
    have ht : target l = target t :=
      (target_compose (compose p q hpq) r _).trans
        ((target_compose _ _ _).trans (target_compose q r hqr)).symm
    exact ⟨higherCell l t hs ht, source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

noncomputable def leftUnitor {A : Type u} {n : Nat} (p : Cell A (n + 1)) :
    { c : Cell A (n + 2) //
      source c = compose (identity (source p)) p (target_identity (source p)) ∧ target c = p } := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ⟨⟨a, b, Path.trans (Path.refl a) p, p,
      RwEq.step (Step.trans_refl_left p)⟩, rfl, rfl⟩
  | succ n =>
    let l := compose (identity (source p)) p (target_identity (source p))
    have hs : source l = source p :=
      (source_compose _ _ _).trans (source_identity (source p))
    have ht : target l = target p := target_compose _ _ _
    exact ⟨higherCell l p hs ht, source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

noncomputable def rightUnitor {A : Type u} {n : Nat} (p : Cell A (n + 1)) :
    { c : Cell A (n + 2) //
      source c = compose p (identity (target p)) (source_identity (target p)).symm ∧ target c = p } := by
  cases n with
  | zero =>
    rcases p with ⟨a, b, p⟩
    exact ⟨⟨a, b, Path.trans p (Path.refl b), p,
      RwEq.step (Step.trans_refl_right p)⟩, rfl, rfl⟩
  | succ n =>
    let l := compose p (identity (target p)) (source_identity (target p)).symm
    have hs : source l = source p := source_compose _ _ _
    have ht : target l = target p :=
      (target_compose _ _ _).trans (target_identity (target p))
    exact ⟨higherCell l p hs ht, source_higherCell _ _ _ _, target_higherCell _ _ _ _⟩

theorem composeAssociator_paths {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (composeAssociator (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A))
      (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl rfl).val = associatorCell p q r := rfl

theorem leftUnitor_paths {A : Type u} {a b : A} (p : Path a b) :
    (leftUnitor (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))).val.2.2.2.2 =
      RwEq.step (Step.trans_refl_left p) := rfl

theorem rightUnitor_paths {A : Type u} {a b : A} (p : Path a b) :
    (rightUnitor (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))).val.2.2.2.2 =
      RwEq.step (Step.trans_refl_right p) := rfl

/-- A predicate on all positive-dimensional cells, with no finite depth bound. -/
def CellPredicate (A : Type u) := ∀ n : Nat, Cell A (n + 1) → Prop

/-- The coinductive invertibility operator: both cancellation witnesses must
belong to the predicate at the next dimension. The reverse cell itself need
not belong to it. This is Definition 3.1.1 of Fujii--Hoshino--Maehara,
specialized to this omega-precategory, not an assertion of an operadic action. -/
def InvertibilityStep {A : Type u} (S : CellPredicate A)
    (n : Nat) (p : Cell A (n + 1)) : Prop :=
  ∃ (q : Cell A (n + 1)) (hs : source q = target p) (ht : target q = source p),
    ∃ (r l : Cell A (n + 2)),
      source r = compose p q hs.symm ∧ target r = identity (source p) ∧
      source l = compose q p ht ∧ target l = identity (target p) ∧
      S (n + 1) r ∧ S (n + 1) l

theorem invertibilityStep_mono {A : Type u} {S T : CellPredicate A}
    (h : ∀ n p, S n p → T n p) {n : Nat} {p : Cell A (n + 1)} :
    InvertibilityStep S n p → InvertibilityStep T n p := by
  rintro ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, sr, sl⟩
  exact ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, h _ _ sr, h _ _ sl⟩

/-- Greatest postfixed point, expressed as the union of all postfixed
predicates. In particular, this is not a finite-fuel approximation. -/
def WeaklyInvertible {A : Type u} (n : Nat) (p : Cell A (n + 1)) : Prop :=
  ∃ S : CellPredicate A, (∀ m c, S m c → InvertibilityStep S m c) ∧ S n p

theorem weaklyInvertible_coinduction {A : Type u} (S : CellPredicate A)
    (closed : ∀ n p, S n p → InvertibilityStep S n p)
    {n : Nat} {p : Cell A (n + 1)} (hp : S n p) : WeaklyInvertible n p :=
  ⟨S, closed, hp⟩

theorem weaklyInvertible_unfold {A : Type u} {n : Nat} {p : Cell A (n + 1)} :
    WeaklyInvertible n p ↔ InvertibilityStep (WeaklyInvertible (A := A)) n p := by
  constructor
  · rintro ⟨S, closed, hp⟩
    exact invertibilityStep_mono (fun m c hc => ⟨S, closed, hc⟩) (closed n p hp)
  · intro hp
    let T : CellPredicate A := fun m c => InvertibilityStep (WeaklyInvertible (A := A)) m c
    have inclusion : ∀ m c, WeaklyInvertible m c → T m c := by
      rintro m c ⟨S, closed, hc⟩
      exact invertibilityStep_mono (fun k d hd => ⟨S, closed, hd⟩) (closed m c hc)
    exact ⟨T, fun m c hc => invertibilityStep_mono inclusion hc, hp⟩

/-- Every positive cell of the specified native/coskeletal omega-precategory
is weakly invertible. The same postfixed predicate contains the cancellation
witnesses, their witnesses, and so on at arbitrarily high dimensions. -/
theorem all_cells_weaklyInvertible {A : Type u} (n : Nat) (p : Cell A (n + 1)) :
    WeaklyInvertible n p := by
  apply weaklyInvertible_coinduction (fun _ _ => True) ?_ trivial
  intro m c _
  exact ⟨reverse c, source_reverse c, target_reverse c,
    (cancelRight c).val, (cancelLeft c).val,
    (cancelRight c).property.1, (cancelRight c).property.2,
    (cancelLeft c).property.1, (cancelLeft c).property.2, trivial, trivial⟩

/-- The existing primitive associator lands in the exact native second level. -/
noncomputable def associator {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Cell A 2 := associatorCell p q r

theorem associator_source {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    source (associator p q r) = ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) := rfl

theorem associator_target {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    target (associator p q r) = ULift.up (⟨a, d, Path.trans p (Path.trans q r)⟩ : PathOne A) := rfl

/-- The raw derivation in the embedded associator is the original primitive
`Step.trans_assoc`, not a proof selected from totality of `RwEq`. -/
theorem associator_derivation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (associator p q r).2.2.2.2 = RwEq.step (Step.trans_assoc p q r) := rfl

/-- The exact native second level has not been quotiented: even reflexivity
and its syntactic composite remain different cells. -/
theorem distinct_rewrite_cells {A : Type u} {a b : A} (p : Path a b) :
    (⟨a, b, p, p, RwEq.refl p⟩ : Cell A 2) ≠
      (⟨a, b, p, p, RwEq.trans (RwEq.refl p) (RwEq.refl p)⟩ : Cell A 2) := by
  intro h
  have h₁ := eq_of_heq (Sigma.mk.inj h).2
  have h₂ := eq_of_heq (Sigma.mk.inj h₁).2
  have h₃ := eq_of_heq (Sigma.mk.inj h₂).2
  have h₄ := eq_of_heq (Sigma.mk.inj h₃).2
  cases h₄

end NativeTower

end ComputationalPaths.Path.OmegaFoundations
