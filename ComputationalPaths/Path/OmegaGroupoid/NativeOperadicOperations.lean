import ComputationalPaths.Path.OmegaGroupoid.GlobularEndomorphism

/-!
# Native adjacent operations selected by the operadic contraction

The operations here evaluate actual operations of the native endomorphism
operad. They are not aliases for the independently defined native binary
operations. The comparison cells below keep that distinction explicit.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

namespace NativeOperadic

abbrev carrier (A : Type u) := NativeTower.globular A
abbrev collection (A : Type u) := Endomorphism.collection (carrier A)

noncomputable def one (A : Type u) (n : Nat) : (collection A).operations.Cell n :=
  (Endomorphism.unit (carrier A)).operations.app (n := n) PUnit.unit

theorem one_arity (A : Type u) (n : Nat) :
    (collection A).arity.app (one A n) =
      Pasting.singleton (G := GlobularSet.terminal) (n := n) PUnit.unit :=
  _root_.congrArg (fun f : GlobularSet.Map GlobularSet.terminal Endomorphism.Shapes =>
    f.app (n := n) PUnit.unit) (Endomorphism.unit (carrier A)).arity

/-- Forgetting all labels makes the two boundaries of a pasting shape
equal. The proof follows the recursive hom/chain representation. -/
theorem pasting_boundary_of_subsingleton {G : GlobularSet.{u}}
    (h : ∀ n, Subsingleton (G.Cell n)) {n : Nat} (p : Pasting (n + 1) G) :
    Pasting.source p = Pasting.target p := by
  induction n generalizing G with
  | zero => exact (h 0).elim _ _
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg (fun q => (⟨a, b, q⟩ : Pasting (n + 1) G))
    apply Chain.map_congr
    intro x y d
    exact ih (G := G.hom x y)
      (fun k => ⟨fun p q => Subtype.ext ((h (k + 1)).elim p.val q.val)⟩) d

theorem shape_boundary {n : Nat} (a : Endomorphism.Shapes.{u}.Cell (n + 1)) :
    Endomorphism.Shapes.source a = Endomorphism.Shapes.target a :=
  pasting_boundary_of_subsingleton (fun _ => inferInstanceAs (Subsingleton PUnit)) a

theorem one_source (A : Type u) (n : Nat) :
    (collection A).operations.source (one A (n + 1)) = one A n :=
  (Endomorphism.unit (carrier A)).operations.source_app (n := n) PUnit.unit

theorem one_target (A : Type u) (n : Nat) :
    (collection A).operations.target (one A (n + 1)) = one A n :=
  (Endomorphism.unit (carrier A)).operations.target_app (n := n) PUnit.unit

/-- Standard instructions preserve singleton units exactly and otherwise
lift their recursively chosen boundary instruction through contraction.
This is the recursion of Fujii--Hoshino--Maehara, Definition 2.5.1. -/
noncomputable def instruction (A : Type u) : (n : Nat) →
    (a : Endomorphism.Shapes.{u + 1}.Cell n) →
      { o : (collection A).operations.Cell n // (collection A).arity.app o = a }
  | 0, a => ⟨one A 0, @Subsingleton.elim PUnit _ _ _⟩
  | n + 1, a => by
    classical
    by_cases ha : a = Pasting.singleton (G := GlobularSet.terminal) (n := n + 1) PUnit.unit
    · exact ⟨one A (n + 1), (one_arity A (n + 1)).trans ha.symm⟩
    · let b := instruction A n (Endomorphism.Shapes.source a)
      let p : GlobularSet.LiftingProblem (collection A).arity n :=
        ⟨⟨b.val, b.val, GlobularSet.Parallel.refl _ _⟩, a,
          b.property, b.property.trans (shape_boundary a)⟩
      exact ⟨((Endomorphism.nativeContraction A).lift p).cell,
        ((Endomorphism.nativeContraction A).lift p).arity_cell⟩

theorem instruction_singleton (A : Type u) (n : Nat) :
    (instruction A n (Pasting.singleton (G := GlobularSet.terminal) (n := n) PUnit.unit)).val =
      one A n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [instruction]
    split
    · rfl
    · rename_i h
      exact False.elim (h rfl)

theorem instruction_contraction (A : Type u) {n : Nat}
    (a : Endomorphism.Shapes.{u + 1}.Cell (n + 1))
    (ha : a ≠ Pasting.singleton (G := GlobularSet.terminal) (n := n + 1) PUnit.unit) :
    (instruction A (n + 1) a).val =
      ((Endomorphism.nativeContraction A).lift
        ⟨⟨(instruction A n (Endomorphism.Shapes.source a)).val,
          (instruction A n (Endomorphism.Shapes.source a)).val, GlobularSet.Parallel.refl _ _⟩,
          a, (instruction A n _).property,
          (instruction A n _).property.trans (shape_boundary a)⟩).cell := by
  simp only [instruction]
  split
  · rename_i h
    exact False.elim (ha h)
  · rfl

theorem instruction_boundary (A : Type u) {n : Nat}
    (a : Endomorphism.Shapes.{u + 1}.Cell (n + 1)) :
    (collection A).operations.source (instruction A (n + 1) a).val =
      (instruction A n (Endomorphism.Shapes.source a)).val ∧
    (collection A).operations.target (instruction A (n + 1) a).val =
      (instruction A n (Endomorphism.Shapes.target a)).val := by
  classical
  by_cases ha : a = Pasting.singleton (G := GlobularSet.terminal) (n := n + 1) PUnit.unit
  · subst a
    rw [instruction_singleton]
    have hs := Pasting.source_singleton GlobularSet.terminal (n := n) PUnit.unit
    have ht := Pasting.target_singleton GlobularSet.terminal (n := n) PUnit.unit
    change Pasting.source _ = _ at hs
    change Pasting.target _ = _ at ht
    constructor
    · exact (one_source A n).trans
        ((instruction_singleton A n).symm.trans
          (_root_.congrArg (fun a => (instruction A n a).val) hs.symm))
    · exact (one_target A n).trans
        ((instruction_singleton A n).symm.trans
          (_root_.congrArg (fun a => (instruction A n a).val) ht.symm))
  · simp only [instruction, dif_neg ha]
    constructor
    · exact ((Endomorphism.nativeContraction A).lift _).source_cell
    · exact ((Endomorphism.nativeContraction A).lift _).target_cell.trans
        (_root_.congrArg (fun a => (instruction A n a).val) (shape_boundary a))

/-- A genuine globular section of the operadic arity map, with the
singleton-unit convention built into its recursion. -/
noncomputable def instructions (A : Type u) :
    GlobularSet.Map Endomorphism.Shapes (collection A).operations where
  app {n} a := (instruction A n a).val
  source_app a := (instruction_boundary A a).1
  target_app a := (instruction_boundary A a).2

theorem instructions_arity (A : Type u) :
    GlobularSet.Map.comp (collection A).arity (instructions A) =
      GlobularSet.Map.id Endomorphism.Shapes := by
  apply GlobularSet.Map.ext
  intro n a
  exact (instruction A n a).property

theorem instructions_unit (A : Type u) :
    GlobularSet.Map.comp (instructions A) (Pasting.singletonGlobular GlobularSet.terminal) =
      (Endomorphism.unit (carrier A)).operations := by
  apply GlobularSet.Map.ext
  intro n a
  cases a
  exact instruction_singleton A n

/-- Pair each complete labelled diagram with its standard instruction.
The section property gives the exact arity match. -/
noncomputable def labelledInstructions (A : Type u) :
    GlobularSet.Map (Pasting.globular (carrier A)) ((collection A).application (carrier A)) where
  app {n} p := ⟨⟨(instructions A).app ((GlobularCollection.shape (carrier A)).app p), p⟩,
    (instruction A n _).property⟩
  source_app p := Subtype.ext (Prod.ext
    (((instructions A).source_app _).trans
      (_root_.congrArg (instructions A).app ((GlobularCollection.shape (carrier A)).source_app p))) rfl)
  target_app p := Subtype.ext (Prod.ext
    (((instructions A).target_app _).trans
      (_root_.congrArg (instructions A).app ((GlobularCollection.shape (carrier A)).target_app p))) rfl)

/-- The unbiased standard pasting operation in every dimension. This is
a globular evaluation, not a claim of strict associativity of pasting. -/
noncomputable def standardEvaluation (A : Type u) :
    GlobularSet.Map (Pasting.globular (carrier A)) (carrier A) :=
  GlobularSet.Map.comp (Endomorphism.evaluation (carrier A)) (labelledInstructions A)

theorem standardEvaluation_singleton {A : Type u} {n : Nat} (p : NativeTower.Cell A n) :
    (standardEvaluation A).app (Pasting.singleton p) = p := by
  have hp : (instruction A n ((GlobularCollection.shape (carrier A)).app
      (Pasting.singleton p))).val = one A n :=
    (_root_.congrArg (fun a => (instruction A n a).val)
      (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) p)).trans (instruction_singleton A n)
  have hi : (labelledInstructions A).app (Pasting.singleton p) =
      ((Endomorphism.unit (carrier A)).application (carrier A)).app
        ((GlobularCollection.identityApplicationIn (carrier A)).app p) :=
    Subtype.ext (Prod.ext hp rfl)
  exact (_root_.congrArg (Endomorphism.evaluation (carrier A)).app hi).trans
    (Endomorphism.evaluation_unit_input (carrier A) p)

theorem standardEvaluation_unit (A : Type u) :
    GlobularSet.Map.comp (standardEvaluation A) (Pasting.singletonGlobular (carrier A)) =
      GlobularSet.Map.id (carrier A) := by
  apply GlobularSet.Map.ext
  intro n p
  exact standardEvaluation_singleton p

/-- Choose an operation solely from its arity and the unit boundaries.
This is the adjacent instance of contraction-based pasting instructions. -/
noncomputable def operation {A : Type u} {n : Nat}
    (a : Endomorphism.Shapes.{u + 1}.Cell (n + 1))
    (hs : Endomorphism.Shapes.source a = (collection A).arity.app (one A n))
    (ht : Endomorphism.Shapes.target a = (collection A).arity.app (one A n)) :
    (collection A).operations.Cell (n + 1) :=
  ((Endomorphism.nativeContraction A).lift
    ⟨⟨one A n, one A n, GlobularSet.Parallel.refl _ _⟩, a, hs.symm, ht.symm⟩).cell

theorem operation_boundary {A : Type u} {n : Nat}
    (a : Endomorphism.Shapes.{u + 1}.Cell (n + 1))
    (hs : Endomorphism.Shapes.source a = (collection A).arity.app (one A n))
    (ht : Endomorphism.Shapes.target a = (collection A).arity.app (one A n)) :
    (collection A).operations.source (operation a hs ht) = one A n ∧
      (collection A).operations.target (operation a hs ht) = one A n ∧
      (collection A).arity.app (operation a hs ht) = a := by
  let p : GlobularSet.LiftingProblem (collection A).arity n :=
    ⟨⟨one A n, one A n, GlobularSet.Parallel.refl _ _⟩, a, hs.symm, ht.symm⟩
  exact ⟨((Endomorphism.nativeContraction A).lift p).source_cell,
    ((Endomorphism.nativeContraction A).lift p).target_cell,
    ((Endomorphism.nativeContraction A).lift p).arity_cell⟩

/-- Label a contraction-selected operation with a diagram having singleton
boundaries. No condition is imposed on the diagram's internal labels. -/
noncomputable def input {A : Type u} {n : Nat}
    (d : Pasting (n + 1) (carrier A)) (s t : (carrier A).Cell n)
    (hs : Pasting.source d = Pasting.singleton s)
    (ht : Pasting.target d = Pasting.singleton t) :
    ((collection A).application (carrier A)).Cell (n + 1) := by
  have hsa : Endomorphism.Shapes.source ((GlobularCollection.shape (carrier A)).app d) =
      (collection A).arity.app (one A n) :=
    ((GlobularCollection.shape (carrier A)).source_app d).trans
      ((_root_.congrArg (GlobularCollection.shape (carrier A)).app hs).trans
        ((Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) s).trans (one_arity A n).symm))
  have hta : Endomorphism.Shapes.target ((GlobularCollection.shape (carrier A)).app d) =
      (collection A).arity.app (one A n) :=
    ((GlobularCollection.shape (carrier A)).target_app d).trans
      ((_root_.congrArg (GlobularCollection.shape (carrier A)).app ht).trans
        ((Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) t).trans (one_arity A n).symm))
  exact ⟨⟨operation ((GlobularCollection.shape (carrier A)).app d) hsa hta, d⟩,
    (operation_boundary _ hsa hta).2.2⟩

theorem input_boundary {A : Type u} {n : Nat}
    (d : Pasting (n + 1) (carrier A)) (s t : (carrier A).Cell n)
    (hs : Pasting.source d = Pasting.singleton s)
    (ht : Pasting.target d = Pasting.singleton t) :
    ((collection A).application (carrier A)).source (input d s t hs ht) =
      ((Endomorphism.unit (carrier A)).application (carrier A)).app
        ((GlobularCollection.identityApplicationIn (carrier A)).app s) ∧
    ((collection A).application (carrier A)).target (input d s t hs ht) =
      ((Endomorphism.unit (carrier A)).application (carrier A)).app
        ((GlobularCollection.identityApplicationIn (carrier A)).app t) := by
  have hsa : Endomorphism.Shapes.source ((GlobularCollection.shape (carrier A)).app d) =
      (collection A).arity.app (one A n) :=
    ((GlobularCollection.shape (carrier A)).source_app d).trans
      ((_root_.congrArg (GlobularCollection.shape (carrier A)).app hs).trans
        ((Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) s).trans (one_arity A n).symm))
  have hta : Endomorphism.Shapes.target ((GlobularCollection.shape (carrier A)).app d) =
      (collection A).arity.app (one A n) :=
    ((GlobularCollection.shape (carrier A)).target_app d).trans
      ((_root_.congrArg (GlobularCollection.shape (carrier A)).app ht).trans
        ((Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) t).trans (one_arity A n).symm))
  constructor
  · apply Subtype.ext
    exact Prod.ext (operation_boundary _ hsa hta).1 hs
  · apply Subtype.ext
    exact Prod.ext (operation_boundary _ hsa hta).2.1 ht

noncomputable def evaluate {A : Type u} {n : Nat}
    (d : Pasting (n + 1) (carrier A)) (s t : (carrier A).Cell n)
    (hs : Pasting.source d = Pasting.singleton s)
    (ht : Pasting.target d = Pasting.singleton t) : (carrier A).Cell (n + 1) :=
  (Endomorphism.evaluation (carrier A)).app (input d s t hs ht)

theorem evaluate_boundary {A : Type u} {n : Nat}
    (d : Pasting (n + 1) (carrier A)) (s t : (carrier A).Cell n)
    (hs : Pasting.source d = Pasting.singleton s)
    (ht : Pasting.target d = Pasting.singleton t) :
    NativeTower.source (evaluate d s t hs ht) = s ∧
      NativeTower.target (evaluate d s t hs ht) = t := by
  exact ⟨((Endomorphism.evaluation (carrier A)).source_app _).trans
    ((_root_.congrArg (Endomorphism.evaluation (carrier A)).app (input_boundary d s t hs ht).1).trans
      (Endomorphism.evaluation_unit_input (carrier A) s)),
    ((Endomorphism.evaluation (carrier A)).target_app _).trans
    ((_root_.congrArg (Endomorphism.evaluation (carrier A)).app (input_boundary d s t hs ht).2).trans
      (Endomorphism.evaluation_unit_input (carrier A) t))⟩

noncomputable def identity {A : Type u} {n : Nat} (p : (carrier A).Cell n) :
    (carrier A).Cell (n + 1) :=
  (standardEvaluation A).app (Pasting.identity (Pasting.singleton p))

theorem identity_boundary {A : Type u} {n : Nat} (p : (carrier A).Cell n) :
    NativeTower.source (identity p) = p ∧ NativeTower.target (identity p) = p :=
  ⟨((standardEvaluation A).source_app _).trans
      ((_root_.congrArg (standardEvaluation A).app (Pasting.source_identity _ _)).trans
        (standardEvaluation_singleton p)),
    ((standardEvaluation A).target_app _).trans
      ((_root_.congrArg (standardEvaluation A).app (Pasting.target_identity _ _)).trans
        (standardEvaluation_singleton p))⟩

noncomputable def compose {A : Type u} {n : Nat} (p q : (carrier A).Cell (n + 1))
    (h : NativeTower.target p = NativeTower.source q) : (carrier A).Cell (n + 1) :=
  (standardEvaluation A).app (Pasting.vertical (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.target_singleton _ p).trans
      ((_root_.congrArg Pasting.singleton h).trans (Pasting.source_singleton _ q).symm)))

theorem compose_boundary {A : Type u} {n : Nat} (p q : (carrier A).Cell (n + 1))
    (h : NativeTower.target p = NativeTower.source q) :
    NativeTower.source (compose p q h) = NativeTower.source p ∧
      NativeTower.target (compose p q h) = NativeTower.target q :=
  ⟨((standardEvaluation A).source_app _).trans
      ((_root_.congrArg (standardEvaluation A).app
        ((Pasting.source_vertical _ _ _).trans (Pasting.source_singleton _ p))).trans
          (standardEvaluation_singleton (NativeTower.source p))),
    ((standardEvaluation A).target_app _).trans
      ((_root_.congrArg (standardEvaluation A).app
        ((Pasting.target_vertical _ _ _).trans (Pasting.target_singleton _ q))).trans
          (standardEvaluation_singleton (NativeTower.target q)))⟩

/-- An explicit comparison with the previous native composite; equality
of distinct raw rewrite derivations is not asserted. -/
noncomputable def compareCompose {A : Type u} {n : Nat}
    (p q : (carrier A).Cell (n + 1)) (h : NativeTower.target p = NativeTower.source q) :
    (carrier A).Cell (n + 2) :=
  NativeTower.fillPositive (compose p q h) (NativeTower.compose p q h)
    ((compose_boundary p q h).1.trans (NativeTower.source_compose p q h).symm)
    ((compose_boundary p q h).2.trans (NativeTower.target_compose p q h).symm)

theorem compareCompose_boundary {A : Type u} {n : Nat}
    (p q : (carrier A).Cell (n + 1)) (h : NativeTower.target p = NativeTower.source q) :
    NativeTower.source (A := A) (n := n + 1) (compareCompose p q h) = compose p q h ∧
      NativeTower.target (A := A) (n := n + 1) (compareCompose p q h) = NativeTower.compose p q h :=
  NativeTower.fillPositive_boundary _ _ _ _

noncomputable def compareIdentity {A : Type u} {n : Nat} (p : NativeTower.Cell A n) :
    NativeTower.Cell A (n + 2) :=
  NativeTower.fillPositive (identity p) (NativeTower.identity p)
    ((identity_boundary p).1.trans (NativeTower.source_identity p).symm)
    ((identity_boundary p).2.trans (NativeTower.target_identity p).symm)

theorem compareIdentity_boundary {A : Type u} {n : Nat} (p : NativeTower.Cell A n) :
    NativeTower.source (compareIdentity p) = identity p ∧
      NativeTower.target (compareIdentity p) = NativeTower.identity p :=
  NativeTower.fillPositive_boundary _ _ _ _

/-- The comparison lands in the actual trace composition, with no
replacement by bare equality or a quotient path. -/
theorem compareCompose_paths_target {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    NativeTower.target (A := A) (n := 1)
      (compareCompose (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
        (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl) =
      ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) :=
  (compareCompose_boundary _ _ _).2

theorem compareCompose_three_paths_target {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    NativeTower.target (A := A) (n := 1)
      (compareCompose (n := 0) (ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A))
        (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl) =
      ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) :=
  (compareCompose_boundary _ _ _).2

noncomputable def cancelRight {A : Type u} {n : Nat} (p : NativeTower.Cell A (n + 1)) :
    { r : NativeTower.Cell A (n + 2) //
      NativeTower.source r = compose p (NativeTower.reverse p) (NativeTower.source_reverse p).symm ∧
      NativeTower.target r = identity (NativeTower.source p) } := by
  let l := compose p (NativeTower.reverse p) (NativeTower.source_reverse p).symm
  let r := identity (NativeTower.source p)
  have hs : NativeTower.source l = NativeTower.source r :=
    (compose_boundary _ _ _).1.trans (identity_boundary _).1.symm
  have ht : NativeTower.target l = NativeTower.target r :=
    (compose_boundary _ _ _).2.trans ((NativeTower.target_reverse p).trans (identity_boundary _).2.symm)
  exact ⟨NativeTower.fillPositive l r hs ht, NativeTower.fillPositive_boundary l r hs ht⟩

noncomputable def cancelLeft {A : Type u} {n : Nat} (p : NativeTower.Cell A (n + 1)) :
    { r : NativeTower.Cell A (n + 2) //
      NativeTower.source r = compose (NativeTower.reverse p) p (NativeTower.target_reverse p) ∧
      NativeTower.target r = identity (NativeTower.target p) } := by
  let l := compose (NativeTower.reverse p) p (NativeTower.target_reverse p)
  let r := identity (NativeTower.target p)
  have hs : NativeTower.source l = NativeTower.source r :=
    (compose_boundary _ _ _).1.trans ((NativeTower.source_reverse p).trans (identity_boundary _).1.symm)
  have ht : NativeTower.target l = NativeTower.target r :=
    (compose_boundary _ _ _).2.trans (identity_boundary _).2.symm
  exact ⟨NativeTower.fillPositive l r hs ht, NativeTower.fillPositive_boundary l r hs ht⟩

/-- The coinductive operator now uses the contraction-selected operadic
identities and composites, not the separate native omega-precategory. -/
def InvertibilityStep {A : Type u} (S : NativeTower.CellPredicate A)
    (n : Nat) (p : NativeTower.Cell A (n + 1)) : Prop :=
  ∃ (q : NativeTower.Cell A (n + 1))
    (hs : NativeTower.source q = NativeTower.target p) (ht : NativeTower.target q = NativeTower.source p),
    ∃ (r l : NativeTower.Cell A (n + 2)),
      NativeTower.source r = compose p q hs.symm ∧ NativeTower.target r = identity (NativeTower.source p) ∧
      NativeTower.source l = compose q p ht ∧ NativeTower.target l = identity (NativeTower.target p) ∧
      S (n + 1) r ∧ S (n + 1) l

theorem invertibilityStep_mono {A : Type u} {S T : NativeTower.CellPredicate A}
    (h : ∀ n p, S n p → T n p) {n : Nat} {p : NativeTower.Cell A (n + 1)} :
    InvertibilityStep S n p → InvertibilityStep T n p := by
  rintro ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, sr, sl⟩
  exact ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, h _ _ sr, h _ _ sl⟩

def WeaklyInvertible {A : Type u} (n : Nat) (p : NativeTower.Cell A (n + 1)) : Prop :=
  ∃ S : NativeTower.CellPredicate A, (∀ m c, S m c → InvertibilityStep S m c) ∧ S n p

theorem weaklyInvertible_unfold {A : Type u} {n : Nat} {p : NativeTower.Cell A (n + 1)} :
    WeaklyInvertible n p ↔ InvertibilityStep (WeaklyInvertible (A := A)) n p := by
  constructor
  · rintro ⟨S, closed, hp⟩
    exact invertibilityStep_mono (fun m c hc => ⟨S, closed, hc⟩) (closed n p hp)
  · intro hp
    let T : NativeTower.CellPredicate A := fun m c => InvertibilityStep (WeaklyInvertible (A := A)) m c
    have inclusion : ∀ m c, WeaklyInvertible m c → T m c := by
      rintro m c ⟨S, closed, hc⟩
      exact invertibilityStep_mono (fun k d hd => ⟨S, closed, hd⟩) (closed m c hc)
    exact ⟨T, fun m c hc => invertibilityStep_mono inclusion hc, hp⟩

/-- Every positive-dimensional native cell is coinductively invertible for
the operations actually obtained from the operadic contraction and action. -/
theorem all_cells_weaklyInvertible {A : Type u} (n : Nat) (p : NativeTower.Cell A (n + 1)) :
    WeaklyInvertible n p := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro m c _
  exact ⟨NativeTower.reverse c, NativeTower.source_reverse c, NativeTower.target_reverse c,
    (cancelRight c).val, (cancelLeft c).val,
    (cancelRight c).property.1, (cancelRight c).property.2,
    (cancelLeft c).property.1, (cancelLeft c).property.2, trivial, trivial⟩

end NativeOperadic

end ComputationalPaths.Path.OmegaFoundations
