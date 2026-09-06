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

/-- Standard instructions can label diagrams of operations as well as
diagrams of native cells, which is needed for nested operadic substitution. -/
noncomputable def labelledInstructionsOn (A : Type u) (G : GlobularSet.{u + 1}) :
    GlobularSet.Map (Pasting.globular G) ((collection A).application G) where
  app {n} p := ⟨⟨(instructions A).app ((GlobularCollection.shape G).app p), p⟩,
    (instruction A n _).property⟩
  source_app p := Subtype.ext (Prod.ext
    (((instructions A).source_app _).trans
      (_root_.congrArg (instructions A).app ((GlobularCollection.shape G).source_app p))) rfl)
  target_app p := Subtype.ext (Prod.ext
    (((instructions A).target_app _).trans
      (_root_.congrArg (instructions A).app ((GlobularCollection.shape G).target_app p))) rfl)

theorem labelledInstructionsOn_natural {A : Type u} {G H : GlobularSet.{u + 1}}
    (f : GlobularSet.Map G H) {n : Nat} (d : Pasting n G) :
    ((collection A).map f).app ((labelledInstructionsOn A G).app d) =
      (labelledInstructionsOn A H).app (Pasting.map f d) :=
  Subtype.ext (Prod.ext
    (_root_.congrArg (instructions A).app (GlobularCollection.shape_map f d).symm) rfl)

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

theorem standardEvaluation_one_nonsingleton {A : Type u}
    (p : Pasting 1 (carrier A))
    (h : (GlobularCollection.shape (carrier A)).app (n := 1) p ≠
      Pasting.singleton (G := GlobularSet.terminal) (n := 1) PUnit.unit) :
    (standardEvaluation A).app (n := 1) p =
      (Endomorphism.nativeOne A ((GlobularCollection.shape (carrier A)).app p)).eval p rfl := by
  have ho : (instruction A 1 ((GlobularCollection.shape (carrier A)).app p)).val =
      Endomorphism.nativeOne A ((GlobularCollection.shape (carrier A)).app p) :=
    instruction_contraction A _ h
  have hi : (labelledInstructions A).app (n := 1) p =
      (⟨⟨Endomorphism.nativeOne A ((GlobularCollection.shape (carrier A)).app p), p⟩, rfl⟩ :
        ((collection A).application (carrier A)).Cell 1) := Subtype.ext (Prod.ext ho rfl)
  exact _root_.congrArg ((Endomorphism.evaluation (carrier A)).app (n := 1)) hi

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

/-- The two-singleton input diagram at any lower composition axis. -/
noncomputable def binaryDiagramOn (G : GlobularSet.{u + 1}) {n : Nat} (c : Pasting.Cut n)
    (p q : G.Cell n)
    (h : Pasting.CutBoundary.target c G p = Pasting.CutBoundary.source c G q) : Pasting n G :=
  (Pasting.cutOperations G).compose c (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c (Pasting.singletonGlobular G) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
        (Pasting.CutBoundary.source_map c (Pasting.singletonGlobular G) q).symm))

theorem binaryDiagramOn_map {G H : GlobularSet.{u + 1}} (f : GlobularSet.Map G H)
    {n : Nat} (c : Pasting.Cut n) (p q : G.Cell n) h h' :
    Pasting.map f (binaryDiagramOn G c p q h) = binaryDiagramOn H c (f.app p) (f.app q) h' := by
  have hm := (Pasting.CutBoundary.target_map c (Pasting.mapGlobular f) (Pasting.singleton p)).trans
    ((_root_.congrArg (Pasting.mapGlobular f).app
      ((Pasting.CutBoundary.target_map c (Pasting.singletonGlobular G) p).trans
        ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
          (Pasting.CutBoundary.source_map c (Pasting.singletonGlobular G) q).symm))).trans
      (Pasting.CutBoundary.source_map c (Pasting.mapGlobular f) (Pasting.singleton q)).symm)
  exact ((Pasting.mapGlobular_preserves f).compose c _ _ _ hm).trans
    (eq_of_heq ((Pasting.CutModel.free H).compose_heq rfl c c rfl _ _ _ _
      (heq_of_eq (Pasting.map_singleton f p)) (heq_of_eq (Pasting.map_singleton f q)) hm _))

noncomputable def binaryDiagram {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell n)
    (h : Pasting.CutBoundary.target c (carrier A) p = Pasting.CutBoundary.source c (carrier A) q) :
    Pasting n (carrier A) :=
  (Pasting.cutOperations (carrier A)).compose c (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c (Pasting.singletonGlobular (carrier A)) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular (carrier A)).app h).trans
        (Pasting.CutBoundary.source_map c (Pasting.singletonGlobular (carrier A)) q).symm))

/-- Standard operadic composition at every axis, not just the adjacent one.
The complete binary diagram is evaluated by the selected operadic instruction. -/
noncomputable def composeAt {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell n)
    (h : Pasting.CutBoundary.target c (carrier A) p = Pasting.CutBoundary.source c (carrier A) q) :
    (carrier A).Cell n := (standardEvaluation A).app (binaryDiagram c p q h)

theorem composeAt_congr {A : Type u} {n : Nat} (c : Pasting.Cut n)
    {p q p' q' : (carrier A).Cell n} (hp : p = p') (hq : q = q') h h' :
    composeAt c p q h = composeAt c p' q' h' := by
  cases hp
  cases hq
  rfl

theorem binaryDiagram_source {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell (n + 1)) h h' :
    (Pasting.globular (carrier A)).source (binaryDiagram c.up p q h) =
      binaryDiagram c (NativeTower.source p) (NativeTower.source q) h' := by
  let F := Pasting.CutModel.free (carrier A)
  have hm := Pasting.CutBoundary.source_matching (Pasting.globular (carrier A)) c
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c.up (Pasting.singletonGlobular (carrier A)) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular (carrier A)).app h).trans
        (Pasting.CutBoundary.source_map c.up (Pasting.singletonGlobular (carrier A)) q).symm))
  exact (F.compatible.source_compose c.raise_up _ _ _ hm).trans
    (eq_of_heq (F.compose_heq rfl c c rfl _ _ _ _
      (heq_of_eq (Pasting.source_singleton _ p)) (heq_of_eq (Pasting.source_singleton _ q)) hm _))

theorem binaryDiagram_target {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell (n + 1)) h h' :
    (Pasting.globular (carrier A)).target (binaryDiagram c.up p q h) =
      binaryDiagram c (NativeTower.target p) (NativeTower.target q) h' := by
  let F := Pasting.CutModel.free (carrier A)
  have hm := Pasting.CutBoundary.target_matching (Pasting.globular (carrier A)) c
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c.up (Pasting.singletonGlobular (carrier A)) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular (carrier A)).app h).trans
        (Pasting.CutBoundary.source_map c.up (Pasting.singletonGlobular (carrier A)) q).symm))
  exact (F.compatible.target_compose c.raise_up _ _ _ hm).trans
    (eq_of_heq (F.compose_heq rfl c c rfl _ _ _ _
      (heq_of_eq (Pasting.target_singleton _ p)) (heq_of_eq (Pasting.target_singleton _ q)) hm _))

theorem composeAt_source {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell (n + 1)) h h' :
    NativeTower.source (composeAt c.up p q h) =
      composeAt c (NativeTower.source p) (NativeTower.source q) h' :=
  ((standardEvaluation A).source_app _).trans
    (_root_.congrArg (standardEvaluation A).app (binaryDiagram_source c p q h h'))

theorem composeAt_target {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (carrier A).Cell (n + 1)) h h' :
    NativeTower.target (composeAt c.up p q h) =
      composeAt c (NativeTower.target p) (NativeTower.target q) h' :=
  ((standardEvaluation A).target_app _).trans
    (_root_.congrArg (standardEvaluation A).app (binaryDiagram_target c p q h h'))

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

set_option backward.isDefEq.respectTransparency.types false in
/-- The standard operadic binary operation preserves the original
one-dimensional trace concatenation exactly. -/
theorem compose_paths {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    compose (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
      (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl =
        ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) := by
  let d : Pasting 1 (carrier A) := Pasting.vertical
    (Pasting.singleton (G := carrier A) (n := 1) (ULift.up (⟨a, b, p⟩ : PathOne A)))
    (Pasting.singleton (G := carrier A) (n := 1) (ULift.up (⟨b, c, q⟩ : PathOne A))) rfl
  have hd : (GlobularCollection.shape (carrier A)).app (n := 1) d ≠
      Pasting.singleton (G := GlobularSet.terminal) (n := 1) PUnit.unit := by
    intro h
    have hc := _root_.congrArg (Pasting.atom? (G := GlobularSet.terminal) (n := 1)) h
    change none = some PUnit.unit at hc
    cases hc
  change (standardEvaluation A).app (n := 1) d = _
  refine (standardEvaluation_one_nonsingleton d hd).trans ?_
  have andRec {P Q : Prop} (h : P ∧ Q) (x : Path a b) :
      And.rec (fun _ _ => x) h = x := by cases h; rfl
  have andRec' {P Q : Prop} (h : P ∧ Q) (x : Path b c) :
      And.rec (fun _ _ => x) h = x := by cases h; rfl
  simp [Endomorphism.nativeOne, d, Pasting.vertical, Pasting.singleton,
    Pasting.pack, Pasting.horizontal, Chain.single, Chain.append,
    Endomorphism.nativeChain, Endomorphism.nativeEdge,
    carrier, id, NativeTower.globular, GlobularSet.sourceZero, GlobularSet.targetZero,
    NativeTower.source, NativeTower.target, sourceOne, targetOne, NativeTower.Cell]
  simp only [andRec, andRec']

theorem composeAt_paths {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    composeAt (A := A) (.bottom : Pasting.Cut 1)
      (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl =
        ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) := by
  change compose (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
    (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl = _
  exact compose_paths p q

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

/-- Apply an actual endomorphism-operad operation to a complete labelled
diagram, retaining its arity equation. -/
noncomputable def applyOperation {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell n) (d : Pasting n (carrier A))
    (h : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app d) :
    NativeTower.Cell A n := (Endomorphism.evaluation (carrier A)).app ⟨⟨o, d⟩, h⟩

theorem applyOperation_congr {A : Type u} {n : Nat}
    {o o' : (collection A).operations.Cell n} {d d' : Pasting n (carrier A)}
    (ho : o = o') (hd : d = d') h h' : applyOperation o d h = applyOperation o' d' h' := by
  cases ho
  cases hd
  rfl

/-- A coherence lifting problem has operation boundaries and a specified
pasting arity. It is not a request to fill arbitrary carrier cells. -/
def coherenceProblem {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting (n + 1) (carrier A))
    (hs : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app (Pasting.source d))
    (ht : (collection A).arity.app r = (GlobularCollection.shape (carrier A)).app (Pasting.target d)) :
    GlobularSet.LiftingProblem (collection A).arity n :=
  ⟨⟨o, r, hp⟩, (GlobularCollection.shape (carrier A)).app d,
    hs.trans ((GlobularCollection.shape (carrier A)).source_app d).symm,
    ht.trans ((GlobularCollection.shape (carrier A)).target_app d).symm⟩

noncomputable def coherenceLift {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting (n + 1) (carrier A)) hs ht :
    GlobularSet.Lift (coherenceProblem o r hp d hs ht) :=
  (Endomorphism.nativeContraction A).lift (coherenceProblem o r hp d hs ht)

noncomputable def coherenceInput {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting (n + 1) (carrier A))
    (hs : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app (Pasting.source d))
    (ht : (collection A).arity.app r = (GlobularCollection.shape (carrier A)).app (Pasting.target d)) :
    ((collection A).application (carrier A)).Cell (n + 1) :=
  ⟨⟨(coherenceLift o r hp d hs ht).cell, d⟩, (coherenceLift o r hp d hs ht).arity_cell⟩

/-- Evaluate the operad's chosen contraction, through its verified action. -/
noncomputable def coherenceCell {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting (n + 1) (carrier A))
    (hs : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app (Pasting.source d))
    (ht : (collection A).arity.app r = (GlobularCollection.shape (carrier A)).app (Pasting.target d)) :
    NativeTower.Cell A (n + 1) :=
  (Endomorphism.evaluation (carrier A)).app (coherenceInput o r hp d hs ht)

theorem coherenceCell_boundary {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting (n + 1) (carrier A)) hs ht :
    NativeTower.source (coherenceCell o r hp d hs ht) = applyOperation o (Pasting.source d) hs ∧
      NativeTower.target (coherenceCell o r hp d hs ht) = applyOperation r (Pasting.target d) ht := by
  have hsource : ((collection A).application (carrier A)).source (coherenceInput o r hp d hs ht) =
      ⟨⟨o, Pasting.source d⟩, hs⟩ :=
    Subtype.ext (Prod.ext (coherenceLift o r hp d hs ht).source_cell rfl)
  have htarget : ((collection A).application (carrier A)).target (coherenceInput o r hp d hs ht) =
      ⟨⟨r, Pasting.target d⟩, ht⟩ :=
    Subtype.ext (Prod.ext (coherenceLift o r hp d hs ht).target_cell rfl)
  exact ⟨((Endomorphism.evaluation (carrier A)).source_app _).trans
      (_root_.congrArg (Endomorphism.evaluation (carrier A)).app hsource),
    ((Endomorphism.evaluation (carrier A)).target_app _).trans
      (_root_.congrArg (Endomorphism.evaluation (carrier A)).app htarget)⟩

/-- Parallel operations of the same arity are compared over the identity
of their common labelled diagram by the actual operadic contraction. -/
noncomputable def sameArityCoherence {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting n (carrier A))
    (ho : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app d)
    (hr : (collection A).arity.app r = (GlobularCollection.shape (carrier A)).app d) :
    { c : NativeTower.Cell A (n + 1) // NativeTower.source c = applyOperation o d ho ∧
      NativeTower.target c = applyOperation r d hr } := by
  let hs := ho.trans (_root_.congrArg (GlobularCollection.shape (carrier A)).app
    (Pasting.source_identity (carrier A) d)).symm
  let ht := hr.trans (_root_.congrArg (GlobularCollection.shape (carrier A)).app
    (Pasting.target_identity (carrier A) d)).symm
  refine ⟨coherenceCell o r hp (Pasting.identity d) hs ht, ?_, ?_⟩
  · exact (coherenceCell_boundary o r hp _ hs ht).1.trans
      (applyOperation_congr rfl (Pasting.source_identity (carrier A) d) _ ho)
  · exact (coherenceCell_boundary o r hp _ hs ht).2.trans
      (applyOperation_congr rfl (Pasting.target_identity (carrier A) d) _ hr)

theorem sameArityCoherence_invertible {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r) (d : Pasting n (carrier A)) ho hr :
    WeaklyInvertible n (sameArityCoherence o r hp d ho hr).val := all_cells_weaklyInvertible _ _

/-- Compare any parallel operation of the appropriate arity with the
selected standard instruction on that very same labelled diagram. -/
noncomputable def instructionComparison {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell n) (d : Pasting n (carrier A))
    (ho : (collection A).arity.app o = (GlobularCollection.shape (carrier A)).app d)
    (hp : (collection A).operations.Parallel n o
      (instruction A n ((GlobularCollection.shape (carrier A)).app d)).val) :
    { c : NativeTower.Cell A (n + 1) // NativeTower.source c = applyOperation o d ho ∧
      NativeTower.target c = (standardEvaluation A).app d } :=
  sameArityCoherence o (instruction A n ((GlobularCollection.shape (carrier A)).app d)).val hp d ho
    (instruction A n ((GlobularCollection.shape (carrier A)).app d)).property

/-- Substitute a labelled diagram of operations by the actual operadic
multiplication, retaining its resulting operation and complete input diagram. -/
noncomputable def substitutedInput {A : Type u} {n : Nat}
    (x : ((collection A).application ((collection A).application (carrier A))).Cell n) :
    ((collection A).application (carrier A)).Cell n :=
  ((Endomorphism.multiplication (carrier A)).application (carrier A)).app
    (((collection A).substitutionComparison (collection A) (carrier A)).app x)

/-- The source evaluates the inner operations first and then the outer
operation; this is the actual algebra multiplication equation. -/
theorem substitutedInput_evaluation {A : Type u} {n : Nat}
    (x : ((collection A).application ((collection A).application (carrier A))).Cell n) :
    (Endomorphism.evaluation (carrier A)).app (substitutedInput x) =
      (Endomorphism.evaluation (carrier A)).app
        (((collection A).map (Endomorphism.evaluation (carrier A))).app x) :=
  Endomorphism.evaluation_multiplication_nested (carrier A) x

/-- A contraction-selected comparison from an actual substituted operation
to the standard instruction on the same flattened labelled input. Parallel
operation boundaries remain an explicit requirement in higher dimensions. -/
noncomputable def substitutionCoherence {A : Type u} {n : Nat}
    (x : ((collection A).application ((collection A).application (carrier A))).Cell n)
    (hp : (collection A).operations.Parallel n (substitutedInput x).val.1
      (instruction A n ((GlobularCollection.shape (carrier A)).app (substitutedInput x).val.2)).val) :
    { c : NativeTower.Cell A (n + 1) //
      NativeTower.source c = (Endomorphism.evaluation (carrier A)).app
        (((collection A).map (Endomorphism.evaluation (carrier A))).app x) ∧
      NativeTower.target c = (standardEvaluation A).app (substitutedInput x).val.2 } := by
  let h := instructionComparison (substitutedInput x).val.1 (substitutedInput x).val.2
    (substitutedInput x).property hp
  exact ⟨h.val, h.property.1.trans (substitutedInput_evaluation x), h.property.2⟩

theorem substitutionCoherence_invertible {A : Type u} {n : Nat}
    (x : ((collection A).application ((collection A).application (carrier A))).Cell n) hp :
    WeaklyInvertible n (substitutionCoherence x hp).val := all_cells_weaklyInvertible _ _

/-- In dimension one, normalized operation boundaries are necessarily
parallel. Thus every nested one-dimensional operation gets this comparison,
without imposing an extra condition on the original path labels. -/
noncomputable def oneSubstitutionCoherence {A : Type u}
    (x : ((collection A).application ((collection A).application (carrier A))).Cell 1) :=
  substitutionCoherence x (GlobularSet.Parallel.cells
    (@Subsingleton.elim PUnit _ _ _) (@Subsingleton.elim PUnit _ _ _))

/-- A genuine nested binary input: its two inner labels are themselves
operations with labelled input diagrams. -/
noncomputable def nestedBinary {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (x y : ((collection A).application (carrier A)).Cell n)
    (h : Pasting.CutBoundary.target c ((collection A).application (carrier A)) x =
      Pasting.CutBoundary.source c ((collection A).application (carrier A)) y) :
    ((collection A).application ((collection A).application (carrier A))).Cell n :=
  (labelledInstructionsOn A ((collection A).application (carrier A))).app
    (binaryDiagramOn ((collection A).application (carrier A)) c x y h)

/-- Nested binary evaluation is the selected binary operation on the two
evaluated inner inputs. This identifies the operational syntax with the
actual selected composition, at every axis and in every dimension. -/
theorem nestedBinary_evaluation {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (x y : ((collection A).application (carrier A)).Cell n) h h' :
    (Endomorphism.evaluation (carrier A)).app
      (((collection A).map (Endomorphism.evaluation (carrier A))).app (nestedBinary c x y h)) =
        composeAt c ((Endomorphism.evaluation (carrier A)).app x)
          ((Endomorphism.evaluation (carrier A)).app y) h' := by
  have hl := labelledInstructionsOn_natural (A := A) (Endomorphism.evaluation (carrier A))
    (binaryDiagramOn ((collection A).application (carrier A)) c x y h)
  have hm := binaryDiagramOn_map (Endomorphism.evaluation (carrier A)) c x y h h'
  exact (_root_.congrArg (Endomorphism.evaluation (carrier A)).app hl).trans
    (_root_.congrArg (fun d => (Endomorphism.evaluation (carrier A)).app
      ((labelledInstructionsOn A (carrier A)).app d)) hm)

/-- The flattened input of a nested binary operation is the actual strict
cut composite of its two inner input diagrams. -/
theorem nestedBinary_inputs {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (x y : ((collection A).application (carrier A)).Cell n) h h' :
    (substitutedInput (nestedBinary c x y h)).val.2 =
      (Pasting.cutOperations (carrier A)).compose c x.val.2 y.val.2 h' := by
  let f := (collection A).inputs (carrier A)
  have hi := (Pasting.CutBoundary.target_map c f x).trans
    ((_root_.congrArg f.app h).trans (Pasting.CutBoundary.source_map c f y).symm)
  have hm := binaryDiagramOn_map f c x y h hi
  change (Pasting.flattenGlobular (carrier A)).app
    (Pasting.map f (binaryDiagramOn ((collection A).application (carrier A)) c x y h)) = _
  rw [hm]
  have hx := Pasting.flatten_singleton x.val.2
  have hy := Pasting.flatten_singleton y.val.2
  have hf := (Pasting.flatten_preserves (carrier A)).compose c
    (Pasting.singleton x.val.2) (Pasting.singleton y.val.2)
    ((Pasting.CutBoundary.target_map c (Pasting.singletonGlobular (Pasting.globular (carrier A))) x.val.2).trans
      ((_root_.congrArg (Pasting.singletonGlobular (Pasting.globular (carrier A))).app hi).trans
        (Pasting.CutBoundary.source_map c (Pasting.singletonGlobular (Pasting.globular (carrier A))) y.val.2).symm))
    ((_root_.congrArg (Pasting.CutBoundary.target c (Pasting.globular (carrier A))) hx).trans
      (h'.trans (_root_.congrArg (Pasting.CutBoundary.source c (Pasting.globular (carrier A))) hy).symm))
  exact hf.trans (eq_of_heq ((Pasting.CutModel.free (carrier A)).compose_heq rfl c c rfl
    _ _ _ _ (heq_of_eq hx) (heq_of_eq hy) _ h'))

def pathDiagram {A : Type u} {a b : A} (p : Path a b) : Pasting 1 (carrier A) :=
  Pasting.singleton (ULift.up (⟨a, b, p⟩ : PathOne A))

noncomputable def pathInput {A : Type u} {a b : A} (p : Path a b) :
    ((collection A).application (carrier A)).Cell 1 := (labelledInstructions A).app (pathDiagram p)

noncomputable def binaryPathInput {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    ((collection A).application (carrier A)).Cell 1 :=
  (labelledInstructions A).app (binaryDiagram (.bottom : Pasting.Cut 1)
    (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl)

theorem pathInput_evaluation {A : Type u} {a b : A} (p : Path a b) :
    (Endomorphism.evaluation (carrier A)).app (pathInput p) = ULift.up (⟨a, b, p⟩ : PathOne A) :=
  standardEvaluation_singleton (A := A) (n := 1) (ULift.up (⟨a, b, p⟩ : PathOne A))

theorem binaryPathInput_evaluation {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    (Endomorphism.evaluation (carrier A)).app (binaryPathInput p q) =
      ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) := composeAt_paths p q

theorem leftBracketedMatching {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Pasting.CutBoundary.target (.bottom : Pasting.Cut 1) ((collection A).application (carrier A))
      (binaryPathInput p q) =
    Pasting.CutBoundary.source (.bottom : Pasting.Cut 1) ((collection A).application (carrier A))
      (pathInput r) :=
  ((labelledInstructions A).target_app _).trans ((labelledInstructions A).source_app (pathDiagram r)).symm

theorem rightBracketedMatching {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Pasting.CutBoundary.target (.bottom : Pasting.Cut 1) ((collection A).application (carrier A))
      (pathInput p) =
    Pasting.CutBoundary.source (.bottom : Pasting.Cut 1) ((collection A).application (carrier A))
      (binaryPathInput q r) :=
  ((labelledInstructions A).target_app (pathDiagram p)).trans
    ((labelledInstructions A).source_app (binaryDiagram (.bottom : Pasting.Cut 1)
      (ULift.up (⟨b, c, q⟩ : PathOne A)) (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl)).symm

noncomputable def leftBracketedInput {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    ((collection A).application ((collection A).application (carrier A))).Cell 1 :=
  nestedBinary (.bottom : Pasting.Cut 1) (binaryPathInput p q) (pathInput r)
    (leftBracketedMatching p q r)

noncomputable def rightBracketedInput {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    ((collection A).application ((collection A).application (carrier A))).Cell 1 :=
  nestedBinary (.bottom : Pasting.Cut 1) (pathInput p) (binaryPathInput q r)
    (rightBracketedMatching p q r)

theorem leftBracketed_evaluation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (Endomorphism.evaluation (carrier A)).app (substitutedInput (leftBracketedInput p q r)) =
      ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) := by
  have hx := binaryPathInput_evaluation p q
  have hy := pathInput_evaluation r
  have hm := (_root_.congrArg (Pasting.CutBoundary.target (.bottom : Pasting.Cut 1) (carrier A)) hx).trans
    (_root_.congrArg (Pasting.CutBoundary.source (.bottom : Pasting.Cut 1) (carrier A)) hy).symm
  exact (substitutedInput_evaluation (leftBracketedInput p q r)).trans
    ((nestedBinary_evaluation (.bottom : Pasting.Cut 1) (binaryPathInput p q) (pathInput r)
      (leftBracketedMatching p q r) hm).trans
        ((composeAt_congr (.bottom : Pasting.Cut 1) hx hy hm rfl).trans (composeAt_paths (Path.trans p q) r)))

theorem rightBracketed_evaluation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (Endomorphism.evaluation (carrier A)).app (substitutedInput (rightBracketedInput p q r)) =
      ULift.up (⟨a, d, Path.trans p (Path.trans q r)⟩ : PathOne A) := by
  have hx := pathInput_evaluation p
  have hy := binaryPathInput_evaluation q r
  have hm := (_root_.congrArg (Pasting.CutBoundary.target (.bottom : Pasting.Cut 1) (carrier A)) hx).trans
    (_root_.congrArg (Pasting.CutBoundary.source (.bottom : Pasting.Cut 1) (carrier A)) hy).symm
  exact (substitutedInput_evaluation (rightBracketedInput p q r)).trans
    ((nestedBinary_evaluation (.bottom : Pasting.Cut 1) (pathInput p) (binaryPathInput q r)
      (rightBracketedMatching p q r) hm).trans
        ((composeAt_congr (.bottom : Pasting.Cut 1) hx hy hm rfl).trans (composeAt_paths p (Path.trans q r))))

/-- Both bracketings retain exactly the same flattened labelled triple. -/
theorem bracketed_inputs_equal {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (substitutedInput (leftBracketedInput p q r)).val.2 =
      (substitutedInput (rightBracketedInput p q r)).val.2 :=
  (nestedBinary_inputs (.bottom : Pasting.Cut 1) (binaryPathInput p q) (pathInput r)
    (leftBracketedMatching p q r) rfl).trans
    ((Pasting.cutOperations_associative (carrier A) (.bottom : Pasting.Cut 1)
      (pathDiagram p) (pathDiagram q) (pathDiagram r) rfl rfl rfl rfl).trans
        (nestedBinary_inputs (.bottom : Pasting.Cut 1) (pathInput p) (binaryPathInput q r)
          (rightBracketedMatching p q r) rfl).symm)

/-- The associator selected by the operadic contraction between the two
actual substituted binary operations over their common triple input. -/
noncomputable def selectedAssociator {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    { h : NativeTower.Cell A 2 //
      NativeTower.source h = ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) ∧
      NativeTower.target h = ULift.up (⟨a, d, Path.trans p (Path.trans q r)⟩ : PathOne A) } := by
  let l := substitutedInput (leftBracketedInput p q r)
  let t := substitutedInput (rightBracketedInput p q r)
  have hd : l.val.2 = t.val.2 := bracketed_inputs_equal p q r
  have ht := t.property.trans (_root_.congrArg (GlobularCollection.shape (carrier A)).app hd.symm)
  let k := sameArityCoherence l.val.1 t.val.1
    (GlobularSet.Parallel.cells (@Subsingleton.elim PUnit _ _ _) (@Subsingleton.elim PUnit _ _ _))
    l.val.2 l.property ht
  exact ⟨k.val, k.property.1.trans (leftBracketed_evaluation p q r),
    k.property.2.trans ((applyOperation_congr rfl hd ht t.property).trans (rightBracketed_evaluation p q r))⟩

theorem selectedAssociator_invertible {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    WeaklyInvertible 1 (selectedAssociator p q r).val := all_cells_weaklyInvertible _ _

/-- Evaluate a diagram of operad operations by selected instructions and
actual operadic multiplication. This acts on operations, not carrier cells. -/
noncomputable def operationEvaluation (A : Type u) :
    GlobularSet.Map (Pasting.globular (collection A).operations) (collection A).operations :=
  GlobularSet.Map.comp (Endomorphism.multiplication (carrier A)).operations
    (labelledInstructionsOn A (collection A).operations)

theorem operationEvaluation_singleton {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell n) :
    (operationEvaluation A).app (Pasting.singleton o) = o := by
  let C := collection A
  let i := (GlobularCollection.identityApplicationIn C.operations).app o
  have hp : (instruction A n ((GlobularCollection.shape C.operations).app (Pasting.singleton o))).val =
      one A n :=
    (_root_.congrArg (fun a => (instruction A n a).val)
      (Pasting.map_singleton (GlobularSet.terminalMap C.operations) o)).trans (instruction_singleton A n)
  have hl : (labelledInstructionsOn A C.operations).app (Pasting.singleton o) =
      (GlobularCollection.Hom.substitute (Endomorphism.unit (carrier A))
        (GlobularCollection.Hom.id C)).operations.app i :=
    Subtype.ext (Prod.ext hp (Pasting.map_id C.operations (Pasting.singleton o)).symm)
  have hm := _root_.congrArg (fun k : GlobularCollection.Hom (GlobularCollection.identity.substitute C) C =>
    k.operations.app i) (Endomorphism.one_mul (carrier A))
  have hi := _root_.congrArg (fun k : GlobularSet.Map C.operations C.operations => k.app o)
    (GlobularCollection.identityApplicationIso C.operations).inv_hom_id
  exact (_root_.congrArg (Endomorphism.multiplication (carrier A)).operations.app hl).trans (hm.trans hi)

/-- The operation produced by multiplication has the flattened diagram of
the original arities, retaining their full globular pasting structure. -/
theorem operationEvaluation_arity {A : Type u} {n : Nat}
    (d : Pasting n (collection A).operations) :
    (collection A).arity.app ((operationEvaluation A).app d) =
      (Pasting.flattenGlobular GlobularSet.terminal).app (Pasting.map (collection A).arity d) :=
  _root_.congrArg (fun k => k.app ((labelledInstructionsOn A (collection A).operations).app d))
    (Endomorphism.multiplication (carrier A)).arity

noncomputable def operationIdentity {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell n) : (collection A).operations.Cell (n + 1) :=
  (operationEvaluation A).app (Pasting.identity (Pasting.singleton o))

theorem operationIdentity_boundary {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell n) :
    (collection A).operations.source (operationIdentity o) = o ∧
      (collection A).operations.target (operationIdentity o) = o :=
  ⟨((operationEvaluation A).source_app _).trans
      ((_root_.congrArg (operationEvaluation A).app (Pasting.source_identity _ _)).trans
        (operationEvaluation_singleton o)),
    ((operationEvaluation A).target_app _).trans
      ((_root_.congrArg (operationEvaluation A).app (Pasting.target_identity _ _)).trans
        (operationEvaluation_singleton o))⟩

/-- Adjacent composition of operations by the operad's own multiplication.
Its exact endpoints can be reused when forming higher coherence diagrams. -/
noncomputable def operationCompose {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell (n + 1))
    (h : (collection A).operations.target o = (collection A).operations.source r) :
    (collection A).operations.Cell (n + 1) :=
  (operationEvaluation A).app (Pasting.vertical (Pasting.singleton o) (Pasting.singleton r)
    ((Pasting.target_singleton _ o).trans
      ((_root_.congrArg Pasting.singleton h).trans (Pasting.source_singleton _ r).symm)))

theorem operationCompose_boundary {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell (n + 1))
    (h : (collection A).operations.target o = (collection A).operations.source r) :
    (collection A).operations.source (operationCompose o r h) = (collection A).operations.source o ∧
      (collection A).operations.target (operationCompose o r h) = (collection A).operations.target r :=
  ⟨((operationEvaluation A).source_app _).trans
      ((_root_.congrArg (operationEvaluation A).app
        ((Pasting.source_vertical _ _ _).trans (Pasting.source_singleton _ o))).trans
          (operationEvaluation_singleton _)),
    ((operationEvaluation A).target_app _).trans
      ((_root_.congrArg (operationEvaluation A).app
        ((Pasting.target_vertical _ _ _).trans (Pasting.target_singleton _ r))).trans
          (operationEvaluation_singleton _))⟩

/-- Composition of actual operad operations along any lower axis. -/
noncomputable def operationComposeAt {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (o r : (collection A).operations.Cell n)
    (h : Pasting.CutBoundary.target c (collection A).operations o =
      Pasting.CutBoundary.source c (collection A).operations r) :
    (collection A).operations.Cell n :=
  (operationEvaluation A).app (binaryDiagramOn (collection A).operations c o r h)

/-- Multiplication retains the cut composite of the original operation arities. -/
theorem operationComposeAt_arity {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (o r : (collection A).operations.Cell n) h h' :
    (collection A).arity.app (operationComposeAt c o r h) =
      (Pasting.cutOperations GlobularSet.terminal).compose c
        ((collection A).arity.app o) ((collection A).arity.app r) h' := by
  let f := (collection A).arity
  have hi := (Pasting.CutBoundary.target_map c f o).trans
    ((_root_.congrArg f.app h).trans (Pasting.CutBoundary.source_map c f r).symm)
  have hm := binaryDiagramOn_map f c o r h hi
  unfold operationComposeAt
  rw [operationEvaluation_arity, hm]
  have hx := Pasting.flatten_singleton (f.app o)
  have hy := Pasting.flatten_singleton (f.app r)
  have hf := (Pasting.flatten_preserves GlobularSet.terminal).compose c
    (Pasting.singleton (f.app o)) (Pasting.singleton (f.app r))
    ((Pasting.CutBoundary.target_map c
      (Pasting.singletonGlobular (Pasting.globular GlobularSet.terminal)) (f.app o)).trans
      ((_root_.congrArg (Pasting.singletonGlobular (Pasting.globular GlobularSet.terminal)).app hi).trans
        (Pasting.CutBoundary.source_map c
          (Pasting.singletonGlobular (Pasting.globular GlobularSet.terminal)) (f.app r)).symm))
    ((_root_.congrArg (Pasting.CutBoundary.target c (Pasting.globular GlobularSet.terminal)) hx).trans
      (h'.trans (_root_.congrArg
        (Pasting.CutBoundary.source c (Pasting.globular GlobularSet.terminal)) hy).symm))
  exact hf.trans (eq_of_heq ((Pasting.CutModel.free GlobularSet.terminal).compose_heq
    rfl c c rfl _ _ _ _ (heq_of_eq hx) (heq_of_eq hy) _ h'))

theorem binaryDiagramOn_source (G : GlobularSet.{u + 1}) {n : Nat} (c : Pasting.Cut n)
    (p q : G.Cell (n + 1)) h h' :
    (Pasting.globular G).source (binaryDiagramOn G c.up p q h) =
      binaryDiagramOn G c (G.source p) (G.source q) h' := by
  let F := Pasting.CutModel.free G
  have hm := Pasting.CutBoundary.source_matching (Pasting.globular G) c
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c.up (Pasting.singletonGlobular G) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
        (Pasting.CutBoundary.source_map c.up (Pasting.singletonGlobular G) q).symm))
  exact (F.compatible.source_compose c.raise_up _ _ _ hm).trans
    (eq_of_heq (F.compose_heq rfl c c rfl _ _ _ _
      (heq_of_eq (Pasting.source_singleton _ p)) (heq_of_eq (Pasting.source_singleton _ q)) hm _))

theorem binaryDiagramOn_target (G : GlobularSet.{u + 1}) {n : Nat} (c : Pasting.Cut n)
    (p q : G.Cell (n + 1)) h h' :
    (Pasting.globular G).target (binaryDiagramOn G c.up p q h) =
      binaryDiagramOn G c (G.target p) (G.target q) h' := by
  let F := Pasting.CutModel.free G
  have hm := Pasting.CutBoundary.target_matching (Pasting.globular G) c
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map c.up (Pasting.singletonGlobular G) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
        (Pasting.CutBoundary.source_map c.up (Pasting.singletonGlobular G) q).symm))
  exact (F.compatible.target_compose c.raise_up _ _ _ hm).trans
    (eq_of_heq (F.compose_heq rfl c c rfl _ _ _ _
      (heq_of_eq (Pasting.target_singleton _ p)) (heq_of_eq (Pasting.target_singleton _ q)) hm _))

theorem operationComposeAt_source {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (collection A).operations.Cell (n + 1)) h h' :
    (collection A).operations.source (operationComposeAt c.up p q h) =
      operationComposeAt c ((collection A).operations.source p)
        ((collection A).operations.source q) h' :=
  ((operationEvaluation A).source_app _).trans
    (_root_.congrArg (operationEvaluation A).app
      (binaryDiagramOn_source (collection A).operations c p q h h'))

theorem operationComposeAt_target {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (p q : (collection A).operations.Cell (n + 1)) h h' :
    (collection A).operations.target (operationComposeAt c.up p q h) =
      operationComposeAt c ((collection A).operations.target p)
        ((collection A).operations.target q) h' :=
  ((operationEvaluation A).target_app _).trans
    (_root_.congrArg (operationEvaluation A).app
      (binaryDiagramOn_target (collection A).operations c p q h h'))

/-- Operation-level contraction over an identity arity. The parallelism and
equal-arity hypotheses remain explicit at every dimension. -/
def operationCoherenceProblem {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n)
    (hp : (collection A).operations.Parallel n o r)
    (ha : (collection A).arity.app o = (collection A).arity.app r) :
    GlobularSet.LiftingProblem (collection A).arity n :=
  ⟨⟨o, r, hp⟩, Pasting.identity ((collection A).arity.app o),
    (Pasting.source_identity _ _).symm,
    ha.symm.trans (Pasting.target_identity _ _).symm⟩

noncomputable def operationCoherence {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n) hp ha :
    GlobularSet.Lift (operationCoherenceProblem o r hp ha) :=
  (Endomorphism.nativeContraction A).lift (operationCoherenceProblem o r hp ha)

theorem operationCoherence_arity {A : Type u} {n : Nat}
    (o r : (collection A).operations.Cell n) hp ha :
    (collection A).arity.app (n := n + 1) (operationCoherence o r hp ha).cell =
      Pasting.identity (n := n) ((collection A).arity.app (n := n) o) :=
  (operationCoherence o r hp ha).arity_cell

/-- Binary substitution of one-dimensional operations. Normalization at
dimension zero makes these operations composable, independently of labels. -/
noncomputable def operationBinary {A : Type u}
    (o r : (collection A).operations.Cell 1) : (collection A).operations.Cell 1 :=
  operationComposeAt .bottom o r (@Subsingleton.elim PUnit _ _ _)

noncomputable def binaryArity (a b : Pasting 1 GlobularSet.terminal) :
    Pasting 1 GlobularSet.terminal :=
  (Pasting.cutOperations GlobularSet.terminal).compose .bottom a b
    (@Subsingleton.elim PUnit _ _ _)

theorem operationBinary_arity {A : Type u}
    (o r : (collection A).operations.Cell 1) :
    (collection A).arity.app (operationBinary o r) =
      binaryArity ((collection A).arity.app o) ((collection A).arity.app r) :=
  operationComposeAt_arity .bottom o r _ _

theorem binaryArity_assoc (a b c : Pasting 1 GlobularSet.terminal) :
    binaryArity (binaryArity a b) c = binaryArity a (binaryArity b c) :=
  Pasting.cutOperations_associative GlobularSet.terminal .bottom a b c _ _ _ _

/-- Both binary substitution trees have the same full pasting arity. -/
theorem operationBinary_assoc_arity {A : Type u}
    (o r s : (collection A).operations.Cell 1) :
    (collection A).arity.app (operationBinary (operationBinary o r) s) =
      (collection A).arity.app (operationBinary o (operationBinary r s)) := by
  simp only [operationBinary_arity]
  exact binaryArity_assoc _ _ _

/-- The associator between actual multiplication trees of operations, prior
to evaluation on any carrier labels. -/
noncomputable def operationAssociator {A : Type u}
    (o r s : (collection A).operations.Cell 1) :=
  operationCoherence (operationBinary (operationBinary o r) s)
    (operationBinary o (operationBinary r s))
    (GlobularSet.Parallel.cells (@Subsingleton.elim PUnit _ _ _)
      (@Subsingleton.elim PUnit _ _ _)) (operationBinary_assoc_arity o r s)

theorem operationAssociator_boundary {A : Type u}
    (o r s : (collection A).operations.Cell 1) :
    (collection A).operations.source (operationAssociator o r s).cell =
      operationBinary (operationBinary o r) s ∧
    (collection A).operations.target (operationAssociator o r s).cell =
      operationBinary o (operationBinary r s) :=
  ⟨(operationAssociator o r s).source_cell, (operationAssociator o r s).target_cell⟩

theorem operationAssociator_arity {A : Type u}
    (o r s : (collection A).operations.Cell 1) :
    (collection A).arity.app (operationAssociator o r s).cell =
      Pasting.identity ((collection A).arity.app (operationBinary (operationBinary o r) s)) :=
  (operationAssociator o r s).arity_cell

/-- An operation 2-cell with fixed operation endpoints, for assembling
coherence diagrams without discarding their actual multiplication trees. -/
structure Operation2Between {A : Type u} (o r : (collection A).operations.Cell 1) where
  cell : (collection A).operations.Cell 2
  source_cell : (collection A).operations.source cell = o
  target_cell : (collection A).operations.target cell = r

noncomputable def operationAssociatorArrow {A : Type u}
    (o r s : (collection A).operations.Cell 1) :
    Operation2Between (operationBinary (operationBinary o r) s)
      (operationBinary o (operationBinary r s)) :=
  ⟨(operationAssociator o r s).cell,
    (operationAssociator_boundary o r s).1, (operationAssociator_boundary o r s).2⟩

noncomputable def operationIdentityArrow {A : Type u}
    (o : (collection A).operations.Cell 1) : Operation2Between o o :=
  ⟨operationIdentity o, (operationIdentity_boundary o).1, (operationIdentity_boundary o).2⟩

noncomputable def operationVerticalArrow {A : Type u}
    {o r s : (collection A).operations.Cell 1}
    (p : Operation2Between o r) (q : Operation2Between r s) : Operation2Between o s :=
  ⟨operationCompose p.cell q.cell (p.target_cell.trans q.source_cell.symm),
    (operationCompose_boundary _ _ _).1.trans p.source_cell,
    (operationCompose_boundary _ _ _).2.trans q.target_cell⟩

noncomputable def operationHorizontalArrow {A : Type u}
    {o r s t : (collection A).operations.Cell 1}
    (p : Operation2Between o r) (q : Operation2Between s t) :
    Operation2Between (operationBinary o s) (operationBinary r t) := by
  let k := operationComposeAt (.bottom : Pasting.Cut 2) p.cell q.cell
    (@Subsingleton.elim PUnit _ _ _)
  have hs : (collection A).operations.source k =
      operationBinary ((collection A).operations.source p.cell)
        ((collection A).operations.source q.cell) :=
    operationComposeAt_source (.bottom : Pasting.Cut 1) p.cell q.cell _ _
  have ht : (collection A).operations.target k =
      operationBinary ((collection A).operations.target p.cell)
        ((collection A).operations.target q.cell) :=
    operationComposeAt_target (.bottom : Pasting.Cut 1) p.cell q.cell _ _
  exact ⟨k, hs.trans (_root_.congrArg₂ operationBinary p.source_cell q.source_cell),
    ht.trans (_root_.congrArg₂ operationBinary p.target_cell q.target_cell)⟩

/-- The two-edge side of the pentagon, composed in the actual operad. -/
noncomputable def operationPentagonShort {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    Operation2Between (operationBinary (operationBinary (operationBinary f g) h) k)
      (operationBinary f (operationBinary g (operationBinary h k))) :=
  operationVerticalArrow (operationAssociatorArrow (operationBinary f g) h k)
    (operationAssociatorArrow f g (operationBinary h k))

/-- The three-edge side uses both whiskered associators and the middle
associator; no carrier-level filler is substituted for any of its edges. -/
noncomputable def operationPentagonLong {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    Operation2Between (operationBinary (operationBinary (operationBinary f g) h) k)
      (operationBinary f (operationBinary g (operationBinary h k))) :=
  operationVerticalArrow
    (operationHorizontalArrow (operationAssociatorArrow f g h) (operationIdentityArrow k))
    (operationVerticalArrow (operationAssociatorArrow f (operationBinary g h) k)
      (operationHorizontalArrow (operationIdentityArrow f) (operationAssociatorArrow g h k)))

/-- Parallelism of the actual short and long operation composites. Equal
arity is a separate obligation before the contraction can be applied. -/
theorem operationPentagon_parallel {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    (collection A).operations.Parallel 2 (operationPentagonShort f g h k).cell
      (operationPentagonLong f g h k).cell :=
  GlobularSet.Parallel.cells
    ((operationPentagonShort f g h k).source_cell.trans
      (operationPentagonLong f g h k).source_cell.symm)
    ((operationPentagonShort f g h k).target_cell.trans
      (operationPentagonLong f g h k).target_cell.symm)

theorem identity_one_cutUnit {G : GlobularSet.{u + 1}} (p : Pasting 1 G) :
    Pasting.identity p = Pasting.cutUnit (.lift .bottom : Pasting.Cut 2) p := by
  rcases p with ⟨a, b, p⟩
  rfl

theorem vertical_two_cutCompose {G : GlobularSet.{u + 1}}
    (p q : Pasting 2 G) (h : Pasting.target p = Pasting.source q)
    (h' : Pasting.cutTarget (.lift .bottom) p = Pasting.cutSource (.lift .bottom) q) :
    Pasting.vertical p q h = Pasting.cutCompose (.lift .bottom) p q h' := by
  rfl

theorem operationIdentity_one_arity {A : Type u}
    (o : (collection A).operations.Cell 1) :
    (collection A).arity.app (operationIdentity o) =
      Pasting.identity ((collection A).arity.app o) := by
  have hi := identity_one_cutUnit (Pasting.singleton o)
  have hm := Pasting.map_cutUnit (.lift .bottom : Pasting.Cut 2) (collection A).arity
    (Pasting.singleton o)
  have hs := _root_.congrArg (Pasting.cutUnit (.lift .bottom : Pasting.Cut 2))
    (Pasting.map_singleton (collection A).arity o)
  exact (operationEvaluation_arity (Pasting.identity (Pasting.singleton o))).trans
    ((_root_.congrArg (Pasting.flattenGlobular GlobularSet.terminal).app
      ((_root_.congrArg (Pasting.map (collection A).arity) hi).trans (hm.trans hs))).trans
    (((Pasting.flatten_preserves GlobularSet.terminal).unit
    (.lift .bottom : Pasting.Cut 2) (Pasting.singleton ((collection A).arity.app o))).trans
    ((_root_.congrArg (Pasting.cutUnit (.lift .bottom : Pasting.Cut 2))
      (Pasting.flatten_singleton ((collection A).arity.app o))).trans (identity_one_cutUnit _).symm)))

theorem operationCompose_two_eq {A : Type u}
    (o r : (collection A).operations.Cell 2)
    (h : (collection A).operations.target o = (collection A).operations.source r) :
    operationCompose o r h = operationComposeAt (.lift .bottom) o r h := by
  apply _root_.congrArg (operationEvaluation A).app
  have hl := (Pasting.target_singleton (collection A).operations o).trans
    ((_root_.congrArg Pasting.singleton h).trans (Pasting.source_singleton _ r).symm)
  have hh := (Pasting.canonical_target_eq_cutTarget (.lift .bottom) (Pasting.singleton o)).symm.trans
    (hl.trans (Pasting.canonical_source_eq_cutSource (.lift .bottom) (Pasting.singleton r)))
  exact vertical_two_cutCompose _ _ _ hh

theorem operationCompose_two_arity {A : Type u}
    (o r : (collection A).operations.Cell 2)
    (h : (collection A).operations.target o = (collection A).operations.source r) h' :
    (collection A).arity.app (operationCompose o r h) =
      (Pasting.cutOperations GlobularSet.terminal).compose (.lift .bottom)
        ((collection A).arity.app o) ((collection A).arity.app r) h' := by
  rw [operationCompose_two_eq]
  exact operationComposeAt_arity _ _ _ _ _

def Operation2Between.IdentityArity {A : Type u} {o r : (collection A).operations.Cell 1}
    (p : Operation2Between o r) : Prop :=
  (collection A).arity.app p.cell = Pasting.identity ((collection A).arity.app o)

theorem Operation2Between.arity_endpoints {A : Type u}
    {o r : (collection A).operations.Cell 1} (p : Operation2Between o r)
    (hp : p.IdentityArity) : (collection A).arity.app o = (collection A).arity.app r := by
  have ht := (collection A).arity.target_app p.cell
  exact ((Pasting.target_identity _ _).symm.trans
    ((_root_.congrArg Pasting.target hp.symm).trans ht)).trans
    (_root_.congrArg (collection A).arity.app p.target_cell)

theorem operationAssociatorArrow_identityArity {A : Type u}
    (o r s : (collection A).operations.Cell 1) :
    (operationAssociatorArrow o r s).IdentityArity := operationAssociator_arity o r s

theorem operationIdentityArrow_identityArity {A : Type u}
    (o : (collection A).operations.Cell 1) :
    (operationIdentityArrow o).IdentityArity := operationIdentity_one_arity o

set_option backward.isDefEq.respectTransparency false in
theorem identityArity_vertical (a : Pasting 1 GlobularSet.terminal.{u + 1})
    (h : Pasting.CutBoundary.target (.lift .bottom : Pasting.Cut 2)
      (Pasting.globular GlobularSet.terminal) (Pasting.identity a) =
      Pasting.CutBoundary.source (.lift .bottom : Pasting.Cut 2)
        (Pasting.globular GlobularSet.terminal) (Pasting.identity a)) :
    (Pasting.cutOperations GlobularSet.terminal).compose (.lift .bottom)
      (Pasting.identity a) (Pasting.identity a) h = Pasting.identity a := by
  have hh := Pasting.cutCompose_right_unit (.lift .bottom : Pasting.Cut 2)
    (Pasting.cutUnit (.lift .bottom : Pasting.Cut 2) a)
  simp only [Pasting.cutTarget_cutUnit] at hh
  simpa only [identity_one_cutUnit, Pasting.cutOperations] using hh

theorem operationVerticalArrow_identityArity {A : Type u}
    {o r s : (collection A).operations.Cell 1}
    (p : Operation2Between o r) (q : Operation2Between r s)
    (hp : p.IdentityArity) (hq : q.IdentityArity) :
    (operationVerticalArrow p q).IdentityArity := by
  let f := (collection A).arity
  have hm := (f.target_app p.cell).trans
    ((_root_.congrArg f.app (p.target_cell.trans q.source_cell.symm)).trans (f.source_app q.cell).symm)
  have hy : f.app q.cell = Pasting.identity (f.app o) :=
    hq.trans (_root_.congrArg Pasting.identity (p.arity_endpoints hp).symm)
  have hi : Pasting.CutBoundary.target (.lift .bottom : Pasting.Cut 2)
      (Pasting.globular GlobularSet.terminal) (Pasting.identity (f.app o)) =
      Pasting.CutBoundary.source (.lift .bottom : Pasting.Cut 2)
        (Pasting.globular GlobularSet.terminal) (Pasting.identity (f.app o)) :=
    (Pasting.target_identity _ _).trans (Pasting.source_identity _ _).symm
  exact (operationCompose_two_arity p.cell q.cell (p.target_cell.trans q.source_cell.symm) hm).trans
    ((eq_of_heq ((Pasting.CutModel.free GlobularSet.terminal).compose_heq
      rfl (.lift .bottom : Pasting.Cut 2) (.lift .bottom : Pasting.Cut 2) rfl
      _ _ _ _ (heq_of_eq hp) (heq_of_eq hy) hm hi)).trans (identityArity_vertical _ hi))

theorem identityArity_horizontal (a b : Pasting 1 GlobularSet.terminal.{u + 1})
    (h : Pasting.CutBoundary.target (.bottom : Pasting.Cut 2)
      (Pasting.globular GlobularSet.terminal) (Pasting.identity a) =
      Pasting.CutBoundary.source (.bottom : Pasting.Cut 2)
        (Pasting.globular GlobularSet.terminal) (Pasting.identity b)) :
    (Pasting.cutOperations GlobularSet.terminal).compose .bottom
      (Pasting.identity a) (Pasting.identity b) h = Pasting.identity (binaryArity a b) := by
  rcases a with ⟨x, y, a⟩
  rcases b with ⟨z, w, b⟩
  cases x
  cases y
  cases z
  cases w
  exact (Pasting.identity_horizontal a b).symm

theorem operationHorizontalArrow_identityArity {A : Type u}
    {o r s t : (collection A).operations.Cell 1}
    (p : Operation2Between o r) (q : Operation2Between s t)
    (hp : p.IdentityArity) (hq : q.IdentityArity) :
    (operationHorizontalArrow p q).IdentityArity := by
  let f := (collection A).arity
  have hm : Pasting.CutBoundary.target (.bottom : Pasting.Cut 2)
      (Pasting.globular GlobularSet.terminal) (f.app p.cell) =
      Pasting.CutBoundary.source (.bottom : Pasting.Cut 2)
        (Pasting.globular GlobularSet.terminal) (f.app q.cell) := @Subsingleton.elim PUnit _ _ _
  have hi : Pasting.CutBoundary.target (.bottom : Pasting.Cut 2)
      (Pasting.globular GlobularSet.terminal) (Pasting.identity (f.app o)) =
      Pasting.CutBoundary.source (.bottom : Pasting.Cut 2)
        (Pasting.globular GlobularSet.terminal) (Pasting.identity (f.app s)) := @Subsingleton.elim PUnit _ _ _
  exact (operationComposeAt_arity (.bottom : Pasting.Cut 2) p.cell q.cell _ hm).trans
    ((eq_of_heq ((Pasting.CutModel.free GlobularSet.terminal).compose_heq
      rfl (.bottom : Pasting.Cut 2) (.bottom : Pasting.Cut 2) rfl
      _ _ _ _ (heq_of_eq hp) (heq_of_eq hq) hm hi)).trans
      ((identityArity_horizontal _ _ hi).trans
        (_root_.congrArg Pasting.identity (operationBinary_arity o s).symm)))

theorem operationPentagonShort_identityArity {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    (operationPentagonShort f g h k).IdentityArity :=
  operationVerticalArrow_identityArity _ _
    (operationAssociatorArrow_identityArity _ _ _) (operationAssociatorArrow_identityArity _ _ _)

theorem operationPentagonLong_identityArity {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    (operationPentagonLong f g h k).IdentityArity :=
  operationVerticalArrow_identityArity _ _
    (operationHorizontalArrow_identityArity _ _
      (operationAssociatorArrow_identityArity _ _ _) (operationIdentityArrow_identityArity _))
    (operationVerticalArrow_identityArity _ _ (operationAssociatorArrow_identityArity _ _ _)
      (operationHorizontalArrow_identityArity _ _
        (operationIdentityArrow_identityArity _) (operationAssociatorArrow_identityArity _ _ _)))

/-- The pentagon contracts between the actual two-edge and three-edge
operation composites, after verifying both parallelism and equal arity. -/
noncomputable def operationPentagon {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :=
  operationCoherence (operationPentagonShort f g h k).cell (operationPentagonLong f g h k).cell
    (operationPentagon_parallel f g h k)
    ((operationPentagonShort_identityArity f g h k).trans (operationPentagonLong_identityArity f g h k).symm)

theorem operationPentagon_boundary {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    (collection A).operations.source (operationPentagon f g h k).cell =
      (operationPentagonShort f g h k).cell ∧
    (collection A).operations.target (operationPentagon f g h k).cell =
      (operationPentagonLong f g h k).cell :=
  ⟨(operationPentagon f g h k).source_cell, (operationPentagon f g h k).target_cell⟩

theorem operationPentagon_arity {A : Type u}
    (f g h k : (collection A).operations.Cell 1) :
    (collection A).arity.app (n := 3) (operationPentagon f g h k).cell =
      Pasting.identity (n := 2) (Pasting.identity (n := 1)
        ((collection A).arity.app (n := 1) (operationBinary (operationBinary (operationBinary f g) h) k))) := by
  have ha : (collection A).arity.app (n := 3) (operationPentagon f g h k).cell =
      Pasting.identity (n := 2) ((collection A).arity.app (n := 2)
        (operationPentagonShort f g h k).cell) :=
    operationCoherence_arity (operationPentagonShort f g h k).cell (operationPentagonLong f g h k).cell _ _
  exact ha.trans (_root_.congrArg (Pasting.identity (n := 2))
    (operationPentagonShort_identityArity f g h k))

theorem operationPentagon_sourceArity {A : Type u}
    (f g h k : (collection A).operations.Cell 1) (d : Pasting 3 (carrier A))
    (hd : (collection A).arity.app (n := 3) (operationPentagon f g h k).cell =
      (GlobularCollection.shape (carrier A)).app (n := 3) d) :
    (collection A).arity.app (n := 2) (operationPentagonShort f g h k).cell =
      (GlobularCollection.shape (carrier A)).app (n := 2) (Pasting.source d) := by
  have hs := _root_.congrArg ((collection A).arity.app (n := 2)) (operationPentagon_boundary f g h k).1
  have hm := (collection A).arity.source_app (n := 2) (operationPentagon f g h k).cell
  exact hs.symm.trans (hm.symm.trans ((_root_.congrArg
    ((Pasting.globular GlobularSet.terminal).source (n := 2)) hd).trans
    ((GlobularCollection.shape (carrier A)).source_app (n := 2) d)))

theorem operationPentagon_targetArity {A : Type u}
    (f g h k : (collection A).operations.Cell 1) (d : Pasting 3 (carrier A))
    (hd : (collection A).arity.app (n := 3) (operationPentagon f g h k).cell =
      (GlobularCollection.shape (carrier A)).app (n := 3) d) :
    (collection A).arity.app (n := 2) (operationPentagonLong f g h k).cell =
      (GlobularCollection.shape (carrier A)).app (n := 2) (Pasting.target d) := by
  have ht := _root_.congrArg ((collection A).arity.app (n := 2)) (operationPentagon_boundary f g h k).2
  have hm := (collection A).arity.target_app (n := 2) (operationPentagon f g h k).cell
  exact ht.symm.trans (hm.symm.trans ((_root_.congrArg
    ((Pasting.globular GlobularSet.terminal).target (n := 2)) hd).trans
    ((GlobularCollection.shape (carrier A)).target_app (n := 2) d)))

/-- Action of this specific pentagon operation on a full admissible labelled
diagram. Both boundaries are actions of the actual composite operations. -/
noncomputable def appliedOperationPentagon {A : Type u}
    (f g h k : (collection A).operations.Cell 1) (d : Pasting 3 (carrier A))
    (hd : (collection A).arity.app (n := 3) (operationPentagon f g h k).cell =
      (GlobularCollection.shape (carrier A)).app (n := 3) d) :
    { c : NativeTower.Cell A 3 //
      NativeTower.source c = applyOperation (operationPentagonShort f g h k).cell (Pasting.source d)
        (operationPentagon_sourceArity f g h k d hd) ∧
      NativeTower.target c = applyOperation (operationPentagonLong f g h k).cell (Pasting.target d)
        (operationPentagon_targetArity f g h k d hd) } := by
  let i : ((collection A).application (carrier A)).Cell 3 :=
    ⟨⟨(operationPentagon f g h k).cell, d⟩, hd⟩
  have hs : ((collection A).application (carrier A)).source i =
      ⟨⟨(operationPentagonShort f g h k).cell, Pasting.source d⟩,
        operationPentagon_sourceArity f g h k d hd⟩ :=
    Subtype.ext (Prod.ext (operationPentagon_boundary f g h k).1 rfl)
  have ht : ((collection A).application (carrier A)).target i =
      ⟨⟨(operationPentagonLong f g h k).cell, Pasting.target d⟩,
        operationPentagon_targetArity f g h k d hd⟩ :=
    Subtype.ext (Prod.ext (operationPentagon_boundary f g h k).2 rfl)
  exact ⟨applyOperation (operationPentagon f g h k).cell d hd,
    ((Endomorphism.evaluation (carrier A)).source_app i).trans
      (_root_.congrArg (Endomorphism.evaluation (carrier A)).app hs),
    ((Endomorphism.evaluation (carrier A)).target_app i).trans
      (_root_.congrArg (Endomorphism.evaluation (carrier A)).app ht)⟩

theorem appliedOperationPentagon_invertible {A : Type u}
    (f g h k : (collection A).operations.Cell 1) (d : Pasting 3 (carrier A)) hd :
    WeaklyInvertible 2 (appliedOperationPentagon f g h k d hd).val :=
  all_cells_weaklyInvertible _ _

/-- Relabelling preserves the adjacent identity diagram in every dimension. -/
theorem map_identityDiagram {G H : GlobularSet.{u + 1}} (f : GlobularSet.Map G H)
    {n : Nat} (p : Pasting n G) :
    Pasting.map f (Pasting.identity p) = Pasting.identity (Pasting.map f p) := by
  induction n generalizing G H with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, b, p⟩
    apply _root_.congrArg Pasting.pack
    exact (Chain.mapAlong_natural _ _ _ _ _ (fun {x y} e => (ih (f.hom x y) e).symm) p).symm

/-- The full quadruple input retains all four original path labels. -/
noncomputable def fourPathDiagram {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) : Pasting 1 (carrier A) :=
  (Pasting.cutOperations (carrier A)).compose .bottom
    ((Pasting.cutOperations (carrier A)).compose .bottom
      ((Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram p) (pathDiagram q) rfl)
      (pathDiagram r) rfl) (pathDiagram s) rfl

theorem shape_one_compose {A : Type u} (p q : Pasting 1 (carrier A)) h :
    (GlobularCollection.shape (carrier A)).app (n := 1)
      ((Pasting.cutOperations (carrier A)).compose .bottom p q h) =
    binaryArity ((GlobularCollection.shape (carrier A)).app (n := 1) p)
      ((GlobularCollection.shape (carrier A)).app (n := 1) q) :=
  (Pasting.mapGlobular_preserves (GlobularSet.terminalMap (carrier A))).compose .bottom p q h _

theorem pathDiagram_shape {A : Type u} {a b : A} (p : Path a b) :
    (GlobularCollection.shape (carrier A)).app (n := 1) (pathDiagram p) =
      (collection A).arity.app (n := 1) (one A 1) :=
  (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) _).trans (one_arity A 1).symm

set_option backward.isDefEq.respectTransparency false in
theorem fourPathDiagram_shape {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (GlobularCollection.shape (carrier A)).app (n := 1) (fourPathDiagram p q r s) =
      (collection A).arity.app (n := 1)
        (operationBinary (operationBinary (operationBinary (one A 1) (one A 1)) (one A 1)) (one A 1)) := by
  unfold fourPathDiagram
  simp only [shape_one_compose, pathDiagram_shape, operationBinary_arity]

/-- The specific double-identity quadruple diagram on which the pentagon
operation acts, with no abstract admissibility assumption left to supply. -/
noncomputable def fourPathPentagonDiagram {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) : Pasting 3 (carrier A) :=
  Pasting.identity (Pasting.identity (fourPathDiagram p q r s))

theorem fourPathPentagonDiagram_arity {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (collection A).arity.app (n := 3) (operationPentagon (one A 1) (one A 1) (one A 1) (one A 1)).cell =
      (GlobularCollection.shape (carrier A)).app (n := 3) (fourPathPentagonDiagram p q r s) := by
  have hm := map_identityDiagram (GlobularSet.terminalMap (carrier A))
    (Pasting.identity (fourPathDiagram p q r s))
  have hi := map_identityDiagram (GlobularSet.terminalMap (carrier A)) (fourPathDiagram p q r s)
  exact (operationPentagon_arity _ _ _ _).trans
    ((_root_.congrArg (fun x : Pasting 1 GlobularSet.terminal => Pasting.identity (Pasting.identity x))
      (fourPathDiagram_shape p q r s).symm).trans
      ((_root_.congrArg (Pasting.identity (n := 2)) hi.symm).trans hm.symm))

/-- The operadic pentagon instantiated on any four composable raw paths. -/
noncomputable def fourPathPentagon {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :=
  appliedOperationPentagon (one A 1) (one A 1) (one A 1) (one A 1)
    (fourPathPentagonDiagram p q r s) (fourPathPentagonDiagram_arity p q r s)

theorem fourPathPentagon_invertible {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    WeaklyInvertible 2 (fourPathPentagon p q r s).val := all_cells_weaklyInvertible _ _

/-- Projecting a nested binary application to its operation gives exactly
the binary operation composite, not merely an equal carrier evaluation. -/
theorem nestedBinary_operation {A : Type u} {n : Nat} (c : Pasting.Cut n)
    (x y : ((collection A).application (carrier A)).Cell n) h h' :
    (substitutedInput (nestedBinary c x y h)).val.1 =
      operationComposeAt c x.val.1 y.val.1 h' := by
  let f := (collection A).operation (carrier A)
  have hl := labelledInstructionsOn_natural (A := A) f
    (binaryDiagramOn ((collection A).application (carrier A)) c x y h)
  have hm := binaryDiagramOn_map f c x y h h'
  exact (_root_.congrArg (Endomorphism.multiplication (carrier A)).operations.app hl).trans
    (_root_.congrArg (fun d => (Endomorphism.multiplication (carrier A)).operations.app
      ((labelledInstructionsOn A (collection A).operations).app d)) hm)

theorem pathInput_operation {A : Type u} {a b : A} (p : Path a b) :
    (pathInput p).val.1 = one A 1 :=
  (_root_.congrArg (instructions A).app
    (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) _)).trans (instruction_singleton A 1)

theorem application_zero_ext {A : Type u}
    {x y : ((collection A).application (carrier A)).Cell 0}
    (h : (Endomorphism.evaluation (carrier A)).app x = (Endomorphism.evaluation (carrier A)).app y) :
    x = y := Subtype.ext (Prod.ext (@Subsingleton.elim PUnit _ _ _) h)

theorem application_matching {A : Type u}
    (x y : ((collection A).application (carrier A)).Cell 1)
    (h : NativeTower.target ((Endomorphism.evaluation (carrier A)).app x) =
      NativeTower.source ((Endomorphism.evaluation (carrier A)).app y)) :
    ((collection A).application (carrier A)).target x =
      ((collection A).application (carrier A)).source y :=
  application_zero_ext (((Endomorphism.evaluation (carrier A)).target_app x).symm.trans
    (h.trans ((Endomorphism.evaluation (carrier A)).source_app y)))

/-- A full labelled operad application computing a specified raw path. -/
structure PathApplication {A : Type u} {a b : A} (p : Path a b) where
  cell : ((collection A).application (carrier A)).Cell 1
  evaluation : (Endomorphism.evaluation (carrier A)).app cell = ULift.up (⟨a, b, p⟩ : PathOne A)

noncomputable def PathApplication.singleton {A : Type u} {a b : A} (p : Path a b) : PathApplication p :=
  ⟨pathInput p, pathInput_evaluation p⟩

theorem PathApplication.matching {A : Type u} {a b c : A} {p : Path a b} {q : Path b c}
    (x : PathApplication p) (y : PathApplication q) :
    ((collection A).application (carrier A)).target x.cell =
      ((collection A).application (carrier A)).source y.cell :=
  application_matching x.cell y.cell ((_root_.congrArg (NativeTower.target (n := 0)) x.evaluation).trans
    (_root_.congrArg (NativeTower.source (n := 0)) y.evaluation).symm)

noncomputable def PathApplication.binary {A : Type u} {a b c : A} {p : Path a b} {q : Path b c}
    (x : PathApplication p) (y : PathApplication q) : PathApplication (Path.trans p q) := by
  let h := x.matching y
  let hm := (_root_.congrArg (NativeTower.target (n := 0)) x.evaluation).trans
    (_root_.congrArg (NativeTower.source (n := 0)) y.evaluation).symm
  exact ⟨substitutedInput (nestedBinary .bottom x.cell y.cell h),
    (substitutedInput_evaluation _).trans
      ((nestedBinary_evaluation .bottom x.cell y.cell h hm).trans
        ((composeAt_congr .bottom x.evaluation y.evaluation hm rfl).trans (composeAt_paths p q)))⟩

theorem PathApplication.singleton_operation {A : Type u} {a b : A} (p : Path a b) :
    (PathApplication.singleton p).cell.val.1 = one A 1 := pathInput_operation p

theorem PathApplication.binary_operation {A : Type u} {a b c : A} {p : Path a b} {q : Path b c}
    (x : PathApplication p) (y : PathApplication q) :
    (x.binary y).cell.val.1 = operationBinary x.cell.val.1 y.cell.val.1 :=
  nestedBinary_operation .bottom x.cell y.cell (x.matching y) _

noncomputable def fourLeftApplication {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    PathApplication (Path.trans (Path.trans (Path.trans p q) r) s) :=
  (((PathApplication.singleton p).binary (PathApplication.singleton q)).binary
    (PathApplication.singleton r)).binary (PathApplication.singleton s)

noncomputable def fourRightApplication {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    PathApplication (Path.trans p (Path.trans q (Path.trans r s))) :=
  (PathApplication.singleton p).binary ((PathApplication.singleton q).binary
    ((PathApplication.singleton r).binary (PathApplication.singleton s)))

theorem fourLeftApplication_operation {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (fourLeftApplication p q r s).cell.val.1 =
      operationBinary (operationBinary (operationBinary (one A 1) (one A 1)) (one A 1)) (one A 1) := by
  unfold fourLeftApplication
  simp only [PathApplication.binary_operation, PathApplication.singleton_operation]

theorem fourRightApplication_operation {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (fourRightApplication p q r s).cell.val.1 =
      operationBinary (one A 1) (operationBinary (one A 1) (operationBinary (one A 1) (one A 1))) := by
  unfold fourRightApplication
  simp only [PathApplication.binary_operation, PathApplication.singleton_operation]

theorem PathApplication.binary_inputs {A : Type u} {a b c : A} {p : Path a b} {q : Path b c}
    (x : PathApplication p) (y : PathApplication q) {d₁ d₂ : Pasting 1 (carrier A)}
    (hx : x.cell.val.2 = d₁) (hy : y.cell.val.2 = d₂) h' :
    (x.binary y).cell.val.2 = (Pasting.cutOperations (carrier A)).compose .bottom d₁ d₂ h' := by
  let f := (collection A).inputs (carrier A)
  have hm := (Pasting.CutBoundary.target_map (.bottom : Pasting.Cut 1) f x.cell).trans
    ((_root_.congrArg f.app (x.matching y)).trans
      (Pasting.CutBoundary.source_map (.bottom : Pasting.Cut 1) f y.cell).symm)
  exact (nestedBinary_inputs .bottom x.cell y.cell (x.matching y) hm).trans
    (eq_of_heq ((Pasting.CutModel.free (carrier A)).compose_heq rfl
      (.bottom : Pasting.Cut 1) (.bottom : Pasting.Cut 1) rfl
      _ _ _ _ (heq_of_eq hx) (heq_of_eq hy) hm h'))

theorem fourLeftApplication_inputs {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (fourLeftApplication p q r s).cell.val.2 = fourPathDiagram p q r s :=
  PathApplication.binary_inputs _ _
    (PathApplication.binary_inputs _ _ (PathApplication.binary_inputs _ _ rfl rfl rfl) rfl rfl) rfl rfl

theorem fourPathDiagram_assoc {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    fourPathDiagram p q r s = (Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram p)
      ((Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram q)
        ((Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram r) (pathDiagram s) rfl) rfl) rfl :=
  (Pasting.cutOperations_associative (carrier A) .bottom
    ((Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram p) (pathDiagram q) rfl)
    (pathDiagram r) (pathDiagram s) rfl rfl rfl rfl).trans
    (Pasting.cutOperations_associative (carrier A) .bottom (pathDiagram p) (pathDiagram q)
      ((Pasting.cutOperations (carrier A)).compose .bottom (pathDiagram r) (pathDiagram s) rfl)
      rfl rfl rfl rfl)

theorem fourRightApplication_inputs {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (fourRightApplication p q r s).cell.val.2 = fourPathDiagram p q r s :=
  (PathApplication.binary_inputs _ _ rfl
    (PathApplication.binary_inputs _ _ rfl (PathApplication.binary_inputs _ _ rfl rfl rfl) rfl) rfl).trans
      (fourPathDiagram_assoc p q r s).symm

theorem PathApplication.applyOperation_eq {A : Type u} {a b : A} {p : Path a b}
    (x : PathApplication p) {o : (collection A).operations.Cell 1} {d : Pasting 1 (carrier A)}
    (ho : x.cell.val.1 = o) (hd : x.cell.val.2 = d) h :
    applyOperation o d h = ULift.up (⟨a, b, p⟩ : PathOne A) :=
  (_root_.congrArg (Endomorphism.evaluation (carrier A)).app
    (Subtype.ext (Prod.ext ho.symm hd.symm))).trans x.evaluation

theorem fourLeftOperation_evaluation {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) h :
    applyOperation
      (operationBinary (operationBinary (operationBinary (one A 1) (one A 1)) (one A 1)) (one A 1))
      (fourPathDiagram p q r s) h =
      ULift.up (⟨a, e, Path.trans (Path.trans (Path.trans p q) r) s⟩ : PathOne A) :=
  (fourLeftApplication p q r s).applyOperation_eq
    (fourLeftApplication_operation p q r s) (fourLeftApplication_inputs p q r s) h

theorem fourRightOperation_evaluation {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) h :
    applyOperation
      (operationBinary (one A 1) (operationBinary (one A 1) (operationBinary (one A 1) (one A 1))))
      (fourPathDiagram p q r s) h =
      ULift.up (⟨a, e, Path.trans p (Path.trans q (Path.trans r s))⟩ : PathOne A) :=
  (fourRightApplication p q r s).applyOperation_eq
    (fourRightApplication_operation p q r s) (fourRightApplication_inputs p q r s) h

theorem applyOperation_source {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell (n + 1)) (d : Pasting (n + 1) (carrier A)) h hs :
    NativeTower.source (applyOperation o d h) =
      applyOperation ((collection A).operations.source o) (Pasting.source d) hs :=
  (Endomorphism.evaluation (carrier A)).source_app ⟨⟨o, d⟩, h⟩

theorem applyOperation_target {A : Type u} {n : Nat}
    (o : (collection A).operations.Cell (n + 1)) (d : Pasting (n + 1) (carrier A)) h ht :
    NativeTower.target (applyOperation o d h) =
      applyOperation ((collection A).operations.target o) (Pasting.target d) ht :=
  (Endomorphism.evaluation (carrier A)).target_app ⟨⟨o, d⟩, h⟩

theorem Operation2Between.identityInputArity {A : Type u}
    {o r : (collection A).operations.Cell 1} (p : Operation2Between o r) (hp : p.IdentityArity)
    (d : Pasting 1 (carrier A))
    (ho : (collection A).arity.app (n := 1) o = (GlobularCollection.shape (carrier A)).app (n := 1) d) :
    (collection A).arity.app (n := 2) p.cell =
      (GlobularCollection.shape (carrier A)).app (n := 2) (Pasting.identity d) :=
  hp.trans ((_root_.congrArg (Pasting.identity (n := 1)) ho).trans
    (map_identityDiagram (GlobularSet.terminalMap (carrier A)) d).symm)

/-- Acting on the identity of a full labelled input preserves the fixed
operation endpoints and does not replace the chosen 2-operation. -/
noncomputable def Operation2Between.actionOnIdentity {A : Type u}
    {o r : (collection A).operations.Cell 1} (p : Operation2Between o r) (hp : p.IdentityArity)
    (d : Pasting 1 (carrier A))
    (ho : (collection A).arity.app (n := 1) o = (GlobularCollection.shape (carrier A)).app (n := 1) d) :
    { c : NativeTower.Cell A 2 // NativeTower.source c = applyOperation o d ho ∧
      NativeTower.target c = applyOperation r d ((p.arity_endpoints hp).symm.trans ho) } := by
  let hr := (p.arity_endpoints hp).symm.trans ho
  let hs := (_root_.congrArg ((collection A).arity.app (n := 1)) p.source_cell).trans
    (ho.trans (_root_.congrArg ((GlobularCollection.shape (carrier A)).app (n := 1))
      (Pasting.source_identity (carrier A) d)).symm)
  let ht := (_root_.congrArg ((collection A).arity.app (n := 1)) p.target_cell).trans
    (hr.trans (_root_.congrArg ((GlobularCollection.shape (carrier A)).app (n := 1))
      (Pasting.target_identity (carrier A) d)).symm)
  exact ⟨applyOperation p.cell (Pasting.identity d) (p.identityInputArity hp d ho),
    (applyOperation_source p.cell _ _ hs).trans
      (applyOperation_congr p.source_cell (Pasting.source_identity (carrier A) d) hs ho),
    (applyOperation_target p.cell _ _ ht).trans
      (applyOperation_congr p.target_cell (Pasting.target_identity (carrier A) d) ht hr)⟩

noncomputable def fourPathPentagonShort {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    { h : NativeTower.Cell A 2 //
      NativeTower.source h = ULift.up (⟨a, e, Path.trans (Path.trans (Path.trans p q) r) s⟩ : PathOne A) ∧
      NativeTower.target h = ULift.up (⟨a, e, Path.trans p (Path.trans q (Path.trans r s))⟩ : PathOne A) } := by
  let h := (operationPentagonShort (one A 1) (one A 1) (one A 1) (one A 1)).actionOnIdentity
    (operationPentagonShort_identityArity _ _ _ _) (fourPathDiagram p q r s) (fourPathDiagram_shape p q r s).symm
  exact ⟨h.val, h.property.1.trans (fourLeftOperation_evaluation p q r s _),
    h.property.2.trans (fourRightOperation_evaluation p q r s _)⟩

noncomputable def fourPathPentagonLong {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    { h : NativeTower.Cell A 2 //
      NativeTower.source h = ULift.up (⟨a, e, Path.trans (Path.trans (Path.trans p q) r) s⟩ : PathOne A) ∧
      NativeTower.target h = ULift.up (⟨a, e, Path.trans p (Path.trans q (Path.trans r s))⟩ : PathOne A) } := by
  let h := (operationPentagonLong (one A 1) (one A 1) (one A 1) (one A 1)).actionOnIdentity
    (operationPentagonLong_identityArity _ _ _ _) (fourPathDiagram p q r s) (fourPathDiagram_shape p q r s).symm
  exact ⟨h.val, h.property.1.trans (fourLeftOperation_evaluation p q r s _),
    h.property.2.trans (fourRightOperation_evaluation p q r s _)⟩

theorem fourPathPentagon_boundary {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    NativeTower.source (fourPathPentagon p q r s).val = (fourPathPentagonShort p q r s).val ∧
      NativeTower.target (fourPathPentagon p q r s).val = (fourPathPentagonLong p q r s).val := by
  constructor
  · exact (fourPathPentagon p q r s).property.1.trans
      (applyOperation_congr rfl (Pasting.source_identity (carrier A) (Pasting.identity (fourPathDiagram p q r s))) _ _)
  · exact (fourPathPentagon p q r s).property.2.trans
      (applyOperation_congr rfl (Pasting.target_identity (carrier A) (Pasting.identity (fourPathDiagram p q r s))) _ _)

end NativeOperadic

end ComputationalPaths.Path.OmegaFoundations
