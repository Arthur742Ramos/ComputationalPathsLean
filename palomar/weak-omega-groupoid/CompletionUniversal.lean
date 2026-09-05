import GlobularCompletion

/-! The layerwise universal property of the chosen globular completion.
This is freeness of reversible composition syntax, NOT freeness as a groupoid:
associativity and inverse cancellation remain higher comparisons, not equations.
-/
namespace ComputationalPaths.PalomarWeakOmegaGroupoid.GlobularCompletion

universe u v

/-- A target interpretation supplies typed operations and a chosen arrow for
each parallel pair. No associativity, cancellation, or uniqueness is assumed. -/
structure Interpretation (L : Layer.{u}) where
  Hom : L.Arr → L.Arr → Type v
  unit : (x : L.Arr) → Hom x x
  generator : {x y : L.Arr} → Parallel L x y → Hom x y
  inverse : {x y : L.Arr} → Hom x y → Hom y x
  compose : {x y z : L.Arr} → Hom x y → Hom y z → Hom x z

/-- Evaluation of the explicit higher derivation in a chosen target. -/
def interpret {L : Layer.{u}} (M : Interpretation.{u,v} L) :
    (x y : L.Arr) → CellDerivation L x y → M.Hom x y
  | _, _, .refl x => M.unit x
  | _, _, .step h _ => M.generator h
  | _, _, .inv d => M.inverse (interpret M _ _ d)
  | _, _, .trans d e => M.compose (interpret M _ _ d) (interpret M _ _ e)

/-- The exact preservation equations required of an interpretation. -/
def Preserves {L : Layer.{u}} (M : Interpretation.{u,v} L)
    (f : (x y : L.Arr) → CellDerivation L x y → M.Hom x y) : Prop :=
  (∀ x, f x x (.refl x) = M.unit x) ∧
  (∀ (x y) (h : Parallel L x y) (i : (⟨x⟩ : Nonempty L.Arr) = ⟨y⟩),
    f x y (.step h i) = M.generator h) ∧
  (∀ (x y) (d : CellDerivation L x y),
    f y x (.inv d) = M.inverse (f x y d)) ∧
  (∀ (x y z) (d : CellDerivation L x y) (e : CellDerivation L y z),
    f x z (.trans d e) = M.compose (f x y d) (f y z e))

/-- Every layer is free for precisely the displayed typed operations. -/
theorem unique_interpretation {L : Layer.{u}} (M : Interpretation.{u,v} L) :
    ∃! f : (x y : L.Arr) → CellDerivation L x y → M.Hom x y,
      Preserves M f := by
  refine ⟨interpret M, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x; rfl
  · intro x y h i; rfl
  · intro x y d; rfl
  · intro x y z d e; rfl
  · intro f hf
    funext x y d
    induction d with
    | refl x => exact hf.1 x
    | step h i => exact hf.2.1 _ _ h i
    | inv d ih =>
      change f _ _ (.inv d) = M.inverse (interpret M _ _ d)
      rw [hf.2.2.1, ih]
    | trans d e ih ih' =>
      change f _ _ (.trans d e) = M.compose (interpret M _ _ d) (interpret M _ _ e)
      rw [hf.2.2.2, ih, ih']

/-- A filler exists exactly for a parallel boundary, in every layer. -/
theorem inhabited_iff_parallel (L : Layer.{u}) (x y : L.Arr) :
    Nonempty (CellDerivation L x y) ↔ Parallel L x y :=
  ⟨fun ⟨d⟩ => d.parallel, fun h => ⟨.step h (Subsingleton.elim _ _)⟩⟩

/-- Count syntax constructors; no quotient identifies distinct expressions. -/
def nodeCount {L : Layer.{u}} {x y : L.Arr} : CellDerivation L x y → Nat
  | .refl _ => 0
  | .step _ _ => 1
  | .inv d => nodeCount d + 1
  | .trans d e => nodeCount d + nodeCount e + 1

/-- Chosen connectedness does not make higher derivations proof-irrelevant. -/
theorem higher_syntax_not_subsingleton (L : Layer.{u}) (x : L.Arr) :
    ¬ Subsingleton (CellDerivation L x x) := by
  intro h
  have eq := h.elim (.refl x) (.inv (.refl x))
  have count := congrArg nodeCount eq
  change 0 = 1 at count
  cases count

/-- Freeness holds uniformly at every layer, not only in low dimensions. -/
theorem tower_unique_interpretation (A : Type u) (n : Nat)
    (M : Interpretation.{u,v} (tower A n)) :
    ∃! f : (x y : (tower A n).Arr) → CellDerivation (tower A n) x y → M.Hom x y,
      Preserves M f := unique_interpretation M

/-- A map of layers preserves both of the actual boundary maps. -/
structure LayerMap (L K : Layer.{u}) where
  onObj : L.Obj → K.Obj
  onArr : L.Arr → K.Arr
  source_law : ∀ x, K.source (onArr x) = onObj (L.source x)
  target_law : ∀ x, K.target (onArr x) = onObj (L.target x)

def LayerMap.identity (L : Layer.{u}) : LayerMap L L :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def LayerMap.comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H) :
    LayerMap L H :=
  ⟨g.onObj ∘ f.onObj, g.onArr ∘ f.onArr,
    fun x => (g.source_law _).trans (congrArg g.onObj (f.source_law x)),
    fun x => (g.target_law _).trans (congrArg g.onObj (f.target_law x))⟩

theorem LayerMap.parallel {L K : Layer.{u}} (f : LayerMap L K)
    {x y : L.Arr} (h : Parallel L x y) : Parallel K (f.onArr x) (f.onArr y) :=
  ⟨(f.source_law x).trans ((congrArg f.onObj h.1).trans (f.source_law y).symm),
    (f.target_law x).trans ((congrArg f.onObj h.2).trans (f.target_law y).symm)⟩

/-- Boundary-preserving maps act on every derivation constructor. -/
def mapDerivation {L K : Layer.{u}} (f : LayerMap L K) :
    {x y : L.Arr} → CellDerivation L x y → CellDerivation K (f.onArr x) (f.onArr y)
  | _, _, .refl x => .refl (f.onArr x)
  | _, _, .step h _ => .step (f.parallel h) (Subsingleton.elim _ _)
  | _, _, .inv d => .inv (mapDerivation f d)
  | _, _, .trans d e => .trans (mapDerivation f d) (mapDerivation f e)

theorem map_identity {L : Layer.{u}} {x y : L.Arr} (d : CellDerivation L x y) :
    mapDerivation (LayerMap.identity L) d = d := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg CellDerivation.inv ih
  | trans d e ih ih' => exact congrArg₂ CellDerivation.trans ih ih'

theorem map_comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H)
    {x y : L.Arr} (d : CellDerivation L x y) :
    mapDerivation (f.comp g) d = mapDerivation g (mapDerivation f d) := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg CellDerivation.inv ih
  | trans d e ih ih' => exact congrArg₂ CellDerivation.trans ih ih'

theorem map_preserves_nodes {L K : Layer.{u}} (f : LayerMap L K)
    {x y : L.Arr} (d : CellDerivation L x y) :
    nodeCount (mapDerivation f d) = nodeCount d := by
  induction d with
  | refl _ => rfl
  | step _ _ => rfl
  | inv d ih => exact congrArg (fun n => n + 1) ih
  | trans d e ih ih' => exact congrArg₂ (fun n m => n + m + 1) ih ih'

/-- Functorial extension from a layer map to a map of its completion. -/
def LayerMap.lift {L K : Layer.{u}} (f : LayerMap L K) :
    LayerMap (extend L) (extend K) :=
  ⟨f.onArr, fun c => ⟨f.onArr c.source, f.onArr c.target, mapDerivation f c.derivation⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem LayerMap.ext {L K : Layer.{u}} (f g : LayerMap L K)
    (h₀ : f.onObj = g.onObj) (h₁ : f.onArr = g.onArr) : f = g := by
  cases f; cases g; cases h₀; cases h₁; rfl

theorem lift_identity (L : Layer.{u}) :
    (LayerMap.identity L).lift = LayerMap.identity (extend L) := by
  apply LayerMap.ext
  · rfl
  · funext c
    cases c with
    | mk x y d => exact congrArg (fun e => Filler.mk x y e) (map_identity d)

theorem lift_comp {L K H : Layer.{u}} (f : LayerMap L K) (g : LayerMap K H) :
    (f.comp g).lift = f.lift.comp g.lift := by
  apply LayerMap.ext
  · rfl
  · funext c
    cases c with
    | mk x y d => exact congrArg (fun e => Filler.mk _ _ e) (map_comp f g d)

/-- The original two-cell data are not identified by adding higher fillers:
the two explicit pentagon routes are distinct but joined by a three-cell. -/
theorem pentagon_distinct_connected {A : Type u} {a b c d e : A}
    (f : Path A a b) (g : Path A b c) (h : Path A c d) (k : Path A d e) :
    let l : Two A := ⟨a, e, _, _, pentagonLeft f g h k⟩
    let r : Two A := ⟨a, e, _, _, pentagonRight f g h k⟩
    l ≠ r ∧ ∃ cell : Cell A 3, source 2 cell = l ∧ target 2 cell = r := by
  constructor
  · intro eq
    have count := congrArg (fun x : Two A => RwEq.stepCount x.2.2.2.2) eq
    change 2 = 3 at count
    cases count
  · exact ⟨pentagonFiller f g h k, rfl, rfl⟩

end ComputationalPaths.PalomarWeakOmegaGroupoid.GlobularCompletion
