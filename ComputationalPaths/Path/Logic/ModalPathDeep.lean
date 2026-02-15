-- ModalPathDeep.lean: Modal logic via computational paths
-- Kripke frames, □/◇, K/T/S4/S5 axiom schemes, bisimulation,
-- temporal operators, dynamic logic
import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

-- ============================================================
-- SECTION 1: Kripke Frames via Paths
-- ============================================================

/-- A world in a Kripke frame -/
structure World where
  id : Nat
deriving DecidableEq, Repr

/-- Step in accessibility relation between worlds -/
inductive AccStep : World → World → Type where
  | access : (w v : World) → AccStep w v
  | refl : (w : World) → AccStep w w
  | symm : {w v : World} → AccStep w v → AccStep v w
  | trans : {w v u : World} → AccStep w v → AccStep v u → AccStep w u

/-- Path of accessibility steps -/
inductive AccPath : World → World → Type where
  | nil : (w : World) → AccPath w w
  | cons : {w v u : World} → AccStep w v → AccPath v u → AccPath w u

/-- Concatenation of accessibility paths -/
def AccPath.append : {w v u : World} → AccPath w v → AccPath v u → AccPath w u
  | _, _, _, AccPath.nil _, q => q
  | _, _, _, AccPath.cons s p, q => AccPath.cons s (AccPath.append p q)

/-- Reverse an accessibility path -/
def AccPath.reverse : {w v : World} → AccPath w v → AccPath v w
  | _, _, AccPath.nil w => AccPath.nil w
  | _, _, AccPath.cons s p => AccPath.append (AccPath.reverse p) (AccPath.cons (AccStep.symm s) (AccPath.nil _))

/-- CongrArg for accessibility paths under a world mapping -/
def AccStep.mapWorld (f : World → World)
    (lift : {w v : World} → AccStep w v → AccStep (f w) (f v))
    {w v : World} (s : AccStep w v) : AccStep (f w) (f v) :=
  lift s

-- ============================================================
-- SECTION 2: Modal Propositions via Path Quantification
-- ============================================================

/-- A modal proposition assigns truth values at worlds -/
def ModalProp := World → Prop

/-- Box: necessarily true = true at all accessible worlds -/
def boxProp (R : World → World → Prop) (φ : ModalProp) : ModalProp :=
  fun w => ∀ v, R w v → φ v

/-- Diamond: possibly true = true at some accessible world -/
def diamondProp (R : World → World → Prop) (φ : ModalProp) : ModalProp :=
  fun w => ∃ v, R w v ∧ φ v

/-- Path-based box: true at all path-reachable worlds -/
def pathBox (φ : ModalProp) : ModalProp :=
  fun w => ∀ v, Nonempty (AccPath w v) → φ v

/-- Path-based diamond: true at some path-reachable world -/
def pathDiamond (φ : ModalProp) : ModalProp :=
  fun w => ∃ v, Nonempty (AccPath w v) ∧ φ v

-- ============================================================
-- SECTION 3: Frame Properties as Path Properties
-- ============================================================

/-- Reflexive frame: every world accesses itself -/
def FrameReflexive (R : World → World → Prop) : Prop :=
  ∀ w, R w w

/-- Transitive frame -/
def FrameTransitive (R : World → World → Prop) : Prop :=
  ∀ w v u, R w v → R v u → R w u

/-- Symmetric frame -/
def FrameSymmetric (R : World → World → Prop) : Prop :=
  ∀ w v, R w v → R v w

/-- Euclidean frame -/
def FrameEuclidean (R : World → World → Prop) : Prop :=
  ∀ w v u, R w v → R w u → R v u

/-- Serial frame -/
def FrameSerial (R : World → World → Prop) : Prop :=
  ∀ w, ∃ v, R w v

-- ============================================================
-- SECTION 4: Axiom Scheme Proofs
-- ============================================================

/-- K axiom: □(φ → ψ) → □φ → □ψ -/
theorem axiom_K (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (h1 : boxProp R (fun v => φ v → ψ v) w) (h2 : boxProp R φ w)
    : boxProp R ψ w :=
  fun v hR => h1 v hR (h2 v hR)

/-- T axiom: □φ → φ (requires reflexivity) -/
theorem axiom_T (R : World → World → Prop) (hRefl : FrameReflexive R)
    (φ : ModalProp) (w : World) (h : boxProp R φ w) : φ w :=
  h w (hRefl w)

/-- 4 axiom: □φ → □□φ (requires transitivity) -/
theorem axiom_4 (R : World → World → Prop) (hTrans : FrameTransitive R)
    (φ : ModalProp) (w : World) (h : boxProp R φ w) : boxProp R (boxProp R φ) w :=
  fun v hWV u hVU => h u (hTrans w v u hWV hVU)

/-- B axiom: φ → □◇φ (requires symmetry) -/
theorem axiom_B (R : World → World → Prop) (hSym : FrameSymmetric R)
    (φ : ModalProp) (w : World) (h : φ w) : boxProp R (diamondProp R φ) w :=
  fun v hWV => ⟨w, hSym w v hWV, h⟩

/-- 5 axiom: ◇φ → □◇φ (requires Euclidean) -/
theorem axiom_5 (R : World → World → Prop) (hEuc : FrameEuclidean R)
    (φ : ModalProp) (w : World) (h : diamondProp R φ w) : boxProp R (diamondProp R φ) w :=
  fun v hWV => match h with
  | ⟨u, hWU, hφU⟩ => ⟨u, hEuc w v u hWV hWU, hφU⟩

/-- Dual: □φ ↔ ¬◇¬φ -/
theorem box_diamond_dual (R : World → World → Prop) (φ : ModalProp) (w : World)
    : boxProp R φ w ↔ ¬ diamondProp R (fun v => ¬ φ v) w :=
  ⟨fun hBox ⟨v, hR, hNeg⟩ => hNeg (hBox v hR),
   fun hNDia v hR => Classical.byContradiction fun hc => hNDia ⟨v, hR, hc⟩⟩

/-- D axiom: □φ → ◇φ (requires seriality) -/
theorem axiom_D (R : World → World → Prop) (hSer : FrameSerial R)
    (φ : ModalProp) (w : World) (h : boxProp R φ w) : diamondProp R φ w :=
  match hSer w with
  | ⟨v, hR⟩ => ⟨v, hR, h v hR⟩

-- ============================================================
-- SECTION 5: S5 = Reflexive + Symmetric + Transitive (Equivalence)
-- ============================================================

/-- Symmetric + transitive implies Euclidean -/
theorem sym_trans_euclidean (R : World → World → Prop)
    (hSym : FrameSymmetric R) (hTrans : FrameTransitive R)
    : FrameEuclidean R :=
  fun w v u hWV hWU => hTrans v w u (hSym w v hWV) hWU

/-- In S5, □φ → □□φ -/
theorem S5_box_idempotent (R : World → World → Prop)
    (_hRefl : FrameReflexive R) (_hSym : FrameSymmetric R) (hTrans : FrameTransitive R)
    (φ : ModalProp) (w : World) (h : boxProp R φ w) : boxProp R (boxProp R φ) w :=
  axiom_4 R hTrans φ w h

/-- In S5, ◇φ → □◇φ -/
theorem S5_diamond_box (R : World → World → Prop)
    (_hRefl : FrameReflexive R) (hSym : FrameSymmetric R) (hTrans : FrameTransitive R)
    (φ : ModalProp) (w : World) (h : diamondProp R φ w) : boxProp R (diamondProp R φ) w :=
  axiom_5 R (sym_trans_euclidean R hSym hTrans) φ w h

/-- In S5, ◇□φ → □φ -/
theorem S5_diamond_box_collapse (R : World → World → Prop)
    (_hRefl : FrameReflexive R) (hSym : FrameSymmetric R) (hTrans : FrameTransitive R)
    (φ : ModalProp) (w : World) (h : diamondProp R (boxProp R φ) w) : boxProp R φ w :=
  fun v hWV => match h with
  | ⟨u, hWU, hBoxU⟩ => hBoxU v (hTrans u w v (hSym w u hWU) hWV)

/-- In S5, ◇□φ → φ -/
theorem S5_diamond_box_to_val (R : World → World → Prop)
    (hRefl : FrameReflexive R) (hSym : FrameSymmetric R) (hTrans : FrameTransitive R)
    (φ : ModalProp) (w : World) (h : diamondProp R (boxProp R φ) w) : φ w :=
  axiom_T R hRefl φ w (S5_diamond_box_collapse R hRefl hSym hTrans φ w h)

-- ============================================================
-- SECTION 6: Path-based Modal Logic Theorems
-- ============================================================

/-- pathBox distributes over conjunction -/
theorem pathBox_and (φ ψ : ModalProp) (w : World)
    (h1 : pathBox φ w) (h2 : pathBox ψ w)
    : pathBox (fun v => φ v ∧ ψ v) w :=
  fun v p => ⟨h1 v p, h2 v p⟩

/-- pathBox is monotone -/
theorem pathBox_mono (φ ψ : ModalProp) (w : World)
    (hImp : ∀ v, φ v → ψ v) (h : pathBox φ w) : pathBox ψ w :=
  fun v p => hImp v (h v p)

/-- pathDiamond is monotone -/
theorem pathDiamond_mono (φ ψ : ModalProp) (w : World)
    (hImp : ∀ v, φ v → ψ v) (h : pathDiamond φ w) : pathDiamond ψ w :=
  match h with
  | ⟨v, p, hφ⟩ => ⟨v, p, hImp v hφ⟩

/-- pathBox implies value at self (via nil path) -/
theorem pathBox_refl (φ : ModalProp) (w : World) (h : pathBox φ w) : φ w :=
  h w ⟨AccPath.nil w⟩

/-- pathBox transitive: if pathBox (pathBox φ) w then pathBox φ w -/
theorem pathBox_trans (φ : ModalProp) (w : World)
    (h : pathBox (pathBox φ) w) : pathBox φ w :=
  fun v p => h v p v ⟨AccPath.nil v⟩

/-- pathDiamond from self -/
theorem pathDiamond_self (φ : ModalProp) (w : World)
    (h : φ w) : pathDiamond φ w :=
  ⟨w, ⟨AccPath.nil w⟩, h⟩

-- ============================================================
-- SECTION 7: Bisimulation via Path Correspondence
-- ============================================================

/-- A bisimulation relation between two Kripke frames -/
structure Bisimulation (R₁ R₂ : World → World → Prop) where
  rel : World → World → Prop
  forth : ∀ w₁ w₂, rel w₁ w₂ → ∀ v₁, R₁ w₁ v₁ → ∃ v₂, R₂ w₂ v₂ ∧ rel v₁ v₂
  back : ∀ w₁ w₂, rel w₁ w₂ → ∀ v₂, R₂ w₂ v₂ → ∃ v₁, R₁ w₁ v₁ ∧ rel v₁ v₂

/-- Bisimulation preserves box (forth direction) -/
theorem bisim_preserves_box (R₁ R₂ : World → World → Prop)
    (B : Bisimulation R₁ R₂) (φ₁ φ₂ : ModalProp)
    (hAtom : ∀ w₁ w₂, B.rel w₁ w₂ → (φ₁ w₁ ↔ φ₂ w₂))
    (w₁ w₂ : World) (hRel : B.rel w₁ w₂)
    (h : boxProp R₁ φ₁ w₁) : boxProp R₂ φ₂ w₂ :=
  fun v₂ hR₂ =>
    match B.back w₁ w₂ hRel v₂ hR₂ with
    | ⟨v₁, hR₁, hRelV⟩ => (hAtom v₁ v₂ hRelV).mp (h v₁ hR₁)

/-- Bisimulation preserves diamond -/
theorem bisim_preserves_diamond (R₁ R₂ : World → World → Prop)
    (B : Bisimulation R₁ R₂) (φ₁ φ₂ : ModalProp)
    (hAtom : ∀ w₁ w₂, B.rel w₁ w₂ → (φ₁ w₁ ↔ φ₂ w₂))
    (w₁ w₂ : World) (hRel : B.rel w₁ w₂)
    (h : diamondProp R₁ φ₁ w₁) : diamondProp R₂ φ₂ w₂ :=
  match h with
  | ⟨v₁, hR₁, hφ₁⟩ =>
    match B.forth w₁ w₂ hRel v₁ hR₁ with
    | ⟨v₂, hR₂, hRelV⟩ => ⟨v₂, hR₂, (hAtom v₁ v₂ hRelV).mp hφ₁⟩

-- ============================================================
-- SECTION 8: Frame Correspondence Results
-- ============================================================

/-- Reflexive frames validate T -/
theorem refl_validates_T (R : World → World → Prop) (hRefl : FrameReflexive R)
    : ∀ φ : ModalProp, ∀ w, boxProp R φ w → φ w :=
  fun φ w h => h w (hRefl w)

/-- Transitive frames validate 4 -/
theorem trans_validates_4 (R : World → World → Prop) (hTrans : FrameTransitive R)
    : ∀ φ : ModalProp, ∀ w, boxProp R φ w → boxProp R (boxProp R φ) w :=
  fun _φ w h v hWV u hVU => h u (hTrans w v u hWV hVU)

/-- Symmetric frames validate B -/
theorem sym_validates_B (R : World → World → Prop) (hSym : FrameSymmetric R)
    : ∀ φ : ModalProp, ∀ w, φ w → boxProp R (diamondProp R φ) w :=
  fun _φ w h v hWV => ⟨w, hSym w v hWV, h⟩

-- ============================================================
-- SECTION 9: Temporal Operators via Paths
-- ============================================================

/-- Until: φ holds until ψ along some path -/
inductive Until (R : World → World → Prop) (φ ψ : ModalProp) : World → Prop where
  | here : ∀ w, ψ w → Until R φ ψ w
  | step : ∀ w v, φ w → R w v → Until R φ ψ v → Until R φ ψ w

/-- Since: φ held since ψ (backward temporal) -/
inductive Since (R : World → World → Prop) (φ ψ : ModalProp) : World → Prop where
  | here : ∀ w, ψ w → Since R φ ψ w
  | step : ∀ w v, φ w → R v w → Since R φ ψ v → Since R φ ψ w

/-- Eventually = True Until ψ -/
def Eventually (R : World → World → Prop) (ψ : ModalProp) : World → Prop :=
  Until R (fun _ => True) ψ

/-- Always = ¬Eventually ¬φ -/
def Always (R : World → World → Prop) (φ : ModalProp) : World → Prop :=
  fun w => ¬ Eventually R (fun v => ¬ φ v) w

/-- Until is monotone in the goal -/
theorem until_mono_right (R : World → World → Prop) (φ ψ₁ ψ₂ : ModalProp)
    (hImp : ∀ v, ψ₁ v → ψ₂ v) (w : World) (h : Until R φ ψ₁ w) : Until R φ ψ₂ w := by
  induction h with
  | here w hw => exact Until.here w (hImp w hw)
  | step w v hw hR _ ih => exact Until.step w v hw hR ih

/-- Until: if ψ already holds, Until φ ψ holds -/
theorem until_of_goal (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (h : ψ w) : Until R φ ψ w :=
  Until.here w h

/-- Eventually is weaker than Until -/
theorem eventually_of_until (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (h : Until R φ ψ w) : Eventually R ψ w := by
  induction h with
  | here w hw => exact Until.here w hw
  | step w v _ hR _ ih => exact Until.step w v trivial hR ih

/-- Until preserves through transitivity step -/
theorem until_step_trans (R : World → World → Prop) (φ ψ : ModalProp) (w v u : World)
    (hw : φ w) (hR1 : R w v) (hv : φ v) (hR2 : R v u) (hu : Until R φ ψ u)
    : Until R φ ψ w :=
  Until.step w v hw hR1 (Until.step v u hv hR2 hu)

/-- Since is monotone in the goal -/
theorem since_mono_right (R : World → World → Prop) (φ ψ₁ ψ₂ : ModalProp)
    (hImp : ∀ v, ψ₁ v → ψ₂ v) (w : World) (h : Since R φ ψ₁ w) : Since R φ ψ₂ w := by
  induction h with
  | here w hw => exact Since.here w (hImp w hw)
  | step w v hw hR _ ih => exact Since.step w v hw hR ih

-- ============================================================
-- SECTION 10: Dynamic Logic via Paths
-- ============================================================

/-- A program is a relation between worlds -/
def Program := World → World → Prop

/-- Sequential composition -/
def Program.seq (α β : Program) : Program :=
  fun w u => ∃ v, α w v ∧ β v u

/-- Choice -/
def Program.choice (α β : Program) : Program :=
  fun w v => α w v ∨ β w v

/-- Iteration (reflexive-transitive closure) -/
inductive Program.star (α : Program) : Program where
  | refl : ∀ w, Program.star α w w
  | step : ∀ w v u, α w v → Program.star α v u → Program.star α w u

/-- Test program -/
def Program.test (φ : ModalProp) : Program :=
  fun w v => w = v ∧ φ w

/-- Dynamic box: [α]φ -/
def dynBox (α : Program) (φ : ModalProp) : ModalProp :=
  fun w => ∀ v, α w v → φ v

/-- Dynamic diamond: ⟨α⟩φ -/
def dynDiamond (α : Program) (φ : ModalProp) : ModalProp :=
  fun w => ∃ v, α w v ∧ φ v

/-- [α;β]φ ↔ [α][β]φ -/
theorem dynBox_seq (α β : Program) (φ : ModalProp) (w : World)
    : dynBox (α.seq β) φ w ↔ dynBox α (dynBox β φ) w :=
  ⟨fun h v hαv u hβu => h u ⟨v, hαv, hβu⟩,
   fun h u ⟨v, hαv, hβu⟩ => h v hαv u hβu⟩

/-- [α∪β]φ ↔ [α]φ ∧ [β]φ -/
theorem dynBox_choice (α β : Program) (φ : ModalProp) (w : World)
    : dynBox (α.choice β) φ w ↔ dynBox α φ w ∧ dynBox β φ w :=
  ⟨fun h => ⟨fun v hα => h v (Or.inl hα), fun v hβ => h v (Or.inr hβ)⟩,
   fun ⟨hα, hβ⟩ v hOr => hOr.elim (fun h => hα v h) (fun h => hβ v h)⟩

/-- [φ?]ψ ↔ φ → ψ (at same world) -/
theorem dynBox_test (φ ψ : ModalProp) (w : World)
    : dynBox (Program.test φ) ψ w ↔ (φ w → ψ w) :=
  ⟨fun h hφ => h w ⟨rfl, hφ⟩,
   fun h v ⟨hEq, hφ⟩ => hEq ▸ h hφ⟩

/-- ⟨α;β⟩φ ↔ ⟨α⟩⟨β⟩φ -/
theorem dynDiamond_seq (α β : Program) (φ : ModalProp) (w : World)
    : dynDiamond (α.seq β) φ w ↔ dynDiamond α (dynDiamond β φ) w :=
  ⟨fun ⟨u, ⟨v, hαv, hβu⟩, hφ⟩ => ⟨v, hαv, u, hβu, hφ⟩,
   fun ⟨v, hαv, u, hβu, hφ⟩ => ⟨u, ⟨v, hαv, hβu⟩, hφ⟩⟩

/-- [α*]φ → φ (star includes refl) -/
theorem dynBox_star_refl (α : Program) (φ : ModalProp) (w : World)
    (h : dynBox (Program.star α) φ w) : φ w :=
  h w (Program.star.refl w)

/-- [α*]φ → [α][α*]φ -/
theorem dynBox_star_step (α : Program) (φ : ModalProp) (w : World)
    (h : dynBox (Program.star α) φ w)
    : dynBox α (dynBox (Program.star α) φ) w :=
  fun v hαv u hStar => h u (Program.star.step w v u hαv hStar)

/-- ⟨φ?⟩ψ ↔ φ ∧ ψ (at same world) -/
theorem dynDiamond_test (φ ψ : ModalProp) (w : World)
    : dynDiamond (Program.test φ) ψ w ↔ (φ w ∧ ψ w) :=
  ⟨fun ⟨v, ⟨hEq, hφ⟩, hψ⟩ => ⟨hEq ▸ hφ, hEq ▸ hψ⟩,
   fun ⟨hφ, hψ⟩ => ⟨w, ⟨rfl, hφ⟩, hψ⟩⟩

/-- ⟨α∪β⟩φ ↔ ⟨α⟩φ ∨ ⟨β⟩φ -/
theorem dynDiamond_choice (α β : Program) (φ : ModalProp) (w : World)
    : dynDiamond (α.choice β) φ w ↔ dynDiamond α φ w ∨ dynDiamond β φ w :=
  ⟨fun ⟨v, hOr, hφ⟩ => hOr.elim (fun h => Or.inl ⟨v, h, hφ⟩) (fun h => Or.inr ⟨v, h, hφ⟩),
   fun h => h.elim (fun ⟨v, hα, hφ⟩ => ⟨v, Or.inl hα, hφ⟩) (fun ⟨v, hβ, hφ⟩ => ⟨v, Or.inr hβ, hφ⟩)⟩

-- ============================================================
-- SECTION 11: Multi-modal Logic (Indexed Modalities)
-- ============================================================

/-- Multi-agent box -/
def multiBox (R : Nat → World → World → Prop) (i : Nat) (φ : ModalProp) : ModalProp :=
  fun w => ∀ v, R i w v → φ v

/-- Common knowledge: everyone knows, everyone knows everyone knows, etc. -/
inductive CommonReach (R : Nat → World → World → Prop) (agents : List Nat) : World → World → Prop where
  | refl : ∀ w, CommonReach R agents w w
  | step : ∀ w v u i, i ∈ agents → R i w v → CommonReach R agents v u → CommonReach R agents w u

def CommonReach.trans' {R : Nat → World → World → Prop} {agents : List Nat}
    {w v u : World} (h1 : CommonReach R agents w v) (h2 : CommonReach R agents v u) : CommonReach R agents w u := by
  induction h1 with
  | refl => exact h2
  | step w' m _ i hi hR _ ih => exact CommonReach.step w' m u i hi hR (ih h2)

def commonBox (R : Nat → World → World → Prop) (agents : List Nat) (φ : ModalProp) : ModalProp :=
  fun w => ∀ v, CommonReach R agents w v → φ v

/-- Common knowledge implies individual knowledge -/
theorem common_implies_individual (R : Nat → World → World → Prop) (agents : List Nat)
    (i : Nat) (hi : i ∈ agents) (φ : ModalProp) (w : World)
    (h : commonBox R agents φ w) : multiBox R i φ w :=
  fun v hR => h v (CommonReach.step w v v i hi hR (CommonReach.refl v))

/-- Common knowledge is self-referential -/
theorem common_box_idempotent (R : Nat → World → World → Prop) (agents : List Nat)
    (φ : ModalProp) (w : World)
    (h : commonBox R agents φ w) : commonBox R agents (commonBox R agents φ) w :=
  fun v hReach u hReach2 => h u (CommonReach.trans' hReach hReach2)

-- ============================================================
-- SECTION 12: Filtration and Finite Model Property
-- ============================================================

/-- Equivalence class of worlds under a set of formulas -/
def worldEquiv (props : List ModalProp) (w v : World) : Prop :=
  ∀ φ, φ ∈ props → (φ w ↔ φ v)

/-- worldEquiv is reflexive -/
theorem worldEquiv_refl (props : List ModalProp) (w : World)
    : worldEquiv props w w :=
  fun _ _ => Iff.rfl

/-- worldEquiv is symmetric -/
theorem worldEquiv_symm (props : List ModalProp) (w v : World)
    (h : worldEquiv props w v) : worldEquiv props v w :=
  fun φ hφ => (h φ hφ).symm

/-- worldEquiv is transitive -/
theorem worldEquiv_trans (props : List ModalProp) (w v u : World)
    (h1 : worldEquiv props w v) (h2 : worldEquiv props v u)
    : worldEquiv props w u :=
  fun φ hφ => (h1 φ hφ).trans (h2 φ hφ)

-- ============================================================
-- SECTION 13: Additional Frame Properties and Theorems
-- ============================================================

/-- Euclidean + reflexive implies symmetric -/
theorem euc_refl_sym (R : World → World → Prop)
    (hEuc : FrameEuclidean R) (hRefl : FrameReflexive R)
    : FrameSymmetric R :=
  fun w v hWV => hEuc w v w hWV (hRefl w)

/-- Symmetric + Euclidean implies transitive -/
theorem sym_euc_trans (R : World → World → Prop)
    (hSym : FrameSymmetric R) (hEuc : FrameEuclidean R)
    : FrameTransitive R :=
  fun w v u hWV hVU => hEuc v w u (hSym w v hWV) hVU

/-- Box-diamond interaction -/
theorem box_implies_not_diamond_neg (R : World → World → Prop) (φ : ModalProp) (w : World)
    (h : boxProp R φ w) : ¬ diamondProp R (fun v => ¬ φ v) w :=
  fun ⟨v, hR, hNeg⟩ => hNeg (h v hR)

/-- Diamond implies not box neg -/
theorem diamond_implies_not_box_neg (R : World → World → Prop) (φ : ModalProp) (w : World)
    (h : diamondProp R φ w) : ¬ boxProp R (fun v => ¬ φ v) w :=
  fun hBox => match h with
  | ⟨v, hR, hφ⟩ => hBox v hR hφ

/-- Necessitation: if φ is universally true, □φ holds -/
theorem necessitation (R : World → World → Prop) (φ : ModalProp)
    (h : ∀ w, φ w) (w : World) : boxProp R φ w :=
  fun v _ => h v

/-- K + necessitation: modus ponens under box -/
theorem box_modus_ponens (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (hImp : boxProp R (fun v => φ v → ψ v) w) (hPrem : boxProp R φ w)
    : boxProp R ψ w :=
  axiom_K R φ ψ w hImp hPrem

/-- Box distributes over conjunction -/
theorem box_and (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (h1 : boxProp R φ w) (h2 : boxProp R ψ w)
    : boxProp R (fun v => φ v ∧ ψ v) w :=
  fun v hR => ⟨h1 v hR, h2 v hR⟩

/-- Diamond distributes over disjunction (forward) -/
theorem diamond_or (R : World → World → Prop) (φ ψ : ModalProp) (w : World)
    (h : diamondProp R (fun v => φ v ∨ ψ v) w)
    : diamondProp R φ w ∨ diamondProp R ψ w :=
  match h with
  | ⟨v, hR, Or.inl hφ⟩ => Or.inl ⟨v, hR, hφ⟩
  | ⟨v, hR, Or.inr hψ⟩ => Or.inr ⟨v, hR, hψ⟩

/-- Reflexive + Euclidean = S5 (equivalence) -/
theorem refl_euc_is_equivalence (R : World → World → Prop)
    (hRefl : FrameReflexive R) (hEuc : FrameEuclidean R)
    : FrameReflexive R ∧ FrameSymmetric R ∧ FrameTransitive R :=
  ⟨hRefl, euc_refl_sym R hEuc hRefl, sym_euc_trans R (euc_refl_sym R hEuc hRefl) hEuc⟩

/-- Star is transitive -/
theorem star_trans (α : Program) (w v u : World)
    (h1 : Program.star α w v) (h2 : Program.star α v u)
    : Program.star α w u := by
  induction h1 with
  | refl => exact h2
  | step _ m _ hα _ ih => exact Program.star.step _ m u hα (ih h2)

-- Total: 42 theorems/lemmas

end ComputationalPaths
