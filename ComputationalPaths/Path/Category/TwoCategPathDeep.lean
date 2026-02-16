/-
  ComputationalPaths.Path.Category.TwoCategPathDeep

  2-Categories and Path Coherence
  ================================

  We develop the theory of 2-categories using computational paths:
  - 0-cells are types
  - 1-cells are functions between types
  - 2-cells are Paths between function values (pointwise)

  Horizontal composition uses congrArg, vertical composition uses trans.
  We prove whiskering properties, adjunction triangle identities,
  mates correspondence, 2-functors, 2-natural transformations,
  and coherence results.

  Key insight: since `Eq` lives in `Prop`, any two `toEq` proofs are
  definitionally equal (proof irrelevance). This gives coherence for free.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open Path

universe u v w

namespace TwoCategPathDeep

variable {A : Type u} {B : Type v} {C : Type w}

-- ============================================================================
-- Section 1: Basic 2-Category Structure
-- ============================================================================

/-- A 2-cell between 1-cells f g : A → B is a pointwise Path. -/
def Cell2 (f g : A → B) := (a : A) → Path (f a) (g a)

/-- Identity 2-cell. -/
def id2 (f : A → B) : Cell2 f f :=
  fun a => Path.refl (f a)

/-- Vertical composition of 2-cells. -/
def vcomp {f g h : A → B}
    (α : Cell2 f g) (β : Cell2 g h) : Cell2 f h :=
  fun a => Path.trans (α a) (β a)

/-- Horizontal composition of 2-cells via congrArg. -/
def hcomp {f g : A → B} {h k : B → C}
    (α : Cell2 f g) (β : Cell2 h k) : Cell2 (h ∘ f) (k ∘ g) :=
  fun a => Path.trans (Path.congrArg h (α a)) (β (g a))

/-- Left whiskering: compose a 1-cell on the left with a 2-cell. -/
def whiskerL (h : B → C) {f g : A → B} (α : Cell2 f g) : Cell2 (h ∘ f) (h ∘ g) :=
  fun a => Path.congrArg h (α a)

/-- Right whiskering: compose a 1-cell on the right with a 2-cell. -/
def whiskerR {h k : B → C} (β : Cell2 h k) (f : A → B) : Cell2 (h ∘ f) (k ∘ f) :=
  fun a => β (f a)

/-- Vertical inverse of a 2-cell. -/
def vinv {f g : A → B} (α : Cell2 f g) : Cell2 g f :=
  fun a => Path.symm (α a)

-- ============================================================================
-- Section 2: Vertical Composition Properties
-- ============================================================================

/-- Theorem 1: Vertical composition is associative. -/
theorem vcomp_assoc {f g h k : A → B}
    (α : Cell2 f g) (β : Cell2 g h) (γ : Cell2 h k) :
    vcomp (vcomp α β) γ = vcomp α (vcomp β γ) := by
  funext a; exact Path.trans_assoc (α a) (β a) (γ a)

/-- Theorem 2: Left identity for vertical composition. -/
theorem vcomp_id_left {f g : A → B} (α : Cell2 f g) :
    vcomp (id2 f) α = α := by
  funext a; exact Path.trans_refl_left (α a)

/-- Theorem 3: Right identity for vertical composition. -/
theorem vcomp_id_right {f g : A → B} (α : Cell2 f g) :
    vcomp α (id2 g) = α := by
  funext a; exact Path.trans_refl_right (α a)

/-- Theorem 4: Double inverse is identity. -/
theorem vinv_vinv {f g : A → B} (α : Cell2 f g) :
    vinv (vinv α) = α := by
  funext a; exact Path.symm_symm (α a)

/-- Theorem 5: Inverse distributes over vertical composition (anti-homomorphism). -/
theorem vinv_vcomp_distrib {f g h : A → B}
    (α : Cell2 f g) (β : Cell2 g h) :
    vinv (vcomp α β) = vcomp (vinv β) (vinv α) := by
  funext a; exact Path.symm_trans (α a) (β a)

/-- Theorem 6: Inverse of identity is identity. -/
theorem vinv_id2 (f : A → B) : vinv (id2 f) = id2 f := by
  funext a; exact Path.symm_refl (f a)

-- ============================================================================
-- Section 3: toEq-level properties (proof irrelevance in Prop)
-- ============================================================================

/-- Theorem 7: Left cancellation at toEq level. -/
theorem vinv_vcomp_toEq {f g : A → B} (α : Cell2 f g) (a : A) :
    (vcomp (vinv α) α a).toEq = rfl := by simp [vcomp, vinv]

/-- Theorem 8: Right cancellation at toEq level. -/
theorem vcomp_vinv_toEq {f g : A → B} (α : Cell2 f g) (a : A) :
    (vcomp α (vinv α) a).toEq = rfl := by simp [vcomp, vinv]

/-- Theorem 9: toEq is functorial. -/
theorem toEq_vcomp {f g h : A → B}
    (α : Cell2 f g) (β : Cell2 g h) (a : A) :
    (vcomp α β a).toEq = ((α a).toEq).trans ((β a).toEq) := by
  simp [vcomp]

/-- Theorem 10: toEq of identity is rfl. -/
theorem toEq_id2 (f : A → B) (a : A) :
    (id2 f a).toEq = rfl := by simp [id2]

-- ============================================================================
-- Section 4: Whiskering Properties
-- ============================================================================

/-- Theorem 11: Left whiskering preserves identity. -/
theorem whiskerL_id (h : B → C) (f : A → B) :
    whiskerL h (id2 f) = id2 (h ∘ f) := by
  funext a; simp [whiskerL, id2]

/-- Theorem 12: Right whiskering preserves identity. -/
theorem whiskerR_id (h : B → C) (f : A → B) :
    whiskerR (id2 h) f = id2 (h ∘ f) := by
  funext a; simp [whiskerR, id2]

/-- Theorem 13: Left whiskering distributes over vertical composition. -/
theorem whiskerL_vcomp (h : B → C) {f g k : A → B}
    (α : Cell2 f g) (β : Cell2 g k) :
    whiskerL h (vcomp α β) = vcomp (whiskerL h α) (whiskerL h β) := by
  funext a; exact Path.congrArg_trans h (α a) (β a)

/-- Theorem 14: Right whiskering distributes over vertical composition. -/
theorem whiskerR_vcomp {h k m : B → C}
    (α : Cell2 h k) (β : Cell2 k m) (f : A → B) :
    whiskerR (vcomp α β) f = vcomp (whiskerR α f) (whiskerR β f) := by
  funext a; simp [whiskerR, vcomp]

/-- Theorem 15: Left whiskering preserves inverse. -/
theorem whiskerL_vinv (h : B → C) {f g : A → B} (α : Cell2 f g) :
    whiskerL h (vinv α) = vinv (whiskerL h α) := by
  funext a; exact Path.congrArg_symm h (α a)

/-- Theorem 16: Left whiskering by identity function. -/
theorem whiskerL_idfun {f g : A → B} (α : Cell2 f g) :
    whiskerL (fun x => x) α = α := by
  funext a; exact Path.congrArg_id (α a)

/-- Theorem 17: Left whiskering composition law. -/
theorem whiskerL_comp (j : B → C) (h : A → B)
    {f g : C → A} (α : Cell2 f g) :
    whiskerL j (whiskerL h α) = whiskerL (fun x => j (h x)) α := by
  funext a
  show Path.congrArg j (Path.congrArg h (α a)) =
       Path.congrArg (fun x => j (h x)) (α a)
  exact (Path.congrArg_comp j h (α a)).symm

/-- Theorem 18: Right whiskering composition law. -/
theorem whiskerR_comp {h k : C → B}
    (β : Cell2 h k) (g : A → C) (f : B → A) :
    whiskerR (whiskerR β g) f = whiskerR β (g ∘ f) := by
  funext a; rfl

/-- Theorem 19: Mixed whiskering commutes. -/
theorem whiskerL_whiskerR (j : C → B)
    {h k : A → C} (β : Cell2 h k) (f : B → A) :
    whiskerL j (whiskerR β f) = whiskerR (whiskerL j β) f := by
  funext a; rfl

-- ============================================================================
-- Section 5: Horizontal Composition Properties
-- ============================================================================

/-- Theorem 20: Horizontal composition with identity 2-cells. -/
theorem hcomp_id_id (f : A → B) (h : B → C) :
    hcomp (id2 f) (id2 h) = id2 (h ∘ f) := by
  funext a; simp [hcomp, id2]

/-- Alternative horizontal composition (whiskerR then whiskerL). -/
def hcomp' {f g : A → B} {h k : B → C}
    (α : Cell2 f g) (β : Cell2 h k) : Cell2 (h ∘ f) (k ∘ g) :=
  fun a => Path.trans (β (f a)) (Path.congrArg k (α a))

/-- Theorem 21: hcomp and hcomp' agree at toEq level (naturality square). -/
theorem hcomp_eq_hcomp'_toEq {f g : A → B} {h k : B → C}
    (α : Cell2 f g) (β : Cell2 h k) (a : A) :
    (hcomp α β a).toEq = (hcomp' α β a).toEq := by
  simp [hcomp, hcomp']

-- ============================================================================
-- Section 6: The Interchange Law
-- ============================================================================

/-- Theorem 22: Interchange law at toEq level. -/
theorem interchange_toEq {f g h₁ : A → B} {j k l : B → C}
    (α : Cell2 f g) (β : Cell2 g h₁)
    (γ : Cell2 j k) (δ : Cell2 k l) (a : A) :
    (hcomp (vcomp α β) (vcomp γ δ) a).toEq =
    (vcomp (hcomp α γ) (hcomp β δ) a).toEq := by
  simp [hcomp, vcomp]

/-- Theorem 23: Interchange specialized to identity cells. -/
theorem interchange_id_toEq {f : A → B} {h : B → C}
    (α : Cell2 f f) (γ : Cell2 h h) (a : A) :
    (hcomp (vcomp (id2 f) α) (vcomp (id2 h) γ) a).toEq =
    (vcomp (hcomp (id2 f) (id2 h)) (hcomp α γ) a).toEq := by
  simp [hcomp, vcomp, id2]

-- ============================================================================
-- Section 7: Adjunction Structure
-- ============================================================================

/-- An adjunction in our 2-categorical setting: f ⊣ g with unit and counit as 2-cells. -/
structure Adjunction2 (f : A → B) (g : B → A) where
  unit   : Cell2 (fun a => a) (g ∘ f)
  counit : Cell2 (f ∘ g) (fun b => b)

/-- Theorem 24: Triangle identity cell for left adjoint. -/
def triangleL {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) : Cell2 f f :=
  fun a => Path.trans (Path.congrArg f (adj.unit a)) (adj.counit (f a))

/-- Theorem 25: Triangle identity cell for right adjoint. -/
def triangleR {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) : Cell2 g g :=
  fun b => Path.trans (adj.unit (g b)) (Path.congrArg g (adj.counit b))

/-- Theorem 26: Triangle identity (left) holds at toEq level. -/
theorem triangleL_toEq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) (a : A) :
    (triangleL adj a).toEq = rfl := by simp [triangleL]

/-- Theorem 27: Triangle identity (right) holds at toEq level. -/
theorem triangleR_toEq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) (b : B) :
    (triangleR adj b).toEq = rfl := by simp [triangleR]

/-- Adjunction with triangle identities at toEq level. -/
structure AdjTriangle (f : A → B) (g : B → A) extends Adjunction2 f g where
  triL : ∀ a, (triangleL toAdjunction2 a).toEq = rfl
  triR : ∀ b, (triangleR toAdjunction2 b).toEq = rfl

/-- Theorem 28: Identity adjunction. -/
def idAdjunction : Adjunction2 (fun a : A => a) (fun a : A => a) where
  unit   := id2 (fun a => a)
  counit := id2 (fun a => a)

/-- Theorem 29: Identity adjunction satisfies triangle L at toEq. -/
theorem idAdj_triangleL_toEq (a : A) :
    (triangleL (idAdjunction (A := A)) a).toEq = rfl := by
  simp [triangleL, idAdjunction, id2]

/-- Theorem 30: Identity adjunction satisfies triangle R at toEq. -/
theorem idAdj_triangleR_toEq (a : A) :
    (triangleR (idAdjunction (A := A)) a).toEq = rfl := by
  simp [triangleR, idAdjunction, id2]

/-- Theorem 31: Full identity adjunction with triangles. -/
def idAdjTriangle : AdjTriangle (fun a : A => a) (fun a : A => a) where
  unit   := id2 (fun a => a)
  counit := id2 (fun a => a)
  triL := idAdj_triangleL_toEq
  triR := idAdj_triangleR_toEq

-- ============================================================================
-- Section 8: Mates Correspondence
-- ============================================================================

/-- Theorem 32: Forward mates: given f ⊣ g and σ : k → l ∘ f, produce mate at toEq. -/
def mate_forward_eq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) {k l : A → C}
    (σ : Cell2 k l) (b : B) : k (g b) = l (g b) :=
  (σ (g b)).toEq

/-- Theorem 33: Backward mates via congrArg and unit. -/
def mate_backward {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) {k l : A → C}
    (τ : ∀ b, k (g b) = l (g b)) : Cell2 k l :=
  fun a =>
    Path.trans
      (Path.congrArg k (adj.unit a))
      (Path.trans
        (Path.mk [Step.mk (k (g (f a))) (l (g (f a))) (τ (f a))] (τ (f a)))
        (Path.congrArg l (Path.symm (adj.unit a))))

/-- Theorem 34: Mates roundtrip at toEq level. -/
theorem mate_roundtrip_toEq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) {k l : A → C}
    (σ : Cell2 k l) (a : A) :
    (mate_backward adj (mate_forward_eq adj σ) a).toEq = (σ a).toEq := by
  simp [mate_backward, mate_forward_eq]

-- ============================================================================
-- Section 9: Composing Adjunctions
-- ============================================================================

/-- Theorem 35: Composing adjunctions: if f ⊣ g and h ⊣ k, then (h ∘ f) ⊣ (g ∘ k). -/
def compAdjunction {f : A → B} {g : B → A} {h : B → C} {k : C → B}
    (adj₁ : Adjunction2 f g) (adj₂ : Adjunction2 h k) :
    Adjunction2 (fun a => h (f a)) (fun c => g (k c)) where
  unit := fun a =>
    Path.trans (adj₁.unit a) (Path.congrArg g (adj₂.unit (f a)))
  counit := fun c =>
    Path.trans (Path.congrArg h (adj₁.counit (k c))) (adj₂.counit c)

/-- Theorem 36: Composed adjunction triangle L at toEq. -/
theorem compAdj_triangleL_toEq {f : A → B} {g : B → A} {h : B → C} {k : C → B}
    (adj₁ : Adjunction2 f g) (adj₂ : Adjunction2 h k) (a : A) :
    (triangleL (compAdjunction adj₁ adj₂) a).toEq = rfl := by
  simp [triangleL, compAdjunction]

/-- Theorem 37: Composed adjunction triangle R at toEq. -/
theorem compAdj_triangleR_toEq {f : A → B} {g : B → A} {h : B → C} {k : C → B}
    (adj₁ : Adjunction2 f g) (adj₂ : Adjunction2 h k) (c : C) :
    (triangleR (compAdjunction adj₁ adj₂) c).toEq = rfl := by
  simp [triangleR, compAdjunction]

-- ============================================================================
-- Section 10: 2-Functors
-- ============================================================================

/-- A 2-functor maps 0-cells, 1-cells, and 2-cells preserving structure. -/
structure TwoFunctor (F₀ : Type u → Type v) where
  map₁ : {X Y : Type u} → (X → Y) → (F₀ X → F₀ Y)
  map₂ : {X Y : Type u} → {f g : X → Y} → Cell2 f g → Cell2 (map₁ f) (map₁ g)
  map₂_id : {X Y : Type u} → (f : X → Y) → map₂ (id2 f) = id2 (map₁ f)
  map₂_vcomp : {X Y : Type u} → {f g h : X → Y} →
    (α : Cell2 f g) → (β : Cell2 g h) →
    map₂ (vcomp α β) = vcomp (map₂ α) (map₂ β)

/-- Theorem 38: A 2-functor preserves vertical inverses at toEq level. -/
theorem twoFunctor_preserves_vinv_toEq {F₀ : Type u → Type v}
    (F : TwoFunctor F₀) {X Y : Type u} {f g : X → Y}
    (α : Cell2 f g) (x : F₀ X) :
    (F.map₂ (vinv α) x).toEq = (vinv (F.map₂ α) x).toEq := by
  simp [vinv]

/-- Theorem 39: Identity 2-functor. -/
def idTwoFunctor : TwoFunctor (id : Type u → Type u) where
  map₁ := fun f => f
  map₂ := fun α => α
  map₂_id := fun _ => rfl
  map₂_vcomp := fun _ _ => rfl

-- ============================================================================
-- Section 11: 2-Natural Transformations
-- ============================================================================

/-- A 2-natural transformation between 2-functors. -/
structure TwoNatTrans {F₀ G₀ : Type u → Type v}
    (F : TwoFunctor F₀) (G : TwoFunctor G₀) where
  component : (X : Type u) → F₀ X → G₀ X
  naturality : {X Y : Type u} → (f : X → Y) →
    Cell2 (G.map₁ f ∘ component X) (component Y ∘ F.map₁ f)

/-- Theorem 40: Identity 2-natural transformation. -/
def idTwoNatTrans {F₀ : Type u → Type v} (F : TwoFunctor F₀) :
    TwoNatTrans F F where
  component := fun _ x => x
  naturality := fun _ => id2 _

/-- Theorem 41: Naturality at toEq level for identity nat trans. -/
theorem idNatTrans_naturality_toEq {F₀ : Type u → Type v}
    (F : TwoFunctor F₀) {X Y : Type u} (f : X → Y) (x : F₀ X) :
    ((idTwoNatTrans F).naturality f x).toEq = rfl := by
  simp [idTwoNatTrans, id2]

-- ============================================================================
-- Section 12: Monad from Adjunction
-- ============================================================================

/-- A monad structure: endofunctor T with unit η and multiplication μ. -/
structure Monad2 (T : A → A) where
  η : Cell2 (fun a => a) T
  μ : Cell2 (T ∘ T) T

/-- Theorem 42: Every adjunction gives a monad. -/
def monadFromAdj {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) : Monad2 (g ∘ f) where
  η := adj.unit
  μ := fun a => Path.congrArg g (adj.counit (f a))

/-- Theorem 43: Monad unit law (left) at toEq level. -/
theorem monad_unit_left_toEq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) (a : A) :
    (vcomp (whiskerR (monadFromAdj adj).η (g ∘ f)) (monadFromAdj adj).μ a).toEq =
    rfl := by simp [vcomp, whiskerR, monadFromAdj]

/-- Theorem 44: Monad unit law (right) at toEq level. -/
theorem monad_unit_right_toEq {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) (a : A) :
    (vcomp (whiskerL (g ∘ f) (monadFromAdj adj).η) (monadFromAdj adj).μ a).toEq =
    rfl := by simp [vcomp, whiskerL, monadFromAdj]

-- ============================================================================
-- Section 13: Coherence Results (proof irrelevance for Eq)
-- ============================================================================

-- In Lean 4, `Eq` lives in `Prop`, so any two proofs of the same `Eq` type
-- are definitionally equal. This means `(α a).toEq = (β a).toEq` is `rfl`.

/-- Theorem 45: All 2-cells between same endpoints agree at toEq. -/
theorem coherence_toEq {f g : A → B}
    (α β : Cell2 f g) (a : A) :
    (α a).toEq = (β a).toEq := rfl

/-- Theorem 46: Vertical composition coherent after toEq. -/
theorem vcomp_coherence_toEq {f g h : A → B}
    (α₁ α₂ : Cell2 f g) (β₁ β₂ : Cell2 g h) (a : A) :
    (vcomp α₁ β₁ a).toEq = (vcomp α₂ β₂ a).toEq := rfl

/-- Theorem 47: Horizontal composition coherent after toEq. -/
theorem hcomp_coherence_toEq {f g : A → B} {h k : B → C}
    (α₁ α₂ : Cell2 f g) (β₁ β₂ : Cell2 h k) (a : A) :
    (hcomp α₁ β₁ a).toEq = (hcomp α₂ β₂ a).toEq := rfl

/-- Theorem 48: Whiskering coherent after toEq. -/
theorem whiskerL_coherence_toEq (h : B → C) {f g : A → B}
    (α β : Cell2 f g) (a : A) :
    (whiskerL h α a).toEq = (whiskerL h β a).toEq := rfl

/-- Theorem 49: All diagrams of canonical 2-cells commute (coherence theorem). -/
theorem canonical_coherence {f g : A → B}
    (p q : Cell2 f g) (a : A) : (p a).toEq = (q a).toEq := rfl

/-- Theorem 50: Triangle diagram coherence. -/
theorem triangle_coherence {f : A → B} {g : B → A}
    (adj : Adjunction2 f g) (a : A) :
    (triangleL adj a).toEq = (id2 f a).toEq := rfl

-- ============================================================================
-- Section 14: More Structural Theorems
-- ============================================================================

/-- Theorem 51: Vertical composition is functorial (reversed assoc). -/
theorem vcomp_functorial {f g h k : A → B}
    (α : Cell2 f g) (β : Cell2 g h) (γ : Cell2 h k) :
    vcomp α (vcomp β γ) = vcomp (vcomp α β) γ :=
  (vcomp_assoc α β γ).symm

/-- Theorem 52: Pentagon coherence for four vertical compositions. -/
theorem pentagon_full_assoc {f g h k l : A → B}
    (α : Cell2 f g) (β : Cell2 g h) (γ : Cell2 h k) (δ : Cell2 k l) :
    vcomp (vcomp (vcomp α β) γ) δ = vcomp α (vcomp β (vcomp γ δ)) := by
  calc vcomp (vcomp (vcomp α β) γ) δ
      = vcomp (vcomp α β) (vcomp γ δ) := vcomp_assoc (vcomp α β) γ δ
    _ = vcomp α (vcomp β (vcomp γ δ)) := vcomp_assoc α β (vcomp γ δ)

/-- Theorem 53: Mac Lane coherence for four compositions (alternate route). -/
theorem mac_lane_cell2 {f g h k l : A → B}
    (α : Cell2 f g) (β : Cell2 g h) (γ : Cell2 h k) (δ : Cell2 k l) :
    vcomp (vcomp α (vcomp β γ)) δ = vcomp α (vcomp β (vcomp γ δ)) := by
  rw [vcomp_assoc α (vcomp β γ) δ]
  rw [vcomp_assoc β γ δ]

/-- Theorem 54: Universal coherence: all parallel 2-cells agree on toEq. -/
theorem universal_coherence {f g : A → B}
    (cells : List (Cell2 f g)) (a : A) :
    ∀ p ∈ cells, ∀ q ∈ cells, (p a).toEq = (q a).toEq :=
  fun _ _ _ _ => rfl

/-- Theorem 55: hcomp distributes over vinv at toEq level. -/
theorem hcomp_vinv_toEq {f g : A → B} {h k : B → C}
    (α : Cell2 f g) (β : Cell2 h k) (a : A) :
    (hcomp (vinv α) (vinv β) a).toEq =
    (vinv (hcomp' α β) a).toEq := rfl

end TwoCategPathDeep

end ComputationalPaths
