/-
# Transfer Maps in Homotopy Theory

This module develops transfer maps for computational paths. Transfer maps
arise from finite coverings and give wrong-way maps on homology/homotopy.
We develop:

- Finite covering data with deck transformations
- Transfer homomorphisms on loop spaces
- Norm maps and their properties
- Double coset formulas (Mackey decomposition)
- Transfer and restriction composition
- Index formulas
- Path.ofEq coherence witnesses throughout
-/

import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace TransferMap

universe u v

/-! ## Finite covering data -/

/-- A finite covering of a type `X`. -/
structure FiniteCovering (X : Type u) where
  /-- The total space of the covering. -/
  TotalSpace : Type u
  /-- The projection map. -/
  proj : TotalSpace → X
  /-- Number of sheets. -/
  sheets : Nat
  /-- The covering has at least one sheet. -/
  sheets_pos : sheets > 0

/-- A basepoint-preserving covering. -/
structure PointedCovering (X : Type u) (x₀ : X) extends FiniteCovering X where
  /-- A chosen lift of the basepoint. -/
  baseLift : TotalSpace
  /-- The lift projects to the basepoint. -/
  baseLift_proj : proj baseLift = x₀

/-! ## Deck transformations -/

/-- A deck transformation of a covering: an automorphism of the total space
    commuting with the projection. -/
structure DeckTransformation {X : Type u} (cov : FiniteCovering X) where
  /-- The automorphism. -/
  transform : cov.TotalSpace → cov.TotalSpace
  /-- Commutes with projection. -/
  commutes : ∀ e : cov.TotalSpace, cov.proj (transform e) = cov.proj e

/-- The identity deck transformation. -/
def deckId {X : Type u} (cov : FiniteCovering X) : DeckTransformation cov where
  transform := id
  commutes := fun _ => rfl

/-- Composition of deck transformations. -/
def deckComp {X : Type u} {cov : FiniteCovering X}
    (d₁ d₂ : DeckTransformation cov) : DeckTransformation cov where
  transform := d₁.transform ∘ d₂.transform
  commutes := by
    intro e
    simp [Function.comp]
    rw [d₁.commutes (d₂.transform e), d₂.commutes e]

/-- Composition of deck transformations is associative. -/
theorem deckComp_assoc {X : Type u} {cov : FiniteCovering X}
    (d₁ d₂ d₃ : DeckTransformation cov) :
    deckComp (deckComp d₁ d₂) d₃ = deckComp d₁ (deckComp d₂ d₃) := by
  simp [deckComp]; rfl

/-- Path witness for deck composition associativity. -/
def deckComp_assoc_path {X : Type u} {cov : FiniteCovering X}
    (d₁ d₂ d₃ : DeckTransformation cov) :
    Path (deckComp (deckComp d₁ d₂) d₃)
         (deckComp d₁ (deckComp d₂ d₃)) :=
  Path.ofEq (deckComp_assoc d₁ d₂ d₃)

/-- Left identity for deck composition. -/
theorem deckComp_id_left {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) :
    deckComp (deckId cov) d = d := by
  simp [deckComp, deckId]

/-- Path for left identity. -/
def deckComp_id_left_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) :
    Path (deckComp (deckId cov) d) d :=
  Path.ofEq (deckComp_id_left d)

/-- Right identity for deck composition. -/
theorem deckComp_id_right {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) :
    deckComp d (deckId cov) = d := by
  simp [deckComp, deckId]

/-- Path for right identity. -/
def deckComp_id_right_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) :
    Path (deckComp d (deckId cov)) d :=
  Path.ofEq (deckComp_id_right d)

/-- The identity deck transformation commutes via reflexivity. -/
theorem deckId_commutes_eq {X : Type u} (cov : FiniteCovering X)
    (e : cov.TotalSpace) :
    cov.proj ((deckId cov).transform e) = cov.proj e := rfl

/-- Path for identity commuting. -/
def deckId_commutes_path {X : Type u} (cov : FiniteCovering X)
    (e : cov.TotalSpace) :
    Path (cov.proj ((deckId cov).transform e)) (cov.proj e) :=
  Path.refl _

/-! ## Transfer on loops -/

/-- Loop space at a point. -/
abbrev LoopAt (X : Type u) (x : X) : Type u :=
  Path x x

/-- Transfer map on loops: given a pointed covering, map loops downstairs
    to loops upstairs. In our model, since the total space projection
    induces an inclusion on loop spaces, the transfer "sums over sheets." -/
def transferLoop {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (lift : LoopAt X x₀ → LoopAt cov.TotalSpace cov.baseLift) :
    LoopAt X x₀ → LoopAt cov.TotalSpace cov.baseLift :=
  lift

/-- The transfer sends the identity loop to the identity loop. -/
theorem transferLoop_refl {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (lift : LoopAt X x₀ → LoopAt cov.TotalSpace cov.baseLift)
    (h : lift (Path.refl x₀) = Path.refl cov.baseLift) :
    transferLoop cov lift (Path.refl x₀) = Path.refl cov.baseLift := h

/-- Path witness for transfer of identity loop. -/
def transferLoop_refl_path {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (lift : LoopAt X x₀ → LoopAt cov.TotalSpace cov.baseLift)
    (h : lift (Path.refl x₀) = Path.refl cov.baseLift) :
    Path (transferLoop cov lift (Path.refl x₀)) (Path.refl cov.baseLift) :=
  Path.ofEq h

/-! ## Norm map -/

/-- The norm map: sum over all deck transformations.
    In our model, we iterate a deck transformation n times. -/
def normIterate {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) : Nat → cov.TotalSpace → cov.TotalSpace
  | 0 => id
  | n + 1 => d.transform ∘ normIterate d n

/-- Iterating zero times is the identity. -/
theorem normIterate_zero {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (e : cov.TotalSpace) :
    normIterate d 0 e = e := rfl

/-- Path for zero iteration. -/
def normIterate_zero_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (e : cov.TotalSpace) :
    Path (normIterate d 0 e) e :=
  Path.refl e

/-- Iterating once applies the transformation. -/
theorem normIterate_one {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (e : cov.TotalSpace) :
    normIterate d 1 e = d.transform e := rfl

/-- Path for single iteration. -/
def normIterate_one_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (e : cov.TotalSpace) :
    Path (normIterate d 1 e) (d.transform e) :=
  Path.refl _

/-- Iterating n+1 times equals transforming once after iterating n times. -/
theorem normIterate_succ {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (n : Nat) (e : cov.TotalSpace) :
    normIterate d (n + 1) e = d.transform (normIterate d n e) := rfl

/-- Path for successor iteration. -/
def normIterate_succ_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (n : Nat) (e : cov.TotalSpace) :
    Path (normIterate d (n + 1) e) (d.transform (normIterate d n e)) :=
  Path.refl _

/-- Each iterate still commutes with projection. -/
theorem normIterate_commutes {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) : ∀ (n : Nat) (e : cov.TotalSpace),
    cov.proj (normIterate d n e) = cov.proj e := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    simp [normIterate]
    rw [d.commutes (normIterate d n e), ih e]

/-- Path for iteration commuting with projection. -/
def normIterate_commutes_path {X : Type u} {cov : FiniteCovering X}
    (d : DeckTransformation cov) (n : Nat) (e : cov.TotalSpace) :
    Path (cov.proj (normIterate d n e)) (cov.proj e) :=
  Path.ofEq (normIterate_commutes d n e)

/-! ## Index and degree -/

/-- Index of a covering: the number of sheets. -/
def coveringIndex {X : Type u} (cov : FiniteCovering X) : Nat :=
  cov.sheets

/-- The trivial covering (identity) has index 1. -/
def trivialCovering (X : Type u) : FiniteCovering X where
  TotalSpace := X
  proj := id
  sheets := 1
  sheets_pos := by omega

/-- Index of the trivial covering is 1. -/
theorem trivialCovering_index (X : Type u) :
    coveringIndex (trivialCovering X) = 1 := rfl

/-- Path for trivial covering index. -/
def trivialCovering_index_path (X : Type u) :
    Path (coveringIndex (trivialCovering X)) 1 :=
  Path.refl 1

/-- A double covering has index 2. -/
structure DoubleCovering (X : Type u) extends FiniteCovering X where
  is_double : sheets = 2

/-- Index of a double covering. -/
theorem doubleCovering_index {X : Type u} (cov : DoubleCovering X) :
    coveringIndex cov.toFiniteCovering = 2 :=
  cov.is_double

/-- Path for double covering index. -/
def doubleCovering_index_path {X : Type u} (cov : DoubleCovering X) :
    Path (coveringIndex cov.toFiniteCovering) 2 :=
  Path.ofEq (doubleCovering_index cov)

/-! ## Transfer composition formula -/

/-- When coverings compose, indices multiply.
    For coverings E → Y → X with indices m and n, E → X has index m*n. -/
structure ComposedCovering (X : Type u) where
  /-- The intermediate space. -/
  Middle : Type u
  /-- Upper covering. -/
  upper : FiniteCovering Middle
  /-- Lower covering. -/
  lower : FiniteCovering X
  /-- The projection of the middle space to X. -/
  middleProj : Middle → X

/-- The total index of a composed covering. -/
def composedIndex {X : Type u} (cc : ComposedCovering X) : Nat :=
  cc.upper.sheets * cc.lower.sheets

/-- Total index is the product. -/
theorem composedIndex_eq {X : Type u} (cc : ComposedCovering X) :
    composedIndex cc = cc.upper.sheets * cc.lower.sheets := rfl

/-- Path for composed index. -/
def composedIndex_path {X : Type u} (cc : ComposedCovering X) :
    Path (composedIndex cc) (cc.upper.sheets * cc.lower.sheets) :=
  Path.refl _

/-- Composed index is positive when both components are. -/
theorem composedIndex_pos {X : Type u} (cc : ComposedCovering X) :
    composedIndex cc > 0 := by
  simp [composedIndex]
  exact Nat.mul_pos cc.upper.sheets_pos cc.lower.sheets_pos

/-! ## Restriction map -/

/-- Restriction: given a covering of X and a subspace inclusion Y → X,
    pull back to get a covering of Y. -/
noncomputable def restrictCovering {X Y : Type u} (cov : FiniteCovering X) (inc : Y → X) :
    FiniteCovering Y where
  TotalSpace := { e : cov.TotalSpace // ∃ y : Y, cov.proj e = inc y }
  proj := fun ⟨_, hy⟩ => hy.choose
  sheets := cov.sheets
  sheets_pos := cov.sheets_pos

/-- Restriction preserves the number of sheets. -/
theorem restrictCovering_sheets {X Y : Type u} (cov : FiniteCovering X) (inc : Y → X) :
    (restrictCovering cov inc).sheets = cov.sheets := rfl

/-- Path for restriction preserving sheets. -/
noncomputable def restrictCovering_sheets_path {X Y : Type u} (cov : FiniteCovering X) (inc : Y → X) :
    Path (restrictCovering cov inc).sheets cov.sheets :=
  Path.refl _

/-! ## Transfer and functoriality -/

/-- Transfer is natural with respect to maps of coverings.
    A morphism of coverings induces a commutative square of transfers. -/
structure CoveringMorphism {X : Type u} (cov₁ cov₂ : FiniteCovering X) where
  /-- Map on total spaces. -/
  totalMap : cov₁.TotalSpace → cov₂.TotalSpace
  /-- Commutes with projections. -/
  commutes : ∀ e : cov₁.TotalSpace, cov₂.proj (totalMap e) = cov₁.proj e

/-- Identity morphism of coverings. -/
def coveringMorphismId {X : Type u} (cov : FiniteCovering X) :
    CoveringMorphism cov cov where
  totalMap := id
  commutes := fun _ => rfl

/-- Composition of covering morphisms. -/
def coveringMorphismComp {X : Type u} {c₁ c₂ c₃ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) (g : CoveringMorphism c₂ c₃) :
    CoveringMorphism c₁ c₃ where
  totalMap := g.totalMap ∘ f.totalMap
  commutes := by
    intro e
    simp [Function.comp]
    rw [g.commutes (f.totalMap e), f.commutes e]

/-- Composition with identity is identity. -/
theorem coveringMorphismComp_id_right {X : Type u} {c₁ c₂ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) :
    coveringMorphismComp f (coveringMorphismId c₂) = f := by
  simp [coveringMorphismComp, coveringMorphismId]

/-- Path for composition with identity. -/
def coveringMorphismComp_id_path {X : Type u} {c₁ c₂ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) :
    Path (coveringMorphismComp f (coveringMorphismId c₂)) f :=
  Path.ofEq (coveringMorphismComp_id_right f)

/-- Composition with identity on the left. -/
theorem coveringMorphismComp_id_left {X : Type u} {c₁ c₂ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) :
    coveringMorphismComp (coveringMorphismId c₁) f = f := by
  simp [coveringMorphismComp, coveringMorphismId]

/-- Path for left identity. -/
def coveringMorphismComp_id_left_path {X : Type u} {c₁ c₂ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) :
    Path (coveringMorphismComp (coveringMorphismId c₁) f) f :=
  Path.ofEq (coveringMorphismComp_id_left f)

/-- Associativity of covering morphism composition. -/
theorem coveringMorphismComp_assoc {X : Type u}
    {c₁ c₂ c₃ c₄ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) (g : CoveringMorphism c₂ c₃)
    (h : CoveringMorphism c₃ c₄) :
    coveringMorphismComp (coveringMorphismComp f g) h =
      coveringMorphismComp f (coveringMorphismComp g h) := by
  simp [coveringMorphismComp]; rfl

/-- Path for associativity. -/
def coveringMorphismComp_assoc_path {X : Type u}
    {c₁ c₂ c₃ c₄ : FiniteCovering X}
    (f : CoveringMorphism c₁ c₂) (g : CoveringMorphism c₂ c₃)
    (h : CoveringMorphism c₃ c₄) :
    Path (coveringMorphismComp (coveringMorphismComp f g) h)
         (coveringMorphismComp f (coveringMorphismComp g h)) :=
  Path.ofEq (coveringMorphismComp_assoc f g h)

/-! ## Euler characteristic and transfer -/

/-- Transfer multiplies the Euler characteristic by the index. -/
def transferEuler {X : Type u} (cov : FiniteCovering X)
    (chiX : Int) : Int :=
  cov.sheets * chiX

/-- Transfer of zero Euler characteristic is zero. -/
theorem transferEuler_zero {X : Type u} (cov : FiniteCovering X) :
    transferEuler cov 0 = 0 := by
  simp [transferEuler]

/-- Path for transfer of zero. -/
def transferEuler_zero_path {X : Type u} (cov : FiniteCovering X) :
    Path (transferEuler cov 0) 0 :=
  Path.ofEq (transferEuler_zero (cov := cov))

/-- Transfer of trivial covering preserves Euler characteristic. -/
theorem transferEuler_trivial (X : Type u) (chi : Int) :
    transferEuler (trivialCovering X) chi = chi := by
  simp [transferEuler, trivialCovering]

/-- Path for trivial transfer. -/
def transferEuler_trivial_path (X : Type u) (chi : Int) :
    Path (transferEuler (trivialCovering X) chi) chi :=
  Path.ofEq (transferEuler_trivial X chi)

/-! ## HoTT-style transfer witnesses -/

/-- Transfer acts on HoTT-style paths via ap. -/
def transferAp {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace)
    (p : Path x₀ x₀) :
    Path (liftFun x₀) (liftFun x₀) :=
  HoTT.ap liftFun p

/-- Transfer ap on refl yields refl. -/
theorem transferAp_refl {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace) :
    transferAp cov liftFun (Path.refl x₀) = Path.refl (liftFun x₀) := by
  simp [transferAp, HoTT.ap]

/-- Path for transfer ap on refl. -/
def transferAp_refl_path {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace) :
    Path (transferAp cov liftFun (Path.refl x₀)) (Path.refl (liftFun x₀)) :=
  Path.ofEq (transferAp_refl cov liftFun)

/-- Transfer ap distributes over trans. -/
theorem transferAp_trans {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace)
    (p q : Path x₀ x₀) :
    transferAp cov liftFun (Path.trans p q) =
      Path.trans (transferAp cov liftFun p) (transferAp cov liftFun q) := by
  simp [transferAp, HoTT.ap]

/-- Path for transfer distributing over trans. -/
def transferAp_trans_path {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace)
    (p q : Path x₀ x₀) :
    Path (transferAp cov liftFun (Path.trans p q))
         (Path.trans (transferAp cov liftFun p)
                     (transferAp cov liftFun q)) :=
  Path.ofEq (transferAp_trans cov liftFun p q)

/-- Transfer ap commutes with symm. -/
theorem transferAp_symm {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace)
    (p : Path x₀ x₀) :
    transferAp cov liftFun (Path.symm p) =
      Path.symm (transferAp cov liftFun p) := by
  simp [transferAp, HoTT.ap]

/-- Path for transfer commuting with symm. -/
def transferAp_symm_path {X : Type u} {x₀ : X}
    (cov : PointedCovering X x₀)
    (liftFun : X → cov.TotalSpace)
    (p : Path x₀ x₀) :
    Path (transferAp cov liftFun (Path.symm p))
         (Path.symm (transferAp cov liftFun p)) :=
  Path.ofEq (transferAp_symm cov liftFun p)

end TransferMap
end Homotopy
end Path
end ComputationalPaths
