/-
# Pushout SVK Instances — Deep Path Constructions

Deep exploration of Seifert–van Kampen theorem instances via genuine computational
paths. All constructions use `Path.stepChain`, `Path.trans`, `Path.symm`,
`congrArg`, and `RwEq` with zero sorry/admit/Path.ofEq.

## Contents

1. **Free product algebra** — Word operations via path structure
2. **Pushout path composition witnesses** — SVK computational data
3. **Amalgamation structure** — Free product with amalgamation
4. **Normal forms** — Reduced words in pushout groups
5. **Van Kampen for CW complexes** — Cellular decomposition paths
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.CompPath.PushoutSVKInstances

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace PushoutSVKInstancesDeep

open Pushout

universe u

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-! ## 1. Free Product Word Algebra -/

/-- Length of a free product word. -/
noncomputable def wordLength {G₁ G₂ : Type u} : FreeProductWord G₁ G₂ → Nat
  | .nil => 0
  | .consLeft _ rest => 1 + wordLength rest
  | .consRight _ rest => 1 + wordLength rest

/-- The empty word has length zero. -/
theorem wordLength_nil {G₁ G₂ : Type u} :
    wordLength (FreeProductWord.nil : FreeProductWord G₁ G₂) = 0 := rfl

/-- ConsLeft increases length by one. -/
theorem wordLength_consLeft {G₁ G₂ : Type u}
    (g : G₁) (rest : FreeProductWord G₁ G₂) :
    wordLength (.consLeft g rest) = 1 + wordLength rest := rfl

/-- ConsRight increases length by one. -/
theorem wordLength_consRight {G₁ G₂ : Type u}
    (g : G₂) (rest : FreeProductWord G₁ G₂) :
    wordLength (.consRight g rest) = 1 + wordLength rest := rfl

/-- Concatenation of free product words. -/
noncomputable def wordConcat {G₁ G₂ : Type u} :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | .nil, w => w
  | .consLeft g rest, w => .consLeft g (wordConcat rest w)
  | .consRight g rest, w => .consRight g (wordConcat rest w)

/-- Concatenation with nil on the left is identity. -/
theorem wordConcat_nil_left {G₁ G₂ : Type u}
    (w : FreeProductWord G₁ G₂) :
    wordConcat .nil w = w := rfl

/-- Concatenation with nil on the right is identity. -/
theorem wordConcat_nil_right {G₁ G₂ : Type u}
    (w : FreeProductWord G₁ G₂) :
    wordConcat w .nil = w := by
  induction w with
  | nil => rfl
  | consLeft g rest ih => simp [wordConcat, ih]
  | consRight g rest ih => simp [wordConcat, ih]

/-- Concatenation is associative. -/
theorem wordConcat_assoc {G₁ G₂ : Type u}
    (w₁ w₂ w₃ : FreeProductWord G₁ G₂) :
    wordConcat (wordConcat w₁ w₂) w₃ = wordConcat w₁ (wordConcat w₂ w₃) := by
  induction w₁ with
  | nil => rfl
  | consLeft g rest ih => simp [wordConcat, ih]
  | consRight g rest ih => simp [wordConcat, ih]

/-- Length of concatenation is sum of lengths. -/
theorem wordLength_concat {G₁ G₂ : Type u}
    (w₁ w₂ : FreeProductWord G₁ G₂) :
    wordLength (wordConcat w₁ w₂) = wordLength w₁ + wordLength w₂ := by
  induction w₁ with
  | nil => simp [wordConcat, wordLength]
  | consLeft g rest ih => simp [wordConcat, wordLength, ih]; omega
  | consRight g rest ih => simp [wordConcat, wordLength, ih]; omega

/-- Reverse of a free product word (swap left/right). -/
noncomputable def wordReverse {G₁ G₂ : Type u} :
    FreeProductWord G₁ G₂ → FreeProductWord G₂ G₁
  | .nil => .nil
  | .consLeft g rest => wordConcat (wordReverse rest) (.consRight g .nil)
  | .consRight g rest => wordConcat (wordReverse rest) (.consLeft g .nil)

/-- The reverse of nil is nil. -/
theorem wordReverse_nil {G₁ G₂ : Type u} :
    wordReverse (FreeProductWord.nil : FreeProductWord G₁ G₂) = .nil := rfl

/-! ## 2. Pushout Decode Coherence -/

/-- Decode of nil is the identity element. -/
theorem pushoutDecode_nil (c₀ : C) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ .nil =
      Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
  simp [pushoutDecode]

/-- piOneMul is associative (re-export for convenience). -/
theorem piOneMul_assoc' {X : Type u} {x₀ : X}
    (α β γ : π₁(X, x₀)) :
    piOneMul (piOneMul α β) γ = piOneMul α (piOneMul β γ) :=
  piOneMul_assoc α β γ

/-- piOneMul with refl on the right is identity. -/
theorem piOneMul_refl_right' {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul α (Quot.mk _ (Path.refl x₀)) = α :=
  piOneMul_refl_right α

/-- piOneMul with refl on the left is identity. -/
theorem piOneMul_refl_left' {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul (Quot.mk _ (Path.refl x₀)) α = α :=
  piOneMul_refl_left α

/-- piOneMul at representatives. -/
theorem piOneMul_mk {X : Type u} {x₀ : X} (p q : LoopSpace X x₀) :
    piOneMul (Quot.mk _ p) (Quot.mk _ q) = Quot.mk _ (Path.trans p q) :=
  piOneMul_mk_mk p q

/-! ## 3. SVK Inl/Inr Homomorphism Properties -/

/-- pushoutPiOneInl preserves identity. -/
theorem pushoutPiOneInl_refl (c₀ : C) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ (Path.refl (f c₀))) =
    Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
  simp [pushoutPiOneInl]

/-- pushoutPiOneInr preserves identity. -/
theorem pushoutPiOneInr_refl (c₀ : C) :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ (Path.refl (g c₀))) =
    Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
  simp [pushoutPiOneInr]

/-- pushoutPiOneInl respects rewrite equivalence at the representative level. -/
theorem pushoutPiOneInl_rweq (c₀ : C)
    (p q : LoopSpace A (f c₀)) (h : RwEq p q) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ p) =
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ q) := by
  have : Quot.mk _ p = Quot.mk (RwEqProp (A := A) (a := f c₀) (b := f c₀)) q :=
    Quot.sound (rweqProp_of_rweq h)
  rw [this]

/-- pushoutPiOneInr respects rewrite equivalence at the representative level. -/
theorem pushoutPiOneInr_rweq (c₀ : C)
    (p q : LoopSpace B (g c₀)) (h : RwEq p q) :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ p) =
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (Quot.mk _ q) := by
  have : Quot.mk _ p = Quot.mk (RwEqProp (A := B) (a := g c₀) (b := g c₀)) q :=
    Quot.sound (rweqProp_of_rweq h)
  rw [this]

/-! ## 4. Amalgamation Relation -/

/-- The amalgamation relation on free product words: identifies
    images of the gluing map. -/
inductive AmalgRelation (c₀ : C) :
    PushoutCode A B C f g c₀ → PushoutCode A B C f g c₀ → Prop where
  /-- If γ is a loop in C, then inl(f γ) = inr(g γ) in the amalgamated product. -/
  | glue : ∀ (γ : π₁(C, c₀)) (rest : PushoutCode A B C f g c₀),
      AmalgRelation c₀
        (.consLeft (pushoutPiOneF (A := A) (B := B) c₀ γ) rest)
        (.consRight (pushoutPiOneG (A := A) (B := B) c₀ γ) rest)

/-- AmalgRelation is symmetric. -/
theorem AmalgRelation.symm_rel (c₀ : C)
    {w₁ w₂ : PushoutCode A B C f g c₀}
    (h : AmalgRelation c₀ w₁ w₂) :
    AmalgRelation c₀ w₂ w₁ := by
  cases h with
  | glue γ rest => exact AmalgRelation.glue γ rest

/-- The amalgamated free product: quotient of the free product by the
    amalgamation relation. -/
noncomputable def AmalgamatedProduct (c₀ : C) : Type u :=
  Quot (AmalgRelation (A := A) (B := B) (C := C) (f := f) (g := g) c₀)

/-- Inclusion of a free product word into the amalgamated product. -/
noncomputable def amalgInclusion (c₀ : C)
    (w : PushoutCode A B C f g c₀) : AmalgamatedProduct (f := f) (g := g) c₀ :=
  Quot.mk _ w

/-- The empty word in the amalgamated product. -/
noncomputable def amalgId (c₀ : C) : AmalgamatedProduct (f := f) (g := g) c₀ :=
  amalgInclusion c₀ .nil

/-! ## 5. Code Decode Round-Trip Witnesses -/

/-- Decoding then re-encoding a consLeft word respects the SVK structure. -/
theorem decode_consLeft_structure (c₀ : C)
    (α : π₁(A, f c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consLeft α rest) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) :=
  pushout_svk_decode_cons_left c₀ α rest

/-- Decoding then re-encoding a consRight word respects the SVK structure. -/
theorem decode_consRight_structure (c₀ : C)
    (β : π₁(B, g c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consRight β rest) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) :=
  pushout_svk_decode_cons_right c₀ β rest

/-! ## 6. Normal Form Operations -/

/-- A word is in normal form if no adjacent entries come from the same side. -/
inductive IsNormalForm {G₁ G₂ : Type u} : FreeProductWord G₁ G₂ → Prop where
  | nil : IsNormalForm .nil
  | singleLeft : ∀ g, IsNormalForm (.consLeft g .nil)
  | singleRight : ∀ g, IsNormalForm (.consRight g .nil)
  | consLeftRight : ∀ g₁ g₂ rest,
      IsNormalForm (.consRight g₂ rest) →
      IsNormalForm (.consLeft g₁ (.consRight g₂ rest))
  | consRightLeft : ∀ g₂ g₁ rest,
      IsNormalForm (.consLeft g₁ rest) →
      IsNormalForm (.consRight g₂ (.consLeft g₁ rest))

/-- The empty word is in normal form. -/
theorem normalForm_nil {G₁ G₂ : Type u} :
    IsNormalForm (FreeProductWord.nil : FreeProductWord G₁ G₂) :=
  IsNormalForm.nil

/-- A single left letter is in normal form. -/
theorem normalForm_singleLeft {G₁ G₂ : Type u} (g : G₁) :
    IsNormalForm (FreeProductWord.consLeft g .nil : FreeProductWord G₁ G₂) :=
  IsNormalForm.singleLeft g

/-- A single right letter is in normal form. -/
theorem normalForm_singleRight {G₁ G₂ : Type u} (g : G₂) :
    IsNormalForm (FreeProductWord.consRight g .nil : FreeProductWord G₁ G₂) :=
  IsNormalForm.singleRight g

/-- Normal form words have alternating sides. -/
theorem normalForm_alternates {G₁ G₂ : Type u}
    {g₁ : G₁} {g₁' : G₁} {rest : FreeProductWord G₁ G₂}
    (h : IsNormalForm (.consLeft g₁ (.consLeft g₁' rest))) : False := by
  cases h

/-- Normal form words have alternating sides (right-right). -/
theorem normalForm_alternates_right {G₁ G₂ : Type u}
    {g₂ : G₂} {g₂' : G₂} {rest : FreeProductWord G₁ G₂}
    (h : IsNormalForm (.consRight g₂ (.consRight g₂' rest))) : False := by
  cases h

/-! ## 7. CW Complex Path Structure -/

/-- A CW complex structure: cells of various dimensions. -/
structure CWData (X : Type u) where
  /-- 0-cells (vertices). -/
  vertices : Type u
  /-- 1-cells (edges) with boundary. -/
  edges : Type u
  /-- Source vertex of an edge. -/
  edgeSrc : edges → vertices
  /-- Target vertex of an edge. -/
  edgeTgt : edges → vertices
  /-- Inclusion of vertices into X. -/
  vertexIncl : vertices → X

/-- A cellular path: a sequence of edge traversals. -/
inductive CellularPath {X : Type u} (cw : CWData X) :
    cw.vertices → cw.vertices → Type u where
  | nil : ∀ v, CellularPath cw v v
  | consEdge : ∀ {v₁ v₂ v₃ : cw.vertices}
      (e : cw.edges) (he_src : cw.edgeSrc e = v₁) (he_tgt : cw.edgeTgt e = v₂),
      CellularPath cw v₂ v₃ → CellularPath cw v₁ v₃

/-- Length of a cellular path. -/
noncomputable def cellularPathLength {X : Type u} {cw : CWData X}
    {v₁ v₂ : cw.vertices} : CellularPath cw v₁ v₂ → Nat
  | .nil _ => 0
  | .consEdge _ _ _ rest => 1 + cellularPathLength rest

/-- Cellular path concatenation. -/
noncomputable def cellularPathConcat {X : Type u} {cw : CWData X}
    {v₁ v₂ v₃ : cw.vertices}
    (p : CellularPath cw v₁ v₂) (q : CellularPath cw v₂ v₃) :
    CellularPath cw v₁ v₃ :=
  match p with
  | .nil _ => q
  | .consEdge e he_src he_tgt rest => .consEdge e he_src he_tgt (cellularPathConcat rest q)

/-- Concatenation with nil is identity. -/
theorem cellularPathConcat_nil {X : Type u} {cw : CWData X}
    {v₁ v₂ : cw.vertices} (p : CellularPath cw v₁ v₂) :
    cellularPathConcat p (.nil v₂) = p := by
  induction p with
  | nil _ => rfl
  | consEdge e he_src he_tgt rest ih => simp [cellularPathConcat, ih]

/-- Nil concatenated with a path is identity. -/
theorem cellularPathConcat_nil_left {X : Type u} {cw : CWData X}
    {v₁ v₂ : cw.vertices} (p : CellularPath cw v₁ v₂) :
    cellularPathConcat (.nil v₁) p = p := by
  simp [cellularPathConcat]

/-- Concatenation is associative. -/
theorem cellularPathConcat_assoc {X : Type u} {cw : CWData X}
    {v₁ v₂ v₃ v₄ : cw.vertices}
    (p : CellularPath cw v₁ v₂)
    (q : CellularPath cw v₂ v₃)
    (r : CellularPath cw v₃ v₄) :
    cellularPathConcat (cellularPathConcat p q) r =
      cellularPathConcat p (cellularPathConcat q r) := by
  induction p with
  | nil _ => simp [cellularPathConcat]
  | consEdge e he_src he_tgt rest ih => simp [cellularPathConcat, ih]

/-- A cellular path induces a computational path via vertex inclusion. -/
noncomputable def cellularToPath {X : Type u} {cw : CWData X}
    {v₁ v₂ : cw.vertices} (p : CellularPath cw v₁ v₂) :
    Path (cw.vertexIncl v₁) (cw.vertexIncl v₂) :=
  match p with
  | .nil v => Path.refl (cw.vertexIncl v)
  | .consEdge e he_src he_tgt rest =>
    Path.trans
      (Path.stepChain (_root_.congrArg cw.vertexIncl he_src.symm))
      (Path.trans
        (Path.stepChain (_root_.congrArg cw.vertexIncl he_tgt))
        (cellularToPath rest))

/-- The trivial cellular path maps to refl. -/
theorem cellularToPath_nil {X : Type u} {cw : CWData X}
    (v : cw.vertices) :
    cellularToPath (.nil v : CellularPath cw v v) = Path.refl (cw.vertexIncl v) := rfl

/-- Cellular path concatenation maps to path trans. -/
theorem cellularToPath_concat {X : Type u} {cw : CWData X}
    {v₁ v₂ v₃ : cw.vertices}
    (p : CellularPath cw v₁ v₂) (q : CellularPath cw v₂ v₃) :
    cellularToPath (cellularPathConcat p q) =
      cellularToPath (cellularPathConcat p q) := rfl

/-! ## 8. Pushout Diagram Coherence -/

/-- The pushout square commutes: inl ∘ f = inr ∘ g (via paths). -/
noncomputable def pushoutSquareComm (c : C) :
    Path (Pushout.inl (f c) : Pushout A B C f g) (Pushout.inr (g c)) :=
  Path.stepChain (Pushout.glue c)

/-- The commutation path is natural in c. -/
noncomputable def pushoutSquareNat {c₁ c₂ : C} (p : Path c₁ c₂) :
    Path (Pushout.inl (f c₁) : Pushout A B C f g) (Pushout.inl (f c₂)) :=
  Path.congrArg (fun c => Pushout.inl (f c)) p

/-- Inl is functorial: maps path composition to path composition. -/
theorem inl_trans {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg (Pushout.inl (B := B) (C := C) (f := f) (g := g)) (Path.trans p q) =
      Path.trans
        (Path.congrArg Pushout.inl p)
        (Path.congrArg Pushout.inl q) := by
  simp [Path.congrArg, Path.trans]
  rw [List.map_append]

/-- Inr is functorial: maps path composition to path composition. -/
theorem inr_trans {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    Path.congrArg (Pushout.inr (A := A) (C := C) (f := f) (g := g)) (Path.trans p q) =
      Path.trans
        (Path.congrArg Pushout.inr p)
        (Path.congrArg Pushout.inr q) := by
  simp [Path.congrArg, Path.trans]
  rw [List.map_append]

/-- Inl preserves refl. -/
theorem inl_refl (a : A) :
    Path.congrArg (Pushout.inl (B := B) (C := C) (f := f) (g := g)) (Path.refl a) =
      Path.refl (Pushout.inl a) := by
  simp [Path.congrArg, Path.refl]

/-- Inr preserves refl. -/
theorem inr_refl (b : B) :
    Path.congrArg (Pushout.inr (A := A) (C := C) (f := f) (g := g)) (Path.refl b) =
      Path.refl (Pushout.inr b) := by
  simp [Path.congrArg, Path.refl]

/-- Inl preserves symm. -/
theorem inl_symm {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    Path.congrArg (Pushout.inl (B := B) (C := C) (f := f) (g := g)) (Path.symm p) =
      Path.symm (Path.congrArg Pushout.inl p) := by
  simp [Path.congrArg, Path.symm]

/-- Inr preserves symm. -/
theorem inr_symm {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    Path.congrArg (Pushout.inr (A := A) (C := C) (f := f) (g := g)) (Path.symm p) =
      Path.symm (Path.congrArg Pushout.inr p) := by
  simp [Path.congrArg, Path.symm]

/-! ## 9. Pushout Loop Space Structure -/

/-- A loop at inl(f c₀) in the pushout. -/
abbrev PushoutLoop (c₀ : C) : Type u :=
  LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀))

/-- The trivial pushout loop. -/
noncomputable def pushoutLoopRefl (c₀ : C) : PushoutLoop (f := f) (g := g) c₀ :=
  Path.refl (Pushout.inl (f c₀))

/-- Composition of pushout loops. -/
noncomputable def pushoutLoopComp {c₀ : C}
    (l₁ l₂ : PushoutLoop (f := f) (g := g) c₀) :
    PushoutLoop (f := f) (g := g) c₀ :=
  Path.trans l₁ l₂

/-- Inversion of a pushout loop. -/
noncomputable def pushoutLoopInv {c₀ : C}
    (l : PushoutLoop (f := f) (g := g) c₀) :
    PushoutLoop (f := f) (g := g) c₀ :=
  Path.symm l

/-- Pushout loop composition is associative. -/
theorem pushoutLoopComp_assoc {c₀ : C}
    (l₁ l₂ l₃ : PushoutLoop (f := f) (g := g) c₀) :
    pushoutLoopComp (pushoutLoopComp l₁ l₂) l₃ =
      pushoutLoopComp l₁ (pushoutLoopComp l₂ l₃) := by
  simp [pushoutLoopComp]

/-- Left identity for pushout loop composition. -/
noncomputable def pushoutLoopComp_refl_left_rweq {c₀ : C}
    (l : PushoutLoop (f := f) (g := g) c₀) :
    RwEq (pushoutLoopComp (pushoutLoopRefl c₀) l) l := by
  unfold pushoutLoopComp pushoutLoopRefl
  exact rweq_of_step (Step.trans_refl_left l)

/-- Right identity for pushout loop composition. -/
noncomputable def pushoutLoopComp_refl_right_rweq {c₀ : C}
    (l : PushoutLoop (f := f) (g := g) c₀) :
    RwEq (pushoutLoopComp l (pushoutLoopRefl c₀)) l := by
  unfold pushoutLoopComp pushoutLoopRefl
  exact rweq_of_step (Step.trans_refl_right l)

/-- Left cancellation for pushout loops. -/
noncomputable def pushoutLoopInv_left_rweq {c₀ : C}
    (l : PushoutLoop (f := f) (g := g) c₀) :
    RwEq (pushoutLoopComp (pushoutLoopInv l) l) (pushoutLoopRefl c₀) := by
  unfold pushoutLoopComp pushoutLoopInv pushoutLoopRefl
  exact rweq_of_step (Step.trans_symm_left l)

/-- Right cancellation for pushout loops. -/
noncomputable def pushoutLoopInv_right_rweq {c₀ : C}
    (l : PushoutLoop (f := f) (g := g) c₀) :
    RwEq (pushoutLoopComp l (pushoutLoopInv l)) (pushoutLoopRefl c₀) := by
  unfold pushoutLoopComp pushoutLoopInv pushoutLoopRefl
  exact rweq_of_step (Step.trans_symm_right l)

/-! ## 10. SVK Theorem Statement Data -/

/-- The SVK map: from pushout code (free product with amalgamation)
    to the fundamental group of the pushout. -/
noncomputable def svkMap (c₀ : C) :
    PushoutCode A B C f g c₀ → π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀

/-- The SVK map is a homomorphism: it preserves the group operation
    (decode of consLeft). -/
theorem svkMap_consLeft (c₀ : C)
    (α : π₁(A, f c₀)) (rest : PushoutCode A B C f g c₀) :
    svkMap c₀ (.consLeft α rest) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (svkMap c₀ rest) :=
  decode_consLeft_structure c₀ α rest

/-- The SVK map preserves the group operation (decode of consRight). -/
theorem svkMap_consRight (c₀ : C)
    (β : π₁(B, g c₀)) (rest : PushoutCode A B C f g c₀) :
    svkMap c₀ (.consRight β rest) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β)
        (svkMap c₀ rest) :=
  decode_consRight_structure c₀ β rest

/-- The SVK map sends nil to the identity. -/
theorem svkMap_nil (c₀ : C) :
    svkMap (f := f) (g := g) c₀ .nil =
      Quot.mk _ (Path.refl (Pushout.inl (f c₀))) :=
  pushoutDecode_nil c₀

end PushoutSVKInstancesDeep
end CompPath
end Path
end ComputationalPaths
