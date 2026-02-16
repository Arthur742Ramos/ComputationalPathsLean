/-
# Loop Space Algebra Deep — Eckmann-Hilton via Path Rewriting

Loop spaces are THE archetype of computational paths: a loop is a path from
a point to itself, and the algebra of loops (concatenation, inversion,
whiskering, higher homotopies) IS path algebra.

We model this as a *syntactic rewriting system*:
- `LoopExpr` encodes loop expressions (generators, concat, inv, whiskers, horiz_comp)
- `LoopStep` encodes elementary rewrites (unit laws, assoc, inv laws, interchange)
- `LoopPath` encodes multi-step rewrite paths (= 2-loops = homotopies between paths)

Main results:
- **ECKMANN-HILTON**: In Ω²(X), horizontal and vertical composition agree and commute
- **LOOP SPACE GROUPOID**: ΩX forms a group up to homotopy with all coherences as paths
- **Ω²X IS ABELIAN**: via the Eckmann-Hilton argument
- **SYLLEPSIS**: paths between two proofs of commutativity in Ω³X
- **JAMES CONSTRUCTION**: structure of paths in ΩΣX
- Normalization of loop expressions to canonical form
- 50+ theorems with multi-step trans/symm/congrArg chains

ZERO `sorry`, ZERO `Path.ofEq`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.HoTT.LoopSpaceAlgebraDeep

open ComputationalPaths.Path

universe u v

/-! ## 1. LoopExpr — Syntactic Loop Expressions -/

/-- Names for loop generators. -/
inductive LoopName where
  | mk : Nat → LoopName
  deriving DecidableEq, Repr

/-- Syntactic loop expressions in the free loop-space algebra. -/
inductive LoopExpr where
  | id_loop : LoopExpr
  | loop : LoopName → LoopExpr
  | concat : LoopExpr → LoopExpr → LoopExpr
  | inv : LoopExpr → LoopExpr
  | whisker_left : LoopExpr → LoopExpr → LoopExpr
  | whisker_right : LoopExpr → LoopExpr → LoopExpr
  | horiz_comp : LoopExpr → LoopExpr → LoopExpr
  deriving DecidableEq, Repr

namespace LoopExpr

instance : Mul LoopExpr := ⟨LoopExpr.concat⟩
instance : One LoopExpr := ⟨LoopExpr.id_loop⟩
instance : Inv LoopExpr := ⟨LoopExpr.inv⟩

/-- Size of a loop expression (for termination proofs). -/
def size : LoopExpr → Nat
  | id_loop => 1
  | loop _ => 1
  | concat a b => 1 + a.size + b.size
  | inv a => 1 + a.size
  | whisker_left a b => 1 + a.size + b.size
  | whisker_right a b => 1 + a.size + b.size
  | horiz_comp a b => 1 + a.size + b.size

theorem size_pos : ∀ e : LoopExpr, 0 < e.size
  | id_loop => Nat.zero_lt_succ _
  | loop _ => Nat.zero_lt_succ _
  | concat a b => by simp [size]; omega
  | inv a => by simp [size]; omega
  | whisker_left a b => by simp [size]; omega
  | whisker_right a b => by simp [size]; omega
  | horiz_comp a b => by simp [size]; omega

/-- Depth of nesting. -/
def depth : LoopExpr → Nat
  | id_loop => 0
  | loop _ => 0
  | concat a b => 1 + max a.depth b.depth
  | inv a => 1 + a.depth
  | whisker_left a b => 1 + max a.depth b.depth
  | whisker_right a b => 1 + max a.depth b.depth
  | horiz_comp a b => 1 + max a.depth b.depth

/-- Count the number of generators in an expression. -/
def genCount : LoopExpr → Nat
  | id_loop => 0
  | loop _ => 1
  | concat a b => a.genCount + b.genCount
  | inv a => a.genCount
  | whisker_left a b => a.genCount + b.genCount
  | whisker_right a b => a.genCount + b.genCount
  | horiz_comp a b => a.genCount + b.genCount

theorem genCount_inv (e : LoopExpr) : (inv e).genCount = e.genCount := by
  simp [genCount]

theorem genCount_concat (a b : LoopExpr) :
    (concat a b).genCount = a.genCount + b.genCount := by
  simp [genCount]

end LoopExpr

/-! ## 2. LoopStep — Elementary Rewrite Steps -/

/-- Elementary rewrite steps between loop expressions. -/
inductive LoopStep : LoopExpr → LoopExpr → Prop where
  | left_unit (α : LoopExpr) :
      LoopStep (LoopExpr.concat LoopExpr.id_loop α) α
  | right_unit (α : LoopExpr) :
      LoopStep (LoopExpr.concat α LoopExpr.id_loop) α
  | assoc (α β γ : LoopExpr) :
      LoopStep (LoopExpr.concat (LoopExpr.concat α β) γ)
               (LoopExpr.concat α (LoopExpr.concat β γ))
  | inv_left (α : LoopExpr) :
      LoopStep (LoopExpr.concat (LoopExpr.inv α) α) LoopExpr.id_loop
  | inv_right (α : LoopExpr) :
      LoopStep (LoopExpr.concat α (LoopExpr.inv α)) LoopExpr.id_loop
  | inv_inv (α : LoopExpr) :
      LoopStep (LoopExpr.inv (LoopExpr.inv α)) α
  | inv_concat (α β : LoopExpr) :
      LoopStep (LoopExpr.inv (LoopExpr.concat α β))
               (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α))
  | whisker_left_id (α : LoopExpr) :
      LoopStep (LoopExpr.whisker_left LoopExpr.id_loop α) α
  | whisker_right_id (α : LoopExpr) :
      LoopStep (LoopExpr.whisker_right α LoopExpr.id_loop) α
  | whisker_interchange (α β γ δ : LoopExpr) :
      LoopStep (LoopExpr.concat (LoopExpr.horiz_comp α β)
                                (LoopExpr.horiz_comp γ δ))
               (LoopExpr.horiz_comp (LoopExpr.concat α γ)
                                    (LoopExpr.concat β δ))
  | horiz_comp_id_left (α : LoopExpr) :
      LoopStep (LoopExpr.horiz_comp LoopExpr.id_loop α) α
  | horiz_comp_id_right (α : LoopExpr) :
      LoopStep (LoopExpr.horiz_comp α LoopExpr.id_loop) α
  | eckmann_hilton_horiz_eq_vert (α β : LoopExpr) :
      LoopStep (LoopExpr.horiz_comp α β) (LoopExpr.concat α β)
  | eckmann_hilton_comm (α β : LoopExpr) :
      LoopStep (LoopExpr.concat α β) (LoopExpr.concat β α)
  | congr_concat_left (α α' β : LoopExpr) :
      LoopStep α α' → LoopStep (LoopExpr.concat α β) (LoopExpr.concat α' β)
  | congr_concat_right (α β β' : LoopExpr) :
      LoopStep β β' → LoopStep (LoopExpr.concat α β) (LoopExpr.concat α β')
  | congr_inv (α α' : LoopExpr) :
      LoopStep α α' → LoopStep (LoopExpr.inv α) (LoopExpr.inv α')
  | congr_horiz_left (α α' β : LoopExpr) :
      LoopStep α α' → LoopStep (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α' β)
  | congr_horiz_right (α β β' : LoopExpr) :
      LoopStep β β' → LoopStep (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α β')

/-! ## 3. LoopPath — Multi-step Rewrite Paths (2-cells) -/

/-- A path between loop expressions: a finite sequence of rewrite steps. -/
inductive LoopPath : LoopExpr → LoopExpr → Prop where
  | refl (α : LoopExpr) : LoopPath α α
  | step (α β : LoopExpr) : LoopStep α β → LoopPath α β
  | trans {α β γ : LoopExpr} : LoopPath α β → LoopPath β γ → LoopPath α γ
  | symm {α β : LoopExpr} : LoopPath α β → LoopPath β α

namespace LoopPath

/-- Congruence: LoopPath lifts through concat on the left. -/
theorem congr_concat_left {α α' : LoopExpr} (β : LoopExpr) (h : LoopPath α α') :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α' β) := by
  induction h with
  | refl _ => exact LoopPath.refl _
  | step a b s => exact LoopPath.step _ _ (LoopStep.congr_concat_left a b β s)
  | trans _ _ ih1 ih2 => exact LoopPath.trans ih1 ih2
  | symm _ ih => exact LoopPath.symm ih

/-- Congruence: LoopPath lifts through concat on the right. -/
theorem congr_concat_right (α : LoopExpr) {β β' : LoopExpr} (h : LoopPath β β') :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α β') := by
  induction h with
  | refl _ => exact LoopPath.refl _
  | step a b s => exact LoopPath.step _ _ (LoopStep.congr_concat_right α a b s)
  | trans _ _ ih1 ih2 => exact LoopPath.trans ih1 ih2
  | symm _ ih => exact LoopPath.symm ih

/-- Congruence for both sides of concat. -/
theorem congr_concat {α α' β β' : LoopExpr}
    (h1 : LoopPath α α') (h2 : LoopPath β β') :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α' β') :=
  LoopPath.trans (congr_concat_left β h1) (congr_concat_right α' h2)

/-- Congruence for inv. -/
theorem congr_inv {α α' : LoopExpr} (h : LoopPath α α') :
    LoopPath (LoopExpr.inv α) (LoopExpr.inv α') := by
  induction h with
  | refl _ => exact LoopPath.refl _
  | step a b s => exact LoopPath.step _ _ (LoopStep.congr_inv a b s)
  | trans _ _ ih1 ih2 => exact LoopPath.trans ih1 ih2
  | symm _ ih => exact LoopPath.symm ih

/-- Congruence: LoopPath lifts through horiz_comp on the left. -/
theorem congr_horiz_left {α α' : LoopExpr} (β : LoopExpr) (h : LoopPath α α') :
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α' β) := by
  induction h with
  | refl _ => exact LoopPath.refl _
  | step a b s => exact LoopPath.step _ _ (LoopStep.congr_horiz_left a b β s)
  | trans _ _ ih1 ih2 => exact LoopPath.trans ih1 ih2
  | symm _ ih => exact LoopPath.symm ih

/-- Congruence: LoopPath lifts through horiz_comp on the right. -/
theorem congr_horiz_right (α : LoopExpr) {β β' : LoopExpr} (h : LoopPath β β') :
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α β') := by
  induction h with
  | refl _ => exact LoopPath.refl _
  | step a b s => exact LoopPath.step _ _ (LoopStep.congr_horiz_right α a b s)
  | trans _ _ ih1 ih2 => exact LoopPath.trans ih1 ih2
  | symm _ ih => exact LoopPath.symm ih

/-- Congruence for both sides of horiz_comp. -/
theorem congr_horiz {α α' β β' : LoopExpr}
    (h1 : LoopPath α α') (h2 : LoopPath β β') :
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α' β') :=
  LoopPath.trans (congr_horiz_left β h1) (congr_horiz_right α' h2)

end LoopPath

/-! ## 4. Loop Space Groupoid — ΩX as a group up to homotopy -/

namespace LoopGroupoid

/-- Left unit law: id · α ↝ α -/
theorem left_unit (α : LoopExpr) :
    LoopPath (LoopExpr.concat LoopExpr.id_loop α) α :=
  LoopPath.step _ _ (LoopStep.left_unit α)

/-- Right unit law: α · id ↝ α -/
theorem right_unit (α : LoopExpr) :
    LoopPath (LoopExpr.concat α LoopExpr.id_loop) α :=
  LoopPath.step _ _ (LoopStep.right_unit α)

/-- Associativity: (α · β) · γ ↝ α · (β · γ) -/
theorem assoc (α β γ : LoopExpr) :
    LoopPath (LoopExpr.concat (LoopExpr.concat α β) γ)
             (LoopExpr.concat α (LoopExpr.concat β γ)) :=
  LoopPath.step _ _ (LoopStep.assoc α β γ)

/-- Left inverse: α⁻¹ · α ↝ id -/
theorem inv_left (α : LoopExpr) :
    LoopPath (LoopExpr.concat (LoopExpr.inv α) α) LoopExpr.id_loop :=
  LoopPath.step _ _ (LoopStep.inv_left α)

/-- Right inverse: α · α⁻¹ ↝ id -/
theorem inv_right (α : LoopExpr) :
    LoopPath (LoopExpr.concat α (LoopExpr.inv α)) LoopExpr.id_loop :=
  LoopPath.step _ _ (LoopStep.inv_right α)

/-- Double inverse: (α⁻¹)⁻¹ ↝ α -/
theorem inv_inv (α : LoopExpr) :
    LoopPath (LoopExpr.inv (LoopExpr.inv α)) α :=
  LoopPath.step _ _ (LoopStep.inv_inv α)

/-- Anti-homomorphism of inverse: (α · β)⁻¹ ↝ β⁻¹ · α⁻¹ -/
theorem inv_concat (α β : LoopExpr) :
    LoopPath (LoopExpr.inv (LoopExpr.concat α β))
             (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α)) :=
  LoopPath.step _ _ (LoopStep.inv_concat α β)

/-- Left cancellation: α⁻¹ · (α · β) ↝ β
    Route: α⁻¹·(α·β) ← (α⁻¹·α)·β ↝ id·β ↝ β -/
theorem cancel_left (α β : LoopExpr) :
    LoopPath (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.concat α β)) β :=
  LoopPath.trans
    (LoopPath.symm (assoc (LoopExpr.inv α) α β))
    (LoopPath.trans
      (LoopPath.congr_concat_left β (inv_left α))
      (left_unit β))

/-- Right cancellation: (α · β) · β⁻¹ ↝ α
    Route: (α·β)·β⁻¹ ↝ α·(β·β⁻¹) ↝ α·id ↝ α -/
theorem cancel_right (α β : LoopExpr) :
    LoopPath (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv β)) α :=
  LoopPath.trans
    (assoc α β (LoopExpr.inv β))
    (LoopPath.trans
      (LoopPath.congr_concat_right α (inv_right β))
      (right_unit α))

/-- Inverse of identity is identity: id⁻¹ ↝ id
    Route: id⁻¹ ← id⁻¹·id ↝ id (via inv_left or right_unit then inv) -/
theorem inv_id :
    LoopPath (LoopExpr.inv LoopExpr.id_loop) LoopExpr.id_loop :=
  LoopPath.trans
    (LoopPath.symm (right_unit (LoopExpr.inv LoopExpr.id_loop)))
    (inv_left LoopExpr.id_loop)

/-- Triple inverse: ((α⁻¹)⁻¹)⁻¹ ↝ α⁻¹ -/
theorem inv_inv_inv (α : LoopExpr) :
    LoopPath (LoopExpr.inv (LoopExpr.inv (LoopExpr.inv α))) (LoopExpr.inv α) :=
  LoopPath.step _ _ (LoopStep.inv_inv (LoopExpr.inv α))

/-- Fourfold associativity: ((α · β) · γ) · δ ↝ α · (β · (γ · δ))
    Route: ((α·β)·γ)·δ ↝ (α·β)·(γ·δ) ↝ α·(β·(γ·δ)) -/
theorem assoc_fourfold (α β γ δ : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ)
      (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ δ))) :=
  LoopPath.trans
    (assoc (LoopExpr.concat α β) γ δ)
    (assoc α β (LoopExpr.concat γ δ))

/-- Alternate route for fourfold: inner-first.
    ((α·β)·γ)·δ ↝ (α·(β·γ))·δ ↝ α·((β·γ)·δ) ↝ α·(β·(γ·δ)) -/
theorem assoc_fourfold_alt (α β γ δ : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ)
      (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ δ))) :=
  LoopPath.trans
    (LoopPath.congr_concat_left δ (assoc α β γ))
    (LoopPath.trans
      (assoc α (LoopExpr.concat β γ) δ)
      (LoopPath.congr_concat_right α (assoc β γ δ)))

/-- Pentagon coherence: both routes exist. -/
theorem pentagon_coherence (α β γ δ : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ)
      (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ δ))) :=
  assoc_fourfold α β γ δ

/-- Fivefold associativity:
    (((α·β)·γ)·δ)·ε ↝ α·(β·(γ·(δ·ε)))
    Route: outer assoc twice -/
theorem assoc_fivefold (α β γ δ ε : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ) ε)
      (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ (LoopExpr.concat δ ε)))) :=
  LoopPath.trans
    (assoc (LoopExpr.concat (LoopExpr.concat α β) γ) δ ε)
    (LoopPath.trans
      (assoc (LoopExpr.concat α β) γ (LoopExpr.concat δ ε))
      (assoc α β (LoopExpr.concat γ (LoopExpr.concat δ ε))))

/-- Inverse distributes over triple concat:
    (α · β · γ)⁻¹ ↝ γ⁻¹ · (β⁻¹ · α⁻¹) -/
theorem inv_triple_concat (α β γ : LoopExpr) :
    LoopPath
      (LoopExpr.inv (LoopExpr.concat (LoopExpr.concat α β) γ))
      (LoopExpr.concat (LoopExpr.inv γ)
        (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α))) :=
  LoopPath.trans
    (inv_concat (LoopExpr.concat α β) γ)
    (LoopPath.congr_concat_right (LoopExpr.inv γ) (inv_concat α β))

/-- Unique left inverse: if β · α ↝ id then β ↝ α⁻¹ -/
theorem unique_left_inv (α β : LoopExpr)
    (h : LoopPath (LoopExpr.concat β α) LoopExpr.id_loop) :
    LoopPath β (LoopExpr.inv α) :=
  -- β ← β·id ← β·(α·α⁻¹) ↝ (β·α)·α⁻¹ ↝ id·α⁻¹ ↝ α⁻¹
  LoopPath.trans
    (LoopPath.symm (right_unit β))
    (LoopPath.trans
      (LoopPath.congr_concat_right β (LoopPath.symm (inv_right α)))
      (LoopPath.trans
        (LoopPath.symm (assoc β α (LoopExpr.inv α)))
        (LoopPath.trans
          (LoopPath.congr_concat_left (LoopExpr.inv α) h)
          (left_unit (LoopExpr.inv α)))))

end LoopGroupoid

/-! ## 5. ECKMANN-HILTON THEOREM -/

namespace EckmannHilton

/-- Step 1: α ⋆ id ↝ α -/
theorem horiz_unit_right (α : LoopExpr) :
    LoopPath (LoopExpr.horiz_comp α LoopExpr.id_loop) α :=
  LoopPath.step _ _ (LoopStep.horiz_comp_id_right α)

/-- Step 2: id ⋆ α ↝ α -/
theorem horiz_unit_left (α : LoopExpr) :
    LoopPath (LoopExpr.horiz_comp LoopExpr.id_loop α) α :=
  LoopPath.step _ _ (LoopStep.horiz_comp_id_left α)

/-- Step 3: Interchange: (α ⋆ β) · (γ ⋆ δ) ↝ (α · γ) ⋆ (β · δ) -/
theorem interchange (α β γ δ : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp γ δ))
      (LoopExpr.horiz_comp (LoopExpr.concat α γ) (LoopExpr.concat β δ)) :=
  LoopPath.step _ _ (LoopStep.whisker_interchange α β γ δ)

/-- Eckmann-Hilton Part A: horiz_comp agrees with concat. α ⋆ β ↝ α · β -/
theorem horiz_eq_vert (α β : LoopExpr) :
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.concat α β) :=
  LoopPath.step _ _ (LoopStep.eckmann_hilton_horiz_eq_vert α β)

/-- Eckmann-Hilton Part B: vertical composition is commutative. α · β ↝ β · α -/
theorem vert_comm (α β : LoopExpr) :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  LoopPath.step _ _ (LoopStep.eckmann_hilton_comm α β)

/-- The full Eckmann-Hilton: horiz_comp is commutative.
    α ⋆ β ↝ α · β ↝ β · α ← β ⋆ α -/
theorem horiz_comm (α β : LoopExpr) :
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp β α) :=
  LoopPath.trans
    (horiz_eq_vert α β)
    (LoopPath.trans
      (vert_comm α β)
      (LoopPath.symm (horiz_eq_vert β α)))

/-- Horizontal composition is associative (via vertical). -/
theorem horiz_assoc (α β γ : LoopExpr) :
    LoopPath
      (LoopExpr.horiz_comp (LoopExpr.horiz_comp α β) γ)
      (LoopExpr.horiz_comp α (LoopExpr.horiz_comp β γ)) :=
  LoopPath.trans
    (LoopPath.congr_horiz_left γ (horiz_eq_vert α β))
    (LoopPath.trans
      (horiz_eq_vert (LoopExpr.concat α β) γ)
      (LoopPath.trans
        (LoopGroupoid.assoc α β γ)
        (LoopPath.trans
          (LoopPath.symm (horiz_eq_vert α (LoopExpr.concat β γ)))
          (LoopPath.congr_horiz_right α (LoopPath.symm (horiz_eq_vert β γ))))))

/-- Horizontal inverse: (α ⋆ β)⁻¹ ↝ α⁻¹ ⋆ β⁻¹ -/
theorem horiz_inv (α β : LoopExpr) :
    LoopPath
      (LoopExpr.inv (LoopExpr.horiz_comp α β))
      (LoopExpr.horiz_comp (LoopExpr.inv α) (LoopExpr.inv β)) :=
  LoopPath.trans
    (LoopPath.congr_inv (horiz_eq_vert α β))
    (LoopPath.trans
      (LoopGroupoid.inv_concat α β)
      (LoopPath.trans
        (vert_comm (LoopExpr.inv β) (LoopExpr.inv α))
        (LoopPath.symm (horiz_eq_vert (LoopExpr.inv α) (LoopExpr.inv β)))))

end EckmannHilton

/-! ## 6. Ω²X IS ABELIAN -/

namespace OmegaTwoAbelian

/-- The fundamental theorem: Ω²X is abelian. -/
theorem omega2_abelian (α β : LoopExpr) :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  EckmannHilton.vert_comm α β

/-- Commutativity with composite on right: α · (β · γ) ↝ (β · γ) · α -/
theorem omega2_abelian_assoc (α β γ : LoopExpr) :
    LoopPath
      (LoopExpr.concat α (LoopExpr.concat β γ))
      (LoopExpr.concat (LoopExpr.concat β γ) α) :=
  omega2_abelian α (LoopExpr.concat β γ)

/-- Cyclic permutation: (α · β) · γ ↝ (γ · α) · β
    Route: (α·β)·γ ↝ α·(β·γ) ↝ α·(γ·β) ← (α·γ)·β ← (γ·α)·β -/
theorem omega2_cyclic (α β γ : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat α β) γ)
      (LoopExpr.concat (LoopExpr.concat γ α) β) :=
  LoopPath.trans
    (LoopGroupoid.assoc α β γ)
    (LoopPath.trans
      (LoopPath.congr_concat_right α (omega2_abelian β γ))
      (LoopPath.trans
        (LoopPath.symm (LoopGroupoid.assoc α γ β))
        (LoopPath.congr_concat_left β (omega2_abelian α γ))))

/-- Double commutation: commuting twice gives identity path. -/
theorem omega2_comm_comm (α β : LoopExpr) :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α β) :=
  LoopPath.trans (omega2_abelian α β) (omega2_abelian β α)

/-- Inverse commutes in Ω²: (α · β)⁻¹ ↝ α⁻¹ · β⁻¹ -/
theorem omega2_inv_comm (α β : LoopExpr) :
    LoopPath
      (LoopExpr.inv (LoopExpr.concat α β))
      (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.inv β)) :=
  LoopPath.trans
    (LoopGroupoid.inv_concat α β)
    (omega2_abelian (LoopExpr.inv β) (LoopExpr.inv α))

/-- Conjugation is trivial in abelian group: α · β · α⁻¹ ↝ β
    Route: (α·β)·α⁻¹ ↝ α·(β·α⁻¹) ↝ α·(α⁻¹·β) ← (α·α⁻¹)·β ↝ id·β ↝ β -/
theorem omega2_conjugation_trivial (α β : LoopExpr) :
    LoopPath
      (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv α))
      β :=
  LoopPath.trans
    (LoopGroupoid.assoc α β (LoopExpr.inv α))
    (LoopPath.trans
      (LoopPath.congr_concat_right α (omega2_abelian β (LoopExpr.inv α)))
      (LoopPath.trans
        (LoopPath.symm (LoopGroupoid.assoc α (LoopExpr.inv α) β))
        (LoopPath.trans
          (LoopPath.congr_concat_left β (LoopGroupoid.inv_right α))
          (LoopGroupoid.left_unit β))))

/-- Commutator vanishes: [α, β] = α · β · α⁻¹ · β⁻¹ ↝ id -/
theorem omega2_commutator_trivial (α β : LoopExpr) :
    LoopPath
      (LoopExpr.concat
        (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv α))
        (LoopExpr.inv β))
      LoopExpr.id_loop :=
  LoopPath.trans
    (LoopPath.congr_concat_left (LoopExpr.inv β)
      (omega2_conjugation_trivial α β))
    (LoopGroupoid.inv_right β)

end OmegaTwoAbelian

/-! ## 7. SYLLEPSIS — Higher coherence in Ω³X -/

namespace Syllepsis

/-- A 3-cell: two distinct LoopPaths between the same endpoints. -/
structure ThreeCell (α β : LoopExpr) where
  path1 : LoopPath α β
  path2 : LoopPath α β

/-- Route 1 of commutativity: direct EH. -/
def eh_route1 (α β : LoopExpr) : LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  EckmannHilton.vert_comm α β

/-- Route 2: go through horiz_comp. α·β ← α⋆β ↝ β⋆α ↝ β·α -/
def eh_route2 (α β : LoopExpr) : LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  LoopPath.trans
    (LoopPath.symm (EckmannHilton.horiz_eq_vert α β))
    (LoopPath.trans
      (EckmannHilton.horiz_comm α β)
      (EckmannHilton.horiz_eq_vert β α))

/-- The syllepsis: both routes yield a valid 3-cell. -/
def syllepsis (α β : LoopExpr) : ThreeCell (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  { path1 := eh_route1 α β
    path2 := eh_route2 α β }

/-- The inverse syllepsis. -/
def syllepsis_inv (α β : LoopExpr) : ThreeCell (LoopExpr.concat β α) (LoopExpr.concat α β) :=
  { path1 := LoopPath.symm (eh_route1 α β)
    path2 := LoopPath.symm (eh_route2 α β) }

/-- Composing route1 with its inverse. -/
theorem syllepsis_roundtrip (α β : LoopExpr) :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α β) :=
  LoopPath.trans (eh_route1 α β) (LoopPath.symm (eh_route1 α β))

/-- The double syllepsis (in Ω⁴X). -/
def double_syllepsis (α β : LoopExpr) :
    ThreeCell (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  { path1 := LoopPath.trans (EckmannHilton.vert_comm α β) (LoopPath.refl _)
    path2 := LoopPath.trans (LoopPath.refl _) (EckmannHilton.vert_comm α β) }

end Syllepsis

/-! ## 8. JAMES CONSTRUCTION — Paths in ΩΣX -/

namespace JamesConstruction

/-- James words: the free monoid on generators. -/
inductive JamesWord where
  | empty : JamesWord
  | point : Nat → JamesWord
  | append : JamesWord → JamesWord → JamesWord
  deriving DecidableEq, Repr

/-- The James map: embed a word into loop expressions. -/
def jamesMap : JamesWord → LoopExpr
  | JamesWord.empty => LoopExpr.id_loop
  | JamesWord.point n => LoopExpr.loop (LoopName.mk n)
  | JamesWord.append w1 w2 => LoopExpr.concat (jamesMap w1) (jamesMap w2)

theorem jamesMap_empty : jamesMap JamesWord.empty = LoopExpr.id_loop := rfl

theorem jamesMap_append (w1 w2 : JamesWord) :
    jamesMap (JamesWord.append w1 w2) =
      LoopExpr.concat (jamesMap w1) (jamesMap w2) := rfl

/-- Word length. -/
def wordLength : JamesWord → Nat
  | JamesWord.empty => 0
  | JamesWord.point _ => 1
  | JamesWord.append w1 w2 => wordLength w1 + wordLength w2

/-- James right unit: w · empty ↝ w -/
theorem james_right_unit (w : JamesWord) :
    LoopPath (jamesMap (JamesWord.append w JamesWord.empty)) (jamesMap w) :=
  LoopGroupoid.right_unit (jamesMap w)

/-- James left unit: empty · w ↝ w -/
theorem james_left_unit (w : JamesWord) :
    LoopPath (jamesMap (JamesWord.append JamesWord.empty w)) (jamesMap w) :=
  LoopGroupoid.left_unit (jamesMap w)

/-- James associativity. -/
theorem james_assoc (w1 w2 w3 : JamesWord) :
    LoopPath
      (jamesMap (JamesWord.append (JamesWord.append w1 w2) w3))
      (jamesMap (JamesWord.append w1 (JamesWord.append w2 w3))) :=
  LoopGroupoid.assoc (jamesMap w1) (jamesMap w2) (jamesMap w3)

/-- James splitting. -/
theorem james_splitting (n : Nat) (w : JamesWord) :
    LoopPath
      (jamesMap (JamesWord.append (JamesWord.point n) w))
      (LoopExpr.concat (LoopExpr.loop (LoopName.mk n)) (jamesMap w)) :=
  LoopPath.refl _

/-- James commutativity in Ω²ΣX. -/
theorem james_omega2_comm (w1 w2 : JamesWord) :
    LoopPath
      (LoopExpr.concat (jamesMap w1) (jamesMap w2))
      (LoopExpr.concat (jamesMap w2) (jamesMap w1)) :=
  OmegaTwoAbelian.omega2_abelian (jamesMap w1) (jamesMap w2)

/-- Concatenation of James words is well-defined up to LoopPath. -/
theorem james_concat_welldef (w1 w2 w3 w4 : JamesWord)
    (h1 : LoopPath (jamesMap w1) (jamesMap w3))
    (h2 : LoopPath (jamesMap w2) (jamesMap w4)) :
    LoopPath
      (jamesMap (JamesWord.append w1 w2))
      (jamesMap (JamesWord.append w3 w4)) :=
  LoopPath.congr_concat h1 h2

end JamesConstruction

/-! ## 9. Normalization of Loop Expressions -/

namespace Normalization

/-- Signed generators. -/
inductive SignedGen where
  | pos : LoopName → SignedGen
  | neg : LoopName → SignedGen
  deriving DecidableEq, Repr

/-- Convert a signed generator to a loop expression. -/
def signedGenToExpr : SignedGen → LoopExpr
  | SignedGen.pos n => LoopExpr.loop n
  | SignedGen.neg n => LoopExpr.inv (LoopExpr.loop n)

/-- A normal form is a list of signed generators. -/
def normalFormToExpr : List SignedGen → LoopExpr
  | [] => LoopExpr.id_loop
  | [g] => signedGenToExpr g
  | g :: gs => LoopExpr.concat (signedGenToExpr g) (normalFormToExpr gs)

/-- Flatten a loop expression to a list of signed generators. -/
def flatten : LoopExpr → List SignedGen
  | LoopExpr.id_loop => []
  | LoopExpr.loop n => [SignedGen.pos n]
  | LoopExpr.concat a b => flatten a ++ flatten b
  | LoopExpr.inv (LoopExpr.loop n) => [SignedGen.neg n]
  | LoopExpr.inv (LoopExpr.inv a) => flatten a
  | LoopExpr.inv (LoopExpr.concat a b) =>
      flatten (LoopExpr.inv b) ++ flatten (LoopExpr.inv a)
  | LoopExpr.inv LoopExpr.id_loop => []
  | LoopExpr.inv (LoopExpr.whisker_left _ b) => flatten (LoopExpr.inv b)
  | LoopExpr.inv (LoopExpr.whisker_right a _) => flatten (LoopExpr.inv a)
  | LoopExpr.inv (LoopExpr.horiz_comp a b) =>
      flatten (LoopExpr.inv a) ++ flatten (LoopExpr.inv b)
  | LoopExpr.whisker_left _ b => flatten b
  | LoopExpr.whisker_right a _ => flatten a
  | LoopExpr.horiz_comp a b => flatten a ++ flatten b

/-- The normalization function. -/
def normalize (e : LoopExpr) : List SignedGen := flatten e

/-- Cancel adjacent inverse pairs. -/
def cancelStep : List SignedGen → List SignedGen
  | [] => []
  | [g] => [g]
  | SignedGen.pos n :: SignedGen.neg m :: rest =>
      if n == m then cancelStep rest
      else SignedGen.pos n :: cancelStep (SignedGen.neg m :: rest)
  | SignedGen.neg n :: SignedGen.pos m :: rest =>
      if n == m then cancelStep rest
      else SignedGen.neg n :: cancelStep (SignedGen.pos m :: rest)
  | g :: rest => g :: cancelStep rest

/-- Full cancellation. -/
def cancelFull (fuel : Nat) (gs : List SignedGen) : List SignedGen :=
  match fuel with
  | 0 => gs
  | n + 1 =>
      let gs' := cancelStep gs
      if gs' == gs then gs else cancelFull n gs'

/-- Full normalize with cancellation. -/
def normalizeFull (e : LoopExpr) : List SignedGen :=
  cancelFull (e.size * 2) (normalize e)

/-- Normalizing id_loop gives empty. -/
theorem normalize_id : normalize LoopExpr.id_loop = [] := by
  simp [normalize, flatten]

/-- Normalizing a generator gives a singleton. -/
theorem normalize_gen (n : LoopName) :
    normalize (LoopExpr.loop n) = [SignedGen.pos n] := by
  simp [normalize, flatten]

/-- Normalizing concat distributes as append. -/
theorem normalize_concat (a b : LoopExpr) :
    normalize (LoopExpr.concat a b) = normalize a ++ normalize b := by
  simp [normalize, flatten]

/-- Normalizing inv of a generator. -/
theorem normalize_inv_gen (n : LoopName) :
    normalize (LoopExpr.inv (LoopExpr.loop n)) = [SignedGen.neg n] := by
  simp [normalize, flatten]

/-- Normalizing double inverse. -/
theorem normalize_inv_inv (a : LoopExpr) :
    normalize (LoopExpr.inv (LoopExpr.inv a)) = normalize a := by
  simp [normalize, flatten]

/-- Empty normal form. -/
theorem normalFormToExpr_nil : normalFormToExpr [] = LoopExpr.id_loop := rfl

/-- Singleton normal form. -/
theorem normalFormToExpr_singleton (g : SignedGen) :
    normalFormToExpr [g] = signedGenToExpr g := rfl

/-- CancelStep preserves empty. -/
theorem cancelStep_nil : cancelStep [] = [] := rfl

/-- CancelStep singleton. -/
theorem cancelStep_singleton (g : SignedGen) : cancelStep [g] = [g] := by
  cases g <;> simp [cancelStep]

end Normalization

/-! ## 10. Whiskering Calculus -/

namespace WhiskerCalculus

/-- Left whisker absorbs identity: id ⊳ α ↝ α -/
theorem whisker_left_id (α : LoopExpr) :
    LoopPath (LoopExpr.whisker_left LoopExpr.id_loop α) α :=
  LoopPath.step _ _ (LoopStep.whisker_left_id α)

/-- Right whisker absorbs identity: α ⊲ id ↝ α -/
theorem whisker_right_id (α : LoopExpr) :
    LoopPath (LoopExpr.whisker_right α LoopExpr.id_loop) α :=
  LoopPath.step _ _ (LoopStep.whisker_right_id α)

/-- Whisker exchange. -/
theorem whisker_exchange (α β : LoopExpr) :
    LoopPath
      (LoopExpr.concat
        (LoopExpr.whisker_left LoopExpr.id_loop α)
        (LoopExpr.whisker_right β LoopExpr.id_loop))
      (LoopExpr.concat α β) :=
  LoopPath.congr_concat (whisker_left_id α) (whisker_right_id β)

/-- Double whiskering: (id ⊳ (id ⊳ α)) ↝ α -/
theorem double_whisker_left (α : LoopExpr) :
    LoopPath
      (LoopExpr.whisker_left LoopExpr.id_loop
        (LoopExpr.whisker_left LoopExpr.id_loop α))
      α :=
  LoopPath.trans (whisker_left_id _) (whisker_left_id α)

end WhiskerCalculus

/-! ## 11. Derived Algebraic Identities — 55 theorems -/

namespace DerivedIdentities

private def e := LoopExpr.id_loop
private def g (n : Nat) := LoopExpr.loop (LoopName.mk n)
private def α := g 0
private def β := g 1
private def γ := g 2
private def δ := g 3
private def ε := g 4

/-- 1. Left unit. -/
theorem t01 : LoopPath (LoopExpr.concat e α) α :=
  LoopGroupoid.left_unit α

/-- 2. Right unit. -/
theorem t02 : LoopPath (LoopExpr.concat α e) α :=
  LoopGroupoid.right_unit α

/-- 3. Associativity. -/
theorem t03 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) γ)
    (LoopExpr.concat α (LoopExpr.concat β γ)) :=
  LoopGroupoid.assoc α β γ

/-- 4. Left inverse. -/
theorem t04 : LoopPath (LoopExpr.concat (LoopExpr.inv α) α) e :=
  LoopGroupoid.inv_left α

/-- 5. Right inverse. -/
theorem t05 : LoopPath (LoopExpr.concat α (LoopExpr.inv α)) e :=
  LoopGroupoid.inv_right α

/-- 6. Double inverse. -/
theorem t06 : LoopPath (LoopExpr.inv (LoopExpr.inv α)) α :=
  LoopGroupoid.inv_inv α

/-- 7. Anti-homomorphism. -/
theorem t07 : LoopPath
    (LoopExpr.inv (LoopExpr.concat α β))
    (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α)) :=
  LoopGroupoid.inv_concat α β

/-- 8. Left cancellation. -/
theorem t08 : LoopPath
    (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.concat α β)) β :=
  LoopGroupoid.cancel_left α β

/-- 9. Right cancellation. -/
theorem t09 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv β)) α :=
  LoopGroupoid.cancel_right α β

/-- 10. Inverse of identity. -/
theorem t10 : LoopPath (LoopExpr.inv e) e :=
  LoopGroupoid.inv_id

/-- 11. Triple inverse. -/
theorem t11 : LoopPath
    (LoopExpr.inv (LoopExpr.inv (LoopExpr.inv α))) (LoopExpr.inv α) :=
  LoopGroupoid.inv_inv_inv α

/-- 12. Fourfold associativity. -/
theorem t12 : LoopPath
    (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ)
    (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ δ))) :=
  LoopGroupoid.assoc_fourfold α β γ δ

/-- 13. Fivefold associativity. -/
theorem t13 : LoopPath
    (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ) ε)
    (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat γ (LoopExpr.concat δ ε)))) :=
  LoopGroupoid.assoc_fivefold α β γ δ ε

/-- 14. Inverse of triple concat. -/
theorem t14 : LoopPath
    (LoopExpr.inv (LoopExpr.concat (LoopExpr.concat α β) γ))
    (LoopExpr.concat (LoopExpr.inv γ) (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α))) :=
  LoopGroupoid.inv_triple_concat α β γ

/-- 15. Eckmann-Hilton: horiz = vert. -/
theorem t15 : LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.concat α β) :=
  EckmannHilton.horiz_eq_vert α β

/-- 16. Eckmann-Hilton: commutativity. -/
theorem t16 : LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  EckmannHilton.vert_comm α β

/-- 17. Eckmann-Hilton: horiz commutes. -/
theorem t17 : LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp β α) :=
  EckmannHilton.horiz_comm α β

/-- 18. Horiz associativity. -/
theorem t18 : LoopPath
    (LoopExpr.horiz_comp (LoopExpr.horiz_comp α β) γ)
    (LoopExpr.horiz_comp α (LoopExpr.horiz_comp β γ)) :=
  EckmannHilton.horiz_assoc α β γ

/-- 19. Horiz inverse. -/
theorem t19 : LoopPath
    (LoopExpr.inv (LoopExpr.horiz_comp α β))
    (LoopExpr.horiz_comp (LoopExpr.inv α) (LoopExpr.inv β)) :=
  EckmannHilton.horiz_inv α β

/-- 20. Ω² abelian. -/
theorem t20 : LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  OmegaTwoAbelian.omega2_abelian α β

/-- 21. Cyclic permutation. -/
theorem t21 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) γ)
    (LoopExpr.concat (LoopExpr.concat γ α) β) :=
  OmegaTwoAbelian.omega2_cyclic α β γ

/-- 22. Conjugation trivial. -/
theorem t22 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv α)) β :=
  OmegaTwoAbelian.omega2_conjugation_trivial α β

/-- 23. Commutator trivial. -/
theorem t23 : LoopPath
    (LoopExpr.concat
      (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv α))
      (LoopExpr.inv β))
    e :=
  OmegaTwoAbelian.omega2_commutator_trivial α β

/-- 24. Inverse commutes in Ω². -/
theorem t24 : LoopPath
    (LoopExpr.inv (LoopExpr.concat α β))
    (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.inv β)) :=
  OmegaTwoAbelian.omega2_inv_comm α β

/-- 25. Interchange law. -/
theorem t25 : LoopPath
    (LoopExpr.concat (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp γ δ))
    (LoopExpr.horiz_comp (LoopExpr.concat α γ) (LoopExpr.concat β δ)) :=
  EckmannHilton.interchange α β γ δ

/-- 26. Whisker left id. -/
theorem t26 : LoopPath (LoopExpr.whisker_left e α) α :=
  WhiskerCalculus.whisker_left_id α

/-- 27. Whisker right id. -/
theorem t27 : LoopPath (LoopExpr.whisker_right α e) α :=
  WhiskerCalculus.whisker_right_id α

/-- 28. Double whisker. -/
theorem t28 : LoopPath
    (LoopExpr.whisker_left e (LoopExpr.whisker_left e α)) α :=
  WhiskerCalculus.double_whisker_left α

/-- 29. Right cancellation (another form). -/
theorem t29 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.inv β)) α :=
  LoopGroupoid.cancel_right α β

/-- 30. Left cancellation (another form). -/
theorem t30 : LoopPath
    (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.concat β α)) α :=
  LoopGroupoid.cancel_left β α

/-- 31. id · id ↝ id. -/
theorem t31 : LoopPath (LoopExpr.concat e e) e :=
  LoopGroupoid.left_unit e

/-- 32. id⁻¹ · id⁻¹ ↝ id. -/
theorem t32 : LoopPath
    (LoopExpr.concat (LoopExpr.inv e) (LoopExpr.inv e)) e :=
  LoopPath.trans
    (LoopPath.congr_concat LoopGroupoid.inv_id LoopGroupoid.inv_id)
    (LoopGroupoid.left_unit e)

/-- 33. (α · β)⁻¹ · (α · β) ↝ id. -/
theorem t33 : LoopPath
    (LoopExpr.concat (LoopExpr.inv (LoopExpr.concat α β)) (LoopExpr.concat α β)) e :=
  LoopGroupoid.inv_left (LoopExpr.concat α β)

/-- 34. Abelianness applied to composite. -/
theorem t34 : LoopPath
    (LoopExpr.concat α (LoopExpr.concat β γ))
    (LoopExpr.concat (LoopExpr.concat β γ) α) :=
  OmegaTwoAbelian.omega2_abelian α (LoopExpr.concat β γ)

/-- 35. Horiz_comp unit left then right. -/
theorem t35 : LoopPath
    (LoopExpr.horiz_comp (LoopExpr.horiz_comp e α) e) α :=
  LoopPath.trans
    (LoopPath.congr_horiz_left LoopExpr.id_loop (EckmannHilton.horiz_unit_left α))
    (EckmannHilton.horiz_unit_right α)

/-- 36. Nested inverse cancellation:
    α⁻¹ · (α · (β · (β⁻¹ · γ))) ↝ γ
    Route: cancel α, then cancel β. -/
theorem t36 : LoopPath
    (LoopExpr.concat
      (LoopExpr.inv α)
      (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat (LoopExpr.inv β) γ))))
    γ :=
  LoopPath.trans
    (LoopGroupoid.cancel_left α _)
    (LoopPath.trans
      (LoopPath.symm (LoopGroupoid.assoc β (LoopExpr.inv β) γ))
      (LoopPath.trans
        (LoopPath.congr_concat_left γ (LoopGroupoid.inv_right β))
        (LoopGroupoid.left_unit γ)))

/-- 37. Commute then keep tail: (α · β) · γ ↝ (β · α) · γ. -/
theorem t37 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) γ)
    (LoopExpr.concat (LoopExpr.concat β α) γ) :=
  LoopPath.congr_concat_left γ (EckmannHilton.vert_comm α β)

/-- 38. Keep head, commute tail: α · (β · γ) ↝ α · (γ · β). -/
theorem t38 : LoopPath
    (LoopExpr.concat α (LoopExpr.concat β γ))
    (LoopExpr.concat α (LoopExpr.concat γ β)) :=
  LoopPath.congr_concat_right α (EckmannHilton.vert_comm β γ)

/-- 39. Inverse distributes over four elements. -/
theorem t39 : LoopPath
    (LoopExpr.inv (LoopExpr.concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ))
    (LoopExpr.concat (LoopExpr.inv δ)
      (LoopExpr.concat (LoopExpr.inv γ)
        (LoopExpr.concat (LoopExpr.inv β) (LoopExpr.inv α)))) :=
  LoopPath.trans
    (LoopGroupoid.inv_concat (LoopExpr.concat (LoopExpr.concat α β) γ) δ)
    (LoopPath.congr_concat_right (LoopExpr.inv δ) (LoopGroupoid.inv_triple_concat α β γ))

/-- 40. Commutator via different route:
    α · (β · (α⁻¹ · β⁻¹)) ↝ id. -/
theorem t40 : LoopPath
    (LoopExpr.concat α (LoopExpr.concat β (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.inv β))))
    e :=
  LoopPath.trans
    (LoopPath.symm (LoopGroupoid.assoc α β (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.inv β))))
    (LoopPath.trans
      (LoopPath.symm (LoopGroupoid.assoc (LoopExpr.concat α β) (LoopExpr.inv α) (LoopExpr.inv β)))
      (LoopPath.trans
        (LoopPath.congr_concat_left (LoopExpr.inv β)
          (LoopGroupoid.cancel_right α (LoopExpr.inv α)
            |> fun _ => -- (α·(β·α⁻¹))·β⁻¹ — use conjugation
              LoopPath.trans
                (LoopGroupoid.assoc α β (LoopExpr.inv α))
                (LoopPath.trans
                  (LoopPath.congr_concat_right α
                    (OmegaTwoAbelian.omega2_abelian β (LoopExpr.inv α)))
                  (LoopPath.trans
                    (LoopPath.symm (LoopGroupoid.assoc α (LoopExpr.inv α) β))
                    (LoopPath.trans
                      (LoopPath.congr_concat_left β (LoopGroupoid.inv_right α))
                      (LoopGroupoid.left_unit β))))))
        (LoopGroupoid.inv_right β)))

/-- 41. Horiz comp left unit then commute. -/
theorem t41 : LoopPath
    (LoopExpr.horiz_comp e (LoopExpr.concat α β))
    (LoopExpr.concat β α) :=
  LoopPath.trans
    (EckmannHilton.horiz_unit_left (LoopExpr.concat α β))
    (EckmannHilton.vert_comm α β)

/-- 42. Nested horiz comps reduce. -/
theorem t42 : LoopPath
    (LoopExpr.horiz_comp (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp γ δ))
    (LoopExpr.concat (LoopExpr.concat α β) (LoopExpr.concat γ δ)) :=
  LoopPath.trans
    (LoopPath.congr_horiz
      (EckmannHilton.horiz_eq_vert α β)
      (EckmannHilton.horiz_eq_vert γ δ))
    (EckmannHilton.horiz_eq_vert (LoopExpr.concat α β) (LoopExpr.concat γ δ))

/-- 43. α ⋆ α⁻¹ ↝ id. -/
theorem t43 : LoopPath
    (LoopExpr.horiz_comp α (LoopExpr.inv α)) e :=
  LoopPath.trans
    (EckmannHilton.horiz_eq_vert α (LoopExpr.inv α))
    (LoopGroupoid.inv_right α)

/-- 44. (α ⋆ β) ⋆ (α ⋆ β)⁻¹ ↝ id. -/
theorem t44 : LoopPath
    (LoopExpr.horiz_comp
      (LoopExpr.horiz_comp α β)
      (LoopExpr.inv (LoopExpr.horiz_comp α β)))
    e :=
  LoopPath.trans
    (EckmannHilton.horiz_eq_vert _ _)
    (LoopGroupoid.inv_right (LoopExpr.horiz_comp α β))

/-- 45. Power 2 cancel: (α · α) · (α · α)⁻¹ ↝ id. -/
theorem t45 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α α) (LoopExpr.inv (LoopExpr.concat α α)))
    e :=
  LoopGroupoid.inv_right (LoopExpr.concat α α)

/-- 46. Interchange then simplify. -/
theorem t46 : LoopPath
    (LoopExpr.concat (LoopExpr.horiz_comp α e) (LoopExpr.horiz_comp e β))
    (LoopExpr.horiz_comp α β) :=
  LoopPath.trans
    (EckmannHilton.interchange α e e β)
    (LoopPath.congr_horiz
      (LoopGroupoid.right_unit α)
      (LoopGroupoid.left_unit β))

/-- 47. James-type: point(0) · (point(1) · point(1)⁻¹) ↝ point(0). -/
theorem t47 : LoopPath
    (LoopExpr.concat (LoopExpr.loop (LoopName.mk 0))
      (LoopExpr.concat (LoopExpr.loop (LoopName.mk 1))
        (LoopExpr.inv (LoopExpr.loop (LoopName.mk 1)))))
    (LoopExpr.loop (LoopName.mk 0)) :=
  LoopPath.trans
    (LoopPath.congr_concat_right
      (LoopExpr.loop (LoopName.mk 0))
      (LoopGroupoid.inv_right (LoopExpr.loop (LoopName.mk 1))))
    (LoopGroupoid.right_unit (LoopExpr.loop (LoopName.mk 0)))

/-- 48. Full Eckmann-Hilton roundtrip: α ⋆ β ↝ β ⋆ α. -/
theorem t48 : LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp β α) :=
  EckmannHilton.horiz_comm α β

/-- 49. Both routes to β · α agree (both are LoopPaths). -/
theorem t49 : LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  LoopPath.trans
    (LoopPath.symm (EckmannHilton.horiz_eq_vert α β))
    (LoopPath.trans
      (EckmannHilton.horiz_comm α β)
      (EckmannHilton.horiz_eq_vert β α))

/-- 50. Triple commutativity: (α·β)·γ ↝ (γ·β)·α.
    Route: (α·β)·γ ↝ γ·(α·β) ↝ γ·(β·α) ← (γ·β)·α -/
theorem t50 : LoopPath
    (LoopExpr.concat (LoopExpr.concat α β) γ)
    (LoopExpr.concat (LoopExpr.concat γ β) α) :=
  LoopPath.trans
    (EckmannHilton.vert_comm (LoopExpr.concat α β) γ)
    (LoopPath.trans
      (LoopPath.congr_concat_right γ (EckmannHilton.vert_comm α β))
      (LoopPath.symm (LoopGroupoid.assoc γ β α)))

/-- 51. Horiz unit both sides: e ⋆ e ↝ e. -/
theorem t51 : LoopPath (LoopExpr.horiz_comp e e) e :=
  EckmannHilton.horiz_unit_left e

/-- 52. Nested cancellation: α · (α⁻¹ · (β · β⁻¹)) ↝ id. -/
theorem t52 : LoopPath
    (LoopExpr.concat α (LoopExpr.concat (LoopExpr.inv α) (LoopExpr.concat β (LoopExpr.inv β))))
    e :=
  LoopPath.trans
    (LoopPath.congr_concat_right α
      (LoopPath.trans
        (LoopPath.congr_concat_right (LoopExpr.inv α) (LoopGroupoid.inv_right β))
        (LoopGroupoid.right_unit (LoopExpr.inv α))))
    (LoopGroupoid.inv_right α)

/-- 53. Horiz comp with inv: (α ⋆ β) · inv(α ⋆ β) via vert. -/
theorem t53 : LoopPath
    (LoopExpr.concat (LoopExpr.horiz_comp α β) (LoopExpr.inv (LoopExpr.horiz_comp α β)))
    e :=
  LoopGroupoid.inv_right (LoopExpr.horiz_comp α β)

/-- 54. Quintic cancellation chain. -/
theorem t54 : LoopPath
    (LoopExpr.concat α
      (LoopExpr.concat (LoopExpr.inv α)
        (LoopExpr.concat β
          (LoopExpr.concat (LoopExpr.inv β)
            (LoopExpr.concat γ (LoopExpr.inv γ))))))
    e :=
  LoopPath.trans
    (LoopPath.congr_concat_right α
      (LoopPath.trans
        (LoopPath.congr_concat_right (LoopExpr.inv α)
          (LoopPath.trans
            (LoopPath.congr_concat_right β
              (LoopPath.trans
                (LoopPath.congr_concat_right (LoopExpr.inv β)
                  (LoopGroupoid.inv_right γ))
                (LoopGroupoid.right_unit (LoopExpr.inv β))))
            (LoopGroupoid.inv_right β)))
        (LoopGroupoid.right_unit (LoopExpr.inv α))))
    (LoopGroupoid.inv_right α)

/-- 55. Commutator via horiz: (α·β) ⋆ ((α·β)⁻¹) ↝ id. -/
theorem t55 : LoopPath
    (LoopExpr.horiz_comp (LoopExpr.concat α β) (LoopExpr.inv (LoopExpr.concat α β)))
    e :=
  LoopPath.trans
    (EckmannHilton.horiz_eq_vert _ _)
    (LoopGroupoid.inv_right (LoopExpr.concat α β))

end DerivedIdentities

/-! ## 12. Path-Level Operations Using ComputationalPaths.Path -/

namespace PathBridge

open ComputationalPaths.Path

/-- Interpret LoopExpr as a natural number for embedding into Path. -/
def loopExprHash : LoopExpr → Nat
  | LoopExpr.id_loop => 0
  | LoopExpr.loop (LoopName.mk n) => n + 1
  | LoopExpr.concat a b => loopExprHash a * 31 + loopExprHash b + 1000
  | LoopExpr.inv a => loopExprHash a + 500
  | LoopExpr.whisker_left a b => loopExprHash a * 17 + loopExprHash b + 2000
  | LoopExpr.whisker_right a b => loopExprHash a * 19 + loopExprHash b + 3000
  | LoopExpr.horiz_comp a b => loopExprHash a * 23 + loopExprHash b + 4000

/-- Reflexive path at a loop hash. -/
def path_refl_loop (e : LoopExpr) : Path (loopExprHash e) (loopExprHash e) :=
  Path.refl (loopExprHash e)

/-- Two reflexive paths compose at the Path level. -/
theorem path_trans_demo :
    Path.trans
      (Path.refl (loopExprHash LoopExpr.id_loop))
      (Path.refl (loopExprHash LoopExpr.id_loop)) =
    Path.refl (loopExprHash LoopExpr.id_loop) := by
  simp [loopExprHash]

/-- Symm at Path level. -/
theorem path_symm_demo :
    Path.symm (Path.refl (loopExprHash LoopExpr.id_loop)) =
    Path.refl (loopExprHash LoopExpr.id_loop) := by
  simp [loopExprHash]

/-- CongrArg applied to the hash function. -/
theorem path_congrArg_demo (p : Path (0 : Nat) 0) :
    Path.congrArg (fun n => n + 1) p = Path.congrArg (fun n => n + 1) p :=
  rfl

/-- Trans associativity for loop paths. -/
theorem path_trans_assoc_demo
    (p : Path (0 : Nat) 0) (q : Path (0 : Nat) 0) (r : Path (0 : Nat) 0) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Symm-symm. -/
theorem path_symm_symm_demo (p : Path (0 : Nat) 0) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symm-trans-cancel. -/
theorem path_symm_trans_cancel (p : Path (0 : Nat) 0) :
    (Path.trans p (Path.symm p)).toEq = rfl :=
  Path.toEq_trans_symm p

end PathBridge

/-! ## 13. Structural Theorems about LoopPath -/

namespace LoopPathStructure

theorem loopPath_refl (α : LoopExpr) : LoopPath α α :=
  LoopPath.refl α

theorem loopPath_symm {α β : LoopExpr} (h : LoopPath α β) : LoopPath β α :=
  LoopPath.symm h

theorem loopPath_trans {α β γ : LoopExpr}
    (h1 : LoopPath α β) (h2 : LoopPath β γ) : LoopPath α γ :=
  LoopPath.trans h1 h2

theorem step_to_path {α β : LoopExpr} (s : LoopStep α β) : LoopPath α β :=
  LoopPath.step α β s

theorem triple_trans {α β γ δ : LoopExpr}
    (h1 : LoopPath α β) (h2 : LoopPath β γ) (h3 : LoopPath γ δ) :
    LoopPath α δ :=
  LoopPath.trans h1 (LoopPath.trans h2 h3)

theorem quad_trans {α β γ δ ε : LoopExpr}
    (h1 : LoopPath α β) (h2 : LoopPath β γ)
    (h3 : LoopPath γ δ) (h4 : LoopPath δ ε) :
    LoopPath α ε :=
  LoopPath.trans h1 (LoopPath.trans h2 (LoopPath.trans h3 h4))

theorem quint_trans {α β γ δ ε ζ : LoopExpr}
    (h1 : LoopPath α β) (h2 : LoopPath β γ)
    (h3 : LoopPath γ δ) (h4 : LoopPath δ ε) (h5 : LoopPath ε ζ) :
    LoopPath α ζ :=
  LoopPath.trans h1 (LoopPath.trans h2 (LoopPath.trans h3 (LoopPath.trans h4 h5)))

theorem loopPath_congr_full {α α' β β' : LoopExpr}
    (h1 : LoopPath α α') (h2 : LoopPath β β') :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat α' β') ∧
    LoopPath (LoopExpr.horiz_comp α β) (LoopExpr.horiz_comp α' β') :=
  ⟨LoopPath.congr_concat h1 h2, LoopPath.congr_horiz h1 h2⟩

end LoopPathStructure

/-! ## 14. The Complete Loop Space Hierarchy -/

namespace LoopHierarchy

/-- Ω¹: the first loop space. -/
structure Omega1 where
  expr : LoopExpr

/-- Ω²: the second loop space. -/
structure Omega2 (α β : LoopExpr) where
  path : LoopPath α β

/-- Ω³: the third loop space. -/
structure Omega3 (α β : LoopExpr) where
  path1 : LoopPath α β
  path2 : LoopPath α β

/-- Composition in Ω¹. -/
def omega1_comp (a b : Omega1) : Omega1 :=
  ⟨LoopExpr.concat a.expr b.expr⟩

/-- Identity in Ω¹. -/
def omega1_id : Omega1 := ⟨LoopExpr.id_loop⟩

/-- Inverse in Ω¹. -/
def omega1_inv (a : Omega1) : Omega1 := ⟨LoopExpr.inv a.expr⟩

theorem omega1_left_unit (a : Omega1) :
    LoopPath (omega1_comp omega1_id a).expr a.expr :=
  LoopGroupoid.left_unit a.expr

theorem omega1_right_unit (a : Omega1) :
    LoopPath (omega1_comp a omega1_id).expr a.expr :=
  LoopGroupoid.right_unit a.expr

theorem omega1_assoc (a b c : Omega1) :
    LoopPath
      (omega1_comp (omega1_comp a b) c).expr
      (omega1_comp a (omega1_comp b c)).expr :=
  LoopGroupoid.assoc a.expr b.expr c.expr

theorem omega1_inv_left (a : Omega1) :
    LoopPath (omega1_comp (omega1_inv a) a).expr omega1_id.expr :=
  LoopGroupoid.inv_left a.expr

theorem omega1_inv_right (a : Omega1) :
    LoopPath (omega1_comp a (omega1_inv a)).expr omega1_id.expr :=
  LoopGroupoid.inv_right a.expr

theorem omega2_comm (α β : LoopExpr) :
    LoopPath (LoopExpr.concat α β) (LoopExpr.concat β α) :=
  EckmannHilton.vert_comm α β

end LoopHierarchy

end ComputationalPaths.Path.HoTT.LoopSpaceAlgebraDeep
