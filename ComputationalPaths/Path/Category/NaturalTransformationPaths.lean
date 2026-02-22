/-
# Natural Transformations as Paths Between Functors (2-Cells)

In a 2-categorical setting, natural transformations are 2-cells between
1-cells (functors).  When functors are modelled as path-preserving maps,
a natural transformation α : F ⟹ G assigns to each object `a` a path
`α.component a : Path (F a) (G a)` satisfying a naturality condition.

Vertical composition of 2-cells is path `trans`; horizontal composition
uses whiskering.  The interchange law follows from proof irrelevance (UIP).

## Key Results

| Definition / Theorem                 | Description                                     |
|-------------------------------------|-------------------------------------------------|
| `PathNatTrans`                      | Natural transformation between path functors    |
| `PathNatTrans.vcomp`               | Vertical composition = trans                     |
| `PathNatTrans.hcomp`               | Horizontal composition via whiskering            |
| `interchange_law`                   | Interchange law for 2-cells                      |
| `vcomp_assoc`                       | Associativity of vertical composition            |
| `id_nat_trans`                      | Identity natural transformation                  |
| `godement_product`                  | Godement calculus via path algebra                |

## References

* Mac Lane, *CWM*, Ch. II §4–5
* Kelly, *Basic Concepts of Enriched Category Theory*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

-- ============================================================
-- §1  Path Natural Transformation
-- ============================================================

/-- A natural transformation between path functors, given as a family
    of paths `component a : Path (F a) (G a)` indexed by objects.
    Naturality says that for any path `p : Path a b`, the two routes
    around the naturality square are equal. -/
structure PathNatTrans {A : Type u} {B : Type v}
    (F G : A → B) where
  /-- Component at each object. -/
  component : (a : A) → Path (F a) (G a)
  /-- Naturality: the two routes around the naturality square agree. -/
  naturality : ∀ {a b : A} (p : Path a b),
    Path.trans (Path.congrArg F p) (component b) =
      Path.trans (component a) (Path.congrArg G p)

namespace PathNatTrans

variable {A : Type u} {B : Type v} {C : Type w}
variable {F G H K : A → B}

-- ============================================================
-- §2  Identity Natural Transformation
-- ============================================================

/-- The identity natural transformation on `F`, with `refl` components. -/
noncomputable def id (F : A → B) : PathNatTrans F F where
  component := fun a => Path.refl (F a)
  naturality := fun p => by simp

/-- Components of the identity natural transformation are refl. -/
@[simp] theorem id_component (F : A → B) (a : A) :
    (PathNatTrans.id F).component a = Path.refl (F a) := rfl

-- ============================================================
-- §3  Vertical Composition = Path Trans
-- ============================================================

/-- Vertical composition of natural transformations: compose componentwise
    via `Path.trans`. -/
noncomputable def vcomp (α : PathNatTrans F G) (β : PathNatTrans G H) :
    PathNatTrans F H where
  component := fun a => Path.trans (α.component a) (β.component a)
  naturality := fun {a b} p => by
    calc Path.trans (Path.congrArg F p) (Path.trans (α.component b) (β.component b))
        = Path.trans (Path.trans (Path.congrArg F p) (α.component b)) (β.component b) :=
            (trans_assoc _ _ _).symm
      _ = Path.trans (Path.trans (α.component a) (Path.congrArg G p)) (β.component b) := by
            rw [α.naturality p]
      _ = Path.trans (α.component a) (Path.trans (Path.congrArg G p) (β.component b)) :=
            trans_assoc _ _ _
      _ = Path.trans (α.component a) (Path.trans (β.component a) (Path.congrArg H p)) := by
            rw [β.naturality p]
      _ = Path.trans (Path.trans (α.component a) (β.component a)) (Path.congrArg H p) :=
            (trans_assoc _ _ _).symm

/-- Vertical composition is associative. -/
theorem vcomp_assoc (α : PathNatTrans F G) (β : PathNatTrans G H)
    (γ : PathNatTrans H K) :
    (vcomp (vcomp α β) γ).component = (vcomp α (vcomp β γ)).component := by
  funext a; simp [vcomp]

/-- Left identity for vertical composition. -/
@[simp] theorem vcomp_id_left (α : PathNatTrans F G) :
    (vcomp (PathNatTrans.id F) α).component = α.component := by
  funext a; simp [vcomp, PathNatTrans.id]

/-- Right identity for vertical composition. -/
@[simp] theorem vcomp_id_right (α : PathNatTrans F G) :
    (vcomp α (PathNatTrans.id G)).component = α.component := by
  funext a; simp [vcomp, PathNatTrans.id]

-- ============================================================
-- §4  Horizontal Composition (Whiskering)
-- ============================================================

/-- Left whiskering: given `J : B → C` and `α : F ⟹ G`, produce
    `J ∘ F ⟹ J ∘ G` by applying `congrArg J` to each component. -/
noncomputable def whiskerLeft (J : B → C) (α : PathNatTrans F G) :
    PathNatTrans (fun a => J (F a)) (fun a => J (G a)) where
  component := fun a => Path.congrArg J (α.component a)
  naturality := fun {a b} p => by
    -- Both sides are paths with the same endpoints; use proof irrelevance
    -- at the path level by showing steps match.
    have nat := α.naturality p
    -- congrArg J (congrArg F p) · congrArg J (α_b) = congrArg J (α_a) · congrArg J (congrArg G p)
    -- follows from: congrArg J distributes over trans, plus naturality of α
    calc Path.trans (Path.congrArg (fun a => J (F a)) p)
            (Path.congrArg J (α.component b))
        = Path.trans (Path.congrArg J (Path.congrArg F p))
            (Path.congrArg J (α.component b)) := by
              rw [congrArg_comp J F]
      _ = Path.congrArg J (Path.trans (Path.congrArg F p) (α.component b)) := by
              rw [congrArg_trans]
      _ = Path.congrArg J (Path.trans (α.component a) (Path.congrArg G p)) := by
              rw [nat]
      _ = Path.trans (Path.congrArg J (α.component a))
            (Path.congrArg J (Path.congrArg G p)) := by
              rw [congrArg_trans]
      _ = Path.trans (Path.congrArg J (α.component a))
            (Path.congrArg (fun a => J (G a)) p) := by
              rw [congrArg_comp J G]

/-- Right whiskering: given `K : C → A` and `α : F ⟹ G`, produce
    `F ∘ K ⟹ G ∘ K`. -/
noncomputable def whiskerRight (α : PathNatTrans F G) (K : C → A) :
    PathNatTrans (fun c => F (K c)) (fun c => G (K c)) where
  component := fun c => α.component (K c)
  naturality := fun {c₁ c₂} p => by
    -- Need: congrArg (F ∘ K) p · α_{K c₂} = α_{K c₁} · congrArg (G ∘ K) p
    -- This follows from naturality of α at congrArg K p, plus congrArg_comp
    have nat := α.naturality (Path.congrArg K p)
    calc Path.trans (Path.congrArg (fun c => F (K c)) p) (α.component (K c₂))
        = Path.trans (Path.congrArg F (Path.congrArg K p)) (α.component (K c₂)) := by
            rw [congrArg_comp F K]
      _ = Path.trans (α.component (K c₁)) (Path.congrArg G (Path.congrArg K p)) := nat
      _ = Path.trans (α.component (K c₁)) (Path.congrArg (fun c => G (K c)) p) := by
            rw [congrArg_comp G K]

/-- Horizontal composition of 2-cells: given `α : F ⟹ G` and
    `β : J ⟹ K` where `J, K : B → C`, form `J∘F ⟹ K∘G`. -/
noncomputable def hcomp {J K : B → C}
    (α : PathNatTrans F G) (β : PathNatTrans J K) :
    PathNatTrans (fun a => J (F a)) (fun a => K (G a)) where
  component := fun a =>
    Path.trans (Path.congrArg J (α.component a)) (β.component (G a))
  naturality := fun {a b} p => by
    -- Direct proof using whiskerLeft naturality and β naturality
    -- Step 1: unfold and reassociate
    calc Path.trans (Path.congrArg (fun a => J (F a)) p)
            (Path.trans (Path.congrArg J (α.component b)) (β.component (G b)))
        = Path.trans (Path.trans (Path.congrArg (fun a => J (F a)) p)
            (Path.congrArg J (α.component b))) (β.component (G b)) := by
              rw [← trans_assoc]
      _ = Path.trans (Path.trans (Path.congrArg J (Path.congrArg F p))
            (Path.congrArg J (α.component b))) (β.component (G b)) := by
              rw [congrArg_comp J F]
      _ = Path.trans (Path.congrArg J (Path.trans (Path.congrArg F p) (α.component b)))
            (β.component (G b)) := by
              rw [congrArg_trans]
      _ = Path.trans (Path.congrArg J (Path.trans (α.component a) (Path.congrArg G p)))
            (β.component (G b)) := by
              rw [α.naturality p]
      _ = Path.trans (Path.trans (Path.congrArg J (α.component a))
            (Path.congrArg J (Path.congrArg G p))) (β.component (G b)) := by
              rw [congrArg_trans]
      _ = Path.trans (Path.congrArg J (α.component a))
            (Path.trans (Path.congrArg J (Path.congrArg G p)) (β.component (G b))) := by
              rw [trans_assoc]
      _ = Path.trans (Path.congrArg J (α.component a))
            (Path.trans (β.component (G a)) (Path.congrArg K (Path.congrArg G p))) := by
              rw [β.naturality (Path.congrArg G p)]
      _ = Path.trans (Path.congrArg J (α.component a))
            (Path.trans (β.component (G a)) (Path.congrArg (fun a => K (G a)) p)) := by
              rw [← congrArg_comp K G]
      _ = Path.trans (Path.trans (Path.congrArg J (α.component a)) (β.component (G a)))
            (Path.congrArg (fun a => K (G a)) p) := by
              rw [← trans_assoc]

-- ============================================================
-- §5  Interchange Law
-- ============================================================

/-- The interchange law: vertical-then-horizontal = horizontal-then-vertical.
    Both sides are paths with the same endpoints; equality follows from
    the path structure. -/
theorem interchange_law {J K L : B → C}
    (α : PathNatTrans F G) (β : PathNatTrans G H)
    (γ : PathNatTrans J K) (δ : PathNatTrans K L) (a : A) :
    (hcomp (vcomp α β) (vcomp γ δ)).component a =
      (vcomp (hcomp α γ) (hcomp β δ)).component a := by
  simp only [hcomp, vcomp]
  -- Both sides build a path from J(F a) to L(H a)
  -- LHS: congrArg J (α_a · β_a) · (γ_{H a} · δ_{H a})
  -- RHS: (congrArg J α_a · γ_{G a}) · (congrArg K β_a · δ_{H a})
  rw [congrArg_trans J (α.component a) (β.component a)]
  -- Now LHS: (congrArg J α_a · congrArg J β_a) · (γ_{H a} · δ_{H a})
  -- Rearrange using associativity and naturality of γ
  rw [← trans_assoc, trans_assoc (Path.congrArg J (α.component a))]
  -- Need: congrArg J β_a · γ_{H a} = γ_{G a} · congrArg K β_a
  -- This is the naturality of γ at β.component a
  have natγ := γ.naturality (β.component a)
  rw [natγ, ← trans_assoc, trans_assoc]

-- ============================================================
-- §6  Godement Product
-- ============================================================

/-- Godement product: the two canonical ways of defining horizontal
    composition agree (naturality of β applied to α.component a). -/
theorem godement_product {J K : B → C}
    (α : PathNatTrans F G) (β : PathNatTrans J K) (a : A) :
    Path.trans (Path.congrArg J (α.component a)) (β.component (G a)) =
    Path.trans (β.component (F a)) (Path.congrArg K (α.component a)) :=
  β.naturality (α.component a)

/-- The two definitions of horizontal composition agree. -/
theorem hcomp_eq_alternative {J K : B → C}
    (α : PathNatTrans F G) (β : PathNatTrans J K) :
    (hcomp α β).component = fun a =>
      Path.trans (β.component (F a)) (Path.congrArg K (α.component a)) := by
  funext a; exact godement_product α β a

-- ============================================================
-- §7  2-Cell Coherence Theorems
-- ============================================================

/-- Any two natural transformations with the same components are equal. -/
theorem ext (α β : PathNatTrans F G) (h : α.component = β.component) :
    α = β := by
  cases α; cases β; simp at h; subst h; rfl

/-- Vertical composition of identity gives identity. -/
theorem vcomp_id_id (F : A → B) :
    (vcomp (PathNatTrans.id F) (PathNatTrans.id F)).component =
      (PathNatTrans.id F).component := by
  funext a; simp [vcomp, PathNatTrans.id]

/-- Right whiskering by identity preserves components. -/
@[simp] theorem whiskerRight_id_component (α : PathNatTrans F G) (a : A) :
    (whiskerRight α (fun x : A => x)).component a = α.component a := rfl

/-- Whiskering preserves vertical composition (components agree). -/
theorem whiskerLeft_vcomp (J : B → C)
    (α : PathNatTrans F G) (β : PathNatTrans G H) :
    (whiskerLeft J (vcomp α β)).component =
      (vcomp (whiskerLeft J α) (whiskerLeft J β)).component := by
  funext a; simp only [whiskerLeft, vcomp]; rw [congrArg_trans]

/-- Whiskering right preserves vertical composition. -/
theorem whiskerRight_vcomp (L : C → A)
    (α : PathNatTrans F G) (β : PathNatTrans G H) :
    (whiskerRight (vcomp α β) L).component =
      (vcomp (whiskerRight α L) (whiskerRight β L)).component := by
  funext c; simp [whiskerRight, vcomp]

/-- Inverse natural transformation: given `α : F ⟹ G`, form `G ⟹ F`.
    The naturality condition holds at the proof level (by UIP). -/
theorem inverse_naturality_proof (α : PathNatTrans F G) {a b : A} (p : Path a b) :
    (Path.trans (Path.congrArg G p) (Path.symm (α.component b))).proof =
    (Path.trans (Path.symm (α.component a)) (Path.congrArg F p)).proof :=
  Subsingleton.elim _ _

/-- The inverse components satisfy the cancellation law. -/
theorem inverse_cancel_toEq (α : PathNatTrans F G) (a : A) :
    (Path.trans (α.component a) (Path.symm (α.component a))).toEq = rfl := by
  simp

/-- The inverse components satisfy the left cancellation law. -/
theorem inverse_cancel_left_toEq (α : PathNatTrans F G) (a : A) :
    (Path.trans (Path.symm (α.component a)) (α.component a)).toEq = rfl := by
  simp

/-- Left inverse for vertical composition (toEq level). -/
theorem vcomp_symm_component_toEq (α : PathNatTrans F G) (a : A) :
    (Path.trans (α.component a) (Path.symm (α.component a))).toEq = rfl := by
  simp

/-- Right inverse for vertical composition (toEq level). -/
theorem symm_vcomp_component_toEq (α : PathNatTrans F G) (a : A) :
    (Path.trans (Path.symm (α.component a)) (α.component a)).toEq = rfl := by
  simp

/-- Vertical composition with inverse yields refl proof. -/
theorem vcomp_symm_component_proof (α : PathNatTrans F G) (a : A) :
    (Path.trans (α.component a) (Path.symm (α.component a))).proof = rfl := by
  simp

/-- The interchange law at the level of underlying proofs always holds. -/
theorem interchange_toEq {J K L : B → C}
    (α : PathNatTrans F G) (β : PathNatTrans G H)
    (γ : PathNatTrans J K) (δ : PathNatTrans K L) (a : A) :
    ((hcomp (vcomp α β) (vcomp γ δ)).component a).toEq =
      ((vcomp (hcomp α γ) (hcomp β δ)).component a).toEq :=
  Subsingleton.elim _ _

end PathNatTrans

end ComputationalPaths
