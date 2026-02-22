/-
# Universal properties of path spaces

Product paths, sum paths, function extensionality, universal property
of path spaces, and pullback as path-based fiber product.
All built on the computational-path infrastructure from `Path.Basic.Core`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

/-! ## Product paths: (a,b) = (a',b') ↔ (a = a') × (b = b') -/

namespace ProdPath

variable {A : Type u} {B : Type v}

/-- Split a product equality into component equalities. -/
noncomputable def projEqs {p₁ p₂ : A × B} (h : p₁ = p₂) :
    p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 := by
  cases h; exact ⟨rfl, rfl⟩

/-- Build a product equality from component equalities. -/
noncomputable def mkEq {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    ((a₁, b₁) : A × B) = (a₂, b₂) := by
  cases ha; cases hb; rfl

/-- Build a product equality from component paths. -/
noncomputable def mkPath {a₁ a₂ : A} {b₁ b₂ : B}
    (pa : Path a₁ a₂) (pb : Path b₁ b₂) :
    ((a₁, b₁) : A × B) = (a₂, b₂) :=
  mkEq pa.toEq pb.toEq

/-- Round-trip: projEqs ∘ mkEq. -/
theorem projEqs_mkEq {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    projEqs (mkEq ha hb) = ⟨ha, hb⟩ := by
  cases ha; cases hb; rfl

/-- Product extensionality. -/
theorem prod_ext {a₁ a₂ : A} {b₁ b₂ : B} :
    ((a₁, b₁) : A × B) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) := by
  constructor
  · intro h; exact projEqs h
  · intro ⟨ha, hb⟩; exact mkEq ha hb

/-- mkEq with rfl is rfl. -/
@[simp] theorem mkEq_rfl (a : A) (b : B) :
    mkEq (rfl : a = a) (rfl : b = b) = rfl := rfl

/-- mkEq respects transitivity. -/
theorem mkEq_trans {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha₁ : a₁ = a₂) (ha₂ : a₂ = a₃)
    (hb₁ : b₁ = b₂) (hb₂ : b₂ = b₃) :
    (mkEq ha₁ hb₁).trans (mkEq ha₂ hb₂) =
      mkEq (ha₁.trans ha₂) (hb₁.trans hb₂) := by
  cases ha₁; cases ha₂; cases hb₁; cases hb₂; rfl

/-- mkEq respects symmetry. -/
theorem mkEq_symm {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (mkEq ha hb).symm = mkEq ha.symm hb.symm := by
  cases ha; cases hb; rfl

/-- First projection of projEqs. -/
theorem projEqs_fst {p₁ p₂ : A × B} (h : p₁ = p₂) :
    (projEqs h).1 = congrArg Prod.fst h := by
  cases h; rfl

/-- Second projection of projEqs. -/
theorem projEqs_snd {p₁ p₂ : A × B} (h : p₁ = p₂) :
    (projEqs h).2 = congrArg Prod.snd h := by
  cases h; rfl

/-- Pair constructor is injective. -/
theorem pair_injective {a₁ a₂ : A} {b₁ b₂ : B}
    (h : (a₁, b₁) = (a₂, b₂)) : a₁ = a₂ ∧ b₁ = b₂ :=
  projEqs h

/-- congrArg fst of mkEq. -/
theorem congrArg_fst_mkEq {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    congrArg Prod.fst (mkEq ha hb) = ha := by
  cases ha; cases hb; rfl

/-- congrArg snd of mkEq. -/
theorem congrArg_snd_mkEq {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    congrArg Prod.snd (mkEq ha hb) = hb := by
  cases ha; cases hb; rfl

end ProdPath

/-! ## Sum paths: classification of paths in coproducts -/

namespace SumPath

variable {A : Type u} {B : Type v}

/-- Paths in `Sum.inl` reduce to paths in `A`. -/
noncomputable def inl_path {a₁ a₂ : A} (h : (Sum.inl a₁ : A ⊕ B) = Sum.inl a₂) :
    a₁ = a₂ :=
  Sum.inl.inj h

/-- Paths in `Sum.inr` reduce to paths in `B`. -/
noncomputable def inr_path {b₁ b₂ : B} (h : (Sum.inr b₁ : A ⊕ B) = Sum.inr b₂) :
    b₁ = b₂ :=
  Sum.inr.inj h

/-- `Sum.inl` is injective as equality. -/
theorem inl_eq {a₁ a₂ : A} (h : a₁ = a₂) :
    (Sum.inl a₁ : A ⊕ B) = Sum.inl a₂ :=
  congrArg Sum.inl h

/-- `Sum.inr` is injective as equality. -/
theorem inr_eq {b₁ b₂ : B} (h : b₁ = b₂) :
    (Sum.inr b₁ : A ⊕ B) = Sum.inr b₂ :=
  congrArg Sum.inr h

/-- `inl ≠ inr` -/
theorem inl_ne_inr (a : A) (b : B) :
    (Sum.inl a : A ⊕ B) ≠ Sum.inr b :=
  Sum.noConfusion

/-- `inr ≠ inl` -/
theorem inr_ne_inl (b : B) (a : A) :
    (Sum.inr b : A ⊕ B) ≠ Sum.inl a :=
  fun h => Sum.noConfusion h

/-- Round-trip for inl paths. -/
theorem inl_path_roundtrip {a₁ a₂ : A} (h : a₁ = a₂) :
    inl_path (inl_eq (B := B) h) = h := by
  cases h; rfl

/-- Round-trip for inr paths. -/
theorem inr_path_roundtrip {b₁ b₂ : B} (h : b₁ = b₂) :
    inr_path (inr_eq (A := A) h) = h := by
  cases h; rfl

/-- Classification: every equality in a sum type lives in one component. -/
theorem classification (x y : A ⊕ B) (h : x = y) :
    (∃ a₁ a₂ : A, x = Sum.inl a₁ ∧ y = Sum.inl a₂) ∨
    (∃ b₁ b₂ : B, x = Sum.inr b₁ ∧ y = Sum.inr b₂) := by
  cases h; cases x with
  | inl a => exact Or.inl ⟨a, a, rfl, rfl⟩
  | inr b => exact Or.inr ⟨b, b, rfl, rfl⟩

/-- inl is injective. -/
theorem inl_injective : Function.Injective (Sum.inl : A → A ⊕ B) :=
  fun _ _ h => Sum.inl.inj h

/-- inr is injective. -/
theorem inr_injective : Function.Injective (Sum.inr : B → A ⊕ B) :=
  fun _ _ h => Sum.inr.inj h

end SumPath

/-! ## Function extensionality as path principle -/

namespace FunExtPath

variable {A : Type u} {B : Type v}

/-- Function extensionality: pointwise paths give a path between functions. -/
noncomputable def funext {f g : A → B} (h : ∀ x, Path (f x) (g x)) :
    Path f g :=
  Path.mk [Step.mk _ _ (_root_.funext (fun x => (h x).toEq))]
    (_root_.funext (fun x => (h x).toEq))

/-- Pointwise extraction from a function path. -/
noncomputable def happly {f g : A → B} (p : Path f g) (x : A) :
    Path (f x) (g x) :=
  Path.congrArg (fun h => h x) p

/-- Round-trip: happly ∘ funext is pointwise identity at toEq level. -/
theorem happly_funext_toEq {f g : A → B} (h : ∀ x, Path (f x) (g x)) (x : A) :
    (happly (funext h) x).toEq = (h x).toEq := by
  simp [happly, funext]

/-- Round-trip: funext ∘ happly = id at toEq level. -/
theorem funext_happly_toEq {f g : A → B} (p : Path f g) :
    (funext (happly p)).toEq = p.toEq := by
  cases p with | mk s h => cases h; simp [funext, happly]

/-- `funext` on reflexive paths yields a path with `toEq = rfl`. -/
@[simp] theorem funext_refl (f : A → B) :
    (funext (fun x => Path.refl (f x))).toEq = rfl := by
  simp [funext]

/-- `funext` respects symmetry at toEq level. -/
theorem funext_symm {f g : A → B} (h : ∀ x, Path (f x) (g x)) :
    (funext (fun x => Path.symm (h x))).toEq =
      (funext h).toEq.symm := by
  simp [funext]

/-- `funext` respects transitivity at toEq level. -/
theorem funext_trans {f g k : A → B}
    (h₁ : ∀ x, Path (f x) (g x)) (h₂ : ∀ x, Path (g x) (k x)) :
    (funext (fun x => Path.trans (h₁ x) (h₂ x))).toEq =
      ((funext h₁).toEq.trans (funext h₂).toEq) := by
  simp [funext]

/-- Dependent function extensionality. -/
noncomputable def dfunext {C : A → Type v} {f g : ∀ x, C x}
    (h : ∀ x, Path (f x) (g x)) : Path f g :=
  Path.mk [Step.mk _ _ (_root_.funext (fun x => (h x).toEq))]
    (_root_.funext (fun x => (h x).toEq))

/-- Pointwise extraction from dependent function path. -/
noncomputable def dhapply {C : A → Type v} {f g : ∀ x, C x}
    (p : Path f g) (x : A) : f x = g x :=
  congrFun p.toEq x

@[simp] theorem dfunext_refl {C : A → Type v} (f : ∀ x, C x) :
    (dfunext (fun x => Path.refl (f x))).toEq = rfl := by
  simp [dfunext]

end FunExtPath

/-! ## Universal property of path spaces -/

namespace PathUniversal

variable {A : Type u} {a b : A}

/-- The path space maps to Eq via toEq. -/
noncomputable def pathToEq : Path a b → (a = b) := Path.toEq

/-- Eq maps to path space via ofEq. -/
noncomputable def eqToPath : (a = b) → Path a b := fun h => Path.mk [Step.mk _ _ h] h

@[simp] theorem pathToEq_eqToPath (h : a = b) :
    pathToEq (eqToPath h) = h := rfl

@[simp] theorem eqToPath_pathToEq (p : Path a b) :
    (eqToPath (pathToEq p)).toEq = p.toEq := rfl

/-- Two paths with the same toEq have equal proofs (proof field). -/
theorem toEq_determines {p q : Path a b} :
    p.toEq = q.toEq := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-- Based path space: the toEq projection is always rfl after cases. -/
theorem based_path_toEq_eq (p : Path a a) : p.toEq = rfl := by
  cases p with | mk s h => cases h; rfl

/-- Path induction on the propositional content: to prove `C (p.toEq)`
for all `p`, it suffices to prove `C rfl`. -/
theorem eq_ind {C : (a = b) → Prop}
    (h : ∀ (p : Path a b), C p.toEq) (e : a = b) : C e := by
  exact h (Path.mk [Step.mk _ _ e] e)

/-- Uniqueness of identity proofs for Path.toEq. -/
theorem toEq_unique (p q : Path a b) : p.toEq = q.toEq := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

/-- The semantic content (toEq) of any path equals any Eq proof. -/
theorem toEq_eq_proof (p : Path a b) (h : a = b) : p.toEq = h :=
  Subsingleton.elim _ _

/-- Transport along a path via ofEq round-trips. -/
theorem transport_ofEq_roundtrip {C : A → Type v} (h : a = b) (x : C a) :
    Path.transport (D := C) (Path.mk [Step.mk _ _ h] h) x = h ▸ x := by
  cases h; rfl

end PathUniversal

/-! ## Pullback as path-based fiber product -/

namespace PullbackPath

variable {A : Type u} {B : Type v} {C : Type w}

/-- The pullback (fiber product) of `f : A → C` and `g : B → C`:
pairs `(a, b)` with a witness that `f a = g b`. -/
structure Pullback (f : A → C) (g : B → C) where
  fst : A
  snd : B
  comm : f fst = g snd

variable {f : A → C} {g : B → C}

/-- Two pullback elements are equal when their components agree. -/
theorem ext {p q : Pullback f g}
    (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) :
    p = q := by
  cases p; cases q; simp at h₁ h₂; cases h₁; cases h₂; rfl

/-- Projection to the first component. -/
noncomputable def pr₁ (p : Pullback f g) : A := p.fst

/-- Projection to the second component. -/
noncomputable def pr₂ (p : Pullback f g) : B := p.snd

/-- The pullback square commutes. -/
theorem commutes (p : Pullback f g) : f (pr₁ p) = g (pr₂ p) :=
  p.comm

/-- Universal property: any cone factors through the pullback. -/
noncomputable def universal {D : Type u}
    (d₁ : D → A) (d₂ : D → B) (comm : ∀ x, f (d₁ x) = g (d₂ x))
    (x : D) : Pullback f g :=
  ⟨d₁ x, d₂ x, comm x⟩

/-- The universal map respects the first projection. -/
@[simp] theorem universal_pr₁ {D : Type u}
    (d₁ : D → A) (d₂ : D → B) (comm : ∀ x, f (d₁ x) = g (d₂ x))
    (x : D) : pr₁ (universal d₁ d₂ comm x) = d₁ x := rfl

/-- The universal map respects the second projection. -/
@[simp] theorem universal_pr₂ {D : Type u}
    (d₁ : D → A) (d₂ : D → B) (comm : ∀ x, f (d₁ x) = g (d₂ x))
    (x : D) : pr₂ (universal d₁ d₂ comm x) = d₂ x := rfl

/-- Uniqueness of the universal map. -/
theorem universal_unique {D : Type u}
    (d₁ : D → A) (d₂ : D → B) (comm : ∀ x, f (d₁ x) = g (d₂ x))
    (u : D → Pullback f g)
    (h₁ : ∀ x, pr₁ (u x) = d₁ x)
    (h₂ : ∀ x, pr₂ (u x) = d₂ x)
    (x : D) : u x = universal d₁ d₂ comm x :=
  ext (h₁ x) (h₂ x)

/-- Pullback of identity functions: f = g = id gives the diagonal. -/
theorem pullback_id_ext (p : Pullback (id : A → A) (id : A → A)) :
    p.fst = p.snd :=
  p.comm

end PullbackPath

end ComputationalPaths
