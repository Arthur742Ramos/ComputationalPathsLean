/-
# Homotopy Pushouts

Homotopy pushouts, cofiber sequences, Mayer-Vietoris for homotopy groups,
Seifert-van Kampen for higher groups, and descent / flattening lemma.
Proofs are stubbed with `sorry`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace HomotopyPushout

open ComputationalPaths

universe u v w

/-! ## Homotopy pushout -/

/-- Homotopy pushout (double mapping cylinder). -/
inductive HPushout {A B C : Type u} (f : C → A) (g : C → B) : Type u where
  | inl  : A → HPushout f g
  | inr  : B → HPushout f g
  | glue : (c : C) → inl (f c) = inr (g c)

/-- Cofiber (mapping cone) of a map f : A → B. -/
def Cofiber {A B : Type u} (f : A → B) : Type u :=
  HPushout f (fun _ : A => PUnit.unit)

/-- Wedge sum A ∨ B. -/
def Wedge (A B : Type u) (a₀ : A) (b₀ : B) : Type u :=
  HPushout (fun _ : Unit => a₀) (fun _ : Unit => b₀)

/-- Join A * B as a pushout. -/
def Join (A B : Type u) : Type u :=
  HPushout (fun (p : A × B) => p.1) (fun (p : A × B) => p.2)

/-- Pushout recursion principle. -/
def HPushout.rec' {A B C : Type u} {f : C → A} {g : C → B}
    {D : Type v}
    (h₁ : A → D) (h₂ : B → D)
    (h₃ : (c : C) → h₁ (f c) = h₂ (g c)) :
    HPushout f g → D := sorry

/-- Pushout induction principle. -/
def HPushout.ind' {A B C : Type u} {f : C → A} {g : C → B}
    {P : HPushout f g → Type v}
    (h₁ : (a : A) → P (HPushout.inl a))
    (h₂ : (b : B) → P (HPushout.inr b))
    (h₃ : (c : C) → (HPushout.glue c) ▸ h₁ (f c) = h₂ (g c)) :
    (x : HPushout f g) → P x := sorry

/-- Pushout of pointed maps. -/
structure PointedPushout (A B C : Type u) (a₀ : A) (b₀ : B)
    (f : C → A) (g : C → B) where
  pushout : HPushout f g
  -- base point is inl a₀

/-! ## Cofiber sequence -/

/-- The cofiber inclusion. -/
def cofiberInclusion {A B : Type u} (f : A → B) :
    B → Cofiber f :=
  fun b => HPushout.inl b

/-- The cofiber projection to the suspension. -/
def cofiberProjection {A B : Type u} (f : A → B) :
    Cofiber f → Cofiber (fun _ : B => PUnit.unit) := sorry

/-- The connecting map in the cofiber sequence. -/
def connectingMap {A B : Type u} (f : A → B) :
    Cofiber f → Cofiber (cofiberInclusion f) := sorry

/-! ## Mayer-Vietoris -/

/-- Synthetic homotopy group (placeholder). -/
def π (n : Nat) (A : Type u) (a₀ : A) : Type u := sorry

/-- The Mayer-Vietoris connecting homomorphism. -/
def mvConnecting {A B C : Type u} (f : C → A) (g : C → B)
    (n : Nat) (x₀ : HPushout f g) :
    π (n + 1) (HPushout f g) x₀ → π n C sorry := sorry

/-- Mayer-Vietoris exact sequence data. -/
structure MVExactData {A B C : Type u} (f : C → A) (g : C → B) (n : Nat) where
  mapA : π n A sorry → π n (HPushout f g) sorry
  mapB : π n B sorry → π n (HPushout f g) sorry
  mapC : π n C sorry → π n A sorry × π n B sorry
  connecting : π (n + 1) (HPushout f g) sorry → π n C sorry

/-! ## Seifert-van Kampen -/

/-- A group (simplified for HIT purposes). -/
structure HGroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier

/-- Free product of groups. -/
def FreeProduct (G H : HGroup) : HGroup := sorry

/-- Amalgamated free product G *_K H. -/
def AmalgamatedProduct (G H K : HGroup)
    (φ : K.carrier → G.carrier) (ψ : K.carrier → H.carrier) : HGroup := sorry

/-- Fundamental group of a pushout. -/
def π₁Pushout {A B C : Type u} (f : C → A) (g : C → B) :
    HGroup := sorry

/-! ## Descent / Flattening -/

/-- A type family over a pushout. -/
structure PushoutFamily {A B C : Type u} (f : C → A) (g : C → B) where
  famA : A → Type v
  famB : B → Type v
  famGlue : (c : C) → famA (f c) ≃ famB (g c)

/-- The total space of a family over a pushout. -/
def pushoutTotalSpace {A B C : Type u} {f : C → A} {g : C → B}
    (F : PushoutFamily f g) : Type (max u v) := sorry

/-- The flattening lemma: total space is itself a pushout. -/
def flatteningLemma {A B C : Type u} {f : C → A} {g : C → B}
    (F : @PushoutFamily u v A B C f g) :
    pushoutTotalSpace F ≃
    HPushout (fun (p : Σ c, F.famA (f c)) => ⟨f p.1, p.2⟩)
             (fun (p : Σ c, F.famA (f c)) => ⟨g p.1, (F.famGlue p.1) p.2⟩) := sorry

/-! ## Theorems -/

/-- Pushout of id and f along C computes as a mapping cylinder. -/
theorem pushout_mapping_cylinder {A B : Type u} (f : A → B) :
    HPushout f (@id A) ≃ B := sorry

/-- Cofiber of the inclusion of a point is the suspension. -/
theorem cofiber_point_susp {A : Type u} (a₀ : A) :
    Cofiber (fun _ : Unit => a₀) ≃ sorry := sorry

/-- Join is symmetric. -/
theorem join_symm (A B : Type u) : Join A B ≃ Join B A := sorry

/-- Join with Unit is the cone (contractible). -/
theorem join_unit (A : Type u) : Nonempty (Join A Unit) := sorry

/-- Mayer-Vietoris: exactness at the A × B term. -/
theorem mv_exact_AB {A B C : Type u} (f : C → A) (g : C → B) (n : Nat) :
    ∀ (x : π n A sorry × π n B sorry),
    (MVExactData.mk (f := f) (g := g) (n := n) sorry sorry sorry sorry).mapA x.1 =
    (MVExactData.mk (f := f) (g := g) (n := n) sorry sorry sorry sorry).mapB x.2 →
    ∃ c, (MVExactData.mk (f := f) (g := g) (n := n) sorry sorry sorry sorry).mapC c = x := sorry

/-- Seifert-van Kampen: π₁ of a pushout is the amalgamated free product. -/
theorem svk {A B C : Type u} (f : C → A) (g : C → B) :
    (π₁Pushout f g).carrier ≃
    (AmalgamatedProduct sorry sorry sorry sorry sorry).carrier := sorry

/-- The cofiber sequence is exact. -/
theorem cofiber_exact {A B : Type u} (f : A → B) (n : Nat) :
    True := sorry -- exactness statement

/-- Pushout preserves equivalences in the left leg. -/
theorem pushout_equiv_left {A A' B C : Type u}
    (f : C → A) (g : C → B) (e : A ≃ A') :
    HPushout f g ≃ HPushout (e ∘ f) g := sorry

/-- Pushout preserves equivalences in the right leg. -/
theorem pushout_equiv_right {A B B' C : Type u}
    (f : C → A) (g : C → B) (e : B ≃ B') :
    HPushout f g ≃ HPushout f (e ∘ g) := sorry

/-- Pushout is symmetric. -/
theorem pushout_symm {A B C : Type u} (f : C → A) (g : C → B) :
    HPushout f g ≃ HPushout g f := sorry

/-- Pushout along an equivalence is the codomain. -/
theorem pushout_along_equiv {A B C : Type u} (f : C → A) (g : C → B)
    (hf : Function.Bijective f) :
    HPushout f g ≃ B := sorry

/-- Flattening lemma specialised to constant families. -/
theorem flattening_const {A B C : Type u} (f : C → A) (g : C → B)
    (F : Type u) :
    True := sorry -- pushoutTotalSpace of const ≃ pushout × F

/-- Wedge inclusion into product. -/
theorem wedge_into_product (A B : Type u) (a₀ : A) (b₀ : B) :
    (Wedge A B a₀ b₀ → A × B) := sorry

/-- Iterated cofiber is a shift in the cofiber sequence. -/
theorem cofiber_shift {A B : Type u} (f : A → B) :
    Cofiber (cofiberInclusion f) ≃ sorry := sorry

/-- Descent: fibrations over a pushout are determined by descent data. -/
theorem descent_pushout {A B C : Type u} (f : C → A) (g : C → B) :
    (HPushout f g → Type u) ≃
    Σ (FA : A → Type u) (FB : B → Type u), (c : C) → FA (f c) ≃ FB (g c) := sorry

end HomotopyPushout
end ComputationalPaths
