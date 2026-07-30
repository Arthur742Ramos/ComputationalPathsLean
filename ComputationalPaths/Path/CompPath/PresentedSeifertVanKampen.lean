/-
# Seifert--van Kampen for presented computational path spaces

This module defines the raw one-vertex path presentation associated with two
group-like components and an amalgamating map.  The construction is independent
of normalization:

* left and right elements are proof-relevant generating edges;
* named relators encode component multiplication, units, inverses, and
  amalgamation;
* arbitrary raw paths are freely built using reflexivity, reversal, and
  composition;
* homotopy is generated from the named relators and the groupoid laws.

Only after this path space has been defined do we construct encode and decode.
The main theorem identifies its fundamental group with
`FullAmalgamatedFreeProduct`.  The figure-eight specialization uses two integer
components with trivial amalgamation.
-/

import ComputationalPaths.Path.CompPath.CirclePresented
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Homotopy.PresentedFundamentalGroup

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace PresentedSeifertVanKampen

open Presented

universe u

/-- The group laws required from a component operation.  They are explicit
rather than hidden in a global algebraic typeclass. -/
structure GroupLaws (G : Type u) [Add G] [Zero G] [Neg G] : Prop where
  add_assoc : ∀ x y z : G, (x + y) + z = x + (y + z)
  zero_add : ∀ x : G, 0 + x = x
  add_zero : ∀ x : G, x + 0 = x
  neg_add_rev : ∀ x y : G, -(x + y) = (-y) + (-x)
  neg_zero : -(0 : G) = 0
  neg_add : ∀ x : G, (-x) + x = 0
  add_neg : ∀ x : G, x + (-x) = 0
  neg_neg : ∀ x : G, -(-x) = x

/-- An amalgamating map preserves the displayed group operations. -/
structure PreservesGroupOps {H G : Type u}
    [Add H] [Zero H] [Neg H] [Add G] [Zero G] [Neg G]
    (i : H → G) : Prop where
  map_add : ∀ x y : H, i (x + y) = i x + i y
  map_zero : i 0 = 0
  map_neg : ∀ h : H, -(i h) = i (-h)

/-- Group laws on the amalgamating type together with two group-homomorphism
certificates. -/
structure AmalgamationLaws
    {H G₁ G₂ : Type u}
    [Add H] [Zero H] [Neg H]
    [Add G₁] [Zero G₁] [Neg G₁]
    [Add G₂] [Zero G₂] [Neg G₂]
    (i₁ : H → G₁) (i₂ : H → G₂) : Prop where
  source_laws : GroupLaws H
  left_hom : PreservesGroupOps i₁
  right_hom : PreservesGroupOps i₂

section Presentation

variable {G₁ G₂ H : Type u}
variable [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
variable [Neg G₁] [Neg G₂]
variable (i₁ : H → G₁) (i₂ : H → G₂)

/-- Left and right component elements as generating edges at one vertex. -/
inductive Edge : Unit → Unit → Type u where
  | left (x : G₁) : Edge () ()
  | right (y : G₂) : Edge () ()

/-- Generator graph of the amalgamated path presentation. -/
def graph : Presented.Graph where
  Point := Unit
  Edge := Edge (G₁ := G₁) (G₂ := G₂)

/-- Raw left component edge. -/
def rawLeft (x : G₁) :
    Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) () () :=
  Presented.RawPath.edge (Edge.left x)

/-- Raw right component edge. -/
def rawRight (y : G₂) :
    Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) () () :=
  Presented.RawPath.edge (Edge.right y)

/-- Named relators of the amalgamated one-vertex path presentation. -/
inductive Relator :
    {a b : (graph (G₁ := G₁) (G₂ := G₂)).Point} →
    Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b →
    Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b → Prop where
  | left_add (x y : G₁) :
      Relator
        (Presented.RawPath.trans (rawLeft x) (rawLeft y))
        (rawLeft (x + y))
  | right_add (x y : G₂) :
      Relator
        (Presented.RawPath.trans (rawRight x) (rawRight y))
        (rawRight (x + y))
  | left_zero :
      Relator (rawLeft (0 : G₁))
        (@Presented.RawPath.refl
          (graph (G₁ := G₁) (G₂ := G₂)) ())
  | right_zero :
      Relator (rawRight (0 : G₂))
        (@Presented.RawPath.refl
          (graph (G₁ := G₁) (G₂ := G₂)) ())
  | left_neg (x : G₁) :
      Relator (Presented.RawPath.symm (rawLeft x)) (rawLeft (-x))
  | right_neg (y : G₂) :
      Relator (Presented.RawPath.symm (rawRight y)) (rawRight (-y))
  | amalg (h : H) :
      Relator (rawLeft (i₁ h)) (rawRight (i₂ h))

/-- The raw amalgamated path presentation. -/
def presentation :
    Presented.Presentation (graph (G₁ := G₁) (G₂ := G₂)) where
  Relator := Relator i₁ i₂

/-- Full amalgamated target of the presentation. -/
abbrev Target : Type u :=
  FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂

section Encoding

variable [Add H] [Zero H] [Neg H]
variable (L₁ : GroupLaws G₁) (L₂ : GroupLaws G₂)
variable (M₁ : PreservesGroupOps i₁) (M₂ : PreservesGroupOps i₂)

/-- Inversion in the full amalgamated target. -/
noncomputable def targetInv : Target i₁ i₂ → Target i₁ i₂ :=
  FullAmalgamatedFreeProduct.inv
    M₁.map_neg M₂.map_neg
    L₁.neg_add_rev L₂.neg_add_rev
    L₁.neg_zero L₂.neg_zero

/-- The target inverse is involutive. -/
theorem targetInv_involutive (x : Target i₁ i₂) :
    targetInv i₁ i₂ L₁ L₂ M₁ M₂
      (targetInv i₁ i₂ L₁ L₂ M₁ M₂ x) = x := by
  induction x using Quot.ind with
  | _ w =>
      change
        FullAmalgamatedFreeProduct.ofWord
            (FreeProductWord.inverse (FreeProductWord.inverse w)) =
          FullAmalgamatedFreeProduct.ofWord w
      rw [FreeProductWord.inverse_inverse L₁.neg_neg L₂.neg_neg]

@[simp] theorem targetInv_one :
    targetInv i₁ i₂ L₁ L₂ M₁ M₂
      (FullAmalgamatedFreeProduct.one : Target i₁ i₂) =
      FullAmalgamatedFreeProduct.one := by
  rfl

theorem targetInv_mul (x y : Target i₁ i₂) :
    targetInv i₁ i₂ L₁ L₂ M₁ M₂
        (FullAmalgamatedFreeProduct.mul x y) =
      FullAmalgamatedFreeProduct.mul
        (targetInv i₁ i₂ L₁ L₂ M₁ M₂ y)
        (targetInv i₁ i₂ L₁ L₂ M₁ M₂ x) := by
  induction x using Quot.ind with
  | _ w₁ =>
      induction y using Quot.ind with
      | _ w₂ =>
          change
            FullAmalgamatedFreeProduct.ofWord
                (FreeProductWord.inverse
                  (FreeProductWord.concat w₁ w₂)) =
              FullAmalgamatedFreeProduct.ofWord
                (FreeProductWord.concat
                  (FreeProductWord.inverse w₂)
                  (FreeProductWord.inverse w₁))
          rw [FreeProductWord.inverse_concat]

/-- Encode a raw presented path in the full amalgamated target. -/
noncomputable def encodeRaw :
    {a b : (graph (G₁ := G₁) (G₂ := G₂)).Point} →
    Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b →
      Target i₁ i₂
  | _, _, .refl _ => FullAmalgamatedFreeProduct.one
  | _, _, .edge (.left x) =>
      FullAmalgamatedFreeProduct.ofWord (FreeProductWord.singleLeft x)
  | _, _, .edge (.right y) =>
      FullAmalgamatedFreeProduct.ofWord (FreeProductWord.singleRight y)
  | _, _, .symm p =>
      targetInv i₁ i₂ L₁ L₂ M₁ M₂
        (encodeRaw p)
  | _, _, .trans p q =>
      FullAmalgamatedFreeProduct.mul
        (encodeRaw p)
        (encodeRaw q)

private theorem binary_congr {α β γ : Type u} (f : α → β → γ)
    {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := by
  cases ha
  cases hb
  rfl

/-- Every named relator has the same image in the full amalgamated target. -/
theorem relator_encode
    {a b : (graph (G₁ := G₁) (G₂ := G₂)).Point}
    {p q : Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b}
    (h : Relator i₁ i₂ p q) :
    encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p =
      encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ q := by
  cases h with
  | left_add x y =>
      have hq :
          (FullAmalgamatedFreeProduct.ofWord
              (FreeProductWord.consLeft x
                (FreeProductWord.consLeft y .nil)) :
            Target i₁ i₂) =
            FullAmalgamatedFreeProduct.ofWord
              (FreeProductWord.singleLeft (x + y)) :=
        Quot.sound (FullAmalgEquiv.freeGroup
          (FreeProductWord.FreeGroupStep.combineLeft x y .nil))
      simpa [encodeRaw, rawLeft, FreeProductWord.singleLeft,
        FullAmalgamatedFreeProduct.mul,
        FullAmalgamatedFreeProduct.mulWordRight] using hq
  | right_add x y =>
      have hq :
          (FullAmalgamatedFreeProduct.ofWord
              (FreeProductWord.consRight x
                (FreeProductWord.consRight y .nil)) :
            Target i₁ i₂) =
            FullAmalgamatedFreeProduct.ofWord
              (FreeProductWord.singleRight (x + y)) :=
        Quot.sound (FullAmalgEquiv.freeGroup
          (FreeProductWord.FreeGroupStep.combineRight x y .nil))
      simpa [encodeRaw, rawRight, FreeProductWord.singleRight,
        FullAmalgamatedFreeProduct.mul,
        FullAmalgamatedFreeProduct.mulWordRight] using hq
  | left_zero =>
      change
        FullAmalgamatedFreeProduct.ofWord
            (FreeProductWord.singleLeft (0 : G₁)) =
          FullAmalgamatedFreeProduct.one
      apply Quot.sound
      exact FullAmalgEquiv.freeGroup
        (FreeProductWord.FreeGroupStep.removeLeftZero .nil)
  | right_zero =>
      change
        FullAmalgamatedFreeProduct.ofWord
            (FreeProductWord.singleRight (0 : G₂)) =
          FullAmalgamatedFreeProduct.one
      apply Quot.sound
      exact FullAmalgEquiv.freeGroup
        (FreeProductWord.FreeGroupStep.removeRightZero .nil)
  | left_neg x =>
      simp [encodeRaw, rawLeft, targetInv,
        FullAmalgamatedFreeProduct.inv,
        FullAmalgamatedFreeProduct.ofWord,
        FreeProductWord.singleLeft, FreeProductWord.inverse]
  | right_neg y =>
      simp [encodeRaw, rawRight, targetInv,
        FullAmalgamatedFreeProduct.inv,
        FullAmalgamatedFreeProduct.ofWord,
        FreeProductWord.singleRight, FreeProductWord.inverse]
  | amalg h =>
      apply Quot.sound
      simpa using
        (FullAmalgEquiv.amalg
          (AmalgRelation.amalgLeftToRight h .nil .nil))

/-- Generated presented homotopy is sound for the full amalgamated target. -/
theorem homotopy_encode
    {a b : (graph (G₁ := G₁) (G₂ := G₂)).Point}
    {p q : Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b}
    (h : Presented.Homotopy (presentation i₁ i₂) p q) :
    encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p =
      encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ q := by
  induction h with
  | refl _ => rfl
  | relator h => exact relator_encode i₁ i₂ L₁ L₂ M₁ M₂ h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | inv_congr _ ih =>
      exact _root_.congrArg (targetInv i₁ i₂ L₁ L₂ M₁ M₂) ih
  | comp_congr _ _ ih₁ ih₂ =>
      exact binary_congr FullAmalgamatedFreeProduct.mul ih₁ ih₂
  | refl_trans p =>
      simpa only [encodeRaw] using FullAmalgamatedFreeProduct.one_mul'
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
  | trans_refl p =>
      simpa only [encodeRaw] using FullAmalgamatedFreeProduct.mul_one'
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
  | trans_assoc p q r =>
      simpa only [encodeRaw] using FullAmalgamatedFreeProduct.mul_assoc'
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ q)
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ r)
  | symm_trans p =>
      simpa only [encodeRaw] using FullAmalgamatedFreeProduct.inv_mul_cancel
        M₁.map_neg M₂.map_neg
        L₁.neg_add_rev L₂.neg_add_rev
        L₁.neg_zero L₂.neg_zero
        L₁.neg_add L₂.neg_add
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
  | trans_symm p =>
      simpa only [encodeRaw] using FullAmalgamatedFreeProduct.mul_inv_cancel
        M₁.map_neg M₂.map_neg
        L₁.neg_add_rev L₂.neg_add_rev
        L₁.neg_zero L₂.neg_zero
        L₁.add_neg L₂.add_neg
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
  | symm_symm p =>
      simpa only [encodeRaw] using targetInv_involutive i₁ i₂ L₁ L₂ M₁ M₂
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
  | symm_refl _ =>
      simpa only [encodeRaw] using targetInv_one i₁ i₂ L₁ L₂ M₁ M₂
  | symm_comp p q =>
      simpa only [encodeRaw] using targetInv_mul i₁ i₂ L₁ L₂ M₁ M₂
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p)
        (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ q)

/-- Encode presented fundamental-group classes. -/
noncomputable def encode :
    Presented.PiOne (presentation i₁ i₂) () → Target i₁ i₂ :=
  Quot.lift
    (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂)
    (fun _ _ h => homotopy_encode i₁ i₂ L₁ L₂ M₁ M₂ h)

end Encoding

/-- Fundamental group of the raw amalgamated path presentation. -/
abbrev PiOne : Type u :=
  Presented.PiOne (presentation i₁ i₂) ()

/-- Left component generator as a presented fundamental-group element. -/
noncomputable def leftClass (x : G₁) : PiOne i₁ i₂ :=
  Presented.PiOne.ofRaw (P := presentation i₁ i₂) (rawLeft x)

/-- Right component generator as a presented fundamental-group element. -/
noncomputable def rightClass (y : G₂) : PiOne i₁ i₂ :=
  Presented.PiOne.ofRaw (P := presentation i₁ i₂) (rawRight y)

@[simp] theorem leftClass_add (x y : G₁) :
    Presented.PiOne.mul (leftClass i₁ i₂ x) (leftClass i₁ i₂ y) =
      leftClass i₁ i₂ (x + y) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.left_add (i₁ := i₁) (i₂ := i₂) x y))

@[simp] theorem rightClass_add (x y : G₂) :
    Presented.PiOne.mul (rightClass i₁ i₂ x) (rightClass i₁ i₂ y) =
      rightClass i₁ i₂ (x + y) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.right_add (i₁ := i₁) (i₂ := i₂) x y))

@[simp] theorem leftClass_zero :
    leftClass i₁ i₂ (0 : G₁) =
      (Presented.PiOne.id : PiOne i₁ i₂) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.left_zero (i₁ := i₁) (i₂ := i₂)))

@[simp] theorem rightClass_zero :
    rightClass i₁ i₂ (0 : G₂) =
      (Presented.PiOne.id : PiOne i₁ i₂) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.right_zero (i₁ := i₁) (i₂ := i₂)))

@[simp] theorem inv_leftClass (x : G₁) :
    Presented.PiOne.inv (leftClass i₁ i₂ x) =
      leftClass i₁ i₂ (-x) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.left_neg (i₁ := i₁) (i₂ := i₂) x))

@[simp] theorem inv_rightClass (y : G₂) :
    Presented.PiOne.inv (rightClass i₁ i₂ y) =
      rightClass i₁ i₂ (-y) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.right_neg (i₁ := i₁) (i₂ := i₂) y))

@[simp] theorem leftClass_amalg (h : H) :
    leftClass i₁ i₂ (i₁ h) = rightClass i₁ i₂ (i₂ h) :=
  Quot.sound (Presented.Homotopy.relator
    (Relator.amalg (i₁ := i₁) (i₂ := i₂) h))

/-- Decode a full-product word as a composable raw path class. -/
noncomputable def decodeWord :
    FreeProductWord G₁ G₂ → PiOne i₁ i₂
  | .nil => Presented.PiOne.id
  | .consLeft x rest =>
      Presented.PiOne.mul (leftClass i₁ i₂ x)
        (decodeWord rest)
  | .consRight y rest =>
      Presented.PiOne.mul (rightClass i₁ i₂ y)
        (decodeWord rest)

/-- Decoding word concatenation is path-class multiplication. -/
theorem decodeWord_concat (w₁ w₂ : FreeProductWord G₁ G₂) :
    decodeWord i₁ i₂ (FreeProductWord.concat w₁ w₂) =
      Presented.PiOne.mul
        (decodeWord i₁ i₂ w₁) (decodeWord i₁ i₂ w₂) := by
  induction w₁ with
  | nil =>
      simp [decodeWord]
  | consLeft x rest ih =>
      simp [FreeProductWord.concat, decodeWord, ih,
        Presented.PiOne.mul_assoc]
  | consRight y rest ih =>
      simp [FreeProductWord.concat, decodeWord, ih,
        Presented.PiOne.mul_assoc]

/-- Decoding word inversion is reversal of the represented path class. -/
theorem decodeWord_inverse (w : FreeProductWord G₁ G₂) :
    decodeWord i₁ i₂ (FreeProductWord.inverse w) =
      Presented.PiOne.inv (decodeWord i₁ i₂ w) := by
  induction w with
  | nil =>
      simp [FreeProductWord.inverse, decodeWord]
  | consLeft x rest ih =>
      simp [FreeProductWord.inverse, decodeWord_concat, decodeWord, ih,
        Presented.PiOne.inv_mul_order, FreeProductWord.singleLeft]
  | consRight y rest ih =>
      simp [FreeProductWord.inverse, decodeWord_concat, decodeWord, ih,
        Presented.PiOne.inv_mul_order, FreeProductWord.singleRight]

/-- A free-group reduction step preserves the decoded presented path class. -/
theorem decode_freeGroupStep
    {w w' : FreeProductWord G₁ G₂}
    (h : FreeProductWord.FreeGroupStep w w') :
    decodeWord i₁ i₂ w = decodeWord i₁ i₂ w' := by
  induction h with
  | combineLeft x y rest =>
      calc
        decodeWord i₁ i₂
            (FreeProductWord.consLeft x
              (FreeProductWord.consLeft y rest)) =
            Presented.PiOne.mul (leftClass i₁ i₂ x)
              (Presented.PiOne.mul (leftClass i₁ i₂ y)
                (decodeWord i₁ i₂ rest)) := rfl
        _ = Presented.PiOne.mul
              (Presented.PiOne.mul (leftClass i₁ i₂ x)
                (leftClass i₁ i₂ y))
              (decodeWord i₁ i₂ rest) :=
            (Presented.PiOne.mul_assoc _ _ _).symm
        _ = Presented.PiOne.mul (leftClass i₁ i₂ (x + y))
              (decodeWord i₁ i₂ rest) := by rw [leftClass_add]
        _ = decodeWord i₁ i₂
              (FreeProductWord.consLeft (x + y) rest) := rfl
  | combineRight x y rest =>
      calc
        decodeWord i₁ i₂
            (FreeProductWord.consRight x
              (FreeProductWord.consRight y rest)) =
            Presented.PiOne.mul (rightClass i₁ i₂ x)
              (Presented.PiOne.mul (rightClass i₁ i₂ y)
                (decodeWord i₁ i₂ rest)) := rfl
        _ = Presented.PiOne.mul
              (Presented.PiOne.mul (rightClass i₁ i₂ x)
                (rightClass i₁ i₂ y))
              (decodeWord i₁ i₂ rest) :=
            (Presented.PiOne.mul_assoc _ _ _).symm
        _ = Presented.PiOne.mul (rightClass i₁ i₂ (x + y))
              (decodeWord i₁ i₂ rest) := by rw [rightClass_add]
        _ = decodeWord i₁ i₂
              (FreeProductWord.consRight (x + y) rest) := rfl
  | removeLeftZero rest =>
      rw [decodeWord, leftClass_zero, Presented.PiOne.id_mul]
  | removeRightZero rest =>
      rw [decodeWord, rightClass_zero, Presented.PiOne.id_mul]
  | congrLeft x h ih =>
      exact _root_.congrArg
        (fun z => Presented.PiOne.mul (leftClass i₁ i₂ x) z) ih
  | congrRight y h ih =>
      exact _root_.congrArg
        (fun z => Presented.PiOne.mul (rightClass i₁ i₂ y) z) ih

/-- An amalgamation step preserves the decoded presented path class. -/
theorem decode_amalgRelation
    {w w' : FreeProductWord G₁ G₂}
    (h : AmalgRelation i₁ i₂ w w') :
    decodeWord i₁ i₂ w = decodeWord i₁ i₂ w' := by
  cases h with
  | amalgLeftToRight h pre suf =>
      simp [decodeWord_concat, FreeProductWord.singleLeft,
        FreeProductWord.singleRight, decodeWord, leftClass_amalg]
  | amalgRightToLeft h pre suf =>
      simp [decodeWord_concat, FreeProductWord.singleLeft,
        FreeProductWord.singleRight, decodeWord, leftClass_amalg]

/-- The full amalgamated equivalence preserves decoded path classes. -/
theorem decode_fullAmalgEquiv
    {w w' : FreeProductWord G₁ G₂}
    (h : FullAmalgEquiv i₁ i₂ w w') :
    decodeWord i₁ i₂ w = decodeWord i₁ i₂ w' := by
  induction h with
  | refl _ => rfl
  | amalg h => exact decode_amalgRelation i₁ i₂ h
  | freeGroup h => exact decode_freeGroupStep i₁ i₂ h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Decode a full amalgamated class into the presented fundamental group. -/
noncomputable def decode : Target i₁ i₂ → PiOne i₁ i₂ :=
  Quot.lift
    (decodeWord i₁ i₂)
    (fun _ _ h => decode_fullAmalgEquiv i₁ i₂ h)

@[simp] theorem decode_ofWord (w : FreeProductWord G₁ G₂) :
    decode i₁ i₂ (FullAmalgamatedFreeProduct.ofWord w) =
      decodeWord i₁ i₂ w :=
  rfl

@[simp] theorem decode_one :
    decode i₁ i₂ (FullAmalgamatedFreeProduct.one : Target i₁ i₂) =
      (Presented.PiOne.id : PiOne i₁ i₂) :=
  rfl

theorem decode_mul (x y : Target i₁ i₂) :
    decode i₁ i₂ (FullAmalgamatedFreeProduct.mul x y) =
      Presented.PiOne.mul (decode i₁ i₂ x) (decode i₁ i₂ y) := by
  induction x using Quot.ind with
  | _ w₁ =>
      induction y using Quot.ind with
      | _ w₂ =>
          exact decodeWord_concat i₁ i₂ w₁ w₂

section DecodeInverse

variable [Add H] [Zero H] [Neg H]
variable (L₁ : GroupLaws G₁) (L₂ : GroupLaws G₂)
variable (M₁ : PreservesGroupOps i₁) (M₂ : PreservesGroupOps i₂)

theorem decode_inv (x : Target i₁ i₂) :
    decode i₁ i₂ (targetInv i₁ i₂ L₁ L₂ M₁ M₂ x) =
      Presented.PiOne.inv (decode i₁ i₂ x) := by
  induction x using Quot.ind with
  | _ w =>
      exact decodeWord_inverse i₁ i₂ w

end DecodeInverse

section Equivalence

variable [Add H] [Zero H] [Neg H]
variable (L₁ : GroupLaws G₁) (L₂ : GroupLaws G₂)
variable (M₁ : PreservesGroupOps i₁) (M₂ : PreservesGroupOps i₂)

@[simp] theorem encode_leftClass (x : G₁) :
    encode i₁ i₂ L₁ L₂ M₁ M₂ (leftClass i₁ i₂ x) =
      FullAmalgamatedFreeProduct.ofWord
        (FreeProductWord.singleLeft x) :=
  rfl

@[simp] theorem encode_rightClass (y : G₂) :
    encode i₁ i₂ L₁ L₂ M₁ M₂ (rightClass i₁ i₂ y) =
      FullAmalgamatedFreeProduct.ofWord
        (FreeProductWord.singleRight y) :=
  rfl

theorem encode_mul (x y : PiOne i₁ i₂) :
    encode i₁ i₂ L₁ L₂ M₁ M₂
        (Presented.PiOne.mul x y) =
      FullAmalgamatedFreeProduct.mul
        (encode i₁ i₂ L₁ L₂ M₁ M₂ x)
        (encode i₁ i₂ L₁ L₂ M₁ M₂ y) := by
  induction x using Quot.ind with
  | _ p =>
      induction y using Quot.ind with
      | _ q =>
          rfl

theorem encode_inv (x : PiOne i₁ i₂) :
    encode i₁ i₂ L₁ L₂ M₁ M₂
        (Presented.PiOne.inv x) =
      targetInv i₁ i₂ L₁ L₂ M₁ M₂
        (encode i₁ i₂ L₁ L₂ M₁ M₂ x) := by
  induction x using Quot.ind with
  | _ p =>
      rfl

@[simp] theorem encode_id :
    encode i₁ i₂ L₁ L₂ M₁ M₂
        (Presented.PiOne.id : PiOne i₁ i₂) =
      (FullAmalgamatedFreeProduct.one : Target i₁ i₂) :=
  rfl

/-- Encoding after word decoding recovers the represented full-product class. -/
theorem encode_decodeWord (w : FreeProductWord G₁ G₂) :
    encode i₁ i₂ L₁ L₂ M₁ M₂ (decodeWord i₁ i₂ w) =
      FullAmalgamatedFreeProduct.ofWord w := by
  induction w with
  | nil =>
      rfl
  | consLeft x rest ih =>
      rw [decodeWord, encode_mul, encode_leftClass, ih]
      rfl
  | consRight y rest ih =>
      rw [decodeWord, encode_mul, encode_rightClass, ih]
      rfl

@[simp] theorem encode_decode (x : Target i₁ i₂) :
    encode i₁ i₂ L₁ L₂ M₁ M₂ (decode i₁ i₂ x) = x := by
  induction x using Quot.ind with
  | _ w =>
      exact encode_decodeWord i₁ i₂ L₁ L₂ M₁ M₂ w

/-- Decoding the encoded image of a raw path returns its homotopy class. -/
theorem decode_encodeRaw
    {a b : (graph (G₁ := G₁) (G₂ := G₂)).Point}
    (p : Presented.RawPath (graph (G₁ := G₁) (G₂ := G₂)) a b) :
    decode i₁ i₂ (encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p) =
      Presented.PathClass.ofRaw p := by
  induction p with
  | refl _ =>
      rfl
  | edge e =>
      cases e with
      | left x =>
          change
            decode i₁ i₂
                (FullAmalgamatedFreeProduct.ofWord
                  (FreeProductWord.singleLeft x)) =
              leftClass i₁ i₂ x
          rw [decode_ofWord]
          change
            Presented.PiOne.mul (leftClass i₁ i₂ x)
                (Presented.PiOne.id : PiOne i₁ i₂) =
              leftClass i₁ i₂ x
          exact Presented.PiOne.mul_id _
      | right y =>
          change
            decode i₁ i₂
                (FullAmalgamatedFreeProduct.ofWord
                  (FreeProductWord.singleRight y)) =
              rightClass i₁ i₂ y
          rw [decode_ofWord]
          change
            Presented.PiOne.mul (rightClass i₁ i₂ y)
                (Presented.PiOne.id : PiOne i₁ i₂) =
              rightClass i₁ i₂ y
          exact Presented.PiOne.mul_id _
  | symm p ih =>
      rw [encodeRaw, decode_inv, ih]
      rfl
  | trans p q ihp ihq =>
      rw [encodeRaw, decode_mul, ihp, ihq]
      rfl

theorem decode_encode (x : PiOne i₁ i₂) :
    decode i₁ i₂ (encode i₁ i₂ L₁ L₂ M₁ M₂ x) = x := by
  induction x using Quot.ind with
  | _ p =>
      exact decode_encodeRaw i₁ i₂ L₁ L₂ M₁ M₂ p

/-- **Presented Seifert--van Kampen.**  The fundamental group of the raw
amalgamated path presentation is equivalent to the full amalgamated free
product. -/
noncomputable def presentedSeifertVanKampenEquiv :
    SimpleEquiv (PiOne i₁ i₂) (Target i₁ i₂) where
  toFun := encode i₁ i₂ L₁ L₂ M₁ M₂
  invFun := decode i₁ i₂
  left_inv := decode_encode i₁ i₂ L₁ L₂ M₁ M₂
  right_inv := encode_decode i₁ i₂ L₁ L₂ M₁ M₂

/-- Group-isomorphism package for presented Seifert--van Kampen. -/
noncomputable def presentedSeifertVanKampenGroupEquivCore :
    Presented.GroupEquiv.{u, u}
      (PiOne i₁ i₂) (Target i₁ i₂)
      Presented.PiOne.mul Presented.PiOne.id Presented.PiOne.inv
      FullAmalgamatedFreeProduct.mul FullAmalgamatedFreeProduct.one
      (targetInv i₁ i₂ L₁ L₂ M₁ M₂) where
  equiv := presentedSeifertVanKampenEquiv i₁ i₂ L₁ L₂ M₁ M₂
  map_mul := encode_mul i₁ i₂ L₁ L₂ M₁ M₂
  map_one := encode_id i₁ i₂ L₁ L₂ M₁ M₂
  map_inv := encode_inv i₁ i₂ L₁ L₂ M₁ M₂

/-- **Presented Seifert--van Kampen as a group equivalence**, with all
component-group and amalgamating-homomorphism laws exposed in the input. -/
noncomputable def presentedSeifertVanKampenGroupEquiv
    (A : AmalgamationLaws i₁ i₂) :
    Presented.GroupEquiv.{u, u}
      (PiOne i₁ i₂) (Target i₁ i₂)
      Presented.PiOne.mul Presented.PiOne.id Presented.PiOne.inv
      FullAmalgamatedFreeProduct.mul FullAmalgamatedFreeProduct.one
      (targetInv i₁ i₂ L₁ L₂ A.left_hom A.right_hom) :=
  presentedSeifertVanKampenGroupEquivCore
    i₁ i₂ L₁ L₂ A.left_hom A.right_hom

/-- Concrete equality trace for the encode/decode normalization. -/
noncomputable def encodeDecodePath (x : Target i₁ i₂) :
    Path
      (encode i₁ i₂ L₁ L₂ M₁ M₂ (decode i₁ i₂ x))
      x :=
  Path.stepChain (encode_decode i₁ i₂ L₁ L₂ M₁ M₂ x)

/-- The SVK normalization trace is right-unit coherent. -/
noncomputable def encodeDecodeCoherence (x : Target i₁ i₂) :
    RwEq
      (Path.trans (encodeDecodePath i₁ i₂ L₁ L₂ M₁ M₂ x)
        (Path.refl x))
      (encodeDecodePath i₁ i₂ L₁ L₂ M₁ M₂ x) :=
  rweq_cmpA_refl_right (encodeDecodePath i₁ i₂ L₁ L₂ M₁ M₂ x)

end Equivalence

end Presentation

/-! ## Figure-eight specialization -/

private instance unitAdd : Add Unit :=
  ⟨fun _ _ => ()⟩

private instance unitZero : Zero Unit :=
  ⟨()⟩

private instance unitNeg : Neg Unit :=
  ⟨fun x => x⟩

def unitGroupLaws : GroupLaws Unit where
  add_assoc := by intro x y z; cases x; cases y; cases z; rfl
  zero_add := by intro x; cases x; rfl
  add_zero := by intro x; cases x; rfl
  neg_add_rev := by intro x y; cases x; cases y; rfl
  neg_zero := rfl
  neg_add := by intro x; cases x; rfl
  add_neg := by intro x; cases x; rfl
  neg_neg := by intro x; cases x; rfl

/-- Integer group laws used by the figure-eight factors. -/
def intGroupLaws : GroupLaws Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_rev := by
    intro x y
    exact Int.neg_add.trans (Int.add_comm (-x) (-y))
  neg_zero := rfl
  neg_add := Int.add_left_neg
  add_neg := Int.add_right_neg
  neg_neg := Int.neg_neg

/-- The trivial map from the amalgamating unit preserves the group operations. -/
def zeroPreservesGroupOps :
    PreservesGroupOps (fun _ : Unit => (0 : Int)) where
  map_add := by
    intro x y
    cases x
    cases y
    rfl
  map_zero := rfl
  map_neg := by
    intro h
    cases h
    rfl

def figureEightAmalgamationLaws :
    AmalgamationLaws
      (fun _ : Unit => (0 : Int))
      (fun _ : Unit => (0 : Int)) where
  source_laws := unitGroupLaws
  left_hom := zeroPreservesGroupOps
  right_hom := zeroPreservesGroupOps

/-- Raw presented figure-eight paths use two integer-labelled edge families
with trivial amalgamation. -/
abbrev FigureEightPiOne : Type :=
  PiOne (fun _ : Unit => (0 : Int)) (fun _ : Unit => (0 : Int))

/-- Full free-product target of the presented figure-eight. -/
abbrev FigureEightTarget : Type :=
  Target (fun _ : Unit => (0 : Int)) (fun _ : Unit => (0 : Int))

/-- The fundamental group of the presented figure-eight path space is the full
free product of two integer groups. -/
noncomputable def figureEightPresentedPiOneEquiv :
    SimpleEquiv FigureEightPiOne FigureEightTarget :=
  presentedSeifertVanKampenEquiv
    (fun _ : Unit => (0 : Int))
    (fun _ : Unit => (0 : Int))
    intGroupLaws intGroupLaws
    zeroPreservesGroupOps zeroPreservesGroupOps

/-- Group-isomorphism package for the presented figure-eight theorem. -/
noncomputable def figureEightPresentedPiOneGroupEquiv :
    Presented.GroupEquiv.{0, 0}
      FigureEightPiOne FigureEightTarget
      Presented.PiOne.mul Presented.PiOne.id Presented.PiOne.inv
      FullAmalgamatedFreeProduct.mul FullAmalgamatedFreeProduct.one
      (targetInv
        (fun _ : Unit => (0 : Int))
        (fun _ : Unit => (0 : Int))
        intGroupLaws intGroupLaws
        zeroPreservesGroupOps zeroPreservesGroupOps) :=
  presentedSeifertVanKampenGroupEquiv
    (fun _ : Unit => (0 : Int))
    (fun _ : Unit => (0 : Int))
    intGroupLaws intGroupLaws
    figureEightAmalgamationLaws

/-- Left exponent sum of a two-factor integer word. -/
def figureEightLeftExponentWord :
    FreeProductWord Int Int → Int
  | .nil => 0
  | .consLeft x rest => x + figureEightLeftExponentWord rest
  | .consRight _ rest => figureEightLeftExponentWord rest

@[simp] theorem figureEightLeftExponentWord_concat
    (w₁ w₂ : FreeProductWord Int Int) :
    figureEightLeftExponentWord (FreeProductWord.concat w₁ w₂) =
      figureEightLeftExponentWord w₁ + figureEightLeftExponentWord w₂ := by
  induction w₁ with
  | nil => simp [FreeProductWord.concat, figureEightLeftExponentWord]
  | consLeft x rest ih =>
      simp [FreeProductWord.concat, figureEightLeftExponentWord, ih,
        Int.add_assoc]
  | consRight y rest ih =>
      simp [FreeProductWord.concat, figureEightLeftExponentWord, ih]

/-- Free-group word reductions preserve the left exponent sum. -/
theorem figureEightLeftExponent_freeGroupStep
    {w w' : FreeProductWord Int Int}
    (h : FreeProductWord.FreeGroupStep w w') :
    figureEightLeftExponentWord w =
      figureEightLeftExponentWord w' := by
  induction h with
  | combineLeft x y rest =>
      simp [figureEightLeftExponentWord, Int.add_assoc]
  | combineRight _ _ _ => rfl
  | removeLeftZero _ => simp [figureEightLeftExponentWord]
  | removeRightZero _ => rfl
  | congrLeft x h ih =>
      simp [figureEightLeftExponentWord, ih]
  | congrRight y h ih =>
      exact ih

/-- Trivial amalgamation preserves the left exponent sum. -/
theorem figureEightLeftExponent_amalg
    {w w' : FreeProductWord Int Int}
    (h : AmalgRelation
      (fun _ : Unit => (0 : Int))
      (fun _ : Unit => (0 : Int)) w w') :
    figureEightLeftExponentWord w =
      figureEightLeftExponentWord w' := by
  cases h with
  | amalgLeftToRight h pre suf =>
      cases h
      simp [figureEightLeftExponentWord_concat,
        FreeProductWord.singleLeft, FreeProductWord.singleRight,
        figureEightLeftExponentWord]
  | amalgRightToLeft h pre suf =>
      cases h
      simp [figureEightLeftExponentWord_concat,
        FreeProductWord.singleLeft, FreeProductWord.singleRight,
        figureEightLeftExponentWord]

/-- The full figure-eight relation preserves the left exponent sum. -/
theorem figureEightLeftExponent_full
    {w w' : FreeProductWord Int Int}
    (h : FullAmalgEquiv
      (fun _ : Unit => (0 : Int))
      (fun _ : Unit => (0 : Int)) w w') :
    figureEightLeftExponentWord w =
      figureEightLeftExponentWord w' := by
  induction h with
  | refl _ => rfl
  | amalg h => exact figureEightLeftExponent_amalg h
  | freeGroup h => exact figureEightLeftExponent_freeGroupStep h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Left exponent homomorphism on the full figure-eight target. -/
noncomputable def figureEightLeftExponent :
    FigureEightTarget → Int :=
  Quot.lift figureEightLeftExponentWord
    (fun _ _ h => figureEightLeftExponent_full h)

/-- The left unit generator is nontrivial in the full figure-eight target. -/
theorem figureEightTarget_left_generator_ne_one :
    (FullAmalgamatedFreeProduct.ofWord
        (FreeProductWord.singleLeft (1 : Int)) :
      FigureEightTarget) ≠
      FullAmalgamatedFreeProduct.one := by
  intro h
  have hexp := _root_.congrArg figureEightLeftExponent h
  simp [figureEightLeftExponent, figureEightLeftExponentWord,
    FreeProductWord.singleLeft, FullAmalgamatedFreeProduct.one,
    FullAmalgamatedFreeProduct.ofWord] at hexp

/-- The presented figure-eight fundamental group is nontrivial. -/
theorem figureEightPresented_nontrivial :
    leftClass
        (fun _ : Unit => (0 : Int))
        (fun _ : Unit => (0 : Int)) 1 ≠
      (Presented.PiOne.id : FigureEightPiOne) := by
  intro h
  apply figureEightTarget_left_generator_ne_one
  have h' := _root_.congrArg
    (encode
      (fun _ : Unit => (0 : Int))
      (fun _ : Unit => (0 : Int))
      intGroupLaws intGroupLaws
      zeroPreservesGroupOps zeroPreservesGroupOps) h
  exact h'

end PresentedSeifertVanKampen
end CompPath
end Path
end ComputationalPaths
