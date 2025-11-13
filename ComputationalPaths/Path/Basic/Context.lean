/-
# Contextual substitution for computational paths

This module packages the "subterm substitution" principle from the paper, making
it possible to treat contexts with one or two holes uniformly.  The constructors
mirror Definition 3.5 (sub L/sub R) and propagate `Path` witnesses through those
contexts.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path

universe u v w

/-- A unary context `A ⊢ B` that can contain a single hole of type `A`. -/
structure Context (A : Type u) (B : Type v) where
  fill : A → B

namespace Context

variable {A : Type u} {B : Type v}

/-- Map a path through a unary context (paper's `sub L`). -/
@[simp] def map (C : Context A B) {a b : A} (p : Path a b) :
    Path (C.fill a) (C.fill b) :=
  congrArg C.fill p

@[simp] theorem map_refl (C : Context A B) (a : A) :
    map C (Path.refl a) = Path.refl (C.fill a) := by
  simp [map]

@[simp] theorem map_symm (C : Context A B) {a b : A} (p : Path a b) :
    map C (Path.symm p) = Path.symm (map C p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [map]

@[simp] theorem map_trans (C : Context A B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    map C (Path.trans p q) =
      Path.trans (map C p) (map C q) := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [map, Path.trans, List.map_append]

/-- Compose two unary contexts. -/
@[simp] def comp {C' : Type w}
    (g : Context B C') (f : Context A B) : Context A C' :=
  ⟨fun a => g.fill (f.fill a)⟩

@[simp] theorem map_comp {C' : Type w}
    (g : Context B C') (f : Context A B)
    {a b : A} (p : Path a b) :
    map (comp g f) p =
      map g (map f p) := by
  cases p
  simp [map, comp]

end Context

/-- A binary context encapsulating Definition 3.5's `sub L` and `sub R`. -/
structure BiContext (A : Type u) (B : Type v) (C : Type w) where
  fill : A → B → C

namespace BiContext

variable {A : Type u} {B : Type v} {C : Type w}

/-- Substitute along the left hole of a binary context (paper's `sub L`). -/
@[simp] def mapLeft (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    Path (K.fill a₁ b) (K.fill a₂ b) :=
  congrArg (fun x => K.fill x b) p

/-- Substitute along the right hole of a binary context (paper's `sub R`). -/
@[simp] def mapRight (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (K.fill a b₁) (K.fill a b₂) :=
  congrArg (K.fill a) p

@[simp] theorem mapLeft_refl (K : BiContext A B C) (a : A) (b : B) :
    mapLeft K (Path.refl a) b = Path.refl (K.fill a b) := by
  simp [mapLeft]

@[simp] theorem mapLeft_symm (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    mapLeft K (Path.symm p) b =
      Path.symm (mapLeft K p b) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapLeft]

@[simp] theorem mapLeft_trans (K : BiContext A B C)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B) :
    mapLeft K (Path.trans p q) b =
      Path.trans (mapLeft K p b) (mapLeft K q b) := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [mapLeft, Path.trans, List.map_append]

@[simp] theorem mapRight_refl (K : BiContext A B C) (a : A) (b : B) :
    mapRight K a (Path.refl b) = Path.refl (K.fill a b) := by
  simp [mapRight]

@[simp] theorem mapRight_symm (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    mapRight K a (Path.symm p) =
      Path.symm (mapRight K a p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapRight]

@[simp] theorem mapRight_trans (K : BiContext A B C)
    (a : A) {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    mapRight K a (Path.trans p q) =
      Path.trans (mapRight K a p) (mapRight K a q) := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [mapRight, Path.trans, List.map_append]

end BiContext

end Path
end ComputationalPaths
