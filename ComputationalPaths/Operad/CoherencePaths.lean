import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Operadic coherence paths

This module records operadic composition laws directly as rewrite paths.
Composition is `Path.trans`, and unit/associativity are witnessed by
`Rw`/`RwEq` derivations from primitive rewrite steps.
-/

namespace ComputationalPaths
namespace Operad

open Path
open Path.Step

universe u

/-- Operadic operations represented as computational paths. -/
abbrev Operation {A : Type u} (a b : A) := Path a b

/-- Operadic composition is path composition. -/
@[simp] noncomputable def opComp {A : Type u} {a b c : A}
    (f : Operation a b) (g : Operation b c) : Operation a c :=
  Path.trans f g

/-- Identity operation. -/
@[simp] noncomputable def opId {A : Type u} (a : A) : Operation a a :=
  Path.refl a

section Coherence

variable {A : Type u}
variable {a b c d : A}

/-- Left unitality as a genuine rewrite path. -/
theorem opComp_id_left_rw (f : Operation a b) :
    Rw (opComp (opId a) f) f :=
  rw_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) f)

/-- Right unitality as a genuine rewrite path. -/
theorem opComp_id_right_rw (f : Operation a b) :
    Rw (opComp f (opId b)) f :=
  rw_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) f)

/-- Associativity as a genuine rewrite path. -/
theorem opComp_assoc_rw (f : Operation a b) (g : Operation b c) (h : Operation c d) :
    Rw (opComp (opComp f g) h) (opComp f (opComp g h)) :=
  rw_of_step (Step.trans_assoc (A := A) (a := a) (b := b) (c := c) (d := d) f g h)

/-- Left unitality in rewrite-equivalence form. -/
noncomputable def opComp_id_left (f : Operation a b) :
    RwEq (opComp (opId a) f) f :=
  rweq_of_rw (opComp_id_left_rw (A := A) (a := a) (b := b) f)

/-- Right unitality in rewrite-equivalence form. -/
noncomputable def opComp_id_right (f : Operation a b) :
    RwEq (opComp f (opId b)) f :=
  rweq_of_rw (opComp_id_right_rw (A := A) (a := a) (b := b) f)

/-- Associativity in rewrite-equivalence form. -/
noncomputable def opComp_assoc (f : Operation a b) (g : Operation b c) (h : Operation c d) :
    RwEq (opComp (opComp f g) h) (opComp f (opComp g h)) :=
  rweq_of_rw (opComp_assoc_rw (A := A) (a := a) (b := b) (c := c) (d := d) f g h)

end Coherence

/-- Operadic composition data with coherence encoded as rewrite paths. -/
structure PathOperad (A : Type u) where
  comp : {a b c : A} → Operation a b → Operation b c → Operation a c
  id : (a : A) → Operation a a
  comp_id_left : {a b : A} → (f : Operation a b) → RwEq (comp (id a) f) f
  comp_id_right : {a b : A} → (f : Operation a b) → RwEq (comp f (id b)) f
  comp_assoc : {a b c d : A} →
    (f : Operation a b) → (g : Operation b c) → (h : Operation c d) →
      RwEq (comp (comp f g) h) (comp f (comp g h))

/-- Canonical operadic coherence induced by path composition. -/
noncomputable def canonicalPathOperad (A : Type u) : PathOperad A where
  comp := fun f g => opComp f g
  id := opId
  comp_id_left := by
    intro a b f
    exact opComp_id_left (A := A) (a := a) (b := b) f
  comp_id_right := by
    intro a b f
    exact opComp_id_right (A := A) (a := a) (b := b) f
  comp_assoc := by
    intro a b c d f g h
    exact opComp_assoc (A := A) (a := a) (b := b) (c := c) (d := d) f g h

end Operad
end ComputationalPaths
