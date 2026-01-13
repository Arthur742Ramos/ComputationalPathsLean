/-
# Derived Transport Theorems

This module provides axiom-free, sorry-free theorems about transport
in the computational paths framework. All results are derived from
the primitive rewrite steps.

## Main Results

### Transport Coherence
- `transport_trans_trans`: Triple composition transport
- `transport_assoc'`: Associativity of transport
- `transport_symm_symm'`: Double symmetry for transport
- `transport_back_and_forth'`: Round-trip transport is identity

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.GroupoidDerived

namespace ComputationalPaths
namespace Path
namespace TransportDerived

open Step

universe u

variable {A : Type u}

/-! ## Transport Computation Rules

These are the fundamental computation rules for transport. -/

/-- Transport along reflexivity is identity.
    `transport (refl a) x = x` -/
theorem rweq_transport_refl'
    {B : A → Type u} {a : A} (x : B a) :
    RwEq (ofEq (transport_refl (D := B) (a := a) (x := x)))
         (refl x) :=
  rweq_transport_refl_beta x

/-! ## Transport Coherence Laws

These theorems describe coherence properties of transport. -/

/-- Transport along double composition.
    `transport ((p · q) · r) x = transport r (transport q (transport p x))` -/
theorem transport_trans_trans
    {B : A → Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : B a) :
    transport (trans (trans p q) r) x =
    transport r (transport q (transport p x)) := by
  rw [transport_trans (trans p q) r]
  rw [transport_trans p q]

/-- Transport along associated composition.
    `transport (p · (q · r)) x = transport r (transport q (transport p x))` -/
theorem transport_assoc'
    {B : A → Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : B a) :
    transport (trans p (trans q r)) x =
    transport r (transport q (transport p x)) := by
  rw [transport_trans p (trans q r)]
  rw [transport_trans q r]

/-- Transport along double symmetry is transport along original.
    `transport (symm (symm p)) x = transport p x` -/
theorem transport_symm_symm'
    {B : A → Type u} {a b : A}
    (p : Path a b) (x : B a) :
    transport (symm (symm p)) x = transport p x := by
  have h : symm (symm p) = p := Path.symm_symm p
  rw [h]

/-! ## Transport and Path Operations

Interactions between transport and other path operations. -/

/-- Subst is the same as transport (alternative formulation). -/
theorem subst_eq_transport'
    {B : A → Type u} {a b : A}
    (x : B a) (p : Path a b) :
    subst x p = transport p x := rfl

/-! ## Transport Functoriality

Transport is functorial in the path. -/

/-- Transport is functorial: composition. -/
theorem transport_comp'
    {B : A → Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    transport (trans p q) x = transport q (transport p x) :=
  transport_trans p q x

/-- Transport respects path equality.
    If p = q (as paths), then transport p = transport q. -/
theorem transport_eq_of_eq'
    {B : A → Type u} {a b : A}
    {p q : Path a b} (h : p = q) (x : B a) :
    transport p x = transport q x := by
  rw [h]

/-! ## Dependent Path Transport

Theorems about transport in the context of dependent paths. -/

/-- Transport along refl applied to any element is that element. -/
theorem transport_refl_id
    {B : A → Type u} (a : A) (x : B a) :
    transport (refl a) x = x :=
  transport_refl (D := B) (a := a) x

/-- Transporting and back is identity. -/
theorem transport_back_and_forth'
    {B : A → Type u} {a b : A}
    (p : Path a b) (x : B a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

/-- Transporting forward from a backwards transport. -/
theorem transport_forth_and_back'
    {B : A → Type u} {a b : A}
    (p : Path a b) (y : B b) :
    transport p (transport (symm p) y) = y :=
  transport_symm_right p y

/-! ## Higher Transport Laws

More complex interactions of transport with path operations. -/

/-- Triple composition transport (left-associated). -/
theorem transport_trans_three'
    {B : A → Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : B a) :
    transport (trans (trans p q) r) x =
    transport r (transport (trans p q) x) :=
  transport_trans (trans p q) r x

/-- Transport through identity paths on both ends. -/
theorem transport_refl_trans_refl'
    {B : A → Type u} {a b : A}
    (p : Path a b) (x : B a) :
    transport (trans (refl a) (trans p (refl b))) x = transport p x := by
  rw [transport_trans (refl a)]
  rw [transport_trans p (refl b)]
  rw [transport_refl (D := B)]
  rw [transport_refl (D := B)]

end TransportDerived
end Path
end ComputationalPaths
