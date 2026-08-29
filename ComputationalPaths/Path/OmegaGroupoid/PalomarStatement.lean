/-
# Publication boundary for the computational-path omega-groupoid

This file is the deliberately small statement-facing boundary for the
Palomar artifact.  It packages the repository's actual proof-relevant
computational-path developments rather than introducing a second toy cell
calculus.

The selected certificate has two synchronized presentations:

* the Type-valued derivation tower, whose core rewrite normalizer has an
  explicit decreasing measure and a typed bridge from every derivation to a
  strict normal form; and
* the RwEq-level weak omega-groupoid presentation, which exposes cancellation,
  explicit Mac Lane pentagon and triangle routes, inverse-cancellation
  coherence, interchange, and Eckmann--Hilton commutativity.

The route-count fields make the coherence content inspectable: the pentagon
routes use two and three primitive rewrite edges, while the triangle routes
use two and one.  Thus the higher witness connects genuinely different
rewrite syntax; it is not merely an equality proof of two proposition-level
statements.

The scope remains exact.  This is an extensional Lean formalization of the
computational-path construction.  It does not claim an intensional HoTT
identity type or a constructive Squier finite-derivation-type theorem.
-/

import ComputationalPaths.Path.OmegaGroupoid.OmegaWeakGroupoid

namespace ComputationalPaths
namespace Path
namespace PalomarOmegaGroupoid

universe u

/-! ## A finite syntax invariant for rewrite certificates -/

/-- Count primitive `Step` constructors in an `RwEq` certificate.

The count ignores the administrative constructors `refl`, `symm`, and
`trans`; it records only the number of primitive rewrite edges.  It is used
below to certify that the two named coherence routes have different syntax. -/
def rwEqStepCount {A : Type u} {a b : A} {p q : Path a b} : RwEq p q → Nat
  | .refl _ => 0
  | .step _ => 1
  | .symm h => rwEqStepCount h
  | .trans h₁ h₂ => rwEqStepCount h₁ + rwEqStepCount h₂

/-! ## The selected proof-relevant certificate -/

structure OmegaGroupoidCertificate (A : Type u) where
  /- The two repository-native packages. -/
  derivation_omega :
    _root_.ComputationalPaths.Path.OmegaGroupoid.StabilizedOmegaGroupoid A
  presentation_omega :
    _root_.ComputationalPaths.Path.OmegaGroupoid.OmegaWeakGroupoid A
  derivation_cells_are_explicit :
    derivation_omega.cells =
      _root_.ComputationalPaths.Path.OmegaGroupoid.CellType A
  stabilization_is_canonical :
    derivation_omega.stabilization =
      _root_.ComputationalPaths.Path.OmegaGroupoid.stabilization_theorem A

  /- The Type-valued 2-cell presentation and its exact RwEq interface. -/
  presentation_bridge : ∀ {a b : A} {p q : Path a b},
    Nonempty
        (_root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q) ↔
      RwEqProp p q
  two_cell_sound : ∀ {a b : A} {p q : Path a b},
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q → RwEq p q
  two_cell_complete : ∀ {a b : A} {p q : Path a b},
    RwEq p q → _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q
  two_cell_to_rw_eq_roundtrip : ∀ {a b : A} {p q : Path a b}
    (h : RwEq p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.toRwEq
      (_root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.ofRwEq h) = h
  two_cell_reification_roundtrip : ∀ {a b : A} {p q : Path a b}
    (d : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.ofRwEq
        (_root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.toRwEq d) = d

  /- A genuine normalization boundary, not just proof irrelevance. -/
  normalization_core : ∀ {a b : A} {p q : Path a b}
    (d : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.StrictNormalForm
        (_root_.ComputationalPaths.Path.OmegaGroupoid.normalizeDeriv d) ∧
      0 < _root_.ComputationalPaths.Path.OmegaGroupoid.kboWeight d
  normalization_is_core_strict : ∀ {a b : A} {p q : Path a b}
    (d : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.CoreStrictNormalForm
      (_root_.ComputationalPaths.Path.OmegaGroupoid.normalizeDeriv d)
  core_step_decreases : ∀ {a b : A} {p q : Path a b}
    {d₁ d₂ : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q},
    _root_.ComputationalPaths.Path.OmegaGroupoid.CoreStep d₁ d₂ →
      (_root_.ComputationalPaths.Path.OmegaGroupoid.kboWeight d₂ <
          _root_.ComputationalPaths.Path.OmegaGroupoid.kboWeight d₁) ∨
        (_root_.ComputationalPaths.Path.OmegaGroupoid.kboWeight d₂ =
            _root_.ComputationalPaths.Path.OmegaGroupoid.kboWeight d₁ ∧
          _root_.ComputationalPaths.Path.OmegaGroupoid.redexCount d₂ <
            _root_.ComputationalPaths.Path.OmegaGroupoid.redexCount d₁)
  normalization_bridge : ∀ {a b : A} {p q : Path a b}
    (d : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₃ d
      (_root_.ComputationalPaths.Path.OmegaGroupoid.normalizeDeriv d)

  /- Explicit pentagon routes and their proof-relevant coherence. -/
  pentagon_right_route : ∀ {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e),
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k)))
  pentagon_left_route : ∀ {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e),
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k)))
  pentagon_route_step_counts : ∀ {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e),
    rwEqStepCount (pentagon_right_route f g h k) = 2 ∧
      rwEqStepCount (pentagon_left_route f g h k) = 3
  pentagon_routes_distinct : ∀ {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e),
    pentagon_right_route f g h k ≠ pentagon_left_route f g h k
  pentagon_coherence : ∀ {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e),
    _root_.ComputationalPaths.Path.OmegaGroupoid.RwEq₃
      (pentagon_right_route f g h k) (pentagon_left_route f g h k)

  /- Explicit triangle routes and their proof-relevant coherence. -/
  triangle_left_route : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    RwEq
      (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g)
  triangle_right_route : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    RwEq
      (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g)
  triangle_route_step_counts : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    rwEqStepCount (triangle_left_route f g) = 2 ∧
      rwEqStepCount (triangle_right_route f g) = 1
  triangle_routes_distinct : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    triangle_left_route f g ≠ triangle_right_route f g
  triangle_coherence : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    _root_.ComputationalPaths.Path.OmegaGroupoid.RwEq₃
      (triangle_left_route f g) (triangle_right_route f g)

  /- A second critical-pair family and the 2-loop consequence. -/
  inverse_route_assoc_then_cancel : ∀ {a b : A} (p : Path a b),
    RwEq (Path.trans (Path.trans p (Path.symm p)) p) p
  inverse_route_cancel_then_unit : ∀ {a b : A} (p : Path a b),
    RwEq (Path.trans (Path.trans p (Path.symm p)) p) p
  inverse_coherence : ∀ {a b : A} (p : Path a b),
    _root_.ComputationalPaths.Path.OmegaGroupoid.RwEq₃
      (inverse_route_assoc_then_cancel p)
      (inverse_route_cancel_then_unit p)
  interchange_coherence : ∀ {a b c : A}
    {p p' p'' : Path a b} {q q' q'' : Path b c}
    (α : RwEq p p') (β : RwEq p' p'')
    (γ : RwEq q q') (δ : RwEq q' q''),
    _root_.ComputationalPaths.Path.OmegaGroupoid.RwEq₃
      (_root_.ComputationalPaths.EckmannHilton.hcomp
        (_root_.ComputationalPaths.EckmannHilton.vcomp α β)
        (_root_.ComputationalPaths.EckmannHilton.vcomp γ δ))
      (_root_.ComputationalPaths.EckmannHilton.vcomp
        (_root_.ComputationalPaths.EckmannHilton.hcomp α γ)
        (_root_.ComputationalPaths.EckmannHilton.hcomp β δ))
  eckmann_hilton : ∀ {a : A}
    (α β : _root_.ComputationalPaths.EckmannHilton.TwoLoop A a),
    _root_.ComputationalPaths.Path.OmegaGroupoid.RwEq₃
      (_root_.ComputationalPaths.EckmannHilton.vcomp α β)
      (_root_.ComputationalPaths.EckmannHilton.vcomp β α)

  /- Explicitly record where syntax remains nontrivial. -/
  path_trace_nontrivial : ∀ (a : A),
    Path.ofEq (rfl : a = a) ≠ Path.refl a
  two_cell_syntax_nontrivial : ∀ {a b : A} (p : Path a b),
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.refl p ≠
      _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂.vcomp
        (.refl p) (.refl p)
  three_cell_syntax_nontrivial : ∀ {a b : A} {p q : Path a b}
    (d : _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₂ p q),
    _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₃.refl d ≠
      _root_.ComputationalPaths.Path.OmegaGroupoid.Derivation₃.step
        (_root_.ComputationalPaths.Path.OmegaGroupoid.MetaStep₃.rweq_transport
          (d₁ := d) (d₂ := d) rfl)

end PalomarOmegaGroupoid
end Path
end ComputationalPaths
