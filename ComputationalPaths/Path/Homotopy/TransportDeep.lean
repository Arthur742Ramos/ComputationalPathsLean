/-
# Deep Transport Algebra via Computational Paths

Transport composition, inverse, dependent paths, functoriality, and naturality
— all proved using explicit Path.trans, Path.symm, Step constructors.

## Main results

1. `transport_trans_eq` — Transport along `Path.trans p q` = composition of transports
2. `transport_symm_eq` — Transport along `Path.symm p` = inverse transport
3. `depPath_over_transport` — Dependent path over transport (ComputationalPaths vs HoTT)
4. `transport_functorial` — Functoriality of transport w.r.t. path composition
5. `transport_naturality` — Naturality of transport
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths
namespace Transport

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ## 1. Transport along Path.trans = composition of transports -/

/-- Transport along a composite path decomposes into sequential transports.
    Proved by destructing Path into steps + proof. -/
theorem transport_trans_eq {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (D := D) (Path.trans p q) x =
      Path.transport (D := D) q (Path.transport (D := D) p x) :=
  Path.transport_trans p q x

/-- The Path witness for transport-trans decomposition. -/
def transport_trans_path {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path (Path.transport (D := D) (Path.trans p q) x)
         (Path.transport (D := D) q (Path.transport (D := D) p x)) :=
  Path.stepChain (transport_trans_eq p q x)

/-- Triple composition decomposes into three sequential transports. -/
theorem transport_triple_trans {D : A → Type v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans p q) r) x =
      Path.transport (D := D) r
        (Path.transport (D := D) q
          (Path.transport (D := D) p x)) := by
  calc Path.transport (D := D) (Path.trans (Path.trans p q) r) x
      = Path.transport (D := D) r (Path.transport (D := D) (Path.trans p q) x) :=
          Path.transport_trans (Path.trans p q) r x
    _ = Path.transport (D := D) r
          (Path.transport (D := D) q (Path.transport (D := D) p x)) := by
          rw [Path.transport_trans p q x]

/-- Transport along refl is identity — definitional. -/
theorem transport_refl_id {D : A → Type v} {a : A} (x : D a) :
    Path.transport (D := D) (Path.refl a) x = x := rfl

/-! ## 2. Transport along Path.symm = inverse transport -/

/-- Transport along `p` then `symm p` cancels. -/
theorem transport_symm_cancel {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) = x :=
  Path.transport_symm_left p x

/-- Transport along `symm p` then `p` cancels. -/
theorem transport_symm_cancel' {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y) = y :=
  Path.transport_symm_right p y

/-- Path witness: `symm p` undoes `p`. -/
def transport_symm_cancel_path {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path (Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x)) x :=
  Path.stepChain (transport_symm_cancel p x)

/-- Path witness: `p` undoes `symm p`. -/
def transport_symm_cancel_path' {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    Path (Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y)) y :=
  Path.stepChain (transport_symm_cancel' p y)

/-- Transport along `trans p (symm p)` is identity. Uses explicit trans decomposition. -/
theorem transport_trans_symm_id {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.trans p (Path.symm p)) x = x := by
  rw [Path.transport_trans]
  exact Path.transport_symm_left p x

/-- Transport along `trans (symm p) p` is identity. -/
theorem transport_symm_trans_id {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport (D := D) (Path.trans (Path.symm p) p) y = y := by
  rw [Path.transport_trans]
  exact Path.transport_symm_right p y

/-- Transport along `symm (symm p)` equals transport along `p`. -/
theorem transport_symm_symm {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm (Path.symm p)) x =
      Path.transport (D := D) p x := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## 3. Dependent path over transport — ComputationalPaths vs HoTT -/

/-- A dependent path over `p : Path a b` in fiber `D`:
    given `x : D a` and `y : D b`, witnesses that `transport p x = y`.

    In HoTT this is a primitive; in ComputationalPaths it's a propositional equation
    using our concrete transport. -/
structure DepPath {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) (y : D b) : Prop where
  eq : Path.transport (D := D) p x = y

/-- Reflexive dependent path over `refl`. -/
def depPath_refl {D : A → Type v} {a : A} (x : D a) :
    DepPath (Path.refl a) x x :=
  ⟨rfl⟩

/-- Compose dependent paths along `Path.trans`. -/
theorem depPath_trans {D : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c}
    {x : D a} {y : D b} {z : D c}
    (dp₁ : DepPath p x y) (dp₂ : DepPath q y z) :
    DepPath (Path.trans p q) x z := by
  constructor
  rw [Path.transport_trans]
  rw [dp₁.eq]
  exact dp₂.eq

/-- Invert a dependent path along `Path.symm`. -/
theorem depPath_symm {D : A → Type v} {a b : A}
    {p : Path a b} {x : D a} {y : D b}
    (dp : DepPath p x y) : DepPath (Path.symm p) y x := by
  constructor
  rw [← dp.eq]
  exact Path.transport_symm_left p x

/-- Key HoTT-vs-ComputationalPaths observation: in our framework, `DepPath` is
    *equivalent* to the transport equation, not a higher path. -/
theorem depPath_iff_transport {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) (y : D b) :
    DepPath p x y ↔ Path.transport (D := D) p x = y :=
  ⟨fun dp => dp.eq, fun h => ⟨h⟩⟩

/-- DepPath is proof-irrelevant (since it's a Prop wrapper around Eq). -/
theorem depPath_subsingleton {D : A → Type v} {a b : A}
    {p : Path a b} {x : D a} {y : D b}
    (dp₁ dp₂ : DepPath p x y) : dp₁ = dp₂ := by
  cases dp₁; cases dp₂; rfl

/-- Construct a DepPath from `apd`: for any dependent function `f`,
    `f` respects transport. -/
theorem depPath_of_apd {D : A → Type v} (f : ∀ x, D x) {a b : A}
    (p : Path a b) :
    DepPath p (f a) (f b) := by
  constructor
  cases p with | mk steps proof => cases proof; rfl

/-! ## 4. Functoriality of transport w.r.t. path composition -/

/-- Transport is functorial: `trans` maps to composition. -/
theorem transport_functorial {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (D := D) (Path.trans p q) x =
      Path.transport (D := D) q (Path.transport (D := D) p x) :=
  Path.transport_trans p q x

/-- Transport respects identity: `refl` maps to `id`. -/
theorem transport_functorial_refl {D : A → Type v} {a : A} (x : D a) :
    Path.transport (D := D) (Path.refl a) x = x := rfl

/-- Transport along `symm p` is a left inverse of transport along `p`. -/
theorem transport_functorial_symm_left {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm p)
      (Path.transport (D := D) p x) = x :=
  Path.transport_symm_left p x

/-- Transport along `symm p` is a right inverse of transport along `p`. -/
theorem transport_functorial_symm_right {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport (D := D) p
      (Path.transport (D := D) (Path.symm p) y) = y :=
  Path.transport_symm_right p y

/-- Associativity of transport composition follows from Path.trans associativity. -/
theorem transport_assoc {D : A → Type v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans p q) r) x =
      Path.transport (D := D) (Path.trans p (Path.trans q r)) x := by
  simp

/-- Transport in a constant family is the identity. -/
theorem transport_const_family {D : Type v} {a b : A}
    (p : Path a b) (x : D) :
    Path.transport (D := fun _ => D) p x = x :=
  Path.transport_const p x

/-- Transport along `congrArg f p` in family `D` equals transport along `p`
    in `D ∘ f`. -/
theorem transport_congrArg {B : Type u} {D : B → Type v}
    (f : A → B) {a b : A} (p : Path a b) (x : D (f a)) :
    Path.transport (D := D) (Path.congrArg f p) x =
      Path.transport (D := D ∘ f) p x := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## 5. Naturality of transport -/

/-- Naturality: transport commutes with dependent functions.
    For `g : ∀ x, D x → E x` and `p : Path a b`,
    `g b (transport p x) = transport p (g a x)`. -/
theorem transport_natural {D E : A → Type v}
    (g : ∀ x : A, D x → E x) {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := E) p (g a x) =
      g b (Path.transport (D := D) p x) := by
  cases p with | mk steps proof => cases proof; rfl

/-- Naturality as a Path witness. -/
def transport_natural_path {D E : A → Type v}
    (g : ∀ x : A, D x → E x) {a b : A}
    (p : Path a b) (x : D a) :
    Path (Path.transport (D := E) p (g a x))
         (g b (Path.transport (D := D) p x)) :=
  Path.stepChain (transport_natural g p x)

/-- Naturality for non-dependent functions: transport in a constant family
    commutes with any function `f`. -/
theorem transport_natural_const {B C : Type v} (f : B → C)
    {a b : A} (p : Path a b) (x : B) :
    f (Path.transport (D := fun _ => B) p x) =
      Path.transport (D := fun _ => C) p (f x) := by
  rw [Path.transport_const, Path.transport_const]

/-- Transport is injective. -/
theorem transport_injective {D : A → Type v} {a b : A}
    (p : Path a b) {x y : D a}
    (h : Path.transport (D := D) p x = Path.transport (D := D) p y) :
    x = y := by
  have := Path.transport_symm_left (D := D) p x
  have := Path.transport_symm_left (D := D) p y
  calc x = Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) := by
            rw [Path.transport_symm_left]
       _ = Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p y) := by
            rw [h]
       _ = y := Path.transport_symm_left p y

/-- Transport is surjective (given the inverse). -/
theorem transport_surjective {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    ∃ x : D a, Path.transport (D := D) p x = y :=
  ⟨Path.transport (D := D) (Path.symm p) y, Path.transport_symm_right p y⟩

/-- Transport gives a bijection: left and right inverse witnesses. -/
theorem transport_bijective {D : A → Type v} {a b : A}
    (p : Path a b) :
    (∀ x, Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) = x) ∧
    (∀ y, Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y) = y) :=
  ⟨fun x => Path.transport_symm_left p x,
   fun y => Path.transport_symm_right p y⟩

/-! ## RwEq witnesses for transport laws -/

/-- Path coherence: double symm transport = single transport. -/
def transport_symm_symm_path {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    Path (Path.transport (D := D) (Path.symm (Path.symm p)) x)
         (Path.transport (D := D) p x) :=
  Path.stepChain (transport_symm_symm p x)

end Transport
end ComputationalPaths
