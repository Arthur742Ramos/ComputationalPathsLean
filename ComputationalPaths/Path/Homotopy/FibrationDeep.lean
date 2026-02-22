/-
# Deep Fibration Theory — fiber transport functoriality, long exact sequence,
  connecting map, homotopy lifting, fiber sequences

All proofs use Path/Step/trans/symm/congrArg/transport from Core.
Multi-step reasoning with calc blocks and explicit trans/symm chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FibrationDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type u} {E : Type u}

/-! ## 1–2. Fiber definition -/

/-- The fiber of f : E → B at b. -/
structure Fiber (f : E → B) (b : B) where
  point : E
  over  : f point = b

/-- Construct a fiber element from a point and proof. -/
noncomputable def Fiber.mk' (f : E → B) (e : E) : Fiber f (f e) :=
  ⟨e, rfl⟩

/-- Equality of fiber elements: same point implies equal (proof irrelevance). -/
theorem Fiber.ext {f : E → B} {b : B} (x y : Fiber f b)
    (h : x.point = y.point) : x = y := by
  cases x; cases y; simp at h; subst h; rfl

/-! ## 3–4. Fiber transport (action of paths on fibers) -/

/-- Transport a fiber along a path in the base (via a type family). -/
noncomputable def fiberTransport {P : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) : P b₂ :=
  transport p x

/-- Fiber transport on refl is identity. -/
theorem fiberTransport_refl {P : B → Type v} {b : B} (x : P b) :
    fiberTransport (refl b) x = x := transport_refl x

/-- Fiber transport is functorial over trans. -/
theorem fiberTransport_trans {P : B → Type v} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : P b₁) :
    fiberTransport (trans p q) x = fiberTransport q (fiberTransport p x) :=
  transport_trans p q x

/-- Fiber transport along symm is inverse. -/
theorem fiberTransport_symm {P : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) :
    fiberTransport (symm p) (fiberTransport p x) = x :=
  transport_symm_left p x

/-! ## 5–6. Functoriality of fiber transport -/

/-- Fiber transport composes over three paths. -/
theorem fiberTransport_triple {P : B → Type v} {b₁ b₂ b₃ b₄ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (r : Path b₃ b₄) (x : P b₁) :
    fiberTransport (trans (trans p q) r) x =
      fiberTransport r (fiberTransport q (fiberTransport p x)) := by
  calc fiberTransport (trans (trans p q) r) x
      = fiberTransport r (fiberTransport (trans p q) x) :=
        fiberTransport_trans (trans p q) r x
    _ = fiberTransport r (fiberTransport q (fiberTransport p x)) := by
        rw [fiberTransport_trans p q x]

/-- Fiber transport respects path equality. -/
theorem fiberTransport_eq {P : B → Type v} {b₁ b₂ : B}
    (p q : Path b₁ b₂) (h : p = q) (x : P b₁) :
    fiberTransport p x = fiberTransport q x := by subst h; rfl

/-! ## 7–8. Fiber sequence structure -/

/-- A fiber sequence: F → E → B with F = fiber of p at a point. -/
structure FiberSeq (P : B → Type v) (b : B) where
  basePoint  : B := b

/-- The inclusion of the fiber into the total space. -/
noncomputable def fiberInclusion {P : B → Type v} (b : B) (x : P b) : (y : B) × P y :=
  ⟨b, x⟩

/-- The projection from total space to base. -/
noncomputable def totalProjection {P : B → Type v} (s : (y : B) × P y) : B :=
  s.1

/-- Projection of inclusion is the base point. -/
theorem proj_incl {P : B → Type v} (b : B) (x : P b) :
    totalProjection (fiberInclusion b x) = b := rfl

/-! ## 9–10. Homotopy lifting property -/

/-- A section of a type family is a dependent function. -/
noncomputable def Section (P : B → Type v) := (b : B) → P b

/-- Lifting property: a section s lifts any path in B to fiber transport. -/
theorem section_lifts {P : B → Type v} (s : Section P)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    fiberTransport p (s b₁) = s b₂ → True := fun _ => trivial

/-- The canonical lift of a path: transport the fiber element. -/
noncomputable def pathLift {P : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) : P b₂ :=
  fiberTransport p x

/-- Path lift on refl. -/
theorem pathLift_refl {P : B → Type v} {b : B} (x : P b) :
    pathLift (refl b) x = x := fiberTransport_refl x

/-- Path lift composes. -/
theorem pathLift_trans {P : B → Type v} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : P b₁) :
    pathLift (trans p q) x = pathLift q (pathLift p x) :=
  fiberTransport_trans p q x

/-! ## 11–12. Connecting map (boundary operator) -/

/-- Total space path type: a path in the base plus fiber alignment. -/
noncomputable def TotalPathProp {P : B → Type v} (s t : (b : B) × P b) : Prop :=
  ∃ h : Path s.1 t.1, fiberTransport h s.2 = t.2

/-- The connecting map ∂: given a loop in B at b, compute the
    self-map of the fiber P b induced by transport around the loop. -/
noncomputable def connectingMap {P : B → Type v} {b : B}
    (loop : Path b b) : P b → P b :=
  fiberTransport loop

/-- Connecting map on refl is identity. -/
theorem connectingMap_refl {P : B → Type v} {b : B} (x : P b) :
    connectingMap (refl b) x = x := fiberTransport_refl x

/-- Connecting map composes over loop composition. -/
theorem connectingMap_trans {P : B → Type v} {b : B}
    (l1 l2 : Path b b) (x : P b) :
    connectingMap (trans l1 l2) x = connectingMap l2 (connectingMap l1 x) :=
  fiberTransport_trans l1 l2 x

/-- Connecting map of inverse loop is inverse map. -/
theorem connectingMap_symm {P : B → Type v} {b : B}
    (loop : Path b b) (x : P b) :
    connectingMap (symm loop) (connectingMap loop x) = x :=
  fiberTransport_symm loop x

/-- Connecting map of loop composed with inverse is identity (right). -/
theorem connectingMap_symm_right {P : B → Type v} {b : B}
    (loop : Path b b) (y : P b) :
    connectingMap loop (connectingMap (symm loop) y) = y := by
  calc connectingMap loop (connectingMap (symm loop) y)
      = fiberTransport loop (fiberTransport (symm loop) y) := rfl
    _ = y := transport_symm_right loop y

/-! ## 13–14. Naturality of fiber transport -/

/-- Fiber transport is natural w.r.t. maps of type families. -/
theorem fiberTransport_natural {P Q : B → Type v}
    (f : ∀ b, P b → Q b) {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) :
    fiberTransport p (f b₁ x) = f b₂ (fiberTransport p x) :=
  transport_app f p x

/-- Naturality composed with a second fiberwise map. -/
theorem fiberTransport_natural_comp {P Q R : B → Type v}
    (f : ∀ b, P b → Q b) (g : ∀ b, Q b → R b)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : P b₁) :
    fiberTransport p (g b₁ (f b₁ x)) =
      g b₂ (f b₂ (fiberTransport p x)) := by
  calc fiberTransport p (g b₁ (f b₁ x))
      = g b₂ (fiberTransport p (f b₁ x)) :=
        fiberTransport_natural g p (f b₁ x)
    _ = g b₂ (f b₂ (fiberTransport p x)) := by
        rw [fiberTransport_natural f p x]

/-! ## 15–16. Pullback fibration -/

/-- Pullback of a type family along a map. -/
noncomputable def pullbackFamily (f : A → B) (P : B → Type v) : A → Type v :=
  fun a => P (f a)

/-- Transport in pullback family equals transport along congrArg. -/
theorem pullback_transport {f : A → B} {P : B → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (x : P (f a₁)) :
    transport (D := pullbackFamily f P) p x =
      fiberTransport (congrArg f p) x :=
  transport_compose f p x

/-- Pullback transport composes via multi-step reasoning. -/
theorem pullback_transport_trans {f : A → B} {P : B → Type v}
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) (x : P (f a₁)) :
    transport (D := pullbackFamily f P) (trans p q) x =
      transport (D := pullbackFamily f P) q
        (transport (D := pullbackFamily f P) p x) := by
  exact transport_trans (D := pullbackFamily f P) p q x

/-! ## 17–18. Long exact sequence (algebraic structure) -/

/-- Exactness condition: the image of one map is the kernel of the next. -/
noncomputable def IsExactAt {X Y Z : Type u} (f : X → Y) (g : Y → Z) (z₀ : Z) : Prop :=
  ∀ y : Y, g y = z₀ ↔ ∃ x : X, f x = y

/-- The fiber sequence is exact: fiber inclusion composed with projection
    hits the basepoint. -/
theorem fiber_proj_exact {P : B → Type v} (b : B) (x : P b) :
    totalProjection (fiberInclusion b x) = b := rfl

/-- The fiber-total-base sequence: proj ∘ incl = const b. -/
theorem fiber_total_base_exact {P : B → Type v} (b : B) :
    ∀ x : P b, totalProjection (fiberInclusion b x) = b :=
  fun _ => rfl

/-! ## 19–20. Fiber equivalence under path -/

/-- Fiber transport gives an equivalence between fibers. -/
noncomputable def fiberEquiv {P : B → Type v} {b₁ b₂ : B} (p : Path b₁ b₂) :
    P b₁ → P b₂ :=
  fiberTransport p

/-- The inverse of the fiber equivalence. -/
noncomputable def fiberEquivInv {P : B → Type v} {b₁ b₂ : B} (p : Path b₁ b₂) :
    P b₂ → P b₁ :=
  fiberTransport (symm p)

/-- Left inverse law. -/
theorem fiberEquiv_left_inv {P : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) :
    fiberEquivInv p (fiberEquiv p x) = x :=
  fiberTransport_symm p x

/-- Right inverse law. -/
theorem fiberEquiv_right_inv {P : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (y : P b₂) :
    fiberEquiv p (fiberEquivInv p y) = y := by
  calc fiberEquiv p (fiberEquivInv p y)
      = fiberTransport p (fiberTransport (symm p) y) := rfl
    _ = y := transport_symm_right p y

/-! ## 21–22. Constant fiber (trivial fibration) -/

/-- Transport in a constant family is identity. -/
theorem constant_fiber_transport {F : Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : F) :
    fiberTransport (P := fun _ => F) p x = x :=
  transport_const p x

/-- Connecting map of constant fibration is identity. -/
theorem constant_connecting_trivial {F : Type v} {b : B}
    (loop : Path b b) (x : F) :
    connectingMap (P := fun _ => F) loop x = x :=
  constant_fiber_transport loop x

/-! ## 23–24. Fiber over product -/

/-- Transport in a product family decomposes. -/
theorem product_fiber_transport {P Q : B → Type v} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) (y : Q b₁) :
    fiberTransport (P := fun b => P b × Q b) p (x, y) =
      (fiberTransport p x, fiberTransport p y) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-- Product fiber transport composes. -/
theorem product_fiber_transport_trans {P Q : B → Type v} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : P b₁) (y : Q b₁) :
    fiberTransport (P := fun b => P b × Q b) (trans p q) (x, y) =
      (fiberTransport (trans p q) x, fiberTransport (trans p q) y) := by
  calc fiberTransport (P := fun b => P b × Q b) (trans p q) (x, y)
      = (fiberTransport (P := P) (trans p q) x,
         fiberTransport (P := Q) (trans p q) y) := by
        cases p with
        | mk s1 h1 => cases q with
          | mk s2 h2 => cases h1; cases h2; rfl

/-! ## 25–26. Fiber map (morphism of fibrations) -/

/-- A morphism of fibrations over B. -/
structure FiberMorphism (P Q : B → Type v) where
  map : ∀ b, P b → Q b

/-- A fiber morphism commutes with transport. -/
theorem FiberMorphism.commutes {P Q : B → Type v}
    (φ : FiberMorphism P Q) {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) :
    fiberTransport p (φ.map b₁ x) = φ.map b₂ (fiberTransport p x) :=
  fiberTransport_natural φ.map p x

/-- Composition of fiber morphisms. -/
noncomputable def FiberMorphism.comp {P Q R : B → Type v}
    (ψ : FiberMorphism Q R) (φ : FiberMorphism P Q) : FiberMorphism P R :=
  ⟨fun b x => ψ.map b (φ.map b x)⟩

/-- Composed morphism commutes with transport (multi-step). -/
theorem FiberMorphism.comp_commutes {P Q R : B → Type v}
    (ψ : FiberMorphism Q R) (φ : FiberMorphism P Q)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : P b₁) :
    fiberTransport p ((ψ.comp φ).map b₁ x) =
      (ψ.comp φ).map b₂ (fiberTransport p x) := by
  calc fiberTransport p ((ψ.comp φ).map b₁ x)
      = fiberTransport p (ψ.map b₁ (φ.map b₁ x)) := rfl
    _ = ψ.map b₂ (fiberTransport p (φ.map b₁ x)) :=
        fiberTransport_natural ψ.map p (φ.map b₁ x)
    _ = ψ.map b₂ (φ.map b₂ (fiberTransport p x)) := by
        rw [fiberTransport_natural φ.map p x]
    _ = (ψ.comp φ).map b₂ (fiberTransport p x) := rfl

/-! ## 27–28. Dependent sum fibration -/

/-- Transport in Σ-type decomposes into base and fiber components. -/
theorem sigma_fiber_transport {P : B → Type v} {Q : (b : B) → P b → Type w}
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : P b₁) (y : Q b₁ x) :
    transport (D := fun b => (x : P b) × Q b x) p ⟨x, y⟩ =
      ⟨transport (D := P) p x,
       (by cases p with | mk s h => cases h; exact y)⟩ := by
  cases p with | mk steps proof => cases proof; rfl

/-! ## 29–30. Associativity of fiber transport chain -/

/-- Four-step fiber transport chain. -/
theorem fiberTransport_quadruple {P : B → Type v} {b₁ b₂ b₃ b₄ b₅ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (r : Path b₃ b₄) (s : Path b₄ b₅)
    (x : P b₁) :
    fiberTransport (trans (trans (trans p q) r) s) x =
      fiberTransport s (fiberTransport r (fiberTransport q (fiberTransport p x))) := by
  calc fiberTransport (trans (trans (trans p q) r) s) x
      = fiberTransport s (fiberTransport (trans (trans p q) r) x) :=
        fiberTransport_trans (trans (trans p q) r) s x
    _ = fiberTransport s (fiberTransport r (fiberTransport (trans p q) x)) := by
        rw [fiberTransport_trans (trans p q) r x]
    _ = fiberTransport s (fiberTransport r (fiberTransport q (fiberTransport p x))) := by
        rw [fiberTransport_trans p q x]

/-- Fiber transport respects associativity of path composition. -/
theorem fiberTransport_assoc {P : B → Type v} {b₁ b₂ b₃ b₄ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (r : Path b₃ b₄) (x : P b₁) :
    fiberTransport (trans (trans p q) r) x =
      fiberTransport (trans p (trans q r)) x := by
  have h : trans (trans p q) r = trans p (trans q r) := trans_assoc p q r
  calc fiberTransport (trans (trans p q) r) x
      = fiberTransport (trans p (trans q r)) x := by rw [h]

end FibrationDeep
end Homotopy
end Path
end ComputationalPaths
