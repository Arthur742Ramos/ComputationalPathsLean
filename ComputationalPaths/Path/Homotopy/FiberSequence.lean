import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.Loops

/-!
# Fiber-sequence higher-path routes

This module packages 2-cell witnesses showing that alternate computational
routes in fiber-sequence constructions are connected.
-/

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FiberSequence

universe u

/-- A 2-cell between parallel computational paths. -/
abbrev TwoCell {A : Type u} {x y : A} (p q : Path x y) : Prop := RwEq p q

/-- Projection in a fiber sequence preserves the associator 2-cell on loops. -/
theorem proj_assoc_two_cell {F E B : Type u}
    (seq : Fibration.FiberSeq F E B) {e : E}
    (p q r : LoopSpace E e) :
    TwoCell
      (Fibration.inducedLoopMap seq.proj e (Path.trans (Path.trans p q) r))
      (Fibration.inducedLoopMap seq.proj e (Path.trans p (Path.trans q r))) := by
  unfold Fibration.inducedLoopMap
  exact rweq_context_map_of_rweq ⟨seq.proj⟩ (rweq_tt p q r)

/-- Fiber inclusion also preserves the same 2-cell route. -/
theorem incl_assoc_two_cell {F E B : Type u}
    (seq : Fibration.FiberSeq F E B) {f₀ : F}
    (p q r : LoopSpace F f₀) :
    TwoCell
      (Fibration.inducedLoopMap (Fibration.FiberSeq.incl seq) f₀
        (Path.trans (Path.trans p q) r))
      (Fibration.inducedLoopMap (Fibration.FiberSeq.incl seq) f₀
        (Path.trans p (Path.trans q r))) := by
  unfold Fibration.inducedLoopMap Fibration.FiberSeq.incl
  exact rweq_context_map_of_rweq ⟨fun f => (seq.toFiber f).point⟩ (rweq_tt p q r)

/-- Connecting-map composition has two equal computational routes. -/
noncomputable def connectingMap_trans_path {B : Type u} {P : B → Type u}
    (b : B) (x₀ : P b) (l₁ l₂ : LoopSpace B b) :
    Path
      (Fibration.connectingMap₁ b x₀ (Path.trans l₁ l₂))
      (Fibration.connectingMap₁ b (Fibration.connectingMap₁ b x₀ l₁) l₂) :=
  Path.stepChain (Fibration.connectingMap₁_trans (P := P) b x₀ l₁ l₂)

/-! ## Path-exact sequence routes -/

/-- Left-associated route in a fiber-sequence loop term. -/
noncomputable def exactRouteLeft {A : Type u} {a : A} (p q r : LoopSpace A a) : LoopSpace A a :=
  Path.trans (Path.trans p q) r

/-- Right-associated route in a fiber-sequence loop term. -/
noncomputable def exactRouteRight {A : Type u} {a : A} (p q r : LoopSpace A a) : LoopSpace A a :=
  Path.trans p (Path.trans q r)

/-- Exactness rerouting is witnessed by the associator 2-cell. -/
theorem exact_route_two_cell {A : Type u} {a : A} (p q r : LoopSpace A a) :
    TwoCell (exactRouteLeft p q r) (exactRouteRight p q r) :=
  rweq_tt p q r

/-- Projection carries exact-route rerouting to exact-route rerouting. -/
theorem proj_exact_route_two_cell {F E B : Type u}
    (seq : Fibration.FiberSeq F E B) {e : E} (p q r : LoopSpace E e) :
    TwoCell
      (Fibration.inducedLoopMap seq.proj e (exactRouteLeft p q r))
      (Fibration.inducedLoopMap seq.proj e (exactRouteRight p q r)) := by
  simpa [exactRouteLeft, exactRouteRight]
    using proj_assoc_two_cell (seq := seq) (p := p) (q := q) (r := r)

/-- Inclusion carries exact-route rerouting to exact-route rerouting. -/
theorem incl_exact_route_two_cell {F E B : Type u}
    (seq : Fibration.FiberSeq F E B) {f₀ : F} (p q r : LoopSpace F f₀) :
    TwoCell
      (Fibration.inducedLoopMap (Fibration.FiberSeq.incl seq) f₀ (exactRouteLeft p q r))
      (Fibration.inducedLoopMap (Fibration.FiberSeq.incl seq) f₀ (exactRouteRight p q r)) := by
  simpa [exactRouteLeft, exactRouteRight]
    using incl_assoc_two_cell (seq := seq) (p := p) (q := q) (r := r)

/-- Connecting map exactness route as a computational path witness. -/
noncomputable def connecting_exact_route_path {B : Type u} {P : B → Type u}
    (b : B) (x₀ : P b) (l₁ l₂ : LoopSpace B b) :
    Path
      (Fibration.connectingMap₁ b x₀ (Path.trans l₁ l₂))
      (Fibration.connectingMap₁ b (Fibration.connectingMap₁ b x₀ l₁) l₂) :=
  connectingMap_trans_path b x₀ l₁ l₂

end FiberSequence
end Homotopy
end Path
end ComputationalPaths
