/-!
# Higher Route 2-cells for Fiber Sequences

This module packages path-of-path coherence for canonical fiber-sequence routes.
-/

import ComputationalPaths.Path.Homotopy.Fibration

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FiberSequence

universe u

variable {F E B : Type u}

/-- Left- and right-unit computational routes for `proj ∘ incl` are connected by a 2-cell. -/
theorem proj_incl_unit_routes_2cell
    (seq : Fibration.FiberSeq F E B) (f : F) :
    RwEq
      (Path.trans (Path.refl (seq.proj (seq.incl f))) (seq.proj_incl f))
      (Path.trans (seq.proj_incl f) (Path.refl seq.baseB)) := by
  have h₁ :
      RwEq
        (Path.trans (Path.refl (seq.proj (seq.incl f))) (seq.proj_incl f))
        (seq.proj_incl f) :=
    rweq_cmpA_refl_left (seq.proj_incl f)
  have h₂ :
      RwEq
        (Path.trans (seq.proj_incl f) (Path.refl seq.baseB))
        (seq.proj_incl f) :=
    rweq_cmpA_refl_right (seq.proj_incl f)
  exact rweq_trans h₁ (rweq_symm h₂)

/-- Two computational boundary routes for a composed base loop coincide as a path. -/
theorem connecting_map_routes_path {P : B → Type u}
    (b : B) (x₀ : P b) (l₁ l₂ : LoopSpace B b) :
    Path
      (Fibration.connectingMap₁ b x₀ (Path.trans l₁ l₂))
      (Fibration.connectingMap₁ b (Fibration.connectingMap₁ b x₀ l₁) l₂) :=
  Path.ofEq (Fibration.connectingMap₁_trans b x₀ l₁ l₂)

end FiberSequence
end Homotopy
end Path
end ComputationalPaths
