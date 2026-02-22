import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths.Path.OmegaGroupoidCompPaths

universe u

noncomputable def pentagon_identity {A : Type u} {a b c d e : A}
    (p : ComputationalPaths.Path a b) (q : ComputationalPaths.Path b c)
    (r : ComputationalPaths.Path c d) (s : ComputationalPaths.Path d e) :
    Eq.trans
      (ComputationalPaths.Path.trans_assoc (ComputationalPaths.Path.trans p q) r s)
      (ComputationalPaths.Path.trans_assoc p q (ComputationalPaths.Path.trans r s)) =
      Eq.trans
        (_root_.congrArg (fun t => ComputationalPaths.Path.trans t s)
          (ComputationalPaths.Path.trans_assoc p q r))
        (Eq.trans
          (ComputationalPaths.Path.trans_assoc p (ComputationalPaths.Path.trans q r) s)
          (_root_.congrArg (fun t => ComputationalPaths.Path.trans p t)
            (ComputationalPaths.Path.trans_assoc q r s))) := by
  simpa using ComputationalPaths.Path.trans_assoc_pentagon (p := p) (q := q) (r := r) (s := s)

noncomputable def triangle_identity {A : Type u} {a b c : A}
    (p : ComputationalPaths.Path a b) (q : ComputationalPaths.Path b c) :
    Eq.trans
      (ComputationalPaths.Path.trans_assoc p (ComputationalPaths.Path.refl b) q)
      (_root_.congrArg (fun t => ComputationalPaths.Path.trans p t)
        (ComputationalPaths.Path.trans_refl_left q)) =
      _root_.congrArg (fun t => ComputationalPaths.Path.trans t q)
        (ComputationalPaths.Path.trans_refl_right p) := by
  rfl  -- both sides are proofs of the same Eq proposition; definitional proof irrelevance

noncomputable def mac_lane_coherence_paths {A : Type u} {a b c d e : A}
    (p : ComputationalPaths.Path a b) (q : ComputationalPaths.Path b c)
    (r : ComputationalPaths.Path c d) (s : ComputationalPaths.Path d e)
    (h₁ h₂ :
      ComputationalPaths.Path.trans
          (ComputationalPaths.Path.trans (ComputationalPaths.Path.trans p q) r) s =
        ComputationalPaths.Path.trans p
          (ComputationalPaths.Path.trans q (ComputationalPaths.Path.trans r s))) :
    h₁ = h₂ := by
  exact ComputationalPaths.Path.mac_lane_coherence p q r s h₁ h₂

noncomputable def eckmann_hilton_two_cells {A : Type u} {a b : A}
    {p : ComputationalPaths.Path a b} (α β : p = p) :
    Eq.trans α β = Eq.trans β α := by
  exact ComputationalPaths.Path.eckmann_hilton_two_paths α β

end ComputationalPaths.Path.OmegaGroupoidCompPaths
