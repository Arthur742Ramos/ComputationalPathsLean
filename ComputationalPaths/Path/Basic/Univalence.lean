/-
# Univalence axioms for transporting along type equivalences

Provide a lightweight axiomatisation of univalence specialised to the
computational-paths setting.  The axioms postulate that every equivalence
between types induces a computational path between them and that transport
along this path coincides with the forward map of the equivalence.  These
principles are sufficient to implement the encode-decode argument for the
circle without committing to a full HoTT-style development of univalence.  Apart
from the circle HIT interface, these are the only axioms used in the project.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u

/-- Axiomatised univalence: every equivalence between types determines a
computational path between them.  We restrict to the lightweight
`SimpleEquiv` structure to avoid additional dependencies. -/
axiom ua {A B : Type u} : SimpleEquiv A B → Path (A := Type u) A B

/-- Transport along the path produced by `ua` computes to the forward map of
the equivalence. -/
axiom ua_beta {A B : Type u} (e : SimpleEquiv A B) (x : A) :
    Path.transport (A := Type u) (D := fun X => X) (ua (A := A) (B := B) e) x =
      e.toFun x

/-- Transporting along the inverse univalence path recovers the inverse map of
the equivalence. -/
@[simp] theorem ua_beta_symm {A B : Type u} (e : SimpleEquiv A B) (y : B) :
    Path.transport (A := Type u) (D := fun X => X)
        (Path.symm (ua (A := A) (B := B) e)) y =
      e.invFun y := by
  -- Rewrite the transported argument using the `ua_beta` axiom together with
  -- the equivalence's right inverse.
  have hTransport :=
    ua_beta (A := A) (B := B) e (x := e.invFun y)
  have hEval : Path.transport (A := Type u) (D := fun X => X)
      (ua (A := A) (B := B) e) (e.invFun y) = y := by
    simp [hTransport, e.right_inv y]
  -- Cancel the forward transport via the general `transport_symm_left` lemma.
  have hSymm :=
    Path.transport_symm_left (A := Type u) (D := fun X => X)
      (p := ua (A := A) (B := B) e) (x := e.invFun y)
  simp [hEval] at hSymm
  exact hSymm

/-- Univalence preserves composition: the path for a composite equivalence is
the concatenation of the paths. -/
axiom ua_trans {A B C : Type u} (e : SimpleEquiv A B) (f : SimpleEquiv B C) :
    Path.trans (ua e) (ua f) = ua (SimpleEquiv.comp e f)

/-- Univalence preserves inverses: the path for the inverse equivalence is
the symmetric path. -/
axiom ua_symm {A B : Type u} (e : SimpleEquiv A B) :
    Path.symm (ua e) = ua (SimpleEquiv.symm e)

end Path
end ComputationalPaths
