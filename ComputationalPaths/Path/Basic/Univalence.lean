/-
# Univalence axioms for transporting along type equivalences

Provide a lightweight axiomatisation of univalence specialised to the
computational-paths setting.  The axioms postulate that every equivalence
between types induces a propositional equality and that transport along the
induced computational path coincides with the forward map of the equivalence.
These
principles are sufficient to implement the encode-decode argument for the
circle without committing to a full HoTT-style development of univalence.  Apart
from the HIT interfaces, these are the only Lean `axiom`s used in the library
core: coherence laws like `ua_trans` are derived from proof irrelevance of `Eq`
in `Prop`.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u

/-- Axiomatised univalence (propositional form): every `SimpleEquiv` between
types determines an equality between them. -/
axiom uaEq {A B : Type u} : SimpleEquiv A B → A = B

/-- Axiomatised univalence (computational-path form): package `uaEq` as a
`Path` in `Type u`.

We fix the step list to `[]` so coherences like `ua_trans` become theorems
(their proof components live in `Prop`). -/
def ua {A B : Type u} (e : SimpleEquiv A B) : Path (A := Type u) A B :=
  Path.mk [] (uaEq e)

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
theorem ua_trans {A B C : Type u} (e : SimpleEquiv A B) (f : SimpleEquiv B C) :
    Path.trans (ua e) (ua f) = ua (SimpleEquiv.comp e f) := by
  have h :
      (uaEq (A := A) (B := B) e).trans (uaEq (A := B) (B := C) f) =
        uaEq (A := A) (B := C) (SimpleEquiv.comp e f) := by
    exact Subsingleton.elim _ _
  cases h
  simp [ua, Path.trans]

/-- Univalence preserves inverses: the path for the inverse equivalence is
the symmetric path. -/
theorem ua_symm {A B : Type u} (e : SimpleEquiv A B) :
    Path.symm (ua e) = ua (SimpleEquiv.symm e) := by
  have h :
      (uaEq (A := A) (B := B) e).symm =
        uaEq (A := B) (B := A) (SimpleEquiv.symm e) := by
    exact Subsingleton.elim _ _
  cases h
  simp [ua, Path.symm]

/-- Univalence maps the identity equivalence to the identity path. -/
theorem ua_refl (A : Type u) :
    ua (SimpleEquiv.refl A) = Path.refl A := by
  have h : uaEq (A := A) (B := A) (SimpleEquiv.refl A) = rfl := by
    exact Subsingleton.elim _ _
  cases h
  simp [ua, Path.refl]

end Path
end ComputationalPaths
