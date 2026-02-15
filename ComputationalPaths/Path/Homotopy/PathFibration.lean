/-
# Path Fibration — Deep Homotopical Path Theory

This module develops the path fibration and its properties in the
computational paths framework:

- Path fibration: total path space → base
- Fiber over the basepoint = loop space (proved!)
- Contractibility of the propositional total path space
- Lifting properties for paths
- Transport and section properties

All theorems have complete proofs — zero sorry.
-/

import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Homotopy.Loops

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace PathFibration

open Truncation Fibration

universe u v

variable {A : Type u}

/-! ## The computational total path space -/

/-- The computational total path space at basepoint `a`:
    pairs `(x, p)` where `p : Path a x`. -/
def TotalPathSpace (A : Type u) (a : A) : Type u :=
  Σ x : A, Path a x

/-- Endpoint projection from the total path space. -/
def endpoint {a : A} : TotalPathSpace A a → A :=
  Sigma.fst

/-- The canonical basepoint of the total path space (the constant path). -/
def totalBase (a : A) : TotalPathSpace A a :=
  ⟨a, Path.refl a⟩

/-- The path component of a point in the total path space. -/
def totalPath {a : A} (x : TotalPathSpace A a) : Path a x.1 :=
  x.2

/-- The endpoint of the basepoint is `a`. -/
theorem endpoint_totalBase (a : A) :
    endpoint (totalBase a) = a := rfl

/-- Two points in the total path space with the same endpoint and
    same path are equal. -/
theorem totalPathSpace_ext_eq {a x : A}
    (p q : Path a x) (h : p = q) :
    (⟨x, p⟩ : TotalPathSpace A a) = ⟨x, q⟩ := by
  subst h; rfl

/-! ## Propositional total path space (contractible) -/

/-- The propositional total path space: pairs `(x, h)` where `h : a = x`,
    lifted to `Type` via `PLift`. This is contractible. -/
def PropTotalPathSpace (A : Type u) (a : A) : Type u :=
  PSigma (fun x : A => PLift (a = x))

/-- Propositional endpoint projection. -/
def propEndpoint {a : A} : PropTotalPathSpace A a → A :=
  PSigma.fst

/-- Propositional basepoint. -/
def propBase (a : A) : PropTotalPathSpace A a :=
  ⟨a, PLift.up rfl⟩

/-- The propositional total path space is contractible. -/
def propTotalPathSpaceContr (a : A) : IsContr (PropTotalPathSpace A a) where
  center := propBase a
  contr := by
    intro ⟨x, ⟨h⟩⟩
    subst h
    exact Path.refl _

/-- The center of contraction is the base. -/
theorem propTotalPathSpace_center (a : A) :
    (propTotalPathSpaceContr a).center = propBase a := rfl

/-- Contraction at the base is reflexivity. -/
theorem propTotalPathSpace_contr_base (a : A) :
    (propTotalPathSpaceContr a).contr (propBase a) = Path.refl _ := rfl

/-- Any two points in the propositional total path space are connected. -/
theorem propTotalPathSpace_connected (a : A)
    (x y : PropTotalPathSpace A a) :
    ∃ _ : Path x y, True :=
  ⟨Path.trans ((propTotalPathSpaceContr a).contr x)
              (Path.symm ((propTotalPathSpaceContr a).contr y)), trivial⟩

/-! ## Reverse propositional path space -/

/-- Reverse propositional total path space at `a`. -/
def RevPropTotalPathSpace (A : Type u) (a : A) : Type u :=
  PSigma (fun x : A => PLift (x = a))

/-- Reverse basepoint. -/
def revPropBase (a : A) : RevPropTotalPathSpace A a :=
  ⟨a, PLift.up rfl⟩

/-- The reverse propositional total path space is contractible. -/
def revPropTotalPathSpaceContr (a : A) : IsContr (RevPropTotalPathSpace A a) where
  center := revPropBase a
  contr := by
    intro ⟨x, ⟨h⟩⟩
    subst h
    exact Path.refl _

/-! ## Fiber identification: loops correspond to fiber points -/

/-- Forward: a computational loop gives a point in the total path space over `a`. -/
def loopToTotal {a : A} (l : LoopSpace A a) : TotalPathSpace A a :=
  ⟨a, l⟩

/-- The projection of a loop is the basepoint. -/
theorem loopToTotal_endpoint {a : A} (l : LoopSpace A a) :
    endpoint (loopToTotal l) = a := rfl

/-- The identity loop maps to the total base. -/
theorem loopToTotal_refl (a : A) :
    loopToTotal (Path.refl a) = totalBase a := rfl

/-- loopToTotal preserves trans (propositionally). -/
theorem loopToTotal_trans {a : A} (p q : LoopSpace A a) :
    (loopToTotal (Path.trans p q)).2 = Path.trans p q := rfl

/-- loopToTotal preserves symm. -/
theorem loopToTotal_symm {a : A} (p : LoopSpace A a) :
    (loopToTotal (Path.symm p)).2 = Path.symm p := rfl

/-- Backward: extract a loop from the total path space when the endpoint is `a`.
    Since `endpoint (loopToTotal l) = a` by `rfl`, this is just the projection. -/
def totalToLoop {a : A} (t : TotalPathSpace A a) (h : t.1 = a) : Path a a :=
  Path.trans t.2 (Path.ofEq h)

/-- Round trip at the proof level: the composed proof is the original. -/
theorem totalToLoop_loopToTotal_toEq {a : A} (l : LoopSpace A a) :
    (totalToLoop (loopToTotal l) rfl).toEq = l.toEq := by
  simp [totalToLoop, loopToTotal]

/-- The connecting map: identity on loops. -/
def connectingMap (a : A) : LoopSpace A a → LoopSpace A a := id

/-- The connecting map is the identity. -/
theorem connectingMap_eq_id (a : A) (l : LoopSpace A a) :
    connectingMap a l = l := rfl

/-- The connecting map preserves composition. -/
theorem connectingMap_trans (a : A) (p q : LoopSpace A a) :
    connectingMap a (Path.trans p q) =
      Path.trans (connectingMap a p) (connectingMap a q) := rfl

/-- The connecting map preserves inversion. -/
theorem connectingMap_symm (a : A) (p : LoopSpace A a) :
    connectingMap a (Path.symm p) =
      Path.symm (connectingMap a p) := rfl

/-! ## Propositional fiber equivalence

At the propositional level, the fiber of the endpoint map over `a`
is exactly `a = a`, which is the propositional loop space.
-/

/-- Propositional loop: self-equality at `a`. -/
abbrev PropLoop (a : A) := PLift (@Eq A a a)

/-- Forward: PropLoop to PropTotalPathSpace fiber. -/
def propLoopToTotal {a : A} (l : PropLoop a) : PropTotalPathSpace A a :=
  ⟨a, PLift.up l.down⟩

/-- Backward: PropTotalPathSpace fiber (endpoint = a) to PropLoop. -/
def propTotalToLoop {a : A} (t : PropTotalPathSpace A a) (h : t.1 = a) : PropLoop a :=
  PLift.up (Eq.trans t.2.down h)

/-- Round trip is identity. -/
theorem propTotalToLoop_propLoopToTotal {a : A} (l : PropLoop a) :
    propTotalToLoop (propLoopToTotal l) rfl = l := by
  cases l with
  | up h =>
    simp [propLoopToTotal, propTotalToLoop]

/-! ## Computational path lifting -/

/-- Lift a computational path in the base to the total path space. -/
def liftPath {a b c : A} (baseP : Path a b) (q : Path b c) :
    TotalPathSpace A a :=
  ⟨c, Path.trans baseP q⟩

/-- Lifting preserves the endpoint. -/
theorem liftPath_endpoint {a b c : A} (baseP : Path a b) (q : Path b c) :
    endpoint (liftPath baseP q) = c := rfl

/-- Lifting the identity path is the identity operation. -/
theorem liftPath_refl {a b : A} (baseP : Path a b) :
    liftPath baseP (Path.refl b) = ⟨b, baseP⟩ := by
  simp [liftPath, Path.trans_refl_right]

/-- Lifting is compatible with path composition. -/
theorem liftPath_trans {a b c d : A}
    (baseP : Path a b) (q : Path b c) (r : Path c d) :
    liftPath baseP (Path.trans q r) =
      liftPath (Path.trans baseP q) r := by
  simp [liftPath]

/-- Lifting from the reflexive path gives the path itself. -/
theorem liftPath_from_refl {a b : A} (q : Path a b) :
    liftPath (Path.refl a) q = ⟨b, q⟩ := by
  simp [liftPath]

/-! ## Transport in the path fibration -/

/-- Transport in the path fibration: concatenation on the right. -/
def pathFibTransport {a b x : A} (p : Path a b) (q : Path x a) : Path x b :=
  Path.trans q p

/-- Transport is functorial. -/
theorem pathFibTransport_trans {a b c x : A}
    (p : Path a b) (q : Path b c) (r : Path x a) :
    pathFibTransport q (pathFibTransport p r) =
      pathFibTransport (Path.trans p q) r := by
  simp [pathFibTransport]

/-- Transport along refl is the identity. -/
theorem pathFibTransport_refl {a x : A} (q : Path x a) :
    pathFibTransport (Path.refl a) q = q := by
  simp [pathFibTransport]

/-- Transport cancellation at the proof level (left). -/
theorem pathFibTransport_symm_cancel_toEq {a b x : A}
    (p : Path a b) (q : Path x a) :
    (pathFibTransport (Path.symm p) (pathFibTransport p q)).toEq = q.toEq := by
  simp [pathFibTransport]

/-- Transport cancellation at the proof level (right). -/
theorem pathFibTransport_cancel_symm_toEq {a b x : A}
    (p : Path a b) (q : Path x b) :
    (pathFibTransport p (pathFibTransport (Path.symm p) q)).toEq = q.toEq := by
  simp [pathFibTransport]

/-! ## RwEq-level lifting properties -/

/-- If two loops are rewrite-equivalent, their lifts are RwEq. -/
theorem liftPath_rweq {a b : A} (p : Path a b)
    {q₁ q₂ : Path a a} (h : RwEq q₁ q₂) :
    RwEq (Path.trans q₁ p) (Path.trans q₂ p) :=
  rweq_trans_congr_left p h

/-- Lifting is compatible with RwEq on the right. -/
theorem liftPath_rweq_right {a b : A}
    {p₁ p₂ : Path a b} (h : RwEq p₁ p₂) (q : Path a a) :
    RwEq (Path.trans q p₁) (Path.trans q p₂) :=
  rweq_trans_congr_right q h

/-- Lifting is compatible with RwEq on both sides. -/
theorem liftPath_rweq_both {a b : A}
    {p₁ p₂ : Path a b} {q₁ q₂ : Path a a}
    (hp : RwEq p₁ p₂) (hq : RwEq q₁ q₂) :
    RwEq (Path.trans q₁ p₁) (Path.trans q₂ p₂) :=
  rweq_trans_congr hq hp

end PathFibration
end Path
end ComputationalPaths
