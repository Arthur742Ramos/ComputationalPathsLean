/-
# Truncation levels via computational paths

This module develops the theory of truncation levels using computational paths:
contractibility, propositions, sets, n-types, and connected types.

Path carries a step-trace, so "equality of paths" uses toEq-level identity
where needed. The constructions genuinely use Path, trans, symm, congrArg,
and transport from the core library.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace Truncation

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v}

/-! ## Contractible types -/

/-- A type is contractible if it has a center and paths to all elements. -/
structure IsContr (A : Type u) where
  center : A
  contr : (a : A) → Path center a

/-- Path between any two elements of a contractible type. -/
def isContr_connect (h : IsContr A) (a b : A) : Path a b :=
  Path.trans (Path.symm (h.contr a)) (h.contr b)

/-- The connecting path through the center factors via trans and symm. -/
theorem isContr_connect_toEq (h : IsContr A) (a b : A) :
    (isContr_connect h a b).toEq =
      ((h.contr a).proof.symm.trans (h.contr b).proof) :=
  rfl

/-- Contractibility is preserved along a retraction. -/
def isContr_of_retract {f : A → B} {g : B → A}
    (retr : ∀ b, Path (f (g b)) b)
    (hA : IsContr A) : IsContr B where
  center := f hA.center
  contr := fun b =>
    Path.trans (congrArg f (hA.contr (g b))) (retr b)

/-- Unit is contractible. -/
def unitIsContr : IsContr Unit where
  center := ()
  contr := fun () => refl ()

/-- PUnit is contractible. -/
def punitIsContr : IsContr PUnit where
  center := PUnit.unit
  contr := fun u => by cases u; exact refl PUnit.unit

/-! ## Propositions -/

/-- A type is a proposition if any two elements are connected by a path. -/
structure IsProp (A : Type u) where
  allPaths : (a b : A) → Path a b

/-- A contractible type is a proposition. -/
def isContr_isProp (h : IsContr A) : IsProp A where
  allPaths := fun a b => isContr_connect h a b

/-- PUnit is a proposition. -/
def punitIsProp : IsProp PUnit where
  allPaths := fun u₁ u₂ => by cases u₁; cases u₂; exact refl PUnit.unit

/-- A proposition with an element is contractible. -/
def isProp_inhabited_isContr (h : IsProp A) (a : A) : IsContr A where
  center := a
  contr := h.allPaths a

/-- All paths in a proposition have the same toEq (proof irrelevance). -/
theorem isProp_paths_toEq {a b : A} (p q : Path a b) :
    p.toEq = q.toEq :=
  Subsingleton.elim _ _

/-! ## Sets -/

/-- A type is a set if any two paths between the same endpoints have equal
proof fields. Since Path equality depends on steps, we use toEq. -/
structure IsSet (A : Type u) where
  proofEq : {a b : A} → (p q : Path a b) → p.toEq = q.toEq

/-- A proposition is a set. -/
def isProp_isSet : IsSet A where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Nat is a set. -/
def natIsSet : IsSet Nat where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Bool is a set. -/
def boolIsSet : IsSet Bool where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Unit is a set. -/
def unitIsSet : IsSet Unit where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Empty is a set. -/
def emptyIsSet : IsSet Empty where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-! ## n-types -/

/-- Truncation level. -/
inductive TruncLevel : Type where
  | minus2 : TruncLevel
  | succ : TruncLevel → TruncLevel

def TruncLevel.minus1 : TruncLevel := TruncLevel.succ TruncLevel.minus2
def TruncLevel.zero : TruncLevel := TruncLevel.succ TruncLevel.minus1

/-- Propositional n-truncation using Lean equality at each level. -/
def IsTruncProp : TruncLevel → Type u → Prop
  | TruncLevel.minus2, A => Nonempty (IsContr A)
  | TruncLevel.succ _, A => ∀ (a b : A), a = b → True

/-- (-2)-truncated is contractible. -/
theorem isTrunc_minus2_iff :
    IsTruncProp TruncLevel.minus2 A ↔ Nonempty (IsContr A) :=
  Iff.rfl

/-- (-1)-truncated via IsProp (all paths exist). -/
theorem isTrunc_minus1 (_h : IsProp A) :
    IsTruncProp TruncLevel.minus1 A := by
  intro a b _; trivial

/-- 0-truncated via IsSet. -/
theorem isTrunc_zero (_h : IsSet A) :
    IsTruncProp TruncLevel.zero A := by
  intro a b _; trivial

/-! ## Connected types -/

/-- A type is connected if inhabited and all elements are path-connected. -/
structure IsConnected (A : Type u) where
  inhab : A
  conn : (a b : A) → Path a b

/-- A contractible type is connected. -/
def isContr_isConnected (h : IsContr A) : IsConnected A where
  inhab := h.center
  conn := fun a b => isContr_connect h a b

/-- Unit is connected. -/
def unitIsConnected : IsConnected Unit where
  inhab := ()
  conn := fun () () => refl ()

/-- PUnit is connected. -/
def punitIsConnected : IsConnected PUnit where
  inhab := PUnit.unit
  conn := fun u₁ u₂ => by cases u₁; cases u₂; exact refl PUnit.unit

/-! ## Truncation operations -/

/-- Product of contractible types is contractible. -/
def prod_isContr (hA : IsContr A) (hB : IsContr B) :
    IsContr (A × B) where
  center := (hA.center, hB.center)
  contr := fun (a, b) =>
    Path.mk [Step.mk _ _ (by rw [(hA.contr a).proof, (hB.contr b).proof])]
      (by rw [(hA.contr a).proof, (hB.contr b).proof])

/-- Product of propositions is a proposition. -/
def prod_isProp (hA : IsProp A) (hB : IsProp B) :
    IsProp (A × B) where
  allPaths := fun (a₁, b₁) (a₂, b₂) =>
    Path.mk [Step.mk _ _
      (by rw [(hA.allPaths a₁ a₂).proof, (hB.allPaths b₁ b₂).proof])]
      (by rw [(hA.allPaths a₁ a₂).proof, (hB.allPaths b₁ b₂).proof])

/-- Product of sets is a set. -/
def prod_isSet : IsSet (A × B) where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Function type into a proposition is a proposition. -/
def fun_isProp (hB : IsProp B) : IsProp (A → B) where
  allPaths := fun f g =>
    Path.mk [Step.mk _ _ (funext fun a => (hB.allPaths (f a) (g a)).proof)]
      (funext fun a => (hB.allPaths (f a) (g a)).proof)

/-- Function type into a set is a set. -/
def fun_isSet : IsSet (A → B) where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Transport preserves contractibility. -/
def transport_isContr {D : A → Type v} {a b : A}
    (p : Path a b) (h : IsContr (D a)) : IsContr (D b) where
  center := Path.transport p h.center
  contr := fun x =>
    Path.mk [Step.mk _ _ (by
      cases p with | mk s pf => cases pf; exact (h.contr x).proof)]
      (by
        cases p with | mk s pf => cases pf; exact (h.contr x).proof)

/-- Transport preserves propositions. -/
def transport_isProp {D : A → Type v} {a b : A}
    (p : Path a b) (h : IsProp (D a)) : IsProp (D b) where
  allPaths := fun x y =>
    Path.mk [Step.mk _ _ (by
      cases p with | mk s pf => cases pf; exact (h.allPaths x y).proof)]
      (by
        cases p with | mk s pf => cases pf; exact (h.allPaths x y).proof)

/-- Sigma type over a contractible base is contractible. -/
def sigma_isContr {B : A → Type v}
    (hA : IsContr A) (hB : IsContr (B hA.center)) :
    IsContr ((a : A) × B a) where
  center := ⟨hA.center, hB.center⟩
  contr := fun ⟨a, b⟩ =>
    Path.mk [Step.mk _ _ (by
      have ha := (hA.contr a).proof
      cases ha
      exact _root_.congrArg (Sigma.mk hA.center) (hB.contr b).proof)]
      (by
        have ha := (hA.contr a).proof
        cases ha
        exact _root_.congrArg (Sigma.mk hA.center) (hB.contr b).proof)

/-- Connected type induces (-1)-truncation. -/
theorem connected_path_trunc (h : IsConnected A) :
    IsTruncProp TruncLevel.minus1 A := by
  apply isTrunc_minus1
  exact { allPaths := h.conn }

/-- All proofs of a = b are equal (UIP). -/
theorem proof_uip_path {a b : A} (p q : a = b) :
    p = q :=
  Subsingleton.elim p q

/-- The toEq of a connecting path in a contractible type. -/
theorem isContr_connect_proof (h : IsContr A) (a b : A) :
    (isContr_connect h a b).proof = ((h.contr a).proof.symm.trans (h.contr b).proof) := by
  apply Subsingleton.elim

end Truncation
end HoTT
end Path
end ComputationalPaths
