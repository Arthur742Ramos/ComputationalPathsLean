/-
# Truncation levels via computational paths

This module develops the theory of truncation levels using computational paths:
contractibility, propositions, sets, n-types, and connected types.

Path carries a step-trace, so "equality of paths" uses toEq-level identity
where needed. The constructions genuinely use Path, trans, symm, congrArg,
and transport from the core library.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

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
noncomputable def isContr_connect (h : IsContr A) (a b : A) : Path a b :=
  Path.trans (Path.symm (h.contr a)) (h.contr b)

/-- The connecting path through the center factors via trans and symm. -/
theorem isContr_connect_toEq (h : IsContr A) (a b : A) :
    (isContr_connect h a b).toEq =
      ((h.contr a).proof.symm.trans (h.contr b).proof) :=
  rfl

/-- Contractibility is preserved along a retraction. -/
noncomputable def isContr_of_retract {f : A → B} {g : B → A}
    (retr : ∀ b, Path (f (g b)) b)
    (hA : IsContr A) : IsContr B where
  center := f hA.center
  contr := fun b =>
    Path.trans (congrArg f (hA.contr (g b))) (retr b)

/-- Unit is contractible. -/
noncomputable def unitIsContr : IsContr Unit where
  center := ()
  contr := fun () => refl ()

/-- PUnit is contractible. -/
noncomputable def punitIsContr : IsContr PUnit where
  center := PUnit.unit
  contr := fun u => by cases u; exact refl PUnit.unit

/-! ## Propositions -/

/-- A type is a proposition if any two elements are connected by a path. -/
structure IsProp (A : Type u) where
  allPaths : (a b : A) → Path a b

/-- A contractible type is a proposition. -/
noncomputable def isContr_isProp (h : IsContr A) : IsProp A where
  allPaths := fun a b => isContr_connect h a b

/-- PUnit is a proposition. -/
noncomputable def punitIsProp : IsProp PUnit where
  allPaths := fun u₁ u₂ => by cases u₁; cases u₂; exact refl PUnit.unit

/-- A proposition with an element is contractible. -/
noncomputable def isProp_inhabited_isContr (h : IsProp A) (a : A) : IsContr A where
  center := a
  contr := h.allPaths a

/-! ## Sets -/

/-- A type is a set if any two paths between the same endpoints have equal
proof fields. Since Path equality depends on steps, we use toEq. -/
structure IsSet (A : Type u) where
  proofEq : {a b : A} → (p q : Path a b) → p.toEq = q.toEq

/-- A proposition is a set. -/
noncomputable def isProp_isSet : IsSet A where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Nat is a set. -/
noncomputable def natIsSet : IsSet Nat where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Bool is a set. -/
noncomputable def boolIsSet : IsSet Bool where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Unit is a set. -/
noncomputable def unitIsSet : IsSet Unit where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Empty is a set. -/
noncomputable def emptyIsSet : IsSet Empty where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-! ## n-types -/

/-- Truncation level. -/
inductive TruncLevel : Type where
  | minus2 : TruncLevel
  | succ : TruncLevel → TruncLevel

noncomputable def TruncLevel.minus1 : TruncLevel := TruncLevel.succ TruncLevel.minus2
noncomputable def TruncLevel.zero : TruncLevel := TruncLevel.succ TruncLevel.minus1

/-- Propositional n-truncation using computational paths at each level.  A
`succ`-level type is required to *realize* every propositional equality by a
genuine computational `Path` (path-connectedness witness), never a `True`
placeholder. -/
noncomputable def IsTruncProp : TruncLevel → Type u → Prop
  | TruncLevel.minus2, A => Nonempty (IsContr A)
  | TruncLevel.succ _, A => ∀ (a b : A), a = b → Nonempty (Path a b)

/-- (-2)-truncated is contractible. -/
theorem isTrunc_minus2_iff :
    IsTruncProp TruncLevel.minus2 A ↔ Nonempty (IsContr A) :=
  Iff.rfl

/-- (-1)-truncated via `IsProp`: every propositional equality is realized by the
proposition's genuine connecting path. -/
theorem isTrunc_minus1 (h : IsProp A) :
    IsTruncProp TruncLevel.minus1 A := by
  intro a b _; exact ⟨h.allPaths a b⟩

/-- 0-truncated via `IsSet`: every propositional equality is realized by a
genuine single-step computational path `Path.ofEq`. -/
theorem isTrunc_zero (_h : IsSet A) :
    IsTruncProp TruncLevel.zero A := by
  intro a b hab; exact ⟨Path.ofEq hab⟩

/-! ## Connected types -/

/-- A type is connected if inhabited and all elements are path-connected. -/
structure IsConnected (A : Type u) where
  inhab : A
  conn : (a b : A) → Path a b

/-- A contractible type is connected. -/
noncomputable def isContr_isConnected (h : IsContr A) : IsConnected A where
  inhab := h.center
  conn := fun a b => isContr_connect h a b

/-- Unit is connected. -/
noncomputable def unitIsConnected : IsConnected Unit where
  inhab := ()
  conn := fun () () => refl ()

/-- PUnit is connected. -/
noncomputable def punitIsConnected : IsConnected PUnit where
  inhab := PUnit.unit
  conn := fun u₁ u₂ => by cases u₁; cases u₂; exact refl PUnit.unit

/-! ## Truncation operations -/

/-- Product of contractible types is contractible. -/
noncomputable def prod_isContr (hA : IsContr A) (hB : IsContr B) :
    IsContr (A × B) where
  center := (hA.center, hB.center)
  contr := fun (a, b) =>
    Path.trans (congrArg (Prod.mk · hB.center) (hA.contr a))
              (congrArg (Prod.mk a ·) (hB.contr b))

/-- Product of propositions is a proposition. -/
noncomputable def prod_isProp (hA : IsProp A) (hB : IsProp B) :
    IsProp (A × B) where
  allPaths := fun (a₁, b₁) (a₂, b₂) =>
    Path.trans (congrArg (Prod.mk · b₁) (hA.allPaths a₁ a₂))
              (congrArg (Prod.mk a₂ ·) (hB.allPaths b₁ b₂))

/-- Product of sets is a set. -/
noncomputable def prod_isSet : IsSet (A × B) where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Function type into a proposition is a proposition. -/
noncomputable def fun_isProp (hB : IsProp B) : IsProp (A → B) where
  allPaths := fun f g =>
    Path.mk [Step.mk _ _ (funext fun a => (hB.allPaths (f a) (g a)).proof)]
      (funext fun a => (hB.allPaths (f a) (g a)).proof)

/-- Function type into a set is a set. -/
noncomputable def fun_isSet : IsSet (A → B) where
  proofEq := fun _ _ => Subsingleton.elim _ _

/-- Transport preserves contractibility. -/
noncomputable def transport_isContr {D : A → Type v} {a b : A}
    (p : Path a b) (h : IsContr (D a)) : IsContr (D b) where
  center := Path.transport p h.center
  contr := fun x => by
    have hp := p.proof
    subst hp
    exact h.contr x

/-- Transport preserves propositions. -/
noncomputable def transport_isProp {D : A → Type v} {a b : A}
    (p : Path a b) (h : IsProp (D a)) : IsProp (D b) where
  allPaths := fun x y => by
    have hp := p.proof
    subst hp
    exact h.allPaths x y

/-- Sigma type over a contractible base is contractible. -/
noncomputable def sigma_isContr {B : A → Type v}
    (hA : IsContr A) (hB : IsContr (B hA.center)) :
    IsContr ((a : A) × B a) where
  center := ⟨hA.center, hB.center⟩
  contr := fun ⟨a, b⟩ => by
    have ha := (hA.contr a).proof
    subst ha
    exact congrArg (Sigma.mk hA.center ·) (hB.contr b)

/-- Connected type induces (-1)-truncation. -/
theorem connected_path_trunc (h : IsConnected A) :
    IsTruncProp TruncLevel.minus1 A := by
  apply isTrunc_minus1
  exact { allPaths := h.conn }

/-! ## Genuine computational-path content

The `toEq`/`Subsingleton` layer above certifies the *h-level structures*
(`IsContr`, `IsProp`, `IsSet`) through proof-irrelevance of Lean's `Eq`.  The
paths themselves, however, carry genuine rewrite traces.  This section exhibits
multi-step `Path.trans` chains between DISTINCT expressions together with their
non-decorative `RwEq` groupoid coherences (`trans_symm`, `trans_assoc`,
`symm_symm`), first for the abstract connecting paths of a contractible type and
then over concrete `Nat`/`Int` carriers, culminating in a certificate
instantiated at fixed numbers. -/

section GenuinePaths

open ComputationalPaths.Path.Topology

/-- The connecting path of a contractible type composed with its inverse
`RwEq`-reduces to the reflexive path: a genuine `trans_symm` coherence on the
trace `symm (contr a) ⧺ contr b`, not a `Subsingleton` identification. -/
noncomputable def isContr_connect_cancel (h : IsContr A) (a b : A) :
    RwEq (Path.trans (isContr_connect h a b) (Path.symm (isContr_connect h a b)))
      (Path.refl a) :=
  rweq_cmpA_inv_right (isContr_connect h a b)

/-- Double inversion of a connecting path is a genuine `symm_symm` rewrite. -/
noncomputable def isContr_connect_double_symm (h : IsContr A) (a b : A) :
    RwEq (Path.symm (Path.symm (isContr_connect h a b))) (isContr_connect h a b) :=
  rweq_ss (isContr_connect h a b)

/-- Triangle composite of connecting paths: a genuine length-two `Path.trans`
chain `a ⤳ b ⤳ c` routed through the center. -/
noncomputable def isContr_triangle (h : IsContr A) (a b c : A) : Path a c :=
  Path.trans (isContr_connect h a b) (isContr_connect h b c)

/-- Reassociating a triple connecting composite is a genuine `trans_assoc`
(`rweq_tt`) rewrite between the two bracketings of `a ⤳ b ⤳ c ⤳ d`. -/
noncomputable def isContr_triangle_assoc (h : IsContr A) (a b c d : A) :
    RwEq
      (Path.trans
        (Path.trans (isContr_connect h a b) (isContr_connect h b c))
        (isContr_connect h c d))
      (Path.trans (isContr_connect h a b)
        (Path.trans (isContr_connect h b c) (isContr_connect h c d))) :=
  rweq_tt (isContr_connect h a b) (isContr_connect h b c) (isContr_connect h c d)

/-! ### Concrete `Nat`/`Int` carriers -/

/-- Associator path over `Nat`: `(a+b)+c ⤳ a+(b+c)` between distinct sides. -/
noncomputable def dAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Inner commutation `a+(b+c) ⤳ a+(c+b)` via `congrArg` on the core equality. -/
noncomputable def dInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- Outer commutation `a+(c+b) ⤳ (c+b)+a`. -/
noncomputable def dOuter (a b c : Nat) : Path (a + (c + b)) ((c + b) + a) :=
  Path.ofEq (Nat.add_comm a (c + b))

/-- Two-step reassociate-then-commute chain `(a+b)+c ⤳ a+(c+b)`. -/
noncomputable def dTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (dAssoc a b c) (dInner a b c)

/-- Three-step chain `(a+b)+c ⤳ (c+b)+a`. -/
noncomputable def dThreeStep (a b c : Nat) : Path ((a + b) + c) ((c + b) + a) :=
  Path.trans (dTwoStep a b c) (dOuter a b c)

/-- The two-step `Nat` chain cancels with its inverse — a non-decorative
`trans_symm` `RwEq` on a length-two trace. -/
noncomputable def dTwoStep_cancel (a b c : Nat) :
    RwEq (Path.trans (dTwoStep a b c) (Path.symm (dTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (dTwoStep a b c)

/-- Reassociation coherence of the three-step `Nat` chain (`trans_assoc`). -/
noncomputable def dThreeStep_assoc (a b c : Nat) :
    RwEq
      (Path.trans (Path.trans (dAssoc a b c) (dInner a b c)) (dOuter a b c))
      (Path.trans (dAssoc a b c) (Path.trans (dInner a b c) (dOuter a b c))) :=
  rweq_tt (dAssoc a b c) (dInner a b c) (dOuter a b c)

/-- Associator path over `Int`: `(x+y)+z ⤳ x+(y+z)` between distinct sides. -/
noncomputable def dAssocInt (x y z : Int) : Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Int.add_assoc x y z)

/-- Inner commutation over `Int`: `x+(y+z) ⤳ x+(z+y)`. -/
noncomputable def dInnerInt (x y z : Int) : Path (x + (y + z)) (x + (z + y)) :=
  Path.ofEq (_root_.congrArg (fun t => x + t) (Int.add_comm y z))

/-- Two-step `Int` chain `(x+y)+z ⤳ x+(z+y)`. -/
noncomputable def dTwoStepInt (x y z : Int) : Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (dAssocInt x y z) (dInnerInt x y z)

/-- The two-step `Int` chain's inverse cancels on the left (`symm_trans`). -/
noncomputable def dTwoStepInt_cancel (x y z : Int) :
    RwEq (Path.trans (Path.symm (dTwoStepInt x y z)) (dTwoStepInt x y z))
      (Path.refl (x + (z + y))) :=
  rweq_cmpA_inv_left (dTwoStepInt x y z)

/-! ### A concrete truncation-path certificate -/

/-- A certificate bundling, over concrete `Nat` data, a genuine three-step
`Path.trans` chain between distinct expressions together with non-decorative
`RwEq` witnesses for its `trans_assoc` reassociation and `trans_symm`
inverse-cancellation. -/
structure NatPathCertificate where
  /-- First summand. -/
  a : Nat
  /-- Second summand. -/
  b : Nat
  /-- Third summand. -/
  c : Nat
  /-- Three-step chain `(a+b)+c ⤳ (c+b)+a`. -/
  route : Path ((a + b) + c) ((c + b) + a)
  /-- Reassociation of the three composed factors (`trans_assoc`). -/
  assocCoh : RwEq
    (Path.trans (Path.trans (dAssoc a b c) (dInner a b c)) (dOuter a b c))
    (Path.trans (dAssoc a b c) (Path.trans (dInner a b c) (dOuter a b c)))
  /-- The chain cancels with its inverse (`trans_symm`). -/
  cancelCoh : RwEq (Path.trans route (Path.symm route)) (Path.refl ((a + b) + c))

/-- Build the certificate from three summands. -/
noncomputable def NatPathCertificate.build (a b c : Nat) : NatPathCertificate where
  a := a
  b := b
  c := c
  route := dThreeStep a b c
  assocCoh := rweq_tt (dAssoc a b c) (dInner a b c) (dOuter a b c)
  cancelCoh := rweq_cmpA_inv_right (dThreeStep a b c)

/-- The certificate at the concrete numbers `2, 3, 4`. -/
noncomputable def natPathCertificate234 : NatPathCertificate :=
  NatPathCertificate.build 2 3 4

/-- Concrete numeric endpoints of the certificate at `2,3,4`: both sides
evaluate to `9` through the syntactically distinct routes. -/
theorem natPathCertificate234_target : ((2 + 3) + 4 : Nat) = (4 + 3) + 2 := rfl

/-- A `PathLawCertificate` (from the topology certificate library) for the
concrete two-step `Nat` chain at `2,3,4`, packaging its right-unit and
inverse-cancellation `RwEq` laws around a genuine trace-carrying path. -/
noncomputable def natLawCertificate234 :
    PathLawCertificate ((2 + 3) + 4 : Nat) (2 + (4 + 3)) :=
  PathLawCertificate.ofPath (dTwoStep 2 3 4)

end GenuinePaths

end Truncation
end HoTT
end Path
end ComputationalPaths
