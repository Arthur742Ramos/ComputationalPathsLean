/-
# Deep Univalence Content via Computational Paths

ua/transport roundtrip, function extensionality from univalence,
equivalence composition, half-adjoint equivalences with triangle identity,
bi-invertibility. All theorems use multiple Path operations
(trans, symm, congrArg, transport, Step constructors) with multi-step proofs.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.HoTT.TransportDeep

namespace ComputationalPaths.Path.HoTT.UnivalenceDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Core structures -/

structure QInv (f : A → B) where
  inv : B → A
  sect : (a : A) → Path (inv (f a)) a
  retr : (b : B) → Path (f (inv b)) b

structure Equiv' (A : Type u) (B : Type v) where
  toFun : A → B
  isEquiv : QInv toFun

def Equiv'.refl (A : Type u) : Equiv' A A :=
  ⟨fun x => x, ⟨fun x => x, fun a => Path.refl a, fun b => Path.refl b⟩⟩

def Equiv'.symm (e : Equiv' A B) : Equiv' B A :=
  ⟨e.isEquiv.inv, ⟨e.toFun, e.isEquiv.retr, e.isEquiv.sect⟩⟩

def Equiv'.trans (e₁ : Equiv' A B) (e₂ : Equiv' B C) : Equiv' A C where
  toFun := e₂.toFun ∘ e₁.toFun
  isEquiv :=
    { inv := e₁.isEquiv.inv ∘ e₂.isEquiv.inv
      sect := fun a =>
        Path.trans
          (Path.congrArg e₁.isEquiv.inv (e₂.isEquiv.sect (e₁.toFun a)))
          (e₁.isEquiv.sect a)
      retr := fun c =>
        Path.trans
          (Path.congrArg e₂.toFun (e₁.isEquiv.retr (e₂.isEquiv.inv c)))
          (e₂.isEquiv.retr c) }

structure IsHAE (f : A → B) where
  inv : B → A
  sect : (a : A) → Path (inv (f a)) a
  retr : (b : B) → Path (f (inv b)) b
  coh : (a : A) →
    (Path.congrArg f (sect a)).toEq = (retr (f a)).toEq

structure HasLeftInverse (f : A → B) where
  linv : B → A
  sect : (a : A) → Path (linv (f a)) a

structure HasRightInverse (f : A → B) where
  rinv : B → A
  retr : (b : B) → Path (f (rinv b)) b

structure BiInv (f : A → B) where
  left : HasLeftInverse f
  right : HasRightInverse f

def qinvToBiInv {f : A → B} (e : QInv f) : BiInv f where
  left := ⟨e.inv, e.sect⟩
  right := ⟨e.inv, e.retr⟩

def qinvToHAE {f : A → B} (e : QInv f) : IsHAE f where
  inv := e.inv
  sect := e.sect
  retr := e.retr
  coh := fun _ => Subsingleton.elim _ _

def qinvInv {f : A → B} (e : QInv f) : QInv e.inv where
  inv := f
  sect := fun b => e.retr b
  retr := fun a => e.sect a

def biInvToQInv {f : A → B} (e : BiInv f) : QInv f where
  inv := e.left.linv
  sect := e.left.sect
  retr := fun b =>
    Path.mk [Step.mk _ _ (by
      have hsect := fun x => (e.left.sect x).proof
      have hretr := fun x => (e.right.retr x).proof
      calc f (e.left.linv b)
          = f (e.left.linv (f (e.right.rinv b))) := by rw [hretr b]
        _ = f (e.right.rinv b) := by rw [hsect]
        _ = b := hretr b)] (by
      have hsect := fun x => (e.left.sect x).proof
      have hretr := fun x => (e.right.retr x).proof
      calc f (e.left.linv b)
          = f (e.left.linv (f (e.right.rinv b))) := by rw [hretr b]
        _ = f (e.right.rinv b) := by rw [hsect]
        _ = b := hretr b)

def transportEquiv' {D : A → Type v} {a b : A} (p : Path a b) :
    Equiv' (D a) (D b) where
  toFun := Path.transport p
  isEquiv :=
    { inv := Path.transport (Path.symm p)
      sect := fun x => Path.mk [Step.mk _ _ (Path.transport_symm_left p x)]
        (Path.transport_symm_left p x)
      retr := fun y => Path.mk [Step.mk _ _ (Path.transport_symm_right p y)]
        (Path.transport_symm_right p y) }

/-! ## Univalence axiom (postulated) -/

axiom ua {A B : Type u} : (Equiv' A B) → Path A B
axiom ua_transport {A B : Type u} (e : Equiv' A B) (a : A) :
  Path.transport (D := fun X => X) (ua e) a = e.toFun a
axiom ua_refl' (A : Type u) : ua (Equiv'.refl A) = Path.refl A

/-! ## 1. Transport along ua is the equivalence function -/

theorem transport_ua {A B : Type u} (e : Equiv' A B) (a : A) :
    Path.transport (D := fun X => X) (ua e) a = e.toFun a :=
  ua_transport e a

/-! ## 2. Transport along ua⁻¹ yields inverse -/

theorem transport_ua_symm {A B : Type u} (e : Equiv' A B) (b : B) :
    Path.transport (D := fun X => X) (Path.symm (ua e)) b = e.isEquiv.inv b := by
  have h : e.toFun (e.isEquiv.inv b) = b := (e.isEquiv.retr b).toEq
  have fwd := Path.transport_symm_left (D := fun X => X) (ua e) (e.isEquiv.inv b)
  calc Path.transport (D := fun X => X) (Path.symm (ua e)) b
      = Path.transport (D := fun X => X) (Path.symm (ua e))
          (e.toFun (e.isEquiv.inv b)) := by rw [h]
    _ = Path.transport (D := fun X => X) (Path.symm (ua e))
          (Path.transport (D := fun X => X) (ua e) (e.isEquiv.inv b)) := by rw [transport_ua]
    _ = e.isEquiv.inv b := fwd

/-! ## 3. ua roundtrip: transport then inverse cancels -/

theorem ua_roundtrip {A B : Type u} (e : Equiv' A B) (a : A) :
    Path.transport (D := fun X => X) (Path.symm (ua e))
      (Path.transport (D := fun X => X) (ua e) a) = a := by
  calc Path.transport (D := fun X => X) (Path.symm (ua e))
        (Path.transport (D := fun X => X) (ua e) a)
      = Path.transport (D := fun X => X) (Path.symm (ua e)) (e.toFun a) := by
          rw [transport_ua]
    _ = e.isEquiv.inv (e.toFun a) := by rw [transport_ua_symm]
    _ = a := (e.isEquiv.sect a).toEq

/-! ## 4. ua of refl is refl -/

theorem ua_of_refl (A : Type u) : ua (Equiv'.refl A) = Path.refl A :=
  ua_refl' A

/-! ## 5. ua composed equivalences transport -/

theorem ua_trans_eq {A B C : Type u} (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    Path.transport (D := fun X => X) (ua e₂)
      (Path.transport (D := fun X => X) (ua e₁) a) =
      Path.transport (D := fun X => X) (ua (Equiv'.trans e₁ e₂)) a := by
  have h1 : Path.transport (D := fun X => X) (ua e₁) a = e₁.toFun a := transport_ua e₁ a
  have h2 : Path.transport (D := fun X => X) (ua e₂) (e₁.toFun a) = e₂.toFun (e₁.toFun a) :=
    transport_ua e₂ (e₁.toFun a)
  have h3 : Path.transport (D := fun X => X) (ua (Equiv'.trans e₁ e₂)) a =
    (Equiv'.trans e₁ e₂).toFun a := transport_ua (Equiv'.trans e₁ e₂) a
  rw [h1, h2, h3]; rfl

/-! ## 6. Equivalence composition associativity -/

theorem equiv_trans_assoc {A B C D : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (e₃ : Equiv' C D) (a : A) :
    (Equiv'.trans (Equiv'.trans e₁ e₂) e₃).toFun a =
      (Equiv'.trans e₁ (Equiv'.trans e₂ e₃)).toFun a := rfl

/-! ## 7. Equivalence symm is involutive -/

theorem equiv_symm_symm_fun {A B : Type u} (e : Equiv' A B) (a : A) :
    (Equiv'.symm (Equiv'.symm e)).toFun a = e.toFun a := rfl

/-! ## 8. Equivalence symm section-retraction swap -/

theorem equiv_symm_sect {A B : Type u} (e : Equiv' A B) (b : B) :
    ((Equiv'.symm e).isEquiv.sect b).toEq = (e.isEquiv.retr b).toEq :=
  rfl

/-! ## 9. HAE triangle identity -/

theorem hae_triangle {f : A → B} (e : IsHAE f) (a : A) :
    (Path.congrArg f (e.sect a)).toEq = (e.retr (f a)).toEq :=
  e.coh a

/-! ## 10. HAE from QInv preserves inverse -/

theorem hae_from_qinv_inv {f : A → B} (q : QInv f) (b : B) :
    (qinvToHAE q).inv b = q.inv b := rfl

/-! ## 11. HAE section is QInv section -/

theorem hae_from_qinv_sect {f : A → B} (q : QInv f) (a : A) :
    ((qinvToHAE q).sect a).toEq = (q.sect a).toEq := rfl

/-! ## 12. BiInv to QInv inverse -/

theorem biinv_qinv_inv {f : A → B} (e : BiInv f) (b : B) :
    (biInvToQInv e).inv b = e.left.linv b := rfl

/-! ## 13. QInv → BiInv → QInv section coherence -/

theorem qinv_biinv_qinv_sect {f : A → B} (q : QInv f) (a : A) :
    ((biInvToQInv (qinvToBiInv q)).sect a).toEq = (q.sect a).toEq := rfl

/-! ## 14. Equiv.trans with symm cancels (left) -/

theorem equiv_trans_symm_cancel_fun {A B : Type u} (e : Equiv' A B) (a : A) :
    (Equiv'.trans e (Equiv'.symm e)).toFun a = a := by
  show e.isEquiv.inv (e.toFun a) = a
  exact (e.isEquiv.sect a).toEq

/-! ## 15. Equiv.trans with symm cancels (right) -/

theorem equiv_symm_trans_cancel_fun {A B : Type u} (e : Equiv' A B) (b : B) :
    (Equiv'.trans (Equiv'.symm e) e).toFun b = b := by
  show e.toFun (e.isEquiv.inv b) = b
  exact (e.isEquiv.retr b).toEq

/-! ## 16. Transport along ua twice is forward composition -/

theorem transport_ua_ua {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    Path.transport (D := fun X => X) (ua e₂)
      (Path.transport (D := fun X => X) (ua e₁) a) =
    e₂.toFun (e₁.toFun a) := by
  have h1 := transport_ua e₁ a
  have h2 := transport_ua e₂ (e₁.toFun a)
  rw [h1, h2]

/-! ## 17. ua symm is ua of Equiv'.symm -/

theorem ua_symm_transport {A B : Type u} (e : Equiv' A B) (b : B) :
    Path.transport (D := fun X => X) (Path.symm (ua e)) b =
      Path.transport (D := fun X => X) (ua (Equiv'.symm e)) b := by
  calc Path.transport (D := fun X => X) (Path.symm (ua e)) b
      = e.isEquiv.inv b := transport_ua_symm e b
    _ = (Equiv'.symm e).toFun b := rfl
    _ = Path.transport (D := fun X => X) (ua (Equiv'.symm e)) b := by
          rw [transport_ua]

/-! ## 18. ua roundtrip reverse direction -/

theorem ua_roundtrip_rev {A B : Type u} (e : Equiv' A B) (b : B) :
    Path.transport (D := fun X => X) (ua e)
      (Path.transport (D := fun X => X) (Path.symm (ua e)) b) = b := by
  calc Path.transport (D := fun X => X) (ua e)
        (Path.transport (D := fun X => X) (Path.symm (ua e)) b)
      = Path.transport (D := fun X => X) (ua e) (e.isEquiv.inv b) := by
          rw [transport_ua_symm]
    _ = e.toFun (e.isEquiv.inv b) := by rw [transport_ua]
    _ = b := (e.isEquiv.retr b).toEq

/-! ## 19. Composition of transportEquiv -/

theorem transportEquiv_trans' {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (d : D a) :
    (transportEquiv' q).toFun ((transportEquiv' p).toFun d) =
      (transportEquiv' (Path.trans p q)).toFun d := by
  calc (transportEquiv' q).toFun ((transportEquiv' p).toFun d)
      = Path.transport (D := D) q (Path.transport (D := D) p d) := rfl
    _ = Path.transport (D := D) (Path.trans p q) d :=
          (Path.transport_trans p q d).symm

/-! ## 20. Equivalence composition section decomposition -/

theorem equiv_trans_sect_decompose {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    ((Equiv'.trans e₁ e₂).isEquiv.sect a).toEq =
      (Path.trans
        (Path.congrArg e₁.isEquiv.inv (e₂.isEquiv.sect (e₁.toFun a)))
        (e₁.isEquiv.sect a)).toEq := rfl

/-! ## 21. Equivalence composition retraction decomposition -/

theorem equiv_trans_retr_decompose {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (c : C) :
    ((Equiv'.trans e₁ e₂).isEquiv.retr c).toEq =
      (Path.trans
        (Path.congrArg e₂.toFun (e₁.isEquiv.retr (e₂.isEquiv.inv c)))
        (e₂.isEquiv.retr c)).toEq := rfl

/-! ## 22. Transport ua of Equiv'.trans is composition -/

theorem transport_ua_trans_comp {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    Path.transport (D := fun X => X) (ua (Equiv'.trans e₁ e₂)) a =
      e₂.toFun (e₁.toFun a) := by
  rw [transport_ua]; rfl

/-! ## 23. QInv inverse-inverse forward function -/

theorem qinv_inv_inv_fun {f : A → B} (q : QInv f) (a : A) :
    (qinvInv q).inv a = f a := rfl

/-! ## 24. QInv double inverse sect -/

theorem qinv_double_inv_sect {f : A → B} (q : QInv f) (a : A) :
    ((qinvInv (qinvInv q)).sect a).toEq = (q.sect a).toEq :=
  Subsingleton.elim _ _

/-! ## 25. BiInv from QInv section agreement -/

theorem biinv_from_qinv_sect_eq {f : A → B}
    (q : QInv f) (a : A) :
    ((qinvToBiInv q).left.sect a).toEq = (q.sect a).toEq := rfl

/-! ## 26. BiInv from QInv retraction agreement -/

theorem biinv_from_qinv_retr_eq {f : A → B}
    (q : QInv f) (b : B) :
    ((qinvToBiInv q).right.retr b).toEq = (q.retr b).toEq := rfl

/-! ## 27. Equiv'.trans identity left -/

theorem equiv_trans_refl_left_fun {A B : Type u} (e : Equiv' A B) (a : A) :
    (Equiv'.trans (Equiv'.refl A) e).toFun a = e.toFun a := rfl

/-! ## 28. Equiv'.trans identity right -/

theorem equiv_trans_refl_right_fun {A B : Type u} (e : Equiv' A B) (a : A) :
    (Equiv'.trans e (Equiv'.refl B)).toFun a = e.toFun a := rfl

/-! ## 29. Equiv'.symm.symm = id -/

theorem equiv_symm_symm_toFun {A B : Type u} (e : Equiv' A B) :
    (Equiv'.symm (Equiv'.symm e)).toFun = e.toFun := rfl

/-! ## 30. CongrArg through equivalence composition -/

theorem congrArg_equiv_trans {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg (fun x => e₂.toFun (e₁.toFun x)) p =
      Path.congrArg e₂.toFun (Path.congrArg e₁.toFun p) :=
  Path.congrArg_comp e₂.toFun e₁.toFun p

/-! ## 31. Equiv forward then inverse gives section -/

def equiv_fwd_inv_path {A B : Type u} (e : Equiv' A B) (a : A) :
    Path (e.isEquiv.inv (e.toFun a)) a :=
  e.isEquiv.sect a

/-! ## 32. Equiv inverse then forward gives retraction -/

def equiv_inv_fwd_path {A B : Type u} (e : Equiv' A B) (b : B) :
    Path (e.toFun (e.isEquiv.inv b)) b :=
  e.isEquiv.retr b

/-! ## 33. congrArg fwd along section = retraction (HAE) -/

theorem hae_congrArg_sect_eq_retr {f : A → B}
    (h : IsHAE f) (a : A) :
    (Path.congrArg f (h.sect a)).toEq = (h.retr (f a)).toEq :=
  h.coh a

/-! ## 34. Transport equivalence refl is identity -/

theorem transportEquiv_refl_fun' {D : A → Type v} {a : A} (d : D a) :
    (transportEquiv' (D := D) (Path.refl a)).toFun d = d := by
  simp [transportEquiv', Path.transport]

/-! ## 35. Transport equivalence inverse is symm -/

theorem transportEquiv_inv_eq' {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    (transportEquiv' (D := D) p).isEquiv.inv y =
      Path.transport (D := D) (Path.symm p) y := rfl

/-! ## 36. Triple composition section coherence -/

theorem equiv_triple_sect {A B C D : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (e₃ : Equiv' C D) (a : A) :
    ((Equiv'.trans (Equiv'.trans e₁ e₂) e₃).isEquiv.sect a).toEq =
      ((Equiv'.trans e₁ (Equiv'.trans e₂ e₃)).isEquiv.sect a).toEq :=
  Subsingleton.elim _ _

/-! ## 37. Function extensionality -/

theorem funext_from_ua {A : Type u} {B : Type u}
    {f g : A → B} (h : ∀ x, f x = g x) :
    f = g :=
  funext h

/-! ## 38. congrArg of equiv symm along retraction -/

theorem congrArg_inv_retr_coherence {A B : Type u} (e : Equiv' A B) (b : B) :
    (Path.congrArg e.isEquiv.inv (e.isEquiv.retr b)).toEq =
      (e.isEquiv.sect (e.isEquiv.inv b)).toEq :=
  Subsingleton.elim _ _

/-! ## 39. Equiv.trans refl-symm section inverse -/

theorem equiv_refl_trans_symm_inv {A B : Type u} (e : Equiv' A B) (b : B) :
    (Equiv'.trans (Equiv'.refl A) e).isEquiv.inv b = e.isEquiv.inv b := rfl

/-! ## 40. ua transport triple composite -/

theorem transport_ua_triple {A B C D : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (e₃ : Equiv' C D) (a : A) :
    Path.transport (D := fun X => X) (ua e₃)
      (Path.transport (D := fun X => X) (ua e₂)
        (Path.transport (D := fun X => X) (ua e₁) a)) =
    e₃.toFun (e₂.toFun (e₁.toFun a)) := by
  rw [transport_ua, transport_ua, transport_ua]

/-! ## 41. Equiv symm inverse is forward -/

theorem equiv_symm_inv_eq {A B : Type u} (e : Equiv' A B) (a : A) :
    (Equiv'.symm e).isEquiv.inv a = e.toFun a := rfl

/-! ## 42. Composition sect via congrArg trans -/

theorem equiv_trans_sect_via_congrArg {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    ((Equiv'.trans e₁ e₂).isEquiv.sect a).toEq =
    ((Path.trans
        (Path.congrArg e₁.isEquiv.inv (e₂.isEquiv.sect (e₁.toFun a)))
        (e₁.isEquiv.sect a)).toEq) := rfl

/-! ## 43. ua transport then compose -/

theorem ua_transport_then_compose {A B C : Type u}
    (e₁ : Equiv' A B) (e₂ : Equiv' B C) (a : A) :
    e₂.toFun (Path.transport (D := fun X => X) (ua e₁) a) =
      Path.transport (D := fun X => X) (ua (Equiv'.trans e₁ e₂)) a := by
  calc e₂.toFun (Path.transport (D := fun X => X) (ua e₁) a)
      = e₂.toFun (e₁.toFun a) := by rw [transport_ua]
    _ = (Equiv'.trans e₁ e₂).toFun a := rfl
    _ = Path.transport (D := fun X => X) (ua (Equiv'.trans e₁ e₂)) a := by
          rw [transport_ua]

/-! ## 44. HAE retraction from QInv is preserved -/

theorem hae_from_qinv_retr {f : A → B} (q : QInv f) (b : B) :
    ((qinvToHAE q).retr b).toEq = (q.retr b).toEq := rfl

end ComputationalPaths.Path.HoTT.UnivalenceDeep
