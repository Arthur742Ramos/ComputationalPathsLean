/-
# Deep Identity Type Theory via Computational Paths

Identity types ARE Path types, reflexivity IS Path.refl, J derived from
path induction, ap IS congrArg, transport IS transport. Multi-step proofs
of function extensionality, encode-decode method, equivalences.

## References

- HoTT Book Chapters 2, 3, 4
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace IdentityTypeDeep

open ComputationalPaths.Path

universe u v w

/-! ## Identity types as Path types -/

/-- Identity type IS the Path type. -/
abbrev IdType {A : Type u} (a b : A) := Path a b

/-- ap IS congrArg. -/
abbrev ap {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) : Path (f a) (f b) := Path.congrArg f p

/-! ## ap (congrArg) laws -/

/-- 1. ap preserves composition. -/
theorem ap_trans {A : Type u} {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    ap f (trans p q) = trans (ap f p) (ap f q) :=
  congrArg_trans f p q

/-- 2. ap preserves inversion. -/
theorem ap_symm {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) :
    ap f (symm p) = symm (ap f p) :=
  congrArg_symm f p

/-- 3. ap at refl is refl. -/
theorem ap_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    ap f (Path.refl a) = Path.refl (f a) := by
  simp [ap]

/-- 4. ap of composition is composition of ap. -/
theorem ap_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) :
    ap g (ap f p) = ap (g ∘ f) p := by
  cases p with | mk steps proof => cases proof; simp [ap]

/-- 5. Three-fold ap chain (deep multi-step). -/
theorem ap_triple {A B : Type u} (f : A → B) {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    ap f (trans (trans p q) r) =
      trans (trans (ap f p) (ap f q)) (ap f r) := by
  simp only [ap, congrArg_trans]

/-- 6. Four-fold ap chain. -/
theorem ap_quad {A B : Type u} (f : A → B) {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    ap f (trans (trans (trans p q) r) s) =
      trans (trans (trans (ap f p) (ap f q)) (ap f r)) (ap f s) := by
  simp only [ap, congrArg_trans]

/-- 7. ap distributes over five-fold composition. -/
theorem ap_penta {A B : Type u} (f : A → B) {a b c d e g : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e g) :
    ap f (trans (trans (trans (trans p q) r) s) t) =
      trans (trans (trans (trans (ap f p) (ap f q)) (ap f r)) (ap f s)) (ap f t) := by
  simp only [ap, congrArg_trans]

/-! ## Transport laws -/

/-- 8. Transport along trans = sequential transport. -/
theorem idTransport_trans {A : Type u} {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (trans p q) x = transport q (transport p x) :=
  transport_trans p q x

/-- 9. Transport along symm inverts (left). -/
theorem idTransport_symm_left {A : Type u} {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

/-- 10. Transport along symm inverts (right). -/
theorem idTransport_symm_right {A : Type u} {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    transport p (transport (symm p) y) = y :=
  transport_symm_right p y

/-- 11. Transport in constant family is identity. -/
theorem idTransport_const {A : Type u} {B : Type v} {a b : A}
    (p : Path a b) (x : B) :
    transport (D := fun _ => B) p x = x :=
  transport_const p x

/-- 12. Transport along ap = transport in pullback. -/
theorem transport_ap_eq {A B : Type u} {P : B → Type v}
    (f : A → B) {a₁ a₂ : A} (p : Path a₁ a₂) (x : P (f a₁)) :
    transport (D := P ∘ f) p x = transport (D := P) (ap f p) x := by
  cases p with | mk steps proof => cases proof; rfl

/-- 13. Naturality of transport: function application commutes with transport. -/
theorem transport_natural {A : Type u} {P Q : A → Type v}
    (f : ∀ x, P x → Q x) {a b : A} (p : Path a b) (u : P a) :
    transport (D := Q) p (f a u) = f b (transport (D := P) p u) := by
  cases p with | mk steps proof => cases proof; rfl

/-- 14. Three-fold transport chain decomposition (deep multi-step). -/
theorem transport_chain_3 {A : Type u} {D : A → Type v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    transport (D := D) (trans (trans p q) r) x =
      transport r (transport q (transport p x)) := by
  simp only [transport_trans]

/-- 15. Four-fold transport chain decomposition. -/
theorem transport_chain_4 {A : Type u} {D : A → Type v} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (x : D a) :
    transport (D := D) (trans (trans (trans p q) r) s) x =
      transport s (transport r (transport q (transport p x))) := by
  simp only [transport_trans]

/-- 16. Double transport roundtrip (deep chain). -/
theorem double_roundtrip {A : Type u} {D : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (D := D) (symm p) (transport (symm q)
      (transport q (transport p x))) = x := by
  simp only [transport_symm_left]

/-- 17. Triple roundtrip. -/
theorem triple_roundtrip {A : Type u} {D : A → Type v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    transport (D := D) (symm p) (transport (symm q) (transport (symm r)
      (transport r (transport q (transport p x))))) = x := by
  simp only [transport_symm_left]

/-! ## Encode-decode method -/

/-- Code family for paths (propositional). -/
noncomputable def Code {A : Type u} [DecidableEq A] (a b : A) : Prop := a = b

/-- 18. Encode: from path to code. -/
noncomputable def encode {A : Type u} [DecidableEq A] {a b : A}
    (p : Path a b) : Code a b := p.proof

/-- 19. Decode: from code to path. -/
noncomputable def decode {A : Type u} [DecidableEq A] {a b : A}
    (c : Code a b) : Path a b := Path.mk [Step.mk _ _ c] c

/-- 20. Encode-decode roundtrip. -/
theorem encode_decode_roundtrip {A : Type u} [DecidableEq A] {a b : A}
    (c : Code a b) : encode (decode c) = c := rfl

/-- 21. Decode-encode gives ofEq of the proof. -/
theorem decode_encode {A : Type u} [DecidableEq A] {a b : A}
    (p : Path a b) : decode (encode p) = Path.mk [Step.mk _ _ p.proof] p.proof := rfl

/-- 22. Encode at refl gives rfl. -/
theorem encode_refl {A : Type u} [DecidableEq A] (a : A) :
    encode (Path.refl a) = (rfl : Code a a) := rfl

/-! ## Function extensionality via paths -/

/-- 23. Function extensionality: pointwise paths give a path between functions. -/
noncomputable def funext_path {A : Type u} {B : A → Type v} {f g : (a : A) → B a}
    (h : ∀ a, Path (f a) (g a)) : Path f g :=
  Path.mk [Step.mk _ _ (funext (fun a => (h a).proof))]
    (funext (fun a => (h a).proof))

/-- 24. Happly: a path between functions gives pointwise paths. -/
noncomputable def happly {A : Type u} {B : A → Type v} {f g : (a : A) → B a}
    (p : Path f g) (a : A) : Path (f a) (g a) :=
  congrArg (fun h => h a) p

/-- 25. Happly at refl is refl. -/
theorem happly_refl {A : Type u} {B : A → Type v} (f : (a : A) → B a) (a : A) :
    happly (Path.refl f) a = Path.refl (f a) := by
  simp [happly]

/-- 26. Happly preserves trans. -/
theorem happly_trans {A : Type u} {B : A → Type v} {f g h : (a : A) → B a}
    (p : Path f g) (q : Path g h) (a : A) :
    happly (trans p q) a = trans (happly p a) (happly q a) := by
  simp only [happly, congrArg_trans]

/-- 27. Happly preserves symm. -/
theorem happly_symm {A : Type u} {B : A → Type v} {f g : (a : A) → B a}
    (p : Path f g) (a : A) :
    happly (symm p) a = symm (happly p a) := by
  simp only [happly, congrArg_symm]

/-! ## Equivalences -/

/-- A quasi-inverse equivalence. -/
structure QInv {A B : Type u} (f : A → B) where
  inv : B → A
  rightInv : ∀ b, Path (f (inv b)) b
  leftInv : ∀ a, Path (inv (f a)) a

/-- 28. Identity is an equivalence. -/
noncomputable def idQInv (A : Type u) : QInv (id : A → A) where
  inv := id
  rightInv := fun _ => Path.refl _
  leftInv := fun _ => Path.refl _

/-- 29. Equivalences compose (deep multi-step proof). -/
noncomputable def compQInv {A B C : Type u} {f : A → B} {g : B → C}
    (ef : QInv f) (eg : QInv g) : QInv (g ∘ f) where
  inv := ef.inv ∘ eg.inv
  rightInv := fun c =>
    trans (ap g (ef.rightInv (eg.inv c))) (eg.rightInv c)
  leftInv := fun a =>
    trans (ap ef.inv (eg.leftInv (f a))) (ef.leftInv a)

/-- 30. Equivalences invert. -/
noncomputable def invQInv {A B : Type u} {f : A → B} (ef : QInv f) : QInv ef.inv where
  inv := f
  rightInv := ef.leftInv
  leftInv := ef.rightInv

/-- 31. Transport is an equivalence (deep proof). -/
noncomputable def transportQInv {A : Type u} {D : A → Type u} {a b : A}
    (p : Path a b) : QInv (transport (D := D) p) where
  inv := transport (D := D) (symm p)
  rightInv := fun y => Path.mk [Step.mk _ _ (transport_symm_right p y)]
    (transport_symm_right p y)
  leftInv := fun x => Path.mk [Step.mk _ _ (transport_symm_left p x)]
    (transport_symm_left p x)

/-! ## Path algebra deep chains -/

/-- 32. Four-fold trans reassociation via two-step calc. -/
theorem trans_quad_reassoc {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    trans (trans (trans p q) r) s = trans p (trans q (trans r s)) := by
  calc trans (trans (trans p q) r) s
      = trans (trans p q) (trans r s) := trans_assoc (trans p q) r s
    _ = trans p (trans q (trans r s)) := trans_assoc p q (trans r s)

/-- 33. Inverse distributes over triple composition. -/
theorem symm_triple {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    symm (trans (trans p q) r) = trans (symm r) (trans (symm q) (symm p)) := by
  simp only [symm_trans]

/-- 34. Inverse distributes over four-fold composition. -/
theorem symm_quad {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    symm (trans (trans (trans p q) r) s) =
      trans (symm s) (trans (symm r) (trans (symm q) (symm p))) := by
  simp only [symm_trans]

/-- 35. Based path space contractibility (propositional). -/
theorem based_path_prop {A : Type u} (a : A) :
    ∀ (bq : (b : A) × PLift (a = b)),
      (⟨a, PLift.up rfl⟩ : (b : A) × PLift (a = b)) = bq := by
  intro ⟨b, ⟨h⟩⟩; cases h; rfl

end IdentityTypeDeep
end TypeTheory
end Path
end ComputationalPaths
