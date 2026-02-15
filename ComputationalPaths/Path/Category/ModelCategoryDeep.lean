namespace ComputationalPaths.Category.ModelCategoryDeep

universe u v

inductive Stp (A : Type u) : A → A → Type u where
  | refl (a : A) : Stp A a a
  | symm {a b : A} : Stp A a b → Stp A b a
  | trans {a b c : A} : Stp A a b → Stp A b c → Stp A a c
  | congrArg {a b : A} (f : A → A) : Stp A a b → Stp Stp A (f a) (f b)

-- Wait, the template has:
-- | congrArg {a b : A} (f : A → A) : Step A a b → Step A (f a) (f b)

inductive Step (A : Type u) : A → A → Type u where
  | refl (a : A) : Step A a a
  | symm {a b : A} : Step A a b → Step A b a
  | trans {a b c : A} : Step A a b → Step A b c → Step A a c
  | congrArg {a b : A} (f : A → A) : Step A a b → Step A (f a) (f b)

inductive Path (A : Type u) : A → A → Type u where
  | nil (a : A) : Path A a a
  | cons {a b c : A} : Step A a b → Path A b c → Path A a c

namespace Step
variable {A : Type u}
def toEq : {a b : A} → Step A a b → a = b
  | _, _, refl _ => rfl
  | _, _, symm s => (toEq s).symm
  | _, _, trans s t => (toEq s).trans (toEq t)
  | _, _, congrArg f s => _root_.congrArg f (toEq s)
end Step

namespace Path
variable {A : Type u}

def trans : {a b c : A} → Path A a b → Path A b c → Path A a c
  | _, _, _, nil _, q => q
  | _, _, _, cons s p, q => cons s (trans p q)

def symm : {a b : A} → Path A a b → Path A b a
  | _, _, nil a => nil a
  | _, _, cons s p => trans (symm p) (cons (Step.symm s) (nil _))

def congrArg (f : A → A) : {a b : A} → Path A a b → Path A (f a) (f b)
  | _, _, nil a => nil (f a)
  | _, _, cons s p => cons (Step.congrArg f s) (congrArg f p)

def toEq : {a b : A} → Path A a b → a = b
  | _, _, nil _ => rfl
  | _, _, cons s p => (Step.toEq s).trans (toEq p)

def transport {D : A → Sort v} {a b : A} (p : Path A a b) (x : D a) : D b :=
  Eq.recOn (toEq p) x

end Path

open Path

variable {A : Type u}

/-- 1. Path associativity. -/
theorem p_trans_assoc {a b c d : A} (p : Path A a b) (q : Path A b c) (r : Path A c d) :
    trans (trans p q) r = trans p (trans q r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show cons s (trans (trans p q) r) = cons s (trans p (trans q r))
    rw [ih]

/-- 2. toEq trans. -/
theorem p_toEq_trans {a b c : A} (p : Path A a b) (q : Path A b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show (Step.toEq s).trans (toEq (trans p q)) = ((Step.toEq s).trans (toEq p)).trans (toEq q)
    rw [ih]
    cases Step.toEq s; cases toEq p; cases toEq q; rfl

/-- 3. toEq symm. -/
theorem p_toEq_symm {a b : A} (p : Path A a b) :
    toEq (symm p) = (toEq p).symm := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show toEq (trans (symm p) (cons (Step.symm s) (nil _))) = ((Step.toEq s).trans (toEq p)).symm
    rw [p_toEq_trans, ih]
    cases Step.toEq s; cases toEq p; rfl

/-- 4. transport trans. -/
theorem p_transport_trans {D : A → Sort v} {a b c : A} (p : Path A a b) (q : Path b c) (x : D a) :
    transport (trans p q) x = transport q (transport p x) := by
  unfold transport
  rw [p_toEq_trans]
  cases toEq p; cases toEq q; rfl

/-- 5. transport symm. -/
theorem p_transport_symm_left {D : A → Sort v} {a b : A} (p : Path A a b) (x : D a) :
    transport (symm p) (transport p x) = x := by
  unfold transport
  rw [p_toEq_symm]
  cases toEq p; rfl

/-- 6. Isomorphism structure. -/
structure IsIso {a b : A} (p : Path A a b) where
  inv : Path A b a
  id_l : toEq (trans p inv) = rfl
  id_r : toEq (trans inv p) = rfl

/-- 7. Weak Equivalence. -/
structure IsWeq {a b : A} (f : Path A a b) where
  iso : IsIso f

/-- 8. weq comp. -/
def weq_comp {a b c : A} {f : Path A a b} {g : Path A b c} (hf : IsWeq f) (hg : IsWeq g) : IsWeq (trans f g) where
  iso := {
    inv := trans hg.iso.inv hf.iso.inv,
    id_l := by
      rw [p_toEq_trans, p_toEq_trans]
      cases toEq f; cases toEq g; cases hf.iso.id_l; cases hg.iso.id_l; rfl,
    id_r := by
      rw [p_toEq_trans, p_toEq_trans]
      cases toEq f; cases toEq g; cases hf.iso.id_r; cases hg.iso.id_r; rfl
  }

/-- 9. Cylinder object. -/
structure Cylinder (a : A) where
  C : A
  i0 : Path A a C
  i1 : Path A a C
  σ : Path A C a
  ret0 : toEq (trans i0 σ) = rfl
  ret1 : toEq (trans i1 σ) = rfl
  weq_σ : IsWeq σ

/-- 10. Path object. -/
structure PathObj (a : A) where
  P : A
  s : Path A a P
  ev0 : Path A P a
  ev1 : Path A P a
  sec0 : toEq (trans s ev0) = rfl
  sec1 : toEq (trans s ev1) = rfl
  weq_s : IsWeq s

/-- 11. Left homotopy relation. -/
def LeftHtpy {a b : A} (f g : Path A a b) : Type u :=
  Σ (C : Cylinder a), Σ (H : Path A C.C b),
    toEq (trans C.i0 H) = toEq f ∧ toEq (trans C.i1 H) = toEq g

/-- 12. Right homotopy relation. -/
def RightHtpy {a b : A} (f g : Path A a b) : Type u :=
  Σ (P : PathObj b), Σ (H : Path A a P.P),
    toEq (trans H P.ev0) = toEq f ∧ toEq (trans H P.ev1) = toEq g

/-- 13. Left htpy refl. -/
def left_htpy_refl {a b : A} (f : Path A a b) (C : Cylinder a) : LeftHtpy f f :=
  ⟨C, trans C.σ f, by rw [p_toEq_trans]; cases toEq f; rw [C.ret0]; rfl,
                  by rw [p_toEq_trans]; cases toEq f; rw [C.ret1]; rfl⟩

/-- 14. Right htpy refl. -/
def right_htpy_refl {a b : A} (f : Path A a b) (P : PathObj b) : RightHtpy f f :=
  ⟨P, trans f P.s, by rw [p_toEq_trans]; cases toEq f; rw [P.sec0]; rfl,
                   by rw [p_toEq_trans]; cases toEq f; rw [P.sec1]; rfl⟩

/-- 15. HasLift property. -/
def HasLift {a b c d : A} (i : Path A a b) (p : Path A c d) : Type u :=
  ∀ (f : Path A a c) (g : Path A b d),
    toEq (trans f p) = toEq (trans i g) →
    { h : Path A b c // toEq (trans i h) = toEq f ∧ toEq (trans h p) = toEq g }

/-- 16. transport swap. -/
theorem transport_swap {a b : A} (p : Path A a b) {D : A → Sort v} (x : D a) (y : D b) (h : transport p x = y) :
    transport (symm p) y = x := by
  rw [← h, p_transport_symm_left]

/-- 17. toEq quad. -/
theorem toEq_quad {a b c d e : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) (s4 : Step A d e) :
    toEq (cons s1 (cons s2 (cons s3 (cons s4 (nil e))))) = (Step.toEq s1).trans ((Step.toEq s2).trans ((Step.toEq s3).trans (Step.toEq s4))) := rfl

/-- 18. toEq triple. -/
theorem toEq_triple {a b c d : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) :
    toEq (cons s1 (cons s2 (cons s3 (nil d)))) = (Step.toEq s1).trans ((Step.toEq s2).trans (Step.toEq s3)) := rfl

/-- 19. transport triple. -/
theorem transport_triple {D : A → Sort v} {a b c d : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) (x : D a) :
    transport (cons s1 (cons s2 (cons s3 (nil d)))) x =
      transport (cons s3 (nil d)) (transport (cons s2 (nil c)) (transport (cons s1 (nil b)) x)) := by
  simp [transport, toEq, Step.toEq]
  cases Step.toEq s1; cases Step.toEq s2; cases Step.toEq s3; rfl

/-- 20. symm of trans. -/
theorem symm_trans {a b c : A} (p : Path A a b) (q : Path A b c) :
    symm (trans p q) = trans (symm q) (symm p) := by
  induction p with
  | nil _ =>
    unfold trans symm
    induction q with
    | nil _ => rfl
    | cons s q ih =>
      show trans (symm (cons s q)) (nil _) = symm (cons s q)
      induction (symm (cons s q)) with
      | nil _ => rfl
      | cons s' p' ih' => rfl
  | cons s p ih =>
    unfold trans symm
    rw [ih, p_trans_assoc]
    rfl

/-- 21. weq inverse is weq. -/
def weq_symm_inv {a b : A} {f : Path A a b} (hf : IsWeq f) : IsWeq hf.inv where
  iso := { inv := f, id_l := hf.id_r, id_r := hf.id_l }

/-- 22. weq identity. -/
def weq_id_data (a : A) : IsWeq (nil a) where
  iso := { inv := nil a, id_l := rfl, id_r := rfl }

/-- 23. composition of fibrations. -/
def fib_comp_data {a b c : A} {p : Path A a b} {q : Path A b c}
    (hp : ∀ {x y : A} (i : Path A x y), IsWeq i → HasLift i p)
    (hq : ∀ {x y : A} (i : Path A x y), IsWeq i → HasLift i q) :
    ∀ {x y : A} (i : Path A x y), IsWeq i → HasLift i (trans p q) := by
  intro x y i hi f g eq
  let ⟨l1, hl1_a, hl1_b⟩ := hq i hi f (trans p g) (by rw [p_toEq_trans]; cases toEq p; exact eq)
  let ⟨l2, hl2_a, hl2_b⟩ := hp i hi l1 g (by rw [p_toEq_trans, hl1_a, p_toEq_trans])
  exact ⟨l2, hl2_a, by rw [p_toEq_trans]; cases toEq q; rw [← hl1_b, ← hl2_b, p_toEq_trans]⟩

/-- 24. composition of cofibrations. -/
def cof_comp_data {a b c : A} {i : Path A a b} {j : Path A b c}
    (hi : ∀ {x y : A} (p : Path A x y), IsWeq p → HasLift i p)
    (hj : ∀ {x y : A} (p : Path A x y), IsWeq p → HasLift j p) :
    ∀ {x y : A} (p : Path A x y), IsWeq p → HasLift (trans i j) p := by
  intro x y p hp f g eq
  let ⟨l1, hl1_a, hl1_b⟩ := hi p hp (trans j f) g (by rw [p_toEq_trans]; cases toEq j; exact eq)
  let ⟨l2, hl2_a, hl2_b⟩ := hj p hp f l1 (by rw [p_toEq_trans, hl1_b, p_toEq_trans])
  exact ⟨l2, by rw [p_toEq_trans]; cases toEq i; rw [← hl1_a, ← hl2_a, p_toEq_trans], hl2_b⟩

/-- 25. transport along congrArg id. -/
theorem transport_congr_id {a b : A} (p : Path A a b) {D : A → Sort v} (x : D a) :
    transport (congrArg (fun z => z) p) x = transport p x := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    unfold congrArg transport toEq
    rw [Step.toEq, ih]
    cases Step.toEq s; rfl

/-- 26. IsIso uniqueness of toEq. -/
theorem iso_unique {a b : A} {p : Path A a b} (i1 i2 : IsIso p) : toEq i1.inv = toEq i2.inv := by
  have h1 := i1.id_l
  have h2 := i2.id_l
  rw [p_toEq_trans] at h1 h2
  cases toEq p; rw [_root_.Eq.refl_trans] at h1 h2; rw [h1, h2]

/-- 27. transport along symm symm. -/
theorem transport_symm_symm {D : A → Sort v} {a b : A} (p : Path A a b) (x : D a) :
    transport (symm (symm p)) x = transport p x := by
  unfold transport
  rw [p_toEq_symm, p_toEq_symm]
  cases toEq p; rfl

/-- 28. toEq of nil. -/
theorem toEq_nil (a : A) : toEq (nil (A := A) a) = rfl := rfl

/-- 29. toEq of cons. -/
theorem toEq_cons {a b c : A} (s : Step A a b) (p : Path A b c) :
    toEq (cons s p) = (Step.toEq s).trans (toEq p) := rfl

/-- 30. transport nil. -/
theorem transport_nil_id {D : A → Sort v} {a : A} (x : D a) : transport (nil a) x = x := rfl

/-- 31. symm symm identity. -/
theorem p_symm_symm_toEq {a b : A} (p : Path A a b) : toEq (symm (symm p)) = toEq p := by
  rw [p_toEq_symm, p_toEq_symm]
  cases toEq p; rfl

/-- 32. nil is identity for trans. -/
theorem trans_nil_r {a b : A} (p : Path A a b) : trans p (nil b) = p := path_trans_nil p

/-- 33. nil is identity for trans (left). -/
theorem trans_nil_l {a b : A} (p : Path A a b) : trans (nil a) p = p := rfl

/-- 34. weq transport roundtrip. -/
theorem weq_transport_id {a b : A} {f : Path A a b} (hf : IsWeq f) {D : A → Sort v} (x : D a) :
    transport hf.inv (transport f x) = x := transport_weq_inv hf x

/-- 35. Whitehead snippet: weq is iso. -/
def weq_to_iso {a b : A} (f : Path A a b) (hf : IsWeq f) : IsIso f := hf.iso

/-- 36. weq composition property. -/
def weq_comp_is_weq {a b c : A} {f : Path A a b} {g : Path A b c} (hf : IsWeq f) (hg : IsWeq g) : IsWeq (trans f g) := weq_comp hf hg

/-- 37. transport constant family property. -/
theorem transport_const_family {a b : A} (p : Path A a b) (B : Type u) (x : B) :
    transport (D := fun _ => B) p x = x := transport_const p B x

/-- 38. path object ev0 section. -/
theorem path_obj_ev0_s {a : A} (P : PathObj a) : toEq (trans P.s P.ev0) = rfl := P.sec0

/-- 39. cylinder i0 retraction. -/
theorem cylinder_i0_σ {a : A} (C : Cylinder a) : toEq (trans C.i0 C.σ) = rfl := C.ret0

/-- 40. derived map toEq preservation. -/
theorem derived_map_pres {B : Type u} (F : A → B) (p : Path A a b) :
    toEq (congrArg F p) = _root_.congrArg F (toEq p) := p_toEq_congrArg F p

end ModelCategoryDeep
end ComputationalPaths
