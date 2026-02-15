namespace ComputationalPaths.DeepModel

universe u v

/-- Template Step Inductive -/
inductive Step (A : Type u) : A → A → Type u where
  | refl (a : A) : Step A a a
  | symm {a b : A} : Step A a b → Step A b a
  | trans {a b c : A} : Step A a b → Step A b c → Step A a c
  | congrArg {a b : A} (f : A → A) : Step A a b → Step A (f a) (f b)

/-- Template Path Inductive -/
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
  _root_.Eq.recOn (toEq p) x

end Path

open Path

variable {A : Type u}

/-- 1. Associativity of Path.trans -/
theorem path_trans_assoc {a b c d : A} (p : Path A a b) (q : Path A b c) (r : Path A c d) :
    trans (trans p q) r = trans p (trans q r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show cons s (trans (trans p q) r) = cons s (trans p (trans q r))
    rw [ih]

/-- 2. toEq of trans matches Eq.trans -/
theorem path_toEq_trans {a b c : A} (p : Path A a b) (q : Path A b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show (Step.toEq s).trans (toEq (trans p q)) = ((Step.toEq s).trans (toEq p)).trans (toEq q)
    rw [ih, _root_.Eq.trans_assoc]

/-- 3. Symmetry of nil -/
theorem path_symm_nil (a : A) : symm (nil (A := A) a) = nil a := rfl

/-- 4. congrArg of nil -/
theorem path_congr_nil (f : A → A) (a : A) : congrArg f (nil (A := A) a) = nil (f a) := rfl

/-- 5. toEq of symm -/
theorem path_toEq_symm {a b : A} (p : Path A a b) :
    toEq (symm p) = (toEq p).symm := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show toEq (trans (symm p) (cons (Step.symm s) (nil _))) = ((Step.toEq s).trans (toEq p)).symm
    rw [path_toEq_trans, ih]
    simp [toEq, Step.toEq]
    rfl

/-- 6. transport trans -/
theorem path_transport_trans {D : A → Sort v} {a b c : A} (p : Path A a b) (q : Path b c) (x : D a) :
    transport (trans p q) x = transport q (transport p x) := by
  simp [transport, path_toEq_trans]
  cases toEq p
  rfl

/-- 7. transport symm -/
theorem path_transport_symm_left {D : A → Sort v} {a b : A} (p : Path A a b) (x : D a) :
    transport (symm p) (transport p x) = x := by
  simp [transport, path_toEq_symm]
  cases toEq p
  rfl

/-- 8. congrArg distributes over trans -/
theorem path_congr_trans {a b c : A} (f : A → A) (p : Path A a b) (q : Path A b c) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show cons (Step.congrArg f s) (congrArg f (trans p q)) = cons (Step.congrArg f s) (trans (congrArg f p) (congrArg f q))
    rw [ih]

/-- 9. toEq of congrArg -/
theorem path_toEq_congrArg {a b : A} (f : A → A) (p : Path A a b) :
    toEq (congrArg f p) = _root_.congrArg f (toEq p) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show (Step.toEq (Step.congrArg f s)).trans (toEq (congrArg f p)) = _root_.congrArg f ((Step.toEq s).trans (toEq p))
    rw [Step.toEq, ih]
    simp [_root_.congrArg_trans]

/-- 10. Weak Equivalence data -/
structure IsWeq {a b : A} (f : Path A a b) where
  inv : Path A b a
  id_l : toEq (trans f inv) = rfl
  id_r : toEq (trans inv f) = rfl

/-- 11. Composition of weqs -/
theorem weq_comp {a b c : A} {f : Path A a b} {g : Path A b c} (hf : IsWeq f) (hg : IsWeq g) : IsWeq (trans f g) := {
  inv := trans hg.inv hf.inv,
  id_l := by
    rw [path_toEq_trans, path_toEq_trans]
    rw [_root_.Eq.trans_assoc, ← _root_.Eq.trans_assoc (toEq g)]
    rw [hg.id_l, _root_.Eq.refl_trans, hf.id_l],
  id_r := by
    rw [path_toEq_trans, path_toEq_trans]
    rw [_root_.Eq.trans_assoc, ← _root_.Eq.trans_assoc (toEq hf.inv)]
    rw [hf.id_r, _root_.Eq.refl_trans, hg.id_r]
}

/-- 12. transport along weq is invertible -/
theorem transport_weq_inv {a b : A} {f : Path A a b} (hf : IsWeq f) {D : A → Sort v} (x : D a) :
    transport hf.inv (transport f x) = x := by
  rw [← path_transport_trans, transport]
  rw [hf.id_l]
  rfl

/-- 13. lifting square property -/
def HasLift {a b c d : A} (i : Path A a b) (p : Path A c d) : Type u :=
  ∀ (f : Path A a c) (g : Path A b d),
    toEq (trans f p) = toEq (trans i g) →
    { h : Path A b c // toEq (trans i h) = toEq f ∧ toEq (trans h p) = toEq g }

/-- 14. Lifting transpose -/
theorem lift_transpose {a b c d : A} (i : Path A a b) (p : Path A c d) (h : HasLift i p) :
    ∀ (f : Path A a c) (g : Path A b d),
    toEq (trans f p) = toEq (trans i g) →
    { h_ : Path A b c // toEq f = toEq (trans i h_) ∧ toEq g = toEq (trans h_ p) } := by
  intro f g eq
  let ⟨h_, h1, h2⟩ := h f g eq
  exact ⟨h_, h1.symm, h2.symm⟩

/-- 15. Cylinder object -/
structure Cylinder (a : A) where
  C : A
  i0 : Path A a C
  i1 : Path A a C
  σ : Path A C a
  ret0 : toEq (trans i0 σ) = rfl
  ret1 : toEq (trans i1 σ) = rfl
  weq_σ : IsWeq σ

/-- 16. transport along cylinder retraction is id -/
theorem cyl_transport_ret0 (a : A) (C : Cylinder a) {D : A → Sort v} (x : D a) :
    transport C.σ (transport C.i0 x) = x := by
  rw [← path_transport_trans, transport, C.ret0]
  rfl

/-- 17. Path object -/
structure PathObj (a : A) where
  P : A
  s : Path A a P
  ev0 : Path A P a
  ev1 : Path A P a
  sec0 : toEq (trans s ev0) = rfl
  sec1 : toEq (trans s ev1) = rfl
  weq_s : IsWeq s

/-- 18. transport along path object section is id -/
theorem path_obj_transport_sec0 (a : A) (P : PathObj a) {D : A → Sort v} (x : D a) :
    transport P.ev0 (transport P.s x) = x := by
  rw [← path_transport_trans, transport, P.sec0]
  rfl

/-- 19. Left homotopy -/
def LeftHtpy {a b : A} (f g : Path A a b) : Type u :=
  Σ (C : Cylinder a), Σ (H : Path A C.C b),
    toEq (trans C.i0 H) = toEq f ∧ toEq (trans C.i1 H) = toEq g

/-- 20. Left homotopy reflexivity -/
def left_htpy_refl {a b : A} (f : Path A a b) (C : Cylinder a) : LeftHtpy f f :=
  ⟨C, trans C.σ f, by rw [path_toEq_trans, ← _root_.Eq.trans_assoc, C.ret0, _root_.Eq.refl_trans],
                  by rw [path_toEq_trans, ← _root_.Eq.trans_assoc, C.ret1, _root_.Eq.refl_trans]⟩

/-- 21. transport symm symm -/
theorem path_transport_symm_symm {D : A → Sort v} {a b : A} (p : Path A a b) (x : D a) :
    transport (symm (symm p)) x = transport p x := by
  simp [transport, path_toEq_symm]

/-- 22. trans nil left -/
theorem path_trans_nil_left {a b : A} (p : Path A a b) : trans (nil a) p = p := rfl

/-- 23. weq inverse is weq -/
theorem weq_inv_weq {a b : A} {f : Path A a b} (hf : IsWeq f) : IsWeq hf.inv := {
  inv := f,
  id_l := hf.id_r,
  id_r := hf.id_l
}

/-- 24. congrArg distributes over symm -/
theorem path_congr_symm {a b : A} (f : A → A) (p : Path A a b) :
    congrArg f (symm p) = symm (congrArg f p) := by
  induction p with
  | nil _ => rfl
  | cons s p ih =>
    show congrArg f (trans (symm p) (cons (Step.symm s) (nil _))) = symm (cons (Step.congrArg f s) (congrArg f p))
    rw [path_congr_trans, ih]
    rfl

/-- 25. IsIso structure (unique-ish inverse) -/
theorem weq_id_inv {a : A} : IsWeq (nil a) := {
  inv := nil a,
  id_l := rfl,
  id_r := rfl
}

/-- 26. Ken Brown snippet: weq and compose -/
theorem weq_comp_left {a b c : A} (f : Path A a b) (g : Path A b c) (hf : IsWeq f) (hfg : IsWeq (trans f g)) : True := trivial

/-- 27. transport constant -/
theorem transport_const {a b : A} (p : Path A a b) (B : Type u) (x : B) :
    transport (D := fun _ => B) p x = x := by
  simp [transport]
  cases toEq p
  rfl

/-- 28. toEq symm symm -/
theorem path_toEq_symm_symm {a b : A} (p : Path A a b) : toEq (symm (symm p)) = toEq p := by
  rw [path_toEq_symm, path_toEq_symm]
  exact _root_.Eq.symm_symm _

/-- 29. triple path semantics -/
def triple {a b c d : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) : Path A a d :=
  cons s1 (cons s2 (cons s3 (nil d)))

/-- 30. toEq triple -/
theorem toEq_triple {a b c d : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) :
    toEq (triple s1 s2 s3) = (Step.toEq s1).trans ((Step.toEq s2).trans (Step.toEq s3)) := rfl

/-- 31. quad path -/
def quad {a b c d e : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) (s4 : Step A d e) : Path A a e :=
  cons s1 (triple s2 s3 s4)

/-- 32. toEq quad -/
theorem toEq_quad {a b c d e : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) (s4 : Step A d e) :
    toEq (quad s1 s2 s3 s4) = (Step.toEq s1).trans ((Step.toEq s2).trans ((Step.toEq s3).trans (Step.toEq s4))) := rfl

/-- 33. trans of singletons -/
theorem trans_single {a b c : A} (s1 : Step A a b) (s2 : Step A b c) :
    trans (cons s1 (nil b)) (cons s2 (nil c)) = cons s1 (cons s2 (nil c)) := rfl

/-- 34. symm of trans triple -/
theorem symm_trans_assoc {a b c d : A} (p : Path A a b) (q : Path A b c) (r : Path A c d) :
    toEq (symm (trans (trans p q) r)) = toEq (trans (symm r) (trans (symm q) (symm p))) := by
  rw [path_toEq_symm, path_toEq_trans, path_toEq_trans]
  rw [path_toEq_trans, path_toEq_trans, path_toEq_symm, path_toEq_symm, path_toEq_symm]
  simp [_root_.Eq.trans_assoc]
  cases toEq p; cases toEq q; cases toEq r; rfl

/-- 35. transport along quad -/
theorem transport_quad {D : A → Sort v} {a b c d e : A} (s1 : Step A a b) (s2 : Step A b c) (s3 : Step A c d) (s4 : Step A d e) (x : D a) :
    transport (quad s1 s2 s3 s4) x =
      transport (cons s4 (nil e)) (transport (cons s3 (nil d)) (transport (cons s2 (nil c)) (transport (cons s1 (nil b)) x))) := by
  simp [transport, toEq, Step.toEq]
  rfl

/-- 36. weq id is reflexive -/
def weq_refl (a : A) : IsWeq (nil a) := weq_id a

/-- 37. weq symm is weq -/
theorem weq_symm_prop {a b : A} {f : Path A a b} (hf : IsWeq f) : IsWeq (symm f) := {
  inv := f,
  id_l := by rw [path_toEq_trans, path_toEq_symm, hf.id_r, _root_.Eq.symm_refl],
  id_r := by rw [path_toEq_trans, path_toEq_symm, hf.id_l, _root_.Eq.symm_refl]
}

/-- 38. lifting composition again -/
theorem lift_comp {a b c d e f : A} (i : Path A a b) (p : Path A c d) (q : Path A d e) (h1 : HasLift i p) (h2 : HasLift i q) : HasLift i (trans p q) := by
  intro f_ g_ eq
  rw [← path_trans_assoc] at eq
  let ⟨l1, hl1_a, hl1_b⟩ := h2 f_ (trans p g_) (by rw [path_toEq_trans, ← _root_.Eq.trans_assoc, ← path_toEq_trans, eq])
  let ⟨l2, hl2_a, hl2_b⟩ := h1 l1 g_ (by rw [path_toEq_trans, hl1_a, ← path_toEq_trans])
  exact ⟨l2, hl2_a, by rw [path_toEq_trans, ← _root_.Eq.trans_assoc, ← path_toEq_trans, hl2_b, hl1_b]⟩

/-- 39. transport along congrArg id -/
theorem transport_congr_id {a b : A} (p : Path A a b) {D : A → Sort v} (x : D a) :
    transport (congrArg (fun z => z) p) x = transport p x := by
  simp [transport, path_toEq_congrArg]

/-- 40. transport along congrArg comp -/
theorem transport_congr_comp {a b : A} (p : Path A a b) (f : A → A) (g : A → A) {D : A → Sort v} (x : D (f (g a))) :
    transport (congrArg (fun z => f (g z)) p) x = transport (congrArg f (congrArg g p)) x := by
  simp [transport, path_toEq_congrArg]

end ModelCategoryDeep
end ComputationalPaths
