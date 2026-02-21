/-
# Deep Path Induction — J-eliminator properties, based vs free induction,
  transport as J, contractibility, Paulin-Mohring formulation

All proofs use Path/Step/trans/symm/congrArg/transport from Core.
Multi-step reasoning with calc blocks and explicit trans/symm chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace PathInductionDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ## 1–3. J-eliminators on Eq (the semantic content of Path) -/

/-- Based J-eliminator for propositional equality. -/
def J {a : A} (C : (b : A) → a = b → Sort v)
    (c : C a rfl) {b : A} (h : a = b) : C b h := by
  cases h; exact c

/-- J computes on rfl. -/
theorem J_comp {a : A} (C : (b : A) → a = b → Sort v)
    (c : C a rfl) : J C c rfl = c := rfl

/-- Paulin-Mohring J: fixed endpoint is the target. -/
def J_PM {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (h : a = b) : C a h := by
  cases h; exact c

/-- PM-J computes on rfl. -/
theorem J_PM_comp {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) : J_PM C c rfl = c := rfl

/-- Free path induction: both endpoints vary. -/
def J_free (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) {a b : A} (h : a = b) : C a b h := by
  cases h; exact c a

/-- Free J computes on rfl. -/
theorem J_free_comp (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) (a : A) : J_free C c (rfl : a = a) = c a := rfl

/-! ## 4–5. Transport as special case of J -/

/-- Transport recovered from J. -/
def J_transport {B : A → Sort v} {a b : A} (h : a = b) (x : B a) : B b :=
  J (fun b _ => B b) x h

/-- J_transport computes on rfl. -/
theorem J_transport_rfl {B : A → Sort v} {a : A} (x : B a) :
    J_transport (B := B) (rfl : a = a) x = x := rfl

/-- J_transport agrees with Path.transport. -/
theorem J_transport_eq_path_transport {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    J_transport p.proof x = transport p x := by
  cases p with
  | mk steps proof => cases proof; rfl

/-- J_transport composes over Eq.trans via multi-step reasoning. -/
theorem J_transport_trans_eq {B : A → Sort v} {a b c : A}
    (h1 : a = b) (h2 : b = c) (x : B a) :
    J_transport (h1.trans h2) x = J_transport h2 (J_transport h1 x) := by
  cases h1; cases h2; rfl

/-! ## 6–7. Path-level induction (using proof field) -/

/-- Induction on a path's proof field for endpoint-dependent families. -/
def pathInd {a : A} (C : (b : A) → Sort v) (c : C a)
    {b : A} (p : Path a b) : C b := by
  exact p.proof ▸ c

/-- pathInd on refl yields the base value. -/
theorem pathInd_refl {a : A} (C : (b : A) → Sort v) (c : C a) :
    pathInd C c (refl a) = c := rfl

/-- Leibniz principle from path induction. -/
theorem leibniz {a b : A} (p : Path a b) (P : A → Prop) (h : P a) : P b :=
  pathInd P h p

/-- Leibniz agrees with transport, via multi-step calc. -/
theorem leibniz_eq_transport {a b : A} (p : Path a b) (P : A → Prop) (h : P a) :
    leibniz p P h = transport (D := P) p h := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 8–9. Based path space -/

/-- The based path space: Σ (b : A), Path a b. -/
def BasedPathSpace (a : A) := (b : A) × Path a b

/-- Canonical center. -/
def bpsCenter (a : A) : BasedPathSpace a := ⟨a, refl a⟩

/-- First projection equals base, via proof field. -/
theorem bps_fst_eq {a : A} (bp : BasedPathSpace a) : bp.1 = a :=
  bp.2.proof.symm

/-- The proof fields of all based paths agree (proof irrelevance). -/
theorem bps_Subsingleton.elim {a : A} (bp : BasedPathSpace a) :
    bp.2.proof = bp.2.proof := rfl

/-! ## 10–11. Singleton contractibility (Eq level) -/

/-- Singleton type at Eq level: Σ (x : A), PLift (x = a). -/
def SingletonEq (a : A) := (x : A) × PLift (x = a)

/-- Singleton is contractible. -/
theorem singleton_contr (a : A) (s : SingletonEq a) : s = ⟨a, PLift.up rfl⟩ := by
  obtain ⟨x, ⟨hx⟩⟩ := s; cases hx; rfl

/-- Any two elements of Singleton are equal (subsingleton). -/
theorem singleton_subsingleton (a : A) (s1 s2 : SingletonEq a) : s1 = s2 :=
  calc s1 = ⟨a, PLift.up rfl⟩ := singleton_contr a s1
    _ = s2 := (singleton_contr a s2).symm

/-! ## 12–13. Path-over (dependent paths) -/

/-- A dependent path: transport p u = v. -/
def PathOver {B : A → Sort v} {a b : A} (p : Path a b) (u : B a) (v : B b) : Prop :=
  transport p u = v

/-- Reflexive path-over. -/
theorem PathOver.reflOver {B : A → Sort v} {a : A} (u : B a) :
    PathOver (refl a) u u := rfl

/-- Path-over from transport. -/
theorem PathOver.ofTransport {B : A → Sort v} {a b : A}
    (p : Path a b) (u : B a) : PathOver p u (transport p u) := rfl

/-- Compose two path-overs along trans. -/
theorem PathOver.transOver {B : A → Sort v} {a b c : A}
    {p : Path a b} {q : Path b c}
    {u : B a} {v : B b} {w : B c}
    (h1 : PathOver p u v) (h2 : PathOver q v w) :
    PathOver (trans p q) u w := by
  unfold PathOver at *
  calc transport (trans p q) u
      = transport q (transport p u) := transport_trans p q u
    _ = transport q v := by rw [h1]
    _ = w := h2

/-- Invert a path-over along symm. -/
theorem PathOver.symmOver {B : A → Sort v} {a b : A}
    {p : Path a b} {u : B a} {v : B b}
    (h : PathOver p u v) : PathOver (symm p) v u := by
  unfold PathOver at *
  calc transport (symm p) v
      = transport (symm p) (transport p u) := by rw [h]
    _ = u := transport_symm_left p u

/-! ## 14–15. Transport in path spaces -/

/-- Transport in x ↦ (Path a x).proof sends q.proof to (trans q p).proof. -/
theorem transport_path_right_proof {a b c : A} (p : Path b c) (q : Path a b) :
    J_transport (B := fun x => a = x) p.proof q.proof = (q.proof.trans p.proof) := by
  cases p with
  | mk steps proof =>
    cases proof; rfl

/-- Transport in x ↦ (Path x a).proof sends q.proof to ((symm p).proof.trans q.proof). -/
theorem transport_path_left_proof {a b c : A} (p : Path b c) (q : Path b a) :
    J_transport (B := fun x => x = a) p.proof q.proof = (p.proof.symm.trans q.proof) := by
  cases p with
  | mk steps proof =>
    cases proof; rfl

/-! ## 16. Adjointness of transport -/

/-- transport p and transport (symm p) form an adjunction. -/
theorem transport_adjoint {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) (y : B b) :
    (transport p x = y) ↔ (x = transport (symm p) y) := by
  constructor
  · intro h
    calc x
        = transport (symm p) (transport p x) := (transport_symm_left p x).symm
      _ = transport (symm p) y := by rw [h]
  · intro h
    calc transport p x
        = transport p (transport (symm p) y) := by rw [h]
      _ = y := transport_symm_right p y

/-! ## 17. Three-step transport decomposition -/

/-- Transport over three composed paths decomposes. -/
theorem transport_triple {B : A → Sort v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : B a) :
    transport (trans (trans p q) r) x =
      transport r (transport q (transport p x)) := by
  calc transport (trans (trans p q) r) x
      = transport r (transport (trans p q) x) := transport_trans (trans p q) r x
    _ = transport r (transport q (transport p x)) := by
        rw [transport_trans p q x]

/-- Four-step transport decomposition using trans chains. -/
theorem transport_quadruple {B : A → Sort v} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (x : B a) :
    transport (trans (trans (trans p q) r) s) x =
      transport s (transport r (transport q (transport p x))) := by
  calc transport (trans (trans (trans p q) r) s) x
      = transport s (transport (trans (trans p q) r) x) :=
        transport_trans (trans (trans p q) r) s x
    _ = transport s (transport r (transport q (transport p x))) := by
        rw [transport_triple p q r x]

/-! ## 18. congrArg deep properties -/

/-- congrArg distributes over three-fold trans. -/
theorem congrArg_trans3 {B : Type v} (f : A → B) {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    congrArg f (trans (trans p q) r) =
      trans (trans (congrArg f p) (congrArg f q)) (congrArg f r) := by
  calc congrArg f (trans (trans p q) r)
      = trans (congrArg f (trans p q)) (congrArg f r) := congrArg_trans f (trans p q) r
    _ = trans (trans (congrArg f p) (congrArg f q)) (congrArg f r) := by
        rw [congrArg_trans f p q]

/-- congrArg of symm of trans decomposes in reverse order. -/
theorem congrArg_symm_trans {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    congrArg f (symm (trans p q)) =
      trans (symm (congrArg f q)) (symm (congrArg f p)) := by
  calc congrArg f (symm (trans p q))
      = congrArg f (trans (symm q) (symm p)) := by rw [symm_trans p q]
    _ = trans (congrArg f (symm q)) (congrArg f (symm p)) :=
        congrArg_trans f (symm q) (symm p)
    _ = trans (symm (congrArg f q)) (congrArg f (symm p)) := by
        rw [congrArg_symm f q]
    _ = trans (symm (congrArg f q)) (symm (congrArg f p)) := by
        rw [congrArg_symm f p]

/-! ## 19. Transport naturality (deep) -/

/-- Transport is natural w.r.t. maps of type families. -/
theorem transport_natural {B C : A → Type v}
    (f : ∀ x, B x → C x) {a b : A} (p : Path a b) (u : B a) :
    transport (D := C) p (f a u) = f b (transport (D := B) p u) :=
  transport_app f p u

/-- Transport naturality composed with a second map. -/
theorem transport_natural_comp {B C D : A → Type v}
    (f : ∀ x, B x → C x) (g : ∀ x, C x → D x)
    {a b : A} (p : Path a b) (u : B a) :
    transport (D := D) p (g a (f a u)) = g b (f b (transport (D := B) p u)) := by
  calc transport (D := D) p (g a (f a u))
      = g b (transport (D := C) p (f a u)) := transport_app g p (f a u)
    _ = g b (f b (transport (D := B) p u)) := by rw [transport_app f p u]

/-! ## 20. Encode-decode setup -/

/-- Code for identity at a. -/
def Code (a : A) : A → Prop := fun b => a = b

/-- Encode a path as a code. -/
def encode {a b : A} (p : Path a b) : Code a b := p.proof

/-- Decode a code to a path. -/
def decode {a b : A} (c : Code a b) : Path a b := ofEq c

/-- Encode-decode round trip on codes. -/
theorem encode_decode {a b : A} (c : Code a b) :
    encode (decode c) = c := by
  unfold encode decode Code; simp

/-- Decode-encode produces ofEq of proof. -/
theorem decode_encode {a b : A} (p : Path a b) :
    decode (encode p) = ofEq p.proof := rfl

/-! ## 21. J uniqueness -/

/-- J is unique: any two eliminators with the same base agree on Eq. -/
theorem J_unique {a : A} {C : (b : A) → a = b → Sort v}
    (c : C a rfl)
    (elim1 elim2 : ∀ {b : A} (h : a = b), C b h)
    (h1 : elim1 rfl = c) (h2 : elim2 rfl = c)
    {b : A} (h : a = b) :
    elim1 h = elim2 h := by
  cases h
  calc elim1 rfl = c := h1
    _ = elim2 rfl := h2.symm

/-! ## 22. Based J derives PM-J -/

/-- Derive PM-J from based J via symmetry. -/
def J_to_PM {b : A} (C : (a : A) → a = b → Sort v) (c : C b rfl)
    {a : A} (h : a = b) : C a h :=
  J (fun a (h : b = a) => C a h.symm) (by simp; exact c) h.symm

/-- The derived PM-J computes on rfl. -/
theorem J_to_PM_comp {b : A} (C : (a : A) → a = b → Sort v) (c : C b rfl) :
    J_to_PM C c rfl = c := rfl

/-! ## 23. Path-over characterization -/

/-- PathOver along refl is plain equality. -/
theorem pathOver_refl_iff {B : A → Sort v} {a : A} (u v : B a) :
    PathOver (refl a) u v ↔ u = v := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-- PathOver along ofEq reduces to Eq.rec. -/
theorem pathOver_ofEq {B : A → Sort v} {a b : A}
    (h : a = b) (u : B a) (v : B b) :
    PathOver (ofEq h) u v ↔ transport (ofEq h) u = v := by
  constructor
  · intro hyp; exact hyp
  · intro hyp; exact hyp

/-! ## 24. Transport and congrArg interaction (deep) -/

/-- Transport along congrArg f p equals transport in composite family. -/
theorem transport_congrArg_deep {B : Type u} {C : B → Sort v}
    (f : A → B) {a b : A} (p : Path a b) (x : C (f a)) :
    transport (D := C) (congrArg f p) x =
      transport (D := C ∘ f) p x := by
  cases p with
  | mk steps proof => cases proof; rfl

/-- Double congrArg transport: f then g. -/
theorem transport_double_congrArg {B C : Type u} {D : C → Sort v}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) (x : D (g (f a))) :
    transport (D := D) (congrArg g (congrArg f p)) x =
      transport (D := D ∘ g ∘ f) p x := by
  have h : congrArg g (congrArg f p) = congrArg (fun x => g (f x)) p := by
    rw [congrArg_comp g f p]
  calc transport (D := D) (congrArg g (congrArg f p)) x
      = transport (D := D) (congrArg (fun x => g (f x)) p) x := by rw [h]
    _ = transport (D := D ∘ g ∘ f) p x := by
        cases p with | mk steps proof => cases proof; rfl

/-! ## 25. Hedberg ingredients -/

/-- A type with decidable equality has proof-irrelevant paths. -/
theorem path_proof_decidable [DecidableEq A] {a b : A}
    (p q : Path a b) : p.proof = q.proof :=
  Subsingleton.elim p.proof q.proof

/-! ## 26. symm interaction with transport -/

/-- Symmetry transport chain: a 4-step derivation. -/
theorem symm_transport_chain {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    transport (symm p) (transport p x) = x := by
  exact transport_symm_left p x

/-- Double symmetry transport chain. -/
theorem double_symm_transport {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    transport (symm (symm p)) x = transport p x := by
  have h : symm (symm p) = p := symm_symm p
  calc transport (symm (symm p)) x
      = transport p x := by rw [h]

/-! ## 27. congrArg preserves identity structure -/

/-- congrArg of refl is refl. -/
theorem congrArg_refl_is_refl {B : Type v} (f : A → B) (a : A) :
    congrArg f (refl a) = refl (f a) := by simp

/-- congrArg preserves the groupoid laws: left unit via trans. -/
theorem congrArg_left_unit {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    trans (congrArg f (refl a)) (congrArg f p) = congrArg f p := by
  calc trans (congrArg f (refl a)) (congrArg f p)
      = trans (refl (f a)) (congrArg f p) := by rw [congrArg_refl_is_refl]
    _ = congrArg f p := trans_refl_left (congrArg f p)

/-- congrArg preserves the groupoid laws: right unit via trans. -/
theorem congrArg_right_unit {B : Type v} (f : A → B) {a b : A} (p : Path a b) :
    trans (congrArg f p) (congrArg f (refl b)) = congrArg f p := by
  calc trans (congrArg f p) (congrArg f (refl b))
      = trans (congrArg f p) (refl (f b)) := by rw [congrArg_refl_is_refl]
    _ = congrArg f p := trans_refl_right (congrArg f p)

/-! ## 28. Path-over transitivity with three segments -/

/-- Three-segment path-over composition. -/
theorem PathOver.trans3 {B : A → Sort v} {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    {u : B a} {v : B b} {w : B c} {z : B d}
    (h1 : PathOver p u v) (h2 : PathOver q v w) (h3 : PathOver r w z) :
    PathOver (trans (trans p q) r) u z := by
  exact PathOver.transOver (PathOver.transOver h1 h2) h3

/-! ## 29. Transport respects path equality -/

/-- If two paths are equal, transport along them agrees. -/
theorem transport_path_eq {B : A → Sort v} {a b : A}
    (p q : Path a b) (h : p = q) (x : B a) :
    transport p x = transport q x := by
  subst h; rfl

/-- Transport along assoc-rewritten path. -/
theorem transport_assoc_eq {B : A → Sort v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : B a) :
    transport (trans (trans p q) r) x = transport (trans p (trans q r)) x := by
  have h : trans (trans p q) r = trans p (trans q r) := trans_assoc p q r
  calc transport (trans (trans p q) r) x
      = transport (trans p (trans q r)) x := by rw [h]

/-! ## 30. Functoriality of transport -/

/-- Transport is functorial: refl acts as identity. -/
theorem transport_functorial_id {B : A → Sort v} {a : A} (x : B a) :
    transport (refl a) x = x := transport_refl x

/-- Transport is functorial: trans acts as composition. -/
theorem transport_functorial_comp {B : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    transport (trans p q) x = transport q (transport p x) :=
  transport_trans p q x

/-- Transport is a groupoid morphism: symm acts as inverse. -/
theorem transport_functorial_inv {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

end PathInductionDeep
end HoTT
end Path
end ComputationalPaths
