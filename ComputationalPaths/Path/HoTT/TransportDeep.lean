/-
# Deep Transport Theory via Computational Paths

Transport along composite paths, in dependent pairs, function types,
naturality squares, path-over-path (dependent paths), and apd.
All theorems use multiple Path operations (trans, symm, congrArg, transport,
Step constructors) with multi-step proofs.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.HoTT.TransportDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## 1. Transport along triple composite -/

/-- Transport along a triple composite decomposes into three successive transports. -/
theorem transport_triple_trans {D : A → Sort v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans p q) r) x =
      Path.transport (D := D) r (Path.transport (D := D) q (Path.transport (D := D) p x)) := by
  calc Path.transport (D := D) (Path.trans (Path.trans p q) r) x
      = Path.transport (D := D) r (Path.transport (D := D) (Path.trans p q) x) :=
          Path.transport_trans (Path.trans p q) r x
    _ = Path.transport (D := D) r (Path.transport (D := D) q (Path.transport (D := D) p x)) := by
          rw [Path.transport_trans p q x]

/-! ## 2. Transport along p⁻¹ · p cancellation -/

/-- Transport along p then p⁻¹ cancels (roundtrip from D a back to D a). -/
theorem transport_symm_after_trans {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) = x := by
  calc Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x)
      = Path.transport (D := D) (Path.trans p (Path.symm p)) x :=
          (Path.transport_trans p (Path.symm p) x).symm
    _ = x := by cases p with | mk steps proof => cases proof; rfl

/-! ## 3. Transport along p⁻¹ then p cancellation -/

/-- Transport along p⁻¹ then p cancels. -/
theorem transport_trans_after_symm {D : A → Sort v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y) = y := by
  calc Path.transport (D := D) p (Path.transport (D := D) (Path.symm p) y)
      = Path.transport (D := D) (Path.trans (Path.symm p) p) y :=
          (Path.transport_trans (Path.symm p) p y).symm
    _ = y := by cases p with | mk steps proof => cases proof; rfl

/-! ## 4. Transport naturality for dependent functions -/

/-- If f : ∀ x, D x and p : Path a b, then transport p (f a) = f b. -/
theorem transport_apd_eq {D : A → Type v} (f : ∀ x, D x) {a b : A}
    (p : Path a b) :
    Path.transport (D := D) p (f a) = f b := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 5. Transport in constant families along composite paths -/

/-- Transport in a constant family along a composite is doubly trivial. -/
theorem transport_const_trans {D : Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D) :
    Path.transport (D := fun _ => D) (Path.trans p q) x =
      Path.transport (D := fun _ => D) q (Path.transport (D := fun _ => D) p x) := by
  calc Path.transport (D := fun _ => D) (Path.trans p q) x
      = x := Path.transport_const (Path.trans p q) x
    _ = Path.transport (D := fun _ => D) p x := (Path.transport_const p x).symm
    _ = Path.transport (D := fun _ => D) q (Path.transport (D := fun _ => D) p x) :=
          (Path.transport_const q _).symm

/-! ## 6. Dependent path (PathOver) -/

/-- A dependent path over p : Path a b in family D. -/
structure PathOver {D : A → Type v} {a b : A} (p : Path a b) (u : D a) (v : D b) where
  over_eq : Path.transport (D := D) p u = v

/-- Reflexive dependent path. -/
def PathOver.reflOver {D : A → Type v} {a : A} (u : D a) :
    PathOver (Path.refl a) u u :=
  ⟨by simp [Path.transport]⟩

/-- Dependent path from apd. -/
def PathOver.fromApd {D : A → Type v} (f : ∀ x, D x)
    {a b : A} (p : Path a b) :
    PathOver p (f a) (f b) :=
  ⟨transport_apd_eq f p⟩

/-! ## 7. PathOver composition along trans -/

/-- Compose dependent paths over a composite base path. -/
def PathOver.trans' {D : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c}
    {u : D a} {v : D b} {w : D c}
    (po₁ : PathOver p u v) (po₂ : PathOver q v w) :
    PathOver (Path.trans p q) u w :=
  ⟨by
    calc Path.transport (D := D) (Path.trans p q) u
        = Path.transport (D := D) q (Path.transport (D := D) p u) :=
            Path.transport_trans p q u
      _ = Path.transport (D := D) q v := by rw [po₁.over_eq]
      _ = w := po₂.over_eq⟩

/-! ## 8. PathOver symmetry -/

/-- Reverse a dependent path. -/
def PathOver.symm' {D : A → Type v} {a b : A}
    {p : Path a b} {u : D a} {v : D b}
    (po : PathOver p u v) :
    PathOver (Path.symm p) v u :=
  ⟨by
    calc Path.transport (D := D) (Path.symm p) v
        = Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p u) := by
            rw [po.over_eq]
      _ = u := Path.transport_symm_left p u⟩

/-! ## 9. Transport in function types -/

/-- Transport in a function type family. -/
theorem transport_fun {D E : A → Type v} {a b : A}
    (p : Path a b) (f : D a → E a) (d : D b) :
    Path.transport (D := fun x => D x → E x) p f d =
      Path.transport (D := E) p (f (Path.transport (D := D) (Path.symm p) d)) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 10. Transport in function types — roundtrip -/

/-- Applying transport-of-function then feeding transported input. -/
theorem transport_fun_roundtrip {D E : A → Type v} {a b : A}
    (p : Path a b) (f : D a → E a) (d : D a) :
    Path.transport (D := fun x => D x → E x) p f (Path.transport (D := D) p d) =
      Path.transport (D := E) p (f d) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 11. Transport compose: D ∘ f -/

/-- Transport in a composite family D ∘ f factors through congrArg. -/
theorem transport_compose_deep {X Y : Type u} {D : Y → Type v}
    (f : X → Y) {x₁ x₂ : X} (p : Path x₁ x₂) (d : D (f x₁)) :
    Path.transport (D := D ∘ f) p d =
      Path.transport (D := D) (Path.congrArg f p) d := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]

/-! ## 12. Double transport compose -/

/-- Transport along congrArg of congrArg. -/
theorem transport_double_compose {X Y Z : Type u} {D : Z → Type v}
    (f : X → Y) (g : Y → Z) {x₁ x₂ : X}
    (p : Path x₁ x₂) (d : D (g (f x₁))) :
    Path.transport (D := D ∘ g ∘ f) p d =
      Path.transport (D := D) (Path.congrArg g (Path.congrArg f p)) d := by
  calc Path.transport (D := D ∘ g ∘ f) p d
      = Path.transport (D := D ∘ g) (Path.congrArg f p) d := by
          cases p with | mk steps proof => cases proof; simp [Path.transport]
    _ = Path.transport (D := D) (Path.congrArg g (Path.congrArg f p)) d := by
          cases p with | mk steps proof => cases proof; simp [Path.transport]

/-! ## 13. Naturality of transport with respect to maps between families -/

/-- If φ : ∀ x, D x → E x then transport commutes with φ. -/
theorem transport_natural {D E : A → Type v}
    (φ : ∀ x, D x → E x) {a b : A} (p : Path a b) (d : D a) :
    Path.transport (D := E) p (φ a d) = φ b (Path.transport (D := D) p d) :=
  Path.transport_app φ p d

/-! ## 14. Transport natural for composite paths -/

/-- Naturality of transport with φ decomposes over a composite path. -/
theorem transport_natural_trans {D E : A → Type v}
    (φ : ∀ x, D x → E x) {a b c : A}
    (p : Path a b) (q : Path b c) (d : D a) :
    φ c (Path.transport (D := D) (Path.trans p q) d) =
      Path.transport (D := E) q (φ b (Path.transport (D := D) p d)) := by
  calc φ c (Path.transport (D := D) (Path.trans p q) d)
      = φ c (Path.transport (D := D) q (Path.transport (D := D) p d)) := by
          rw [Path.transport_trans p q d]
    _ = Path.transport (D := E) q (φ b (Path.transport (D := D) p d)) := by
          rw [← transport_natural φ q (Path.transport (D := D) p d)]

/-! ## 15. Quadruple transport decomposition -/

/-- Transport along a quadruple composite decomposes into four. -/
theorem transport_quadruple_trans {D : A → Sort v} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans (Path.trans p q) r) s) x =
      Path.transport (D := D) s
        (Path.transport (D := D) r
          (Path.transport (D := D) q
            (Path.transport (D := D) p x))) := by
  calc Path.transport (D := D) (Path.trans (Path.trans (Path.trans p q) r) s) x
      = Path.transport (D := D) s
          (Path.transport (D := D) (Path.trans (Path.trans p q) r) x) :=
          Path.transport_trans _ s x
    _ = Path.transport (D := D) s
          (Path.transport (D := D) r
            (Path.transport (D := D) (Path.trans p q) x)) := by
          rw [Path.transport_trans (Path.trans p q) r x]
    _ = Path.transport (D := D) s
          (Path.transport (D := D) r
            (Path.transport (D := D) q
              (Path.transport (D := D) p x))) := by
          rw [Path.transport_trans p q x]

/-! ## 16. Transport conjugation -/

/-- Conjugation: transport p ∘ transport p⁻¹ ∘ transport p = transport p. -/
theorem transport_conjugation {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) p
      (Path.transport (D := D) (Path.symm p)
        (Path.transport (D := D) p x)) =
      Path.transport (D := D) p x := by
  calc Path.transport (D := D) p
        (Path.transport (D := D) (Path.symm p)
          (Path.transport (D := D) p x))
      = Path.transport (D := D) (Path.trans (Path.symm p) p)
          (Path.transport (D := D) p x) :=
          (Path.transport_trans (Path.symm p) p _).symm
    _ = Path.transport (D := D) p x := by
          cases p with
          | mk steps proof => cases proof; rfl

/-! ## 17. PathOver for constant families -/

/-- In a constant family, PathOver reduces to equality. -/
theorem pathover_const {D : Type v} {a b : A}
    (p : Path a b) (u v : D) :
    PathOver (D := fun _ => D) p u v ↔ u = v := by
  constructor
  · intro po
    have h := po.over_eq
    rw [Path.transport_const] at h
    exact h
  · intro h
    exact ⟨by rw [Path.transport_const]; exact h⟩

/-! ## 18. Transport in product type -/

/-- Transport in a product family decomposes componentwise. -/
theorem transport_prod {D E : A → Type v} {a b : A}
    (p : Path a b) (x : D a × E a) :
    Path.transport (D := fun z => D z × E z) p x =
      (Path.transport (D := D) p x.1, Path.transport (D := E) p x.2) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 19. Transport product along composite -/

/-- Transport of product along composite decomposes both ways. -/
theorem transport_prod_trans {D E : A → Type v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a × E a) :
    Path.transport (D := fun z => D z × E z) (Path.trans p q) x =
      (Path.transport (D := D) q (Path.transport (D := D) p x.1),
       Path.transport (D := E) q (Path.transport (D := E) p x.2)) := by
  calc Path.transport (D := fun z => D z × E z) (Path.trans p q) x
      = Path.transport (D := fun z => D z × E z) q
          (Path.transport (D := fun z => D z × E z) p x) := by
          cases p with | mk s1 h1 => cases h1; cases q with | mk s2 h2 => cases h2; rfl
    _ = Path.transport (D := fun z => D z × E z) q
          (Path.transport (D := D) p x.1, Path.transport (D := E) p x.2) := by
          rw [transport_prod p x]
    _ = (Path.transport (D := D) q (Path.transport (D := D) p x.1),
         Path.transport (D := E) q (Path.transport (D := E) p x.2)) :=
          transport_prod q (Path.transport (D := D) p x.1, Path.transport (D := E) p x.2)

/-! ## 20. Transport along congrArg preserves trans -/

/-- Transport along congrArg of trans decomposes. -/
theorem transport_congrArg_trans {X : Type u} {D : A → Type v}
    (f : X → A) {x y z : X} (p : Path x y) (q : Path y z)
    (d : D (f x)) :
    Path.transport (D := D) (Path.congrArg f (Path.trans p q)) d =
      Path.transport (D := D) (Path.congrArg f q)
        (Path.transport (D := D) (Path.congrArg f p) d) := by
  calc Path.transport (D := D) (Path.congrArg f (Path.trans p q)) d
      = Path.transport (D := D) (Path.trans (Path.congrArg f p) (Path.congrArg f q)) d := by
          rw [Path.congrArg_trans f p q]
    _ = Path.transport (D := D) (Path.congrArg f q)
          (Path.transport (D := D) (Path.congrArg f p) d) :=
          Path.transport_trans (Path.congrArg f p) (Path.congrArg f q) d

/-! ## 21. Transport along congrArg symm -/

/-- Transport along congrArg of symm inverts. -/
theorem transport_congrArg_symm {X : Type u} {D : A → Type v}
    (f : X → A) {x y : X} (p : Path x y)
    (d : D (f y)) :
    Path.transport (D := D) (Path.congrArg f (Path.symm p)) d =
      Path.transport (D := D) (Path.symm (Path.congrArg f p)) d := by
  rw [Path.congrArg_symm f p]

/-! ## 22. Transport along congrArg roundtrip -/

/-- Transport along congrArg f p then congrArg f p⁻¹ cancels. -/
theorem transport_congrArg_roundtrip {X : Type u} {D : A → Type v}
    (f : X → A) {x y : X} (p : Path x y)
    (d : D (f x)) :
    Path.transport (D := D) (Path.congrArg f (Path.symm p))
      (Path.transport (D := D) (Path.congrArg f p) d) = d := by
  calc Path.transport (D := D) (Path.congrArg f (Path.symm p))
        (Path.transport (D := D) (Path.congrArg f p) d)
      = Path.transport (D := D) (Path.symm (Path.congrArg f p))
          (Path.transport (D := D) (Path.congrArg f p) d) := by
          rw [Path.congrArg_symm f p]
    _ = d := Path.transport_symm_left (Path.congrArg f p) d

/-! ## 23. Transport in path family (target) -/

/-- Transport along p in the family (fun x => Path c x) for a proof-irrelevant result. -/
theorem transport_path_tgt_eq {a b c : A}
    (p : Path a b) (q : Path c a) :
    (Path.transport (D := fun x => Path c x) p q).toEq =
      (Path.trans q p).toEq := by
  cases p with
  | mk s1 h1 => cases h1; simp

/-! ## 24. Transport in path family (source) -/

/-- Transport along p in the family (fun x => Path x c) for a proof-irrelevant result. -/
theorem transport_path_src_eq {a b c : A}
    (p : Path a b) (q : Path a c) :
    (Path.transport (D := fun x => Path x c) p q).toEq =
      (Path.trans (Path.symm p) q).toEq := by
  cases p with
  | mk s1 h1 => cases h1; simp

/-! ## 25. apd along refl is trivial -/

/-- apd of any function along refl is refl. -/
theorem apd_refl_is_refl {D : A → Type v} (f : ∀ x, D x) (a : A) :
    Path.apd f (Path.refl a) = Path.refl (f a) := by
  simp [Path.apd, Path.transport]

/-! ## 26. apd for non-dependent functions -/

/-- apd of a non-dependent function reduces to congrArg at the proof level. -/
theorem apd_nondep {f : A → B} {a b : A} (p : Path a b) :
    (Path.apd (B := fun _ => B) f p).toEq =
      ((Path.transport_const p (f a)).trans (Path.congrArg f p).toEq) := by
  cases p with
  | mk steps proof => cases proof; simp

/-! ## 27. Transport preserves paths (congruence) -/

/-- If two values are path-equal, their transports are path-equal. -/
def transport_path_cong {D : A → Type v} {a b : A}
    (p : Path a b) {u w : D a}
    (q : Path u w) :
    Path (Path.transport (D := D) p u) (Path.transport (D := D) p w) := by
  cases p with
  | mk s1 h1 => cases h1; simp [Path.transport]; exact q

/-! ## 28. Transport along ofEq then symm roundtrip -/

/-- Transport along ofEq h, then along symm (ofEq h), is identity. -/
theorem transport_ofEq_symm_cancel {D : A → Type v} {a b : A}
    (h : a = b) (x : D a) :
    Path.transport (D := D) (Path.symm (Path.ofEq h))
      (Path.transport (D := D) (Path.ofEq h) x) = x := by
  calc Path.transport (D := D) (Path.symm (Path.ofEq h))
        (Path.transport (D := D) (Path.ofEq h) x)
      = Path.transport (D := D) (Path.trans (Path.ofEq h) (Path.symm (Path.ofEq h))) x :=
          (Path.transport_trans (Path.ofEq h) (Path.symm (Path.ofEq h)) x).symm
    _ = x := by cases h; rfl

/-! ## 29. cast_eq_transport -/

/-- Path.cast equals transport. -/
theorem cast_eq_transport {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.cast (D := D) p x = Path.transport (D := D) p x := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 30. Transport along reassociated paths -/

/-- Transport is invariant under path reassociation. -/
theorem transport_assoc_invariant {D : A → Sort v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans p q) r) x =
      Path.transport (D := D) (Path.trans p (Path.trans q r)) x := by
  calc Path.transport (D := D) (Path.trans (Path.trans p q) r) x
      = Path.transport (D := D) r
          (Path.transport (D := D) q
            (Path.transport (D := D) p x)) :=
          transport_triple_trans p q r x
    _ = Path.transport (D := D) (Path.trans q r)
          (Path.transport (D := D) p x) :=
          (Path.transport_trans q r _).symm
    _ = Path.transport (D := D) (Path.trans p (Path.trans q r)) x :=
          (Path.transport_trans p (Path.trans q r) x).symm

/-! ## 31. PathOver trans then symm cancels -/

/-- Composing a dependent path with its reverse yields identity transport. -/
theorem pathover_trans_symm {D : A → Type v} {a b : A}
    {p : Path a b} {u : D a} {v : D b}
    (po : PathOver p u v) :
    (PathOver.trans' po (PathOver.symm' po)).over_eq =
      (by rw [Path.transport_trans]; exact Path.transport_symm_left p u) := by
  apply Subsingleton.elim

/-! ## 32. Transport pullback with triple compose -/

/-- Transport pullback along triple congrArg. -/
theorem transport_triple_congrArg {X Y Z W : Type u} {D : W → Type v}
    (f : X → Y) (g : Y → Z) (h : Z → W)
    {x₁ x₂ : X} (p : Path x₁ x₂) (d : D (h (g (f x₁)))) :
    Path.transport (D := D ∘ h ∘ g ∘ f) p d =
      Path.transport (D := D) (Path.congrArg h (Path.congrArg g (Path.congrArg f p))) d := by
  calc Path.transport (D := D ∘ h ∘ g ∘ f) p d
      = Path.transport (D := D ∘ h ∘ g) (Path.congrArg f p) d := by
          cases p with | mk steps proof => cases proof; simp [Path.transport]
    _ = Path.transport (D := D ∘ h) (Path.congrArg g (Path.congrArg f p)) d := by
          cases p with | mk steps proof => cases proof; simp [Path.transport]
    _ = Path.transport (D := D) (Path.congrArg h (Path.congrArg g (Path.congrArg f p))) d := by
          cases p with | mk steps proof => cases proof; simp [Path.transport]

/-! ## 33. Transport product symmetric -/

/-- Transport of product along symm decomposes symmetrically. -/
theorem transport_prod_symm {D E : A → Type v} {a b : A}
    (p : Path a b) (x : D b × E b) :
    Path.transport (D := fun z => D z × E z) (Path.symm p) x =
      (Path.transport (D := D) (Path.symm p) x.1,
       Path.transport (D := E) (Path.symm p) x.2) :=
  transport_prod (Path.symm p) x

/-! ## 34. Transport function along symm -/

/-- Transport of function type along symm relates to forward transport. -/
theorem transport_fun_symm {D E : A → Type v} {a b : A}
    (p : Path a b) (g : D b → E b) (d : D a) :
    Path.transport (D := fun x => D x → E x) (Path.symm p) g d =
      Path.transport (D := E) (Path.symm p) (g (Path.transport (D := D) p d)) := by
  calc Path.transport (D := fun x => D x → E x) (Path.symm p) g d
      = Path.transport (D := E) (Path.symm p)
          (g (Path.transport (D := D) (Path.symm (Path.symm p)) d)) :=
          transport_fun (Path.symm p) g d
    _ = Path.transport (D := E) (Path.symm p) (g (Path.transport (D := D) p d)) := by
          cases p with
          | mk steps proof => cases proof; rfl

/-! ## 35. Transport via congrArg identity is no-op -/

/-- Transport along congrArg id p is the same as transport along p. -/
theorem transport_congrArg_id {D : A → Type v} {a b : A}
    (p : Path a b) (d : D a) :
    Path.transport (D := D) (Path.congrArg (fun x => x) p) d =
      Path.transport (D := D) p d := by
  rw [Path.congrArg_id]

/-! ## 36. PathOver constant transport -/

/-- PathOver in constant family from transport_const. -/
def pathover_of_eq_const {D : Type v} {a b : A}
    (p : Path a b) {u v : D} (h : u = v) :
    PathOver (D := fun _ => D) p u v :=
  ⟨by rw [Path.transport_const]; exact h⟩

/-! ## 37. Transport in Sigma fst -/

/-- Transport of Sigma first component. -/
theorem transport_sigma_fst' {D E : A → Type v}
    {a b : A} (p : Path a b) (x : D a) (y : E a) :
    (Path.transport (D := fun z => D z × E z) p (x, y)).1 =
      Path.transport (D := D) p x := by
  have h := transport_prod (D := D) (E := E) p (x, y)
  rw [h]

/-! ## 38. PathOver trans associativity -/

/-- PathOver composition is associative (proof-irrelevant). -/
theorem pathover_trans_assoc {D : A → Type v} {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    {u : D a} {v : D b} {w : D c} {z : D d}
    (po₁ : PathOver p u v) (po₂ : PathOver q v w) (po₃ : PathOver r w z) :
    (PathOver.trans' (PathOver.trans' po₁ po₂) po₃).over_eq =
      (transport_assoc_invariant (D := D) p q r u ▸
       (PathOver.trans' po₁ (PathOver.trans' po₂ po₃)).over_eq) := by
  apply Subsingleton.elim

/-! ## 39. Transport commutes with congrArg for families -/

/-- Transport in (D ∘ f) along p equals transport in D along (congrArg f p),
    composed with the triple decomposition. -/
theorem transport_congrArg_triple {X Y : Type u} {D : A → Type v}
    (f : X → Y) (g : Y → A) {x₁ x₂ : X}
    (p : Path x₁ x₂) (d : D (g (f x₁))) :
    Path.transport (D := D ∘ g ∘ f) p d =
      Path.transport (D := D) (Path.congrArg (fun x => g (f x)) p) d := by
  calc Path.transport (D := D ∘ g ∘ f) p d
      = Path.transport (D := D) (Path.congrArg g (Path.congrArg f p)) d :=
          transport_double_compose f g p d
    _ = Path.transport (D := D) (Path.congrArg (fun x => g (f x)) p) d := by
          rw [← Path.congrArg_comp g f p]

/-! ## 40. Double PathOver symmetry is identity -/

/-- Reversing a dependent path twice recovers the original. -/
theorem pathover_symm_symm {D : A → Type v} {a b : A}
    {p : Path a b} {u : D a} {v : D b}
    (po : PathOver p u v) :
    (PathOver.symm' (PathOver.symm' po)).over_eq =
      (by rw [Path.symm_symm]; exact po.over_eq) := by
  apply Subsingleton.elim

end ComputationalPaths.Path.HoTT.TransportDeep
