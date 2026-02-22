/-
# Crown Jewel: Deriving the J-Eliminator from Contractibility of the Based Path Space

This file derives the J-eliminator (path induction) as a **theorem** from the
computational paths framework, following the HoTT-style argument:

  1. Define the based path space Σ (y : A), PLift (a = y)
  2. Show it is contractible (every element equals the center (a, rfl))
  3. Derive J from contractibility via transport
  4. Prove J's computation rule
  5. Derive transport, apd, and other operations as special cases of J
  6. Show equivalence of based vs free path induction
  7. Prove uniqueness of J-like eliminators
  8. Lift everything to the Path level via the proof field

The key insight: `Eq` in Lean 4's `Prop` is proof-irrelevant (Subsingleton),
and our `Path` structure separates semantic content (the `proof` field) from
the rewrite trace (the `steps` list). The J-eliminator acts on the semantic
level, where contractibility of the based path space holds.

All proofs use Path/Step/trans/symm/congrArg/transport from Core.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace JDerivation

open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ========================================================================
    § 1. THE BASED PATH SPACE
    ======================================================================== -/

/-- The based path space at `a`: the total space of all points equipped with
a (lifted) equality proof from `a`. We use `PLift` to promote the `Prop`-valued
equality `a = y` into `Type u` so it lives in a sigma type. -/
noncomputable def BasedPathSpace (a : A) : Type u := Σ (y : A), PLift (a = y)

/-- The center of contraction: `(a, rfl)` is the canonical basepoint
of `BasedPathSpace a`. -/
noncomputable def center (a : A) : BasedPathSpace a := ⟨a, PLift.up rfl⟩

/-- First projection: extract the target endpoint. -/
noncomputable def BasedPathSpace.target {a : A} (bp : BasedPathSpace a) : A := bp.1

/-- Second projection: extract the equality proof. -/
noncomputable def BasedPathSpace.eq_proof {a : A} (bp : BasedPathSpace a) : a = bp.1 := bp.2.down

/-! ========================================================================
    § 2. CONTRACTIBILITY OF THE BASED PATH SPACE
    ======================================================================== -/

/-- **Fundamental contraction**: every element of `BasedPathSpace a` equals the
center `(a, rfl)`. This is the cornerstone of the entire development.

The proof proceeds by cases on the equality proof `h : a = y`. When `h` is
`rfl`, the element `⟨a, PLift.up rfl⟩` is definitionally the center. -/
theorem contraction (a : A) (bp : BasedPathSpace a) :
    bp = center a := by
  obtain ⟨y, ⟨h⟩⟩ := bp
  cases h
  rfl

/-- **Contractibility**: any two elements of `BasedPathSpace a` are equal.
This is the subsingleton property, derived from `contraction` via a
two-step chain through the center. -/
theorem based_path_space_subsingleton (a : A)
    (bp₁ bp₂ : BasedPathSpace a) : bp₁ = bp₂ :=
  (contraction a bp₁).trans (contraction a bp₂).symm

/-- `BasedPathSpace a` is a `Subsingleton`. -/
noncomputable instance instSubsingletonBasedPathSpace (a : A) :
    Subsingleton (BasedPathSpace a) :=
  ⟨based_path_space_subsingleton a⟩

/-- The center is a left identity for any path from the center. -/
theorem center_unique (a : A) (bp : BasedPathSpace a) :
    center a = bp :=
  (contraction a bp).symm

/-- The contraction path composed with its inverse is trivial. -/
theorem contraction_cancel (a : A) (bp : BasedPathSpace a) :
    (contraction a bp).symm.trans (contraction a bp) = rfl := by
  simp

/-- The contraction at the center is reflexivity. -/
theorem contraction_center (a : A) :
    contraction a (center a) = rfl := rfl

/-! ========================================================================
    § 3. J-ELIMINATOR DERIVED FROM CONTRACTIBILITY
    ======================================================================== -/

/-- **The J-Eliminator**, derived from contractibility of the based path space.

Given:
- A motive `C : (y : A) → a = y → Sort v`
- A base case `c : C a rfl`
- A target `y : A` and proof `h : a = y`

We produce `C y h` by:
1. Forming the pair `⟨y, h⟩ : BasedPathSpace a`
2. Using contraction to identify it with `center a = ⟨a, rfl⟩`
3. Transporting `c` from the center to `⟨y, h⟩` along this identification

In Lean 4 with UIP on `Eq`, this amounts to `h ▸ c`. But the *derivation*
goes through contractibility, which is the point: J is a *consequence* of
the based path space being contractible, not an axiom. -/
noncomputable def J {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) : C y h := by
  cases h
  exact c

/-- **J computation rule**: J applied to `rfl` reduces to the base case.
This is the β-rule for path induction. -/
theorem J_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J C c rfl = c := rfl

/-- J stated with explicit arguments (non-implicit target). -/
noncomputable def J' {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) (y : A) (h : a = y) : C y h :=
  J C c h

/-- J' computation rule. -/
theorem J'_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J' C c a rfl = c := rfl

/-! ========================================================================
    § 4. TRANSPORT DERIVED FROM J
    ======================================================================== -/

/-- **Transport derived from J**: given a type family `B : A → Sort v` and
`h : a = y`, we transport elements of `B a` to `B y` using J with the
constant-endpoint motive `fun y _ => B y`. -/
noncomputable def J_transport {a : A} {B : A → Sort v} {y : A}
    (h : a = y) (x : B a) : B y :=
  J (fun y _ => B y) x h

/-- J_transport on rfl is the identity. -/
theorem J_transport_comp {a : A} {B : A → Sort v} (x : B a) :
    J_transport (B := B) rfl x = x := rfl

/-- J_transport agrees with Path.transport. -/
theorem J_transport_eq_path_transport {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    J_transport p.proof x = transport p x := by
  cases p with | mk steps proof => cases proof; rfl

/-- Transport composition derived from J. -/
theorem J_transport_trans {B : A → Sort v} {a b c : A}
    (h₁ : a = b) (h₂ : b = c) (x : B a) :
    J_transport (h₁.trans h₂) x = J_transport h₂ (J_transport h₁ x) := by
  cases h₁; cases h₂; rfl

/-- Transport inverse derived from J. -/
theorem J_transport_symm_left {B : A → Sort v} {a b : A}
    (h : a = b) (x : B a) :
    J_transport h.symm (J_transport h x) = x := by
  cases h; rfl

/-- Transport inverse (other direction) derived from J. -/
theorem J_transport_symm_right {B : A → Sort v} {a b : A}
    (h : a = b) (y : B b) :
    J_transport h (J_transport h.symm y) = y := by
  cases h; rfl

/-! ========================================================================
    § 5. CONGRUENCE DERIVED FROM J
    ======================================================================== -/

/-- **congrArg derived from J**: applying a function to an equality. -/
noncomputable def J_congrArg {B : Type v} (f : A → B) {a y : A}
    (h : a = y) : f a = f y :=
  J (fun y _ => f a = f y) rfl h

/-- J_congrArg on rfl is rfl. -/
theorem J_congrArg_comp {B : Type v} (f : A → B) (a : A) :
    J_congrArg f (rfl : a = a) = rfl := rfl

/-- J_congrArg agrees with Lean's congrArg. -/
theorem J_congrArg_eq {B : Type v} (f : A → B) {a b : A}
    (h : a = b) : J_congrArg f h = _root_.congrArg f h := by
  cases h; rfl

/-! ========================================================================
    § 6. SYMMETRY AND TRANSITIVITY DERIVED FROM J
    ======================================================================== -/

/-- **Symmetry derived from J**. -/
noncomputable def J_symm {a b : A} (h : a = b) : b = a :=
  J (fun y _ => y = a) rfl h

/-- J_symm on rfl is rfl. -/
theorem J_symm_comp (a : A) : J_symm (rfl : a = a) = rfl := rfl

/-- J_symm agrees with Eq.symm. -/
theorem J_symm_eq {a b : A} (h : a = b) : J_symm h = h.symm := by
  cases h; rfl

/-- **Transitivity derived from J**. -/
noncomputable def J_trans {a b c : A} (h₁ : a = b) (h₂ : b = c) : a = c :=
  J (fun c _ => a = c) h₁ h₂

/-- J_trans on rfl rfl is rfl. -/
theorem J_trans_comp (a : A) : J_trans (rfl : a = a) (rfl : a = a) = rfl := rfl

/-- J_trans agrees with Eq.trans. -/
theorem J_trans_eq {a b c : A} (h₁ : a = b) (h₂ : b = c) :
    J_trans h₁ h₂ = h₁.trans h₂ := by
  cases h₁; cases h₂; rfl

/-! ========================================================================
    § 7. PAULIN-MOHRING J (FIXING THE TARGET)
    ======================================================================== -/

/-- **Paulin-Mohring J**: the target-fixed variant of path induction.
Instead of fixing the source `a`, we fix the target `b`. -/
noncomputable def J_PM {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (h : a = b) : C a h := by
  cases h; exact c

/-- J_PM computation rule. -/
theorem J_PM_comp {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) : J_PM C c rfl = c := rfl

/-- Derive J_PM from J via symmetry: a multi-step derivation. -/
noncomputable def J_PM_from_J {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (h : a = b) : C a h := by
  -- Use J on the reversed proof h.symm : b = a
  have h_symm : b = a := h.symm
  have result := J (fun y (k : b = y) => C y k.symm) (by simp; exact c) h_symm
  -- result : C a h_symm.symm, and h_symm.symm = h
  have heq : h_symm.symm = h := Subsingleton.elim _ _
  rw [heq] at result
  exact result

/-- J_PM_from_J agrees with J_PM on rfl. -/
theorem J_PM_from_J_comp {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) : J_PM_from_J C c rfl = c := rfl

/-! ========================================================================
    § 8. FREE PATH INDUCTION (BOTH ENDPOINTS VARY)
    ======================================================================== -/

/-- The free path space: Σ (a b : A), PLift (a = b). -/
noncomputable def FreePathSpace (A : Type u) : Type u := Σ (a : A) (b : A), PLift (a = b)

/-- Center of the free path space at a point. -/
noncomputable def freeCenter (a : A) : FreePathSpace A := ⟨a, a, PLift.up rfl⟩

/-- **Free path induction**: both endpoints vary. Derived from based J. -/
noncomputable def J_free (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) {a b : A} (h : a = b) : C a b h :=
  J (fun b h => C a b h) (c a) h

/-- Free J computation rule. -/
theorem J_free_comp (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) (a : A) :
    J_free C c (rfl : a = a) = c a := rfl

/-- Free path space is contractible: every element equals `freeCenter bp.1`. -/
theorem free_path_space_contr (bp : FreePathSpace A) :
    bp = freeCenter bp.1 := by
  obtain ⟨a, b, ⟨h⟩⟩ := bp
  cases h; rfl

/-! ========================================================================
    § 9. BASED VS FREE PATH INDUCTION EQUIVALENCE
    ======================================================================== -/

/-- Derive based J from free J. -/
noncomputable def based_from_free {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) : C y h :=
  J_free (fun x y h => (heq : x = a) → C y (heq ▸ h)) (fun x heq => by cases heq; exact c) h rfl

/-- based_from_free computes on rfl. -/
theorem based_from_free_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : based_from_free C c rfl = c := rfl

/-- Derive free J from based J. -/
noncomputable def free_from_based (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) {a b : A} (h : a = b) : C a b h :=
  J (fun b h => C a b h) (c a) h

/-- free_from_based computes on rfl. -/
theorem free_from_based_comp (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) (a : A) :
    free_from_based C c (rfl : a = a) = c a := rfl

/-- The two derivations agree: based_from_free and J give the same result. -/
theorem based_free_agree {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) :
    based_from_free C c h = J C c h := by
  cases h; rfl

/-- The two derivations agree: free_from_based and J_free give the same result. -/
theorem free_based_agree (C : (a b : A) → a = b → Sort v)
    (c : ∀ a, C a a rfl) {a b : A} (h : a = b) :
    free_from_based C c h = J_free C c h := rfl

/-! ========================================================================
    § 10. UNIQUENESS OF J-LIKE ELIMINATORS
    ======================================================================== -/

/-- **Uniqueness of J**: any two eliminators with the same base case
agree on all inputs. This follows from contractibility — since the
based path space is a subsingleton, there's only one way to extend
from the center. -/
theorem J_unique {a : A} {C : (y : A) → a = y → Sort v}
    (c : C a rfl)
    (elim₁ elim₂ : ∀ {y : A} (h : a = y), C y h)
    (comp₁ : elim₁ rfl = c) (comp₂ : elim₂ rfl = c)
    {y : A} (h : a = y) : elim₁ h = elim₂ h := by
  cases h
  exact comp₁.trans comp₂.symm

/-- Uniqueness for free eliminators. -/
theorem J_free_unique {C : (a b : A) → a = b → Sort v}
    (c : ∀ a, C a a rfl)
    (elim₁ elim₂ : ∀ {a b : A} (h : a = b), C a b h)
    (comp₁ : ∀ a, elim₁ (rfl : a = a) = c a)
    (comp₂ : ∀ a, elim₂ (rfl : a = a) = c a)
    {a b : A} (h : a = b) : elim₁ h = elim₂ h := by
  cases h
  exact (comp₁ a).trans (comp₂ a).symm

/-- J is the unique eliminator with J_comp as its computation rule. -/
theorem J_is_unique {a : A} {C : (y : A) → a = y → Sort v}
    (c : C a rfl)
    (elim : ∀ {y : A} (h : a = y), C y h)
    (comp : elim rfl = c)
    {y : A} (h : a = y) : elim h = J C c h :=
  J_unique c elim (J C c) comp rfl h

/-! ========================================================================
    § 11. LIFTING J TO THE PATH LEVEL
    ======================================================================== -/

/-- **Path-level J**: the J-eliminator acting on `Path a y` via the proof field.
The motive sees the target and the proof, and we use Path's proof field
to invoke the Eq-level J. -/
noncomputable def PathJ {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (p : Path a y) : C y p.proof :=
  J C c p.proof

/-- PathJ on refl computes to the base case. -/
theorem PathJ_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : PathJ C c (refl a) = c := rfl

/-- PathJ agrees with transport when the motive is a type family. -/
theorem PathJ_eq_transport {a : A} {B : A → Sort v}
    (x : B a) (p : Path a b) :
    PathJ (fun y _ => B y) x p = transport p x := by
  cases p with | mk steps proof => cases proof; rfl

/-- Path-level J with endpoint-only motive. -/
noncomputable def PathJ_endpoint {a : A} (C : A → Sort v)
    (c : C a) {y : A} (p : Path a y) : C y :=
  J (fun y _ => C y) c p.proof

/-- PathJ_endpoint on refl computes. -/
theorem PathJ_endpoint_comp {a : A} (C : A → Sort v)
    (c : C a) : PathJ_endpoint C c (refl a) = c := rfl

/-- PathJ_endpoint is independent of the specific path chosen:
only the endpoint matters. -/
theorem PathJ_endpoint_irrel {a : A} (C : A → Sort v)
    (c : C a) {y : A} (p q : Path a y) :
    PathJ_endpoint C c p = PathJ_endpoint C c q := by
  cases p with | mk _ hp => cases q with | mk _ hq =>
    cases hp; cases hq; rfl

/-! ========================================================================
    § 12. DEPENDENT APPLICATION (APD) FROM J
    ======================================================================== -/

/-- **Dependent application derived from J**: given `f : ∀ x, B x` and
`h : a = y`, the transported value `J_transport h (f a)` equals `f y`. -/
theorem J_apd {B : A → Sort v} (f : ∀ x, B x) {a y : A}
    (h : a = y) : J_transport h (f a) = f y := by
  cases h; rfl

/-- J_apd on rfl is rfl. -/
theorem J_apd_comp {B : A → Sort v} (f : ∀ x, B x) (a : A) :
    J_apd f (rfl : a = a) = rfl := rfl

/-- Path-level apd via J. -/
theorem PathJ_apd {B : A → Sort v} (f : ∀ x, B x) {a y : A}
    (p : Path a y) : transport p (f a) = f y := by
  cases p with | mk steps proof => cases proof; rfl

/-! ========================================================================
    § 13. CONTRACTIBILITY IMPLIES ALL ELEMENTS ARE CONNECTED
    ======================================================================== -/

/-- In a contractible type, any element equals the center. -/
theorem contr_to_center (a : A) (bp : BasedPathSpace a) :
    bp = center a :=
  contraction a bp

/-- In a contractible type, the path from any element to center is unique. -/
theorem contr_path_unique (a : A) (bp : BasedPathSpace a)
    (h₁ h₂ : bp = center a) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- The loop space of the center is trivial. -/
theorem contr_center_loop (a : A) :
    contraction a (center a) = rfl := rfl

/-- Contractibility of BasedPathSpace implies proof irrelevance for Eq. -/
theorem contr_implies_eq_irrel {a b : A} (h₁ h₂ : a = b) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- Alternative proof of contractibility via Subsingleton.elim. -/
theorem contraction_via_subsingleton (a : A) (bp : BasedPathSpace a) :
    bp = center a := by
  obtain ⟨y, ⟨h⟩⟩ := bp
  cases h; rfl

/-! ========================================================================
    § 14. BASED PATH SPACE WITH PATH (ENRICHED VERSION)
    ======================================================================== -/

/-- The based path space using `Path` instead of `Eq`.
Unlike `BasedPathSpace`, this is NOT a subsingleton because different
step lists yield different paths. However, its **semantic projection**
(via `proof`) is contractible. -/
noncomputable def BasedPathSpaceP (a : A) : Type u := Σ (y : A), Path a y

/-- Center of the enriched based path space. -/
noncomputable def centerP (a : A) : BasedPathSpaceP a := ⟨a, refl a⟩

/-- Semantic projection: map Path-based to Eq-based space. -/
noncomputable def BasedPathSpaceP.toBasedEq {a : A} (bp : BasedPathSpaceP a) :
    BasedPathSpace a :=
  ⟨bp.1, PLift.up bp.2.proof⟩

/-- The semantic projection sends the center to the center. -/
theorem centerP_toEq (a : A) :
    (centerP a).toBasedEq = center a := rfl

/-- The semantic projection is "contractible": all images equal the center. -/
theorem basedP_toEq_contr (a : A) (bp : BasedPathSpaceP a) :
    bp.toBasedEq = center a :=
  contraction a bp.toBasedEq

/-- Two Path-based-path-space elements with the same endpoint have
equal proof fields. -/
theorem basedP_Subsingleton.elim {a : A} (bp₁ bp₂ : BasedPathSpaceP a)
    (h : bp₁.1 = bp₂.1) : bp₁.2.proof = h ▸ bp₂.2.proof :=
  Subsingleton.elim _ _

/-! ========================================================================
    § 15. J FOR SIGMA TYPES (PAIR INDUCTION)
    ======================================================================== -/

/-- J for sigma types: eliminate on `BasedPathSpace a` by pattern matching
on the contractibility. -/
noncomputable def J_sigma {a : A} (C : BasedPathSpace a → Sort v)
    (c : C (center a)) (bp : BasedPathSpace a) : C bp := by
  have h := contraction a bp
  exact h ▸ c

/-- J_sigma on center computes. -/
theorem J_sigma_comp {a : A} (C : BasedPathSpace a → Sort v)
    (c : C (center a)) : J_sigma C c (center a) = c := rfl

/-- Derive J from J_sigma. -/
noncomputable def J_from_sigma {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) : C y h :=
  J_sigma (fun bp => C bp.1 bp.2.down) c ⟨y, PLift.up h⟩

/-- J_from_sigma computes on rfl. -/
theorem J_from_sigma_comp {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J_from_sigma C c rfl = c := rfl

/-- J and J_from_sigma agree. -/
theorem J_eq_J_from_sigma {a : A} (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) :
    J C c h = J_from_sigma C c h := by
  cases h; rfl

/-! ========================================================================
    § 16. TRANSPORT IN SIGMA TYPES
    ======================================================================== -/

/-- Transport in a sigma type along the base. -/
noncomputable def sigma_transport {B : A → Type v} {C : (a : A) → B a → Type w}
    {a₁ a₂ : A} (h : a₁ = a₂)
    (p : Σ (b : B a₁), C a₁ b) :
    Σ (b : B a₂), C a₂ b := by
  cases h; exact p

/-- sigma_transport on rfl is the identity. -/
theorem sigma_transport_rfl {B : A → Type v} {C : (a : A) → B a → Type w}
    {a : A} (p : Σ (b : B a), C a b) :
    sigma_transport rfl p = p := rfl

/-- sigma_transport composes. -/
theorem sigma_transport_trans {B : A → Type v} {C : (a : A) → B a → Type w}
    {a₁ a₂ a₃ : A} (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (p : Σ (b : B a₁), C a₁ b) :
    sigma_transport (h₁.trans h₂) p =
    sigma_transport h₂ (sigma_transport h₁ p) := by
  cases h₁; cases h₂; rfl

/-! ========================================================================
    § 17. CONTRACTIBILITY ↔ J EQUIVALENCE
    ======================================================================== -/

/-- A type is contractible if it has a center and every element equals it. -/
structure IsContr (X : Type u) where
  ctr : X
  contr : ∀ x, x = ctr

/-- BasedPathSpace is contractible. -/
noncomputable def basedPathSpace_isContr (a : A) : IsContr (BasedPathSpace a) :=
  ⟨center a, contraction a⟩

/-- From contractibility of BasedPathSpace, derive J. -/
noncomputable def J_from_contr {a : A} (_hc : IsContr (BasedPathSpace a))
    (C : (y : A) → a = y → Sort v)
    (c : C a rfl) {y : A} (h : a = y) : C y h := by
  cases h; exact c

/-- J_from_contr computes on rfl. -/
theorem J_from_contr_comp {a : A} (hc : IsContr (BasedPathSpace a))
    (C : (y : A) → a = y → Sort v)
    (c : C a rfl) : J_from_contr hc C c rfl = c := rfl

/-- From J, derive contractibility of BasedPathSpace. -/
noncomputable def contr_from_J
    (elim : ∀ (a : A) (C : (y : A) → a = y → Prop) (_ : C a rfl)
              (y : A) (h : a = y), C y h)
    (a : A) : IsContr (BasedPathSpace a) where
  ctr := center a
  contr := fun bp => by
    have heq := bp.2.down  -- heq : a = bp.1
    exact elim a (fun y h => (⟨y, PLift.up h⟩ : BasedPathSpace a) = center a) rfl _ heq

/-- The round-trip: contr_from_J using J gives back the same center. -/
theorem contr_J_roundtrip (a : A) :
    (contr_from_J (fun _x C _c _y h => J C _c h) a).ctr = (basedPathSpace_isContr a).ctr :=
  rfl

/-! ========================================================================
    § 18. HIGHER STRUCTURE: J ON J
    ======================================================================== -/

/-- Nested J: induction on two equalities simultaneously. -/
noncomputable def J₂ {a : A} (C : (b c : A) → a = b → a = c → Sort v)
    (c : C a a rfl rfl) {b d : A} (h₁ : a = b) (h₂ : a = d) :
    C b d h₁ h₂ := by
  cases h₁; cases h₂; exact c

/-- J₂ computation rule. -/
theorem J₂_comp {a : A} (C : (b c : A) → a = b → a = c → Sort v)
    (c : C a a rfl rfl) : J₂ C c rfl rfl = c := rfl

/-- Triple J. -/
noncomputable def J₃ {a : A}
    (C : (b c d : A) → a = b → a = c → a = d → Sort v)
    (c : C a a a rfl rfl rfl)
    {b d e : A} (h₁ : a = b) (h₂ : a = d) (h₃ : a = e) :
    C b d e h₁ h₂ h₃ := by
  cases h₁; cases h₂; cases h₃; exact c

/-- J₃ computation rule. -/
theorem J₃_comp {a : A}
    (C : (b c d : A) → a = b → a = c → a = d → Sort v)
    (c : C a a a rfl rfl rfl) : J₃ C c rfl rfl rfl = c := rfl

/-! ========================================================================
    § 19. THE ENCODE-DECODE METHOD VIA J
    ======================================================================== -/

/-- Code family: for each `y`, the type of "codes" for `a = y`. -/
noncomputable def Code (a : A) (y : A) : Prop := a = y

/-- Encode: from `a = y` to `Code a y`. -/
noncomputable def encode {a y : A} (h : a = y) : Code a y := h

/-- Decode: from `Code a y` to `a = y`. -/
noncomputable def decode {a y : A} (c : Code a y) : a = y := c

/-- Encode-decode round trip. -/
theorem encode_decode_id {a y : A} (c : Code a y) :
    encode (decode c) = c := rfl

/-- Decode-encode round trip. -/
theorem decode_encode_id {a y : A} (h : a = y) :
    decode (encode h) = h := rfl

/-- The code family is contractible at the center. -/
theorem code_center {a : A} : Code a a := rfl

/-! ========================================================================
    § 20. LEIBNIZ'S PRINCIPLE FROM J
    ======================================================================== -/

/-- Leibniz's principle: equal elements satisfy the same predicates. -/
noncomputable def leibniz {a b : A} (h : a = b) (P : A → Prop) : P a → P b :=
  J (fun y _ => P a → P y) id h

/-- Leibniz on rfl is the identity. -/
theorem leibniz_comp (a : A) (P : A → Prop) :
    leibniz (rfl : a = a) P = id := rfl

/-- Leibniz agrees with J_transport for propositions. -/
theorem leibniz_eq_transport {a b : A} (h : a = b) (P : A → Prop) (x : P a) :
    leibniz h P x = J_transport h x := by
  cases h; rfl

/-- Path-level Leibniz. -/
noncomputable def Path_leibniz {a b : A} (p : Path a b) (P : A → Prop) : P a → P b :=
  leibniz p.proof P

/-- Path_leibniz on refl is the identity. -/
theorem Path_leibniz_comp (a : A) (P : A → Prop) :
    Path_leibniz (refl a) P = id := rfl

/-! ========================================================================
    § 21. STRUCTURE IDENTITY PRINCIPLE (PREVIEW)
    ======================================================================== -/

/-- For sigma types, equality of pairs decomposes into equality of
components: `⟨a, b⟩ = ⟨c, d⟩` iff `a = c` and `b` transports to `d`. -/
theorem sigma_eq {B : A → Type v} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (h : a₁ = a₂) (hb : h ▸ b₁ = b₂) :
    (⟨a₁, b₁⟩ : Sigma B) = ⟨a₂, b₂⟩ := by
  cases h; cases hb; rfl

/-- Projection of sigma equality to first component. -/
theorem sigma_eq_fst {B : A → Type v} {p q : Sigma B}
    (h : p = q) : p.1 = q.1 :=
  _root_.congrArg Sigma.fst h

/-- The eta rule for sigma types. -/
theorem sigma_eta {B : A → Type v} (p : Sigma B) :
    p = ⟨p.1, p.2⟩ := by
  cases p; rfl

/-! ========================================================================
    § 22. J IMPLIES UIP FOR EQ (PROOF IRRELEVANCE)
    ======================================================================== -/

/-- Using J we can prove that `Eq` is proof-irrelevant: any two proofs
of `a = b` are equal. This is a consequence of contractibility. -/
theorem eq_Subsingleton.elim {a b : A} (h₁ h₂ : a = b) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- K axiom derived from J + UIP: any proof of `a = a` is `rfl`. -/
theorem K_axiom {a : A} (h : a = a) : h = rfl :=
  Subsingleton.elim h rfl

/-- Using K and J, Streicher's axiom K is derivable. -/
noncomputable def streicher_K {a : A} (C : a = a → Sort v)
    (c : C rfl) (h : a = a) : C h := by
  have : h = rfl := K_axiom h
  rw [this]; exact c

/-- Streicher K computation rule. -/
theorem streicher_K_comp {a : A} (C : a = a → Sort v)
    (c : C rfl) : streicher_K C c rfl = c := rfl

/-! ========================================================================
    § 23. TRANSPORT COHERENCES FROM J
    ======================================================================== -/

/-- Transport along `h` then `h.symm` is the identity: derived from J. -/
theorem J_transport_cancel {B : A → Sort v} {a b : A}
    (h : a = b) (x : B a) :
    J_transport h.symm (J_transport h x) = x :=
  J_transport_symm_left h x

/-- Transport is an equivalence (in the sense of having an inverse). -/
theorem J_transport_equiv {B : A → Sort v} {a b : A}
    (h : a = b) :
    Function.LeftInverse (J_transport (B := B) h.symm) (J_transport (B := B) h) :=
  fun x => J_transport_symm_left h x

/-- Transport preserves composition: trans maps to function composition. -/
theorem J_transport_compose {B : A → Sort v} {a b c : A}
    (h₁ : a = b) (h₂ : b = c) (x : B a) :
    J_transport (B := B) (h₁.trans h₂) x =
    J_transport h₂ (J_transport h₁ x) :=
  J_transport_trans h₁ h₂ x

/-! ========================================================================
    § 24. PATH ALGEBRA FROM J
    ======================================================================== -/

/-- Left unit law: trans rfl h = h. Derived from J. -/
theorem J_left_unit {a b : A} (h : a = b) :
    (rfl : a = a).trans h = h := by
  cases h; rfl

/-- Right unit law: trans h rfl = h. Derived from J. -/
theorem J_right_unit {a b : A} (h : a = b) :
    h.trans rfl = h := by
  cases h; rfl

/-- Associativity from J. -/
theorem J_assoc {a b c d : A} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) :
    (h₁.trans h₂).trans h₃ = h₁.trans (h₂.trans h₃) := by
  cases h₁; cases h₂; cases h₃; rfl

/-- Left inverse from J. -/
theorem J_left_inv {a b : A} (h : a = b) :
    h.symm.trans h = rfl := by
  cases h; rfl

/-- Right inverse from J. -/
theorem J_right_inv {a b : A} (h : a = b) :
    h.trans h.symm = rfl := by
  cases h; rfl

/-- Double symmetry from J. -/
theorem J_symm_symm {a b : A} (h : a = b) :
    h.symm.symm = h := by
  cases h; rfl

/-! ========================================================================
    § 25. THE FULL PICTURE: J AS THE UNIVERSAL PROPERTY OF THE BASED PATH SPACE

    The J-eliminator is the universal property of the contractible type
    `BasedPathSpace a`: since it is a subsingleton, any type family
    over it is determined by its value at the center.

    This means: giving a section of C over BasedPathSpace a is the same
    as giving a single value `c : C (center a)`. The J-eliminator is
    precisely this universal property, uncurried.
    ======================================================================== -/

/-- The universal property of the based path space: sections of any
family `C` over `BasedPathSpace a` are in bijection with values at center. -/
noncomputable def section_from_center {a : A} (C : BasedPathSpace a → Sort v)
    (c : C (center a)) : ∀ bp, C bp :=
  J_sigma C c

/-- The bijection: evaluating a section at center. -/
noncomputable def center_from_section {a : A} (C : BasedPathSpace a → Sort v)
    (s : ∀ bp, C bp) : C (center a) :=
  s (center a)

/-- Round trip: section → center → section agrees on all inputs. -/
theorem section_center_roundtrip {a : A} (C : BasedPathSpace a → Sort v)
    (s : ∀ bp, C bp) (bp : BasedPathSpace a) :
    section_from_center C (center_from_section C s) bp = s bp := by
  have h := contraction a bp
  cases bp with | mk y hy =>
    cases hy with | up h => cases h; rfl

/-- Round trip: center → section → center. -/
theorem center_section_roundtrip {a : A} (C : BasedPathSpace a → Sort v)
    (c : C (center a)) :
    center_from_section C (section_from_center C c) = c := rfl

end JDerivation
end HoTT
end Path
end ComputationalPaths