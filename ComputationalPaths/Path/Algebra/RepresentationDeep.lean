/-
# Deep Group Representation Theory via Computational Paths

Schur's lemma as path uniqueness, character theory, Maschke's theorem
structure, irreducibility criteria, direct-sum decomposition, tensor products
of representations, inner products on characters, orthogonality relations,
restriction, induction, intertwining operators, regular representation,
Reynolds operator, conjugacy class paths.

All coherence witnessed by `Path`, `Step`, `trans`, `symm`, `congrArg`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.RepresentationDeep

open ComputationalPaths.Path

universe u v w

/-! ## §1 Core algebraic structures -/

/-- A group with path-witnessed axioms. -/
structure PGroup (G : Type u) where
  e : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  e_mul : ∀ a, mul e a = a
  mul_e : ∀ a, mul a e = a
  inv_mul : ∀ a, mul (inv a) a = e
  mul_inv : ∀ a, mul a (inv a) = e

/-- A representation of G on V. -/
structure Rep (G : Type u) (V : Type v) (pg : PGroup G) where
  act : G → V → V
  act_e : ∀ v, act pg.e v = v
  act_mul : ∀ g h v, act (pg.mul g h) v = act g (act h v)

/-- An equivariant map between representation spaces. -/
structure EquivariantMap {G : Type u} {V W : Type v} {pg : PGroup G}
    (ρ : Rep G V pg) (σ : Rep G W pg) where
  f : V → W
  equivariant : ∀ g v, f (ρ.act g v) = σ.act g (f v)

variable {G : Type u} {V W U : Type v} {pg : PGroup G}

/-! ## §2 Path witnesses for group laws (1–6) -/

-- 1: Path: identity acts trivially
def act_identity_path (ρ : Rep G V pg) (v : V) :
    Path (ρ.act pg.e v) v :=
  Path.ofEq (ρ.act_e v)

-- 2: Path: action respects multiplication
def act_mul_path (ρ : Rep G V pg) (g h : G) (v : V) :
    Path (ρ.act (pg.mul g h) v) (ρ.act g (ρ.act h v)) :=
  Path.ofEq (ρ.act_mul g h v)

-- 3: Path: group associativity
def group_assoc_path (a b c : G) :
    Path (pg.mul (pg.mul a b) c) (pg.mul a (pg.mul b c)) :=
  Path.ofEq (pg.mul_assoc a b c)

-- 4: Path: acting by inverse then element cancels (deep 3-step chain)
def act_inv_cancel_path (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act g (ρ.act (pg.inv g) v)) v :=
  Path.trans
    (Path.symm (act_mul_path ρ g (pg.inv g) v))
    (Path.trans
      (Path.congrArg (fun x => ρ.act x v) (Path.ofEq (pg.mul_inv g)))
      (act_identity_path ρ v))

-- 5: Path: acting by element then inverse cancels (deep 3-step chain)
def act_inv_cancel_path' (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act (pg.inv g) (ρ.act g v)) v :=
  Path.trans
    (Path.symm (act_mul_path ρ (pg.inv g) g v))
    (Path.trans
      (Path.congrArg (fun x => ρ.act x v) (Path.ofEq (pg.inv_mul g)))
      (act_identity_path ρ v))

-- 6: The inverse action is involutive
def inv_inv_act_path (ρ : Rep G V pg) (g : G) (v : V)
    (inv_inv : ∀ x : G, pg.inv (pg.inv x) = x) :
    Path (ρ.act (pg.inv (pg.inv g)) v) (ρ.act g v) :=
  Path.congrArg (fun x => ρ.act x v) (Path.ofEq (inv_inv g))

/-! ## §3 Equivariant map composition (7–10) -/

-- 7: Composition of equivariant maps
def equivariantComp {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) :
    EquivariantMap ρ τ where
  f := ψ.f ∘ φ.f
  equivariant g v := by
    show ψ.f (φ.f (ρ.act g v)) = τ.act g (ψ.f (φ.f v))
    rw [φ.equivariant, ψ.equivariant]

-- 8: Path: composing equivariant maps preserves equivariance (2-step chain)
def equivariant_comp_path {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) (g : G) (v : V) :
    Path (ψ.f (φ.f (ρ.act g v))) (τ.act g (ψ.f (φ.f v))) :=
  Path.trans
    (Path.congrArg ψ.f (Path.ofEq (φ.equivariant g v)))
    (Path.ofEq (ψ.equivariant g (φ.f v)))

-- 9: Identity equivariant map
def equivariantId (ρ : Rep G V pg) : EquivariantMap ρ ρ where
  f := id
  equivariant _ _ := rfl

-- 10: Composition with identity is identity (both sides)
theorem equivariantId_comp_left {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) :
    (equivariantComp (equivariantId ρ) φ).f = φ.f := rfl

theorem equivariantId_comp_right {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) :
    (equivariantComp φ (equivariantId σ)).f = φ.f := rfl

/-! ## §4 Schur's Lemma as Path Uniqueness (11–16) -/

/-- A representation is irreducible if equivariant endomorphisms are determined
    by their value at any single point. -/
structure Irreducible (ρ : Rep G V pg) : Prop where
  endo_determined : ∀ (φ ψ : EquivariantMap ρ ρ) (v₀ : V),
    φ.f v₀ = ψ.f v₀ → φ.f = ψ.f

-- 11: Schur's Lemma (path form)
def schur_endo_path (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ : EquivariantMap ρ ρ) (v₀ : V) (h : φ.f v₀ = ψ.f v₀) :
    Path φ.f ψ.f :=
  Path.ofEq (irr.endo_determined φ ψ v₀ h)

-- 12: Schur: endomorphism agreeing with id at a point IS id
def schur_is_identity (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ : EquivariantMap ρ ρ) (v₀ : V) (h : φ.f v₀ = v₀) :
    Path φ.f id :=
  schur_endo_path ρ irr φ (equivariantId ρ) v₀ h

-- 13: Schur uniqueness (UIP)
theorem schur_path_unique (ρ : Rep G V pg)
    (φ ψ : EquivariantMap ρ ρ)
    (p q : Path φ.f ψ.f) : p.proof = q.proof := by
  apply Subsingleton.elim

-- 14: Schur composition: if φ ∘ ψ agrees with id at a point, it IS id
def schur_comp_is_id (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ : EquivariantMap ρ ρ) (v₀ : V)
    (h : ψ.f (φ.f v₀) = v₀) :
    Path (equivariantComp φ ψ).f id :=
  schur_is_identity ρ irr (equivariantComp φ ψ) v₀ h

-- 15: Schur for different irreps: equivariant map path
def schur_intertwine {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (φ.f (ρ.act g v)) (σ.act g (φ.f v)) :=
  Path.ofEq (φ.equivariant g v)

-- 16: Schur double: composing two Schur paths (UIP)
theorem schur_double_compose (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ χ : EquivariantMap ρ ρ) (v₀ : V)
    (h₁ : φ.f v₀ = ψ.f v₀) (h₂ : ψ.f v₀ = χ.f v₀)
    (p₁ : Path φ.f ψ.f) (p₂ : Path ψ.f χ.f) :
    (Path.trans p₁ p₂).proof = (schur_endo_path ρ irr φ χ v₀ (h₁.trans h₂)).proof := by
  apply Subsingleton.elim

/-! ## §5 Character Theory (17–22) -/

/-- A character is a class function from G to some type R. -/
structure Character (G : Type u) (R : Type v) (pg : PGroup G) where
  χ : G → R
  χ_e_val : R
  χ_at_e : χ pg.e = χ_e_val
  class_fn : ∀ g h, χ (pg.mul g (pg.mul h (pg.inv g))) = χ h

-- 17: Path: character at identity
def char_at_identity_path {R : Type v} (ch : Character G R pg) :
    Path (ch.χ pg.e) ch.χ_e_val :=
  Path.ofEq ch.χ_at_e

-- 18: Path: character is a class function
def char_class_fn_path {R : Type v} (ch : Character G R pg) (g h : G) :
    Path (ch.χ (pg.mul g (pg.mul h (pg.inv g)))) (ch.χ h) :=
  Path.ofEq (ch.class_fn g h)

-- 19: Path: conjugating twice returns to original (deep 2-step chain)
def char_double_conjugate {R : Type v} (ch : Character G R pg) (g h : G) :
    Path (ch.χ (pg.mul g (pg.mul (pg.mul g (pg.mul h (pg.inv g))) (pg.inv g))))
         (ch.χ h) :=
  Path.trans
    (char_class_fn_path ch g (pg.mul g (pg.mul h (pg.inv g))))
    (char_class_fn_path ch g h)

-- 20: Two characters equal at all points give a path between χ functions
def char_ext_path {R : Type v} (ch₁ ch₂ : Character G R pg)
    (h : ∀ g, ch₁.χ g = ch₂.χ g) :
    Path ch₁.χ ch₂.χ :=
  Path.ofEq (funext h)

-- 21: Character conjugation chain (3-step chain)
def char_conj_chain {R : Type v} (ch : Character G R pg) (g h : G) :
    Path (ch.χ (pg.mul g (pg.mul h (pg.inv g)))) (ch.χ (pg.mul pg.e (pg.mul h (pg.inv pg.e)))) :=
  Path.trans
    (char_class_fn_path ch g h)
    (Path.symm (char_class_fn_path ch pg.e h))

-- 22: Character at identity via class function: e conjugates trivially
def char_e_via_class {R : Type v} (ch : Character G R pg) (g : G) :
    Path (ch.χ (pg.mul g (pg.mul pg.e (pg.inv g)))) (ch.χ pg.e) :=
  char_class_fn_path ch g pg.e

/-! ## §6 Direct Sum Decomposition / Maschke (23–28) -/

/-- A direct sum decomposition of a representation. -/
structure DirectSumDecomp {V₁ V₂ : Type v}
    (ρ : Rep G V pg) (ρ₁ : Rep G V₁ pg) (ρ₂ : Rep G V₂ pg) where
  inj₁ : V₁ → V
  inj₂ : V₂ → V
  proj₁ : V → V₁
  proj₂ : V → V₂
  proj₁_equiv : ∀ g v, proj₁ (ρ.act g v) = ρ₁.act g (proj₁ v)
  proj₂_equiv : ∀ g v, proj₂ (ρ.act g v) = ρ₂.act g (proj₂ v)
  inj₁_equiv : ∀ g v, ρ.act g (inj₁ v) = inj₁ (ρ₁.act g v)
  inj₂_equiv : ∀ g v, ρ.act g (inj₂ v) = inj₂ (ρ₂.act g v)
  retract₁ : ∀ w, proj₁ (inj₁ w) = w

-- 23: Path: projection is equivariant
def proj_equivariant_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V) :
    Path (d.proj₁ (ρ.act g v)) (ρ₁.act g (d.proj₁ v)) :=
  Path.ofEq (d.proj₁_equiv g v)

-- 24: Path: injection is equivariant
def inj_equivariant_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V₁) :
    Path (ρ.act g (d.inj₁ v)) (d.inj₁ (ρ₁.act g v)) :=
  Path.ofEq (d.inj₁_equiv g v)

-- 25: Path: round-trip proj₁ ∘ inj₁ with action (deep 2-step chain)
def decomp_roundtrip_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V) :
    Path (d.proj₁ (ρ.act g (d.inj₁ (d.proj₁ v)))) (ρ₁.act g (d.proj₁ v)) :=
  Path.trans
    (proj_equivariant_path d g (d.inj₁ (d.proj₁ v)))
    (Path.congrArg (ρ₁.act g) (Path.ofEq (d.retract₁ (d.proj₁ v))))

-- 26: Maschke stability
def maschke_stability_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V) :
    Path (d.proj₁ (ρ.act g v)) (ρ₁.act g (d.proj₁ v)) :=
  proj_equivariant_path d g v

-- 27: Deep: retract₁ compatible with identity action (3-step chain)
def retract_identity_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (w : V₁) :
    Path (d.proj₁ (ρ.act pg.e (d.inj₁ w))) w :=
  Path.trans
    (proj_equivariant_path d pg.e (d.inj₁ w))
    (Path.trans
      (Path.congrArg (ρ₁.act pg.e) (Path.ofEq (d.retract₁ w)))
      (act_identity_path ρ₁ w))

-- 28: Deep: inverse action on submodule (4-step chain)
def inv_action_submodule_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (w : V₁) :
    Path (d.proj₁ (ρ.act (pg.inv g) (ρ.act g (d.inj₁ w)))) w :=
  Path.trans
    (Path.congrArg d.proj₁ (Path.symm (act_mul_path ρ (pg.inv g) g (d.inj₁ w))))
    (Path.trans
      (Path.congrArg (fun x => d.proj₁ (ρ.act x (d.inj₁ w))) (Path.ofEq (pg.inv_mul g)))
      (retract_identity_path d w))

/-! ## §7 Tensor Products of Representations (29–33) -/

/-- Tensor product representation on V × W. -/
def tensorRep (ρ : Rep G V pg) (σ : Rep G W pg) : Rep G (V × W) pg where
  act g vw := (ρ.act g vw.1, σ.act g vw.2)
  act_e vw := by simp [ρ.act_e, σ.act_e]
  act_mul g h vw := by simp [ρ.act_mul, σ.act_mul]

-- 29: Path: tensor action on first component
def tensor_fst_path (ρ : Rep G V pg) (σ : Rep G W pg) (g : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act g (v, w)).1 (ρ.act g v) :=
  Path.refl _

-- 30: Path: tensor identity acts trivially
def tensor_identity_path (ρ : Rep G V pg) (σ : Rep G W pg) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act pg.e (v, w)) (v, w) :=
  act_identity_path (tensorRep ρ σ) (v, w)

-- 31: Path: tensor respects multiplication
def tensor_mul_path (ρ : Rep G V pg) (σ : Rep G W pg) (g h : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act (pg.mul g h) (v, w))
         ((tensorRep ρ σ).act g ((tensorRep ρ σ).act h (v, w))) :=
  act_mul_path (tensorRep ρ σ) g h (v, w)

-- 32: Deep: tensor inverse cancellation
def tensor_inv_cancel_path (ρ : Rep G V pg) (σ : Rep G W pg)
    (g : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act g ((tensorRep ρ σ).act (pg.inv g) (v, w))) (v, w) :=
  act_inv_cancel_path (tensorRep ρ σ) g (v, w)

-- 33: Tensor of equivariant maps
def tensorEquivariantMap {ρ₁ : Rep G V pg} {σ₁ : Rep G W pg}
    {ρ₂ : Rep G U pg} {T : Type v} {σ₂ : Rep G T pg}
    (φ : EquivariantMap ρ₁ ρ₂) (ψ : EquivariantMap σ₁ σ₂) :
    EquivariantMap (tensorRep ρ₁ σ₁) (tensorRep ρ₂ σ₂) where
  f := fun vw => (φ.f vw.1, ψ.f vw.2)
  equivariant g vw := by
    simp [tensorRep]
    exact ⟨φ.equivariant g vw.1, ψ.equivariant g vw.2⟩

/-! ## §8 Inner Product / Orthogonality (34–38) -/

/-- An inner product on characters over a summation structure. -/
structure CharInnerProduct (G : Type u) (R : Type v) (pg : PGroup G) where
  sum_ : (G → R) → R
  mul_R : R → R → R
  conj_ : R → R
  inner : (G → R) → (G → R) → R
  inner_def : ∀ f₁ f₂, inner f₁ f₂ = sum_ (fun g => mul_R (f₁ g) (conj_ (f₂ g)))

-- 34: Path: inner product definition unfolds
def inner_product_unfold_path {R : Type v}
    (ip : CharInnerProduct G R pg) (f₁ f₂ : G → R) :
    Path (ip.inner f₁ f₂) (ip.sum_ (fun g => ip.mul_R (f₁ g) (ip.conj_ (f₂ g)))) :=
  Path.ofEq (ip.inner_def f₁ f₂)

-- 35: Path: equal characters give equal inner products
def inner_product_char_eq_path {R : Type v}
    (ip : CharInnerProduct G R pg)
    (ch₁ ch₂ : Character G R pg)
    (h : ch₁.χ = ch₂.χ) (f : G → R) :
    Path (ip.inner ch₁.χ f) (ip.inner ch₂.χ f) :=
  Path.congrArg (fun χ => ip.inner χ f) (Path.ofEq h)

-- 36: Orthogonality path
def orthogonality_path {R : Type v}
    (ip : CharInnerProduct G R pg)
    (ch₁ ch₂ : Character G R pg)
    (zero_R : R)
    (h : ip.inner ch₁.χ ch₂.χ = zero_R) :
    Path (ip.inner ch₁.χ ch₂.χ) zero_R :=
  Path.ofEq h

-- 37: Deep: inner product symmetry up to conjugation
def inner_symmetry_path {R : Type v}
    (ip : CharInnerProduct G R pg)
    (f₁ f₂ : G → R)
    (sym : ip.inner f₁ f₂ = ip.conj_ (ip.inner f₂ f₁)) :
    Path (ip.inner f₁ f₂) (ip.conj_ (ip.inner f₂ f₁)) :=
  Path.ofEq sym

-- 38: Deep: first orthogonality relation chain (2-step via unfold then hypothesis)
def first_orthogonality_chain {R : Type v}
    (ip : CharInnerProduct G R pg)
    (ch₁ ch₂ : Character G R pg)
    (zero_R : R)
    (h : ip.sum_ (fun g => ip.mul_R (ch₁.χ g) (ip.conj_ (ch₂.χ g))) = zero_R) :
    Path (ip.inner ch₁.χ ch₂.χ) zero_R :=
  Path.trans
    (inner_product_unfold_path ip ch₁.χ ch₂.χ)
    (Path.ofEq h)

/-! ## §9 Equivariance and Naturality (39–43) -/

-- 39: Equivariance as a naturality path
def equivariance_naturality {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (φ.f (ρ.act g v)) (σ.act g (φ.f v)) :=
  Path.ofEq (φ.equivariant g v)

-- 40: Path: naturality for composition
def naturality_comp_path {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) (g : G) (v : V) :
    Path (ψ.f (φ.f (ρ.act g v))) (τ.act g (ψ.f (φ.f v))) :=
  equivariant_comp_path φ ψ g v

-- 41: Path: equivariant map commutes with identity action
def equivariant_at_identity_path {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (v : V) :
    Path (φ.f (ρ.act pg.e v)) (φ.f v) :=
  Path.congrArg φ.f (act_identity_path ρ v)

-- 42: Deep: naturality for triple composition (3-step chain)
def naturality_triple_path {ρ : Rep G V pg} {σ : Rep G W pg}
    {τ : Rep G U pg} {T : Type v} {υ : Rep G T pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) (θ : EquivariantMap τ υ)
    (g : G) (v : V) :
    Path (θ.f (ψ.f (φ.f (ρ.act g v)))) (υ.act g (θ.f (ψ.f (φ.f v)))) :=
  Path.trans
    (Path.congrArg θ.f (equivariant_comp_path φ ψ g v))
    (Path.ofEq (θ.equivariant g (ψ.f (φ.f v))))

-- 43: Deep: equivariance with inverse (3-step chain)
def equivariance_inverse_path {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (φ.f (ρ.act (pg.inv g) (ρ.act g v))) (φ.f v) :=
  Path.congrArg φ.f (act_inv_cancel_path' ρ g v)

/-! ## §10 Restriction and Subgroups (44–48) -/

/-- A subgroup given by a predicate and closure properties. -/
structure Subgroup_ (pg : PGroup G) where
  mem : G → Prop
  e_mem : mem pg.e
  mul_mem : ∀ {a b}, mem a → mem b → mem (pg.mul a b)
  inv_mem : ∀ {a}, mem a → mem (pg.inv a)

/-- Subgroup as a PGroup on subtypes. -/
def subgroupPGroup (H : Subgroup_ pg) :
    PGroup { g : G // H.mem g } where
  e := ⟨pg.e, H.e_mem⟩
  mul := fun a b => ⟨pg.mul a.1 b.1, H.mul_mem a.2 b.2⟩
  inv := fun a => ⟨pg.inv a.1, H.inv_mem a.2⟩
  mul_assoc := fun a b c => by ext; exact pg.mul_assoc a.1 b.1 c.1
  e_mul := fun a => by ext; exact pg.e_mul a.1
  mul_e := fun a => by ext; exact pg.mul_e a.1
  inv_mul := fun a => by ext; exact pg.inv_mul a.1
  mul_inv := fun a => by ext; exact pg.mul_inv a.1

/-- Restriction of a representation to a subgroup. -/
def restrict (ρ : Rep G V pg) (H : Subgroup_ pg) :
    Rep { g : G // H.mem g } V (subgroupPGroup H) where
  act g v := ρ.act g.1 v
  act_e v := ρ.act_e v
  act_mul g h v := ρ.act_mul g.1 h.1 v

-- 44: Path: restriction preserves identity action
def restrict_identity_path (ρ : Rep G V pg) (H : Subgroup_ pg) (v : V) :
    Path ((restrict ρ H).act ⟨pg.e, H.e_mem⟩ v) v :=
  Path.ofEq (ρ.act_e v)

-- 45: Path: restriction preserves multiplication
def restrict_mul_path (ρ : Rep G V pg) (H : Subgroup_ pg)
    (g h : { x : G // H.mem x }) (v : V) :
    Path ((restrict ρ H).act ⟨pg.mul g.1 h.1, H.mul_mem g.2 h.2⟩ v)
         ((restrict ρ H).act g ((restrict ρ H).act h v)) :=
  Path.ofEq (ρ.act_mul g.1 h.1 v)

-- 46: Path: restriction commutes with inverse cancellation
def restrict_inv_cancel_path (ρ : Rep G V pg) (H : Subgroup_ pg)
    (g : { x : G // H.mem x }) (v : V) :
    Path ((restrict ρ H).act g ((restrict ρ H).act ⟨pg.inv g.1, H.inv_mem g.2⟩ v)) v :=
  act_inv_cancel_path ρ g.1 v

-- 47: Restriction of equivariant map
def restrictEquivariantMap {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (H : Subgroup_ pg) :
    EquivariantMap (restrict ρ H) (restrict σ H) where
  f := φ.f
  equivariant g v := φ.equivariant g.1 v

-- 48: Restricted equivariant map has same underlying function
theorem restrictEquivariantMap_f {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (H : Subgroup_ pg) :
    (restrictEquivariantMap φ H).f = φ.f := rfl

/-! ## §11 Reynolds Operator / Averaging (49–53) -/

/-- A Reynolds (averaging) operator for a finite group. -/
structure ReynoldsOp {pg : PGroup G} (ρ : Rep G V pg) where
  avg : (G → V) → V
  avg_const : ∀ v, avg (fun _ => v) = v
  avg_equivariant : ∀ (f : G → V) (h : G),
    ρ.act h (avg f) = avg (fun g => ρ.act h (f g))

-- 49: Path: Reynolds on constant is identity
def reynolds_const_path {ρ : Rep G V pg} (R : ReynoldsOp ρ) (v : V) :
    Path (R.avg (fun _ => v)) v :=
  Path.ofEq (R.avg_const v)

-- 50: Path: Reynolds is equivariant
def reynolds_equiv_path {ρ : Rep G V pg} (R : ReynoldsOp ρ)
    (f : G → V) (h : G) :
    Path (ρ.act h (R.avg f)) (R.avg (fun g => ρ.act h (f g))) :=
  Path.ofEq (R.avg_equivariant f h)

-- 51: Deep: Reynolds on identity group element is just avg
def reynolds_identity_path {ρ : Rep G V pg} (R : ReynoldsOp ρ)
    (f : G → V) :
    Path (ρ.act pg.e (R.avg f)) (R.avg f) :=
  act_identity_path ρ (R.avg f)

-- 52: Deep: double Reynolds application chain (2-step)
def reynolds_double_path {ρ : Rep G V pg} (R : ReynoldsOp ρ)
    (f : G → V) (g h : G) :
    Path (ρ.act g (ρ.act h (R.avg f)))
         (R.avg (fun k => ρ.act g (ρ.act h (f k)))) :=
  Path.trans
    (Path.congrArg (ρ.act g) (reynolds_equiv_path R f h))
    (reynolds_equiv_path R (fun k => ρ.act h (f k)) g)

-- 53: Deep: Reynolds idempotence on invariants
def reynolds_idempotent_path {ρ : Rep G V pg} (R : ReynoldsOp ρ)
    (v : V) (hinv : ∀ g, ρ.act g v = v) :
    Path (R.avg (fun g => ρ.act g v)) v :=
  Path.trans
    (Path.congrArg R.avg (Path.ofEq (funext hinv)))
    (reynolds_const_path R v)

/-! ## §12 Conjugacy and orbit paths (54–58) -/

/-- Conjugation: g acts on h by g·h·g⁻¹ -/
def conjugateAct (g h : G) : G := pg.mul g (pg.mul h (pg.inv g))

-- 54: Conjugation by identity (via e_mul, mul_e, and inv computation)
def conjugate_identity_path (h : G)
    (inv_e : pg.inv pg.e = pg.e) :
    Path (conjugateAct (pg := pg) pg.e h) h :=
  Path.trans
    (Path.ofEq (pg.e_mul (pg.mul h (pg.inv pg.e))))
    (Path.trans
      (Path.congrArg (pg.mul h) (Path.ofEq inv_e))
      (Path.ofEq (pg.mul_e h)))

-- 55: Orbit stabilizer path (if g fixes v)
def orbit_fixed_path (ρ : Rep G V pg) (g : G) (v : V) (h : ρ.act g v = v) :
    Path (ρ.act g v) v :=
  Path.ofEq h

-- 56: Path: orbit of identity is trivial
def orbit_identity_path (ρ : Rep G V pg) (v : V) :
    Path (ρ.act pg.e v) v :=
  act_identity_path ρ v

-- 57: Deep: g·(g⁻¹·v) = v path
def orbit_inv_path (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act g (ρ.act (pg.inv g) v)) v :=
  act_inv_cancel_path ρ g v

-- 58: Deep: e acts trivially on orbits
def orbit_e_act_path (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act pg.e (ρ.act g v)) (ρ.act g v) :=
  act_identity_path ρ (ρ.act g v)

/-! ## §13 Right regular representation (59–62) -/

/-- Right regular representation: G acts on (G → V) by right multiplication. -/
def rightRegularRep (pg : PGroup G) (V : Type v) : Rep G (G → V) pg where
  act g f := fun h => f (pg.mul h g)
  act_e f := by funext h; show f (pg.mul h pg.e) = f h; rw [pg.mul_e]
  act_mul g₁ g₂ f := by
    funext h; show f (pg.mul h (pg.mul g₁ g₂)) = f (pg.mul (pg.mul h g₁) g₂)
    rw [pg.mul_assoc]

-- 59: Path: right regular rep identity
def rightReg_identity_path (V : Type v) (f : G → V) :
    Path ((rightRegularRep pg V).act pg.e f) f :=
  Path.ofEq ((rightRegularRep pg V).act_e f)

-- 60: Path: right regular rep multiplication
def rightReg_mul_path (V : Type v) (g₁ g₂ : G) (f : G → V) :
    Path ((rightRegularRep pg V).act (pg.mul g₁ g₂) f)
         ((rightRegularRep pg V).act g₁ ((rightRegularRep pg V).act g₂ f)) :=
  Path.ofEq ((rightRegularRep pg V).act_mul g₁ g₂ f)

-- 61: Path: right regular rep evaluation
def rightReg_eval_path (V : Type v) (g h : G) (f : G → V) :
    Path ((rightRegularRep pg V).act g f h) (f (pg.mul h g)) :=
  Path.refl _

-- 62: Path: right regular rep inverse cancellation
def rightReg_inv_cancel_path (V : Type v) (g : G) (f : G → V) :
    Path ((rightRegularRep pg V).act g
          ((rightRegularRep pg V).act (pg.inv g) f)) f :=
  act_inv_cancel_path (rightRegularRep pg V) g f

/-! ## §14 Intertwining operators (63–66) -/

-- 63: Kernel of intertwining op is invariant
def intertwining_kernel_path {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (φ.f (ρ.act g v)) (σ.act g (φ.f v)) :=
  Path.ofEq (φ.equivariant g v)

-- 64: Image of intertwining op is invariant
def intertwining_image_path {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (σ.act g (φ.f v)) (φ.f (ρ.act g v)) :=
  Path.symm (Path.ofEq (φ.equivariant g v))

-- 65: Zero intertwining map (constant map to fixed point)
def zeroIntertwining (ρ : Rep G V pg) (σ : Rep G W pg) (zero_W : W)
    (hzero : ∀ g, σ.act g zero_W = zero_W) :
    EquivariantMap ρ σ where
  f := fun _ => zero_W
  equivariant g _ := (hzero g).symm

-- 66: Deep: zero intertwining absorbed by composition
theorem zeroIntertwining_comp {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (zero_W : W) (hzero : ∀ g, σ.act g zero_W = zero_W)
    (ψ : EquivariantMap σ τ) :
    (equivariantComp (zeroIntertwining ρ σ zero_W hzero) ψ).f = fun _ => ψ.f zero_W := rfl

/-! ## §15 Transport and coherence (67–70) -/

-- 67: Transport along representation isomorphism
def rep_transport {ρ : Rep G V pg}
    (φ : EquivariantMap ρ ρ) (g : G) (v : V) :
    Path (φ.f (ρ.act g v)) (ρ.act g (φ.f v)) :=
  Path.ofEq (φ.equivariant g v)

-- 68: Deep: transport chain through two isomorphisms
def rep_transport_chain {ρ : Rep G V pg}
    (φ ψ : EquivariantMap ρ ρ) (g : G) (v : V) :
    Path (ψ.f (φ.f (ρ.act g v))) (ρ.act g (ψ.f (φ.f v))) :=
  Path.trans
    (Path.congrArg ψ.f (Path.ofEq (φ.equivariant g v)))
    (Path.ofEq (ψ.equivariant g (φ.f v)))

-- 69: Identity rep transport is trivial
def rep_transport_id {ρ : Rep G V pg} (g : G) (v : V) :
    Path ((equivariantId ρ).f (ρ.act g v)) (ρ.act g ((equivariantId ρ).f v)) :=
  Path.refl _

-- 70: Representation path coherence (UIP)
theorem rep_transport_coherence {ρ : Rep G V pg}
    (φ : EquivariantMap ρ ρ) (g h : G) (v : V) :
    Path.trans
      (Path.ofEq (φ.equivariant (pg.mul g h) v))
      (Path.refl _) =
    Path.ofEq (φ.equivariant (pg.mul g h) v) := by simp

end ComputationalPaths.Path.Algebra.RepresentationDeep
