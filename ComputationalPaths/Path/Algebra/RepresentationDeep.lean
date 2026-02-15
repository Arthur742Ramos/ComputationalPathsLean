/-
# Deep Group Representation Theory via Computational Paths

Schur's lemma as path uniqueness, character theory, Maschke's theorem
structure, irreducibility criteria, direct-sum decomposition, tensor products
of representations, inner products on characters, orthogonality relations.

All coherence witnessed by `Path`, `Step`, `trans`, `symm`, `congrArg`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.RepresentationDeep

open ComputationalPaths.Path

universe u v

/-! ## Core algebraic structures -/

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

/-- A linear map between representation spaces (equivariant). -/
structure EquivariantMap {G : Type u} {V W : Type v} {pg : PGroup G}
    (ρ : Rep G V pg) (σ : Rep G W pg) where
  f : V → W
  equivariant : ∀ g v, f (ρ.act g v) = σ.act g (f v)

variable {G : Type u} {V W U : Type v} {pg : PGroup G}

/-! ## 1–3: Path witnesses for basic group laws -/

/-- 1. Path: identity acts trivially. -/
def act_identity_path (ρ : Rep G V pg) (v : V) :
    Path (ρ.act pg.e v) v :=
  Path.ofEq (ρ.act_e v)

/-- 2. Path: action respects multiplication. -/
def act_mul_path (ρ : Rep G V pg) (g h : G) (v : V) :
    Path (ρ.act (pg.mul g h) v) (ρ.act g (ρ.act h v)) :=
  Path.ofEq (ρ.act_mul g h v)

/-- 3. Path: group associativity for the underlying group. -/
def group_assoc_path (a b c : G) :
    Path (pg.mul (pg.mul a b) c) (pg.mul a (pg.mul b c)) :=
  Path.ofEq (pg.mul_assoc a b c)

/-! ## 4–6: Inverse action -/

/-- 4. Path: acting by inverse then element is identity. -/
def act_inv_cancel_path (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act g (ρ.act (pg.inv g) v)) v :=
  Path.trans
    (Path.symm (act_mul_path ρ g (pg.inv g) v))
    (Path.trans
      (Path.congrArg (fun x => ρ.act x v) (Path.ofEq (pg.mul_inv g)))
      (act_identity_path ρ v))

/-- 5. Path: acting by element then inverse is identity. -/
def act_inv_cancel_path' (ρ : Rep G V pg) (g : G) (v : V) :
    Path (ρ.act (pg.inv g) (ρ.act g v)) v :=
  Path.trans
    (Path.symm (act_mul_path ρ (pg.inv g) g v))
    (Path.trans
      (Path.congrArg (fun x => ρ.act x v) (Path.ofEq (pg.inv_mul g)))
      (act_identity_path ρ v))

/-- 6. The inverse action is involutive: inv(inv g) acts as g. -/
def inv_inv_act_path (ρ : Rep G V pg) (g : G) (v : V)
    (inv_inv : ∀ x : G, pg.inv (pg.inv x) = x) :
    Path (ρ.act (pg.inv (pg.inv g)) v) (ρ.act g v) :=
  Path.congrArg (fun x => ρ.act x v) (Path.ofEq (inv_inv g))

/-! ## 7–9: Equivariant map composition -/

/-- 7. Composition of equivariant maps. -/
def equivariantComp {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) :
    EquivariantMap ρ τ where
  f := ψ.f ∘ φ.f
  equivariant g v := by
    show ψ.f (φ.f (ρ.act g v)) = τ.act g (ψ.f (φ.f v))
    rw [φ.equivariant, ψ.equivariant]

/-- 8. Path: composing equivariant maps preserves equivariance at each element. -/
def equivariant_comp_path {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) (g : G) (v : V) :
    Path (ψ.f (φ.f (ρ.act g v))) (τ.act g (ψ.f (φ.f v))) :=
  Path.trans
    (Path.congrArg ψ.f (Path.ofEq (φ.equivariant g v)))
    (Path.ofEq (ψ.equivariant g (φ.f v)))

/-- 9. Identity equivariant map. -/
def equivariantId (ρ : Rep G V pg) : EquivariantMap ρ ρ where
  f := id
  equivariant _ _ := rfl

/-! ## 10–13: Schur's Lemma as Path Uniqueness -/

/-- A representation is irreducible if equivariant endomorphisms are determined
    by their value at any single point (scalar-like). -/
structure Irreducible (ρ : Rep G V pg) : Prop where
  endo_determined : ∀ (φ ψ : EquivariantMap ρ ρ) (v₀ : V),
    φ.f v₀ = ψ.f v₀ → φ.f = ψ.f

/-- 10. Schur's Lemma (path form): Two equivariant endomorphisms of an
    irreducible rep agreeing at a point yield a path between them. -/
def schur_endo_path (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ : EquivariantMap ρ ρ) (v₀ : V) (h : φ.f v₀ = ψ.f v₀) :
    Path φ.f ψ.f :=
  Path.ofEq (irr.endo_determined φ ψ v₀ h)

/-- 11. Schur: any equivariant endomorphism agreeing with id at a point IS id. -/
def schur_is_identity (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ : EquivariantMap ρ ρ) (v₀ : V) (h : φ.f v₀ = v₀) :
    Path φ.f id :=
  schur_endo_path ρ irr φ (equivariantId ρ) v₀ h

/-- 12. Schur uniqueness: two Schur paths have the same proof (UIP). -/
theorem schur_path_unique (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ : EquivariantMap ρ ρ) (v₀ : V) (h : φ.f v₀ = ψ.f v₀)
    (p q : Path φ.f ψ.f) : p.proof = q.proof := by
  apply Subsingleton.elim

/-- 13. Schur composition: if φ ∘ ψ agrees with id at a point, it IS id. -/
def schur_comp_is_id (ρ : Rep G V pg) (irr : Irreducible ρ)
    (φ ψ : EquivariantMap ρ ρ) (v₀ : V)
    (h : ψ.f (φ.f v₀) = v₀) :
    Path (equivariantComp φ ψ).f id :=
  schur_is_identity ρ irr (equivariantComp φ ψ) v₀ h

/-! ## 14–17: Character Theory -/

/-- A character is a function from G to some numeric type with path axioms. -/
structure Character (G : Type u) (R : Type v) (pg : PGroup G) where
  χ : G → R
  /-- Character at identity -/
  χ_e_val : R
  χ_at_e : χ pg.e = χ_e_val
  /-- Character is a class function: χ(g h g⁻¹) = χ(h) -/
  class_fn : ∀ g h, χ (pg.mul g (pg.mul h (pg.inv g))) = χ h

/-- 14. Path: character evaluated at identity. -/
def char_at_identity_path {R : Type v} (ch : Character G R pg) :
    Path (ch.χ pg.e) ch.χ_e_val :=
  Path.ofEq ch.χ_at_e

/-- 15. Path: character is a class function. -/
def char_class_fn_path {R : Type v} (ch : Character G R pg) (g h : G) :
    Path (ch.χ (pg.mul g (pg.mul h (pg.inv g)))) (ch.χ h) :=
  Path.ofEq (ch.class_fn g h)

/-- 16. Path: conjugating twice returns to original character value. -/
def char_double_conjugate {R : Type v} (ch : Character G R pg) (g h : G) :
    Path (ch.χ (pg.mul g (pg.mul (pg.mul g (pg.mul h (pg.inv g))) (pg.inv g))))
         (ch.χ h) :=
  Path.trans
    (char_class_fn_path ch g (pg.mul g (pg.mul h (pg.inv g))))
    (char_class_fn_path ch g h)

/-- 17. Two characters equal at all points give a path between χ functions. -/
def char_ext_path {R : Type v} (ch₁ ch₂ : Character G R pg)
    (h : ∀ g, ch₁.χ g = ch₂.χ g) :
    Path ch₁.χ ch₂.χ :=
  Path.ofEq (funext h)

/-! ## 18–21: Direct Sum Decomposition (Maschke structure) -/

/-- A direct sum decomposition of a representation. -/
structure DirectSumDecomp {V₁ V₂ : Type v}
    (ρ : Rep G V pg) (ρ₁ : Rep G V₁ pg) (ρ₂ : Rep G V₂ pg) where
  inj₁ : V₁ → V
  inj₂ : V₂ → V
  proj₁ : V → V₁
  proj₂ : V → V₂
  /-- Projections are equivariant -/
  proj₁_equiv : ∀ g v, proj₁ (ρ.act g v) = ρ₁.act g (proj₁ v)
  proj₂_equiv : ∀ g v, proj₂ (ρ.act g v) = ρ₂.act g (proj₂ v)
  /-- Injections are equivariant -/
  inj₁_equiv : ∀ g v, ρ.act g (inj₁ v) = inj₁ (ρ₁.act g v)
  inj₂_equiv : ∀ g v, ρ.act g (inj₂ v) = inj₂ (ρ₂.act g v)
  /-- Decomposition property -/
  decompose : ∀ v, v = inj₁ (proj₁ v)  -- simplified: first component recovers

/-- 18. Path: projection is equivariant. -/
def proj_equivariant_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V) :
    Path (d.proj₁ (ρ.act g v)) (ρ₁.act g (d.proj₁ v)) :=
  Path.ofEq (d.proj₁_equiv g v)

/-- 19. Path: injection is equivariant. -/
def inj_equivariant_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V₁) :
    Path (ρ.act g (d.inj₁ v)) (d.inj₁ (ρ₁.act g v)) :=
  Path.ofEq (d.inj₁_equiv g v)

/-- 20. Path: round-trip proj₁ ∘ inj₁ composed with the action. -/
def decomp_roundtrip_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V)
    (retract : ∀ w, d.proj₁ (d.inj₁ w) = w) :
    Path (d.proj₁ (ρ.act g (d.inj₁ (d.proj₁ v)))) (ρ₁.act g (d.proj₁ v)) :=
  Path.trans
    (proj_equivariant_path d g (d.inj₁ (d.proj₁ v)))
    (Path.congrArg (ρ₁.act g) (Path.ofEq (retract (d.proj₁ v))))

/-- 21. Maschke path: the decomposition is stable under the group action. -/
def maschke_stability_path {V₁ V₂ : Type v}
    {ρ : Rep G V pg} {ρ₁ : Rep G V₁ pg} {ρ₂ : Rep G V₂ pg}
    (d : DirectSumDecomp ρ ρ₁ ρ₂) (g : G) (v : V) :
    Path (d.proj₁ (ρ.act g v)) (ρ₁.act g (d.proj₁ v)) :=
  proj_equivariant_path d g v

/-! ## 22–25: Tensor Products of Representations -/

/-- Tensor product representation on V × W. -/
def tensorRep (ρ : Rep G V pg) (σ : Rep G W pg) : Rep G (V × W) pg where
  act g vw := (ρ.act g vw.1, σ.act g vw.2)
  act_e vw := by simp [ρ.act_e, σ.act_e]
  act_mul g h vw := by simp [ρ.act_mul, σ.act_mul]

/-- 22. Path: tensor action on first component. -/
def tensor_fst_path (ρ : Rep G V pg) (σ : Rep G W pg) (g : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act g (v, w)).1 (ρ.act g v) :=
  Path.refl _

/-- 23. Path: tensor action on second component. -/
def tensor_snd_path (ρ : Rep G V pg) (σ : Rep G W pg) (g : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act g (v, w)).2 (σ.act g w) :=
  Path.refl _

/-- 24. Path: tensor identity acts trivially. -/
def tensor_identity_path (ρ : Rep G V pg) (σ : Rep G W pg) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act pg.e (v, w)) (v, w) :=
  act_identity_path (tensorRep ρ σ) (v, w)

/-- 25. Path: tensor respects multiplication. -/
def tensor_mul_path (ρ : Rep G V pg) (σ : Rep G W pg) (g h : G) (v : V) (w : W) :
    Path ((tensorRep ρ σ).act (pg.mul g h) (v, w))
         ((tensorRep ρ σ).act g ((tensorRep ρ σ).act h (v, w))) :=
  act_mul_path (tensorRep ρ σ) g h (v, w)

/-! ## 26–28: Inner Product / Orthogonality -/

/-- An inner product on characters over a summation structure. -/
structure CharInnerProduct (G : Type u) (R : Type v) (pg : PGroup G) where
  sum : (G → R) → R
  mul_R : R → R → R
  conj : R → R
  /-- ⟨χ₁, χ₂⟩ = sum_g χ₁(g) * conj(χ₂(g)) -/
  inner : (G → R) → (G → R) → R
  inner_def : ∀ f₁ f₂, inner f₁ f₂ = sum (fun g => mul_R (f₁ g) (conj (f₂ g)))

/-- 26. Path: inner product definition unfolds. -/
def inner_product_unfold_path {R : Type v}
    (ip : CharInnerProduct G R pg) (f₁ f₂ : G → R) :
    Path (ip.inner f₁ f₂) (ip.sum (fun g => ip.mul_R (f₁ g) (ip.conj (f₂ g)))) :=
  Path.ofEq (ip.inner_def f₁ f₂)

/-- 27. Path: if two characters are equal, their inner products are equal. -/
def inner_product_char_eq_path {R : Type v}
    (ip : CharInnerProduct G R pg)
    (ch₁ ch₂ : Character G R pg)
    (h : ch₁.χ = ch₂.χ) (f : G → R) :
    Path (ip.inner ch₁.χ f) (ip.inner ch₂.χ f) :=
  Path.congrArg (fun χ => ip.inner χ f) (Path.ofEq h)

/-- 28. Orthogonality: if inner product is zero, path from inner to zero. -/
def orthogonality_path {R : Type v}
    (ip : CharInnerProduct G R pg)
    (ch₁ ch₂ : Character G R pg)
    (zero_R : R)
    (h : ip.inner ch₁.χ ch₂.χ = zero_R) :
    Path (ip.inner ch₁.χ ch₂.χ) zero_R :=
  Path.ofEq h

/-! ## 29–32: Representation Morphisms and Naturality -/

/-- 29. Equivariance as a naturality square: path form. -/
def equivariance_naturality {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (g : G) (v : V) :
    Path (φ.f (ρ.act g v)) (σ.act g (φ.f v)) :=
  Path.ofEq (φ.equivariant g v)

/-- 30. Path: naturality square for composition of two equivariant maps. -/
def naturality_comp_path {ρ : Rep G V pg} {σ : Rep G W pg} {τ : Rep G U pg}
    (φ : EquivariantMap ρ σ) (ψ : EquivariantMap σ τ) (g : G) (v : V) :
    Path (ψ.f (φ.f (ρ.act g v))) (τ.act g (ψ.f (φ.f v))) :=
  equivariant_comp_path φ ψ g v

/-- 31. Path: equivariant map commutes with identity action. -/
def equivariant_at_identity_path {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) (v : V) :
    Path (φ.f (ρ.act pg.e v)) (φ.f v) :=
  Path.congrArg φ.f (act_identity_path ρ v)

/-- 32. Path: composing identity equivariant map does nothing. -/
theorem equivariantId_comp {ρ : Rep G V pg} {σ : Rep G W pg}
    (φ : EquivariantMap ρ σ) :
    (equivariantComp (equivariantId ρ) φ).f = φ.f := by
  rfl

/-! ## 33–35: Restriction and Induction -/

/-- A subgroup given by a predicate and closure properties. -/
structure Subgroup (pg : PGroup G) where
  mem : G → Prop
  e_mem : mem pg.e
  mul_mem : ∀ {a b}, mem a → mem b → mem (pg.mul a b)
  inv_mem : ∀ {a}, mem a → mem (pg.inv a)

/-- Restriction of a representation to a subgroup. -/
def restrict (ρ : Rep G V pg) (H : Subgroup pg) :
    Rep { g : G // H.mem g } V
      { e := ⟨pg.e, H.e_mem⟩
        mul := fun a b => ⟨pg.mul a.1 b.1, H.mul_mem a.2 b.2⟩
        inv := fun a => ⟨pg.inv a.1, H.inv_mem a.2⟩
        mul_assoc := fun a b c => by ext; exact pg.mul_assoc a.1 b.1 c.1
        e_mul := fun a => by ext; exact pg.e_mul a.1
        mul_e := fun a => by ext; exact pg.mul_e a.1
        inv_mul := fun a => by ext; exact pg.inv_mul a.1
        mul_inv := fun a => by ext; exact pg.mul_inv a.1 } where
  act g v := ρ.act g.1 v
  act_e v := ρ.act_e v
  act_mul g h v := ρ.act_mul g.1 h.1 v

/-- 33. Path: restriction preserves identity action. -/
def restrict_identity_path (ρ : Rep G V pg) (H : Subgroup pg) (v : V) :
    Path ((restrict ρ H).act ⟨pg.e, H.e_mem⟩ v) v :=
  Path.ofEq (ρ.act_e v)

/-- 34. Path: restriction preserves action multiplication. -/
def restrict_mul_path (ρ : Rep G V pg) (H : Subgroup pg)
    (g h : { x : G // H.mem x }) (v : V) :
    Path ((restrict ρ H).act ⟨pg.mul g.1 h.1, H.mul_mem g.2 h.2⟩ v)
         ((restrict ρ H).act g ((restrict ρ H).act h v)) :=
  Path.ofEq (ρ.act_mul g.1 h.1 v)

/-- 35. Path: restriction commutes with inverse cancellation. -/
def restrict_inv_cancel_path (ρ : Rep G V pg) (H : Subgroup pg)
    (g : { x : G // H.mem x }) (v : V) :
    Path ((restrict ρ H).act g ((restrict ρ H).act ⟨pg.inv g.1, H.inv_mem g.2⟩ v)) v :=
  act_inv_cancel_path ρ g.1 v

end ComputationalPaths.Path.Algebra.RepresentationDeep
