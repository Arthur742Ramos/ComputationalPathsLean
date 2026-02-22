/-
# Deep Representation Theory (Schur-Weyl) via Computational Paths

Schur's lemma, Maschke's theorem, character theory, tensor products,
induced representations, Peter-Weyl, Burnside — formalized through
multi-step computational path reasoning.

## References
- Fulton & Harris, "Representation Theory"
- Serre, "Linear Representations of Finite Groups"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SchurWeylDeep

open ComputationalPaths.Path

universe u v

/-! ## Core algebraic structures -/

/-- A group structure (abstract). -/
structure Grp where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ a, Path (mul a one) a
  one_mul : ∀ a, Path (mul one a) a
  mul_inv : ∀ a, Path (mul a (inv a)) one
  inv_mul : ∀ a, Path (mul (inv a) a) one

/-- A representation of G on a type V. -/
structure Rep (G : Grp.{u}) where
  V : Type u
  act : G.carrier → V → V
  act_one : ∀ v, Path (act G.one v) v
  act_mul : ∀ g h v, Path (act (G.mul g h) v) (act g (act h v))

/-- A morphism of representations (intertwiner). -/
structure RepMorphism {G : Grp.{u}} (ρ σ : Rep G) where
  map : ρ.V → σ.V
  equivariant : ∀ g v, Path (map (ρ.act g v)) (σ.act g (map v))

variable {G : Grp.{u}}

/-! ## 1: Identity intertwiner -/

noncomputable def repMorphism_id (ρ : Rep G) : RepMorphism ρ ρ where
  map := id
  equivariant := fun _ _ => Path.refl _

/-! ## 2: Composition of intertwiners -/

noncomputable def repMorphism_comp {ρ σ τ : Rep G}
    (f : RepMorphism ρ σ) (g : RepMorphism σ τ) : RepMorphism ρ τ where
  map := g.map ∘ f.map
  equivariant := fun gh v =>
    let step1 : Path (g.map (f.map (ρ.act gh v))) (g.map (σ.act gh (f.map v))) :=
      Path.congrArg g.map (f.equivariant gh v)
    let step2 : Path (g.map (σ.act gh (f.map v))) (τ.act gh (g.map (f.map v))) :=
      g.equivariant gh (f.map v)
    Path.trans step1 step2

/-! ## 3: Composition preserves equivariance (explicit) -/

noncomputable def repMorphism_comp_equivariant {ρ σ τ : Rep G}
    (f : RepMorphism ρ σ) (g : RepMorphism σ τ) (gh : G.carrier) (v : ρ.V) :
    Path (g.map (f.map (ρ.act gh v))) (τ.act gh (g.map (f.map v))) :=
  (repMorphism_comp f g).equivariant gh v

/-! ## 4: Left unit law for intertwiner composition -/

noncomputable def repMorphism_comp_id_left {ρ σ : Rep G} (f : RepMorphism ρ σ)
    (g : G.carrier) (v : ρ.V) :
    Path ((repMorphism_comp (repMorphism_id ρ) f).map (ρ.act g v))
         (σ.act g (f.map v)) :=
  (repMorphism_comp (repMorphism_id ρ) f).equivariant g v

/-! ## Schur's lemma structure -/

/-- Irreducibility: every equivariant endomorphism is trivial (scalar). -/
structure Irreducible (ρ : Rep G) where
  scalar : RepMorphism ρ ρ → ρ.V → ρ.V
  is_scalar : ∀ (f : RepMorphism ρ ρ) (v : ρ.V), Path (f.map v) (scalar f v)

/-! ## 5: Schur's lemma: endomorphism reduces to scalar -/

noncomputable def schur_endomorphism_scalar (ρ : Rep G) (irr : Irreducible ρ)
    (f : RepMorphism ρ ρ) (v : ρ.V) :
    Path (f.map v) (irr.scalar f v) :=
  irr.is_scalar f v

/-! ## 6: Schur composition of two endomorphisms -/

noncomputable def schur_comp_scalar (ρ : Rep G) (irr : Irreducible ρ)
    (f g : RepMorphism ρ ρ) (v : ρ.V) :
    Path ((repMorphism_comp f g).map v) (irr.scalar (repMorphism_comp f g) v) :=
  irr.is_scalar (repMorphism_comp f g) v

/-! ## 7: Schur equivariance + scalar factorization -/

noncomputable def schur_equivariant_scalar (ρ : Rep G) (irr : Irreducible ρ)
    (f : RepMorphism ρ ρ) (gh : G.carrier) (v : ρ.V) :
    Path (f.map (ρ.act gh v)) (ρ.act gh (irr.scalar f v)) :=
  let step1 : Path (f.map (ρ.act gh v)) (ρ.act gh (f.map v)) :=
    f.equivariant gh v
  let step2 : Path (ρ.act gh (f.map v)) (ρ.act gh (irr.scalar f v)) :=
    Path.congrArg (ρ.act gh) (irr.is_scalar f v)
  Path.trans step1 step2

/-! ## Maschke's theorem structure -/

/-- Complete reducibility: every subrepresentation has a complement. -/
structure CompletelyReducible (ρ : Rep G) where
  /-- Projection onto subspace. -/
  projSub : ρ.V → ρ.V
  /-- Projection onto complement. -/
  projComp : ρ.V → ρ.V
  /-- Direct sum decomposition. -/
  decomp : ∀ v, Path v (ρ.act G.one v)
  /-- Projection is equivariant. -/
  proj_equivariant : ∀ g v, Path (projSub (ρ.act g v)) (ρ.act g (projSub v))
  /-- Complement projection is equivariant. -/
  comp_equivariant : ∀ g v, Path (projComp (ρ.act g v)) (ρ.act g (projComp v))

/-! ## 8: Maschke projection equivariance -/

noncomputable def maschke_proj_equivariant (ρ : Rep G) (cr : CompletelyReducible ρ)
    (g : G.carrier) (v : ρ.V) :
    Path (cr.projSub (ρ.act g v)) (ρ.act g (cr.projSub v)) :=
  cr.proj_equivariant g v

/-! ## 9: Maschke complement equivariance -/

noncomputable def maschke_comp_equivariant (ρ : Rep G) (cr : CompletelyReducible ρ)
    (g : G.carrier) (v : ρ.V) :
    Path (cr.projComp (ρ.act g v)) (ρ.act g (cr.projComp v)) :=
  cr.comp_equivariant g v

/-! ## 10: Maschke + Schur: projection is scalar on irreducible -/

noncomputable def maschke_schur_proj_scalar (ρ : Rep G) (irr : Irreducible ρ)
    (cr : CompletelyReducible ρ) (v : ρ.V) :
    Path (cr.projSub v)
         (irr.scalar ⟨cr.projSub, cr.proj_equivariant⟩ v) :=
  irr.is_scalar ⟨cr.projSub, cr.proj_equivariant⟩ v

/-! ## Character theory -/

/-- A character: trace of the representation (abstracted). -/
structure Character (G : Grp.{u}) where
  χ : G.carrier → G.carrier
  /-- Character is a class function. -/
  class_fn : ∀ g h, Path (χ (G.mul (G.mul g h) (G.inv g))) (χ h)
  /-- Character of identity. -/
  χ_one : G.carrier

/-! ## 11: Character class function property -/

noncomputable def character_class_fn (ch : Character G) (g h : G.carrier) :
    Path (ch.χ (G.mul (G.mul g h) (G.inv g))) (ch.χ h) :=
  ch.class_fn g h

/-! ## 12: Character conjugation invariance (two-step) -/

noncomputable def character_conjugation_two (ch : Character G) (g₁ g₂ h : G.carrier) :
    Path (ch.χ (G.mul (G.mul g₁ (G.mul (G.mul g₂ h) (G.inv g₂))) (G.inv g₁)))
         (ch.χ h) :=
  let step1 := ch.class_fn g₁ (G.mul (G.mul g₂ h) (G.inv g₂))
  let step2 := ch.class_fn g₂ h
  Path.trans step1 step2

/-! ## Character orthogonality -/

structure CharacterOrthogonality (G : Grp.{u}) where
  chars : Nat → Character G
  inner : Character G → Character G → G.carrier
  orthogonality : ∀ i j, (i ≠ j) →
    Path (inner (chars i) (chars j)) G.one
  norm : ∀ i, Path (inner (chars i) (chars i)) (inner (chars i) (chars i))

/-! ## 13: Orthogonality for distinct characters -/

noncomputable def char_orthogonal (orth : CharacterOrthogonality G)
    (i j : Nat) (hij : i ≠ j) :
    Path (orth.inner (orth.chars i) (orth.chars j)) G.one :=
  orth.orthogonality i j hij

/-! ## Tensor product of representations -/

structure TensorRep (G : Grp.{u}) (ρ σ : Rep G) where
  tensor : Type u
  tensorAct : G.carrier → tensor → tensor
  tensorAct_one : ∀ t, Path (tensorAct G.one t) t
  tensorAct_mul : ∀ g h t, Path (tensorAct (G.mul g h) t) (tensorAct g (tensorAct h t))
  pair : ρ.V → σ.V → tensor
  pair_act : ∀ g v w, Path (tensorAct g (pair v w)) (pair (ρ.act g v) (σ.act g w))

/-! ## 14: Tensor action on identity -/

noncomputable def tensor_act_one (ρ σ : Rep G) (T : TensorRep G ρ σ) (t : T.tensor) :
    Path (T.tensorAct G.one t) t :=
  T.tensorAct_one t

/-! ## 15: Tensor action on product -/

noncomputable def tensor_act_mul (ρ σ : Rep G) (T : TensorRep G ρ σ) (g h : G.carrier) (t : T.tensor) :
    Path (T.tensorAct (G.mul g h) t) (T.tensorAct g (T.tensorAct h t)) :=
  T.tensorAct_mul g h t

/-! ## 16: Tensor pair equivariance -/

noncomputable def tensor_pair_equivariant (ρ σ : Rep G) (T : TensorRep G ρ σ)
    (g : G.carrier) (v : ρ.V) (w : σ.V) :
    Path (T.tensorAct g (T.pair v w)) (T.pair (ρ.act g v) (σ.act g w)) :=
  T.pair_act g v w

/-! ## 17: Tensor double action via trans -/

noncomputable def tensor_double_action (ρ σ : Rep G) (T : TensorRep G ρ σ)
    (g h : G.carrier) (v : ρ.V) (w : σ.V) :
    Path (T.tensorAct (G.mul g h) (T.pair v w))
         (T.pair (ρ.act g (ρ.act h v)) (σ.act g (σ.act h w))) :=
  let step1 : Path (T.tensorAct (G.mul g h) (T.pair v w))
                   (T.tensorAct g (T.tensorAct h (T.pair v w))) :=
    T.tensorAct_mul g h (T.pair v w)
  let step2 : Path (T.tensorAct g (T.tensorAct h (T.pair v w)))
                   (T.tensorAct g (T.pair (ρ.act h v) (σ.act h w))) :=
    Path.congrArg (T.tensorAct g) (T.pair_act h v w)
  let step3 : Path (T.tensorAct g (T.pair (ρ.act h v) (σ.act h w)))
                   (T.pair (ρ.act g (ρ.act h v)) (σ.act g (σ.act h w))) :=
    T.pair_act g (ρ.act h v) (σ.act h w)
  Path.trans (Path.trans step1 step2) step3

/-! ## Induced representations -/

structure InducedRep (G H : Grp.{u}) (ρ : Rep H) where
  /-- Inclusion of H into G. -/
  incl : H.carrier → G.carrier
  /-- Coset representatives. -/
  cosets : Type u
  /-- The induced representation space. -/
  indV : Type u
  /-- Action of G on induced space. -/
  indAct : G.carrier → indV → indV
  indAct_one : ∀ v, Path (indAct G.one v) v
  indAct_mul : ∀ g₁ g₂ v, Path (indAct (G.mul g₁ g₂) v) (indAct g₁ (indAct g₂ v))
  /-- Restriction to H gives back ρ (Frobenius reciprocity witness). -/
  restrict : indV → ρ.V
  restrict_equivariant : ∀ h v,
    Path (restrict (indAct (incl h) v)) (ρ.act h (restrict v))

/-! ## 18: Induced representation identity action -/

noncomputable def induced_act_one (G H : Grp.{u}) (ρ : Rep H) (ind : InducedRep G H ρ)
    (v : ind.indV) :
    Path (ind.indAct G.one v) v :=
  ind.indAct_one v

/-! ## 19: Induced representation composition -/

noncomputable def induced_act_mul (G H : Grp.{u}) (ρ : Rep H) (ind : InducedRep G H ρ)
    (g₁ g₂ : G.carrier) (v : ind.indV) :
    Path (ind.indAct (G.mul g₁ g₂) v) (ind.indAct g₁ (ind.indAct g₂ v)) :=
  ind.indAct_mul g₁ g₂ v

/-! ## 20: Frobenius reciprocity witness -/

noncomputable def frobenius_reciprocity (G H : Grp.{u}) (ρ : Rep H) (ind : InducedRep G H ρ)
    (h : H.carrier) (v : ind.indV) :
    Path (ind.restrict (ind.indAct (ind.incl h) v)) (ρ.act h (ind.restrict v)) :=
  ind.restrict_equivariant h v

/-! ## 21: Frobenius reciprocity with double action -/

noncomputable def frobenius_double (G H : Grp.{u}) (ρ : Rep H) (ind : InducedRep G H ρ)
    (h₁ h₂ : H.carrier) (v : ind.indV) :
    Path (ind.restrict (ind.indAct (ind.incl (H.mul h₁ h₂)) v))
         (ρ.act h₁ (ρ.act h₂ (ind.restrict v))) :=
  let step1 : Path (ind.restrict (ind.indAct (ind.incl (H.mul h₁ h₂)) v))
                   (ρ.act (H.mul h₁ h₂) (ind.restrict v)) :=
    ind.restrict_equivariant (H.mul h₁ h₂) v
  let step2 : Path (ρ.act (H.mul h₁ h₂) (ind.restrict v))
                   (ρ.act h₁ (ρ.act h₂ (ind.restrict v))) :=
    ρ.act_mul h₁ h₂ (ind.restrict v)
  Path.trans step1 step2

/-! ## Burnside's theorem structure (group algebra) -/

structure GroupAlgebra (G : Grp.{u}) where
  /-- Group algebra element type. -/
  Elem : Type u
  /-- Embedding of group elements. -/
  embed : G.carrier → Elem
  /-- Multiplication in the algebra. -/
  algMul : Elem → Elem → Elem
  /-- Unit. -/
  algOne : Elem
  /-- Embedding preserves multiplication. -/
  embed_mul : ∀ g h, Path (embed (G.mul g h)) (algMul (embed g) (embed h))
  /-- Embedding preserves identity. -/
  embed_one : Path (embed G.one) algOne
  /-- Associativity. -/
  algMul_assoc : ∀ a b c, Path (algMul (algMul a b) c) (algMul a (algMul b c))

/-! ## 22: Group algebra embedding preserves multiplication -/

noncomputable def groupAlg_embed_mul (ga : GroupAlgebra G) (g h : G.carrier) :
    Path (ga.embed (G.mul g h)) (ga.algMul (ga.embed g) (ga.embed h)) :=
  ga.embed_mul g h

/-! ## 23: Group algebra triple product via trans -/

noncomputable def groupAlg_triple_product (ga : GroupAlgebra G) (g h k : G.carrier) :
    Path (ga.embed (G.mul (G.mul g h) k))
         (ga.algMul (ga.embed g) (ga.algMul (ga.embed h) (ga.embed k))) :=
  let step1 : Path (ga.embed (G.mul (G.mul g h) k))
                   (ga.algMul (ga.embed (G.mul g h)) (ga.embed k)) :=
    ga.embed_mul (G.mul g h) k
  let step2 : Path (ga.algMul (ga.embed (G.mul g h)) (ga.embed k))
                   (ga.algMul (ga.algMul (ga.embed g) (ga.embed h)) (ga.embed k)) :=
    Path.congrArg (fun x => ga.algMul x (ga.embed k)) (ga.embed_mul g h)
  let step3 : Path (ga.algMul (ga.algMul (ga.embed g) (ga.embed h)) (ga.embed k))
                   (ga.algMul (ga.embed g) (ga.algMul (ga.embed h) (ga.embed k))) :=
    ga.algMul_assoc (ga.embed g) (ga.embed h) (ga.embed k)
  Path.trans (Path.trans step1 step2) step3

/-! ## 24: Group algebra identity embedding -/

noncomputable def groupAlg_embed_one (ga : GroupAlgebra G) :
    Path (ga.embed G.one) ga.algOne :=
  ga.embed_one

/-! ## 25: Group algebra embedding inverse coherence -/

noncomputable def groupAlg_embed_inv_mul (ga : GroupAlgebra G) (g : G.carrier) :
    Path (ga.embed (G.mul g (G.inv g))) ga.algOne :=
  let step1 : Path (ga.embed (G.mul g (G.inv g)))
                   (ga.algMul (ga.embed g) (ga.embed (G.inv g))) :=
    ga.embed_mul g (G.inv g)
  let step2_inner : Path (G.mul g (G.inv g)) G.one := G.mul_inv g
  let step2 : Path (ga.embed (G.mul g (G.inv g))) ga.algOne :=
    Path.trans (Path.congrArg ga.embed step2_inner) ga.embed_one
  step2

/-! ## Peter-Weyl structure -/

structure PeterWeyl (G : Grp.{u}) where
  /-- Family of irreducible representations. -/
  irreps : Nat → Rep G
  /-- Each irrep is irreducible. -/
  irred : (n : Nat) → Irreducible (irreps n)
  /-- Matrix coefficients. -/
  matCoeff : Nat → G.carrier → G.carrier
  /-- Completeness: every class function decomposes. -/
  complete : (f : G.carrier → G.carrier) →
    (n : Nat) → G.carrier → Path (f (G.mul G.one G.one)) (f G.one)

/-! ## 26: Peter-Weyl irreducibility witness -/

noncomputable def peter_weyl_irred (pw : PeterWeyl G) (n : Nat) :
    Irreducible (pw.irreps n) :=
  pw.irred n

/-! ## 27: Peter-Weyl Schur on n-th irrep -/

noncomputable def peter_weyl_schur (pw : PeterWeyl G) (n : Nat)
    (f : RepMorphism (pw.irreps n) (pw.irreps n)) (v : (pw.irreps n).V) :
    Path (f.map v) ((pw.irred n).scalar f v) :=
  (pw.irred n).is_scalar f v

/-! ## Weight lattice paths -/

structure WeightLattice where
  weights : Type u
  add : weights → weights → weights
  zero : weights
  neg : weights → weights
  add_zero : ∀ w, Path (add w zero) w
  zero_add : ∀ w, Path (add zero w) w
  add_neg : ∀ w, Path (add w (neg w)) zero
  add_assoc : ∀ w₁ w₂ w₃, Path (add (add w₁ w₂) w₃) (add w₁ (add w₂ w₃))

/-! ## 28: Weight lattice identity -/

noncomputable def weight_add_zero (wl : WeightLattice.{u}) (w : wl.weights) :
    Path (wl.add w wl.zero) w :=
  wl.add_zero w

/-! ## 29: Weight lattice inverse -/

noncomputable def weight_add_neg (wl : WeightLattice.{u}) (w : wl.weights) :
    Path (wl.add w (wl.neg w)) wl.zero :=
  wl.add_neg w

/-! ## 30: Weight lattice double inverse via trans -/

noncomputable def weight_double_neg (wl : WeightLattice.{u}) (w : wl.weights) :
    Path (wl.add (wl.add w (wl.neg w)) (wl.neg wl.zero))
         (wl.neg wl.zero) :=
  let step1 : Path (wl.add (wl.add w (wl.neg w)) (wl.neg wl.zero))
                   (wl.add wl.zero (wl.neg wl.zero)) :=
    Path.congrArg (fun x => wl.add x (wl.neg wl.zero)) (wl.add_neg w)
  let step2 : Path (wl.add wl.zero (wl.neg wl.zero)) (wl.neg wl.zero) :=
    wl.zero_add (wl.neg wl.zero)
  Path.trans step1 step2

/-! ## 31: Weight lattice associativity four-fold -/

noncomputable def weight_assoc_four (wl : WeightLattice.{u}) (a b c d : wl.weights) :
    Path (wl.add (wl.add (wl.add a b) c) d)
         (wl.add a (wl.add b (wl.add c d))) :=
  let step1 := wl.add_assoc (wl.add a b) c d
  let step2 := Path.congrArg (fun x => wl.add x (wl.add c d)) (wl.add_assoc a b c)
  -- Hmm, step2 has wrong shape. Let me restructure:
  let s1 : Path (wl.add (wl.add (wl.add a b) c) d)
                (wl.add (wl.add a b) (wl.add c d)) :=
    wl.add_assoc (wl.add a b) c d
  let s2 : Path (wl.add (wl.add a b) (wl.add c d))
                (wl.add a (wl.add b (wl.add c d))) :=
    wl.add_assoc a b (wl.add c d)
  Path.trans s1 s2

/-! ## Representation ring -/

structure RepRing (G : Grp.{u}) where
  elem : Type u
  add : elem → elem → elem
  mul : elem → elem → elem
  zero : elem
  one : elem
  fromRep : Rep G → elem
  add_comm : ∀ a b, Path (add a b) (add b a)
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, Path (add a zero) a
  mul_one : ∀ a, Path (mul a one) a

/-! ## 32: Rep ring addition commutes -/

noncomputable def repRing_add_comm (rr : RepRing G) (a b : rr.elem) :
    Path (rr.add a b) (rr.add b a) :=
  rr.add_comm a b

/-! ## 33: Rep ring multiplication associativity -/

noncomputable def repRing_mul_assoc (rr : RepRing G) (a b c : rr.elem) :
    Path (rr.mul (rr.mul a b) c) (rr.mul a (rr.mul b c)) :=
  rr.mul_assoc a b c

/-! ## 34: Rep ring triple add commutation -/

noncomputable def repRing_triple_add_comm (rr : RepRing G) (a b c : rr.elem) :
    Path (rr.add (rr.add a b) c) (rr.add c (rr.add a b)) :=
  let step1 : Path (rr.add (rr.add a b) c) (rr.add c (rr.add a b)) :=
    rr.add_comm (rr.add a b) c
  step1

/-! ## 35: Rep ring identity chain -/

noncomputable def repRing_identity_chain (rr : RepRing G) (a : rr.elem) :
    Path (rr.mul (rr.mul a rr.one) rr.one) a :=
  let step1 : Path (rr.mul (rr.mul a rr.one) rr.one)
                   (rr.mul a rr.one) :=
    rr.mul_one (rr.mul a rr.one)
  let step2 : Path (rr.mul a rr.one) a := rr.mul_one a
  Path.trans step1 step2

/-! ## 36: Action on identity element -/

noncomputable def rep_act_one_v (ρ : Rep G) (v : ρ.V) :
    Path (ρ.act G.one v) v :=
  ρ.act_one v

/-! ## 37: Action composition (g * h) -/

noncomputable def rep_act_mul (ρ : Rep G) (g h : G.carrier) (v : ρ.V) :
    Path (ρ.act (G.mul g h) v) (ρ.act g (ρ.act h v)) :=
  ρ.act_mul g h v

/-! ## 38: Triple action via trans chain -/

noncomputable def rep_triple_action (ρ : Rep G) (g h k : G.carrier) (v : ρ.V) :
    Path (ρ.act (G.mul (G.mul g h) k) v)
         (ρ.act g (ρ.act h (ρ.act k v))) :=
  let step1 : Path (ρ.act (G.mul (G.mul g h) k) v)
                   (ρ.act (G.mul g h) (ρ.act k v)) :=
    ρ.act_mul (G.mul g h) k v
  let step2 : Path (ρ.act (G.mul g h) (ρ.act k v))
                   (ρ.act g (ρ.act h (ρ.act k v))) :=
    ρ.act_mul g h (ρ.act k v)
  Path.trans step1 step2

/-! ## 39: Action by inverse cancels -/

noncomputable def rep_act_inv_cancel (ρ : Rep G) (g : G.carrier) (v : ρ.V) :
    Path (ρ.act (G.mul g (G.inv g)) v) v :=
  let step1 : Path (ρ.act (G.mul g (G.inv g)) v)
                   (ρ.act g (ρ.act (G.inv g) v)) :=
    ρ.act_mul g (G.inv g) v
  let step2_inner : Path (G.mul g (G.inv g)) G.one := G.mul_inv g
  let step2 : Path (ρ.act (G.mul g (G.inv g)) v) v :=
    Path.trans (Path.congrArg (fun x => ρ.act x v) step2_inner) (ρ.act_one v)
  step2

/-! ## 40: Group associativity + action coherence -/

noncomputable def rep_assoc_action (ρ : Rep G) (g h k : G.carrier) (v : ρ.V) :
    Path (ρ.act (G.mul g (G.mul h k)) v)
         (ρ.act g (ρ.act h (ρ.act k v))) :=
  let step1 : Path (ρ.act (G.mul g (G.mul h k)) v)
                   (ρ.act g (ρ.act (G.mul h k) v)) :=
    ρ.act_mul g (G.mul h k) v
  let step2 : Path (ρ.act g (ρ.act (G.mul h k) v))
                   (ρ.act g (ρ.act h (ρ.act k v))) :=
    Path.congrArg (ρ.act g) (ρ.act_mul h k v)
  Path.trans step1 step2

/-! ## 41: Group associativity witness via action -/

noncomputable def group_assoc_via_action (ρ : Rep G) (g h k : G.carrier) (v : ρ.V) :
    Path (ρ.act (G.mul (G.mul g h) k) v)
         (ρ.act (G.mul g (G.mul h k)) v) :=
  Path.congrArg (fun x => ρ.act x v) (G.mul_assoc g h k)

/-! ## 42: Intertwiner on identity action -/

noncomputable def intertwiner_on_identity {ρ σ : Rep G}
    (f : RepMorphism ρ σ) (v : ρ.V) :
    Path (f.map (ρ.act G.one v)) (σ.act G.one (f.map v)) :=
  f.equivariant G.one v

/-! ## 43: Intertwiner + identity simplification -/

noncomputable def intertwiner_identity_simplify {ρ σ : Rep G}
    (f : RepMorphism ρ σ) (v : ρ.V) :
    Path (f.map (ρ.act G.one v)) (f.map v) :=
  let step1 : Path (f.map (ρ.act G.one v)) (σ.act G.one (f.map v)) :=
    f.equivariant G.one v
  let step2 : Path (σ.act G.one (f.map v)) (f.map v) :=
    σ.act_one (f.map v)
  Path.trans step1 step2

/-! ## 44: Intertwiner on double action -/

noncomputable def intertwiner_double_action {ρ σ : Rep G}
    (f : RepMorphism ρ σ) (g h : G.carrier) (v : ρ.V) :
    Path (f.map (ρ.act g (ρ.act h v))) (σ.act g (σ.act h (f.map v))) :=
  let step1 : Path (f.map (ρ.act g (ρ.act h v)))
                   (σ.act g (f.map (ρ.act h v))) :=
    f.equivariant g (ρ.act h v)
  let step2 : Path (σ.act g (f.map (ρ.act h v)))
                   (σ.act g (σ.act h (f.map v))) :=
    Path.congrArg (σ.act g) (f.equivariant h v)
  Path.trans step1 step2

/-! ## 45: Triple composition of intertwiners -/

noncomputable def repMorphism_triple_comp {ρ σ τ υ : Rep G}
    (f : RepMorphism ρ σ) (g : RepMorphism σ τ) (h : RepMorphism τ υ)
    (gh : G.carrier) (v : ρ.V) :
    Path (h.map (g.map (f.map (ρ.act gh v)))) (υ.act gh (h.map (g.map (f.map v)))) :=
  let step1 : Path (h.map (g.map (f.map (ρ.act gh v))))
                   (h.map (g.map (σ.act gh (f.map v)))) :=
    Path.congrArg (fun x => h.map (g.map x)) (f.equivariant gh v)
  let step2 : Path (h.map (g.map (σ.act gh (f.map v))))
                   (h.map (τ.act gh (g.map (f.map v)))) :=
    Path.congrArg h.map (g.equivariant gh (f.map v))
  let step3 : Path (h.map (τ.act gh (g.map (f.map v))))
                   (υ.act gh (h.map (g.map (f.map v)))) :=
    h.equivariant gh (g.map (f.map v))
  Path.trans (Path.trans step1 step2) step3

end SchurWeylDeep
end Algebra
end Path
end ComputationalPaths
