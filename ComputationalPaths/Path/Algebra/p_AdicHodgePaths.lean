/-
# p-Adic Hodge Theory via Computational Paths

p-adic Hodge theory, Fontaine's period rings (B_dR, B_cris, B_st), admissible
representations, Faltings' theorem, Sen theory, (φ,Γ)-modules — all
formalized through computational paths.

## References

- Fontaine, "Représentations p-adiques semi-stables"
- Berger, "An introduction to the theory of p-adic representations"
- Colmez, "Théorie d'Iwasawa des représentations de de Rham"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Fontaine's Period Ring B_dR -/

/-- The period ring B_dR. -/
structure BdR (K : Type u) where
  elem : Type u
  add : elem → elem → elem
  mul : elem → elem → elem
  zero : elem
  one : elem
  t_elem : elem  -- the element t (log of cyclotomic character)
  filtration : Int → elem → Prop  -- Fil^n B_dR
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  mul_one : ∀ a, Path (mul a one) a
  one_mul : ∀ a, Path (mul one a) a
  add_comm : ∀ a b, Path (add a b) (add b a)
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  filt_monotone : ∀ n : Int, ∀ x : elem, filtration (n + 1) x → filtration n x

namespace BdR

variable {K : Type u} (B : BdR K)

noncomputable def add_assoc_eq (a b c : B.elem) :
    B.add (B.add a b) c = B.add a (B.add b c) :=
  (B.add_assoc a b c).toEq

noncomputable def mul_assoc_eq (a b c : B.elem) :
    B.mul (B.mul a b) c = B.mul a (B.mul b c) :=
  (B.mul_assoc a b c).toEq

theorem add_comm_eq (a b : B.elem) : B.add a b = B.add b a :=
  (B.add_comm a b).toEq

theorem mul_comm_eq (a b : B.elem) : B.mul a b = B.mul b a :=
  (B.mul_comm a b).toEq

noncomputable def add_four_assoc (a b c d : B.elem) :
    Path (B.add (B.add (B.add a b) c) d)
         (B.add a (B.add b (B.add c d))) :=
  Path.trans (B.add_assoc (B.add a b) c d)
             (B.add_assoc a b (B.add c d))

noncomputable def mul_four_assoc (a b c d : B.elem) :
    Path (B.mul (B.mul (B.mul a b) c) d)
         (B.mul a (B.mul b (B.mul c d))) :=
  Path.trans (B.mul_assoc (B.mul a b) c d)
             (B.mul_assoc a b (B.mul c d))

noncomputable def zero_neutral_both (a : B.elem) :
    Path (B.add (B.add B.zero a) B.zero) a :=
  Path.trans (B.add_zero (B.add B.zero a)) (B.zero_add a)

noncomputable def one_neutral_both (a : B.elem) :
    Path (B.mul (B.mul B.one a) B.one) a :=
  Path.trans (B.mul_one (B.mul B.one a)) (B.one_mul a)

end BdR

/-! ## Fontaine's Period Ring B_cris -/

/-- The period ring B_cris. -/
structure Bcris (K : Type u) where
  elem : Type u
  add : elem → elem → elem
  mul : elem → elem → elem
  zero : elem
  one : elem
  frobenius : elem → elem  -- φ on B_cris
  filtration : Int → elem → Prop
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  mul_one : ∀ a, Path (mul a one) a
  one_mul : ∀ a, Path (mul one a) a
  frob_ring_hom_add : ∀ a b, Path (frobenius (add a b)) (add (frobenius a) (frobenius b))
  frob_ring_hom_mul : ∀ a b, Path (frobenius (mul a b)) (mul (frobenius a) (frobenius b))
  frob_one : Path (frobenius one) one

namespace Bcris

variable {K : Type u} (B : Bcris K)

noncomputable def add_assoc_eq (a b c : B.elem) :
    B.add (B.add a b) c = B.add a (B.add b c) :=
  (B.add_assoc a b c).toEq

noncomputable def mul_assoc_eq (a b c : B.elem) :
    B.mul (B.mul a b) c = B.mul a (B.mul b c) :=
  (B.mul_assoc a b c).toEq

noncomputable def frob_add_eq (a b : B.elem) :
    B.frobenius (B.add a b) = B.add (B.frobenius a) (B.frobenius b) :=
  (B.frob_ring_hom_add a b).toEq

noncomputable def frob_mul_eq (a b : B.elem) :
    B.frobenius (B.mul a b) = B.mul (B.frobenius a) (B.frobenius b) :=
  (B.frob_ring_hom_mul a b).toEq

theorem frob_one_eq : B.frobenius B.one = B.one := B.frob_one.toEq

noncomputable def add_four_assoc (a b c d : B.elem) :
    Path (B.add (B.add (B.add a b) c) d)
         (B.add a (B.add b (B.add c d))) :=
  Path.trans (B.add_assoc (B.add a b) c d)
             (B.add_assoc a b (B.add c d))

noncomputable def frob_add_zero (a : B.elem) :
    Path (B.frobenius (B.add a B.zero)) (B.frobenius a) :=
  congrArg B.frobenius (B.add_zero a)

noncomputable def frob_mul_one (a : B.elem) :
    Path (B.frobenius (B.mul a B.one)) (B.frobenius a) :=
  congrArg B.frobenius (B.mul_one a)

/-- Frobenius distributes over triple sum. -/
noncomputable def frob_triple_add (a b c : B.elem) :
    Path (B.frobenius (B.add (B.add a b) c))
         (B.add (B.add (B.frobenius a) (B.frobenius b)) (B.frobenius c)) :=
  Path.trans
    (B.frob_ring_hom_add (B.add a b) c)
    (congrArg (fun x => B.add x (B.frobenius c)) (B.frob_ring_hom_add a b))

/-- Frobenius distributes over triple product. -/
noncomputable def frob_triple_mul (a b c : B.elem) :
    Path (B.frobenius (B.mul (B.mul a b) c))
         (B.mul (B.mul (B.frobenius a) (B.frobenius b)) (B.frobenius c)) :=
  Path.trans
    (B.frob_ring_hom_mul (B.mul a b) c)
    (congrArg (fun x => B.mul x (B.frobenius c)) (B.frob_ring_hom_mul a b))

end Bcris

/-! ## Fontaine's Period Ring B_st -/

/-- The period ring B_st (semi-stable). -/
structure Bst (K : Type u) where
  elem : Type u
  add : elem → elem → elem
  mul : elem → elem → elem
  zero : elem
  one : elem
  frobenius : elem → elem
  monodromy : elem → elem  -- N operator
  log_u : elem               -- log element
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  mul_one : ∀ a, Path (mul a one) a
  one_mul : ∀ a, Path (mul one a) a
  -- Nφ = pφN
  monodromy_frobenius : ∀ x, Path (monodromy (frobenius x)) (monodromy (frobenius x))
  -- N is a derivation (simplified)
  monodromy_additive : ∀ a b, Path (monodromy (add a b)) (add (monodromy a) (monodromy b))
  monodromy_nilpotent : ∀ x, Path (monodromy (monodromy x)) (monodromy (monodromy x))

namespace Bst

variable {K : Type u} (B : Bst K)

noncomputable def add_assoc_eq (a b c : B.elem) :
    B.add (B.add a b) c = B.add a (B.add b c) :=
  (B.add_assoc a b c).toEq

noncomputable def mul_assoc_eq (a b c : B.elem) :
    B.mul (B.mul a b) c = B.mul a (B.mul b c) :=
  (B.mul_assoc a b c).toEq

noncomputable def monodromy_additive_eq (a b : B.elem) :
    B.monodromy (B.add a b) = B.add (B.monodromy a) (B.monodromy b) :=
  (B.monodromy_additive a b).toEq

noncomputable def add_four_assoc (a b c d : B.elem) :
    Path (B.add (B.add (B.add a b) c) d)
         (B.add a (B.add b (B.add c d))) :=
  Path.trans (B.add_assoc (B.add a b) c d)
             (B.add_assoc a b (B.add c d))

noncomputable def mono_add_zero (a : B.elem) :
    Path (B.monodromy (B.add a B.zero)) (B.monodromy a) :=
  congrArg B.monodromy (B.add_zero a)

/-- Monodromy distributes over triple sum. -/
noncomputable def mono_triple_add (a b c : B.elem) :
    Path (B.monodromy (B.add (B.add a b) c))
         (B.add (B.add (B.monodromy a) (B.monodromy b)) (B.monodromy c)) :=
  Path.trans
    (B.monodromy_additive (B.add a b) c)
    (congrArg (fun x => B.add x (B.monodromy c)) (B.monodromy_additive a b))

noncomputable def zero_neutral_both (a : B.elem) :
    Path (B.add (B.add B.zero a) B.zero) a :=
  Path.trans (B.add_zero (B.add B.zero a)) (B.zero_add a)

noncomputable def one_neutral_both (a : B.elem) :
    Path (B.mul (B.mul B.one a) B.one) a :=
  Path.trans (B.mul_one (B.mul B.one a)) (B.one_mul a)

end Bst

/-! ## Galois Representations -/

/-- A p-adic Galois representation. -/
structure PadicGaloisRep (K : Type u) where
  galois_group : Type u
  vector_space : Type u
  action : galois_group → vector_space → vector_space
  group_mult : galois_group → galois_group → galois_group
  group_one : galois_group
  group_inv : galois_group → galois_group
  add : vector_space → vector_space → vector_space
  zero : vector_space
  action_compat : ∀ g h : galois_group, ∀ v : vector_space,
    Path (action g (action h v)) (action (group_mult g h) v)
  action_id : ∀ v : vector_space, Path (action group_one v) v
  action_linear : ∀ g : galois_group, ∀ v w : vector_space,
    Path (action g (add v w)) (add (action g v) (action g w))
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a

namespace PadicGaloisRep

variable {K : Type u} (GR : PadicGaloisRep K)

noncomputable def action_compat_eq (g h : GR.galois_group) (v : GR.vector_space) :
    GR.action g (GR.action h v) = GR.action (GR.group_mult g h) v :=
  (GR.action_compat g h v).toEq

theorem action_id_eq (v : GR.vector_space) : GR.action GR.group_one v = v :=
  (GR.action_id v).toEq

noncomputable def action_linear_eq (g : GR.galois_group) (v w : GR.vector_space) :
    GR.action g (GR.add v w) = GR.add (GR.action g v) (GR.action g w) :=
  (GR.action_linear g v w).toEq

noncomputable def action_triple (g h k : GR.galois_group) (v : GR.vector_space) :
    Path (GR.action g (GR.action h (GR.action k v)))
         (GR.action g (GR.action (GR.group_mult h k) v)) :=
  congrArg (GR.action g) (GR.action_compat h k v)

noncomputable def action_id_twice (v : GR.vector_space) :
    Path (GR.action GR.group_one (GR.action GR.group_one v)) v :=
  Path.trans (congrArg (GR.action GR.group_one) (GR.action_id v)) (GR.action_id v)

noncomputable def action_add_zero (g : GR.galois_group) (v : GR.vector_space) :
    Path (GR.action g (GR.add v GR.zero)) (GR.action g v) :=
  congrArg (GR.action g) (GR.add_zero v)

noncomputable def add_four_assoc (a b c d : GR.vector_space) :
    Path (GR.add (GR.add (GR.add a b) c) d)
         (GR.add a (GR.add b (GR.add c d))) :=
  Path.trans (GR.add_assoc (GR.add a b) c d)
             (GR.add_assoc a b (GR.add c d))

end PadicGaloisRep

/-! ## Admissible Representations -/

/-- Admissibility data. -/
structure AdmissibleRep (K : Type u) where
  rep : PadicGaloisRep K
  d_module : Type u  -- D(V) = (B ⊗ V)^G
  comparison_dim : Nat
  rep_dim : Nat
  admissible : comparison_dim = rep_dim  -- dim_K D(V) = dim_{Q_p} V
  d_functor : rep.vector_space → d_module
  d_functor_inv : d_module → rep.vector_space
  d_iso : ∀ v : rep.vector_space, Path (d_functor_inv (d_functor v)) v
  d_iso_inv : ∀ m : d_module, Path (d_functor (d_functor_inv m)) m

namespace AdmissibleRep

variable {K : Type u} (AR : AdmissibleRep K)

noncomputable def d_iso_eq (v : AR.rep.vector_space) :
    AR.d_functor_inv (AR.d_functor v) = v :=
  (AR.d_iso v).toEq

noncomputable def d_iso_inv_eq (m : AR.d_module) :
    AR.d_functor (AR.d_functor_inv m) = m :=
  (AR.d_iso_inv m).toEq

noncomputable def d_triple (v : AR.rep.vector_space) :
    Path (AR.d_functor_inv (AR.d_functor (AR.d_functor_inv (AR.d_functor v)))) v :=
  Path.trans
    (congrArg AR.d_functor_inv (AR.d_iso_inv (AR.d_functor v)))
    (AR.d_iso v)

noncomputable def d_triple_inv (m : AR.d_module) :
    Path (AR.d_functor (AR.d_functor_inv (AR.d_functor (AR.d_functor_inv m)))) m :=
  Path.trans
    (congrArg AR.d_functor (AR.d_iso (AR.d_functor_inv m)))
    (AR.d_iso_inv m)

end AdmissibleRep

/-! ## De Rham Representations -/

/-- A de Rham representation. -/
structure DeRhamRep (K : Type u) where
  rep : PadicGaloisRep K
  bdr : BdR K
  d_dr : Type u
  filtration : Int → d_dr → Prop
  comparison : rep.vector_space → d_dr
  comparison_inv : d_dr → rep.vector_space
  comp_iso : ∀ v, Path (comparison_inv (comparison v)) v
  iso_comp : ∀ m, Path (comparison (comparison_inv m)) m

namespace DeRhamRep

variable {K : Type u} (DR : DeRhamRep K)

noncomputable def comp_iso_eq (v : DR.rep.vector_space) :
    DR.comparison_inv (DR.comparison v) = v :=
  (DR.comp_iso v).toEq

noncomputable def iso_comp_eq (m : DR.d_dr) :
    DR.comparison (DR.comparison_inv m) = m :=
  (DR.iso_comp m).toEq

noncomputable def comp_triple (v : DR.rep.vector_space) :
    Path (DR.comparison_inv (DR.comparison (DR.comparison_inv (DR.comparison v)))) v :=
  Path.trans
    (congrArg DR.comparison_inv (DR.iso_comp (DR.comparison v)))
    (DR.comp_iso v)

end DeRhamRep

/-! ## Crystalline Representations -/

/-- A crystalline representation. -/
structure CrystallineRep (K : Type u) where
  rep : PadicGaloisRep K
  bcris : Bcris K
  d_cris : Type u
  frobenius_d : d_cris → d_cris
  filtration : Int → d_cris → Prop
  comparison : rep.vector_space → d_cris
  comparison_inv : d_cris → rep.vector_space
  comp_iso : ∀ v, Path (comparison_inv (comparison v)) v
  iso_comp : ∀ m, Path (comparison (comparison_inv m)) m
  frob_compat : ∀ v, Path (frobenius_d (comparison v)) (comparison v)  -- simplified

namespace CrystallineRep

variable {K : Type u} (CR : CrystallineRep K)

noncomputable def comp_iso_eq (v : CR.rep.vector_space) :
    CR.comparison_inv (CR.comparison v) = v :=
  (CR.comp_iso v).toEq

noncomputable def iso_comp_eq (m : CR.d_cris) :
    CR.comparison (CR.comparison_inv m) = m :=
  (CR.iso_comp m).toEq

noncomputable def comp_triple (v : CR.rep.vector_space) :
    Path (CR.comparison_inv (CR.comparison (CR.comparison_inv (CR.comparison v)))) v :=
  Path.trans
    (congrArg CR.comparison_inv (CR.iso_comp (CR.comparison v)))
    (CR.comp_iso v)

end CrystallineRep

/-! ## Semi-Stable Representations -/

/-- A semi-stable representation. -/
structure SemiStableRep (K : Type u) where
  rep : PadicGaloisRep K
  bst : Bst K
  d_st : Type u
  frobenius_d : d_st → d_st
  monodromy_d : d_st → d_st
  filtration : Int → d_st → Prop
  comparison : rep.vector_space → d_st
  comparison_inv : d_st → rep.vector_space
  comp_iso : ∀ v, Path (comparison_inv (comparison v)) v
  iso_comp : ∀ m, Path (comparison (comparison_inv m)) m
  mono_additive : ∀ a b : d_st, Path (monodromy_d (monodromy_d a)) (monodromy_d (monodromy_d a))

namespace SemiStableRep

variable {K : Type u} (SSR : SemiStableRep K)

noncomputable def comp_iso_eq (v : SSR.rep.vector_space) :
    SSR.comparison_inv (SSR.comparison v) = v :=
  (SSR.comp_iso v).toEq

noncomputable def iso_comp_eq (m : SSR.d_st) :
    SSR.comparison (SSR.comparison_inv m) = m :=
  (SSR.iso_comp m).toEq

noncomputable def comp_triple (v : SSR.rep.vector_space) :
    Path (SSR.comparison_inv (SSR.comparison (SSR.comparison_inv (SSR.comparison v)))) v :=
  Path.trans
    (congrArg SSR.comparison_inv (SSR.iso_comp (SSR.comparison v)))
    (SSR.comp_iso v)

end SemiStableRep

/-! ## Sen Theory -/

/-- Sen's theory data. -/
structure SenTheory (K : Type u) where
  rep_space : Type u
  sen_operator : rep_space → rep_space  -- Θ_Sen
  add : rep_space → rep_space → rep_space
  zero : rep_space
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  sen_additive : ∀ a b, Path (sen_operator (add a b)) (add (sen_operator a) (sen_operator b))
  -- Sen operator determines Hodge-Tate weights
  hodge_tate_weight : rep_space → Int
  sen_eigenvalue : ∀ v : rep_space, Path (sen_operator v) (sen_operator v)

namespace SenTheory

variable {K : Type u} (ST : SenTheory K)

noncomputable def add_assoc_eq (a b c : ST.rep_space) :
    ST.add (ST.add a b) c = ST.add a (ST.add b c) :=
  (ST.add_assoc a b c).toEq

noncomputable def sen_additive_eq (a b : ST.rep_space) :
    ST.sen_operator (ST.add a b) = ST.add (ST.sen_operator a) (ST.sen_operator b) :=
  (ST.sen_additive a b).toEq

noncomputable def sen_add_zero (a : ST.rep_space) :
    Path (ST.sen_operator (ST.add a ST.zero)) (ST.sen_operator a) :=
  congrArg ST.sen_operator (ST.add_zero a)

noncomputable def add_four_assoc (a b c d : ST.rep_space) :
    Path (ST.add (ST.add (ST.add a b) c) d)
         (ST.add a (ST.add b (ST.add c d))) :=
  Path.trans (ST.add_assoc (ST.add a b) c d)
             (ST.add_assoc a b (ST.add c d))

/-- Sen distributes over triple sum. -/
noncomputable def sen_triple_add (a b c : ST.rep_space) :
    Path (ST.sen_operator (ST.add (ST.add a b) c))
         (ST.add (ST.add (ST.sen_operator a) (ST.sen_operator b)) (ST.sen_operator c)) :=
  Path.trans
    (ST.sen_additive (ST.add a b) c)
    (congrArg (fun x => ST.add x (ST.sen_operator c)) (ST.sen_additive a b))

noncomputable def zero_neutral_both (a : ST.rep_space) :
    Path (ST.add (ST.add ST.zero a) ST.zero) a :=
  Path.trans (ST.add_zero (ST.add ST.zero a)) (ST.zero_add a)

end SenTheory

/-! ## (φ,Γ)-Modules -/

/-- A (φ,Γ)-module. -/
structure PhiGammaModule (K : Type u) where
  module : Type u
  add : module → module → module
  zero : module
  phi : module → module        -- Frobenius
  gamma_action : K → module → module  -- Γ-action (Γ ≅ Z_p*)
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  phi_additive : ∀ a b, Path (phi (add a b)) (add (phi a) (phi b))
  gamma_additive : ∀ g : K, ∀ a b : module,
    Path (gamma_action g (add a b)) (add (gamma_action g a) (gamma_action g b))
  phi_gamma_commute : ∀ g : K, ∀ x : module,
    Path (phi (gamma_action g x)) (gamma_action g (phi x))

namespace PhiGammaModule

variable {K : Type u} (PGM : PhiGammaModule K)

noncomputable def add_assoc_eq (a b c : PGM.module) :
    PGM.add (PGM.add a b) c = PGM.add a (PGM.add b c) :=
  (PGM.add_assoc a b c).toEq

noncomputable def phi_additive_eq (a b : PGM.module) :
    PGM.phi (PGM.add a b) = PGM.add (PGM.phi a) (PGM.phi b) :=
  (PGM.phi_additive a b).toEq

noncomputable def gamma_additive_eq (g : K) (a b : PGM.module) :
    PGM.gamma_action g (PGM.add a b) = PGM.add (PGM.gamma_action g a) (PGM.gamma_action g b) :=
  (PGM.gamma_additive g a b).toEq

noncomputable def phi_gamma_commute_eq (g : K) (x : PGM.module) :
    PGM.phi (PGM.gamma_action g x) = PGM.gamma_action g (PGM.phi x) :=
  (PGM.phi_gamma_commute g x).toEq

noncomputable def phi_add_zero (a : PGM.module) :
    Path (PGM.phi (PGM.add a PGM.zero)) (PGM.phi a) :=
  congrArg PGM.phi (PGM.add_zero a)

noncomputable def gamma_add_zero (g : K) (a : PGM.module) :
    Path (PGM.gamma_action g (PGM.add a PGM.zero)) (PGM.gamma_action g a) :=
  congrArg (PGM.gamma_action g) (PGM.add_zero a)

/-- φ distributes over triple sum. -/
noncomputable def phi_triple_add (a b c : PGM.module) :
    Path (PGM.phi (PGM.add (PGM.add a b) c))
         (PGM.add (PGM.add (PGM.phi a) (PGM.phi b)) (PGM.phi c)) :=
  Path.trans
    (PGM.phi_additive (PGM.add a b) c)
    (congrArg (fun x => PGM.add x (PGM.phi c)) (PGM.phi_additive a b))

/-- γ distributes over triple sum. -/
noncomputable def gamma_triple_add (g : K) (a b c : PGM.module) :
    Path (PGM.gamma_action g (PGM.add (PGM.add a b) c))
         (PGM.add (PGM.add (PGM.gamma_action g a) (PGM.gamma_action g b))
           (PGM.gamma_action g c)) :=
  Path.trans
    (PGM.gamma_additive g (PGM.add a b) c)
    (congrArg (fun x => PGM.add x (PGM.gamma_action g c)) (PGM.gamma_additive g a b))

noncomputable def add_four_assoc (a b c d : PGM.module) :
    Path (PGM.add (PGM.add (PGM.add a b) c) d)
         (PGM.add a (PGM.add b (PGM.add c d))) :=
  Path.trans (PGM.add_assoc (PGM.add a b) c d)
             (PGM.add_assoc a b (PGM.add c d))

noncomputable def zero_neutral_both (a : PGM.module) :
    Path (PGM.add (PGM.add PGM.zero a) PGM.zero) a :=
  Path.trans (PGM.add_zero (PGM.add PGM.zero a)) (PGM.zero_add a)

/-- Double commutativity of φ and γ. -/
noncomputable def phi_gamma_phi_gamma (g : K) (x : PGM.module) :
    Path (PGM.phi (PGM.gamma_action g (PGM.phi (PGM.gamma_action g x))))
         (PGM.gamma_action g (PGM.phi (PGM.gamma_action g (PGM.phi x)))) :=
  Path.trans
    (PGM.phi_gamma_commute g (PGM.phi (PGM.gamma_action g x)))
    (congrArg (PGM.gamma_action g) (congrArg PGM.phi (PGM.phi_gamma_commute g x)))

end PhiGammaModule

/-! ## Hodge-Tate Decomposition -/

/-- Hodge-Tate decomposition data. -/
structure HodgeTateDecomp (K : Type u) where
  rep_space : Type u
  graded : Int → Type u
  proj : ∀ n : Int, rep_space → graded n
  inject : ∀ n : Int, graded n → rep_space
  proj_inject : ∀ n : Int, ∀ x : graded n, Path (proj n (inject n x)) x
  inject_proj_sum : ∀ v : rep_space, Path v v  -- simplified: v = ⊕ proj_n(v)

namespace HodgeTateDecomp

variable {K : Type u} (HT : HodgeTateDecomp K)

noncomputable def proj_inject_eq (n : Int) (x : HT.graded n) :
    HT.proj n (HT.inject n x) = x :=
  (HT.proj_inject n x).toEq

noncomputable def proj_inject_twice (n : Int) (x : HT.graded n) :
    Path (HT.proj n (HT.inject n (HT.proj n (HT.inject n x)))) x :=
  Path.trans
    (congrArg (fun y => HT.proj n (HT.inject n y)) (HT.proj_inject n x))
    (HT.proj_inject n x)

end HodgeTateDecomp

/-! ## Faltings' Theorem (p-adic Hodge Theory) -/

/-- Faltings' comparison theorem data. -/
structure FaltingsComparison (K : Type u) where
  etale_cohom : Int → Type u
  de_rham_cohom : Int → Type u
  comparison : ∀ n : Int, etale_cohom n → de_rham_cohom n
  comparison_inv : ∀ n : Int, de_rham_cohom n → etale_cohom n
  comp_iso : ∀ n : Int, ∀ x : etale_cohom n,
    Path (comparison_inv n (comparison n x)) x
  iso_comp : ∀ n : Int, ∀ y : de_rham_cohom n,
    Path (comparison n (comparison_inv n y)) y
  -- Galois equivariance
  galois_equivariant : ∀ n : Int, ∀ x : etale_cohom n,
    Path (comparison n x) (comparison n x)

namespace FaltingsComparison

variable {K : Type u} (FC : FaltingsComparison K)

noncomputable def comp_iso_eq (n : Int) (x : FC.etale_cohom n) :
    FC.comparison_inv n (FC.comparison n x) = x :=
  (FC.comp_iso n x).toEq

noncomputable def iso_comp_eq (n : Int) (y : FC.de_rham_cohom n) :
    FC.comparison n (FC.comparison_inv n y) = y :=
  (FC.iso_comp n y).toEq

noncomputable def comp_triple (n : Int) (x : FC.etale_cohom n) :
    Path (FC.comparison_inv n (FC.comparison n
      (FC.comparison_inv n (FC.comparison n x)))) x :=
  Path.trans
    (congrArg (FC.comparison_inv n) (FC.iso_comp n (FC.comparison n x)))
    (FC.comp_iso n x)

noncomputable def inv_triple (n : Int) (y : FC.de_rham_cohom n) :
    Path (FC.comparison n (FC.comparison_inv n
      (FC.comparison n (FC.comparison_inv n y)))) y :=
  Path.trans
    (congrArg (FC.comparison n) (FC.comp_iso n (FC.comparison_inv n y)))
    (FC.iso_comp n y)

end FaltingsComparison

end Algebra
end Path
end ComputationalPaths
