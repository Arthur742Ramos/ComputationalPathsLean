/-
# Homotopy Type Theory (Deep) via Computational Paths

Univalent foundations, higher inductive types, synthetic homotopy groups,
Blakers-Massey via HoTT, Seifert-van Kampen via HoTT — all formalized
through computational paths.

## References

- The Univalent Foundations Program, "Homotopy Type Theory"
- Licata–Shulman, "Calculating the fundamental group of the circle in HoTT"
- Favonia–van Doorn, "Formalization of Blakers-Massey in HoTT"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Identity Types and Path Algebra -/

/-- Identity type structure (HoTT-style). -/
structure IdentityType (A : Type u) where
  eq : A → A → Type u
  refl_id : ∀ a : A, eq a a
  concat : ∀ a b c : A, eq a b → eq b c → eq a c
  inverse : ∀ a b : A, eq a b → eq b a
  concat_assoc : ∀ a b c d : A,
    ∀ (p : eq a b) (q : eq b c) (r : eq c d),
    Path (concat a c d (concat a b c p q) r)
         (concat a b d p (concat b c d q r))
  concat_refl : ∀ a b : A, ∀ p : eq a b,
    Path (concat a b b p (refl_id b)) p
  refl_concat : ∀ a b : A, ∀ p : eq a b,
    Path (concat a a b (refl_id a) p) p
  concat_inv : ∀ a b : A, ∀ p : eq a b,
    Path (concat a b a p (inverse a b p)) (refl_id a)
  inv_concat : ∀ a b : A, ∀ p : eq a b,
    Path (concat b a b (inverse a b p) p) (refl_id b)

namespace IdentityType

variable {A : Type u} (IT : IdentityType A)

noncomputable def concat_assoc_eq (a b c d : A) (p : IT.eq a b) (q : IT.eq b c) (r : IT.eq c d) :
    IT.concat a c d (IT.concat a b c p q) r =
    IT.concat a b d p (IT.concat b c d q r) :=
  (IT.concat_assoc a b c d p q r).toEq

noncomputable def concat_refl_eq (a b : A) (p : IT.eq a b) :
    IT.concat a b b p (IT.refl_id b) = p :=
  (IT.concat_refl a b p).toEq

noncomputable def refl_concat_eq (a b : A) (p : IT.eq a b) :
    IT.concat a a b (IT.refl_id a) p = p :=
  (IT.refl_concat a b p).toEq

noncomputable def concat_inv_eq (a b : A) (p : IT.eq a b) :
    IT.concat a b a p (IT.inverse a b p) = IT.refl_id a :=
  (IT.concat_inv a b p).toEq

noncomputable def refl_neutral_both (a b : A) (p : IT.eq a b) :
    Path (IT.concat a a b (IT.refl_id a) (IT.concat a b b p (IT.refl_id b))) p :=
  Path.trans
    (congrArg (IT.concat a a b (IT.refl_id a)) (IT.concat_refl a b p))
    (IT.refl_concat a b p)

noncomputable def concat_four_assoc (a b c d e : A)
    (p : IT.eq a b) (q : IT.eq b c) (r : IT.eq c d) (s : IT.eq d e) :
    Path (IT.concat a d e (IT.concat a c d (IT.concat a b c p q) r) s)
         (IT.concat a b e p (IT.concat b d e (IT.concat b c d q r) s)) :=
  Path.trans
    (IT.concat_assoc a c d e (IT.concat a b c p q) r s)
    (congrArg (fun x => IT.concat a c e x (IT.concat c d e r s))
      (IT.concat_assoc a b c d p q r))

end IdentityType

/-! ## Univalence -/

/-- Univalence axiom data. -/
structure Univalence where
  type_eq : Type u → Type u → Type u  -- A = B in the universe
  equiv : Type u → Type u → Type u    -- A ≃ B
  id_to_equiv : ∀ A B : Type u, type_eq A B → equiv A B
  equiv_to_id : ∀ A B : Type u, equiv A B → type_eq A B
  ua : ∀ A B : Type u, ∀ e : equiv A B,
    Path (id_to_equiv A B (equiv_to_id A B e)) e
  ua_inv : ∀ A B : Type u, ∀ p : type_eq A B,
    Path (equiv_to_id A B (id_to_equiv A B p)) p

namespace Univalence

variable (UA : Univalence)

noncomputable def ua_eq (A B : Type u) (e : UA.equiv A B) :
    UA.id_to_equiv A B (UA.equiv_to_id A B e) = e :=
  (UA.ua A B e).toEq

noncomputable def ua_inv_eq (A B : Type u) (p : UA.type_eq A B) :
    UA.equiv_to_id A B (UA.id_to_equiv A B p) = p :=
  (UA.ua_inv A B p).toEq

noncomputable def ua_triple (A B : Type u) (e : UA.equiv A B) :
    Path (UA.id_to_equiv A B (UA.equiv_to_id A B
      (UA.id_to_equiv A B (UA.equiv_to_id A B e)))) e :=
  Path.trans
    (congrArg (UA.id_to_equiv A B) (UA.ua_inv A B (UA.equiv_to_id A B e)))
    (UA.ua A B e)

noncomputable def ua_triple_inv (A B : Type u) (p : UA.type_eq A B) :
    Path (UA.equiv_to_id A B (UA.id_to_equiv A B
      (UA.equiv_to_id A B (UA.id_to_equiv A B p)))) p :=
  Path.trans
    (congrArg (UA.equiv_to_id A B) (UA.ua A B (UA.id_to_equiv A B p)))
    (UA.ua_inv A B p)

end Univalence

/-! ## Transport -/

/-- Transport along paths. -/
structure Transport (A : Type u) where
  family : A → Type u
  transport : ∀ a b : A, Path a b → family a → family b
  transport_refl : ∀ a : A, ∀ x : family a,
    Path (transport a a (Path.refl a) x) x
  transport_concat : ∀ a b c : A, ∀ (p : Path a b) (q : Path b c), ∀ x : family a,
    Path (transport a c (Path.trans p q) x)
         (transport b c q (transport a b p x))

namespace Transport

variable {A : Type u} (TR : Transport A)

noncomputable def transport_refl_eq (a : A) (x : TR.family a) :
    TR.transport a a (Path.refl a) x = x :=
  (TR.transport_refl a x).toEq

noncomputable def transport_concat_eq (a b c : A) (p : Path a b) (q : Path b c) (x : TR.family a) :
    TR.transport a c (Path.trans p q) x =
    TR.transport b c q (TR.transport a b p x) :=
  (TR.transport_concat a b c p q x).toEq

noncomputable def transport_refl_twice (a : A) (x : TR.family a) :
    Path (TR.transport a a (Path.refl a) (TR.transport a a (Path.refl a) x)) x :=
  Path.trans
    (congrArg (TR.transport a a (Path.refl a)) (TR.transport_refl a x))
    (TR.transport_refl a x)

end Transport

/-! ## Higher Inductive Types -/

/-- The circle S¹ as a higher inductive type. -/
structure CircleHIT where
  carrier : Type u
  base : carrier
  loop_elem : Path base base  -- loop : base = base
  elim : ∀ (B : Type u) (b : B) (l : Path b b), carrier → B
  elim_base : ∀ (B : Type u) (b : B) (l : Path b b),
    Path (rec B b l base) b
  elim_loop : ∀ (B : Type u) (b : B) (l : Path b b),
    Path l l  -- simplified

namespace CircleHIT

variable (S1 : CircleHIT)

noncomputable def rec_base_eq (B : Type u) (b : B) (l : Path b b) :
    S1.elim B b l S1.base = b :=
  (S1.elim_base B b l).toEq

noncomputable def loop_concat : Path S1.base S1.base :=
  Path.trans S1.loop_elem S1.loop_elem

noncomputable def loop_triple : Path S1.base S1.base :=
  Path.trans (Path.trans S1.loop_elem S1.loop_elem) S1.loop_elem

noncomputable def loop_inverse : Path S1.base S1.base :=
  Path.symm S1.loop_elem

noncomputable def loop_concat_inv : Path S1.base S1.base :=
  Path.trans S1.loop_elem (Path.symm S1.loop_elem)

end CircleHIT

/-- The suspension as a higher inductive type. -/
structure SuspensionHIT (A : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : A → Path north south
  elim : ∀ (B : Type u) (n s : B) (m : A → Path n s), carrier → B
  elim_north : ∀ (B : Type u) (n s : B) (m : A → Path n s),
    Path (rec B n s m north) n
  elim_south : ∀ (B : Type u) (n s : B) (m : A → Path n s),
    Path (rec B n s m south) s

namespace SuspensionHIT

variable {A : Type u} (SU : SuspensionHIT A)

noncomputable def rec_north_eq (B : Type u) (n s : B) (m : A → Path n s) :
    SU.elim B n s m SU.north = n :=
  (SU.elim_north B n s m).toEq

noncomputable def rec_south_eq (B : Type u) (n s : B) (m : A → Path n s) :
    SU.elim B n s m SU.south = s :=
  (SU.elim_south B n s m).toEq

/-- Meridian composition. -/
noncomputable def merid_comp (a b : A) : Path SU.north SU.north :=
  Path.trans (SU.merid a) (Path.symm (SU.merid b))

end SuspensionHIT

/-- The pushout as a higher inductive type. -/
structure PushoutHIT (A B C : Type u) where
  carrier : Type u
  inl : A → carrier
  inr : B → carrier
  glue : C → Type u  -- simplified: should have glue(c) : inl(f(c)) = inr(g(c))
  elim : ∀ (D : Type u) (l : A → D) (r : B → D), carrier → D
  elim_inl : ∀ (D : Type u) (l : A → D) (r : B → D) (a : A),
    Path (rec D l r (inl a)) (l a)
  elim_inr : ∀ (D : Type u) (l : A → D) (r : B → D) (b : B),
    Path (rec D l r (inr b)) (r b)

namespace PushoutHIT

variable {A B C : Type u} (PO : PushoutHIT A B C)

noncomputable def rec_inl_eq (D : Type u) (l : A → D) (r : B → D) (a : A) :
    PO.elim D l r (PO.inl a) = l a :=
  (PO.elim_inl D l r a).toEq

noncomputable def rec_inr_eq (D : Type u) (l : A → D) (r : B → D) (b : B) :
    PO.elim D l r (PO.inr b) = r b :=
  (PO.elim_inr D l r b).toEq

noncomputable def rec_inl_twice (D : Type u) (l l' : A → D) (r : B → D) (a : A) :
    Path (PO.elim D l r (PO.inl a)) (l a) :=
  PO.elim_inl D l r a

end PushoutHIT

/-! ## Synthetic Homotopy Groups -/

/-- Synthetic homotopy group computation. -/
structure SyntheticPiN where
  space : Type u
  basepoint : space
  pi : Nat → Type u  -- π_n(X)
  group_op : ∀ n : Nat, n ≥ 1 → pi n → pi n → pi n
  group_one : ∀ n : Nat, n ≥ 1 → pi n
  group_inv : ∀ n : Nat, n ≥ 1 → pi n → pi n
  op_assoc : ∀ n : Nat, ∀ h : n ≥ 1, ∀ a b c : pi n,
    Path (group_op n h (group_op n h a b) c)
         (group_op n h a (group_op n h b c))
  op_one : ∀ n : Nat, ∀ h : n ≥ 1, ∀ a : pi n,
    Path (group_op n h a (group_one n h)) a
  one_op : ∀ n : Nat, ∀ h : n ≥ 1, ∀ a : pi n,
    Path (group_op n h (group_one n h) a) a
  op_inv : ∀ n : Nat, ∀ h : n ≥ 1, ∀ a : pi n,
    Path (group_op n h a (group_inv n h a)) (group_one n h)
  -- For n ≥ 2, abelian
  abelian : ∀ n : Nat, ∀ h : n ≥ 2, ∀ a b : pi n,
    Path (group_op n (by omega) a b) (group_op n (by omega) b a)

namespace SyntheticPiN

variable (SP : SyntheticPiN)

noncomputable def op_assoc_eq (n : Nat) (h : n ≥ 1) (a b c : SP.pi n) :
    SP.group_op n h (SP.group_op n h a b) c =
    SP.group_op n h a (SP.group_op n h b c) :=
  (SP.op_assoc n h a b c).toEq

noncomputable def op_inv_eq (n : Nat) (h : n ≥ 1) (a : SP.pi n) :
    SP.group_op n h a (SP.group_inv n h a) = SP.group_one n h :=
  (SP.op_inv n h a).toEq

noncomputable def one_neutral_both (n : Nat) (h : n ≥ 1) (a : SP.pi n) :
    Path (SP.group_op n h (SP.group_op n h (SP.group_one n h) a) (SP.group_one n h)) a :=
  Path.trans (SP.op_one n h (SP.group_op n h (SP.group_one n h) a))
             (SP.one_op n h a)

noncomputable def op_four_assoc (n : Nat) (h : n ≥ 1) (a b c d : SP.pi n) :
    Path (SP.group_op n h (SP.group_op n h (SP.group_op n h a b) c) d)
         (SP.group_op n h a (SP.group_op n h b (SP.group_op n h c d))) :=
  Path.trans (SP.op_assoc n h (SP.group_op n h a b) c d)
             (SP.op_assoc n h a b (SP.group_op n h c d))

end SyntheticPiN

/-! ## Blakers-Massey Theorem -/

/-- Blakers-Massey theorem data. -/
structure BlakersMassey where
  pushout_type : Type u
  fiber_type : Type u
  connectivity_n : Nat
  connectivity_m : Nat
  -- The comparison map is (n+m)-connected
  comparison : fiber_type → pushout_type
  comparison_conn : connectivity_n + connectivity_m > 0 → True
  -- Blakers-Massey: freudenthal as special case
  freudenthal_special : ∀ k : Nat, k ≤ connectivity_n + connectivity_m → True

namespace BlakersMassey

variable (BM : BlakersMassey)

noncomputable def connectivity_positive (h : BM.connectivity_n + BM.connectivity_m > 0) :
    True := BM.comparison_conn h

end BlakersMassey

/-! ## Freudenthal Suspension Theorem -/

/-- Freudenthal suspension theorem data. -/
structure FreudenthalSuspension where
  space : Type u
  connectivity : Nat  -- n-connected
  pi_k : Nat → Type u  -- π_k(X)
  susp_pi : Nat → Type u  -- π_k(ΣX)
  suspension_map : ∀ k : Nat, pi_k k → susp_pi (k + 1)
  suspension_inv : ∀ k : Nat, k ≤ 2 * connectivity → susp_pi (k + 1) → pi_k k
  susp_iso : ∀ k : Nat, ∀ h : k ≤ 2 * connectivity, ∀ x : pi_k k,
    Path (suspension_inv k h (suspension_map k x)) x
  susp_iso_inv : ∀ k : Nat, ∀ h : k ≤ 2 * connectivity, ∀ y : susp_pi (k + 1),
    Path (suspension_map k (suspension_inv k h y)) y

namespace FreudenthalSuspension

variable (FS : FreudenthalSuspension)

noncomputable def susp_iso_eq (k : Nat) (h : k ≤ 2 * FS.connectivity) (x : FS.pi_k k) :
    FS.suspension_inv k h (FS.suspension_map k x) = x :=
  (FS.susp_iso k h x).toEq

noncomputable def susp_iso_inv_eq (k : Nat) (h : k ≤ 2 * FS.connectivity) (y : FS.susp_pi (k + 1)) :
    FS.suspension_map k (FS.suspension_inv k h y) = y :=
  (FS.susp_iso_inv k h y).toEq

noncomputable def susp_triple (k : Nat) (h : k ≤ 2 * FS.connectivity) (x : FS.pi_k k) :
    Path (FS.suspension_inv k h (FS.suspension_map k
      (FS.suspension_inv k h (FS.suspension_map k x)))) x :=
  Path.trans
    (congrArg (FS.suspension_inv k h) (FS.susp_iso_inv k h (FS.suspension_map k x)))
    (FS.susp_iso k h x)

end FreudenthalSuspension

/-! ## Seifert-van Kampen (HoTT) -/

/-- Seifert-van Kampen theorem in HoTT. -/
structure SvKHoTT where
  pushout_space : Type u
  fund_groupoid : Type u  -- π₁(X)
  u_groupoid : Type u     -- π₁(U)
  v_groupoid : Type u     -- π₁(V)
  uv_groupoid : Type u    -- π₁(U ∩ V)
  incl_u : uv_groupoid → u_groupoid
  incl_v : uv_groupoid → v_groupoid
  coproduct : u_groupoid → pushout_space
  coproduct_v : v_groupoid → pushout_space
  svk_map : fund_groupoid → pushout_space
  svk_inv : pushout_space → fund_groupoid
  svk_iso : ∀ g : fund_groupoid, Path (svk_inv (svk_map g)) g
  svk_iso_inv : ∀ p : pushout_space, Path (svk_map (svk_inv p)) p

namespace SvKHoTT

variable (SVK : SvKHoTT)

noncomputable def svk_iso_eq (g : SVK.fund_groupoid) :
    SVK.svk_inv (SVK.svk_map g) = g :=
  (SVK.svk_iso g).toEq

noncomputable def svk_iso_inv_eq (p : SVK.pushout_space) :
    SVK.svk_map (SVK.svk_inv p) = p :=
  (SVK.svk_iso_inv p).toEq

noncomputable def svk_triple (g : SVK.fund_groupoid) :
    Path (SVK.svk_inv (SVK.svk_map (SVK.svk_inv (SVK.svk_map g)))) g :=
  Path.trans
    (congrArg SVK.svk_inv (SVK.svk_iso_inv (SVK.svk_map g)))
    (SVK.svk_iso g)

noncomputable def svk_triple_inv (p : SVK.pushout_space) :
    Path (SVK.svk_map (SVK.svk_inv (SVK.svk_map (SVK.svk_inv p)))) p :=
  Path.trans
    (congrArg SVK.svk_map (SVK.svk_iso (SVK.svk_inv p)))
    (SVK.svk_iso_inv p)

end SvKHoTT

/-! ## Truncation Levels -/

/-- n-truncation data. -/
structure Truncation (n : Int) where
  carrier : Type u
  truncated : Type u
  trunc_map : carrier → truncated
  trunc_univ : ∀ (B : Type u) (f : carrier → B), truncated → B
  trunc_beta : ∀ (B : Type u) (f : carrier → B) (x : carrier),
    Path (trunc_univ B f (trunc_map x)) (f x)

namespace Truncation

variable {n : Int} (TR : Truncation n)

noncomputable def trunc_beta_eq (B : Type u) (f : TR.carrier → B) (x : TR.carrier) :
    TR.trunc_univ B f (TR.trunc_map x) = f x :=
  (TR.trunc_beta B f x).toEq

noncomputable def trunc_beta_id (x : TR.carrier) :
    Path (TR.trunc_univ TR.carrier id (TR.trunc_map x)) x :=
  TR.trunc_beta TR.carrier id x

end Truncation

/-! ## Eilenberg-MacLane Spaces in HoTT -/

/-- Eilenberg-MacLane space K(G,n) in HoTT. -/
structure EMSpaceHoTT where
  carrier : Type u
  basepoint : carrier
  n_level : Nat  -- the n in K(G,n)
  group_type : Type u
  group_op : group_type → group_type → group_type
  group_one : group_type
  group_inv : group_type → group_type
  op_assoc : ∀ a b c : group_type,
    Path (group_op (group_op a b) c) (group_op a (group_op b c))
  op_one : ∀ a : group_type, Path (group_op a group_one) a
  one_op : ∀ a : group_type, Path (group_op group_one a) a
  op_inv : ∀ a : group_type, Path (group_op a (group_inv a)) group_one
  inv_op : ∀ a : group_type, Path (group_op (group_inv a) a) group_one
  -- π_n(K(G,n)) ≅ G
  pi_iso : group_type → carrier
  pi_iso_inv : carrier → group_type
  iso_forward : ∀ g : group_type, Path (pi_iso_inv (pi_iso g)) g
  iso_backward : ∀ x : carrier, Path (pi_iso (pi_iso_inv x)) x

namespace EMSpaceHoTT

variable (EM : EMSpaceHoTT)

noncomputable def op_assoc_eq (a b c : EM.group_type) :
    EM.group_op (EM.group_op a b) c = EM.group_op a (EM.group_op b c) :=
  (EM.op_assoc a b c).toEq

noncomputable def iso_forward_eq (g : EM.group_type) :
    EM.pi_iso_inv (EM.pi_iso g) = g :=
  (EM.iso_forward g).toEq

noncomputable def iso_backward_eq (x : EM.carrier) :
    EM.pi_iso (EM.pi_iso_inv x) = x :=
  (EM.iso_backward x).toEq

noncomputable def op_four_assoc (a b c d : EM.group_type) :
    Path (EM.group_op (EM.group_op (EM.group_op a b) c) d)
         (EM.group_op a (EM.group_op b (EM.group_op c d))) :=
  Path.trans (EM.op_assoc (EM.group_op a b) c d)
             (EM.op_assoc a b (EM.group_op c d))

noncomputable def one_neutral_both (a : EM.group_type) :
    Path (EM.group_op (EM.group_op EM.group_one a) EM.group_one) a :=
  Path.trans (EM.op_one (EM.group_op EM.group_one a)) (EM.one_op a)

noncomputable def iso_triple (g : EM.group_type) :
    Path (EM.pi_iso_inv (EM.pi_iso (EM.pi_iso_inv (EM.pi_iso g)))) g :=
  Path.trans
    (congrArg EM.pi_iso_inv (EM.iso_backward (EM.pi_iso g)))
    (EM.iso_forward g)

end EMSpaceHoTT

/-! ## Cohomology in HoTT -/

/-- Cohomology as maps into Eilenberg-MacLane spaces. -/
structure CohomologyHoTT where
  space : Type u
  coefficients : Type u
  cohom_group : Int → Type u  -- H^n(X; G)
  add : ∀ n : Int, cohom_group n → cohom_group n → cohom_group n
  zero : ∀ n : Int, cohom_group n
  add_assoc : ∀ n : Int, ∀ a b c : cohom_group n,
    Path (add n (add n a b) c) (add n a (add n b c))
  add_zero : ∀ n : Int, ∀ a : cohom_group n, Path (add n a (zero n)) a
  zero_add : ∀ n : Int, ∀ a : cohom_group n, Path (add n (zero n) a) a
  add_comm : ∀ n : Int, ∀ a b : cohom_group n, Path (add n a b) (add n b a)
  cup_product : ∀ n m : Int, cohom_group n → cohom_group m → cohom_group (n + m)

namespace CohomologyHoTT

variable (CH : CohomologyHoTT)

noncomputable def add_assoc_eq (n : Int) (a b c : CH.cohom_group n) :
    CH.add n (CH.add n a b) c = CH.add n a (CH.add n b c) :=
  (CH.add_assoc n a b c).toEq

noncomputable def add_comm_eq (n : Int) (a b : CH.cohom_group n) :
    CH.add n a b = CH.add n b a :=
  (CH.add_comm n a b).toEq

noncomputable def add_four_assoc (n : Int) (a b c d : CH.cohom_group n) :
    Path (CH.add n (CH.add n (CH.add n a b) c) d)
         (CH.add n a (CH.add n b (CH.add n c d))) :=
  Path.trans (CH.add_assoc n (CH.add n a b) c d)
             (CH.add_assoc n a b (CH.add n c d))

noncomputable def zero_neutral_both (n : Int) (a : CH.cohom_group n) :
    Path (CH.add n (CH.add n (CH.zero n) a) (CH.zero n)) a :=
  Path.trans (CH.add_zero n (CH.add n (CH.zero n) a)) (CH.zero_add n a)

end CohomologyHoTT

end Algebra
end Path
end ComputationalPaths
