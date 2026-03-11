/-
# Categorified Knot Invariants via Computational Paths

Categorification of knot invariants, Khovanov-Rozansky homology,
HOMFLY-PT categorification, foam categories, Webster's tensor product algebras.

## References

- Khovanov, "A categorification of the Jones polynomial"
- Khovanov-Rozansky, "Matrix factorizations and link homology"
- Webster, "Knot invariants and higher representation theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Chain Complexes for Knot Homology -/

/-- A chain complex for knot homology. -/
structure KnotChainComplex (C : Type u) where
  add : C → C → C
  zero : C
  neg : C → C
  diff : C → C
  grade : C → Int
  d_squared : ∀ (c : C), Path (diff (diff c)) zero
  diff_grade : ∀ (c : C), Path (grade (diff c)) (grade c + 1)
  add_assoc : ∀ (a b c : C), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : C), Path (add a b) (add b a)
  add_zero : ∀ (a : C), Path (add a zero) a
  neg_add : ∀ (a : C), Path (add (neg a) a) zero

namespace KnotChainComplex

variable {C : Type u} (KC : KnotChainComplex C)

theorem d_squared_eq (c : C) : KC.diff (KC.diff c) = KC.zero := (KC.d_squared c).toEq
theorem add_assoc_eq (a b c : C) : KC.add (KC.add a b) c = KC.add a (KC.add b c) := (KC.add_assoc a b c).toEq
theorem add_comm_eq (a b : C) : KC.add a b = KC.add b a := (KC.add_comm a b).toEq
theorem add_zero_eq (a : C) : KC.add a KC.zero = a := (KC.add_zero a).toEq
theorem neg_add_eq (a : C) : KC.add (KC.neg a) a = KC.zero := (KC.neg_add a).toEq

/-- d³ = 0. -/
noncomputable def d_cubed (c : C) : Path (KC.diff (KC.diff (KC.diff c))) KC.zero :=
  KC.d_squared (KC.diff c)

theorem d_cubed_eq (c : C) : KC.diff (KC.diff (KC.diff c)) = KC.zero := (KC.d_cubed c).toEq

/-- Add zero twice. -/
noncomputable def add_zero_zero (a : C) : Path (KC.add (KC.add a KC.zero) KC.zero) a :=
  Path.trans (KC.add_zero (KC.add a KC.zero)) (KC.add_zero a)

theorem add_zero_zero_eq (a : C) : KC.add (KC.add a KC.zero) KC.zero = a := (KC.add_zero_zero a).toEq

end KnotChainComplex

/-! ## Khovanov Homology -/

/-- Khovanov bracket data: cube of resolutions. -/
structure KhovanovBracket (V : Type u) where
  complex : KnotChainComplex V
  merge : V → V → V  -- merge map (m)
  split : V → V → V  -- comultiplication (Δ)
  unit : V
  counit : V → V
  merge_assoc : ∀ (a b c : V), Path (merge (merge a b) c) (merge a (merge b c))
  merge_comm : ∀ (a b : V), Path (merge a b) (merge b a)
  merge_unit : ∀ (a : V), Path (merge a unit) a
  frobenius : ∀ (a b : V),
    Path (split (merge a b) unit) (merge a (split b unit))

namespace KhovanovBracket

variable {V : Type u} (KB : KhovanovBracket V)

theorem merge_assoc_eq (a b c : V) : KB.merge (KB.merge a b) c = KB.merge a (KB.merge b c) :=
  (KB.merge_assoc a b c).toEq
theorem merge_comm_eq (a b : V) : KB.merge a b = KB.merge b a := (KB.merge_comm a b).toEq
theorem merge_unit_eq (a : V) : KB.merge a KB.unit = a := (KB.merge_unit a).toEq

/-- Triple merge assoc. -/
noncomputable def triple_merge (a b c d : V) :
    Path (KB.merge (KB.merge (KB.merge a b) c) d) (KB.merge a (KB.merge b (KB.merge c d))) :=
  Path.trans (KB.merge_assoc (KB.merge a b) c d) (KB.merge_assoc a b (KB.merge c d))

theorem triple_merge_eq (a b c d : V) :
    KB.merge (KB.merge (KB.merge a b) c) d = KB.merge a (KB.merge b (KB.merge c d)) :=
  (KB.triple_merge a b c d).toEq

/-- Unit absorbed on both sides. -/
noncomputable def unit_merge_unit (a : V) :
    Path (KB.merge KB.unit (KB.merge a KB.unit)) a :=
  Path.trans (Path.trans (KB.merge_comm KB.unit (KB.merge a KB.unit))
    (KB.merge_assoc a KB.unit KB.unit |>.trans (Path.rfl _) |> fun _ =>
      congrArg (KB.merge KB.unit) (KB.merge_unit a)))
    (KB.merge_comm KB.unit a |>.trans (KB.merge_unit a))

theorem unit_merge_unit_eq (a : V) : KB.merge KB.unit (KB.merge a KB.unit) = a :=
  (KB.unit_merge_unit a).toEq

end KhovanovBracket

/-! ## Khovanov-Rozansky Homology -/

/-- Khovanov-Rozansky sl(n) homology. -/
structure KhovanovRozansky (n : Nat) (V : Type u) where
  complex : KnotChainComplex V
  potentialW : V → V  -- the potential W(x) = x^{n+1}
  matrixFact : V → V → V  -- matrix factorization
  mf_compose : V → V → V → V
  diff0 : V → V
  diff1 : V → V
  d0_d1 : ∀ (v : V), Path (diff0 (diff1 v)) v  -- d₀∘d₁ = W·id (simplified)
  d1_d0 : ∀ (v : V), Path (diff1 (diff0 v)) v

namespace KhovanovRozansky

variable {n : Nat} {V : Type u} (KR : KhovanovRozansky n V)

theorem d0_d1_eq (v : V) : KR.diff0 (KR.diff1 v) = v := (KR.d0_d1 v).toEq
theorem d1_d0_eq (v : V) : KR.diff1 (KR.diff0 v) = v := (KR.d1_d0 v).toEq

/-- Double d0∘d1 is identity. -/
noncomputable def double_d0_d1 (v : V) :
    Path (KR.diff0 (KR.diff1 (KR.diff0 (KR.diff1 v)))) v :=
  Path.trans (congrArg KR.diff0 (congrArg KR.diff1 (KR.d0_d1 v))) (KR.d0_d1 v)

theorem double_d0_d1_eq (v : V) : KR.diff0 (KR.diff1 (KR.diff0 (KR.diff1 v))) = v :=
  (KR.double_d0_d1 v).toEq

/-- Double d1∘d0 is identity. -/
noncomputable def double_d1_d0 (v : V) :
    Path (KR.diff1 (KR.diff0 (KR.diff1 (KR.diff0 v)))) v :=
  Path.trans (congrArg KR.diff1 (congrArg KR.diff0 (KR.d1_d0 v))) (KR.d1_d0 v)

theorem double_d1_d0_eq (v : V) : KR.diff1 (KR.diff0 (KR.diff1 (KR.diff0 v))) = v :=
  (KR.double_d1_d0 v).toEq

end KhovanovRozansky

/-! ## HOMFLY-PT Categorification -/

/-- HOMFLY-PT polynomial categorification data. -/
structure HOMFLYPTCat (H : Type u) where
  add : H → H → H
  mul : H → H → H
  zero : H
  one : H
  qshift : H → H  -- q-grading shift
  tshift : H → H  -- t-grading shift
  qshift_inv : H → H
  tshift_inv : H → H
  q_roundtrip : ∀ (h : H), Path (qshift (qshift_inv h)) h
  q_inv_roundtrip : ∀ (h : H), Path (qshift_inv (qshift h)) h
  t_roundtrip : ∀ (h : H), Path (tshift (tshift_inv h)) h
  t_inv_roundtrip : ∀ (h : H), Path (tshift_inv (tshift h)) h
  mul_assoc : ∀ (a b c : H), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : H), Path (mul a one) a
  one_mul : ∀ (a : H), Path (mul one a) a
  add_assoc : ∀ (a b c : H), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : H), Path (add a b) (add b a)
  add_zero : ∀ (a : H), Path (add a zero) a
  skein : ∀ (a : H), Path (add (qshift a) (qshift_inv a)) (add a a)  -- simplified skein

namespace HOMFLYPTCat

variable {H : Type u} (HP : HOMFLYPTCat H)

theorem q_roundtrip_eq (h : H) : HP.qshift (HP.qshift_inv h) = h := (HP.q_roundtrip h).toEq
theorem q_inv_roundtrip_eq (h : H) : HP.qshift_inv (HP.qshift h) = h := (HP.q_inv_roundtrip h).toEq
theorem t_roundtrip_eq (h : H) : HP.tshift (HP.tshift_inv h) = h := (HP.t_roundtrip h).toEq
theorem t_inv_roundtrip_eq (h : H) : HP.tshift_inv (HP.tshift h) = h := (HP.t_inv_roundtrip h).toEq
theorem mul_assoc_eq (a b c : H) : HP.mul (HP.mul a b) c = HP.mul a (HP.mul b c) := (HP.mul_assoc a b c).toEq
theorem mul_one_eq (a : H) : HP.mul a HP.one = a := (HP.mul_one a).toEq
theorem one_mul_eq (a : H) : HP.mul HP.one a = a := (HP.one_mul a).toEq
theorem add_assoc_eq (a b c : H) : HP.add (HP.add a b) c = HP.add a (HP.add b c) := (HP.add_assoc a b c).toEq
theorem add_comm_eq (a b : H) : HP.add a b = HP.add b a := (HP.add_comm a b).toEq
theorem add_zero_eq (a : H) : HP.add a HP.zero = a := (HP.add_zero a).toEq

/-- Double q-shift roundtrip. -/
noncomputable def double_q (h : H) :
    Path (HP.qshift (HP.qshift_inv (HP.qshift (HP.qshift_inv h)))) h :=
  Path.trans (congrArg HP.qshift (congrArg HP.qshift_inv (HP.q_roundtrip h))) (HP.q_roundtrip h)

theorem double_q_eq (h : H) : HP.qshift (HP.qshift_inv (HP.qshift (HP.qshift_inv h))) = h :=
  (HP.double_q h).toEq

/-- Triple mul. -/
noncomputable def triple_mul (a b c d : H) :
    Path (HP.mul (HP.mul (HP.mul a b) c) d) (HP.mul a (HP.mul b (HP.mul c d))) :=
  Path.trans (HP.mul_assoc (HP.mul a b) c d) (HP.mul_assoc a b (HP.mul c d))

theorem triple_mul_eq (a b c d : H) :
    HP.mul (HP.mul (HP.mul a b) c) d = HP.mul a (HP.mul b (HP.mul c d)) := (HP.triple_mul a b c d).toEq

end HOMFLYPTCat

/-! ## Foam Categories -/

/-- Foam category for sl(n) link homology. -/
structure FoamCategory (Foam : Type u) (Web : Type v) where
  compose : Foam → Foam → Foam
  identity : Web → Foam
  tensor : Foam → Foam → Foam
  src : Foam → Web
  tgt : Foam → Web
  comp_assoc : ∀ (f g h : Foam), Path (compose (compose f g) h) (compose f (compose g h))
  id_comp : ∀ (f : Foam), Path (compose (identity (src f)) f) f
  comp_id : ∀ (f : Foam), Path (compose f (identity (tgt f))) f
  tensor_assoc : ∀ (f g h : Foam), Path (tensor (tensor f g) h) (tensor f (tensor g h))

namespace FoamCategory

variable {Foam : Type u} {Web : Type v} (FC : FoamCategory Foam Web)

theorem comp_assoc_eq (f g h : Foam) : FC.compose (FC.compose f g) h = FC.compose f (FC.compose g h) :=
  (FC.comp_assoc f g h).toEq
theorem id_comp_eq (f : Foam) : FC.compose (FC.identity (FC.src f)) f = f := (FC.id_comp f).toEq
theorem comp_id_eq (f : Foam) : FC.compose f (FC.identity (FC.tgt f)) = f := (FC.comp_id f).toEq
theorem tensor_assoc_eq (f g h : Foam) : FC.tensor (FC.tensor f g) h = FC.tensor f (FC.tensor g h) :=
  (FC.tensor_assoc f g h).toEq

/-- Triple comp. -/
noncomputable def triple_comp (f g h k : Foam) :
    Path (FC.compose (FC.compose (FC.compose f g) h) k) (FC.compose f (FC.compose g (FC.compose h k))) :=
  Path.trans (FC.comp_assoc (FC.compose f g) h k) (FC.comp_assoc f g (FC.compose h k))

theorem triple_comp_eq (f g h k : Foam) :
    FC.compose (FC.compose (FC.compose f g) h) k = FC.compose f (FC.compose g (FC.compose h k)) :=
  (FC.triple_comp f g h k).toEq

/-- Triple tensor. -/
noncomputable def triple_tensor (f g h k : Foam) :
    Path (FC.tensor (FC.tensor (FC.tensor f g) h) k) (FC.tensor f (FC.tensor g (FC.tensor h k))) :=
  Path.trans (FC.tensor_assoc (FC.tensor f g) h k) (FC.tensor_assoc f g (FC.tensor h k))

theorem triple_tensor_eq (f g h k : Foam) :
    FC.tensor (FC.tensor (FC.tensor f g) h) k = FC.tensor f (FC.tensor g (FC.tensor h k)) :=
  (FC.triple_tensor f g h k).toEq

/-- Id absorb left. -/
noncomputable def id_absorb_left (f g : Foam) :
    Path (FC.compose (FC.compose (FC.identity (FC.src f)) f) g) (FC.compose f g) :=
  congrArg (fun z => FC.compose z g) (FC.id_comp f)

theorem id_absorb_left_eq (f g : Foam) :
    FC.compose (FC.compose (FC.identity (FC.src f)) f) g = FC.compose f g :=
  (FC.id_absorb_left f g).toEq

end FoamCategory

/-! ## Webster's Tensor Product Algebras -/

/-- Webster's tensor product algebra for categorified quantum groups. -/
structure WebsterAlgebra (A : Type u) where
  mul : A → A → A
  add : A → A → A
  zero : A
  one : A
  idempotent : Nat → A  -- e_i
  crossing : Nat → Nat → A  -- crossing generators
  mul_assoc : ∀ (a b c : A), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : A), Path (mul a one) a
  one_mul : ∀ (a : A), Path (mul one a) a
  add_assoc : ∀ (a b c : A), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : A), Path (add a b) (add b a)
  add_zero : ∀ (a : A), Path (add a zero) a
  idemp_sq : ∀ (i : Nat), Path (mul (idempotent i) (idempotent i)) (idempotent i)
  left_distrib : ∀ (a b c : A), Path (mul a (add b c)) (add (mul a b) (mul a c))

namespace WebsterAlgebra

variable {A : Type u} (WA : WebsterAlgebra A)

theorem mul_assoc_eq (a b c : A) : WA.mul (WA.mul a b) c = WA.mul a (WA.mul b c) := (WA.mul_assoc a b c).toEq
theorem mul_one_eq (a : A) : WA.mul a WA.one = a := (WA.mul_one a).toEq
theorem one_mul_eq (a : A) : WA.mul WA.one a = a := (WA.one_mul a).toEq
theorem add_assoc_eq (a b c : A) : WA.add (WA.add a b) c = WA.add a (WA.add b c) := (WA.add_assoc a b c).toEq
theorem add_comm_eq (a b : A) : WA.add a b = WA.add b a := (WA.add_comm a b).toEq
theorem add_zero_eq (a : A) : WA.add a WA.zero = a := (WA.add_zero a).toEq
theorem idemp_sq_eq (i : Nat) : WA.mul (WA.idempotent i) (WA.idempotent i) = WA.idempotent i := (WA.idemp_sq i).toEq

/-- Idempotent cubed = idempotent. -/
noncomputable def idemp_cubed (i : Nat) :
    Path (WA.mul (WA.mul (WA.idempotent i) (WA.idempotent i)) (WA.idempotent i)) (WA.idempotent i) :=
  Path.trans (congrArg (fun z => WA.mul z (WA.idempotent i)) (WA.idemp_sq i)) (WA.idemp_sq i)

theorem idemp_cubed_eq (i : Nat) :
    WA.mul (WA.mul (WA.idempotent i) (WA.idempotent i)) (WA.idempotent i) = WA.idempotent i :=
  (WA.idemp_cubed i).toEq

/-- Triple mul. -/
noncomputable def triple_mul (a b c d : A) :
    Path (WA.mul (WA.mul (WA.mul a b) c) d) (WA.mul a (WA.mul b (WA.mul c d))) :=
  Path.trans (WA.mul_assoc (WA.mul a b) c d) (WA.mul_assoc a b (WA.mul c d))

theorem triple_mul_eq (a b c d : A) :
    WA.mul (WA.mul (WA.mul a b) c) d = WA.mul a (WA.mul b (WA.mul c d)) := (WA.triple_mul a b c d).toEq

/-- One on both sides. -/
noncomputable def one_mul_one_val (a : A) :
    Path (WA.mul WA.one (WA.mul a WA.one)) a :=
  Path.trans (WA.one_mul (WA.mul a WA.one)) (WA.mul_one a)

theorem one_mul_one_eq (a : A) : WA.mul WA.one (WA.mul a WA.one) = a := (WA.one_mul_one_val a).toEq

end WebsterAlgebra

/-! ## Reidemeister Moves -/

/-- Reidemeister move invariance. -/
structure ReidemeisterInvariance (H : Type u) where
  homology : H → H
  R1 : H → H  -- result after R1 move
  R2 : H → H
  R3 : H → H
  R1_inv : ∀ (h : H), Path (homology (R1 h)) (homology h)
  R2_inv : ∀ (h : H), Path (homology (R2 h)) (homology h)
  R3_inv : ∀ (h : H), Path (homology (R3 h)) (homology h)

namespace ReidemeisterInvariance

variable {H : Type u} (RI : ReidemeisterInvariance H)

theorem R1_inv_eq (h : H) : RI.homology (RI.R1 h) = RI.homology h := (RI.R1_inv h).toEq
theorem R2_inv_eq (h : H) : RI.homology (RI.R2 h) = RI.homology h := (RI.R2_inv h).toEq
theorem R3_inv_eq (h : H) : RI.homology (RI.R3 h) = RI.homology h := (RI.R3_inv h).toEq

/-- R1 then R2 doesn't change homology. -/
noncomputable def R1_R2 (h : H) :
    Path (RI.homology (RI.R1 (RI.R2 h))) (RI.homology h) :=
  Path.trans (RI.R1_inv (RI.R2 h)) (RI.R2_inv h)

theorem R1_R2_eq (h : H) : RI.homology (RI.R1 (RI.R2 h)) = RI.homology h := (RI.R1_R2 h).toEq

/-- All three moves. -/
noncomputable def R1_R2_R3 (h : H) :
    Path (RI.homology (RI.R1 (RI.R2 (RI.R3 h)))) (RI.homology h) :=
  Path.trans (RI.R1_inv (RI.R2 (RI.R3 h))) (Path.trans (RI.R2_inv (RI.R3 h)) (RI.R3_inv h))

theorem R1_R2_R3_eq (h : H) : RI.homology (RI.R1 (RI.R2 (RI.R3 h))) = RI.homology h :=
  (RI.R1_R2_R3 h).toEq

end ReidemeisterInvariance

end Algebra
end Path
end ComputationalPaths
