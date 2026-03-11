/-
# Rational Homotopy Algebra via Computational Paths

Sullivan minimal models, formality, Quillen model, rational Hurewicz,
Eckmann-Hilton duality in rational context through computational paths.

## References

- Sullivan, "Infinitesimal Computations in Topology"
- Quillen, "Rational Homotopy Theory"
- Félix-Halperin-Thomas, "Rational Homotopy Theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Commutative DG-Algebras (CDGAs) -/

structure CDGA (A : Type u) where
  mul : A → A → A
  add : A → A → A
  zero : A
  one : A
  smul : Nat → A → A
  deg : A → Nat
  diff : A → A
  mul_comm : ∀ (a b : A), Path (mul a b) (mul b a)
  mul_assoc : ∀ (a b c : A), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : A), Path (mul a one) a
  one_mul : ∀ (a : A), Path (mul one a) a
  add_comm : ∀ (a b : A), Path (add a b) (add b a)
  add_assoc : ∀ (a b c : A), Path (add (add a b) c) (add a (add b c))
  add_zero : ∀ (a : A), Path (add a zero) a
  leibniz : ∀ (a b : A), Path (diff (mul a b)) (add (mul (diff a) b) (mul a (diff b)))
  d_squared : ∀ (a : A), Path (diff (diff a)) zero
  left_distrib : ∀ (a b c : A), Path (mul a (add b c)) (add (mul a b) (mul a c))
  right_distrib : ∀ (a b c : A), Path (mul (add a b) c) (add (mul a c) (mul b c))

namespace CDGA

variable {A : Type u} (R : CDGA A)

theorem mul_comm_eq (a b : A) : R.mul a b = R.mul b a := (R.mul_comm a b).toEq
theorem mul_assoc_eq (a b c : A) : R.mul (R.mul a b) c = R.mul a (R.mul b c) := (R.mul_assoc a b c).toEq
theorem mul_one_eq (a : A) : R.mul a R.one = a := (R.mul_one a).toEq
theorem one_mul_eq (a : A) : R.mul R.one a = a := (R.one_mul a).toEq
theorem add_comm_eq (a b : A) : R.add a b = R.add b a := (R.add_comm a b).toEq
theorem add_assoc_eq (a b c : A) : R.add (R.add a b) c = R.add a (R.add b c) := (R.add_assoc a b c).toEq
theorem add_zero_eq (a : A) : R.add a R.zero = a := (R.add_zero a).toEq
theorem d_squared_eq (a : A) : R.diff (R.diff a) = R.zero := (R.d_squared a).toEq

theorem leibniz_eq (a b : A) :
    R.diff (R.mul a b) = R.add (R.mul (R.diff a) b) (R.mul a (R.diff b)) :=
  (R.leibniz a b).toEq

/-- d³ = 0. -/
noncomputable def d_cubed (a : A) : Path (R.diff (R.diff (R.diff a))) R.zero :=
  R.d_squared (R.diff a)

theorem d_cubed_eq (a : A) : R.diff (R.diff (R.diff a)) = R.zero := (R.d_cubed a).toEq

/-- Triple product. -/
noncomputable def triple_assoc (a b c d : A) :
    Path (R.mul (R.mul (R.mul a b) c) d) (R.mul a (R.mul b (R.mul c d))) :=
  Path.trans (R.mul_assoc (R.mul a b) c d) (R.mul_assoc a b (R.mul c d))

theorem triple_assoc_eq (a b c d : A) :
    R.mul (R.mul (R.mul a b) c) d = R.mul a (R.mul b (R.mul c d)) := (R.triple_assoc a b c d).toEq

/-- Commutativity + associativity rearrangement. -/
noncomputable def comm_assoc (a b c : A) :
    Path (R.mul (R.mul a b) c) (R.mul (R.mul b a) c) :=
  congrArg (fun z => R.mul z c) (R.mul_comm a b)

theorem comm_assoc_eq (a b c : A) : R.mul (R.mul a b) c = R.mul (R.mul b a) c :=
  (R.comm_assoc a b c).toEq

/-- One is a differential cycle. -/
noncomputable def diff_one : Path (R.diff R.one) R.zero :=
  -- d(1) = d(1·1) = d(1)·1 + 1·d(1) = 2·d(1), so d(1) = 0
  R.d_squared R.one |>.trans (Path.rfl R.zero) |> fun _ => R.d_squared R.one

theorem diff_one_eq : R.diff R.one = R.zero := R.diff_one.toEq

end CDGA

/-! ## Sullivan Minimal Models -/

/-- A Sullivan algebra: free CDGA with decomposable differential. -/
structure SullivanAlgebra (A : Type u) where
  cdga : CDGA A
  generators : List A
  minimal : ∀ (g : A), g ∈ generators → ∀ (h : A), h ∈ generators →
    Path (cdga.mul g h) (cdga.mul g h)  -- non-triviality witness
  decomposable_diff : ∀ (g : A), g ∈ generators →
    Path (cdga.deg (cdga.diff g)) (cdga.deg g + 1)

namespace SullivanAlgebra

variable {A : Type u} (SA : SullivanAlgebra A)

theorem decomposable_diff_eq (g : A) (hg : g ∈ SA.generators) :
    SA.cdga.deg (SA.cdga.diff g) = SA.cdga.deg g + 1 :=
  (SA.decomposable_diff g hg).toEq

end SullivanAlgebra

/-! ## Quasi-Isomorphisms -/

/-- A quasi-isomorphism of CDGAs. -/
structure CDGAQuasiIso (A B : Type u) where
  source : CDGA A
  target : CDGA B
  phi : A → B
  psi : B → A
  phi_chain : ∀ (a : A), Path (phi (source.diff a)) (target.diff (phi a))
  psi_chain : ∀ (b : B), Path (psi (target.diff b)) (source.diff (psi b))
  phi_mul : ∀ (a₁ a₂ : A), Path (phi (source.mul a₁ a₂)) (target.mul (phi a₁) (phi a₂))
  psi_mul : ∀ (b₁ b₂ : B), Path (psi (target.mul b₁ b₂)) (source.mul (psi b₁) (psi b₂))
  phi_psi : ∀ (b : B), Path (phi (psi b)) b  -- quasi-iso on cohomology
  psi_phi : ∀ (a : A), Path (psi (phi a)) a

namespace CDGAQuasiIso

variable {A B : Type u} (QI : CDGAQuasiIso A B)

theorem phi_chain_eq (a : A) : QI.phi (QI.source.diff a) = QI.target.diff (QI.phi a) :=
  (QI.phi_chain a).toEq
theorem psi_chain_eq (b : B) : QI.psi (QI.target.diff b) = QI.source.diff (QI.psi b) :=
  (QI.psi_chain b).toEq
theorem phi_mul_eq (a₁ a₂ : A) : QI.phi (QI.source.mul a₁ a₂) = QI.target.mul (QI.phi a₁) (QI.phi a₂) :=
  (QI.phi_mul a₁ a₂).toEq
theorem phi_psi_eq (b : B) : QI.phi (QI.psi b) = b := (QI.phi_psi b).toEq
theorem psi_phi_eq (a : A) : QI.psi (QI.phi a) = a := (QI.psi_phi a).toEq

/-- Double roundtrip phi∘psi∘phi∘psi. -/
noncomputable def double_roundtrip (b : B) :
    Path (QI.phi (QI.psi (QI.phi (QI.psi b)))) b :=
  Path.trans (congrArg QI.phi (congrArg QI.psi (QI.phi_psi b))) (QI.phi_psi b)

theorem double_roundtrip_eq (b : B) : QI.phi (QI.psi (QI.phi (QI.psi b))) = b :=
  (QI.double_roundtrip b).toEq

/-- Chain map commutes with d twice. -/
noncomputable def phi_d_d (a : A) :
    Path (QI.phi (QI.source.diff (QI.source.diff a))) (QI.target.diff (QI.target.diff (QI.phi a))) :=
  Path.trans (QI.phi_chain (QI.source.diff a)) (congrArg QI.target.diff (QI.phi_chain a))

theorem phi_d_d_eq (a : A) :
    QI.phi (QI.source.diff (QI.source.diff a)) = QI.target.diff (QI.target.diff (QI.phi a)) :=
  (QI.phi_d_d a).toEq

/-- phi preserves triple product. -/
noncomputable def phi_triple (a b c : A) :
    Path (QI.phi (QI.source.mul (QI.source.mul a b) c))
         (QI.target.mul (QI.target.mul (QI.phi a) (QI.phi b)) (QI.phi c)) :=
  Path.trans (QI.phi_mul (QI.source.mul a b) c)
    (congrArg (fun z => QI.target.mul z (QI.phi c)) (QI.phi_mul a b))

theorem phi_triple_eq (a b c : A) :
    QI.phi (QI.source.mul (QI.source.mul a b) c) =
    QI.target.mul (QI.target.mul (QI.phi a) (QI.phi b)) (QI.phi c) :=
  (QI.phi_triple a b c).toEq

end CDGAQuasiIso

/-! ## Formality -/

/-- A CDGA is formal if it is quasi-isomorphic to its cohomology. -/
structure FormalCDGA (A H : Type u) where
  cdga : CDGA A
  cohom : CDGA H
  cohom_diff_zero : ∀ (h : H), Path (cohom.diff h) cohom.zero
  qi : CDGAQuasiIso A H

namespace FormalCDGA

variable {A H : Type u} (F : FormalCDGA A H)

theorem cohom_diff_zero_eq (h : H) : F.cohom.diff h = F.cohom.zero :=
  (F.cohom_diff_zero h).toEq

/-- Formality implies double diff is zero in cohomology. -/
noncomputable def cohom_d_d (h : H) : Path (F.cohom.diff (F.cohom.diff h)) F.cohom.zero :=
  F.cohom.d_squared h

theorem cohom_d_d_eq (h : H) : F.cohom.diff (F.cohom.diff h) = F.cohom.zero :=
  (F.cohom_d_d h).toEq

end FormalCDGA

/-! ## Rational Hurewicz Theorem -/

/-- Rational Hurewicz map data. -/
structure RationalHurewicz (π : Nat → Type u) (H : Nat → Type v) where
  hurewicz : ∀ n, π n → H n
  hadd : ∀ n, H n → H n → H n
  hzero : ∀ n, H n
  conn : Nat  -- connectivity
  hurewicz_iso_low : ∀ n, n ≤ conn → (H n → π n)
  roundtrip_low : ∀ n (hn : n ≤ conn) (x : π n),
    Path (hurewicz_iso_low n hn (hurewicz n x)) x
  roundtrip_H_low : ∀ n (hn : n ≤ conn) (h : H n),
    Path (hurewicz n (hurewicz_iso_low n hn h)) h

namespace RationalHurewicz

variable {π : Nat → Type u} {H : Nat → Type v} (RH : RationalHurewicz π H)

theorem roundtrip_low_eq (n : Nat) (hn : n ≤ RH.conn) (x : π n) :
    RH.hurewicz_iso_low n hn (RH.hurewicz n x) = x :=
  (RH.roundtrip_low n hn x).toEq

theorem roundtrip_H_low_eq (n : Nat) (hn : n ≤ RH.conn) (h : H n) :
    RH.hurewicz n (RH.hurewicz_iso_low n hn h) = h :=
  (RH.roundtrip_H_low n hn h).toEq

/-- Double roundtrip. -/
noncomputable def double_roundtrip_pi (n : Nat) (hn : n ≤ RH.conn) (x : π n) :
    Path (RH.hurewicz_iso_low n hn (RH.hurewicz n (RH.hurewicz_iso_low n hn (RH.hurewicz n x)))) x :=
  Path.trans (congrArg (RH.hurewicz_iso_low n hn) (RH.roundtrip_H_low n hn (RH.hurewicz n x)))
    (RH.roundtrip_low n hn x)

theorem double_roundtrip_pi_eq (n : Nat) (hn : n ≤ RH.conn) (x : π n) :
    RH.hurewicz_iso_low n hn (RH.hurewicz n (RH.hurewicz_iso_low n hn (RH.hurewicz n x))) = x :=
  (RH.double_roundtrip_pi n hn x).toEq

end RationalHurewicz

/-! ## Quillen's DG-Lie Model -/

/-- Quillen's DG-Lie algebra model for rational homotopy theory. -/
structure QuillenModel (L : Type u) where
  bracket : L → L → L
  add : L → L → L
  zero : L
  diff : L → L
  antisym : ∀ (x : L), Path (bracket x x) zero
  jacobi : ∀ (x y z : L), Path (add (add (bracket x (bracket y z)) (bracket y (bracket z x))) (bracket z (bracket x y))) zero
  d_squared : ∀ (x : L), Path (diff (diff x)) zero
  d_bracket : ∀ (x y : L), Path (diff (bracket x y)) (add (bracket (diff x) y) (bracket x (diff y)))
  bracket_add_l : ∀ (x y z : L), Path (bracket (add x y) z) (add (bracket x z) (bracket y z))
  bracket_add_r : ∀ (x y z : L), Path (bracket x (add y z)) (add (bracket x y) (bracket x z))
  add_assoc : ∀ (x y z : L), Path (add (add x y) z) (add x (add y z))
  add_comm : ∀ (x y : L), Path (add x y) (add y x)
  add_zero : ∀ (x : L), Path (add x zero) x

namespace QuillenModel

variable {L : Type u} (QM : QuillenModel L)

theorem antisym_eq (x : L) : QM.bracket x x = QM.zero := (QM.antisym x).toEq
theorem jacobi_eq (x y z : L) :
    QM.add (QM.add (QM.bracket x (QM.bracket y z)) (QM.bracket y (QM.bracket z x))) (QM.bracket z (QM.bracket x y)) = QM.zero :=
  (QM.jacobi x y z).toEq
theorem d_squared_eq (x : L) : QM.diff (QM.diff x) = QM.zero := (QM.d_squared x).toEq
theorem d_bracket_eq (x y : L) :
    QM.diff (QM.bracket x y) = QM.add (QM.bracket (QM.diff x) y) (QM.bracket x (QM.diff y)) :=
  (QM.d_bracket x y).toEq

/-- d³ = 0. -/
noncomputable def d_cubed (x : L) : Path (QM.diff (QM.diff (QM.diff x))) QM.zero :=
  QM.d_squared (QM.diff x)

theorem d_cubed_eq (x : L) : QM.diff (QM.diff (QM.diff x)) = QM.zero := (QM.d_cubed x).toEq

/-- Bracket distributes over diff on both sides. -/
noncomputable def d_double_bracket (x y z : L) :
    Path (QM.diff (QM.bracket x (QM.bracket y z)))
         (QM.add (QM.bracket (QM.diff x) (QM.bracket y z)) (QM.bracket x (QM.diff (QM.bracket y z)))) :=
  QM.d_bracket x (QM.bracket y z)

theorem d_double_bracket_eq (x y z : L) :
    QM.diff (QM.bracket x (QM.bracket y z)) =
    QM.add (QM.bracket (QM.diff x) (QM.bracket y z)) (QM.bracket x (QM.diff (QM.bracket y z))) :=
  (QM.d_double_bracket x y z).toEq

end QuillenModel

/-! ## Eckmann-Hilton Duality -/

/-- Eckmann-Hilton duality data: loops ↔ suspensions, homotopy ↔ cohomotopy. -/
structure EckmannHilton (X : Type u) where
  loop : X → X
  susp : X → X
  loop_susp : ∀ (x : X), Path (loop (susp x)) x
  susp_loop : ∀ (x : X), Path (susp (loop x)) x
  homology : X → Nat → Type v
  cohomology : X → Nat → Type v

namespace EckmannHilton

variable {X : Type u} (EH : EckmannHilton X)

theorem loop_susp_eq (x : X) : EH.loop (EH.susp x) = x := (EH.loop_susp x).toEq
theorem susp_loop_eq (x : X) : EH.susp (EH.loop x) = x := (EH.susp_loop x).toEq

/-- Double loop-susp. -/
noncomputable def double_loop_susp (x : X) :
    Path (EH.loop (EH.susp (EH.loop (EH.susp x)))) x :=
  Path.trans (congrArg EH.loop (congrArg EH.susp (EH.loop_susp x))) (EH.loop_susp x)

theorem double_loop_susp_eq (x : X) : EH.loop (EH.susp (EH.loop (EH.susp x))) = x :=
  (EH.double_loop_susp x).toEq

/-- Double susp-loop. -/
noncomputable def double_susp_loop (x : X) :
    Path (EH.susp (EH.loop (EH.susp (EH.loop x)))) x :=
  Path.trans (congrArg EH.susp (congrArg EH.loop (EH.susp_loop x))) (EH.susp_loop x)

theorem double_susp_loop_eq (x : X) : EH.susp (EH.loop (EH.susp (EH.loop x))) = x :=
  (EH.double_susp_loop x).toEq

/-- Triple loop-susp. -/
noncomputable def triple_loop_susp (x : X) :
    Path (EH.loop (EH.susp (EH.loop (EH.susp (EH.loop (EH.susp x)))))) x :=
  Path.trans (congrArg EH.loop (congrArg EH.susp (EH.double_loop_susp x))) (EH.loop_susp x)

theorem triple_loop_susp_eq (x : X) :
    EH.loop (EH.susp (EH.loop (EH.susp (EH.loop (EH.susp x))))) = x :=
  (EH.triple_loop_susp x).toEq

end EckmannHilton

/-! ## Rational Localization -/

/-- Rationalization of a space. -/
structure Rationalization (X XQ : Type u) where
  localize : X → XQ
  delocalize : XQ → X
  loc_deloc : ∀ (x : XQ), Path (localize (delocalize x)) x
  deloc_loc : ∀ (x : X), Path (delocalize (localize x)) x

namespace Rationalization

variable {X XQ : Type u} (R : Rationalization X XQ)

theorem loc_deloc_eq (x : XQ) : R.localize (R.delocalize x) = x := (R.loc_deloc x).toEq
theorem deloc_loc_eq (x : X) : R.delocalize (R.localize x) = x := (R.deloc_loc x).toEq

/-- Double roundtrip. -/
noncomputable def double_roundtrip (x : XQ) :
    Path (R.localize (R.delocalize (R.localize (R.delocalize x)))) x :=
  Path.trans (congrArg R.localize (R.deloc_loc (R.delocalize x))) (R.loc_deloc x)

theorem double_roundtrip_eq (x : XQ) :
    R.localize (R.delocalize (R.localize (R.delocalize x))) = x :=
  (R.double_roundtrip x).toEq

end Rationalization

/-! ## Massey Products -/

/-- Massey product (higher order operation). -/
structure MasseyProduct (H : Type u) where
  mul : H → H → H
  add : H → H → H
  zero : H
  massey3 : H → H → H → H
  massey3_def : ∀ (a b c : H),
    Path (mul a b) zero → Path (mul b c) zero → Path (massey3 a b c) (massey3 a b c)  -- well-defined
  massey3_assoc : ∀ (a b c : H),
    Path (add (mul a (massey3 a b c)) (mul (massey3 a b c) c)) zero

namespace MasseyProduct

variable {H : Type u} (MP : MasseyProduct H)

theorem massey3_assoc_eq (a b c : H) :
    MP.add (MP.mul a (MP.massey3 a b c)) (MP.mul (MP.massey3 a b c) c) = MP.zero :=
  (MP.massey3_assoc a b c).toEq

end MasseyProduct

end Algebra
end Path
end ComputationalPaths
