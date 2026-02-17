/- 
# Commutative Algebra via Computational Paths

Synthetic commutative-algebra interfaces built with computational paths:
rings, ideals, prime/maximal tags, localization, Noetherian behavior,
primary decomposition, integral extensions, going-up/going-down, Krull
dimension, completion, flatness, and Tor/Ext stubs.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.CommutativeAlgebraDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u

inductive Sym : Type
  | ring
  | ideal
  | mod
  deriving DecidableEq, Repr

inductive Gam : Type
  | base
  | local
  | complete
  deriving DecidableEq, Repr

theorem sym_refl_toEq (s : Sym) : Path.toEq (Path.refl s) = rfl := rfl

theorem gam_refl_toEq (g : Gam) : Path.toEq (Path.refl g) = rfl := rfl

@[simp] def mkStepPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem mkStepPath_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (mkStepPath h) = h := rfl

theorem mkStepPath_symm_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (Path.symm (mkStepPath h)) = h.symm := rfl

theorem mkStepPath_trans_symm_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (Path.trans (mkStepPath h) (Path.symm (mkStepPath h))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := mkStepPath h))

theorem mkStepPath_symm_trans_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (Path.trans (Path.symm (mkStepPath h)) (mkStepPath h)) = rfl := by
  simpa using (Path.toEq_symm_trans (p := mkStepPath h))

theorem mkStepPath_refl_left {A : Type u} {a b : A} (h : a = b) :
    Path.trans (Path.refl a) (mkStepPath h) = mkStepPath h := by
  simpa using (Path.trans_refl_left (p := mkStepPath h))

theorem mkStepPath_refl_right {A : Type u} {a b : A} (h : a = b) :
    Path.trans (mkStepPath h) (Path.refl b) = mkStepPath h := by
  simpa using (Path.trans_refl_right (p := mkStepPath h))

structure CommRing where
  ident : Nat
  dim : Nat
  depth : Nat
  deriving DecidableEq, Repr

structure CommIdeal where
  gen : Nat
  deriving DecidableEq, Repr

namespace CommIdeal

@[simp] def zero : CommIdeal := ⟨0⟩
@[simp] def one : CommIdeal := ⟨1⟩
@[simp] def add (I J : CommIdeal) : CommIdeal := ⟨Nat.gcd I.gen J.gen⟩
@[simp] def mul (I J : CommIdeal) : CommIdeal := ⟨I.gen * J.gen⟩
@[simp] def inter (I J : CommIdeal) : CommIdeal := ⟨Nat.lcm I.gen J.gen⟩
@[simp] def rad (I : CommIdeal) : CommIdeal := ⟨I.gen⟩

@[simp] def isPrime (I : CommIdeal) : Prop := I.gen ≤ 1
@[simp] def isMaximal (I : CommIdeal) : Prop := I.gen = 1
@[simp] def isPrimary (_I : CommIdeal) : Prop := True

end CommIdeal

theorem commIdeal_add_comm_eq (I J : CommIdeal) :
    CommIdeal.add I J = CommIdeal.add J I := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          simp [CommIdeal.add, Nat.gcd_comm]

theorem commIdeal_add_assoc_eq (I J K : CommIdeal) :
    CommIdeal.add (CommIdeal.add I J) K = CommIdeal.add I (CommIdeal.add J K) := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          cases K with
          | mk k =>
              simp [CommIdeal.add, Nat.gcd_assoc]

theorem commIdeal_add_idem_eq (I : CommIdeal) :
    CommIdeal.add I I = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.add]

theorem commIdeal_add_zero_right_eq (I : CommIdeal) :
    CommIdeal.add I CommIdeal.zero = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.add, CommIdeal.zero]

theorem commIdeal_add_zero_left_eq (I : CommIdeal) :
    CommIdeal.add CommIdeal.zero I = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.add, CommIdeal.zero]

theorem commIdeal_mul_comm_eq (I J : CommIdeal) :
    CommIdeal.mul I J = CommIdeal.mul J I := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          simp [CommIdeal.mul, Nat.mul_comm]

theorem commIdeal_mul_assoc_eq (I J K : CommIdeal) :
    CommIdeal.mul (CommIdeal.mul I J) K = CommIdeal.mul I (CommIdeal.mul J K) := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          cases K with
          | mk k =>
              simp [CommIdeal.mul, Nat.mul_assoc]

theorem commIdeal_mul_one_right_eq (I : CommIdeal) :
    CommIdeal.mul I CommIdeal.one = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.mul, CommIdeal.one]

theorem commIdeal_mul_one_left_eq (I : CommIdeal) :
    CommIdeal.mul CommIdeal.one I = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.mul, CommIdeal.one]

theorem commIdeal_mul_zero_right_eq (I : CommIdeal) :
    CommIdeal.mul I CommIdeal.zero = CommIdeal.zero := by
  cases I with
  | mk i =>
      simp [CommIdeal.mul, CommIdeal.zero]

theorem commIdeal_mul_zero_left_eq (I : CommIdeal) :
    CommIdeal.mul CommIdeal.zero I = CommIdeal.zero := by
  cases I with
  | mk i =>
      simp [CommIdeal.mul, CommIdeal.zero]

theorem commIdeal_inter_comm_eq (I J : CommIdeal) :
    CommIdeal.inter I J = CommIdeal.inter J I := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          simp [CommIdeal.inter, Nat.lcm_comm]

theorem commIdeal_inter_assoc_eq (I J K : CommIdeal) :
    CommIdeal.inter (CommIdeal.inter I J) K = CommIdeal.inter I (CommIdeal.inter J K) := by
  cases I with
  | mk i =>
      cases J with
      | mk j =>
          cases K with
          | mk k =>
              simp [CommIdeal.inter, Nat.lcm_assoc]

theorem commIdeal_rad_id_eq (I : CommIdeal) :
    CommIdeal.rad I = I := by
  cases I with
  | mk i =>
      simp [CommIdeal.rad]

theorem commIdeal_maximal_implies_prime (I : CommIdeal) :
    CommIdeal.isMaximal I → CommIdeal.isPrime I := by
  intro h
  cases I with
  | mk i =>
      simp [CommIdeal.isMaximal, CommIdeal.isPrime] at h ⊢
      cases h
      decide

theorem commIdeal_zero_is_prime : CommIdeal.isPrime CommIdeal.zero := by
  simp [CommIdeal.isPrime, CommIdeal.zero]

theorem commIdeal_one_is_maximal : CommIdeal.isMaximal CommIdeal.one := by
  simp [CommIdeal.isMaximal, CommIdeal.one]

theorem commIdeal_every_primary (I : CommIdeal) : CommIdeal.isPrimary I := by
  simp [CommIdeal.isPrimary]

inductive CommIdealStep : CommIdeal → CommIdeal → Type where
  | addComm (I J : CommIdeal) :
      CommIdealStep (CommIdeal.add I J) (CommIdeal.add J I)
  | addAssoc (I J K : CommIdeal) :
      CommIdealStep (CommIdeal.add (CommIdeal.add I J) K) (CommIdeal.add I (CommIdeal.add J K))
  | addZeroRight (I : CommIdeal) :
      CommIdealStep (CommIdeal.add I CommIdeal.zero) I
  | mulComm (I J : CommIdeal) :
      CommIdealStep (CommIdeal.mul I J) (CommIdeal.mul J I)
  | mulAssoc (I J K : CommIdeal) :
      CommIdealStep (CommIdeal.mul (CommIdeal.mul I J) K) (CommIdeal.mul I (CommIdeal.mul J K))
  | mulOneRight (I : CommIdeal) :
      CommIdealStep (CommIdeal.mul I CommIdeal.one) I
  | interComm (I J : CommIdeal) :
      CommIdealStep (CommIdeal.inter I J) (CommIdeal.inter J I)

def CommIdealStep.sound : CommIdealStep I J → I = J
  | .addComm I J => commIdeal_add_comm_eq I J
  | .addAssoc I J K => commIdeal_add_assoc_eq I J K
  | .addZeroRight I => commIdeal_add_zero_right_eq I
  | .mulComm I J => commIdeal_mul_comm_eq I J
  | .mulAssoc I J K => commIdeal_mul_assoc_eq I J K
  | .mulOneRight I => commIdeal_mul_one_right_eq I
  | .interComm I J => commIdeal_inter_comm_eq I J

def CommIdealStep.toPath (s : CommIdealStep I J) : Path I J :=
  Path.mk [Step.mk I J s.sound] s.sound

theorem commIdealStep_toEq {I J : CommIdeal} (s : CommIdealStep I J) :
    Path.toEq (s.toPath) = s.sound := rfl

def add_comm_path (I J : CommIdeal) : Path (CommIdeal.add I J) (CommIdeal.add J I) :=
  (CommIdealStep.addComm I J).toPath

def add_assoc_path (I J K : CommIdeal) :
    Path (CommIdeal.add (CommIdeal.add I J) K) (CommIdeal.add I (CommIdeal.add J K)) :=
  (CommIdealStep.addAssoc I J K).toPath

def add_zero_right_path (I : CommIdeal) :
    Path (CommIdeal.add I CommIdeal.zero) I :=
  (CommIdealStep.addZeroRight I).toPath

def mul_comm_path (I J : CommIdeal) : Path (CommIdeal.mul I J) (CommIdeal.mul J I) :=
  (CommIdealStep.mulComm I J).toPath

def mul_assoc_path (I J K : CommIdeal) :
    Path (CommIdeal.mul (CommIdeal.mul I J) K) (CommIdeal.mul I (CommIdeal.mul J K)) :=
  (CommIdealStep.mulAssoc I J K).toPath

def mul_one_right_path (I : CommIdeal) :
    Path (CommIdeal.mul I CommIdeal.one) I :=
  (CommIdealStep.mulOneRight I).toPath

def inter_comm_path (I J : CommIdeal) :
    Path (CommIdeal.inter I J) (CommIdeal.inter J I) :=
  (CommIdealStep.interComm I J).toPath

theorem add_comm_path_toEq (I J : CommIdeal) :
    Path.toEq (add_comm_path I J) = commIdeal_add_comm_eq I J := rfl

theorem add_assoc_path_toEq (I J K : CommIdeal) :
    Path.toEq (add_assoc_path I J K) = commIdeal_add_assoc_eq I J K := rfl

theorem add_zero_right_path_toEq (I : CommIdeal) :
    Path.toEq (add_zero_right_path I) = commIdeal_add_zero_right_eq I := rfl

theorem mul_comm_path_toEq (I J : CommIdeal) :
    Path.toEq (mul_comm_path I J) = commIdeal_mul_comm_eq I J := rfl

theorem mul_assoc_path_toEq (I J K : CommIdeal) :
    Path.toEq (mul_assoc_path I J K) = commIdeal_mul_assoc_eq I J K := rfl

theorem mul_one_right_path_toEq (I : CommIdeal) :
    Path.toEq (mul_one_right_path I) = commIdeal_mul_one_right_eq I := rfl

theorem inter_comm_path_toEq (I J : CommIdeal) :
    Path.toEq (inter_comm_path I J) = commIdeal_inter_comm_eq I J := rfl

theorem add_comm_roundtrip_toEq (I J : CommIdeal) :
    Path.toEq (Path.trans (add_comm_path I J) (Path.symm (add_comm_path I J))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := add_comm_path I J))

theorem mul_comm_roundtrip_toEq (I J : CommIdeal) :
    Path.toEq (Path.trans (mul_comm_path I J) (Path.symm (mul_comm_path I J))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := mul_comm_path I J))

theorem inter_comm_roundtrip_toEq (I J : CommIdeal) :
    Path.toEq (Path.trans (inter_comm_path I J) (Path.symm (inter_comm_path I J))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := inter_comm_path I J))

def add_comm_congr_mul_left (I J K : CommIdeal) :
    Path (CommIdeal.mul (CommIdeal.add I J) K) (CommIdeal.mul (CommIdeal.add J I) K) :=
  Path.congrArg (fun X => CommIdeal.mul X K) (add_comm_path I J)

def add_comm_congr_mul_right (I J K : CommIdeal) :
    Path (CommIdeal.mul K (CommIdeal.add I J)) (CommIdeal.mul K (CommIdeal.add J I)) :=
  Path.congrArg (fun X => CommIdeal.mul K X) (add_comm_path I J)

def mul_comm_congr_add_left (I J K : CommIdeal) :
    Path (CommIdeal.add (CommIdeal.mul I J) K) (CommIdeal.add (CommIdeal.mul J I) K) :=
  Path.congrArg (fun X => CommIdeal.add X K) (mul_comm_path I J)

def mul_comm_congr_add_right (I J K : CommIdeal) :
    Path (CommIdeal.add K (CommIdeal.mul I J)) (CommIdeal.add K (CommIdeal.mul J I)) :=
  Path.congrArg (fun X => CommIdeal.add K X) (mul_comm_path I J)

theorem add_comm_congr_mul_left_toEq (I J K : CommIdeal) :
    Path.toEq (add_comm_congr_mul_left I J K) =
      _root_.congrArg (fun X => CommIdeal.mul X K) (Path.toEq (add_comm_path I J)) := rfl

theorem add_comm_congr_mul_right_toEq (I J K : CommIdeal) :
    Path.toEq (add_comm_congr_mul_right I J K) =
      _root_.congrArg (fun X => CommIdeal.mul K X) (Path.toEq (add_comm_path I J)) := rfl

theorem mul_comm_congr_add_left_toEq (I J K : CommIdeal) :
    Path.toEq (mul_comm_congr_add_left I J K) =
      _root_.congrArg (fun X => CommIdeal.add X K) (Path.toEq (mul_comm_path I J)) := rfl

theorem mul_comm_congr_add_right_toEq (I J K : CommIdeal) :
    Path.toEq (mul_comm_congr_add_right I J K) =
      _root_.congrArg (fun X => CommIdeal.add K X) (Path.toEq (mul_comm_path I J)) := rfl

namespace CommRing

@[simp] def localize (R : CommRing) (s : Nat) : CommRing :=
  ⟨R.ident + s, R.dim, R.depth⟩

@[simp] def completion (R : CommRing) : CommRing :=
  ⟨R.ident, R.dim, R.depth + 1⟩

@[simp] def krullDim (R : CommRing) : Nat := R.dim

@[simp] def noetherian (_R : CommRing) : Prop := True

@[simp] def integralExt (R S : CommRing) : Prop := R.ident ≤ S.ident

@[simp] def goingUp (R S : CommRing) : Prop := integralExt R S

@[simp] def goingDown (R S : CommRing) : Prop := R.dim = S.dim

@[simp] def flat (_R : CommRing) : Prop := True

end CommRing

theorem noetherian_intro (R : CommRing) : CommRing.noetherian R := by
  trivial

theorem noetherian_localize (R : CommRing) (s : Nat) :
    CommRing.noetherian (CommRing.localize R s) := by
  trivial

theorem noetherian_completion (R : CommRing) :
    CommRing.noetherian (CommRing.completion R) := by
  trivial

theorem krull_dim_localize (R : CommRing) (s : Nat) :
    CommRing.krullDim (CommRing.localize R s) = CommRing.krullDim R := by
  cases R with
  | mk i d t =>
      simp [CommRing.localize, CommRing.krullDim]

theorem krull_dim_completion (R : CommRing) :
    CommRing.krullDim (CommRing.completion R) = CommRing.krullDim R := by
  cases R with
  | mk i d t =>
      simp [CommRing.completion, CommRing.krullDim]

theorem completion_depth_eq (R : CommRing) :
    (CommRing.completion R).depth = R.depth + 1 := by
  cases R with
  | mk i d t =>
      simp [CommRing.completion]

theorem integral_refl (R : CommRing) : CommRing.integralExt R R := by
  exact Nat.le_refl R.ident

theorem integral_trans (R S T : CommRing) :
    CommRing.integralExt R S → CommRing.integralExt S T → CommRing.integralExt R T := by
  intro hRS hST
  exact Nat.le_trans hRS hST

theorem going_up_of_integral (R S : CommRing) :
    CommRing.integralExt R S → CommRing.goingUp R S := by
  intro h
  exact h

theorem going_down_refl (R : CommRing) : CommRing.goingDown R R := by
  rfl

theorem going_down_symm (R S : CommRing) :
    CommRing.goingDown R S → CommRing.goingDown S R := by
  intro h
  simpa [CommRing.goingDown] using h.symm

theorem going_down_trans (R S T : CommRing) :
    CommRing.goingDown R S → CommRing.goingDown S T → CommRing.goingDown R T := by
  intro hRS hST
  simpa [CommRing.goingDown] using Eq.trans hRS hST

theorem flat_intro (R : CommRing) : CommRing.flat R := by
  trivial

theorem localization_zero_eq (R : CommRing) :
    CommRing.localize R 0 = R := by
  cases R with
  | mk i d t =>
      simp [CommRing.localize]

theorem localization_zero_path_toEq (R : CommRing) :
    Path.toEq (mkStepPath (localization_zero_eq R)) = localization_zero_eq R := rfl

theorem completion_ident_path_toEq (R : CommRing) :
    Path.toEq (Path.refl (CommRing.completion R).ident) = rfl := rfl

theorem completion_dim_path_toEq (R : CommRing) :
    Path.toEq (Path.refl (CommRing.completion R).dim) = rfl := rfl

@[simp] def primaryDecomposition (I : CommIdeal) : List CommIdeal := [I]

@[simp] def recombinePrimary : List CommIdeal → CommIdeal
  | [] => CommIdeal.zero
  | I :: _ => I

theorem primary_nonempty (I : CommIdeal) :
    primaryDecomposition I ≠ [] := by
  simp [primaryDecomposition]

theorem primary_length_one (I : CommIdeal) :
    (primaryDecomposition I).length = 1 := by
  simp [primaryDecomposition]

theorem primary_recombine_singleton (I : CommIdeal) :
    recombinePrimary [I] = I := by
  simp [recombinePrimary]

theorem primary_reconstruct_eq (I : CommIdeal) :
    recombinePrimary (primaryDecomposition I) = I := by
  simp [primaryDecomposition, recombinePrimary]

theorem primary_reconstruct_path_toEq (I : CommIdeal) :
    Path.toEq (mkStepPath (primary_reconstruct_eq I)) = primary_reconstruct_eq I := rfl

theorem primary_radical_eq (I : CommIdeal) :
    CommIdeal.rad (recombinePrimary (primaryDecomposition I)) = CommIdeal.rad I := by
  simp [primaryDecomposition, recombinePrimary, CommIdeal.rad]

theorem primary_component_isPrimary (I : CommIdeal) :
    CommIdeal.isPrimary (recombinePrimary (primaryDecomposition I)) := by
  simp [primaryDecomposition, recombinePrimary, CommIdeal.isPrimary]

structure Fraction where
  num : Nat
  den : Nat
  deriving DecidableEq, Repr

namespace Fraction

@[simp] def mul (x y : Fraction) : Fraction :=
  ⟨x.num * y.num, x.den * y.den⟩

@[simp] def add (x y : Fraction) : Fraction :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩

@[simp] def normalize (x : Fraction) : Fraction :=
  ⟨x.num, x.den + 1⟩

end Fraction

theorem fraction_mul_comm_eq (x y : Fraction) :
    Fraction.mul x y = Fraction.mul y x := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          simp [Fraction.mul, Nat.mul_comm]

theorem fraction_mul_assoc_eq (x y z : Fraction) :
    Fraction.mul (Fraction.mul x y) z = Fraction.mul x (Fraction.mul y z) := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          cases z with
          | mk zn zd =>
              simp [Fraction.mul, Nat.mul_assoc]

theorem fraction_mul_comm_path_toEq (x y : Fraction) :
    Path.toEq (mkStepPath (fraction_mul_comm_eq x y)) = fraction_mul_comm_eq x y := rfl

theorem fraction_mul_roundtrip_toEq (x y : Fraction) :
    Path.toEq (Path.trans (mkStepPath (fraction_mul_comm_eq x y))
      (Path.symm (mkStepPath (fraction_mul_comm_eq x y)))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := mkStepPath (fraction_mul_comm_eq x y)))

theorem fraction_num_congr_toEq (x y : Fraction) :
    Path.toEq (Path.congrArg Fraction.num (mkStepPath (fraction_mul_comm_eq x y))) =
      _root_.congrArg Fraction.num (fraction_mul_comm_eq x y) := rfl

theorem fraction_den_congr_toEq (x y : Fraction) :
    Path.toEq (Path.congrArg Fraction.den (mkStepPath (fraction_mul_comm_eq x y))) =
      _root_.congrArg Fraction.den (fraction_mul_comm_eq x y) := rfl

theorem normalize_preserves_num (x : Fraction) :
    (Fraction.normalize x).num = x.num := by
  rfl

structure ModObj where
  rank : Nat
  deriving DecidableEq, Repr

namespace ModObj

@[simp] def directSum (M N : ModObj) : ModObj := ⟨M.rank + N.rank⟩
@[simp] def tensor (M N : ModObj) : ModObj := ⟨M.rank * N.rank⟩

end ModObj

@[simp] def Tor (i : Nat) (M N : ModObj) : Nat :=
  if i = 0 then (ModObj.tensor M N).rank else 0

@[simp] def Ext (i : Nat) (M N : ModObj) : Nat :=
  if i = 0 then (ModObj.directSum M N).rank else 0

theorem tensor_comm_eq (M N : ModObj) :
    ModObj.tensor M N = ModObj.tensor N M := by
  cases M with
  | mk m =>
      cases N with
      | mk n =>
          simp [ModObj.tensor, Nat.mul_comm]

theorem tensor_comm_path_toEq (M N : ModObj) :
    Path.toEq (mkStepPath (tensor_comm_eq M N)) = tensor_comm_eq M N := rfl

theorem tensor_roundtrip_toEq (M N : ModObj) :
    Path.toEq (Path.trans (mkStepPath (tensor_comm_eq M N))
      (Path.symm (mkStepPath (tensor_comm_eq M N)))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := mkStepPath (tensor_comm_eq M N)))

theorem directSum_comm_eq (M N : ModObj) :
    ModObj.directSum M N = ModObj.directSum N M := by
  cases M with
  | mk m =>
      cases N with
      | mk n =>
          simp [ModObj.directSum, Nat.add_comm]

theorem directSum_comm_path_toEq (M N : ModObj) :
    Path.toEq (mkStepPath (directSum_comm_eq M N)) = directSum_comm_eq M N := rfl

theorem directSum_roundtrip_toEq (M N : ModObj) :
    Path.toEq (Path.trans (mkStepPath (directSum_comm_eq M N))
      (Path.symm (mkStepPath (directSum_comm_eq M N)))) = rfl := by
  simpa using (Path.toEq_trans_symm (p := mkStepPath (directSum_comm_eq M N)))

theorem tor_zero_formula (M N : ModObj) :
    Tor 0 M N = (ModObj.tensor M N).rank := by
  simp [Tor]

theorem tor_one_vanish (M N : ModObj) :
    Tor 1 M N = 0 := by
  simp [Tor]

theorem tor_succ_vanish (n : Nat) (M N : ModObj) :
    Tor (Nat.succ n) M N = 0 := by
  simp [Tor]

theorem ext_zero_formula (M N : ModObj) :
    Ext 0 M N = (ModObj.directSum M N).rank := by
  simp [Ext]

theorem ext_one_vanish (M N : ModObj) :
    Ext 1 M N = 0 := by
  simp [Ext]

theorem ext_succ_vanish (n : Nat) (M N : ModObj) :
    Ext (Nat.succ n) M N = 0 := by
  simp [Ext]

theorem tor_zero_path_toEq (M N : ModObj) :
    Path.toEq (Path.refl (Tor 0 M N)) = rfl := rfl

theorem ext_zero_path_toEq (M N : ModObj) :
    Path.toEq (Path.refl (Ext 0 M N)) = rfl := rfl

theorem flat_tensor_rank_refl (M N : ModObj) :
    Path.toEq (Path.refl ((ModObj.tensor M N).rank)) = rfl := rfl

theorem ext_congr_rank_toEq (M N : ModObj) :
    Path.toEq (Path.congrArg (fun n : Nat => n + 0) (Path.refl (Ext 0 M N))) = rfl := by
  simp

end ComputationalPaths.Path.Algebra.CommutativeAlgebraDeep
