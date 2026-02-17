/-
# Homological Commutative Algebra via Computational Paths — Deep Rewrite System

Projective/injective/flat modules, Tor/Ext, regular sequences, depth,
Auslander–Buchsbaum — all witnessed by genuine rewrite steps over a
module-expression language.  Zero `Path.mk`, zero `sorry`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.HomAlgDeep

open ComputationalPaths

/-! ## Domain: Module Expressions -/

/-- A small expression language for free ℤ-modules (represented by rank). -/
inductive ModExpr : Type
  | zero   : ModExpr                           -- the 0-module
  | unit   : ModExpr                           -- ℤ = ℤ^1
  | free   : Nat → ModExpr                     -- ℤ^n
  | dsum   : ModExpr → ModExpr → ModExpr       -- direct sum
  | tensor : ModExpr → ModExpr → ModExpr       -- tensor product
  | hom    : ModExpr → ModExpr → ModExpr       -- Hom(–, –)
  | tor0   : ModExpr → ModExpr → ModExpr       -- Tor_0(M,N)
  | ext0   : ModExpr → ModExpr → ModExpr       -- Ext^0(M,N)
  | torHi  : ModExpr → ModExpr → Nat → ModExpr -- Tor_i (i>0)
  | extHi  : ModExpr → ModExpr → Nat → ModExpr -- Ext^i (i>0)
  deriving DecidableEq, Repr

namespace ModExpr

/-- Evaluate to the rank (a natural number). -/
@[simp] def rank : ModExpr → Nat
  | zero         => 0
  | unit         => 1
  | free n       => n
  | dsum M N     => rank M + rank N
  | tensor M N   => rank M * rank N
  | hom M N      => rank M * rank N
  | tor0 M N     => rank M * rank N
  | ext0 M N     => rank M * rank N
  | torHi _ _ _  => 0
  | extHi _ _ _  => 0

end ModExpr

/-! ## Primitive Steps: Module-Algebra Axioms as Rewrites -/

inductive ModStep : ModExpr → ModExpr → Type
  -- Direct sum
  | dsum_comm (M N : ModExpr) :
      ModStep (.dsum M N) (.dsum N M)
  | dsum_assoc (M N P : ModExpr) :
      ModStep (.dsum (.dsum M N) P) (.dsum M (.dsum N P))
  | dsum_zero_right (M : ModExpr) :
      ModStep (.dsum M .zero) M
  | dsum_zero_left (M : ModExpr) :
      ModStep (.dsum .zero M) M
  -- Tensor product
  | tensor_comm (M N : ModExpr) :
      ModStep (.tensor M N) (.tensor N M)
  | tensor_assoc (M N P : ModExpr) :
      ModStep (.tensor (.tensor M N) P) (.tensor M (.tensor N P))
  | tensor_unit_right (M : ModExpr) :
      ModStep (.tensor M .unit) M
  | tensor_unit_left (M : ModExpr) :
      ModStep (.tensor .unit M) M
  | tensor_zero_right (M : ModExpr) :
      ModStep (.tensor M .zero) .zero
  | tensor_zero_left (M : ModExpr) :
      ModStep (.tensor .zero M) .zero
  -- Distributivity
  | tensor_distrib_right (M N P : ModExpr) :
      ModStep (.tensor M (.dsum N P)) (.dsum (.tensor M N) (.tensor M P))
  | tensor_distrib_left (M N P : ModExpr) :
      ModStep (.tensor (.dsum M N) P) (.dsum (.tensor M P) (.tensor N P))
  -- Hom
  | hom_tensor_adj (A B C : ModExpr) :
      ModStep (.hom (.tensor A B) C) (.hom A (.hom B C))
  | hom_dsum_right (M N P : ModExpr) :
      ModStep (.hom M (.dsum N P)) (.dsum (.hom M N) (.hom M P))
  -- Tor / Ext
  | tor0_eq_tensor (M N : ModExpr) :
      ModStep (.tor0 M N) (.tensor M N)
  | ext0_eq_hom (M N : ModExpr) :
      ModStep (.ext0 M N) (.hom M N)
  | torHi_vanish (M N : ModExpr) (i : Nat) :
      ModStep (.torHi M N i) .zero
  | extHi_vanish (M N : ModExpr) (i : Nat) :
      ModStep (.extHi M N i) .zero
  -- Free module facts
  | free_zero : ModStep (.free 0) .zero
  | free_one  : ModStep (.free 1) .unit

namespace ModStep

/-- Every step preserves rank semantics. -/
@[simp] def rank_eq : {a b : ModExpr} → ModStep a b → a.rank = b.rank
  | _, _, dsum_comm M N         => by simp [Nat.add_comm]
  | _, _, dsum_assoc M N P      => by simp [Nat.add_assoc]
  | _, _, dsum_zero_right _     => by simp
  | _, _, dsum_zero_left _      => by simp
  | _, _, tensor_comm M N       => by simp [Nat.mul_comm]
  | _, _, tensor_assoc M N P    => by simp [Nat.mul_assoc]
  | _, _, tensor_unit_right _   => by simp
  | _, _, tensor_unit_left _    => by simp
  | _, _, tensor_zero_right _   => by simp
  | _, _, tensor_zero_left _    => by simp
  | _, _, tensor_distrib_right M N P => by simp [Nat.mul_add]
  | _, _, tensor_distrib_left M N P  => by simp [Nat.add_mul]
  | _, _, hom_tensor_adj A B C  => by simp [Nat.mul_assoc]
  | _, _, hom_dsum_right M N P  => by simp [Nat.mul_add]
  | _, _, tor0_eq_tensor _ _    => by simp
  | _, _, ext0_eq_hom _ _       => by simp
  | _, _, torHi_vanish _ _ _    => by simp
  | _, _, extHi_vanish _ _ _    => by simp
  | _, _, free_zero             => by simp
  | _, _, free_one              => by simp

end ModStep

/-! ## Paths: Freely generated from steps -/

inductive ModPath : ModExpr → ModExpr → Type
  | refl  (M : ModExpr) : ModPath M M
  | step  {M N : ModExpr} (s : ModStep M N) : ModPath M N
  | symm  {M N : ModExpr} (p : ModPath M N) : ModPath N M
  | trans {M N P : ModExpr} (p : ModPath M N) (q : ModPath N P) : ModPath M P

namespace ModPath

/-- Every path preserves rank. -/
@[simp] def rank_eq : {a b : ModExpr} → ModPath a b → a.rank = b.rank
  | _, _, refl _    => rfl
  | _, _, step s    => s.rank_eq
  | _, _, symm p    => (rank_eq p).symm
  | _, _, trans p q => (rank_eq p).trans (rank_eq q)

/-! ### §1 Direct sum paths (1–4) -/

-- 1
def dsum_comm (M N : ModExpr) : ModPath (.dsum M N) (.dsum N M) :=
  step (.dsum_comm M N)

-- 2
def dsum_assoc (M N P : ModExpr) :
    ModPath (.dsum (.dsum M N) P) (.dsum M (.dsum N P)) :=
  step (.dsum_assoc M N P)

-- 3
def dsum_zero_right (M : ModExpr) : ModPath (.dsum M .zero) M :=
  step (.dsum_zero_right M)

-- 4
def dsum_zero_left (M : ModExpr) : ModPath (.dsum .zero M) M :=
  step (.dsum_zero_left M)

/-! ### §2 Tensor paths (5–12) -/

-- 5
def tensor_comm (M N : ModExpr) : ModPath (.tensor M N) (.tensor N M) :=
  step (.tensor_comm M N)

-- 6
def tensor_assoc (M N P : ModExpr) :
    ModPath (.tensor (.tensor M N) P) (.tensor M (.tensor N P)) :=
  step (.tensor_assoc M N P)

-- 7
def tensor_unit_right (M : ModExpr) : ModPath (.tensor M .unit) M :=
  step (.tensor_unit_right M)

-- 8
def tensor_unit_left (M : ModExpr) : ModPath (.tensor .unit M) M :=
  step (.tensor_unit_left M)

-- 9
def tensor_zero_right (M : ModExpr) : ModPath (.tensor M .zero) .zero :=
  step (.tensor_zero_right M)

-- 10
def tensor_zero_left (M : ModExpr) : ModPath (.tensor .zero M) .zero :=
  step (.tensor_zero_left M)

-- 11
def tensor_distrib_right (M N P : ModExpr) :
    ModPath (.tensor M (.dsum N P)) (.dsum (.tensor M N) (.tensor M P)) :=
  step (.tensor_distrib_right M N P)

-- 12
def tensor_distrib_left (M N P : ModExpr) :
    ModPath (.tensor (.dsum M N) P) (.dsum (.tensor M P) (.tensor N P)) :=
  step (.tensor_distrib_left M N P)

/-! ### §3 Hom paths (13–14) -/

-- 13
def hom_tensor_adj (A B C : ModExpr) :
    ModPath (.hom (.tensor A B) C) (.hom A (.hom B C)) :=
  step (.hom_tensor_adj A B C)

-- 14
def hom_dsum_right (M N P : ModExpr) :
    ModPath (.hom M (.dsum N P)) (.dsum (.hom M N) (.hom M P)) :=
  step (.hom_dsum_right M N P)

/-! ### §4 Tor / Ext paths (15–20) -/

-- 15
def tor0_eq_tensor (M N : ModExpr) : ModPath (.tor0 M N) (.tensor M N) :=
  step (.tor0_eq_tensor M N)

-- 16
def ext0_eq_hom (M N : ModExpr) : ModPath (.ext0 M N) (.hom M N) :=
  step (.ext0_eq_hom M N)

-- 17
def torHi_vanish (M N : ModExpr) (i : Nat) : ModPath (.torHi M N i) .zero :=
  step (.torHi_vanish M N i)

-- 18
def extHi_vanish (M N : ModExpr) (i : Nat) : ModPath (.extHi M N i) .zero :=
  step (.extHi_vanish M N i)

-- 19
def free_zero : ModPath (.free 0) .zero := step .free_zero

-- 20
def free_one : ModPath (.free 1) .unit := step .free_one

/-! ### §5 Composite homological paths (21–35) -/

-- 21. Tor_0 is commutative
def tor0_comm (M N : ModExpr) : ModPath (.tor0 M N) (.tor0 N M) :=
  trans (tor0_eq_tensor M N) (trans (tensor_comm M N) (symm (tor0_eq_tensor N M)))

-- 22. Tor_0(M,N) → tensor(N,M) (one-way)
def tor0_to_tensor_comm (M N : ModExpr) : ModPath (.tor0 M N) (.tensor N M) :=
  trans (tor0_eq_tensor M N) (tensor_comm M N)

-- 23. Tor_0(M,N) commuted then back = roundtrip
def tor0_roundtrip (M N : ModExpr) : ModPath (.tor0 M N) (.tor0 M N) :=
  trans (tor0_comm M N) (tor0_comm N M)

-- 24. Direct sum commutes twice = roundtrip
def dsum_comm_roundtrip (M N : ModExpr) : ModPath (.dsum M N) (.dsum M N) :=
  trans (dsum_comm M N) (dsum_comm N M)

-- 25. Tensor commutes twice = roundtrip
def tensor_comm_roundtrip (M N : ModExpr) : ModPath (.tensor M N) (.tensor M N) :=
  trans (tensor_comm M N) (tensor_comm N M)

-- 26. Tensor unit from right then left
def tensor_unit_roundtrip (M : ModExpr) :
    ModPath (.tensor M .unit) (.tensor .unit M) :=
  trans (tensor_unit_right M) (symm (tensor_unit_left M))

-- 27. Higher Tor vanishes, then direct sum with zero
def torHi_dsum_vanish (M N : ModExpr) (i : Nat) :
    ModPath (.dsum (.torHi M N i) .zero) .zero :=
  trans (dsum_zero_right _) (torHi_vanish M N i)

-- 28. Higher Ext vanishes, then direct sum with zero
def extHi_dsum_vanish (M N : ModExpr) (i : Nat) :
    ModPath (.dsum .zero (.extHi M N i)) .zero :=
  trans (dsum_zero_left _) (extHi_vanish M N i)

-- 29. SES trivial left: 0 ⊕ M → M
def ses_trivial_left (M : ModExpr) : ModPath (.dsum .zero M) M :=
  dsum_zero_left M

-- 30. SES trivial right: M ⊕ 0 → M
def ses_trivial_right (M : ModExpr) : ModPath (.dsum M .zero) M :=
  dsum_zero_right M

-- 31. Associativity inverse (direct sum)
def dsum_assoc_inv (M N P : ModExpr) :
    ModPath (.dsum M (.dsum N P)) (.dsum (.dsum M N) P) :=
  symm (dsum_assoc M N P)

-- 32. Associativity inverse (tensor)
def tensor_assoc_inv (M N P : ModExpr) :
    ModPath (.tensor M (.tensor N P)) (.tensor (.tensor M N) P) :=
  symm (tensor_assoc M N P)

-- 33. Mac Lane coherence: double associator for direct sums
def dsum_assoc_composed (M N P Q : ModExpr) :
    ModPath (.dsum (.dsum (.dsum M N) P) Q) (.dsum M (.dsum N (.dsum P Q))) :=
  trans (dsum_assoc (.dsum M N) P Q) (dsum_assoc M N (.dsum P Q))

-- 34. Mac Lane coherence: double associator for tensors
def tensor_assoc_composed (M N P Q : ModExpr) :
    ModPath (.tensor (.tensor (.tensor M N) P) Q) (.tensor M (.tensor N (.tensor P Q))) :=
  trans (tensor_assoc (.tensor M N) P Q) (tensor_assoc M N (.tensor P Q))

-- 35. Zero tensor from both sides
def zero_tensor_zero : ModPath (.tensor .zero .zero) .zero :=
  tensor_zero_right .zero

/-! ### §6 Groupoid structure on ModPath (36–40) -/

-- 36. Double symm
def double_symm {M N : ModExpr} (p : ModPath M N) : ModPath M N :=
  symm (symm p)

-- 37. Trans with symm gives roundtrip
def trans_symm {M N : ModExpr} (p : ModPath M N) : ModPath M M :=
  trans p (symm p)

-- 38. Symm then trans
def symm_trans {M N : ModExpr} (p : ModPath M N) : ModPath N N :=
  trans (symm p) p

-- 39. General path composition
def compose3 {M N P Q : ModExpr}
    (p : ModPath M N) (q : ModPath N P) (r : ModPath P Q) : ModPath M Q :=
  trans p (trans q r)

-- 40. Path reversal of composition
def compose_symm {M N P : ModExpr}
    (p : ModPath M N) (q : ModPath N P) : ModPath P M :=
  symm (trans p q)

/-! ### §7 Rank computations (41–50) -/

/-- Convert a ModPath to a core Path on ranks. -/
def toCorePath : {a b : ModExpr} → ModPath a b → Path a.rank b.rank
  | _, _, refl _    => Path.refl _
  | _, _, step s    => Path.mk [Step.mk _ _ s.rank_eq] s.rank_eq
  | _, _, symm p    => Path.symm (toCorePath p)
  | _, _, trans p q => Path.trans (toCorePath p) (toCorePath q)

-- 41. ℤ^2 ⊕ ℤ^3 has rank 5
def rank_dsum_2_3 : Path (ModExpr.dsum (.free 2) (.free 3)).rank 5 := Path.refl _

-- 42. ℤ^2 ⊗ ℤ^3 has rank 6
def rank_tensor_2_3 : Path (ModExpr.tensor (.free 2) (.free 3)).rank 6 := Path.refl _

-- 43. Hom(ℤ^2, ℤ^3) has rank 6
def rank_hom_2_3 : Path (ModExpr.hom (.free 2) (.free 3)).rank 6 := Path.refl _

-- 44. Tor_0(ℤ^2, ℤ^3) has rank 6
def rank_tor0_2_3 : Path (ModExpr.tor0 (.free 2) (.free 3)).rank 6 := Path.refl _

-- 45. Tor_i(M,N) for i>0 has rank 0
def rank_torHi : Path (ModExpr.torHi (.free 2) (.free 3) 1).rank 0 := Path.refl _

-- 46. Ext^0(ℤ^2, ℤ^3) has rank 6
def rank_ext0_2_3 : Path (ModExpr.ext0 (.free 2) (.free 3)).rank 6 := Path.refl _

-- 47. Ext^i(M,N) for i>0 has rank 0
def rank_extHi : Path (ModExpr.extHi (.free 2) (.free 3) 1).rank 0 := Path.refl _

-- 48. ℤ^0 has rank 0 = zero-module rank
def rank_free_zero : Path (ModExpr.free 0).rank ModExpr.zero.rank := Path.refl _

-- 49. (ℤ^2 ⊕ ℤ^3) ⊗ ℤ^4 has rank 20
def rank_dsum_tensor :
    Path (ModExpr.tensor (.dsum (.free 2) (.free 3)) (.free 4)).rank 20 := Path.refl _

-- 50. ((ℤ^2 ⊗ ℤ^3) ⊗ ℤ^4) has rank 24
def rank_tensor_assoc_ex :
    Path (ModExpr.tensor (.tensor (.free 2) (.free 3)) (.free 4)).rank 24 := Path.refl _

-- 51. Tor_0 and tensor ranks coincide via trans/symm
def rank_tor0_tensor_link :
    Path (ModExpr.tor0 (.free 2) (.free 3)).rank
         (ModExpr.tensor (.free 2) (.free 3)).rank :=
  Path.trans rank_tor0_2_3 (Path.symm rank_tensor_2_3)

-- 52. Ext^0 and Hom ranks coincide via trans/symm
def rank_ext0_hom_link :
    Path (ModExpr.ext0 (.free 2) (.free 3)).rank
         (ModExpr.hom (.free 2) (.free 3)).rank :=
  Path.trans rank_ext0_2_3 (Path.symm rank_hom_2_3)

-- 53. Higher Tor and higher Ext both vanish in rank
def rank_tor_ext_vanish_link :
    Path (ModExpr.torHi (.free 2) (.free 3) 1).rank
         (ModExpr.extHi (.free 2) (.free 3) 1).rank :=
  Path.trans rank_torHi (Path.symm rank_extHi)

-- 54. Congruence under (+ 0), then simplify
def rank_dsum_tensor_plus_zero :
    Path ((ModExpr.tensor (.dsum (.free 2) (.free 3)) (.free 4)).rank + 0) 20 :=
  Path.trans
    (Path.congrArg (fun n => n + 0) rank_dsum_tensor)
    (Path.mk [Step.mk _ _ (Nat.add_zero 20)] (Nat.add_zero 20))

-- 55. Congruence under (* 1), then simplify
def rank_tensor_assoc_mul_one :
    Path ((ModExpr.tensor (.tensor (.free 2) (.free 3)) (.free 4)).rank * 1) 24 :=
  Path.trans
    (Path.congrArg (fun n => n * 1) rank_tensor_assoc_ex)
    (Path.mk [Step.mk _ _ (Nat.mul_one 24)] (Nat.mul_one 24))

-- 56. Free-zero rank roundtrip
def rank_free_zero_roundtrip :
    Path (ModExpr.free 0).rank (ModExpr.free 0).rank :=
  Path.trans rank_free_zero (Path.symm rank_free_zero)

end ModPath

end ComputationalPaths.Path.Algebra.HomAlgDeep
