/-
# Synthetic homotopy theory: higher paths and loop spaces

Develops loop spaces, loop-space functors, path-space
characterizations for product / sigma types, all witnessed
by explicit `Path.Step` / `RwEq` rewriting.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Synthetic.HomotopyPaths
import ComputationalPaths.Synthetic.FiberEquiv

namespace ComputationalPaths
namespace Synthetic

open Path

universe u v

variable {A : Type u}

/-! ## Loop spaces -/

abbrev Ω (a : A) : Type u := Path a a

abbrev Ω2 (a : A) : Type u := Path (Path.refl a) (Path.refl a)

noncomputable def loopConcat {a : A} (p q : Ω a) : Ω a :=
  Path.trans p q

noncomputable def loopInv {a : A} (p : Ω a) : Ω a :=
  Path.symm p

noncomputable def loopRefl (a : A) : Ω a := Path.refl a

/-! ## Loop space group laws via Step -/

theorem loopConcat_assoc {a : A} (p q r : Ω a) :
    Path.Step (loopConcat (loopConcat p q) r) (loopConcat p (loopConcat q r)) :=
  Path.Step.trans_assoc p q r

theorem loopConcat_left_unit {a : A} (p : Ω a) :
    Path.Step (loopConcat (loopRefl a) p) p :=
  Path.Step.trans_refl_left p

theorem loopConcat_right_unit {a : A} (p : Ω a) :
    Path.Step (loopConcat p (loopRefl a)) p :=
  Path.Step.trans_refl_right p

theorem loopConcat_right_inv {a : A} (p : Ω a) :
    Path.Step (loopConcat p (loopInv p)) (loopRefl a) :=
  Path.Step.trans_symm p

theorem loopConcat_left_inv {a : A} (p : Ω a) :
    Path.Step (loopConcat (loopInv p) p) (loopRefl a) :=
  Path.Step.symm_trans p

theorem loopInv_involutive {a : A} (p : Ω a) :
    Path.Step (loopInv (loopInv p)) p :=
  Path.Step.symm_symm p

theorem loopInv_concat {a : A} (p q : Ω a) :
    Path.Step (loopInv (loopConcat p q)) (loopConcat (loopInv q) (loopInv p)) :=
  Path.Step.symm_trans_congr p q

/-! ## RwEq versions -/

noncomputable def loopConcat_assoc_rweq {a : A} (p q r : Ω a) :
    RwEq (loopConcat (loopConcat p q) r) (loopConcat p (loopConcat q r)) :=
  RwEq.step (loopConcat_assoc p q r)

noncomputable def loopConcat_left_unit_rweq {a : A} (p : Ω a) :
    RwEq (loopConcat (loopRefl a) p) p :=
  RwEq.step (loopConcat_left_unit p)

noncomputable def loopConcat_right_unit_rweq {a : A} (p : Ω a) :
    RwEq (loopConcat p (loopRefl a)) p :=
  RwEq.step (loopConcat_right_unit p)

noncomputable def loopConcat_right_inv_rweq {a : A} (p : Ω a) :
    RwEq (loopConcat p (loopInv p)) (loopRefl a) :=
  RwEq.step (loopConcat_right_inv p)

noncomputable def loopConcat_left_inv_rweq {a : A} (p : Ω a) :
    RwEq (loopConcat (loopInv p) p) (loopRefl a) :=
  RwEq.step (loopConcat_left_inv p)

/-! ## Loop space ap (functoriality of Ω) -/

noncomputable def loopAp {B : Type u} (f : A → B) {a : A} (p : Ω a) : Ω (f a) :=
  Path.congrArg f p

noncomputable def loopAp_refl {B : Type u} (f : A → B) (a : A) :
    loopAp f (loopRefl a) = loopRefl (f a) := by
  simp [loopAp, loopRefl, Path.congrArg, Path.refl]

/-! ## Path spaces of product types -/

variable {B : Type u}

noncomputable def prodPathEquiv {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) : Path a₁ a₂ × Path b₁ b₂ :=
  (Path.fst p, Path.snd p)

noncomputable def prodPathMk {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) :=
  Path.prodMk p q

noncomputable def prodPath_roundtrip_rweq {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (prodPathMk (prodPathEquiv p).1 (prodPathEquiv p).2) p :=
  RwEq.step (Path.Step.prod_eta p)

/-! ## Path spaces of sigma types -/

noncomputable def sigmaPathFst {C : A → Type u} {x y : Sigma C}
    (p : Path x y) : Path x.1 y.1 :=
  Path.congrArg Sigma.fst p

noncomputable def sigmaPathMk_refl {C : A → Type u} {a : A} {c₁ c₂ : C a}
    (q : Path c₁ c₂) : Path (⟨a, c₁⟩ : Sigma C) ⟨a, c₂⟩ :=
  Path.congrArg (Sigma.mk a) q

/-! ## Pointed types and loop space pointed functor -/

/-- The loop space of a pointed type as a pointed type. -/
noncomputable def loopSpacePointed (X : Pointed) : Pointed where
  carrier := Ω X.basepoint
  basepoint := loopRefl X.basepoint

/-- The double loop space. -/
noncomputable def loopSpacePointed2 (X : Pointed) : Pointed :=
  loopSpacePointed (loopSpacePointed X)

/-- The loop-space induced map (not necessarily pointed). -/
noncomputable def loopSpaceFun {X Y : Pointed} (f : PointedMap X Y) :
    Ω X.basepoint → Ω Y.basepoint :=
  fun p => Path.trans (Path.symm f.preserves)
             (Path.trans (Path.congrArg f.toFun p) f.preserves)

/-! ## Higher coherences for loop space -/

/-- Pentagon identity for loops. -/
noncomputable def loop_pentagon {a : A} (p q r s : Ω a) :
    RwEq (loopConcat (loopConcat (loopConcat p q) r) s)
         (loopConcat p (loopConcat q (loopConcat r s))) :=
  RwEq.trans
    (RwEq.step (Path.Step.trans_assoc (loopConcat p q) r s))
    (RwEq.step (Path.Step.trans_assoc p q (loopConcat r s)))

/-- Inverse distributes over concatenation (for loops). -/
noncomputable def loop_inv_concat_rweq {a : A} (p q : Ω a) :
    RwEq (loopInv (loopConcat p q)) (loopConcat (loopInv q) (loopInv p)) :=
  RwEq.step (loopInv_concat p q)

/-- Double inverse is identity (for loops). -/
noncomputable def loop_inv_inv_rweq {a : A} (p : Ω a) :
    RwEq (loopInv (loopInv p)) p :=
  RwEq.step (loopInv_involutive p)

/-- Conjugation by a loop: p ↦ q · p · q⁻¹. -/
noncomputable def loopConjugate {a : A} (q p : Ω a) : Ω a :=
  loopConcat (loopConcat q p) (loopInv q)

/-- Conjugation by refl is identity. -/
noncomputable def loopConjugate_refl_rweq {a : A} (p : Ω a) :
    RwEq (loopConjugate (loopRefl a) p) p :=
  RwEq.trans
    (rweq_trans_congr_left (loopInv (loopRefl a))
      (RwEq.step (Path.Step.trans_refl_left p)))
    (RwEq.trans
      (RwEq.step (Path.Step.trans_refl_right p))
      (RwEq.refl p))

/-- Conjugation preserves the identity loop. -/
noncomputable def loopConjugate_id_rweq {a : A} (q : Ω a) :
    RwEq (loopConjugate q (loopRefl a)) (loopRefl a) :=
  RwEq.trans
    (rweq_trans_congr_left (loopInv q)
      (RwEq.step (Path.Step.trans_refl_right q)))
    (RwEq.step (Path.Step.trans_symm q))

end Synthetic
end ComputationalPaths
