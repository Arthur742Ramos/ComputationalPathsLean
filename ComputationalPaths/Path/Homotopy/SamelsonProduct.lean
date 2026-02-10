/-
# Samelson Product on Loop Spaces

This module defines the Samelson product on based loop spaces in the
computational paths setting. The product is the loop commutator
`p * q * p^{-1} * q^{-1}`, expressed using `Path` concatenation and symmetry,
with basic RwEq properties.

## Key Results

- `samelson`: Samelson product on `LoopSpace`
- `samelson_congr`: respects `RwEq` in each variable
- `samelson_refl_left` / `samelson_refl_right`: unit laws up to `RwEq`
- `samelson_self`: self-commutator is `RwEq` to `refl`

## References

- Samelson, "A connection between the Whitehead and Pontrjagin products" (1953)
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.LoopDerived

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace SamelsonProduct

universe u

variable {A : Type u} {a : A}

/-- The Samelson product on loops: the loop commutator. -/
@[simp] def samelson (p q : LoopSpace A a) : LoopSpace A a :=
  Path.trans (Path.trans (Path.trans p q) (Path.symm p)) (Path.symm q)

/-- Samelson product respects rewrite equivalence in both variables. -/
theorem samelson_congr {p p' q q' : LoopSpace A a}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (samelson p q) (samelson p' q') := by
  have hq_symm : RwEq (Path.symm q) (Path.symm q') :=
    rweq_symm_congr hq
  have hp_symm : RwEq (Path.symm p) (Path.symm p') :=
    rweq_symm_congr hp
  have h1 : RwEq (Path.trans p q) (Path.trans p' q') :=
    rweq_trans_congr hp hq
  have h2 :
      RwEq (Path.trans (Path.trans p q) (Path.symm p))
        (Path.trans (Path.trans p' q') (Path.symm p')) :=
    rweq_trans_congr h1 hp_symm
  have h3 :
      RwEq (Path.trans (Path.trans (Path.trans p q) (Path.symm p)) (Path.symm q))
        (Path.trans (Path.trans (Path.trans p' q') (Path.symm p')) (Path.symm q')) :=
    rweq_trans_congr h2 hq_symm
  simpa [samelson] using h3

/-- Samelson product with the identity loop on the left is trivial. -/
@[simp] theorem samelson_refl_left (p : LoopSpace A a) :
    RwEq (samelson (LoopSpace.id (A := A) (a := a)) p)
      (LoopSpace.id (A := A) (a := a)) := by
  have h1 :
      RwEq (Path.trans
        (Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a)))
        (Path.symm p))
        (Path.trans p (Path.symm p)) := by
    exact
      rweq_trans_congr_left (Path.symm p)
        (LoopDerived.rweq_loop_conj_refl (a := a) (q := p))
  have h2 : RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
    LoopDerived.rweq_loop_inv_right (a := a) (p := p)
  simpa [samelson, LoopSpace.id] using (RwEq.trans h1 h2)

/-- Samelson product with the identity loop on the right is trivial. -/
@[simp] theorem samelson_refl_right (p : LoopSpace A a) :
    RwEq (samelson p (LoopSpace.id (A := A) (a := a)))
      (LoopSpace.id (A := A) (a := a)) := by
  have h1 :
      RwEq (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
        (Path.trans p (Path.symm p)) := by
    exact
      rweq_trans_congr_left (Path.symm p)
        (LoopDerived.rweq_loop_unit_right (a := a) (p := p))
  have h2 :
      RwEq
        (Path.trans (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
          (Path.symm (Path.refl a)))
        (Path.trans (Path.trans p (Path.symm p)) (Path.symm (Path.refl a))) := by
    exact rweq_trans_congr_left (Path.symm (Path.refl a)) h1
  have h3 : RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
    rweq_of_step (Step.symm_refl a)
  have h4 :
      RwEq (Path.trans (Path.trans p (Path.symm p)) (Path.symm (Path.refl a)))
        (Path.trans (Path.trans p (Path.symm p)) (Path.refl a)) := by
    exact rweq_trans_congr_right (Path.trans p (Path.symm p)) h3
  have h5 :
      RwEq (Path.trans (Path.trans p (Path.symm p)) (Path.refl a))
        (Path.trans p (Path.symm p)) :=
    LoopDerived.rweq_loop_unit_right (a := a) (p := Path.trans p (Path.symm p))
  have h6 : RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
    LoopDerived.rweq_loop_inv_right (a := a) (p := p)
  simpa [samelson, LoopSpace.id] using
    (RwEq.trans h2 (RwEq.trans h4 (RwEq.trans h5 h6)))

/-- Self-commutator is trivial in the loop space. -/
@[simp] theorem samelson_self (p : LoopSpace A a) :
    RwEq (samelson p p) (LoopSpace.id (A := A) (a := a)) := by
  simpa [samelson, LoopSpace.id] using
    (LoopDerived.rweq_loop_self_commutator (a := a) (p := p))

end SamelsonProduct
end Homotopy
end Path
end ComputationalPaths
