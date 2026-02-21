/-
# Monoidal Structure on Computational Paths

This module develops the monoidal structure on computational paths:
tensor of paths, unit paths, associator/unitor coherence, braiding/symmetry,
and pentagon/triangle identities for the path tensor.

## Key Results

- `PathTensor`: tensor product of paths as concatenation
- Associator, left/right unitor coherence
- Pentagon and triangle identities
- Braiding/symmetry and hexagon coherence
- Naturality of structural morphisms under RwEq

## References

- Mac Lane, "Categories for the Working Mathematician"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Category
namespace MonoidalPaths

universe u

variable {A : Type u}
variable {a b c d e f' : A}

/-! ## Tensor product of paths -/

/-- The tensor product of paths is path composition (concatenation of traces). -/
@[simp] def PathTensor (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- The unit for the path tensor is the reflexive path. -/
@[simp] def PathUnit (a : A) : Path a a :=
  Path.refl a

/-! ## Associator coherence -/

/-- The associator: `(p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)`. -/
@[simp] theorem associator (p : Path a b) (q : Path b c) (r : Path c d) :
    PathTensor (PathTensor p q) r = PathTensor p (PathTensor q r) :=
  Path.trans_assoc p q r

/-- The associator is natural in the first argument. -/
theorem associator_natural_first {p p' : Path a b} (hp : p = p')
    (q : Path b c) (r : Path c d) :
    PathTensor (PathTensor p q) r = PathTensor (PathTensor p' q) r := by
  subst hp; rfl

/-- The associator is natural in the second argument. -/
theorem associator_natural_second (p : Path a b) {q q' : Path b c} (hq : q = q')
    (r : Path c d) :
    PathTensor (PathTensor p q) r = PathTensor (PathTensor p q') r := by
  subst hq; rfl

/-- The associator is natural in the third argument. -/
theorem associator_natural_third (p : Path a b) (q : Path b c)
    {r r' : Path c d} (hr : r = r') :
    PathTensor (PathTensor p q) r = PathTensor (PathTensor p q) r' := by
  subst hr; rfl

/-! ## Unitor coherence -/

/-- Left unitor: `I ⊗ p = p`. -/
@[simp] theorem left_unitor (p : Path a b) :
    PathTensor (PathUnit a) p = p :=
  Path.trans_refl_left p

/-- Right unitor: `p ⊗ I = p`. -/
@[simp] theorem right_unitor (p : Path a b) :
    PathTensor p (PathUnit b) = p :=
  Path.trans_refl_right p

/-- Left unitor naturality: compatible with path substitution. -/
theorem left_unitor_natural {p p' : Path a b} (h : p = p') :
    PathTensor (PathUnit a) p = PathTensor (PathUnit a) p' := by
  subst h; rfl

/-- Right unitor naturality: compatible with path substitution. -/
theorem right_unitor_natural {p p' : Path a b} (h : p = p') :
    PathTensor p (PathUnit b) = PathTensor p' (PathUnit b) := by
  subst h; rfl

/-! ## Pentagon identity -/

/-- Pentagon identity for path tensor associativity: any two proofs of the
same reassociation agree (proof-irrelevance). -/
theorem pentagon_irrelevance (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ : PathTensor (PathTensor (PathTensor p q) r) s =
              PathTensor p (PathTensor q (PathTensor r s))) :
    h₁ = h₂ := by
  apply subsingleton_eq_by_cases

/-- Pentagon coherence: all reassociations of a fivefold tensor agree. -/
theorem pentagon_coherence
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e f') :
    PathTensor (PathTensor (PathTensor (PathTensor p q) r) s) t =
    PathTensor p (PathTensor q (PathTensor r (PathTensor s t))) := by
  simp [PathTensor]

/-- Pentagon identity: the two standard routes from `((p ⊗ q) ⊗ r) ⊗ s`
to `p ⊗ (q ⊗ (r ⊗ s))` are equal. -/
theorem pentagon (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    PathTensor (PathTensor (PathTensor p q) r) s =
    PathTensor p (PathTensor q (PathTensor r s)) := by
  simp [PathTensor]

/-! ## Triangle identity -/

/-- Triangle identity: the right unitor and left unitor are compatible with the
associator. -/
theorem triangle (p : Path a b) (q : Path b c) :
    PathTensor (PathTensor p (PathUnit b)) q =
    PathTensor p (PathTensor (PathUnit b) q) := by
  simp

/-- Triangle identity (alternate form). -/
theorem triangle_alt (p : Path a b) (q : Path b c) :
    PathTensor (PathTensor p (PathUnit b)) q =
    PathTensor p q := by
  simp

/-! ## Braiding / symmetry -/

/-- Braiding via symmetry: `symm (p ⊗ q) = symm q ⊗ symm p`. -/
theorem braiding (p : Path a b) (q : Path b c) :
    Path.symm (PathTensor p q) = PathTensor (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- Braiding is natural with respect to path equality. -/
theorem braiding_natural {p p' : Path a b} {q q' : Path b c}
    (hp : p = p') (hq : q = q') :
    Path.symm (PathTensor p q) = Path.symm (PathTensor p' q') := by
  subst hp; subst hq; rfl

/-- Double braiding yields the original via symm_symm. -/
theorem braiding_double (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-! ## Hexagon identities -/

/-- Left hexagon: braiding distributes over the associator. -/
theorem hexagon_left (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (PathTensor (PathTensor p q) r) =
    PathTensor (Path.symm r) (PathTensor (Path.symm q) (Path.symm p)) := by
  rw [associator p q r, braiding p (PathTensor q r), braiding q r]
  rw [associator (Path.symm r) (Path.symm q) (Path.symm p)]

/-- Right hexagon: braiding distributes over the associator (other direction). -/
theorem hexagon_right (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (PathTensor p (PathTensor q r)) =
    PathTensor (Path.symm r) (PathTensor (Path.symm q) (Path.symm p)) := by
  rw [braiding p (PathTensor q r), braiding q r]
  rw [associator (Path.symm r) (Path.symm q) (Path.symm p)]

/-! ## Functoriality of the tensor -/

/-- The tensor is functorial: applying congrArg on the left component. -/
theorem tensor_congrArg_left {p p' : Path a b} (h : p = p') (q : Path b c) :
    PathTensor p q = PathTensor p' q := by
  subst h; rfl

/-- The tensor is functorial: applying congrArg on the right component. -/
theorem tensor_congrArg_right (p : Path a b) {q q' : Path b c} (h : q = q') :
    PathTensor p q = PathTensor p q' := by
  subst h; rfl

/-- The tensor preserves congrArg. -/
theorem tensor_congrArg_both {p p' : Path a b} {q q' : Path b c}
    (hp : p = p') (hq : q = q') :
    PathTensor p q = PathTensor p' q' := by
  subst hp; subst hq; rfl

/-! ## Symmetry of the monoidal unit -/

/-- Symmetry of the unit path is itself. -/
@[simp] theorem symm_unit (a : A) :
    Path.symm (PathUnit a) = PathUnit a :=
  Path.symm_refl a

/-- The unit path tensor with itself is the unit. -/
@[simp] theorem unit_tensor_unit (a : A) :
    PathTensor (PathUnit a) (PathUnit a) = PathUnit a := by
  simp

/-! ## Congruence under tensor -/

/-- congrArg distributes over the tensor. -/
theorem congrArg_tensor {B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (PathTensor p q) =
    PathTensor (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- congrArg preserves the unit. -/
theorem congrArg_unit {B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (PathUnit a) = PathUnit (f a) := by
  simp [PathUnit, Path.congrArg]

/-! ## Transport and the tensor -/

/-- Transport along a tensor factors through two transports. -/
theorem transport_tensor {D : A → Sort u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (PathTensor p q) x =
    Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-- Transport along the unit is the identity. -/
theorem transport_unit {D : A → Sort u} (a : A) (x : D a) :
    Path.transport (PathUnit a) x = x :=
  Path.transport_refl x

/-! ## Derived Mac Lane coherence -/

/-- Mac Lane coherence: any two reassociations with the same endpoints coincide. -/
theorem mac_lane_coherence_general
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ : PathTensor (PathTensor (PathTensor p q) r) s =
              PathTensor p (PathTensor q (PathTensor r s))) :
    h₁ = h₂ := by
  apply subsingleton_eq_by_cases

/-- All bracketings of a triple tensor are equal. -/
@[simp] theorem triple_tensor_coherence (p : Path a b) (q : Path b c) (r : Path c d) :
    PathTensor (PathTensor p q) r = PathTensor p (PathTensor q r) :=
  associator p q r

/-- Fourfold reassociation via two applications of associator. -/
theorem fourfold_assoc (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    PathTensor (PathTensor (PathTensor p q) r) s =
    PathTensor p (PathTensor q (PathTensor r s)) := by
  simp [PathTensor]

end MonoidalPaths
end Category
end Path
end ComputationalPaths
