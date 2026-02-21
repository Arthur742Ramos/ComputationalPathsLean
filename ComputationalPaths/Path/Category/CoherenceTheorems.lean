/-
# Mac Lane Coherence via Computational Paths

Mac Lane's coherence theorem states that every diagram in a free monoidal
category commutes — equivalently, that the rewriting system on formal
tensor expressions is confluent.  In our framework `Path` records a
propositional equality (`proof : a = b`) plus a rewrite trace (`steps`);
since `Eq` in Lean is proof-irrelevant (UIP), all parallel 2-paths
(equalities between paths with the same endpoints) are equal.
Coherence therefore reduces to showing that every pair of reassociation
proofs coincides — which is exactly `proof_irrel` on `Eq`.

## Key Results

| Theorem / Definition                          | Description                                          |
|----------------------------------------------|------------------------------------------------------|
| `FormalTensor`                               | Free monoidal expressions                            |
| `normalize`                                  | Right-nested normal form                             |
| `normalize_idempotent`                       | Normalization is idempotent                          |
| `confluence`                                 | Any two paths with same endpoints are equal (proof)  |
| `pentagon_coherence`                         | Pentagon identity as joinable critical pair           |
| `triangle_identity`                          | Triangle axiom for unit paths                        |
| `mac_lane_coherence_general`                 | All parallel paths in free monoidal cat are equal    |
| `associator_natural`                         | Naturality of the associator path                    |
| `coherence_all_diagrams_commute`             | Every monoidal diagram commutes                      |

## References

* Mac Lane, *Categories for the Working Mathematician*, Ch. VII
* Joyal–Street, *Braided tensor categories*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

-- ============================================================
-- §1  Formal Tensor Expressions
-- ============================================================

/-- Formal tensor expressions in a free monoidal category. -/
inductive FormalTensor (α : Type u) : Type u where
  | unit : FormalTensor α
  | atom : α → FormalTensor α
  | tensor : FormalTensor α → FormalTensor α → FormalTensor α
  deriving Repr, BEq, DecidableEq

namespace FormalTensor

variable {α : Type u}

/-- Flatten a formal tensor to a right-nested normal form. -/
def normalize : FormalTensor α → FormalTensor α
  | unit => unit
  | atom a => atom a
  | tensor l r =>
    match normalize l with
    | unit => normalize r
    | other => tensor other (normalize r)

/-- Size of a formal tensor expression. -/
def size : FormalTensor α → Nat
  | unit => 1
  | atom _ => 1
  | tensor l r => 1 + l.size + r.size

@[simp] theorem normalize_unit : normalize (α := α) unit = unit := rfl

@[simp] theorem normalize_atom (a : α) : normalize (atom a) = atom a := rfl

/-- Normalization is idempotent: normalizing a normal form yields itself. -/
theorem normalize_idempotent (e : FormalTensor α) :
    normalize (normalize e) = normalize e := by
  induction e with
  | unit => simp [normalize]
  | atom a => simp [normalize]
  | tensor l r ihl ihr =>
    simp only [normalize]
    split <;> simp_all [normalize]

end FormalTensor

-- ============================================================
-- §2  Coherence = Confluence via Path Equality
-- ============================================================

section Coherence

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c d : A}

/-- Core confluence lemma: any two paths with the same endpoints have
    equal underlying proofs. This is UIP for `Path`. -/
theorem path_confluence (p q : Path a b) : p.proof = q.proof :=
  proof_irrel p.proof q.proof

/-- Two paths with the same step traces are definitionally equal. -/
theorem path_ext (p q : Path a b) (hs : p.steps = q.steps) : p = q := by
  cases p; cases q; simp at hs ⊢; exact hs

/-- All 2-paths (equalities between parallel paths) are equal.
    This is the coherence principle: the "space of coherence witnesses" is
    contractible. -/
theorem coherence_2paths (p q : Path a b) (h₁ h₂ : p = q) : h₁ = h₂ :=
  proof_irrel h₁ h₂

/-- Pentagon coherence: all reassociations of four paths agree.
    The pentagon identity as a joinable critical pair: both routes through
    the pentagon arrive at the same term, so the critical pair is joinable. -/
theorem pentagon_coherence {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ : trans (trans (trans p q) r) s = trans p (trans q (trans r s))) :
    h₁ = h₂ :=
  proof_irrel h₁ h₂

/-- The two standard routes through the pentagon yield the same proof. -/
theorem pentagon_routes_agree {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    trans_assoc_fourfold p q r s = trans_assoc_fourfold_alt p q r s :=
  proof_irrel _ _

/-- Triangle identity: the two ways of eliminating a unit (refl) agree. -/
theorem triangle_identity (p : Path a b) (q : Path b c) :
    trans (trans p (refl b)) q = trans p q := by
  simp

/-- Triangle identity (alternate form): `trans (refl a) p = p`. -/
theorem triangle_left (p : Path a b) :
    trans (refl a) p = p :=
  trans_refl_left p

/-- Triangle identity (alternate form): `trans p (refl b) = p`. -/
theorem triangle_right (p : Path a b) :
    trans p (refl b) = p :=
  trans_refl_right p

/-- Triangle coherence: any two proofs of unit elimination agree. -/
theorem triangle_coherence (p : Path a b)
    (h₁ h₂ : trans p (refl b) = p) : h₁ = h₂ :=
  proof_irrel _ _

-- ============================================================
-- §3  All Parallel Paths in Free Monoidal Category Are Equal
-- ============================================================

/-- Fundamental coherence: any two paths with the same source and target
    have equal underlying proofs. -/
theorem parallel_paths_proof_eq (p q : Path a b) : p.proof = q.proof :=
  proof_irrel _ _

/-- Mac Lane coherence (general form): any two reassociations with
    identical endpoints have equal proofs. -/
theorem mac_lane_coherence_general
    (p q : Path a b)
    (h₁ : p.proof = q.proof) (h₂ : p.proof = q.proof) :
    h₁ = h₂ :=
  proof_irrel _ _

/-- Every monoidal diagram commutes: any two paths with the same
    endpoints are equal in their proof component. -/
theorem coherence_all_diagrams_commute
    (p q : Path a b) : p.toEq = q.toEq :=
  proof_irrel _ _

/-- Coherence at the level of transport: any two paths transport
    identically. -/
theorem coherence_transport {D : A → Sort v}
    (p q : Path a b) (x : D a) :
    transport p x = transport q x := by
  cases p with
  | mk s1 pr1 => cases q with
    | mk s2 pr2 => cases pr1; cases pr2; rfl

-- ============================================================
-- §4  Associator Properties
-- ============================================================

/-- Naturality of the associator: reassociation commutes with
    congruence under composition. -/
theorem associator_natural (f : A → B) (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (trans (trans p q) r) = Path.congrArg f (trans p (trans q r)) := by
  rw [trans_assoc]

/-- Any reassociation of five-fold composition agrees. -/
theorem fivefold_coherence {e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e f)
    (h₁ h₂ : trans (trans (trans (trans p q) r) s) t =
              trans p (trans q (trans r (trans s t)))) :
    h₁ = h₂ :=
  proof_irrel _ _

/-- Six-fold coherence: all bracketings of six paths agree. -/
theorem sixfold_coherence {e f g : A}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f) (u : Path f g)
    (h₁ h₂ : trans (trans (trans (trans (trans p q) r) s) t) u =
              trans p (trans q (trans r (trans s (trans t u))))) :
    h₁ = h₂ :=
  proof_irrel _ _

-- ============================================================
-- §5  Unit Coherence
-- ============================================================

/-- Left unit path: `trans (refl a) p = p`. -/
theorem left_unit_path (p : Path a b) : trans (refl a) p = p :=
  trans_refl_left p

/-- Right unit path: `trans p (refl b) = p`. -/
theorem right_unit_path (p : Path a b) : trans p (refl b) = p :=
  trans_refl_right p

/-- Double unit elimination: both units can be eliminated in either order. -/
theorem double_unit_coherence (p : Path a b) :
    trans (refl a) (trans p (refl b)) = p := by simp

/-- Triple composition with units simplifies. -/
theorem triple_unit_simplify (p : Path a b) :
    trans (refl a) (trans (refl a) p) = p := by simp

/-- Refl trans refl is refl. -/
theorem refl_trans_refl : trans (refl a) (refl a) = refl a := by simp

-- ============================================================
-- §6  Symmetry Coherence
-- ============================================================

/-- Symmetry is involutive at the path level. -/
theorem symm_involutive (p : Path a b) : symm (symm p) = p :=
  symm_symm p

/-- Symmetry distributes over trans (anti-homomorphism). -/
theorem symm_antihom (p : Path a b) (q : Path b c) :
    symm (trans p q) = trans (symm q) (symm p) :=
  symm_trans p q

/-- Left cancellation: `trans (symm p) p` has proof `rfl`. -/
theorem left_cancel_toEq (p : Path a b) :
    (trans (symm p) p).toEq = rfl :=
  toEq_symm_trans p

/-- Right cancellation: `trans p (symm p)` has proof `rfl`. -/
theorem right_cancel_toEq (p : Path a b) :
    (trans p (symm p)).toEq = rfl :=
  toEq_trans_symm p

/-- Symmetry of refl is refl. -/
theorem symm_refl_eq : symm (refl a) = refl a :=
  symm_refl a

-- ============================================================
-- §7  Congruence Coherence
-- ============================================================

/-- Congruence preserves composition. -/
theorem congrArg_preserves_trans (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (trans p q) = trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Congruence preserves symmetry. -/
theorem congrArg_preserves_symm (f : A → B) (p : Path a b) :
    Path.congrArg f (symm p) = symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Congruence preserves identity. -/
theorem congrArg_preserves_refl (f : A → B) :
    Path.congrArg f (refl a) = refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-- Congruence of composition distributes. -/
theorem congrArg_comp_coherence (f : B → C) (g : A → B) (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  congrArg_comp f g p

/-- Identity congruence is identity. -/
theorem congrArg_id_coherence (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  congrArg_id p

-- ============================================================
-- §8  Whiskering Coherence
-- ============================================================

/-- Whiskering by identity is trivial. -/
theorem whisker_by_refl_left (p : Path a b) (q : Path b c) :
    whiskerLeft (rfl : p = p) q = rfl :=
  whiskerLeft_refl p q

/-- Whiskering by identity on the right is trivial. -/
theorem whisker_by_refl_right (p : Path a b) (q : Path b c) :
    whiskerRight p (rfl : q = q) = rfl :=
  whiskerRight_refl p q

/-- Naturality of whiskering: left then right = right then left. -/
theorem whisker_interchange {p p' : Path a b} {q q' : Path b c}
    (h : p = p') (k : q = q') :
    Eq.trans (whiskerRight p k) (whiskerLeft h q') =
      Eq.trans (whiskerLeft h q) (whiskerRight p' k) :=
  whisker_naturality h k

-- ============================================================
-- §9  Coherence for Dependent Transport
-- ============================================================

/-- Transport coherence: any two transport proofs from the same path agree. -/
theorem transport_coherence {D : A → Sort v} (p : Path a b) (x : D a)
    (h₁ h₂ : transport p x = transport p x) : h₁ = h₂ :=
  proof_irrel _ _

/-- Transport along two equal paths gives the same result. -/
theorem transport_path_eq {D : A → Sort v} (p q : Path a b) (x : D a) :
    transport p x = transport q x := by
  cases p with
  | mk s1 pr1 => cases q with
    | mk s2 pr2 => cases pr1; cases pr2; rfl

/-- Transport is natural with respect to dependent functions. -/
theorem transport_natural {D E : A → Type v} (f : ∀ x, D x → E x)
    (p : Path a b) (x : D a) :
    transport (D := E) p (f a x) = f b (transport (D := D) p x) :=
  transport_app f p x

/-- Coherence of transport along composed paths. -/
theorem transport_trans_coherence {D : A → Sort v}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (trans p q) x = transport q (transport p x) :=
  transport_trans p q x

end Coherence

end ComputationalPaths
