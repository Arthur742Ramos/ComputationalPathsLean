/-
# Challenge: a self-contained computational-path coherence certificate

This file is deliberately independent of the repository's implementation
modules.  Palomar checks the transitive source closure of Challenge, so the
statement boundary contains its own small trace-carrying path calculus and
the Type-valued rewrite presentations used by the theorem below.  The proof
is supplied separately in `Solution.lean`.
-/

import Mathlib

set_option linter.dupNamespace false

namespace ComputationalPaths.Path.PalomarOmegaGroupoid433

universe u

/-! ## Trace-carrying paths -/

structure Step (A : Type u) where
  src : A
  tgt : A
  proof : src = tgt

namespace Step

def symm {A : Type u} (s : Step A) : Step A :=
  ⟨s.tgt, s.src, s.proof.symm⟩

end Step

structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b

namespace Path

def refl {A : Type u} (a : A) : Path a a :=
  ⟨[], rfl⟩

def ofEq {A : Type u} {a b : A} (h : a = b) : Path a b :=
  ⟨[⟨a, b, h⟩], h⟩

def trans {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  ⟨p.steps ++ q.steps, p.proof.trans q.proof⟩

def symm {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  ⟨p.steps.reverse.map Step.symm, p.proof.symm⟩

@[simp] theorem trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    trans (refl a) p = p := by
  cases p
  simp [trans, refl]

@[simp] theorem trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    trans p (refl b) = p := by
  cases p
  simp [trans, refl]

theorem trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) := by
  cases p
  cases q
  cases r
  simp [trans, List.append_assoc]

theorem ofEq_ne_refl {A : Type u} (a : A) :
    ofEq (rfl : a = a) ≠ refl a := by
  intro h
  have hs := congrArg (fun p : Path a a => p.steps) h
  simp [ofEq, refl] at hs

end Path

/-! ## Primitive rewrites and their symmetric closure -/

inductive RewriteStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Type (u + 1) where
  | trans_assoc {a b c d : A}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      RewriteStep (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))
  | trans_refl_left {a b : A} (p : Path a b) :
      RewriteStep (Path.trans (Path.refl a) p) p
  | trans_refl_right {a b : A} (p : Path a b) :
      RewriteStep (Path.trans p (Path.refl b)) p
  | trans_symm {a b : A} (p : Path a b) :
      RewriteStep (Path.trans p (Path.symm p)) (Path.refl a)
  | symm_trans {a b : A} (p : Path a b) :
      RewriteStep (Path.trans (Path.symm p) p) (Path.refl b)
  | trans_congr_left {a c d : A}
      (q : Path c d) {p r : Path a c} (s : RewriteStep p r) :
      RewriteStep (Path.trans p q) (Path.trans r q)
  | trans_congr_right {a b c : A}
      (p : Path a b) {q r : Path b c} (s : RewriteStep q r) :
      RewriteStep (Path.trans p q) (Path.trans p r)

inductive RwEq {A : Type u} {a b : A} :
    Path a b → Path a b → Type (u + 1) where
  | refl {p : Path a b} : RwEq p p
  | step {p q : Path a b} : RewriteStep p q → RwEq p q
  | symm {p q : Path a b} : RwEq p q → RwEq q p
  | trans {p q r : Path a b} : RwEq p q → RwEq q r → RwEq p r

inductive Derivation₂ {A : Type u} {a b : A} :
    Path a b → Path a b → Type (u + 1) where
  | refl {p : Path a b} : Derivation₂ p p
  | step {p q : Path a b} : RewriteStep p q → Derivation₂ p q
  | symm {p q : Path a b} : Derivation₂ p q → Derivation₂ q p
  | trans {p q r : Path a b} : Derivation₂ p q → Derivation₂ q r → Derivation₂ p r

def toRwEq {A : Type u} {a b : A} {p q : Path a b} :
    Derivation₂ p q → RwEq p q
  | .refl => .refl
  | .step s => .step s
  | .symm h => .symm (toRwEq h)
  | .trans h₁ h₂ => .trans (toRwEq h₁) (toRwEq h₂)

def ofRwEq {A : Type u} {a b : A} {p q : Path a b} :
    RwEq p q → Derivation₂ p q
  | .refl => .refl
  | .step s => .step s
  | .symm h => .symm (ofRwEq h)
  | .trans h₁ h₂ => .trans (ofRwEq h₁) (ofRwEq h₂)

def rwEqStepCount {A : Type u} {a b : A} {p q : Path a b} :
    RwEq p q → Nat
  | .refl => 0
  | .step _ => 1
  | .symm h => rwEqStepCount h
  | .trans h₁ h₂ => rwEqStepCount h₁ + rwEqStepCount h₂

/-! ## Explicit coherence routes -/

def pentagon_right_route {A : Type u} {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  RwEq.trans
    (RwEq.step (RewriteStep.trans_assoc (Path.trans f g) h k))
    (RwEq.step (RewriteStep.trans_assoc f g (Path.trans h k)))

def pentagon_left_route {A : Type u} {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  RwEq.trans
    (RwEq.step (RewriteStep.trans_congr_left k
      (RewriteStep.trans_assoc f g h)))
    (RwEq.trans
      (RwEq.step (RewriteStep.trans_assoc f (Path.trans g h) k))
      (RwEq.step (RewriteStep.trans_congr_right f
        (RewriteStep.trans_assoc g h k))))

def triangle_left_route {A : Type u} {a b c : A}
    (f : Path a b) (g : Path b c) :
    RwEq
      (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  RwEq.trans
    (RwEq.step (RewriteStep.trans_assoc f (Path.refl b) g))
    (RwEq.step (RewriteStep.trans_congr_right f
      (RewriteStep.trans_refl_left g)))

def triangle_right_route {A : Type u} {a b c : A}
    (f : Path a b) (g : Path b c) :
    RwEq
      (Path.trans (Path.trans f (Path.refl b)) g)
      (Path.trans f g) :=
  RwEq.step (RewriteStep.trans_congr_left g
    (RewriteStep.trans_refl_right f))

/-! This is the extensional boundary of a higher coherence cell.  Its two
routes remain distinct Type-valued derivations; only their endpoint equality
proofs are identified, exactly at Lean's proof-irrelevant boundary. -/

structure BoundaryCoherence {A : Type u} {a b : A}
    {p q : Path a b} (left right : RwEq p q) : Type (u + 1) where
  proof_boundary : p.proof = q.proof

def boundaryCoherence {A : Type u} {a b : A}
    {p q : Path a b} (left right : RwEq p q) : BoundaryCoherence left right :=
  ⟨Subsingleton.elim _ _⟩

/-! ## Selected auditable theorem boundary -/

structure OmegaGroupoidCertificate (A : Type u) where
  derivation_presentation :
    ∀ {a b : A} {p q : Path a b},
      Nonempty (Derivation₂ p q) ↔ Nonempty (RwEq p q)
  two_cell_to_rw_eq_roundtrip :
    ∀ {a b : A} {p q : Path a b} (h : RwEq p q),
      toRwEq (ofRwEq h) = h
  two_cell_reification_roundtrip :
    ∀ {a b : A} {p q : Path a b} (d : Derivation₂ p q),
      ofRwEq (toRwEq d) = d
  pentagon_right_witness :
    ∀ {a b c d e : A} (f : Path a b) (g : Path b c)
      (h : Path c d) (k : Path d e),
      RwEq
        (Path.trans (Path.trans (Path.trans f g) h) k)
        (Path.trans f (Path.trans g (Path.trans h k)))
  pentagon_left_witness :
    ∀ {a b c d e : A} (f : Path a b) (g : Path b c)
      (h : Path c d) (k : Path d e),
      RwEq
        (Path.trans (Path.trans (Path.trans f g) h) k)
        (Path.trans f (Path.trans g (Path.trans h k)))
  pentagon_route_counts :
    ∀ {a b c d e : A} (f : Path a b) (g : Path b c)
      (h : Path c d) (k : Path d e),
      rwEqStepCount (pentagon_right_route f g h k) = 2 ∧
        rwEqStepCount (pentagon_left_route f g h k) = 3
  pentagon_routes_distinct :
    ∀ {a b c d e : A} (f : Path a b) (g : Path b c)
      (h : Path c d) (k : Path d e),
      pentagon_right_route f g h k ≠ pentagon_left_route f g h k
  pentagon_coherence :
    ∀ {a b c d e : A} (f : Path a b) (g : Path b c)
      (h : Path c d) (k : Path d e),
      BoundaryCoherence
        (pentagon_right_route f g h k) (pentagon_left_route f g h k)
  triangle_left_witness :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      RwEq (Path.trans (Path.trans f (Path.refl b)) g) (Path.trans f g)
  triangle_right_witness :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      RwEq (Path.trans (Path.trans f (Path.refl b)) g) (Path.trans f g)
  triangle_route_counts :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      rwEqStepCount (triangle_left_route f g) = 2 ∧
        rwEqStepCount (triangle_right_route f g) = 1
  triangle_routes_distinct :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      triangle_left_route f g ≠ triangle_right_route f g
  triangle_coherence :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      BoundaryCoherence (triangle_left_route f g) (triangle_right_route f g)
  inverse_cancellation :
    ∀ {a b : A} (p : Path a b),
      RwEq (Path.trans p (Path.symm p)) (Path.refl a)
  path_trace_is_nontrivial :
    ∀ (a : A), Path.ofEq (rfl : a = a) ≠ Path.refl a

theorem main_result (A : Type u) : Nonempty (OmegaGroupoidCertificate A) := by
  sorry

end ComputationalPaths.Path.PalomarOmegaGroupoid433
