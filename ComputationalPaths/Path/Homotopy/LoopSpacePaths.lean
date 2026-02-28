/-
# Loop Space Theory via Computational Paths

Based loops as Path a a, loop composition via trans, loop inverse via symm,
higher loops, Omega-spectrum structure, loop space functoriality.
All constructions use the core Path/Step/trans/symm/congrArg/transport API.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace LoopSpacePaths

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Based loop space -/

/-- The based loop space Ω(A, a) is the type of paths from a to a. -/
noncomputable def Omega (A : Type u) (a : A) : Type u := Path a a

/-- The constant loop at a. -/
noncomputable def omega_id {A : Type u} (a : A) : Omega A a := Path.refl a

/-- Loop composition via path trans. -/
noncomputable def omega_comp {a : A} (p q : Omega A a) : Omega A a :=
  Path.trans p q

/-- Loop inverse via path symm. -/
noncomputable def omega_inv {a : A} (p : Omega A a) : Omega A a :=
  Path.symm p

/-! ## Loop space group laws -/

/-- Left identity for loop composition. -/
theorem omega_comp_id_left {a : A} (p : Omega A a) :
    omega_comp (omega_id a) p = p := by
  unfold omega_comp omega_id
  cases p; simp

/-- Right identity for loop composition. -/
theorem omega_comp_id_right {a : A} (p : Omega A a) :
    omega_comp p (omega_id a) = p := by
  unfold omega_comp omega_id
  cases p; simp

/-- Associativity of loop composition. -/
theorem omega_comp_assoc {a : A} (p q r : Omega A a) :
    omega_comp (omega_comp p q) r = omega_comp p (omega_comp q r) := by
  unfold omega_comp; exact Path.trans_assoc p q r

/-- Left inverse for loop composition (propositional). -/
noncomputable def omega_inv_comp_rweq {a : A} (p : Omega A a) :
    RwEq (omega_comp (omega_inv p) p) (omega_id a) := by
  unfold omega_comp omega_inv omega_id
  exact rweq_cmpA_inv_left p

/-- Left inverse for loop composition (propositional). -/
theorem omega_inv_comp_toEq {a : A} (p : Omega A a) :
    (omega_comp (omega_inv p) p).toEq = (Path.refl a).toEq := by
  exact rweq_toEq (omega_inv_comp_rweq p)

/-- Right inverse for loop composition (propositional). -/
noncomputable def omega_comp_inv_rweq {a : A} (p : Omega A a) :
    RwEq (omega_comp p (omega_inv p)) (omega_id a) := by
  unfold omega_comp omega_inv omega_id
  exact rweq_cmpA_inv_right p

/-- Right inverse for loop composition (propositional). -/
theorem omega_comp_inv_toEq {a : A} (p : Omega A a) :
    (omega_comp p (omega_inv p)).toEq = (Path.refl a).toEq := by
  exact rweq_toEq (omega_comp_inv_rweq p)

/-- Double inverse is identity. -/
theorem omega_inv_inv {a : A} (p : Omega A a) :
    omega_inv (omega_inv p) = p := by
  unfold omega_inv; exact Path.symm_symm p

/-- Inverse of composition reverses order. -/
theorem omega_inv_comp {a : A} (p q : Omega A a) :
    omega_inv (omega_comp p q) = omega_comp (omega_inv q) (omega_inv p) := by
  unfold omega_inv omega_comp; simp

/-- Inverse of the identity loop. -/
theorem omega_inv_id (a : A) :
    omega_inv (omega_id a) = omega_id a := by
  unfold omega_inv omega_id; simp

/-! ## Higher loop spaces: 2-loops (paths between loops) -/

/-- A 2-loop is an equality between loops. -/
noncomputable def TwoLoop {a : A} (p q : Omega A a) : Prop := p = q

/-- Reflexive 2-loop. -/
noncomputable def twoLoop_refl {a : A} (p : Omega A a) : TwoLoop p p := rfl

/-- 2-loop composition via Eq.trans. -/
noncomputable def twoLoop_comp {a : A} {p q r : Omega A a} (α : TwoLoop p q) (β : TwoLoop q r) :
    TwoLoop p r :=
  Eq.trans α β

/-- 2-loop inverse via Eq.symm. -/
noncomputable def twoLoop_inv {a : A} {p q : Omega A a} (α : TwoLoop p q) : TwoLoop q p :=
  Eq.symm α

/-- Path-first 2-loop witness. -/
abbrev TwoLoopPath {a : A} (p q : Omega A a) : Type u := Path p q

/-- RwEq-first 2-loop witness. -/
abbrev TwoLoopRwEq {a : A} (p q : Omega A a) : Type u := RwEq p q

/-- Promote Eq-based 2-loops to path witnesses. -/
noncomputable def twoLoop_toPath {a : A} {p q : Omega A a} (α : TwoLoop p q) : TwoLoopPath p q :=
  Path.stepChain α

/-- Promote Eq-based 2-loops to rewrite-equivalence witnesses. -/
noncomputable def twoLoop_toRwEq {a : A} {p q : Omega A a} (α : TwoLoop p q) : TwoLoopRwEq p q :=
  rweq_of_eq α

/-- Path composition of path-first 2-loops. -/
noncomputable def twoLoopPath_comp {a : A} {p q r : Omega A a}
    (α : TwoLoopPath p q) (β : TwoLoopPath q r) : TwoLoopPath p r :=
  Path.trans α β

/-- Path inverse of a path-first 2-loop. -/
noncomputable def twoLoopPath_inv {a : A} {p q : Omega A a}
    (α : TwoLoopPath p q) : TwoLoopPath q p :=
  Path.symm α

/-- All 2-loops between the same endpoints are equal (proof irrelevance). -/
theorem twoLoop_subsingleton {a : A} {p q : Omega A a} (α β : TwoLoop p q) :
    α = β :=
  Subsingleton.elim α β

/-- 2-loop composition is commutative (Eckmann-Hilton). -/
theorem twoLoop_eckmann_hilton {a : A} {p : Omega A a}
    (α β : TwoLoop p p) :
    twoLoop_comp α β = twoLoop_comp β α :=
  Subsingleton.elim _ _

/-- 2-loop left identity. -/
theorem twoLoop_comp_refl_left {a : A} {p q : Omega A a} (α : TwoLoop p q) :
    twoLoop_comp (twoLoop_refl p) α = α :=
  Subsingleton.elim _ _

/-- 2-loop right identity. -/
theorem twoLoop_comp_refl_right {a : A} {p q : Omega A a} (α : TwoLoop p q) :
    twoLoop_comp α (twoLoop_refl q) = α :=
  Subsingleton.elim _ _

/-- 2-loop left inverse. -/
theorem twoLoop_inv_comp {a : A} {p q : Omega A a} (α : TwoLoop p q) :
    twoLoop_comp (twoLoop_inv α) α = twoLoop_refl q :=
  Subsingleton.elim _ _

/-- 2-loop right inverse. -/
theorem twoLoop_comp_inv {a : A} {p q : Omega A a} (α : TwoLoop p q) :
    twoLoop_comp α (twoLoop_inv α) = twoLoop_refl p :=
  Subsingleton.elim _ _

/-- 2-loop associativity. -/
theorem twoLoop_comp_assoc {a : A} {p q r s : Omega A a}
    (α : TwoLoop p q) (β : TwoLoop q r) (γ : TwoLoop r s) :
    twoLoop_comp (twoLoop_comp α β) γ = twoLoop_comp α (twoLoop_comp β γ) :=
  Subsingleton.elim _ _

/-! ## Loop space functoriality -/

/-- Map a function over the loop space via congrArg. -/
noncomputable def omega_map (f : A → B) {a : A} (p : Omega A a) : Omega B (f a) :=
  Path.congrArg f p

/-- The loop space functor preserves the identity loop. -/
theorem omega_map_id_loop (f : A → B) (a : A) :
    omega_map f (omega_id a) = omega_id (f a) := by
  unfold omega_map omega_id; simp

/-- The loop space functor preserves loop composition. -/
theorem omega_map_comp (f : A → B) {a : A} (p q : Omega A a) :
    omega_map f (omega_comp p q) = omega_comp (omega_map f p) (omega_map f q) := by
  unfold omega_map omega_comp; simp

/-- Step.map f commutes with Step.symm. -/
private theorem step_map_symm_comm (f : A → B) (s : ComputationalPaths.Step A) :
    ComputationalPaths.Step.map f (ComputationalPaths.Step.symm s) =
      ComputationalPaths.Step.symm (ComputationalPaths.Step.map f s) := by
  cases s; rfl

/-- The loop space functor preserves loop inverse. -/
theorem omega_map_inv (f : A → B) {a : A} (p : Omega A a) :
    omega_map f (omega_inv p) = omega_inv (omega_map f p) := by
  exact Path.congrArg_symm f p

/-- Step.map distributes over composition. -/
private theorem step_map_comp (f : B → C) (g : A → B) (s : ComputationalPaths.Step A) :
    ComputationalPaths.Step.map (fun x => f (g x)) s =
      ComputationalPaths.Step.map f (ComputationalPaths.Step.map g s) := by
  cases s; rfl

/-- Functoriality: composition of maps. -/
theorem omega_map_comp_fun (f : B → C) (g : A → B) {a : A} (p : Omega A a) :
    omega_map (fun x => f (g x)) p = omega_map f (omega_map g p) := by
  exact Path.congrArg_comp f g p

/-- Step.map id is identity. -/
private theorem step_map_id_eq (s : ComputationalPaths.Step A) :
    ComputationalPaths.Step.map (fun x : A => x) s = s := by
  cases s; simp

/-- Identity function acts trivially on loops. -/
theorem omega_map_id_fun {a : A} (p : Omega A a) :
    omega_map (fun x : A => x) p = p := by
  exact Path.congrArg_id p

/-! ## Transport in loop spaces -/

/-- Transport a loop along a path between base points via conjugation. -/
noncomputable def omega_transport {a b : A} (p : Path a b) (l : Omega A a) : Omega A b :=
  Path.trans (Path.symm p) (Path.trans l p)

/-- Transport preserves the identity loop (propositionally). -/
noncomputable def omega_transport_id_rweq {a b : A} (p : Path a b) :
    RwEq (omega_transport p (omega_id a)) (omega_id b) := by
  unfold omega_transport omega_id
  exact rweq_trans
    (rweq_trans_congr_right (Path.symm p) (rweq_cmpA_refl_left p))
    (rweq_cmpA_inv_left p)

/-- Transport preserves the identity loop (propositionally). -/
theorem omega_transport_id_toEq {a b : A} (p : Path a b) :
    (omega_transport p (omega_id a)).toEq = (omega_id b).toEq := by
  exact rweq_toEq (omega_transport_id_rweq p)

/-- Transport along refl is identity. -/
theorem omega_transport_refl_path {a : A} (l : Omega A a) :
    omega_transport (Path.refl a) l = l := by
  unfold omega_transport; simp
  cases l; simp

/-! ## Conjugation in loop spaces -/

/-- Conjugation of a loop by another loop: g⁻¹ ∘ l ∘ g. -/
noncomputable def omega_conj {a : A} (g l : Omega A a) : Omega A a :=
  omega_comp (omega_inv g) (omega_comp l g)

/-- Conjugation by the identity is trivial. -/
theorem omega_conj_id {a : A} (l : Omega A a) :
    omega_conj (omega_id a) l = l := by
  unfold omega_conj omega_comp omega_inv omega_id; simp
  cases l; simp

/-- Conjugation preserves the identity loop (propositionally). -/
noncomputable def omega_conj_id_loop_rweq {a : A} (g : Omega A a) :
    RwEq (omega_conj g (omega_id a)) (omega_id a) := by
  unfold omega_conj omega_comp omega_inv omega_id
  exact rweq_trans
    (rweq_trans_congr_right (Path.symm g) (rweq_cmpA_refl_left g))
    (rweq_cmpA_inv_left g)

/-- Conjugation preserves the identity loop (propositionally). -/
theorem omega_conj_id_loop_toEq {a : A} (g : Omega A a) :
    (omega_conj g (omega_id a)).toEq = (omega_id a).toEq := by
  exact rweq_toEq (omega_conj_id_loop_rweq g)

/-! ## Power operations -/

/-- n-fold power of a loop. -/
noncomputable def omega_pow {a : A} (p : Omega A a) : Nat → Omega A a
  | 0 => omega_id a
  | n + 1 => omega_comp (omega_pow p n) p

/-- p^0 = id. -/
theorem omega_pow_zero {a : A} (p : Omega A a) :
    omega_pow p 0 = omega_id a := rfl

/-- p^(n+1) = p^n ∘ p. -/
theorem omega_pow_succ {a : A} (p : Omega A a) (n : Nat) :
    omega_pow p (n + 1) = omega_comp (omega_pow p n) p := rfl

/-- p^1 = p. -/
theorem omega_pow_one {a : A} (p : Omega A a) :
    omega_pow p 1 = p := by
  show omega_comp (omega_id a) p = p
  exact omega_comp_id_left p

/-- Power of the identity is the identity. -/
theorem omega_pow_id (a : A) (n : Nat) :
    omega_pow (omega_id a) n = omega_id a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show omega_comp (omega_pow (omega_id a) n) (omega_id a) = omega_id a
      rw [ih]
      exact omega_comp_id_left (omega_id a)

/-! ## Loop space of a product -/

/-- Loop in a product projects to first component. -/
noncomputable def omega_prod_fst {a : A} {b : B} (p : Omega (A × B) (a, b)) : Omega A a :=
  Path.congrArg Prod.fst p

/-- Loop in a product projects to second component. -/
noncomputable def omega_prod_snd {a : A} {b : B} (p : Omega (A × B) (a, b)) : Omega B b :=
  Path.congrArg Prod.snd p

/-- Projection preserves identity loop (fst). -/
theorem omega_prod_fst_id {a : A} {b : B} :
    omega_prod_fst (omega_id (A := A × B) (a, b)) = omega_id a := by
  unfold omega_prod_fst omega_id; simp

/-- Projection preserves identity loop (snd). -/
theorem omega_prod_snd_id {a : A} {b : B} :
    omega_prod_snd (omega_id (A := A × B) (a, b)) = omega_id b := by
  unfold omega_prod_snd omega_id; simp

/-- Projection preserves loop composition (fst). -/
theorem omega_prod_fst_comp {a : A} {b : B}
    (p q : Omega (A × B) (a, b)) :
    omega_prod_fst (omega_comp p q) =
      omega_comp (omega_prod_fst p) (omega_prod_fst q) := by
  unfold omega_prod_fst omega_comp; simp

/-- Projection preserves loop composition (snd). -/
theorem omega_prod_snd_comp {a : A} {b : B}
    (p q : Omega (A × B) (a, b)) :
    omega_prod_snd (omega_comp p q) =
      omega_comp (omega_prod_snd p) (omega_prod_snd q) := by
  unfold omega_prod_snd omega_comp; simp

/-- Projection preserves loop inverse (fst). -/
theorem omega_prod_fst_inv {a : A} {b : B}
    (p : Omega (A × B) (a, b)) :
    omega_prod_fst (omega_inv p) = omega_inv (omega_prod_fst p) := by
  exact Path.congrArg_symm Prod.fst p

/-- Projection preserves loop inverse (snd). -/
theorem omega_prod_snd_inv {a : A} {b : B}
    (p : Omega (A × B) (a, b)) :
    omega_prod_snd (omega_inv p) = omega_inv (omega_prod_snd p) := by
  exact Path.congrArg_symm Prod.snd p

end LoopSpacePaths
end Path
end ComputationalPaths
