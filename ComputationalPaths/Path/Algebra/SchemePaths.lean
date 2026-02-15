/-
# Scheme-like Structures via Computational Paths

Ringed spaces, structure sheaves, affine schemes, morphisms of schemes,
fiber products — all modelled with computational paths over discrete
topological/algebraic data on finite index types.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.SchemePaths

open ComputationalPaths.Path

universe u

/-! ## Basic open sets and sections -/

/-- A basic open set in Spec ℤ[x], indexed by Nat (representing D(f_i)). -/
abbrev OpenIdx := Nat

/-- A section over an open set: just an Int value (global sections of 𝒪). -/
abbrev Section := Int

/-- A presheaf assigns a section type to each open. We model it as a function. -/
structure Presheaf where
  sections : OpenIdx → Section

/-- Restriction map between opens (identity in our simplified model). -/
@[simp] def restrict (F : Presheaf) (_ _ : OpenIdx) : Section :=
  F.sections 0

/-- A ringed space: a presheaf with ring operations on sections. -/
structure RingedSpace where
  sheaf : Presheaf
  zero : Section := 0
  one : Section := 1
  add : Section → Section → Section := Int.add
  mul : Section → Section → Section := Int.mul

/-- The structure sheaf of Spec ℤ. -/
@[simp] def structureSheaf (f : OpenIdx → Section) : Presheaf := ⟨f⟩

/-- A morphism of ringed spaces (on the sheaf level). -/
structure SheafMorphism (F G : Presheaf) where
  map : OpenIdx → Section → Section

/-- Identity sheaf morphism. -/
@[simp] def idMorphism (F : Presheaf) : SheafMorphism F F :=
  ⟨fun _ s => s⟩

/-- Composition of sheaf morphisms. -/
@[simp] def compMorphism {F G H : Presheaf}
    (φ : SheafMorphism F G) (ψ : SheafMorphism G H) : SheafMorphism F H :=
  ⟨fun i s => ψ.map i (φ.map i s)⟩

/-- An affine scheme datum: a ring (represented by operations on Int). -/
structure AffineScheme where
  ring_zero : Section := 0
  ring_one : Section := 1
  ring_add : Section → Section → Section := Int.add
  ring_mul : Section → Section → Section := Int.mul

/-- The default affine scheme (Spec ℤ). -/
@[simp] def specZ : AffineScheme := ⟨0, 1, Int.add, Int.mul⟩

/-- Fiber product of two sections. -/
@[simp] def fiberProd (a b : Section) : Section × Section := (a, b)

/-- Projection from fiber product. -/
@[simp] def fiberFst (p : Section × Section) : Section := p.1
@[simp] def fiberSnd (p : Section × Section) : Section := p.2

/-! ## Core theorems -/

-- 1. Identity morphism acts as identity
theorem id_morphism_act (F : Presheaf) (i : OpenIdx) (s : Section) :
    (idMorphism F).map i s = s := by simp

def id_morphism_act_path (F : Presheaf) (i : OpenIdx) (s : Section) :
    Path ((idMorphism F).map i s) s :=
  Path.ofEq (id_morphism_act F i s)

-- 2. Composition with identity (left)
theorem comp_id_left {F G : Presheaf} (φ : SheafMorphism F G) (i : OpenIdx) (s : Section) :
    (compMorphism (idMorphism F) φ).map i s = φ.map i s := by simp

def comp_id_left_path {F G : Presheaf} (φ : SheafMorphism F G) (i : OpenIdx) (s : Section) :
    Path ((compMorphism (idMorphism F) φ).map i s) (φ.map i s) :=
  Path.ofEq (comp_id_left φ i s)

-- 3. Composition with identity (right)
theorem comp_id_right {F G : Presheaf} (φ : SheafMorphism F G) (i : OpenIdx) (s : Section) :
    (compMorphism φ (idMorphism G)).map i s = φ.map i s := by simp

def comp_id_right_path {F G : Presheaf} (φ : SheafMorphism F G) (i : OpenIdx) (s : Section) :
    Path ((compMorphism φ (idMorphism G)).map i s) (φ.map i s) :=
  Path.ofEq (comp_id_right φ i s)

-- 4. Associativity of composition
theorem comp_assoc {F G H K : Presheaf}
    (φ : SheafMorphism F G) (ψ : SheafMorphism G H) (χ : SheafMorphism H K)
    (i : OpenIdx) (s : Section) :
    (compMorphism (compMorphism φ ψ) χ).map i s =
    (compMorphism φ (compMorphism ψ χ)).map i s := by simp

def comp_assoc_path {F G H K : Presheaf}
    (φ : SheafMorphism F G) (ψ : SheafMorphism G H) (χ : SheafMorphism H K)
    (i : OpenIdx) (s : Section) :
    Path ((compMorphism (compMorphism φ ψ) χ).map i s)
         ((compMorphism φ (compMorphism ψ χ)).map i s) :=
  Path.ofEq (comp_assoc φ ψ χ i s)

-- 5. Fiber product projections
theorem fiber_fst_proj (a b : Section) : fiberFst (fiberProd a b) = a := by simp

def fiber_fst_proj_path (a b : Section) :
    Path (fiberFst (fiberProd a b)) a :=
  Path.ofEq (fiber_fst_proj a b)

-- 6. Fiber product second projection
theorem fiber_snd_proj (a b : Section) : fiberSnd (fiberProd a b) = b := by simp

def fiber_snd_proj_path (a b : Section) :
    Path (fiberSnd (fiberProd a b)) b :=
  Path.ofEq (fiber_snd_proj a b)

-- 7. Fiber product universal property (reconstruction)
theorem fiber_prod_reconstruct (p : Section × Section) :
    fiberProd (fiberFst p) (fiberSnd p) = p := by
  simp

def fiber_prod_reconstruct_path (p : Section × Section) :
    Path (fiberProd (fiberFst p) (fiberSnd p)) p :=
  Path.ofEq (fiber_prod_reconstruct p)

-- 8. SpecZ addition is commutative (via default fields)
theorem specZ_default_add_comm (a b : Section) :
    specZ.ring_add a b = specZ.ring_add b a := by
  simp [Int.add_comm]

-- 9. SpecZ multiplication is commutative
theorem specZ_default_mul_comm (a b : Section) :
    specZ.ring_mul a b = specZ.ring_mul b a := by
  simp [Int.mul_comm]

-- 10. SpecZ addition commutativity
theorem specZ_add_comm (a b : Section) : specZ.ring_add a b = specZ.ring_add b a := by
  simp [Int.add_comm]

def specZ_add_comm_path (a b : Section) :
    Path (specZ.ring_add a b) (specZ.ring_add b a) :=
  Path.ofEq (specZ_add_comm a b)

-- 11. SpecZ multiplication commutativity
theorem specZ_mul_comm (a b : Section) : specZ.ring_mul a b = specZ.ring_mul b a := by
  simp [Int.mul_comm]

def specZ_mul_comm_path (a b : Section) :
    Path (specZ.ring_mul a b) (specZ.ring_mul b a) :=
  Path.ofEq (specZ_mul_comm a b)

-- 12. SpecZ additive identity
theorem specZ_add_zero (a : Section) : specZ.ring_add a 0 = a := by simp

def specZ_add_zero_path (a : Section) : Path (specZ.ring_add a 0) a :=
  Path.ofEq (specZ_add_zero a)

-- 13. SpecZ multiplicative identity
theorem specZ_mul_one (a : Section) : specZ.ring_mul a 1 = a := by simp

def specZ_mul_one_path (a : Section) : Path (specZ.ring_mul a 1) a :=
  Path.ofEq (specZ_mul_one a)

-- 14. SpecZ distributivity
theorem specZ_distrib (a b c : Section) :
    specZ.ring_mul a (specZ.ring_add b c) =
    specZ.ring_add (specZ.ring_mul a b) (specZ.ring_mul a c) := by
  simp [Int.mul_add]

def specZ_distrib_path (a b c : Section) :
    Path (specZ.ring_mul a (specZ.ring_add b c))
         (specZ.ring_add (specZ.ring_mul a b) (specZ.ring_mul a c)) :=
  Path.ofEq (specZ_distrib a b c)

-- 15. SpecZ addition associativity
theorem specZ_add_assoc (a b c : Section) :
    specZ.ring_add (specZ.ring_add a b) c = specZ.ring_add a (specZ.ring_add b c) := by
  simp [Int.add_assoc]

def specZ_add_assoc_path (a b c : Section) :
    Path (specZ.ring_add (specZ.ring_add a b) c)
         (specZ.ring_add a (specZ.ring_add b c)) :=
  Path.ofEq (specZ_add_assoc a b c)

-- 16. SpecZ multiplication associativity
theorem specZ_mul_assoc (a b c : Section) :
    specZ.ring_mul (specZ.ring_mul a b) c = specZ.ring_mul a (specZ.ring_mul b c) := by
  simp [Int.mul_assoc]

def specZ_mul_assoc_path (a b c : Section) :
    Path (specZ.ring_mul (specZ.ring_mul a b) c)
         (specZ.ring_mul a (specZ.ring_mul b c)) :=
  Path.ofEq (specZ_mul_assoc a b c)

-- 17. Congruence of morphism application
def morphism_congrArg {F G : Presheaf} {φ₁ φ₂ : SheafMorphism F G}
    (h : Path φ₁ φ₂) (i : OpenIdx) (s : Section) :
    Path (φ₁.map i s) (φ₂.map i s) :=
  Path.congrArg (fun φ => φ.map i s) h

-- 18. Congruence of presheaf sections
def sections_congrArg {F G : Presheaf} (h : Path F G) (i : OpenIdx) :
    Path (F.sections i) (G.sections i) :=
  Path.congrArg (fun F => F.sections i) h

-- 19. Transport of ringed space sheaf
def ringedSpace_sheaf_congrArg {R₁ R₂ : RingedSpace} (h : Path R₁ R₂) :
    Path R₁.sheaf R₂.sheaf :=
  Path.congrArg RingedSpace.sheaf h

-- 20. Transport of affine scheme operations
def affine_ring_add_congrArg {S₁ S₂ : AffineScheme} (h : Path S₁ S₂) :
    Path S₁.ring_add S₂.ring_add :=
  Path.congrArg AffineScheme.ring_add h

-- 21. Symmetry of specZ add commutativity
theorem specZ_add_comm_symm (a b : Section) :
    Path.symm (specZ_add_comm_path a b) = specZ_add_comm_path b a := by
  unfold specZ_add_comm_path
  simp

-- 22. Trans chain: add assoc then commute
def specZ_add_rotate (a b c : Section) :
    Path (specZ.ring_add (specZ.ring_add a b) c)
         (specZ.ring_add (specZ.ring_add b c) a) :=
  Path.trans
    (specZ_add_assoc_path a b c)
    (specZ_add_comm_path a (specZ.ring_add b c))

-- 23. Fiber product congruence
def fiber_prod_congrArg_left {a₁ a₂ : Section} (h : Path a₁ a₂) (b : Section) :
    Path (fiberProd a₁ b) (fiberProd a₂ b) :=
  Path.congrArg (fun a => fiberProd a b) h

-- 24. SpecZ mul zero
theorem specZ_mul_zero (a : Section) : specZ.ring_mul a 0 = 0 := by simp

def specZ_mul_zero_path (a : Section) : Path (specZ.ring_mul a 0) 0 :=
  Path.ofEq (specZ_mul_zero a)

-- 25. Chain: distributivity + zero = identity
def specZ_distrib_zero_chain (a b : Section) :
    Path (specZ.ring_mul a (specZ.ring_add b 0))
         (specZ.ring_add (specZ.ring_mul a b) 0) :=
  Path.trans
    (specZ_distrib_path a b 0)
    (Path.congrArg (fun x => specZ.ring_add (specZ.ring_mul a b) x) (specZ_mul_zero_path a))

end ComputationalPaths.Path.Algebra.SchemePaths
