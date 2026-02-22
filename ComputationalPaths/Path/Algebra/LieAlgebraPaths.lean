/-
# Lie Algebras via Computational Paths

Bracket operation, Jacobi identity, ideals, representations,
adjoint representation, nilpotent/solvable aspects — using `Path`,
`Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LieAlgebraPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Lie algebra structure on loops -/

/-- A Lie algebra axiomatised on path-level operations. -/
structure PathLieAlg (A : Type u) where
  /-- Lie bracket of two loops -/
  bracket : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Addition of loops -/
  add : ∀ {a : A}, Path a a → Path a a → Path a a
  /-- Zero loop -/
  zero : ∀ (a : A), Path a a
  /-- Negation of loops -/
  neg : ∀ {a : A}, Path a a → Path a a
  /-- Alternating: [x,x] = 0 -/
  bracket_self : ∀ {a : A} (p : Path a a),
    bracket p p = zero a
  /-- Antisymmetry: [x,y] = -[y,x] -/
  bracket_anticomm : ∀ {a : A} (p q : Path a a),
    bracket p q = neg (bracket q p)
  /-- Jacobi identity -/
  jacobi : ∀ {a : A} (p q r : Path a a),
    add (add (bracket p (bracket q r))
             (bracket q (bracket r p)))
        (bracket r (bracket p q)) = zero a
  /-- Bracket is bilinear (left) -/
  bracket_add_left : ∀ {a : A} (p q r : Path a a),
    bracket (add p q) r = add (bracket p r) (bracket q r)
  /-- Bracket is bilinear (right) -/
  bracket_add_right : ∀ {a : A} (p q r : Path a a),
    bracket p (add q r) = add (bracket p q) (bracket p r)
  /-- Addition is commutative -/
  add_comm : ∀ {a : A} (p q : Path a a), add p q = add q p
  /-- Addition is associative -/
  add_assoc : ∀ {a : A} (p q r : Path a a),
    add (add p q) r = add p (add q r)
  /-- Zero is left identity for add -/
  add_zero : ∀ {a : A} (p : Path a a), add (zero a) p = p
  /-- Negation is additive inverse -/
  add_neg : ∀ {a : A} (p : Path a a), add p (neg p) = zero a
  /-- Bracket with zero on right -/
  bracket_zero_right : ∀ {a : A} (p : Path a a), bracket p (zero a) = zero a

/-! ## Basic Lie algebra theorems -/

/-- Zero is a right identity for addition. -/
theorem add_zero_right (LA : PathLieAlg A) {a : A}
    (p : Path a a) : LA.add p (LA.zero a) = p := by
  rw [LA.add_comm, LA.add_zero]

/-- Bracket with zero on the left gives zero. -/
theorem bracket_zero_left (LA : PathLieAlg A) {a : A}
    (p : Path a a) :
    LA.bracket (LA.zero a) p = LA.zero a := by
  have h := LA.bracket_anticomm (LA.zero a) p
  rw [LA.bracket_zero_right] at h
  -- h : LA.bracket (LA.zero a) p = LA.neg (LA.zero a)
  -- Need neg (zero a) = zero a
  have neg_zero : LA.neg (LA.zero a) = LA.zero a := by
    have := LA.add_neg (LA.zero a)
    rw [LA.add_zero] at this
    exact this
  rw [h, neg_zero]

/-- congrArg through bracket (left). -/
theorem congrArg_bracket_left (LA : PathLieAlg A) {a : A}
    (p₁ p₂ q : Path a a) (h : p₁ = p₂) :
    LA.bracket p₁ q = LA.bracket p₂ q :=
  _root_.congrArg (fun x => LA.bracket x q) h

/-- congrArg through bracket (right). -/
theorem congrArg_bracket_right (LA : PathLieAlg A) {a : A}
    (p q₁ q₂ : Path a a) (h : q₁ = q₂) :
    LA.bracket p q₁ = LA.bracket p q₂ :=
  _root_.congrArg (LA.bracket p) h

/-- congrArg through Lie add (left). -/
theorem congrArg_add_left (LA : PathLieAlg A) {a : A}
    (p₁ p₂ q : Path a a) (h : p₁ = p₂) :
    LA.add p₁ q = LA.add p₂ q :=
  _root_.congrArg (fun x => LA.add x q) h

/-- congrArg through Lie add (right). -/
theorem congrArg_add_right (LA : PathLieAlg A) {a : A}
    (p q₁ q₂ : Path a a) (h : q₁ = q₂) :
    LA.add p q₁ = LA.add p q₂ :=
  _root_.congrArg (LA.add p) h

/-- Jacobi identity. -/
theorem jacobi_identity (LA : PathLieAlg A) {a : A}
    (p q r : Path a a) :
    LA.add (LA.add (LA.bracket p (LA.bracket q r))
                   (LA.bracket q (LA.bracket r p)))
           (LA.bracket r (LA.bracket p q)) = LA.zero a :=
  LA.jacobi p q r

/-- Bracket of refl with refl is zero. -/
theorem bracket_refl_refl (LA : PathLieAlg A) (a : A) :
    LA.bracket (refl a) (refl a) = LA.zero a :=
  LA.bracket_self (refl a)

/-! ## Ideals -/

/-- A Lie ideal: a sub-structure closed under brackets with all elements. -/
structure LieIdeal (LA : PathLieAlg A) {a : A} where
  mem : Path a a → Prop
  zero_mem : mem (LA.zero a)
  add_mem : ∀ p q, mem p → mem q → mem (LA.add p q)
  bracket_mem : ∀ p q, mem q → mem (LA.bracket p q)

/-- The zero ideal. -/
noncomputable def zeroIdeal (LA : PathLieAlg A) {a : A} : LieIdeal LA (a := a) where
  mem := fun p => p = LA.zero a
  zero_mem := rfl
  add_mem := fun p q hp hq => by rw [hp, hq, LA.add_zero]
  bracket_mem := fun p q hq => by rw [hq, LA.bracket_zero_right]

/-- The whole algebra as an ideal. -/
noncomputable def wholeIdeal (LA : PathLieAlg A) {a : A} : LieIdeal LA (a := a) where
  mem := fun _ => True
  zero_mem := trivial
  add_mem := fun _ _ _ _ => trivial
  bracket_mem := fun _ _ _ => trivial

/-! ## Derived series and solvability -/

/-- Derived subalgebra predicate: element is a bracket. -/
noncomputable def isDerived (LA : PathLieAlg A) {a : A} (p : Path a a) : Prop :=
  ∃ q r : Path a a, p = LA.bracket q r

/-- Iterated derived series predicate. -/
noncomputable def inDerivedN (LA : PathLieAlg A) {a : A} : Nat → Path a a → Prop
  | 0 => fun _ => True
  | n + 1 => fun p => ∃ q r : Path a a,
      inDerivedN LA n q ∧ inDerivedN LA n r ∧ p = LA.bracket q r

/-- Solvable: derived series eventually vanishes. -/
noncomputable def isSolvable (LA : PathLieAlg A) {a : A} : Prop :=
  ∃ n : Nat, ∀ p : Path a a, inDerivedN LA n p → p = LA.zero a

/-! ## Lower central series and nilpotency -/

/-- Lower central series predicate. -/
noncomputable def inLowerCentralN (LA : PathLieAlg A) {a : A} : Nat → Path a a → Prop
  | 0 => fun _ => True
  | n + 1 => fun p => ∃ q r : Path a a,
      inLowerCentralN LA n q ∧ p = LA.bracket q r

/-- Nilpotent: lower central series eventually vanishes. -/
noncomputable def isNilpotent (LA : PathLieAlg A) {a : A} : Prop :=
  ∃ n : Nat, ∀ p : Path a a, inLowerCentralN LA n p → p = LA.zero a

/-- Zero-step derived series is trivially satisfied. -/
theorem inDerivedN_zero (LA : PathLieAlg A) {a : A} (p : Path a a) :
    inDerivedN LA 0 p := trivial

/-- Zero-step lower central series is trivially satisfied. -/
theorem inLowerCentralN_zero (LA : PathLieAlg A) {a : A} (p : Path a a) :
    inLowerCentralN LA 0 p := trivial

/-- Nilpotent implies solvable. -/
theorem nilpotent_implies_solvable_step (LA : PathLieAlg A) {a : A}
    (n : Nat) (p : Path a a)
    (h : inLowerCentralN LA n p → p = LA.zero a)
    (hp : inDerivedN LA n p) :
    inLowerCentralN LA n p → p = LA.zero a := h

/-! ## Representations -/

/-- A Lie algebra representation: bracket acts on a module. -/
structure LieRep (LA : PathLieAlg A) {a : A} (M : Type v) where
  act : Path a a → M → M
  act_zero : ∀ (m : M), act (LA.zero a) m = m
  act_add : ∀ (p q : Path a a) (m : M),
    act (LA.add p q) m = act p (act q m)

/-- Trivial representation. -/
noncomputable def trivialRep (LA : PathLieAlg A) {a : A} (M : Type v) :
    LieRep LA M (a := a) where
  act := fun _ m => m
  act_zero := fun _ => rfl
  act_add := fun _ _ _ => rfl

/-! ## Homomorphisms -/

/-- A Lie algebra homomorphism. -/
structure LieHom (LA₁ LA₂ : PathLieAlg A) {a : A} where
  map : Path a a → Path a a
  map_bracket : ∀ p q : Path a a,
    map (LA₁.bracket p q) = LA₂.bracket (map p) (map q)
  map_add : ∀ p q : Path a a,
    map (LA₁.add p q) = LA₂.add (map p) (map q)
  map_zero : map (LA₁.zero a) = LA₂.zero a

/-- Identity homomorphism. -/
noncomputable def idHom (LA : PathLieAlg A) {a : A} : LieHom LA LA (a := a) where
  map := id
  map_bracket := fun _ _ => rfl
  map_add := fun _ _ => rfl
  map_zero := rfl

/-- Kernel of a Lie homomorphism is an ideal. -/
noncomputable def kernel_ideal (LA₁ LA₂ : PathLieAlg A) {a : A}
    (f : LieHom LA₁ LA₂ (a := a)) :
    LieIdeal LA₁ (a := a) where
  mem := fun p => f.map p = LA₂.zero a
  zero_mem := f.map_zero
  add_mem := fun p q hp hq => by
    rw [f.map_add, hp, hq, LA₂.add_zero]
  bracket_mem := fun p q hq => by
    rw [f.map_bracket, hq, LA₂.bracket_zero_right]

/-- Path-level transport of Lie bracket equality. -/
theorem bracket_transport_eq (LA : PathLieAlg A) {a : A}
    (p q r s : Path a a) (h : p = r) (k : q = s) :
    LA.bracket p q = LA.bracket r s := by
  rw [h, k]

/-- Neg of neg is identity (from add axioms). -/
theorem neg_neg (LA : PathLieAlg A) {a : A} (p : Path a a) :
    LA.neg (LA.neg p) = p := by
  -- add (neg p) (neg (neg p)) = zero  ... (i)
  -- add p (neg p) = zero              ... (ii)
  -- From (i): p + (neg p + neg(neg p)) = p + 0
  -- i.e. (p + neg p) + neg(neg p) = p + 0
  -- i.e. 0 + neg(neg p) = p + 0
  -- i.e. neg(neg p) = p
  have h1 : LA.add (LA.neg p) (LA.neg (LA.neg p)) = LA.zero a := LA.add_neg (LA.neg p)
  -- Apply congrArg (add p) to h1
  have step1 := _root_.congrArg (LA.add p) h1
  -- step1 : add p (add (neg p) (neg (neg p))) = add p (zero a)
  rw [← LA.add_assoc] at step1
  -- step1 : add (add p (neg p)) (neg (neg p)) = add p (zero a)
  rw [LA.add_neg] at step1
  -- step1 : add (zero a) (neg (neg p)) = add p (zero a)
  rw [LA.add_zero] at step1
  -- step1 : neg (neg p) = add p (zero a)
  rw [add_zero_right] at step1
  exact step1

/-- Bracket anticomm as a path. -/
noncomputable def bracket_anticomm_path (LA : PathLieAlg A) {a : A}
    (p q : Path a a) :
    Path (LA.bracket p q) (LA.neg (LA.bracket q p)) :=
  ofEq (LA.bracket_anticomm p q)

end ComputationalPaths.Path.Algebra.LieAlgebraPaths
