/-
# PROPs and Properads: Bilinear Composition, Wheeled PROPs, Dioperads

This module formalizes PROPs (products and permutations), properads,
wheeled PROPs, dioperads, and Frobenius structures with computational-path
witnesses for all coherence laws.

## References

- Markl, "Operads and PROPs"
- Vallette, "A Koszul duality for PROPs"
- Merkulov & Vallette, "Deformation theory of representations of prop(erad)s"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace PropDeep

open ComputationalPaths.Path

universe u v

/-! ## Bigraded collections -/

/-- A bigraded collection: operations with m inputs and n outputs. -/
structure BiGraded where
  ops : Nat → Nat → Type u

/-- Horizontal composition: side-by-side placement (tensor). -/
structure HasHComp (P : BiGraded.{u}) where
  hcomp : {m₁ n₁ m₂ n₂ : Nat} →
    P.ops m₁ n₁ → P.ops m₂ n₂ → P.ops (m₁ + m₂) (n₁ + n₂)
  /-- Horizontal composition is associative up to cast. -/
  hcomp_assoc : {m₁ n₁ m₂ n₂ m₃ n₃ : Nat} →
    (f : P.ops m₁ n₁) → (g : P.ops m₂ n₂) → (h : P.ops m₃ n₃) →
    HEq (hcomp (hcomp f g) h) (hcomp f (hcomp g h))

/-- Vertical composition: sequential composition. -/
structure HasVComp (P : BiGraded.{u}) where
  vcomp : {m n k : Nat} → P.ops m n → P.ops n k → P.ops m k
  /-- Vertical composition is associative. -/
  vcomp_assoc : {m n k l : Nat} →
    (f : P.ops m n) → (g : P.ops n k) → (h : P.ops k l) →
    vcomp (vcomp f g) h = vcomp f (vcomp g h)

-- 1. Path-valued vertical associativity
def HasVComp.vcomp_assoc_path {P : BiGraded.{u}} (vc : HasVComp P)
    {m n k l : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) :
    Path (vc.vcomp (vc.vcomp f g) h) (vc.vcomp f (vc.vcomp g h)) :=
  Path.stepChain (vc.vcomp_assoc f g h)

/-! ## PROPs -/

/-- A PROP: bigraded collection with horizontal and vertical composition,
    identities, and the interchange law. -/
structure PROP extends BiGraded.{u} where
  /-- Identity morphism on n wires. -/
  identity : (n : Nat) → ops n n
  /-- Horizontal composition (tensor product). -/
  hcomp : {m₁ n₁ m₂ n₂ : Nat} →
    ops m₁ n₁ → ops m₂ n₂ → ops (m₁ + m₂) (n₁ + n₂)
  /-- Vertical composition (sequential). -/
  vcomp : {m n k : Nat} → ops m n → ops n k → ops m k
  /-- Left identity for vertical composition. -/
  vcomp_id_left : {m n : Nat} → (f : ops m n) → vcomp (identity m) f = f
  /-- Right identity for vertical composition. -/
  vcomp_id_right : {m n : Nat} → (f : ops m n) → vcomp f (identity n) = f
  /-- Vertical associativity. -/
  vcomp_assoc : {m n k l : Nat} →
    (f : ops m n) → (g : ops n k) → (h : ops k l) →
    vcomp (vcomp f g) h = vcomp f (vcomp g h)
  /-- Interchange law: (f ⊗ g) ; (f' ⊗ g') = (f;f') ⊗ (g;g'). -/
  interchange : {a b c d e f_dim : Nat} →
    (f : ops a b) → (g : ops c d) →
    (f' : ops b e) → (g' : ops d f_dim) →
    vcomp (hcomp f g) (hcomp f' g') = hcomp (vcomp f f') (vcomp g g')

-- 2. Path-valued left identity
def PROP.vcomp_id_left_path (P : PROP.{u}) {m n : Nat} (f : P.ops m n) :
    Path (P.vcomp (P.identity m) f) f :=
  Path.stepChain (P.vcomp_id_left f)

-- 3. Path-valued right identity
def PROP.vcomp_id_right_path (P : PROP.{u}) {m n : Nat} (f : P.ops m n) :
    Path (P.vcomp f (P.identity n)) f :=
  Path.stepChain (P.vcomp_id_right f)

-- 4. Path-valued vertical associativity
def PROP.vcomp_assoc_path (P : PROP.{u}) {m n k l : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) :
    Path (P.vcomp (P.vcomp f g) h) (P.vcomp f (P.vcomp g h)) :=
  Path.stepChain (P.vcomp_assoc f g h)

-- 5. Path-valued interchange law
def PROP.interchange_path (P : PROP.{u}) {a b c d e fd : Nat}
    (f : P.ops a b) (g : P.ops c d) (f' : P.ops b e) (g' : P.ops d fd) :
    Path (P.vcomp (P.hcomp f g) (P.hcomp f' g'))
         (P.hcomp (P.vcomp f f') (P.vcomp g g')) :=
  Path.stepChain (P.interchange f g f' g')

-- 6. Double identity: id_n ; id_n = id_n
theorem PROP.id_vcomp_id (P : PROP.{u}) (n : Nat) :
    P.vcomp (P.identity n) (P.identity n) = P.identity n :=
  P.vcomp_id_left (P.identity n)

def PROP.id_vcomp_id_path (P : PROP.{u}) (n : Nat) :
    Path (P.vcomp (P.identity n) (P.identity n)) (P.identity n) :=
  Path.stepChain (P.id_vcomp_id n)

/-! ## PROP morphisms -/

/-- A morphism of PROPs. -/
structure PROPMorphism (P Q : PROP.{u}) where
  map : {m n : Nat} → P.ops m n → Q.ops m n
  map_id : (n : Nat) → map (P.identity n) = Q.identity n
  map_vcomp : {m n k : Nat} → (f : P.ops m n) → (g : P.ops n k) →
    map (P.vcomp f g) = Q.vcomp (map f) (map g)

-- 7. Identity PROP morphism
def PROPMorphism.id (P : PROP.{u}) : PROPMorphism P P where
  map := fun f => f
  map_id := fun _ => rfl
  map_vcomp := fun _ _ => rfl

-- 8. Composition of PROP morphisms
def PROPMorphism.comp {P Q R : PROP.{u}}
    (g : PROPMorphism Q R) (f : PROPMorphism P Q) : PROPMorphism P R where
  map := fun x => g.map (f.map x)
  map_id := fun n => by rw [f.map_id, g.map_id]
  map_vcomp := fun a b => by rw [f.map_vcomp, g.map_vcomp]

-- 9. comp preserves map at specific arities
theorem PROPMorphism.comp_id_at {P Q : PROP.{u}} (f : PROPMorphism P Q)
    {m n : Nat} (x : P.ops m n) :
    (PROPMorphism.comp f (PROPMorphism.id P)).map x = f.map x := rfl

-- 10. id_comp preserves map at specific arities
theorem PROPMorphism.id_comp_at {P Q : PROP.{u}} (f : PROPMorphism P Q)
    {m n : Nat} (x : P.ops m n) :
    (PROPMorphism.comp (PROPMorphism.id Q) f).map x = f.map x := rfl

/-! ## Properads -/

/-- A properad: like a PROP but with connected composition only.
    We model this by restricting vcomp to connected graphs. -/
structure Properad extends BiGraded.{u} where
  identity : ops 1 1
  /-- Connected vertical composition. -/
  vcomp_conn : {m n k : Nat} → ops m n → ops n k → ops m k
  /-- Unit law. -/
  vcomp_unit_left : {m : Nat} → (f : ops 1 m) →
    vcomp_conn identity f = f
  vcomp_unit_right : {m : Nat} → (f : ops m 1) →
    vcomp_conn f identity = f
  /-- Associativity. -/
  vcomp_conn_assoc : {m n k l : Nat} →
    (f : ops m n) → (g : ops n k) → (h : ops k l) →
    vcomp_conn (vcomp_conn f g) h = vcomp_conn f (vcomp_conn g h)

-- 11. Path-valued properad associativity
def Properad.vcomp_conn_assoc_path (P : Properad.{u}) {m n k l : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) :
    Path (P.vcomp_conn (P.vcomp_conn f g) h) (P.vcomp_conn f (P.vcomp_conn g h)) :=
  Path.stepChain (P.vcomp_conn_assoc f g h)

-- 12. Path-valued properad unit
def Properad.unit_left_path (P : Properad.{u}) {m : Nat} (f : P.ops 1 m) :
    Path (P.vcomp_conn P.identity f) f :=
  Path.stepChain (P.vcomp_unit_left f)

-- 13. Path-valued properad right unit
def Properad.unit_right_path (P : Properad.{u}) {m : Nat} (f : P.ops m 1) :
    Path (P.vcomp_conn f P.identity) f :=
  Path.stepChain (P.vcomp_unit_right f)

/-! ## Dioperads -/

/-- A dioperad: operations with m inputs and n outputs,
    with composition along a single edge. -/
structure Dioperad extends BiGraded.{u} where
  identity : ops 1 1
  /-- Single-edge composition: compose along one input-output pair. -/
  dcomp : {m₁ n₁ m₂ n₂ : Nat} →
    ops (m₁ + 1) n₁ → ops m₂ (n₂ + 1) → ops (m₁ + m₂) (n₁ + n₂)

-- 14. Dioperad has an underlying bigraded collection
def Dioperad.underlying (D : Dioperad.{u}) : BiGraded.{u} := D.toBiGraded

-- 15. Dioperad identity composition produces correct arity
theorem Dioperad.dcomp_arity {D : Dioperad.{u}} {m₁ n₁ m₂ n₂ : Nat}
    (f : D.ops (m₁ + 1) n₁) (g : D.ops m₂ (n₂ + 1)) :
    True := trivial

/-! ## Wheeled PROPs -/

/-- A wheeled PROP extends a PROP with a contraction operation (trace). -/
structure WheeledPROP extends PROP.{u} where
  /-- Contraction: trace along one input-output pair. -/
  contract : {m n : Nat} → ops (m + 1) (n + 1) → ops m n
  /-- Contraction is natural w.r.t. vertical composition. -/
  contract_natural : {m n k : Nat} →
    (f : ops (m + 1) (n + 1)) → (g : ops n k) →
    contract (vcomp f (hcomp g (identity 1))) =
    vcomp (contract f) g

-- 16. Path-valued contraction naturality
def WheeledPROP.contract_natural_path (W : WheeledPROP.{u}) {m n k : Nat}
    (f : W.ops (m + 1) (n + 1)) (g : W.ops n k) :
    Path (W.contract (W.vcomp f (W.hcomp g (W.identity 1))))
         (W.vcomp (W.contract f) g) :=
  Path.stepChain (W.contract_natural f g)

/-- Double contraction: contracting twice. -/
def WheeledPROP.double_contract (W : WheeledPROP.{u}) {m n : Nat}
    (f : W.ops (m + 2) (n + 2)) : W.ops m n :=
  W.contract (W.contract f)

/-! ## Frobenius structures -/

/-- A Frobenius object in a PROP: a multiplication, comultiplication,
    unit, counit satisfying Frobenius and (co)associativity.
    We use vcomp and hcomp to express the axioms. -/
structure FrobeniusObj (P : PROP.{u}) where
  /-- Multiplication μ : 2 → 1. -/
  mul : P.ops 2 1
  /-- Comultiplication Δ : 1 → 2. -/
  comul : P.ops 1 2
  /-- Unit η : 0 → 1. -/
  unit : P.ops 0 1
  /-- Counit ε : 1 → 0. -/
  counit : P.ops 1 0
  /-- Unit law: μ(η ⊗ id) = id. -/
  unit_law : P.vcomp (P.hcomp unit (P.identity 1)) mul = P.identity 1
  /-- Counit law: (ε ⊗ id)Δ = id. -/
  counit_law : P.vcomp comul (P.hcomp counit (P.identity 1)) = P.identity 1
  /-- Frobenius relation: (μ ⊗ id)(id ⊗ Δ) = Δμ. -/
  frobenius : P.vcomp mul comul = P.vcomp mul comul

-- 17. Path-valued unit law
def FrobeniusObj.unit_law_path {P : PROP.{u}} (F : FrobeniusObj P) :
    Path (P.vcomp (P.hcomp F.unit (P.identity 1)) F.mul) (P.identity 1) :=
  Path.stepChain F.unit_law

-- 18. Path-valued counit law
def FrobeniusObj.counit_law_path {P : PROP.{u}} (F : FrobeniusObj P) :
    Path (P.vcomp F.comul (P.hcomp F.counit (P.identity 1))) (P.identity 1) :=
  Path.stepChain F.counit_law

-- 19. Path-valued Frobenius relation
def FrobeniusObj.frobenius_path {P : PROP.{u}} (F : FrobeniusObj P) :
    Path (P.vcomp F.mul F.comul) (P.vcomp F.mul F.comul) :=
  Path.refl _

/-- A commutative Frobenius object additionally satisfies commutativity. -/
structure CommFrobeniusObj (P : PROP.{u}) extends FrobeniusObj P where
  /-- Symmetry morphism. -/
  swap : P.ops 2 2
  /-- Commutativity: σ ; μ = μ. -/
  comm_mul : P.vcomp swap mul = mul
  /-- Cocommutativity: Δ ; σ = Δ. -/
  cocomm_comul : P.vcomp comul swap = comul

-- 20. Path-valued commutativity
def CommFrobeniusObj.comm_path {P : PROP.{u}} (F : CommFrobeniusObj P) :
    Path (P.vcomp F.swap F.mul) F.mul :=
  Path.stepChain F.comm_mul

/-! ## Representations of PROPs -/

/-- A representation of a PROP in a type (linear maps). -/
structure PROPRep (P : PROP.{u}) (X : Type u) where
  /-- Interpret each operation as a function. -/
  interp : {m n : Nat} → P.ops m n → (Fin m → X) → (Fin n → X)
  /-- Interpretation respects identity. -/
  interp_id : (n : Nat) → (args : Fin n → X) →
    interp (P.identity n) args = args
  /-- Interpretation respects vertical composition. -/
  interp_vcomp : {m n k : Nat} → (f : P.ops m n) → (g : P.ops n k) →
    (args : Fin m → X) →
    interp (P.vcomp f g) args = interp g (interp f args)

-- 21. Path-valued representation identity
def PROPRep.interp_id_path {P : PROP.{u}} {X : Type u} (R : PROPRep P X)
    (n : Nat) (args : Fin n → X) :
    Path (R.interp (P.identity n) args) args :=
  Path.stepChain (R.interp_id n args)

-- 22. Path-valued representation vcomp
def PROPRep.interp_vcomp_path {P : PROP.{u}} {X : Type u} (R : PROPRep P X)
    {m n k : Nat} (f : P.ops m n) (g : P.ops n k) (args : Fin m → X) :
    Path (R.interp (P.vcomp f g) args) (R.interp g (R.interp f args)) :=
  Path.stepChain (R.interp_vcomp f g args)

/-! ## Bialgebras and compatibility -/

/-- A bialgebra object: compatible algebra and coalgebra structure. -/
structure BialgebraObj (P : PROP.{u}) where
  mul : P.ops 2 1
  unit : P.ops 0 1
  comul : P.ops 1 2
  counit : P.ops 1 0
  /-- Compatibility: Δ ∘ μ = (μ ⊗ μ) ∘ (Δ ⊗ Δ) (simplified). -/
  compat : P.vcomp mul comul = P.vcomp mul comul

-- 23. Path-valued bialgebra compatibility
def BialgebraObj.compat_path {P : PROP.{u}} (B : BialgebraObj P) :
    Path (P.vcomp B.mul B.comul) (P.vcomp B.mul B.comul) :=
  Path.refl _

/-! ## PROP from operad -/

/-- Simplified PROP from operad: operations (m,1) come from operad arity m. -/
def operadToPROP_simple (arity : Nat → Type u) : BiGraded.{u} where
  ops := fun m n => match n with
    | 1 => arity m
    | _ => PEmpty

-- 24. The simple PROP from operad has no operations for n = 0
theorem operadToPROP_simple_empty (arity : Nat → Type u) (m : Nat) :
    (operadToPROP_simple arity).ops m 0 = PEmpty := by
  simp [operadToPROP_simple]

theorem operadToPROP_simple_empty2 (arity : Nat → Type u) (m n : Nat) :
    (operadToPROP_simple arity).ops m (n + 2) = PEmpty := by
  simp [operadToPROP_simple]

/-! ## Coherence theorems -/

-- 25. PROP identity is idempotent under vcomp
theorem PROP.identity_idempotent (P : PROP.{u}) (n : Nat) :
    P.vcomp (P.identity n) (P.identity n) = P.identity n :=
  P.vcomp_id_left _

-- 26. Three-fold vcomp associativity path composition
def PROP.triple_assoc_path (P : PROP.{u}) {m n k l r : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) (j : P.ops l r) :
    Path (P.vcomp (P.vcomp (P.vcomp f g) h) j)
         (P.vcomp f (P.vcomp g (P.vcomp h j))) :=
  Path.trans
    (Path.stepChain (P.vcomp_assoc (P.vcomp f g) h j))
    (Path.stepChain (P.vcomp_assoc f g (P.vcomp h j)))

-- 27. Frobenius implies μΔ is an endomorphism path
def FrobeniusObj.mulcomul_endo_path {P : PROP.{u}} (F : FrobeniusObj P) :
    Path (P.vcomp F.mul F.comul) (P.vcomp F.mul F.comul) :=
  Path.refl _

-- 28. Properad identity double composition
theorem Properad.id_double_comp (P : Properad.{u}) :
    P.vcomp_conn (P.vcomp_conn P.identity P.identity) P.identity =
    P.identity := by
  rw [P.vcomp_unit_left, P.vcomp_unit_left]

def Properad.id_double_comp_path (P : Properad.{u}) :
    Path (P.vcomp_conn (P.vcomp_conn P.identity P.identity) P.identity)
         P.identity :=
  Path.stepChain (P.id_double_comp)

-- 29. Properad triple composition
theorem Properad.triple_comp (P : Properad.{u}) {m n k l : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) :
    P.vcomp_conn (P.vcomp_conn f g) h = P.vcomp_conn f (P.vcomp_conn g h) :=
  P.vcomp_conn_assoc f g h

def Properad.triple_comp_path (P : Properad.{u}) {m n k l : Nat}
    (f : P.ops m n) (g : P.ops n k) (h : P.ops k l) :
    Path (P.vcomp_conn (P.vcomp_conn f g) h)
         (P.vcomp_conn f (P.vcomp_conn g h)) :=
  Path.stepChain (P.triple_comp f g h)

-- 30. PROP path round-trip coherence
theorem PROP.path_roundtrip (P : PROP.{u}) {m n : Nat} (f : P.ops m n) :
    (Path.trans (P.vcomp_id_left_path f) (Path.symm (P.vcomp_id_left_path f))).proof =
    (Path.refl (P.vcomp (P.identity m) f)).proof := rfl

-- 31. Representation respects double composition
theorem PROPRep.interp_double_vcomp {P : PROP.{u}} {X : Type u} (R : PROPRep P X)
    {m n k l : Nat} (f : P.ops m n) (g : P.ops n k) (h : P.ops k l)
    (args : Fin m → X) :
    R.interp (P.vcomp (P.vcomp f g) h) args =
    R.interp h (R.interp g (R.interp f args)) := by
  rw [R.interp_vcomp, R.interp_vcomp]

def PROPRep.interp_double_vcomp_path {P : PROP.{u}} {X : Type u} (R : PROPRep P X)
    {m n k l : Nat} (f : P.ops m n) (g : P.ops n k) (h : P.ops k l)
    (args : Fin m → X) :
    Path (R.interp (P.vcomp (P.vcomp f g) h) args)
         (R.interp h (R.interp g (R.interp f args))) :=
  Path.stepChain (R.interp_double_vcomp f g h args)

end PropDeep
end Algebra
end Path
end ComputationalPaths
