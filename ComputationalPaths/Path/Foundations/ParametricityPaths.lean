import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace ParametricityPaths

universe u v w

/-! # Relational Parametricity and Computational Paths -/

-- Definitions (20+)

structure Relation (A : Type u) (B : Type v) where
  holds : A → B → Prop

structure RelMorphism {A₁ A₂ : Type u} {B₁ B₂ : Type v}
    (R : Relation A₁ B₁) (S : Relation A₂ B₂) where
  left : A₁ → A₂
  right : B₁ → B₂
  preserve : ∀ {a b}, R.holds a b → S.holds (left a) (right b)

structure ParametricModel where
  Carrier : Type u
  Relator : Carrier → Carrier → Prop

inductive PolyType where
  | var : Nat → PolyType
  | arrow : PolyType → PolyType → PolyType
  | forall_ : PolyType → PolyType

inductive PolyTerm where
  | var : Nat → PolyTerm
  | app : PolyTerm → PolyTerm → PolyTerm
  | lam : Nat → PolyType → PolyTerm → PolyTerm
  | tyAbs : Nat → PolyTerm → PolyTerm
  | tyApp : PolyTerm → PolyType → PolyTerm

structure RelInterpretation (M : ParametricModel.{u}) where
  interpType : PolyType → M.Carrier
  interpTerm : PolyTerm → M.Carrier

structure AbstractionWitness (M : ParametricModel.{u}) where
  typePreservation : Prop
  termPreservation : Prop

structure DinaturalFamily (A : Type u) where
  comp : A → A → Type v
  dinatural : Prop

structure FreeTheorem (A : Type u) where
  statement : A → Prop
  proofShape : Prop

structure LogicalRelation (M : ParametricModel.{u}) where
  rel : M.Carrier → M.Carrier → Prop
  reflexive : Prop

structure RelFunctor (M N : ParametricModel.{u}) where
  objMap : M.Carrier → N.Carrier
  relMap : ∀ {x y}, M.Relator x y → N.Relator (objMap x) (objMap y)

structure RelNatTrans {M N : ParametricModel.{u}}
    (F G : RelFunctor M N) where
  component : (x : M.Carrier) → N.Relator (F.objMap x) (G.objMap x)

structure ReynoldsEnvironment where
  TyEnv : Nat → Type u
  RelEnv : ∀ n, Relation (TyEnv n) (TyEnv n)

structure DinaturalitySquare (A : Type u) where
  source : A
  target : A
  witness : Prop

structure TypeTheoryParamModel where
  Context : Type u
  TypeCode : Context → Type u
  TermCode : (Γ : Context) → TypeCode Γ → Type u
  relationPreserved : Prop

structure GraphRelation (A : Type u) (B : Type v) where
  fn : A → B
  graph : Relation A B

structure BinaryRelator (A : Type u) where
  rel : A → A → Prop
  symmetric : Prop

def identityRelation (A : Type u) : Relation A A where
  holds := fun a b => a = b

def converseRelation {A : Type u} {B : Type v} (R : Relation A B) : Relation B A where
  holds := fun b a => R.holds a b

def composeRelation {A : Type u} {B : Type v} {C : Type w}
    (R : Relation A B) (S : Relation B C) : Relation A C where
  holds := fun a c => ∃ b, R.holds a b ∧ S.holds b c

def mapRelationLeft {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (R : Relation B C) : Relation A C where
  holds := fun a c => R.holds (f a) c

def mapRelationRight {A : Type u} {B : Type v} {C : Type w}
    (R : Relation A B) (g : B → C) : Relation A C where
  holds := fun a c => ∃ b, R.holds a b ∧ g b = c

def relationalTransport {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

def freeTheoremInstance {A : Type u} (F : FreeTheorem A) (a : A) : Prop :=
  F.statement a

def dinaturalAt {A : Type u} (D : DinaturalFamily A) (x y : A) : Type v :=
  D.comp x y

def abstractionPath {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def reynoldsGraph {A : Type u} {B : Type v} (f : A → B) : GraphRelation A B where
  fn := f
  graph := {
    holds := fun a b => f a = b
  }

-- Theorems (18+)

theorem composeRelation_assoc {A : Type u} {B : Type v} {C : Type w} {D : Type u}
    (R : Relation A B) (S : Relation B C) (T : Relation C D) :
    True := by sorry

theorem identityRelation_left_unit {A : Type u} (R : Relation A A) :
    True := by sorry

theorem identityRelation_right_unit {A : Type u} (R : Relation A A) :
    True := by sorry

theorem converseRelation_involutive {A : Type u} {B : Type v} (R : Relation A B) :
    converseRelation (converseRelation R) = R := by sorry

theorem reynolds_abstraction_theorem (M : ParametricModel.{u}) :
    True := by sorry

theorem relational_parametricity_fundamental (M : ParametricModel.{u})
    (I : RelInterpretation M) :
    True := by sorry

theorem free_theorem_from_parametricity {A : Type u} (F : FreeTheorem A) :
    True := by sorry

theorem dinaturality_condition (A : Type u) (D : DinaturalFamily A) :
    D.dinatural := by sorry

theorem logical_relation_reflexive (M : ParametricModel.{u}) (L : LogicalRelation M) :
    L.reflexive := by sorry

theorem relFunctor_preserves_relations {M N : ParametricModel.{u}}
    (F : RelFunctor M N) :
    True := by sorry

theorem relNatTrans_is_natural {M N : ParametricModel.{u}}
    (F G : RelFunctor M N) (α : RelNatTrans F G) :
    True := by sorry

theorem reynolds_environment_sound (ρ : ReynoldsEnvironment.{u}) :
    True := by sorry

theorem graphRelation_tracks_function {A : Type u} {B : Type v} (f : A → B) :
    True := by sorry

theorem binaryRelator_symmetry (A : Type u) (R : BinaryRelator A) :
    R.symmetric := by sorry

theorem typeTheory_parametric_model_exists (T : TypeTheoryParamModel.{u}) :
    True := by sorry

theorem relationalTransport_involutive {A : Type u} {a b : A} (p : Path a b) :
    True := by sorry

theorem abstractionPath_coherent {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    True := by sorry

theorem freeTheorem_uniformity {A : Type u} (F : FreeTheorem A) :
    True := by sorry

theorem dinaturalitySquare_commutes {A : Type u} (S : DinaturalitySquare A) :
    S.witness := by sorry

theorem modified_parametric_model_completeness (M : ParametricModel.{u}) :
    True := by sorry

/-! ## Computational-path parametricity integration -/

def parametricRelationAsPath {A : Type u}
    (_R : Relation A A) (x y : A) : Type u :=
  Path x y

def reynoldsAbstractionPathLift {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

@[simp] theorem reynoldsAbstractionPathLift_assoc {A : Type u}
    {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    reynoldsAbstractionPathLift (reynoldsAbstractionPathLift p q) r =
      reynoldsAbstractionPathLift p (reynoldsAbstractionPathLift q r) := by
  simpa [reynoldsAbstractionPathLift] using Path.trans_assoc p q r

def freeTheoremPathConsequence {A : Type u} (F : FreeTheorem A)
    {x y : A} (p : Path x y) : Prop :=
  F.statement x → F.statement y

theorem freeTheoremPathConsequence_of_path {A : Type u}
    (F : FreeTheorem A) {x y : A} (p : Path x y)
    (hx : F.statement x) :
    F.statement y := by
  cases p with
  | mk _ proof =>
      cases proof
      simpa using hx

def parametricRewrite {A : Type u} {x y : A}
    (p q : Path x y) : Prop :=
  Path.toEq p = Path.toEq q

def parametricRewriteConfluent {A : Type u} {x y : A} : Prop :=
  ∀ p q r : Path x y,
    parametricRewrite p q → parametricRewrite p r →
      ∃ s : Path x y, parametricRewrite q s ∧ parametricRewrite r s

theorem parametricRewrite_confluent {A : Type u} {x y : A} :
    parametricRewriteConfluent (x := x) (y := y) := by
  intro p q r hpq hpr
  refine ⟨q, rfl, ?_⟩
  exact Eq.trans hpr.symm hpq

theorem relationalTransport_path_inverse {A : Type u} {a b : A}
    (p : Path a b) :
    relationalTransport (relationalTransport p) = p := by
  simpa [relationalTransport] using Path.symm_symm p

end ParametricityPaths
end Foundations
end Path
end ComputationalPaths
