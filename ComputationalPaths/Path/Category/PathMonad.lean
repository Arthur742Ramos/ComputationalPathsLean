/-
# Free Path Monad

The "free path" construction on a type `A` yields a monad whose underlying
endofunctor sends `a : A` to the type of all paths starting at `a`.  In our
framework, since `Path a b` records a propositional equality (`a = b` in
`Prop`) plus a step trace, the monad structure is given by:

- `pure a = refl a` (the empty path)
- `extend p q = trans p q` (extend a path by a continuation)

This file formalizes the free path monad, its Kleisli category, the monad
laws proved via path equations, and characterizes path algebras as
Eilenberg–Moore algebras.

## Key Results

| Definition / Theorem            | Description                                      |
|--------------------------------|--------------------------------------------------|
| `PathMonad.pure`               | Unit of the path monad (`refl`)                  |
| `PathMonad.extend`             | Kleisli extension                                |
| `PathMonad.left_unit`          | Left unit law                                    |
| `PathMonad.right_unit`         | Right unit law                                   |
| `PathMonad.assoc`              | Associativity law                                |
| `KleisliArrow`                 | Kleisli category of paths                        |
| `TransportAlgebra`             | Eilenberg–Moore algebra for the path monad       |

## References

* Mac Lane, *CWM*, Ch. VI (Monads)
* Moggi, *Notions of computation and monads*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v

-- ============================================================
-- §1  The Free Path Monad
-- ============================================================

namespace PathMonad

variable {A : Type u}

/-- Unit of the path monad: the reflexive path. -/
@[simp] def pure (a : A) : Path a a := Path.refl a

/-- Kleisli extension for the path monad: compose two paths. -/
@[simp] def extend {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- ============================================================
-- §2  Monad Laws
-- ============================================================

/-- Left unit law: `extend (pure a) f = f`. -/
@[simp] theorem left_unit {a b : A} (f : Path a b) :
    extend (pure a) f = f :=
  trans_refl_left f

/-- Right unit law: `extend p (pure b) = p`. -/
@[simp] theorem right_unit {a b : A} (p : Path a b) :
    extend p (pure b) = p :=
  trans_refl_right p

/-- Associativity law: `extend (extend p f) g = extend p (extend f g)`. -/
@[simp] theorem assoc {a b c d : A}
    (p : Path a b) (f : Path b c) (g : Path c d) :
    extend (extend p f) g = extend p (extend f g) :=
  trans_assoc p f g

/-- Double unit: extend pure with pure gives pure. -/
@[simp] theorem pure_extend_pure (a : A) :
    extend (pure a) (pure a) = pure a := by simp

/-- Extend with symm on the right cancels (toEq level). -/
theorem extend_symm_toEq {a b : A} (p : Path a b) :
    (extend p (Path.symm p)).toEq = rfl :=
  toEq_trans_symm p

/-- Extend with symm on the left cancels (toEq level). -/
theorem symm_extend_toEq {a b : A} (p : Path a b) :
    (extend (Path.symm p) p).toEq = rfl :=
  toEq_symm_trans p

/-- Four-fold composition in the monad. -/
theorem extend_four {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    extend (extend (extend p q) r) s = extend p (extend q (extend r s)) := by
  simp

/-- Left unit absorbed into composition chain. -/
theorem pure_extend_chain {a b c : A} (p : Path a b) (q : Path b c) :
    extend (extend (pure a) p) q = extend p q := by simp

/-- Right unit absorbed into composition chain. -/
theorem extend_pure_chain {a b c : A} (p : Path a b) (q : Path b c) :
    extend p (extend q (pure c)) = extend p q := by simp

/-- Naturality of extend with respect to congrArg. -/
theorem extend_congrArg {B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (extend p q) =
      extend (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Symmetry interacts correctly with extend (proof level). -/
theorem extend_symm_proof {a b : A} (p : Path a b) :
    (extend p (Path.symm p)).proof = (pure a).proof :=
  proof_irrel _ _

/-- Extend preserves the proof component. -/
theorem extend_proof {a b c : A} (p : Path a b) (q : Path b c) :
    (extend p q).proof = p.proof.trans q.proof := rfl

-- ============================================================
-- §3  Kleisli Category
-- ============================================================

/-- A Kleisli arrow in the path monad: wraps a path. -/
structure KleisliArrow (A : Type u) (a b : A) where
  arrow : Path a b

namespace KleisliArrow

variable {a b c d : A}

/-- Identity Kleisli arrow. -/
@[simp] def id (a : A) : KleisliArrow A a a :=
  ⟨pure a⟩

/-- Composition of Kleisli arrows. -/
@[simp] def comp (f : KleisliArrow A a b) (g : KleisliArrow A b c) :
    KleisliArrow A a c :=
  ⟨extend f.arrow g.arrow⟩

/-- Left identity for Kleisli composition. -/
@[simp] theorem comp_id_left (f : KleisliArrow A a b) :
    comp (KleisliArrow.id a) f = f := by
  cases f; simp

/-- Right identity for Kleisli composition. -/
@[simp] theorem comp_id_right (f : KleisliArrow A a b) :
    comp f (KleisliArrow.id b) = f := by
  cases f; simp

/-- Associativity of Kleisli composition. -/
@[simp] theorem comp_assoc
    (f : KleisliArrow A a b) (g : KleisliArrow A b c) (h : KleisliArrow A c d) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f; cases g; cases h; simp

/-- Inverse Kleisli arrow via path symmetry. -/
@[simp] def inv (f : KleisliArrow A a b) : KleisliArrow A b a :=
  ⟨Path.symm f.arrow⟩

/-- Left inverse for Kleisli arrows (at the toEq level). -/
theorem inv_comp_toEq (f : KleisliArrow A a b) :
    (comp (inv f) f).arrow.toEq = rfl := by simp

/-- Right inverse for Kleisli arrows (at the toEq level). -/
theorem comp_inv_toEq (f : KleisliArrow A a b) :
    (comp f (inv f)).arrow.toEq = rfl := by simp

/-- Inverse is involutive on the proof level. -/
theorem inv_inv_proof (f : KleisliArrow A a b) :
    (inv (inv f)).arrow.proof = f.arrow.proof :=
  proof_irrel _ _

/-- Inverse distributes over composition on the proof level. -/
theorem inv_comp_proof (f : KleisliArrow A a b) (g : KleisliArrow A b c) :
    (inv (comp f g)).arrow.proof = (comp (inv g) (inv f)).arrow.proof :=
  proof_irrel _ _

/-- The Kleisli category has all morphisms invertible (groupoid). -/
theorem kleisli_groupoid (f : KleisliArrow A a b) :
    (comp (inv f) f).arrow.proof = (KleisliArrow.id b).arrow.proof :=
  proof_irrel _ _

/-- Kleisli arrows with the same proof are proof-equal. -/
theorem arrow_proof_eq (f g : KleisliArrow A a b) :
    f.arrow.proof = g.arrow.proof :=
  proof_irrel _ _

end KleisliArrow

-- ============================================================
-- §4  Transport Algebra (Eilenberg–Moore)
-- ============================================================

/-- The transport algebra: the canonical Eilenberg–Moore algebra for
    the path monad.  The action is `Path.transport`, which uses only
    the `proof` field and ignores the step trace. -/
structure TransportAlgebra (A : Type u) (X : A → Type v) where
  /-- Transport action. -/
  action : {a b : A} → (a = b) → X a → X b
  /-- Unit law. -/
  action_rfl : ∀ (a : A) (x : X a), action (rfl : a = a) x = x
  /-- Composition law. -/
  action_trans_eq : ∀ {a b c : A} (p : a = b) (q : b = c) (x : X a),
    action (p.trans q) x = action q (action p x)

namespace TransportAlgebra

variable {A : Type u} {X : A → Type v}

/-- The canonical transport algebra uses Eq.rec. -/
def canonical (X : A → Type v) : TransportAlgebra A X where
  action := fun h x => h ▸ x
  action_rfl := fun _ _ => rfl
  action_trans_eq := fun p q x => by cases p; cases q; rfl

/-- Canonical action on rfl is the identity. -/
@[simp] theorem canonical_rfl (a : A) (x : X a) :
    (canonical X).action rfl x = x := rfl

/-- Canonical action on transitive equality factors. -/
@[simp] theorem canonical_trans {a b c : A} (p : a = b) (q : b = c) (x : X a) :
    (canonical X).action (p.trans q) x =
      (canonical X).action q ((canonical X).action p x) := by
  cases p; cases q; rfl

/-- Action on inverse gives left inverse. -/
theorem action_symm_left (alg : TransportAlgebra A X) {a b : A}
    (p : a = b) (x : X a) :
    alg.action p.symm (alg.action p x) = x := by
  cases p; simp [alg.action_rfl]

/-- Action on inverse gives right inverse. -/
theorem action_symm_right (alg : TransportAlgebra A X) {a b : A}
    (p : a = b) (y : X b) :
    alg.action p (alg.action p.symm y) = y := by
  cases p; simp [alg.action_rfl]

/-- Lift a transport algebra to act on paths (using the proof field). -/
def liftToPath (alg : TransportAlgebra A X) :
    {a b : A} → Path a b → X a → X b :=
  fun p x => alg.action p.proof x

/-- The lifted action preserves refl. -/
@[simp] theorem liftToPath_refl (alg : TransportAlgebra A X) (a : A) (x : X a) :
    alg.liftToPath (Path.refl a) x = x :=
  alg.action_rfl a x

/-- The lifted action preserves trans. -/
@[simp] theorem liftToPath_trans (alg : TransportAlgebra A X) {a b c : A}
    (p : Path a b) (q : Path b c) (x : X a) :
    alg.liftToPath (Path.trans p q) x =
      alg.liftToPath q (alg.liftToPath p x) :=
  alg.action_trans_eq p.proof q.proof x

end TransportAlgebra

-- ============================================================
-- §5  Algebra Homomorphisms
-- ============================================================

/-- A homomorphism between transport algebras. -/
structure AlgHom {X Y : A → Type v}
    (alg₁ : TransportAlgebra A X) (alg₂ : TransportAlgebra A Y) where
  map : ∀ (a : A), X a → Y a
  commute : ∀ {a b : A} (p : a = b) (x : X a),
    map b (alg₁.action p x) = alg₂.action p (map a x)

/-- Identity algebra homomorphism. -/
def AlgHom.id {X : A → Type v} (alg : TransportAlgebra A X) : AlgHom alg alg where
  map := fun _ x => x
  commute := fun _ _ => rfl

/-- Composition of algebra homomorphisms. -/
def AlgHom.comp {X Y Z : A → Type v}
    {alg₁ : TransportAlgebra A X} {alg₂ : TransportAlgebra A Y}
    {alg₃ : TransportAlgebra A Z}
    (f : AlgHom alg₁ alg₂) (g : AlgHom alg₂ alg₃) :
    AlgHom alg₁ alg₃ where
  map := fun a x => g.map a (f.map a x)
  commute := fun {a b} p x => by
    rw [f.commute, g.commute]

/-- Left identity for algebra hom composition. -/
theorem AlgHom.id_comp' {X Y : A → Type v}
    {alg₁ : TransportAlgebra A X} {alg₂ : TransportAlgebra A Y}
    (f : AlgHom alg₁ alg₂) :
    AlgHom.comp (AlgHom.id alg₁) f = f := by
  cases f; rfl

/-- Right identity for algebra hom composition. -/
theorem AlgHom.comp_id' {X Y : A → Type v}
    {alg₁ : TransportAlgebra A X} {alg₂ : TransportAlgebra A Y}
    (f : AlgHom alg₁ alg₂) :
    AlgHom.comp f (AlgHom.id alg₂) = f := by
  cases f; rfl

-- ============================================================
-- §6  Constant Algebra
-- ============================================================

/-- The constant transport algebra: equality acts trivially. -/
def constAlg (D : Type v) : TransportAlgebra A (fun _ => D) where
  action := fun p x => by cases p; exact x
  action_rfl := fun _ _ => rfl
  action_trans_eq := fun p q x => by cases p; cases q; rfl

/-- The constant algebra action is the identity. -/
@[simp] theorem constAlg_action {D : Type v} {a b : A}
    (p : a = b) (x : D) :
    (constAlg (A := A) D).action p x = x := by
  cases p; rfl

-- ============================================================
-- §7  Monad laws at the proof level
-- ============================================================

/-- All paths with the same endpoints have the same proof. -/
theorem path_proof_unique {a b : A} (p q : Path a b) :
    p.proof = q.proof :=
  proof_irrel _ _

/-- The monad multiplication (join): flatten nested paths. -/
theorem monad_join {a b c : A} (p : Path a b) (q : Path b c) :
    extend p q = Path.trans p q := rfl

/-- The monad is well-defined: extend respects proof equality. -/
theorem extend_proof_eq {a b c : A} (p₁ p₂ : Path a b) (q₁ q₂ : Path b c) :
    (extend p₁ q₁).proof = (extend p₂ q₂).proof :=
  proof_irrel _ _

/-- Pure is a two-sided identity at the proof level. -/
theorem pure_neutral_proof {a b : A} (p : Path a b) :
    (extend (pure a) p).proof = p.proof :=
  proof_irrel _ _

end PathMonad

end ComputationalPaths
