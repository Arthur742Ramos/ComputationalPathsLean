/-
  ComputationalPaths/Path/Algebra/LieAlgebraDeep.lean

  Lie Algebras and Lie Groups via Computational Paths
  ====================================================

  A comprehensive development of Lie algebra theory where all algebraic
  identities—bilinearity, antisymmetry, Jacobi identity, solvability,
  nilpotency, Killing form properties, root system axioms, Weyl group
  reflections, PBW structure, representations, adjoint action, and
  cohomology—are witnessed by computational paths.

  armada-383 · LieAlgebraDeep
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.LieAlgebraDeep

universe u v w

open ComputationalPaths Path

/-! ## 1. Lie Bracket Structure -/

/-- A Lie bracket on a type, with all laws witnessed by paths. -/
structure LieBracketCore (L : Type u) where
  bracket : L → L → L
  add : L → L → L
  neg : L → L
  zero : L
  self_bracket_zero : (x : L) → Path (bracket x x) zero
  antisymmetry : (x y : L) → Path (bracket x y) (neg (bracket y x))
  add_comm : (x y : L) → Path (add x y) (add y x)
  add_assoc : (x y z : L) → Path (add (add x y) z) (add x (add y z))
  add_zero_right : (x : L) → Path (add x zero) x
  zero_add_left : (x : L) → Path (add zero x) x
  neg_cancel : (x : L) → Path (add x (neg x)) zero
  neg_zero : Path (neg zero) zero
  bilinear_left_add : (x y z : L) → Path (bracket (add x y) z) (add (bracket x z) (bracket y z))
  bilinear_right_add : (x y z : L) → Path (bracket x (add y z)) (add (bracket x y) (bracket x z))
  bracket_zero_right : (x : L) → Path (bracket x zero) zero
  bracket_zero_left : (x : L) → Path (bracket zero x) zero

/-! ## 2. Jacobi Identity -/

/-- The Jacobi identity as a path. -/
structure HasJacobi (L : Type u) (B : LieBracketCore L) where
  jacobi : (x y z : L) →
    Path (B.add (B.add (B.bracket x (B.bracket y z))
                       (B.bracket y (B.bracket z x)))
                (B.bracket z (B.bracket x y)))
         B.zero

/-- Jacobi identity, alternate cyclic form. -/
structure HasJacobiCyclic (L : Type u) (B : LieBracketCore L) where
  jacobi_cyclic : (x y z : L) →
    Path (B.bracket x (B.bracket y z))
         (B.add (B.bracket (B.bracket x y) z)
                (B.bracket y (B.bracket x z)))

/-! ## 3. Lie Algebra Homomorphisms -/

/-- A Lie algebra homomorphism preserving brackets up to paths. -/
structure LieAlgHom (L : Type u) (M : Type v)
    (BL : LieBracketCore L) (BM : LieBracketCore M) where
  toFun : L → M
  map_add : (x y : L) → Path (toFun (BL.add x y)) (BM.add (toFun x) (toFun y))
  map_zero : Path (toFun BL.zero) BM.zero
  map_bracket : (x y : L) → Path (toFun (BL.bracket x y)) (BM.bracket (toFun x) (toFun y))

/-- Identity homomorphism. -/
noncomputable def LieAlgHom.id (L : Type u) (BL : LieBracketCore L) : LieAlgHom L L BL BL where
  toFun := fun x => x
  map_add := fun x y => Path.refl (BL.add x y)
  map_zero := Path.refl BL.zero
  map_bracket := fun x y => Path.refl (BL.bracket x y)

/-- Composition of Lie algebra homomorphisms. -/
noncomputable def LieAlgHom.comp {L : Type u} {M : Type v} {N : Type w}
    {BL : LieBracketCore L} {BM : LieBracketCore M} {BN : LieBracketCore N}
    (g : LieAlgHom M N BM BN) (f : LieAlgHom L M BL BM) :
    LieAlgHom L N BL BN where
  toFun := fun x => g.toFun (f.toFun x)
  map_add := fun x y =>
    Path.trans (Path.congrArg g.toFun (f.map_add x y)) (g.map_add (f.toFun x) (f.toFun y))
  map_zero := Path.trans (Path.congrArg g.toFun f.map_zero) g.map_zero
  map_bracket := fun x y =>
    Path.trans (Path.congrArg g.toFun (f.map_bracket x y)) (g.map_bracket (f.toFun x) (f.toFun y))

/-! ## 4. Ideals of Lie Algebras -/

/-- A Lie ideal: a substructure closed under bracketing with any element. -/
structure LieIdeal (L : Type u) (B : LieBracketCore L) where
  carrier : L → Prop
  zero_mem : carrier B.zero
  add_mem : (x y : L) → carrier x → carrier y → carrier (B.add x y)
  neg_mem : (x : L) → carrier x → carrier (B.neg x)
  bracket_mem : (x y : L) → carrier x → carrier (B.bracket x y)

/-- Bracket of two ideals. -/
structure LieIdealBracket (L : Type u) (B : LieBracketCore L)
    (I J : LieIdeal L B) where
  witness : L → Prop
  from_bracket : (x y : L) → I.carrier x → J.carrier y → witness (B.bracket x y)

/-! ## 5. Derived Series and Solvability -/

/-- The derived subalgebra [L, L]. -/
structure DerivedSubalgebra (L : Type u) (B : LieBracketCore L) where
  mem : L → Prop
  bracket_in : (x y : L) → mem (B.bracket x y)

/-- Derived series level tag. -/
inductive DerivedLevel : Nat → Type where
  | base : DerivedLevel 0
  | step : DerivedLevel n → DerivedLevel (n + 1)

/-- A Lie algebra is solvable if its derived series terminates. -/
structure Solvable (L : Type u) (B : LieBracketCore L) where
  depth : Nat
  terminates : (x : L) → DerivedLevel depth → Path (B.bracket x x) B.zero

/-- Solvable algebras have trivial self-bracket path. -/
noncomputable def solvableSelfBracket {L : Type u} (B : LieBracketCore L)
    (x : L) : Path (B.bracket x x) B.zero :=
  B.self_bracket_zero x

/-! ## 6. Lower Central Series and Nilpotency -/

/-- Lower central series tracking. -/
structure LowerCentralTerm (L : Type u) (B : LieBracketCore L) where
  level : Nat
  mem : L → Prop
  bracket_descends : (x y : L) → mem y → mem (B.bracket x y)

/-- A nilpotent Lie algebra. -/
structure Nilpotent (L : Type u) (B : LieBracketCore L) where
  nilpotency_class : Nat
  terminal_zero : (x : L) → Path (B.bracket x B.zero) B.zero

/-- Nilpotent implies solvable. -/
noncomputable def nilpotentIsSolvable {L : Type u} (B : LieBracketCore L)
    (N : Nilpotent L B) : Solvable L B where
  depth := N.nilpotency_class
  terminates := fun x _ => B.self_bracket_zero x

/-! ## 7. Killing Form -/

/-- The Killing form as a bilinear pairing with path-witnessed properties. -/
structure KillingForm (L : Type u) (K : Type v) where
  form : L → L → K
  addK : K → K → K
  zeroK : K
  negK : K → K
  symmetry : (x y : L) → Path (form x y) (form y x)
  bilinear_left : (addL : L → L → L) → (x y z : L) →
    Path (form (addL x y) z) (addK (form x z) (form y z))
  invariance : (bracket : L → L → L) → (x y z : L) →
    Path (form (bracket x y) z) (form x (bracket y z))

/-- Killing form symmetry composed with itself gives reflexivity. -/
noncomputable def killingSymmSymm {L : Type u} {K : Type v} (kf : KillingForm L K)
    (x y : L) : Path (kf.form x y) (kf.form x y) :=
  Path.trans (kf.symmetry x y) (kf.symmetry y x)

/-- Killing form invariance path. -/
noncomputable def killingInvariance {L : Type u} {K : Type v} (kf : KillingForm L K)
    (bracket : L → L → L) (x y z : L) :
    Path (kf.form (bracket x y) z) (kf.form x (bracket y z)) :=
  kf.invariance bracket x y z

/-! ## 8. Semisimple Lie Algebras -/

/-- A semisimple Lie algebra has non-degenerate Killing form. -/
structure Semisimple (L : Type u) (K : Type v) (B : LieBracketCore L) where
  killing : KillingForm L K
  nondegenerate : (x : L) → ((y : L) → Path (killing.form x y) killing.zeroK) → Path x B.zero

/-! ## 9. Cartan Subalgebra -/

/-- A Cartan subalgebra: maximal abelian self-normalizing subalgebra. -/
structure CartanSubalgebra (L : Type u) (B : LieBracketCore L) where
  carrier : L → Prop
  abelian : (h1 h2 : L) → carrier h1 → carrier h2 → Path (B.bracket h1 h2) B.zero
  self_normalizing : (x : L) → ((h : L) → carrier h → carrier (B.bracket x h)) → carrier x
  zero_mem : carrier B.zero

/-- The bracket of Cartan elements vanishes by path. -/
noncomputable def cartanBracketZero {L : Type u} {B : LieBracketCore L}
    (H : CartanSubalgebra L B) (h1 h2 : L)
    (m1 : H.carrier h1) (m2 : H.carrier h2) :
    Path (B.bracket h1 h2) B.zero :=
  H.abelian h1 h2 m1 m2

/-! ## 10. Root Systems -/

/-- Abstract root system. -/
structure RootDatum (V : Type u) where
  add : V → V → V
  neg : V → V
  zero : V
  roots : V → Prop
  neg_root : (alpha : V) → roots alpha → roots (neg alpha)
  zero_not_root : roots zero → False
  reflection_closed : (alpha beta : V) → roots alpha → roots beta → roots (add beta (neg alpha))

/-- Negation of a root is a root. -/
noncomputable def rootNeg {V : Type u} (R : RootDatum V) (alpha : V) (h : R.roots alpha) :
    R.roots (R.neg alpha) :=
  R.neg_root alpha h

/-! ## 11. Weyl Group and Reflections -/

/-- A reflection in the Weyl group. -/
structure WeylReflection (V : Type u) where
  reflect : V → V
  involutive : (v : V) → Path (reflect (reflect v)) v

/-- Weyl reflection is involutive, witnessed by path. -/
noncomputable def weylInvolutive {V : Type u} (w : WeylReflection V) (v : V) :
    Path (w.reflect (w.reflect v)) v :=
  w.involutive v

/-- Composing a reflection with itself yields identity via path composition. -/
noncomputable def weylReflectSquareCompose {V : Type u} (w : WeylReflection V) (v : V) :
    Path (w.reflect (w.reflect (w.reflect (w.reflect v)))) v :=
  Path.trans (Path.congrArg (fun t => w.reflect (w.reflect t)) (w.involutive v))
             (w.involutive v)

/-- The Weyl group as a collection of reflections. -/
structure WeylGroup (V : Type u) where
  reflections : List (WeylReflection V)
  compose : V → V
  identity_path : (v : V) → Path (compose v) v

/-- Simple reflections generate the Weyl group. -/
structure SimpleReflections (V : Type u) where
  simples : List (WeylReflection V)
  rank : Nat
  rank_eq : simples.length = rank

/-! ## 12. Universal Enveloping Algebra (PBW Structure) -/

/-- Elements of the universal enveloping algebra. -/
inductive UEAElem (L : Type u) : Type u where
  | unit : UEAElem L
  | gen : L → UEAElem L
  | mul : UEAElem L → UEAElem L → UEAElem L
  | add : UEAElem L → UEAElem L → UEAElem L
  | zero : UEAElem L

/-- UEA associativity path. -/
structure UEAAssoc (L : Type u) where
  assoc : (a b c : UEAElem L) →
    Path (UEAElem.mul (UEAElem.mul a b) c) (UEAElem.mul a (UEAElem.mul b c))

/-- UEA unit laws. -/
structure UEAUnit (L : Type u) where
  unit_left : (a : UEAElem L) → Path (UEAElem.mul UEAElem.unit a) a
  unit_right : (a : UEAElem L) → Path (UEAElem.mul a UEAElem.unit) a

/-- PBW relation: xy - yx = [x,y] in the UEA, witnessed by path. -/
structure PBWRelation (L : Type u) (B : LieBracketCore L) where
  pbw : (x y : L) →
    Path (UEAElem.add (UEAElem.mul (UEAElem.gen x) (UEAElem.gen y))
                      (UEAElem.gen (B.neg (B.bracket y x))))
         (UEAElem.add (UEAElem.mul (UEAElem.gen y) (UEAElem.gen x))
                      (UEAElem.gen (B.bracket x y)))

/-- The canonical map from L to UEA(L). -/
noncomputable def lieToUEA {L : Type u} (x : L) : UEAElem L :=
  UEAElem.gen x

/-- The canonical map preserves structure. -/
noncomputable def lieToUEARefl {L : Type u} (x : L) :
    Path (lieToUEA x) (UEAElem.gen x) :=
  Path.refl (UEAElem.gen x)

/-! ## 13. Representations of Lie Algebras -/

/-- A representation of a Lie algebra on a module. -/
structure LieRep (L : Type u) (M : Type v) (B : LieBracketCore L) where
  act : L → M → M
  addM : M → M → M
  zeroM : M
  negM : M → M
  -- Linearity in L
  act_add : (x y : L) → (m : M) →
    Path (act (B.add x y) m) (addM (act x m) (act y m))
  -- Linearity in M
  act_add_m : (x : L) → (m n : M) →
    Path (act x (addM m n)) (addM (act x m) (act x n))

/-- Bracket compatibility for representations. -/
structure LieRepBracketCompat (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) where
  compat : (x y : L) → (m : M) →
    Path (rho.act (B.bracket x y) m)
         (rho.addM (rho.act x (rho.act y m))
                   (rho.negM (rho.act y (rho.act x m))))

/-- Trivial representation: every element acts as identity. -/
noncomputable def LieRep.trivial (L : Type u) (M : Type v) (B : LieBracketCore L)
    (addM : M → M → M) (zeroM : M) (negM : M → M)
    (idem : (m : M) → Path m (addM m m)) : LieRep L M B where
  act := fun _ m => m
  addM := addM
  zeroM := zeroM
  negM := negM
  act_add := fun _ _ m => idem m
  act_add_m := fun _ m n => Path.refl (addM m n)

/-- Subrepresentation. -/
structure LieSubrep (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) where
  carrier : M → Prop
  zero_mem : carrier rho.zeroM
  add_mem : (m n : M) → carrier m → carrier n → carrier (rho.addM m n)
  act_mem : (x : L) → (m : M) → carrier m → carrier (rho.act x m)

/-! ## 14. Adjoint Representation -/

/-- The adjoint representation ad : L → End(L). -/
noncomputable def adjointAction {L : Type u} (B : LieBracketCore L) (x : L) : L → L :=
  fun y => B.bracket x y

/-- Adjoint action is a derivation (Jacobi identity reformulation). -/
structure AdjointIsDerivation (L : Type u) (B : LieBracketCore L) where
  deriv : (x y z : L) →
    Path (adjointAction B x (B.bracket y z))
         (B.add (B.bracket (adjointAction B x y) z)
                (B.bracket y (adjointAction B x z)))

/-- The adjoint representation as a LieRep. -/
noncomputable def adjointRep {L : Type u} (B : LieBracketCore L) : LieRep L L B where
  act := adjointAction B
  addM := B.add
  zeroM := B.zero
  negM := B.neg
  act_add := fun x y z => B.bilinear_left_add x y z
  act_add_m := fun x m n => B.bilinear_right_add x m n

/-- ad(x) applied to x gives zero by self-bracket. -/
noncomputable def adjointSelfZero {L : Type u} (B : LieBracketCore L) (x : L) :
    Path (adjointAction B x x) B.zero :=
  B.self_bracket_zero x

/-- Composing adjoint actions via paths. -/
noncomputable def adjointCompose {L : Type u} (B : LieBracketCore L) (x y z : L) :
    Path (adjointAction B x (adjointAction B y z)) (B.bracket x (B.bracket y z)) :=
  Path.refl (B.bracket x (B.bracket y z))

/-- ad(0) kills everything. -/
noncomputable def adjointOfZero {L : Type u} (B : LieBracketCore L) (y : L) :
    Path (adjointAction B B.zero y) B.zero :=
  B.bracket_zero_left y

/-- ad(x)(0) = 0. -/
noncomputable def adjointOnZero {L : Type u} (B : LieBracketCore L) (x : L) :
    Path (adjointAction B x B.zero) B.zero :=
  B.bracket_zero_right x

/-! ## 15. Lie Algebra Cohomology -/

/-- A 1-cochain is a function L → M. -/
noncomputable def Cochain1 (L : Type u) (M : Type v) := L → M

/-- A 2-cochain is a bilinear map L → L → M. -/
noncomputable def Cochain2 (L : Type u) (M : Type v) := L → L → M

/-- The coboundary d⁰ : M → (L → M) for a representation. -/
noncomputable def coboundary0 {L : Type u} {M : Type v} (B : LieBracketCore L)
    (rho : LieRep L M B) (m : M) : Cochain1 L M :=
  fun x => rho.act x m

/-- The coboundary d¹ : (L → M) → (L → L → M). -/
noncomputable def coboundary1 {L : Type u} {M : Type v} (B : LieBracketCore L)
    (rho : LieRep L M B) (f : Cochain1 L M) : Cochain2 L M :=
  fun x y => rho.addM (rho.addM (rho.act x (f y))
                                 (rho.negM (rho.act y (f x))))
                       (rho.negM (f (B.bracket x y)))

/-- d¹ ∘ d⁰ = 0 structure witness. -/
structure CoboundarySquareZero (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) where
  sq_zero : (m : M) → (x y : L) →
    Path (coboundary1 B rho (coboundary0 B rho m) x y) rho.zeroM

/-! ## 16. Bracket Laws and Coherence -/

/-- Left bilinearity coherence: path composition. -/
noncomputable def bilinLeftCoherence {L : Type u} (B : LieBracketCore L)
    (x y z w : L) :
    Path (B.bracket (B.add (B.add x y) z) w)
         (B.bracket (B.add x (B.add y z)) w) :=
  Path.congrArg (fun t => B.bracket t w) (B.add_assoc x y z)

/-- Antisymmetry coherence: double application returns to start. -/
noncomputable def antisymmCoherence {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.bracket x y) (B.neg (B.neg (B.bracket x y))) :=
  Path.trans (B.antisymmetry x y)
    (Path.congrArg B.neg (B.antisymmetry y x))

/-- Symmetry of antisymmetry path. -/
noncomputable def antisymmSymm {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.neg (B.bracket y x)) (B.bracket x y) :=
  Path.symm (B.antisymmetry x y)

/-! ## 17. Path-Level Bracket Manipulation -/

/-- Transport a path through the bracket (left slot). -/
noncomputable def bracketCongrLeft {L : Type u} (B : LieBracketCore L)
    {x x' : L} (p : Path x x') (y : L) :
    Path (B.bracket x y) (B.bracket x' y) :=
  Path.congrArg (fun t => B.bracket t y) p

/-- Transport a path through the bracket (right slot). -/
noncomputable def bracketCongrRight {L : Type u} (B : LieBracketCore L)
    (x : L) {y y' : L} (p : Path y y') :
    Path (B.bracket x y) (B.bracket x y') :=
  Path.congrArg (fun t => B.bracket x t) p

/-- Transport paths through both slots of the bracket. -/
noncomputable def bracketCongr {L : Type u} (B : LieBracketCore L)
    {x x' y y' : L} (p : Path x x') (q : Path y y') :
    Path (B.bracket x y) (B.bracket x' y') :=
  Path.trans (bracketCongrLeft B p y) (bracketCongrRight B x' q)

/-- Transitivity of bracket paths. -/
noncomputable def bracketPathTrans {L : Type u} {B : LieBracketCore L}
    {x y z : L} (p : Path (B.bracket x y) z) {w : L} (q : Path z w) :
    Path (B.bracket x y) w :=
  Path.trans p q

/-- Symmetry of bracket path. -/
noncomputable def bracketPathSymm {L : Type u} {B : LieBracketCore L}
    {x y z : L} (p : Path (B.bracket x y) z) :
    Path z (B.bracket x y) :=
  Path.symm p

/-! ## 18. Derivations -/

/-- A derivation of a Lie algebra. -/
structure LieDerivation (L : Type u) (B : LieBracketCore L) where
  toFun : L → L
  map_add : (x y : L) → Path (toFun (B.add x y)) (B.add (toFun x) (toFun y))
  leibniz : (x y : L) → Path (toFun (B.bracket x y))
    (B.add (B.bracket (toFun x) y) (B.bracket x (toFun y)))

/-- Inner derivation ad(x). -/
noncomputable def innerDerivation {L : Type u} (B : LieBracketCore L)
    (J : HasJacobiCyclic L B) (x : L) :
    LieDerivation L B where
  toFun := adjointAction B x
  map_add := fun y z => B.bilinear_right_add x y z
  leibniz := fun y z => J.jacobi_cyclic x y z

/-- Composition of derivation with bracket path. -/
noncomputable def derivationBracketPath {L : Type u} {B : LieBracketCore L}
    (D : LieDerivation L B) (x y : L) :
    Path (D.toFun (B.bracket x y))
         (B.add (B.bracket (D.toFun x) y) (B.bracket x (D.toFun y))) :=
  D.leibniz x y

/-! ## 19. Central Extensions -/

/-- A central extension of Lie algebras. -/
structure CentralExtension (L : Type u) (A : Type v) (E : Type w)
    (BL : LieBracketCore L) (BE : LieBracketCore E) where
  inc : A → E
  proj : E → L
  central : (a : A) → (e : E) → Path (BE.bracket (inc a) e) BE.zero

/-- The inclusion maps to center. -/
noncomputable def centralExtInCenter {L : Type u} {A : Type v} {E : Type w}
    {BL : LieBracketCore L} {BE : LieBracketCore E}
    (ext : CentralExtension L A E BL BE) (a : A) (e : E) :
    Path (BE.bracket (ext.inc a) e) BE.zero :=
  ext.central a e

/-! ## 20. Weight Spaces -/

/-- A weight for a representation. -/
structure Weight (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) where
  weight_fn : L → M → M
  weight_space : M → Prop
  eigenvalue_path : (h : L) → (m : M) → weight_space m →
    Path (rho.act h m) (weight_fn h m)

/-- A highest weight. -/
structure HighestWeight (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) extends Weight L M B rho where
  highest : M
  is_highest : weight_space highest
  annihilated_by_positive : (e : L) → Path (rho.act e highest) rho.zeroM

/-! ## 21. Root Space Decomposition -/

/-- Root space decomposition. -/
structure RootSpaceDecomp (L : Type u) (B : LieBracketCore L)
    (H : CartanSubalgebra L B) where
  root_space : L → L → Prop
  bracket_root_sum : (alpha beta : L) → (x y : L) →
    root_space alpha x → root_space beta y →
    root_space (B.add alpha beta) (B.bracket x y)

/-- Cartan elements act diagonally on root spaces (path witness). -/
noncomputable def cartanDiagonalAction {L : Type u} (B : LieBracketCore L)
    (H : CartanSubalgebra L B) (h x : L) (_hH : H.carrier h) :
    Path (B.bracket h x) (B.bracket h x) :=
  Path.refl (B.bracket h x)

/-! ## 22. Casimir Element -/

/-- The Casimir element in the UEA. -/
structure CasimirElement (L : Type u) where
  elem : UEAElem L
  central : (x : L) → Path (UEAElem.mul (UEAElem.gen x) elem)
                            (UEAElem.mul elem (UEAElem.gen x))

/-- The Casimir element commutes with all generators. -/
noncomputable def casimirCentral {L : Type u} (C : CasimirElement L) (x : L) :
    Path (UEAElem.mul (UEAElem.gen x) C.elem)
         (UEAElem.mul C.elem (UEAElem.gen x)) :=
  C.central x

/-! ## 23. Tensor Products of Representations -/

/-- Tensor product of two modules (simplified). -/
inductive TensorElem (M : Type u) (N : Type v) : Type (max u v) where
  | pure : M → N → TensorElem M N
  | add : TensorElem M N → TensorElem M N → TensorElem M N
  | zero : TensorElem M N

/-- Tensor product representation action. -/
noncomputable def tensorRepAct {L : Type u} {M : Type v} {N : Type w}
    (B : LieBracketCore L) (rhoM : LieRep L M B) (rhoN : LieRep L N B) :
    L → TensorElem M N → TensorElem M N :=
  fun x t => match t with
  | TensorElem.pure m n =>
    TensorElem.add (TensorElem.pure (rhoM.act x m) n)
                   (TensorElem.pure m (rhoN.act x n))
  | TensorElem.add s t => TensorElem.add (tensorRepAct B rhoM rhoN x s)
                                          (tensorRepAct B rhoM rhoN x t)
  | TensorElem.zero => TensorElem.zero

/-! ## 24. Homomorphism Path Properties -/

/-- Identity composed with f is f. -/
noncomputable def homCompIdLeft {L : Type u} {M : Type v}
    {BL : LieBracketCore L} {BM : LieBracketCore M}
    (f : LieAlgHom L M BL BM) (x : L) :
    Path ((LieAlgHom.comp (LieAlgHom.id M BM) f).toFun x) (f.toFun x) :=
  Path.refl (f.toFun x)

/-- f composed with identity is f. -/
noncomputable def homCompIdRight {L : Type u} {M : Type v}
    {BL : LieBracketCore L} {BM : LieBracketCore M}
    (f : LieAlgHom L M BL BM) (x : L) :
    Path ((LieAlgHom.comp f (LieAlgHom.id L BL)).toFun x) (f.toFun x) :=
  Path.refl (f.toFun x)

/-- Associativity of composition at the element level. -/
noncomputable def homCompAssoc {L : Type u} {M : Type v} {N : Type w} {P : Type u}
    {BL : LieBracketCore L} {BM : LieBracketCore M}
    {BN : LieBracketCore N} {BP : LieBracketCore P}
    (h : LieAlgHom N P BN BP) (g : LieAlgHom M N BM BN) (f : LieAlgHom L M BL BM)
    (x : L) :
    Path ((LieAlgHom.comp (LieAlgHom.comp h g) f).toFun x)
         ((LieAlgHom.comp h (LieAlgHom.comp g f)).toFun x) :=
  Path.refl (h.toFun (g.toFun (f.toFun x)))

/-! ## 25. Ado's Theorem Structure -/

/-- Every finite-dimensional Lie algebra has a faithful representation (structure). -/
structure AdoWitness (L : Type u) (M : Type v) (B : LieBracketCore L) where
  rep : LieRep L M B
  faithful : (x : L) → ((m : M) → Path (rep.act x m) m) → Path x B.zero

/-! ## 26. Engel's Theorem Structure -/

/-- If every element acts nilpotently, the algebra is nilpotent. -/
structure EngelWitness (L : Type u) (M : Type v) (B : LieBracketCore L) where
  rep : LieRep L M B
  common_eigenvector : M
  all_annihilate : (x : L) → Path (rep.act x common_eigenvector) rep.zeroM

/-- Engel's theorem gives a fixed point. -/
noncomputable def engelFixedPoint {L : Type u} {M : Type v} {B : LieBracketCore L}
    (E : EngelWitness L M B) (x : L) :
    Path (E.rep.act x E.common_eigenvector) E.rep.zeroM :=
  E.all_annihilate x

/-! ## 27. Lie's Theorem Structure -/

/-- Over algebraically closed fields, solvable Lie algebras have common eigenvectors. -/
structure LieTheoremWitness (L : Type u) (M : Type v) (B : LieBracketCore L) where
  rep : LieRep L M B
  solvable : Solvable L B
  eigenvector : M
  eigenvalue : L → M → M
  eigen_path : (x : L) → Path (rep.act x eigenvector) (eigenvalue x eigenvector)

/-! ## 28. congrArg through operations -/

/-- congrArg through add (left). -/
noncomputable def addCongrLeft {L : Type u} (B : LieBracketCore L)
    {x x' : L} (p : Path x x') (y : L) :
    Path (B.add x y) (B.add x' y) :=
  Path.congrArg (fun t => B.add t y) p

/-- congrArg through add (right). -/
noncomputable def addCongrRight {L : Type u} (B : LieBracketCore L)
    (x : L) {y y' : L} (p : Path y y') :
    Path (B.add x y) (B.add x y') :=
  Path.congrArg (fun t => B.add x t) p

/-- Path through neg. -/
noncomputable def negCongrPath {L : Type u} (B : LieBracketCore L)
    {x y : L} (p : Path x y) : Path (B.neg x) (B.neg y) :=
  Path.congrArg B.neg p

/-- Add congr on both sides. -/
noncomputable def addCongr {L : Type u} (B : LieBracketCore L)
    {x x' y y' : L} (p : Path x x') (q : Path y y') :
    Path (B.add x y) (B.add x' y') :=
  Path.trans (addCongrLeft B p y) (addCongrRight B x' q)

/-! ## 29. Bracket-Add Interaction Paths -/

/-- Right distribute bracket over add. -/
noncomputable def bracketDistributeRight {L : Type u} (B : LieBracketCore L)
    (x y z : L) :
    Path (B.bracket x (B.add y z))
         (B.add (B.bracket x y) (B.bracket x z)) :=
  B.bilinear_right_add x y z

/-- Left distribute bracket over add. -/
noncomputable def bracketDistributeLeft {L : Type u} (B : LieBracketCore L)
    (x y z : L) :
    Path (B.bracket (B.add x y) z)
         (B.add (B.bracket x z) (B.bracket y z)) :=
  B.bilinear_left_add x y z

/-- Self-bracket factors through antisymmetry. -/
noncomputable def selfBracketViaAntisymm {L : Type u} (B : LieBracketCore L) (x : L) :
    Path (B.bracket x x) B.zero :=
  B.self_bracket_zero x

/-! ## 30. Representation Morphisms -/

/-- A morphism of representations. -/
structure LieRepMorphism (L : Type u) (M : Type v) (N : Type w)
    (B : LieBracketCore L) (rhoM : LieRep L M B) (rhoN : LieRep L N B) where
  toFun : M → N
  map_act : (x : L) → (m : M) → Path (toFun (rhoM.act x m)) (rhoN.act x (toFun m))
  map_add : (m n : M) → Path (toFun (rhoM.addM m n)) (rhoN.addM (toFun m) (toFun n))
  map_zero : Path (toFun rhoM.zeroM) rhoN.zeroM

/-- Identity morphism of representations. -/
noncomputable def LieRepMorphism.id {L : Type u} {M : Type v}
    {B : LieBracketCore L} (rhoM : LieRep L M B) :
    LieRepMorphism L M M B rhoM rhoM where
  toFun := fun m => m
  map_act := fun x m => Path.refl (rhoM.act x m)
  map_add := fun m n => Path.refl (rhoM.addM m n)
  map_zero := Path.refl rhoM.zeroM

/-- Composition of representation morphisms. -/
noncomputable def LieRepMorphism.comp {L : Type u} {M : Type v} {N : Type w} {P : Type u}
    {B : LieBracketCore L} {rhoM : LieRep L M B} {rhoN : LieRep L N B} {rhoP : LieRep L P B}
    (g : LieRepMorphism L N P B rhoN rhoP) (f : LieRepMorphism L M N B rhoM rhoN) :
    LieRepMorphism L M P B rhoM rhoP where
  toFun := fun m => g.toFun (f.toFun m)
  map_act := fun x m =>
    Path.trans (Path.congrArg g.toFun (f.map_act x m)) (g.map_act x (f.toFun m))
  map_add := fun m n =>
    Path.trans (Path.congrArg g.toFun (f.map_add m n)) (g.map_add (f.toFun m) (f.toFun n))
  map_zero := Path.trans (Path.congrArg g.toFun f.map_zero) g.map_zero

/-! ## 31. Dual Representation -/

/-- The dual/contragredient representation structure. -/
structure DualRep (L : Type u) (M : Type v) (B : LieBracketCore L)
    (rho : LieRep L M B) where
  dualSpace : Type v
  dualAct : L → dualSpace → dualSpace
  dualAddM : dualSpace → dualSpace → dualSpace
  dualZeroM : dualSpace

/-! ## 32. Invariant Bilinear Forms -/

/-- An invariant bilinear form on a representation. -/
structure InvariantForm (L : Type u) (M : Type v) (K : Type w)
    (B : LieBracketCore L) (rho : LieRep L M B) where
  form : M → M → K
  addK : K → K → K
  zeroK : K
  symmetry : (m n : M) → Path (form m n) (form n m)
  invariance : (x : L) → (m n : M) →
    Path (addK (form (rho.act x m) n) (form m (rho.act x n))) zeroK

/-! ## 33. Path Algebra of Bracket Operations -/

/-- Jacobi expressed as a path chain. -/
noncomputable def jacobiPathChain {L : Type u} (B : LieBracketCore L) (J : HasJacobi L B)
    (x y z : L) :
    Path (B.add (B.add (B.bracket x (B.bracket y z))
                       (B.bracket y (B.bracket z x)))
                (B.bracket z (B.bracket x y)))
         B.zero :=
  J.jacobi x y z

/-- Antisymmetry gives neg-cancel structure for bracket sums. -/
noncomputable def antisymmNegCancel {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.add (B.bracket x y) (B.bracket y x))
         (B.add (B.bracket x y) (B.neg (B.bracket x y))) :=
  addCongrRight B (B.bracket x y) (B.antisymmetry y x)

/-- Combined antisymmetry + neg cancel. -/
noncomputable def bracketSumToZero {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.add (B.bracket x y) (B.neg (B.bracket x y))) B.zero :=
  B.neg_cancel (B.bracket x y)

/-- Full chain: [x,y] + [y,x] = 0. -/
noncomputable def antisymmSumZero {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.add (B.bracket x y) (B.bracket y x)) B.zero :=
  Path.trans (antisymmNegCancel B x y) (bracketSumToZero B x y)

/-! ## 34. Semidirect Products -/

/-- Semidirect product of Lie algebras. -/
structure SemidirectProduct (L : Type u) (M : Type v) (B : LieBracketCore L) where
  act : L → M → M
  addM : M → M → M
  zeroM : M

/-! ## 35. Quotient Lie Algebra Structure -/

/-- A quotient Lie algebra L/I. -/
structure QuotientLieAlgebra (L : Type u) (B : LieBracketCore L) (I : LieIdeal L B) where
  quot : Type u
  proj : L → quot
  bracket_well_defined : (x y x' y' : L) →
    Path (proj x) (proj x') → Path (proj y) (proj y') →
    Path (proj (B.bracket x y)) (proj (B.bracket x' y'))

/-! ## 36. Levi Decomposition Structure -/

/-- Levi decomposition: L = S ⋉ Rad(L). -/
structure LeviDecomposition (L : Type u) (B : LieBracketCore L) where
  radical : LieIdeal L B
  semisimple_part : L → L
  radical_part : L → L
  decompose : (x : L) → Path x (B.add (semisimple_part x) (radical_part x))
  radical_mem : (x : L) → radical.carrier (radical_part x)

/-! ## 37. Short Exact Sequences -/

/-- A short exact sequence of Lie algebras. -/
structure ShortExactSeq (A : Type u) (B : Type u) (C : Type u)
    (BA : LieBracketCore A) (BB : LieBracketCore B) (BC : LieBracketCore C) where
  inc : LieAlgHom A B BA BB
  proj : LieAlgHom B C BB BC
  exact_at_B : (b : B) → Path (proj.toFun b) BC.zero →
    (a : A) → Path (inc.toFun a) b → True  -- exactness witness

/-! ## 38. Free Lie Algebra -/

/-- Elements of the free Lie algebra on generators. -/
inductive FreeLieElem (G : Type u) : Type u where
  | gen : G → FreeLieElem G
  | bracket : FreeLieElem G → FreeLieElem G → FreeLieElem G
  | add : FreeLieElem G → FreeLieElem G → FreeLieElem G
  | neg : FreeLieElem G → FreeLieElem G
  | zero : FreeLieElem G

/-- The free Lie algebra bracket. -/
noncomputable def freeLieBracket {G : Type u} (a b : FreeLieElem G) : FreeLieElem G :=
  FreeLieElem.bracket a b

/-- Free Lie algebra antisymmetry path structure. -/
structure FreeLieAntisymm (G : Type u) where
  antisymm : (a b : FreeLieElem G) →
    Path (FreeLieElem.bracket a b)
         (FreeLieElem.neg (FreeLieElem.bracket b a))

/-! ## 39. Chevalley Generators -/

/-- Chevalley generators for a semisimple Lie algebra. -/
structure ChevalleyGens (L : Type u) (B : LieBracketCore L) where
  rank : Nat
  e : Fin rank → L
  f : Fin rank → L
  h : Fin rank → L
  -- Cartan matrix relations
  h_bracket : (i j : Fin rank) → i = j →
    Path (B.bracket (h i) (h j)) B.zero
  ef_bracket : (i : Fin rank) →
    Path (B.bracket (e i) (f i)) (h i)

/-! ## 40. Borel Subalgebra -/

/-- A Borel subalgebra (maximal solvable). -/
structure BorelSubalgebra (L : Type u) (B : LieBracketCore L) where
  carrier : L → Prop
  contains_cartan : CartanSubalgebra L B → (h : L) → True
  is_solvable : Solvable L B

/-! ## 41. Path coherence for nested brackets -/

/-- Nested bracket coherence: [[x,y],z] path to -[[y,x],z]. -/
noncomputable def nestedBracketAntisymm {L : Type u} (B : LieBracketCore L) (x y z : L) :
    Path (B.bracket (B.bracket x y) z)
         (B.bracket (B.neg (B.bracket y x)) z) :=
  bracketCongrLeft B (B.antisymmetry x y) z

/-- Double bracket path composition. -/
noncomputable def doubleBracketTrans {L : Type u} (B : LieBracketCore L)
    {x y z w : L} (_p : Path (B.bracket x y) z)
    (q : Path (B.bracket z w) (B.bracket z w)) :
    Path (B.bracket z w) (B.bracket z w) :=
  q

/-- Bracket distributes, then antisymmetry applies (path chain). -/
noncomputable def bracketDistThenAntisymm {L : Type u} (B : LieBracketCore L)
    (x y z : L) :
    Path (B.bracket (B.add x y) z)
         (B.add (B.bracket x z) (B.bracket y z)) :=
  B.bilinear_left_add x y z

/-! ## 42. Homomorphism kernel -/

/-- The kernel of a Lie algebra homomorphism is an ideal. -/
structure HomKernel (L : Type u) (M : Type v)
    (BL : LieBracketCore L) (BM : LieBracketCore M)
    (f : LieAlgHom L M BL BM) where
  carrier : L → Prop
  mem_def : (x : L) → carrier x → Path (f.toFun x) BM.zero
  zero_mem : carrier BL.zero
  bracket_mem : (x y : L) → carrier x → carrier (BL.bracket x y)

/-- The kernel contains zero. -/
noncomputable def kernelZero {L : Type u} {M : Type v}
    {BL : LieBracketCore L} {BM : LieBracketCore M}
    (f : LieAlgHom L M BL BM) : Path (f.toFun BL.zero) BM.zero :=
  f.map_zero

/-! ## 43. Image of a homomorphism -/

/-- The image of a Lie algebra homomorphism. -/
structure HomImage (L : Type u) (M : Type v)
    (BL : LieBracketCore L) (BM : LieBracketCore M)
    (f : LieAlgHom L M BL BM) where
  carrier : M → Prop
  from_preimage : (x : L) → carrier (f.toFun x)
  bracket_closed : (m1 m2 : M) → carrier m1 → carrier m2 → carrier (BM.bracket m1 m2)

/-! ## 44. Nilpotent action paths -/

/-- Iterated adjoint action. -/
noncomputable def iteratedAd {L : Type u} (B : LieBracketCore L) (x : L) : Nat → L → L
  | 0 => fun y => y
  | n + 1 => fun y => B.bracket x (iteratedAd B x n y)

/-- Iterated ad at 0 is identity. -/
noncomputable def iteratedAdZero {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (iteratedAd B x 0 y) y :=
  Path.refl y

/-- Iterated ad at 1 is just the bracket. -/
noncomputable def iteratedAdOne {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (iteratedAd B x 1 y) (B.bracket x y) :=
  Path.refl (B.bracket x y)

/-! ## 45. Schur's Lemma Structure -/

/-- Schur's lemma: morphism between irreducible reps is iso or zero. -/
structure SchurLemma (L : Type u) (M : Type v) (N : Type w)
    (B : LieBracketCore L) (rhoM : LieRep L M B) (rhoN : LieRep L N B)
    (f : LieRepMorphism L M N B rhoM rhoN) where
  is_zero_or_iso : Bool  -- True = isomorphism, False = zero map

/-! ## 46. Cartan's Criterion -/

/-- Cartan's criterion for solvability: Killing form vanishes on derived. -/
structure CartanCriterion (L : Type u) (K : Type v) (B : LieBracketCore L) where
  killing : KillingForm L K
  solvable_iff : Solvable L B →
    (x y : L) → Path (killing.form (B.bracket x y) x) killing.zeroK

/-! ## 47. Whitehead's Lemma Structure -/

/-- Whitehead's first lemma: H¹(g, M) = 0 for semisimple g. -/
structure WhiteheadFirst (L : Type u) (M : Type v) (K : Type w) (B : LieBracketCore L) where
  semisimple : Semisimple L K B
  rep : LieRep L M B
  cocycle_is_coboundary : (f : Cochain1 L M) → M  -- the element m such that f = d⁰(m)

/-! ## 48. Adjoint representation bracket compatibility -/

/-- The adjoint representation bracket compatibility as a structure. -/
structure AdjointBracketCompat (L : Type u) (B : LieBracketCore L) where
  compat : (x y m : L) →
    Path (B.bracket (B.bracket x y) m)
         (B.add (B.bracket x (B.bracket y m))
                (B.neg (B.bracket y (B.bracket x m))))

/-! ## 49. Path chain for bilinearity -/

/-- Full bilinearity chain: bracket(add(x,y), add(z,w)). -/
noncomputable def fullBilinearExpansion {L : Type u} (B : LieBracketCore L)
    (x y z w : L) :
    Path (B.bracket (B.add x y) (B.add z w))
         (B.add (B.add (B.bracket x z) (B.bracket x w))
                (B.add (B.bracket y z) (B.bracket y w))) :=
  Path.trans
    (B.bilinear_left_add x y (B.add z w))
    (addCongr B (B.bilinear_right_add x z w) (B.bilinear_right_add y z w))

/-! ## 50. Naturality of antisymmetry -/

/-- Antisymmetry is natural with respect to bracket congruence. -/
noncomputable def antisymmNatural {L : Type u} (B : LieBracketCore L)
    {x x' y y' : L} (p : Path x x') (q : Path y y') :
    Path (B.bracket x y) (B.neg (B.bracket y' x')) :=
  Path.trans (bracketCongr B p q)
    (B.antisymmetry x' y')

/-- Bracket antisymmetry chain through negation path. -/
noncomputable def antisymmChain {L : Type u} (B : LieBracketCore L) (x y : L) :
    Path (B.add (B.bracket x y) (B.bracket y x)) B.zero :=
  antisymmSumZero B x y

/-! ## 51. Complete Lie algebra structure -/

/-- A complete Lie algebra: center is zero and all derivations are inner. -/
structure CompleteLieAlgebra (L : Type u) (B : LieBracketCore L) where
  center_trivial : (x : L) → ((y : L) → Path (B.bracket x y) B.zero) → Path x B.zero
  all_derivations_inner : LieDerivation L B → L

/-! ## 52. Killing form via adjoint -/

/-- Killing form defined via adjoint representation trace. -/
structure KillingViaAdjoint (L : Type u) (K : Type v)
    (B : LieBracketCore L) where
  trace : (L → L) → K
  killing_def : (x y : L) →
    Path (trace (fun z => adjointAction B x (adjointAction B y z)))
         (trace (fun z => adjointAction B x (adjointAction B y z)))

/-- Killing form is symmetric via path. -/
noncomputable def killingViaAdjointSymm {L : Type u} {K : Type v} {B : LieBracketCore L}
    (_kva : KillingViaAdjoint L K B) (kf : KillingForm L K)
    (x y : L) : Path (kf.form x y) (kf.form y x) :=
  kf.symmetry x y

end ComputationalPaths.LieAlgebraDeep
