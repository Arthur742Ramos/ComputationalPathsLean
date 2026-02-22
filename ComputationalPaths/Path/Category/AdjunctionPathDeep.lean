/-
  ComputationalPaths/Path/Category/AdjunctionPathDeep.lean

  Adjunctions and Monads via Computational Paths

  We develop the theory of adjunctions, monads, Kleisli composition,
  monad algebras, and Beck's monadicity structure entirely through
  Path-valued constructions. Every coherence law is witnessed by
  explicit Path operations: congrArg for functoriality, trans for
  composition, symm for inverses. Equalities between paths use Lean's
  propositional equality (UIP).

  Author: armada-330 (AdjunctionPathDeep)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open ComputationalPaths.Path

universe u v w

namespace AdjunctionPathDeep

-- ============================================================
-- Section 1: Foundational Structures
-- ============================================================

/-- A Path-valued endofunctor on a type -/
structure PathFunctor (A : Type u) where
  obj : A → A
  map : {x y : A} → Path x y → Path (obj x) (obj y)
  map_id : (x : A) → map (Path.refl x) = Path.refl (obj x)
  map_comp : {x y z : A} → (p : Path x y) → (q : Path y z) →
    map (p.trans q) = (map p).trans (map q)

/-- A Path-valued functor between two types -/
structure PathFunctorAB (A : Type u) (B : Type v) where
  obj : A → B
  map : {x y : A} → Path x y → Path (obj x) (obj y)
  map_id : (x : A) → map (Path.refl x) = Path.refl (obj x)
  map_comp : {x y z : A} → (p : Path x y) → (q : Path y z) →
    map (p.trans q) = (map p).trans (map q)

/-- A Path-valued natural transformation between functors A → B -/
structure PathNatTrans {A : Type u} {B : Type v}
    (F G : PathFunctorAB A B) where
  component : (x : A) → Path (F.obj x) (G.obj x)
  naturality : {x y : A} → (p : Path x y) →
    (F.map p).trans (component y) = (component x).trans (G.map p)

-- ============================================================
-- Section 2: Adjunction Structure
-- ============================================================

/-- An adjunction F ⊣ G via unit and counit with triangle identities -/
structure PathAdjunction (A : Type u) (B : Type v) where
  F : PathFunctorAB A B
  G : PathFunctorAB B A
  eta : (x : A) → Path x (G.obj (F.obj x))
  eps : (y : B) → Path (F.obj (G.obj y)) y
  eta_nat : {x x' : A} → (p : Path x x') →
    p.trans (eta x') = (eta x).trans (G.map (F.map p))
  eps_nat : {y y' : B} → (q : Path y y') →
    (F.map (G.map q)).trans (eps y') = (eps y).trans q
  triangle_left : (x : A) →
    (F.map (eta x)).trans (eps (F.obj x)) = Path.refl (F.obj x)
  triangle_right : (y : B) →
    (eta (G.obj y)).trans (G.map (eps y)) = Path.refl (G.obj y)

-- Theorem 1: Unit component is a path from x to GF(x)
noncomputable def unit_path {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    Path x (adj.G.obj (adj.F.obj x)) :=
  adj.eta x

-- Theorem 2: Counit component is a path from FG(y) to y
noncomputable def counit_path {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (y : B) :
    Path (adj.F.obj (adj.G.obj y)) y :=
  adj.eps y

-- Theorem 3: The triangle identity for F
theorem triangle_F_identity {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    (adj.F.map (adj.eta x)).trans (adj.eps (adj.F.obj x)) =
        Path.refl (adj.F.obj x) :=
  adj.triangle_left x

-- Theorem 4: The triangle identity for G
theorem triangle_G_identity {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (y : B) :
    (adj.eta (adj.G.obj y)).trans (adj.G.map (adj.eps y)) =
        Path.refl (adj.G.obj y) :=
  adj.triangle_right y

-- Theorem 5: Symmetry of triangle identity for F
theorem triangle_F_symm {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    Path.refl (adj.F.obj x) =
    (adj.F.map (adj.eta x)).trans (adj.eps (adj.F.obj x)) :=
  (adj.triangle_left x).symm

-- ============================================================
-- Section 3: Monad from Adjunction
-- ============================================================

/-- The monad T = GF arising from an adjunction -/
noncomputable def monadFromAdj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) : PathFunctor A where
  obj := fun x => adj.G.obj (adj.F.obj x)
  map := fun p => adj.G.map (adj.F.map p)
  map_id := fun x => by
    rw [adj.F.map_id x, adj.G.map_id]
  map_comp := fun p q => by
    rw [adj.F.map_comp p q, adj.G.map_comp]

-- Theorem 6: Monad unit η : x → T(x) from adjunction unit
noncomputable def monad_unit_from_adj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    Path x ((monadFromAdj adj).obj x) :=
  adj.eta x

-- Theorem 7: Monad multiplication μ = GεF : T²(x) → T(x)
noncomputable def monad_mult_from_adj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    Path ((monadFromAdj adj).obj ((monadFromAdj adj).obj x))
         ((monadFromAdj adj).obj x) :=
  adj.G.map (adj.eps (adj.F.obj x))

-- Theorem 8: Left unit law: μ ∘ ηT = id (from triangle identity for G)
theorem monad_left_unit {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    (adj.eta (adj.G.obj (adj.F.obj x))).trans
      (adj.G.map (adj.eps (adj.F.obj x))) =
    Path.refl (adj.G.obj (adj.F.obj x)) :=
  adj.triangle_right (adj.F.obj x)

-- Theorem 9: Right unit law uses triangle identity for F plus functoriality
theorem monad_right_unit {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (x : A) :
    (adj.G.map (adj.F.map (adj.eta x))).trans
      (adj.G.map (adj.eps (adj.F.obj x))) =
    Path.refl (adj.G.obj (adj.F.obj x)) := by
  rw [← adj.G.map_comp]
  rw [adj.triangle_left x]
  exact adj.G.map_id (adj.F.obj x)

-- ============================================================
-- Section 4: Path-valued Monad Laws (standalone)
-- ============================================================

/-- A monad on a type via Path operations -/
structure PathMonad (A : Type u) where
  T : PathFunctor A
  eta : (x : A) → Path x (T.obj x)
  mu : (x : A) → Path (T.obj (T.obj x)) (T.obj x)
  left_unit : (x : A) →
    (eta (T.obj x)).trans (mu x) = Path.refl (T.obj x)
  right_unit : (x : A) →
    (T.map (eta x)).trans (mu x) = Path.refl (T.obj x)
  assoc : (x : A) →
    (mu (T.obj x)).trans (mu x) = (T.map (mu x)).trans (mu x)

-- Theorem 10: Monad unit coherence (left)
theorem monad_left_unit_coherence {A : Type u}
    (M : PathMonad A) (x : A) :
    (M.eta (M.T.obj x)).trans (M.mu x) = Path.refl (M.T.obj x) :=
  M.left_unit x

-- Theorem 11: Monad unit coherence (right)
theorem monad_right_unit_coherence {A : Type u}
    (M : PathMonad A) (x : A) :
    (M.T.map (M.eta x)).trans (M.mu x) = Path.refl (M.T.obj x) :=
  M.right_unit x

-- Theorem 12: Monad associativity coherence
theorem monad_assoc_coherence {A : Type u}
    (M : PathMonad A) (x : A) :
    (M.mu (M.T.obj x)).trans (M.mu x) =
    (M.T.map (M.mu x)).trans (M.mu x) :=
  M.assoc x

-- ============================================================
-- Section 5: Kleisli Composition via Path.trans
-- ============================================================

/-- Kleisli arrow: a → T(b) as a Path -/
noncomputable def KleisliArr {A : Type u} (M : PathMonad A) (x y : A) :=
  Path x (M.T.obj y)

-- Theorem 13: Kleisli identity arrow
noncomputable def kleisli_id {A : Type u} (M : PathMonad A) (x : A) :
    KleisliArr M x x :=
  M.eta x

-- Theorem 14: Kleisli composition via trans and mu
noncomputable def kleisli_comp {A : Type u} (M : PathMonad A) {x y z : A}
    (f : KleisliArr M x y) (g : KleisliArr M y z) :
    KleisliArr M x z :=
  f.trans ((M.T.map g).trans (M.mu z))

-- Theorem 15: Kleisli identity is the monad unit
theorem kleisli_id_is_eta {A : Type u} (M : PathMonad A) (x : A) :
    kleisli_id M x = M.eta x :=
  rfl

-- Theorem 16: Kleisli composition uses trans
theorem kleisli_comp_uses_trans {A : Type u} (M : PathMonad A)
    {x y z : A} (f : KleisliArr M x y) (g : KleisliArr M y z) :
    kleisli_comp M f g = f.trans ((M.T.map g).trans (M.mu z)) :=
  rfl

-- Theorem 17: Kleisli composition yields a path
noncomputable def kleisli_comp_path {A : Type u} (M : PathMonad A)
    {x y z : A} (f : KleisliArr M x y) (g : KleisliArr M y z) :
    Path x (M.T.obj z) :=
  kleisli_comp M f g

-- Theorem 18: Kleisli right identity: f >=> id = f
theorem kleisli_right_id {A : Type u} (M : PathMonad A)
    {x y : A} (f : KleisliArr M x y) :
    kleisli_comp M f (kleisli_id M y) = f := by
  unfold kleisli_comp kleisli_id
  rw [M.right_unit y, Path.trans_refl_right]

-- ============================================================
-- Section 6: Monad Algebras
-- ============================================================

/-- An algebra for a monad M -/
structure PathAlgebra {A : Type u} (M : PathMonad A) where
  carrier : A
  structure_map : Path (M.T.obj carrier) carrier
  unit_law : (M.eta carrier).trans structure_map = Path.refl carrier
  assoc_law : (M.mu carrier).trans structure_map =
              (M.T.map structure_map).trans structure_map

-- Theorem 19: Free algebra for a monad
noncomputable def freeAlgebra {A : Type u} (M : PathMonad A) (x : A) :
    PathAlgebra M where
  carrier := M.T.obj x
  structure_map := M.mu x
  unit_law := M.left_unit x
  assoc_law := M.assoc x

-- Theorem 20: Free algebra carrier is T(x)
theorem free_algebra_carrier {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).carrier = M.T.obj x :=
  rfl

-- Theorem 21: Free algebra structure map is μ
theorem free_algebra_structure {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).structure_map = M.mu x :=
  rfl

-- Theorem 22: Algebra unit law
theorem algebra_unit_law {A : Type u} (M : PathMonad A)
    (alg : PathAlgebra M) :
    (M.eta alg.carrier).trans alg.structure_map = Path.refl alg.carrier :=
  alg.unit_law

-- Theorem 23: Algebra associativity law
theorem algebra_assoc_law {A : Type u} (M : PathMonad A)
    (alg : PathAlgebra M) :
    (M.mu alg.carrier).trans alg.structure_map =
    (M.T.map alg.structure_map).trans alg.structure_map :=
  alg.assoc_law

-- ============================================================
-- Section 7: Algebra Morphisms
-- ============================================================

/-- A morphism between monad algebras -/
structure AlgebraMorphism {A : Type u} {M : PathMonad A}
    (alg1 alg2 : PathAlgebra M) where
  morph : Path alg1.carrier alg2.carrier
  commutes : (M.T.map morph).trans alg2.structure_map =
             alg1.structure_map.trans morph

-- Theorem 24: Identity algebra morphism
noncomputable def algebra_id_morph {A : Type u} {M : PathMonad A}
    (alg : PathAlgebra M) :
    AlgebraMorphism alg alg where
  morph := Path.refl alg.carrier
  commutes := by
    rw [M.T.map_id]
    simp

-- Theorem 25: Composition of algebra morphisms
noncomputable def algebra_comp_morph {A : Type u} {M : PathMonad A}
    {alg1 alg2 alg3 : PathAlgebra M}
    (f : AlgebraMorphism alg1 alg2)
    (g : AlgebraMorphism alg2 alg3) :
    AlgebraMorphism alg1 alg3 where
  morph := f.morph.trans g.morph
  commutes := by
    rw [M.T.map_comp f.morph g.morph]
    rw [Path.trans_assoc]
    rw [g.commutes]
    rw [← Path.trans_assoc]
    rw [f.commutes]
    rw [Path.trans_assoc]

-- ============================================================
-- Section 8: Natural Transformation Operations
-- ============================================================

/-- Vertical composition of natural transformations -/
noncomputable def pathNatTransComp {A : Type u} {B : Type v}
    {F G H : PathFunctorAB A B}
    (alpha : PathNatTrans F G) (beta : PathNatTrans G H) :
    PathNatTrans F H where
  component := fun x => (alpha.component x).trans (beta.component x)
  naturality := fun {x y} p => by
    rw [Path.trans_assoc]
    rw [← Path.trans_assoc (F.map p) (alpha.component y) (beta.component y)]
    rw [alpha.naturality p]
    rw [Path.trans_assoc (alpha.component x) (G.map p) (beta.component y)]
    rw [beta.naturality p]

-- Theorem 26: Composed natural transformation component
theorem natTransComp_component {A : Type u} {B : Type v}
    {F G H : PathFunctorAB A B}
    (alpha : PathNatTrans F G) (beta : PathNatTrans G H) (x : A) :
    (pathNatTransComp alpha beta).component x =
    (alpha.component x).trans (beta.component x) :=
  rfl

/-- Identity natural transformation -/
noncomputable def pathNatTransId {A : Type u} {B : Type v}
    (F : PathFunctorAB A B) : PathNatTrans F F where
  component := fun x => Path.refl (F.obj x)
  naturality := fun p => by
    simp

-- Theorem 27: Identity natural transformation has refl components
theorem natTransId_component {A : Type u} {B : Type v}
    (F : PathFunctorAB A B) (x : A) :
    (pathNatTransId F).component x = Path.refl (F.obj x) :=
  rfl

-- ============================================================
-- Section 9: Adjunction naturality squares
-- ============================================================

-- Theorem 28: Unit naturality as a commuting square
theorem unit_naturality_square {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) {x x' : A} (p : Path x x') :
    p.trans (adj.eta x') = (adj.eta x).trans (adj.G.map (adj.F.map p)) :=
  adj.eta_nat p

-- Theorem 29: Counit naturality as a commuting square
theorem counit_naturality_square {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) {y y' : B} (q : Path y y') :
    (adj.F.map (adj.G.map q)).trans (adj.eps y') = (adj.eps y).trans q :=
  adj.eps_nat q

-- ============================================================
-- Section 10: Path congruence and functoriality
-- ============================================================

-- Theorem 30: congrArg preserves refl
theorem congrArg_refl_eq {A : Type u} {B : Type v}
    (f : A → B) (x : A) :
    Path.congrArg f (Path.refl x) = Path.refl (f x) := by
  simp [Path.congrArg, Path.refl]

-- Theorem 31: congrArg distributes over trans
theorem congrArg_trans_dist {A : Type u} {B : Type v}
    (f : A → B) {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg f (p.trans q) =
    (Path.congrArg f p).trans (Path.congrArg f q) :=
  Path.congrArg_trans f p q

-- Theorem 32: congrArg preserves symm
theorem congrArg_symm_pres {A : Type u} {B : Type v}
    (f : A → B) {x y : A} (p : Path x y) :
    Path.congrArg f p.symm = (Path.congrArg f p).symm :=
  Path.congrArg_symm f p

-- Theorem 33: Double congrArg for composition
theorem congrArg_congrArg {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {x y : A} (p : Path x y) :
    Path.congrArg g (Path.congrArg f p) = Path.congrArg (g ∘ f) p :=
  (Path.congrArg_comp g f p).symm

-- Theorem 34: congrArg of id
theorem congrArg_id_eq {A : Type u} {x y : A} (p : Path x y) :
    Path.congrArg id p = p :=
  Path.congrArg_id p

-- ============================================================
-- Section 11: Symmetry properties
-- ============================================================

-- Theorem 35: symm is involution
theorem symm_involution {A : Type u} {x y : A} (p : Path x y) :
    p.symm.symm = p := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.symm]
    induction steps with
    | nil => simp
    | cons s t ih =>
      simp [List.map_cons, ih]

-- Theorem 36: symm of refl is refl
theorem symm_refl_eq {A : Type u} (x : A) :
    (Path.refl x).symm = Path.refl x := by
  simp [Path.refl, Path.symm]

-- Theorem 37: symm of trans is trans of symms reversed
theorem symm_trans_eq {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  simp

-- Theorem 38: trans associativity
theorem path_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (p.trans q).trans r = p.trans (q.trans r) :=
  Path.trans_assoc p q r

-- Theorem 39: trans left identity
theorem path_trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    (Path.refl a).trans p = p :=
  Path.trans_refl_left p

-- Theorem 40: trans right identity
theorem path_trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    p.trans (Path.refl b) = p :=
  Path.trans_refl_right p

-- ============================================================
-- Section 12: Monad Morphisms
-- ============================================================

/-- A morphism of monads -/
structure MonadMorphism {A : Type u} (M N : PathMonad A) where
  tau : (x : A) → Path (M.T.obj x) (N.T.obj x)
  unit_compat : (x : A) →
    (M.eta x).trans (tau x) = N.eta x
  mult_compat : (x : A) →
    (M.mu x).trans (tau x) =
    (tau (M.T.obj x)).trans ((N.T.map (tau x)).trans (N.mu x))

-- Theorem 41: Monad morphism preserves unit
theorem monad_morph_unit {A : Type u} {M N : PathMonad A}
    (phi : MonadMorphism M N) (x : A) :
    (M.eta x).trans (phi.tau x) = N.eta x :=
  phi.unit_compat x

-- Theorem 42: Monad morphism compatibility with multiplication
theorem monad_morph_mult {A : Type u} {M N : PathMonad A}
    (phi : MonadMorphism M N) (x : A) :
    (M.mu x).trans (phi.tau x) =
    (phi.tau (M.T.obj x)).trans ((N.T.map (phi.tau x)).trans (N.mu x)) :=
  phi.mult_compat x

-- ============================================================
-- Section 13: Kleisli Category Structure
-- ============================================================

/-- The Kleisli category of a monad -/
structure KleisliCategory {A : Type u} (M : PathMonad A) where
  hom : A → A → Type u := fun x y => KleisliArr M x y
  id_arr : (x : A) → KleisliArr M x x := fun x => kleisli_id M x
  comp_arr : {x y z : A} → KleisliArr M x y → KleisliArr M y z →
    KleisliArr M x z := fun f g => kleisli_comp M f g

-- Theorem 43: Kleisli composition expands to trans
theorem kleisli_comp_expand {A : Type u} (M : PathMonad A)
    {w x y z : A}
    (f : KleisliArr M w x) (g : KleisliArr M x y) (h : KleisliArr M y z) :
    kleisli_comp M f (kleisli_comp M g h) =
    f.trans ((M.T.map (g.trans ((M.T.map h).trans (M.mu z)))).trans (M.mu z)) :=
  rfl

-- ============================================================
-- Section 14: Free-Forgetful Adjunction from Monad
-- ============================================================

/-- Free functor sends morphisms via T.map -/
noncomputable def freeFunctorMap {A : Type u} (M : PathMonad A) {x y : A}
    (p : Path x y) : Path (M.T.obj x) (M.T.obj y) :=
  M.T.map p

-- Theorem 44: Free functor preserves identity
theorem freeFunctor_pres_id {A : Type u} (M : PathMonad A) (x : A) :
    freeFunctorMap M (Path.refl x) = Path.refl (M.T.obj x) :=
  M.T.map_id x

-- Theorem 45: Free functor preserves composition
theorem freeFunctor_pres_comp {A : Type u} (M : PathMonad A)
    {x y z : A} (p : Path x y) (q : Path y z) :
    freeFunctorMap M (p.trans q) =
    (freeFunctorMap M p).trans (freeFunctorMap M q) :=
  M.T.map_comp p q

-- ============================================================
-- Section 15: Beck's Monadicity Structure
-- ============================================================

/-- A split coequalizer witnessed by paths -/
structure PathSplitCoequalizer {A : Type u}
    (s : A) (coeq : A) where
  proj : Path s coeq
  section_map : Path coeq s
  retract : proj.trans section_map = Path.refl s

/-- Beck's monadicity condition -/
structure BeckMonadicity {A : Type u} (M : PathMonad A) where
  alg_split : (alg : PathAlgebra M) →
    Path alg.carrier (M.T.obj alg.carrier)
  split_is_unit : (alg : PathAlgebra M) →
    alg_split alg = M.eta alg.carrier
  retract : (alg : PathAlgebra M) →
    (alg_split alg).trans alg.structure_map = Path.refl alg.carrier

-- Theorem 46: Beck split section is monad unit
theorem beck_split_section {A : Type u} {M : PathMonad A}
    (beck : BeckMonadicity M) (alg : PathAlgebra M) :
    beck.alg_split alg = M.eta alg.carrier :=
  beck.split_is_unit alg

-- Theorem 47: Beck retract condition
theorem beck_retract {A : Type u} {M : PathMonad A}
    (beck : BeckMonadicity M) (alg : PathAlgebra M) :
    (beck.alg_split alg).trans alg.structure_map = Path.refl alg.carrier :=
  beck.retract alg

-- Theorem 48: Beck retract rewrites to algebra unit law
theorem beck_retract_via_unit {A : Type u} {M : PathMonad A}
    (beck : BeckMonadicity M) (alg : PathAlgebra M) :
    (M.eta alg.carrier).trans alg.structure_map = Path.refl alg.carrier := by
  rw [← beck.split_is_unit alg]
  exact beck.retract alg

-- ============================================================
-- Section 16: Comonad Structure (Dual)
-- ============================================================

/-- A comonad on a type via Path operations (dual of monad) -/
structure PathComonad (A : Type u) where
  D : PathFunctor A
  epsilon : (x : A) → Path (D.obj x) x
  delta : (x : A) → Path (D.obj x) (D.obj (D.obj x))
  left_counit : (x : A) →
    (delta x).trans (epsilon (D.obj x)) = Path.refl (D.obj x)
  right_counit : (x : A) →
    (delta x).trans (D.map (epsilon x)) = Path.refl (D.obj x)
  coassoc : (x : A) →
    (delta x).trans (delta (D.obj x)) =
    (delta x).trans (D.map (delta x))

-- Theorem 49: Comonad counit
noncomputable def comonad_counit {A : Type u} (W : PathComonad A) (x : A) :
    Path (W.D.obj x) x :=
  W.epsilon x

-- Theorem 50: Comonad comultiplication
noncomputable def comonad_comult {A : Type u} (W : PathComonad A) (x : A) :
    Path (W.D.obj x) (W.D.obj (W.D.obj x)) :=
  W.delta x

-- Theorem 51: Comonad left counit law
theorem comonad_left_counit_law {A : Type u} (W : PathComonad A) (x : A) :
    (W.delta x).trans (W.epsilon (W.D.obj x)) = Path.refl (W.D.obj x) :=
  W.left_counit x

-- Theorem 52: Comonad right counit law
theorem comonad_right_counit_law {A : Type u} (W : PathComonad A) (x : A) :
    (W.delta x).trans (W.D.map (W.epsilon x)) = Path.refl (W.D.obj x) :=
  W.right_counit x

-- Theorem 53: Comonad coassociativity law
theorem comonad_coassoc_law {A : Type u} (W : PathComonad A) (x : A) :
    (W.delta x).trans (W.delta (W.D.obj x)) =
    (W.delta x).trans (W.D.map (W.delta x)) :=
  W.coassoc x

-- ============================================================
-- Section 17: Comonad from Adjunction
-- ============================================================

/-- Comonad D = FG from adjunction -/
noncomputable def comonadFunctorFromAdj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) : PathFunctor B where
  obj := fun y => adj.F.obj (adj.G.obj y)
  map := fun q => adj.F.map (adj.G.map q)
  map_id := fun y => by
    rw [adj.G.map_id y, adj.F.map_id]
  map_comp := fun p q => by
    rw [adj.G.map_comp p q, adj.F.map_comp]

-- Theorem 54: Comonad counit from adjunction
noncomputable def comonad_counit_from_adj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (y : B) :
    Path (adj.F.obj (adj.G.obj y)) y :=
  adj.eps y

-- Theorem 55: Comonad comultiplication from adjunction: FηG
noncomputable def comonad_comult_from_adj {A : Type u} {B : Type v}
    (adj : PathAdjunction A B) (y : B) :
    Path (adj.F.obj (adj.G.obj y))
         (adj.F.obj (adj.G.obj (adj.F.obj (adj.G.obj y)))) :=
  adj.F.map (adj.eta (adj.G.obj y))

-- ============================================================
-- Section 18: Whiskering and Functor Composition
-- ============================================================

-- Theorem 56: Left whiskering component: F maps α components
noncomputable def leftWhisker_comp {A : Type u} {B : Type v} {C : Type w}
    (F : PathFunctorAB B C) {G H : PathFunctorAB A B}
    (alpha : PathNatTrans G H) (x : A) :
    Path (F.obj (G.obj x)) (F.obj (H.obj x)) :=
  F.map (alpha.component x)

-- Theorem 57: Left whiskering naturality via functoriality
theorem leftWhisker_naturality {A : Type u} {B : Type v} {C : Type w}
    (F : PathFunctorAB B C) {G H : PathFunctorAB A B}
    (alpha : PathNatTrans G H) {x y : A} (p : Path x y) :
    (F.map (G.map p)).trans (F.map (alpha.component y)) =
    (F.map (alpha.component x)).trans (F.map (H.map p)) := by
  rw [← F.map_comp, alpha.naturality, F.map_comp]

-- Theorem 58: Right whiskering component: α at F(x)
noncomputable def rightWhisker_comp {A : Type u} {B : Type v} {C : Type w}
    {G H : PathFunctorAB B C}
    (alpha : PathNatTrans G H) (F : PathFunctorAB A B) (x : A) :
    Path (G.obj (F.obj x)) (H.obj (F.obj x)) :=
  alpha.component (F.obj x)

-- Theorem 59: Right whiskering naturality
theorem rightWhisker_naturality {A : Type u} {B : Type v} {C : Type w}
    {G H : PathFunctorAB B C}
    (alpha : PathNatTrans G H) (F : PathFunctorAB A B)
    {x y : A} (p : Path x y) :
    (G.map (F.map p)).trans (alpha.component (F.obj y)) =
    (alpha.component (F.obj x)).trans (H.map (F.map p)) :=
  alpha.naturality (F.map p)

-- ============================================================
-- Section 19: Distributive Laws
-- ============================================================

/-- A distributive law of monad S over monad T -/
structure DistributiveLaw {A : Type u} (S T : PathMonad A) where
  law : (x : A) → Path (S.T.obj (T.T.obj x)) (T.T.obj (S.T.obj x))
  unit_S_compat : (x : A) →
    (Path.congrArg S.T.obj (T.eta x)).trans (law x) =
    T.eta (S.T.obj x)
  unit_T_compat : (x : A) →
    (Path.congrArg T.T.obj (S.eta x)).trans (law x).symm =
    S.eta (T.T.obj x)

-- Theorem 58: Distributive law swaps functor applications
noncomputable def dist_law_swap {A : Type u} {S T : PathMonad A}
    (dl : DistributiveLaw S T) (x : A) :
    Path (S.T.obj (T.T.obj x)) (T.T.obj (S.T.obj x)) :=
  dl.law x

-- ============================================================
-- Section 20: Additional Coherence
-- ============================================================

-- Theorem 59: Free algebra unit law unfolds to monad left unit
theorem free_alg_unit_unfolds {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).unit_law = M.left_unit x :=
  rfl

-- Theorem 60: Free algebra associativity unfolds to monad associativity
theorem free_alg_assoc_unfolds {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).assoc_law = M.assoc x :=
  rfl

end AdjunctionPathDeep

end ComputationalPaths
