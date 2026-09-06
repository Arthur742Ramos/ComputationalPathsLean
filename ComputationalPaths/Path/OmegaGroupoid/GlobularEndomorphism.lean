import ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
import ComputationalPaths.Path.OmegaGroupoid.NativeGlobularTower

/-!
# Boundary-compatible endomorphism operations

Operations retain their pasting arity and evaluate labelled inputs of that
arity. The zero-dimensional operation is normalized to the identity.
This file constructs a collection, evaluation, unit and substitution maps,
and a native contraction. The operadic coherence laws remain to be proved;
the displayed maps alone do not yet constitute an operad.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

namespace Endomorphism

abbrev Shapes := Pasting.globular GlobularSet.terminal.{u}

/-- Two consecutive levels of arity-indexed evaluations. -/
structure Stage (G : GlobularSet.{u}) (n : Nat) where
  lower : Type u
  upper : Type u
  source : upper → lower
  target : upper → lower
  lowerArity : lower → Shapes.Cell n
  upperArity : upper → Shapes.Cell (n + 1)
  source_arity : ∀ o, Shapes.source (upperArity o) = lowerArity (source o)
  target_arity : ∀ o, Shapes.target (upperArity o) = lowerArity (target o)
  lowerEval : (o : lower) → (p : Pasting n G) →
    lowerArity o = (GlobularCollection.shape G).app (n := n) p → G.Cell n
  upperEval : (o : upper) → (p : Pasting (n + 1) G) →
    upperArity o = (GlobularCollection.shape G).app (n := n + 1) p → G.Cell (n + 1)
  source_eval : ∀ o p h, G.source (upperEval o p h) =
    lowerEval (source o) (Pasting.source p)
      ((source_arity o).symm.trans ((_root_.congrArg Shapes.source h).trans
        ((GlobularCollection.shape G).source_app p)))
  target_eval : ∀ o p h, G.target (upperEval o p h) =
    lowerEval (target o) (Pasting.target p)
      ((target_arity o).symm.trans ((_root_.congrArg Shapes.target h).trans
        ((GlobularCollection.shape G).target_app p)))

/-- A higher operation has specified parallel boundary operations. Its
evaluation is required to commute with those exact boundary evaluations. -/
structure NextOperation {G : GlobularSet.{u}} {n : Nat} (S : Stage G n) where
  left : S.upper
  right : S.upper
  parallel_source : S.source left = S.source right
  parallel_target : S.target left = S.target right
  arity : Shapes.Cell (n + 2)
  source_arity : Shapes.source arity = S.upperArity left
  target_arity : Shapes.target arity = S.upperArity right
  eval : (p : Pasting (n + 2) G) → arity = (GlobularCollection.shape G).app (n := n + 2) p →
    G.Cell (n + 2)
  source_eval : ∀ p h, G.source (eval p h) =
    S.upperEval left (Pasting.source p)
      (source_arity.symm.trans ((_root_.congrArg Shapes.source h).trans
        ((GlobularCollection.shape G).source_app p)))
  target_eval : ∀ p h, G.target (eval p h) =
    S.upperEval right (Pasting.target p)
      (target_arity.symm.trans ((_root_.congrArg Shapes.target h).trans
        ((GlobularCollection.shape G).target_app p)))

def Stage.next {G : GlobularSet.{u}} {n : Nat} (S : Stage G n) : Stage G (n + 1) where
  lower := S.upper
  upper := NextOperation S
  source := NextOperation.left
  target := NextOperation.right
  lowerArity := S.upperArity
  upperArity := NextOperation.arity
  source_arity := NextOperation.source_arity
  target_arity := NextOperation.target_arity
  lowerEval := S.upperEval
  upperEval o := o.eval
  source_eval o := o.source_eval
  target_eval o := o.target_eval

/-- A one-dimensional operation evaluates a path diagram with its original
endpoints. No associativity equation is imposed on the resulting traces. -/
structure OneOperation (G : GlobularSet.{u}) where
  arity : Shapes.Cell 1
  eval : (p : Pasting 1 G) → arity = (GlobularCollection.shape G).app (n := 1) p → G.Cell 1
  source_eval : ∀ p h, G.source (eval p h) = Pasting.source p
  target_eval : ∀ p h, G.target (eval p h) = Pasting.target p

def base (G : GlobularSet.{u}) : Stage G 0 where
  lower := PUnit
  upper := OneOperation G
  source _ := PUnit.unit
  target _ := PUnit.unit
  lowerArity _ := PUnit.unit
  upperArity := OneOperation.arity
  source_arity _ := @Subsingleton.elim PUnit _ _ _
  target_arity _ := @Subsingleton.elim PUnit _ _ _
  lowerEval _ p _ := p
  upperEval o := o.eval
  source_eval o := o.source_eval
  target_eval o := o.target_eval

def stages (G : GlobularSet.{u}) : (n : Nat) → Stage G n
  | 0 => base G
  | n + 1 => (stages G n).next

def operations (G : GlobularSet.{u}) : GlobularSet.{u} where
  Cell n := (stages G n).lower
  source {n} := (stages G n).source
  target {n} := (stages G n).target
  source_source p := p.parallel_source
  target_source p := p.parallel_target

def arity (G : GlobularSet.{u}) : GlobularSet.Map (operations G) Shapes where
  app {n} := (stages G n).lowerArity
  source_app {n} := (stages G n).source_arity
  target_app {n} := (stages G n).target_arity

def collection (G : GlobularSet.{u}) : GlobularCollection.{u} := ⟨operations G, arity G⟩

/-- Evaluation is a globular map on the actual collection application,
whose cells pair an operation with a labelled diagram of matching arity. -/
def evaluation (G : GlobularSet.{u}) : GlobularSet.Map ((collection G).application G) G where
  app {n} p := (stages G n).lowerEval p.val.1 p.val.2 p.property
  source_app {n} p := (stages G n).source_eval p.val.1 p.val.2 p.property
  target_app {n} p := (stages G n).target_eval p.val.1 p.val.2 p.property

theorem evaluation_objects (G : GlobularSet.{u})
    (p : ((collection G).application G).Cell 0) : (evaluation G).app p = p.val.2 := rfl

/-- The normalization needed to interpret a collection in these
endomorphisms: every object operation returns its input object. -/
def Normalized {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) : Prop :=
  ∀ p : (C.application G).Cell 0, e.app p = p.val.2

/-- Two levels of abstraction, retaining the exact evaluation equation.
This record supports dimension recursion, not an assumed operadic law. -/
structure AbstractionStage {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (n : Nat) where
  lower : C.operations.Cell n → (stages G n).lower
  upper : C.operations.Cell (n + 1) → (stages G n).upper
  source_upper : ∀ o, (stages G n).source (upper o) = lower (C.operations.source o)
  target_upper : ∀ o, (stages G n).target (upper o) = lower (C.operations.target o)
  lower_arity : ∀ o, (stages G n).lowerArity (lower o) = C.arity.app o
  upper_arity : ∀ o, (stages G n).upperArity (upper o) = C.arity.app o
  lower_eval : ∀ o p h, (stages G n).lowerEval (lower o) p ((lower_arity o).trans h) =
    e.app ⟨⟨o, p⟩, h⟩
  upper_eval : ∀ o p h, (stages G n).upperEval (upper o) p ((upper_arity o).trans h) =
    e.app ⟨⟨o, p⟩, h⟩

def AbstractionStage.next {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    {e : GlobularSet.Map (C.application G) G} {n : Nat}
    (R : AbstractionStage e n) : AbstractionStage e (n + 1) where
  lower := R.upper
  upper o := {
    left := R.upper (C.operations.source o)
    right := R.upper (C.operations.target o)
    parallel_source := (R.source_upper _).trans
      ((_root_.congrArg R.lower (C.operations.source_source o)).trans (R.source_upper _).symm)
    parallel_target := (R.target_upper _).trans
      ((_root_.congrArg R.lower (C.operations.target_source o)).trans (R.target_upper _).symm)
    arity := C.arity.app o
    source_arity := (C.arity.source_app o).trans (R.upper_arity _).symm
    target_arity := (C.arity.target_app o).trans (R.upper_arity _).symm
    eval := fun p h => e.app ⟨⟨o, p⟩, h⟩
    source_eval := fun p h => (e.source_app ⟨⟨o, p⟩, h⟩).trans (R.upper_eval _ _ _).symm
    target_eval := fun p h => (e.target_app ⟨⟨o, p⟩, h⟩).trans (R.upper_eval _ _ _).symm }
  source_upper _ := rfl
  target_upper _ := rfl
  lower_arity := R.upper_arity
  upper_arity _ := rfl
  lower_eval := R.upper_eval
  upper_eval _ _ _ := rfl

def abstractionBase {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) : AbstractionStage e 0 where
  lower _ := PUnit.unit
  upper o := {
    arity := C.arity.app o
    eval := fun p h => e.app ⟨⟨o, p⟩, h⟩
    source_eval := fun p h => (e.source_app ⟨⟨o, p⟩, h⟩).trans (h0 _)
    target_eval := fun p h => (e.target_app ⟨⟨o, p⟩, h⟩).trans (h0 _) }
  source_upper _ := rfl
  target_upper _ := rfl
  lower_arity _ := @Subsingleton.elim PUnit _ _ _
  upper_arity _ := rfl
  lower_eval o p h := (h0 ⟨⟨o, p⟩, h⟩).symm
  upper_eval _ _ _ := rfl

def abstractionStages {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) :
    (n : Nat) → AbstractionStage e n
  | 0 => abstractionBase e h0
  | n + 1 => (abstractionStages e h0 n).next

/-- Abstract an actual normalized globular evaluation into operations,
without quotienting its values or imposing any new evaluation equations. -/
def abstractionMap {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) :
    GlobularSet.Map C.operations (operations G) where
  app {n} := (abstractionStages e h0 n).lower
  source_app {n} := (abstractionStages e h0 n).source_upper
  target_app {n} := (abstractionStages e h0 n).target_upper

def abstraction {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) :
    GlobularCollection.Hom C (collection G) where
  operations := abstractionMap e h0
  arity := by
    apply GlobularSet.Map.ext
    intro n o
    exact (abstractionStages e h0 n).lower_arity o

/-- Abstraction followed by evaluation recovers the supplied map exactly,
including its unquotiented higher-dimensional values. -/
theorem evaluation_abstraction {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) :
    GlobularSet.Map.comp (evaluation G) ((abstraction e h0).application G) = e := by
  apply GlobularSet.Map.ext
  intro n p
  exact (abstractionStages e h0 n).lower_eval p.val.1 p.val.2 p.property

theorem OneOperation.ext {G : GlobularSet.{u}} (o q : OneOperation G)
    (ha : o.arity = q.arity)
    (he : ∀ p h k, o.eval p h = q.eval p k) : o = q := by
  rcases o with ⟨oa, oe, os, ot⟩
  rcases q with ⟨qa, qe, qs, qt⟩
  dsimp at ha he
  cases ha
  have hh : oe = qe := funext (fun p => funext (fun h => he p h h))
  cases hh
  rfl

theorem NextOperation.ext {G : GlobularSet.{u}} {n : Nat} {S : Stage G n}
    (o q : NextOperation S) (hl : o.left = q.left) (hr : o.right = q.right)
    (ha : o.arity = q.arity)
    (he : ∀ p h k, o.eval p h = q.eval p k) : o = q := by
  rcases o with ⟨ol, or, ops, opt, oa, osa, ota, oe, ose, ote⟩
  rcases q with ⟨ql, qr, qps, qpt, qa, qsa, qta, qe, qse, qte⟩
  dsimp at hl hr ha he
  cases hl
  cases hr
  cases ha
  have hh : oe = qe := funext (fun p => funext (fun h => he p h h))
  cases hh
  rfl

/-- Evaluation detects collection maps into the normalized endomorphisms.
Thus later operadic laws can be proved by their actual action on inputs. -/
theorem evaluation_injective {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (f g : GlobularCollection.Hom C (collection G))
    (he : GlobularSet.Map.comp (evaluation G) (f.application G) =
      GlobularSet.Map.comp (evaluation G) (g.application G)) : f = g := by
  have fa {n} (o : C.operations.Cell n) :
      (stages G n).lowerArity (f.operations.app o) = C.arity.app o :=
    _root_.congrArg (fun k : GlobularSet.Map C.operations Shapes => k.app o) f.arity
  have ga {n} (o : C.operations.Cell n) :
      (stages G n).lowerArity (g.operations.app o) = C.arity.app o :=
    _root_.congrArg (fun k : GlobularSet.Map C.operations Shapes => k.app o) g.arity
  have ev {n} (o : C.operations.Cell n) (p : Pasting n G)
      (h : C.arity.app o = (GlobularCollection.shape G).app (n := n) p) :
      (stages G n).lowerEval (f.operations.app o) p ((fa o).trans h) =
        (stages G n).lowerEval (g.operations.app o) p ((ga o).trans h) :=
    _root_.congrArg (fun k : GlobularSet.Map (C.application G) G =>
      k.app ⟨⟨o, p⟩, h⟩) he
  apply GlobularCollection.Hom.ext
  apply GlobularSet.Map.ext
  intro n
  induction n with
  | zero => intro o; exact @Subsingleton.elim PUnit _ _ _
  | succ n ih =>
    intro o
    cases n with
    | zero =>
      apply OneOperation.ext
      · exact (fa o).trans (ga o).symm
      · intro p h k
        exact ev o p ((fa o).symm.trans h)
    | succ n =>
      apply NextOperation.ext
      · exact (f.operations.source_app o).trans
          ((ih (C.operations.source o)).trans (g.operations.source_app o).symm)
      · exact (f.operations.target_app o).trans
          ((ih (C.operations.target o)).trans (g.operations.target_app o).symm)
      · exact (fa o).trans (ga o).symm
      · intro p h k
        exact ev o p ((fa o).symm.trans h)

/-- The universal property is for normalized globular evaluations, not
yet for algebras satisfying a unit or multiplication law. -/
theorem existsUnique_abstraction {C : GlobularCollection.{u}} {G : GlobularSet.{u}}
    (e : GlobularSet.Map (C.application G) G) (h0 : Normalized e) :
    ∃! f : GlobularCollection.Hom C (collection G),
      GlobularSet.Map.comp (evaluation G) (f.application G) = e := by
  refine ⟨abstraction e h0, evaluation_abstraction e h0, ?_⟩
  intro f hf
  exact evaluation_injective f (abstraction e h0) (hf.trans (evaluation_abstraction e h0).symm)

theorem identityEvaluation_normalized (G : GlobularSet.{u}) :
    Normalized (GlobularCollection.identityApplicationOut G) := by
  intro p
  exact _root_.congrArg (fun k : GlobularSet.Map (GlobularCollection.identity.application G)
    (Pasting.globular G) => k.app p) (GlobularCollection.identityApplicationOut_inputs G)

/-- The unit operation extracts the singleton input, at every dimension. -/
noncomputable def unit (G : GlobularSet.{u}) :
    GlobularCollection.Hom GlobularCollection.identity (collection G) :=
  abstraction (GlobularCollection.identityApplicationOut G) (identityEvaluation_normalized G)

theorem evaluation_unit (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (evaluation G) ((unit G).application G) =
      GlobularCollection.identityApplicationOut G :=
  evaluation_abstraction _ _

/-- Evaluate a substituted operation by recovering its nested labelled
inputs, evaluating the inner operations, then evaluating the outer one. -/
noncomputable def multiplicationEvaluation (G : GlobularSet.{u}) :
    GlobularSet.Map (((collection G).substitute (collection G)).application G) G :=
  GlobularSet.Map.comp (evaluation G)
    (GlobularSet.Map.comp ((collection G).map (evaluation G))
      ((collection G).substitutionComparisonInverse (collection G) G))

theorem multiplicationEvaluation_normalized (G : GlobularSet.{u}) :
    Normalized (multiplicationEvaluation G) := by
  intro p
  have h := ((collection G).substitutionComparison_unique_lift (collection G) G p).choose_spec.1
  exact _root_.congrArg (fun q : (((collection G).substitute (collection G)).application G).Cell 0 =>
    q.val.2) h

/-- Concrete substitution of endomorphism operations. Its evaluation law
is proved below; the monoid's coherence laws are still separate obligations. -/
noncomputable def multiplication (G : GlobularSet.{u}) :
    GlobularCollection.Hom ((collection G).substitute (collection G)) (collection G) :=
  abstraction (multiplicationEvaluation G) (multiplicationEvaluation_normalized G)

theorem evaluation_multiplication (G : GlobularSet.{u}) :
    GlobularSet.Map.comp (evaluation G) ((multiplication G).application G) =
      multiplicationEvaluation G := evaluation_abstraction _ _

/-- The concrete unit acts as the identity on every input cell, not just
on its boundary or equality proof. -/
theorem evaluation_unit_input (G : GlobularSet.{u}) {n : Nat} (p : G.Cell n) :
    (evaluation G).app (((unit G).application G).app
      ((GlobularCollection.identityApplicationIn G).app p)) = p := by
  have hu := _root_.congrArg (fun k : GlobularSet.Map
    (GlobularCollection.identity.application G) G =>
      k.app ((GlobularCollection.identityApplicationIn G).app p)) (evaluation_unit G)
  exact hu.trans (_root_.congrArg (fun k : GlobularSet.Map G G => k.app p)
    (GlobularCollection.identityApplicationIso G).inv_hom_id)

/-- Substituting a nested operation and then evaluating equals nested
evaluation, in every dimension and on the actual labelled pasting input. -/
theorem evaluation_multiplication_nested (G : GlobularSet.{u}) {n : Nat}
    (p : ((collection G).application ((collection G).application G)).Cell n) :
    (evaluation G).app (((multiplication G).application G).app
      (((collection G).substitutionComparison (collection G) G).app p)) =
        (evaluation G).app (((collection G).map (evaluation G)).app p) := by
  have hm := _root_.congrArg (fun k : GlobularSet.Map
    (((collection G).substitute (collection G)).application G) G =>
      k.app (((collection G).substitutionComparison (collection G) G).app p))
    (evaluation_multiplication G)
  have hi := _root_.congrArg (fun k : GlobularSet.Map
    ((collection G).application ((collection G).application G))
    ((collection G).application ((collection G).application G)) => k.app p)
    ((collection G).substitutionComparisonIso (collection G) G).hom_inv_id
  exact hm.trans (_root_.congrArg (fun q =>
    (evaluation G).app (((collection G).map (evaluation G)).app q)) hi)

/-- Recover the actual trace carried by a one-dimensional hom label. -/
def nativeEdge {A : Type u} {a b : (NativeTower.globular A).Cell 0}
    (e : ((NativeTower.globular A).hom a b).Cell 0) : Path a.down b.down := by
  rcases e with ⟨⟨x, y, p⟩, hx, hy⟩
  have hx' : x = a.down := _root_.congrArg ULift.down hx
  have hy' : y = b.down := _root_.congrArg ULift.down hy
  exact hx' ▸ hy' ▸ p

/-- Right-associated evaluation of a labelled one-dimensional diagram.
This composes its actual path traces; it does not erase them to `Eq`. -/
noncomputable def nativeChain {A : Type u} {a b : (NativeTower.globular A).Cell 0} :
    Chain (fun a b => ((NativeTower.globular A).hom a b).Cell 0) a b → Path a.down b.down
  | .nil a => Path.refl a.down
  | .cons e p => Path.trans (nativeEdge e) (nativeChain p)

theorem nativeChain_cons {A : Type u} {a b c : (NativeTower.globular A).Cell 0}
    (e : ((NativeTower.globular A).hom a b).Cell 0)
    (p : Chain (fun a b => ((NativeTower.globular A).hom a b).Cell 0) b c) :
    nativeChain (.cons e p) = Path.trans (nativeEdge e) (nativeChain p) := rfl

theorem nativeChain_pair {A : Type u} {a b c : (NativeTower.globular A).Cell 0}
    (e : ((NativeTower.globular A).hom a b).Cell 0)
    (f : ((NativeTower.globular A).hom b c).Cell 0) :
    nativeChain (.cons e (.cons f (.nil c))) =
      Path.trans (nativeEdge e) (Path.trans (nativeEdge f) (Path.refl c.down)) := rfl

/-- There is a native one-operation over every one-dimensional shape,
including empty chains. Both endpoints are preserved on every labelling. -/
noncomputable def nativeOne (A : Type u) (a : Shapes.{u + 1}.Cell 1) :
    OneOperation (NativeTower.globular A) where
  arity := a
  eval p _ := ULift.up ⟨p.1.down, p.2.1.down, nativeChain p.2.2⟩
  source_eval p _ := by cases p with | mk a p => cases a; rfl
  target_eval p _ := by rcases p with ⟨a, b, p⟩; cases b; rfl

/-- Every positive-dimensional pair of parallel native operations extends
over any specified matching arity. Fillers act pointwise on labelled inputs;
they do not identify the underlying raw `RwEq` witnesses. -/
noncomputable def nativeNext {A : Type u} {n : Nat}
    (S : Stage (NativeTower.globular A) n) (l r : S.upper)
    (hs : S.source l = S.source r) (ht : S.target l = S.target r)
    (a : Shapes.Cell (n + 2))
    (ha : Shapes.source a = S.upperArity l) (hb : Shapes.target a = S.upperArity r) :
    NextOperation S := by
  let left (p : Pasting (n + 2) (NativeTower.globular A))
      (h : a = (GlobularCollection.shape (NativeTower.globular A)).app (n := n + 2) p) :=
    S.upperEval l (Pasting.source p)
      (ha.symm.trans ((_root_.congrArg Shapes.source h).trans
        ((GlobularCollection.shape (NativeTower.globular A)).source_app p)))
  let right (p : Pasting (n + 2) (NativeTower.globular A))
      (h : a = (GlobularCollection.shape (NativeTower.globular A)).app (n := n + 2) p) :=
    S.upperEval r (Pasting.target p)
      (hb.symm.trans ((_root_.congrArg Shapes.target h).trans
        ((GlobularCollection.shape (NativeTower.globular A)).target_app p)))
  have source_match p h : NativeTower.source (left p h) = NativeTower.source (right p h) := by
    dsimp [left, right]
    refine (S.source_eval l _ _).trans (Eq.trans ?_ (S.source_eval r _ _).symm)
    simp only [hs, Pasting.source_source]
  have target_match p h : NativeTower.target (left p h) = NativeTower.target (right p h) := by
    dsimp [left, right]
    refine (S.target_eval l _ _).trans (Eq.trans ?_ (S.target_eval r _ _).symm)
    simp only [ht, Pasting.target_source]
  exact {
    left := l, right := r, parallel_source := hs, parallel_target := ht
    arity := a, source_arity := ha, target_arity := hb
    eval := fun p h => NativeTower.fillPositive (left p h) (right p h)
      (source_match p h) (target_match p h)
    source_eval := fun p h => (NativeTower.fillPositive_boundary _ _ _ _).1
    target_eval := fun p h => (NativeTower.fillPositive_boundary _ _ _ _).2 }

/-- The normalized native endomorphism collection has an actual contraction
over the pasting-shape map in every positive dimension. This is not yet a
contractible operad: its substitution and unit laws remain to be supplied. -/
noncomputable def nativeContraction (A : Type u) :
    GlobularSet.Contraction (arity (NativeTower.globular A)) where
  lift {n} p := by
    cases n with
    | zero =>
      exact ⟨nativeOne A p.arity, @Subsingleton.elim PUnit _ _ _,
        @Subsingleton.elim PUnit _ _ _, rfl⟩
    | succ n =>
      have hh : (operations (NativeTower.globular A)).source p.boundary.left =
          (operations (NativeTower.globular A)).source p.boundary.right ∧
          (operations (NativeTower.globular A)).target p.boundary.left =
          (operations (NativeTower.globular A)).target p.boundary.right := by
        cases p.boundary.parallel with
        | cells hs ht => exact ⟨hs, ht⟩
      exact ⟨nativeNext (stages (NativeTower.globular A) n)
        p.boundary.left p.boundary.right hh.1 hh.2 p.arity
        p.source_arity.symm p.target_arity.symm, rfl, rfl, rfl⟩

end Endomorphism

end ComputationalPaths.Path.OmegaFoundations
