import ComputationalPaths.Path.OmegaGroupoid.GlobularPasting
import ComputationalPaths.Path.OmegaGroupoid.NativeGlobularTower

/-!
# Boundary-compatible endomorphism operations

Operations retain their pasting arity and evaluate labelled inputs of that
arity. The zero-dimensional operation is normalized to the identity.
This file constructs a collection and its evaluation, not yet an operad:
substitution, units and contraction are separate obligations.
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
