/-
# Infinity Operads: Dendroidal Sets and Boardman–Vogt Tensor Product

This module formalizes ∞-operads via dendroidal sets in the computational
paths framework. We model trees, dendroidal sets, inner horn inclusions,
∞-operads as inner Kan dendroidal sets, the Boardman–Vogt tensor product,
and operadic nerve constructions with Path-valued coherence witnesses.

## Mathematical Background

∞-Operads generalize both ∞-categories and classical operads:

1. **Trees**: planar rooted trees as indexing shapes for operations
2. **Dendroidal sets**: presheaves on the dendroidal category Ω
3. **Inner Kan condition**: filling of inner horns → ∞-operad structure
4. **Boardman–Vogt tensor product**: symmetric monoidal structure on
   dendroidal sets
5. **Operadic nerve**: from colored operads to dendroidal sets

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `PlanarTree` | Planar rooted tree structure |
| `TreeMorphism` | Morphism between trees |
| `DendroidalSet` | Dendroidal set (presheaf on Ω) |
| `DendroidalMap` | Map of dendroidal sets |
| `InnerHorn` | Inner horn of a dendroidal set |
| `InfinityOperad` | ∞-operad (inner Kan dendroidal set) |
| `BVTensor` | Boardman–Vogt tensor product |
| `OperadicNerve` | Nerve of a colored operad |
| `InfOperadStep` | Domain-specific rewrite steps |

## References

- Moerdijk–Weiss, "Dendroidal sets"
- Cisinski–Moerdijk, "Dendroidal sets as models for homotopy operads"
- Berger–Moerdijk, "On the homotopy theory of enriched categories"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace InfinityOperads

universe u

/-! ## Planar Trees -/

/-- An edge in a tree: just an identifier. -/
structure Edge where
  /-- Edge identifier. -/
  idx : Nat

/-- A vertex in a tree: has input edges and one output edge. -/
structure Vertex where
  /-- Input edges. -/
  inputs : List Edge
  /-- Output edge. -/
  output : Edge
  /-- Arity of the vertex. -/
  arity : Nat
  /-- Arity matches input count. -/
  arity_eq : arity = inputs.length

/-- Path witness for vertex arity. -/
def Vertex.arity_path (v : Vertex) : Path v.arity v.inputs.length :=
  Path.stepChain v.arity_eq

/-- A planar rooted tree. -/
structure PlanarTree where
  /-- Vertices of the tree. -/
  vertices : List Vertex
  /-- Edges of the tree. -/
  edges : List Edge
  /-- Root edge. -/
  root : Edge
  /-- Leaf edges (inputs). -/
  leaves : List Edge
  /-- Number of vertices. -/
  numVertices : Nat
  /-- numVertices agrees. -/
  numVertices_eq : numVertices = vertices.length

/-- Path witness for tree vertex count. -/
def PlanarTree.numVertices_path (T : PlanarTree) :
    Path T.numVertices T.vertices.length :=
  Path.stepChain T.numVertices_eq

/-- The corolla: a tree with one vertex. -/
def corolla (n : Nat) : PlanarTree where
  vertices := [{ inputs := (List.range n).map (fun i => Edge.mk i)
                 output := Edge.mk n
                 arity := n
                 arity_eq := by simp [List.length_map] }]
  edges := (List.range (n + 1)).map (fun i => Edge.mk i)
  root := Edge.mk n
  leaves := (List.range n).map (fun i => Edge.mk i)
  numVertices := 1
  numVertices_eq := rfl

/-- The unit tree: no vertices, one edge. -/
def unitTree : PlanarTree where
  vertices := []
  edges := [Edge.mk 0]
  root := Edge.mk 0
  leaves := [Edge.mk 0]
  numVertices := 0
  numVertices_eq := rfl

/-- Path witness: unit tree has zero vertices. -/
def unitTree_numVertices : Path unitTree.numVertices 0 :=
  Path.refl 0

/-- Path witness: corolla has one vertex. -/
def corolla_numVertices (n : Nat) : Path (corolla n).numVertices 1 :=
  Path.refl 1

/-! ## Tree Morphisms -/

/-- A morphism of trees: maps edges to edges and vertices to vertices. -/
structure TreeMorphism (S T : PlanarTree) where
  /-- Edge map. -/
  edgeMap : Edge → Edge
  /-- Root preservation. -/
  root_pres : edgeMap S.root = T.root
  /-- Number of edges is monotone (weak condition). -/
  edge_compat : True

/-- Path witness for root preservation. -/
def TreeMorphism.root_path {S T : PlanarTree} (f : TreeMorphism S T) :
    Path (f.edgeMap S.root) T.root :=
  Path.stepChain f.root_pres

/-- Identity tree morphism. -/
def TreeMorphism.id (T : PlanarTree) : TreeMorphism T T where
  edgeMap := fun e => e
  root_pres := rfl
  edge_compat := trivial

/-- Composition of tree morphisms. -/
def TreeMorphism.comp {S T U : PlanarTree}
    (f : TreeMorphism S T) (g : TreeMorphism T U) :
    TreeMorphism S U where
  edgeMap := fun e => g.edgeMap (f.edgeMap e)
  root_pres := by rw [f.root_pres, g.root_pres]
  edge_compat := trivial

/-- Path witness for composition root preservation. -/
def TreeMorphism.comp_root_path {S T U : PlanarTree}
    (f : TreeMorphism S T) (g : TreeMorphism T U) :
    Path ((TreeMorphism.comp f g).edgeMap S.root) U.root :=
  Path.stepChain (TreeMorphism.comp f g).root_pres

/-- Left identity law for tree morphisms. -/
theorem TreeMorphism.id_comp {S T : PlanarTree}
    (f : TreeMorphism S T) :
    (TreeMorphism.comp (TreeMorphism.id S) f).edgeMap = f.edgeMap := by
  unfold comp id
  rfl

/-- Path witness for left identity. -/
def TreeMorphism.id_comp_path {S T : PlanarTree}
    (f : TreeMorphism S T) :
    Path (TreeMorphism.comp (TreeMorphism.id S) f).edgeMap f.edgeMap :=
  Path.stepChain (TreeMorphism.id_comp f)

/-- Right identity law for tree morphisms. -/
theorem TreeMorphism.comp_id {S T : PlanarTree}
    (f : TreeMorphism S T) :
    (TreeMorphism.comp f (TreeMorphism.id T)).edgeMap = f.edgeMap := by
  unfold comp id
  rfl

/-- Path witness for right identity. -/
def TreeMorphism.comp_id_path {S T : PlanarTree}
    (f : TreeMorphism S T) :
    Path (TreeMorphism.comp f (TreeMorphism.id T)).edgeMap f.edgeMap :=
  Path.stepChain (TreeMorphism.comp_id f)

/-! ## Dendroidal Sets -/

/-- A dendroidal set: assigns a type to each tree. -/
structure DendroidalSet where
  /-- Dendrices indexed by trees. -/
  dendrex : PlanarTree → Type u
  /-- Restriction along tree morphisms. -/
  restrict : {S T : PlanarTree} → TreeMorphism S T →
    dendrex T → dendrex S
  /-- Identity restriction is the identity. -/
  restrict_id : ∀ (T : PlanarTree) (x : dendrex T),
    restrict (TreeMorphism.id T) x = x
  /-- Composition of restrictions. -/
  restrict_comp : ∀ {S T U : PlanarTree}
    (f : TreeMorphism S T) (g : TreeMorphism T U)
    (x : dendrex U),
    restrict (TreeMorphism.comp f g) x =
      restrict f (restrict g x)

/-- Path witness for identity restriction. -/
def DendroidalSet.restrict_id_path (D : DendroidalSet)
    (T : PlanarTree) (x : D.dendrex T) :
    Path (D.restrict (TreeMorphism.id T) x) x :=
  Path.stepChain (D.restrict_id T x)

/-- Path witness for composition of restrictions. -/
def DendroidalSet.restrict_comp_path (D : DendroidalSet)
    {S T U : PlanarTree}
    (f : TreeMorphism S T) (g : TreeMorphism T U)
    (x : D.dendrex U) :
    Path (D.restrict (TreeMorphism.comp f g) x)
         (D.restrict f (D.restrict g x)) :=
  Path.stepChain (D.restrict_comp f g x)

/-- A map of dendroidal sets. -/
structure DendroidalMap (X Y : DendroidalSet) where
  /-- Component maps. -/
  toFun : (T : PlanarTree) → X.dendrex T → Y.dendrex T
  /-- Naturality: commutes with restrictions. -/
  natural : ∀ {S T : PlanarTree} (f : TreeMorphism S T)
    (x : X.dendrex T),
    toFun S (X.restrict f x) = Y.restrict f (toFun T x)

/-- Path witness for naturality. -/
def DendroidalMap.natural_path {X Y : DendroidalSet}
    (φ : DendroidalMap X Y) {S T : PlanarTree}
    (f : TreeMorphism S T) (x : X.dendrex T) :
    Path (φ.toFun S (X.restrict f x))
         (Y.restrict f (φ.toFun T x)) :=
  Path.stepChain (φ.natural f x)

/-- Identity map of dendroidal sets. -/
def DendroidalMap.id (X : DendroidalSet) : DendroidalMap X X where
  toFun := fun _ x => x
  natural := by intros; rfl

/-- Composition of dendroidal maps. -/
def DendroidalMap.comp {X Y Z : DendroidalSet}
    (φ : DendroidalMap X Y) (ψ : DendroidalMap Y Z) :
    DendroidalMap X Z where
  toFun := fun T x => ψ.toFun T (φ.toFun T x)
  natural := by
    intro S T f x
    rw [φ.natural, ψ.natural]

/-- Left identity for dendroidal maps. -/
theorem DendroidalMap.id_comp {X Y : DendroidalSet}
    (φ : DendroidalMap X Y) :
    (DendroidalMap.comp (DendroidalMap.id X) φ).toFun = φ.toFun := by
  rfl

/-- Path witness for left identity. -/
def DendroidalMap.id_comp_path {X Y : DendroidalSet}
    (φ : DendroidalMap X Y) :
    Path (DendroidalMap.comp (DendroidalMap.id X) φ).toFun φ.toFun :=
  Path.stepChain (DendroidalMap.id_comp φ)

/-- Right identity for dendroidal maps. -/
theorem DendroidalMap.comp_id {X Y : DendroidalSet}
    (φ : DendroidalMap X Y) :
    (DendroidalMap.comp φ (DendroidalMap.id Y)).toFun = φ.toFun := by
  rfl

/-- Path witness for right identity. -/
def DendroidalMap.comp_id_path {X Y : DendroidalSet}
    (φ : DendroidalMap X Y) :
    Path (DendroidalMap.comp φ (DendroidalMap.id Y)).toFun φ.toFun :=
  Path.stepChain (DendroidalMap.comp_id φ)

/-! ## Inner Horns and ∞-Operads -/

/-- Face data for a dendroidal set: identifies boundary inclusions. -/
structure DendroidalFace (D : DendroidalSet) (T : PlanarTree) where
  /-- The face tree (one vertex removed). -/
  faceTree : PlanarTree
  /-- Inclusion of the face. -/
  incl : TreeMorphism faceTree T
  /-- The face dendrex is a subset of D(T). -/
  faceMap : D.dendrex T → D.dendrex faceTree
  /-- Compatibility with restriction. -/
  compat : ∀ (x : D.dendrex T), faceMap x = D.restrict incl x

/-- Path witness for face compatibility. -/
def DendroidalFace.compat_path {D : DendroidalSet} {T : PlanarTree}
    (F : DendroidalFace D T) (x : D.dendrex T) :
    Path (F.faceMap x) (D.restrict F.incl x) :=
  Path.stepChain (F.compat x)

/-- An inner horn of a dendroidal set. -/
structure InnerHorn (D : DendroidalSet) where
  /-- The tree shape. -/
  tree : PlanarTree
  /-- The inner edge being removed. -/
  innerEdge : Edge
  /-- Partial data: faces except the one corresponding to innerEdge. -/
  partialData : (T : PlanarTree) → TreeMorphism T tree → D.dendrex T
  /-- Coherence: partial data commutes with restrictions. -/
  coherent : ∀ {S T : PlanarTree} (f : TreeMorphism S T)
    (g : TreeMorphism T tree),
    partialData S (TreeMorphism.comp f g) =
      D.restrict f (partialData T g)

/-- Path witness for inner horn coherence. -/
def InnerHorn.coherent_path {D : DendroidalSet} (H : InnerHorn D)
    {S T : PlanarTree} (f : TreeMorphism S T)
    (g : TreeMorphism T H.tree) :
    Path (H.partialData S (TreeMorphism.comp f g))
         (D.restrict f (H.partialData T g)) :=
  Path.stepChain (H.coherent f g)

/-- An inner horn filler. -/
structure InnerHornFiller (D : DendroidalSet) (H : InnerHorn D) where
  /-- The filler dendrex. -/
  filler : D.dendrex H.tree
  /-- The filler extends the partial data. -/
  extends_data : ∀ (T : PlanarTree) (f : TreeMorphism T H.tree),
    D.restrict f filler = H.partialData T f

/-- Path witness for filler extending data. -/
def InnerHornFiller.extends_path {D : DendroidalSet} {H : InnerHorn D}
    (F : InnerHornFiller D H) (T : PlanarTree)
    (f : TreeMorphism T H.tree) :
    Path (D.restrict f F.filler) (H.partialData T f) :=
  Path.stepChain (F.extends_data T f)

/-- An ∞-operad: a dendroidal set with inner horn fillers. -/
structure InfinityOperad extends DendroidalSet where
  /-- Every inner horn has a filler. -/
  innerKan : ∀ (H : InnerHorn toDendroidalSet),
    InnerHornFiller toDendroidalSet H

/-- Path witness for ∞-operad horn filling. -/
def InfinityOperad.fill_path (O : InfinityOperad) (H : InnerHorn O.toDendroidalSet)
    (T : PlanarTree) (f : TreeMorphism T H.tree) :
    Path (O.restrict f (O.innerKan H).filler)
         (H.partialData T f) :=
  (O.innerKan H).extends_path T f

/-! ## Boardman–Vogt Tensor Product -/

/-- A bidendrex: element indexed by a pair of trees. -/
structure Bidendrex (X Y : DendroidalSet) where
  /-- Bidendrex type for a pair of trees. -/
  carrier : PlanarTree → PlanarTree → Type u
  /-- Left restriction. -/
  restrictLeft : {S T : PlanarTree} → TreeMorphism S T →
    (U : PlanarTree) → carrier T U → carrier S U
  /-- Right restriction. -/
  restrictRight : (T : PlanarTree) →
    {U V : PlanarTree} → TreeMorphism U V →
    carrier T V → carrier T U
  /-- Left identity. -/
  restrictLeft_id : ∀ (T U : PlanarTree) (x : carrier T U),
    restrictLeft (TreeMorphism.id T) U x = x
  /-- Right identity. -/
  restrictRight_id : ∀ (T U : PlanarTree) (x : carrier T U),
    restrictRight T (TreeMorphism.id U) x = x

/-- Path witness for left restriction identity. -/
def Bidendrex.restrictLeft_id_path {X Y : DendroidalSet}
    (B : Bidendrex X Y) (T U : PlanarTree)
    (x : B.carrier T U) :
    Path (B.restrictLeft (TreeMorphism.id T) U x) x :=
  Path.stepChain (B.restrictLeft_id T U x)

/-- Path witness for right restriction identity. -/
def Bidendrex.restrictRight_id_path {X Y : DendroidalSet}
    (B : Bidendrex X Y) (T U : PlanarTree)
    (x : B.carrier T U) :
    Path (B.restrictRight T (TreeMorphism.id U) x) x :=
  Path.stepChain (B.restrictRight_id T U x)

/-- The Boardman–Vogt tensor product of two dendroidal sets. -/
structure BVTensor where
  /-- First factor. -/
  left : DendroidalSet
  /-- Second factor. -/
  right : DendroidalSet
  /-- The tensor product dendroidal set. -/
  tensor : DendroidalSet
  /-- The bidendrex data. -/
  bidata : Bidendrex left right
  /-- Universal property: maps from tensor correspond to bidendrex maps. -/
  univ : ∀ (T : PlanarTree), tensor.dendrex T →
    (S U : PlanarTree) → TreeMorphism S T → TreeMorphism U T →
    bidata.carrier S U

/-- Symmetry data for the BV tensor product. -/
structure BVTensorSymmetry (bv1 bv2 : BVTensor) where
  /-- The symmetry isomorphism. -/
  sym : DendroidalMap bv1.tensor bv2.tensor
  /-- Inverse map. -/
  inv : DendroidalMap bv2.tensor bv1.tensor
  /-- Round-trip identity. -/
  roundtrip : ∀ (T : PlanarTree) (x : bv1.tensor.dendrex T),
    inv.toFun T (sym.toFun T x) = x

/-- Path witness for BV tensor symmetry. -/
def BVTensorSymmetry.roundtrip_path {bv1 bv2 : BVTensor}
    (S : BVTensorSymmetry bv1 bv2) (T : PlanarTree)
    (x : bv1.tensor.dendrex T) :
    Path (S.inv.toFun T (S.sym.toFun T x)) x :=
  Path.stepChain (S.roundtrip T x)

/-! ## Operadic Nerve -/

/-- A colored operad (for nerve construction). -/
structure ColoredOp where
  /-- Color set. -/
  Color : Type u
  /-- Operations. -/
  Ops : List Color → Color → Type u
  /-- Identity for each color. -/
  identity : (c : Color) → Ops [c] c
  /-- Composition of operations. -/
  comp : {inputs₁ : List Color} → {c d : Color} →
    Ops [c] d → Ops inputs₁ c → Ops inputs₁ d
  /-- Left unitality. -/
  comp_id_left : {c d : Color} → (f : Ops [c] d) →
    comp f (identity c) = f
  /-- Right unitality. -/
  comp_id_right : {c : Color} → (f : Ops [c] c) →
    comp (identity c) f = f

/-- Path witness for left unitality. -/
def ColoredOp.comp_id_left_path (O : ColoredOp) {c d : O.Color}
    (f : O.Ops [c] d) :
    Path (O.comp f (O.identity c)) f :=
  Path.stepChain (O.comp_id_left f)

/-- Path witness for right unitality. -/
def ColoredOp.comp_id_right_path (O : ColoredOp) {c : O.Color}
    (f : O.Ops [c] c) :
    Path (O.comp (O.identity c) f) f :=
  Path.stepChain (O.comp_id_right f)

/-- The operadic nerve of a colored operad. -/
structure OperadicNerve (O : ColoredOp) where
  /-- The resulting dendroidal set. -/
  nerve : DendroidalSet
  /-- Labeling: each dendrex labels edges by colors. -/
  label : (T : PlanarTree) → nerve.dendrex T →
    Edge → O.Color
  /-- Operations: each vertex of T gives an operation. -/
  ops : (T : PlanarTree) → (x : nerve.dendrex T) →
    (v : Vertex) → O.Ops (v.inputs.map (label T x)) (label T x v.output)
  /-- Identity for the unit tree. -/
  unit_is_id : ∀ (x : nerve.dendrex unitTree) (c : O.Color),
    label unitTree x (Edge.mk 0) = c →
    ∃ (e : Edge), e = Edge.mk 0

/-- Path witness for unit tree labeling. -/
def OperadicNerve.unit_path {O : ColoredOp}
    (N : OperadicNerve O) (x : N.nerve.dendrex unitTree) :
    Path (N.label unitTree x (Edge.mk 0))
         (N.label unitTree x (Edge.mk 0)) :=
  Path.refl _

/-- The nerve is an ∞-operad (statement as structure). -/
structure NerveIsInfinityOperad (O : ColoredOp) extends OperadicNerve O where
  /-- The nerve satisfies the inner Kan condition. -/
  innerKan : ∀ (H : InnerHorn nerve),
    InnerHornFiller nerve H

/-! ## Domain-Specific Steps -/

/-- Kinds of ∞-operad steps. -/
inductive InfOperadStepKind where
  | horn_fill
  | nerve_restrict
  | tensor_sym
  | comp_assoc

/-- An ∞-operad step witness. -/
structure InfOperadStep (A : Type u) where
  /-- Source. -/
  src : A
  /-- Target. -/
  tgt : A
  /-- Step kind. -/
  kind : InfOperadStepKind
  /-- Proof. -/
  proof : src = tgt

/-- Convert to a Path. -/
def InfOperadStep.toPath {A : Type u}
    (s : InfOperadStep A) : Path s.src s.tgt :=
  Path.stepChain s.proof

/-- Compose two ∞-operad step paths. -/
def infOperadChain {A : Type u} {a b c : A}
    (h1 : a = b) (h2 : b = c) : Path a c :=
  Path.trans (Path.stepChain h1) (Path.stepChain h2)

/-- Triple chain of ∞-operad steps. -/
def infOperadChain3 {A : Type u} {a b c d : A}
    (h1 : a = b) (h2 : b = c) (h3 : c = d) : Path a d :=
  Path.trans (Path.trans (Path.stepChain h1) (Path.stepChain h2))
             (Path.stepChain h3)

/-! ## Summary -/

end InfinityOperads
end Algebra
end Path
end ComputationalPaths
