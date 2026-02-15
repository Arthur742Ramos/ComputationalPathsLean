import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ComputationalTopology

/-! ## Simplicial and persistent data -/

def Vertex : Type := Nat

def Simplex : Type := List Vertex

def SimplicialComplex : Type := List Simplex

def chainRank (K : SimplicialComplex) : Nat :=
  K.length

def boundaryMatrix (K : SimplicialComplex) : List (List Int) :=
  K.map (fun s => [Int.ofNat s.length])

def homologyRank (K : SimplicialComplex) (n : Nat) : Nat :=
  chainRank K - n

def filtration : Type := Nat → SimplicialComplex

def filtrationLevel (F : filtration) (i : Nat) : SimplicialComplex :=
  F i

def persistentPair : Type := Nat × Nat

def barcode : Type := List persistentPair

def persistenceFromFiltration (_F : filtration) (maxLevel : Nat) : barcode :=
  (List.range maxLevel).map (fun i => (i, i + 1))

/-! ## Complex constructions -/

def vietorisRips (pts : List (List Int)) (_ε : Nat) : SimplicialComplex :=
  (List.range pts.length).map (fun i => [i])

def cechComplex (pts : List (List Int)) (_ε : Nat) : SimplicialComplex :=
  (List.range pts.length).map (fun i => [i])

def alphaShape (pts : List (List Int)) (α : Nat) : SimplicialComplex :=
  vietorisRips pts α

def mapperCover (_values : List Int) (intervalCount : Nat) : List (Int × Int) :=
  (List.range intervalCount).map (fun i => (Int.ofNat i, Int.ofNat (i + 1)))

def mapperNodes (pts : List (List Int)) (_values : List Int) (intervalCount : Nat) :
    List (Nat × Nat) :=
  (List.range pts.length).map (fun i => (i, i % (intervalCount + 1)))

def mapperEdges (nodes : List (Nat × Nat)) : List (Nat × Nat) :=
  nodes.map (fun p => (p.1, p.1))

def mapperGraph (pts : List (List Int)) (values : List Int) (intervalCount : Nat) :
    List (Nat × Nat) × List (Nat × Nat) :=
  let ns := mapperNodes pts values intervalCount
  (ns, mapperEdges ns)

def reebVertices (values : List Int) : List (Nat × Int) :=
  (List.range values.length).map (fun i => (i, values.getD i 0))

def reebEdges (verts : List (Nat × Int)) : List (Nat × Nat) :=
  verts.map (fun v => (v.1, v.1))

def reebGraph (values : List Int) : List (Nat × Int) × List (Nat × Nat) :=
  let vs := reebVertices values
  (vs, reebEdges vs)

def eulerCharacteristic (K : SimplicialComplex) : Int :=
  Int.ofNat K.length

/-! ## Theorems (algorithmic contracts) -/

theorem chainRank_nonnegative (K : SimplicialComplex) :
    0 ≤ chainRank K := by
  sorry

theorem homologyRank_le_chainRank (K : SimplicialComplex) (n : Nat) :
    homologyRank K n ≤ chainRank K := by
  sorry

theorem boundaryMatrix_length (K : SimplicialComplex) :
    (boundaryMatrix K).length = K.length := by
  sorry

theorem filtrationLevel_def (F : filtration) (i : Nat) :
    filtrationLevel F i = F i := by
  sorry

theorem persistenceFromFiltration_length (F : filtration) (m : Nat) :
    (persistenceFromFiltration F m).length = m := by
  sorry

theorem vietorisRips_length (pts : List (List Int)) (ε : Nat) :
    (vietorisRips pts ε).length = pts.length := by
  sorry

theorem cechComplex_length (pts : List (List Int)) (ε : Nat) :
    (cechComplex pts ε).length = pts.length := by
  sorry

theorem alphaShape_eq_vietorisRips (pts : List (List Int)) (α : Nat) :
    alphaShape pts α = vietorisRips pts α := by
  sorry

theorem mapperCover_length (values : List Int) (intervalCount : Nat) :
    (mapperCover values intervalCount).length = intervalCount := by
  sorry

theorem mapperNodes_length (pts : List (List Int)) (values : List Int) (intervalCount : Nat) :
    (mapperNodes pts values intervalCount).length = pts.length := by
  sorry

theorem mapperEdges_length (nodes : List (Nat × Nat)) :
    (mapperEdges nodes).length = nodes.length := by
  sorry

theorem mapperGraph_nodes (pts : List (List Int)) (values : List Int) (intervalCount : Nat) :
    (mapperGraph pts values intervalCount).1 = mapperNodes pts values intervalCount := by
  sorry

theorem reebVertices_length (values : List Int) :
    (reebVertices values).length = values.length := by
  sorry

theorem reebEdges_length (verts : List (Nat × Int)) :
    (reebEdges verts).length = verts.length := by
  sorry

theorem reebGraph_vertices (values : List Int) :
    (reebGraph values).1 = reebVertices values := by
  sorry

theorem eulerCharacteristic_empty :
    eulerCharacteristic [] = 0 := by
  sorry

theorem homologyRank_zero (K : SimplicialComplex) :
    homologyRank K 0 = chainRank K := by
  sorry

theorem chainRank_path (K : SimplicialComplex) :
    Nonempty (Path (chainRank K) (chainRank K)) := by
  sorry

theorem mapperGraph_edge_self (pts : List (List Int)) (values : List Int) (intervalCount : Nat) :
    (mapperGraph pts values intervalCount).2 =
      mapperEdges (mapperNodes pts values intervalCount) := by
  sorry

theorem reebGraph_path (values : List Int) :
    Nonempty (Path (reebGraph values) (reebGraph values)) := by
  sorry

end ComputationalTopology
end Topology
end Path
end ComputationalPaths
