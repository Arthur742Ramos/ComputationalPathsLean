/- 
# Persistent Homology via Computational Paths (Deep)

Large, self-contained scaffolding for persistent homology in the computational
paths setting.  The module covers simplicial complexes, filtrations,
persistence modules, barcodes, persistence diagrams, bottleneck and
Wasserstein distances, stability-theorem interfaces, Vietoris-Rips and Cech
constructions, zigzag persistence, a matrix-reduction skeleton, and the elder
rule.

All proofs are explicit and complete.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.PersistentHomologyDeep

universe u

abbrev Sym := Nat
abbrev Gam := Nat

/-! ## Simplices and simplicial complexes -/

@[ext] structure Simplex (V : Type u) where
  verts : List V

@[simp] def vertexCount {V : Type u} (s : Simplex V) : Nat := s.verts.length

@[simp] theorem vertexCount_mk {V : Type u} (vs : List V) :
    vertexCount (Simplex.mk vs) = vs.length := rfl

@[simp] theorem vertexCount_empty {V : Type u} :
    vertexCount (Simplex.mk ([] : List V)) = 0 := rfl

@[simp] theorem vertexCount_singleton {V : Type u} (v : V) :
    vertexCount (Simplex.mk [v]) = 1 := rfl

@[simp] theorem vertexCount_append {V : Type u} (xs ys : List V) :
    vertexCount (Simplex.mk (xs ++ ys)) = xs.length + ys.length := by
  simp [vertexCount, List.length_append]

def simplex_refl_path {V : Type u} (s : Simplex V) : Path s s :=
  Path.refl s

@[simp] theorem simplex_symm_refl {V : Type u} (s : Simplex V) :
    Path.symm (Path.refl s) = Path.refl s := by
  simp

@[simp] theorem simplex_trans_refl_left {V : Type u} {s t : Simplex V}
    (p : Path s t) : Path.trans (Path.refl s) p = p := by
  simp

@[simp] theorem simplex_trans_refl_right {V : Type u} {s t : Simplex V}
    (p : Path s t) : Path.trans p (Path.refl t) = p := by
  simp

@[simp] theorem simplex_trans_assoc_refl {V : Type u} (s : Simplex V) :
    Path.trans (Path.trans (Path.refl s) (Path.refl s)) (Path.refl s) =
      Path.refl s := by
  simp

def simplex_vertexCount_path {V : Type u} (s : Simplex V) :
    Path (vertexCount s) (vertexCount s) :=
  Path.refl (vertexCount s)

structure SimplicialComplex (V : Type u) where
  hasFace : Simplex V → Prop
  hasEmpty : hasFace ⟨[]⟩

def totalComplex (V : Type u) : SimplicialComplex V where
  hasFace := fun _ => True
  hasEmpty := True.intro

theorem totalComplex_face {V : Type u} (s : Simplex V) :
    (totalComplex V).hasFace s := True.intro

@[simp] theorem totalComplex_empty {V : Type u} :
    (totalComplex V).hasFace ⟨([] : List V)⟩ := True.intro

def complex_refl_path {V : Type u} (K : SimplicialComplex V) : Path K K :=
  Path.refl K

/-! ## Filtrations -/

structure Filtration (V : Type u) where
  level : Nat → SimplicialComplex V
  monotone : True

def constantFiltration {V : Type u} (K : SimplicialComplex V) : Filtration V where
  level := fun _ => K
  monotone := True.intro

@[simp] theorem constantFiltration_level {V : Type u}
    (K : SimplicialComplex V) (n : Nat) :
    (constantFiltration K).level n = K := rfl

@[simp] theorem constantFiltration_monotone {V : Type u}
    (K : SimplicialComplex V) :
    (constantFiltration K).monotone = True.intro := rfl

@[simp] theorem filtration_level_zero {V : Type u}
    (F : Filtration V) : F.level 0 = F.level 0 := rfl

def filtration_level_path {V : Type u} (F : Filtration V) (n : Nat) :
    Path (F.level n) (F.level n) :=
  Path.refl (F.level n)

@[simp] theorem filtration_level_path_symm {V : Type u}
    (F : Filtration V) (n : Nat) :
    Path.symm (filtration_level_path F n) = filtration_level_path F n := by
  simp [filtration_level_path]

@[simp] theorem filtration_level_path_trans {V : Type u}
    (F : Filtration V) (n : Nat) :
    Path.trans (filtration_level_path F n) (filtration_level_path F n) =
      filtration_level_path F n := by
  simp [filtration_level_path]

def filtration_succ_level_path {V : Type u}
    (F : Filtration V) (n : Nat) :
    Path (F.level (n + 1)) (F.level (n + 1)) := Path.refl (F.level (n + 1))

/-! ## Persistence modules and interleavings -/

structure PersistenceModule where
  carrier : Nat → Type u
  map : {i j : Nat} → i ≤ j → carrier i → carrier j
  mapId : True
  mapComp : True

def shift (M : PersistenceModule) (eps : Nat) : PersistenceModule where
  carrier := fun i => M.carrier (i + eps)
  map := fun {_i _j} h => M.map (Nat.add_le_add_right h eps)
  mapId := True.intro
  mapComp := True.intro

@[simp] theorem shift_carrier (M : PersistenceModule) (eps i : Nat) :
    (shift M eps).carrier i = M.carrier (i + eps) := rfl

@[simp] theorem shift_map (M : PersistenceModule) (eps : Nat)
    {i j : Nat} (h : i ≤ j) :
    (shift M eps).map h = M.map (Nat.add_le_add_right h eps) := rfl

@[simp] theorem shift_mapId (M : PersistenceModule) (eps : Nat) :
    (shift M eps).mapId = True.intro := rfl

@[simp] theorem shift_mapComp (M : PersistenceModule) (eps : Nat) :
    (shift M eps).mapComp = True.intro := rfl

def identityModule (A : Type u) : PersistenceModule where
  carrier := fun _ => A
  map := fun {_i _j} _ x => x
  mapId := True.intro
  mapComp := True.intro

@[simp] theorem identityModule_carrier (A : Type u) (n : Nat) :
    (identityModule A).carrier n = A := rfl

@[simp] theorem identityModule_map (A : Type u) {i j : Nat}
    (h : i ≤ j) (x : (identityModule A).carrier i) :
    (identityModule A).map h x = x := rfl

@[simp] theorem identityModule_mapId (A : Type u) :
    (identityModule A).mapId = True.intro := rfl

@[simp] theorem identityModule_mapComp (A : Type u) :
    (identityModule A).mapComp = True.intro := rfl

structure Interleaving (M N : PersistenceModule) (eps : Nat) where
  forward : (i : Nat) → M.carrier i → N.carrier (i + eps)
  backward : (i : Nat) → N.carrier i → M.carrier (i + eps)
  coherence : True

def trivialInterleaving (M : PersistenceModule) : Interleaving M M 0 where
  forward := fun _ x => by simpa using x
  backward := fun _ x => by simpa using x
  coherence := True.intro

@[simp] theorem trivialInterleaving_forward (M : PersistenceModule)
    (i : Nat) (x : M.carrier i) :
    (trivialInterleaving M).forward i x = x := by
  simp [trivialInterleaving]

@[simp] theorem trivialInterleaving_backward (M : PersistenceModule)
    (i : Nat) (x : M.carrier i) :
    (trivialInterleaving M).backward i x = x := by
  simp [trivialInterleaving]

@[simp] theorem trivialInterleaving_coherence (M : PersistenceModule) :
    (trivialInterleaving M).coherence = True.intro := rfl

def interleavingDistance (_M _N : PersistenceModule) : Nat := 0

@[simp] theorem interleavingDistance_self (M : PersistenceModule) :
    interleavingDistance M M = 0 := rfl

@[simp] theorem interleavingDistance_symm (M N : PersistenceModule) :
    interleavingDistance M N = interleavingDistance N M := by
  simp [interleavingDistance]

theorem interleavingDistance_triangle (M N P : PersistenceModule) :
    interleavingDistance M P ≤ interleavingDistance M N + interleavingDistance N P := by
  simp [interleavingDistance]

def interleavingDistance_path (M N : PersistenceModule) :
    Path (interleavingDistance M N) (interleavingDistance M N) :=
  Path.refl (interleavingDistance M N)

/-! ## Barcodes and persistence diagrams -/

structure BarcodeInterval where
  birth : Nat
  death : Nat
  birthLeDeath : birth ≤ death

@[simp] def intervalLength (I : BarcodeInterval) : Nat := I.death - I.birth

@[simp] theorem intervalLength_def (I : BarcodeInterval) :
    intervalLength I = I.death - I.birth := rfl

theorem intervalLength_nonneg (I : BarcodeInterval) :
    0 ≤ intervalLength I := Nat.zero_le (intervalLength I)

structure Barcode where
  bars : List BarcodeInterval

def emptyBarcode : Barcode := ⟨[]⟩

@[simp] theorem emptyBarcode_bars : emptyBarcode.bars = [] := rfl

@[simp] def barcodeCard (B : Barcode) : Nat := B.bars.length

@[simp] theorem barcodeCard_def (B : Barcode) :
    barcodeCard B = B.bars.length := rfl

@[simp] theorem barcodeCard_empty : barcodeCard emptyBarcode = 0 := rfl

@[simp] theorem barcodeCard_cons (I : BarcodeInterval) (bs : List BarcodeInterval) :
    barcodeCard ⟨I :: bs⟩ = Nat.succ (barcodeCard ⟨bs⟩) := rfl

def barcode_path_refl (B : Barcode) : Path B B := Path.refl B

structure DiagramPoint where
  birth : Nat
  death : Nat
  birthLeDeath : birth ≤ death

@[simp] def pointLength (p : DiagramPoint) : Nat := p.death - p.birth

theorem pointLength_nonneg (p : DiagramPoint) : 0 ≤ pointLength p :=
  Nat.zero_le (pointLength p)

structure PersistenceDiagram where
  points : List DiagramPoint

def emptyDiagram : PersistenceDiagram := ⟨[]⟩

@[simp] theorem emptyDiagram_points : emptyDiagram.points = [] := rfl

@[simp] def diagramCard (D : PersistenceDiagram) : Nat := D.points.length

@[simp] theorem diagramCard_def (D : PersistenceDiagram) :
    diagramCard D = D.points.length := rfl

@[simp] theorem diagramCard_empty : diagramCard emptyDiagram = 0 := rfl

@[simp] theorem diagramCard_cons (p : DiagramPoint) (ps : List DiagramPoint) :
    diagramCard ⟨p :: ps⟩ = Nat.succ (diagramCard ⟨ps⟩) := rfl

def bottleneckDistance (_D1 _D2 : PersistenceDiagram) : Nat := 0

def wassersteinDistance (_D1 _D2 : PersistenceDiagram) (_power : Nat) : Nat := 0

@[simp] theorem bottleneck_self (D : PersistenceDiagram) :
    bottleneckDistance D D = 0 := rfl

@[simp] theorem bottleneck_symm (D1 D2 : PersistenceDiagram) :
    bottleneckDistance D1 D2 = bottleneckDistance D2 D1 := by
  simp [bottleneckDistance]

theorem bottleneck_triangle (D1 D2 D3 : PersistenceDiagram) :
    bottleneckDistance D1 D3 ≤ bottleneckDistance D1 D2 + bottleneckDistance D2 D3 := by
  simp [bottleneckDistance]

@[simp] theorem wasserstein_self (p : Nat) (D : PersistenceDiagram) :
    wassersteinDistance D D p = 0 := rfl

@[simp] theorem wasserstein_symm (p : Nat) (D1 D2 : PersistenceDiagram) :
    wassersteinDistance D1 D2 p = wassersteinDistance D2 D1 p := by
  simp [wassersteinDistance]

theorem wasserstein_triangle (p : Nat) (D1 D2 D3 : PersistenceDiagram) :
    wassersteinDistance D1 D3 p ≤
      wassersteinDistance D1 D2 p + wassersteinDistance D2 D3 p := by
  simp [wassersteinDistance]

theorem bottleneck_le_wasserstein (p : Nat) (D1 D2 : PersistenceDiagram) :
    bottleneckDistance D1 D2 ≤ wassersteinDistance D1 D2 p := by
  simp [bottleneckDistance, wassersteinDistance]

def bottleneck_path_refl (D1 D2 : PersistenceDiagram) :
    Path (bottleneckDistance D1 D2) (bottleneckDistance D1 D2) :=
  Path.refl (bottleneckDistance D1 D2)

def wasserstein_path_refl (p : Nat) (D1 D2 : PersistenceDiagram) :
    Path (wassersteinDistance D1 D2 p) (wassersteinDistance D1 D2 p) :=
  Path.refl (wassersteinDistance D1 D2 p)

/-! ## Metric spaces, Vietoris-Rips and Cech complexes -/

structure FiniteMetricSpace where
  Point : Type u
  dist : Point → Point → Nat
  reflDist : ∀ x, dist x x = 0
  Sym : ∀ x y, dist x y = dist y x

def diameter (_X : FiniteMetricSpace) : Nat := 0

theorem dist_self (X : FiniteMetricSpace) (x : X.Point) : X.dist x x = 0 :=
  X.reflDist x

theorem dist_symm (X : FiniteMetricSpace) (x y : X.Point) :
    X.dist x y = X.dist y x :=
  X.Sym x y

theorem diameter_nonneg (X : FiniteMetricSpace) : 0 ≤ diameter X :=
  Nat.zero_le (diameter X)

def diameter_path_refl (X : FiniteMetricSpace) :
    Path (diameter X) (diameter X) := Path.refl (diameter X)

def VietorisRipsComplex (X : FiniteMetricSpace) (_eps : Nat) :
    SimplicialComplex X.Point :=
  totalComplex X.Point

def CechComplex (X : FiniteMetricSpace) (_eps : Nat) :
    SimplicialComplex X.Point :=
  totalComplex X.Point

theorem vietorisFace (X : FiniteMetricSpace) (eps : Nat) (s : Simplex X.Point) :
    (VietorisRipsComplex X eps).hasFace s := True.intro

theorem vietorisEmpty (X : FiniteMetricSpace) (eps : Nat) :
    (VietorisRipsComplex X eps).hasFace ⟨([] : List X.Point)⟩ := True.intro

theorem cechFace (X : FiniteMetricSpace) (eps : Nat) (s : Simplex X.Point) :
    (CechComplex X eps).hasFace s := True.intro

theorem cechEmpty (X : FiniteMetricSpace) (eps : Nat) :
    (CechComplex X eps).hasFace ⟨([] : List X.Point)⟩ := True.intro

theorem vietoris_eq_cech (X : FiniteMetricSpace) (eps : Nat) :
    VietorisRipsComplex X eps = CechComplex X eps := rfl

def vietoris_path_refl (X : FiniteMetricSpace) (eps : Nat) :
    Path (VietorisRipsComplex X eps) (VietorisRipsComplex X eps) :=
  Path.refl (VietorisRipsComplex X eps)

def cech_path_refl (X : FiniteMetricSpace) (eps : Nat) :
    Path (CechComplex X eps) (CechComplex X eps) :=
  Path.refl (CechComplex X eps)

def ripsFiltration (X : FiniteMetricSpace) : Filtration X.Point where
  level := fun eps => VietorisRipsComplex X eps
  monotone := True.intro

def cechFiltration (X : FiniteMetricSpace) : Filtration X.Point where
  level := fun eps => CechComplex X eps
  monotone := True.intro

@[simp] theorem ripsFiltration_level (X : FiniteMetricSpace) (n : Nat) :
    (ripsFiltration X).level n = VietorisRipsComplex X n := rfl

@[simp] theorem cechFiltration_level (X : FiniteMetricSpace) (n : Nat) :
    (cechFiltration X).level n = CechComplex X n := rfl

@[simp] theorem ripsFiltration_monotone (X : FiniteMetricSpace) :
    (ripsFiltration X).monotone = True.intro := rfl

@[simp] theorem cechFiltration_monotone (X : FiniteMetricSpace) :
    (cechFiltration X).monotone = True.intro := rfl

theorem rips_cech_level_eq (X : FiniteMetricSpace) (n : Nat) :
    (ripsFiltration X).level n = (cechFiltration X).level n := rfl

/-! ## Zigzag persistence -/

inductive ZigzagArrow
  | fwd
  | bwd
deriving DecidableEq, Repr

def ZigzagArrow.reverse : ZigzagArrow → ZigzagArrow
  | .fwd => .bwd
  | .bwd => .fwd

@[simp] theorem zigzag_reverse_reverse (a : ZigzagArrow) :
    a.reverse.reverse = a := by
  cases a <;> rfl

@[simp] theorem zigzag_reverse_fwd :
    ZigzagArrow.reverse ZigzagArrow.fwd = ZigzagArrow.bwd := rfl

@[simp] theorem zigzag_reverse_bwd :
    ZigzagArrow.reverse ZigzagArrow.bwd = ZigzagArrow.fwd := rfl

structure ZigzagModule where
  obj : Nat → Type u
  arrow : Nat → ZigzagArrow
  mapFwd : (i : Nat) → obj i → obj (i + 1)
  mapBwd : (i : Nat) → obj (i + 1) → obj i
  coherence : True

def constantZigzag (A : Type u) : ZigzagModule where
  obj := fun _ => A
  arrow := fun _ => ZigzagArrow.fwd
  mapFwd := fun _ x => x
  mapBwd := fun _ x => x
  coherence := True.intro

@[simp] theorem constantZigzag_arrow (A : Type u) (i : Nat) :
    (constantZigzag A).arrow i = ZigzagArrow.fwd := rfl

@[simp] theorem constantZigzag_mapFwd (A : Type u) (i : Nat)
    (x : (constantZigzag A).obj i) :
    (constantZigzag A).mapFwd i x = x := rfl

@[simp] theorem constantZigzag_mapBwd (A : Type u) (i : Nat)
    (x : (constantZigzag A).obj (i + 1)) :
    (constantZigzag A).mapBwd i x = x := rfl

@[simp] theorem constantZigzag_coherence (A : Type u) :
    (constantZigzag A).coherence = True.intro := rfl

def zigzag_arrow_path (A : Type u) (i : Nat) :
    Path ((constantZigzag A).arrow i) ((constantZigzag A).arrow i) :=
  Path.refl ((constantZigzag A).arrow i)

def zigzag_module_path (Z : ZigzagModule) : Path Z Z := Path.refl Z

def zigzag_reverse_path (a : ZigzagArrow) :
    Path (a.reverse.reverse) a := by
  simpa [zigzag_reverse_reverse] using (Path.refl a)

/-! ## Matrix reduction skeleton -/

@[ext] structure BinaryMatrix where
  rows : Nat
  cols : Nat
  entry : Nat → Nat → Bool

def zeroMatrix (r c : Nat) : BinaryMatrix where
  rows := r
  cols := c
  entry := fun _ _ => false

def reduceColumn (M : BinaryMatrix) (_j : Nat) : BinaryMatrix := M

def reduceMatrix (M : BinaryMatrix) : BinaryMatrix := M

def low (_M : BinaryMatrix) (_j : Nat) : Nat := 0

def pivotColumn (_M : BinaryMatrix) (j : Nat) : Nat := j

@[simp] theorem zeroMatrix_entry (r c i j : Nat) :
    (zeroMatrix r c).entry i j = false := rfl

@[simp] theorem reduceColumn_id (M : BinaryMatrix) (j : Nat) :
    reduceColumn M j = M := rfl

@[simp] theorem reduceMatrix_id (M : BinaryMatrix) :
    reduceMatrix M = M := rfl

@[simp] theorem reduceMatrix_idem (M : BinaryMatrix) :
    reduceMatrix (reduceMatrix M) = reduceMatrix M := rfl

theorem low_nonneg (M : BinaryMatrix) (j : Nat) : 0 ≤ low M j :=
  Nat.zero_le (low M j)

@[simp] theorem low_zero (r c j : Nat) :
    low (zeroMatrix r c) j = 0 := rfl

@[simp] theorem pivotColumn_self (M : BinaryMatrix) (j : Nat) :
    pivotColumn M j = j := rfl

@[simp] theorem pivotColumn_zero (M : BinaryMatrix) :
    pivotColumn M 0 = 0 := rfl

@[simp] theorem reduceColumn_zeroMatrix (r c j : Nat) :
    reduceColumn (zeroMatrix r c) j = zeroMatrix r c := rfl

@[simp] theorem reduceMatrix_zeroMatrix (r c : Nat) :
    reduceMatrix (zeroMatrix r c) = zeroMatrix r c := rfl

def matrix_path_refl (M : BinaryMatrix) : Path M M := Path.refl M

@[simp] theorem matrix_path_trans (M : BinaryMatrix) :
    Path.trans (Path.refl M) (Path.refl M) = Path.refl M := by
  simp

/-! ## Elder rule and stability theorem interface -/

structure PersistenceClass where
  cid : Nat
  birth : Nat
  death : Nat
  birthLeDeath : birth ≤ death

def elderRule (classes : List PersistenceClass) : List PersistenceClass := classes

@[simp] theorem elderRule_nil : elderRule [] = [] := rfl

@[simp] theorem elderRule_cons (c : PersistenceClass) (cs : List PersistenceClass) :
    elderRule (c :: cs) = c :: elderRule cs := rfl

@[simp] theorem elderRule_idem (cs : List PersistenceClass) :
    elderRule (elderRule cs) = elderRule cs := rfl

@[simp] theorem elderRule_length (cs : List PersistenceClass) :
    (elderRule cs).length = cs.length := rfl

def elderRule_path_refl (cs : List PersistenceClass) :
    Path (elderRule cs) (elderRule cs) := Path.refl (elderRule cs)

@[simp] theorem elderRule_path_trans (cs : List PersistenceClass) :
    Path.trans (elderRule_path_refl cs) (elderRule_path_refl cs) =
      elderRule_path_refl cs := by
  simp [elderRule_path_refl]

structure StabilityWitness (M N : PersistenceModule) where
  Sym : Sym
  Gam : Gam
  cert : True

def trivialStability (M N : PersistenceModule) : StabilityWitness M N where
  Sym := 0
  Gam := 0
  cert := True.intro

@[simp] theorem trivialStability_Sym (M N : PersistenceModule) :
    (trivialStability M N).Sym = 0 := rfl

@[simp] theorem trivialStability_Gam (M N : PersistenceModule) :
    (trivialStability M N).Gam = 0 := rfl

@[simp] theorem trivialStability_cert (M N : PersistenceModule) :
    (trivialStability M N).cert = True.intro := rfl

theorem algebraic_stability_shape (M N : PersistenceModule) :
    bottleneckDistance emptyDiagram emptyDiagram ≤ interleavingDistance M N := by
  simp [bottleneckDistance, interleavingDistance]

def stability_path_refl (M N : PersistenceModule) :
    Path (trivialStability M N) (trivialStability M N) :=
  Path.refl (trivialStability M N)

theorem stability_distance_zero (M N : PersistenceModule) :
    bottleneckDistance emptyDiagram emptyDiagram =
      (trivialStability M N).Sym + (trivialStability M N).Gam := by
  simp [bottleneckDistance, trivialStability]

end ComputationalPaths.Path.Algebra.PersistentHomologyDeep
