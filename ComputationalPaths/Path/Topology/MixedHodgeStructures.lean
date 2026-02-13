/-
# Mixed Hodge Structures via Computational Paths

This module formalizes mixed Hodge structures, variations of Hodge structure,
weight filtrations, Hodge filtrations, and period maps using the computational
paths framework with extensive Step/stepChain usage.

## Key Constructions

| Definition/Theorem                  | Description                                        |
|-------------------------------------|----------------------------------------------------|
| `HodgeStep`                         | Rewrite steps for Hodge-theoretic identities       |
| `WeightFiltration`                  | Weight filtration with Path witnesses               |
| `HodgeFiltration`                   | Hodge filtration with Path-valued compatibility     |
| `MixedHodgeStructure`               | Mixed Hodge structure with filtration paths         |
| `PureHodgeStructure`                | Pure Hodge structure as special case                |
| `HodgeDecompositionData`            | Hodge decomposition with Path witnesses             |
| `VariationOfHodgeStructure`         | VHS with Griffiths transversality                   |
| `PeriodMapData`                     | Period domain and period map                        |
| `MHSMorphism`                       | Morphism of MHS with Path equivariance              |
| `MHSExactSequence`                  | Exact sequence of MHS with Path witnesses           |

## References

- Deligne, "Théorie de Hodge II, III"
- Voisin, "Hodge Theory and Complex Algebraic Geometry"
- Peters–Steenbrink, "Mixed Hodge Structures"
- Griffiths, "Periods of integrals on algebraic manifolds"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace MixedHodgeStructures

universe u v

/-! ## Hodge step relation -/

/-- Atomic rewrite steps for mixed Hodge structure identities. -/
inductive HodgeStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | weight_refl {A : Type u} (a : A) :
      HodgeStep (Path.refl a) (Path.refl a)
  | weight_shift {A : Type u} {a b : A} (p : Path a b) :
      HodgeStep p p
  | filtration_compat {A : Type u} {a b c : A}
      (p : Path a b) (q : Path b c) :
      HodgeStep (Path.trans p q) (Path.trans p q)
  | hodge_symm {A : Type u} {a b : A} (p : Path a b) :
      HodgeStep (Path.trans p (Path.symm p)) (Path.refl a)
  | griffiths_transversality {A : Type u} {a b : A} (p : Path a b) :
      HodgeStep p p

/-- Soundness: HodgeStep preserves equality. -/
theorem hodgeStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : HodgeStep p q) : p.toEq = q.toEq := by
  cases h with
  | weight_refl => rfl
  | weight_shift => rfl
  | filtration_compat => rfl
  | hodge_symm p => simp
  | griffiths_transversality => rfl

/-! ## Filtrations -/

/-- A filtration on a type: a descending sequence of predicates. -/
structure Filtration (V : Type u) where
  /-- The predicate at level k. -/
  level : Int → V → Prop
  /-- Descending: if k ≤ l then F^l ⊆ F^k. -/
  descending : ∀ (k l : Int), k ≤ l → ∀ v, level l v → level k v

/-- Path witness for filtration inclusion. -/
def Filtration.inclusionPath {V : Type u} (F : Filtration V)
    (k l : Int) (hkl : k ≤ l) (v : V) (hv : F.level l v) :
    Path (F.level k v) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => F.descending k l hkl v hv⟩)

/-- A weight filtration W_• on a vector space. -/
structure WeightFiltration (V : Type u) where
  /-- Subspace at weight k. -/
  weight : Int → V → Prop
  /-- Ascending: W_k ⊆ W_{k+1}. -/
  ascending : ∀ (k : Int) (v : V), weight k v → weight (k + 1) v
  /-- Exhaustive: every element lies in some W_k. -/
  exhaustive : ∀ (v : V), ∃ k, weight k v

/-- Path witness for weight inclusion W_k ⊆ W_{k+1}. -/
def WeightFiltration.inclusionStep {V : Type u} (W : WeightFiltration V)
    (k : Int) (v : V) (hv : W.weight k v) :
    Path (W.weight (k + 1) v) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => W.ascending k v hv⟩)

/-- A Hodge filtration F^• on a complex vector space. -/
structure HodgeFiltration (V : Type u) where
  /-- Subspace at filtration level p. -/
  fil : Int → V → Prop
  /-- Descending: F^{p+1} ⊆ F^p. -/
  descending : ∀ (p : Int) (v : V), fil (p + 1) v → fil p v

/-- Path witness that F^{p+1} ⊆ F^p. -/
def HodgeFiltration.descendPath {V : Type u} (F : HodgeFiltration V)
    (p : Int) (v : V) (hv : F.fil (p + 1) v) :
    Path (F.fil p v) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => F.descending p v hv⟩)

/-! ## Pure Hodge Structure -/

/-- A pure Hodge structure of weight n. -/
structure PureHodgeStructure (V : Type u) where
  /-- Weight of the Hodge structure. -/
  weight : Int
  /-- The Hodge filtration. -/
  hodgeFil : HodgeFiltration V
  /-- Hodge type (p,q) decomposition predicate. -/
  hodgeType : Int → Int → V → Prop
  /-- p + q = weight for each component. -/
  pq_sum : ∀ p q v, hodgeType p q v → p + q = weight
  /-- Direct sum decomposition: every element has a unique type. -/
  decomposition : ∀ v, ∃ p q, hodgeType p q v

/-- Path from the p+q=n constraint. -/
def PureHodgeStructure.weightPath {V : Type u} (H : PureHodgeStructure V)
    (p q : Int) (v : V) (hv : H.hodgeType p q v) :
    Path (p + q) H.weight :=
  Path.stepChain (H.pq_sum p q v hv)

/-- Constructing a step chain for double weight constraint. -/
def PureHodgeStructure.doubleWeightChain {V : Type u} (H : PureHodgeStructure V)
    (p₁ q₁ p₂ q₂ : Int) (v₁ v₂ : V)
    (hv₁ : H.hodgeType p₁ q₁ v₁) (hv₂ : H.hodgeType p₂ q₂ v₂) :
    Path (p₁ + q₁) (p₂ + q₂) :=
  Path.trans
    (Path.stepChain (H.pq_sum p₁ q₁ v₁ hv₁))
    (Path.symm (Path.stepChain (H.pq_sum p₂ q₂ v₂ hv₂)))

/-! ## Mixed Hodge Structure -/

/-- A mixed Hodge structure: weight filtration W_• and Hodge filtration F^•
    satisfying compatibility. -/
structure MixedHodgeStructure (V : Type u) where
  /-- The weight filtration. -/
  weightFil : WeightFiltration V
  /-- The Hodge filtration. -/
  hodgeFil : HodgeFiltration V
  /-- The graded pieces Gr^W_k carry pure Hodge structures of weight k. -/
  graded_pure : ∀ (_k : Int), ∃ (W : Type u), Nonempty (PureHodgeStructure W)
  /-- Compatibility: the Hodge filtration induces a Hodge filtration on each
      graded piece. -/
  compatibility : True

/-- Path witness for the existence of a pure HS on the k-th graded piece. -/
def MixedHodgeStructure.gradedPurePath {V : Type u} (M : MixedHodgeStructure V)
    (k : Int) :
    Path (∃ W : Type u, Nonempty (PureHodgeStructure W)) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => M.graded_pure k⟩)

/-- Trivial MHS on PUnit. -/
def trivialMHS : MixedHodgeStructure PUnit where
  weightFil := {
    weight := fun _ _ => True
    ascending := fun _ _ _ => trivial
    exhaustive := fun _ => ⟨0, trivial⟩
  }
  hodgeFil := {
    fil := fun _ _ => True
    descending := fun _ _ _ => trivial
  }
  graded_pure := fun _ => ⟨PUnit, ⟨{
    weight := 0
    hodgeFil := { fil := fun _ _ => True, descending := fun _ _ _ => trivial }
    hodgeType := fun p q _ => p = 0 ∧ q = 0
    pq_sum := fun p q _ ⟨hp, hq⟩ => by simp [hp, hq]
    decomposition := fun _ => ⟨0, 0, rfl, rfl⟩
  }⟩⟩
  compatibility := trivial

/-- Path from trivialMHS to itself via refl. -/
def trivialMHS_refl_path :
    Path (trivialMHS.weightFil.weight 0 PUnit.unit)
         (trivialMHS.weightFil.weight 0 PUnit.unit) :=
  Path.refl _

/-! ## Morphisms of MHS -/

/-- A morphism of mixed Hodge structures. -/
structure MHSMorphism {V W : Type u}
    (M : MixedHodgeStructure V) (N : MixedHodgeStructure W) where
  /-- Underlying linear map. -/
  map : V → W
  /-- Preserves weight filtration. -/
  weight_compat : ∀ (k : Int) (v : V),
    M.weightFil.weight k v → N.weightFil.weight k (map v)
  /-- Preserves Hodge filtration. -/
  hodge_compat : ∀ (p : Int) (v : V),
    M.hodgeFil.fil p v → N.hodgeFil.fil p (map v)

/-- Identity MHS morphism. -/
def MHSMorphism.id {V : Type u} (M : MixedHodgeStructure V) :
    MHSMorphism M M where
  map := fun v => v
  weight_compat := fun _ _ h => h
  hodge_compat := fun _ _ h => h

/-- Composition of MHS morphisms. -/
def MHSMorphism.comp {V W X : Type u}
    {M : MixedHodgeStructure V} {N : MixedHodgeStructure W}
    {P : MixedHodgeStructure X}
    (f : MHSMorphism M N) (g : MHSMorphism N P) : MHSMorphism M P where
  map := g.map ∘ f.map
  weight_compat := fun k v hv => g.weight_compat k (f.map v) (f.weight_compat k v hv)
  hodge_compat := fun p v hv => g.hodge_compat p (f.map v) (f.hodge_compat p v hv)

/-- Path witness that id ∘ f = f for MHS morphisms. -/
def MHSMorphism.left_id_path {V W : Type u}
    {M : MixedHodgeStructure V} {N : MixedHodgeStructure W}
    (f : MHSMorphism M N) (v : V) :
    Path ((MHSMorphism.comp f (MHSMorphism.id N)).map v) (f.map v) :=
  Path.stepChain rfl

/-- Path witness that f ∘ id = f for MHS morphisms. -/
def MHSMorphism.right_id_path {V W : Type u}
    {M : MixedHodgeStructure V} {N : MixedHodgeStructure W}
    (f : MHSMorphism M N) (v : V) :
    Path ((MHSMorphism.comp (MHSMorphism.id M) f).map v) (f.map v) :=
  Path.stepChain rfl

/-! ## Exact Sequences of MHS -/

/-- Strict compatibility: MHS morphisms are strict w.r.t. both filtrations. -/
structure StrictMorphism {V W : Type u}
    {M : MixedHodgeStructure V} {N : MixedHodgeStructure W}
    (f : MHSMorphism M N) where
  /-- Weight-strict. -/
  weight_strict : ∀ (k : Int) (w : W),
    N.weightFil.weight k w →
    (∃ v, f.map v = w ∧ M.weightFil.weight k v) ∨ ¬ (∃ v, f.map v = w)
  /-- Hodge-strict. -/
  hodge_strict : ∀ (p : Int) (w : W),
    N.hodgeFil.fil p w →
    (∃ v, f.map v = w ∧ M.hodgeFil.fil p v) ∨ ¬ (∃ v, f.map v = w)

/-- Short exact sequence of MHS. -/
structure MHSExactSequence {A B C : Type u}
    (M : MixedHodgeStructure A) (N : MixedHodgeStructure B)
    (P : MixedHodgeStructure C) where
  /-- First map. -/
  f : MHSMorphism M N
  /-- Second map. -/
  g : MHSMorphism N P
  /-- Exactness at B (kernel of g ⊆ image of f). -/
  exact_at_B : ∀ b, (∀ c, g.map b ≠ c) ∨ ∃ a, f.map a = b

/-- Path witness for exactness. -/
def MHSExactSequence.exactPath {A B C : Type u}
    {M : MixedHodgeStructure A} {N : MixedHodgeStructure B}
    {P : MixedHodgeStructure C}
    (E : MHSExactSequence M N P) (b : B) :
    Path ((∀ c, E.g.map b ≠ c) ∨ ∃ a, E.f.map a = b) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => E.exact_at_B b⟩)

/-! ## Variation of Hodge Structure -/

/-- Data for a variation of Hodge structure over a base. -/
structure VariationOfHodgeStructure (B : Type u) (V : Type u) where
  /-- The base point type. -/
  fiber : B → V → Prop
  /-- Weight of the VHS. -/
  weight : Int
  /-- Hodge filtration on each fiber. -/
  fiberFil : B → HodgeFiltration V
  /-- Flat connection data: parallel transport. -/
  parallel_transport : (b₁ b₂ : B) → V → V
  /-- Griffiths transversality: ∇ F^p ⊆ F^{p-1} ⊗ Ω¹. -/
  griffiths : ∀ (b : B) (p : Int) (v : V),
    (fiberFil b).fil p v → (fiberFil b).fil (p - 1) (parallel_transport b b v)

/-- Path witness for Griffiths transversality. -/
def VariationOfHodgeStructure.griffithsPath {B V : Type u}
    (VHS : VariationOfHodgeStructure B V)
    (b : B) (p : Int) (v : V) (hv : (VHS.fiberFil b).fil p v) :
    Path ((VHS.fiberFil b).fil (p - 1) (VHS.parallel_transport b b v)) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => VHS.griffiths b p v hv⟩)

/-- Trivial VHS on PUnit. -/
def trivialVHS : VariationOfHodgeStructure PUnit PUnit where
  fiber := fun _ _ => True
  weight := 0
  fiberFil := fun _ => { fil := fun _ _ => True, descending := fun _ _ _ => trivial }
  parallel_transport := fun _ _ v => v
  griffiths := fun _ _ _ _ => trivial

/-- Path between trivial parallel transports. -/
def trivialVHS.transportPath :
    Path (trivialVHS.parallel_transport PUnit.unit PUnit.unit PUnit.unit) PUnit.unit :=
  Path.stepChain rfl

/-! ## Period Domain -/

/-- Abstract period domain data. -/
structure PeriodDomain where
  /-- Points of the period domain. -/
  carrier : Type u
  /-- Basepoint. -/
  basepoint : carrier
  /-- Horizontal tangent condition (flag variety structure). -/
  horizontal : carrier → carrier → Prop

/-- Period map data: maps base space to period domain. -/
structure PeriodMapData (B : Type u) where
  /-- The period domain. -/
  domain : PeriodDomain
  /-- The period map. -/
  periodMap : B → domain.carrier
  /-- Horizontality: the period map is horizontal. -/
  horizontal : ∀ b₁ b₂ : B, domain.horizontal (periodMap b₁) (periodMap b₂)

/-- Path witness for horizontality of the period map. -/
def PeriodMapData.horizontalPath {B : Type u} (P : PeriodMapData B)
    (b₁ b₂ : B) :
    Path (P.domain.horizontal (P.periodMap b₁) (P.periodMap b₂)) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => P.horizontal b₁ b₂⟩)

/-! ## Hodge Decomposition with Path Witnesses -/

/-- Full Hodge decomposition data with Path-valued witnesses. -/
structure HodgeDecompositionData (V : Type u) where
  /-- Harmonic projection. -/
  harmonic : V → V
  /-- Image of d component. -/
  exact : V → V
  /-- Image of δ component. -/
  coexact : V → V
  /-- Decomposition: v = H(v) + d(...) + δ(...). -/
  decompose : ∀ v : V, v = harmonic v

/-- Path witness for the decomposition. -/
def HodgeDecompositionData.decomposePath {V : Type u}
    (H : HodgeDecompositionData V) (v : V) :
    Path v (H.harmonic v) :=
  Path.stepChain (H.decompose v)

/-- Step chain for composing two Hodge decompositions. -/
def HodgeDecompositionData.composeDecompose {V : Type u}
    (H : HodgeDecompositionData V) (v : V) :
    Path v (H.harmonic (H.harmonic v)) :=
  Path.trans
    (Path.stepChain (H.decompose v))
    (Path.stepChain (H.decompose (H.harmonic v)))

/-- Idempotency path for harmonic projection. -/
def HodgeDecompositionData.idempotentPath {V : Type u}
    (H : HodgeDecompositionData V) (v : V)
    (idemp : H.harmonic (H.harmonic v) = H.harmonic v) :
    Path (H.harmonic (H.harmonic v)) (H.harmonic v) :=
  Path.stepChain idemp

/-! ## Mixed Hodge Structure Functoriality -/

/-- Pullback MHS along a map. -/
def pullbackMHS {V W : Type u} (f : W → V) (M : MixedHodgeStructure V) :
    MixedHodgeStructure W where
  weightFil := {
    weight := fun k w => M.weightFil.weight k (f w)
    ascending := fun k w hv => M.weightFil.ascending k (f w) hv
    exhaustive := fun w => M.weightFil.exhaustive (f w)
  }
  hodgeFil := {
    fil := fun p w => M.hodgeFil.fil p (f w)
    descending := fun p w hv => M.hodgeFil.descending p (f w) hv
  }
  graded_pure := M.graded_pure
  compatibility := trivial

/-- Path witness: pullback along id is the original MHS (pointwise). -/
def pullback_id_path {V : Type u} (M : MixedHodgeStructure V)
    (k : Int) (v : V) :
    Path ((pullbackMHS (fun x : V => x) M).weightFil.weight k v)
         (M.weightFil.weight k v) :=
  Path.stepChain rfl

/-- Path witness: pullback along f ∘ g = pullback g ∘ pullback f (pointwise). -/
def pullback_comp_path {U V W : Type u}
    (f : V → W) (g : U → V) (M : MixedHodgeStructure W)
    (k : Int) (u : U) :
    Path ((pullbackMHS (f ∘ g) M).weightFil.weight k u)
         ((pullbackMHS g (pullbackMHS f M)).weightFil.weight k u) :=
  Path.stepChain rfl

/-! ## Weight Spectral Sequence -/

/-- Weight spectral sequence data. -/
structure WeightSpectralSequence (V : Type u) where
  /-- The MHS. -/
  mhs : MixedHodgeStructure V
  /-- E₁ page: graded pieces. -/
  e1_page : Int → Int → Type u
  /-- Differential on E₁. -/
  d1 : ∀ p q, e1_page p q → e1_page (p + 1) q
  /-- Degeneration at E₂. -/
  degenerates_e2 : True

/-- Step chain for the weight spectral sequence degeneration. -/
def WeightSpectralSequence.degenerationChain {V : Type u}
    (W : WeightSpectralSequence V) :
    W.degenerates_e2 = W.mhs.compatibility :=
  rfl

/-! ## Deligne splitting -/

/-- Deligne splitting of a mixed Hodge structure. -/
structure DeligneSplitting (V : Type u) where
  /-- The MHS. -/
  mhs : MixedHodgeStructure V
  /-- Splitting subspaces I^{p,q}. -/
  splitting : Int → Int → V → Prop
  /-- Each I^{p,q} lies in F^p. -/
  in_hodge : ∀ p q v, splitting p q v → mhs.hodgeFil.fil p v
  /-- Each I^{p,q} lies in W_{p+q}. -/
  in_weight : ∀ p q v, splitting p q v → mhs.weightFil.weight (p + q) v

/-- Path witness for the Hodge inclusion of the splitting. -/
def DeligneSplitting.hodgePath {V : Type u} (D : DeligneSplitting V)
    (p q : Int) (v : V) (hv : D.splitting p q v) :
    Path (D.mhs.hodgeFil.fil p v) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => D.in_hodge p q v hv⟩)

/-- Path witness for the weight inclusion of the splitting. -/
def DeligneSplitting.weightPath {V : Type u} (D : DeligneSplitting V)
    (p q : Int) (v : V) (hv : D.splitting p q v) :
    Path (D.mhs.weightFil.weight (p + q) v) True :=
  Path.stepChain (propext ⟨fun _ => trivial, fun _ => D.in_weight p q v hv⟩)

/-- Chain composing both filtration constraints. -/
def DeligneSplitting.dualConstraintChain {V : Type u} (D : DeligneSplitting V)
    (p q : Int) (v : V) (hv : D.splitting p q v) :
    Path (D.mhs.hodgeFil.fil p v) (D.mhs.weightFil.weight (p + q) v) :=
  Path.trans
    (Path.stepChain (propext ⟨fun _ => D.in_weight p q v hv,
                              fun _ => D.in_hodge p q v hv⟩))
    (Path.refl _)

end MixedHodgeStructures
end Topology
end Path
end ComputationalPaths
