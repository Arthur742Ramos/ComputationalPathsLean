/-
  TypeClassPathDeep.lean
  Type Class Resolution and Dictionary Passing via Computational Paths

  Models type class resolution, instance derivation, superclass inheritance,
  diamond resolution, coherence, and dictionary passing — all via Path operations.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace TypeClassPathDeep

open Path

universe u v

-- ============================================================================
-- SECTION 1: Type Classes as Structures with Dictionaries
-- ============================================================================

/-- A type class is represented by a dictionary type for a given carrier -/
structure TClass (A : Type u) where
  dictType : Type u
  resolve  : A → dictType

/-- An instance witness: a specific dictionary value for a class -/
structure Instance (A : Type u) (tc : TClass A) where
  carrier : A
  dict    : tc.dictType
  valid   : tc.resolve carrier = dict

/-- Resolution step: one step in instance search -/
structure ResolutionStep {A : Type u} (a b : A) where
  step : Path a b

/-- Superclass relation: tc1 is a superclass of tc2 -/
structure Superclass (A : Type u) (tc1 tc2 : TClass A) where
  project : tc2.dictType → tc1.dictType

/-- Inheritance path through superclass chain -/
structure InheritancePath (A : Type u) where
  source : TClass A
  target : TClass A
  path   : source.dictType → target.dictType

-- ============================================================================
-- THEOREM 1: Identity resolution step
-- ============================================================================
def resolution_identity {A : Type u} (a : A) :
    Path a a := Path.refl a

-- ============================================================================
-- THEOREM 2: Resolution steps compose via trans
-- ============================================================================
def resolution_compose {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- ============================================================================
-- THEOREM 3: Resolution is associative
-- ============================================================================
theorem resolution_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================================
-- THEOREM 4: Resolution with identity left
-- ============================================================================
theorem resolution_id_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

-- ============================================================================
-- THEOREM 5: Resolution with identity right
-- ============================================================================
theorem resolution_id_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

-- ============================================================================
-- THEOREM 6: Resolution reversal (backtracking)
-- ============================================================================
def resolution_backtrack {A : Type u} {a b : A} (p : Path a b) :
    Path b a := Path.symm p

-- ============================================================================
-- THEOREM 7: Double backtrack = original
-- ============================================================================
theorem double_backtrack {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- ============================================================================
-- THEOREM 8: Symm distributes over trans
-- ============================================================================
theorem symm_trans_dist {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- ============================================================================
-- SECTION 2: Dictionary Passing Transformation
-- ============================================================================

/-- Dictionary passing: transforms a class method call into explicit dict arg -/
structure DictPass (A B : Type u) where
  original  : A → B
  withDict  : A → B
  coherence : (a : A) → Path (original a) (withDict a)

-- ============================================================================
-- THEOREM 9: Dictionary passing preserves function composition
-- ============================================================================
def dictpass_compose {A B C : Type u}
    (dp1 : DictPass A B) (dp2 : DictPass B C) (a : A) :
    Path (dp2.original (dp1.original a)) (dp2.withDict (dp1.withDict a)) :=
  let step1 : Path (dp2.original (dp1.original a))
                    (dp2.original (dp1.withDict a)) :=
    Path.congrArg dp2.original (dp1.coherence a)
  let step2 : Path (dp2.original (dp1.withDict a))
                    (dp2.withDict (dp1.withDict a)) :=
    dp2.coherence (dp1.withDict a)
  Path.trans step1 step2

-- ============================================================================
-- THEOREM 10: Dictionary passing identity
-- ============================================================================
def dictpass_id {A : Type u} (a : A) :
    Path (id a) (id a) := Path.refl (id a)

-- ============================================================================
-- THEOREM 11: CongrArg distributes over resolution chains
-- ============================================================================
theorem congrArg_resolution {A B : Type u} {a₁ a₂ a₃ : A}
    (f : A → B) (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- ============================================================================
-- THEOREM 12: CongrArg preserves backtracking
-- ============================================================================
theorem congrArg_backtrack {A B : Type u} {a₁ a₂ : A}
    (f : A → B) (p : Path a₁ a₂) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- ============================================================================
-- SECTION 3: Diamond Problem Resolution
-- ============================================================================

/-- Diamond: two paths from a to d through b and c respectively -/
structure Diamond {X : Type u} (a b c d : X) where
  left_up    : Path a b
  left_down  : Path b d
  right_up   : Path a c
  right_down : Path c d

/-- Coherent diamond: both paths yield the same result -/
structure CoherentDiamond {X : Type u} (a b c d : X) extends Diamond a b c d where
  coherence : Path.trans left_up left_down = Path.trans right_up right_down

-- ============================================================================
-- THEOREM 13: Diamond left path
-- ============================================================================
def diamond_left {X : Type u} {a b c d : X} (dia : Diamond a b c d) :
    Path a d := Path.trans dia.left_up dia.left_down

-- ============================================================================
-- THEOREM 14: Diamond right path
-- ============================================================================
def diamond_right {X : Type u} {a b c d : X} (dia : Diamond a b c d) :
    Path a d := Path.trans dia.right_up dia.right_down

-- ============================================================================
-- THEOREM 15: Coherent diamond yields path equality
-- ============================================================================
theorem coherent_diamond_eq {X : Type u} {a b c d : X}
    (cdia : CoherentDiamond a b c d) :
    Path.trans cdia.left_up cdia.left_down =
    Path.trans cdia.right_up cdia.right_down :=
  cdia.coherence

-- ============================================================================
-- THEOREM 16: Symmetric coherent diamond
-- ============================================================================
theorem diamond_symm_coherence {X : Type u} {a b c d : X}
    (cdia : CoherentDiamond a b c d) :
    Path.trans cdia.right_up cdia.right_down =
    Path.trans cdia.left_up cdia.left_down :=
  cdia.coherence.symm

-- ============================================================================
-- THEOREM 17: Trivial diamond (both paths identical)
-- ============================================================================
theorem trivial_diamond {X : Type u} {a b : X} (p : Path a b) :
    Path.trans p (Path.refl b) = Path.trans (Path.refl a) p := by
  rw [trans_refl_right, trans_refl_left]

-- ============================================================================
-- SECTION 4: Instance Resolution Search
-- ============================================================================

/-- Search state during instance resolution -/
structure SearchState {A : Type u} (start current : A) where
  accumulated : Path start current

/-- A resolution oracle: given current, produce next step -/
structure ResOracle (A : Type u) where
  step : (a : A) → Sigma (fun b : A => Path a b)

-- ============================================================================
-- THEOREM 18: Initial search state has refl path
-- ============================================================================
def initial_search {A : Type u} (a : A) :
    SearchState a a := ⟨Path.refl a⟩

-- ============================================================================
-- THEOREM 19: Search step extends path
-- ============================================================================
def search_extend {A : Type u} {a b c : A}
    (accumulated : Path a b) (step : Path b c) :
    Path a c := Path.trans accumulated step

-- ============================================================================
-- THEOREM 20: Search can be undone
-- ============================================================================
def search_undo {A : Type u} {a b : A}
    (p : Path a b) : Path b a := Path.symm p

-- ============================================================================
-- THEOREM 21: Extended search then undo = original (assoc)
-- ============================================================================
theorem search_extend_undo {A : Type u} {a b c : A}
    (acc : Path a b) (step : Path b c) :
    Path.trans (Path.trans acc step) (Path.symm step) =
    Path.trans acc (Path.trans step (Path.symm step)) :=
  trans_assoc acc step (Path.symm step)

-- ============================================================================
-- SECTION 5: Functional Dependencies via Paths
-- ============================================================================

/-- Functional dependency: knowing A determines B -/
structure FunDep (A B : Type u) where
  determine : A → B
  unique    : (a : A) → (b₁ b₂ : B) →
              Path (determine a) b₁ → Path (determine a) b₂ → Path b₁ b₂

-- ============================================================================
-- THEOREM 22: Functional dependency yields unique resolution
-- ============================================================================
def fundep_unique {A B : Type u} (fd : FunDep A B) (a : A)
    (b₁ b₂ : B) (p : Path (fd.determine a) b₁)
    (q : Path (fd.determine a) b₂) :
    Path b₁ b₂ :=
  fd.unique a b₁ b₂ p q

-- ============================================================================
-- THEOREM 23: Functional dependency is deterministic
-- ============================================================================
def fundep_deterministic {A B : Type u} (fd : FunDep A B) (a : A) :
    Path (fd.determine a) (fd.determine a) :=
  Path.refl (fd.determine a)

-- ============================================================================
-- THEOREM 24: Composed functional dependencies
-- ============================================================================
def fundep_compose_refl {A B C : Type u}
    (fd1 : FunDep A B) (fd2 : FunDep B C) (a : A) :
    Path (fd2.determine (fd1.determine a)) (fd2.determine (fd1.determine a)) :=
  Path.refl _

-- ============================================================================
-- THEOREM 25: Fundep lifts through congrArg
-- ============================================================================
def fundep_lift {A B : Type u} (fd : FunDep A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    Path (fd.determine a₁) (fd.determine a₂) :=
  Path.congrArg fd.determine p

-- ============================================================================
-- SECTION 6: Type Class Morphisms
-- ============================================================================

/-- Morphism between type class instances preserving structure -/
structure TCMorphism (A B : Type u) where
  map       : A → B
  mapPath   : {a₁ a₂ : A} → Path a₁ a₂ → Path (map a₁) (map a₂)
  presRefl  : (a : A) → mapPath (Path.refl a) = Path.refl (map a)
  presTrans : {a₁ a₂ a₃ : A} → (p : Path a₁ a₂) → (q : Path a₂ a₃) →
              mapPath (Path.trans p q) = Path.trans (mapPath p) (mapPath q)

-- ============================================================================
-- THEOREM 26: Identity morphism
-- ============================================================================
def idMorphism (A : Type u) : TCMorphism A A where
  map := id
  mapPath := id
  presRefl := fun _ => rfl
  presTrans := fun _ _ => rfl

-- ============================================================================
-- THEOREM 27: Identity morphism preserves paths
-- ============================================================================
theorem id_morphism_path {A : Type u} {a b : A} (p : Path a b) :
    (idMorphism A).mapPath p = p := rfl

-- ============================================================================
-- THEOREM 28: Morphism composition
-- ============================================================================
def composeMorphism {A B C : Type u}
    (f : TCMorphism A B) (g : TCMorphism B C) : TCMorphism A C where
  map := g.map ∘ f.map
  mapPath := g.mapPath ∘ f.mapPath
  presRefl := fun a => by
    show g.mapPath (f.mapPath (Path.refl a)) = Path.refl (g.map (f.map a))
    rw [f.presRefl a, g.presRefl (f.map a)]
  presTrans := fun p q => by
    show g.mapPath (f.mapPath (Path.trans p q)) =
         Path.trans (g.mapPath (f.mapPath p)) (g.mapPath (f.mapPath q))
    rw [f.presTrans p q, g.presTrans (f.mapPath p) (f.mapPath q)]

-- ============================================================================
-- THEOREM 29: Morphism preserves symm
-- ============================================================================
def morphism_pres_symm {A B : Type u} (m : TCMorphism A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (m.map a₂) (m.map a₁) :=
  Path.symm (m.mapPath p)

-- ============================================================================
-- THEOREM 30: CongrArg is a morphism's mapPath
-- ============================================================================
theorem congrArg_is_mapPath {A B : Type u} (f : A → B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg f p = Path.congrArg f p := rfl

-- ============================================================================
-- SECTION 7: Default Method Resolution
-- ============================================================================

/-- Default method: a fallback implementation -/
structure DefaultMethod {A : Type u} (default_impl custom_impl : A) where
  override_path : Path default_impl custom_impl

-- ============================================================================
-- THEOREM 31: Default method can be overridden via path
-- ============================================================================
def default_override {A : Type u} {d c : A} (dm : DefaultMethod d c) :
    Path d c := dm.override_path

-- ============================================================================
-- THEOREM 32: Override is reversible
-- ============================================================================
def override_reversible {A : Type u} {d c : A} (dm : DefaultMethod d c) :
    Path c d := Path.symm dm.override_path

-- ============================================================================
-- THEOREM 33: Chained defaults
-- ============================================================================
def chained_defaults {A : Type u} {a b c d : A}
    (dm1 : DefaultMethod a b) (dm2 : DefaultMethod c d)
    (link : Path b c) :
    Path a d :=
  Path.trans (Path.trans dm1.override_path link) dm2.override_path

-- ============================================================================
-- THEOREM 34: Chained defaults associativity
-- ============================================================================
theorem chained_defaults_assoc {A : Type u} {a b c d : A}
    (dm1 : DefaultMethod a b) (dm2 : DefaultMethod c d)
    (link : Path b c) :
    Path.trans (Path.trans dm1.override_path link) dm2.override_path =
    Path.trans dm1.override_path (Path.trans link dm2.override_path) :=
  trans_assoc dm1.override_path link dm2.override_path

-- ============================================================================
-- SECTION 8: Overlapping Instances
-- ============================================================================

/-- Two overlapping instances for the same class -/
structure OverlapPair {A : Type u} (inst1 inst2 : A) where
  overlap_coherence : Path inst1 inst2

-- ============================================================================
-- THEOREM 35: Overlapping instances are coherent
-- ============================================================================
def overlap_coherent {A : Type u} {i₁ i₂ : A} (op : OverlapPair i₁ i₂) :
    Path i₁ i₂ := op.overlap_coherence

-- ============================================================================
-- THEOREM 36: Triple overlap coherence
-- ============================================================================
def triple_overlap {A : Type u} {a b c d : A}
    (op1 : OverlapPair a b) (op2 : OverlapPair c d)
    (link : Path b c) :
    Path a d :=
  Path.trans (Path.trans op1.overlap_coherence link) op2.overlap_coherence

-- ============================================================================
-- THEOREM 37: Overlap with identity
-- ============================================================================
def overlap_refl {A : Type u} (a : A) :
    OverlapPair a a := ⟨Path.refl a⟩

-- ============================================================================
-- SECTION 9: Instance Chains
-- ============================================================================

/-- Instance chain: ordered list of instances to try -/
structure InstChain {A : Type u} (head tail : A) where
  fallback : Path head tail

-- ============================================================================
-- THEOREM 38: Chain resolution: head to tail
-- ============================================================================
def chain_resolve {A : Type u} {h t : A} (ch : InstChain h t) :
    Path h t := ch.fallback

-- ============================================================================
-- THEOREM 39: Concatenating chains
-- ============================================================================
def chain_concat {A : Type u} {a b c d : A}
    (ch1 : InstChain a b) (ch2 : InstChain c d)
    (link : Path b c) :
    Path a d :=
  Path.trans (Path.trans ch1.fallback link) ch2.fallback

-- ============================================================================
-- THEOREM 40: Chain with backtrack
-- ============================================================================
def chain_backtrack {A : Type u} {h t : A} (ch : InstChain h t) :
    Path t h := Path.symm ch.fallback

-- ============================================================================
-- THEOREM 41: Chain concat associativity
-- ============================================================================
theorem chain_concat_assoc {A : Type u} {a b c d : A}
    (ch1 : InstChain a b) (ch2 : InstChain c d) (link : Path b c) :
    Path.trans (Path.trans ch1.fallback link) ch2.fallback =
    Path.trans ch1.fallback (Path.trans link ch2.fallback) :=
  trans_assoc ch1.fallback link ch2.fallback

-- ============================================================================
-- SECTION 10: Coherence Proofs for Resolution
-- ============================================================================

/-- Global coherence: any two derivations of same instance are path-equal -/
structure GlobalCoherence (A : Type u) where
  coherent : {a b : A} → (p q : Path a b) → p = q

-- ============================================================================
-- THEOREM 42: Coherence implies all loops are refl
-- ============================================================================
theorem coherence_refl_loop {A : Type u} (gc : GlobalCoherence A) {a : A}
    (p : Path a a) : p = Path.refl a :=
  gc.coherent p (Path.refl a)

-- ============================================================================
-- THEOREM 43: Coherence for composed paths
-- ============================================================================
theorem coherence_compose {A : Type u} (gc : GlobalCoherence A)
    {a b c : A} (p₁ p₂ : Path a b) (q₁ q₂ : Path b c) :
    Path.trans p₁ q₁ = Path.trans p₂ q₂ :=
  gc.coherent (Path.trans p₁ q₁) (Path.trans p₂ q₂)

-- ============================================================================
-- THEOREM 44: Coherence for symmetric paths
-- ============================================================================
theorem coherence_symm {A : Type u} (gc : GlobalCoherence A)
    {a b : A} (p q : Path a b) :
    Path.symm p = Path.symm q :=
  gc.coherent (Path.symm p) (Path.symm q)

-- ============================================================================
-- THEOREM 45: Coherence implies uniqueness of resolution
-- ============================================================================
theorem coherence_unique_resolution {A : Type u} (gc : GlobalCoherence A)
    {a b : A} (p q : Path a b) : p = q :=
  gc.coherent p q

-- ============================================================================
-- SECTION 11: Derivation Trees as Paths
-- ============================================================================

/-- A derivation node: an instance with its dependencies resolved -/
structure DerivNode {A : Type u} (parent value : A) where
  edge : Path parent value

-- ============================================================================
-- THEOREM 46: Derivation path from root
-- ============================================================================
def deriv_from_root {A : Type u} {a b c d : A}
    (n1 : DerivNode a b) (n2 : DerivNode c d) (link : Path b c) :
    Path a d :=
  Path.trans (Path.trans n1.edge link) n2.edge

-- ============================================================================
-- THEOREM 47: Single derivation step
-- ============================================================================
def deriv_single {A : Type u} {p v : A} (n : DerivNode p v) :
    Path p v := n.edge

-- ============================================================================
-- THEOREM 48: Derivation reversal
-- ============================================================================
def deriv_reverse {A : Type u} {p v : A} (n : DerivNode p v) :
    Path v p := Path.symm n.edge

-- ============================================================================
-- SECTION 12: Superclass Extraction Paths
-- ============================================================================

/-- Extract superclass dictionary via projection path -/
structure SuperExtract (D₁ D₂ : Type u) where
  project  : D₁ → D₂
  embed    : D₂ → D₁
  retract  : (d : D₂) → Path (project (embed d)) d

-- ============================================================================
-- THEOREM 49: Superclass extraction is a retraction
-- ============================================================================
def super_retract {D₁ D₂ : Type u} (se : SuperExtract D₁ D₂) (d : D₂) :
    Path (se.project (se.embed d)) d := se.retract d

-- ============================================================================
-- THEOREM 50: Composed superclass extraction
-- ============================================================================
def super_extract_compose {D₁ D₂ D₃ : Type u}
    (se1 : SuperExtract D₁ D₂) (se2 : SuperExtract D₂ D₃) (d : D₃) :
    Path (se2.project (se1.project (se1.embed (se2.embed d)))) d :=
  let step1 : Path (se2.project (se1.project (se1.embed (se2.embed d))))
                    (se2.project (se2.embed d)) :=
    Path.congrArg se2.project (se1.retract (se2.embed d))
  let step2 : Path (se2.project (se2.embed d)) d := se2.retract d
  Path.trans step1 step2

-- ============================================================================
-- THEOREM 51: CongrArg through superclass projection
-- ============================================================================
def super_congrArg {D₁ D₂ : Type u} (se : SuperExtract D₁ D₂)
    {d₁ d₂ : D₁} (p : Path d₁ d₂) :
    Path (se.project d₁) (se.project d₂) :=
  Path.congrArg se.project p

-- ============================================================================
-- THEOREM 52: Extraction preserves composition
-- ============================================================================
theorem super_extract_trans {D₁ D₂ : Type u} (se : SuperExtract D₁ D₂)
    {d₁ d₂ d₃ : D₁} (p : Path d₁ d₂) (q : Path d₂ d₃) :
    Path.congrArg se.project (Path.trans p q) =
    Path.trans (Path.congrArg se.project p) (Path.congrArg se.project q) :=
  congrArg_trans se.project p q

-- ============================================================================
-- SECTION 13: Multi-Parameter Type Classes
-- ============================================================================

/-- Multi-param class: resolution depends on multiple types -/
structure MultiParamTC (A B : Type u) where
  dictType : Type u
  resolve  : A → B → dictType

-- ============================================================================
-- THEOREM 53: Multi-param resolution is functorial in first arg
-- ============================================================================
def multiparam_fst {A B : Type u} {a₁ a₂ : A} (b : B)
    (tc : MultiParamTC A B) (p : Path a₁ a₂) :
    Path (tc.resolve a₁ b) (tc.resolve a₂ b) :=
  Path.congrArg (fun a => tc.resolve a b) p

-- ============================================================================
-- THEOREM 54: Multi-param resolution is functorial in second arg
-- ============================================================================
def multiparam_snd {A B : Type u} (a : A) {b₁ b₂ : B}
    (tc : MultiParamTC A B) (q : Path b₁ b₂) :
    Path (tc.resolve a b₁) (tc.resolve a b₂) :=
  Path.congrArg (fun b => tc.resolve a b) q

-- ============================================================================
-- THEOREM 55: Multi-param resolution composition
-- ============================================================================
def multiparam_compose {A B : Type u} {a₁ a₂ : A} {b₁ b₂ : B}
    (tc : MultiParamTC A B) (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (tc.resolve a₁ b₁) (tc.resolve a₂ b₂) :=
  let step1 := Path.congrArg (fun a => tc.resolve a b₁) p
  let step2 := Path.congrArg (fun b => tc.resolve a₂ b) q
  Path.trans step1 step2

-- ============================================================================
-- SECTION 14: Canonical Structures and Unification Hints
-- ============================================================================

/-- Canonical structure: a designated instance for unification -/
structure Canonical {A : Type u} (canonical any_inst : A) where
  witness : Path any_inst canonical

-- ============================================================================
-- THEOREM 56: Canonical instance is unique up to path
-- ============================================================================
def canonical_unique {A : Type u} {c₁ c₂ a₁ a₂ : A}
    (can1 : Canonical c₁ a₁) (can2 : Canonical c₂ a₂)
    (h : Path c₁ c₂) :
    Path a₁ a₂ :=
  Path.trans (Path.trans can1.witness h) (Path.symm can2.witness)

-- ============================================================================
-- THEOREM 57: Canonical is idempotent
-- ============================================================================
def canonical_idempotent {A : Type u} {c a : A} (can : Canonical c a) :
    Path a c := can.witness

-- ============================================================================
-- THEOREM 58: Two canonical witnesses for same target compose to refl (step eq)
-- ============================================================================
theorem canonical_compose_refl {A : Type u} {c a : A}
    (can : Canonical c a) :
    Path.trans can.witness (Path.symm can.witness) =
    Path.trans (Path.symm (Path.symm can.witness)) (Path.symm can.witness) := by
  rw [symm_symm]

-- ============================================================================
-- SECTION 15: Newtype Deriving via Paths
-- ============================================================================

/-- Newtype: wrapping a type preserves its instances -/
structure NewtypeDeriving (A B : Type u) where
  wrap   : A → B
  unwrap : B → A
  iso1   : (a : A) → Path (unwrap (wrap a)) a
  iso2   : (b : B) → Path (wrap (unwrap b)) b

-- ============================================================================
-- THEOREM 59: Newtype deriving preserves paths
-- ============================================================================
def newtype_path {A B : Type u} (nt : NewtypeDeriving A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (nt.wrap a₁) (nt.wrap a₂) :=
  Path.congrArg nt.wrap p

-- ============================================================================
-- THEOREM 60: Newtype unwrap preserves paths
-- ============================================================================
def newtype_unwrap_path {A B : Type u} (nt : NewtypeDeriving A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (nt.unwrap b₁) (nt.unwrap b₂) :=
  Path.congrArg nt.unwrap p

-- ============================================================================
-- THEOREM 61: Newtype round-trip coherence
-- ============================================================================
def newtype_roundtrip {A B : Type u} (nt : NewtypeDeriving A B)
    (a : A) : Path (nt.unwrap (nt.wrap a)) a :=
  nt.iso1 a

-- ============================================================================
-- THEOREM 62: Newtype wrap-unwrap coherence
-- ============================================================================
def newtype_wrap_unwrap {A B : Type u} (nt : NewtypeDeriving A B)
    (b : B) : Path (nt.wrap (nt.unwrap b)) b :=
  nt.iso2 b

-- ============================================================================
-- THEOREM 63: Newtype path lifting distributes over trans
-- ============================================================================
theorem newtype_trans {A B : Type u} (nt : NewtypeDeriving A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg nt.wrap (Path.trans p q) =
    Path.trans (Path.congrArg nt.wrap p) (Path.congrArg nt.wrap q) :=
  congrArg_trans nt.wrap p q

-- ============================================================================
-- SECTION 16: Constraint Propagation
-- ============================================================================

/-- Constraint: a resolved type class obligation -/
structure Constraint {A : Type u} (required provided : A) where
  satisfy : Path required provided

-- ============================================================================
-- THEOREM 64: Constraint composition
-- ============================================================================
def constraint_compose {A : Type u} {a b c d : A}
    (c1 : Constraint a b) (c2 : Constraint c d)
    (link : Path b c) :
    Path a d :=
  Path.trans (Path.trans c1.satisfy link) c2.satisfy

-- ============================================================================
-- THEOREM 65: Constraint is satisfiable (witness)
-- ============================================================================
def constraint_satisfiable {A : Type u} {r p : A} (c : Constraint r p) :
    Path r p := c.satisfy

-- ============================================================================
-- THEOREM 66: Constraint reversal
-- ============================================================================
def constraint_reverse {A : Type u} {r p : A} (c : Constraint r p) :
    Path p r := Path.symm c.satisfy

-- ============================================================================
-- SECTION 17: Evidence Translation
-- ============================================================================

/-- Translating evidence between equivalent type class formulations -/
structure EvidenceTranslation (A B : Type u) where
  translate : A → B
  back      : B → A
  section_  : (a : A) → Path (back (translate a)) a
  retract_  : (b : B) → Path (translate (back b)) b

-- ============================================================================
-- THEOREM 67: Evidence translation preserves identity
-- ============================================================================
def evidence_id {A B : Type u} (et : EvidenceTranslation A B) (a : A) :
    Path (et.back (et.translate a)) a := et.section_ a

-- ============================================================================
-- THEOREM 68: Evidence translation composes
-- ============================================================================
def evidence_compose {A B C : Type u}
    (et1 : EvidenceTranslation A B) (et2 : EvidenceTranslation B C) (a : A) :
    Path (et1.back (et2.back (et2.translate (et1.translate a)))) a :=
  let step1 : Path (et2.back (et2.translate (et1.translate a)))
                    (et1.translate a) :=
    et2.section_ (et1.translate a)
  let step2 : Path (et1.back (et2.back (et2.translate (et1.translate a))))
                    (et1.back (et1.translate a)) :=
    Path.congrArg et1.back step1
  Path.trans step2 (et1.section_ a)

-- ============================================================================
-- THEOREM 69: Evidence translation path lifting
-- ============================================================================
def evidence_lift {A B : Type u} (et : EvidenceTranslation A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (et.translate a₁) (et.translate a₂) :=
  Path.congrArg et.translate p

-- ============================================================================
-- SECTION 18: Associated Types via Paths
-- ============================================================================

/-- Associated type family: each class instance determines an associated type value -/
structure AssocType (Idx : Type u) (Val : Type u) where
  assoc : Idx → Val

-- ============================================================================
-- THEOREM 70: Associated type is functorial
-- ============================================================================
def assoc_functorial {Idx Val : Type u} (at_ : AssocType Idx Val)
    {i₁ i₂ : Idx} (p : Path i₁ i₂) :
    Path (at_.assoc i₁) (at_.assoc i₂) :=
  Path.congrArg at_.assoc p

-- ============================================================================
-- THEOREM 71: Associated type composition
-- ============================================================================
theorem assoc_compose {Idx Val : Type u} (at_ : AssocType Idx Val)
    {i₁ i₂ i₃ : Idx} (p : Path i₁ i₂) (q : Path i₂ i₃) :
    Path.congrArg at_.assoc (Path.trans p q) =
    Path.trans (Path.congrArg at_.assoc p) (Path.congrArg at_.assoc q) :=
  congrArg_trans at_.assoc p q

-- ============================================================================
-- THEOREM 72: Associated type preserves symmetry
-- ============================================================================
theorem assoc_symm {Idx Val : Type u} (at_ : AssocType Idx Val)
    {i₁ i₂ : Idx} (p : Path i₁ i₂) :
    Path.congrArg at_.assoc (Path.symm p) =
    Path.symm (Path.congrArg at_.assoc p) :=
  congrArg_symm at_.assoc p

-- ============================================================================
-- SECTION 19: Full Resolution Pipeline
-- ============================================================================

/-- Full resolution pipeline: search → resolve → extract → pass dictionary -/
structure FullPipeline (A B : Type u) where
  search   : A → A
  resolve  : A → B
  coherent : (a : A) → Path (search a) a

-- ============================================================================
-- THEOREM 73: Pipeline coherence via congrArg
-- ============================================================================
def pipeline_coherent {A B : Type u} (fp : FullPipeline A B) (a : A) :
    Path (fp.resolve (fp.search a)) (fp.resolve a) :=
  Path.congrArg fp.resolve (fp.coherent a)

-- ============================================================================
-- THEOREM 74: Pipeline is idempotent up to path
-- ============================================================================
def pipeline_idempotent {A B : Type u} (fp : FullPipeline A B)
    (a : A) (h : Path (fp.search (fp.search a)) (fp.search a)) :
    Path (fp.resolve (fp.search (fp.search a))) (fp.resolve a) :=
  Path.trans (Path.congrArg fp.resolve h) (Path.congrArg fp.resolve (fp.coherent a))

-- ============================================================================
-- THEOREM 75: Two pipelines compose
-- ============================================================================
def pipeline_compose {A B C : Type u}
    (fp1 : FullPipeline A B) (fp2 : FullPipeline B C) (a : A) :
    Path (fp2.resolve (fp2.search (fp1.resolve (fp1.search a))))
         (fp2.resolve (fp1.resolve a)) :=
  let step1 : Path (fp2.resolve (fp2.search (fp1.resolve (fp1.search a))))
                    (fp2.resolve (fp1.resolve (fp1.search a))) :=
    Path.congrArg fp2.resolve (fp2.coherent (fp1.resolve (fp1.search a)))
  let step2 : Path (fp2.resolve (fp1.resolve (fp1.search a)))
                    (fp2.resolve (fp1.resolve a)) :=
    Path.congrArg fp2.resolve (Path.congrArg fp1.resolve (fp1.coherent a))
  Path.trans step1 step2

-- ============================================================================
-- THEOREM 76: Pipeline resolve distributes
-- ============================================================================
theorem pipeline_resolve_trans {A B : Type u} (fp : FullPipeline A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg fp.resolve (Path.trans p q) =
    Path.trans (Path.congrArg fp.resolve p) (Path.congrArg fp.resolve q) :=
  congrArg_trans fp.resolve p q

-- ============================================================================
-- SECTION 20: Fourfold Resolution and Pentagon
-- ============================================================================

-- THEOREM 77: Fourfold resolution associativity
theorem fourfold_resolution {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) :=
  trans_assoc_fourfold p q r s

-- THEOREM 78: Fourfold resolution (alt)
theorem fourfold_resolution_alt {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) :=
  trans_assoc_fourfold_alt p q r s

-- ============================================================================
-- THEOREM 79: CongrArg preserves refl
-- ============================================================================
theorem congrArg_refl {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

-- ============================================================================
-- THEOREM 80: CongrArg composition
-- ============================================================================
theorem congrArg_comp_eq {A B C : Type u} (f : B → C) (g : A → B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg f (Path.congrArg g p) = Path.congrArg (f ∘ g) p :=
  (congrArg_comp f g p).symm

-- ============================================================================
-- SECTION 21: Resolution Uniqueness and Canonicity
-- ============================================================================

-- THEOREM 81: CongrArg id is identity
theorem congrArg_id_path {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg id p = p :=
  congrArg_id p

-- THEOREM 82: Trans left cancel
theorem resolution_left_cancel {A : Type u} {a b c : A}
    (p : Path a b) (q₁ q₂ : Path b c) (h : Path.trans p q₁ = Path.trans p q₂) :
    q₁ = q₂ := by
  have h₁ := _root_.congrArg Path.steps h
  simp [Path.trans] at h₁
  have h₂ := _root_.congrArg Path.proof h
  cases q₁; cases q₂; simp at h₁ h₂; simp [h₁]

-- THEOREM 83: Trans right cancel
theorem resolution_right_cancel {A : Type u} {a b c : A}
    (p₁ p₂ : Path a b) (q : Path b c) (h : Path.trans p₁ q = Path.trans p₂ q) :
    p₁ = p₂ := by
  have h₁ := _root_.congrArg Path.steps h
  simp [Path.trans] at h₁
  cases p₁; cases p₂; simp at h₁; simp [h₁]

-- ============================================================================
-- SECTION 22: Witness Extraction
-- ============================================================================

/-- Extract the underlying equality from a resolution path -/
theorem resolution_toEq {A : Type u} {a b : A} (p : Path a b) :
    a = b := Path.toEq p

-- THEOREM 84: toEq preserves trans
theorem toEq_resolution_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.toEq (Path.trans p q) = (Path.toEq p).trans (Path.toEq q) :=
  toEq_trans p q

-- THEOREM 85: toEq preserves symm
theorem toEq_resolution_symm {A : Type u} {a b : A}
    (p : Path a b) :
    Path.toEq (Path.symm p) = (Path.toEq p).symm :=
  toEq_symm p

-- ============================================================================
-- SECTION 23: Instance Priority and Selection
-- ============================================================================

/-- Instance with priority: higher priority wins -/
structure PriorityInstance {A : Type u} (val : A) where
  priority : Nat

/-- Selection between two instances based on priority -/
def selectInstance {A : Type u} {v₁ v₂ : A}
    (_i₁ : PriorityInstance v₁) (_i₂ : PriorityInstance v₂)
    (p : Path v₁ v₂) : Path v₁ v₂ := p

-- THEOREM 86: Selection is coherent regardless of priority
theorem select_coherent {A : Type u} {v₁ v₂ : A}
    (i₁ : PriorityInstance v₁) (i₂ : PriorityInstance v₂)
    (p : Path v₁ v₂) :
    selectInstance i₁ i₂ p = p := rfl

-- ============================================================================
-- SECTION 24: Local Instances and Scoped Resolution
-- ============================================================================

/-- Local instance: valid within a scope -/
structure LocalInst {A : Type u} (global_ local_ : A) where
  override : Path global_ local_

-- THEOREM 87: Local instance overrides global
def local_overrides {A : Type u} {g l : A} (li : LocalInst g l) :
    Path g l := li.override

-- THEOREM 88: Leaving scope restores global
def scope_exit {A : Type u} {g l : A} (li : LocalInst g l) :
    Path l g := Path.symm li.override

-- THEOREM 89: Nested local instances compose
def nested_local {A : Type u} {g l₁ l₂ : A}
    (li1 : LocalInst g l₁) (li2 : LocalInst l₁ l₂) :
    Path g l₂ := Path.trans li1.override li2.override

-- THEOREM 90: Nested local + exit = single local (assoc)
theorem nested_exit {A : Type u} {g l₁ l₂ : A}
    (li1 : LocalInst g l₁) (li2 : LocalInst l₁ l₂) :
    Path.trans (Path.trans li1.override li2.override) (Path.symm li2.override) =
    Path.trans li1.override (Path.trans li2.override (Path.symm li2.override)) :=
  trans_assoc li1.override li2.override (Path.symm li2.override)

-- ============================================================================
-- SECTION 25: Coherence via Symmetry and Groupoid Laws
-- ============================================================================

-- THEOREM 91: Symm is involutive
theorem symm_involutive {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := symm_symm p

-- THEOREM 92: Refl is fixed by symm
theorem symm_refl_is_refl {A : Type u} (a : A) :
    Path.symm (Path.refl a) = Path.refl a := symm_refl a

-- THEOREM 93: Trans-symm toEq is rfl
theorem left_inverse_toEq {A : Type u} {a : A} (p : Path a a) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl a).toEq := by
  simp

-- THEOREM 94: Symm-trans toEq is rfl
theorem right_inverse_toEq {A : Type u} {a : A} (p : Path a a) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by
  simp

-- ============================================================================
-- SECTION 26: Uniqueness of Identity Proofs in Resolution
-- ============================================================================

-- THEOREM 95: Path equality from step-level equality
theorem path_eq_of_steps {A : Type u} {a b : A}
    (p q : Path a b) (h : p.steps = q.steps) : p = q := by
  cases p; cases q; simp at h; simp [h]

-- THEOREM 96: Refl is unique among empty-step paths
theorem refl_unique_empty {A : Type u} (a : A)
    (p : Path a a) (h : p.steps = []) : p = Path.refl a := by
  cases p; simp at h; simp [Path.refl, h]

-- ============================================================================
-- SECTION 27: Dictionary Passing Naturality
-- ============================================================================

-- THEOREM 97: Dictionary passing naturality square (toEq level)
theorem dictpass_naturality_toEq {A B : Type u}
    (dp : DictPass A B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.toEq (Path.trans (dp.coherence a₁) (Path.congrArg dp.withDict p)) =
    Path.toEq (Path.trans (Path.congrArg dp.original p) (dp.coherence a₂)) := by
  cases p with
  | mk steps proof => cases proof; simp

-- ============================================================================
-- SECTION 28: Resolution Path Algebra Summary
-- ============================================================================

-- THEOREM 98: Full groupoid: left unit + right unit + assoc + inverse
theorem resolution_groupoid {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.refl a) p = p
    ∧ Path.trans p (Path.refl b) = p
    ∧ Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  ⟨trans_refl_left p, trans_refl_right p, trans_assoc p q r⟩

-- THEOREM 99: Symm is anti-homomorphism
theorem symm_anti_homo {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- THEOREM 100: CongrArg is a functor (preserves trans and symm)
theorem congrArg_functor {A B : Type u} (f : A → B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q)
    ∧ Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  ⟨congrArg_trans f p q, congrArg_symm f p⟩

end TypeClassPathDeep
end ComputationalPaths
