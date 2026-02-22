/-
  ComputationalPaths.Path.Algebra.SpectraPathDeep
  ================================================
  Spectra and Stable Homotopy Theory via Computational Paths

  We develop the theory of spectra — the fundamental objects of stable
  homotopy theory — entirely through computational paths. Structure maps,
  omega-spectra, maps of spectra, homotopy groups, cofiber/fiber sequences,
  Eilenberg-MacLane spectra, suspension spectra, and long exact sequences
  are all witnessed by Path.trans, Path.symm, Path.congrArg, etc.

  Key: Path is a Type (structure with steps + proof). Lemmas like trans_assoc
  produce Prop equalities (=) between Paths. We use `def` for Path-valued
  constructions and `theorem` for Prop-valued results.

  Author: armada-343 (SpectraPathDeep)
  Date: 2026-02-16
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Spectra

open ComputationalPaths.Path

-- ============================================================================
-- § 1. BASIC SPECTRUM STRUCTURE
-- ============================================================================

/-- A prespectrum: sequence of pointed types with structure maps. -/
structure PreSpectrum where
  Space : Nat → Type
  point : (n : Nat) → Space n
  structMap : (n : Nat) → Space n → Space (n + 1)
  structPoint : (n : Nat) → Path (structMap n (point n)) (point (n + 1))

/-- An omega-spectrum: structure maps are equivalences witnessed by paths. -/
structure OmegaSpectrum extends PreSpectrum where
  adjoint : (n : Nat) → Space (n + 1) → Space n
  rightInv : (n : Nat) → (x : Space (n + 1)) →
    Path (structMap n (adjoint n x)) x
  leftInv : (n : Nat) → (x : Space n) →
    Path (adjoint n (structMap n x)) x

/-- Level of a spectrum. -/
noncomputable def PreSpectrum.level (E : PreSpectrum) (n : Nat) : Type := E.Space n

/-- The basepoint at level n. -/
noncomputable def PreSpectrum.base (E : PreSpectrum) (n : Nat) : E.Space n := E.point n

-- ============================================================================
-- § 2. MAPS OF SPECTRA
-- ============================================================================

/-- A map of prespectra: level-wise maps commuting with structure maps. -/
structure SpectrumMap (E F : PreSpectrum) where
  mapLevel : (n : Nat) → E.Space n → F.Space n
  mapPoint : (n : Nat) → Path (mapLevel n (E.point n)) (F.point n)
  mapCommute : (n : Nat) → (x : E.Space n) →
    Path (F.structMap n (mapLevel n x)) (mapLevel (n + 1) (E.structMap n x))

/-- Identity map of spectra. -/
noncomputable def SpectrumMap.idMap (E : PreSpectrum) : SpectrumMap E E where
  mapLevel := fun _ x => x
  mapPoint := fun n => Path.refl (E.point n)
  mapCommute := fun n x => Path.refl (E.structMap n x)

/-- Composition of spectrum maps. -/
noncomputable def SpectrumMap.comp {E F G : PreSpectrum}
    (g : SpectrumMap F G) (f : SpectrumMap E F) : SpectrumMap E G where
  mapLevel := fun n x => g.mapLevel n (f.mapLevel n x)
  mapPoint := fun n =>
    Path.trans
      (Path.congrArg (g.mapLevel n) (f.mapPoint n))
      (g.mapPoint n)
  mapCommute := fun n x =>
    Path.trans
      (Path.congrArg (G.structMap n) (Path.refl (g.mapLevel n (f.mapLevel n x))))
      (Path.trans
        (g.mapCommute n (f.mapLevel n x))
        (Path.congrArg (g.mapLevel (n + 1)) (f.mapCommute n x)))

-- ============================================================================
-- § 3. HOMOTOPY OF SPECTRUM MAPS
-- ============================================================================

/-- A homotopy between two spectrum maps. -/
structure SpectrumHomotopy {E F : PreSpectrum}
    (f g : SpectrumMap E F) where
  htpyLevel : (n : Nat) → (x : E.Space n) →
    Path (f.mapLevel n x) (g.mapLevel n x)
  htpyPoint : (n : Nat) →
    Path.trans (htpyLevel n (E.point n)) (g.mapPoint n) =
    f.mapPoint n

/-- Reflexive homotopy — identity homotopy. -/
noncomputable def SpectrumHomotopy.refl {E F : PreSpectrum}
    (f : SpectrumMap E F) : SpectrumHomotopy f f where
  htpyLevel := fun n x => Path.refl (f.mapLevel n x)
  htpyPoint := fun n => trans_refl_left (f.mapPoint n)

-- ============================================================================
-- § 4. STABLE HOMOTOPY GROUPS — LOOPS
-- ============================================================================

/-- A loop at level n: path from basepoint to itself. -/
noncomputable def LoopAt (E : PreSpectrum) (n : Nat) : Type :=
  Path (E.point n) (E.point n)

/-- The trivial loop. -/
noncomputable def LoopAt.trivial (E : PreSpectrum) (n : Nat) : LoopAt E n :=
  Path.refl (E.point n)

/-- Loop composition via trans. -/
noncomputable def LoopAt.compose {E : PreSpectrum} {n : Nat}
    (p q : LoopAt E n) : LoopAt E n :=
  Path.trans p q

/-- Loop inverse via symm. -/
noncomputable def LoopAt.inverse {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) : LoopAt E n :=
  Path.symm p

/-- Theorem 1: Loop composition is associative. -/
theorem loop_compose_assoc {E : PreSpectrum} {n : Nat}
    (p q r : LoopAt E n) :
    LoopAt.compose (LoopAt.compose p q) r =
    LoopAt.compose p (LoopAt.compose q r) :=
  trans_assoc p q r

/-- Theorem 2: Trivial loop is left identity. -/
theorem loop_trivial_left {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    LoopAt.compose (LoopAt.trivial E n) p = p :=
  trans_refl_left p

/-- Theorem 3: Trivial loop is right identity. -/
theorem loop_trivial_right {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    LoopAt.compose p (LoopAt.trivial E n) = p :=
  trans_refl_right p

/-- Theorem 4: Symm-trans law for loops. -/
theorem loop_symm_trans {E : PreSpectrum} {n : Nat}
    (p q : LoopAt E n) :
    Path.symm (LoopAt.compose p q) =
    Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 5: Double inverse is identity. -/
theorem loop_inverse_invol {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    LoopAt.inverse (LoopAt.inverse p) = p :=
  symm_symm p

-- ============================================================================
-- § 5. STRUCTURE MAP ACTION ON LOOPS (SUSPENSION HOMOMORPHISM)
-- ============================================================================

/-- Push a loop forward through the structure map. -/
noncomputable def suspensionMap {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) : Path (E.structMap n (E.point n)) (E.structMap n (E.point n)) :=
  Path.congrArg (E.structMap n) p

/-- Theorem 6: Suspension map preserves composition. -/
theorem suspensionMap_compose {E : PreSpectrum} {n : Nat}
    (p q : LoopAt E n) :
    suspensionMap (LoopAt.compose p q) =
    Path.trans (suspensionMap p) (suspensionMap q) :=
  congrArg_trans (E.structMap n) p q

/-- Theorem 7: Suspension map preserves inverses. -/
theorem suspensionMap_inverse {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    suspensionMap (LoopAt.inverse p) =
    Path.symm (suspensionMap p) :=
  congrArg_symm (E.structMap n) p

/-- Theorem 8: Suspension map preserves identity. -/
theorem suspensionMap_refl {E : PreSpectrum} {n : Nat} :
    suspensionMap (LoopAt.trivial E n) =
    Path.refl (E.structMap n (E.point n)) :=
  rfl

-- ============================================================================
-- § 6. OMEGA-SPECTRUM LOOP EQUIVALENCE
-- ============================================================================

/-- For an omega-spectrum, map loops at n+1 back to level n. -/
noncomputable def omegaLoopBack {E : OmegaSpectrum} {n : Nat}
    (p : LoopAt E.toPreSpectrum (n + 1)) :
    Path (E.adjoint n (E.point (n + 1))) (E.adjoint n (E.point (n + 1))) :=
  Path.congrArg (E.adjoint n) p

/-- Theorem 9: Omega loop-back preserves composition. -/
theorem omegaLoopBack_compose {E : OmegaSpectrum} {n : Nat}
    (p q : LoopAt E.toPreSpectrum (n + 1)) :
    omegaLoopBack (LoopAt.compose p q) =
    Path.trans (omegaLoopBack p) (omegaLoopBack q) :=
  congrArg_trans (E.adjoint n) p q

/-- Theorem 10: Omega loop-back preserves inverses. -/
theorem omegaLoopBack_inverse {E : OmegaSpectrum} {n : Nat}
    (p : LoopAt E.toPreSpectrum (n + 1)) :
    omegaLoopBack (LoopAt.inverse p) =
    Path.symm (omegaLoopBack p) :=
  congrArg_symm (E.adjoint n) p

-- ============================================================================
-- § 7. FIBER SEQUENCES
-- ============================================================================

/-- Fiber of a spectrum map at a level. -/
structure SpectrumFiber {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat) where
  pt : E.Space n
  witness : Path (f.mapLevel n pt) (F.point n)

/-- The basepoint fiber element. -/
noncomputable def SpectrumFiber.baseFiber {E F : PreSpectrum}
    (f : SpectrumMap E F) (n : Nat) : SpectrumFiber f n where
  pt := E.point n
  witness := f.mapPoint n

/-- Path in the fiber: paths in E compatible over F. -/
structure FiberPath {E F : PreSpectrum} {f : SpectrumMap E F} {n : Nat}
    (a b : SpectrumFiber f n) where
  basePath : Path a.pt b.pt
  overPath :
    Path.trans (Path.congrArg (f.mapLevel n) basePath) b.witness =
    a.witness

/-- Theorem 11: Reflexive fiber path. -/
noncomputable def FiberPath.refl {E F : PreSpectrum} {f : SpectrumMap E F} {n : Nat}
    (a : SpectrumFiber f n) : FiberPath a a where
  basePath := Path.refl a.pt
  overPath := trans_refl_left a.witness

-- ============================================================================
-- § 8. COFIBER SEQUENCES
-- ============================================================================

/-- Cofiber data for a spectrum map. -/
structure SpectrumCofiber (E F : PreSpectrum) where
  CofSpace : Nat → Type
  cofPoint : (n : Nat) → CofSpace n
  incl : (n : Nat) → F.Space n → CofSpace n
  inclPoint : (n : Nat) → Path (incl n (F.point n)) (cofPoint n)

/-- The collapse data in a cofiber construction. -/
structure CofiberMapData {E F : PreSpectrum}
    (f : SpectrumMap E F)
    (C : SpectrumCofiber E F) where
  collapse : (n : Nat) → (x : E.Space n) →
    Path (C.incl n (f.mapLevel n x)) (C.cofPoint n)

/-- Theorem 12: Cofiber inclusion sends basepoint to cofPoint. -/
noncomputable def cofiber_incl_base {E F : PreSpectrum}
    (C : SpectrumCofiber E F) (n : Nat) :
    Path (C.incl n (F.point n)) (C.cofPoint n) :=
  C.inclPoint n

-- ============================================================================
-- § 9. SUSPENSION SPECTRUM
-- ============================================================================

/-- Suspension data: a type with a point and suspension operation. -/
structure SuspensionData where
  carrier : Nat → Type
  base : (n : Nat) → carrier n
  susp : (n : Nat) → carrier n → carrier (n + 1)
  suspBase : (n : Nat) → Path (susp n (base n)) (base (n + 1))

/-- Build a prespectrum from suspension data. -/
noncomputable def SuspensionData.toPreSpectrum (S : SuspensionData) : PreSpectrum where
  Space := S.carrier
  point := S.base
  structMap := S.susp
  structPoint := S.suspBase

/-- Theorem 13: Suspension spectrum structure map preserves basepoint. -/
noncomputable def susp_spectrum_base (S : SuspensionData) (n : Nat) :
    Path (S.susp n (S.base n)) (S.base (n + 1)) :=
  S.suspBase n

/-- Iterated suspension. -/
noncomputable def iterSusp (S : SuspensionData) (n : Nat) (x : S.carrier 0) : S.carrier n :=
  match n with
  | 0 => x
  | k + 1 => S.susp k (iterSusp S k x)

/-- Theorem 14: Iterated suspension of base is base (Path-valued). -/
noncomputable def iterSusp_base (S : SuspensionData) :
    (n : Nat) → Path (iterSusp S n (S.base 0)) (S.base n)
  | 0 => Path.refl (S.base 0)
  | n + 1 =>
    Path.trans
      (Path.congrArg (S.susp n) (iterSusp_base S n))
      (S.suspBase n)

-- ============================================================================
-- § 10. EILENBERG-MACLANE SPECTRUM
-- ============================================================================

/-- Eilenberg-MacLane spectrum data: each level has a group operation. -/
structure EMSpectrumData where
  KSpace : Nat → Type
  kpoint : (n : Nat) → KSpace n
  kop : (n : Nat) → KSpace n → KSpace n → KSpace n
  kunit_left : (n : Nat) → (x : KSpace n) →
    Path (kop n (kpoint n) x) x
  kunit_right : (n : Nat) → (x : KSpace n) →
    Path (kop n x (kpoint n)) x
  kinv : (n : Nat) → KSpace n → KSpace n
  kinv_left : (n : Nat) → (x : KSpace n) →
    Path (kop n (kinv n x) x) (kpoint n)
  kassoc : (n : Nat) → (x y z : KSpace n) →
    Path (kop n (kop n x y) z) (kop n x (kop n y z))
  kstruct : (n : Nat) → KSpace n → KSpace (n + 1)
  kstructBase : (n : Nat) → Path (kstruct n (kpoint n)) (kpoint (n + 1))

/-- Theorem 15: EM group operation is unital (left). -/
noncomputable def em_unit_left (D : EMSpectrumData) (n : Nat) (x : D.KSpace n) :
    Path (D.kop n (D.kpoint n) x) x :=
  D.kunit_left n x

/-- Theorem 16: EM group operation is unital (right). -/
noncomputable def em_unit_right (D : EMSpectrumData) (n : Nat) (x : D.KSpace n) :
    Path (D.kop n x (D.kpoint n)) x :=
  D.kunit_right n x

/-- Theorem 17: EM group operation is associative. -/
noncomputable def em_assoc (D : EMSpectrumData) (n : Nat) (x y z : D.KSpace n) :
    Path (D.kop n (D.kop n x y) z) (D.kop n x (D.kop n y z)) :=
  D.kassoc n x y z

/-- Theorem 18: EM inverse is left inverse. -/
noncomputable def em_inv_left (D : EMSpectrumData) (n : Nat) (x : D.KSpace n) :
    Path (D.kop n (D.kinv n x) x) (D.kpoint n) :=
  D.kinv_left n x

/-- Build EM prespectrum from EM data. -/
noncomputable def EMSpectrumData.toPreSpectrum (D : EMSpectrumData) : PreSpectrum where
  Space := D.KSpace
  point := D.kpoint
  structMap := D.kstruct
  structPoint := D.kstructBase

-- ============================================================================
-- § 11. SMASH PRODUCT OF SPECTRA
-- ============================================================================

/-- Smash product data for two prespectra. -/
structure SmashSpectrum (E F : PreSpectrum) where
  SmSpace : Nat → Type
  smPoint : (n : Nat) → SmSpace n
  smPair : (n : Nat) → E.Space n → F.Space n → SmSpace n
  smLeft : (n : Nat) → (y : F.Space n) →
    Path (smPair n (E.point n) y) (smPoint n)
  smRight : (n : Nat) → (x : E.Space n) →
    Path (smPair n x (F.point n)) (smPoint n)
  smStruct : (n : Nat) → SmSpace n → SmSpace (n + 1)
  smStructBase : (n : Nat) → Path (smStruct n (smPoint n)) (smPoint (n + 1))

/-- Theorem 19: Smash of basepoints is basepoint (left). -/
noncomputable def smash_base_left {E F : PreSpectrum} (S : SmashSpectrum E F) (n : Nat)
    (y : F.Space n) :
    Path (S.smPair n (E.point n) y) (S.smPoint n) :=
  S.smLeft n y

/-- Theorem 20: Smash of basepoints is basepoint (right). -/
noncomputable def smash_base_right {E F : PreSpectrum} (S : SmashSpectrum E F) (n : Nat)
    (x : E.Space n) :
    Path (S.smPair n x (F.point n)) (S.smPoint n) :=
  S.smRight n x

/-- SmashSpectrum as a PreSpectrum. -/
noncomputable def SmashSpectrum.toPreSpectrum {E F : PreSpectrum} (S : SmashSpectrum E F) : PreSpectrum where
  Space := S.SmSpace
  point := S.smPoint
  structMap := S.smStruct
  structPoint := S.smStructBase

-- ============================================================================
-- § 12. DESUSPENSION
-- ============================================================================

/-- Desuspension data for a spectrum. -/
structure DesuspensionData (E : PreSpectrum) where
  desusp : (n : Nat) → E.Space (n + 1) → E.Space n
  desuspBase : (n : Nat) → Path (desusp n (E.point (n + 1))) (E.point n)
  desuspStruct : (n : Nat) → (x : E.Space n) →
    Path (desusp n (E.structMap n x)) x

/-- Theorem 21: Desuspension sends basepoint to basepoint. -/
noncomputable def desusp_base {E : PreSpectrum} (D : DesuspensionData E) (n : Nat) :
    Path (D.desusp n (E.point (n + 1))) (E.point n) :=
  D.desuspBase n

/-- Theorem 22: Desuspension is left inverse of structure map. -/
noncomputable def desusp_struct_inv {E : PreSpectrum} (D : DesuspensionData E) (n : Nat)
    (x : E.Space n) :
    Path (D.desusp n (E.structMap n x)) x :=
  D.desuspStruct n x

-- ============================================================================
-- § 13. LONG EXACT SEQUENCES IN STABLE HOMOTOPY
-- ============================================================================

/-- A triple of spectrum maps forming an exact sequence. -/
structure ExactTriple where
  specE : PreSpectrum
  specF : PreSpectrum
  specG : PreSpectrum
  f : SpectrumMap specE specF
  g : SpectrumMap specF specG
  exactness : (n : Nat) → (x : specE.Space n) →
    Path (g.mapLevel n (f.mapLevel n x)) (specG.point n)

/-- Theorem 23: Exactness at basepoint. -/
noncomputable def exact_at_base (T : ExactTriple) (n : Nat) :
    Path (T.g.mapLevel n (T.f.mapLevel n (T.specE.point n))) (T.specG.point n) :=
  T.exactness n (T.specE.point n)

/-- Connecting map data in a long exact sequence. -/
structure ConnectingMap (T : ExactTriple) where
  delta : (n : Nat) → T.specG.Space (n + 1) → T.specE.Space n
  deltaBase : (n : Nat) → Path (delta n (T.specG.point (n + 1))) (T.specE.point n)

/-- Theorem 24: Connecting map sends basepoint to basepoint. -/
noncomputable def connecting_base (T : ExactTriple) (C : ConnectingMap T) (n : Nat) :
    Path (C.delta n (T.specG.point (n + 1))) (T.specE.point n) :=
  C.deltaBase n

/-- Extended exact sequence: composing f with delta gives trivial. -/
structure ExtendedExactness (T : ExactTriple) (C : ConnectingMap T) where
  exactDeltaF : (n : Nat) → (x : T.specG.Space (n + 1)) →
    Path (T.f.mapLevel n (C.delta n x)) (T.specF.point n)

/-- Theorem 25: Extended exactness at delta-f composition. -/
noncomputable def extended_exact_delta_f
    (T : ExactTriple) (C : ConnectingMap T) (EE : ExtendedExactness T C)
    (n : Nat) (x : T.specG.Space (n + 1)) :
    Path (T.f.mapLevel n (C.delta n x)) (T.specF.point n) :=
  EE.exactDeltaF n x

-- ============================================================================
-- § 14. FUNCTORIALITY OF SPECTRUM CONSTRUCTIONS
-- ============================================================================

/-- Applying a function levelwise to paths in a spectrum. -/
noncomputable def spectrumCongrArg {E : PreSpectrum} {n : Nat}
    (f : E.Space n → E.Space n)
    {x y : E.Space n}
    (p : Path x y) : Path (f x) (f y) :=
  Path.congrArg f p

/-- Theorem 26: spectrumCongrArg preserves composition. -/
theorem spectrumCongrArg_trans {E : PreSpectrum} {n : Nat}
    (f : E.Space n → E.Space n)
    {x y z : E.Space n}
    (p : Path x y) (q : Path y z) :
    spectrumCongrArg f (Path.trans p q) =
    Path.trans (spectrumCongrArg f p) (spectrumCongrArg f q) :=
  congrArg_trans f p q

/-- Theorem 27: spectrumCongrArg preserves inverses. -/
theorem spectrumCongrArg_symm {E : PreSpectrum} {n : Nat}
    (f : E.Space n → E.Space n)
    {x y : E.Space n}
    (p : Path x y) :
    spectrumCongrArg f (Path.symm p) =
    Path.symm (spectrumCongrArg f p) :=
  congrArg_symm f p

/-- Theorem 28: Structure map is functorial on paths (trans). -/
theorem structMap_trans {E : PreSpectrum} {n : Nat}
    {x y z : E.Space n}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (E.structMap n) (Path.trans p q) =
    Path.trans (Path.congrArg (E.structMap n) p)
               (Path.congrArg (E.structMap n) q) :=
  congrArg_trans (E.structMap n) p q

/-- Theorem 29: Structure map is functorial on paths (symm). -/
theorem structMap_symm {E : PreSpectrum} {n : Nat}
    {x y : E.Space n}
    (p : Path x y) :
    Path.congrArg (E.structMap n) (Path.symm p) =
    Path.symm (Path.congrArg (E.structMap n) p) :=
  congrArg_symm (E.structMap n) p

-- ============================================================================
-- § 15. SPECTRUM MAP FUNCTORIALITY
-- ============================================================================

/-- Theorem 30: Spectrum map is functorial on paths (trans). -/
theorem specMap_path_trans {E F : PreSpectrum} (f : SpectrumMap E F)
    {n : Nat} {x y z : E.Space n}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (f.mapLevel n) (Path.trans p q) =
    Path.trans (Path.congrArg (f.mapLevel n) p)
               (Path.congrArg (f.mapLevel n) q) :=
  congrArg_trans (f.mapLevel n) p q

/-- Theorem 31: Spectrum map preserves inverse paths. -/
theorem specMap_path_symm {E F : PreSpectrum} (f : SpectrumMap E F)
    {n : Nat} {x y : E.Space n}
    (p : Path x y) :
    Path.congrArg (f.mapLevel n) (Path.symm p) =
    Path.symm (Path.congrArg (f.mapLevel n) p) :=
  congrArg_symm (f.mapLevel n) p

/-- Theorem 32: Composition of spectrum maps is associative on paths. -/
theorem specMap_comp_assoc {A B C D : PreSpectrum}
    (h : SpectrumMap C D) (g : SpectrumMap B C) (f : SpectrumMap A B)
    (n : Nat) (x : A.Space n) :
    (SpectrumMap.comp h (SpectrumMap.comp g f)).mapLevel n x =
    (SpectrumMap.comp (SpectrumMap.comp h g) f).mapLevel n x :=
  rfl

/-- Theorem 33: Identity map is left identity for composition. -/
theorem specMap_id_left {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat) (x : E.Space n) :
    (SpectrumMap.comp (SpectrumMap.idMap F) f).mapLevel n x =
    f.mapLevel n x :=
  rfl

/-- Theorem 34: Identity map is right identity for composition. -/
theorem specMap_id_right {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat) (x : E.Space n) :
    (SpectrumMap.comp f (SpectrumMap.idMap E)).mapLevel n x =
    f.mapLevel n x :=
  rfl

-- ============================================================================
-- § 16. PATH ALGEBRA IN SPECTRUM CONTEXT
-- ============================================================================

/-- Theorem 35: Pentagon-like coherence for four-fold loop composition. -/
theorem loop_four_assoc {E : PreSpectrum} {n : Nat}
    (p q r s : LoopAt E n) :
    LoopAt.compose (LoopAt.compose (LoopAt.compose p q) r) s =
    LoopAt.compose p (LoopAt.compose q (LoopAt.compose r s)) := by
  unfold LoopAt.compose
  rw [trans_assoc (Path.trans p q) r s]
  rw [trans_assoc p q (Path.trans r s)]

/-- Theorem 36: symm distributes over trans (reversed order). -/
theorem loop_inverse_compose {E : PreSpectrum} {n : Nat}
    (p q : LoopAt E n) :
    LoopAt.inverse (LoopAt.compose p q) =
    LoopAt.compose (LoopAt.inverse q) (LoopAt.inverse p) :=
  symm_trans p q

/-- Theorem 37: Symm of refl is refl. -/
theorem loop_inverse_trivial {E : PreSpectrum} {n : Nat} :
    LoopAt.inverse (LoopAt.trivial E n) = LoopAt.trivial E n :=
  symm_refl (E.point n)

-- ============================================================================
-- § 17. STABLE EQUIVALENCES
-- ============================================================================

/-- A stable equivalence between two spectra. -/
structure StableEquiv (E F : PreSpectrum) where
  forward : SpectrumMap E F
  backward : SpectrumMap F E
  rightInv : (n : Nat) → (x : F.Space n) →
    Path (forward.mapLevel n (backward.mapLevel n x)) x
  leftInv : (n : Nat) → (x : E.Space n) →
    Path (backward.mapLevel n (forward.mapLevel n x)) x

/-- Theorem 38: A stable equivalence gives path (right). -/
noncomputable def stable_equiv_right {E F : PreSpectrum}
    (e : StableEquiv E F) (n : Nat) (x : F.Space n) :
    Path (e.forward.mapLevel n (e.backward.mapLevel n x)) x :=
  e.rightInv n x

/-- Theorem 39: A stable equivalence gives path (left). -/
noncomputable def stable_equiv_left {E F : PreSpectrum}
    (e : StableEquiv E F) (n : Nat) (x : E.Space n) :
    Path (e.backward.mapLevel n (e.forward.mapLevel n x)) x :=
  e.leftInv n x

/-- Theorem 40: Identity is a stable equivalence. -/
noncomputable def StableEquiv.id (E : PreSpectrum) : StableEquiv E E where
  forward := SpectrumMap.idMap E
  backward := SpectrumMap.idMap E
  rightInv := fun _ x => Path.refl x
  leftInv := fun _ x => Path.refl x

/-- Theorem 41: Stable equivalence is symmetric. -/
noncomputable def StableEquiv.symm {E F : PreSpectrum}
    (e : StableEquiv E F) : StableEquiv F E where
  forward := e.backward
  backward := e.forward
  rightInv := e.leftInv
  leftInv := e.rightInv

-- ============================================================================
-- § 18. SHIFT AND TRUNCATION
-- ============================================================================

/-- Shift a spectrum by one level. -/
noncomputable def shiftSpectrum (E : PreSpectrum) : PreSpectrum where
  Space := fun n => E.Space (n + 1)
  point := fun n => E.point (n + 1)
  structMap := fun n => E.structMap (n + 1)
  structPoint := fun n => E.structPoint (n + 1)

/-- Theorem 42: Shift preserves the structure map path. -/
noncomputable def shift_structPoint (E : PreSpectrum) (n : Nat) :
    Path ((shiftSpectrum E).structMap n ((shiftSpectrum E).point n))
         ((shiftSpectrum E).point (n + 1)) :=
  E.structPoint (n + 1)

/-- The canonical map from E to its shift via structure maps. -/
noncomputable def toShift (E : PreSpectrum) : SpectrumMap E (shiftSpectrum E) where
  mapLevel := fun n => E.structMap n
  mapPoint := fun n => E.structPoint n
  mapCommute := fun n x => Path.refl (E.structMap (n + 1) (E.structMap n x))

/-- Theorem 43: toShift sends basepoint correctly. -/
noncomputable def toShift_base (E : PreSpectrum) (n : Nat) :
    Path ((toShift E).mapLevel n (E.point n))
         ((shiftSpectrum E).point n) :=
  E.structPoint n

/-- Theorem 44: Double shift space identity. -/
theorem double_shift_space (E : PreSpectrum) (n : Nat) :
    (shiftSpectrum (shiftSpectrum E)).Space n = E.Space (n + 2) :=
  rfl

-- ============================================================================
-- § 19. HIGHER PATH OPERATIONS IN SPECTRA
-- ============================================================================

/-- A 2-path (path between paths) at a spectrum level — equality of paths. -/
noncomputable def Path2At (_E : PreSpectrum) (_n : Nat) {A : Type}
    (p q : A) : Prop :=
  p = q

/-- Theorem 45: 2-paths are reflexive. -/
theorem path2_refl {E : PreSpectrum} {n : Nat} {x y : E.Space n}
    (p : Path x y) : Path2At E n p p :=
  rfl

/-- Theorem 46: 2-paths can be composed. -/
theorem path2_trans {E : PreSpectrum} {n : Nat} {x y : E.Space n}
    {p q r : Path x y}
    (alpha : Path2At E n p q) (beta : Path2At E n q r) : Path2At E n p r :=
  alpha.trans beta

/-- Theorem 47: 2-paths have inverses. -/
theorem path2_symm {E : PreSpectrum} {n : Nat} {x y : E.Space n}
    {p q : Path x y}
    (alpha : Path2At E n p q) : Path2At E n q p :=
  alpha.symm

/-- Theorem 48: Structure map lifts equalities of paths. -/
theorem structMap_path2 {E : PreSpectrum} {n : Nat} {x y : E.Space n}
    {p q : Path x y}
    (alpha : p = q) :
    Path.congrArg (E.structMap n) p =
    Path.congrArg (E.structMap n) q :=
  _root_.congrArg (Path.congrArg (E.structMap n)) alpha

-- ============================================================================
-- § 20. SPECTRUM MAP ON LOOPS
-- ============================================================================

/-- Theorem 49: Spectrum map on loops preserves composition. -/
theorem specMap_loop_compose {E F : PreSpectrum} (f : SpectrumMap E F)
    {n : Nat} (p q : LoopAt E n) :
    Path.congrArg (f.mapLevel n) (LoopAt.compose p q) =
    Path.trans (Path.congrArg (f.mapLevel n) p)
               (Path.congrArg (f.mapLevel n) q) :=
  congrArg_trans (f.mapLevel n) p q

/-- Theorem 50: Spectrum map on loops preserves inverses. -/
theorem specMap_loop_inverse {E F : PreSpectrum} (f : SpectrumMap E F)
    {n : Nat} (p : LoopAt E n) :
    Path.congrArg (f.mapLevel n) (LoopAt.inverse p) =
    Path.symm (Path.congrArg (f.mapLevel n) p) :=
  congrArg_symm (f.mapLevel n) p

-- ============================================================================
-- § 21. OMEGA-SPECTRUM ADJOINT FUNCTORIALITY
-- ============================================================================

/-- Theorem 51: Omega-spectrum adjoint is functorial on paths. -/
theorem omega_adjoint_trans {E : OmegaSpectrum} {n : Nat}
    {x y z : E.Space (n + 1)}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (E.adjoint n) (Path.trans p q) =
    Path.trans (Path.congrArg (E.adjoint n) p)
               (Path.congrArg (E.adjoint n) q) :=
  congrArg_trans (E.adjoint n) p q

/-- Theorem 52: Omega-spectrum adjoint preserves path inverses. -/
theorem omega_adjoint_symm {E : OmegaSpectrum} {n : Nat}
    {x y : E.Space (n + 1)}
    (p : Path x y) :
    Path.congrArg (E.adjoint n) (Path.symm p) =
    Path.symm (Path.congrArg (E.adjoint n) p) :=
  congrArg_symm (E.adjoint n) p

/-- Theorem 53: Omega adjoint preserves identity. -/
theorem omega_adjoint_refl {E : OmegaSpectrum} {n : Nat}
    (x : E.Space (n + 1)) :
    Path.congrArg (E.adjoint n) (Path.refl x) =
    Path.refl (E.adjoint n x) :=
  rfl

-- ============================================================================
-- § 22. EM SPECTRUM FUNCTORIALITY
-- ============================================================================

/-- Theorem 54: EM spectrum operation is functorial (left). -/
noncomputable def em_op_congrArg {D : EMSpectrumData} {n : Nat}
    {x y : D.KSpace n} (z : D.KSpace n)
    (p : Path x y) :
    Path (D.kop n x z) (D.kop n y z) :=
  Path.congrArg (fun w => D.kop n w z) p

/-- Theorem 55: EM spectrum operation is functorial (right). -/
noncomputable def em_op_congrArg_right {D : EMSpectrumData} {n : Nat}
    (x : D.KSpace n) {y z : D.KSpace n}
    (p : Path y z) :
    Path (D.kop n x y) (D.kop n x z) :=
  Path.congrArg (D.kop n x) p

/-- Theorem 56: EM operation functoriality preserves composition (left). -/
theorem em_op_trans_left {D : EMSpectrumData} {n : Nat}
    {x y z : D.KSpace n} (w : D.KSpace n)
    (p : Path x y) (q : Path y z) :
    Path.congrArg (fun v => D.kop n v w) (Path.trans p q) =
    Path.trans (Path.congrArg (fun v => D.kop n v w) p)
               (Path.congrArg (fun v => D.kop n v w) q) :=
  congrArg_trans (fun v => D.kop n v w) p q

/-- Theorem 57: EM operation functoriality preserves composition (right). -/
theorem em_op_trans_right {D : EMSpectrumData} {n : Nat}
    (x : D.KSpace n)
    {y z w : D.KSpace n}
    (p : Path y z) (q : Path z w) :
    Path.congrArg (D.kop n x) (Path.trans p q) =
    Path.trans (Path.congrArg (D.kop n x) p)
               (Path.congrArg (D.kop n x) q) :=
  congrArg_trans (D.kop n x) p q

/-- Theorem 58: EM operation symm (left). -/
theorem em_op_symm_left {D : EMSpectrumData} {n : Nat}
    {x y : D.KSpace n} (w : D.KSpace n)
    (p : Path x y) :
    Path.congrArg (fun v => D.kop n v w) (Path.symm p) =
    Path.symm (Path.congrArg (fun v => D.kop n v w) p) :=
  congrArg_symm (fun v => D.kop n v w) p

/-- Theorem 59: EM kstruct is functorial on paths. -/
theorem em_kstruct_trans {D : EMSpectrumData} {n : Nat}
    {x y z : D.KSpace n}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (D.kstruct n) (Path.trans p q) =
    Path.trans (Path.congrArg (D.kstruct n) p)
               (Path.congrArg (D.kstruct n) q) :=
  congrArg_trans (D.kstruct n) p q

-- ============================================================================
-- § 23. STABLE EQUIVALENCE COMPOSITION
-- ============================================================================

/-- Theorem 60: Stable equivalence composition at level. -/
theorem stable_equiv_comp_level {E F G : PreSpectrum}
    (e1 : StableEquiv E F) (e2 : StableEquiv F G)
    (n : Nat) (x : E.Space n) :
    (SpectrumMap.comp e2.forward e1.forward).mapLevel n x =
    e2.forward.mapLevel n (e1.forward.mapLevel n x) :=
  rfl

/-- Theorem 61: CongrArg composition law in spectrum context. -/
theorem spectrum_congrArg_comp {E : PreSpectrum} {n : Nat}
    {f : E.Space n → E.Space n} {g : E.Space n → E.Space n}
    {x y : E.Space n} (p : Path x y) :
    Path.congrArg (fun z => f (g z)) p =
    Path.congrArg f (Path.congrArg g p) :=
  congrArg_comp f g p

/-- Theorem 62: CongrArg identity is identity in spectrum context. -/
theorem spectrum_congrArg_id {E : PreSpectrum} {n : Nat}
    {x y : E.Space n} (p : Path x y) :
    Path.congrArg (fun z : E.Space n => z) p = p :=
  congrArg_id p

-- ============================================================================
-- § 24. WEDGE SPECTRUM
-- ============================================================================

/-- Wedge (coproduct) of two spectra. -/
noncomputable def wedgeSpectrum
    (wedge : Nat → Type)
    (wpt : (n : Nat) → wedge n)
    (wstruct : (n : Nat) → wedge n → wedge (n + 1))
    (wstructBase : (n : Nat) → Path (wstruct n (wpt n)) (wpt (n + 1))) :
    PreSpectrum where
  Space := wedge
  point := wpt
  structMap := wstruct
  structPoint := wstructBase

/-- Wedge inclusion data. -/
structure WedgeInclusion (E : PreSpectrum) (W : PreSpectrum) where
  incl : (n : Nat) → E.Space n → W.Space n
  inclBase : (n : Nat) → Path (incl n (E.point n)) (W.point n)

/-- Theorem 63: Wedge inclusion sends basepoint to basepoint. -/
noncomputable def wedge_incl_base {E W : PreSpectrum}
    (i : WedgeInclusion E W) (n : Nat) :
    Path (i.incl n (E.point n)) (W.point n) :=
  i.inclBase n

-- ============================================================================
-- § 25. CONNECTING MAP FUNCTORIALITY
-- ============================================================================

/-- Theorem 64: Connecting map is functorial on paths. -/
theorem connecting_map_trans {T : ExactTriple} {C : ConnectingMap T}
    {n : Nat} {x y z : T.specG.Space (n + 1)}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (C.delta n) (Path.trans p q) =
    Path.trans (Path.congrArg (C.delta n) p)
               (Path.congrArg (C.delta n) q) :=
  congrArg_trans (C.delta n) p q

/-- Theorem 65: Connecting map preserves path inverses. -/
theorem connecting_map_symm {T : ExactTriple} {C : ConnectingMap T}
    {n : Nat} {x y : T.specG.Space (n + 1)}
    (p : Path x y) :
    Path.congrArg (C.delta n) (Path.symm p) =
    Path.symm (Path.congrArg (C.delta n) p) :=
  congrArg_symm (C.delta n) p

-- ============================================================================
-- § 26. FIBER PATH ALGEBRA
-- ============================================================================

/-- Theorem 66: Fiber path symm-trans law. -/
theorem fiberPath_overPath_refl {E F : PreSpectrum} {f : SpectrumMap E F} {n : Nat}
    (a : SpectrumFiber f n) :
    (FiberPath.refl a).overPath = trans_refl_left a.witness :=
  rfl

-- ============================================================================
-- § 27. SMASH SPECTRUM FUNCTORIALITY
-- ============================================================================

/-- Theorem 67: Smash structure map is functorial on paths. -/
theorem smash_struct_trans {E F : PreSpectrum} (S : SmashSpectrum E F)
    {n : Nat} {x y z : S.SmSpace n}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (S.smStruct n) (Path.trans p q) =
    Path.trans (Path.congrArg (S.smStruct n) p)
               (Path.congrArg (S.smStruct n) q) :=
  congrArg_trans (S.smStruct n) p q

/-- Theorem 68: Smash structure map preserves symm. -/
theorem smash_struct_symm {E F : PreSpectrum} (S : SmashSpectrum E F)
    {n : Nat} {x y : S.SmSpace n}
    (p : Path x y) :
    Path.congrArg (S.smStruct n) (Path.symm p) =
    Path.symm (Path.congrArg (S.smStruct n) p) :=
  congrArg_symm (S.smStruct n) p

-- ============================================================================
-- § 28. DESUSPENSION FUNCTORIALITY
-- ============================================================================

/-- Theorem 69: Desuspension is functorial on paths (trans). -/
theorem desusp_trans {E : PreSpectrum} (D : DesuspensionData E)
    {n : Nat} {x y z : E.Space (n + 1)}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (D.desusp n) (Path.trans p q) =
    Path.trans (Path.congrArg (D.desusp n) p)
               (Path.congrArg (D.desusp n) q) :=
  congrArg_trans (D.desusp n) p q

/-- Theorem 70: Desuspension preserves symm. -/
theorem desusp_symm {E : PreSpectrum} (D : DesuspensionData E)
    {n : Nat} {x y : E.Space (n + 1)}
    (p : Path x y) :
    Path.congrArg (D.desusp n) (Path.symm p) =
    Path.symm (Path.congrArg (D.desusp n) p) :=
  congrArg_symm (D.desusp n) p

-- ============================================================================
-- § 29. SPECTRUM MAPS PRESERVE LOOP STRUCTURE
-- ============================================================================

/-- A spectrum map induces a group homomorphism on loops. -/
noncomputable def specMapOnLoops {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat)
    (p : LoopAt E n) : Path (f.mapLevel n (E.point n)) (f.mapLevel n (E.point n)) :=
  Path.congrArg (f.mapLevel n) p

/-- Theorem 71: specMapOnLoops preserves trivial loop. -/
theorem specMapOnLoops_trivial {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat) :
    specMapOnLoops f n (LoopAt.trivial E n) =
    Path.refl (f.mapLevel n (E.point n)) :=
  rfl

/-- Theorem 72: specMapOnLoops preserves composition. -/
theorem specMapOnLoops_compose {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat)
    (p q : LoopAt E n) :
    specMapOnLoops f n (LoopAt.compose p q) =
    Path.trans (specMapOnLoops f n p) (specMapOnLoops f n q) :=
  congrArg_trans (f.mapLevel n) p q

/-- Theorem 73: specMapOnLoops preserves inverse. -/
theorem specMapOnLoops_inverse {E F : PreSpectrum} (f : SpectrumMap E F) (n : Nat)
    (p : LoopAt E n) :
    specMapOnLoops f n (LoopAt.inverse p) =
    Path.symm (specMapOnLoops f n p) :=
  congrArg_symm (f.mapLevel n) p

-- ============================================================================
-- § 30. NATURALITY OF SUSPENSION HOMOMORPHISM
-- ============================================================================

/-- Conjugated loop: transport a loop at level n to a loop at level n+1
    using the structure path. -/
noncomputable def conjugatedLoop {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    Path (E.structMap n (E.point n)) (E.structMap n (E.point n)) :=
  Path.congrArg (E.structMap n) p

/-- Theorem 74: Conjugated loop preserves composition. -/
theorem conjugatedLoop_compose {E : PreSpectrum} {n : Nat}
    (p q : LoopAt E n) :
    conjugatedLoop (LoopAt.compose p q) =
    Path.trans (conjugatedLoop p) (conjugatedLoop q) :=
  congrArg_trans (E.structMap n) p q

/-- Theorem 75: Conjugated loop preserves inverse. -/
theorem conjugatedLoop_inverse {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    conjugatedLoop (LoopAt.inverse p) =
    Path.symm (conjugatedLoop p) :=
  congrArg_symm (E.structMap n) p

-- ============================================================================
-- § 31. TRANSPORT IN SPECTRA
-- ============================================================================

/-- Transport along a path in a spectrum level. -/
noncomputable def spectrumTransport {E : PreSpectrum} {n : Nat}
    {x y : E.Space n}
    (p : Path x y) : x = y :=
  p.toEq

/-- Theorem 76: Spectrum transport along refl is rfl. -/
theorem spectrumTransport_refl {E : PreSpectrum} {n : Nat}
    (x : E.Space n) :
    spectrumTransport (Path.refl x) = rfl :=
  rfl

/-- Theorem 77: Spectrum transport along trans is composition. -/
theorem spectrumTransport_trans {E : PreSpectrum} {n : Nat}
    {x y z : E.Space n}
    (p : Path x y) (q : Path y z) :
    spectrumTransport (Path.trans p q) =
    (spectrumTransport p).trans (spectrumTransport q) :=
  rfl

-- ============================================================================
-- § 32. ADDITIONAL COHERENCE
-- ============================================================================

/-- Theorem 78: congrArg through structure map then adjoint. -/
theorem struct_adjoint_congrArg {E : OmegaSpectrum} {n : Nat}
    {x y : E.Space n}
    (p : Path x y) :
    Path.congrArg (fun z => E.adjoint n (E.structMap n z)) p =
    Path.congrArg (E.adjoint n) (Path.congrArg (E.structMap n) p) :=
  congrArg_comp (E.adjoint n) (E.structMap n) p

/-- Theorem 79: congrArg through adjoint then structure map. -/
theorem adjoint_struct_congrArg {E : OmegaSpectrum} {n : Nat}
    {x y : E.Space (n + 1)}
    (p : Path x y) :
    Path.congrArg (fun z => E.structMap n (E.adjoint n z)) p =
    Path.congrArg (E.structMap n) (Path.congrArg (E.adjoint n) p) :=
  congrArg_comp (E.structMap n) (E.adjoint n) p

/-- Theorem 80: congrArg id on loop is identity. -/
theorem loop_congrArg_id {E : PreSpectrum} {n : Nat}
    (p : LoopAt E n) :
    Path.congrArg (fun x : E.Space n => x) p = p :=
  congrArg_id p

end ComputationalPaths.Spectra
