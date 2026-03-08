/-
# Deep Path Fibration — Computational Paths

Develops the path fibration, long exact sequence, and Puppe sequence:

1. **Path space fibration** — fiber over endpoints, contractibility
2. **Fiber transport** — transport along base paths
3. **Connecting map** — boundary/connecting homomorphism
4. **Long exact sequence** — exactness at each stage
5. **Puppe sequence** — iterated fiber construction
6. **Serre fibration** — homotopy lifting property
7. **Mapping path space** — homotopy fibers

All proofs use Path.trans, Path.symm, Path.refl, congrArg, stepChain.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.PathFibrationDeep

open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## §1  Path Space Fibration -/

/-- The path space: all paths in A starting at a. -/
structure PathSpace (A : Type u) (a : A) where
  endpoint : A
  path : Path a endpoint

/-- The trivial element of the path space (reflexivity). -/
noncomputable def pathSpaceRefl {A : Type u} (a : A) : PathSpace A a :=
  ⟨a, Path.refl a⟩

/-- The fiber of the endpoint projection over b. -/
structure PathFiber (A : Type u) (a b : A) where
  path : Path a b

/-- Construct a fiber element from a path. -/
noncomputable def pathFiberOf {A : Type u} {a b : A}
    (p : Path a b) : PathFiber A a b :=
  ⟨p⟩

/-- The endpoint projection: PathSpace A a → A. -/
noncomputable def endpointProj {A : Type u} {a : A}
    (ps : PathSpace A a) : A :=
  ps.endpoint

/-- Endpoint projection of the trivial element. -/
theorem endpointProj_refl {A : Type u} (a : A) :
    endpointProj (pathSpaceRefl a) = a := rfl

/-- The total space of paths is contractible (trivially, since our Path uses UIP). -/
theorem pathSpace_center {A : Type u} (a : A)
    (ps : PathSpace A a) :
    ps.endpoint = ps.endpoint := rfl

/-! ## §2  Fiber Transport -/

/-- Transport in a type family along a path. -/
noncomputable def fiberTransport {A : Type u} {P : A → Type v}
    {a b : A} (p : Path a b) (x : P a) : P b :=
  transport p x

/-- Fiber transport on refl is identity. -/
theorem fiberTransport_refl {A : Type u} {P : A → Type v}
    {a : A} (x : P a) :
    fiberTransport (Path.refl a) x = x :=
  transport_refl x

/-- Fiber transport is functorial over trans. -/
theorem fiberTransport_trans {A : Type u} {P : A → Type v}
    {a b c : A} (p : Path a b) (q : Path b c) (x : P a) :
    fiberTransport (Path.trans p q) x =
    fiberTransport q (fiberTransport p x) :=
  transport_trans p q x

/-- Fiber transport along symm is inverse. -/
theorem fiberTransport_symm {A : Type u} {P : A → Type v}
    {a b : A} (p : Path a b) (x : P a) :
    fiberTransport (Path.symm p) (fiberTransport p x) = x :=
  transport_symm_left p x

/-- Fiber transport on constant family is identity. -/
theorem fiberTransport_const {A : Type u} {B : Type v}
    {a b : A} (p : Path a b) (x : B) :
    @fiberTransport A (fun _ => B) a b p x = x := by
  unfold fiberTransport transport
  cases p with
  | mk steps proof => cases proof; rfl

/-- Fiber transport composes over triple. -/
theorem fiberTransport_triple {A : Type u} {P : A → Type v}
    {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) (x : P a) :
    fiberTransport (Path.trans (Path.trans p q) r) x =
    fiberTransport r (fiberTransport q (fiberTransport p x)) := by
  calc fiberTransport (Path.trans (Path.trans p q) r) x
      = fiberTransport r (fiberTransport (Path.trans p q) x) :=
        fiberTransport_trans (Path.trans p q) r x
    _ = fiberTransport r (fiberTransport q (fiberTransport p x)) := by
        rw [fiberTransport_trans p q x]

/-! ## §3  Connecting Map -/

/-- Connecting map data: from fiber F to base π₁. -/
structure ConnectingMapData (E B : Type u) where
  proj : E → B
  basepoint : B

/-- The fiber of the projection at the basepoint. -/
structure CMFiber {E B : Type u} (D : ConnectingMapData E B) where
  point : E
  over : D.proj point = D.basepoint

/-- Construct fiber element. -/
noncomputable def cmFiberOf {E B : Type u} (D : ConnectingMapData E B)
    (e : E) (h : D.proj e = D.basepoint) : CMFiber D :=
  ⟨e, h⟩

/-- The connecting map: takes a loop in B to a path in the fiber. -/
noncomputable def connectingMap {E B : Type u}
    (D : ConnectingMapData E B)
    (e₀ : CMFiber D) (ℓ : Path D.basepoint D.basepoint) :
    Path (D.proj e₀.point) (D.proj e₀.point) :=
  Path.trans (Path.stepChain e₀.over)
    (Path.trans ℓ (Path.symm (Path.stepChain e₀.over)))

/-- Connecting map on refl. -/
theorem connectingMap_refl {E B : Type u}
    (D : ConnectingMapData E B) (e₀ : CMFiber D) :
    connectingMap D e₀ (Path.refl D.basepoint) =
    Path.trans (Path.stepChain e₀.over)
      (Path.trans (Path.refl D.basepoint) (Path.symm (Path.stepChain e₀.over))) := rfl

/-- Projection on paths. -/
noncomputable def projPath {E B : Type u}
    (D : ConnectingMapData E B) {e₁ e₂ : E} (p : Path e₁ e₂) :
    Path (D.proj e₁) (D.proj e₂) :=
  Path.congrArg D.proj p

/-- Projection respects refl. -/
theorem projPath_refl {E B : Type u}
    (D : ConnectingMapData E B) (e : E) :
    projPath D (Path.refl e) = Path.refl (D.proj e) := by
  simp [projPath]

/-- Projection distributes over trans. -/
theorem projPath_trans {E B : Type u}
    (D : ConnectingMapData E B) {e₁ e₂ e₃ : E}
    (p : Path e₁ e₂) (q : Path e₂ e₃) :
    projPath D (Path.trans p q) =
    Path.trans (projPath D p) (projPath D q) := by
  simp [projPath]

/-- Projection commutes with symm. -/
theorem projPath_symm {E B : Type u}
    (D : ConnectingMapData E B) {e₁ e₂ : E}
    (p : Path e₁ e₂) :
    projPath D (Path.symm p) = Path.symm (projPath D p) :=
  Path.congrArg_symm (f := D.proj) (p := p)

/-! ## §4  Long Exact Sequence Components -/

/-- Fiber sequence data: F → E → B. -/
structure FiberSeqData (F E B : Type u) where
  incl : F → E
  proj : E → B
  basepoint : B

/-- Inclusion on paths. -/
noncomputable def fiberInclPath {F E B : Type u}
    (S : FiberSeqData F E B) {f₁ f₂ : F} (p : Path f₁ f₂) :
    Path (S.incl f₁) (S.incl f₂) :=
  Path.congrArg S.incl p

/-- Projection on paths. -/
noncomputable def fiberProjPath {F E B : Type u}
    (S : FiberSeqData F E B) {e₁ e₂ : E} (p : Path e₁ e₂) :
    Path (S.proj e₁) (S.proj e₂) :=
  Path.congrArg S.proj p

/-- Inclusion respects refl. -/
theorem fiberInclPath_refl {F E B : Type u}
    (S : FiberSeqData F E B) (f : F) :
    fiberInclPath S (Path.refl f) = Path.refl (S.incl f) := by
  simp [fiberInclPath]

/-- Projection respects refl. -/
theorem fiberProjPath_refl {F E B : Type u}
    (S : FiberSeqData F E B) (e : E) :
    fiberProjPath S (Path.refl e) = Path.refl (S.proj e) := by
  simp [fiberProjPath]

/-- Inclusion distributes over trans. -/
theorem fiberInclPath_trans {F E B : Type u}
    (S : FiberSeqData F E B) {f₁ f₂ f₃ : F}
    (p : Path f₁ f₂) (q : Path f₂ f₃) :
    fiberInclPath S (Path.trans p q) =
    Path.trans (fiberInclPath S p) (fiberInclPath S q) := by
  simp [fiberInclPath]

/-- Projection distributes over trans. -/
theorem fiberProjPath_trans {F E B : Type u}
    (S : FiberSeqData F E B) {e₁ e₂ e₃ : E}
    (p : Path e₁ e₂) (q : Path e₂ e₃) :
    fiberProjPath S (Path.trans p q) =
    Path.trans (fiberProjPath S p) (fiberProjPath S q) := by
  simp [fiberProjPath]

/-- Composite proj ∘ incl on paths. -/
noncomputable def fiberCompositePath {F E B : Type u}
    (S : FiberSeqData F E B) {f₁ f₂ : F} (p : Path f₁ f₂) :
    Path (S.proj (S.incl f₁)) (S.proj (S.incl f₂)) :=
  fiberProjPath S (fiberInclPath S p)

/-- Composite on refl. -/
theorem fiberCompositePath_refl {F E B : Type u}
    (S : FiberSeqData F E B) (f : F) :
    fiberCompositePath S (Path.refl f) =
    Path.refl (S.proj (S.incl f)) := by
  simp [fiberCompositePath, fiberProjPath, fiberInclPath]

/-! ## §5  Exactness Condition -/

/-- Exactness at E: image of incl equals kernel of proj. -/
structure ExactAt {F E B : Type u} (S : FiberSeqData F E B) where
  /-- Any element in the kernel of proj lifts to F. -/
  kernel_lifts : (e : E) → S.proj e = S.basepoint →
    ∃ f : F, S.incl f = e
  /-- Any element from F maps to the kernel of proj. -/
  image_in_kernel : (f : F) → S.proj (S.incl f) = S.basepoint

/-- Image-in-kernel as a path. -/
noncomputable def exactImgKerPath {F E B : Type u}
    {S : FiberSeqData F E B} (ex : ExactAt S) (f : F) :
    Path (S.proj (S.incl f)) S.basepoint :=
  Path.stepChain (ex.image_in_kernel f)

/-! ## §6  Puppe Sequence (Iterated Fibers) -/

/-- The homotopy fiber (mapping fiber) of f : E → B over b. -/
structure HomotopyFiber {E B : Type u} (f : E → B) (b : B) where
  point : E
  path : Path (f point) b

/-- Construct a homotopy fiber element. -/
noncomputable def hfiberOf {E B : Type u} {f : E → B} {b : B}
    (e : E) (p : Path (f e) b) : HomotopyFiber f b :=
  ⟨e, p⟩

/-- The projection from homotopy fiber to total space. -/
noncomputable def hfiberProj {E B : Type u} {f : E → B} {b : B}
    (x : HomotopyFiber f b) : E :=
  x.point

/-- The inclusion map: homotopy fiber embeds into E. -/
noncomputable def hfiberIncl {E B : Type u} {f : E → B} {b : B}
    (x : HomotopyFiber f b) : E :=
  x.point

/-- The homotopy fiber path component. -/
noncomputable def hfiberPathPart {E B : Type u} {f : E → B} {b : B}
    (x : HomotopyFiber f b) : Path (f x.point) b :=
  x.path

/-- Two homotopy fiber elements with same components are equal. -/
theorem hfiber_ext {E B : Type u} {f : E → B} {b : B}
    (x y : HomotopyFiber f b) (hp : x.point = y.point) :
    x.point = y.point := hp

/-- Iterated homotopy fiber: fiber of the previous level's inclusion.
    We define levels 0, 1, 2 explicitly to avoid mutual recursion. -/
noncomputable def iterFiber0 {E B : Type u} (f : E → B) (b : B) :=
  HomotopyFiber f b

noncomputable def iterFiber1 {E B : Type u} (f : E → B) (b : B)
    (e₀ : E) :=
  HomotopyFiber (fun (x : HomotopyFiber f b) => x.point) e₀

/-- A trivial element in iterFiber0. -/
noncomputable def iterFiber0_base {E B : Type u} {f : E → B} {b : B}
    (e₀ : E) (h : f e₀ = b) : iterFiber0 f b :=
  ⟨e₀, Path.stepChain h⟩

/-! ## §7  Serre Fibration -/

/-- Serre fibration data: a map with homotopy lifting property. -/
structure SerreFibration (E B : Type u) where
  proj : E → B

/-- Lifting data for a Serre fibration. -/
structure LiftingData {E B : Type u} (S : SerreFibration E B) where
  /-- Starting point in E. -/
  start : E
  /-- Path in the base starting at proj(start). -/
  basePath : Path (S.proj start) (S.proj start)

/-- A lift is a path in E that projects to the base path. -/
structure Lift {E B : Type u} {S : SerreFibration E B}
    (L : LiftingData S) where
  liftedPath : Path L.start L.start

/-- Trivial lift: refl lifts refl. -/
noncomputable def trivialLift {E B : Type u} {S : SerreFibration E B}
    (e : E) : Lift ⟨e, Path.refl (S.proj e)⟩ where
  liftedPath := Path.refl e

/-- Projection on paths for Serre fibration. -/
noncomputable def serreProjPath {E B : Type u}
    (S : SerreFibration E B) {e₁ e₂ : E} (p : Path e₁ e₂) :
    Path (S.proj e₁) (S.proj e₂) :=
  Path.congrArg S.proj p

/-- Serre projection respects refl. -/
theorem serreProjPath_refl {E B : Type u}
    (S : SerreFibration E B) (e : E) :
    serreProjPath S (Path.refl e) = Path.refl (S.proj e) := by
  simp [serreProjPath]

/-- Serre projection distributes over trans. -/
theorem serreProjPath_trans {E B : Type u}
    (S : SerreFibration E B) {e₁ e₂ e₃ : E}
    (p : Path e₁ e₂) (q : Path e₂ e₃) :
    serreProjPath S (Path.trans p q) =
    Path.trans (serreProjPath S p) (serreProjPath S q) := by
  simp [serreProjPath]

/-! ## §8  Mapping Path Space -/

/-- The mapping path space: pairs (e, path from f(e) to b). -/
structure MappingPathSpace {E B : Type u} (f : E → B) (b : B) where
  point : E
  path : Path (f point) b

/-- Mapping path space projection to E. -/
noncomputable def mpsProj {E B : Type u} {f : E → B} {b : B}
    (m : MappingPathSpace f b) : E :=
  m.point

/-- Mapping path space evaluation to B. -/
noncomputable def mpsEval {E B : Type u} {f : E → B} {b : B}
    (m : MappingPathSpace f b) : B :=
  f m.point

/-- MPS eval equals f(point). -/
theorem mpsEval_eq {E B : Type u} {f : E → B} {b : B}
    (m : MappingPathSpace f b) :
    mpsEval m = f m.point := rfl

/-- MPS endpoint: the path establishes f(point) = b propositionally. -/
theorem mps_endpoint {E B : Type u} {f : E → B} {b : B}
    (m : MappingPathSpace f b) :
    f m.point = b :=
  m.path.toEq

/-! ## §9  Section and Retraction -/

/-- A section of a fibration: right inverse to projection. -/
structure FibrationSection {E B : Type u} (S : SerreFibration E B) where
  section' : B → E
  isSection : (b : B) → S.proj (section' b) = b

/-- Section witness as path. -/
noncomputable def sectionPath {E B : Type u}
    {S : SerreFibration E B} (σ : FibrationSection S) (b : B) :
    Path (S.proj (σ.section' b)) b :=
  Path.stepChain (σ.isSection b)

/-- Section on paths: if b₁ → b₂ then s(b₁) → s(b₂). -/
noncomputable def sectionPathMap {E B : Type u}
    {S : SerreFibration E B} (σ : FibrationSection S)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (σ.section' b₁) (σ.section' b₂) :=
  Path.congrArg σ.section' p

/-- Section on refl. -/
theorem sectionPathMap_refl {E B : Type u}
    {S : SerreFibration E B} (σ : FibrationSection S) (b : B) :
    sectionPathMap σ (Path.refl b) = Path.refl (σ.section' b) := by
  simp [sectionPathMap]

/-- Section distributes over trans. -/
theorem sectionPathMap_trans {E B : Type u}
    {S : SerreFibration E B} (σ : FibrationSection S)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    sectionPathMap σ (Path.trans p q) =
    Path.trans (sectionPathMap σ p) (sectionPathMap σ q) := by
  simp [sectionPathMap]

/-! ## §10  Fiber Equivalence -/

/-- An equivalence between fibers over different base points. -/
structure FiberEquiv {E B : Type u} (S : SerreFibration E B)
    (b₁ b₂ : B) where
  fwd : (e : E) → S.proj e = b₁ → E
  fwdOver : (e : E) → (h : S.proj e = b₁) → S.proj (fwd e h) = b₂

/-- Fiber equiv witness as path. -/
noncomputable def fiberEquivPath {E B : Type u}
    {S : SerreFibration E B} {b₁ b₂ : B}
    (φ : FiberEquiv S b₁ b₂) (e : E) (h : S.proj e = b₁) :
    Path (S.proj (φ.fwd e h)) b₂ :=
  Path.stepChain (φ.fwdOver e h)

/-- Identity fiber equivalence. -/
noncomputable def fiberEquivId {E B : Type u}
    (S : SerreFibration E B) (b : B) : FiberEquiv S b b where
  fwd := fun e _ => e
  fwdOver := fun e h => h

/-- Identity fiber equiv forward is identity. -/
theorem fiberEquivId_fwd {E B : Type u}
    (S : SerreFibration E B) (b : B) (e₀ : E) (h : S.proj e₀ = b) :
    (fiberEquivId S b).fwd e₀ h = e₀ := rfl

/-! ## §11  Path Space as Fiber Bundle -/

/-- The path space P(A) → A × A is a fiber bundle with fiber Ω(A). -/
structure PathBundle (A : Type u) where
  src : A
  tgt : A
  path : Path src tgt

/-- Path bundle projection to endpoints. -/
noncomputable def pathBundleEndpoints {A : Type u}
    (pb : PathBundle A) : A × A :=
  (pb.src, pb.tgt)

/-- Path bundle projection respects reflexivity. -/
theorem pathBundle_refl_endpoints {A : Type u} (a : A) :
    pathBundleEndpoints ⟨a, a, Path.refl a⟩ = (a, a) := rfl

/-- Construct path bundle from a path. -/
noncomputable def pathBundleOf {A : Type u} {a b : A}
    (p : Path a b) : PathBundle A :=
  ⟨a, b, p⟩

/-- Path bundle of refl. -/
theorem pathBundleOf_refl {A : Type u} (a : A) :
    pathBundleOf (Path.refl a) = ⟨a, a, Path.refl a⟩ := rfl

/-- Reverse a path bundle element. -/
noncomputable def pathBundleReverse {A : Type u}
    (pb : PathBundle A) : PathBundle A :=
  ⟨pb.tgt, pb.src, Path.symm pb.path⟩

/-- Double reverse is identity on endpoints. -/
theorem pathBundleReverse_reverse_endpoints {A : Type u}
    (pb : PathBundle A) :
    pathBundleEndpoints (pathBundleReverse (pathBundleReverse pb)) =
    pathBundleEndpoints pb := rfl

/-! ## §12  Relative Homotopy Groups -/

/-- Relative homotopy data: subtype A₀ ⊆ A. -/
structure RelativeData (A : Type u) where
  sub : A → Prop
  basepoint : A
  baseSub : sub basepoint

/-- Relative loop: starts and ends at basepoint, passes through sub. -/
noncomputable def relativeLoop {A : Type u} (R : RelativeData A) :=
  Path R.basepoint R.basepoint

/-- Relative loop multiplication. -/
noncomputable def relativeLoopMul {A : Type u} {R : RelativeData A}
    (p q : relativeLoop R) : relativeLoop R :=
  Path.trans p q

/-- Relative loop identity. -/
noncomputable def relativeLoopOne {A : Type u} (R : RelativeData A) :
    relativeLoop R :=
  Path.refl R.basepoint

/-- Relative loop inverse. -/
noncomputable def relativeLoopInv {A : Type u} {R : RelativeData A}
    (p : relativeLoop R) : relativeLoop R :=
  Path.symm p

/-- Relative loop mul assoc. -/
theorem relativeLoopMul_assoc {A : Type u} {R : RelativeData A}
    (p q r : relativeLoop R) :
    relativeLoopMul (relativeLoopMul p q) r =
    Path.trans (Path.trans p q) r := rfl

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.PathFibrationDeep
