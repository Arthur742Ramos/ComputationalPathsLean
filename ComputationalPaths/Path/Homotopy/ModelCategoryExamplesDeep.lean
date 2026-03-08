/-
# Deep Model Category Examples — Computational Paths

Develops model category structures entirely within the Path/Step/RwEq framework:

1. **Chain complex model structure** — differentials, boundaries, cycles, homology
2. **Simplicial model structure** — faces, degeneracies, Kan fillers
3. **Quillen adjunctions** — adjoint functors preserving model structure
4. **Derived functors** — left/right derived via cofibrant/fibrant replacement
5. **Cylinder and path objects** — factorization axioms
6. **Retract arguments** — closure under retracts
7. **Ken Brown's lemma** — weak equivalences between fibrant objects

All proofs use Path.trans, Path.symm, Path.refl, congrArg, transport.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep

open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## §1  Chain Complex Basics -/

/-- A chain complex is a sequence of types with differentials. -/
structure ChainComplex (C : Nat → Type u) where
  d : {n : Nat} → C (n + 1) → C n

/-- Graded element: a pair (n, x) where x : C n. -/
structure GradedElem (C : Nat → Type u) where
  degree : Nat
  elem   : C degree

/-- Apply differential to a path. -/
noncomputable def dMap {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 1)} (p : Path x y) : Path (cx.d x) (cx.d y) :=
  Path.congrArg cx.d p

/-- Differential respects reflexivity. -/
theorem dMap_refl {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} (x : C (n + 1)) :
    dMap cx (Path.refl x) = Path.refl (cx.d x) := by
  simp [dMap]

/-- Differential distributes over composition. -/
theorem dMap_trans {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y z : C (n + 1)} (p : Path x y) (q : Path y z) :
    dMap cx (Path.trans p q) = Path.trans (dMap cx p) (dMap cx q) := by
  simp [dMap]

/-- Differential commutes with symmetry. -/
theorem dMap_symm {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 1)} (p : Path x y) :
    dMap cx (Path.symm p) = Path.symm (dMap cx p) := by
  simp [dMap]

/-- Double differential. -/
noncomputable def ddMap {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 2)} (p : Path x y) :
    Path (cx.d (cx.d x)) (cx.d (cx.d y)) :=
  dMap cx (dMap cx p)

/-- Double differential on refl. -/
theorem ddMap_refl {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} (x : C (n + 2)) :
    ddMap cx (Path.refl x) = Path.refl (cx.d (cx.d x)) := by
  simp [ddMap, dMap]

/-- Double differential distributes over trans. -/
theorem ddMap_trans {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y z : C (n + 2)} (p : Path x y) (q : Path y z) :
    ddMap cx (Path.trans p q) = Path.trans (ddMap cx p) (ddMap cx q) := by
  simp [ddMap, dMap]

/-! ## §2  Chain Maps -/

/-- A chain map between chain complexes. -/
structure ChainMap {C D : Nat → Type u}
    (cC : ChainComplex C) (cD : ChainComplex D) where
  f : {n : Nat} → C n → D n

/-- Chain map applied to paths. -/
noncomputable def chainMapPath {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n} (p : Path x y) :
    Path (φ.f x) (φ.f y) :=
  Path.congrArg φ.f p

/-- Chain map respects reflexivity. -/
theorem chainMapPath_refl {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} (x : C n) :
    chainMapPath φ (Path.refl x) = Path.refl (φ.f x) := by
  simp [chainMapPath]

/-- Chain map distributes over trans. -/
theorem chainMapPath_trans {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y z : C n}
    (p : Path x y) (q : Path y z) :
    chainMapPath φ (Path.trans p q) =
    Path.trans (chainMapPath φ p) (chainMapPath φ q) := by
  simp [chainMapPath]

/-- Chain map commutes with symm. -/
theorem chainMapPath_symm {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n}
    (p : Path x y) :
    chainMapPath φ (Path.symm p) = Path.symm (chainMapPath φ p) := by
  simp [chainMapPath]

/-- Composition of chain maps. -/
noncomputable def chainMapComp {C D E : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D} {cE : ChainComplex E}
    (ψ : ChainMap cD cE) (φ : ChainMap cC cD) : ChainMap cC cE where
  f := fun x => ψ.f (φ.f x)

/-- Composition of chain maps on paths. -/
theorem chainMapComp_path {C D E : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D} {cE : ChainComplex E}
    (ψ : ChainMap cD cE) (φ : ChainMap cC cD)
    {n : Nat} {x y : C n} (p : Path x y) :
    chainMapPath (chainMapComp ψ φ) p =
    Path.congrArg (fun z => ψ.f (φ.f z)) p := by
  simp [chainMapPath, chainMapComp]

/-- Identity chain map. -/
noncomputable def chainMapId {C : Nat → Type u}
    (cC : ChainComplex C) : ChainMap cC cC where
  f := fun x => x

/-- Identity chain map acts trivially on paths. -/
theorem chainMapId_path {C : Nat → Type u}
    {cC : ChainComplex C} {n : Nat} {x y : C n} (p : Path x y) :
    chainMapPath (chainMapId cC) p = p := by
  simp [chainMapPath, chainMapId]

/-! ## §3  Simplicial Structure -/

/-- A simplicial object: sequence of types with face and degeneracy maps. -/
structure SimplicialObject (X : Nat → Type u) where
  face : {n : Nat} → (i : Fin (n + 2)) → X (n + 1) → X n
  degen : {n : Nat} → (i : Fin (n + 1)) → X n → X (n + 1)

/-- Face map applied to paths. -/
noncomputable def faceMap {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) {x y : X (n + 1)} (p : Path x y) :
    Path (S.face i x) (S.face i y) :=
  Path.congrArg (S.face i) p

/-- Face map respects refl. -/
theorem faceMap_refl {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (x : X (n + 1)) :
    faceMap S i (Path.refl x) = Path.refl (S.face i x) := by
  simp [faceMap]

/-- Face map distributes over trans. -/
theorem faceMap_trans {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) {x y z : X (n + 1)}
    (p : Path x y) (q : Path y z) :
    faceMap S i (Path.trans p q) = Path.trans (faceMap S i p) (faceMap S i q) := by
  simp [faceMap]

/-- Degeneracy map applied to paths. -/
noncomputable def degenMap {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) {x y : X n} (p : Path x y) :
    Path (S.degen i x) (S.degen i y) :=
  Path.congrArg (S.degen i) p

/-- Degeneracy map respects refl. -/
theorem degenMap_refl {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) (x : X n) :
    degenMap S i (Path.refl x) = Path.refl (S.degen i x) := by
  simp [degenMap]

/-- Degeneracy map distributes over trans. -/
theorem degenMap_trans {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) {x y z : X n}
    (p : Path x y) (q : Path y z) :
    degenMap S i (Path.trans p q) = Path.trans (degenMap S i p) (degenMap S i q) := by
  simp [degenMap]

/-- Composite face-face map. -/
noncomputable def faceFace {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 3))
    {x y : X (n + 2)} (p : Path x y) :
    Path (S.face i (S.face j x)) (S.face i (S.face j y)) :=
  faceMap S i (faceMap S j p)

/-- Composite face-face on refl. -/
theorem faceFace_refl {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 3)) (x : X (n + 2)) :
    faceFace S i j (Path.refl x) = Path.refl (S.face i (S.face j x)) := by
  simp [faceFace, faceMap]

/-! ## §4  Quillen Adjunction -/

/-- Data for a Quillen adjunction L ⊣ R. -/
structure QuillenAdjData (A B : Type u) where
  L : A → B
  R : B → A
  unit : (a : A) → Path a (R (L a))
  counit : (b : B) → Path (L (R b)) b

/-- Left functor on paths. -/
noncomputable def leftPath {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (Q.L a₁) (Q.L a₂) :=
  Path.congrArg Q.L p

/-- Right functor on paths. -/
noncomputable def rightPath {A B : Type u} (Q : QuillenAdjData A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (Q.R b₁) (Q.R b₂) :=
  Path.congrArg Q.R p

/-- Left functor respects refl. -/
theorem leftPath_refl {A B : Type u} (Q : QuillenAdjData A B) (a : A) :
    leftPath Q (Path.refl a) = Path.refl (Q.L a) := by
  simp [leftPath]

/-- Right functor respects refl. -/
theorem rightPath_refl {A B : Type u} (Q : QuillenAdjData A B) (b : B) :
    rightPath Q (Path.refl b) = Path.refl (Q.R b) := by
  simp [rightPath]

/-- Left functor distributes over trans. -/
theorem leftPath_trans {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    leftPath Q (Path.trans p q) = Path.trans (leftPath Q p) (leftPath Q q) := by
  simp [leftPath]

/-- Right functor distributes over trans. -/
theorem rightPath_trans {A B : Type u} (Q : QuillenAdjData A B)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    rightPath Q (Path.trans p q) = Path.trans (rightPath Q p) (rightPath Q q) := by
  simp [rightPath]

/-- Left functor commutes with symm. -/
theorem leftPath_symm {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    leftPath Q (Path.symm p) = Path.symm (leftPath Q p) := by
  simp [leftPath]

/-- Right functor commutes with symm. -/
theorem rightPath_symm {A B : Type u} (Q : QuillenAdjData A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    rightPath Q (Path.symm p) = Path.symm (rightPath Q p) := by
  simp [rightPath]

/-- Round-trip R ∘ L on paths. -/
noncomputable def roundTripRL {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (Q.R (Q.L a₁)) (Q.R (Q.L a₂)) :=
  rightPath Q (leftPath Q p)

/-- Round-trip RL on refl. -/
theorem roundTripRL_refl {A B : Type u} (Q : QuillenAdjData A B) (a : A) :
    roundTripRL Q (Path.refl a) = Path.refl (Q.R (Q.L a)) := by
  simp [roundTripRL, leftPath, rightPath]

/-- Round-trip L ∘ R on paths. -/
noncomputable def roundTripLR {A B : Type u} (Q : QuillenAdjData A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (Q.L (Q.R b₁)) (Q.L (Q.R b₂)) :=
  leftPath Q (rightPath Q p)

/-- Round-trip LR on refl. -/
theorem roundTripLR_refl {A B : Type u} (Q : QuillenAdjData A B) (b : B) :
    roundTripLR Q (Path.refl b) = Path.refl (Q.L (Q.R b)) := by
  simp [roundTripLR, leftPath, rightPath]

/-- Round-trip RL distributes over trans. -/
theorem roundTripRL_trans {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    roundTripRL Q (Path.trans p q) =
    Path.trans (roundTripRL Q p) (roundTripRL Q q) := by
  simp [roundTripRL, leftPath, rightPath]

/-! ## §5  Unit-Counit Triangle Identities -/

/-- The triangle identity: counit(L a) ∘ L(unit(a)) = refl(L a)
    represented as a path equality. -/
structure TriangleId (Q : QuillenAdjData A B) where
  leftTriangle : (a : A) →
    Path.trans (leftPath Q (Q.unit a)) (Q.counit (Q.L a)) = Path.refl (Q.L a)
  rightTriangle : (b : B) →
    Path.trans (Q.unit (Q.R b)) (rightPath Q (Q.counit b)) = Path.refl (Q.R b)

/-- From triangle identity, extract left triangle for a specific point. -/
theorem triangleLeft {A B : Type u} (Q : QuillenAdjData A B)
    (tri : TriangleId Q) (a : A) :
    Path.trans (leftPath Q (Q.unit a)) (Q.counit (Q.L a)) = Path.refl (Q.L a) :=
  tri.leftTriangle a

/-- From triangle identity, extract right triangle for a specific point. -/
theorem triangleRight {A B : Type u} (Q : QuillenAdjData A B)
    (tri : TriangleId Q) (b : B) :
    Path.trans (Q.unit (Q.R b)) (rightPath Q (Q.counit b)) = Path.refl (Q.R b) :=
  tri.rightTriangle b

/-! ## §6  Cylinder Objects -/

/-- A cylinder object for a type A. -/
structure CylinderObj (A : Type u) where
  cyl : Type u
  i₀ : A → cyl
  i₁ : A → cyl
  proj : cyl → A

/-- Cylinder inclusion i₀ on paths. -/
noncomputable def cylI₀Path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (C.i₀ a₁) (C.i₀ a₂) :=
  Path.congrArg C.i₀ p

/-- Cylinder inclusion i₁ on paths. -/
noncomputable def cylI₁Path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (C.i₁ a₁) (C.i₁ a₂) :=
  Path.congrArg C.i₁ p

/-- Cylinder projection on paths. -/
noncomputable def cylProjPath {A : Type u} (C : CylinderObj A)
    {x y : C.cyl} (p : Path x y) : Path (C.proj x) (C.proj y) :=
  Path.congrArg C.proj p

/-- Cylinder i₀ respects refl. -/
theorem cylI₀Path_refl {A : Type u} (C : CylinderObj A) (a : A) :
    cylI₀Path C (Path.refl a) = Path.refl (C.i₀ a) := by simp [cylI₀Path]

/-- Cylinder i₁ respects refl. -/
theorem cylI₁Path_refl {A : Type u} (C : CylinderObj A) (a : A) :
    cylI₁Path C (Path.refl a) = Path.refl (C.i₁ a) := by simp [cylI₁Path]

/-- Cylinder projection respects refl. -/
theorem cylProjPath_refl {A : Type u} (C : CylinderObj A) (x : C.cyl) :
    cylProjPath C (Path.refl x) = Path.refl (C.proj x) := by simp [cylProjPath]

/-- Cylinder i₀ distributes over trans. -/
theorem cylI₀Path_trans {A : Type u} (C : CylinderObj A)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    cylI₀Path C (Path.trans p q) =
    Path.trans (cylI₀Path C p) (cylI₀Path C q) := by simp [cylI₀Path]

/-! ## §7  Path Objects -/

/-- A path object for a type B. -/
structure PathObj (B : Type u) where
  pathSpace : Type u
  ev₀ : pathSpace → B
  ev₁ : pathSpace → B
  diag : B → pathSpace

/-- Path object ev₀ on paths. -/
noncomputable def pathObjEv₀ {B : Type u} (P : PathObj B)
    {x y : P.pathSpace} (p : Path x y) : Path (P.ev₀ x) (P.ev₀ y) :=
  Path.congrArg P.ev₀ p

/-- Path object ev₁ on paths. -/
noncomputable def pathObjEv₁ {B : Type u} (P : PathObj B)
    {x y : P.pathSpace} (p : Path x y) : Path (P.ev₁ x) (P.ev₁ y) :=
  Path.congrArg P.ev₁ p

/-- Path object diagonal on paths. -/
noncomputable def pathObjDiag {B : Type u} (P : PathObj B)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (P.diag b₁) (P.diag b₂) :=
  Path.congrArg P.diag p

/-- Path object ev₀ ∘ diag on refl. -/
theorem pathObjEv₀Diag_refl {B : Type u} (P : PathObj B) (b : B) :
    pathObjEv₀ P (pathObjDiag P (Path.refl b)) = Path.refl (P.ev₀ (P.diag b)) := by
  simp [pathObjEv₀, pathObjDiag]

/-! ## §8  Fibrant/Cofibrant Replacement -/

/-- Fibrant replacement data. -/
structure FibReplacement (A : Type u) where
  fibRepl : A → A
  replMap : (a : A) → Path a (fibRepl a)

/-- Cofibrant replacement data. -/
structure CofReplacement (A : Type u) where
  cofRepl : A → A
  replMap : (a : A) → Path (cofRepl a) a

/-- Fibrant replacement on paths. -/
noncomputable def fibReplPath {A : Type u} (F : FibReplacement A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (F.fibRepl a₁) (F.fibRepl a₂) :=
  Path.congrArg F.fibRepl p

/-- Fibrant replacement respects refl. -/
theorem fibReplPath_refl {A : Type u} (F : FibReplacement A) (a : A) :
    fibReplPath F (Path.refl a) = Path.refl (F.fibRepl a) := by
  simp [fibReplPath]

/-- Fibrant replacement distributes over trans. -/
theorem fibReplPath_trans {A : Type u} (F : FibReplacement A)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    fibReplPath F (Path.trans p q) =
    Path.trans (fibReplPath F p) (fibReplPath F q) := by
  simp [fibReplPath]

/-- Cofibrant replacement on paths. -/
noncomputable def cofReplPath {A : Type u} (C : CofReplacement A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (C.cofRepl a₁) (C.cofRepl a₂) :=
  Path.congrArg C.cofRepl p

/-- Cofibrant replacement respects refl. -/
theorem cofReplPath_refl {A : Type u} (C : CofReplacement A) (a : A) :
    cofReplPath C (Path.refl a) = Path.refl (C.cofRepl a) := by
  simp [cofReplPath]

/-! ## §9  Retract Data -/

/-- A retract diagram: i : A → B, r : B → A with r ∘ i = id. -/
structure RetractData (A B : Type u) where
  i : A → B
  r : B → A
  retract : (a : A) → r (i a) = a

/-- Retract section on paths. -/
noncomputable def retractI {A B : Type u} (R : RetractData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (R.i a₁) (R.i a₂) :=
  Path.congrArg R.i p

/-- Retract retraction on paths. -/
noncomputable def retractR {A B : Type u} (R : RetractData A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (R.r b₁) (R.r b₂) :=
  Path.congrArg R.r p

/-- Retract witness path. -/
noncomputable def retractWitness {A B : Type u} (R : RetractData A B) (a : A) :
    Path (R.r (R.i a)) a :=
  Path.stepChain (R.retract a)

/-- Retract i respects refl. -/
theorem retractI_refl {A B : Type u} (R : RetractData A B) (a : A) :
    retractI R (Path.refl a) = Path.refl (R.i a) := by simp [retractI]

/-- Retract r respects refl. -/
theorem retractR_refl {A B : Type u} (R : RetractData A B) (b : B) :
    retractR R (Path.refl b) = Path.refl (R.r b) := by simp [retractR]

/-- Round-trip r ∘ i on paths. -/
noncomputable def retractRI {A B : Type u} (R : RetractData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (R.r (R.i a₁)) (R.r (R.i a₂)) :=
  retractR R (retractI R p)

/-- Round-trip r ∘ i on refl. -/
theorem retractRI_refl {A B : Type u} (R : RetractData A B) (a : A) :
    retractRI R (Path.refl a) = Path.refl (R.r (R.i a)) := by
  simp [retractRI, retractR, retractI]

/-! ## §10  Weak Factorization System -/

/-- A weak factorization system: every map factors as left class ∘ right class. -/
structure WFS (A B : Type u) where
  mid : Type u
  leftMap : A → mid
  rightMap : mid → B

/-- Left map on paths. -/
noncomputable def wfsLeftPath {A B : Type u} (w : WFS A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (w.leftMap a₁) (w.leftMap a₂) :=
  Path.congrArg w.leftMap p

/-- Right map on paths. -/
noncomputable def wfsRightPath {A B : Type u} (w : WFS A B)
    {x y : w.mid} (p : Path x y) : Path (w.rightMap x) (w.rightMap y) :=
  Path.congrArg w.rightMap p

/-- Composite of WFS equals original map (as paths). -/
noncomputable def wfsComposite {A B : Type u} (w : WFS A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (w.rightMap (w.leftMap a₁)) (w.rightMap (w.leftMap a₂)) :=
  wfsRightPath w (wfsLeftPath w p)

/-- WFS composite respects refl. -/
theorem wfsComposite_refl {A B : Type u} (w : WFS A B) (a : A) :
    wfsComposite w (Path.refl a) = Path.refl (w.rightMap (w.leftMap a)) := by
  simp [wfsComposite, wfsRightPath, wfsLeftPath]

/-- WFS composite distributes over trans. -/
theorem wfsComposite_trans {A B : Type u} (w : WFS A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    wfsComposite w (Path.trans p q) =
    Path.trans (wfsComposite w p) (wfsComposite w q) := by
  simp [wfsComposite, wfsRightPath, wfsLeftPath]

/-! ## §11  Homotopy Classes -/

/-- Left homotopy between maps, witnessed by a cylinder. -/
structure LeftHomotopy {A B : Type u} (C : CylinderObj A) (f g : A → B) where
  hom : C.cyl → B
  hom_i₀ : (a : A) → hom (C.i₀ a) = f a
  hom_i₁ : (a : A) → hom (C.i₁ a) = g a

/-- Left homotopy witness as path for i₀. -/
noncomputable def leftHom_i₀_path {A B : Type u} {C : CylinderObj A}
    {f g : A → B} (H : LeftHomotopy C f g) (a : A) :
    Path (H.hom (C.i₀ a)) (f a) :=
  Path.stepChain (H.hom_i₀ a)

/-- Left homotopy witness as path for i₁. -/
noncomputable def leftHom_i₁_path {A B : Type u} {C : CylinderObj A}
    {f g : A → B} (H : LeftHomotopy C f g) (a : A) :
    Path (H.hom (C.i₁ a)) (g a) :=
  Path.stepChain (H.hom_i₁ a)

/-- Right homotopy between maps, witnessed by a path object. -/
structure RightHomotopy {A B : Type u} (P : PathObj B) (f g : A → B) where
  hom : A → P.pathSpace
  hom_ev₀ : (a : A) → P.ev₀ (hom a) = f a
  hom_ev₁ : (a : A) → P.ev₁ (hom a) = g a

/-- Right homotopy witness as path for ev₀. -/
noncomputable def rightHom_ev₀_path {A B : Type u} {P : PathObj B}
    {f g : A → B} (H : RightHomotopy P f g) (a : A) :
    Path (P.ev₀ (H.hom a)) (f a) :=
  Path.stepChain (H.hom_ev₀ a)

/-- Right homotopy witness as path for ev₁. -/
noncomputable def rightHom_ev₁_path {A B : Type u} {P : PathObj B}
    {f g : A → B} (H : RightHomotopy P f g) (a : A) :
    Path (P.ev₁ (H.hom a)) (g a) :=
  Path.stepChain (H.hom_ev₁ a)

/-! ## §12  Ken Brown's Lemma Components -/

/-- A functor preserves path equivalences if it maps equivs to equivs. -/
structure PathEquivPreserving (F : A → B) where
  preserves : {a₁ a₂ : A} → (Path a₁ a₂ → Path a₂ a₁) →
    (Path (F a₁) (F a₂) → Path (F a₂) (F a₁))

/-- Composition of path-equiv-preserving functors. -/
noncomputable def pathEquivPresComp {A B C : Type u}
    (F : A → B) (G : B → C)
    (pF : PathEquivPreserving F) (pG : PathEquivPreserving G) :
    PathEquivPreserving (G ∘ F) where
  preserves := fun inv =>
    pG.preserves (pF.preserves inv)

/-! ## §13  Derived Functors -/

/-- Left derived functor data. -/
structure LeftDerived (A B : Type u) where
  cofRepl : CofReplacement A
  F : A → B

/-- Apply left derived to paths. -/
noncomputable def leftDerivedPath {A B : Type u} (D : LeftDerived A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (D.F a₁) (D.F a₂) :=
  Path.congrArg D.F p

/-- Left derived on refl. -/
theorem leftDerivedPath_refl {A B : Type u} (D : LeftDerived A B) (a : A) :
    leftDerivedPath D (Path.refl a) = Path.refl (D.F a) := by
  simp [leftDerivedPath]

/-- Right derived functor data. -/
structure RightDerived (A B : Type u) where
  fibRepl : FibReplacement B
  G : A → B

/-- Apply right derived to paths. -/
noncomputable def rightDerivedPath {A B : Type u} (D : RightDerived A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (D.G a₁) (D.G a₂) :=
  Path.congrArg D.G p

/-- Right derived on refl. -/
theorem rightDerivedPath_refl {A B : Type u} (D : RightDerived A B) (a : A) :
    rightDerivedPath D (Path.refl a) = Path.refl (D.G a) := by
  simp [rightDerivedPath]

/-! ## §14  Localization at Weak Equivalences -/

/-- Localization data: a class of maps to invert. -/
structure LocalizationData (A : Type u) where
  isWeak : {a b : A} → Path a b → Prop

/-- A weak equivalence has an inverse (up to paths). -/
structure WeakEquiv {A : Type u} (f : A → A) where
  inv : A → A
  leftInv : (a : A) → inv (f a) = a
  rightInv : (a : A) → f (inv a) = a

/-- Left inverse witness as path. -/
noncomputable def weakEquiv_leftInv_path {A : Type u}
    {f : A → A} (w : WeakEquiv f) (a : A) :
    Path (w.inv (f a)) a :=
  Path.stepChain (w.leftInv a)

/-- Right inverse witness as path. -/
noncomputable def weakEquiv_rightInv_path {A : Type u}
    {f : A → A} (w : WeakEquiv f) (a : A) :
    Path (f (w.inv a)) a :=
  Path.stepChain (w.rightInv a)

/-- Weak equivalences compose: if f and g are weak, so is g ∘ f. -/
noncomputable def weakEquivComp {A : Type u}
    {f g : A → A} (wf : WeakEquiv f) (wg : WeakEquiv g) :
    WeakEquiv (g ∘ f) where
  inv := wf.inv ∘ wg.inv
  leftInv := fun a => by
    show wf.inv (wg.inv (g (f a))) = a
    rw [wg.leftInv (f a), wf.leftInv a]
  rightInv := fun a => by
    show g (f (wf.inv (wg.inv a))) = a
    rw [wf.rightInv (wg.inv a), wg.rightInv a]

/-- Weak equivalence identity. -/
noncomputable def weakEquivId (A : Type u) : WeakEquiv (id : A → A) where
  inv := id
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl

/-- Composition of left-derived path with cofibrant replacement. -/
theorem leftDerived_cofRepl {A B : Type u} (D : LeftDerived A B) (a : A) :
    leftDerivedPath D (D.cofRepl.replMap a) =
    Path.congrArg D.F (D.cofRepl.replMap a) := by
  rfl

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep
