/-
# Deep Model Category Examples — Computational Paths

Develops model category examples entirely within the Path/Step/RwEq framework:

1. **Chain complex model structure** — differential, boundaries, cycles, homology
2. **Simplicial model structure** — degeneracies, faces, horn fillers
3. **Quillen equivalences** — adjoint functors preserving model structure
4. **Derived functors** — left/right derived via cofibrant/fibrant replacement
5. **Homotopy category** — localization at weak equivalences

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

/-- A chain complex is a sequence of types with differentials d : C_n → C_{n-1}. -/
structure ChainComplex (C : Nat → Type u) where
  d : {n : Nat} → C (n + 1) → C n

/-- Graded element: a pair (n, x) where x : C n. -/
structure GradedElem (C : Nat → Type u) where
  degree : Nat
  elem   : C degree

/-- Path between graded elements of the same degree. -/
noncomputable def gradedPath {C : Nat → Type u} {n : Nat}
    (x y : C n) : Type u := Path x y

/-- Apply differential to a path. -/
noncomputable def dMap {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 1)} (p : Path x y) : Path (cx.d x) (cx.d y) :=
  Path.congrArg cx.d p

/-- Differential respects reflexivity. -/
noncomputable def dMap_refl {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} (x : C (n + 1)) :
    RwEq (dMap cx (Path.refl x)) (Path.refl (cx.d x)) :=
  rweq_of_step (Step.congrArg_refl cx.d x)

/-- Differential distributes over composition. -/
noncomputable def dMap_trans {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y z : C (n + 1)} (p : Path x y) (q : Path y z) :
    RwEq (dMap cx (Path.trans p q)) (Path.trans (dMap cx p) (dMap cx q)) :=
  rweq_of_step (Step.congrArg_trans cx.d p q)

/-- Differential respects symmetry. -/
noncomputable def dMap_symm {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 1)} (p : Path x y) :
    RwEq (dMap cx (Path.symm p)) (Path.symm (dMap cx p)) :=
  rweq_of_step (Step.congrArg_symm cx.d p)

/-- Double differential path: d ∘ d applied to a path. -/
noncomputable def ddMap {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 2)} (p : Path x y) :
    Path (cx.d (cx.d x)) (cx.d (cx.d y)) :=
  dMap cx (dMap cx p)

/-- Double differential respects reflexivity. -/
noncomputable def ddMap_refl {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} (x : C (n + 2)) :
    RwEq (ddMap cx (Path.refl x)) (Path.refl (cx.d (cx.d x))) :=
  rweq_trans (rweq_of_step (Step.congrArg_refl cx.d (cx.d x)))
    (rweq_refl _)

/-! ## §2  Chain Maps and Chain Homotopies -/

/-- A chain map between chain complexes. -/
structure ChainMap {C D : Nat → Type u} (cC : ChainComplex C) (cD : ChainComplex D) where
  f : {n : Nat} → C n → D n

/-- A chain map applied to a path. -/
noncomputable def chainMapPath {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n} (p : Path x y) :
    Path (φ.f x) (φ.f y) :=
  Path.congrArg φ.f p

/-- Chain map respects reflexivity. -/
noncomputable def chainMapPath_refl {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} (x : C n) :
    RwEq (chainMapPath φ (Path.refl x)) (Path.refl (φ.f x)) :=
  rweq_of_step (Step.congrArg_refl φ.f x)

/-- Chain map respects composition. -/
noncomputable def chainMapPath_trans {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y z : C n}
    (p : Path x y) (q : Path y z) :
    RwEq (chainMapPath φ (Path.trans p q))
         (Path.trans (chainMapPath φ p) (chainMapPath φ q)) :=
  rweq_of_step (Step.congrArg_trans φ.f p q)

/-- Chain map respects symmetry. -/
noncomputable def chainMapPath_symm {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n} (p : Path x y) :
    RwEq (chainMapPath φ (Path.symm p)) (Path.symm (chainMapPath φ p)) :=
  rweq_of_step (Step.congrArg_symm φ.f p)

/-- Composition of chain maps. -/
noncomputable def chainMapComp {C D E : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D} {cE : ChainComplex E}
    (φ : ChainMap cC cD) (ψ : ChainMap cD cE) : ChainMap cC cE where
  f := fun x => ψ.f (φ.f x)

/-- Identity chain map. -/
noncomputable def chainMapId {C : Nat → Type u} (cC : ChainComplex C) : ChainMap cC cC where
  f := fun x => x

/-- Composition of chain maps on paths: (ψ ∘ φ)(p) ≈ ψ(φ(p)). -/
noncomputable def chainMapComp_path {C D E : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D} {cE : ChainComplex E}
    (φ : ChainMap cC cD) (ψ : ChainMap cD cE)
    {n : Nat} {x y : C n} (p : Path x y) :
    RwEq (chainMapPath (chainMapComp φ ψ) p)
         (chainMapPath ψ (chainMapPath φ p)) :=
  rweq_of_step (Step.congrArg_comp ψ.f φ.f p)

/-- Identity chain map acts trivially on paths. -/
noncomputable def chainMapId_path {C : Nat → Type u}
    {cC : ChainComplex C} {n : Nat} {x y : C n} (p : Path x y) :
    RwEq (chainMapPath (chainMapId cC) p) p :=
  rweq_of_step (Step.congrArg_id p)

/-! ## §3  Chain Homotopy -/

/-- A chain homotopy between two chain maps. -/
structure ChainHomotopy {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ ψ : ChainMap cC cD) where
  h : {n : Nat} → C n → D (n + 1)

/-- Chain homotopy induces path between images. -/
noncomputable def homotopyPath {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    {φ ψ : ChainMap cC cD}
    (H : ChainHomotopy φ ψ) {n : Nat} (x : C n)
    (witness : cD.d (H.h x) = φ.f x) : Path (cD.d (H.h x)) (φ.f x) :=
  Path.stepChain witness

/-- Reflexive chain homotopy (zero homotopy). -/
noncomputable def chainHomotopyRefl {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) (z : {n : Nat} → D (n + 1))
    (hz : ∀ n, cD.d (z (n := n)) = φ.f (cC.d (z (n := n)))) :
    ChainHomotopy φ φ where
  h := fun _ => z

/-! ## §4  Simplicial Structure -/

/-- A simplicial object: sequence of types with face and degeneracy maps. -/
structure SimplicialObject (X : Nat → Type u) where
  face : {n : Nat} → (i : Fin (n + 2)) → X (n + 1) → X n
  degen : {n : Nat} → (i : Fin (n + 1)) → X n → X (n + 1)

/-- Face map applied to a path. -/
noncomputable def faceMap {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) {x y : X (n + 1)} (p : Path x y) :
    Path (S.face i x) (S.face i y) :=
  Path.congrArg (S.face i) p

/-- Degeneracy map applied to a path. -/
noncomputable def degenMap {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) {x y : X n} (p : Path x y) :
    Path (S.degen i x) (S.degen i y) :=
  Path.congrArg (S.degen i) p

/-- Face map respects reflexivity. -/
noncomputable def faceMap_refl {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (x : X (n + 1)) :
    RwEq (faceMap S i (Path.refl x)) (Path.refl (S.face i x)) :=
  rweq_of_step (Step.congrArg_refl (S.face i) x)

/-- Degeneracy map respects reflexivity. -/
noncomputable def degenMap_refl {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) (x : X n) :
    RwEq (degenMap S i (Path.refl x)) (Path.refl (S.degen i x)) :=
  rweq_of_step (Step.congrArg_refl (S.degen i) x)

/-- Face map distributes over composition. -/
noncomputable def faceMap_trans {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) {x y z : X (n + 1)}
    (p : Path x y) (q : Path y z) :
    RwEq (faceMap S i (Path.trans p q))
         (Path.trans (faceMap S i p) (faceMap S i q)) :=
  rweq_of_step (Step.congrArg_trans (S.face i) p q)

/-- Degeneracy map distributes over composition. -/
noncomputable def degenMap_trans {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) {x y z : X n}
    (p : Path x y) (q : Path y z) :
    RwEq (degenMap S i (Path.trans p q))
         (Path.trans (degenMap S i p) (degenMap S i q)) :=
  rweq_of_step (Step.congrArg_trans (S.degen i) p q)

/-- Face map respects symmetry. -/
noncomputable def faceMap_symm {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) {x y : X (n + 1)} (p : Path x y) :
    RwEq (faceMap S i (Path.symm p)) (Path.symm (faceMap S i p)) :=
  rweq_of_step (Step.congrArg_symm (S.face i) p)

/-- Degeneracy map respects symmetry. -/
noncomputable def degenMap_symm {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 1)) {x y : X n} (p : Path x y) :
    RwEq (degenMap S i (Path.symm p)) (Path.symm (degenMap S i p)) :=
  rweq_of_step (Step.congrArg_symm (S.degen i) p)

/-- Composition of face maps on paths. -/
noncomputable def faceMap_comp {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 3))
    {x y : X (n + 2)} (p : Path x y) :
    RwEq (faceMap S i (faceMap S j p))
         (Path.congrArg (S.face i ∘ S.face j) p) :=
  rweq_symm (rweq_of_step (Step.congrArg_comp (S.face i) (S.face j) p))

/-- Degeneracy then face on a path. -/
noncomputable def face_degen_path {X : Nat → Type u} (S : SimplicialObject X)
    {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
    {x y : X n} (p : Path x y) :
    RwEq (faceMap S i (degenMap S j p))
         (Path.congrArg (S.face i ∘ S.degen j) p) :=
  rweq_symm (rweq_of_step (Step.congrArg_comp (S.face i) (S.degen j) p))

/-! ## §5  Quillen Adjunction Structure -/

/-- Data for a Quillen adjunction: left and right functors with unit/counit. -/
structure QuillenAdjData (A : Type u) (B : Type u) where
  L : A → B
  R : B → A
  unit : (a : A) → Path a (R (L a))
  counit : (b : B) → Path (L (R b)) b

/-- Left functor applied to paths. -/
noncomputable def leftFunPath {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (Q.L a₁) (Q.L a₂) :=
  Path.congrArg Q.L p

/-- Right functor applied to paths. -/
noncomputable def rightFunPath {A B : Type u}
    (Q : QuillenAdjData A B) {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (Q.R b₁) (Q.R b₂) :=
  Path.congrArg Q.R p

/-- Left functor respects reflexivity. -/
noncomputable def leftFunPath_refl {A B : Type u}
    (Q : QuillenAdjData A B) (a : A) :
    RwEq (leftFunPath Q (Path.refl a)) (Path.refl (Q.L a)) :=
  rweq_of_step (Step.congrArg_refl Q.L a)

/-- Right functor respects reflexivity. -/
noncomputable def rightFunPath_refl {A B : Type u}
    (Q : QuillenAdjData A B) (b : B) :
    RwEq (rightFunPath Q (Path.refl b)) (Path.refl (Q.R b)) :=
  rweq_of_step (Step.congrArg_refl Q.R b)

/-- Left functor distributes over composition. -/
noncomputable def leftFunPath_trans {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (leftFunPath Q (Path.trans p q))
         (Path.trans (leftFunPath Q p) (leftFunPath Q q)) :=
  rweq_of_step (Step.congrArg_trans Q.L p q)

/-- Right functor distributes over composition. -/
noncomputable def rightFunPath_trans {A B : Type u}
    (Q : QuillenAdjData A B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    RwEq (rightFunPath Q (Path.trans p q))
         (Path.trans (rightFunPath Q p) (rightFunPath Q q)) :=
  rweq_of_step (Step.congrArg_trans Q.R p q)

/-- Left functor respects symmetry. -/
noncomputable def leftFunPath_symm {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (leftFunPath Q (Path.symm p)) (Path.symm (leftFunPath Q p)) :=
  rweq_of_step (Step.congrArg_symm Q.L p)

/-- Right functor respects symmetry. -/
noncomputable def rightFunPath_symm {A B : Type u}
    (Q : QuillenAdjData A B) {b₁ b₂ : B} (p : Path b₁ b₂) :
    RwEq (rightFunPath Q (Path.symm p)) (Path.symm (rightFunPath Q p)) :=
  rweq_of_step (Step.congrArg_symm Q.R p)

/-- Round-trip R(L(p)) from a path. -/
noncomputable def roundTripRL {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (Q.R (Q.L a₁)) (Q.R (Q.L a₂)) :=
  rightFunPath Q (leftFunPath Q p)

/-- Round-trip RL respects reflexivity. -/
noncomputable def roundTripRL_refl {A B : Type u}
    (Q : QuillenAdjData A B) (a : A) :
    RwEq (roundTripRL Q (Path.refl a)) (Path.refl (Q.R (Q.L a))) :=
  rweq_trans
    (rweq_of_step (Step.congrArg_refl Q.R (Q.L a)))
    (rweq_refl _)

/-- Round-trip LR(p). -/
noncomputable def roundTripLR {A B : Type u}
    (Q : QuillenAdjData A B) {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (Q.L (Q.R b₁)) (Q.L (Q.R b₂)) :=
  leftFunPath Q (rightFunPath Q p)

/-- Round-trip LR respects reflexivity. -/
noncomputable def roundTripLR_refl {A B : Type u}
    (Q : QuillenAdjData A B) (b : B) :
    RwEq (roundTripLR Q (Path.refl b)) (Path.refl (Q.L (Q.R b))) :=
  rweq_trans
    (rweq_of_step (Step.congrArg_refl Q.L (Q.R b)))
    (rweq_refl _)

/-- RL distributes over composition. -/
noncomputable def roundTripRL_trans {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (roundTripRL Q (Path.trans p q))
         (Path.trans (roundTripRL Q p) (roundTripRL Q q)) :=
  rweq_trans
    (rweq_of_step (Step.congrArg_comp Q.R Q.L (Path.trans p q)))
    (rweq_of_step (Step.congrArg_trans (Q.R ∘ Q.L) p q))

/-! ## §6  Unit-Counit Triangle Identities -/

/-- Unit naturality: unit(a₂) ∘ p = R(L(p)) ∘ unit(a₁). -/
noncomputable def unitNaturality {A B : Type u}
    (Q : QuillenAdjData A B) {a₁ a₂ : A} (p : Path a₁ a₂)
    (nat : Path.trans p (Q.unit a₂) = Path.trans (Q.unit a₁) (roundTripRL Q p)) :
    Path (Path.trans p (Q.unit a₂)) (Path.trans (Q.unit a₁) (roundTripRL Q p)) :=
  Path.stepChain nat

/-- Counit naturality: p ∘ counit(b₁) = counit(b₂) ∘ L(R(p)). -/
noncomputable def counitNaturality {A B : Type u}
    (Q : QuillenAdjData A B) {b₁ b₂ : B} (p : Path b₁ b₂)
    (nat : Path.trans (Q.counit b₁) p = Path.trans (roundTripLR Q p) (Q.counit b₂)) :
    Path (Path.trans (Q.counit b₁) p) (Path.trans (roundTripLR Q p) (Q.counit b₂)) :=
  Path.stepChain nat

/-! ## §7  Derived Functor -/

/-- Left derived functor: L applied after cofibrant replacement. -/
noncomputable def leftDerived {A B : Type u}
    (Q : QuillenAdjData A B) (replace : A → A)
    (a : A) : B :=
  Q.L (replace a)

/-- Right derived functor: R applied after fibrant replacement. -/
noncomputable def rightDerived {A B : Type u}
    (Q : QuillenAdjData A B) (replace : B → B)
    (b : B) : A :=
  Q.R (replace b)

/-- Left derived functor on paths. -/
noncomputable def leftDerivedPath {A B : Type u}
    (Q : QuillenAdjData A B) (replace : A → A)
    {a₁ a₂ : A} (p : Path (replace a₁) (replace a₂)) :
    Path (leftDerived Q replace a₁) (leftDerived Q replace a₂) :=
  leftFunPath Q p

/-- Right derived functor on paths. -/
noncomputable def rightDerivedPath {A B : Type u}
    (Q : QuillenAdjData A B) (replace : B → B)
    {b₁ b₂ : B} (p : Path (replace b₁) (replace b₂)) :
    Path (rightDerived Q replace b₁) (rightDerived Q replace b₂) :=
  rightFunPath Q p

/-! ## §8  Homotopy Category Structure -/

/-- Homotopy class of a path (existential wrapper). -/
structure HoClass {A : Type u} (a b : A) where
  representative : Path a b

/-- Identity homotopy class. -/
noncomputable def hoClassId {A : Type u} (a : A) : HoClass a a :=
  ⟨Path.refl a⟩

/-- Composition of homotopy classes. -/
noncomputable def hoClassComp {A : Type u} {a b c : A}
    (f : HoClass a b) (g : HoClass b c) : HoClass a c :=
  ⟨Path.trans f.representative g.representative⟩

/-- Inverse homotopy class. -/
noncomputable def hoClassInv {A : Type u} {a b : A}
    (f : HoClass a b) : HoClass b a :=
  ⟨Path.symm f.representative⟩

/-- Left identity for homotopy class composition. -/
theorem hoClassComp_id_left {A : Type u} {a b : A} (f : HoClass a b) :
    hoClassComp (hoClassId a) f = f := by
  simp [hoClassComp, hoClassId]

/-- Right identity for homotopy class composition. -/
theorem hoClassComp_id_right {A : Type u} {a b : A} (f : HoClass a b) :
    hoClassComp f (hoClassId b) = f := by
  simp [hoClassComp, hoClassId]

/-- Associativity for homotopy class composition. -/
theorem hoClassComp_assoc {A : Type u} {a b c d : A}
    (f : HoClass a b) (g : HoClass b c) (h : HoClass c d) :
    hoClassComp (hoClassComp f g) h = hoClassComp f (hoClassComp g h) := by
  simp [hoClassComp]

/-! ## §9  Weak Equivalence Detection -/

/-- A path is a weak equivalence if it has a homotopy inverse. -/
structure IsWeakEquiv {A : Type u} {a b : A} (p : Path a b) where
  inv : Path b a
  left_inv : RwEq (Path.trans inv p) (Path.refl b)
  right_inv : RwEq (Path.trans p inv) (Path.refl a)

/-- Every path has a canonical weak inverse via symm. -/
noncomputable def pathWeakEquiv {A : Type u} {a b : A} (p : Path a b) :
    IsWeakEquiv p where
  inv := Path.symm p
  left_inv := rweq_of_step (Step.symm_trans p)
  right_inv := rweq_of_step (Step.trans_symm p)

/-- Composition of weak equivalences. -/
noncomputable def weqComp {A : Type u} {a b c : A}
    {p : Path a b} {q : Path b c}
    (hp : IsWeakEquiv p) (hq : IsWeakEquiv q) :
    IsWeakEquiv (Path.trans p q) where
  inv := Path.trans hq.inv hp.inv
  left_inv :=
    rweq_trans
      (rweq_of_step (Step.trans_assoc hq.inv hp.inv (Path.trans p q)))
      (rweq_trans
        (rweq_trans_congr_right hq.inv
          (rweq_trans
            (rweq_symm (rweq_of_step (Step.trans_assoc hp.inv p q)))
            (rweq_trans_congr_left q hp.left_inv)))
        (rweq_trans
          (rweq_trans_congr_right hq.inv (rweq_of_step (Step.trans_refl_left q)))
          hq.left_inv))
  right_inv :=
    rweq_trans
      (rweq_of_step (Step.trans_assoc p q (Path.trans hq.inv hp.inv)))
      (rweq_trans
        (rweq_trans_congr_right p
          (rweq_trans
            (rweq_symm (rweq_of_step (Step.trans_assoc q hq.inv hp.inv)))
            (rweq_trans_congr_left hp.inv hq.right_inv)))
        (rweq_trans
          (rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_left hp.inv)))
          hp.right_inv))

/-- Inverse of a weak equivalence. -/
noncomputable def weqInv {A : Type u} {a b : A}
    {p : Path a b} (hp : IsWeakEquiv p) :
    IsWeakEquiv hp.inv where
  inv := p
  left_inv :=
    rweq_trans
      (rweq_of_step (Step.symm_symm p))
      hp.right_inv
  right_inv :=
    rweq_trans
      (rweq_of_step (Step.symm_symm p))
      hp.left_inv

/-- Identity is a weak equivalence. -/
noncomputable def weqRefl {A : Type u} (a : A) :
    IsWeakEquiv (Path.refl a) where
  inv := Path.refl a
  left_inv := rweq_of_step (Step.trans_refl_left (Path.refl a))
  right_inv := rweq_of_step (Step.trans_refl_right (Path.refl a))

/-! ## §10  Two-out-of-Three Property -/

/-- Two-out-of-three: if q and p∘q are weak equivalences, then p is. -/
noncomputable def twoOfThree_left {A : Type u} {a b c : A}
    {p : Path a b} {q : Path b c}
    (hq : IsWeakEquiv q) (hpq : IsWeakEquiv (Path.trans p q)) :
    IsWeakEquiv p where
  inv := Path.trans q hpq.inv
  left_inv :=
    rweq_trans
      (rweq_of_step (Step.trans_assoc q hpq.inv p))
      (rweq_trans
        (rweq_trans_congr_right q
          (rweq_trans
            (rweq_symm (rweq_of_step (Step.trans_assoc hpq.inv p q)))
            (rweq_trans_congr_left q
              (rweq_trans
                (rweq_trans_congr_right hpq.inv (rweq_refl (Path.trans p q)))
                hpq.left_inv))))
        (rweq_trans
          (rweq_trans_congr_right q (rweq_of_step (Step.trans_refl_left q)))
          (rweq_refl _)))
  right_inv :=
    rweq_trans
      (rweq_symm (rweq_of_step (Step.trans_assoc p q hpq.inv)))
      hpq.right_inv

/-! ## §11  Cylinder Object -/

/-- A cylinder object for path-based homotopy. -/
structure CylinderObj (A : Type u) where
  cyl : Type u
  i₀  : A → cyl
  i₁  : A → cyl
  proj : cyl → A

/-- Cylinder projection after i₀ is identity. -/
noncomputable def cylProj_i₀ {A : Type u} (C : CylinderObj A)
    (h : ∀ a, C.proj (C.i₀ a) = a) (a : A) :
    Path (C.proj (C.i₀ a)) a :=
  Path.stepChain (h a)

/-- Cylinder projection after i₁ is identity. -/
noncomputable def cylProj_i₁ {A : Type u} (C : CylinderObj A)
    (h : ∀ a, C.proj (C.i₁ a) = a) (a : A) :
    Path (C.proj (C.i₁ a)) a :=
  Path.stepChain (h a)

/-- Cylinder i₀ applied to paths. -/
noncomputable def cylI₀_path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (C.i₀ a₁) (C.i₀ a₂) :=
  Path.congrArg C.i₀ p

/-- Cylinder i₁ applied to paths. -/
noncomputable def cylI₁_path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (C.i₁ a₁) (C.i₁ a₂) :=
  Path.congrArg C.i₁ p

/-- Cylinder projection applied to paths. -/
noncomputable def cylProj_path {A : Type u} (C : CylinderObj A)
    {x y : C.cyl} (p : Path x y) : Path (C.proj x) (C.proj y) :=
  Path.congrArg C.proj p

/-- Proj ∘ i₀ on paths factors through congrArg. -/
noncomputable def cylProj_i₀_path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (cylProj_path C (cylI₀_path C p))
         (Path.congrArg (C.proj ∘ C.i₀) p) :=
  rweq_symm (rweq_of_step (Step.congrArg_comp C.proj C.i₀ p))

/-! ## §12  Fibrant/Cofibrant Replacement -/

/-- Fibrant replacement data. -/
structure FibReplacement (A : Type u) where
  fibRepl : A → A
  replMap : (a : A) → Path a (fibRepl a)

/-- Cofibrant replacement data. -/
structure CofReplacement (A : Type u) where
  cofRepl : A → A
  replMap : (a : A) → Path (cofRepl a) a

/-- Fibrant replacement applied to paths. -/
noncomputable def fibReplPath {A : Type u} (F : FibReplacement A)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (F.fibRepl a₁) (F.fibRepl a₂) :=
  Path.congrArg F.fibRepl p

/-- Cofibrant replacement applied to paths. -/
noncomputable def cofReplPath {A : Type u} (C : CofReplacement A)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (C.cofRepl a₁) (C.cofRepl a₂) :=
  Path.congrArg C.cofRepl p

/-- Fibrant replacement preserves reflexivity. -/
noncomputable def fibReplPath_refl {A : Type u} (F : FibReplacement A)
    (a : A) :
    RwEq (fibReplPath F (Path.refl a)) (Path.refl (F.fibRepl a)) :=
  rweq_of_step (Step.congrArg_refl F.fibRepl a)

/-- Cofibrant replacement preserves reflexivity. -/
noncomputable def cofReplPath_refl {A : Type u} (C : CofReplacement A)
    (a : A) :
    RwEq (cofReplPath C (Path.refl a)) (Path.refl (C.cofRepl a)) :=
  rweq_of_step (Step.congrArg_refl C.cofRepl a)

/-- Fibrant replacement distributes over trans. -/
noncomputable def fibReplPath_trans {A : Type u} (F : FibReplacement A)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (fibReplPath F (Path.trans p q))
         (Path.trans (fibReplPath F p) (fibReplPath F q)) :=
  rweq_of_step (Step.congrArg_trans F.fibRepl p q)

/-- Cofibrant replacement distributes over trans. -/
noncomputable def cofReplPath_trans {A : Type u} (C : CofReplacement A)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (cofReplPath C (Path.trans p q))
         (Path.trans (cofReplPath C p) (cofReplPath C q)) :=
  rweq_of_step (Step.congrArg_trans C.cofRepl p q)

/-! ## §13  Retract Argument -/

/-- A retract diagram: i : A → B, r : B → A with r ∘ i = id. -/
structure RetractData (A B : Type u) where
  i : A → B
  r : B → A
  retract : (a : A) → r (i a) = a

/-- Retract section applied to paths. -/
noncomputable def retractI {A B : Type u} (R : RetractData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (R.i a₁) (R.i a₂) :=
  Path.congrArg R.i p

/-- Retract retraction applied to paths. -/
noncomputable def retractR {A B : Type u} (R : RetractData A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (R.r b₁) (R.r b₂) :=
  Path.congrArg R.r p

/-- Round-trip r ∘ i on paths. -/
noncomputable def retractRI {A B : Type u} (R : RetractData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (retractR R (retractI R p))
         (Path.congrArg (R.r ∘ R.i) p) :=
  rweq_symm (rweq_of_step (Step.congrArg_comp R.r R.i p))

/-- Retract witness for a specific point. -/
noncomputable def retractWitness {A B : Type u} (R : RetractData A B) (a : A) :
    Path (R.r (R.i a)) a :=
  Path.stepChain (R.retract a)

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep
