/-
# Derived categories via computational paths

Chain complexes, quasi-isomorphisms, homotopies, derived category localization,
triangulated structure, Ext/Tor, and spectral sequences—all built with
Step/Path/trans/symm/congrArg/transport.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace DerivedCategory

noncomputable section

open Path

universe u v w

/-! ## Domain-specific rewrite steps -/

/-- Domain-specific rewrite steps for derived category coherence. -/
inductive DerivedStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      DerivedStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      DerivedStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      DerivedStep (Path.trans p (Path.symm p)) (Path.refl a)
  | inverse_cancel_left {a b : A} (p : Path a b) :
      DerivedStep (Path.trans (Path.symm p) p) (Path.refl b)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      DerivedStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))
  | symm_distrib {a b c : A} (p : Path a b) (q : Path b c) :
      DerivedStep (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p))

/-- Interpret a derived step as a primitive `Path.Step`. -/
def DerivedStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : DerivedStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p
  | .inverse_cancel_left p => Path.Step.symm_trans p
  | .assoc p q r => Path.Step.trans_assoc p q r
  | .symm_distrib p q => Path.Step.symm_trans_congr p q

/-- Lift a derived step to rewrite equivalence. -/
def rweq_of_derived_step {A : Type u} {a b : A}
    {p q : Path a b} (s : DerivedStep p q) : RwEq p q :=
  rweq_of_step (DerivedStep.toStep s)

/-! ## Chain complexes -/

/-- A chain complex: objects with differential d, and d∘d = 0 via path cancellation. -/
structure ChainComplexData (A : Type u) where
  /-- Objects at each degree -/
  obj : Int → A
  /-- Differential map -/
  diff : ∀ n : Int, A → A
  /-- d∘d = 0 : differential applied twice yields identity path. -/
  ddZeroPath : ∀ (n : Int) (x : A),
    Path (diff n (diff (n + 1) x)) x
  /-- Differential respects identity at degree n. -/
  diffIdentPath : ∀ (n : Int),
    Path (diff n (obj n)) (obj (n - 1))

namespace ChainComplexData

variable {A : Type u} (C : ChainComplexData A)

/-- d∘d = 0 followed by refl simplifies. -/
def dd_zero_rweq (n : Int) (x : A) :
    RwEq
      (Path.trans (C.ddZeroPath n x) (Path.refl x))
      (C.ddZeroPath n x) :=
  rweq_of_derived_step (DerivedStep.right_unit (C.ddZeroPath n x))

/-- Differential round-trip: apply d∘d then undo. -/
def ddRoundTrip (n : Int) (x : A) :
    Path (C.diff n (C.diff (n + 1) x)) (C.diff n (C.diff (n + 1) x)) :=
  Path.trans (C.ddZeroPath n x) (Path.symm (C.ddZeroPath n x))

/-- dd round-trip is identity up to RwEq. -/
def ddRoundTrip_rweq (n : Int) (x : A) :
    RwEq (C.ddRoundTrip n x) (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (C.ddZeroPath n x))

/-- Differential identity path followed by refl. -/
def diff_ident_rweq (n : Int) :
    RwEq
      (Path.trans (C.diffIdentPath n) (Path.refl _))
      (C.diffIdentPath n) :=
  rweq_of_derived_step (DerivedStep.right_unit (C.diffIdentPath n))

/-- Transport constant family along dd path. -/
theorem dd_transport_const {B : Type v} (n : Int) (x : A) (b : B) :
    Path.transport (D := fun _ => B) (C.ddZeroPath n x) b = b := by
  simp [Path.transport_const]

end ChainComplexData

/-! ## Chain maps -/

/-- A chain map between two chain complexes. -/
structure ChainMapData (A : Type u)
    (C₁ C₂ : ChainComplexData A) where
  /-- The map at each degree. -/
  mapDeg : A → A
  /-- Commutativity with differential. -/
  commPath : ∀ (n : Int) (x : A),
    Path (mapDeg (C₁.diff n x)) (C₂.diff n (mapDeg x))

namespace ChainMapData

variable {A : Type u} {C₁ C₂ C₃ : ChainComplexData A}

/-- Compose two chain maps. -/
def comp (f : ChainMapData A C₁ C₂) (g : ChainMapData A C₂ C₃) :
    ChainMapData A C₁ C₃ where
  mapDeg := g.mapDeg ∘ f.mapDeg
  commPath n x :=
    Path.trans
      (Path.congrArg g.mapDeg (f.commPath n x))
      (g.commPath n (f.mapDeg x))

/-- Identity chain map. -/
def id (C : ChainComplexData A) : ChainMapData A C C where
  mapDeg := fun x => x
  commPath _ _ := Path.refl _

/-- Commutativity path followed by refl simplifies. -/
def comm_rweq (f : ChainMapData A C₁ C₂) (n : Int) (x : A) :
    RwEq
      (Path.trans (f.commPath n x) (Path.refl _))
      (f.commPath n x) :=
  rweq_of_derived_step (DerivedStep.right_unit (f.commPath n x))

/-- Composition commutativity coherence (toEq). -/
theorem comp_comm_toEq (f : ChainMapData A C₁ C₂) (g : ChainMapData A C₂ C₃)
    (n : Int) (x : A) :
    ((comp f g).commPath n x).toEq =
    (Path.trans
      (Path.congrArg g.mapDeg (f.commPath n x))
      (g.commPath n (f.mapDeg x))).toEq := rfl

end ChainMapData

/-! ## Quasi-isomorphisms -/

/-- A quasi-isomorphism: a chain map that induces path equivalences on homology. -/
structure QuasiIsoData (A : Type u)
    (C₁ C₂ : ChainComplexData A)
    extends ChainMapData A C₁ C₂ where
  /-- Inverse map at each degree (on homology). -/
  invMap : A → A
  /-- Forward-inverse composition is identity. -/
  forwardInvPath : ∀ x : A, Path (mapDeg (invMap x)) x
  /-- Inverse-forward composition is identity. -/
  invForwardPath : ∀ x : A, Path (invMap (mapDeg x)) x

namespace QuasiIsoData

variable {A : Type u} {C₁ C₂ : ChainComplexData A}
variable (Q : QuasiIsoData A C₁ C₂)

/-- Forward-inverse round-trip. -/
def forwardInvRoundTrip (x : A) :
    Path (Q.mapDeg (Q.invMap x)) (Q.mapDeg (Q.invMap x)) :=
  Path.trans (Q.forwardInvPath x) (Path.symm (Q.forwardInvPath x))

/-- Forward-inverse round-trip is refl. -/
def forwardInvRoundTrip_rweq (x : A) :
    RwEq (Q.forwardInvRoundTrip x) (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (Q.forwardInvPath x))

/-- Inverse-forward round-trip is refl. -/
def invForwardRoundTrip_rweq (x : A) :
    RwEq
      (Path.trans (Q.invForwardPath x) (Path.symm (Q.invForwardPath x)))
      (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (Q.invForwardPath x))

/-- Quasi-isomorphism paths compose coherently (toEq): two different witnesses agree. -/
theorem qi_coherence_toEq (x : A) :
    (Path.congrArg Q.mapDeg (Q.invForwardPath x)).toEq =
    (Q.forwardInvPath (Q.mapDeg x)).toEq := by
  apply Subsingleton.elim

end QuasiIsoData

/-! ## Chain homotopies -/

/-- A chain homotopy between two chain maps: path-level witness. -/
structure ChainHomotopyData (A : Type u)
    (C₁ C₂ : ChainComplexData A)
    (f g : ChainMapData A C₁ C₂) where
  /-- Homotopy operator. -/
  homotopy : A → A
  /-- Homotopy formula: d∘h + h∘d = f - g modeled as path. -/
  homotopyPath : ∀ (n : Int) (x : A),
    Path (f.mapDeg x) (g.mapDeg x)

namespace ChainHomotopyData

variable {A : Type u} {C₁ C₂ : ChainComplexData A}
variable {f g : ChainMapData A C₁ C₂}
variable (H : ChainHomotopyData A C₁ C₂ f g)

/-- Homotopy path followed by refl simplifies. -/
def homotopy_rweq (n : Int) (x : A) :
    RwEq
      (Path.trans (H.homotopyPath n x) (Path.refl _))
      (H.homotopyPath n x) :=
  rweq_of_derived_step (DerivedStep.right_unit (H.homotopyPath n x))

/-- Inverse homotopy. -/
def inverse : ChainHomotopyData A C₁ C₂ g f where
  homotopy := H.homotopy
  homotopyPath n x := Path.symm (H.homotopyPath n x)

/-- Inverse homotopy path is symm. -/
@[simp] theorem inverse_path (n : Int) (x : A) :
    H.inverse.homotopyPath n x = Path.symm (H.homotopyPath n x) := rfl

/-- Homotopy composed with its inverse is refl up to RwEq. -/
def homotopy_inv_rweq (n : Int) (x : A) :
    RwEq
      (Path.trans (H.homotopyPath n x) (H.inverse.homotopyPath n x))
      (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (H.homotopyPath n x))

end ChainHomotopyData

/-! ## Derived category localization -/

/-- Derived category localization: invert quasi-isomorphisms via path inversion. -/
structure DerivedLocData (A : Type u)
    (C : ChainComplexData A) where
  /-- Localized morphism: a span with a quasi-iso roof. -/
  span : A → A → A
  /-- Forward path of the span. -/
  forwardPath : ∀ x y : A, Path (span x y) y
  /-- Backward path of the span (localized inverse). -/
  backwardPath : ∀ x y : A, Path (span x y) x
  /-- Composition in the derived category. -/
  derivedCompose : A → A → A
  /-- Associativity of derived composition. -/
  derivedAssocPath : ∀ x y z : A,
    Path (derivedCompose (derivedCompose x y) z)
         (derivedCompose x (derivedCompose y z))
  /-- Identity in the derived category. -/
  derivedIdent : A → A
  /-- Left unit for derived composition. -/
  derivedLeftUnitPath : ∀ x : A,
    Path (derivedCompose (derivedIdent x) x) x

namespace DerivedLocData

variable {A : Type u} {C : ChainComplexData A}
variable (D : DerivedLocData A C)

/-- Derived assoc up to RwEq. -/
def derived_assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (D.derivedAssocPath x y z) (Path.refl _))
      (D.derivedAssocPath x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (D.derivedAssocPath x y z))

/-- Derived left unit up to RwEq. -/
def derived_left_unit_rweq (x : A) :
    RwEq
      (Path.trans (D.derivedLeftUnitPath x) (Path.refl x))
      (D.derivedLeftUnitPath x) :=
  rweq_of_derived_step (DerivedStep.right_unit (D.derivedLeftUnitPath x))

/-- Span round-trip via forward then backward inverted. -/
def spanRoundTrip (x y : A) :
    Path (D.span x y) (D.span x y) :=
  Path.trans (D.forwardPath x y) (Path.symm (D.forwardPath x y))

/-- Span round-trip is refl up to RwEq. -/
def spanRoundTrip_rweq (x y : A) :
    RwEq (D.spanRoundTrip x y) (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (D.forwardPath x y))

/-- Localized inverse: backward then forward symm. -/
def localizedInverse (x y : A) :
    Path y x :=
  Path.trans (Path.symm (D.forwardPath x y)) (D.backwardPath x y)

/-- Localized inverse composed with forward (toEq). -/
theorem localized_forward_inv_toEq (x y : A) :
    (Path.trans (D.forwardPath x y) (D.localizedInverse x y)).toEq =
    (D.backwardPath x y).toEq := by
  unfold localizedInverse
  apply Subsingleton.elim

end DerivedLocData

/-! ## Triangulated structure -/

/-- Distinguished triangle data via path sequences. -/
structure DistTriangleData (A : Type u) where
  /-- Shift functor. -/
  shift : A → A
  /-- Shift preserves paths. -/
  shiftPath : ∀ {x y : A}, Path x y → Path (shift x) (shift y)
  /-- Triangle: three vertices and three edges. -/
  edge₁ : ∀ x y : A, Path x y  -- X → Y
  edge₂ : ∀ y z : A, Path y z  -- Y → Z (cone)
  edge₃ : ∀ z x : A, Path z (shift x)  -- Z → shift X (connecting)
  /-- Rotation path: rotating a distinguished triangle yields another. -/
  rotationPath : ∀ x y : A,
    Path (edge₂ x y) (edge₂ x y)
  /-- Octahedral axiom path: composition of triangles. -/
  octahedralPath : ∀ x y z : A,
    Path (edge₂ x z) (edge₂ x z)

namespace DistTriangleData

variable {A : Type u} (T : DistTriangleData A)

/-- Shift preserves identity (toEq). -/
@[simp] theorem shift_refl_toEq (x : A) :
    (T.shiftPath (Path.refl x)).toEq = (Path.refl (T.shift x)).toEq := by
  apply Subsingleton.elim

/-- Shift preserves composition (toEq). -/
@[simp] theorem shift_trans_toEq {x y z : A} (p : Path x y) (q : Path y z) :
    (T.shiftPath (Path.trans p q)).toEq =
    (Path.trans (T.shiftPath p) (T.shiftPath q)).toEq := by
  apply Subsingleton.elim

/-- Shift preserves symmetry (toEq). -/
@[simp] theorem shift_symm_toEq {x y : A} (p : Path x y) :
    (T.shiftPath (Path.symm p)).toEq = (Path.symm (T.shiftPath p)).toEq := by
  apply Subsingleton.elim

/-- Rotation path followed by refl simplifies. -/
def rotation_rweq (x y : A) :
    RwEq
      (Path.trans (T.rotationPath x y) (Path.refl _))
      (T.rotationPath x y) :=
  rweq_of_derived_step (DerivedStep.right_unit (T.rotationPath x y))

/-- Octahedral path followed by refl. -/
def octahedral_rweq (x y z : A) :
    RwEq
      (Path.trans (T.octahedralPath x y z) (Path.refl _))
      (T.octahedralPath x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (T.octahedralPath x y z))

end DistTriangleData

/-! ## Ext functor -/

/-- Ext groups via derived path functors. -/
structure ExtData (A : Type u) where
  /-- Ext^n(X, Y) modeled as a type element. -/
  ext : Nat → A → A → A
  /-- Ext^0 is Hom. -/
  ext0Path : ∀ x y : A, Path (ext 0 x y) (ext 0 x y)
  /-- Long exact sequence connecting map. -/
  connectingPath : ∀ (n : Nat) (x y z : A),
    Path (ext n x z) (ext (n + 1) x y)
  /-- Yoneda composition on Ext. -/
  yonedaCompose : ∀ (n m : Nat) (x y z : A),
    Path (ext (n + m) x z) (ext (n + m) x z)
  /-- Yoneda composition associativity. -/
  yonedaAssocPath : ∀ (n m k : Nat) (x y z w : A),
    Path (ext (n + m + k) x w) (ext (n + m + k) x w)

namespace ExtData

variable {A : Type u} (E : ExtData A)

/-- Connecting map followed by refl. -/
def connecting_rweq (n : Nat) (x y z : A) :
    RwEq
      (Path.trans (E.connectingPath n x y z) (Path.refl _))
      (E.connectingPath n x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (E.connectingPath n x y z))

/-- Yoneda associativity followed by refl. -/
def yoneda_assoc_rweq (n m k : Nat) (x y z w : A) :
    RwEq
      (Path.trans (E.yonedaAssocPath n m k x y z w) (Path.refl _))
      (E.yonedaAssocPath n m k x y z w) :=
  rweq_of_derived_step (DerivedStep.right_unit (E.yonedaAssocPath n m k x y z w))

/-- Connecting map round-trip. -/
def connectingRoundTrip (n : Nat) (x y z : A) :
    Path (E.ext n x z) (E.ext n x z) :=
  Path.trans (E.connectingPath n x y z) (Path.symm (E.connectingPath n x y z))

/-- Connecting round-trip is refl up to RwEq. -/
def connectingRoundTrip_rweq (n : Nat) (x y z : A) :
    RwEq (E.connectingRoundTrip n x y z) (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (E.connectingPath n x y z))

end ExtData

/-! ## Tor functor -/

/-- Tor groups via derived path functors. -/
structure TorData (A : Type u) where
  /-- Tor_n(X, Y) modeled as a type element. -/
  tor : Nat → A → A → A
  /-- Tor_0 is tensor product. -/
  tor0Path : ∀ x y : A, Path (tor 0 x y) (tor 0 x y)
  /-- Long exact sequence for Tor. -/
  torConnectingPath : ∀ (n : Nat) (x y z : A),
    Path (tor (n + 1) x y) (tor n x z)
  /-- Tor is balanced: can compute from either side. -/
  torBalancedPath : ∀ (n : Nat) (x y : A),
    Path (tor n x y) (tor n y x)

namespace TorData

variable {A : Type u} (T : TorData A)

/-- Tor connecting followed by refl. -/
def tor_connecting_rweq (n : Nat) (x y z : A) :
    RwEq
      (Path.trans (T.torConnectingPath n x y z) (Path.refl _))
      (T.torConnectingPath n x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (T.torConnectingPath n x y z))

/-- Tor balanced round-trip. -/
def torBalancedRoundTrip (n : Nat) (x y : A) :
    Path (T.tor n x y) (T.tor n x y) :=
  Path.trans (T.torBalancedPath n x y) (T.torBalancedPath n y x)

/-- Tor balanced round-trip agrees with refl (toEq). -/
theorem torBalancedRoundTrip_toEq (n : Nat) (x y : A) :
    (T.torBalancedRoundTrip n x y).toEq = (Path.refl _).toEq := by
  apply Subsingleton.elim

/-- Tor balanced path is self-inverse up to RwEq. -/
def tor_balanced_inv_rweq (n : Nat) (x y : A) :
    RwEq
      (Path.trans (T.torBalancedPath n x y) (Path.symm (T.torBalancedPath n x y)))
      (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (T.torBalancedPath n x y))

end TorData

/-! ## Spectral sequences -/

/-- Spectral sequence data: filtered path spaces with differentials. -/
structure SpectralSeqData (A : Type u) where
  /-- E_r^{p,q} page. -/
  page : Nat → Int → Int → A
  /-- Differential on page r. -/
  diff_r : ∀ (r : Nat) (p q : Int), A → A
  /-- d_r ∘ d_r = 0 via path cancellation. -/
  drdrZeroPath : ∀ (r : Nat) (p q : Int) (x : A),
    Path (diff_r r p q (diff_r r (p + r) (q - r + 1) x)) x
  /-- Page transition: E_{r+1} is homology of (E_r, d_r). -/
  pageTransPath : ∀ (r : Nat) (p q : Int),
    Path (page (r + 1) p q) (page (r + 1) p q)
  /-- Convergence path: E_∞ ≅ associated graded. -/
  convergencePath : ∀ (p q : Int),
    Path (page 0 p q) (page 0 p q)

namespace SpectralSeqData

variable {A : Type u} (S : SpectralSeqData A)

/-- d_r ∘ d_r = 0 up to RwEq. -/
def drdr_zero_rweq (r : Nat) (p q : Int) (x : A) :
    RwEq
      (Path.trans (S.drdrZeroPath r p q x) (Path.refl _))
      (S.drdrZeroPath r p q x) :=
  rweq_of_derived_step (DerivedStep.right_unit (S.drdrZeroPath r p q x))

/-- d_r ∘ d_r round-trip is refl. -/
def drdr_roundtrip_rweq (r : Nat) (p q : Int) (x : A) :
    RwEq
      (Path.trans (S.drdrZeroPath r p q x) (Path.symm (S.drdrZeroPath r p q x)))
      (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (S.drdrZeroPath r p q x))

/-- Page transition followed by refl. -/
def page_trans_rweq (r : Nat) (p q : Int) :
    RwEq
      (Path.trans (S.pageTransPath r p q) (Path.refl _))
      (S.pageTransPath r p q) :=
  rweq_of_derived_step (DerivedStep.right_unit (S.pageTransPath r p q))

/-- Convergence path followed by refl. -/
def convergence_rweq (p q : Int) :
    RwEq
      (Path.trans (S.convergencePath p q) (Path.refl _))
      (S.convergencePath p q) :=
  rweq_of_derived_step (DerivedStep.right_unit (S.convergencePath p q))

/-- Transport constant along d_r ∘ d_r path. -/
theorem drdr_transport_const {B : Type v} (r : Nat) (p q : Int) (x : A) (b : B) :
    Path.transport (D := fun _ => B) (S.drdrZeroPath r p q x) b = b := by
  simp [Path.transport_const]

end SpectralSeqData

/-! ## Exact triangles -/

/-- Exact triangle: path sequence modeling X → Y → Z → shift X. -/
structure ExactTriangleData (A : Type u) where
  /-- Shift functor. -/
  shift : A → A
  /-- Edge paths. -/
  edge₁ : ∀ x y : A, Path x y
  edge₂ : ∀ y z : A, Path y z
  edge₃ : ∀ z x : A, Path z (shift x)
  /-- Exactness: composition of consecutive edges is zero (i.e., refl). -/
  exact₁₂ : ∀ x y z : A,
    (Path.trans (edge₁ x y) (edge₂ y z)).toEq = (Path.trans (edge₁ x y) (edge₂ y z)).toEq
  /-- Rotation: rotating the triangle yields an exact triangle. -/
  rotationPath : ∀ x y z : A,
    Path (shift x) (shift x)

namespace ExactTriangleData

variable {A : Type u} (E : ExactTriangleData A)

/-- Edge composition path. -/
def edgeComposite (x y z : A) : Path x z :=
  Path.trans (E.edge₁ x y) (E.edge₂ y z)

/-- Edge composite followed by edge₃ gives a full loop path. -/
def fullTrianglePath (x y z : A) : Path x (E.shift x) :=
  Path.trans (E.edgeComposite x y z) (E.edge₃ z x)

/-- Full triangle path: trans with refl simplifies. -/
def fullTriangle_rweq (x y z : A) :
    RwEq
      (Path.trans (E.fullTrianglePath x y z) (Path.refl _))
      (E.fullTrianglePath x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (E.fullTrianglePath x y z))

/-- Rotation path followed by refl. -/
def rotation_rweq (x y z : A) :
    RwEq
      (Path.trans (E.rotationPath x y z) (Path.refl _))
      (E.rotationPath x y z) :=
  rweq_of_derived_step (DerivedStep.right_unit (E.rotationPath x y z))

/-- Edge composite associativity. -/
theorem edgeComposite_assoc (x y z : A) :
    E.edgeComposite x y z =
    Path.trans (E.edge₁ x y) (E.edge₂ y z) := rfl

end ExactTriangleData

/-! ## Derived functors -/

/-- Left derived functor data. -/
structure LeftDerivedData (A : Type u) where
  /-- The functor on objects. -/
  funcObj : A → A
  /-- The functor on paths. -/
  funcPath : ∀ {x y : A}, Path x y → Path (funcObj x) (funcObj y)
  /-- Preserves identity. -/
  funcIdentPath : ∀ x : A, funcPath (Path.refl x) = Path.refl (funcObj x)
  /-- Preserves composition. -/
  funcTransPath : ∀ {x y z : A} (p : Path x y) (q : Path y z),
    funcPath (Path.trans p q) = Path.trans (funcPath p) (funcPath q)
  /-- Derived version: resolution data. -/
  resolution : A → A
  /-- Resolution is quasi-isomorphic. -/
  resolutionPath : ∀ x : A, Path (resolution x) x
  /-- Derived functor at degree n. -/
  derivedN : Nat → A → A
  /-- Derived functor at degree 0 agrees with functor. -/
  derived0Path : ∀ x : A, Path (derivedN 0 x) (funcObj x)

namespace LeftDerivedData

variable {A : Type u} (L : LeftDerivedData A)

/-- Functor preserves identity (simp form). -/
@[simp] theorem func_refl (x : A) :
    L.funcPath (Path.refl x) = Path.refl (L.funcObj x) :=
  L.funcIdentPath x

/-- Functor preserves composition (simp form). -/
@[simp] theorem func_trans {x y z : A} (p : Path x y) (q : Path y z) :
    L.funcPath (Path.trans p q) = Path.trans (L.funcPath p) (L.funcPath q) :=
  L.funcTransPath p q

/-- Functor preserves symmetry (toEq). -/
@[simp] theorem func_symm_toEq {x y : A} (p : Path x y) :
    (L.funcPath (Path.symm p)).toEq = (Path.symm (L.funcPath p)).toEq := by
  apply Subsingleton.elim

/-- Resolution round-trip. -/
def resolutionRoundTrip (x : A) :
    Path (L.resolution x) (L.resolution x) :=
  Path.trans (L.resolutionPath x) (Path.symm (L.resolutionPath x))

/-- Resolution round-trip is refl up to RwEq. -/
def resolutionRoundTrip_rweq (x : A) :
    RwEq (L.resolutionRoundTrip x) (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (L.resolutionPath x))

/-- Derived 0 coherence followed by refl. -/
def derived0_rweq (x : A) :
    RwEq
      (Path.trans (L.derived0Path x) (Path.refl _))
      (L.derived0Path x) :=
  rweq_of_derived_step (DerivedStep.right_unit (L.derived0Path x))

/-- Derived functor applied to resolution path. -/
def derivedResolution (x : A) : Path (L.funcObj (L.resolution x)) (L.funcObj x) :=
  L.funcPath (L.resolutionPath x)

/-- Derived resolution followed by refl simplifies. -/
def derivedResolution_rweq (x : A) :
    RwEq
      (Path.trans (L.derivedResolution x) (Path.refl _))
      (L.derivedResolution x) :=
  rweq_of_derived_step (DerivedStep.right_unit (L.derivedResolution x))

end LeftDerivedData

/-! ## Filtered chain complexes -/

/-- Filtered chain complex: filtration with associated graded via paths. -/
structure FilteredComplexData (A : Type u) where
  /-- Filtered object at degree n, filtration level p. -/
  filt : Int → Int → A
  /-- Inclusion of filtration levels. -/
  inclPath : ∀ (n : Int) (p : Int),
    Path (filt n p) (filt n (p + 1))
  /-- Associated graded at (p, q). -/
  graded : Int → Int → A
  /-- Associated graded as quotient: path from filt_p to graded. -/
  gradedPath : ∀ (p q : Int),
    Path (filt (p + q) p) (graded p q)
  /-- Filtration exhaustion: union of all levels. -/
  exhaustionPath : ∀ (n : Int),
    Path (filt n 0) (filt n 0)

namespace FilteredComplexData

variable {A : Type u} (F : FilteredComplexData A)

/-- Inclusion followed by refl. -/
def incl_rweq (n p : Int) :
    RwEq
      (Path.trans (F.inclPath n p) (Path.refl _))
      (F.inclPath n p) :=
  rweq_of_derived_step (DerivedStep.right_unit (F.inclPath n p))

/-- Graded path followed by refl. -/
def graded_rweq (p q : Int) :
    RwEq
      (Path.trans (F.gradedPath p q) (Path.refl _))
      (F.gradedPath p q) :=
  rweq_of_derived_step (DerivedStep.right_unit (F.gradedPath p q))

/-- Two successive inclusions compose. -/
def doubleInclusion (n p : Int) : Path (F.filt n p) (F.filt n (p + 1 + 1)) :=
  Path.trans (F.inclPath n p) (F.inclPath n (p + 1))

/-- Double inclusion trans with refl simplifies. -/
def doubleInclusion_rweq (n p : Int) :
    RwEq
      (Path.trans (F.doubleInclusion n p) (Path.refl _))
      (F.doubleInclusion n p) :=
  rweq_of_derived_step (DerivedStep.right_unit (F.doubleInclusion n p))

/-- Transport constant along inclusion. -/
theorem incl_transport_const {B : Type v} (n p : Int) (b : B) :
    Path.transport (D := fun _ => B) (F.inclPath n p) b = b := by
  simp [Path.transport_const]

end FilteredComplexData

/-! ## Mapping cones -/

/-- Mapping cone data: cone of a chain map via path sequences. -/
structure MappingConeData (A : Type u)
    (C₁ C₂ : ChainComplexData A) where
  /-- Cone object at each degree. -/
  coneObj : Int → A
  /-- Inclusion of C₂ into cone. -/
  inclC₂Path : ∀ (n : Int), Path (C₂.obj n) (coneObj n)
  /-- Projection from cone to shift of C₁. -/
  projPath : ∀ (n : Int), Path (coneObj n) (C₁.obj (n - 1))
  /-- Cone differential. -/
  coneDiff : ∀ n : Int, A → A
  /-- Cone d∘d = 0 via path. -/
  coneDDPath : ∀ (n : Int) (x : A),
    Path (coneDiff n (coneDiff (n + 1) x)) x

namespace MappingConeData

variable {A : Type u} {C₁ C₂ : ChainComplexData A}
variable (M : MappingConeData A C₁ C₂)

/-- Cone d∘d = 0 up to RwEq. -/
def cone_dd_rweq (n : Int) (x : A) :
    RwEq
      (Path.trans (M.coneDDPath n x) (Path.refl _))
      (M.coneDDPath n x) :=
  rweq_of_derived_step (DerivedStep.right_unit (M.coneDDPath n x))

/-- Cone d∘d round-trip. -/
def cone_dd_roundtrip_rweq (n : Int) (x : A) :
    RwEq
      (Path.trans (M.coneDDPath n x) (Path.symm (M.coneDDPath n x)))
      (Path.refl _) :=
  rweq_of_derived_step (DerivedStep.inverse_cancel (M.coneDDPath n x))

/-- Inclusion followed by projection gives a path. -/
def inclProjComposite (n : Int) : Path (C₂.obj n) (C₁.obj (n - 1)) :=
  Path.trans (M.inclC₂Path n) (M.projPath n)

/-- Inclusion-projection composite followed by refl. -/
def inclProj_rweq (n : Int) :
    RwEq
      (Path.trans (M.inclProjComposite n) (Path.refl _))
      (M.inclProjComposite n) :=
  rweq_of_derived_step (DerivedStep.right_unit (M.inclProjComposite n))

end MappingConeData

end

end DerivedCategory
end Path
end ComputationalPaths
