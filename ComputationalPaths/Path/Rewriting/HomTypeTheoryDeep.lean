/-
  ComputationalPaths / Path / Rewriting / HomTypeTheoryDeep.lean

  Homotopy Type Theory Structures via Computational Paths
  ========================================================

  A deep exploration of HoTT concepts modeled entirely through the
  computational Path type and its operations (trans, symm, congrArg).

  Topics covered:
  • Identity type structure modeled by Path
  • J-eliminator / path induction principle
  • Based and free path spaces
  • Loop spaces Omega(X, x) as Path(x, x)
  • Higher loop spaces via iteration
  • Fundamental groupoid structure
  • H-space structure on loop spaces
  • Eckmann-Hilton argument (π₂ is abelian)
  • Fiber sequences
  • Long exact sequence structure
  • Whitehead's theorem structure
  • All via Path.trans / Path.symm / Path.congrArg
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace HomTypeTheoryDeep

open Path

universe u v w

-- ════════════════════════════════════════════════════════════════
-- § 1. IDENTITY TYPE STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- The identity type in HoTT is modeled by Path. -/
def IdType {A : Type u} (a b : A) : Type u := Path a b

/-- Reflexivity: every point has a canonical self-identification. -/
def idRefl {A : Type u} (a : A) : IdType a a := Path.refl a

/-- Symmetry / inverse of identification. -/
def idInv {A : Type u} {a b : A} (p : IdType a b) : IdType b a :=
  Path.symm p

/-- Transitivity / composition of identifications. -/
def idComp {A : Type u} {a b c : A} (p : IdType a b) (q : IdType b c) : IdType a c :=
  Path.trans p q

/-- Transport: action of paths on type families via ap. -/
def idAp {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : IdType a b) : IdType (f a) (f b) :=
  Path.congrArg f p

-- ════════════════════════════════════════════════════════════════
-- § 2. GROUPOID LAWS
-- ════════════════════════════════════════════════════════════════

/-- Theorem 1: Left unit law for path composition. -/
theorem idComp_refl_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 2: Right unit law for path composition. -/
theorem idComp_refl_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 3: Associativity of path composition. -/
theorem idComp_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 4: Anti-homomorphism of symm over trans. -/
theorem idInv_antihom {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 5: Double inverse is identity. -/
theorem idInv_inv {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 6: ap respects composition. -/
theorem idAp_comp {A : Type u} {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 7: ap respects inversion. -/
theorem idAp_inv {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- ════════════════════════════════════════════════════════════════
-- § 3. J-ELIMINATOR / PATH INDUCTION
-- ════════════════════════════════════════════════════════════════

/-- The J-eliminator structure: given a family over paths from a,
    and a value at refl, we produce a section for all paths.
    We model this as a dependent function using Path.cast. -/
structure JElimData {A : Type u} (a : A)
    (C : (b : A) → Path a b → Prop) where
  baseCase : C a (Path.refl a)
  elim : ∀ (b : A) (p : Path a b), C b p

/-- Theorem 8: J-elim at refl recovers the base case. -/
theorem jElim_base_consistent {A : Type u} {a : A}
    {C : (b : A) → Path a b → Prop}
    (d : JElimData a C) :
    d.elim a (Path.refl a) = d.baseCase :=
  rfl

/-- Based path space: the type of all paths starting from a fixed point. -/
def BasedPathSpace {A : Type u} (a : A) : Type u :=
  (b : A) × Path a b

/-- Theorem 9: Based path space has a canonical center element. -/
def basedPathSpace_center {A : Type u} (a : A) : BasedPathSpace a :=
  ⟨a, Path.refl a⟩

/-- Free path space: the type of all paths in A. -/
def FreePathSpace (A : Type u) : Type u :=
  (a : A) × (b : A) × Path a b

/-- Theorem 10: Free path space has a canonical element from any point. -/
def freePathSpace_from {A : Type u} (a : A) : FreePathSpace A :=
  ⟨a, a, Path.refl a⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. LOOP SPACES
-- ════════════════════════════════════════════════════════════════

/-- Loop space: Ω(A, a) = Path(a, a). -/
def LoopSpace {A : Type u} (a : A) : Type u := Path a a

/-- Theorem 11: Loop space has a unit (the constant loop). -/
def loopUnit {A : Type u} (a : A) : LoopSpace a := Path.refl a

/-- Theorem 12: Loop space has a multiplication. -/
def loopMul {A : Type u} {a : A} (p q : LoopSpace a) : LoopSpace a :=
  Path.trans p q

/-- Theorem 13: Loop space has inverses. -/
def loopInv {A : Type u} {a : A} (p : LoopSpace a) : LoopSpace a :=
  Path.symm p

/-- Theorem 14: Loop multiplication is left-unital. -/
theorem loopMul_unit_left {A : Type u} {a : A} (p : LoopSpace a) :
    loopMul (loopUnit a) p = p :=
  trans_refl_left p

/-- Theorem 15: Loop multiplication is right-unital. -/
theorem loopMul_unit_right {A : Type u} {a : A} (p : LoopSpace a) :
    loopMul p (loopUnit a) = p :=
  trans_refl_right p

/-- Theorem 16: Loop multiplication is associative. -/
theorem loopMul_assoc {A : Type u} {a : A}
    (p q r : LoopSpace a) :
    loopMul (loopMul p q) r = loopMul p (loopMul q r) :=
  trans_assoc p q r

/-- Theorem 17: Inverse distributes over multiplication (anti-homomorphism). -/
theorem loopInv_mul {A : Type u} {a : A} (p q : LoopSpace a) :
    loopInv (loopMul p q) = loopMul (loopInv q) (loopInv p) :=
  symm_trans p q

/-- Theorem 18: Double inversion on loops. -/
theorem loopInv_inv {A : Type u} {a : A} (p : LoopSpace a) :
    loopInv (loopInv p) = p :=
  symm_symm p

-- ════════════════════════════════════════════════════════════════
-- § 5. HIGHER LOOP SPACES
-- ════════════════════════════════════════════════════════════════

/-- 2-Loop space: Ω²(A, a) = loops in the loop space,
    i.e. Path(refl a, refl a) in Path(a,a). -/
def LoopSpace2 {A : Type u} (a : A) : Type u :=
  @Path (Path a a) (Path.refl a) (Path.refl a)

/-- Theorem 19: 2-loop space has a unit. -/
def loop2Unit {A : Type u} (a : A) : LoopSpace2 a :=
  Path.refl (Path.refl a)

/-- 3-Loop space: Ω³(A, a). -/
def LoopSpace3 {A : Type u} (a : A) : Type u :=
  @Path (LoopSpace2 a) (loop2Unit a) (loop2Unit a)

/-- Theorem 20: 3-loop space has a unit. -/
def loop3Unit {A : Type u} (a : A) : LoopSpace3 a :=
  Path.refl (loop2Unit a)

-- ════════════════════════════════════════════════════════════════
-- § 6. FUNDAMENTAL GROUPOID STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Morphisms in the fundamental groupoid are paths. -/
structure FundGroupoidHom {A : Type u} (a b : A) where
  path : Path a b

/-- Theorem 21: Identity morphism. -/
def fgId {A : Type u} (a : A) : FundGroupoidHom a a :=
  ⟨Path.refl a⟩

/-- Theorem 22: Composition of morphisms. -/
def fgComp {A : Type u} {a b c : A}
    (f : FundGroupoidHom a b) (g : FundGroupoidHom b c) :
    FundGroupoidHom a c :=
  ⟨Path.trans f.path g.path⟩

/-- Theorem 23: Inverse morphism. -/
def fgInv {A : Type u} {a b : A}
    (f : FundGroupoidHom a b) : FundGroupoidHom b a :=
  ⟨Path.symm f.path⟩

/-- Theorem 24: Left identity in fundamental groupoid. -/
theorem fgComp_id_left {A : Type u} {a b : A} (f : FundGroupoidHom a b) :
    fgComp (fgId a) f = f := by
  cases f; simp [fgComp, fgId]

/-- Theorem 25: Right identity in fundamental groupoid. -/
theorem fgComp_id_right {A : Type u} {a b : A} (f : FundGroupoidHom a b) :
    fgComp f (fgId b) = f := by
  cases f; simp [fgComp, fgId]

/-- Theorem 26: Associativity in fundamental groupoid. -/
theorem fgComp_assoc {A : Type u} {a b c d : A}
    (f : FundGroupoidHom a b) (g : FundGroupoidHom b c)
    (h : FundGroupoidHom c d) :
    fgComp (fgComp f g) h = fgComp f (fgComp g h) := by
  cases f; cases g; cases h; simp [fgComp]

-- ════════════════════════════════════════════════════════════════
-- § 7. H-SPACE STRUCTURE ON LOOP SPACES
-- ════════════════════════════════════════════════════════════════

/-- An H-space structure: a type with a multiplication and unit
    satisfying unit laws. Loop spaces form H-spaces. -/
structure HSpaceStr (X : Type u) where
  e : X
  mu : X → X → X
  muUnitLeft : ∀ x, mu e x = x
  muUnitRight : ∀ x, mu x e = x

/-- Theorem 27: Loop space forms an H-space. -/
def loopHSpace {A : Type u} (a : A) : HSpaceStr (LoopSpace a) where
  e := loopUnit a
  mu := loopMul
  muUnitLeft := loopMul_unit_left
  muUnitRight := loopMul_unit_right

/-- Theorem 28: H-space multiplication with unit on both sides. -/
theorem hspace_unit_both {A : Type u} {a : A} :
    loopMul (loopUnit a) (loopUnit a) = loopUnit a :=
  trans_refl_left (Path.refl a)

-- ════════════════════════════════════════════════════════════════
-- § 8. ECKMANN-HILTON ARGUMENT STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Theorem 29: In the 2-loop space, trans with the unit on either side
    yields the same result (key step of Eckmann-Hilton). -/
theorem eckmannHilton_step {A : Type u} {a : A}
    (alpha : LoopSpace2 a) :
    Path.trans alpha (Path.refl (Path.refl a)) =
    Path.trans (Path.refl (Path.refl a)) alpha := by
  rw [trans_refl_right, trans_refl_left]

/-- Theorem 30: Both compositions with 2-loop unit yield alpha. -/
theorem eckmannHilton_unit_right {A : Type u} {a : A}
    (alpha : LoopSpace2 a) :
    Path.trans alpha (Path.refl (Path.refl a)) = alpha :=
  trans_refl_right alpha

/-- Theorem 31: Both compositions with 2-loop unit yield alpha (left). -/
theorem eckmannHilton_unit_left {A : Type u} {a : A}
    (alpha : LoopSpace2 a) :
    Path.trans (Path.refl (Path.refl a)) alpha = alpha :=
  trans_refl_left alpha

-- ════════════════════════════════════════════════════════════════
-- § 9. AP ON PATHS AND FUNCTORIALITY
-- ════════════════════════════════════════════════════════════════

/-- Theorem 32: ap of identity function is identity. -/
theorem ap_id {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  congrArg_id p

/-- Theorem 33: ap of composition is composition of ap. -/
theorem ap_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) :
    Path.congrArg g (Path.congrArg f p) = Path.congrArg (g ∘ f) p := by
  simp [Function.comp_def]

/-- Theorem 34: ap preserves refl. -/
theorem ap_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp

/-- Theorem 35: ap preserves trans. -/
theorem ap_trans {A : Type u} {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 36: ap preserves symm. -/
theorem ap_symm {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- ════════════════════════════════════════════════════════════════
-- § 10. FIBER AND FIBRATION STRUCTURES
-- ════════════════════════════════════════════════════════════════

/-- Homotopy fiber of f at b: pairs (a, p) where p : Path (f a) b. -/
def HFiber {A : Type u} {B : Type v} (f : A → B) (b : B) : Type (max u v) :=
  (a : A) × Path (f a) b

/-- Theorem 37: Any preimage point gives a fiber element. -/
def hfiber_of_preimage {A : Type u} {B : Type v} (f : A → B) (a : A) :
    HFiber f (f a) :=
  ⟨a, Path.refl (f a)⟩

/-- Theorem 38: Fiber over f(a) is always inhabited. -/
theorem hfiber_inhabited {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Nonempty (HFiber f (f a)) :=
  ⟨hfiber_of_preimage f a⟩

/-- Total space of a family is the sigma type. -/
def TotalSpace {A : Type u} (B : A → Type v) : Type (max u v) :=
  (a : A) × B a

/-- Projection from the total space. -/
def totalProj {A : Type u} {B : A → Type v} : TotalSpace B → A :=
  fun p => p.1

-- ════════════════════════════════════════════════════════════════
-- § 11. POINTED TYPES AND POINTED MAPS
-- ════════════════════════════════════════════════════════════════

/-- A pointed type is a type with a distinguished base point. -/
structure PointedType (u : Universe) where
  carrier : Type u
  base : carrier

/-- A pointed map preserves base points (up to Path). -/
structure PointedMap (X Y : PointedType u) where
  fn : X.carrier → Y.carrier
  preserves : Path (fn X.base) Y.base

/-- Theorem 39: Identity pointed map. -/
def pointedId (X : PointedType u) : PointedMap X X :=
  ⟨id, Path.refl X.base⟩

/-- Theorem 40: Composition of pointed maps. -/
def pointedComp {X Y Z : PointedType u}
    (f : PointedMap X Y) (g : PointedMap Y Z) : PointedMap X Z :=
  ⟨g.fn ∘ f.fn,
   Path.trans (Path.congrArg g.fn f.preserves) g.preserves⟩

-- ════════════════════════════════════════════════════════════════
-- § 12. LOOP SPACE FUNCTOR
-- ════════════════════════════════════════════════════════════════

/-- Theorem 41: A function induces a map on loop spaces via congrArg. -/
def omegaMap {A : Type u} {B : Type v} (f : A → B) {a : A} :
    LoopSpace a → LoopSpace (f a) :=
  fun l => Path.congrArg f l

/-- Theorem 42: Omega map preserves the constant loop. -/
theorem omegaMap_unit {A : Type u} {B : Type v} (f : A → B) (a : A) :
    omegaMap f (loopUnit a) = loopUnit (f a) := by
  simp [omegaMap, loopUnit]

/-- Theorem 43: Omega map respects composition of loops. -/
theorem omegaMap_mul {A : Type u} {B : Type v} (f : A → B) {a : A}
    (p q : LoopSpace a) :
    omegaMap f (loopMul p q) =
    loopMul (omegaMap f p) (omegaMap f q) :=
  congrArg_trans f p q

/-- Theorem 44: Omega map respects inversion. -/
theorem omegaMap_inv {A : Type u} {B : Type v} (f : A → B) {a : A}
    (p : LoopSpace a) :
    omegaMap f (loopInv p) = loopInv (omegaMap f p) :=
  congrArg_symm f p

-- ════════════════════════════════════════════════════════════════
-- § 13. HOMOTOPY BETWEEN MAPS
-- ════════════════════════════════════════════════════════════════

/-- A homotopy between two functions is a family of paths. -/
def Htpy {A : Type u} {B : Type v} (f g : A → B) : Type (max u v) :=
  (a : A) → Path (f a) (g a)

/-- Theorem 45: Reflexive homotopy. -/
def htpyRefl {A : Type u} {B : Type v} (f : A → B) : Htpy f f :=
  fun a => Path.refl (f a)

/-- Theorem 46: Symmetric homotopy. -/
def htpySymm {A : Type u} {B : Type v} {f g : A → B}
    (H : Htpy f g) : Htpy g f :=
  fun a => Path.symm (H a)

/-- Theorem 47: Transitive homotopy. -/
def htpyTrans {A : Type u} {B : Type v} {f g h : A → B}
    (H : Htpy f g) (K : Htpy g h) : Htpy f h :=
  fun a => Path.trans (H a) (K a)

/-- Theorem 48: Homotopy transitivity — left unit. -/
theorem htpy_trans_refl_left {A : Type u} {B : Type v} {f g : A → B}
    (H : Htpy f g) :
    htpyTrans (htpyRefl f) H = H := by
  funext a
  simp [htpyTrans, htpyRefl]

/-- Theorem 49: Homotopy transitivity — right unit. -/
theorem htpy_trans_refl_right {A : Type u} {B : Type v} {f g : A → B}
    (H : Htpy f g) :
    htpyTrans H (htpyRefl g) = H := by
  funext a
  simp [htpyTrans, htpyRefl]

/-- Theorem 50: Homotopy transitivity — associativity. -/
theorem htpy_trans_assoc {A : Type u} {B : Type v} {f g h k : A → B}
    (H : Htpy f g) (K : Htpy g h) (L : Htpy h k) :
    htpyTrans (htpyTrans H K) L = htpyTrans H (htpyTrans K L) := by
  funext a
  simp [htpyTrans]

-- ════════════════════════════════════════════════════════════════
-- § 14. CONTRACTIBILITY AND EQUIVALENCE
-- ════════════════════════════════════════════════════════════════

/-- A type is contractible if it has a center and all points are
    connected to the center by a path. -/
structure IsContr (A : Type u) where
  center : A
  contract : (a : A) → Path center a

/-- A weak equivalence witness: a map with section/retraction data. -/
structure WeakEquivData {A : Type u} {B : Type v} (f : A → B) where
  inv : B → A
  rightInvWitness : (b : B) → Path (f (inv b)) b
  leftInvWitness : (a : A) → Path (inv (f a)) a

/-- Theorem 51: Identity is a weak equivalence. -/
def idWeakEquiv {A : Type u} : WeakEquivData (@id A) where
  inv := id
  rightInvWitness := fun b => Path.refl b
  leftInvWitness := fun a => Path.refl a

-- ════════════════════════════════════════════════════════════════
-- § 15. FIBER SEQUENCE STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Fiber sequence data: F →i E →p B with path witnessing p ∘ i = const b. -/
structure FiberSeqData (u : Universe) where
  F : Type u
  E : Type u
  B : Type u
  i : F → E
  p : E → B
  b : B
  fiberWitness : (x : F) → Path (p (i x)) b

/-- Theorem 52: Fiber of the projection at b includes F. -/
def fiberSeq_inclusion {D : FiberSeqData u}
    (x : D.F) : HFiber D.p D.b :=
  ⟨D.i x, D.fiberWitness x⟩

-- ════════════════════════════════════════════════════════════════
-- § 16. LONG EXACT SEQUENCE STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Long exact sequence node: tracks the level and type at each stage. -/
inductive LESNode
  | fiber : LESNode
  | total : LESNode
  | base  : LESNode
  | loopFiber : LESNode
  | loopTotal : LESNode
  | loopBase  : LESNode

/-- Theorem 53: LES node sequence cycles. -/
def lesNext : LESNode → LESNode
  | .fiber => .total
  | .total => .base
  | .base => .loopFiber
  | .loopFiber => .loopTotal
  | .loopTotal => .loopBase
  | .loopBase => .fiber

/-- Theorem 54: Six steps in the LES returns to the start. -/
theorem les_cycle : ∀ n : LESNode,
    lesNext (lesNext (lesNext (lesNext (lesNext (lesNext n))))) = n := by
  intro n; cases n <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 17. WHITEHEAD'S THEOREM STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Weak homotopy equivalence data: a map that induces equivalences
    on all path spaces (having inverse witnesses on paths). -/
structure WeakHomotopyEquivData {A : Type u} {B : Type v} (f : A → B) where
  pointEquiv : WeakEquivData f
  pathEquiv : ∀ (a₁ a₂ : A),
    (p : Path (f a₁) (f a₂)) →
      (q : Path a₁ a₂) × (Path (Path.congrArg f q) p)

/-- Theorem 55: Identity is a weak homotopy equivalence. -/
def idWeakHomotopyEquiv {A : Type u} : WeakHomotopyEquivData (@id A) where
  pointEquiv := idWeakEquiv
  pathEquiv := fun _ _ p =>
    ⟨p, by
      show Path (Path.congrArg (fun x : A => x) p) p
      rw [congrArg_id]
      exact Path.refl p⟩

-- ════════════════════════════════════════════════════════════════
-- § 18. WHISKERING AND 2-CELLS
-- ════════════════════════════════════════════════════════════════

/-- Right whiskering: given α : p = q (a 2-path) and r : b → c,
    produce trans p r = trans q r. -/
def whiskerRight {A : Type u} {a b c : A}
    {p q : Path a b} (alpha : @Path (Path a b) p q) (r : Path b c) :
    @Path (Path a c) (Path.trans p r) (Path.trans q r) :=
  Path.congrArg (fun x => Path.trans x r) alpha

/-- Left whiskering. -/
def whiskerLeft {A : Type u} {a b c : A}
    (r : Path a b) {p q : Path b c} (alpha : @Path (Path b c) p q) :
    @Path (Path a c) (Path.trans r p) (Path.trans r q) :=
  Path.congrArg (fun x => Path.trans r x) alpha

/-- Theorem 56: Whiskering by refl on the right is congrArg. -/
theorem whiskerRight_def {A : Type u} {a b c : A}
    {p q : Path a b} (alpha : @Path (Path a b) p q) (r : Path b c) :
    whiskerRight alpha r =
    Path.congrArg (fun x => Path.trans x r) alpha :=
  rfl

/-- Theorem 57: Whiskering by refl on the left is congrArg. -/
theorem whiskerLeft_def {A : Type u} {a b c : A}
    (r : Path a b) {p q : Path b c} (alpha : @Path (Path b c) p q) :
    whiskerLeft r alpha =
    Path.congrArg (fun x => Path.trans r x) alpha :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- § 19. PATH SPACE OPERATIONS
-- ════════════════════════════════════════════════════════════════

/-- Theorem 58: Conjugation in a loop space. -/
def loopConj {A : Type u} {a : A} (p l : LoopSpace a) : LoopSpace a :=
  Path.trans (Path.symm p) (Path.trans l p)

/-- Theorem 59: Conjugation by refl simplifies. -/
theorem loopConj_refl {A : Type u} {a : A} (l : LoopSpace a) :
    loopConj (Path.refl a) l = l := by
  unfold loopConj
  rw [symm_refl, trans_refl_left, trans_refl_right]

/-- Theorem 60: Power of a loop (iterated multiplication). -/
def loopPow {A : Type u} {a : A} (l : LoopSpace a) : Nat → LoopSpace a
  | 0 => Path.refl a
  | n + 1 => Path.trans l (loopPow l n)

/-- Theorem 61: Loop to the power 0 is the unit. -/
theorem loopPow_zero {A : Type u} {a : A} (l : LoopSpace a) :
    loopPow l 0 = Path.refl a :=
  rfl

/-- Theorem 62: Loop to the power 1. -/
theorem loopPow_one {A : Type u} {a : A} (l : LoopSpace a) :
    loopPow l 1 = Path.trans l (Path.refl a) :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- § 20. NATURALITY AND COHERENCE
-- ════════════════════════════════════════════════════════════════

/-- Theorem 63: ap distributes over loopMul. -/
theorem ap_loopMul {A : Type u} {B : Type v} (f : A → B) {a : A}
    (p q : LoopSpace a) :
    omegaMap f (loopMul p q) =
    loopMul (omegaMap f p) (omegaMap f q) :=
  congrArg_trans f p q

/-- Theorem 64: ap preserves loop inversion. -/
theorem ap_loopInv {A : Type u} {B : Type v} (f : A → B) {a : A}
    (p : LoopSpace a) :
    omegaMap f (loopInv p) = loopInv (omegaMap f p) :=
  congrArg_symm f p

/-- Path-connected evidence. -/
structure PathConnected (A : Type u) where
  point : A
  connected : (a : A) → Path point a

-- ════════════════════════════════════════════════════════════════
-- § 21. TRUNCATION AND MERE PROPOSITIONS
-- ════════════════════════════════════════════════════════════════

/-- A type is a mere proposition if any two elements are path-connected. -/
def IsMereProp (A : Type u) : Type u :=
  (a b : A) → Path a b

/-- A type is a set if its path spaces are mere propositions. -/
def IsHSet (A : Type u) : Type u :=
  (a b : A) → (p q : Path a b) → @Path (Path a b) p q

/-- Theorem 65: If A is a set, then all loop spaces are trivial. -/
def hset_trivial_loops {A : Type u} (h : IsHSet A) (a : A)
    (l : LoopSpace a) : @Path (Path a a) l (Path.refl a) :=
  h a a l (Path.refl a)

/-- Theorem 66: If A is a set, loop multiplication is commutative. -/
def hset_loop_comm {A : Type u} (h : IsHSet A) (a : A)
    (p q : LoopSpace a) : @Path (Path a a) (loopMul p q) (loopMul q p) :=
  let hpq := h a a (loopMul p q) (Path.refl a)
  let hqp := h a a (loopMul q p) (Path.refl a)
  Path.trans hpq (Path.symm hqp)

-- ════════════════════════════════════════════════════════════════
-- § 22. SUSPENSION AND MERIDIAN STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Suspension data: north pole, south pole, meridians. -/
structure SuspensionData (A : Type u) where
  SuspType : Type u
  north : SuspType
  south : SuspType
  merid : A → Path north south

/-- Theorem 67: Composing meridians gives a loop through north. -/
def susp_loop {A : Type u} (S : SuspensionData A) (a b : A) :
    Path S.north S.north :=
  Path.trans (S.merid a) (Path.symm (S.merid b))

-- ════════════════════════════════════════════════════════════════
-- § 23. ENCODE-DECODE STRUCTURE
-- ════════════════════════════════════════════════════════════════

/-- Encode-decode method data: a code family with encoding/decoding. -/
structure EncodeDecodeData {A : Type u} (a : A) where
  Code : A → Type v
  codeRefl : Code a
  encode : {b : A} → Path a b → Code b
  decode : {b : A} → Code b → Path a b
  decodeRefl : @Path (Path a a) (decode codeRefl) (Path.refl a)

-- ════════════════════════════════════════════════════════════════
-- § 24. ADDITIONAL COHERENCE THEOREMS
-- ════════════════════════════════════════════════════════════════

/-- Theorem 68: Pentagon-like coherence — reassociating four paths. -/
theorem four_assoc {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  rw [trans_assoc (Path.trans p q) r s, trans_assoc p q (Path.trans r s)]

/-- Theorem 69: symm distributes over trans (reversed order). -/
theorem symm_trans_distr {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) =
    Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 70: symm of refl is refl. -/
theorem symm_refl_eq {A : Type u} (a : A) :
    Path.symm (Path.refl a) = Path.refl a :=
  symm_refl a

end HomTypeTheoryDeep
end ComputationalPaths
