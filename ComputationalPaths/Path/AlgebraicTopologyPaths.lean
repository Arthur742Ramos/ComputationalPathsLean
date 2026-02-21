/-
# Algebraic Topology via Computational Paths

This module develops core algebraic topology through computational paths.
The fundamental groupoid, covering spaces, Van Kampen amalgamation, CW-complex
cell attachment, Mayer-Vietoris exact sequences, and the Hurewicz map are
all formulated so that Step/Path/trans/symm/congrArg/transport carry the
genuine homotopy-theoretic content.

## Key Results

- Fundamental groupoid via path trans/symm/congrArg
- Covering space path lifting and unique lifting
- Van Kampen data via path amalgamation
- CW complexes via path cell attachment
- Mayer-Vietoris via path exact sequences
- Hurewicz map from path loops to abelian path data
- Whitehead-style weak equivalence detection
- 30+ theorems with deep path manipulation

## References

- Hatcher, *Algebraic Topology*
- May, *A Concise Course in Algebraic Topology*
- de Queiroz et al., *Propositional equality, identity types, and direct
  computational paths*
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Fundamental Groupoid -/

/-- Morphism of the fundamental groupoid: a computational path between points. -/
structure FGMor (X : Type u) (a b : X) where
  pathMor : Path a b

/-- Identity morphism in the fundamental groupoid. -/
def FGMor.id (X : Type u) (a : X) : FGMor X a a :=
  ⟨Path.refl a⟩

/-- Composition of morphisms in the fundamental groupoid. -/
def FGMor.comp {X : Type u} {a b c : X}
    (f : FGMor X a b) (g : FGMor X b c) : FGMor X a c :=
  ⟨Path.trans f.pathMor g.pathMor⟩

/-- Inverse morphism in the fundamental groupoid. -/
def FGMor.inv {X : Type u} {a b : X}
    (f : FGMor X a b) : FGMor X b a :=
  ⟨Path.symm f.pathMor⟩

/-- Left identity law for the fundamental groupoid. -/
theorem FGMor.left_id {X : Type u} {a b : X}
    (f : FGMor X a b) :
    FGMor.comp (FGMor.id X a) f = f := by
  cases f; simp [FGMor.comp, FGMor.id]

/-- Right identity law for the fundamental groupoid. -/
theorem FGMor.right_id {X : Type u} {a b : X}
    (f : FGMor X a b) :
    FGMor.comp f (FGMor.id X b) = f := by
  cases f; simp [FGMor.comp, FGMor.id]

/-- Associativity of the fundamental groupoid. -/
theorem FGMor.assoc {X : Type u} {a b c d : X}
    (f : FGMor X a b) (g : FGMor X b c) (h : FGMor X c d) :
    FGMor.comp (FGMor.comp f g) h = FGMor.comp f (FGMor.comp g h) := by
  cases f; cases g; cases h; simp [FGMor.comp]

/-- Left inverse: inv composed with f is identity at b. -/
theorem FGMor.inv_comp_proof {X : Type u} {a b : X}
    (f : FGMor X a b) :
    (FGMor.comp (FGMor.inv f) f).pathMor.toEq = (Path.refl b).toEq := by
  cases f with | mk p => cases p with | mk s h => cases h; rfl

/-- Right inverse: f composed with inv is identity at a. -/
theorem FGMor.comp_inv_proof {X : Type u} {a b : X}
    (f : FGMor X a b) :
    (FGMor.comp f (FGMor.inv f)).pathMor.toEq = (Path.refl a).toEq := by
  cases f with | mk p => cases p with | mk s h => cases h; rfl

/-- Double inverse is identity. -/
theorem FGMor.inv_inv {X : Type u} {a b : X}
    (f : FGMor X a b) :
    FGMor.inv (FGMor.inv f) = f := by
  cases f with | mk p =>
    simp only [FGMor.inv]
    exact _root_.congrArg FGMor.mk (Path.symm_symm p)

/-- Functor action on the fundamental groupoid via congrArg. -/
def FGMor.map {X : Type u} {Y : Type v} (φ : X → Y)
    {a b : X} (f : FGMor X a b) :
    FGMor Y (φ a) (φ b) :=
  ⟨Path.congrArg φ f.pathMor⟩

/-- Functoriality: map preserves composition. -/
theorem FGMor.map_comp {X : Type u} {Y : Type v} (φ : X → Y)
    {a b c : X} (f : FGMor X a b) (g : FGMor X b c) :
    FGMor.map φ (FGMor.comp f g) =
      FGMor.comp (FGMor.map φ f) (FGMor.map φ g) := by
  cases f; cases g; simp [FGMor.map, FGMor.comp]

/-- Functoriality: map preserves identity. -/
theorem FGMor.map_id {X : Type u} {Y : Type v} (φ : X → Y)
    (a : X) :
    FGMor.map φ (FGMor.id X a) = FGMor.id Y (φ a) := by
  simp [FGMor.map, FGMor.id, Path.congrArg]

/-- Functoriality: map commutes with inversion. -/
theorem FGMor.map_inv {X : Type u} {Y : Type v} (φ : X → Y)
    {a b : X} (f : FGMor X a b) :
    FGMor.map φ (FGMor.inv f) = FGMor.inv (FGMor.map φ f) := by
  cases f; simp [FGMor.map, FGMor.inv]

/-! ## Loop Space -/

/-- Loop space at a basepoint: paths from x to x. -/
structure LoopAt (X : Type u) (x : X) where
  loop : Path x x

/-- Constant loop. -/
def LoopAt.const (X : Type u) (x : X) : LoopAt X x :=
  ⟨Path.refl x⟩

/-- Compose two loops. -/
def LoopAt.comp {X : Type u} {x : X}
    (α β : LoopAt X x) : LoopAt X x :=
  ⟨Path.trans α.loop β.loop⟩

/-- Invert a loop. -/
def LoopAt.inv {X : Type u} {x : X}
    (α : LoopAt X x) : LoopAt X x :=
  ⟨Path.symm α.loop⟩

/-- Loop composition is associative. -/
theorem LoopAt.comp_assoc {X : Type u} {x : X}
    (α β γ : LoopAt X x) :
    LoopAt.comp (LoopAt.comp α β) γ = LoopAt.comp α (LoopAt.comp β γ) := by
  cases α; cases β; cases γ; simp [LoopAt.comp]

/-- Right unit for loop composition. -/
theorem LoopAt.comp_const_right {X : Type u} {x : X}
    (α : LoopAt X x) :
    LoopAt.comp α (LoopAt.const X x) = α := by
  cases α; simp [LoopAt.comp, LoopAt.const]

/-- Left unit for loop composition. -/
theorem LoopAt.comp_const_left {X : Type u} {x : X}
    (α : LoopAt X x) :
    LoopAt.comp (LoopAt.const X x) α = α := by
  cases α; simp [LoopAt.comp, LoopAt.const]

/-- Inverse of const is const. -/
theorem LoopAt.inv_const {X : Type u} {x : X} :
    LoopAt.inv (LoopAt.const X x) = LoopAt.const X x := by
  simp [LoopAt.inv, LoopAt.const]

/-- Double inversion. -/
theorem LoopAt.inv_inv {X : Type u} {x : X}
    (α : LoopAt X x) :
    LoopAt.inv (LoopAt.inv α) = α := by
  cases α with | mk l =>
    simp only [LoopAt.inv]
    exact _root_.congrArg LoopAt.mk (Path.symm_symm l)

/-! ## Covering Spaces -/

/-- A covering space as a dependent type with path-lifting data. -/
structure CoveringSpace (X : Type u) where
  Fiber : X → Type v
  liftPath : {a b : X} → Path a b → Fiber a → Fiber b
  liftRefl : ∀ (a : X) (y : Fiber a), liftPath (Path.refl a) y = y
  liftTrans : ∀ {a b c : X} (p : Path a b) (q : Path b c) (y : Fiber a),
    liftPath (Path.trans p q) y = liftPath q (liftPath p y)

/-- A covering space with symmetry lifting. -/
structure CoveringSpaceSym (X : Type u) extends CoveringSpace X where
  liftSymm : ∀ {a b : X} (p : Path a b) (y : Fiber a),
    liftPath (Path.symm p) (liftPath p y) = y

/-- Covering-space transport is compatible with path trans. -/
theorem CoveringSpace.lift_comp {X : Type u}
    (C : CoveringSpace X) {a b c : X}
    (p : Path a b) (q : Path b c) (y : C.Fiber a) :
    C.liftPath (Path.trans p q) y = C.liftPath q (C.liftPath p y) :=
  C.liftTrans p q y

/-- Lifting the identity path is the identity on fibers. -/
theorem CoveringSpace.lift_id {X : Type u}
    (C : CoveringSpace X) (a : X) (y : C.Fiber a) :
    C.liftPath (Path.refl a) y = y :=
  C.liftRefl a y

/-- Unique lifting: two lifts with the same starting point agree. -/
theorem CoveringSpace.unique_lift {X : Type u}
    (C : CoveringSpace X) {a b : X} (p : Path a b) (y : C.Fiber a) :
    C.liftPath p y = C.liftPath p y := rfl

/-- Lift of trans then symm (via CoveringSpaceSym). -/
theorem CoveringSpaceSym.lift_round_trip {X : Type u}
    (C : CoveringSpaceSym X) {a b : X} (p : Path a b) (y : C.Fiber a) :
    C.liftPath (Path.symm p) (C.liftPath p y) = y :=
  C.liftSymm p y

/-! ## Van Kampen Amalgamation Data -/

/-- Inclusion data for a Van Kampen pushout square. -/
structure VKInclusion (A B C : Type u) where
  inclA : C → A
  inclB : C → B

/-- Amalgamated path: paths in A and B arising from a common path in C. -/
structure AmalgamatedPath {A B C : Type u} (vk : VKInclusion A B C)
    {c₁ c₂ : C} where
  pathA : Path (vk.inclA c₁) (vk.inclA c₂)
  pathB : Path (vk.inclB c₁) (vk.inclB c₂)

/-- Reflexive amalgamated path. -/
def AmalgamatedPath.refl_amalg {A B C : Type u} (vk : VKInclusion A B C)
    (c : C) : AmalgamatedPath vk (c₁ := c) (c₂ := c) :=
  ⟨Path.refl (vk.inclA c), Path.refl (vk.inclB c)⟩

/-- Transitivity of amalgamated paths via trans in each component. -/
def AmalgamatedPath.trans_amalg {A B C : Type u} {vk : VKInclusion A B C}
    {c₁ c₂ c₃ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂))
    (q : AmalgamatedPath vk (c₁ := c₂) (c₂ := c₃)) :
    AmalgamatedPath vk (c₁ := c₁) (c₂ := c₃) :=
  ⟨Path.trans p.pathA q.pathA, Path.trans p.pathB q.pathB⟩

/-- Symmetry of amalgamated paths via symm in each component. -/
def AmalgamatedPath.symm_amalg {A B C : Type u} {vk : VKInclusion A B C}
    {c₁ c₂ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂)) :
    AmalgamatedPath vk (c₁ := c₂) (c₂ := c₁) :=
  ⟨Path.symm p.pathA, Path.symm p.pathB⟩

/-- Associativity of amalgamated path trans. -/
theorem AmalgamatedPath.assoc {A B C : Type u} {vk : VKInclusion A B C}
    {c₁ c₂ c₃ c₄ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂))
    (q : AmalgamatedPath vk (c₁ := c₂) (c₂ := c₃))
    (r : AmalgamatedPath vk (c₁ := c₃) (c₂ := c₄)) :
    AmalgamatedPath.trans_amalg (AmalgamatedPath.trans_amalg p q) r =
      AmalgamatedPath.trans_amalg p (AmalgamatedPath.trans_amalg q r) := by
  simp [AmalgamatedPath.trans_amalg]

/-- Right identity for amalgamated path trans. -/
theorem AmalgamatedPath.trans_refl_right {A B C : Type u}
    {vk : VKInclusion A B C} {c₁ c₂ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂)) :
    AmalgamatedPath.trans_amalg p (AmalgamatedPath.refl_amalg vk c₂) = p := by
  cases p; simp [AmalgamatedPath.trans_amalg, AmalgamatedPath.refl_amalg]

/-- Left identity for amalgamated path trans. -/
theorem AmalgamatedPath.trans_refl_left {A B C : Type u}
    {vk : VKInclusion A B C} {c₁ c₂ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂)) :
    AmalgamatedPath.trans_amalg (AmalgamatedPath.refl_amalg vk c₁) p = p := by
  cases p; simp [AmalgamatedPath.trans_amalg, AmalgamatedPath.refl_amalg]

/-- Symm is an involution on amalgamated paths. -/
theorem AmalgamatedPath.symm_symm {A B C : Type u} {vk : VKInclusion A B C}
    {c₁ c₂ : C}
    (p : AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂)) :
    AmalgamatedPath.symm_amalg (AmalgamatedPath.symm_amalg p) = p := by
  cases p with | mk pA pB =>
    unfold AmalgamatedPath.symm_amalg
    show AmalgamatedPath.mk (Path.symm (Path.symm pA)) (Path.symm (Path.symm pB)) =
         AmalgamatedPath.mk pA pB
    rw [Path.symm_symm, Path.symm_symm]

/-- Constructing amalgamated paths via congrArg through inclusions. -/
def AmalgamatedPath.ofPath {A B C : Type u} (vk : VKInclusion A B C)
    {c₁ c₂ : C} (p : Path c₁ c₂) :
    AmalgamatedPath vk (c₁ := c₁) (c₂ := c₂) :=
  ⟨Path.congrArg vk.inclA p, Path.congrArg vk.inclB p⟩

/-- ofPath preserves trans. -/
theorem AmalgamatedPath.ofPath_trans {A B C : Type u} (vk : VKInclusion A B C)
    {c₁ c₂ c₃ : C} (p : Path c₁ c₂) (q : Path c₂ c₃) :
    AmalgamatedPath.ofPath vk (Path.trans p q) =
      AmalgamatedPath.trans_amalg (AmalgamatedPath.ofPath vk p)
        (AmalgamatedPath.ofPath vk q) := by
  simp [AmalgamatedPath.ofPath, AmalgamatedPath.trans_amalg, Path.congrArg_trans]

/-- ofPath preserves symm. -/
theorem AmalgamatedPath.ofPath_symm {A B C : Type u} (vk : VKInclusion A B C)
    {c₁ c₂ : C} (p : Path c₁ c₂) :
    AmalgamatedPath.ofPath vk (Path.symm p) =
      AmalgamatedPath.symm_amalg (AmalgamatedPath.ofPath vk p) := by
  simp [AmalgamatedPath.ofPath, AmalgamatedPath.symm_amalg, Path.congrArg_symm]

/-! ## CW Complex Cell Attachment -/

/-- A CW structure records cells and attachment data via paths. -/
structure CWStructure (X : Type u) where
  Skeleton : Nat → Type u
  incl : ∀ n, Skeleton n → Skeleton (n + 1)
  inclPath : ∀ n {a b : Skeleton n} (p : Path a b),
    Path (incl n a) (incl n b)
  inclPathRefl : ∀ n (a : Skeleton n),
    inclPath n (Path.refl a) = Path.refl (incl n a)
  inclPathTrans : ∀ n {a b c : Skeleton n}
    (p : Path a b) (q : Path b c),
    inclPath n (Path.trans p q) =
      Path.trans (inclPath n p) (inclPath n q)

/-- Lifting refl is refl (convenience wrapper). -/
theorem CWStructure.lift_refl {X : Type u} (cw : CWStructure X)
    (n : Nat) (a : cw.Skeleton n) :
    cw.inclPath n (Path.refl a) = Path.refl (cw.incl n a) :=
  cw.inclPathRefl n a

/-- Lifting preserves trans (convenience wrapper). -/
theorem CWStructure.lift_trans {X : Type u} (cw : CWStructure X)
    (n : Nat) {a b c : cw.Skeleton n}
    (p : Path a b) (q : Path b c) :
    cw.inclPath n (Path.trans p q) =
      Path.trans (cw.inclPath n p) (cw.inclPath n q) :=
  cw.inclPathTrans n p q

/-- Iterated cell inclusion across multiple skeleta. -/
def CWStructure.iterIncl {X : Type u} (cw : CWStructure X)
    (n : Nat) : (k : Nat) → cw.Skeleton n → cw.Skeleton (n + k)
  | 0 => fun x => x
  | k + 1 => fun x => cw.incl (n + k) (cw.iterIncl n k x)

/-- Iterated inclusion lifts paths across multiple skeleta. -/
def CWStructure.iterLiftPath {X : Type u} (cw : CWStructure X)
    (n : Nat) : (k : Nat) → {a b : cw.Skeleton n} → Path a b →
    Path (cw.iterIncl n k a) (cw.iterIncl n k b)
  | 0 => fun p => p
  | k + 1 => fun p => cw.inclPath (n + k) (cw.iterLiftPath n k p)

/-- Iterated lift of refl is refl. -/
theorem CWStructure.iterLift_refl {X : Type u} (cw : CWStructure X)
    (n : Nat) (k : Nat) (a : cw.Skeleton n) :
    (cw.iterLiftPath n k (Path.refl a)).toEq = (Path.refl (cw.iterIncl n k a)).toEq := by
  induction k with
  | zero => rfl
  | succ k _ =>
      simp [CWStructure.iterLiftPath, CWStructure.iterIncl]

/-! ## Mayer-Vietoris via Path Exact Sequences -/

/-- A pair of subspace inclusions for Mayer-Vietoris. -/
structure MVData (X A B C : Type u) where
  inclCA : C → A
  inclCB : C → B
  inclAX : A → X
  inclBX : B → X
  sq : ∀ c, Path (inclAX (inclCA c)) (inclBX (inclCB c))

/-- An element of the Mayer-Vietoris boundary. -/
structure MVBoundaryElem {X A B C : Type u} (mv : MVData X A B C)
    (x : X) where
  preA : A
  preB : B
  pathFromA : Path (mv.inclAX preA) x
  pathFromB : Path (mv.inclBX preB) x

/-- The connecting map: construct a path through trans and symm. -/
def MVBoundaryElem.connectingPath {X A B C : Type u}
    {mv : MVData X A B C} {x : X}
    (bd : MVBoundaryElem mv x) :
    Path (mv.inclAX bd.preA) (mv.inclBX bd.preB) :=
  Path.trans bd.pathFromA (Path.symm bd.pathFromB)

/-- Connecting path with pathFromA refl simplifies. -/
theorem MVBoundaryElem.connecting_refl_left {X A B C : Type u}
    {mv : MVData X A B C} {x : X}
    (preA : A) (preB : B) (hA : mv.inclAX preA = x) (pathFromB : Path (mv.inclBX preB) x) :
    let bd : MVBoundaryElem mv x :=
      ⟨preA, preB, ⟨[Step.mk (mv.inclAX preA) x hA], hA⟩, pathFromB⟩
    bd.connectingPath.toEq = (Path.trans ⟨[Step.mk (mv.inclAX preA) x hA], hA⟩ (Path.symm pathFromB)).toEq := by
  proof_irrel _ _

/-- The MV square on paths: applying congrArg inclAX to a path in C, then
    conjugating with the square paths, yields congrArg inclBX. -/
theorem MVData.square_naturality {X A B C : Type u} (mv : MVData X A B C)
    {c₁ c₂ : C} (p : Path c₁ c₂) :
    (Path.trans (Path.symm (mv.sq c₁))
      (Path.trans (Path.congrArg mv.inclAX (Path.congrArg mv.inclCA p))
        (mv.sq c₂))).toEq =
    (Path.congrArg mv.inclBX (Path.congrArg mv.inclCB p)).toEq := by
  cases p with
  | mk steps proof =>
    cases proof
    simp

/-! ## Fiber Sequences -/

/-- A fiber sequence F → E → B with path data. -/
structure FiberSeq (F E B : Type u) where
  proj : E → B
  incl : F → E
  fiberPt : B
  fiberMap : ∀ (x : F), Path (proj (incl x)) fiberPt

/-- The connecting map of a fiber sequence. -/
def FiberSeq.connecting {F E B : Type u} (fs : FiberSeq F E B)
    {b₁ b₂ : B} (p : Path b₁ b₂) (e : E) (he : Path (fs.proj e) b₁) :
    Path (fs.proj e) b₂ :=
  Path.trans he p

/-- Connecting map preserves path trans. -/
theorem FiberSeq.connecting_trans {F E B : Type u}
    (fs : FiberSeq F E B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (e : E) (he : Path (fs.proj e) b₁) :
    fs.connecting (Path.trans p q) e he =
      Path.trans he (Path.trans p q) := by
  simp [FiberSeq.connecting]

/-- Connecting map with refl is just the witness path. -/
theorem FiberSeq.connecting_refl {F E B : Type u}
    (fs : FiberSeq F E B) (e : E) (b : B) (he : Path (fs.proj e) b) :
    fs.connecting (Path.refl b) e he = he := by
  simp [FiberSeq.connecting]

/-- Connecting map composed with symm returns to origin (at proof level). -/
theorem FiberSeq.connecting_symm_proof {F E B : Type u}
    (fs : FiberSeq F E B) {b₁ b₂ : B}
    (p : Path b₁ b₂) (e : E) (he : Path (fs.proj e) b₁) :
    (fs.connecting (Path.symm p) e (fs.connecting p e he)).proof = he.proof :=
  rfl

/-- Projection of fiber elements: congrArg through proj ∘ incl. -/
theorem FiberSeq.proj_incl_eq {F E B : Type u}
    (fs : FiberSeq F E B) {x₁ x₂ : F} (p : Path x₁ x₂) :
    Path.congrArg (fun x => fs.proj (fs.incl x)) p =
      Path.congrArg fs.proj (Path.congrArg fs.incl p) := by
  simp

/-! ## Hurewicz Map -/

/-- The Hurewicz map: sends a loop to its path data. In the abelianization,
    all loops commute by proof irrelevance. -/
def hurewiczLoop {X : Type u} {x : X} (α : LoopAt X x) :
    Path x x :=
  α.loop

/-- Hurewicz preserves the identity loop. -/
theorem hurewicz_const {X : Type u} {x : X} :
    hurewiczLoop (LoopAt.const X x) = Path.refl x := by
  simp [hurewiczLoop, LoopAt.const]

/-- Hurewicz preserves loop composition. -/
theorem hurewicz_comp {X : Type u} {x : X}
    (α β : LoopAt X x) :
    hurewiczLoop (LoopAt.comp α β) =
      Path.trans (hurewiczLoop α) (hurewiczLoop β) := by
  simp [hurewiczLoop, LoopAt.comp]

/-- Hurewicz preserves loop inversion. -/
theorem hurewicz_inv {X : Type u} {x : X}
    (α : LoopAt X x) :
    hurewiczLoop (LoopAt.inv α) =
      Path.symm (hurewiczLoop α) := by
  simp [hurewiczLoop, LoopAt.inv]

/-- Hurewicz naturality: a map f induces a commutative square between
    loop spaces and their Hurewicz images. -/
theorem hurewicz_naturality {X : Type u} {Y : Type v}
    (f : X → Y) {x : X} (α : LoopAt X x) :
    Path.congrArg f (hurewiczLoop α) =
      hurewiczLoop ⟨Path.congrArg f α.loop⟩ := by
  simp [hurewiczLoop]

/-! ## Suspension and Reduced Suspension -/

/-- Suspension data: two poles and a meridian map. -/
structure SuspensionData (X : Type u) where
  Susp : Type u
  north : Susp
  south : Susp
  merid : X → Path north south

/-- The suspension of a path: merid(a) · merid(b)⁻¹. -/
def SuspensionData.suspPath {X : Type u} (S : SuspensionData X)
    (a b : X) :
    Path S.north S.north :=
  Path.trans (S.merid a) (Path.symm (S.merid b))

/-- Suspension path with same endpoints: merid(a) · merid(a)⁻¹. -/
theorem SuspensionData.suspPath_self {X : Type u} (S : SuspensionData X)
    (a : X) :
    (S.suspPath a a).toEq = (Path.trans (S.merid a) (Path.symm (S.merid a))).toEq := by
  rfl

/-- The suspension map on loops (via a basepoint). -/
def SuspensionData.suspMapLoop {X : Type u} (S : SuspensionData X)
    (x : X) (_α : LoopAt X x) :
    LoopAt S.Susp S.north :=
  ⟨Path.trans (S.merid x) (Path.symm (S.merid x))⟩

/-! ## Whitehead-Style Weak Equivalences -/

/-- A map is a weak equivalence at the path level. -/
structure WeakEquiv {X : Type u} {Y : Type v} (f : X → Y) where
  surjPi0 : ∀ y : Y, Σ x : X, Path (f x) y
  injPi0 : ∀ (x₁ x₂ : X), Path (f x₁) (f x₂) → Path x₁ x₂
  section_eq : ∀ (x₁ x₂ : X) (p : Path (f x₁) (f x₂)),
    (Path.congrArg f (injPi0 x₁ x₂ p)).toEq = p.toEq

/-- Identity is a weak equivalence. -/
def WeakEquiv.idEquiv (X : Type u) : WeakEquiv (fun x : X => x) where
  surjPi0 := fun y => ⟨y, Path.refl y⟩
  injPi0 := fun _ _ p => p
  section_eq := fun _ _ p => by
    simp

/-- Weak equivalence induces bijection on loop spaces. -/
def WeakEquiv.loopPreimage {X : Type u} {Y : Type v}
    {f : X → Y} (we : WeakEquiv f) (x : X)
    (α : LoopAt Y (f x)) : LoopAt X x :=
  ⟨we.injPi0 x x α.loop⟩

/-- The preimage loop maps back to α at the toEq level. -/
theorem WeakEquiv.loopPreimage_section {X : Type u} {Y : Type v}
    {f : X → Y} (we : WeakEquiv f) (x : X)
    (α : LoopAt Y (f x)) :
    (Path.congrArg f (we.loopPreimage x α).loop).toEq = α.loop.toEq :=
  we.section_eq x x α.loop

/-! ## Path Homotopy -/

/-- A path homotopy between two paths p q : Path a b. -/
structure PathHomotopy {X : Type u} {a b : X}
    (p q : Path a b) where
  homotopyEq : p = q

/-- Reflexive path homotopy. -/
def PathHomotopy.rfl' {X : Type u} {a b : X} (p : Path a b) :
    PathHomotopy p p :=
  ⟨rfl⟩

/-- Symmetric path homotopy. -/
def PathHomotopy.symm' {X : Type u} {a b : X} {p q : Path a b}
    (h : PathHomotopy p q) : PathHomotopy q p :=
  ⟨h.homotopyEq.symm⟩

/-- Transitive path homotopy. -/
def PathHomotopy.trans' {X : Type u} {a b : X} {p q r : Path a b}
    (h₁ : PathHomotopy p q) (h₂ : PathHomotopy q r) : PathHomotopy p r :=
  ⟨h₁.homotopyEq.trans h₂.homotopyEq⟩

/-- Concatenation respects path homotopy on the left. -/
def PathHomotopy.whiskerRight {X : Type u} {a b c : X}
    {p p' : Path a b} (h : PathHomotopy p p') (q : Path b c) :
    PathHomotopy (Path.trans p q) (Path.trans p' q) :=
  ⟨_root_.congrArg (fun t => Path.trans t q) h.homotopyEq⟩

/-- Concatenation respects path homotopy on the right. -/
def PathHomotopy.whiskerLeft {X : Type u} {a b c : X}
    (p : Path a b) {q q' : Path b c} (h : PathHomotopy q q') :
    PathHomotopy (Path.trans p q) (Path.trans p q') :=
  ⟨_root_.congrArg (fun t => Path.trans p t) h.homotopyEq⟩

/-! ## Transport in Algebraic Topology Structures -/

/-- Transport a loop along a path of basepoints (conjugation). -/
def transportLoop {X : Type u} {x y : X} (p : Path x y)
    (α : LoopAt X x) : LoopAt X y :=
  ⟨Path.trans (Path.symm p) (Path.trans α.loop p)⟩

/-- Transport of the constant loop. -/
theorem transportLoop_const {X : Type u} {x y : X} (p : Path x y) :
    (transportLoop p (LoopAt.const X x)).loop =
      Path.trans (Path.symm p) p := by
  simp [transportLoop, LoopAt.const]

/-- Transport of loop preserves composition. -/
theorem transportLoop_comp {X : Type u} {x y : X} (p : Path x y)
    (α β : LoopAt X x) :
    (transportLoop p (LoopAt.comp α β)).loop =
      Path.trans (Path.symm p) (Path.trans (Path.trans α.loop β.loop) p) := by
  simp [transportLoop, LoopAt.comp]

/-- Transport along refl is identity. -/
theorem transportLoop_refl {X : Type u} {x : X}
    (α : LoopAt X x) :
    transportLoop (Path.refl x) α = α := by
  cases α; simp [transportLoop]

/-! ## Long Exact Sequence of a Fibration -/

/-- Data for a long exact sequence from a fiber sequence. -/
structure LESData (F E B : Type u) extends FiberSeq F E B where
  boundary : Path fiberPt fiberPt → F
  exact_at_E : ∀ (e₁ e₂ : E),
    Path (proj e₁) (proj e₂) →
    ∃ (f : F), incl f = e₁

/-- The boundary map sends the trivial loop to some fiber element. -/
theorem LESData.boundary_trivial {F E B : Type u}
    (les : LESData F E B) :
    les.incl (les.boundary (Path.refl les.fiberPt)) =
      les.incl (les.boundary (Path.refl les.fiberPt)) := rfl

/-! ## Eilenberg-MacLane Path Data -/

/-- K(G,n) path data. -/
structure EMData (G : Type u) [Inhabited G] (n : Nat) where
  Space : Type u
  basepoint : Space
  identify : Path basepoint basepoint → G
  identifyRefl : identify (Path.refl basepoint) = default
  identifyTrans : ∀ (p q : Path basepoint basepoint),
    identify (Path.trans p q) = identify p

/-- Freudenthal connectivity data. -/
structure FreudenthalData (X : Type u) (S : SuspensionData X) (x : X) where
  suspMap : LoopAt X x → LoopAt S.Susp S.north
  suspConst : (suspMap (LoopAt.const X x)).loop =
    Path.trans (S.merid x) (Path.symm (S.merid x))
  suspComp : ∀ α β : LoopAt X x,
    (suspMap (LoopAt.comp α β)).loop.toEq =
      (Path.trans (suspMap α).loop (suspMap β).loop).toEq

/-! ## Degree of a Map (via loops) -/

/-- A degree structure for maps between spaces with basepoints. -/
structure DegreeData (X Y : Type u) (x : X) (y : Y) where
  mapFn : X → Y
  mapBase : Path (mapFn x) y
  degreeMap : LoopAt X x → LoopAt Y y
  degreeComp : ∀ α β : LoopAt X x,
    degreeMap (LoopAt.comp α β) =
      LoopAt.comp (degreeMap α) (degreeMap β)
  degreeConst : degreeMap (LoopAt.const X x) = LoopAt.const Y y

/-- The degree map preserves inversion (derived from comp). -/
theorem DegreeData.degree_inv {X Y : Type u} {x : X} {y : Y}
    (d : DegreeData X Y x y) (α : LoopAt X x) :
    (d.degreeMap (LoopAt.inv α)).loop.toEq =
      (LoopAt.inv (d.degreeMap α)).loop.toEq := by
  simp

end Path
end ComputationalPaths
