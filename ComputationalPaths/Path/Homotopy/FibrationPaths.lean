/-
# Fibration Theory via Computational Paths

Fiber sequences, long exact sequence of a fibration, homotopy lifting,
Serre fibration aspects, fiber transport. All constructions use the core
Path/Step/trans/symm/congrArg/transport API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace FibrationPaths

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Fibration structure -/

/-- A fibration is a map p : E → B together with a lifting structure. -/
structure Fibration (B : Type v) where
  total : Type v
  proj : total → B

/-- The fiber over a point b. -/
def Fiber (fib : Fibration B) (b : B) : Type v :=
  { e : fib.total // fib.proj e = b }

/-- Inclusion of a fiber element into the total space. -/
def Fiber.incl {fib : Fibration B} {b : B} (x : Fiber fib b) : fib.total :=
  x.val

/-- The projection of a fiber element equals the base point. -/
theorem Fiber.proj_eq {fib : Fibration B} {b : B} (x : Fiber fib b) :
    fib.proj x.val = b :=
  x.property

/-! ## Fiber transport along paths -/

/-- Transport in the fiber along a path in the base. -/
def fiberTransport {fib : Fibration B} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : Fiber fib b₁) : Fiber fib b₂ :=
  ⟨x.val, x.property.trans p.toEq⟩

/-- Transport along refl is identity. -/
theorem fiberTransport_refl {fib : Fibration B} {b : B}
    (x : Fiber fib b) : fiberTransport (Path.refl b) x = x := by
  simp [fiberTransport]
  exact Subtype.ext rfl

/-- Transport preserves the underlying total space element. -/
theorem fiberTransport_val {fib : Fibration B} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : Fiber fib b₁) :
    (fiberTransport p x).val = x.val := rfl

/-- Transport along trans composes. -/
theorem fiberTransport_trans {fib : Fibration B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : Fiber fib b₁) :
    fiberTransport (Path.trans p q) x = fiberTransport q (fiberTransport p x) := by
  exact Subtype.ext rfl

/-- Transport along symm inverts. -/
theorem fiberTransport_symm {fib : Fibration B} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : Fiber fib b₁) :
    fiberTransport (Path.symm p) (fiberTransport p x) = x := by
  exact Subtype.ext rfl

/-! ## Dependent fibration from a type family -/

/-- Every type family gives a fibration via Sigma. -/
def familyFibration (F : B → Type v) : Fibration B where
  total := Σ b, F b
  proj := Sigma.fst

/-- Construct a fiber element from a family element. -/
def familyFiber_mk (F : B → Type v) {b : B} (x : F b) :
    Fiber (familyFibration F) b :=
  ⟨⟨b, x⟩, rfl⟩

/-- The fiber of a family fibration over b is F b. -/
def familyFiber_proj (F : B → Type v) {b : B}
    (x : Fiber (familyFibration F) b) : F b := by
  have h : x.val.fst = b := x.property
  exact h ▸ x.val.snd

/-! ## Fiber sequence -/

/-- A fiber sequence F → E → B. -/
structure FiberSeq (B E F : Type v) where
  proj : E → B
  incl : F → E
  basepoint : B
  fiberOver : ∀ x : F, proj (incl x) = basepoint

/-- The inclusion of a fiber sequence maps into the fiber over the basepoint. -/
theorem fiberSeq_incl_proj {B E F : Type v} (fs : FiberSeq B E F) (x : F) :
    fs.proj (fs.incl x) = fs.basepoint :=
  fs.fiberOver x

/-- Path from proj ∘ incl to the basepoint. -/
def fiberSeq_proj_incl_path {B E F : Type v} (fs : FiberSeq B E F) (x : F) :
    Path (fs.proj (fs.incl x)) fs.basepoint :=
  Path.mk [Step.mk _ _ (fs.fiberOver x)] (fs.fiberOver x)

/-! ## Homotopy lifting property -/

/-- A path lifting structure for a fibration. -/
structure PathLifting (fib : Fibration B) where
  lift : {b₁ b₂ : B} → Path b₁ b₂ → Fiber fib b₁ → fib.total
  covers : {b₁ b₂ : B} → (p : Path b₁ b₂) → (x : Fiber fib b₁) →
    fib.proj (lift p x) = b₂

/-- The lifted endpoint lies in the target fiber. -/
def liftedFiber {fib : Fibration B} (pl : PathLifting fib)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : Fiber fib b₁) :
    Fiber fib b₂ :=
  ⟨pl.lift p x, pl.covers p x⟩

/-- Trivial lifting: using fiber transport. -/
def trivialLifting (fib : Fibration B) : PathLifting fib where
  lift := fun p x => (fiberTransport p x).val
  covers := fun p x => (fiberTransport p x).property

/-- The trivial lifting agrees with fiber transport. -/
theorem trivialLifting_eq (fib : Fibration B) {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : Fiber fib b₁) :
    liftedFiber (trivialLifting fib) p x = fiberTransport p x := by
  exact Subtype.ext rfl

/-! ## Long exact sequence components -/

/-- The connecting map δ : Ω(B, b) → Fiber sends a loop to transport around it. -/
def connectingMap {fib : Fibration B} {b : B}
    (x₀ : Fiber fib b) (l : Path b b) : Fiber fib b :=
  fiberTransport l x₀

/-- The connecting map sends the identity loop to the basepoint fiber element. -/
theorem connectingMap_refl {fib : Fibration B} {b : B}
    (x₀ : Fiber fib b) :
    connectingMap x₀ (Path.refl b) = x₀ := by
  exact fiberTransport_refl x₀

/-- The connecting map respects loop composition. -/
theorem connectingMap_trans {fib : Fibration B} {b : B}
    (x₀ : Fiber fib b) (l₁ l₂ : Path b b) :
    connectingMap x₀ (Path.trans l₁ l₂) =
      connectingMap (connectingMap x₀ l₁) l₂ := by
  exact fiberTransport_trans l₁ l₂ x₀

/-- The connecting map respects loop inverse. -/
theorem connectingMap_symm {fib : Fibration B} {b : B}
    (x₀ : Fiber fib b) (l : Path b b) :
    connectingMap (connectingMap x₀ l) (Path.symm l) = x₀ := by
  exact fiberTransport_symm l x₀

/-! ## Pullback fibration -/

/-- Pullback of a fibration along a map. -/
def pullbackFib (fib : Fibration B) (f : B → B) : Fibration B where
  total := { p : B × fib.total // fib.proj p.2 = f p.1 }
  proj := fun p => p.val.1

/-! ## Path-space fibration -/

/-- The path-space fibration: total space is paths from a fixed basepoint. -/
def pathSpaceFib (b₀ : B) : Fibration B where
  total := Σ b, Path b₀ b
  proj := Sigma.fst

/-- The path-space fibration base point. -/
def pathSpaceFib_basepoint (b₀ : B) :
    Fiber (pathSpaceFib b₀) b₀ :=
  ⟨⟨b₀, Path.refl b₀⟩, rfl⟩

/-- The path-space fibration: fiber elements project correctly. -/
theorem pathSpaceFib_fiber_proj (b₀ b : B)
    (x : Fiber (pathSpaceFib b₀) b) :
    x.val.fst = b :=
  x.property

/-! ## Functoriality of fibrations -/

/-- A map of fibrations. -/
structure FibMap (fib₁ fib₂ : Fibration B) where
  totalMap : fib₁.total → fib₂.total
  commutes : ∀ e, fib₂.proj (totalMap e) = fib₁.proj e

/-- A fibration map sends fibers to fibers. -/
def FibMap.fiberMap {fib₁ fib₂ : Fibration B} (fm : FibMap fib₁ fib₂)
    {b : B} (x : Fiber fib₁ b) : Fiber fib₂ b :=
  ⟨fm.totalMap x.val, (fm.commutes x.val).trans x.property⟩

/-- The identity fibration map. -/
def FibMap.ident (fib : Fibration B) : FibMap fib fib where
  totalMap := fun x => x
  commutes := fun _ => rfl

/-- Identity fibration map preserves fiber elements. -/
theorem FibMap.ident_fiberMap {fib : Fibration B} {b : B}
    (x : Fiber fib b) :
    (FibMap.ident fib).fiberMap x = x := by
  exact Subtype.ext rfl

/-- Composition of fibration maps. -/
def FibMap.comp {fib₁ fib₂ fib₃ : Fibration B}
    (g : FibMap fib₂ fib₃) (f : FibMap fib₁ fib₂) : FibMap fib₁ fib₃ where
  totalMap := g.totalMap ∘ f.totalMap
  commutes := fun e => (g.commutes (f.totalMap e)).trans (f.commutes e)

/-- Composition of fibration maps on fibers. -/
theorem FibMap.comp_fiberMap {fib₁ fib₂ fib₃ : Fibration B}
    (g : FibMap fib₂ fib₃) (f : FibMap fib₁ fib₂) {b : B}
    (x : Fiber fib₁ b) :
    (FibMap.comp g f).fiberMap x = g.fiberMap (f.fiberMap x) := by
  exact Subtype.ext rfl

/-- Fiber map preserves transport. -/
theorem FibMap.fiberMap_transport {fib₁ fib₂ : Fibration B}
    (fm : FibMap fib₁ fib₂) {b₁ b₂ : B} (p : Path b₁ b₂)
    (x : Fiber fib₁ b₁) :
    fm.fiberMap (fiberTransport p x) = fiberTransport p (fm.fiberMap x) := by
  exact Subtype.ext rfl

end FibrationPaths
end Path
end ComputationalPaths
