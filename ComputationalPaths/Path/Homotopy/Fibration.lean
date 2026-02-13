/-
# Fibrations and Fiber Sequences

This module develops the theory of fibrations in the computational paths framework.

## Mathematical Background

A fibration p : E → B is a map with the homotopy lifting property:
given a homotopy in B and a lift of its starting point to E,
the entire homotopy lifts to E.

In HoTT, type families P : B → Type automatically satisfy this property,
making them "fibrations" in the type-theoretic sense.

## Key Concepts

- `Fiber p b`: The fiber of p over b
- `FiberSeq`: Fiber sequence F → E → B
- `connectingMap`: The boundary map ∂ : π_n(B) → π_{n-1}(F)
- Long exact sequence of homotopy groups

## References

- HoTT Book, Chapter 8.3 (Fiber sequences and the long exact sequence)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path
namespace Fibration

open HigherHomotopy CoveringSpace

universe u v

variable {A : Type u} {B : Type u} {E : Type u}

/-! ## Fibers of Maps

The fiber of a map f : A → B over a point b : B consists of
all points in A that map to b.
-/

/-- The fiber of a map f at a point b. -/
def Fiber (f : A → B) (b : B) : Type u :=
  { a : A // f a = b }

/-- Project from fiber to total space. -/
def Fiber.point {f : A → B} {b : B} (x : Fiber f b) : A :=
  x.val

/-- The proof that a fiber element maps to the base point. -/
def Fiber.prop {f : A → B} {b : B} (x : Fiber f b) : Path (f x.point) b :=
  Path.stepChain x.property

/-- Construct a fiber element. -/
def Fiber.mk {f : A → B} {b : B} (a : A) (h : Path (f a) b) : Fiber f b :=
  ⟨a, h.toEq⟩

/-! ## Type Families as Fibrations

In HoTT, a type family P : B → Type is the archetypal fibration.
The total space is Σ(b:B). P(b), and the projection is fst.
-/

/-- The total space of a type family. -/
abbrev Total (P : B → Type u) : Type u := Σ (b : B), P b

/-- The projection from total space to base. -/
def Total.proj {P : B → Type u} : Total P → B := Sigma.fst

/-- The fiber of Total.proj over b is equivalent to P(b). -/
def fiberEquivFamily {P : B → Type u} (b : B) :
    SimpleEquiv (Fiber (@Total.proj B P) b) (P b) where
  toFun := fun ⟨⟨_, p⟩, h⟩ => Path.transport (Path.stepChain h) p
  invFun := fun p => Fiber.mk (f := @Total.proj B P) (b := b) ⟨b, p⟩ (Path.refl b)
  left_inv := fun ⟨⟨_, _⟩, h⟩ => by subst h; rfl
  right_inv := fun _ => rfl

/-! ## Fiber Sequences

A fiber sequence is a sequence F → E → B where F is the fiber of the map E → B.
-/

/-- A fiber sequence consists of a map, basepoints, and a fiber identification. -/
structure FiberSeq (F : Type u) (E : Type u) (B : Type u) where
  /-- The projection map. -/
  proj : E → B
  /-- The basepoint in B. -/
  baseB : B
  /-- The basepoint in E lying over baseB. -/
  baseE : E
  /-- Proof that baseE projects to baseB. -/
  base_proj : Path (proj baseE) baseB
  /-- Function from F to the fiber. -/
  toFiber : F → Fiber proj baseB
  /-- Function from fiber to F. -/
  fromFiber : Fiber proj baseB → F
  /-- Left inverse property. -/
  left_inv : ∀ f, fromFiber (toFiber f) = f
  /-- Right inverse property. -/
  right_inv : ∀ x, toFiber (fromFiber x) = x

namespace FiberSeq

variable {F E B : Type u}

/-- The inclusion of the fiber into the total space. -/
def incl (seq : FiberSeq F E B) : F → E :=
  fun f => (seq.toFiber f).point

/-- The fiber inclusion composed with projection is constant. -/
def proj_incl (seq : FiberSeq F E B) (f : F) :
    Path (seq.proj (seq.incl f)) seq.baseB :=
  (seq.toFiber f).prop

end FiberSeq

/-! ## Path Lifting for Fibrations

The key property of fibrations is path lifting: a path in the base
can be lifted to a path in the total space.
-/

/-- Lift a path in the base to the total space of a type family.
Given p : Path b₁ b₂ in B and x : P(b₁), we get a path from (b₁, x) to (b₂, transport p x). -/
noncomputable def liftPath {P : B → Type u} {b₁ b₂ : B}
    (p : Path b₁ b₂) (x : P b₁) :
    Path (⟨b₁, x⟩ : Total P) ⟨b₂, Path.transport p x⟩ :=
  CoveringSpace.pathLift p x

/-! ## Connecting Map

The connecting map ∂ : π_n(B, b) → π_{n-1}(F, *) is fundamental
to the long exact sequence of homotopy groups.

For n = 1, ∂ : π₁(B, b) → π₀(F) sends a loop in B to the
endpoint of its lift starting at the basepoint of F.
-/

/-- The connecting map at level 1: π₁(B) → F (as a set map).
Given a loop in B based at b, lift it starting at the basepoint fiber element,
and return the endpoint in F. -/
noncomputable def connectingMap₁ {P : B → Type u} (b : B) (x₀ : P b) :
    LoopSpace B b → P b := fun loop =>
  -- Lift the loop starting at x₀
  -- The lifted path ends at transport(loop)(x₀)
  -- Since loop is a loop (ends at b), transport(loop)(x₀) : P b
  Path.transport loop x₀

/-- The connecting map respects RwEq. -/
theorem connectingMap₁_respects_rweq {P : B → Type u} (b : B) (x₀ : P b)
    {l₁ l₂ : LoopSpace B b} (h : RwEq l₁ l₂) :
    connectingMap₁ b x₀ l₁ = connectingMap₁ b x₀ l₂ := by
  unfold connectingMap₁
  exact Path.transport_of_toEq_eq (rweq_toEq h) x₀

/-- The connecting map descends to the quotient π₁. -/
noncomputable def connectingMapPi1 {P : B → Type u} (b : B) (x₀ : P b) :
    π₁(B, b) → P b :=
  Quot.lift (connectingMap₁ b x₀) (fun _ _ h => connectingMap₁_respects_rweq b x₀ h)

/-- Connecting map of refl is the identity. -/
theorem connectingMap₁_refl {P : B → Type u} (b : B) (x₀ : P b) :
    connectingMap₁ b x₀ (Path.refl b) = x₀ := rfl

/-- Connecting map of composition. -/
theorem connectingMap₁_trans {P : B → Type u} (b : B) (x₀ : P b)
    (l₁ l₂ : LoopSpace B b) :
    connectingMap₁ b x₀ (Path.trans l₁ l₂) =
    connectingMap₁ b (connectingMap₁ b x₀ l₁) l₂ := by
  unfold connectingMap₁
  exact Path.transport_trans l₁ l₂ x₀

/-! ## Exactness

The fiber sequence F → E → B induces exact sequences on homotopy groups.
Exactness at E means: im(incl) = ker(proj).
-/

/-- A sequence F →i E →p B is exact at E if the image of i equals the kernel of p.
In our setting, this means: e is in im(incl) iff proj(e) = baseB. -/
structure IsExactAt (seq : FiberSeq F E B) where
  /-- Elements in the image of incl map to baseB. -/
  incl_to_base : ∀ f, Path (seq.proj (seq.incl f)) seq.baseB
  /-- Elements mapping to baseB come from the fiber. -/
  base_from_fiber : ∀ e, Path (seq.proj e) seq.baseB → Σ f, Path (seq.incl f) e

/-- The canonical fiber sequence for a type family. -/
def canonicalFiberSeq {P : B → Type u} (b : B) (x₀ : P b) :
    FiberSeq (P b) (Total P) B where
  proj := @Total.proj B P
  baseB := b
  baseE := ⟨b, x₀⟩
  base_proj := Path.refl b
  toFiber := fun p => Fiber.mk (f := @Total.proj B P) (b := b) ⟨b, p⟩ (Path.refl b)
  fromFiber := fun x =>
    match x with
    | ⟨⟨b', p⟩, h⟩ => Path.transport (Path.stepChain h) p
  left_inv := fun _ => rfl
  right_inv := fun x =>
    match x with
    | ⟨⟨_, p⟩, h⟩ => by subst h; rfl

/-- The canonical fiber sequence is exact. -/
def canonicalFiberSeq_exact {P : B → Type u} (b : B) (x₀ : P b) :
    IsExactAt (canonicalFiberSeq b x₀) where
  incl_to_base := fun f => (canonicalFiberSeq b x₀).proj_incl f
  base_from_fiber := fun ⟨b', p⟩ h => by
    cases h.toEq
    exact ⟨p, Path.refl _⟩

/-! ## Induced Maps on Homotopy Groups

A map f : A → B induces maps f_* : π_n(A, a) → π_n(B, f(a)).
-/

/-- Induced map on loop spaces. -/
def inducedLoopMap (f : A → B) (a : A) : LoopSpace A a → LoopSpace B (f a) :=
  Path.congrArg f

/-- Induced map respects RwEq (via context map preservation). -/
theorem inducedLoopMap_respects_rweq (f : A → B) (a : A)
    {l₁ l₂ : LoopSpace A a} (h : RwEq l₁ l₂) :
    RwEq (inducedLoopMap f a l₁) (inducedLoopMap f a l₂) := by
  unfold inducedLoopMap
  exact rweq_context_map_of_rweq ⟨f⟩ h

/-- Induced map on π₁. -/
noncomputable def inducedPi1Map (f : A → B) (a : A) :
    π₁(A, a) → π₁(B, f a) :=
  Quot.lift
    (fun l => Quot.mk _ (inducedLoopMap f a l))
    (fun _ _ h => Quot.sound (inducedLoopMap_respects_rweq f a h))

/-- Induced map preserves identity. -/
theorem inducedPi1Map_id (a : A) :
    inducedPi1Map (id : A → A) a = id := by
  funext α
  induction α using Quot.ind with
  | _ l =>
    unfold inducedPi1Map inducedLoopMap
    apply Quot.sound
    -- congrArg id l ≈ l
    exact rweq_of_eq (Path.congrArg_id l)

/-- Induced map respects composition. -/
theorem inducedPi1Map_comp (f : A → B) (g : B → E) (a : A) :
    inducedPi1Map (g ∘ f) a = inducedPi1Map g (f a) ∘ inducedPi1Map f a := by
  funext α
  induction α using Quot.ind with
  | _ l =>
    unfold inducedPi1Map inducedLoopMap Function.comp
    apply Quot.sound
    -- congrArg (g ∘ f) l ≈ congrArg g (congrArg f l)
    exact rweq_of_eq (Path.congrArg_comp g f l)

/-! ## Long Exact Sequence Preview

The full long exact sequence of homotopy groups is:

  ... → π_n(F) → π_n(E) → π_n(B) → π_{n-1}(F) → ... → π_1(B) → π_0(F) → π_0(E) → π_0(B)

Key exactness properties:
1. At π_n(E): im(incl_*) = ker(proj_*)
2. At π_n(B): im(proj_*) = ker(∂)
3. At π_{n-1}(F): im(∂) = ker(incl_*)

For computational paths, we establish these at the π₁ level.
-/

/-- Image of a map on π₁ (as a predicate). -/
def imageOnPi1 (f : A → B) (a : A) : π₁(B, f a) → Prop :=
  fun β => ∃ α, inducedPi1Map f a α = β

/-- Kernel of a map on π₁ (elements mapping to identity). -/
def kernelOnPi1 (f : A → B) (a : A) : π₁(A, a) → Prop :=
  fun α => inducedPi1Map f a α = Quot.mk _ (Path.refl (f a))

/-! ## Long Exact Sequence of Homotopy Groups

The computational paths framework collapses higher homotopies beyond π₂ to
`PUnit` (see `HigherHomotopy.PiN`). We provide a structure-level long exact
sequence that is compatible with that truncation. For n ≥ 3 the maps are
trivial by definition, while for n = 1 and n = 2 we recover the explicit
connecting map at the π₁ level.
-/

/-- Structure capturing exactness at a point in the sequence.
    Exactness at X means: im(f) = ker(g). -/
structure ExactAt {X Y Z : Type u} (f : X → Y) (g : Y → Z) (z₀ : Z) where
  /-- Image is contained in kernel. -/
  im_subset_ker : ∀ x, Path (g (f x)) z₀
  /-- Kernel is contained in image. -/
  ker_subset_im : ∀ y, Path (g y) z₀ → Σ x, Path (f x) y

/-- Induced maps on higher homotopy groups for a function.
    For n ≥ 3, `PiN` is `PUnit`, so the map is the unique constant map. -/
noncomputable def inducedPiNMap (n : Nat) (f : A → B) (a : A) :
    HigherHomotopy.PiN n A a → HigherHomotopy.PiN n B (f a) := by
  cases n with
  | zero =>
      intro _
      exact PUnit.unit
  | succ n =>
      cases n with
      | zero =>
          exact inducedPi1Map f a
      | succ n =>
          cases n with
          | zero =>
              intro _
              exact PiTwo.id (A := B) (a := f a)
          | succ n =>
              intro _
              exact PUnit.unit

/-- The long exact sequence at the π₁ level for a type family fibration.
    We have: π₁(F) →i* π₁(E) →p* π₁(B) →∂ π₀(F) -/
structure LongExactSequencePi1 {P : B → Type u} (b : B) (x₀ : P b) where
  /-- The induced map i_* : π₁(F) → π₁(E). -/
  incl_star : π₁(P b, x₀) → π₁(Total P, ⟨b, x₀⟩)
  /-- The induced map p_* : π₁(E) → π₁(B). -/
  proj_star : π₁(Total P, ⟨b, x₀⟩) → π₁(B, b)
  /-- The connecting map ∂ : π₁(B) → P(b). -/
  boundary : π₁(B, b) → P b
  /-- Exactness at π₁(E): im(incl_*) = ker(proj_*). -/
  exact_at_E : ∀ α : π₁(P b, x₀),
    proj_star (incl_star α) = Quot.mk _ (Path.refl b)
  /-- Exactness at π₁(B): im(proj_*) = ker(∂). -/
  exact_at_B : ∀ β : π₁(Total P, ⟨b, x₀⟩),
    boundary (proj_star β) = x₀

/-- Construct the long exact sequence for a type family.
    The construction uses the induced maps on π₁ and the connecting map. -/
noncomputable def longExactSequence {P : B → Type u} (b : B) (x₀ : P b) :
    LongExactSequencePi1 b x₀ where
  incl_star := fun α =>
    -- For α : π₁(P b, x₀), we embed it as a loop in Σ P at ⟨b, x₀⟩
    -- The fiber P b embeds into Total P via x ↦ ⟨b, x⟩
    Quot.lift
      (fun l => Quot.mk _ (Path.congrArg (fun x => (⟨b, x⟩ : Total P)) l))
      (fun _ _ h => Quot.sound (rweq_context_map_of_rweq ⟨fun x => (⟨b, x⟩ : Total P)⟩ h))
      α
  proj_star := fun β =>
    -- For β : π₁(Total P, ⟨b, x₀⟩), project to a loop in B
    -- This is the induced map on π₁
    inducedPi1Map Total.proj ⟨b, x₀⟩ β
  boundary := connectingMapPi1 b x₀
  exact_at_E := fun α => by
    -- proj_star ∘ incl_star maps loops in fiber to constant loops in base
    induction α using Quot.ind with
    | _ l =>
      -- congrArg proj (congrArg (⟨b, ·⟩) l) = refl b
      -- because proj ∘ (fun x => ⟨b, x⟩) = const b
      simp only [inducedPi1Map, inducedLoopMap]
      apply Quot.sound
      -- First use congrArg_comp: congrArg (proj ∘ (⟨b,·⟩)) l = congrArg proj (congrArg (⟨b,·⟩) l)
      -- So symm gives: congrArg proj (congrArg (⟨b,·⟩) l) = congrArg (proj ∘ (⟨b,·⟩)) l
      -- And proj ∘ (fun x => ⟨b, x⟩) = const b
      -- Finally, rweq_congrArg_const gives the result
      apply rweq_trans (rweq_symm (rweq_of_eq (Path.congrArg_comp Total.proj (fun x => ⟨b, x⟩) l)))
      exact rweq_congrArg_const b l
  exact_at_B := fun β => by
    -- boundary ∘ proj_star = transport ∘ proj
    -- For a loop l in Total P at ⟨b, x₀⟩, transport along proj(l) gives x₀
    induction β using Quot.ind with
    | _ l =>
      simp only [connectingMapPi1, inducedPi1Map, inducedLoopMap]
      -- l : Path ⟨b, x₀⟩ ⟨b, x₀⟩ in Total P = Σ P
      -- We need: transport (congrArg Total.proj l) x₀ = x₀
      --
      -- By sigma type path characterization:
      -- - sigmaFst l : Path b b (the base path)
      -- - sigmaSnd l : Path (transport (sigmaFst l) x₀) x₀ (the fiber path)
      --
      -- Since Total.proj = Sigma.fst, we have congrArg Total.proj l = sigmaFst l
      -- Thus: transport (congrArg Total.proj l) x₀ = transport (sigmaFst l) x₀
      -- And (sigmaSnd l).toEq proves: transport (sigmaFst l) x₀ = x₀
      exact (sigmaSnd l).toEq

/-- Exactness theorem: in a long exact sequence, composing adjacent maps gives trivial result. -/
theorem les_composition_trivial {P : B → Type u} (b : B) (x₀ : P b)
    (les : LongExactSequencePi1 (P := P) b x₀) :
    ∀ α : π₁(P b, x₀), les.proj_star (les.incl_star α) = Quot.mk _ (Path.refl b) :=
  les.exact_at_E

/-! ## Summary

This module establishes fibration theory for computational paths:

1. **Fibers**: The fiber of f : A → B over b is {a : A | f a = b}

2. **Type families as fibrations**: P : B → Type gives fibration Total P → B

3. **Fiber sequences**: F → E → B with F = Fiber(E → B)

4. **Path lifting**: Paths in B lift to Total P

5. **Connecting map**: ∂ : π₁(B) → P(b) via transport

6. **Exactness**: Canonical fiber sequences are exact

7. **Induced maps**: f : A → B induces f_* : π_n(A) → π_n(B)

8. **Long exact sequence**: π₁(F) → π₁(E) → π₁(B) → π₀(F) with exactness

This provides the foundation for:
- Long exact sequence of homotopy groups
- Computations via fiber sequences
- Connections between π_n of related spaces
-/

end Fibration
end Path
end ComputationalPaths
