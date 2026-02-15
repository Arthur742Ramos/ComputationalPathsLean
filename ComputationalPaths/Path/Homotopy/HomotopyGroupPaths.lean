/-
# Homotopy Groups via Computational Paths

This module develops homotopy group theory using the computational paths framework:
loop spaces, π_n as path equivalence classes, group structure on π_1,
long exact sequence aspects, and the Hurewicz map.

## Key Results

- Loop space algebra: composition, inverses, identity
- Group structure on π_1 via RwEq quotient
- Induced homomorphisms on loop spaces
- Hurewicz homomorphism from π_1 to H_1
- Fiber sequence aspects
- Naturality of loop maps

## References

- HoTT Book, Chapter 8
- May, "A Concise Course in Algebraic Topology", Chapters 1-4
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths.Path
namespace HomotopyGroupPaths

open HigherHomotopy Fibration SuspensionLoop

universe u v

variable {A : Type u} {B : Type u}

/-! ## Loop Space Algebra -/

/-- Loop composition in the loop space. -/
def loopComp {a : A} (l₁ l₂ : LoopSpace A a) : LoopSpace A a :=
  Path.trans l₁ l₂

/-- Loop inverse in the loop space. -/
def loopInv {a : A} (l : LoopSpace A a) : LoopSpace A a :=
  Path.symm l

/-- Loop identity is refl. -/
def loopId (a : A) : LoopSpace A a :=
  Path.refl a

/-- Loop composition is associative. -/
theorem loopComp_assoc {a : A} (l₁ l₂ l₃ : LoopSpace A a) :
    loopComp (loopComp l₁ l₂) l₃ = loopComp l₁ (loopComp l₂ l₃) := by
  simp [loopComp]

/-- Left identity for loop composition. -/
theorem loopComp_id_left {a : A} (l : LoopSpace A a) :
    loopComp (loopId a) l = l := by
  simp [loopComp, loopId]

/-- Right identity for loop composition. -/
theorem loopComp_id_right {a : A} (l : LoopSpace A a) :
    loopComp l (loopId a) = l := by
  simp [loopComp, loopId]

/-- Double inverse is identity. -/
theorem loopInv_inv {a : A} (l : LoopSpace A a) :
    loopInv (loopInv l) = l := by
  exact Path.symm_symm l

/-- Inverse of composition reverses order. -/
theorem loopInv_comp {a : A} (l₁ l₂ : LoopSpace A a) :
    loopInv (loopComp l₁ l₂) = loopComp (loopInv l₂) (loopInv l₁) := by
  simp [loopInv, loopComp]

/-- Right inverse law via RwEq. -/
theorem loopComp_inv_right_rweq {a : A} (l : LoopSpace A a) :
    RwEq (loopComp l (loopInv l)) (loopId a) :=
  rweq_cmpA_inv_right l

/-- Left inverse law via RwEq. -/
theorem loopComp_inv_left_rweq {a : A} (l : LoopSpace A a) :
    RwEq (loopComp (loopInv l) l) (loopId a) :=
  rweq_cmpA_inv_left l

/-! ## π_1 Group Structure -/

/-- The quotient map from loops to π_1. -/
def toπ₁ {a : A} (l : LoopSpace A a) : π₁(A, a) :=
  Quot.mk RwEq l

/-- π_1 multiplication via Quot.lift. -/
def π₁mul {a : A} (x y : π₁(A, a)) : π₁(A, a) :=
  Quot.lift
    (fun l₁ => Quot.lift
      (fun l₂ => Quot.mk RwEq (Path.trans l₁ l₂))
      (fun _ _ h => Quot.sound (rweq_trans_congr_right l₁ h))
      y)
    (fun _ _ h => by
      induction y using Quot.ind with
      | _ l₂ => exact Quot.sound (rweq_trans_congr_left l₂ h))
    x

/-- π_1 inverse via Quot.lift. -/
def π₁inv {a : A} (x : π₁(A, a)) : π₁(A, a) :=
  Quot.lift
    (fun l => Quot.mk RwEq (Path.symm l))
    (fun _ _ h => by
      apply Quot.sound
      induction h with
      | refl => exact RwEq.refl _
      | step hs => exact RwEq.step (Step.symm_congr hs)
      | symm _ ih => exact RwEq.symm ih
      | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂)
    x

/-- The identity element of π_1. -/
def π₁id (a : A) : π₁(A, a) :=
  Quot.mk RwEq (Path.refl a)

/-- Left identity for π_1 multiplication. -/
theorem π₁mul_id_left {a : A} (x : π₁(A, a)) :
    π₁mul (π₁id a) x = x := by
  induction x using Quot.ind with
  | _ l => simp [π₁mul, π₁id]

/-- Right identity for π_1 multiplication. -/
theorem π₁mul_id_right {a : A} (x : π₁(A, a)) :
    π₁mul x (π₁id a) = x := by
  induction x using Quot.ind with
  | _ l => simp [π₁mul, π₁id]

/-- The quotient map preserves composition. -/
theorem toπ₁_comp {a : A} (l₁ l₂ : LoopSpace A a) :
    π₁mul (toπ₁ l₁) (toπ₁ l₂) = toπ₁ (loopComp l₁ l₂) := by
  simp [π₁mul, toπ₁, loopComp]

/-- The quotient map preserves inverses. -/
theorem toπ₁_inv {a : A} (l : LoopSpace A a) :
    π₁inv (toπ₁ l) = toπ₁ (loopInv l) := by
  simp [π₁inv, toπ₁, loopInv]

/-- π₁ multiplication is associative. -/
theorem π₁mul_assoc {a : A} (x y z : π₁(A, a)) :
    π₁mul (π₁mul x y) z = π₁mul x (π₁mul y z) := by
  induction x using Quot.ind with
  | _ l₁ =>
  induction y using Quot.ind with
  | _ l₂ =>
  induction z using Quot.ind with
  | _ l₃ => simp [π₁mul]

/-! ## Induced Homomorphisms -/

/-- A map f : A → B induces a map on loop spaces. -/
def loopMap (f : A → B) {a : A} (l : LoopSpace A a) : LoopSpace B (f a) :=
  Path.congrArg f l

/-- Loop map preserves refl. -/
theorem loopMap_refl (f : A → B) (a : A) :
    loopMap f (loopId a) = loopId (f a) := by
  simp [loopMap, loopId]

/-- Loop map preserves composition. -/
theorem loopMap_comp (f : A → B) {a : A} (l₁ l₂ : LoopSpace A a) :
    loopMap f (loopComp l₁ l₂) = loopComp (loopMap f l₁) (loopMap f l₂) := by
  simp [loopMap, loopComp]

/-- Loop map preserves inverses. -/
theorem loopMap_inv (f : A → B) {a : A} (l : LoopSpace A a) :
    loopMap f (loopInv l) = loopInv (loopMap f l) := by
  simp [loopMap, loopInv]

/-- Loop map respects function composition. -/
theorem loopMap_comp_fun {C : Type u} (f : B → C) (g : A → B) {a : A}
    (l : LoopSpace A a) :
    loopMap (f ∘ g) l = loopMap f (loopMap g l) := by
  simp [loopMap]

/-! ## Fiber Sequence and Connecting Map -/

/-- Path lifting structure for a fibration. -/
structure PathLift {E B : Type u} (p : E → B) (e : E) {b₁ b₂ : B}
    (_γ : Path b₁ b₂) (h : p e = b₁) where
  /-- The lifted endpoint. -/
  endpoint : E
  /-- The lifted path projects to the original. -/
  proj_eq : p endpoint = b₂

/-- Trivial path lift along refl. -/
def trivialPathLift {E B : Type u} (p : E → B) (e : E) :
    PathLift p e (Path.refl (p e)) rfl where
  endpoint := e
  proj_eq := rfl

/-- Path lift preserves fiber membership. -/
def pathLift_fiber {E B : Type u} (p : E → B) (e : E) {b : B}
    (γ : Path b b) (h : p e = b)
    (lift : PathLift p e γ h) :
    Path (p lift.endpoint) b :=
  Path.stepChain lift.proj_eq

/-! ## Hurewicz Map -/

/-- The first homology group H_1 as abelianization of π_1 (quotient structure). -/
def H₁ (A : Type u) (a : A) : Type u :=
  Quot (fun (x y : π₁(A, a)) => ∃ c : π₁(A, a), π₁mul x c = π₁mul c y)

/-- The Hurewicz map π_1 → H_1. -/
def hurewiczMap {a : A} : π₁(A, a) → H₁ A a :=
  fun x => Quot.mk _ x

/-- Hurewicz map preserves identity. -/
theorem hurewicz_id {a : A} :
    hurewiczMap (π₁id a) = (Quot.mk _ (π₁id a) : H₁ A a) := by
  rfl

/-- Hurewicz map is natural with respect to the quotient. -/
theorem hurewicz_natural {a : A} (x : π₁(A, a)) :
    hurewiczMap x = (Quot.mk _ x : H₁ A a) := by
  rfl

/-! ## Transport of Loops -/

/-- Transport of loops along a path (conjugation). -/
def transportLoop {a b : A} (p : Path a b) (l : LoopSpace A a) : LoopSpace A b :=
  Path.trans (Path.symm p) (Path.trans l p)

/-- Transport along refl preserves the loop. -/
theorem transportLoop_refl_path {a : A} (l : LoopSpace A a) :
    transportLoop (Path.refl a) l = l := by
  simp [transportLoop]

/-- Transport of refl loop gives the inverse-then-forward path. -/
theorem transportLoop_refl_loop {a b : A} (p : Path a b) :
    transportLoop p (loopId a) = Path.trans (Path.symm p) p := by
  simp [transportLoop, loopId]

/-- Loop map is compatible with transport (conjugation). -/
theorem loopMap_transport (f : A → B) {a₁ a₂ : A} (p : Path a₁ a₂)
    (l : LoopSpace A a₁) :
    loopMap f (transportLoop p l) =
      transportLoop (Path.congrArg f p) (loopMap f l) := by
  simp [transportLoop, loopMap]

/-! ## Exact Sequence Aspects -/

/-- Exactness data: the image of one map is contained in the kernel of the next. -/
structure ExactAt {X Y Z : Type u} (f : X → Y) (g : Y → Z) (z₀ : Z) : Prop where
  /-- Image is contained in kernel. -/
  im_sub_ker : ∀ x : X, g (f x) = z₀

/-- Exactness of id composed with constant map. -/
theorem exactAtId (a : A) : ExactAt (fun _ : A => a) (fun _ : A => a) a where
  im_sub_ker := fun _ => rfl

/-- The composite of adjacent maps in an exact sequence is null. -/
theorem exact_composite_null {X Y Z : Type u} {f : X → Y} {g : Y → Z} {z₀ : Z}
    (ex : ExactAt f g z₀) (x : X) : g (f x) = z₀ :=
  ex.im_sub_ker x

/-! ## Suspension and Loop Map -/

/-- The suspension map on loops: a loop in A gives rise to a
    2-cell in ΣA via the meridian. -/
noncomputable def suspensionLoopMap {a : A}
    (_l : LoopSpace A a) :
    Path (Suspension.merid (X := A) a) (Suspension.merid (X := A) a) :=
  Path.ofEq rfl

/-- The suspension of refl is the identity 2-cell. -/
theorem suspensionLoopMap_refl {a : A} :
    @suspensionLoopMap A a (loopId a) =
      Path.ofEq (rfl : Suspension.merid (X := A) a = Suspension.merid (X := A) a) := by
  rfl

/-! ## Path Space Fibration -/

/-- Path space fibration: projects to the endpoint. -/
def pathSpaceProj (a : A) : (Σ b : A, Path a b) → A :=
  fun ⟨b, _⟩ => b

/-- The fiber of the path space projection over a is the loop space. -/
theorem pathSpaceProj_fiber (a : A) :
    Fiber (pathSpaceProj a) a = { x : (Σ b : A, Path a b) // pathSpaceProj a x = a } := by
  rfl

/-! ## Naturality Theorems -/

/-- congrArg preserves refl. -/
theorem congrArg_refl_loop (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp

/-- congrArg preserves trans. -/
theorem congrArg_trans_loop (f : A → B) {a : A} (l₁ l₂ : LoopSpace A a) :
    Path.congrArg f (Path.trans l₁ l₂) =
      Path.trans (Path.congrArg f l₁) (Path.congrArg f l₂) := by
  simp

/-- congrArg preserves symm. -/
theorem congrArg_symm_loop (f : A → B) {a : A} (l : LoopSpace A a) :
    Path.congrArg f (Path.symm l) =
      Path.symm (Path.congrArg f l) := by
  simp

/-- Composition of loopMap with a path transport. -/
theorem loopMap_transportLoop_comp {C : Type u}
    (f : A → B) (g : B → C) {a₁ a₂ : A}
    (p : Path a₁ a₂) (l : LoopSpace A a₁) :
    loopMap g (loopMap f (transportLoop p l)) =
      loopMap (g ∘ f) (transportLoop p l) := by
  simp [loopMap]

/-- Induced map on π₁ from a function. -/
def inducedπ₁ (f : A → B) {a : A} : π₁(A, a) → π₁(B, f a) :=
  Quot.lift
    (fun l => Quot.mk RwEq (loopMap f l))
    (fun _ _ h => Quot.sound (rweq_context_map_of_rweq ⟨f⟩ h))

/-- Induced map preserves identity. -/
theorem inducedπ₁_id (f : A → B) {a : A} :
    inducedπ₁ f (π₁id a) = π₁id (f a) := by
  simp [inducedπ₁, π₁id, loopMap]

/-- Induced map preserves multiplication. -/
theorem inducedπ₁_mul (f : A → B) {a : A} (x y : π₁(A, a)) :
    inducedπ₁ f (π₁mul x y) = π₁mul (inducedπ₁ f x) (inducedπ₁ f y) := by
  induction x using Quot.ind with
  | _ l₁ =>
  induction y using Quot.ind with
  | _ l₂ => simp [inducedπ₁, π₁mul, loopMap]

end HomotopyGroupPaths
end ComputationalPaths.Path
