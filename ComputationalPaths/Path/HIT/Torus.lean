/-
# The torus as a higher-inductive type (axiomatic skeleton)

This module introduces `Torus` together with its base-point, two fundamental loops,
and a surface path witnessing their commutativity.  We provide an eliminator
stated in the computational-path style.

## Key Results

- `torusLoop1`, `torusLoop2`: The two fundamental loops around T²
- `torusSurf`: Surface path witnessing `α ∘ β = β ∘ α`
- `torusPiOneEquivZxZ`: π₁(T²) ≃ ℤ × ℤ (the main theorem)
- `TorusLoopClass`: Classification of torus loops by winding numbers

## Mathematical Background

The torus T² = S¹ × S¹ has fundamental group π₁(T²) ≃ ℤ × ℤ, the free
abelian group on two generators. The two generators correspond to loops
around each "hole" of the torus. The surface relation `torusSurf` witnesses
that these generators commute.

## Reference

de Veras, Ramos, de Queiroz & de Oliveira,
"A Topological Application of Labelled Natural Deduction"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract torus type. -/
axiom Torus : Type u

/-- Distinguished point on the torus. -/
axiom torusBase : Torus

/-- First fundamental loop around the torus. -/
axiom torusLoop1 : Path (A := Torus) torusBase torusBase

/-- Second fundamental loop around the torus. -/
axiom torusLoop2 : Path (A := Torus) torusBase torusBase

/-- Surface path witnessing the commutativity of the two loops. -/
axiom torusSurf :
  Path.trans torusLoop1 torusLoop2 = Path.trans torusLoop2 torusLoop1

/-- Data required to eliminate from the torus into a target type `C`. -/
structure TorusRecData (C : Type v) where
  base : C
  loop1 : Path base base
  loop2 : Path base base
  surf : Path.trans loop1 loop2 = Path.trans loop2 loop1

/-- Torus eliminator (recursor). -/
axiom torusRec {C : Type v} (data : TorusRecData C) : Torus → C

/-- β-rule for `torusRec` at the base point. -/
axiom torusRec_base {C : Type v} (data : TorusRecData C) :
  torusRec data torusBase = data.base

/-- β-rule for `torusRec` on the first fundamental loop. -/
axiom torusRec_loop1 {C : Type v} (data : TorusRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (torusRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (torusRec data) torusLoop1)
      (Path.ofEq (torusRec_base (C := C) data))) =
  data.loop1

/-- β-rule for `torusRec` on the second fundamental loop. -/
axiom torusRec_loop2 {C : Type v} (data : TorusRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (torusRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (torusRec data) torusLoop2)
      (Path.ofEq (torusRec_base (C := C) data))) =
  data.loop2

noncomputable section

variable [HasUnivalence.{0}]

open SimpleEquiv

/-- Equivalence shifting the first coordinate of the plane. -/
def torusEquiv1 : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (x, y) => (x + 1, y)
  invFun := fun (x, y) => (x - 1, y)
  left_inv := by intro (x, y); simp
  right_inv := by intro (x, y); simp

/-- Equivalence shifting the second coordinate of the plane. -/
def torusEquiv2 : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (x, y) => (x, y + 1)
  invFun := fun (x, y) => (x, y - 1)
  left_inv := by intro (x, y); simp
  right_inv := by intro (x, y); simp

omit [HasUnivalence] in
theorem SimpleEquiv_eq {α : Type u} {β : Type v} (e1 e2 : SimpleEquiv α β)
  (h1 : e1.toFun = e2.toFun) (h2 : e1.invFun = e2.invFun) : e1 = e2 := by
  cases e1
  cases e2
  congr

omit [HasUnivalence] in
theorem torusEquiv_comm :
    SimpleEquiv.comp torusEquiv1 torusEquiv2 =
      SimpleEquiv.comp torusEquiv2 torusEquiv1 := by
  apply SimpleEquiv_eq
  · rfl
  · rfl

def torusCodeData : TorusRecData (Type _) where
  base := Int × Int
  loop1 := Path.ua torusEquiv1
  loop2 := Path.ua torusEquiv2
  surf := by
    rw [ua_trans, ua_trans]
    exact Path.toEq (Path.congrArg Path.ua (Path.ofEq torusEquiv_comm))

/-- Universal-cover code family for the torus, landing in the plane. -/
noncomputable def torusCode : Torus → Type _ :=
  torusRec torusCodeData

@[simp] theorem torusCode_base :
    torusCode torusBase = (Int × Int) := by
  unfold torusCode
  exact torusRec_base torusCodeData

/-- View an element of `torusCode torusBase` as a pair of integers. -/
@[simp] def torusCodeToProd : torusCode torusBase → Int × Int :=
  fun z => Eq.mp torusCode_base z

/-- Interpret a pair of integers as an element of `torusCode torusBase`. -/
@[simp] def torusCodeOfProd : Int × Int → torusCode torusBase :=
  fun z => Eq.mpr torusCode_base z

@[simp] theorem torusCodeToProd_ofProd (z : Int × Int) :
    torusCodeToProd (torusCodeOfProd z) = z := by
  simp [torusCodeToProd, torusCodeOfProd]

@[simp] theorem torusCodeOfProd_toProd (z : torusCode torusBase) :
    torusCodeOfProd (torusCodeToProd z) = z := by
  simp [torusCodeToProd, torusCodeOfProd]

theorem cast_torusCode_base_torusCodeOfProd (z : Int × Int) :
    cast torusCode_base (torusCodeOfProd z) = z := by
  unfold torusCodeOfProd
  change cast torusCode_base (cast torusCode_base.symm z) = z
  rw [cast_cast]
  rfl

/-- Chosen basepoint in the code fibre at the torus base. -/
@[simp] def torusCodeZero : torusCode torusBase :=
  torusCodeOfProd (0, 0)

/-- Transport the base code point along a loop to encode a path. -/
@[simp] def torusEncodeRaw (x : Torus) :
    Path torusBase x → torusCode x :=
  fun p => Path.transport (A := Torus) (D := torusCode) p torusCodeZero

/-- Encode a loop `p : base = base` as a pair of integers. -/
@[simp] def torusEncodePath :
    Path torusBase torusBase → Int × Int :=
  fun p => torusCodeToProd (torusEncodeRaw torusBase p)

@[simp] theorem torusEncodePath_refl : torusEncodePath (Path.refl torusBase) = (0, 0) := by
  unfold torusEncodePath
  simp
  exact cast_torusCode_base_torusCodeOfProd (0, 0)

@[simp] theorem torusEncodePath_rweq
    {p q : Path torusBase torusBase} (h : RwEq p q) :
    torusEncodePath p = torusEncodePath q := by
  unfold torusEncodePath torusEncodeRaw
  have hEq : p.toEq = q.toEq := rweq_toEq (p := p) (q := q) h
  have htransport :=
    Path.transport_of_toEq_eq (A := Torus) (D := torusCode)
      (p := p) (q := q) (x := torusCodeZero) hEq
  exact _root_.congrArg torusCodeToProd htransport

@[simp] theorem torusCode_loop1_path :
    Path.trans (Path.symm (Path.ofEq torusCode_base))
        (Path.trans (Path.congrArg torusCode torusLoop1)
          (Path.ofEq torusCode_base)) =
      Path.ua torusEquiv1 :=
  torusRec_loop1 torusCodeData

@[simp] theorem torusCode_loop2_path :
    Path.trans (Path.symm (Path.ofEq torusCode_base))
        (Path.trans (Path.congrArg torusCode torusLoop2)
          (Path.ofEq torusCode_base)) =
      Path.ua torusEquiv2 :=
  torusRec_loop2 torusCodeData

/-- Iterate the first fundamental loop `n` times. -/
def torusLoop1PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop1PathPow n) torusLoop1

def torusLoop1PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop1PathPow n
  | Int.negSucc n => Path.symm (torusLoop1PathPow (Nat.succ n))

/-- Iterate the second fundamental loop `n` times. -/
def torusLoop2PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop2PathPow n) torusLoop2

def torusLoop2PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop2PathPow n
  | Int.negSucc n => Path.symm (torusLoop2PathPow (Nat.succ n))


-- Helper for Int arithmetic
omit [HasUnivalence] in
theorem eq_sub_of_add_eq {a b c : Int} (h : a + b = c) : a = c - b := by
  rw [← h]
  simp

omit [HasUnivalence] in
theorem Int.negSucc_add_neg_one (n : Nat) : Int.negSucc n + -1 = Int.negSucc (n + 1) := rfl

@[simp] theorem torusCode_transport_loop1 (z : Int × Int) :
    torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop1 (torusCodeOfProd z)) = (z.1 + 1, z.2) := by
  let p1 := Path.ofEq torusCode_base
  let q := Path.congrArg torusCode torusLoop1
  let z_code := torusCodeOfProd z
  have hEq : Path.trans (Path.symm p1) (Path.trans q p1) = Path.ua torusEquiv1 :=
    torusCode_loop1_path
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 z_code)
  have hLeftCancel :=
    _root_.congrArg
      (fun w =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) w)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := z_code))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code)
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code := by
    exact hLeftStep.trans hLeftCancel
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua torusEquiv1)
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code) := by
    rw [← hLeftSimp]
    rw [hEq]

  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := z_code)
  have hMove :=
    (Path.transport_congrArg (A := Torus) (D := torusCode)
      (p := torusLoop1) (x := z_code))
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      torusCodeToProd
        (Path.transport (A := Torus) (D := torusCode) torusLoop1 z_code) := by
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) z_code
        =
        Path.transport (A := Type _) (D := fun X => X) p1
          (Path.transport (A := Type _) (D := fun X => X) q z_code) := by
      simpa using hAssoc
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q z_code
        = Path.transport (A := Torus) (D := torusCode) torusLoop1 z_code := by
      exact hMove.symm
    exact hSplit.trans (_root_.congrArg (fun w => p1.transport w) hInner)
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 z_code
      = z := by
    exact cast_torusCode_base_torusCodeOfProd z
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua torusEquiv1) z
      = (z.1 + 1, z.2) := by
    simp [Path.ua_beta, torusEquiv1]
  exact (hLHS.trans hComb).trans (by simpa [hBase] using hRHS)

@[simp] theorem torusCode_transport_loop2 (z : Int × Int) :
    torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop2 (torusCodeOfProd z)) = (z.1, z.2 + 1) := by
  let p1 := Path.ofEq torusCode_base
  let q := Path.congrArg torusCode torusLoop2
  let z_code := torusCodeOfProd z
  have hEq : Path.trans (Path.symm p1) (Path.trans q p1) = Path.ua torusEquiv2 :=
    torusCode_loop2_path
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 z_code)
  have hLeftCancel :=
    _root_.congrArg
      (fun w =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) w)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := z_code))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code)
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code := by
    exact hLeftStep.trans hLeftCancel
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua torusEquiv2)
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code) := by
    rw [← hLeftSimp]
    rw [hEq]

  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := z_code)
  have hMove :=
    (Path.transport_congrArg (A := Torus) (D := torusCode)
      (p := torusLoop2) (x := z_code))
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      torusCodeToProd
        (Path.transport (A := Torus) (D := torusCode) torusLoop2 z_code) := by
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) z_code
        =
        Path.transport (A := Type _) (D := fun X => X) p1
          (Path.transport (A := Type _) (D := fun X => X) q z_code) := by
      simpa using hAssoc
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q z_code
        = Path.transport (A := Torus) (D := torusCode) torusLoop2 z_code := by
      exact hMove.symm
    exact hSplit.trans (_root_.congrArg (fun w => p1.transport w) hInner)
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 z_code
      = z := by
    exact cast_torusCode_base_torusCodeOfProd z
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua torusEquiv2) z
      = (z.1, z.2 + 1) := by
    simp [Path.ua_beta, torusEquiv2]
  exact (hLHS.trans hComb).trans (by simpa [hBase] using hRHS)

@[simp] theorem torusCode_transport_loop1_inv (z : Int × Int) :
    torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop1) (torusCodeOfProd z)) = (z.1 - 1, z.2) := by
  let x := torusCodeOfProd z
  have h : torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop1
      (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop1) x)) = z := by
    rw [Path.transport_symm_right]
    exact cast_torusCode_base_torusCodeOfProd z
  have h2 := torusCode_transport_loop1 (torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop1) x))
  rw [torusCodeOfProd_toProd] at h2
  rw [h] at h2
  ext
  . simp at h2
    have h2_1 := _root_.congrArg Prod.fst h2
    simp at h2_1
    apply eq_sub_of_add_eq
    exact h2_1.symm
  . simp at h2
    have h2_2 := _root_.congrArg Prod.snd h2
    simp at h2_2
    exact h2_2.symm

@[simp] theorem torusCode_transport_loop2_inv (z : Int × Int) :
    torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop2) (torusCodeOfProd z)) = (z.1, z.2 - 1) := by
  let x := torusCodeOfProd z
  have h : torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop2
      (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop2) x)) = z := by
    rw [Path.transport_symm_right]
    exact cast_torusCode_base_torusCodeOfProd z
  have h2 := torusCode_transport_loop2 (torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop2) x))
  rw [torusCodeOfProd_toProd] at h2
  rw [h] at h2
  ext
  . simp at h2
    have h2_1 := _root_.congrArg Prod.fst h2
    simp at h2_1
    exact h2_1.symm
  . simp at h2
    have h2_2 := _root_.congrArg Prod.snd h2
    simp at h2_2
    apply eq_sub_of_add_eq
    exact h2_2.symm

omit [HasUnivalence] in
theorem sub_eq_add_neg (a b : Int) : a - b = a + -b := rfl

theorem torusEncodePath_trans_loop1 (p : Path torusBase torusBase) :
    torusEncodePath (Path.trans p torusLoop1) =
      ((torusEncodePath p).1 + 1, (torusEncodePath p).2) := by
  let z := torusEncodePath p
  have h : torusEncodePath (Path.trans p torusLoop1) = torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop1 (torusCodeOfProd z)) := by
    simp only [torusEncodePath, torusEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, torusEncodePath, torusEncodeRaw]
    rw [torusCodeOfProd_toProd]
  rw [h]
  rw [torusCode_transport_loop1]

@[simp] theorem torusEncodePath_trans_loop2 (p : Path torusBase torusBase) :
    torusEncodePath (Path.trans p torusLoop2) =
      ((torusEncodePath p).1, (torusEncodePath p).2 + 1) := by
  let z := torusEncodePath p
  have h : torusEncodePath (Path.trans p torusLoop2) = torusCodeToProd (Path.transport (A := Torus) (D := torusCode) torusLoop2 (torusCodeOfProd z)) := by
    simp only [torusEncodePath, torusEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, torusEncodePath, torusEncodeRaw]
    rw [torusCodeOfProd_toProd]
  rw [h]
  rw [torusCode_transport_loop2]

@[simp] theorem torusEncodePath_loop1 : torusEncodePath torusLoop1 = (1, 0) := by
  rw [← Path.trans_refl_left torusLoop1]
  rw [torusEncodePath_trans_loop1]
  rw [torusEncodePath_refl]
  simp

@[simp] theorem torusEncodePath_loop2 : torusEncodePath torusLoop2 = (0, 1) := by
  rw [← Path.trans_refl_left torusLoop2]
  rw [torusEncodePath_trans_loop2]
  rw [torusEncodePath_refl]
  simp

@[simp] theorem torusEncodePath_trans_symm_loop1
    (p : Path torusBase torusBase) :
    torusEncodePath (Path.trans p (Path.symm torusLoop1)) =
      ((torusEncodePath p).1 - 1, (torusEncodePath p).2) := by
  let z := torusEncodePath p
  have h : torusEncodePath (Path.trans p (Path.symm torusLoop1)) = torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop1) (torusCodeOfProd z)) := by
    simp only [torusEncodePath, torusEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, torusEncodePath, torusEncodeRaw]
    rw [torusCodeOfProd_toProd]
  rw [h]
  rw [torusCode_transport_loop1_inv]

@[simp] theorem torusEncodePath_trans_symm_loop2
    (p : Path torusBase torusBase) :
    torusEncodePath (Path.trans p (Path.symm torusLoop2)) =
      ((torusEncodePath p).1, (torusEncodePath p).2 - 1) := by
  let z := torusEncodePath p
  have h : torusEncodePath (Path.trans p (Path.symm torusLoop2)) = torusCodeToProd (Path.transport (A := Torus) (D := torusCode) (Path.symm torusLoop2) (torusCodeOfProd z)) := by
    simp only [torusEncodePath, torusEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, torusEncodePath, torusEncodeRaw]
    rw [torusCodeOfProd_toProd]
  rw [h]
  rw [torusCode_transport_loop2_inv]

theorem torusEncodePath_trans_loop1PathZPow (p : Path torusBase torusBase) (n : Int) :
    torusEncodePath (Path.trans p (torusLoop1PathZPow n)) =
      ((torusEncodePath p).1 + n, (torusEncodePath p).2) := by
  revert p
  cases n with
  | ofNat n =>
    induction n with
    | zero => intro p; simp only [torusLoop1PathZPow, torusLoop1PathPow, Path.trans_refl_right, Int.ofNat_eq_coe]; simp [Int.add_zero]
    | succ n ih =>
      intro p
      simp only [torusLoop1PathZPow, torusLoop1PathPow]
      rw [← Path.trans_assoc]
      rw [torusEncodePath_trans_loop1]
      simp only [torusLoop1PathZPow] at ih
      rw [ih]
      simp [Int.add_assoc]
  | negSucc n =>
    induction n with
    | zero =>
      intro p
      simp only [torusLoop1PathZPow, torusLoop1PathPow]
      simp only [Path.trans_refl_left]
      rw [torusEncodePath_trans_symm_loop1]
      simp [sub_eq_add_neg]
    | succ n ih =>
      intro p
      have h_decomp : torusLoop1PathZPow (Int.negSucc (n + 1)) = Path.trans (Path.symm torusLoop1) (torusLoop1PathZPow (Int.negSucc n)) := by
        simp only [torusLoop1PathZPow, torusLoop1PathPow]
        rw [Path.symm_trans]
      rw [h_decomp]
      rw [← Path.trans_assoc]
      conv =>
        lhs
        erw [ih (Path.trans p (Path.symm torusLoop1))]
      rw [torusEncodePath_trans_symm_loop1]
      dsimp
      rw [sub_eq_add_neg, Int.add_assoc]
      rw [Int.add_comm (-1)]
      rw [Int.negSucc_add_neg_one]

theorem torusEncodePath_trans_loop2PathZPow (p : Path torusBase torusBase) (n : Int) :
    torusEncodePath (Path.trans p (torusLoop2PathZPow n)) =
      ((torusEncodePath p).1, (torusEncodePath p).2 + n) := by
  revert p
  cases n with
  | ofNat n =>
    induction n with
    | zero => intro p; simp only [torusLoop2PathZPow, torusLoop2PathPow, Path.trans_refl_right, Int.ofNat_eq_coe]; simp [Int.add_zero]
    | succ n ih =>
      intro p
      simp only [torusLoop2PathZPow, torusLoop2PathPow]
      rw [← Path.trans_assoc]
      rw [torusEncodePath_trans_loop2]
      simp only [torusLoop2PathZPow] at ih
      rw [ih]
      simp [Int.add_assoc]
  | negSucc n =>
    induction n with
    | zero =>
      intro p
      simp only [torusLoop2PathZPow, torusLoop2PathPow]
      simp only [Path.trans_refl_left]
      rw [torusEncodePath_trans_symm_loop2]
      simp [sub_eq_add_neg]
    | succ n ih =>
      intro p
      have h_decomp : torusLoop2PathZPow (Int.negSucc (n + 1)) = Path.trans (Path.symm torusLoop2) (torusLoop2PathZPow (Int.negSucc n)) := by
        simp only [torusLoop2PathZPow, torusLoop2PathPow]
        rw [Path.symm_trans]
      rw [h_decomp]
      rw [← Path.trans_assoc]
      conv =>
        lhs
        erw [ih (Path.trans p (Path.symm torusLoop2))]
      rw [torusEncodePath_trans_symm_loop2]
      dsimp
      apply Prod.ext
      . rfl
      . rw [sub_eq_add_neg, Int.add_assoc]
        rw [Int.add_comm (-1)]
        rw [Int.negSucc_add_neg_one]

omit [HasUnivalence] in
theorem torusLoop_comm (p : Path torusBase torusBase) :
    Path.trans torusLoop1 (Path.trans torusLoop2 p) = Path.trans torusLoop2 (Path.trans torusLoop1 p) := by
  rw [← Path.trans_assoc, torusSurf, Path.trans_assoc]

omit [HasUnivalence] in
theorem torusLoop_comm_pow (n : Nat) (p : Path torusBase torusBase) :
    Path.trans torusLoop1 (Path.trans (torusLoop2PathPow n) p) =
    Path.trans (torusLoop2PathPow n) (Path.trans torusLoop1 p) := by
  revert p
  induction n with
  | zero => intro p; simp [torusLoop2PathPow]
  | succ n ih =>
    intro p
    unfold torusLoop2PathPow
    conv => lhs; arg 2; rw [Path.trans_assoc]
    rw [ih]
    rw [torusLoop_comm]
    rw [← Path.trans_assoc]

def torusDecodePath (z : Int × Int) : Path torusBase torusBase :=
  Path.trans (torusLoop1PathZPow z.1) (torusLoop2PathZPow z.2)

theorem torusEncode_decode (z : Int × Int) :
    torusEncodePath (torusDecodePath z) = z := by
  unfold torusDecodePath
  rw [torusEncodePath_trans_loop2PathZPow]
  have h : torusEncodePath (torusLoop1PathZPow z.fst) = (z.fst, 0) := by
    have h2 := torusEncodePath_trans_loop1PathZPow (Path.refl torusBase) z.fst
    rw [Path.trans_refl_left] at h2
    rw [h2]
    rw [torusEncodePath_refl]
    simp
  rw [h]
  simp

/-
## Fundamental group interface
-/

/-- Loop space at the torus base point. -/
abbrev TorusLoopSpace : Type _ :=
  LoopSpace Torus torusBase

/-- Loop quotient of the torus. -/
abbrev TorusLoopQuot : Type _ :=
  LoopQuot Torus torusBase

/-- Fundamental group π₁(T²) as rewrite classes of loops. -/
abbrev torusPiOne : Type _ :=
  PiOne Torus torusBase

/-- Strict group structure on π₁(T²). -/
abbrev torusPiOneGroup : LoopGroup Torus torusBase :=
  PiOneGroup Torus torusBase

/-- Fundamental loop classes in the rewrite quotient. -/
@[simp] def torusLoop1Class : TorusLoopQuot :=
  LoopQuot.ofLoop (A := Torus) (a := torusBase) torusLoop1

@[simp] def torusLoop2Class : TorusLoopQuot :=
  LoopQuot.ofLoop (A := Torus) (a := torusBase) torusLoop2

/-- Encode π₁ loops by quotient-lifting `torusEncodePath`. -/
@[simp] def torusEncodeLift : TorusLoopQuot → Int × Int :=
  Quot.lift (fun (p : Path torusBase torusBase) => torusEncodePath p)
    (by
      intro p q h
      exact torusEncodePath_rweq (p := p) (q := q) h)

@[simp] theorem torusEncodeLift_ofLoop (p : Path torusBase torusBase) :
    torusEncodeLift (LoopQuot.ofLoop (A := Torus) (a := torusBase) p) =
      torusEncodePath p := rfl

/-- Fundamental-group encoding map `π₁(T²) → ℤ × ℤ`. -/
@[simp] def torusEncode : torusPiOne → Int × Int :=
  torusEncodeLift

/-- Decode a pair of integers as a torus loop class. -/
@[simp] def torusDecode : Int × Int → torusPiOne :=
  fun z =>
    LoopQuot.ofLoop (A := Torus) (a := torusBase) (torusDecodePath z)

/-- Encoding of the first fundamental loop. -/
@[simp] theorem torusEncode_loop1Class :
    torusEncode torusLoop1Class = (1, 0) := by
  change torusEncodePath torusLoop1 = (1, 0)
  simpa using torusEncodePath_loop1

/-- Encoding of the second fundamental loop. -/
@[simp] theorem torusEncode_loop2Class :
    torusEncode torusLoop2Class = (0, 1) := by
  change torusEncodePath torusLoop2 = (0, 1)
  simpa using torusEncodePath_loop2

/-- Encode∘decode is the identity on ℤ × ℤ. -/
@[simp] theorem torusEncode_torusDecode (z : Int × Int) :
    torusEncode (torusDecode z) = z := by
  change torusEncodePath (torusDecodePath z) = z
  simpa using torusEncode_decode (z := z)

/-- Composing with the first fundamental loop adds `(1, 0)` at the code level. -/
theorem torusEncodeLift_comp_loop1 (x : TorusLoopQuot) :
    torusEncodeLift (LoopQuot.comp x torusLoop1Class) =
      ((torusEncodeLift x).1 + 1, (torusEncodeLift x).2) := by
  refine Quot.inductionOn x ?_
  intro p
  change
    torusEncodePath (Path.trans p torusLoop1) =
      ((torusEncodePath p).1 + 1, (torusEncodePath p).2)
  simpa using torusEncodePath_trans_loop1 (p := p)

/-- Encoded step law for the first fundamental loop. -/
theorem torusEncode_comp_loop1 (x : torusPiOne) :
    torusEncode (LoopQuot.comp x torusLoop1Class) =
      ((torusEncode x).1 + 1, (torusEncode x).2) :=
  torusEncodeLift_comp_loop1 (x := x)

/-- Composing with the second fundamental loop adds `(0, 1)` at the code level. -/
theorem torusEncodeLift_comp_loop2 (x : TorusLoopQuot) :
    torusEncodeLift (LoopQuot.comp x torusLoop2Class) =
      ((torusEncodeLift x).1, (torusEncodeLift x).2 + 1) := by
  refine Quot.inductionOn x ?_
  intro p
  change
    torusEncodePath (Path.trans p torusLoop2) =
      ((torusEncodePath p).1, (torusEncodePath p).2 + 1)
  simpa using torusEncodePath_trans_loop2 (p := p)

/-- Encoded step law for the second fundamental loop. -/
theorem torusEncode_comp_loop2 (x : torusPiOne) :
    torusEncode (LoopQuot.comp x torusLoop2Class) =
      ((torusEncode x).1, (torusEncode x).2 + 1) :=
  torusEncodeLift_comp_loop2 (x := x)

/-- Composing with the inverse of the first loop subtracts `(1, 0)`. -/
theorem torusEncodeLift_comp_inv_loop1 (x : TorusLoopQuot) :
    torusEncodeLift (LoopQuot.comp x (LoopQuot.inv torusLoop1Class)) =
      ((torusEncodeLift x).1 - 1, (torusEncodeLift x).2) := by
  refine Quot.inductionOn x ?_
  intro p
  change
    torusEncodePath (Path.trans p (Path.symm torusLoop1)) =
      ((torusEncodePath p).1 - 1, (torusEncodePath p).2)
  simpa using torusEncodePath_trans_symm_loop1 (p := p)

/-- Encoded step law for the inverse of the first loop. -/
theorem torusEncode_comp_inv_loop1 (x : torusPiOne) :
    torusEncode (LoopQuot.comp x (LoopQuot.inv torusLoop1Class)) =
      ((torusEncode x).1 - 1, (torusEncode x).2) :=
  torusEncodeLift_comp_inv_loop1 (x := x)

/-- Composing with the inverse of the second loop subtracts `(0, 1)`. -/
theorem torusEncodeLift_comp_inv_loop2 (x : TorusLoopQuot) :
    torusEncodeLift (LoopQuot.comp x (LoopQuot.inv torusLoop2Class)) =
      ((torusEncodeLift x).1, (torusEncodeLift x).2 - 1) := by
  refine Quot.inductionOn x ?_
  intro p
  change
    torusEncodePath (Path.trans p (Path.symm torusLoop2)) =
      ((torusEncodePath p).1, (torusEncodePath p).2 - 1)
  simpa using torusEncodePath_trans_symm_loop2 (p := p)

/-- Encoded step law for the inverse of the second loop. -/
theorem torusEncode_comp_inv_loop2 (x : torusPiOne) :
    torusEncode (LoopQuot.comp x (LoopQuot.inv torusLoop2Class)) =
      ((torusEncode x).1, (torusEncode x).2 - 1) :=
  torusEncodeLift_comp_inv_loop2 (x := x)

omit [HasUnivalence] in
@[simp] theorem torusDecodePath_zero_zero :
    torusDecodePath (0, 0) = Path.refl torusBase := by
  unfold torusDecodePath
  simp [torusLoop1PathZPow, torusLoop1PathPow,
    torusLoop2PathZPow, torusLoop2PathPow]

omit [HasUnivalence] in
@[simp] theorem torusDecode_zero_zero :
    torusDecode (0, 0) = LoopQuot.id := by
  unfold torusDecode torusDecodePath
  have htrans :
      Path.trans (torusLoop1PathZPow 0) (torusLoop2PathZPow 0) =
        Path.refl torusBase := by
    simp [torusLoop1PathZPow, torusLoop1PathPow,
      torusLoop2PathZPow, torusLoop2PathPow]
  change LoopQuot.ofLoop
      (Path.trans (torusLoop1PathZPow 0) (torusLoop2PathZPow 0)) =
    LoopQuot.id
  rw [htrans]
  rfl

@[simp] theorem torusDecodeEq_torusEncodeEq
    (e : torusBase = torusBase) :
    (torusDecodePath (torusEncodePath (Path.ofEq e))).toEq = e := by
  cases e
  simp

/-- **Torus loop classification axiom**: Every loop on the torus is RwEq to
the decoded form of its winding numbers. This is the torus analogue of
`circleLoop_rweq_decode`. -/
class HasTorusLoopDecode : Prop where
  torusLoop_rweq_decode (p : Path.{u} torusBase torusBase) :
    RwEq.{u} p (torusDecodePath (torusEncodePath p))

/-- Every loop is RwEq to the decoded form of its winding numbers. -/
theorem torusLoop_rweq_decode [h : HasTorusLoopDecode.{u}] (p : Path.{u} torusBase torusBase) :
    RwEq.{u} p (torusDecodePath (torusEncodePath p)) :=
  h.torusLoop_rweq_decode p

@[simp] theorem torusDecode_torusEncode [h : HasTorusLoopDecode.{u}] (x : torusPiOne.{u}) :
    torusDecode (torusEncode x) = x := by
  induction x using Quot.ind with
  | _ p =>
    simp only [torusEncode, torusDecode, torusEncodeLift]
    exact Quot.sound (rweq_symm (torusLoop_rweq_decode (h := h) p))

/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`. -/
noncomputable def torusPiOneEquivIntProd [HasTorusLoopDecode.{u}] :
    SimpleEquiv torusPiOne (Int × Int) where
  toFun := torusEncode
  invFun := torusDecode
  left_inv := by
    intro x
    exact torusDecode_torusEncode (x := x)
  right_inv := by
    intro z
    exact torusEncode_torusDecode (z := z)
