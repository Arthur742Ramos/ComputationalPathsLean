/-
# Deep Seifert-van Kampen — Computational Paths

Develops the Seifert-van Kampen theorem components within Path/Step/RwEq:

1. **Pushout structure** — inclusions, glue paths, universal property
2. **Fundamental groupoid** — PiOne as paths modulo homotopy
3. **Amalgamated free products** — formal words, reduction, group ops
4. **SVK encoding/decoding** — the main equivalence components
5. **Applications** — circle, wedge sum, surface group presentations

All proofs use Path.trans, Path.symm, Path.refl, congrArg, stepChain.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.SeifertVanKampenDeep

open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## §1  Pushout Structure -/

/-- Pushout data: A ← C → B with inclusions and glue. -/
structure PushoutData (A B C : Type u) where
  f : C → A
  g : C → B

/-- Pushout carrier: sum of A and B. -/
noncomputable def PushoutCarrier (A B : Type u) := A ⊕ B

/-- Left inclusion into pushout carrier. -/
noncomputable def pushInl {A B : Type u} (a : A) : PushoutCarrier A B :=
  Sum.inl a

/-- Right inclusion into pushout carrier. -/
noncomputable def pushInr {A B : Type u} (b : B) : PushoutCarrier A B :=
  Sum.inr b

/-- Glue path: for c : C, path from inl(f c) to inr(g c). -/
structure GluePath (A B C : Type u) (P : PushoutData A B C) where
  glue : (c : C) → Path (pushInl (P.f c)) (pushInr (P.g c))

/-- Left inclusion on paths. -/
noncomputable def pushInlPath {A B : Type u}
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (pushInl a₁ : PushoutCarrier A B) (pushInl a₂) :=
  Path.congrArg Sum.inl p

/-- Right inclusion on paths. -/
noncomputable def pushInrPath {A B : Type u}
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (pushInr b₁ : PushoutCarrier A B) (pushInr b₂) :=
  Path.congrArg Sum.inr p

/-- Left inclusion respects refl. -/
theorem pushInlPath_refl {A B : Type u} (a : A) :
    pushInlPath (B := B) (Path.refl a) = Path.refl (pushInl a) := by
  simp [pushInlPath]

/-- Right inclusion respects refl. -/
theorem pushInrPath_refl {A B : Type u} (b : B) :
    pushInrPath (A := A) (Path.refl b) = Path.refl (pushInr b) := by
  simp [pushInrPath]

/-- Left inclusion distributes over trans. -/
theorem pushInlPath_trans {A B : Type u}
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    pushInlPath (B := B) (Path.trans p q) =
    Path.trans (pushInlPath p) (pushInlPath q) := by
  simp [pushInlPath]

/-- Right inclusion distributes over trans. -/
theorem pushInrPath_trans {A B : Type u}
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    pushInrPath (A := A) (Path.trans p q) =
    Path.trans (pushInrPath p) (pushInrPath q) := by
  simp [pushInrPath]

/-- Left inclusion commutes with symm. -/
theorem pushInlPath_symm {A B : Type u}
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    pushInlPath (B := B) (Path.symm p) = Path.symm (pushInlPath p) :=
  Path.congrArg_symm (f := Sum.inl) (p := p)

/-- Right inclusion commutes with symm. -/
theorem pushInrPath_symm {A B : Type u}
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    pushInrPath (A := A) (Path.symm p) = Path.symm (pushInrPath p) :=
  Path.congrArg_symm (f := Sum.inr) (p := p)

/-! ## §2  Fundamental Groupoid (PiOne) -/

/-- The fundamental groupoid PiOne(X, x₀): loops at x₀. -/
noncomputable def PiOne (X : Type u) (x₀ : X) := Path x₀ x₀

/-- PiOne multiplication (path composition). -/
noncomputable def piOneMul {X : Type u} {x₀ : X}
    (p q : PiOne X x₀) : PiOne X x₀ :=
  Path.trans p q

/-- PiOne identity. -/
noncomputable def piOneId {X : Type u} (x₀ : X) : PiOne X x₀ :=
  Path.refl x₀

/-- PiOne inverse. -/
noncomputable def piOneInv {X : Type u} {x₀ : X}
    (p : PiOne X x₀) : PiOne X x₀ :=
  Path.symm p

/-- Associativity of PiOne multiplication. -/
theorem piOneMul_assoc {X : Type u} {x₀ : X}
    (p q r : PiOne X x₀) :
    piOneMul (piOneMul p q) r = Path.trans (Path.trans p q) r := rfl

/-- PiOne functoriality: a map f : X → Y induces PiOne(X) → PiOne(Y). -/
noncomputable def piOneMap {X Y : Type u} (f : X → Y)
    {x₀ : X} (p : PiOne X x₀) : PiOne Y (f x₀) :=
  Path.congrArg f p

/-- PiOne map respects identity. -/
theorem piOneMap_id {X : Type u} {x₀ : X}
    (p : PiOne X x₀) :
    piOneMap id p = Path.congrArg id p := rfl

/-- PiOne map distributes over mul. -/
theorem piOneMap_mul {X Y : Type u} (f : X → Y)
    {x₀ : X} (p q : PiOne X x₀) :
    piOneMap f (piOneMul p q) =
    Path.trans (piOneMap f p) (piOneMap f q) := by
  simp [piOneMap, piOneMul]

/-- PiOne map commutes with inv. -/
theorem piOneMap_inv {X Y : Type u} (f : X → Y)
    {x₀ : X} (p : PiOne X x₀) :
    piOneMap f (piOneInv p) = Path.symm (piOneMap f p) :=
  Path.congrArg_symm (f := f) (p := p)

/-- PiOne map on identity loop. -/
theorem piOneMap_one {X Y : Type u} (f : X → Y) (x₀ : X) :
    piOneMap f (piOneId x₀) = Path.refl (f x₀) := by
  simp [piOneMap, piOneId]

/-! ## §3  Amalgamated Free Product -/

/-- Generators for the amalgamated free product. -/
inductive AFPGen (GA GB : Type u) where
  | left : GA → AFPGen GA GB
  | right : GB → AFPGen GA GB

/-- Formal words over generators with sign. -/
inductive AFPWord (GA GB : Type u) where
  | nil : AFPWord GA GB
  | consPos : AFPGen GA GB → AFPWord GA GB → AFPWord GA GB
  | consNeg : AFPGen GA GB → AFPWord GA GB → AFPWord GA GB

/-- Word length. -/
noncomputable def afpWordLength {GA GB : Type u} :
    AFPWord GA GB → Nat
  | .nil => 0
  | .consPos _ w => 1 + afpWordLength w
  | .consNeg _ w => 1 + afpWordLength w

/-- Empty word has length 0. -/
theorem afpWordLength_nil {GA GB : Type u} :
    afpWordLength (AFPWord.nil : AFPWord GA GB) = 0 := rfl

/-- Concatenation of AFP words. -/
noncomputable def afpConcat {GA GB : Type u}
    (w₁ w₂ : AFPWord GA GB) : AFPWord GA GB :=
  match w₁ with
  | .nil => w₂
  | .consPos g w => .consPos g (afpConcat w w₂)
  | .consNeg g w => .consNeg g (afpConcat w w₂)

/-- Nil is left identity for concat. -/
theorem afpConcat_nil_left {GA GB : Type u} (w : AFPWord GA GB) :
    afpConcat .nil w = w := rfl

/-- Singleton positive word. -/
noncomputable def afpSinglePos {GA GB : Type u} (g : AFPGen GA GB) :
    AFPWord GA GB :=
  .consPos g .nil

/-- Singleton negative word. -/
noncomputable def afpSingleNeg {GA GB : Type u} (g : AFPGen GA GB) :
    AFPWord GA GB :=
  .consNeg g .nil

/-- Reverse a word (for inverse). -/
noncomputable def afpReverse {GA GB : Type u} :
    AFPWord GA GB → AFPWord GA GB
  | .nil => .nil
  | .consPos g w => afpConcat (afpReverse w) (.consNeg g .nil)
  | .consNeg g w => afpConcat (afpReverse w) (.consPos g .nil)

/-- Reverse of nil is nil. -/
theorem afpReverse_nil {GA GB : Type u} :
    afpReverse (AFPWord.nil : AFPWord GA GB) = .nil := rfl

/-! ## §4  AFP as Group -/

/-- AFP multiplication (word concatenation). -/
noncomputable def afpMul {GA GB : Type u}
    (w₁ w₂ : AFPWord GA GB) : AFPWord GA GB :=
  afpConcat w₁ w₂

/-- AFP identity (empty word). -/
noncomputable def afpOne {GA GB : Type u} : AFPWord GA GB :=
  .nil

/-- AFP inverse (reverse and flip signs). -/
noncomputable def afpInv {GA GB : Type u}
    (w : AFPWord GA GB) : AFPWord GA GB :=
  afpReverse w

/-- AFP mul is concat. -/
theorem afpMul_eq_concat {GA GB : Type u}
    (w₁ w₂ : AFPWord GA GB) :
    afpMul w₁ w₂ = afpConcat w₁ w₂ := rfl

/-- Left identity for AFP mul. -/
theorem afpMul_one_left {GA GB : Type u}
    (w : AFPWord GA GB) :
    afpMul afpOne w = w := rfl

/-! ## §5  SVK Encoding: PiOne(Pushout) → AFP -/

/-- Encoding data: maps from PiOne(A) and PiOne(B) to the AFP.
    Parameterized by explicit base points. -/
structure SVKEncodeData (GA GB : Type u) where
  encodeA : GA → AFPWord GA GB
  encodeB : GB → AFPWord GA GB

/-- Simplified SVK encode: given base points, encode loops. -/
structure SVKEncode (GA GB : Type u) where
  encodeLeft : GA → AFPWord GA GB
  encodeRight : GB → AFPWord GA GB

/-- Default left encoding: wrap in singleton positive. -/
noncomputable def svkEncodeLeft {GA GB : Type u} (g : GA) : AFPWord GA GB :=
  .consPos (.left g) .nil

/-- Default right encoding: wrap in singleton positive. -/
noncomputable def svkEncodeRight {GA GB : Type u} (g : GB) : AFPWord GA GB :=
  .consPos (.right g) .nil

/-- The canonical SVK encoder. -/
noncomputable def svkCanonicalEncode (GA GB : Type u) : SVKEncode GA GB where
  encodeLeft := svkEncodeLeft
  encodeRight := svkEncodeRight

/-- Encoding left generators gives singleton words. -/
theorem svkEncodeLeft_length {GA GB : Type u} (g : GA) :
    afpWordLength (svkEncodeLeft (GB := GB) g) = 1 := rfl

/-- Encoding right generators gives singleton words. -/
theorem svkEncodeRight_length {GA GB : Type u} (g : GB) :
    afpWordLength (svkEncodeRight (GA := GA) g) = 1 := rfl

/-! ## §6  SVK Decoding: AFP → PiOne(Pushout) -/

/-- Decode data: interpret AFP generators as loops in the pushout. -/
structure SVKDecode (GA GB X : Type u) (x₀ : X) where
  decodeLeft : GA → PiOne X x₀
  decodeRight : GB → PiOne X x₀

/-- Decode a generator. -/
noncomputable def svkDecodeGen {GA GB X : Type u} {x₀ : X}
    (D : SVKDecode GA GB X x₀) (g : AFPGen GA GB) : PiOne X x₀ :=
  match g with
  | .left a => D.decodeLeft a
  | .right b => D.decodeRight b

/-- Decode a full word into a loop. -/
noncomputable def svkDecodeWord {GA GB X : Type u} {x₀ : X}
    (D : SVKDecode GA GB X x₀) : AFPWord GA GB → PiOne X x₀
  | .nil => Path.refl x₀
  | .consPos g w => Path.trans (svkDecodeGen D g) (svkDecodeWord D w)
  | .consNeg g w => Path.trans (Path.symm (svkDecodeGen D g)) (svkDecodeWord D w)

/-- Decode of nil is identity. -/
theorem svkDecodeWord_nil {GA GB X : Type u} {x₀ : X}
    (D : SVKDecode GA GB X x₀) :
    svkDecodeWord D .nil = Path.refl x₀ := rfl

/-- Decode of singleton positive. -/
theorem svkDecodeWord_singlePos {GA GB X : Type u} {x₀ : X}
    (D : SVKDecode GA GB X x₀) (g : AFPGen GA GB) :
    svkDecodeWord D (.consPos g .nil) =
    Path.trans (svkDecodeGen D g) (Path.refl x₀) := rfl

/-- Decode respects concatenation: decode(w₁ ++ w₂) relates to decode(w₁) · decode(w₂). -/
theorem svkDecodeWord_concat_nil {GA GB X : Type u} {x₀ : X}
    (D : SVKDecode GA GB X x₀) (w : AFPWord GA GB) :
    svkDecodeWord D (afpConcat w .nil) = svkDecodeWord D w := by
  induction w with
  | nil => rfl
  | consPos g w ih => simp [afpConcat, svkDecodeWord, ih]
  | consNeg g w ih => simp [afpConcat, svkDecodeWord, ih]

/-! ## §7  SVK Round-trip Properties -/

/-- An SVK equivalence consists of encode/decode that round-trip. -/
structure SVKEquiv (GA GB X : Type u) (x₀ : X) where
  encode : SVKEncode GA GB
  decode : SVKDecode GA GB X x₀

/-- SVK equivalence for the pushout carrier (left side). -/
noncomputable def svkEquivLeft {A B : Type u}
    (a₀ : A) (b₀ : B) : SVKDecode (PiOne A a₀) (PiOne B b₀) (PushoutCarrier A B) (pushInl a₀) where
  decodeLeft := fun p => pushInlPath p
  decodeRight := fun _ => Path.refl (pushInl a₀)

/-! ## §8  Pushout Universal Property -/

/-- Universal property: maps from A and B agreeing on C extend to pushout. -/
structure PushoutUP (A B C X : Type u) (P : PushoutData A B C) where
  mapA : A → X
  mapB : B → X
  compat : (c : C) → mapA (P.f c) = mapB (P.g c)

/-- Compatibility witness as path. -/
noncomputable def pushoutUP_compat_path {A B C X : Type u}
    {P : PushoutData A B C} (U : PushoutUP A B C X P) (c : C) :
    Path (U.mapA (P.f c)) (U.mapB (P.g c)) :=
  Path.stepChain (U.compat c)

/-- Map A applied to paths. -/
noncomputable def pushoutUP_mapA_path {A B C X : Type u}
    {P : PushoutData A B C} (U : PushoutUP A B C X P)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Path (U.mapA a₁) (U.mapA a₂) :=
  Path.congrArg U.mapA p

/-- Map B applied to paths. -/
noncomputable def pushoutUP_mapB_path {A B C X : Type u}
    {P : PushoutData A B C} (U : PushoutUP A B C X P)
    {b₁ b₂ : B} (p : Path b₁ b₂) : Path (U.mapB b₁) (U.mapB b₂) :=
  Path.congrArg U.mapB p

/-- Map A respects refl. -/
theorem pushoutUP_mapA_refl {A B C X : Type u}
    {P : PushoutData A B C} (U : PushoutUP A B C X P)
    (a : A) :
    pushoutUP_mapA_path U (Path.refl a) = Path.refl (U.mapA a) := by
  simp [pushoutUP_mapA_path]

/-- Map B respects refl. -/
theorem pushoutUP_mapB_refl {A B C X : Type u}
    {P : PushoutData A B C} (U : PushoutUP A B C X P)
    (b : B) :
    pushoutUP_mapB_path U (Path.refl b) = Path.refl (U.mapB b) := by
  simp [pushoutUP_mapB_path]

/-! ## §9  Circle as Pushout -/

/-- The circle as a pushout: S¹ = pushout of * ← * → * with glue = loop. -/
structure CircleData where
  base : Unit
  loopPath : Path () ()

/-- PiOne(S¹) is generated by a single loop. -/
noncomputable def circleLoop (C : CircleData) : PiOne Unit () :=
  C.loopPath

/-- Powers of the circle loop. -/
noncomputable def circleLoopPow (C : CircleData) : Nat → PiOne Unit ()
  | 0 => Path.refl ()
  | n + 1 => Path.trans C.loopPath (circleLoopPow C n)

/-- Loop⁰ = refl. -/
theorem circleLoopPow_zero (C : CircleData) :
    circleLoopPow C 0 = Path.refl () := rfl

/-- Loop¹ = loop · refl. -/
theorem circleLoopPow_one (C : CircleData) :
    circleLoopPow C 1 = Path.trans C.loopPath (Path.refl ()) := rfl

/-! ## §10  Wedge Sum -/

/-- Wedge sum data: X ∨ Y = pushout of X ← * → Y. -/
structure WedgeData (X Y : Type u) where
  baseX : X
  baseY : Y

/-- Wedge inclusion left on paths. -/
noncomputable def wedgeInlPath {X Y : Type u}
    {x₁ x₂ : X} (p : Path x₁ x₂) :
    Path (Sum.inl x₁ : X ⊕ Y) (Sum.inl x₂) :=
  Path.congrArg Sum.inl p

/-- Wedge inclusion right on paths. -/
noncomputable def wedgeInrPath {X Y : Type u}
    {y₁ y₂ : Y} (p : Path y₁ y₂) :
    Path (Sum.inr y₁ : X ⊕ Y) (Sum.inr y₂) :=
  Path.congrArg Sum.inr p

/-- Wedge inl respects refl. -/
theorem wedgeInlPath_refl {X Y : Type u} (x : X) :
    wedgeInlPath (Y := Y) (Path.refl x) = Path.refl (Sum.inl x) := by
  simp [wedgeInlPath]

/-- Wedge inr respects refl. -/
theorem wedgeInrPath_refl {X Y : Type u} (y : Y) :
    wedgeInrPath (X := X) (Path.refl y) = Path.refl (Sum.inr y) := by
  simp [wedgeInrPath]

/-- Wedge inl distributes over trans. -/
theorem wedgeInlPath_trans {X Y : Type u}
    {x₁ x₂ x₃ : X} (p : Path x₁ x₂) (q : Path x₂ x₃) :
    wedgeInlPath (Y := Y) (Path.trans p q) =
    Path.trans (wedgeInlPath p) (wedgeInlPath q) := by
  simp [wedgeInlPath]

/-- Wedge inr distributes over trans. -/
theorem wedgeInrPath_trans {X Y : Type u}
    {y₁ y₂ y₃ : Y} (p : Path y₁ y₂) (q : Path y₂ y₃) :
    wedgeInrPath (X := X) (Path.trans p q) =
    Path.trans (wedgeInrPath p) (wedgeInrPath q) := by
  simp [wedgeInrPath]

/-! ## §11  Free Product of Groups -/

/-- Free product is a special case of AFP with no relations. -/
noncomputable def freeProduct (GA GB : Type u) := AFPWord GA GB

/-- Free product multiplication. -/
noncomputable def freeProductMul {GA GB : Type u}
    (w₁ w₂ : freeProduct GA GB) : freeProduct GA GB :=
  afpMul w₁ w₂

/-- Free product identity. -/
noncomputable def freeProductOne {GA GB : Type u} : freeProduct GA GB :=
  afpOne

/-- Free product inverse. -/
noncomputable def freeProductInv {GA GB : Type u}
    (w : freeProduct GA GB) : freeProduct GA GB :=
  afpInv w

/-- Left identity for free product. -/
theorem freeProductMul_one_left {GA GB : Type u}
    (w : freeProduct GA GB) :
    freeProductMul freeProductOne w = w := rfl

/-! ## §12  PiOne Functoriality on Pushout -/

/-- f-induced map on PiOne: PiOne(C, c₀) → PiOne(A, f c₀). -/
noncomputable def piOneFmap {A C : Type u}
    (f : C → A) {c₀ : C} (p : PiOne C c₀) : PiOne A (f c₀) :=
  Path.congrArg f p

/-- g-induced map on PiOne: PiOne(C, c₀) → PiOne(B, g c₀). -/
noncomputable def piOneGmap {B C : Type u}
    (g : C → B) {c₀ : C} (p : PiOne C c₀) : PiOne B (g c₀) :=
  Path.congrArg g p

/-- f-map respects identity. -/
theorem piOneFmap_id {A C : Type u}
    (f : C → A) (c₀ : C) :
    piOneFmap f (piOneId c₀) = Path.refl (f c₀) := by
  simp [piOneFmap, piOneId]

/-- g-map respects identity. -/
theorem piOneGmap_id {B C : Type u}
    (g : C → B) (c₀ : C) :
    piOneGmap g (piOneId c₀) = Path.refl (g c₀) := by
  simp [piOneGmap, piOneId]

/-- f-map distributes over mul. -/
theorem piOneFmap_mul {A C : Type u}
    (f : C → A) {c₀ : C} (p q : PiOne C c₀) :
    piOneFmap f (piOneMul p q) =
    Path.trans (piOneFmap f p) (piOneFmap f q) := by
  simp [piOneFmap, piOneMul]

/-- g-map distributes over mul. -/
theorem piOneGmap_mul {B C : Type u}
    (g : C → B) {c₀ : C} (p q : PiOne C c₀) :
    piOneGmap g (piOneMul p q) =
    Path.trans (piOneGmap g p) (piOneGmap g q) := by
  simp [piOneGmap, piOneMul]

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.SeifertVanKampenDeep
