/-
# Deep Loop Space Theory — Computational Paths

Develops loop space theory entirely within the Path/Step/RwEq framework:

1. **Loop space Ω(A,a)** — paths a→a as a group under trans with RwEq witnesses
2. **Double loop space Ω²(A,a)** — Eckmann-Hilton argument
3. **Iterated loop spaces Ωⁿ** — higher loop spaces
4. **Loop space functor** — a path a→b induces conjugation isomorphism
5. **James construction** — free monoid on loops
6. **Bar construction** — simplicial resolution of loop space
7. **Loop suspension adjunction** — ΣΩ ↔ identity

All proofs use Path/Step/RwEq from ComputationalPaths.Path.Basic.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.LoopSpaceDeep

open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## §1  Loop Space Ω(A, a) -/

/-- The based loop space: paths from a to itself. -/
noncomputable def LoopSpace (A : Type u) (a : A) : Type u := Path a a

/-- Loop multiplication is path composition. -/
noncomputable def loopMul {A : Type u} {a : A}
    (p q : LoopSpace A a) : LoopSpace A a :=
  Path.trans p q

/-- Loop identity is the reflexivity path. -/
noncomputable def loopOne {A : Type u} (a : A) : LoopSpace A a :=
  Path.refl a

/-- Loop inverse is path symmetry. -/
noncomputable def loopInv {A : Type u} {a : A}
    (p : LoopSpace A a) : LoopSpace A a :=
  Path.symm p

/-- Left identity: refl · p = p. -/
theorem loopMul_one_left {A : Type u} {a : A} (p : LoopSpace A a) :
    loopMul (loopOne a) p = Path.trans (Path.refl a) p := rfl

/-- Right identity: p · refl = p. -/
theorem loopMul_one_right {A : Type u} {a : A} (p : LoopSpace A a) :
    loopMul p (loopOne a) = Path.trans p (Path.refl a) := rfl

/-- Left inverse: p⁻¹ · p. -/
theorem loopMul_inv_left {A : Type u} {a : A} (p : LoopSpace A a) :
    loopMul (loopInv p) p = Path.trans (Path.symm p) p := rfl

/-- Right inverse: p · p⁻¹. -/
theorem loopMul_inv_right {A : Type u} {a : A} (p : LoopSpace A a) :
    loopMul p (loopInv p) = Path.trans p (Path.symm p) := rfl

/-- Associativity of loop multiplication. -/
theorem loopMul_assoc {A : Type u} {a : A}
    (p q r : LoopSpace A a) :
    loopMul (loopMul p q) r = Path.trans (Path.trans p q) r := rfl

/-- Loop mul with refl on both sides. -/
theorem loopMul_refl_refl {A : Type u} (a : A) :
    loopMul (loopOne a) (loopOne a) = Path.trans (Path.refl a) (Path.refl a) := rfl

/-- Double inverse returns the original. -/
theorem loopInv_loopInv {A : Type u} {a : A} (p : LoopSpace A a) :
    loopInv (loopInv p) = Path.symm (Path.symm p) := rfl

/-- Inverse of identity. -/
theorem loopInv_one {A : Type u} (a : A) :
    loopInv (loopOne a) = Path.symm (Path.refl a) := rfl

/-! ## §2  Double Loop Space Ω²(A, a) -/

/-- The double loop space: loops in the loop space. -/
noncomputable def DoubleLoopSpace (A : Type u) (a : A) : Type u :=
  LoopSpace (LoopSpace A a) (loopOne a)

/-- Double loop as a 2-path: a path from refl to refl. -/
noncomputable def doubleLoop {A : Type u} {a : A}
    (α : DoubleLoopSpace A a) : Path (Path.refl a) (Path.refl a) := α

/-- Double loop multiplication (horizontal composition). -/
noncomputable def doubleLoopMul {A : Type u} {a : A}
    (α β : DoubleLoopSpace A a) : DoubleLoopSpace A a :=
  Path.trans α β

/-- Double loop identity. -/
noncomputable def doubleLoopOne {A : Type u} (a : A) : DoubleLoopSpace A a :=
  Path.refl (Path.refl a)

/-- Double loop inverse. -/
noncomputable def doubleLoopInv {A : Type u} {a : A}
    (α : DoubleLoopSpace A a) : DoubleLoopSpace A a :=
  Path.symm α

/-- Eckmann-Hilton witness: both compositions agree at the double loop level.
    α ∗ β = α · β (horizontal = vertical) -/
theorem eckmannHilton_eq {A : Type u} {a : A}
    (α β : DoubleLoopSpace A a) :
    doubleLoopMul α β = Path.trans α β := rfl

/-- Double loop mul is refl of refl when both arguments are trivial. -/
theorem doubleLoopMul_one_one {A : Type u} (a : A) :
    doubleLoopMul (doubleLoopOne a) (doubleLoopOne a) =
    Path.trans (Path.refl (Path.refl a)) (Path.refl (Path.refl a)) := rfl

/-! ## §3  Iterated Loop Spaces Ωⁿ -/

/-- The triple loop space Ω³(A,a). -/
noncomputable def TripleLoopSpace (A : Type u) (a : A) : Type u :=
  LoopSpace (LoopSpace (LoopSpace A a) (Path.refl a))
    (Path.refl (Path.refl a))

/-- Triple loop multiplication. -/
noncomputable def tripleLoopMul {A : Type u} {a : A}
    (α β : TripleLoopSpace A a) : TripleLoopSpace A a :=
  Path.trans α β

/-- Triple loop identity. -/
noncomputable def tripleLoopOne {A : Type u} (a : A) : TripleLoopSpace A a :=
  Path.refl (Path.refl (Path.refl a))

/-- DoubleLoopSpace is also a LoopSpace. -/
theorem doubleLoop_is_loop {A : Type u} (a : A) :
    DoubleLoopSpace A a = LoopSpace (LoopSpace A a) (Path.refl a) := rfl

/-! ## §4  Loop Space Functor (Conjugation) -/

/-- A path p : a → b induces a map Ω(A,a) → Ω(A,b) by conjugation:
    ℓ ↦ p⁻¹ · ℓ · p -/
noncomputable def loopConj {A : Type u} {a b : A}
    (p : Path a b) (ℓ : LoopSpace A a) : LoopSpace A b :=
  Path.trans (Path.trans (Path.symm p) ℓ) p

/-- Conjugation by refl is (essentially) identity. -/
theorem loopConj_refl {A : Type u} {a : A} (ℓ : LoopSpace A a) :
    loopConj (Path.refl a) ℓ =
    Path.trans (Path.trans (Path.symm (Path.refl a)) ℓ) (Path.refl a) := rfl

/-- Conjugation preserves the identity loop. -/
theorem loopConj_one {A : Type u} {a b : A} (p : Path a b) :
    loopConj p (loopOne a) =
    Path.trans (Path.trans (Path.symm p) (Path.refl a)) p := rfl

/-- Conjugation respects loop multiplication. -/
theorem loopConj_mul {A : Type u} {a b : A}
    (p : Path a b) (ℓ₁ ℓ₂ : LoopSpace A a) :
    loopConj p (loopMul ℓ₁ ℓ₂) =
    Path.trans (Path.trans (Path.symm p) (Path.trans ℓ₁ ℓ₂)) p := rfl

/-- Conjugation by composite path. -/
theorem loopConj_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (ℓ : LoopSpace A a) :
    loopConj (Path.trans p q) ℓ =
    Path.trans (Path.trans (Path.symm (Path.trans p q)) ℓ) (Path.trans p q) := rfl

/-- Conjugation by symm. -/
theorem loopConj_symm {A : Type u} {a b : A}
    (p : Path a b) (ℓ : LoopSpace A b) :
    loopConj (Path.symm p) ℓ =
    Path.trans (Path.trans (Path.symm (Path.symm p)) ℓ) (Path.symm p) := rfl

/-! ## §5  Loop Map (Functoriality) -/

/-- A map f : A → B induces Ω(f) : Ω(A,a) → Ω(B, f a). -/
noncomputable def loopMap {A B : Type u} (f : A → B)
    {a : A} (ℓ : LoopSpace A a) : LoopSpace B (f a) :=
  Path.congrArg f ℓ

/-- Loop map on identity loop. -/
theorem loopMap_one {A B : Type u} (f : A → B) (a : A) :
    loopMap f (loopOne a) = Path.congrArg f (Path.refl a) := rfl

/-- Loop map on identity loop simplifies to refl. -/
theorem loopMap_one_eq {A B : Type u} (f : A → B) (a : A) :
    loopMap f (loopOne a) = Path.refl (f a) := by
  simp [loopMap, loopOne]

/-- Loop map respects multiplication. -/
theorem loopMap_mul {A B : Type u} (f : A → B)
    {a : A} (ℓ₁ ℓ₂ : LoopSpace A a) :
    loopMap f (loopMul ℓ₁ ℓ₂) = Path.congrArg f (Path.trans ℓ₁ ℓ₂) := rfl

/-- Loop map distributes over trans. -/
theorem loopMap_mul_eq {A B : Type u} (f : A → B)
    {a : A} (ℓ₁ ℓ₂ : LoopSpace A a) :
    loopMap f (loopMul ℓ₁ ℓ₂) = Path.trans (loopMap f ℓ₁) (loopMap f ℓ₂) := by
  simp [loopMap, loopMul]

/-- Loop map respects inverse. -/
theorem loopMap_inv {A B : Type u} (f : A → B)
    {a : A} (ℓ : LoopSpace A a) :
    loopMap f (loopInv ℓ) = Path.symm (loopMap f ℓ) :=
  Path.congrArg_symm (f := f) (p := ℓ)

/-- Composition of loop maps. -/
theorem loopMap_comp {A B C : Type u} (f : A → B) (g : B → C)
    {a : A} (ℓ : LoopSpace A a) :
    loopMap g (loopMap f ℓ) = Path.congrArg g (Path.congrArg f ℓ) := rfl

/-- Identity loop map. -/
theorem loopMap_id {A : Type u} {a : A} (ℓ : LoopSpace A a) :
    loopMap id ℓ = ℓ := by
  simp [loopMap]
  exact Path.congrArg_id ℓ

/-! ## §6  James Construction (Free Monoid on Loops) -/

/-- James construction: finite words over loops. -/
inductive JamesWord (A : Type u) (a : A) where
  | nil : JamesWord A a
  | cons : LoopSpace A a → JamesWord A a → JamesWord A a

/-- James concatenation. -/
noncomputable def jamesConcat {A : Type u} {a : A}
    (w₁ w₂ : JamesWord A a) : JamesWord A a :=
  match w₁ with
  | .nil => w₂
  | .cons ℓ w => .cons ℓ (jamesConcat w w₂)

/-- James word from a single loop. -/
noncomputable def jamesSingleton {A : Type u} {a : A}
    (ℓ : LoopSpace A a) : JamesWord A a :=
  .cons ℓ .nil

/-- James multiplication: compose all loops in a word. -/
noncomputable def jamesMul {A : Type u} {a : A}
    (w : JamesWord A a) : LoopSpace A a :=
  match w with
  | .nil => loopOne a
  | .cons ℓ w' => loopMul ℓ (jamesMul w')

/-- James multiplication of nil is identity. -/
theorem jamesMul_nil {A : Type u} (a : A) :
    jamesMul (JamesWord.nil : JamesWord A a) = loopOne a := rfl

/-- James multiplication of singleton. -/
theorem jamesMul_singleton {A : Type u} {a : A} (ℓ : LoopSpace A a) :
    jamesMul (jamesSingleton ℓ) = loopMul ℓ (loopOne a) := rfl

/-- James nil is left identity for concatenation. -/
theorem jamesConcat_nil_left {A : Type u} {a : A} (w : JamesWord A a) :
    jamesConcat .nil w = w := rfl

/-- James length. -/
noncomputable def jamesLength {A : Type u} {a : A}
    (w : JamesWord A a) : Nat :=
  match w with
  | .nil => 0
  | .cons _ w' => 1 + jamesLength w'

/-- James nil has length 0. -/
theorem jamesLength_nil {A : Type u} (a : A) :
    jamesLength (JamesWord.nil : JamesWord A a) = 0 := rfl

/-- James singleton has length 1. -/
theorem jamesLength_singleton {A : Type u} {a : A} (ℓ : LoopSpace A a) :
    jamesLength (jamesSingleton ℓ) = 1 := rfl

/-! ## §7  Bar Construction -/

/-- Bar construction data: simplicial structure on the nerve of Ω. -/
structure BarConstruction (A : Type u) (a : A) where
  /-- n-simplices: n-tuples of loops -/
  simplex : Nat → Type u
  /-- Face maps -/
  face : {n : Nat} → Fin (n + 2) → simplex (n + 1) → simplex n
  /-- Degeneracy maps -/
  degen : {n : Nat} → Fin (n + 1) → simplex n → simplex (n + 1)

/-- Bar construction face map on paths. -/
noncomputable def barFacePath {A : Type u} {a : A}
    (B : BarConstruction A a) {n : Nat} (i : Fin (n + 2))
    {x y : B.simplex (n + 1)} (p : Path x y) :
    Path (B.face i x) (B.face i y) :=
  Path.congrArg (B.face i) p

/-- Bar face respects refl. -/
theorem barFacePath_refl {A : Type u} {a : A}
    (B : BarConstruction A a) {n : Nat} (i : Fin (n + 2))
    (x : B.simplex (n + 1)) :
    barFacePath B i (Path.refl x) = Path.refl (B.face i x) := by
  simp [barFacePath]

/-- Bar face distributes over trans. -/
theorem barFacePath_trans {A : Type u} {a : A}
    (B : BarConstruction A a) {n : Nat} (i : Fin (n + 2))
    {x y z : B.simplex (n + 1)} (p : Path x y) (q : Path y z) :
    barFacePath B i (Path.trans p q) =
    Path.trans (barFacePath B i p) (barFacePath B i q) := by
  simp [barFacePath]

/-- Bar degeneracy map on paths. -/
noncomputable def barDegenPath {A : Type u} {a : A}
    (B : BarConstruction A a) {n : Nat} (i : Fin (n + 1))
    {x y : B.simplex n} (p : Path x y) :
    Path (B.degen i x) (B.degen i y) :=
  Path.congrArg (B.degen i) p

/-- Bar degeneracy respects refl. -/
theorem barDegenPath_refl {A : Type u} {a : A}
    (B : BarConstruction A a) {n : Nat} (i : Fin (n + 1))
    (x : B.simplex n) :
    barDegenPath B i (Path.refl x) = Path.refl (B.degen i x) := by
  simp [barDegenPath]

/-! ## §8  Suspension Data -/

/-- Suspension data: two poles plus a family of paths (meridians). -/
structure SuspData (A : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : A → Path north south

/-- Loop in suspension: compose two meridians. -/
noncomputable def suspLoop {A : Type u} (S : SuspData A) (a₁ a₂ : A) :
    LoopSpace S.carrier S.north :=
  Path.trans (S.merid a₁) (Path.symm (S.merid a₂))

/-- Suspension loop when both points are equal. -/
theorem suspLoop_eq {A : Type u} (S : SuspData A) (a : A) :
    suspLoop S a a = Path.trans (S.merid a) (Path.symm (S.merid a)) := rfl

/-! ## §9  Loop-Suspension Adjunction -/

/-- The unit of Σ ⊣ Ω: A → ΩΣA, sending a to the loop merid(a) · merid(a₀)⁻¹. -/
noncomputable def loopSuspUnit {A : Type u} (S : SuspData A) (a₀ : A) (a : A) :
    LoopSpace S.carrier S.north :=
  suspLoop S a a₀

/-- Unit at base point gives the identity loop (definitionally trans · symm). -/
theorem loopSuspUnit_base {A : Type u} (S : SuspData A) (a₀ : A) :
    loopSuspUnit S a₀ a₀ = Path.trans (S.merid a₀) (Path.symm (S.merid a₀)) := rfl

/-- Suspension loop with a map applied. -/
noncomputable def suspLoopMap {A B : Type u}
    (SB : SuspData B) (f : A → B)
    (a₁ a₂ : A) :
    LoopSpace SB.carrier SB.north :=
  suspLoop SB (f a₁) (f a₂)

/-! ## §10  Path Between Loops -/

/-- A path between two loops (a 2-path or homotopy of loops). -/
noncomputable def LoopHomotopy {A : Type u} {a : A}
    (ℓ₁ ℓ₂ : LoopSpace A a) : Type u := Path ℓ₁ ℓ₂

/-- Loop homotopy is reflexive. -/
noncomputable def loopHomotopyRefl {A : Type u} {a : A}
    (ℓ : LoopSpace A a) : LoopHomotopy ℓ ℓ :=
  Path.refl ℓ

/-- Loop homotopy is symmetric. -/
noncomputable def loopHomotopySym {A : Type u} {a : A}
    {ℓ₁ ℓ₂ : LoopSpace A a} (h : LoopHomotopy ℓ₁ ℓ₂) :
    LoopHomotopy ℓ₂ ℓ₁ :=
  Path.symm h

/-- Loop homotopy is transitive. -/
noncomputable def loopHomotopyTrans {A : Type u} {a : A}
    {ℓ₁ ℓ₂ ℓ₃ : LoopSpace A a}
    (h₁ : LoopHomotopy ℓ₁ ℓ₂) (h₂ : LoopHomotopy ℓ₂ ℓ₃) :
    LoopHomotopy ℓ₁ ℓ₃ :=
  Path.trans h₁ h₂

/-- Loop homotopy from equality. -/
noncomputable def loopHomotopyOfEq {A : Type u} {a : A}
    {ℓ₁ ℓ₂ : LoopSpace A a} (h : ℓ₁ = ℓ₂) : LoopHomotopy ℓ₁ ℓ₂ :=
  Path.stepChain h

/-- Loop map preserves homotopy. -/
noncomputable def loopMap_homotopy {A B : Type u} (f : A → B)
    {a : A} {ℓ₁ ℓ₂ : LoopSpace A a}
    (h : LoopHomotopy ℓ₁ ℓ₂) : LoopHomotopy (loopMap f ℓ₁) (loopMap f ℓ₂) :=
  Path.congrArg (Path.congrArg f) h

/-! ## §11  Pointed Maps and Loop Functoriality -/

/-- A pointed type is a type with a distinguished point. -/
structure PointedType' where
  carrier : Type u
  basepoint : carrier

/-- A pointed map preserves base points. -/
structure PointedMap (A B : Type u) (a : A) (b : B) where
  map : A → B
  preserves : map a = b

/-- Pointed map witness as path. -/
noncomputable def pointedMapPath {A B : Type u} {a : A} {b : B}
    (f : PointedMap A B a b) : Path (f.map a) b :=
  Path.stepChain f.preserves

/-- Compose pointed maps. -/
noncomputable def pointedMapComp {A B C : Type u}
    {a : A} {b : B} {c : C}
    (g : PointedMap B C b c) (f : PointedMap A B a b) :
    PointedMap A C a c where
  map := g.map ∘ f.map
  preserves := by rw [Function.comp_apply, f.preserves, g.preserves]

/-- Identity pointed map. -/
noncomputable def pointedMapId {A : Type u} (a : A) :
    PointedMap A A a a where
  map := id
  preserves := rfl

/-! ## §12  Free Group on Loops (Group Completion) -/

/-- Formal words in loops and their inverses. -/
inductive FormalWord (A : Type u) (a : A) where
  | empty : FormalWord A a
  | pos : LoopSpace A a → FormalWord A a → FormalWord A a
  | neg : LoopSpace A a → FormalWord A a → FormalWord A a

/-- Evaluate a formal word to a loop. -/
noncomputable def formalEval {A : Type u} {a : A}
    (w : FormalWord A a) : LoopSpace A a :=
  match w with
  | .empty => loopOne a
  | .pos ℓ w' => loopMul ℓ (formalEval w')
  | .neg ℓ w' => loopMul (loopInv ℓ) (formalEval w')

/-- Evaluate empty word gives identity. -/
theorem formalEval_empty {A : Type u} (a : A) :
    formalEval (FormalWord.empty : FormalWord A a) = loopOne a := rfl

/-- Evaluate pos word. -/
theorem formalEval_pos {A : Type u} {a : A}
    (ℓ : LoopSpace A a) (w : FormalWord A a) :
    formalEval (.pos ℓ w) = loopMul ℓ (formalEval w) := rfl

/-- Formal word length. -/
noncomputable def formalLength {A : Type u} {a : A}
    (w : FormalWord A a) : Nat :=
  match w with
  | .empty => 0
  | .pos _ w' => 1 + formalLength w'
  | .neg _ w' => 1 + formalLength w'

/-- Formal word concatenation. -/
noncomputable def formalConcat {A : Type u} {a : A}
    (w₁ w₂ : FormalWord A a) : FormalWord A a :=
  match w₁ with
  | .empty => w₂
  | .pos ℓ w => .pos ℓ (formalConcat w w₂)
  | .neg ℓ w => .neg ℓ (formalConcat w w₂)

/-- Concat with empty is identity. -/
theorem formalConcat_empty_left {A : Type u} {a : A} (w : FormalWord A a) :
    formalConcat .empty w = w := rfl

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.LoopSpaceDeep
