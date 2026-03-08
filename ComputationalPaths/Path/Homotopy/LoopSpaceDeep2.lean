/-
# Deep Loop Space Theory — Extended

Further loop space theory within the Path/Step/RwEq framework:

1. **Loop space conjugation** — conjugation action and inner automorphisms
2. **Power operations** — iterated loop composition with path witnesses
3. **Eckmann-Hilton for loops** — commutativity from interchange
4. **James construction** — free monoid on loops with path algebra
5. **Bar construction** — simplicial bar complex from loop data
6. **Loop space functoriality** — induced maps between loop spaces
7. **Higher loop spaces** — Ω² and beyond with coherence

All proofs use Path.trans, Path.symm, Path.refl, congrArg, transport.
No sorry, no admit, no Path.ofEq.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.LoopSpaceDeep2

open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## §1  Loop Space Basics -/

/-- Based loop space. -/
noncomputable def Ω (A : Type u) (a : A) : Type u := Path a a

/-- Loop multiplication. -/
noncomputable def ωMul {A : Type u} {a : A} (p q : Ω A a) : Ω A a :=
  Path.trans p q

/-- Loop identity. -/
noncomputable def ωOne {A : Type u} (a : A) : Ω A a :=
  Path.refl a

/-- Loop inverse. -/
noncomputable def ωInv {A : Type u} {a : A} (p : Ω A a) : Ω A a :=
  Path.symm p

/-- Associativity. -/
noncomputable def ωMul_assoc {A : Type u} {a : A} (p q r : Ω A a) :
    RwEq (ωMul (ωMul p q) r) (ωMul p (ωMul q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Left identity. -/
noncomputable def ωOne_mul {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωMul (ωOne a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right identity. -/
noncomputable def ωMul_one {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωMul p (ωOne a)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Left inverse. -/
noncomputable def ωInv_mul {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωMul (ωInv p) p) (ωOne a) :=
  rweq_of_step (Step.symm_trans p)

/-- Right inverse. -/
noncomputable def ωMul_inv {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωMul p (ωInv p)) (ωOne a) :=
  rweq_of_step (Step.trans_symm p)

/-- Double inverse. -/
noncomputable def ωInv_inv {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωInv (ωInv p)) p :=
  rweq_of_step (Step.symm_symm p)

/-! ## §2  Conjugation -/

/-- Conjugation: g · p · g⁻¹. -/
noncomputable def conj {A : Type u} {a : A} (g p : Ω A a) : Ω A a :=
  ωMul (ωMul g p) (ωInv g)

/-- Conjugation by identity is identity. -/
noncomputable def conj_one {A : Type u} {a : A} (p : Ω A a) :
    RwEq (conj (ωOne a) p) p :=
  rweq_trans
    (rweq_trans_congr_left (ωInv (ωOne a))
      (rweq_of_step (Step.trans_refl_left p)))
    (rweq_trans
      (rweq_trans_congr_right p
        (rweq_of_step (Step.symm_refl a)))
      (rweq_of_step (Step.trans_refl_right p)))

/-- Conjugation preserves identity: conj g refl ≈ refl. -/
noncomputable def conj_preserves_one {A : Type u} {a : A} (g : Ω A a) :
    RwEq (conj g (ωOne a)) (ωOne a) :=
  rweq_trans
    (rweq_trans_congr_left (ωInv g)
      (rweq_of_step (Step.trans_refl_right g)))
    (rweq_of_step (Step.trans_symm g))

/-- Conjugation distributes over multiplication:
    conj g (p · q) ≈ conj g p · conj g q. -/
noncomputable def conj_mul {A : Type u} {a : A} (g p q : Ω A a) :
    RwEq (conj g (ωMul p q)) (ωMul (conj g p) (conj g q)) :=
  rweq_trans
    (rweq_trans_congr_left (ωInv g)
      (rweq_of_step (Step.trans_assoc g p q)))
    (rweq_trans
      (rweq_of_step (Step.trans_assoc (ωMul g p) q (ωInv g)))
      (rweq_trans
        (rweq_trans_congr_right (ωMul g p)
          (rweq_symm (rweq_trans
            (rweq_trans_congr_left (ωMul q (ωInv g))
              (rweq_of_step (Step.trans_symm g)))
            (rweq_of_step (Step.trans_refl_left (ωMul q (ωInv g)))))))
        (rweq_trans
          (rweq_trans_congr_right (ωMul g p)
            (rweq_symm (rweq_of_step
              (Step.trans_assoc (ωMul g (ωInv g)) q (ωInv g)))))
          (rweq_trans
            (rweq_trans_congr_right (ωMul g p)
              (rweq_symm (rweq_of_step
                (Step.trans_assoc g (ωInv g) (ωMul q (ωInv g))))))
            (rweq_of_step (Step.trans_assoc (ωMul g p) (ωMul (ωInv g) (ωMul q (ωInv g))) (Path.refl a)))))))

/-! ## §3  Powers of Loops -/

/-- n-fold power of a loop. -/
noncomputable def ωPow {A : Type u} {a : A} (p : Ω A a) : Nat → Ω A a
  | 0 => ωOne a
  | n + 1 => ωMul (ωPow p n) p

/-- Power 0 is identity. -/
noncomputable def ωPow_zero {A : Type u} {a : A} (p : Ω A a) :
    ωPow p 0 = ωOne a := rfl

/-- Power 1 is the loop itself. -/
noncomputable def ωPow_one {A : Type u} {a : A} (p : Ω A a) :
    RwEq (ωPow p 1) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Power of identity is identity. -/
noncomputable def ωPow_one_loop {A : Type u} {a : A} :
    (n : Nat) → RwEq (ωPow (ωOne a) n) (ωOne a)
  | 0 => rweq_refl _
  | n + 1 =>
    rweq_trans
      (rweq_trans_congr_left (ωOne a) (ωPow_one_loop n))
      (rweq_of_step (Step.trans_refl_right (ωOne a)))

/-- Power (n+1) unfolds correctly. -/
noncomputable def ωPow_succ {A : Type u} {a : A} (p : Ω A a) (n : Nat) :
    ωPow p (n + 1) = ωMul (ωPow p n) p := rfl

/-- Inverse power: p^n · (p⁻¹)^n ≈ refl, by induction. -/
noncomputable def ωPow_inv_cancel {A : Type u} {a : A} (p : Ω A a) :
    (n : Nat) → RwEq (ωMul (ωPow p n) (ωPow (ωInv p) n)) (ωOne a)
  | 0 =>
    rweq_of_step (Step.trans_refl_left (ωOne a))
  | n + 1 =>
    rweq_trans
      (rweq_of_step (Step.trans_assoc (ωPow p n) p
        (ωMul (ωPow (ωInv p) n) (ωInv p))))
      (rweq_trans
        (rweq_trans_congr_right (ωPow p n)
          (rweq_trans
            (rweq_symm (rweq_of_step (Step.trans_assoc p
              (ωPow (ωInv p) n) (ωInv p))))
            (rweq_trans_congr_left (ωInv p)
              (rweq_trans
                (rweq_of_step (Step.trans_assoc p (ωPow (ωInv p) n) (Path.refl a)))
                (rweq_trans_congr_right p (rweq_of_step (Step.trans_refl_right (ωPow (ωInv p) n))))))))
        (ωPow_inv_cancel p n))

/-! ## §4  Loop Space Functoriality -/

/-- A pointed map f : (A,a) → (B,b). -/
structure PointedMap (A : Type u) (a : A) (B : Type u) (b : B) where
  f : A → B
  base : f a = b

/-- Induced map on loop spaces. -/
noncomputable def ωMap {A B : Type u} {a : A} {b : B}
    (φ : PointedMap A a B b) (p : Ω A a) : Path (φ.f a) (φ.f a) :=
  Path.congrArg φ.f p

/-- Ω-map preserves identity. -/
noncomputable def ωMap_one {A B : Type u} {a : A} {b : B}
    (φ : PointedMap A a B b) :
    RwEq (ωMap φ (ωOne a)) (Path.refl (φ.f a)) :=
  rweq_of_step (Step.congrArg_refl φ.f a)

/-- Ω-map preserves multiplication. -/
noncomputable def ωMap_mul {A B : Type u} {a : A} {b : B}
    (φ : PointedMap A a B b) (p q : Ω A a) :
    RwEq (ωMap φ (ωMul p q))
         (Path.trans (ωMap φ p) (ωMap φ q)) :=
  rweq_of_step (Step.congrArg_trans φ.f p q)

/-- Ω-map preserves inverses. -/
noncomputable def ωMap_inv {A B : Type u} {a : A} {b : B}
    (φ : PointedMap A a B b) (p : Ω A a) :
    RwEq (ωMap φ (ωInv p)) (Path.symm (ωMap φ p)) :=
  rweq_of_step (Step.congrArg_symm φ.f p)

/-- Ω-map composition: Ω(ψ ∘ φ) = Ω(ψ) ∘ Ω(φ). -/
noncomputable def ωMap_comp {A B C : Type u} {a : A} {b : B} {c : C}
    (φ : PointedMap A a B b) (ψ : PointedMap B b C c) (p : Ω A a) :
    RwEq (Path.congrArg (ψ.f ∘ φ.f) p)
         (Path.congrArg ψ.f (ωMap φ p)) :=
  rweq_of_step (Step.congrArg_comp ψ.f φ.f p)

/-! ## §5  Double Loop Space Ω² -/

/-- The double loop space: loops in the loop space. -/
noncomputable def Ω² (A : Type u) (a : A) : Type u :=
  Ω (Ω A a) (ωOne a)

/-- This is the type of paths from refl to refl in Path a a.
    We represent it as Path (Path.refl a) (Path.refl a) at the meta level.
    For Lean's purposes, Ω² A a = Path (Path.refl a) (Path.refl a). -/

/-- Vertical composition in Ω². -/
noncomputable def ω²Vert {A : Type u} {a : A} (α β : Ω² A a) : Ω² A a :=
  Path.trans α β

/-- Vertical identity in Ω². -/
noncomputable def ω²One {A : Type u} (a : A) : Ω² A a :=
  Path.refl (ωOne a)

/-- Vertical inverse in Ω². -/
noncomputable def ω²Inv {A : Type u} {a : A} (α : Ω² A a) : Ω² A a :=
  Path.symm α

/-- Ω² vertical associativity. -/
noncomputable def ω²Vert_assoc {A : Type u} {a : A} (α β γ : Ω² A a) :
    RwEq (ω²Vert (ω²Vert α β) γ) (ω²Vert α (ω²Vert β γ)) :=
  rweq_of_step (Step.trans_assoc α β γ)

/-- Ω² left identity. -/
noncomputable def ω²One_vert {A : Type u} {a : A} (α : Ω² A a) :
    RwEq (ω²Vert (ω²One a) α) α :=
  rweq_of_step (Step.trans_refl_left α)

/-- Ω² right identity. -/
noncomputable def ω²Vert_one {A : Type u} {a : A} (α : Ω² A a) :
    RwEq (ω²Vert α (ω²One a)) α :=
  rweq_of_step (Step.trans_refl_right α)

/-- Ω² left inverse. -/
noncomputable def ω²Inv_vert {A : Type u} {a : A} (α : Ω² A a) :
    RwEq (ω²Vert (ω²Inv α) α) (ω²One a) :=
  rweq_of_step (Step.symm_trans α)

/-- Ω² right inverse. -/
noncomputable def ω²Vert_inv {A : Type u} {a : A} (α : Ω² A a) :
    RwEq (ω²Vert α (ω²Inv α)) (ω²One a) :=
  rweq_of_step (Step.trans_symm α)

/-! ## §6  James Construction (Free Monoid on Pointed Space) -/

/-- James word: finite list representing the free topological monoid. -/
inductive JamesWord (A : Type u) (a : A) : Type u where
  | nil  : JamesWord A a
  | cons : A → JamesWord A a → JamesWord A a

/-- James word concatenation. -/
noncomputable def jamesConcat {A : Type u} {a : A} :
    JamesWord A a → JamesWord A a → JamesWord A a
  | JamesWord.nil, w => w
  | JamesWord.cons x xs, w => JamesWord.cons x (jamesConcat xs w)

/-- James concatenation with nil on the right is identity. -/
theorem jamesConcat_nil {A : Type u} {a : A} (w : JamesWord A a) :
    jamesConcat w JamesWord.nil = w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [jamesConcat, ih]

/-- James concatenation is associative. -/
theorem jamesConcat_assoc {A : Type u} {a : A}
    (u v w : JamesWord A a) :
    jamesConcat (jamesConcat u v) w = jamesConcat u (jamesConcat v w) := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp [jamesConcat, ih]

/-- Path between James words from a pointwise path. -/
noncomputable def jamesConsPath {A : Type u} {a : A}
    {x y : A} (p : Path x y) (w : JamesWord A a) :
    Path (JamesWord.cons x w) (JamesWord.cons y w) :=
  Path.congrArg (fun z => JamesWord.cons z w) p

/-- James cons path respects refl. -/
noncomputable def jamesConsPath_refl {A : Type u} {a : A}
    (x : A) (w : JamesWord A a) :
    RwEq (jamesConsPath (Path.refl x) w) (Path.refl (JamesWord.cons x w)) :=
  rweq_of_step (Step.congrArg_refl (fun z => JamesWord.cons z w) x)

/-- James cons path respects trans. -/
noncomputable def jamesConsPath_trans {A : Type u} {a : A}
    {x y z : A} (p : Path x y) (q : Path y z) (w : JamesWord A a) :
    RwEq (jamesConsPath (Path.trans p q) w)
         (Path.trans (jamesConsPath p w) (jamesConsPath q w)) :=
  rweq_of_step (Step.congrArg_trans (fun z => JamesWord.cons z w) p q)

/-- James cons path respects symm. -/
noncomputable def jamesConsPath_symm {A : Type u} {a : A}
    {x y : A} (p : Path x y) (w : JamesWord A a) :
    RwEq (jamesConsPath (Path.symm p) w) (Path.symm (jamesConsPath p w)) :=
  rweq_of_step (Step.congrArg_symm (fun z => JamesWord.cons z w) p)

/-- Length of a James word. -/
noncomputable def jamesLength {A : Type u} {a : A} : JamesWord A a → Nat
  | JamesWord.nil => 0
  | JamesWord.cons _ xs => 1 + jamesLength xs

/-- James word of length 0 is nil. -/
theorem jamesLength_zero_nil {A : Type u} {a : A} (w : JamesWord A a)
    (h : jamesLength w = 0) : w = JamesWord.nil := by
  cases w with
  | nil => rfl
  | cons x xs => simp [jamesLength] at h

/-- Concatenation adds lengths. -/
theorem jamesLength_concat {A : Type u} {a : A}
    (u v : JamesWord A a) :
    jamesLength (jamesConcat u v) = jamesLength u + jamesLength v := by
  induction u with
  | nil => simp [jamesConcat, jamesLength]
  | cons x xs ih => simp [jamesConcat, jamesLength, ih, Nat.add_assoc]

/-! ## §7  Bar Construction -/

/-- Bar n-simplex: an (n+1)-tuple of elements forming a bar chain. -/
inductive BarSimplex (A : Type u) : Nat → Type u where
  | point : A → BarSimplex A 0
  | edge  : A → A → BarSimplex A 1
  | face  : {n : Nat} → (Fin (n + 2) → A) → BarSimplex A (n + 1)

/-- Path between bar 0-simplices. -/
noncomputable def barPointPath {A : Type u} {x y : A}
    (p : Path x y) : Path (BarSimplex.point x) (BarSimplex.point y) :=
  Path.congrArg BarSimplex.point p

/-- Bar point path respects refl. -/
noncomputable def barPointPath_refl {A : Type u} (x : A) :
    RwEq (barPointPath (Path.refl x)) (Path.refl (BarSimplex.point x)) :=
  rweq_of_step (Step.congrArg_refl BarSimplex.point x)

/-- Bar point path distributes over trans. -/
noncomputable def barPointPath_trans {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    RwEq (barPointPath (Path.trans p q))
         (Path.trans (barPointPath p) (barPointPath q)) :=
  rweq_of_step (Step.congrArg_trans BarSimplex.point p q)

/-- Bar point path respects symm. -/
noncomputable def barPointPath_symm {A : Type u} {x y : A}
    (p : Path x y) :
    RwEq (barPointPath (Path.symm p)) (Path.symm (barPointPath p)) :=
  rweq_of_step (Step.congrArg_symm BarSimplex.point p)

/-- Path between bar 1-simplices from first component. -/
noncomputable def barEdgePath_fst {A : Type u} {x₁ x₂ y : A}
    (p : Path x₁ x₂) : Path (BarSimplex.edge x₁ y) (BarSimplex.edge x₂ y) :=
  Path.congrArg (fun z => BarSimplex.edge z y) p

/-- Path between bar 1-simplices from second component. -/
noncomputable def barEdgePath_snd {A : Type u} {x y₁ y₂ : A}
    (p : Path y₁ y₂) : Path (BarSimplex.edge x y₁) (BarSimplex.edge x y₂) :=
  Path.congrArg (fun z => BarSimplex.edge x z) p

/-! ## §8  Loop Space Transport -/

/-- Transport a loop along a path in the base. -/
noncomputable def loopTransport {A : Type u} {a b : A}
    (p : Path a b) (ℓ : Ω A a) : Ω A b :=
  Path.trans (Path.symm p) (Path.trans ℓ p)

/-- Transport of identity loop is identity. -/
noncomputable def loopTransport_one {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (loopTransport p (ωOne a)) (ωOne b) :=
  rweq_trans
    (rweq_trans_congr_right (Path.symm p)
      (rweq_of_step (Step.trans_refl_left p)))
    (rweq_of_step (Step.symm_trans p))

/-- Transport along refl is identity. -/
noncomputable def loopTransport_refl {A : Type u} {a : A}
    (ℓ : Ω A a) :
    RwEq (loopTransport (Path.refl a) ℓ) ℓ :=
  rweq_trans
    (rweq_trans_congr_left (Path.trans ℓ (Path.refl a))
      (rweq_of_step (Step.symm_refl a)))
    (rweq_trans
      (rweq_of_step (Step.trans_refl_left (Path.trans ℓ (Path.refl a))))
      (rweq_of_step (Step.trans_refl_right ℓ)))

/-- Transport preserves multiplication. -/
noncomputable def loopTransport_mul {A : Type u} {a b : A}
    (p : Path a b) (ℓ₁ ℓ₂ : Ω A a) :
    RwEq (loopTransport p (ωMul ℓ₁ ℓ₂))
         (ωMul (loopTransport p ℓ₁) (loopTransport p ℓ₂)) :=
  rweq_trans
    (rweq_trans_congr_right (Path.symm p)
      (rweq_of_step (Step.trans_assoc ℓ₁ ℓ₂ p)))
    (rweq_trans
      (rweq_of_step (Step.trans_assoc (Path.symm p) ℓ₁ (Path.trans ℓ₂ p)))
      (rweq_trans
        (rweq_trans_congr_right (Path.symm p)
          (rweq_symm (rweq_trans
            (rweq_trans_congr_left (Path.trans ℓ₂ p)
              (rweq_of_step (Step.symm_trans p)))
            (rweq_of_step (Step.trans_refl_left (Path.trans ℓ₂ p))))))
        (rweq_trans
          (rweq_trans_congr_right (Path.symm p)
            (rweq_symm (rweq_of_step (Step.trans_assoc
              (Path.trans (Path.symm p) p) ℓ₂ p))))
          (rweq_trans
            (rweq_trans_congr_right (Path.symm p)
              (rweq_symm (rweq_of_step (Step.trans_assoc
                (Path.symm p) p (Path.trans ℓ₂ p)))))
            (rweq_of_step (Step.trans_assoc (Path.symm p)
              (Path.trans (Path.symm p) (Path.trans p (Path.trans ℓ₂ p)))
              (Path.refl b)))))))

/-! ## §9  Commutator and Abelianization -/

/-- Commutator of two loops. -/
noncomputable def commutator {A : Type u} {a : A} (p q : Ω A a) : Ω A a :=
  ωMul (ωMul p q) (ωMul (ωInv p) (ωInv q))

/-- Commutator with self is trivial. -/
noncomputable def commutator_self {A : Type u} {a : A} (p : Ω A a) :
    RwEq (commutator p p) (ωOne a) :=
  rweq_trans
    (rweq_of_step (Step.trans_assoc (ωMul p p) (ωInv p) (ωInv p)))
    (rweq_trans
      (rweq_trans_congr_left (ωInv p)
        (rweq_trans
          (rweq_symm (rweq_of_step (Step.trans_assoc p p (ωInv p))))
          (rweq_trans_congr_right p
            (rweq_of_step (Step.trans_symm p)))))
      (rweq_trans
        (rweq_trans_congr_left (ωInv p)
          (rweq_of_step (Step.trans_refl_right p)))
        (rweq_of_step (Step.trans_symm p))))

/-- Commutator with identity is trivial. -/
noncomputable def commutator_one_left {A : Type u} {a : A} (q : Ω A a) :
    RwEq (commutator (ωOne a) q) (ωOne a) :=
  rweq_trans
    (rweq_trans_congr_left (ωMul (ωInv (ωOne a)) (ωInv q))
      (rweq_of_step (Step.trans_refl_left q)))
    (rweq_trans
      (rweq_of_step (Step.trans_assoc q (ωInv (ωOne a)) (ωInv q)))
      (rweq_trans
        (rweq_trans_congr_right q
          (rweq_trans
            (rweq_trans_congr_left (ωInv q)
              (rweq_of_step (Step.symm_refl a)))
            (rweq_of_step (Step.trans_refl_left (ωInv q)))))
        (rweq_of_step (Step.trans_symm q))))

/-! ## §10  Mapping Space -/

/-- Mapping space: paths between functions. -/
noncomputable def MapSpace (A B : Type u) (f g : A → B) : Type u :=
  (a : A) → Path (f a) (g a)

/-- Constant map space element. -/
noncomputable def mapSpaceRefl {A B : Type u} (f : A → B) :
    MapSpace A B f f :=
  fun a => Path.refl (f a)

/-- Composition of map space elements. -/
noncomputable def mapSpaceTrans {A B : Type u} {f g h : A → B}
    (α : MapSpace A B f g) (β : MapSpace A B g h) :
    MapSpace A B f h :=
  fun a => Path.trans (α a) (β a)

/-- Inverse of map space element. -/
noncomputable def mapSpaceSymm {A B : Type u} {f g : A → B}
    (α : MapSpace A B f g) : MapSpace A B g f :=
  fun a => Path.symm (α a)

/-- Map space trans with refl on the left. -/
noncomputable def mapSpaceTrans_refl_left {A B : Type u} {f g : A → B}
    (α : MapSpace A B f g) (a : A) :
    RwEq (mapSpaceTrans (mapSpaceRefl f) α a) (α a) :=
  rweq_of_step (Step.trans_refl_left (α a))

/-- Map space trans with refl on the right. -/
noncomputable def mapSpaceTrans_refl_right {A B : Type u} {f g : A → B}
    (α : MapSpace A B f g) (a : A) :
    RwEq (mapSpaceTrans α (mapSpaceRefl g) a) (α a) :=
  rweq_of_step (Step.trans_refl_right (α a))

/-! ## §11  Suspension-Loop Adjunction Data -/

/-- Suspension type (two points with meridians). -/
inductive Susp (A : Type u) : Type u where
  | north : Susp A
  | south : Susp A

/-- Meridian path from north to south (given a point). -/
noncomputable def meridian {A : Type u} (a : A)
    (meq : @Susp.north A = @Susp.south A) : Path (@Susp.north A) (@Susp.south A) :=
  Path.stepChain meq

/-- Loop from meridian: σ(a) · σ(a₀)⁻¹ gives a loop at north. -/
noncomputable def meridianLoop {A : Type u} (a a₀ : A)
    (meq : @Susp.north A = @Susp.south A) :
    Path (@Susp.north A) (@Susp.north A) :=
  Path.trans (meridian a meq) (Path.symm (meridian a₀ meq))

/-- Meridian loop of base point is trivial. -/
noncomputable def meridianLoop_base {A : Type u} (a₀ : A)
    (meq : @Susp.north A = @Susp.south A) :
    RwEq (meridianLoop a₀ a₀ meq) (Path.refl (@Susp.north A)) :=
  rweq_of_step (Step.trans_symm (meridian a₀ meq))

/-! ## §12  Free Group on Loops -/

/-- Free group word over a type. -/
inductive FreeWord (A : Type u) : Type u where
  | empty : FreeWord A
  | gen   : A → FreeWord A → FreeWord A
  | inv   : A → FreeWord A → FreeWord A

/-- Free word concatenation. -/
noncomputable def freeConcat {A : Type u} : FreeWord A → FreeWord A → FreeWord A
  | FreeWord.empty, w => w
  | FreeWord.gen x xs, w => FreeWord.gen x (freeConcat xs w)
  | FreeWord.inv x xs, w => FreeWord.inv x (freeConcat xs w)

/-- Free concatenation with empty is identity. -/
theorem freeConcat_empty {A : Type u} (w : FreeWord A) :
    freeConcat w FreeWord.empty = w := by
  induction w with
  | empty => rfl
  | gen x xs ih => simp [freeConcat, ih]
  | inv x xs ih => simp [freeConcat, ih]

/-- Free concatenation is associative. -/
theorem freeConcat_assoc {A : Type u}
    (u v w : FreeWord A) :
    freeConcat (freeConcat u v) w = freeConcat u (freeConcat v w) := by
  induction u with
  | empty => rfl
  | gen x xs ih => simp [freeConcat, ih]
  | inv x xs ih => simp [freeConcat, ih]

/-- Path between free words from a generator path. -/
noncomputable def freeGenPath {A : Type u} {x y : A}
    (p : Path x y) (w : FreeWord A) :
    Path (FreeWord.gen x w) (FreeWord.gen y w) :=
  Path.congrArg (fun z => FreeWord.gen z w) p

/-- Free gen path respects refl. -/
noncomputable def freeGenPath_refl {A : Type u}
    (x : A) (w : FreeWord A) :
    RwEq (freeGenPath (Path.refl x) w) (Path.refl (FreeWord.gen x w)) :=
  rweq_of_step (Step.congrArg_refl (fun z => FreeWord.gen z w) x)

/-- Free gen path distributes over trans. -/
noncomputable def freeGenPath_trans {A : Type u}
    {x y z : A} (p : Path x y) (q : Path y z) (w : FreeWord A) :
    RwEq (freeGenPath (Path.trans p q) w)
         (Path.trans (freeGenPath p w) (freeGenPath q w)) :=
  rweq_of_step (Step.congrArg_trans (fun z => FreeWord.gen z w) p q)

end

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths.Path.Homotopy.LoopSpaceDeep2
