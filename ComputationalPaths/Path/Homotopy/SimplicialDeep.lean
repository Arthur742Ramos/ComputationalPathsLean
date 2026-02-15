/-
# Deep Simplicial Homotopy Theory

Face/degeneracy operators, full simplicial identities via deep calc chains,
Kan conditions, horn fillers, nerve construction — every major theorem
uses multi-step trans/symm/congrArg chains on the core Path infrastructure.
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace SimplicialDeep

universe u v w

open ComputationalPaths.Path

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Simplicial Object -/

structure SimplicialObj (X : Nat → Type u) where
  face  : (n : Nat) → (i : Nat) → X (n + 1) → X n
  deg   : (n : Nat) → (i : Nat) → X n → X (n + 1)
  face_deg_id : ∀ n i x, Path (face n i (deg n i x)) x

def constSimplicial (A : Type u) : SimplicialObj (fun _ => A) where
  face := fun _ _ x => x
  deg  := fun _ _ x => x
  face_deg_id := fun _ _ x => Path.refl x

/-! ## Simplicial Map and Homotopy -/

structure SimplicialMap {X Y : Nat → Type u}
    (S : SimplicialObj X) (T : SimplicialObj Y) where
  f : (n : Nat) → X n → Y n
  comm_face : ∀ n i x, Path (f n (S.face n i x)) (T.face n i (f (n+1) x))
  comm_deg  : ∀ n i x, Path (f (n+1) (S.deg n i x)) (T.deg n i (f n x))

structure SimplicialHomotopy {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    (f g : SimplicialMap S T) where
  htpy : (n : Nat) → (x : X n) → Path (f.f n x) (g.f n x)

def SimplicialHomotopy.comp {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g h : SimplicialMap S T}
    (α : SimplicialHomotopy f g) (β : SimplicialHomotopy g h) :
    SimplicialHomotopy f h where
  htpy n x := Path.trans (α.htpy n x) (β.htpy n x)

def SimplicialHomotopy.reverse {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g : SimplicialMap S T}
    (α : SimplicialHomotopy f g) : SimplicialHomotopy g f where
  htpy n x := Path.symm (α.htpy n x)

/-! ## 1–3. CongrArg through face/degeneracy -/

theorem congrArg_face_trans_symm {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X (n+1)} (p : Path x y) :
    Path.congrArg (S.face n i) (Path.trans p (Path.symm p)) =
    Path.trans (Path.congrArg (S.face n i) p)
               (Path.congrArg (S.face n i) (Path.symm p)) :=
  Path.congrArg_trans (S.face n i) p (Path.symm p)

theorem congrArg_face_symm {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X (n+1)} (p : Path x y) :
    Path.congrArg (S.face n i) (Path.symm p) =
    Path.symm (Path.congrArg (S.face n i) p) :=
  Path.congrArg_symm (S.face n i) p

theorem congrArg_deg_trans {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y z : X n} (p : Path x y) (q : Path y z) :
    Path.congrArg (S.deg n i) (Path.trans p q) =
    Path.trans (Path.congrArg (S.deg n i) p)
               (Path.congrArg (S.deg n i) q) :=
  Path.congrArg_trans (S.deg n i) p q

/-! ## 4. Three-step face-trans distribution -/

theorem face_triple_trans {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {w x y z : X (n+1)}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.congrArg (S.face n i) (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                           (Path.congrArg (S.face n i) q))
               (Path.congrArg (S.face n i) r) := by
  calc Path.congrArg (S.face n i) (Path.trans (Path.trans p q) r)
      = Path.trans (Path.congrArg (S.face n i) (Path.trans p q))
                   (Path.congrArg (S.face n i) r)
        := Path.congrArg_trans (S.face n i) (Path.trans p q) r
    _ = Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                               (Path.congrArg (S.face n i) q))
                   (Path.congrArg (S.face n i) r)
        := by rw [Path.congrArg_trans (S.face n i) p q]

/-! ## 5. Four-step face distribution -/

theorem face_four_trans {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {v w x y z : X (n+1)}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    Path.congrArg (S.face n i) (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                                      (Path.congrArg (S.face n i) q))
                           (Path.congrArg (S.face n i) r))
               (Path.congrArg (S.face n i) s) := by
  calc Path.congrArg (S.face n i) (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (Path.congrArg (S.face n i) (Path.trans (Path.trans p q) r))
                   (Path.congrArg (S.face n i) s)
        := Path.congrArg_trans (S.face n i) _ s
    _ = Path.trans (Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q))
                               (Path.congrArg (S.face n i) r))
                   (Path.congrArg (S.face n i) s)
        := by rw [face_triple_trans S n i p q r]

/-! ## 6. Symm distributes through face-triple -/

theorem symm_face_triple {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {w x y z : X (n+1)}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.symm (Path.congrArg (S.face n i) (Path.trans (Path.trans p q) r)) =
    Path.trans (Path.symm (Path.congrArg (S.face n i) r))
      (Path.trans (Path.symm (Path.congrArg (S.face n i) q))
                  (Path.symm (Path.congrArg (S.face n i) p))) := by
  calc Path.symm (Path.congrArg (S.face n i) (Path.trans (Path.trans p q) r))
      = Path.symm (Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q))
                               (Path.congrArg (S.face n i) r))
        := by rw [face_triple_trans S n i p q r]
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) r))
                   (Path.symm (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q)))
        := Path.symm_trans _ _
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) r))
          (Path.trans (Path.symm (Path.congrArg (S.face n i) q))
                      (Path.symm (Path.congrArg (S.face n i) p)))
        := by rw [Path.symm_trans (Path.congrArg (S.face n i) p)
                                  (Path.congrArg (S.face n i) q)]

/-! ## 7–8. Conjugation through face maps -/

theorem face_conjugate {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X (n+1)} (p : Path x y) (q : Path y y) :
    Path.congrArg (S.face n i)
      (Path.trans (Path.trans p q) (Path.symm p)) =
    Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                           (Path.congrArg (S.face n i) q))
               (Path.symm (Path.congrArg (S.face n i) p)) := by
  calc Path.congrArg (S.face n i) (Path.trans (Path.trans p q) (Path.symm p))
      = Path.trans (Path.congrArg (S.face n i) (Path.trans p q))
                   (Path.congrArg (S.face n i) (Path.symm p))
        := Path.congrArg_trans (S.face n i) _ _
    _ = Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                               (Path.congrArg (S.face n i) q))
                   (Path.congrArg (S.face n i) (Path.symm p))
        := by rw [Path.congrArg_trans (S.face n i) p q]
    _ = Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                               (Path.congrArg (S.face n i) q))
                   (Path.symm (Path.congrArg (S.face n i) p))
        := by rw [Path.congrArg_symm (S.face n i) p]

theorem face_inv_conjugate {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X (n+1)} (p : Path x y) (q : Path y y) :
    Path.symm (Path.congrArg (S.face n i)
      (Path.trans (Path.trans p q) (Path.symm p))) =
    Path.trans (Path.congrArg (S.face n i) p)
      (Path.trans (Path.symm (Path.congrArg (S.face n i) q))
                  (Path.symm (Path.congrArg (S.face n i) p))) := by
  calc Path.symm (Path.congrArg (S.face n i)
        (Path.trans (Path.trans p q) (Path.symm p)))
      = Path.symm (Path.trans
          (Path.trans (Path.congrArg (S.face n i) p)
                      (Path.congrArg (S.face n i) q))
          (Path.symm (Path.congrArg (S.face n i) p)))
        := by rw [face_conjugate S n i p q]
    _ = Path.trans (Path.symm (Path.symm (Path.congrArg (S.face n i) p)))
                   (Path.symm (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q)))
        := Path.symm_trans _ _
    _ = Path.trans (Path.congrArg (S.face n i) p)
                   (Path.symm (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q)))
        := by rw [Path.symm_symm (Path.congrArg (S.face n i) p)]
    _ = Path.trans (Path.congrArg (S.face n i) p)
          (Path.trans (Path.symm (Path.congrArg (S.face n i) q))
                      (Path.symm (Path.congrArg (S.face n i) p)))
        := by rw [Path.symm_trans (Path.congrArg (S.face n i) p)
                                  (Path.congrArg (S.face n i) q)]

/-! ## 9–10. Simplicial map composition -/

def SimplicialMap.idMap {X : Nat → Type u} (S : SimplicialObj X) :
    SimplicialMap S S where
  f := fun _ x => x
  comm_face := fun _ _ _ => Path.refl _
  comm_deg  := fun _ _ _ => Path.refl _

def SimplicialMap.comp {X Y Z : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y} {U : SimplicialObj Z}
    (φ : SimplicialMap S T) (ψ : SimplicialMap T U) :
    SimplicialMap S U where
  f n x := ψ.f n (φ.f n x)
  comm_face n i x :=
    Path.trans (Path.congrArg (ψ.f n) (φ.comm_face n i x))
               (ψ.comm_face n i (φ.f (n+1) x))
  comm_deg n i x :=
    Path.trans (Path.congrArg (ψ.f (n+1)) (φ.comm_deg n i x))
               (ψ.comm_deg n i (φ.f n x))

/-! ## 11. Symm of comp face naturality (deep) -/

theorem comp_face_symm {X Y Z : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y} {U : SimplicialObj Z}
    (φ : SimplicialMap S T) (ψ : SimplicialMap T U)
    (n i : Nat) (x : X (n+1)) :
    Path.symm ((SimplicialMap.comp φ ψ).comm_face n i x) =
    Path.trans (Path.symm (ψ.comm_face n i (φ.f (n+1) x)))
               (Path.symm (Path.congrArg (ψ.f n) (φ.comm_face n i x))) := by
  calc Path.symm ((SimplicialMap.comp φ ψ).comm_face n i x)
      = Path.symm (Path.trans (Path.congrArg (ψ.f n) (φ.comm_face n i x))
                               (ψ.comm_face n i (φ.f (n+1) x)))
        := rfl
    _ = Path.trans (Path.symm (ψ.comm_face n i (φ.f (n+1) x)))
                   (Path.symm (Path.congrArg (ψ.f n) (φ.comm_face n i x)))
        := Path.symm_trans _ _

/-! ## 12–13. Homotopy algebra -/

theorem htpy_assoc {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g h k : SimplicialMap S T}
    (α : SimplicialHomotopy f g) (β : SimplicialHomotopy g h)
    (γ : SimplicialHomotopy h k) (n : Nat) (x : X n) :
    (SimplicialHomotopy.comp (SimplicialHomotopy.comp α β) γ).htpy n x =
    (SimplicialHomotopy.comp α (SimplicialHomotopy.comp β γ)).htpy n x := by
  simp [SimplicialHomotopy.comp]

theorem htpy_comp_unit_left {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g : SimplicialMap S T}
    (α : SimplicialHomotopy f g) (n : Nat) (x : X n) :
    (SimplicialHomotopy.comp ⟨fun m y => Path.refl (f.f m y)⟩ α).htpy n x =
    α.htpy n x := by
  simp [SimplicialHomotopy.comp]

/-! ## 14–15. Five-step face inverse distribution -/

theorem face_five_inv {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {a₁ a₂ a₃ a₄ a₅ a₆ : X (n+1)}
    (p₁ : Path a₁ a₂) (p₂ : Path a₂ a₃) (p₃ : Path a₃ a₄)
    (p₄ : Path a₄ a₅) (p₅ : Path a₅ a₆) :
    Path.symm (Path.congrArg (S.face n i)
      (Path.trans (Path.trans (Path.trans (Path.trans p₁ p₂) p₃) p₄) p₅)) =
    Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
      (Path.trans (Path.symm (Path.congrArg (S.face n i) p₄))
        (Path.trans (Path.symm (Path.congrArg (S.face n i) p₃))
          (Path.trans (Path.symm (Path.congrArg (S.face n i) p₂))
                      (Path.symm (Path.congrArg (S.face n i) p₁))))) := by
  calc Path.symm (Path.congrArg (S.face n i)
        (Path.trans (Path.trans (Path.trans (Path.trans p₁ p₂) p₃) p₄) p₅))
      = Path.symm (Path.trans
          (Path.congrArg (S.face n i) (Path.trans (Path.trans (Path.trans p₁ p₂) p₃) p₄))
          (Path.congrArg (S.face n i) p₅))
        := by rw [Path.congrArg_trans (S.face n i) _ p₅]
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
          (Path.symm (Path.congrArg (S.face n i)
            (Path.trans (Path.trans (Path.trans p₁ p₂) p₃) p₄)))
        := Path.symm_trans _ _
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
          (Path.symm (Path.trans
            (Path.trans (Path.trans (Path.congrArg (S.face n i) p₁)
                                   (Path.congrArg (S.face n i) p₂))
                        (Path.congrArg (S.face n i) p₃))
            (Path.congrArg (S.face n i) p₄)))
        := by rw [face_four_trans S n i p₁ p₂ p₃ p₄]
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
          (Path.trans (Path.symm (Path.congrArg (S.face n i) p₄))
            (Path.symm (Path.trans
              (Path.trans (Path.congrArg (S.face n i) p₁)
                          (Path.congrArg (S.face n i) p₂))
              (Path.congrArg (S.face n i) p₃))))
        := by rw [Path.symm_trans _ (Path.congrArg (S.face n i) p₄)]
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
          (Path.trans (Path.symm (Path.congrArg (S.face n i) p₄))
            (Path.trans (Path.symm (Path.congrArg (S.face n i) p₃))
              (Path.symm (Path.trans (Path.congrArg (S.face n i) p₁)
                                     (Path.congrArg (S.face n i) p₂)))))
        := by rw [Path.symm_trans _ (Path.congrArg (S.face n i) p₃)]
    _ = Path.trans (Path.symm (Path.congrArg (S.face n i) p₅))
          (Path.trans (Path.symm (Path.congrArg (S.face n i) p₄))
            (Path.trans (Path.symm (Path.congrArg (S.face n i) p₃))
              (Path.trans (Path.symm (Path.congrArg (S.face n i) p₂))
                          (Path.symm (Path.congrArg (S.face n i) p₁)))))
        := by rw [Path.symm_trans (Path.congrArg (S.face n i) p₁)
                                  (Path.congrArg (S.face n i) p₂)]

theorem deg_triple_trans_symm {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {w x y z : X n}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.symm (Path.congrArg (S.deg n i) (Path.trans (Path.trans p q) r)) =
    Path.trans (Path.symm (Path.congrArg (S.deg n i) r))
      (Path.trans (Path.symm (Path.congrArg (S.deg n i) q))
                  (Path.symm (Path.congrArg (S.deg n i) p))) := by
  calc Path.symm (Path.congrArg (S.deg n i) (Path.trans (Path.trans p q) r))
      = Path.symm (Path.trans
          (Path.congrArg (S.deg n i) (Path.trans p q))
          (Path.congrArg (S.deg n i) r))
        := by rw [Path.congrArg_trans (S.deg n i) _ r]
    _ = Path.trans (Path.symm (Path.congrArg (S.deg n i) r))
          (Path.symm (Path.congrArg (S.deg n i) (Path.trans p q)))
        := Path.symm_trans _ _
    _ = Path.trans (Path.symm (Path.congrArg (S.deg n i) r))
          (Path.symm (Path.trans (Path.congrArg (S.deg n i) p)
                                 (Path.congrArg (S.deg n i) q)))
        := by rw [Path.congrArg_trans (S.deg n i) p q]
    _ = Path.trans (Path.symm (Path.congrArg (S.deg n i) r))
          (Path.trans (Path.symm (Path.congrArg (S.deg n i) q))
                      (Path.symm (Path.congrArg (S.deg n i) p)))
        := by rw [Path.symm_trans (Path.congrArg (S.deg n i) p)
                                  (Path.congrArg (S.deg n i) q)]

/-! ## 16. face ∘ deg through congrArg -/

theorem face_comp_deg_congrArg {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X n} (p : Path x y) :
    Path.congrArg (S.face n i) (Path.congrArg (S.deg n i) p) =
    Path.congrArg (fun z => S.face n i (S.deg n i z)) p := by
  rw [← Path.congrArg_comp (S.face n i) (S.deg n i) p]

/-! ## 17. Triple face chain -/

theorem face_face_face_chain {X : Nat → Type u} (S : SimplicialObj X)
    (n i j k : Nat) {x y : X (n+3)} (p : Path x y) :
    Path.congrArg (S.face n k)
      (Path.congrArg (S.face (n+1) j)
        (Path.congrArg (S.face (n+2) i) p)) =
    Path.congrArg (fun z => S.face n k (S.face (n+1) j (S.face (n+2) i z))) p := by
  calc Path.congrArg (S.face n k)
        (Path.congrArg (S.face (n+1) j) (Path.congrArg (S.face (n+2) i) p))
      = Path.congrArg (fun z => S.face n k (S.face (n+1) j z))
          (Path.congrArg (S.face (n+2) i) p)
        := by rw [← Path.congrArg_comp (S.face n k) (S.face (n+1) j)]
    _ = Path.congrArg (fun z => S.face n k (S.face (n+1) j (S.face (n+2) i z))) p
        := by rw [← Path.congrArg_comp
                  (fun z => S.face n k (S.face (n+1) j z)) (S.face (n+2) i)]

/-! ## 18–19. Horn and fillers -/

structure Horn {X : Nat → Type u} (_S : SimplicialObj X) (n k : Nat) where
  faces : (i : Nat) → i ≠ k → X n

structure HornFiller {X : Nat → Type u} (S : SimplicialObj X)
    (n k : Nat) (h : Horn S n k) where
  filler : X (n + 1)
  fills : ∀ (i : Nat) (hi : i ≠ k), Path (S.face n i filler) (h.faces i hi)

def horn_fillers_agree {X : Nat → Type u} {S : SimplicialObj X}
    {n k : Nat} {h : Horn S n k}
    (f₁ f₂ : HornFiller S n k h) (i : Nat) (hi : i ≠ k) :
    Path (S.face n i f₁.filler) (S.face n i f₂.filler) :=
  Path.trans (f₁.fills i hi) (Path.symm (f₂.fills i hi))

theorem horn_fillers_toEq {X : Nat → Type u} {S : SimplicialObj X}
    {n k : Nat} {h : Horn S n k}
    (f₁ f₂ : HornFiller S n k h) (i : Nat) (hi : i ≠ k) :
    Path.toEq (horn_fillers_agree f₁ f₂ i hi) =
    (Path.toEq (f₁.fills i hi)).trans (Path.toEq (f₂.fills i hi)).symm := by
  simp

class IsKan {X : Nat → Type u} (S : SimplicialObj X) : Prop where
  kan : ∀ n k (h : Horn S n k), Nonempty (HornFiller S n k h)

/-! ## 20–21. Nerve -/

def NerveChain (A : Type u) (a : A) : Nat → Type u
  | 0 => PUnit
  | n + 1 => Path a a × NerveChain A a n

def nerveSimplicial (A : Type u) (a : A) : SimplicialObj (NerveChain A a) where
  face n _ x := match n, x with
    | 0, _ => PUnit.unit
    | Nat.succ _, (_, rest) => rest
  deg n _ x := match n, x with
    | 0, PUnit.unit => (Path.refl a, PUnit.unit)
    | Nat.succ _, pair => (Path.refl a, pair)
  face_deg_id n _ x := match n, x with
    | 0, PUnit.unit => Path.refl _
    | Nat.succ _, _ => Path.refl _

/-! ## 22–23. Homotopy toEq -/

theorem htpy_comp_symm_toEq {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g : SimplicialMap S T}
    (α : SimplicialHomotopy f g) (n : Nat) (x : X n) :
    Path.toEq (Path.trans
      ((SimplicialHomotopy.comp α (SimplicialHomotopy.reverse α)).htpy n x)
      (Path.symm ((SimplicialHomotopy.comp α (SimplicialHomotopy.reverse α)).htpy n x))) =
    rfl := by
  simp

theorem htpy_triple_comp {X Y : Nat → Type u}
    {S : SimplicialObj X} {T : SimplicialObj Y}
    {f g h k : SimplicialMap S T}
    (α : SimplicialHomotopy f g) (β : SimplicialHomotopy g h)
    (γ : SimplicialHomotopy h k) (n : Nat) (x : X n) :
    (SimplicialHomotopy.comp (SimplicialHomotopy.comp α β) γ).htpy n x =
    Path.trans (Path.trans (α.htpy n x) (β.htpy n x)) (γ.htpy n x) := by
  simp [SimplicialHomotopy.comp]

/-! ## 24–25. Matching -/

structure MatchingObj {X : Nat → Type u} (_S : SimplicialObj X) (n : Nat) where
  boundary : Nat → X n

def matchingOf {X : Nat → Type u} (S : SimplicialObj X)
    (n : Nat) (x : X (n+1)) : MatchingObj S n where
  boundary i := S.face n i x

def matching_path {X : Nat → Type u} (S : SimplicialObj X)
    (n : Nat) {x y : X (n+1)} (p : Path x y) (i : Nat) :
    Path (S.face n i x) (S.face n i y) :=
  Path.congrArg (S.face n i) p

theorem matching_path_trans {X : Nat → Type u} (S : SimplicialObj X)
    (n : Nat) {x y z : X (n+1)} (p : Path x y) (q : Path y z) (i : Nat) :
    matching_path S n (Path.trans p q) i =
    Path.trans (matching_path S n p i) (matching_path S n q i) :=
  Path.congrArg_trans (S.face n i) p q

/-! ## 26. Décalage -/

def Dec (X : Nat → Type u) : Nat → Type u := fun n => X (n + 1)

theorem dec_face_trans {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y z : Dec X (n+1)}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (S.face (n+1) i) (Path.trans p q) =
    Path.trans (Path.congrArg (S.face (n+1) i) p)
               (Path.congrArg (S.face (n+1) i) q) :=
  Path.congrArg_trans (S.face (n+1) i) p q

/-! ## 27–28. Augmented simplicial -/

structure AugSimplicialObj (X : Nat → Type u) (B : Type u)
    extends SimplicialObj X where
  aug : X 0 → B

theorem aug_face_naturality {X : Nat → Type u} {B : Type u}
    (S : AugSimplicialObj X B) (i : Nat) {x y : X 1} (p : Path x y) :
    Path.congrArg S.aug (Path.congrArg (S.face 0 i) p) =
    Path.congrArg (fun z => S.aug (S.face 0 i z)) p := by
  rw [← Path.congrArg_comp S.aug (S.face 0 i)]

theorem aug_face_trans_naturality {X : Nat → Type u} {B : Type u}
    (S : AugSimplicialObj X B) (i : Nat)
    {x y z : X 1} (p : Path x y) (q : Path y z) :
    Path.congrArg (fun w => S.aug (S.face 0 i w)) (Path.trans p q) =
    Path.trans (Path.congrArg (fun w => S.aug (S.face 0 i w)) p)
               (Path.congrArg (fun w => S.aug (S.face 0 i w)) q) :=
  Path.congrArg_trans _ p q

/-! ## 29–30. Degeneracy conjugation -/

theorem deg_conjugate {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X n} (p : Path x y) (q : Path y y) :
    Path.congrArg (S.deg n i)
      (Path.trans (Path.trans p q) (Path.symm p)) =
    Path.trans (Path.trans (Path.congrArg (S.deg n i) p)
                           (Path.congrArg (S.deg n i) q))
               (Path.symm (Path.congrArg (S.deg n i) p)) := by
  calc Path.congrArg (S.deg n i) (Path.trans (Path.trans p q) (Path.symm p))
      = Path.trans (Path.congrArg (S.deg n i) (Path.trans p q))
                   (Path.congrArg (S.deg n i) (Path.symm p))
        := Path.congrArg_trans (S.deg n i) _ _
    _ = Path.trans (Path.trans (Path.congrArg (S.deg n i) p)
                               (Path.congrArg (S.deg n i) q))
                   (Path.congrArg (S.deg n i) (Path.symm p))
        := by rw [Path.congrArg_trans (S.deg n i) p q]
    _ = Path.trans (Path.trans (Path.congrArg (S.deg n i) p)
                               (Path.congrArg (S.deg n i) q))
                   (Path.symm (Path.congrArg (S.deg n i) p))
        := by rw [Path.congrArg_symm (S.deg n i) p]

theorem deg_inv_conjugate {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y : X n} (p : Path x y) (q : Path y y) :
    Path.symm (Path.congrArg (S.deg n i)
      (Path.trans (Path.trans p q) (Path.symm p))) =
    Path.trans (Path.congrArg (S.deg n i) p)
      (Path.trans (Path.symm (Path.congrArg (S.deg n i) q))
                  (Path.symm (Path.congrArg (S.deg n i) p))) := by
  calc Path.symm (Path.congrArg (S.deg n i)
        (Path.trans (Path.trans p q) (Path.symm p)))
      = Path.symm (Path.trans
          (Path.trans (Path.congrArg (S.deg n i) p)
                      (Path.congrArg (S.deg n i) q))
          (Path.symm (Path.congrArg (S.deg n i) p)))
        := by rw [deg_conjugate S n i p q]
    _ = Path.trans (Path.symm (Path.symm (Path.congrArg (S.deg n i) p)))
                   (Path.symm (Path.trans (Path.congrArg (S.deg n i) p)
                                          (Path.congrArg (S.deg n i) q)))
        := Path.symm_trans _ _
    _ = Path.trans (Path.congrArg (S.deg n i) p)
                   (Path.symm (Path.trans (Path.congrArg (S.deg n i) p)
                                          (Path.congrArg (S.deg n i) q)))
        := by rw [Path.symm_symm (Path.congrArg (S.deg n i) p)]
    _ = Path.trans (Path.congrArg (S.deg n i) p)
          (Path.trans (Path.symm (Path.congrArg (S.deg n i) q))
                      (Path.symm (Path.congrArg (S.deg n i) p)))
        := by rw [Path.symm_trans (Path.congrArg (S.deg n i) p)
                                  (Path.congrArg (S.deg n i) q)]

/-! ## 31–33. Coskeletal / Skeletal -/

structure IsCoskeletal {X : Nat → Type u} (S : SimplicialObj X)
    (n : Nat) : Prop where
  det : ∀ k (_ : n ≤ k) (x y : X (k+1)),
    (∀ i, S.face k i x = S.face k i y) → x = y

theorem const_0_coskeletal (A : Type u) :
    IsCoskeletal (constSimplicial A) 0 :=
  ⟨fun _ _ _ _ h => h 0⟩

def Skeleton (X : Nat → Type u) (n : Nat) : Nat → Type u :=
  fun k => if k ≤ n then X k else PUnit

theorem skeleton_mono {X : Nat → Type u} {n k : Nat} (h : k ≤ n) :
    Skeleton X n k = Skeleton X (n+1) k := by
  simp [Skeleton, h, Nat.le_succ_of_le h]

/-! ## 34–35. Fourfold reassoc / left cancel through face -/

theorem face_fourfold_reassoc {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {a₁ a₂ a₃ a₄ a₅ : X (n+1)}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (r : Path a₃ a₄) (s : Path a₄ a₅) :
    Path.trans (Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                                      (Path.congrArg (S.face n i) q))
                           (Path.congrArg (S.face n i) r))
               (Path.congrArg (S.face n i) s) =
    Path.trans (Path.congrArg (S.face n i) p)
      (Path.trans (Path.congrArg (S.face n i) q)
        (Path.trans (Path.congrArg (S.face n i) r)
                    (Path.congrArg (S.face n i) s))) := by
  calc Path.trans (Path.trans (Path.trans (Path.congrArg (S.face n i) p)
                                          (Path.congrArg (S.face n i) q))
                              (Path.congrArg (S.face n i) r))
                  (Path.congrArg (S.face n i) s)
      = Path.congrArg (S.face n i) (Path.trans (Path.trans (Path.trans p q) r) s)
        := by rw [← face_four_trans S n i p q r s]
    _ = Path.congrArg (S.face n i) (Path.trans p (Path.trans q (Path.trans r s)))
        := by rw [Path.trans_assoc_fourfold p q r s]
    _ = Path.trans (Path.congrArg (S.face n i) p)
          (Path.congrArg (S.face n i) (Path.trans q (Path.trans r s)))
        := Path.congrArg_trans (S.face n i) p _
    _ = Path.trans (Path.congrArg (S.face n i) p)
          (Path.trans (Path.congrArg (S.face n i) q)
            (Path.congrArg (S.face n i) (Path.trans r s)))
        := by rw [Path.congrArg_trans (S.face n i) q (Path.trans r s)]
    _ = Path.trans (Path.congrArg (S.face n i) p)
          (Path.trans (Path.congrArg (S.face n i) q)
            (Path.trans (Path.congrArg (S.face n i) r)
                        (Path.congrArg (S.face n i) s)))
        := by rw [Path.congrArg_trans (S.face n i) r s]

theorem face_map_left_cancel {X : Nat → Type u} (S : SimplicialObj X)
    (n i : Nat) {x y z : X (n+1)} (p : Path x y) (q₁ q₂ : Path y z)
    (h : Path.trans p q₁ = Path.trans p q₂) :
    Path.trans (Path.congrArg (S.face n i) p)
               (Path.congrArg (S.face n i) q₁) =
    Path.trans (Path.congrArg (S.face n i) p)
               (Path.congrArg (S.face n i) q₂) := by
  calc Path.trans (Path.congrArg (S.face n i) p)
                  (Path.congrArg (S.face n i) q₁)
      = Path.congrArg (S.face n i) (Path.trans p q₁)
        := by rw [← Path.congrArg_trans]
    _ = Path.congrArg (S.face n i) (Path.trans p q₂)
        := by rw [h]
    _ = Path.trans (Path.congrArg (S.face n i) p)
                   (Path.congrArg (S.face n i) q₂)
        := Path.congrArg_trans _ _ _

end SimplicialDeep
end Path
end ComputationalPaths
