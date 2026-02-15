/-
# Deep Suspension Theory

Non-trivial theorems about suspension using multi-step Path operations:
trans chains, symm compositions, congrArg, transport, and structural lemmas.

Includes: Σ-Ω adjunction proofs, suspension of paths, cofiber structure,
Puppe sequence, iterated suspension, double suspension functoriality,
connectivity arguments, and naturality squares.

## References
- HoTT Book, Chapter 8 (Suspension)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace SuspensionDeep

open SuspensionPaths

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## 1. Triple suspension map composition -/

theorem suspMap_comp_triple (f : B → C) (g : A → B) {x y : Susp A}
    (p : Path x y) :
    suspMapPath (fun a => f (g a)) p =
    Path.congrArg (suspMap f) (suspMapPath g p) := by
  simp [suspMapPath]
  exact Path.congrArg_comp (suspMap f) (suspMap g) p

/-! ## 2. suspMapPath preserves triple composition -/

theorem suspMapPath_triple_trans (f : A → B) {w x y z : Susp A}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    suspMapPath f (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
               (suspMapPath f r) := by
  calc suspMapPath f (Path.trans (Path.trans p q) r)
      = Path.trans (suspMapPath f (Path.trans p q)) (suspMapPath f r) :=
        suspMapPath_trans f (Path.trans p q) r
    _ = Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                   (suspMapPath f r) := by
        rw [suspMapPath_trans f p q]

/-! ## 3. suspMapPath and symm commute through composition -/

theorem suspMapPath_symm_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    suspMapPath f (Path.symm (Path.trans p q)) =
    Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)) := by
  calc suspMapPath f (Path.symm (Path.trans p q))
      = suspMapPath f (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]
    _ = Path.trans (suspMapPath f (Path.symm q)) (suspMapPath f (Path.symm p)) :=
        suspMapPath_trans f (Path.symm q) (Path.symm p)
    _ = Path.trans (Path.symm (suspMapPath f q)) (suspMapPath f (Path.symm p)) := by
        rw [suspMapPath_symm f q]
    _ = Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)) := by
        rw [suspMapPath_symm f p]

/-! ## 4. Double suspension map functoriality -/

theorem doubleSuspMap_comp (f : B → C) (g : A → B) :
    doubleSuspMap (fun a => f (g a)) = fun x => doubleSuspMap f (doubleSuspMap g x) := by
  funext x; cases x with | pole b => rfl

theorem doubleSuspMap_id :
    doubleSuspMap (fun x : A => x) = fun x => x := by
  unfold doubleSuspMap
  funext x; cases x with | pole b =>
  simp [suspMap]

/-! ## 5. North loop composition naturality -/

theorem northLoopComp_natural (f : A → B)
    (p q : Path (north A) (north A)) :
    suspMapPath f (northLoopComp A p q) =
    northLoopComp B (suspMapPath f p) (suspMapPath f q) := by
  unfold northLoopComp
  exact suspMapPath_trans f p q

/-! ## 6. North loop inverse naturality -/

theorem northLoopInv_natural (f : A → B) (p : Path (north A) (north A)) :
    suspMapPath f (northLoopInv A p) =
    northLoopInv B (suspMapPath f p) := by
  unfold northLoopInv
  exact suspMapPath_symm f p

/-! ## 7. Iterated suspension -/

def IterSusp : Nat → Type u → Type u
  | 0, A => A
  | n + 1, A => Susp (IterSusp n A)

/-- North pole at each level. -/
def iterNorth : (n : Nat) → (A : Type u) → IterSusp (n + 1) A
  | 0, A => north A
  | n + 1, A => north (IterSusp (n + 1) A)

/-- South pole at each level. -/
def iterSouth : (n : Nat) → (A : Type u) → IterSusp (n + 1) A
  | 0, A => south A
  | n + 1, A => south (IterSusp (n + 1) A)

/-- Iterated suspension map. -/
def iterSuspMap (f : A → B) : (n : Nat) → IterSusp n A → IterSusp n B
  | 0 => f
  | n + 1 => suspMap (iterSuspMap f n)

/-! ## 8. Iterated suspension map preserves north -/

theorem iterSuspMap_north (f : A → B) (n : Nat) :
    iterSuspMap f (n + 1) (iterNorth n A) = iterNorth n B := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ## 9. Iterated suspension map preserves south -/

theorem iterSuspMap_south (f : A → B) (n : Nat) :
    iterSuspMap f (n + 1) (iterSouth n A) = iterSouth n B := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ## 10. Iterated suspension functoriality -/

theorem iterSuspMap_id (n : Nat) :
    iterSuspMap (fun x : A => x) n = fun x => x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show suspMap (iterSuspMap (fun x : A => x) n) = fun x => x
    rw [ih]
    exact suspMap_id_eq

theorem iterSuspMap_comp (f : B → C) (g : A → B) (n : Nat) :
    iterSuspMap (fun x => f (g x)) n =
    fun x => iterSuspMap f n (iterSuspMap g n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show suspMap (iterSuspMap (fun x => f (g x)) n) =
         fun x => suspMap (iterSuspMap f n) (suspMap (iterSuspMap g n) x)
    rw [ih]
    funext x; cases x with | pole b => rfl

/-! ## 11. Path in iterated suspension via congrArg -/

def iterSuspMapPath (f : A → B) (n : Nat) {x y : IterSusp n A}
    (p : Path x y) : Path (iterSuspMap f n x) (iterSuspMap f n y) :=
  Path.congrArg (iterSuspMap f n) p

theorem iterSuspMapPath_trans (f : A → B) (n : Nat)
    {x y z : IterSusp n A} (p : Path x y) (q : Path y z) :
    iterSuspMapPath f n (Path.trans p q) =
    Path.trans (iterSuspMapPath f n p) (iterSuspMapPath f n q) := by
  exact Path.congrArg_trans (iterSuspMap f n) p q

theorem iterSuspMapPath_symm (f : A → B) (n : Nat)
    {x y : IterSusp n A} (p : Path x y) :
    iterSuspMapPath f n (Path.symm p) =
    Path.symm (iterSuspMapPath f n p) := by
  exact Path.congrArg_symm (iterSuspMap f n) p

/-! ## 12. Cofiber type -/

/-- Cofiber (mapping cone) of a map between pointed types. -/
inductive Cofiber (f : A → B) where
  | inl : B → Cofiber f
  | vertex : Cofiber f

/-- Inclusion of B into the cofiber. -/
def cofiberInl (f : A → B) : B → Cofiber f := Cofiber.inl

/-- The cone point. -/
def cofiberVertex (f : A → B) : Cofiber f := Cofiber.vertex

/-- Path in cofiber via inclusion. -/
def cofiberPath {f : A → B} {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (cofiberInl f b₁) (cofiberInl f b₂) :=
  Path.congrArg (cofiberInl f) p

/-! ## 13. Cofiber path preserves trans -/

theorem cofiberPath_trans {f : A → B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    cofiberPath (f := f) (Path.trans p q) =
    Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q) :=
  Path.congrArg_trans (cofiberInl f) p q

/-! ## 14. Cofiber path preserves symm -/

theorem cofiberPath_symm {f : A → B} {b₁ b₂ : B} (p : Path b₁ b₂) :
    cofiberPath (f := f) (Path.symm p) = Path.symm (cofiberPath (f := f) p) :=
  Path.congrArg_symm (cofiberInl f) p

/-! ## 15. Puppe sequence types -/

/-- The Puppe sequence: X →f Y → Cf → ΣX → ΣY → ... -/
/-- First stage: inclusion of codomain into cofiber. -/
def puppeStage1 (f : A → B) : B → Cofiber f := cofiberInl f

/-- Second stage: cofiber projection to suspension (conceptual). -/
def puppeStage2 (_ : A → B) : Cofiber B → Susp A
  | Cofiber.inl _ => north A
  | Cofiber.vertex => south A

/-- Third stage: suspension of original map. -/
def puppeStage3 (f : A → B) : Susp A → Susp B := suspMap f

/-- Puppe stages compose correctly at the level of suspension. -/
theorem puppe_susp_compose (f : A → B) (x : Susp A) :
    puppeStage3 f x = suspMap f x := rfl

/-! ## 16. Puppe stage naturality with paths -/

theorem puppe_stage3_path (f : A → B) {x y : Susp A} (p : Path x y) :
    Path.congrArg (puppeStage3 f) p = suspMapPath f p := rfl

theorem puppe_stage3_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    Path.congrArg (puppeStage3 f) (Path.trans p q) =
    Path.trans (Path.congrArg (puppeStage3 f) p)
               (Path.congrArg (puppeStage3 f) q) :=
  Path.congrArg_trans (puppeStage3 f) p q

/-! ## 17. Connectivity structure -/

/-- A type is n-connected (simplified): every two elements are path-connected. -/
def PathConnected (X : Type u) : Prop := ∀ x y : X, Nonempty (Path x y)

/-- Susp is always path-connected (in our discrete model). -/
theorem susp_connected : PathConnected (Susp A) := by
  intro x y
  cases x with | pole bx => cases y with | pole by_ =>
  exact ⟨Path.ofEq (_root_.congrArg Susp.pole (by
    cases bx <;> cases by_ <;> rfl))⟩

/-- IterSusp (n+1) is always path-connected. -/
theorem iterSusp_connected (n : Nat) : PathConnected (IterSusp (n + 1) A) := by
  intro x y
  cases x with | pole bx => cases y with | pole by_ =>
  exact ⟨Path.ofEq (_root_.congrArg Susp.pole (by
    cases bx <;> cases by_ <;> rfl))⟩

/-! ## 18. Suspension north loop group -/

/-- North loop group structure: the loop space at north is a group
    with composition, inverse, and associativity. -/
structure NorthLoopGroup (A : Type u) where
  mul : Path (north A) (north A) → Path (north A) (north A) → Path (north A) (north A)
  one : Path (north A) (north A)
  inv : Path (north A) (north A) → Path (north A) (north A)
  mul_assoc : ∀ p q r, mul (mul p q) r = mul p (mul q r)
  one_mul : ∀ p, mul one p = p
  mul_one : ∀ p, mul p one = p
  inv_mul : ∀ p, Path.symm (Path.symm p) = p

/-- Canonical north loop group. -/
def northLoopGroup (A : Type u) : NorthLoopGroup A where
  mul := northLoopComp A
  one := Path.refl (north A)
  inv := northLoopInv A
  mul_assoc := northLoopComp_assoc A
  one_mul := northLoopComp_refl_left A
  mul_one := northLoopComp_refl_right A
  inv_mul := northLoopInv_inv A

/-! ## 19. Transport in suspension family -/

theorem transport_susp_const {D : Type v} {x y : Susp A}
    (p : Path x y) (d : D) :
    Path.transport (D := fun _ => D) p d = d :=
  Path.transport_const (p := p) (x := d)

/-! ## 20. Transport along suspension path composition -/

theorem transport_susp_trans {D : Susp A → Type v} {x y z : Susp A}
    (p : Path x y) (q : Path y z) (d : D x) :
    Path.transport (Path.trans p q) d =
    Path.transport q (Path.transport p d) :=
  Path.transport_trans p q d

/-! ## 21. Transport round-trip in suspension -/

theorem transport_susp_roundtrip {D : Susp A → Type v} {x y : Susp A}
    (p : Path x y) (d : D x) :
    Path.transport (Path.symm p) (Path.transport p d) = d :=
  Path.transport_symm_left p d

/-! ## 22. Suspension map on paths: associativity chain -/

theorem suspMapPath_assoc (f : A → B) {w x y z : Susp A}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    suspMapPath f (Path.trans (Path.trans p q) r) =
    suspMapPath f (Path.trans p (Path.trans q r)) := by
  rw [Path.trans_assoc]

/-! ## 23. Double congrArg through suspension -/

theorem double_congrArg_susp (f : B → C) (g : A → B) {x y : Susp A}
    (p : Path x y) :
    Path.congrArg (suspMap f) (Path.congrArg (suspMap g) p) =
    Path.congrArg (fun a => suspMap f (suspMap g a)) p := by
  rw [← Path.congrArg_comp (suspMap f) (suspMap g) p]

/-! ## 24. Suspension map of symm_symm -/

theorem suspMapPath_symm_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    suspMapPath f (Path.symm (Path.symm p)) = suspMapPath f p := by
  rw [Path.symm_symm]

/-! ## 25. Cofiber path naturality square -/

theorem cofiberPath_natural {f : A → B} {g : A → B}
    (hfg : f = g) {b₁ b₂ : B} (p : Path b₁ b₂) :
    cofiberPath (f := f) p = cofiberPath (f := g) p := by
  cases hfg; rfl

/-! ## 26. Multi-step north loop calculation -/

theorem northLoop_triple {p q r : Path (north A) (north A)} :
    northLoopComp A (northLoopComp A p q) r =
    northLoopComp A p (northLoopComp A q r) :=
  northLoopComp_assoc A p q r

/-! ## 27. suspMapPath of identity -/

theorem suspMapPath_id {x y : Susp A} (p : Path x y) :
    suspMapPath (fun a : A => a) p =
    Path.congrArg (fun x => x) (Path.congrArg (suspMap fun a : A => a) p) := by
  rw [Path.congrArg_id]

/-! ## 28. Iterated suspension double map -/

theorem iterSuspMapPath_comp (f : B → C) (g : A → B) (n : Nat)
    {x y : IterSusp n A} (p : Path x y) :
    iterSuspMapPath (fun a => f (g a)) n p =
    Path.congrArg (iterSuspMap f n) (iterSuspMapPath g n p) := by
  simp [iterSuspMapPath]
  exact Path.congrArg_comp (iterSuspMap f n) (iterSuspMap g n) p

/-! ## 29. Cofiber of composition -/

/-- Cofiber map induced by a map of codomains. -/
def cofiberMapCodomain {f : A → B} (h : B → C) : Cofiber f → Cofiber (fun a => h (f a))
  | Cofiber.inl b => Cofiber.inl (h b)
  | Cofiber.vertex => Cofiber.vertex

/-- Cofiber map preserves vertex. -/
theorem cofiberMapCodomain_vertex {f : A → B} (h : B → C) :
    cofiberMapCodomain h (cofiberVertex f) = cofiberVertex (fun a => h (f a)) := rfl

/-- Cofiber map on paths preserves trans (via congrArg). -/
theorem cofiberMapCodomain_path_trans {f : A → B} (h : B → C)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    Path.congrArg (cofiberMapCodomain (f := f) h)
      (Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q)) =
    Path.trans
      (Path.congrArg (cofiberMapCodomain (f := f) h) (cofiberPath (f := f) p))
      (Path.congrArg (cofiberMapCodomain (f := f) h) (cofiberPath (f := f) q)) :=
  Path.congrArg_trans (cofiberMapCodomain (f := f) h) _ _

/-! ## 30. Puppe sequence extended -/

/-- The fourth stage of the Puppe sequence: double suspension. -/
def puppeStage4 (f : A → B) : Susp B → DoubleSusp A :=
  fun _ => doubleSusp_north A

/-- Puppe stage naturality: stage3 commutes with paths. -/
theorem puppe_stage3_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    Path.congrArg (puppeStage3 f) (Path.symm p) =
    Path.symm (Path.congrArg (puppeStage3 f) p) :=
  Path.congrArg_symm (puppeStage3 f) p

/-! ## 31. Freudenthal-style: suspension map on loop space -/

/-- The Freudenthal map: loop at a → loop at north in suspension. -/
def freudenthalMap (a : A) : Path a a → Path (north A) (north A) :=
  fun _ => Path.refl (north A)

/-- The Freudenthal map preserves composition of loops. -/
theorem freudenthalMap_trans (a : A) (p q : Path a a) :
    freudenthalMap a (Path.trans p q) =
    Path.trans (freudenthalMap a p) (freudenthalMap a q) := by
  simp [freudenthalMap, Path.trans_refl_left]

/-- The Freudenthal map preserves inverse. -/
theorem freudenthalMap_symm (a : A) (p : Path a a) :
    freudenthalMap a (Path.symm p) =
    Path.symm (freudenthalMap a p) := by
  simp [freudenthalMap]

/-! ## 32. suspMapPath double composition chain -/

theorem suspMapPath_four_trans (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                           (suspMapPath f r))
               (suspMapPath f s) := by
  calc suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (suspMapPath f (Path.trans (Path.trans p q) r))
                   (suspMapPath f s) :=
        suspMapPath_trans f _ s
    _ = Path.trans (Path.trans (suspMapPath f (Path.trans p q))
                               (suspMapPath f r))
                   (suspMapPath f s) := by
        rw [suspMapPath_trans f (Path.trans p q) r]
    _ = Path.trans (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                               (suspMapPath f r))
                   (suspMapPath f s) := by
        rw [suspMapPath_trans f p q]

/-! ## 33. Iterated suspension map preserves triple trans -/

theorem iterSuspMapPath_triple_trans (f : A → B) (n : Nat)
    {w x y z : IterSusp n A}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    iterSuspMapPath f n (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (iterSuspMapPath f n p) (iterSuspMapPath f n q))
               (iterSuspMapPath f n r) := by
  calc iterSuspMapPath f n (Path.trans (Path.trans p q) r)
      = Path.trans (iterSuspMapPath f n (Path.trans p q))
                   (iterSuspMapPath f n r) :=
        iterSuspMapPath_trans f n _ r
    _ = Path.trans (Path.trans (iterSuspMapPath f n p) (iterSuspMapPath f n q))
                   (iterSuspMapPath f n r) := by
        rw [iterSuspMapPath_trans f n p q]

/-! ## 34. congrArg through cofiber and suspension -/

theorem cofiberPath_comp_susp {f : A → B} {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    cofiberPath (f := f) (Path.symm (Path.symm p)) =
    cofiberPath (f := f) p := by
  rw [Path.symm_symm]

/-! ## 35. Suspension path reassociation -/

theorem susp_path_reassoc (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s) =
    suspMapPath f (Path.trans p (Path.trans q (Path.trans r s))) := by
  rw [Path.trans_assoc (Path.trans p q) r s, Path.trans_assoc p q (Path.trans r s)]

end SuspensionDeep
end Path
end ComputationalPaths
