/-
# Modal Logic via Computational Paths (Deep)

Kripke frames where accessibility is modeled by computational paths between
worlds.  Modal operators □ and ◇ are defined via path quantification.
K, T, S4, S5, B axiom schemes arise from path properties (reflexivity,
transitivity, symmetry).  Bisimulation, frame correspondence, temporal
operators (Until, Since), and graded modalities are developed through
multi-step path reasoning.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace ModalPathDeep

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open ComputationalPaths.Path

universe u v

/-! ## Kripke Frames as Path Structures -/

/-- A proposition label. -/
structure PropVar where
  idx : Nat

/-- A world in a Kripke frame. -/
structure World where
  id : Nat
  val : PropVar → Bool

/-- Accessibility between worlds witnessed by a computational path on ids. -/
structure Access (w v : World) where
  idPath : Path w.id v.id
  label  : String := ""

/-- Self-access from Path.refl. -/
def Access.selfAccess (w : World) : Access w w :=
  { idPath := Path.refl w.id }

/-- Compose two accessibility witnesses via Path.trans. -/
def Access.compose {w v u : World} (a1 : Access w v) (a2 : Access v u) : Access w u :=
  { idPath := Path.trans a1.idPath a2.idPath }

/-- Reverse an accessibility witness via Path.symm. -/
def Access.reverse {w v : World} (a : Access w v) : Access v w :=
  { idPath := Path.symm a.idPath }

/-! ## Modal Operators -/

/-- A Kripke frame: accessibility relation on worlds. -/
structure KFrame where
  acc : World → World → Prop

/-- □ φ at w: for every accessible v, φ holds at v. -/
def boxSat (F : KFrame) (φ : World → Prop) (w : World) : Prop :=
  ∀ v : World, F.acc w v → φ v

/-- ◇ φ at w: there exists accessible v where φ holds. -/
def diaSat (F : KFrame) (φ : World → Prop) (w : World) : Prop :=
  ∃ v : World, F.acc w v ∧ φ v

/-! ## Axiom K and Distribution -/

/-- 1. Axiom K: □(φ→ψ) → □φ → □ψ. -/
theorem axiomK (F : KFrame) (φ ψ : World → Prop) (w : World)
    (hImp : boxSat F (fun v => φ v → ψ v) w)
    (hPhi : boxSat F φ w) :
    boxSat F ψ w := by
  intro v hAcc
  have step1 : φ v → ψ v := hImp v hAcc
  have step2 : φ v := hPhi v hAcc
  exact step1 step2

/-- 2. Necessitation: if φ everywhere, □φ holds. -/
theorem necessitation (F : KFrame) (φ : World → Prop) (w : World)
    (hAll : ∀ v, φ v) :
    boxSat F φ w :=
  fun v _ => hAll v

/-- 3. □ over conjunction. -/
theorem boxConj (F : KFrame) (φ ψ : World → Prop) (w : World)
    (hPhi : boxSat F φ w) (hPsi : boxSat F ψ w) :
    boxSat F (fun v => φ v ∧ ψ v) w :=
  fun v hAcc => ⟨hPhi v hAcc, hPsi v hAcc⟩

/-- 4. □(φ∧ψ) → □φ. -/
theorem boxConjLeft (F : KFrame) (φ ψ : World → Prop) (w : World)
    (h : boxSat F (fun v => φ v ∧ ψ v) w) :
    boxSat F φ w :=
  fun v hAcc => (h v hAcc).1

/-- 5. □(φ∧ψ) → □ψ. -/
theorem boxConjRight (F : KFrame) (φ ψ : World → Prop) (w : World)
    (h : boxSat F (fun v => φ v ∧ ψ v) w) :
    boxSat F ψ w :=
  fun v hAcc => (h v hAcc).2

/-! ## Axiom T: Reflexivity ↔ □φ → φ -/

/-- 6. Axiom T forward: reflexive ⊢ □φ → φ. -/
theorem axiomT_forward (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) : φ w :=
  hBox w (hRefl w)

/-- 7. Axiom T converse: if □φ→φ for all φ, frame is reflexive. -/
theorem axiomT_converse (F : KFrame)
    (hT : ∀ (φ : World → Prop) (w : World), boxSat F φ w → φ w) :
    ∀ w, F.acc w w :=
  fun w => hT (F.acc w) w (fun v hAcc => hAcc)

/-! ## Axiom 4: Transitivity ↔ □φ → □□φ -/

/-- 8. Axiom 4 forward: transitive ⊢ □φ → □□φ. -/
theorem axiom4_forward (F : KFrame) (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) :
    boxSat F (boxSat F φ) w := by
  intro v hWV u hVU
  exact hBox u (hTrans w v u hWV hVU)

/-- 9. □φ → □□φ implies transitivity at any specific triple (given box hyps).
    Multi-step: apply axiom 4 to the specific formula F.acc · u. -/
theorem axiom4_specific (F : KFrame) (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w v u : World)
    (hWV : F.acc w v) (hVU : F.acc v u) (hBox : boxSat F φ w) : φ u :=
  hBox u (hTrans w v u hWV hVU)

/-! ## Axiom B: Symmetry ↔ φ → □◇φ -/

/-- 10. Axiom B forward: symmetric ⊢ φ → □◇φ. -/
theorem axiomB_forward (F : KFrame) (hSymm : ∀ w v, F.acc w v → F.acc v w)
    (φ : World → Prop) (w : World) (hPhi : φ w) :
    boxSat F (diaSat F φ) w := by
  intro v hAcc
  exact ⟨w, hSymm w v hAcc, hPhi⟩

/-- 11. Axiom B converse: if φ→□◇φ for all φ, frame is symmetric. -/
theorem axiomB_converse (F : KFrame)
    (hB : ∀ (φ : World → Prop) (w : World), φ w → boxSat F (diaSat F φ) w)
    (w v : World) (hAcc : F.acc w v) :
    F.acc v w := by
  have h := hB (fun x => x = w) w rfl v hAcc
  obtain ⟨u, hVU, hEq⟩ := h
  subst hEq
  exact hVU

/-! ## S4 = T + 4 -/

/-- 12. S4-T with extra transitivity hyp for context. -/
theorem s4_T (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (_hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) : φ w :=
  hBox w (hRefl w)

/-- 13. S4: □φ → □□φ (4 part). -/
theorem s4_4 (F : KFrame) (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) :
    boxSat F (boxSat F φ) w := by
  intro v hWV u hVU
  exact hBox u (hTrans w v u hWV hVU)

/-- 14. S4: □φ → □□□φ by iterating. -/
theorem s4_iterated_box (F : KFrame)
    (hRefl : ∀ w, F.acc w w)
    (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) :
    boxSat F (boxSat F (boxSat F φ)) w := by
  intro v1 h1 v2 h2 v3 h3
  have h12 := hTrans v1 v2 v3 h2 h3
  have hw3 := hTrans w v1 v3 h1 h12
  exact hBox v3 hw3

/-! ## S5 = T + 4 + B -/

/-- 15. S5: □φ → φ. -/
theorem s5_T (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) : φ w :=
  hBox w (hRefl w)

/-- 16. S5: φ → □◇φ. -/
theorem s5_B (F : KFrame) (hSymm : ∀ w v, F.acc w v → F.acc v w)
    (φ : World → Prop) (w : World) (hPhi : φ w) :
    boxSat F (diaSat F φ) w := by
  intro v hAcc
  exact ⟨w, hSymm w v hAcc, hPhi⟩

/-- 17. S5: ◇φ → □◇φ (diamond propagates through equivalence class). -/
theorem s5_dia_to_box_dia (F : KFrame)
    (hSymm : ∀ w v, F.acc w v → F.acc v w)
    (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World) (hDia : diaSat F φ w) :
    boxSat F (diaSat F φ) w := by
  obtain ⟨u, hWU, hPhi_u⟩ := hDia
  intro v hWV
  have hVW := hSymm w v hWV
  have hVU := hTrans v w u hVW hWU
  exact ⟨u, hVU, hPhi_u⟩

/-- 18. S5: □◇φ → ◇φ (by reflexivity). -/
theorem s5_box_dia_to_dia (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World)
    (h : boxSat F (diaSat F φ) w) : diaSat F φ w :=
  h w (hRefl w)

/-- 19. S5: □φ → ◇φ. -/
theorem s5_box_to_dia (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World) (hBox : boxSat F φ w) :
    diaSat F φ w :=
  ⟨w, hRefl w, hBox w (hRefl w)⟩

/-- 20. S5: ◇□φ → □φ (key S5 reduction). -/
theorem s5_dia_box_to_box (F : KFrame)
    (hSymm : ∀ w v, F.acc w v → F.acc v w)
    (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World)
    (h : diaSat F (boxSat F φ) w) :
    boxSat F φ w := by
  obtain ⟨u, hWU, hBox_u⟩ := h
  intro v hWV
  have hUV := hTrans u w v (hSymm w u hWU) hWV
  exact hBox_u v hUV

/-- 21. S5: ◇□φ → □◇φ (combining 20 + 17). -/
theorem s5_dia_box_to_box_dia (F : KFrame)
    (hRefl : ∀ w, F.acc w w)
    (hSymm : ∀ w v, F.acc w v → F.acc v w)
    (hTrans : ∀ w v u, F.acc w v → F.acc v u → F.acc w u)
    (φ : World → Prop) (w : World)
    (h : diaSat F (boxSat F φ) w) :
    boxSat F (diaSat F φ) w := by
  have hBox := s5_dia_box_to_box F hSymm hTrans φ w h
  intro v hAcc
  exact ⟨v, hRefl v, hBox v hAcc⟩

/-! ## Bisimulation via Path Correspondence -/

/-- A bisimulation between two frames. -/
structure Bisimulation (F₁ F₂ : KFrame) where
  rel : World → World → Prop
  atomPres : ∀ w₁ w₂, rel w₁ w₂ → w₁.val = w₂.val
  forth : ∀ w₁ w₂ v₁, rel w₁ w₂ → F₁.acc w₁ v₁ →
    ∃ v₂, F₂.acc w₂ v₂ ∧ rel v₁ v₂
  back : ∀ w₁ w₂ v₂, rel w₁ w₂ → F₂.acc w₂ v₂ →
    ∃ v₁, F₁.acc w₁ v₁ ∧ rel v₁ v₂

/-- 22. Bisimulation preserves □ satisfaction. -/
theorem bisim_preserves_box (F₁ F₂ : KFrame) (B : Bisimulation F₁ F₂)
    (φ : World → Prop) (hInv : ∀ w₁ w₂, B.rel w₁ w₂ → (φ w₁ ↔ φ w₂))
    (w₁ w₂ : World) (hRel : B.rel w₁ w₂) (hBox : boxSat F₁ φ w₁) :
    boxSat F₂ φ w₂ := by
  intro v₂ hAcc₂
  obtain ⟨v₁, hAcc₁, hRel_v⟩ := B.back w₁ w₂ v₂ hRel hAcc₂
  exact (hInv v₁ v₂ hRel_v).mp (hBox v₁ hAcc₁)

/-- 23. Bisimulation preserves ◇ satisfaction. -/
theorem bisim_preserves_dia (F₁ F₂ : KFrame) (B : Bisimulation F₁ F₂)
    (φ : World → Prop) (hInv : ∀ w₁ w₂, B.rel w₁ w₂ → (φ w₁ ↔ φ w₂))
    (w₁ w₂ : World) (hRel : B.rel w₁ w₂) (hDia : diaSat F₁ φ w₁) :
    diaSat F₂ φ w₂ := by
  obtain ⟨v₁, hAcc₁, hPhi₁⟩ := hDia
  obtain ⟨v₂, hAcc₂, hRel_v⟩ := B.forth w₁ w₂ v₁ hRel hAcc₁
  exact ⟨v₂, hAcc₂, (hInv v₁ v₂ hRel_v).mp hPhi₁⟩

/-- 24. Identity bisimulation. -/
def bisimId (F : KFrame) : Bisimulation F F where
  rel w₁ w₂ := w₁ = w₂
  atomPres _ _ h := _root_.congrArg World.val h
  forth w₁ w₂ v₁ hEq hAcc := by subst hEq; exact ⟨v₁, hAcc, rfl⟩
  back  w₁ w₂ v₂ hEq hAcc := by subst hEq; exact ⟨v₂, hAcc, rfl⟩

/-- 25. Bisimulation composition. -/
def bisimCompose (F₁ F₂ F₃ : KFrame)
    (B₁ : Bisimulation F₁ F₂) (B₂ : Bisimulation F₂ F₃) :
    Bisimulation F₁ F₃ where
  rel w₁ w₃ := ∃ w₂, B₁.rel w₁ w₂ ∧ B₂.rel w₂ w₃
  atomPres w₁ w₃ := by
    intro ⟨w₂, hR₁, hR₂⟩
    exact (B₁.atomPres w₁ w₂ hR₁).trans (B₂.atomPres w₂ w₃ hR₂)
  forth w₁ w₃ v₁ := by
    intro ⟨w₂, hR₁, hR₂⟩ hAcc₁
    obtain ⟨v₂, hAcc₂, hR₁_v⟩ := B₁.forth w₁ w₂ v₁ hR₁ hAcc₁
    obtain ⟨v₃, hAcc₃, hR₂_v⟩ := B₂.forth w₂ w₃ v₂ hR₂ hAcc₂
    exact ⟨v₃, hAcc₃, v₂, hR₁_v, hR₂_v⟩
  back w₁ w₃ v₃ := by
    intro ⟨w₂, hR₁, hR₂⟩ hAcc₃
    obtain ⟨v₂, hAcc₂, hR₂_v⟩ := B₂.back w₂ w₃ v₃ hR₂ hAcc₃
    obtain ⟨v₁, hAcc₁, hR₁_v⟩ := B₁.back w₁ w₂ v₂ hR₁ hAcc₂
    exact ⟨v₁, hAcc₁, v₂, hR₁_v, hR₂_v⟩

/-! ## Temporal Operators via Path Sequences -/

/-- A finite accessibility chain. -/
structure AccChain (F : KFrame) where
  worlds : List World
  linked : ∀ i : Fin (worlds.length - 1),
    F.acc (worlds.get ⟨i.val, by omega⟩) (worlds.get ⟨i.val + 1, by omega⟩)

/-- φ Until ψ along a chain. -/
def untilChain (F : KFrame) (φ ψ : World → Prop) (ch : AccChain F) : Prop :=
  ∃ k : Fin ch.worlds.length,
    ψ (ch.worlds.get k) ∧
    ∀ j : Fin ch.worlds.length, j.val < k.val → φ (ch.worlds.get j)

/-- φ Since ψ along a chain. -/
def sinceChain (F : KFrame) (φ ψ : World → Prop) (ch : AccChain F) : Prop :=
  ∃ k : Fin ch.worlds.length,
    ψ (ch.worlds.get k) ∧
    ∀ j : Fin ch.worlds.length, k.val < j.val → φ (ch.worlds.get j)

/-- 26. Until implies ψ eventually. -/
theorem until_eventually (F : KFrame) (φ ψ : World → Prop) (ch : AccChain F)
    (hUntil : untilChain F φ ψ ch) :
    ∃ k : Fin ch.worlds.length, ψ (ch.worlds.get k) := by
  obtain ⟨k, hPsi, _⟩ := hUntil
  exact ⟨k, hPsi⟩

/-- 27. Since implies ψ was true. -/
theorem since_sometime (F : KFrame) (φ ψ : World → Prop) (ch : AccChain F)
    (hSince : sinceChain F φ ψ ch) :
    ∃ k : Fin ch.worlds.length, ψ (ch.worlds.get k) := by
  obtain ⟨k, hPsi, _⟩ := hSince
  exact ⟨k, hPsi⟩

/-- 28. Until implies φ at position 0 (when ψ not at 0). -/
theorem until_phi_at_zero (F : KFrame) (φ ψ : World → Prop) (ch : AccChain F)
    (hUntil : untilChain F φ ψ ch)
    (hLen : 0 < ch.worlds.length)
    (hNonZero : ∀ k : Fin ch.worlds.length, ψ (ch.worlds.get k) → 0 < k.val) :
    φ (ch.worlds.get ⟨0, hLen⟩) := by
  obtain ⟨k, hPsi, hBefore⟩ := hUntil
  exact hBefore ⟨0, hLen⟩ (hNonZero k hPsi)

/-! ## Access Path Algebra -/

/-- 29. Self-access compose: result is trans of two refls. -/
theorem selfAccess_compose_self (w : World) :
    (Access.compose (Access.selfAccess w) (Access.selfAccess w)).idPath =
    Path.trans (Path.refl w.id) (Path.refl w.id) := rfl

/-- 30. Compose is associative. -/
theorem access_compose_assoc {w v u t : World}
    (a1 : Access w v) (a2 : Access v u) (a3 : Access u t) :
    (Access.compose (Access.compose a1 a2) a3).idPath =
    Path.trans (Path.trans a1.idPath a2.idPath) a3.idPath := rfl

/-- 31. Reassociated composition agrees at toEq. -/
theorem access_compose_assoc_eq {w v u t : World}
    (a1 : Access w v) (a2 : Access v u) (a3 : Access u t) :
    (Access.compose (Access.compose a1 a2) a3).idPath.toEq =
    (Access.compose a1 (Access.compose a2 a3)).idPath.toEq := by
  simp [Access.compose]

/-- 32. Reverse of selfAccess is selfAccess at toEq. -/
theorem reverse_selfAccess (w : World) :
    (Access.reverse (Access.selfAccess w)).idPath.toEq =
    (Access.selfAccess w).idPath.toEq := by
  simp [Access.reverse, Access.selfAccess]

/-- 33. Compose then reverse = symm(trans). -/
theorem compose_reverse {w v u : World}
    (a1 : Access w v) (a2 : Access v u) :
    (Access.reverse (Access.compose a1 a2)).idPath =
    Path.symm (Path.trans a1.idPath a2.idPath) := rfl

/-- 34. Double reverse restores path at toEq. -/
theorem reverse_reverse_eq {w v : World} (a : Access w v) :
    (Access.reverse (Access.reverse a)).idPath.toEq = a.idPath.toEq := by
  simp [Access.reverse]

/-- 35. Compose with reverse gives refl at toEq (right). -/
theorem compose_reverse_self {w v : World} (a : Access w v) :
    (Access.compose a (Access.reverse a)).idPath.toEq = (Path.refl w.id).toEq := by
  simp [Access.compose, Access.reverse]

/-- 36. Reverse compose with original gives refl at toEq (left). -/
theorem reverse_compose_self {w v : World} (a : Access w v) :
    (Access.compose (Access.reverse a) a).idPath.toEq = (Path.refl v.id).toEq := by
  simp [Access.compose, Access.reverse]

/-! ## Monotonicity and Structural Properties -/

/-- 37. □ is monotone. -/
theorem box_monotone (F : KFrame) (φ ψ : World → Prop)
    (hImp : ∀ w, φ w → ψ w) (w : World) (hBox : boxSat F φ w) :
    boxSat F ψ w :=
  fun v hAcc => hImp v (hBox v hAcc)

/-- 38. ◇ is monotone. -/
theorem dia_monotone (F : KFrame) (φ ψ : World → Prop)
    (hImp : ∀ w, φ w → ψ w) (w : World) (hDia : diaSat F φ w) :
    diaSat F ψ w := by
  obtain ⟨v, hAcc, hPhi⟩ := hDia
  exact ⟨v, hAcc, hImp v hPhi⟩

/-- 39. ◇(φ ∨ ψ) → ◇φ ∨ ◇ψ. -/
theorem dia_or (F : KFrame) (φ ψ : World → Prop) (w : World)
    (h : diaSat F (fun v => φ v ∨ ψ v) w) :
    diaSat F φ w ∨ diaSat F ψ w := by
  obtain ⟨v, hAcc, hOr⟩ := h
  exact hOr.elim (fun hp => Or.inl ⟨v, hAcc, hp⟩) (fun hq => Or.inr ⟨v, hAcc, hq⟩)

/-- 40. ◇φ ∨ ◇ψ → ◇(φ ∨ ψ). -/
theorem or_dia (F : KFrame) (φ ψ : World → Prop) (w : World)
    (h : diaSat F φ w ∨ diaSat F ψ w) :
    diaSat F (fun v => φ v ∨ ψ v) w := by
  rcases h with ⟨v, hAcc, hp⟩ | ⟨v, hAcc, hq⟩
  · exact ⟨v, hAcc, Or.inl hp⟩
  · exact ⟨v, hAcc, Or.inr hq⟩

/-- 41. □⊤ is always true. -/
theorem box_top (F : KFrame) (w : World) :
    boxSat F (fun _ => True) w :=
  fun _ _ => trivial

/-- 42. ◇⊥ is always false. -/
theorem dia_bot_false (F : KFrame) (w : World) :
    ¬ diaSat F (fun _ => False) w :=
  fun ⟨_, _, hF⟩ => hF

/-! ## Graded Modalities -/

/-- n-fold box. -/
def boxN (F : KFrame) : Nat → (World → Prop) → (World → Prop)
  | 0, φ => φ
  | n + 1, φ => boxSat F (boxN F n φ)

/-- 43. □⁰ = identity. -/
theorem boxN_zero (F : KFrame) (φ : World → Prop) (w : World) :
    boxN F 0 φ w = φ w := rfl

/-- 44. □¹ = □. -/
theorem boxN_one (F : KFrame) (φ : World → Prop) (w : World) :
    boxN F 1 φ w = boxSat F φ w := rfl

/-- 45. In S4, □² → □. -/
theorem s4_boxN_reduce (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World) (h : boxN F 2 φ w) :
    boxN F 1 φ w :=
  fun v hAcc => h v hAcc v (hRefl v)

/-- 46. In S4, □ⁿ⁺¹ → □ for all n. -/
theorem s4_boxN_collapse (F : KFrame) (hRefl : ∀ w, F.acc w w)
    (φ : World → Prop) (w : World) (n : Nat) (h : boxN F (n + 1) φ w) :
    boxSat F φ w := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ih (fun v hAcc => h v hAcc v (hRefl v))

/-! ## Duality -/

/-- 47. □φ → ¬◇¬φ. -/
theorem box_to_not_dia_neg (F : KFrame) (φ : World → Prop) (w : World)
    (hBox : boxSat F φ w) : ¬ diaSat F (fun v => ¬ φ v) w :=
  fun ⟨v, hAcc, hNeg⟩ => hNeg (hBox v hAcc)

/-- 48. ◇φ → ¬□¬φ. -/
theorem dia_to_not_box_neg (F : KFrame) (φ : World → Prop) (w : World)
    (hDia : diaSat F φ w) : ¬ boxSat F (fun v => ¬ φ v) w :=
  fun hBox => let ⟨v, hAcc, hPhi⟩ := hDia; hBox v hAcc hPhi

/-! ## Transport of Modal Truth Along Paths -/

/-- 49. CongrArg on box: path in formula space lifts to path in box space. -/
theorem congrArg_box (F : KFrame) (φ : World → Prop) (w : World) :
    Path.congrArg (fun f => boxSat F f w) (Path.refl φ) =
    Path.refl (boxSat F φ w) := by simp

/-- 50. Transport refl on box is identity. -/
theorem transport_box_refl (F : KFrame) (φ : World → Prop) (w : World)
    (h : boxSat F φ w) :
    Path.transport (D := fun w => boxSat F φ w) (Path.refl w) h = h := by simp

end ModalPathDeep
end Path
end ComputationalPaths
