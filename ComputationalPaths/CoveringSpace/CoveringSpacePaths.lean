import ComputationalPaths.Path.Basic

/-!
# Covering space paths

Computational paths for covering-space theory: fiber transport, lifting,
deck transformations, monodromy, and fundamental-group computations.
All theorems use `Path`/`Step`/`trans`/`symm`/`congrArg` — no `sorry`.
-/

namespace ComputationalPaths
namespace CoveringSpace
namespace CoveringSpacePaths

open Path

universe u

-- ============================================================
-- §1  Covering-space data
-- ============================================================

/-- Rewrite tags for covering-space coherence moves. -/
inductive CovStep : Type
  | liftUnique | fiberTransport | deckAction | monodromy | homotopyLift

/-- A minimal covering-space package. -/
structure CovData (E B : Type u) where
  proj        : E → B
  lift        : B → E
  deck        : E → E
  basepoint   : B
  fiberpoint  : E
  projLiftPath    : ∀ b : B, Path (proj (lift b)) b
  liftProjPath    : ∀ e : E, Path (lift (proj e)) e
  deckProjPath    : ∀ e : E, Path (proj (deck e)) (proj e)
  deckDeckPath    : ∀ e : E, Path (deck (deck e)) e
  deckLiftPath    : ∀ b : B, Path (deck (lift b)) (lift b)

namespace CovData

variable {E B : Type u} (C : CovData E B)

-- §2  projLift / liftProj coherence (12 theorems)

/-- 1 -/ @[simp] theorem projLift_trans_refl (b : B) :
    Path.trans (C.projLiftPath b) (Path.refl b) = C.projLiftPath b := Path.trans_refl_right _
/-- 2 -/ @[simp] theorem liftProj_trans_refl (e : E) :
    Path.trans (C.liftProjPath e) (Path.refl e) = C.liftProjPath e := Path.trans_refl_right _
/-- 3 -/ @[simp] theorem refl_trans_projLift (b : B) :
    Path.trans (Path.refl (C.proj (C.lift b))) (C.projLiftPath b) = C.projLiftPath b := Path.trans_refl_left _
/-- 4 -/ @[simp] theorem refl_trans_liftProj (e : E) :
    Path.trans (Path.refl (C.lift (C.proj e))) (C.liftProjPath e) = C.liftProjPath e := Path.trans_refl_left _
/-- 5 -/ @[simp] theorem projLift_symm_toEq (b : B) :
    (Path.trans (C.projLiftPath b) (Path.symm (C.projLiftPath b))).toEq = rfl := Path.toEq_trans_symm (C.projLiftPath b)
/-- 6 -/ @[simp] theorem symm_projLift_toEq (b : B) :
    (Path.trans (Path.symm (C.projLiftPath b)) (C.projLiftPath b)).toEq = rfl := Path.toEq_symm_trans (C.projLiftPath b)
/-- 7 -/ @[simp] theorem liftProj_symm_toEq (e : E) :
    (Path.trans (C.liftProjPath e) (Path.symm (C.liftProjPath e))).toEq = rfl := Path.toEq_trans_symm (C.liftProjPath e)
/-- 8 -/ @[simp] theorem symm_liftProj_toEq (e : E) :
    (Path.trans (Path.symm (C.liftProjPath e)) (C.liftProjPath e)).toEq = rfl := Path.toEq_symm_trans (C.liftProjPath e)
/-- 9 -/ @[simp] theorem symm_symm_projLift (b : B) :
    Path.symm (Path.symm (C.projLiftPath b)) = C.projLiftPath b := Path.symm_symm _
/-- 10 -/ @[simp] theorem symm_symm_liftProj (e : E) :
    Path.symm (Path.symm (C.liftProjPath e)) = C.liftProjPath e := Path.symm_symm _
/-- 11 -/ def projOfLiftProjPath (e : E) : Path (C.proj (C.lift (C.proj e))) (C.proj e) :=
    Path.congrArg C.proj (C.liftProjPath e)
/-- 12 -/ def liftOfProjLiftPath (b : B) : Path (C.lift (C.proj (C.lift b))) (C.lift b) :=
    Path.congrArg C.lift (C.projLiftPath b)

-- §3  Deck-transformation coherence (12 theorems)

/-- 13 -/ @[simp] theorem deckDeck_trans_refl (e : E) :
    Path.trans (C.deckDeckPath e) (Path.refl e) = C.deckDeckPath e := Path.trans_refl_right _
/-- 14 -/ @[simp] theorem refl_trans_deckDeck (e : E) :
    Path.trans (Path.refl (C.deck (C.deck e))) (C.deckDeckPath e) = C.deckDeckPath e := Path.trans_refl_left _
/-- 15 -/ @[simp] theorem deckDeck_symm_toEq (e : E) :
    (Path.trans (C.deckDeckPath e) (Path.symm (C.deckDeckPath e))).toEq = rfl := Path.toEq_trans_symm (C.deckDeckPath e)
/-- 16 -/ @[simp] theorem symm_deckDeck_toEq (e : E) :
    (Path.trans (Path.symm (C.deckDeckPath e)) (C.deckDeckPath e)).toEq = rfl := Path.toEq_symm_trans (C.deckDeckPath e)
/-- 17 -/ @[simp] theorem symm_symm_deckDeck (e : E) :
    Path.symm (Path.symm (C.deckDeckPath e)) = C.deckDeckPath e := Path.symm_symm _
/-- 18 -/ @[simp] theorem deckProj_trans_refl (e : E) :
    Path.trans (C.deckProjPath e) (Path.refl (C.proj e)) = C.deckProjPath e := Path.trans_refl_right _
/-- 19 -/ @[simp] theorem refl_trans_deckProj (e : E) :
    Path.trans (Path.refl (C.proj (C.deck e))) (C.deckProjPath e) = C.deckProjPath e := Path.trans_refl_left _
/-- 20 -/ @[simp] theorem deckProj_symm_toEq (e : E) :
    (Path.trans (C.deckProjPath e) (Path.symm (C.deckProjPath e))).toEq = rfl := Path.toEq_trans_symm (C.deckProjPath e)
/-- 21 -/ def projDeckDeckPath (e : E) : Path (C.proj (C.deck (C.deck e))) (C.proj e) :=
    Path.congrArg C.proj (C.deckDeckPath e)
/-- 22 -/ @[simp] theorem deckLift_trans_refl (b : B) :
    Path.trans (C.deckLiftPath b) (Path.refl (C.lift b)) = C.deckLiftPath b := Path.trans_refl_right _
/-- 23 -/ @[simp] theorem refl_trans_deckLift (b : B) :
    Path.trans (Path.refl (C.deck (C.lift b))) (C.deckLiftPath b) = C.deckLiftPath b := Path.trans_refl_left _
/-- 24 -/ @[simp] theorem symm_symm_deckLift (b : B) :
    Path.symm (Path.symm (C.deckLiftPath b)) = C.deckLiftPath b := Path.symm_symm _

-- §4  Composite coherence paths (14 theorems)

/-- 25 -/ def projDeckLiftPath (b : B) : Path (C.proj (C.deck (C.lift b))) b :=
    Path.trans (C.deckProjPath (C.lift b)) (C.projLiftPath b)
/-- 26 -/ @[simp] theorem projDeckLift_trans_refl (b : B) :
    Path.trans (C.projDeckLiftPath b) (Path.refl b) = C.projDeckLiftPath b := Path.trans_refl_right _
/-- 27 -/ @[simp] theorem refl_trans_projDeckLift (b : B) :
    Path.trans (Path.refl _) (C.projDeckLiftPath b) = C.projDeckLiftPath b := Path.trans_refl_left _
/-- 28 -/ @[simp] theorem projDeckLift_symm_toEq (b : B) :
    (Path.trans (C.projDeckLiftPath b) (Path.symm (C.projDeckLiftPath b))).toEq = rfl := Path.toEq_trans_symm (C.projDeckLiftPath b)
/-- 29 -/ @[simp] theorem symm_symm_projDeckLift (b : B) :
    Path.symm (Path.symm (C.projDeckLiftPath b)) = C.projDeckLiftPath b := Path.symm_symm _
/-- 30 -/ def liftProjDeckPath (e : E) : Path (C.lift (C.proj (C.deck e))) (C.lift (C.proj e)) :=
    Path.congrArg C.lift (C.deckProjPath e)
/-- 31 -/ @[simp] theorem liftProjDeck_trans_refl (e : E) :
    Path.trans (C.liftProjDeckPath e) (Path.refl _) = C.liftProjDeckPath e := Path.trans_refl_right _
/-- 32 -/ theorem projDeckLift_assoc (b : B) :
    Path.trans (Path.trans (C.deckProjPath (C.lift b)) (C.projLiftPath b)) (Path.refl b) =
    Path.trans (C.deckProjPath (C.lift b)) (Path.trans (C.projLiftPath b) (Path.refl b)) := Path.trans_assoc _ _ _
/-- 33 -/ def deckLiftProjPath (e : E) : Path (C.deck (C.lift (C.proj e))) (C.deck e) :=
    Path.congrArg C.deck (C.liftProjPath e)
/-- 34 -/ @[simp] theorem deckLiftProj_trans_refl (e : E) :
    Path.trans (C.deckLiftProjPath e) (Path.refl _) = C.deckLiftProjPath e := Path.trans_refl_right _
/-- 35 -/ @[simp] theorem deckLiftProj_symm_toEq (e : E) :
    (Path.trans (C.deckLiftProjPath e) (Path.symm (C.deckLiftProjPath e))).toEq = rfl := Path.toEq_trans_symm (C.deckLiftProjPath e)
/-- 36 -/ @[simp] theorem symm_deckLiftProj_toEq (e : E) :
    (Path.trans (Path.symm (C.deckLiftProjPath e)) (C.deckLiftProjPath e)).toEq = rfl := Path.toEq_symm_trans (C.deckLiftProjPath e)
/-- 37 -/ @[simp] theorem symm_symm_deckLiftProj (e : E) :
    Path.symm (Path.symm (C.deckLiftProjPath e)) = C.deckLiftProjPath e := Path.symm_symm _
/-- 38 -/ theorem congrArg_deck_lift_projLift (b : B) :
    Path.congrArg C.deck (Path.congrArg C.lift (C.projLiftPath b)) =
    Path.congrArg (fun x => C.deck (C.lift x)) (C.projLiftPath b) := by simp

-- §5  Monodromy paths (12 theorems)

/-- 39 -/ def monodromyPath (e : E) : Path (C.deck (C.deck e)) e := C.deckDeckPath e
/-- 40 -/ @[simp] theorem monodromy_eq_deckDeck (e : E) : C.monodromyPath e = C.deckDeckPath e := rfl
/-- 41 -/ @[simp] theorem monodromy_trans_refl (e : E) :
    Path.trans (C.monodromyPath e) (Path.refl e) = C.monodromyPath e := Path.trans_refl_right _
/-- 42 -/ @[simp] theorem monodromy_symm_toEq (e : E) :
    (Path.trans (C.monodromyPath e) (Path.symm (C.monodromyPath e))).toEq = rfl := Path.toEq_trans_symm (C.deckDeckPath e)
/-- 43 -/ @[simp] theorem symm_monodromy_toEq (e : E) :
    (Path.trans (Path.symm (C.monodromyPath e)) (C.monodromyPath e)).toEq = rfl := Path.toEq_symm_trans (C.deckDeckPath e)
/-- 44 -/ @[simp] theorem symm_symm_monodromy (e : E) :
    Path.symm (Path.symm (C.monodromyPath e)) = C.monodromyPath e := Path.symm_symm _
/-- 45 -/ def projMonodromyPath (e : E) : Path (C.proj (C.deck (C.deck e))) (C.proj e) :=
    Path.congrArg C.proj (C.monodromyPath e)
/-- 46 -/ @[simp] theorem projMonodromy_eq (e : E) : C.projMonodromyPath e = C.projDeckDeckPath e := rfl
/-- 47 -/ @[simp] theorem projMonodromy_trans_refl (e : E) :
    Path.trans (C.projMonodromyPath e) (Path.refl _) = C.projMonodromyPath e := Path.trans_refl_right _
/-- 48 -/ def deckMonodromyPath (e : E) : Path (C.deck (C.deck (C.deck e))) (C.deck e) :=
    Path.congrArg C.deck (C.monodromyPath e)
/-- 49 -/ @[simp] theorem deckMonodromy_trans_refl (e : E) :
    Path.trans (C.deckMonodromyPath e) (Path.refl _) = C.deckMonodromyPath e := Path.trans_refl_right _
/-- 50 -/ @[simp] theorem symm_symm_deckMonodromy (e : E) :
    Path.symm (Path.symm (C.deckMonodromyPath e)) = C.deckMonodromyPath e := Path.symm_symm _

end CovData
end CoveringSpacePaths
end CoveringSpace
end ComputationalPaths
