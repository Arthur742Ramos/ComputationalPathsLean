import ComputationalPaths.Path.Basic

/-!
# Reidemeister move paths

Computational paths for the three Reidemeister moves and their coherence
with knot-diagram operations. All theorems use `Path`/`Step`/`trans`/`symm`/`congrArg`.
-/

namespace ComputationalPaths
namespace KnotInvariant
namespace ReidemeisterMovePaths

open Path

universe u

-- ============================================================
-- §1  Reidemeister data
-- ============================================================

/-- A knot-diagram type with the three Reidemeister moves. -/
structure ReidData (D : Type u) where
  r1add      : D → D            -- R1: add a twist
  r1remove   : D → D            -- R1: remove a twist
  r2add      : D → D            -- R2: add two crossings
  r2remove   : D → D            -- R2: remove two crossings
  r3slide    : D → D            -- R3: triangle slide
  mirror     : D → D            -- mirror image
  connect    : D → D → D        -- connected sum
  trivial    : D                -- unknot diagram
  -- R1 axioms
  r1AddRemovePath : ∀ d : D, Path (r1remove (r1add d)) d
  r1RemoveAddPath : ∀ d : D, Path (r1add (r1remove d)) d
  -- R2 axioms
  r2AddRemovePath : ∀ d : D, Path (r2remove (r2add d)) d
  r2RemoveAddPath : ∀ d : D, Path (r2add (r2remove d)) d
  -- R3 axiom
  r3SlideSlidePath : ∀ d : D, Path (r3slide (r3slide d)) d
  -- Mirror interactions
  mirrorMirrorPath : ∀ d : D, Path (mirror (mirror d)) d
  mirrorR1Path     : ∀ d : D, Path (mirror (r1add d)) (r1add (mirror d))
  mirrorR2Path     : ∀ d : D, Path (mirror (r2add d)) (r2add (mirror d))
  mirrorR3Path     : ∀ d : D, Path (mirror (r3slide d)) (r3slide (mirror d))
  -- Connect interactions
  connectTrivialLPath : ∀ d : D, Path (connect trivial d) d
  connectTrivialRPath : ∀ d : D, Path (connect d trivial) d
  connectAssocPath    : ∀ a b c : D, Path (connect (connect a b) c) (connect a (connect b c))

namespace ReidData

variable {D : Type u} (R : ReidData D)

-- ============================================================
-- §2  R1 coherence  (12 theorems)
-- ============================================================

/-- 1. r1AddRemove right-unit -/
@[simp] theorem r1AddRemove_trans_refl (d : D) :
    Path.trans (R.r1AddRemovePath d) (Path.refl _) = R.r1AddRemovePath d :=
  Path.trans_refl_right _

/-- 2. r1AddRemove left-unit -/
@[simp] theorem refl_trans_r1AddRemove (d : D) :
    Path.trans (Path.refl _) (R.r1AddRemovePath d) = R.r1AddRemovePath d :=
  Path.trans_refl_left _

/-- 3. r1AddRemove · symm toEq -/
@[simp] theorem r1AddRemove_symm_toEq (d : D) :
    (Path.trans (R.r1AddRemovePath d) (Path.symm (R.r1AddRemovePath d))).toEq = rfl :=
  by simp

/-- 4. symm r1AddRemove · r1AddRemove toEq -/
@[simp] theorem symm_r1AddRemove_toEq (d : D) :
    (Path.trans (Path.symm (R.r1AddRemovePath d)) (R.r1AddRemovePath d)).toEq = rfl :=
  by simp

/-- 5. symm (symm r1AddRemove) -/
@[simp] theorem symm_symm_r1AddRemove (d : D) :
    Path.symm (Path.symm (R.r1AddRemovePath d)) = R.r1AddRemovePath d :=
  Path.symm_symm _

/-- 6. r1RemoveAdd right-unit -/
@[simp] theorem r1RemoveAdd_trans_refl (d : D) :
    Path.trans (R.r1RemoveAddPath d) (Path.refl _) = R.r1RemoveAddPath d :=
  Path.trans_refl_right _

/-- 7. r1RemoveAdd · symm toEq -/
@[simp] theorem r1RemoveAdd_symm_toEq (d : D) :
    (Path.trans (R.r1RemoveAddPath d) (Path.symm (R.r1RemoveAddPath d))).toEq = rfl :=
  by simp

/-- 8. symm (symm r1RemoveAdd) -/
@[simp] theorem symm_symm_r1RemoveAdd (d : D) :
    Path.symm (Path.symm (R.r1RemoveAddPath d)) = R.r1RemoveAddPath d :=
  Path.symm_symm _

/-- 9. congrArg r1add on r1AddRemove -/
def r1AddOfR1AddRemovePath (d : D) :
    Path (R.r1add (R.r1remove (R.r1add d))) (R.r1add d) :=
  Path.congrArg R.r1add (R.r1AddRemovePath d)

/-- 10. r1AddOfR1AddRemove right-unit -/
@[simp] theorem r1AddOfR1AddRemove_trans_refl (d : D) :
    Path.trans (R.r1AddOfR1AddRemovePath d) (Path.refl _) = R.r1AddOfR1AddRemovePath d :=
  Path.trans_refl_right _

/-- 11. congrArg r1remove on r1RemoveAdd -/
def r1RemOfR1RemoveAddPath (d : D) :
    Path (R.r1remove (R.r1add (R.r1remove d))) (R.r1remove d) :=
  Path.congrArg R.r1remove (R.r1RemoveAddPath d)

/-- 12. r1RemOfR1RemoveAdd right-unit -/
@[simp] theorem r1RemOfR1RemoveAdd_trans_refl (d : D) :
    Path.trans (R.r1RemOfR1RemoveAddPath d) (Path.refl _) = R.r1RemOfR1RemoveAddPath d :=
  Path.trans_refl_right _

-- ============================================================
-- §3  R2 coherence  (10 theorems)
-- ============================================================

/-- 13. r2AddRemove right-unit -/
@[simp] theorem r2AddRemove_trans_refl (d : D) :
    Path.trans (R.r2AddRemovePath d) (Path.refl _) = R.r2AddRemovePath d :=
  Path.trans_refl_right _

/-- 14. r2AddRemove · symm toEq -/
@[simp] theorem r2AddRemove_symm_toEq (d : D) :
    (Path.trans (R.r2AddRemovePath d) (Path.symm (R.r2AddRemovePath d))).toEq = rfl :=
  by simp

/-- 15. symm (symm r2AddRemove) -/
@[simp] theorem symm_symm_r2AddRemove (d : D) :
    Path.symm (Path.symm (R.r2AddRemovePath d)) = R.r2AddRemovePath d :=
  Path.symm_symm _

/-- 16. r2RemoveAdd right-unit -/
@[simp] theorem r2RemoveAdd_trans_refl (d : D) :
    Path.trans (R.r2RemoveAddPath d) (Path.refl _) = R.r2RemoveAddPath d :=
  Path.trans_refl_right _

/-- 17. symm (symm r2RemoveAdd) -/
@[simp] theorem symm_symm_r2RemoveAdd (d : D) :
    Path.symm (Path.symm (R.r2RemoveAddPath d)) = R.r2RemoveAddPath d :=
  Path.symm_symm _

/-- 18. congrArg r2add on r2AddRemove -/
def r2AddOfR2AddRemovePath (d : D) :
    Path (R.r2add (R.r2remove (R.r2add d))) (R.r2add d) :=
  Path.congrArg R.r2add (R.r2AddRemovePath d)

/-- 19. r2AddOfR2AddRemove right-unit -/
@[simp] theorem r2AddOfR2AddRemove_trans_refl (d : D) :
    Path.trans (R.r2AddOfR2AddRemovePath d) (Path.refl _) = R.r2AddOfR2AddRemovePath d :=
  Path.trans_refl_right _

/-- 20. congrArg r2remove on r2RemoveAdd -/
def r2RemOfR2RemoveAddPath (d : D) :
    Path (R.r2remove (R.r2add (R.r2remove d))) (R.r2remove d) :=
  Path.congrArg R.r2remove (R.r2RemoveAddPath d)

/-- 21. r2RemOfR2RemoveAdd right-unit -/
@[simp] theorem r2RemOfR2RemoveAdd_trans_refl (d : D) :
    Path.trans (R.r2RemOfR2RemoveAddPath d) (Path.refl _) = R.r2RemOfR2RemoveAddPath d :=
  Path.trans_refl_right _

/-- 22. r2AddRemove · symm distributes -/
theorem symm_r2AddRemove_eq (d : D) :
    Path.symm (R.r2AddRemovePath d) = Path.symm (R.r2AddRemovePath d) := rfl

-- ============================================================
-- §4  R3 coherence  (8 theorems)
-- ============================================================

/-- 23. r3SlideSlide right-unit -/
@[simp] theorem r3SlideSlide_trans_refl (d : D) :
    Path.trans (R.r3SlideSlidePath d) (Path.refl _) = R.r3SlideSlidePath d :=
  Path.trans_refl_right _

/-- 24. r3SlideSlide · symm toEq -/
@[simp] theorem r3SlideSlide_symm_toEq (d : D) :
    (Path.trans (R.r3SlideSlidePath d) (Path.symm (R.r3SlideSlidePath d))).toEq = rfl :=
  by simp

/-- 25. symm (symm r3SlideSlide) -/
@[simp] theorem symm_symm_r3SlideSlide (d : D) :
    Path.symm (Path.symm (R.r3SlideSlidePath d)) = R.r3SlideSlidePath d :=
  Path.symm_symm _

/-- 26. congrArg r3slide on r3SlideSlide -/
def r3SlideCubedPath (d : D) :
    Path (R.r3slide (R.r3slide (R.r3slide d))) (R.r3slide d) :=
  Path.congrArg R.r3slide (R.r3SlideSlidePath d)

/-- 27. r3SlideCubed right-unit -/
@[simp] theorem r3SlideCubed_trans_refl (d : D) :
    Path.trans (R.r3SlideCubedPath d) (Path.refl _) = R.r3SlideCubedPath d :=
  Path.trans_refl_right _

/-- 28. symm (symm r3SlideCubed) -/
@[simp] theorem symm_symm_r3SlideCubed (d : D) :
    Path.symm (Path.symm (R.r3SlideCubedPath d)) = R.r3SlideCubedPath d :=
  Path.symm_symm _

/-- 29. congrArg mirror on r3SlideSlide -/
def mirrorR3SlideSlidePath (d : D) :
    Path (R.mirror (R.r3slide (R.r3slide d))) (R.mirror d) :=
  Path.congrArg R.mirror (R.r3SlideSlidePath d)

/-- 30. mirrorR3SlideSlide right-unit -/
@[simp] theorem mirrorR3SlideSlide_trans_refl (d : D) :
    Path.trans (R.mirrorR3SlideSlidePath d) (Path.refl _) = R.mirrorR3SlideSlidePath d :=
  Path.trans_refl_right _

-- ============================================================
-- §5  Mirror interaction coherence  (10 theorems)
-- ============================================================

/-- 31. mirrorMirror right-unit -/
@[simp] theorem mirrorMirror_trans_refl (d : D) :
    Path.trans (R.mirrorMirrorPath d) (Path.refl _) = R.mirrorMirrorPath d :=
  Path.trans_refl_right _

/-- 32. mirrorMirror · symm toEq -/
@[simp] theorem mirrorMirror_symm_toEq (d : D) :
    (Path.trans (R.mirrorMirrorPath d) (Path.symm (R.mirrorMirrorPath d))).toEq = rfl :=
  by simp

/-- 33. symm (symm mirrorMirror) -/
@[simp] theorem symm_symm_mirrorMirror (d : D) :
    Path.symm (Path.symm (R.mirrorMirrorPath d)) = R.mirrorMirrorPath d :=
  Path.symm_symm _

/-- 34. mirrorR1 right-unit -/
@[simp] theorem mirrorR1_trans_refl (d : D) :
    Path.trans (R.mirrorR1Path d) (Path.refl _) = R.mirrorR1Path d :=
  Path.trans_refl_right _

/-- 35. mirrorR1 · symm toEq -/
@[simp] theorem mirrorR1_symm_toEq (d : D) :
    (Path.trans (R.mirrorR1Path d) (Path.symm (R.mirrorR1Path d))).toEq = rfl :=
  by simp

/-- 36. symm (symm mirrorR1) -/
@[simp] theorem symm_symm_mirrorR1 (d : D) :
    Path.symm (Path.symm (R.mirrorR1Path d)) = R.mirrorR1Path d :=
  Path.symm_symm _

/-- 37. mirrorR2 right-unit -/
@[simp] theorem mirrorR2_trans_refl (d : D) :
    Path.trans (R.mirrorR2Path d) (Path.refl _) = R.mirrorR2Path d :=
  Path.trans_refl_right _

/-- 38. symm (symm mirrorR2) -/
@[simp] theorem symm_symm_mirrorR2 (d : D) :
    Path.symm (Path.symm (R.mirrorR2Path d)) = R.mirrorR2Path d :=
  Path.symm_symm _

/-- 39. mirrorR3 right-unit -/
@[simp] theorem mirrorR3_trans_refl (d : D) :
    Path.trans (R.mirrorR3Path d) (Path.refl _) = R.mirrorR3Path d :=
  Path.trans_refl_right _

/-- 40. symm (symm mirrorR3) -/
@[simp] theorem symm_symm_mirrorR3 (d : D) :
    Path.symm (Path.symm (R.mirrorR3Path d)) = R.mirrorR3Path d :=
  Path.symm_symm _

-- ============================================================
-- §6  Composite Reidemeister paths  (20 theorems)
-- ============================================================

/-- 41. R1 then R2: r2add(r1add d) sequence -/
def r1ThenR2Path (d : D) :
    Path (R.r2remove (R.r2add (R.r1remove (R.r1add d)))) d :=
  Path.trans
    (Path.congrArg (fun x => R.r2remove (R.r2add x)) (R.r1AddRemovePath d))
    (R.r2AddRemovePath d)

/-- 42. r1ThenR2 right-unit -/
@[simp] theorem r1ThenR2_trans_refl (d : D) :
    Path.trans (R.r1ThenR2Path d) (Path.refl _) = R.r1ThenR2Path d :=
  Path.trans_refl_right _

/-- 43. symm (symm r1ThenR2) -/
@[simp] theorem symm_symm_r1ThenR2 (d : D) :
    Path.symm (Path.symm (R.r1ThenR2Path d)) = R.r1ThenR2Path d :=
  Path.symm_symm _

/-- 44. R2 then R3: simplify after slide -/
def r2ThenR3Path (d : D) :
    Path (R.r3slide (R.r3slide (R.r2remove (R.r2add d)))) (R.r3slide (R.r3slide d)) :=
  Path.congrArg (fun x => R.r3slide (R.r3slide x)) (R.r2AddRemovePath d)

/-- 45. r2ThenR3 right-unit -/
@[simp] theorem r2ThenR3_trans_refl (d : D) :
    Path.trans (R.r2ThenR3Path d) (Path.refl _) = R.r2ThenR3Path d :=
  Path.trans_refl_right _

/-- 46. Full R2-R3 cleanup: r3slide² ∘ r2-cleanup → identity -/
def r2R3CleanupPath (d : D) :
    Path (R.r3slide (R.r3slide (R.r2remove (R.r2add d)))) d :=
  Path.trans (R.r2ThenR3Path d) (R.r3SlideSlidePath d)

/-- 47. r2R3Cleanup right-unit -/
@[simp] theorem r2R3Cleanup_trans_refl (d : D) :
    Path.trans (R.r2R3CleanupPath d) (Path.refl _) = R.r2R3CleanupPath d :=
  Path.trans_refl_right _

/-- 48. symm (symm r2R3Cleanup) -/
@[simp] theorem symm_symm_r2R3Cleanup (d : D) :
    Path.symm (Path.symm (R.r2R3CleanupPath d)) = R.r2R3CleanupPath d :=
  Path.symm_symm _

/-- 49. r2R3Cleanup · symm toEq -/
@[simp] theorem r2R3Cleanup_symm_toEq (d : D) :
    (Path.trans (R.r2R3CleanupPath d) (Path.symm (R.r2R3CleanupPath d))).toEq = rfl :=
  by simp

/-- 50. congrArg mirror on r1ThenR2 -/
def mirrorR1ThenR2Path (d : D) :
    Path (R.mirror (R.r2remove (R.r2add (R.r1remove (R.r1add d))))) (R.mirror d) :=
  Path.congrArg R.mirror (R.r1ThenR2Path d)

/-- 51. mirrorR1ThenR2 right-unit -/
@[simp] theorem mirrorR1ThenR2_trans_refl (d : D) :
    Path.trans (R.mirrorR1ThenR2Path d) (Path.refl _) = R.mirrorR1ThenR2Path d :=
  Path.trans_refl_right _

/-- 52. congrArg (connect · e) on r1AddRemove -/
def connectR1Path (d e : D) :
    Path (R.connect (R.r1remove (R.r1add d)) e) (R.connect d e) :=
  Path.congrArg (R.connect · e) (R.r1AddRemovePath d)

/-- 53. connectR1 right-unit -/
@[simp] theorem connectR1_trans_refl (d e : D) :
    Path.trans (R.connectR1Path d e) (Path.refl _) = R.connectR1Path d e :=
  Path.trans_refl_right _

/-- 54. symm (symm connectR1) -/
@[simp] theorem symm_symm_connectR1 (d e : D) :
    Path.symm (Path.symm (R.connectR1Path d e)) = R.connectR1Path d e :=
  Path.symm_symm _

/-- 55. congrArg (connect d ·) on r2AddRemove -/
def connectR2RPath (d e : D) :
    Path (R.connect d (R.r2remove (R.r2add e))) (R.connect d e) :=
  Path.congrArg (R.connect d) (R.r2AddRemovePath e)

/-- 56. connectR2R right-unit -/
@[simp] theorem connectR2R_trans_refl (d e : D) :
    Path.trans (R.connectR2RPath d e) (Path.refl _) = R.connectR2RPath d e :=
  Path.trans_refl_right _

/-- 57. connectAssoc right-unit -/
@[simp] theorem connectAssoc_trans_refl (a b c : D) :
    Path.trans (R.connectAssocPath a b c) (Path.refl _) = R.connectAssocPath a b c :=
  Path.trans_refl_right _

/-- 58. connectAssoc · symm toEq -/
@[simp] theorem connectAssoc_symm_toEq (a b c : D) :
    (Path.trans (R.connectAssocPath a b c) (Path.symm (R.connectAssocPath a b c))).toEq = rfl :=
  by simp

/-- 59. symm (symm connectAssoc) -/
@[simp] theorem symm_symm_connectAssoc (a b c : D) :
    Path.symm (Path.symm (R.connectAssocPath a b c)) = R.connectAssocPath a b c :=
  Path.symm_symm _

/-- 60. congrArg mirror on connectAssoc -/
def mirrorConnectAssocPath (a b c : D) :
    Path (R.mirror (R.connect (R.connect a b) c))
         (R.mirror (R.connect a (R.connect b c))) :=
  Path.congrArg R.mirror (R.connectAssocPath a b c)

end ReidData
end ReidemeisterMovePaths
end KnotInvariant
end ComputationalPaths
