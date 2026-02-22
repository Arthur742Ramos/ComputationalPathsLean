import ComputationalPaths.Path.Basic

/-!
# Knot invariant paths

Computational paths for knot invariants: Jones polynomial, writhe,
crossing number, bracket polynomial, and their coherence under
isotopy. All theorems use `Path`/`Step`/`trans`/`symm`/`congrArg` — no `sorry`.
-/

namespace ComputationalPaths
namespace KnotInvariant
namespace KnotInvariantPaths

open Path

universe u

-- ============================================================
-- §1  Knot-invariant data
-- ============================================================

/-- Rewrite tags for knot-invariant coherence moves. -/
inductive KnotStep : Type
  | jonesNorm | writheChange | bracketSkein | crossingSign | mirrorDual

/-- Minimal knot-invariant package:
    `K` is the type of knot diagrams,
    `Inv` is the type of invariant values. -/
structure KnotInvData (K Inv : Type u) where
  jones       : K → Inv          -- Jones polynomial evaluation
  writhe      : K → Inv          -- writhe (sum of crossing signs)
  bracket     : K → Inv          -- Kauffman bracket
  crossNum    : K → Inv          -- crossing number
  mirror      : K → K            -- mirror image
  connect     : K → K → K        -- connected sum
  trivial     : K                -- unknot
  invMul      : Inv → Inv → Inv  -- multiplication on invariants
  invUnit     : Inv              -- unit invariant
  invNeg      : Inv → Inv        -- negation / dual
  -- Axiom paths
  jonesMirrorPath   : ∀ k : K, Path (jones (mirror k)) (invNeg (jones k))
  jonesConnectPath  : ∀ k₁ k₂ : K, Path (jones (connect k₁ k₂)) (invMul (jones k₁) (jones k₂))
  jonesTrivialPath  : Path (jones trivial) invUnit
  writheConnectPath : ∀ k₁ k₂ : K, Path (writhe (connect k₁ k₂)) (invMul (writhe k₁) (writhe k₂))
  writheMirrorPath  : ∀ k : K, Path (writhe (mirror k)) (invNeg (writhe k))
  bracketConnectPath: ∀ k₁ k₂ : K, Path (bracket (connect k₁ k₂)) (invMul (bracket k₁) (bracket k₂))
  bracketTrivialPath: Path (bracket trivial) invUnit
  crossConnectPath  : ∀ k₁ k₂ : K, Path (crossNum (connect k₁ k₂)) (invMul (crossNum k₁) (crossNum k₂))
  mirrorMirrorPath  : ∀ k : K, Path (mirror (mirror k)) k
  connectTrivialLPath : ∀ k : K, Path (connect trivial k) k
  connectTrivialRPath : ∀ k : K, Path (connect k trivial) k
  connectAssocPath  : ∀ k₁ k₂ k₃ : K, Path (connect (connect k₁ k₂) k₃) (connect k₁ (connect k₂ k₃))
  invMulAssocPath   : ∀ a b c : Inv, Path (invMul (invMul a b) c) (invMul a (invMul b c))
  invMulUnitLPath   : ∀ a : Inv, Path (invMul invUnit a) a
  invMulUnitRPath   : ∀ a : Inv, Path (invMul a invUnit) a
  invNegNegPath     : ∀ a : Inv, Path (invNeg (invNeg a)) a

namespace KnotInvData

variable {K Inv : Type u} (I : KnotInvData K Inv)

-- ============================================================
-- §2  Jones polynomial coherence  (12 theorems)
-- ============================================================

/-- 1. jonesMirror right-unit -/
@[simp] theorem jonesMirror_trans_refl (k : K) :
    Path.trans (I.jonesMirrorPath k) (Path.refl _) = I.jonesMirrorPath k :=
  Path.trans_refl_right _

/-- 2. jonesMirror left-unit -/
@[simp] theorem refl_trans_jonesMirror (k : K) :
    Path.trans (Path.refl _) (I.jonesMirrorPath k) = I.jonesMirrorPath k :=
  Path.trans_refl_left _

/-- 3. jonesMirror · symm toEq -/
@[simp] theorem jonesMirror_symm_toEq (k : K) :
    (Path.trans (I.jonesMirrorPath k) (Path.symm (I.jonesMirrorPath k))).toEq = rfl :=
  by simp

/-- 4. symm (symm jonesMirror) -/
@[simp] theorem symm_symm_jonesMirror (k : K) :
    Path.symm (Path.symm (I.jonesMirrorPath k)) = I.jonesMirrorPath k :=
  Path.symm_symm _

/-- 5. jonesConnect right-unit -/
@[simp] theorem jonesConnect_trans_refl (k₁ k₂ : K) :
    Path.trans (I.jonesConnectPath k₁ k₂) (Path.refl _) = I.jonesConnectPath k₁ k₂ :=
  Path.trans_refl_right _

/-- 6. jonesConnect · symm toEq -/
@[simp] theorem jonesConnect_symm_toEq (k₁ k₂ : K) :
    (Path.trans (I.jonesConnectPath k₁ k₂) (Path.symm (I.jonesConnectPath k₁ k₂))).toEq = rfl :=
  by simp

/-- 7. symm (symm jonesConnect) -/
@[simp] theorem symm_symm_jonesConnect (k₁ k₂ : K) :
    Path.symm (Path.symm (I.jonesConnectPath k₁ k₂)) = I.jonesConnectPath k₁ k₂ :=
  Path.symm_symm _

/-- 8. jonesTrivial right-unit -/
@[simp] theorem jonesTrivial_trans_refl :
    Path.trans I.jonesTrivialPath (Path.refl _) = I.jonesTrivialPath :=
  Path.trans_refl_right _

/-- 9. jonesTrivial · symm toEq -/
@[simp] theorem jonesTrivial_symm_toEq :
    (Path.trans I.jonesTrivialPath (Path.symm I.jonesTrivialPath)).toEq = rfl :=
  by simp

/-- 10. symm (symm jonesTrivial) -/
@[simp] theorem symm_symm_jonesTrivial :
    Path.symm (Path.symm I.jonesTrivialPath) = I.jonesTrivialPath :=
  Path.symm_symm _

/-- 11. Jones of double mirror: jones(mirror(mirror k)) path -/
noncomputable def jonesDoubleMirrorPath (k : K) :
    Path (I.jones (I.mirror (I.mirror k))) (I.jones k) :=
  Path.congrArg I.jones (I.mirrorMirrorPath k)

/-- 12. jonesDoubleMirror right-unit -/
@[simp] theorem jonesDoubleMirror_trans_refl (k : K) :
    Path.trans (I.jonesDoubleMirrorPath k) (Path.refl _) = I.jonesDoubleMirrorPath k :=
  Path.trans_refl_right _

-- ============================================================
-- §3  Writhe & bracket coherence  (10 theorems)
-- ============================================================

/-- 13. writheConnect right-unit -/
@[simp] theorem writheConnect_trans_refl (k₁ k₂ : K) :
    Path.trans (I.writheConnectPath k₁ k₂) (Path.refl _) = I.writheConnectPath k₁ k₂ :=
  Path.trans_refl_right _

/-- 14. writheConnect · symm toEq -/
@[simp] theorem writheConnect_symm_toEq (k₁ k₂ : K) :
    (Path.trans (I.writheConnectPath k₁ k₂) (Path.symm (I.writheConnectPath k₁ k₂))).toEq = rfl :=
  by simp

/-- 15. symm (symm writheConnect) -/
@[simp] theorem symm_symm_writheConnect (k₁ k₂ : K) :
    Path.symm (Path.symm (I.writheConnectPath k₁ k₂)) = I.writheConnectPath k₁ k₂ :=
  Path.symm_symm _

/-- 16. writheMirror right-unit -/
@[simp] theorem writheMirror_trans_refl (k : K) :
    Path.trans (I.writheMirrorPath k) (Path.refl _) = I.writheMirrorPath k :=
  Path.trans_refl_right _

/-- 17. symm (symm writheMirror) -/
@[simp] theorem symm_symm_writheMirror (k : K) :
    Path.symm (Path.symm (I.writheMirrorPath k)) = I.writheMirrorPath k :=
  Path.symm_symm _

/-- 18. bracketConnect right-unit -/
@[simp] theorem bracketConnect_trans_refl (k₁ k₂ : K) :
    Path.trans (I.bracketConnectPath k₁ k₂) (Path.refl _) = I.bracketConnectPath k₁ k₂ :=
  Path.trans_refl_right _

/-- 19. bracketConnect · symm toEq -/
@[simp] theorem bracketConnect_symm_toEq (k₁ k₂ : K) :
    (Path.trans (I.bracketConnectPath k₁ k₂) (Path.symm (I.bracketConnectPath k₁ k₂))).toEq = rfl :=
  by simp

/-- 20. symm (symm bracketConnect) -/
@[simp] theorem symm_symm_bracketConnect (k₁ k₂ : K) :
    Path.symm (Path.symm (I.bracketConnectPath k₁ k₂)) = I.bracketConnectPath k₁ k₂ :=
  Path.symm_symm _

/-- 21. bracketTrivial right-unit -/
@[simp] theorem bracketTrivial_trans_refl :
    Path.trans I.bracketTrivialPath (Path.refl _) = I.bracketTrivialPath :=
  Path.trans_refl_right _

/-- 22. symm (symm bracketTrivial) -/
@[simp] theorem symm_symm_bracketTrivial :
    Path.symm (Path.symm I.bracketTrivialPath) = I.bracketTrivialPath :=
  Path.symm_symm _

-- ============================================================
-- §4  Connected sum & mirror coherence  (14 theorems)
-- ============================================================

/-- 23. mirrorMirror right-unit -/
@[simp] theorem mirrorMirror_trans_refl (k : K) :
    Path.trans (I.mirrorMirrorPath k) (Path.refl _) = I.mirrorMirrorPath k :=
  Path.trans_refl_right _

/-- 24. mirrorMirror · symm toEq -/
@[simp] theorem mirrorMirror_symm_toEq (k : K) :
    (Path.trans (I.mirrorMirrorPath k) (Path.symm (I.mirrorMirrorPath k))).toEq = rfl :=
  by simp

/-- 25. symm (symm mirrorMirror) -/
@[simp] theorem symm_symm_mirrorMirror (k : K) :
    Path.symm (Path.symm (I.mirrorMirrorPath k)) = I.mirrorMirrorPath k :=
  Path.symm_symm _

/-- 26. connectTrivialL right-unit -/
@[simp] theorem connectTrivialL_trans_refl (k : K) :
    Path.trans (I.connectTrivialLPath k) (Path.refl _) = I.connectTrivialLPath k :=
  Path.trans_refl_right _

/-- 27. connectTrivialR right-unit -/
@[simp] theorem connectTrivialR_trans_refl (k : K) :
    Path.trans (I.connectTrivialRPath k) (Path.refl _) = I.connectTrivialRPath k :=
  Path.trans_refl_right _

/-- 28. connectAssoc right-unit -/
@[simp] theorem connectAssoc_trans_refl (k₁ k₂ k₃ : K) :
    Path.trans (I.connectAssocPath k₁ k₂ k₃) (Path.refl _) = I.connectAssocPath k₁ k₂ k₃ :=
  Path.trans_refl_right _

/-- 29. connectAssoc · symm toEq -/
@[simp] theorem connectAssoc_symm_toEq (k₁ k₂ k₃ : K) :
    (Path.trans (I.connectAssocPath k₁ k₂ k₃) (Path.symm (I.connectAssocPath k₁ k₂ k₃))).toEq = rfl :=
  by simp

/-- 30. symm (symm connectAssoc) -/
@[simp] theorem symm_symm_connectAssoc (k₁ k₂ k₃ : K) :
    Path.symm (Path.symm (I.connectAssocPath k₁ k₂ k₃)) = I.connectAssocPath k₁ k₂ k₃ :=
  Path.symm_symm _

/-- 31. congrArg mirror on connectAssoc -/
noncomputable def mirrorConnectAssocPath (k₁ k₂ k₃ : K) :
    Path (I.mirror (I.connect (I.connect k₁ k₂) k₃))
         (I.mirror (I.connect k₁ (I.connect k₂ k₃))) :=
  Path.congrArg I.mirror (I.connectAssocPath k₁ k₂ k₃)

/-- 32. mirrorConnectAssoc right-unit -/
@[simp] theorem mirrorConnectAssoc_trans_refl (k₁ k₂ k₃ : K) :
    Path.trans (I.mirrorConnectAssocPath k₁ k₂ k₃) (Path.refl _) = I.mirrorConnectAssocPath k₁ k₂ k₃ :=
  Path.trans_refl_right _

/-- 33. congrArg jones on connectAssoc -/
noncomputable def jonesConnectAssocPath (k₁ k₂ k₃ : K) :
    Path (I.jones (I.connect (I.connect k₁ k₂) k₃))
         (I.jones (I.connect k₁ (I.connect k₂ k₃))) :=
  Path.congrArg I.jones (I.connectAssocPath k₁ k₂ k₃)

/-- 34. jonesConnectAssoc right-unit -/
@[simp] theorem jonesConnectAssoc_trans_refl (k₁ k₂ k₃ : K) :
    Path.trans (I.jonesConnectAssocPath k₁ k₂ k₃) (Path.refl _) = I.jonesConnectAssocPath k₁ k₂ k₃ :=
  Path.trans_refl_right _

/-- 35. congrArg mirror on mirrorMirror -/
noncomputable def mirrorCubedPath (k : K) :
    Path (I.mirror (I.mirror (I.mirror k))) (I.mirror k) :=
  Path.congrArg I.mirror (I.mirrorMirrorPath k)

/-- 36. mirrorCubed right-unit -/
@[simp] theorem mirrorCubed_trans_refl (k : K) :
    Path.trans (I.mirrorCubedPath k) (Path.refl _) = I.mirrorCubedPath k :=
  Path.trans_refl_right _

-- ============================================================
-- §5  Invariant algebra coherence  (10 theorems)
-- ============================================================

/-- 37. invMulAssoc right-unit -/
@[simp] theorem invMulAssoc_trans_refl (a b c : Inv) :
    Path.trans (I.invMulAssocPath a b c) (Path.refl _) = I.invMulAssocPath a b c :=
  Path.trans_refl_right _

/-- 38. invMulAssoc · symm toEq -/
@[simp] theorem invMulAssoc_symm_toEq (a b c : Inv) :
    (Path.trans (I.invMulAssocPath a b c) (Path.symm (I.invMulAssocPath a b c))).toEq = rfl :=
  by simp

/-- 39. symm (symm invMulAssoc) -/
@[simp] theorem symm_symm_invMulAssoc (a b c : Inv) :
    Path.symm (Path.symm (I.invMulAssocPath a b c)) = I.invMulAssocPath a b c :=
  Path.symm_symm _

/-- 40. invMulUnitL right-unit -/
@[simp] theorem invMulUnitL_trans_refl (a : Inv) :
    Path.trans (I.invMulUnitLPath a) (Path.refl _) = I.invMulUnitLPath a :=
  Path.trans_refl_right _

/-- 41. invMulUnitR right-unit -/
@[simp] theorem invMulUnitR_trans_refl (a : Inv) :
    Path.trans (I.invMulUnitRPath a) (Path.refl _) = I.invMulUnitRPath a :=
  Path.trans_refl_right _

/-- 42. invNegNeg right-unit -/
@[simp] theorem invNegNeg_trans_refl (a : Inv) :
    Path.trans (I.invNegNegPath a) (Path.refl _) = I.invNegNegPath a :=
  Path.trans_refl_right _

/-- 43. invNegNeg · symm toEq -/
@[simp] theorem invNegNeg_symm_toEq (a : Inv) :
    (Path.trans (I.invNegNegPath a) (Path.symm (I.invNegNegPath a))).toEq = rfl :=
  by simp

/-- 44. symm (symm invNegNeg) -/
@[simp] theorem symm_symm_invNegNeg (a : Inv) :
    Path.symm (Path.symm (I.invNegNegPath a)) = I.invNegNegPath a :=
  Path.symm_symm _

/-- 45. congrArg invNeg on invMulAssoc -/
noncomputable def negMulAssocPath (a b c : Inv) :
    Path (I.invNeg (I.invMul (I.invMul a b) c))
         (I.invNeg (I.invMul a (I.invMul b c))) :=
  Path.congrArg I.invNeg (I.invMulAssocPath a b c)

/-- 46. negMulAssoc right-unit -/
@[simp] theorem negMulAssoc_trans_refl (a b c : Inv) :
    Path.trans (I.negMulAssocPath a b c) (Path.refl _) = I.negMulAssocPath a b c :=
  Path.trans_refl_right _

-- ============================================================
-- §6  Composite invariance paths  (14 theorems)
-- ============================================================

/-- 47. Jones of connected-sum of mirror: j(mirror k₁ # k₂) -/
noncomputable def jonesMirrorConnectPath (k₁ k₂ : K) :
    Path (I.jones (I.connect (I.mirror k₁) k₂))
         (I.invMul (I.invNeg (I.jones k₁)) (I.jones k₂)) :=
  Path.trans
    (I.jonesConnectPath (I.mirror k₁) k₂)
    (Path.congrArg (I.invMul · (I.jones k₂)) (I.jonesMirrorPath k₁))

/-- 48. jonesMirrorConnect right-unit -/
@[simp] theorem jonesMirrorConnect_trans_refl (k₁ k₂ : K) :
    Path.trans (I.jonesMirrorConnectPath k₁ k₂) (Path.refl _) = I.jonesMirrorConnectPath k₁ k₂ :=
  Path.trans_refl_right _

/-- 49. symm (symm jonesMirrorConnect) -/
@[simp] theorem symm_symm_jonesMirrorConnect (k₁ k₂ : K) :
    Path.symm (Path.symm (I.jonesMirrorConnectPath k₁ k₂)) = I.jonesMirrorConnectPath k₁ k₂ :=
  Path.symm_symm _

/-- 50. Jones of trivial connect: jones(unknot # k) = jones k -/
noncomputable def jonesTrivialConnectPath (k : K) :
    Path (I.jones (I.connect I.trivial k)) (I.jones k) :=
  Path.congrArg I.jones (I.connectTrivialLPath k)

/-- 51. jonesTrivialConnect right-unit -/
@[simp] theorem jonesTrivialConnect_trans_refl (k : K) :
    Path.trans (I.jonesTrivialConnectPath k) (Path.refl _) = I.jonesTrivialConnectPath k :=
  Path.trans_refl_right _

/-- 52. congrArg writhe on connectAssoc -/
noncomputable def writheConnectAssocPath (k₁ k₂ k₃ : K) :
    Path (I.writhe (I.connect (I.connect k₁ k₂) k₃))
         (I.writhe (I.connect k₁ (I.connect k₂ k₃))) :=
  Path.congrArg I.writhe (I.connectAssocPath k₁ k₂ k₃)

/-- 53. writheConnectAssoc right-unit -/
@[simp] theorem writheConnectAssoc_trans_refl (k₁ k₂ k₃ : K) :
    Path.trans (I.writheConnectAssocPath k₁ k₂ k₃) (Path.refl _) = I.writheConnectAssocPath k₁ k₂ k₃ :=
  Path.trans_refl_right _

/-- 54. congrArg bracket on connectAssoc -/
noncomputable def bracketConnectAssocPath (k₁ k₂ k₃ : K) :
    Path (I.bracket (I.connect (I.connect k₁ k₂) k₃))
         (I.bracket (I.connect k₁ (I.connect k₂ k₃))) :=
  Path.congrArg I.bracket (I.connectAssocPath k₁ k₂ k₃)

/-- 55. bracketConnectAssoc right-unit -/
@[simp] theorem bracketConnectAssoc_trans_refl (k₁ k₂ k₃ : K) :
    Path.trans (I.bracketConnectAssocPath k₁ k₂ k₃) (Path.refl _) = I.bracketConnectAssocPath k₁ k₂ k₃ :=
  Path.trans_refl_right _

/-- 56. congrArg crossNum on mirrorMirror -/
noncomputable def crossMirrorMirrorPath (k : K) :
    Path (I.crossNum (I.mirror (I.mirror k))) (I.crossNum k) :=
  Path.congrArg I.crossNum (I.mirrorMirrorPath k)

/-- 57. crossMirrorMirror right-unit -/
@[simp] theorem crossMirrorMirror_trans_refl (k : K) :
    Path.trans (I.crossMirrorMirrorPath k) (Path.refl _) = I.crossMirrorMirrorPath k :=
  Path.trans_refl_right _

/-- 58. symm distributes over jonesMirrorConnect -/
theorem symm_jonesMirrorConnect (k₁ k₂ : K) :
    Path.symm (I.jonesMirrorConnectPath k₁ k₂) =
    Path.trans
      (Path.symm (Path.congrArg (I.invMul · (I.jones k₂)) (I.jonesMirrorPath k₁)))
      (Path.symm (I.jonesConnectPath (I.mirror k₁) k₂)) :=
  Path.symm_trans _ _

/-- 59. congrArg jones on connectTrivialR -/
noncomputable def jonesConnectTrivialRPath (k : K) :
    Path (I.jones (I.connect k I.trivial)) (I.jones k) :=
  Path.congrArg I.jones (I.connectTrivialRPath k)

/-- 60. jonesConnectTrivialR right-unit -/
@[simp] theorem jonesConnectTrivialR_trans_refl (k : K) :
    Path.trans (I.jonesConnectTrivialRPath k) (Path.refl _) = I.jonesConnectTrivialRPath k :=
  Path.trans_refl_right _

end KnotInvData
end KnotInvariantPaths
end KnotInvariant
end ComputationalPaths
