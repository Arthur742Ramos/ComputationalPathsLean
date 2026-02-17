/-
# Homological Commutative Algebra via Computational Paths — Deep Rewrite System

Free ℤ-module algebra (direct sum, tensor, Hom, Ext, Tor) modelled as
a domain-specific rewriting system with genuine multi-step Path operations.

Zero `Path.mk [Step.mk _ _ h] h` — every path built from `step`, `trans`, `symm`, `congrDS/Ten`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.HomCommAlgDeep

universe u

-- ============================================================
-- § 1. Free ℤ-module expressions (symbolic algebra)
-- ============================================================

/-- Symbolic expressions for free ℤ-module operations. -/
inductive FMExpr : Type where
  | zero : FMExpr
  | ofRank : Nat → FMExpr
  | ds : FMExpr → FMExpr → FMExpr          -- direct sum
  | ten : FMExpr → FMExpr → FMExpr         -- tensor product
  | hom : FMExpr → FMExpr → FMExpr         -- Hom space
  | ext1 : FMExpr → FMExpr → FMExpr        -- Ext¹
  | tor1 : FMExpr → FMExpr → FMExpr        -- Tor₁
  deriving DecidableEq, Repr

-- Notation shortcuts for readability
local notation "𝟎" => FMExpr.zero
local notation "ℤ^" => FMExpr.ofRank
local infixl:65 " ⊕ " => FMExpr.ds
local infixl:70 " ⊗ " => FMExpr.ten

-- ============================================================
-- § 2. Single rewrite steps (domain axioms)
-- ============================================================

/-- Elementary rewrite steps for free module algebra. -/
inductive FMStep : FMExpr → FMExpr → Type where
  -- Direct sum axioms
  | dsComm (M N : FMExpr) : FMStep (M ⊕ N) (N ⊕ M)
  | dsAssoc (M N K : FMExpr) : FMStep ((M ⊕ N) ⊕ K) (M ⊕ (N ⊕ K))
  | dsZeroR (M : FMExpr) : FMStep (M ⊕ 𝟎) M
  | dsZeroL (M : FMExpr) : FMStep (𝟎 ⊕ M) M
  -- Tensor axioms
  | tenComm (M N : FMExpr) : FMStep (M ⊗ N) (N ⊗ M)
  | tenAssoc (M N K : FMExpr) : FMStep ((M ⊗ N) ⊗ K) (M ⊗ (N ⊗ K))
  | tenUnitR (M : FMExpr) : FMStep (M ⊗ (ℤ^ 1)) M
  | tenUnitL (M : FMExpr) : FMStep ((ℤ^ 1) ⊗ M) M
  | tenZeroR (M : FMExpr) : FMStep (M ⊗ 𝟎) 𝟎
  | tenZeroL (M : FMExpr) : FMStep (𝟎 ⊗ M) 𝟎
  -- Distributivity
  | tenDistR (M N K : FMExpr) : FMStep (M ⊗ (N ⊕ K)) ((M ⊗ N) ⊕ (M ⊗ K))
  | tenDistL (M N K : FMExpr) : FMStep ((M ⊕ N) ⊗ K) ((M ⊗ K) ⊕ (N ⊗ K))
  -- Hom/Ext/Tor for free modules
  | ext1Free (M N : FMExpr) : FMStep (.ext1 M N) 𝟎
  | tor1Free (M N : FMExpr) : FMStep (.tor1 M N) 𝟎

-- ============================================================
-- § 3. Paths: reflexive-transitive-symmetric congruence closure
-- ============================================================

/-- Paths in the free module rewriting system. -/
inductive FMPath : FMExpr → FMExpr → Type where
  | refl (M : FMExpr) : FMPath M M
  | step {M N : FMExpr} : FMStep M N → FMPath M N
  | trans {M N K : FMExpr} : FMPath M N → FMPath N K → FMPath M K
  | symm {M N : FMExpr} : FMPath M N → FMPath N M
  | congrDS {M M' N N' : FMExpr} :
      FMPath M M' → FMPath N N' → FMPath (M ⊕ N) (M' ⊕ N')
  | congrTen {M M' N N' : FMExpr} :
      FMPath M M' → FMPath N N' → FMPath (M ⊗ N) (M' ⊗ N')

namespace FMPath

-- ============================================================
-- § 4. Direct sum algebra (theorems 1–10)
-- ============================================================

/-- 1. Direct sum commutativity -/
def dsComm (M N : FMExpr) : FMPath (M ⊕ N) (N ⊕ M) :=
  step (.dsComm M N)

/-- 2. Direct sum associativity -/
def dsAssoc (M N K : FMExpr) : FMPath ((M ⊕ N) ⊕ K) (M ⊕ (N ⊕ K)) :=
  step (.dsAssoc M N K)

/-- 3. Right zero unit -/
def dsZeroR (M : FMExpr) : FMPath (M ⊕ 𝟎) M :=
  step (.dsZeroR M)

/-- 4. Left zero unit -/
def dsZeroL (M : FMExpr) : FMPath (𝟎 ⊕ M) M :=
  step (.dsZeroL M)

/-- 5. Left zero via comm + right zero (2-step) -/
def dsZeroL' (M : FMExpr) : FMPath (𝟎 ⊕ M) M :=
  trans (dsComm 𝟎 M) (dsZeroR M)

/-- 6. Double comm is roundtrip -/
def dsCommComm (M N : FMExpr) : FMPath (M ⊕ N) (M ⊕ N) :=
  trans (dsComm M N) (dsComm N M)

/-- 7. Associativity inverse -/
def dsAssocInv (M N K : FMExpr) : FMPath (M ⊕ (N ⊕ K)) ((M ⊕ N) ⊕ K) :=
  symm (dsAssoc M N K)

/-- 8. Swap inner pair: (M⊕N)⊕K → (N⊕M)⊕K -/
def dsSwapLeft (M N K : FMExpr) : FMPath ((M ⊕ N) ⊕ K) ((N ⊕ M) ⊕ K) :=
  congrDS (dsComm M N) (refl K)

/-- 9. Swap inner pair: M⊕(N⊕K) → M⊕(K⊕N) -/
def dsSwapRight (M N K : FMExpr) : FMPath (M ⊕ (N ⊕ K)) (M ⊕ (K ⊕ N)) :=
  congrDS (refl M) (dsComm N K)

/-- 10. Pentagon associator path (left route):
    ((A⊕B)⊕C)⊕D → (A⊕B)⊕(C⊕D) → A⊕(B⊕(C⊕D)) -/
def dsPentagonLeft (A B C D : FMExpr) :
    FMPath (((A ⊕ B) ⊕ C) ⊕ D) (A ⊕ (B ⊕ (C ⊕ D))) :=
  trans (dsAssoc (A ⊕ B) C D) (dsAssoc A B (C ⊕ D))

-- ============================================================
-- § 5. Tensor product algebra (theorems 11–20)
-- ============================================================

/-- 11. Tensor commutativity -/
def tenComm (M N : FMExpr) : FMPath (M ⊗ N) (N ⊗ M) :=
  step (.tenComm M N)

/-- 12. Tensor associativity -/
def tenAssoc (M N K : FMExpr) : FMPath ((M ⊗ N) ⊗ K) (M ⊗ (N ⊗ K)) :=
  step (.tenAssoc M N K)

/-- 13. Tensor right unit -/
def tenUnitR (M : FMExpr) : FMPath (M ⊗ (ℤ^ 1)) M :=
  step (.tenUnitR M)

/-- 14. Tensor left unit via comm -/
def tenUnitL (M : FMExpr) : FMPath ((ℤ^ 1) ⊗ M) M :=
  step (.tenUnitL M)

/-- 15. Tensor left unit via comm + right unit (2-step) -/
def tenUnitL' (M : FMExpr) : FMPath ((ℤ^ 1) ⊗ M) M :=
  trans (tenComm (ℤ^ 1) M) (tenUnitR M)

/-- 16. Tensor zero right -/
def tenZeroR (M : FMExpr) : FMPath (M ⊗ 𝟎) 𝟎 :=
  step (.tenZeroR M)

/-- 17. Tensor zero left via comm (2-step) -/
def tenZeroL' (M : FMExpr) : FMPath (𝟎 ⊗ M) 𝟎 :=
  trans (tenComm 𝟎 M) (tenZeroR M)

/-- 18. Tensor distributes right -/
def tenDistR (M N K : FMExpr) : FMPath (M ⊗ (N ⊕ K)) ((M ⊗ N) ⊕ (M ⊗ K)) :=
  step (.tenDistR M N K)

/-- 19. Tensor distributes left -/
def tenDistL (M N K : FMExpr) : FMPath ((M ⊕ N) ⊗ K) ((M ⊗ K) ⊕ (N ⊗ K)) :=
  step (.tenDistL M N K)

/-- 20. Double tensor comm is roundtrip -/
def tenCommComm (M N : FMExpr) : FMPath (M ⊗ N) (M ⊗ N) :=
  trans (tenComm M N) (tenComm N M)

-- ============================================================
-- § 6. Composite paths (theorems 21–30)
-- ============================================================

/-- 21. Tensor comm then assoc (3-step): (M⊗N)⊗K → (N⊗M)⊗K → N⊗(M⊗K) -/
def tenCommAssoc (M N K : FMExpr) :
    FMPath ((M ⊗ N) ⊗ K) (N ⊗ (M ⊗ K)) :=
  trans (congrTen (tenComm M N) (refl K)) (tenAssoc N M K)

/-- 22. Tensor assoc inverse -/
def tenAssocInv (M N K : FMExpr) : FMPath (M ⊗ (N ⊗ K)) ((M ⊗ N) ⊗ K) :=
  symm (tenAssoc M N K)

/-- 23. Pentagon for tensor (left route) -/
def tenPentagonLeft (A B C D : FMExpr) :
    FMPath (((A ⊗ B) ⊗ C) ⊗ D) (A ⊗ (B ⊗ (C ⊗ D))) :=
  trans (tenAssoc (A ⊗ B) C D) (tenAssoc A B (C ⊗ D))

/-- 24. Pentagon for tensor (right route) -/
def tenPentagonRight (A B C D : FMExpr) :
    FMPath (((A ⊗ B) ⊗ C) ⊗ D) (A ⊗ (B ⊗ (C ⊗ D))) :=
  trans (congrTen (tenAssoc A B C) (refl D))
    (trans (tenAssoc A (B ⊗ C) D)
      (congrTen (refl A) (tenAssoc B C D)))

/-- 25. Tensor zero absorbs direct sum:
    M ⊗ (N ⊕ 𝟎) → (M⊗N) ⊕ (M⊗𝟎) → (M⊗N) ⊕ 𝟎 → M⊗N (4-step) -/
def tenAbsorbDSZero (M N : FMExpr) :
    FMPath (M ⊗ (N ⊕ 𝟎)) (M ⊗ N) :=
  trans (tenDistR M N 𝟎)
    (trans (congrDS (refl (M ⊗ N)) (tenZeroR M))
      (dsZeroR (M ⊗ N)))

/-- 26. Direct sum of zeros is zero (3-step): 𝟎 ⊕ 𝟎 → 𝟎 -/
def dsZeroZero : FMPath (𝟎 ⊕ 𝟎) 𝟎 :=
  dsZeroR 𝟎

/-- 27. Tensor of units: (ℤ^1) ⊗ (ℤ^1) → ℤ^1 -/
def tenUnits : FMPath ((ℤ^ 1) ⊗ (ℤ^ 1)) (ℤ^ 1) :=
  tenUnitR (ℤ^ 1)

-- ============================================================
-- § 7. Ext/Tor vanishing (theorems 28–35)
-- ============================================================

/-- 28. Ext¹ vanishes for free modules -/
def ext1Vanish (M N : FMExpr) : FMPath (.ext1 M N) 𝟎 :=
  step (.ext1Free M N)

/-- 29. Tor₁ vanishes for free modules -/
def tor1Vanish (M N : FMExpr) : FMPath (.tor1 M N) 𝟎 :=
  step (.tor1Free M N)

/-- 30. Ext¹ vanishing is symmetric (up to both being zero):
    Ext¹(M,N) → 𝟎 ← Ext¹(N,M) -/
def ext1VanishSym (M N : FMExpr) : FMPath (.ext1 M N) (.ext1 N M) :=
  trans (ext1Vanish M N) (symm (ext1Vanish N M))

/-- 31. Tor₁ vanishing is symmetric -/
def tor1VanishSym (M N : FMExpr) : FMPath (.tor1 M N) (.tor1 N M) :=
  trans (tor1Vanish M N) (symm (tor1Vanish N M))

/-- 32. Direct sum of Ext¹ vanishes:
    Ext¹(M,N) ⊕ Ext¹(N,M) → 𝟎 ⊕ 𝟎 → 𝟎 -/
def ext1DSSumVanish (M N : FMExpr) :
    FMPath (.ext1 M N ⊕ .ext1 N M) 𝟎 :=
  trans (congrDS (ext1Vanish M N) (ext1Vanish N M)) dsZeroZero

/-- 33. Direct sum of Tor₁ vanishes -/
def tor1DSSumVanish (M N : FMExpr) :
    FMPath (.tor1 M N ⊕ .tor1 N M) 𝟎 :=
  trans (congrDS (tor1Vanish M N) (tor1Vanish N M)) dsZeroZero

/-- 34. Tensor with Ext¹ vanishes:
    K ⊗ Ext¹(M,N) → K ⊗ 𝟎 → 𝟎 -/
def tenExt1Vanish (K M N : FMExpr) : FMPath (K ⊗ .ext1 M N) 𝟎 :=
  trans (congrTen (refl K) (ext1Vanish M N)) (tenZeroR K)

/-- 35. Tensor with Tor₁ vanishes -/
def tenTor1Vanish (K M N : FMExpr) : FMPath (K ⊗ .tor1 M N) 𝟎 :=
  trans (congrTen (refl K) (tor1Vanish M N)) (tenZeroR K)

-- ============================================================
-- § 8. Longer composite paths (theorems 36–42)
-- ============================================================

/-- 36. Four-fold direct sum reassociation:
    ((A⊕B)⊕C)⊕D → A⊕(B⊕(C⊕D)) → (B⊕(C⊕D))⊕A -/
def dsFourFoldComm (A B C D : FMExpr) :
    FMPath (((A ⊕ B) ⊕ C) ⊕ D) ((B ⊕ (C ⊕ D)) ⊕ A) :=
  trans (dsPentagonLeft A B C D) (dsComm A (B ⊕ (C ⊕ D)))

/-- 37. Distribute then collect:
    (A⊕B)⊗(C⊕D) → ((A⊕B)⊗C)⊕((A⊕B)⊗D) → ((A⊗C)⊕(B⊗C))⊕((A⊗D)⊕(B⊗D)) -/
def tenFullDist (A B C D : FMExpr) :
    FMPath ((A ⊕ B) ⊗ (C ⊕ D))
           (((A ⊗ C) ⊕ (B ⊗ C)) ⊕ ((A ⊗ D) ⊕ (B ⊗ D))) :=
  trans (tenDistR (A ⊕ B) C D)
    (congrDS (tenDistL A B C) (tenDistL A B D))

/-- 38. Symmetric version of full distribute:
    (C⊕D)⊗(A⊕B) → (A⊕B)⊗(C⊕D) → full dist -/
def tenFullDistSym (A B C D : FMExpr) :
    FMPath ((C ⊕ D) ⊗ (A ⊕ B))
           (((A ⊗ C) ⊕ (B ⊗ C)) ⊕ ((A ⊗ D) ⊕ (B ⊗ D))) :=
  trans (tenComm (C ⊕ D) (A ⊕ B)) (tenFullDist A B C D)

/-- 39. Zero tensor absorbed through direct sum:
    (M ⊕ 𝟎) ⊗ N → M ⊗ N (3-step) -/
def dsTenAbsorb (M N : FMExpr) : FMPath ((M ⊕ 𝟎) ⊗ N) (M ⊗ N) :=
  trans (tenDistL M 𝟎 N)
    (trans (congrDS (refl (M ⊗ N)) (step (.tenZeroL N)))
      (dsZeroR (M ⊗ N)))

/-- 40. Hexagon path for direct sum braiding:
    (A⊕B)⊕C → A⊕(B⊕C) → A⊕(C⊕B) → (A⊕C)⊕B -/
def dsHexagon (A B C : FMExpr) :
    FMPath ((A ⊕ B) ⊕ C) ((A ⊕ C) ⊕ B) :=
  trans (dsAssoc A B C)
    (trans (dsSwapRight A B C) (dsAssocInv A C B))

/-- 41. Hexagon path for tensor braiding:
    (A⊗B)⊗C → A⊗(B⊗C) → A⊗(C⊗B) → (A⊗C)⊗B -/
def tenHexagon (A B C : FMExpr) :
    FMPath ((A ⊗ B) ⊗ C) ((A ⊗ C) ⊗ B) :=
  trans (tenAssoc A B C)
    (trans (congrTen (refl A) (tenComm B C))
      (tenAssocInv A C B))

/-- 42. Triangle coherence: (M⊗ℤ^1)⊗N → M⊗N ← M⊗(ℤ^1⊗N) -/
def tenTriangle (M N : FMExpr) :
    FMPath ((M ⊗ (ℤ^ 1)) ⊗ N) (M ⊗ N) :=
  congrTen (tenUnitR M) (refl N)

def tenTriangleAlt (M N : FMExpr) :
    FMPath (M ⊗ ((ℤ^ 1) ⊗ N)) (M ⊗ N) :=
  congrTen (refl M) (tenUnitL N)

-- ============================================================
-- § 9. Path algebra utilities (theorems 43–48)
-- ============================================================

/-- 43. Compose congruences: (M⊕N)⊗K → (N⊕M)⊗K -/
def congrTenDSComm (M N K : FMExpr) :
    FMPath ((M ⊕ N) ⊗ K) ((N ⊕ M) ⊗ K) :=
  congrTen (dsComm M N) (refl K)

/-- 44. Nested congruence: (M⊗N)⊕(K⊗L) → (N⊗M)⊕(L⊗K) -/
def dsOfTenComms (M N K L : FMExpr) :
    FMPath ((M ⊗ N) ⊕ (K ⊗ L)) ((N ⊗ M) ⊕ (L ⊗ K)) :=
  congrDS (tenComm M N) (tenComm K L)

/-- 45. Self-inverse symmetry: symm (symm p) -/
def symmSymm (M N : FMExpr) (p : FMPath M N) : FMPath M N :=
  symm (symm p)

/-- 46. Ext vanishing chain with tensor:
    (Ext¹(M,N) ⊕ Tor₁(M,N)) ⊗ K → 𝟎⊗K → 𝟎 -/
def extTorTenVanish (M N K : FMExpr) :
    FMPath ((.ext1 M N ⊕ .tor1 M N) ⊗ K) 𝟎 :=
  trans (congrTen
    (trans (congrDS (ext1Vanish M N) (tor1Vanish M N)) dsZeroZero)
    (refl K))
    (step (.tenZeroL K))

/-- 47. Three-way direct sum comm:
    (A⊕B)⊕C → A⊕(B⊕C) → (B⊕C)⊕A → B⊕(C⊕A) -/
def dsThreeWayRotate (A B C : FMExpr) :
    FMPath ((A ⊕ B) ⊕ C) (B ⊕ (C ⊕ A)) :=
  trans (dsAssoc A B C)
    (trans (dsComm A (B ⊕ C)) (dsAssoc B C A))

/-- 48. Symmetry preserves composition: trans (symm q) (symm p) -/
def transSymmRev {A B C : FMExpr} (p : FMPath A B) (q : FMPath B C) :
    FMPath C A :=
  trans (symm q) (symm p)

end FMPath

end ComputationalPaths.Path.Algebra.HomCommAlgDeep
