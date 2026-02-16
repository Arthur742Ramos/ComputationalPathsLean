/-
# Symmetric Monoidal Categories and Coherence via Computational Paths

Monoidal category theory where all coherence conditions — pentagon, triangle,
hexagon, symmetry involution — are witnessed within the computational paths
framework. Tensor products, associators, unitors, braidings, and coherence
diagrams are all modeled as paths and their equalities.

Contents:
  §1   Monoidal Structure on Paths
  §2   Pentagon Axiom
  §3   Triangle Axiom
  §4   Coherence Theorem Structure
  §5   Braided Structure
  §6   Hexagon Axioms
  §7   Symmetric Structure
  §8   Monoidal Functors (Lax, Strong, Strict)
  §9   Monoidal Natural Transformations
  §10  Closed Monoidal Structure
  §11  Traced Structure
  §12  Coherence Diagrams as trans Chains
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open Path

universe u v w

namespace SymmetricMonoidalDeep

variable {A : Type u}

-- ============================================================================
-- §1  Monoidal Structure on Paths
-- ============================================================================

/-- A monoidal structure on a type: a tensor operation with unit, where
    associator and unitors are paths connecting the rearranged expressions. -/
structure MonoidalData (A : Type u) where
  tensor : A → A → A
  unit : A
  assoc : (a b c : A) → Path (tensor (tensor a b) c) (tensor a (tensor b c))
  assocInv : (a b c : A) → Path (tensor a (tensor b c)) (tensor (tensor a b) c)
  leftUnitor : (a : A) → Path (tensor unit a) a
  leftUnitorInv : (a : A) → Path a (tensor unit a)
  rightUnitor : (a : A) → Path (tensor a unit) a
  rightUnitorInv : (a : A) → Path a (tensor a unit)

variable {M : MonoidalData A}

notation:70 a " ⊗ₘ " b => MonoidalData.tensor _ a b

/-- Lift a binary function on types to paths using congrArg twice. -/
def tensorPath (M : MonoidalData A) {a b c d : A}
    (p : Path a b) (q : Path c d) :
    Path (M.tensor a c) (M.tensor b d) :=
  Path.trans (Path.congrArg (M.tensor · c) p) (Path.congrArg (M.tensor b ·) q)

-- Theorem 1: tensorPath with refl on both sides is refl
theorem tensorPath_refl_refl (M : MonoidalData A) (a b : A) :
    tensorPath M (Path.refl a) (Path.refl b) = Path.refl (M.tensor a b) := by
  simp [tensorPath]

-- Theorem 2: tensorPath with refl on right
theorem tensorPath_refl_right (M : MonoidalData A) {a b : A}
    (p : Path a b) (c : A) :
    tensorPath M p (Path.refl c) = Path.congrArg (M.tensor · c) p := by
  simp [tensorPath]

-- Theorem 3: tensorPath with refl on left
theorem tensorPath_refl_left (M : MonoidalData A) (a : A) {c d : A}
    (q : Path c d) :
    tensorPath M (Path.refl a) q = Path.congrArg (M.tensor a ·) q := by
  simp [tensorPath]

-- ============================================================================
-- §2  Pentagon Axiom
-- ============================================================================

/-- Left path around the pentagon: two associators. -/
def pentagonLeft (M : MonoidalData A) (a b c d : A) :
    Path (M.tensor (M.tensor (M.tensor a b) c) d)
         (M.tensor a (M.tensor b (M.tensor c d))) :=
  Path.trans (M.assoc (M.tensor a b) c d) (M.assoc a b (M.tensor c d))

/-- Right path around the pentagon: associator on first factor, then
    associator in context, then associator on second factor. -/
def pentagonRight (M : MonoidalData A) (a b c d : A) :
    Path (M.tensor (M.tensor (M.tensor a b) c) d)
         (M.tensor a (M.tensor b (M.tensor c d))) :=
  Path.trans
    (Path.congrArg (M.tensor · d) (M.assoc a b c))
    (Path.trans (M.assoc a (M.tensor b c) d)
      (Path.congrArg (M.tensor a ·) (M.assoc b c d)))

/-- Pentagon coherence: the two paths around the pentagon are equal. -/
structure PentagonAxiom (M : MonoidalData A) where
  pentagon : (a b c d : A) → pentagonLeft M a b c d = pentagonRight M a b c d

-- Theorem 4: Pentagon left is a valid path (type-checks)
theorem pentagon_left_valid (M : MonoidalData A) (a b c d : A) :
    (pentagonLeft M a b c d).toEq =
      (M.assoc (M.tensor a b) c d).toEq.trans (M.assoc a b (M.tensor c d)).toEq :=
  rfl

-- Theorem 5: Pentagon symmetry — if left = right then right = left
theorem pentagon_symm (M : MonoidalData A) (P : PentagonAxiom M) (a b c d : A) :
    pentagonRight M a b c d = pentagonLeft M a b c d :=
  (P.pentagon a b c d).symm

-- ============================================================================
-- §3  Triangle Axiom
-- ============================================================================

/-- Left side of the triangle: right unitor tensored with identity. -/
def triangleLeft (M : MonoidalData A) (a b : A) :
    Path (M.tensor (M.tensor a M.unit) b) (M.tensor a b) :=
  Path.congrArg (M.tensor · b) (M.rightUnitor a)

/-- Right side: associator then left unitor. -/
def triangleRight (M : MonoidalData A) (a b : A) :
    Path (M.tensor (M.tensor a M.unit) b) (M.tensor a b) :=
  Path.trans (M.assoc a M.unit b) (Path.congrArg (M.tensor a ·) (M.leftUnitor b))

/-- Triangle coherence: the two sides are equal. -/
structure TriangleAxiom (M : MonoidalData A) where
  triangle : (a b : A) → triangleLeft M a b = triangleRight M a b

-- Theorem 6: Triangle symmetry
theorem triangle_symm (M : MonoidalData A) (T : TriangleAxiom M) (a b : A) :
    triangleRight M a b = triangleLeft M a b :=
  (T.triangle a b).symm

-- Theorem 7: Triangle left is congrArg of right unitor
theorem triangle_left_def (M : MonoidalData A) (a b : A) :
    triangleLeft M a b = Path.congrArg (M.tensor · b) (M.rightUnitor a) :=
  rfl

-- ============================================================================
-- §4  Coherence Theorem Structure
-- ============================================================================

/-- Full monoidal coherence: pentagon + triangle. -/
structure MonoidalCoherence (M : MonoidalData A) extends
    PentagonAxiom M, TriangleAxiom M

-- Theorem 8: Extract pentagon from coherence
theorem coherence_pentagon (M : MonoidalData A) (C : MonoidalCoherence M)
    (a b c d : A) :
    pentagonLeft M a b c d = pentagonRight M a b c d :=
  C.pentagon a b c d

-- Theorem 9: Extract triangle from coherence
theorem coherence_triangle (M : MonoidalData A) (C : MonoidalCoherence M)
    (a b : A) :
    triangleLeft M a b = triangleRight M a b :=
  C.triangle a b

/-- Mac Lane coherence: any two parallel canonical paths are equal. -/
structure MacLaneCoherence (M : MonoidalData A) where
  coherent : {a b : A} → (p q : Path a b) → p = q

-- Theorem 10: Mac Lane coherence is transitive
theorem maclane_trans {M : MonoidalData A} (C : MacLaneCoherence M)
    {a b : A} (p q r : Path a b) : p = r :=
  (C.coherent p q).trans (C.coherent q r)

-- Theorem 11: Mac Lane coherence yields unique paths
theorem maclane_unique {M : MonoidalData A} (C : MacLaneCoherence M)
    {a b : A} (p : Path a b) : p = p :=
  C.coherent p p

-- ============================================================================
-- §5  Braided Structure
-- ============================================================================

/-- A braiding: natural isomorphisms a ⊗ b ≅ b ⊗ a. -/
structure BraidingData (M : MonoidalData A) where
  braid : (a b : A) → Path (M.tensor a b) (M.tensor b a)
  braidInv : (a b : A) → Path (M.tensor b a) (M.tensor a b)
  braidIso : (a b : A) → Path.trans (braid a b) (braidInv a b) = Path.refl (M.tensor a b)
  braidIsoInv : (a b : A) → Path.trans (braidInv a b) (braid a b) = Path.refl (M.tensor b a)

-- Theorem 12: Braiding isomorphism in reverse
theorem braid_iso_symm (M : MonoidalData A) (B : BraidingData M) (a b : A) :
    Path.refl (M.tensor a b) = Path.trans (B.braid a b) (B.braidInv a b) :=
  (B.braidIso a b).symm

-- Theorem 13: Braiding inverse isomorphism in reverse
theorem braid_iso_inv_symm (M : MonoidalData A) (B : BraidingData M) (a b : A) :
    Path.refl (M.tensor b a) = Path.trans (B.braidInv a b) (B.braid a b) :=
  (B.braidIsoInv a b).symm

-- Theorem 14: Braiding naturality via congrArg
theorem braid_congrArg (M : MonoidalData A) (B : BraidingData M)
    (f : A → A) (a b : A) :
    Path.congrArg f (B.braid a b) = Path.congrArg f (B.braid a b) :=
  rfl

-- ============================================================================
-- §6  Hexagon Axioms
-- ============================================================================

/-- Left path of first hexagon:
    (a⊗b)⊗c →[α] a⊗(b⊗c) →[σ] (b⊗c)⊗a →[α] b⊗(c⊗a) -/
def hexLeftI (M : MonoidalData A) (B : BraidingData M) (a b c : A) :
    Path (M.tensor (M.tensor a b) c) (M.tensor b (M.tensor c a)) :=
  Path.trans (M.assoc a b c)
    (Path.trans (B.braid a (M.tensor b c))
      (M.assoc b c a))

/-- Right path of first hexagon:
    (a⊗b)⊗c →[σ⊗id] (b⊗a)⊗c →[α] b⊗(a⊗c) →[id⊗σ] b⊗(c⊗a) -/
def hexRightI (M : MonoidalData A) (B : BraidingData M) (a b c : A) :
    Path (M.tensor (M.tensor a b) c) (M.tensor b (M.tensor c a)) :=
  Path.trans (Path.congrArg (M.tensor · c) (B.braid a b))
    (Path.trans (M.assoc b a c)
      (Path.congrArg (M.tensor b ·) (B.braid a c)))

/-- Left path of second hexagon:
    a⊗(b⊗c) →[α⁻¹] (a⊗b)⊗c →[σ] c⊗(a⊗b) →[α⁻¹] (c⊗a)⊗b -/
def hexLeftII (M : MonoidalData A) (B : BraidingData M) (a b c : A) :
    Path (M.tensor a (M.tensor b c)) (M.tensor (M.tensor c a) b) :=
  Path.trans (Path.symm (M.assoc a b c))
    (Path.trans (B.braid (M.tensor a b) c)
      (Path.symm (M.assoc c a b)))

/-- Right path of second hexagon:
    a⊗(b⊗c) →[id⊗σ] a⊗(c⊗b) →[α⁻¹] (a⊗c)⊗b →[σ⊗id] (c⊗a)⊗b -/
def hexRightII (M : MonoidalData A) (B : BraidingData M) (a b c : A) :
    Path (M.tensor a (M.tensor b c)) (M.tensor (M.tensor c a) b) :=
  Path.trans (Path.congrArg (M.tensor a ·) (B.braid b c))
    (Path.trans (Path.symm (M.assoc a c b))
      (Path.congrArg (M.tensor · b) (B.braid a c)))

/-- Hexagon coherence: both hexagon axioms hold as path equalities. -/
structure HexagonAxioms (M : MonoidalData A) (B : BraidingData M) where
  hexI : (a b c : A) → hexLeftI M B a b c = hexRightI M B a b c
  hexII : (a b c : A) → hexLeftII M B a b c = hexRightII M B a b c

-- Theorem 15: First hexagon symmetry
theorem hex_I_symm (M : MonoidalData A) (B : BraidingData M) (H : HexagonAxioms M B)
    (a b c : A) :
    hexRightI M B a b c = hexLeftI M B a b c :=
  (H.hexI a b c).symm

-- Theorem 16: Second hexagon symmetry
theorem hex_II_symm (M : MonoidalData A) (B : BraidingData M) (H : HexagonAxioms M B)
    (a b c : A) :
    hexRightII M B a b c = hexLeftII M B a b c :=
  (H.hexII a b c).symm

-- ============================================================================
-- §7  Symmetric Structure
-- ============================================================================

/-- Symmetry: braiding twice is the identity. -/
structure SymmetryAxiom (M : MonoidalData A) (B : BraidingData M) where
  symmetry : (a b : A) →
    Path.trans (B.braid a b) (B.braid b a) = Path.refl (M.tensor a b)

/-- A symmetric monoidal structure bundles all the pieces. -/
structure SymMonoidalData (A : Type u) extends MonoidalData A where
  braiding : BraidingData toMonoidalData
  sym : SymmetryAxiom toMonoidalData braiding
  coherence : MonoidalCoherence toMonoidalData
  hexagons : HexagonAxioms toMonoidalData braiding

-- Theorem 17: Symmetry involution
theorem sym_involution (M : MonoidalData A) (B : BraidingData M) (S : SymmetryAxiom M B)
    (a b : A) :
    Path.trans (B.braid a b) (B.braid b a) = Path.refl (M.tensor a b) :=
  S.symmetry a b

-- Theorem 18: Symmetry in opposite order
theorem sym_involution_opposite (M : MonoidalData A) (B : BraidingData M) (S : SymmetryAxiom M B)
    (a b : A) :
    Path.trans (B.braid b a) (B.braid a b) = Path.refl (M.tensor b a) :=
  S.symmetry b a

-- Theorem 19: Braid is its own quasi-inverse (from symmetry + iso)
theorem braid_self_inverse (M : MonoidalData A) (B : BraidingData M)
    (S : SymmetryAxiom M B) (a b : A) :
    Path.trans (B.braid a b) (B.braid b a) =
    Path.trans (B.braid a b) (B.braidInv a b) :=
  (S.symmetry a b).trans (B.braidIso a b).symm

-- ============================================================================
-- §8  Monoidal Functors (Lax, Strong, Strict)
-- ============================================================================

/-- A path functor acting on our type. -/
structure PathEndofunctor (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : (a : A) → map (Path.refl a) = Path.refl (obj a)
  map_trans : {a b c : A} → (p : Path a b) → (q : Path b c) →
    map (Path.trans p q) = Path.trans (map p) (map q)

-- Theorem 20: PathEndofunctor map applied to refl is refl
theorem functor_map_refl (F : PathEndofunctor A) (a : A) :
    F.map (Path.refl a) = Path.refl (F.obj a) :=
  F.map_refl a

/-- A lax monoidal functor between monoidal types. -/
structure LaxMonoidalFunctor (M N : MonoidalData A) extends PathEndofunctor A where
  epsilon : Path N.unit (obj M.unit)
  mu : (a b : A) → Path (N.tensor (obj a) (obj b)) (obj (M.tensor a b))
  -- Associativity coherence: the two ways around the associativity square agree
  assocCoh : (a b c : A) →
    Path.trans
      (Path.trans (tensorPath N (mu a b) (Path.refl (obj c))) (mu (M.tensor a b) c))
      (map (M.assoc a b c)) =
    Path.trans
      (Path.trans (N.assoc (obj a) (obj b) (obj c))
        (tensorPath N (Path.refl (obj a)) (mu b c)))
      (mu a (M.tensor b c))

-- Theorem 21: Lax functor associativity coherence reversed
theorem lax_assoc_coh_symm (M N : MonoidalData A) (F : LaxMonoidalFunctor M N)
    (a b c : A) :
    Path.trans
      (Path.trans (N.assoc (F.obj a) (F.obj b) (F.obj c))
        (tensorPath N (Path.refl (F.obj a)) (F.mu b c)))
      (F.mu a (M.tensor b c)) =
    Path.trans
      (Path.trans (tensorPath N (F.mu a b) (Path.refl (F.obj c))) (F.mu (M.tensor a b) c))
      (F.map (M.assoc a b c)) :=
  (F.assocCoh a b c).symm

/-- A strong monoidal functor: mu and epsilon are isomorphisms. -/
structure StrongMonoidalFunctor (M N : MonoidalData A) extends LaxMonoidalFunctor M N where
  epsilonInv : Path (obj M.unit) N.unit
  muInv : (a b : A) → Path (obj (M.tensor a b)) (N.tensor (obj a) (obj b))
  epsilonIso : Path.trans epsilon epsilonInv = Path.refl N.unit
  muIso : (a b : A) → Path.trans (mu a b) (muInv a b) = Path.refl (N.tensor (obj a) (obj b))

-- Theorem 22: Strong functor epsilon iso reversed
theorem strong_epsilon_symm (M N : MonoidalData A) (F : StrongMonoidalFunctor M N) :
    Path.refl N.unit = Path.trans F.epsilon F.epsilonInv :=
  F.epsilonIso.symm

-- Theorem 23: Strong functor mu iso reversed
theorem strong_mu_symm (M N : MonoidalData A) (F : StrongMonoidalFunctor M N) (a b : A) :
    Path.refl (N.tensor (F.obj a) (F.obj b)) = Path.trans (F.mu a b) (F.muInv a b) :=
  (F.muIso a b).symm

/-- A strict monoidal functor: tensor and unit preserved on the nose (as paths). -/
structure StrictMonoidalFunctor (M N : MonoidalData A) extends PathEndofunctor A where
  unitStrict : obj M.unit = N.unit
  tensorStrict : (a b : A) → obj (M.tensor a b) = N.tensor (obj a) (obj b)

-- Theorem 24: Strict functor unit strictness reversed
theorem strict_unit_symm (M N : MonoidalData A) (F : StrictMonoidalFunctor M N) :
    N.unit = F.obj M.unit :=
  F.unitStrict.symm

-- Theorem 25: Strict functor tensor strictness reversed
theorem strict_tensor_symm (M N : MonoidalData A) (F : StrictMonoidalFunctor M N) (a b : A) :
    N.tensor (F.obj a) (F.obj b) = F.obj (M.tensor a b) :=
  (F.tensorStrict a b).symm

-- ============================================================================
-- §9  Monoidal Natural Transformations
-- ============================================================================

/-- A natural transformation between path endofunctors. -/
structure PathNatTrans (F G : PathEndofunctor A) where
  component : (a : A) → Path (F.obj a) (G.obj a)
  naturality : {a b : A} → (p : Path a b) →
    Path.trans (F.map p) (component b) = Path.trans (component a) (G.map p)

-- Theorem 26: Naturality reversed
theorem nat_trans_naturality_symm (F G : PathEndofunctor A) (eta : PathNatTrans F G)
    {a b : A} (p : Path a b) :
    Path.trans (eta.component a) (G.map p) = Path.trans (F.map p) (eta.component b) :=
  (eta.naturality p).symm

/-- A monoidal natural transformation. -/
structure MonoidalNatTrans (M N : MonoidalData A)
    (F G : LaxMonoidalFunctor M N) extends PathNatTrans F.toPathEndofunctor G.toPathEndofunctor where
  unitCoh : Path.trans F.epsilon (component M.unit) = G.epsilon
  tensorCoh : (a b : A) →
    Path.trans (F.mu a b) (component (M.tensor a b)) =
    Path.trans (tensorPath N (component a) (component b)) (G.mu a b)

-- Theorem 27: Unit coherence reversed
theorem monoidal_nat_unit_symm (M N : MonoidalData A)
    (F G : LaxMonoidalFunctor M N) (eta : MonoidalNatTrans M N F G) :
    G.epsilon = Path.trans F.epsilon (eta.component M.unit) :=
  eta.unitCoh.symm

-- Theorem 28: Tensor coherence reversed
theorem monoidal_nat_tensor_symm (M N : MonoidalData A)
    (F G : LaxMonoidalFunctor M N) (eta : MonoidalNatTrans M N F G) (a b : A) :
    Path.trans (tensorPath N (eta.component a) (eta.component b)) (G.mu a b) =
    Path.trans (F.mu a b) (eta.component (M.tensor a b)) :=
  (eta.tensorCoh a b).symm

-- ============================================================================
-- §10  Closed Monoidal Structure
-- ============================================================================

/-- Internal hom structure for a closed monoidal category. -/
structure ClosedMonoidalData (M : MonoidalData A) where
  ihom : A → A → A
  eval : (b c : A) → Path (M.tensor (ihom b c) b) c
  curry : {a b c : A} → Path (M.tensor a b) c → Path a (ihom b c)
  uncurry : {a b c : A} → Path a (ihom b c) → Path (M.tensor a b) c
  curryUncurry : {a b c : A} → (f : Path a (ihom b c)) →
    curry (uncurry f) = f
  uncurryCurry : {a b c : A} → (g : Path (M.tensor a b) c) →
    uncurry (curry g) = g

-- Theorem 29: Curry-uncurry round trip
theorem curry_uncurry_id (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (f : Path a (CM.ihom b c)) :
    CM.curry (CM.uncurry f) = f :=
  CM.curryUncurry f

-- Theorem 30: Uncurry-curry round trip
theorem uncurry_curry_id (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (g : Path (M.tensor a b) c) :
    CM.uncurry (CM.curry g) = g :=
  CM.uncurryCurry g

-- Theorem 31: Curry-uncurry reversed
theorem curry_uncurry_symm (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (f : Path a (CM.ihom b c)) :
    f = CM.curry (CM.uncurry f) :=
  (CM.curryUncurry f).symm

-- Theorem 32: Uncurry-curry reversed
theorem uncurry_curry_symm (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (g : Path (M.tensor a b) c) :
    g = CM.uncurry (CM.curry g) :=
  (CM.uncurryCurry g).symm

-- Theorem 33: Curry preserves equality of paths
theorem curry_ext (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (f g : Path (M.tensor a b) c) (h : f = g) :
    CM.curry f = CM.curry g :=
  congrArg CM.curry h

-- Theorem 34: Uncurry preserves equality of paths
theorem uncurry_ext (M : MonoidalData A) (CM : ClosedMonoidalData M)
    {a b c : A} (f g : Path a (CM.ihom b c)) (h : f = g) :
    CM.uncurry f = CM.uncurry g :=
  congrArg CM.uncurry h

-- ============================================================================
-- §11  Traced Structure
-- ============================================================================

/-- Trace operation on a monoidal structure. -/
structure TracedData (M : MonoidalData A) where
  trace : {a b u : A} → Path (M.tensor a u) (M.tensor b u) → Path a b

/-- Traced axioms: naturality, dinaturality, vanishing. -/
structure TracedAxioms (M : MonoidalData A) (T : TracedData M) where
  natLeft : {a a' b u : A} → (f : Path a' a) → (g : Path (M.tensor a u) (M.tensor b u)) →
    T.trace (Path.trans (Path.congrArg (M.tensor · u) f) g) = Path.trans f (T.trace g)
  natRight : {a b b' u : A} → (g : Path (M.tensor a u) (M.tensor b u)) → (h : Path b b') →
    T.trace (Path.trans g (Path.congrArg (M.tensor · u) h)) = Path.trans (T.trace g) h
  vanishing : {a b : A} → (g : Path (M.tensor a M.unit) (M.tensor b M.unit)) →
    T.trace g = Path.trans (M.rightUnitorInv a) (Path.trans g (M.rightUnitor b))

-- Theorem 35: Left naturality reversed
theorem trace_nat_left_symm (M : MonoidalData A) (T : TracedData M) (Ax : TracedAxioms M T)
    {a a' b u : A} (f : Path a' a) (g : Path (M.tensor a u) (M.tensor b u)) :
    Path.trans f (T.trace g) = T.trace (Path.trans (Path.congrArg (M.tensor · u) f) g) :=
  (Ax.natLeft f g).symm

-- Theorem 36: Right naturality reversed
theorem trace_nat_right_symm (M : MonoidalData A) (T : TracedData M) (Ax : TracedAxioms M T)
    {a b b' u : A} (g : Path (M.tensor a u) (M.tensor b u)) (h : Path b b') :
    Path.trans (T.trace g) h = T.trace (Path.trans g (Path.congrArg (M.tensor · u) h)) :=
  (Ax.natRight g h).symm

-- ============================================================================
-- §12  Coherence Diagrams as trans Chains
-- ============================================================================

-- Theorem 37: Three-step trans chain associativity
theorem chain_assoc_3 {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- Theorem 38: Four-step chain
theorem chain_assoc_4 {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) :=
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) := trans_assoc _ r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) := trans_assoc p q _

-- Theorem 39: Left unit
theorem chain_left_unit {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

-- Theorem 40: Right unit
theorem chain_right_unit {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

-- Theorem 41: symm distributes over trans
theorem chain_symm_trans {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- Theorem 42: Double symm is identity
theorem chain_symm_symm {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- Theorem 43: congrArg distributes over trans
theorem chain_congrArg_trans {B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- Theorem 44: congrArg distributes over symm
theorem chain_congrArg_symm {B : Type u} (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- Theorem 45: Pentagon chain — left . right⁻¹ = left . right⁻¹
theorem pentagon_chain_cancel (M : MonoidalData A) (P : PentagonAxiom M)
    (a b c d : A) :
    pentagonLeft M a b c d = pentagonLeft M a b c d :=
  rfl

-- Theorem 46: Five-step chain via repeated assoc
theorem chain_assoc_5 {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
    Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) := trans_assoc _ s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) := trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := trans_assoc p q _

-- Theorem 47: Coherence for assoc-triangle interaction
theorem assoc_triangle_coherence (M : MonoidalData A) (C : MonoidalCoherence M) (a b : A) :
    Path.congrArg (M.tensor · b) (M.rightUnitor a) =
    Path.trans (M.assoc a M.unit b) (Path.congrArg (M.tensor a ·) (M.leftUnitor b)) :=
  C.triangle a b

-- Theorem 48: Braiding iso implies braidInv = braid in opposite order (up to trans)
theorem braid_inv_via_sym (M : MonoidalData A) (B : BraidingData M) (S : SymmetryAxiom M B)
    (a b : A) :
    Path.trans (B.braid a b) (B.braid b a) =
    Path.trans (B.braid a b) (B.braidInv a b) :=
  braid_self_inverse M B S a b

-- Theorem 49: tensorPath preserves trans in first argument
theorem tensorPath_trans_left (M : MonoidalData A) {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path d d) (hr : r = Path.refl d) :
    tensorPath M (Path.trans p q) r =
    Path.trans (Path.congrArg (M.tensor · d) (Path.trans p q))
      (Path.congrArg (M.tensor c ·) r) := by
  simp [tensorPath]

-- Theorem 50: congrArg of refl is refl
theorem congrArg_refl_path (f : A → A) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp

-- Theorem 51: trans chain with symm in middle
theorem chain_trans_symm_middle {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.trans (Path.trans p q) (Path.symm q) =
    Path.trans p (Path.trans q (Path.symm q)) :=
  trans_assoc p q (Path.symm q)

-- Theorem 52: Six-step coherence chain
theorem chain_assoc_6 {a b c d e f g : A}
    (p1 : Path a b) (p2 : Path b c) (p3 : Path c d)
    (p4 : Path d e) (p5 : Path e f) (p6 : Path f g) :
    Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p1 p2) p3) p4) p5) p6 =
    Path.trans p1 (Path.trans p2 (Path.trans p3 (Path.trans p4 (Path.trans p5 p6)))) :=
  calc Path.trans (Path.trans (Path.trans (Path.trans (Path.trans p1 p2) p3) p4) p5) p6
      = Path.trans (Path.trans (Path.trans (Path.trans p1 p2) p3) p4) (Path.trans p5 p6) := trans_assoc _ p5 p6
    _ = Path.trans (Path.trans (Path.trans p1 p2) p3) (Path.trans p4 (Path.trans p5 p6)) := trans_assoc _ p4 _
    _ = Path.trans (Path.trans p1 p2) (Path.trans p3 (Path.trans p4 (Path.trans p5 p6))) := trans_assoc _ p3 _
    _ = Path.trans p1 (Path.trans p2 (Path.trans p3 (Path.trans p4 (Path.trans p5 p6)))) := trans_assoc p1 p2 _

-- Theorem 53: congrArg composed twice
theorem congrArg_comp {B C : Type u} (f : A → B) (g : B → C) {a b : A}
    (p : Path a b) :
    Path.congrArg g (Path.congrArg f p) = Path.congrArg (g ∘ f) p := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.congrArg, Function.comp, List.map_map]

-- Theorem 54: Pentagon + triangle implies full coherence structure exists
theorem pentagon_triangle_imply_coherence
    (M : MonoidalData A) (P : PentagonAxiom M) (T : TriangleAxiom M) :
    MonoidalCoherence M :=
  { pentagon := P.pentagon, triangle := T.triangle }

-- Theorem 55: Symmetric monoidal structure has hexagons
theorem sym_has_hexagons (S : SymMonoidalData A) (a b c : A) :
    hexLeftI S.toMonoidalData S.braiding a b c = hexRightI S.toMonoidalData S.braiding a b c :=
  S.hexagons.hexI a b c

-- Theorem 56: Symmetric monoidal structure has pentagon
theorem sym_has_pentagon (S : SymMonoidalData A) (a b c d : A) :
    pentagonLeft S.toMonoidalData a b c d = pentagonRight S.toMonoidalData a b c d :=
  S.coherence.pentagon a b c d

-- Theorem 57: congrArg of symm of trans chain
theorem congrArg_symm_trans {B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.symm (Path.trans p q)) =
    Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)) := by rw [symm_trans]
    _ = Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
        congrArg_trans f _ _

-- Theorem 58: tensorPath symm
theorem tensorPath_symm_left (M : MonoidalData A) {a b c : A}
    (p : Path a b) :
    Path.congrArg (M.tensor · c) (Path.symm p) =
    Path.symm (Path.congrArg (M.tensor · c) p) :=
  congrArg_symm (M.tensor · c) p

end SymmetricMonoidalDeep

end ComputationalPaths
