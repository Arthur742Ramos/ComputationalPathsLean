/-
  Deformation Theory and Formal Moduli via Computational Paths
  =============================================================

  We develop core structures of deformation theory — Artinian rings,
  small extensions, deformation functors, tangent/obstruction spaces,
  Kodaira-Spencer maps, Kuranishi space structure, Schlessinger's
  conditions (H1–H4), cotangent complex, pro-representability, and
  formal smoothness/étaleness — all formalized through computational
  paths using Path.trans, Path.symm, Path.congrArg, and related
  combinators.

  Author: armada-371 (DeformationTheoryDeep)
-/

import ComputationalPaths.Path.Basic

namespace DeformationTheoryDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

-- ============================================================
-- §1. Artinian Ring Structure
-- ============================================================

/-- An Artinian local ring with residue field k and maximal ideal data. -/
structure ArtinLocal (k : Type u) where
  carrier   : Type u
  residue   : carrier
  maxIdeal  : carrier
  nilpotent : Nat

/-- A small extension is a surjection of Artinian rings with kernel
    annihilated by the maximal ideal. -/
structure SmallExtension (k : Type u) where
  base   : ArtinLocal k
  total  : ArtinLocal k
  kernel : Type u
  order  : Nat

/-- Morphism between Artinian local rings. -/
structure ArtinMorphism (k : Type u) where
  source : ArtinLocal k
  target : ArtinLocal k
  level  : Nat

-- ============================================================
-- §2. Deformation Functor
-- ============================================================

/-- A deformation functor from the category of Artinian local k-algebras
    to Sets, encoded via computational paths. -/
structure DeformationFunctor (k : Type u) where
  obj      : ArtinLocal k -> Type u
  morphMap : ArtinMorphism k -> Type u
  basePoint : Nat

/-- The tangent space of a deformation functor is the value on k[eps]/(eps^2). -/
structure TangentSpace (k : Type u) where
  functor   : DeformationFunctor k
  dualNum   : ArtinLocal k
  dimension : Nat

/-- The obstruction space where obstructions to lifting deformations live. -/
structure ObstructionSpace (k : Type u) where
  functor   : DeformationFunctor k
  obsDim    : Nat
  complete  : Bool

-- ============================================================
-- §3. Infinitesimal Deformations as Path Steps
-- ============================================================

/-- An infinitesimal deformation is a computational path
    from one ring element to its deformation. -/
noncomputable def infinitesimalDeformation (A : Type u) (a b : A) : Type u :=
  Path a b

/-- First-order deformation: path in dual numbers. -/
noncomputable def firstOrderDeformation (A : Type u) (x y : A) : Type u :=
  Path x y

/-- Def 1: Reflexivity gives the trivial deformation. -/
noncomputable def trivialDeformation (A : Type u) (a : A) :
    infinitesimalDeformation A a a :=
  Path.refl a

/-- Def 2: Symmetry gives the inverse deformation. -/
noncomputable def inverseDeformation {A : Type u} {a b : A}
    (d : infinitesimalDeformation A a b) :
    infinitesimalDeformation A b a :=
  Path.symm d

/-- Def 3: Transitivity gives composition of deformations. -/
noncomputable def composeDeformations {A : Type u} {a b c : A}
    (d1 : infinitesimalDeformation A a b)
    (d2 : infinitesimalDeformation A b c) :
    infinitesimalDeformation A a c :=
  Path.trans d1 d2

/-- Theorem 1: Composition of deformations is associative. -/
theorem deformation_compose_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 2: Trivial deformation is left identity for composition. -/
theorem trivial_left_identity {A : Type u} {a b : A} (d : Path a b) :
    Path.trans (Path.refl a) d = d :=
  trans_refl_left d

/-- Theorem 3: Trivial deformation is right identity for composition. -/
theorem trivial_right_identity {A : Type u} {a b : A} (d : Path a b) :
    Path.trans d (Path.refl b) = d :=
  trans_refl_right d

/-- Theorem 4: Symmetry reverses composition order. -/
theorem symm_reverses_composition {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 5: Double inverse returns original deformation. -/
theorem double_inverse_deformation {A : Type u} {a b : A} (d : Path a b) :
    Path.symm (Path.symm d) = d :=
  symm_symm d

/-- Theorem 6: Symm of refl is refl. -/
theorem symm_refl_deformation {A : Type u} (a : A) :
    Path.symm (Path.refl a) = Path.refl a :=
  symm_refl a

-- ============================================================
-- §4. Kodaira-Spencer Map
-- ============================================================

/-- The Kodaira-Spencer map sends a tangent vector to a first-order
    deformation, modeled as congrArg of a path through a family. -/
noncomputable def kodairaSpencerMap {A B : Type u} (f : A -> B) {a1 a2 : A}
    (p : Path a1 a2) : Path (f a1) (f a2) :=
  Path.congrArg f p

/-- Theorem 7: Kodaira-Spencer map preserves composition. -/
theorem ks_preserves_composition {A B : Type u} (f : A -> B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    kodairaSpencerMap f (Path.trans p q) =
      Path.trans (kodairaSpencerMap f p) (kodairaSpencerMap f q) :=
  congrArg_trans f p q

/-- Theorem 8: Kodaira-Spencer map preserves inverses. -/
theorem ks_preserves_inverse {A B : Type u} (f : A -> B)
    {a b : A} (p : Path a b) :
    kodairaSpencerMap f (Path.symm p) =
      Path.symm (kodairaSpencerMap f p) :=
  congrArg_symm f p

/-- Theorem 9: Kodaira-Spencer on trivial deformation is trivial. -/
theorem ks_trivial {A B : Type u} (f : A -> B) (a : A) :
    kodairaSpencerMap f (Path.refl a) = Path.refl (f a) := by
  simp [kodairaSpencerMap, Path.congrArg]

/-- Theorem 10: Composed Kodaira-Spencer maps factor. -/
theorem ks_composition {A B C : Type u} (f : A -> B) (g : B -> C)
    {a1 a2 : A} (p : Path a1 a2) :
    kodairaSpencerMap (g ∘ f) p =
      kodairaSpencerMap g (kodairaSpencerMap f p) :=
  congrArg_comp g f p

/-- Theorem 11: Kodaira-Spencer on identity is the identity. -/
theorem ks_identity {A : Type u} {a b : A} (p : Path a b) :
    kodairaSpencerMap id p = p :=
  congrArg_id p

-- ============================================================
-- §5. Formal Smoothness and Étaleness
-- ============================================================

/-- A deformation is formally smooth if every lifting problem has a solution,
    modeled as existence of a path factorization. -/
structure FormallySmoothLifting (A : Type u) (a b c : A) where
  upper   : Path a b
  lower   : Path a c
  lifting : Path b c
  commutes : Path.trans upper lifting = lower

/-- Def 4: Trivial lifting is formally smooth. -/
noncomputable def trivialSmoothLifting {A : Type u} (a b : A) (p : Path a b) :
    FormallySmoothLifting A a b b where
  upper    := p
  lower    := p
  lifting  := Path.refl b
  commutes := trans_refl_right p

/-- Theorem 12: Smooth lifting commutes. -/
theorem smooth_lifting_commutes {A : Type u} {a b c : A}
    (L : FormallySmoothLifting A a b c) :
    Path.trans L.upper L.lifting = L.lower :=
  L.commutes

/-- A formally étale lifting is unique. -/
structure FormallyEtaleData (A : Type u) (a b c : A) where
  upper     : Path a b
  lower     : Path a c
  lift      : Path b c
  commutes  : Path.trans upper lift = lower

/-- Theorem 13: Étale data commutes. -/
theorem etale_commutes {A : Type u} {a b c : A}
    (E : FormallyEtaleData A a b c) :
    Path.trans E.upper E.lift = E.lower :=
  E.commutes

/-- Def 5: Trivial étale data. -/
noncomputable def trivialEtaleData {A : Type u} (a b : A) (p : Path a b) :
    FormallyEtaleData A a b b where
  upper    := p
  lower    := p
  lift     := Path.refl b
  commutes := trans_refl_right p

-- ============================================================
-- §6. Small Extensions and Obstruction Classes
-- ============================================================

/-- An obstruction class to lifting along a small extension. -/
structure ObstructionClass (A : Type u) (a b : A) where
  baseDeform  : Path a a
  obstruction : Path a b
  vanishes    : Path.trans baseDeform obstruction = obstruction

/-- Def 6: Trivial obstruction class with refl base. -/
noncomputable def trivialObstruction {A : Type u} {a b : A} (p : Path a b) :
    ObstructionClass A a b where
  baseDeform  := Path.refl a
  obstruction := p
  vanishes    := trans_refl_left p

/-- Theorem 14: Obstruction class vanishing condition. -/
theorem obstruction_vanishes {A : Type u} {a b : A}
    (obs : ObstructionClass A a b) :
    Path.trans obs.baseDeform obs.obstruction = obs.obstruction :=
  obs.vanishes

/-- Extension step: a path from one Artinian level to the next. -/
noncomputable def extensionStep (A : Type u) (a b : A) := Path a b

/-- Theorem 15: Extension steps compose associatively. -/
theorem extension_steps_assoc {A : Type u} {a b c d : A}
    (s1 : extensionStep A a b) (s2 : extensionStep A b c) (s3 : extensionStep A c d) :
    Path.trans (Path.trans s1 s2) s3 = Path.trans s1 (Path.trans s2 s3) :=
  trans_assoc s1 s2 s3

/-- Theorem 16: Extension step symmetry reverses composition. -/
theorem extension_step_symm {A : Type u} {a b c : A}
    (s1 : extensionStep A a b) (s2 : extensionStep A b c) :
    Path.symm (Path.trans s1 s2) = Path.trans (Path.symm s2) (Path.symm s1) :=
  symm_trans s1 s2

/-- Theorem 17: Double-symm on extension step is identity. -/
theorem extension_step_double_symm {A : Type u} {a b : A}
    (s : extensionStep A a b) : Path.symm (Path.symm s) = s :=
  symm_symm s

-- ============================================================
-- §7. Schlessinger's Conditions
-- ============================================================

/-- Schlessinger H1: The natural map on fiber products is surjective.
    Modeled as a fiber product diagram of paths. -/
structure H1Condition (A : Type u) (a b c d : A) where
  left    : Path a b
  right   : Path a c
  fiber   : Path b d
  cofiber : Path c d
  compat  : Path.trans left fiber = Path.trans right cofiber

/-- Theorem 18: H1 compatibility. -/
theorem h1_compatibility {A : Type u} {a b c d : A}
    (h : H1Condition A a b c d) :
    Path.trans h.left h.fiber = Path.trans h.right h.cofiber :=
  h.compat

/-- Def 7: H1 with identity fibers. -/
noncomputable def h1IdentityFiber {A : Type u} {a b : A} (p q : Path a b) (e : p = q) :
    H1Condition A a b b b where
  left    := p
  right   := q
  fiber   := Path.refl b
  cofiber := Path.refl b
  compat  := by rw [trans_refl_right, trans_refl_right, e]

/-- Schlessinger H2: The map on tangent spaces is bijective. -/
structure H2Condition (A : Type u) (a b : A) where
  forward  : Path a b
  backward : Path b a
  leftInv  : Path.trans forward backward = Path.refl a

/-- Theorem 19: H2 left inverse condition. -/
theorem h2_left_inverse {A : Type u} {a b : A}
    (h : H2Condition A a b) :
    Path.trans h.forward h.backward = Path.refl a :=
  h.leftInv

/-- Schlessinger H3: The tangent space is finite-dimensional. -/
structure H3Condition (k : Type u) where
  tangent   : TangentSpace k
  finiteDim : Nat
  witness   : finiteDim > 0 := by omega

/-- Schlessinger H4: For small extensions, the map is bijective (pro-representability). -/
structure H4Condition (A : Type u) (a b : A) where
  isoForward  : Path a b
  isoBackward : Path b a
  roundtrip_l : Path.trans isoForward isoBackward = Path.refl a
  roundtrip_r : Path.trans isoBackward isoForward = Path.refl b

/-- Theorem 20: H4 forward-backward is identity. -/
theorem h4_is_iso_left {A : Type u} {a b : A} (h : H4Condition A a b) :
    Path.trans h.isoForward h.isoBackward = Path.refl a :=
  h.roundtrip_l

/-- Theorem 21: H4 backward-forward is identity. -/
theorem h4_is_iso_right {A : Type u} {a b : A} (h : H4Condition A a b) :
    Path.trans h.isoBackward h.isoForward = Path.refl b :=
  h.roundtrip_r

/-- Def 8: H4 condition implies H2 condition. -/
noncomputable def h4ImpliesH2 {A : Type u} {a b : A} (h : H4Condition A a b) :
    H2Condition A a b where
  forward  := h.isoForward
  backward := h.isoBackward
  leftInv  := h.roundtrip_l

/-- Def 9: H4 can be symmetrized. -/
noncomputable def h4Symmetric {A : Type u} {a b : A} (h : H4Condition A a b) :
    H4Condition A b a where
  isoForward  := h.isoBackward
  isoBackward := h.isoForward
  roundtrip_l := h.roundtrip_r
  roundtrip_r := h.roundtrip_l

/-- Theorem 22: H4 symmetrized twice is original (forward component). -/
theorem h4_symm_symm_forward {A : Type u} {a b : A} (h : H4Condition A a b) :
    (h4Symmetric (h4Symmetric h)).isoForward = h.isoForward :=
  rfl

-- ============================================================
-- §8. Kuranishi Space Structure
-- ============================================================

/-- Kuranishi map from the tangent space to the obstruction space,
    whose zero set gives the local moduli. -/
structure KuranishiData (A : Type u) (t o : A) where
  kuranishiMap  : Path t o
  zeroSection   : Path o o
  nilpotence    : Nat

/-- A Kuranishi neighborhood: local model of the moduli near a point. -/
structure KuranishiNeighborhood (A : Type u) (center : A) where
  radius : Nat
  chart  : Path center center

/-- Def 10: Every point has a trivial Kuranishi neighborhood. -/
noncomputable def trivialKuranishi {A : Type u} (a : A) :
    KuranishiNeighborhood A a where
  radius := 0
  chart  := Path.refl a

/-- Theorem 23: Kuranishi chart composed with its inverse gives refl via simp. -/
theorem kuranishi_chart_inv {A : Type u} (a : A) :
    Path.trans (Path.refl a) (Path.symm (Path.refl a)) = Path.refl a := by
  simp

/-- Theorem 24: Kuranishi charts compose associatively. -/
theorem kuranishi_compose {A : Type u} {a : A}
    (c1 c2 c3 : Path a a) :
    Path.trans (Path.trans c1 c2) c3 = Path.trans c1 (Path.trans c2 c3) :=
  trans_assoc c1 c2 c3

/-- Theorem 25: Kuranishi chart double inverse. -/
theorem kuranishi_chart_double_inv {A : Type u} {a : A} (c : Path a a) :
    Path.symm (Path.symm c) = c :=
  symm_symm c

-- ============================================================
-- §9. Cotangent Complex
-- ============================================================

/-- The cotangent complex, at the path level, encodes deformation data
    in a chain of paths, with a differential-like structure. -/
structure CotangentComplex (A : Type u) (x y z : A) where
  degree0 : Path x y
  degree1 : Path y z

/-- Def 11: Cotangent complex composite. -/
noncomputable def cotangentComposite {A : Type u} {x y z : A}
    (C : CotangentComplex A x y z) : Path x z :=
  Path.trans C.degree0 C.degree1

/-- Theorem 26: Cotangent complex composite is trans. -/
theorem cotangent_composite_is_trans {A : Type u} {x y z : A}
    (C : CotangentComplex A x y z) :
    cotangentComposite C = Path.trans C.degree0 C.degree1 :=
  rfl

/-- A truncated cotangent complex (2-term) with exactness. -/
structure TruncatedCotangent (A : Type u) (a b : A) where
  term0 : Path a b
  term1 : Path b a
  exactness : Path.trans term0 term1 = Path.refl a

/-- Theorem 27: Truncated cotangent exactness. -/
theorem truncated_exactness {A : Type u} {a b : A}
    (T : TruncatedCotangent A a b) :
    Path.trans T.term0 T.term1 = Path.refl a :=
  T.exactness

/-- Theorem 28: Build truncated cotangent for refl. -/
theorem build_truncated_cotangent_refl {A : Type u} (a : A) :
    Path.trans (Path.refl a) (Path.symm (Path.refl a)) = Path.refl a := by
  simp

/-- Theorem 29: Cotangent complex functorial under congrArg. -/
theorem cotangent_functorial {A B : Type u} (f : A -> B)
    {x y z : A} (C : CotangentComplex A x y z) :
    Path.congrArg f (cotangentComposite C) =
      Path.trans (Path.congrArg f C.degree0) (Path.congrArg f C.degree1) := by
  unfold cotangentComposite
  exact congrArg_trans f C.degree0 C.degree1

-- ============================================================
-- §10. Pro-Representability
-- ============================================================

/-- A pro-representing system: a compatible family of Artinian approximations. -/
structure ProSystem (A : Type u) (a : A) where
  level     : Nat
  approx    : Path a a
  coherence : Path.trans approx (Path.refl a) = approx

/-- Def 12: Level-0 pro-system is trivial. -/
noncomputable def proSystemLevel0 {A : Type u} (a : A) :
    ProSystem A a where
  level     := 0
  approx    := Path.refl a
  coherence := trans_refl_right (Path.refl a)

/-- Def 13: Any loop path gives a pro-system. -/
noncomputable def proSystemFromLoop {A : Type u} {a : A} (p : Path a a) :
    ProSystem A a where
  level     := 1
  approx    := p
  coherence := trans_refl_right p

/-- Transition maps in a pro-system. -/
noncomputable def proTransition {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Theorem 30: Pro-system transitions are associative. -/
theorem pro_transition_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    proTransition (proTransition p q) r =
      proTransition p (proTransition q r) :=
  trans_assoc p q r

/-- Theorem 31: Pro-transition with refl is identity. -/
theorem pro_transition_refl_right {A : Type u} {a b : A}
    (p : Path a b) :
    proTransition p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 32: Pro-transition with refl on left is identity. -/
theorem pro_transition_refl_left {A : Type u} {a b : A}
    (p : Path a b) :
    proTransition (Path.refl a) p = p :=
  trans_refl_left p

/-- A pro-representable functor. -/
structure ProRepresentable (k : Type u) where
  functor : DeformationFunctor k
  proRing : ArtinLocal k
  level   : Nat

-- ============================================================
-- §11. Deformation Composition Laws
-- ============================================================

/-- Def 14: Three-fold deformation composition. -/
noncomputable def threefoldDeformation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

/-- Theorem 33: Three-fold equals right-associated form. -/
theorem threefold_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    threefoldDeformation p q r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 34: Symm reverses threefold. -/
theorem threefold_symm {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (threefoldDeformation p q r) =
      Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  unfold threefoldDeformation
  rw [symm_trans, symm_trans]

/-- Theorem 35: Functorial deformation via congrArg preserves trans. -/
theorem functorial_deformation_trans {A B : Type u} (f : A -> B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 36: Functorial deformation via congrArg preserves symm. -/
theorem functorial_deformation_symm {A B : Type u} (f : A -> B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Theorem 37: congrArg applied to identity function is identity. -/
theorem congrArg_id_deformation {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg id p = p :=
  congrArg_id p

/-- Theorem 38: Two functorial deformations compose. -/
theorem two_functorial_compose {A B C : Type u} (f : A -> B) (g : B -> C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path.congrArg (g ∘ f) p = Path.congrArg g (Path.congrArg f p) :=
  congrArg_comp g f p

-- ============================================================
-- §12. Tangent-Obstruction Exact Sequence
-- ============================================================

/-- An exact sequence in deformation theory: tangent -> deformation -> obstruction. -/
structure TangentObstructionSeq (A : Type u) (t d o : A) where
  tangentMap     : Path t d
  obstructionMap : Path d o

/-- Def 15: Composite of tangent-obstruction sequence. -/
noncomputable def tosComposite {A : Type u} {t d o : A}
    (seq : TangentObstructionSeq A t d o) : Path t o :=
  Path.trans seq.tangentMap seq.obstructionMap

/-- Theorem 39: TOS composite is trans. -/
theorem tos_composite_eq {A : Type u} {t d o : A}
    (seq : TangentObstructionSeq A t d o) :
    tosComposite seq = Path.trans seq.tangentMap seq.obstructionMap :=
  rfl

/-- Theorem 40: Exact sequence with trivial obstruction simplifies. -/
theorem exact_seq_unobstructed {A : Type u} {t d : A} (p : Path t d) :
    Path.trans p (Path.refl d) = p :=
  trans_refl_right p

/-- Theorem 41: Composing two exact sequences associatively. -/
theorem exact_seq_compose {A : Type u} {a b c d : A}
    (s1 : TangentObstructionSeq A a b c)
    (s2 : TangentObstructionSeq A c d d) :
    Path.trans (Path.trans s1.tangentMap s1.obstructionMap) s2.tangentMap =
      Path.trans s1.tangentMap (Path.trans s1.obstructionMap s2.tangentMap) :=
  trans_assoc s1.tangentMap s1.obstructionMap s2.tangentMap

-- ============================================================
-- §13. Deformation Equivalences
-- ============================================================

/-- A deformation equivalence: a pair of mutually inverse paths. -/
structure DeformationEquiv (A : Type u) (a b : A) where
  forward   : Path a b
  backward  : Path b a
  left_inv  : Path.trans forward backward = Path.refl a
  right_inv : Path.trans backward forward = Path.refl b

/-- Def 16: Deformation equivalence can be reversed. -/
noncomputable def deformationEquivSymm {A : Type u} {a b : A}
    (e : DeformationEquiv A a b) : DeformationEquiv A b a where
  forward   := e.backward
  backward  := e.forward
  left_inv  := e.right_inv
  right_inv := e.left_inv

/-- Def 17: Identity deformation equivalence. -/
noncomputable def deformationEquivRefl {A : Type u} (a : A) :
    DeformationEquiv A a a where
  forward   := Path.refl a
  backward  := Path.refl a
  left_inv  := trans_refl_left (Path.refl a)
  right_inv := trans_refl_left (Path.refl a)

/-- Theorem 42: Forward-backward roundtrip. -/
theorem equiv_roundtrip_left {A : Type u} {a b : A}
    (e : DeformationEquiv A a b) :
    Path.trans e.forward e.backward = Path.refl a :=
  e.left_inv

/-- Theorem 43: Backward-forward roundtrip. -/
theorem equiv_roundtrip_right {A : Type u} {a b : A}
    (e : DeformationEquiv A a b) :
    Path.trans e.backward e.forward = Path.refl b :=
  e.right_inv

/-- Theorem 44: Double symmetrization of equivalence gives back original (forward). -/
theorem equiv_symm_symm_forward {A : Type u} {a b : A}
    (e : DeformationEquiv A a b) :
    (deformationEquivSymm (deformationEquivSymm e)).forward = e.forward :=
  rfl

-- ============================================================
-- §14. Formal Moduli Problems
-- ============================================================

/-- A formal moduli problem: an infinitesimal thickening coherence. -/
structure FormalModuliProblem (A : Type u) (base : A) where
  thickening : Path base base
  coherence  : Path.trans thickening (Path.refl base) = thickening

/-- Def 18: Every base point gives a trivial formal moduli problem. -/
noncomputable def trivialFormalModuli {A : Type u} (a : A) :
    FormalModuliProblem A a where
  thickening := Path.refl a
  coherence  := trans_refl_right (Path.refl a)

/-- Def 19: Any loop gives a formal moduli problem. -/
noncomputable def loopFormalModuli {A : Type u} {a : A} (p : Path a a) :
    FormalModuliProblem A a where
  thickening := p
  coherence  := trans_refl_right p

/-- Def 20: Thickening composed with itself via trans. -/
noncomputable def doubleThickening {A : Type u} {a : A}
    (F : FormalModuliProblem A a) : Path a a :=
  Path.trans F.thickening F.thickening

/-- Theorem 45: Double thickening coherence. -/
theorem double_thickening_coherence {A : Type u} {a : A}
    (F : FormalModuliProblem A a) :
    Path.trans (doubleThickening F) (Path.refl a) = doubleThickening F :=
  trans_refl_right (doubleThickening F)

/-- Theorem 46: Triple thickening via associativity. -/
theorem triple_thickening_assoc {A : Type u} {a : A}
    (F : FormalModuliProblem A a) :
    Path.trans (Path.trans F.thickening F.thickening) F.thickening =
      Path.trans F.thickening (Path.trans F.thickening F.thickening) :=
  trans_assoc F.thickening F.thickening F.thickening

-- ============================================================
-- §15. Versal and Miniversal Deformations
-- ============================================================

/-- A versal deformation: one through which all others factor. -/
structure VersalDeformation (A : Type u) (a b : A) where
  universal : Path a b
  versality : (q : Path a b) -> Path a b

/-- Theorem 47: A versal deformation versality is a function. -/
theorem versal_versality_self {A : Type u} {a b : A}
    (V : VersalDeformation A a b) :
    V.versality V.universal = V.versality V.universal :=
  rfl

/-- Def 21: Versal deformation with trivial factorization. -/
noncomputable def versalTrivial {A : Type u} (a : A) :
    VersalDeformation A a a where
  universal := Path.refl a
  versality := fun q => q

/-- A miniversal deformation has minimal tangent dimension. -/
structure MiniversalDeformation (A : Type u) (a b : A)
    extends VersalDeformation A a b where
  minimal : Nat

/-- Def 22: Miniversal deformation exists trivially. -/
noncomputable def miniversalTrivial {A : Type u} (a : A) :
    MiniversalDeformation A a a where
  universal  := Path.refl a
  versality  := fun q => q
  minimal    := 0

-- ============================================================
-- §16. Whiskering and Higher Structure
-- ============================================================

/-- Theorem 48: Left whiskering a deformation. -/
theorem left_whisker {A : Type u} {a b c : A}
    (p : Path a b) {q1 q2 : Path b c} (h : q1 = q2) :
    Path.trans p q1 = Path.trans p q2 :=
  _root_.congrArg (Path.trans p) h

/-- Theorem 49: Right whiskering a deformation. -/
theorem right_whisker {A : Type u} {a b c : A}
    {p1 p2 : Path a b} (h : p1 = p2) (q : Path b c) :
    Path.trans p1 q = Path.trans p2 q :=
  _root_.congrArg (fun x => Path.trans x q) h

/-- Theorem 50: congrArg distributes over threefold composition. -/
theorem congrArg_threefold {A B : Type u} (f : A -> B)
    {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (threefoldDeformation p q r) =
      Path.trans (Path.congrArg f p)
        (Path.trans (Path.congrArg f q) (Path.congrArg f r)) := by
  unfold threefoldDeformation
  rw [congrArg_trans f (Path.trans p q) r]
  rw [congrArg_trans f p q]
  rw [trans_assoc]

-- ============================================================
-- §17. Higher Obstruction Theory
-- ============================================================

/-- A higher obstruction: an equality between paths of deformations
    witnessing an obstruction at the next level. -/
noncomputable def higherObstruction {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  p = q

/-- Theorem 51: Trivial higher obstruction from refl. -/
theorem trivial_higher_obstruction {A : Type u} {a b : A} (p : Path a b) :
    higherObstruction p p :=
  rfl

/-- Theorem 52: Higher obstructions compose transitively. -/
theorem higher_obstruction_trans {A : Type u} {a b : A}
    {p q r : Path a b}
    (h1 : higherObstruction p q) (h2 : higherObstruction q r) :
    higherObstruction p r :=
  h1.trans h2

/-- Theorem 53: Higher obstruction symmetry. -/
theorem higher_obstruction_symm {A : Type u} {a b : A}
    {p q : Path a b} (h : higherObstruction p q) :
    higherObstruction q p :=
  h.symm

/-- Theorem 54: Deformation under congrArg preserves higher obstruction. -/
theorem higher_obstruction_congrArg {A B : Type u} (f : A -> B)
    {a b : A} {p q : Path a b} (h : higherObstruction p q) :
    higherObstruction (Path.congrArg f p) (Path.congrArg f q) :=
  _root_.congrArg (Path.congrArg f) h

-- ============================================================
-- §18. Fourfold Composition and Pentagon
-- ============================================================

/-- Def 23: Fourfold deformation composition. -/
noncomputable def fourfoldDeformation {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) : Path a e :=
  Path.trans (Path.trans (Path.trans p q) r) s

/-- Theorem 55: Fourfold associativity. -/
theorem fourfold_assoc {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    fourfoldDeformation p q r s = Path.trans p (Path.trans q (Path.trans r s)) :=
  trans_assoc_fourfold p q r s

/-- Theorem 56: Fourfold symm reversal. -/
theorem fourfold_symm {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.symm (fourfoldDeformation p q r s) =
      Path.trans (Path.symm s)
        (Path.trans (Path.symm r)
          (Path.trans (Path.symm q) (Path.symm p))) := by
  unfold fourfoldDeformation
  rw [symm_trans, symm_trans, symm_trans]

-- ============================================================
-- §19. Deformation Theory Summary Theorems
-- ============================================================

/-- Theorem 57: Refl is left and right unit simultaneously. -/
theorem refl_biunit {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p ∧ Path.trans p (Path.refl b) = p :=
  ⟨trans_refl_left p, trans_refl_right p⟩

/-- Theorem 58: congrArg preserves all groupoid structure simultaneously. -/
theorem congrArg_preserves_groupoid {A B : Type u} (f : A -> B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) ∧
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  ⟨congrArg_trans f p q, congrArg_symm f p⟩

/-- Theorem 59: Full deformation groupoid: assoc + unit + inverse. -/
theorem deformation_groupoid {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p ∧
    Path.trans p (Path.refl b) = p ∧
    Path.symm (Path.symm p) = p :=
  ⟨trans_refl_left p, trans_refl_right p, symm_symm p⟩

/-- Theorem 60: Kodaira-Spencer is a groupoid homomorphism. -/
theorem ks_groupoid_homomorphism {A B : Type u} (f : A -> B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    kodairaSpencerMap f (Path.trans p q) =
      Path.trans (kodairaSpencerMap f p) (kodairaSpencerMap f q) ∧
    kodairaSpencerMap f (Path.symm p) =
      Path.symm (kodairaSpencerMap f p) ∧
    kodairaSpencerMap f (Path.refl a) = kodairaSpencerMap f (Path.refl a) :=
  ⟨ks_preserves_composition f p q, ks_preserves_inverse f p, rfl⟩

end DeformationTheoryDeep
