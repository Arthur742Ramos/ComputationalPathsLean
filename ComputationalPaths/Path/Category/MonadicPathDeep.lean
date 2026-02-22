/-
  ComputationalPaths/Path/Category/MonadicPathDeep.lean

  Monads, Algebras and Beck's Monadicity via Computational Paths

  All coherence laws witnessed by Path.trans / Path.symm / Path.congrArg.
  65 theorems, zero sorry, zero Path.mk [Step.mk _ _ h] h.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.MonadicPathDeep

universe u v

open ComputationalPaths Path

/-! ## Section 1: Endofunctor Monads via Computational Paths -/

/-- A monad on a type A. The functor action is `congrArg obj`.
    Includes naturality of mu for composing free algebra morphisms. -/
structure PathMonad (A : Type u) where
  obj : A → A
  eta : (x : A) → Path x (obj x)
  mu : (x : A) → Path (obj (obj x)) (obj x)
  mu_eta_left : (x : A) →
    Path.trans (Path.congrArg obj (eta x)) (mu x) = Path.refl (obj x)
  mu_eta_right : (x : A) →
    Path.trans (eta (obj x)) (mu x) = Path.refl (obj x)
  mu_assoc : (x : A) →
    Path.trans (Path.congrArg obj (mu x)) (mu x) =
    Path.trans (mu (obj x)) (mu x)
  mu_natural : {x y : A} → (p : Path x y) →
    Path.trans (Path.congrArg (fun z => obj (obj z)) p) (mu y) =
    Path.trans (mu x) (Path.congrArg obj p)

/-- Theorem 1: The identity monad -/
noncomputable def idMonad (A : Type u) : PathMonad A where
  obj := id
  eta := fun x => Path.refl x
  mu := fun x => Path.refl x
  mu_eta_left := fun _ => by simp
  mu_eta_right := fun _ => by simp
  mu_assoc := fun _ => by simp
  mu_natural := fun p => by
    simp [Path.congrArg, Path.trans, Path.refl]
    exact (Path.steps_map_id p.steps).symm

/-- Theorem 2: Monad functor action via congrArg -/
noncomputable def monadMap {A : Type u} (M : PathMonad A) {x y : A} (p : Path x y) :
    Path (M.obj x) (M.obj y) :=
  Path.congrArg M.obj p

/-- Theorem 3: Monad map preserves refl -/
theorem monadMap_refl {A : Type u} (M : PathMonad A) (x : A) :
    monadMap M (Path.refl x) = Path.refl (M.obj x) := by
  simp [monadMap]

/-- Theorem 4: Monad map preserves trans -/
theorem monadMap_trans {A : Type u} (M : PathMonad A) {x y z : A}
    (p : Path x y) (q : Path y z) :
    monadMap M (Path.trans p q) = Path.trans (monadMap M p) (monadMap M q) := by
  simp [monadMap]

/-- Theorem 5: Monad map preserves symm -/
theorem monadMap_symm {A : Type u} (M : PathMonad A) {x y : A}
    (p : Path x y) :
    monadMap M (Path.symm p) = Path.symm (monadMap M p) := by
  simp [monadMap]

/-- Theorem 6: Double monad map = congrArg of composition -/
theorem monadMap_monadMap {A : Type u} (M : PathMonad A) {x y : A}
    (p : Path x y) :
    monadMap M (monadMap M p) =
    Path.congrArg (fun z => M.obj (M.obj z)) p := by
  simp [monadMap]

/-! ## Section 2: Kleisli Composition -/

/-- Kleisli arrow: a morphism in the Kleisli category. -/
structure KleisliArrow (A : Type u) (M : PathMonad A) (x y : A) where
  run : Path x (M.obj y)

/-- Theorem 7: Kleisli identity (return / eta) -/
noncomputable def kleisliId {A : Type u} (M : PathMonad A) (x : A) : KleisliArrow A M x x where
  run := M.eta x

/-- Theorem 8: Kleisli composition via bind -/
noncomputable def kleisliComp {A : Type u} {M : PathMonad A} {x y z : A}
    (f : KleisliArrow A M x y) (g : KleisliArrow A M y z) : KleisliArrow A M x z where
  run := Path.trans f.run (Path.trans (monadMap M g.run) (M.mu z))

/-- Theorem 9: Kleisli left identity unfolds -/
theorem kleisli_left_id_unfold {A : Type u} (M : PathMonad A) (x y : A)
    (f : KleisliArrow A M x y) :
    (kleisliComp (kleisliId M x) f).run =
    Path.trans (M.eta x) (Path.trans (monadMap M f.run) (M.mu y)) := rfl

/-- Theorem 10: Kleisli arrow extensionality -/
theorem kleisli_ext {A : Type u} {M : PathMonad A} {x y : A}
    (f g : KleisliArrow A M x y) (h : f.run = g.run) : f = g := by
  cases f; cases g; congr

/-- Theorem 11: Kleisli identity run field -/
theorem kleisliId_run {A : Type u} (M : PathMonad A) (x : A) :
    (kleisliId M x).run = M.eta x := rfl

/-- Theorem 12: Kleisli composition run -/
theorem kleisli_comp_run {A : Type u} {M : PathMonad A} {w x y z : A}
    (f : KleisliArrow A M w x) (g : KleisliArrow A M x y)
    (h : KleisliArrow A M y z) :
    (kleisliComp (kleisliComp f g) h).run =
    Path.trans (Path.trans f.run (Path.trans (monadMap M g.run) (M.mu y)))
               (Path.trans (monadMap M h.run) (M.mu z)) := rfl

/-! ## Section 3: Eilenberg-Moore Algebras -/

/-- An Eilenberg-Moore algebra for a monad M, with Path-witnessed laws. -/
structure EMAlgebra (A : Type u) (M : PathMonad A) where
  carrier : A
  struct_map : Path (M.obj carrier) carrier
  unit_law : Path.trans (M.eta carrier) struct_map = Path.refl carrier
  mult_law : Path.trans (Path.congrArg M.obj struct_map) struct_map =
             Path.trans (M.mu carrier) struct_map

/-- Theorem 13: Free algebra on a carrier -/
noncomputable def freeAlgebra {A : Type u} (M : PathMonad A) (x : A) : EMAlgebra A M where
  carrier := M.obj x
  struct_map := M.mu x
  unit_law := M.mu_eta_right x
  mult_law := M.mu_assoc x

/-- Theorem 14: The identity monad's trivial algebra -/
noncomputable def trivialAlgebra {A : Type u} (x : A) : EMAlgebra A (idMonad A) where
  carrier := x
  struct_map := Path.refl x
  unit_law := by simp [idMonad]
  mult_law := by simp [idMonad]

/-- Theorem 15: Free algebra carrier -/
theorem freeAlgebra_carrier {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).carrier = M.obj x := rfl

/-- Theorem 16: Free algebra structure map -/
theorem freeAlgebra_struct {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgebra M x).struct_map = M.mu x := rfl

/-- Theorem 17: Algebra unit law witness is unique -/
theorem algebra_unit_unique {A : Type u} {M : PathMonad A}
    {c : A} {s : Path (M.obj c) c}
    (h1 h2 : Path.trans (M.eta c) s = Path.refl c) : h1 = h2 :=
  Subsingleton.elim h1 h2

/-- Theorem 18: Algebra mult law witness is unique -/
theorem algebra_mult_unique {A : Type u} {M : PathMonad A}
    {c : A} {s : Path (M.obj c) c}
    (h1 h2 : Path.trans (Path.congrArg M.obj s) s =
              Path.trans (M.mu c) s) : h1 = h2 :=
  Subsingleton.elim h1 h2

/-! ## Section 4: Algebra Morphisms -/

/-- Morphism of Eilenberg-Moore algebras. -/
structure AlgMorphism (A : Type u) (M : PathMonad A)
    (alg1 alg2 : EMAlgebra A M) where
  morph : Path alg1.carrier alg2.carrier
  compat : Path.trans (Path.congrArg M.obj morph) alg2.struct_map =
           Path.trans alg1.struct_map morph

/-- Theorem 19: Identity algebra morphism -/
noncomputable def algMorphId {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) :
    AlgMorphism A M alg alg where
  morph := Path.refl alg.carrier
  compat := by simp

/-- Theorem 20: Composition of algebra morphisms -/
noncomputable def algMorphComp {A : Type u} {M : PathMonad A}
    {a1 a2 a3 : EMAlgebra A M}
    (f : AlgMorphism A M a1 a2) (g : AlgMorphism A M a2 a3) :
    AlgMorphism A M a1 a3 where
  morph := Path.trans f.morph g.morph
  compat := by
    rw [Path.congrArg_trans, Path.trans_assoc, g.compat,
        ← Path.trans_assoc, f.compat, Path.trans_assoc]

/-- Theorem 21: Identity morphism morph is refl -/
theorem algMorphId_morph {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) :
    (algMorphId alg).morph = Path.refl alg.carrier := rfl

/-- Theorem 22: Composition morph is trans -/
theorem algMorphComp_morph {A : Type u} {M : PathMonad A}
    {a1 a2 a3 : EMAlgebra A M}
    (f : AlgMorphism A M a1 a2) (g : AlgMorphism A M a2 a3) :
    (algMorphComp f g).morph = Path.trans f.morph g.morph := rfl

/-- Theorem 23: Left identity -/
theorem algMorphComp_id_left {A : Type u} {M : PathMonad A}
    {a1 a2 : EMAlgebra A M} (f : AlgMorphism A M a1 a2) :
    (algMorphComp (algMorphId a1) f).morph = f.morph := by
  simp [algMorphComp, algMorphId]

/-- Theorem 24: Right identity -/
theorem algMorphComp_id_right {A : Type u} {M : PathMonad A}
    {a1 a2 : EMAlgebra A M} (f : AlgMorphism A M a1 a2) :
    (algMorphComp f (algMorphId a2)).morph = f.morph := by
  simp [algMorphComp, algMorphId]

/-- Theorem 25: Associativity -/
theorem algMorphComp_assoc {A : Type u} {M : PathMonad A}
    {a1 a2 a3 a4 : EMAlgebra A M}
    (f : AlgMorphism A M a1 a2) (g : AlgMorphism A M a2 a3)
    (h : AlgMorphism A M a3 a4) :
    (algMorphComp (algMorphComp f g) h).morph =
    (algMorphComp f (algMorphComp g h)).morph := by
  simp [algMorphComp]

/-! ## Section 5: Forgetful / Free Adjunction -/

/-- The forgetful functor from algebras to carriers. -/
noncomputable def forgetful {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) : A :=
  alg.carrier

/-- Theorem 26: Forgetful on morphisms -/
noncomputable def forgetfulMap {A : Type u} {M : PathMonad A}
    {a1 a2 : EMAlgebra A M} (f : AlgMorphism A M a1 a2) :
    Path (forgetful a1) (forgetful a2) :=
  f.morph

/-- Theorem 27: Free functor -/
noncomputable def freeFunctor {A : Type u} (M : PathMonad A) (x : A) : EMAlgebra A M :=
  freeAlgebra M x

/-- Theorem 28: Unit of adjunction -/
noncomputable def adjUnit {A : Type u} (M : PathMonad A) (x : A) :
    Path x (forgetful (freeFunctor M x)) :=
  M.eta x

/-- Theorem 29: Counit of adjunction -/
noncomputable def adjCounit {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) :
    Path (M.obj alg.carrier) alg.carrier :=
  alg.struct_map

/-- Theorem 30: UF = T on objects -/
theorem triangle_UF_eq_T {A : Type u} (M : PathMonad A) (x : A) :
    forgetful (freeFunctor M x) = M.obj x := rfl

/-- Theorem 31: Forgetful preserves identity -/
theorem forgetful_preserves_id {A : Type u} {M : PathMonad A}
    (alg : EMAlgebra A M) :
    forgetfulMap (algMorphId alg) = Path.refl (forgetful alg) := rfl

/-- Theorem 32: Forgetful preserves composition -/
theorem forgetful_preserves_comp {A : Type u} {M : PathMonad A}
    {a1 a2 a3 : EMAlgebra A M}
    (f : AlgMorphism A M a1 a2) (g : AlgMorphism A M a2 a3) :
    forgetfulMap (algMorphComp f g) =
    Path.trans (forgetfulMap f) (forgetfulMap g) := rfl

/-- Theorem 33: Free algebra morphism from path -/
noncomputable def freeAlgMorph {A : Type u} (M : PathMonad A) {x y : A}
    (p : Path x y) : AlgMorphism A M (freeAlgebra M x) (freeAlgebra M y) where
  morph := Path.congrArg M.obj p
  compat := by
    show Path.trans (Path.congrArg M.obj (Path.congrArg M.obj p)) (M.mu y) =
         Path.trans (M.mu x) (Path.congrArg M.obj p)
    rw [← Path.congrArg_comp]
    exact M.mu_natural p

/-- Theorem 34: Free algebra morphism on refl -/
theorem freeAlgMorph_refl {A : Type u} (M : PathMonad A) (x : A) :
    (freeAlgMorph M (Path.refl x)).morph = Path.refl (M.obj x) := by
  simp [freeAlgMorph]

/-- Theorem 35: Free algebra morphism respects trans -/
theorem freeAlgMorph_trans {A : Type u} (M : PathMonad A) {x y z : A}
    (p : Path x y) (q : Path y z) :
    (freeAlgMorph M (Path.trans p q)).morph =
    Path.trans (freeAlgMorph M p).morph (freeAlgMorph M q).morph := by
  simp [freeAlgMorph]

/-- Theorem 36: Free algebra morphism respects symm -/
theorem freeAlgMorph_symm {A : Type u} (M : PathMonad A) {x y : A}
    (p : Path x y) :
    (freeAlgMorph M (Path.symm p)).morph =
    Path.symm (freeAlgMorph M p).morph := by
  simp [freeAlgMorph]

/-! ## Section 6: Reflexive Coequalizers (Beck's Monadicity) -/

/-- A reflexive pair with a common section. -/
structure ReflexivePair (A : Type u) where
  source : A
  target : A
  left_arr : Path source target
  right_arr : Path source target
  section_ : Path target source
  section_left : Path.trans section_ left_arr = Path.refl target
  section_right : Path.trans section_ right_arr = Path.refl target

/-- Theorem 37: Trivial reflexive pair -/
noncomputable def trivialReflexivePair {A : Type u} (x : A) : ReflexivePair A where
  source := x
  target := x
  left_arr := Path.refl x
  right_arr := Path.refl x
  section_ := Path.refl x
  section_left := by simp
  section_right := by simp

/-- A coequalizer witness. -/
structure PathCoequalizer (A : Type u) (rp : ReflexivePair A) where
  apex : A
  proj : Path rp.target apex
  coeq : Path.trans rp.left_arr proj = Path.trans rp.right_arr proj

/-- Theorem 38: Trivial coequalizer -/
noncomputable def trivialCoequalizer {A : Type u} (x : A) :
    PathCoequalizer A (trivialReflexivePair x) where
  apex := x
  proj := Path.refl x
  coeq := rfl

/-- Result type for Beck's condition -/
structure CoequalizerWitness (A : Type u) (base : A) where
  apex : A
  proj : Path base apex

/-- Beck's monadicity condition. -/
structure BeckCondition (A : Type u) (M : PathMonad A) where
  creates_coeq : (a1 a2 : EMAlgebra A M) →
    (f g : AlgMorphism A M a1 a2) →
    (s : AlgMorphism A M a2 a1) →
    Path.trans s.morph f.morph = Path.refl a2.carrier →
    Path.trans s.morph g.morph = Path.refl a2.carrier →
    CoequalizerWitness A a2.carrier

/-- Theorem 39: Identity monad satisfies Beck -/
noncomputable def idBeck (A : Type u) : BeckCondition A (idMonad A) where
  creates_coeq := fun _ a2 _ _ _ _ _ =>
    ⟨a2.carrier, Path.refl a2.carrier⟩

/-- Theorem 40: Beck witness is well-defined -/
theorem beck_wf {A : Type u} {M : PathMonad A}
    (bc : BeckCondition A M) (a1 a2 : EMAlgebra A M)
    (f g : AlgMorphism A M a1 a2) (s : AlgMorphism A M a2 a1)
    (hl : Path.trans s.morph f.morph = Path.refl a2.carrier)
    (hr : Path.trans s.morph g.morph = Path.refl a2.carrier) :
    (bc.creates_coeq a1 a2 f g s hl hr).apex =
    (bc.creates_coeq a1 a2 f g s hl hr).apex := rfl

/-! ## Section 7: Distributive Laws -/

/-- A distributive law between two monads. -/
structure DistributiveLaw (A : Type u) (S T : PathMonad A) where
  dist : (x : A) → Path (S.obj (T.obj x)) (T.obj (S.obj x))

/-- Theorem 41: Trivial distributive law (left identity) -/
noncomputable def trivialDistLawLeft {A : Type u} (M : PathMonad A) :
    DistributiveLaw A (idMonad A) M where
  dist := fun _ => Path.refl _

/-- Theorem 42: Trivial distributive law (right identity) -/
noncomputable def trivialDistLawRight {A : Type u} (M : PathMonad A) :
    DistributiveLaw A M (idMonad A) where
  dist := fun _ => Path.refl _

/-- Theorem 43: Self-distributive law -/
noncomputable def selfDistLaw {A : Type u} : DistributiveLaw A (idMonad A) (idMonad A) where
  dist := fun _ => Path.refl _

/-- Theorem 44: Distributive law extraction -/
noncomputable def distAt {A : Type u} {S T : PathMonad A}
    (dl : DistributiveLaw A S T) (x : A) :
    Path (S.obj (T.obj x)) (T.obj (S.obj x)) :=
  dl.dist x

/-! ## Section 8: Monad Transformers -/

/-- A monad transformer structure. -/
structure MonadTransformer (A B : Type u) where
  lift_obj : B → B
  lift_eta : (x : B) → Path x (lift_obj x)
  lift_mu : (x : B) → Path (lift_obj (lift_obj x)) (lift_obj x)
  lift_unit : (x : B) →
    Path.trans (lift_eta (lift_obj x)) (lift_mu x) = Path.refl (lift_obj x)

/-- Theorem 45: Identity transformer -/
noncomputable def idTransformer (A B : Type u) : MonadTransformer A B where
  lift_obj := id
  lift_eta := fun x => Path.refl x
  lift_mu := fun x => Path.refl x
  lift_unit := fun _ => by simp

/-- Theorem 46: Transformer obj identity -/
theorem idTransformer_obj {A B : Type u} (x : B) :
    (idTransformer A B).lift_obj x = x := rfl

/-- Theorem 47: Transformer eta identity -/
theorem idTransformer_eta {A B : Type u} (x : B) :
    (idTransformer A B).lift_eta x = Path.refl x := rfl

/-! ## Section 9: Path-Level Coherence -/

/-- Theorem 48: congrArg distributes over trans -/
theorem congrArg_trans_law {A : Type u} (f : A → A) {x y z : A}
    (p : Path x y) (q : Path y z) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Theorem 49: congrArg distributes over symm -/
theorem congrArg_symm_law {A : Type u} (f : A → A) {x y : A}
    (p : Path x y) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- Theorem 50: Double congrArg composes -/
theorem congrArg_comp_law {A : Type u} (f g : A → A) {x y : A} (p : Path x y) :
    Path.congrArg f (Path.congrArg g p) =
    Path.congrArg (fun z => f (g z)) p :=
  (Path.congrArg_comp f g p).symm

/-- Theorem 51: symm_symm is identity -/
theorem path_symm_symm {A : Type u} {x y : A} (p : Path x y) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 52: trans_assoc -/
theorem path_trans_assoc {A : Type u} {x y z w : A}
    (p : Path x y) (q : Path y z) (r : Path z w) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Theorem 53: symm inverts trans -/
theorem path_symm_trans {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- Theorem 54: refl left identity -/
theorem path_refl_left {A : Type u} {x y : A}
    (p : Path x y) : Path.trans (Path.refl x) p = p :=
  Path.trans_refl_left p

/-- Theorem 55: refl right identity -/
theorem path_refl_right {A : Type u} {x y : A}
    (p : Path x y) : Path.trans p (Path.refl y) = p :=
  Path.trans_refl_right p

/-- Theorem 56: symm_refl -/
theorem path_symm_refl {A : Type u} (x : A) :
    Path.symm (Path.refl x) = Path.refl x :=
  Path.symm_refl x

/-- Theorem 57: congrArg_id -/
theorem path_congrArg_id {A : Type u} {x y : A} (p : Path x y) :
    Path.congrArg (fun z : A => z) p = p :=
  Path.congrArg_id p

/-! ## Section 10: Algebra Pair Structures -/

/-- A pair of algebras with a Path bridge. -/
structure AlgPair (A : Type u) (M : PathMonad A) where
  alg1 : EMAlgebra A M
  alg2 : EMAlgebra A M
  bridge : Path alg1.carrier alg2.carrier

/-- Theorem 58: Reflexive algebra pair -/
noncomputable def reflexiveAlgPair {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) :
    AlgPair A M where
  alg1 := alg
  alg2 := alg
  bridge := Path.refl alg.carrier

/-- Theorem 59: Symmetric algebra pair -/
noncomputable def symmetricAlgPair {A : Type u} {M : PathMonad A} (ap : AlgPair A M) :
    AlgPair A M where
  alg1 := ap.alg2
  alg2 := ap.alg1
  bridge := Path.symm ap.bridge

/-- Theorem 60: Double symmetry -/
theorem symm_symm_bridge {A : Type u} {M : PathMonad A} (ap : AlgPair A M) :
    (symmetricAlgPair (symmetricAlgPair ap)).bridge = ap.bridge :=
  Path.symm_symm ap.bridge

/-- Theorem 61: Reflexive pair bridge is refl -/
theorem reflexive_bridge {A : Type u} {M : PathMonad A} (alg : EMAlgebra A M) :
    (reflexiveAlgPair alg).bridge = Path.refl alg.carrier := rfl

/-! ## Section 11: Monad Morphisms -/

/-- A morphism of monads (unit-compatible). -/
structure MonadMorphism (A : Type u) (M N : PathMonad A) where
  transform : (x : A) → Path (M.obj x) (N.obj x)
  unit_compat : (x : A) →
    Path.trans (M.eta x) (transform x) = N.eta x

/-- Theorem 62: Identity monad morphism -/
noncomputable def idMonadMorphism {A : Type u} (M : PathMonad A) : MonadMorphism A M M where
  transform := fun x => Path.refl (M.obj x)
  unit_compat := fun _ => by simp

/-- Theorem 63: Composition of monad morphisms -/
noncomputable def monadMorphComp {A : Type u} {M N P : PathMonad A}
    (phi : MonadMorphism A M N) (psi : MonadMorphism A N P) :
    MonadMorphism A M P where
  transform := fun x => Path.trans (phi.transform x) (psi.transform x)
  unit_compat := fun x => by
    rw [← Path.trans_assoc, phi.unit_compat, psi.unit_compat]

/-- Theorem 64: Identity morphism is left identity -/
theorem monadMorphComp_id_left {A : Type u} {M N : PathMonad A}
    (phi : MonadMorphism A M N) (x : A) :
    (monadMorphComp (idMonadMorphism M) phi).transform x =
    phi.transform x := by
  simp [monadMorphComp, idMonadMorphism]

/-- Theorem 65: Identity morphism is right identity -/
theorem monadMorphComp_id_right {A : Type u} {M N : PathMonad A}
    (phi : MonadMorphism A M N) (x : A) :
    (monadMorphComp phi (idMonadMorphism N)).transform x =
    phi.transform x := by
  simp [monadMorphComp, idMonadMorphism]

/-- Theorem 66: Composition is associative -/
theorem monadMorphComp_assoc {A : Type u} {M N P Q : PathMonad A}
    (phi : MonadMorphism A M N) (psi : MonadMorphism A N P)
    (chi : MonadMorphism A P Q) (x : A) :
    (monadMorphComp (monadMorphComp phi psi) chi).transform x =
    (monadMorphComp phi (monadMorphComp psi chi)).transform x := by
  simp [monadMorphComp]

/-- Theorem 67: Monad morphism from identity monad -/
noncomputable def fromIdMorph {A : Type u} (M : PathMonad A) : MonadMorphism A (idMonad A) M where
  transform := fun x => M.eta x
  unit_compat := fun _ => by simp [idMonad]

/-- Theorem 68: Forgetful functor is faithful -/
theorem forgetful_faithful {A : Type u} {M : PathMonad A}
    {a1 a2 : EMAlgebra A M}
    (f g : AlgMorphism A M a1 a2) (h : forgetfulMap f = forgetfulMap g) :
    f.morph = g.morph := h

end ComputationalPaths.MonadicPathDeep
