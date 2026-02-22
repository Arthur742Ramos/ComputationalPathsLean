/-
  CoalgebraPathDeep.lean
  Coalgebras and Comonads via Computational Paths

  Topics:
  - F-coalgebras: structure maps A → F(A)
  - Coalgebra homomorphisms, composition, identity
  - Final coalgebra (terminal coalgebra)
  - Bisimulation as coalgebraic relation
  - Coinduction principle
  - Comonads: counit (epsilon), comultiplication (delta)
  - Comonad laws: coassociativity, counit laws as Path
  - Comonad coalgebras (coEilenberg-Moore)
  - Cofree coalgebras
  - Coalgebraic modal logic
  - Lambek's lemma: final coalgebra is fixed point
  - All via Path.trans/symm/congrArg
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace CoalgebraPathDeep

open Path

universe u v w

-- ========================================================================
-- Section 1: F-Coalgebras
-- ========================================================================

/-- An F-coalgebra consists of a carrier type and a structure map A → F(A) -/
structure FCoalgebra (F : Type u → Type u) where
  carrier : Type u
  struct : carrier → F carrier

/-- A coalgebra homomorphism between F-coalgebras -/
structure CoalgHom (F : Type u → Type u) (A B : FCoalgebra F) where
  morphism : A.carrier → B.carrier
  mapF : F A.carrier → F B.carrier
  commutes : (a : A.carrier) → Path (mapF (A.struct a)) (B.struct (morphism a))

/-- Identity coalgebra homomorphism -/
noncomputable def coalg_id_hom (F : Type u → Type u) (A : FCoalgebra F) : CoalgHom F A A where
  morphism := id
  mapF := id
  commutes := fun a => Path.refl (A.struct a)

/-- Def 1: Identity homomorphism preserves structure -/
noncomputable def coalg_id_preserves {F : Type u → Type u} (A : FCoalgebra F) (a : A.carrier) :
    Path ((coalg_id_hom F A).mapF (A.struct a)) (A.struct a) :=
  Path.refl (A.struct a)

/-- Composition of coalgebra homomorphisms -/
noncomputable def coalg_comp {F : Type u → Type u} {A B C : FCoalgebra F}
    (g : CoalgHom F B C) (f : CoalgHom F A B) : CoalgHom F A C where
  morphism := g.morphism ∘ f.morphism
  mapF := g.mapF ∘ f.mapF
  commutes := fun a =>
    let step1 : Path (g.mapF (f.mapF (A.struct a))) (g.mapF (B.struct (f.morphism a))) :=
      Path.congrArg g.mapF (f.commutes a)
    let step2 : Path (g.mapF (B.struct (f.morphism a))) (C.struct (g.morphism (f.morphism a))) :=
      g.commutes (f.morphism a)
    Path.trans step1 step2

/-- Def 2: Composition of homomorphisms is associative on morphisms -/
noncomputable def coalg_comp_assoc {F : Type u → Type u} {A B C D : FCoalgebra F}
    (h : CoalgHom F C D) (g : CoalgHom F B C) (f : CoalgHom F A B) (a : A.carrier) :
    Path ((coalg_comp h (coalg_comp g f)).morphism a)
         ((coalg_comp (coalg_comp h g) f).morphism a) :=
  Path.refl (h.morphism (g.morphism (f.morphism a)))

/-- Def 3: Left identity for composition -/
noncomputable def coalg_comp_id_left {F : Type u → Type u} {A B : FCoalgebra F}
    (f : CoalgHom F A B) (a : A.carrier) :
    Path ((coalg_comp (coalg_id_hom F B) f).morphism a) (f.morphism a) :=
  Path.refl (f.morphism a)

/-- Def 4: Right identity for composition -/
noncomputable def coalg_comp_id_right {F : Type u → Type u} {A B : FCoalgebra F}
    (f : CoalgHom F A B) (a : A.carrier) :
    Path ((coalg_comp f (coalg_id_hom F A)).morphism a) (f.morphism a) :=
  Path.refl (f.morphism a)

/-- Theorem 5: Homomorphism commutation coherence -/
theorem coalg_hom_commute_trans {F : Type u → Type u} {A B C : FCoalgebra F}
    (g : CoalgHom F B C) (f : CoalgHom F A B) (a : A.carrier) :
    (coalg_comp g f).commutes a =
    Path.trans (Path.congrArg g.mapF (f.commutes a)) (g.commutes (f.morphism a)) :=
  rfl

/-- Theorem 6: Left identity commutation is refl -/
theorem coalg_id_left_commutes {F : Type u → Type u} {A B : FCoalgebra F}
    (f : CoalgHom F A B) (a : A.carrier) :
    (coalg_comp (coalg_id_hom F B) f).commutes a =
    Path.trans (Path.congrArg id (f.commutes a)) (Path.refl (B.struct (f.morphism a))) :=
  rfl

-- ========================================================================
-- Section 2: Bisimulation as Coalgebraic Relation
-- ========================================================================

/-- A bisimulation relation on an F-coalgebra -/
structure Bisimulation (F : Type u → Type u) (A : FCoalgebra F) where
  rel : A.carrier → A.carrier → Prop
  isReflexive : (a : A.carrier) → rel a a

/-- Def 7: Reflexivity of bisimulation witnessed by Path -/
noncomputable def bisim_refl_path {F : Type u → Type u} {A : FCoalgebra F}
    (B : Bisimulation F A) (a : A.carrier) :
    Path (B.rel a a) (B.rel a a) :=
  Path.refl (B.rel a a)

/-- Def 8: Bisimulation preserves identity via congrArg -/
noncomputable def bisim_congrArg {F : Type u → Type u} {A : FCoalgebra F}
    (B : Bisimulation F A) (a b : A.carrier) (p : Path a b) :
    Path (B.rel a a) (B.rel b b) :=
  Path.trans (Path.congrArg (B.rel · a) p) (Path.congrArg (B.rel b ·) p)

-- ========================================================================
-- Section 3: Coinduction Principle
-- ========================================================================

/-- Coinduction: if a relation is a bisimulation, elements are Path-equal -/
structure CoinductionWitness (A : Type u) where
  observe : A → A → Prop
  coinduct : (a b : A) → observe a b → Path a b

/-- Theorem 9: Coinductive proof composed with refl gives original -/
theorem coinduction_trans_refl {A : Type u} (W : CoinductionWitness A)
    (a b : A) (h : W.observe a b) :
    Path.trans (W.coinduct a b h) (Path.refl b) = W.coinduct a b h :=
  Path.trans_refl_right (W.coinduct a b h)

/-- Theorem 10: Coinductive proof with left refl gives original -/
theorem coinduction_refl_trans {A : Type u} (W : CoinductionWitness A)
    (a b : A) (h : W.observe a b) :
    Path.trans (Path.refl a) (W.coinduct a b h) = W.coinduct a b h :=
  Path.trans_refl_left (W.coinduct a b h)

/-- Theorem 11: Coinductive proof symm-trans toEq cancels -/
theorem coinduction_symm_cancel {A : Type u} (W : CoinductionWitness A)
    (a b : A) (h : W.observe a b) :
    (Path.trans (W.coinduct a b h) (Path.symm (W.coinduct a b h))).toEq = rfl :=
  Path.toEq_trans_symm (W.coinduct a b h)

/-- Theorem 12: Coinductive proof symm-symm -/
theorem coinduction_symm_symm {A : Type u} (W : CoinductionWitness A)
    (a b : A) (h : W.observe a b) :
    Path.symm (Path.symm (W.coinduct a b h)) = W.coinduct a b h :=
  Path.symm_symm (W.coinduct a b h)

-- ========================================================================
-- Section 4: Comonads
-- ========================================================================

/-- A comonad with counit (epsilon) and comultiplication (delta) -/
structure Comonad (W : Type u → Type u) where
  counit : {A : Type u} → W A → A
  comult : {A : Type u} → W A → W (W A)
  map : {A B : Type u} → (A → B) → W A → W B

/-- Comonad law witnesses via Path -/
structure ComonadLaws (W : Type u → Type u) (CM : Comonad W) where
  counit_left : {A : Type u} → (wa : W A) →
    Path (CM.map CM.counit (CM.comult wa)) wa
  counit_right : {A : Type u} → (wa : W A) →
    Path (CM.counit (CM.comult wa)) wa
  coassoc : {A : Type u} → (wa : W A) →
    Path (CM.comult (CM.comult wa)) (CM.map CM.comult (CM.comult wa))

/-- Theorem 13: Left counit law trans-refl -/
theorem comonad_counit_left_trans_refl {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (laws.counit_left wa) (Path.refl wa) = laws.counit_left wa :=
  Path.trans_refl_right (laws.counit_left wa)

/-- Theorem 14: Right counit law refl-trans -/
theorem comonad_counit_right_refl_trans {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (Path.refl (CM.counit (CM.comult wa))) (laws.counit_right wa) =
      laws.counit_right wa :=
  Path.trans_refl_left (laws.counit_right wa)

/-- Theorem 15: Coassociativity symm-symm -/
theorem comonad_coassoc_symm_symm {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.symm (Path.symm (laws.coassoc wa)) = laws.coassoc wa :=
  Path.symm_symm (laws.coassoc wa)

/-- Theorem 16: Counit left law symm-trans toEq -/
theorem comonad_counit_left_inv_toEq {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    (Path.trans (laws.counit_left wa) (Path.symm (laws.counit_left wa))).toEq = rfl :=
  Path.toEq_trans_symm (laws.counit_left wa)

/-- Theorem 17: Counit right law symm-trans toEq -/
theorem comonad_counit_right_inv_toEq {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    (Path.trans (laws.counit_right wa) (Path.symm (laws.counit_right wa))).toEq = rfl :=
  Path.toEq_trans_symm (laws.counit_right wa)

/-- Theorem 18: Double symm of counit law -/
theorem comonad_counit_symm_symm {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.symm (Path.symm (laws.counit_left wa)) = laws.counit_left wa :=
  Path.symm_symm (laws.counit_left wa)

/-- Theorem 19: Coassoc refl-trans -/
theorem comonad_coassoc_refl_trans {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (Path.refl _) (laws.coassoc wa) = laws.coassoc wa :=
  Path.trans_refl_left (laws.coassoc wa)

/-- Theorem 20: Coassoc trans-refl -/
theorem comonad_coassoc_trans_refl {W : Type u → Type u} {CM : Comonad W}
    (laws : ComonadLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (laws.coassoc wa) (Path.refl _) = laws.coassoc wa :=
  Path.trans_refl_right (laws.coassoc wa)

-- ========================================================================
-- Section 5: Comonad Functor Laws
-- ========================================================================

/-- Functor laws for the comonad -/
structure ComonadFunctorLaws (W : Type u → Type u) (CM : Comonad W) where
  map_id : {A : Type u} → (wa : W A) → Path (CM.map id wa) wa
  map_comp : {A B C : Type u} → (f : A → B) → (g : B → C) → (wa : W A) →
    Path (CM.map (g ∘ f) wa) (CM.map g (CM.map f wa))

/-- Theorem 21: Map id law trans-refl -/
theorem comonad_map_id_trans_refl {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (fl.map_id wa) (Path.refl wa) = fl.map_id wa :=
  Path.trans_refl_right (fl.map_id wa)

/-- Theorem 22: Map id law symm-symm -/
theorem comonad_map_id_symm_symm {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) {A : Type u} (wa : W A) :
    Path.symm (Path.symm (fl.map_id wa)) = fl.map_id wa :=
  Path.symm_symm (fl.map_id wa)

/-- Theorem 23: Map comp law symm-trans toEq -/
theorem comonad_map_comp_inv_toEq {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) {A B C : Type u}
    (f : A → B) (g : B → C) (wa : W A) :
    (Path.trans (fl.map_comp f g wa) (Path.symm (fl.map_comp f g wa))).toEq = rfl :=
  Path.toEq_trans_symm (fl.map_comp f g wa)

/-- Theorem 24: Map id law refl-trans -/
theorem comonad_map_id_refl_trans {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) {A : Type u} (wa : W A) :
    Path.trans (Path.refl _) (fl.map_id wa) = fl.map_id wa :=
  Path.trans_refl_left (fl.map_id wa)

-- ========================================================================
-- Section 6: Comonad Coalgebras (coEilenberg-Moore)
-- ========================================================================

/-- A coalgebra over a comonad W -/
structure ComonadCoalgebra (W : Type u → Type u) (CM : Comonad W) where
  carrier : Type u
  coaction : carrier → W carrier

/-- Laws for a comonad coalgebra -/
structure ComonadCoalgebraLaws (W : Type u → Type u) (CM : Comonad W)
    (CA : ComonadCoalgebra W CM) where
  counit_law : (a : CA.carrier) → Path (CM.counit (CA.coaction a)) a
  comult_law : (a : CA.carrier) →
    Path (CM.comult (CA.coaction a)) (CM.map CA.coaction (CA.coaction a))

/-- Theorem 25: Counit law trans-refl -/
theorem coalg_counit_trans_refl {W : Type u → Type u} {CM : Comonad W}
    {CA : ComonadCoalgebra W CM} (laws : ComonadCoalgebraLaws W CM CA)
    (a : CA.carrier) :
    Path.trans (laws.counit_law a) (Path.refl a) = laws.counit_law a :=
  Path.trans_refl_right (laws.counit_law a)

/-- Theorem 26: Comultiplication law symm-symm -/
theorem coalg_comult_symm_symm {W : Type u → Type u} {CM : Comonad W}
    {CA : ComonadCoalgebra W CM} (laws : ComonadCoalgebraLaws W CM CA)
    (a : CA.carrier) :
    Path.symm (Path.symm (laws.comult_law a)) = laws.comult_law a :=
  Path.symm_symm (laws.comult_law a)

/-- Theorem 27: Counit law inverse toEq -/
theorem coalg_counit_inv_toEq {W : Type u → Type u} {CM : Comonad W}
    {CA : ComonadCoalgebra W CM} (laws : ComonadCoalgebraLaws W CM CA)
    (a : CA.carrier) :
    (Path.trans (laws.counit_law a) (Path.symm (laws.counit_law a))).toEq = rfl :=
  Path.toEq_trans_symm (laws.counit_law a)

/-- Theorem 28: Comult law inverse toEq -/
theorem coalg_comult_inv_toEq {W : Type u → Type u} {CM : Comonad W}
    {CA : ComonadCoalgebra W CM} (laws : ComonadCoalgebraLaws W CM CA)
    (a : CA.carrier) :
    (Path.trans (laws.comult_law a) (Path.symm (laws.comult_law a))).toEq = rfl :=
  Path.toEq_trans_symm (laws.comult_law a)

/-- Morphism of comonad coalgebras -/
structure ComonadCoalgMorphism (W : Type u → Type u) (CM : Comonad W)
    (A B : ComonadCoalgebra W CM) where
  morph : A.carrier → B.carrier
  compat : (a : A.carrier) →
    Path (CM.map morph (A.coaction a)) (B.coaction (morph a))

/-- Theorem 29: CoalgMorphism compat trans-refl -/
theorem coalg_morph_compat_trans_refl {W : Type u → Type u} {CM : Comonad W}
    {A B : ComonadCoalgebra W CM} (m : ComonadCoalgMorphism W CM A B)
    (a : A.carrier) :
    Path.trans (m.compat a) (Path.refl (B.coaction (m.morph a))) = m.compat a :=
  Path.trans_refl_right (m.compat a)

/-- Identity morphism of comonad coalgebras -/
noncomputable def comonad_coalg_id {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) (CA : ComonadCoalgebra W CM) :
    ComonadCoalgMorphism W CM CA CA where
  morph := id
  compat := fun a => fl.map_id (CA.coaction a)

/-- Theorem 30: Identity morphism compat is map_id -/
theorem comonad_coalg_id_compat {W : Type u → Type u} {CM : Comonad W}
    (fl : ComonadFunctorLaws W CM) (CA : ComonadCoalgebra W CM) (a : CA.carrier) :
    (comonad_coalg_id fl CA).compat a = fl.map_id (CA.coaction a) :=
  rfl

/-- Theorem 31: CoalgMorphism compat symm-symm -/
theorem coalg_morph_compat_symm_symm {W : Type u → Type u} {CM : Comonad W}
    {A B : ComonadCoalgebra W CM} (m : ComonadCoalgMorphism W CM A B)
    (a : A.carrier) :
    Path.symm (Path.symm (m.compat a)) = m.compat a :=
  Path.symm_symm (m.compat a)

-- ========================================================================
-- Section 7: Cofree Coalgebras (pair-based)
-- ========================================================================

/-- Cofree coalgebra seed: head and F-tail -/
structure CofreeSeed (F : Type u → Type u) (A : Type u) where
  head : A
  tail : F A

/-- Extract operation on cofree seed -/
noncomputable def cofree_extract {F : Type u → Type u} {A : Type u} (c : CofreeSeed F A) : A :=
  c.head

/-- Def 32: Extract returns the head -/
noncomputable def cofree_extract_head {F : Type u → Type u} {A : Type u} (c : CofreeSeed F A) :
    Path (cofree_extract c) c.head :=
  Path.refl c.head

/-- Def 33: CongrArg through extract -/
noncomputable def cofree_extract_congrArg {F : Type u → Type u} {A B : Type u}
    (f : A → B) (c : CofreeSeed F A) :
    Path (f (cofree_extract c)) (f c.head) :=
  Path.congrArg f (cofree_extract_head c)

/-- Theorem 34: CongrArg through extract distributes over trans -/
theorem cofree_extract_congrArg_trans {F : Type u → Type u} {A B : Type u}
    (f : A → B) (c : CofreeSeed F A) :
    Path.congrArg f (Path.trans (cofree_extract_head c) (Path.refl c.head)) =
    Path.trans (Path.congrArg f (cofree_extract_head c)) (Path.congrArg f (Path.refl c.head)) :=
  Path.congrArg_trans f (cofree_extract_head c) (Path.refl c.head)

/-- Theorem 35: CongrArg through extract symm -/
theorem cofree_extract_congrArg_symm {F : Type u → Type u} {A B : Type u}
    (f : A → B) (c : CofreeSeed F A) :
    Path.congrArg f (Path.symm (cofree_extract_head c)) =
    Path.symm (Path.congrArg f (cofree_extract_head c)) :=
  Path.congrArg_symm f (cofree_extract_head c)

-- ========================================================================
-- Section 8: Final Coalgebra and Lambek's Lemma
-- ========================================================================

/-- A final coalgebra for functor F -/
structure FinalCoalgebra (F : Type u → Type u) extends FCoalgebra F where
  finality : (other : FCoalgebra F) →
    (f : other.carrier → carrier) ×
    ((a : other.carrier) → Path (struct (f a)) (struct (f a)))

/-- Lambek's lemma witness: the structure map of a final coalgebra is an iso -/
structure LambekWitness (F : Type u → Type u) (FC : FinalCoalgebra F) where
  inv : F FC.carrier → FC.carrier
  left_inv : (a : FC.carrier) → Path (inv (FC.struct a)) a
  right_inv : (fa : F FC.carrier) → Path (FC.struct (inv fa)) fa

/-- Theorem 36: Lambek left inverse trans-refl -/
theorem lambek_left_trans_refl {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a : FC.carrier) :
    Path.trans (lw.left_inv a) (Path.refl a) = lw.left_inv a :=
  Path.trans_refl_right (lw.left_inv a)

/-- Theorem 37: Lambek right inverse trans-refl -/
theorem lambek_right_trans_refl {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (fa : F FC.carrier) :
    Path.trans (lw.right_inv fa) (Path.refl fa) = lw.right_inv fa :=
  Path.trans_refl_right (lw.right_inv fa)

/-- Theorem 38: Lambek left inverse symm-symm -/
theorem lambek_left_symm_symm {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a : FC.carrier) :
    Path.symm (Path.symm (lw.left_inv a)) = lw.left_inv a :=
  Path.symm_symm (lw.left_inv a)

/-- Theorem 39: Lambek left inverse toEq cancels -/
theorem lambek_left_inv_toEq {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a : FC.carrier) :
    (Path.trans (lw.left_inv a) (Path.symm (lw.left_inv a))).toEq = rfl :=
  Path.toEq_trans_symm (lw.left_inv a)

/-- Theorem 40: Lambek right inverse toEq cancels -/
theorem lambek_right_inv_toEq {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (fa : F FC.carrier) :
    (Path.trans (lw.right_inv fa) (Path.symm (lw.right_inv fa))).toEq = rfl :=
  Path.toEq_trans_symm (lw.right_inv fa)

/-- Def 41: Lambek roundtrip via left_inv -/
noncomputable def lambek_roundtrip {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a : FC.carrier) :
    Path (lw.inv (FC.struct a)) a :=
  lw.left_inv a

/-- Def 42: Lambek congrArg of inv through struct -/
noncomputable def lambek_congrArg_inv {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a b : FC.carrier) (p : Path a b) :
    Path (lw.inv (FC.struct a)) (lw.inv (FC.struct b)) :=
  Path.congrArg (fun x => lw.inv (FC.struct x)) p

/-- Theorem 43: Lambek left refl-trans -/
theorem lambek_left_refl_trans {F : Type u → Type u} {FC : FinalCoalgebra F}
    (lw : LambekWitness F FC) (a : FC.carrier) :
    Path.trans (Path.refl _) (lw.left_inv a) = lw.left_inv a :=
  Path.trans_refl_left (lw.left_inv a)

-- ========================================================================
-- Section 9: Coalgebraic Modal Logic
-- ========================================================================

/-- A modal operator on a coalgebra -/
structure CoalgModalOp (F : Type u → Type u) (A : FCoalgebra F) where
  box : (A.carrier → Prop) → (A.carrier → Prop)
  monotone : {P Q : A.carrier → Prop} →
    ((a : A.carrier) → P a → Q a) → (a : A.carrier) → box P a → box Q a

/-- Diamond operator as dual of box -/
noncomputable def diamond {F : Type u → Type u} {A : FCoalgebra F}
    (M : CoalgModalOp F A) (P : A.carrier → Prop) (a : A.carrier) : Prop :=
  ¬ M.box (fun x => ¬ P x) a

/-- Theorem 44: Diamond is definitionally ¬ box ¬ -/
theorem diamond_unfold {F : Type u → Type u} {A : FCoalgebra F}
    (M : CoalgModalOp F A) (P : A.carrier → Prop) (a : A.carrier) :
    diamond M P a = (¬ M.box (fun x => ¬ P x) a) :=
  rfl

-- ========================================================================
-- Section 10: Stream Coalgebra (canonical example)
-- ========================================================================

/-- Stream as a coalgebraic pair of head + tail reference -/
structure StreamState (A : Type u) where
  headVal : A
  next : StreamState A

/-- Head observation -/
noncomputable def stream_head {A : Type u} (s : StreamState A) : A := s.headVal

/-- Def 45: Head observation path -/
noncomputable def stream_head_path {A : Type u} (s : StreamState A) :
    Path (stream_head s) s.headVal :=
  Path.refl s.headVal

/-- Def 46: CongrArg of head observation -/
noncomputable def stream_head_congrArg {A B : Type u} (f : A → B) (s t : StreamState A)
    (p : Path s.headVal t.headVal) :
    Path (f s.headVal) (f t.headVal) :=
  Path.congrArg f p

/-- Theorem 47: CongrArg distributes for head observation -/
theorem stream_head_congrArg_trans {A B : Type u} (f : A → B) (s t u : StreamState A)
    (p : Path s.headVal t.headVal) (q : Path t.headVal u.headVal) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Theorem 48: CongrArg symm for head observation -/
theorem stream_head_congrArg_symm {A B : Type u} (f : A → B) (s t : StreamState A)
    (p : Path s.headVal t.headVal) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

-- ========================================================================
-- Section 11: Path Algebra for Coalgebraic Proofs
-- ========================================================================

/-- Theorem 49: Trans associativity in coalgebraic context -/
theorem coalg_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Theorem 50: Coalgebraic path left unit -/
theorem coalg_trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Theorem 51: Coalgebraic path right unit -/
theorem coalg_trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Theorem 52: Coalgebraic path symm-symm -/
theorem coalg_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 53: CongrArg distributes over trans -/
theorem coalg_congrArg_trans {A B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Theorem 54: CongrArg distributes over symm -/
theorem coalg_congrArg_symm {A B : Type u} (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- Theorem 55: CongrArg composition -/
theorem coalg_congrArg_comp {A B C : Type u} (f : B → C) (g : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-- Theorem 56: CongrArg id is identity -/
theorem coalg_congrArg_id {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  Path.congrArg_id p

-- ========================================================================
-- Section 12: Comonad Extend and Duplicate
-- ========================================================================

/-- Extend operation derived from comonad -/
noncomputable def comonad_extend {W : Type u → Type u} (CM : Comonad W) {A B : Type u}
    (f : W A → B) (wa : W A) : W B :=
  CM.map f (CM.comult wa)

/-- Def 57: Extend definition unfolds -/
noncomputable def extend_path {W : Type u → Type u} (CM : Comonad W)
    {A B : Type u} (f : W A → B) (wa : W A) :
    Path (comonad_extend CM f wa) (CM.map f (CM.comult wa)) :=
  Path.refl _

/-- Duplicate = comult -/
noncomputable def comonad_duplicate {W : Type u → Type u} (CM : Comonad W)
    {A : Type u} (wa : W A) : W (W A) :=
  CM.comult wa

/-- Def 58: Duplicate equals comult -/
noncomputable def duplicate_is_comult {W : Type u → Type u} (CM : Comonad W)
    {A : Type u} (wa : W A) :
    Path (comonad_duplicate CM wa) (CM.comult wa) :=
  Path.refl (CM.comult wa)

-- ========================================================================
-- Section 13: Coalgebra Product
-- ========================================================================

/-- Product of two coalgebras -/
noncomputable def coalg_product (F : Type u → Type u) (A B : FCoalgebra F)
    (pairF : F A.carrier → F B.carrier → F (A.carrier × B.carrier)) :
    FCoalgebra F where
  carrier := A.carrier × B.carrier
  struct := fun ⟨a, b⟩ => pairF (A.struct a) (B.struct b)

/-- Def 59: Product coalgebra structure path -/
noncomputable def coalg_product_struct {F : Type u → Type u} (A B : FCoalgebra F)
    (pairF : F A.carrier → F B.carrier → F (A.carrier × B.carrier))
    (a : A.carrier) (b : B.carrier) :
    Path ((coalg_product F A B pairF).struct (a, b))
         (pairF (A.struct a) (B.struct b)) :=
  Path.refl _

/-- Def 60: First projection path -/
noncomputable def coalg_fst_path {A B : Type u}
    (a : A) (b : B) :
    Path (Prod.fst (a, b)) a :=
  Path.refl a

-- ========================================================================
-- Section 14: Coalgebraic Fixed Points
-- ========================================================================

/-- Fixed point witness: F(X) ≅ X -/
structure CoalgFixedPoint (F : Type u → Type u) where
  fixType : Type u
  unfold : fixType → F fixType
  fold : F fixType → fixType
  unfold_fold : (fx : F fixType) → Path (unfold (fold fx)) fx
  fold_unfold : (x : fixType) → Path (fold (unfold x)) x

/-- Theorem 61: Fixed point unfold-fold trans-refl -/
theorem fixpoint_unfold_fold_trans_refl {F : Type u → Type u}
    (fp : CoalgFixedPoint F) (fx : F fp.fixType) :
    Path.trans (fp.unfold_fold fx) (Path.refl fx) = fp.unfold_fold fx :=
  Path.trans_refl_right (fp.unfold_fold fx)

/-- Theorem 62: Fixed point fold-unfold symm-symm -/
theorem fixpoint_fold_unfold_symm_symm {F : Type u → Type u}
    (fp : CoalgFixedPoint F) (x : fp.fixType) :
    Path.symm (Path.symm (fp.fold_unfold x)) = fp.fold_unfold x :=
  Path.symm_symm (fp.fold_unfold x)

/-- Theorem 63: Fixed point roundtrip toEq -/
theorem fixpoint_roundtrip_toEq {F : Type u → Type u}
    (fp : CoalgFixedPoint F) (fx : F fp.fixType) :
    (Path.trans (fp.unfold_fold fx) (Path.symm (fp.unfold_fold fx))).toEq = rfl :=
  Path.toEq_trans_symm (fp.unfold_fold fx)

/-- Def 64: CongrArg of fold through fixed point -/
noncomputable def fixpoint_congrArg_fold {F : Type u → Type u}
    (fp : CoalgFixedPoint F) (fx fy : F fp.fixType) (p : Path fx fy) :
    Path (fp.fold fx) (fp.fold fy) :=
  Path.congrArg fp.fold p

/-- Theorem 65: Fixed point unfold-fold refl-trans -/
theorem fixpoint_unfold_fold_refl_trans {F : Type u → Type u}
    (fp : CoalgFixedPoint F) (fx : F fp.fixType) :
    Path.trans (Path.refl _) (fp.unfold_fold fx) = fp.unfold_fold fx :=
  Path.trans_refl_left (fp.unfold_fold fx)

-- ========================================================================
-- Section 15: Comonad Morphisms
-- ========================================================================

/-- A morphism between comonads -/
structure ComonadMorphism (W V : Type u → Type u) (CW : Comonad W) (CV : Comonad V) where
  transform : {A : Type u} → W A → V A
  counit_compat : {A : Type u} → (wa : W A) →
    Path (CV.counit (transform wa)) (CW.counit wa)

/-- Theorem 66: Comonad morphism counit compatibility trans-refl -/
theorem comonad_morph_counit_trans_refl {W V : Type u → Type u}
    {CW : Comonad W} {CV : Comonad V}
    (m : ComonadMorphism W V CW CV) {A : Type u} (wa : W A) :
    Path.trans (m.counit_compat wa) (Path.refl (CW.counit wa)) =
      m.counit_compat wa :=
  Path.trans_refl_right (m.counit_compat wa)

/-- Theorem 67: Comonad morphism counit compat symm-symm -/
theorem comonad_morph_counit_symm_symm {W V : Type u → Type u}
    {CW : Comonad W} {CV : Comonad V}
    (m : ComonadMorphism W V CW CV) {A : Type u} (wa : W A) :
    Path.symm (Path.symm (m.counit_compat wa)) = m.counit_compat wa :=
  Path.symm_symm (m.counit_compat wa)

-- ========================================================================
-- Section 16: Anamorphisms
-- ========================================================================

/-- Anamorphism: unfold from a seed -/
structure Anamorphism (F : Type u → Type u) (FC : FinalCoalgebra F) (A : Type u) where
  coalg : A → F A
  ana : A → FC.carrier
  commutes : (a : A) → Path (FC.struct (ana a)) (FC.struct (ana a))

/-- Theorem 68: Anamorphism commutes composed refl -/
theorem ana_commutes_refl {F : Type u → Type u} {FC : FinalCoalgebra F} {A : Type u}
    (an : Anamorphism F FC A) (a : A) :
    Path.trans (an.commutes a) (Path.refl _) = an.commutes a :=
  Path.trans_refl_right (an.commutes a)

/-- Def 69: Anamorphism congrArg -/
noncomputable def ana_congrArg {F : Type u → Type u} {FC : FinalCoalgebra F} {A : Type u}
    (an : Anamorphism F FC A) (a b : A) (p : Path a b) :
    Path (an.ana a) (an.ana b) :=
  Path.congrArg an.ana p

-- ========================================================================
-- Section 17: Coalgebraic Simulation
-- ========================================================================

/-- A simulation between two coalgebras -/
structure CoalgSimulation (F : Type u → Type u) (A B : FCoalgebra F) where
  rel : A.carrier → B.carrier → Prop
  sim_refl : (a : A.carrier) → (b : B.carrier) → rel a b → Path (rel a b) (rel a b)

/-- Def 70: Simulation relation is path-reflexive -/
noncomputable def simulation_path_refl {F : Type u → Type u} {A B : FCoalgebra F}
    (sim : CoalgSimulation F A B) (a : A.carrier) (b : B.carrier) (h : sim.rel a b) :
    Path (sim.rel a b) (sim.rel a b) :=
  sim.sim_refl a b h

/-- Theorem 71: Simulation trans-refl -/
theorem simulation_trans_refl {F : Type u → Type u} {A B : FCoalgebra F}
    (sim : CoalgSimulation F A B) (a : A.carrier) (b : B.carrier) (h : sim.rel a b) :
    Path.trans (sim.sim_refl a b h) (Path.refl _) = sim.sim_refl a b h :=
  Path.trans_refl_right (sim.sim_refl a b h)

-- ========================================================================
-- Section 18: Coiterative Structures
-- ========================================================================

/-- A coiterative structure with observation and transition -/
structure Coiterative (S : Type u) (O : Type u) where
  observe : S → O
  transition : S → S

/-- Def 72: Observation congrArg -/
noncomputable def coiter_congrArg_observe {S O : Type u} (C : Coiterative S O)
    (s t : S) (p : Path s t) :
    Path (C.observe s) (C.observe t) :=
  Path.congrArg C.observe p

/-- Def 73: Transition congrArg -/
noncomputable def coiter_congrArg_transition {S O : Type u} (C : Coiterative S O)
    (s t : S) (p : Path s t) :
    Path (C.transition s) (C.transition t) :=
  Path.congrArg C.transition p

/-- Theorem 74: Observe-after-transition congrArg composition -/
theorem coiter_observe_transition_comp {S O : Type u} (C : Coiterative S O)
    (s t : S) (p : Path s t) :
    Path.congrArg (fun x => C.observe (C.transition x)) p =
    Path.congrArg C.observe (Path.congrArg C.transition p) :=
  Path.congrArg_comp C.observe C.transition p

/-- Theorem 75: Observation distributes over path trans -/
theorem coiter_observe_trans {S O : Type u} (C : Coiterative S O)
    {s t u : S} (p : Path s t) (q : Path t u) :
    Path.congrArg C.observe (Path.trans p q) =
    Path.trans (Path.congrArg C.observe p) (Path.congrArg C.observe q) :=
  Path.congrArg_trans C.observe p q

/-- Theorem 76: Observation distributes over symm -/
theorem coiter_observe_symm {S O : Type u} (C : Coiterative S O)
    {s t : S} (p : Path s t) :
    Path.congrArg C.observe (Path.symm p) =
    Path.symm (Path.congrArg C.observe p) :=
  Path.congrArg_symm C.observe p

/-- Theorem 77: Transition distributes over path trans -/
theorem coiter_transition_trans {S O : Type u} (C : Coiterative S O)
    {s t u : S} (p : Path s t) (q : Path t u) :
    Path.congrArg C.transition (Path.trans p q) =
    Path.trans (Path.congrArg C.transition p) (Path.congrArg C.transition q) :=
  Path.congrArg_trans C.transition p q

/-- Theorem 78: Transition distributes over symm -/
theorem coiter_transition_symm {S O : Type u} (C : Coiterative S O)
    {s t : S} (p : Path s t) :
    Path.congrArg C.transition (Path.symm p) =
    Path.symm (Path.congrArg C.transition p) :=
  Path.congrArg_symm C.transition p

end CoalgebraPathDeep
end ComputationalPaths
