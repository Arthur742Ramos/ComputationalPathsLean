/-
# Path Groupoid Functoriality and Natural Transformations via Computational Paths

The fundamental groupoid: objects = elements of a type, morphisms = Path.
Groupoid axioms from trans_assoc, refl, symm. Functors between path groupoids
induced by functions (via congrArg). Natural transformations between such
functors. Functor composition coherence. Automorphism groups at a point.
Covering spaces as functors from the path groupoid.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open Path

universe u v w

namespace PathGroupoidDeep

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## 1. The Path Groupoid: Objects and Morphisms -/

/-- A morphism in the path groupoid from a to b. -/
abbrev Mor (a b : A) := Path a b

/-- Identity morphism at a point. -/
def idMor (a : A) : Mor a a := Path.refl a

/-- Composition of morphisms in the path groupoid. -/
def comp {a b c : A} (f : Mor a b) (g : Mor b c) : Mor a c :=
  Path.trans f g

/-- Inverse morphism in the path groupoid. -/
def inv {a b : A} (f : Mor a b) : Mor b a :=
  Path.symm f

/-! ## 2. Groupoid Axioms -/

/-- Theorem 1: Left unit law for the path groupoid. -/
theorem comp_id_left {a b : A} (f : Mor a b) :
    comp (idMor a) f = f :=
  Path.trans_refl_left f

/-- Theorem 2: Right unit law for the path groupoid. -/
theorem comp_id_right {a b : A} (f : Mor a b) :
    comp f (idMor b) = f :=
  Path.trans_refl_right f

/-- Theorem 3: Associativity of composition. -/
theorem comp_assoc {a b c d : A} (f : Mor a b) (g : Mor b c) (h : Mor c d) :
    comp (comp f g) h = comp f (comp g h) :=
  Path.trans_assoc f g h

/-- Theorem 4: Right inverse law (propositional). -/
theorem comp_inv_right_toEq {a b : A} (f : Mor a b) :
    (comp f (inv f)).toEq = rfl := by
  simp

/-- Theorem 5: Left inverse law (propositional). -/
theorem comp_inv_left_toEq {a b : A} (f : Mor a b) :
    (comp (inv f) f).toEq = rfl := by
  simp

/-- Theorem 6: Double inverse is identity. -/
theorem inv_inv {a b : A} (f : Mor a b) :
    inv (inv f) = f :=
  Path.symm_symm f

/-- Theorem 7: Inverse distributes over composition (anti-homomorphism). -/
theorem inv_comp {a b c : A} (f : Mor a b) (g : Mor b c) :
    inv (comp f g) = comp (inv g) (inv f) :=
  Path.symm_trans f g

/-- Theorem 8: Inverse of identity is identity. -/
theorem inv_id (a : A) : inv (idMor a) = idMor a :=
  Path.symm_refl a

/-! ## 3. Functors Between Path Groupoids -/

/-- A functor between path groupoids induced by a function f : A → B.
    On objects: f. On morphisms: congrArg f. -/
def mapMor (f : A → B) {a b : A} (p : Mor a b) : Mor (f a) (f b) :=
  Path.congrArg f p

/-- Theorem 9: Functors preserve identity morphisms. -/
theorem mapMor_id (f : A → B) (a : A) :
    mapMor f (idMor a) = idMor (f a) := by
  simp [mapMor, idMor]

/-- Theorem 10: Functors preserve composition. -/
theorem mapMor_comp (f : A → B) {a b c : A} (p : Mor a b) (q : Mor b c) :
    mapMor f (comp p q) = comp (mapMor f p) (mapMor f q) := by
  unfold mapMor comp
  exact Path.congrArg_trans f p q

/-- Theorem 11: Functors preserve inverses. -/
theorem mapMor_inv (f : A → B) {a b : A} (p : Mor a b) :
    mapMor f (inv p) = inv (mapMor f p) := by
  unfold mapMor inv
  exact Path.congrArg_symm f p

/-- Theorem 12: Identity functor acts as identity on morphisms. -/
theorem mapMor_id_fun {a b : A} (p : Mor a b) :
    mapMor (fun x => x) p = p :=
  Path.congrArg_id p

/-- Theorem 13: Functor composition coherence. -/
theorem mapMor_compose (f : B → C) (g : A → B) {a b : A} (p : Mor a b) :
    mapMor (fun x => f (g x)) p = mapMor f (mapMor g p) := by
  unfold mapMor
  exact Path.congrArg_comp f g p

/-! ## 4. Natural Transformations -/

/-- A natural transformation between functors f, g : A → B is given by a
    family of morphisms eta_a : Mor (f a) (g a). -/
structure NatTrans (f g : A → B) where
  component : (a : A) → Mor (f a) (g a)

@[ext]
theorem NatTrans.ext {f g : A → B} {eta eps : NatTrans f g}
    (h : ∀ a, eta.component a = eps.component a) : eta = eps := by
  cases eta; cases eps; simp; funext a; exact h a

/-- Theorem 14: Naturality condition – the square commutes propositionally. -/
theorem naturality_toEq (f g : A → B)
    (eta : NatTrans f g) {a b : A} (p : Mor a b) :
    (comp (mapMor f p) (eta.component b)).toEq =
    (comp (eta.component a) (mapMor g p)).toEq := by
  simp

/-- Theorem 15: Identity natural transformation (eta_a = refl). -/
def natTransId (f : A → B) : NatTrans f f :=
  ⟨fun a => idMor (f a)⟩

/-- Theorem 16: Identity natural transformation component is idMor. -/
theorem natTransId_component (f : A → B) (a : A) :
    (natTransId f).component a = idMor (f a) := rfl

/-- Vertical composition of natural transformations. -/
def natTransVComp {f g h : A → B}
    (eta : NatTrans f g) (eps : NatTrans g h) : NatTrans f h :=
  ⟨fun a => comp (eta.component a) (eps.component a)⟩

/-- Theorem 17: Left unit for vertical composition. -/
theorem natTransVComp_id_left {f g : A → B} (eta : NatTrans f g) :
    natTransVComp (natTransId f) eta = eta := by
  simp [natTransVComp, natTransId]
  ext a
  exact comp_id_left (eta.component a)

/-- Theorem 18: Right unit for vertical composition. -/
theorem natTransVComp_id_right {f g : A → B} (eta : NatTrans f g) :
    natTransVComp eta (natTransId g) = eta := by
  simp [natTransVComp, natTransId]
  ext a
  exact comp_id_right (eta.component a)

/-- Theorem 19: Associativity of vertical composition. -/
theorem natTransVComp_assoc {f g h k : A → B}
    (eta : NatTrans f g) (eps : NatTrans g h) (mu : NatTrans h k) :
    natTransVComp (natTransVComp eta eps) mu =
    natTransVComp eta (natTransVComp eps mu) := by
  simp [natTransVComp]
  ext a
  exact comp_assoc (eta.component a) (eps.component a) (mu.component a)

/-- Inverse natural transformation. -/
def natTransInv {f g : A → B} (eta : NatTrans f g) : NatTrans g f :=
  ⟨fun a => inv (eta.component a)⟩

/-- Theorem 20: Inverse involution for natural transformations. -/
theorem natTransInv_inv {f g : A → B} (eta : NatTrans f g) :
    natTransInv (natTransInv eta) = eta := by
  simp [natTransInv, inv_inv]

/-- Theorem 21: Right inverse for natural transformations (propositional). -/
theorem natTransVComp_inv_right_toEq {f g : A → B}
    (eta : NatTrans f g) (a : A) :
    (comp (eta.component a) ((natTransInv eta).component a)).toEq = rfl :=
  comp_inv_right_toEq (eta.component a)

/-- Theorem 22: Left inverse for natural transformations (propositional). -/
theorem natTransVComp_inv_left_toEq {f g : A → B}
    (eta : NatTrans f g) (a : A) :
    (comp ((natTransInv eta).component a) (eta.component a)).toEq = rfl :=
  comp_inv_left_toEq (eta.component a)

/-! ## 5. Horizontal Composition (Whiskering) -/

/-- Left whiskering: precompose a natural transformation with a functor. -/
def whiskerLeft (h : C → A) {f g : A → B} (eta : NatTrans f g) :
    NatTrans (fun x => f (h x)) (fun x => g (h x)) :=
  ⟨fun c => eta.component (h c)⟩

/-- Right whiskering: postcompose a natural transformation with a functor. -/
def whiskerRight {f g : A → B} (eta : NatTrans f g) (h : B → C) :
    NatTrans (fun x => h (f x)) (fun x => h (g x)) :=
  ⟨fun a => mapMor h (eta.component a)⟩

/-- Theorem 23: Whiskering with identity functor on the left. -/
theorem whiskerLeft_id {f g : A → B} (eta : NatTrans f g) :
    whiskerLeft (fun x : A => x) eta = eta := by
  simp [whiskerLeft]

/-- Theorem 24: Right whiskering preserves idMor components. -/
theorem whiskerRight_natTransId (f : A → B) (h : B → C) :
    whiskerRight (natTransId f) h = natTransId (fun x => h (f x)) := by
  simp [whiskerRight, natTransId, mapMor_id]

/-- Theorem 25: Left whiskering preserves identity. -/
theorem whiskerLeft_natTransId (h : C → A) (f : A → B) :
    whiskerLeft h (natTransId f) = natTransId (fun x => f (h x)) := by
  simp [whiskerLeft, natTransId]

/-! ## 6. Functor Category Structure -/

/-- Theorem 26: Composition of functors is associative on morphisms. -/
theorem functor_comp_assoc (f : A → B) (g : B → C) (h : C → A)
    {a b : A} (p : Mor a b) :
    mapMor (fun x => h (g (f x))) p =
    mapMor h (mapMor g (mapMor f p)) := by
  unfold mapMor
  exact Path.congrArg_comp (fun x => h (g x)) f p |>.trans
    (Path.congrArg_comp h g (Path.congrArg f p))

/-- Theorem 27: mapMor preserves double inverse. -/
theorem mapMor_inv_inv (f : A → B) {a b : A} (p : Mor a b) :
    mapMor f (inv (inv p)) = mapMor f p := by
  rw [inv_inv]

/-- Theorem 28: mapMor and inv commute doubly. -/
theorem mapMor_inv_comm (f : A → B) {a b : A} (p : Mor a b) :
    inv (inv (mapMor f p)) = mapMor f p := by
  rw [inv_inv]

/-! ## 7. Automorphism Groups at a Point -/

/-- The automorphism group at a point: loops (paths from a to a). -/
def Aut (a : A) := Mor a a

/-- Theorem 29: The identity loop. -/
def autId (a : A) : Aut a := idMor a

/-- Theorem 30: Composition of automorphisms. -/
def autComp {a : A} (f g : Aut a) : Aut a := comp f g

/-- Theorem 31: Inverse of automorphism. -/
def autInv {a : A} (f : Aut a) : Aut a := inv f

/-- Theorem 32: Left unit for Aut composition. -/
theorem autComp_id_left {a : A} (f : Aut a) :
    autComp (autId a) f = f :=
  comp_id_left f

/-- Theorem 33: Right unit for Aut composition. -/
theorem autComp_id_right {a : A} (f : Aut a) :
    autComp f (autId a) = f :=
  comp_id_right f

/-- Theorem 34: Associativity for Aut. -/
theorem autComp_assoc {a : A} (f g h : Aut a) :
    autComp (autComp f g) h = autComp f (autComp g h) :=
  comp_assoc f g h

/-- Theorem 35: Right inverse for Aut (propositional). -/
theorem autComp_inv_right_toEq {a : A} (f : Aut a) :
    (autComp f (autInv f)).toEq = rfl :=
  comp_inv_right_toEq f

/-- Theorem 36: Left inverse for Aut (propositional). -/
theorem autComp_inv_left_toEq {a : A} (f : Aut a) :
    (autComp (autInv f) f).toEq = rfl :=
  comp_inv_left_toEq f

/-- Theorem 37: Double inverse for Aut. -/
theorem autInv_autInv {a : A} (f : Aut a) :
    autInv (autInv f) = f :=
  inv_inv f

/-- Theorem 38: Inverse anti-homomorphism for Aut. -/
theorem autInv_comp {a : A} (f g : Aut a) :
    autInv (autComp f g) = autComp (autInv g) (autInv f) :=
  inv_comp f g

/-! ## 8. Conjugation in the Automorphism Group -/

/-- Conjugation of an automorphism by a path. -/
def conjugate {a b : A} (p : Mor a b) (f : Aut a) : Aut b :=
  comp (inv p) (comp f p)

/-- Theorem 39: Conjugation by identity is identity (propositional toEq). -/
theorem conjugate_id_toEq {a : A} (f : Aut a) :
    (conjugate (idMor a) f).toEq = f.toEq := by
  unfold conjugate comp inv idMor
  simp

/-- Theorem 40: Conjugation preserves identity automorphism (propositional toEq). -/
theorem conjugate_autId_toEq {a b : A} (p : Mor a b) :
    (conjugate p (autId a)).toEq = (idMor b).toEq := by
  unfold conjugate autId idMor comp inv
  simp

/-- Theorem 41: Conjugation by composition decomposes. -/
theorem conjugate_comp {a b c : A} (p : Mor a b) (q : Mor b c) (f : Aut a) :
    conjugate (comp p q) f = conjugate q (conjugate p f) := by
  unfold conjugate comp inv
  rw [Path.symm_trans p q]
  -- LHS: ((symm q).trans (symm p)).trans (f.trans (p.trans q))
  -- RHS: (symm q).trans (((symm p).trans (f.trans p)).trans q)
  rw [← Path.trans_assoc f p q]
  -- LHS: ((symm q).trans (symm p)).trans ((f.trans p).trans q)
  -- RHS: (symm q).trans (((symm p).trans (f.trans p)).trans q)
  rw [Path.trans_assoc (Path.symm q) (Path.symm p) ((Path.trans f p).trans q)]
  -- LHS: (symm q).trans ((symm p).trans ((f.trans p).trans q))
  rw [Path.trans_assoc (Path.symm p) (Path.trans f p) q]

/-! ## 9. Functor-Induced Group Homomorphisms -/

/-- A function f : A → B induces a group homomorphism Aut(a) → Aut(f a). -/
def autMap (f : A → B) {a : A} (loop : Aut a) : Aut (f a) :=
  mapMor f loop

/-- Theorem 42: autMap preserves identity. -/
theorem autMap_id (f : A → B) (a : A) :
    autMap f (autId a) = autId (f a) :=
  mapMor_id f a

/-- Theorem 43: autMap preserves composition. -/
theorem autMap_comp (f : A → B) {a : A} (p q : Aut a) :
    autMap f (autComp p q) = autComp (autMap f p) (autMap f q) :=
  mapMor_comp f p q

/-- Theorem 44: autMap preserves inverses. -/
theorem autMap_inv (f : A → B) {a : A} (p : Aut a) :
    autMap f (autInv p) = autInv (autMap f p) :=
  mapMor_inv f p

/-- Theorem 45: Identity function gives identity homomorphism. -/
theorem autMap_id_fun {a : A} (p : Aut a) :
    autMap (fun x => x) p = p :=
  mapMor_id_fun p

/-- Theorem 46: Composition of functions gives composition of homomorphisms. -/
theorem autMap_compose (f : B → C) (g : A → B) {a : A} (p : Aut a) :
    autMap (fun x => f (g x)) p = autMap f (autMap g p) :=
  mapMor_compose f g p

/-! ## 10. Path Groupoid as Self-Enriched Category -/

/-- The hom-Path between two morphisms: a 2-morphism (equality of paths). -/
def Hom2 {a b : A} (f g : Mor a b) := f = g

/-- Theorem 47: Reflexivity of 2-morphisms. -/
def hom2Refl {a b : A} (f : Mor a b) : Hom2 f f := rfl

/-- Theorem 48: Symmetry of 2-morphisms. -/
def hom2Symm {a b : A} {f g : Mor a b} (h : Hom2 f g) : Hom2 g f :=
  h.symm

/-- Theorem 49: Transitivity of 2-morphisms. -/
def hom2Trans {a b : A} {f g h : Mor a b}
    (alpha : Hom2 f g) (beta : Hom2 g h) : Hom2 f h :=
  alpha.trans beta

/-- Left whiskering of 2-morphisms by a 1-morphism. -/
def hom2WhiskerLeft {a b c : A} {f g : Mor a b} (alpha : Hom2 f g)
    (h : Mor b c) : Hom2 (comp f h) (comp g h) :=
  congrArg (fun t => comp t h) alpha

/-- Right whiskering of 2-morphisms by a 1-morphism. -/
def hom2WhiskerRight {a b c : A} (h : Mor a b)
    {f g : Mor b c} (alpha : Hom2 f g) : Hom2 (comp h f) (comp h g) :=
  congrArg (fun t => comp h t) alpha

/-- Theorem 50: Interchange law for 2-morphisms. -/
theorem hom2_interchange {a b c : A}
    {f1 f2 : Mor a b} {g1 g2 : Mor b c}
    (alpha : Hom2 f1 f2) (gamma : Hom2 g1 g2) :
    hom2Trans (hom2WhiskerRight f1 gamma) (hom2WhiskerLeft alpha g2) =
    hom2Trans (hom2WhiskerLeft alpha g1) (hom2WhiskerRight f2 gamma) := by
  subst alpha; subst gamma; rfl

/-! ## 11. Covering Spaces as Functors -/

/-- A "covering functor" from the path groupoid of A to Type: assigns to each
    point a fiber, and to each path a transport function. -/
structure CoveringFunctor (A : Type u) where
  fiber : A → Type v
  lift : {a b : A} → Mor a b → fiber a → fiber b
  lift_id : (a : A) → (x : fiber a) → lift (idMor a) x = x
  lift_comp : {a b c : A} → (p : Mor a b) → (q : Mor b c) →
    (x : fiber a) → lift (comp p q) x = lift q (lift p x)

/-- Theorem 51: The constant covering functor. -/
def constCovering (A : Type u) (F : Type v) : CoveringFunctor A where
  fiber := fun _ => F
  lift := fun _ x => x
  lift_id := fun _ _ => rfl
  lift_comp := fun _ _ _ => rfl

/-- Theorem 52: The transport covering functor for a type family. -/
def transportCovering {A : Type u} (D : A → Type v) : CoveringFunctor A where
  fiber := D
  lift := fun p x => Path.transport p x
  lift_id := fun _ _ => rfl
  lift_comp := fun p q x => Path.transport_trans p q x

/-- A morphism of covering functors. -/
structure CoveringMorphism {A : Type u} (F G : CoveringFunctor A) where
  fiberMap : (a : A) → F.fiber a → G.fiber a
  naturality : {a b : A} → (p : Mor a b) → (x : F.fiber a) →
    fiberMap b (F.lift p x) = G.lift p (fiberMap a x)

/-- Theorem 53: Identity morphism of covering functors. -/
def coveringMorphismId {A : Type u} (F : CoveringFunctor A) :
    CoveringMorphism F F where
  fiberMap := fun _ x => x
  naturality := fun _ _ => rfl

/-- Theorem 54: Composition of covering morphisms. -/
def coveringMorphismComp {A : Type u} {F G H : CoveringFunctor A}
    (alpha : CoveringMorphism F G) (beta : CoveringMorphism G H) :
    CoveringMorphism F H where
  fiberMap := fun a x => beta.fiberMap a (alpha.fiberMap a x)
  naturality := fun p x => by
    rw [alpha.naturality p x]
    exact beta.naturality p (alpha.fiberMap _ x)

/-! ## 12. Groupoid Functor Properties -/

/-- Theorem 55: mapMor preserves double composition (4-fold). -/
theorem mapMor_comp4 (f : A → B) {a b c d e : A}
    (p : Mor a b) (q : Mor b c) (r : Mor c d) (s : Mor d e) :
    mapMor f (comp (comp (comp p q) r) s) =
    comp (comp (comp (mapMor f p) (mapMor f q)) (mapMor f r)) (mapMor f s) := by
  unfold mapMor comp
  rw [Path.congrArg_trans f (Path.trans (Path.trans p q) r) s]
  rw [Path.congrArg_trans f (Path.trans p q) r]
  rw [Path.congrArg_trans f p q]

/-- Theorem 56: mapMor respects the associator. -/
theorem mapMor_assoc_coherence (f : A → B) {a b c d : A}
    (p : Mor a b) (q : Mor b c) (r : Mor c d) :
    mapMor f (comp (comp p q) r) = mapMor f (comp p (comp q r)) := by
  rw [comp_assoc]

/-- Theorem 57: Conjugation commutes with mapMor. -/
theorem conjugate_mapMor (f : A → B) {a b : A} (p : Mor a b) (loop : Aut a) :
    mapMor f (conjugate p loop) = conjugate (mapMor f p) (autMap f loop) := by
  unfold conjugate autMap mapMor comp inv
  rw [Path.congrArg_trans f (Path.symm p) (Path.trans loop p)]
  rw [Path.congrArg_symm f p]
  rw [Path.congrArg_trans f loop p]

/-! ## 13. Natural Transformation Composition Laws -/

/-- Theorem 58: Vertical composition with inverse is propositionally trivial. -/
theorem natTransVComp_natTransInv_toEq {f g : A → B}
    (eta : NatTrans f g) (a : A) :
    ((natTransVComp eta (natTransInv eta)).component a).toEq = rfl := by
  exact comp_inv_right_toEq (eta.component a)

/-- Theorem 59: Right whiskering distributes over vertical composition. -/
theorem whiskerRight_vcomp {f g h : A → B} (k : B → C)
    (eta : NatTrans f g) (eps : NatTrans g h) :
    whiskerRight (natTransVComp eta eps) k =
    natTransVComp (whiskerRight eta k) (whiskerRight eps k) := by
  unfold whiskerRight natTransVComp mapMor comp
  congr 1; funext a
  exact Path.congrArg_trans k (eta.component a) (eps.component a)

/-- Theorem 60: Left whiskering distributes over vertical composition. -/
theorem whiskerLeft_vcomp (k : C → A) {f g h : A → B}
    (eta : NatTrans f g) (eps : NatTrans g h) :
    whiskerLeft k (natTransVComp eta eps) =
    natTransVComp (whiskerLeft k eta) (whiskerLeft k eps) := by
  simp [whiskerLeft, natTransVComp]

/-- Theorem 61: Right whiskering preserves inverse. -/
theorem whiskerRight_inv {f g : A → B} (k : B → C) (eta : NatTrans f g) :
    whiskerRight (natTransInv eta) k = natTransInv (whiskerRight eta k) := by
  unfold whiskerRight natTransInv mapMor inv
  congr 1; funext a
  exact Path.congrArg_symm k (eta.component a)

/-- Theorem 62: Left whiskering preserves inverse. -/
theorem whiskerLeft_inv (k : C → A) {f g : A → B} (eta : NatTrans f g) :
    whiskerLeft k (natTransInv eta) = natTransInv (whiskerLeft k eta) := by
  simp [whiskerLeft, natTransInv]

end PathGroupoidDeep

end ComputationalPaths
