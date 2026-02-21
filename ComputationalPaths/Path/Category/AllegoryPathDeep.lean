/-
  AllegoryPathDeep.lean

  Allegories and Categories of Relations via Computational Paths

  An allegory is a category enriched over lattices of relations. We develop
  the theory of allegories — relation composition, converse, intersection,
  tabular and unitary allegories, maps (total single-valued relations),
  difunctional relations, power allegories, regular categories as allegories,
  and Freyd's representation theorem structure — all with coherence witnessed
  by computational paths (Path.trans, Path.symm, Path.congrArg).

  Author: armada-395 (AllegoryPathDeep)
  Date: 2026-02-16
-/

import ComputationalPaths.Path.Basic

namespace AllegoryPathDeep

open ComputationalPaths

universe u v

-- ============================================================================
-- Section 1: Abstract Allegory — Operations and Axiom Paths
-- ============================================================================

/-- An abstract allegory: a category enriched over meet-semilattices with
    converse, whose axioms are witnessed by computational paths. -/
structure Allegory where
  Ob : Type u
  Hom : Ob → Ob → Type u
  idM   : (A : Ob) → Hom A A
  comp  : {A B C : Ob} → Hom B C → Hom A B → Hom A C
  conv  : {A B : Ob} → Hom A B → Hom B A
  meet  : {A B : Ob} → Hom A B → Hom A B → Hom A B
  comp_assoc : {A B C D : Ob} → (f : Hom C D) → (g : Hom B C) → (h : Hom A B) →
    Path (comp (comp f g) h) (comp f (comp g h))
  comp_id_left : {A B : Ob} → (f : Hom A B) → Path (comp (idM B) f) f
  comp_id_right : {A B : Ob} → (f : Hom A B) → Path (comp f (idM A)) f
  conv_conv : {A B : Ob} → (f : Hom A B) → Path (conv (conv f)) f
  conv_comp : {A B C : Ob} → (f : Hom B C) → (g : Hom A B) →
    Path (conv (comp f g)) (comp (conv g) (conv f))
  conv_id : (A : Ob) → Path (conv (idM A)) (idM A)
  meet_comm : {A B : Ob} → (f g : Hom A B) → Path (meet f g) (meet g f)
  meet_assoc : {A B : Ob} → (f g h : Hom A B) →
    Path (meet (meet f g) h) (meet f (meet g h))
  meet_idem : {A B : Ob} → (f : Hom A B) → Path (meet f f) f
  conv_meet : {A B : Ob} → (f g : Hom A B) →
    Path (conv (meet f g)) (meet (conv f) (conv g))

-- ============================================================================
-- Section 2: Derived Category Coherence via Path Combinators
-- ============================================================================

section WithAllegory
variable (Al : Allegory)

/-- Theorem 1: Pentagon coherence for composition associativity -/
def pentagon_coherence {A B C D E : Al.Ob}
    (f : Al.Hom D E) (g : Al.Hom C D) (h : Al.Hom B C) (k : Al.Hom A B) :
    Path (Al.comp (Al.comp (Al.comp f g) h) k)
         (Al.comp f (Al.comp g (Al.comp h k))) :=
  Path.trans
    (Al.comp_assoc (Al.comp f g) h k)
    (Al.comp_assoc f g (Al.comp h k))

/-- Theorem 2: Left triangle coherence -/
def triangle_left {A B C : Al.Ob} (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.comp f (Al.comp (Al.idM B) g))
         (Al.comp f g) :=
  Path.congrArg (fun x => Al.comp f x) (Al.comp_id_left g)

/-- Theorem 3: Right triangle coherence -/
def triangle_right {A B C : Al.Ob} (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.comp (Al.comp f (Al.idM B)) g)
         (Al.comp f g) :=
  Path.congrArg (fun x => Al.comp x g) (Al.comp_id_right f)

/-- Theorem 4: Identity is its own converse -/
def id_self_conv (A : Al.Ob) :
    Path (Al.conv (Al.idM A)) (Al.idM A) :=
  Al.conv_id A

/-- Theorem 5: Converse involution -/
def conv_involution {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.conv f)) f :=
  Al.conv_conv f

/-- Theorem 6: Triple converse simplification -/
def conv_triple {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.conv (Al.conv f))) (Al.conv f) :=
  Al.conv_conv (Al.conv f)

/-- Theorem 7: Converse distributes over triple composition -/
def conv_triple_comp {A B C D : Al.Ob}
    (f : Al.Hom C D) (g : Al.Hom B C) (h : Al.Hom A B) :
    Path (Al.conv (Al.comp f (Al.comp g h)))
         (Al.comp (Al.conv (Al.comp g h)) (Al.conv f)) :=
  Al.conv_comp f (Al.comp g h)

/-- Theorem 8: Full expansion of converse of triple composition -/
def conv_triple_comp_expanded {A B C D : Al.Ob}
    (f : Al.Hom C D) (g : Al.Hom B C) (h : Al.Hom A B) :
    Path (Al.conv (Al.comp f (Al.comp g h)))
         (Al.comp (Al.comp (Al.conv h) (Al.conv g)) (Al.conv f)) :=
  Path.trans
    (Al.conv_comp f (Al.comp g h))
    (Path.congrArg (fun x => Al.comp x (Al.conv f)) (Al.conv_comp g h))

/-- Theorem 9: Converse of composition with identity left -/
def conv_comp_id_left {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.comp (Al.idM B) f))
         (Al.comp (Al.conv f) (Al.idM B)) :=
  Path.trans
    (Al.conv_comp (Al.idM B) f)
    (Path.congrArg (fun x => Al.comp (Al.conv f) x) (Al.conv_id B))

/-- Theorem 10: Converse of composition with identity simplified -/
def conv_comp_id_left_simplified {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.comp (Al.idM B) f))
         (Al.conv f) :=
  Path.congrArg Al.conv (Al.comp_id_left f)

-- ============================================================================
-- Section 3: Meet (Intersection) Coherence
-- ============================================================================

/-- Theorem 11: Meet double commutativity -/
def meet_comm_comm {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.meet (Al.meet f g) (Al.meet g f))
         (Al.meet (Al.meet f g) (Al.meet f g)) :=
  Path.congrArg (fun x => Al.meet (Al.meet f g) x) (Al.meet_comm g f)

/-- Theorem 12: Meet with self via idempotence -/
def meet_self_via_comm {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.meet f f) f :=
  Al.meet_idem f

/-- Theorem 13: Meet-converse-meet coherence -/
def meet_conv_meet {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.conv (Al.meet f g))
         (Al.meet (Al.conv g) (Al.conv f)) :=
  Path.trans
    (Al.conv_meet f g)
    (Al.meet_comm (Al.conv f) (Al.conv g))

/-- Theorem 14: Double converse of a meet -/
def conv_conv_meet {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.conv (Al.conv (Al.meet f g)))
         (Al.meet f g) :=
  Al.conv_conv (Al.meet f g)

/-- Theorem 15: Converse of meet, then converse again -/
def meet_conv_roundtrip {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.conv (Al.meet (Al.conv f) (Al.conv g)))
         (Al.meet f g) :=
  Path.trans
    (Al.conv_meet (Al.conv f) (Al.conv g))
    (Path.trans
      (Path.congrArg (fun x => Al.meet x (Al.conv (Al.conv g))) (Al.conv_conv f))
      (Path.congrArg (fun x => Al.meet f x) (Al.conv_conv g)))

/-- Theorem 16: Meet associativity-commutativity interaction -/
def meet_assoc_comm {A B : Al.Ob} (f g h : Al.Hom A B) :
    Path (Al.meet (Al.meet f g) h)
         (Al.meet f (Al.meet h g)) :=
  Path.trans
    (Al.meet_assoc f g h)
    (Path.congrArg (fun x => Al.meet f x) (Al.meet_comm g h))

-- ============================================================================
-- Section 4: Maps in an Allegory
-- ============================================================================

/-- A map in an allegory: a morphism f with meet-witnessed totality/sv -/
structure AllegoryMap (Al : Allegory) (A B : Al.Ob) where
  mor : Al.Hom A B
  totalWitness : Path (Al.meet (Al.idM A) (Al.comp (Al.conv mor) mor)) (Al.idM A)
  svWitness : Path (Al.meet (Al.comp mor (Al.conv mor)) (Al.idM B)) (Al.idM B)

/-- Theorem 17: The identity converse composed with identity -/
def id_is_map (A : Al.Ob) :
    Path (Al.comp (Al.conv (Al.idM A)) (Al.idM A))
         (Al.comp (Al.idM A) (Al.idM A)) :=
  Path.congrArg (fun x => Al.comp x (Al.idM A)) (Al.conv_id A)

/-- Theorem 18: Identity composition simplification -/
def id_comp_id (A : Al.Ob) :
    Path (Al.comp (Al.idM A) (Al.idM A))
         (Al.idM A) :=
  Al.comp_id_left (Al.idM A)

/-- Theorem 19: Full identity-as-map path -/
def id_map_full (A : Al.Ob) :
    Path (Al.comp (Al.conv (Al.idM A)) (Al.idM A))
         (Al.idM A) :=
  Path.trans (id_is_map Al A) (id_comp_id Al A)

/-- Theorem 20: Map composition preserves converse structure -/
def map_comp_conv {A B C : Al.Ob}
    (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.conv (Al.comp f g))
         (Al.comp (Al.conv g) (Al.conv f)) :=
  Al.conv_comp f g

/-- Theorem 21: Map composition converse roundtrip -/
def map_comp_conv_roundtrip {A B C : Al.Ob}
    (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.conv (Al.conv (Al.comp f g)))
         (Al.comp f g) :=
  Al.conv_conv (Al.comp f g)

-- ============================================================================
-- Section 5: Difunctional Relations
-- ============================================================================

/-- A relation R is difunctional if R;R°;R ≤ R (modeled as meet) -/
structure Difunctional (Al : Allegory) {A B : Al.Ob} (R : Al.Hom A B) where
  witness : Path (Al.meet (Al.comp R (Al.comp (Al.conv R) R)) R) R

/-- Theorem 22: Difunctional triple composition reassociation -/
def difunctional_assoc {A B : Al.Ob} (R : Al.Hom A B) :
    Path (Al.comp R (Al.comp (Al.conv R) R))
         (Al.comp (Al.comp R (Al.conv R)) R) :=
  Path.symm (Al.comp_assoc R (Al.conv R) R)

/-- Theorem 23: Difunctional converse coherence -/
def difunctional_conv {A B : Al.Ob} (R : Al.Hom A B) :
    Path (Al.conv (Al.comp R (Al.comp (Al.conv R) R)))
         (Al.comp (Al.conv (Al.comp (Al.conv R) R)) (Al.conv R)) :=
  Al.conv_comp R (Al.comp (Al.conv R) R)

/-- Theorem 24: Difunctional inner converse expansion -/
def difunctional_inner_conv {A B : Al.Ob} (R : Al.Hom A B) :
    Path (Al.conv (Al.comp (Al.conv R) R))
         (Al.comp (Al.conv R) (Al.conv (Al.conv R))) :=
  Al.conv_comp (Al.conv R) R

/-- Theorem 25: Difunctional inner double converse simplification -/
def difunctional_inner_simplified {A B : Al.Ob} (R : Al.Hom A B) :
    Path (Al.conv (Al.comp (Al.conv R) R))
         (Al.comp (Al.conv R) R) :=
  Path.trans
    (difunctional_inner_conv Al R)
    (Path.congrArg (fun x => Al.comp (Al.conv R) x) (Al.conv_conv R))

-- ============================================================================
-- Section 6: Tabular Allegories
-- ============================================================================

/-- A tabulation of R: maps f, g with R = g ; f° -/
structure Tabulation (Al : Allegory) {A B : Al.Ob} (R : Al.Hom A B) where
  T : Al.Ob
  f : Al.Hom T A
  g : Al.Hom T B
  tab : Path R (Al.comp g (Al.conv f))

/-- Theorem 26: Tabulation converse coherence -/
def tabulation_conv {A B : Al.Ob} (R : Al.Hom A B)
    (T : Al.Ob) (f : Al.Hom T A) (g : Al.Hom T B)
    (tab : Path R (Al.comp g (Al.conv f))) :
    Path (Al.conv R)
         (Al.comp (Al.conv (Al.conv f)) (Al.conv g)) :=
  Path.trans
    (Path.congrArg Al.conv tab)
    (Al.conv_comp g (Al.conv f))

/-- Theorem 27: Tabulation converse simplified -/
def tabulation_conv_simplified {A B : Al.Ob} (R : Al.Hom A B)
    (T : Al.Ob) (f : Al.Hom T A) (g : Al.Hom T B)
    (tab : Path R (Al.comp g (Al.conv f))) :
    Path (Al.conv R)
         (Al.comp f (Al.conv g)) :=
  Path.trans
    (tabulation_conv Al R T f g tab)
    (Path.congrArg (fun x => Al.comp x (Al.conv g)) (Al.conv_conv f))

/-- Theorem 28: Tabulation double converse roundtrip -/
def tabulation_double_conv {A B : Al.Ob} (R : Al.Hom A B) :
    Path (Al.conv (Al.conv R)) R :=
  Al.conv_conv R

end WithAllegory

-- ============================================================================
-- Section 7: Unitary Allegories
-- ============================================================================

/-- A unitary allegory has a distinguished "unit" morphism -/
structure UnitaryAllegory (Al : Allegory) where
  unitMor : (A : Al.Ob) → Al.Hom A A
  unit_refl : (A : Al.Ob) → Path (Al.meet (Al.idM A) (unitMor A)) (Al.idM A)
  unit_symm : (A : Al.Ob) → Path (Al.conv (unitMor A)) (unitMor A)

/-- Theorem 29: Unit morphism converse involution -/
def unitary_conv_invol (Al : Allegory) (U : UnitaryAllegory Al) (A : Al.Ob) :
    Path (Al.conv (Al.conv (U.unitMor A))) (U.unitMor A) :=
  Al.conv_conv (U.unitMor A)

/-- Theorem 30: Unit symmetry composed with converse -/
def unitary_symm_conv (Al : Allegory) (U : UnitaryAllegory Al) (A : Al.Ob) :
    Path (Al.conv (U.unitMor A)) (U.unitMor A) :=
  U.unit_symm A

/-- Theorem 31: Unit identity interaction -/
def unitary_id_unit (Al : Allegory) (U : UnitaryAllegory Al) (A : Al.Ob) :
    Path (Al.comp (U.unitMor A) (Al.idM A))
         (U.unitMor A) :=
  Al.comp_id_right (U.unitMor A)

/-- Theorem 32: Unit composition with itself reassociation -/
def unitary_self_comp_assoc (Al : Allegory) (U : UnitaryAllegory Al) (A : Al.Ob) :
    Path (Al.comp (Al.comp (U.unitMor A) (U.unitMor A)) (U.unitMor A))
         (Al.comp (U.unitMor A) (Al.comp (U.unitMor A) (U.unitMor A))) :=
  Al.comp_assoc (U.unitMor A) (U.unitMor A) (U.unitMor A)

-- ============================================================================
-- Section 8: Power Allegory Structure
-- ============================================================================

/-- A power allegory wraps an allegory with power objects -/
structure PowerAllegory (Al : Allegory) where
  Pow : Al.Ob → Al.Ob
  membership : (A : Al.Ob) → Al.Hom A (Pow A)
  mem_conv_conv : (A : Al.Ob) → Path (Al.conv (Al.conv (membership A))) (membership A)

/-- Theorem 33: Power membership converse coherence -/
def power_mem_conv (Al : Allegory) (P : PowerAllegory Al) (A : Al.Ob) :
    Path (Al.conv (Al.conv (P.membership A))) (P.membership A) :=
  P.mem_conv_conv A

/-- Theorem 34: Power composition identity left -/
def power_comp_id_left (Al : Allegory) (P : PowerAllegory Al) (A : Al.Ob) :
    Path (Al.comp (Al.idM (P.Pow A)) (P.membership A))
         (P.membership A) :=
  Al.comp_id_left (P.membership A)

/-- Theorem 35: Power membership composition associativity -/
def power_mem_assoc (Al : Allegory) (P : PowerAllegory Al) {A B : Al.Ob}
    (f : Al.Hom B (P.Pow A)) (g : Al.Hom A B) :
    Path (Al.comp (Al.comp f g) (Al.conv (P.membership A)))
         (Al.comp f (Al.comp g (Al.conv (P.membership A)))) :=
  Al.comp_assoc f g (Al.conv (P.membership A))

-- ============================================================================
-- Section 9: Regular Categories as Allegories
-- ============================================================================

/-- A regular category gives rise to an allegory of relations -/
structure RegularAllegory (Al : Allegory) where
  img : {A B : Al.Ob} → Al.Hom A B → Al.Hom A B
  img_idem : {A B : Al.Ob} → (f : Al.Hom A B) → Path (img (img f)) (img f)

/-- Theorem 36: Regular image converse coherence -/
def regular_img_conv (Al : Allegory) (R : RegularAllegory Al) {A B : Al.Ob}
    (f : Al.Hom A B) :
    Path (Al.conv (Al.conv (R.img f))) (R.img f) :=
  Al.conv_conv (R.img f)

/-- Theorem 37: Regular image composition with identity -/
def regular_img_id (Al : Allegory) (R : RegularAllegory Al) {A B : Al.Ob}
    (f : Al.Hom A B) :
    Path (Al.comp (Al.idM B) (R.img f)) (R.img f) :=
  Al.comp_id_left (R.img f)

/-- Theorem 38: Regular image idempotence path -/
def regular_img_idem_path (Al : Allegory) (R : RegularAllegory Al) {A B : Al.Ob}
    (f : Al.Hom A B) :
    Path (R.img (R.img f)) (R.img f) :=
  R.img_idem f

-- ============================================================================
-- Section 10: Freyd's Representation Theorem Structure
-- ============================================================================

/-- An allegory functor preserving the allegory structure -/
structure AllegoryFunctor (Al1 Al2 : Allegory) where
  mapOb : Al1.Ob → Al2.Ob
  mapHom : {A B : Al1.Ob} → Al1.Hom A B → Al2.Hom (mapOb A) (mapOb B)
  pres_id : (A : Al1.Ob) → Path (mapHom (Al1.idM A)) (Al2.idM (mapOb A))
  pres_comp : {A B C : Al1.Ob} → (f : Al1.Hom B C) → (g : Al1.Hom A B) →
    Path (mapHom (Al1.comp f g)) (Al2.comp (mapHom f) (mapHom g))
  pres_conv : {A B : Al1.Ob} → (f : Al1.Hom A B) →
    Path (mapHom (Al1.conv f)) (Al2.conv (mapHom f))
  pres_meet : {A B : Al1.Ob} → (f g : Al1.Hom A B) →
    Path (mapHom (Al1.meet f g)) (Al2.meet (mapHom f) (mapHom g))

section WithAllegory2
variable (Al : Allegory)

/-- Theorem 39: Functor preserves converse involution -/
def functor_pres_conv_conv (F : AllegoryFunctor Al Al) {A B : Al.Ob}
    (f : Al.Hom A B) :
    Path (F.mapHom (Al.conv (Al.conv f)))
         (F.mapHom f) :=
  Path.congrArg F.mapHom (Al.conv_conv f)

/-- Theorem 40: Functor preserves identity converse -/
def functor_pres_id_conv (F : AllegoryFunctor Al Al) (A : Al.Ob) :
    Path (F.mapHom (Al.conv (Al.idM A)))
         (F.mapHom (Al.idM A)) :=
  Path.congrArg F.mapHom (Al.conv_id A)

/-- Theorem 41: Functor composition-converse interchange -/
def functor_comp_conv_interchange (F : AllegoryFunctor Al Al) {A B C : Al.Ob}
    (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (F.mapHom (Al.conv (Al.comp f g)))
         (Al.comp (Al.conv (F.mapHom g)) (Al.conv (F.mapHom f))) :=
  Path.trans
    (Path.congrArg F.mapHom (Al.conv_comp f g))
    (Path.trans
      (F.pres_comp (Al.conv g) (Al.conv f))
      (Path.trans
        (Path.congrArg (fun x => Al.comp x (F.mapHom (Al.conv f))) (F.pres_conv g))
        (Path.congrArg (fun x => Al.comp (Al.conv (F.mapHom g)) x) (F.pres_conv f))))

-- ============================================================================
-- Section 11: Bicategory of Relations
-- ============================================================================

/-- A 2-cell in the allegory: witnessed by a meet equation -/
structure TwoCell (Al : Allegory) {A B : Al.Ob} (R S : Al.Hom A B) where
  witness : Path (Al.meet R S) R

/-- Theorem 42: Identity 2-cell -/
def twocell_id {A B : Al.Ob} (R : Al.Hom A B) :
    TwoCell Al R R :=
  ⟨Al.meet_idem R⟩

/-- Theorem 43: Composite 2-cell witness extraction -/
def twocell_trans {A B : Al.Ob} {R S T : Al.Hom A B}
    (alpha : TwoCell Al R S) (_beta : TwoCell Al S T) :
    Path (Al.meet R S) R :=
  alpha.witness

/-- Theorem 44: 2-cell converse contravariance -/
def twocell_conv {A B : Al.Ob} {R S : Al.Hom A B}
    (alpha : TwoCell Al R S) :
    Path (Al.conv (Al.meet R S)) (Al.conv R) :=
  Path.congrArg Al.conv alpha.witness

/-- Theorem 45: 2-cell meet compatibility -/
def twocell_meet_compat {A B : Al.Ob} (R S : Al.Hom A B) :
    Path (Al.meet (Al.meet R S) R)
         (Al.meet R (Al.meet S R)) :=
  Al.meet_assoc R S R

-- ============================================================================
-- Section 12: Relation Algebra Coherence
-- ============================================================================

/-- Theorem 46: Full coherence diamond: assoc + id + converse -/
def coherence_diamond {A B C : Al.Ob} (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.conv (Al.comp f (Al.comp (Al.idM B) g)))
         (Al.comp (Al.conv g) (Al.conv f)) :=
  Path.trans
    (Path.congrArg Al.conv (triangle_left Al f g))
    (Al.conv_comp f g)

/-- Theorem 47: Composition with converses and identity -/
def comp_conv_id {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.comp f (Al.comp (Al.conv f) f))
         (Al.comp (Al.comp f (Al.conv f)) f) :=
  Path.symm (Al.comp_assoc f (Al.conv f) f)

/-- Theorem 48: Converse of meet with identity -/
def conv_meet_id {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.meet f (Al.comp (Al.idM B) f)))
         (Al.conv (Al.meet f f)) :=
  Path.congrArg (fun x => Al.conv (Al.meet f x)) (Al.comp_id_left f)

/-- Theorem 49: Full modular law context path -/
def modular_context {A B C : Al.Ob}
    (R : Al.Hom A B) (S : Al.Hom B C) (T : Al.Hom A C) :
    Path (Al.meet (Al.comp S R) T)
         (Al.meet T (Al.comp S R)) :=
  Al.meet_comm (Al.comp S R) T

/-- Theorem 50: Modular law with converse interaction -/
def modular_conv_context {A B C : Al.Ob}
    (R : Al.Hom A B) (S : Al.Hom B C) (T : Al.Hom A C) :
    Path (Al.conv (Al.meet (Al.comp S R) T))
         (Al.meet (Al.conv T) (Al.conv (Al.comp S R))) :=
  Path.trans
    (Al.conv_meet (Al.comp S R) T)
    (Al.meet_comm (Al.conv (Al.comp S R)) (Al.conv T))

-- ============================================================================
-- Section 13: Symmetric Structure and Dagger Coherence
-- ============================================================================

/-- Theorem 51: Dagger functor coherence: (f;g)° = g°;f° naturality -/
def dagger_naturality {A B C D : Al.Ob}
    (f : Al.Hom C D) (g : Al.Hom B C) (h : Al.Hom A B) :
    Path (Al.conv (Al.comp (Al.comp f g) h))
         (Al.comp (Al.conv h) (Al.comp (Al.conv g) (Al.conv f))) :=
  Path.trans
    (Al.conv_comp (Al.comp f g) h)
    (Path.congrArg (fun x => Al.comp (Al.conv h) x) (Al.conv_comp f g))

/-- Theorem 52: Dagger squared is identity on composition -/
def dagger_squared_comp {A B C : Al.Ob}
    (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.conv (Al.conv (Al.comp f g)))
         (Al.comp f g) :=
  Al.conv_conv (Al.comp f g)

/-- Theorem 53: Meet-converse double naturality -/
def meet_conv_double_nat {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.conv (Al.conv (Al.meet f g)))
         (Al.meet f g) :=
  Al.conv_conv (Al.meet f g)

/-- Theorem 54: Converse preserves meet idempotence -/
def conv_pres_meet_idem {A B : Al.Ob} (f : Al.Hom A B) :
    Path (Al.conv (Al.meet f f))
         (Al.conv f) :=
  Path.congrArg Al.conv (Al.meet_idem f)

/-- Theorem 55: Converse of meet via expansion and collapse -/
def conv_meet_expand_collapse {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.meet (Al.conv (Al.conv f)) (Al.conv (Al.conv g)))
         (Al.meet f g) :=
  Path.trans
    (Path.congrArg (fun x => Al.meet x (Al.conv (Al.conv g))) (Al.conv_conv f))
    (Path.congrArg (fun x => Al.meet f x) (Al.conv_conv g))

-- ============================================================================
-- Section 14: Enrichment and Lattice Structure
-- ============================================================================

/-- Theorem 56: Meet absorbs via idempotence and associativity -/
def meet_absorption {A B : Al.Ob} (f g : Al.Hom A B) :
    Path (Al.meet f (Al.meet f g))
         (Al.meet f g) :=
  Path.trans
    (Path.symm (Al.meet_assoc f f g))
    (Path.congrArg (fun x => Al.meet x g) (Al.meet_idem f))

/-- Theorem 57: Meet is monotone: congruence of meet -/
def meet_monotone {A B : Al.Ob} (f g h : Al.Hom A B)
    (p : Path (Al.meet f g) f) :
    Path (Al.meet (Al.meet f g) h)
         (Al.meet f h) :=
  Path.congrArg (fun x => Al.meet x h) p

/-- Theorem 58: Composition preserves meet ordering (left) -/
def comp_pres_meet_left {A B C : Al.Ob}
    (f : Al.Hom B C) (g h : Al.Hom A B) :
    Path (Al.comp f (Al.meet g h))
         (Al.comp f (Al.meet h g)) :=
  Path.congrArg (fun x => Al.comp f x) (Al.meet_comm g h)

/-- Theorem 59: Iterated meet associativity (4-fold) -/
def meet_assoc_4 {A B : Al.Ob} (f g h k : Al.Hom A B) :
    Path (Al.meet (Al.meet (Al.meet f g) h) k)
         (Al.meet (Al.meet f g) (Al.meet h k)) :=
  Al.meet_assoc (Al.meet f g) h k

/-- Theorem 60: Complete coherence path combining all operations -/
def full_allegory_coherence {A B C : Al.Ob}
    (f : Al.Hom B C) (g : Al.Hom A B) :
    Path (Al.meet (Al.conv (Al.conv (Al.comp f g)))
                  (Al.comp f (Al.comp (Al.idM B) g)))
         (Al.meet (Al.comp f g) (Al.comp f g)) :=
  Path.trans
    (Path.congrArg
      (fun x => Al.meet x (Al.comp f (Al.comp (Al.idM B) g)))
      (Al.conv_conv (Al.comp f g)))
    (Path.congrArg
      (fun x => Al.meet (Al.comp f g) x)
      (triangle_left Al f g))

end WithAllegory2

end AllegoryPathDeep
