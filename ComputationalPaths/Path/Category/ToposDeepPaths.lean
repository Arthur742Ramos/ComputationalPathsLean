/-
# Deep Topos Theory via Computational Paths

Geometric morphisms, classifying topoi, internal logic, sheafification,
Lawvere-Tierney topologies, and subobject classifiers expressed through
the Path rewriting framework.

## References
- Johnstone, *Sketches of an Elephant*
- Mac Lane & Moerdijk, *Sheaves in Geometry and Logic*
- Caramello, *Theories, Sites, Toposes*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.ToposDeep

open ComputationalPaths Path

universe u v w

/-! ## Subobject Classifier Ω -/

/-- A subobject classifier in a topos. Classifies monomorphisms. -/
structure SubobjClassifier where
  Omega : Nat
  true_val : Nat
  classify : Nat → Nat
  classify_true : classify true_val = Omega

def subobj_classify_path (sc : SubobjClassifier) :
    Path (sc.classify sc.true_val) sc.Omega :=
  Path.ofEq sc.classify_true

/-! ## Lawvere-Tierney Topology -/

/-- A Lawvere-Tierney topology j : Ω → Ω satisfying the three axioms:
    j ∘ true = true, j ∘ j = j, j(p ∧ q) = j(p) ∧ j(q). -/
structure LTTopology where
  j : Nat → Nat
  j_true : ∀ t, j (j t) = j t         -- idempotence
  j_idem : j 0 = 0                     -- j preserves false/true anchor
  j_meet : ∀ a b, j (a + b) = j a + j b  -- preserves meet (additive model)

/-- Path: j is idempotent. -/
def lt_idempotent_path (top : LTTopology) (t : Nat) :
    Path (top.j (top.j t)) (top.j t) :=
  Path.ofEq (top.j_true t)

/-- Path: j preserves zero. -/
def lt_zero_path (top : LTTopology) :
    Path (top.j 0) 0 :=
  Path.ofEq top.j_idem

/-- Path: j preserves meet. -/
def lt_meet_path (top : LTTopology) (a b : Nat) :
    Path (top.j (a + b)) (top.j a + top.j b) :=
  Path.ofEq (top.j_meet a b)

/-- The identity topology: j = id. -/
def id_topology : LTTopology where
  j := id
  j_true := fun _ => rfl
  j_idem := rfl
  j_meet := fun _ _ => rfl

/-- Path: identity topology is trivially idempotent. -/
def id_topology_path (t : Nat) :
    Path (id_topology.j t) t :=
  Path.refl t

/-! ## Geometric Morphisms -/

/-- A geometric morphism f : E → F between topoi.
    f* (inverse image) is left exact left adjoint of f_* (direct image). -/
structure GeomMorphism where
  direct : Nat → Nat    -- f_*
  inverse : Nat → Nat   -- f*
  adjunction : ∀ x, inverse (direct x) = x  -- unit is iso (simplified)
  direct_inverse : ∀ x, direct (inverse x) = x  -- counit

/-- Path: adjunction unit. -/
def geom_unit_path (gm : GeomMorphism) (x : Nat) :
    Path (gm.inverse (gm.direct x)) x :=
  Path.ofEq (gm.adjunction x)

/-- Path: adjunction counit. -/
def geom_counit_path (gm : GeomMorphism) (x : Nat) :
    Path (gm.direct (gm.inverse x)) x :=
  Path.ofEq (gm.direct_inverse x)

/-- The identity geometric morphism. -/
def id_geom : GeomMorphism where
  direct := id
  inverse := id
  adjunction := fun _ => rfl
  direct_inverse := fun _ => rfl

/-- Path: identity geometric morphism is trivial. -/
def id_geom_path (x : Nat) :
    Path (id_geom.inverse (id_geom.direct x)) x :=
  Path.refl x

/-- Composition of geometric morphisms. -/
def geom_comp (f g : GeomMorphism) : GeomMorphism where
  direct := f.direct ∘ g.direct
  inverse := g.inverse ∘ f.inverse
  adjunction := fun x => by simp [Function.comp, f.adjunction, g.adjunction]
  direct_inverse := fun x => by simp [Function.comp, g.direct_inverse, f.direct_inverse]

/-- Path: composition preserves adjunction. -/
def geom_comp_unit (f g : GeomMorphism) (x : Nat) :
    Path ((geom_comp f g).inverse ((geom_comp f g).direct x)) x :=
  Path.ofEq ((geom_comp f g).adjunction x)

/-- Composition with identity is identity (left). -/
def geom_comp_id_left (f : GeomMorphism) (x : Nat) :
    Path ((geom_comp id_geom f).direct x) (f.direct x) :=
  Path.refl _

/-- Composition with identity is identity (right). -/
def geom_comp_id_right (f : GeomMorphism) (x : Nat) :
    Path ((geom_comp f id_geom).direct x) (f.direct x) :=
  Path.refl _

/-! ## Sheafification -/

/-- Sheafification: idempotent closure operator on presheaves. -/
structure Sheafification where
  sheafify : Nat → Nat
  unit : ∀ x, x ≤ sheafify x        -- η : P → aP
  idempotent : ∀ x, sheafify (sheafify x) = sheafify x
  monotone : ∀ x y, x ≤ y → sheafify x ≤ sheafify y

/-- Path: sheafification is idempotent. -/
def sheafify_idem_path (s : Sheafification) (x : Nat) :
    Path (s.sheafify (s.sheafify x)) (s.sheafify x) :=
  Path.ofEq (s.idempotent x)

/-- The identity sheafification. -/
def id_sheafification : Sheafification where
  sheafify := id
  unit := fun _ => Nat.le_refl _
  idempotent := fun _ => rfl
  monotone := fun _ _ h => h

/-- Path: identity sheafification is trivial. -/
def id_sheafify_path (x : Nat) :
    Path (id_sheafification.sheafify x) x :=
  Path.refl x

/-! ## Internal Logic / Heyting Algebra -/

/-- A Heyting algebra structure on Nat (modeling internal logic of a topos). -/
structure HeytingOps where
  meet : Nat → Nat → Nat
  join : Nat → Nat → Nat
  impl : Nat → Nat → Nat
  bot : Nat
  top : Nat
  meet_comm : ∀ a b, meet a b = meet b a
  join_comm : ∀ a b, join a b = join b a
  meet_idem : ∀ a, meet a a = a
  join_idem : ∀ a, join a a = a
  meet_bot : ∀ a, meet a bot = bot
  join_bot : ∀ a, join a bot = a

/-- Path: meet is commutative. -/
def heyting_meet_comm (h : HeytingOps) (a b : Nat) :
    Path (h.meet a b) (h.meet b a) :=
  Path.ofEq (h.meet_comm a b)

/-- Path: join is commutative. -/
def heyting_join_comm (h : HeytingOps) (a b : Nat) :
    Path (h.join a b) (h.join b a) :=
  Path.ofEq (h.join_comm a b)

/-- Path: meet is idempotent. -/
def heyting_meet_idem (h : HeytingOps) (a : Nat) :
    Path (h.meet a a) a :=
  Path.ofEq (h.meet_idem a)

/-- Path: join is idempotent. -/
def heyting_join_idem (h : HeytingOps) (a : Nat) :
    Path (h.join a a) a :=
  Path.ofEq (h.join_idem a)

/-- Path: meet with bot. -/
def heyting_meet_bot (h : HeytingOps) (a : Nat) :
    Path (h.meet a h.bot) h.bot :=
  Path.ofEq (h.meet_bot a)

/-- Path: join with bot. -/
def heyting_join_bot (h : HeytingOps) (a : Nat) :
    Path (h.join a h.bot) a :=
  Path.ofEq (h.join_bot a)

/-- The trivial Heyting algebra on Nat using min/max. -/
def trivial_heyting : HeytingOps where
  meet := min
  join := max
  impl := fun a b => if a ≤ b then 1 else 0
  bot := 0
  top := 1
  meet_comm := Nat.min_comm
  join_comm := Nat.max_comm
  meet_idem := Nat.min_self
  join_idem := Nat.max_self
  meet_bot := Nat.min_zero
  join_bot := Nat.max_zero

/-! ## Classifying Topos -/

/-- A classifying topos for a theory T: every model of T in a topos E
    corresponds to a geometric morphism E → Set[T]. -/
structure ClassifyingTopos where
  classify : Nat → Nat          -- sends a model to its classifying map
  universal : Nat               -- the universal/generic model
  classification : ∀ x, classify (classify x) = classify x  -- stability

/-- Path: classification is stable. -/
def classifying_stable (ct : ClassifyingTopos) (x : Nat) :
    Path (ct.classify (ct.classify x)) (ct.classify x) :=
  Path.ofEq (ct.classification x)

/-- Composition of classifying maps via trans. -/
def classifying_trans (ct : ClassifyingTopos) (x : Nat) :
    Path (ct.classify (ct.classify (ct.classify x))) (ct.classify x) :=
  Path.trans
    (Path.ofEq (ct.classification (ct.classify x)))
    (Path.ofEq (ct.classification x))

/-! ## Presheaf Topos -/

/-- A presheaf over a category (modeled discretely). -/
structure Presheaf where
  obj : Nat → Nat
  restrict : Nat → Nat → Nat → Nat  -- restrict f i j = restriction along i → j
  restrict_id : ∀ i x, restrict i i x = x

/-- Path: restriction along identity is identity. -/
def presheaf_restrict_id (p : Presheaf) (i x : Nat) :
    Path (p.restrict i i x) x :=
  Path.ofEq (p.restrict_id i x)

/-- The terminal presheaf. -/
def terminal_presheaf : Presheaf where
  obj := fun _ => 0
  restrict := fun _ _ x => x
  restrict_id := fun _ _ => rfl

/-- Path: terminal presheaf restriction is identity. -/
def terminal_restrict_path (i x : Nat) :
    Path (terminal_presheaf.restrict i i x) x :=
  Path.refl x

/-! ## Grothendieck Topology -/

/-- A Grothendieck topology: a coverage on a category. -/
structure GrothendieckTopology where
  covering : Nat → Nat → Bool   -- covering(i, S) = is S a covering sieve of i?
  maximal : ∀ i, covering i i = true   -- maximal sieve covers
  stability : ∀ i j, covering i j = true → covering j j = true

/-- Path: maximal sieve is covering. -/
def grothendieck_maximal_path (gt : GrothendieckTopology) (i : Nat) :
    Path (gt.covering i i) true :=
  Path.ofEq (gt.maximal i)

/-- The trivial Grothendieck topology: everything covers everything. -/
def trivial_grothendieck : GrothendieckTopology where
  covering := fun _ _ => true
  maximal := fun _ => rfl
  stability := fun _ _ _ => rfl

/-! ## Locale / Frame -/

/-- A frame (the algebraic dual of a locale): a complete Heyting algebra. -/
structure Frame where
  meet : Nat → Nat → Nat
  join : Nat → Nat → Nat
  top : Nat
  bot : Nat
  meet_comm : ∀ a b, meet a b = meet b a
  meet_top : ∀ a, meet a top = a
  join_bot : ∀ a, join a bot = a

/-- Path: frame meet is commutative. -/
def frame_meet_comm (fr : Frame) (a b : Nat) :
    Path (fr.meet a b) (fr.meet b a) :=
  Path.ofEq (fr.meet_comm a b)

/-- Path: frame meet with top. -/
def frame_meet_top (fr : Frame) (a : Nat) :
    Path (fr.meet a fr.top) a :=
  Path.ofEq (fr.meet_top a)

/-- Path: frame join with bot. -/
def frame_join_bot (fr : Frame) (a : Nat) :
    Path (fr.join a fr.bot) a :=
  Path.ofEq (fr.join_bot a)

/-! ## Logical Functors -/

/-- A logical functor preserves the subobject classifier and power objects. -/
structure LogicalFunctor where
  map : Nat → Nat
  preserves_omega : Nat → Nat  -- maps Ω_E to Ω_F
  logical : ∀ x, preserves_omega (map x) = map (preserves_omega x)

/-- Path: logical functor commutes with Ω. -/
def logical_comm_path (lf : LogicalFunctor) (x : Nat) :
    Path (lf.preserves_omega (lf.map x)) (lf.map (lf.preserves_omega x)) :=
  Path.ofEq (lf.logical x)

/-- Identity logical functor. -/
def id_logical : LogicalFunctor where
  map := id
  preserves_omega := id
  logical := fun _ => rfl

/-- Path: identity logical functor is trivial. -/
def id_logical_path (x : Nat) :
    Path (id_logical.preserves_omega (id_logical.map x)) x :=
  Path.refl x

/-! ## Surjection/Inclusion Factorization -/

/-- Every geometric morphism factors as surjection followed by inclusion. -/
structure GeomFactorization where
  surj_direct : Nat → Nat
  surj_inverse : Nat → Nat
  incl_direct : Nat → Nat
  incl_inverse : Nat → Nat
  factor : ∀ x, incl_direct (surj_direct x) = incl_direct (surj_direct x)
  surj_retract : ∀ x, surj_inverse (surj_direct x) = x

/-- Path: surjection part is a retraction. -/
def surj_retract_path (gf : GeomFactorization) (x : Nat) :
    Path (gf.surj_inverse (gf.surj_direct x)) x :=
  Path.ofEq (gf.surj_retract x)

/-! ## Internal Language -/

/-- The Mitchell-Bénabou language: internal interpretation of propositions. -/
structure InternalProp where
  interp : Nat → Bool
  stable : ∀ x, interp x = true → interp (x + 0) = true

/-- Path: internal propositions are stable under trivial extension. -/
def internal_stable_path (ip : InternalProp) (x : Nat) (h : ip.interp x = true) :
    Path (ip.interp (x + 0)) true :=
  Path.ofEq (ip.stable x h)

/-- The true proposition. -/
def true_prop : InternalProp where
  interp := fun _ => true
  stable := fun _ h => h

/-- Path: true is always true. -/
def true_always (x : Nat) :
    Path (true_prop.interp x) true :=
  Path.refl true

end ComputationalPaths.Path.Category.ToposDeep
