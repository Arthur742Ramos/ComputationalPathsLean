/-
# Deep Enriched Category Theory via Computational Paths

Enriched categories where hom-objects ARE Path types, composition IS trans,
enriched functors, enriched natural transformations, ends/coends as path
limits. Pentagon and triangle coherence via multi-step trans chains.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths

open Path

universe u v w

namespace EnrichedDeep

variable {A : Type u}

/-! ## Enriched Hom-Object: Path types as the enrichment -/

/-- The hom-object in our enriched category: the type of paths from a to b. -/
noncomputable def Hom (a b : A) := Path a b

/-- Identity morphism in the enriched sense: refl as the unit. -/
noncomputable def homId (a : A) : Hom a a := Path.refl a

/-- Composition in the enriched category: trans IS composition. -/
noncomputable def homComp {a b c : A} (f : Hom a b) (g : Hom b c) : Hom a c :=
  Path.trans f g

/-! ## Enriched Category Laws via multi-step trans chains -/

/-- Left unit: composing with identity on the left yields the original.
    Multi-step: unfold homComp, apply trans_refl_left. -/
theorem homComp_id_left {a b : A} (f : Hom a b) :
    homComp (homId a) f = f := by
  unfold homComp homId
  exact Path.trans_refl_left f

/-- Right unit: composing with identity on the right yields the original. -/
theorem homComp_id_right {a b : A} (f : Hom a b) :
    homComp f (homId b) = f := by
  unfold homComp homId
  exact Path.trans_refl_right f

/-- Associativity of enriched composition via multi-step proof. -/
theorem homComp_assoc {a b c d : A} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    homComp (homComp f g) h = homComp f (homComp g h) := by
  unfold homComp
  exact Path.trans_assoc f g h

/-! ## Enriched symmetry structure (dagger/involutive enrichment) -/

/-- The enriched dagger: symm gives each hom an involution. -/
noncomputable def homDagger {a b : A} (f : Hom a b) : Hom b a :=
  Path.symm f

/-- Dagger is involutive: applying it twice recovers the original.
    Multi-step: unfold dagger twice, apply symm_symm. -/
theorem homDagger_involutive {a b : A} (f : Hom a b) :
    homDagger (homDagger f) = f := by
  unfold homDagger
  exact Path.symm_symm f

/-- Dagger reverses composition: dagger of a composition = composition of daggers in reverse.
    Uses trans chain through symm_trans. -/
theorem homDagger_comp {a b c : A} (f : Hom a b) (g : Hom b c) :
    homDagger (homComp f g) = homComp (homDagger g) (homDagger f) := by
  unfold homDagger homComp
  exact Path.symm_trans f g

/-- Dagger of the identity is the identity. -/
theorem homDagger_id (a : A) : homDagger (homId a) = homId a := by
  unfold homDagger homId
  exact Path.symm_refl a

/-! ## Enriched Functor -/

/-- An enriched functor maps objects and acts on hom-objects via congrArg. -/
structure EnrichedFunctor (A : Type u) (B : Type v) where
  obj : A → B
  map : {a₁ a₂ : A} → Hom a₁ a₂ → Hom (obj a₁) (obj a₂)
  map_def : ∀ {a₁ a₂ : A} (f : Hom a₁ a₂), map f = Path.congrArg obj f

namespace EnrichedFunctor

variable {B : Type v} {C : Type w}

/-- An enriched functor preserves identities. Multi-step trans chain. -/
theorem map_id (F : EnrichedFunctor A B) (a : A) :
    F.map (homId a) = homId (F.obj a) := by
  rw [F.map_def]
  unfold homId
  simp [Path.congrArg]

/-- An enriched functor preserves composition. Multi-step using congrArg_trans. -/
theorem map_comp (F : EnrichedFunctor A B) {a b c : A}
    (f : Hom a b) (g : Hom b c) :
    F.map (homComp f g) = homComp (F.map f) (F.map g) := by
  rw [F.map_def, F.map_def, F.map_def]
  unfold homComp
  exact Path.congrArg_trans F.obj f g

/-- An enriched functor commutes with dagger. Multi-step using congrArg_symm. -/
theorem map_dagger (F : EnrichedFunctor A B) {a b : A}
    (f : Hom a b) :
    F.map (homDagger f) = homDagger (F.map f) := by
  rw [F.map_def, F.map_def]
  unfold homDagger
  exact Path.congrArg_symm F.obj f

/-- Composition of enriched functors. -/
noncomputable def comp (F : EnrichedFunctor A B) (G : EnrichedFunctor B C) : EnrichedFunctor A C where
  obj := G.obj ∘ F.obj
  map := fun f => G.map (F.map f)
  map_def := fun f => by
    rw [F.map_def, G.map_def]
    exact (Path.congrArg_comp G.obj F.obj f).symm

/-- Composition of enriched functors preserves composition of morphisms.
    Multi-step: unfold comp, use map_comp twice. -/
theorem comp_map_comp (F : EnrichedFunctor A B) (G : EnrichedFunctor B C)
    {a b c : A} (f : Hom a b) (g : Hom b c) :
    (comp F G).map (homComp f g) = homComp ((comp F G).map f) ((comp F G).map g) := by
  show G.map (F.map (homComp f g)) = homComp (G.map (F.map f)) (G.map (F.map g))
  rw [map_comp F f g]
  exact map_comp G (F.map f) (F.map g)

end EnrichedFunctor

/-! ## Enriched Natural Transformation -/

/-- An enriched natural transformation between enriched functors.
    Components are paths, naturality is a path equation. -/
structure EnrichedNatTrans {B : Type v}
    (F G : EnrichedFunctor A B) where
  component : (a : A) → Hom (F.obj a) (G.obj a)
  naturality : ∀ {a₁ a₂ : A} (f : Hom a₁ a₂),
    homComp (F.map f) (component a₂) = homComp (component a₁) (G.map f)

namespace EnrichedNatTrans

variable {B : Type v}

/-- Identity natural transformation. Multi-step: verify naturality via
    trans_refl_right and trans_refl_left. -/
noncomputable def id (F : EnrichedFunctor A B) : EnrichedNatTrans F F where
  component := fun a => homId (F.obj a)
  naturality := fun f => by
    show homComp (F.map f) (homId _) = homComp (homId _) (F.map f)
    rw [homComp_id_right, homComp_id_left]

/-- Vertical composition of natural transformations.
    Components composed via trans, naturality by multi-step chain. -/
noncomputable def vcomp {F G H : EnrichedFunctor A B}
    (α : EnrichedNatTrans F G) (β : EnrichedNatTrans G H) :
    EnrichedNatTrans F H where
  component := fun a => homComp (α.component a) (β.component a)
  naturality := fun {a₁ a₂} f => by
    -- Goal: homComp (F.map f) (homComp (α a₂) (β a₂))
    --     = homComp (homComp (α a₁) (β a₁)) (H.map f)
    -- Step 1: reassociate left side
    have step1 : homComp (F.map f) (homComp (α.component a₂) (β.component a₂))
      = homComp (homComp (F.map f) (α.component a₂)) (β.component a₂) :=
      (homComp_assoc (F.map f) (α.component a₂) (β.component a₂)).symm
    -- Step 2: use α naturality
    have step2 : homComp (F.map f) (α.component a₂) = homComp (α.component a₁) (G.map f) :=
      α.naturality f
    -- Step 3: substitute
    have step3 : homComp (homComp (α.component a₁) (G.map f)) (β.component a₂)
      = homComp (α.component a₁) (homComp (G.map f) (β.component a₂)) :=
      homComp_assoc (α.component a₁) (G.map f) (β.component a₂)
    -- Step 4: use β naturality
    have step4 : homComp (G.map f) (β.component a₂) = homComp (β.component a₁) (H.map f) :=
      β.naturality f
    -- Step 5: reassociate
    have step5 : homComp (α.component a₁) (homComp (β.component a₁) (H.map f))
      = homComp (homComp (α.component a₁) (β.component a₁)) (H.map f) :=
      (homComp_assoc (α.component a₁) (β.component a₁) (H.map f)).symm
    -- Compose all steps
    calc homComp (F.map f) (homComp (α.component a₂) (β.component a₂))
        = homComp (homComp (F.map f) (α.component a₂)) (β.component a₂) := step1
      _ = homComp (homComp (α.component a₁) (G.map f)) (β.component a₂) := by rw [step2]
      _ = homComp (α.component a₁) (homComp (G.map f) (β.component a₂)) := step3
      _ = homComp (α.component a₁) (homComp (β.component a₁) (H.map f)) := by rw [step4]
      _ = homComp (homComp (α.component a₁) (β.component a₁)) (H.map f) := step5

/-- Left identity for vertical composition. -/
theorem vcomp_id_left {F G : EnrichedFunctor A B}
    (α : EnrichedNatTrans F G) :
    (vcomp (id F) α).component = α.component := by
  funext a
  show homComp (homId (F.obj a)) (α.component a) = α.component a
  exact homComp_id_left (α.component a)

/-- Right identity for vertical composition. -/
theorem vcomp_id_right {F G : EnrichedFunctor A B}
    (α : EnrichedNatTrans F G) :
    (vcomp α (id G)).component = α.component := by
  funext a
  show homComp (α.component a) (homId (G.obj a)) = α.component a
  exact homComp_id_right (α.component a)

end EnrichedNatTrans

/-! ## Pentagon coherence for enriched composition -/

/-- Pentagon identity: the two canonical ways to reassociate a 4-fold
    composition agree. Multi-step calc chain through trans_assoc applications. -/
theorem pentagon_coherence {a b c d e : A}
    (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    -- Route 1: ((fg)h)k → (fg)(hk) → f(g(hk))
    -- Route 2: ((fg)h)k → (f(gh))k → f((gh)k) → f(g(hk))
    -- Both routes yield the same result
    homComp (homComp (homComp f g) h) k = homComp f (homComp g (homComp h k)) := by
  unfold homComp
  exact Path.trans_assoc_fourfold f g h k

/-- Pentagon route 1: reassociate outer then inner. -/
theorem pentagon_route1 {a b c d e : A}
    (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    homComp (homComp (homComp f g) h) k = homComp f (homComp g (homComp h k)) := by
  unfold homComp
  calc Path.trans (Path.trans (Path.trans f g) h) k
      = Path.trans (Path.trans f g) (Path.trans h k) := Path.trans_assoc _ h k
    _ = Path.trans f (Path.trans g (Path.trans h k)) := Path.trans_assoc f g _

/-- Pentagon route 2: reassociate inner then outer. -/
theorem pentagon_route2 {a b c d e : A}
    (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    homComp (homComp (homComp f g) h) k = homComp f (homComp g (homComp h k)) := by
  unfold homComp
  calc Path.trans (Path.trans (Path.trans f g) h) k
      = Path.trans (Path.trans f (Path.trans g h)) k := by
          rw [Path.trans_assoc f g h]
    _ = Path.trans f (Path.trans (Path.trans g h) k) := Path.trans_assoc f _ k
    _ = Path.trans f (Path.trans g (Path.trans h k)) := by
          rw [Path.trans_assoc g h k]

/-- Pentagon routes are equal (coherence). -/
theorem pentagon_routes_agree {a b c d e : A}
    (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    pentagon_route1 f g h k = pentagon_route2 f g h k := by
  apply Subsingleton.elim

/-! ## Triangle coherence for the enriched unit -/

/-- Triangle identity: the two ways to simplify f ∘ id ∘ g agree.
    Multi-step calc chain. -/
theorem triangle_coherence {a b c : A}
    (f : Hom a b) (g : Hom b c) :
    homComp (homComp f (homId b)) g = homComp f g := by
  unfold homComp homId
  calc Path.trans (Path.trans f (Path.refl b)) g
      = Path.trans f (Path.trans (Path.refl b) g) := Path.trans_assoc f _ g
    _ = Path.trans f g := by rw [Path.trans_refl_left g]

/-- Triangle right: simplifying id ∘ g inside a composition. -/
theorem triangle_right {a b c : A}
    (f : Hom a b) (g : Hom b c) :
    homComp f (homComp (homId b) g) = homComp f g := by
  unfold homComp homId
  rw [Path.trans_refl_left g]

/-- Both triangle routes agree. -/
theorem triangle_routes_agree {a b c : A}
    (f : Hom a b) (g : Hom b c) :
    triangle_coherence f g =
    Eq.trans (homComp_assoc f (homId b) g) (triangle_right f g) := by
  apply Subsingleton.elim

/-! ## Enriched transport structure -/

/-- Transport along an enriched hom-object acts on dependent types.
    Multi-step: unfold to Path.transport, use its properties. -/
theorem enriched_transport_comp {D : A → Type v} {a b c : A}
    (f : Hom a b) (g : Hom b c) (x : D a) :
    Path.transport (homComp f g) x = Path.transport g (Path.transport f x) := by
  unfold homComp
  exact Path.transport_trans f g x

/-- Transport along dagger is inverse to transport.
    Multi-step using transport_symm_left. -/
theorem enriched_transport_dagger_left {D : A → Type v} {a b : A}
    (f : Hom a b) (x : D a) :
    Path.transport (homDagger f) (Path.transport f x) = x := by
  unfold homDagger
  exact Path.transport_symm_left f x

/-- Transport along dagger is inverse on the other side. -/
theorem enriched_transport_dagger_right {D : A → Type v} {a b : A}
    (f : Hom a b) (y : D b) :
    Path.transport f (Path.transport (homDagger f) y) = y := by
  unfold homDagger
  exact Path.transport_symm_right f y

/-! ## Ends as equalizers over path actions -/

/-- An end over a bifunctor: an element compatible with all path actions.
    This is the path-enriched analogue of ∫_c T(c,c). -/
structure PathEnd (T : A → A → Type v) where
  elem : (a : A) → T a a
  wedge : ∀ {a b : A} (f : Hom a b),
    Path.transport (D := fun x => T a x) f (elem a) =
    Path.transport (D := fun x => T x b) (homDagger f) (elem b)

/-- A coend cocone: elements in target compatible with path actions. -/
structure PathCoend (T : A → A → Type v) (X : Type v) where
  inject : (a : A) → T a a → X
  cowedge : ∀ {a b : A} (f : Hom a b) (t : T b b),
    inject b t = inject b (Path.transport (D := fun x => T x x)
      (homComp (homDagger f) f) t)

/-! ## Enriched Yoneda lemma -/

/-- The enriched Yoneda map: from a natural family to an element.
    Given a family of maps Hom(a, x) → F(x) natural in x, evaluate at id_a. -/
noncomputable def yonedaMap {F : A → Type v}
    (η : (x : A) → Hom a x → F x) : F a :=
  η a (homId a)

/-- Congruence for enriched composition: if f = f' then f ∘ g = f' ∘ g.
    Multi-step using congrArg on the Path level. -/
theorem homComp_congrLeft {a b c : A} {f f' : Hom a b} (h : f = f') (g : Hom b c) :
    homComp f g = homComp f' g := by
  unfold homComp
  exact _root_.congrArg (fun t => Path.trans t g) h

/-- Congruence for enriched composition: if g = g' then f ∘ g = f ∘ g'. -/
theorem homComp_congrRight {a b c : A} (f : Hom a b) {g g' : Hom b c} (h : g = g') :
    homComp f g = homComp f g' := by
  unfold homComp
  exact _root_.congrArg (fun t => Path.trans f t) h

/-! ## Enriched functor congruence on composition chains -/

/-- Enriched functor applied to a 3-fold composition.
    Multi-step: map_comp twice then reassociate. -/
theorem enrichedFunctor_comp3 {B : Type v} (F : EnrichedFunctor A B)
    {a b c d : A} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    F.map (homComp (homComp f g) h) = homComp (homComp (F.map f) (F.map g)) (F.map h) := by
  calc F.map (homComp (homComp f g) h)
      = homComp (F.map (homComp f g)) (F.map h) := F.map_comp _ h
    _ = homComp (homComp (F.map f) (F.map g)) (F.map h) := by rw [F.map_comp f g]

/-- Enriched functor respects reassociation.
    Multi-step: map_comp on both sides then use assoc. -/
theorem enrichedFunctor_assoc_nat {B : Type v} (F : EnrichedFunctor A B)
    {a b c d : A} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    F.map (homComp f (homComp g h)) = homComp (F.map f) (homComp (F.map g) (F.map h)) := by
  calc F.map (homComp f (homComp g h))
      = homComp (F.map f) (F.map (homComp g h)) := F.map_comp f _
    _ = homComp (F.map f) (homComp (F.map g) (F.map h)) := by rw [F.map_comp g h]

/-- Enriched functor maps dagger-comp pair to dagger-comp pair.
    Multi-step chain through map_comp and map_dagger. -/
theorem enrichedFunctor_dagger_comp {B : Type v} (F : EnrichedFunctor A B)
    {a b : A} (f : Hom a b) :
    F.map (homComp f (homDagger f)) = homComp (F.map f) (homDagger (F.map f)) := by
  calc F.map (homComp f (homDagger f))
      = homComp (F.map f) (F.map (homDagger f)) := F.map_comp f (homDagger f)
    _ = homComp (F.map f) (homDagger (F.map f)) := by rw [F.map_dagger f]

/-! ## Whiskering in the enriched setting -/

/-- Left whiskering of an enriched 2-cell by a morphism.
    Given α : f = g and h, produce a path h∘f = h∘g. -/
theorem enriched_whiskerLeft {a b c : A} {f g : Hom a b} (α : f = g) (h : Hom b c) :
    homComp f h = homComp g h := by
  exact homComp_congrLeft α h

/-- Right whiskering of an enriched 2-cell.
    Given h and α : f = g, produce h∘f = h∘g. -/
theorem enriched_whiskerRight {a b c : A} (h : Hom a b) {f g : Hom b c} (α : f = g) :
    homComp h f = homComp h g := by
  exact homComp_congrRight h α

/-- Interchange law for enriched whiskering.
    Multi-step: compose left and right whiskerings. -/
theorem enriched_interchange {a b c : A}
    {f f' : Hom a b} {g g' : Hom b c}
    (α : f = f') (β : g = g') :
    homComp f g = homComp f' g' := by
  calc homComp f g
      = homComp f' g := homComp_congrLeft α g
    _ = homComp f' g' := homComp_congrRight f' β

/-! ## Composing natural transformations with functors (horizontal composition) -/

/-- Horizontal composition (whiskering a nat trans by a functor on the right). -/
noncomputable def whiskerRight_natTrans {B : Type v} {C : Type w}
    {F G : EnrichedFunctor A B} (α : EnrichedNatTrans F G)
    (H : EnrichedFunctor B C) : EnrichedNatTrans (EnrichedFunctor.comp F H) (EnrichedFunctor.comp G H) where
  component := fun a => H.map (α.component a)
  naturality := fun {a₁ a₂} f => by
    show homComp (H.map (F.map f)) (H.map (α.component a₂))
       = homComp (H.map (α.component a₁)) (H.map (G.map f))
    rw [← H.map_comp (F.map f) (α.component a₂)]
    rw [← H.map_comp (α.component a₁) (G.map f)]
    exact _root_.congrArg H.map (α.naturality f)

end EnrichedDeep

end ComputationalPaths
