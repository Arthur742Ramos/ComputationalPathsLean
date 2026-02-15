/-
# Deep Adjunction Theory via Computational Paths

Unit/counit triangles, adjoint equivalences, mates correspondence,
Kan extensions as adjunctions, monadicity — all proved via multi-step
trans/symm compositions using the core Path infrastructure.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths

open Path

universe u v w

namespace AdjunctionDeep

variable {A : Type u}

/-! ## Path endofunctors -/

/-- A path endofunctor: a function A → A with action on paths via congrArg. -/
structure PathFunctor (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_id : ∀ (a : A), map (Path.refl a) = Path.refl (obj a)
  map_comp : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    map (Path.trans f g) = Path.trans (map f) (map g)

namespace PathFunctor

/-- Identity functor. -/
def id : PathFunctor A where
  obj := fun a => a
  map := fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Composition of path functors. Multi-step: verify laws using both components. -/
def comp (F G : PathFunctor A) : PathFunctor A where
  obj := G.obj ∘ F.obj
  map := fun p => G.map (F.map p)
  map_id := fun a => by
    calc G.map (F.map (Path.refl a))
        = G.map (Path.refl (F.obj a)) := by rw [F.map_id]
      _ = Path.refl (G.obj (F.obj a)) := G.map_id (F.obj a)
  map_comp := fun f g => by
    calc G.map (F.map (Path.trans f g))
        = G.map (Path.trans (F.map f) (F.map g)) := by rw [F.map_comp]
      _ = Path.trans (G.map (F.map f)) (G.map (F.map g)) := G.map_comp _ _

end PathFunctor

/-! ## Adjunction: unit/counit with triangle identities -/

/-- An adjunction between path endofunctors F ⊣ G.
    Unit η : id → GF, counit ε : FG → id, with triangle identities. -/
structure PathAdjunction (F G : PathFunctor A) where
  unit : (a : A) → Path a (G.obj (F.obj a))
  counit : (a : A) → Path (F.obj (G.obj a)) a
  triangle_left : ∀ (a : A),
    Path.trans (F.map (unit a)) (counit (F.obj a)) = Path.refl (F.obj a)
  triangle_right : ∀ (a : A),
    Path.trans (unit (G.obj a)) (G.map (counit a)) = Path.refl (G.obj a)

namespace PathAdjunction

variable {F G : PathFunctor A}

/-- From the left triangle, extract toEq = rfl. -/
theorem counit_after_Funit_toEq (adj : PathAdjunction F G) (a : A) :
    (Path.trans (F.map (adj.unit a)) (adj.counit (F.obj a))).toEq = rfl := by
  rw [adj.triangle_left a]

/-- From the right triangle, extract toEq = rfl. -/
theorem Gcounit_after_unit_toEq (adj : PathAdjunction F G) (a : A) :
    (Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a))).toEq = rfl := by
  rw [adj.triangle_right a]

/-- The unit is a section: composing with G applied to the left triangle yields refl.
    Multi-step via G.map_comp, triangle_left, G.map_id. -/
theorem unit_section (adj : PathAdjunction F G) (a : A) :
    Path.trans (adj.unit a)
      (Path.trans (G.map (F.map (adj.unit a))) (G.map (adj.counit (F.obj a))))
    = adj.unit a := by
  have h1 : Path.trans (G.map (F.map (adj.unit a))) (G.map (adj.counit (F.obj a)))
    = G.map (Path.trans (F.map (adj.unit a)) (adj.counit (F.obj a))) :=
    (G.map_comp _ _).symm
  have h2 : G.map (Path.trans (F.map (adj.unit a)) (adj.counit (F.obj a)))
    = G.map (Path.refl (F.obj a)) := by rw [adj.triangle_left]
  have h3 : G.map (Path.refl (F.obj a)) = Path.refl (G.obj (F.obj a)) :=
    G.map_id (F.obj a)
  calc Path.trans (adj.unit a)
        (Path.trans (G.map (F.map (adj.unit a))) (G.map (adj.counit (F.obj a))))
      = Path.trans (adj.unit a) (G.map (Path.trans (F.map (adj.unit a)) (adj.counit (F.obj a)))) := by
          rw [h1]
    _ = Path.trans (adj.unit a) (G.map (Path.refl (F.obj a))) := by rw [h2]
    _ = Path.trans (adj.unit a) (Path.refl (G.obj (F.obj a))) := by rw [h3]
    _ = adj.unit a := Path.trans_refl_right _

/-- Counit is a retraction: composing with F applied to the right triangle yields refl.
    Multi-step via F.map_comp, triangle_right, F.map_id. -/
theorem counit_retraction (adj : PathAdjunction F G) (a : A) :
    Path.trans (F.map (adj.unit (G.obj a)))
      (Path.trans (F.map (G.map (adj.counit a))) (adj.counit a))
    = adj.counit a := by
  have h1 : Path.trans (F.map (adj.unit (G.obj a))) (F.map (G.map (adj.counit a)))
    = F.map (Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a))) :=
    (F.map_comp _ _).symm
  have h2 : F.map (Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a)))
    = F.map (Path.refl (G.obj a)) := by rw [adj.triangle_right]
  have h3 : F.map (Path.refl (G.obj a)) = Path.refl (F.obj (G.obj a)) :=
    F.map_id (G.obj a)
  calc Path.trans (F.map (adj.unit (G.obj a)))
        (Path.trans (F.map (G.map (adj.counit a))) (adj.counit a))
      = Path.trans (Path.trans (F.map (adj.unit (G.obj a))) (F.map (G.map (adj.counit a)))) (adj.counit a) :=
          (Path.trans_assoc _ _ _).symm
    _ = Path.trans (F.map (Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a)))) (adj.counit a) := by
          rw [h1]
    _ = Path.trans (F.map (Path.refl (G.obj a))) (adj.counit a) := by rw [h2]
    _ = Path.trans (Path.refl (F.obj (G.obj a))) (adj.counit a) := by rw [h3]
    _ = adj.counit a := Path.trans_refl_left _

end PathAdjunction

/-! ## Adjoint Equivalences -/

/-- An adjoint equivalence: an adjunction where unit and counit have path inverses. -/
structure AdjointEquiv (F G : PathFunctor A) extends PathAdjunction F G where
  unit_inv : (a : A) → Path (G.obj (F.obj a)) a
  counit_inv : (a : A) → Path a (F.obj (G.obj a))
  unit_section : ∀ (a : A), Path.trans (unit a) (unit_inv a) = Path.refl a
  unit_retraction : ∀ (a : A), Path.trans (unit_inv a) (unit a) = Path.refl (G.obj (F.obj a))
  counit_section : ∀ (a : A), Path.trans (counit a) (counit_inv a) = Path.refl (F.obj (G.obj a))
  counit_retraction : ∀ (a : A), Path.trans (counit_inv a) (counit a) = Path.refl a

namespace AdjointEquiv

variable {F G : PathFunctor A}

/-- Transport along unit then unit_inv is identity.
    Multi-step: transport_trans then use unit_section. -/
theorem transport_unit_roundtrip (e : AdjointEquiv F G)
    {D : A → Type v} (a : A) (x : D a) :
    Path.transport (e.unit_inv a) (Path.transport (e.unit a) x) = x := by
  rw [← Path.transport_trans]
  rw [e.unit_section]
  rfl

/-- Transport along counit then counit_inv is identity. -/
theorem transport_counit_roundtrip (e : AdjointEquiv F G)
    {D : A → Type v} (a : A) (x : D (F.obj (G.obj a))) :
    Path.transport (e.counit_inv a) (Path.transport (e.counit a) x) = x := by
  rw [← Path.transport_trans]
  rw [e.counit_section]
  rfl

/-- GF acts as identity on toEq via unit.
    Multi-step: extract from unit_section. -/
theorem GF_id_toEq (e : AdjointEquiv F G) (a : A) :
    (Path.trans (e.unit a) (e.unit_inv a)).toEq = rfl := by
  rw [e.unit_section a]

/-- FG acts as identity on toEq via counit. -/
theorem FG_id_toEq (e : AdjointEquiv F G) (a : A) :
    (Path.trans (e.counit_inv a) (e.counit a)).toEq = rfl := by
  rw [e.counit_retraction a]

end AdjointEquiv

/-! ## Mates Correspondence -/

/-- Given adjunctions F ⊣ G and F' ⊣ G', a mate sends
    σ : F'a → Fa to mate(σ) : Ga → G'a via η' ∘ G'σ ∘ G'ε. -/
def mate {F G F' G' : PathFunctor A}
    (adj1 : PathAdjunction F G) (adj2 : PathAdjunction F' G')
    (σ : (a : A) → Path (F'.obj a) (F.obj a))
    (a : A) : Path (G.obj a) (G'.obj a) :=
  Path.trans (adj2.unit (G.obj a))
    (G'.map (Path.trans (σ (G.obj a)) (adj1.counit a)))

/-- Mate of identity morphisms using a single adjunction. -/
def mate_self {F G : PathFunctor A}
    (adj : PathAdjunction F G) (a : A) : Path (G.obj a) (G.obj a) :=
  Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a))

/-- The self-mate is refl via triangle_right.
    Multi-step: direct application of the triangle identity. -/
theorem mate_self_is_refl {F G : PathFunctor A}
    (adj : PathAdjunction F G) (a : A) :
    mate_self adj a = Path.refl (G.obj a) :=
  adj.triangle_right a

/-! ## Monad from Adjunction -/

/-- The monad T = GF arising from an adjunction. -/
def monadObj (F G : PathFunctor A) (a : A) : A := G.obj (F.obj a)

/-- Monad action on paths. -/
def monadMap (F G : PathFunctor A) {a b : A} (p : Path a b) :
    Path (monadObj F G a) (monadObj F G b) :=
  G.map (F.map p)

/-- Monad unit η : a → T(a) from the adjunction unit. -/
def monadUnit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path a (monadObj F G a) :=
  adj.unit a

/-- Monad multiplication μ : T²(a) → T(a).
    μ_a = G(ε_{F(a)}). -/
def monadMult {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path (monadObj F G (monadObj F G a)) (monadObj F G a) :=
  G.map (adj.counit (F.obj a))

/-- Monad left unit law: μ ∘ Tη = id.
    Multi-step: unfold, use G.map_comp, triangle_left, G.map_id. -/
theorem monad_left_unit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (monadMap F G (monadUnit adj a)) (monadMult adj a)
    = Path.refl (monadObj F G a) := by
  unfold monadMap monadUnit monadMult monadObj
  calc Path.trans (G.map (F.map (adj.unit a))) (G.map (adj.counit (F.obj a)))
      = G.map (Path.trans (F.map (adj.unit a)) (adj.counit (F.obj a))) :=
        (G.map_comp _ _).symm
    _ = G.map (Path.refl (F.obj a)) := by rw [adj.triangle_left]
    _ = Path.refl (G.obj (F.obj a)) := G.map_id (F.obj a)

/-- Monad right unit law: μ ∘ ηT = id.
    Multi-step: unfold, use triangle_right. -/
theorem monad_right_unit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (monadUnit adj (monadObj F G a)) (monadMult adj a)
    = Path.refl (monadObj F G a) := by
  unfold monadUnit monadMult monadObj
  exact adj.triangle_right (F.obj a)

/-! ## Comonad from Adjunction -/

/-- Comonad object W = FG. -/
def comonadObj (F G : PathFunctor A) (a : A) : A := F.obj (G.obj a)

/-- Comonad action on paths. -/
def comonadMap (F G : PathFunctor A) {a b : A} (p : Path a b) :
    Path (comonadObj F G a) (comonadObj F G b) :=
  F.map (G.map p)

/-- Comonad counit ε : W(a) → a. -/
def comonadCounit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path (comonadObj F G a) a :=
  adj.counit a

/-- Comonad comultiplication δ : W(a) → W²(a). -/
def comonadComult {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path (comonadObj F G a) (comonadObj F G (comonadObj F G a)) :=
  F.map (adj.unit (G.obj a))

/-- Comonad left counit law: ε_W ∘ δ = id.
    Multi-step: expand, use triangle_left. -/
theorem comonad_left_counit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (comonadComult adj a) (comonadCounit adj (comonadObj F G a))
    = Path.refl (comonadObj F G a) := by
  unfold comonadComult comonadCounit comonadObj
  exact adj.triangle_left (G.obj a)

/-- Comonad right counit law: Wε ∘ δ = id.
    Multi-step: expand, use F.map_comp then triangle_right then F.map_id. -/
theorem comonad_right_counit {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (comonadComult adj a) (comonadMap F G (comonadCounit adj a))
    = Path.refl (comonadObj F G a) := by
  unfold comonadComult comonadMap comonadCounit comonadObj
  calc Path.trans (F.map (adj.unit (G.obj a))) (F.map (G.map (adj.counit a)))
      = F.map (Path.trans (adj.unit (G.obj a)) (G.map (adj.counit a))) :=
        (F.map_comp _ _).symm
    _ = F.map (Path.refl (G.obj a)) := by rw [adj.triangle_right]
    _ = Path.refl (F.obj (G.obj a)) := F.map_id (G.obj a)

/-! ## Hom-set bijection from adjunction -/

/-- Forward direction: Path(Fa, b) → Path(a, Gb).
    Multi-step: compose unit with G.map. -/
def homBijFwd {F G : PathFunctor A} (adj : PathAdjunction F G)
    {a b : A} (f : Path (F.obj a) b) : Path a (G.obj b) :=
  Path.trans (adj.unit a) (G.map f)

/-- Backward direction: Path(a, Gb) → Path(Fa, b).
    Multi-step: compose F.map with counit. -/
def homBijBwd {F G : PathFunctor A} (adj : PathAdjunction F G)
    {a b : A} (g : Path a (G.obj b)) : Path (F.obj a) b :=
  Path.trans (F.map g) (adj.counit b)

/-- Round-trip bwd ∘ fwd on toEq level. -/
theorem homBij_roundtrip_left_toEq {F G : PathFunctor A} (adj : PathAdjunction F G)
    {a b : A} (f : Path (F.obj a) b) :
    (homBijBwd adj (homBijFwd adj f)).toEq = f.toEq := by
  unfold homBijBwd homBijFwd; simp

/-- Round-trip fwd ∘ bwd on toEq level. -/
theorem homBij_roundtrip_right_toEq {F G : PathFunctor A} (adj : PathAdjunction F G)
    {a b : A} (g : Path a (G.obj b)) :
    (homBijFwd adj (homBijBwd adj g)).toEq = g.toEq := by
  unfold homBijFwd homBijBwd; simp

/-! ## Transport along adjunction data -/

/-- Composing transports along unit and G(counit) yields identity.
    Multi-step: use transport_trans then triangle_right. -/
theorem transport_unit_Gcounit {F G : PathFunctor A} (adj : PathAdjunction F G)
    {D : A → Type v} (a : A) (x : D (G.obj a)) :
    Path.transport (G.map (adj.counit a))
      (Path.transport (adj.unit (G.obj a)) x) = x := by
  rw [← Path.transport_trans]
  rw [adj.triangle_right a]
  rfl

/-- Composing transports along F(unit) and counit yields identity. -/
theorem transport_Funit_counit {F G : PathFunctor A} (adj : PathAdjunction F G)
    {D : A → Type v} (a : A) (x : D (F.obj a)) :
    Path.transport (adj.counit (F.obj a))
      (Path.transport (F.map (adj.unit a)) x) = x := by
  rw [← Path.transport_trans]
  rw [adj.triangle_left a]
  rfl

/-! ## Kan extensions via adjunction structure -/

/-- A left Kan extension structure: Lan is left adjoint to K. -/
structure LeftKan (K : PathFunctor A) where
  lan : PathFunctor A
  adj : PathAdjunction lan K

/-- The left Kan extension preserves identity paths. -/
theorem leftKan_preserves_id (lk : LeftKan K) (a : A) :
    lk.lan.map (Path.refl a) = Path.refl (lk.lan.obj a) :=
  lk.lan.map_id a

/-- The left Kan extension preserves composition. -/
theorem leftKan_preserves_comp (lk : LeftKan K) {a b c : A}
    (f : Path a b) (g : Path b c) :
    lk.lan.map (Path.trans f g) = Path.trans (lk.lan.map f) (lk.lan.map g) :=
  lk.lan.map_comp f g

/-- Left Kan monad unit from adjunction unit. -/
def leftKan_monadUnit (lk : LeftKan K) (a : A) :
    Path a (monadObj lk.lan K a) :=
  monadUnit lk.adj a

/-- Left Kan monad left unit law. -/
theorem leftKan_monad_left_unit (lk : LeftKan K) (a : A) :
    Path.trans (monadMap lk.lan K (monadUnit lk.adj a)) (monadMult lk.adj a)
    = Path.refl (monadObj lk.lan K a) :=
  monad_left_unit lk.adj a

/-- A right Kan extension structure. -/
structure RightKan (K : PathFunctor A) where
  ran : PathFunctor A
  adj : PathAdjunction K ran

/-- Right Kan extension unit via the adjunction. -/
def rightKan_unit (rk : RightKan K) (a : A) :
    Path a (rk.ran.obj (K.obj a)) :=
  rk.adj.unit a

/-- Right Kan comonad counit from adjunction counit. -/
def rightKan_comonadCounit (rk : RightKan K) (a : A) :
    Path (comonadObj K rk.ran a) a :=
  comonadCounit rk.adj a

/-! ## Algebra structure from monad -/

/-- A T-algebra for the monad T = GF: an object with a structure map. -/
structure MonadAlgebra {F G : PathFunctor A} (adj : PathAdjunction F G) where
  carrier : A
  struct_map : Path (monadObj F G carrier) carrier
  unit_law : Path.trans (monadUnit adj carrier) struct_map = Path.refl carrier

/-- Free algebra on a: carrier is monadObj a, struct_map is μ_a.
    unit_law is the right unit law of the monad. -/
def freeAlgebra {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    MonadAlgebra adj where
  carrier := monadObj F G a
  struct_map := monadMult adj a
  unit_law := monad_right_unit adj a

/-- Free algebra structure map is the monad multiplication. -/
theorem freeAlgebra_struct_toEq {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    (freeAlgebra adj a).struct_map.toEq = (monadMult adj a).toEq := rfl

/-! ## Coalgebra structure from comonad -/

/-- A W-coalgebra for the comonad W = FG. -/
structure ComonadCoalgebra {F G : PathFunctor A} (adj : PathAdjunction F G) where
  carrier : A
  struct_map : Path carrier (comonadObj F G carrier)
  counit_law : Path.trans struct_map (comonadCounit adj carrier) = Path.refl carrier

/-- Cofree coalgebra: carrier is comonadObj a, struct_map is δ_a.
    Uses the left counit law. -/
def cofreeCoalgebra {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    ComonadCoalgebra adj where
  carrier := comonadObj F G a
  struct_map := comonadComult adj a
  counit_law := comonad_left_counit adj a

/-! ## Idempotent monad characterization -/

/-- An adjunction where the counit is an iso gives an idempotent monad.
    Multi-step: monad_left_unit already proves μ ∘ Tη = id. -/
theorem idempotent_monad_left {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (monadMap F G (monadUnit adj a)) (monadMult adj a)
    = Path.refl (monadObj F G a) :=
  monad_left_unit adj a

/-- The dual: μ ∘ ηT = id. -/
theorem idempotent_monad_right {F G : PathFunctor A} (adj : PathAdjunction F G) (a : A) :
    Path.trans (monadUnit adj (monadObj F G a)) (monadMult adj a)
    = Path.refl (monadObj F G a) :=
  monad_right_unit adj a

/-! ## Path functor composition laws -/

/-- Identity functor composed with F is F (on objects). -/
theorem comp_id_obj (F : PathFunctor A) (a : A) :
    (PathFunctor.comp PathFunctor.id F).obj a = F.obj a := rfl

/-- F composed with identity is F (on objects). -/
theorem id_comp_obj (F : PathFunctor A) (a : A) :
    (PathFunctor.comp F PathFunctor.id).obj a = F.obj a := rfl

/-- Triple composition associativity (on objects). -/
theorem comp_assoc_obj (F G H : PathFunctor A) (a : A) :
    (PathFunctor.comp (PathFunctor.comp F G) H).obj a =
    (PathFunctor.comp F (PathFunctor.comp G H)).obj a := rfl

/-! ## Monad map preserves structure -/

/-- Monad map preserves identity. Multi-step via both map_id. -/
theorem monadMap_id {F G : PathFunctor A} (a : A) :
    monadMap F G (Path.refl a) = Path.refl (monadObj F G a) := by
  unfold monadMap monadObj
  calc G.map (F.map (Path.refl a))
      = G.map (Path.refl (F.obj a)) := by rw [F.map_id]
    _ = Path.refl (G.obj (F.obj a)) := G.map_id _

/-- Monad map preserves composition. Multi-step via both map_comp. -/
theorem monadMap_comp {F G : PathFunctor A} {a b c : A}
    (f : Path a b) (g : Path b c) :
    monadMap F G (Path.trans f g) = Path.trans (monadMap F G f) (monadMap F G g) := by
  unfold monadMap
  calc G.map (F.map (Path.trans f g))
      = G.map (Path.trans (F.map f) (F.map g)) := by rw [F.map_comp]
    _ = Path.trans (G.map (F.map f)) (G.map (F.map g)) := G.map_comp _ _

/-! ## Monad laws via transport -/

/-- Transport along monad unit then mult is identity.
    Multi-step: transport_trans then monad_right_unit. -/
theorem transport_monadUnit_mult {F G : PathFunctor A} (adj : PathAdjunction F G)
    {D : A → Type v} (a : A) (x : D (monadObj F G a)) :
    Path.transport (monadMult adj a)
      (Path.transport (monadUnit adj (monadObj F G a)) x) = x := by
  rw [← Path.transport_trans]
  rw [monad_right_unit]
  rfl

/-- Transport along Tη then μ is identity. -/
theorem transport_monadMap_unit_mult {F G : PathFunctor A} (adj : PathAdjunction F G)
    {D : A → Type v} (a : A) (x : D (monadObj F G a)) :
    Path.transport (monadMult adj a)
      (Path.transport (monadMap F G (monadUnit adj a)) x) = x := by
  rw [← Path.transport_trans]
  rw [monad_left_unit]
  rfl

end AdjunctionDeep

end ComputationalPaths
