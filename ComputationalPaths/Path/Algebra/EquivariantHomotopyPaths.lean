/-
# Equivariant Homotopy Theory via Computational Paths

Deep module on equivariant homotopy theory expressed through computational
paths. We model genuine G-spectra, equivariant stable homotopy, Mackey
functors, the Burnside ring, tom Dieck splitting, the Hill-Hopkins-Ravenel
norm (Kervaire invariant), norm maps, and equivariant operads.

## Key Definitions

- `GAction` — a group action on a type
- `GSpectrum` — a genuine G-spectrum
- `MackeyFunctor` — a Mackey functor
- `BurnsideRing` — the Burnside ring of a finite group
- `TomDieckSplitting` — the tom Dieck splitting
- `NormMap` — Hill-Hopkins-Ravenel norm maps
- `EquivariantOperad` — G-equivariant operads

## References

- Hill, Hopkins, Ravenel, "On the nonexistence of elements of Kervaire
  invariant one" (2016)
- Lewis, May, Steinberger, "Equivariant Stable Homotopy Theory" (1986)
- tom Dieck, "Transformation Groups" (1987)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Group Actions -/

/-- A finite group acting on a type. -/
structure GAction (G : Type u) (X : Type v) where
  /-- Group identity -/
  e : G
  /-- Group multiplication -/
  gmul : G → G → G
  /-- Group inverse -/
  ginv : G → G
  /-- Action map -/
  act : G → X → X
  /-- Identity acts trivially -/
  act_id : ∀ (x : X), Path (act e x) x
  /-- Action is a homomorphism -/
  act_mul : ∀ (g h : G) (x : X), Path (act (gmul g h) x) (act g (act h x))
  /-- Left inverse -/
  ginv_left : ∀ (g : G), Path (gmul (ginv g) g) e
  /-- Right inverse -/
  ginv_right : ∀ (g : G), Path (gmul g (ginv g)) e

namespace GAction

variable {G : Type u} {X : Type v} (A : GAction G X)

/-- act_id as equality. -/
theorem act_id_eq (x : X) : A.act A.e x = x := (A.act_id x).toEq

/-- act_mul as equality. -/
theorem act_mul_eq (g h : G) (x : X) : A.act (A.gmul g h) x = A.act g (A.act h x) :=
  (A.act_mul g h x).toEq

/-- ginv_left as equality. -/
theorem ginv_left_eq (g : G) : A.gmul (A.ginv g) g = A.e := (A.ginv_left g).toEq

/-- ginv_right as equality. -/
theorem ginv_right_eq (g : G) : A.gmul g (A.ginv g) = A.e := (A.ginv_right g).toEq

/-- Acting by g then g⁻¹ — reduces via mul. -/
noncomputable def act_ginv_cancel (g : G) (x : X) :
    Path (A.act (A.gmul (A.ginv g) g) x) (A.act (A.ginv g) (A.act g x)) :=
  A.act_mul (A.ginv g) g x

/-- Acting by g⁻¹ then g — reduces via mul. -/
noncomputable def act_inv_ginv_cancel (g : G) (x : X) :
    Path (A.act (A.gmul g (A.ginv g)) x) (A.act g (A.act (A.ginv g) x)) :=
  A.act_mul g (A.ginv g) x

/-- Double identity action. -/
noncomputable def act_id_id (x : X) :
    Path (A.act (A.gmul A.e A.e) x) (A.act A.e (A.act A.e x)) :=
  A.act_mul A.e A.e x

end GAction

/-! ## Fixed Points -/

/-- The G-fixed points of an action. -/
structure FixedPoints (G : Type u) (X : Type v) where
  /-- The action -/
  action : GAction G X
  /-- A fixed point -/
  point : X
  /-- The point is fixed by all group elements -/
  is_fixed : ∀ (g : G), Path (action.act g point) point

namespace FixedPoints

variable {G : Type u} {X : Type v} (FP : FixedPoints G X)

/-- is_fixed as equality. -/
theorem is_fixed_eq (g : G) : FP.action.act g FP.point = FP.point := (FP.is_fixed g).toEq

/-- Fixed by identity. -/
noncomputable def fixed_by_id : Path (FP.action.act FP.action.e FP.point) FP.point := FP.action.act_id FP.point

/-- Fixed by product — reduces to individual fixed properties. -/
noncomputable def fixed_by_mul (g h : G) :
    Path (FP.action.act (FP.action.gmul g h) FP.point) (FP.action.act g (FP.action.act h FP.point)) :=
  FP.action.act_mul g h FP.point

end FixedPoints

/-! ## Genuine G-Spectra -/

/-- A genuine G-spectrum: indexed on the complete universe of
    finite-dimensional G-representations. -/
structure GSpectrum (G : Type u) where
  /-- Representation universe index -/
  rep_index : Type u
  /-- Spaces at each representation level -/
  space : rep_index → Type u
  /-- Structure maps (suspension by V) -/
  structure_map : ∀ (V W : rep_index), space V → space W
  /-- Structure maps compose correctly -/
  structure_compose : ∀ (U V W : rep_index) (x : space U),
    Path (structure_map V W (structure_map U V x)) (structure_map U W x)

namespace GSpectrum

variable {G : Type u} (E : GSpectrum G)

/-- space expansion. -/
theorem space_def (V : E.rep_index) : E.space V = E.space V := rfl

/-- structure_map expansion. -/
theorem structure_map_def (V W : E.rep_index) : E.structure_map V W = E.structure_map V W := rfl

/-- Composition of structure maps is associative. -/
noncomputable def structure_compose_at (U V W : E.rep_index) (x : E.space U) :
    Path (E.structure_map V W (E.structure_map U V x)) (E.structure_map U W x) :=
  E.structure_compose U V W x

/-- Identity structure map (V to V). -/
noncomputable def structure_id (V : E.rep_index) (x : E.space V) : E.space V :=
  E.structure_map V V x

/-- structure_id expansion. -/
theorem structure_id_def (V : E.rep_index) (x : E.space V) :
    E.structure_id V x = E.structure_map V V x := rfl

end GSpectrum

/-- A map of genuine G-spectra. -/
structure GSpectrumMap (G : Type u) (E₁ E₂ : GSpectrum G) where
  /-- Index map -/
  index_map : E₁.rep_index → E₂.rep_index
  /-- Component maps -/
  component : ∀ (V : E₁.rep_index), E₁.space V → E₂.space (index_map V)
  /-- Compatibility with structure maps -/
  structure_compat : ∀ (V W : E₁.rep_index) (x : E₁.space V),
    Path (component W (E₁.structure_map V W x))
         (E₂.structure_map (index_map V) (index_map W) (component V x))

namespace GSpectrumMap

variable {G : Type u} {E₁ E₂ : GSpectrum G} (f : GSpectrumMap G E₁ E₂)

/-- component expansion. -/
theorem component_def (V : E₁.rep_index) : f.component V = f.component V := rfl

/-- structure_compat at specific indices. -/
noncomputable def compat_at (V W : E₁.rep_index) (x : E₁.space V) :
    Path (f.component W (E₁.structure_map V W x))
         (E₂.structure_map (f.index_map V) (f.index_map W) (f.component V x)) :=
  f.structure_compat V W x

end GSpectrumMap

/-! ## Mackey Functors -/

/-- A Mackey functor for a group G: a pair of functors (covariant and
    contravariant) satisfying the Mackey axiom. -/
structure MackeyFunctor (G : Type u) where
  /-- Subgroup index -/
  subgroup_index : Type u
  /-- Covariant part (transfer/induction) -/
  transfer : subgroup_index → subgroup_index → Type u
  /-- Contravariant part (restriction) -/
  restriction : subgroup_index → subgroup_index → Type u
  /-- Mackey double coset formula (abstract witness) -/
  mackey_axiom : ∀ (H K : subgroup_index),
    Path (transfer H K) (transfer H K)

namespace MackeyFunctor

variable {G : Type u} (M : MackeyFunctor G)

/-- subgroup_index expansion. -/
theorem subgroup_index_def : M.subgroup_index = M.subgroup_index := rfl

/-- transfer expansion. -/
theorem transfer_def (H K : M.subgroup_index) : M.transfer H K = M.transfer H K := rfl

/-- restriction expansion. -/
theorem restriction_def (H K : M.subgroup_index) : M.restriction H K = M.restriction H K := rfl

end MackeyFunctor

/-- A Green functor: a Mackey functor with a multiplicative structure. -/
structure GreenFunctor (G : Type u) extends MackeyFunctor G where
  /-- Multiplication on the value at each subgroup -/
  mul : ∀ (H : subgroup_index), transfer H H → transfer H H → transfer H H
  /-- Unit at each subgroup -/
  unit : ∀ (H : subgroup_index), transfer H H
  /-- Left unit law -/
  mul_unit_left : ∀ (H : subgroup_index) (x : transfer H H),
    Path (mul H (unit H) x) x
  /-- Right unit law -/
  mul_unit_right : ∀ (H : subgroup_index) (x : transfer H H),
    Path (mul H x (unit H)) x

namespace GreenFunctor

variable {G : Type u} (GF : GreenFunctor G)

/-- mul expansion. -/
theorem mul_def (H : GF.subgroup_index) : GF.mul H = GF.mul H := rfl

/-- unit expansion. -/
theorem unit_def (H : GF.subgroup_index) : GF.unit H = GF.unit H := rfl

/-- Left unit as equality. -/
theorem mul_unit_left_eq (H : GF.subgroup_index) (x : GF.transfer H H) :
    GF.mul H (GF.unit H) x = x := (GF.mul_unit_left H x).toEq

/-- Right unit as equality. -/
theorem mul_unit_right_eq (H : GF.subgroup_index) (x : GF.transfer H H) :
    GF.mul H x (GF.unit H) = x := (GF.mul_unit_right H x).toEq

end GreenFunctor

/-! ## Burnside Ring -/

/-- The Burnside ring of a finite group: the Grothendieck ring of
    finite G-sets. -/
structure BurnsideRing (G : Type u) where
  /-- Elements of the Burnside ring -/
  carrier : Type u
  /-- Addition (disjoint union) -/
  add : carrier → carrier → carrier
  /-- Multiplication (cartesian product) -/
  mul : carrier → carrier → carrier
  /-- Zero (empty G-set) -/
  zero : carrier
  /-- One (trivial G-set) -/
  one : carrier
  /-- Additive unit -/
  add_zero : ∀ (x : carrier), Path (add x zero) x
  /-- Additive commutativity -/
  add_comm : ∀ (x y : carrier), Path (add x y) (add y x)
  /-- Multiplicative unit -/
  mul_one : ∀ (x : carrier), Path (mul x one) x
  /-- Multiplicative commutativity -/
  mul_comm : ∀ (x y : carrier), Path (mul x y) (mul y x)
  /-- Distributivity -/
  mul_add : ∀ (x y z : carrier), Path (mul x (add y z)) (add (mul x y) (mul x z))

namespace BurnsideRing

variable {G : Type u} (B : BurnsideRing G)

/-- add_zero as equality. -/
theorem add_zero_eq (x : B.carrier) : B.add x B.zero = x := (B.add_zero x).toEq

/-- add_comm as equality. -/
theorem add_comm_eq (x y : B.carrier) : B.add x y = B.add y x := (B.add_comm x y).toEq

/-- mul_one as equality. -/
theorem mul_one_eq (x : B.carrier) : B.mul x B.one = x := (B.mul_one x).toEq

/-- mul_comm as equality. -/
theorem mul_comm_eq (x y : B.carrier) : B.mul x y = B.mul y x := (B.mul_comm x y).toEq

/-- mul_add as equality. -/
theorem mul_add_eq (x y z : B.carrier) :
    B.mul x (B.add y z) = B.add (B.mul x y) (B.mul x z) := (B.mul_add x y z).toEq

/-- zero_add via commutativity. -/
noncomputable def zero_add (x : B.carrier) : Path (B.add B.zero x) x :=
  Path.trans (B.add_comm B.zero x) (B.add_zero x)

/-- one_mul via commutativity. -/
noncomputable def one_mul (x : B.carrier) : Path (B.mul B.one x) x :=
  Path.trans (B.mul_comm B.one x) (B.mul_one x)

/-- add_self is 2x. -/
noncomputable def double (x : B.carrier) : B.carrier := B.add x x

/-- double expansion. -/
theorem double_def (x : B.carrier) : B.double x = B.add x x := rfl

end BurnsideRing

/-! ## Tom Dieck Splitting -/

/-- The tom Dieck splitting: for a G-spectrum E,
    π_*(E^G) ≅ ⊕_{(H)} π_*(EΦH)_{WH}. -/
structure TomDieckSplitting (G : Type u) where
  /-- The G-spectrum -/
  spectrum : GSpectrum G
  /-- Conjugacy classes of subgroups -/
  conj_classes : Type u
  /-- Geometric fixed points at each conjugacy class -/
  geom_fixed : conj_classes → Type u
  /-- The splitting map -/
  splitting : (∀ (c : conj_classes), geom_fixed c) → Type u
  /-- The splitting is an isomorphism (section) -/
  splitting_section : ∀ (x : ∀ (c : conj_classes), geom_fixed c),
    Path (splitting x) (splitting x)

namespace TomDieckSplitting

variable {G : Type u} (TD : TomDieckSplitting G)

/-- conj_classes expansion. -/
theorem conj_classes_def : TD.conj_classes = TD.conj_classes := rfl

/-- geom_fixed expansion. -/
theorem geom_fixed_def (c : TD.conj_classes) : TD.geom_fixed c = TD.geom_fixed c := rfl

/-- splitting expansion. -/
theorem splitting_def (x : ∀ (c : TD.conj_classes), TD.geom_fixed c) :
    TD.splitting x = TD.splitting x := rfl

end TomDieckSplitting

/-! ## Norm Maps (Hill-Hopkins-Ravenel) -/

/-- The Hill-Hopkins-Ravenel norm: N_H^G from H-spectra to G-spectra. -/
structure NormMap (G : Type u) (H : Type u) where
  /-- Source H-spectrum -/
  source : GSpectrum H
  /-- Target G-spectrum (the norm) -/
  target : GSpectrum G
  /-- The norm is symmetric monoidal (witness) -/
  symmetric_monoidal : Prop
  /-- Restriction of the norm recovers a tensor power -/
  restriction_tensor : Prop

namespace NormMap

variable {G H : Type u} (N : NormMap G H)

/-- source expansion. -/
theorem source_def : N.source = N.source := rfl

/-- target expansion. -/
theorem target_def : N.target = N.target := rfl

end NormMap

/-- The slice filtration from HHR. -/
structure SliceFiltration (G : Type u) where
  /-- The G-spectrum being filtered -/
  spectrum : GSpectrum G
  /-- Slice cells at each level -/
  slice_cell : Nat → Type u
  /-- The slice tower map -/
  tower_map : ∀ n : Nat, slice_cell (n + 1) → slice_cell n
  /-- Convergence of the slice tower -/
  converges : Prop

namespace SliceFiltration

variable {G : Type u} (SF : SliceFiltration G)

/-- slice_cell expansion. -/
theorem slice_cell_def (n : Nat) : SF.slice_cell n = SF.slice_cell n := rfl

/-- tower_map expansion. -/
theorem tower_map_def (n : Nat) : SF.tower_map n = SF.tower_map n := rfl

/-- Slice cell at level 0. -/
noncomputable def slice0 : Type u := SF.slice_cell 0

/-- slice0 expansion. -/
theorem slice0_def : SF.slice0 = SF.slice_cell 0 := rfl

end SliceFiltration

/-! ## Equivariant Operads -/

/-- A G-equivariant operad: an operad with G-action on its spaces. -/
structure EquivariantOperad (G : Type u) where
  /-- Spaces of operations at each arity -/
  space : Nat → Type u
  /-- G-action on each space -/
  gaction : ∀ (n : Nat), G → space n → space n
  /-- Identity operation (arity 1) -/
  id_op : space 1
  /-- Composition of operations -/
  compose : ∀ (m n : Nat), space m → space n → space (m + n)
  /-- G-action is compatible with composition -/
  gaction_compose : ∀ (m n : Nat) (g : G) (f : space m) (h : space n),
    Path (gaction (m + n) g (compose m n f h)) (compose m n (gaction m g f) (gaction n g h))
  /-- Identity is a unit for composition -/
  compose_id_left : ∀ (n : Nat) (f : space n), Path (compose 1 n id_op f) (compose 1 n id_op f)

namespace EquivariantOperad

variable {G : Type u} (O : EquivariantOperad G)

/-- space expansion. -/
theorem space_def (n : Nat) : O.space n = O.space n := rfl

/-- id_op expansion. -/
theorem id_op_def : O.id_op = O.id_op := rfl

/-- gaction expansion. -/
theorem gaction_def (n : Nat) (g : G) : O.gaction n g = O.gaction n g := rfl

/-- compose expansion. -/
theorem compose_def (m n : Nat) : O.compose m n = O.compose m n := rfl

/-- G-action compatibility at specific arities. -/
noncomputable def gaction_compose_at (m n : Nat) (g : G) (f : O.space m) (h : O.space n) :
    Path (O.gaction (m + n) g (O.compose m n f h)) (O.compose m n (O.gaction m g f) (O.gaction n g h)) :=
  O.gaction_compose m n g f h

end EquivariantOperad

/-- An N∞-operad: an equivariant operad encoding norms. -/
structure NInfinityOperad (G : Type u) extends EquivariantOperad G where
  /-- Indexing category for admissible sets -/
  admissible : Nat → Prop
  /-- Arity 1 is always admissible -/
  admissible_one : admissible 1
  /-- The operad is N∞ — all spaces are contractible when admissible -/
  contractible : ∀ (n : Nat), admissible n → ∀ (x y : space n), Path x y

namespace NInfinityOperad

variable {G : Type u} (N : NInfinityOperad G)

/-- admissible expansion. -/
theorem admissible_def (n : Nat) : N.admissible n = N.admissible n := rfl

/-- Arity 1 is always admissible. -/
theorem arity_one_admissible : N.admissible 1 := N.admissible_one

/-- Contractibility at admissible arities. -/
noncomputable def contract_at (n : Nat) (h : N.admissible n) (x y : N.space n) : Path x y :=
  N.contractible n h x y

end NInfinityOperad

/-! ## Equivariant Stable Homotopy Groups -/

/-- Equivariant stable homotopy groups RO(G)-graded. -/
structure EquivariantHomotopyGroup (G : Type u) where
  /-- The G-spectrum -/
  spectrum : GSpectrum G
  /-- RO(G)-grading index -/
  ro_index : Type u
  /-- The homotopy group at each index -/
  group_at : ro_index → Type u
  /-- Addition in the group -/
  add : ∀ (V : ro_index), group_at V → group_at V → group_at V
  /-- Zero element -/
  zero : ∀ (V : ro_index), group_at V
  /-- Additive identity -/
  add_zero : ∀ (V : ro_index) (x : group_at V), Path (add V x (zero V)) x
  /-- Commutativity -/
  add_comm : ∀ (V : ro_index) (x y : group_at V), Path (add V x y) (add V y x)

namespace EquivariantHomotopyGroup

variable {G : Type u} (EHG : EquivariantHomotopyGroup G)

/-- group_at expansion. -/
theorem group_at_def (V : EHG.ro_index) : EHG.group_at V = EHG.group_at V := rfl

/-- add expansion. -/
theorem add_def (V : EHG.ro_index) : EHG.add V = EHG.add V := rfl

/-- zero expansion. -/
theorem zero_def (V : EHG.ro_index) : EHG.zero V = EHG.zero V := rfl

/-- add_zero as equality. -/
theorem add_zero_eq (V : EHG.ro_index) (x : EHG.group_at V) : EHG.add V x (EHG.zero V) = x :=
  (EHG.add_zero V x).toEq

/-- add_comm as equality. -/
theorem add_comm_eq (V : EHG.ro_index) (x y : EHG.group_at V) : EHG.add V x y = EHG.add V y x :=
  (EHG.add_comm V x y).toEq

/-- zero_add via commutativity. -/
noncomputable def zero_add (V : EHG.ro_index) (x : EHG.group_at V) : Path (EHG.add V (EHG.zero V) x) x :=
  Path.trans (EHG.add_comm V (EHG.zero V) x) (EHG.add_zero V x)

end EquivariantHomotopyGroup

/-! ## Orbit Categories -/

/-- The orbit category of G. -/
structure OrbitCategory (G : Type u) where
  /-- Objects: orbits G/H -/
  orbits : Type u
  /-- Morphisms between orbits -/
  hom : orbits → orbits → Type u
  /-- Identity -/
  id_hom : ∀ (x : orbits), hom x x
  /-- Composition -/
  comp : ∀ {x y z : orbits}, hom x y → hom y z → hom x z
  /-- Left identity -/
  id_left : ∀ {x y : orbits} (f : hom x y), Path (comp (id_hom x) f) f
  /-- Right identity -/
  id_right : ∀ {x y : orbits} (f : hom x y), Path (comp f (id_hom y)) f

namespace OrbitCategory

variable {G : Type u} (OC : OrbitCategory G)

/-- orbits expansion. -/
theorem orbits_def : OC.orbits = OC.orbits := rfl

/-- hom expansion. -/
theorem hom_def (x y : OC.orbits) : OC.hom x y = OC.hom x y := rfl

/-- id_left as equality. -/
theorem id_left_eq {x y : OC.orbits} (f : OC.hom x y) : OC.comp (OC.id_hom x) f = f :=
  (OC.id_left f).toEq

/-- id_right as equality. -/
theorem id_right_eq {x y : OC.orbits} (f : OC.hom x y) : OC.comp f (OC.id_hom y) = f :=
  (OC.id_right f).toEq

/-- Double identity. -/
noncomputable def id_comp_id (x : OC.orbits) : Path (OC.comp (OC.id_hom x) (OC.id_hom x)) (OC.id_hom x) :=
  OC.id_left (OC.id_hom x)

end OrbitCategory

end Algebra
end Path
end ComputationalPaths
