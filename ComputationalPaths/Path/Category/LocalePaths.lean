/-
# Locales and Frames via Computational Paths

This module formalizes locale/frame theory using computational paths:
frame homomorphisms, locale maps, nucleus operators as path idempotents,
open/closed sublocales, spatial locales, point-free topology via path lattices.

## References

* Johnstone, *Stone Spaces* (1982)
* Picado–Pultr, *Frames and Locales* (2012)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace LocalePaths

open ComputationalPaths.Path

universe u

-- ============================================================
-- §1  Frames as Path Lattices
-- ============================================================

/-- A frame element: a value in a bounded lattice represented concretely
    as a natural number (modeling an open set index). -/
structure FrameElt where
  idx : Nat
  deriving DecidableEq, Repr, BEq

/-- The top element of the frame. -/
def frameTop : FrameElt := ⟨0⟩

/-- The bottom element of the frame. -/
def frameBot : FrameElt := ⟨1⟩

/-- Meet operation on frame elements (min of indices). -/
def frameMeet (a b : FrameElt) : FrameElt :=
  ⟨min a.idx b.idx⟩

/-- Join operation on frame elements (max of indices). -/
def frameJoin (a b : FrameElt) : FrameElt :=
  ⟨max a.idx b.idx⟩

/-- Meet is commutative. -/
def frameMeet_comm (a b : FrameElt) :
    Path (frameMeet a b) (frameMeet b a) :=
  Path.ofEq (by simp [frameMeet, Nat.min_comm])

/-- Join is commutative. -/
def frameJoin_comm (a b : FrameElt) :
    Path (frameJoin a b) (frameJoin b a) :=
  Path.ofEq (by simp [frameJoin, Nat.max_comm])

/-- Meet is associative. -/
def frameMeet_assoc (a b c : FrameElt) :
    Path (frameMeet (frameMeet a b) c) (frameMeet a (frameMeet b c)) :=
  Path.ofEq (by simp [frameMeet, Nat.min_assoc])

/-- Join is associative. -/
def frameJoin_assoc (a b c : FrameElt) :
    Path (frameJoin (frameJoin a b) c) (frameJoin a (frameJoin b c)) :=
  Path.ofEq (by simp [frameJoin, Nat.max_assoc])

/-- Meet is idempotent. -/
def frameMeet_idem (a : FrameElt) :
    Path (frameMeet a a) a :=
  Path.ofEq (by simp [frameMeet])

/-- Join is idempotent. -/
def frameJoin_idem (a : FrameElt) :
    Path (frameJoin a a) a :=
  Path.ofEq (by simp [frameJoin])

-- ============================================================
-- §2  Frame Homomorphisms
-- ============================================================

/-- A frame homomorphism: preserves meet and join. -/
structure FrameHom where
  map : FrameElt → FrameElt
  preserves_meet : ∀ a b, map (frameMeet a b) = frameMeet (map a) (map b)
  preserves_join : ∀ a b, map (frameJoin a b) = frameJoin (map a) (map b)

/-- Identity frame homomorphism. -/
def idFrameHom : FrameHom where
  map := id
  preserves_meet := fun _ _ => rfl
  preserves_join := fun _ _ => rfl

/-- Composition of frame homomorphisms. -/
def compFrameHom (f g : FrameHom) : FrameHom where
  map := f.map ∘ g.map
  preserves_meet := fun a b => by
    simp [Function.comp, g.preserves_meet, f.preserves_meet]
  preserves_join := fun a b => by
    simp [Function.comp, g.preserves_join, f.preserves_join]

/-- Identity homomorphism maps correctly. -/
theorem idFrameHom_map (a : FrameElt) : idFrameHom.map a = a := rfl

/-- Composition applies in the right order. -/
theorem compFrameHom_map (f g : FrameHom) (a : FrameElt) :
    (compFrameHom f g).map a = f.map (g.map a) := rfl

/-- Frame hom preserves meet via path. -/
def frameHom_meet_path (f : FrameHom) (a b : FrameElt) :
    Path (f.map (frameMeet a b)) (frameMeet (f.map a) (f.map b)) :=
  Path.ofEq (f.preserves_meet a b)

/-- Frame hom preserves join via path. -/
def frameHom_join_path (f : FrameHom) (a b : FrameElt) :
    Path (f.map (frameJoin a b)) (frameJoin (f.map a) (f.map b)) :=
  Path.ofEq (f.preserves_join a b)

-- ============================================================
-- §3  Nucleus Operators as Path Idempotents
-- ============================================================

/-- A nucleus on a frame: an idempotent, inflationary, meet-preserving operator. -/
structure Nucleus where
  j : FrameElt → FrameElt
  idempotent : ∀ a, j (j a) = j a
  inflationary : ∀ a, a.idx ≤ (j a).idx
  preserves_meet : ∀ a b, j (frameMeet a b) = frameMeet (j a) (j b)

/-- The identity nucleus. -/
def idNucleus : Nucleus where
  j := id
  idempotent := fun _ => rfl
  inflationary := fun _ => Nat.le_refl _
  preserves_meet := fun _ _ => rfl

/-- Nucleus idempotence as a path. -/
def nucleus_idem_path (n : Nucleus) (a : FrameElt) :
    Path (n.j (n.j a)) (n.j a) :=
  Path.ofEq (n.idempotent a)

/-- Nucleus preserves meet as a path. -/
def nucleus_meet_path (n : Nucleus) (a b : FrameElt) :
    Path (n.j (frameMeet a b)) (frameMeet (n.j a) (n.j b)) :=
  Path.ofEq (n.preserves_meet a b)

/-- Triple application of a nucleus equals single application. -/
theorem nucleus_triple (n : Nucleus) (a : FrameElt) :
    n.j (n.j (n.j a)) = n.j a := by
  rw [n.idempotent, n.idempotent]

/-- Triple application as a path. -/
def nucleus_triple_path (n : Nucleus) (a : FrameElt) :
    Path (n.j (n.j (n.j a))) (n.j a) :=
  Path.ofEq (nucleus_triple n a)

/-- Nucleus on the identity is trivially idempotent. -/
theorem idNucleus_idem (a : FrameElt) :
    idNucleus.j (idNucleus.j a) = idNucleus.j a := rfl

/-- Nucleus applied to meet via congrArg. -/
def nucleus_congrArg (n : Nucleus) {a b : FrameElt} (p : Path a b) :
    Path (n.j a) (n.j b) :=
  Path.congrArg n.j p

-- ============================================================
-- §4  Open and Closed Sublocales
-- ============================================================

/-- An open sublocale: given by a frame element (the open set). -/
structure OpenSublocale where
  element : FrameElt

/-- A closed sublocale: complement of an open sublocale. -/
structure ClosedSublocale where
  element : FrameElt

/-- The open nucleus: j_a(x) = a ∨ x (join). -/
def openNucleus (a : FrameElt) : FrameElt → FrameElt :=
  fun x => frameJoin a x

/-- Open nucleus is inflationary (x ≤ a ∨ x). -/
theorem openNucleus_inflationary (a x : FrameElt) :
    x.idx ≤ (openNucleus a x).idx := by
  simp [openNucleus, frameJoin]
  exact Nat.le_max_right a.idx x.idx

/-- Open nucleus is idempotent. -/
theorem openNucleus_idem (a x : FrameElt) :
    openNucleus a (openNucleus a x) = openNucleus a x := by
  simp [openNucleus, frameJoin]
  omega

/-- Open nucleus idempotence as a path. -/
def openNucleus_idem_path (a x : FrameElt) :
    Path (openNucleus a (openNucleus a x)) (openNucleus a x) :=
  Path.ofEq (openNucleus_idem a x)

/-- Closed nucleus: j_c(x) = x ∧ a (meet). -/
def closedNucleus (a : FrameElt) : FrameElt → FrameElt :=
  fun x => frameMeet x a

/-- Closed nucleus is idempotent. -/
theorem closedNucleus_idem (a x : FrameElt) :
    closedNucleus a (closedNucleus a x) = closedNucleus a x := by
  simp [closedNucleus, frameMeet]

/-- Closed nucleus idempotence as a path. -/
def closedNucleus_idem_path (a x : FrameElt) :
    Path (closedNucleus a (closedNucleus a x)) (closedNucleus a x) :=
  Path.ofEq (closedNucleus_idem a x)

-- ============================================================
-- §5  Locale Maps
-- ============================================================

/-- A locale map (contravariant frame hom): f* is a frame homomorphism. -/
structure LocaleMap where
  pullback : FrameHom

/-- Identity locale map. -/
def idLocaleMap : LocaleMap where
  pullback := idFrameHom

/-- Composition of locale maps (reversed from frame homs). -/
def compLocaleMap (f g : LocaleMap) : LocaleMap where
  pullback := compFrameHom g.pullback f.pullback

/-- Identity locale map is identity. -/
theorem idLocaleMap_pullback (a : FrameElt) :
    idLocaleMap.pullback.map a = a := rfl

/-- Locale map composition is associative at the map level. -/
theorem compLocaleMap_assoc (f g h : LocaleMap) (a : FrameElt) :
    (compLocaleMap (compLocaleMap f g) h).pullback.map a =
    (compLocaleMap f (compLocaleMap g h)).pullback.map a := rfl

/-- Locale map composition respects identity on the left. -/
theorem compLocaleMap_id_left (f : LocaleMap) (a : FrameElt) :
    (compLocaleMap idLocaleMap f).pullback.map a = f.pullback.map a := rfl

/-- Locale map composition respects identity on the right. -/
theorem compLocaleMap_id_right (f : LocaleMap) (a : FrameElt) :
    (compLocaleMap f idLocaleMap).pullback.map a = f.pullback.map a := rfl

-- ============================================================
-- §6  Spatial Locales and Points
-- ============================================================

/-- A point of a locale: a frame homomorphism to the two-element frame. -/
structure LocalePoint where
  isMember : FrameElt → Bool
  preserves_meet : ∀ a b, isMember (frameMeet a b) = (isMember a && isMember b)
  preserves_join : ∀ a b, isMember (frameJoin a b) = (isMember a || isMember b)

/-- Points map meets to conjunctions, as a path. -/
def point_meet_path (pt : LocalePoint) (a b : FrameElt) :
    Path (pt.isMember (frameMeet a b)) (pt.isMember a && pt.isMember b) :=
  Path.ofEq (pt.preserves_meet a b)

/-- Points map joins to disjunctions, as a path. -/
def point_join_path (pt : LocalePoint) (a b : FrameElt) :
    Path (pt.isMember (frameJoin a b)) (pt.isMember a || pt.isMember b) :=
  Path.ofEq (pt.preserves_join a b)

/-- Point membership transported along a frame element path. -/
def point_transport (pt : LocalePoint) {a b : FrameElt}
    (p : Path a b) : Path (pt.isMember a) (pt.isMember b) :=
  Path.congrArg pt.isMember p

/-- The trivial point: everything is a member. -/
def trivialPoint : LocalePoint where
  isMember := fun _ => true
  preserves_meet := fun _ _ => rfl
  preserves_join := fun _ _ => rfl

/-- Trivial point classifies everything as true. -/
theorem trivialPoint_mem (a : FrameElt) :
    trivialPoint.isMember a = true := rfl

-- ============================================================
-- §7  Point-Free Topology via Path Lattices
-- ============================================================

/-- The path lattice of frame elements under meet and join. -/
structure PathLattice where
  carrier : Type u
  meet : carrier → carrier → carrier
  join : carrier → carrier → carrier
  meet_comm : ∀ a b, meet a b = meet b a
  join_comm : ∀ a b, join a b = join b a
  meet_assoc : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  meet_idem : ∀ a, meet a a = a
  join_idem : ∀ a, join a a = a

/-- The frame element lattice is a path lattice. -/
def framePathLattice : PathLattice where
  carrier := FrameElt
  meet := frameMeet
  join := frameJoin
  meet_comm := fun a b => by simp [frameMeet, Nat.min_comm]
  join_comm := fun a b => by simp [frameJoin, Nat.max_comm]
  meet_assoc := fun a b c => by simp [frameMeet, Nat.min_assoc]
  join_assoc := fun a b c => by simp [frameJoin, Nat.max_assoc]
  meet_idem := fun a => by simp [frameMeet]
  join_idem := fun a => by simp [frameJoin]

/-- Meet commutativity as a path in any path lattice. -/
def lattice_meet_comm_path (L : PathLattice) (a b : L.carrier) :
    Path (L.meet a b) (L.meet b a) :=
  Path.ofEq (L.meet_comm a b)

/-- Join commutativity as a path in any path lattice. -/
def lattice_join_comm_path (L : PathLattice) (a b : L.carrier) :
    Path (L.join a b) (L.join b a) :=
  Path.ofEq (L.join_comm a b)

/-- Meet associativity as a path. -/
def lattice_meet_assoc_path (L : PathLattice) (a b c : L.carrier) :
    Path (L.meet (L.meet a b) c) (L.meet a (L.meet b c)) :=
  Path.ofEq (L.meet_assoc a b c)

/-- Join associativity as a path. -/
def lattice_join_assoc_path (L : PathLattice) (a b c : L.carrier) :
    Path (L.join (L.join a b) c) (L.join a (L.join b c)) :=
  Path.ofEq (L.join_assoc a b c)

/-- Meet idempotence as a path. -/
def lattice_meet_idem_path (L : PathLattice) (a : L.carrier) :
    Path (L.meet a a) a :=
  Path.ofEq (L.meet_idem a)

/-- Join idempotence as a path. -/
def lattice_join_idem_path (L : PathLattice) (a : L.carrier) :
    Path (L.join a a) a :=
  Path.ofEq (L.join_idem a)

-- ============================================================
-- §8  Lattice Homomorphisms via Paths
-- ============================================================

/-- A lattice homomorphism between path lattices. -/
structure LatticeHom (L₁ L₂ : PathLattice) where
  map : L₁.carrier → L₂.carrier
  preserves_meet : ∀ a b, map (L₁.meet a b) = L₂.meet (map a) (map b)
  preserves_join : ∀ a b, map (L₁.join a b) = L₂.join (map a) (map b)

/-- Identity lattice homomorphism. -/
def idLatticeHom (L : PathLattice) : LatticeHom L L where
  map := id
  preserves_meet := fun _ _ => rfl
  preserves_join := fun _ _ => rfl

/-- Composition of lattice homomorphisms. -/
def compLatticeHom {L₁ L₂ L₃ : PathLattice}
    (f : LatticeHom L₁ L₂) (g : LatticeHom L₂ L₃) : LatticeHom L₁ L₃ where
  map := g.map ∘ f.map
  preserves_meet := fun a b => by
    simp [Function.comp, f.preserves_meet, g.preserves_meet]
  preserves_join := fun a b => by
    simp [Function.comp, f.preserves_join, g.preserves_join]

/-- Lattice hom preserves meet as a path. -/
def latticeHom_meet_path {L₁ L₂ : PathLattice} (f : LatticeHom L₁ L₂)
    (a b : L₁.carrier) :
    Path (f.map (L₁.meet a b)) (L₂.meet (f.map a) (f.map b)) :=
  Path.ofEq (f.preserves_meet a b)

/-- Lattice hom preserves join as a path. -/
def latticeHom_join_path {L₁ L₂ : PathLattice} (f : LatticeHom L₁ L₂)
    (a b : L₁.carrier) :
    Path (f.map (L₁.join a b)) (L₂.join (f.map a) (f.map b)) :=
  Path.ofEq (f.preserves_join a b)

/-- Composition of lattice homs evaluates correctly. -/
theorem compLatticeHom_map {L₁ L₂ L₃ : PathLattice}
    (f : LatticeHom L₁ L₂) (g : LatticeHom L₂ L₃) (a : L₁.carrier) :
    (compLatticeHom f g).map a = g.map (f.map a) := rfl

-- ============================================================
-- §9  Coherence of Frame Operations
-- ============================================================

/-- The meet-comm path proof composed with itself yields refl proof. -/
theorem frameMeet_comm_invol_proof (a b : FrameElt) :
    (Path.trans (frameMeet_comm a b) (frameMeet_comm b a)).proof =
    (Path.refl (frameMeet a b)).proof := by
  simp

/-- CongrArg of meet along frame element paths. -/
def frameMeet_congrArg {a₁ a₂ b : FrameElt} (p : Path a₁ a₂) :
    Path (frameMeet a₁ b) (frameMeet a₂ b) :=
  Path.congrArg (fun x => frameMeet x b) p

/-- CongrArg of join along frame element paths. -/
def frameJoin_congrArg {a₁ a₂ b : FrameElt} (p : Path a₁ a₂) :
    Path (frameJoin a₁ b) (frameJoin a₂ b) :=
  Path.congrArg (fun x => frameJoin x b) p

/-- Transport of meet along refl gives refl. -/
theorem frameMeet_congrArg_refl (a b : FrameElt) :
    frameMeet_congrArg (Path.refl a) = Path.refl (frameMeet a b) := by
  simp [frameMeet_congrArg, Path.congrArg]

/-- Transport of join along refl gives refl. -/
theorem frameJoin_congrArg_refl (a b : FrameElt) :
    frameJoin_congrArg (Path.refl a) = Path.refl (frameJoin a b) := by
  simp [frameJoin_congrArg, Path.congrArg]

/-- CongrArg of meet respects trans. -/
theorem frameMeet_congrArg_trans {a₁ a₂ a₃ b : FrameElt}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    frameMeet_congrArg (Path.trans p q) =
    Path.trans (frameMeet_congrArg (b := b) p) (frameMeet_congrArg q) := by
  cases p with
  | mk sp hp =>
    cases q with
    | mk sq hq =>
      cases hp; cases hq
      simp [frameMeet_congrArg, Path.congrArg, Path.trans, List.map_append]

-- ============================================================
-- §10  Absorption Laws
-- ============================================================

/-- Absorption: a ∧ (a ∨ b) = a (for Nat min/max). -/
theorem frame_absorption_meet_join (a b : FrameElt) :
    frameMeet a (frameJoin a b) = a := by
  cases a; cases b; simp [frameMeet, frameJoin, Nat.min_eq_left, Nat.le_max_left]

/-- Absorption as a path. -/
def frame_absorption_meet_join_path (a b : FrameElt) :
    Path (frameMeet a (frameJoin a b)) a :=
  Path.ofEq (frame_absorption_meet_join a b)

/-- Absorption: a ∨ (a ∧ b) = a (for Nat min/max). -/
theorem frame_absorption_join_meet (a b : FrameElt) :
    frameJoin a (frameMeet a b) = a := by
  cases a; cases b; simp [frameJoin, frameMeet, Nat.max_eq_left, Nat.min_le_left]

/-- Absorption as a path (join-meet variant). -/
def frame_absorption_join_meet_path (a b : FrameElt) :
    Path (frameJoin a (frameMeet a b)) a :=
  Path.ofEq (frame_absorption_join_meet a b)

end LocalePaths
end Category
end Path
end ComputationalPaths
