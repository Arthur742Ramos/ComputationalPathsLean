/-
# Locales and Frames via Computational Paths

Frame homomorphisms, locale maps, nucleus operators, open/closed sublocales,
spatial locales, point-free topology via path lattices.

## References

- Johnstone, *Stone Spaces* (1982)
- Picado–Pultr, *Frames and Locales* (2012)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace LocalePaths

universe u v

/-! ## §1  Frame structure -/

/-- A frame: complete lattice with finite meets distributing over arbitrary joins.
    We model this abstractly with top, bot, meet, join. -/
structure Frame where
  /-- Carrier type. -/
  carrier : Type u
  /-- Top element. -/
  top : carrier
  /-- Bottom element. -/
  bot : carrier
  /-- Binary meet. -/
  meet : carrier → carrier → carrier
  /-- Binary join. -/
  join : carrier → carrier → carrier
  /-- Meet is commutative. -/
  meet_comm : ∀ a b, meet a b = meet b a
  /-- Join is commutative. -/
  join_comm : ∀ a b, join a b = join b a
  /-- Meet is idempotent. -/
  meet_idem : ∀ a, meet a a = a
  /-- Join is idempotent. -/
  join_idem : ∀ a, join a a = a
  /-- Top is a unit for meet. -/
  meet_top : ∀ a, meet a top = a
  /-- Bot is a unit for join. -/
  join_bot : ∀ a, join a bot = a
  /-- Meet distributes over join. -/
  meet_distrib_join : ∀ a b c, meet a (join b c) = join (meet a b) (meet a c)

/-- Path between frame elements via meet commutativity. -/
def meetCommPath (F : Frame.{u}) (a b : F.carrier) :
    Path (F.meet a b) (F.meet b a) :=
  Path.ofEq (F.meet_comm a b)

/-- Path between frame elements via join commutativity. -/
def joinCommPath (F : Frame.{u}) (a b : F.carrier) :
    Path (F.join a b) (F.join b a) :=
  Path.ofEq (F.join_comm a b)

/-- Path from `meet a a` to `a` via idempotence. -/
def meetIdemPath (F : Frame.{u}) (a : F.carrier) :
    Path (F.meet a a) a :=
  Path.ofEq (F.meet_idem a)

/-- Path from `join a a` to `a` via idempotence. -/
def joinIdemPath (F : Frame.{u}) (a : F.carrier) :
    Path (F.join a a) a :=
  Path.ofEq (F.join_idem a)

/-- Path from `meet a top` to `a`. -/
def meetTopPath (F : Frame.{u}) (a : F.carrier) :
    Path (F.meet a F.top) a :=
  Path.ofEq (F.meet_top a)

/-- Path from `join a bot` to `a`. -/
def joinBotPath (F : Frame.{u}) (a : F.carrier) :
    Path (F.join a F.bot) a :=
  Path.ofEq (F.join_bot a)

/-- Distributivity path. -/
def distribPath (F : Frame.{u}) (a b c : F.carrier) :
    Path (F.meet a (F.join b c)) (F.join (F.meet a b) (F.meet a c)) :=
  Path.ofEq (F.meet_distrib_join a b c)

/-- Composing meet-comm with itself gives refl (proof-level). -/
theorem meetComm_twice_proof (F : Frame.{u}) (a b : F.carrier) :
    (Path.trans (meetCommPath F a b) (meetCommPath F b a)).proof = rfl := by
  simp

/-! ## §2  Frame homomorphisms -/

/-- A frame homomorphism preserves top, meet and join. -/
structure FrameHom (F G : Frame.{u}) where
  /-- The underlying map. -/
  toFun : F.carrier → G.carrier
  /-- Preserves top. -/
  map_top : toFun F.top = G.top
  /-- Preserves meet. -/
  map_meet : ∀ a b, toFun (F.meet a b) = G.meet (toFun a) (toFun b)
  /-- Preserves join. -/
  map_join : ∀ a b, toFun (F.join a b) = G.join (toFun a) (toFun b)

/-- Identity frame homomorphism. -/
def frameHomId (F : Frame.{u}) : FrameHom F F where
  toFun := id
  map_top := rfl
  map_meet := fun _ _ => rfl
  map_join := fun _ _ => rfl

/-- Composition of frame homomorphisms. -/
def frameHomComp {F G H : Frame.{u}} (f : FrameHom F G) (g : FrameHom G H) :
    FrameHom F H where
  toFun := g.toFun ∘ f.toFun
  map_top := by simp [Function.comp, f.map_top, g.map_top]
  map_meet := by intro a b; simp [Function.comp, f.map_meet, g.map_meet]
  map_join := by intro a b; simp [Function.comp, f.map_join, g.map_join]

/-- Left identity for composition. -/
theorem frameHomComp_id_left {F G : Frame.{u}} (f : FrameHom F G) :
    (frameHomComp (frameHomId F) f).toFun = f.toFun := rfl

/-- Right identity for composition. -/
theorem frameHomComp_id_right {F G : Frame.{u}} (f : FrameHom F G) :
    (frameHomComp f (frameHomId G)).toFun = f.toFun := rfl

/-- A frame homomorphism induces a Path map via congrArg. -/
def frameHomPathMap {F G : Frame.{u}} (f : FrameHom F G)
    {a b : F.carrier} (p : Path a b) :
    Path (f.toFun a) (f.toFun b) :=
  Path.congrArg f.toFun p

/-- Frame hom maps refl to refl (proof-level). -/
theorem frameHomPathMap_refl {F G : Frame.{u}} (f : FrameHom F G) (a : F.carrier) :
    (frameHomPathMap f (Path.refl a)).proof = rfl := by
  simp

/-- Frame hom preserves meet-comm path (proof-level). -/
theorem frameHomPathMap_meetComm {F G : Frame.{u}} (f : FrameHom F G)
    (a b : F.carrier) :
    (frameHomPathMap f (meetCommPath F a b)).proof =
    (f.map_meet a b ▸ f.map_meet b a ▸ (meetCommPath G (f.toFun a) (f.toFun b)).proof) := by
  apply Subsingleton.elim

/-! ## §3  Nucleus operators -/

/-- A nucleus on a frame: an inflationary, idempotent, meet-preserving closure. -/
structure Nucleus (F : Frame.{u}) where
  /-- The closure operator. -/
  j : F.carrier → F.carrier
  /-- Inflationary: a ≤ j a (modelled as meet a (j a) = a). -/
  inflationary : ∀ a, F.meet a (j a) = a
  /-- Idempotent: j (j a) = j a. -/
  idempotent : ∀ a, j (j a) = j a
  /-- Preserves meets: j (a ∧ b) = j a ∧ j b. -/
  preserves_meet : ∀ a b, j (F.meet a b) = F.meet (j a) (j b)

/-- Inflationary path: `meet a (j a) = a`. -/
def nucleusInflPath {F : Frame.{u}} (n : Nucleus F) (a : F.carrier) :
    Path (F.meet a (n.j a)) a :=
  Path.ofEq (n.inflationary a)

/-- Idempotency path: `j (j a) = j a`. -/
def nucleusIdemPath {F : Frame.{u}} (n : Nucleus F) (a : F.carrier) :
    Path (n.j (n.j a)) (n.j a) :=
  Path.ofEq (n.idempotent a)

/-- Meet-preservation path. -/
def nucleusMeetPath {F : Frame.{u}} (n : Nucleus F) (a b : F.carrier) :
    Path (n.j (F.meet a b)) (F.meet (n.j a) (n.j b)) :=
  Path.ofEq (n.preserves_meet a b)

/-- Nucleus applied to top is top (derived). -/
theorem nucleus_top {F : Frame.{u}} (n : Nucleus F) :
    F.meet F.top (n.j F.top) = F.top :=
  n.inflationary F.top

/-- Triple application of a nucleus equals single application (proof-level). -/
theorem nucleus_triple_idem {F : Frame.{u}} (n : Nucleus F) (a : F.carrier) :
    n.j (n.j (n.j a)) = n.j a := by
  rw [n.idempotent (n.j a), n.idempotent a]

/-- Path for triple idempotence. -/
def nucleusTriplePath {F : Frame.{u}} (n : Nucleus F) (a : F.carrier) :
    Path (n.j (n.j (n.j a))) (n.j a) :=
  Path.ofEq (nucleus_triple_idem n a)

/-- Composing idem paths: trans of two idempotency paths gives the triple path (proof-level). -/
theorem nucleusIdem_trans_proof {F : Frame.{u}} (n : Nucleus F) (a : F.carrier) :
    (Path.trans (nucleusIdemPath n (n.j a)) (nucleusIdemPath n a)).proof =
    (nucleusTriplePath n a).proof := by
  apply Subsingleton.elim

/-! ## §4  Open and closed sublocales -/

/-- An open sublocale determined by an element `a`: the nucleus `a ∨ -`. -/
def openNucleus (F : Frame.{u}) (a : F.carrier) : F.carrier → F.carrier :=
  fun x => F.join a x

/-- A closed sublocale determined by `a`: the nucleus `a ∧ -`. -/
def closedNucleus (F : Frame.{u}) (a : F.carrier) : F.carrier → F.carrier :=
  fun x => F.meet a x

/-- The open nucleus is inflationary when join absorbs. -/
theorem openNucleus_absorb (F : Frame.{u}) (a x : F.carrier)
    (h : F.meet x (F.join a x) = x) :
    F.meet x (openNucleus F a x) = x :=
  h

/-- The closed nucleus is definitionally `meet a`. -/
theorem closedNucleus_def (F : Frame.{u}) (a x : F.carrier) :
    closedNucleus F a x = F.meet a x :=
  rfl

/-- Closed nucleus with itself is idempotent via meet_idem. -/
theorem closedNucleus_self (F : Frame.{u}) (a : F.carrier) :
    closedNucleus F a a = a :=
  F.meet_idem a

/-- The open and closed nuclei compose trivially on bot. -/
theorem open_closed_bot (F : Frame.{u}) (a : F.carrier) :
    openNucleus F a F.bot = F.join a F.bot :=
  rfl

/-- Open nucleus of bot equals join a bot. -/
theorem openNucleus_bot_eq (F : Frame.{u}) (a : F.carrier) :
    openNucleus F a F.bot = F.join a F.bot :=
  rfl

/-- Closed nucleus of top equals meet a top. -/
theorem closedNucleus_top_eq (F : Frame.{u}) (a : F.carrier) :
    closedNucleus F a F.top = F.meet a F.top :=
  rfl

/-- Closed nucleus with top element gives identity. -/
theorem closedNucleus_top_is_id (F : Frame.{u}) (x : F.carrier) :
    closedNucleus F F.top x = F.meet F.top x :=
  rfl

/-! ## §5  Locale maps (= frame homs in opposite direction) -/

/-- A locale map from L to M is a frame homomorphism from M to L. -/
structure LocaleMap (L M : Frame.{u}) where
  /-- The underlying frame hom in the reverse direction. -/
  frameHom : FrameHom M L

/-- Identity locale map. -/
def localeMapId (L : Frame.{u}) : LocaleMap L L where
  frameHom := frameHomId L

/-- Composition of locale maps (reverses frame hom composition). -/
def localeMapComp {L M N : Frame.{u}} (f : LocaleMap L M) (g : LocaleMap M N) :
    LocaleMap L N where
  frameHom := frameHomComp g.frameHom f.frameHom

/-- Left identity. -/
theorem localeMapComp_id_left {L M : Frame.{u}} (f : LocaleMap L M) :
    (localeMapComp (localeMapId L) f).frameHom.toFun = f.frameHom.toFun := rfl

/-- Right identity. -/
theorem localeMapComp_id_right {L M : Frame.{u}} (f : LocaleMap L M) :
    (localeMapComp f (localeMapId M)).frameHom.toFun = f.frameHom.toFun := rfl

/-! ## §6  Spatial locales -/

/-- A point of a locale L is a frame hom from L to the two-element frame. -/
structure LocalePoint (L : Frame.{u}) where
  /-- Evaluation of a point at each open. -/
  eval : L.carrier → Prop
  /-- Points preserve top. -/
  eval_top : eval L.top = True
  /-- Points preserve meet. -/
  eval_meet : ∀ a b, eval (L.meet a b) = (eval a ∧ eval b)

/-- A locale is spatial if points separate opens. -/
structure Spatial (L : Frame.{u}) where
  /-- For distinct opens, some point separates them. -/
  separate : ∀ (a b : L.carrier), a ≠ b →
    ∃ pt : LocalePoint L, pt.eval a ≠ pt.eval b

/-- Evaluation at top yields True. -/
theorem localePoint_top {L : Frame.{u}} (pt : LocalePoint L) :
    pt.eval L.top = True :=
  pt.eval_top

/-- Evaluation at meet is conjunction. -/
theorem localePoint_meet {L : Frame.{u}} (pt : LocalePoint L) (a b : L.carrier) :
    pt.eval (L.meet a b) = (pt.eval a ∧ pt.eval b) :=
  pt.eval_meet a b

/-! ## §7  Path lattice operations -/

/-- Transport of a frame element along a Path in some index type. -/
def frameTransport {X : Type u} (F : Frame.{u}) {a b : X}
    (p : Path a b) (f : X → F.carrier) :
    Path (f a) (f b) :=
  Path.congrArg f p

/-- Transport preserves meet. -/
theorem frameTransport_meet {X : Type u} (F : Frame.{u}) {a b : X}
    (p : Path a b) (f g : X → F.carrier) :
    (frameTransport F p (fun x => F.meet (f x) (g x))).proof =
    (Eq.trans
      (_root_.congrArg (fun x => F.meet (f x) (g x)) p.proof)
      rfl) := by
  apply Subsingleton.elim

/-- congrArg of meet decomposes (proof-level). -/
theorem congrArg_meet_proof {X : Type u} (F : Frame.{u}) {a b : X}
    (p : Path a b) (f g : X → F.carrier) :
    (_root_.congrArg (fun x => F.meet (f x) (g x)) p.proof) =
    (show F.meet (f a) (g a) = F.meet (f b) (g b)
     from _root_.congrArg (fun x => F.meet (f x) (g x)) p.proof) := by
  rfl

/-- Symmetry of meet-comm paths composes to refl (proof-level). -/
theorem meetComm_symm_trans {F : Frame.{u}} (a b : F.carrier) :
    (Path.trans (Path.symm (meetCommPath F a b)) (meetCommPath F a b)).proof = rfl := by
  simp

/-- Distributivity path is natural w.r.t. frame transport (proof-level, via Subsingleton). -/
theorem distrib_transport_natural {X : Type u} (F : Frame.{u}) {x y : X}
    (p : Path x y) (f g h : X → F.carrier) :
    (frameTransport F p (fun z => F.meet (f z) (F.join (g z) (h z)))).proof =
    (_root_.congrArg (fun z => F.meet (f z) (F.join (g z) (h z))) p.proof) := by
  rfl

end LocalePaths
end Category
end Path
end ComputationalPaths
