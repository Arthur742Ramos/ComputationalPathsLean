/-
  Locale Theory and Pointless Topology via Computational Paths
  =============================================================
  Frames, nuclei, sublocales, spatial locales, Stone duality structure,
  localic groups — all laws witnessed by Path.trans / Path.symm / Path.congrArg.

  Author: armada-391 (LocaleTheoryDeep)
-/
import ComputationalPaths.Path.Basic

namespace LocaleTheoryDeep

universe u v w

open ComputationalPaths
open ComputationalPaths.Path

-- ============================================================
-- §1  FRAME STRUCTURE
-- ============================================================

/-- A Frame: complete lattice with infinite distributivity.
    All laws are witnessed by computational Paths. -/
structure Frame (F : Type u) where
  top   : F
  bot   : F
  meet  : F → F → F
  join  : F → F → F
  sup   : {I : Type u} → (I → F) → F
  -- Lattice laws
  meet_comm    : (a b : F) → Path (meet a b) (meet b a)
  meet_assoc   : (a b c : F) → Path (meet (meet a b) c) (meet a (meet b c))
  meet_idem    : (a : F) → Path (meet a a) a
  join_comm    : (a b : F) → Path (join a b) (join b a)
  join_assoc   : (a b c : F) → Path (join (join a b) c) (join a (join b c))
  join_idem    : (a : F) → Path (join a a) a
  absorb_mj    : (a b : F) → Path (meet a (join a b)) a
  absorb_jm    : (a b : F) → Path (join a (meet a b)) a
  meet_top     : (a : F) → Path (meet a top) a
  join_bot     : (a : F) → Path (join a bot) a
  meet_bot     : (a : F) → Path (meet a bot) bot
  join_top     : (a : F) → Path (join a top) top
  -- Infinite distributivity: a ∧ (⋁ᵢ bᵢ) = ⋁ᵢ (a ∧ bᵢ)
  inf_dist     : (a : F) → {I : Type u} → (b : I → F) →
                   Path (meet a (sup b)) (sup (fun i => meet a (b i)))

variable {F : Type u} (fr : Frame F)

-- ============================================================
-- §1a  Derived Frame Paths (Theorems 1–14)
-- ============================================================

/-- Theorem 1: meet is commutative (symmetric witness) -/
noncomputable def frame_meet_comm_symm (a b : F) : Path (fr.meet b a) (fr.meet a b) :=
  Path.symm (fr.meet_comm a b)

/-- Theorem 2: join is commutative (symmetric witness) -/
noncomputable def frame_join_comm_symm (a b : F) : Path (fr.join b a) (fr.join a b) :=
  Path.symm (fr.join_comm a b)

/-- Theorem 3: top is left identity for meet -/
noncomputable def frame_top_meet_left (a : F) : Path (fr.meet fr.top a) a :=
  Path.trans (fr.meet_comm fr.top a) (fr.meet_top a)

/-- Theorem 4: bot is left identity for join -/
noncomputable def frame_bot_join_left (a : F) : Path (fr.join fr.bot a) a :=
  Path.trans (fr.join_comm fr.bot a) (fr.join_bot a)

/-- Theorem 5: meet_assoc reversed -/
noncomputable def frame_meet_assoc_rev (a b c : F) :
    Path (fr.meet a (fr.meet b c)) (fr.meet (fr.meet a b) c) :=
  Path.symm (fr.meet_assoc a b c)

/-- Theorem 6: join_assoc reversed -/
noncomputable def frame_join_assoc_rev (a b c : F) :
    Path (fr.join a (fr.join b c)) (fr.join (fr.join a b) c) :=
  Path.symm (fr.join_assoc a b c)

/-- Theorem 7: bot is left annihilator for meet -/
noncomputable def frame_bot_meet_left (a : F) : Path (fr.meet fr.bot a) fr.bot :=
  Path.trans (fr.meet_comm fr.bot a) (fr.meet_bot a)

/-- Theorem 8: top is left annihilator for join -/
noncomputable def frame_top_join_left (a : F) : Path (fr.join fr.top a) fr.top :=
  Path.trans (fr.join_comm fr.top a) (fr.join_top a)

/-- Theorem 9: Double meet idempotence -/
noncomputable def frame_meet_idem_double (a : F) :
    Path (fr.meet (fr.meet a a) (fr.meet a a)) (fr.meet a a) :=
  fr.meet_idem (fr.meet a a)

/-- Theorem 10: Congruence of meet in left argument -/
noncomputable def frame_meet_congrL (a b c : F) (p : Path a b) :
    Path (fr.meet a c) (fr.meet b c) :=
  Path.congrArg (fun x => fr.meet x c) p

/-- Theorem 11: Congruence of meet in right argument -/
noncomputable def frame_meet_congrR (a b c : F) (p : Path b c) :
    Path (fr.meet a b) (fr.meet a c) :=
  Path.congrArg (fun x => fr.meet a x) p

/-- Theorem 12: Congruence of join in left argument -/
noncomputable def frame_join_congrL (a b c : F) (p : Path a b) :
    Path (fr.join a c) (fr.join b c) :=
  Path.congrArg (fun x => fr.join x c) p

/-- Theorem 13: Congruence of join in right argument -/
noncomputable def frame_join_congrR (a b c : F) (p : Path b c) :
    Path (fr.join a b) (fr.join a c) :=
  Path.congrArg (fun x => fr.join a x) p

/-- Theorem 14: Congruence of sup through a function path -/
noncomputable def frame_sup_congr {I : Type u} (s t : I → F)
    (p : Path s t) :
    Path (fr.sup s) (fr.sup t) :=
  Path.congrArg fr.sup p

-- ============================================================
-- §2  FRAME HOMOMORPHISMS (Theorems 15–18)
-- ============================================================

/-- A frame homomorphism preserves finite meets and arbitrary joins -/
structure FrameHom (F G : Type u) (frF : Frame F) (frG : Frame G) where
  fn           : F → G
  pres_top     : Path (fn frF.top) frG.top
  pres_meet    : (a b : F) → Path (fn (frF.meet a b)) (frG.meet (fn a) (fn b))
  pres_sup     : {I : Type u} → (s : I → F) →
                   Path (fn (frF.sup s)) (frG.sup (fun i => fn (s i)))

variable {G : Type u} {frG : Frame G}

/-- Theorem 15: Frame hom applied to meet_top -/
noncomputable def frameHom_meet_top (h : FrameHom F G fr frG) (a : F) :
    Path (h.fn (fr.meet a fr.top)) (h.fn a) :=
  Path.congrArg h.fn (fr.meet_top a)

/-- Theorem 16: Composition of frame homs -/
noncomputable def frameHom_comp {H : Type u} {frH : Frame H}
    (g : FrameHom G H frG frH) (f : FrameHom F G fr frG) :
    FrameHom F H fr frH where
  fn := fun x => g.fn (f.fn x)
  pres_top :=
    Path.trans (Path.congrArg g.fn f.pres_top) g.pres_top
  pres_meet := fun a b =>
    Path.trans (Path.congrArg g.fn (f.pres_meet a b)) (g.pres_meet (f.fn a) (f.fn b))
  pres_sup := fun s =>
    Path.trans (Path.congrArg g.fn (f.pres_sup s)) (g.pres_sup (fun i => f.fn (s i)))

/-- Theorem 17: Identity frame homomorphism -/
noncomputable def frameHom_id : FrameHom F F fr fr where
  fn := id
  pres_top := Path.refl _
  pres_meet := fun _ _ => Path.refl _
  pres_sup := fun _ => Path.refl _

/-- Theorem 18: Frame hom composition is associative pointwise -/
noncomputable def frameHom_comp_assoc {H K : Type u} {frH : Frame H} {frK : Frame K}
    (h : FrameHom H K frH frK) (g : FrameHom G H frG frH) (f : FrameHom F G fr frG) :
    (a : F) → Path ((frameHom_comp fr (frameHom_comp frG h g) f).fn a)
                    ((frameHom_comp fr h (frameHom_comp fr g f)).fn a) :=
  fun _ => Path.refl _

-- ============================================================
-- §3  NUCLEI (Closure Operators on Frames) (Theorems 19–25)
-- ============================================================

/-- A nucleus on a frame: an inflationary, idempotent, meet-preserving map -/
structure Nucleus (F : Type u) (fr : Frame F) where
  j          : F → F
  inflate    : (a : F) → Path (fr.meet a (j a)) a
  idempotent : (a : F) → Path (j (j a)) (j a)
  pres_meet  : (a b : F) → Path (j (fr.meet a b)) (fr.meet (j a) (j b))

variable {fr}
variable (nu : Nucleus F fr)

/-- Theorem 19: Nucleus preserves top via inflate + meet_top -/
noncomputable def nucleus_pres_top : Path (nu.j fr.top) fr.top :=
  -- inflate: meet(top, j(top)) = top
  -- meet_idem(j(top)): meet(j(top), j(top)) = j(top)  [symm]
  -- pres_meet(top,top): j(meet(top,top)) = meet(j(top),j(top))
  -- congrArg j (meet_idem top): j(meet(top,top)) = j(top)
  -- So j(top) = meet(j(top),j(top)) = j(meet(top,top)) [by symm pres_meet] = j(top)
  -- We need to use idempotent + inflate
  -- idempotent(top): j(j(top)) = j(top)
  -- inflate(top): meet(top, j(top)) = top
  -- We know: meet(top, j(top)) = top [inflate]
  -- i.e., top ≤ j(top) in frame ordering (inflate says a ≤ j(a))
  -- Also j is idempotent. But we need j(top) = top directly.
  -- Use: pres_meet top top gives j(meet(top,top)) = meet(j(top), j(top))
  -- congrArg j (meet_idem top) gives j(meet(top,top)) = j(top)
  -- So j(top) = meet(j(top),j(top))  [by trans symm ...]
  -- meet_idem(j(top)) gives meet(j(top),j(top)) = j(top)
  -- So j(top) = j(top), which is circular.
  -- Instead: inflate(j(top)): meet(j(top), j(j(top))) = j(top)
  -- idempotent(top): j(j(top)) = j(top)
  -- So meet(j(top), j(top)) = j(top) [by congrArg in inflate]
  -- inflate(top): meet(top, j(top)) = top
  -- So top = meet(top, j(top)) [symm inflate]
  -- meet_top(j(top)): meet(j(top), top) = j(top)
  -- meet_comm: meet(top, j(top)) = meet(j(top), top)
  -- So top = meet(j(top), top) = j(top)
  let p1 : Path (fr.meet fr.top (nu.j fr.top)) fr.top := nu.inflate fr.top
  let p2 : Path (fr.meet fr.top (nu.j fr.top)) (fr.meet (nu.j fr.top) fr.top) :=
    fr.meet_comm fr.top (nu.j fr.top)
  let p3 : Path (fr.meet (nu.j fr.top) fr.top) (nu.j fr.top) := fr.meet_top (nu.j fr.top)
  -- p1: meet(top, j(top)) = top
  -- p2 then p3: meet(top, j(top)) = j(top)
  -- So j(top) = top by symm(trans p2 p3) then p1
  Path.trans (Path.symm p3) (Path.trans (Path.symm p2) p1)

/-- Theorem 20: Nucleus is monotone (path witness) -/
noncomputable def nucleus_monotone_witness (a b : F) (p : Path (fr.meet a b) a) :
    Path (fr.meet (nu.j a) (nu.j b)) (nu.j a) :=
  let step1 : Path (nu.j (fr.meet a b)) (nu.j a) := Path.congrArg nu.j p
  Path.trans (Path.symm (nu.pres_meet a b)) step1

/-- Theorem 21: j(j(j(a))) = j(a) via transitivity -/
noncomputable def nucleus_triple_idem (a : F) : Path (nu.j (nu.j (nu.j a))) (nu.j a) :=
  Path.trans (nu.idempotent (nu.j a)) (nu.idempotent a)

/-- Theorem 22: Nucleus applied to meet then idem -/
noncomputable def nucleus_meet_idem (a b : F) :
    Path (nu.j (nu.j (fr.meet a b))) (fr.meet (nu.j a) (nu.j b)) :=
  Path.trans (nu.idempotent (fr.meet a b)) (nu.pres_meet a b)

/-- Theorem 23: Congruence through nucleus -/
noncomputable def nucleus_congr (a b : F) (p : Path a b) : Path (nu.j a) (nu.j b) :=
  Path.congrArg nu.j p

/-- Theorem 24: Nucleus on meet commutes with meet commutativity -/
noncomputable def nucleus_meet_comm (a b : F) :
    Path (nu.j (fr.meet a b)) (nu.j (fr.meet b a)) :=
  Path.congrArg nu.j (fr.meet_comm a b)

/-- Theorem 25: Nucleus on join bot -/
noncomputable def nucleus_join_bot (a : F) :
    Path (nu.j (fr.join a fr.bot)) (nu.j a) :=
  Path.congrArg nu.j (fr.join_bot a)

-- ============================================================
-- §4  SUBLOCALES VIA NUCLEI (Theorems 26–28)
-- ============================================================

/-- The fixed points of a nucleus form a subframe (sublocale). -/
structure Sublocale (F : Type u) (fr : Frame F) where
  nu : Nucleus F fr

/-- Theorem 26: j(a) is always a fixed point -/
noncomputable def sublocale_image_fixed (sl : Sublocale F fr) (a : F) :
    Path (sl.nu.j (sl.nu.j a)) (sl.nu.j a) :=
  sl.nu.idempotent a

/-- Theorem 27: Meet of fixed points is fixed -/
noncomputable def sublocale_meet_closed (sl : Sublocale F fr) (a b : F)
    (pa : Path (sl.nu.j a) a) (pb : Path (sl.nu.j b) b) :
    Path (sl.nu.j (fr.meet a b)) (fr.meet a b) :=
  let step1 := sl.nu.pres_meet a b
  let step2 := frame_meet_congrL fr (sl.nu.j a) a (sl.nu.j b) pa
  let step3 := frame_meet_congrR fr a (sl.nu.j b) b pb
  Path.trans step1 (Path.trans step2 step3)

/-- Theorem 28: Top is a fixed point under any nucleus -/
noncomputable def sublocale_top_fixed (sl : Sublocale F fr) :
    Path (sl.nu.j fr.top) fr.top :=
  nucleus_pres_top sl.nu

-- ============================================================
-- §5  LOCALE AS DUAL OF FRAME (Theorems 29–31)
-- ============================================================

/-- A Locale is the formal dual of a Frame. -/
structure Locale (L : Type u) where
  frameOf  : Type u
  fr       : Frame frameOf

/-- Theorem 29: Locale morphism = frame hom in opposite direction -/
structure LocaleMorphism (L1 L2 : Type u) (loc1 : Locale L1) (loc2 : Locale L2) where
  star : FrameHom loc2.frameOf loc1.frameOf loc2.fr loc1.fr

/-- Theorem 30: Identity locale morphism -/
noncomputable def localeMorphism_id (L : Type u) (loc : Locale L) : LocaleMorphism L L loc loc where
  star := frameHom_id loc.fr

/-- Theorem 31: Composition of locale morphisms (note reversal) -/
noncomputable def localeMorphism_comp {L1 L2 L3 : Type u}
    {loc1 : Locale L1} {loc2 : Locale L2} {loc3 : Locale L3}
    (g : LocaleMorphism L2 L3 loc2 loc3) (f : LocaleMorphism L1 L2 loc1 loc2) :
    LocaleMorphism L1 L3 loc1 loc3 where
  -- f* : O(L2) → O(L1),  g* : O(L3) → O(L2)
  -- (g ∘ f)* = f* ∘ g* : O(L3) → O(L1)
  star :=
    let fg : FrameHom loc3.frameOf loc1.frameOf loc3.fr loc1.fr :=
      { fn := fun x => f.star.fn (g.star.fn x)
        pres_top := Path.trans (Path.congrArg f.star.fn g.star.pres_top) f.star.pres_top
        pres_meet := fun a b =>
          Path.trans (Path.congrArg f.star.fn (g.star.pres_meet a b))
                     (f.star.pres_meet (g.star.fn a) (g.star.fn b))
        pres_sup := fun s =>
          Path.trans (Path.congrArg f.star.fn (g.star.pres_sup s))
                     (f.star.pres_sup (fun i => g.star.fn (s i))) }
    fg

-- ============================================================
-- §6  SPATIAL LOCALES AND SOBER SPACES (Theorems 32–35)
-- ============================================================

/-- A point of a locale is a frame hom to the two-element frame -/
structure LocalePoint (F : Type u) (fr : Frame F) where
  pt : F → Bool
  pres_top  : Path (pt fr.top) true
  pres_meet : (a b : F) → Path (pt (fr.meet a b)) (pt a && pt b)

/-- Theorem 32: A point preserves idempotence of meet -/
noncomputable def localePoint_idem (lp : LocalePoint F fr) (a : F) :
    Path (lp.pt (fr.meet a a)) (lp.pt a) :=
  Path.congrArg lp.pt (fr.meet_idem a)

/-- Theorem 33: A point preserves meet commutativity -/
noncomputable def localePoint_meet_comm (lp : LocalePoint F fr) (a b : F) :
    Path (lp.pt (fr.meet a b)) (lp.pt (fr.meet b a)) :=
  Path.congrArg lp.pt (fr.meet_comm a b)

/-- Spatial locale: has enough points -/
structure SpatialLocale (F : Type u) (fr : Frame F) where
  points : Type u
  eval   : points → LocalePoint F fr
  sep    : (a b : F) →
           ((p : points) → Path ((eval p).pt a) ((eval p).pt b)) →
           Path a b

/-- Theorem 34: In a spatial locale, top is detected by all points -/
noncomputable def spatial_top_detected (sp : SpatialLocale F fr) (p : sp.points) :
    Path ((sp.eval p).pt fr.top) true :=
  (sp.eval p).pres_top

/-- Theorem 35: Spatial locale meet preservation through points -/
noncomputable def spatial_meet_point (sp : SpatialLocale F fr)
    (p : sp.points) (a b : F) :
    Path ((sp.eval p).pt (fr.meet a b)) ((sp.eval p).pt a && (sp.eval p).pt b) :=
  (sp.eval p).pres_meet a b

-- ============================================================
-- §7  COMPACTNESS IN LOCALE THEORY (Theorems 36–37)
-- ============================================================

/-- A frame element is compact if covers have finite subcovers -/
structure CompactElement (F : Type u) (fr : Frame F) (k : F) where
  compact_cond : {I : Type u} → (d : I → F) →
    Path (fr.meet k (fr.sup d)) k →
    PSigma (fun (i : I) => Path (fr.meet k (d i)) k)

/-- A locale is compact if top is compact -/
structure CompactLocale (F : Type u) (fr : Frame F) where
  top_compact : CompactElement F fr fr.top

/-- Theorem 36: In a compact locale, top is covered by finite subfamily -/
noncomputable def compact_top_witness {I : Type u} (cl : CompactLocale F fr) (s : I → F)
    (cov : Path (fr.meet fr.top (fr.sup s)) fr.top) :
    PSigma (fun (i : I) => Path (fr.meet fr.top (s i)) fr.top) :=
  cl.top_compact.compact_cond s cov

/-- Theorem 37: Compact element meets with itself -/
noncomputable def compact_self_meet (k : F) (_ : CompactElement F fr k) :
    Path (fr.meet k k) k :=
  fr.meet_idem k

-- ============================================================
-- §8  REGULARITY IN LOCALE THEORY (Theorems 38–40)
-- ============================================================

/-- The "well-inside" relation -/
structure WellInside (F : Type u) (fr : Frame F) (a b : F) where
  complement : F
  disj       : Path (fr.meet a complement) fr.bot
  cover      : Path (fr.join b complement) fr.top

/-- A regular locale: every element is a join of elements well-inside it -/
structure RegularLocale (F : Type u) (fr : Frame F) where
  reg_family : (a : F) → Type u
  reg_elems  : (a : F) → reg_family a → F
  reg_well   : (a : F) → (i : reg_family a) → WellInside F fr (reg_elems a i) a
  reg_join   : (a : F) → Path (fr.sup (reg_elems a)) a

/-- Theorem 38: Well-inside complement disj is symmetric -/
noncomputable def wellInside_complement_symm {a b : F} (w : WellInside F fr a b) :
    Path (fr.meet w.complement a) fr.bot :=
  Path.trans (fr.meet_comm w.complement a) w.disj

/-- Theorem 39: Well-inside cover is symmetric in join -/
noncomputable def wellInside_cover_symm {a b : F} (w : WellInside F fr a b) :
    Path (fr.join w.complement b) fr.top :=
  Path.trans (fr.join_comm w.complement b) w.cover

/-- Theorem 40: Well-inside implies double disj -/
noncomputable def wellInside_both_disj {a b : F} (w : WellInside F fr a b) :
    Path (fr.meet (fr.meet a w.complement) (fr.meet w.complement a))
         (fr.meet fr.bot fr.bot) :=
  let p1 := frame_meet_congrL fr (fr.meet a w.complement) fr.bot
              (fr.meet w.complement a) w.disj
  let p2 := frame_meet_congrR fr fr.bot (fr.meet w.complement a) fr.bot
              (wellInside_complement_symm w)
  Path.trans p1 p2

-- ============================================================
-- §9  PRODUCT OF LOCALES (Theorems 41–44)
-- ============================================================

/-- Product frame -/
structure ProductFrame (F1 F2 : Type u) (fr1 : Frame F1) (fr2 : Frame F2) where
  carrier : Type u
  pfr     : Frame carrier
  proj1   : FrameHom carrier F1 pfr fr1
  proj2   : FrameHom carrier F2 pfr fr2

/-- Theorem 41: Product projection 1 preserves top -/
noncomputable def product_proj1_top {fr1 : Frame F} {fr2 : Frame G}
    (pf : ProductFrame F G fr1 fr2) :
    Path (pf.proj1.fn pf.pfr.top) fr1.top :=
  pf.proj1.pres_top

/-- Theorem 42: Product projection 1 preserves meet -/
noncomputable def product_proj_meet {fr1 : Frame F} {fr2 : Frame G}
    (pf : ProductFrame F G fr1 fr2) (a b : pf.carrier) :
    Path (pf.proj1.fn (pf.pfr.meet a b)) (fr1.meet (pf.proj1.fn a) (pf.proj1.fn b)) :=
  pf.proj1.pres_meet a b

/-- Theorem 43: Product projection 2 preserves top -/
noncomputable def product_proj2_top {fr1 : Frame F} {fr2 : Frame G}
    (pf : ProductFrame F G fr1 fr2) :
    Path (pf.proj2.fn pf.pfr.top) fr2.top :=
  pf.proj2.pres_top

/-- Theorem 44: Product projection 2 preserves meet -/
noncomputable def product_proj2_meet {fr1 : Frame F} {fr2 : Frame G}
    (pf : ProductFrame F G fr1 fr2) (a b : pf.carrier) :
    Path (pf.proj2.fn (pf.pfr.meet a b)) (fr2.meet (pf.proj2.fn a) (pf.proj2.fn b)) :=
  pf.proj2.pres_meet a b

-- ============================================================
-- §10  STONE DUALITY STRUCTURE (Theorems 45–49)
-- ============================================================

/-- A coherent frame: compact elements form a sublattice -/
structure CoherentFrame (F : Type u) (fr : Frame F) where
  compacts    : Type u
  embed       : compacts → F
  comp_meet   : compacts → compacts → compacts
  comp_top    : compacts
  meet_compat : (a b : compacts) →
    Path (embed (comp_meet a b)) (fr.meet (embed a) (embed b))
  top_compat  : Path (embed comp_top) fr.top
  basis       : (x : F) → Type u
  basis_elems : (x : F) → basis x → compacts
  basis_sup   : (x : F) → Path (fr.sup (fun i => embed (basis_elems x i))) x

/-- Theorem 45: Coherent frame compact meet is associative via frame meet -/
noncomputable def coherent_meet_assoc (cf : CoherentFrame F fr) (a b c : cf.compacts) :
    Path (cf.embed (cf.comp_meet (cf.comp_meet a b) c))
         (fr.meet (fr.meet (cf.embed a) (cf.embed b)) (cf.embed c)) :=
  let p1 := cf.meet_compat (cf.comp_meet a b) c
  let p2 := frame_meet_congrL fr (cf.embed (cf.comp_meet a b))
              (fr.meet (cf.embed a) (cf.embed b)) (cf.embed c)
              (cf.meet_compat a b)
  Path.trans p1 p2

/-- Theorem 46: Coherent frame compact top is idempotent -/
noncomputable def coherent_top_idem (cf : CoherentFrame F fr) :
    Path (cf.embed (cf.comp_meet cf.comp_top cf.comp_top)) (cf.embed cf.comp_top) :=
  let p1 := cf.meet_compat cf.comp_top cf.comp_top
  let p2 := frame_meet_congrL fr (cf.embed cf.comp_top) fr.top (cf.embed cf.comp_top) cf.top_compat
  let p3 := frame_meet_congrR fr fr.top (cf.embed cf.comp_top) fr.top cf.top_compat
  let p4 := fr.meet_idem fr.top
  let p5 := Path.symm cf.top_compat
  Path.trans p1 (Path.trans p2 (Path.trans p3 (Path.trans p4 p5)))

/-- A Boolean frame / Boolean algebra structure on a frame -/
structure BooleanFrame (F : Type u) (fr : Frame F) where
  compl       : F → F
  compl_meet  : (a : F) → Path (fr.meet a (compl a)) fr.bot
  compl_join  : (a : F) → Path (fr.join a (compl a)) fr.top

/-- Theorem 47: Complement gives well-inside -/
noncomputable def boolean_wellInside (bf : BooleanFrame F fr) (a : F) :
    WellInside F fr a a where
  complement := bf.compl a
  disj := bf.compl_meet a
  cover := bf.compl_join a

/-- Theorem 48: In a Boolean frame, compl(a) ∧ a = ⊥ -/
noncomputable def boolean_compl_meet_symm (bf : BooleanFrame F fr) (a : F) :
    Path (fr.meet (bf.compl a) a) fr.bot :=
  Path.trans (fr.meet_comm (bf.compl a) a) (bf.compl_meet a)

/-- Theorem 49: Boolean frame partition simplifies to a -/
noncomputable def boolean_partition_simp (bf : BooleanFrame F fr) (a : F) :
    Path (fr.meet a (fr.join a (bf.compl a))) a :=
  let step1 := frame_meet_congrR fr a (fr.join a (bf.compl a)) fr.top (bf.compl_join a)
  Path.trans step1 (fr.meet_top a)

-- ============================================================
-- §11  LOCALIC GROUPS (Theorems 50–54)
-- ============================================================

/-- A localic group: a group object in the category of locales -/
structure LocalicGroup (F : Type u) (fr : Frame F) where
  mulFrame   : Type u
  mulFr      : Frame mulFrame
  mul_hom    : FrameHom F mulFrame fr mulFr
  unit       : F
  unit_left  : (a : F) → Path (fr.meet unit a) a
  unit_right : (a : F) → Path (fr.meet a unit) a
  inv_hom    : FrameHom F F fr fr

/-- Theorem 50: Inverse preserves top -/
noncomputable def localicGroup_inv_top (lg : LocalicGroup F fr) :
    Path (lg.inv_hom.fn fr.top) fr.top :=
  lg.inv_hom.pres_top

/-- Theorem 51: Inverse preserves meet -/
noncomputable def localicGroup_inv_meet (lg : LocalicGroup F fr) (a b : F) :
    Path (lg.inv_hom.fn (fr.meet a b))
         (fr.meet (lg.inv_hom.fn a) (lg.inv_hom.fn b)) :=
  lg.inv_hom.pres_meet a b

/-- Theorem 52: Multiplication hom preserves top -/
noncomputable def localicGroup_mul_top (lg : LocalicGroup F fr) :
    Path (lg.mul_hom.fn fr.top) lg.mulFr.top :=
  lg.mul_hom.pres_top

/-- Theorem 53: Unit meet idempotence -/
noncomputable def localicGroup_unit_idem (lg : LocalicGroup F fr) :
    Path (fr.meet lg.unit lg.unit) lg.unit :=
  fr.meet_idem lg.unit

/-- Theorem 54: Inverse composed with meet preserves commutativity -/
noncomputable def localicGroup_inv_meet_comm (lg : LocalicGroup F fr) (a b : F) :
    Path (lg.inv_hom.fn (fr.meet a b)) (lg.inv_hom.fn (fr.meet b a)) :=
  Path.congrArg lg.inv_hom.fn (fr.meet_comm a b)

-- ============================================================
-- §12  ADDITIONAL PATH ALGEBRA IN FRAMES (Theorems 55–65)
-- ============================================================

/-- Theorem 55: Mac Lane pentagon for meet associativity -/
noncomputable def frame_pentagon (a b c d : F) :
    Path (fr.meet (fr.meet (fr.meet a b) c) d)
         (fr.meet a (fr.meet b (fr.meet c d))) :=
  let step1 := fr.meet_assoc (fr.meet a b) c d
  let step2 := fr.meet_assoc a b (fr.meet c d)
  Path.trans step1 step2

/-- Theorem 56: Three-fold commutativity path -/
noncomputable def frame_meet_comm3 (a b c : F) :
    Path (fr.meet a (fr.meet b c))
         (fr.meet b (fr.meet a c)) :=
  let step1 := Path.symm (fr.meet_assoc a b c)
  let step2 := frame_meet_congrL fr (fr.meet a b) (fr.meet b a) c (fr.meet_comm a b)
  let step3 := fr.meet_assoc b a c
  Path.trans step1 (Path.trans step2 step3)

/-- Theorem 57: Join pentagon -/
noncomputable def frame_join_pentagon (a b c d : F) :
    Path (fr.join (fr.join (fr.join a b) c) d)
         (fr.join a (fr.join b (fr.join c d))) :=
  let step1 := fr.join_assoc (fr.join a b) c d
  let step2 := fr.join_assoc a b (fr.join c d)
  Path.trans step1 step2

/-- Theorem 58: Absorption chain -/
noncomputable def frame_absorption_chain (a b : F) :
    Path (fr.meet a (fr.join a (fr.meet a b))) a :=
  let inner := fr.absorb_jm a b
  let step1 := frame_meet_congrR fr a (fr.join a (fr.meet a b)) a inner
  Path.trans step1 (fr.meet_idem a)

/-- Theorem 59: Nucleus preserves frame meet associativity -/
noncomputable def nucleus_meet_assoc (a b c : F) :
    Path (nu.j (fr.meet (fr.meet a b) c))
         (nu.j (fr.meet a (fr.meet b c))) :=
  Path.congrArg nu.j (fr.meet_assoc a b c)

/-- Theorem 60: Nucleus distributes over frame meet twice -/
noncomputable def nucleus_meet_expand (a b c : F) :
    Path (nu.j (fr.meet a (fr.meet b c)))
         (fr.meet (nu.j a) (fr.meet (nu.j b) (nu.j c))) :=
  let step1 := nu.pres_meet a (fr.meet b c)
  let step2 := Path.congrArg (fun x => fr.meet (nu.j a) x) (nu.pres_meet b c)
  Path.trans step1 step2

/-- Theorem 61: Frame hom composition preserves meet -/
noncomputable def frameHom_comp_meet {H : Type u} {frH : Frame H}
    (g : FrameHom G H frG frH) (f : FrameHom F G fr frG) (a b : F) :
    Path (g.fn (f.fn (fr.meet a b)))
         (frH.meet (g.fn (f.fn a)) (g.fn (f.fn b))) :=
  let step1 := Path.congrArg g.fn (f.pres_meet a b)
  let step2 := g.pres_meet (f.fn a) (f.fn b)
  Path.trans step1 step2

/-- Theorem 62: Nucleus on sup idempotent -/
noncomputable def nucleus_sup_idem {I : Type u} (s : I → F) :
    Path (nu.j (nu.j (fr.sup s))) (nu.j (fr.sup s)) :=
  nu.idempotent (fr.sup s)

/-- Theorem 63: Four-fold meet associativity for joins -/
noncomputable def frame_join_comm3 (a b c : F) :
    Path (fr.join a (fr.join b c))
         (fr.join b (fr.join a c)) :=
  let step1 := Path.symm (fr.join_assoc a b c)
  let step2 := frame_join_congrL fr (fr.join a b) (fr.join b a) c (fr.join_comm a b)
  let step3 := fr.join_assoc b a c
  Path.trans step1 (Path.trans step2 step3)

/-- Theorem 64: Infinite distributivity then nucleus -/
noncomputable def nucleus_inf_dist (a : F) {I : Type u} (b : I → F) :
    Path (nu.j (fr.meet a (fr.sup b)))
         (nu.j (fr.sup (fun i => fr.meet a (b i)))) :=
  Path.congrArg nu.j (fr.inf_dist a b)

/-- Theorem 65: Nucleus applied to congruent meet arguments -/
noncomputable def nucleus_congr_meet (a b c d : F) (p : Path a c) (q : Path b d) :
    Path (nu.j (fr.meet a b)) (nu.j (fr.meet c d)) :=
  Path.congrArg nu.j
    (Path.trans (frame_meet_congrL fr a c b p) (frame_meet_congrR fr c b d q))

end LocaleTheoryDeep
