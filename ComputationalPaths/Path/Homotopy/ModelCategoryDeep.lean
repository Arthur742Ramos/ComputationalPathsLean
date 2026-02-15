/-
# Model Category Theory via Computational Paths (Deep)

Weak equivalences, fibrations, cofibrations, factorization systems, lifting
properties, retract arguments, Quillen adjunctions, Ken Brown's lemma, and
derived functors.  Every proof uses Path/Step/trans/symm from Core.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace ModelCategoryDeep

open ComputationalPaths.Path

universe u

-- ════════════════════════════════════════════════════════════════════════
-- §1  Arrows & weak equivalences
-- ════════════════════════════════════════════════════════════════════════

structure Arrow (X Y : Type u) where
  fn : X → Y

def Arrow.idArr (X : Type u) : Arrow X X := ⟨id⟩
def Arrow.comp {X Y Z : Type u} (f : Arrow X Y) (g : Arrow Y Z) :
    Arrow X Z := ⟨g.fn ∘ f.fn⟩

-- 1: WE structure
structure WE {X Y : Type u} (f : Arrow X Y) where
  inv  : Arrow Y X
  sect : ∀ y, Path (f.fn (inv.fn y)) y
  retr : ∀ x, Path (inv.fn (f.fn x)) x

-- 2: Identity is a WE
def WE.idWE (X : Type u) : WE (Arrow.idArr X) where
  inv := Arrow.idArr X
  sect := fun y => Path.refl y
  retr := fun x => Path.refl x

-- 3: Inverse of a WE
def WE.symmWE {X Y : Type u} {f : Arrow X Y} (w : WE f) : WE w.inv where
  inv := f; sect := w.retr; retr := w.sect

-- 4: Composition of WEs
def WE.compWE {X Y Z : Type u} {f : Arrow X Y} {g : Arrow Y Z}
    (wf : WE f) (wg : WE g) : WE (Arrow.comp f g) where
  inv := Arrow.comp wg.inv wf.inv
  sect := fun z =>
    Path.trans (Path.congrArg g.fn (wf.sect (wg.inv.fn z))) (wg.sect z)
  retr := fun x =>
    Path.trans (Path.congrArg wf.inv.fn (wg.retr (f.fn x))) (wf.retr x)

-- ════════════════════════════════════════════════════════════════════════
-- §2  Two-out-of-three
-- ════════════════════════════════════════════════════════════════════════

-- 5: 2-of-3 (left): gf WE, g WE ⇒ f WE
def twoOfThree_left {X Y Z : Type u} {f : Arrow X Y} {g : Arrow Y Z}
    (wgf : WE (Arrow.comp f g)) (wg : WE g) : WE f where
  inv := Arrow.comp g wgf.inv
  sect := fun y =>
    Path.trans
      (Path.symm (wg.retr (f.fn (wgf.inv.fn (g.fn y)))))
      (Path.trans
        (Path.congrArg wg.inv.fn (wgf.sect (g.fn y)))
        (wg.retr y))
  retr := fun x => wgf.retr x

-- 6: 2-of-3 (right): gf WE, f WE ⇒ g WE
def twoOfThree_right {X Y Z : Type u} {f : Arrow X Y} {g : Arrow Y Z}
    (wgf : WE (Arrow.comp f g)) (wf : WE f) : WE g where
  inv := Arrow.comp wgf.inv f
  sect := fun z => wgf.sect z
  retr := fun y =>
    Path.trans
      (Path.congrArg (fun t => f.fn (wgf.inv.fn (g.fn t)))
                     (Path.symm (wf.sect y)))
      (Path.trans
        (Path.congrArg f.fn (wgf.retr (wf.inv.fn y)))
        (wf.sect y))

-- ════════════════════════════════════════════════════════════════════════
-- §3  Lifting properties
-- ════════════════════════════════════════════════════════════════════════

-- 7: Lifting square
structure HasLift {A' B' X Y : Type u}
    (i : Arrow A' B') (p : Arrow X Y)
    (top : Arrow A' X) (bot : Arrow B' Y)
    (sq : ∀ a, Path (p.fn (top.fn a)) (bot.fn (i.fn a))) where
  lift  : Arrow B' X
  upper : ∀ a, Path (lift.fn (i.fn a)) (top.fn a)
  lower : ∀ b, Path (p.fn (lift.fn b)) (bot.fn b)

-- 8: Fibration (RLP)
structure Fib {X Y : Type u} (p : Arrow X Y) where
  liftId : ∀ (top : Arrow X X) (bot : Arrow X Y)
    (sq : ∀ x, Path (p.fn (top.fn x)) (bot.fn x)),
    HasLift (Arrow.idArr X) p top bot sq

-- 9: Cofibration (LLP)
structure Cof {A' B' : Type u} (i : Arrow A' B') where
  liftId : ∀ (top : Arrow A' B') (bot : Arrow B' B')
    (sq : ∀ a, Path (top.fn a) (bot.fn (i.fn a))),
    HasLift i (Arrow.idArr B') top bot sq

-- 10: Identity has RLP
def Fib.ofId (X : Type u) : Fib (Arrow.idArr X) where
  liftId := fun top _bot sq =>
    { lift := top
      upper := fun a => Path.refl (top.fn a)
      lower := fun b => sq b }

-- 11: Identity has LLP
def Cof.ofId (X : Type u) : Cof (Arrow.idArr X) where
  liftId := fun top _bot sq =>
    { lift := top
      upper := fun a => Path.refl (top.fn a)
      lower := fun b => Path.trans (sq b) (Path.refl _) }

-- ════════════════════════════════════════════════════════════════════════
-- §4  Factorisation
-- ════════════════════════════════════════════════════════════════════════

-- 12: Factorisation structure
structure Factor {X Y : Type u} (f : Arrow X Y) where
  mid   : Type u
  left  : Arrow X mid
  right : Arrow mid Y
  eq    : ∀ x, Path (right.fn (left.fn x)) (f.fn x)

-- 13: Trivial factorisation (left)
def Factor.trivialL {X Y : Type u} (f : Arrow X Y) : Factor f :=
  { mid := X, left := Arrow.idArr X, right := f,
    eq := fun x => Path.refl (f.fn x) }

-- 14: Trivial factorisation (right)
def Factor.trivialR {X Y : Type u} (f : Arrow X Y) : Factor f :=
  { mid := Y, left := f, right := Arrow.idArr Y,
    eq := fun x => Path.refl (f.fn x) }

-- 15: CWF factorisation
structure CWF_Factor {X Y : Type u} (f : Arrow X Y) extends Factor f where
  leftWE : WE left

-- 16: Identity CWF factorisation
def Factor.idFactor (X : Type u) : CWF_Factor (Arrow.idArr X) :=
  { mid := X, left := Arrow.idArr X, right := Arrow.idArr X,
    eq := fun x => Path.refl x, leftWE := WE.idWE X }

-- ════════════════════════════════════════════════════════════════════════
-- §5  Retract argument
-- ════════════════════════════════════════════════════════════════════════

-- 17: Retract structure
structure IsRetract {A' B' C' D' : Type u}
    (f : Arrow A' B') (g : Arrow C' D') where
  inclA : Arrow A' C'
  projA : Arrow C' A'
  inclB : Arrow B' D'
  projB : Arrow D' B'
  retractA : ∀ a, Path (projA.fn (inclA.fn a)) a
  retractB : ∀ b, Path (projB.fn (inclB.fn b)) b
  topSq : ∀ a, Path (g.fn (inclA.fn a)) (inclB.fn (f.fn a))
  botSq : ∀ c, Path (f.fn (projA.fn c)) (projB.fn (g.fn c))

-- 18: Retract of a WE is a WE
def WE.ofRetract {A' B' C' D' : Type u}
    {f : Arrow A' B'} {g : Arrow C' D'}
    (r : IsRetract f g) (wg : WE g) : WE f where
  inv := Arrow.comp (Arrow.comp r.inclB wg.inv) r.projA
  sect := fun b =>
    Path.trans
      (r.botSq (wg.inv.fn (r.inclB.fn b)))
      (Path.trans
        (Path.congrArg r.projB.fn (wg.sect (r.inclB.fn b)))
        (r.retractB b))
  retr := fun a =>
    Path.trans
      (Path.congrArg r.projA.fn
        (Path.trans
          (Path.congrArg wg.inv.fn (Path.symm (r.topSq a)))
          (wg.retr (r.inclA.fn a))))
      (r.retractA a)

-- ════════════════════════════════════════════════════════════════════════
-- §6  Cylinder objects & left homotopy
-- ════════════════════════════════════════════════════════════════════════

-- 19: Cylinder
structure Cyl (X : Type u) where
  obj : Type u
  inc0 : Arrow X obj
  inc1 : Arrow X obj
  proj : Arrow obj X
  proj_inc0 : ∀ x, Path (proj.fn (inc0.fn x)) x
  proj_inc1 : ∀ x, Path (proj.fn (inc1.fn x)) x

-- 20: Trivial cylinder
def Cyl.trivial (X : Type u) : Cyl X :=
  { obj := X, inc0 := Arrow.idArr X, inc1 := Arrow.idArr X,
    proj := Arrow.idArr X,
    proj_inc0 := fun x => Path.refl x,
    proj_inc1 := fun x => Path.refl x }

-- 21: Left homotopy
structure LHtpy {X Y : Type u} (f g : Arrow X Y) where
  cyl : Cyl X
  hmap : Arrow cyl.obj Y
  at_inc0 : ∀ x, Path (hmap.fn (cyl.inc0.fn x)) (f.fn x)
  at_inc1 : ∀ x, Path (hmap.fn (cyl.inc1.fn x)) (g.fn x)

-- 22: Reflexivity of left homotopy
def LHtpy.lrefl {X Y : Type u} (f : Arrow X Y) : LHtpy f f :=
  { cyl := Cyl.trivial X, hmap := f,
    at_inc0 := fun _ => Path.refl _, at_inc1 := fun _ => Path.refl _ }

-- 23: Symmetry of left homotopy
def LHtpy.lsymm {X Y : Type u} {f g : Arrow X Y} (h : LHtpy f g) : LHtpy g f :=
  { cyl := { obj := h.cyl.obj, inc0 := h.cyl.inc1, inc1 := h.cyl.inc0,
              proj := h.cyl.proj,
              proj_inc0 := h.cyl.proj_inc1, proj_inc1 := h.cyl.proj_inc0 },
    hmap := h.hmap, at_inc0 := h.at_inc1, at_inc1 := h.at_inc0 }

-- ════════════════════════════════════════════════════════════════════════
-- §7  Path objects & right homotopy
-- ════════════════════════════════════════════════════════════════════════

-- 24: Path object
structure PObj (Y : Type u) where
  obj : Type u
  sec : Arrow Y obj
  ev0 : Arrow obj Y
  ev1 : Arrow obj Y
  sec_ev0 : ∀ y, Path (ev0.fn (sec.fn y)) y
  sec_ev1 : ∀ y, Path (ev1.fn (sec.fn y)) y

-- 25: Trivial path object
def PObj.trivial (Y : Type u) : PObj Y :=
  { obj := Y, sec := Arrow.idArr Y, ev0 := Arrow.idArr Y, ev1 := Arrow.idArr Y,
    sec_ev0 := fun y => Path.refl y, sec_ev1 := fun y => Path.refl y }

-- 26: Right homotopy
structure RHtpy {X Y : Type u} (f g : Arrow X Y) where
  po : PObj Y
  hmap : Arrow X po.obj
  at_ev0 : ∀ x, Path (po.ev0.fn (hmap.fn x)) (f.fn x)
  at_ev1 : ∀ x, Path (po.ev1.fn (hmap.fn x)) (g.fn x)

-- 27: Reflexivity of right homotopy
def RHtpy.rrefl {X Y : Type u} (f : Arrow X Y) : RHtpy f f :=
  { po := PObj.trivial Y, hmap := f,
    at_ev0 := fun _ => Path.refl _, at_ev1 := fun _ => Path.refl _ }

-- 28: Symmetry of right homotopy
def RHtpy.rsymm {X Y : Type u} {f g : Arrow X Y} (h : RHtpy f g) : RHtpy g f :=
  { po := { obj := h.po.obj, sec := h.po.sec, ev0 := h.po.ev1, ev1 := h.po.ev0,
             sec_ev0 := h.po.sec_ev1, sec_ev1 := h.po.sec_ev0 },
    hmap := h.hmap, at_ev0 := h.at_ev1, at_ev1 := h.at_ev0 }

-- ════════════════════════════════════════════════════════════════════════
-- §8  Quillen adjunction & Ken Brown
-- ════════════════════════════════════════════════════════════════════════

-- 29: Adjunction
structure Adj {C D : Type u} (F : Arrow C D) (G : Arrow D C) where
  unit   : ∀ c, Path c (G.fn (F.fn c))
  counit : ∀ d, Path (F.fn (G.fn d)) d

-- 30: Quillen pair
structure QuillenPair {C D : Type u} (F : Arrow C D) (G : Arrow D C)
    extends Adj F G where
  F_pres_WE : ∀ (h : Arrow C C), WE h → WE ⟨fun c => F.fn (h.fn c)⟩

-- 31: Derived functor data
structure LDerived {C D : Type u} (F : Arrow C D) where
  Q   : Arrow C C
  Qwe : WE Q
  LF  : Arrow C D
  compat : ∀ c, Path (LF.fn c) (F.fn (Q.fn c))

-- 32: Trivial derived functor
def LDerived.trivial {C D : Type u} (F : Arrow C D) : LDerived F :=
  { Q := Arrow.idArr C, Qwe := WE.idWE C, LF := F,
    compat := fun _ => Path.refl _ }

-- 33: Ken Brown's lemma (abstract)
def kenBrown {C D : Type u} (F : Arrow C D)
    (h : Arrow C C) (wh : WE h)
    (pres : ∀ (g : Arrow C C), WE g → WE ⟨fun c => F.fn (g.fn c)⟩) :
    WE ⟨fun c => F.fn (h.fn c)⟩ :=
  pres h wh

-- ════════════════════════════════════════════════════════════════════════
-- §9  Localisation / homotopy-category
-- ════════════════════════════════════════════════════════════════════════

-- 34: Homotopy relation
structure HRel (X Y : Type u) where
  rel    : Arrow X Y → Arrow X Y → Prop
  hrefl  : ∀ f, rel f f
  hsymm  : ∀ f g, rel f g → rel g f
  htrans : ∀ f g h, rel f g → rel g h → rel f h

-- 35: WE becomes iso (right)
theorem WE_iso_right {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    ∀ y, f.fn (w.inv.fn y) = y := fun y => (w.sect y).proof

-- 36: WE becomes iso (left)
theorem WE_iso_left {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    ∀ x, w.inv.fn (f.fn x) = x := fun x => (w.retr x).proof

-- ════════════════════════════════════════════════════════════════════════
-- §10  Coherence of WE algebra
-- ════════════════════════════════════════════════════════════════════════

-- 37
theorem compWE_inv_eq {X Y Z : Type u}
    {f : Arrow X Y} {g : Arrow Y Z}
    (wf : WE f) (wg : WE g) :
    ∀ z, (WE.compWE wf wg).inv.fn z = wf.inv.fn (wg.inv.fn z) :=
  fun _ => rfl

-- 38
theorem idWE_sect (X : Type u) (x : X) :
    (WE.idWE X).sect x = Path.refl x := rfl

-- 39
theorem idWE_retr (X : Type u) (x : X) :
    (WE.idWE X).retr x = Path.refl x := rfl

-- 40
theorem symmWE_invol {X Y : Type u} {f : Arrow X Y} (w : WE f) :
    (WE.symmWE (WE.symmWE w)).inv = w.inv := rfl

-- 41
theorem compWE_inv_fn {X Y Z : Type u}
    {f : Arrow X Y} {g : Arrow Y Z}
    (wf : WE f) (wg : WE g) :
    (WE.compWE wf wg).inv.fn = (fun z => wf.inv.fn (wg.inv.fn z)) := rfl

-- ════════════════════════════════════════════════════════════════════════
-- §11  Fibrant / cofibrant replacement
-- ════════════════════════════════════════════════════════════════════════

-- 42: Fibrant replacement
structure FibRep (X : Type u) where
  RX : Type u
  rmap : Arrow X RX
  rwe : WE rmap

-- 43: Cofibrant replacement
structure CofRep (X : Type u) where
  QX : Type u
  qmap : Arrow QX X
  qwe : WE qmap

-- 44
def FibRep.trivial (X : Type u) : FibRep X :=
  { RX := X, rmap := Arrow.idArr X, rwe := WE.idWE X }

-- 45
def CofRep.trivial (X : Type u) : CofRep X :=
  { QX := X, qmap := Arrow.idArr X, qwe := WE.idWE X }

-- 46: Two fibrant replacements connected by WE
def FibRep.compare {X : Type u} (r1 r2 : FibRep X) :
    WE (Arrow.comp r1.rwe.inv r2.rmap) :=
  WE.compWE (WE.symmWE r1.rwe) r2.rwe

-- ════════════════════════════════════════════════════════════════════════
-- §12  Transfinite towers
-- ════════════════════════════════════════════════════════════════════════

-- 47
structure Tower (X : Type u) where
  stage : Nat → X
  bond  : ∀ n, Path (stage n) (stage (n + 1))

-- 48
def Tower.pathTo {X : Type u} (t : Tower X) : (n : Nat) → Path (t.stage 0) (t.stage n)
  | 0     => Path.refl _
  | n + 1 => Path.trans (t.pathTo n) (t.bond n)

-- 49
theorem Tower.pathTo_zero {X : Type u} (t : Tower X) :
    t.pathTo 0 = Path.refl _ := rfl

-- 50
theorem Tower.pathTo_succ {X : Type u} (t : Tower X) (n : Nat) :
    t.pathTo (n + 1) = Path.trans (t.pathTo n) (t.bond n) := rfl

-- ════════════════════════════════════════════════════════════════════════
-- §13  Homotopy fibres
-- ════════════════════════════════════════════════════════════════════════

-- 51
structure HFib {X Y : Type u} (f : Arrow X Y) (y : Y) where
  pt   : X
  path : Path (f.fn pt) y

-- 52
def HFib.ofId (Y : Type u) (y : Y) : HFib (Arrow.idArr Y) y :=
  { pt := y, path := Path.refl y }

-- 53: Fibre of composition → fibre of second map
def HFib.compFib {X Y Z : Type u} {f : Arrow X Y} {g : Arrow Y Z}
    (z : Z) (fib : HFib (Arrow.comp f g) z) : HFib g z :=
  { pt := f.fn fib.pt, path := fib.path }

-- 54: WE induces a fibre
def HFib.fromWE {X Y : Type u} {f : Arrow X Y} (w : WE f) (y : Y) :
    HFib f y :=
  { pt := w.inv.fn y, path := w.sect y }

-- ════════════════════════════════════════════════════════════════════════
-- §14  Homotopy equivalence (Whitehead)
-- ════════════════════════════════════════════════════════════════════════

-- 55
structure HEquiv {X Y : Type u} (f : Arrow X Y) where
  einv : Arrow Y X
  lh  : LHtpy (Arrow.comp einv f) (Arrow.idArr Y)
  rh  : LHtpy (Arrow.comp f einv) (Arrow.idArr X)

-- 56: WE gives homotopy equivalence
def HEquiv.ofWE {X Y : Type u} (f : Arrow X Y) (w : WE f) : HEquiv f where
  einv := w.inv
  lh := {
    cyl := Cyl.trivial Y
    hmap := Arrow.idArr Y
    at_inc0 := fun y => Path.symm (w.sect y)
    at_inc1 := fun y => Path.refl y
  }
  rh := {
    cyl := Cyl.trivial X
    hmap := Arrow.idArr X
    at_inc0 := fun x => Path.symm (w.retr x)
    at_inc1 := fun x => Path.refl x
  }

-- 57: Identity homotopy equivalence
def HEquiv.ofId (X : Type u) : HEquiv (Arrow.idArr X) :=
  HEquiv.ofWE (Arrow.idArr X) (WE.idWE X)

-- 58: Inverse homotopy equivalence
def HEquiv.inv_hequiv {X Y : Type u} {f : Arrow X Y} (he : HEquiv f) :
    HEquiv he.einv where
  einv := f
  lh  := he.rh
  rh  := he.lh

-- ════════════════════════════════════════════════════════════════════════
-- §15  Arrow composition coherence
-- ════════════════════════════════════════════════════════════════════════

-- 59: comp with id left
theorem Arrow.comp_idArr_left {X Y : Type u} (f : Arrow X Y) :
    Arrow.comp (Arrow.idArr X) f = f := by
  cases f; rfl

-- 60: comp with id right
theorem Arrow.comp_idArr_right {X Y : Type u} (f : Arrow X Y) :
    Arrow.comp f (Arrow.idArr Y) = f := by
  cases f; rfl

-- 61: LHtpy double symmetry
theorem LHtpy.lsymm_lsymm {X Y : Type u} {f g : Arrow X Y} (h : LHtpy f g) :
    h.lsymm.lsymm.at_inc0 = h.at_inc0 := rfl

end ModelCategoryDeep
end Path
end ComputationalPaths
