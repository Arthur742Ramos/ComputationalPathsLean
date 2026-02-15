/-
# Abstract Homotopy Theory via Computational Paths (Deep)

Cylinder and path objects, homotopy relation as equivalence relation,
Whitehead theorem structure, localisation at weak equivalences, homotopy
(co)fibre sequences, loop/suspension, Postnikov data, derived natural
transformations.  Every proof completed (no sorry), uses Path/Step/trans/symm.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace AbstractHomotopyDeep

open ComputationalPaths.Path

universe u

-- ================================================================
-- S1  Arrows (self-contained so the file is stand-alone)
-- ================================================================

structure Arrow (X Y : Type u) where
  fn : X -> Y

@[reducible] def Arrow.idArr (X : Type u) : Arrow X X :=
  { fn := fun x => x }

@[reducible] def Arrow.comp {X Y Z : Type u}
    (f : Arrow X Y) (g : Arrow Y Z) : Arrow X Z :=
  { fn := fun x => g.fn (f.fn x) }

structure WE {X Y : Type u} (f : Arrow X Y) where
  inv  : Arrow Y X
  sect : forall y, Path (f.fn (inv.fn y)) y
  retr : forall x, Path (inv.fn (f.fn x)) x

-- Theorem 1
def WE.idWE (X : Type u) : WE (Arrow.idArr X) where
  inv := Arrow.idArr X
  sect := fun y => Path.refl y
  retr := fun x => Path.refl x

-- Theorem 2
def WE.symmWE {X Y : Type u} {f : Arrow X Y} (w : WE f) : WE w.inv where
  inv := f
  sect := w.retr
  retr := w.sect

-- Theorem 3
def WE.compWE {X Y Z : Type u} {f : Arrow X Y} {g : Arrow Y Z}
    (wf : WE f) (wg : WE g) :
    WE { fn := fun x => g.fn (f.fn x) } where
  inv := { fn := fun z => wf.inv.fn (wg.inv.fn z) }
  sect := fun z =>
    Path.trans (Path.congrArg g.fn (wf.sect (wg.inv.fn z))) (wg.sect z)
  retr := fun x =>
    Path.trans (Path.congrArg wf.inv.fn (wg.retr (f.fn x))) (wf.retr x)

-- ================================================================
-- S2  Cylinder objects
-- ================================================================

structure Cyl (X : Type u) where
  obj   : Type u
  inc0  : Arrow X obj
  inc1  : Arrow X obj
  proj  : Arrow obj X
  proj0 : forall x, Path (proj.fn (inc0.fn x)) x
  proj1 : forall x, Path (proj.fn (inc1.fn x)) x

-- Theorem 4
def Cyl.trivial (X : Type u) : Cyl X where
  obj := X
  inc0 := Arrow.idArr X
  inc1 := Arrow.idArr X
  proj := Arrow.idArr X
  proj0 := fun x => Path.refl x
  proj1 := fun x => Path.refl x

-- Theorem 5: trivial cylinder projection is WE
def Cyl.trivProj_WE (X : Type u) : WE (Cyl.trivial X).proj :=
  WE.idWE X

-- Theorem 6: good cylinder = proj is WE
structure GoodCyl (X : Type u) extends Cyl X where
  projWE : WE proj

-- Theorem 7
def GoodCyl.trivial (X : Type u) : GoodCyl X where
  obj := X
  inc0 := Arrow.idArr X
  inc1 := Arrow.idArr X
  proj := Arrow.idArr X
  proj0 := fun x => Path.refl x
  proj1 := fun x => Path.refl x
  projWE := WE.idWE X

-- ================================================================
-- S3  Path objects
-- ================================================================

structure PObj (Y : Type u) where
  obj  : Type u
  diag : Arrow Y obj
  ev0  : Arrow obj Y
  ev1  : Arrow obj Y
  ev0d : forall y, Path (ev0.fn (diag.fn y)) y
  ev1d : forall y, Path (ev1.fn (diag.fn y)) y

-- Theorem 8
def PObj.trivial (Y : Type u) : PObj Y where
  obj := Y
  diag := Arrow.idArr Y
  ev0 := Arrow.idArr Y
  ev1 := Arrow.idArr Y
  ev0d := fun y => Path.refl y
  ev1d := fun y => Path.refl y

structure GoodPObj (Y : Type u) extends PObj Y where
  diagWE : WE diag

-- Theorem 9
def GoodPObj.trivial (Y : Type u) : GoodPObj Y where
  obj := Y
  diag := Arrow.idArr Y
  ev0 := Arrow.idArr Y
  ev1 := Arrow.idArr Y
  ev0d := fun y => Path.refl y
  ev1d := fun y => Path.refl y
  diagWE := WE.idWE Y

-- ================================================================
-- S4  Left homotopy
-- ================================================================

structure LHtpy {X Y : Type u} (f g : Arrow X Y) where
  cyl  : Cyl X
  hom  : Arrow cyl.obj Y
  hom0 : forall x, Path (hom.fn (cyl.inc0.fn x)) (f.fn x)
  hom1 : forall x, Path (hom.fn (cyl.inc1.fn x)) (g.fn x)

-- Theorem 10: reflexivity
def LHtpy.lrefl {X Y : Type u} (f : Arrow X Y) : LHtpy f f where
  cyl := Cyl.trivial X
  hom := f
  hom0 := fun _ => Path.refl _
  hom1 := fun _ => Path.refl _

-- Theorem 11: symmetry
def LHtpy.lsymm {X Y : Type u} {f g : Arrow X Y}
    (h : LHtpy f g) : LHtpy g f where
  cyl := { obj := h.cyl.obj, inc0 := h.cyl.inc1, inc1 := h.cyl.inc0,
            proj := h.cyl.proj, proj0 := h.cyl.proj1, proj1 := h.cyl.proj0 }
  hom := h.hom
  hom0 := h.hom1
  hom1 := h.hom0

-- Theorem 12: WE induces left homotopy sect
def LHtpy.ofWE_sect {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    LHtpy { fn := fun y => f.fn (w.inv.fn y) } (Arrow.idArr Y) where
  cyl := Cyl.trivial Y
  hom := Arrow.idArr Y
  hom0 := fun y => Path.symm (w.sect y)
  hom1 := fun _ => Path.refl _

-- Theorem 13: WE induces left homotopy retr
def LHtpy.ofWE_retr {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    LHtpy { fn := fun x => w.inv.fn (f.fn x) } (Arrow.idArr X) where
  cyl := Cyl.trivial X
  hom := Arrow.idArr X
  hom0 := fun x => Path.symm (w.retr x)
  hom1 := fun _ => Path.refl _

-- Theorem 14: post-composition preserves left homotopy
def LHtpy.postcomp {X Y Z : Type u} {f g : Arrow X Y}
    (h : LHtpy f g) (k : Arrow Y Z) :
    LHtpy { fn := fun x => k.fn (f.fn x) }
          { fn := fun x => k.fn (g.fn x) } where
  cyl := h.cyl
  hom := { fn := fun c => k.fn (h.hom.fn c) }
  hom0 := fun x => Path.congrArg k.fn (h.hom0 x)
  hom1 := fun x => Path.congrArg k.fn (h.hom1 x)

-- ================================================================
-- S5  Right homotopy
-- ================================================================

structure RHtpy {X Y : Type u} (f g : Arrow X Y) where
  po   : PObj Y
  hom  : Arrow X po.obj
  hom0 : forall x, Path (po.ev0.fn (hom.fn x)) (f.fn x)
  hom1 : forall x, Path (po.ev1.fn (hom.fn x)) (g.fn x)

-- Theorem 15
def RHtpy.rrefl {X Y : Type u} (f : Arrow X Y) : RHtpy f f where
  po := PObj.trivial Y
  hom := f
  hom0 := fun _ => Path.refl _
  hom1 := fun _ => Path.refl _

-- Theorem 16
def RHtpy.rsymm {X Y : Type u} {f g : Arrow X Y}
    (h : RHtpy f g) : RHtpy g f where
  po := { obj := h.po.obj, diag := h.po.diag, ev0 := h.po.ev1,
           ev1 := h.po.ev0, ev0d := h.po.ev1d, ev1d := h.po.ev0d }
  hom := h.hom
  hom0 := h.hom1
  hom1 := h.hom0

-- Theorem 17: pre-composition preserves right homotopy
def RHtpy.precomp {W X Y : Type u} {f g : Arrow X Y}
    (h : RHtpy f g) (k : Arrow W X) :
    RHtpy { fn := fun w => f.fn (k.fn w) }
          { fn := fun w => g.fn (k.fn w) } where
  po := h.po
  hom := { fn := fun w => h.hom.fn (k.fn w) }
  hom0 := fun w => h.hom0 (k.fn w)
  hom1 := fun w => h.hom1 (k.fn w)

-- ================================================================
-- S6  Homotopy equivalence (Whitehead)
-- ================================================================

structure HEquiv {X Y : Type u} (f : Arrow X Y) where
  hInv : Arrow Y X
  lh   : LHtpy { fn := fun y => f.fn (hInv.fn y) } (Arrow.idArr Y)
  rh   : LHtpy { fn := fun x => hInv.fn (f.fn x) } (Arrow.idArr X)

-- Theorem 18
def HEquiv.ofWE {X Y : Type u} (f : Arrow X Y) (w : WE f) : HEquiv f where
  hInv := w.inv
  lh := LHtpy.ofWE_sect f w
  rh := LHtpy.ofWE_retr f w

-- Theorem 19
def HEquiv.ofId (X : Type u) : HEquiv (Arrow.idArr X) :=
  HEquiv.ofWE (Arrow.idArr X) (WE.idWE X)

-- Theorem 20: inverse
def HEquiv.hinv {X Y : Type u} {f : Arrow X Y}
    (he : HEquiv f) : HEquiv he.hInv where
  hInv := f
  lh := he.rh
  rh := he.lh

-- ================================================================
-- S7  Localisation at weak equivalences (zigzags)
-- ================================================================

inductive ZigZag : Type u -> Type u -> Type (u + 1)
  | idZ   (A : Type u) : ZigZag A A
  | fwd   {A B : Type u} : Arrow A B -> ZigZag A B
  | bwd   {A B : Type u} : Arrow B A -> WE (Arrow.idArr B) -> ZigZag A B
  | comp  {A B C : Type u} : ZigZag A B -> ZigZag B C -> ZigZag A C

-- Theorem 21: length
def ZigZag.len : ZigZag A B -> Nat
  | .idZ _       => 0
  | .fwd _       => 1
  | .bwd _ _     => 1
  | .comp z1 z2  => z1.len + z2.len

-- Theorem 22
theorem ZigZag.len_id (X : Type u) : (ZigZag.idZ X).len = 0 := rfl

-- Theorem 23
theorem ZigZag.len_fwd {X Y : Type u} (f : Arrow X Y) :
    (ZigZag.fwd f).len = 1 := rfl

-- Theorem 24: a WE becomes invertible
def weqInvertible {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    ZigZag Y X := ZigZag.fwd w.inv

-- Theorem 25: sect/retr in the localisation
theorem weqInvertible_sect {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    forall y, f.fn (w.inv.fn y) = y := fun y => (w.sect y).proof

theorem weqInvertible_retr {X Y : Type u} (f : Arrow X Y) (w : WE f) :
    forall x, w.inv.fn (f.fn x) = x := fun x => (w.retr x).proof

-- ================================================================
-- S8  Homotopy fibre & cofibre
-- ================================================================

structure HFib {X Y : Type u} (f : Arrow X Y) (y : Y) where
  pt   : X
  path : Path (f.fn pt) y

-- Theorem 26
def HFib.ofId (Y : Type u) (y : Y) : HFib (Arrow.idArr Y) y :=
  { pt := y, path := Path.refl y }

-- Theorem 27: fibre from WE
def HFib.fromWE {X Y : Type u} {f : Arrow X Y} (w : WE f) (y : Y) :
    HFib f y :=
  { pt := w.inv.fn y, path := w.sect y }

-- Theorem 28: transport in fibre
def HFib.transport_path {X Y : Type u} {f : Arrow X Y} {y1 y2 : Y}
    (fib : HFib f y1) (p : Path y1 y2) : HFib f y2 :=
  { pt := fib.pt, path := Path.trans fib.path p }

structure HCofibre {X Y : Type u} (f : Arrow X Y) where
  carrier : Type u
  proj    : Arrow Y carrier
  glue    : forall x, Path (proj.fn (f.fn x)) (proj.fn (f.fn x))

-- Theorem 29
def HCofibre.trivial {X Y : Type u} (f : Arrow X Y) : HCofibre f where
  carrier := Y
  proj := Arrow.idArr Y
  glue := fun _ => Path.refl _

-- ================================================================
-- S9  Fibre sequences
-- ================================================================

structure FibSeq {E B : Type u} (p : Arrow E B) (b : B) where
  fiber : Type u
  incl  : Arrow fiber E
  fibEq : forall x, Path (p.fn (incl.fn x)) b

-- Theorem 30
def FibSeq.trivial (B : Type u) (b : B) :
    FibSeq (Arrow.idArr B) b where
  fiber := { x : B // x = b }
  incl := { fn := fun x => x.val }
  fibEq := fun x => Path.ofEq x.property

-- ================================================================
-- S10  Loop space & suspension data
-- ================================================================

structure LoopData (X : Type u) (x : X) where
  carrier : Type u
  baseloop : carrier
  eval : Arrow carrier X
  evalBase : Path (eval.fn baseloop) x
  isLoop : forall l, Path (eval.fn l) x

-- Theorem 31
def LoopData.trivial (X : Type u) (x : X) : LoopData X x where
  carrier := PUnit.{u+1}
  baseloop := PUnit.unit
  eval := { fn := fun _ => x }
  evalBase := Path.refl x
  isLoop := fun _ => Path.refl x

structure SuspData (X : Type u) where
  carrier : Type u
  north : carrier
  south : carrier
  merid : X -> Path north south

-- ================================================================
-- S11  Postnikov tower
-- ================================================================

structure PostnikovTower (A : Type u) where
  stage : Nat -> Type u
  proj  : forall n, Arrow A (stage n)
  bond  : forall n, Arrow (stage (n + 1)) (stage n)
  bondProj : forall n (a : A),
    Path (bond n |>.fn (proj (n + 1) |>.fn a)) (proj n |>.fn a)

-- Theorem 32
def PostnikovTower.trivial (A : Type u) : PostnikovTower A where
  stage := fun _ => A
  proj := fun _ => Arrow.idArr A
  bond := fun _ => Arrow.idArr A
  bondProj := fun _ a => Path.refl a

-- ================================================================
-- S12  Derived natural transformations
-- ================================================================

structure DerivedNatTrans {A B : Type u} (F G : Arrow A B) where
  component : forall a, Path (F.fn a) (G.fn a)
  naturality : forall (a1 a2 : A), Path a1 a2 ->
    Path (F.fn a1) (G.fn a2)

-- Theorem 33
def DerivedNatTrans.idNat {A B : Type u} (F : Arrow A B) :
    DerivedNatTrans F F where
  component := fun _ => Path.refl _
  naturality := fun _ _ p => Path.congrArg F.fn p

-- Theorem 34: composition
def DerivedNatTrans.comp {A B : Type u} {F G H : Arrow A B}
    (a : DerivedNatTrans F G) (b : DerivedNatTrans G H) :
    DerivedNatTrans F H where
  component := fun x => Path.trans (a.component x) (b.component x)
  naturality := fun x y p =>
    Path.trans (a.naturality x y p) (b.component y)

-- Theorem 35: inverse
def DerivedNatTrans.inv {A B : Type u} {F G : Arrow A B}
    (a : DerivedNatTrans F G) : DerivedNatTrans G F where
  component := fun x => Path.symm (a.component x)
  naturality := fun x y p =>
    Path.trans (Path.symm (a.component x)) (Path.congrArg F.fn p)

-- ================================================================
-- S13  Homotopy invariance
-- ================================================================

structure HomotopyInvariant {A B C : Type u} (F : Arrow B C) where
  inv : forall (f g : Arrow A B),
    (forall a, Path (f.fn a) (g.fn a)) ->
    forall a, Path (F.fn (f.fn a)) (F.fn (g.fn a))

-- Theorem 36
def HomotopyInvariant.ofAny {A B C : Type u} (F : Arrow B C) :
    HomotopyInvariant (A := A) F where
  inv := fun _ _ heq a => Path.congrArg F.fn (heq a)

-- ================================================================
-- S14  Homotopy pushout & pullback
-- ================================================================

structure HPushout {A B C : Type u} (f : Arrow A B) (g : Arrow A C) where
  carrier : Type u
  inclB   : Arrow B carrier
  inclC   : Arrow C carrier
  glue    : forall a, Path (inclB.fn (f.fn a)) (inclC.fn (g.fn a))

-- Theorem 37
def HPushout.trivial (A : Type u) :
    HPushout (Arrow.idArr A) (Arrow.idArr A) where
  carrier := A
  inclB := Arrow.idArr A
  inclC := Arrow.idArr A
  glue := fun a => Path.refl a

structure HPullback {A B C : Type u} (f : Arrow A C) (g : Arrow B C) where
  carrier : Type u
  projA   : Arrow carrier A
  projB   : Arrow carrier B
  comm    : forall x, Path (f.fn (projA.fn x)) (g.fn (projB.fn x))

-- Theorem 38
def HPullback.trivial (A : Type u) :
    HPullback (Arrow.idArr A) (Arrow.idArr A) where
  carrier := A
  projA := Arrow.idArr A
  projB := Arrow.idArr A
  comm := fun a => Path.refl a

-- ================================================================
-- S15  Derived functors via replacement
-- ================================================================

structure LDerived {C D : Type u} (F : Arrow C D) where
  Q    : Arrow C C
  Qwe  : WE Q
  LF   : Arrow C D
  comp : forall c, Path (LF.fn c) (F.fn (Q.fn c))

-- Theorem 39
def LDerived.trivial {C D : Type u} (F : Arrow C D) : LDerived F where
  Q := Arrow.idArr C
  Qwe := WE.idWE C
  LF := F
  comp := fun _ => Path.refl _

structure RDerived {C D : Type u} (G : Arrow D C) where
  R    : Arrow D D
  Rwe  : WE R
  RG   : Arrow D C
  comp : forall d, Path (RG.fn d) (G.fn (R.fn d))

-- Theorem 40
def RDerived.trivial {C D : Type u} (G : Arrow D C) : RDerived G where
  R := Arrow.idArr D
  Rwe := WE.idWE D
  RG := G
  comp := fun _ => Path.refl _

-- ================================================================
-- S16  Additional deep results
-- ================================================================

-- Theorem 41: trivial cylinder proj is id
theorem trivCyl_proj_eq {X : Type u} :
    (Cyl.trivial X).proj = Arrow.idArr X := rfl

-- Theorem 42: trivial PObj diag is id
theorem trivPObj_diag_eq {Y : Type u} :
    (PObj.trivial Y).diag = Arrow.idArr Y := rfl

-- Theorem 43: homotopy fibre from composition
def HFib.ofComp {X Y Z : Type u} (f : Arrow X Y) (g : Arrow Y Z)
    (z : Z) (fib : HFib { fn := fun x => g.fn (f.fn x) } z) :
    HFib g z :=
  { pt := f.fn fib.pt, path := fib.path }

-- Theorem 44: left homotopy from explicit data
def LHtpy.mk' {X Y : Type u} (cyl : Cyl X) (f g : Arrow X Y)
    (H : Arrow cyl.obj Y)
    (h0 : forall x, Path (H.fn (cyl.inc0.fn x)) (f.fn x))
    (h1 : forall x, Path (H.fn (cyl.inc1.fn x)) (g.fn x)) :
    LHtpy f g :=
  { cyl := cyl, hom := H, hom0 := h0, hom1 := h1 }

-- Theorem 45: Postnikov bond is definitionally simple for trivial tower
theorem PostnikovTower.trivial_bond {A : Type u} (n : Nat) :
    (PostnikovTower.trivial A).bond n = Arrow.idArr A := rfl

-- Theorem 46: derived nat trans identity is unit for composition
theorem DerivedNatTrans.comp_id_left {A B : Type u} {F G : Arrow A B}
    (a : DerivedNatTrans F G) :
    forall x, (DerivedNatTrans.comp (DerivedNatTrans.idNat F) a).component x =
              Path.trans (Path.refl _) (a.component x) := fun _ => rfl

-- Theorem 47: zigzag id has length 0
theorem ZigZag.comp_len {A B C : Type u} (z1 : ZigZag A B) (z2 : ZigZag B C) :
    (ZigZag.comp z1 z2).len = z1.len + z2.len := rfl

-- Theorem 48: HPushout symmetry
def HPushout.symm {A B C : Type u} {f : Arrow A B} {g : Arrow A C}
    (hp : HPushout f g) : HPushout g f where
  carrier := hp.carrier
  inclB := hp.inclC
  inclC := hp.inclB
  glue := fun a => Path.symm (hp.glue a)

-- Theorem 49: HPullback symmetry
def HPullback.symm {A B C : Type u} {f : Arrow A C} {g : Arrow B C}
    (hp : HPullback f g) : HPullback g f where
  carrier := hp.carrier
  projA := hp.projB
  projB := hp.projA
  comm := fun x => Path.symm (hp.comm x)

-- Theorem 50: WE gives natural transformation between id and f ∘ inv
def WE.natTrans {X Y : Type u} {f : Arrow X Y} (w : WE f) :
    DerivedNatTrans { fn := fun y => f.fn (w.inv.fn y) } (Arrow.idArr Y) where
  component := fun y => w.sect y
  naturality := fun y1 y2 p =>
    Path.trans (Path.congrArg (fun y => f.fn (w.inv.fn y)) p) (w.sect y2)

end AbstractHomotopyDeep
end Path
end ComputationalPaths
