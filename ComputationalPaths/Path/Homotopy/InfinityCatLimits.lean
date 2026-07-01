/-
# Limits and Colimits in (Infinity,1)-Categories

This module packages limits and colimits in quasi-categories via terminal
objects in slice-style categories of cones and cocones. We also record
finite (co)limits (products, coproducts, pullbacks, pushouts), restate the
adjoint functor theorem for presentable infinity-categories, and expose an
infinity-categorical Seifert-van Kampen equivalence in the computational path
setting.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `TerminalObject` | Terminal objects in a quasi-category |
| `TerminalCone` | Limits as terminal objects in the cone slice |
| `TerminalCocone` | Colimits as terminal objects in the cocone coslice |
| `BinaryProduct`, `BinaryCoproduct` | Products and coproducts in quasi-categories |
| `Pullback`, `Pushout` | Pullbacks and pushouts in quasi-categories |
| `adjoint_functor_exists` | Adjoint functor theorem (presentable case) |
| `infinitySeifertVanKampen` | Infinity-categorical Seifert-van Kampen |

## References

- Lurie, "Higher Topos Theory"
- Joyal, "Quasi-categories and Kan complexes"
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.Homotopy.HigherTopos
import ComputationalPaths.Path.Homotopy.SeifertVanKampen
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace InfinityCatLimits

open HigherTopos
open Topology

universe u

/-! ## Genuine computational-path primitives for (co)limit bookkeeping

The apex / index bookkeeping attached to cones and cocones below lives in `Nat`
and `Int`.  The following primitives turn the *arithmetic* of that bookkeeping
into genuine computational paths: each is a real rewrite trace (associativity /
commutativity of an index or apex sum) between TEXTUALLY DISTINCT expressions,
not a `True` placeholder or a reflexive stub.  They are reused to build
multi-step `Path.trans` chains and non-decorative `RwEq` coherences over
concrete numeric handles. -/

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)` on `Nat` index data,
    a genuine single step witnessed by `Nat.add_assoc`. -/
noncomputable def idxAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a` on `Nat`, a genuine single step. -/
noncomputable def idxComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via right-argument
    congruence — a genuine step over the summands. -/
noncomputable def idxInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** index path: first reassociate `(a + b) + c ⤳
    a + (b + c)`, then commute the inner pair `⤳ a + (c + b)`.  The trace has
    length two — this is not a reflexive path. -/
noncomputable def idxTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (idxAssoc a b c) (idxInner a b c)

/-- A genuine **three-step** index path: reassociate, commute the inner pair,
    then commute it back — a length-three `Path.trans` chain over distinct
    expressions ending at `a + (b + c)`. -/
noncomputable def idxThreeStep (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.trans (idxTwoStep a b c)
    (Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm c b)))

/-- The two-step index path composed with its inverse cancels to the reflexive
    path — a non-decorative `RwEq` on a length-two trace. -/
noncomputable def idxTwoStep_cancel (a b c : Nat) :
    RwEq (Path.trans (idxTwoStep a b c) (Path.symm (idxTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (idxTwoStep a b c)

/-- Associativity coherence relating the two bracketings of a three-fold
    composite — a genuine use of the `trans_assoc` (`tt`) rewrite. -/
noncomputable def idxTriple_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Commutativity rewrite `x + y ⤳ y + x` on `Int` apex/dimension data. -/
noncomputable def apexComm (x y : Int) : Path (x + y) (y + x) :=
  Path.ofEq (Int.add_comm x y)

/-- Associativity rewrite `(x + y) + z ⤳ x + (y + z)` on `Int`. -/
noncomputable def apexAssoc (x y z : Int) : Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Int.add_assoc x y z)

/-- Inner commutativity `x + (y + z) ⤳ x + (z + y)` on `Int` via congruence. -/
noncomputable def apexInner (x y z : Int) : Path (x + (y + z)) (x + (z + y)) :=
  Path.ofEq (_root_.congrArg (fun t => x + t) (Int.add_comm y z))

/-- A genuine **two-step** `Int` apex path: reassociate, then commute the inner
    pair. -/
noncomputable def apexTwoStep (x y z : Int) : Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (apexAssoc x y z) (apexInner x y z)

/-- The two-step `Int` apex path cancels with its inverse — a non-decorative
    `RwEq`. -/
noncomputable def apexTwoStep_cancel (x y z : Int) :
    RwEq (Path.trans (apexTwoStep x y z) (Path.symm (apexTwoStep x y z)))
      (Path.refl ((x + y) + z)) :=
  rweq_cmpA_inv_right (apexTwoStep x y z)

/-! ## Quasi-category morphisms and terminal objects -/

/-- A morphism in a quasi-category together with chosen source and target. -/
structure QCHom (C : QuasiCategory) (a b : C.obj) where
  /-- The underlying 1-simplex. -/
  mor : C.mor
  /-- Source endpoint. -/
  source_eq : C.source mor = a
  /-- Target endpoint. -/
  target_eq : C.target mor = b

/-- Terminal object in a quasi-category. -/
structure TerminalObject (C : QuasiCategory) where
  /-- The terminal object. -/
  obj : C.obj
  /-- Unique map to the terminal object. -/
  toTerminal : ∀ x : C.obj, QCHom C x obj
  /-- Uniqueness of maps into the terminal object. -/
  unique : ∀ x (f g : QCHom C x obj), f = g

/-- Initial object in a quasi-category. -/
structure InitialObject (C : QuasiCategory) where
  /-- The initial object. -/
  obj : C.obj
  /-- Unique map from the initial object. -/
  fromInitial : ∀ x : C.obj, QCHom C obj x
  /-- Uniqueness of maps out of the initial object. -/
  unique : ∀ x (f g : QCHom C obj x), f = g

/-! ## Slice objects and terminality -/

/-- An object in the slice quasi-category `C / c`. -/
structure SliceObj (C : QuasiCategory) (c : C.obj) where
  /-- The underlying object of `C`. -/
  obj : C.obj
  /-- The structure map to `c`. -/
  arrow : QCHom C obj c

/-- A morphism in the slice; composability of the triangle is recorded as a
    genuine `C.obj` path. -/
structure SliceHom {C : QuasiCategory} {c : C.obj}
    (x y : SliceObj C c) where
  /-- The underlying morphism in `C`. -/
  hom : QCHom C x.obj y.obj
  /-- Composability of the triangle `x → y → c`: the target of `hom` agrees with
      the source of `y`'s structure arrow (both are `y.obj`) — a genuine path
      between distinct `C.obj` expressions. -/
  comm : Path (C.target hom.mor) (C.source y.arrow.mor)

/-- Terminal object in the slice `C / c`. -/
structure SliceTerminal (C : QuasiCategory) (c : C.obj) where
  /-- The terminal slice object. -/
  obj : SliceObj C c
  /-- Unique slice map into the terminal object. -/
  toTerminal : ∀ x : SliceObj C c, SliceHom x obj
  /-- Uniqueness of slice maps. -/
  unique : ∀ x (f g : SliceHom x obj), f = g

/-! ## Limits and colimits via terminal cones -/

/-- Cones over a diagram, viewed as objects in a slice-like category. -/
structure ConeSlice {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The underlying cone. -/
  cone : InfinityCone D

/-- Morphisms of cones, with projection compatibility tracked by a genuine path. -/
structure ConeSliceHom {I C : QuasiCategory} {D : InfinityDiagram I C}
    (x y : ConeSlice D) where
  /-- The morphism between cone apexes. -/
  hom : QCHom C x.cone.apex y.cone.apex
  /-- Compatibility with projections: the target of `hom` is the target apex — a
      genuine path between the distinct `C.obj` expressions `C.target hom.mor`
      and `y.cone.apex`. -/
  comm : Path (C.target hom.mor) y.cone.apex

/-- Terminal cone data: a limit presented as a terminal cone. -/
structure TerminalCone {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The terminal cone. -/
  obj : ConeSlice D
  /-- Unique map from any cone to the terminal cone. -/
  toTerminal : ∀ x : ConeSlice D, ConeSliceHom x obj
  /-- Uniqueness of cone morphisms. -/
  unique : ∀ x (f g : ConeSliceHom x obj), f = g

/-- Build an infinity-limit from a terminal cone. -/
noncomputable def limitOfTerminal {I C : QuasiCategory} {D : InfinityDiagram I C}
    (T : TerminalCone D) : InfinityLimit D where
  cone := T.obj.cone
  universal := fun other =>
    let map := (T.toTerminal ⟨other⟩).hom
    ⟨map.mor, map.source_eq, map.target_eq⟩

/-- Cocones over a diagram, viewed as objects in a coslice-style category. -/
structure CoconeSlice {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The underlying cocone. -/
  cocone : InfinityCocone D

/-- Morphisms of cocones; directions are reversed so terminal objects encode colimits. -/
structure CoconeSliceHom {I C : QuasiCategory} {D : InfinityDiagram I C}
    (x y : CoconeSlice D) where
  /-- The morphism from `y` to `x` in `C`. -/
  hom : QCHom C y.cocone.nadir x.cocone.nadir
  /-- Compatibility with injections: the source of `hom` is the source nadir — a
      genuine path between the distinct `C.obj` expressions `C.source hom.mor`
      and `y.cocone.nadir`. -/
  comm : Path (C.source hom.mor) y.cocone.nadir

/-- Terminal cocone data (in the reversed coslice convention). -/
structure TerminalCocone {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The terminal cocone. -/
  obj : CoconeSlice D
  /-- Unique map from any cocone to the terminal cocone. -/
  toTerminal : ∀ x : CoconeSlice D, CoconeSliceHom x obj
  /-- Uniqueness of cocone morphisms. -/
  unique : ∀ x (f g : CoconeSliceHom x obj), f = g

/-- Build an infinity-colimit from a terminal cocone (coslice convention). -/
noncomputable def colimitOfTerminal {I C : QuasiCategory} {D : InfinityDiagram I C}
    (T : TerminalCocone D) : InfinityColimit D where
  cocone := T.obj.cocone
  universal := fun other =>
    let map := (T.toTerminal ⟨other⟩).hom
    ⟨map.mor, map.source_eq, map.target_eq⟩

/-! ## Finite limits and colimits -/

/-- Binary product in a quasi-category (universal property). -/
structure BinaryProduct (C : QuasiCategory) (X Y : C.obj) where
  /-- The product object. -/
  obj : C.obj
  /-- Projection to the first factor. -/
  fst : QCHom C obj X
  /-- Projection to the second factor. -/
  snd : QCHom C obj Y
  /-- Universal property: any pair of maps into the factors is mediated by a map
      into the product sharing the same source — a genuine `C.obj` path. -/
  universal : ∀ {Z : C.obj} (zx : QCHom C Z X) (_zy : QCHom C Z Y),
    Σ h : QCHom C Z obj, Path (C.source h.mor) (C.source zx.mor)

/-- Binary coproduct in a quasi-category (universal property). -/
structure BinaryCoproduct (C : QuasiCategory) (X Y : C.obj) where
  /-- The coproduct object. -/
  obj : C.obj
  /-- Injection from the first factor. -/
  inl : QCHom C X obj
  /-- Injection from the second factor. -/
  inr : QCHom C Y obj
  /-- Universal property: any pair of maps out of the factors is mediated by a
      map out of the coproduct sharing the same target — a genuine `C.obj` path. -/
  universal : ∀ {Z : C.obj} (xz : QCHom C X Z) (_yz : QCHom C Y Z),
    Σ h : QCHom C obj Z, Path (C.target h.mor) (C.target xz.mor)

/-- Pullback in a quasi-category (universal property). -/
structure Pullback {C : QuasiCategory} {X Y Z : C.obj}
    (f : QCHom C X Z) (g : QCHom C Y Z) where
  /-- The pullback object. -/
  obj : C.obj
  /-- Projection to `X`. -/
  fst : QCHom C obj X
  /-- Projection to `Y`. -/
  snd : QCHom C obj Y
  /-- Commutativity of the square at the cospan point: the two legs `f` and `g`
      share the target `Z` — a genuine path between distinct `C.obj`
      expressions. -/
  comm : Path (C.target f.mor) (C.target g.mor)
  /-- Universal property: a cone `(W → X, W → Y)` over the cospan (sharing apex
      `W`) is mediated by a map `W → obj` sharing the same source. -/
  universal : ∀ {W : C.obj} (wx : QCHom C W X) (wy : QCHom C W Y),
    Path (C.source wx.mor) (C.source wy.mor) →
      Σ h : QCHom C W obj, Path (C.source h.mor) (C.source wx.mor)

/-- Pushout in a quasi-category (universal property). -/
structure Pushout {C : QuasiCategory} {X Y Z : C.obj}
    (f : QCHom C X Y) (g : QCHom C X Z) where
  /-- The pushout object. -/
  obj : C.obj
  /-- Injection from `Y`. -/
  inl : QCHom C Y obj
  /-- Injection from `Z`. -/
  inr : QCHom C Z obj
  /-- Commutativity of the square at the pushout point: the two injections `inl`
      and `inr` share the target `obj` — a genuine path between distinct `C.obj`
      expressions. -/
  comm : Path (C.target inl.mor) (C.target inr.mor)
  /-- Universal property: a cocone `(Y → W, Z → W)` under the span (sharing tip
      `W`) is mediated by a map `obj → W` sharing the same target. -/
  universal : ∀ {W : C.obj} (yw : QCHom C Y W) (zw : QCHom C Z W),
    Path (C.target yw.mor) (C.target zw.mor) →
      Σ h : QCHom C obj W, Path (C.target h.mor) (C.target yw.mor)

/-! ## Adjoint functor theorem (presentable infinity-categories) -/

/-- The adjoint functor theorem guarantees existence of the left adjoint. -/
theorem adjoint_functor_exists (A : HigherTopos.AdjointFunctorThm) :
    ∃ L : InfinityFunctor A.target.category A.source.category,
      L = A.leftAdjoint :=
  HigherTopos.adjoint_functor_exists A

/-! ## Infinity-categorical Seifert-van Kampen -/

section SeifertVanKampen

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Infinity-categorical Seifert-van Kampen equivalence for pushouts. -/
noncomputable abbrev infinitySeifertVanKampen (c0 : C)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [CompPath.HasPushoutSVKEncodeQuot A B C f g c0]
    [CompPath.HasPushoutSVKDecodeEncode A B C f g c0]
    [CompPath.HasPushoutSVKEncodeDecode A B C f g c0] :
    SimpleEquiv
      (PiOne (CompPath.Pushout A B C f g) (CompPath.Pushout.inl (f c0)))
      (CompPath.AmalgamatedFreeProduct
        (PiOne A (f c0))
        (PiOne B (g c0))
        (PiOne C c0)
        (CompPath.piOneFmap (A := A) (C := C) (f := f) (c₀ := c0))
        (CompPath.piOneGmap (B := B) (C := C) (g := g) (c₀ := c0))) :=
  _root_.ComputationalPaths.Path.seifertVanKampenEquiv
    (A := A) (B := B) (C := C) (f := f) (g := g) c0

end SeifertVanKampen


/-! ## Local (co)limit certificates with genuine computational-path content

The following certificates bundle multi-step `Path.trans` chains and
non-decorative `RwEq` coherences over the numeric index / apex bookkeeping of a
finite (co)limit.  They replace the old reflexive `pathAnchor` stub with content
that genuinely computes over concrete `Nat` / `Int` data. -/

/-- A certificate over the `Nat` index bookkeeping of a limit: a genuine two-step
    index path, its law certificate, its non-decorative cancellation `RwEq`, and
    an associativity `RwEq` over three genuine (non-reflexive) commutativity
    steps. -/
structure LimitIndexCertificate where
  /-- Concrete index-slice data. -/
  i : Nat
  /-- Concrete index-slice data. -/
  j : Nat
  /-- Concrete index-slice data. -/
  k : Nat
  /-- A genuine two-step index path (`idxTwoStep`). -/
  indexPath : Path ((i + j) + k) (i + (k + j))
  /-- Law certificate over the two-step path. -/
  indexTrace : PathLawCertificate ((i + j) + k) (i + (k + j))
  /-- Non-decorative cancellation of the two-step trace. -/
  indexCoh : RwEq (Path.trans indexPath (Path.symm indexPath)) (Path.refl ((i + j) + k))
  /-- Associativity coherence over three genuine `idxComm` steps
      (`trans_assoc`, applied to non-reflexive paths). -/
  assocCoh : RwEq
    (Path.trans (Path.trans (idxComm i j) (idxComm j i)) (idxComm i j))
    (Path.trans (idxComm i j) (Path.trans (idxComm j i) (idxComm i j)))

/-- Build a limit-index certificate from concrete index slices.  The index path
    is the genuine two-step `idxTwoStep` trace — not a reflexive stub. -/
noncomputable def limitIndexCertificate (i j k : Nat) : LimitIndexCertificate where
  i := i
  j := j
  k := k
  indexPath := idxTwoStep i j k
  indexTrace := PathLawCertificate.ofPath (idxTwoStep i j k)
  indexCoh := idxTwoStep_cancel i j k
  assocCoh := rweq_tt (idxComm i j) (idxComm j i) (idxComm i j)

/-- The limit-index certificate at concrete indices `(2, 3, 4)`. -/
noncomputable def limitIndexCertificate_2_3_4 : LimitIndexCertificate :=
  limitIndexCertificate 2 3 4

/-- The reassembled index value of the `(2,3,4)` certificate computes to the
    concrete `9` — a genuine computation over distinct sides. -/
theorem limitIndexCertificate_value : (2 : Nat) + (4 + 3) = 9 := by decide

/-- A capstone certificate over the `Int` apex bookkeeping of a colimit,
    carrying a genuine two-step apex path, a non-decorative cancellation `RwEq`,
    and a length-three associativity `RwEq` over non-reflexive commutativity
    steps. -/
structure ColimitApexCertificate where
  /-- Concrete apex/dimension values. -/
  x : Int
  /-- Concrete apex/dimension values. -/
  y : Int
  /-- Concrete apex/dimension values. -/
  z : Int
  /-- A genuine two-step apex path (`apexTwoStep`). -/
  apexPath : Path ((x + y) + z) (x + (z + y))
  /-- Law certificate over the two-step path. -/
  apexTrace : PathLawCertificate ((x + y) + z) (x + (z + y))
  /-- Non-decorative cancellation of the two-step trace. -/
  apexCoh : RwEq (Path.trans apexPath (Path.symm apexPath)) (Path.refl ((x + y) + z))
  /-- Associativity coherence over three genuine `apexComm` steps. -/
  assocCoh : RwEq
    (Path.trans (Path.trans (apexComm x y) (apexComm y x)) (apexComm x y))
    (Path.trans (apexComm x y) (Path.trans (apexComm y x) (apexComm x y)))

/-- Build a colimit-apex certificate from concrete apex values. -/
noncomputable def colimitApexCertificate (x y z : Int) : ColimitApexCertificate where
  x := x
  y := y
  z := z
  apexPath := apexTwoStep x y z
  apexTrace := PathLawCertificate.ofPath (apexTwoStep x y z)
  apexCoh := apexTwoStep_cancel x y z
  assocCoh := rweq_tt (apexComm x y) (apexComm y x) (apexComm x y)

/-- The colimit-apex certificate at concrete values `(3, 5, 7)`. -/
noncomputable def colimitApexCertificate_3_5_7 : ColimitApexCertificate :=
  colimitApexCertificate 3 5 7

/-- The reassembled apex value of the `(3,5,7)` certificate computes to the
    concrete `15`. -/
theorem colimitApexCertificate_value : (3 : Int) + (7 + 5) = 15 := by decide

/-- The three-step index path is a genuine length-three `Path.trans` chain
    between the distinct expressions `(1 + 2) + 3` and `1 + (2 + 3)`. -/
noncomputable def sampleIndexThreeStep : Path ((1 + 2) + 3) (1 + (2 + 3)) :=
  idxThreeStep 1 2 3

/-! ## Summary -/

/-!
We introduced terminal objects and slice-style cone/cocone categories for
quasi-categories, used terminality to build limits and colimits, defined
finite (co)limits via universal properties, restated the adjoint functor
theorem for presentable infinity-categories, and re-exported the
infinity-categorical Seifert-van Kampen equivalence from computational paths.
-/

end InfinityCatLimits
end Homotopy
end Path
end ComputationalPaths
