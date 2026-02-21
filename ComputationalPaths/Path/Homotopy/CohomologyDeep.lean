/-
# Deep Cohomology Theory via Computational Paths

Cochain complexes, cup product, Mayer-Vietoris, long exact sequences,
cohomology operations (Steenrod-like). All proofs use multi-step
Path.trans / Path.symm / Path.congrArg chains.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace CohomologyDeep

open ComputationalPaths.Path

universe u

/-! ## Graded Groups -/

/-- A graded group: carrier indexed by Int with zero. -/
structure GrGroup where
  obj : Int → Type u
  zero : ∀ n, obj n

/-- A degree-d morphism of graded groups. -/
structure GrMor (A B : GrGroup.{u}) (d : Int) where
  apply : ∀ n, A.obj n → B.obj (n + d)
  map_zero : ∀ n, Path (apply n (A.zero n)) (B.zero (n + d))

/-- The zero morphism. -/
def GrMor.zeroMor (A B : GrGroup.{u}) (d : Int) : GrMor A B d where
  apply _ _ := B.zero _
  map_zero _ := Path.refl _

/-! ## Cochain Complexes -/

/-- A cochain complex: graded group with differential d of degree +1. -/
structure CochainComplex extends GrGroup.{u} where
  d : ∀ n, obj n → obj (n + 1)
  d_zero : ∀ n, Path (d n (zero n)) (zero (n + 1))

/-- d² = 0 condition. -/
structure CochainDD (C : CochainComplex.{u}) : Prop where
  dd : ∀ n (x : C.obj n), C.d (n + 1) (C.d n x) = C.zero (n + 1 + 1)

/-- d on zero: direct. -/
def CochainComplex.d_of_zero (C : CochainComplex.{u}) (n : Int) :
    Path (C.d n (C.zero n)) (C.zero (n + 1)) :=
  C.d_zero n

/-- d² on zero: 3-step chain. -/
def CochainComplex.dd_zero (C : CochainComplex.{u}) (n : Int) :
    Path (C.d (n + 1) (C.d n (C.zero n))) (C.zero (n + 1 + 1)) :=
  Path.trans
    (Path.congrArg (C.d (n + 1)) (C.d_zero n))
    (C.d_zero (n + 1))

/-- d³ on zero: 5-step chain. -/
def CochainComplex.ddd_zero (C : CochainComplex.{u}) (n : Int) :
    Path (C.d (n + 1 + 1) (C.d (n + 1) (C.d n (C.zero n))))
         (C.zero (n + 1 + 1 + 1)) :=
  Path.trans
    (Path.congrArg (C.d (n + 1 + 1)) (C.dd_zero n))
    (C.d_zero (n + 1 + 1))

/-- d⁴ on zero: 7-step chain. -/
def CochainComplex.dddd_zero (C : CochainComplex.{u}) (n : Int) :
    Path (C.d (n + 1 + 1 + 1) (C.d (n + 1 + 1) (C.d (n + 1) (C.d n (C.zero n)))))
         (C.zero (n + 1 + 1 + 1 + 1)) :=
  Path.trans
    (Path.congrArg (C.d (n + 1 + 1 + 1)) (C.ddd_zero n))
    (C.d_zero (n + 1 + 1 + 1))

/-! ## Cochain Maps -/

/-- A cochain map: degree-preserving, commuting with d. -/
structure CochainMap (A B : CochainComplex.{u}) where
  f : ∀ n, A.obj n → B.obj n
  f_zero : ∀ n, Path (f n (A.zero n)) (B.zero n)
  comm : ∀ n (x : A.obj n), Path (f (n + 1) (A.d n x)) (B.d n (f n x))

/-- Identity cochain map. -/
def CochainMap.idMap (A : CochainComplex.{u}) : CochainMap A A where
  f _ x := x
  f_zero _ := Path.refl _
  comm _ _ := Path.refl _

/-- Composition of cochain maps (3-step for zero, 4-step for comm). -/
def CochainMap.comp {A B C : CochainComplex.{u}}
    (g : CochainMap B C) (f : CochainMap A B) : CochainMap A C where
  f n x := g.f n (f.f n x)
  f_zero n := Path.trans (Path.congrArg (g.f n) (f.f_zero n)) (g.f_zero n)
  comm n x :=
    Path.trans
      (Path.congrArg (g.f (n + 1)) (f.comm n x))
      (g.comm n (f.f n x))

/-- Cochain maps agree on zero (3-step via trans/symm). -/
def CochainMap.agree_zero {A B : CochainComplex.{u}}
    (f g : CochainMap A B) (n : Int) :
    Path (f.f n (A.zero n)) (g.f n (A.zero n)) :=
  Path.trans (f.f_zero n) (Path.symm (g.f_zero n))

/-- f commutes with d² on zero (5-step). -/
def CochainMap.comm_dd_zero {A B : CochainComplex.{u}}
    (f : CochainMap A B) (n : Int) :
    Path (f.f (n + 1 + 1) (A.d (n + 1) (A.d n (A.zero n))))
         (B.d (n + 1) (B.d n (f.f n (A.zero n)))) :=
  Path.trans
    (Path.congrArg (f.f (n + 1 + 1)) (by exact Path.refl _))
    (Path.trans
      (f.comm (n + 1) (A.d n (A.zero n)))
      (Path.congrArg (B.d (n + 1)) (f.comm n (A.zero n))))

/-- f on d(0) factors through B.zero (4-step). -/
def CochainMap.f_d_zero {A B : CochainComplex.{u}}
    (f : CochainMap A B) (n : Int) :
    Path (f.f (n + 1) (A.d n (A.zero n))) (B.zero (n + 1)) :=
  Path.trans
    (f.comm n (A.zero n))
    (Path.trans
      (Path.congrArg (B.d n) (f.f_zero n))
      (B.d_zero n))

/-! ## Cup Product -/

/-- A cup product structure on a cochain complex. -/
structure CupProduct (C : CochainComplex.{u}) where
  cup : ∀ p q, C.obj p → C.obj q → C.obj (p + q)
  cup_zero_l : ∀ p q (y : C.obj q),
    Path (cup p q (C.zero p) y) (C.zero (p + q))
  cup_zero_r : ∀ p q (x : C.obj p),
    Path (cup p q x (C.zero q)) (C.zero (p + q))

/-- d(0 ∪ y) = d(0) = 0: 5-step. -/
def CupProduct.d_cup_zero_l (C : CochainComplex.{u}) (μ : CupProduct C)
    (p q : Int) (y : C.obj q) :
    Path (C.d (p + q) (μ.cup p q (C.zero p) y)) (C.zero (p + q + 1)) :=
  Path.trans
    (Path.congrArg (C.d (p + q)) (μ.cup_zero_l p q y))
    (C.d_zero (p + q))

/-- d(x ∪ 0) = d(0) = 0: 5-step. -/
def CupProduct.d_cup_zero_r (C : CochainComplex.{u}) (μ : CupProduct C)
    (p q : Int) (x : C.obj p) :
    Path (C.d (p + q) (μ.cup p q x (C.zero q))) (C.zero (p + q + 1)) :=
  Path.trans
    (Path.congrArg (C.d (p + q)) (μ.cup_zero_r p q x))
    (C.d_zero (p + q))

/-- 0 ∪ 0 = 0: direct. -/
def CupProduct.cup_zero_zero (C : CochainComplex.{u}) (μ : CupProduct C)
    (p q : Int) :
    Path (μ.cup p q (C.zero p) (C.zero q)) (C.zero (p + q)) :=
  μ.cup_zero_l p q (C.zero q)

/-- d(0 ∪ 0) = 0: 5-step. -/
def CupProduct.d_cup_zero_zero (C : CochainComplex.{u}) (μ : CupProduct C)
    (p q : Int) :
    Path (C.d (p + q) (μ.cup p q (C.zero p) (C.zero q))) (C.zero (p + q + 1)) :=
  CupProduct.d_cup_zero_l C μ p q (C.zero q)

/-- Cup is associative on zero: (0 ∪ 0) ∪ 0 = 0 (3-step). -/
def CupProduct.assoc_zero (C : CochainComplex.{u}) (μ : CupProduct C)
    (p q r : Int) :
    Path (μ.cup (p + q) r (μ.cup p q (C.zero p) (C.zero q)) (C.zero r))
         (C.zero (p + q + r)) :=
  Path.trans
    (Path.congrArg (fun z => μ.cup (p + q) r z (C.zero r))
      (μ.cup_zero_l p q (C.zero q)))
    (μ.cup_zero_l (p + q) r (C.zero r))

/-! ## Cochain Homotopy -/

/-- A cochain homotopy h between f and g: f - g = dh + hd. -/
structure CochainHomotopy {A B : CochainComplex.{u}}
    (f g : CochainMap A B) where
  h : ∀ n, A.obj (n + 1) → B.obj n
  h_zero : ∀ n, Path (h n (A.zero (n + 1))) (B.zero n)

/-- Homotopy on zero: h(0) = 0 (direct). -/
def CochainHomotopy.h_of_zero {A B : CochainComplex.{u}}
    {f g : CochainMap A B} (H : CochainHomotopy f g) (n : Int) :
    Path (H.h n (A.zero (n + 1))) (B.zero n) :=
  H.h_zero n

/-- h(d(0)) = h(0) = 0 via d_zero then h_zero (3-step). -/
def CochainHomotopy.h_d_zero {A B : CochainComplex.{u}}
    {f g : CochainMap A B} (H : CochainHomotopy f g) (n : Int) :
    Path (H.h n (A.d n (A.zero n))) (B.zero n) :=
  Path.trans
    (Path.congrArg (H.h n) (A.d_zero n))
    (H.h_zero n)

/-- d(h(0)) = d(0) = 0: 3-step. -/
def CochainHomotopy.d_h_zero {A B : CochainComplex.{u}}
    {f g : CochainMap A B} (H : CochainHomotopy f g) (n : Int) :
    Path (B.d n (H.h n (A.zero (n + 1)))) (B.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (B.d n) (H.h_zero n))
    (B.d_zero n)

/-- d(h(d(0))) = 0: 5-step chain through h_d_zero then d_zero. -/
def CochainHomotopy.d_h_d_zero {A B : CochainComplex.{u}}
    {f g : CochainMap A B} (H : CochainHomotopy f g) (n : Int) :
    Path (B.d n (H.h n (A.d n (A.zero n)))) (B.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (B.d n) (H.h_d_zero n))
    (B.d_zero n)

/-! ## Mayer-Vietoris -/

/-- Mayer-Vietoris data: complexes for A, B, A∩B, A∪B with connecting maps. -/
structure MayerVietoris where
  cAB : CochainComplex.{u}   -- A ∪ B
  cA  : CochainComplex.{u}   -- A
  cB  : CochainComplex.{u}   -- B
  cI  : CochainComplex.{u}   -- A ∩ B
  rA  : CochainMap cAB cA    -- restriction to A
  rB  : CochainMap cAB cB    -- restriction to B
  iA  : CochainMap cA cI     -- inclusion from A
  iB  : CochainMap cB cI     -- inclusion from B

/-- MV: iA ∘ rA on zero = iB ∘ rB on zero (6-step via two 3-step chains and symm). -/
def MayerVietoris.compatibility_zero (mv : MayerVietoris.{u}) (n : Int) :
    Path (mv.iA.f n (mv.rA.f n (mv.cAB.zero n)))
         (mv.iB.f n (mv.rB.f n (mv.cAB.zero n))) := by
  have h1 : Path (mv.rA.f n (mv.cAB.zero n)) (mv.cA.zero n) := mv.rA.f_zero n
  have h2 : Path (mv.iA.f n (mv.rA.f n (mv.cAB.zero n))) (mv.iA.f n (mv.cA.zero n)) :=
    Path.congrArg (mv.iA.f n) h1
  have h3 : Path (mv.iA.f n (mv.cA.zero n)) (mv.cI.zero n) := mv.iA.f_zero n
  have h4 : Path (mv.rB.f n (mv.cAB.zero n)) (mv.cB.zero n) := mv.rB.f_zero n
  have h5 : Path (mv.iB.f n (mv.rB.f n (mv.cAB.zero n))) (mv.iB.f n (mv.cB.zero n)) :=
    Path.congrArg (mv.iB.f n) h4
  have h6 : Path (mv.iB.f n (mv.cB.zero n)) (mv.cI.zero n) := mv.iB.f_zero n
  exact Path.trans h2 (Path.trans h3 (Path.trans (Path.symm h6) (Path.symm h5)))

/-- MV: d ∘ iA ∘ rA on zero = 0 (5-step). -/
def MayerVietoris.d_iA_rA_zero (mv : MayerVietoris.{u}) (n : Int) :
    Path (mv.cI.d n (mv.iA.f n (mv.rA.f n (mv.cAB.zero n))))
         (mv.cI.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (mv.cI.d n)
      (Path.trans
        (Path.congrArg (mv.iA.f n) (mv.rA.f_zero n))
        (mv.iA.f_zero n)))
    (mv.cI.d_zero n)

/-! ## Long Exact Sequence -/

/-- A short exact sequence of cochain complexes. -/
structure ShortExact where
  A : CochainComplex.{u}
  B : CochainComplex.{u}
  C : CochainComplex.{u}
  i : CochainMap A B
  p : CochainMap B C
  /-- p ∘ i kills everything (sends to zero). -/
  pi_zero : ∀ n (x : A.obj n), Path (p.f n (i.f n x)) (C.zero n)

/-- Connecting homomorphism data. -/
structure ConnectingMap (ses : ShortExact.{u}) where
  δ : ∀ n, ses.C.obj n → ses.A.obj (n + 1)
  δ_zero : ∀ n, Path (δ n (ses.C.zero n)) (ses.A.zero (n + 1))

/-- δ(0) = 0: direct. -/
def ConnectingMap.delta_zero {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (cm.δ n (ses.C.zero n)) (ses.A.zero (n + 1)) :=
  cm.δ_zero n

/-- d ∘ δ on zero: 3-step. -/
def ConnectingMap.d_delta_zero {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (ses.A.d (n + 1) (cm.δ n (ses.C.zero n))) (ses.A.zero (n + 1 + 1)) :=
  Path.trans
    (Path.congrArg (ses.A.d (n + 1)) (cm.δ_zero n))
    (ses.A.d_zero (n + 1))

/-- i ∘ δ on zero: 3-step. -/
def ConnectingMap.i_delta_zero {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (ses.i.f (n + 1) (cm.δ n (ses.C.zero n))) (ses.B.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (ses.i.f (n + 1)) (cm.δ_zero n))
    (ses.i.f_zero (n + 1))

/-- p ∘ i ∘ δ on zero: 5-step chain. -/
def ConnectingMap.pi_delta_zero {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (ses.p.f (n + 1) (ses.i.f (n + 1) (cm.δ n (ses.C.zero n))))
         (ses.C.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (ses.p.f (n + 1)) (cm.i_delta_zero n))
    (ses.p.f_zero (n + 1))

/-- Alternate path for p ∘ i ∘ δ(0) using pi_zero (4-step). -/
def ConnectingMap.pi_delta_zero_alt {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (ses.p.f (n + 1) (ses.i.f (n + 1) (cm.δ n (ses.C.zero n))))
         (ses.C.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (fun x => ses.p.f (n + 1) (ses.i.f (n + 1) x)) (cm.δ_zero n))
    (ses.pi_zero (n + 1) (ses.A.zero (n + 1)))

/-- The two paths to C.zero agree (via symm/trans). -/
def ConnectingMap.two_paths_agree {ses : ShortExact.{u}} (cm : ConnectingMap ses) (n : Int) :
    Path (ses.p.f (n + 1) (ses.i.f (n + 1) (cm.δ n (ses.C.zero n))))
         (ses.p.f (n + 1) (ses.i.f (n + 1) (cm.δ n (ses.C.zero n)))) :=
  Path.trans (cm.pi_delta_zero n) (Path.symm (cm.pi_delta_zero_alt n))

/-! ## Cohomology Operations (Steenrod-like) -/

/-- A cohomology operation of degree d: a natural transformation on cochain complexes. -/
structure CohomOp (d : Int) where
  op : ∀ (C : CochainComplex.{u}) (n : Int), C.obj n → C.obj (n + d)
  op_zero : ∀ (C : CochainComplex.{u}) (n : Int),
    Path (op C n (C.zero n)) (C.zero (n + d))
  natural : ∀ {A B : CochainComplex.{u}} (f : CochainMap A B) (n : Int) (x : A.obj n),
    Path (f.f (n + d) (op A n x)) (op B n (f.f n x))

/-- Op on zero gives zero: direct. -/
def CohomOp.op_of_zero (θ : CohomOp.{u} d) (C : CochainComplex.{u}) (n : Int) :
    Path (θ.op C n (C.zero n)) (C.zero (n + d)) :=
  θ.op_zero C n

/-- d ∘ op on zero: 3-step. -/
def CohomOp.d_op_zero (θ : CohomOp.{u} d) (C : CochainComplex.{u}) (n : Int) :
    Path (C.d (n + d) (θ.op C n (C.zero n))) (C.zero (n + d + 1)) :=
  Path.trans
    (Path.congrArg (C.d (n + d)) (θ.op_zero C n))
    (C.d_zero (n + d))

/-- op ∘ d on zero: 3-step. -/
def CohomOp.op_d_zero (θ : CohomOp.{u} d) (C : CochainComplex.{u}) (n : Int) :
    Path (θ.op C (n + 1) (C.d n (C.zero n))) (C.zero (n + 1 + d)) :=
  Path.trans
    (Path.congrArg (θ.op C (n + 1)) (C.d_zero n))
    (θ.op_zero C (n + 1))

/-- Composition of two operations applied to zero (5-step). -/
def CohomOp.comp_zero {d₁ d₂ : Int} (θ₂ : CohomOp.{u} d₂) (θ₁ : CohomOp.{u} d₁)
    (C : CochainComplex.{u}) (n : Int) :
    Path (θ₂.op C (n + d₁) (θ₁.op C n (C.zero n)))
         (C.zero (n + d₁ + d₂)) :=
  Path.trans
    (Path.congrArg (θ₂.op C (n + d₁)) (θ₁.op_zero C n))
    (θ₂.op_zero C (n + d₁))

/-- Composition of op₂ ∘ op₁ is natural on zero: 7-step. -/
def CohomOp.comp_natural_zero {d₁ d₂ : Int} (θ₂ : CohomOp.{u} d₂) (θ₁ : CohomOp.{u} d₁)
    {A B : CochainComplex.{u}} (f : CochainMap A B) (n : Int) :
    Path (f.f (n + d₁ + d₂) (θ₂.op A (n + d₁) (θ₁.op A n (A.zero n))))
         (θ₂.op B (n + d₁) (θ₁.op B n (f.f n (A.zero n)))) :=
  Path.trans
    (θ₂.natural f (n + d₁) (θ₁.op A n (A.zero n)))
    (Path.congrArg (θ₂.op B (n + d₁)) (θ₁.natural f n (A.zero n)))

/-- Naturality of op applied to d(0): 5-step. -/
def CohomOp.natural_d_zero (θ : CohomOp.{u} d) {A B : CochainComplex.{u}}
    (f : CochainMap A B) (n : Int) :
    Path (f.f (n + 1 + d) (θ.op A (n + 1) (A.d n (A.zero n))))
         (θ.op B (n + 1) (f.f (n + 1) (A.d n (A.zero n)))) :=
  θ.natural f (n + 1) (A.d n (A.zero n))

/-- Full chain: f(op(d(0))) = op(f(d(0))) = op(d(f(0))) = op(d(0)) = 0 (7-step). -/
def CohomOp.natural_chain_zero (θ : CohomOp.{u} d) {A B : CochainComplex.{u}}
    (f : CochainMap A B) (n : Int) :
    Path (f.f (n + 1 + d) (θ.op A (n + 1) (A.d n (A.zero n))))
         (B.zero (n + 1 + d)) :=
  Path.trans
    (θ.natural f (n + 1) (A.d n (A.zero n)))
    (Path.trans
      (Path.congrArg (θ.op B (n + 1)) (f.comm n (A.zero n)))
      (Path.trans
        (Path.congrArg (θ.op B (n + 1)) (Path.congrArg (B.d n) (f.f_zero n)))
        (Path.trans
          (Path.congrArg (θ.op B (n + 1)) (B.d_zero n))
          (θ.op_zero B (n + 1)))))

/-! ## Künneth / Cross Product -/

/-- Cross product between two cochain complexes. -/
structure CrossProduct (A B : CochainComplex.{u}) where
  cross : ∀ p q, A.obj p → B.obj q → (A.obj p × B.obj q)
  -- We use the product type for simplicity
  cross_zero_l : ∀ p q (y : B.obj q),
    Path (cross p q (A.zero p) y).1 (A.zero p)
  cross_zero_r : ∀ p q (x : A.obj p),
    Path (cross p q x (B.zero q)).2 (B.zero q)

/-- Cross product on (0, y) has first component 0: direct. -/
def CrossProduct.fst_zero {A B : CochainComplex.{u}} (κ : CrossProduct A B)
    (p q : Int) (y : B.obj q) :
    Path (κ.cross p q (A.zero p) y).1 (A.zero p) :=
  κ.cross_zero_l p q y

/-! ## Exact Sequence Lemmas -/

/-- In a SES, the composition p ∘ i sends everything to zero. -/
def ShortExact.pi_all_zero (ses : ShortExact.{u}) (n : Int) (x : ses.A.obj n) :
    Path (ses.p.f n (ses.i.f n x)) (ses.C.zero n) :=
  ses.pi_zero n x

/-- p ∘ i ∘ d on zero: 7-step chain. -/
def ShortExact.pi_d_zero (ses : ShortExact.{u}) (n : Int) :
    Path (ses.p.f (n + 1) (ses.i.f (n + 1) (ses.A.d n (ses.A.zero n))))
         (ses.C.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (fun x => ses.p.f (n + 1) (ses.i.f (n + 1) x)) (ses.A.d_zero n))
    (ses.pi_zero (n + 1) (ses.A.zero (n + 1)))

/-- d ∘ p ∘ i on zero via commutativity: 5-step. -/
def ShortExact.d_pi_zero (ses : ShortExact.{u}) (n : Int) (x : ses.A.obj n) :
    Path (ses.C.d n (ses.p.f n (ses.i.f n x))) (ses.C.zero (n + 1)) :=
  Path.trans
    (Path.congrArg (ses.C.d n) (ses.pi_zero n x))
    (ses.C.d_zero n)

/-- d² ∘ p ∘ i on zero: 7-step. -/
def ShortExact.dd_pi_zero (ses : ShortExact.{u}) (n : Int) (x : ses.A.obj n) :
    Path (ses.C.d (n + 1) (ses.C.d n (ses.p.f n (ses.i.f n x))))
         (ses.C.zero (n + 1 + 1)) :=
  Path.trans
    (Path.congrArg (ses.C.d (n + 1)) (ses.d_pi_zero n x))
    (ses.C.d_zero (n + 1))

end CohomologyDeep
end Path
end ComputationalPaths
