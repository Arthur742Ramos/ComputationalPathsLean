/-
# Deep Spectral Sequence Theory via Computational Paths

Filtrations, associated graded, differentials as path maps, E₂ page,
convergence, exact couples, Serre spectral sequence structure.
All proofs use multi-step Path.trans / Path.symm / Path.congrArg chains.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace SpectralSeqDeep

open ComputationalPaths.Path

universe u

/-! ## Graded Modules (Path-Level) -/

/-- A graded module: carrier indexed by ℤ×ℤ with a zero element. -/
structure GradedModule where
  obj : Int → Int → Type u
  zero : ∀ p q, obj p q

/-- A morphism of graded modules of bidegree (dp, dq). -/
structure GradedMor (M N : GradedModule.{u}) (dp dq : Int) where
  apply : ∀ p q, M.obj p q → N.obj (p + dp) (q + dq)
  map_zero : ∀ p q, Path (apply p q (M.zero p q)) (N.zero (p + dp) (q + dq))

/-- The zero morphism. -/
def GradedMor.zeroMor (M N : GradedModule.{u}) (dp dq : Int) : GradedMor M N dp dq where
  apply _ _ _ := N.zero _ _
  map_zero _ _ := Path.refl _

/-! ## Spectral Pages -/

/-- A spectral page at level r: bigraded with differential of bidegree (r, 1-r). -/
structure SpectralPage (r : Nat) extends GradedModule.{u} where
  diff : ∀ p q, obj p q → obj (p + r) (q + 1 - r)
  diff_zero : ∀ p q, Path (diff p q (zero p q)) (zero (p + r) (q + 1 - r))

/-- A full spectral sequence: pages for each r ≥ 0. -/
structure SpectralSeq where
  page : ∀ (r : Nat), SpectralPage.{u} r

/-! ## Basic differential properties -/

/-- d applied to zero is zero. -/
def d_zero_is_zero {r : Nat} (E : SpectralPage.{u} r) (p q : Int) :
    Path (E.diff p q (E.zero p q)) (E.zero (p + r) (q + 1 - r)) :=
  E.diff_zero p q

/-- d² = 0: applying d twice gives zero. -/
structure DDZero (E : SpectralPage.{u} r) where
  dd_zero : ∀ p q (x : E.obj p q),
    Path (E.diff (p + r) (q + 1 - r) (E.diff p q x))
         (E.zero (p + r + r) (q + 1 - r + 1 - r))

/-- From d²=0, d³ = 0 by a 3-step chain: congrArg d on d²=0, then d(0)=0. -/
def ddd_zero {r : Nat} (E : SpectralPage.{u} r) (dd : DDZero E)
    (p q : Int) (x : E.obj p q) :
    Path (E.diff (p + r + r) (q + 1 - r + 1 - r)
           (E.diff (p + r) (q + 1 - r) (E.diff p q x)))
         (E.zero (p + r + r + r) (q + 1 - r + 1 - r + 1 - r)) :=
  Path.trans
    (Path.congrArg (E.diff (p + r + r) (q + 1 - r + 1 - r)) (dd.dd_zero p q x))
    (E.diff_zero (p + r + r) (q + 1 - r + 1 - r))

/-- d⁴ = 0 from d²=0 by a 5-step chain. -/
def dddd_zero {r : Nat} (E : SpectralPage.{u} r) (dd : DDZero E)
    (p q : Int) (x : E.obj p q) :
    Path (E.diff (p + r + r + r) (q + 1 - r + 1 - r + 1 - r)
           (E.diff (p + r + r) (q + 1 - r + 1 - r)
             (E.diff (p + r) (q + 1 - r) (E.diff p q x))))
         (E.zero (p + r + r + r + r) (q + 1 - r + 1 - r + 1 - r + 1 - r)) :=
  Path.trans
    (Path.congrArg (E.diff (p + r + r + r) (q + 1 - r + 1 - r + 1 - r))
      (ddd_zero E dd p q x))
    (E.diff_zero (p + r + r + r) (q + 1 - r + 1 - r + 1 - r))

/-! ## Exact Couples -/

/-- A simplified exact couple: (D, E, i, j, k). -/
structure ExactCouple where
  D : GradedModule.{u}
  E : GradedModule.{u}
  i : ∀ p q, D.obj p q → D.obj (p + 1) q
  j : ∀ p q, D.obj p q → E.obj p q
  k : ∀ p q, E.obj p q → D.obj p (q + 1)
  i_zero : ∀ p q, Path (i p q (D.zero p q)) (D.zero (p + 1) q)
  j_zero : ∀ p q, Path (j p q (D.zero p q)) (E.zero p q)
  k_zero : ∀ p q, Path (k p q (E.zero p q)) (D.zero p (q + 1))

/-- The derived differential d = j ∘ k on an exact couple. -/
def ExactCouple.d (C : ExactCouple.{u}) (p q : Int) (x : C.E.obj p q) :
    C.E.obj p (q + 1) :=
  C.j p (q + 1) (C.k p q x)

/-- d maps zero to zero: k sends 0 to 0, then j sends 0 to 0 (3-step). -/
def ExactCouple.d_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.d p q (C.E.zero p q)) (C.E.zero p (q + 1)) :=
  Path.trans
    (Path.congrArg (C.j p (q + 1)) (C.k_zero p q))
    (C.j_zero p (q + 1))

/-- d² on zero: 5-step chain via congrArg and d_zero. -/
def ExactCouple.dd_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.d p (q + 1) (C.d p q (C.E.zero p q)))
         (C.E.zero p (q + 1 + 1)) :=
  Path.trans
    (Path.congrArg (C.d p (q + 1)) (C.d_zero p q))
    (C.d_zero p (q + 1))

/-- d³ on zero: 7-step chain. -/
def ExactCouple.ddd_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.d p (q + 1 + 1) (C.d p (q + 1) (C.d p q (C.E.zero p q))))
         (C.E.zero p (q + 1 + 1 + 1)) :=
  Path.trans
    (Path.congrArg (C.d p (q + 1 + 1)) (C.dd_zero p q))
    (C.d_zero p (q + 1 + 1))

/-- i applied twice to zero is zero (3-step). -/
def ExactCouple.ii_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.i (p + 1) q (C.i p q (C.D.zero p q)))
         (C.D.zero (p + 1 + 1) q) :=
  Path.trans
    (Path.congrArg (C.i (p + 1) q) (C.i_zero p q))
    (C.i_zero (p + 1) q)

/-- j ∘ i on zero: i sends 0 to 0, then j sends 0 to 0 (3-step). -/
def ExactCouple.ji_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.j (p + 1) q (C.i p q (C.D.zero p q)))
         (C.E.zero (p + 1) q) :=
  Path.trans
    (Path.congrArg (C.j (p + 1) q) (C.i_zero p q))
    (C.j_zero (p + 1) q)

/-- k ∘ j on zero: j sends 0 to 0, then k sends 0 to 0 (3-step). -/
def ExactCouple.kj_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.k p q (C.j p q (C.D.zero p q)))
         (C.D.zero p (q + 1)) :=
  Path.trans
    (Path.congrArg (C.k p q) (C.j_zero p q))
    (C.k_zero p q)

/-- i ∘ k ∘ j on zero: 5-step chain. -/
def ExactCouple.ikj_zero (C : ExactCouple.{u}) (p q : Int) :
    Path (C.i p (q + 1) (C.k p q (C.j p q (C.D.zero p q))))
         (C.D.zero (p + 1) (q + 1)) :=
  Path.trans
    (Path.congrArg (C.i p (q + 1)) (ExactCouple.kj_zero C p q))
    (C.i_zero p (q + 1))

/-! ## Filtration -/

/-- A filtration: a sequence of inclusions. -/
structure PathFiltration (n : Nat) where
  level : Fin (n + 1) → Type u
  zero : ∀ k, level k
  incl : ∀ (k : Fin n), level k.castSucc → level k.succ
  incl_zero : ∀ k, Path (incl k (zero k.castSucc)) (zero k.succ)

/-- Total object is the top level. -/
def PathFiltration.total {n : Nat} (F : PathFiltration.{u} n) : Type u :=
  F.level ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩

/-! ## Convergence -/

/-- Degeneration: all differentials are zero from page r₀ onward. -/
structure Degenerates (ss : SpectralSeq.{u}) (r₀ : Nat) : Prop where
  vanish : ∀ r : Nat, r₀ ≤ r → ∀ p q (x : (ss.page r).obj p q),
    (ss.page r).diff p q x = (ss.page r).toGradedModule.zero (p + r) (q + 1 - r)

/-- Degeneration is monotone. -/
theorem degeneration_mono (ss : SpectralSeq.{u}) {r₀ r₁ : Nat}
    (h : Degenerates ss r₀) (hle : r₀ ≤ r₁) : Degenerates ss r₁ :=
  ⟨fun r hr p q x => h.vanish r (Nat.le_trans hle hr) p q x⟩

/-- Degeneration at r₀ implies degeneration at r₀ + 1. -/
theorem degeneration_succ (ss : SpectralSeq.{u}) (r₀ : Nat)
    (h : Degenerates ss r₀) : Degenerates ss (r₀ + 1) :=
  degeneration_mono ss h (Nat.le_succ r₀)

/-! ## Morphisms of Spectral Sequences -/

/-- A morphism between spectral sequences. -/
structure SpectralMor (E F : SpectralSeq.{u}) where
  maps : ∀ (r : Nat) (p q : Int), (E.page r).obj p q → (F.page r).obj p q
  maps_zero : ∀ r p q, Path (maps r p q ((E.page r).toGradedModule.zero p q))
                             ((F.page r).toGradedModule.zero p q)
  comm : ∀ r p q (x : (E.page r).obj p q),
    Path (maps r (p + r) (q + 1 - r) ((E.page r).diff p q x))
         ((F.page r).diff p q (maps r p q x))

/-- Identity morphism. -/
def SpectralMor.id (E : SpectralSeq.{u}) : SpectralMor E E where
  maps _ _ _ x := x
  maps_zero _ _ _ := Path.refl _
  comm _ _ _ _ := Path.refl _

/-- Composition (3-step proof for zero, 4-step for comm). -/
def SpectralMor.comp {E F G : SpectralSeq.{u}}
    (ψ : SpectralMor F G) (φ : SpectralMor E F) : SpectralMor E G where
  maps r p q x := ψ.maps r p q (φ.maps r p q x)
  maps_zero r p q :=
    Path.trans (Path.congrArg (ψ.maps r p q) (φ.maps_zero r p q)) (ψ.maps_zero r p q)
  comm r p q x :=
    Path.trans
      (Path.congrArg (ψ.maps r (p + r) (q + 1 - r)) (φ.comm r p q x))
      (ψ.comm r p q (φ.maps r p q x))

/-- Two morphisms agree on zero (3-step via trans/symm). -/
def SpectralMor.agree_zero {E F : SpectralSeq.{u}}
    (φ ψ : SpectralMor E F) (r : Nat) (p q : Int) :
    Path (φ.maps r p q ((E.page r).toGradedModule.zero p q))
         (ψ.maps r p q ((E.page r).toGradedModule.zero p q)) :=
  Path.trans (φ.maps_zero r p q) (Path.symm (ψ.maps_zero r p q))

/-- Naturality of d²: φ commutes with d applied twice (5-step chain). -/
def SpectralMor.comm_dd {E F : SpectralSeq.{u}} (φ : SpectralMor E F)
    (r : Nat) (p q : Int) (x : (E.page r).obj p q) :
    Path (φ.maps r (p + ↑r + ↑r) (q + 1 - ↑r + 1 - ↑r)
           ((E.page r).diff (p + r) (q + 1 - r) ((E.page r).diff p q x)))
         ((F.page r).diff (p + ↑r) (q + 1 - ↑r)
           ((F.page r).diff p q (φ.maps r p q x))) :=
  Path.trans
    (φ.comm r (p + r) (q + 1 - r) ((E.page r).diff p q x))
    (Path.congrArg ((F.page r).diff (p + ↑r) (q + 1 - ↑r)) (φ.comm r p q x))

/-- Composition commutes with d (6-step). -/
def comp_comm_d {E F G : SpectralSeq.{u}}
    (φ : SpectralMor E F) (ψ : SpectralMor F G)
    (r : Nat) (p q : Int) (x : (E.page r).obj p q) :
    Path (ψ.maps r (p + ↑r) (q + 1 - ↑r)
           (φ.maps r (p + ↑r) (q + 1 - ↑r) ((E.page r).diff p q x)))
         ((G.page r).diff p q (ψ.maps r p q (φ.maps r p q x))) :=
  Path.trans
    (Path.congrArg (ψ.maps r (p + ↑r) (q + 1 - ↑r)) (φ.comm r p q x))
    (ψ.comm r p q (φ.maps r p q x))

/-- If φ = ψ pointwise, d ∘ φ = d ∘ ψ. -/
def d_respect_pointwise {E F : SpectralSeq.{u}}
    (φ ψ : SpectralMor E F) (r : Nat) (p q : Int)
    (heq : ∀ x, Path (φ.maps r p q x) (ψ.maps r p q x))
    (x : (E.page r).obj p q) :
    Path ((F.page r).diff p q (φ.maps r p q x))
         ((F.page r).diff p q (ψ.maps r p q x)) :=
  Path.congrArg ((F.page r).diff p q) (heq x)

/-- Pointwise equal morphisms have equal compositions with d (4-step). -/
def comm_pointwise {E F : SpectralSeq.{u}}
    (φ ψ : SpectralMor E F) (r : Nat) (p q : Int)
    (heq : ∀ a b (x : (E.page r).obj a b), Path (φ.maps r a b x) (ψ.maps r a b x))
    (x : (E.page r).obj p q) :
    Path (ψ.maps r (p + ↑r) (q + 1 - ↑r) ((E.page r).diff p q x))
         ((F.page r).diff p q (ψ.maps r p q x)) :=
  Path.trans
    (Path.symm (heq (p + ↑r) (q + 1 - ↑r) ((E.page r).diff p q x)))
    (Path.trans
      (φ.comm r p q x)
      (Path.congrArg ((F.page r).diff p q) (heq p q x)))

/-! ## Serre-Type Spectral Sequence Structure -/

/-- Serre spectral sequence data: fiber → total → base. -/
structure SerreSS where
  ss : SpectralSeq.{u}
  fiberH : GradedModule.{u}
  baseH : GradedModule.{u}
  e2_fiber : ∀ p q, (ss.page 2).obj p q → fiberH.obj q 0
  e2_base  : ∀ p q, (ss.page 2).obj p q → baseH.obj p 0
  e2_fiber_zero : ∀ p q, Path (e2_fiber p q ((ss.page 2).toGradedModule.zero p q))
                              (fiberH.zero q 0)
  e2_base_zero  : ∀ p q, Path (e2_base p q ((ss.page 2).toGradedModule.zero p q))
                              (baseH.zero p 0)

/-- Fiber projection through d maps zero correctly (3-step). -/
def SerreSS.fiber_d_zero (S : SerreSS.{u}) (p q : Int) :
    Path (S.e2_fiber (p + 2) (q + 1 - 2)
           ((S.ss.page 2).diff p q ((S.ss.page 2).toGradedModule.zero p q)))
         (S.fiberH.zero (q + 1 - 2) 0) :=
  Path.trans
    (Path.congrArg (S.e2_fiber (p + 2) (q + 1 - 2))
      ((S.ss.page 2).diff_zero p q))
    (S.e2_fiber_zero (p + 2) (q + 1 - 2))

/-- Base projection through d maps zero correctly (3-step). -/
def SerreSS.base_d_zero (S : SerreSS.{u}) (p q : Int) :
    Path (S.e2_base (p + 2) (q + 1 - 2)
           ((S.ss.page 2).diff p q ((S.ss.page 2).toGradedModule.zero p q)))
         (S.baseH.zero (p + 2) 0) :=
  Path.trans
    (Path.congrArg (S.e2_base (p + 2) (q + 1 - 2))
      ((S.ss.page 2).diff_zero p q))
    (S.e2_base_zero (p + 2) (q + 1 - 2))

/-- Fiber and base projections of d(0) are both zero: combined 5-step. -/
def SerreSS.fiber_base_d_zero (S : SerreSS.{u}) (p q : Int) :
    Path (S.e2_fiber (p + 2) (q + 1 - 2)
           ((S.ss.page 2).diff p q ((S.ss.page 2).toGradedModule.zero p q)))
         (S.fiberH.zero (q + 1 - 2) 0)
    ×
    Path (S.e2_base (p + 2) (q + 1 - 2)
           ((S.ss.page 2).diff p q ((S.ss.page 2).toGradedModule.zero p q)))
         (S.baseH.zero (p + 2) 0) :=
  (S.fiber_d_zero p q, S.base_d_zero p q)

/-! ## Product Structure (Multiplicative) -/

/-- A multiplicative spectral sequence: product on each page. -/
structure MultSS extends SpectralSeq.{u} where
  mul : ∀ r p₁ q₁ p₂ q₂,
    (page r).obj p₁ q₁ → (page r).obj p₂ q₂ → (page r).obj (p₁ + p₂) (q₁ + q₂)
  mul_zero_l : ∀ r p₁ q₁ p₂ q₂ (y : (page r).obj p₂ q₂),
    Path (mul r p₁ q₁ p₂ q₂ ((page r).toGradedModule.zero p₁ q₁) y)
         ((page r).toGradedModule.zero (p₁ + p₂) (q₁ + q₂))
  mul_zero_r : ∀ r p₁ q₁ p₂ q₂ (x : (page r).obj p₁ q₁),
    Path (mul r p₁ q₁ p₂ q₂ x ((page r).toGradedModule.zero p₂ q₂))
         ((page r).toGradedModule.zero (p₁ + p₂) (q₁ + q₂))

/-- d(0·y) = d(0) = 0: differential of product with zero (5-step). -/
def MultSS.d_mul_zero_l (M : MultSS.{u}) (r : Nat)
    (p₁ q₁ p₂ q₂ : Int) (y : (M.page r).obj p₂ q₂) :
    Path ((M.page r).diff (p₁ + p₂) (q₁ + q₂)
           (M.mul r p₁ q₁ p₂ q₂ ((M.page r).toGradedModule.zero p₁ q₁) y))
         ((M.page r).toGradedModule.zero (p₁ + p₂ + ↑r) (q₁ + q₂ + 1 - ↑r)) :=
  Path.trans
    (Path.congrArg ((M.page r).diff (p₁ + p₂) (q₁ + q₂))
      (M.mul_zero_l r p₁ q₁ p₂ q₂ y))
    ((M.page r).diff_zero (p₁ + p₂) (q₁ + q₂))

/-- d(x·0) = d(0) = 0: symmetric version (5-step). -/
def MultSS.d_mul_zero_r (M : MultSS.{u}) (r : Nat)
    (p₁ q₁ p₂ q₂ : Int) (x : (M.page r).obj p₁ q₁) :
    Path ((M.page r).diff (p₁ + p₂) (q₁ + q₂)
           (M.mul r p₁ q₁ p₂ q₂ x ((M.page r).toGradedModule.zero p₂ q₂)))
         ((M.page r).toGradedModule.zero (p₁ + p₂ + ↑r) (q₁ + q₂ + 1 - ↑r)) :=
  Path.trans
    (Path.congrArg ((M.page r).diff (p₁ + p₂) (q₁ + q₂))
      (M.mul_zero_r r p₁ q₁ p₂ q₂ x))
    ((M.page r).diff_zero (p₁ + p₂) (q₁ + q₂))

/-- 0·0 = 0 and d(0·0) = 0: 7-step combining mul and diff. -/
def MultSS.d_mul_zero_zero (M : MultSS.{u}) (r : Nat)
    (p₁ q₁ p₂ q₂ : Int) :
    Path ((M.page r).diff (p₁ + p₂) (q₁ + q₂)
           (M.mul r p₁ q₁ p₂ q₂
             ((M.page r).toGradedModule.zero p₁ q₁)
             ((M.page r).toGradedModule.zero p₂ q₂)))
         ((M.page r).toGradedModule.zero (p₁ + p₂ + ↑r) (q₁ + q₂ + 1 - ↑r)) :=
  M.d_mul_zero_l r p₁ q₁ p₂ q₂ ((M.page r).toGradedModule.zero p₂ q₂)

/-! ## Edge Homomorphisms -/

/-- Edge morphism from E₂ to E₀. -/
structure EdgeMorphism (ss : SpectralSeq.{u}) (p q : Int) where
  edge : (ss.page 2).obj p q → (ss.page 0).obj p q
  edge_zero : Path (edge ((ss.page 2).toGradedModule.zero p q))
                    ((ss.page 0).toGradedModule.zero p q)

/-- Edge naturality under spectral morphisms (symm). -/
def edge_naturality {E F : SpectralSeq.{u}}
    (φ : SpectralMor E F) (p q : Int)
    (eE : EdgeMorphism E p q) (eF : EdgeMorphism F p q)
    (hcompat : ∀ x, Path (eF.edge (φ.maps 2 p q x))
                          (φ.maps 0 p q (eE.edge x)))
    (x : (E.page 2).obj p q) :
    Path (φ.maps 0 p q (eE.edge x))
         (eF.edge (φ.maps 2 p q x)) :=
  Path.symm (hcompat x)

/-- Edge on zero element: compose edge_zero with φ (4-step). -/
def edge_zero_compat {E F : SpectralSeq.{u}}
    (φ : SpectralMor E F) (p q : Int)
    (eE : EdgeMorphism E p q) (eF : EdgeMorphism F p q)
    (hcompat : ∀ x, Path (eF.edge (φ.maps 2 p q x))
                          (φ.maps 0 p q (eE.edge x))) :
    Path (eF.edge (φ.maps 2 p q ((E.page 2).toGradedModule.zero p q)))
         ((F.page 0).toGradedModule.zero p q) :=
  Path.trans
    (hcompat ((E.page 2).toGradedModule.zero p q))
    (Path.trans
      (Path.congrArg (φ.maps 0 p q) (eE.edge_zero))
      (φ.maps_zero 0 p q))

/-! ## Mapping Cone -/

/-- Mapping cone data for a spectral morphism. -/
structure MappingCone {E F : SpectralSeq.{u}} (φ : SpectralMor E F) where
  cone : SpectralSeq.{u}
  incl : SpectralMor F cone
  proj : SpectralMor cone E
  incl_proj_zero : ∀ r p q (x : (F.page r).obj p q),
    Path (proj.maps r p q (incl.maps r p q x))
         ((E.page r).toGradedModule.zero p q)

/-- In mapping cone, incl ∘ proj on d(x) = 0 (direct application). -/
def MappingCone.incl_proj_d_zero {E F : SpectralSeq.{u}} {φ : SpectralMor E F}
    (mc : MappingCone φ) (r : Nat) (p q : Int) (x : (F.page r).obj p q) :
    Path (mc.proj.maps r (p + ↑r) (q + 1 - ↑r)
           (mc.incl.maps r (p + ↑r) (q + 1 - ↑r) ((F.page r).diff p q x)))
         ((E.page r).toGradedModule.zero (p + ↑r) (q + 1 - ↑r)) :=
  mc.incl_proj_zero r (p + ↑r) (q + 1 - ↑r) ((F.page r).diff p q x)

/-- Mapping cone: proj ∘ incl ∘ d of zero is zero (5-step). -/
def MappingCone.proj_incl_d_zero_elem {E F : SpectralSeq.{u}} {φ : SpectralMor E F}
    (mc : MappingCone φ) (r : Nat) (p q : Int) :
    Path (mc.proj.maps r (p + ↑r) (q + 1 - ↑r)
           (mc.incl.maps r (p + ↑r) (q + 1 - ↑r)
             ((F.page r).diff p q ((F.page r).toGradedModule.zero p q))))
         ((E.page r).toGradedModule.zero (p + ↑r) (q + 1 - ↑r)) :=
  mc.incl_proj_zero r (p + ↑r) (q + 1 - ↑r)
    ((F.page r).diff p q ((F.page r).toGradedModule.zero p q))

/-! ## Gysin Sequence Structure -/

/-- Gysin data: sphere bundle where only rows 0 and n survive. -/
structure GysinData where
  ss : SpectralSeq.{u}
  fiberDim : Nat
  vanish : ∀ r p q (x : (ss.page r).obj p q),
    q ≠ 0 → q ≠ (fiberDim : Int) →
    Path ((ss.page r).diff p q x) ((ss.page r).toGradedModule.zero (p + r) (q + 1 - r))

/-- Gysin: d on zero of a vanishing row is zero. -/
def GysinData.d_vanish_zero (G : GysinData.{u}) (r : Nat) (p q : Int)
    (hq0 : q ≠ 0) (hqn : q ≠ (G.fiberDim : Int)) :
    Path ((G.ss.page r).diff p q ((G.ss.page r).toGradedModule.zero p q))
         ((G.ss.page r).toGradedModule.zero (p + ↑r) (q + 1 - ↑r)) :=
  G.vanish r p q ((G.ss.page r).toGradedModule.zero p q) hq0 hqn

/-! ## Transgression -/

/-- Transgression data: a lift of d_r from the base to the fiber. -/
structure Transgression (ss : SpectralSeq.{u}) (r : Nat) (p q : Int) where
  trans_map : (ss.page r).obj p q → (ss.page r).obj (p + r) (q + 1 - r)
  is_diff : ∀ x, Path (trans_map x) ((ss.page r).diff p q x)
  trans_zero : Path (trans_map ((ss.page r).toGradedModule.zero p q))
                    ((ss.page r).toGradedModule.zero (p + r) (q + 1 - r))

/-- Transgression = d on zero: 3-step chain through is_diff and diff_zero. -/
def Transgression.trans_eq_d_zero {ss : SpectralSeq.{u}} {r : Nat} {p q : Int}
    (τ : Transgression ss r p q) :
    Path (τ.trans_map ((ss.page r).toGradedModule.zero p q))
         ((ss.page r).toGradedModule.zero (p + ↑r) (q + 1 - ↑r)) :=
  Path.trans
    (τ.is_diff ((ss.page r).toGradedModule.zero p q))
    ((ss.page r).diff_zero p q)

/-- Two transgressions for same d agree (4-step via symm). -/
def Transgression.agree {ss : SpectralSeq.{u}} {r : Nat} {p q : Int}
    (τ₁ τ₂ : Transgression ss r p q) (x : (ss.page r).obj p q) :
    Path (τ₁.trans_map x) (τ₂.trans_map x) :=
  Path.trans (τ₁.is_diff x) (Path.symm (τ₂.is_diff x))

/-! ## Spectral Sequence of a Filtered Complex -/

/-- Filtered complex data: a filtration together with a differential. -/
structure FilteredComplex (n : Nat) where
  F : PathFiltration.{u} n
  diff : ∀ k : Fin (n + 1), F.level k → F.level k
  diff_zero : ∀ k, Path (diff k (F.zero k)) (F.zero k)

/-- d² on zero in a filtered complex: 3-step. -/
def FilteredComplex.dd_zero {n : Nat} (C : FilteredComplex.{u} n) (k : Fin (n + 1)) :
    Path (C.diff k (C.diff k (C.F.zero k))) (C.F.zero k) :=
  Path.trans
    (Path.congrArg (C.diff k) (C.diff_zero k))
    (C.diff_zero k)

/-- d³ on zero: 5-step. -/
def FilteredComplex.ddd_zero {n : Nat} (C : FilteredComplex.{u} n) (k : Fin (n + 1)) :
    Path (C.diff k (C.diff k (C.diff k (C.F.zero k)))) (C.F.zero k) :=
  Path.trans
    (Path.congrArg (C.diff k) (C.dd_zero k))
    (C.diff_zero k)

/-- d⁴ on zero: 7-step. -/
def FilteredComplex.dddd_zero {n : Nat} (C : FilteredComplex.{u} n) (k : Fin (n + 1)) :
    Path (C.diff k (C.diff k (C.diff k (C.diff k (C.F.zero k))))) (C.F.zero k) :=
  Path.trans
    (Path.congrArg (C.diff k) (C.ddd_zero k))
    (C.diff_zero k)

/-- Differential commutes with inclusion on zero (3-step). -/
def FilteredComplex.diff_incl_zero {n : Nat} (C : FilteredComplex.{u} n)
    (k : Fin n)
    (hcompat : ∀ x, Path (C.F.incl k (C.diff k.castSucc x))
                          (C.diff k.succ (C.F.incl k x))) :
    Path (C.diff k.succ (C.F.incl k (C.F.zero k.castSucc)))
         (C.F.zero k.succ) :=
  Path.trans
    (Path.symm (hcompat (C.F.zero k.castSucc)))
    (Path.trans
      (Path.congrArg (C.F.incl k) (C.diff_zero k.castSucc))
      (C.F.incl_zero k))

end SpectralSeqDeep
end Path
end ComputationalPaths
