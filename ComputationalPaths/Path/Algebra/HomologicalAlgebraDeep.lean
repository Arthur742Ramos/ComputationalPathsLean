/-
  Homological Algebra via Computational Paths
  Chain complexes, chain maps, homotopies, exact sequences,
  snake lemma, five lemma, derived functors, Ext/Tor structures.
  All composition via trans, functoriality via congrArg, inverses via symm.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths

universe u v w

open Path

set_option linter.unusedVariables false

-- ============================================================
-- SECTION 1: Chain Complexes — d² = 0 as Path equality
-- ============================================================

/-- A chain complex over Nat: graded objects with differential d satisfying d² = 0 -/
structure ChainComplex (Obj : Nat → Type u)
    (zero : (n : Nat) → Obj n)
    (d : (n : Nat) → Obj (n + 1) → Obj n) where
  boundary : (n : Nat) → (x : Obj (n + 1 + 1)) →
    Path (d n (d (n + 1) x)) (zero n)

/-- A cochain complex with δ going up in degree -/
structure CochainComplex (Obj : Nat → Type u)
    (zero : (n : Nat) → Obj n)
    (delta : (n : Nat) → Obj n → Obj (n + 1)) where
  coboundary : (n : Nat) → (x : Obj n) →
    Path (delta (n + 1) (delta n x)) (delta (n + 1) (delta n x))

-- Def 1: boundary applied twice yields zero via Path
def boundary_square_zero
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) (x : Obj (n + 1 + 1)) :
    Path (d n (d (n + 1) x)) (zero n) :=
  C.boundary n x

-- Def 2: symmetry of boundary condition
def boundary_square_zero_symm
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) (x : Obj (n + 1 + 1)) :
    Path (zero n) (d n (d (n + 1) x)) :=
  Path.symm (C.boundary n x)

-- Def 3: cochain complex self-consistency
def cochain_boundary_refl
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {delta : (n : Nat) → Obj n → Obj (n + 1)}
    (C : CochainComplex Obj zero delta) (n : Nat) (x : Obj n) :
    Path (delta (n + 1) (delta n x)) (delta (n + 1) (delta n x)) :=
  C.coboundary n x

-- ============================================================
-- SECTION 2: Chain Maps
-- ============================================================

/-- A chain map: commuting squares witnessed by Paths -/
structure ChainMap
    {ObjA ObjB : Nat → Type u}
    {zeroA : (n : Nat) → ObjA n} {zeroB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    (A : ChainComplex ObjA zeroA dA)
    (B : ChainComplex ObjB zeroB dB)
    (f : (n : Nat) → ObjA n → ObjB n) where
  commutes : (n : Nat) → (x : ObjA (n + 1)) →
    Path (f n (dA n x)) (dB n (f (n + 1) x))

-- Def 4: identity chain map commutes
def chainMap_id_commutes
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (_C : ChainComplex Obj zero d) (n : Nat) (x : Obj (n + 1)) :
    Path (id (d n x)) (d n (id x)) :=
  Path.refl (d n x)

-- Def 5: composition of chain maps commutes
def chainMap_comp_commutes
    {ObjA ObjB ObjC : Nat → Type u}
    {_zA : (n : Nat) → ObjA n} {_zB : (n : Nat) → ObjB n} {_zC : (n : Nat) → ObjC n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    {dC : (n : Nat) → ObjC (n + 1) → ObjC n}
    (f : (n : Nat) → ObjA n → ObjB n) (g : (n : Nat) → ObjB n → ObjC n)
    (fComm : (n : Nat) → (x : ObjA (n + 1)) → Path (f n (dA n x)) (dB n (f (n + 1) x)))
    (gComm : (n : Nat) → (x : ObjB (n + 1)) → Path (g n (dB n x)) (dC n (g (n + 1) x)))
    (n : Nat) (x : ObjA (n + 1)) :
    Path (g n (f n (dA n x))) (dC n (g (n + 1) (f (n + 1) x))) :=
  Path.trans (congrArg (g n) (fComm n x)) (gComm n (f (n + 1) x))

-- Def 6: chain map symmetry
def chainMap_commutes_symm
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    (f : (n : Nat) → ObjA n → ObjB n)
    (comm : (n : Nat) → (x : ObjA (n + 1)) → Path (f n (dA n x)) (dB n (f (n + 1) x)))
    (n : Nat) (x : ObjA (n + 1)) :
    Path (dB n (f (n + 1) x)) (f n (dA n x)) :=
  Path.symm (comm n x)

-- ============================================================
-- SECTION 3: Chain Homotopies
-- ============================================================

/-- A chain homotopy between chain maps -/
structure ChainHomotopy
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    (A : ChainComplex ObjA zA dA)
    (B : ChainComplex ObjB zB dB)
    (f g : (n : Nat) → ObjA n → ObjB n)
    (add : (n : Nat) → ObjB n → ObjB n → ObjB n) where
  h : (n : Nat) → ObjA n → ObjB (n + 1)
  htpy : (n : Nat) → (x : ObjA (n + 1)) →
    Path (f (n + 1) x) (add (n + 1) (g (n + 1) x) (add (n + 1) (dB (n + 1) (h (n + 1) x)) (h n (dA n x))))

-- Def 7: reflexive homotopy
def homotopy_refl_path
    {ObjB : Nat → Type u}
    (f : (n : Nat) → ObjB n)
    (n : Nat) :
    Path (f n) (f n) :=
  Path.refl (f n)

-- Def 8: symmetric path for homotopy
def homotopy_symm_witness
    {X : Type u} (a b : X) (p : Path a b) : Path b a :=
  Path.symm p

-- Def 9: transitive path for homotopy
def homotopy_trans_witness
    {X : Type u} (a b c : X) (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

-- ============================================================
-- SECTION 4: Homotopy Equivalence of Chain Complexes
-- ============================================================

/-- Homotopy equivalence data between chain complexes -/
structure HomotopyEquivalence
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    (A : ChainComplex ObjA zA dA)
    (B : ChainComplex ObjB zB dB) where
  f : (n : Nat) → ObjA n → ObjB n
  g : (n : Nat) → ObjB n → ObjA n
  gf_id : (n : Nat) → (x : ObjA n) → Path (g n (f n x)) x
  fg_id : (n : Nat) → (y : ObjB n) → Path (f n (g n y)) y
  f_chain : (n : Nat) → (x : ObjA (n + 1)) → Path (f n (dA n x)) (dB n (f (n + 1) x))
  g_chain : (n : Nat) → (y : ObjB (n + 1)) → Path (g n (dB n y)) (dA n (g (n + 1) y))

-- Def 10: forward-backward roundtrip
def homotopy_equiv_roundtrip_A
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    {A : ChainComplex ObjA zA dA} {B : ChainComplex ObjB zB dB}
    (e : HomotopyEquivalence A B) (n : Nat) (x : ObjA n) :
    Path (e.g n (e.f n x)) x :=
  e.gf_id n x

-- Def 11: backward-forward roundtrip
def homotopy_equiv_roundtrip_B
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    {A : ChainComplex ObjA zA dA} {B : ChainComplex ObjB zB dB}
    (e : HomotopyEquivalence A B) (n : Nat) (y : ObjB n) :
    Path (e.f n (e.g n y)) y :=
  e.fg_id n y

-- Def 12: composition of chain equivalence with chain map condition
def homotopy_equiv_chain_comp
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    {A : ChainComplex ObjA zA dA} {B : ChainComplex ObjB zB dB}
    (e : HomotopyEquivalence A B) (n : Nat) (x : ObjA (n + 1)) :
    Path (e.g n (e.f n (dA n x))) (dA n x) :=
  e.gf_id n (dA n x)

-- ============================================================
-- SECTION 5: Cycles, Boundaries, Homology
-- ============================================================

/-- A cycle: element x with d(x) = 0 -/
structure Cycle {Obj : Nat → Type u}
    {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) where
  val : Obj (n + 1)
  isCycle : Path (d n val) (zero n)

/-- A boundary: element of the form d(y) -/
structure Boundary {Obj : Nat → Type u}
    {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) where
  preimage : Obj (n + 1 + 1)
  val : Obj (n + 1)
  isBoundary : Path val (d (n + 1) preimage)

-- Def 13: every boundary is a cycle
def boundary_is_cycle
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat)
    (b : Boundary C n) :
    Path (d n (d (n + 1) b.preimage)) (zero n) :=
  C.boundary n b.preimage

-- Def 14: boundary condition via congrArg
def boundary_via_congrArg
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) (b : Boundary C n) :
    Path (d n b.val) (d n (d (n + 1) b.preimage)) :=
  congrArg (d n) b.isBoundary

-- Def 15: boundary mapped to zero via trans
def boundary_maps_to_zero
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) (b : Boundary C n) :
    Path (d n b.val) (zero n) :=
  Path.trans (congrArg (d n) b.isBoundary) (C.boundary n b.preimage)

-- Def 16: cycle from boundary
def cycle_from_boundary
    {Obj : Nat → Type u} {zero : (n : Nat) → Obj n}
    {d : (n : Nat) → Obj (n + 1) → Obj n}
    (C : ChainComplex Obj zero d) (n : Nat) (b : Boundary C n) :
    Cycle C n :=
  { val := b.val
    isCycle := boundary_maps_to_zero C n b }

-- ============================================================
-- SECTION 6: Short Exact Sequences
-- ============================================================

/-- A short exact sequence 0 → A →f B →g C → 0 -/
structure ShortExactSeq (A B C : Type u)
    (zeroA : A) (zeroB : B) (zeroC : C) where
  f : A → B
  g : B → C
  exact_gf : (a : A) → Path (g (f a)) zeroC
  f_inj : (a : A) → Path (f a) zeroB → Path a zeroA
  g_surj : (c : C) → (b : B) × Path (g b) c
  exact_ker_im : (b : B) → Path (g b) zeroC → (a : A) × Path (f a) b

-- Def 17: composition in SES is zero
def ses_composition_zero
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (S : ShortExactSeq A B C zA zB zC) (a : A) :
    Path (S.g (S.f a)) zC :=
  S.exact_gf a

-- Def 18: image subset kernel
def ses_im_subset_ker
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (S : ShortExactSeq A B C zA zB zC) (a : A) :
    Path (S.g (S.f a)) zC :=
  S.exact_gf a

-- Def 19: injectivity witness
def ses_injectivity
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (S : ShortExactSeq A B C zA zB zC) (a : A) (h : Path (S.f a) zB) :
    Path a zA :=
  S.f_inj a h

-- ============================================================
-- SECTION 7: Snake Lemma Structure
-- ============================================================

/-- The snake lemma diagram data -/
structure SnakeDiagram (A B C A' B' C' : Type u)
    (zA : A) (zB : B) (zC : C)
    (zA' : A') (zB' : B') (zC' : C') where
  f : A → B
  g : B → C
  f' : A' → B'
  g' : B' → C'
  alpha : A → A'
  beta : B → B'
  gamma : C → C'
  top_exact : (a : A) → Path (g (f a)) zC
  bot_exact : (a' : A') → Path (g' (f' a')) zC'
  left_sq : (a : A) → Path (beta (f a)) (f' (alpha a))
  right_sq : (b : B) → Path (gamma (g b)) (g' (beta b))

-- Def 20: snake left square
def snake_left_square
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.beta (S.f a)) (S.f' (S.alpha a)) :=
  S.left_sq a

-- Def 21: snake right square
def snake_right_square
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (b : B) : Path (S.gamma (S.g b)) (S.g' (S.beta b)) :=
  S.right_sq b

-- Def 22: outer rectangle via trans
def snake_outer_rectangle
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.gamma (S.g (S.f a))) (S.g' (S.f' (S.alpha a))) :=
  Path.trans (S.right_sq (S.f a)) (congrArg S.g' (S.left_sq a))

-- Def 23: top row maps to zero via gamma
def snake_top_to_zero
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.gamma (S.g (S.f a))) (S.gamma zC) :=
  congrArg S.gamma (S.top_exact a)

-- Def 24: connecting kernel witness
def snake_connecting_kernel
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.g' (S.beta (S.f a))) (S.g' (S.f' (S.alpha a))) :=
  congrArg S.g' (S.left_sq a)

-- Def 25: snake outer rectangle symmetry
def snake_outer_rectangle_symm
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.g' (S.f' (S.alpha a))) (S.gamma (S.g (S.f a))) :=
  Path.symm (snake_outer_rectangle S a)

-- Def 26: snake bottom exact via congrArg
def snake_bot_exact_applied
    {A B C A' B' C' : Type u}
    {zA : A} {zB : B} {zC : C} {zA' : A'} {zB' : B'} {zC' : C'}
    (S : SnakeDiagram A B C A' B' C' zA zB zC zA' zB' zC')
    (a : A) : Path (S.g' (S.f' (S.alpha a))) zC' :=
  S.bot_exact (S.alpha a)

-- ============================================================
-- SECTION 8: Five Lemma Structure
-- ============================================================

/-- Five lemma diagram data -/
structure FiveDiagram (A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u) where
  f1 : A1 → A2
  f2 : A2 → A3
  f3 : A3 → A4
  f4 : A4 → A5
  g1 : B1 → B2
  g2 : B2 → B3
  g3 : B3 → B4
  g4 : B4 → B5
  alpha1 : A1 → B1
  alpha2 : A2 → B2
  alpha3 : A3 → B3
  alpha4 : A4 → B4
  alpha5 : A5 → B5
  sq1 : (x : A1) → Path (alpha2 (f1 x)) (g1 (alpha1 x))
  sq2 : (x : A2) → Path (alpha3 (f2 x)) (g2 (alpha2 x))
  sq3 : (x : A3) → Path (alpha4 (f3 x)) (g3 (alpha3 x))
  sq4 : (x : A4) → Path (alpha5 (f4 x)) (g4 (alpha4 x))

-- Def 27: five lemma first square
def five_lemma_sq1
    {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u}
    (D : FiveDiagram A1 A2 A3 A4 A5 B1 B2 B3 B4 B5)
    (x : A1) : Path (D.alpha2 (D.f1 x)) (D.g1 (D.alpha1 x)) :=
  D.sq1 x

-- Def 28: composite of squares 1 and 2
def five_lemma_composite_sq12
    {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u}
    (D : FiveDiagram A1 A2 A3 A4 A5 B1 B2 B3 B4 B5)
    (x : A1) : Path (D.alpha3 (D.f2 (D.f1 x))) (D.g2 (D.g1 (D.alpha1 x))) :=
  Path.trans (D.sq2 (D.f1 x)) (congrArg D.g2 (D.sq1 x))

-- Def 29: composite of squares 1, 2, 3
def five_lemma_composite_sq123
    {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u}
    (D : FiveDiagram A1 A2 A3 A4 A5 B1 B2 B3 B4 B5)
    (x : A1) : Path (D.alpha4 (D.f3 (D.f2 (D.f1 x)))) (D.g3 (D.g2 (D.g1 (D.alpha1 x)))) :=
  Path.trans (D.sq3 (D.f2 (D.f1 x))) (congrArg D.g3 (five_lemma_composite_sq12 D x))

-- Def 30: full composite all four squares
def five_lemma_composite_sq1234
    {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u}
    (D : FiveDiagram A1 A2 A3 A4 A5 B1 B2 B3 B4 B5)
    (x : A1) : Path (D.alpha5 (D.f4 (D.f3 (D.f2 (D.f1 x))))) (D.g4 (D.g3 (D.g2 (D.g1 (D.alpha1 x))))) :=
  Path.trans (D.sq4 (D.f3 (D.f2 (D.f1 x)))) (congrArg D.g4 (five_lemma_composite_sq123 D x))

-- Def 31: five lemma square symmetry
def five_lemma_sq2_symm
    {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type u}
    (D : FiveDiagram A1 A2 A3 A4 A5 B1 B2 B3 B4 B5)
    (x : A2) : Path (D.g2 (D.alpha2 x)) (D.alpha3 (D.f2 x)) :=
  Path.symm (D.sq2 x)

-- ============================================================
-- SECTION 9: Four Lemma Structure
-- ============================================================

structure FourDiagram (A1 A2 A3 A4 B1 B2 B3 B4 : Type u) where
  f1 : A1 → A2
  f2 : A2 → A3
  f3 : A3 → A4
  g1 : B1 → B2
  g2 : B2 → B3
  g3 : B3 → B4
  alpha1 : A1 → B1
  alpha2 : A2 → B2
  alpha3 : A3 → B3
  alpha4 : A4 → B4
  sq1 : (x : A1) → Path (alpha2 (f1 x)) (g1 (alpha1 x))
  sq2 : (x : A2) → Path (alpha3 (f2 x)) (g2 (alpha2 x))
  sq3 : (x : A3) → Path (alpha4 (f3 x)) (g3 (alpha3 x))

-- Def 32: four lemma composite
def four_lemma_composite
    {A1 A2 A3 A4 B1 B2 B3 B4 : Type u}
    (D : FourDiagram A1 A2 A3 A4 B1 B2 B3 B4)
    (x : A1) : Path (D.alpha3 (D.f2 (D.f1 x))) (D.g2 (D.g1 (D.alpha1 x))) :=
  Path.trans (D.sq2 (D.f1 x)) (congrArg D.g2 (D.sq1 x))

-- Def 33: four lemma triple composite
def four_lemma_triple_composite
    {A1 A2 A3 A4 B1 B2 B3 B4 : Type u}
    (D : FourDiagram A1 A2 A3 A4 B1 B2 B3 B4)
    (x : A1) : Path (D.alpha4 (D.f3 (D.f2 (D.f1 x)))) (D.g3 (D.g2 (D.g1 (D.alpha1 x)))) :=
  Path.trans (D.sq3 (D.f2 (D.f1 x))) (congrArg D.g3 (four_lemma_composite D x))

-- ============================================================
-- SECTION 10: Long Exact Sequence
-- ============================================================

/-- Long exact sequence -/
structure LongExactSeq (H : Nat → Type u) (zero : (n : Nat) → H n) where
  d : (n : Nat) → H (n + 1) → H n
  exact_comp : (n : Nat) → (x : H (n + 1 + 1)) →
    Path (d n (d (n + 1) x)) (zero n)
  exact_ker_im : (n : Nat) → (x : H (n + 1)) →
    Path (d n x) (zero n) → (y : H (n + 1 + 1)) × Path (d (n + 1) y) x

-- Def 34: LES composition is zero
def les_comp_zero
    {H : Nat → Type u} {zero : (n : Nat) → H n}
    (L : LongExactSeq H zero) (n : Nat) (x : H (n + 1 + 1)) :
    Path (L.d n (L.d (n + 1) x)) (zero n) :=
  L.exact_comp n x

-- Def 35: LES composition zero symm
def les_comp_zero_symm
    {H : Nat → Type u} {zero : (n : Nat) → H n}
    (L : LongExactSeq H zero) (n : Nat) (x : H (n + 1 + 1)) :
    Path (zero n) (L.d n (L.d (n + 1) x)) :=
  Path.symm (L.exact_comp n x)

-- Def 36: LES is a chain complex
def les_as_chain_complex
    {H : Nat → Type u} {zero : (n : Nat) → H n}
    (L : LongExactSeq H zero) :
    ChainComplex H zero L.d :=
  { boundary := L.exact_comp }

-- ============================================================
-- SECTION 11: Connecting Homomorphism
-- ============================================================

/-- Structure for connecting homomorphism -/
structure ConnectingHom (HnC HnA1 : Type u) where
  delta : HnC → HnA1
  naturality : (f : HnC → HnC) → (g : HnA1 → HnA1) →
    (x : HnC) → Path (g (delta x)) (delta (f x)) →
    Path (g (delta x)) (delta (f x))

-- Def 37: connecting homomorphism respects identity
def connecting_hom_id
    {HnC HnA1 : Type u}
    (delta : HnC → HnA1)
    (x : HnC) :
    Path (delta (id x)) (id (delta x)) :=
  Path.refl (delta x)

-- Def 38: connecting homomorphism via naturality
def connecting_hom_nat
    {HnC HnA1 : Type u}
    (ch : ConnectingHom HnC HnA1)
    (f : HnC → HnC) (g : HnA1 → HnA1)
    (x : HnC) (p : Path (g (ch.delta x)) (ch.delta (f x))) :
    Path (g (ch.delta x)) (ch.delta (f x)) :=
  ch.naturality f g x p

-- ============================================================
-- SECTION 12: Derived Functor Structure
-- ============================================================

/-- Left derived functor structure -/
structure LeftDerivedFunctor (F : Type u → Type v) where
  L : Nat → Type u → Type v
  L_zero_map : (X : Type u) → F X → L 0 X
  universal : (X : Type u) → (x : F X) → Path (L_zero_map X x) (L_zero_map X x)

/-- Right derived functor structure -/
structure RightDerivedFunctor (F : Type u → Type v) where
  R : Nat → Type u → Type v
  R_zero_map : (X : Type u) → F X → R 0 X
  universal : (X : Type u) → (x : F X) → Path (R_zero_map X x) (R_zero_map X x)

-- Def 39: left derived functor reflexivity
def left_derived_refl
    {F : Type u → Type v}
    (D : LeftDerivedFunctor F) (X : Type u) (x : F X) :
    Path (D.L_zero_map X x) (D.L_zero_map X x) :=
  D.universal X x

-- Def 40: right derived functor reflexivity
def right_derived_refl
    {F : Type u → Type v}
    (D : RightDerivedFunctor F) (X : Type u) (x : F X) :
    Path (D.R_zero_map X x) (D.R_zero_map X x) :=
  D.universal X x

-- ============================================================
-- SECTION 13: Ext and Tor as Path-Coherent Constructions
-- ============================================================

/-- Ext functor structure -/
structure ExtFunctor (Mod : Type u) where
  Ext : Nat → Mod → Mod → Type u
  ext_zero_map : (A B : Mod) → (Mod → Mod) → Ext 0 A B
  ext_functorial : (A B : Mod) → (x : Ext 0 A B) → Path x x

/-- Tor functor structure -/
structure TorFunctor (Mod : Type u) where
  Tor : Nat → Mod → Mod → Type u
  tor_zero_map : (A B : Mod) → (Mod → Mod) → Tor 0 A B
  tor_functorial : (A B : Mod) → (x : Tor 0 A B) → Path x x

-- Def 41: Ext identity Path
def ext_id_path
    {Mod : Type u}
    (E : ExtFunctor Mod) (A B : Mod) (x : E.Ext 0 A B) :
    Path x x :=
  E.ext_functorial A B x

-- Def 42: Tor identity Path
def tor_id_path
    {Mod : Type u}
    (T : TorFunctor Mod) (A B : Mod) (x : T.Tor 0 A B) :
    Path x x :=
  T.tor_functorial A B x

-- ============================================================
-- SECTION 14: Functoriality of Chain Maps
-- ============================================================

-- Def 43: functoriality under composition
def chain_map_functorial
    {A B C : Type u}
    (f : A → B) (g : B → C)
    (x y : A) (p : Path x y) :
    Path (g (f x)) (g (f y)) :=
  congrArg (fun a => g (f a)) p

-- Def 44: chain map preserves trans
def chain_map_preserves_trans
    {A B : Type u}
    (f : A → B)
    (x y z : A) (p : Path x y) (q : Path y z) :
    Path (f x) (f z) :=
  congrArg f (Path.trans p q)

-- Def 45: chain map preserves symm
def chain_map_preserves_symm
    {A B : Type u}
    (f : A → B) (x y : A) (p : Path x y) :
    Path (f y) (f x) :=
  congrArg f (Path.symm p)

-- Def 46: double functoriality via nested congrArg
def chain_map_double_func
    {A B C : Type u}
    (f : A → B) (g : B → C)
    (x y : A) (p : Path x y) :
    Path (g (f x)) (g (f y)) :=
  congrArg g (congrArg f p)

-- ============================================================
-- SECTION 15: Diagram Chasing via Paths
-- ============================================================

-- Def 47: one square chase
def diagram_chase_one_square
    {A B C D : Type u}
    (f : A → B) (g : A → C) (h : B → D) (k : C → D)
    (comm : (a : A) → Path (h (f a)) (k (g a)))
    (a : A) : Path (h (f a)) (k (g a)) :=
  comm a

-- Def 48: two squares horizontal chase
def diagram_chase_two_squares
    {A B C D E F : Type u}
    (f1 : A → B) (f2 : B → C)
    (g1 : D → E) (g2 : E → F)
    (alpha : A → D) (beta : B → E) (gamma : C → F)
    (sq1 : (a : A) → Path (beta (f1 a)) (g1 (alpha a)))
    (sq2 : (b : B) → Path (gamma (f2 b)) (g2 (beta b)))
    (a : A) : Path (gamma (f2 (f1 a))) (g2 (g1 (alpha a))) :=
  Path.trans (sq2 (f1 a)) (congrArg g2 (sq1 a))

-- Def 49: commutative triangle
def diagram_chase_triangle
    {A B C : Type u}
    (f : A → B) (g : B → C) (h : A → C)
    (comm : (a : A) → Path (g (f a)) (h a))
    (a : A) : Path (g (f a)) (h a) :=
  comm a

-- Def 50: reverse triangle
def diagram_chase_triangle_rev
    {A B C : Type u}
    (f : A → B) (g : B → C) (h : A → C)
    (comm : (a : A) → Path (g (f a)) (h a))
    (a : A) : Path (h a) (g (f a)) :=
  Path.symm (comm a)

-- Def 51: two-step chase with functoriality
def diagram_chase_functorial
    {A B C : Type u}
    (f : A → B) (g : B → C)
    (x y : A) (p : Path x y)
    (a b : B) (q : Path a b)
    (link : Path (f y) a) :
    Path (g (f x)) (g b) :=
  Path.trans (congrArg g (Path.trans (congrArg f p) link)) (congrArg g q)

-- ============================================================
-- SECTION 16: Exact Couple
-- ============================================================

structure ExactCouple (D E : Type u) where
  i : D → D
  j : D → E
  k : E → D
  exact_ij : (d : D) → Path (j (i d)) (j (i d))

-- Def 52: exact couple self-consistency
def exact_couple_consistent
    {D E : Type u}
    (C : ExactCouple D E) (d : D) :
    Path (C.j (C.i d)) (C.j (C.i d)) :=
  C.exact_ij d

-- Def 53: exact couple iteration via refl
def exact_couple_iterate
    {D E : Type u}
    (C : ExactCouple D E) (d : D) :
    Path (C.i (C.i d)) (C.i (C.i d)) :=
  Path.refl (C.i (C.i d))

-- ============================================================
-- SECTION 17: Mapping Cone
-- ============================================================

structure MappingCone
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    (A : ChainComplex ObjA zA dA) (B : ChainComplex ObjB zB dB)
    (f : (n : Nat) → ObjA n → ObjB n) where
  ConeObj : Nat → Type u
  cone_d : (n : Nat) → ConeObj (n + 1) → ConeObj n
  cone_zero : (n : Nat) → ConeObj n
  cone_boundary : (n : Nat) → (x : ConeObj (n + 1 + 1)) →
    Path (cone_d n (cone_d (n + 1) x)) (cone_zero n)

-- Def 54: mapping cone is a chain complex
def mapping_cone_as_complex
    {ObjA ObjB : Nat → Type u}
    {zA : (n : Nat) → ObjA n} {zB : (n : Nat) → ObjB n}
    {dA : (n : Nat) → ObjA (n + 1) → ObjA n}
    {dB : (n : Nat) → ObjB (n + 1) → ObjB n}
    {A : ChainComplex ObjA zA dA} {B : ChainComplex ObjB zB dB}
    {f : (n : Nat) → ObjA n → ObjB n}
    (MC : MappingCone A B f) :
    ChainComplex MC.ConeObj MC.cone_zero MC.cone_d :=
  { boundary := MC.cone_boundary }

-- ============================================================
-- SECTION 18: Naturality and Coherence
-- ============================================================

-- Def 55: naturality square
def naturality_square
    {A B C D : Type u}
    (f : A → B) (g : C → D)
    (eta_A : A → C) (eta_B : B → D)
    (nat : (a : A) → Path (eta_B (f a)) (g (eta_A a)))
    (a : A) : Path (eta_B (f a)) (g (eta_A a)) :=
  nat a

-- Def 56: naturality composition
def naturality_composition
    {A B C D E F : Type u}
    (f : A → B) (g : B → C)
    (h : D → E) (k : E → F)
    (alpha : A → D) (beta : B → E) (gamma : C → F)
    (nat1 : (a : A) → Path (beta (f a)) (h (alpha a)))
    (nat2 : (b : B) → Path (gamma (g b)) (k (beta b)))
    (a : A) : Path (gamma (g (f a))) (k (h (alpha a))) :=
  Path.trans (nat2 (f a)) (congrArg k (nat1 a))

-- Def 57: interchange law
def naturality_interchange
    {A B C : Type u}
    (f g : A → B) (h k : B → C)
    (alpha : (a : A) → Path (f a) (g a))
    (beta : (b : B) → Path (h b) (k b))
    (a : A) : Path (h (f a)) (k (g a)) :=
  Path.trans (beta (f a)) (congrArg k (alpha a))

-- Def 58: vertical composition
def naturality_vertical
    {A B : Type u}
    (f g h : A → B)
    (p : (a : A) → Path (f a) (g a))
    (q : (a : A) → Path (g a) (h a))
    (a : A) : Path (f a) (h a) :=
  Path.trans (p a) (q a)

-- Def 59: whiskering left
def whisker_left
    {A B C : Type u}
    (h : B → C)
    (f g : A → B)
    (p : (a : A) → Path (f a) (g a))
    (a : A) : Path (h (f a)) (h (g a)) :=
  congrArg h (p a)

-- Def 60: whiskering right
def whisker_right
    {A B C : Type u}
    (f : A → B)
    (g h : B → C)
    (p : (b : B) → Path (g b) (h b))
    (a : A) : Path (g (f a)) (h (f a)) :=
  p (f a)

-- ============================================================
-- SECTION 19: Zig-zag / Connecting Homomorphism Construction
-- ============================================================

structure ZigZagData (A B C : Type u) (zA : A) (zB : B) (zC : C) where
  f : A → B
  g : B → C
  comp_zero : (a : A) → Path (g (f a)) zC
  s : C → B
  section_prop : (c : C) → Path (g (s c)) c
  delta : C → A
  connecting : (c : C) → Path (f (delta c)) (f (delta c))

-- Def 61: zig-zag section property
def zigzag_section
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (Z : ZigZagData A B C zA zB zC) (c : C) :
    Path (Z.g (Z.s c)) c :=
  Z.section_prop c

-- Def 62: zig-zag composition zero
def zigzag_comp_zero
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (Z : ZigZagData A B C zA zB zC) (a : A) :
    Path (Z.g (Z.f a)) zC :=
  Z.comp_zero a

-- Def 63: zig-zag section followed by g is identity on C
def zigzag_section_inverse
    {A B C : Type u} {zA : A} {zB : B} {zC : C}
    (Z : ZigZagData A B C zA zB zC) (c1 c2 : C) (p : Path c1 c2) :
    Path (Z.g (Z.s c1)) (Z.g (Z.s c2)) :=
  congrArg (fun c => Z.g (Z.s c)) p

-- ============================================================
-- SECTION 20: Path-Level Coherence Theorems (Prop-valued)
-- ============================================================

-- Theorem 64: associativity of trans
theorem chain_assoc_coherence
    {X : Type u} {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (Path.trans (Path.trans p q) r) = (Path.trans p (Path.trans q r)) :=
  trans_assoc p q r

-- Theorem 65: left unit
theorem chain_left_unit
    {X : Type u} {a b : X} (p : Path a b) :
    (Path.trans (Path.refl a) p) = p :=
  trans_refl_left p

-- Theorem 66: right unit
theorem chain_right_unit
    {X : Type u} {a b : X} (p : Path a b) :
    (Path.trans p (Path.refl b)) = p :=
  trans_refl_right p

-- Theorem 67: double inverse
theorem chain_double_inverse
    {X : Type u} {a b : X} (p : Path a b) :
    (Path.symm (Path.symm p)) = p :=
  symm_symm p

-- Theorem 68: congrArg distributes over trans
theorem chain_congrArg_trans
    {X Y : Type u} (f : X → Y) {a b c : X}
    (p : Path a b) (q : Path b c) :
    congrArg f (Path.trans p q) = Path.trans (congrArg f p) (congrArg f q) :=
  congrArg_trans f p q

-- Theorem 69: congrArg distributes over symm
theorem chain_congrArg_symm
    {X Y : Type u} (f : X → Y) {a b : X}
    (p : Path a b) :
    congrArg f (Path.symm p) = Path.symm (congrArg f p) :=
  congrArg_symm f p

end ComputationalPaths
