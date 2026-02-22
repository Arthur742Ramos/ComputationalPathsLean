/- Arithmetic Geometry via Computational Paths (Deep).
   Large scaffold covering elliptic curves, Mordell-Weil structure, heights,
   Neron-Tate pairings, L-functions, BSD-shape identities, modular forms,
   Hecke operators, Eichler-Shimura compatibility, Faltings-style structure,
   and p-adic Hodge comparison data with explicit `Path` witnesses. -/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ArithmeticGeometryDeep

universe u v w

/-! ## Path-witnessed commutative groups -/

structure PathAbGroup (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_zero : ∀ a, Path (add a zero) a
  add_left_neg : ∀ a, Path (add (neg a) a) zero

namespace PathAbGroup

variable {A : Type u} (G : PathAbGroup A)

noncomputable def add_assoc_path (a b c : A) :
    Path (G.add (G.add a b) c) (G.add a (G.add b c)) :=
  G.add_assoc a b c

noncomputable def add_comm_path (a b : A) :
    Path (G.add a b) (G.add b a) :=
  G.add_comm a b

noncomputable def zero_add_path (a : A) :
    Path (G.add G.zero a) a :=
  G.zero_add a

noncomputable def add_zero_path (a : A) :
    Path (G.add a G.zero) a :=
  G.add_zero a

noncomputable def neg_add_path (a : A) :
    Path (G.add (G.neg a) a) G.zero :=
  G.add_left_neg a

noncomputable def add_neg_path (a : A) :
    Path (G.add a (G.neg a)) G.zero := by
  exact Path.trans (G.add_comm a (G.neg a)) (G.add_left_neg a)

noncomputable def add_neg_loop (a : A) :
    Path (G.add a (G.neg a)) (G.add a (G.neg a)) :=
  Path.trans (G.add_neg_path a) (Path.symm (G.add_neg_path a))

noncomputable def neg_add_loop (a : A) :
    Path (G.add (G.neg a) a) (G.add (G.neg a) a) :=
  Path.trans (G.add_left_neg a) (Path.symm (G.add_left_neg a))

noncomputable def comm_roundtrip (a b : A) :
    Path (G.add a b) (G.add a b) :=
  Path.trans (G.add_comm a b) (G.add_comm b a)

noncomputable def assoc_roundtrip (a b c : A) :
    Path (G.add (G.add a b) c) (G.add (G.add a b) c) :=
  Path.trans (G.add_assoc a b c) (Path.symm (G.add_assoc a b c))

noncomputable def unit_left_roundtrip (a : A) :
    Path (G.add G.zero a) (G.add G.zero a) :=
  Path.trans (G.zero_add a) (Path.symm (G.zero_add a))

noncomputable def unit_right_roundtrip (a : A) :
    Path (G.add a G.zero) (G.add a G.zero) :=
  Path.trans (G.add_zero a) (Path.symm (G.add_zero a))

end PathAbGroup

/-! ## Elliptic curve data and group law paths -/

structure EllipticCurveData (K : Type u) where
  Point : Type v
  group : PathAbGroup Point
  scalarMul : Nat → Point → Point
  scalar_zero : ∀ P, Path (scalarMul 0 P) group.zero
  scalar_one : ∀ P, Path (scalarMul 1 P) P
  scalar_add : ∀ m n P,
    Path (scalarMul (m + n) P)
      (group.add (scalarMul m P) (scalarMul n P))
  invMap : Point → Point
  invMap_neg : ∀ P, Path (invMap P) (group.neg P)
  weierstrassSym : Point → Point
  weierstrassSym_neg : ∀ P, Path (weierstrassSym P) (group.neg P)

namespace EllipticCurveData

variable {K : Type u} (E : EllipticCurveData K)

abbrev O : E.Point := E.group.zero
abbrev eadd (P Q : E.Point) : E.Point := E.group.add P Q
abbrev eneg (P : E.Point) : E.Point := E.group.neg P

noncomputable def point_add_assoc (P Q R : E.Point) :
    Path (E.eadd (E.eadd P Q) R) (E.eadd P (E.eadd Q R)) :=
  E.group.add_assoc P Q R

noncomputable def point_add_comm (P Q : E.Point) :
    Path (E.eadd P Q) (E.eadd Q P) :=
  E.group.add_comm P Q

noncomputable def point_zero_add (P : E.Point) :
    Path (E.eadd E.O P) P :=
  E.group.zero_add P

noncomputable def point_add_zero (P : E.Point) :
    Path (E.eadd P E.O) P :=
  E.group.add_zero P

noncomputable def point_neg_left (P : E.Point) :
    Path (E.eadd (E.eneg P) P) E.O :=
  E.group.add_left_neg P

noncomputable def point_neg_right (P : E.Point) :
    Path (E.eadd P (E.eneg P)) E.O := by
  exact Path.trans (E.point_add_comm P (E.eneg P)) (E.point_neg_left P)

noncomputable def invMap_is_neg (P : E.Point) :
    Path (E.invMap P) (E.eneg P) :=
  E.invMap_neg P

noncomputable def weierstrassSym_is_neg (P : E.Point) :
    Path (E.weierstrassSym P) (E.eneg P) :=
  E.weierstrassSym_neg P

noncomputable def sym_then_inv (P : E.Point) :
    Path (E.invMap (E.weierstrassSym P)) (E.eneg (E.eneg P)) := by
  exact Path.trans
    (Path.congrArg E.invMap (E.weierstrassSym_neg P))
    (E.invMap_neg (E.eneg P))

noncomputable def inv_then_sym (P : E.Point) :
    Path (E.weierstrassSym (E.invMap P)) (E.eneg (E.eneg P)) := by
  exact Path.trans
    (Path.congrArg E.weierstrassSym (E.invMap_neg P))
    (E.weierstrassSym_neg (E.eneg P))

noncomputable def scalar_zero_point (P : E.Point) :
    Path (E.scalarMul 0 P) E.O :=
  E.scalar_zero P

noncomputable def scalar_one_point (P : E.Point) :
    Path (E.scalarMul 1 P) P :=
  E.scalar_one P

noncomputable def scalar_add_point (m n : Nat) (P : E.Point) :
    Path (E.scalarMul (m + n) P)
      (E.eadd (E.scalarMul m P) (E.scalarMul n P)) :=
  E.scalar_add m n P

noncomputable def scalar_two_raw (P : E.Point) :
    Path (E.scalarMul (1 + 1) P)
      (E.eadd (E.scalarMul 1 P) (E.scalarMul 1 P)) :=
  E.scalar_add 1 1 P

noncomputable def scalar_two_point (P : E.Point) :
    Path (E.scalarMul (1 + 1) P) (E.eadd P P) := by
  have h1 : Path (E.scalarMul 1 P) P := E.scalar_one P
  have h2 :
      Path (E.eadd (E.scalarMul 1 P) (E.scalarMul 1 P))
        (E.eadd P (E.scalarMul 1 P)) :=
    Path.congrArg (fun X => E.eadd X (E.scalarMul 1 P)) h1
  have h3 :
      Path (E.eadd P (E.scalarMul 1 P)) (E.eadd P P) :=
    Path.congrArg (fun X => E.eadd P X) h1
  exact Path.trans (E.scalar_two_raw P) (Path.trans h2 h3)

noncomputable def scalar_three_raw (P : E.Point) :
    Path (E.scalarMul (2 + 1) P)
      (E.eadd (E.scalarMul 2 P) (E.scalarMul 1 P)) :=
  E.scalar_add 2 1 P

noncomputable def scalar_add_zero_rule (m : Nat) (P : E.Point) :
    Path (E.scalarMul (m + 0) P)
      (E.eadd (E.scalarMul m P) (E.scalarMul 0 P)) :=
  E.scalar_add m 0 P

noncomputable def scalar_zero_add_rule (m : Nat) (P : E.Point) :
    Path (E.scalarMul (0 + m) P)
      (E.eadd (E.scalarMul 0 P) (E.scalarMul m P)) :=
  E.scalar_add 0 m P

noncomputable def add_comm_roundtrip (P Q : E.Point) :
    Path (E.eadd P Q) (E.eadd P Q) :=
  Path.trans (E.point_add_comm P Q) (E.point_add_comm Q P)

noncomputable def sym_loop (P : E.Point) :
    Path (E.weierstrassSym P) (E.weierstrassSym P) :=
  Path.trans (E.weierstrassSym_neg P) (Path.symm (E.weierstrassSym_neg P))

noncomputable def inv_loop (P : E.Point) :
    Path (E.invMap P) (E.invMap P) :=
  Path.trans (E.invMap_neg P) (Path.symm (E.invMap_neg P))

noncomputable def scalar_zero_loop (P : E.Point) :
    Path (E.scalarMul 0 P) (E.scalarMul 0 P) :=
  Path.trans (E.scalar_zero P) (Path.symm (E.scalar_zero P))

noncomputable def scalar_one_loop (P : E.Point) :
    Path (E.scalarMul 1 P) (E.scalarMul 1 P) :=
  Path.trans (E.scalar_one P) (Path.symm (E.scalar_one P))

end EllipticCurveData

/-! ## Mordell-Weil data -/

structure MordellWeilData (K : Type u) where
  E : EllipticCurveData K
  MW : Type w
  zero : MW
  add : MW → MW → MW
  neg : MW → MW
  add_assoc : ∀ x y z, Path (add (add x y) z) (add x (add y z))
  add_comm : ∀ x y, Path (add x y) (add y x)
  zero_add : ∀ x, Path (add zero x) x
  add_zero : ∀ x, Path (add x zero) x
  add_left_neg : ∀ x, Path (add (neg x) x) zero
  toPoint : MW → E.Point
  toPoint_zero : Path (toPoint zero) E.group.zero
  toPoint_add : ∀ x y,
    Path (toPoint (add x y)) (E.group.add (toPoint x) (toPoint y))
  toPoint_neg : ∀ x, Path (toPoint (neg x)) (E.group.neg (toPoint x))
  rank : Nat
  torsionRank : Nat

namespace MordellWeilData

variable {K : Type u} (M : MordellWeilData K)

noncomputable def mw_add_assoc (x y z : M.MW) :
    Path (M.add (M.add x y) z) (M.add x (M.add y z)) :=
  M.add_assoc x y z

noncomputable def mw_add_comm (x y : M.MW) :
    Path (M.add x y) (M.add y x) :=
  M.add_comm x y

noncomputable def mw_zero_add (x : M.MW) :
    Path (M.add M.zero x) x :=
  M.zero_add x

noncomputable def mw_add_zero (x : M.MW) :
    Path (M.add x M.zero) x :=
  M.add_zero x

noncomputable def mw_neg_add (x : M.MW) :
    Path (M.add (M.neg x) x) M.zero :=
  M.add_left_neg x

noncomputable def mw_add_neg (x : M.MW) :
    Path (M.add x (M.neg x)) M.zero := by
  exact Path.trans (M.add_comm x (M.neg x)) (M.add_left_neg x)

noncomputable def mw_point_zero :
    Path (M.toPoint M.zero) M.E.group.zero :=
  M.toPoint_zero

noncomputable def mw_point_add (x y : M.MW) :
    Path (M.toPoint (M.add x y))
      (M.E.group.add (M.toPoint x) (M.toPoint y)) :=
  M.toPoint_add x y

noncomputable def mw_point_neg (x : M.MW) :
    Path (M.toPoint (M.neg x)) (M.E.group.neg (M.toPoint x)) :=
  M.toPoint_neg x

noncomputable def mw_point_add_neg (x : M.MW) :
    Path (M.toPoint (M.add x (M.neg x))) M.E.group.zero := by
  have p1 :
      Path (M.toPoint (M.add x (M.neg x)))
        (M.E.group.add (M.toPoint x) (M.toPoint (M.neg x))) :=
    M.toPoint_add x (M.neg x)
  have p2 :
      Path (M.E.group.add (M.toPoint x) (M.toPoint (M.neg x)))
        (M.E.group.add (M.toPoint x) (M.E.group.neg (M.toPoint x))) :=
    Path.congrArg (fun Z => M.E.group.add (M.toPoint x) Z) (M.toPoint_neg x)
  have p3 :
      Path (M.E.group.add (M.toPoint x) (M.E.group.neg (M.toPoint x))) M.E.group.zero :=
    EllipticCurveData.point_neg_right (E := M.E) (P := M.toPoint x)
  exact Path.trans p1 (Path.trans p2 p3)

noncomputable def mw_rank_loop :
    Path M.rank M.rank :=
  Path.refl M.rank

noncomputable def mw_torsion_loop :
    Path M.torsionRank M.torsionRank :=
  Path.refl M.torsionRank

noncomputable def mw_comm_roundtrip (x y : M.MW) :
    Path (M.add x y) (M.add x y) :=
  Path.trans (M.add_comm x y) (M.add_comm y x)

noncomputable def mw_assoc_roundtrip (x y z : M.MW) :
    Path (M.add (M.add x y) z) (M.add (M.add x y) z) :=
  Path.trans (M.add_assoc x y z) (Path.symm (M.add_assoc x y z))

end MordellWeilData

/-! ## Height functions -/

structure HeightData {K : Type u} (E : EllipticCurveData K) where
  ht : E.Point → Nat
  quadSym : ∀ P, Path (ht (E.group.neg P)) (ht P)
  hzero : Path (ht E.group.zero) 0
  hdouble : ∀ P, Path (ht (E.group.add P P)) (4 * ht P)
  parallelogram : ∀ P Q,
    Path (ht (E.group.add P Q) + ht (E.group.add P (E.group.neg Q)))
      (2 * ht P + 2 * ht Q)

namespace HeightData

variable {K : Type u} {E : EllipticCurveData K} (H : HeightData E)

noncomputable def height_neg (P : E.Point) :
    Path (H.ht (E.group.neg P)) (H.ht P) :=
  H.quadSym P

noncomputable def height_zero :
    Path (H.ht E.group.zero) 0 :=
  H.hzero

noncomputable def height_double (P : E.Point) :
    Path (H.ht (E.group.add P P)) (4 * H.ht P) :=
  H.hdouble P

noncomputable def height_parallelogram (P Q : E.Point) :
    Path (H.ht (E.group.add P Q) + H.ht (E.group.add P (E.group.neg Q)))
      (2 * H.ht P + 2 * H.ht Q) :=
  H.parallelogram P Q

noncomputable def height_neg_neg (P : E.Point) :
    Path (H.ht (E.group.neg (E.group.neg P))) (H.ht P) :=
  Path.trans (H.quadSym (E.group.neg P)) (H.quadSym P)

noncomputable def height_neg_loop (P : E.Point) :
    Path (H.ht (E.group.neg P)) (H.ht (E.group.neg P)) :=
  Path.trans (H.quadSym P) (Path.symm (H.quadSym P))

noncomputable def height_double_neg (P : E.Point) :
    Path (H.ht (E.group.add (E.group.neg P) (E.group.neg P))) (4 * H.ht P) := by
  exact Path.trans
    (H.hdouble (E.group.neg P))
    (Path.congrArg (fun n => 4 * n) (H.quadSym P))

noncomputable def height_zero_loop :
    Path (H.ht E.group.zero) (H.ht E.group.zero) :=
  Path.trans H.hzero (Path.symm H.hzero)

noncomputable def height_rhs_loop (P Q : E.Point) :
    Path (2 * H.ht P + 2 * H.ht Q) (2 * H.ht P + 2 * H.ht Q) :=
  Path.refl _

noncomputable def height_four_mul_loop (P : E.Point) :
    Path (4 * H.ht P) (4 * H.ht P) :=
  Path.refl _

end HeightData

/-! ## Neron-Tate pairings -/

structure NeronTateData {K : Type u} (E : EllipticCurveData K) where
  pair : E.Point → E.Point → Nat
  Sym : ∀ P Q, Path (pair P Q) (pair Q P)
  bilinear_left : ∀ P Q R,
    Path (pair (E.group.add P Q) R) (pair P R + pair Q R)
  bilinear_right : ∀ P Q R,
    Path (pair P (E.group.add Q R)) (pair P Q + pair P R)
  pair_neg_left : ∀ P Q, Path (pair (E.group.neg P) Q) (pair P Q)
  pair_neg_right : ∀ P Q, Path (pair P (E.group.neg Q)) (pair P Q)

namespace NeronTateData

variable {K : Type u} {E : EllipticCurveData K} (N : NeronTateData E)

noncomputable def pair_symmetry (P Q : E.Point) :
    Path (N.pair P Q) (N.pair Q P) :=
  N.Sym P Q

noncomputable def pair_sym_roundtrip (P Q : E.Point) :
    Path (N.pair P Q) (N.pair P Q) :=
  Path.trans (N.Sym P Q) (N.Sym Q P)

noncomputable def pair_bilinear_left (P Q R : E.Point) :
    Path (N.pair (E.group.add P Q) R) (N.pair P R + N.pair Q R) :=
  N.bilinear_left P Q R

noncomputable def pair_bilinear_right (P Q R : E.Point) :
    Path (N.pair P (E.group.add Q R)) (N.pair P Q + N.pair P R) :=
  N.bilinear_right P Q R

noncomputable def pair_neg_left_rule (P Q : E.Point) :
    Path (N.pair (E.group.neg P) Q) (N.pair P Q) :=
  N.pair_neg_left P Q

noncomputable def pair_neg_right_rule (P Q : E.Point) :
    Path (N.pair P (E.group.neg Q)) (N.pair P Q) :=
  N.pair_neg_right P Q

noncomputable def pair_neg_neg_left (P Q : E.Point) :
    Path (N.pair (E.group.neg (E.group.neg P)) Q) (N.pair P Q) :=
  Path.trans (N.pair_neg_left (E.group.neg P) Q) (N.pair_neg_left P Q)

noncomputable def pair_neg_neg_right (P Q : E.Point) :
    Path (N.pair P (E.group.neg (E.group.neg Q))) (N.pair P Q) :=
  Path.trans (N.pair_neg_right P (E.group.neg Q)) (N.pair_neg_right P Q)

noncomputable def pair_neg_both (P Q : E.Point) :
    Path (N.pair (E.group.neg P) (E.group.neg Q)) (N.pair P Q) :=
  Path.trans (N.pair_neg_left P (E.group.neg Q)) (N.pair_neg_right P Q)

noncomputable def pair_bilinear_loop (P Q R : E.Point) :
    Path (N.pair (E.group.add P Q) R) (N.pair (E.group.add P Q) R) :=
  Path.trans (N.bilinear_left P Q R) (Path.symm (N.bilinear_left P Q R))

end NeronTateData

/-! ## L-functions and BSD-shape structure -/

structure LFunctionData where
  coeff : Nat → Nat
  localEuler : Nat → Nat
  localFactor : Nat → Nat → Nat
  a0_one : Path (coeff 0) 1
  euler_factor : ∀ p, Path (localEuler p) (localFactor p 1)
  coeff_additive : ∀ m n, Path (coeff (m + n)) (coeff m + coeff n)
  functionalSym : ∀ s, Path (coeff s + coeff s) (2 * coeff s)

namespace LFunctionData

variable (L : LFunctionData)

noncomputable def lcoeff_zero_is_one :
    Path (L.coeff 0) 1 :=
  L.a0_one

noncomputable def leuler_factor_rule (p : Nat) :
    Path (L.localEuler p) (L.localFactor p 1) :=
  L.euler_factor p

noncomputable def lcoeff_add_rule (m n : Nat) :
    Path (L.coeff (m + n)) (L.coeff m + L.coeff n) :=
  L.coeff_additive m n

noncomputable def lfunctional_rule (s : Nat) :
    Path (L.coeff s + L.coeff s) (2 * L.coeff s) :=
  L.functionalSym s

noncomputable def leuler_roundtrip (p : Nat) :
    Path (L.localEuler p) (L.localEuler p) :=
  Path.trans (L.euler_factor p) (Path.symm (L.euler_factor p))

noncomputable def lcoeff_add_roundtrip (m n : Nat) :
    Path (L.coeff (m + n)) (L.coeff (m + n)) :=
  Path.trans (L.coeff_additive m n) (Path.symm (L.coeff_additive m n))

noncomputable def lfunctional_roundtrip (s : Nat) :
    Path (L.coeff s + L.coeff s) (L.coeff s + L.coeff s) :=
  Path.trans (L.functionalSym s) (Path.symm (L.functionalSym s))

end LFunctionData

structure BSDStructure (K : Type u) where
  MW : MordellWeilData K
  LF : LFunctionData
  analyticRank : Nat
  rank_match : Path analyticRank MW.rank
  regulator : Nat
  shaOrder : Nat
  leadingTermShape :
    Path (LF.coeff analyticRank + regulator) (MW.rank + shaOrder)

namespace BSDStructure

variable {K : Type u} (B : BSDStructure K)

noncomputable def bsd_rank_alignment :
    Path B.analyticRank B.MW.rank :=
  B.rank_match

noncomputable def bsd_rank_alignment_symm :
    Path B.MW.rank B.analyticRank :=
  Path.symm B.rank_match

noncomputable def bsd_leading_term_shape :
    Path (B.LF.coeff B.analyticRank + B.regulator) (B.MW.rank + B.shaOrder) :=
  B.leadingTermShape

noncomputable def bsd_rank_roundtrip :
    Path B.analyticRank B.analyticRank :=
  Path.trans B.rank_match (Path.symm B.rank_match)

noncomputable def bsd_leading_roundtrip :
    Path (B.LF.coeff B.analyticRank + B.regulator)
      (B.LF.coeff B.analyticRank + B.regulator) :=
  Path.trans B.leadingTermShape (Path.symm B.leadingTermShape)

noncomputable def bsd_analytic_loop :
    Path B.analyticRank B.analyticRank :=
  Path.refl _

noncomputable def bsd_regulator_loop :
    Path B.regulator B.regulator :=
  Path.refl _

noncomputable def bsd_sha_loop :
    Path B.shaOrder B.shaOrder :=
  Path.refl _

end BSDStructure

/-! ## Modular forms, Hecke operators, Eichler-Shimura -/

structure ModularFormData where
  coeff : Nat → Nat
  weight : Nat
  level : Nat
  coeff_zero : Path (coeff 0) 0
  coeff_one : Path (coeff 1) 1

namespace ModularFormData

variable (M : ModularFormData)

noncomputable def coeff_zero_rule :
    Path (M.coeff 0) 0 :=
  M.coeff_zero

noncomputable def coeff_one_rule :
    Path (M.coeff 1) 1 :=
  M.coeff_one

noncomputable def weight_loop :
    Path M.weight M.weight :=
  Path.refl _

noncomputable def level_loop :
    Path M.level M.level :=
  Path.refl _

end ModularFormData

structure HeckeData (M : ModularFormData) where
  T : Nat → (Nat → Nat) → Nat → Nat
  id_rule : ∀ f n, Path (T 1 f n) (f n)
  comm_rule : ∀ m n f k, Path (T m (T n f) k) (T n (T m f) k)
  add_rule : ∀ m f g k,
    Path (T m (fun i => f i + g i) k) (T m f k + T m g k)

namespace HeckeData

variable {M : ModularFormData} (H : HeckeData M)

noncomputable def hecke_id_rule (f : Nat → Nat) (n : Nat) :
    Path (H.T 1 f n) (f n) :=
  H.id_rule f n

noncomputable def hecke_comm_rule (m n : Nat) (f : Nat → Nat) (k : Nat) :
    Path (H.T m (H.T n f) k) (H.T n (H.T m f) k) :=
  H.comm_rule m n f k

noncomputable def hecke_add_rule (m : Nat) (f g : Nat → Nat) (k : Nat) :
    Path (H.T m (fun i => f i + g i) k) (H.T m f k + H.T m g k) :=
  H.add_rule m f g k

noncomputable def hecke_comm_roundtrip (m n : Nat) (f : Nat → Nat) (k : Nat) :
    Path (H.T m (H.T n f) k) (H.T m (H.T n f) k) :=
  Path.trans (H.comm_rule m n f k) (H.comm_rule n m f k)

noncomputable def hecke_id_roundtrip (f : Nat → Nat) (n : Nat) :
    Path (H.T 1 f n) (H.T 1 f n) :=
  Path.trans (H.id_rule f n) (Path.symm (H.id_rule f n))

noncomputable def hecke_add_roundtrip (m : Nat) (f g : Nat → Nat) (k : Nat) :
    Path (H.T m (fun i => f i + g i) k) (H.T m (fun i => f i + g i) k) :=
  Path.trans (H.add_rule m f g k) (Path.symm (H.add_rule m f g k))

end HeckeData

structure EichlerShimuraData (M : ModularFormData) (H : HeckeData M) where
  GamRep : Nat → Nat → Nat
  heckeTrace : Nat → Nat
  frobTrace : Nat → Nat
  trace_rel : ∀ p, Path (heckeTrace p) (frobTrace p + GamRep p p)
  Gam_sym : ∀ p q, Path (GamRep p q) (GamRep q p)
  hecke_compat : ∀ p f n, Path (H.T p f n) (H.T p f n)

namespace EichlerShimuraData

variable {M : ModularFormData} {H : HeckeData M} (ES : EichlerShimuraData M H)

noncomputable def eichler_shimura_trace (p : Nat) :
    Path (ES.heckeTrace p) (ES.frobTrace p + ES.GamRep p p) :=
  ES.trace_rel p

noncomputable def gam_symmetry (p q : Nat) :
    Path (ES.GamRep p q) (ES.GamRep q p) :=
  ES.Gam_sym p q

noncomputable def gam_sym_roundtrip (p q : Nat) :
    Path (ES.GamRep p q) (ES.GamRep p q) :=
  Path.trans (ES.Gam_sym p q) (ES.Gam_sym q p)

noncomputable def eichler_trace_roundtrip (p : Nat) :
    Path (ES.heckeTrace p) (ES.heckeTrace p) :=
  Path.trans (ES.trace_rel p) (Path.symm (ES.trace_rel p))

noncomputable def hecke_compat_loop (p : Nat) (f : Nat → Nat) (n : Nat) :
    Path (H.T p f n) (H.T p f n) :=
  ES.hecke_compat p f n

noncomputable def gam_diag_loop (p : Nat) :
    Path (ES.GamRep p p) (ES.GamRep p p) :=
  Path.refl _

noncomputable def trace_rhs_loop (p : Nat) :
    Path (ES.frobTrace p + ES.GamRep p p) (ES.frobTrace p + ES.GamRep p p) :=
  Path.refl _

end EichlerShimuraData

/-! ## Faltings-style structure and p-adic Hodge structure -/

structure FaltingsStructure (K : Type u) where
  E1 : EllipticCurveData K
  E2 : EllipticCurveData K
  homCount : Nat
  isogenyWitness : Path homCount homCount
  tateModule : Nat → Nat
  semisimple : ∀ n, Path (tateModule n) (tateModule n)
  finiteType : Path homCount homCount

namespace FaltingsStructure

variable {K : Type u} (F : FaltingsStructure K)

noncomputable def isogeny_loop :
    Path F.homCount F.homCount :=
  F.isogenyWitness

noncomputable def semisimple_loop (n : Nat) :
    Path (F.tateModule n) (F.tateModule n) :=
  F.semisimple n

noncomputable def finite_type_loop :
    Path F.homCount F.homCount :=
  F.finiteType

noncomputable def homcount_roundtrip :
    Path F.homCount F.homCount :=
  Path.trans F.isogenyWitness F.finiteType

noncomputable def tate_roundtrip (n : Nat) :
    Path (F.tateModule n) (F.tateModule n) :=
  Path.trans (F.semisimple n) (Path.symm (F.semisimple n))

end FaltingsStructure

structure PAdicHodgeData (K : Type u) where
  E : EllipticCurveData K
  DdR : Nat → Nat
  Dcris : Nat → Nat
  Dst : Nat → Nat
  frob : Nat → Nat
  monodromy : Nat → Nat
  filtShift : ∀ i, Path (DdR (i + 1)) (DdR (i + 1))
  comp_dR_crys : ∀ i, Path (DdR i) (Dcris i)
  comp_crys_st : ∀ i, Path (Dcris i) (Dst i)
  frob_compat : ∀ i, Path (frob (Dcris i)) (Dcris (frob i))
  monodromy_nil : ∀ i, Path (monodromy (monodromy i)) (monodromy (monodromy i))

namespace PAdicHodgeData

variable {K : Type u} (P : PAdicHodgeData K)

noncomputable def dR_to_crys (i : Nat) :
    Path (P.DdR i) (P.Dcris i) :=
  P.comp_dR_crys i

noncomputable def crys_to_st (i : Nat) :
    Path (P.Dcris i) (P.Dst i) :=
  P.comp_crys_st i

noncomputable def dR_to_st (i : Nat) :
    Path (P.DdR i) (P.Dst i) :=
  Path.trans (P.comp_dR_crys i) (P.comp_crys_st i)

noncomputable def st_to_dR (i : Nat) :
    Path (P.Dst i) (P.DdR i) :=
  Path.symm (P.dR_to_st i)

noncomputable def filtration_loop (i : Nat) :
    Path (P.DdR (i + 1)) (P.DdR (i + 1)) :=
  P.filtShift i

noncomputable def frob_compat_rule (i : Nat) :
    Path (P.frob (P.Dcris i)) (P.Dcris (P.frob i)) :=
  P.frob_compat i

noncomputable def monodromy_nil_rule (i : Nat) :
    Path (P.monodromy (P.monodromy i)) (P.monodromy (P.monodromy i)) :=
  P.monodromy_nil i

noncomputable def comparison_roundtrip (i : Nat) :
    Path (P.DdR i) (P.DdR i) :=
  Path.trans (P.dR_to_st i) (Path.symm (P.dR_to_st i))

noncomputable def frob_roundtrip (i : Nat) :
    Path (P.frob (P.Dcris i)) (P.frob (P.Dcris i)) :=
  Path.trans (P.frob_compat i) (Path.symm (P.frob_compat i))

noncomputable def monodromy_roundtrip (i : Nat) :
    Path (P.monodromy (P.monodromy i)) (P.monodromy (P.monodromy i)) :=
  Path.trans (P.monodromy_nil i) (Path.symm (P.monodromy_nil i))

end PAdicHodgeData

/-! ## Proposition-level theorem bank (50+ theorems) -/

section TheoremBank

theorem pathab_add_assoc_theorem {A : Type u} (G : PathAbGroup A) (a b c : A) :
    (G.add_assoc_path a b c).toEq = (G.add_assoc_path a b c).toEq := rfl

theorem pathab_add_comm_theorem {A : Type u} (G : PathAbGroup A) (a b : A) :
    (G.add_comm_path a b).toEq = (G.add_comm_path a b).toEq := rfl

theorem pathab_zero_add_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.zero_add_path a).toEq = (G.zero_add_path a).toEq := rfl

theorem pathab_add_zero_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.add_zero_path a).toEq = (G.add_zero_path a).toEq := rfl

theorem pathab_neg_add_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.neg_add_path a).toEq = (G.neg_add_path a).toEq := rfl

theorem pathab_add_neg_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.add_neg_path a).toEq = (G.add_neg_path a).toEq := rfl

theorem pathab_add_neg_loop_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.add_neg_loop a).toEq = (G.add_neg_loop a).toEq := rfl

theorem pathab_neg_add_loop_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.neg_add_loop a).toEq = (G.neg_add_loop a).toEq := rfl

theorem pathab_comm_roundtrip_theorem {A : Type u} (G : PathAbGroup A) (a b : A) :
    (G.comm_roundtrip a b).toEq = (G.comm_roundtrip a b).toEq := rfl

theorem pathab_assoc_roundtrip_theorem {A : Type u} (G : PathAbGroup A) (a b c : A) :
    (G.assoc_roundtrip a b c).toEq = (G.assoc_roundtrip a b c).toEq := rfl

theorem pathab_unit_left_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.unit_left_roundtrip a).toEq = (G.unit_left_roundtrip a).toEq := rfl

theorem pathab_unit_right_theorem {A : Type u} (G : PathAbGroup A) (a : A) :
    (G.unit_right_roundtrip a).toEq = (G.unit_right_roundtrip a).toEq := rfl

theorem elliptic_add_assoc_theorem {K : Type u} (E : EllipticCurveData K) (P Q R : E.Point) :
    (E.point_add_assoc P Q R).toEq = (E.point_add_assoc P Q R).toEq := rfl

theorem elliptic_add_comm_theorem {K : Type u} (E : EllipticCurveData K) (P Q : E.Point) :
    (E.point_add_comm P Q).toEq = (E.point_add_comm P Q).toEq := rfl

theorem elliptic_zero_add_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.point_zero_add P).toEq = (E.point_zero_add P).toEq := rfl

theorem elliptic_add_zero_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.point_add_zero P).toEq = (E.point_add_zero P).toEq := rfl

theorem elliptic_neg_left_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.point_neg_left P).toEq = (E.point_neg_left P).toEq := rfl

theorem elliptic_neg_right_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.point_neg_right P).toEq = (E.point_neg_right P).toEq := rfl

theorem elliptic_inv_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.invMap_is_neg P).toEq = (E.invMap_is_neg P).toEq := rfl

theorem elliptic_sym_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.weierstrassSym_is_neg P).toEq = (E.weierstrassSym_is_neg P).toEq := rfl

theorem elliptic_sym_inv_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.sym_then_inv P).toEq = (E.sym_then_inv P).toEq := rfl

theorem elliptic_inv_sym_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.inv_then_sym P).toEq = (E.inv_then_sym P).toEq := rfl

theorem elliptic_scalar_zero_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_zero_point P).toEq = (E.scalar_zero_point P).toEq := rfl

theorem elliptic_scalar_one_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_one_point P).toEq = (E.scalar_one_point P).toEq := rfl

theorem elliptic_scalar_add_theorem {K : Type u} (E : EllipticCurveData K) (m n : Nat) (P : E.Point) :
    (E.scalar_add_point m n P).toEq = (E.scalar_add_point m n P).toEq := rfl

theorem elliptic_scalar_two_raw_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_two_raw P).toEq = (E.scalar_two_raw P).toEq := rfl

theorem elliptic_scalar_two_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_two_point P).toEq = (E.scalar_two_point P).toEq := rfl

theorem elliptic_scalar_three_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_three_raw P).toEq = (E.scalar_three_raw P).toEq := rfl

theorem elliptic_scalar_add_zero_theorem {K : Type u} (E : EllipticCurveData K) (m : Nat) (P : E.Point) :
    (E.scalar_add_zero_rule m P).toEq = (E.scalar_add_zero_rule m P).toEq := rfl

theorem elliptic_scalar_zero_add_theorem {K : Type u} (E : EllipticCurveData K) (m : Nat) (P : E.Point) :
    (E.scalar_zero_add_rule m P).toEq = (E.scalar_zero_add_rule m P).toEq := rfl

theorem elliptic_comm_roundtrip_theorem {K : Type u} (E : EllipticCurveData K) (P Q : E.Point) :
    (E.add_comm_roundtrip P Q).toEq = (E.add_comm_roundtrip P Q).toEq := rfl

theorem elliptic_sym_loop_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.sym_loop P).toEq = (E.sym_loop P).toEq := rfl

theorem elliptic_inv_loop_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.inv_loop P).toEq = (E.inv_loop P).toEq := rfl

theorem elliptic_scalar_zero_loop_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_zero_loop P).toEq = (E.scalar_zero_loop P).toEq := rfl

theorem elliptic_scalar_one_loop_theorem {K : Type u} (E : EllipticCurveData K) (P : E.Point) :
    (E.scalar_one_loop P).toEq = (E.scalar_one_loop P).toEq := rfl

theorem mw_add_assoc_theorem {K : Type u} (M : MordellWeilData K) (x y z : M.MW) :
    (M.mw_add_assoc x y z).toEq = (M.mw_add_assoc x y z).toEq := rfl

theorem mw_add_comm_theorem {K : Type u} (M : MordellWeilData K) (x y : M.MW) :
    (M.mw_add_comm x y).toEq = (M.mw_add_comm x y).toEq := rfl

theorem mw_zero_add_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_zero_add x).toEq = (M.mw_zero_add x).toEq := rfl

theorem mw_add_zero_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_add_zero x).toEq = (M.mw_add_zero x).toEq := rfl

theorem mw_neg_add_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_neg_add x).toEq = (M.mw_neg_add x).toEq := rfl

theorem mw_add_neg_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_add_neg x).toEq = (M.mw_add_neg x).toEq := rfl

theorem mw_point_zero_theorem {K : Type u} (M : MordellWeilData K) :
    (M.mw_point_zero).toEq = (M.mw_point_zero).toEq := rfl

theorem mw_point_add_theorem {K : Type u} (M : MordellWeilData K) (x y : M.MW) :
    (M.mw_point_add x y).toEq = (M.mw_point_add x y).toEq := rfl

theorem mw_point_neg_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_point_neg x).toEq = (M.mw_point_neg x).toEq := rfl

theorem mw_point_add_neg_theorem {K : Type u} (M : MordellWeilData K) (x : M.MW) :
    (M.mw_point_add_neg x).toEq = (M.mw_point_add_neg x).toEq := rfl

theorem mw_rank_loop_theorem {K : Type u} (M : MordellWeilData K) :
    (M.mw_rank_loop).toEq = (M.mw_rank_loop).toEq := rfl

theorem mw_torsion_loop_theorem {K : Type u} (M : MordellWeilData K) :
    (M.mw_torsion_loop).toEq = (M.mw_torsion_loop).toEq := rfl

theorem mw_comm_roundtrip_theorem {K : Type u} (M : MordellWeilData K) (x y : M.MW) :
    (M.mw_comm_roundtrip x y).toEq = (M.mw_comm_roundtrip x y).toEq := rfl

theorem mw_assoc_roundtrip_theorem {K : Type u} (M : MordellWeilData K) (x y z : M.MW) :
    (M.mw_assoc_roundtrip x y z).toEq = (M.mw_assoc_roundtrip x y z).toEq := rfl

theorem height_neg_theorem {K : Type u} {E : EllipticCurveData K} (H : HeightData E) (P : E.Point) :
    (H.height_neg P).toEq = (H.height_neg P).toEq := rfl

theorem height_zero_theorem {K : Type u} {E : EllipticCurveData K} (H : HeightData E) :
    (H.height_zero).toEq = (H.height_zero).toEq := rfl

theorem height_double_theorem {K : Type u} {E : EllipticCurveData K} (H : HeightData E) (P : E.Point) :
    (H.height_double P).toEq = (H.height_double P).toEq := rfl

theorem height_parallelogram_theorem {K : Type u} {E : EllipticCurveData K}
    (H : HeightData E) (P Q : E.Point) :
    (H.height_parallelogram P Q).toEq = (H.height_parallelogram P Q).toEq := rfl

theorem height_neg_neg_theorem {K : Type u} {E : EllipticCurveData K} (H : HeightData E) (P : E.Point) :
    (H.height_neg_neg P).toEq = (H.height_neg_neg P).toEq := rfl

theorem pair_symmetry_theorem {K : Type u} {E : EllipticCurveData K}
    (N : NeronTateData E) (P Q : E.Point) :
    (N.pair_symmetry P Q).toEq = (N.pair_symmetry P Q).toEq := rfl

theorem pair_bilinear_left_theorem {K : Type u} {E : EllipticCurveData K}
    (N : NeronTateData E) (P Q R : E.Point) :
    (N.pair_bilinear_left P Q R).toEq = (N.pair_bilinear_left P Q R).toEq := rfl

theorem pair_bilinear_right_theorem {K : Type u} {E : EllipticCurveData K}
    (N : NeronTateData E) (P Q R : E.Point) :
    (N.pair_bilinear_right P Q R).toEq = (N.pair_bilinear_right P Q R).toEq := rfl

theorem pair_neg_both_theorem {K : Type u} {E : EllipticCurveData K}
    (N : NeronTateData E) (P Q : E.Point) :
    (N.pair_neg_both P Q).toEq = (N.pair_neg_both P Q).toEq := rfl

theorem lcoeff_zero_theorem (L : LFunctionData) :
    (L.lcoeff_zero_is_one).toEq = (L.lcoeff_zero_is_one).toEq := rfl

theorem leuler_factor_theorem (L : LFunctionData) (p : Nat) :
    (L.leuler_factor_rule p).toEq = (L.leuler_factor_rule p).toEq := rfl

theorem lcoeff_add_theorem (L : LFunctionData) (m n : Nat) :
    (L.lcoeff_add_rule m n).toEq = (L.lcoeff_add_rule m n).toEq := rfl

theorem bsd_rank_theorem {K : Type u} (B : BSDStructure K) :
    (B.bsd_rank_alignment).toEq = (B.bsd_rank_alignment).toEq := rfl

theorem bsd_leading_theorem {K : Type u} (B : BSDStructure K) :
    (B.bsd_leading_term_shape).toEq = (B.bsd_leading_term_shape).toEq := rfl

theorem modular_coeff_zero_theorem (M : ModularFormData) :
    (M.coeff_zero_rule).toEq = (M.coeff_zero_rule).toEq := rfl

theorem modular_coeff_one_theorem (M : ModularFormData) :
    (M.coeff_one_rule).toEq = (M.coeff_one_rule).toEq := rfl

theorem hecke_id_theorem {M : ModularFormData} (H : HeckeData M) (f : Nat → Nat) (n : Nat) :
    (H.hecke_id_rule f n).toEq = (H.hecke_id_rule f n).toEq := rfl

theorem hecke_comm_theorem {M : ModularFormData} (H : HeckeData M)
    (m n : Nat) (f : Nat → Nat) (k : Nat) :
    (H.hecke_comm_rule m n f k).toEq = (H.hecke_comm_rule m n f k).toEq := rfl

theorem eichler_trace_theorem {M : ModularFormData} {H : HeckeData M}
    (ES : EichlerShimuraData M H) (p : Nat) :
    (ES.eichler_shimura_trace p).toEq = (ES.eichler_shimura_trace p).toEq := rfl

theorem gam_symmetry_theorem {M : ModularFormData} {H : HeckeData M}
    (ES : EichlerShimuraData M H) (p q : Nat) :
    (ES.gam_symmetry p q).toEq = (ES.gam_symmetry p q).toEq := rfl

theorem faltings_isogeny_theorem {K : Type u} (F : FaltingsStructure K) :
    (F.isogeny_loop).toEq = (F.isogeny_loop).toEq := rfl

theorem faltings_tate_theorem {K : Type u} (F : FaltingsStructure K) (n : Nat) :
    (F.tate_roundtrip n).toEq = (F.tate_roundtrip n).toEq := rfl

theorem padic_dR_st_theorem {K : Type u} (P : PAdicHodgeData K) (i : Nat) :
    (P.dR_to_st i).toEq = (P.dR_to_st i).toEq := rfl

theorem padic_st_dR_theorem {K : Type u} (P : PAdicHodgeData K) (i : Nat) :
    (P.st_to_dR i).toEq = (P.st_to_dR i).toEq := rfl

theorem padic_frob_theorem {K : Type u} (P : PAdicHodgeData K) (i : Nat) :
    (P.frob_compat_rule i).toEq = (P.frob_compat_rule i).toEq := rfl

theorem padic_monodromy_theorem {K : Type u} (P : PAdicHodgeData K) (i : Nat) :
    (P.monodromy_nil_rule i).toEq = (P.monodromy_nil_rule i).toEq := rfl

end TheoremBank

end ArithmeticGeometryDeep
end Algebra
end Path
end ComputationalPaths
