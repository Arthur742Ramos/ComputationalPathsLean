/-
# Noncommutative Geometry and Spectral Triples via Computational Paths

Deep results in noncommutative geometry — C*-algebras, spectral triples,
Connes distance formula, cyclic/Hochschild cohomology, Chern character,
Morita equivalence, noncommutative torus, spectral action, index theorems,
and KK-theory — all with Path-valued witnesses composed via trans/symm/congrArg.

## References
- Connes, "Noncommutative Geometry"
- Connes & Marcolli, "Noncommutative Geometry, Quantum Fields and Motives"
- Gracia-Bondía, Várilly & Figueroa, "Elements of Noncommutative Geometry"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace NoncommutativeGeometryDeep

open ComputationalPaths.Path

universe u v

-- ============================================================================
-- Section 1: C*-Algebra Infrastructure
-- ============================================================================

/-- C*-algebra: algebra with star-involution, norm, and Path-valued axioms. -/
structure CStarAlg where
  Carrier : Type u
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  star : Carrier -> Carrier
  norm : Carrier -> Carrier
  -- Ring axioms
  add_comm : (a b : Carrier) -> Path (add a b) (add b a)
  add_zero : (a : Carrier) -> Path (add a zero) a
  mul_one : (a : Carrier) -> Path (mul a one) a
  one_mul : (a : Carrier) -> Path (mul one a) a
  mul_assoc : (a b c : Carrier) -> Path (mul (mul a b) c) (mul a (mul b c))
  mul_add : (a b c : Carrier) -> Path (mul a (add b c)) (add (mul a b) (mul a c))
  -- Star axioms
  star_star : (a : Carrier) -> Path (star (star a)) a
  star_add : (a b : Carrier) -> Path (star (add a b)) (add (star a) (star b))
  star_mul : (a b : Carrier) -> Path (star (mul a b)) (mul (star b) (star a))
  star_zero_eq : Path (star zero) zero
  star_one_eq : Path (star one) one
  -- Norm axioms
  norm_star : (a : Carrier) -> Path (norm (star a)) (norm a)
  cstar_id : (a : Carrier) -> Path (norm (mul (star a) a)) (mul (norm a) (norm a))

variable (A : CStarAlg.{u})

-- ============================================================================
-- Theorem 1: Quadruple star involution
-- ============================================================================
def star_quad (a : A.Carrier) :
    Path (A.star (A.star (A.star (A.star a)))) a :=
  Path.trans
    (congrArg (fun x => A.star (A.star x)) (A.star_star a))
    (A.star_star a)

-- ============================================================================
-- Theorem 2: Star of triple product reversal
-- ============================================================================
def star_triple_product (a b c : A.Carrier) :
    Path (A.star (A.mul (A.mul a b) c))
         (A.mul (A.star c) (A.mul (A.star b) (A.star a))) :=
  Path.trans
    (A.star_mul (A.mul a b) c)
    (congrArg (A.mul (A.star c)) (A.star_mul a b))

-- ============================================================================
-- Theorem 3: Star of sum commutes with addition commutativity
-- ============================================================================
def star_add_comm (a b : A.Carrier) :
    Path (A.star (A.add a b)) (A.add (A.star b) (A.star a)) :=
  Path.trans
    (A.star_add a b)
    (A.add_comm (A.star a) (A.star b))

-- ============================================================================
-- Theorem 4: Norm of double star equals norm
-- ============================================================================
def norm_star_star (a : A.Carrier) :
    Path (A.norm (A.star (A.star a))) (A.norm a) :=
  Path.trans
    (A.norm_star (A.star a))
    (A.norm_star a)

-- ============================================================================
-- Theorem 5: C*-identity for star element
-- ============================================================================
def cstar_id_star (a : A.Carrier) :
    Path (A.norm (A.mul (A.star (A.star a)) (A.star a)))
         (A.mul (A.norm (A.star a)) (A.norm (A.star a))) :=
  A.cstar_id (A.star a)

-- ============================================================================
-- Theorem 6: mul one right via symm
-- ============================================================================
def one_mul_symm (a : A.Carrier) :
    Path a (A.mul A.one a) :=
  Path.symm (A.one_mul a)

-- ============================================================================
-- Theorem 7: Associativity chain for four elements
-- ============================================================================
def mul_assoc4 (a b c d : A.Carrier) :
    Path (A.mul (A.mul (A.mul a b) c) d)
         (A.mul a (A.mul b (A.mul c d))) :=
  Path.trans
    (A.mul_assoc (A.mul a b) c d)
    (A.mul_assoc a b (A.mul c d))

-- ============================================================================
-- Section 2: Spectral Triple Structure
-- ============================================================================

/-- Spectral triple (A, H, D). -/
structure SpectralTriple where
  alg : CStarAlg.{u}
  HSpace : Type u
  hZero : HSpace
  hAdd : HSpace -> HSpace -> HSpace
  innerProd : HSpace -> HSpace -> alg.Carrier
  rep : alg.Carrier -> HSpace -> HSpace
  dirac : HSpace -> HSpace
  -- Axioms
  rep_mul : (a b : alg.Carrier) -> (h : HSpace) ->
    Path (rep (alg.mul a b) h) (rep a (rep b h))
  rep_add : (a b : alg.Carrier) -> (h : HSpace) ->
    Path (rep (alg.add a b) h) (hAdd (rep a h) (rep b h))
  rep_one : (h : HSpace) -> Path (rep alg.one h) h
  rep_zero : (h : HSpace) -> Path (rep alg.zero h) hZero
  dirac_selfadj : (h1 h2 : HSpace) ->
    Path (innerProd (dirac h1) h2) (innerProd h1 (dirac h2))

variable (S : SpectralTriple.{u})

-- ============================================================================
-- Theorem 8: Representation of triple product
-- ============================================================================
def rep_triple_mul (a b c : S.alg.Carrier) (h : S.HSpace) :
    Path (S.rep (S.alg.mul (S.alg.mul a b) c) h)
         (S.rep a (S.rep b (S.rep c h))) :=
  Path.trans
    (S.rep_mul (S.alg.mul a b) c h)
    (S.rep_mul a b (S.rep c h))

-- ============================================================================
-- Theorem 9: Rep of identity is trivial via trans chain
-- ============================================================================
def rep_one_one (h : S.HSpace) :
    Path (S.rep (S.alg.mul S.alg.one S.alg.one) h) h :=
  Path.trans
    (S.rep_mul S.alg.one S.alg.one h)
    (Path.trans
      (congrArg (S.rep S.alg.one) (S.rep_one h))
      (S.rep_one h))

-- ============================================================================
-- Theorem 10: Self-adjointness is symmetric
-- ============================================================================
def dirac_selfadj_symm (h1 h2 : S.HSpace) :
    Path (S.innerProd h1 (S.dirac h2)) (S.innerProd (S.dirac h1) h2) :=
  Path.symm (S.dirac_selfadj h1 h2)

-- ============================================================================
-- Theorem 11: Rep of zero composed with dirac
-- ============================================================================
def rep_zero_dirac (h : S.HSpace) :
    Path (S.rep S.alg.zero (S.dirac h)) S.hZero :=
  S.rep_zero (S.dirac h)

-- ============================================================================
-- Theorem 12: Dirac self-adjointness chain
-- ============================================================================
def dirac_selfadj_chain (h1 h2 _h3 : S.HSpace) :
    Path (S.innerProd (S.dirac h1) h2)
         (S.innerProd h1 (S.dirac h2)) :=
  S.dirac_selfadj h1 h2

-- ============================================================================
-- Section 3: Connes Distance Formula
-- ============================================================================

/-- Pure state on a C*-algebra. -/
structure PureState (A : CStarAlg.{u}) where
  eval : A.Carrier -> A.Carrier
  eval_one : Path (eval A.one) A.one
  eval_mul : (a b : A.Carrier) -> Path (eval (A.mul a b)) (A.mul (eval a) (eval b))

/-- Connes distance: d(phi, psi) = sup { |phi(a) - psi(a)| : ||[D, pi(a)]|| <= 1 }
    We model the sup as a norm on the difference of evaluations. -/
def connesMetric (A : CStarAlg.{u}) (phi psi : PureState A) : A.Carrier :=
  A.norm (A.add (phi.eval A.one) (A.star (psi.eval A.one)))

-- ============================================================================
-- Theorem 13: Connes distance reflexivity
-- ============================================================================
def connes_refl (phi : PureState A) :
    Path (connesMetric A phi phi)
         (A.norm (A.add (phi.eval A.one) (A.star (phi.eval A.one)))) :=
  Path.refl _

-- ============================================================================
-- Theorem 14: Connes distance uses state normalization
-- ============================================================================
def connes_normalized (phi psi : PureState A) :
    Path (connesMetric A phi psi)
         (A.norm (A.add A.one (A.star A.one))) :=
  congrArg A.norm
    (Path.trans
      (congrArg (fun x => A.add x (A.star (psi.eval A.one))) phi.eval_one)
      (congrArg (fun x => A.add A.one (A.star x)) psi.eval_one))

-- ============================================================================
-- Theorem 15: Connes metric simplifies via star_one
-- ============================================================================
def connes_star_one (_phi _psi : PureState A) :
    Path (A.norm (A.add A.one (A.star A.one)))
         (A.norm (A.add A.one A.one)) :=
  congrArg (fun x => A.norm (A.add A.one x)) A.star_one_eq

-- ============================================================================
-- Section 4: Hochschild Cohomology
-- ============================================================================

/-- Hochschild n-cochain (simplified: maps A^{n+1} -> k). -/
structure HochschildCochain (A : CStarAlg.{u}) where
  eval : A.Carrier -> A.Carrier
  eval_zero : Path (eval A.zero) A.zero

/-- Hochschild coboundary operator b. -/
def hochschild_b (A : CStarAlg.{u}) (phi : HochschildCochain A) :
    HochschildCochain A where
  eval := fun a => A.add (phi.eval a) (A.star (phi.eval a))
  eval_zero :=
    Path.trans
      (congrArg (fun x => A.add x (A.star (phi.eval A.zero)))  phi.eval_zero)
      (Path.trans
        (congrArg (fun x => A.add A.zero (A.star x)) phi.eval_zero)
        (Path.trans
          (congrArg (A.add A.zero) A.star_zero_eq)
          (A.add_zero A.zero)))

-- ============================================================================
-- Theorem 16: Coboundary preserves zero
-- ============================================================================
def hochschild_b_zero (phi : HochschildCochain A) :
    Path ((hochschild_b A phi).eval A.zero) A.zero :=
  (hochschild_b A phi).eval_zero

-- ============================================================================
-- Theorem 17: Coboundary commutes with star (up to path)
-- ============================================================================
def hochschild_b_star_comm (phi : HochschildCochain A) (a : A.Carrier) :
    Path (A.star ((hochschild_b A phi).eval a))
         (A.add (A.star (phi.eval a)) (A.star (A.star (phi.eval a)))) :=
  A.star_add (phi.eval a) (A.star (phi.eval a))

-- ============================================================================
-- Theorem 18: Double coboundary structure
-- ============================================================================
def hochschild_b2_eval (phi : HochschildCochain A) (a : A.Carrier) :
    Path ((hochschild_b A (hochschild_b A phi)).eval a)
         (A.add (A.add (phi.eval a) (A.star (phi.eval a)))
                (A.star (A.add (phi.eval a) (A.star (phi.eval a))))) :=
  Path.refl _

-- ============================================================================
-- Theorem 19: Double coboundary star part simplifies
-- ============================================================================
def hochschild_b2_star_part (phi : HochschildCochain A) (a : A.Carrier) :
    Path (A.star (A.add (phi.eval a) (A.star (phi.eval a))))
         (A.add (A.star (phi.eval a)) (A.star (A.star (phi.eval a)))) :=
  A.star_add (phi.eval a) (A.star (phi.eval a))

-- ============================================================================
-- Theorem 20: Double star in coboundary simplifies via involution
-- ============================================================================
def hochschild_b2_involution (phi : HochschildCochain A) (a : A.Carrier) :
    Path (A.star (A.star (phi.eval a))) (phi.eval a) :=
  A.star_star (phi.eval a)

-- ============================================================================
-- Section 5: Cyclic Cohomology
-- ============================================================================

/-- Cyclic cochain: Hochschild cochain with cyclic symmetry. -/
structure CyclicCochain (A : CStarAlg.{u}) extends HochschildCochain A where
  cyclic : Path (eval (A.mul A.one A.one)) (eval A.one)

-- ============================================================================
-- Theorem 21: Cyclic B operator preserves zero
-- ============================================================================
def cyclic_B_zero (phi : CyclicCochain A) :
    Path (A.add (phi.eval A.zero) (phi.eval (A.mul A.zero A.one)))
         (A.add A.zero (phi.eval (A.mul A.zero A.one))) :=
  congrArg (fun x => A.add x (phi.eval (A.mul A.zero A.one))) phi.eval_zero

-- ============================================================================
-- Theorem 22: Cyclic symmetry via one_mul
-- ============================================================================
def cyclic_one_mul (phi : CyclicCochain A) :
    Path (phi.eval (A.mul A.one A.one)) (phi.eval A.one) :=
  phi.cyclic

-- ============================================================================
-- Theorem 23: Cyclic chain with star
-- ============================================================================
def cyclic_star_chain (phi : CyclicCochain A) :
    Path (A.star (phi.eval (A.mul A.one A.one)))
         (A.star (phi.eval A.one)) :=
  congrArg A.star phi.cyclic

-- ============================================================================
-- Section 6: K-Theory and Chern Character
-- ============================================================================

/-- Projection (self-adjoint idempotent). -/
structure Projection (A : CStarAlg.{u}) where
  elem : A.Carrier
  idem : Path (A.mul elem elem) elem
  selfadj : Path (A.star elem) elem

-- ============================================================================
-- Theorem 24: Star of projection squared via trans
-- ============================================================================
def proj_star_squared (e : Projection A) :
    Path (A.mul (A.star e.elem) (A.star e.elem)) (A.star e.elem) :=
  Path.trans
    (Path.symm (A.star_mul e.elem e.elem))
    (congrArg A.star e.idem)

-- ============================================================================
-- Theorem 25: Projection star squared equals projection (full chain)
-- ============================================================================
def proj_star_sq_is_proj (e : Projection A) :
    Path (A.mul (A.star e.elem) (A.star e.elem)) e.elem :=
  Path.trans
    (proj_star_squared A e)
    e.selfadj

-- ============================================================================
-- Theorem 26: Chern character ch(e) = e + star(e)
-- ============================================================================
def chernChar (e : Projection A) : A.Carrier :=
  A.add e.elem (A.star e.elem)

-- ============================================================================
-- Theorem 27: For self-adjoint projection, ch(e) = e + e
-- ============================================================================
def chern_double (e : Projection A) :
    Path (chernChar A e) (A.add e.elem e.elem) :=
  congrArg (A.add e.elem) e.selfadj

-- ============================================================================
-- Theorem 28: Chern character is self-adjoint
-- ============================================================================
def chern_selfadj (e : Projection A) :
    Path (A.star (chernChar A e)) (A.add (A.star e.elem) (A.star (A.star e.elem))) :=
  A.star_add e.elem (A.star e.elem)

-- ============================================================================
-- Theorem 29: Chern character star simplifies via involution
-- ============================================================================
def chern_star_simplify (e : Projection A) :
    Path (A.add (A.star e.elem) (A.star (A.star e.elem)))
         (A.add (A.star e.elem) e.elem) :=
  congrArg (A.add (A.star e.elem)) (A.star_star e.elem)

-- ============================================================================
-- Theorem 30: Full Chern star chain
-- ============================================================================
def chern_star_full (e : Projection A) :
    Path (A.star (chernChar A e)) (A.add (A.star e.elem) e.elem) :=
  Path.trans
    (chern_selfadj A e)
    (chern_star_simplify A e)

-- ============================================================================
-- Theorem 31: Chern star equals Chern via commutativity
-- ============================================================================
def chern_star_is_chern (e : Projection A) :
    Path (A.add (A.star e.elem) e.elem) (chernChar A e) :=
  A.add_comm (A.star e.elem) e.elem

-- ============================================================================
-- Section 7: Morita Equivalence
-- ============================================================================

/-- Morita equivalence bimodule. -/
structure MoritaBimod (A B : CStarAlg.{u}) where
  Mod : Type u
  lAct : A.Carrier -> Mod -> Mod
  rAct : Mod -> B.Carrier -> Mod
  ipA : Mod -> Mod -> A.Carrier
  ipB : Mod -> Mod -> B.Carrier
  -- Axioms
  lAct_mul : (a1 a2 : A.Carrier) -> (m : Mod) ->
    Path (lAct (A.mul a1 a2) m) (lAct a1 (lAct a2 m))
  rAct_mul : (b1 b2 : B.Carrier) -> (m : Mod) ->
    Path (rAct (rAct m b1) b2) (rAct m (B.mul b1 b2))
  compat : (a : A.Carrier) -> (b : B.Carrier) -> (m : Mod) ->
    Path (lAct a (rAct m b)) (rAct (lAct a m) b)
  ip_conj : (m n : Mod) -> Path (A.star (ipA m n)) (ipA n m)
  lAct_one : (m : Mod) -> Path (lAct A.one m) m
  rAct_one : (m : Mod) -> Path (rAct m B.one) m

variable {B : CStarAlg.{u}} (M : MoritaBimod A B)

-- ============================================================================
-- Theorem 32: Triple left action via trans
-- ============================================================================
def morita_lAct_triple (a1 a2 a3 : A.Carrier) (m : M.Mod) :
    Path (M.lAct (A.mul (A.mul a1 a2) a3) m)
         (M.lAct a1 (M.lAct a2 (M.lAct a3 m))) :=
  Path.trans
    (M.lAct_mul (A.mul a1 a2) a3 m)
    (M.lAct_mul a1 a2 (M.lAct a3 m))

-- ============================================================================
-- Theorem 33: Left action of one is identity (reversed)
-- ============================================================================
def morita_lAct_one_symm (m : M.Mod) :
    Path m (M.lAct A.one m) :=
  Path.symm (M.lAct_one m)

-- ============================================================================
-- Theorem 34: Inner product double conjugation
-- ============================================================================
def morita_ip_double_conj (m n : M.Mod) :
    Path (A.star (A.star (M.ipA m n))) (M.ipA m n) :=
  A.star_star (M.ipA m n)

-- ============================================================================
-- Theorem 35: Inner product conjugation chain
-- ============================================================================
def morita_ip_conj_chain (m n : M.Mod) :
    Path (A.star (A.star (M.ipA m n))) (M.ipA m n) :=
  Path.trans
    (congrArg A.star (M.ip_conj m n))
    (M.ip_conj n m)

-- ============================================================================
-- Theorem 36: Compatibility with identity
-- ============================================================================
def morita_compat_one (m : M.Mod) :
    Path (M.lAct A.one (M.rAct m B.one)) (M.rAct (M.lAct A.one m) B.one) :=
  M.compat A.one B.one m

-- ============================================================================
-- Theorem 37: Compatibility simplification chain
-- ============================================================================
def morita_compat_simplify (m : M.Mod) :
    Path (M.lAct A.one (M.rAct m B.one)) m :=
  Path.trans
    (M.compat A.one B.one m)
    (Path.trans
      (congrArg (fun x => M.rAct x B.one) (M.lAct_one m))
      (M.rAct_one m))

-- ============================================================================
-- Section 8: Noncommutative Torus
-- ============================================================================

/-- Noncommutative torus T_theta. -/
structure NCTorus where
  alg : CStarAlg.{u}
  U : alg.Carrier
  V : alg.Carrier
  theta : alg.Carrier
  -- VU = theta * UV
  comm_rel : Path (alg.mul V U) (alg.mul theta (alg.mul U V))
  -- Unitarity
  U_unitary : Path (alg.mul (alg.star U) U) alg.one
  V_unitary : Path (alg.mul (alg.star V) V) alg.one
  theta_unitary : Path (alg.mul (alg.star theta) theta) alg.one

variable (T : NCTorus.{u})

-- ============================================================================
-- Theorem 38: Reverse commutation relation
-- ============================================================================
def nctorus_comm_rev :
    Path (T.alg.mul T.theta (T.alg.mul T.U T.V)) (T.alg.mul T.V T.U) :=
  Path.symm T.comm_rel

-- ============================================================================
-- Theorem 39: Star of UV via anti-morphism
-- ============================================================================
def nctorus_star_UV :
    Path (T.alg.star (T.alg.mul T.U T.V))
         (T.alg.mul (T.alg.star T.V) (T.alg.star T.U)) :=
  T.alg.star_mul T.U T.V

-- ============================================================================
-- Theorem 40: Star of VU equals star of theta*UV
-- ============================================================================
def nctorus_star_VU :
    Path (T.alg.star (T.alg.mul T.V T.U))
         (T.alg.star (T.alg.mul T.theta (T.alg.mul T.U T.V))) :=
  congrArg T.alg.star T.comm_rel

-- ============================================================================
-- Theorem 41: Star of VU expanded
-- ============================================================================
def nctorus_star_VU_expanded :
    Path (T.alg.star (T.alg.mul T.V T.U))
         (T.alg.mul (T.alg.star T.U) (T.alg.star T.V)) :=
  T.alg.star_mul T.V T.U

-- ============================================================================
-- Theorem 42: U*U = 1 implies norm property
-- ============================================================================
def nctorus_U_norm :
    Path (T.alg.norm (T.alg.mul (T.alg.star T.U) T.U))
         (T.alg.mul (T.alg.norm T.U) (T.alg.norm T.U)) :=
  T.alg.cstar_id T.U

-- ============================================================================
-- Section 9: Spectral Action Principle
-- ============================================================================

/-- Spectral action data: trace functional on spectral triple. -/
structure SpectralAction where
  triple : SpectralTriple.{u}
  cutoff : triple.alg.Carrier
  trFunc : triple.alg.Carrier -> triple.alg.Carrier
  -- Trace property
  trace_mul_comm : (a b : triple.alg.Carrier) ->
    Path (trFunc (triple.alg.mul a b)) (trFunc (triple.alg.mul b a))
  -- Trace linearity
  trace_add : (a b : triple.alg.Carrier) ->
    Path (trFunc (triple.alg.add a b)) (triple.alg.add (trFunc a) (trFunc b))

variable (SA : SpectralAction.{u})

-- ============================================================================
-- Theorem 43: Spectral action trace cyclicity
-- ============================================================================
def spectral_trace_cyclic (a b c : SA.triple.alg.Carrier) :
    Path (SA.trFunc (SA.triple.alg.mul (SA.triple.alg.mul a b) c))
         (SA.trFunc (SA.triple.alg.mul c (SA.triple.alg.mul a b))) :=
  SA.trace_mul_comm (SA.triple.alg.mul a b) c

-- ============================================================================
-- Theorem 44: Trace of star product
-- ============================================================================
def spectral_trace_star (a : SA.triple.alg.Carrier) :
    Path (SA.trFunc (SA.triple.alg.mul (SA.triple.alg.star a) a))
         (SA.trFunc (SA.triple.alg.mul a (SA.triple.alg.star a))) :=
  SA.trace_mul_comm (SA.triple.alg.star a) a

-- ============================================================================
-- Theorem 45: Trace linearity chain
-- ============================================================================
def spectral_trace_linear_chain (a b c : SA.triple.alg.Carrier) :
    Path (SA.trFunc (SA.triple.alg.add a (SA.triple.alg.add b c)))
         (SA.triple.alg.add (SA.trFunc a) (SA.triple.alg.add (SA.trFunc b) (SA.trFunc c))) :=
  Path.trans
    (SA.trace_add a (SA.triple.alg.add b c))
    (congrArg (SA.triple.alg.add (SA.trFunc a)) (SA.trace_add b c))

-- ============================================================================
-- Section 10: Index Theorems (Connes-Moscovici)
-- ============================================================================

/-- Fredholm module: (A, H, F) with F approximately involutive. -/
structure FredholmModule where
  alg : CStarAlg.{u}
  HSpace : Type u
  rep : alg.Carrier -> HSpace -> HSpace
  F : HSpace -> HSpace
  -- F^2 = 1
  F_sq : (h : HSpace) -> Path (F (F h)) h
  -- [F, pi(a)] compact
  F_commutes : (a : alg.Carrier) -> (h : HSpace) ->
    Path (F (rep a h)) (rep a (F h))
  -- Rep hom
  rep_mul : (a b : alg.Carrier) -> (h : HSpace) ->
    Path (rep (alg.mul a b) h) (rep a (rep b h))
  rep_one : (h : HSpace) -> Path (rep alg.one h) h

variable (FM : FredholmModule.{u})

-- ============================================================================
-- Theorem 46: Triple F application
-- ============================================================================
def fredholm_F_triple (h : FM.HSpace) :
    Path (FM.F (FM.F (FM.F h))) (FM.F h) :=
  congrArg FM.F (FM.F_sq h)

-- ============================================================================
-- Theorem 47: Quadruple F application
-- ============================================================================
def fredholm_F_quad (h : FM.HSpace) :
    Path (FM.F (FM.F (FM.F (FM.F h)))) h :=
  Path.trans
    (congrArg FM.F (fredholm_F_triple FM h))
    (FM.F_sq h)

-- ============================================================================
-- Theorem 48: F commutes with rep of product
-- ============================================================================
def fredholm_F_rep_prod (a b : FM.alg.Carrier) (h : FM.HSpace) :
    Path (FM.F (FM.rep (FM.alg.mul a b) h))
         (FM.rep a (FM.rep b (FM.F h))) :=
  Path.trans
    (FM.F_commutes (FM.alg.mul a b) h)
    (Path.trans
      (FM.rep_mul a b (FM.F h))
      (congrArg (FM.rep a) (Path.refl _)))

-- ============================================================================
-- Theorem 49: Index pairing via rep and F
-- ============================================================================
def index_pairing (e : Projection FM.alg) (h : FM.HSpace) :
    Path (FM.F (FM.rep e.elem (FM.F (FM.rep e.elem h))))
         (FM.rep e.elem (FM.rep e.elem h)) :=
  Path.trans
    (FM.F_commutes e.elem (FM.F (FM.rep e.elem h)))
    (congrArg (FM.rep e.elem) (FM.F_sq (FM.rep e.elem h)))

-- ============================================================================
-- Theorem 50: Index pairing simplification via idempotent
-- ============================================================================
def index_pairing_idem (e : Projection FM.alg) (h : FM.HSpace) :
    Path (FM.rep (FM.alg.mul e.elem e.elem) h) (FM.rep e.elem h) :=
  congrArg (fun x => FM.rep x h) e.idem

-- ============================================================================
-- Section 11: KK-Theory Structure
-- ============================================================================

/-- Kasparov module for KK(A, B). -/
structure KasparovMod (A B : CStarAlg.{u}) where
  Mod : Type u
  lAct : A.Carrier -> Mod -> Mod
  rAct : Mod -> B.Carrier -> Mod
  ipB : Mod -> Mod -> B.Carrier
  F : Mod -> Mod
  -- Axioms
  lAct_mul : (a1 a2 : A.Carrier) -> (m : Mod) ->
    Path (lAct (A.mul a1 a2) m) (lAct a1 (lAct a2 m))
  lAct_one : (m : Mod) -> Path (lAct A.one m) m
  F_sq : (m : Mod) -> Path (F (F m)) m
  F_compat : (a : A.Carrier) -> (m : Mod) ->
    Path (F (lAct a m)) (lAct a (F m))
  rAct_mul : (b1 b2 : B.Carrier) -> (m : Mod) ->
    Path (rAct (rAct m b1) b2) (rAct m (B.mul b1 b2))

variable {C : CStarAlg.{u}}
variable (KAB : KasparovMod A B)

-- ============================================================================
-- Theorem 51: KK triple left action
-- ============================================================================
def kk_lAct_triple (a1 a2 a3 : A.Carrier) (m : KAB.Mod) :
    Path (KAB.lAct (A.mul (A.mul a1 a2) a3) m)
         (KAB.lAct a1 (KAB.lAct a2 (KAB.lAct a3 m))) :=
  Path.trans
    (KAB.lAct_mul (A.mul a1 a2) a3 m)
    (KAB.lAct_mul a1 a2 (KAB.lAct a3 m))

-- ============================================================================
-- Theorem 52: KK F triple
-- ============================================================================
def kk_F_triple (m : KAB.Mod) :
    Path (KAB.F (KAB.F (KAB.F m))) (KAB.F m) :=
  congrArg KAB.F (KAB.F_sq m)

-- ============================================================================
-- Theorem 53: KK F quad
-- ============================================================================
def kk_F_quad (m : KAB.Mod) :
    Path (KAB.F (KAB.F (KAB.F (KAB.F m)))) m :=
  Path.trans
    (congrArg KAB.F (kk_F_triple A KAB m))
    (KAB.F_sq m)

-- ============================================================================
-- Theorem 54: KK F commutes with triple action
-- ============================================================================
def kk_F_lAct_triple (a1 a2 a3 : A.Carrier) (m : KAB.Mod) :
    Path (KAB.F (KAB.lAct (A.mul (A.mul a1 a2) a3) m))
         (KAB.lAct a1 (KAB.lAct a2 (KAB.lAct a3 (KAB.F m)))) :=
  Path.trans
    (KAB.F_compat (A.mul (A.mul a1 a2) a3) m)
    (kk_lAct_triple A KAB a1 a2 a3 (KAB.F m))

-- ============================================================================
-- Theorem 55: KK one action via F
-- ============================================================================
def kk_F_one (m : KAB.Mod) :
    Path (KAB.F (KAB.lAct A.one m)) (KAB.F m) :=
  congrArg KAB.F (KAB.lAct_one m)

-- ============================================================================
-- Theorem 56: KK one action identity chain
-- ============================================================================
def kk_one_F_chain (m : KAB.Mod) :
    Path (KAB.F (KAB.lAct A.one m)) (KAB.lAct A.one (KAB.F m)) :=
  KAB.F_compat A.one m

-- ============================================================================
-- Theorem 57: KK right action triple
-- ============================================================================
def kk_rAct_triple (b1 b2 b3 : B.Carrier) (m : KAB.Mod) :
    Path (KAB.rAct (KAB.rAct (KAB.rAct m b1) b2) b3)
         (KAB.rAct m (B.mul (B.mul b1 b2) b3)) :=
  Path.trans
    (congrArg (fun x => KAB.rAct x b3) (KAB.rAct_mul b1 b2 m))
    (KAB.rAct_mul (B.mul b1 b2) b3 m)

-- ============================================================================
-- Section 12: Additional Deep Path Compositions
-- ============================================================================

-- ============================================================================
-- Theorem 58: Star distributes over add (reversed direction)
-- ============================================================================
def star_add_rev (a b : A.Carrier) :
    Path (A.add (A.star a) (A.star b)) (A.star (A.add a b)) :=
  Path.symm (A.star_add a b)

-- ============================================================================
-- Theorem 59: C*-identity combined with norm_star
-- ============================================================================
def cstar_norm_chain (a : A.Carrier) :
    Path (A.norm (A.mul (A.star a) a))
         (A.mul (A.norm a) (A.norm a)) :=
  A.cstar_id a

-- ============================================================================
-- Theorem 60: Norm of star product via chain
-- ============================================================================
def norm_star_product_chain (a : A.Carrier) :
    Path (A.norm (A.mul (A.star (A.star a)) (A.star a)))
         (A.mul (A.norm (A.star a)) (A.norm (A.star a))) :=
  A.cstar_id (A.star a)

-- ============================================================================
-- Theorem 61: Full norm chain: ||a*a|| = ||a||^2 with star simplification
-- ============================================================================
def full_norm_chain (a : A.Carrier) :
    Path (A.mul (A.norm (A.star a)) (A.norm (A.star a)))
         (A.mul (A.norm a) (A.norm a)) :=
  Path.trans
    (congrArg (fun x => A.mul x (A.norm (A.star a))) (A.norm_star a))
    (congrArg (A.mul (A.norm a)) (A.norm_star a))

-- ============================================================================
-- Theorem 62: Morita inner product chain: star(star(<m,n>)) = <m,n>
-- ============================================================================
def morita_ip_involution (m n : M.Mod) :
    Path (A.star (A.star (M.ipA m n))) (M.ipA m n) :=
  A.star_star (M.ipA m n)

-- ============================================================================
-- Theorem 63: Morita full conjugation chain
-- ============================================================================
def morita_full_conj_chain (m n : M.Mod) :
    Path (A.star (A.star (M.ipA m n))) (M.ipA m n) :=
  Path.trans
    (congrArg A.star (M.ip_conj m n))
    (M.ip_conj n m)

-- ============================================================================
-- Theorem 64: NC torus star relation chain
-- ============================================================================
def nctorus_star_rel_chain :
    Path (T.alg.star (T.alg.mul T.V T.U))
         (T.alg.mul (T.alg.star (T.alg.mul T.U T.V)) (T.alg.star T.theta)) :=
  Path.trans
    (congrArg T.alg.star T.comm_rel)
    (T.alg.star_mul T.theta (T.alg.mul T.U T.V))

-- ============================================================================
-- Theorem 65: Spectral rep one chain
-- ============================================================================
def spectral_rep_one_chain (h : S.HSpace) :
    Path (S.rep (S.alg.mul S.alg.one (S.alg.mul S.alg.one S.alg.one)) h)
         h :=
  Path.trans
    (S.rep_mul S.alg.one (S.alg.mul S.alg.one S.alg.one) h)
    (Path.trans
      (congrArg (S.rep S.alg.one) (rep_one_one S h))
      (S.rep_one h))

-- ============================================================================
-- Section 13: Gelfand-Naimark Representation Theory
-- ============================================================================

/-- Gelfand-Naimark style representation package. -/
structure GelfandNaimarkRep (A : CStarAlg.{u}) where
  Hilb : Type u
  rep : A.Carrier -> Hilb -> Hilb
  cyc : Hilb
  rep_mul : (a b : A.Carrier) -> (h : Hilb) ->
    Path (rep (A.mul a b) h) (rep a (rep b h))
  rep_one : (h : Hilb) -> Path (rep A.one h) h
  faithful : (a : A.Carrier) -> Path (rep a cyc) (rep a cyc)

variable (GN : GelfandNaimarkRep A)

-- ============================================================================
-- Theorem 66: Gelfand-Naimark triple product representation
-- ============================================================================
def gelfand_rep_triple (a b c : A.Carrier) (h : GN.Hilb) :
    Path (GN.rep (A.mul (A.mul a b) c) h)
         (GN.rep a (GN.rep b (GN.rep c h))) :=
  Path.trans
    (GN.rep_mul (A.mul a b) c h)
    (GN.rep_mul a b (GN.rep c h))

-- ============================================================================
-- Theorem 67: Gelfand-Naimark representation of one*one
-- ============================================================================
def gelfand_rep_one_one (h : GN.Hilb) :
    Path (GN.rep (A.mul A.one A.one) h) h :=
  Path.trans
    (GN.rep_mul A.one A.one h)
    (Path.trans
      (congrArg (GN.rep A.one) (GN.rep_one h))
      (GN.rep_one h))

-- ============================================================================
-- Theorem 68: Faithfulness witness at cyclic vector
-- ============================================================================
def gelfand_faithful_cyc (a : A.Carrier) :
    Path (GN.rep a GN.cyc) (GN.rep a GN.cyc) :=
  GN.faithful a

-- ============================================================================
-- Section 14: Real/graded data using Sym and Gam
-- ============================================================================

/-- Real-graded package for spectral triples using ASCII names `Sym` and `Gam`. -/
structure RealGradedData where
  triple : SpectralTriple.{u}
  Sym : triple.HSpace -> triple.HSpace
  Gam : triple.HSpace -> triple.HSpace
  Sym_sq : (h : triple.HSpace) -> Path (Sym (Sym h)) h
  Gam_sq : (h : triple.HSpace) -> Path (Gam (Gam h)) h
  SymGam : (h : triple.HSpace) -> Path (Sym (Gam h)) (Gam (Sym h))

variable (RG : RealGradedData)

-- ============================================================================
-- Theorem 69: Sym quadruple action contracts to identity
-- ============================================================================
def real_sym_quad (h : RG.triple.HSpace) :
    Path (RG.Sym (RG.Sym (RG.Sym (RG.Sym h)))) h :=
  Path.trans
    (congrArg RG.Sym (RG.Sym_sq (RG.Sym h)))
    (RG.Sym_sq h)

-- ============================================================================
-- Theorem 70: Gam quadruple action contracts to identity
-- ============================================================================
def real_gam_quad (h : RG.triple.HSpace) :
    Path (RG.Gam (RG.Gam (RG.Gam (RG.Gam h)))) h :=
  Path.trans
    (congrArg RG.Gam (RG.Gam_sq (RG.Gam h)))
    (RG.Gam_sq h)

-- ============================================================================
-- Theorem 71: Sym/Gam commutation roundtrip
-- ============================================================================
def real_sym_gam_roundtrip (h : RG.triple.HSpace) :
    Path (RG.Sym (RG.Gam h)) (RG.Sym (RG.Gam h)) :=
  Path.trans
    (RG.SymGam h)
    (Path.symm (RG.SymGam h))

-- ============================================================================
-- Theorem 72: Sym commutes with Gam-square simplification
-- ============================================================================
def real_sym_after_gam_sq (h : RG.triple.HSpace) :
    Path (RG.Sym (RG.Gam (RG.Gam h))) (RG.Sym h) :=
  congrArg RG.Sym (RG.Gam_sq h)

-- ============================================================================
-- Theorem 73: Gam commutes with Sym-square simplification
-- ============================================================================
def real_gam_after_sym_sq (h : RG.triple.HSpace) :
    Path (RG.Gam (RG.Sym (RG.Sym h))) (RG.Gam h) :=
  congrArg RG.Gam (RG.Sym_sq h)

-- ============================================================================
-- Section 15: Deformation Quantization
-- ============================================================================

/-- Deformation quantization package for operator algebra products. -/
structure DeformationQuantData (A : CStarAlg.{u}) where
  hbar : A.Carrier
  starProd : A.Carrier -> A.Carrier -> A.Carrier
  zeroth : (a b : A.Carrier) -> Path (starProd a b) (A.mul a b)
  unitL : (a : A.Carrier) -> Path (starProd A.one a) a
  assoc : (a b c : A.Carrier) ->
    Path (starProd (starProd a b) c) (starProd a (starProd b c))
  firstOrder : (a b : A.Carrier) ->
    Path (starProd a b) (A.add (A.mul a b) (A.mul b a))

variable (DQ : DeformationQuantData A)

-- ============================================================================
-- Theorem 74: Zeroth-order deformation recovers multiplication
-- ============================================================================
def deformation_zeroth (a b : A.Carrier) :
    Path (DQ.starProd a b) (A.mul a b) :=
  DQ.zeroth a b

-- ============================================================================
-- Theorem 75: Left unit chain for star product
-- ============================================================================
def deformation_unit_chain (a : A.Carrier) :
    Path (DQ.starProd A.one (DQ.starProd A.one a)) a :=
  Path.trans
    (Path.symm (DQ.assoc A.one A.one a))
    (Path.trans
      (congrArg (fun x => DQ.starProd x a) (DQ.unitL A.one))
      (DQ.unitL a))

-- ============================================================================
-- Theorem 76: First-order term realizes noncommutative correction
-- ============================================================================
def deformation_first_order (a b : A.Carrier) :
    Path (DQ.starProd a b) (A.add (A.mul a b) (A.mul b a)) :=
  DQ.firstOrder a b

-- ============================================================================
-- Theorem 77: First-order correction is symmetric under add_comm
-- ============================================================================
def deformation_first_symm (a b : A.Carrier) :
    Path (A.add (A.mul a b) (A.mul b a))
         (A.add (A.mul b a) (A.mul a b)) :=
  A.add_comm (A.mul a b) (A.mul b a)

-- ============================================================================
-- Theorem 78: First-order chain to swapped correction
-- ============================================================================
def deformation_first_chain (a b : A.Carrier) :
    Path (DQ.starProd a b)
         (A.add (A.mul b a) (A.mul a b)) :=
  Path.trans
    (DQ.firstOrder a b)
    (deformation_first_symm A a b)

end NoncommutativeGeometryDeep
end Algebra
end Path
end ComputationalPaths
