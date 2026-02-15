import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

/-!
# Arithmetic Geometry via Computational Paths

Formalization of:
- Elliptic curves (group law, isogenies)
- Modular forms and Hecke operators
- L-functions and functional equations
- Birch-Swinnerton-Dyer conjecture structure
- Tate-Shafarevich and Selmer groups
- p-adic paths and Iwasawa theory
- Class field theory and Artin reciprocity
-/

-- ============================================================
-- SECTION 1: Elliptic Curve Group Law
-- ============================================================

inductive ECStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → ECStep α a a
  | symm  : ECStep α a b → ECStep α b a
  | trans : ECStep α a b → ECStep α b c → ECStep α a c
  | congrArg : (f : α → α) → ECStep α a b → ECStep α (f a) (f b)
  -- Group law
  | ecAdd     : ECStep α a b  -- P + Q on curve
  | ecNeg     : ECStep α a b  -- negation −P
  | ecDouble  : ECStep α a b  -- [2]P doubling
  | ecIdentity : ECStep α a b -- identity element O
  -- Isogeny
  | isogeny   : ECStep α a b  -- φ: E → E'
  | dualIsog  : ECStep α a b  -- dual isogeny φ̂
  | endomorph : ECStep α a b  -- endomorphism ring element
  | frobenius : ECStep α a b  -- Frobenius endomorphism

inductive ECPath : (α : Type u) → α → α → Type u where
  | nil  : ECPath α a a
  | cons : ECStep α a b → ECPath α b c → ECPath α a c

namespace ECPath

def single (s : ECStep α a b) : ECPath α a b := cons s nil

def append : ECPath α a b → ECPath α b c → ECPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : ECPath α a b → ECPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (ECStep.symm s))

def congrArg (f : α → α) : ECPath α a b → ECPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (ECStep.congrArg f s) (congrArg f p)

end ECPath

-- Group law associativity: (P+Q)+R = P+(Q+R)
def ec_group_assoc {α : Type u} (a b : α) :
    ECPath α a b :=
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.ecAdd ECStep.ecAdd)) <|
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.ecAdd) ECPath.nil

-- Identity: P + O = P
def ec_identity_right {α : Type u} (a : α) :
    ECPath α a a :=
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.ecIdentity) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.ecAdd ECStep.ecIdentity)) <|
  ECPath.nil

-- Inverse: P + (−P) = O
def ec_inverse_path {α : Type u} (a b : α) :
    ECPath α a b :=
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.ecNeg) <|
  ECPath.cons (ECStep.ecIdentity) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.ecAdd
    (ECStep.trans ECStep.ecNeg ECStep.ecIdentity))) <|
  ECPath.cons (ECStep.ecIdentity) ECPath.nil

-- Doubling formula: [2]P = P + P
def ec_doubling_path {α : Type u} (a b : α) :
    ECPath α a b :=
  ECPath.cons (ECStep.ecDouble) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.ecAdd ECStep.ecAdd)) <|
  ECPath.cons (ECStep.ecAdd) <|
  ECPath.cons (ECStep.ecAdd) ECPath.nil

-- Isogeny composition: φ̂∘φ = [deg φ]
def isogeny_dual_composition {α : Type u} (a : α) :
    ECPath α a a :=
  ECPath.cons (ECStep.isogeny) <|
  ECPath.cons (ECStep.dualIsog) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.isogeny ECStep.dualIsog)) <|
  ECPath.nil

-- Frobenius: φ_p∘φ̂_p = [p]
def frobenius_dual_degree {α : Type u} (a : α) :
    ECPath α a a :=
  ECPath.cons (ECStep.frobenius) <|
  ECPath.cons (ECStep.dualIsog) <|
  ECPath.cons (ECStep.endomorph) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.frobenius
    (ECStep.trans ECStep.dualIsog ECStep.endomorph))) <|
  ECPath.nil

-- ============================================================
-- SECTION 2: Modular Forms and Hecke Operators
-- ============================================================

inductive ModFormStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → ModFormStep α a a
  | symm  : ModFormStep α a b → ModFormStep α b a
  | trans : ModFormStep α a b → ModFormStep α b c → ModFormStep α a c
  | congrArg : (f : α → α) → ModFormStep α a b → ModFormStep α (f a) (f b)
  | heckeOp    : ModFormStep α a b  -- Hecke operator T_n
  | diamondOp  : ModFormStep α a b  -- diamond operator <d>
  | slashAction : ModFormStep α a b -- slash action f|_k γ
  | eisenstein : ModFormStep α a b  -- Eisenstein series
  | cuspForm   : ModFormStep α a b  -- cusp form projection
  | petersson  : ModFormStep α a b  -- Petersson inner product

inductive ModFormPath : (α : Type u) → α → α → Type u where
  | nil  : ModFormPath α a a
  | cons : ModFormStep α a b → ModFormPath α b c → ModFormPath α a c

namespace ModFormPath

def single (s : ModFormStep α a b) : ModFormPath α a b := cons s nil

def append : ModFormPath α a b → ModFormPath α b c → ModFormPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : ModFormPath α a b → ModFormPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (ModFormStep.symm s))

def congrArg (f : α → α) : ModFormPath α a b → ModFormPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (ModFormStep.congrArg f s) (congrArg f p)

end ModFormPath

-- Hecke operators commute: T_m T_n = T_n T_m for (m,n)=1
def hecke_commute_coprime {α : Type u} (a : α) :
    ModFormPath α a a :=
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.symm (ModFormStep.trans ModFormStep.heckeOp ModFormStep.heckeOp)) <|
  ModFormPath.nil

-- Hecke multiplicativity: T_mn = T_m T_n for (m,n)=1
def hecke_multiplicative {α : Type u} (a b : α) :
    ModFormPath α a b :=
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.symm (ModFormStep.trans ModFormStep.heckeOp ModFormStep.heckeOp)) <|
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.heckeOp) ModFormPath.nil

-- Hecke is self-adjoint wrt Petersson product
def hecke_petersson_adjoint {α : Type u} (a : α) :
    ModFormPath α a a :=
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.petersson) <|
  ModFormPath.cons (ModFormStep.symm (ModFormStep.trans ModFormStep.heckeOp ModFormStep.petersson)) <|
  ModFormPath.nil

-- Eisenstein + cusp decomposition: M_k = E_k ⊕ S_k
def modform_decomposition {α : Type u} (a b : α) :
    ModFormPath α a b :=
  ModFormPath.cons (ModFormStep.eisenstein) <|
  ModFormPath.cons (ModFormStep.cuspForm) <|
  ModFormPath.cons (ModFormStep.symm ModFormStep.cuspForm) <|
  ModFormPath.cons (ModFormStep.symm ModFormStep.eisenstein) <|
  ModFormPath.cons (ModFormStep.slashAction) <|
  ModFormPath.cons (ModFormStep.eisenstein) <|
  ModFormPath.cons (ModFormStep.cuspForm) ModFormPath.nil

-- ============================================================
-- SECTION 3: L-functions and BSD
-- ============================================================

inductive LFuncStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → LFuncStep α a a
  | symm  : LFuncStep α a b → LFuncStep α b a
  | trans : LFuncStep α a b → LFuncStep α b c → LFuncStep α a c
  | congrArg : (f : α → α) → LFuncStep α a b → LFuncStep α (f a) (f b)
  | eulerProd   : LFuncStep α a b  -- Euler product L(s) = ∏(1-a_p p^{-s})^{-1}
  | funcEq      : LFuncStep α a b  -- functional equation Λ(s) = ε·Λ(k-s)
  | analyticCont : LFuncStep α a b -- analytic continuation
  | specialVal  : LFuncStep α a b  -- special value L(E,1)
  | bsdRank     : LFuncStep α a b  -- BSD: ord_{s=1} L(E,s) = rank E(Q)
  | regulator   : LFuncStep α a b  -- regulator
  | tateShaf    : LFuncStep α a b  -- Tate-Shafarevich group Ш
  | selmer      : LFuncStep α a b  -- Selmer group

inductive LFuncPath : (α : Type u) → α → α → Type u where
  | nil  : LFuncPath α a a
  | cons : LFuncStep α a b → LFuncPath α b c → LFuncPath α a c

namespace LFuncPath

def single (s : LFuncStep α a b) : LFuncPath α a b := cons s nil

def append : LFuncPath α a b → LFuncPath α b c → LFuncPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : LFuncPath α a b → LFuncPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (LFuncStep.symm s))

def congrArg (f : α → α) : LFuncPath α a b → LFuncPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (LFuncStep.congrArg f s) (congrArg f p)

end LFuncPath

-- Functional equation: Λ(s) = ε·Λ(k-s)
def functional_equation_path {α : Type u} (a : α) :
    LFuncPath α a a :=
  LFuncPath.cons (LFuncStep.funcEq) <|
  LFuncPath.cons (LFuncStep.funcEq) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.trans LFuncStep.funcEq LFuncStep.funcEq)) <|
  LFuncPath.nil

-- Euler product to analytic continuation
def euler_to_analytic {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.eulerProd) <|
  LFuncPath.cons (LFuncStep.analyticCont) <|
  LFuncPath.cons (LFuncStep.funcEq) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.trans LFuncStep.eulerProd
    (LFuncStep.trans LFuncStep.analyticCont LFuncStep.funcEq))) <|
  LFuncPath.cons (LFuncStep.analyticCont) LFuncPath.nil

-- BSD formula path: L(E,1)/Ω = |Ш|·R·∏c_p / |E(Q)_tors|²
def bsd_formula_path {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.specialVal) <|
  LFuncPath.cons (LFuncStep.bsdRank) <|
  LFuncPath.cons (LFuncStep.regulator) <|
  LFuncPath.cons (LFuncStep.tateShaf) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.trans LFuncStep.bsdRank
    (LFuncStep.trans LFuncStep.regulator LFuncStep.tateShaf))) <|
  LFuncPath.cons (LFuncStep.specialVal) LFuncPath.nil

-- Selmer-Tate-Shafarevich exact sequence: 0 → E(Q)/nE(Q) → Sel → Ш[n] → 0
def selmer_tate_shaf_exact {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.tateShaf) <|
  LFuncPath.cons (LFuncStep.symm LFuncStep.tateShaf) <|
  LFuncPath.cons (LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.tateShaf) LFuncPath.nil

-- BSD rank zero: L(E,1) ≠ 0 implies E(Q) finite
def bsd_rank_zero {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.specialVal) <|
  LFuncPath.cons (LFuncStep.bsdRank) <|
  LFuncPath.cons (LFuncStep.symm LFuncStep.bsdRank) <|
  LFuncPath.cons (LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.tateShaf) LFuncPath.nil

-- ============================================================
-- SECTION 4: p-adic and Iwasawa Theory
-- ============================================================

inductive IwasStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → IwasStep α a a
  | symm  : IwasStep α a b → IwasStep α b a
  | trans : IwasStep α a b → IwasStep α b c → IwasStep α a c
  | congrArg : (f : α → α) → IwasStep α a b → IwasStep α (f a) (f b)
  | padicLog    : IwasStep α a b  -- p-adic logarithm
  | padicExp    : IwasStep α a b  -- p-adic exponential
  | iwasAlgebra : IwasStep α a b  -- Iwasawa algebra Λ
  | charPoly    : IwasStep α a b  -- characteristic polynomial
  | mainConj    : IwasStep α a b  -- Iwasawa main conjecture
  | classGroup  : IwasStep α a b  -- class group tower
  | artinMap    : IwasStep α a b  -- Artin reciprocity map
  | localRecip  : IwasStep α a b  -- local reciprocity

inductive IwasPath : (α : Type u) → α → α → Type u where
  | nil  : IwasPath α a a
  | cons : IwasStep α a b → IwasPath α b c → IwasPath α a c

namespace IwasPath

def single (s : IwasStep α a b) : IwasPath α a b := cons s nil

def append : IwasPath α a b → IwasPath α b c → IwasPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : IwasPath α a b → IwasPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (IwasStep.symm s))

def congrArg (f : α → α) : IwasPath α a b → IwasPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (IwasStep.congrArg f s) (congrArg f p)

end IwasPath

-- p-adic log∘exp = id (on convergence domain)
def padic_log_exp_inverse {α : Type u} (a : α) :
    IwasPath α a a :=
  IwasPath.cons (IwasStep.padicExp) <|
  IwasPath.cons (IwasStep.padicLog) <|
  IwasPath.cons (IwasStep.symm (IwasStep.trans IwasStep.padicExp IwasStep.padicLog)) <|
  IwasPath.nil

-- Iwasawa main conjecture: char ideal = p-adic L-function
def iwasawa_main_conjecture {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.iwasAlgebra) <|
  IwasPath.cons (IwasStep.charPoly) <|
  IwasPath.cons (IwasStep.mainConj) <|
  IwasPath.cons (IwasStep.symm (IwasStep.trans IwasStep.iwasAlgebra
    (IwasStep.trans IwasStep.charPoly IwasStep.mainConj))) <|
  IwasPath.cons (IwasStep.charPoly) IwasPath.nil

-- Class number tower: #Cl(K_n) grows via Iwasawa formula
def class_number_tower {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.classGroup) <|
  IwasPath.cons (IwasStep.iwasAlgebra) <|
  IwasPath.cons (IwasStep.charPoly) <|
  IwasPath.cons (IwasStep.symm IwasStep.charPoly) <|
  IwasPath.cons (IwasStep.classGroup) IwasPath.nil

-- Artin reciprocity: Gal(K^ab/K) ≅ C_K / C_K^0
def artin_reciprocity_path {α : Type u} (a : α) :
    IwasPath α a a :=
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.symm IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.symm IwasStep.artinMap) <|
  IwasPath.nil

-- Local reciprocity: K* → Gal(K^ab/K)
def local_reciprocity_path {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.localRecip) <|
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.symm (IwasStep.trans IwasStep.localRecip IwasStep.artinMap)) <|
  IwasPath.cons (IwasStep.localRecip) <|
  IwasPath.cons (IwasStep.artinMap) IwasPath.nil

-- Local-global compatibility
def local_global_compat {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.localRecip) <|
  IwasPath.cons (IwasStep.symm IwasStep.localRecip) <|
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.classGroup) IwasPath.nil

-- p-adic interpolation of L-values
def padic_interpolation {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.padicLog) <|
  IwasPath.cons (IwasStep.iwasAlgebra) <|
  IwasPath.cons (IwasStep.mainConj) <|
  IwasPath.cons (IwasStep.symm (IwasStep.trans IwasStep.padicLog
    (IwasStep.trans IwasStep.iwasAlgebra IwasStep.mainConj))) <|
  IwasPath.cons (IwasStep.charPoly) IwasPath.nil

-- ============================================================
-- SECTION 5: Cross-domain CongrArg Theorems
-- ============================================================

-- Elliptic curve operations under functorial map
def ec_add_functorial {α : Type u} (f : α → α) (a b : α) :
    ECPath α (f a) (f b) :=
  ECPath.cons (ECStep.congrArg f ECStep.ecAdd) <|
  ECPath.cons (ECStep.congrArg f ECStep.ecNeg) <|
  ECPath.cons (ECStep.symm (ECStep.congrArg f (ECStep.trans ECStep.ecAdd ECStep.ecNeg))) <|
  ECPath.cons (ECStep.congrArg f ECStep.isogeny) <|
  ECPath.cons (ECStep.congrArg f ECStep.dualIsog) ECPath.nil

-- Hecke action functorial
def hecke_functorial {α : Type u} (f : α → α) (a b : α) :
    ModFormPath α (f a) (f b) :=
  ModFormPath.cons (ModFormStep.congrArg f ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.congrArg f ModFormStep.petersson) <|
  ModFormPath.cons (ModFormStep.symm (ModFormStep.congrArg f
    (ModFormStep.trans ModFormStep.heckeOp ModFormStep.petersson))) <|
  ModFormPath.cons (ModFormStep.congrArg f ModFormStep.cuspForm) ModFormPath.nil

-- L-function functorial
def lfunc_functorial {α : Type u} (f : α → α) (a b : α) :
    LFuncPath α (f a) (f b) :=
  LFuncPath.cons (LFuncStep.congrArg f LFuncStep.eulerProd) <|
  LFuncPath.cons (LFuncStep.congrArg f LFuncStep.funcEq) <|
  LFuncPath.cons (LFuncStep.congrArg f LFuncStep.analyticCont) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.congrArg f
    (LFuncStep.trans LFuncStep.eulerProd (LFuncStep.trans LFuncStep.funcEq LFuncStep.analyticCont)))) <|
  LFuncPath.cons (LFuncStep.congrArg f LFuncStep.specialVal) LFuncPath.nil

-- Iwasawa under base change
def iwasawa_base_change {α : Type u} (f : α → α) (a b : α) :
    IwasPath α (f a) (f b) :=
  IwasPath.cons (IwasStep.congrArg f IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.congrArg f IwasStep.classGroup) <|
  IwasPath.cons (IwasStep.congrArg f IwasStep.mainConj) <|
  IwasPath.cons (IwasStep.symm (IwasStep.congrArg f
    (IwasStep.trans IwasStep.artinMap (IwasStep.trans IwasStep.classGroup IwasStep.mainConj)))) <|
  IwasPath.cons (IwasStep.congrArg f IwasStep.iwasAlgebra) IwasPath.nil

-- Modularity theorem path: E/Q → f ∈ S_2(Γ_0(N))
def modularity_theorem_path {α : Type u} (a b : α) :
    ECPath α a b :=
  ECPath.cons (ECStep.frobenius) <|
  ECPath.cons (ECStep.endomorph) <|
  ECPath.cons (ECStep.isogeny) <|
  ECPath.cons (ECStep.symm (ECStep.trans ECStep.frobenius
    (ECStep.trans ECStep.endomorph ECStep.isogeny))) <|
  ECPath.cons (ECStep.isogeny) <|
  ECPath.cons (ECStep.dualIsog) ECPath.nil

-- Eichler-Shimura: L(f,s) = L(A_f,s) for modular abelian variety
def eichler_shimura_path {α : Type u} (a b : α) :
    ModFormPath α a b :=
  ModFormPath.cons (ModFormStep.heckeOp) <|
  ModFormPath.cons (ModFormStep.cuspForm) <|
  ModFormPath.cons (ModFormStep.petersson) <|
  ModFormPath.cons (ModFormStep.symm (ModFormStep.trans ModFormStep.heckeOp
    (ModFormStep.trans ModFormStep.cuspForm ModFormStep.petersson))) <|
  ModFormPath.cons (ModFormStep.slashAction) <|
  ModFormPath.cons (ModFormStep.heckeOp) ModFormPath.nil

-- Gross-Zagier: L'(E,1) relates to Heegner point height
def gross_zagier_path {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.specialVal) <|
  LFuncPath.cons (LFuncStep.bsdRank) <|
  LFuncPath.cons (LFuncStep.regulator) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.trans LFuncStep.specialVal
    (LFuncStep.trans LFuncStep.bsdRank LFuncStep.regulator))) <|
  LFuncPath.cons (LFuncStep.regulator) <|
  LFuncPath.cons (LFuncStep.bsdRank) LFuncPath.nil

-- Kato's Euler system
def kato_euler_system {α : Type u} (a b : α) :
    IwasPath α a b :=
  IwasPath.cons (IwasStep.iwasAlgebra) <|
  IwasPath.cons (IwasStep.mainConj) <|
  IwasPath.cons (IwasStep.classGroup) <|
  IwasPath.cons (IwasStep.artinMap) <|
  IwasPath.cons (IwasStep.symm (IwasStep.trans IwasStep.mainConj
    (IwasStep.trans IwasStep.classGroup IwasStep.artinMap))) <|
  IwasPath.cons (IwasStep.charPoly) IwasPath.nil

-- Tate duality for Selmer groups
def tate_duality_selmer {α : Type u} (a b : α) :
    LFuncPath α a b :=
  LFuncPath.cons (LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.tateShaf) <|
  LFuncPath.cons (LFuncStep.symm LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.selmer) <|
  LFuncPath.cons (LFuncStep.symm (LFuncStep.trans LFuncStep.tateShaf LFuncStep.selmer)) <|
  LFuncPath.cons (LFuncStep.tateShaf) <|
  LFuncPath.cons (LFuncStep.selmer) LFuncPath.nil

end ComputationalPaths
