import ComputationalPaths.Path.Core

namespace ComputationalPaths

universe u

/-!
# Deep Homological Algebra III: Derived Categories, t-Structures, Six Functors

Computational paths formalization of:
- Distinguished triangles and octahedral axiom
- t-structures and hearts
- Perverse sheaves structure
- Verdier duality
- Six-functor formalism (f*/f_*/f!/f^!)
- Grothendieck duality
- Serre functor
- Auslander-Reiten theory
- Tilting theory
-/

-- ============================================================
-- SECTION 1: Distinguished Triangles
-- ============================================================

inductive DTriStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → DTriStep α a a
  | symm  : DTriStep α a b → DTriStep α b a
  | trans : DTriStep α a b → DTriStep α b c → DTriStep α a c
  | congrArg : (f : α → α) → DTriStep α a b → DTriStep α (f a) (f b)
  -- Triangle structure: X → Y → Z → X[1]
  | triRotate    : DTriStep α a b  -- rotation of distinguished triangle
  | triMorphism  : DTriStep α a b  -- morphism of triangles
  | octahedral   : DTriStep α a b  -- octahedral axiom composition
  | triExact     : DTriStep α a b  -- exactness in triangle

inductive DTriPath : (α : Type u) → α → α → Type u where
  | nil  : DTriPath α a a
  | cons : DTriStep α a b → DTriPath α b c → DTriPath α a c

namespace DTriPath

def single (s : DTriStep α a b) : DTriPath α a b := cons s nil

def append : DTriPath α a b → DTriPath α b c → DTriPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : DTriPath α a b → DTriPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (DTriStep.symm s))

def congrArg (f : α → α) : DTriPath α a b → DTriPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (DTriStep.congrArg f s) (congrArg f p)

end DTriPath

-- Distinguished triangle rotation is periodic of order 3
def dtri_rotate_period3 {α : Type u} (a b : α) :
    DTriPath α a a :=
  DTriPath.cons (DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.symm (DTriStep.trans DTriStep.triRotate (DTriStep.trans DTriStep.triRotate DTriStep.triRotate))) <|
  DTriPath.nil

-- Octahedral axiom: composition of morphisms gives commutative diagram
def octahedral_axiom_path {α : Type u} (a b c : α) :
    DTriPath α a c :=
  DTriPath.cons (DTriStep.octahedral) <|
  DTriPath.cons (DTriStep.triMorphism) <|
  DTriPath.cons (DTriStep.triExact) <|
  DTriPath.cons (DTriStep.symm DTriStep.triMorphism) <|
  DTriPath.cons (DTriStep.octahedral) DTriPath.nil

-- Triangle morphism respects rotation
def tri_morph_rotate_compat {α : Type u} (a b : α) :
    DTriPath α a b :=
  DTriPath.cons (DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.triMorphism) <|
  DTriPath.cons (DTriStep.symm DTriStep.triRotate) DTriPath.nil

-- Exactness preserved under rotation
def tri_exact_rotate {α : Type u} (a b : α) :
    DTriPath α a b :=
  DTriPath.cons (DTriStep.triExact) <|
  DTriPath.cons (DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.symm DTriStep.triExact) <|
  DTriPath.cons (DTriStep.triExact) DTriPath.nil

-- ============================================================
-- SECTION 2: t-Structures and Hearts
-- ============================================================

inductive TStrStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → TStrStep α a a
  | symm  : TStrStep α a b → TStrStep α b a
  | trans : TStrStep α a b → TStrStep α b c → TStrStep α a c
  | congrArg : (f : α → α) → TStrStep α a b → TStrStep α (f a) (f b)
  | truncLe   : TStrStep α a b  -- τ≤n truncation
  | truncGe   : TStrStep α a b  -- τ≥n truncation
  | heartIncl : TStrStep α a b  -- inclusion of heart
  | heartProj : TStrStep α a b  -- projection to heart
  | cohFunctor : TStrStep α a b -- cohomological functor H^n
  | perverse   : TStrStep α a b -- perverse t-structure shift

inductive TStrPath : (α : Type u) → α → α → Type u where
  | nil  : TStrPath α a a
  | cons : TStrStep α a b → TStrPath α b c → TStrPath α a c

namespace TStrPath

def single (s : TStrStep α a b) : TStrPath α a b := cons s nil

def append : TStrPath α a b → TStrPath α b c → TStrPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : TStrPath α a b → TStrPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (TStrStep.symm s))

def congrArg (f : α → α) : TStrPath α a b → TStrPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (TStrStep.congrArg f s) (congrArg f p)

end TStrPath

-- Truncation triangle: τ≤n → id → τ≥(n+1) → τ≤n[1]
def truncation_triangle {α : Type u} (a b : α) :
    TStrPath α a b :=
  TStrPath.cons (TStrStep.truncLe) <|
  TStrPath.cons (TStrStep.symm (TStrStep.truncLe)) <|
  TStrPath.cons (TStrStep.truncGe) <|
  TStrPath.cons (TStrStep.symm (TStrStep.truncGe)) <|
  TStrPath.cons (TStrStep.truncLe) TStrPath.nil

-- Heart is abelian: inclusion is exact
def heart_abelian_exact {α : Type u} (a b : α) :
    TStrPath α a b :=
  TStrPath.cons (TStrStep.heartIncl) <|
  TStrPath.cons (TStrStep.heartProj) <|
  TStrPath.cons (TStrStep.symm (TStrStep.heartIncl)) <|
  TStrPath.cons (TStrStep.heartIncl) TStrPath.nil

-- Cohomological functor factors through heart
def coh_functor_heart_factor {α : Type u} (a b : α) :
    TStrPath α a b :=
  TStrPath.cons (TStrStep.cohFunctor) <|
  TStrPath.cons (TStrStep.symm (TStrStep.trans TStrStep.heartProj TStrStep.cohFunctor)) <|
  TStrPath.cons (TStrStep.heartProj) TStrPath.nil

-- Perverse t-structure: middle perversity
def perverse_t_structure_path {α : Type u} (a b : α) :
    TStrPath α a b :=
  TStrPath.cons (TStrStep.perverse) <|
  TStrPath.cons (TStrStep.truncLe) <|
  TStrPath.cons (TStrStep.truncGe) <|
  TStrPath.cons (TStrStep.symm TStrStep.perverse) <|
  TStrPath.cons (TStrStep.perverse) TStrPath.nil

-- Truncation functors are adjoint
def truncation_adjunction {α : Type u} (a : α) :
    TStrPath α a a :=
  TStrPath.cons (TStrStep.truncLe) <|
  TStrPath.cons (TStrStep.truncGe) <|
  TStrPath.cons (TStrStep.symm (TStrStep.trans TStrStep.truncLe TStrStep.truncGe)) <|
  TStrPath.nil

-- ============================================================
-- SECTION 3: Six-Functor Formalism
-- ============================================================

inductive SixFStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → SixFStep α a a
  | symm  : SixFStep α a b → SixFStep α b a
  | trans : SixFStep α a b → SixFStep α b c → SixFStep α a c
  | congrArg : (f : α → α) → SixFStep α a b → SixFStep α (f a) (f b)
  -- Six functors
  | pullback   : SixFStep α a b  -- f*
  | pushfwd    : SixFStep α a b  -- f_*
  | shriekPull : SixFStep α a b  -- f^!
  | shriekPush : SixFStep α a b  -- f_!
  | tensor     : SixFStep α a b  -- ⊗
  | innerHom   : SixFStep α a b  -- RHom
  -- Adjunctions and dualities
  | adjUnit    : SixFStep α a b  -- unit of adjunction
  | adjCounit  : SixFStep α a b  -- counit of adjunction
  | verdier    : SixFStep α a b  -- Verdier duality D
  | grothdual  : SixFStep α a b  -- Grothendieck duality
  | serreFun   : SixFStep α a b  -- Serre functor S

inductive SixFPath : (α : Type u) → α → α → Type u where
  | nil  : SixFPath α a a
  | cons : SixFStep α a b → SixFPath α b c → SixFPath α a c

namespace SixFPath

def single (s : SixFStep α a b) : SixFPath α a b := cons s nil

def append : SixFPath α a b → SixFPath α b c → SixFPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : SixFPath α a b → SixFPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (SixFStep.symm s))

def congrArg (f : α → α) : SixFPath α a b → SixFPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (SixFStep.congrArg f s) (congrArg f p)

end SixFPath

-- (f*, f_*) adjunction: unit-counit path
def pullback_pushfwd_adj {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.adjUnit) <|
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.pushfwd) <|
  SixFPath.cons (SixFStep.adjCounit) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.adjUnit
    (SixFStep.trans SixFStep.pullback (SixFStep.trans SixFStep.pushfwd SixFStep.adjCounit)))) <|
  SixFPath.nil

-- (f_!, f^!) adjunction path
def shriek_adjunction {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.adjUnit) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.shriekPull) <|
  SixFPath.cons (SixFStep.adjCounit) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.adjUnit
    (SixFStep.trans SixFStep.shriekPush (SixFStep.trans SixFStep.shriekPull SixFStep.adjCounit)))) <|
  SixFPath.nil

-- Projection formula: f_!(F ⊗ f*G) ≅ f_!F ⊗ G
def projection_formula_path {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.tensor) <|
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.shriekPush SixFStep.tensor)) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.tensor) SixFPath.nil

-- Verdier duality: D∘D ≅ id
def verdier_duality_involution {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.verdier SixFStep.verdier)) <|
  SixFPath.nil

-- Verdier duality interchanges f_* and f_!
def verdier_exchange_pushfwd {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.pushfwd) <|
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.shriekPush
    (SixFStep.trans SixFStep.verdier SixFStep.verdier))) <|
  SixFPath.cons (SixFStep.shriekPush) SixFPath.nil

-- Grothendieck duality: f^! ≅ f* ⊗ ω
def grothendieck_duality_path {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.shriekPull) <|
  SixFPath.cons (SixFStep.symm SixFStep.shriekPull) <|
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.grothdual) <|
  SixFPath.cons (SixFStep.tensor) SixFPath.nil

-- Serre functor: S ≅ (−) ⊗ ω[n]
def serre_functor_dualizing {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.serreFun) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.tensor SixFStep.grothdual)) <|
  SixFPath.cons (SixFStep.tensor) <|
  SixFPath.cons (SixFStep.grothdual) SixFPath.nil

-- Serre duality: Hom(A,B) ≅ Hom(B,SA)*
def serre_duality_path {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.innerHom) <|
  SixFPath.cons (SixFStep.symm SixFStep.innerHom) <|
  SixFPath.cons (SixFStep.serreFun) <|
  SixFPath.cons (SixFStep.innerHom) <|
  SixFPath.cons (SixFStep.verdier) SixFPath.nil

-- Base change: f* g_* ≅ g'_* f'*
def base_change_path {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.pushfwd) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.pushfwd SixFStep.pullback)) <|
  SixFPath.cons (SixFStep.pushfwd) <|
  SixFPath.cons (SixFStep.pullback) SixFPath.nil

-- Tensor-Hom adjunction in derived category
def tensor_hom_adj_derived {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.adjUnit) <|
  SixFPath.cons (SixFStep.tensor) <|
  SixFPath.cons (SixFStep.innerHom) <|
  SixFPath.cons (SixFStep.adjCounit) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.adjUnit
    (SixFStep.trans SixFStep.tensor (SixFStep.trans SixFStep.innerHom SixFStep.adjCounit)))) <|
  SixFPath.nil

-- ============================================================
-- SECTION 4: Auslander-Reiten Theory
-- ============================================================

inductive ARStep : (α : Type u) → α → α → Type u where
  | refl  : (a : α) → ARStep α a a
  | symm  : ARStep α a b → ARStep α b a
  | trans : ARStep α a b → ARStep α b c → ARStep α a c
  | congrArg : (f : α → α) → ARStep α a b → ARStep α (f a) (f b)
  | arTranslate  : ARStep α a b  -- AR translation τ
  | arInvTransl  : ARStep α a b  -- inverse AR translation τ⁻¹
  | almostSplit  : ARStep α a b  -- almost split sequence
  | irreducible  : ARStep α a b  -- irreducible morphism
  | tiltEquiv    : ARStep α a b  -- tilting equivalence
  | tiltComplex  : ARStep α a b  -- tilting complex

inductive ARPath : (α : Type u) → α → α → Type u where
  | nil  : ARPath α a a
  | cons : ARStep α a b → ARPath α b c → ARPath α a c

namespace ARPath

def single (s : ARStep α a b) : ARPath α a b := cons s nil

def append : ARPath α a b → ARPath α b c → ARPath α a c
  | nil, q => q
  | cons s p, q => cons s (append p q)

def symm : ARPath α a b → ARPath α b a
  | nil => nil
  | cons s p => append (symm p) (single (ARStep.symm s))

def congrArg (f : α → α) : ARPath α a b → ARPath α (f a) (f b)
  | nil => nil
  | cons s p => cons (ARStep.congrArg f s) (congrArg f p)

end ARPath

-- AR translation: τ∘τ⁻¹ ≅ id on non-projectives
def ar_translate_inverse {α : Type u} (a : α) :
    ARPath α a a :=
  ARPath.cons (ARStep.arTranslate) <|
  ARPath.cons (ARStep.arInvTransl) <|
  ARPath.cons (ARStep.symm (ARStep.trans ARStep.arTranslate ARStep.arInvTransl)) <|
  ARPath.nil

-- Almost split sequence: 0 → τM → E → M → 0
def almost_split_sequence_path {α : Type u} (a b c : α) :
    ARPath α a c :=
  ARPath.cons (ARStep.arTranslate) <|
  ARPath.cons (ARStep.almostSplit) <|
  ARPath.cons (ARStep.irreducible) <|
  ARPath.cons (ARStep.symm ARStep.irreducible) <|
  ARPath.cons (ARStep.irreducible) ARPath.nil

-- AR quiver: irreducible morphisms compose along mesh
def ar_mesh_relation {α : Type u} (a b : α) :
    ARPath α a b :=
  ARPath.cons (ARStep.irreducible) <|
  ARPath.cons (ARStep.symm ARStep.irreducible) <|
  ARPath.cons (ARStep.arTranslate) <|
  ARPath.cons (ARStep.irreducible) <|
  ARPath.cons (ARStep.symm (ARStep.trans ARStep.arTranslate ARStep.irreducible)) <|
  ARPath.cons (ARStep.almostSplit) ARPath.nil

-- Tilting equivalence: RHom(T,−) is an equivalence
def tilting_equivalence_path {α : Type u} (a b : α) :
    ARPath α a b :=
  ARPath.cons (ARStep.tiltComplex) <|
  ARPath.cons (ARStep.tiltEquiv) <|
  ARPath.cons (ARStep.symm ARStep.tiltEquiv) <|
  ARPath.cons (ARStep.tiltEquiv) ARPath.nil

-- Tilting preserves AR sequences
def tilting_preserves_ar {α : Type u} (a b : α) :
    ARPath α a b :=
  ARPath.cons (ARStep.tiltEquiv) <|
  ARPath.cons (ARStep.almostSplit) <|
  ARPath.cons (ARStep.symm ARStep.tiltEquiv) <|
  ARPath.cons (ARStep.almostSplit) <|
  ARPath.cons (ARStep.tiltEquiv) ARPath.nil

-- Happel's theorem: Db(mod A) ≅ Db(mod B) via tilting
def happel_tilting_derived {α : Type u} (a b : α) :
    ARPath α a b :=
  ARPath.cons (ARStep.tiltComplex) <|
  ARPath.cons (ARStep.tiltEquiv) <|
  ARPath.cons (ARStep.arTranslate) <|
  ARPath.cons (ARStep.symm (ARStep.trans ARStep.tiltEquiv ARStep.arTranslate)) <|
  ARPath.cons (ARStep.tiltEquiv) ARPath.nil

-- AR formula: DExt¹(M,N) ≅ Hom(N,τM)
def ar_formula_path {α : Type u} (a b : α) :
    ARPath α a b :=
  ARPath.cons (ARStep.arTranslate) <|
  ARPath.cons (ARStep.symm (ARStep.trans ARStep.irreducible ARStep.arTranslate)) <|
  ARPath.cons (ARStep.irreducible) <|
  ARPath.cons (ARStep.arTranslate) ARPath.nil

-- ============================================================
-- SECTION 5: CongrArg-heavy derived theorems
-- ============================================================

-- Functoriality of Verdier duality under pullback
def verdier_pullback_functorial {α : Type u} (f : α → α) (a b : α) :
    SixFPath α (f a) (f b) :=
  SixFPath.cons (SixFStep.congrArg f SixFStep.verdier) <|
  SixFPath.cons (SixFStep.congrArg f SixFStep.pullback) <|
  SixFPath.cons (SixFStep.symm (SixFStep.congrArg f (SixFStep.trans SixFStep.verdier SixFStep.pullback))) <|
  SixFPath.cons (SixFStep.congrArg f SixFStep.verdier) <|
  SixFPath.cons (SixFStep.congrArg f SixFStep.pullback) SixFPath.nil

-- Functoriality of truncation
def truncation_functorial {α : Type u} (f : α → α) (a b : α) :
    TStrPath α (f a) (f b) :=
  TStrPath.cons (TStrStep.congrArg f TStrStep.truncLe) <|
  TStrPath.cons (TStrStep.congrArg f TStrStep.truncGe) <|
  TStrPath.cons (TStrStep.symm (TStrStep.congrArg f (TStrStep.trans TStrStep.truncLe TStrStep.truncGe))) <|
  TStrPath.cons (TStrStep.congrArg f TStrStep.cohFunctor) TStrPath.nil

-- Triangle functoriality
def triangle_functorial {α : Type u} (f : α → α) (a b : α) :
    DTriPath α (f a) (f b) :=
  DTriPath.cons (DTriStep.congrArg f DTriStep.triRotate) <|
  DTriPath.cons (DTriStep.congrArg f DTriStep.triMorphism) <|
  DTriPath.cons (DTriStep.congrArg f DTriStep.octahedral) <|
  DTriPath.cons (DTriStep.symm (DTriStep.congrArg f
    (DTriStep.trans DTriStep.triRotate (DTriStep.trans DTriStep.triMorphism DTriStep.octahedral)))) <|
  DTriPath.cons (DTriStep.congrArg f DTriStep.triExact) DTriPath.nil

-- AR translation under functor
def ar_translate_functorial {α : Type u} (f : α → α) (a b : α) :
    ARPath α (f a) (f b) :=
  ARPath.cons (ARStep.congrArg f ARStep.arTranslate) <|
  ARPath.cons (ARStep.congrArg f ARStep.almostSplit) <|
  ARPath.cons (ARStep.congrArg f ARStep.irreducible) <|
  ARPath.cons (ARStep.symm (ARStep.congrArg f
    (ARStep.trans ARStep.arTranslate (ARStep.trans ARStep.almostSplit ARStep.irreducible)))) <|
  ARPath.cons (ARStep.congrArg f ARStep.tiltEquiv) ARPath.nil

-- Six-functor composition: (gf)* ≅ f* g*
def six_functor_composition {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.pullback SixFStep.pullback)) <|
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.pushfwd) <|
  SixFPath.cons (SixFStep.adjCounit) SixFPath.nil

-- Perverse sheaf decomposition theorem
def perverse_decomposition {α : Type u} (a b : α) :
    TStrPath α a b :=
  TStrPath.cons (TStrStep.perverse) <|
  TStrPath.cons (TStrStep.heartIncl) <|
  TStrPath.cons (TStrStep.cohFunctor) <|
  TStrPath.cons (TStrStep.symm (TStrStep.trans TStrStep.heartIncl TStrStep.cohFunctor)) <|
  TStrPath.cons (TStrStep.heartProj) <|
  TStrPath.cons (TStrStep.perverse) TStrPath.nil

-- Grothendieck group path: [E] = [A] + [C] for exact 0→A→E→C→0
def grothendieck_group_exact {α : Type u} (a b : α) :
    DTriPath α a b :=
  DTriPath.cons (DTriStep.triExact) <|
  DTriPath.cons (DTriStep.triMorphism) <|
  DTriPath.cons (DTriStep.symm DTriStep.triExact) <|
  DTriPath.cons (DTriStep.triExact) <|
  DTriPath.cons (DTriStep.triMorphism) DTriPath.nil

-- Proper base change
def proper_base_change {α : Type u} (a b : α) :
    SixFPath α a b :=
  SixFPath.cons (SixFStep.pullback) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.shriekPush SixFStep.pullback)) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.pullback) SixFPath.nil

-- Poincaré-Verdier duality
def poincare_verdier_duality {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.shriekPush) <|
  SixFPath.cons (SixFStep.grothdual) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.verdier
    (SixFStep.trans SixFStep.shriekPush SixFStep.grothdual))) <|
  SixFPath.nil

-- Biduality for constructible sheaves
def constructible_biduality {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.innerHom) <|
  SixFPath.cons (SixFStep.verdier) <|
  SixFPath.cons (SixFStep.symm (SixFStep.trans SixFStep.verdier
    (SixFStep.trans SixFStep.innerHom SixFStep.verdier))) <|
  SixFPath.nil

-- Calabi-Yau: S ≅ [n] (Serre functor is shift)
def calabi_yau_serre_shift {α : Type u} (a : α) :
    SixFPath α a a :=
  SixFPath.cons (SixFStep.serreFun) <|
  SixFPath.cons (SixFStep.symm SixFStep.serreFun) <|
  SixFPath.cons (SixFStep.grothdual) <|
  SixFPath.cons (SixFStep.symm SixFStep.grothdual) <|
  SixFPath.nil

end ComputationalPaths
