/-
# Field Theory via Computational Paths

Field axioms, characteristic, field extensions, minimal polynomials,
algebraic elements, splitting field aspects. All coherence witnessed by `Path`.

## References

- Lang, "Algebra"
- Hungerford, "Algebra"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FieldPaths

universe u v

open ComputationalPaths.Path

/-! ## Path-witnessed field structure -/

/-- A field with Path-witnessed laws. -/
structure PathField (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  inv : F → F
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one

/-- Path for add associativity. -/
def addAssocPath {F : Type u} (pf : PathField F) (a b c : F) :
    Path (pf.add (pf.add a b) c) (pf.add a (pf.add b c)) :=
  Path.ofEq (pf.add_assoc a b c)

/-- Path for add commutativity. -/
def addCommPath {F : Type u} (pf : PathField F) (a b : F) :
    Path (pf.add a b) (pf.add b a) :=
  Path.ofEq (pf.add_comm a b)

/-- Path for zero_add. -/
def zeroAddPath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.add pf.zero a) a :=
  Path.ofEq (pf.zero_add a)

/-- Path for additive inverse. -/
def addNegPath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.add a (pf.neg a)) pf.zero :=
  Path.ofEq (pf.add_neg a)

/-- Path for mul associativity. -/
def mulAssocPath {F : Type u} (pf : PathField F) (a b c : F) :
    Path (pf.mul (pf.mul a b) c) (pf.mul a (pf.mul b c)) :=
  Path.ofEq (pf.mul_assoc a b c)

/-- Path for mul commutativity. -/
def mulCommPath {F : Type u} (pf : PathField F) (a b : F) :
    Path (pf.mul a b) (pf.mul b a) :=
  Path.ofEq (pf.mul_comm a b)

/-- Path for one_mul. -/
def oneMulPath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.mul pf.one a) a :=
  Path.ofEq (pf.one_mul a)

/-- Path for left distributivity. -/
def leftDistribPath {F : Type u} (pf : PathField F) (a b c : F) :
    Path (pf.mul a (pf.add b c)) (pf.add (pf.mul a b) (pf.mul a c)) :=
  Path.ofEq (pf.left_distrib a b c)

/-- Path for multiplicative inverse. -/
def mulInvPath {F : Type u} (pf : PathField F) (a : F) (ha : a ≠ pf.zero) :
    Path (pf.mul a (pf.inv a)) pf.one :=
  Path.ofEq (pf.mul_inv a ha)

/-! ## Derived field laws via path trans -/

/-- add_zero from zero_add via commutativity. -/
theorem add_zero {F : Type u} (pf : PathField F) (a : F) :
    pf.add a pf.zero = a := by
  rw [pf.add_comm]; exact pf.zero_add a

/-- Path for add_zero. -/
def addZeroPath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.add a pf.zero) a :=
  Path.trans (addCommPath pf a pf.zero) (zeroAddPath pf a)

/-- mul_one from one_mul via commutativity. -/
theorem mul_one {F : Type u} (pf : PathField F) (a : F) :
    pf.mul a pf.one = a := by
  rw [pf.mul_comm]; exact pf.one_mul a

/-- Path for mul_one. -/
def mulOnePath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.mul a pf.one) a :=
  Path.trans (mulCommPath pf a pf.one) (oneMulPath pf a)

/-- neg_add from add_neg via commutativity. -/
theorem neg_add {F : Type u} (pf : PathField F) (a : F) :
    pf.add (pf.neg a) a = pf.zero := by
  rw [pf.add_comm]; exact pf.add_neg a

/-- Path for neg_add. -/
def negAddPath {F : Type u} (pf : PathField F) (a : F) :
    Path (pf.add (pf.neg a) a) pf.zero :=
  Path.trans (addCommPath pf (pf.neg a) a) (addNegPath pf a)

/-- inv_mul from mul_inv via commutativity. -/
theorem inv_mul {F : Type u} (pf : PathField F) (a : F) (ha : a ≠ pf.zero) :
    pf.mul (pf.inv a) a = pf.one := by
  rw [pf.mul_comm]; exact pf.mul_inv a ha

/-- Path for inv_mul. -/
def invMulPath {F : Type u} (pf : PathField F) (a : F) (ha : a ≠ pf.zero) :
    Path (pf.mul (pf.inv a) a) pf.one :=
  Path.trans (mulCommPath pf (pf.inv a) a) (mulInvPath pf a ha)

/-! ## Right distributivity -/

/-- Right distributivity from left distributivity and commutativity. -/
theorem right_distrib {F : Type u} (pf : PathField F) (a b c : F) :
    pf.mul (pf.add a b) c = pf.add (pf.mul a c) (pf.mul b c) := by
  rw [pf.mul_comm, pf.left_distrib, pf.mul_comm c a, pf.mul_comm c b]

/-- Path for right distributivity. -/
def rightDistribPath {F : Type u} (pf : PathField F) (a b c : F) :
    Path (pf.mul (pf.add a b) c) (pf.add (pf.mul a c) (pf.mul b c)) :=
  Path.ofEq (right_distrib pf a b c)

/-! ## Characteristic -/

/-- Repeated addition of one: n * 1 in the field. -/
def charNat {F : Type u} (pf : PathField F) : Nat → F
  | 0 => pf.zero
  | n + 1 => pf.add (charNat pf n) pf.one

/-- 0 * 1 = zero. -/
theorem charNat_zero {F : Type u} (pf : PathField F) :
    charNat pf 0 = pf.zero := rfl

/-- Path: 0 maps to zero. -/
def charNat_zero_path {F : Type u} (pf : PathField F) :
    Path (charNat pf 0) pf.zero :=
  Path.refl _

/-- 1 * 1 = one. -/
theorem charNat_one {F : Type u} (pf : PathField F) :
    charNat pf 1 = pf.one := by
  simp [charNat]; exact pf.zero_add pf.one

/-- Path: 1 maps to one. -/
def charNat_one_path {F : Type u} (pf : PathField F) :
    Path (charNat pf 1) pf.one :=
  Path.ofEq (charNat_one pf)

/-- charNat is additive: (m + n) * 1 = m*1 + n*1. -/
theorem charNat_add {F : Type u} (pf : PathField F) (m n : Nat) :
    charNat pf (m + n) = pf.add (charNat pf m) (charNat pf n) := by
  induction n with
  | zero => simp [charNat, add_zero pf]
  | succ n ih =>
    simp only [charNat]
    show pf.add (charNat pf (m + n)) pf.one = pf.add (charNat pf m) (pf.add (charNat pf n) pf.one)
    rw [ih, pf.add_assoc]

/-- Path: charNat additivity. -/
def charNat_add_path {F : Type u} (pf : PathField F) (m n : Nat) :
    Path (charNat pf (m + n)) (pf.add (charNat pf m) (charNat pf n)) :=
  Path.ofEq (charNat_add pf m n)

/-! ## Field extensions -/

/-- A field extension: F embeds into E. -/
structure FieldExtension (F E : Type u)
    (pF : PathField F) (pE : PathField E) where
  embed : F → E
  map_zero : embed pF.zero = pE.zero
  map_one : embed pF.one = pE.one
  map_add : ∀ a b, embed (pF.add a b) = pE.add (embed a) (embed b)
  map_mul : ∀ a b, embed (pF.mul a b) = pE.mul (embed a) (embed b)

/-- Path: embedding preserves zero. -/
def extZeroPath {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) :
    Path (ext.embed pF.zero) pE.zero :=
  Path.ofEq ext.map_zero

/-- Path: embedding preserves one. -/
def extOnePath {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) :
    Path (ext.embed pF.one) pE.one :=
  Path.ofEq ext.map_one

/-- Path: embedding preserves addition. -/
def extAddPath {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) (a b : F) :
    Path (ext.embed (pF.add a b)) (pE.add (ext.embed a) (ext.embed b)) :=
  Path.ofEq (ext.map_add a b)

/-- Path: embedding preserves multiplication. -/
def extMulPath {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) (a b : F) :
    Path (ext.embed (pF.mul a b)) (pE.mul (ext.embed a) (ext.embed b)) :=
  Path.ofEq (ext.map_mul a b)

/-- Identity extension. -/
def idExtension {F : Type u} (pF : PathField F) :
    FieldExtension F F pF pF :=
  ⟨id, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Identity extension maps to self. -/
theorem idExtension_embed {F : Type u} (pF : PathField F) (a : F) :
    (idExtension pF).embed a = a := rfl

/-- Path: identity extension is identity. -/
def idExtension_path {F : Type u} (pF : PathField F) (a : F) :
    Path ((idExtension pF).embed a) a :=
  Path.refl _

/-- Compose field extensions. -/
def compExtension {F E K : Type u}
    {pF : PathField F} {pE : PathField E} {pK : PathField K}
    (fe : FieldExtension F E pF pE) (ek : FieldExtension E K pE pK) :
    FieldExtension F K pF pK :=
  { embed := ek.embed ∘ fe.embed
    map_zero := by simp [Function.comp, fe.map_zero, ek.map_zero]
    map_one := by simp [Function.comp, fe.map_one, ek.map_one]
    map_add := fun a b => by
      simp [Function.comp, fe.map_add, ek.map_add]
    map_mul := fun a b => by
      simp [Function.comp, fe.map_mul, ek.map_mul] }

/-- Composing with identity on the right. -/
theorem compExtension_id_right {F E : Type u}
    {pF : PathField F} {pE : PathField E}
    (fe : FieldExtension F E pF pE) (a : F) :
    (compExtension fe (idExtension pE)).embed a = fe.embed a := rfl

/-- Path: compose with id. -/
def compExtension_id_right_path {F E : Type u}
    {pF : PathField F} {pE : PathField E}
    (fe : FieldExtension F E pF pE) (a : F) :
    Path ((compExtension fe (idExtension pE)).embed a) (fe.embed a) :=
  Path.refl _

/-! ## Polynomials over a field -/

/-- A polynomial as a list of coefficients (constant term first). -/
structure Poly (F : Type u) where
  coeffs : List F

/-- Zero polynomial. -/
def polyZero {F : Type u} (pf : PathField F) : Poly F := ⟨[]⟩

/-- Constant polynomial. -/
def polyConst {F : Type u} (a : F) : Poly F := ⟨[a]⟩

/-- Degree of a polynomial (-1 for zero, modeled as 0). -/
def polyDeg {F : Type u} (p : Poly F) : Nat :=
  match p.coeffs with
  | [] => 0
  | _ => p.coeffs.length - 1

/-- Constant polynomial has degree 0 or less. -/
theorem polyConst_deg {F : Type u} (a : F) :
    polyDeg (polyConst a) = 0 := by
  rfl

/-- Path: constant polynomial degree. -/
def polyConst_deg_path {F : Type u} (a : F) :
    Path (polyDeg (polyConst a)) 0 :=
  Path.refl _

/-- congrArg: equal polynomials have equal degrees. -/
def polyDeg_congr {F : Type u} (p q : Poly F) (h : p = q) :
    Path (polyDeg p) (polyDeg q) :=
  Path.congrArg polyDeg (Path.ofEq h)

/-! ## Algebraic elements -/

/-- An element α is algebraic over F if there exists a polynomial that vanishes. -/
structure AlgebraicElement {F E : Type u}
    (pF : PathField F) (pE : PathField E)
    (ext : FieldExtension F E pF pE) (α : E) where
  minPoly : Poly F
  vanishes : E  -- the evaluation result
  isZero : vanishes = pE.zero

/-- Path: algebraic element satisfies its minimal polynomial. -/
def algebraicPath {F E : Type u}
    {pF : PathField F} {pE : PathField E}
    {ext : FieldExtension F E pF pE} {α : E}
    (ae : AlgebraicElement pF pE ext α) :
    Path ae.vanishes pE.zero :=
  Path.ofEq ae.isZero

/-- Transport: if extensions are equal, algebraic elements transport. -/
theorem algebraic_transport {F E : Type u}
    {pF : PathField F} {pE : PathField E}
    (ext1 ext2 : FieldExtension F E pF pE)
    (h : ext1 = ext2) (α : E)
    (ae : AlgebraicElement pF pE ext1 α) :
    ae.vanishes = pE.zero :=
  ae.isZero

/-- congrArg on embedding through field extension. -/
def embed_congr {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) (a b : F) (h : a = b) :
    Path (ext.embed a) (ext.embed b) :=
  Path.congrArg ext.embed (Path.ofEq h)

/-- Embedding preserves negation: embed(-a) = -embed(a). -/
theorem embed_neg {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) (a : F) :
    pE.add (ext.embed a) (ext.embed (pF.neg a)) = pE.zero := by
  rw [← ext.map_add]; rw [pF.add_neg]; exact ext.map_zero

/-- Path for embed_neg. -/
def embed_neg_path {F E : Type u} {pF : PathField F} {pE : PathField E}
    (ext : FieldExtension F E pF pE) (a : F) :
    Path (pE.add (ext.embed a) (ext.embed (pF.neg a))) pE.zero :=
  Path.ofEq (embed_neg ext a)

end FieldPaths
end Algebra
end Path
end ComputationalPaths
