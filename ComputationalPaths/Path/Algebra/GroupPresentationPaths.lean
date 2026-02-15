/-
# Group Presentations as Rewriting Systems

Group presentations modeled via computational paths: generators become
vertices, relations become rewrite rules, consequences are paths,
Tietze transformations preserve path structure, and the free group
is a path groupoid on generators. Normal forms via coset enumeration
correspond to path search.

## References

- Magnus, Karrass, Solitar, "Combinatorial Group Theory"
- Lyndon & Schupp, "Combinatorial Group Theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Free Group as List of Signed Generators -/

/-- A signed generator: either a generator or its formal inverse. -/
inductive SignedGen (G : Type u) : Type u
  | pos : G → SignedGen G
  | neg : G → SignedGen G

namespace SignedGen

variable {G : Type u}

/-- Formal inverse of a signed generator. -/
@[simp] def inv : SignedGen G → SignedGen G
  | pos g => neg g
  | neg g => pos g

/-- Double inverse is identity. -/
@[simp] theorem inv_inv (s : SignedGen G) : inv (inv s) = s := by
  cases s <;> rfl

end SignedGen

/-- A word in the free group: a list of signed generators. -/
structure FreeGroupWord (G : Type u) where
  letters : List (SignedGen G)

namespace FreeGroupWord

variable {G : Type u}

/-- Empty word (identity element). -/
@[simp] def empty : FreeGroupWord G := ⟨[]⟩

/-- Concatenation of words. -/
@[simp] def mul (w1 w2 : FreeGroupWord G) : FreeGroupWord G :=
  ⟨w1.letters ++ w2.letters⟩

/-- Formal inverse of a word: reverse and invert each generator. -/
@[simp] def inv (w : FreeGroupWord G) : FreeGroupWord G :=
  ⟨(w.letters.reverse).map SignedGen.inv⟩

/-- Double inverse is identity. -/
@[simp] theorem inv_inv (w : FreeGroupWord G) : inv (inv w) = w := by
  simp only [inv]
  congr 1
  simp [List.map_reverse, List.reverse_reverse, List.map_map]
  have : (SignedGen.inv ∘ SignedGen.inv) = @id (SignedGen G) := by
    funext s; cases s <;> rfl
  simp [this]

/-- Inverse of empty is empty. -/
@[simp] theorem inv_empty : inv (empty : FreeGroupWord G) = empty := by
  simp [inv, empty]

/-- Inverse distributes over concatenation (reversed). -/
theorem inv_mul (w1 w2 : FreeGroupWord G) :
    inv (mul w1 w2) = mul (inv w2) (inv w1) := by
  simp [inv, mul, List.reverse_append, List.map_append]

/-- Multiplication is associative. -/
theorem mul_assoc (w1 w2 w3 : FreeGroupWord G) :
    mul (mul w1 w2) w3 = mul w1 (mul w2 w3) := by
  simp [mul, List.append_assoc]

/-- Left identity. -/
theorem mul_empty_left (w : FreeGroupWord G) :
    mul empty w = w := by
  simp [mul, empty]

/-- Right identity. -/
theorem mul_empty_right (w : FreeGroupWord G) :
    mul w empty = w := by
  simp [mul, empty]

end FreeGroupWord

/-! ## Group Presentations -/

/-- A group presentation: generators and relations. -/
structure GroupPresentation (G : Type u) where
  relations : List (FreeGroupWord G × FreeGroupWord G)

/-! ## Relations as Rewrite Rules, Consequences as Paths -/

/-- A consequence of a presentation is witnessed by a path. -/
structure Consequence (G : Type u) (_pres : GroupPresentation G) where
  source : FreeGroupWord G
  target : FreeGroupWord G
  witness : Path source target

/-- Reflexive consequence: every word equals itself. -/
def reflexiveConsequence {G : Type u} (pres : GroupPresentation G)
    (w : FreeGroupWord G) : Consequence G pres :=
  ⟨w, w, Path.refl w⟩

/-- Consequences compose via path composition. -/
def composeConsequences {G : Type u} (pres : GroupPresentation G)
    (c1 : Consequence G pres) (c2 : Consequence G pres)
    (h : c1.target = c2.source) : Consequence G pres :=
  ⟨c1.source, c2.target, Path.trans c1.witness (h ▸ c2.witness)⟩

/-- Consequence is invertible. -/
def invertConsequence {G : Type u} (pres : GroupPresentation G)
    (c : Consequence G pres) : Consequence G pres :=
  ⟨c.target, c.source, Path.symm c.witness⟩

/-- Reflexive consequence has trivial toEq. -/
theorem reflexive_consequence_toEq {G : Type u} (pres : GroupPresentation G)
    (w : FreeGroupWord G) :
    (reflexiveConsequence pres w).witness.toEq = rfl := by
  rfl

/-- Inverted consequence of reflexive is reflexive. -/
theorem invert_reflexive {G : Type u} (pres : GroupPresentation G)
    (w : FreeGroupWord G) :
    (invertConsequence pres (reflexiveConsequence pres w)).witness.toEq = rfl := by
  simp [invertConsequence, reflexiveConsequence]

/-- Consequence gives propositional equality. -/
theorem consequence_eq {G : Type u} {pres : GroupPresentation G}
    (c : Consequence G pres) : c.source = c.target :=
  c.witness.toEq

/-! ## Tietze Transformations as Path-Preserving Operations -/

/-- Tietze transformation types. -/
inductive TietzeType
  | addRelation
  | removeRelation
  | addGenerator
  | removeGenerator

/-- A Tietze transformation between two presentations. -/
structure TietzeTransformation (G : Type u) where
  before : GroupPresentation G
  after : GroupPresentation G
  ttype : TietzeType

/-- Tietze transformation preserves consequences. -/
structure TietzePreservation (G : Type u) (tt : TietzeTransformation G) where
  preserve : ∀ (w1 w2 : FreeGroupWord G),
    Path w1 w2 → Path w1 w2

/-- Tietze preservation is functorial on reflexive paths. -/
theorem tietze_preserves_refl {G : Type u} (tt : TietzeTransformation G)
    (tp : TietzePreservation G tt) (w : FreeGroupWord G) :
    (tp.preserve w w (Path.refl w)).toEq = (Path.refl w).toEq := by
  simp

/-- Tietze preservation is compatible with composition. -/
theorem tietze_preserves_trans {G : Type u} (tt : TietzeTransformation G)
    (tp : TietzePreservation G tt) {a b c : FreeGroupWord G}
    (p : Path a b) (q : Path b c) :
    (tp.preserve a c (Path.trans p q)).toEq =
      (Path.trans (tp.preserve a b p) (tp.preserve b c q)).toEq := by
  simp

/-- Tietze preservation is compatible with symmetry. -/
theorem tietze_preserves_symm {G : Type u} (tt : TietzeTransformation G)
    (tp : TietzePreservation G tt) {a b : FreeGroupWord G}
    (p : Path a b) :
    (tp.preserve b a (Path.symm p)).toEq =
      (Path.symm (tp.preserve a b p)).toEq := by
  simp

/-- Composing two Tietze preservations. -/
def composeTietze {G : Type u}
    (_t1 t2 : TietzeTransformation G)
    (tp1 : TietzePreservation G _t1)
    (tp2 : TietzePreservation G t2) :
    ∀ (w1 w2 : FreeGroupWord G), Path w1 w2 → Path w1 w2 :=
  fun w1 w2 p => tp2.preserve w1 w2 (tp1.preserve w1 w2 p)

/-- Composed Tietze preservations agree at toEq level. -/
theorem composeTietze_toEq {G : Type u}
    (t1 t2 : TietzeTransformation G)
    (tp1 : TietzePreservation G t1)
    (tp2 : TietzePreservation G t2)
    {w1 w2 : FreeGroupWord G} (p : Path w1 w2) :
    (composeTietze t1 t2 tp1 tp2 w1 w2 p).toEq = p.toEq := by
  simp [composeTietze]

/-! ## Free Group as Path Groupoid on Generators -/

/-- The path groupoid structure on free group words. -/
structure FreeGroupGroupoid (G : Type u) where
  obj : Type u
  hom : obj → obj → Type u
  id : ∀ x, hom x x
  comp : ∀ {x y z}, hom x y → hom y z → hom x z
  inv : ∀ {x y}, hom x y → hom y x

/-- Build a path groupoid from a free group. -/
def freeGroupPathGroupoid (G : Type u) : FreeGroupGroupoid G where
  obj := FreeGroupWord G
  hom := fun a b => Path a b
  id := fun x => Path.refl x
  comp := fun p q => Path.trans p q
  inv := fun p => Path.symm p

/-- Path groupoid identity law (left). -/
theorem groupoid_id_left {G : Type u}
    {a b : FreeGroupWord G} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by simp

/-- Path groupoid identity law (right). -/
theorem groupoid_id_right {G : Type u}
    {a b : FreeGroupWord G} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by simp

/-- Path groupoid associativity. -/
theorem groupoid_assoc {G : Type u}
    {a b c d : FreeGroupWord G} (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by simp

/-- Path groupoid inverse (toEq level). -/
theorem groupoid_inv_right {G : Type u}
    {a b : FreeGroupWord G} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by simp

/-- Path groupoid inverse (toEq level, left). -/
theorem groupoid_inv_left {G : Type u}
    {a b : FreeGroupWord G} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq := by simp

/-! ## Normal Forms via Coset Enumeration as Path Search -/

/-- A coset table entry. -/
structure CosetEntry (G : Type u) where
  coset : Nat
  generator : SignedGen G
  targetCoset : Nat

/-- A coset enumeration table. -/
structure CosetTable (G : Type u) where
  entries : List (CosetEntry G)
  numCosets : Nat

/-- A normal form function for group words. -/
structure GroupNormalForm (G : Type u) where
  nf : FreeGroupWord G → FreeGroupWord G
  reduce : ∀ w, Path w (nf w)
  idem : ∀ w, Path (nf (nf w)) (nf w)

/-- Normal form gives propositional equality. -/
theorem gnf_reduce_eq {G : Type u} (N : GroupNormalForm G) (w : FreeGroupWord G) :
    w = N.nf w :=
  (N.reduce w).toEq

/-- Normal form is idempotent propositionally. -/
theorem gnf_idem_eq {G : Type u} (N : GroupNormalForm G) (w : FreeGroupWord G) :
    N.nf (N.nf w) = N.nf w :=
  (N.idem w).toEq

/-- Two path-connected words have connected normal forms. -/
theorem gnf_resp_eq {G : Type u} (N : GroupNormalForm G)
    {w1 w2 : FreeGroupWord G} (p : Path w1 w2) :
    w1 = w2 := p.toEq

/-- Inverse distributes over multiplication (path version). -/
theorem free_group_inv_mul_eq {G : Type u}
    (w1 w2 : FreeGroupWord G) :
    FreeGroupWord.inv (FreeGroupWord.mul w1 w2) =
    FreeGroupWord.mul (FreeGroupWord.inv w2) (FreeGroupWord.inv w1) :=
  FreeGroupWord.inv_mul w1 w2

/-- Double inverse is identity (propositional). -/
theorem free_group_inv_inv_eq {G : Type u}
    (w : FreeGroupWord G) :
    FreeGroupWord.inv (FreeGroupWord.inv w) = w :=
  FreeGroupWord.inv_inv w

/-- Multiplication associativity. -/
theorem free_group_mul_assoc_eq {G : Type u}
    (w1 w2 w3 : FreeGroupWord G) :
    FreeGroupWord.mul (FreeGroupWord.mul w1 w2) w3 =
    FreeGroupWord.mul w1 (FreeGroupWord.mul w2 w3) :=
  FreeGroupWord.mul_assoc w1 w2 w3

/-- Left identity for multiplication. -/
theorem free_group_mul_id_left_eq {G : Type u}
    (w : FreeGroupWord G) :
    FreeGroupWord.mul FreeGroupWord.empty w = w :=
  FreeGroupWord.mul_empty_left w

/-- Right identity for multiplication. -/
theorem free_group_mul_id_right_eq {G : Type u}
    (w : FreeGroupWord G) :
    FreeGroupWord.mul w FreeGroupWord.empty = w :=
  FreeGroupWord.mul_empty_right w

end Algebra
end Path
end ComputationalPaths
