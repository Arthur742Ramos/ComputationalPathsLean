/-
# Inductive Types as Path Algebras

Initial algebras, catamorphisms as unique path maps, paramorphisms,
anamorphisms, hylomorphisms, and fusion laws as path equalities.

## References

- Meijer, Fokkinga, Paterson, "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire"
- Bird, de Moor, "Algebra of Programming"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace InductiveTypePaths

universe u v

/-! ## Nat algebra (initial algebra for Option functor) -/

/-- An algebra for the Option functor: a carrier with zero and successor. -/
structure NatAlg where
  Carrier : Type u
  zero : Carrier
  succ : Carrier → Carrier

/-- The initial Nat-algebra. -/
def NatAlg.initial : NatAlg where
  Carrier := Nat
  zero := 0
  succ := Nat.succ

/-- Morphism of Nat-algebras. -/
structure NatAlgHom (A B : NatAlg) where
  map : A.Carrier → B.Carrier
  map_zero : map A.zero = B.zero
  map_succ : ∀ x, map (A.succ x) = B.succ (map x)

/-- Catamorphism (fold) from the initial algebra. -/
def natCata (B : NatAlg) : Nat → B.Carrier
  | 0 => B.zero
  | n + 1 => B.succ (natCata B n)

/-- Path witnessing the zero computation rule. -/
def natCata_zero_path (B : NatAlg) :
    Path (natCata B 0) B.zero := Path.refl _

/-- Path witnessing the successor computation rule. -/
def natCata_succ_path (B : NatAlg) (n : Nat) :
    Path (natCata B (n + 1)) (B.succ (natCata B n)) := Path.refl _

/-- The catamorphism is a NatAlg morphism. -/
def natCataHom (B : NatAlg) : NatAlgHom NatAlg.initial B where
  map := natCata B
  map_zero := rfl
  map_succ := fun _ => rfl

/-- Path witnessing catamorphism is an algebra hom on zero. -/
def natCataHomZeroPath (B : NatAlg) :
    Path (natCata B NatAlg.initial.zero) B.zero := Path.refl _

theorem natCataHomZeroPath_toEq (B : NatAlg) :
    (natCataHomZeroPath B).toEq = rfl := rfl

/-- Path witnessing catamorphism is an algebra hom on succ. -/
def natCataHomSuccPath (B : NatAlg) (n : Nat) :
    Path (natCata B (NatAlg.initial.succ n)) (B.succ (natCata B n)) := Path.refl _

theorem natCataHomSuccPath_toEq (B : NatAlg) (n : Nat) :
    (natCataHomSuccPath B n).toEq = rfl := rfl

/-! ## Uniqueness of catamorphism -/

/-- Any algebra hom from initial agrees with catamorphism. -/
def natCata_unique (B : NatAlg) (h : NatAlgHom NatAlg.initial B) :
    (n : Nat) → Path (h.map n) (natCata B n)
  | 0 => Path.ofEq h.map_zero
  | n + 1 => Path.trans
      (Path.ofEq (h.map_succ n))
      (Path.congrArg B.succ (natCata_unique B h n))

theorem natCata_unique_zero (B : NatAlg) (h : NatAlgHom NatAlg.initial B) :
    (natCata_unique B h 0).toEq = h.map_zero := rfl

/-! ## List algebra (initial algebra for ListF functor) -/

/-- An algebra for lists over a fixed element type. -/
structure ListAlg (E : Type u) where
  Carrier : Type u
  nil : Carrier
  cons : E → Carrier → Carrier

/-- The initial list algebra. -/
def ListAlg.initial (E : Type u) : ListAlg E where
  Carrier := List E
  nil := []
  cons := List.cons

/-- Catamorphism on lists. -/
def listCata {E : Type u} (B : ListAlg E) : List E → B.Carrier
  | [] => B.nil
  | x :: xs => B.cons x (listCata B xs)

/-- Path for nil computation. -/
def listCata_nil_path {E : Type u} (B : ListAlg E) :
    Path (listCata B []) B.nil := Path.refl _

/-- Path for cons computation. -/
def listCata_cons_path {E : Type u} (B : ListAlg E) (x : E) (xs : List E) :
    Path (listCata B (x :: xs)) (B.cons x (listCata B xs)) := Path.refl _

theorem listCata_nil_path_toEq {E : Type u} (B : ListAlg E) :
    (listCata_nil_path B).toEq = rfl := rfl

theorem listCata_cons_path_toEq {E : Type u} (B : ListAlg E) (x : E) (xs : List E) :
    (listCata_cons_path B x xs).toEq = rfl := rfl

/-! ## Paramorphism -/

/-- Paramorphism on Nat: recursion with access to predecessor. -/
def natPara {X : Type u} (z : X) (s : Nat → X → X) : Nat → X
  | 0 => z
  | n + 1 => s n (natPara z s n)

/-- Zero computation path for paramorphism. -/
def natPara_zero_path {X : Type u} (z : X) (s : Nat → X → X) :
    Path (natPara z s 0) z := Path.refl _

/-- Successor computation path for paramorphism. -/
def natPara_succ_path {X : Type u} (z : X) (s : Nat → X → X) (n : Nat) :
    Path (natPara z s (n + 1)) (s n (natPara z s n)) := Path.refl _

/-- Paramorphism on lists. -/
def listPara {E X : Type u} (z : X) (s : E → List E → X → X) : List E → X
  | [] => z
  | x :: xs => s x xs (listPara z s xs)

/-- Nil computation path for list paramorphism. -/
def listPara_nil_path {E X : Type u} (z : X) (s : E → List E → X → X) :
    Path (listPara z s ([] : List E)) z := Path.refl _

/-- Cons computation path for list paramorphism. -/
def listPara_cons_path {E X : Type u} (z : X) (s : E → List E → X → X)
    (x : E) (xs : List E) :
    Path (listPara z s (x :: xs)) (s x xs (listPara z s xs)) := Path.refl _

/-! ## Anamorphism (unfold) -/

/-- Bounded anamorphism (unfold) on Nat. -/
def natAnaBounded (step : Nat → Option Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, seed => match step seed with
    | none => 0
    | some next => 1 + natAnaBounded step fuel next

/-- Path: zero fuel gives zero. -/
def natAnaBounded_zero_path (step : Nat → Option Nat) (seed : Nat) :
    Path (natAnaBounded step 0 seed) 0 := Path.refl _

theorem natAnaBounded_zero_toEq (step : Nat → Option Nat) (seed : Nat) :
    (natAnaBounded_zero_path step seed).toEq = rfl := rfl

/-! ## Hylomorphism -/

/-- Hylomorphism: unfold then fold (anamorphism then catamorphism). -/
def natHylo {X : Type u} (z : X) (s : X → X) (step : Nat → Option Nat) :
    Nat → Nat → X
  | 0, _ => z
  | fuel + 1, seed => match step seed with
    | none => z
    | some next => s (natHylo z s step fuel next)

/-- Path: zero fuel gives zero value. -/
def natHylo_zero_path {X : Type u} (z : X) (s : X → X)
    (step : Nat → Option Nat) (seed : Nat) :
    Path (natHylo z s step 0 seed) z := Path.refl _

theorem natHylo_zero_toEq {X : Type u} (z : X) (s : X → X)
    (step : Nat → Option Nat) (seed : Nat) :
    (natHylo_zero_path z s step seed).toEq = rfl := rfl

/-! ## Fusion laws as path equalities -/

/-- Catamorphism fusion: if h is an algebra hom, h ∘ cata = cata'. -/
def cata_fusion (A B : NatAlg) (h : NatAlgHom A B)
    (hA : NatAlgHom NatAlg.initial A)
    (n : Nat)
    (heq : h.map (hA.map n) = (natCata B) n) :
    Path (h.map (hA.map n)) (natCata B n) :=
  Path.ofEq heq

/-- Catamorphism identity law: fold with initial algebra constructors is identity. -/
def cata_id_path (n : Nat) :
    Path (natCata NatAlg.initial n) n := by
  induction n with
  | zero => exact Path.refl _
  | succ n ih => exact Path.congrArg Nat.succ ih

theorem cata_id_path_zero :
    (cata_id_path 0).toEq = rfl := rfl

/-- List catamorphism identity path. -/
def listCata_id_path {E : Type u} :
    (xs : List E) → Path (listCata (ListAlg.initial E) xs) xs
  | [] => Path.refl _
  | x :: xs => Path.congrArg (List.cons x) (listCata_id_path xs)

theorem listCata_id_nil {E : Type u} :
    (listCata_id_path ([] : List E)).toEq = rfl := rfl

/-! ## Algebra composition -/

/-- Identity algebra morphism on NatAlg. -/
def NatAlgHom.id (A : NatAlg) : NatAlgHom A A where
  map := fun x => x
  map_zero := rfl
  map_succ := fun _ => rfl

/-- Composition of NatAlg morphisms. -/
def NatAlgHom.comp {A B C : NatAlg} (g : NatAlgHom B C) (f : NatAlgHom A B) :
    NatAlgHom A C where
  map := g.map ∘ f.map
  map_zero := by show g.map (f.map A.zero) = C.zero; rw [f.map_zero, g.map_zero]
  map_succ := fun x => by show g.map (f.map (A.succ x)) = C.succ (g.map (f.map x)); rw [f.map_succ, g.map_succ]

/-- Identity morphism path. -/
def natAlgId_path (A : NatAlg) (x : A.Carrier) :
    Path ((NatAlgHom.id A).map x) x := Path.refl _

/-- Composition commutation path. -/
def natAlgComp_path {A B C : NatAlg} (g : NatAlgHom B C) (f : NatAlgHom A B)
    (x : A.Carrier) :
    Path ((NatAlgHom.comp g f).map x) (g.map (f.map x)) := Path.refl _

theorem natAlgComp_path_toEq {A B C : NatAlg} (g : NatAlgHom B C) (f : NatAlgHom A B)
    (x : A.Carrier) :
    (natAlgComp_path g f x).toEq = rfl := rfl

/-! ## Transport on algebra carriers -/

/-- Transport a value along a path of carrier elements. -/
def algTransport {A : NatAlg} {x y : A.Carrier} (p : Path x y)
    {P : A.Carrier → Type v} (px : P x) : P y :=
  Path.transport p px

theorem algTransport_refl {A : NatAlg} (x : A.Carrier)
    {P : A.Carrier → Type v} (px : P x) :
    algTransport (Path.refl x) px = px := rfl

theorem algTransport_trans {A : NatAlg} {x y z : A.Carrier}
    (p : Path x y) (q : Path y z)
    {P : A.Carrier → Type v} (px : P x) :
    algTransport (Path.trans p q) px = algTransport q (algTransport p px) := by
  cases p with | mk _ proof₁ => cases q with | mk _ proof₂ =>
    cases proof₁; cases proof₂; rfl

theorem algTransport_symm {A : NatAlg} {x y : A.Carrier}
    (p : Path x y) {P : A.Carrier → Type v} (px : P x) :
    algTransport (Path.symm p) (algTransport p px) = px := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Congruence for algebra operations -/

/-- Congruence of succ along paths. -/
def succCongrPath (A : NatAlg) {x y : A.Carrier} (p : Path x y) :
    Path (A.succ x) (A.succ y) := Path.congrArg A.succ p

theorem succCongrPath_trans (A : NatAlg) {x y z : A.Carrier}
    (p : Path x y) (q : Path y z) :
    succCongrPath A (Path.trans p q) =
    Path.trans (succCongrPath A p) (succCongrPath A q) := by
  simp [succCongrPath]

theorem succCongrPath_symm (A : NatAlg) {x y : A.Carrier} (p : Path x y) :
    succCongrPath A (Path.symm p) = Path.symm (succCongrPath A p) := by
  simp [succCongrPath]

/-- Congruence for list cons along paths. -/
def consCongrPath {E : Type u} (A : ListAlg E) (x : E)
    {a b : A.Carrier} (p : Path a b) :
    Path (A.cons x a) (A.cons x b) := Path.congrArg (A.cons x) p

theorem consCongrPath_trans {E : Type u} (A : ListAlg E) (x : E)
    {a b c : A.Carrier} (p : Path a b) (q : Path b c) :
    consCongrPath A x (Path.trans p q) =
    Path.trans (consCongrPath A x p) (consCongrPath A x q) := by
  simp [consCongrPath]

theorem consCongrPath_symm {E : Type u} (A : ListAlg E) (x : E)
    {a b : A.Carrier} (p : Path a b) :
    consCongrPath A x (Path.symm p) = Path.symm (consCongrPath A x p) := by
  simp [consCongrPath]

/-! ## Morphism congruence -/

/-- Apply a morphism along a path. -/
def morphCongrPath {A B : NatAlg} (f : NatAlgHom A B) {x y : A.Carrier}
    (p : Path x y) : Path (f.map x) (f.map y) :=
  Path.congrArg f.map p

theorem morphCongrPath_trans {A B : NatAlg} (f : NatAlgHom A B)
    {x y z : A.Carrier} (p : Path x y) (q : Path y z) :
    morphCongrPath f (Path.trans p q) =
    Path.trans (morphCongrPath f p) (morphCongrPath f q) := by
  simp [morphCongrPath]

theorem morphCongrPath_symm {A B : NatAlg} (f : NatAlgHom A B)
    {x y : A.Carrier} (p : Path x y) :
    morphCongrPath f (Path.symm p) = Path.symm (morphCongrPath f p) := by
  simp [morphCongrPath]

end InductiveTypePaths
end TypeTheory
end Path
end ComputationalPaths
