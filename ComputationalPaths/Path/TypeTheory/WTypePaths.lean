/-
# W-types via Computational Paths

Well-founded trees modeled through computational paths:
W-type recursion, path induction, initiality, algebra morphisms,
path-based well-founded recursion, and W-type eliminators.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace WTypePaths

universe u v

/-! ## W-type as well-founded tree -/

/-- A well-founded tree type parameterized by shapes and arities. -/
inductive WTree (S : Type u) (ar : S → Type u) : Type u where
  | node : (s : S) → (ar s → WTree S ar) → WTree S ar

/-- Algebra for the polynomial endofunctor of a W-type. -/
structure WAlgebra (S : Type u) (ar : S → Type u) where
  Carrier : Type u
  op : (s : S) → (ar s → Carrier) → Carrier

/-- The canonical W-algebra whose carrier is the W-type itself. -/
def WTree.initialAlg (S : Type u) (ar : S → Type u) : WAlgebra S ar where
  Carrier := WTree S ar
  op := WTree.node

/-- Morphism between W-algebras. -/
structure WAlgHom (S : Type u) (ar : S → Type u) (A B : WAlgebra S ar) where
  map : A.Carrier → B.Carrier
  commutes : ∀ (s : S) (f : ar s → A.Carrier),
    map (A.op s f) = B.op s (fun p => map (f p))

/-! ## Reflexivity and congruence paths for W-trees -/

/-- Reflexivity path for a W-tree node. -/
def wtreeReflPath {S : Type u} {ar : S → Type u} (w : WTree S ar) :
    Path w w := Path.refl w

theorem wtreeReflPath_toEq {S : Type u} {ar : S → Type u} (w : WTree S ar) :
    (wtreeReflPath w).toEq = rfl := rfl

/-- Double reflexivity (trans refl refl). -/
def wtreeDoubleRefl {S : Type u} {ar : S → Type u} (w : WTree S ar) :
    Path w w := Path.trans (Path.refl w) (Path.refl w)

theorem wtreeDoubleRefl_toEq {S : Type u} {ar : S → Type u} (w : WTree S ar) :
    (wtreeDoubleRefl w).toEq = rfl := rfl

/-- Congruence: equal children give equal nodes. -/
def nodeCongrChildren {S : Type u} {ar : S → Type u} (s : S)
    {f g : ar s → WTree S ar} (h : f = g) :
    Path (WTree.node s f) (WTree.node s g) :=
  Path.congrArg (WTree.node s) (Path.ofEq h)

theorem nodeCongrChildren_refl {S : Type u} {ar : S → Type u} (s : S)
    (f : ar s → WTree S ar) :
    (nodeCongrChildren s (rfl : f = f)).toEq = rfl := rfl

/-- Symmetry of node congruence. -/
theorem nodeCongrChildren_symm {S : Type u} {ar : S → Type u} (s : S)
    {f g : ar s → WTree S ar} (h : f = g) :
    Path.symm (nodeCongrChildren s h) = nodeCongrChildren s h.symm := by
  subst h; simp [nodeCongrChildren]

/-! ## W-type recursion (catamorphism) -/

/-- Fold/catamorphism on W-trees. -/
def WTree.fold {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → X) → X) : WTree S ar → X
  | WTree.node s f => alg s (fun p => WTree.fold alg (f p))

/-- Computation rule path for fold. -/
def foldComputePath {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → X) → X) (s : S) (f : ar s → WTree S ar) :
    Path (WTree.fold alg (WTree.node s f))
         (alg s (fun p => WTree.fold alg (f p))) :=
  Path.refl _

theorem foldComputePath_toEq {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → X) → X) (s : S) (f : ar s → WTree S ar) :
    (foldComputePath alg s f).toEq = rfl := rfl

/-- The fold gives an algebra morphism from the initial algebra. -/
def foldAlgHom {S : Type u} {ar : S → Type u} (B : WAlgebra S ar) :
    WAlgHom S ar (WTree.initialAlg S ar) B where
  map := WTree.fold B.op
  commutes := fun _ _ => rfl

/-- Path witnessing fold is an algebra morphism. -/
def foldAlgHomPath {S : Type u} {ar : S → Type u} (B : WAlgebra S ar)
    (s : S) (f : ar s → WTree S ar) :
    Path ((foldAlgHom B).map (WTree.node s f))
         (B.op s (fun p => (foldAlgHom B).map (f p))) :=
  Path.refl _

/-! ## Identity and composition of algebra morphisms -/

/-- Identity algebra morphism. -/
def WAlgHom.idHom (S : Type u) (ar : S → Type u) (A : WAlgebra S ar) :
    WAlgHom S ar A A where
  map := id
  commutes := fun _ _ => rfl

/-- Composition of algebra morphisms. -/
def WAlgHom.comp {S : Type u} {ar : S → Type u} {A B C : WAlgebra S ar}
    (g : WAlgHom S ar B C) (f : WAlgHom S ar A B) :
    WAlgHom S ar A C where
  map := g.map ∘ f.map
  commutes := fun s k => by
    show g.map (f.map (A.op s k)) = C.op s (fun p => g.map (f.map (k p)))
    rw [f.commutes s k, g.commutes s (fun p => f.map (k p))]

/-- Identity morphism path. -/
def idHomPath {S : Type u} {ar : S → Type u} (A : WAlgebra S ar)
    (s : S) (f : ar s → A.Carrier) :
    Path ((WAlgHom.idHom S ar A).map (A.op s f)) (A.op s f) :=
  Path.refl _

/-- Composition morphism commutation path. -/
def compHomPath {S : Type u} {ar : S → Type u} {A B C : WAlgebra S ar}
    (g : WAlgHom S ar B C) (f : WAlgHom S ar A B)
    (s : S) (k : ar s → A.Carrier) :
    Path ((WAlgHom.comp g f).map (A.op s k))
         (C.op s (fun p => (WAlgHom.comp g f).map (k p))) :=
  Path.ofEq ((WAlgHom.comp g f).commutes s k)

/-! ## Dependent eliminator -/

/-- Dependent eliminator (induction principle) for W-trees. -/
def WTree.elim {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    (h : ∀ (s : S) (f : ar s → WTree S ar),
         (∀ p, P (f p)) → P (WTree.node s f)) :
    (w : WTree S ar) → P w
  | WTree.node s f => h s f (fun p => WTree.elim h (f p))

/-- Computation rule for the eliminator. -/
theorem elimCompute {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    (h : ∀ (s : S) (f : ar s → WTree S ar),
         (∀ p, P (f p)) → P (WTree.node s f))
    (s : S) (f : ar s → WTree S ar) :
    WTree.elim h (WTree.node s f) = h s f (fun p => WTree.elim h (f p)) := rfl

/-- Eliminator computation as a path. -/
def elimComputePath {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    (h : ∀ (s : S) (f : ar s → WTree S ar),
         (∀ p, P (f p)) → P (WTree.node s f))
    (s : S) (f : ar s → WTree S ar) :
    Path (WTree.elim h (WTree.node s f))
         (h s f (fun p => WTree.elim h (f p))) :=
  Path.refl _

/-! ## Transport on W-tree families -/

/-- Transport over W-tree families. -/
def wtreeTransport {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    {w₁ w₂ : WTree S ar} (p : Path w₁ w₂) (x : P w₁) : P w₂ :=
  Path.transport p x

theorem wtreeTransport_refl {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v} (w : WTree S ar) (x : P w) :
    wtreeTransport (Path.refl w) x = x := rfl

theorem wtreeTransport_trans {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    {w₁ w₂ w₃ : WTree S ar} (p : Path w₁ w₂) (q : Path w₂ w₃) (x : P w₁) :
    wtreeTransport (Path.trans p q) x = wtreeTransport q (wtreeTransport p x) := by
  cases p with | mk _ proof₁ => cases q with | mk _ proof₂ =>
    cases proof₁; cases proof₂; rfl

theorem wtreeTransport_symm {S : Type u} {ar : S → Type u}
    {P : WTree S ar → Type v}
    {w₁ w₂ : WTree S ar} (p : Path w₁ w₂) (x : P w₁) :
    wtreeTransport (Path.symm p) (wtreeTransport p x) = x := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Natural numbers as W-type -/

/-- Natural number shapes: zero or successor. -/
inductive NatShape where | zero | succ

/-- Arities: zero has no children, succ has one. -/
def natArity : NatShape → Type
  | NatShape.zero => Empty
  | NatShape.succ => Unit

/-- W-tree encoding of zero. -/
def wZero : WTree NatShape natArity :=
  WTree.node NatShape.zero Empty.elim

/-- W-tree encoding of successor. -/
def wSucc (n : WTree NatShape natArity) : WTree NatShape natArity :=
  WTree.node NatShape.succ (fun _ => n)

/-- Successor congruence path. -/
def wSuccCongrPath {m n : WTree NatShape natArity} (p : Path m n) :
    Path (wSucc m) (wSucc n) :=
  Path.congrArg wSucc p

theorem wSuccCongrPath_trans {a b c : WTree NatShape natArity}
    (p : Path a b) (q : Path b c) :
    wSuccCongrPath (Path.trans p q) =
    Path.trans (wSuccCongrPath p) (wSuccCongrPath q) := by
  simp [wSuccCongrPath]

theorem wSuccCongrPath_symm {a b : WTree NatShape natArity}
    (p : Path a b) :
    wSuccCongrPath (Path.symm p) = Path.symm (wSuccCongrPath p) := by
  simp [wSuccCongrPath]

theorem wSuccCongrPath_refl (n : WTree NatShape natArity) :
    (wSuccCongrPath (Path.refl n)).toEq = rfl := rfl

/-! ## Uniqueness of morphisms from initial algebra -/

/-- Any two maps agreeing with algebra structure are path-equal. -/
def fold_unique {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → X) → X)
    (h : WTree S ar → X)
    (hcomm : ∀ s f, h (WTree.node s f) = alg s (fun p => h (f p))) :
    (w : WTree S ar) → Path (h w) (WTree.fold alg w)
  | WTree.node s f =>
    Path.trans (Path.ofEq (hcomm s f))
      (Path.congrArg (alg s) (Path.ofEq (funext fun p => (fold_unique alg h hcomm (f p)).toEq)))

/-- Initiality: fold from two identical algebras gives the same result. -/
def fold_initiality {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → X) → X) (w : WTree S ar) :
    Path (WTree.fold alg w) (WTree.fold alg w) :=
  Path.refl _

/-! ## Paramorphism -/

/-- Paramorphism: recursion with access to sub-trees. -/
def WTree.para {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → WTree S ar) → (ar s → X) → X) :
    WTree S ar → X
  | WTree.node s f => alg s f (fun p => WTree.para alg (f p))

/-- Computation rule path for paramorphism. -/
def paraComputePath {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → WTree S ar) → (ar s → X) → X)
    (s : S) (f : ar s → WTree S ar) :
    Path (WTree.para alg (WTree.node s f))
         (alg s f (fun p => WTree.para alg (f p))) :=
  Path.refl _

theorem paraComputePath_toEq {S : Type u} {ar : S → Type u} {X : Type u}
    (alg : (s : S) → (ar s → WTree S ar) → (ar s → X) → X)
    (s : S) (f : ar s → WTree S ar) :
    (paraComputePath alg s f).toEq = rfl := rfl

/-! ## Congruence of fold under algebra change -/

/-- If two algebras agree pointwise, their folds produce path-equal results. -/
def fold_congrAlg {S : Type u} {ar : S → Type u} {X : Type u}
    (alg₁ alg₂ : (s : S) → (ar s → X) → X)
    (heq : ∀ s f, alg₁ s f = alg₂ s f) :
    (w : WTree S ar) → Path (WTree.fold alg₁ w) (WTree.fold alg₂ w)
  | WTree.node s f =>
    Path.trans
      (Path.congrArg (alg₁ s) (Path.ofEq (funext fun p => (fold_congrAlg alg₁ alg₂ heq (f p)).toEq)))
      (Path.ofEq (heq s _))

/-! ## Path algebra for WAlgHom -/

/-- Reflexivity for algebra morphism maps. -/
def walgHom_map_refl {S : Type u} {ar : S → Type u} {A B : WAlgebra S ar}
    (f : WAlgHom S ar A B) (x : A.Carrier) :
    Path (f.map x) (f.map x) := Path.refl _

/-- Congruence for algebra morphism application. -/
def walgHom_congrArg {S : Type u} {ar : S → Type u} {A B : WAlgebra S ar}
    (f : WAlgHom S ar A B) {x y : A.Carrier} (p : Path x y) :
    Path (f.map x) (f.map y) :=
  Path.congrArg f.map p

theorem walgHom_congrArg_trans {S : Type u} {ar : S → Type u} {A B : WAlgebra S ar}
    (f : WAlgHom S ar A B) {x y z : A.Carrier} (p : Path x y) (q : Path y z) :
    walgHom_congrArg f (Path.trans p q) =
    Path.trans (walgHom_congrArg f p) (walgHom_congrArg f q) := by
  simp [walgHom_congrArg]

theorem walgHom_congrArg_symm {S : Type u} {ar : S → Type u} {A B : WAlgebra S ar}
    (f : WAlgHom S ar A B) {x y : A.Carrier} (p : Path x y) :
    walgHom_congrArg f (Path.symm p) = Path.symm (walgHom_congrArg f p) := by
  simp [walgHom_congrArg]

end WTypePaths
end TypeTheory
end Path
end ComputationalPaths
