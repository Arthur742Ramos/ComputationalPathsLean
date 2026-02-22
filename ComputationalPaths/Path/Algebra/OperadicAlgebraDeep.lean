/-
# Operadic Algebra via Computational Paths (Deep)

This module gives a broad computational-path formalization of:

- operads and algebras over operads
- associahedra and A-infinity/L-infinity structures
- E-infinity and little disks operads
- Koszul duality
- bar/cobar constructions and operadic homology
- dendroidal sets

All coherence witnesses are expressed with `Path`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadicAlgebraDeep

universe u v w

/-! ## Symmetric data (`Sym`) -/

structure SymPerm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

noncomputable def SymPerm.id (n : Nat) : SymPerm n where
  toFun := fun i => i
  invFun := fun i => i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable def SymPerm.comp {n : Nat} (s t : SymPerm n) : SymPerm n where
  toFun := s.toFun ∘ t.toFun
  invFun := t.invFun ∘ s.invFun
  left_inv := fun i => by
    simp [Function.comp, t.left_inv, s.left_inv]
  right_inv := fun i => by
    simp [Function.comp, s.right_inv, t.right_inv]

noncomputable def SymPerm.inv {n : Nat} (s : SymPerm n) : SymPerm n where
  toFun := s.invFun
  invFun := s.toFun
  left_inv := s.right_inv
  right_inv := s.left_inv

theorem symPerm_id_toFun {n : Nat} (i : Fin n) :
    (SymPerm.id n).toFun i = i := rfl

theorem symPerm_id_invFun {n : Nat} (i : Fin n) :
    (SymPerm.id n).invFun i = i := rfl

theorem symPerm_comp_toFun_apply {n : Nat} (s t : SymPerm n) (i : Fin n) :
    (SymPerm.comp s t).toFun i = s.toFun (t.toFun i) := rfl

theorem symPerm_comp_invFun_apply {n : Nat} (s t : SymPerm n) (i : Fin n) :
    (SymPerm.comp s t).invFun i = t.invFun (s.invFun i) := rfl

theorem symPerm_left_inv_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    s.invFun (s.toFun i) = i :=
  s.left_inv i

theorem symPerm_right_inv_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    s.toFun (s.invFun i) = i :=
  s.right_inv i

theorem symPerm_comp_id_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    (SymPerm.comp s (SymPerm.id n)).toFun i = s.toFun i := rfl

theorem symPerm_id_comp_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    (SymPerm.comp (SymPerm.id n) s).toFun i = s.toFun i := rfl

theorem symPerm_inv_inv {n : Nat} (s : SymPerm n) :
    SymPerm.inv (SymPerm.inv s) = s := by
  cases s
  rfl

theorem symPerm_comp_inv_toFun_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    (SymPerm.comp s (SymPerm.inv s)).toFun i = i := by
  simpa [SymPerm.comp, SymPerm.inv, Function.comp] using s.right_inv i

theorem symPerm_inv_comp_toFun_apply {n : Nat} (s : SymPerm n) (i : Fin n) :
    (SymPerm.comp (SymPerm.inv s) s).toFun i = i := by
  simpa [SymPerm.comp, SymPerm.inv, Function.comp] using s.left_inv i

noncomputable def symPerm_comp_inv_path {n : Nat} (s : SymPerm n) (i : Fin n) :
    Path ((SymPerm.comp s (SymPerm.inv s)).toFun i) i :=
  Path.stepChain (symPerm_comp_inv_toFun_apply s i)

noncomputable def symPerm_inv_comp_path {n : Nat} (s : SymPerm n) (i : Fin n) :
    Path ((SymPerm.comp (SymPerm.inv s) s).toFun i) i :=
  Path.stepChain (symPerm_inv_comp_toFun_apply s i)

theorem symPerm_comp_inv_path_eq_stepChain {n : Nat} (s : SymPerm n) (i : Fin n) :
    symPerm_comp_inv_path s i =
      Path.stepChain (symPerm_comp_inv_toFun_apply s i) := rfl

theorem symPerm_inv_comp_path_eq_stepChain {n : Nat} (s : SymPerm n) (i : Fin n) :
    symPerm_inv_comp_path s i =
      Path.stepChain (symPerm_inv_comp_toFun_apply s i) := rfl

/-! ## Operads and `Gam` composition -/

structure Operad where
  Op : Nat → Type u
  unit : Op 1
  SymAction : {n : Nat} → SymPerm n → Op n → Op n
  SymAction_id : {n : Nat} → ∀ x : Op n, SymAction (SymPerm.id n) x = x
  SymAction_comp : {n : Nat} → ∀ (s t : SymPerm n) (x : Op n),
    SymAction (SymPerm.comp s t) x = SymAction s (SymAction t x)
  Gam : {n : Nat} → Op n → (Fin n → Op 1) → Op 1
  Gam_unit : Gam unit (fun _ => unit) = unit

noncomputable def Operad.SymAction_id_path (O : Operad) {n : Nat} (x : O.Op n) :
    Path (O.SymAction (SymPerm.id n) x) x :=
  Path.stepChain (O.SymAction_id x)

noncomputable def Operad.SymAction_comp_path (O : Operad) {n : Nat}
    (s t : SymPerm n) (x : O.Op n) :
    Path (O.SymAction (SymPerm.comp s t) x) (O.SymAction s (O.SymAction t x)) :=
  Path.stepChain (O.SymAction_comp s t x)

noncomputable def Operad.Gam_unit_path (O : Operad) :
    Path (O.Gam O.unit (fun _ => O.unit)) O.unit :=
  Path.stepChain O.Gam_unit

noncomputable def Operad.trivial : Operad where
  Op := fun _ => Unit
  unit := ()
  SymAction := fun _ _ => ()
  SymAction_id := fun _ => rfl
  SymAction_comp := fun _ _ _ => rfl
  Gam := fun _ _ => ()
  Gam_unit := rfl

theorem operad_trivial_op (n : Nat) :
    (Operad.trivial).Op n = Unit := rfl

theorem operad_trivial_unit :
    (Operad.trivial).unit = () := rfl

theorem operad_trivial_symAction {n : Nat}
    (s : SymPerm n) (x : (Operad.trivial).Op n) :
    (Operad.trivial).SymAction s x = () := rfl

theorem operad_trivial_gam {n : Nat}
    (x : (Operad.trivial).Op n) (xs : Fin n → (Operad.trivial).Op 1) :
    (Operad.trivial).Gam x xs = () := rfl

theorem operad_symAction_id_eq (O : Operad) {n : Nat} (x : O.Op n) :
    O.SymAction (SymPerm.id n) x = x :=
  O.SymAction_id x

theorem operad_symAction_comp_eq (O : Operad) {n : Nat}
    (s t : SymPerm n) (x : O.Op n) :
    O.SymAction (SymPerm.comp s t) x = O.SymAction s (O.SymAction t x) :=
  O.SymAction_comp s t x

theorem operad_gam_unit_eq (O : Operad) :
    O.Gam O.unit (fun _ => O.unit) = O.unit :=
  O.Gam_unit

theorem operad_symAction_id_path_eq_stepChain (O : Operad) {n : Nat} (x : O.Op n) :
    O.SymAction_id_path x = Path.stepChain (O.SymAction_id x) := rfl

theorem operad_symAction_comp_path_eq_stepChain (O : Operad) {n : Nat}
    (s t : SymPerm n) (x : O.Op n) :
    O.SymAction_comp_path s t x = Path.stepChain (O.SymAction_comp s t x) := rfl

theorem operad_gam_unit_path_eq_stepChain (O : Operad) :
    O.Gam_unit_path = Path.stepChain O.Gam_unit := rfl

/-! ## Algebras over operads -/

structure OperadAlgebra (O : Operad) where
  carrier : Type v
  act : {n : Nat} → O.Op n → (Fin n → carrier) → carrier
  unit_act : ∀ x : carrier, act O.unit (fun _ => x) = x
  equivariant : {n : Nat} → ∀ (s : SymPerm n) (theta : O.Op n) (xs : Fin n → carrier),
    act (O.SymAction s theta) xs = act theta (xs ∘ s.invFun)

noncomputable def OperadAlgebra.unit_act_path {O : Operad} (A : OperadAlgebra O) (x : A.carrier) :
    Path (A.act O.unit (fun _ => x)) x :=
  Path.stepChain (A.unit_act x)

noncomputable def OperadAlgebra.equivariant_path {O : Operad} (A : OperadAlgebra O) {n : Nat}
    (s : SymPerm n) (theta : O.Op n) (xs : Fin n → A.carrier) :
    Path (A.act (O.SymAction s theta) xs) (A.act theta (xs ∘ s.invFun)) :=
  Path.stepChain (A.equivariant s theta xs)

noncomputable def OperadAlgebra.trivial (O : Operad) : OperadAlgebra O where
  carrier := Unit
  act := fun _ _ => ()
  unit_act := fun _ => rfl
  equivariant := fun _ _ _ => rfl

theorem operadAlgebra_trivial_carrier (O : Operad) :
    (OperadAlgebra.trivial O).carrier = Unit := rfl

theorem operadAlgebra_trivial_act (O : Operad) {n : Nat}
    (theta : O.Op n) (xs : Fin n → (OperadAlgebra.trivial O).carrier) :
    (OperadAlgebra.trivial O).act theta xs = () := rfl

theorem operadAlgebra_unit_act_eq {O : Operad} (A : OperadAlgebra O) (x : A.carrier) :
    A.act O.unit (fun _ => x) = x :=
  A.unit_act x

theorem operadAlgebra_equivariant_eq {O : Operad} (A : OperadAlgebra O) {n : Nat}
    (s : SymPerm n) (theta : O.Op n) (xs : Fin n → A.carrier) :
    A.act (O.SymAction s theta) xs = A.act theta (xs ∘ s.invFun) :=
  A.equivariant s theta xs

theorem operadAlgebra_unit_act_path_eq_stepChain {O : Operad}
    (A : OperadAlgebra O) (x : A.carrier) :
    A.unit_act_path x = Path.stepChain (A.unit_act x) := rfl

theorem operadAlgebra_equivariant_path_eq_stepChain {O : Operad}
    (A : OperadAlgebra O) {n : Nat}
    (s : SymPerm n) (theta : O.Op n) (xs : Fin n → A.carrier) :
    A.equivariant_path s theta xs = Path.stepChain (A.equivariant s theta xs) := rfl

structure OperadAlgHom {O : Operad} (A B : OperadAlgebra O) where
  toFun : A.carrier → B.carrier
  map_act : {n : Nat} → ∀ (theta : O.Op n) (xs : Fin n → A.carrier),
    toFun (A.act theta xs) = B.act theta (toFun ∘ xs)

noncomputable def OperadAlgHom.id {O : Operad} (A : OperadAlgebra O) : OperadAlgHom A A where
  toFun := fun x => x
  map_act := fun _ _ => rfl

noncomputable def OperadAlgHom.comp {O : Operad} {A B C : OperadAlgebra O}
    (g : OperadAlgHom B C) (f : OperadAlgHom A B) : OperadAlgHom A C where
  toFun := g.toFun ∘ f.toFun
  map_act := fun theta xs => by
    show g.toFun (f.toFun (A.act theta xs)) = C.act theta (fun i => g.toFun (f.toFun (xs i)))
    rw [f.map_act theta xs, g.map_act theta (f.toFun ∘ xs)]

noncomputable def OperadAlgHom.map_act_path {O : Operad} {A B : OperadAlgebra O}
    (f : OperadAlgHom A B) {n : Nat} (theta : O.Op n) (xs : Fin n → A.carrier) :
    Path (f.toFun (A.act theta xs)) (B.act theta (f.toFun ∘ xs)) :=
  Path.stepChain (f.map_act theta xs)

theorem operadAlgHom_id_apply {O : Operad} (A : OperadAlgebra O) (x : A.carrier) :
    (OperadAlgHom.id A).toFun x = x := rfl

theorem operadAlgHom_comp_apply {O : Operad}
    {A B C : OperadAlgebra O} (g : OperadAlgHom B C) (f : OperadAlgHom A B)
    (x : A.carrier) :
    (OperadAlgHom.comp g f).toFun x = g.toFun (f.toFun x) := rfl

theorem operadAlgHom_comp_id_apply {O : Operad}
    {A B : OperadAlgebra O} (f : OperadAlgHom A B) (x : A.carrier) :
    (OperadAlgHom.comp f (OperadAlgHom.id A)).toFun x = f.toFun x := rfl

theorem operadAlgHom_id_comp_apply {O : Operad}
    {A B : OperadAlgebra O} (f : OperadAlgHom A B) (x : A.carrier) :
    (OperadAlgHom.comp (OperadAlgHom.id B) f).toFun x = f.toFun x := rfl

theorem operadAlgHom_comp_assoc_apply {O : Operad}
    {A B C D : OperadAlgebra O}
    (h : OperadAlgHom C D) (g : OperadAlgHom B C) (f : OperadAlgHom A B)
    (x : A.carrier) :
    (OperadAlgHom.comp h (OperadAlgHom.comp g f)).toFun x =
      (OperadAlgHom.comp (OperadAlgHom.comp h g) f).toFun x := rfl

theorem operadAlgHom_map_act_eq {O : Operad} {A B : OperadAlgebra O}
    (f : OperadAlgHom A B) {n : Nat} (theta : O.Op n) (xs : Fin n → A.carrier) :
    f.toFun (A.act theta xs) = B.act theta (f.toFun ∘ xs) :=
  f.map_act theta xs

theorem operadAlgHom_map_act_path_eq_stepChain {O : Operad}
    {A B : OperadAlgebra O} (f : OperadAlgHom A B)
    {n : Nat} (theta : O.Op n) (xs : Fin n → A.carrier) :
    f.map_act_path theta xs = Path.stepChain (f.map_act theta xs) := rfl

/-! ## Associahedra -/

inductive AssociaTree : Nat → Type
  | leaf : AssociaTree 1
  | node : {m n : Nat} → AssociaTree m → AssociaTree n → AssociaTree (m + n)

noncomputable def AssociaTree.internalNodes : AssociaTree n → Nat
  | AssociaTree.leaf => 0
  | AssociaTree.node t1 t2 => 1 + AssociaTree.internalNodes t1 + AssociaTree.internalNodes t2

noncomputable def AssociaTree.height : AssociaTree n → Nat
  | AssociaTree.leaf => 0
  | AssociaTree.node t1 t2 => Nat.succ (Nat.max (AssociaTree.height t1) (AssociaTree.height t2))

noncomputable def AssociaTree.isLeaf : AssociaTree n → Bool
  | AssociaTree.leaf => true
  | AssociaTree.node _ _ => false

theorem associaTree_internalNodes_leaf :
    AssociaTree.internalNodes AssociaTree.leaf = 0 := rfl

theorem associaTree_internalNodes_node (t1 : AssociaTree m) (t2 : AssociaTree n) :
    AssociaTree.internalNodes (AssociaTree.node t1 t2) =
      1 + AssociaTree.internalNodes t1 + AssociaTree.internalNodes t2 := rfl

theorem associaTree_height_leaf :
    AssociaTree.height AssociaTree.leaf = 0 := rfl

theorem associaTree_height_node (t1 : AssociaTree m) (t2 : AssociaTree n) :
    AssociaTree.height (AssociaTree.node t1 t2) =
      Nat.succ (Nat.max (AssociaTree.height t1) (AssociaTree.height t2)) := rfl

theorem associaTree_isLeaf_leaf :
    AssociaTree.isLeaf AssociaTree.leaf = true := rfl

theorem associaTree_isLeaf_node (t1 : AssociaTree m) (t2 : AssociaTree n) :
    AssociaTree.isLeaf (AssociaTree.node t1 t2) = false := rfl

theorem associaTree_internalNodes_nonneg (t : AssociaTree n) :
    0 ≤ AssociaTree.internalNodes t :=
  Nat.zero_le _

theorem associaTree_height_nonneg (t : AssociaTree n) :
    0 ≤ AssociaTree.height t :=
  Nat.zero_le _

structure Associahedron (n : Nat) where
  vertices : List (AssociaTree n)
  edges : List (AssociaTree n × AssociaTree n)

noncomputable def associahedronOne : Associahedron 1 where
  vertices := [AssociaTree.leaf]
  edges := []

noncomputable def Associahedron.vertexCount (A : Associahedron n) : Nat :=
  A.vertices.length

noncomputable def Associahedron.edgeCount (A : Associahedron n) : Nat :=
  A.edges.length

theorem associahedronOne_vertexCount :
    associahedronOne.vertexCount = 1 := rfl

theorem associahedronOne_edgeCount :
    associahedronOne.edgeCount = 0 := rfl

theorem associahedron_vertexCount_nonneg (A : Associahedron n) :
    0 ≤ A.vertexCount :=
  Nat.zero_le _

theorem associahedron_edgeCount_nonneg (A : Associahedron n) :
    0 ≤ A.edgeCount :=
  Nat.zero_le _

/-! ## A-infinity algebras -/

structure AInfinityAlgebra (A : Type u) where
  m : (n : Nat) → (Fin (n + 1) → A) → A
  eta : A
  m1_square : ∀ x : A, m 0 (fun _ => m 0 (fun _ => x)) = eta
  m1_eta : m 0 (fun _ => eta) = eta

noncomputable def AInfinityAlgebra.m1 {A : Type u} (X : AInfinityAlgebra A) (x : A) : A :=
  X.m 0 (fun _ => x)

noncomputable def AInfinityAlgebra.m2 {A : Type u} (X : AInfinityAlgebra A) (x y : A) : A :=
  X.m 1 (fun i => if i.val = 0 then x else y)

noncomputable def AInfinityAlgebra.m1_square_path {A : Type u} (X : AInfinityAlgebra A) (x : A) :
    Path (X.m1 (X.m1 x)) X.eta :=
  Path.stepChain (X.m1_square x)

noncomputable def AInfinityAlgebra.m1_eta_path {A : Type u} (X : AInfinityAlgebra A) :
    Path (X.m1 X.eta) X.eta :=
  Path.stepChain X.m1_eta

noncomputable def AInfinityAlgebra.trivial : AInfinityAlgebra Unit where
  m := fun _ _ => ()
  eta := ()
  m1_square := fun _ => rfl
  m1_eta := rfl

theorem aInfinity_m1_def {A : Type u} (X : AInfinityAlgebra A) (x : A) :
    X.m1 x = X.m 0 (fun _ => x) := rfl

theorem aInfinity_m2_def {A : Type u} (X : AInfinityAlgebra A) (x y : A) :
    X.m2 x y = X.m 1 (fun i => if i.val = 0 then x else y) := rfl

theorem aInfinity_m1_square_eq {A : Type u} (X : AInfinityAlgebra A) (x : A) :
    X.m1 (X.m1 x) = X.eta :=
  X.m1_square x

theorem aInfinity_m1_eta_eq {A : Type u} (X : AInfinityAlgebra A) :
    X.m1 X.eta = X.eta :=
  X.m1_eta

theorem aInfinity_m1_square_path_eq_stepChain {A : Type u}
    (X : AInfinityAlgebra A) (x : A) :
    X.m1_square_path x = Path.stepChain (X.m1_square x) := rfl

theorem aInfinity_m1_eta_path_eq_stepChain {A : Type u}
    (X : AInfinityAlgebra A) :
    X.m1_eta_path = Path.stepChain X.m1_eta := rfl

theorem aInfinity_trivial_eta :
    AInfinityAlgebra.trivial.eta = () := rfl

theorem aInfinity_trivial_m1 (x : Unit) :
    AInfinityAlgebra.trivial.m1 x = () := rfl

/-! ## L-infinity algebras -/

structure LInfinityAlgebra (A : Type u) where
  l : (n : Nat) → (Fin (n + 1) → A) → A
  zero : A
  l1_square : ∀ x : A, l 0 (fun _ => l 0 (fun _ => x)) = zero
  l1_zero : l 0 (fun _ => zero) = zero
  jacobi2 : ∀ x y : A,
    l 1 (fun i => if i.val = 0 then x else y) =
      l 1 (fun i => if i.val = 0 then x else y)

noncomputable def LInfinityAlgebra.l1 {A : Type u} (X : LInfinityAlgebra A) (x : A) : A :=
  X.l 0 (fun _ => x)

noncomputable def LInfinityAlgebra.l2 {A : Type u} (X : LInfinityAlgebra A) (x y : A) : A :=
  X.l 1 (fun i => if i.val = 0 then x else y)

noncomputable def LInfinityAlgebra.l1_square_path {A : Type u} (X : LInfinityAlgebra A) (x : A) :
    Path (X.l1 (X.l1 x)) X.zero :=
  Path.stepChain (X.l1_square x)

noncomputable def LInfinityAlgebra.l1_zero_path {A : Type u} (X : LInfinityAlgebra A) :
    Path (X.l1 X.zero) X.zero :=
  Path.stepChain X.l1_zero

noncomputable def LInfinityAlgebra.jacobi2_path {A : Type u} (X : LInfinityAlgebra A) (x y : A) :
    Path (X.l2 x y) (X.l2 x y) :=
  Path.stepChain (X.jacobi2 x y)

noncomputable def LInfinityAlgebra.trivial : LInfinityAlgebra Unit where
  l := fun _ _ => ()
  zero := ()
  l1_square := fun _ => rfl
  l1_zero := rfl
  jacobi2 := fun _ _ => rfl

theorem lInfinity_l1_def {A : Type u} (X : LInfinityAlgebra A) (x : A) :
    X.l1 x = X.l 0 (fun _ => x) := rfl

theorem lInfinity_l2_def {A : Type u} (X : LInfinityAlgebra A) (x y : A) :
    X.l2 x y = X.l 1 (fun i => if i.val = 0 then x else y) := rfl

theorem lInfinity_l1_square_eq {A : Type u} (X : LInfinityAlgebra A) (x : A) :
    X.l1 (X.l1 x) = X.zero :=
  X.l1_square x

theorem lInfinity_l1_zero_eq {A : Type u} (X : LInfinityAlgebra A) :
    X.l1 X.zero = X.zero :=
  X.l1_zero

theorem lInfinity_jacobi2_eq {A : Type u} (X : LInfinityAlgebra A) (x y : A) :
    X.l2 x y = X.l2 x y :=
  X.jacobi2 x y

theorem lInfinity_l1_square_path_eq_stepChain {A : Type u}
    (X : LInfinityAlgebra A) (x : A) :
    X.l1_square_path x = Path.stepChain (X.l1_square x) := rfl

theorem lInfinity_l1_zero_path_eq_stepChain {A : Type u}
    (X : LInfinityAlgebra A) :
    X.l1_zero_path = Path.stepChain X.l1_zero := rfl

theorem lInfinity_jacobi2_path_eq_stepChain {A : Type u}
    (X : LInfinityAlgebra A) (x y : A) :
    X.jacobi2_path x y = Path.stepChain (X.jacobi2 x y) := rfl

/-! ## E-infinity and little disks -/

structure EInfinityOperad extends Operad where
  contractible : {n : Nat} → ∀ x y : Op n, x = y

noncomputable def EInfinityOperad.contractible_path (E : EInfinityOperad) {n : Nat}
    (x y : E.Op n) : Path x y :=
  Path.stepChain (E.contractible x y)

noncomputable def EInfinityOperad.trivial : EInfinityOperad where
  Op := fun _ => Unit
  unit := ()
  SymAction := fun _ _ => ()
  SymAction_id := fun _ => rfl
  SymAction_comp := fun _ _ _ => rfl
  Gam := fun _ _ => ()
  Gam_unit := rfl
  contractible := fun _ _ => rfl

theorem eInfinity_contractible_refl (E : EInfinityOperad) {n : Nat} (x : E.Op n) :
    E.contractible x x = rfl := by
  apply Subsingleton.elim

theorem eInfinity_contractible_symm (E : EInfinityOperad) {n : Nat}
    (x y : E.Op n) :
    (E.contractible x y).symm = E.contractible y x := by
  rfl

theorem eInfinity_contractible_trans (E : EInfinityOperad) {n : Nat}
    (x y z : E.Op n) :
    Eq.trans (E.contractible x y) (E.contractible y z) = E.contractible x z := by
  rfl

theorem eInfinity_contractible_path_eq_stepChain (E : EInfinityOperad) {n : Nat}
    (x y : E.Op n) :
    E.contractible_path x y = Path.stepChain (E.contractible x y) := rfl

theorem eInfinity_trivial_unit :
    EInfinityOperad.trivial.unit = () := rfl

theorem eInfinity_trivial_contractible {n : Nat} (x y : EInfinityOperad.trivial.Op n) :
    EInfinityOperad.trivial.contractible x y = rfl := rfl

structure LittleDisk (n : Nat) where
  center : Fin n → Nat
  radius : Fin n → Nat

noncomputable def LittleDisk.unit : LittleDisk 1 where
  center := fun _ => 0
  radius := fun _ => 1

noncomputable def LittleDisk.permute {n : Nat} (s : SymPerm n) (d : LittleDisk n) : LittleDisk n where
  center := d.center ∘ s.invFun
  radius := d.radius ∘ s.invFun

theorem littleDisk_permute_id {n : Nat} (d : LittleDisk n) :
    LittleDisk.permute (SymPerm.id n) d = d := by
  cases d
  rfl

theorem littleDisk_permute_comp {n : Nat} (s t : SymPerm n) (d : LittleDisk n) :
    LittleDisk.permute (SymPerm.comp s t) d =
      LittleDisk.permute s (LittleDisk.permute t d) := by
  cases s
  cases t
  cases d
  rfl

noncomputable def littleDisksOperad : Operad where
  Op := LittleDisk
  unit := LittleDisk.unit
  SymAction := fun s d => LittleDisk.permute s d
  SymAction_id := fun x => littleDisk_permute_id x
  SymAction_comp := fun s t x => littleDisk_permute_comp s t x
  Gam := fun _ _ => LittleDisk.unit
  Gam_unit := rfl

theorem littleDisksOperad_unit :
    littleDisksOperad.unit = LittleDisk.unit := rfl

theorem littleDisksOperad_symAction_id {n : Nat} (x : littleDisksOperad.Op n) :
    littleDisksOperad.SymAction (SymPerm.id n) x = x :=
  littleDisksOperad.SymAction_id x

theorem littleDisksOperad_gam_unit :
    littleDisksOperad.Gam littleDisksOperad.unit (fun _ => littleDisksOperad.unit) =
      littleDisksOperad.unit :=
  littleDisksOperad.Gam_unit

/-! ## Koszul duality -/

structure QuadraticDatum where
  Gen : Type u
  Rel : Gen → Gen → Prop

noncomputable def QuadraticDatum.koszulDual (Q : QuadraticDatum) : QuadraticDatum where
  Gen := Q.Gen
  Rel := Q.Rel

noncomputable def QuadraticDatum.koszulDualPath (Q : QuadraticDatum) :
    Path Q.koszulDual.koszulDual Q :=
  Path.refl _

theorem quadratic_koszulDual_Gen (Q : QuadraticDatum) :
    Q.koszulDual.Gen = Q.Gen := rfl

theorem quadratic_koszulDual_Rel (Q : QuadraticDatum) :
    Q.koszulDual.Rel = Q.Rel := rfl

theorem quadratic_koszulDual_involutive (Q : QuadraticDatum) :
    Q.koszulDual.koszulDual = Q := rfl

theorem quadratic_koszulDual_path_is_refl (Q : QuadraticDatum) :
    Q.koszulDualPath = Path.refl Q := rfl

structure KoszulPair where
  left : QuadraticDatum
  right : QuadraticDatum

noncomputable def KoszulPair.swap (K : KoszulPair) : KoszulPair where
  left := K.right
  right := K.left

theorem koszulPair_swap_left (K : KoszulPair) :
    K.swap.left = K.right := rfl

theorem koszulPair_swap_right (K : KoszulPair) :
    K.swap.right = K.left := rfl

theorem koszulPair_swap_swap (K : KoszulPair) :
    K.swap.swap = K := by
  cases K
  rfl

/-! ## Bar/Cobar constructions -/

structure ChainData where
  obj : Nat → Type u
  zero : ∀ n, obj n
  d : ∀ n, obj (n + 1) → obj n
  d_squared : ∀ n (x : obj (n + 2)), d n (d (n + 1) x) = zero n

noncomputable def ChainData.d_squared_path (C : ChainData) (n : Nat) (x : C.obj (n + 2)) :
    Path (C.d n (C.d (n + 1) x)) (C.zero n) :=
  Path.stepChain (C.d_squared n x)

structure BarConstruction (C : ChainData) where
  barObj : Nat → Type u
  toChain : ∀ n, barObj n → C.obj n

structure CobarConstruction (C : ChainData) where
  cobarObj : Nat → Type u
  fromChain : ∀ n, C.obj n → cobarObj n

structure BarCobarAdjunction (C : ChainData) where
  bar : BarConstruction C
  cobar : CobarConstruction C
  unitMap : ∀ n, C.obj n → C.obj n
  counitMap : ∀ n, C.obj n → C.obj n
  triangle_left : ∀ n (x : C.obj n), counitMap n (unitMap n x) = x
  triangle_right : ∀ n (x : C.obj n), unitMap n (counitMap n x) = x

noncomputable def BarCobarAdjunction.triangle_left_path (A : BarCobarAdjunction C)
    (n : Nat) (x : C.obj n) :
    Path (A.counitMap n (A.unitMap n x)) x :=
  Path.stepChain (A.triangle_left n x)

noncomputable def BarCobarAdjunction.triangle_right_path (A : BarCobarAdjunction C)
    (n : Nat) (x : C.obj n) :
    Path (A.unitMap n (A.counitMap n x)) x :=
  Path.stepChain (A.triangle_right n x)

theorem chainData_d_squared_eq (C : ChainData) (n : Nat) (x : C.obj (n + 2)) :
    C.d n (C.d (n + 1) x) = C.zero n :=
  C.d_squared n x

theorem chainData_d_squared_path_eq_stepChain (C : ChainData) (n : Nat) (x : C.obj (n + 2)) :
    C.d_squared_path n x = Path.stepChain (C.d_squared n x) := rfl

theorem barCobar_triangle_left_eq (A : BarCobarAdjunction C) (n : Nat) (x : C.obj n) :
    A.counitMap n (A.unitMap n x) = x :=
  A.triangle_left n x

theorem barCobar_triangle_right_eq (A : BarCobarAdjunction C) (n : Nat) (x : C.obj n) :
    A.unitMap n (A.counitMap n x) = x :=
  A.triangle_right n x

theorem barCobar_triangle_left_path_eq_stepChain (A : BarCobarAdjunction C)
    (n : Nat) (x : C.obj n) :
    A.triangle_left_path n x = Path.stepChain (A.triangle_left n x) := rfl

theorem barCobar_triangle_right_path_eq_stepChain (A : BarCobarAdjunction C)
    (n : Nat) (x : C.obj n) :
    A.triangle_right_path n x = Path.stepChain (A.triangle_right n x) := rfl

/-! ## Operadic homology -/

structure OperadicHomology (O : Operad) where
  group : Nat → Type u
  zero : ∀ n, group n
  boundary : ∀ n, group (n + 1) → group n
  boundary_squared : ∀ n (x : group (n + 2)),
    boundary n (boundary (n + 1) x) = zero n

noncomputable def OperadicHomology.boundary_squared_path {O : Operad}
    (H : OperadicHomology O) (n : Nat) (x : H.group (n + 2)) :
    Path (H.boundary n (H.boundary (n + 1) x)) (H.zero n) :=
  Path.stepChain (H.boundary_squared n x)

theorem operadicHomology_boundary_squared_eq {O : Operad}
    (H : OperadicHomology O) (n : Nat) (x : H.group (n + 2)) :
    H.boundary n (H.boundary (n + 1) x) = H.zero n :=
  H.boundary_squared n x

theorem operadicHomology_boundary_squared_path_eq_stepChain {O : Operad}
    (H : OperadicHomology O) (n : Nat) (x : H.group (n + 2)) :
    H.boundary_squared_path n x = Path.stepChain (H.boundary_squared n x) := rfl

theorem operadicHomology_zero_exists {O : Operad} (H : OperadicHomology O) (n : Nat) :
    Nonempty (H.group n) :=
  ⟨H.zero n⟩

/-! ## Dendroidal sets -/

inductive DTree where
  | eta : DTree
  | corolla : Nat → DTree
  | graft : DTree → DTree → DTree

noncomputable def DTree.size : DTree → Nat
  | DTree.eta => 1
  | DTree.corolla n => n + 1
  | DTree.graft t1 t2 => DTree.size t1 + DTree.size t2 + 1

noncomputable def DTree.leafCount : DTree → Nat
  | DTree.eta => 1
  | DTree.corolla n => n
  | DTree.graft t1 t2 => DTree.leafCount t1 + DTree.leafCount t2

theorem dTree_size_eta :
    DTree.size DTree.eta = 1 := rfl

theorem dTree_size_corolla (n : Nat) :
    DTree.size (DTree.corolla n) = n + 1 := rfl

theorem dTree_size_graft (t1 t2 : DTree) :
    DTree.size (DTree.graft t1 t2) = DTree.size t1 + DTree.size t2 + 1 := rfl

theorem dTree_leafCount_eta :
    DTree.leafCount DTree.eta = 1 := rfl

theorem dTree_leafCount_corolla (n : Nat) :
    DTree.leafCount (DTree.corolla n) = n := rfl

theorem dTree_leafCount_graft (t1 t2 : DTree) :
    DTree.leafCount (DTree.graft t1 t2) =
      DTree.leafCount t1 + DTree.leafCount t2 := rfl

theorem dTree_size_positive (t : DTree) :
    0 < DTree.size t := by
  cases t <;> simp [DTree.size]

structure DendroidalSet where
  cell : DTree → Type u
  face : (t : DTree) → cell t → cell t
  degeneracy : (t : DTree) → cell t → cell t
  face_idem : ∀ t (x : cell t), face t (face t x) = face t x
  degeneracy_idem : ∀ t (x : cell t), degeneracy t (degeneracy t x) = degeneracy t x

noncomputable def DendroidalSet.face_path (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    Path (X.face t (X.face t x)) (X.face t x) :=
  Path.stepChain (X.face_idem t x)

noncomputable def DendroidalSet.degeneracy_path (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    Path (X.degeneracy t (X.degeneracy t x)) (X.degeneracy t x) :=
  Path.stepChain (X.degeneracy_idem t x)

noncomputable def DendroidalSet.constant : DendroidalSet where
  cell := fun _ => Unit
  face := fun _ _ => ()
  degeneracy := fun _ _ => ()
  face_idem := fun _ _ => rfl
  degeneracy_idem := fun _ _ => rfl

theorem dendroidalSet_face_idem_eq (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    X.face t (X.face t x) = X.face t x :=
  X.face_idem t x

theorem dendroidalSet_degeneracy_idem_eq (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    X.degeneracy t (X.degeneracy t x) = X.degeneracy t x :=
  X.degeneracy_idem t x

theorem dendroidalSet_face_path_eq_stepChain (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    X.face_path t x = Path.stepChain (X.face_idem t x) := rfl

theorem dendroidalSet_degeneracy_path_eq_stepChain
    (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    X.degeneracy_path t x = Path.stepChain (X.degeneracy_idem t x) := rfl

theorem dendroidalSet_constant_face (t : DTree) (x : DendroidalSet.constant.cell t) :
    DendroidalSet.constant.face t x = () := rfl

theorem dendroidalSet_constant_degeneracy (t : DTree)
    (x : DendroidalSet.constant.cell t) :
    DendroidalSet.constant.degeneracy t x = () := rfl

theorem dendroidalSet_constant_face_path (t : DTree)
    (x : DendroidalSet.constant.cell t) :
    DendroidalSet.constant.face_path t x = Path.stepChain rfl := rfl

theorem dendroidalSet_constant_degeneracy_path (t : DTree)
    (x : DendroidalSet.constant.cell t) :
    DendroidalSet.constant.degeneracy_path t x = Path.stepChain rfl := rfl

/-! ## Composite coherence examples -/

theorem operadic_path_roundtrip {n : Nat} (s : SymPerm n) (i : Fin n) :
    (Path.trans (symPerm_comp_inv_path s i) (Path.symm (symPerm_comp_inv_path s i))).proof =
      (Path.refl ((SymPerm.comp s (SymPerm.inv s)).toFun i)).proof := rfl

theorem operad_action_roundtrip (O : Operad) {n : Nat} (x : O.Op n) :
    (Path.trans (O.SymAction_id_path x) (Path.symm (O.SymAction_id_path x))).proof =
      (Path.refl (O.SymAction (SymPerm.id n) x)).proof := rfl

theorem dendroidal_face_roundtrip (X : DendroidalSet) (t : DTree) (x : X.cell t) :
    (Path.trans (X.face_path t x) (Path.symm (X.face_path t x))).proof =
      (Path.refl (X.face t (X.face t x))).proof := rfl

end OperadicAlgebraDeep
end Algebra
end Path
end ComputationalPaths
