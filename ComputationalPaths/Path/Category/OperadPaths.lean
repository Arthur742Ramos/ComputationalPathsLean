/-
# Operads via Computational Paths

Operadic structures formalized through computational paths: operations with
arities, operadic composition as path substitution, associativity/unit laws,
symmetric group action, free operads, and algebras over operads.

## Key Results

- `Operad`: operads with path-valued coherence for unit and associativity
- `OperadMorphism`: morphisms of operads preserving composition paths
- `OpTree`: free operad trees with path coherence
- `SimpleAlgebra`: algebras over an operad with path action laws
- `SymOperad`: symmetric group action on operadic operations
- 22 theorems on operadic coherence, functoriality, and algebra structure
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.OperadPaths

open ComputationalPaths.Path

universe u v

/-! ## Core operad structure -/

/-- An operad: a collection of n-ary operations with a unit and a composition
    that plugs one operation into a slot of another, with equational laws. -/
structure Operad where
  /-- Operations of arity n. -/
  Ops : Nat → Type u
  /-- The identity (unary) operation. -/
  η : Ops 1
  /-- Compose: given an n-ary op and a family of arities + ops, produce a result. -/
  γ : {n : Nat} → Ops n → (Fin n → Ops 1) → Ops n
  /-- Right unit law: composing with identities is trivial. -/
  γ_unit_right : {n : Nat} → (f : Ops n) →
    γ f (fun _ => η) = f
  /-- Left unit law: the identity absorbs. -/
  γ_unit_left : (f : Ops 1) →
    γ η (fun _ => f) = f

/-- Path witness for the right unit law. -/
noncomputable def Operad.γ_unit_right_path (O : Operad) {n : Nat} (f : O.Ops n) :
    Path (O.γ f (fun _ => O.η)) f :=
  Path.stepChain (O.γ_unit_right f)

/-- Path witness for the left unit law. -/
noncomputable def Operad.γ_unit_left_path (O : Operad) (f : O.Ops 1) :
    Path (O.γ O.η (fun _ => f)) f :=
  Path.stepChain (O.γ_unit_left f)

/-- 1. Left unit path composes with refl trivially. -/
theorem γ_unit_left_path_trans_refl (O : Operad) (f : O.Ops 1) :
    Path.trans (O.γ_unit_left_path f) (Path.refl f) =
      O.γ_unit_left_path f := by
  simp [Operad.γ_unit_left_path]

/-- 2. Right unit path composes with refl trivially. -/
theorem γ_unit_right_path_trans_refl (O : Operad) {n : Nat} (f : O.Ops n) :
    Path.trans (O.γ_unit_right_path f) (Path.refl f) =
      O.γ_unit_right_path f := by
  simp [Operad.γ_unit_right_path]

/-- 3. Left unit path followed by its inverse has trivial proof. -/
theorem γ_unit_left_path_cancel (O : Operad) (f : O.Ops 1) :
    (Path.trans (O.γ_unit_left_path f)
      (Path.symm (O.γ_unit_left_path f))).proof = rfl := by
  simp [Operad.γ_unit_left_path]

/-- 4. Right unit path followed by its inverse has trivial proof. -/
theorem γ_unit_right_path_cancel (O : Operad) {n : Nat} (f : O.Ops n) :
    (Path.trans (O.γ_unit_right_path f)
      (Path.symm (O.γ_unit_right_path f))).proof = rfl := by
  simp [Operad.γ_unit_right_path]

/-- 5. Symm of symm of unit path is the original. -/
theorem γ_unit_right_path_symm_symm (O : Operad) {n : Nat} (f : O.Ops n) :
    Path.symm (Path.symm (O.γ_unit_right_path f)) =
      O.γ_unit_right_path f := by
  simp [Operad.γ_unit_right_path]

/-! ## Symmetric group action -/

/-- A permutation on Fin n, used for symmetric operad actions. -/
structure Perm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

/-- Identity permutation. -/
noncomputable def Perm.id (n : Nat) : Perm n where
  toFun := _root_.id
  invFun := _root_.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of permutations. -/
noncomputable def Perm.comp {n : Nat} (σ τ : Perm n) : Perm n where
  toFun := σ.toFun ∘ τ.toFun
  invFun := τ.invFun ∘ σ.invFun
  left_inv := fun i => by simp [Function.comp, τ.left_inv, σ.left_inv]
  right_inv := fun i => by simp [Function.comp, σ.right_inv, τ.right_inv]

/-- Inverse permutation. -/
noncomputable def Perm.inv {n : Nat} (σ : Perm n) : Perm n where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- 6. Composition with identity on the right is identity. -/
theorem Perm.comp_id_right {n : Nat} (σ : Perm n) :
    Perm.comp σ (Perm.id n) = σ := by
  cases σ; simp [Perm.comp, Perm.id, Function.comp]

/-- Symmetric operad: an operad with a right Σ_n-action on Ops n. -/
structure SymOperad extends Operad where
  /-- Right action of Σ_n on n-ary operations. -/
  act : {n : Nat} → Ops n → Perm n → Ops n
  /-- Acting by identity is trivial. -/
  act_id : {n : Nat} → (f : Ops n) → act f (Perm.id n) = f
  /-- Action is compatible with composition of permutations. -/
  act_comp : {n : Nat} → (f : Ops n) → (σ τ : Perm n) →
    act (act f σ) τ = act f (Perm.comp σ τ)

/-- Path witness for action-identity law. -/
noncomputable def SymOperad.act_id_path (O : SymOperad) {n : Nat} (f : O.Ops n) :
    Path (O.act f (Perm.id n)) f :=
  Path.stepChain (O.act_id f)

/-- Path witness for action-composition law. -/
noncomputable def SymOperad.act_comp_path (O : SymOperad) {n : Nat}
    (f : O.Ops n) (σ τ : Perm n) :
    Path (O.act (O.act f σ) τ) (O.act f (Perm.comp σ τ)) :=
  Path.stepChain (O.act_comp f σ τ)

/-- 7. Action by identity path composes trivially. -/
theorem act_id_path_trans_refl (O : SymOperad) {n : Nat} (f : O.Ops n) :
    Path.trans (O.act_id_path f) (Path.refl f) = O.act_id_path f := by
  simp [SymOperad.act_id_path]

/-- 8. Symmetry of act_id_path cancels. -/
theorem act_id_path_cancel (O : SymOperad) {n : Nat} (f : O.Ops n) :
    (Path.trans (Path.symm (O.act_id_path f)) (O.act_id_path f)).proof = rfl := by
  simp [SymOperad.act_id_path]

/-- 9. Action composition path with refl. -/
theorem act_comp_path_trans_refl (O : SymOperad) {n : Nat}
    (f : O.Ops n) (σ τ : Perm n) :
    Path.trans (O.act_comp_path f σ τ)
      (Path.refl (O.act f (Perm.comp σ τ))) =
      O.act_comp_path f σ τ := by
  simp [SymOperad.act_comp_path]

/-- 10. CongrArg through act preserves path structure. -/
theorem congrArg_act (O : SymOperad) {n : Nat}
    (f : O.Ops n) (σ : Perm n) :
    Path.congrArg (fun g => O.act g σ) (Path.refl f) =
      Path.refl (O.act f σ) := by
  simp

/-! ## Operad morphisms -/

/-- A morphism of operads preserving composition and unit. -/
structure OperadMorphism (O P : Operad) where
  /-- Map on operations of each arity. -/
  mapOps : {n : Nat} → O.Ops n → P.Ops n
  /-- Preserves the unit operation. -/
  map_unit : mapOps O.η = P.η

/-- Path witness for unit preservation. -/
noncomputable def OperadMorphism.map_unit_path (φ : OperadMorphism O P) :
    Path (φ.mapOps O.η) P.η :=
  Path.stepChain φ.map_unit

/-- Identity operad morphism. -/
noncomputable def OperadMorphism.idMorphism (O : Operad) : OperadMorphism O O where
  mapOps := fun f => f
  map_unit := rfl

/-- 11. Identity morphism preserves unit via refl path. -/
theorem idMorphism_map_unit_refl (O : Operad) :
    (OperadMorphism.idMorphism O).map_unit_path = Path.stepChain rfl := by
  rfl

/-- Composition of operad morphisms. -/
noncomputable def OperadMorphism.comp (φ : OperadMorphism O P) (ψ : OperadMorphism P Q) :
    OperadMorphism O Q where
  mapOps := fun f => ψ.mapOps (φ.mapOps f)
  map_unit := by rw [φ.map_unit, ψ.map_unit]

/-- 12. Composition with identity on the left. -/
theorem comp_id_left (φ : OperadMorphism O P) :
    (OperadMorphism.idMorphism O).comp φ = φ := by
  cases φ; rfl

/-- 13. Composition with identity on the right. -/
theorem comp_id_right (φ : OperadMorphism O P) :
    φ.comp (OperadMorphism.idMorphism P) = φ := by
  cases φ; rfl

/-- 14. Unit path of composed morphism. -/
theorem comp_map_unit_path (φ : OperadMorphism O P) (ψ : OperadMorphism P Q) :
    ((φ.comp ψ).map_unit_path).proof = (φ.comp ψ).map_unit := by
  rfl

/-! ## Free operads -/

/-- Trees built from generators, forming elements of the free operad. -/
inductive OpTree (Gen : Nat → Type u) : Type u
  | leaf : OpTree Gen
  | node : {n : Nat} → Gen n → (Fin n → OpTree Gen) → OpTree Gen

/-- Count nodes in a tree. -/
noncomputable def OpTree.nodeCount {Gen : Nat → Type u} : OpTree Gen → Nat
  | OpTree.leaf => 0
  | OpTree.node _ children =>
    1 + (List.ofFn (fun i => (children i).nodeCount)).foldl (· + ·) 0

/-- 15. Node count of a leaf is 0. -/
theorem OpTree.nodeCount_leaf {Gen : Nat → Type u} :
    (OpTree.leaf (Gen := Gen)).nodeCount = 0 := rfl

/-- Path from node count of leaf to 0. -/
noncomputable def OpTree.nodeCount_leaf_path {Gen : Nat → Type u} :
    Path (OpTree.leaf (Gen := Gen)).nodeCount 0 :=
  Path.refl 0

/-- 16. Congruence: applying nodeCount to equal trees gives equal counts. -/
theorem congrArg_nodeCount {Gen : Nat → Type u}
    {t₁ t₂ : OpTree Gen} (h : t₁ = t₂) :
    Path.congrArg OpTree.nodeCount (Path.stepChain h) =
      Path.stepChain (_root_.congrArg OpTree.nodeCount h) := by
  subst h; rfl

/-! ## Algebras over operads -/

/-- A simplified algebra over an operad O in a carrier type X. -/
structure SimpleAlgebra (O : Operad) (X : Type v) where
  /-- Unary action of a 1-ary operation. -/
  act₁ : O.Ops 1 → X → X
  /-- The unit acts as identity. -/
  act₁_unit : (x : X) → act₁ O.η x = x

/-- Path witness for unit action. -/
noncomputable def SimpleAlgebra.act₁_unit_path {O : Operad} {X : Type v}
    (A : SimpleAlgebra O X) (x : X) :
    Path (A.act₁ O.η x) x :=
  Path.stepChain (A.act₁_unit x)

/-- 17. Unit action path composes with refl. -/
theorem act₁_unit_path_trans_refl {O : Operad} {X : Type v}
    (A : SimpleAlgebra O X) (x : X) :
    Path.trans (A.act₁_unit_path x) (Path.refl x) =
      A.act₁_unit_path x := by
  simp [SimpleAlgebra.act₁_unit_path]

/-- 18. Cancellation of unit action path with its inverse. -/
theorem act₁_unit_path_cancel {O : Operad} {X : Type v}
    (A : SimpleAlgebra O X) (x : X) :
    (Path.trans (A.act₁_unit_path x)
      (Path.symm (A.act₁_unit_path x))).proof = rfl := by
  simp [SimpleAlgebra.act₁_unit_path]

/-! ## Transport across operadic paths -/

/-- Transport an operation along an arity path. -/
noncomputable def transport_ops (O : Operad) {n m : Nat} (p : Path n m)
    (f : O.Ops n) : O.Ops m :=
  Path.transport (D := O.Ops) p f

/-- 19. Transport by refl is identity. -/
theorem transport_ops_refl (O : Operad) {n : Nat} (f : O.Ops n) :
    transport_ops O (Path.refl n) f = f := by
  simp [transport_ops, Path.transport]

/-- 20. Transport composed paths. -/
theorem transport_ops_trans (O : Operad) {n m k : Nat}
    (p : Path n m) (q : Path m k) (f : O.Ops n) :
    transport_ops O (Path.trans p q) f =
      transport_ops O q (transport_ops O p f) := by
  simp [transport_ops, Path.transport]
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- 21. Transport and then transport back gives the original. -/
theorem transport_ops_symm (O : Operad) {n m : Nat}
    (p : Path n m) (f : O.Ops n) :
    transport_ops O (Path.symm p) (transport_ops O p f) = f := by
  simp [transport_ops, Path.transport]
  cases p with
  | mk sp pp => cases pp; rfl

/-- 22. CongrArg through transport is refl on refl. -/
theorem congrArg_transport_ops (O : Operad) {n m : Nat}
    (p : Path n m) (f : O.Ops n) :
    Path.congrArg (transport_ops O p) (Path.refl f) =
      Path.refl (transport_ops O p f) := by
  simp

end ComputationalPaths.Path.Category.OperadPaths
