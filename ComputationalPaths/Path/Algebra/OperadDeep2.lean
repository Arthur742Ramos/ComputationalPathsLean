/-
# Deep Operadic Structures: Koszul Duality, Bar-Cobar, A∞/E∞ Operads

This module develops deep operadic algebra with computational-path witnesses:
operadic composition with associativity/equivariance, Koszul duality,
the bar-cobar adjunction, and A∞ and E∞ operads.

## References

- Loday & Vallette, "Algebraic Operads"
- Markl, Shnider & Stasheff, "Operads in Algebra, Topology, and Physics"
- Fresse, "Modules over Operads and Functors"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperadDeep2

open ComputationalPaths.Path

universe u v

/-! ## Permutations -/

structure OPerm (n : Nat) where
  fwd : Fin n → Fin n
  bwd : Fin n → Fin n
  fwd_bwd : ∀ i, fwd (bwd i) = i
  bwd_fwd : ∀ i, bwd (fwd i) = i

def OPerm.id (n : Nat) : OPerm n where
  fwd := _root_.id; bwd := _root_.id
  fwd_bwd := fun _ => rfl; bwd_fwd := fun _ => rfl

def OPerm.comp {n : Nat} (σ τ : OPerm n) : OPerm n where
  fwd := σ.fwd ∘ τ.fwd
  bwd := τ.bwd ∘ σ.bwd
  fwd_bwd i := by
    show σ.fwd (τ.fwd (τ.bwd (σ.bwd i))) = i
    rw [τ.fwd_bwd, σ.fwd_bwd]
  bwd_fwd i := by
    show τ.bwd (σ.bwd (σ.fwd (τ.fwd i))) = i
    rw [σ.bwd_fwd, τ.bwd_fwd]

def OPerm.inv {n : Nat} (σ : OPerm n) : OPerm n where
  fwd := σ.bwd; bwd := σ.fwd
  fwd_bwd := σ.bwd_fwd; bwd_fwd := σ.fwd_bwd

theorem OPerm.comp_id {n : Nat} (σ : OPerm n) :
    OPerm.comp σ (OPerm.id n) = σ := by cases σ; rfl

theorem OPerm.id_comp {n : Nat} (σ : OPerm n) :
    OPerm.comp (OPerm.id n) σ = σ := by cases σ; rfl

theorem OPerm.comp_assoc {n : Nat} (σ τ ρ : OPerm n) :
    OPerm.comp (OPerm.comp σ τ) ρ = OPerm.comp σ (OPerm.comp τ ρ) := by
  cases σ; cases τ; cases ρ; rfl

theorem OPerm.comp_inv {n : Nat} (σ : OPerm n) :
    OPerm.comp σ (OPerm.inv σ) = OPerm.id n := by
  cases σ with | mk f b fb bf =>
  simp only [OPerm.comp, OPerm.inv, OPerm.id]
  congr 1 <;> funext i <;> simp [Function.comp, fb]

theorem OPerm.inv_comp {n : Nat} (σ : OPerm n) :
    OPerm.comp (OPerm.inv σ) σ = OPerm.id n := by
  cases σ with | mk f b fb bf =>
  simp only [OPerm.comp, OPerm.inv, OPerm.id]
  congr 1 <;> funext i <;> simp [Function.comp, bf]

theorem OPerm.inv_inv {n : Nat} (σ : OPerm n) :
    OPerm.inv (OPerm.inv σ) = σ := by cases σ; rfl

/-! ## Graded collections -/

structure GradedCollection where
  arity : Nat → Type u

/-! ## Operad with ∘ᵢ composition -/

/-- An operad with partial composition ∘ᵢ. Arities use (n+1) to avoid subtraction. -/
structure Operad extends GradedCollection.{u} where
  unit : arity 1
  circI : {n m : Nat} → arity (n + 1) → Fin (n + 1) → arity (m + 1) →
    arity (n + m + 1)
  action : {n : Nat} → OPerm n → arity n → arity n
  action_id : {n : Nat} → ∀ (x : arity n), action (OPerm.id n) x = x
  action_comp : {n : Nat} → ∀ (σ τ : OPerm n) (x : arity n),
    action (OPerm.comp σ τ) x = action σ (action τ x)

-- 1. Path-valued action identity
def Operad.action_id_path (O : Operad.{u}) {n : Nat} (x : O.arity n) :
    Path (O.action (OPerm.id n) x) x :=
  Path.stepChain (O.action_id x)

-- 2. Path-valued action composition
def Operad.action_comp_path (O : Operad.{u}) {n : Nat}
    (σ τ : OPerm n) (x : O.arity n) :
    Path (O.action (OPerm.comp σ τ) x) (O.action σ (O.action τ x)) :=
  Path.stepChain (O.action_comp σ τ x)

-- 3. Action by inverse is an involution
def Operad.action_inv_path (O : Operad.{u}) {n : Nat}
    (σ : OPerm n) (x : O.arity n) :
    Path (O.action (OPerm.inv σ) (O.action σ x)) x := by
  have h := O.action_comp (OPerm.inv σ) σ x
  rw [OPerm.inv_comp] at h
  exact Path.stepChain (h.symm.trans (O.action_id x))

-- 4. Double action inverse
theorem Operad.double_action_inv (O : Operad.{u}) {n : Nat}
    (σ : OPerm n) (x : O.arity n) :
    O.action (OPerm.inv σ) (O.action σ x) =
    O.action (OPerm.id n) x := by
  rw [← O.action_comp]; congr 1; exact OPerm.inv_comp σ

/-! ## Sequential associativity -/

-- 5. Sequential associativity (using HEq for arity matching)
structure SeqAssoc (O : Operad.{u}) where
  seq : {n m k : Nat} →
    (f : O.arity (n + 1)) → (i : Fin (n + 1)) →
    (g : O.arity (m + 1)) → (j : Fin (m + 1)) →
    (h : O.arity (k + 1)) →
    HEq (O.circI (n := n + m) (O.circI f i g) ⟨i.val + j.val, by omega⟩ h)
         (O.circI (m := m + k) f i (O.circI g j h))

/-! ## Equivariance -/

-- 6. Equivariance structure
structure Equivariant (O : Operad.{u}) where
  equiv : {n m : Nat} → (f : O.arity (n + 1)) → (σ : OPerm (n + 1)) →
    (i : Fin (n + 1)) → (g : O.arity (m + 1)) →
    O.circI (O.action σ f) i g = O.circI f (σ.fwd i) g

-- 7. Path-valued equivariance
def Equivariant.path {O : Operad.{u}} (eq : Equivariant O) {n m : Nat}
    (f : O.arity (n + 1)) (σ : OPerm (n + 1))
    (i : Fin (n + 1)) (g : O.arity (m + 1)) :
    Path (O.circI (O.action σ f) i g) (O.circI f (σ.fwd i) g) :=
  Path.stepChain (eq.equiv f σ i g)

/-! ## Quadratic data and Koszul duality -/

-- 8. Quadratic datum
structure QuadraticDatum where
  gen : Type u
  rel : (gen × gen) → Prop

-- 9. Koszul dual
def QuadraticDatum.koszulDual (Q : QuadraticDatum.{u}) : QuadraticDatum.{u} where
  gen := Q.gen
  rel := fun p => ¬ Q.rel p

-- 10. Double Koszul dual is involutive
theorem QuadraticDatum.koszulDual_involutive (Q : QuadraticDatum.{u}) :
    Q.koszulDual.koszulDual.rel = Q.rel := by
  funext p
  simp only [QuadraticDatum.koszulDual]
  exact propext ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

-- 11. Path-valued Koszul involutivity
def QuadraticDatum.koszulDual_path (Q : QuadraticDatum.{u}) :
    Path Q.koszulDual.koszulDual.rel Q.rel :=
  Path.stepChain Q.koszulDual_involutive

-- 12. Koszul operad
structure KoszulOperad extends QuadraticDatum.{u} where
  is_koszul : Prop

/-! ## Bar and cobar complexes -/

structure GradedMod where
  deg : Int → Type u
  zero : (n : Int) → deg n

-- 13. Bar complex
structure BarComplex (P : GradedCollection.{u}) where
  bar : GradedMod.{u}
  codiff : (n : Int) → bar.deg n → bar.deg (n - 1)
  codiff_sq : ∀ (n : Int) (x : bar.deg n),
    codiff (n - 1) (codiff n x) = bar.zero (n - 1 - 1)

-- 14. Path-valued d² = 0
def BarComplex.codiff_sq_path {P : GradedCollection.{u}} (B : BarComplex P)
    (n : Int) (x : B.bar.deg n) :
    Path (B.codiff (n - 1) (B.codiff n x)) (B.bar.zero (n - 1 - 1)) :=
  Path.stepChain (B.codiff_sq n x)

-- 15. Cobar complex
structure CobarComplex (C : GradedCollection.{u}) where
  cobar : GradedMod.{u}
  diff : (n : Int) → cobar.deg n → cobar.deg (n + 1)
  diff_sq : ∀ (n : Int) (x : cobar.deg n),
    diff (n + 1) (diff n x) = cobar.zero (n + 1 + 1)

-- 16. Path-valued d² = 0 for cobar
def CobarComplex.diff_sq_path {C : GradedCollection.{u}} (Ω : CobarComplex C)
    (n : Int) (x : Ω.cobar.deg n) :
    Path (Ω.diff (n + 1) (Ω.diff n x)) (Ω.cobar.zero (n + 1 + 1)) :=
  Path.stepChain (Ω.diff_sq n x)

/-! ## Twisting morphisms and bar-cobar adjunction -/

-- 17. Twisting morphism
structure TwistingMorphism (C P : GradedCollection.{u}) where
  alpha : (n : Nat) → C.arity n → P.arity n

-- 18. Identity twisting morphism
def TwistingMorphism.idTwist (P : GradedCollection.{u}) : TwistingMorphism P P where
  alpha := fun _ x => x

-- 19. Path from identity twisting morphism
def TwistingMorphism.idTwist_path (P : GradedCollection.{u}) (n : Nat)
    (x : P.arity n) :
    Path ((TwistingMorphism.idTwist P).alpha n x) x :=
  Path.refl _

-- 20. Bar-cobar adjunction
structure BarCobarAdj (P C : GradedCollection.{u})
    (B : BarComplex P) (Ω : CobarComplex C) where
  unit : (n : Nat) → P.arity n → Ω.cobar.deg (Int.ofNat n)
  counit : (n : Int) → B.bar.deg n → C.arity n.toNat

/-! ## A∞ operad -/

-- 21. A∞ operad: one μₙ at each arity
structure AInfOperad where
  mu : Nat → Type u
  mu2 : mu 2
  comp : {n m : Nat} → mu (n + 1) → Fin (n + 1) → mu (m + 1) → mu (n + m + 1)
  stasheff : ∀ (n : Nat), (f g : mu (n + 2)) → f = g

-- 22. A∞ contractibility path
def AInfOperad.contract_path (O : AInfOperad.{u}) (n : Nat)
    (f g : O.mu (n + 2)) : Path f g :=
  Path.stepChain (O.stasheff n f g)

-- 23. A∞ transitivity
theorem AInfOperad.contract_trans (O : AInfOperad.{u}) (n : Nat)
    (f g h : O.mu (n + 2)) :
    (Path.trans (O.contract_path n f g) (O.contract_path n g h)).proof =
    (O.contract_path n f h).proof := rfl

/-! ## E∞ operad -/

-- 24. E∞ operad: contractible Σ-free
structure EInfOperad where
  ops : Nat → Type u
  action : {n : Nat} → OPerm n → ops n → ops n
  action_id : {n : Nat} → ∀ (x : ops n), action (OPerm.id n) x = x
  action_comp : {n : Nat} → ∀ (σ τ : OPerm n) (x : ops n),
    action (OPerm.comp σ τ) x = action σ (action τ x)
  contractible : {n : Nat} → ∀ (x y : ops n), x = y
  free_action : {n : Nat} → ∀ (σ : OPerm n) (x : ops n),
    action σ x = x → σ = OPerm.id n

-- 25. E∞ contractibility path
def EInfOperad.contractible_path (E : EInfOperad.{u}) {n : Nat}
    (x y : E.ops n) : Path x y :=
  Path.stepChain (E.contractible x y)

-- 26. E∞ contractibility is transitive (proof level)
theorem EInfOperad.contractible_trans (E : EInfOperad.{u}) {n : Nat}
    (x y z : E.ops n) :
    (Path.trans (E.contractible_path x y) (E.contractible_path y z)).proof =
    (E.contractible_path x z).proof := rfl

-- 27. E∞ action on unique element yields that element
theorem EInfOperad.action_contractible (E : EInfOperad.{u}) {n : Nat}
    (σ : OPerm n) (x y : E.ops n) :
    E.action σ x = y :=
  E.contractible (E.action σ x) y

/-! ## Morphisms of graded collections -/

structure GCMorphism (P Q : GradedCollection.{u}) where
  map : (n : Nat) → P.arity n → Q.arity n

def GCMorphism.id (P : GradedCollection.{u}) : GCMorphism P P where
  map := fun _ x => x

def GCMorphism.comp {P Q R : GradedCollection.{u}}
    (g : GCMorphism Q R) (f : GCMorphism P Q) : GCMorphism P R where
  map := fun n x => g.map n (f.map n x)

-- 28. Morphism composition left identity
theorem GCMorphism.comp_id {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    GCMorphism.comp f (GCMorphism.id P) = f := by cases f; rfl

-- 29. Morphism composition right identity
theorem GCMorphism.id_comp {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    GCMorphism.comp (GCMorphism.id Q) f = f := by cases f; rfl

-- 30. Morphism composition associativity
theorem GCMorphism.comp_assoc {P Q R S : GradedCollection.{u}}
    (h : GCMorphism R S) (g : GCMorphism Q R) (f : GCMorphism P Q) :
    GCMorphism.comp h (GCMorphism.comp g f) =
    GCMorphism.comp (GCMorphism.comp h g) f := by
  cases h; cases g; cases f; rfl

-- 31-33. Path-valued morphism laws
def GCMorphism.comp_id_path {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    Path (GCMorphism.comp f (GCMorphism.id P)) f :=
  Path.stepChain (GCMorphism.comp_id f)

def GCMorphism.id_comp_path {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    Path (GCMorphism.comp (GCMorphism.id Q) f) f :=
  Path.stepChain (GCMorphism.id_comp f)

def GCMorphism.comp_assoc_path {P Q R S : GradedCollection.{u}}
    (h : GCMorphism R S) (g : GCMorphism Q R) (f : GCMorphism P Q) :
    Path (GCMorphism.comp h (GCMorphism.comp g f))
         (GCMorphism.comp (GCMorphism.comp h g) f) :=
  Path.stepChain (GCMorphism.comp_assoc h g f)

/-! ## Endomorphism operad -/

-- 34. Endomorphism operad
def EndOperad (X : Type u) : GradedCollection.{u} where
  arity := fun n => (Fin n → X) → X

def EndOperad.unitOp (X : Type u) : (EndOperad X).arity 1 :=
  fun f => f ⟨0, by omega⟩

-- 35. Composition in End(X)
def EndOperad.circI (X : Type u) {n m : Nat}
    (f : (EndOperad X).arity (n + 1)) (i : Fin (n + 1))
    (g : (EndOperad X).arity (m + 1)) :
    (EndOperad X).arity (n + m + 1) :=
  fun args =>
    f (fun j =>
      if j.val = i.val then
        g (fun k => args ⟨i.val + k.val, by omega⟩)
      else if j.val < i.val then
        args ⟨j.val, by omega⟩
      else
        args ⟨j.val + m, by omega⟩)

/-! ## Suspension/desuspension -/

-- 36. Suspension of a graded collection
def GradedCollection.susp (P : GradedCollection.{u}) : GradedCollection.{u} where
  arity := fun n => P.arity (n + 1)

-- 37. Desuspension
def GradedCollection.desusp (P : GradedCollection.{u}) : GradedCollection.{u} where
  arity := fun n => match n with | 0 => PEmpty | n + 1 => P.arity n

-- 38. Suspension-desuspension recovery
theorem GradedCollection.susp_desusp_recover (P : GradedCollection.{u}) (n : Nat) :
    P.susp.desusp.arity (n + 1) = P.arity (n + 1) := by
  simp [susp, desusp]

/-! ## Free operad trees -/

-- 39. Free operad as trees
inductive FreeTree (P : GradedCollection.{u}) (X : Type u) where
  | leaf : X → FreeTree P X
  | node : {n : Nat} → P.arity n → (Fin n → FreeTree P X) → FreeTree P X

-- 40. Leaf injection is injective
theorem FreeTree.leaf_injective {P : GradedCollection.{u}} {X : Type u}
    (x y : X) (h : FreeTree.leaf (P := P) x = FreeTree.leaf y) : x = y := by
  injection h

def FreeTree.leaf_injective_path {P : GradedCollection.{u}} {X : Type u}
    (x y : X) (h : FreeTree.leaf (P := P) x = FreeTree.leaf y) : Path x y :=
  Path.stepChain (FreeTree.leaf_injective x y h)

/-! ## Operadic algebras -/

-- 41. Algebra over a graded collection
structure OperadAlg (P : GradedCollection.{u}) (X : Type u) where
  act : {n : Nat} → P.arity n → (Fin n → X) → X

-- 42. Algebra morphism
structure AlgMorphism {P : GradedCollection.{u}} {X Y : Type u}
    (A : OperadAlg P X) (B : OperadAlg P Y) where
  f : X → Y
  compat : {n : Nat} → (op : P.arity n) → (args : Fin n → X) →
    f (A.act op args) = B.act op (f ∘ args)

-- 43. Identity algebra morphism
def AlgMorphism.id {P : GradedCollection.{u}} {X : Type u}
    (A : OperadAlg P X) : AlgMorphism A A where
  f := _root_.id
  compat := fun _ _ => rfl

-- 44. Composition of algebra morphisms
def AlgMorphism.comp {P : GradedCollection.{u}} {X Y Z : Type u}
    {A : OperadAlg P X} {B : OperadAlg P Y} {C : OperadAlg P Z}
    (g : AlgMorphism B C) (φ : AlgMorphism A B) : AlgMorphism A C where
  f := g.f ∘ φ.f
  compat := fun op args => by
    show g.f (φ.f (A.act op args)) = C.act op (fun i => g.f (φ.f (args i)))
    rw [φ.compat op args, g.compat op (φ.f ∘ args)]
    rfl

-- 45. comp ∘ id = id
theorem AlgMorphism.comp_id {P : GradedCollection.{u}} {X Y : Type u}
    {A : OperadAlg P X} {B : OperadAlg P Y}
    (f : AlgMorphism A B) : AlgMorphism.comp f (AlgMorphism.id A) = f := by
  simp [AlgMorphism.comp, AlgMorphism.id]

-- 46. id ∘ comp = id
theorem AlgMorphism.id_comp {P : GradedCollection.{u}} {X Y : Type u}
    {A : OperadAlg P X} {B : OperadAlg P Y}
    (f : AlgMorphism A B) : AlgMorphism.comp (AlgMorphism.id B) f = f := by
  simp [AlgMorphism.comp, AlgMorphism.id]

/-! ## Coherence theorems -/

-- 47. Perm double inverse identity
theorem OPerm.double_inv_id {n : Nat} (σ : OPerm n) :
    OPerm.comp (OPerm.comp σ (OPerm.inv σ)) (OPerm.comp (OPerm.inv σ) σ) =
    OPerm.id n := by
  rw [OPerm.comp_inv, OPerm.inv_comp, OPerm.comp_id]

-- 48. Path-valued double inverse
def OPerm.double_inv_id_path {n : Nat} (σ : OPerm n) :
    Path (OPerm.comp (OPerm.comp σ (OPerm.inv σ)) (OPerm.comp (OPerm.inv σ) σ))
         (OPerm.id n) :=
  Path.stepChain (OPerm.double_inv_id σ)

-- 49. Morphism path round-trip (proof-level)
theorem morphism_path_roundtrip
    {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    (Path.trans (GCMorphism.comp_id_path f)
               (Path.symm (GCMorphism.comp_id_path f))).proof =
    (Path.refl f).proof := rfl

-- 50. E∞ action path coherence (proof-level)
theorem EInf_action_round_trip (E : EInfOperad.{u}) {n : Nat}
    (x y : E.ops n) :
    (Path.trans (E.contractible_path x y)
               (Path.symm (E.contractible_path x y))).proof =
    (Path.refl x).proof := rfl

-- 51. Operadic path coherence (proof-level)
theorem operadic_path_coherence
    {P Q : GradedCollection.{u}} (f : GCMorphism P Q) :
    (Path.trans (GCMorphism.id_comp_path f)
               (Path.symm (GCMorphism.id_comp_path f))).proof =
    (Path.refl f).proof := rfl

end OperadDeep2
end Algebra
end Path
end ComputationalPaths
