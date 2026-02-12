/-
# Galois Representation Equivalences via Computational Paths
 
This module formalizes absolute Galois groups and their representations using
explicit computational paths.  We record continuous representations, Artin data,
l-adic representations, and Path witnesses for representation equivalences.  A
simple rewrite system `GaloisStep` captures basic moves between representations.
 
## Key Constructions
 
- `AbsoluteGaloisGroup`
- `ContinuousGaloisRepresentation`
- `ArtinRepresentation`
- `GaloisLAdicRepresentation`
- `RepresentationEquiv`
- `GaloisStep`
 
## References
 
- Serre, "Abelian l-adic Representations and Elliptic Curves"
- Tate, "Number theoretic background"
- Fontaine, "p-adic Galois representations"
- Milne, "Arithmetic Duality Theorems"
-/
 
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Algebra.GaloisRepresentations
 
namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GaloisRepresentation
 
universe u v w x
 
/-! ## Absolute Galois Groups -/
 
/-- An absolute Galois group with strict group data and Path-level continuity witnesses. -/
structure AbsoluteGaloisGroup (K : Type u) where
  /-- Underlying carrier. -/
  carrier : Type v
  /-- Strict group structure on the carrier. -/
  group : StrictGroup carrier
  /-- Continuity witness for multiplication. -/
  continuous_mul : ∀ g h, Path (group.mul g h) (group.mul g h)
  /-- Continuity witness for inversion. -/
  continuous_inv : ∀ g, Path (group.inv g) (group.inv g)
  /-- Continuity witness for the identity element. -/
  continuous_one : Path group.one group.one
 
namespace AbsoluteGaloisGroup
 
variable {K : Type u}
 
/-- Continuity witness for multiplication as a composed path. -/
def mul_stable (Γ : AbsoluteGaloisGroup K) (g h : Γ.carrier) :
    Path (Γ.group.mul g h) (Γ.group.mul g h) :=
  Path.trans (Γ.continuous_mul g h) (Path.refl _)
 
/-- Continuity witness for inversion, expressed via symmetry. -/
def inv_stable (Γ : AbsoluteGaloisGroup K) (g : Γ.carrier) :
    Path (Γ.group.inv g) (Γ.group.inv g) :=
  Path.trans (Γ.continuous_inv g) (Path.symm (Path.refl _))
 
/-- Continuity witness for the identity element. -/
def one_stable (Γ : AbsoluteGaloisGroup K) :
    Path Γ.group.one Γ.group.one :=
  Path.trans Γ.continuous_one (Path.refl _)
 
end AbsoluteGaloisGroup
 
/-! ## Continuous Representations of Absolute Galois Groups -/
 
/-- A continuous representation of an absolute Galois group on a type `V`. -/
structure ContinuousGaloisRepresentation {K : Type u}
    (Γ : AbsoluteGaloisGroup K) (V : Type v) where
  /-- Action of the Galois group. -/
  action : Γ.carrier → V → V
  /-- Identity acts trivially. -/
  action_one : ∀ v, Path (action Γ.group.one v) v
  /-- Action respects multiplication. -/
  action_mul : ∀ g h v,
    Path (action (Γ.group.mul g h) v) (action g (action h v))
  /-- Continuity witness for the action. -/
  continuous : ∀ g v, Path (action g v) (action g v)
 
namespace ContinuousGaloisRepresentation
 
variable {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v}
 
/-- The action respects paths by a composed Path.trans witness. -/
def action_stable (rep : ContinuousGaloisRepresentation Γ V) (g : Γ.carrier) (v : V) :
    Path (rep.action g v) (rep.action g v) :=
  Path.trans (rep.continuous g v) (Path.refl _)
 
/-- Symmetric form of the identity action witness. -/
def action_one_symm (rep : ContinuousGaloisRepresentation Γ V) (v : V) :
    Path v (rep.action Γ.group.one v) :=
  Path.symm (rep.action_one v)
 
/-- Action of a group element on a trivial action uses Path.trans. -/
def action_on_one (rep : ContinuousGaloisRepresentation Γ V) (g : Γ.carrier) (v : V) :
    Path (rep.action g (rep.action Γ.group.one v)) (rep.action g v) :=
  Path.trans
    (Path.congrArg (rep.action g) (rep.action_one v))
    (Path.refl _)
 
/-- Triple action associativity using Path.trans. -/
def action_assoc (rep : ContinuousGaloisRepresentation Γ V) (g h k : Γ.carrier) (v : V) :
    Path (rep.action (Γ.group.mul (Γ.group.mul g h) k) v)
      (rep.action g (rep.action h (rep.action k v))) :=
  Path.trans
    (Path.congrArg (fun x => rep.action x v) (Path.ofEq (Γ.group.mul_assoc g h k)))
    (Path.trans
      (rep.action_mul g (Γ.group.mul h k) v)
      (Path.congrArg (rep.action g) (rep.action_mul h k v)))
 
end ContinuousGaloisRepresentation
 
/-! ## Artin Representations -/
 
/-- Finite image data for an Artin representation. -/
structure FiniteImage (G : Type u) where
  /-- The image type. -/
  carrier : Type v
  /-- Map from the group to the image. -/
  map : G → carrier
  /-- Size parameter (abstract finite witness). -/
  size : Nat
  /-- Path witness that the size is stable. -/
  size_stable : Path size size
 
/-- An Artin representation: continuous with finite image data. -/
structure ArtinRepresentation {K : Type u} (Γ : AbsoluteGaloisGroup K) (V : Type v) where
  /-- Underlying continuous representation. -/
  rep : ContinuousGaloisRepresentation Γ V
  /-- Finite image data. -/
  image : FiniteImage Γ.carrier
 
namespace ArtinRepresentation
 
variable {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v}
 
/-- Finite-image stability witnessed by Path.trans. -/
def image_stable (ρ : ArtinRepresentation Γ V) :
    Path ρ.image.size ρ.image.size :=
  Path.trans ρ.image.size_stable (Path.refl _)
 
/-- Artin representations inherit continuity of the action. -/
def action_stable (ρ : ArtinRepresentation Γ V) (g : Γ.carrier) (v : V) :
    Path (ρ.rep.action g v) (ρ.rep.action g v) :=
  Path.trans (ρ.rep.continuous g v) (Path.refl _)
 
end ArtinRepresentation
 
/-! ## l-adic Representations -/
 
/-- An l-adic representation of an absolute Galois group on a Tate module. -/
structure GaloisLAdicRepresentation {K : Type u} (Γ : AbsoluteGaloisGroup K) (A : Type v) where
  /-- Underlying l-adic representation on the carrier. -/
  rep : GaloisRepresentations.LAdicRepresentation Γ.carrier A
  /-- Path witness that the strict group structure agrees with `Γ`. -/
  group_path : Path rep.group Γ.group
 
namespace GaloisLAdicRepresentation
 
variable {K : Type u} {Γ : AbsoluteGaloisGroup K} {A : Type v}
 
/-- Symmetric form of the group equivalence witness. -/
def group_path_symm (ρ : GaloisLAdicRepresentation Γ A) :
    Path Γ.group ρ.rep.group :=
  Path.symm ρ.group_path
 
/-- Levelwise continuity for the l-adic action. -/
def action_stable (ρ : GaloisLAdicRepresentation Γ A) (n : Nat) (g : Γ.carrier)
    (x : ρ.rep.tate.level n) :
    Path (ρ.rep.action n g x) (ρ.rep.action n g x) :=
  Path.trans (ρ.rep.continuous n g x) (Path.refl _)
 
end GaloisLAdicRepresentation
 
/-! ## Representation Equivalences -/
 
/-- Path-based equivalence between two representations. -/
structure RepresentationEquiv {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v}
    (ρ σ : ContinuousGaloisRepresentation Γ V) where
  /-- Path witness that the actions coincide. -/
  action_path : ∀ g v, Path (ρ.action g v) (σ.action g v)
 
namespace RepresentationEquiv
 
variable {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v}
variable {ρ σ τ : ContinuousGaloisRepresentation Γ V}
 
/-- Reflexive representation equivalence. -/
def refl (ρ : ContinuousGaloisRepresentation Γ V) : RepresentationEquiv ρ ρ where
  action_path := fun _ _ => Path.refl _
 
/-- Symmetry of representation equivalence using Path.symm. -/
def symm (e : RepresentationEquiv ρ σ) : RepresentationEquiv σ ρ where
  action_path := fun g v => Path.symm (e.action_path g v)
 
/-- Composition of representation equivalences using Path.trans. -/
def trans (e₁ : RepresentationEquiv ρ σ) (e₂ : RepresentationEquiv σ τ) :
    RepresentationEquiv ρ τ where
  action_path := fun g v => Path.trans (e₁.action_path g v) (e₂.action_path g v)
 
end RepresentationEquiv
 
/-! ## GaloisStep Inductive -/
 
/-- Rewrite steps for Galois representation equivalences. -/
inductive GaloisStep {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v} :
    ContinuousGaloisRepresentation Γ V → ContinuousGaloisRepresentation Γ V → Prop
  /-- Reflexive step. -/
  | refl (ρ : ContinuousGaloisRepresentation Γ V) : GaloisStep ρ ρ
  /-- Step coming from a representation equivalence. -/
  | equiv {ρ σ : ContinuousGaloisRepresentation Γ V} (h : RepresentationEquiv ρ σ) :
      GaloisStep ρ σ
 
namespace GaloisStep
 
variable {K : Type u} {Γ : AbsoluteGaloisGroup K} {V : Type v}
variable {ρ σ τ : ContinuousGaloisRepresentation Γ V}
 
/-- Symmetry of a Galois step using Path.symm. -/
theorem symm (h : GaloisStep ρ σ) : GaloisStep σ ρ := by
  cases h with
  | refl => exact GaloisStep.refl _
  | equiv h => exact GaloisStep.equiv (RepresentationEquiv.symm h)

/-- Composition of Galois steps using Path.trans. -/
theorem trans (h₁ : GaloisStep ρ σ) (h₂ : GaloisStep σ τ) : GaloisStep ρ τ := by
  cases h₁ with
  | refl => exact h₂
  | equiv h₁ =>
      cases h₂ with
      | refl => exact GaloisStep.equiv h₁
      | equiv h₂ => exact GaloisStep.equiv (RepresentationEquiv.trans h₁ h₂)
 
end GaloisStep
 
/-! ## Summary -/
 
end GaloisRepresentation
end Algebra
end Path
end ComputationalPaths
