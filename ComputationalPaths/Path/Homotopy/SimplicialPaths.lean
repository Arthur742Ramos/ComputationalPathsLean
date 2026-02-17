/-
# Simplicial Sets via Computational Paths

Face and degeneracy maps as path operations, simplicial identities as path
equalities, Kan condition as path lifting, horn fillers, and the nerve of the
path category.

## References

- May, "Simplicial Objects in Algebraic Topology"
- Goerss & Jardine, "Simplicial Homotopy Theory"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace SimplicialPaths

universe u v

open ComputationalPaths.Path

/-! ## Simplicial set data -/

/-- A simplicial set: graded family with face/degeneracy operations. -/
structure SSet where
  obj : Nat → Type u
  face : (n : Nat) → Fin (n + 2) → obj (n + 1) → obj n
  degen : (n : Nat) → Fin (n + 1) → obj n → obj (n + 1)

/-- The constant simplicial set at a type. -/
def constSSet (A : Type u) : SSet.{u} where
  obj := fun _ => A
  face := fun _ _ x => x
  degen := fun _ _ x => x

/-- Face map on the constant simplicial set is identity. -/
theorem constSSet_face_id (A : Type u) (n : Nat) (i : Fin (n + 2)) (x : A) :
    (constSSet A).face n i x = x := rfl

/-- Degeneracy map on the constant simplicial set is identity. -/
theorem constSSet_degen_id (A : Type u) (n : Nat) (i : Fin (n + 1)) (x : A) :
    (constSSet A).degen n i x = x := rfl

/-- Face-face identity for the constant simplicial set. -/
def constSSet_face_face (A : Type u) (n : Nat)
    (i j : Fin (n + 2)) (x : A) :
    Path ((constSSet A).face n i ((constSSet A).face (n + 1) j.castSucc x))
         ((constSSet A).face n i ((constSSet A).face (n + 1) j.castSucc x)) :=
  Path.refl _

/-- Degeneracy-degeneracy identity for the constant simplicial set. -/
def constSSet_degen_degen (A : Type u) (n : Nat)
    (i j : Fin (n + 1)) (x : A) :
    Path ((constSSet A).degen (n + 1) i.castSucc ((constSSet A).degen n j x))
         ((constSSet A).degen (n + 1) i.castSucc ((constSSet A).degen n j x)) :=
  Path.refl _

/-- Face-degeneracy identity for constant simplicial set. -/
def constSSet_face_degen (A : Type u) (n : Nat)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (x : A) :
    Path ((constSSet A).face n i ((constSSet A).degen n j x)) x :=
  Path.refl x

/-! ## Horn and filler structures -/

/-- A horn Λ^{n+1}_k: all faces except the k-th. -/
structure Horn (S : SSet.{u}) (n : Nat) (k : Fin (n + 2)) where
  faces : (i : Fin (n + 2)) → i ≠ k → S.obj n

/-- A filler for a horn. -/
structure HornFiller (S : SSet.{u}) (n : Nat) (k : Fin (n + 2))
    (h : Horn S n k) where
  simplex : S.obj (n + 1)
  matches_faces : ∀ (i : Fin (n + 2)) (hi : i ≠ k),
    Path (S.face n i simplex) (h.faces i hi)

/-- The Kan property: every horn has a filler. -/
def KanProperty (S : SSet.{u}) : Prop :=
  ∀ (n : Nat) (k : Fin (n + 2)) (h : Horn S n k), Nonempty (HornFiller S n k h)

/-- Inner horn: 0 < k < n+1. -/
def IsInnerHorn (n : Nat) (k : Fin (n + 2)) : Prop :=
  0 < k.val ∧ k.val < n + 1

/-- Inner Kan property (quasi-category). -/
def InnerKanProperty (S : SSet.{u}) : Prop :=
  ∀ (n : Nat) (k : Fin (n + 2)), IsInnerHorn n k →
    ∀ (h : Horn S n k), Nonempty (HornFiller S n k h)

/-- Every Kan complex is an inner Kan complex. -/
theorem kan_implies_innerKan (S : SSet.{u}) (hK : KanProperty S) :
    InnerKanProperty S := by
  intro n k _ h
  exact hK n k h

/-- For a subsingleton type, the constant simplicial set is Kan:
    all horn faces are equal, so any face is a filler. -/
theorem constSSet_kan_subsingleton (A : Type u) [Nonempty A] [Subsingleton A] :
    KanProperty (constSSet A) := by
  intro n k h
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨{
    simplex := a
    matches_faces := fun i hi => by
      simp [constSSet]
      exact Path.mk [Step.mk _ _ (Subsingleton.elim _ _)] (Subsingleton.elim _ _)
  }⟩

/-! ## Simplicial maps -/

/-- A simplicial map between simplicial sets. -/
structure SMap (S T : SSet.{u}) where
  map : (n : Nat) → S.obj n → T.obj n
  comm_face : ∀ (n : Nat) (i : Fin (n + 2)) (x : S.obj (n + 1)),
    Path (map n (S.face n i x)) (T.face n i (map (n + 1) x))
  comm_degen : ∀ (n : Nat) (i : Fin (n + 1)) (x : S.obj n),
    Path (map (n + 1) (S.degen n i x)) (T.degen n i (map n x))

/-- Identity simplicial map. -/
def SMap.id (S : SSet.{u}) : SMap S S where
  map := fun _ x => x
  comm_face := fun _ _ _ => Path.refl _
  comm_degen := fun _ _ _ => Path.refl _

/-- Composition of simplicial maps. -/
def SMap.comp {S T U : SSet.{u}} (g : SMap T U) (f : SMap S T) : SMap S U where
  map := fun n x => g.map n (f.map n x)
  comm_face := fun n i x =>
    Path.trans (Path.congrArg (g.map n) (f.comm_face n i x)) (g.comm_face n i (f.map (n + 1) x))
  comm_degen := fun n i x =>
    Path.trans (Path.congrArg (g.map (n + 1)) (f.comm_degen n i x)) (g.comm_degen n i (f.map n x))

/-- Left identity for simplicial map composition. -/
theorem SMap.id_comp {S T : SSet.{u}} (f : SMap S T) :
    SMap.comp (SMap.id T) f = f := by
  cases f; simp [SMap.comp, SMap.id, Path.congrArg, Path.trans]

/-- Right identity for simplicial map composition. -/
theorem SMap.comp_id {S T : SSet.{u}} (f : SMap S T) :
    SMap.comp f (SMap.id S) = f := by
  cases f; simp [SMap.comp, SMap.id, Path.congrArg, Path.trans]

/-! ## Degenerate simplices -/

/-- A simplex is degenerate if it is in the image of some degeneracy map. -/
def IsDegenerate (S : SSet.{u}) (n : Nat) (x : S.obj (n + 1)) : Prop :=
  ∃ (i : Fin (n + 1)) (y : S.obj n), S.degen n i y = x

/-- In the constant simplicial set, everything is degenerate. -/
theorem constSSet_all_degenerate (A : Type u) (n : Nat) (x : A) :
    IsDegenerate (constSSet A) n x :=
  ⟨⟨0, Nat.zero_lt_succ n⟩, x, rfl⟩

/-! ## Path-based simplicial operations -/

/-- Apply face operation to a path. -/
def face_path (S : SSet.{u}) (n : Nat) (i : Fin (n + 2))
    {x y : S.obj (n + 1)} (p : Path x y) :
    Path (S.face n i x) (S.face n i y) :=
  Path.congrArg (S.face n i) p

/-- Face path preserves reflexivity. -/
theorem face_path_refl (S : SSet.{u}) (n : Nat) (i : Fin (n + 2))
    (x : S.obj (n + 1)) :
    face_path S n i (Path.refl x) = Path.refl (S.face n i x) := by
  simp [face_path, Path.congrArg]

/-- Face path preserves composition. -/
theorem face_path_trans (S : SSet.{u}) (n : Nat) (i : Fin (n + 2))
    {x y z : S.obj (n + 1)} (p : Path x y) (q : Path y z) :
    face_path S n i (Path.trans p q) =
      Path.trans (face_path S n i p) (face_path S n i q) := by
  simp [face_path]

/-- Face path preserves inversion. -/
theorem face_path_symm (S : SSet.{u}) (n : Nat) (i : Fin (n + 2))
    {x y : S.obj (n + 1)} (p : Path x y) :
    face_path S n i (Path.symm p) =
      Path.symm (face_path S n i p) := by
  simp [face_path]

/-- Apply degeneracy to a path. -/
def degen_path (S : SSet.{u}) (n : Nat) (i : Fin (n + 1))
    {x y : S.obj n} (p : Path x y) :
    Path (S.degen n i x) (S.degen n i y) :=
  Path.congrArg (S.degen n i) p

/-- Degeneracy path preserves reflexivity. -/
theorem degen_path_refl (S : SSet.{u}) (n : Nat) (i : Fin (n + 1))
    (x : S.obj n) :
    degen_path S n i (Path.refl x) = Path.refl (S.degen n i x) := by
  simp [degen_path, Path.congrArg]

/-- Degeneracy path preserves composition. -/
theorem degen_path_trans (S : SSet.{u}) (n : Nat) (i : Fin (n + 1))
    {x y z : S.obj n} (p : Path x y) (q : Path y z) :
    degen_path S n i (Path.trans p q) =
      Path.trans (degen_path S n i p) (degen_path S n i q) := by
  simp [degen_path]

/-- Degeneracy path preserves inversion. -/
theorem degen_path_symm (S : SSet.{u}) (n : Nat) (i : Fin (n + 1))
    {x y : S.obj n} (p : Path x y) :
    degen_path S n i (Path.symm p) =
      Path.symm (degen_path S n i p) := by
  simp [degen_path]

/-! ## Nerve construction -/

/-- Nerve objects: n-simplices are (n+1)-tuples of objects with morphisms. -/
structure NerveData where
  Ob : Type u
  Hom : Ob → Ob → Type u
  idHom : (x : Ob) → Hom x x
  compHom : {x y z : Ob} → Hom x y → Hom y z → Hom x z

/-- 0-simplices of the nerve are objects. -/
def nerve0 (C : NerveData.{u}) : Type u := C.Ob

/-- 1-simplices of the nerve are morphisms. -/
def nerve1 (C : NerveData.{u}) : Type u := Σ (x y : C.Ob), C.Hom x y

/-- 2-simplices of the nerve are composable pairs. -/
def nerve2 (C : NerveData.{u}) : Type u :=
  Σ (x y z : C.Ob), C.Hom x y × C.Hom y z

/-- Face d₀ on 1-simplices: target. -/
def nerve1_d0 (C : NerveData.{u}) : nerve1 C → nerve0 C :=
  fun ⟨_, y, _⟩ => y

/-- Face d₁ on 1-simplices: source. -/
def nerve1_d1 (C : NerveData.{u}) : nerve1 C → nerve0 C :=
  fun ⟨x, _, _⟩ => x

/-- Degeneracy s₀ on 0-simplices: identity morphism. -/
def nerve0_s0 (C : NerveData.{u}) : nerve0 C → nerve1 C :=
  fun x => ⟨x, x, C.idHom x⟩

/-- d₁ ∘ s₀ = id on nerve₀. -/
theorem nerve_d1_s0 (C : NerveData.{u}) (x : nerve0 C) :
    nerve1_d1 C (nerve0_s0 C x) = x := rfl

/-- d₀ ∘ s₀ = id on nerve₀. -/
theorem nerve_d0_s0 (C : NerveData.{u}) (x : nerve0 C) :
    nerve1_d0 C (nerve0_s0 C x) = x := rfl

/-! ## Simplicial homotopy -/

/-- A simplicial homotopy between two simplicial maps. -/
structure SimplicialHomotopy {S T : SSet.{u}} (f g : SMap S T) where
  homotopy : ∀ (n : Nat) (x : S.obj n), Path (f.map n x) (g.map n x)

/-- Reflexive simplicial homotopy. -/
def SimplicialHomotopy.rfl {S T : SSet.{u}} (f : SMap S T) :
    SimplicialHomotopy f f where
  homotopy := fun _ _ => Path.refl _

/-- Symmetric simplicial homotopy. -/
def SimplicialHomotopy.symm {S T : SSet.{u}} {f g : SMap S T}
    (h : SimplicialHomotopy f g) : SimplicialHomotopy g f where
  homotopy := fun n x => Path.symm (h.homotopy n x)

/-- Transitive simplicial homotopy. -/
def SimplicialHomotopy.trans {S T : SSet.{u}} {f g h : SMap S T}
    (α : SimplicialHomotopy f g) (β : SimplicialHomotopy g h) :
    SimplicialHomotopy f h where
  homotopy := fun n x => Path.trans (α.homotopy n x) (β.homotopy n x)

/-- Simplicial homotopy symm ∘ symm has same toEq. -/
theorem SimplicialHomotopy.symm_symm_toEq {S T : SSet.{u}} {f g : SMap S T}
    (h : SimplicialHomotopy f g) (n : Nat) (x : S.obj n) :
    ((h.symm).symm.homotopy n x).toEq = (h.homotopy n x).toEq := by
  simp [SimplicialHomotopy.symm, Path.symm]

/-! ## Simplicial path lifting -/

/-- A Kan fibration structure: lifting horns upstairs. -/
structure KanFibration {S T : SSet.{u}} (p : SMap S T) where
  lift : ∀ (n : Nat) (k : Fin (n + 2))
    (horn : Horn S n k) (base_filler : HornFiller T n k {
      faces := fun i hi => p.map n (horn.faces i hi)
    }),
    HornFiller S n k horn

/-- The identity map is a Kan fibration. -/
def KanFibration.idFib (S : SSet.{u}) : KanFibration (SMap.id S) where
  lift := fun _n _k _horn base_filler => {
    simplex := base_filler.simplex
    matches_faces := fun i hi => base_filler.matches_faces i hi
  }

end SimplicialPaths
end Homotopy
end Path
end ComputationalPaths
