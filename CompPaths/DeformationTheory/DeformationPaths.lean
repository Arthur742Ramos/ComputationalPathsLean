import CompPaths.Core

namespace CompPaths
namespace DeformationTheory

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

/-- Formal deformations modeled by path witnesses between undeformed and deformed points. -/
structure FormalDeformation (A : Type u) where
  base : A → A
  deform : A → A
  witness : ∀ a, Path (base a) (deform a)

namespace FormalDeformation

variable {A : Type u}

/-- The first-order step induced by a deformation witness. -/
noncomputable def infinitesimalStep (D : FormalDeformation A) (a : A) : Step A :=
  Step.mk (D.base a) (D.deform a) (D.witness a).proof

noncomputable def infinitesimalStep_src (D : FormalDeformation A) (a : A) :
    (D.infinitesimalStep a).src = D.base a := rfl

noncomputable def infinitesimalStep_tgt (D : FormalDeformation A) (a : A) :
    (D.infinitesimalStep a).tgt = D.deform a := rfl

noncomputable def pushForward (D : FormalDeformation A) {a b : A} (p : Path a b) :
    Path (D.base a) (D.deform b) :=
  trans (D.witness a) (congrArg D.deform p)

noncomputable def pullForward (D : FormalDeformation A) {a b : A} (p : Path a b) :
    Path (D.base a) (D.deform b) :=
  trans (congrArg D.base p) (D.witness b)

end FormalDeformation

/-- Maurer-Cartan data encoded by computational paths at a basepoint. -/
structure MaurerCartanPath {A : Type u} (a : A) where
  omega : Path a a
  dOmega : Path a a
  bracket : Path a a
  equation : RwEq (trans dOmega bracket) (symm omega)

namespace MaurerCartanPath

variable {A : Type u}

noncomputable def trivial (a : A) : MaurerCartanPath a where
  omega := Path.refl a
  dOmega := Path.refl a
  bracket := Path.refl a
  equation := by
    simpa using (rweq_cmpA_refl_left (Path.refl a))

end MaurerCartanPath

/-- Deformation functors preserve paths, rewrite equivalence, and groupoid structure. -/
structure DeformationFunctor (A : Type u) (B : Type v) where
  obj : A → B
  mapPath : {a b : A} → Path a b → Path (obj a) (obj b)
  map_rweq :
      ∀ {a b : A} {p q : Path a b}, RwEq p q → RwEq (mapPath p) (mapPath q)
  map_trans :
      ∀ {a b c : A} (p : Path a b) (q : Path b c),
        RwEq (mapPath (trans p q)) (trans (mapPath p) (mapPath q))
  map_symm :
      ∀ {a b : A} (p : Path a b),
        RwEq (mapPath (symm p)) (symm (mapPath p))

namespace DeformationFunctor

noncomputable def id (A : Type u) : DeformationFunctor A A where
  obj := fun a => a
  mapPath := fun p => p
  map_rweq := fun h => h
  map_trans := fun _ _ => rweq_refl _
  map_symm := fun _ => rweq_refl _

noncomputable def comp {A : Type u} {B : Type v} {C : Type w}
    (F : DeformationFunctor A B) (G : DeformationFunctor B C) :
    DeformationFunctor A C where
  obj := fun a => G.obj (F.obj a)
  mapPath := fun p => G.mapPath (F.mapPath p)
  map_rweq := fun h => G.map_rweq (F.map_rweq h)
  map_trans := fun p q =>
    rweq_trans
      (G.map_rweq (F.map_trans p q))
      (G.map_trans (F.mapPath p) (F.mapPath q))
  map_symm := fun p =>
    rweq_trans
      (G.map_rweq (F.map_symm p))
      (G.map_symm (F.mapPath p))

noncomputable def mapMaurerCartan {A : Type u} {B : Type v}
    (F : DeformationFunctor A B) {a : A} (mc : MaurerCartanPath a) :
    MaurerCartanPath (F.obj a) where
  omega := F.mapPath mc.omega
  dOmega := F.mapPath mc.dOmega
  bracket := F.mapPath mc.bracket
  equation := by
    exact rweq_trans
      (rweq_symm (F.map_trans mc.dOmega mc.bracket))
      (rweq_trans
        (F.map_rweq mc.equation)
        (F.map_symm mc.omega))

end DeformationFunctor

end DeformationTheory
end CompPaths
