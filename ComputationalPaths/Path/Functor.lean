/- 
# Functor laws for the fundamental groupoid

This module records additional functoriality laws for
`FundamentalGroupoidFunctor`, including naturality orientations,
associativity/identity laws for composition, and preservation of
path rewrite equivalence.
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor

namespace ComputationalPaths
namespace Path

universe u

namespace FundamentalGroupoidFunctor

variable {A B C D : Type u}

/-! ## Naturality orientations -/

@[simp] theorem map_comp_naturality
    (F : FundamentalGroupoidFunctor A B)
    {a b c : A}
    (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c) :
    FundamentalGroupoid.comp' B (F.map p) (F.map q) =
      F.map (FundamentalGroupoid.comp' A p q) := by
  simpa using (F.map_comp p q).symm

@[simp] theorem map_comp_naturality'
    (F : FundamentalGroupoidFunctor A B)
    {a b c : A}
    (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c) :
    F.map (FundamentalGroupoid.comp' A p q) =
      FundamentalGroupoid.comp' B (F.map p) (F.map q) :=
  F.map_comp p q

/-! ## Composition associativity -/

@[simp] theorem comp_assoc_obj
    (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B C)
    (H : FundamentalGroupoidFunctor C D)
    (a : A) :
    (comp (comp F G) H).obj a = (comp F (comp G H)).obj a := rfl

@[simp] theorem comp_assoc_map
    (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B C)
    (H : FundamentalGroupoidFunctor C D)
    {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    (comp (comp F G) H).map p = (comp F (comp G H)).map p := rfl

theorem comp_assoc_functor
    (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B C)
    (H : FundamentalGroupoidFunctor C D) :
    comp (comp F G) H = comp F (comp G H) := by
  cases F
  cases G
  cases H
  rfl

/-! ## Identity functor laws -/

@[simp] theorem id_comp_obj
    (F : FundamentalGroupoidFunctor A B)
    (a : A) :
    (comp (id A) F).obj a = F.obj a := rfl

@[simp] theorem id_comp_map
    (F : FundamentalGroupoidFunctor A B)
    {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    (comp (id A) F).map p = F.map p := rfl

@[simp] theorem comp_id_obj
    (F : FundamentalGroupoidFunctor A B)
    (a : A) :
    (comp F (id B)).obj a = F.obj a := rfl

@[simp] theorem comp_id_map
    (F : FundamentalGroupoidFunctor A B)
    {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    (comp F (id B)).map p = F.map p := rfl

theorem id_comp_functor
    (F : FundamentalGroupoidFunctor A B) :
    comp (id A) F = F := by
  cases F
  rfl

theorem comp_id_functor
    (F : FundamentalGroupoidFunctor A B) :
    comp F (id B) = F := by
  cases F
  rfl

/-! ## Function-induced functor naturality -/

@[simp] theorem fundamentalGroupoidFunctor_comp_obj
    (f : A → B) (g : B → C) (a : A) :
    (comp (fundamentalGroupoidFunctor f) (fundamentalGroupoidFunctor g)).obj a =
      (fundamentalGroupoidFunctor (Function.comp g f)).obj a := rfl

@[simp] theorem fundamentalGroupoidFunctor_comp_map
    (f : A → B) (g : B → C)
    {a a' : A}
    (p : FundamentalGroupoid.Hom A a a') :
    (comp (fundamentalGroupoidFunctor f) (fundamentalGroupoidFunctor g)).map p =
      (fundamentalGroupoidFunctor (Function.comp g f)).map p := by
  simpa [comp, fundamentalGroupoidFunctor] using
    (fundamentalGroupoidMap_compFun (f := f) (g := g) (p := p))

/-! ## Preservation of rewrite equivalence -/

theorem fundamentalGroupoidMap_preserves_rweq
    (f : A → B)
    {a b : A}
    {p q : Path a b}
    (h : RwEq p q) :
    fundamentalGroupoidMap f (Quot.mk _ p) =
      fundamentalGroupoidMap f (Quot.mk _ q) := by
  exact congrArg (fun x => fundamentalGroupoidMap f x) (Quot.sound h)

theorem fundamentalGroupoidFunctor_preserves_rweq
    (f : A → B)
    {a b : A}
    {p q : Path a b}
    (h : RwEq p q) :
    (fundamentalGroupoidFunctor f).map (Quot.mk _ p) =
      (fundamentalGroupoidFunctor f).map (Quot.mk _ q) :=
  fundamentalGroupoidMap_preserves_rweq (f := f) (h := h)

end FundamentalGroupoidFunctor

end Path
end ComputationalPaths
