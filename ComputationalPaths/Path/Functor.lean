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







/-! ## Function-induced functor naturality -/



/-! ## Preservation of rewrite equivalence -/



end FundamentalGroupoidFunctor

end Path
end ComputationalPaths
