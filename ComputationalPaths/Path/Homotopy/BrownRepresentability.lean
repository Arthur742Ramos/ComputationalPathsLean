/-
# Brown Representability (Path-typed)

This module records Path-typed versions of the Brown representability
equivalence for contravariant functors on the path homotopy category.
We reuse the core representability data and expose Path witnesses for the
inverse laws and naturality.

## Key Results

- `equiv_leftInvPath`: Path-typed left inverse for representability
- `equiv_rightInvPath`: Path-typed right inverse for representability
- `equiv_naturalityPath`: Path-typed naturality
- `brown_representability_path`: Brown representability in Path form

## References

- Brown, "Representability of Cohomology Theories"
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.BrownRepresentability

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace BrownRepresentability

universe u v

/-! ## Path-typed representability -/

/-- Path-typed left inverse for a representability equivalence. -/
def equiv_leftInvPath {A : Type u} {F : PathContraFunctor A}
    (R : ContraRepresentable A F) (b : A) (x : F.obj b) :
    ComputationalPaths.Path
      ((R.equiv b).invFun ((R.equiv b).toFun x)) x :=
  ComputationalPaths.Path.ofEq ((R.equiv b).left_inv x)

/-- Path-typed right inverse for a representability equivalence. -/
def equiv_rightInvPath {A : Type u} {F : PathContraFunctor A}
    (R : ContraRepresentable A F) (b : A)
    (y : FundamentalGroupoid.Hom A b R.obj) :
    ComputationalPaths.Path
      ((R.equiv b).toFun ((R.equiv b).invFun y)) y :=
  ComputationalPaths.Path.ofEq ((R.equiv b).right_inv y)

/-- Path-typed naturality of a representability equivalence. -/
def equiv_naturalityPath {A : Type u} {F : PathContraFunctor A}
    (R : ContraRepresentable A F) {b c : A}
    (p : FundamentalGroupoid.Hom A b c) (x : F.obj c) :
    ComputationalPaths.Path
      ((R.equiv b).toFun (F.map p x))
      (FundamentalGroupoid.comp' A p ((R.equiv c).toFun x)) :=
  ComputationalPaths.Path.ofEq (R.naturality (p := p) (x := x))

/-- Brown representability expressed as a Path-typed inverse law. -/
def brown_representability_path {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W)
    (b : A) (x : F.obj b) :
    ComputationalPaths.Path
      (((brown_representability (W := W) (MV := MV)).equiv b).invFun
        (((brown_representability (W := W) (MV := MV)).equiv b).toFun x)) x := by
  let R := brown_representability (W := W) (MV := MV)
  exact equiv_leftInvPath (R := R) (b := b) (x := x)

/-! ## Summary -/

/-!
We exposed Path-typed inverses and naturality for Brown representability
equivalences and packaged the representability theorem as a Path witness.
-/

end BrownRepresentability
end Homotopy
end Path
end ComputationalPaths
