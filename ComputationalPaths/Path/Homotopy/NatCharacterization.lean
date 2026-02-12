import ComputationalPaths.Path.Basic.Core

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

