/-
# Topology Law Certificates

Shared certificate records for topology modules that replace bare `True`
placeholders with concrete computational-path evidence.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology

universe u

/-- A compact certificate that a domain law has been anchored to concrete
left/right data and carries computational path evidence for the law witness. -/
structure PathLawCertificate {α : Type u} (lhs rhs : α) where
  witness : Path lhs rhs
  rightUnit : RwEq (Path.trans witness (Path.refl rhs)) witness
  inverseCancel : RwEq (Path.trans witness (Path.symm witness)) (Path.refl lhs)

namespace PathLawCertificate

/-- Build a law certificate from an explicit computational path. -/
noncomputable def ofPath {α : Type u} {lhs rhs : α} (p : Path lhs rhs) :
    PathLawCertificate lhs rhs where
  witness := p
  rightUnit := rweq_cmpA_refl_right p
  inverseCancel := rweq_cmpA_inv_right p

/-- Reflexive law certificate at a concrete anchor. -/
noncomputable def refl {α : Type u} (x : α) : PathLawCertificate x x :=
  ofPath (Path.refl x)

end PathLawCertificate

end Topology
end Path
end ComputationalPaths
