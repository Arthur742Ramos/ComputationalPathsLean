/-
# FormalGroupLaws

Formal group laws via computational paths.

This public wrapper re-exports representative formal-group-law traces from
`FormalGroupLawsDeep` into the
`ComputationalPaths.Path.Topology.FormalGroupLaws` namespace.
-/

import ComputationalPaths.Path.Topology.FormalGroupLawsDeep

namespace ComputationalPaths.Path.Topology.FormalGroupLaws

open ComputationalPaths

universe u

/-! ## Representative formal-group-law traces -/

@[inline] noncomputable def fgl_assoc_unit {A : Sort u}
    (F : A → A → A) (zero : A) (a b : A) :=
  ComputationalPaths.fgl_assoc_unit F zero a b

theorem fgl_assoc_unit_length {A : Sort u}
    (F : A → A → A) (zero : A) (a b : A) :
    ComputationalPaths.FGLPath.length (fgl_assoc_unit F zero a b) = 2 := rfl

@[inline] noncomputable def fgl_double_inv_zero {A : Sort u}
    (F : A → A → A) (inv : A → A) (zero : A) (a : A) :=
  ComputationalPaths.fgl_double_inv_zero F inv zero a

theorem fgl_double_inv_zero_length {A : Sort u}
    (F : A → A → A) (inv : A → A) (zero : A) (a : A) :
    ComputationalPaths.FGLPath.length (fgl_double_inv_zero F inv zero a) = 2 := rfl

@[inline] noncomputable def fgl_log_exp {A : Sort u}
    (log exp : A → A) (a : A) :=
  ComputationalPaths.fgl_log_exp log exp a

theorem fgl_log_exp_length {A : Sort u}
    (log exp : A → A) (a : A) :
    ComputationalPaths.FGLPath.length (fgl_log_exp log exp a) = 1 := rfl

@[inline] noncomputable def log_exp_identity_on_fgl {A : Sort u}
    (log exp : A → A) (F op : A → A → A) (a b : A) :=
  ComputationalPaths.log_exp_identity_on_fgl log exp F op a b

theorem log_exp_identity_on_fgl_length {A : Sort u}
    (log exp : A → A) (F op : A → A → A) (a b : A) :
    ComputationalPaths.FGLPath.length (log_exp_identity_on_fgl log exp F op a b) = 1 := rfl

@[inline] noncomputable def lt_full_chain {A : Sort u}
    (def_ u h ht : A → A) (a : A) :=
  ComputationalPaths.lt_full_chain def_ u h ht a

theorem lt_full_chain_length {A : Sort u}
    (def_ u h ht : A → A) (a : A) :
    ComputationalPaths.FGLPath.length (lt_full_chain def_ u h ht a) = 1 := rfl

@[inline] noncomputable def p_typical_log {A : Sort u}
    (pt log : A → A) (F op : A → A → A) (a b : A) :=
  ComputationalPaths.p_typical_log pt log F op a b

theorem p_typical_log_length {A : Sort u}
    (pt log : A → A) (F op : A → A → A) (a b : A) :
    ComputationalPaths.FGLPath.length (p_typical_log pt log F op a b) = 1 := rfl

@[inline] noncomputable def fgl_comm_through_hom {A : Sort u}
    (f : A → A) (F : A → A → A) (a b : A) :=
  ComputationalPaths.fgl_comm_through_hom f F a b

theorem fgl_comm_through_hom_length {A : Sort u}
    (f : A → A) (F : A → A → A) (a b : A) :
    ComputationalPaths.FGLPath.length (fgl_comm_through_hom f F a b) = 1 := rfl

@[inline] noncomputable def fgl_inv_exp {A : Sort u}
    (exp : A → A) (F op : A → A → A) (inv : A → A) (zero : A) (a : A) :=
  ComputationalPaths.fgl_inv_exp exp F op inv zero a

theorem fgl_inv_exp_length {A : Sort u}
    (exp : A → A) (F op : A → A → A) (inv : A → A) (zero : A) (a : A) :
    ComputationalPaths.FGLPath.length (fgl_inv_exp exp F op inv zero a) = 1 := rfl

@[inline] noncomputable def lazard_log {A : Sort u}
    (laz log : A → A) (F op : A → A → A) (a b : A) :=
  ComputationalPaths.lazard_log laz log F op a b

theorem lazard_log_length {A : Sort u}
    (laz log : A → A) (F op : A → A → A) (a b : A) :
    ComputationalPaths.FGLPath.length (lazard_log laz log F op a b) = 1 := rfl

end ComputationalPaths.Path.Topology.FormalGroupLaws
