/-
# SpectraAlgebra

Spectra algebra via computational paths.

This public module provides a self-contained
computational-path surface for representative spectra-algebra constructions.
It deliberately keeps its step and trace vocabulary local to avoid polluting the
global `ComputationalPaths` namespace.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Topology.SpectraAlgebra

universe u

inductive SpectraStep : {A : Sort u} → A → A → Type u where
  | refl (a : A) : SpectraStep a a
  | symm {a b : A} : SpectraStep a b → SpectraStep b a
  | trans {a b c : A} : SpectraStep a b → SpectraStep b c → SpectraStep a c
  | congrArg {A B : Sort u} (f : A → B) {a b : A} :
      SpectraStep a b → SpectraStep (f a) (f b)
  | smashUnitLeft {A : Sort u} (smash : A → A → A) (sphere : A) (a : A) :
      SpectraStep (smash sphere a) a
  | smashUnitRight {A : Sort u} (smash : A → A → A) (sphere : A) (a : A) :
      SpectraStep (smash a sphere) a
  | ringUnitLeft {A : Sort u} (mult : A → A → A) (unit : A) (a : A) :
      SpectraStep (mult unit a) a
  | ringUnitRight {A : Sort u} (mult : A → A → A) (unit : A) (a : A) :
      SpectraStep (mult a unit) a
  | modAssoc {A : Sort u} (mult act : A → A → A) (r s m : A) :
      SpectraStep (act (mult r s) m) (act r (act s m))
  | suspSigmaOmega {A : Sort u} (sigma omega : A → A) (a : A) :
      SpectraStep (sigma (omega a)) a
  | thomIso {A : Sort u} (thom : A → A) (a : A) :
      SpectraStep (thom a) a
  | swDoubleDual {A : Sort u} (dual : A → A) (a : A) :
      SpectraStep (dual (dual a)) a
  | chromaticSmash {A : Sort u} (loc : A → A) (smash : A → A → A) (a b : A) :
      SpectraStep (loc (smash a b)) (smash (loc a) (loc b))
  | modDistrib {A : Sort u} (act add : A → A → A) (r m n : A) :
      SpectraStep (act r (add m n)) (add (act r m) (act r n))
  | emRing {A : Sort u} (em : A → A) (mult : A → A → A) (a b : A) :
      SpectraStep (em (mult a b)) (mult (em a) (em b))

inductive SpectraTrace : {A : Sort u} → A → A → Type u where
  | nil (a : A) : SpectraTrace a a
  | cons {a b c : A} : SpectraStep a b → SpectraTrace b c → SpectraTrace a c

namespace SpectraTrace

noncomputable def trans {A : Sort u} {a b c : A} :
    SpectraTrace a b → SpectraTrace b c → SpectraTrace a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm {A : Sort u} {a b : A} :
    SpectraTrace a b → SpectraTrace b a
  | .nil _ => .nil _
  | .cons s p => trans (symm p) (.cons (.symm s) (.nil _))

noncomputable def congrArg {A B : Sort u} (f : A → B) {a b : A} :
    SpectraTrace a b → SpectraTrace (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length {A : Sort u} {a b : A} : SpectraTrace a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + length p

end SpectraTrace

/-! ## Primitive traces used by the interface -/

noncomputable def smash_unit_left_path {A : Sort u}
    (smash : A → A → A) (sphere : A) (a : A) :
    SpectraTrace (smash sphere a) a :=
  .cons (.smashUnitLeft smash sphere a) (.nil _)

noncomputable def smash_unit_right_path {A : Sort u}
    (smash : A → A → A) (sphere : A) (a : A) :
    SpectraTrace (smash a sphere) a :=
  .cons (.smashUnitRight smash sphere a) (.nil _)

noncomputable def ring_unit_left_path {A : Sort u}
    (mult : A → A → A) (unit : A) (a : A) :
    SpectraTrace (mult unit a) a :=
  .cons (.ringUnitLeft mult unit a) (.nil _)

noncomputable def ring_unit_right_path {A : Sort u}
    (mult : A → A → A) (unit : A) (a : A) :
    SpectraTrace (mult a unit) a :=
  .cons (.ringUnitRight mult unit a) (.nil _)

noncomputable def mod_assoc_path {A : Sort u}
    (mult act : A → A → A) (r s m : A) :
    SpectraTrace (act (mult r s) m) (act r (act s m)) :=
  .cons (.modAssoc mult act r s m) (.nil _)

noncomputable def susp_sigma_omega_path {A : Sort u}
    (sigma omega : A → A) (a : A) :
    SpectraTrace (sigma (omega a)) a :=
  .cons (.suspSigmaOmega sigma omega a) (.nil _)

noncomputable def thom_iso_path {A : Sort u}
    (thom : A → A) (a : A) :
    SpectraTrace (thom a) a :=
  .cons (.thomIso thom a) (.nil _)

noncomputable def sw_double_dual_path {A : Sort u}
    (dual : A → A) (a : A) :
    SpectraTrace (dual (dual a)) a :=
  .cons (.swDoubleDual dual a) (.nil _)

noncomputable def chromatic_smash_path {A : Sort u}
    (loc : A → A) (smash : A → A → A) (a b : A) :
    SpectraTrace (loc (smash a b)) (smash (loc a) (loc b)) :=
  .cons (.chromaticSmash loc smash a b) (.nil _)

noncomputable def mod_distrib_path {A : Sort u}
    (act add : A → A → A) (r m n : A) :
    SpectraTrace (act r (add m n)) (add (act r m) (act r n)) :=
  .cons (.modDistrib act add r m n) (.nil _)

noncomputable def em_ring_path {A : Sort u}
    (em : A → A) (mult : A → A → A) (a b : A) :
    SpectraTrace (em (mult a b)) (mult (em a) (em b)) :=
  .cons (.emRing em mult a b) (.nil _)

/-! ## Public representative traces -/

noncomputable def smash_unit_interchange {A : Sort u}
    (smash : A → A → A) (sphere : A) (a : A) :
    SpectraTrace (smash sphere a) (smash a sphere) :=
  SpectraTrace.trans
    (smash_unit_left_path smash sphere a)
    (SpectraTrace.symm (smash_unit_right_path smash sphere a))

theorem smash_unit_interchange_length {A : Sort u}
    (smash : A → A → A) (sphere : A) (a : A) :
    SpectraTrace.length (smash_unit_interchange smash sphere a) = 2 := rfl

noncomputable def ring_unit_interchange {A : Sort u}
    (mult : A → A → A) (unit : A) (a : A) :
    SpectraTrace (mult unit a) (mult a unit) :=
  SpectraTrace.trans
    (ring_unit_left_path mult unit a)
    (SpectraTrace.symm (ring_unit_right_path mult unit a))

theorem ring_unit_interchange_length {A : Sort u}
    (mult : A → A → A) (unit : A) (a : A) :
    SpectraTrace.length (ring_unit_interchange mult unit a) = 2 := rfl

noncomputable def mod_double_action {A : Sort u}
    (mult act : A → A → A) (r s t m : A) :
    SpectraTrace (act (mult (mult r s) t) m) (act (mult r s) (act t m)) :=
  .cons (.modAssoc mult act (mult r s) t m) (.nil _)

theorem mod_double_action_length {A : Sort u}
    (mult act : A → A → A) (r s t m : A) :
    SpectraTrace.length (mod_double_action mult act r s t m) = 1 := rfl

noncomputable def susp_double_adj {A : Sort u}
    (sigma omega : A → A) (a : A) :
    SpectraTrace (sigma (omega (sigma (omega a)))) (sigma (omega a)) :=
  SpectraTrace.congrArg sigma (SpectraTrace.congrArg omega (susp_sigma_omega_path sigma omega a))

theorem susp_double_adj_length {A : Sort u}
    (sigma omega : A → A) (a : A) :
    SpectraTrace.length (susp_double_adj sigma omega a) = 1 := rfl

noncomputable def em_thom {A : Sort u}
    (em thom : A → A) (a : A) :
    SpectraTrace (em (thom a)) (em a) :=
  SpectraTrace.congrArg em (thom_iso_path thom a)

theorem em_thom_length {A : Sort u}
    (em thom : A → A) (a : A) :
    SpectraTrace.length (em_thom em thom a) = 1 := rfl

noncomputable def sw_triple_dual {A : Sort u}
    (dual : A → A) (a : A) :
    SpectraTrace (dual (dual (dual a))) (dual a) :=
  SpectraTrace.congrArg dual (sw_double_dual_path dual a)

theorem sw_triple_dual_length {A : Sort u}
    (dual : A → A) (a : A) :
    SpectraTrace.length (sw_triple_dual dual a) = 1 := rfl

noncomputable def spectra_full_chain {A : Sort u}
    (loc : A → A) (smash mult : A → A → A) (a b c : A) :
    SpectraTrace (loc (smash (mult a b) c)) (smash (loc (mult a b)) (loc c)) :=
  chromatic_smash_path loc smash (mult a b) c

theorem spectra_full_chain_length {A : Sort u}
    (loc : A → A) (smash mult : A → A → A) (a b c : A) :
    SpectraTrace.length (spectra_full_chain loc smash mult a b c) = 1 := rfl

noncomputable def mod_distrib_susp {A : Sort u}
    (sigma : A → A) (act add : A → A → A) (r m n : A) :
    SpectraTrace (sigma (act r (add m n))) (sigma (add (act r m) (act r n))) :=
  SpectraTrace.congrArg sigma (mod_distrib_path act add r m n)

theorem mod_distrib_susp_length {A : Sort u}
    (sigma : A → A) (act add : A → A → A) (r m n : A) :
    SpectraTrace.length (mod_distrib_susp sigma act add r m n) = 1 := rfl

noncomputable def chromatic_em_ring {A : Sort u}
    (loc em : A → A) (mult : A → A → A) (a b : A) :
    SpectraTrace (loc (em (mult a b))) (loc (mult (em a) (em b))) :=
  SpectraTrace.congrArg loc (em_ring_path em mult a b)

theorem chromatic_em_ring_length {A : Sort u}
    (loc em : A → A) (mult : A → A → A) (a b : A) :
    SpectraTrace.length (chromatic_em_ring loc em mult a b) = 1 := rfl

end ComputationalPaths.Path.Topology.SpectraAlgebra
