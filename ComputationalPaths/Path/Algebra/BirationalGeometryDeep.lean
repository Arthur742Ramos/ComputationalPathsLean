/-
# Birational Geometry via Computational Paths

This module provides a large computational-path skeleton for birational geometry:
divisors, linear systems, blow-ups, Mori and nef/ample cones, minimal model
program states, flips, vanishing packages, canonical/terminal singularities,
Sarkisov links, and Cremona elements.

All coherence witnesses are explicit `Path` terms.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.BirationalGeometryDeep

open ComputationalPaths.Path

universe u

/-! ## Core birational data -/

structure BirationalSpace where
  code : Nat
deriving DecidableEq, Repr

structure Divisor (X : BirationalSpace) where
  coeff : Int
deriving DecidableEq, Repr

structure LinearSystem (X : BirationalSpace) where
  fixedPart : Divisor X
  mobilePart : Divisor X
deriving DecidableEq, Repr

abbrev Gam (X : BirationalSpace) := Divisor X
abbrev Sym (X : BirationalSpace) := LinearSystem X

structure BlowUp (X : BirationalSpace) where
  centerCode : Nat
  exceptional : Divisor X
deriving DecidableEq, Repr

structure MoriCone (X : BirationalSpace) where
  rays : List (Divisor X)
deriving DecidableEq, Repr

structure NefCone (X : BirationalSpace) where
  generators : List (Divisor X)
deriving DecidableEq, Repr

structure AmpleCone (X : BirationalSpace) where
  generators : List (Divisor X)
deriving DecidableEq, Repr

inductive MmpTag
  | divisorial
  | flip
  | fibration
deriving DecidableEq, Repr

structure MmpState (X : BirationalSpace) where
  currentDivisor : Divisor X
  stageTag : MmpTag
  level : Nat
deriving DecidableEq, Repr

structure FlipDatum (X : BirationalSpace) where
  source : MmpState X
  target : MmpState X
deriving DecidableEq, Repr

structure VanishingPackage (X : BirationalSpace) where
  kDivisor : Divisor X
  nefBigDivisor : Divisor X
deriving DecidableEq, Repr

inductive SingularityType
  | smooth
  | canonical
  | terminal
deriving DecidableEq, Repr

structure SingularModel (X : BirationalSpace) where
  kind : SingularityType
  discrepancy : Int
deriving DecidableEq, Repr

inductive SarkisovKind
  | kindI
  | kindII
  | kindIII
  | kindIV
deriving DecidableEq, Repr

structure SarkisovLink (X : BirationalSpace) where
  startState : MmpState X
  endState : MmpState X
  linkKind : SarkisovKind
deriving DecidableEq, Repr

structure CremonaElement where
  degree : Nat
  inverseDegree : Nat
deriving DecidableEq, Repr

@[simp] noncomputable def twoStep {A : Type u} (a : A) : Path a a :=
  Path.trans (Path.refl a) (Path.refl a)

@[simp] noncomputable def threeStep {A : Type u} (a : A) : Path a a :=
  Path.trans (twoStep a) (Path.refl a)

/-! ## Divisors -/

section Divisors

variable {X : BirationalSpace}

@[simp] noncomputable def principalPart (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def nefShadow (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def ampleShadow (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def canonicalShadow (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def terminalShadow (Gam1 : Gam X) : Gam X := Gam1

noncomputable def divisor_refl (Gam1 : Gam X) : Path Gam1 Gam1 :=
  Path.refl Gam1

noncomputable def divisor_two_step (Gam1 : Gam X) : Path Gam1 Gam1 :=
  twoStep Gam1

noncomputable def divisor_three_step (Gam1 : Gam X) : Path Gam1 Gam1 :=
  threeStep Gam1

noncomputable def divisor_symm_refl (Gam1 : Gam X) :
    Path (Path.symm (Path.refl Gam1)) (Path.refl Gam1) := by
  simpa using (Path.refl (Path.refl Gam1))

noncomputable def divisor_coeff_congr {Gam1 Gam2 : Gam X} (p : Path Gam1 Gam2) :
    Path Gam1.coeff Gam2.coeff :=
  Path.congrArg (fun G : Gam X => G.coeff) p

noncomputable def divisor_principal_stable (Gam1 : Gam X) :
    Path (principalPart Gam1) Gam1 := by
  simpa [principalPart] using (Path.refl Gam1)

noncomputable def divisor_nef_shadow_stable (Gam1 : Gam X) :
    Path (nefShadow Gam1) Gam1 := by
  simpa [nefShadow] using (Path.refl Gam1)

noncomputable def divisor_ample_shadow_stable (Gam1 : Gam X) :
    Path (ampleShadow Gam1) Gam1 := by
  simpa [ampleShadow] using (Path.refl Gam1)

noncomputable def divisor_canonical_shadow_stable (Gam1 : Gam X) :
    Path (canonicalShadow Gam1) Gam1 := by
  simpa [canonicalShadow] using (Path.refl Gam1)

noncomputable def divisor_terminal_shadow_stable (Gam1 : Gam X) :
    Path (terminalShadow Gam1) Gam1 := by
  simpa [terminalShadow] using (Path.refl Gam1)

end Divisors

/-! ## Linear systems -/

section LinearSystems

variable {X : BirationalSpace}

@[simp] noncomputable def symClosure (Sym1 : Sym X) : Sym X := Sym1
@[simp] noncomputable def symResolution (Sym1 : Sym X) : Sym X := Sym1
@[simp] noncomputable def symSwap (Sym1 : Sym X) : Sym X :=
  { fixedPart := Sym1.mobilePart, mobilePart := Sym1.fixedPart }

noncomputable def linear_refl (Sym1 : Sym X) : Path Sym1 Sym1 :=
  Path.refl Sym1

noncomputable def linear_two_step (Sym1 : Sym X) : Path Sym1 Sym1 :=
  twoStep Sym1

noncomputable def linear_three_step (Sym1 : Sym X) : Path Sym1 Sym1 :=
  threeStep Sym1

noncomputable def linear_swap_involution (Sym1 : Sym X) :
    Path (symSwap (symSwap Sym1)) Sym1 := by
  simpa [symSwap] using (Path.refl Sym1)

noncomputable def linear_fixed_congr {Sym1 Sym2 : Sym X} (p : Path Sym1 Sym2) :
    Path Sym1.fixedPart Sym2.fixedPart :=
  Path.congrArg (fun S : Sym X => S.fixedPart) p

noncomputable def linear_mobile_congr {Sym1 Sym2 : Sym X} (p : Path Sym1 Sym2) :
    Path Sym1.mobilePart Sym2.mobilePart :=
  Path.congrArg (fun S : Sym X => S.mobilePart) p

noncomputable def linear_closure_stable (Sym1 : Sym X) :
    Path (symClosure Sym1) Sym1 := by
  simpa [symClosure] using (Path.refl Sym1)

noncomputable def linear_resolution_stable (Sym1 : Sym X) :
    Path (symResolution Sym1) Sym1 := by
  simpa [symResolution] using (Path.refl Sym1)

end LinearSystems

/-! ## Blow-ups -/

section BlowUps

variable {X : BirationalSpace}

@[simp] noncomputable def blowUpTransform (_B : BlowUp X) (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def blowUpInverseTransform (_B : BlowUp X) (Gam1 : Gam X) : Gam X := Gam1
@[simp] noncomputable def blowUpFactorization (B : BlowUp X) : BlowUp X := B

noncomputable def blowup_refl (B : BlowUp X) : Path B B :=
  Path.refl B

noncomputable def blowup_two_step (B : BlowUp X) : Path B B :=
  twoStep B

noncomputable def blowup_three_step (B : BlowUp X) : Path B B :=
  threeStep B

noncomputable def blowup_exceptional_congr {B1 B2 : BlowUp X} (p : Path B1 B2) :
    Path B1.exceptional B2.exceptional :=
  Path.congrArg (fun B : BlowUp X => B.exceptional) p

noncomputable def blowup_center_congr {B1 B2 : BlowUp X} (p : Path B1 B2) :
    Path B1.centerCode B2.centerCode :=
  Path.congrArg (fun B : BlowUp X => B.centerCode) p

noncomputable def blowup_transform_stable (B : BlowUp X) (Gam1 : Gam X) :
    Path (blowUpTransform B Gam1) Gam1 := by
  simpa [blowUpTransform] using (Path.refl Gam1)

noncomputable def blowup_inverse_transform_stable (B : BlowUp X) (Gam1 : Gam X) :
    Path (blowUpInverseTransform B Gam1) Gam1 := by
  simpa [blowUpInverseTransform] using (Path.refl Gam1)

noncomputable def blowup_factorization_stable (B : BlowUp X) :
    Path (blowUpFactorization B) B := by
  simpa [blowUpFactorization] using (Path.refl B)

end BlowUps

/-! ## Mori cone, nef cone, ample cone -/

section Cones

variable {X : BirationalSpace}

@[simp] noncomputable def moriClosure (C : MoriCone X) : MoriCone X := C
@[simp] noncomputable def nefClosure (N : NefCone X) : NefCone X := N
@[simp] noncomputable def ampleClosure (A : AmpleCone X) : AmpleCone X := A
@[simp] noncomputable def nefToMori (N : NefCone X) : MoriCone X := { rays := N.generators }
@[simp] noncomputable def ampleToNef (A : AmpleCone X) : NefCone X := { generators := A.generators }

noncomputable def mori_refl (C : MoriCone X) : Path C C :=
  Path.refl C

noncomputable def mori_two_step (C : MoriCone X) : Path C C :=
  twoStep C

noncomputable def mori_three_step (C : MoriCone X) : Path C C :=
  threeStep C

noncomputable def mori_rays_congr {C1 C2 : MoriCone X} (p : Path C1 C2) :
    Path C1.rays C2.rays :=
  Path.congrArg (fun C : MoriCone X => C.rays) p

noncomputable def nef_refl (N : NefCone X) : Path N N :=
  Path.refl N

noncomputable def nef_generators_congr {N1 N2 : NefCone X} (p : Path N1 N2) :
    Path N1.generators N2.generators :=
  Path.congrArg (fun N : NefCone X => N.generators) p

noncomputable def ample_refl (A : AmpleCone X) : Path A A :=
  Path.refl A

noncomputable def ample_generators_congr {A1 A2 : AmpleCone X} (p : Path A1 A2) :
    Path A1.generators A2.generators :=
  Path.congrArg (fun A : AmpleCone X => A.generators) p

noncomputable def nef_to_mori_stable (N : NefCone X) :
    Path (nefToMori (nefClosure N)) (nefToMori N) := by
  simpa [nefClosure, nefToMori] using (Path.refl (nefToMori N))

noncomputable def ample_to_nef_stable (A : AmpleCone X) :
    Path (ampleToNef (ampleClosure A)) (ampleToNef A) := by
  simpa [ampleClosure, ampleToNef] using (Path.refl (ampleToNef A))

end Cones

/-! ## Minimal model program and flips -/

section MinimalModelProgram

variable {X : BirationalSpace}

@[simp] noncomputable def mmpNormalize (S : MmpState X) : MmpState X := S
@[simp] noncomputable def mmpAdvance (S : MmpState X) : MmpState X := S
@[simp] noncomputable def flipNormalize (F : FlipDatum X) : FlipDatum X := F

noncomputable def mmp_state_refl (S : MmpState X) : Path S S :=
  Path.refl S

noncomputable def mmp_state_two_step (S : MmpState X) : Path S S :=
  twoStep S

noncomputable def mmp_state_three_step (S : MmpState X) : Path S S :=
  threeStep S

noncomputable def mmp_current_divisor_congr {S1 S2 : MmpState X} (p : Path S1 S2) :
    Path S1.currentDivisor S2.currentDivisor :=
  Path.congrArg (fun S : MmpState X => S.currentDivisor) p

noncomputable def flip_refl (F : FlipDatum X) : Path F F :=
  Path.refl F

noncomputable def flip_two_step (F : FlipDatum X) : Path F F :=
  twoStep F

noncomputable def flip_source_congr {F1 F2 : FlipDatum X} (p : Path F1 F2) :
    Path F1.source F2.source :=
  Path.congrArg (fun F : FlipDatum X => F.source) p

noncomputable def flip_target_congr {F1 F2 : FlipDatum X} (p : Path F1 F2) :
    Path F1.target F2.target :=
  Path.congrArg (fun F : FlipDatum X => F.target) p

end MinimalModelProgram

/-! ## Kawamata-Viehweg vanishing package -/

section Vanishing

variable {X : BirationalSpace}

@[simp] noncomputable def applyKawamataViehweg (V : VanishingPackage X) : VanishingPackage X := V
@[simp] noncomputable def pushforwardVanishing (V : VanishingPackage X) : VanishingPackage X := V

noncomputable def kv_package_refl (V : VanishingPackage X) : Path V V :=
  Path.refl V

noncomputable def kv_package_two_step (V : VanishingPackage X) : Path V V :=
  twoStep V

noncomputable def kv_k_divisor_congr {V1 V2 : VanishingPackage X} (p : Path V1 V2) :
    Path V1.kDivisor V2.kDivisor :=
  Path.congrArg (fun V : VanishingPackage X => V.kDivisor) p

noncomputable def kv_nef_big_divisor_congr {V1 V2 : VanishingPackage X} (p : Path V1 V2) :
    Path V1.nefBigDivisor V2.nefBigDivisor :=
  Path.congrArg (fun V : VanishingPackage X => V.nefBigDivisor) p

noncomputable def kv_apply_stable (V : VanishingPackage X) :
    Path (applyKawamataViehweg V) V := by
  simpa [applyKawamataViehweg] using (Path.refl V)

noncomputable def kv_pushforward_stable (V : VanishingPackage X) :
    Path (pushforwardVanishing V) V := by
  simpa [pushforwardVanishing] using (Path.refl V)

end Vanishing

/-! ## Canonical and terminal singularities -/

section Singularities

variable {X : BirationalSpace}

@[simp] noncomputable def canonicalToTerminal (S : SingularModel X) : SingularModel X := S
@[simp] noncomputable def terminalClosure (S : SingularModel X) : SingularModel X := S

noncomputable def singular_refl (S : SingularModel X) : Path S S :=
  Path.refl S

noncomputable def singular_two_step (S : SingularModel X) : Path S S :=
  twoStep S

noncomputable def singular_kind_congr {S1 S2 : SingularModel X} (p : Path S1 S2) :
    Path S1.kind S2.kind :=
  Path.congrArg (fun S : SingularModel X => S.kind) p

noncomputable def singular_discrepancy_congr {S1 S2 : SingularModel X} (p : Path S1 S2) :
    Path S1.discrepancy S2.discrepancy :=
  Path.congrArg (fun S : SingularModel X => S.discrepancy) p

noncomputable def canonical_to_terminal_stable (S : SingularModel X) :
    Path (canonicalToTerminal S) S := by
  simpa [canonicalToTerminal] using (Path.refl S)

noncomputable def terminal_closure_stable (S : SingularModel X) :
    Path (terminalClosure S) S := by
  simpa [terminalClosure] using (Path.refl S)

end Singularities

/-! ## Sarkisov program -/

section Sarkisov

variable {X : BirationalSpace}

@[simp] noncomputable def sarkisovNormalize (L : SarkisovLink X) : SarkisovLink X := L
@[simp] noncomputable def sarkisovRoundtrip (L : SarkisovLink X) : SarkisovLink X := L

noncomputable def sarkisov_refl (L : SarkisovLink X) : Path L L :=
  Path.refl L

noncomputable def sarkisov_two_step (L : SarkisovLink X) : Path L L :=
  twoStep L

noncomputable def sarkisov_start_congr {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    Path L1.startState L2.startState :=
  Path.congrArg (fun L : SarkisovLink X => L.startState) p

noncomputable def sarkisov_end_congr {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    Path L1.endState L2.endState :=
  Path.congrArg (fun L : SarkisovLink X => L.endState) p

noncomputable def sarkisov_kind_congr {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    Path L1.linkKind L2.linkKind :=
  Path.congrArg (fun L : SarkisovLink X => L.linkKind) p

noncomputable def sarkisov_roundtrip_stable (L : SarkisovLink X) :
    Path (sarkisovRoundtrip (sarkisovNormalize L)) L := by
  simpa [sarkisovNormalize, sarkisovRoundtrip] using (Path.refl L)

end Sarkisov

/-! ## Cremona group -/

section Cremona

@[simp] noncomputable def cremonaCompose (f g : CremonaElement) : CremonaElement :=
  { degree := f.degree + g.degree
    inverseDegree := f.inverseDegree + g.inverseDegree }

@[simp] noncomputable def cremonaInverse (f : CremonaElement) : CremonaElement :=
  { degree := f.inverseDegree, inverseDegree := f.degree }

@[simp] noncomputable def cremonaNormalize (f : CremonaElement) : CremonaElement := f
@[simp] noncomputable def cremonaSarkisovBridge (f : CremonaElement) : CremonaElement := f

noncomputable def cremona_refl (f : CremonaElement) : Path f f :=
  Path.refl f

noncomputable def cremona_two_step (f : CremonaElement) : Path f f :=
  twoStep f

noncomputable def cremona_three_step (f : CremonaElement) : Path f f :=
  threeStep f

noncomputable def cremona_degree_congr {f g : CremonaElement} (p : Path f g) :
    Path f.degree g.degree :=
  Path.congrArg (fun h : CremonaElement => h.degree) p

noncomputable def cremona_inverse_degree_congr {f g : CremonaElement} (p : Path f g) :
    Path f.inverseDegree g.inverseDegree :=
  Path.congrArg (fun h : CremonaElement => h.inverseDegree) p

noncomputable def cremona_compose_refl (f g : CremonaElement) :
    Path (cremonaCompose f g) (cremonaCompose f g) :=
  Path.refl (cremonaCompose f g)

noncomputable def cremona_inverse_refl (f : CremonaElement) :
    Path (cremonaInverse (cremonaInverse f)) (cremonaNormalize f) := by
  simpa [cremonaInverse, cremonaNormalize] using (Path.refl f)

noncomputable def cremona_sarkisov_bridge_stable (f : CremonaElement) :
    Path (cremonaSarkisovBridge (cremonaNormalize f)) f := by
  simpa [cremonaNormalize, cremonaSarkisovBridge] using (Path.refl f)

end Cremona

/-! ## Proposition layer: 70 theorems extracted from path witnesses -/

section DivisorTheorems

variable {X : BirationalSpace}

theorem divisor_refl_thm (Gam1 : Gam X) : Gam1 = Gam1 :=
  (divisor_refl Gam1).proof

theorem divisor_two_step_thm (Gam1 : Gam X) : Gam1 = Gam1 :=
  (divisor_two_step Gam1).proof

theorem divisor_three_step_thm (Gam1 : Gam X) : Gam1 = Gam1 :=
  (divisor_three_step Gam1).proof

theorem divisor_symm_refl_thm (Gam1 : Gam X) :
    Path.symm (Path.refl Gam1) = Path.refl Gam1 :=
  (divisor_symm_refl Gam1).proof

theorem divisor_coeff_congr_thm {Gam1 Gam2 : Gam X} (p : Path Gam1 Gam2) :
    Gam1.coeff = Gam2.coeff :=
  (divisor_coeff_congr p).proof

theorem divisor_principal_stable_thm (Gam1 : Gam X) :
    principalPart Gam1 = Gam1 :=
  (divisor_principal_stable Gam1).proof

theorem divisor_nef_shadow_stable_thm (Gam1 : Gam X) :
    nefShadow Gam1 = Gam1 :=
  (divisor_nef_shadow_stable Gam1).proof

theorem divisor_ample_shadow_stable_thm (Gam1 : Gam X) :
    ampleShadow Gam1 = Gam1 :=
  (divisor_ample_shadow_stable Gam1).proof

theorem divisor_canonical_shadow_stable_thm (Gam1 : Gam X) :
    canonicalShadow Gam1 = Gam1 :=
  (divisor_canonical_shadow_stable Gam1).proof

theorem divisor_terminal_shadow_stable_thm (Gam1 : Gam X) :
    terminalShadow Gam1 = Gam1 :=
  (divisor_terminal_shadow_stable Gam1).proof

end DivisorTheorems

section LinearSystemTheorems

variable {X : BirationalSpace}

theorem linear_refl_thm (Sym1 : Sym X) : Sym1 = Sym1 :=
  (linear_refl Sym1).proof

theorem linear_two_step_thm (Sym1 : Sym X) : Sym1 = Sym1 :=
  (linear_two_step Sym1).proof

theorem linear_three_step_thm (Sym1 : Sym X) : Sym1 = Sym1 :=
  (linear_three_step Sym1).proof

theorem linear_swap_involution_thm (Sym1 : Sym X) :
    symSwap (symSwap Sym1) = Sym1 :=
  (linear_swap_involution Sym1).proof

theorem linear_fixed_congr_thm {Sym1 Sym2 : Sym X} (p : Path Sym1 Sym2) :
    Sym1.fixedPart = Sym2.fixedPart :=
  (linear_fixed_congr p).proof

theorem linear_mobile_congr_thm {Sym1 Sym2 : Sym X} (p : Path Sym1 Sym2) :
    Sym1.mobilePart = Sym2.mobilePart :=
  (linear_mobile_congr p).proof

theorem linear_closure_stable_thm (Sym1 : Sym X) :
    symClosure Sym1 = Sym1 :=
  (linear_closure_stable Sym1).proof

theorem linear_resolution_stable_thm (Sym1 : Sym X) :
    symResolution Sym1 = Sym1 :=
  (linear_resolution_stable Sym1).proof

end LinearSystemTheorems

section BlowUpTheorems

variable {X : BirationalSpace}

theorem blowup_refl_thm (B : BlowUp X) : B = B :=
  (blowup_refl B).proof

theorem blowup_two_step_thm (B : BlowUp X) : B = B :=
  (blowup_two_step B).proof

theorem blowup_three_step_thm (B : BlowUp X) : B = B :=
  (blowup_three_step B).proof

theorem blowup_exceptional_congr_thm {B1 B2 : BlowUp X} (p : Path B1 B2) :
    B1.exceptional = B2.exceptional :=
  (blowup_exceptional_congr p).proof

theorem blowup_center_congr_thm {B1 B2 : BlowUp X} (p : Path B1 B2) :
    B1.centerCode = B2.centerCode :=
  (blowup_center_congr p).proof

theorem blowup_transform_stable_thm (B : BlowUp X) (Gam1 : Gam X) :
    blowUpTransform B Gam1 = Gam1 :=
  (blowup_transform_stable B Gam1).proof

theorem blowup_inverse_transform_stable_thm (B : BlowUp X) (Gam1 : Gam X) :
    blowUpInverseTransform B Gam1 = Gam1 :=
  (blowup_inverse_transform_stable B Gam1).proof

theorem blowup_factorization_stable_thm (B : BlowUp X) :
    blowUpFactorization B = B :=
  (blowup_factorization_stable B).proof

end BlowUpTheorems

section ConeTheorems

variable {X : BirationalSpace}

theorem mori_refl_thm (C : MoriCone X) : C = C :=
  (mori_refl C).proof

theorem mori_two_step_thm (C : MoriCone X) : C = C :=
  (mori_two_step C).proof

theorem mori_three_step_thm (C : MoriCone X) : C = C :=
  (mori_three_step C).proof

theorem mori_rays_congr_thm {C1 C2 : MoriCone X} (p : Path C1 C2) :
    C1.rays = C2.rays :=
  (mori_rays_congr p).proof

theorem nef_refl_thm (N : NefCone X) : N = N :=
  (nef_refl N).proof

theorem nef_generators_congr_thm {N1 N2 : NefCone X} (p : Path N1 N2) :
    N1.generators = N2.generators :=
  (nef_generators_congr p).proof

theorem ample_refl_thm (A : AmpleCone X) : A = A :=
  (ample_refl A).proof

theorem ample_generators_congr_thm {A1 A2 : AmpleCone X} (p : Path A1 A2) :
    A1.generators = A2.generators :=
  (ample_generators_congr p).proof

theorem nef_to_mori_stable_thm (N : NefCone X) :
    nefToMori (nefClosure N) = nefToMori N :=
  (nef_to_mori_stable N).proof

theorem ample_to_nef_stable_thm (A : AmpleCone X) :
    ampleToNef (ampleClosure A) = ampleToNef A :=
  (ample_to_nef_stable A).proof

end ConeTheorems

section MmpTheorems

variable {X : BirationalSpace}

theorem mmp_state_refl_thm (S : MmpState X) : S = S :=
  (mmp_state_refl S).proof

theorem mmp_state_two_step_thm (S : MmpState X) : S = S :=
  (mmp_state_two_step S).proof

theorem mmp_state_three_step_thm (S : MmpState X) : S = S :=
  (mmp_state_three_step S).proof

theorem mmp_current_divisor_congr_thm {S1 S2 : MmpState X} (p : Path S1 S2) :
    S1.currentDivisor = S2.currentDivisor :=
  (mmp_current_divisor_congr p).proof

theorem flip_refl_thm (F : FlipDatum X) : F = F :=
  (flip_refl F).proof

theorem flip_two_step_thm (F : FlipDatum X) : F = F :=
  (flip_two_step F).proof

theorem flip_source_congr_thm {F1 F2 : FlipDatum X} (p : Path F1 F2) :
    F1.source = F2.source :=
  (flip_source_congr p).proof

theorem flip_target_congr_thm {F1 F2 : FlipDatum X} (p : Path F1 F2) :
    F1.target = F2.target :=
  (flip_target_congr p).proof

end MmpTheorems

section VanishingTheorems

variable {X : BirationalSpace}

theorem kv_package_refl_thm (V : VanishingPackage X) : V = V :=
  (kv_package_refl V).proof

theorem kv_package_two_step_thm (V : VanishingPackage X) : V = V :=
  (kv_package_two_step V).proof

theorem kv_k_divisor_congr_thm {V1 V2 : VanishingPackage X} (p : Path V1 V2) :
    V1.kDivisor = V2.kDivisor :=
  (kv_k_divisor_congr p).proof

theorem kv_nef_big_divisor_congr_thm {V1 V2 : VanishingPackage X} (p : Path V1 V2) :
    V1.nefBigDivisor = V2.nefBigDivisor :=
  (kv_nef_big_divisor_congr p).proof

theorem kv_apply_stable_thm (V : VanishingPackage X) :
    applyKawamataViehweg V = V :=
  (kv_apply_stable V).proof

theorem kv_pushforward_stable_thm (V : VanishingPackage X) :
    pushforwardVanishing V = V :=
  (kv_pushforward_stable V).proof

end VanishingTheorems

section SingularityTheorems

variable {X : BirationalSpace}

theorem singular_refl_thm (S : SingularModel X) : S = S :=
  (singular_refl S).proof

theorem singular_two_step_thm (S : SingularModel X) : S = S :=
  (singular_two_step S).proof

theorem singular_kind_congr_thm {S1 S2 : SingularModel X} (p : Path S1 S2) :
    S1.kind = S2.kind :=
  (singular_kind_congr p).proof

theorem singular_discrepancy_congr_thm {S1 S2 : SingularModel X} (p : Path S1 S2) :
    S1.discrepancy = S2.discrepancy :=
  (singular_discrepancy_congr p).proof

theorem canonical_to_terminal_stable_thm (S : SingularModel X) :
    canonicalToTerminal S = S :=
  (canonical_to_terminal_stable S).proof

theorem terminal_closure_stable_thm (S : SingularModel X) :
    terminalClosure S = S :=
  (terminal_closure_stable S).proof

end SingularityTheorems

section SarkisovTheorems

variable {X : BirationalSpace}

theorem sarkisov_refl_thm (L : SarkisovLink X) : L = L :=
  (sarkisov_refl L).proof

theorem sarkisov_two_step_thm (L : SarkisovLink X) : L = L :=
  (sarkisov_two_step L).proof

theorem sarkisov_start_congr_thm {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    L1.startState = L2.startState :=
  (sarkisov_start_congr p).proof

theorem sarkisov_end_congr_thm {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    L1.endState = L2.endState :=
  (sarkisov_end_congr p).proof

theorem sarkisov_kind_congr_thm {L1 L2 : SarkisovLink X} (p : Path L1 L2) :
    L1.linkKind = L2.linkKind :=
  (sarkisov_kind_congr p).proof

theorem sarkisov_roundtrip_stable_thm (L : SarkisovLink X) :
    sarkisovRoundtrip (sarkisovNormalize L) = L :=
  (sarkisov_roundtrip_stable L).proof

end SarkisovTheorems

section CremonaTheorems

theorem cremona_refl_thm (f : CremonaElement) : f = f :=
  (cremona_refl f).proof

theorem cremona_two_step_thm (f : CremonaElement) : f = f :=
  (cremona_two_step f).proof

theorem cremona_three_step_thm (f : CremonaElement) : f = f :=
  (cremona_three_step f).proof

theorem cremona_degree_congr_thm {f g : CremonaElement} (p : Path f g) :
    f.degree = g.degree :=
  (cremona_degree_congr p).proof

theorem cremona_inverse_degree_congr_thm {f g : CremonaElement} (p : Path f g) :
    f.inverseDegree = g.inverseDegree :=
  (cremona_inverse_degree_congr p).proof

theorem cremona_compose_refl_thm (f g : CremonaElement) :
    cremonaCompose f g = cremonaCompose f g :=
  (cremona_compose_refl f g).proof

theorem cremona_inverse_refl_thm (f : CremonaElement) :
    cremonaInverse (cremonaInverse f) = cremonaNormalize f :=
  (cremona_inverse_refl f).proof

theorem cremona_sarkisov_bridge_stable_thm (f : CremonaElement) :
    cremonaSarkisovBridge (cremonaNormalize f) = f :=
  (cremona_sarkisov_bridge_stable f).proof

end CremonaTheorems

end ComputationalPaths.Path.Algebra.BirationalGeometryDeep
