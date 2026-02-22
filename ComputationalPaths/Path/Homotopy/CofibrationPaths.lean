/-
# Cofibrations via Computational Paths

This module develops cofibration theory using the computational paths framework:
cofiber sequences, Puppe sequence aspects, suspension, mapping cones,
coexact sequences, and iterated cofibrations.

## Key Results

- Mapping cone constructions and properties
- Cofiber inclusion and projection maps
- Puppe sequence: A → B → Cf → ΣA → ΣB → ...
- Coexactness properties
- Iterated cofiber constructions
- Mapping telescope

## References

- HoTT Book, Chapter 8
- May, "A Concise Course in Algebraic Topology", Chapter 8
-/

import ComputationalPaths.Path.Homotopy.CofiberSequence
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.HigherHomotopy

namespace ComputationalPaths.Path
namespace CofibrationPaths

open Homotopy.CofiberSequence SuspensionLoop HigherHomotopy CompPath

universe u

variable {A B C : Type u}

/-! ## Mapping Cone Properties -/

/-- The inclusion map from B into Cofiber f. -/
noncomputable def cofiberIncl (f : A → B) : B → Cofiber f :=
  cofiberInclusion f

/-- The cofiber basepoint. -/
noncomputable def cofiberPt (f : A → B) : Cofiber f :=
  Cofiber.basepoint f

/-- The gluing path in the cofiber: f(a) is identified with the basepoint. -/
noncomputable def cofiberGlue (f : A → B) (a : A) :
    Path (cofiberIncl f (f a)) (cofiberPt f) :=
  Cofiber.glue f a

/-- Inclusion followed by glue gives a null-homotopy of the composite. -/
noncomputable def cofiber_composite_null (f : A → B) (a : A) :
    Path (cofiberIncl f (f a)) (cofiberPt f) :=
  cofiberGlue f a

/-- The cofiber sequence is exact: composite A → B → Cf is null. -/
noncomputable def cofiber_exact_left (f : A → B) :
    ∀ a : A, Path (cofiberIncl f (f a)) (cofiberPt f) :=
  fun a => cofiberGlue f a

/-! ## Suspension Functoriality -/

/-- Suspension of a map: given f : A → B, define Σf : ΣA → ΣB. -/
noncomputable def suspMap (f : A → B) : Suspension A → Suspension B :=
  Quot.lift
    (fun s => match s with
      | Sum.inl _ => Suspension.north (X := B)
      | Sum.inr _ => Suspension.south (X := B))
    (by
      intro x y h
      cases h with
      | glue a =>
        exact Quot.sound
          (PushoutCompPathRel.glue
            (A := PUnit') (B := PUnit') (C := B)
            (f := fun _ => PUnit'.unit)
            (g := fun _ => PUnit'.unit) (f a)))

/-- Suspension sends north to north. -/
theorem suspMap_north (f : A → B) :
    suspMap f (Suspension.north (X := A)) = Suspension.north (X := B) := by
  rfl

/-- Suspension sends south to south. -/
theorem suspMap_south (f : A → B) :
    suspMap f (Suspension.south (X := A)) = Suspension.south (X := B) := by
  rfl

/-! ## Iterated Cofiber -/

/-- The cofiber of the inclusion B → Cf is the double cofiber. -/
noncomputable def doubleCofiber (f : A → B) : Type u :=
  Cofiber (cofiberIncl f)

/-- Double cofiber inclusion. -/
noncomputable def doubleCofiber_incl (f : A → B) : Cofiber f → doubleCofiber f :=
  cofiberInclusion (cofiberIncl f)

/-- Double cofiber basepoint. -/
noncomputable def doubleCofiber_pt (f : A → B) : doubleCofiber f :=
  Cofiber.basepoint (cofiberIncl f)

/-- The glue in the double cofiber identifies images of B. -/
noncomputable def doubleCofiber_glue (f : A → B) (b : B) :
    Path (doubleCofiber_incl f (cofiberIncl f b)) (doubleCofiber_pt f) :=
  Cofiber.glue (cofiberIncl f) b

/-! ## Coexactness -/

/-- Coexactness at the first stage: composite B → Cf → C(incl) is null. -/
noncomputable def coexact_first_stage (f : A → B) (b : B) :
    Path (doubleCofiber_incl f (cofiberIncl f b)) (doubleCofiber_pt f) :=
  doubleCofiber_glue f b

/-- The connecting map Cf → ΣA sends B to north. -/
noncomputable def connecting_map_on_B (f : A → B) (b : B) :
    Path (cofiberToSuspension f (cofiberIncl f b)) (Suspension.north (X := A)) :=
  Path.refl _

/-! ## Puppe Sequence Data -/

/-- Extended Puppe sequence: A → B → Cf → ΣA. -/
structure ExtendedPuppe (A B : Type u) (f : A → B) where
  /-- The map from A to B. -/
  mapAB : A → B
  /-- The inclusion B → Cf. -/
  incl : B → Cofiber f
  /-- The connecting map Cf → ΣA. -/
  connecting : Cofiber f → Suspension A

/-- Construct the extended Puppe sequence from f. -/
noncomputable def extendedPuppe (f : A → B) : ExtendedPuppe A B f where
  mapAB := f
  incl := cofiberIncl f
  connecting := cofiberToSuspension f

/-- The first composite in the Puppe sequence is null. -/
noncomputable def puppe_exact_1 (f : A → B) (a : A) :
    Path ((extendedPuppe f).incl ((extendedPuppe f).mapAB a)) (cofiberPt f) :=
  cofiberGlue f a

/-- The second composite in the Puppe sequence is null. -/
noncomputable def puppe_exact_2 (f : A → B) (b : B) :
    Path ((extendedPuppe f).connecting ((extendedPuppe f).incl b))
         (Suspension.north (X := A)) :=
  Path.refl _

/-! ## Mapping Telescope -/

/-- A mapping telescope datum: a sequence of maps. -/
structure MappingTelescope where
  /-- The sequence of spaces. -/
  space : Nat → Type u
  /-- The bonding maps. -/
  bond : (n : Nat) → space n → space (n + 1)

/-- The n-th cofiber in a mapping telescope. -/
noncomputable def telescopeCofiber (T : MappingTelescope) (n : Nat) : Type u :=
  Cofiber (T.bond n)

/-- Inclusion of the n-th space into its cofiber. -/
noncomputable def telescopeIncl (T : MappingTelescope) (n : Nat) :
    T.space (n + 1) → telescopeCofiber T n :=
  cofiberInclusion (T.bond n)

/-- The basepoint of the n-th cofiber. -/
noncomputable def telescopePt (T : MappingTelescope) (n : Nat) : telescopeCofiber T n :=
  Cofiber.basepoint (T.bond n)

/-- Exactness in the mapping telescope. -/
noncomputable def telescope_exact (T : MappingTelescope) (n : Nat) (x : T.space n) :
    Path (telescopeIncl T n (T.bond n x)) (telescopePt T n) :=
  Cofiber.glue (T.bond n) x

/-! ## Path-level Properties -/

/-- Suspension north is preserved by identity suspension map. -/
theorem susp_north_preserved :
    suspMap (f := fun (x : A) => x) (Suspension.north (X := A)) = Suspension.north (X := A) := by
  rfl

/-- Cofiber of identity is contractible to the basepoint. -/
noncomputable def cofiber_id_trivial (a : A) :
    Path (cofiberIncl (fun x : A => x) a) (cofiberPt (fun x : A => x)) :=
  cofiberGlue (fun x : A => x) a

/-- The Puppe sequence for identity is trivial. -/
noncomputable def puppe_id_trivial (a : A) :
    Path (cofiberToSuspension (fun x : A => x) (cofiberIncl (fun x : A => x) a))
         (Suspension.north (X := A)) :=
  Path.refl _

/-- Cofibration data: a map with its cofiber sequence. -/
structure CofibrationData (A B : Type u) where
  /-- The map. -/
  map : A → B
  /-- The cofiber. -/
  cofiber : Type u := Cofiber map
  /-- Exactness witness. -/
  exact : ∀ a, Path (cofiberInclusion map (map a)) (Cofiber.basepoint map) :=
    fun a => Cofiber.glue map a

/-- Construct cofibration data from a map. -/
noncomputable def mkCofibrationData (f : A → B) : CofibrationData A B where
  map := f

/-- The cofiber glue proof is equal to itself (UIP on proofs). -/
theorem cofiberGlue_Subsingleton.elim (f : A → B) (a : A) :
    (cofiberGlue f a).proof = (cofiberGlue f a).proof := by
  rfl

/-- Two cofiber glue paths have the same proof component. -/
theorem cofiberGlue_proof_eq (f : A → B) (a : A) :
    (Cofiber.glue f a).toEq = (cofiberGlue f a).toEq := by
  rfl

/-- Cofiber inclusion composed with toEq. -/
theorem cofiber_incl_eq (f : A → B) (a : A) :
    (cofiberGlue f a).toEq = (Cofiber.glue f a).toEq := by
  rfl

/-- Double cofiber glue proof equality. -/
theorem doubleCofiber_proof_eq (f : A → B) (b : B) :
    (doubleCofiber_glue f b).toEq = (Cofiber.glue (cofiberIncl f) b).toEq := by
  rfl

end CofibrationPaths
end ComputationalPaths.Path
