/-
# Ring Spectrum Paths — Prime Spectrum, Zariski Topology, Localization, Structure Sheaf

This module encodes the prime spectrum of a commutative ring, the Zariski
topology as a path structure, localization at prime ideals, and the
structure sheaf, all witnessed by computational `Path` values.

## Key Constructions

- `SpecRing`: commutative ring data with Path-witnessed axioms
- `PrimeIdealData`: prime ideals with Path-witnessed closure properties
- `ZariskiOpen`: basic open sets D(f) and their path algebra
- `LocalizationData`: localization at a multiplicative set
- `StructureSheafData`: the structure sheaf on Spec R

## References

- Atiyah–Macdonald, *Introduction to Commutative Algebra*
- Hartshorne, *Algebraic Geometry*, Ch. II
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace RingSpectrum

open ComputationalPaths.Path

universe u v

/-! ## Ring with Path-witnessed axioms -/

structure SpecRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  mul_comm : ∀ a b, Path (mul a b) (mul b a)
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))

/-! ## Prime ideal -/

structure PrimeIdealData {R : Type u} (ring : SpecRing R) where
  mem : R → Prop
  mem_zero : mem ring.zero
  mem_add : ∀ a b, mem a → mem b → mem (ring.add a b)
  mem_mul_left : ∀ a b, mem a → mem (ring.mul a b)
  not_mem_one : ¬ mem ring.one
  prime : ∀ a b, mem (ring.mul a b) → mem a ∨ mem b

/-! ## Basic open sets D(f) -/

def basicOpen {R : Type u} (ring : SpecRing R) (f : R)
    (p : PrimeIdealData ring) : Prop :=
  ¬ p.mem f

-- 1
theorem basicOpen_one {R : Type u} (ring : SpecRing R)
    (p : PrimeIdealData ring) : basicOpen ring ring.one p :=
  p.not_mem_one

-- 2
theorem basicOpen_zero_false {R : Type u} (ring : SpecRing R)
    (p : PrimeIdealData ring) : ¬ basicOpen ring ring.zero p :=
  fun h => h p.mem_zero

-- 3
theorem basicOpen_mul_sub {R : Type u} (ring : SpecRing R)
    (f g : R) (p : PrimeIdealData ring)
    (h : basicOpen ring (ring.mul f g) p) :
    basicOpen ring f p ∧ basicOpen ring g p := by
  constructor
  · intro hf; exact h (p.mem_mul_left f g hf)
  · intro hg
    have hcomm : ring.mul f g = ring.mul g f := (ring.mul_comm f g).proof
    rw [hcomm] at h
    exact h (p.mem_mul_left g f hg)

-- 4
theorem basicOpen_mul_sup {R : Type u} (ring : SpecRing R)
    (f g : R) (p : PrimeIdealData ring)
    (hf : basicOpen ring f p) (hg : basicOpen ring g p) :
    basicOpen ring (ring.mul f g) p := by
  intro hmul
  cases p.prime f g hmul with
  | inl h => exact hf h
  | inr h => exact hg h

-- 5
theorem basicOpen_inter_eq_mul {R : Type u} (ring : SpecRing R)
    (f g : R) (p : PrimeIdealData ring) :
    (basicOpen ring f p ∧ basicOpen ring g p) ↔
    basicOpen ring (ring.mul f g) p :=
  ⟨fun ⟨hf, hg⟩ => basicOpen_mul_sup ring f g p hf hg,
   fun h => basicOpen_mul_sub ring f g p h⟩

/-! ## Multiplicative sets and localization -/

structure MultSet {R : Type u} (ring : SpecRing R) where
  mem : R → Prop
  one_mem : mem ring.one
  mul_mem : ∀ a b, mem a → mem b → mem (ring.mul a b)

-- 6
def primeComplement {R : Type u} {ring : SpecRing R}
    (p : PrimeIdealData ring) : MultSet ring where
  mem := fun r => ¬ p.mem r
  one_mem := p.not_mem_one
  mul_mem := fun a b ha hb h => by
    cases p.prime a b h with
    | inl h => exact ha h
    | inr h => exact hb h

structure LocalizationData {R : Type u} (ring : SpecRing R)
    (S : MultSet ring) where
  num : R
  den : R
  den_mem : S.mem den

def fracEquiv {R : Type u} {ring : SpecRing R} {S : MultSet ring}
    (x y : LocalizationData ring S) : Prop :=
  ∃ t : R, S.mem t ∧
    ring.mul t (ring.add (ring.mul x.num y.den)
                         (ring.neg (ring.mul y.num x.den))) = ring.zero

-- 7
theorem fracEquiv_refl {R : Type u} {ring : SpecRing R} {S : MultSet ring}
    (x : LocalizationData ring S) : fracEquiv x x := by
  refine ⟨ring.one, S.one_mem, ?_⟩
  have h := (ring.add_neg (ring.mul x.num x.den)).proof
  have h1 := (ring.one_mul (ring.add (ring.mul x.num x.den)
    (ring.neg (ring.mul x.num x.den)))).proof
  rw [h1, h]

-- 8
def fracEquivReflPath {R : Type u} {ring : SpecRing R} {S : MultSet ring}
    (x : LocalizationData ring S) :
    Path (fracEquiv x x) True :=
  Path.mk [Step.mk _ _ (propext ⟨fun _ => trivial, fun _ => fracEquiv_refl x⟩)]
    (propext ⟨fun _ => trivial, fun _ => fracEquiv_refl x⟩)

/-! ## Localization at a prime -/

def localizeAtPrime {R : Type u} {ring : SpecRing R}
    (p : PrimeIdealData ring) :=
  LocalizationData ring (primeComplement p)

-- 9
def toLocalization {R : Type u} {ring : SpecRing R}
    (p : PrimeIdealData ring) (r : R) : localizeAtPrime p :=
  ⟨r, ring.one, p.not_mem_one⟩

/-! ## Vanishing ideal V(S) -/

def vanishing {R : Type u} (ring : SpecRing R)
    (S : R → Prop) (p : PrimeIdealData ring) : Prop :=
  ∀ f, S f → p.mem f

-- 10
theorem vanishing_empty {R : Type u} (ring : SpecRing R)
    (p : PrimeIdealData ring) :
    vanishing ring (fun _ => False) p :=
  fun _ hf => hf.elim

-- 11
theorem vanishing_whole_empty {R : Type u} (ring : SpecRing R)
    (p : PrimeIdealData ring) :
    ¬ vanishing ring (fun _ => True) p :=
  fun h => p.not_mem_one (h ring.one trivial)

-- 12
theorem vanishing_mono {R : Type u} (ring : SpecRing R)
    (S T : R → Prop) (hST : ∀ f, S f → T f)
    (p : PrimeIdealData ring) (hp : vanishing ring T p) :
    vanishing ring S p :=
  fun f hf => hp f (hST f hf)

-- 13
theorem vanishing_singleton_mul {R : Type u} (ring : SpecRing R)
    (f g : R) (p : PrimeIdealData ring) :
    p.mem (ring.mul f g) ↔ (p.mem f ∨ p.mem g) := by
  constructor
  · exact p.prime f g
  · intro h; cases h with
    | inl hf =>
      have hmfg : ring.mul f g = ring.mul f g := rfl
      exact p.mem_mul_left f g hf
    | inr hg =>
      have hcomm : ring.mul f g = ring.mul g f := (ring.mul_comm f g).proof
      rw [hcomm]; exact p.mem_mul_left g f hg

-- 14
theorem basicOpen_eq_compl_vanishing {R : Type u} (ring : SpecRing R)
    (f : R) (p : PrimeIdealData ring) :
    basicOpen ring f p ↔ ¬ vanishing ring (· = f) p :=
  ⟨fun hf hv => hf (hv f rfl), fun h hf => h (fun _ hg => hg ▸ hf)⟩

/-! ## Ring powers -/

def ringPow {R : Type u} (ring : SpecRing R) (f : R) : Nat → R
  | 0 => ring.one
  | n + 1 => ring.mul f (ringPow ring f n)

-- 15
theorem ringPow_zero {R : Type u} (ring : SpecRing R) (f : R) :
    ringPow ring f 0 = ring.one := rfl

-- 16
theorem ringPow_succ {R : Type u} (ring : SpecRing R) (f : R) (n : Nat) :
    ringPow ring f (n + 1) = ring.mul f (ringPow ring f n) := rfl

-- 17
theorem basicOpen_pow {R : Type u} (ring : SpecRing R)
    (f : R) (p : PrimeIdealData ring) (n : Nat) (hn : n ≥ 1)
    (hf : basicOpen ring f p) :
    basicOpen ring (ringPow ring f n) p := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp [ringPow]
    exact basicOpen_mul_sup ring f (ringPow ring f k) p hf (by
      cases k with
      | zero => simp [ringPow]; exact p.not_mem_one
      | succ m => exact ih (by omega))

/-! ## Structure sheaf sections -/

structure SheafSection {R : Type u} (ring : SpecRing R) (f : R) where
  num : R
  den : R
  den_power : ∃ n : Nat, den = ringPow ring f n

def sectionEquiv {R : Type u} {ring : SpecRing R} {f : R}
    (s t : SheafSection ring f) : Prop :=
  ∃ k : Nat,
    ring.mul (ringPow ring f k)
      (ring.add (ring.mul s.num t.den)
                (ring.neg (ring.mul t.num s.den))) = ring.zero

-- 18
def zeroSection {R : Type u} (ring : SpecRing R) (f : R) :
    SheafSection ring f :=
  ⟨ring.zero, ring.one, ⟨0, rfl⟩⟩

-- 19
def oneSection {R : Type u} (ring : SpecRing R) (f : R) :
    SheafSection ring f :=
  ⟨ring.one, ring.one, ⟨0, rfl⟩⟩

/-! ## Nilradical and reduced rings -/

def isNilpotent {R : Type u} (ring : SpecRing R) (f : R) : Prop :=
  ∃ n : Nat, ringPow ring f n = ring.zero

def isReduced {R : Type u} (ring : SpecRing R) : Prop :=
  ∀ f, isNilpotent ring f → f = ring.zero

-- 20
theorem nilpotent_not_basicOpen {R : Type u} (ring : SpecRing R)
    (f : R) (n : Nat) (hn : ringPow ring f (n + 1) = ring.zero)
    (p : PrimeIdealData ring)
    (hf : basicOpen ring f p) : False := by
  have hpow := basicOpen_pow ring f p (n + 1) (by omega) hf
  simp [basicOpen] at hpow
  exact hpow (hn ▸ p.mem_zero)

/-! ## Spec functoriality -/

structure SpecHom {R : Type u} {S : Type v}
    (rR : SpecRing R) (rS : SpecRing S) where
  toFun : R → S
  map_zero : Path (toFun rR.zero) rS.zero
  map_one : Path (toFun rR.one) rS.one
  map_add : ∀ a b, Path (toFun (rR.add a b)) (rS.add (toFun a) (toFun b))
  map_mul : ∀ a b, Path (toFun (rR.mul a b)) (rS.mul (toFun a) (toFun b))

-- 21
def specMap {R : Type u} {S : Type v}
    {rR : SpecRing R} {rS : SpecRing S}
    (φ : SpecHom rR rS)
    (q : PrimeIdealData rS) : PrimeIdealData rR where
  mem := fun r => q.mem (φ.toFun r)
  mem_zero := (φ.map_zero).proof ▸ q.mem_zero
  mem_add := fun a b ha hb => by
    have := (φ.map_add a b).proof
    rw [this]; exact q.mem_add _ _ ha hb
  mem_mul_left := fun a b ha => by
    have := (φ.map_mul a b).proof
    rw [this]; exact q.mem_mul_left _ _ ha
  not_mem_one := by
    intro h; have := (φ.map_one).proof; rw [this] at h
    exact q.not_mem_one h
  prime := fun a b hab => by
    have := (φ.map_mul a b).proof; rw [this] at hab
    exact q.prime _ _ hab

-- 22
theorem specMap_basicOpen {R : Type u} {S : Type v}
    {rR : SpecRing R} {rS : SpecRing S}
    (φ : SpecHom rR rS)
    (q : PrimeIdealData rS) (f : R) :
    basicOpen rR f (specMap φ q) ↔ basicOpen rS (φ.toFun f) q :=
  ⟨fun h => h, fun h => h⟩

-- 23
def specHomId {R : Type u} (rR : SpecRing R) : SpecHom rR rR where
  toFun := id
  map_zero := Path.refl _
  map_one := Path.refl _
  map_add := fun _ _ => Path.refl _
  map_mul := fun _ _ => Path.refl _

-- 24
theorem specMap_id_mem {R : Type u} {rR : SpecRing R}
    (p : PrimeIdealData rR) (r : R) :
    (specMap (specHomId rR) p).mem r ↔ p.mem r :=
  ⟨fun h => h, fun h => h⟩

-- 25
def specHomComp {R S T : Type u}
    {rR : SpecRing R} {rS : SpecRing S} {rT : SpecRing T}
    (φ : SpecHom rR rS) (ψ : SpecHom rS rT) : SpecHom rR rT where
  toFun := ψ.toFun ∘ φ.toFun
  map_zero := trans (congrArg ψ.toFun φ.map_zero) ψ.map_zero
  map_one := trans (congrArg ψ.toFun φ.map_one) ψ.map_one
  map_add := fun a b => trans (congrArg ψ.toFun (φ.map_add a b))
    (trans (ψ.map_add (φ.toFun a) (φ.toFun b)) (Path.refl _))
  map_mul := fun a b => trans (congrArg ψ.toFun (φ.map_mul a b))
    (trans (ψ.map_mul (φ.toFun a) (φ.toFun b)) (Path.refl _))

-- 26
theorem specMap_comp_mem {R S T : Type u}
    {rR : SpecRing R} {rS : SpecRing S} {rT : SpecRing T}
    (φ : SpecHom rR rS) (ψ : SpecHom rS rT)
    (q : PrimeIdealData rT) (r : R) :
    (specMap (specHomComp φ ψ) q).mem r ↔
    (specMap φ (specMap ψ q)).mem r :=
  ⟨fun h => h, fun h => h⟩

-- 27
theorem basicOpen_sq {R : Type u} (ring : SpecRing R)
    (f : R) (p : PrimeIdealData ring) :
    basicOpen ring (ring.mul f f) p ↔ basicOpen ring f p := by
  constructor
  · intro h hf; exact h (p.mem_mul_left f f hf)
  · intro hf; exact basicOpen_mul_sup ring f f p hf hf

-- 28
theorem basicOpen_bool_dec (ring : SpecRing Bool)
    (f : Bool) (p : PrimeIdealData ring) :
    basicOpen ring f p ∨ ¬ basicOpen ring f p :=
  Classical.em _

-- 29
theorem vanishing_singleton {R : Type u} (ring : SpecRing R)
    (f : R) (p : PrimeIdealData ring) :
    vanishing ring (· = f) p ↔ p.mem f :=
  ⟨fun h => h f rfl, fun hf _ hg => hg ▸ hf⟩

-- 30
theorem basicOpen_comm {R : Type u} (ring : SpecRing R)
    (f g : R) (p : PrimeIdealData ring) :
    basicOpen ring (ring.mul f g) p ↔ basicOpen ring (ring.mul g f) p := by
  have h := (ring.mul_comm f g).proof
  constructor
  · intro hfg; rw [h] at hfg; exact hfg
  · intro hgf; rw [h]; exact hgf

end RingSpectrum
end Algebra
end Path
end ComputationalPaths
