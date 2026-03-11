/-
# Homological Stability via Computational Paths

This module develops homological stability for families of groups,
Quillen's stability for GL_n, mapping class groups, configuration spaces,
and scanning maps through computational paths.

## References

- Quillen, "On the Cohomology and K-Theory of the General Linear Groups"
- Hatcher-Vogtmann, "Homological Stability for Unitary Groups"
- Randal-Williams, Wahl, "Homological Stability for Automorphism Groups"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Stabilization Maps -/

/-- A stabilization system: a family of groups with stabilization maps. -/
structure StabilizationSystem (G : Nat → Type u) where
  mul : ∀ n, G n → G n → G n
  one : ∀ n, G n
  inv : ∀ n, G n → G n
  stab : ∀ n, G n → G (n + 1)
  mul_assoc : ∀ n (a b c : G n), Path (mul n (mul n a b) c) (mul n a (mul n b c))
  mul_one : ∀ n (a : G n), Path (mul n a (one n)) a
  one_mul : ∀ n (a : G n), Path (mul n (one n) a) a
  inv_left : ∀ n (a : G n), Path (mul n (inv n a) a) (one n)
  inv_right : ∀ n (a : G n), Path (mul n a (inv n a)) (one n)
  stab_hom : ∀ n (a b : G n), Path (stab n (mul n a b)) (mul (n+1) (stab n a) (stab n b))
  stab_one : ∀ n, Path (stab n (one n)) (one (n+1))

namespace StabilizationSystem

variable {G : Nat → Type u} (S : StabilizationSystem G)

theorem mul_assoc_eq (n : Nat) (a b c : G n) : S.mul n (S.mul n a b) c = S.mul n a (S.mul n b c) :=
  (S.mul_assoc n a b c).toEq

theorem mul_one_eq (n : Nat) (a : G n) : S.mul n a (S.one n) = a := (S.mul_one n a).toEq

theorem one_mul_eq (n : Nat) (a : G n) : S.mul n (S.one n) a = a := (S.one_mul n a).toEq

theorem inv_left_eq (n : Nat) (a : G n) : S.mul n (S.inv n a) a = S.one n :=
  (S.inv_left n a).toEq

theorem inv_right_eq (n : Nat) (a : G n) : S.mul n a (S.inv n a) = S.one n :=
  (S.inv_right n a).toEq

theorem stab_hom_eq (n : Nat) (a b : G n) :
    S.stab n (S.mul n a b) = S.mul (n+1) (S.stab n a) (S.stab n b) :=
  (S.stab_hom n a b).toEq

theorem stab_one_eq (n : Nat) : S.stab n (S.one n) = S.one (n+1) :=
  (S.stab_one n).toEq

/-- Stabilization preserves inverses. -/
noncomputable def stab_inv (n : Nat) (a : G n) :
    Path (S.mul (n+1) (S.stab n a) (S.stab n (S.inv n a))) (S.one (n+1)) :=
  Path.trans (Path.symm (S.stab_hom n a (S.inv n a)))
    (Path.trans (congrArg (S.stab n) (S.inv_right n a)) (S.stab_one n))

theorem stab_inv_eq (n : Nat) (a : G n) :
    S.mul (n+1) (S.stab n a) (S.stab n (S.inv n a)) = S.one (n+1) :=
  (S.stab_inv n a).toEq

/-- Double stabilization is a homomorphism. -/
noncomputable def double_stab_hom (n : Nat) (a b : G n) :
    Path (S.stab (n+1) (S.stab n (S.mul n a b)))
         (S.mul (n+2) (S.stab (n+1) (S.stab n a)) (S.stab (n+1) (S.stab n b))) :=
  Path.trans (congrArg (S.stab (n+1)) (S.stab_hom n a b))
             (S.stab_hom (n+1) (S.stab n a) (S.stab n b))

theorem double_stab_hom_eq (n : Nat) (a b : G n) :
    S.stab (n+1) (S.stab n (S.mul n a b)) =
    S.mul (n+2) (S.stab (n+1) (S.stab n a)) (S.stab (n+1) (S.stab n b)) :=
  (S.double_stab_hom n a b).toEq

/-- Triple product after stabilization. -/
noncomputable def stab_triple (n : Nat) (a b c : G n) :
    Path (S.mul (n+1) (S.mul (n+1) (S.stab n a) (S.stab n b)) (S.stab n c))
         (S.mul (n+1) (S.stab n a) (S.mul (n+1) (S.stab n b) (S.stab n c))) :=
  S.mul_assoc (n+1) (S.stab n a) (S.stab n b) (S.stab n c)

theorem stab_triple_eq (n : Nat) (a b c : G n) :
    S.mul (n+1) (S.mul (n+1) (S.stab n a) (S.stab n b)) (S.stab n c) =
    S.mul (n+1) (S.stab n a) (S.mul (n+1) (S.stab n b) (S.stab n c)) :=
  (S.stab_triple n a b c).toEq

/-- Stabilization of one twice. -/
noncomputable def stab_one_twice (n : Nat) :
    Path (S.stab (n+1) (S.stab n (S.one n))) (S.one (n+2)) :=
  Path.trans (congrArg (S.stab (n+1)) (S.stab_one n)) (S.stab_one (n+1))

theorem stab_one_twice_eq (n : Nat) : S.stab (n+1) (S.stab n (S.one n)) = S.one (n+2) :=
  (S.stab_one_twice n).toEq

end StabilizationSystem

/-! ## Homological Stability Data -/

/-- Homological stability: the stabilization map induces isomorphism in homology up to degree n/2. -/
structure HomologicalStabilityData (G : Nat → Type u) (H : Nat → Nat → Type v) where
  sys : StabilizationSystem G
  homology_map : ∀ n k, H n k → H (n+1) k
  stability_iso : ∀ n k, k ≤ n / 2 → (H n k → H (n+1) k) × (H (n+1) k → H n k)
  left_inv : ∀ n k (hk : k ≤ n / 2) (h : H n k),
    Path ((stability_iso n k hk).2 ((stability_iso n k hk).1 h)) h
  right_inv : ∀ n k (hk : k ≤ n / 2) (h : H (n+1) k),
    Path ((stability_iso n k hk).1 ((stability_iso n k hk).2 h)) h

namespace HomologicalStabilityData

variable {G : Nat → Type u} {H : Nat → Nat → Type v} (HS : HomologicalStabilityData G H)

theorem left_inv_eq (n k : Nat) (hk : k ≤ n / 2) (h : H n k) :
    (HS.stability_iso n k hk).2 ((HS.stability_iso n k hk).1 h) = h :=
  (HS.left_inv n k hk h).toEq

theorem right_inv_eq (n k : Nat) (hk : k ≤ n / 2) (h : H (n+1) k) :
    (HS.stability_iso n k hk).1 ((HS.stability_iso n k hk).2 h) = h :=
  (HS.right_inv n k hk h).toEq

/-- Double roundtrip is identity. -/
noncomputable def double_roundtrip (n k : Nat) (hk : k ≤ n / 2) (h : H n k) :
    Path ((HS.stability_iso n k hk).2 ((HS.stability_iso n k hk).1
          ((HS.stability_iso n k hk).2 ((HS.stability_iso n k hk).1 h)))) h :=
  Path.trans (congrArg (HS.stability_iso n k hk).2
    (congrArg (HS.stability_iso n k hk).1 (HS.left_inv n k hk h)))
    (HS.left_inv n k hk h)

theorem double_roundtrip_eq (n k : Nat) (hk : k ≤ n / 2) (h : H n k) :
    (HS.stability_iso n k hk).2 ((HS.stability_iso n k hk).1
      ((HS.stability_iso n k hk).2 ((HS.stability_iso n k hk).1 h))) = h :=
  (HS.double_roundtrip n k hk h).toEq

end HomologicalStabilityData

/-! ## Configuration Spaces -/

/-- Configuration space of n points in a manifold. -/
structure ConfigurationSpace (M : Type u) (n : Nat) where
  config : Type v
  inclusion : config → config  -- stabilization: add point at infinity
  forget : config → config     -- forget last point
  incl_forget : ∀ (c : config), Path (forget (inclusion c)) c
  points : config → Fin n → M

namespace ConfigurationSpace

variable {M : Type u} {n : Nat} (C : ConfigurationSpace M n)

theorem incl_forget_eq (c : C.config) : C.forget (C.inclusion c) = c :=
  (C.incl_forget c).toEq

/-- Double inclusion then forget. -/
noncomputable def double_incl_forget (c : C.config) :
    Path (C.forget (C.inclusion (C.forget (C.inclusion c)))) c :=
  Path.trans (congrArg C.forget (congrArg C.inclusion (C.incl_forget c))) (C.incl_forget c)

theorem double_incl_forget_eq (c : C.config) :
    C.forget (C.inclusion (C.forget (C.inclusion c))) = c :=
  (C.double_incl_forget c).toEq

/-- Triple application of incl then forget. -/
noncomputable def triple_incl_forget (c : C.config) :
    Path (C.forget (C.inclusion (C.forget (C.inclusion (C.forget (C.inclusion c)))))) c :=
  Path.trans (congrArg C.forget (congrArg C.inclusion (C.double_incl_forget c))) (C.incl_forget c)

theorem triple_incl_forget_eq (c : C.config) :
    C.forget (C.inclusion (C.forget (C.inclusion (C.forget (C.inclusion c))))) = c :=
  (C.triple_incl_forget c).toEq

end ConfigurationSpace

/-! ## Scanning Maps -/

/-- Scanning map data for homological stability. -/
structure ScanningMap (C : Type u) (Ω : Type v) where
  scan : C → Ω
  inv_scan : Ω → C
  scan_inv : ∀ (ω : Ω), Path (scan (inv_scan ω)) ω
  inv_scan_id : ∀ (c : C), Path (inv_scan (scan c)) c

namespace ScanningMap

variable {C : Type u} {Ω : Type v} (SM : ScanningMap C Ω)

theorem scan_inv_eq (ω : Ω) : SM.scan (SM.inv_scan ω) = ω := (SM.scan_inv ω).toEq

theorem inv_scan_eq (c : C) : SM.inv_scan (SM.scan c) = c := (SM.inv_scan_id c).toEq

/-- Double scan roundtrip. -/
noncomputable def double_scan (ω : Ω) :
    Path (SM.scan (SM.inv_scan (SM.scan (SM.inv_scan ω)))) ω :=
  Path.trans (congrArg SM.scan (congrArg SM.inv_scan (SM.scan_inv ω))) (SM.scan_inv ω)

theorem double_scan_eq (ω : Ω) : SM.scan (SM.inv_scan (SM.scan (SM.inv_scan ω))) = ω :=
  (SM.double_scan ω).toEq

/-- Double inv_scan roundtrip. -/
noncomputable def double_inv_scan (c : C) :
    Path (SM.inv_scan (SM.scan (SM.inv_scan (SM.scan c)))) c :=
  Path.trans (congrArg SM.inv_scan (congrArg SM.scan (SM.inv_scan_id c))) (SM.inv_scan_id c)

theorem double_inv_scan_eq (c : C) : SM.inv_scan (SM.scan (SM.inv_scan (SM.scan c))) = c :=
  (SM.double_inv_scan c).toEq

end ScanningMap

/-! ## Mapping Class Groups -/

/-- Mapping class group of a surface. -/
structure MappingClassGroup (Σ : Type u) where
  elem : Type v
  mul : elem → elem → elem
  one : elem
  inv : elem → elem
  mul_assoc : ∀ (a b c : elem), Path (mul (mul a b) c) (mul a (mul b c))
  mul_one : ∀ (a : elem), Path (mul a one) a
  one_mul : ∀ (a : elem), Path (mul one a) a
  inv_left : ∀ (a : elem), Path (mul (inv a) a) one
  inv_right : ∀ (a : elem), Path (mul a (inv a)) one
  genus : Nat
  stab : elem → elem  -- stabilization by increasing genus
  stab_hom : ∀ (a b : elem), Path (stab (mul a b)) (mul (stab a) (stab b))
  stab_one : Path (stab one) one

namespace MappingClassGroup

variable {Σ : Type u} (MCG : MappingClassGroup Σ)

theorem mul_assoc_eq (a b c : MCG.elem) : MCG.mul (MCG.mul a b) c = MCG.mul a (MCG.mul b c) :=
  (MCG.mul_assoc a b c).toEq

theorem mul_one_eq (a : MCG.elem) : MCG.mul a MCG.one = a := (MCG.mul_one a).toEq

theorem one_mul_eq (a : MCG.elem) : MCG.mul MCG.one a = a := (MCG.one_mul a).toEq

theorem inv_left_eq (a : MCG.elem) : MCG.mul (MCG.inv a) a = MCG.one :=
  (MCG.inv_left a).toEq

theorem inv_right_eq (a : MCG.elem) : MCG.mul a (MCG.inv a) = MCG.one :=
  (MCG.inv_right a).toEq

theorem stab_hom_eq (a b : MCG.elem) : MCG.stab (MCG.mul a b) = MCG.mul (MCG.stab a) (MCG.stab b) :=
  (MCG.stab_hom a b).toEq

theorem stab_one_eq : MCG.stab MCG.one = MCG.one := MCG.stab_one.toEq

/-- Stabilization preserves inverses. -/
noncomputable def stab_inv (a : MCG.elem) :
    Path (MCG.mul (MCG.stab a) (MCG.stab (MCG.inv a))) MCG.one :=
  Path.trans (Path.symm (MCG.stab_hom a (MCG.inv a)))
    (Path.trans (congrArg MCG.stab (MCG.inv_right a)) MCG.stab_one)

theorem stab_inv_eq (a : MCG.elem) : MCG.mul (MCG.stab a) (MCG.stab (MCG.inv a)) = MCG.one :=
  (MCG.stab_inv a).toEq

/-- Triple product associativity. -/
noncomputable def triple_assoc (a b c d : MCG.elem) :
    Path (MCG.mul (MCG.mul (MCG.mul a b) c) d) (MCG.mul a (MCG.mul b (MCG.mul c d))) :=
  Path.trans (MCG.mul_assoc (MCG.mul a b) c d) (MCG.mul_assoc a b (MCG.mul c d))

theorem triple_assoc_eq (a b c d : MCG.elem) :
    MCG.mul (MCG.mul (MCG.mul a b) c) d = MCG.mul a (MCG.mul b (MCG.mul c d)) :=
  (MCG.triple_assoc a b c d).toEq

/-- Stab of triple product. -/
noncomputable def stab_triple (a b c : MCG.elem) :
    Path (MCG.stab (MCG.mul (MCG.mul a b) c))
         (MCG.mul (MCG.mul (MCG.stab a) (MCG.stab b)) (MCG.stab c)) :=
  Path.trans (MCG.stab_hom (MCG.mul a b) c)
    (congrArg (fun z => MCG.mul z (MCG.stab c)) (MCG.stab_hom a b))

theorem stab_triple_eq (a b c : MCG.elem) :
    MCG.stab (MCG.mul (MCG.mul a b) c) =
    MCG.mul (MCG.mul (MCG.stab a) (MCG.stab b)) (MCG.stab c) :=
  (MCG.stab_triple a b c).toEq

/-- Conjugation invariant after stab. -/
noncomputable def stab_conj (a b : MCG.elem) :
    Path (MCG.stab (MCG.mul (MCG.mul a b) (MCG.inv a)))
         (MCG.mul (MCG.mul (MCG.stab a) (MCG.stab b)) (MCG.stab (MCG.inv a))) :=
  MCG.stab_triple a b (MCG.inv a)

theorem stab_conj_eq (a b : MCG.elem) :
    MCG.stab (MCG.mul (MCG.mul a b) (MCG.inv a)) =
    MCG.mul (MCG.mul (MCG.stab a) (MCG.stab b)) (MCG.stab (MCG.inv a)) :=
  (MCG.stab_conj a b).toEq

end MappingClassGroup

/-! ## Quillen Stability for GL_n -/

/-- GL_n stabilization system. -/
structure GLStability (F : Type u) where
  GLn : Nat → Type v
  mul : ∀ n, GLn n → GLn n → GLn n
  one : ∀ n, GLn n
  inv : ∀ n, GLn n → GLn n
  stab : ∀ n, GLn n → GLn (n + 1)  -- A ↦ (A 0; 0 1)
  mul_assoc : ∀ n (a b c : GLn n), Path (mul n (mul n a b) c) (mul n a (mul n b c))
  mul_one : ∀ n (a : GLn n), Path (mul n a (one n)) a
  one_mul : ∀ n (a : GLn n), Path (mul n (one n) a) a
  inv_left : ∀ n (a : GLn n), Path (mul n (inv n a) a) (one n)
  inv_right : ∀ n (a : GLn n), Path (mul n a (inv n a)) (one n)
  stab_hom : ∀ n (a b : GLn n), Path (stab n (mul n a b)) (mul (n+1) (stab n a) (stab n b))
  stab_one : ∀ n, Path (stab n (one n)) (one (n+1))

namespace GLStability

variable {F : Type u} (GL : GLStability F)

theorem mul_assoc_eq (n : Nat) (a b c : GL.GLn n) :
    GL.mul n (GL.mul n a b) c = GL.mul n a (GL.mul n b c) :=
  (GL.mul_assoc n a b c).toEq

theorem mul_one_eq (n : Nat) (a : GL.GLn n) : GL.mul n a (GL.one n) = a :=
  (GL.mul_one n a).toEq

theorem stab_hom_eq (n : Nat) (a b : GL.GLn n) :
    GL.stab n (GL.mul n a b) = GL.mul (n+1) (GL.stab n a) (GL.stab n b) :=
  (GL.stab_hom n a b).toEq

theorem stab_one_eq (n : Nat) : GL.stab n (GL.one n) = GL.one (n+1) :=
  (GL.stab_one n).toEq

/-- Double stabilization. -/
noncomputable def double_stab_one (n : Nat) :
    Path (GL.stab (n+1) (GL.stab n (GL.one n))) (GL.one (n+2)) :=
  Path.trans (congrArg (GL.stab (n+1)) (GL.stab_one n)) (GL.stab_one (n+1))

theorem double_stab_one_eq (n : Nat) : GL.stab (n+1) (GL.stab n (GL.one n)) = GL.one (n+2) :=
  (GL.double_stab_one n).toEq

/-- Stab preserves inverses. -/
noncomputable def stab_inv (n : Nat) (a : GL.GLn n) :
    Path (GL.mul (n+1) (GL.stab n a) (GL.stab n (GL.inv n a))) (GL.one (n+1)) :=
  Path.trans (Path.symm (GL.stab_hom n a (GL.inv n a)))
    (Path.trans (congrArg (GL.stab n) (GL.inv_right n a)) (GL.stab_one n))

theorem stab_inv_eq (n : Nat) (a : GL.GLn n) :
    GL.mul (n+1) (GL.stab n a) (GL.stab n (GL.inv n a)) = GL.one (n+1) :=
  (GL.stab_inv n a).toEq

/-- Stab of triple product. -/
noncomputable def stab_triple (n : Nat) (a b c : GL.GLn n) :
    Path (GL.stab n (GL.mul n (GL.mul n a b) c))
         (GL.mul (n+1) (GL.mul (n+1) (GL.stab n a) (GL.stab n b)) (GL.stab n c)) :=
  Path.trans (GL.stab_hom n (GL.mul n a b) c)
    (congrArg (fun z => GL.mul (n+1) z (GL.stab n c)) (GL.stab_hom n a b))

theorem stab_triple_eq (n : Nat) (a b c : GL.GLn n) :
    GL.stab n (GL.mul n (GL.mul n a b) c) =
    GL.mul (n+1) (GL.mul (n+1) (GL.stab n a) (GL.stab n b)) (GL.stab n c) :=
  (GL.stab_triple n a b c).toEq

end GLStability

/-! ## Highly Connected Semisimplicial Sets -/

/-- Semisimplicial set data for proving homological stability. -/
structure SemisimplicialSet (X : Nat → Type u) where
  face : ∀ n (i : Fin (n + 1)), X (n + 1) → X n
  face_face : ∀ n (i j : Fin (n + 1)) (hij : i.val ≤ j.val) (x : X (n + 2)),
    Path (face n i (face (n+1) ⟨j.val + 1, by omega⟩ x))
         (face n ⟨j.val, by omega⟩ (face (n+1) ⟨i.val, by omega⟩ x))

namespace SemisimplicialSet

variable {X : Nat → Type u} (SS : SemisimplicialSet X)

/-- Augmented semisimplicial set. -/
structure Augmented where
  aug : Type u
  augMap : X 0 → aug

end SemisimplicialSet

/-! ## Spectral Sequence for Stability -/

/-- Spectral sequence data converging to homology of stabilization. -/
structure StabilitySpectralSequence (E : Nat → Nat → Type u) where
  zero : ∀ p q, E p q
  differential : ∀ r p q, E p q → E (p - r) (q + r - 1)
  d_squared : ∀ r p q (x : E p q),
    Path (differential r (p - r) (q + r - 1) (differential r p q x)) (zero (p - 2*r) (q + 2*r - 2))
  converges : ∀ p q, E p q  -- E^∞ term

namespace StabilitySpectralSequence

variable {E : Nat → Nat → Type u} (SS : StabilitySpectralSequence E)

theorem d_squared_eq (r p q : Nat) (x : E p q) :
    SS.differential r (p - r) (q + r - 1) (SS.differential r p q x) = SS.zero (p - 2*r) (q + 2*r - 2) :=
  (SS.d_squared r p q x).toEq

end StabilitySpectralSequence

/-! ## High Connectivity -/

/-- Connectivity data: X_n is (n/2)-connected. -/
structure ConnectivityBound (X : Nat → Type u) where
  conn : Nat → Nat  -- connectivity of X_n
  conn_bound : ∀ n, conn n ≥ n / 2
  conn_mono : ∀ n, conn (n + 1) ≥ conn n

/-! ## Homology Groups -/

/-- Homology group of a chain complex. -/
structure HomologyGroup (C : Nat → Type u) where
  differential : ∀ n, C (n + 1) → C n
  zero : ∀ n, C n
  add : ∀ n, C n → C n → C n
  d_squared : ∀ n (c : C (n + 2)), Path (differential n (differential (n+1) c)) (zero n)
  add_assoc : ∀ n (a b c : C n), Path (add n (add n a b) c) (add n a (add n b c))
  add_comm : ∀ n (a b : C n), Path (add n a b) (add n b a)
  add_zero : ∀ n (a : C n), Path (add n a (zero n)) a

namespace HomologyGroup

variable {C : Nat → Type u} (HG : HomologyGroup C)

theorem d_squared_eq (n : Nat) (c : C (n + 2)) : HG.differential n (HG.differential (n+1) c) = HG.zero n :=
  (HG.d_squared n c).toEq

theorem add_assoc_eq (n : Nat) (a b c : C n) : HG.add n (HG.add n a b) c = HG.add n a (HG.add n b c) :=
  (HG.add_assoc n a b c).toEq

theorem add_comm_eq (n : Nat) (a b : C n) : HG.add n a b = HG.add n b a :=
  (HG.add_comm n a b).toEq

theorem add_zero_eq (n : Nat) (a : C n) : HG.add n a (HG.zero n) = a :=
  (HG.add_zero n a).toEq

/-- d³ = 0. -/
noncomputable def d_cubed (n : Nat) (c : C (n + 3)) :
    Path (HG.differential n (HG.differential (n+1) (HG.differential (n+2) c))) (HG.zero n) :=
  HG.d_squared n (HG.differential (n+2) c)

theorem d_cubed_eq (n : Nat) (c : C (n + 3)) :
    HG.differential n (HG.differential (n+1) (HG.differential (n+2) c)) = HG.zero n :=
  (HG.d_cubed n c).toEq

/-- Sum with zero on both sides. -/
noncomputable def add_zero_twice (n : Nat) (a : C n) :
    Path (HG.add n (HG.add n a (HG.zero n)) (HG.zero n)) a :=
  Path.trans (HG.add_zero n (HG.add n a (HG.zero n))) (HG.add_zero n a)

theorem add_zero_twice_eq (n : Nat) (a : C n) :
    HG.add n (HG.add n a (HG.zero n)) (HG.zero n) = a :=
  (HG.add_zero_twice n a).toEq

end HomologyGroup

/-! ## Transfer Maps -/

/-- Transfer (Becker-Gottlieb) map data. -/
structure TransferMap (H : Type u) where
  transfer : H → H
  res : H → H
  norm : H → H
  transfer_res : ∀ (h : H), Path (transfer (res h)) (norm h)
  res_transfer : ∀ (h : H), Path (res (transfer h)) (norm h)

namespace TransferMap

variable {H : Type u} (T : TransferMap H)

theorem transfer_res_eq (h : H) : T.transfer (T.res h) = T.norm h :=
  (T.transfer_res h).toEq

theorem res_transfer_eq (h : H) : T.res (T.transfer h) = T.norm h :=
  (T.res_transfer h).toEq

/-- Double transfer-res. -/
noncomputable def double_transfer_res (h : H) :
    Path (T.transfer (T.res (T.transfer (T.res h)))) (T.norm (T.norm h)) :=
  Path.trans (congrArg T.transfer (congrArg T.res (T.transfer_res h))) (T.transfer_res (T.norm h))

theorem double_transfer_res_eq (h : H) :
    T.transfer (T.res (T.transfer (T.res h))) = T.norm (T.norm h) :=
  (T.double_transfer_res h).toEq

/-- Symmetry of transfer and restriction. -/
noncomputable def transfer_res_symm (h : H) :
    Path (T.norm h) (T.transfer (T.res h)) :=
  Path.symm (T.transfer_res h)

theorem transfer_res_symm_eq (h : H) : T.norm h = T.transfer (T.res h) :=
  (T.transfer_res_symm h).toEq

end TransferMap

/-! ## Hurewicz Map for Stability -/

/-- Hurewicz map in the context of homological stability. -/
structure HurewiczStability (π : Nat → Type u) (H : Nat → Type v) where
  hurewicz : ∀ n, π n → H n
  stab_π : ∀ n, π n → π (n + 1)
  stab_H : ∀ n, H n → H (n + 1)
  naturality : ∀ n (x : π n), Path (hurewicz (n+1) (stab_π n x)) (stab_H n (hurewicz n x))

namespace HurewiczStability

variable {π : Nat → Type u} {H : Nat → Type v} (HS : HurewiczStability π H)

theorem naturality_eq (n : Nat) (x : π n) :
    HS.hurewicz (n+1) (HS.stab_π n x) = HS.stab_H n (HS.hurewicz n x) :=
  (HS.naturality n x).toEq

/-- Double naturality. -/
noncomputable def double_naturality (n : Nat) (x : π n) :
    Path (HS.hurewicz (n+2) (HS.stab_π (n+1) (HS.stab_π n x)))
         (HS.stab_H (n+1) (HS.stab_H n (HS.hurewicz n x))) :=
  Path.trans (HS.naturality (n+1) (HS.stab_π n x))
    (congrArg (HS.stab_H (n+1)) (HS.naturality n x))

theorem double_naturality_eq (n : Nat) (x : π n) :
    HS.hurewicz (n+2) (HS.stab_π (n+1) (HS.stab_π n x)) =
    HS.stab_H (n+1) (HS.stab_H n (HS.hurewicz n x)) :=
  (HS.double_naturality n x).toEq

end HurewiczStability

end Algebra
end Path
end ComputationalPaths
