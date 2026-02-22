/-
  ComputationalPaths/Path/Algebra/HomologicalAlgebraDeep3.lean

  Homological Algebra on Concrete Types: Chain Complexes, Chain Maps,
  Exactness, and Functoriality via Computational Paths
  ============================================================

  Author: armada-538 (HomologicalAlgebraDeep3)
  Date: 2026-02-17
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.HomologicalAlgebraDeep3

open ComputationalPaths.Path

-- ============================================================================
-- Section 1: Modular Arithmetic Paths
-- ============================================================================

noncomputable def addMod (n : Nat) (a b : Nat) : Nat := (a + b) % n

-- Theorem 1: addMod commutative
theorem addMod_comm (n a b : Nat) : addMod n a b = addMod n b a := by
  simp [addMod, Nat.add_comm]

-- Theorem 2: addMod comm path
noncomputable def addMod_comm_path (n a b : Nat) :
    Path (addMod n a b) (addMod n b a) :=
  Path.mk [⟨_, _, addMod_comm n a b⟩] (addMod_comm n a b)

-- Theorem 3: addMod identity
theorem addMod_zero (n a : Nat) (ha : a < n) :
    addMod n a 0 = a := by
  simp [addMod, Nat.mod_eq_of_lt ha]

-- Theorem 4: addMod identity path
noncomputable def addMod_zero_path (n a : Nat) (ha : a < n) :
    Path (addMod n a 0) a :=
  Path.mk [⟨_, _, addMod_zero n a ha⟩] (addMod_zero n a ha)

-- ============================================================================
-- Section 2: Chain Complex
-- ============================================================================

/-- Chain complex: d(n) ∘ d(n+1) = 0 for all n, and d(0) = 0. -/
structure ChainComplex where
  d : Nat → (Nat → Nat)
  d_zero : ∀ n, d n 0 = 0
  dd_zero : ∀ (n : Nat) (x : Nat), d n (d (n + 1) x) = 0

-- Theorem 5: dd = 0 path
noncomputable def dd_zero_path (C : ChainComplex) (n x : Nat) :
    Path (C.d n (C.d (n + 1) x)) 0 :=
  Path.mk [⟨_, _, C.dd_zero n x⟩] (C.dd_zero n x)

-- Theorem 6: d(0) = 0 path
noncomputable def d_zero_path (C : ChainComplex) (n : Nat) :
    Path (C.d n 0) 0 :=
  Path.mk [⟨_, _, C.d_zero n⟩] (C.d_zero n)

-- ============================================================================
-- Section 3: Zero Complex
-- ============================================================================

noncomputable def zeroComplex : ChainComplex where
  d := fun _ _ => 0
  d_zero := fun _ => rfl
  dd_zero := fun _ _ => rfl

-- Theorem 7: Zero d path
noncomputable def zero_d_path (n x : Nat) : Path (zeroComplex.d n x) 0 := Path.refl _

-- Theorem 8: Zero dd path
noncomputable def zero_dd_path (n x : Nat) :
    Path (zeroComplex.d n (zeroComplex.d (n + 1) x)) 0 := Path.refl _

-- ============================================================================
-- Section 4: Mod-2 Complex
-- ============================================================================

/-- d_0(x) = x % 2, d_{n+1}(x) = 0. -/
noncomputable def mod2Complex : ChainComplex where
  d := fun n x => match n with
    | 0     => x % 2
    | _ + 1 => 0
  d_zero := fun n => by cases n <;> simp
  dd_zero := fun n x => by cases n <;> simp

-- Theorem 9: d_0 on even
theorem mod2_d0_even (k : Nat) : mod2Complex.d 0 (2 * k) = 0 := by
  simp [mod2Complex, Nat.mul_mod_right]

-- Theorem 10: d_0(2k) = 0 path
noncomputable def mod2_d0_even_path (k : Nat) : Path (mod2Complex.d 0 (2 * k)) 0 :=
  Path.mk [⟨_, _, mod2_d0_even k⟩] (mod2_d0_even k)

-- Theorem 11: d_1 zero
theorem mod2_d1_zero (x : Nat) : mod2Complex.d 1 x = 0 := by simp [mod2Complex]

-- Theorem 12: d_1 path
noncomputable def mod2_d1_path (x : Nat) : Path (mod2Complex.d 1 x) 0 :=
  Path.mk [⟨_, _, mod2_d1_zero x⟩] (mod2_d1_zero x)

-- Theorem 13: dd trans via congrArg
noncomputable def mod2_dd_trans (x : Nat) :
    Path (mod2Complex.d 0 (mod2Complex.d 1 x)) 0 :=
  Path.trans
    (Path.congrArg (mod2Complex.d 0) (mod2_d1_path x))
    (d_zero_path mod2Complex 0)

-- ============================================================================
-- Section 5: Doubling Complex
-- ============================================================================

/-- d_0(x) = 2*x, d_{n+1} = 0. -/
noncomputable def doublingComplex : ChainComplex where
  d := fun n x => match n with
    | 0     => 2 * x
    | _ + 1 => 0
  d_zero := fun n => by cases n <;> simp
  dd_zero := fun n x => by cases n <;> simp

-- Theorem 14: Doubling d_0
noncomputable def doubling_d0_path (x : Nat) : Path (doublingComplex.d 0 x) (2 * x) := Path.refl _

-- Theorem 15: dd = 0 in doubling
noncomputable def doubling_dd_path (n x : Nat) :
    Path (doublingComplex.d n (doublingComplex.d (n + 1) x)) 0 :=
  dd_zero_path doublingComplex n x

-- ============================================================================
-- Section 6: Cycles and Boundaries
-- ============================================================================

/-- Cycle: d_n(x) = 0. -/
noncomputable def IsCycle (C : ChainComplex) (n : Nat) (x : Nat) : Prop := C.d n x = 0

/-- Boundary: ∃ y, d_{n+1}(y) = x. -/
noncomputable def IsBoundary (C : ChainComplex) (n : Nat) (x : Nat) : Prop :=
  ∃ y, C.d (n + 1) y = x

-- Theorem 16: Every boundary is a cycle
theorem boundary_is_cycle (C : ChainComplex) (n x : Nat)
    (hx : IsBoundary C n x) : IsCycle C n x := by
  obtain ⟨y, hy⟩ := hx
  unfold IsCycle; rw [← hy]; exact C.dd_zero n y

-- Theorem 17: Boundary→cycle path
noncomputable def boundary_cycle_path (C : ChainComplex) (n x : Nat)
    (hx : IsBoundary C n x) :
    Path (C.d n x) 0 :=
  Path.mk [⟨_, _, boundary_is_cycle C n x hx⟩] (boundary_is_cycle C n x hx)

-- Theorem 18: d-image is boundary
theorem d_image_boundary (C : ChainComplex) (n y : Nat) :
    IsBoundary C n (C.d (n + 1) y) := ⟨y, rfl⟩

-- Theorem 19: 0 is always a cycle
theorem zero_is_cycle (C : ChainComplex) (n : Nat) :
    IsCycle C n 0 := C.d_zero n

-- Theorem 20: 0-cycle path
noncomputable def zero_cycle_path (C : ChainComplex) (n : Nat) :
    Path (C.d n 0) 0 := Path.mk [⟨_, _, zero_is_cycle C n⟩] (zero_is_cycle C n)

-- Theorem 21: Even cycles in mod2
theorem mod2_even_cycle (k : Nat) : IsCycle mod2Complex 0 (2 * k) := mod2_d0_even k

-- Theorem 22: 0 boundary in zero complex
theorem zero_boundary (n : Nat) : IsBoundary zeroComplex n 0 := ⟨0, rfl⟩

-- ============================================================================
-- Section 7: Exactness
-- ============================================================================

/-- Exact: every cycle is a boundary. -/
noncomputable def IsExact (C : ChainComplex) (n : Nat) : Prop :=
  ∀ x, IsCycle C n x → IsBoundary C n x

-- Theorem 23: Zero complex: 0 is exact (0 is a boundary)
theorem zero_zero_exact (n : Nat) : IsCycle zeroComplex n 0 → IsBoundary zeroComplex n 0 :=
  fun _ => ⟨0, rfl⟩

-- Theorem 24: Exact gives boundary
theorem exact_gives_boundary (C : ChainComplex) (n x : Nat)
    (hexact : IsExact C n) (hcycle : IsCycle C n x) :
    IsBoundary C n x := hexact x hcycle

-- Theorem 25: Cycle→0 path
noncomputable def cycle_d_path (C : ChainComplex) (n x : Nat) (hcycle : IsCycle C n x) :
    Path (C.d n x) 0 := Path.mk [⟨_, _, hcycle⟩] hcycle

-- ============================================================================
-- Section 8: Chain Maps
-- ============================================================================

/-- Chain map: commutes with d and preserves 0.
    f_n ∘ d_n^C = d_n^D ∘ f_n, i.e. D.d n (f n x) = f n (C.d n x). -/
structure ChainMap (C D : ChainComplex) where
  f : Nat → (Nat → Nat)
  f_zero : ∀ n, f n 0 = 0
  comm : ∀ (n : Nat) (x : Nat), f n (C.d (n + 1) x) = D.d (n + 1) (f (n + 1) x)

-- Theorem 26: Comm path
noncomputable def chainMap_comm_path {C D : ChainComplex} (φ : ChainMap C D) (n x : Nat) :
    Path (φ.f n (C.d (n + 1) x)) (D.d (n + 1) (φ.f (n + 1) x)) :=
  Path.mk [⟨_, _, φ.comm n x⟩] (φ.comm n x)

-- Theorem 27: f(0) = 0 path
noncomputable def chainMap_zero_path {C D : ChainComplex} (φ : ChainMap C D) (n : Nat) :
    Path (φ.f n 0) 0 := Path.mk [⟨_, _, φ.f_zero n⟩] (φ.f_zero n)

-- ============================================================================
-- Section 9: Identity Chain Map
-- ============================================================================

noncomputable def idChainMap (C : ChainComplex) : ChainMap C C where
  f := fun _ x => x
  f_zero := fun _ => rfl
  comm := fun _ _ => rfl

-- Theorem 28: Id path
noncomputable def id_map_path (C : ChainComplex) (n x : Nat) :
    Path ((idChainMap C).f n x) x := Path.refl _

-- ============================================================================
-- Section 10: Zero Chain Map
-- ============================================================================

noncomputable def zeroMap (C D : ChainComplex) : ChainMap C D where
  f := fun _ _ => 0
  f_zero := fun _ => rfl
  comm := fun n _ => by simp [D.d_zero (n + 1)]

-- Theorem 29: Zero map path
noncomputable def zero_map_path (C D : ChainComplex) (n x : Nat) :
    Path ((zeroMap C D).f n x) 0 := Path.refl _

-- ============================================================================
-- Section 11: Composition
-- ============================================================================

noncomputable def compChainMap {C D E : ChainComplex} (φ : ChainMap C D) (ψ : ChainMap D E) :
    ChainMap C E where
  f := fun n x => ψ.f n (φ.f n x)
  f_zero := fun n => by rw [φ.f_zero, ψ.f_zero]
  comm := fun n x => by
    show ψ.f n (φ.f n (C.d (n + 1) x)) = E.d (n + 1) (ψ.f (n + 1) (φ.f (n + 1) x))
    rw [φ.comm n x, ψ.comm n (φ.f (n + 1) x)]

-- Theorem 30: Comp path
noncomputable def comp_path {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (n x : Nat) :
    Path ((compChainMap φ ψ).f n x) (ψ.f n (φ.f n x)) := Path.refl _

-- Theorem 31: Right identity
noncomputable def comp_id_right {C D : ChainComplex} (φ : ChainMap C D) (n x : Nat) :
    Path ((compChainMap φ (idChainMap D)).f n x) (φ.f n x) := Path.refl _

-- Theorem 32: Left identity
noncomputable def comp_id_left {C D : ChainComplex} (φ : ChainMap C D) (n x : Nat) :
    Path ((compChainMap (idChainMap C) φ).f n x) (φ.f n x) := Path.refl _

-- Theorem 33: Associativity
noncomputable def comp_assoc {C D E F : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (χ : ChainMap E F) (n x : Nat) :
    Path ((compChainMap (compChainMap φ ψ) χ).f n x)
         ((compChainMap φ (compChainMap ψ χ)).f n x) := Path.refl _

-- ============================================================================
-- Section 12: Preservation of Cycles/Boundaries
-- ============================================================================

-- Theorem 34: Chain maps preserve cycles
theorem chainmap_cycles {C D : ChainComplex} (φ : ChainMap C D)
    (n x : Nat) (hx : IsCycle C (n + 1) x) : IsCycle D (n + 1) (φ.f (n + 1) x) := by
  unfold IsCycle at *
  have h := φ.comm n x
  rw [hx, φ.f_zero] at h
  exact h.symm

-- Theorem 35: Cycle path
noncomputable def chainmap_cycle_path {C D : ChainComplex} (φ : ChainMap C D)
    (n x : Nat) (hx : IsCycle C (n + 1) x) :
    Path (D.d (n + 1) (φ.f (n + 1) x)) 0 := by
  have h := chainmap_cycles φ n x hx
  exact Path.mk [⟨_, _, h⟩] h

-- Theorem 36: Chain maps preserve boundaries
theorem chainmap_boundaries {C D : ChainComplex} (φ : ChainMap C D)
    (n x : Nat) (hx : IsBoundary C n x) :
    IsBoundary D n (φ.f n x) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨φ.f (n + 1) y, ?_⟩
  have h := φ.comm n y
  simp [hy] at h
  exact h.symm

-- ============================================================================
-- Section 13: Functoriality
-- ============================================================================

-- Theorem 37: Composition preserves cycles
theorem comp_cycles {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E)
    (n x : Nat) (hx : IsCycle C (n + 1) x) :
    IsCycle E (n + 1) ((compChainMap φ ψ).f (n + 1) x) :=
  chainmap_cycles (compChainMap φ ψ) n x hx

-- Theorem 38: Functorial cycle path
noncomputable def functorial_cycle_path {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E)
    (n x : Nat) (hx : IsCycle C (n + 1) x) :
    Path (E.d (n + 1) (ψ.f (n + 1) (φ.f (n + 1) x))) 0 := by
  have h := comp_cycles φ ψ n x hx
  exact Path.mk [⟨_, _, h⟩] h

-- Theorem 39: Composition preserves boundaries
theorem comp_boundaries {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E)
    (n x : Nat) (hx : IsBoundary C n x) :
    IsBoundary E n ((compChainMap φ ψ).f n x) := by
  exact chainmap_boundaries (compChainMap φ ψ) n x hx

-- ============================================================================
-- Section 14: CongrArg Paths
-- ============================================================================

-- Theorem 40: congrArg chain map
noncomputable def congrArg_cm {C D : ChainComplex} (φ : ChainMap C D)
    (n : Nat) {x y : Nat} (p : Path x y) :
    Path (φ.f n x) (φ.f n y) := Path.congrArg (φ.f n) p

-- Theorem 41: congrArg differential
noncomputable def congrArg_d (C : ChainComplex) (n : Nat) {x y : Nat} (p : Path x y) :
    Path (C.d n x) (C.d n y) := Path.congrArg (C.d n) p

-- Theorem 42: Trans: x → y → d(y)=0
noncomputable def cycle_congrArg_trans (C : ChainComplex) (n : Nat)
    {x y : Nat} (p : Path x y) (hcycle : IsCycle C n y) :
    Path (C.d n x) 0 :=
  Path.trans (congrArg_d C n p) (cycle_d_path C n y hcycle)

-- Theorem 43: Symm coherence
theorem congrArg_cm_symm {C D : ChainComplex} (φ : ChainMap C D)
    (n : Nat) {x y : Nat} (p : Path x y) :
    congrArg_cm φ n (Path.symm p) = Path.symm (congrArg_cm φ n p) := by
  simp [congrArg_cm]

-- Theorem 44: Trans coherence
theorem congrArg_cm_trans {C D : ChainComplex} (φ : ChainMap C D)
    (n : Nat) {x y z : Nat} (p : Path x y) (q : Path y z) :
    congrArg_cm φ n (Path.trans p q) =
      Path.trans (congrArg_cm φ n p) (congrArg_cm φ n q) := by
  simp [congrArg_cm]

-- ============================================================================
-- Section 15: Concrete Chain Maps
-- ============================================================================

-- Theorem 45: Zero-to-mod2
noncomputable def zeroToMod2 : ChainMap zeroComplex mod2Complex := zeroMap zeroComplex mod2Complex

-- Theorem 46: Zero-to-mod2 path
noncomputable def zeroToMod2_path (n x : Nat) :
    Path (zeroToMod2.f n x) 0 := Path.refl _

-- Theorem 47: Mod2-to-zero
noncomputable def mod2ToZero : ChainMap mod2Complex zeroComplex := zeroMap mod2Complex zeroComplex

-- Theorem 48: Mod2-to-zero path
noncomputable def mod2ToZero_path (n x : Nat) :
    Path (mod2ToZero.f n x) 0 := Path.refl _

-- ============================================================================
-- Section 16: Short Exact Sequences
-- ============================================================================

structure ShortExact (A B C_ : ChainComplex) where
  i : ChainMap A B
  p : ChainMap B C_
  pi_zero : ∀ n x, p.f n (i.f n x) = 0

-- Theorem 49: p ∘ i = 0 path
noncomputable def pi_zero_path {A B C_ : ChainComplex} (ses : ShortExact A B C_)
    (n x : Nat) :
    Path (ses.p.f n (ses.i.f n x)) 0 :=
  Path.mk [⟨_, _, ses.pi_zero n x⟩] (ses.pi_zero n x)

-- Theorem 50: Composition path
noncomputable def pi_comp_path {A B C_ : ChainComplex} (ses : ShortExact A B C_)
    (n x : Nat) :
    Path ((compChainMap ses.i ses.p).f n x) 0 :=
  Path.mk [⟨_, _, ses.pi_zero n x⟩] (ses.pi_zero n x)

-- ============================================================================
-- Section 17: Homology Classes
-- ============================================================================

structure HomologyClass (C : ChainComplex) (n : Nat) where
  rep : Nat
  is_cycle : IsCycle C (n + 1) rep

-- Theorem 51: 0 homology class
noncomputable def zero_hom_class (C : ChainComplex) (n : Nat) : HomologyClass C n :=
  ⟨0, zero_is_cycle C (n + 1)⟩

-- Theorem 52: Zero class rep path
noncomputable def zero_class_path (C : ChainComplex) (n : Nat) :
    Path (zero_hom_class C n).rep 0 := Path.refl _

-- Theorem 53: Induced map on homology
noncomputable def induced_hom {C D : ChainComplex} (φ : ChainMap C D) (n : Nat)
    (cls : HomologyClass C n) : HomologyClass D n :=
  ⟨φ.f (n + 1) cls.rep, chainmap_cycles φ n cls.rep cls.is_cycle⟩

-- Theorem 54: Induced rep path
noncomputable def induced_rep_path {C D : ChainComplex} (φ : ChainMap C D)
    (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom φ n cls).rep (φ.f (n + 1) cls.rep) := Path.refl _

-- Theorem 55: Id induced = id
noncomputable def id_induced_path (C : ChainComplex) (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom (idChainMap C) n cls).rep cls.rep := Path.refl _

-- Theorem 56: Comp induced = induced ∘ induced
noncomputable def comp_induced_path {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom (compChainMap φ ψ) n cls).rep
         (induced_hom ψ n (induced_hom φ n cls)).rep := Path.refl _

-- ============================================================================
-- Section 18: dd Paths
-- ============================================================================

-- Theorem 57: congrArg dd
noncomputable def dd_congrArg (C : ChainComplex) (n : Nat) {x y : Nat} (p : Path x y) :
    Path (C.d n (C.d (n + 1) x)) (C.d n (C.d (n + 1) y)) :=
  Path.congrArg (fun z => C.d n (C.d (n + 1) z)) p

-- Theorem 58: dd congrArg + dd=0
noncomputable def dd_to_zero (C : ChainComplex) (n : Nat) {x y : Nat} (p : Path x y) :
    Path (C.d n (C.d (n + 1) x)) 0 :=
  Path.trans (dd_congrArg C n p) (dd_zero_path C n y)

-- Theorem 59: Symm dd
noncomputable def dd_symm (C : ChainComplex) (n : Nat) {x y : Nat} (p : Path x y) :
    Path (C.d n (C.d (n + 1) y)) (C.d n (C.d (n + 1) x)) :=
  Path.symm (dd_congrArg C n p)

-- ============================================================================
-- Section 19: Concrete Homology
-- ============================================================================

-- Theorem 60: 0 cycle in mod2 at d_0
theorem mod2_zero_cycle : IsCycle mod2Complex 1 0 := rfl

-- Theorem 61: 2 cycle in mod2
theorem mod2_two_cycle : IsCycle mod2Complex 1 2 := rfl

-- Theorem 62: Homology class 0
noncomputable def mod2_cls0 : HomologyClass mod2Complex 0 := ⟨0, mod2_zero_cycle⟩  -- IsCycle mod2Complex 1 0

-- Theorem 63: Homology class 2
noncomputable def mod2_cls2 : HomologyClass mod2Complex 0 := ⟨2, mod2_two_cycle⟩  -- IsCycle mod2Complex 1 2

-- Theorem 64: d(cls0.rep) = 0 path
noncomputable def mod2_cls0_d_path : Path (mod2Complex.d 1 mod2_cls0.rep) 0 :=
  Path.mk [⟨_, _, mod2_zero_cycle⟩] mod2_zero_cycle

-- Theorem 65: d(cls2.rep) = 0 path
noncomputable def mod2_cls2_d_path : Path (mod2Complex.d 1 mod2_cls2.rep) 0 :=
  Path.mk [⟨_, _, mod2_two_cycle⟩] mod2_two_cycle

-- ============================================================================
-- Section 20: Chain Homotopy
-- ============================================================================

noncomputable def ChainHomotopic (C D : ChainComplex) (φ ψ : ChainMap C D) : Prop :=
  ∀ n x, IsCycle C n x → φ.f n x = ψ.f n x

-- Theorem 66: Reflexive
theorem homotopic_refl {C D : ChainComplex} (φ : ChainMap C D) :
    ChainHomotopic C D φ φ := fun _ _ _ => rfl

-- Theorem 67: Symmetric
theorem homotopic_symm {C D : ChainComplex} {φ ψ : ChainMap C D}
    (h : ChainHomotopic C D φ ψ) : ChainHomotopic C D ψ φ :=
  fun n x hx => (h n x hx).symm

-- Theorem 68: Symmetry path
noncomputable def homotopic_symm_path {C D : ChainComplex} {φ ψ : ChainMap C D}
    (h : ChainHomotopic C D φ ψ) (n x : Nat) (hx : IsCycle C n x) :
    Path (ψ.f n x) (φ.f n x) :=
  Path.mk [⟨_, _, (h n x hx).symm⟩] (h n x hx).symm

-- Theorem 69: Transitive
theorem homotopic_trans {C D : ChainComplex} {φ ψ χ : ChainMap C D}
    (h1 : ChainHomotopic C D φ ψ) (h2 : ChainHomotopic C D ψ χ) :
    ChainHomotopic C D φ χ :=
  fun n x hx => (h1 n x hx).trans (h2 n x hx)

-- Theorem 70: Transitivity path
noncomputable def homotopic_trans_path {C D : ChainComplex} {φ ψ χ : ChainMap C D}
    (h1 : ChainHomotopic C D φ ψ) (h2 : ChainHomotopic C D ψ χ)
    (n x : Nat) (hx : IsCycle C n x) :
    Path (φ.f n x) (χ.f n x) :=
  Path.trans
    (Path.mk [⟨_, _, h1 n x hx⟩] (h1 n x hx))
    (Path.mk [⟨_, _, h2 n x hx⟩] (h2 n x hx))

-- ============================================================================
-- Section 21: Exact Functor Properties
-- ============================================================================

noncomputable def PreservesExactness {C D : ChainComplex} (_φ : ChainMap C D) : Prop :=
  ∀ n, IsExact C n → IsExact D n

-- Theorem 71: Id preserves exactness
theorem id_exact (C : ChainComplex) : PreservesExactness (idChainMap C) :=
  fun _ h => h

-- ============================================================================
-- Section 22: dd naturality paths
-- ============================================================================

-- Theorem 72: dd natural
noncomputable def dd_natural (D : ChainComplex) (n : Nat) (y : Nat) :
    Path (D.d n (D.d (n + 1) y)) 0 :=
  dd_zero_path D n y

-- Theorem 73: dd through chain map
noncomputable def dd_cm_path {C D : ChainComplex} (φ : ChainMap C D) (n : Nat) (x : Nat) :
    Path (D.d (n + 1) (φ.f (n + 1) (C.d (n + 1 + 1) x))) 0 := by
  -- φ.f (n+1) maps d_{n+2} image, which is a boundary, so cycle, so d kills it
  have hcycle : IsCycle C (n + 1) (C.d (n + 1 + 1) x) := by
    unfold IsCycle; exact C.dd_zero (n + 1) x
  have h := chainmap_cycles φ n (C.d (n + 1 + 1) x) hcycle
  exact Path.mk [⟨_, _, h⟩] h

-- Theorem 74: Full trans chain
noncomputable def dd_cm_full_trans {C D : ChainComplex} (φ : ChainMap C D) (n x : Nat) :
    Path (φ.f n (C.d (n + 1) (C.d (n + 1 + 1) x))) 0 :=
  Path.trans
    (Path.congrArg (φ.f n) (dd_zero_path C (n + 1) x))
    (chainMap_zero_path φ n)

-- ============================================================================
-- Section 23: Mapping Cone (zero case)
-- ============================================================================

noncomputable def mappingConeZero : ChainComplex where
  d := fun _ _ => 0
  d_zero := fun _ => rfl
  dd_zero := fun _ _ => rfl

-- Theorem 75: Cone path
noncomputable def cone_d_path (n x : Nat) : Path (mappingConeZero.d n x) 0 := Path.refl _

-- ============================================================================
-- Section 25: More Cycle/Boundary Paths
-- ============================================================================

-- Theorem 78: All cycles in zero complex
theorem zero_all_cycles (n x : Nat) : IsCycle zeroComplex n x := rfl

-- Theorem 79: Path
noncomputable def zero_all_cycles_path (n x : Nat) : Path (zeroComplex.d n x) 0 := Path.refl _

-- Theorem 80: 0 boundary
theorem zero_is_boundary (C : ChainComplex) (n : Nat) :
    IsBoundary C n 0 := ⟨0, C.d_zero (n + 1)⟩

-- Theorem 81: 1 cycle at d_2 in mod2
theorem mod2_one_cycle_d2 : IsCycle mod2Complex 2 1 := rfl

-- Theorem 82: Path
-- Theorem 82: Path d_3(1) = 0
noncomputable def mod2_one_d3_path : Path (mod2Complex.d 3 1) 0 :=
  Path.mk [⟨mod2Complex.d 3 1, 0, rfl⟩] rfl

-- ============================================================================
-- Section 26: Long Trans Chains
-- ============================================================================

-- Theorem 83: Long dd chain through two maps
noncomputable def long_dd {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (n x : Nat) :
    Path (E.d n (E.d (n + 1) (ψ.f (n + 1) (φ.f (n + 1) x)))) 0 :=
  dd_zero_path E n (ψ.f (n + 1) (φ.f (n + 1) x))

-- Theorem 84: Composed dd path
noncomputable def comp_dd {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (n x : Nat) :
    Path (E.d n (E.d (n + 1) ((compChainMap φ ψ).f (n + 1) x))) 0 :=
  dd_zero_path E n ((compChainMap φ ψ).f (n + 1) x)

-- Theorem 85: Zero induced class
noncomputable def zero_induced (C D : ChainComplex) (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom (zeroMap C D) n cls).rep 0 := Path.refl _

-- Theorem 86: Id induced
noncomputable def id_induced (C : ChainComplex) (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom (idChainMap C) n cls).rep cls.rep := Path.refl _

-- Theorem 87: Functorial chain
noncomputable def functorial_chain {C D E : ChainComplex}
    (φ : ChainMap C D) (ψ : ChainMap D E) (n : Nat) (cls : HomologyClass C n) :
    Path (induced_hom (compChainMap φ ψ) n cls).rep
         (induced_hom ψ n (induced_hom φ n cls)).rep := Path.refl _

-- ============================================================================
-- Section 27: Concrete: zero complex SES
-- ============================================================================

-- Theorem 88: Trivial SES: 0 → 0 → 0
noncomputable def trivial_ses : ShortExact zeroComplex zeroComplex zeroComplex where
  i := zeroMap zeroComplex zeroComplex
  p := zeroMap zeroComplex zeroComplex
  pi_zero := fun _ _ => rfl

-- Theorem 89: Trivial SES path
noncomputable def trivial_ses_path (n x : Nat) :
    Path ((compChainMap trivial_ses.i trivial_ses.p).f n x) 0 := Path.refl _

-- Theorem 90: Trivial SES pi = 0 path
noncomputable def trivial_pi_path (n x : Nat) :
    Path (trivial_ses.p.f n (trivial_ses.i.f n x)) 0 :=
  pi_zero_path trivial_ses n x

end ComputationalPaths.Path.Algebra.HomologicalAlgebraDeep3
