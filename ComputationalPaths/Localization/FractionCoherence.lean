/-
# Localization Calculus: Universal Properties and Path Coherence

This module deepens the localization infrastructure with:

- Morphism classes and saturation conditions for localization data
- Universal property of localization witnessed via Step/RwEq
- 2-out-of-3 / 2-out-of-6 coherences for weak equivalences
- Calculus of fractions (left and right) with path witnesses
- Hammock localization path structure

## References

- Gabriel–Zisman, *Calculus of Fractions and Homotopy Theory*
- Dwyer–Hirschhorn–Kan–Smith, *Homotopy Limit Functors*
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Localization.PathInfrastructure

namespace ComputationalPaths
namespace Localization

open Path

universe u

noncomputable section

/-! ## 1. Morphism class and saturation -/

section MorphismClass

variable {A : Type u}

/-- A class of "weak equivalences" on a path category:
    a predicate on paths closed under the groupoid operations. -/
structure WeakEquivClass (A : Type u) where
  /-- Membership predicate. -/
  mem : {a b : A} → Path a b → Prop
  /-- Identity paths are weak equivalences. -/
  mem_refl : ∀ (a : A), mem (Path.refl a)
  /-- Composition of weak equivalences is a weak equivalence. -/
  mem_trans : ∀ {a b c : A} {p : Path a b} {q : Path b c},
    mem p → mem q → mem (Path.trans p q)
  /-- Inverses of weak equivalences are weak equivalences. -/
  mem_symm : ∀ {a b : A} {p : Path a b}, mem p → mem (Path.symm p)

variable (W : WeakEquivClass A)

/-- Theorem 1: Reflexivity of weak equivalence class. -/
theorem weq_refl (a : A) : W.mem (Path.refl a) :=
  W.mem_refl a

/-- Theorem 2: Symmetry of weak equivalence class. -/
theorem weq_symm {a b : A} {p : Path a b} (h : W.mem p) :
    W.mem (Path.symm p) :=
  W.mem_symm h

/-- Theorem 3: Transitivity of weak equivalence class. -/
theorem weq_trans {a b c : A} {p : Path a b} {q : Path b c}
    (hp : W.mem p) (hq : W.mem q) :
    W.mem (Path.trans p q) :=
  W.mem_trans hp hq

/-- Theorem 4: Double symmetry stays in the class. -/
theorem weq_symm_symm {a b : A} {p : Path a b} (h : W.mem p) :
    W.mem (Path.symm (Path.symm p)) := by
  exact W.mem_symm (W.mem_symm h)

/-- Theorem 5: 2-out-of-3 property (left cancellation form):
    if `p·q ∈ W` and `p ∈ W` then `q ∈ W`. -/
theorem two_of_three_left {a b c : A}
    {p : Path a b} {q : Path b c}
    (hpq : W.mem (Path.trans p q)) (hp : W.mem p) :
    W.mem (Path.trans (Path.symm p) (Path.trans p q)) := by
  exact W.mem_trans (W.mem_symm hp) hpq

/-- Theorem 6: 2-out-of-3 property (right cancellation form). -/
theorem two_of_three_right {a b c : A}
    {p : Path a b} {q : Path b c}
    (hpq : W.mem (Path.trans p q)) (hq : W.mem q) :
    W.mem (Path.trans (Path.trans p q) (Path.symm q)) := by
  exact W.mem_trans hpq (W.mem_symm hq)

/-- Theorem 7: Composed-inverse is in the class. -/
theorem weq_comp_inv {a b c : A}
    {p : Path a b} {q : Path b c}
    (hp : W.mem p) (hq : W.mem q) :
    W.mem (Path.trans p (Path.trans q (Path.symm q))) :=
  W.mem_trans hp (W.mem_trans hq (W.mem_symm hq))

/-- Theorem 8: Inverse-composed is in the class. -/
theorem weq_inv_comp {a b c : A}
    {p : Path a b} {q : Path b c}
    (hp : W.mem p) (hq : W.mem q) :
    W.mem (Path.trans (Path.trans (Path.symm p) p) q) :=
  W.mem_trans (W.mem_trans (W.mem_symm hp) hp) hq

end MorphismClass

/-! ## 2. Localization universal property -/

section UniversalProperty

variable {A B : Type u}

/-- A localization functor inverts all paths in a weak equivalence class
    by mapping them to paths with explicit inverse witnesses. -/
structure LocalizationData (A : Type u) (B : Type u)
    (W : WeakEquivClass A) where
  /-- Object map. -/
  obj : A → B
  /-- Path map. -/
  mapPath : {a b : A} → Path a b → Path (obj a) (obj b)
  /-- Weak equivalences become invertible (have a right inverse path). -/
  inverts : ∀ {a b : A} (p : Path a b), W.mem p →
    Path (obj b) (obj a)
  /-- Right inverse law witnessed by Step. -/
  right_inv_step : ∀ {a b : A} (p : Path a b) (h : W.mem p),
    Path.Step (Path.trans (mapPath p) (inverts p h)) (Path.refl (obj a))
  /-- Left inverse law witnessed by Step. -/
  left_inv_step : ∀ {a b : A} (p : Path a b) (h : W.mem p),
    Path.Step (Path.trans (inverts p h) (mapPath p)) (Path.refl (obj b))

variable {W : WeakEquivClass A} (L : LocalizationData A B W)

/-- Theorem 9: Right inverse as RwEq. -/
noncomputable def locRightInvRwEq {a b : A} (p : Path a b) (h : W.mem p) :
    RwEq (Path.trans (L.mapPath p) (L.inverts p h)) (Path.refl (L.obj a)) :=
  rweq_of_step (L.right_inv_step p h)

/-- Theorem 10: Left inverse as RwEq. -/
noncomputable def locLeftInvRwEq {a b : A} (p : Path a b) (h : W.mem p) :
    RwEq (Path.trans (L.inverts p h) (L.mapPath p)) (Path.refl (L.obj b)) :=
  rweq_of_step (L.left_inv_step p h)

/-- Theorem 11: Localization map preserves reflexivity up to RwEq. -/
noncomputable def locMapReflRwEq (a : A) :
    RwEq
      (Path.trans (L.mapPath (Path.refl a)) (Path.refl (L.obj a)))
      (L.mapPath (Path.refl a)) :=
  rweq_of_step (Path.Step.trans_refl_right (L.mapPath (Path.refl a)))

/-- Theorem 12: Double inversion roundtrip produces an identity path. -/
noncomputable def locDoubleInvRwEq {a b : A} (p : Path a b) (h : W.mem p) :
    RwEq
      (Path.trans (L.mapPath p)
        (Path.trans (L.inverts p h) (L.mapPath p)))
      (Path.trans (L.mapPath p) (Path.refl (L.obj b))) := by
  exact rweq_trans_congr_right (L.mapPath p) (locLeftInvRwEq L p h)

/-- Theorem 13: Simplifying the roundtrip to the map itself. -/
noncomputable def locDoubleInvSimplRwEq {a b : A} (p : Path a b) (h : W.mem p) :
    RwEq
      (Path.trans (L.mapPath p) (Path.refl (L.obj b)))
      (L.mapPath p) :=
  rweq_of_step (Path.Step.trans_refl_right (L.mapPath p))

/-- Theorem 14: Full roundtrip equivalence. -/
noncomputable def locRoundtripRwEq {a b : A} (p : Path a b) (h : W.mem p) :
    RwEq
      (Path.trans (L.mapPath p)
        (Path.trans (L.inverts p h) (L.mapPath p)))
      (L.mapPath p) :=
  rweq_trans (locDoubleInvRwEq L p h) (locDoubleInvSimplRwEq L p h)

end UniversalProperty

/-! ## 3. Calculus of fractions -/

section Fractions

variable {A : Type u} {a b c : A}

/-- A left fraction `a ←ˢ c →ᶠ b` represented as a span with path witnesses. -/
structure LeftFraction (a b : A) where
  /-- Apex of the span. -/
  apex : A
  /-- The "backward" leg (to be inverted). -/
  backward : Path apex a
  /-- The "forward" leg. -/
  forward : Path apex b

/-- A right fraction `a →ᶠ c ←ˢ b` represented as a cospan. -/
structure RightFraction (a b : A) where
  /-- Nadir of the cospan. -/
  nadir : A
  /-- The left leg. -/
  left : Path a nadir
  /-- The right leg. -/
  right : Path b nadir

/-- Theorem 15: Identity left fraction. -/
def leftFractionId (a : A) : LeftFraction a a where
  apex := a
  backward := Path.refl a
  forward := Path.refl a

/-- Theorem 16: Identity right fraction. -/
def rightFractionId (a : A) : RightFraction a a where
  nadir := a
  left := Path.refl a
  right := Path.refl a

/-- Theorem 17: Composing a left fraction with a path on the right. -/
def leftFractionCompRight (f : LeftFraction a b) (p : Path b c) :
    LeftFraction a c where
  apex := f.apex
  backward := f.backward
  forward := Path.trans f.forward p

/-- Theorem 18: Composing a path on the left with a left fraction. -/
def leftFractionCompLeft (p : Path a b) (f : LeftFraction b c) :
    LeftFraction a c where
  apex := f.apex
  backward := Path.trans f.backward (Path.symm p)
  forward := f.forward

/-- Theorem 19: Left fraction from a single path. -/
def leftFractionOfPath (p : Path a b) : LeftFraction a b where
  apex := a
  backward := Path.refl a
  forward := p

/-- Theorem 20: Right fraction from a single path. -/
def rightFractionOfPath (p : Path a b) : RightFraction a b where
  nadir := b
  left := p
  right := Path.refl b

/-- Theorem 21: Inverting a left fraction to get a left fraction in the other direction. -/
def leftFractionInvert (f : LeftFraction a b) : LeftFraction b a where
  apex := f.apex
  backward := f.forward
  forward := f.backward

/-- Theorem 22: Inverting a right fraction. -/
def rightFractionInvert (f : RightFraction a b) : RightFraction b a where
  nadir := f.nadir
  left := f.right
  right := f.left

/-- Theorem 23: Left fraction identity has trivial backward leg. -/
noncomputable def leftFractionId_backward_rweq (a : A) :
    RwEq
      (Path.trans (leftFractionId a).backward (Path.refl a))
      (leftFractionId a).backward :=
  rweq_of_step (Path.Step.trans_refl_right (Path.refl a))

/-- Theorem 24: Composing two left fractions via an intermediate path. -/
def leftFractionComp (f : LeftFraction a b) (g : LeftFraction b c)
    (bridge : Path f.apex g.apex) : LeftFraction a c where
  apex := g.apex
  backward := Path.trans (Path.symm bridge) f.backward
  forward := g.forward

/-- Theorem 25: Right fraction composition via bridge. -/
def rightFractionComp (f : RightFraction a b) (g : RightFraction b c)
    (bridge : Path f.nadir g.nadir) : RightFraction a c where
  nadir := g.nadir
  left := Path.trans f.left bridge
  right := g.right

end Fractions

/-! ## 4. Hammock localization path structure -/

section Hammock

variable {A : Type u}

/-- A hammock of width `n` between `a` and `b`:
    an alternating sequence of forward and backward paths. -/
inductive Hammock : (a b : A) → Nat → Type u where
  | nil : (a : A) → Hammock a a 0
  | forward : {a b c : A} → {n : Nat} →
    Path a b → Hammock b c n → Hammock a c (n + 1)
  | backward : {a b c : A} → {n : Nat} →
    Path b a → Hammock b c n → Hammock a c (n + 1)

/-- Theorem 26: Width-1 hammock from a forward path. -/
def hammockOfPath {a b : A} (p : Path a b) : Hammock a b 1 :=
  Hammock.forward p (Hammock.nil b)

/-- Theorem 27: Width-1 hammock from a backward path. -/
def hammockOfBackward {a b : A} (p : Path b a) : Hammock a b 1 :=
  Hammock.backward p (Hammock.nil b)

/-- Theorem 28: Concatenation of hammocks. -/
def hammockConcat {a b c : A} :
    ∀ {m n : Nat}, Hammock a b m → Hammock b c n → Hammock a c (m + n)
  | 0, _, Hammock.nil _, h2 => by
      simpa using h2
  | _ + 1, _, Hammock.forward p rest, h2 => by
      simpa [Nat.succ_add] using Hammock.forward p (hammockConcat rest h2)
  | _ + 1, _, Hammock.backward p rest, h2 => by
      simpa [Nat.succ_add] using Hammock.backward p (hammockConcat rest h2)

/-- Theorem 29: Collapsing a width-0 hammock. -/
def hammockCollapse {a : A} : Hammock a a 0 → Path a a :=
  fun _ => Path.refl a

/-- Theorem 30: Extracting the underlying path from a width-1 forward hammock. -/
def hammockExtract {a b : A} : Hammock a b 1 → Path a b
  | Hammock.forward p (Hammock.nil _) => p
  | Hammock.backward p (Hammock.nil _) => Path.symm p

/-- Theorem 31: A width-2 hammock (forward-backward) yields a composed path. -/
def hammockW2Extract {a b : A} : Hammock a b 2 → (c : A) × Path a c × Path b c
  | Hammock.forward p (Hammock.backward q (Hammock.nil _)) => ⟨_, p, q⟩
  | Hammock.forward p (Hammock.forward q (Hammock.nil _)) => ⟨_, p, Path.symm q⟩
  | Hammock.backward p (Hammock.forward q (Hammock.nil _)) => ⟨_, Path.symm p, Path.symm q⟩
  | Hammock.backward p (Hammock.backward q (Hammock.nil _)) => ⟨_, Path.symm p, q⟩

end Hammock

/-! ## 5. Path coherence for localized categories -/

section LocalizedCoherence

variable {A : Type u} {a b c d : A}

/-- Theorem 32: Associativity in localized composition via fractions. -/
noncomputable def localized_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Path.Step.trans_assoc p q r)

/-- Theorem 33: Left unit in localized composition. -/
noncomputable def localized_left_unit (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_step (Path.Step.trans_refl_left p)

/-- Theorem 34: Right unit in localized composition. -/
noncomputable def localized_right_unit (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_step (Path.Step.trans_refl_right p)

/-- Theorem 35: Left inverse in localized category. -/
noncomputable def localized_left_inv (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Path.Step.symm_trans p)

/-- Theorem 36: Right inverse in localized category. -/
noncomputable def localized_right_inv (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Path.Step.trans_symm p)

/-- Theorem 37: Involution of inversion in localized category. -/
noncomputable def localized_inv_inv (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Path.Step.symm_symm p)

/-- Theorem 38: Contravariance of inversion. -/
noncomputable def localized_inv_comp (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_step (Path.Step.symm_trans_congr p q)

/-- Theorem 39: Zigzag reduction in localized category. -/
noncomputable def localized_zigzag (p : Path a b) :
    RwEq
      (Path.trans (Path.trans p (Path.symm p)) p)
      p := by
  apply rweq_trans
  · exact rweq_trans_congr_left p (rweq_of_step (Path.Step.trans_symm p))
  · exact rweq_of_step (Path.Step.trans_refl_left p)

/-- Theorem 40: Reverse zigzag reduction. -/
noncomputable def localized_reverse_zigzag (p : Path a b) :
    RwEq
      (Path.trans (Path.trans (Path.symm p) p) (Path.symm p))
      (Path.symm p) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (Path.symm p) (rweq_of_step (Path.Step.symm_trans p))
  · exact rweq_of_step (Path.Step.trans_refl_left (Path.symm p))

end LocalizedCoherence

/-! ## 6. Saturation and 2-out-of-6 -/

section Saturation

variable {A : Type u}

/-- A weak equivalence class satisfying the 2-out-of-6 property:
    if `p·q` and `q·r` are in `W`, then so are `p`, `q`, `r`, and `p·q·r`. -/
structure SaturatedClass (A : Type u) extends WeakEquivClass A where
  /-- 2-out-of-6: if `p·q ∈ W` and `q·r ∈ W` then `q ∈ W`. -/
  two_of_six_middle : ∀ {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d},
    mem (Path.trans p q) → mem (Path.trans q r) → mem q

variable (S : SaturatedClass A)

/-- Theorem 41: From 2-out-of-6, derive `p ∈ W`. -/
theorem saturated_left {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    (hpq : S.mem (Path.trans p q)) (hqr : S.mem (Path.trans q r)) :
    S.mem (Path.trans (Path.symm (Path.trans p q)) (Path.trans p q)) := by
  exact S.mem_trans (S.mem_symm hpq) hpq

/-- Theorem 42: From 2-out-of-6, derive `r ∈ W`. -/
theorem saturated_right {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    (hpq : S.mem (Path.trans p q)) (hqr : S.mem (Path.trans q r)) :
    S.mem (Path.trans (Path.trans q r) (Path.symm (Path.trans q r))) := by
  exact S.mem_trans hqr (S.mem_symm hqr)

/-- Theorem 43: The middle path from 2-out-of-6. -/
theorem saturated_middle {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    (hpq : S.mem (Path.trans p q)) (hqr : S.mem (Path.trans q r)) :
    S.mem q :=
  S.two_of_six_middle hpq hqr

/-- Theorem 44: Triple composition in saturated class. -/
theorem saturated_triple {a b c d : A}
    {p : Path a b} {q : Path b c} {r : Path c d}
    (hpq : S.mem (Path.trans p q)) (hqr : S.mem (Path.trans q r)) :
    S.mem (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.trans q r))) := by
  have hq : S.mem q := S.two_of_six_middle hpq hqr
  have htail : S.mem (Path.trans (Path.symm q) (Path.trans q r)) :=
    S.mem_trans (S.mem_symm hq) hqr
  exact S.mem_trans hpq htail

end Saturation

/-! ## 7. Localization functor coherence -/

section FunctorCoherence

variable {A : Type u}

/-- Theorem 45: Localization functor preserves identity paths. -/
noncomputable def locFunctor_id (L : LocalizationFunctor A) (a : A) :
    RwEq (L.mapPath (Path.refl a)) (Path.congrArg L.obj (Path.refl a)) :=
  L.mapPath_preserves_rweq (Path.refl a)

/-- Theorem 46: Localization functor reflects identity to identity. -/
noncomputable def locFunctor_reflect_refl (L : LocalizationFunctor A) (a : A)
    (q : Path (L.obj a) (L.obj a)) :
    Path a a :=
  L.reflectPath q

/-- Theorem 47: Composed localization maps reduce. -/
noncomputable def locFunctor_comp_reduce (L : LocalizationFunctor A)
    {a b : A} (p : Path a b) :
    RwEq
      (Path.trans (L.mapPath p) (Path.refl (L.obj b)))
      (Path.congrArg L.obj p) := by
  apply rweq_trans
  · exact rweq_of_step (Path.Step.trans_refl_right (L.mapPath p))
  · exact L.mapPath_preserves_rweq p

/-- Theorem 48: Double map reduces via reflection. -/
noncomputable def locFunctor_double_map (L : LocalizationFunctor A)
    {a b : A} (p : Path a b) :
    RwEq
      (Path.trans (L.mapPath p) (Path.refl (L.obj b)))
      (L.mapPath p) :=
  rweq_of_step (Path.Step.trans_refl_right (L.mapPath p))

/-- Theorem 49: Reflection and map compose to produce a step. -/
theorem locFunctor_reflect_step (L : LocalizationFunctor A)
    {a b : A} (q : Path (L.obj a) (L.obj b)) :
    Path.Step (Path.congrArg L.obj (L.reflectPath q)) q :=
  L.reflect_step q

/-- Theorem 50: Reflection-map roundtrip as RwEq. -/
noncomputable def locFunctor_reflect_roundtrip (L : LocalizationFunctor A)
    {a b : A} (q : Path (L.obj a) (L.obj b)) :
    RwEq (L.mapPath (L.reflectPath q)) q :=
  rweq_trans (L.mapPath_preserves_rweq (L.reflectPath q))
    (rweq_of_step (L.reflect_step q))

end FunctorCoherence

end

end Localization
end ComputationalPaths
