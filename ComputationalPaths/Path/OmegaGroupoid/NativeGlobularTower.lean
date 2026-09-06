import ComputationalPaths.Path.OmegaGroupoid.GlobularFoundations

/-!
# A recursive globular extension of the raw computational-path two-skeleton

Dimensions zero through two preserve the actual objects, `Path` traces and
Type-valued `RwEq` derivations. Above dimension two we explicitly adjoin one
cell for each parallel pair, recursively. This is a coskeletal extension,
not a theorem that native higher rewrite syntax is complete or that these
added cells are derivable in that syntax.

No operadic action or weak omega-groupoid theorem is asserted in this file.
The eventual action must still be built and its algebra laws verified.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

namespace NativeTower

/-- Two consecutive levels, with the boundary maps at this stage. -/
structure Stage where
  objects : Type (u + 1)
  arrows : Type (u + 1)
  source : arrows → objects
  target : arrows → objects

/-- The next level consists of parallel pairs at the previous level.
The previous arrows, not a fixed type repeated at every dimension, become
the new objects. -/
def Stage.next (S : Stage.{u}) : Stage.{u} where
  objects := S.arrows
  arrows := Σ p : S.arrows, { q : S.arrows // S.source p = S.source q ∧ S.target p = S.target q }
  source d := d.1
  target d := d.2.1

def Stage.grow (S : Stage.{u}) : Nat → Stage.{u}
  | 0 => S
  | n + 1 => (S.grow n).next

/-- The starting stage retains the entire native two-cell derivation. -/
def base (A : Type u) : Stage.{u} where
  objects := ULift.{u + 1} (PathOne A)
  arrows := PathTwo A
  source d := ULift.up (sourceTwo d)
  target d := ULift.up (targetTwo d)

def Cell (A : Type u) : Nat → Type (u + 1)
  | 0 => ULift.{u + 1} A
  | 1 => ULift.{u + 1} (PathOne A)
  | n + 2 => ((base A).grow n).arrows

def source {A : Type u} : {n : Nat} → Cell A (n + 1) → Cell A n
  | 0, p => ULift.up (sourceOne p.down)
  | 1, p => ULift.up (sourceTwo p)
  | _ + 2, p => p.1

def target {A : Type u} : {n : Nat} → Cell A (n + 1) → Cell A n
  | 0, p => ULift.up (targetOne p.down)
  | 1, p => ULift.up (targetTwo p)
  | _ + 2, p => p.2.1

theorem source_source {A : Type u} {n : Nat} (p : Cell A (n + 2)) :
    source (source p) = source (target p) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact p.2.2.1
    | succ n => exact p.2.2.1

theorem target_source {A : Type u} {n : Nat} (p : Cell A (n + 2)) :
    target (source p) = target (target p) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact p.2.2.2
    | succ n => exact p.2.2.2

def globular (A : Type u) : GlobularSet.{u + 1} where
  Cell := Cell A
  source := source
  target := target
  source_source := source_source
  target_source := target_source

/-- Exact equivalences at all three prescribed native levels. -/
def realizes (A : Type u) : RealizesPathSkeleton (globular A) A where
  objects := Equiv.ulift
  paths := Equiv.ulift
  rewrites := Equiv.refl _
  source_paths _ := rfl
  target_paths _ := rfl
  source_rewrites _ := rfl
  target_rewrites _ := rfl

/-- A chosen, explicitly adjoined three-cell between parallel raw rewrites. -/
def thirdCell {A : Type u} (p q : PathTwo A)
    (hs : sourceTwo p = sourceTwo q) (ht : targetTwo p = targetTwo q) : Cell A 3 :=
  ⟨p, q, _root_.congrArg ULift.up hs, _root_.congrArg ULift.up ht⟩

/-- The explicitly adjoined filler at every dimension above the native
two-skeleton. Its boundary consists of the actual preceding cells. -/
def higherCell {A : Type u} : {n : Nat} → (p q : Cell A (n + 2)) →
    source p = source q → target p = target q → Cell A (n + 3)
  | 0, p, q, hs, ht => ⟨p, q, hs, ht⟩
  | _ + 1, p, q, hs, ht => ⟨p, q, hs, ht⟩

theorem source_higherCell {A : Type u} {n : Nat} (p q : Cell A (n + 2))
    (hs : source p = source q) (ht : target p = target q) :
    source (higherCell p q hs ht) = p := by cases n <;> rfl

theorem target_higherCell {A : Type u} {n : Nat} (p q : Cell A (n + 2))
    (hs : source p = source q) (ht : target p = target q) :
    target (higherCell p q hs ht) = q := by cases n <;> rfl

/-- Semantic limitation: in this chosen extension, cells of dimension at
least three are uniquely determined by their two boundaries. This is not a
claim about the native higher-derivation syntax. -/
theorem higher_ext {A : Type u} {n : Nat} (p q : Cell A (n + 3))
    (hs : source p = source q) (ht : target p = target q) : p = q := by
  rcases p with ⟨p, p', hp⟩
  rcases q with ⟨q, q', hq⟩
  change p = q at hs
  cases hs
  apply _root_.congrArg (Sigma.mk p)
  exact Subtype.ext ht

noncomputable def identity {A : Type u} : {n : Nat} → Cell A n → Cell A (n + 1)
  | 0, a => ULift.up ⟨a.down, a.down, Path.refl a.down⟩
  | 1, p => ⟨p.down.1, p.down.2.1, p.down.2.2, p.down.2.2, RwEq.refl _⟩
  | _ + 2, p => higherCell p p rfl rfl

theorem source_identity {A : Type u} {n : Nat} (p : Cell A n) : source (identity p) = p := by
  cases n with
  | zero => cases p; rfl
  | succ n =>
    cases n with
    | zero => cases p; rfl
    | succ n => exact source_higherCell p p rfl rfl

theorem target_identity {A : Type u} {n : Nat} (p : Cell A n) : target (identity p) = p := by
  cases n with
  | zero => cases p; rfl
  | succ n =>
    cases n with
    | zero => cases p; rfl
    | succ n => exact target_higherCell p p rfl rfl

noncomputable def identities (A : Type u) : GlobularSet.Identities (globular A) where
  identity := identity
  source_identity := source_identity
  target_identity := target_identity

/-- The existing primitive associator lands in the exact native second level. -/
noncomputable def associator {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Cell A 2 := associatorCell p q r

theorem associator_source {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    source (associator p q r) = ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) := rfl

theorem associator_target {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    target (associator p q r) = ULift.up (⟨a, d, Path.trans p (Path.trans q r)⟩ : PathOne A) := rfl

/-- The raw derivation in the embedded associator is the original primitive
`Step.trans_assoc`, not a proof selected from totality of `RwEq`. -/
theorem associator_derivation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (associator p q r).2.2.2.2 = RwEq.step (Step.trans_assoc p q r) := rfl

/-- The exact native second level has not been quotiented: even reflexivity
and its syntactic composite remain different cells. -/
theorem distinct_rewrite_cells {A : Type u} {a b : A} (p : Path a b) :
    (⟨a, b, p, p, RwEq.refl p⟩ : Cell A 2) ≠
      (⟨a, b, p, p, RwEq.trans (RwEq.refl p) (RwEq.refl p)⟩ : Cell A 2) := by
  intro h
  have h₁ := eq_of_heq (Sigma.mk.inj h).2
  have h₂ := eq_of_heq (Sigma.mk.inj h₁).2
  have h₃ := eq_of_heq (Sigma.mk.inj h₂).2
  have h₄ := eq_of_heq (Sigma.mk.inj h₃).2
  cases h₄

end NativeTower

end ComputationalPaths.Path.OmegaFoundations
