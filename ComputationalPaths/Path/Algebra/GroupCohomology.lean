/-
# Group Cohomology for Computational Paths

A minimal group cohomology interface H^n(G, M) phrased using computational
paths. All proofs are complete -- no sorry, no axiom.
-/
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GroupCohomology

universe u v

/-! ## G-modules -/

/-- A left G-module with an abelian-group structure. -/
structure GroupModule (G : Type u) (S : StrictGroup G) where
  /-- The underlying carrier. -/
  carrier : Type v
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Zero element. -/
  zero : carrier
  /-- Negation. -/
  neg : carrier → carrier
  /-- Commutativity of addition. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Associativity of addition. -/
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  /-- Right identity for addition. -/
  add_zero : ∀ x, add x zero = x
  /-- Left inverse for addition. -/
  add_left_neg : ∀ x, add (neg x) x = zero
  /-- G-action on the carrier. -/
  act : G → carrier → carrier
  /-- Identity acts trivially. -/
  act_one : ∀ x, act S.one x = x
  /-- Action respects multiplication. -/
  act_mul : ∀ g h x, act (S.mul g h) x = act g (act h x)
  /-- Action is additive. -/
  act_add : ∀ g x y, act g (add x y) = add (act g x) (act g y)
  /-- Action preserves zero. -/
  act_zero : ∀ g, act g zero = zero

namespace GroupModule

variable {G : Type u} {S : StrictGroup G}
variable (M : GroupModule G S)

/-- Path witnessing x + 0 = x. -/
def add_zero_path (x : M.carrier) : Path (M.add x M.zero) x :=
  Path.ofEq (M.add_zero x)

/-- Path witnessing (-x) + x = 0. -/
def add_left_neg_path (x : M.carrier) : Path (M.add (M.neg x) x) M.zero :=
  Path.ofEq (M.add_left_neg x)

/-- Path witnessing the identity action. -/
def act_one_path (x : M.carrier) : Path (M.act S.one x) x :=
  Path.ofEq (M.act_one x)

/-- Path witnessing that g • 0 = 0. -/
def act_zero_path (g : G) : Path (M.act g M.zero) M.zero :=
  Path.ofEq (M.act_zero g)

end GroupModule

/-! ## Cochains -/

/-- The n-cochains on G with values in M. -/
def Cochain {G : Type u} {S : StrictGroup G} (M : GroupModule G S) (n : Nat) :=
  (Fin n → G) → M.carrier

/-- The zero cochain. -/
def cochainZero {G : Type u} {S : StrictGroup G} (M : GroupModule G S) (n : Nat) :
    Cochain M n :=
  fun (_ : Fin n → G) => M.zero

/-- Pointwise addition of cochains. -/
def cochainAdd {G : Type u} {S : StrictGroup G} (M : GroupModule G S) (n : Nat)
    (f g : Cochain M n) : Cochain M n :=
  fun (xs : Fin n → G) => M.add (f xs) (g xs)

/-- Path witnessing f + 0 = f for cochains. -/
def cochain_add_zero_path {G : Type u} {S : StrictGroup G} (M : GroupModule G S)
    (n : Nat) (f : Cochain M n) :
    Path (cochainAdd M n f (cochainZero M n)) f := by
  apply Path.ofEq
  funext xs
  simpa [cochainAdd, cochainZero] using M.add_zero (f xs)

/-! ## Cohomology differentials -/

/-- A cohomology differential on group cochains. -/
structure CohomologyDifferential {G : Type u} {S : StrictGroup G}
    (M : GroupModule G S) where
  /-- The coboundary operator. -/
  delta : (n : Nat) → Cochain M n → Cochain M (n + 1)
  /-- d ∘ d = 0, expressed with a path. -/
  delta_sq : ∀ n (f : Cochain M n),
    Path (delta (n + 1) (delta n f)) (cochainZero M (n + 2))
  /-- d sends zero to zero. -/
  delta_zero : ∀ n, Path (delta n (cochainZero M n)) (cochainZero M (n + 1))

/-! ## Cocycles and cohomology -/

/-- A cocycle is a cochain with vanishing coboundary. -/
structure Cocycle {G : Type u} {S : StrictGroup G} {M : GroupModule G S}
    (D : CohomologyDifferential M) (n : Nat) where
  /-- The underlying cochain. -/
  cochain : Cochain M n
  /-- The cocycle condition. -/
  closed : Path (D.delta n cochain) (cochainZero M (n + 1))

/-- Two cocycles are cohomologous if they differ by a coboundary. -/
def CohomologyRel {G : Type u} {S : StrictGroup G} {M : GroupModule G S}
    (D : CohomologyDifferential M) (n : Nat) :
    Cocycle D n → Cocycle D n → Prop :=
  match n with
  | 0 =>
      fun x y => Nonempty (Path x.cochain y.cochain)
  | Nat.succ k =>
      fun x y =>
        ∃ b : Cochain M k,
          Nonempty (Path x.cochain (cochainAdd M (Nat.succ k) y.cochain (D.delta k b)))

/-- The group cohomology H^n(G, M) as cocycles modulo coboundaries. -/
def Cohomology {G : Type u} {S : StrictGroup G} {M : GroupModule G S}
    (D : CohomologyDifferential M) (n : Nat) : Type _ :=
  Quot (CohomologyRel (D := D) n)

/-- Alias for H^n(G, M). -/
abbrev H {G : Type u} {S : StrictGroup G} {M : GroupModule G S}
    (D : CohomologyDifferential M) (n : Nat) : Type _ :=
  Cohomology D n

/-- The zero cocycle in any degree. -/
def zeroCocycle {G : Type u} {S : StrictGroup G} {M : GroupModule G S}
    (D : CohomologyDifferential M) (n : Nat) : Cocycle D n where
  cochain := cochainZero M n
  closed := D.delta_zero n

/-! ## Trivial examples -/

/-- The zero differential on cochains. -/
def trivialDifferential {G : Type u} {S : StrictGroup G} (M : GroupModule G S) :
    CohomologyDifferential M where
  delta := fun n _ => cochainZero M (n + 1)
  delta_sq := by
    intro n f
    exact Path.ofEq rfl
  delta_zero := by
    intro n
    exact Path.ofEq rfl

/-- The trivial G-module with carrier PUnit. -/
def trivialModule (G : Type u) (S : StrictGroup G) : GroupModule G S where
  carrier := PUnit
  add := fun _ _ => PUnit.unit
  zero := PUnit.unit
  neg := fun _ => PUnit.unit
  add_comm := by intro _ _; rfl
  add_assoc := by intro _ _ _; rfl
  add_zero := by intro _; rfl
  add_left_neg := by intro _; rfl
  act := fun _ _ => PUnit.unit
  act_one := by intro _; rfl
  act_mul := by intro _ _ _; rfl
  act_add := by intro _ _ _; rfl
  act_zero := by intro _; rfl

/-! ## Summary -/

-- We introduced group modules, cochains, a path-based differential, and the
-- cohomology quotient H^n(G, M) together with trivial examples.

end GroupCohomology
end Algebra
end Path
end ComputationalPaths
