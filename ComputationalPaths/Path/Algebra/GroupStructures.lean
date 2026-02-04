/-
# Algebraic Structures for Computational Paths

This module defines strict monoids, groups, homomorphisms, and actions
specialized to the computational paths development.  The structures are
lightweight and avoid Mathlib dependencies while providing the algebraic
infrastructure needed by loop spaces, coverings, and higher groupoid
constructions.

## Key Definitions

- `StrictMonoid`, `StrictGroup`
- `MonoidHom`, `GroupHom`
- `Subgroup`
- `GroupAction`

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Hatcher, "Algebraic Topology", Section 1.3
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Strict Monoids -/

/-- A strict monoid structure with definitional associativity and units. -/
structure StrictMonoid (M : Type u) where
  /-- Multiplication. -/ 
  mul : M → M → M
  /-- Identity element. -/
  one : M
  /-- Associativity law. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity. -/
  mul_one : ∀ x, mul x one = x

namespace StrictMonoid

variable {M : Type u}

/-- Symmetric associativity. -/
theorem mul_assoc_symm (S : StrictMonoid M) (x y z : M) :
    S.mul x (S.mul y z) = S.mul (S.mul x y) z := by
  exact (S.mul_assoc x y z).symm

/-- Left cancellation given an explicit left inverse. -/
theorem mul_left_cancel {S : StrictMonoid M}
    (x y z : M) (h : S.mul z x = S.mul z y)
    (inv : M) (h_inv : S.mul inv z = S.one) :
    x = y := by
  calc
    x = S.mul S.one x := (S.one_mul x).symm
    _ = S.mul (S.mul inv z) x := by simp [h_inv]
    _ = S.mul inv (S.mul z x) := S.mul_assoc _ _ _
    _ = S.mul inv (S.mul z y) := by simp [h]
    _ = S.mul (S.mul inv z) y := (S.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by simp [h_inv]
    _ = y := S.one_mul y

/-- Right cancellation given an explicit right inverse. -/
theorem mul_right_cancel {S : StrictMonoid M}
    (x y z : M) (h : S.mul x z = S.mul y z)
    (inv : M) (h_inv : S.mul z inv = S.one) :
    x = y := by
  calc
    x = S.mul x S.one := (S.mul_one x).symm
    _ = S.mul x (S.mul z inv) := by simp [h_inv]
    _ = S.mul (S.mul x z) inv := (S.mul_assoc _ _ _).symm
    _ = S.mul (S.mul y z) inv := by simp [h]
    _ = S.mul y (S.mul z inv) := S.mul_assoc _ _ _
    _ = S.mul y S.one := by simp [h_inv]
    _ = y := S.mul_one y

end StrictMonoid

/-! ## Strict Groups -/

/-- A strict group structure with definitional inverses. -/
structure StrictGroup (G : Type u) extends StrictMonoid G where
  /-- Inversion. -/
  inv : G → G
  /-- Left inverse law. -/
  mul_left_inv : ∀ x, mul (inv x) x = one
  /-- Right inverse law. -/
  mul_right_inv : ∀ x, mul x (inv x) = one

namespace StrictGroup

variable {G : Type u}

/-- Left cancellation in a strict group. -/
theorem mul_left_cancel (S : StrictGroup G) (x y z : G) (h : S.mul z x = S.mul z y) :
    x = y :=
  StrictMonoid.mul_left_cancel (S := S.toStrictMonoid)
    x y z h (S.inv z) (S.mul_left_inv z)

/-- Right cancellation in a strict group. -/
theorem mul_right_cancel (S : StrictGroup G) (x y z : G) (h : S.mul x z = S.mul y z) :
    x = y :=
  StrictMonoid.mul_right_cancel (S := S.toStrictMonoid)
    x y z h (S.inv z) (S.mul_right_inv z)

/-- Inverse of identity. -/
theorem inv_one (S : StrictGroup G) : S.inv S.one = S.one := by
  calc
    S.inv S.one = S.mul S.one (S.inv S.one) := (S.one_mul _).symm
    _ = S.one := S.mul_right_inv S.one

/-- Inverse is involutive. -/
theorem inv_inv (S : StrictGroup G) (x : G) : S.inv (S.inv x) = x := by
  apply StrictGroup.mul_left_cancel S (S.inv (S.inv x)) x (S.inv x)
  calc
    S.mul (S.inv x) (S.inv (S.inv x)) = S.one := S.mul_right_inv (S.inv x)
    _ = S.mul (S.inv x) x := (S.mul_left_inv x).symm

/-- Solve for the inverse from a right inverse equation. -/
theorem inv_unique_right (S : StrictGroup G) (x y : G)
    (h : S.mul x y = S.one) : y = S.inv x := by
  apply StrictGroup.mul_left_cancel S y (S.inv x) x
  calc
    S.mul x y = S.one := h
    _ = S.mul x (S.inv x) := (S.mul_right_inv x).symm

/-- Solve for the inverse from a left inverse equation. -/
theorem inv_unique_left (S : StrictGroup G) (x y : G)
    (h : S.mul y x = S.one) : y = S.inv x := by
  apply StrictGroup.mul_right_cancel S y (S.inv x) x
  calc
    S.mul y x = S.one := h
    _ = S.mul (S.inv x) x := (S.mul_left_inv x).symm

end StrictGroup

/-! ## Homomorphisms -/

/-- Monoid homomorphisms between strict monoids. -/
structure MonoidHom (M : Type u) (N : Type v) (S : StrictMonoid M) (T : StrictMonoid N) where
  /-- Underlying function. -/
  toFun : M → N
  /-- Preserve multiplication. -/
  map_mul : ∀ x y, toFun (S.mul x y) = T.mul (toFun x) (toFun y)
  /-- Preserve identity. -/
  map_one : toFun S.one = T.one

namespace MonoidHom

variable {M : Type u} {N : Type v} {P : Type w}
variable {S : StrictMonoid M} {T : StrictMonoid N} {U : StrictMonoid P}

instance : CoeFun (MonoidHom M N S T) (fun _ => M → N) :=
  ⟨MonoidHom.toFun⟩

/-- Identity homomorphism. -/
@[simp] def id (S : StrictMonoid M) : MonoidHom M M S S where
  toFun := _root_.id
  map_mul := by intro x y; rfl
  map_one := rfl

/-- Composition of homomorphisms. -/
@[simp] def comp (f : MonoidHom M N S T) (g : MonoidHom N P T U) :
    MonoidHom M P S U where
  toFun := fun x => g (f x)
  map_mul := by intro x y; simp [f.map_mul, g.map_mul]
  map_one := by simpa [f.map_one] using g.map_one

@[simp] theorem comp_apply (f : MonoidHom M N S T) (g : MonoidHom N P T U) (x : M) :
    comp f g x = g (f x) := rfl

end MonoidHom

/-- Group homomorphisms between strict groups. -/
structure GroupHom (G : Type u) (H : Type v) (S : StrictGroup G) (T : StrictGroup H)
    extends MonoidHom G H S.toStrictMonoid T.toStrictMonoid where
  /-- Preserve inverses. -/
  map_inv : ∀ x, toFun (S.inv x) = T.inv (toFun x)

namespace GroupHom

variable {G : Type u} {H : Type v} {K : Type w}
variable {S : StrictGroup G} {T : StrictGroup H} {U : StrictGroup K}

instance : CoeFun (GroupHom G H S T) (fun _ => G → H) :=
  ⟨fun f => f.toMonoidHom.toFun⟩

/-- Identity group homomorphism. -/
@[simp] def id (S : StrictGroup G) : GroupHom G G S S where
  toMonoidHom := MonoidHom.id S.toStrictMonoid
  map_inv := by intro x; rfl

/-- Composition of group homomorphisms. -/
@[simp] def comp (f : GroupHom G H S T) (g : GroupHom H K T U) :
    GroupHom G K S U where
  toMonoidHom := MonoidHom.comp f.toMonoidHom g.toMonoidHom
  map_inv := by intro x; simp [f.map_inv, g.map_inv]

@[simp] theorem comp_apply (f : GroupHom G H S T) (g : GroupHom H K T U) (x : G) :
    comp f g x = g (f x) := rfl

/-- Inverse of the identity is preserved. -/
@[simp] theorem map_inv_id (S : StrictGroup G) (x : G) :
    (id S) (S.inv x) = S.inv x := rfl

end GroupHom

/-! ## Subgroups -/

/-- A subgroup of a strict group defined by a closed predicate. -/
structure Subgroup (G : Type u) (S : StrictGroup G) where
  /-- Membership predicate. -/
  carrier : G → Prop
  /-- Contains identity. -/
  one_mem : carrier S.one
  /-- Closed under multiplication. -/
  mul_mem : ∀ {x y}, carrier x → carrier y → carrier (S.mul x y)
  /-- Closed under inverses. -/
  inv_mem : ∀ {x}, carrier x → carrier (S.inv x)

namespace Subgroup

variable {G : Type u} {S : StrictGroup G}

/-- Trivial subgroup. -/
@[simp] def trivial (S : StrictGroup G) : Subgroup G S where
  carrier := fun x => x = S.one
  one_mem := rfl
  mul_mem := by
    intro x y hx hy
    simp [hx, hy, S.mul_one]
  inv_mem := by
    intro x hx
    simpa [hx] using (StrictGroup.inv_one S)

/-- Intersection of subgroups. -/
@[simp] def inter (H K : Subgroup G S) : Subgroup G S where
  carrier := fun x => H.carrier x ∧ K.carrier x
  one_mem := ⟨H.one_mem, K.one_mem⟩
  mul_mem := by
    intro x y hx hy
    exact ⟨H.mul_mem hx.1 hy.1, K.mul_mem hx.2 hy.2⟩
  inv_mem := by
    intro x hx
    exact ⟨H.inv_mem hx.1, K.inv_mem hx.2⟩

/-- Membership of the identity is unique in a subgroup. -/
theorem one_unique {H : Subgroup G S} {x : G} (_ : H.carrier x) (_ : H.carrier (S.inv x)) :
    S.mul x (S.inv x) = S.one := by
  exact S.mul_right_inv x

end Subgroup

/-! ## Group Actions -/

/-- A (left) group action of a strict group on a type. -/
structure GroupAction (G : Type u) (S : StrictGroup G) (X : Type v) where
  /-- Action map. -/
  act : G → X → X
  /-- Identity acts trivially. -/
  act_one : ∀ x, act S.one x = x
  /-- Compatibility with multiplication. -/
  act_mul : ∀ g h x, act (S.mul g h) x = act g (act h x)

namespace GroupAction

variable {G : Type u} {X : Type v} {S : StrictGroup G}

/-- Action respects identity. -/
@[simp] theorem act_one' (A : GroupAction G S X) (x : X) : A.act S.one x = x :=
  A.act_one x

/-- Action respects multiplication. -/
@[simp] theorem act_mul' (A : GroupAction G S X) (g h : G) (x : X) :
    A.act (S.mul g h) x = A.act g (A.act h x) :=
  A.act_mul g h x

end GroupAction

/-! ## Powers and Conjugation -/

namespace StrictMonoid

variable {M : Type u}

/-- Natural power of an element in a strict monoid. -/
@[simp] def pow (S : StrictMonoid M) (x : M) : Nat → M
  | 0 => S.one
  | Nat.succ n => S.mul (pow S x n) x

/-- Zero power is the identity. -/
@[simp] theorem pow_zero (S : StrictMonoid M) (x : M) :
    pow S x 0 = S.one := rfl

/-- Successor power expands by one multiplication. -/
@[simp] theorem pow_succ (S : StrictMonoid M) (x : M) (n : Nat) :
    pow S x (Nat.succ n) = S.mul (pow S x n) x := rfl

/-- Power one is the element itself. -/
@[simp] theorem pow_one (S : StrictMonoid M) (x : M) :
    pow S x 1 = x := by
  simp [pow, S.one_mul]

/-- Addition law for powers. -/
theorem pow_add (S : StrictMonoid M) (x : M) (m n : Nat) :
    pow S x (m + n) = S.mul (pow S x m) (pow S x n) := by
  induction n with
  | zero =>
      simp [pow, S.mul_one]
  | succ n ih =>
      calc
        pow S x (m + Nat.succ n)
            = pow S x (Nat.succ (m + n)) := by simp
        _ = S.mul (pow S x (m + n)) x := rfl
        _ = S.mul (S.mul (pow S x m) (pow S x n)) x := by simp [ih]
        _ = S.mul (pow S x m) (S.mul (pow S x n) x) := by
            simp [S.mul_assoc]
        _ = S.mul (pow S x m) (pow S x (Nat.succ n)) := rfl

/-- Power commutation for a fixed base. -/
theorem pow_comm (S : StrictMonoid M) (x : M) (m n : Nat) :
    S.mul (pow S x m) (pow S x n) = S.mul (pow S x n) (pow S x m) := by
  calc
    S.mul (pow S x m) (pow S x n) = pow S x (m + n) := (pow_add S x m n).symm
    _ = pow S x (n + m) := by simp [Nat.add_comm]
    _ = S.mul (pow S x n) (pow S x m) := pow_add S x n m

/-- Multiplicative law for powers. -/
theorem pow_mul (S : StrictMonoid M) (x : M) (m n : Nat) :
    pow S x (m * n) = pow S (pow S x m) n := by
  induction n with
  | zero =>
      simp [pow]
  | succ n ih =>
      have hNat : m * Nat.succ n = m * n + m := Nat.mul_succ m n
      calc
        pow S x (m * Nat.succ n)
            = pow S x (m * n + m) := by simp [hNat]
        _ = S.mul (pow S x (m * n)) (pow S x m) := pow_add S x (m * n) m
        _ = S.mul (pow S (pow S x m) n) (pow S x m) := by simp [ih]
        _ = pow S (pow S x m) (Nat.succ n) := rfl

end StrictMonoid

namespace StrictGroup

variable {G : Type u}

/-- Natural power in a strict group (alias of monoid power). -/
@[simp] def pow (S : StrictGroup G) (x : G) : Nat → G :=
  StrictMonoid.pow (S := S.toStrictMonoid) x

/-- Zero power in a strict group. -/
@[simp] theorem pow_zero (S : StrictGroup G) (x : G) :
    pow S x 0 = S.one :=
  StrictMonoid.pow_zero (S := S.toStrictMonoid) (x := x)

/-- Successor power in a strict group. -/
@[simp] theorem pow_succ (S : StrictGroup G) (x : G) (n : Nat) :
    pow S x (Nat.succ n) = S.mul (pow S x n) x :=
  StrictMonoid.pow_succ (S := S.toStrictMonoid) (x := x) (n := n)

/-- Power one in a strict group. -/
@[simp] theorem pow_one (S : StrictGroup G) (x : G) :
    pow S x 1 = x :=
  StrictMonoid.pow_one (S := S.toStrictMonoid) (x := x)

/-- Addition law for powers in a strict group. -/
theorem pow_add (S : StrictGroup G) (x : G) (m n : Nat) :
    pow S x (m + n) = S.mul (pow S x m) (pow S x n) :=
  StrictMonoid.pow_add (S := S.toStrictMonoid) (x := x) (m := m) (n := n)

/-- Power commutation for a fixed base in a strict group. -/
theorem pow_comm (S : StrictGroup G) (x : G) (m n : Nat) :
    S.mul (pow S x m) (pow S x n) = S.mul (pow S x n) (pow S x m) :=
  StrictMonoid.pow_comm (S := S.toStrictMonoid) (x := x) (m := m) (n := n)

/-- Multiplicative law for powers in a strict group. -/
theorem pow_mul (S : StrictGroup G) (x : G) (m n : Nat) :
    pow S x (m * n) = pow S (pow S x m) n :=
  StrictMonoid.pow_mul (S := S.toStrictMonoid) (x := x) (m := m) (n := n)

@[simp] private theorem neg_ofNat_succ_eq_negSucc (n : Nat) :
    -Int.ofNat (Nat.succ n) = Int.negSucc n := rfl

@[simp] private theorem neg_negSucc_eq_ofNat_succ (n : Nat) :
    -Int.negSucc n = Int.ofNat (Nat.succ n) := rfl

/-- Integer power in a strict group. -/
@[simp] def zpow (S : StrictGroup G) (x : G) : Int → G
  | Int.ofNat n => pow S x n
  | Int.negSucc n => S.inv (pow S x (Nat.succ n))

/-- Integer power for naturals. -/
@[simp] theorem zpow_ofNat (S : StrictGroup G) (x : G) (n : Nat) :
    zpow S x n = pow S x n := rfl

/-- Integer power at zero. -/
@[simp] theorem zpow_zero (S : StrictGroup G) (x : G) :
    zpow S x 0 = S.one := rfl

/-- Integer power at one. -/
@[simp] theorem zpow_one (S : StrictGroup G) (x : G) :
    zpow S x 1 = x := by
  change pow S x 1 = x
  exact pow_one S x

/-- Integer power at negative successor. -/
@[simp] theorem zpow_negSucc (S : StrictGroup G) (x : G) (n : Nat) :
    zpow S x (Int.negSucc n) = S.inv (pow S x (Nat.succ n)) := rfl

/-- Integer power at -1. -/
@[simp] theorem zpow_neg_one (S : StrictGroup G) (x : G) :
    zpow S x (-1) = S.inv x := by
  have h :=
    _root_.congrArg (fun y => S.inv y)
      (pow_one (S := S) (x := x))
  change S.inv (pow S x (Nat.succ 0)) = S.inv x
  exact h

/-- Power of an inverse equals inverse of power. -/
theorem inv_pow (S : StrictGroup G) (x : G) (n : Nat) :
    S.inv (pow S x n) = pow S (S.inv x) n := by
  induction n with
  | zero =>
      simp [pow, StrictGroup.inv_one]
  | succ n ih =>
      have h_inv :
          S.mul (S.mul (pow S x n) x) (S.mul (S.inv x) (S.inv (pow S x n))) = S.one := by
        calc
          S.mul (S.mul (pow S x n) x) (S.mul (S.inv x) (S.inv (pow S x n)))
              = S.mul (pow S x n) (S.mul x (S.mul (S.inv x) (S.inv (pow S x n)))) := by
                  simp [S.mul_assoc]
          _ = S.mul (pow S x n) (S.mul (S.mul x (S.inv x)) (S.inv (pow S x n))) := by
                  simp [S.mul_assoc]
          _ = S.mul (pow S x n) (S.mul S.one (S.inv (pow S x n))) := by
                  simp [S.mul_right_inv]
          _ = S.mul (pow S x n) (S.inv (pow S x n)) := by simp [S.one_mul]
          _ = S.one := S.mul_right_inv (pow S x n)
      have h :=
        StrictGroup.inv_unique_right S (S.mul (pow S x n) x)
          (S.mul (S.inv x) (S.inv (pow S x n))) h_inv
      calc
        S.inv (pow S x (Nat.succ n))
            = S.inv (S.mul (pow S x n) x) := by rfl
        _ = S.mul (S.inv x) (S.inv (pow S x n)) := h.symm
        _ = S.mul (S.inv x) (pow S (S.inv x) n) := by rw [ih]
        _ = S.mul (pow S (S.inv x) n) (S.inv x) := by
              simpa [pow_one, S.one_mul, S.mul_one] using
                (pow_comm (S := S) (x := S.inv x) (m := 1) (n := n))
        _ = pow S (S.inv x) (Nat.succ n) := rfl

/-- Inverse of a product. -/
theorem inv_mul_eq (S : StrictGroup G) (x y : G) :
    S.inv (S.mul x y) = S.mul (S.inv y) (S.inv x) := by
  apply StrictGroup.mul_right_cancel S (S.inv (S.mul x y)) (S.mul (S.inv y) (S.inv x)) (S.mul x y)
  have hR : S.mul (S.mul (S.inv y) (S.inv x)) (S.mul x y) = S.one := by
    calc
      S.mul (S.mul (S.inv y) (S.inv x)) (S.mul x y)
          = S.mul (S.inv y) (S.mul (S.inv x) (S.mul x y)) := by
              simp [S.mul_assoc]
      _ = S.mul (S.inv y) (S.mul (S.mul (S.inv x) x) y) := by
              simp [S.mul_assoc]
      _ = S.mul (S.inv y) (S.mul S.one y) := by
              simp [S.mul_left_inv]
      _ = S.mul (S.inv y) y := by simp [S.one_mul]
      _ = S.one := S.mul_left_inv y
  calc
    S.mul (S.inv (S.mul x y)) (S.mul x y) = S.one := S.mul_left_inv (S.mul x y)
    _ = S.mul (S.mul (S.inv y) (S.inv x)) (S.mul x y) := hR.symm

/-- Alternate successor law: x^(n+1) = x * x^n. -/
theorem pow_succ_left (S : StrictGroup G) (x : G) (n : Nat) :
    pow S x (Nat.succ n) = S.mul x (pow S x n) := by
  calc
    pow S x (Nat.succ n) = pow S x (n + 1) := by
      simp
    _ = pow S x (1 + n) := by
      simp [Nat.add_comm]
    _ = S.mul (pow S x 1) (pow S x n) := pow_add S x 1 n
    _ = S.mul x (pow S x n) := by
          rw [pow_one]

/-- Commutation between x and inverse of x^n. -/
theorem inv_pow_comm (S : StrictGroup G) (x : G) (n : Nat) :
    S.mul (S.inv (pow S x n)) x = S.mul x (S.inv (pow S x n)) := by
  apply StrictGroup.mul_right_cancel S
    (S.mul (S.inv (pow S x n)) x)
    (S.mul x (S.inv (pow S x n)))
    (pow S x n)
  calc
    S.mul (S.mul (S.inv (pow S x n)) x) (pow S x n)
        = S.mul (S.inv (pow S x n)) (S.mul x (pow S x n)) := by
            simp [S.mul_assoc]
    _ = S.mul (S.inv (pow S x n)) (pow S x (Nat.succ n)) := by
            rw [← pow_succ_left (S := S) (x := x) (n := n)]
    _ = S.mul (S.inv (pow S x n)) (S.mul (pow S x n) x) := by rfl
    _ = S.mul (S.mul (S.inv (pow S x n)) (pow S x n)) x := by
            simp [S.mul_assoc]
    _ = S.mul S.one x := by
            simp [S.mul_left_inv]
    _ = x := by simp [S.one_mul]
    _ = S.mul x S.one := (S.mul_one x).symm
    _ = S.mul x (S.mul (S.inv (pow S x n)) (pow S x n)) := by
            simp [S.mul_left_inv]
    _ = S.mul (S.mul x (S.inv (pow S x n))) (pow S x n) := by
            simp [S.mul_assoc]

/-- Integer successor law. -/
theorem zpow_succ (S : StrictGroup G) (x : G) (n : Int) :
    zpow S x (n + 1) = S.mul (zpow S x n) x := by
  cases n with
  | ofNat n =>
      have : Int.ofNat n + 1 = Int.ofNat (n + 1) := rfl
      rw [this]
      simp [zpow]
  | negSucc n =>
      cases n with
      | zero =>
          have : Int.negSucc 0 + 1 = 0 := rfl
          rw [this]
          simp [zpow, S.mul_left_inv, S.one_mul]
      | succ n =>
          have : Int.negSucc (Nat.succ n) + 1 = Int.negSucc n := rfl
          rw [this]
          simp only [zpow]
          have hcalc :
              S.mul (S.inv (pow S x (Nat.succ (Nat.succ n)))) x =
                S.inv (pow S x (Nat.succ n)) := by
            calc
              S.mul (S.inv (pow S x (Nat.succ (Nat.succ n)))) x
                  = S.mul (S.inv (S.mul (pow S x (Nat.succ n)) x)) x := by
                      simp
              _ = S.mul (S.mul (S.inv x) (S.inv (pow S x (Nat.succ n)))) x := by
                      simp [inv_mul_eq, S.mul_assoc]
              _ = S.mul (S.inv x) (S.mul (S.inv (pow S x (Nat.succ n))) x) := by
                      simp [S.mul_assoc]
              _ = S.mul (S.inv x) (S.mul x (S.inv (pow S x (Nat.succ n)))) := by
                      rw [inv_pow_comm (S := S) (x := x) (n := Nat.succ n)]
              _ = S.mul (S.mul (S.inv x) x) (S.inv (pow S x (Nat.succ n))) := by
                      simp [S.mul_assoc]
              _ = S.mul S.one (S.inv (pow S x (Nat.succ n))) := by
                      simp [S.mul_left_inv]
              _ = S.inv (pow S x (Nat.succ n)) := by
                      simp [S.one_mul]
          exact hcalc.symm

/-- Integer predecessor law. -/
theorem zpow_pred (S : StrictGroup G) (x : G) (n : Int) :
    zpow S x (n - 1) = S.mul (zpow S x n) (S.inv x) := by
  cases n with
  | ofNat n =>
      cases n with
      | zero =>
          have : Int.ofNat 0 - 1 = Int.negSucc 0 := rfl
          rw [this]
          simp [zpow, S.one_mul]
      | succ n =>
          have : Int.ofNat (Nat.succ n) - 1 = Int.ofNat n := by simp
          rw [this]
          simp [zpow, S.mul_assoc, S.mul_right_inv, S.mul_one]
  | negSucc n =>
      have : Int.negSucc n - 1 = Int.negSucc (Nat.succ n) := rfl
      rw [this]
      simp only [zpow]
      calc
        S.inv (pow S x (Nat.succ (Nat.succ n)))
            = S.inv (S.mul x (pow S x (Nat.succ n))) := by
                rw [pow_succ_left (S := S) (x := x) (n := Nat.succ n)]
        _ = S.mul (S.inv (pow S x (Nat.succ n))) (S.inv x) := by
                simp [inv_mul_eq, S.mul_assoc]

/-- Integer induction for group power proofs. -/
theorem int_induction {P : Int → Prop}
    (base : P 0)
    (succ : ∀ n, P n → P (n + 1))
    (pred : ∀ n, P n → P (n - 1)) : ∀ n, P n := by
  intro n
  cases n with
  | ofNat n =>
      induction n with
      | zero => exact base
      | succ n ih => exact succ _ ih
  | negSucc n =>
      induction n with
      | zero => exact pred 0 base
      | succ n ih => exact pred (Int.negSucc n) ih

/-- Addition law for integer powers. -/
theorem zpow_add (S : StrictGroup G) (x : G) (m n : Int) :
    zpow S x (m + n) = S.mul (zpow S x m) (zpow S x n) := by
  induction n using int_induction with
  | base =>
      simp [zpow, S.mul_one]
  | succ n ih =>
      rw [← Int.add_assoc, zpow_succ, ih, zpow_succ, S.mul_assoc]
  | pred n ih =>
      rw [Int.sub_eq_add_neg, ← Int.add_assoc, ← Int.sub_eq_add_neg]
      rw [zpow_pred, ih]
      conv =>
        rhs
        rw [← Int.sub_eq_add_neg]
        rw [zpow_pred]
      rw [S.mul_assoc]

/-- Negation law for integer powers. -/
theorem zpow_neg (S : StrictGroup G) (x : G) (z : Int) :
    zpow S x (-z) = S.inv (zpow S x z) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          change S.one = S.inv S.one
          simp [StrictGroup.inv_one]
      | succ n =>
          rw [neg_ofNat_succ_eq_negSucc]
          rfl
  | negSucc n =>
      rw [neg_negSucc_eq_ofNat_succ]
      have h₁ : zpow S x ((Nat.succ n : Nat) : Int) = pow S x (Nat.succ n) := rfl
      have h₂ :
          S.inv (zpow S x (Int.negSucc n)) = pow S x (Nat.succ n) := by
        change S.inv (S.inv (pow S x (Nat.succ n))) = pow S x (Nat.succ n)
        exact inv_inv S (pow S x (Nat.succ n))
      exact h₁.trans h₂.symm

/-- Conjugation by an element. -/
@[simp] def conj (S : StrictGroup G) (g x : G) : G :=
  S.mul (S.mul g x) (S.inv g)

/-- Conjugation by identity is identity. -/
@[simp] theorem conj_one_left (S : StrictGroup G) (x : G) :
    conj S S.one x = x := by
  simp [conj, S.one_mul, S.mul_one, StrictGroup.inv_one S]

/-- Conjugation of identity gives identity. -/
@[simp] theorem conj_one_right (S : StrictGroup G) (g : G) :
    conj S g S.one = S.one := by
  calc
    conj S g S.one = S.mul (S.mul g S.one) (S.inv g) := rfl
    _ = S.mul g (S.inv g) := by simp [S.mul_one]
    _ = S.one := S.mul_right_inv g

/-- Conjugation distributes over multiplication. -/
theorem conj_mul (S : StrictGroup G) (g x y : G) :
    conj S g (S.mul x y) = S.mul (conj S g x) (conj S g y) := by
  have h1 :
      S.mul (S.inv g) (S.mul (S.mul g y) (S.inv g)) =
        S.mul (S.mul (S.inv g) g) (S.mul y (S.inv g)) := by
    calc
      S.mul (S.inv g) (S.mul (S.mul g y) (S.inv g))
          = S.mul (S.mul (S.inv g) (S.mul g y)) (S.inv g) := by
              simp [S.mul_assoc]
      _ = S.mul (S.mul (S.mul (S.inv g) g) y) (S.inv g) := by
              simp [S.mul_assoc]
      _ = S.mul (S.mul (S.inv g) g) (S.mul y (S.inv g)) := by
            simp [S.mul_assoc]
  have h2 :
      S.mul y (S.inv g) = S.mul (S.inv g) (S.mul (S.mul g y) (S.inv g)) := by
    calc
      S.mul y (S.inv g)
          = S.mul S.one (S.mul y (S.inv g)) := (S.one_mul _).symm
      _ = S.mul (S.mul (S.inv g) g) (S.mul y (S.inv g)) := by
            simp [S.mul_left_inv]
      _ = S.mul (S.inv g) (S.mul (S.mul g y) (S.inv g)) := h1.symm
  calc
    conj S g (S.mul x y)
        = S.mul (S.mul g (S.mul x y)) (S.inv g) := rfl
    _ = S.mul (S.mul (S.mul g x) y) (S.inv g) := by
          simp [S.mul_assoc]
    _ = S.mul (S.mul g x) (S.mul y (S.inv g)) := by
          simp [S.mul_assoc]
    _ = S.mul (S.mul g x) (S.mul (S.inv g) (S.mul (S.mul g y) (S.inv g))) := by
          simp [h2]
    _ = S.mul (S.mul (S.mul g x) (S.inv g)) (S.mul (S.mul g y) (S.inv g)) := by
          simp [S.mul_assoc]
    _ = S.mul (conj S g x) (conj S g y) := rfl

/-- Conjugation of an inverse. -/
theorem conj_inv (S : StrictGroup G) (g x : G) :
    conj S g (S.inv x) = S.inv (conj S g x) := by
  have h :
      S.inv (S.mul (S.mul g x) (S.inv g)) = S.mul (S.mul g (S.inv x)) (S.inv g) := by
    calc
      S.inv (S.mul (S.mul g x) (S.inv g))
          = S.mul (S.inv (S.inv g)) (S.inv (S.mul g x)) := inv_mul_eq S _ _
      _ = S.mul g (S.inv (S.mul g x)) := by
            simp [inv_inv]
      _ = S.mul g (S.mul (S.inv x) (S.inv g)) := by
            simp [inv_mul_eq]
      _ = S.mul (S.mul g (S.inv x)) (S.inv g) := by
            simp [S.mul_assoc]
  calc
    conj S g (S.inv x) = S.mul (S.mul g (S.inv x)) (S.inv g) := rfl
    _ = S.inv (S.mul (S.mul g x) (S.inv g)) := by simp [h]
    _ = S.inv (conj S g x) := rfl

/-- Conjugation composition law. -/
theorem conj_conj (S : StrictGroup G) (g h x : G) :
    conj S g (conj S h x) = conj S (S.mul g h) x := by
  calc
    conj S g (conj S h x)
        = S.mul (S.mul g (S.mul (S.mul h x) (S.inv h))) (S.inv g) := rfl
    _ = S.mul (S.mul (S.mul g h) x) (S.mul (S.inv h) (S.inv g)) := by
          simp [S.mul_assoc]
    _ = S.mul (S.mul (S.mul g h) x) (S.inv (S.mul g h)) := by
          simp [inv_mul_eq]
    _ = conj S (S.mul g h) x := rfl

/-- Commutator of two elements. -/
@[simp] def commutator (S : StrictGroup G) (x y : G) : G :=
  S.mul (S.mul x y) (S.mul (S.inv x) (S.inv y))

/-- Commutator with identity on the left. -/
@[simp] theorem commutator_one_left (S : StrictGroup G) (y : G) :
    commutator S S.one y = S.one := by
  simp [commutator, S.one_mul, StrictGroup.inv_one S, S.mul_right_inv]

/-- Commutator with identity on the right. -/
@[simp] theorem commutator_one_right (S : StrictGroup G) (x : G) :
    commutator S x S.one = S.one := by
  simp [commutator, S.mul_one, StrictGroup.inv_one S, S.mul_right_inv]

/-- Self-commutator is identity. -/
@[simp] theorem commutator_self (S : StrictGroup G) (x : G) :
    commutator S x x = S.one := by
  calc
    commutator S x x = S.mul (S.mul (S.mul x x) (S.inv x)) (S.inv x) := by
      simp [commutator, S.mul_assoc]
    _ = S.mul (S.mul x (S.mul x (S.inv x))) (S.inv x) := by
      simp [S.mul_assoc]
    _ = S.mul (S.mul x S.one) (S.inv x) := by
      simp [S.mul_right_inv]
    _ = S.mul x (S.inv x) := by simp [S.one_mul, S.mul_assoc]
    _ = S.one := S.mul_right_inv x

/-- Conjugation preserves commutators. -/
theorem conj_commutator (S : StrictGroup G) (g x y : G) :
    conj S g (commutator S x y) = commutator S (conj S g x) (conj S g y) := by
  have h1 := conj_mul (S := S) g x y
  have h2 := conj_mul (S := S) g (S.inv x) (S.inv y)
  have h3 := conj_inv (S := S) g x
  have h4 := conj_inv (S := S) g y
  calc
    conj S g (commutator S x y)
        = S.mul (conj S g (S.mul x y)) (conj S g (S.mul (S.inv x) (S.inv y))) := by
            simpa [commutator] using
              (conj_mul (S := S) g (S.mul x y) (S.mul (S.inv x) (S.inv y)))
    _ = S.mul (S.mul (conj S g x) (conj S g y))
          (S.mul (conj S g (S.inv x)) (conj S g (S.inv y))) := by
            rw [h1, h2]
    _ = S.mul (S.mul (conj S g x) (conj S g y))
          (S.mul (S.inv (conj S g x)) (S.inv (conj S g y))) := by
            rw [h3, h4]
    _ = commutator S (conj S g x) (conj S g y) := rfl

end StrictGroup

/-! ## Equivalences from Homomorphisms -/

/-- A group isomorphism packaged as a SimpleEquiv. -/
@[simp] def groupIso_toSimpleEquiv {G : Type u} {H : Type v}
    {S : StrictGroup G} {T : StrictGroup H}
    (f : GroupHom G H S T)
    (g : GroupHom H G T S)
    (h₁ : ∀ x, g (f x) = x)
    (h₂ : ∀ y, f (g y) = y) :
    SimpleEquiv G H where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂

end Algebra
end Path
end ComputationalPaths
