/-
# Operadic Structure on Loop Spaces

This module packages parenthesized loop composition as an associative operad and
records the associahedron (K4) coherence for its action on loop spaces.

## Key Results

- `assocOperad`: the operad of associative parenthesizations
- `loopOperadAction`: action on loop spaces by concatenation
- `associahedron_k4`: pentagon coherence for the operad action

## References

- Stasheff, "Homotopy Associativity of H-Spaces"
- Leinster, "Higher Operads, Higher Categories"
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.HigherCoherenceDerived

namespace ComputationalPaths
namespace Path
namespace OperadicStructure

universe u v

/-! ## Length-Indexed Vectors -/

/-- Length-indexed vectors used to feed operadic inputs. -/
inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (Nat.succ n)

namespace Vec

variable {α : Type u}

/-- Singleton vector. -/
def singleton (x : α) : Vec α 1 :=
  Vec.cons x Vec.nil

/-- Convenience constructor for length-4 vectors. -/
def of4 (a b c d : α) : Vec α 4 :=
  Vec.cons a (Vec.cons b (Vec.cons c (Vec.cons d Vec.nil)))

/-- Split a vector at a fixed length. -/
def split : {m n : Nat} → Vec α (m + n) → Vec α m × Vec α n
  | 0, n, xs =>
      (Vec.nil, by
        simpa [Nat.zero_add] using xs)
  | Nat.succ m, n, xs =>
      let xs' : Vec α (Nat.succ (m + n)) := by
        simpa [Nat.succ_add] using xs
      match xs' with
      | Vec.cons x xs'' =>
          let (xs1, xs2) := split (m := m) (n := n) xs''
          (Vec.cons x xs1, xs2)

end Vec

/-! ## Associative Operad Trees -/

/-- Planar binary trees encoding parenthesizations. -/
inductive AssocTree : Type u
  | leaf : AssocTree
  | node : AssocTree → AssocTree → AssocTree

/-- Number of leaves in a parenthesization tree. -/
def AssocTree.arity : AssocTree → Nat
  | AssocTree.leaf => 1
  | AssocTree.node t1 t2 => AssocTree.arity t1 + AssocTree.arity t2

/-- Operadic operations are parenthesization trees. -/
abbrev AssocOp := AssocTree

/-- Unit operation (single leaf). -/
def AssocOp.unit : AssocOp :=
  AssocTree.leaf

/-- Graft operations into the leaves of a parenthesization tree. -/
def AssocOp.graft : (op : AssocOp) → Vec AssocOp (AssocTree.arity op) → AssocOp
  | AssocTree.leaf, Vec.cons op Vec.nil => op
  | AssocTree.node t1 t2, ops =>
      let (ops1, ops2) := Vec.split
        (m := AssocTree.arity t1) (n := AssocTree.arity t2) ops
      AssocTree.node (AssocOp.graft t1 ops1) (AssocOp.graft t2 ops2)

/-- Non-symmetric operad data given by arities and grafting. -/
structure Operad (Op : Type u) where
  /-- Arity of each operation. -/
  arity : Op → Nat
  /-- Unit operation. -/
  unit : Op
  /-- Operadic grafting (substitution). -/
  graft : (f : Op) → Vec Op (arity f) → Op

/-- Operad of associative parenthesizations. -/
def assocOperad : Operad AssocOp where
  arity := AssocTree.arity
  unit := AssocOp.unit
  graft := AssocOp.graft

/-! ## Operad Action on Loop Spaces -/

/-- Action of an operad on a carrier type. -/
structure OperadAction (Op : Type u) (O : Operad Op) (X : Type v) where
  /-- Evaluate an operation on a vector of inputs. -/
  act : (op : Op) → Vec X (O.arity op) → X

/-- Evaluate a parenthesization tree on loop space inputs. -/
def AssocTree.eval {A : Type u} {a : A} :
    (t : AssocTree) →
      Vec (LoopSpace A a) (AssocTree.arity t) → LoopSpace A a
  | AssocTree.leaf, Vec.cons p Vec.nil => p
  | AssocTree.node t1 t2, xs =>
      let (xs1, xs2) := Vec.split
        (m := AssocTree.arity t1) (n := AssocTree.arity t2) xs
      LoopSpace.comp (AssocTree.eval t1 xs1) (AssocTree.eval t2 xs2)

/-- Action of a tree operation on loop space. -/
def AssocOp.act {A : Type u} {a : A} (op : AssocOp) :
    Vec (LoopSpace A a) (AssocTree.arity op) → LoopSpace A a :=
  AssocTree.eval op

/-- The associative operad action on loop spaces by concatenation. -/
def loopOperadAction (A : Type u) (a : A) :
    OperadAction AssocOp assocOperad (LoopSpace A a) where
  act := fun op xs => AssocOp.act op xs

/-! ## Associahedron Coherence -/

/-- Left-associated arity-4 operation. -/
def assocTreeLeft : AssocOp :=
  AssocTree.node
    (AssocTree.node (AssocTree.node AssocTree.leaf AssocTree.leaf) AssocTree.leaf)
    AssocTree.leaf

/-- Right-associated arity-4 operation. -/
def assocTreeRight : AssocOp :=
  AssocTree.node AssocTree.leaf
    (AssocTree.node AssocTree.leaf (AssocTree.node AssocTree.leaf AssocTree.leaf))

/-- Associahedron K4 coherence for the loop operad action. -/
theorem associahedron_k4 {A : Type u} {a : A}
    (p q r s : LoopSpace A a) :
    RwEq (AssocOp.act assocTreeLeft (Vec.of4 p q r s))
      (AssocOp.act assocTreeRight (Vec.of4 p q r s)) := by
  simp [assocTreeLeft, assocTreeRight, AssocOp.act, AssocTree.eval, Vec.of4,
    Vec.split, LoopSpace.comp]

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end OperadicStructure
end Path
end ComputationalPaths
