---
name: lean-hit-development
description: Guides adding new computational-path constructions to the ComputationalPaths library. Use when defining new spaces, pi1 calculations, encode-decode proofs, or adding new topological constructions.
---

# Computational Path Construction Development

This skill guides implementation of new computational-path spaces in the ComputationalPaths Lean 4 library. The goal is to define spaces using inductive point types and explicit path-expression syntax, then quotient by a relation and build encode-decode proofs without introducing new axioms.

## File Location

New constructions go in `ComputationalPaths/Path/CompPath/YourSpace.lean`.

## Required Module Structure

```lean
/--
# [Space Name] via computational paths

Brief mathematical description of the space.

## Key Results
- `yourSpaceBase`: basepoint
- `yourSpaceLoopExpr`: loop generator expression (if present)
- `piOneEquiv*`: pi1 equivalence when available
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path.CompPath

universe u

/-! ## Point type and basepoint -/

inductive YourSpace : Type u
  | base : YourSpace

@[simp] def yourSpaceBase : YourSpace := YourSpace.base

/-! ## Path expressions and generators -/

inductive YourSpaceExpr : YourSpace → YourSpace → Type u
  | loop : YourSpaceExpr yourSpaceBase yourSpaceBase
  | refl (a : YourSpace) : YourSpaceExpr a a
  | symm {a b} (p : YourSpaceExpr a b) : YourSpaceExpr b a
  | trans {a b c} (p : YourSpaceExpr a b) (q : YourSpaceExpr b c) : YourSpaceExpr a c

/-! ## Relation, quotient, and pi1 -/

def yourSpaceRel : YourSpaceExpr yourSpaceBase yourSpaceBase →
  YourSpaceExpr yourSpaceBase yourSpaceBase → Prop := ...

def yourSpaceSetoid : Setoid (YourSpaceExpr yourSpaceBase yourSpaceBase) := ...

abbrev yourSpacePiOne : Type u := Quot yourSpaceSetoid.r

/-! ## Encode-decode -/

noncomputable def encode : yourSpacePiOne → Presentation := ...
noncomputable def decode : Presentation → yourSpacePiOne := ...

theorem decode_encode (x : yourSpacePiOne) : decode (encode x) = x := by
  -- quotient induction
  ...

theorem encode_decode (y : Presentation) : encode (decode y) = y := by
  -- quotient induction
  ...

noncomputable def piOneEquiv : SimpleEquiv yourSpacePiOne Presentation := ...

end Path.CompPath
end ComputationalPaths
```

## Checklist for New Constructions

1. Define the point type and basepoint.
2. Define path expressions and any generators.
3. Provide a relation or normal form for loops.
4. Define the quotient for pi1 (or path classes).
5. Implement encode/decode and prove round-trip properties.
6. Add to imports in `ComputationalPaths/Path.lean`.
7. Update README with the new result.

## Common Patterns

- Circle: one basepoint, one loop generator, encode via winding number.
- Torus: product of circle constructions and the pi1 product theorem.
- Pushout/wedge: quotient-based pushout plus SVK encode/decode interfaces.
- Sphere: suspension or pushout arguments for pi1 triviality.

## Key Imports

```lean
import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic.Congruence
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.CompPath.CircleCompPath
```

## Axiom Policy

Avoid new axioms. If an interface is needed, prefer Prop-level typeclass assumptions and keep them local to the smallest scope possible.
