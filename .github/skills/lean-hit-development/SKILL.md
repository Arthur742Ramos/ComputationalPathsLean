---
name: lean-hit-development
description: Guides adding new computational-path constructions to the ComputationalPaths library. Use when defining new spaces, π₁ calculations, encode-decode proofs, or adding new topological constructions.
---

# Computational Path Construction Development

Add new computational-path constructions to the ComputationalPaths library.

## File Location

`ComputationalPaths/Path/CompPath/YourSpace.lean`

## Required Structure

```lean
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths.Path.CompPath

/-! ## Point type and basepoint -/

inductive YourSpace : Type u
  | base : YourSpace

@[simp] def yourSpaceBase : YourSpace := YourSpace.base

/-! ## Path expressions with generators -/

inductive YourSpaceExpr : YourSpace → YourSpace → Type u
  | loop : YourSpaceExpr yourSpaceBase yourSpaceBase
  | refl (a : YourSpace) : YourSpaceExpr a a
  | symm {a b} (p : YourSpaceExpr a b) : YourSpaceExpr b a
  | trans {a b c} (p : YourSpaceExpr a b) (q : YourSpaceExpr b c) : YourSpaceExpr a c

/-! ## Relation, quotient, and encode/decode -/

def yourSpaceRel : YourSpaceExpr yourSpaceBase yourSpaceBase →
  YourSpaceExpr yourSpaceBase yourSpaceBase → Prop := ...

def yourSpaceSetoid : Setoid (YourSpaceExpr yourSpaceBase yourSpaceBase) := ...

abbrev yourSpacePiOne : Type u := Quot yourSpaceSetoid.r

noncomputable def encode : yourSpacePiOne → Presentation := ...
noncomputable def decode : Presentation → yourSpacePiOne := ...

theorem decode_encode : decode (encode x) = x := by
  -- quotient induction
  ...

theorem encode_decode : encode (decode y) = y := by
  -- quotient induction
  ...

noncomputable def piOneEquiv : SimpleEquiv yourSpacePiOne Presentation := ...

end ComputationalPaths.Path.CompPath
```

## Checklist

1. Define the point type and basepoint
2. Define path expressions and generators
3. Provide a relation/normal form and a quotient for π₁
4. Implement encode/decode over the quotient
5. Prove round-trip properties
6. Add to imports in `ComputationalPaths/Path.lean`
7. Update README

## Common Constructions

| Space | Computational-path model |
|------|---------------------------|
| Circle (S¹) | One basepoint, one loop generator |
| Torus (T²) | Product of circle constructions |
| Sphere (S²) | Suspension/pushout-based loop triviality |
| Wedge (A ∨ B) | Pushout of basepoints, free product on π₁ |
