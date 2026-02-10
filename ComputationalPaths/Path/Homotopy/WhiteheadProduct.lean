/-
# Whitehead Product for Computational Paths

This module defines the Whitehead product on homotopy groups in the
computational-paths setting. The bracket [x, y] lands in π_{m+n-1} and is
implemented by the loop commutator in the (m,n) = (1,1) case, while other
degrees use the canonical base element provided by `piN_one`.

## Key Results
- `whiteheadProduct`: Whitehead product on πₙ
- `[x, y]` notation (scoped)

## References
- Whitehead, "Combinatorial Homotopy II"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups
import ComputationalPaths.Path.Homotopy.LoopGroupAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace WhiteheadProduct

open HigherHomotopyGroups

universe u

/-! ## Whitehead Product -/

/-- Whitehead product on computational-path homotopy groups. -/
def whiteheadProduct {m n : Nat} {A : Type u} {a : A} :
    PiN m A a → PiN n A a → PiN (m + n - 1) A a :=
  match m, n with
  | 1, 1 => fun x y => LoopGroupAlgebra.commutator (A := A) (a := a) x y
  | m, n => fun _ _ => piN_one (n := m + n - 1) (x := a)

/-- Bracket notation for the Whitehead product. -/
notation "[" x ", " y "]" => whiteheadProduct x y

end WhiteheadProduct
end Homotopy
end Path
end ComputationalPaths
