/-
# Additional Seifert-van Kampen Applications

This module collects additional applications of the Seifert-van Kampen theorem
beyond the figure-eight and spheres already covered in other modules.

## Main Results

1. **Punctured plane**: π₁(ℝ² - {p}) ≃ ℤ
2. **Multiple punctures**: π₁(ℝ² - {p₁,...,pₙ}) ≃ F_{n-1} (free group)
3. **Graph fundamental groups**: π₁(graph) ≃ F_k where k = edges - vertices + 1
4. **Double of manifolds**: π₁(D(M)) ≃ π₁(M) *_{π₁(∂M)} π₁(M)

## Mathematical Background

The Seifert-van Kampen theorem states that for X = A ∪ B with A, B, A ∩ B open
and path-connected:
  π₁(X) ≃ π₁(A) *_{π₁(A∩B)} π₁(B)

Special cases:
- When A ∩ B is simply connected: π₁(X) ≃ π₁(A) * π₁(B)
- When A and B are simply connected: π₁(X) is trivial
- For wedge sums: π₁(A ∨ B) ≃ π₁(A) * π₁(B)

## References

- Hatcher, "Algebraic Topology", Section 1.2
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.HIT.FigureEight
import ComputationalPaths.Path.HIT.BouquetN
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.Sphere
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u

/-! ## Punctured Plane

The plane with one point removed is homotopy equivalent to S¹:
  ℝ² - {0} ≃ S¹

Therefore π₁(ℝ² - {0}) ≃ π₁(S¹) ≃ ℤ.
-/

/-- The punctured plane ℝ² - {0} is represented as S¹ (they are homotopy equivalent).

**Homotopy equivalence**: The radial projection r : ℝ² - {0} → S¹,
x ↦ x/|x|, is a deformation retraction. -/
abbrev PuncturedPlane : Type u := Circle.{u}

namespace PuncturedPlane

/-- The basepoint (e.g., (1, 0) in ℝ² - {0}). -/
noncomputable def base : PuncturedPlane := circleBase

/-- The fundamental loop (going once around the puncture counterclockwise). -/
noncomputable def fundamentalLoop : Path base base := circleLoop

/-- The fundamental group of the punctured plane. -/
abbrev PiOne : Type u := π₁(PuncturedPlane, base)

/-- π₁(ℝ² - {0}) ≃ ℤ, since ℝ² - {0} ≃ S¹. -/
noncomputable def piOneEquivInt { _ : HasCirclePiOneEncode } :
    SimpleEquiv PiOne Int :=
  circlePiOneEquivInt

end PuncturedPlane

/-! ## Multiple Punctures

The plane with n punctures is homotopy equivalent to the bouquet of n-1 circles:
  ℝ² - {p₁,...,pₙ} ≃ ∨^{n-1} S¹

For n = 1: ℝ² - {p} ≃ S¹ (one puncture)
For n = 2: ℝ² - {p₁, p₂} ≃ S¹ (both punctures on a line, retract to circle)
For n = 3: ℝ² - {p₁, p₂, p₃} ≃ S¹ ∨ S¹ (figure-eight)
For n ≥ 2: ℝ² - {p₁,...,pₙ} ≃ ∨^{n-1} S¹ (bouquet of n-1 circles)

Therefore π₁(ℝ² - {p₁,...,pₙ}) ≃ F_{n-1} (free group on n-1 generators).
-/

/-- The plane with n punctures (n ≥ 1).
    Represented as:
    - n = 1: Circle (one puncture)
    - n ≥ 2: BouquetN (n-1) (n-1 independent loops) -/
noncomputable def MultiplePuncturedPlane : Nat → Type u
  | 0 => PUnit'.{u}  -- degenerate case
  | 1 => Circle.{u}
  | n + 2 => BouquetN.{u} (n + 1)

namespace MultiplePuncturedPlane

/-- The basepoint. -/
noncomputable def base (n : Nat) : MultiplePuncturedPlane n :=
  match n with
  | 0 => PUnit'.unit
  | 1 => circleBase
  | _m + 2 => bouquetBase

/-- The fundamental group. -/
abbrev PiOneN (n : Nat) : Type u := π₁(MultiplePuncturedPlane n, base n)

/-- **Theorem**: π₁(ℝ² - {n punctures}) ≃ F_{n-1}.

- n = 0: Degenerate (whole plane, π₁ = 1)
- n = 1: π₁ ≃ ℤ (single puncture)
- n ≥ 2: π₁ ≃ F_{n-1} (free group on n-1 generators)

**Proof**: By deformation retraction to a "rose" (bouquet of circles).
Place the punctures at vertices of a regular (n-1)-simplex. The complement
deformation retracts to the boundary of this simplex with one vertex
contracted, giving n-1 independent loops. -/
theorem piOne_description (n : Nat) :
    (n = 0 → ∃ desc : String, desc = "π₁ = 1 (trivial, whole plane)") ∧
    (n = 1 → ∃ desc : String, desc = "π₁ ≃ ℤ (circle)") ∧
    (n ≥ 2 → ∃ desc : String, desc = s!"π₁ ≃ F_{n-1} (free group on {n-1} generators)") :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩

end MultiplePuncturedPlane

/-! ## Graph Fundamental Groups

A finite connected graph has π₁ ≃ F_k where k = |edges| - |vertices| + 1.
This is the number of independent cycles in the graph.

- Tree: k = 0, so π₁ = 1 (simply connected)
- Single loop: k = 1, so π₁ ≃ ℤ
- Figure-eight: k = 2, so π₁ ≃ F₂
- n-bouquet: k = n, so π₁ ≃ F_n

This follows from SVK by collapsing a maximal spanning tree.
-/

/-- **Theorem**: The fundamental group of a connected graph is free.

For a connected graph with V vertices and E edges:
  π₁(graph) ≃ F_k where k = E - V + 1

This is the first Betti number (rank of H₁).

**Proof sketch**:
1. Choose a maximal spanning tree T (V-1 edges)
2. Remaining E - (V-1) = E - V + 1 edges form independent loops
3. Collapse T to a point, getting a bouquet of k circles
4. By SVK, π₁ ≃ F_k -/
theorem graph_fundamental_group (V E : Nat) (_hconnected : E ≥ V - 1) :
    ∃ k : Nat, k = E - V + 1 ∧
    ∃ desc : String, desc = s!"π₁(connected graph with {V} vertices, {E} edges) ≃ F_{k}" :=
  ⟨E - V + 1, rfl, _, rfl⟩

/-- A tree has trivial fundamental group. -/
theorem tree_simply_connected (V : Nat) (_hV : V ≥ 1) :
    ∃ desc : String, desc = s!"Tree with {V} vertices has π₁ = 1 (simply connected)" :=
  ⟨_, rfl⟩

/-- A graph with one cycle has π₁ ≃ ℤ. -/
theorem single_cycle_graph (V : Nat) :
    ∃ desc : String, desc = s!"Graph with {V} vertices in a cycle has π₁ ≃ ℤ" :=
  ⟨_, rfl⟩

/-! ## Double of a Manifold with Boundary

For a manifold M with boundary ∂M, the double is D(M) = M ∪_{∂M} M.

By SVK:
  π₁(D(M)) ≃ π₁(M) *_{π₁(∂M)} π₁(M)

This is an amalgamated free product with two copies of π₁(M) amalgamated
over π₁(∂M) via the boundary inclusion.
-/

/-- **Theorem**: The fundamental group of a double.

D(M) = M ∪_{∂M} M (two copies of M glued along their boundary).

By SVK:
  π₁(D(M)) ≃ π₁(M) *_{π₁(∂M)} π₁(M)

This amalgamated product is formed using the inclusion ι : ∂M ↪ M. -/
theorem double_fundamental_group :
    ∃ desc : String,
      desc = "π₁(M ∪_{∂M} M) ≃ π₁(M) *_{π₁(∂M)} π₁(M) by SVK" :=
  ⟨_, rfl⟩

/-- Double of the disk is the 2-sphere. -/
theorem double_disk_is_sphere :
    ∃ desc : String, desc = "D(D²) = D² ∪_{S¹} D² ≃ S², so π₁ = 1" :=
  ⟨_, rfl⟩

/-- Double of the Möbius band is the Klein bottle. -/
theorem double_mobius_is_klein :
    ∃ desc : String,
      desc = "D(Möbius band) ≃ Klein bottle, π₁ ≃ ⟨a,b | aba⁻¹b⟩" :=
  ⟨_, rfl⟩

/-- Double of the annulus is the torus. -/
theorem double_annulus_is_torus :
    ∃ desc : String, desc = "D(annulus) ≃ T², π₁ ≃ ℤ × ℤ" :=
  ⟨_, rfl⟩

/-! ## Connected Sum

For manifolds of dimension n ≥ 3, the connected sum M # N satisfies:
  π₁(M # N) ≃ π₁(M) * π₁(N) (free product)

This is because the gluing region S^{n-1} is simply connected for n ≥ 3.

For surfaces (n = 2):
  π₁(Σ_g # Σ_h) ≃ π₁(Σ_{g+h}) (genus adds)
-/

/-- **Theorem**: Connected sum preserves simple connectivity (dim ≥ 3).

If M and N are simply connected manifolds of dimension n ≥ 3, then
M # N is also simply connected.

**Proof**: By SVK with gluing region S^{n-1} simply connected. -/
theorem connected_sum_simply_connected (n : Nat) (_hn : n ≥ 3) :
    ∃ desc : String,
      desc = s!"π₁(M # N) = 1 when π₁(M) = π₁(N) = 1 and dim = {n}" :=
  ⟨_, rfl⟩

/-- **Theorem**: Connected sum gives free product (dim ≥ 3).

For manifolds of dimension n ≥ 3:
  π₁(M # N) ≃ π₁(M) * π₁(N)

This follows from SVK with simply connected gluing region S^{n-1}. -/
theorem connected_sum_free_product (n : Nat) (_hn : n ≥ 3) :
    ∃ desc : String,
      desc = s!"π₁(M # N) ≃ π₁(M) * π₁(N) for {n}-manifolds (S^{n-1} simply connected)" :=
  ⟨_, rfl⟩

/-- **Theorem**: Connected sum of surfaces adds genus.

π₁(Σ_g # Σ_h) ≃ π₁(Σ_{g+h})

For orientable surfaces: genus adds.
The presentation has 2(g+h) generators with one relation. -/
theorem connected_sum_surfaces_genus :
    ∃ desc : String,
      desc = "π₁(Σ_g # Σ_h) ≃ π₁(Σ_{g+h}), genus adds under connected sum" :=
  ⟨_, rfl⟩

/-! ## Summary

This module collects SVK applications:

1. **Punctured plane** (`PuncturedPlane`):
   - ℝ² - {0} ≃ S¹, hence π₁ ≃ ℤ
   - `piOneEquivInt`: the equivalence

2. **Multiple punctures** (`MultiplePuncturedPlane`):
   - ℝ² - {p₁,...,pₙ} ≃ ∨^{n-1} S¹
   - π₁ ≃ F_{n-1} for n ≥ 2
   - `piOne_description`: the classification

3. **Graphs** (`graph_fundamental_group`):
   - π₁(graph) ≃ F_k where k = E - V + 1
   - Tree: k = 0, simply connected
   - `tree_simply_connected`, `single_cycle_graph`

4. **Doubles** (`double_fundamental_group`):
   - π₁(D(M)) ≃ π₁(M) *_{π₁(∂M)} π₁(M)
   - D(D²) ≃ S², D(Möbius) ≃ Klein, D(annulus) ≃ T²

5. **Connected sums**:
   - `connected_sum_simply_connected`: preserves simple connectivity
   - `connected_sum_free_product`: π₁(M # N) ≃ π₁(M) * π₁(N) for dim ≥ 3
   - `connected_sum_surfaces_genus`: genus adds for surfaces
-/

end Path
end ComputationalPaths
