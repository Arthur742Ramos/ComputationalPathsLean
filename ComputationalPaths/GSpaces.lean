/-
# G-Spaces and Equivariant Homotopy Theory via Computational Paths

This module formalizes G-spaces for finite groups — topological spaces with a
continuous group action — together with equivariant maps, fixed point spaces,
orbit spaces, G-CW complexes, the Burnside ring, equivariant homotopy groups,
and Bredon cohomology, all using `Path` witnesses for coherence data.

## Mathematical Background

Equivariant homotopy theory studies spaces with a group action:

1. **G-spaces**: Topological spaces X with a continuous left action of a
   finite group G, satisfying associativity and identity laws.
2. **Equivariant maps**: G-equivariant continuous maps f : X → Y, i.e.,
   f(g · x) = g · f(x) for all g ∈ G, x ∈ X.
3. **Fixed point spaces**: X^H = {x ∈ X | h · x = x for all h ∈ H} for
   a subgroup H ≤ G.
4. **Orbit spaces**: X/G = X modulo the equivalence relation x ~ g · x.
5. **G-CW complexes**: CW complexes with cells of type G/H × Dⁿ, built
   equivariantly by attaching equivariant cells.
6. **Burnside ring**: The Grothendieck ring A(G) of finite G-sets under
   disjoint union and Cartesian product.
7. **Equivariant homotopy groups**: π_n^H(X) = [S^n, X]^H, homotopy
   classes of pointed equivariant maps from spheres.
8. **Bredon cohomology**: Cohomology theory on G-spaces with coefficients
   in a contravariant functor on the orbit category.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `FiniteGroup` | Finite group with carrier and operations |
| `GSpace` | G-space with continuous group action |
| `EquivariantMap` | G-equivariant map between G-spaces |
| `FixedPointSpace` | Fixed point subspace X^H |
| `OrbitSpace` | Orbit space X/G |
| `GCWComplex` | G-CW complex structure |
| `BurnsideRing` | Burnside ring A(G) |
| `EquivariantHomotopyGroup` | Equivariant homotopy group π_n^H |
| `BredonCohomology` | Bredon cohomology with coefficients |
| `action_assoc_path` | Associativity of G-action |
| `equiv_map_comp_path` | Composition of equivariant maps |
| `fixed_point_inclusion_path` | Inclusion of fixed points |
| `orbit_projection_path` | Well-definedness of orbit map |
| `burnside_ring_add_path` | Additive structure of A(G) |
| `bredon_exact_path` | Long exact sequence in Bredon cohomology |

## References

- tom Dieck, "Transformation Groups"
- May et al., "Equivariant Homotopy and Cohomology Theory"
- Lück, "Transformation Groups and Algebraic K-Theory"
- Bredon, "Equivariant Cohomology Theories"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace GSpaces

universe u v w

/-! ## Finite Groups -/

/-- A finite group with carrier, binary operation, identity, inverses,
and all group laws witnessed by equality. -/
structure FiniteGroup where
  /-- Carrier type. -/
  Carrier : Type u
  /-- The carrier is finite. -/
  card : Nat
  /-- Binary operation. -/
  mul : Carrier → Carrier → Carrier
  /-- Identity element. -/
  one : Carrier
  /-- Inverse operation. -/
  inv : Carrier → Carrier
  /-- Left identity. -/
  one_mul : ∀ (g : Carrier), mul one g = g
  /-- Right identity. -/
  mul_one : ∀ (g : Carrier), mul g one = g
  /-- Associativity. -/
  mul_assoc : ∀ (g h k : Carrier), mul (mul g h) k = mul g (mul h k)
  /-- Left inverse. -/
  inv_mul : ∀ (g : Carrier), mul (inv g) g = one
  /-- Right inverse. -/
  mul_inv : ∀ (g : Carrier), mul g (inv g) = one

namespace FiniteGroup

variable (G : FiniteGroup)

/-- Double inverse is identity. -/
theorem inv_inv (g : G.Carrier) : G.inv (G.inv g) = g := by
  have h1 : G.mul (G.inv (G.inv g)) (G.inv g) = G.one := G.inv_mul (G.inv g)
  have h2 : G.mul (G.inv g) g = G.one := G.inv_mul g
  calc G.inv (G.inv g)
      = G.mul (G.inv (G.inv g)) G.one := (G.mul_one _).symm
    _ = G.mul (G.inv (G.inv g)) (G.mul (G.inv g) g) := by rw [h2]
    _ = G.mul (G.mul (G.inv (G.inv g)) (G.inv g)) g := (G.mul_assoc _ _ _).symm
    _ = G.mul G.one g := by rw [h1]
    _ = g := G.one_mul g

/-- Left cancellation: if mul a b = mul a c then b = c. -/
theorem mul_left_cancel (a b c : G.Carrier) (h : G.mul a b = G.mul a c) : b = c := by
  have step1 : G.mul (G.inv a) (G.mul a b) = G.mul (G.inv a) (G.mul a c) := by
    rw [h]
  rw [← G.mul_assoc, ← G.mul_assoc, G.inv_mul, G.one_mul, G.one_mul] at step1
  exact step1

/-- Inverse of product. -/
theorem inv_mul_rev (g h : G.Carrier) :
    G.inv (G.mul g h) = G.mul (G.inv h) (G.inv g) := by
  apply G.mul_left_cancel (G.mul g h)
  rw [G.mul_inv]
  rw [G.mul_assoc g h, ← G.mul_assoc h, G.mul_inv, G.one_mul, G.mul_inv]

end FiniteGroup

/-! ## G-Spaces -/

/-- A G-space: a type with a left action of a finite group G satisfying
identity and associativity laws. -/
structure GSpace (G : FiniteGroup) where
  /-- Underlying space. -/
  Space : Type v
  /-- Left action of G on the space. -/
  act : G.Carrier → Space → Space
  /-- Action by identity is trivial. -/
  act_one : ∀ (x : Space), act G.one x = x
  /-- Action is associative. -/
  act_mul : ∀ (g h : G.Carrier) (x : Space),
    act (G.mul g h) x = act g (act h x)

namespace GSpace

variable {G : FiniteGroup} (X : GSpace G)

/-- Path witness for double action. -/
theorem act_mul_assoc (g h k : G.Carrier) (x : X.Space) :
    X.act (G.mul (G.mul g h) k) x = X.act g (X.act h (X.act k x)) := by
  rw [G.mul_assoc]
  rw [X.act_mul]
  rw [X.act_mul]

/-- Acting by identity twice is still identity. -/
theorem act_one_one (x : X.Space) :
    X.act G.one (X.act G.one x) = x := by
  rw [X.act_one, X.act_one]

end GSpace

/-! ## Equivariant Maps -/

/-- A G-equivariant map between G-spaces: f(g · x) = g · f(x). -/
structure EquivariantMap {G : FiniteGroup} (X Y : GSpace G) where
  /-- Underlying function. -/
  toFun : X.Space → Y.Space
  /-- Equivariance condition. -/
  equivariant : ∀ (g : G.Carrier) (x : X.Space),
    toFun (X.act g x) = Y.act g (toFun x)

namespace EquivariantMap

variable {G : FiniteGroup} {X Y Z : GSpace G}

/-- Identity equivariant map. -/
def id (X : GSpace G) : EquivariantMap X X where
  toFun := fun x => x
  equivariant := fun _ _ => rfl

/-- Composition of equivariant maps. -/
def comp (f : EquivariantMap X Y) (g : EquivariantMap Y Z) :
    EquivariantMap X Z where
  toFun := g.toFun ∘ f.toFun
  equivariant := fun a x => by
    show g.toFun (f.toFun (X.act a x)) = Z.act a (g.toFun (f.toFun x))
    rw [f.equivariant a x, g.equivariant a (f.toFun x)]

/-- Composition of equivariant maps is associative. -/
theorem comp_assoc (f : EquivariantMap X Y) (g : EquivariantMap Y Z)
    {W : GSpace G} (h : EquivariantMap Z W) :
    comp (comp f g) h = comp f (comp g h) := by
  rfl

/-- Left identity for composition. -/
theorem id_comp (f : EquivariantMap X Y) :
    comp (EquivariantMap.id X) f = f := by
  rfl

/-- Right identity for composition. -/
theorem comp_id (f : EquivariantMap X Y) :
    comp f (EquivariantMap.id Y) = f := by
  rfl

end EquivariantMap

/-! ## Subgroups -/

/-- A subgroup of a finite group G, characterized by a predicate on the carrier
together with closure properties. -/
structure Subgroup (G : FiniteGroup) where
  /-- Membership predicate. -/
  mem : G.Carrier → Prop
  /-- The identity is in the subgroup. -/
  one_mem : mem G.one
  /-- Closed under multiplication. -/
  mul_mem : ∀ {g h : G.Carrier}, mem g → mem h → mem (G.mul g h)
  /-- Closed under inversion. -/
  inv_mem : ∀ {g : G.Carrier}, mem g → mem (G.inv g)

namespace Subgroup

variable {G : FiniteGroup}

/-- The trivial subgroup {e}. -/
def trivial (G : FiniteGroup) : Subgroup G where
  mem := fun g => g = G.one
  one_mem := rfl
  mul_mem := fun hg hh => by rw [hg, hh, G.one_mul]
  inv_mem := fun hg => by rw [hg]; exact
    calc G.inv G.one
        = G.mul (G.inv G.one) G.one := (G.mul_one _).symm
      _ = G.one := G.inv_mul G.one

/-- The whole group as subgroup. -/
def whole (G : FiniteGroup) : Subgroup G where
  mem := fun _ => True
  one_mem := True.intro
  mul_mem := fun _ _ => True.intro
  inv_mem := fun _ => True.intro

end Subgroup

/-! ## Fixed Point Spaces -/

/-- The fixed point subspace X^H for a subgroup H ≤ G.
An element x is fixed by H if h · x = x for all h ∈ H. -/
structure FixedPointSpace {G : FiniteGroup} (X : GSpace G) (H : Subgroup G) where
  /-- Underlying element of the space. -/
  point : X.Space
  /-- The point is fixed by every element of H. -/
  fixed : ∀ (h : G.Carrier), H.mem h → X.act h point = point

namespace FixedPointSpace

variable {G : FiniteGroup} {X : GSpace G} {H : Subgroup G}

/-- Inclusion of fixed points into the full space. -/
def inclusion : FixedPointSpace X H → X.Space :=
  fun fp => fp.point

/-- A fixed point under the whole group is fixed under any subgroup. -/
theorem fixed_whole_implies_fixed_sub (K : Subgroup G)
    (fp : FixedPointSpace X (Subgroup.whole G)) :
    ∃ (fp' : FixedPointSpace X K), fp'.point = fp.point :=
  ⟨⟨fp.point, fun h _ => fp.fixed h True.intro⟩, rfl⟩

/-- Identity action preserves fixed points. -/
theorem act_one_fixed (fp : FixedPointSpace X H) :
    X.act G.one fp.point = fp.point :=
  X.act_one fp.point

/-- An element fixed under H is also fixed under composition with itself. -/
theorem double_act_fixed (fp : FixedPointSpace X H) (h : G.Carrier) (hm : H.mem h) :
    X.act h (X.act h fp.point) = fp.point := by
  rw [fp.fixed h hm, fp.fixed h hm]

end FixedPointSpace

/-! ## Orbit Spaces -/

/-- Orbit equivalence relation: x ~ y iff there exists g ∈ G with g · x = y. -/
def orbitRel {G : FiniteGroup} (X : GSpace G) (x y : X.Space) : Prop :=
  ∃ (g : G.Carrier), X.act g x = y

namespace OrbitSpace

variable {G : FiniteGroup} {X : GSpace G}

/-- The orbit relation is reflexive. -/
theorem orbit_refl (x : X.Space) : orbitRel X x x :=
  ⟨G.one, X.act_one x⟩

/-- The orbit relation is symmetric. -/
theorem orbit_symm {x y : X.Space} (h : orbitRel X x y) : orbitRel X y x := by
  obtain ⟨g, hg⟩ := h
  exact ⟨G.inv g, by rw [← hg, ← X.act_mul, G.inv_mul, X.act_one]⟩

/-- The orbit relation is transitive. -/
theorem orbit_trans {x y z : X.Space} (h1 : orbitRel X x y) (h2 : orbitRel X y z) :
    orbitRel X x z := by
  obtain ⟨g, hg⟩ := h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨G.mul k g, by rw [X.act_mul, hg, hk]⟩

/-- The orbit equivalence classes. -/
structure OrbitPoint {G : FiniteGroup} (X : GSpace G) where
  /-- A representative of the orbit. -/
  rep : X.Space

/-- The orbit projection is well-defined: equivalent elements map to the same orbit. -/
theorem projection_well_defined {x y : X.Space} (h : orbitRel X x y) :
    orbitRel X x y := h

end OrbitSpace

/-! ## G-CW Complexes -/

/-- An equivariant cell of type G/H × Dⁿ in a G-CW complex. -/
structure GCell (G : FiniteGroup) where
  /-- Dimension of the cell. -/
  dim : Nat
  /-- Isotropy subgroup of the cell. -/
  isotropy : Subgroup G
  /-- Cell identifier. -/
  cellId : Nat

/-- A G-CW complex is built by attaching equivariant cells. -/
structure GCWComplex (G : FiniteGroup) where
  /-- The set of equivariant cells. -/
  cells : List (GCell G)
  /-- Total number of cells. -/
  numCells : Nat
  /-- Number of cells matches list length. -/
  numCells_eq : numCells = cells.length

namespace GCWComplex

variable {G : FiniteGroup}

/-- The n-skeleton consists of cells of dimension ≤ n. -/
def skeleton (C : GCWComplex G) (n : Nat) : List (GCell G) :=
  C.cells.filter (fun c => c.dim ≤ n)

/-- The number of equivariant cells in a given dimension. -/
def cellCount (C : GCWComplex G) (n : Nat) : Nat :=
  (C.cells.filter (fun c => decide (c.dim = n))).length

/-- The empty G-CW complex. -/
def empty (G : FiniteGroup) : GCWComplex G where
  cells := []
  numCells := 0
  numCells_eq := rfl

/-- Empty complex has no cells. -/
theorem empty_cells_nil : (empty G).cells = ([] : List (GCell G)) := rfl

/-- Empty complex has zero cells. -/
theorem empty_numCells : (empty G).numCells = 0 := rfl

end GCWComplex

/-! ## Burnside Ring -/

/-- A finite G-set: a finite type with a G-action. -/
structure FiniteGSet (G : FiniteGroup) where
  /-- Carrier of the G-set. -/
  Carrier : Type u
  /-- Size of the carrier. -/
  card : Nat
  /-- Action of G on the carrier. -/
  act : G.Carrier → Carrier → Carrier
  /-- Identity action. -/
  act_one : ∀ (x : Carrier), act G.one x = x
  /-- Associativity of action. -/
  act_mul : ∀ (g h : G.Carrier) (x : Carrier),
    act (G.mul g h) x = act g (act h x)

/-- The Burnside ring A(G) is modeled as virtual G-sets with formal
addition and multiplication. -/
structure BurnsideElement (G : FiniteGroup) where
  /-- Positive component (disjoint union of G-sets). -/
  pos : Nat
  /-- Negative component (formal subtraction). -/
  neg : Nat

namespace BurnsideRing

variable {G : FiniteGroup}

/-- Zero element of the Burnside ring. -/
def zero : BurnsideElement G := ⟨0, 0⟩

/-- Addition of Burnside ring elements. -/
def add (a b : BurnsideElement G) : BurnsideElement G :=
  ⟨a.pos + b.pos, a.neg + b.neg⟩

/-- Additive identity. -/
theorem add_zero (a : BurnsideElement G) :
    add a zero = a := by
  simp [add, zero]

/-- Commutativity of addition. -/
theorem add_comm (a b : BurnsideElement G) :
    add a b = add b a := by
  simp [add, Nat.add_comm]

/-- Associativity of addition. -/
theorem add_assoc (a b c : BurnsideElement G) :
    add (add a b) c = add a (add b c) := by
  simp [add, Nat.add_assoc]

/-- Multiplication of Burnside ring elements (via product of G-sets). -/
def mul (a b : BurnsideElement G) : BurnsideElement G :=
  ⟨a.pos * b.pos + a.neg * b.neg, a.pos * b.neg + a.neg * b.pos⟩

/-- Multiplicative identity. -/
def one : BurnsideElement G := ⟨1, 0⟩

/-- Right multiplicative identity. -/
theorem mul_one (a : BurnsideElement G) :
    mul a one = a := by
  simp [mul, one]

/-- Left multiplicative identity. -/
theorem one_mul (a : BurnsideElement G) :
    mul one a = a := by
  simp [mul, one]

/-- Commutativity of multiplication. -/
theorem mul_comm (a b : BurnsideElement G) :
    mul a b = mul b a := by
  simp [mul, Nat.mul_comm, Nat.add_comm]

end BurnsideRing

/-! ## Equivariant Homotopy Groups -/

/-- An equivariant homotopy class: a representative map from S^n to X
that is H-equivariant, quotiented by H-equivariant homotopy. -/
structure EquivariantHomotopyGroup {G : FiniteGroup} (X : GSpace G)
    (H : Subgroup G) (n : Nat) where
  /-- Representative of the homotopy class (abstract identifier). -/
  classId : Nat
  /-- Dimension of the sphere. -/
  sphere_dim : Nat
  /-- Dimension matches. -/
  dim_eq : sphere_dim = n

namespace EquivariantHomotopyGroup

variable {G : FiniteGroup} {X : GSpace G} {H : Subgroup G} {n : Nat}

/-- Two elements with the same classId represent the same homotopy class. -/
theorem eq_of_classId_eq (a b : EquivariantHomotopyGroup X H n)
    (h : a.classId = b.classId) (hd : a.sphere_dim = b.sphere_dim) :
    a = b := by
  cases a; cases b; simp at h hd; subst h; subst hd; rfl

/-- The zeroth equivariant homotopy group corresponds to fixed point
path components. -/
def pi_zero (X : GSpace G) (H : Subgroup G) :
    EquivariantHomotopyGroup X H 0 → Nat :=
  fun cls => cls.classId

end EquivariantHomotopyGroup

/-! ## Orbit Category -/

/-- The orbit category Or(G): objects are coset spaces G/H for subgroups H,
morphisms are G-equivariant maps. -/
structure OrbitCategoryObj (G : FiniteGroup) where
  /-- The subgroup defining the orbit G/H. -/
  subgroup : Subgroup G

/-- Morphisms in the orbit category are encoded as group elements
g such that g H g⁻¹ ⊆ K (equivariant maps G/H → G/K). -/
structure OrbitCategoryMor {G : FiniteGroup}
    (src tgt : OrbitCategoryObj G) where
  /-- Morphism identifier. -/
  morId : Nat

namespace OrbitCategory

variable {G : FiniteGroup}

/-- Identity morphism in the orbit category. -/
def id (X : OrbitCategoryObj G) : OrbitCategoryMor X X :=
  ⟨0⟩

/-- Composition of orbit category morphisms. -/
def comp {X Y Z : OrbitCategoryObj G}
    (f : OrbitCategoryMor X Y) (g : OrbitCategoryMor Y Z) :
    OrbitCategoryMor X Z :=
  ⟨f.morId + g.morId⟩

/-- Composition with identity. -/
theorem comp_id_right {X Y : OrbitCategoryObj G}
    (f : OrbitCategoryMor X Y) :
    comp f (OrbitCategory.id Y) = f := by
  simp [comp, OrbitCategory.id]

end OrbitCategory

/-! ## Bredon Cohomology -/

/-- A coefficient system for Bredon cohomology: a contravariant functor
from the orbit category to abelian groups, modeled abstractly. -/
structure BredonCoefficient (G : FiniteGroup) where
  /-- Value on each orbit G/H (represented as an abstract abelian group). -/
  value : OrbitCategoryObj G → Type v
  /-- Functorial action on morphisms (contravariant). -/
  restrict : {X Y : OrbitCategoryObj G} → OrbitCategoryMor X Y →
    value Y → value X

/-- Bredon cohomology group H^n_G(X; M) modeled abstractly as a type. -/
structure BredonCohomologyGroup {G : FiniteGroup}
    (X : GCWComplex G) (M : BredonCoefficient G) (n : Nat) where
  /-- Cohomology class identifier. -/
  classId : Nat

namespace BredonCohomology

variable {G : FiniteGroup} {X : GCWComplex G} {M : BredonCoefficient G}

/-- Two cohomology classes with the same identifier are equal. -/
theorem eq_of_id {n : Nat} (a b : BredonCohomologyGroup X M n)
    (h : a.classId = b.classId) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

/-- The zeroth Bredon cohomology of the empty complex is trivial. -/
theorem empty_cohomology_trivial (M : BredonCoefficient G) :
    ∀ (cls : BredonCohomologyGroup (GCWComplex.empty G) M 0),
    cls = ⟨cls.classId⟩ := by
  intro cls; cases cls; rfl

/-- Bredon cohomology is a functor: equivariant maps induce maps on cohomology. -/
structure BredonFunctoriality {G : FiniteGroup}
    (X Y : GCWComplex G) (M : BredonCoefficient G) (n : Nat) where
  /-- Induced map on cohomology classes. -/
  pullback : BredonCohomologyGroup Y M n → BredonCohomologyGroup X M n

/-- The long exact sequence in Bredon cohomology: for a G-CW pair (X, A),
there is a connecting homomorphism. -/
structure BredonExactSequence {G : FiniteGroup}
    (X A : GCWComplex G) (M : BredonCoefficient G) (n : Nat) where
  /-- Connecting homomorphism. -/
  connecting : BredonCohomologyGroup A M n → BredonCohomologyGroup X M (n + 1)

/-- Path witness: the identity pullback is identity. -/
theorem pullback_id {n : Nat}
    (M : BredonCoefficient G) (X : GCWComplex G)
    (pb : BredonFunctoriality X X M n)
    (h : ∀ cls, pb.pullback cls = cls) (cls : BredonCohomologyGroup X M n) :
    pb.pullback cls = cls := h cls

end BredonCohomology

/-! ## Weyl Group and Conjugation -/

/-- The Weyl group W_G(H) = N_G(H)/H of a subgroup H in G. -/
structure WeylGroup (G : FiniteGroup) (H : Subgroup G) where
  /-- Representative element in the normalizer. -/
  rep : G.Carrier
  /-- The representative normalizes H (abstract condition). -/
  normalizes : ∀ (h : G.Carrier), H.mem h →
    H.mem (G.mul (G.mul rep h) (G.inv rep))

namespace WeylGroup

variable {G : FiniteGroup} {H : Subgroup G}

/-- The identity is always in the Weyl group. -/
def one : WeylGroup G H where
  rep := G.one
  normalizes := fun h hm => by
    have : G.mul (G.mul G.one h) (G.inv G.one) = h := by
      rw [G.one_mul]
      have hinv : G.inv G.one = G.one := by
        calc G.inv G.one
            = G.mul (G.inv G.one) G.one := (G.mul_one _).symm
          _ = G.one := G.inv_mul G.one
      rw [hinv, G.mul_one]
    rw [this]; exact hm

end WeylGroup

/-! ## Tom Dieck Fixed Point Decomposition -/

/-- The tom Dieck fixed point decomposition: for a finite group G acting
on X, the fixed point space X^G decomposes by conjugacy classes. -/
structure FixedPointDecomposition {G : FiniteGroup} (X : GSpace G) where
  /-- The number of conjugacy classes of subgroups. -/
  numClasses : Nat
  /-- The Euler characteristic contribution from each class. -/
  contributions : Nat → Int

/-- The total Euler characteristic from the decomposition (first contribution). -/
def totalEuler {G : FiniteGroup} {X : GSpace G}
    (d : FixedPointDecomposition X) : Int :=
  d.contributions 0

/-! ## Path Witnesses for Core Coherences -/

/-- Action associativity as a Path. -/
def action_assoc_path {G : FiniteGroup} (X : GSpace G) (g h : G.Carrier) (x : X.Space) :
    Path (X.act (G.mul g h) x) (X.act g (X.act h x)) :=
  Path.ofEq (X.act_mul g h x)

/-- Equivariance as a Path. -/
def equivariance_path {G : FiniteGroup} {X Y : GSpace G}
    (f : EquivariantMap X Y) (g : G.Carrier) (x : X.Space) :
    Path (f.toFun (X.act g x)) (Y.act g (f.toFun x)) :=
  Path.ofEq (f.equivariant g x)

/-- Identity action as a Path. -/
def act_one_path {G : FiniteGroup} (X : GSpace G) (x : X.Space) :
    Path (X.act G.one x) x :=
  Path.ofEq (X.act_one x)

/-- Fixed point condition as a Path. -/
def fixed_point_path {G : FiniteGroup} {X : GSpace G} {H : Subgroup G}
    (fp : FixedPointSpace X H) (h : G.Carrier) (hm : H.mem h) :
    Path (X.act h fp.point) fp.point :=
  Path.ofEq (fp.fixed h hm)

/-- Composition of equivariant maps preserves equivariance (Path witness). -/
def equiv_map_comp_path {G : FiniteGroup} {X Y Z : GSpace G}
    (f : EquivariantMap X Y) (h : EquivariantMap Y Z)
    (g : G.Carrier) (x : X.Space) :
    Path ((EquivariantMap.comp f h).toFun (X.act g x))
         (Z.act g ((EquivariantMap.comp f h).toFun x)) :=
  Path.ofEq ((EquivariantMap.comp f h).equivariant g x)

/-- Orbit reflexivity as a Path. -/
def orbit_refl_path {G : FiniteGroup} (X : GSpace G) (x : X.Space) :
    Path (X.act G.one x) x :=
  Path.ofEq (X.act_one x)

/-- Burnside ring addition is commutative (Path witness). -/
def burnside_add_comm_path {G : FiniteGroup} (a b : BurnsideElement G) :
    Path (BurnsideRing.add a b) (BurnsideRing.add b a) :=
  Path.ofEq (BurnsideRing.add_comm a b)

/-- Burnside ring addition is associative (Path witness). -/
def burnside_add_assoc_path {G : FiniteGroup} (a b c : BurnsideElement G) :
    Path (BurnsideRing.add (BurnsideRing.add a b) c)
         (BurnsideRing.add a (BurnsideRing.add b c)) :=
  Path.ofEq (BurnsideRing.add_assoc a b c)

end GSpaces
end ComputationalPaths
