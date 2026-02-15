/-
# Cohomology via Computational Paths

Cochains, coboundary operator, cocycles and coboundaries, cohomology groups,
long exact sequence aspects, cup product.

## References

- Hatcher, "Algebraic Topology"
- Bott & Tu, "Differential Forms in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace CohomologyPaths

universe u

/-! ## Abelian Group -/

/-- An abelian group for coefficients. -/
structure AbGroup where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  add_comm : ∀ a b, Path (add a b) (add b a)
  add_zero : ∀ a, Path (add a zero) a
  zero_add : ∀ a, Path (add zero a) a
  add_neg : ∀ a, Path (add a (neg a)) zero
  neg_add : ∀ a, Path (add (neg a) a) zero
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))

/-- Negation of zero is zero. -/
def neg_zero (G : AbGroup) : Path (G.neg G.zero) G.zero :=
  Path.trans (Path.symm (G.zero_add (G.neg G.zero))) (G.add_neg G.zero)

/-! ## Cochain Complex -/

/-- A cochain complex: graded abelian groups with coboundary δ. -/
structure CochainComplex where
  group : Nat → AbGroup
  delta : (n : Nat) → (group n).carrier → (group (n + 1)).carrier
  delta_zero : ∀ n, Path (delta n (group n).zero) (group (n + 1)).zero
  delta_add : ∀ n a b, Path (delta n ((group n).add a b))
                             ((group (n + 1)).add (delta n a) (delta n b))
  delta_squared : ∀ n (x : (group n).carrier),
    Path (delta (n + 1) (delta n x)) (group (n + 2)).zero

/-! ## Cocycles and Coboundaries -/

/-- A cocycle in degree n: element in ker(δ). -/
structure Cocycle (C : CochainComplex) (n : Nat) where
  val : (C.group n).carrier
  is_cocycle : Path (C.delta n val) (C.group (n + 1)).zero

/-- A coboundary in degree n+1: element in im(δ). -/
structure Coboundary (C : CochainComplex) (n : Nat) where
  val : (C.group (n + 1)).carrier
  preimage : (C.group n).carrier
  is_coboundary : Path val (C.delta n preimage)

/-- The zero cocycle. -/
def zeroCocycle (C : CochainComplex) (n : Nat) : Cocycle C n where
  val := (C.group n).zero
  is_cocycle := C.delta_zero n

/-- A coboundary is a cocycle (δ² = 0). -/
def coboundary_is_cocycle (C : CochainComplex) (n : Nat) (x : (C.group n).carrier) :
    Cocycle C (n + 1) where
  val := C.delta n x
  is_cocycle := C.delta_squared n x

/-- The zero coboundary. -/
def zeroCoboundary (C : CochainComplex) (n : Nat) : Coboundary C n where
  val := (C.group (n + 1)).zero
  preimage := (C.group n).zero
  is_coboundary := Path.symm (C.delta_zero n)

/-- δ of a cocycle is zero (restated). -/
def delta_cocycle_zero (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Path (C.delta n z.val) (C.group (n + 1)).zero :=
  z.is_cocycle

/-- Sum of cocycles is a cocycle. -/
def cocycle_add (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C n) :
    Cocycle C n where
  val := (C.group n).add z₁.val z₂.val
  is_cocycle :=
    Path.trans (C.delta_add n z₁.val z₂.val)
      (Path.trans
        (Path.congrArg ((C.group (n + 1)).add · (C.delta n z₂.val)) z₁.is_cocycle)
        (Path.trans
          (Path.congrArg ((C.group (n + 1)).add (C.group (n + 1)).zero ·) z₂.is_cocycle)
          ((C.group (n + 1)).zero_add (C.group (n + 1)).zero)))

/-- Negation of a cocycle is a cocycle. -/
def cocycle_neg (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Cocycle C n where
  val := (C.group n).neg z.val
  is_cocycle := by
    let G := C.group (n + 1)
    let δneg := C.delta n ((C.group n).neg z.val)
    -- δ(neg z + z) = δ(0) = 0
    have h1 : Path (C.delta n ((C.group n).add ((C.group n).neg z.val) z.val)) G.zero :=
      Path.trans (Path.congrArg (C.delta n) ((C.group n).neg_add z.val)) (C.delta_zero n)
    -- δ(neg z + z) = δ(neg z) + δ(z)
    have h2 : Path (C.delta n ((C.group n).add ((C.group n).neg z.val) z.val))
                    (G.add δneg (C.delta n z.val)) :=
      C.delta_add n ((C.group n).neg z.val) z.val
    -- δ(neg z) + δ(z) = 0
    have h3 : Path (G.add δneg (C.delta n z.val)) G.zero :=
      Path.trans (Path.symm h2) h1
    -- δ(neg z) + 0 = δ(neg z)
    have h4 : Path (G.add δneg G.zero) δneg := G.add_zero δneg
    -- δ(neg z) + δ(z) = δ(neg z) + 0  (since δ(z) = 0)
    have h5 : Path (G.add δneg (C.delta n z.val)) (G.add δneg G.zero) :=
      Path.congrArg (G.add δneg) z.is_cocycle
    -- Chain: δneg = δneg + 0 ←→ δneg + δz ←→ 0
    exact Path.trans (Path.symm h4) (Path.trans (Path.symm h5) h3)

/-- Sum of coboundaries is a coboundary. -/
def coboundary_add (C : CochainComplex) (n : Nat) (b₁ b₂ : Coboundary C n) :
    Coboundary C n where
  val := (C.group (n + 1)).add b₁.val b₂.val
  preimage := (C.group n).add b₁.preimage b₂.preimage
  is_coboundary :=
    Path.trans
      (Path.congrArg ((C.group (n + 1)).add · b₂.val) b₁.is_coboundary)
      (Path.trans
        (Path.congrArg ((C.group (n + 1)).add (C.delta n b₁.preimage) ·) b₂.is_coboundary)
        (Path.symm (C.delta_add n b₁.preimage b₂.preimage)))

/-! ## Cohomology Classes -/

/-- Two cocycles are cohomologous if they differ by a coboundary. -/
structure Cohomologous (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C (n + 1)) where
  witness : (C.group n).carrier
  rel : Path ((C.group (n + 1)).add z₁.val ((C.group (n + 1)).neg z₂.val))
             (C.delta n witness)

/-- Any cocycle is cohomologous to itself (witness = 0). -/
def cohomologous_refl (C : CochainComplex) (n : Nat) (z : Cocycle C (n + 1)) :
    Cohomologous C n z z where
  witness := (C.group n).zero
  rel := Path.trans ((C.group (n + 1)).add_neg z.val) (Path.symm (C.delta_zero n))

/-- A cohomology class (representative). -/
structure CohomologyClass (C : CochainComplex) (n : Nat) where
  rep : Cocycle C n

/-- Zero cohomology class. -/
def zeroCohomologyClass (C : CochainComplex) (n : Nat) : CohomologyClass C n where
  rep := zeroCocycle C n

/-- Addition of cohomology classes. -/
def cohomologyClassAdd (C : CochainComplex) (n : Nat)
    (a b : CohomologyClass C n) : CohomologyClass C n where
  rep := cocycle_add C n a.rep b.rep

/-- Negation of cohomology classes. -/
def cohomologyClassNeg (C : CochainComplex) (n : Nat)
    (a : CohomologyClass C n) : CohomologyClass C n where
  rep := cocycle_neg C n a.rep

/-- Adding zero class on the right. -/
def cohomologyClassAdd_zero (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    Path (cohomologyClassAdd C n a (zeroCohomologyClass C n)).rep.val
         ((C.group n).add a.rep.val (C.group n).zero) :=
  Path.refl _

/-! ## Short Exact Sequence -/

/-- A short exact sequence of cochain complexes (graded maps). -/
structure ShortExactSeq where
  A : CochainComplex
  B : CochainComplex
  C' : CochainComplex
  inject : (n : Nat) → (A.group n).carrier → (B.group n).carrier
  project : (n : Nat) → (B.group n).carrier → (C'.group n).carrier
  inject_zero : ∀ n, Path (inject n (A.group n).zero) (B.group n).zero
  project_zero : ∀ n, Path (project n (B.group n).zero) (C'.group n).zero
  exact_at_B : ∀ n x, Path (project n (inject n x)) (C'.group n).zero

/-- Exactness: p ∘ i = 0 (restated as path). -/
def ses_exact {ses : ShortExactSeq} (n : Nat) (x : (ses.A.group n).carrier) :
    Path (ses.project n (ses.inject n x)) (ses.C'.group n).zero :=
  ses.exact_at_B n x

/-- Injection preserves zero (restated). -/
def ses_inject_zero (ses : ShortExactSeq) (n : Nat) :
    Path (ses.inject n (ses.A.group n).zero) (ses.B.group n).zero :=
  ses.inject_zero n

/-- Projection preserves zero (restated). -/
def ses_project_zero (ses : ShortExactSeq) (n : Nat) :
    Path (ses.project n (ses.B.group n).zero) (ses.C'.group n).zero :=
  ses.project_zero n

/-! ## Cup Product -/

/-- A cup product on a cochain complex. -/
structure CupProduct (C : CochainComplex) where
  cup : (p q : Nat) → (C.group p).carrier → (C.group q).carrier → (C.group (p + q)).carrier
  cup_zero_left : ∀ p q y, Path (cup p q (C.group p).zero y) (C.group (p + q)).zero
  cup_zero_right : ∀ p q x, Path (cup p q x (C.group q).zero) (C.group (p + q)).zero

/-- Cup with zero on left. -/
def cup_zero_left_val {C : CochainComplex} (cp : CupProduct C) (p q : Nat)
    (y : (C.group q).carrier) :
    Path (cp.cup p q (C.group p).zero y) (C.group (p + q)).zero :=
  cp.cup_zero_left p q y

/-- Cup with zero on right. -/
def cup_zero_right_val {C : CochainComplex} (cp : CupProduct C) (p q : Nat)
    (x : (C.group p).carrier) :
    Path (cp.cup p q x (C.group q).zero) (C.group (p + q)).zero :=
  cp.cup_zero_right p q x

/-- Cup of zero cocycles is zero. -/
def cup_zero_cocycles {C : CochainComplex} (cp : CupProduct C) (p q : Nat) :
    Path (cp.cup p q (C.group p).zero (C.group q).zero) (C.group (p + q)).zero :=
  cp.cup_zero_left p q (C.group q).zero

/-! ## Degree Arithmetic -/

/-- δ raises degree by 1. -/
theorem delta_raises_degree (n : Nat) : n + 1 = n + 1 := rfl

/-- δ² raises degree by 2. -/
theorem delta_squared_raises (n : Nat) : n + 1 + 1 = n + 2 := by omega

/-- Path: δ² degree. -/
def delta_squared_degree_path (n : Nat) : Path (n + 1 + 1) (n + 2) :=
  Path.ofEq (delta_squared_raises n)

/-- Cup product degree addition. -/
theorem cup_degree_add (p q : Nat) : p + q = p + q := rfl

/-- Cup is commutative in degree (abstractly). -/
theorem cup_degree_comm (p q : Nat) : p + q = q + p := by omega

/-- Path: cup degree commutativity. -/
def cup_degree_comm_path (p q : Nat) : Path (p + q) (q + p) :=
  Path.ofEq (cup_degree_comm p q)

end CohomologyPaths
end Topology
end Path
end ComputationalPaths
