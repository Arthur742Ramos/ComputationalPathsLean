/-
# Cohomology via Computational Paths

Cochains, coboundary operator, cocycles and coboundaries, cohomology classes,
long exact sequence aspects, cup product, connecting homomorphism,
graded ring structure, naturality of coboundary.

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

/-- Double negation is identity. -/
def neg_neg (G : AbGroup) (a : G.carrier) : Path (G.neg (G.neg a)) a := by
  let nna := G.neg (G.neg a)
  exact Path.trans
    (Path.symm (G.add_zero nna))
    (Path.trans
      (Path.congrArg (G.add nna) (Path.symm (G.neg_add a)))
      (Path.trans
        (Path.symm (G.add_assoc nna (G.neg a) a))
        (Path.trans
          (Path.congrArg (G.add · a) (G.neg_add (G.neg a)))
          (G.zero_add a))))

/-- Addition is left-cancellative via paths. -/
def add_cancel_left (G : AbGroup) (a b : G.carrier) :
    Path (G.add a (G.add (G.neg a) b)) b :=
  Path.trans
    (Path.symm (G.add_assoc a (G.neg a) b))
    (Path.trans
      (Path.congrArg (G.add · b) (G.add_neg a))
      (G.zero_add b))

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

/-- Delta preserves negation. -/
def delta_neg (C : CochainComplex) (n : Nat) (x : (C.group n).carrier) :
    Path (C.delta n ((C.group n).neg x))
         ((C.group (n + 1)).neg (C.delta n x)) := by
  let G := C.group (n + 1)
  let δx := C.delta n x
  let δnx := C.delta n ((C.group n).neg x)
  have h1 : Path (C.delta n ((C.group n).add ((C.group n).neg x) x)) G.zero :=
    Path.trans (Path.congrArg (C.delta n) ((C.group n).neg_add x)) (C.delta_zero n)
  have h2 : Path (C.delta n ((C.group n).add ((C.group n).neg x) x))
                  (G.add δnx δx) :=
    C.delta_add n ((C.group n).neg x) x
  have h3 : Path (G.add δnx δx) G.zero := Path.trans (Path.symm h2) h1
  exact Path.trans
    (Path.symm (G.add_zero δnx))
    (Path.trans
      (Path.congrArg (G.add δnx) (Path.symm (G.add_neg δx)))
      (Path.trans
        (Path.symm (G.add_assoc δnx δx (G.neg δx)))
        (Path.trans
          (Path.congrArg (G.add · (G.neg δx)) h3)
          (G.zero_add (G.neg δx)))))

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
    have h1 : Path (C.delta n ((C.group n).add ((C.group n).neg z.val) z.val)) G.zero :=
      Path.trans (Path.congrArg (C.delta n) ((C.group n).neg_add z.val)) (C.delta_zero n)
    have h2 : Path (C.delta n ((C.group n).add ((C.group n).neg z.val) z.val))
                    (G.add δneg (C.delta n z.val)) :=
      C.delta_add n ((C.group n).neg z.val) z.val
    have h3 : Path (G.add δneg (C.delta n z.val)) G.zero :=
      Path.trans (Path.symm h2) h1
    have h4 : Path (G.add δneg G.zero) δneg := G.add_zero δneg
    have h5 : Path (G.add δneg (C.delta n z.val)) (G.add δneg G.zero) :=
      Path.congrArg (G.add δneg) z.is_cocycle
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

/-- Negation of a coboundary is a coboundary. -/
def coboundary_neg (C : CochainComplex) (n : Nat) (b : Coboundary C n) :
    Coboundary C n where
  val := (C.group (n + 1)).neg b.val
  preimage := (C.group n).neg b.preimage
  is_coboundary :=
    Path.trans
      (Path.congrArg (C.group (n + 1)).neg b.is_coboundary)
      (Path.symm (delta_neg C n b.preimage))

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

/-- Cohomologous is symmetric (via group inverse unique lemma). -/
def cohomologous_symm (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C (n + 1))
    (h : Cohomologous C n z₁ z₂) :
    Cohomologous C n z₂ z₁ where
  witness := (C.group n).neg h.witness
  rel := by
    let G := C.group (n + 1)
    apply Path.ofEq
    -- Goal: G.add z₂.val (G.neg z₁.val) = C.delta n ((C.group n).neg h.witness)
    have h1 : G.add z₁.val (G.neg z₂.val) = C.delta n h.witness := h.rel.proof
    have h2 : C.delta n ((C.group n).neg h.witness) = G.neg (C.delta n h.witness) :=
      (delta_neg C n h.witness).proof
    -- h1: G.add z₁.val (G.neg z₂.val) = C.delta n h.witness
    -- rewrite δ w → z₁ + neg z₂ in h2
    rw [← h1] at h2
    -- h2 : C.delta n ((C.group n).neg h.witness) = G.neg (G.add z₁.val (G.neg z₂.val))
    -- Show: G.add z₂.val (G.neg z₁.val) = G.neg (G.add z₁.val (G.neg z₂.val))
    -- then conclude with h2.symm
    -- Proof that x + y = 0 → x = neg y (where x = z₂+neg z₁, y = z₁+neg z₂)
    have step1 : G.add (G.add z₂.val (G.neg z₁.val)) z₁.val = z₂.val :=
      ((G.add_assoc z₂.val (G.neg z₁.val) z₁.val).proof).trans
        ((_root_.congrArg (G.add z₂.val) (G.neg_add z₁.val).proof).trans (G.add_zero z₂.val).proof)
    have key : G.add (G.add z₂.val (G.neg z₁.val)) (G.add z₁.val (G.neg z₂.val)) = G.zero :=
      ((G.add_assoc (G.add z₂.val (G.neg z₁.val)) z₁.val (G.neg z₂.val)).proof.symm).trans
        ((_root_.congrArg (G.add · (G.neg z₂.val)) step1).trans (G.add_neg z₂.val).proof)
    -- x + y = 0 implies x = neg y
    let x := G.add z₂.val (G.neg z₁.val)
    let y := G.add z₁.val (G.neg z₂.val)
    have inv_unique : x = G.neg y :=
      ((G.add_zero x).proof.symm).trans
        ((_root_.congrArg (G.add x) (G.add_neg y).proof.symm).trans
          (((G.add_assoc x y (G.neg y)).proof.symm).trans
            ((_root_.congrArg (G.add · (G.neg y)) key).trans (G.zero_add (G.neg y)).proof)))
    exact inv_unique.trans h2.symm

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

/-- Adding zero class on the right gives same underlying value. -/
theorem cohomologyClassAdd_zero_val (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    (cohomologyClassAdd C n a (zeroCohomologyClass C n)).rep.val =
    (C.group n).add a.rep.val (C.group n).zero := rfl

/-- Adding zero class on the left gives same underlying value. -/
theorem cohomologyClassAdd_zero_left_val (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    (cohomologyClassAdd C n (zeroCohomologyClass C n) a).rep.val =
    (C.group n).add (C.group n).zero a.rep.val := rfl

/-- Negation then addition at value level. -/
theorem cohomologyClassNeg_add_val (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    (cohomologyClassAdd C n (cohomologyClassNeg C n a) a).rep.val =
    (C.group n).add ((C.group n).neg a.rep.val) a.rep.val := rfl

/-- Cohomology class addition is commutative at the value level. -/
def cohomologyClassAdd_comm_val (C : CochainComplex) (n : Nat) (a b : CohomologyClass C n) :
    Path (cohomologyClassAdd C n a b).rep.val (cohomologyClassAdd C n b a).rep.val :=
  (C.group n).add_comm a.rep.val b.rep.val

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

/-- Composing inject then project on zero yields zero via two paths. -/
def ses_compose_zero (ses : ShortExactSeq) (n : Nat) :
    Path (ses.project n (ses.inject n (ses.A.group n).zero)) (ses.C'.group n).zero :=
  Path.trans
    (Path.congrArg (ses.project n) (ses.inject_zero n))
    (ses.project_zero n)

/-- The two routes to zero (via exactness vs via zero-preservation) agree propositionally. -/
theorem ses_zero_coherence (ses : ShortExactSeq) (n : Nat) :
    (ses_compose_zero ses n).proof = (ses.exact_at_B n (ses.A.group n).zero).proof :=
  Subsingleton.elim _ _

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

/-- Cup of zero with zero factors through right-zero equally. -/
theorem cup_zero_zero_coherence {C : CochainComplex} (cp : CupProduct C) (p q : Nat) :
    (cp.cup_zero_left p q (C.group q).zero).proof =
    (cp.cup_zero_right p q (C.group p).zero).proof :=
  Subsingleton.elim _ _

/-! ## Graded Ring Structure -/

/-- An associative cup product. -/
structure AssociativeCup (C : CochainComplex) extends CupProduct C where
  cup_assoc : ∀ p q r (x : (C.group p).carrier) (y : (C.group q).carrier)
    (z : (C.group r).carrier),
    Path (Path.transport (D := fun n => (C.group n).carrier)
           (Path.ofEq (Nat.add_assoc p q r))
           (cup (p + q) r (cup p q x y) z))
         (cup p (q + r) x (cup q r y z))

/-- Graded commutativity for cup product. -/
structure GradedCommCup (C : CochainComplex) extends CupProduct C where
  cup_comm : ∀ p q (x : (C.group p).carrier) (y : (C.group q).carrier),
    Path (Path.transport (D := fun n => (C.group n).carrier)
           (Path.ofEq (Nat.add_comm p q))
           (cup p q x y))
         (cup q p y x)

/-! ## Connecting Homomorphism -/

/-- The connecting homomorphism in the long exact sequence. -/
structure ConnectingHom (ses : ShortExactSeq) where
  connecting : (n : Nat) → (ses.C'.group n).carrier → (ses.A.group (n + 1)).carrier
  connecting_zero : ∀ n, Path (connecting n (ses.C'.group n).zero) (ses.A.group (n + 1)).zero

/-- Connecting hom preserves zero. -/
def connecting_preserves_zero {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ch.connecting n (ses.C'.group n).zero) (ses.A.group (n + 1)).zero :=
  ch.connecting_zero n

/-- Composing inject with connecting on zero. -/
def connecting_inject_zero {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ses.inject (n + 1) (ch.connecting n (ses.C'.group n).zero)) (ses.B.group (n + 1)).zero :=
  Path.trans
    (Path.congrArg (ses.inject (n + 1)) (ch.connecting_zero n))
    (ses.inject_zero (n + 1))

/-! ## Degree Arithmetic -/

/-- δ² raises degree by 2. -/
theorem delta_squared_raises (n : Nat) : n + 1 + 1 = n + 2 := by omega

/-- Path: δ² degree. -/
def delta_squared_degree_path (n : Nat) : Path (n + 1 + 1) (n + 2) :=
  Path.ofEq (delta_squared_raises n)

/-- Cup product degree addition is associative. -/
theorem cup_degree_assoc (p q r : Nat) : p + q + r = p + (q + r) := by omega

/-- Path for cup degree associativity. -/
def cup_degree_assoc_path (p q r : Nat) : Path (p + q + r) (p + (q + r)) :=
  Path.ofEq (cup_degree_assoc p q r)

/-- Cup degree commutativity. -/
theorem cup_degree_comm (p q : Nat) : p + q = q + p := by omega

/-- Path: cup degree commutativity. -/
def cup_degree_comm_path (p q : Nat) : Path (p + q) (q + p) :=
  Path.ofEq (cup_degree_comm p q)

/-- Degree associativity then commutativity compose. -/
def degree_assoc_then_comm (p q r : Nat) : Path (p + q + r) (q + r + p) :=
  Path.trans (cup_degree_assoc_path p q r) (cup_degree_comm_path p (q + r))

/-- Transport along refl degree path is identity. -/
theorem transport_degree_refl {C : CochainComplex} (n : Nat) (x : (C.group n).carrier) :
    Path.transport (D := fun m => (C.group m).carrier) (Path.refl n) x = x := rfl

/-- Symmetry of degree path: transporting back and forth is identity. -/
theorem transport_degree_symm {C : CochainComplex} (n m : Nat) (h : n = m)
    (x : (C.group n).carrier) :
    Path.transport (D := fun k => (C.group k).carrier)
      (Path.symm (Path.ofEq h))
      (Path.transport (D := fun k => (C.group k).carrier)
        (Path.ofEq h) x) = x := by
  cases h
  simp [Path.transport]

end CohomologyPaths
end Topology
end Path
end ComputationalPaths
