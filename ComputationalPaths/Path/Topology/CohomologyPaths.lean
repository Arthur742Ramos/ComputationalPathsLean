/-
# Cohomology via Computational Paths

Cochains, coboundary operator, cocycles and coboundaries, cohomology classes,
cup product, short exact sequences, connecting homomorphism — all built with
genuine `Path` operations (`refl`, `trans`, `symm`, `congrArg`). Zero `Path.mk [Step.mk _ _ h] h`.

## References

- Hatcher, "Algebraic Topology"
- Bott & Tu, "Differential Forms in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace CohomologyPaths

universe u

/-! ## Abelian Group via Paths -/

/-- An abelian group for coefficients, with axioms as paths. -/
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

/-! ### Derived group laws -/

/-- 1. Negation of zero is zero. -/
noncomputable def neg_zero (G : AbGroup) : Path (G.neg G.zero) G.zero :=
  Path.trans (Path.symm (G.zero_add (G.neg G.zero))) (G.add_neg G.zero)

/-- 2. Double negation is identity. -/
noncomputable def neg_neg (G : AbGroup) (a : G.carrier) : Path (G.neg (G.neg a)) a :=
  Path.trans
    (Path.symm (G.add_zero (G.neg (G.neg a))))
    (Path.trans
      (Path.congrArg (G.add (G.neg (G.neg a))) (Path.symm (G.neg_add a)))
      (Path.trans
        (Path.symm (G.add_assoc (G.neg (G.neg a)) (G.neg a) a))
        (Path.trans
          (Path.congrArg (G.add · a) (G.neg_add (G.neg a)))
          (G.zero_add a))))

/-- 3. Left cancellation: a + (neg a + b) = b. -/
noncomputable def add_cancel_left (G : AbGroup) (a b : G.carrier) :
    Path (G.add a (G.add (G.neg a) b)) b :=
  Path.trans
    (Path.symm (G.add_assoc a (G.neg a) b))
    (Path.trans
      (Path.congrArg (G.add · b) (G.add_neg a))
      (G.zero_add b))

/-- 4. Right cancellation: (a + neg b) + b = a. -/
noncomputable def add_cancel_right (G : AbGroup) (a b : G.carrier) :
    Path (G.add (G.add a (G.neg b)) b) a :=
  Path.trans
    (G.add_assoc a (G.neg b) b)
    (Path.trans
      (Path.congrArg (G.add a) (G.neg_add b))
      (G.add_zero a))

/-- 5. neg distributes over add: neg(a + b) path to neg b + neg a. -/
noncomputable def neg_add_rev (G : AbGroup) (a b : G.carrier) :
    Path (G.add (G.neg b) (G.neg a)) (G.neg (G.add a b)) := by
  -- Show (neg b + neg a) + (a + b) = 0, so neg b + neg a = neg(a+b)
  -- We use the unique inverse property
  let lhs := G.add (G.neg b) (G.neg a)
  let rhs := G.add a b
  -- lhs + rhs = neg b + (neg a + (a + b)) via assoc
  -- = neg b + ((neg a + a) + b) via assoc
  -- = neg b + (0 + b) = neg b + b = 0
  have step1 : Path (G.add lhs rhs) (G.add (G.neg b) (G.add (G.neg a) rhs)) :=
    G.add_assoc (G.neg b) (G.neg a) rhs
  have step2 : Path (G.add (G.neg a) rhs) (G.add (G.neg a) (G.add a b)) :=
    Path.refl _
  have step3 : Path (G.add (G.neg a) (G.add a b)) (G.add (G.add (G.neg a) a) b) :=
    Path.symm (G.add_assoc (G.neg a) a b)
  have step4 : Path (G.add (G.add (G.neg a) a) b) (G.add G.zero b) :=
    Path.congrArg (G.add · b) (G.neg_add a)
  have step5 : Path (G.add G.zero b) b := G.zero_add b
  have inner : Path (G.add (G.neg a) rhs) b :=
    Path.trans step2 (Path.trans step3 (Path.trans step4 step5))
  have sum_zero : Path (G.add lhs rhs) (G.add (G.neg b) b) :=
    Path.trans step1 (Path.congrArg (G.add (G.neg b)) inner)
  have sum_is_zero : Path (G.add lhs rhs) G.zero :=
    Path.trans sum_zero (G.neg_add b)
  -- Now: lhs + rhs = 0 implies lhs = neg rhs
  -- lhs = lhs + 0 = lhs + (rhs + neg rhs) = (lhs + rhs) + neg rhs = 0 + neg rhs = neg rhs
  exact Path.trans
    (Path.symm (G.add_zero lhs))
    (Path.trans
      (Path.congrArg (G.add lhs) (Path.symm (G.add_neg rhs)))
      (Path.trans
        (Path.symm (G.add_assoc lhs rhs (G.neg rhs)))
        (Path.trans
          (Path.congrArg (G.add · (G.neg rhs)) sum_is_zero)
          (G.zero_add (G.neg rhs)))))

/-- 6. add is associative (4-fold, left). -/
noncomputable def add_assoc4_left (G : AbGroup) (a b c d : G.carrier) :
    Path (G.add (G.add (G.add a b) c) d) (G.add a (G.add b (G.add c d))) :=
  Path.trans (G.add_assoc (G.add a b) c d)
    (Path.trans (G.add_assoc a b (G.add c d)) (Path.refl _))

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

/-- 7. Delta preserves negation. -/
noncomputable def delta_neg (C : CochainComplex) (n : Nat) (x : (C.group n).carrier) :
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
  -- δnx + δx = 0 implies δnx = neg δx
  exact Path.trans
    (Path.symm (G.add_zero δnx))
    (Path.trans
      (Path.congrArg (G.add δnx) (Path.symm (G.add_neg δx)))
      (Path.trans
        (Path.symm (G.add_assoc δnx δx (G.neg δx)))
        (Path.trans
          (Path.congrArg (G.add · (G.neg δx)) h3)
          (G.zero_add (G.neg δx)))))

/-- 8. Delta applied to (a + neg a) is zero. -/
noncomputable def delta_add_neg (C : CochainComplex) (n : Nat) (a : (C.group n).carrier) :
    Path (C.delta n ((C.group n).add a ((C.group n).neg a))) (C.group (n + 1)).zero :=
  Path.trans (Path.congrArg (C.delta n) ((C.group n).add_neg a)) (C.delta_zero n)

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

/-- 9. The zero cocycle. -/
noncomputable def zeroCocycle (C : CochainComplex) (n : Nat) : Cocycle C n where
  val := (C.group n).zero
  is_cocycle := C.delta_zero n

/-- 10. A coboundary is a cocycle (δ² = 0). -/
noncomputable def coboundary_is_cocycle (C : CochainComplex) (n : Nat) (x : (C.group n).carrier) :
    Cocycle C (n + 1) where
  val := C.delta n x
  is_cocycle := C.delta_squared n x

/-- 11. The zero coboundary. -/
noncomputable def zeroCoboundary (C : CochainComplex) (n : Nat) : Coboundary C n where
  val := (C.group (n + 1)).zero
  preimage := (C.group n).zero
  is_coboundary := Path.symm (C.delta_zero n)

/-- 12. δ of a cocycle is zero. -/
noncomputable def delta_cocycle_zero (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Path (C.delta n z.val) (C.group (n + 1)).zero :=
  z.is_cocycle

/-- 13. Sum of cocycles is a cocycle. -/
noncomputable def cocycle_add (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C n) :
    Cocycle C n where
  val := (C.group n).add z₁.val z₂.val
  is_cocycle :=
    Path.trans (C.delta_add n z₁.val z₂.val)
      (Path.trans
        (Path.congrArg ((C.group (n + 1)).add · (C.delta n z₂.val)) z₁.is_cocycle)
        (Path.trans
          (Path.congrArg ((C.group (n + 1)).add (C.group (n + 1)).zero ·) z₂.is_cocycle)
          ((C.group (n + 1)).zero_add (C.group (n + 1)).zero)))

/-- 14. Negation of a cocycle is a cocycle. -/
noncomputable def cocycle_neg (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Cocycle C n where
  val := (C.group n).neg z.val
  is_cocycle := by
    let G := C.group (n + 1)
    let δneg := C.delta n ((C.group n).neg z.val)
    have h_neg_delta : Path δneg (G.neg (C.delta n z.val)) :=
      delta_neg C n z.val
    have h_delta_zero : Path (C.delta n z.val) G.zero := z.is_cocycle
    have h_neg_zero : Path (G.neg G.zero) G.zero := neg_zero G
    exact Path.trans h_neg_delta
      (Path.trans (Path.congrArg G.neg h_delta_zero) h_neg_zero)

/-- 15. Sum of coboundaries is a coboundary. -/
noncomputable def coboundary_add (C : CochainComplex) (n : Nat) (b₁ b₂ : Coboundary C n) :
    Coboundary C n where
  val := (C.group (n + 1)).add b₁.val b₂.val
  preimage := (C.group n).add b₁.preimage b₂.preimage
  is_coboundary :=
    Path.trans
      (Path.congrArg ((C.group (n + 1)).add · b₂.val) b₁.is_coboundary)
      (Path.trans
        (Path.congrArg ((C.group (n + 1)).add (C.delta n b₁.preimage) ·) b₂.is_coboundary)
        (Path.symm (C.delta_add n b₁.preimage b₂.preimage)))

/-- 16. Negation of a coboundary is a coboundary. -/
noncomputable def coboundary_neg (C : CochainComplex) (n : Nat) (b : Coboundary C n) :
    Coboundary C n where
  val := (C.group (n + 1)).neg b.val
  preimage := (C.group n).neg b.preimage
  is_coboundary :=
    Path.trans
      (Path.congrArg (C.group (n + 1)).neg b.is_coboundary)
      (Path.symm (delta_neg C n b.preimage))

/-- 17. Cocycle addition is commutative (at value level). -/
noncomputable def cocycle_add_comm (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C n) :
    Path (cocycle_add C n z₁ z₂).val (cocycle_add C n z₂ z₁).val :=
  (C.group n).add_comm z₁.val z₂.val

/-- 18. Cocycle addition is associative (at value level). -/
noncomputable def cocycle_add_assoc (C : CochainComplex) (n : Nat) (z₁ z₂ z₃ : Cocycle C n) :
    Path (cocycle_add C n (cocycle_add C n z₁ z₂) z₃).val
         (cocycle_add C n z₁ (cocycle_add C n z₂ z₃)).val :=
  (C.group n).add_assoc z₁.val z₂.val z₃.val

/-- 19. Adding zero cocycle on right. -/
noncomputable def cocycle_add_zero (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Path (cocycle_add C n z (zeroCocycle C n)).val z.val :=
  (C.group n).add_zero z.val

/-- 20. Adding zero cocycle on left. -/
noncomputable def cocycle_zero_add (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Path (cocycle_add C n (zeroCocycle C n) z).val z.val :=
  (C.group n).zero_add z.val

/-- 21. Cocycle + neg cocycle = zero cocycle (value level). -/
noncomputable def cocycle_add_neg_zero (C : CochainComplex) (n : Nat) (z : Cocycle C n) :
    Path (cocycle_add C n z (cocycle_neg C n z)).val (zeroCocycle C n).val :=
  (C.group n).add_neg z.val

/-! ## Cohomology Classes -/

/-- Two cocycles are cohomologous if they differ by a coboundary. -/
structure Cohomologous (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C (n + 1)) where
  witness : (C.group n).carrier
  rel : Path ((C.group (n + 1)).add z₁.val ((C.group (n + 1)).neg z₂.val))
             (C.delta n witness)

/-- 22. Any cocycle is cohomologous to itself (witness = 0). -/
noncomputable def cohomologous_refl (C : CochainComplex) (n : Nat) (z : Cocycle C (n + 1)) :
    Cohomologous C n z z where
  witness := (C.group n).zero
  rel := Path.trans ((C.group (n + 1)).add_neg z.val) (Path.symm (C.delta_zero n))

/-- 23. Cohomologous is symmetric. -/
noncomputable def cohomologous_symm (C : CochainComplex) (n : Nat) (z₁ z₂ : Cocycle C (n + 1))
    (h : Cohomologous C n z₁ z₂) :
    Cohomologous C n z₂ z₁ where
  witness := (C.group n).neg h.witness
  rel := by
    let G := C.group (n + 1)
    let Gn := C.group n
    -- We need: Path (G.add z₂.val (G.neg z₁.val)) (C.delta n (Gn.neg h.witness))
    -- h.rel : Path (G.add z₁.val (G.neg z₂.val)) (C.delta n h.witness)
    -- delta_neg gives: Path (C.delta n (Gn.neg h.witness)) (G.neg (C.delta n h.witness))
    -- So target = neg(delta h.witness) = neg(z₁ + neg z₂)
    -- We show z₂ + neg z₁ = neg(z₁ + neg z₂) via group theory
    let x := G.add z₂.val (G.neg z₁.val)
    let y := G.add z₁.val (G.neg z₂.val)
    -- Show x + y = 0
    have assoc1 : Path (G.add x y) (G.add (G.add z₂.val (G.neg z₁.val)) (G.add z₁.val (G.neg z₂.val))) :=
      Path.refl _
    have inner1 : Path (G.add (G.neg z₁.val) (G.add z₁.val (G.neg z₂.val)))
                       (G.add (G.add (G.neg z₁.val) z₁.val) (G.neg z₂.val)) :=
      Path.symm (G.add_assoc (G.neg z₁.val) z₁.val (G.neg z₂.val))
    have inner2 : Path (G.add (G.add (G.neg z₁.val) z₁.val) (G.neg z₂.val))
                       (G.add G.zero (G.neg z₂.val)) :=
      Path.congrArg (G.add · (G.neg z₂.val)) (G.neg_add z₁.val)
    have inner3 : Path (G.add G.zero (G.neg z₂.val)) (G.neg z₂.val) :=
      G.zero_add (G.neg z₂.val)
    have inner_combined : Path (G.add (G.neg z₁.val) y) (G.neg z₂.val) :=
      Path.trans inner1 (Path.trans inner2 inner3)
    have outer1 : Path (G.add x y) (G.add z₂.val (G.add (G.neg z₁.val) y)) :=
      G.add_assoc z₂.val (G.neg z₁.val) y
    have outer2 : Path (G.add z₂.val (G.add (G.neg z₁.val) y))
                       (G.add z₂.val (G.neg z₂.val)) :=
      Path.congrArg (G.add z₂.val) inner_combined
    have sum_zero : Path (G.add x y) G.zero :=
      Path.trans outer1 (Path.trans outer2 (G.add_neg z₂.val))
    -- x + y = 0 implies x = neg y
    have x_eq_neg_y : Path x (G.neg y) :=
      Path.trans
        (Path.symm (G.add_zero x))
        (Path.trans
          (Path.congrArg (G.add x) (Path.symm (G.add_neg y)))
          (Path.trans
            (Path.symm (G.add_assoc x y (G.neg y)))
            (Path.trans
              (Path.congrArg (G.add · (G.neg y)) sum_zero)
              (G.zero_add (G.neg y)))))
    -- neg y = neg(delta w) via congrArg neg on h.rel
    have neg_y_eq : Path (G.neg y) (G.neg (C.delta n h.witness)) :=
      Path.congrArg G.neg h.rel
    -- delta(neg w) = neg(delta w)
    have delta_neg_w : Path (C.delta n (Gn.neg h.witness)) (G.neg (C.delta n h.witness)) :=
      delta_neg C n h.witness
    exact Path.trans x_eq_neg_y (Path.trans neg_y_eq (Path.symm delta_neg_w))

/-- A cohomology class (representative). -/
structure CohomologyClass (C : CochainComplex) (n : Nat) where
  rep : Cocycle C n

/-- 24. Zero cohomology class. -/
noncomputable def zeroCohomologyClass (C : CochainComplex) (n : Nat) : CohomologyClass C n where
  rep := zeroCocycle C n

/-- 25. Addition of cohomology classes. -/
noncomputable def cohomologyClassAdd (C : CochainComplex) (n : Nat)
    (a b : CohomologyClass C n) : CohomologyClass C n where
  rep := cocycle_add C n a.rep b.rep

/-- 26. Negation of cohomology classes. -/
noncomputable def cohomologyClassNeg (C : CochainComplex) (n : Nat)
    (a : CohomologyClass C n) : CohomologyClass C n where
  rep := cocycle_neg C n a.rep

/-- 27. Addition is commutative at value level. -/
noncomputable def cohomologyClassAdd_comm_val (C : CochainComplex) (n : Nat) (a b : CohomologyClass C n) :
    Path (cohomologyClassAdd C n a b).rep.val (cohomologyClassAdd C n b a).rep.val :=
  (C.group n).add_comm a.rep.val b.rep.val

/-- 28. Right identity at value level. -/
noncomputable def cohomologyClassAdd_zero_right (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    Path (cohomologyClassAdd C n a (zeroCohomologyClass C n)).rep.val a.rep.val :=
  (C.group n).add_zero a.rep.val

/-- 29. Left identity at value level. -/
noncomputable def cohomologyClassAdd_zero_left (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    Path (cohomologyClassAdd C n (zeroCohomologyClass C n) a).rep.val a.rep.val :=
  (C.group n).zero_add a.rep.val

/-- 30. Inverse property at value level. -/
noncomputable def cohomologyClassNeg_add (C : CochainComplex) (n : Nat) (a : CohomologyClass C n) :
    Path (cohomologyClassAdd C n (cohomologyClassNeg C n a) a).rep.val
         (zeroCohomologyClass C n).rep.val :=
  (C.group n).neg_add a.rep.val

/-! ## Short Exact Sequences -/

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

/-- 31. Exactness restated. -/
noncomputable def ses_exact {ses : ShortExactSeq} (n : Nat) (x : (ses.A.group n).carrier) :
    Path (ses.project n (ses.inject n x)) (ses.C'.group n).zero :=
  ses.exact_at_B n x

/-- 32. Composing inject then project on zero yields zero via two routes. -/
noncomputable def ses_compose_zero (ses : ShortExactSeq) (n : Nat) :
    Path (ses.project n (ses.inject n (ses.A.group n).zero)) (ses.C'.group n).zero :=
  Path.trans
    (Path.congrArg (ses.project n) (ses.inject_zero n))
    (ses.project_zero n)

/-- 33. Two routes to zero agree. -/
theorem ses_zero_coherence (ses : ShortExactSeq) (n : Nat) :
    (ses_compose_zero ses n).proof = (ses.exact_at_B n (ses.A.group n).zero).proof :=
  Subsingleton.elim _ _

/-! ## Cup Product -/

/-- A cup product on a cochain complex. -/
structure CupProduct (C : CochainComplex) where
  cup : (p q : Nat) → (C.group p).carrier → (C.group q).carrier → (C.group (p + q)).carrier
  cup_zero_left : ∀ p q y, Path (cup p q (C.group p).zero y) (C.group (p + q)).zero
  cup_zero_right : ∀ p q x, Path (cup p q x (C.group q).zero) (C.group (p + q)).zero

/-- 34. Cup with zero left. -/
noncomputable def cup_zero_left_val {C : CochainComplex} (cp : CupProduct C) (p q : Nat)
    (y : (C.group q).carrier) :
    Path (cp.cup p q (C.group p).zero y) (C.group (p + q)).zero :=
  cp.cup_zero_left p q y

/-- 35. Cup with zero right. -/
noncomputable def cup_zero_right_val {C : CochainComplex} (cp : CupProduct C) (p q : Nat)
    (x : (C.group p).carrier) :
    Path (cp.cup p q x (C.group q).zero) (C.group (p + q)).zero :=
  cp.cup_zero_right p q x

/-- 36. Cup of zero with zero. -/
noncomputable def cup_zero_cocycles {C : CochainComplex} (cp : CupProduct C) (p q : Nat) :
    Path (cp.cup p q (C.group p).zero (C.group q).zero) (C.group (p + q)).zero :=
  cp.cup_zero_left p q (C.group q).zero

/-- 37. Zero-zero coherence. -/
theorem cup_zero_zero_coherence {C : CochainComplex} (cp : CupProduct C) (p q : Nat) :
    (cp.cup_zero_left p q (C.group q).zero).proof =
    (cp.cup_zero_right p q (C.group p).zero).proof :=
  Subsingleton.elim _ _

/-! ## Connecting Homomorphism -/

/-- The connecting homomorphism in the long exact sequence. -/
structure ConnectingHom (ses : ShortExactSeq) where
  connecting : (n : Nat) → (ses.C'.group n).carrier → (ses.A.group (n + 1)).carrier
  connecting_zero : ∀ n, Path (connecting n (ses.C'.group n).zero) (ses.A.group (n + 1)).zero

/-- 38. Connecting hom preserves zero. -/
noncomputable def connecting_preserves_zero {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ch.connecting n (ses.C'.group n).zero) (ses.A.group (n + 1)).zero :=
  ch.connecting_zero n

/-- 39. Composing inject with connecting on zero. -/
noncomputable def connecting_inject_zero {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ses.inject (n + 1) (ch.connecting n (ses.C'.group n).zero)) (ses.B.group (n + 1)).zero :=
  Path.trans
    (Path.congrArg (ses.inject (n + 1)) (ch.connecting_zero n))
    (ses.inject_zero (n + 1))

/-- 40. Exactness at A: project ∘ connecting = 0 at zero. -/
noncomputable def connecting_exact_at_zero {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ses.project (n + 1) (ses.inject (n + 1) (ch.connecting n (ses.C'.group n).zero)))
         (ses.C'.group (n + 1)).zero :=
  ses.exact_at_B (n + 1) (ch.connecting n (ses.C'.group n).zero)

/-- 41. Two routes to zero at connecting: via inject-zero vs via exactness. -/
noncomputable def connecting_zero_two_routes {ses : ShortExactSeq} (ch : ConnectingHom ses) (n : Nat) :
    Path (ses.project (n + 1) (ses.inject (n + 1) (ch.connecting n (ses.C'.group n).zero)))
         (ses.C'.group (n + 1)).zero :=
  Path.trans
    (Path.congrArg (ses.project (n + 1)) (connecting_inject_zero ch n))
    (ses.project_zero (n + 1))

/-! ## Transport along degree paths -/

/-- 42. Transport along refl is identity. -/
theorem transport_degree_refl {C : CochainComplex} (n : Nat) (x : (C.group n).carrier) :
    Path.transport (D := fun m => (C.group m).carrier) (Path.refl n) x = x := rfl

end CohomologyPaths
end Topology
end Path
end ComputationalPaths
