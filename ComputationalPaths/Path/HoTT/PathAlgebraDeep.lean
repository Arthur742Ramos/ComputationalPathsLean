/-
# Deep Path Algebra — non-trivial identities for trans/symm/congrArg

Multi-step proofs of algebraic identities in the computational path groupoid.
Every theorem uses genuine Path operations (trans, symm, congrArg, transport)
and requires reasoning through the step-list structure.

## Main results

- Anti-homomorphism: `(p.trans q).symm = q.symm.trans p.symm`
- congrArg distributes over trans and symm
- Transport along composite paths decomposes
- Naturality of path operations under congrArg
- Cancellation identities (symm-trans, trans-symm)
- Whiskering and interchange at the path level
- Pentagon coherence for fourfold composition
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.HoTT.PathAlgebraDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## 1. Anti-homomorphism of symm over trans -/

/-- Symm is an anti-homomorphism: reversing a composite reverses the order. -/
theorem symm_trans_antihom {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- Triple anti-homomorphism: `(p · q · r)⁻¹ = r⁻¹ · q⁻¹ · p⁻¹`. -/
theorem symm_trans_triple {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (Path.trans (Path.trans p q) r) =
      Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) := Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-- Quadruple anti-homomorphism. -/
theorem symm_trans_quadruple {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.symm (Path.trans (Path.trans (Path.trans p q) r) s) =
      Path.trans (Path.symm s)
        (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (Path.symm s) (Path.symm (Path.trans (Path.trans p q) r)) :=
          Path.symm_trans _ s
    _ = Path.trans (Path.symm s)
          (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
        rw [symm_trans_triple p q r]

/-! ## 2. Double symm (involutivity) -/

/-- Double symmetry is identity. -/
theorem symm_symm_eq {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Applying symm to both sides of a trans then symming back. -/
theorem symm_symm_trans {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (Path.symm (Path.trans p q)) = Path.trans p q :=
  Path.symm_symm (Path.trans p q)

/-! ## 3. congrArg distributes over trans -/

/-- congrArg distributes over trans (functoriality). -/
theorem congrArg_trans_dist {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- congrArg distributes over triple trans. -/
theorem congrArg_triple_trans {a b c d : A} (f : A → B)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
      Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q)) (Path.congrArg f r) := by
  calc Path.congrArg f (Path.trans (Path.trans p q) r)
      = Path.trans (Path.congrArg f (Path.trans p q)) (Path.congrArg f r) :=
          Path.congrArg_trans f (Path.trans p q) r
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q)) (Path.congrArg f r) := by
          rw [Path.congrArg_trans f p q]

/-! ## 4. congrArg commutes with symm -/

/-- congrArg commutes with symm. -/
theorem congrArg_symm_comm {a b : A} (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- congrArg of symm of trans = symm reversal applied through f. -/
theorem congrArg_symm_trans {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.symm (Path.trans p q)) =
      Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)) := by
          rw [Path.symm_trans p q]
    _ = Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
          Path.congrArg_trans f (Path.symm q) (Path.symm p)
    _ = Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
          rw [Path.congrArg_symm f q, Path.congrArg_symm f p]

/-! ## 5. congrArg composition (functoriality of ap) -/

/-- congrArg of composite function equals composition of congrArgs. -/
theorem congrArg_comp_eq {a b : A} (f : B → C) (g : A → B) (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p =
      Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-- Triple composition of congrArg. -/
theorem congrArg_triple_comp {D : Type u} {a b : A}
    (f : C → D) (g : B → C) (h : A → B) (p : Path a b) :
    Path.congrArg (fun x => f (g (h x))) p =
      Path.congrArg f (Path.congrArg g (Path.congrArg h p)) := by
  calc Path.congrArg (fun x => f (g (h x))) p
      = Path.congrArg f (Path.congrArg (fun x => g (h x)) p) :=
          Path.congrArg_comp f (fun x => g (h x)) p
    _ = Path.congrArg f (Path.congrArg g (Path.congrArg h p)) := by
          rw [Path.congrArg_comp g h p]

/-! ## 6. congrArg of identity is identity -/

/-- congrArg id = id on paths. -/
theorem congrArg_id_eq {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  Path.congrArg_id p

/-! ## 7. Transport along composite paths -/

/-- Transport along p · q = transport q ∘ transport p. -/
theorem transport_trans_decompose {D : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
      Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-- Transport along triple composite. -/
theorem transport_triple_trans {D : A → Sort v} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (Path.trans (Path.trans p q) r) x =
      Path.transport r (Path.transport q (Path.transport p x)) := by
  calc Path.transport (Path.trans (Path.trans p q) r) x
      = Path.transport r (Path.transport (Path.trans p q) x) :=
          Path.transport_trans (Path.trans p q) r x
    _ = Path.transport r (Path.transport q (Path.transport p x)) := by
          rw [Path.transport_trans p q x]

/-! ## 8. Transport and symm cancel -/

/-- Transport along p then symm p is identity. -/
theorem transport_symm_cancel_right {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

/-- Transport along symm p then p is identity. -/
theorem transport_symm_cancel_left {D : A → Sort v} {a b : A}
    (p : Path a b) (y : D b) :
    Path.transport p (Path.transport (Path.symm p) y) = y :=
  Path.transport_symm_right p y

/-! ## 9. Transport naturality with congrArg -/

/-- Transport in composite family = transport in base family along congrArg. -/
theorem transport_congrArg_compose {P : B → Type v}
    (f : A → B) {a₁ a₂ : A} (p : Path a₁ a₂) (x : P (f a₁)) :
    Path.transport (D := P ∘ f) p x =
      Path.transport (D := P) (Path.congrArg f p) x := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## 10. Cancellation identities at step-list level -/

/-- trans p (symm p) has same proof as refl. -/
theorem trans_symm_toEq {a b : A} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq :=
  Path.toEq_trans_symm p

/-- trans (symm p) p has same proof as refl. -/
theorem symm_trans_toEq {a b : A} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq :=
  Path.toEq_symm_trans p

/-! ## 11. Associativity coherence -/

/-- Fourfold associativity: left-nested to right-nested. -/
theorem trans_assoc4 {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s)) :=
  Path.trans_assoc_fourfold p q r s

/-- Fivefold reassociation. -/
theorem trans_assoc5 {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
      Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
          Path.trans_assoc _ s t
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
          Path.trans_assoc_fourfold p q r (Path.trans s t)

/-! ## 12. congrArg preserves associativity -/

/-- congrArg respects associativity of trans. -/
theorem congrArg_assoc {a b c d : A} (f : A → B)
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
      Path.trans (Path.congrArg f p) (Path.trans (Path.congrArg f q) (Path.congrArg f r)) := by
  calc Path.congrArg f (Path.trans (Path.trans p q) r)
      = Path.trans (Path.congrArg f (Path.trans p q)) (Path.congrArg f r) :=
          Path.congrArg_trans f _ r
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q)) (Path.congrArg f r) := by
          rw [Path.congrArg_trans f p q]
    _ = Path.trans (Path.congrArg f p) (Path.trans (Path.congrArg f q) (Path.congrArg f r)) :=
          Path.trans_assoc _ _ _

/-! ## 13. congrArg preserves cancellation -/

/-- congrArg of (p · p⁻¹) = (fp) · (fp)⁻¹. -/
theorem congrArg_trans_symm_cancel {a b : A} (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.trans p (Path.symm p)) =
      Path.trans (Path.congrArg f p) (Path.symm (Path.congrArg f p)) := by
  calc Path.congrArg f (Path.trans p (Path.symm p))
      = Path.trans (Path.congrArg f p) (Path.congrArg f (Path.symm p)) :=
          Path.congrArg_trans f p (Path.symm p)
    _ = Path.trans (Path.congrArg f p) (Path.symm (Path.congrArg f p)) := by
          rw [Path.congrArg_symm f p]

/-! ## 14. Transport is natural w.r.t. dependent maps -/

/-- Naturality of transport: applying f commutes with transport. -/
theorem transport_naturality_dep {D E : A → Type v}
    (f : ∀ x, D x → E x) {a b : A} (p : Path a b) (d : D a) :
    Path.transport (D := E) p (f a d) = f b (Path.transport (D := D) p d) :=
  Path.transport_app f p d

/-! ## 15. Whiskering and 2-cell structure -/

/-- Left whiskering: pre-composing a 2-cell with a path. -/
theorem whiskerLeft_comp {a b c : A} {p p' : Path a b}
    (α : p = p') (q : Path b c) :
    Path.trans p q = Path.trans p' q :=
  Path.whiskerLeft α q

/-- Right whiskering: post-composing a 2-cell with a path. -/
theorem whiskerRight_comp {a b c : A} (p : Path a b)
    {q q' : Path b c} (β : q = q') :
    Path.trans p q = Path.trans p q' :=
  Path.whiskerRight p β

/-- Whiskering is natural: the two ways of whiskering commute. -/
theorem whisker_exchange {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (α : p = p') (β : q = q') :
    Eq.trans (Path.whiskerRight p β) (Path.whiskerLeft α q') =
      Eq.trans (Path.whiskerLeft α q) (Path.whiskerRight p' β) :=
  Path.whisker_naturality α β

/-! ## 16. congrArg preserves refl -/

/-- congrArg of refl is refl. -/
theorem congrArg_refl (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-! ## 17. Length invariants under path operations -/

/-- Length of trans is additive. -/
theorem length_trans_additive {a b c : A} (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps.length = p.steps.length + q.steps.length := by
  simp [Path.trans]

/-- Length of symm equals length of original. -/
theorem length_symm_eq {a b : A} (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp [Path.symm]

/-- Length of congrArg equals length of original. -/
theorem length_congrArg_eq {a b : A} (f : A → B) (p : Path a b) :
    (Path.congrArg f p).steps.length = p.steps.length := by
  simp [Path.congrArg]

/-! ## 18. Steps of symm∘symm = original steps -/

/-- The step list of double-symm equals the original step list. -/
theorem steps_symm_symm {a b : A} (p : Path a b) :
    (Path.symm (Path.symm p)).steps = p.steps := by
  have h := Path.symm_symm p
  exact _root_.congrArg Path.steps h

/-! ## 19. congrArg respects step structure -/

/-- Steps of congrArg f (trans p q) = steps of (congrArg f p) ++ (congrArg f q). -/
theorem steps_congrArg_trans {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    (Path.congrArg f (Path.trans p q)).steps =
      (Path.congrArg f p).steps ++ (Path.congrArg f q).steps := by
  have h := Path.congrArg_trans f p q
  exact _root_.congrArg Path.steps h

/-! ## 20. Pentagon identity -/

/-- The pentagon identity for reassociation holds by proof irrelevance. -/
theorem pentagon_coherence {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Eq.trans
      (Path.trans_assoc (Path.trans p q) r s)
      (Path.trans_assoc p q (Path.trans r s)) =
    Eq.trans
      (_root_.congrArg (fun t => Path.trans t s) (Path.trans_assoc p q r))
      (Eq.trans
        (Path.trans_assoc p (Path.trans q r) s)
        (_root_.congrArg (fun t => Path.trans p t) (Path.trans_assoc q r s))) :=
  rfl

/-! ## 21. Transport along congrArg path -/

/-- Transport in a type family via congrArg decomposes. -/
theorem transport_via_congrArg {D : A → Type w} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) p x =
      Path.transport (D := fun X => X)
        (Path.congrArg (fun t => D t) p) x :=
  Path.transport_congrArg p x

/-! ## 22. congrArg distributes over quadruple trans -/

/-- congrArg distributes over fourfold composition. -/
theorem congrArg_quadruple_trans {a b c d e : A} (f : A → B)
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.congrArg f (Path.trans (Path.trans (Path.trans p q) r) s) =
      Path.trans (Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
        (Path.congrArg f r)) (Path.congrArg f s) := by
  calc Path.congrArg f (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (Path.congrArg f (Path.trans (Path.trans p q) r)) (Path.congrArg f s) :=
          Path.congrArg_trans f _ s
    _ = Path.trans (Path.trans (Path.congrArg f (Path.trans p q)) (Path.congrArg f r))
          (Path.congrArg f s) := by
          rw [Path.congrArg_trans f (Path.trans p q) r]
    _ = Path.trans (Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
          (Path.congrArg f r)) (Path.congrArg f s) := by
          rw [Path.congrArg_trans f p q]

/-! ## 23. Symm of congrArg of symm roundtrip -/

/-- symm (congrArg f (symm p)) = congrArg f p. -/
theorem symm_congrArg_symm {a b : A} (f : A → B) (p : Path a b) :
    Path.symm (Path.congrArg f (Path.symm p)) = Path.congrArg f p := by
  calc Path.symm (Path.congrArg f (Path.symm p))
      = Path.symm (Path.symm (Path.congrArg f p)) := by
          rw [Path.congrArg_symm f p]
    _ = Path.congrArg f p := Path.symm_symm _

/-! ## 24. Transport constant family -/

/-- Transport in a constant family is the identity. -/
theorem transport_const_family {D : Type v} {a b : A}
    (p : Path a b) (x : D) :
    Path.transport (D := fun _ => D) p x = x :=
  Path.transport_const p x

/-! ## 25. congrArg respects step reversal -/

/-- Steps of congrArg f (symm p) = reversed mapped steps. -/
theorem steps_congrArg_symm {a b : A} (f : A → B) (p : Path a b) :
    (Path.congrArg f (Path.symm p)).steps =
      (Path.symm (Path.congrArg f p)).steps := by
  have h := Path.congrArg_symm f p
  exact _root_.congrArg Path.steps h

end ComputationalPaths.Path.HoTT.PathAlgebraDeep
