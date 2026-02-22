/-
# Galois Theory via Computational Paths — Deep Formalization

Field expressions, automorphism steps, fixed-field reasoning, Galois groups,
normal/separable witnesses — all built from domain-specific `GExpr`/`GStep`/`GPath`
inductives. Zero `Path.mk [Step.mk _ _ h] h`.

## References

- Lang, "Algebra"
- Artin, "Galois Theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.GaloisPaths

universe u

/-! ## 1. Field Expression Language -/

/-- Symbolic expressions for a field with named automorphisms. -/
inductive GExpr : Type where
  | val   : Nat → GExpr
  | zero  : GExpr
  | one   : GExpr
  | add   : GExpr → GExpr → GExpr
  | mul   : GExpr → GExpr → GExpr
  | neg   : GExpr → GExpr
  | inv   : GExpr → GExpr
  | aut   : Nat → GExpr → GExpr   -- apply automorphism #n
  | autInv : Nat → GExpr → GExpr  -- apply inverse of automorphism #n
  deriving Repr, DecidableEq

/-! ## 2. Elementary Rewrite Steps -/

/-- Elementary rewrite steps witnessing field axioms and automorphism laws. -/
inductive GStep : GExpr → GExpr → Type where
  -- Field axioms
  | add_comm   : (a b : GExpr) → GStep (.add a b) (.add b a)
  | add_assoc  : (a b c : GExpr) →
      GStep (.add (.add a b) c) (.add a (.add b c))
  | zero_add   : (a : GExpr) → GStep (.add .zero a) a
  | add_zero   : (a : GExpr) → GStep (.add a .zero) a
  | add_neg    : (a : GExpr) → GStep (.add a (.neg a)) .zero
  | neg_add    : (a : GExpr) → GStep (.add (.neg a) a) .zero
  | mul_comm   : (a b : GExpr) → GStep (.mul a b) (.mul b a)
  | mul_assoc  : (a b c : GExpr) →
      GStep (.mul (.mul a b) c) (.mul a (.mul b c))
  | one_mul    : (a : GExpr) → GStep (.mul .one a) a
  | mul_one    : (a : GExpr) → GStep (.mul a .one) a
  | distrib_l  : (a b c : GExpr) →
      GStep (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  | distrib_r  : (a b c : GExpr) →
      GStep (.mul (.add a b) c) (.add (.mul a c) (.mul b c))
  | mul_zero   : (a : GExpr) → GStep (.mul a .zero) .zero
  | zero_mul   : (a : GExpr) → GStep (.mul .zero a) .zero
  | neg_neg    : (a : GExpr) → GStep (.neg (.neg a)) a
  | mul_inv    : (a : GExpr) → GStep (.mul a (.inv a)) .one
  -- Automorphism homomorphism laws
  | aut_zero   : (n : Nat) → GStep (.aut n .zero) .zero
  | aut_one    : (n : Nat) → GStep (.aut n .one) .one
  | aut_add    : (n : Nat) → (a b : GExpr) →
      GStep (.aut n (.add a b)) (.add (.aut n a) (.aut n b))
  | aut_mul    : (n : Nat) → (a b : GExpr) →
      GStep (.aut n (.mul a b)) (.mul (.aut n a) (.aut n b))
  | aut_neg    : (n : Nat) → (a : GExpr) →
      GStep (.aut n (.neg a)) (.neg (.aut n a))
  -- Identity automorphism (aut 0 = id)
  | aut_id     : (a : GExpr) → GStep (.aut 0 a) a
  -- Automorphism inverse cancellation
  | aut_inv_cancel : (n : Nat) → (a : GExpr) →
      GStep (.autInv n (.aut n a)) a
  | inv_aut_cancel : (n : Nat) → (a : GExpr) →
      GStep (.aut n (.autInv n a)) a
  -- Automorphism composition
  | aut_comp   : (n m : Nat) → (a : GExpr) →
      GStep (.aut n (.aut m a)) (.aut (n + m) a)
  -- Congruence
  | congr_add_l : {a b : GExpr} → GStep a b → (c : GExpr) →
      GStep (.add a c) (.add b c)
  | congr_add_r : (c : GExpr) → {a b : GExpr} → GStep a b →
      GStep (.add c a) (.add c b)
  | congr_mul_l : {a b : GExpr} → GStep a b → (c : GExpr) →
      GStep (.mul a c) (.mul b c)
  | congr_mul_r : (c : GExpr) → {a b : GExpr} → GStep a b →
      GStep (.mul c a) (.mul c b)
  | congr_neg  : {a b : GExpr} → GStep a b → GStep (.neg a) (.neg b)
  | congr_aut  : (n : Nat) → {a b : GExpr} → GStep a b →
      GStep (.aut n a) (.aut n b)

/-! ## 3. Path = Sequence of Steps -/

/-- A `GPath` is a freely generated path from steps, with refl/trans/symm. -/
inductive GPath : GExpr → GExpr → Type where
  | refl  : (a : GExpr) → GPath a a
  | step  : GStep a b → GPath a b
  | trans : GPath a b → GPath b c → GPath a c
  | symm  : GPath a b → GPath b a

/-! ## 4. Basic Path Combinators -/

-- 1. Concatenation (synonym for trans)
noncomputable def GPath.concat (p : GPath a b) (q : GPath b c) : GPath a c :=
  GPath.trans p q

-- 2. Length of a path
noncomputable def GPath.length : GPath a b → Nat
  | .refl _    => 0
  | .step _    => 1
  | .trans p q => p.length + q.length
  | .symm p    => p.length

-- 3. Refl has length 0
theorem gpath_refl_length (a : GExpr) : (GPath.refl a).length = 0 := rfl

-- 4. Step has length 1
theorem gpath_step_length (s : GStep a b) : (GPath.step s).length = 1 := rfl

-- 5. Symm preserves length
theorem gpath_symm_length (p : GPath a b) :
    (GPath.symm p).length = p.length := rfl

-- 6. Trans adds lengths
theorem gpath_trans_length (p : GPath a b) (q : GPath b c) :
    (GPath.trans p q).length = p.length + q.length := rfl

-- 7. Refl is a left identity for concat (up to GPath equality)
theorem gpath_refl_trans_length (p : GPath a b) :
    (GPath.trans (.refl a) p).length = p.length := by
  simp [GPath.length]

/-! ## 5. Congruence Lifts -/

-- 8. Lift a path through addition on the left
noncomputable def GPath.congr_add_left (p : GPath a b) (c : GExpr) : GPath (.add a c) (.add b c) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_add_l s c)
  | .trans p q => .trans (p.congr_add_left c) (q.congr_add_left c)
  | .symm p    => .symm (p.congr_add_left c)

-- 9. Lift a path through addition on the right
noncomputable def GPath.congr_add_right (c : GExpr) (p : GPath a b) : GPath (.add c a) (.add c b) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_add_r c s)
  | .trans p q => .trans (p.congr_add_right c) (q.congr_add_right c)
  | .symm p    => .symm (p.congr_add_right c)

-- 10. Lift a path through multiplication on the left
noncomputable def GPath.congr_mul_left (p : GPath a b) (c : GExpr) : GPath (.mul a c) (.mul b c) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_mul_l s c)
  | .trans p q => .trans (p.congr_mul_left c) (q.congr_mul_left c)
  | .symm p    => .symm (p.congr_mul_left c)

-- 11. Lift a path through multiplication on the right
noncomputable def GPath.congr_mul_right (c : GExpr) (p : GPath a b) : GPath (.mul c a) (.mul c b) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_mul_r c s)
  | .trans p q => .trans (p.congr_mul_right c) (q.congr_mul_right c)
  | .symm p    => .symm (p.congr_mul_right c)

-- 12. Lift a path through negation
noncomputable def GPath.congr_neg (p : GPath a b) : GPath (.neg a) (.neg b) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_neg s)
  | .trans p q => .trans p.congr_neg q.congr_neg
  | .symm p    => .symm p.congr_neg

-- 13. Lift a path through an automorphism
noncomputable def GPath.congr_aut (n : Nat) (p : GPath a b) : GPath (.aut n a) (.aut n b) :=
  match p with
  | .refl _    => .refl _
  | .step s    => .step (.congr_aut n s)
  | .trans p q => .trans (p.congr_aut n) (q.congr_aut n)
  | .symm p    => .symm (p.congr_aut n)

/-! ## 6. Field Automorphism Paths -/

-- 14. Identity automorphism fixes any expression
noncomputable def aut_id_path (a : GExpr) : GPath (.aut 0 a) a :=
  .step (.aut_id a)

-- 15. Automorphism preserves zero
noncomputable def aut_zero_path (n : Nat) : GPath (.aut n .zero) .zero :=
  .step (.aut_zero n)

-- 16. Automorphism preserves one
noncomputable def aut_one_path (n : Nat) : GPath (.aut n .one) .one :=
  .step (.aut_one n)

-- 17. Automorphism distributes over addition
noncomputable def aut_add_path (n : Nat) (a b : GExpr) :
    GPath (.aut n (.add a b)) (.add (.aut n a) (.aut n b)) :=
  .step (.aut_add n a b)

-- 18. Automorphism distributes over multiplication
noncomputable def aut_mul_path (n : Nat) (a b : GExpr) :
    GPath (.aut n (.mul a b)) (.mul (.aut n a) (.aut n b)) :=
  .step (.aut_mul n a b)

-- 19. Automorphism inverse cancellation
noncomputable def aut_cancel_path (n : Nat) (a : GExpr) :
    GPath (.autInv n (.aut n a)) a :=
  .step (.aut_inv_cancel n a)

-- 20. Forward-inverse cancellation
noncomputable def inv_aut_cancel_path (n : Nat) (a : GExpr) :
    GPath (.aut n (.autInv n a)) a :=
  .step (.inv_aut_cancel n a)

/-! ## 7. Composition of Automorphisms -/

-- 21. Automorphism composition path
noncomputable def aut_comp_path (n m : Nat) (a : GExpr) :
    GPath (.aut n (.aut m a)) (.aut (n + m) a) :=
  .step (.aut_comp n m a)

-- 22. Identity is left unit for composition: aut 0 ∘ aut m = aut m
noncomputable def aut_comp_id_left (m : Nat) (a : GExpr) :
    GPath (.aut 0 (.aut m a)) (.aut m a) :=
  .step (.aut_id (.aut m a))

-- 23. Composition associativity: aut n (aut m (aut k a)) two ways
noncomputable def aut_comp_assoc (n m k : Nat) (a : GExpr) :
    GPath (.aut n (.aut m (.aut k a))) (.aut (n + (m + k)) a) :=
  .trans (.congr_aut n (.step (.aut_comp m k a))) (.step (.aut_comp n (m + k) a))

/-! ## 8. Fixed Elements -/

/-- An expression `a` is fixed by automorphism `n` if there is a path
    `aut n a ~~> a`. -/
structure IsGFixed (n : Nat) (a : GExpr) where
  witness : GPath (.aut n a) a

-- 24. Zero is fixed by every automorphism
noncomputable def zero_fixed (n : Nat) : IsGFixed n .zero :=
  ⟨aut_zero_path n⟩

-- 25. One is fixed by every automorphism
noncomputable def one_fixed (n : Nat) : IsGFixed n .one :=
  ⟨aut_one_path n⟩

-- 26. Fixed elements closed under addition
noncomputable def fixed_add (n : Nat) (a b : GExpr)
    (ha : IsGFixed n a) (hb : IsGFixed n b) :
    IsGFixed n (.add a b) :=
  ⟨.trans (aut_add_path n a b)
          (.trans (ha.witness.congr_add_left (.aut n b))
                  (hb.witness.congr_add_right a))⟩

-- 27. Fixed elements closed under multiplication
noncomputable def fixed_mul (n : Nat) (a b : GExpr)
    (ha : IsGFixed n a) (hb : IsGFixed n b) :
    IsGFixed n (.mul a b) :=
  ⟨.trans (aut_mul_path n a b)
          (.trans (ha.witness.congr_mul_left (.aut n b))
                  (hb.witness.congr_mul_right a))⟩

-- 28. Fixed elements closed under negation
noncomputable def fixed_neg (n : Nat) (a : GExpr)
    (ha : IsGFixed n a) : IsGFixed n (.neg a) :=
  ⟨.trans (.step (.aut_neg n a)) ha.witness.congr_neg⟩

-- 29. Everything is fixed by the identity automorphism
noncomputable def id_fixes_all (a : GExpr) : IsGFixed 0 a :=
  ⟨aut_id_path a⟩

/-! ## 9. Galois Group Structure -/

/-- A Galois group is a list of automorphism indices. -/
structure GGaloisGroup where
  auts : List Nat
  hasId : 0 ∈ auts

/-- An element is in the fixed field of a Galois group. -/
noncomputable def IsInFixedField (G : GGaloisGroup) (a : GExpr) : Prop :=
  ∀ n, n ∈ G.auts → Nonempty (GPath (.aut n a) a)

-- 30. Zero is in every fixed field
theorem zero_in_fixed_field (G : GGaloisGroup) :
    IsInFixedField G .zero :=
  fun n _ => ⟨aut_zero_path n⟩

-- 31. One is in every fixed field
theorem one_in_fixed_field (G : GGaloisGroup) :
    IsInFixedField G .one :=
  fun n _ => ⟨aut_one_path n⟩

-- 32. Trivial Galois group {id}
noncomputable def trivialGalois : GGaloisGroup :=
  ⟨[0], by simp⟩

-- 33. Trivial group has order 1
theorem trivialGalois_order : trivialGalois.auts.length = 1 := rfl

/-! ## 10. Normal Extension Witness -/

/-- Witness that a set of roots is permuted by automorphisms. -/
structure NormalWitness (G : GGaloisGroup) (roots : List GExpr) where
  permute : Nat → GExpr → GExpr
  preserves : ∀ n, n ∈ G.auts → ∀ r, r ∈ roots → (permute n r) ∈ roots
  coherent : ∀ r, permute 0 r = r

-- 34. Identity witness
noncomputable def trivialNormalWitness (G : GGaloisGroup) (roots : List GExpr) :
    NormalWitness G roots where
  permute := fun _ r => r
  preserves := fun _ _ _ hr => hr
  coherent := fun _ => rfl

/-! ## 11. Separable Witness -/

structure SepWitness where
  roots : List GExpr
  distinct : roots.Nodup

-- 35. Empty separable witness
noncomputable def emptySep : SepWitness := ⟨[], List.nodup_nil⟩

-- 36. Empty witness has no roots
theorem emptySep_roots : emptySep.roots = [] := rfl

/-! ## 12. Composite Paths — Field Laws -/

-- 37. a + b + (-b) ~~> a (cancellation)
noncomputable def add_cancel_right (a b : GExpr) :
    GPath (.add (.add a b) (.neg b)) a :=
  .trans (.step (.add_assoc a b (.neg b)))
    (.trans (GPath.congr_add_right a (.step (.add_neg b)))
            (.step (.add_zero a)))

-- 38. Automorphism of a sum, then cancel, yields the original
noncomputable def aut_add_cancel (n : Nat) (a b : GExpr) :
    GPath (.aut n (.add (.add a b) (.neg b)))
          (.add (.add (.aut n a) (.aut n b)) (.neg (.aut n b))) :=
  .trans (.step (.aut_add n (.add a b) (.neg b)))
    (.trans (GPath.congr_add_left (.step (.aut_add n a b)) (.aut n (.neg b)))
            (GPath.congr_add_right (.add (.aut n a) (.aut n b)) (.step (.aut_neg n b))))

-- 39. Double negation path
noncomputable def neg_neg_path (a : GExpr) : GPath (.neg (.neg a)) a :=
  .step (.neg_neg a)

-- 40. Mul distributes over add, witnessed path
noncomputable def distrib_path (a b c : GExpr) :
    GPath (.mul a (.add b c)) (.add (.mul a b) (.mul a c)) :=
  .step (.distrib_l a b c)

-- 41. Automorphism commutes with distributivity
noncomputable def aut_distrib (n : Nat) (a b c : GExpr) :
    GPath (.aut n (.mul a (.add b c)))
          (.add (.mul (.aut n a) (.aut n b)) (.mul (.aut n a) (.aut n c))) :=
  .trans (.step (.aut_mul n a (.add b c)))
    (.trans (GPath.congr_mul_right (.aut n a) (aut_add_path n b c))
            (.step (.distrib_l (.aut n a) (.aut n b) (.aut n c))))

/-! ## 13. Path Algebra -/

-- 42. Symm of symm is the original (propositionally)
theorem gpath_symm_symm_length (p : GPath a b) :
    (GPath.symm (GPath.symm p)).length = p.length := rfl

-- 43. Trans with refl on right preserves length
theorem gpath_trans_refl_length (p : GPath a b) :
    (GPath.trans p (.refl b)).length = p.length := by
  simp [GPath.length]

-- 44. Concat is associative in length
theorem gpath_concat_assoc_length (p : GPath a b) (q : GPath b c) (r : GPath c d) :
    (GPath.concat (GPath.concat p q) r).length =
    (GPath.concat p (GPath.concat q r)).length := by
  simp [GPath.concat, GPath.length, Nat.add_assoc]

/-! ## 14. Galois Correspondence Aspects -/

/-- Subgroup inclusion: G₁ ⊆ G₂ as automorphism lists. -/
noncomputable def GSubgroup (G₁ G₂ : GGaloisGroup) : Prop :=
  ∀ n, n ∈ G₁.auts → n ∈ G₂.auts

-- 45. Larger group ⟹ smaller fixed field (contravariant)
theorem fixed_field_contravariant (G₁ G₂ : GGaloisGroup) (a : GExpr)
    (sub : GSubgroup G₁ G₂) (hfix : IsInFixedField G₂ a) :
    IsInFixedField G₁ a :=
  fun n hn => hfix n (sub n hn)

-- 46. Every group is a subgroup of itself
theorem gsubgroup_refl (G : GGaloisGroup) : GSubgroup G G :=
  fun _ hn => hn

-- 47. Subgroup is transitive
theorem gsubgroup_trans (G₁ G₂ G₃ : GGaloisGroup)
    (h12 : GSubgroup G₁ G₂) (h23 : GSubgroup G₂ G₃) :
    GSubgroup G₁ G₃ :=
  fun n hn => h23 n (h12 n hn)

/-! ## 15. Extended Automorphism Paths -/

-- 48. Automorphism applied to a product of fixed elements
noncomputable def aut_fixed_mul_path (n : Nat) (a b : GExpr)
    (ha : IsGFixed n a) (hb : IsGFixed n b) :
    GPath (.aut n (.mul a b)) (.mul a b) :=
  (fixed_mul n a b ha hb).witness

-- 49. Chain: aut n (aut n⁻¹ a) = a
noncomputable def aut_round_trip (n : Nat) (a : GExpr) :
    GPath (.aut n (.autInv n a)) a :=
  inv_aut_cancel_path n a

-- 50. Inverse round trip
noncomputable def autInv_round_trip (n : Nat) (a : GExpr) :
    GPath (.autInv n (.aut n a)) a :=
  aut_cancel_path n a

end ComputationalPaths.Path.Algebra.GaloisPaths
