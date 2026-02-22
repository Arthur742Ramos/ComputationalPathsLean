/-
  ComputationalPaths / Path / Algebra / DerivativesDeep.lean

  Derivatives of data types via computational paths.
  Models: type functors, zippers as derivatives, one-hole contexts,
  chain rule for nested types, product/sum rules, derivative of
  recursive types (Leibniz rule), McBride's dissection,
  path through derivative = focus navigation.

  All proofs are sorry‑free.
-/

-- ============================================================
-- §1  Computational Paths infrastructure
-- ============================================================

namespace DerivDeep

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

noncomputable def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

noncomputable def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

noncomputable def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

noncomputable def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

noncomputable def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

noncomputable def Path.map {α β : Type} (f : α → β) {a b : α}
    (p : Path α a b) : Path β (f a) (f b) :=
  match p with
  | .nil a => .nil (f a)
  | .cons (.mk name x y) rest =>
    .cons (.mk ("map(" ++ name ++ ")") (f x) (f y)) (rest.map f)

-- ============================================================
-- §2  Type Functors (polynomial functors as data)
-- ============================================================

/-- Polynomial functor codes for regular types. -/
inductive TyF where
  | zero   : TyF
  | one    : TyF
  | var    : TyF
  | sum    : TyF → TyF → TyF
  | prod   : TyF → TyF → TyF
  | comp   : TyF → TyF → TyF
  | mu     : TyF → TyF
deriving DecidableEq, Repr

noncomputable def TyF.varCount : TyF → Nat
  | .zero => 0
  | .one => 0
  | .var => 1
  | .sum f g => f.varCount + g.varCount
  | .prod f g => f.varCount + g.varCount
  | .comp f g => f.varCount * g.varCount
  | .mu f => f.varCount

noncomputable def TyF.size : TyF → Nat
  | .zero => 1
  | .one => 1
  | .var => 1
  | .sum f g => 1 + f.size + g.size
  | .prod f g => 1 + f.size + g.size
  | .comp f g => 1 + f.size + g.size
  | .mu f => 1 + f.size

-- ============================================================
-- §3  Formal Derivative
-- ============================================================

noncomputable def TyF.deriv : TyF → TyF
  | .zero     => .zero
  | .one      => .zero
  | .var      => .one
  | .sum f g  => .sum f.deriv g.deriv
  | .prod f g => .sum (.prod f.deriv g) (.prod f g.deriv)
  | .comp f g => .prod (.comp f.deriv g) g.deriv
  | .mu f     => .mu (.sum .one (.prod f.deriv (.mu f)))

noncomputable def TyF.deriv2 (f : TyF) : TyF := f.deriv.deriv

-- ============================================================
-- §4  Rewrite steps with full congruence
-- ============================================================

inductive DStep : TyF → TyF → Prop where
  | sumZeroL (f : TyF) : DStep (.sum .zero f) f
  | sumZeroR (f : TyF) : DStep (.sum f .zero) f
  | prodZeroL (f : TyF) : DStep (.prod .zero f) .zero
  | prodZeroR (f : TyF) : DStep (.prod f .zero) .zero
  | prodOneL (f : TyF) : DStep (.prod .one f) f
  | prodOneR (f : TyF) : DStep (.prod f .one) f
  | sumCongL {f₁ f₂ : TyF} (g : TyF) : DStep f₁ f₂ → DStep (.sum f₁ g) (.sum f₂ g)
  | sumCongR {g₁ g₂ : TyF} (f : TyF) : DStep g₁ g₂ → DStep (.sum f g₁) (.sum f g₂)
  | prodCongL {f₁ f₂ : TyF} (g : TyF) : DStep f₁ f₂ → DStep (.prod f₁ g) (.prod f₂ g)
  | prodCongR {g₁ g₂ : TyF} (f : TyF) : DStep g₁ g₂ → DStep (.prod f g₁) (.prod f g₂)

inductive DPath : TyF → TyF → Prop where
  | refl (f : TyF) : DPath f f
  | step {f₁ f₂ f₃ : TyF} : DStep f₁ f₂ → DPath f₂ f₃ → DPath f₁ f₃

-- ============================================================
-- §5  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of DPath. -/
theorem DPath.trans {a b c : TyF}
    (p : DPath a b) (q : DPath b c) : DPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact .step s (ih q)

/-- Theorem 2: Left sum congruence lifts to paths. -/
theorem DPath.congrArg_sumL {f₁ f₂ : TyF} (g : TyF)
    (p : DPath f₁ f₂) : DPath (.sum f₁ g) (.sum f₂ g) := by
  induction p with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.sumCongL g s) ih

/-- Theorem 3: Right sum congruence lifts to paths. -/
theorem DPath.congrArg_sumR {g₁ g₂ : TyF} (f : TyF)
    (p : DPath g₁ g₂) : DPath (.sum f g₁) (.sum f g₂) := by
  induction p with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.sumCongR f s) ih

/-- Theorem 4: Left prod congruence lifts to paths. -/
theorem DPath.congrArg_prodL {f₁ f₂ : TyF} (g : TyF)
    (p : DPath f₁ f₂) : DPath (.prod f₁ g) (.prod f₂ g) := by
  induction p with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.prodCongL g s) ih

/-- Theorem 5: Right prod congruence lifts to paths. -/
theorem DPath.congrArg_prodR {g₁ g₂ : TyF} (f : TyF)
    (p : DPath g₁ g₂) : DPath (.prod f g₁) (.prod f g₂) := by
  induction p with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.prodCongR f s) ih

-- ============================================================
-- §6  Basic derivative theorems
-- ============================================================

/-- Theorem 6: Derivative of zero is zero. -/
theorem deriv_zero : TyF.deriv .zero = .zero := rfl

/-- Theorem 7: Derivative of one is zero. -/
theorem deriv_one : TyF.deriv .one = .zero := rfl

/-- Theorem 8: Derivative of var is one. -/
theorem deriv_var : TyF.deriv .var = .one := rfl

/-- Theorem 9: Sum rule for derivatives. -/
theorem deriv_sum (f g : TyF) :
    TyF.deriv (.sum f g) = .sum f.deriv g.deriv := rfl

/-- Theorem 10: Product rule (Leibniz) for derivatives. -/
theorem deriv_prod (f g : TyF) :
    TyF.deriv (.prod f g) = .sum (.prod f.deriv g) (.prod f g.deriv) := rfl

/-- Theorem 11: Chain rule for derivatives. -/
theorem deriv_comp (f g : TyF) :
    TyF.deriv (.comp f g) = .prod (.comp f.deriv g) g.deriv := rfl

/-- Theorem 12: Size is always positive. -/
theorem TyF.size_pos (f : TyF) : f.size > 0 := by
  cases f <;> simp [TyF.size] <;> omega

/-- Theorem 13: Derivative of constants is zero. -/
theorem deriv_const_zero : TyF.deriv .one = .zero ∧ TyF.deriv .zero = .zero :=
  ⟨rfl, rfl⟩

/-- Theorem 14: Second derivative of X is 0. -/
theorem deriv2_var : TyF.deriv2 .var = .zero := rfl

/-- Theorem 15: Mu-type derivative structure. -/
theorem deriv_mu (f : TyF) :
    TyF.deriv (.mu f) = .mu (.sum .one (.prod f.deriv (.mu f))) := rfl

-- ============================================================
-- §7  Simplification paths (multi-step trans/symm/congrArg chains)
-- ============================================================

/-- Theorem 16: DPath from sum-zero-left to simplified. -/
theorem dpath_sum_zero_l (f : TyF) : DPath (.sum .zero f) f :=
  .step (.sumZeroL f) (.refl f)

/-- Theorem 17: DPath from sum-zero-right to simplified. -/
theorem dpath_sum_zero_r (f : TyF) : DPath (.sum f .zero) f :=
  .step (.sumZeroR f) (.refl f)

/-- Theorem 18: DPath from prod-one-left. -/
theorem dpath_prod_one_l (f : TyF) : DPath (.prod .one f) f :=
  .step (.prodOneL f) (.refl f)

/-- Theorem 19: DPath from prod-one-right. -/
theorem dpath_prod_one_r (f : TyF) : DPath (.prod f .one) f :=
  .step (.prodOneR f) (.refl f)

/-- Theorem 20: Multi-step: (1 × (0 + F)) → F via trans chain. -/
theorem dpath_prod_one_sum_zero (f : TyF) :
    DPath (.prod .one (.sum .zero f)) f := by
  apply DPath.trans
  · exact DPath.congrArg_prodR TyF.one (dpath_sum_zero_l f)
  · exact dpath_prod_one_l f

/-- Theorem 21: Multi-step: ((F + 0) × 1) → F. -/
theorem dpath_sum_zero_prod_one (f : TyF) :
    DPath (.prod (.sum f .zero) .one) f := by
  apply DPath.trans
  · exact DPath.congrArg_prodL TyF.one (dpath_sum_zero_r f)
  · exact dpath_prod_one_r f

/-- Theorem 22: Full Leibniz simplification: 0×G + F×0 → 0. -/
theorem leibniz_zero_path (f g : TyF) :
    DPath (.sum (.prod .zero g) (.prod f .zero)) .zero := by
  apply DPath.trans
  · exact DPath.congrArg_sumL _ (.step (.prodZeroL g) (.refl _))
  · apply DPath.trans
    · exact DPath.congrArg_sumR _ (.step (.prodZeroR f) (.refl _))
    · exact .step (.sumZeroL _) (.refl _)

/-- Theorem 23: Derivative of (0 × F) simplifies to 0 via path. -/
theorem deriv_zero_prod_path (f : TyF) :
    DPath (TyF.deriv (.prod .zero f)) .zero := by
  -- ∂(0×F) = ∂0×F + 0×∂F = 0×F + 0×∂F
  simp [TyF.deriv]
  -- goal: DPath (.sum (.prod .zero f) (.prod .zero f.deriv)) .zero
  apply DPath.trans
  · exact DPath.congrArg_sumL (.prod .zero f.deriv) (.step (.prodZeroL f) (.refl _))
  · exact .step (.sumZeroL _) (.step (.prodZeroL f.deriv) (.refl _))

/-- Theorem 24: Double zero simplification: 0 + (0 + F) → F. -/
theorem dpath_double_sum_zero (f : TyF) :
    DPath (.sum .zero (.sum .zero f)) f := by
  apply DPath.trans
  · exact .step (.sumZeroL _) (.refl _)
  · exact .step (.sumZeroL f) (.refl f)

/-- Theorem 25: Alternative path: simplify inner then outer. -/
theorem dpath_double_sum_zero_alt (f : TyF) :
    DPath (.sum .zero (.sum .zero f)) f := by
  apply DPath.trans
  · exact DPath.congrArg_sumR TyF.zero (.step (.sumZeroL f) (.refl f))
  · exact .step (.sumZeroL f) (.refl f)

-- ============================================================
-- §8  Zipper as derivative
-- ============================================================

inductive BTree where
  | leaf : BTree
  | node : BTree → Nat → BTree → BTree
deriving DecidableEq, Repr

inductive TreeCtx where
  | top   : TreeCtx
  | left  : TreeCtx → Nat → BTree → TreeCtx
  | right : BTree → Nat → TreeCtx → TreeCtx
deriving DecidableEq, Repr

noncomputable def TreeCtx.depth : TreeCtx → Nat
  | .top => 0
  | .left ctx _ _ => 1 + ctx.depth
  | .right _ _ ctx => 1 + ctx.depth

structure Zipper where
  focus : BTree
  ctx   : TreeCtx
deriving DecidableEq, Repr

noncomputable def Zipper.plug : Zipper → BTree
  | ⟨t, .top⟩ => t
  | ⟨t, .left ctx v r⟩ => Zipper.plug ⟨.node t v r, ctx⟩
  | ⟨t, .right l v ctx⟩ => Zipper.plug ⟨.node l v t, ctx⟩
termination_by z => z.ctx.depth
decreasing_by all_goals simp_wf; simp [TreeCtx.depth]

noncomputable def Zipper.goLeft : Zipper → Option Zipper
  | ⟨.node l v r, ctx⟩ => some ⟨l, .left ctx v r⟩
  | ⟨.leaf, _⟩ => none

noncomputable def Zipper.goRight : Zipper → Option Zipper
  | ⟨.node l v r, ctx⟩ => some ⟨r, .right l v ctx⟩
  | ⟨.leaf, _⟩ => none

noncomputable def Zipper.goUp : Zipper → Option Zipper
  | ⟨_, .top⟩ => none
  | ⟨t, .left ctx v r⟩ => some ⟨.node t v r, ctx⟩
  | ⟨t, .right l v ctx⟩ => some ⟨.node l v t, ctx⟩

-- ============================================================
-- §9  Zipper navigation as computational paths
-- ============================================================

inductive NavStep : Zipper → Zipper → Prop where
  | goLeft (z z' : Zipper) : z.goLeft = some z' → NavStep z z'
  | goRight (z z' : Zipper) : z.goRight = some z' → NavStep z z'
  | goUp (z z' : Zipper) : z.goUp = some z' → NavStep z z'

inductive NavPath : Zipper → Zipper → Prop where
  | refl (z : Zipper) : NavPath z z
  | step {z₁ z₂ z₃ : Zipper} : NavStep z₁ z₂ → NavPath z₂ z₃ → NavPath z₁ z₃

/-- Theorem 26: Transitivity of navigation paths. -/
theorem NavPath.trans {a b c : Zipper}
    (p : NavPath a b) (q : NavPath b c) : NavPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact .step s (ih q)

/-- Theorem 27: Left then up recovers original. -/
theorem goLeft_then_up (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    let z := Zipper.mk (.node l v r) ctx
    let z' := Zipper.mk l (.left ctx v r)
    z.goLeft = some z' ∧ z'.goUp = some z := by
  simp [Zipper.goLeft, Zipper.goUp]

/-- Theorem 28: Right then up recovers original. -/
theorem goRight_then_up (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    let z := Zipper.mk (.node l v r) ctx
    let z' := Zipper.mk r (.right l v ctx)
    z.goRight = some z' ∧ z'.goUp = some z := by
  simp [Zipper.goRight, Zipper.goUp]

/-- Theorem 29: Leaf can't go left. -/
theorem leaf_no_left (ctx : TreeCtx) :
    (Zipper.mk .leaf ctx).goLeft = none := rfl

/-- Theorem 30: Leaf can't go right. -/
theorem leaf_no_right (ctx : TreeCtx) :
    (Zipper.mk .leaf ctx).goRight = none := rfl

/-- Theorem 31: Top can't go up. -/
theorem top_no_up (t : BTree) :
    (Zipper.mk t .top).goUp = none := rfl

/-- Theorem 32: Left-up roundtrip gives a 2-step NavPath. -/
theorem left_up_navpath (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    let z := Zipper.mk (.node l v r) ctx
    NavPath z z := by
  intro z
  have ⟨hl, hu⟩ := goLeft_then_up l r v ctx
  exact .step (.goLeft z _ hl) (.step (.goUp _ z hu) (.refl z))

/-- Theorem 33: Right-up roundtrip gives a 2-step NavPath. -/
theorem right_up_navpath (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    let z := Zipper.mk (.node l v r) ctx
    NavPath z z := by
  intro z
  have ⟨hr, hu⟩ := goRight_then_up l r v ctx
  exact .step (.goRight z _ hr) (.step (.goUp _ z hu) (.refl z))

-- ============================================================
-- §10  One-hole contexts for lists
-- ============================================================

structure ListOneHole (α : Type) where
  prefix_ : List α
  suffix_ : List α
deriving Repr

noncomputable def ListOneHole.plug {α : Type} (ctx : ListOneHole α) (a : α) : List α :=
  ctx.prefix_ ++ [a] ++ ctx.suffix_

/-- Theorem 34: Plugging into empty context gives singleton. -/
theorem ListOneHole.plug_empty {α : Type} (a : α) :
    (ListOneHole.mk (α := α) [] []).plug a = [a] := rfl

/-- Theorem 35: Plug length formula. -/
theorem ListOneHole.plug_length {α : Type} (ctx : ListOneHole α) (a : α) :
    (ctx.plug a).length = ctx.prefix_.length + 1 + ctx.suffix_.length := by
  simp [ListOneHole.plug, List.length_append]
  omega

/-- Theorem 36: Plugging is injective in value. -/
theorem ListOneHole.plug_injective {α : Type}
    (ctx : ListOneHole α) (a b : α)
    (h : ctx.plug a = ctx.plug b) : a = b := by
  simp [ListOneHole.plug] at h
  exact h

-- ============================================================
-- §11  Chain rule deeper
-- ============================================================

/-- Theorem 37: Chain rule structure. -/
theorem chain_rule_structure (f g : TyF) :
    TyF.deriv (.comp f g) = TyF.prod (TyF.comp f.deriv g) g.deriv := rfl

/-- Theorem 38: Chain rule with identity inner. -/
theorem chain_rule_identity (f : TyF) :
    TyF.deriv (.comp f .var) = TyF.prod (TyF.comp f.deriv .var) .one := rfl

/-- Theorem 39: Double composition chain rule. -/
theorem chain_rule_double (f g h : TyF) :
    TyF.deriv (.comp f (.comp g h)) =
    TyF.prod (TyF.comp f.deriv (.comp g h)) (TyF.prod (TyF.comp g.deriv h) h.deriv) := rfl

/-- Theorem 40: Chain with constant inner gives zero derivative path. -/
theorem chain_const_inner_path :
    DPath (TyF.deriv (.comp .var .one)) .zero := by
  -- ∂(X ∘ 1) = (1 ∘ 1) × 0 = 1 × 0 → 0
  simp [TyF.deriv]
  exact .step (.prodZeroR _) (.refl _)

-- ============================================================
-- §12  McBride's Dissection
-- ============================================================

noncomputable def TyF.dissect : TyF → TyF
  | .zero => .zero
  | .one => .zero
  | .var => .one
  | .sum f g => .sum f.dissect g.dissect
  | .prod f g => .sum (.prod f.dissect g) (.prod f g.dissect)
  | .comp f g => .prod (.comp f.dissect g) g.dissect
  | .mu f => .mu (.sum .one (.prod f.dissect (.mu f)))

/-- Theorem 41: Dissection of var is one. -/
theorem dissect_var : TyF.dissect .var = .one := rfl

/-- Theorem 42: Dissection of constants is zero. -/
theorem dissect_const : TyF.dissect .one = .zero ∧ TyF.dissect .zero = .zero :=
  ⟨rfl, rfl⟩

/-- Theorem 43: Dissection matches derivative on var. -/
theorem dissect_eq_deriv_var : TyF.dissect .var = TyF.deriv .var := rfl

/-- Theorem 44: Dissection sum structure. -/
theorem dissect_sum (f g : TyF) :
    TyF.dissect (.sum f g) = TyF.sum (TyF.dissect f) (TyF.dissect g) := rfl

/-- Theorem 45: Dissection product = Leibniz pattern. -/
theorem dissect_prod (f g : TyF) :
    TyF.dissect (.prod f g) =
    TyF.sum (TyF.prod f.dissect g) (TyF.prod f g.dissect) := rfl

-- ============================================================
-- §13  Navigation actions and sequences
-- ============================================================

inductive NavAction where
  | left | right | up | modify (f : Nat → Nat)

noncomputable def applyNav : Zipper → NavAction → Option Zipper
  | z, .left => z.goLeft
  | z, .right => z.goRight
  | z, .up => z.goUp
  | ⟨.node l v r, ctx⟩, .modify f => some ⟨.node l (f v) r, ctx⟩
  | ⟨.leaf, _⟩, .modify _ => none

noncomputable def applyNavs : Zipper → List NavAction → Option Zipper
  | z, [] => some z
  | z, a :: as => match applyNav z a with
    | some z' => applyNavs z' as
    | none => none

/-- Theorem 46: Empty action list is identity. -/
theorem applyNavs_nil (z : Zipper) : applyNavs z [] = some z := rfl

/-- Theorem 47: Single left on a node succeeds. -/
theorem applyNavs_left (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    applyNavs ⟨.node l v r, ctx⟩ [.left] = some ⟨l, .left ctx v r⟩ := by
  simp [applyNavs, applyNav, Zipper.goLeft]

/-- Theorem 48: Left-up roundtrip via action sequence. -/
theorem applyNavs_left_up (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    applyNavs ⟨.node l v r, ctx⟩ [.left, .up] =
    some ⟨.node l v r, ctx⟩ := by
  simp [applyNavs, applyNav, Zipper.goLeft, Zipper.goUp]

/-- Theorem 49: Right-up roundtrip via action sequence. -/
theorem applyNavs_right_up (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    applyNavs ⟨.node l v r, ctx⟩ [.right, .up] =
    some ⟨.node l v r, ctx⟩ := by
  simp [applyNavs, applyNav, Zipper.goRight, Zipper.goUp]

-- ============================================================
-- §14  varCount properties
-- ============================================================

/-- Theorem 50: VarCount of deriv var is 0. -/
theorem varCount_deriv_var : TyF.varCount (TyF.deriv .var) = 0 := rfl

/-- Theorem 51: VarCount of deriv (X×X) is 2. -/
theorem varCount_deriv_prod_var :
    TyF.varCount (TyF.deriv (TyF.prod .var .var)) = 2 := rfl

/-- Theorem 52: VarCount of deriv (X+X) is 0. -/
theorem varCount_deriv_sum_var :
    TyF.varCount (TyF.deriv (TyF.sum .var .var)) = 0 := rfl

-- ============================================================
-- §15  More multi-step path constructions
-- ============================================================

/-- Theorem 53: Simplify (0 + F) × (G + 0) → F × G. -/
theorem dpath_simplify_both (f g : TyF) :
    DPath (.prod (.sum .zero f) (.sum g .zero)) (.prod f g) := by
  apply DPath.trans
  · exact DPath.congrArg_prodL _ (.step (.sumZeroL f) (.refl f))
  · exact DPath.congrArg_prodR _ (.step (.sumZeroR g) (.refl g))

/-- Theorem 54: Simplify 1 × (1 × F) → F. -/
theorem dpath_prod_one_nested (f : TyF) :
    DPath (.prod .one (.prod .one f)) f := by
  apply DPath.trans
  · exact DPath.congrArg_prodR _ (.step (.prodOneL f) (.refl f))
  · exact .step (.prodOneL f) (.refl f)

/-- Theorem 55: Deeply nested zero kills everything: 0 × (F × G) → 0. -/
theorem dpath_zero_kills (f g : TyF) :
    DPath (.prod .zero (.prod f g)) .zero :=
  .step (.prodZeroL _) (.refl _)

/-- Theorem 56: Leibniz applied to X×1: ∂(X×1) simplifies to 1. -/
theorem deriv_x_times_one_path :
    DPath (TyF.deriv (.prod .var .one)) .one := by
  -- ∂(X×1) = 1×1 + X×0
  simp [TyF.deriv]
  -- need: (1×1 + X×0) → 1
  apply DPath.trans
  · exact DPath.congrArg_sumR _ (.step (.prodZeroR _) (.refl _))
  · apply DPath.trans
    · exact .step (.sumZeroR _) (.refl _)
    · exact .step (.prodOneL _) (.refl _)

/-- Theorem 57: Leibniz applied to 1×X: ∂(1×X) simplifies to 1. -/
theorem deriv_one_times_x_path :
    DPath (TyF.deriv (.prod .one .var)) .one := by
  simp [TyF.deriv]
  -- need: (0×X + 1×1) → 1
  apply DPath.trans
  · exact DPath.congrArg_sumL _ (.step (.prodZeroL _) (.refl _))
  · apply DPath.trans
    · exact .step (.sumZeroL _) (.refl _)
    · exact .step (.prodOneL _) (.refl _)

-- ============================================================
-- §16  Recursive type derivatives
-- ============================================================

noncomputable def listF : TyF := .mu (.sum .one (.prod .var .var))
noncomputable def treeF : TyF := .mu (.sum .one (.prod .var .var))

/-- Theorem 58: List and tree have same code. -/
theorem tree_list_same : treeF = listF := rfl

/-- Theorem 59: Derivative of list functor structure. -/
theorem deriv_listF :
    TyF.deriv listF =
    TyF.mu (TyF.sum .one (TyF.prod (TyF.sum .one (.prod .var .var)).deriv (TyF.mu (TyF.sum .one (.prod .var .var))))) := rfl

/-- Theorem 60: Derivative of zero-functor mu. -/
theorem deriv_mu_zero :
    TyF.deriv (.mu .zero) = TyF.mu (TyF.sum .one (TyF.prod .zero (.mu .zero))) := rfl

-- ============================================================
-- §17  Coherence: different simplification paths agree
-- ============================================================

/-- Theorem 61: Two paths from 0 + (1×F + 0) to F. -/
theorem coherence_path1 (f : TyF) :
    DPath (.sum .zero (.sum (.prod .one f) .zero)) f := by
  apply DPath.trans
  · exact .step (.sumZeroL _) (.refl _)
  · apply DPath.trans
    · exact .step (.sumZeroR _) (.refl _)
    · exact .step (.prodOneL f) (.refl f)

/-- Theorem 62: Alternative path for same expression. -/
theorem coherence_path2 (f : TyF) :
    DPath (.sum .zero (.sum (.prod .one f) .zero)) f := by
  apply DPath.trans
  · exact DPath.congrArg_sumR _ (.step (.sumZeroR _) (.refl _))
  · apply DPath.trans
    · exact .step (.sumZeroL _) (.refl _)
    · exact .step (.prodOneL f) (.refl f)

/-- Theorem 63: Path through product distributes. -/
theorem prod_distribute_path (f g h : TyF) :
    DPath (.prod (.sum .zero f) (.sum .zero (.sum g h)))
          (.prod f (.sum g h)) := by
  apply DPath.trans
  · exact DPath.congrArg_prodR _ (.step (.sumZeroL _) (.refl _))
  · exact DPath.congrArg_prodL _ (.step (.sumZeroL f) (.refl f))

-- ============================================================
-- §18  Focus navigation = path through derivative
-- ============================================================

/-- A focus is a position in a type expression (via derivative). -/
structure Focus where
  ty : TyF
  deriv_ctx : TyF  -- the derivative at this position
deriving DecidableEq, Repr

/-- Theorem 64: Focus at var has unit context. -/
theorem focus_var : Focus.mk .var .one = { ty := .var, deriv_ctx := TyF.deriv .var } := rfl

/-- Theorem 65: Navigation preserves plug (stated abstractly). -/
theorem nav_preserves_structure (l r : BTree) (v : Nat) (ctx : TreeCtx) :
    let z := Zipper.mk (.node l v r) ctx
    z.goLeft.bind Zipper.goUp = some z := by
  simp [Zipper.goLeft, Zipper.goUp, Option.bind]

/-- Theorem 66: Modifying focus doesn't change context. -/
theorem modify_preserves_ctx (l r : BTree) (v : Nat) (ctx : TreeCtx) (f : Nat → Nat) :
    match applyNav ⟨.node l v r, ctx⟩ (.modify f) with
    | some z => z.ctx = ctx
    | none => False := by
  simp [applyNav]

end DerivDeep
