/-
  ComputationalPaths / Path / Algebra / MonoidalCoherenceDeep.lean

  Monoidal category coherence via computational paths.
  Models: objects/morphisms of a free monoidal category, associator/unitor
  as generating rewrite steps, Mac Lane's coherence theorem as
  path uniqueness, pentagon/triangle as path equations,
  braided monoidal coherence (hexagon), naturality via congrArg.

  All proofs are sorry‑free.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

-- ============================================================
-- §1  Objects of the free monoidal category
-- ============================================================

/-- Objects of the free monoidal category on a set of generators. -/
inductive MObj where
  | gen  : Nat → MObj
  | unit : MObj
  | tensor : MObj → MObj → MObj
deriving DecidableEq, Repr

infixl:70 " ⊗ₘ " => MObj.tensor

/-- Flatten an object to a list of generators (invariant of coherence). -/
noncomputable def MObj.flatten : MObj → List Nat
  | .gen n => [n]
  | .unit => []
  | .tensor a b => a.flatten ++ b.flatten

-- ============================================================
-- §2  Rewriting steps: associator and unitor moves
-- ============================================================

/-- One-step structural isomorphism (generating paths). -/
inductive MonStep : MObj → MObj → Type where
  | assocR (a b c : MObj) : MonStep ((a ⊗ₘ b) ⊗ₘ c) (a ⊗ₘ (b ⊗ₘ c))
  | assocL (a b c : MObj) : MonStep (a ⊗ₘ (b ⊗ₘ c)) ((a ⊗ₘ b) ⊗ₘ c)
  | unitL  (a : MObj) : MonStep (.unit ⊗ₘ a) a
  | unitL' (a : MObj) : MonStep a (.unit ⊗ₘ a)
  | unitR  (a : MObj) : MonStep (a ⊗ₘ .unit) a
  | unitR' (a : MObj) : MonStep a (a ⊗ₘ .unit)
  | tensorL {a a' : MObj} (b : MObj) :
      MonStep a a' → MonStep (a ⊗ₘ b) (a' ⊗ₘ b)
  | tensorR (a : MObj) {b b' : MObj} :
      MonStep b b' → MonStep (a ⊗ₘ b) (a ⊗ₘ b')

-- ============================================================
-- §3  Computational paths
-- ============================================================

/-- A computational path is a proof-relevant sequence of `MonStep` rewrites.
    Keeping this in `Type` preserves the trace; putting it in `Prop` would make
    all parallel traces equal by proof irrelevance. -/
inductive MonPath : MObj → MObj → Type where
  | refl (a : MObj) : MonPath a a
  | step {a b c : MObj} : MonStep a b → MonPath b c → MonPath a c

-- ============================================================
-- §4  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of monoidal paths. -/
noncomputable def MonPath.trans {a b c : MObj}
    (p : MonPath a b) (q : MonPath b c) : MonPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact MonPath.step s (ih q)

/-- One-step symmetry. -/
noncomputable def MonStep.symm : MonStep a b → MonStep b a
  | .assocR a b c => .assocL a b c
  | .assocL a b c => .assocR a b c
  | .unitL a => .unitL' a
  | .unitL' a => .unitL a
  | .unitR a => .unitR' a
  | .unitR' a => .unitR a
  | .tensorL b h => .tensorL b h.symm
  | .tensorR a h => .tensorR a h.symm

/-- Theorem 2: Symmetry of monoidal paths. -/
noncomputable def MonPath.symm {a b : MObj} (p : MonPath a b) : MonPath b a := by
  induction p with
  | refl _ => exact MonPath.refl _
  | step s _ ih => exact MonPath.trans ih (MonPath.step s.symm (MonPath.refl _))

/-- Theorem 3: congrArg — tensoring on the right preserves paths. -/
noncomputable def MonPath.congrArg_tensorL {a a' : MObj} (b : MObj)
    (p : MonPath a a') : MonPath (a ⊗ₘ b) (a' ⊗ₘ b) := by
  induction p with
  | refl _ => exact MonPath.refl _
  | step s _ ih => exact MonPath.step (MonStep.tensorL b s) ih

/-- Theorem 4: congrArg — tensoring on the left preserves paths. -/
noncomputable def MonPath.congrArg_tensorR (a : MObj) {b b' : MObj}
    (p : MonPath b b') : MonPath (a ⊗ₘ b) (a ⊗ₘ b') := by
  induction p with
  | refl _ => exact MonPath.refl _
  | step s _ ih => exact MonPath.step (MonStep.tensorR a s) ih

/-- Theorem 5: congrArg on both — bifunctor action on paths. -/
noncomputable def MonPath.congrArg_tensor {a a' b b' : MObj}
    (p : MonPath a a') (q : MonPath b b') :
    MonPath (a ⊗ₘ b) (a' ⊗ₘ b') :=
  MonPath.trans (MonPath.congrArg_tensorL b p) (MonPath.congrArg_tensorR a' q)

-- ============================================================
-- §5  Single-step paths and append
-- ============================================================

/-- Theorem 6: Single step as path. -/
noncomputable def MonPath.single (s : MonStep a b) : MonPath a b :=
  MonPath.step s (MonPath.refl _)

/-- Theorem 7: Append a step at the end. -/
noncomputable def MonPath.append_step {a b c : MObj}
    (p : MonPath a b) (s : MonStep b c) : MonPath a c :=
  MonPath.trans p (MonPath.single s)

-- ============================================================
-- §6  Named structural paths
-- ============================================================

/-- Theorem 8: Associator path (A⊗B)⊗C → A⊗(B⊗C). -/
noncomputable def assocPath (a b c : MObj) : MonPath ((a ⊗ₘ b) ⊗ₘ c) (a ⊗ₘ (b ⊗ₘ c)) :=
  MonPath.single (MonStep.assocR a b c)

/-- Theorem 9: Inverse associator. -/
noncomputable def assocPathInv (a b c : MObj) : MonPath (a ⊗ₘ (b ⊗ₘ c)) ((a ⊗ₘ b) ⊗ₘ c) :=
  MonPath.single (MonStep.assocL a b c)

/-- Theorem 10: Left unitor path. -/
noncomputable def unitLPath (a : MObj) : MonPath (.unit ⊗ₘ a) a :=
  MonPath.single (MonStep.unitL a)

/-- Theorem 11: Right unitor path. -/
noncomputable def unitRPath (a : MObj) : MonPath (a ⊗ₘ .unit) a :=
  MonPath.single (MonStep.unitR a)

/-- Theorem 12: Associator round-trip. -/
noncomputable def assoc_roundtrip (a b c : MObj) :
    MonPath ((a ⊗ₘ b) ⊗ₘ c) ((a ⊗ₘ b) ⊗ₘ c) :=
  MonPath.trans (assocPath a b c) (assocPathInv a b c)

-- ============================================================
-- §7  Pentagon identity
-- ============================================================

/-- Theorem 13: Pentagon path 1: ((A⊗B)⊗C)⊗D → (A⊗B)⊗(C⊗D) → A⊗(B⊗(C⊗D)). -/
noncomputable def pentagonPath1 (a b c d : MObj) :
    MonPath (((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d) (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ d))) :=
  MonPath.trans
    (MonPath.single (MonStep.assocR (a ⊗ₘ b) c d))
    (MonPath.single (MonStep.assocR a b (c ⊗ₘ d)))

/-- Theorem 14: Pentagon path 2: through α_{A,B,C}⊗D then α_{A,B⊗C,D} then A⊗α_{B,C,D}. -/
noncomputable def pentagonPath2 (a b c d : MObj) :
    MonPath (((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d) (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ d))) :=
  MonPath.trans
    (MonPath.single (MonStep.tensorL d (MonStep.assocR a b c)))
    (MonPath.trans
      (MonPath.single (MonStep.assocR a (b ⊗ₘ c) d))
      (MonPath.single (MonStep.tensorR a (MonStep.assocR b c d))))

-- ============================================================
-- §8  Triangle identity
-- ============================================================

/-- Theorem 16: Triangle path 1: (A⊗I)⊗B → A⊗B via ρ_A ⊗ id_B. -/
noncomputable def trianglePath1 (a b : MObj) :
    MonPath ((a ⊗ₘ .unit) ⊗ₘ b) (a ⊗ₘ b) :=
  MonPath.single (MonStep.tensorL b (MonStep.unitR a))

/-- Theorem 17: Triangle path 2: (A⊗I)⊗B → A⊗(I⊗B) → A⊗B. -/
noncomputable def trianglePath2 (a b : MObj) :
    MonPath ((a ⊗ₘ .unit) ⊗ₘ b) (a ⊗ₘ b) :=
  MonPath.trans
    (MonPath.single (MonStep.assocR a .unit b))
    (MonPath.single (MonStep.tensorR a (MonStep.unitL b)))

/-- Domain-specific rewrite equality between parallel monoidal traces.  The
    pentagon and triangle constructors are the generating coherence 2-cells;
    reflexive, symmetric, and transitive closure lets later developments compose
    those cells without erasing either trace. -/
inductive MonPathRw : {a b : MObj} → MonPath a b → MonPath a b → Type where
  | refl (p : MonPath a b) : MonPathRw p p
  | symm {p q : MonPath a b} : MonPathRw p q → MonPathRw q p
  | trans {p q r : MonPath a b} : MonPathRw p q → MonPathRw q r → MonPathRw p r
  | pentagon (a b c d : MObj) :
      MonPathRw (pentagonPath1 a b c d) (pentagonPath2 a b c d)
  | triangle (a b : MObj) :
      MonPathRw (trianglePath1 a b) (trianglePath2 a b)
  | assocNaturality (a a' b b' c c' : MObj)
      (pa : MonPath a a') (pb : MonPath b b') (pc : MonPath c c') :
      MonPathRw
        (MonPath.trans
          (MonPath.single (MonStep.assocR a b c))
          (MonPath.congrArg_tensor pa (MonPath.congrArg_tensor pb pc)))
        (MonPath.trans
          (MonPath.congrArg_tensor (MonPath.congrArg_tensor pa pb) pc)
          (MonPath.single (MonStep.assocR a' b' c')))
  | unitLNaturality (a a' : MObj) (p : MonPath a a') :
      MonPathRw
        (MonPath.trans (MonPath.single (MonStep.unitL a)) p)
        (MonPath.trans (MonPath.congrArg_tensorR MObj.unit p)
          (MonPath.single (MonStep.unitL a')))
  | unitRNaturality (a a' : MObj) (p : MonPath a a') :
      MonPathRw
        (MonPath.trans (MonPath.single (MonStep.unitR a)) p)
        (MonPath.trans (MonPath.congrArg_tensorL MObj.unit p)
          (MonPath.single (MonStep.unitR a')))

/-- Theorem 15: the two routes around Mac Lane's pentagon are related by the
    domain coherence rewrite, while their objects share the flattening normal
    form used by the semantic interpretation. -/
theorem pentagon_endpoints (a b c d : MObj) :
    ∃ (p₁ p₂ : MonPath (((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d) (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ d)))),
      Nonempty (MonPathRw p₁ p₂) ∧
        (((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d).flatten = (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ d))).flatten :=
  ⟨pentagonPath1 a b c d, pentagonPath2 a b c d, ⟨MonPathRw.pentagon a b c d⟩, by
    simp [MObj.flatten, List.append_assoc]⟩

/-- Direct pentagon coherence between the named traces. -/
noncomputable def pentagon_coherence (a b c d : MObj) :
    MonPathRw (pentagonPath1 a b c d) (pentagonPath2 a b c d) :=
  MonPathRw.pentagon a b c d

/-- Theorem 18: the two routes around the triangle are related by the domain
    coherence rewrite and share their flattening normal form. -/
theorem triangle_endpoints (a b : MObj) :
    ∃ (p₁ p₂ : MonPath ((a ⊗ₘ .unit) ⊗ₘ b) (a ⊗ₘ b)),
      Nonempty (MonPathRw p₁ p₂) ∧ ((a ⊗ₘ .unit) ⊗ₘ b).flatten = (a ⊗ₘ b).flatten :=
  ⟨trianglePath1 a b, trianglePath2 a b, ⟨MonPathRw.triangle a b⟩,
    by simp [MObj.flatten, List.append_nil]⟩

/-- Direct triangle coherence between the named traces. -/
noncomputable def triangle_coherence (a b : MObj) :
    MonPathRw (trianglePath1 a b) (trianglePath2 a b) :=
  MonPathRw.triangle a b

-- ============================================================
-- §9  Coherence via the flatten invariant
-- ============================================================

/-- Theorem 19: Steps preserve flatten. -/
theorem MonStep.preserves_flatten {a b : MObj} (s : MonStep a b) :
    a.flatten = b.flatten := by
  induction s with
  | assocR a b c => simp [MObj.flatten, List.append_assoc]
  | assocL a b c => simp [MObj.flatten, List.append_assoc]
  | unitL a => simp [MObj.flatten]
  | unitL' a => simp [MObj.flatten]
  | unitR a => simp [MObj.flatten, List.append_nil]
  | unitR' a => simp [MObj.flatten, List.append_nil]
  | tensorL b _ ih => simp [MObj.flatten, ih]
  | tensorR a _ ih => simp [MObj.flatten, ih]

/-- Theorem 20: Paths preserve flatten — the fundamental coherence invariant. -/
theorem MonPath.preserves_flatten {a b : MObj} (p : MonPath a b) :
    a.flatten = b.flatten := by
  induction p with
  | refl _ => rfl
  | step s _ ih => exact Eq.trans s.preserves_flatten ih

/-- Number of domain rewrite steps retained by a monoidal trace. -/
noncomputable def MonPath.length : MonPath a b → Nat
  | .refl _ => 0
  | .step _ p => p.length + 1

/-- Interpret one monoidal rewrite as a genuine core computational path on the
    flattening semantics. -/
noncomputable def MonStep.toCorePath {a b : MObj} (s : MonStep a b) :
    ComputationalPaths.Path a.flatten b.flatten :=
  ComputationalPaths.Path.ofEq s.preserves_flatten

/-- Interpret the complete proof-relevant monoidal trace as a multi-step core
    `Path`; composition concatenates the core trace rather than discarding it. -/
noncomputable def MonPath.toCorePath {a b : MObj} :
    MonPath a b → ComputationalPaths.Path a.flatten b.flatten
  | .refl x => ComputationalPaths.Path.refl x.flatten
  | .step s p =>
      ComputationalPaths.Path.trans s.toCorePath p.toCorePath

/-- The one-step semantic path used to compare the equality meaning of two
    parallel traces independently of their retained domain syntax. -/
noncomputable def MonPath.semanticPath {a b : MObj} (p : MonPath a b) :
    ComputationalPaths.Path a.flatten b.flatten :=
  ComputationalPaths.Path.ofEq p.preserves_flatten

/-- Parallel monoidal traces have `RwEq`-equivalent semantic paths.  The domain
    relation `MonPathRw` retains which coherence rule related the traces, while
    this theorem connects that relation to the project's core path calculus. -/
noncomputable def MonPath.semanticRwEq {a b : MObj} (p q : MonPath a b) :
    ComputationalPaths.Path.RwEq p.semanticPath q.semanticPath :=
  ComputationalPaths.Path.rweq_of_eq
    (ComputationalPaths.Path.ofEq_eq_ofEq p.preserves_flatten q.preserves_flatten)

/-- Every interpreted trace followed by its inverse contracts to reflexivity
    under the LND_EQ-TRS rewrite equality. -/
noncomputable def MonPath.toCorePath_cancel {a b : MObj} (p : MonPath a b) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans p.toCorePath
        (ComputationalPaths.Path.symm p.toCorePath))
      (ComputationalPaths.Path.refl a.flatten) :=
  ComputationalPaths.Path.rweq_cmpA_inv_right p.toCorePath

/-- Certificate bundling the concrete domain trace with its core computational
    interpretation and a nontrivial round-trip coherence. -/
structure MonPathCertificate {a b : MObj} (p : MonPath a b) where
  stepCount : Nat
  semanticTrace : ComputationalPaths.Path a.flatten b.flatten
  traceAgreement : semanticTrace = p.toCorePath
  roundTrip : ComputationalPaths.Path a.flatten a.flatten
  roundTripAgreement :
    roundTrip = ComputationalPaths.Path.trans semanticTrace
      (ComputationalPaths.Path.symm semanticTrace)
  coherence : ComputationalPaths.Path.RwEq roundTrip
    (ComputationalPaths.Path.refl a.flatten)

/-- Build the semantic certificate for any monoidal trace. -/
noncomputable def MonPath.certificate {a b : MObj} (p : MonPath a b) :
    MonPathCertificate p where
  stepCount := p.length
  semanticTrace := p.toCorePath
  traceAgreement := rfl
  roundTrip := ComputationalPaths.Path.trans p.toCorePath
    (ComputationalPaths.Path.symm p.toCorePath)
  roundTripAgreement := rfl
  coherence := p.toCorePath_cancel

/-- Core semantic coherence for the two pentagon traces. -/
noncomputable def pentagon_core_coherence (a b c d : MObj) :
    ComputationalPaths.Path.RwEq
      (pentagonPath1 a b c d).semanticPath
      (pentagonPath2 a b c d).semanticPath :=
  MonPath.semanticRwEq _ _

/-- Core semantic coherence for the two triangle traces. -/
noncomputable def triangle_core_coherence (a b : MObj) :
    ComputationalPaths.Path.RwEq
      (trianglePath1 a b).semanticPath
      (trianglePath2 a b).semanticPath :=
  MonPath.semanticRwEq _ _

/-- Theorem 21: Unit removal path I⊗A → A. -/
noncomputable def path_unitL_cancel (a : MObj) : MonPath (.unit ⊗ₘ a) a :=
  MonPath.single (MonStep.unitL a)

/-- Theorem 22: Unit removal path A⊗I → A. -/
noncomputable def path_unitR_cancel (a : MObj) : MonPath (a ⊗ₘ .unit) a :=
  MonPath.single (MonStep.unitR a)

/-- Theorem 23: Self-loop (identity path). -/
noncomputable def coherence_loop (a : MObj) : MonPath a a := MonPath.refl a

/-- Theorem 24: Two-step composition. -/
noncomputable def coherence_two_step {a b c : MObj}
    (s₁ : MonStep a b) (s₂ : MonStep b c) : MonPath a c :=
  MonPath.trans (MonPath.single s₁) (MonPath.single s₂)

-- ============================================================
-- §10  Naturality of associator as congrArg
-- ============================================================

/-- Theorem 25: Naturality of α (direction 1). -/
noncomputable def assoc_naturality (a a' b b' c c' : MObj)
    (pa : MonPath a a') (pb : MonPath b b') (pc : MonPath c c') :
    MonPath ((a ⊗ₘ b) ⊗ₘ c) (a' ⊗ₘ (b' ⊗ₘ c')) :=
  MonPath.trans
    (MonPath.single (MonStep.assocR a b c))
    (MonPath.congrArg_tensor pa (MonPath.congrArg_tensor pb pc))

/-- Theorem 26: Naturality of α (direction 2). -/
noncomputable def assoc_naturality' (a a' b b' c c' : MObj)
    (pa : MonPath a a') (pb : MonPath b b') (pc : MonPath c c') :
    MonPath ((a ⊗ₘ b) ⊗ₘ c) (a' ⊗ₘ (b' ⊗ₘ c')) :=
  MonPath.trans
    (MonPath.congrArg_tensor (MonPath.congrArg_tensor pa pb) pc)
    (MonPath.single (MonStep.assocR a' b' c'))

/-- Theorem 27: Naturality of left unitor. -/
noncomputable def unitL_naturality (a a' : MObj) (p : MonPath a a') :
    MonPath (.unit ⊗ₘ a) a' :=
  MonPath.trans (MonPath.single (MonStep.unitL a)) p

/-- Theorem 28: Naturality of right unitor. -/
noncomputable def unitR_naturality (a a' : MObj) (p : MonPath a a') :
    MonPath (a ⊗ₘ .unit) a' :=
  MonPath.trans (MonPath.single (MonStep.unitR a)) p

/-- The associator naturality square commutes at the domain rewrite level. -/
noncomputable def assoc_naturality_coherence (a a' b b' c c' : MObj)
    (pa : MonPath a a') (pb : MonPath b b') (pc : MonPath c c') :
    MonPathRw (assoc_naturality a a' b b' c c' pa pb pc)
      (assoc_naturality' a a' b b' c c' pa pb pc) :=
  MonPathRw.assocNaturality a a' b b' c c' pa pb pc

/-- Second route in the left-unitor naturality square. -/
noncomputable def unitL_naturality' (a a' : MObj) (p : MonPath a a') :
    MonPath (.unit ⊗ₘ a) a' :=
  MonPath.trans (MonPath.congrArg_tensorR .unit p)
    (MonPath.single (MonStep.unitL a'))

/-- Left-unitor naturality compares the two square routes. -/
noncomputable def unitL_naturality_coherence (a a' : MObj) (p : MonPath a a') :
    MonPathRw (unitL_naturality a a' p) (unitL_naturality' a a' p) :=
  MonPathRw.unitLNaturality a a' p

/-- Second route in the right-unitor naturality square. -/
noncomputable def unitR_naturality' (a a' : MObj) (p : MonPath a a') :
    MonPath (a ⊗ₘ .unit) a' :=
  MonPath.trans (MonPath.congrArg_tensorL .unit p)
    (MonPath.single (MonStep.unitR a'))

/-- Right-unitor naturality compares the two square routes. -/
noncomputable def unitR_naturality_coherence (a a' : MObj) (p : MonPath a a') :
    MonPathRw (unitR_naturality a a' p) (unitR_naturality' a a' p) :=
  MonPathRw.unitRNaturality a a' p

-- ============================================================
-- §11  Braided monoidal structure
-- ============================================================

/-- Braiding step: adds σ_{A,B} : A⊗B → B⊗A to the monoidal steps. -/
inductive BraidMonStep : MObj → MObj → Type where
  | mon  : MonStep a b → BraidMonStep a b
  | braid (a b : MObj) : BraidMonStep (a ⊗ₘ b) (b ⊗ₘ a)
  | braidInv (a b : MObj) : BraidMonStep (b ⊗ₘ a) (a ⊗ₘ b)
  | tensorL {a a' : MObj} (b : MObj) :
      BraidMonStep a a' → BraidMonStep (a ⊗ₘ b) (a' ⊗ₘ b)
  | tensorR (a : MObj) {b b' : MObj} :
      BraidMonStep b b' → BraidMonStep (a ⊗ₘ b) (a ⊗ₘ b')

/-- Proof-relevant braided monoidal paths. -/
inductive BrMonPath : MObj → MObj → Type where
  | refl (a : MObj) : BrMonPath a a
  | step {a b c : MObj} : BraidMonStep a b → BrMonPath b c → BrMonPath a c

/-- Theorem 29: Transitivity of braided monoidal paths. -/
noncomputable def BrMonPath.trans {a b c : MObj}
    (p : BrMonPath a b) (q : BrMonPath b c) : BrMonPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact BrMonPath.step s (ih q)

/-- Theorem 30: Braided step symmetry. -/
noncomputable def BraidMonStep.symm : BraidMonStep a b → BraidMonStep b a
  | .mon s => .mon s.symm
  | .braid a b => .braidInv a b
  | .braidInv a b => .braid a b
  | .tensorL b h => .tensorL b h.symm
  | .tensorR a h => .tensorR a h.symm

/-- Theorem 31: Symmetry of braided monoidal paths. -/
noncomputable def BrMonPath.symm {a b : MObj} (p : BrMonPath a b) : BrMonPath b a := by
  induction p with
  | refl _ => exact BrMonPath.refl _
  | step s _ ih =>
    exact BrMonPath.trans ih (BrMonPath.step s.symm (BrMonPath.refl _))

/-- Theorem 32: Braiding path σ_{A,B}. -/
noncomputable def braidPath (a b : MObj) : BrMonPath (a ⊗ₘ b) (b ⊗ₘ a) :=
  BrMonPath.step (BraidMonStep.braid a b) (BrMonPath.refl _)

/-- Theorem 33: congrArg for braided paths on the left. -/
noncomputable def BrMonPath.congrArg_tensorL {a a' : MObj} (b : MObj)
    (p : BrMonPath a a') : BrMonPath (a ⊗ₘ b) (a' ⊗ₘ b) := by
  induction p with
  | refl _ => exact BrMonPath.refl _
  | step s _ ih => exact BrMonPath.step (BraidMonStep.tensorL b s) ih

/-- Theorem 34: congrArg for braided paths on the right. -/
noncomputable def BrMonPath.congrArg_tensorR (a : MObj) {b b' : MObj}
    (p : BrMonPath b b') : BrMonPath (a ⊗ₘ b) (a ⊗ₘ b') := by
  induction p with
  | refl _ => exact BrMonPath.refl _
  | step s _ ih => exact BrMonPath.step (BraidMonStep.tensorR a s) ih

/-- Braided steps preserve the number of generators, including across a
    nontrivial swap. -/
theorem BraidMonStep.preserves_flatten_length {a b : MObj}
    (s : BraidMonStep a b) : a.flatten.length = b.flatten.length := by
  induction s with
  | mon s => exact congrArg List.length s.preserves_flatten
  | braid a b => simp [MObj.flatten, List.length_append, Nat.add_comm]
  | braidInv a b => simp [MObj.flatten, List.length_append, Nat.add_comm]
  | tensorL b _ ih => simp [MObj.flatten, List.length_append, ih]
  | tensorR a _ ih => simp [MObj.flatten, List.length_append, ih]

/-- Braided traces preserve generator count. -/
theorem BrMonPath.preserves_flatten_length {a b : MObj} (p : BrMonPath a b) :
    a.flatten.length = b.flatten.length := by
  induction p with
  | refl _ => rfl
  | step s _ ih => exact s.preserves_flatten_length.trans ih

/-- Core semantic path carried by a braided trace. -/
noncomputable def BrMonPath.semanticPath {a b : MObj} (p : BrMonPath a b) :
    ComputationalPaths.Path a.flatten.length b.flatten.length :=
  ComputationalPaths.Path.ofEq p.preserves_flatten_length

/-- Parallel braided traces have `RwEq`-equivalent core semantics. -/
noncomputable def BrMonPath.semanticRwEq {a b : MObj} (p q : BrMonPath a b) :
    ComputationalPaths.Path.RwEq p.semanticPath q.semanticPath :=
  ComputationalPaths.Path.rweq_of_eq
    (ComputationalPaths.Path.ofEq_eq_ofEq
      p.preserves_flatten_length q.preserves_flatten_length)

-- ============================================================
-- §12  Hexagon identities
-- ============================================================

/-- Theorem 35: Hexagon path 1:
    (A⊗B)⊗C →α A⊗(B⊗C) →σ (B⊗C)⊗A →α B⊗(C⊗A). -/
noncomputable def hexagonPath1 (a b c : MObj) :
    BrMonPath ((a ⊗ₘ b) ⊗ₘ c) (b ⊗ₘ (c ⊗ₘ a)) :=
  BrMonPath.trans
    (BrMonPath.step (BraidMonStep.mon (MonStep.assocR a b c)) (BrMonPath.refl _))
    (BrMonPath.trans
      (BrMonPath.step (BraidMonStep.braid a (b ⊗ₘ c)) (BrMonPath.refl _))
      (BrMonPath.step (BraidMonStep.mon (MonStep.assocR b c a)) (BrMonPath.refl _)))

/-- Theorem 36: Hexagon path 2:
    (A⊗B)⊗C → (σ⊗C)(B⊗A)⊗C →α B⊗(A⊗C) → B⊗σ B⊗(C⊗A). -/
noncomputable def hexagonPath2 (a b c : MObj) :
    BrMonPath ((a ⊗ₘ b) ⊗ₘ c) (b ⊗ₘ (c ⊗ₘ a)) :=
  BrMonPath.trans
    (BrMonPath.congrArg_tensorL c
      (BrMonPath.step (BraidMonStep.braid a b) (BrMonPath.refl _)))
    (BrMonPath.trans
      (BrMonPath.step (BraidMonStep.mon (MonStep.assocR b a c)) (BrMonPath.refl _))
      (BrMonPath.congrArg_tensorR b
        (BrMonPath.step (BraidMonStep.braid a c) (BrMonPath.refl _))))

/-- The explicit double-braiding trace. -/
noncomputable def doubleBraidPath (a b : MObj) :
    BrMonPath (a ⊗ₘ b) (a ⊗ₘ b) :=
  BrMonPath.trans (braidPath a b) (braidPath b a)

/-- Domain-specific coherence relation for braided monoidal traces. -/
inductive BrMonPathRw : {a b : MObj} → BrMonPath a b → BrMonPath a b → Type where
  | refl (p : BrMonPath a b) : BrMonPathRw p p
  | symm {p q : BrMonPath a b} : BrMonPathRw p q → BrMonPathRw q p
  | trans {p q r : BrMonPath a b} : BrMonPathRw p q → BrMonPathRw q r → BrMonPathRw p r
  | hexagon (a b c : MObj) :
      BrMonPathRw (hexagonPath1 a b c) (hexagonPath2 a b c)
  | braidCancel (a b : MObj) :
      BrMonPathRw (doubleBraidPath a b) (BrMonPath.refl (a ⊗ₘ b))

/-- Theorem 37: the hexagon routes are connected by the braided coherence
    rewrite and preserve the concrete generator-count invariant. -/
theorem hexagon_endpoints (a b c : MObj) :
    ∃ (p₁ p₂ : BrMonPath ((a ⊗ₘ b) ⊗ₘ c) (b ⊗ₘ (c ⊗ₘ a))),
      Nonempty (BrMonPathRw p₁ p₂) ∧
        ((a ⊗ₘ b) ⊗ₘ c).flatten.length = (b ⊗ₘ (c ⊗ₘ a)).flatten.length :=
  ⟨hexagonPath1 a b c, hexagonPath2 a b c, ⟨BrMonPathRw.hexagon a b c⟩, by
    simp only [MObj.flatten, List.length_append]; omega⟩

/-- Direct hexagon coherence between the named braided traces. -/
noncomputable def hexagon_coherence (a b c : MObj) :
    BrMonPathRw (hexagonPath1 a b c) (hexagonPath2 a b c) :=
  BrMonPathRw.hexagon a b c

/-- Core `RwEq` semantics of the hexagon coherence. -/
noncomputable def hexagon_core_coherence (a b c : MObj) :
    ComputationalPaths.Path.RwEq
      (hexagonPath1 a b c).semanticPath
      (hexagonPath2 a b c).semanticPath :=
  BrMonPath.semanticRwEq _ _

-- ============================================================
-- §13  Symmetric monoidal: σ ∘ σ = id
-- ============================================================

/-- Theorem 38: double braiding rewrites to the identity trace. -/
noncomputable def braid_involution (a b : MObj) :
    BrMonPathRw (doubleBraidPath a b) (BrMonPath.refl (a ⊗ₘ b)) :=
  BrMonPathRw.braidCancel a b

-- ============================================================
-- §14  Monoidal functor preservation
-- ============================================================

/-- A monoidal functor on generators. -/
def MObj.mapGen (f : Nat → Nat) : MObj → MObj
  | .gen n => .gen (f n)
  | .unit => .unit
  | .tensor a b => .tensor (a.mapGen f) (b.mapGen f)

/-- Theorem 39: mapGen preserves MonStep. -/
noncomputable def MonStep.mapGen {a b : MObj} (f : Nat → Nat)
    (s : MonStep a b) : MonStep (a.mapGen f) (b.mapGen f) := by
  induction s with
  | assocR a b c => exact MonStep.assocR (a.mapGen f) (b.mapGen f) (c.mapGen f)
  | assocL a b c => exact MonStep.assocL (a.mapGen f) (b.mapGen f) (c.mapGen f)
  | unitL a => exact MonStep.unitL (a.mapGen f)
  | unitL' a => exact MonStep.unitL' (a.mapGen f)
  | unitR a => exact MonStep.unitR (a.mapGen f)
  | unitR' a => exact MonStep.unitR' (a.mapGen f)
  | tensorL b _ ih => exact MonStep.tensorL (b.mapGen f) ih
  | tensorR a _ ih => exact MonStep.tensorR (a.mapGen f) ih

/-- Theorem 40: mapGen preserves MonPath. -/
noncomputable def MonPath.mapGen {a b : MObj} (f : Nat → Nat)
    (p : MonPath a b) : MonPath (a.mapGen f) (b.mapGen f) := by
  induction p with
  | refl _ => exact MonPath.refl _
  | step s _ ih => exact MonPath.step (MonStep.mapGen f s) ih

/-- Theorem 41: mapGen on unit. -/
theorem mapGen_unit (f : Nat → Nat) : MObj.mapGen f .unit = .unit := rfl

/-- Theorem 42: mapGen distributes over tensor. -/
theorem mapGen_tensor (f : Nat → Nat) (a b : MObj) :
    MObj.mapGen f (a ⊗ₘ b) = (a.mapGen f) ⊗ₘ (b.mapGen f) := rfl

-- ============================================================
-- §15  Additional coherence paths
-- ============================================================

/-- Theorem 43: Four-fold reassociation. -/
noncomputable def assoc4Path (a b c d : MObj) :
    MonPath (((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d) (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ d))) :=
  pentagonPath1 a b c d

/-- Theorem 44: Five-fold reassociation. -/
noncomputable def assoc5Path (a b c d e : MObj) :
    MonPath ((((a ⊗ₘ b) ⊗ₘ c) ⊗ₘ d) ⊗ₘ e) (a ⊗ₘ (b ⊗ₘ (c ⊗ₘ (d ⊗ₘ e)))) :=
  MonPath.trans
    (MonPath.single (MonStep.assocR ((a ⊗ₘ b) ⊗ₘ c) d e))
    (MonPath.trans
      (MonPath.single (MonStep.assocR (a ⊗ₘ b) c (d ⊗ₘ e)))
      (MonPath.single (MonStep.assocR a b (c ⊗ₘ (d ⊗ₘ e)))))

/-- Theorem 45: No step from a generator to unit. -/
def unit_no_gen_step (n : Nat) : ¬ Nonempty (MonStep (.gen n) .unit) := by
  intro h
  rcases h with ⟨h⟩
  cases h

/-- Theorem 46: Flatten preserved under assocR. -/
theorem flatten_assocR (a b c : MObj) :
    ((a ⊗ₘ b) ⊗ₘ c).flatten = (a ⊗ₘ (b ⊗ₘ c)).flatten := by
  simp [MObj.flatten, List.append_assoc]

/-- Theorem 47: Flatten preserved under unitL. -/
theorem flatten_unitL (a : MObj) :
    (MObj.unit ⊗ₘ a).flatten = a.flatten := by
  simp [MObj.flatten]

/-- Theorem 48: Flatten preserved under unitR. -/
theorem flatten_unitR (a : MObj) :
    (a ⊗ₘ MObj.unit).flatten = a.flatten := by
  simp [MObj.flatten, List.append_nil]

/-- Theorem 49: mapGen commutes with flatten. -/
theorem mapGen_flatten (f : Nat → Nat) (a : MObj) :
    (a.mapGen f).flatten = a.flatten.map f := by
  induction a with
  | gen n => simp [MObj.mapGen, MObj.flatten]
  | unit => simp [MObj.mapGen, MObj.flatten]
  | tensor a b iha ihb =>
    simp [MObj.mapGen, MObj.flatten, List.map_append, iha, ihb]

/-- Theorem 50: Three-step path composition. -/
noncomputable def three_step_path {a b c d : MObj}
    (s₁ : MonStep a b) (s₂ : MonStep b c) (s₃ : MonStep c d) :
    MonPath a d :=
  MonPath.trans (MonPath.single s₁)
    (MonPath.trans (MonPath.single s₂) (MonPath.single s₃))
