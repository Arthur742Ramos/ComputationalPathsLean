import Solution

/-! Adversarial checks of the exact c5b35d85 submission definitions.
These are evidence of missing constraints, not replacement research claims. -/
namespace ComputationalPaths.PalomarWeakOmegaGroupoid.SemanticAudit

universe u

/-- The advertised boundary permits an arbitrary unrelated cell family. -/
noncomputable def arbitraryCells (A : Type u) (C : Nat → Type u) :
    WeakOmegaGroupoidBoundary A :=
  { compPathOmegaGroupoidBoundary A with cells := C }

/-- Even an inhabited carrier can have no cells in any recorded dimension. -/
theorem emptyCellsAllowed :
    ∃ b : WeakOmegaGroupoidBoundary Unit, ∀ n, IsEmpty (b.cells n) := by
  refine ⟨arbitraryCells Unit (fun _ => Empty), ?_⟩
  intro n
  exact inferInstanceAs (IsEmpty Empty)

/-- A trace entry need not be an equality or match the path endpoints. -/
def disconnectedTrace : Path Nat 0 0 := ⟨[(1, 2)], rfl⟩

theorem disconnectedTraceEntry : disconnectedTrace.trace = [(1, 2)] := rfl

/-- Proof irrelevance identifies truncations, not their witnesses. -/
theorem truncationEqualityDoesNotReflect :
    (⟨true⟩ : Nonempty Bool) = ⟨false⟩ ∧ true ≠ false := by
  exact ⟨Subsingleton.elim _ _, Bool.noConfusion⟩

/-- The higher filler exists for unrelated distinct elements of any carrier. -/
def booleanFiller (n : Nat) : DerivationHigh n true false :=
  contractibilityHigher n true false

/-- Dimension six still takes dimension-four endpoints, not five-cells. -/
example : CellType Unit 6 =
    (Σ (a b : Unit) (p q : Path Unit a b) (d e : Derivation2 p q)
      (m n : Derivation3 d e) (c₁ c₂ : Derivation4 m n),
        DerivationHigh 1 c₁ c₂) := rfl

/-- A generator connects any pair without inspecting rewrite content. -/
def automaticPrimitive {A : Type u} {a b : A} {p q : Path A a b}
    (d e : Derivation2 p q) : MetaStep3 d e :=
  .rweq_transport (Subsingleton.elim _ _)

#print axioms emptyCellsAllowed
#print axioms truncationEqualityDoesNotReflect
#print axioms booleanFiller
#print axioms automaticPrimitive

/-- The manuscript's unrestricted rewrite-to-identity comparison cannot hold
for these retained Path records: a rewrite can change their observable trace. -/
theorem rewriteDoesNotReflectIdentity :
    ∃ p q : Path Unit () (), RwProp p q ∧ p ≠ q := by
  let p : Path Unit () () := Path.ofEq rfl
  refine ⟨Path.trans p (Path.symm p), Path.refl (),
    ⟨.step (.trans_symm p)⟩, ?_⟩
  intro h
  have count := congrArg (fun x => x.trace.length) h
  change 2 = 0 at count
  cases count

theorem noUnrestrictedRewriteToIdentity :
    ¬ (∀ p q : Path Unit () (), RwProp p q → p = q) := by
  intro reflect
  obtain ⟨p, q, h, ne⟩ := rewriteDoesNotReflectIdentity
  exact ne (reflect p q h)

#print axioms rewriteDoesNotReflectIdentity
#print axioms noUnrestrictedRewriteToIdentity

end ComputationalPaths.PalomarWeakOmegaGroupoid.SemanticAudit
