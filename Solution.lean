/-
# Solution: an extensional, 3-truncated weak omega-groupoid

The proof below is intentionally focused.  It uses the actual trace-carrying
computational-path record from the library, a Type-valued rewrite-derivation
presentation for 2-cells, and explicit coherence constructors at dimensions
3 and above.

The crucial boundary is visible in `contractibility₃`: the induced equality
proofs are elements of `Prop`, so proof irrelevance supplies the transport
argument.  Dimensions 4 and above use the declared parallel-cell fillers.  The
result is therefore an extensional 3-truncated weak omega-groupoid certificate,
not a claim of a constructive Squier finite-derivation-type proof or an
intensional HoTT identity type.
-/

import ComputationalPaths.Path.OmegaGroupoid.PalomarStatement

namespace ComputationalPaths
namespace Path
namespace PalomarOmegaGroupoid

universe u

/-! ## The rewrite presentation -/

theorem ofRwEq_toRwEq {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) :
    Derivation₂.toRwEq (Derivation₂.ofRwEq h) = h := by
  induction h with
  | refl p => rfl
  | step s => rfl
  | symm h ih =>
      simp [Derivation₂.ofRwEq, Derivation₂.toRwEq, ih]
  | trans h₁ h₂ ih₁ ih₂ =>
      simp [Derivation₂.ofRwEq, Derivation₂.toRwEq, ih₁, ih₂]

theorem ofRwEq_toRwEq_roundtrip {A : Type u} {a b : A} {p q : Path a b}
    (d : Derivation₂ p q) :
    Derivation₂.ofRwEq (Derivation₂.toRwEq d) = d := by
  induction d with
  | refl p => rfl
  | step s => rfl
  | inv d ih =>
      simp [Derivation₂.toRwEq, Derivation₂.ofRwEq, ih]
  | vcomp d₁ d₂ ih₁ ih₂ =>
      simp [Derivation₂.toRwEq, Derivation₂.ofRwEq, ih₁, ih₂]

/-! ## The proof-irrelevance contraction and higher fillers -/

noncomputable def contractibility₃ {A : Type u} {a b : A}
    {p q : Path a b} (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  .step (.rweq_transport (Subsingleton.elim _ _))

def contractibility₄ {A : Type u} {a b : A} {p q : Path a b}
    {d₁ d₂ : Derivation₂ p q}
    (m₁ m₂ : Derivation₃ d₁ d₂) : Derivation₄ m₁ m₂ :=
  .step (.diamond_filler m₁ m₂)

def contractibilityHigh {A : Type u} {a b : A} {p q : Path a b}
    {d₁ d₂ : Derivation₂ p q} {m₁ m₂ : Derivation₃ d₁ d₂}
    (n : Nat) (c₁ c₂ : Derivation₄ m₁ m₂) : DerivationHigh n c₁ c₂ :=
  .step (.diamond_filler c₁ c₂)

noncomputable def coherenceCertificate (A : Type u) : CoherenceCertificate A where
  unit_left := fun d => .step (.vcomp_refl_left d)
  unit_right := fun d => .step (.vcomp_refl_right d)
  associativity := fun d₁ d₂ d₃ => .step (.vcomp_assoc d₁ d₂ d₃)
  inverse_inverse := fun d => .step (.inv_inv d)
  inverse_left := fun d => .step (.vcomp_inv_left d)
  inverse_right := fun d => .step (.vcomp_inv_right d)
  inverse_composition := fun d₁ d₂ => .step (.inv_vcomp d₁ d₂)
  interchange := fun α β => .step (.interchange α β)
  pentagon := fun f g h k => .step (.pentagon f g h k)
  triangle := fun f g => .step (.triangle f g)

noncomputable def omegaStructure (A : Type u) : WeakOmegaGroupoid A where
  cells := CellType A
  contract₃ := contractibility₃
  contract₄ := contractibility₄
  contractHigh := contractibilityHigh
  pentagon := fun f g h k => .step (.pentagon f g h k)
  triangle := fun f g => .step (.triangle f g)

/-! ## The selected theorem -/

theorem main_result (A : Type u) : Nonempty (OmegaGroupoidCertificate A) := by
  let omega := omegaStructure A
  exact ⟨
    { omega := omega
      cells_are_explicit := by rfl
      two_cell_sound := fun d => Derivation₂.toRwEq d
      two_cell_complete := fun h => Derivation₂.ofRwEq h
      two_cell_iff := by
        intro a b p q
        constructor
        · rintro ⟨d⟩
          exact ⟨Derivation₂.toRwEq d⟩
        · rintro ⟨h⟩
          exact ⟨Derivation₂.ofRwEq h⟩
      two_cell_to_rw_eq_roundtrip := by
        intro a b p q h
        exact ofRwEq_toRwEq h
      two_cell_reification_roundtrip := by
        intro a b p q d
        exact ofRwEq_toRwEq_roundtrip d
      three_cell_sound := by
        intro a b p q d₁ d₂ m
        exact Subsingleton.elim _ _
      contractibility₃ := contractibility₃
      contractibility₄ := contractibility₄
      contractibility_high := contractibilityHigh
      coherence := coherenceCertificate A
      trace_metadata_nontrivial := by
        intro a h
        have hs := _root_.congrArg (fun r : Path a a => r.steps) h
        simpa [Path.ofEq, Path.refl] using hs
      two_cell_syntax_nontrivial := by
        intro a p h
        cases h }⟩

end PalomarOmegaGroupoid
end Path
end ComputationalPaths
