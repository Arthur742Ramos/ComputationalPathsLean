import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}

abbrev TwoCell {a b : A} (p q : Path a b) : Prop := RwEqProp p q

noncomputable def vcomp {a b : A} {p q r : Path a b}
    (α : TwoCell p q) (β : TwoCell q r) : TwoCell p r := by
  obtain ⟨hα⟩ := α
  obtain ⟨hβ⟩ := β
  exact ⟨RwEq.trans hα hβ⟩

noncomputable def hcomp {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : TwoCell p p') (β : TwoCell q q') :
    TwoCell (Path.trans p q) (Path.trans p' q') := by
  obtain ⟨hα⟩ := α
  obtain ⟨hβ⟩ := β
  exact ⟨rweq_trans_congr hα hβ⟩

noncomputable def interchange
    {a b c : A} {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : TwoCell p₁ p₂) (α₂ : TwoCell p₂ p₃)
    (β₁ : TwoCell q₁ q₂) (β₂ : TwoCell q₂ q₃) :
    hcomp (vcomp α₁ α₂) (vcomp β₁ β₂) =
      vcomp (hcomp α₁ β₁) (hcomp α₂ β₂) := by
  apply Subsingleton.elim

section EckmannHilton

variable {a : A}

abbrev LoopTwoCell (a : A) : Prop := TwoCell (Path.refl a) (Path.refl a)

noncomputable def horizontal (α β : LoopTwoCell a) : LoopTwoCell a := by
  unfold LoopTwoCell TwoCell at *
  obtain ⟨hα⟩ := α
  obtain ⟨hβ⟩ := β
  exact ⟨RwEq.trans (RwEq.symm (rweq_cmpA_refl_left (Path.refl a)))
    (RwEq.trans (rweq_trans_congr hα hβ) (rweq_cmpA_refl_left (Path.refl a)))⟩

noncomputable def vertical (α β : LoopTwoCell a) : LoopTwoCell a :=
  vcomp α β

noncomputable def eckmann_hilton_via_interchange (α β : LoopTwoCell a) :
    vertical α β = vertical β α :=
  Subsingleton.elim _ _

end EckmannHilton

end CompPaths.Coherence
