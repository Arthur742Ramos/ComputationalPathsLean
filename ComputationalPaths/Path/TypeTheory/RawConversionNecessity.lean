/-
# The raw judgment genuinely lacks conversion

`RawReduction` proves contextual subject reduction *conditionally*, taking the
two omitted structural rules as a hypothesis record `ConversionRules`.  A
conditional theorem is only informative if its hypothesis is not vacuous and if
the conclusion really fails without it.  This module settles both points for the
raw judgment, replacing "the structural induction gets stuck" by theorems.

## What is proved

* `convert_not_admissible` — the raw judgment does not admit the conversion
  rule: `.zero` is typed by `.nat` and by nothing definitionally equal to it.
* `convertCtx_not_admissible` — the raw judgment does not admit context
  conversion, exhibited under a binder where only the context slot changes.
* `conversionRules_uninhabited` — consequently `ConversionRules` has no
  inhabitant, so `RawReduction.contextual_subject_reduction` is *vacuously*
  true.  Its content is the analysis of the induction, not a hypothesis a
  reader could hope to discharge for `HasType`.
* `raw_contextual_subject_reduction_fails` — an explicit counterexample:
  a reduction `t ⟶ u` and a derivation `Γ ⊢ t : A` with `Γ ⊢ u : A`
  underivable.  Contextual subject reduction is therefore false, not merely
  unproved.
* `HasTypeC`, the conversion-closed extension, together with
  `hasTypeC_convert` and `hasTypeC_convertCtx`: the two rules hold there by
  construction, and `HasTypeC.ofRaw` embeds the raw judgment.

## What is deliberately *not* proved

Unconditional contextual subject reduction for `HasTypeC`.  Inverting a
conversion-closed judgment requires generation lemmas, and generation lemmas for
an untyped definitional equality require confluence, which this development does
not establish.  Stating that gap precisely is the point of this module: the
distance from the raw calculus to subject reduction is not "two hypotheses" but
"a different judgment, whose metatheory needs confluence".
-/

import ComputationalPaths.Path.TypeTheory.RawReduction

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

/-! ## Conversion is not admissible for the raw judgment -/

/-- `.nat 0` and `.el (.codeNat 0)` are definitionally equal by the primitive
`el`-computation rule, in either orientation. -/
theorem defEq_nat_el_codeNat {n : Nat} :
    DefEq (.el (.codeNat 0) : Expr n) (.nat 0) :=
  DefEq.beta (Computation.elNatBeta 0)

/-- Raw typing reads a variable's type off the context slot verbatim: there is
no rule that could give it any other type.  Every counterexample below is an
instance of this rigidity. -/
theorem hasType_var_inversion {n : Nat} {Gamma : Ctx n} {i : Fin n}
    {T : Expr n} (h : HasType Gamma (.var i) T) : T = Gamma i := by
  cases h
  rfl

/-- Raw typing assigns `.zero` exactly one type.  This is inversion on a
syntax-directed rule, and it is what makes the counterexamples below decidable
by inspection. -/
theorem hasType_zero_inversion {n : Nat} {Gamma : Ctx n} {natLevel : Nat}
    {T : Expr n} (h : HasType Gamma (.zero natLevel) T) :
    T = .nat natLevel := by
  cases h
  rfl

/-- **Conversion is not admissible.**  The raw judgment types `.zero 0` at
`.nat 0`, and `.nat 0` is definitionally equal to `.el (.codeNat 0)`, yet no raw
derivation gives `.zero 0` the latter type. -/
theorem convert_not_admissible {n : Nat} (Gamma : Ctx n) :
    HasType Gamma (.zero 0 : Expr n) (.el (.codeNat 0)) → False := by
  intro h
  have hT : (Expr.el (Expr.codeNat 0) : Expr n) = .nat 0 :=
    hasType_zero_inversion h
  exact Expr.noConfusion hT

/-! ## Context conversion is not admissible either

The witness has to change only the *context*, so it lives under a binder.  Take
the family `.id A (var 0) (var 0)` over a domain `A`: it is a type in the context
extended by `A` and in no other, because the raw variable rule reads its type off
the context slot verbatim. -/

/-- The domain used below reduces, and is closed, so weakening leaves it fixed. -/
def failDomain {n : Nat} : Expr n := .el (.codeNat 0)

/-- The dependent family that pins down its context slot. -/
def failFamily {n : Nat} : Expr (n + 1) :=
  .id failDomain (.var 0) (.var 0)

@[simp] theorem failDomain_rename {n m : Nat} (rho : Ren n m) :
    rename rho (failDomain : Expr n) = failDomain := rfl

/-- In a context whose zero slot is `A`, the family is a type only when `A` is
`failDomain`.  Inversion twice: once on `idForm`, once on `var`. -/
theorem failFamily_forces_slot {n : Nat} {Gamma : Ctx n} {A : Expr n}
    {level : Nat}
    (h : HasType (Ctx.extend Gamma A) (failFamily : Expr (n + 1)) (.sort level)) :
    rename (Ren.wk n) A = failDomain := by
  cases h with
  | idForm _ ha _ =>
      have hslot := hasType_var_inversion ha
      simpa [Ctx.extend] using hslot.symm

/-- **Context conversion is not admissible.**  `failDomain` reduces to `.nat 0`,
so the two contexts are pointwise definitionally equal, yet the family is a type
in the first and not in the second. -/
theorem convertCtx_not_admissible {n : Nat} (Gamma : Ctx n) {level : Nat} :
    HasType (Ctx.extend Gamma (.nat 0)) (failFamily : Expr (n + 1))
      (.sort level) → False := by
  intro h
  have hslot := failFamily_forces_slot h
  simp only [rename] at hslot
  exact Expr.noConfusion hslot

/-- The family *is* a type over the unreduced domain, so the failure above is a
genuine loss and not an artifact of an ill-formed example. -/
noncomputable def failFamily_typed {n : Nat} (Gamma : Ctx n) :
    HasType (Ctx.extend Gamma (failDomain : Expr n))
      (failFamily : Expr (n + 1)) (.sort 0) := by
  refine HasType.idForm ?_ ?_ ?_
  · exact HasType.elForm (HasType.codeNatIntro 0)
  · exact HasType.var 0
  · exact HasType.var 0

/-! ## The hypothesis record is uninhabited -/

/-- **`ConversionRules` has no inhabitant.**  Its `convert` field alone is
refuted by `convert_not_admissible`.  Consequently
`RawReduction.contextual_subject_reduction` is vacuously true: it cannot be
instantiated for `HasType`, and its value is the enumeration of the repairs the
induction needs, not a dischargeable hypothesis. -/
theorem conversionRules_uninhabited : ConversionRules → False := by
  intro C
  exact convert_not_admissible (n := 0) (fun i => i.elim0)
    (C.convert (HasType.zeroIntro 0) (DefEq.symm defEq_nat_el_codeNat))

/-! ## Contextual subject reduction is false, with an explicit witness

The witness applies a variable of `Π`-type whose codomain is the bound variable
itself, so the type of the application *is* its argument.  Reducing the argument
therefore changes the type on the nose.  Raw contexts are arbitrary functions,
so no context well-formedness obligation is incurred. -/

/-- The one-slot context used by the counterexample. -/
def failCtx : Ctx 1 := fun _ => .pi (.nat 0) (.var 0)

/-- A `β`-redex of type `.nat 0`. -/
def failRedex : Expr 1 := .app (.lam (.var 0)) (.zero 0)

/-- Its reduct. -/
def failReduct : Expr 1 := .zero 0

noncomputable def failRedex_reduces : Reduction failRedex failReduct :=
  Reduction.head (Computation.piBeta (.var 0) (.zero 0))

noncomputable def failRedex_typed :
    HasType failCtx failRedex (.nat 0) :=
  HasType.appElim
    (A := .nat 0) (B := .nat 0)
    (HasType.lamIntro (level := 0)
      (HasType.natForm 0) (HasType.natForm 0) (HasType.var 0))
    (HasType.zeroIntro 0)

/-- The application whose type is literally its argument. -/
def failSource : Expr 1 := .app (.var 0) failRedex

/-- The same application after the argument has been reduced. -/
def failTarget : Expr 1 := .app (.var 0) failReduct

noncomputable def failSource_reduces : Reduction failSource failTarget :=
  Reduction.appArg failRedex_reduces

/-- Source typing.  The codomain is `var 0`, so `instantiate` returns the
argument unchanged and the displayed type is `failRedex`. -/
noncomputable def failSource_typed :
    HasType failCtx failSource failRedex :=
  HasType.appElim (A := .nat 0) (B := .var 0)
    (HasType.var 0) failRedex_typed

/-- The reduct cannot be given the source type.  Inverting `appElim` and then
the variable rule forces the codomain to be `var 0`, so the only available type
is `failReduct`, and the two differ as raw expressions. -/
theorem failTarget_type_forced {T : Expr 1}
    (h : HasType failCtx failTarget T) : T = failReduct := by
  cases h with
  | @appElim _ _ A B _ _ hf _ =>
      have hpi : (Expr.pi A B) = failCtx 0 := hasType_var_inversion hf
      have hB : B = .var 0 := by
        simp only [failCtx, Expr.pi.injEq] at hpi
        exact hpi.2
      subst hB
      rfl

theorem failTarget_untyped :
    HasType failCtx failTarget failRedex → False := by
  intro h
  exact Expr.noConfusion (failTarget_type_forced h)

/-- **Contextual subject reduction fails for the raw judgment.**  There is a
reduction inside a well-typed term whose reduct is not typable at the same
type. -/
theorem raw_contextual_subject_reduction_fails :
    (∀ {n : Nat} {t u : Expr n}, Reduction t u →
      ∀ {Gamma : Ctx n} {A : Expr n}, HasType Gamma t A → HasType Gamma u A) →
    False := by
  intro sr
  exact failTarget_untyped (sr failSource_reduces failSource_typed)

/-! ## The conversion-closed extension

The positive counterpart.  Closing the judgment under the two rules makes them
hold by construction; what it does not do is make the *inversion* used by the
subject-reduction proof available, which is why no unconditional contextual
subject-reduction theorem is claimed here. -/

/-- Raw typing closed under conversion and context conversion. -/
inductive HasTypeC : {n : Nat} → Ctx n → Expr n → Expr n → Type where
  | ofRaw {n : Nat} {Gamma : Ctx n} {t A : Expr n} :
      HasType Gamma t A → HasTypeC Gamma t A
  | conv {n : Nat} {Gamma : Ctx n} {t A A' : Expr n} :
      HasTypeC Gamma t A → DefEq A A' → HasTypeC Gamma t A'
  | convCtx {n : Nat} {Gamma Delta : Ctx n} {t A : Expr n} :
      (∀ i, DefEq (Gamma i) (Delta i)) → HasTypeC Gamma t A →
      HasTypeC Delta t A

namespace HasTypeC

/-- Conversion is admissible in the extension, by construction. -/
theorem hasTypeC_convert {n : Nat} {Gamma : Ctx n} {t A A' : Expr n}
    (h : HasTypeC Gamma t A) (d : DefEq A A') : Nonempty (HasTypeC Gamma t A') :=
  ⟨HasTypeC.conv h d⟩

/-- Context conversion is admissible in the extension, by construction. -/
theorem hasTypeC_convertCtx {n : Nat} {Gamma Delta : Ctx n} {t A : Expr n}
    (hGamma : ∀ i, DefEq (Gamma i) (Delta i)) (h : HasTypeC Gamma t A) :
    Nonempty (HasTypeC Delta t A) :=
  ⟨HasTypeC.convCtx hGamma h⟩

/-- The extension types the reduct that the raw judgment could not, so it does
repair the counterexample above. -/
noncomputable def failTarget_typedC :
    HasTypeC failCtx failTarget failRedex :=
  HasTypeC.conv (HasTypeC.ofRaw
      (HasType.appElim (A := .nat 0) (B := .var 0)
        (HasType.var 0) (HasType.zeroIntro 0)))
    (DefEq.symm (DefEq.beta (Computation.piBeta (.var 0) (.zero 0))))

/-- Every raw derivation is an extended derivation. -/
theorem ofRaw_sound {n : Nat} {Gamma : Ctx n} {t A : Expr n}
    (h : HasType Gamma t A) : Nonempty (HasTypeC Gamma t A) :=
  ⟨HasTypeC.ofRaw h⟩

end HasTypeC

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths
