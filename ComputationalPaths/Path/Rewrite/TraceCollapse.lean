import ComputationalPaths.Path.Rewrite.RwEq

/-!
# The primitive trace-collapse derivation

Dependency-light extraction of the existing construction from
`TypeTheory.QuotientPathInduction`. The public namespace and declarations
are preserved. No quotient or additional rewrite rule is introduced.
-/

namespace ComputationalPaths.Path.QuotientPathInduction

universe u

/-- An ambient equality recorded with no rewrite steps. -/
noncomputable def emptyTrace {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [] h

@[simp] theorem emptyTrace_steps {A : Type u} {a b : A} (h : a = b) :
    (emptyTrace h).steps = [] := rfl

theorem emptyTrace_eq {A : Type u} {a b : A} (h h' : a = b) :
    emptyTrace h = emptyTrace h' := rfl

@[simp] theorem emptyTrace_refl {A : Type u} (a : A) :
    emptyTrace (rfl : a = a) = Path.refl a := rfl

@[simp] theorem lamCongr_steps {A : Type u} {α : Type u} {f g : α → A}
    (p : ∀ x : α, Path (f x) (g x)) :
    (Path.lamCongr (f := f) (g := g) p).steps = [] := rfl

/-- The existing application-beta rule relates the empty trace to any
path, because lambda congruence records an empty trace. -/
noncomputable def stepEmptyTrace {A : Type u} {a b : A} (p : Path a b) :
    Step (emptyTrace p.proof) p :=
  Step.fun_app_beta (A := A) (α := PUnit.{u + 1})
    (f := fun _ => a) (g := fun _ => b) (fun _ => p) PUnit.unit

noncomputable def rweqEmptyTrace {A : Type u} {a b : A} (p : Path a b) :
    RwEq (emptyTrace p.proof) p := rweq_of_step (stepEmptyTrace p)

/-- The same explicit two-stage derivation used by quotient path induction.
The intermediate path is trace-free; the endpoints retain their raw traces. -/
noncomputable def rweqAny {A : Type u} {a b : A} (p q : Path a b) : RwEq p q :=
  rweq_trans (rweq_symm (rweqEmptyTrace p)) (rweqEmptyTrace q)

theorem rweq_total {A : Type u} {a b : A} (p q : Path a b) :
    Nonempty (RwEq p q) := ⟨rweqAny p q⟩

end ComputationalPaths.Path.QuotientPathInduction
