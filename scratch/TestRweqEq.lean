import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths.Path.OmegaGroupoid

universe u
variable {A : Type u} {a b : A} {p q : Path a b}
variable (d₁ d₂ : Derivation₂ p q)

#check MetaStep₃.rweq_eq (A:=A) (a:=a) (b:=b) (p:=p) (q:=q) (d₁:=d₁) (d₂:=d₂)
-- The next line should fail if rweq_eq has no explicit arguments:
#check MetaStep₃.rweq_eq (A:=A) (a:=a) (b:=b) (p:=p) (q:=q) (d₁:=d₁) (d₂:=d₂) rfl

end ComputationalPaths.Path.OmegaGroupoid
