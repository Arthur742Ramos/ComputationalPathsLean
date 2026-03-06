/-
# Eckmann-Hilton and Interchange — Proof-Relevant Wrappers

This module exposes proof-relevant 3-cells for `RwEq`-level interchange and
Eckmann-Hilton by reifying `RwEq` witnesses into the core
`Derivation₂`/`Derivation₃` tower.
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths.EckmannHilton

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaGroupoid

universe u

noncomputable section

@[simp] noncomputable def vcomp {A : Type u} {a b : A} {p q r : Path a b}
    (α : RwEq p q) (β : RwEq q r) : RwEq p r :=
  RwEq.trans α β

section HComp

variable {A : Type u} {a b c : A}

@[simp] noncomputable def lwhisker
    (p : Path a b) {q q' : Path b c} (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p q') :=
  (OmegaGroupoid.whiskerLeft p (OmegaGroupoid.derivation₂_of_rweq β)).toRwEq

@[simp] noncomputable def rwhisker
    {p p' : Path a b} (α : RwEq p p') (q : Path b c) :
    RwEq (Path.trans p q) (Path.trans p' q) :=
  (OmegaGroupoid.whiskerRight (OmegaGroupoid.derivation₂_of_rweq α) q).toRwEq

@[simp] noncomputable def hcomp
    {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  (OmegaGroupoid.hcomp (OmegaGroupoid.derivation₂_of_rweq α)
    (OmegaGroupoid.derivation₂_of_rweq β)).toRwEq

@[simp] noncomputable def hcomp'
    {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  (Derivation₂.vcomp
    (OmegaGroupoid.whiskerLeft p (OmegaGroupoid.derivation₂_of_rweq β))
    (OmegaGroupoid.whiskerRight (OmegaGroupoid.derivation₂_of_rweq α) q')).toRwEq

end HComp

@[simp] private theorem derivation₂_of_lwhisker
    {A : Type u} {a b c : A} (p : Path a b) {q q' : Path b c} (β : RwEq q q') :
    OmegaGroupoid.derivation₂_of_rweq (lwhisker p β) =
      OmegaGroupoid.whiskerLeft p (OmegaGroupoid.derivation₂_of_rweq β) := by
  simp [lwhisker, OmegaGroupoid.derivation₂_of_rweq]

@[simp] private theorem derivation₂_of_rwhisker
    {A : Type u} {a b c : A} {p p' : Path a b} (α : RwEq p p') (q : Path b c) :
    OmegaGroupoid.derivation₂_of_rweq (rwhisker α q) =
      OmegaGroupoid.whiskerRight (OmegaGroupoid.derivation₂_of_rweq α) q := by
  simp [rwhisker, OmegaGroupoid.derivation₂_of_rweq]

@[simp] private theorem derivation₂_of_hcomp
    {A : Type u} {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    OmegaGroupoid.derivation₂_of_rweq (hcomp α β) =
      OmegaGroupoid.hcomp (OmegaGroupoid.derivation₂_of_rweq α)
        (OmegaGroupoid.derivation₂_of_rweq β) := by
  simp [hcomp, OmegaGroupoid.derivation₂_of_rweq]

@[simp] private theorem derivation₂_of_hcomp'
    {A : Type u} {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : RwEq p p') (β : RwEq q q') :
    OmegaGroupoid.derivation₂_of_rweq (hcomp' α β) =
      Derivation₂.vcomp
        (OmegaGroupoid.whiskerLeft p (OmegaGroupoid.derivation₂_of_rweq β))
        (OmegaGroupoid.whiskerRight (OmegaGroupoid.derivation₂_of_rweq α) q') := by
  simp [hcomp', OmegaGroupoid.derivation₂_of_rweq]

@[simp] private theorem derivation₂_of_toRwEq_trans
    {A : Type u} {a b : A} {p q r : Path a b}
    (d₁ : Derivation₂ p q) (d₂ : Derivation₂ q r) :
    OmegaGroupoid.derivation₂_of_rweq (RwEq.trans d₁.toRwEq d₂.toRwEq) =
      Derivation₂.vcomp d₁ d₂ := by
  simp [OmegaGroupoid.derivation₂_of_rweq, OmegaGroupoid.Derivation₂.ofRwEq]

section Interchange

variable {A : Type u} {a b c : A}

private noncomputable def interchange_unfolded
    {p p' p'' : Path a b} {q q' q'' : Path b c}
    (α : Derivation₂ p p') (β : Derivation₂ p' p'')
    (γ : Derivation₂ q q') (δ : Derivation₂ q' q'') :
    Derivation₃
      (Derivation₂.vcomp
        (Derivation₂.vcomp (OmegaGroupoid.whiskerRight α q) (OmegaGroupoid.whiskerRight β q))
        (Derivation₂.vcomp (OmegaGroupoid.whiskerLeft p'' γ) (OmegaGroupoid.whiskerLeft p'' δ)))
      (Derivation₂.vcomp
        (Derivation₂.vcomp (OmegaGroupoid.whiskerRight α q) (OmegaGroupoid.whiskerLeft p' γ))
        (Derivation₂.vcomp (OmegaGroupoid.whiskerRight β q') (OmegaGroupoid.whiskerLeft p'' δ))) := by
  let wr₁ := OmegaGroupoid.whiskerRight α q
  let wr₂ := OmegaGroupoid.whiskerRight β q
  let wl₁ := OmegaGroupoid.whiskerLeft p'' γ
  let wl₂ := OmegaGroupoid.whiskerLeft p'' δ
  let mid₁ := OmegaGroupoid.whiskerLeft p' γ
  let mid₂ := OmegaGroupoid.whiskerRight β q'
  exact Derivation₃.vcomp
    (Derivation₃.step (MetaStep₃.vcomp_assoc wr₁ wr₂ (.vcomp wl₁ wl₂)))
    (Derivation₃.vcomp
      (Derivation₃.whiskerLeft₃ wr₁
        (Derivation₃.inv (Derivation₃.step (MetaStep₃.vcomp_assoc wr₂ wl₁ wl₂))))
      (Derivation₃.vcomp
        (Derivation₃.whiskerLeft₃ wr₁
          (Derivation₃.whiskerRight₃ (Derivation₃.step (MetaStep₃.interchange β γ)) wl₂))
        (Derivation₃.vcomp
          (Derivation₃.whiskerLeft₃ wr₁
            (Derivation₃.step (MetaStep₃.vcomp_assoc mid₁ mid₂ wl₂)))
          (Derivation₃.inv
            (Derivation₃.step (MetaStep₃.vcomp_assoc wr₁ mid₁ (.vcomp mid₂ wl₂)))))))

/-- Proof-relevant bicategorical interchange for `RwEq` witnesses. -/
noncomputable def interchange
    {p p' p'' : Path a b} {q q' q'' : Path b c}
    (α : RwEq p p') (β : RwEq p' p'') (γ : RwEq q q') (δ : RwEq q' q'') :
    OmegaGroupoid.RwEq₃ (hcomp (vcomp α β) (vcomp γ δ))
      (vcomp (hcomp α γ) (hcomp β δ)) := by
  simpa [OmegaGroupoid.RwEq₃, OmegaGroupoid.derivation₂_of_rweq,
      OmegaGroupoid.Derivation₂.ofRwEq, hcomp, vcomp, lwhisker, rwhisker,
      OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]
    using interchange_unfolded (OmegaGroupoid.derivation₂_of_rweq α)
      (OmegaGroupoid.derivation₂_of_rweq β)
      (OmegaGroupoid.derivation₂_of_rweq γ)
      (OmegaGroupoid.derivation₂_of_rweq δ)

end Interchange

section EckmannHilton

variable {A : Type u} {a : A}

abbrev TwoLoop (A : Type u) (a : A) := RwEq (Path.refl a) (Path.refl a)

@[simp] noncomputable def hcomp_loops (α β : TwoLoop A a) : TwoLoop A a :=
  hcomp α β

/-- On `Ω²`, horizontal and vertical composition are connected by a genuine 3-cell. -/
noncomputable def hcomp_eq_vcomp (α β : TwoLoop A a) :
    OmegaGroupoid.RwEq₃ (hcomp_loops α β) (vcomp α β) := by
  change Derivation₃
    (OmegaGroupoid.derivation₂_of_rweq (hcomp_loops α β))
    (OmegaGroupoid.derivation₂_of_rweq (vcomp α β))
  exact OmegaGroupoid.connect_normalized
    (OmegaGroupoid.derivation₂_of_rweq (hcomp_loops α β))
    (OmegaGroupoid.derivation₂_of_rweq (vcomp α β))

private noncomputable def hcomp'_eq_vcomp (α β : TwoLoop A a) :
    OmegaGroupoid.RwEq₃ (hcomp' α β) (vcomp β α) := by
  change Derivation₃
    (OmegaGroupoid.derivation₂_of_rweq (hcomp' α β))
    (OmegaGroupoid.derivation₂_of_rweq (vcomp β α))
  exact OmegaGroupoid.connect_normalized
    (OmegaGroupoid.derivation₂_of_rweq (hcomp' α β))
    (OmegaGroupoid.derivation₂_of_rweq (vcomp β α))

private noncomputable def hcomp_eq_hcomp' (α β : TwoLoop A a) :
    OmegaGroupoid.RwEq₃ (hcomp α β) (hcomp' α β) := by
  change Derivation₃
    (OmegaGroupoid.derivation₂_of_rweq (hcomp α β))
    (OmegaGroupoid.derivation₂_of_rweq (hcomp' α β))
  simpa [derivation₂_of_hcomp, derivation₂_of_hcomp', OmegaGroupoid.hcomp]
    using (Derivation₃.step (MetaStep₃.interchange
      (OmegaGroupoid.derivation₂_of_rweq α)
      (OmegaGroupoid.derivation₂_of_rweq β)))

/-- Proof-relevant Eckmann-Hilton commutativity for 2-loops. -/
noncomputable def eckmann_hilton (α β : TwoLoop A a) :
    OmegaGroupoid.RwEq₃ (vcomp α β) (vcomp β α) := by
  simpa [OmegaGroupoid.RwEq₃, OmegaGroupoid.derivation₂_of_rweq,
      OmegaGroupoid.Derivation₂.ofRwEq, hcomp, hcomp', vcomp, lwhisker, rwhisker,
      OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]
    using
      (Derivation₃.vcomp
        (Derivation₃.vcomp
          (Derivation₃.inv (hcomp_eq_vcomp α β))
          (hcomp_eq_hcomp' α β))
        (hcomp'_eq_vcomp α β))

/-- Horizontal composition on `Ω²` is commutative through the same 3-cell calculus. -/
noncomputable def eckmann_hilton_hcomp (α β : TwoLoop A a) :
    OmegaGroupoid.RwEq₃ (hcomp_loops α β) (hcomp_loops β α) := by
  simpa [OmegaGroupoid.RwEq₃, OmegaGroupoid.derivation₂_of_rweq,
      OmegaGroupoid.Derivation₂.ofRwEq, hcomp_loops, hcomp, hcomp', vcomp,
      lwhisker, rwhisker, OmegaGroupoid.whiskerLeft, OmegaGroupoid.whiskerRight]
    using
      (Derivation₃.vcomp
        (hcomp_eq_vcomp α β)
        (Derivation₃.vcomp
          (eckmann_hilton α β)
          (Derivation₃.inv (hcomp_eq_vcomp β α))))

end EckmannHilton

end

end ComputationalPaths.EckmannHilton
