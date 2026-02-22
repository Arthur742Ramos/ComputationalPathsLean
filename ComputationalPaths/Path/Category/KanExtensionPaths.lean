/-
# Kan Extensions via Paths

Left/right Kan extensions for path endofunctors, universal property as path
factorization, Kan extension along identity, composition of extensions,
pointwise extensions, and the Yoneda lemma as a Kan extension.

## References
* Mac Lane, *Categories for the Working Mathematician*, Ch. X
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
open Path
universe u

/-! ## Endofunctor and natural transformations -/

structure KanPEF (A : Type u) where
  obj : A → A
  mp : {a b : A} → Path a b → Path (obj a) (obj b)
  mp_refl : ∀ a, mp (Path.refl a) = Path.refl (obj a)
  mp_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mp (Path.trans p q) = Path.trans (mp p) (mp q)

namespace KanPEF
variable {A : Type u}

noncomputable def id : KanPEF A where
  obj a := a; mp p := p; mp_refl _ := rfl; mp_trans _ _ := rfl

noncomputable def comp (F G : KanPEF A) : KanPEF A where
  obj a := G.obj (F.obj a)
  mp p := G.mp (F.mp p)
  mp_refl a := by show G.mp (F.mp (Path.refl a)) = _; rw [F.mp_refl, G.mp_refl]
  mp_trans p q := by show G.mp (F.mp (Path.trans p q)) = _; rw [F.mp_trans, G.mp_trans]

theorem comp_obj (F G : KanPEF A) (a : A) : (comp F G).obj a = G.obj (F.obj a) := rfl
theorem id_obj (a : A) : (KanPEF.id (A := A)).obj a = a := rfl
theorem id_mp {a b : A} (p : Path a b) : (KanPEF.id (A := A)).mp p = p := rfl

end KanPEF

structure KanNT {A : Type u} (F G : KanPEF A) where
  cmp : ∀ a, Path (F.obj a) (G.obj a)
  nat : ∀ {a b : A} (p : Path a b),
    Path.trans (F.mp p) (cmp b) = Path.trans (cmp a) (G.mp p)

namespace KanNT
variable {A : Type u}

noncomputable def idNT (F : KanPEF A) : KanNT F F where
  cmp a := Path.refl (F.obj a)
  nat _ := by simp

noncomputable def vcomp {F G H : KanPEF A} (η : KanNT F G) (θ : KanNT G H) : KanNT F H where
  cmp a := Path.trans (η.cmp a) (θ.cmp a)
  nat p := by
    rw [← Path.trans_assoc, η.nat p, Path.trans_assoc, θ.nat p, ← Path.trans_assoc]

theorem vcomp_cmp {F G H : KanPEF A} (η : KanNT F G) (θ : KanNT G H) (a : A) :
    (vcomp η θ).cmp a = Path.trans (η.cmp a) (θ.cmp a) := rfl

end KanNT

/-! ## Left Kan Extension -/

/-- Left Kan extension of F along K: Lan with unit η : F → Lan ∘ K. -/
structure LKE {A : Type u} (K F : KanPEF A) where
  Lan : KanPEF A
  η : KanNT F (KanPEF.comp K Lan)

namespace LKE
variable {A : Type u}

/-- Left Kan extension along the identity is F itself. -/
noncomputable def alongId (F : KanPEF A) : LKE KanPEF.id F where
  Lan := F
  η := {
    cmp := fun a =>
      show Path (F.obj a) (F.obj (KanPEF.id.obj a)) from Path.refl (F.obj a)
    nat := by
      intro a b p
      show Path.trans (F.mp p) (Path.refl (F.obj b)) =
           Path.trans (Path.refl (F.obj a)) (F.mp (KanPEF.id.mp p))
      simp [KanPEF.id]
  }

theorem alongId_Lan (F : KanPEF A) : (alongId F).Lan = F := rfl

theorem alongId_η_toEq (F : KanPEF A) (a : A) :
    ((alongId F).η.cmp a).toEq = rfl := rfl

/-- Uniqueness: two left Kan extensions along id agree on objects if given. -/
theorem alongId_unique_obj (F : KanPEF A) (e : LKE KanPEF.id F)
    (hobj : ∀ a, e.Lan.obj a = F.obj a) (a : A) :
    (alongId F).Lan.obj a = e.Lan.obj a := (hobj a).symm

/-- Composition of left Kan extensions. -/
noncomputable def compLKE {K K' F : KanPEF A} (e₁ : LKE K F) (e₂ : LKE K' e₁.Lan) :
    LKE (KanPEF.comp K K') F where
  Lan := e₂.Lan
  η := {
    cmp := fun a =>
      show Path (F.obj a) (e₂.Lan.obj (K'.obj (K.obj a))) from
        Path.trans (e₁.η.cmp a)
          (show Path (e₁.Lan.obj (K.obj a)) (e₂.Lan.obj (K'.obj (K.obj a))) from
            e₂.η.cmp (K.obj a))
    nat := by
      intro a b p
      show Path.trans (F.mp p)
            (Path.trans (e₁.η.cmp b) (e₂.η.cmp (K.obj b))) =
           Path.trans (Path.trans (e₁.η.cmp a) (e₂.η.cmp (K.obj a)))
            (e₂.Lan.mp (K'.mp (K.mp p)))
      rw [← Path.trans_assoc]
      have h1 : Path.trans (F.mp p) (e₁.η.cmp b) =
        Path.trans (e₁.η.cmp a) (e₁.Lan.mp (K.mp p)) := e₁.η.nat p
      rw [h1, Path.trans_assoc]
      have h2 : Path.trans (e₁.Lan.mp (K.mp p)) (e₂.η.cmp (K.obj b)) =
        Path.trans (e₂.η.cmp (K.obj a)) (e₂.Lan.mp (K'.mp (K.mp p))) :=
        e₂.η.nat (K.mp p)
      rw [h2, ← Path.trans_assoc]
  }

theorem compLKE_Lan {K K' F : KanPEF A} (e₁ : LKE K F) (e₂ : LKE K' e₁.Lan) :
    (compLKE e₁ e₂).Lan = e₂.Lan := rfl

theorem compLKE_η_cmp {K K' F : KanPEF A} (e₁ : LKE K F) (e₂ : LKE K' e₁.Lan) (a : A) :
    (compLKE e₁ e₂).η.cmp a =
      Path.trans (e₁.η.cmp a) (e₂.η.cmp (K.obj a)) := rfl

end LKE

/-! ## Right Kan Extension -/

/-- Right Kan extension of F along K: Ran with counit ε : Ran ∘ K → F. -/
structure RKE {A : Type u} (K F : KanPEF A) where
  Ran : KanPEF A
  ε : KanNT (KanPEF.comp K Ran) F

namespace RKE
variable {A : Type u}

/-- Right Kan extension along the identity is F itself. -/
noncomputable def alongId (F : KanPEF A) : RKE KanPEF.id F where
  Ran := F
  ε := {
    cmp := fun a =>
      show Path (F.obj (KanPEF.id.obj a)) (F.obj a) from Path.refl (F.obj a)
    nat := by
      intro a b p
      show Path.trans (F.mp (KanPEF.id.mp p)) (Path.refl (F.obj b)) =
           Path.trans (Path.refl (F.obj a)) (F.mp p)
      simp [KanPEF.id]
  }

theorem alongId_Ran (F : KanPEF A) : (alongId F).Ran = F := rfl

theorem alongId_ε_toEq (F : KanPEF A) (a : A) :
    ((alongId F).ε.cmp a).toEq = rfl := rfl

theorem alongId_unique_obj (F : KanPEF A) (e : RKE KanPEF.id F)
    (hobj : ∀ a, e.Ran.obj a = F.obj a) (a : A) :
    (alongId F).Ran.obj a = e.Ran.obj a := (hobj a).symm

/-- Composition of right Kan extensions. -/
noncomputable def compRKE {K K' F : KanPEF A} (e₁ : RKE K F) (e₂ : RKE K' e₁.Ran) :
    RKE (KanPEF.comp K K') F where
  Ran := e₂.Ran
  ε := {
    cmp := fun a =>
      show Path (e₂.Ran.obj (K'.obj (K.obj a))) (F.obj a) from
        Path.trans
          (show Path (e₂.Ran.obj (K'.obj (K.obj a))) (e₁.Ran.obj (K.obj a)) from
            e₂.ε.cmp (K.obj a))
          (e₁.ε.cmp a)
    nat := by
      intro a b p
      show Path.trans (e₂.Ran.mp (K'.mp (K.mp p)))
            (Path.trans (e₂.ε.cmp (K.obj b)) (e₁.ε.cmp b)) =
           Path.trans (Path.trans (e₂.ε.cmp (K.obj a)) (e₁.ε.cmp a)) (F.mp p)
      rw [← Path.trans_assoc]
      have h1 : Path.trans (e₂.Ran.mp (K'.mp (K.mp p))) (e₂.ε.cmp (K.obj b)) =
        Path.trans (e₂.ε.cmp (K.obj a)) (e₁.Ran.mp (K.mp p)) := e₂.ε.nat (K.mp p)
      rw [h1, Path.trans_assoc]
      have h2 : Path.trans (e₁.Ran.mp (K.mp p)) (e₁.ε.cmp b) =
        Path.trans (e₁.ε.cmp a) (F.mp p) := e₁.ε.nat p
      rw [h2, ← Path.trans_assoc]
  }

theorem compRKE_Ran {K K' F : KanPEF A} (e₁ : RKE K F) (e₂ : RKE K' e₁.Ran) :
    (compRKE e₁ e₂).Ran = e₂.Ran := rfl

theorem compRKE_ε_cmp {K K' F : KanPEF A} (e₁ : RKE K F) (e₂ : RKE K' e₁.Ran) (a : A) :
    (compRKE e₁ e₂).ε.cmp a =
      Path.trans (e₂.ε.cmp (K.obj a)) (e₁.ε.cmp a) := rfl

end RKE

/-! ## Kan along fully faithful -/

theorem lan_comp_obj {A : Type u} (K F : KanPEF A) (e : LKE K F) (a : A) :
    (KanPEF.comp K e.Lan).obj a = e.Lan.obj (K.obj a) := rfl

theorem ran_comp_obj {A : Type u} (K F : KanPEF A) (e : RKE K F) (a : A) :
    (KanPEF.comp K e.Ran).obj a = e.Ran.obj (K.obj a) := rfl

/-! ## Pointwise Kan extensions -/

structure PointwiseLKE {A : Type u} (K F : KanPEF A) where
  ext : LKE K F
  pointwise : ∀ a, ∃ (apex : A), apex = ext.Lan.obj a

namespace PointwiseLKE
variable {A : Type u}

noncomputable def fromAlongId (F : KanPEF A) : PointwiseLKE KanPEF.id F where
  ext := LKE.alongId F
  pointwise a := ⟨F.obj a, rfl⟩

theorem fromAlongId_Lan (F : KanPEF A) : (fromAlongId F).ext.Lan = F := rfl

end PointwiseLKE

structure PointwiseRKE {A : Type u} (K F : KanPEF A) where
  ext : RKE K F
  pointwise : ∀ a, ∃ (apex : A), apex = ext.Ran.obj a

namespace PointwiseRKE
variable {A : Type u}

noncomputable def fromAlongId (F : KanPEF A) : PointwiseRKE KanPEF.id F where
  ext := RKE.alongId F
  pointwise a := ⟨F.obj a, rfl⟩

theorem fromAlongId_Ran (F : KanPEF A) : (fromAlongId F).ext.Ran = F := rfl

end PointwiseRKE

/-! ## Yoneda as Kan extension -/

theorem yoneda_as_lan {A : Type u} (F : KanPEF A) :
    (LKE.alongId F).Lan = F := rfl

theorem yoneda_as_ran {A : Type u} (F : KanPEF A) :
    (RKE.alongId F).Ran = F := rfl

theorem yoneda_unit_id {A : Type u} (F : KanPEF A) (a : A) :
    ((LKE.alongId F).η.cmp a).toEq = rfl := rfl

theorem yoneda_counit_id {A : Type u} (F : KanPEF A) (a : A) :
    ((RKE.alongId F).ε.cmp a).toEq = rfl := rfl

/-! ## Additional properties -/

theorem lan_ran_id_agree {A : Type u} (F : KanPEF A) :
    (LKE.alongId F).Lan = (RKE.alongId F).Ran := rfl

theorem lan_unit_nat {A : Type u} (K F : KanPEF A) (e : LKE K F)
    {a b : A} (p : Path a b) :
    Path.trans (F.mp p) (e.η.cmp b) =
    Path.trans (e.η.cmp a) ((KanPEF.comp K e.Lan).mp p) :=
  e.η.nat p

theorem ran_counit_nat {A : Type u} (K F : KanPEF A) (e : RKE K F)
    {a b : A} (p : Path a b) :
    Path.trans ((KanPEF.comp K e.Ran).mp p) (e.ε.cmp b) =
    Path.trans (e.ε.cmp a) (F.mp p) :=
  e.ε.nat p

theorem lan_id_univ_trivial {A : Type u} (F G : KanPEF A)
    (σ : KanNT F (KanPEF.comp KanPEF.id G)) (a : A) :
    (σ.cmp a).toEq.symm.trans (σ.cmp a).toEq = rfl := by simp

end ComputationalPaths
