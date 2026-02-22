/-
# Adjunctions as Path Correspondences

Adjunctions between path endofunctors: unit/counit pairs, triangle identities
at the toEq level, identity and composition adjunctions, hom-set equivalence,
mate correspondence, and uniqueness of adjoints.

## References
* Mac Lane, *Categories for the Working Mathematician*, Ch. IV
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
open Path
universe u

/-! ## Endofunctor -/

structure AdjPEF (A : Type u) where
  obj : A → A
  mp : {a b : A} → Path a b → Path (obj a) (obj b)
  mp_refl : ∀ a, mp (Path.refl a) = Path.refl (obj a)
  mp_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mp (Path.trans p q) = Path.trans (mp p) (mp q)

namespace AdjPEF
variable {A : Type u}

noncomputable def id : AdjPEF A where
  obj a := a
  mp p := p
  mp_refl _ := rfl
  mp_trans _ _ := rfl

noncomputable def comp (F G : AdjPEF A) : AdjPEF A where
  obj a := G.obj (F.obj a)
  mp p := G.mp (F.mp p)
  mp_refl a := by show G.mp (F.mp (Path.refl a)) = _; rw [F.mp_refl, G.mp_refl]
  mp_trans p q := by show G.mp (F.mp (Path.trans p q)) = _; rw [F.mp_trans, G.mp_trans]

theorem comp_obj (F G : AdjPEF A) (a : A) : (comp F G).obj a = G.obj (F.obj a) := rfl
theorem comp_mp (F G : AdjPEF A) {a b : A} (p : Path a b) :
    (comp F G).mp p = G.mp (F.mp p) := rfl
theorem id_obj (a : A) : (AdjPEF.id (A := A)).obj a = a := rfl
theorem id_mp {a b : A} (p : Path a b) : (AdjPEF.id (A := A)).mp p = p := rfl

end AdjPEF

/-! ## Natural transformation -/

structure AdjNT {A : Type u} (F G : AdjPEF A) where
  cmp : ∀ a : A, Path (F.obj a) (G.obj a)
  nat : ∀ {a b : A} (p : Path a b),
    Path.trans (F.mp p) (cmp b) = Path.trans (cmp a) (G.mp p)

namespace AdjNT
variable {A : Type u}

noncomputable def idNT (F : AdjPEF A) : AdjNT F F where
  cmp a := Path.refl (F.obj a)
  nat p := by simp

noncomputable def vcomp {F G H : AdjPEF A} (η : AdjNT F G) (θ : AdjNT G H) : AdjNT F H where
  cmp a := Path.trans (η.cmp a) (θ.cmp a)
  nat p := by
    rw [← Path.trans_assoc, η.nat p, Path.trans_assoc, θ.nat p, ← Path.trans_assoc]

theorem vcomp_cmp {F G H : AdjPEF A} (η : AdjNT F G) (θ : AdjNT G H) (a : A) :
    (vcomp η θ).cmp a = Path.trans (η.cmp a) (θ.cmp a) := rfl

noncomputable def whiskerL {F G : AdjPEF A} (H : AdjPEF A) (η : AdjNT F G) :
    AdjNT (AdjPEF.comp F H) (AdjPEF.comp G H) where
  cmp a := H.mp (η.cmp a)
  nat p := by
    show Path.trans (H.mp (F.mp p)) (H.mp (η.cmp _)) =
         Path.trans (H.mp (η.cmp _)) (H.mp (G.mp p))
    rw [← H.mp_trans, ← H.mp_trans, η.nat p]

noncomputable def whiskerR {F G : AdjPEF A} (η : AdjNT F G) (H : AdjPEF A) :
    AdjNT (AdjPEF.comp H F) (AdjPEF.comp H G) where
  cmp a := η.cmp (H.obj a)
  nat p := η.nat (H.mp p)

theorem idNT_cmp (F : AdjPEF A) (a : A) : (idNT F).cmp a = Path.refl (F.obj a) := rfl

end AdjNT

/-! ## Adjunction -/

structure PathAdj {A : Type u} (L R : AdjPEF A) where
  η : AdjNT AdjPEF.id (AdjPEF.comp L R)
  ε : AdjNT (AdjPEF.comp R L) AdjPEF.id
  triL : ∀ a, (Path.trans (L.mp (η.cmp a)) (ε.cmp (L.obj a))).toEq = rfl
  triR : ∀ a, (Path.trans (η.cmp (R.obj a)) (R.mp (ε.cmp a))).toEq = rfl

namespace PathAdj
variable {A : Type u}

/-! ### Identity adjunction -/

noncomputable def idAdj : PathAdj (AdjPEF.id (A := A)) AdjPEF.id where
  η := AdjNT.idNT AdjPEF.id
  ε := AdjNT.idNT AdjPEF.id
  triL _ := by simp [AdjPEF.id]
  triR _ := by simp [AdjPEF.id]

theorem idAdj_η (a : A) : (idAdj (A := A)).η.cmp a = Path.refl a := rfl
theorem idAdj_ε (a : A) : (idAdj (A := A)).ε.cmp a = Path.refl a := rfl
theorem idAdj_triL (a : A) : (idAdj (A := A)).triL a = rfl := Subsingleton.elim _ _
theorem idAdj_triR (a : A) : (idAdj (A := A)).triR a = rfl := Subsingleton.elim _ _

/-! ### Composition of adjunctions -/

noncomputable def compAdj {L R L' R' : AdjPEF A} (adj₁ : PathAdj L R) (adj₂ : PathAdj L' R') :
    PathAdj (AdjPEF.comp L L') (AdjPEF.comp R' R) where
  η := {
    cmp := fun a => Path.trans (adj₁.η.cmp a) (R.mp (adj₂.η.cmp (L.obj a)))
    nat := by
      intro a b p
      -- Goal: trans (id.mp p) (η_comp b) = trans (η_comp a) ((comp (comp L L') (comp R' R)).mp p)
      -- Unfold: id.mp p = p, composite mp = R.mp (R'.mp (L'.mp (L.mp p)))
      show Path.trans p (Path.trans (adj₁.η.cmp b) (R.mp (adj₂.η.cmp (L.obj b)))) =
           Path.trans (Path.trans (adj₁.η.cmp a) (R.mp (adj₂.η.cmp (L.obj a))))
             (R.mp (R'.mp (L'.mp (L.mp p))))
      rw [← Path.trans_assoc]
      have h1 : Path.trans p (adj₁.η.cmp b) =
        Path.trans (adj₁.η.cmp a) (R.mp (L.mp p)) := adj₁.η.nat p
      rw [h1, Path.trans_assoc, ← R.mp_trans]
      have h2 : Path.trans (L.mp p) (adj₂.η.cmp (L.obj b)) =
        Path.trans (adj₂.η.cmp (L.obj a)) (R'.mp (L'.mp (L.mp p))) :=
        adj₂.η.nat (L.mp p)
      rw [h2, R.mp_trans, ← Path.trans_assoc]
  }
  ε := {
    cmp := fun a => Path.trans (L'.mp (adj₁.ε.cmp (R'.obj a))) (adj₂.ε.cmp a)
    nat := by
      intro a b p
      -- Goal: trans ((comp (comp R' R) (comp L L')).mp p) (ε_comp b) = trans (ε_comp a) (id.mp p)
      -- Unfold: composite mp = L'.mp (L.mp (R.mp (R'.mp p))), id.mp p = p
      show Path.trans (L'.mp (L.mp (R.mp (R'.mp p))))
             (Path.trans (L'.mp (adj₁.ε.cmp (R'.obj b))) (adj₂.ε.cmp b)) =
           Path.trans (Path.trans (L'.mp (adj₁.ε.cmp (R'.obj a))) (adj₂.ε.cmp a)) p
      rw [← Path.trans_assoc, ← L'.mp_trans]
      have h1 : Path.trans (L.mp (R.mp (R'.mp p))) (adj₁.ε.cmp (R'.obj b)) =
        Path.trans (adj₁.ε.cmp (R'.obj a)) (R'.mp p) := adj₁.ε.nat (R'.mp p)
      rw [h1, L'.mp_trans, Path.trans_assoc]
      have h2 : Path.trans (L'.mp (R'.mp p)) (adj₂.ε.cmp b) =
        Path.trans (adj₂.ε.cmp a) p := adj₂.ε.nat p
      rw [h2, ← Path.trans_assoc]
  }
  triL _ := Subsingleton.elim _ _
  triR _ := Subsingleton.elim _ _

theorem compAdj_η {L R L' R' : AdjPEF A} (adj₁ : PathAdj L R) (adj₂ : PathAdj L' R') (a : A) :
    (compAdj adj₁ adj₂).η.cmp a =
      Path.trans (adj₁.η.cmp a) (R.mp (adj₂.η.cmp (L.obj a))) := rfl

theorem compAdj_ε {L R L' R' : AdjPEF A} (adj₁ : PathAdj L R) (adj₂ : PathAdj L' R') (a : A) :
    (compAdj adj₁ adj₂).ε.cmp a =
      Path.trans (L'.mp (adj₁.ε.cmp (R'.obj a))) (adj₂.ε.cmp a) := rfl

/-! ### Hom-set equivalence -/

noncomputable def homFwd {L R : AdjPEF A} (adj : PathAdj L R) {a b : A}
    (f : Path (L.obj a) b) : Path a (R.obj b) :=
  Path.trans (adj.η.cmp a) (R.mp f)

noncomputable def homBwd {L R : AdjPEF A} (adj : PathAdj L R) {a b : A}
    (g : Path a (R.obj b)) : Path (L.obj a) b :=
  Path.trans (L.mp g) (adj.ε.cmp b)

theorem homFwd_Bwd_toEq {L R : AdjPEF A} (adj : PathAdj L R)
    {a b : A} (f : Path (L.obj a) b) :
    (homBwd adj (homFwd adj f)).toEq = f.toEq := Subsingleton.elim _ _

theorem homBwd_Fwd_toEq {L R : AdjPEF A} (adj : PathAdj L R)
    {a b : A} (g : Path a (R.obj b)) :
    (homFwd adj (homBwd adj g)).toEq = g.toEq := Subsingleton.elim _ _

theorem η_from_hom {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    (homFwd adj (Path.refl (L.obj a))).toEq = (adj.η.cmp a).toEq :=
  Subsingleton.elim _ _

theorem ε_from_hom {L R : AdjPEF A} (adj : PathAdj L R) (b : A) :
    (homBwd adj (Path.refl (R.obj b))).toEq = (adj.ε.cmp b).toEq :=
  Subsingleton.elim _ _

theorem homFwd_def {L R : AdjPEF A} (adj : PathAdj L R) {a b : A}
    (f : Path (L.obj a) b) : homFwd adj f = Path.trans (adj.η.cmp a) (R.mp f) := rfl

theorem homBwd_def {L R : AdjPEF A} (adj : PathAdj L R) {a b : A}
    (g : Path a (R.obj b)) : homBwd adj g = Path.trans (L.mp g) (adj.ε.cmp b) := rfl

/-! ### Mate correspondence (propositional level) -/

/-- Given L ⊣ R and L' ⊣ R', any σ : L.obj a = L'.obj a induces a mate R'.obj a = R.obj a. -/
noncomputable def mateProp {L R L' R' : AdjPEF A} (adj₁ : PathAdj L R) (adj₂ : PathAdj L' R')
    (σ : ∀ a, L.obj a = L'.obj a) (a : A) : R'.obj a = R.obj a :=
  ((adj₁.η.cmp (R'.obj a)).toEq).trans
    (_root_.congrArg R.obj (((σ (R'.obj a)).trans (adj₂.ε.cmp a).toEq)))

theorem mateProp_id {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    mateProp adj adj (fun x => rfl) a =
      ((adj.η.cmp (R.obj a)).toEq).trans (_root_.congrArg R.obj (adj.ε.cmp a).toEq) := rfl

/-! ### Adjoint uniqueness -/

structure AdjPEFIso (F G : AdjPEF A) where
  fwd : ∀ a, F.obj a = G.obj a
  bwd : ∀ a, G.obj a = F.obj a
  li  : ∀ a, (fwd a).trans (bwd a) = rfl
  ri  : ∀ a, (bwd a).trans (fwd a) = rfl

/-- Left adjoints are unique up to isomorphism (propositional level). -/
noncomputable def leftUnique {L L' R : AdjPEF A} (a1 : PathAdj L R) (a2 : PathAdj L' R) :
    AdjPEFIso L L' where
  fwd a := (_root_.congrArg L.obj (a2.η.cmp a).toEq).trans (a1.ε.cmp (L'.obj a)).toEq
  bwd a := (_root_.congrArg L'.obj (a1.η.cmp a).toEq).trans (a2.ε.cmp (L.obj a)).toEq
  li _ := Subsingleton.elim _ _
  ri _ := Subsingleton.elim _ _

/-- Right adjoints are unique up to propositional isomorphism via the mate. -/
noncomputable def rightUnique {L R R' : AdjPEF A} (a1 : PathAdj L R) (a2 : PathAdj L R') :
    AdjPEFIso R R' where
  fwd a := mateProp a2 a1 (fun _ => rfl) a
  bwd a := mateProp a1 a2 (fun _ => rfl) a
  li _ := Subsingleton.elim _ _
  ri _ := Subsingleton.elim _ _

/-! ### Naturality as equalities -/

theorem η_nat_toEq {L R : AdjPEF A} (adj : PathAdj L R) {a b : A} (p : Path a b) :
    (Path.trans p (adj.η.cmp b)).toEq =
    (Path.trans (adj.η.cmp a) (R.mp (L.mp p))).toEq := Subsingleton.elim _ _

theorem ε_nat_toEq {L R : AdjPEF A} (adj : PathAdj L R) {a b : A} (p : Path a b) :
    (Path.trans (L.mp (R.mp p)) (adj.ε.cmp b)).toEq =
    (Path.trans (adj.ε.cmp a) p).toEq := Subsingleton.elim _ _

theorem triL_from_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    (Path.trans (L.mp (adj.η.cmp a)) (adj.ε.cmp (L.obj a))).toEq = rfl :=
  adj.triL a

theorem triR_from_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    (Path.trans (adj.η.cmp (R.obj a)) (R.mp (adj.ε.cmp a))).toEq = rfl :=
  adj.triR a

/-! ### Composition with identity -/

theorem compAdj_idAdj_left_η_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    ((compAdj idAdj adj).η.cmp a).toEq = (adj.η.cmp a).toEq :=
  Subsingleton.elim _ _

theorem compAdj_idAdj_left_ε_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    ((compAdj idAdj adj).ε.cmp a).toEq = (adj.ε.cmp a).toEq :=
  Subsingleton.elim _ _

theorem compAdj_idAdj_right_η_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    ((compAdj adj idAdj).η.cmp a).toEq = (adj.η.cmp a).toEq :=
  Subsingleton.elim _ _

theorem compAdj_idAdj_right_ε_toEq {L R : AdjPEF A} (adj : PathAdj L R) (a : A) :
    ((compAdj adj idAdj).ε.cmp a).toEq = (adj.ε.cmp a).toEq :=
  Subsingleton.elim _ _

end PathAdj
end ComputationalPaths
