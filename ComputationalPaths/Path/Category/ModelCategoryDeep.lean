import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Category
namespace ModelCategoryDeep

universe u v

variable {A : Type u}

structure IsIso {a b : A} (p : Path a b) where
  inv : Path b a
  id_l : RwEq (Path.trans p inv) (Path.refl a)
  id_r : RwEq (Path.trans inv p) (Path.refl b)

structure IsWeq {a b : A} (p : Path a b) where
  iso : IsIso p

noncomputable def path_is_weq {a b : A} (p : Path a b) : IsWeq p where
  iso :=
    { inv := Path.symm p
      id_l := rweq_cmpA_inv_right (p := p)
      id_r := rweq_cmpA_inv_left (p := p) }

noncomputable def iso_comp {a b c : A} {f : Path a b} {g : Path b c}
    (hf : IsIso f) (hg : IsIso g) : IsIso (Path.trans f g) where
  inv := Path.trans hg.inv hf.inv
  id_l :=
    rweq_trans
      (rweq_tt f g (Path.trans hg.inv hf.inv))
      (rweq_trans
        (rweq_trans_congr_right f
          (rweq_trans
            (rweq_symm (rweq_tt g hg.inv hf.inv))
            (rweq_trans
              (rweq_trans_congr_left hf.inv hg.id_l)
              (rweq_cmpA_refl_left hf.inv))))
        hf.id_l)
  id_r :=
    rweq_trans
      (rweq_tt hg.inv hf.inv (Path.trans f g))
      (rweq_trans
        (rweq_trans_congr_right hg.inv
          (rweq_trans
            (rweq_symm (rweq_tt hf.inv f g))
            (rweq_trans
              (rweq_trans_congr_left g hf.id_r)
              (rweq_cmpA_refl_left g))))
        hg.id_r)

noncomputable def weq_comp {a b c : A} {f : Path a b} {g : Path b c}
    (hf : IsWeq f) (hg : IsWeq g) : IsWeq (Path.trans f g) where
  iso := iso_comp hf.iso hg.iso

structure Cylinder (a : A) where
  C : A
  i0 : Path a C
  i1 : Path a C
  σ : Path C a
  ret0 : RwEq (Path.trans i0 σ) (Path.refl a)
  ret1 : RwEq (Path.trans i1 σ) (Path.refl a)

structure PathObj (a : A) where
  P : A
  s : Path a P
  ev0 : Path P a
  ev1 : Path P a
  sec0 : RwEq (Path.trans s ev0) (Path.refl a)
  sec1 : RwEq (Path.trans s ev1) (Path.refl a)

noncomputable def LeftHtpy {a b : A} (f g : Path a b) : Type (u + 1) :=
  RwEq f g

noncomputable def RightHtpy {a b : A} (f g : Path a b) : Type (u + 1) :=
  RwEq f g

noncomputable def left_htpy_refl {a b : A} (f : Path a b) : LeftHtpy f f :=
  RwEq.refl f

noncomputable def right_htpy_refl {a b : A} (f : Path a b) : RightHtpy f f :=
  RwEq.refl f

noncomputable def HasLift {a b c d : A} (i : Path a b) (p : Path c d) : Type (u + 1) :=
  ∀ (f : Path a c) (g : Path b d),
    RwEq (Path.trans f p) (Path.trans i g) →
    Σ h : Path b c, RwEq (Path.trans i h) f × RwEq (Path.trans h p) g

noncomputable def trans_assoc_rweq {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

noncomputable def trans_right_unit_rweq {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_cmpA_refl_right (p := p)

noncomputable def trans_left_unit_rweq {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_cmpA_refl_left (p := p)

end ModelCategoryDeep
end Category
end Path
end ComputationalPaths
