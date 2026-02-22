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

noncomputable def weq_comp {a b c : A} {f : Path a b} {g : Path b c}
    (_hf : IsWeq f) (_hg : IsWeq g) : IsWeq (Path.trans f g) :=
  path_is_weq (Path.trans f g)

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

def LeftHtpy {a b : A} (f g : Path a b) : Type u :=
  RwEq f g

def RightHtpy {a b : A} (f g : Path a b) : Type u :=
  RwEq f g

def left_htpy_refl {a b : A} (f : Path a b) : LeftHtpy f f :=
  RwEq.refl f

def right_htpy_refl {a b : A} (f : Path a b) : RightHtpy f f :=
  RwEq.refl f

def HasLift {a b c d : A} (i : Path a b) (p : Path c d) : Type u :=
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
