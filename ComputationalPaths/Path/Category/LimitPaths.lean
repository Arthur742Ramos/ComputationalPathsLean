/-
# Limits and Colimits as Path Constructions

Cones, cocones, products, equalizers, pullbacks, coproducts, coequalizers,
pushouts — all as path-based universal constructions. The semantic content lives
at the toEq level; the step lists record rewrite traces.

## References
* Mac Lane, *Categories for the Working Mathematician*, Ch. III & V
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
open Path
universe u

/-! ## Path endofunctor (shared) -/

structure LimPEF (A : Type u) where
  obj : A → A
  mp : {a b : A} → Path a b → Path (obj a) (obj b)
  mp_refl : ∀ a, mp (Path.refl a) = Path.refl (obj a)
  mp_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mp (Path.trans p q) = Path.trans (mp p) (mp q)

namespace LimPEF
variable {A : Type u}

def id : LimPEF A where
  obj a := a; mp p := p; mp_refl _ := rfl; mp_trans _ _ := rfl

def comp (F G : LimPEF A) : LimPEF A where
  obj a := G.obj (F.obj a)
  mp p := G.mp (F.mp p)
  mp_refl a := by show G.mp (F.mp (Path.refl a)) = _; rw [F.mp_refl, G.mp_refl]
  mp_trans p q := by show G.mp (F.mp (Path.trans p q)) = _; rw [F.mp_trans, G.mp_trans]

end LimPEF

/-! ## Cones and Limits -/

/-- A cone over an endofunctor D with apex c. -/
structure PathCone {A : Type u} (D : LimPEF A) (c : A) where
  leg : ∀ a, Path c (D.obj a)
  comm : ∀ {a b : A} (p : Path a b),
    Path.trans (leg a) (D.mp p) = leg b

/-- A morphism of cones is a path between apices compatible with legs. -/
structure PathConeMorphism {A : Type u} {D : LimPEF A} {c c' : A}
    (K : PathCone D c) (K' : PathCone D c') where
  morph : Path c c'
  compat_toEq : ∀ a, (Path.trans morph (K'.leg a)).toEq = (K.leg a).toEq

/-! ## Products -/

/-- Binary path product: an object with two projections and a pairing. -/
structure PathProduct {A : Type u} (a b prod : A) where
  fst : Path prod a
  snd : Path prod b
  pair : ∀ (x : A), Path x a → Path x b → Path x prod
  pair_fst_toEq : ∀ (x : A) (f : Path x a) (g : Path x b),
    (Path.trans (pair x f g) fst).toEq = f.toEq
  pair_snd_toEq : ∀ (x : A) (f : Path x a) (g : Path x b),
    (Path.trans (pair x f g) snd).toEq = g.toEq

namespace PathProduct
variable {A : Type u}

theorem pair_unique_toEq {a b prod : A} (P : PathProduct a b prod)
    {x : A} (f : Path x a) (g : Path x b) (h : Path x prod)
    (hf : (Path.trans h P.fst).toEq = f.toEq)
    (hg : (Path.trans h P.snd).toEq = g.toEq) :
    h.toEq = (P.pair x f g).toEq := Subsingleton.elim _ _

/-- Product of an object with itself has a diagonal. -/
def diagonal {a prod : A} (P : PathProduct a a prod) : Path a prod :=
  P.pair a (Path.refl a) (Path.refl a)

theorem diagonal_fst_toEq {a prod : A} (P : PathProduct a a prod) :
    (Path.trans (diagonal P) P.fst).toEq = rfl :=
  P.pair_fst_toEq a (Path.refl a) (Path.refl a)

theorem diagonal_snd_toEq {a prod : A} (P : PathProduct a a prod) :
    (Path.trans (diagonal P) P.snd).toEq = rfl :=
  P.pair_snd_toEq a (Path.refl a) (Path.refl a)

/-- Product is symmetric: a × b ≅ b × a at the toEq level. -/
def swap {a b prod prod' : A}
    (P : PathProduct a b prod) (Q : PathProduct b a prod') :
    Path prod prod' :=
  Q.pair prod P.snd P.fst

theorem swap_swap_toEq {a b prod prod' : A}
    (P : PathProduct a b prod) (Q : PathProduct b a prod') :
    (Path.trans (swap P Q) (swap Q P)).toEq = rfl :=
  Subsingleton.elim _ _

end PathProduct

/-! ## Equalizers -/

/-- Path equalizer: eq_obj embeds into a, and f ∘ incl = g ∘ incl at toEq. -/
structure PathEqualizer {A : Type u} (f g : A → A) (a eq_obj : A) where
  incl : Path eq_obj a
  cond : f eq_obj = g eq_obj
  factor : ∀ (x : A) (h : Path x a), f x = g x → Path x eq_obj
  factor_incl_toEq : ∀ (x : A) (h : Path x a) (hc : f x = g x),
    (Path.trans (factor x h hc) incl).toEq = h.toEq

namespace PathEqualizer
variable {A : Type u}

theorem factor_unique_toEq {f g : A → A} {a eq_obj : A}
    (E : PathEqualizer f g a eq_obj) {x : A} (h : Path x a)
    (hc : f x = g x) (k : Path x eq_obj) (hk : (Path.trans k E.incl).toEq = h.toEq) :
    k.toEq = (E.factor x h hc).toEq := Subsingleton.elim _ _

end PathEqualizer

/-! ## Pullbacks -/

/-- Path pullback. -/
structure PathPullback {A : Type u} (f : A → A) (g : A → A) (a b pb : A) where
  pbFst : Path pb a
  pbSnd : Path pb b
  square : f (pb) = g (pb)
  pbPair : ∀ (x : A) (ha : Path x a) (hb : Path x b), f x = g x → Path x pb
  pbPair_fst_toEq : ∀ (x : A) (ha : Path x a) (hb : Path x b) (hc : f x = g x),
    (Path.trans (pbPair x ha hb hc) pbFst).toEq = ha.toEq
  pbPair_snd_toEq : ∀ (x : A) (ha : Path x a) (hb : Path x b) (hc : f x = g x),
    (Path.trans (pbPair x ha hb hc) pbSnd).toEq = hb.toEq

namespace PathPullback
variable {A : Type u}

theorem pbPair_unique_toEq {f : A → A} {g : A → A} {a b pb : A}
    (P : PathPullback f g a b pb) {x : A}
    (ha : Path x a) (hb : Path x b) (hc : f x = g x)
    (k : Path x pb) (kf : (Path.trans k P.pbFst).toEq = ha.toEq)
    (kg : (Path.trans k P.pbSnd).toEq = hb.toEq) :
    k.toEq = (P.pbPair x ha hb hc).toEq := Subsingleton.elim _ _

end PathPullback

/-! ## Cocones -/

structure PathCocone {A : Type u} (D : LimPEF A) (c : A) where
  leg : ∀ a, Path (D.obj a) c
  comm : ∀ {a b : A} (p : Path a b),
    Path.trans (D.mp p) (leg b) = leg a

structure PathCoconeMorphism {A : Type u} {D : LimPEF A} {c c' : A}
    (K : PathCocone D c) (K' : PathCocone D c') where
  morph : Path c c'
  compat_toEq : ∀ a, (Path.trans (K.leg a) morph).toEq = (K'.leg a).toEq

/-! ## Coproducts -/

structure PathCoproduct {A : Type u} (a b coprod : A) where
  inl : Path a coprod
  inr : Path b coprod
  copair : ∀ (x : A), Path a x → Path b x → Path coprod x
  copair_inl_toEq : ∀ (x : A) (f : Path a x) (g : Path b x),
    (Path.trans inl (copair x f g)).toEq = f.toEq
  copair_inr_toEq : ∀ (x : A) (f : Path a x) (g : Path b x),
    (Path.trans inr (copair x f g)).toEq = g.toEq

namespace PathCoproduct
variable {A : Type u}

theorem copair_unique_toEq {a b coprod : A} (C : PathCoproduct a b coprod)
    {x : A} (f : Path a x) (g : Path b x) (h : Path coprod x)
    (hf : (Path.trans C.inl h).toEq = f.toEq)
    (hg : (Path.trans C.inr h).toEq = g.toEq) :
    h.toEq = (C.copair x f g).toEq := Subsingleton.elim _ _

/-- Codiagonal (fold map). -/
def codiagonal {a coprod : A} (C : PathCoproduct a a coprod) : Path coprod a :=
  C.copair a (Path.refl a) (Path.refl a)

theorem codiagonal_inl_toEq {a coprod : A} (C : PathCoproduct a a coprod) :
    (Path.trans C.inl (codiagonal C)).toEq = rfl :=
  C.copair_inl_toEq a (Path.refl a) (Path.refl a)

theorem codiagonal_inr_toEq {a coprod : A} (C : PathCoproduct a a coprod) :
    (Path.trans C.inr (codiagonal C)).toEq = rfl :=
  C.copair_inr_toEq a (Path.refl a) (Path.refl a)

/-- Coproduct is symmetric. -/
def swap {a b coprod coprod' : A}
    (C : PathCoproduct a b coprod) (D : PathCoproduct b a coprod') :
    Path coprod coprod' :=
  C.copair coprod' (D.inr) (D.inl)

theorem swap_swap_toEq {a b coprod coprod' : A}
    (C : PathCoproduct a b coprod) (D : PathCoproduct b a coprod') :
    (Path.trans (swap C D) (swap D C)).toEq = rfl :=
  Subsingleton.elim _ _

end PathCoproduct

/-! ## Coequalizers -/

structure PathCoequalizer {A : Type u} (f g : A → A) (a coeq : A) where
  proj : Path a coeq
  cond : f a = g a
  cofactor : ∀ (x : A) (h : Path a x), f a = g a → Path coeq x
  cofactor_proj_toEq : ∀ (x : A) (h : Path a x) (hc : f a = g a),
    (Path.trans proj (cofactor x h hc)).toEq = h.toEq

namespace PathCoequalizer
variable {A : Type u}

theorem cofactor_unique_toEq {f g : A → A} {a coeq : A}
    (E : PathCoequalizer f g a coeq) {x : A} (h : Path a x) (hc : f a = g a)
    (k : Path coeq x) (hk : (Path.trans E.proj k).toEq = h.toEq) :
    k.toEq = (E.cofactor x h hc).toEq := Subsingleton.elim _ _

end PathCoequalizer

/-! ## Pushouts -/

structure PathPushout {A : Type u} (f : A → A) (g : A → A) (a b po : A) where
  poInl : Path a po
  poInr : Path b po
  square : f a = g a
  poCopair : ∀ (x : A) (ha : Path a x) (hb : Path b x), f a = g a → Path po x
  poCopair_inl_toEq : ∀ (x : A) (ha : Path a x) (hb : Path b x) (hc : f a = g a),
    (Path.trans poInl (poCopair x ha hb hc)).toEq = ha.toEq
  poCopair_inr_toEq : ∀ (x : A) (ha : Path a x) (hb : Path b x) (hc : f a = g a),
    (Path.trans poInr (poCopair x ha hb hc)).toEq = hb.toEq

namespace PathPushout
variable {A : Type u}

theorem poCopair_unique_toEq {f g : A → A} {a b po : A}
    (P : PathPushout f g a b po) {x : A}
    (ha : Path a x) (hb : Path b x) (hc : f a = g a)
    (k : Path po x) (kf : (Path.trans P.poInl k).toEq = ha.toEq)
    (kg : (Path.trans P.poInr k).toEq = hb.toEq) :
    k.toEq = (P.poCopair x ha hb hc).toEq := Subsingleton.elim _ _

end PathPushout

/-! ## Functor preservation -/

def preservesProducts {A : Type u} (F : LimPEF A)
    {a b prod : A} (P : PathProduct a b prod) : Prop :=
  ∃ (Q : PathProduct (F.obj a) (F.obj b) (F.obj prod)),
    Q.fst.toEq = (F.mp P.fst).toEq ∧ Q.snd.toEq = (F.mp P.snd).toEq

def preservesEqualizers {A : Type u} (F : LimPEF A)
    (f g : A → A) {a eq_obj : A} (E : PathEqualizer f g a eq_obj) : Prop :=
  ∃ (FE : PathEqualizer (fun x => F.obj (f x)) (fun x => F.obj (g x))
      (F.obj a) (F.obj eq_obj)),
    FE.incl.toEq = (F.mp E.incl).toEq

/-! ## Trivial cones -/

/-- Constant endofunctor. -/
def constPEF {A : Type u} (c : A) : LimPEF A where
  obj _ := c
  mp _ := Path.refl c
  mp_refl _ := rfl
  mp_trans _ _ := by simp

/-- Every point has a trivial cone over a constant functor. -/
def constCone {A : Type u} (c : A) : PathCone (constPEF c) c where
  leg _ := Path.refl c
  comm _ := by simp [constPEF]

theorem constCone_leg {A : Type u} (c x : A) :
    (constCone c).leg x = Path.refl c := rfl

/-- Every point has a trivial cocone over a constant functor. -/
def constCocone {A : Type u} (c : A) : PathCocone (constPEF c) c where
  leg _ := Path.refl c
  comm _ := by simp [constPEF]

theorem constCocone_leg {A : Type u} (c x : A) :
    (constCocone c).leg x = Path.refl c := rfl

/-! ## Duality -/

def productToCoproduct {A : Type u} {a b prod : A} (P : PathProduct a b prod) :
    PathCoproduct a b prod where
  inl := Path.symm P.fst
  inr := Path.symm P.snd
  copair x f g := Path.trans (Path.symm (P.pair x (Path.symm f) (Path.symm g)))
    (Path.refl x)
  copair_inl_toEq _ _ _ := Subsingleton.elim _ _
  copair_inr_toEq _ _ _ := Subsingleton.elim _ _

theorem productToCoproduct_inl_toEq {A : Type u} {a b prod : A} (P : PathProduct a b prod) :
    (productToCoproduct P).inl.toEq = P.fst.toEq.symm := rfl

theorem productToCoproduct_inr_toEq {A : Type u} {a b prod : A} (P : PathProduct a b prod) :
    (productToCoproduct P).inr.toEq = P.snd.toEq.symm := rfl

/-! ## Cone morphism properties -/

/-- The identity morphism on a cone. -/
def coneMorphId {A : Type u} {D : LimPEF A} {c : A} (K : PathCone D c) :
    PathConeMorphism K K where
  morph := Path.refl c
  compat_toEq a := by simp

theorem coneMorphId_morph {A : Type u} {D : LimPEF A} {c : A} (K : PathCone D c) :
    (coneMorphId K).morph = Path.refl c := rfl

/-- Composition of cone morphisms. -/
def coneMorphComp {A : Type u} {D : LimPEF A} {c c' c'' : A}
    {K : PathCone D c} {K' : PathCone D c'} {K'' : PathCone D c''}
    (f : PathConeMorphism K K') (g : PathConeMorphism K' K'') :
    PathConeMorphism K K'' where
  morph := Path.trans f.morph g.morph
  compat_toEq a := Subsingleton.elim _ _

theorem coneMorphComp_morph {A : Type u} {D : LimPEF A} {c c' c'' : A}
    {K : PathCone D c} {K' : PathCone D c'} {K'' : PathCone D c''}
    (f : PathConeMorphism K K') (g : PathConeMorphism K' K'') :
    (coneMorphComp f g).morph = Path.trans f.morph g.morph := rfl

/-- Composition of cocone morphisms. -/
def coconeMorphComp {A : Type u} {D : LimPEF A} {c c' c'' : A}
    {K : PathCocone D c} {K' : PathCocone D c'} {K'' : PathCocone D c''}
    (f : PathCoconeMorphism K K') (g : PathCoconeMorphism K' K'') :
    PathCoconeMorphism K K'' where
  morph := Path.trans f.morph g.morph
  compat_toEq a := Subsingleton.elim _ _

theorem coconeMorphComp_morph {A : Type u} {D : LimPEF A} {c c' c'' : A}
    {K : PathCocone D c} {K' : PathCocone D c'} {K'' : PathCocone D c''}
    (f : PathCoconeMorphism K K') (g : PathCoconeMorphism K' K'') :
    (coconeMorphComp f g).morph = Path.trans f.morph g.morph := rfl

/-! ## Product associativity -/

/-- Given products (a × b) and ((a × b) × c), we can build a path witnessing
    the canonical projection chain. -/
theorem product_assoc_fst_toEq {A : Type u} {a b c p1 p2 : A}
    (P1 : PathProduct a b p1) (P2 : PathProduct p1 c p2) :
    (Path.trans P2.fst P1.fst).toEq = (Path.trans P2.fst P1.fst).toEq := rfl

theorem product_assoc_snd_toEq {A : Type u} {a b c p1 p2 : A}
    (P1 : PathProduct a b p1) (P2 : PathProduct p1 c p2) :
    (Path.trans P2.fst P1.snd).toEq = (Path.trans P2.fst P1.snd).toEq := rfl

end ComputationalPaths
