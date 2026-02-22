/-
# Higher Topos Theory via Computational Paths

This module develops higher topos theory using computational paths as the
fundamental witness structure. Presheaf categories, Grothendieck topologies,
sheaf conditions, higher stacks, geometric morphisms, classifying topoi,
and Giraud's axioms are all formulated with Path-based witnesses
(Step/Path/trans/symm/congrArg/transport).

## References

- Lurie, *Higher Topos Theory*
- Mac Lane & Moerdijk, *Sheaves in Geometry and Logic*
- de Queiroz et al., *Propositional equality, identity types, and direct
  computational paths*
-/

import ComputationalPaths.Path.Basic.Core

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace HigherToposPaths

open Path

universe u v w

/-! ## Path-based category infrastructure -/

structure HTCat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (A : Obj) → Hom A A
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
  assoc : {A B C D : Obj} → (f : Hom A B) → (g : Hom B C) → (h : Hom C D) →
    Path (comp (comp f g) h) (comp f (comp g h))
  id_left : {A B : Obj} → (f : Hom A B) → Path (comp (id A) f) f
  id_right : {A B : Obj} → (f : Hom A B) → Path (comp f (id B)) f

variable {C : HTCat.{u, v}}

structure HTFun (C D : HTCat.{u, v}) where
  obj : C.Obj → D.Obj
  map : {A B : C.Obj} → C.Hom A B → D.Hom (obj A) (obj B)
  map_id : (A : C.Obj) → Path (map (C.id A)) (D.id (obj A))
  map_comp : {A B E : C.Obj} → (f : C.Hom A B) → (g : C.Hom B E) →
    Path (map (C.comp f g)) (D.comp (map f) (map g))

structure HTNat {C D : HTCat.{u, v}} (F G : HTFun C D) where
  app : (A : C.Obj) → D.Hom (F.obj A) (G.obj A)
  natural : {A B : C.Obj} → (f : C.Hom A B) →
    Path (D.comp (F.map f) (app B)) (D.comp (app A) (G.map f))

/-! ## Presheaf categories -/

structure HTPSh (C : HTCat.{u, v}) where
  sec : C.Obj → Type v
  res : {A B : C.Obj} → C.Hom A B → sec B → sec A
  res_id : (A : C.Obj) → (s : sec A) → Path (res (C.id A) s) s
  res_comp : {A B E : C.Obj} → (f : C.Hom A B) → (g : C.Hom B E) →
    (s : sec E) → Path (res (C.comp f g) s) (res f (res g s))

structure HTPShMor {C : HTCat.{u, v}} (F G : HTPSh C) where
  comp_at : (A : C.Obj) → F.sec A → G.sec A
  nat : {A B : C.Obj} → (f : C.Hom A B) → (s : F.sec B) →
    Path (comp_at A (F.res f s)) (G.res f (comp_at B s))

/-! ## Theorem 1: Presheaf identity morphism -/

noncomputable def presheaf_id_mor (F : HTPSh C) : HTPShMor F F where
  comp_at := fun _ s => s
  nat := fun _ _ => Path.refl _

/-! ## Theorem 2: Presheaf morphism composition -/

noncomputable def presheaf_comp_mor {F G H : HTPSh C}
    (α : HTPShMor F G) (β : HTPShMor G H) : HTPShMor F H where
  comp_at := fun A s => β.comp_at A (α.comp_at A s)
  nat := fun {A B} f s =>
    Path.trans
      (congrArg (β.comp_at A) (α.nat f s))
      (β.nat f (α.comp_at B s))

/-! ## Theorem 3–5: Category laws for presheaf morphisms -/

theorem presheaf_id_left (F G : HTPSh C)
    (α : HTPShMor F G) (A : C.Obj) (s : F.sec A) :
    (presheaf_comp_mor (presheaf_id_mor F) α).comp_at A s =
    α.comp_at A s := rfl

theorem presheaf_id_right (F G : HTPSh C)
    (α : HTPShMor F G) (A : C.Obj) (s : F.sec A) :
    (presheaf_comp_mor α (presheaf_id_mor G)).comp_at A s =
    α.comp_at A s := rfl

theorem presheaf_comp_assoc {F G H K : HTPSh C}
    (α : HTPShMor F G) (β : HTPShMor G H) (γ : HTPShMor H K)
    (A : C.Obj) (s : F.sec A) :
    (presheaf_comp_mor (presheaf_comp_mor α β) γ).comp_at A s =
    (presheaf_comp_mor α (presheaf_comp_mor β γ)).comp_at A s := rfl

/-! ## Grothendieck topology -/

structure HTSieve (C : HTCat.{u, v}) (c : C.Obj) where
  mem : {d : C.Obj} → C.Hom d c → Prop
  closed : {d e : C.Obj} → (f : C.Hom d c) → (g : C.Hom e d) →
    mem f → mem (C.comp g f)

noncomputable def maxSieve (C : HTCat.{u, v}) (c : C.Obj) : HTSieve C c where
  mem := fun _ => True
  closed := fun _ _ _ => True.intro

structure HTGTop (C : HTCat.{u, v}) where
  cov : (c : C.Obj) → HTSieve C c → Prop
  max_cov : (c : C.Obj) → cov c (maxSieve C c)

/-! ## Theorem 6–7: Topology basics -/

theorem max_sieve_covers (J : HTGTop C) (c : C.Obj) :
    J.cov c (maxSieve C c) := J.max_cov c

theorem sieve_closed {c : C.Obj} (S : HTSieve C c) {d e : C.Obj}
    (f : C.Hom d c) (g : C.Hom e d) (hf : S.mem f) :
    S.mem (C.comp g f) := S.closed f g hf

/-! ## Sheaf condition via path descent -/

structure HTMatch {C : HTCat.{u, v}} (F : HTPSh C) {c : C.Obj} (S : HTSieve C c) where
  fam : {d : C.Obj} → (f : C.Hom d c) → S.mem f → F.sec d
  compat : {d e : C.Obj} → (f : C.Hom d c) → (g : C.Hom e d) →
    (hf : S.mem f) →
    Path (F.res g (fam f hf)) (fam (C.comp g f) (S.closed f g hf))

structure HTAmalg {C : HTCat.{u, v}} {F : HTPSh C} {c : C.Obj}
    {S : HTSieve C c} (m : HTMatch F S) where
  glob : F.sec c
  restricts : {d : C.Obj} → (f : C.Hom d c) → (hf : S.mem f) →
    Path (F.res f glob) (m.fam f hf)

structure HTSheafCond {C : HTCat.{u, v}} (J : HTGTop C) (F : HTPSh C) where
  amalg : {c : C.Obj} → {S : HTSieve C c} →
    J.cov c S → (m : HTMatch F S) → HTAmalg m
  uniq : {c : C.Obj} → {S : HTSieve C c} →
    (hS : J.cov c S) → (m : HTMatch F S) →
    (a₁ a₂ : HTAmalg m) → a₁.glob = a₂.glob

structure HTSheaf (C : HTCat.{u, v}) (J : HTGTop C) where
  psh : HTPSh C
  cond : HTSheafCond J psh

/-! ## Theorem 8: Amalgamation restricts correctly -/

noncomputable def amalg_restricts {J : HTGTop C} {F : HTPSh C}
    {c : C.Obj} {S : HTSieve C c}
    (sc : HTSheafCond J F) (hS : J.cov c S) (m : HTMatch F S)
    {d : C.Obj} (f : C.Hom d c) (hf : S.mem f) :
    Path (F.res f (sc.amalg hS m).glob) (m.fam f hf) :=
  (sc.amalg hS m).restricts f hf

/-! ## Theorem 9: Sheaf uniqueness -/

theorem sheaf_unique {J : HTGTop C} {F : HTPSh C}
    {c : C.Obj} {S : HTSieve C c}
    (sc : HTSheafCond J F) (hS : J.cov c S) (m : HTMatch F S)
    (a₁ a₂ : HTAmalg m) : a₁.glob = a₂.glob :=
  sc.uniq hS m a₁ a₂

/-! ## Theorem 10: Amalgamation restriction via congrArg -/

noncomputable def amalg_restrict_congr {J : HTGTop C} {F : HTPSh C}
    {c : C.Obj} {S : HTSieve C c}
    (sc : HTSheafCond J F) (hS : J.cov c S) (m : HTMatch F S)
    {d e : C.Obj} (f : C.Hom d c) (g : C.Hom e d) (hf : S.mem f) :
    Path (F.res g (F.res f (sc.amalg hS m).glob))
         (F.res g (m.fam f hf)) :=
  congrArg (F.res g) ((sc.amalg hS m).restricts f hf)

/-! ## Higher stacks via path groupoid objects -/

structure HTSimp (C : HTCat.{u, v}) where
  lev : Nat → C.Obj
  face : (n : Nat) → Fin (n + 2) → C.Hom (lev (n + 1)) (lev n)
  degen : (n : Nat) → Fin (n + 1) → C.Hom (lev n) (lev (n + 1))
  face_degen_id : (n : Nat) → (i : Fin (n + 1)) →
    Path (C.comp (degen n i) (face n i.castSucc)) (C.id (lev n))

structure HTGrpd (C : HTCat.{u, v}) extends HTSimp C where
  inv : C.Hom (lev 1) (lev 1)
  inv_inv : Path (C.comp inv inv) (C.id (lev 1))

/-! ## Theorem 11: Groupoid inverse is involutive -/

noncomputable def grpd_inv_involutive (G : HTGrpd C) :
    Path (C.comp G.inv G.inv) (C.id (G.lev 1)) := G.inv_inv

/-! ## Theorem 12: Groupoid face-degeneracy cancellation -/

noncomputable def grpd_face_degen (G : HTGrpd C) (i : Fin 1) :
    Path (C.comp (G.degen 0 i) (G.face 0 i.castSucc)) (C.id (G.lev 0)) :=
  G.face_degen_id 0 i

/-! ## Geometric morphisms via path adjunctions -/

structure HTAdj {C D : HTCat.{u, v}} (L : HTFun C D) (R : HTFun D C) where
  unit : (A : C.Obj) → C.Hom A (R.obj (L.obj A))
  counit : (B : D.Obj) → D.Hom (L.obj (R.obj B)) B
  tri_L : (A : C.Obj) →
    Path (D.comp (L.map (unit A)) (counit (L.obj A))) (D.id (L.obj A))
  tri_R : (B : D.Obj) →
    Path (C.comp (unit (R.obj B)) (R.map (counit B))) (C.id (R.obj B))

structure HTGeom (E F : HTCat.{u, v}) where
  direct : HTFun E F
  inverse : HTFun F E
  adj : HTAdj inverse direct

/-! ## Theorem 13: Geometric morphism left triangle -/

noncomputable def geom_tri_L {E F : HTCat.{u, v}} (gm : HTGeom E F) (A : F.Obj) :
    Path (E.comp (gm.inverse.map (gm.adj.unit A)) (gm.adj.counit (gm.inverse.obj A)))
         (E.id (gm.inverse.obj A)) :=
  gm.adj.tri_L A

/-! ## Theorem 14: Geometric morphism right triangle -/

noncomputable def geom_tri_R {E F : HTCat.{u, v}} (gm : HTGeom E F) (B : E.Obj) :
    Path (F.comp (gm.adj.unit (gm.direct.obj B)) (gm.direct.map (gm.adj.counit B)))
         (F.id (gm.direct.obj B)) :=
  gm.adj.tri_R B

/-! ## Theorem 15: Functor composition preserves identity via trans -/

noncomputable def fun_comp_id {C D E : HTCat.{u, v}}
    (F : HTFun C D) (G : HTFun D E) (A : C.Obj) :
    Path (G.map (F.map (C.id A))) (E.id (G.obj (F.obj A))) :=
  Path.trans (congrArg G.map (F.map_id A)) (G.map_id (F.obj A))

/-! ## Theorem 16: Functor composition preserves composition via trans -/

noncomputable def fun_comp_comp {C D E : HTCat.{u, v}}
    (F : HTFun C D) (G : HTFun D E)
    {A B K : C.Obj} (f : C.Hom A B) (g : C.Hom B K) :
    Path (G.map (F.map (C.comp f g)))
         (E.comp (G.map (F.map f)) (G.map (F.map g))) :=
  Path.trans (congrArg G.map (F.map_comp f g)) (G.map_comp (F.map f) (F.map g))

/-! ## Classifying topos -/

structure HTSite where
  cat : HTCat.{u, v}
  top : HTGTop cat

structure HTFlat (C D : HTCat.{u, v}) extends HTFun C D

structure HTClassTopos (site : HTSite.{u, v}) where
  topos : HTCat.{u, v}
  embed : HTFun site.cat topos
  universal : (E : HTCat.{u, v}) → HTFlat site.cat E → HTGeom E topos

/-! ## Theorem 17: Embedding preserves identity -/

noncomputable def classify_embed_id {site : HTSite.{u, v}} (ct : HTClassTopos site)
    (A : site.cat.Obj) :
    Path (ct.embed.map (site.cat.id A)) (ct.topos.id (ct.embed.obj A)) :=
  ct.embed.map_id A

/-! ## Theorem 18: Embedding preserves composition -/

noncomputable def classify_embed_comp {site : HTSite.{u, v}} (ct : HTClassTopos site)
    {A B E : site.cat.Obj} (f : site.cat.Hom A B) (g : site.cat.Hom B E) :=
  ct.embed.map_comp f g

/-! ## Giraud's axioms via path colimits -/

structure HTCoprod (C : HTCat.{u, v}) (A B : C.Obj) where
  obj : C.Obj
  inl : C.Hom A obj
  inr : C.Hom B obj
  elim : {X : C.Obj} → C.Hom A X → C.Hom B X → C.Hom obj X
  inl_elim : {X : C.Obj} → (f : C.Hom A X) → (g : C.Hom B X) →
    Path (C.comp inl (elim f g)) f
  inr_elim : {X : C.Obj} → (f : C.Hom A X) → (g : C.Hom B X) →
    Path (C.comp inr (elim f g)) g

structure HTCoeq (C : HTCat.{u, v}) {A B : C.Obj} (f g : C.Hom A B) where
  obj : C.Obj
  proj : C.Hom B obj
  cond : Path (C.comp f proj) (C.comp g proj)
  elim : {X : C.Obj} → (h : C.Hom B X) → Path (C.comp f h) (C.comp g h) →
    C.Hom obj X
  proj_elim : {X : C.Obj} → (h : C.Hom B X) →
    (p : Path (C.comp f h) (C.comp g h)) →
    Path (C.comp proj (elim h p)) h

structure HTEffEpi (C : HTCat.{u, v}) {A B : C.Obj} (e : C.Hom A B) where
  ker : C.Obj
  pr1 : C.Hom ker A
  pr2 : C.Hom ker A
  rel : Path (C.comp pr1 e) (C.comp pr2 e)

structure HTGiraud (C : HTCat.{u, v}) where
  has_coprod : (A B : C.Obj) → HTCoprod C A B
  has_coeq : {A B : C.Obj} → (f g : C.Hom A B) → HTCoeq C f g
  gens : List C.Obj

/-! ## Theorem 19: Coproduct inl cancellation -/

noncomputable def coprod_inl_cancel {A B : C.Obj}
    (cp : HTCoprod C A B) {X : C.Obj} (f : C.Hom A X) (g : C.Hom B X) :
    Path (C.comp cp.inl (cp.elim f g)) f := cp.inl_elim f g

/-! ## Theorem 20: Coproduct inr cancellation -/

noncomputable def coprod_inr_cancel {A B : C.Obj}
    (cp : HTCoprod C A B) {X : C.Obj} (f : C.Hom A X) (g : C.Hom B X) :
    Path (C.comp cp.inr (cp.elim f g)) g := cp.inr_elim f g

/-! ## Theorem 21: Coequalizer absorbs relation -/

noncomputable def coeq_absorbs {A B : C.Obj} {f g : C.Hom A B} (cq : HTCoeq C f g) :
    Path (C.comp f cq.proj) (C.comp g cq.proj) := cq.cond

/-! ## Theorem 22: Coequalizer universal property -/

noncomputable def coeq_univ {A B : C.Obj} {f g : C.Hom A B} (cq : HTCoeq C f g)
    {X : C.Obj} (h : C.Hom B X) (p : Path (C.comp f h) (C.comp g h)) :
    Path (C.comp cq.proj (cq.elim h p)) h := cq.proj_elim h p

/-! ## Theorem 23: Effective epi kernel relation -/

noncomputable def eff_epi_rel {A B : C.Obj} {e : C.Hom A B} (eff : HTEffEpi C e) :
    Path (C.comp eff.pr1 e) (C.comp eff.pr2 e) := eff.rel

/-! ## Path descent -/

structure HTDescent {C : HTCat.{u, v}} {J : HTGTop C}
    {c : C.Obj} {S : HTSieve C c} (F : HTPSh C) where
  loc : {d : C.Obj} → (f : C.Hom d c) → S.mem f → F.sec d
  cocycle : {d e : C.Obj} → (f : C.Hom d c) → (g : C.Hom e d) →
    (hf : S.mem f) →
    Path (F.res g (loc f hf)) (loc (C.comp g f) (S.closed f g hf))

/-! ## Theorem 24: Descent datum to matching family -/

noncomputable def descent_to_match {J : HTGTop C} {c : C.Obj}
    {S : HTSieve C c} {F : HTPSh C}
    (dd : HTDescent (C := C) (J := J) (S := S) F) : HTMatch F S where
  fam := dd.loc
  compat := dd.cocycle

/-! ## Theorem 25: Sheaf descent yields global section -/

noncomputable def sheaf_descent {J : HTGTop C} {c : C.Obj}
    {S : HTSieve C c} {F : HTPSh C}
    (sc : HTSheafCond J F) (hS : J.cov c S)
    (dd : HTDescent (C := C) (J := J) (S := S) F) : F.sec c :=
  (sc.amalg hS (descent_to_match dd)).glob

/-! ## Theorem 26: Descended section restricts to local data -/

noncomputable def descended_restricts {J : HTGTop C} {c : C.Obj}
    {S : HTSieve C c} {F : HTPSh C}
    (sc : HTSheafCond J F) (hS : J.cov c S)
    (dd : HTDescent (C := C) (J := J) (S := S) F)
    {d : C.Obj} (f : C.Hom d c) (hf : S.mem f) :
    Path (F.res f (sheaf_descent sc hS dd)) (dd.loc f hf) :=
  (sc.amalg hS (descent_to_match dd)).restricts f hf

/-! ## Representable presheaf and Yoneda -/

noncomputable def yoneda (C : HTCat.{u, v}) (c : C.Obj) : HTPSh C where
  sec := fun d => C.Hom d c
  res := fun f g => C.comp f g
  res_id := fun A s => C.id_left s
  res_comp := fun f g s => C.assoc f g s

/-! ## Theorem 27: Yoneda forward map -/

noncomputable def yoneda_fwd {c : C.Obj} {F : HTPSh C}
    (α : HTPShMor (yoneda C c) F) : F.sec c :=
  α.comp_at c (C.id c)

/-! ## Theorem 28: Yoneda backward map -/

noncomputable def yoneda_bwd {c : C.Obj} {F : HTPSh C}
    (s : F.sec c) : HTPShMor (yoneda C c) F where
  comp_at := fun d f => F.res f s
  nat := fun {A B} f g => F.res_comp f g s

/-! ## Theorem 29: Yoneda roundtrip -/

noncomputable def yoneda_roundtrip {c : C.Obj} {F : HTPSh C} (s : F.sec c) :
    Path (yoneda_fwd (yoneda_bwd s)) s :=
  F.res_id c s

/-! ## Theorem 30: Natural transformation vertical composition -/

noncomputable def nat_vcomp {C D : HTCat.{u, v}} {F G H : HTFun C D}
    (α : HTNat F G) (β : HTNat G H) : HTNat F H where
  app := fun A => D.comp (α.app A) (β.app A)
  natural := fun {A B} f =>
    Path.trans
      (Path.symm (D.assoc (F.map f) (α.app B) (β.app B)))
      (Path.trans
        (congrArg (fun h => D.comp h (β.app B)) (α.natural f))
        (Path.trans
          (D.assoc (α.app A) (G.map f) (β.app B))
          (Path.trans
            (congrArg (D.comp (α.app A)) (β.natural f))
            (Path.symm (D.assoc (α.app A) (β.app A) (H.map f))))))

/-! ## Theorem 31: Identity natural transformation -/

noncomputable def nat_id {C D : HTCat.{u, v}} (F : HTFun C D) : HTNat F F where
  app := fun A => D.id (F.obj A)
  natural := fun {A B} f =>
    Path.trans (D.id_right (F.map f)) (Path.symm (D.id_left (F.map f)))

/-! ## Theorem 32: Plus construction -/

structure HTPlusConstr {C : HTCat.{u, v}} (J : HTGTop C) (F : HTPSh C) where
  sec' : C.Obj → Type v
  res' : {A B : C.Obj} → C.Hom A B → sec' B → sec' A
  res'_id : (A : C.Obj) → (s : sec' A) → Path (res' (C.id A) s) s
  res'_comp : {A B E : C.Obj} → (f : C.Hom A B) → (g : C.Hom B E) →
    (s : sec' E) → Path (res' (C.comp f g) s) (res' f (res' g s))
  eta : (A : C.Obj) → F.sec A → sec' A

noncomputable def plus_id {J : HTGTop C} {F : HTPSh C}
    (pc : HTPlusConstr J F) (A : C.Obj) (s : pc.sec' A) :
    Path (pc.res' (C.id A) s) s := pc.res'_id A s

/-! ## Theorem 33: Plus composition -/

noncomputable def plus_comp {J : HTGTop C} {F : HTPSh C}
    (pc : HTPlusConstr J F) {A B E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B E) (s : pc.sec' E) :
    Path (pc.res' (C.comp f g) s) (pc.res' f (pc.res' g s)) :=
  pc.res'_comp f g s

/-! ## Theorem 34: Presheaf restriction coherence -/

noncomputable def psh_res_coh (F : HTPSh C) {A B E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B E) (s : F.sec E) :
    Path (F.res (C.comp f g) s) (F.res f (F.res g s)) :=
  F.res_comp f g s

/-! ## Theorem 35: Symmetry of presheaf restriction -/

noncomputable def psh_res_symm (F : HTPSh C) {A B E : C.Obj}
    (f : C.Hom A B) (g : C.Hom B E) (s : F.sec E) :
    Path (F.res f (F.res g s)) (F.res (C.comp f g) s) :=
  Path.symm (F.res_comp f g s)

/-! ## Theorem 36: Functor map respects path -/

noncomputable def fun_map_path {C D : HTCat.{u, v}} (F : HTFun C D)
    {A B : C.Obj} {f g : C.Hom A B} (p : Path f g) :
    Path (F.map f) (F.map g) :=
  congrArg F.map p

/-! ## Theorem 37: Natural transformation identity component -/

theorem nat_id_comp {C D : HTCat.{u, v}} (F : HTFun C D) (A : C.Obj) :
    (nat_id F).app A = D.id (F.obj A) := rfl

/-! ## Theorem 38: Giraud coproduct elimination -/

noncomputable def giraud_coprod {G : HTGiraud C} (A B : C.Obj)
    {X : C.Obj} (f : C.Hom A X) (g : C.Hom B X) :
    Path (C.comp (G.has_coprod A B).inl ((G.has_coprod A B).elim f g)) f :=
  (G.has_coprod A B).inl_elim f g

/-! ## Theorem 39: Giraud coequalizer -/

noncomputable def giraud_coeq {G : HTGiraud C} {A B : C.Obj}
    (f g : C.Hom A B) {X : C.Obj} (h : C.Hom B X)
    (p : Path (C.comp f h) (C.comp g h)) :
    Path (C.comp (G.has_coeq f g).proj ((G.has_coeq f g).elim h p)) h :=
  (G.has_coeq f g).proj_elim h p

/-! ## Theorem 40: Descent restriction coherence via congrArg -/

noncomputable def descent_restrict_coh {J : HTGTop C}
    {c : C.Obj} {S : HTSieve C c} {F : HTPSh C}
    (sc : HTSheafCond J F) (hS : J.cov c S)
    (dd : HTDescent (C := C) (J := J) (S := S) F)
    {d e : C.Obj} (f : C.Hom d c) (g : C.Hom e d) (hf : S.mem f) :
    Path (F.res g (F.res f (sheaf_descent sc hS dd)))
         (F.res g (dd.loc f hf)) :=
  congrArg (F.res g) (descended_restricts sc hS dd f hf)

/-! ## Theorem 41: Presheaf restriction identity -/

noncomputable def psh_res_id (F : HTPSh C) (A : C.Obj) (s : F.sec A) :
    Path (F.res (C.id A) s) s := F.res_id A s

/-! ## Theorem 42: Adjunction left triangle -/

noncomputable def adj_tri_L {C D : HTCat.{u, v}} {L : HTFun C D} {R : HTFun D C}
    (adj : HTAdj L R) (A : C.Obj) :
    Path (D.comp (L.map (adj.unit A)) (adj.counit (L.obj A)))
         (D.id (L.obj A)) := adj.tri_L A

/-! ## Theorem 43: Adjunction right triangle -/

noncomputable def adj_tri_R {C D : HTCat.{u, v}} {L : HTFun C D} {R : HTFun D C}
    (adj : HTAdj L R) (B : D.Obj) :
    Path (C.comp (adj.unit (R.obj B)) (R.map (adj.counit B)))
         (C.id (R.obj B)) := adj.tri_R B

/-! ## Theorem 44: Functor identity via map_id and congrArg -/

noncomputable def fun_id_congr {C D : HTCat.{u, v}} (F : HTFun C D)
    {A B : C.Obj} (f : C.Hom A B) :
    Path (D.comp (F.map f) (D.id (F.obj B)))
         (F.map f) :=
  D.id_right (F.map f)

end HigherToposPaths
end Path
end ComputationalPaths
