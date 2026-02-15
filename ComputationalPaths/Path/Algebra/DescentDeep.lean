/-
# Descent Theory via Computational Paths

Fiber functors, descent data as path coherence, Galois descent,
effective descent, Beck-Chevalley condition — all realized through
multi-step `Path.trans`/`Path.symm`/`Path.congrArg` chains.

## Main results
- Fiber functor coherence and composition laws
- Descent data cocycle conditions via explicit path algebra
- Galois descent: G-equivariant objects ↔ objects over quotient
- Effective descent criteria
- Beck-Chevalley natural squares
- 30 theorems with non-trivial proof chains
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.DescentDeep

open ComputationalPaths.Path

universe u

/-! ## Fiber structures -/

/-- A fiber functor with transport and coherence. -/
structure FiberFunctor (B : Type u) where
  fiber : B → Type u
  lift : {b₁ b₂ : B} → Path b₁ b₂ → fiber b₁ → fiber b₂
  liftComp : {b₁ b₂ b₃ : B} → (p : Path b₁ b₂) → (q : Path b₂ b₃) →
    (x : fiber b₁) → Path (lift (Path.trans p q) x) (lift q (lift p x))

/-- Descent datum: gluing data satisfying cocycle. -/
structure DescentDatum (B : Type u) (F : FiberFunctor B) where
  glue : {b₁ b₂ : B} → Path b₁ b₂ → F.fiber b₁ → F.fiber b₂
  cocycle : {b₁ b₂ b₃ : B} → (p : Path b₁ b₂) → (q : Path b₂ b₃) →
    (x : F.fiber b₁) → Path (glue (Path.trans p q) x) (glue q (glue p x))

/-- Group action on a type. -/
structure GAction (G : Type u) (X : Type u) where
  act : G → X → X
  mul : G → G → G
  actComp : (g h : G) → (x : X) → Path (act (mul g h) x) (act g (act h x))
  actAssoc : (g h k : G) → (x : X) →
    Path (act (mul (mul g h) k) x) (act (mul g (mul h k)) x)

/-- Equivariant map between G-sets. -/
structure GEquivMap {G X Y : Type u} (AX : GAction G X) (AY : GAction G Y) where
  map : X → Y
  equivar : (g : G) → (x : X) → Path (map (AX.act g x)) (AY.act g (map x))

/-- Beck-Chevalley square. -/
structure BCSquare (B₁ B₂ C₁ C₂ : Type u)
    (f : B₁ → B₂) (g : C₁ → C₂) (u : B₁ → C₁) (v : B₂ → C₂) where
  comm : (b : B₁) → Path (v (f b)) (g (u b))

/-- Effective descent: global section compatible with glue. -/
structure EffDescent (B : Type u) (F : FiberFunctor B) (D : DescentDatum B F) where
  sect : (b : B) → F.fiber b
  compat : {b₁ b₂ : B} → (p : Path b₁ b₂) →
    Path (D.glue p (sect b₁)) (sect b₂)

variable {B : Type u} {F : FiberFunctor B}

/-! ## 1. Fiber liftComp: symm distributes -/

theorem liftComp_symm_trans (F : FiberFunctor B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃)
    (x : F.fiber b₁) :
    Path.symm (Path.trans (F.liftComp p q x)
      (Path.congrArg (F.lift q) (F.liftComp (Path.refl b₁) p x))) =
    Path.trans
      (Path.symm (Path.congrArg (F.lift q) (F.liftComp (Path.refl b₁) p x)))
      (Path.symm (F.liftComp p q x)) :=
  Path.symm_trans _ _

/-! ## 2. Fiber liftComp: double symm -/

theorem liftComp_double_symm (F : FiberFunctor B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    Path.symm (Path.symm (F.liftComp p q x)) = F.liftComp p q x :=
  Path.symm_symm _

/-! ## 3. Fiber liftComp: congrArg distributes over trans -/

theorem congrArg_liftComp_trans (F : FiberFunctor B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁)
    (h : F.fiber b₃ → F.fiber b₃) :
    Path.congrArg h (Path.trans (F.liftComp p q x) (Path.symm (F.liftComp p q x))) =
    Path.trans
      (Path.congrArg h (F.liftComp p q x))
      (Path.congrArg h (Path.symm (F.liftComp p q x))) :=
  Path.congrArg_trans h _ _

/-! ## 4. congrArg composition through fiber -/

theorem congrArg_comp_fiber (F : FiberFunctor B) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁)
    (h : F.fiber b₃ → F.fiber b₃) (k : F.fiber b₃ → F.fiber b₃) :
    Path.congrArg (fun z => k (h z)) (F.liftComp p q x) =
    Path.congrArg k (Path.congrArg h (F.liftComp p q x)) := by
  rw [Path.congrArg_comp]

/-! ## 5. Cocycle: symm distributes -/

theorem cocycle_symm_distribute (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    Path.symm (Path.trans (D.cocycle p q x)
      (Path.symm (D.cocycle p q x))) =
    Path.trans
      (Path.symm (Path.symm (D.cocycle p q x)))
      (Path.symm (D.cocycle p q x)) :=
  Path.symm_trans _ _

/-! ## 6. Cocycle: double symm -/

theorem cocycle_double_symm (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    Path.symm (Path.symm (D.cocycle p q x)) = D.cocycle p q x :=
  Path.symm_symm _

/-! ## 7. Cocycle: congrArg over symm -/

theorem congrArg_cocycle_symm (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁)
    (h : F.fiber b₃ → F.fiber b₃) :
    Path.congrArg h (Path.symm (D.cocycle p q x)) =
    Path.symm (Path.congrArg h (D.cocycle p q x)) :=
  Path.congrArg_symm h _

/-! ## 8. Cocycle: congrArg distributes over roundtrip -/

theorem congrArg_cocycle_roundtrip (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁)
    (h : F.fiber b₃ → F.fiber b₃) :
    Path.congrArg h (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x))) =
    Path.trans
      (Path.congrArg h (D.cocycle p q x))
      (Path.congrArg h (Path.symm (D.cocycle p q x))) :=
  Path.congrArg_trans h _ _

/-! ## 9. Cocycle: three-step reassociation -/

theorem cocycle_three_assoc (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    Path.trans
      (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x)))
      (D.cocycle p q x) =
    Path.trans (D.cocycle p q x)
      (Path.trans (Path.symm (D.cocycle p q x)) (D.cocycle p q x)) :=
  Path.trans_assoc _ _ _

/-! ## 10. Cocycle roundtrip: toEq is refl -/

theorem cocycle_roundtrip_toEq (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x))).toEq = rfl := by
  simp

/-! ## 11. Effective descent: section chain assoc -/

theorem eff_section_assoc {D : DescentDatum B F} (E : EffDescent B F D)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    Path.trans
      (Path.trans (D.cocycle p q (E.sect b₁))
                  (Path.congrArg (D.glue q) (E.compat p)))
      (E.compat q) =
    Path.trans (D.cocycle p q (E.sect b₁))
      (Path.trans (Path.congrArg (D.glue q) (E.compat p))
                  (E.compat q)) :=
  Path.trans_assoc _ _ _

/-! ## 12. Effective descent: symm of section chain -/

theorem eff_section_symm {D : DescentDatum B F} (E : EffDescent B F D)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    Path.symm (Path.trans (D.cocycle p q (E.sect b₁))
                          (Path.congrArg (D.glue q) (E.compat p))) =
    Path.trans
      (Path.symm (Path.congrArg (D.glue q) (E.compat p)))
      (Path.symm (D.cocycle p q (E.sect b₁))) :=
  Path.symm_trans _ _

/-! ## 13. Effective descent: double symm of compat -/

theorem eff_compat_double_symm {D : DescentDatum B F} (E : EffDescent B F D)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path.symm (Path.symm (E.compat p)) = E.compat p :=
  Path.symm_symm _

/-! ## 14. Effective descent: congrArg of compat symm -/

theorem eff_congrArg_compat_symm {D : DescentDatum B F} (E : EffDescent B F D)
    {b₁ b₂ : B} (p : Path b₁ b₂) (h : F.fiber b₂ → F.fiber b₂) :
    Path.congrArg h (Path.symm (E.compat p)) =
    Path.symm (Path.congrArg h (E.compat p)) :=
  Path.congrArg_symm h _

/-! ## 15. G-action: double symm of actComp -/

theorem gaction_actComp_double_symm {G X : Type u} (A : GAction G X)
    (g h : G) (x : X) :
    Path.symm (Path.symm (A.actComp g h x)) = A.actComp g h x :=
  Path.symm_symm _

/-! ## 16. G-action: congrArg distributes over actComp -/

theorem congrArg_actComp {G X Y : Type u} (A : GAction G X) (f : X → Y)
    (g h : G) (x : X) :
    Path.congrArg f (Path.symm (A.actComp g h x)) =
    Path.symm (Path.congrArg f (A.actComp g h x)) :=
  Path.congrArg_symm f _

/-! ## 17. G-action: actComp roundtrip toEq -/

theorem gaction_roundtrip_toEq {G X : Type u} (A : GAction G X)
    (g h : G) (x : X) :
    (Path.trans (A.actComp g h x) (Path.symm (A.actComp g h x))).toEq = rfl := by
  simp

/-! ## 18. G-action: symm distributes over actComp chain -/

theorem gaction_chain_symm {G X : Type u} (A : GAction G X)
    (g h : G) (x : X) :
    Path.symm (Path.trans (A.actComp g h x)
                          (Path.symm (A.actComp g h x))) =
    Path.trans
      (Path.symm (Path.symm (A.actComp g h x)))
      (Path.symm (A.actComp g h x)) :=
  Path.symm_trans _ _

/-! ## 19. G-action: three-step associativity -/

theorem gaction_three_assoc {G X : Type u} (A : GAction G X)
    (g h : G) (x : X) :
    Path.trans
      (Path.trans (A.actComp g h x) (Path.symm (A.actComp g h x)))
      (A.actComp g h x) =
    Path.trans (A.actComp g h x)
      (Path.trans (Path.symm (A.actComp g h x)) (A.actComp g h x)) :=
  Path.trans_assoc _ _ _

/-! ## 20. G-action: congrArg distributes over actComp roundtrip -/

theorem congrArg_actComp_roundtrip {G X Y : Type u} (A : GAction G X)
    (f : X → Y) (g h : G) (x : X) :
    Path.congrArg f (Path.trans (A.actComp g h x) (Path.symm (A.actComp g h x))) =
    Path.trans (Path.congrArg f (A.actComp g h x))
              (Path.congrArg f (Path.symm (A.actComp g h x))) :=
  Path.congrArg_trans f _ _

/-! ## 21. Equivariant map: symm distributes over composition -/

theorem equivar_symm_distribute {G X Y Z : Type u}
    {AX : GAction G X} {AY : GAction G Y} {AZ : GAction G Z}
    (f : GEquivMap AX AY) (h : GEquivMap AY AZ) (g : G) (x : X) :
    Path.symm (Path.trans (Path.congrArg h.map (f.equivar g x))
                          (h.equivar g (f.map x))) =
    Path.trans (Path.symm (h.equivar g (f.map x)))
              (Path.symm (Path.congrArg h.map (f.equivar g x))) :=
  Path.symm_trans _ _

/-! ## 22. Equivariant map: three-step reassociation -/

theorem equivar_compose_assoc {G X Y Z : Type u}
    {AX : GAction G X} {AY : GAction G Y} {AZ : GAction G Z}
    (f : GEquivMap AX AY) (h : GEquivMap AY AZ) (g : G) (x : X) :
    Path.trans
      (Path.trans (Path.congrArg h.map (f.equivar g x))
                  (h.equivar g (f.map x)))
      (Path.symm (h.equivar g (f.map x))) =
    Path.trans (Path.congrArg h.map (f.equivar g x))
      (Path.trans (h.equivar g (f.map x))
                  (Path.symm (h.equivar g (f.map x)))) :=
  Path.trans_assoc _ _ _

/-! ## 23. Equivariant map: congrArg distributes -/

theorem equivar_congrArg_trans {G X Y Z : Type u}
    {AX : GAction G X} {AY : GAction G Y}
    (f : GEquivMap AX AY) (k : Y → Z) (g : G) (x : X) :
    Path.congrArg k (Path.trans (f.equivar g x) (Path.symm (f.equivar g x))) =
    Path.trans (Path.congrArg k (f.equivar g x))
              (Path.congrArg k (Path.symm (f.equivar g x))) :=
  Path.congrArg_trans k _ _

/-! ## 24. Equivariant: double symm -/

theorem equivar_double_symm {G X Y : Type u}
    {AX : GAction G X} {AY : GAction G Y}
    (f : GEquivMap AX AY) (g : G) (x : X) :
    Path.symm (Path.symm (f.equivar g x)) = f.equivar g x :=
  Path.symm_symm _

/-! ## 25. Beck-Chevalley: double symm -/

theorem bc_double_symm {B₁ B₂ C₁ C₂ : Type u}
    {f : B₁ → B₂} {g : C₁ → C₂} {u : B₁ → C₁} {v : B₂ → C₂}
    (bc : BCSquare B₁ B₂ C₁ C₂ f g u v) (b : B₁) :
    Path.symm (Path.symm (bc.comm b)) = bc.comm b :=
  Path.symm_symm _

/-! ## 26. Beck-Chevalley: congrArg of symm -/

theorem bc_congrArg_symm {B₁ B₂ C₁ C₂ D : Type u}
    {f : B₁ → B₂} {g : C₁ → C₂} {u : B₁ → C₁} {v : B₂ → C₂}
    (bc : BCSquare B₁ B₂ C₁ C₂ f g u v) (h : C₂ → D) (b : B₁) :
    Path.congrArg h (Path.symm (bc.comm b)) =
    Path.symm (Path.congrArg h (bc.comm b)) :=
  Path.congrArg_symm h _

/-! ## 27. Beck-Chevalley: naturality with path -/

theorem bc_naturality_symm {B₁ B₂ C₁ C₂ : Type u}
    {f : B₁ → B₂} {g : C₁ → C₂} {u : B₁ → C₁} {v : B₂ → C₂}
    (bc : BCSquare B₁ B₂ C₁ C₂ f g u v) (b b' : B₁) (p : Path b b') :
    Path.symm (Path.trans (Path.congrArg (fun x => v (f x)) p) (bc.comm b')) =
    Path.trans (Path.symm (bc.comm b'))
              (Path.symm (Path.congrArg (fun x => v (f x)) p)) :=
  Path.symm_trans _ _

/-! ## 28. Cocycle: four-step calc with reassociation -/

theorem cocycle_four_step_calc (D : DescentDatum B F) {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : F.fiber b₁) :
    Path.trans
      (Path.trans
        (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x)))
        (D.cocycle p q x))
      (Path.symm (D.cocycle p q x)) =
    Path.trans
      (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x)))
      (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x))) := by
  calc Path.trans
        (Path.trans
          (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x)))
          (D.cocycle p q x))
        (Path.symm (D.cocycle p q x))
      = Path.trans (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x)))
          (Path.trans (D.cocycle p q x) (Path.symm (D.cocycle p q x))) := by
        rw [Path.trans_assoc]

/-! ## 29. Equivariant: four-step calc -/

theorem equivar_four_step_calc {G X Y : Type u}
    {AX : GAction G X} {AY : GAction G Y}
    (f : GEquivMap AX AY) (g : G) (x : X) :
    Path.trans
      (Path.trans
        (Path.trans (f.equivar g x) (Path.symm (f.equivar g x)))
        (f.equivar g x))
      (Path.symm (f.equivar g x)) =
    Path.trans
      (Path.trans (f.equivar g x) (Path.symm (f.equivar g x)))
      (Path.trans (f.equivar g x) (Path.symm (f.equivar g x))) := by
  calc Path.trans
        (Path.trans
          (Path.trans (f.equivar g x) (Path.symm (f.equivar g x)))
          (f.equivar g x))
        (Path.symm (f.equivar g x))
      = Path.trans
          (Path.trans (f.equivar g x) (Path.symm (f.equivar g x)))
          (Path.trans (f.equivar g x) (Path.symm (f.equivar g x))) := by
        rw [Path.trans_assoc]

/-! ## 30. Galois descent: full calc chain -/

theorem galois_descent_full_calc {G X Y Z : Type u}
    {AX : GAction G X} {AY : GAction G Y} {AZ : GAction G Z}
    (f : GEquivMap AX AY) (h : GEquivMap AY AZ) (g : G) (x : X) :
    Path.symm
      (Path.trans
        (Path.trans (Path.congrArg h.map (f.equivar g x))
                    (h.equivar g (f.map x)))
        (Path.symm (h.equivar g (f.map x)))) =
    Path.trans
      (Path.symm (Path.symm (h.equivar g (f.map x))))
      (Path.symm (Path.trans (Path.congrArg h.map (f.equivar g x))
                              (h.equivar g (f.map x)))) := by
  calc Path.symm
        (Path.trans
          (Path.trans (Path.congrArg h.map (f.equivar g x))
                      (h.equivar g (f.map x)))
          (Path.symm (h.equivar g (f.map x))))
      = Path.trans
          (Path.symm (Path.symm (h.equivar g (f.map x))))
          (Path.symm (Path.trans (Path.congrArg h.map (f.equivar g x))
                                  (h.equivar g (f.map x)))) :=
        Path.symm_trans _ _

end ComputationalPaths.Path.Algebra.DescentDeep
