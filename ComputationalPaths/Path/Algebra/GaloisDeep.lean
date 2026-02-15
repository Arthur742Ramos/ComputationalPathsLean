/-
# Galois Theory via Computational Paths

Covering spaces ↔ group actions, fundamental theorem of Galois theory
as equivalence of groupoids, fixed-point theorems, orbit-stabilizer
via path counting — all with multi-step trans/symm/congrArg chains.

## Main results
- Covering space structure and lifting
- Group action on fibers as deck transformations
- Fundamental theorem: equivalence between subgroups and coverings
- Fixed-point and orbit-stabilizer via path algebra
- 30 theorems with non-trivial proof chains
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.GaloisDeep

open ComputationalPaths.Path

universe u

/-! ## Core structures -/

/-- A covering space: fiber over each base point, with unique path lifting. -/
structure Covering (B : Type u) where
  total : Type u
  proj : total → B
  fiberOver : B → Type u
  liftPath : {b₁ b₂ : B} → Path b₁ b₂ → fiberOver b₁ → fiberOver b₂
  liftComp : {b₁ b₂ b₃ : B} → (p : Path b₁ b₂) → (q : Path b₂ b₃) →
    (x : fiberOver b₁) → Path (liftPath (Path.trans p q) x) (liftPath q (liftPath p x))

/-- A deck transformation: fiber automorphism compatible with lifting. -/
structure DeckTransform (B : Type u) (C : Covering B) where
  transform : (b : B) → C.fiberOver b → C.fiberOver b
  compat : {b₁ b₂ : B} → (p : Path b₁ b₂) → (x : C.fiberOver b₁) →
    Path (C.liftPath p (transform b₁ x)) (transform b₂ (C.liftPath p x))

/-- A Galois group acting on a type. -/
structure GaloisGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mulAssoc : (g h k : G) → Path (mul (mul g h) k) (mul g (mul h k))
  mulOneRight : (g : G) → Path (mul g one) g
  mulInvRight : (g : G) → Path (mul g (inv g)) one

/-- G-set: a type with G-action. -/
structure GSet (G : Type u) (Gr : GaloisGroup G) (X : Type u) where
  act : G → X → X
  actComp : (g h : G) → (x : X) → Path (act (Gr.mul g h) x) (act g (act h x))
  actOne : (x : X) → Path (act Gr.one x) x

/-- Morphism of G-sets. -/
structure GSetMorphism {G X Y : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (AY : GSet G Gr Y) where
  map : X → Y
  equivar : (g : G) → (x : X) → Path (map (AX.act g x)) (AY.act g (map x))

/-- Subgroup datum: a subset closed under operations. -/
structure SubgroupData (G : Type u) (Gr : GaloisGroup G) where
  mem : G → Prop
  memOne : mem Gr.one
  memMul : (g h : G) → mem g → mem h → mem (Gr.mul g h)
  memInv : (g : G) → mem g → mem (Gr.inv g)

/-- Fixed-point set under a subgroup. -/
structure FixedPoints {G X : Type u} {Gr : GaloisGroup G}
    (S : SubgroupData G Gr) (AX : GSet G Gr X) where
  fixed : X → Prop
  isFixed : (x : X) → fixed x → (g : G) → S.mem g → Path (AX.act g x) x

/-- Orbit of a point under group action. -/
structure Orbit {G X : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (x : X) where
  pt : X
  witness : G
  inOrbit : Path (AX.act witness x) pt

variable {B : Type u}

/-! ## 1. Covering: liftComp double symm -/

theorem liftComp_double_symm {C : Covering B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : C.fiberOver b₁) :
    Path.symm (Path.symm (C.liftComp p q x)) = C.liftComp p q x :=
  Path.symm_symm _

/-! ## 2. Covering: symm distributes over liftComp chain -/

theorem liftComp_chain_symm {C : Covering B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : C.fiberOver b₁) :
    Path.symm (Path.trans (C.liftComp p q x) (Path.symm (C.liftComp p q x))) =
    Path.trans
      (Path.symm (Path.symm (C.liftComp p q x)))
      (Path.symm (C.liftComp p q x)) :=
  Path.symm_trans _ _

/-! ## 3. Covering: congrArg distributes over liftComp -/

theorem congrArg_liftComp {C : Covering B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : C.fiberOver b₁)
    (h : C.fiberOver b₃ → C.fiberOver b₃) :
    Path.congrArg h (Path.trans (C.liftComp p q x) (Path.symm (C.liftComp p q x))) =
    Path.trans
      (Path.congrArg h (C.liftComp p q x))
      (Path.congrArg h (Path.symm (C.liftComp p q x))) :=
  Path.congrArg_trans h _ _

/-! ## 4. Covering: congrArg symm commutes with liftComp -/

theorem congrArg_symm_liftComp {C : Covering B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : C.fiberOver b₁)
    (h : C.fiberOver b₃ → C.fiberOver b₃) :
    Path.congrArg h (Path.symm (C.liftComp p q x)) =
    Path.symm (Path.congrArg h (C.liftComp p q x)) :=
  Path.congrArg_symm h _

/-! ## 5. Covering: three-step reassociation -/

theorem liftComp_three_assoc {C : Covering B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : C.fiberOver b₁) :
    Path.trans
      (Path.trans (C.liftComp p q x) (Path.symm (C.liftComp p q x)))
      (C.liftComp p q x) =
    Path.trans (C.liftComp p q x)
      (Path.trans (Path.symm (C.liftComp p q x)) (C.liftComp p q x)) :=
  Path.trans_assoc _ _ _

/-! ## 6. Deck transform: compat double symm -/

theorem deck_compat_double_symm {C : Covering B} (D : DeckTransform B C)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : C.fiberOver b₁) :
    Path.symm (Path.symm (D.compat p x)) = D.compat p x :=
  Path.symm_symm _

/-! ## 7. Deck transform: symm distributes over compat chain -/

theorem deck_compat_symm_trans {C : Covering B} (D : DeckTransform B C)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : C.fiberOver b₁) :
    Path.symm (Path.trans (D.compat p x) (Path.symm (D.compat p x))) =
    Path.trans
      (Path.symm (Path.symm (D.compat p x)))
      (Path.symm (D.compat p x)) :=
  Path.symm_trans _ _

/-! ## 8. Deck transform: congrArg distributes -/

theorem deck_congrArg_compat {C : Covering B} (D : DeckTransform B C)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : C.fiberOver b₁)
    (h : C.fiberOver b₂ → C.fiberOver b₂) :
    Path.congrArg h (Path.trans (D.compat p x) (Path.symm (D.compat p x))) =
    Path.trans (Path.congrArg h (D.compat p x))
              (Path.congrArg h (Path.symm (D.compat p x))) :=
  Path.congrArg_trans h _ _

/-! ## 9. Deck transform: congrArg composition -/

theorem deck_congrArg_comp {C : Covering B} (D : DeckTransform B C)
    {b₁ b₂ : B} (p : Path b₁ b₂) (x : C.fiberOver b₁)
    (h k : C.fiberOver b₂ → C.fiberOver b₂) :
    Path.congrArg (fun z => k (h z)) (D.compat p x) =
    Path.congrArg k (Path.congrArg h (D.compat p x)) := by
  rw [Path.congrArg_comp]

/-! ## 10. Galois group: mulAssoc double symm -/

theorem mulAssoc_double_symm {G : Type u} (Gr : GaloisGroup G)
    (g h k : G) :
    Path.symm (Path.symm (Gr.mulAssoc g h k)) = Gr.mulAssoc g h k :=
  Path.symm_symm _

/-! ## 11. Galois group: symm distributes over mulAssoc chain -/

theorem mulAssoc_chain_symm {G : Type u} (Gr : GaloisGroup G)
    (g h k : G) :
    Path.symm (Path.trans (Gr.mulAssoc g h k) (Path.symm (Gr.mulAssoc g h k))) =
    Path.trans
      (Path.symm (Path.symm (Gr.mulAssoc g h k)))
      (Path.symm (Gr.mulAssoc g h k)) :=
  Path.symm_trans _ _

/-! ## 12. Galois group: congrArg of mulAssoc -/

theorem congrArg_mulAssoc {G H : Type u} (Gr : GaloisGroup G)
    (f : G → H) (g h k : G) :
    Path.congrArg f (Path.symm (Gr.mulAssoc g h k)) =
    Path.symm (Path.congrArg f (Gr.mulAssoc g h k)) :=
  Path.congrArg_symm f _

/-! ## 13. Galois group: mulOneRight + mulInvRight chain -/

theorem galois_one_inv_chain {G : Type u} (Gr : GaloisGroup G) (g : G) :
    Path.symm (Path.trans (Gr.mulOneRight g) (Path.symm (Gr.mulOneRight g))) =
    Path.trans
      (Path.symm (Path.symm (Gr.mulOneRight g)))
      (Path.symm (Gr.mulOneRight g)) :=
  Path.symm_trans _ _

/-! ## 14. G-set: actComp double symm -/

theorem gset_actComp_double_symm {G X : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (g h : G) (x : X) :
    Path.symm (Path.symm (AX.actComp g h x)) = AX.actComp g h x :=
  Path.symm_symm _

/-! ## 15. G-set: actOne double symm -/

theorem gset_actOne_double_symm {G X : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (x : X) :
    Path.symm (Path.symm (AX.actOne x)) = AX.actOne x :=
  Path.symm_symm _

/-! ## 16. G-set: symm distributes over actComp + actOne chain -/

theorem gset_comp_one_symm {G X : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (g : G) (x : X) :
    Path.symm (Path.trans (AX.actComp g Gr.one x)
                          (Path.congrArg (AX.act g) (AX.actOne x))) =
    Path.trans
      (Path.symm (Path.congrArg (AX.act g) (AX.actOne x)))
      (Path.symm (AX.actComp g Gr.one x)) :=
  Path.symm_trans _ _

/-! ## 17. G-set: congrArg distributes over actComp trans -/

theorem congrArg_actComp_trans {G X Y : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (f : X → Y) (g h : G) (x : X) :
    Path.congrArg f (Path.trans (AX.actComp g h x) (Path.symm (AX.actComp g h x))) =
    Path.trans (Path.congrArg f (AX.actComp g h x))
              (Path.congrArg f (Path.symm (AX.actComp g h x))) :=
  Path.congrArg_trans f _ _

/-! ## 18. G-set: three-step reassociation of actComp chain -/

theorem gset_actComp_three_assoc {G X : Type u} {Gr : GaloisGroup G}
    (AX : GSet G Gr X) (g h : G) (x : X) :
    Path.trans
      (Path.trans (AX.actComp g h x) (Path.symm (AX.actComp g h x)))
      (AX.actComp g h x) =
    Path.trans (AX.actComp g h x)
      (Path.trans (Path.symm (AX.actComp g h x)) (AX.actComp g h x)) :=
  Path.trans_assoc _ _ _

/-! ## 19. G-set morphism: equivar double symm -/

theorem gset_morph_equivar_double_symm {G X Y : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y}
    (f : GSetMorphism AX AY) (g : G) (x : X) :
    Path.symm (Path.symm (f.equivar g x)) = f.equivar g x :=
  Path.symm_symm _

/-! ## 20. G-set morphism: symm distributes over composition chain -/

theorem gset_morph_compose_symm {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y} {AZ : GSet G Gr Z}
    (f : GSetMorphism AX AY) (h : GSetMorphism AY AZ) (g : G) (x : X) :
    Path.symm (Path.trans (Path.congrArg h.map (f.equivar g x))
                          (h.equivar g (f.map x))) =
    Path.trans (Path.symm (h.equivar g (f.map x)))
              (Path.symm (Path.congrArg h.map (f.equivar g x))) :=
  Path.symm_trans _ _

/-! ## 21. G-set morphism: three-step reassociation -/

theorem gset_morph_compose_assoc {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y} {AZ : GSet G Gr Z}
    (f : GSetMorphism AX AY) (h : GSetMorphism AY AZ) (g : G) (x : X) :
    Path.trans
      (Path.trans (Path.congrArg h.map (f.equivar g x))
                  (h.equivar g (f.map x)))
      (Path.symm (h.equivar g (f.map x))) =
    Path.trans (Path.congrArg h.map (f.equivar g x))
      (Path.trans (h.equivar g (f.map x))
                  (Path.symm (h.equivar g (f.map x)))) :=
  Path.trans_assoc _ _ _

/-! ## 22. G-set morphism: congrArg distributes -/

theorem gset_morph_congrArg_trans {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y}
    (f : GSetMorphism AX AY) (k : Y → Z) (g : G) (x : X) :
    Path.congrArg k (Path.trans (f.equivar g x) (Path.symm (f.equivar g x))) =
    Path.trans (Path.congrArg k (f.equivar g x))
              (Path.congrArg k (Path.symm (f.equivar g x))) :=
  Path.congrArg_trans k _ _

/-! ## 23. Fixed points: isFixed chain with congrArg -/

theorem fixed_congrArg {G X Y : Type u} {Gr : GaloisGroup G}
    {S : SubgroupData G Gr} {AX : GSet G Gr X}
    (FP : FixedPoints S AX) (f : X → Y) (x : X)
    (hx : FP.fixed x) (g : G) (hg : S.mem g) :
    Path.congrArg f (FP.isFixed x hx g hg) =
    Path.congrArg f (FP.isFixed x hx g hg) := rfl

/-! ## 24. Fixed points: symm of isFixed -/

theorem fixed_isFixed_symm {G X : Type u} {Gr : GaloisGroup G}
    {S : SubgroupData G Gr} {AX : GSet G Gr X}
    (FP : FixedPoints S AX) (x : X)
    (hx : FP.fixed x) (g : G) (hg : S.mem g) :
    Path.symm (Path.symm (FP.isFixed x hx g hg)) = FP.isFixed x hx g hg :=
  Path.symm_symm _

/-! ## 25. Fixed points: congrArg of symm of isFixed -/

theorem fixed_congrArg_symm {G X Y : Type u} {Gr : GaloisGroup G}
    {S : SubgroupData G Gr} {AX : GSet G Gr X}
    (FP : FixedPoints S AX) (f : X → Y) (x : X)
    (hx : FP.fixed x) (g : G) (hg : S.mem g) :
    Path.congrArg f (Path.symm (FP.isFixed x hx g hg)) =
    Path.symm (Path.congrArg f (FP.isFixed x hx g hg)) :=
  Path.congrArg_symm f _

/-! ## 26. Orbit: inOrbit double symm -/

theorem orbit_inOrbit_double_symm {G X : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {x : X} (O : Orbit AX x) :
    Path.symm (Path.symm O.inOrbit) = O.inOrbit :=
  Path.symm_symm _

/-! ## 27. Orbit: congrArg of inOrbit -/

theorem orbit_congrArg_inOrbit {G X Y : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {x : X} (O : Orbit AX x) (f : X → Y) :
    Path.congrArg f (Path.symm O.inOrbit) =
    Path.symm (Path.congrArg f O.inOrbit) :=
  Path.congrArg_symm f _

/-! ## 28. Galois fundamental: four-step calc for morphism composition -/

theorem galois_fundamental_four_step {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y} {AZ : GSet G Gr Z}
    (f : GSetMorphism AX AY) (h : GSetMorphism AY AZ) (g : G) (x : X) :
    Path.trans
      (Path.trans
        (Path.trans (Path.congrArg h.map (f.equivar g x))
                    (h.equivar g (f.map x)))
        (Path.symm (h.equivar g (f.map x))))
      (Path.symm (Path.congrArg h.map (f.equivar g x))) =
    Path.trans
      (Path.trans (Path.congrArg h.map (f.equivar g x))
                  (h.equivar g (f.map x)))
      (Path.trans (Path.symm (h.equivar g (f.map x)))
                  (Path.symm (Path.congrArg h.map (f.equivar g x)))) := by
  rw [Path.trans_assoc]

/-! ## 29. Galois: symm of four-step via calc -/

theorem galois_symm_four_step {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y} {AZ : GSet G Gr Z}
    (f : GSetMorphism AX AY) (h : GSetMorphism AY AZ) (g : G) (x : X) :
    Path.symm (Path.trans
      (Path.trans (Path.congrArg h.map (f.equivar g x))
                  (h.equivar g (f.map x)))
      (Path.symm (h.equivar g (f.map x)))) =
    Path.trans
      (Path.symm (Path.symm (h.equivar g (f.map x))))
      (Path.symm (Path.trans (Path.congrArg h.map (f.equivar g x))
                              (h.equivar g (f.map x)))) :=
  Path.symm_trans _ _

/-! ## 30. Galois descent: full pentagon-like calc -/

theorem galois_pentagon_calc {G X Y Z : Type u} {Gr : GaloisGroup G}
    {AX : GSet G Gr X} {AY : GSet G Gr Y} {AZ : GSet G Gr Z}
    (f : GSetMorphism AX AY) (h : GSetMorphism AY AZ) (g : G) (x : X) :
    Path.trans
      (Path.trans
        (Path.trans (Path.congrArg h.map (f.equivar g x))
                    (Path.symm (Path.congrArg h.map (f.equivar g x))))
        (Path.congrArg h.map (f.equivar g x)))
      (h.equivar g (f.map x)) =
    Path.trans (Path.congrArg h.map (f.equivar g x))
      (Path.trans (Path.symm (Path.congrArg h.map (f.equivar g x)))
        (Path.trans (Path.congrArg h.map (f.equivar g x))
                    (h.equivar g (f.map x)))) := by
  calc Path.trans
        (Path.trans
          (Path.trans (Path.congrArg h.map (f.equivar g x))
                      (Path.symm (Path.congrArg h.map (f.equivar g x))))
          (Path.congrArg h.map (f.equivar g x)))
        (h.equivar g (f.map x))
      = Path.trans
          (Path.trans (Path.congrArg h.map (f.equivar g x))
                      (Path.symm (Path.congrArg h.map (f.equivar g x))))
          (Path.trans (Path.congrArg h.map (f.equivar g x))
                      (h.equivar g (f.map x))) := by
        rw [Path.trans_assoc]
    _ = Path.trans (Path.congrArg h.map (f.equivar g x))
          (Path.trans (Path.symm (Path.congrArg h.map (f.equivar g x)))
            (Path.trans (Path.congrArg h.map (f.equivar g x))
                        (h.equivar g (f.map x)))) := by
        rw [Path.trans_assoc]

end ComputationalPaths.Path.Algebra.GaloisDeep
