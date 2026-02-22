import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Adjunction.PathInfrastructure

/-!
# Adjunction coherence paths — derived identities

This module extends the basic adjunction infrastructure with derived
coherence identities: mate correspondence, adjunction composition,
identity adjunction, and interaction with Path operations.
-/

namespace ComputationalPaths
namespace Adjunction

open Path
open AdjunctionData

universe u

variable {C : Type u} {D : Type u}
variable {F : C → D} {G : D → C}

-- ============================================================
-- § 1. Mate correspondence
-- ============================================================

/-- Left mate: given F ⊣ G and f : F x → y, produce x → G y. -/
noncomputable def leftMate (adj : AdjunctionData C D F G)
    {x : C} {y : D} (f : Path (F x) y) : Path x (G y) :=
  Path.trans (adj.unit x) (Path.congrArg G f)

/-- Right mate: given F ⊣ G and g : x → G y, produce F x → y. -/
noncomputable def rightMate (adj : AdjunctionData C D F G)
    {x : C} {y : D} (g : Path x (G y)) : Path (F x) y :=
  Path.trans (Path.congrArg F g) (adj.counit y)

/-- Left mate of refl ↝ unit. -/
noncomputable def leftMate_refl (adj : AdjunctionData C D F G) (x : C) :
    RwEq (leftMate adj (Path.refl (F x)))
         (adj.unit x) :=
  rweq_trans
    (rweq_trans_congr_right (adj.unit x) (rweq_congrArg_refl G (F x)))
    (rweq_cmpA_refl_right (adj.unit x))

/-- Right mate of refl ↝ counit. -/
noncomputable def rightMate_refl (adj : AdjunctionData C D F G) (y : D) :
    RwEq (rightMate adj (Path.refl (G y)))
         (adj.counit y) :=
  rweq_trans
    (rweq_trans_congr_left (adj.counit y) (rweq_congrArg_refl F (G y)))
    (rweq_cmpA_refl_left (adj.counit y))

-- ============================================================
-- § 2. Mate respects RwEq
-- ============================================================

/-- Left mate respects rewrite equivalence. -/
noncomputable def leftMate_rweq (adj : AdjunctionData C D F G)
    {x : C} {y : D} {f f' : Path (F x) y}
    (h : RwEq f f') :
    RwEq (leftMate adj f) (leftMate adj f') :=
  rweq_trans_congr_right (adj.unit x) (rweq_congrArg_of_rweq G h)

/-- Right mate respects rewrite equivalence. -/
noncomputable def rightMate_rweq (adj : AdjunctionData C D F G)
    {x : C} {y : D} {g g' : Path x (G y)}
    (h : RwEq g g') :
    RwEq (rightMate adj g) (rightMate adj g') :=
  rweq_trans_congr_left (adj.counit y) (rweq_congrArg_of_rweq F h)

-- ============================================================
-- § 3. Mate composition
-- ============================================================

/-- Left mate of a composite: leftMate(f · g) ↝ leftMate(f) · G(g). -/
noncomputable def leftMate_trans (adj : AdjunctionData C D F G)
    {x : C} {y z : D} (f : Path (F x) y) (g : Path y z) :
    RwEq (leftMate adj (Path.trans f g))
         (Path.trans (leftMate adj f) (Path.congrArg G g)) :=
  rweq_trans
    (rweq_trans_congr_right (adj.unit x) (rweq_congrArg_trans G f g))
    (rweq_symm (rweq_of_step (Step.trans_assoc
      (adj.unit x) (Path.congrArg G f) (Path.congrArg G g))))

/-- Right mate of a composite: rightMate(g · h) ↝ F(g) · rightMate(h). -/
noncomputable def rightMate_trans (adj : AdjunctionData C D F G)
    {x y : C} {z : D} (g : Path x y) (h : Path y (G z)) :
    RwEq (rightMate adj (Path.trans g h))
         (Path.trans (Path.congrArg F g) (rightMate adj h)) :=
  rweq_trans
    (rweq_trans_congr_left (adj.counit z) (rweq_congrArg_trans F g h))
    (rweq_of_step (Step.trans_assoc
      (Path.congrArg F g) (Path.congrArg F h) (adj.counit z)))

-- ============================================================
-- § 4. Zigzag via mates
-- ============================================================

/-- The left triangle is the right mate of the unit. -/
noncomputable def leftTriangle_via_mate (adj : AdjunctionData C D F G) (x : C) :
    RwEq (rightMate adj (adj.unit x))
         (adj.leftTriangle x) :=
  rweq_refl _

/-- The right triangle is the left mate of the counit. -/
noncomputable def rightTriangle_via_mate (adj : AdjunctionData C D F G) (y : D) :
    RwEq (leftMate adj (adj.counit y))
         (adj.rightTriangle y) :=
  rweq_refl _

-- ============================================================
-- § 5. Identity adjunction
-- ============================================================

/-- The identity adjunction: id ⊣ id. -/
noncomputable def idAdjunction (C : Type u) : AdjunctionData C C id id where
  unit := fun x => Path.refl x
  counit := fun x => Path.refl x

/-- The identity adjunction satisfies zigzag trivially. -/
noncomputable def idZigzag (C : Type u) : Zigzag (idAdjunction C) where
  left := by
    intro x
    show RwEq (Path.trans (Path.refl x) (Path.refl x)) (Path.refl x)
    exact rweq_cmpA_refl_left (Path.refl x)
  right := by
    intro y
    show RwEq (Path.trans (Path.refl y) (Path.refl y)) (Path.refl y)
    exact rweq_cmpA_refl_left (Path.refl y)

-- ============================================================
-- § 6. Adjunction composition
-- ============================================================

/-- Given F ⊣ G and F' ⊣ G', the composite F'F ⊣ GG'. -/
noncomputable def compAdjunction
    {E : Type u}
    {F' : D → E} {G' : E → D}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData D E F' G') :
    AdjunctionData C E (fun x => F' (F x)) (fun z => G (G' z)) where
  unit := fun x =>
    Path.trans (adj₁.unit x) (Path.congrArg G (adj₂.unit (F x)))
  counit := fun z =>
    Path.trans (Path.congrArg F' (adj₁.counit (G' z))) (adj₂.counit z)

/-- The composite unit decomposes. -/
noncomputable def compUnit_decompose
    {E : Type u}
    {F' : D → E} {G' : E → D}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData D E F' G')
    (x : C) :
    RwEq ((compAdjunction adj₁ adj₂).unit x)
         (Path.trans (adj₁.unit x) (Path.congrArg G (adj₂.unit (F x)))) :=
  rweq_refl _

/-- The composite counit decomposes. -/
noncomputable def compCounit_decompose
    {E : Type u}
    {F' : D → E} {G' : E → D}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData D E F' G')
    (z : E) :
    RwEq ((compAdjunction adj₁ adj₂).counit z)
         (Path.trans (Path.congrArg F' (adj₁.counit (G' z))) (adj₂.counit z)) :=
  rweq_refl _

-- ============================================================
-- § 7. Adjunction from zigzag data
-- ============================================================

/-- An equivalence (inverse pair) gives zigzag identities. -/
noncomputable def adjOfEquiv
    (η : ∀ x : C, Path x (G (F x)))
    (ε : ∀ y : D, Path (F (G y)) y)
    (hε : ∀ x : C, RwEq (Path.trans (Path.congrArg F (η x)) (ε (F x)))
                         (Path.refl (F x)))
    (hη : ∀ y : D, RwEq (Path.trans (η (G y)) (Path.congrArg G (ε y)))
                         (Path.refl (G y))) :
    AdjunctionData.Zigzag ⟨η, ε⟩ where
  left := hε
  right := hη

-- ============================================================
-- § 8. Mate interaction with refl (additional)
-- ============================================================

/-- Left mate of a path that starts and ends at F x. -/
noncomputable def leftMate_loop (adj : AdjunctionData C D F G)
    (x : C) (f : Path (F x) (F x)) :
    RwEq (leftMate adj f)
         (Path.trans (adj.unit x) (Path.congrArg G f)) :=
  rweq_refl _

/-- Right mate of a path that starts and ends at G y. -/
noncomputable def rightMate_loop (adj : AdjunctionData C D F G)
    (y : D) (g : Path (G y) (G y)) :
    RwEq (rightMate adj g)
         (Path.trans (Path.congrArg F g) (adj.counit y)) :=
  rweq_refl _

/-- Left mate of refl followed by trans reduces. -/
noncomputable def leftMate_refl_trans (adj : AdjunctionData C D F G)
    {x : C} {y : D} (f : Path (F x) y) :
    RwEq (leftMate adj (Path.trans (Path.refl (F x)) f))
         (leftMate adj f) :=
  leftMate_rweq adj (rweq_cmpA_refl_left f)

/-- Right mate of refl followed by trans reduces. -/
noncomputable def rightMate_refl_trans (adj : AdjunctionData C D F G)
    {x : C} {y : D} (g : Path x (G y)) :
    RwEq (rightMate adj (Path.trans (Path.refl x) g))
         (rightMate adj g) :=
  rightMate_rweq adj (rweq_cmpA_refl_left g)

/-- Left mate of trans followed by refl reduces. -/
noncomputable def leftMate_trans_refl (adj : AdjunctionData C D F G)
    {x : C} {y : D} (f : Path (F x) y) :
    RwEq (leftMate adj (Path.trans f (Path.refl y)))
         (leftMate adj f) :=
  leftMate_rweq adj (rweq_cmpA_refl_right f)

/-- Right mate of trans followed by refl reduces. -/
noncomputable def rightMate_trans_refl (adj : AdjunctionData C D F G)
    {x : C} {y : D} (g : Path x (G y)) :
    RwEq (rightMate adj (Path.trans g (Path.refl (G y))))
         (rightMate adj g) :=
  rightMate_rweq adj (rweq_cmpA_refl_right g)

-- ============================================================
-- § 10. Uniqueness of adjoints
-- ============================================================

/-- Comparison path G y → G' y when both are right adjoint to F. -/
noncomputable def adjoint_unique_path
    {G' : D → C}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData C D F G')
    (y : D) : Path (G y) (G' y) :=
  leftMate adj₂ (adj₁.counit y)

-- ============================================================
-- § 11. CongrArg distributes over mates
-- ============================================================

/-- CongrArg commutes with left mate construction. -/
noncomputable def congrArg_leftMate
    (h : C → C)
    (adj : AdjunctionData C D F G)
    {x : C} {y : D} (f : Path (F x) y) :
    RwEq (Path.congrArg h (leftMate adj f))
         (Path.trans (Path.congrArg h (adj.unit x))
                     (Path.congrArg h (Path.congrArg G f))) :=
  rweq_congrArg_trans h (adj.unit x) (Path.congrArg G f)

/-- CongrArg commutes with right mate construction. -/
noncomputable def congrArg_rightMate
    (h : D → D)
    (adj : AdjunctionData C D F G)
    {x : C} {y : D} (g : Path x (G y)) :
    RwEq (Path.congrArg h (rightMate adj g))
         (Path.trans (Path.congrArg h (Path.congrArg F g))
                     (Path.congrArg h (adj.counit y))) :=
  rweq_congrArg_trans h (Path.congrArg F g) (adj.counit y)

-- ============================================================
-- § 12. Composite adjunction identity/associativity
-- ============================================================

/-- The composite unit path with trailing refl reduces. -/
noncomputable def compUnit_refl_right
    {E : Type u} {F' : D → E} {G' : E → D}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData D E F' G')
    (x : C) :
    RwEq (Path.trans ((compAdjunction adj₁ adj₂).unit x)
                     (Path.refl (G (G' (F' (F x))))))
         ((compAdjunction adj₁ adj₂).unit x) :=
  rweq_cmpA_refl_right _

/-- The composite counit path with leading refl reduces. -/
noncomputable def compCounit_refl_left
    {E : Type u} {F' : D → E} {G' : E → D}
    (adj₁ : AdjunctionData C D F G)
    (adj₂ : AdjunctionData D E F' G')
    (z : E) :
    RwEq (Path.trans (Path.refl (F' (F (G (G' z)))))
                     ((compAdjunction adj₁ adj₂).counit z))
         ((compAdjunction adj₁ adj₂).counit z) :=
  rweq_cmpA_refl_left _

-- ============================================================
-- § 13. Left/right triangle as trans+cancel
-- ============================================================

/-- Left triangle expanded. -/
noncomputable def leftTriangle_expand (adj : AdjunctionData C D F G) (x : C) :
    RwEq (adj.leftTriangle x)
         (Path.trans (Path.congrArg F (adj.unit x)) (adj.counit (F x))) :=
  rweq_refl _

/-- Right triangle expanded. -/
noncomputable def rightTriangle_expand (adj : AdjunctionData C D F G) (y : D) :
    RwEq (adj.rightTriangle y)
         (Path.trans (adj.unit (G y)) (Path.congrArg G (adj.counit y))) :=
  rweq_refl _

/-- Zigzag left: leftTriangle ↝ refl. -/
noncomputable def zigzag_left_rweq
    (adj : AdjunctionData C D F G) (zig : Zigzag adj) (x : C) :
    RwEq (adj.leftTriangle x) (Path.refl (F x)) :=
  zig.left x

/-- Zigzag right: rightTriangle ↝ refl. -/
noncomputable def zigzag_right_rweq
    (adj : AdjunctionData C D F G) (zig : Zigzag adj) (y : D) :
    RwEq (adj.rightTriangle y) (Path.refl (G y)) :=
  zig.right y

-- ============================================================
-- § 14. Unit/counit inversion
-- ============================================================

/-- Given zigzag, counit(Fx) ↝ symm(congrArg F (unit x)). -/
noncomputable def counit_is_inv_of_F_unit
    (adj : AdjunctionData C D F G) (zig : Zigzag adj) (x : C) :
    RwEq (adj.counit (F x))
         (Path.symm (Path.congrArg F (adj.unit x))) :=
  -- From zig.left x : congrArg F (unit x) · counit(Fx) ↝ refl
  -- Derive: counit(Fx) ↝ (congrArg F (unit x))⁻¹
  rweq_trans
    (rweq_symm (rweq_cmpA_refl_left (adj.counit (F x))))
    (rweq_trans
      (rweq_trans_congr_left (adj.counit (F x))
        (rweq_symm (rweq_cmpA_inv_left (Path.congrArg F (adj.unit x)))))
      (rweq_trans
        (rweq_of_step (Step.trans_assoc
          (Path.symm (Path.congrArg F (adj.unit x)))
          (Path.congrArg F (adj.unit x))
          (adj.counit (F x))))
        (rweq_trans
          (rweq_trans_congr_right (Path.symm (Path.congrArg F (adj.unit x)))
            (zig.left x))
          (rweq_cmpA_refl_right (Path.symm (Path.congrArg F (adj.unit x)))))))

/-- Given zigzag, unit(Gy) ↝ symm(congrArg G (counit y)). -/
noncomputable def unit_is_inv_of_G_counit
    (adj : AdjunctionData C D F G) (zig : Zigzag adj) (y : D) :
    RwEq (adj.unit (G y))
         (Path.symm (Path.congrArg G (adj.counit y))) :=
  rweq_trans
    (rweq_symm (rweq_cmpA_refl_right (adj.unit (G y))))
    (rweq_trans
      (rweq_trans_congr_right (adj.unit (G y))
        (rweq_symm (rweq_cmpA_inv_right (Path.congrArg G (adj.counit y)))))
      (rweq_trans
        (rweq_symm (rweq_of_step (Step.trans_assoc
          (adj.unit (G y))
          (Path.congrArg G (adj.counit y))
          (Path.symm (Path.congrArg G (adj.counit y))))))
        (rweq_trans
          (rweq_trans_congr_left (Path.symm (Path.congrArg G (adj.counit y)))
            (zig.right y))
          (rweq_cmpA_refl_left (Path.symm (Path.congrArg G (adj.counit y)))))))

end Adjunction
end ComputationalPaths
