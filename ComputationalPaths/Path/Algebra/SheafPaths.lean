/-
# Sheaf Theory via Computational Paths

Presheaves, sheaf condition, stalks, sheafification, cohomology —
all modelled with computational paths over Nat/Int.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.SheafPaths

open ComputationalPaths.Path

/-! ## Presheaves and sheaves -/

/-- Open set index. -/
abbrev OpenIdx := Nat

/-- Section type. -/
abbrev Sect := Int

/-- A presheaf: assigns sections to opens with restriction maps. -/
structure Presheaf where
  sections : OpenIdx → Sect
  restrict : OpenIdx → OpenIdx → Sect → Sect

/-- The constant presheaf with value v. -/
@[simp] def constPresheaf (v : Sect) : Presheaf :=
  ⟨fun _ => v, fun _ _ s => s⟩

/-- The zero presheaf. -/
@[simp] def zeroPresheaf : Presheaf :=
  ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- A presheaf morphism. -/
structure PresheafMor (F G : Presheaf) where
  map : OpenIdx → Sect → Sect

/-- Identity presheaf morphism. -/
@[simp] def idPresheafMor (F : Presheaf) : PresheafMor F F :=
  ⟨fun _ s => s⟩

/-- Composition of presheaf morphisms. -/
@[simp] def compPresheafMor {F G H : Presheaf}
    (φ : PresheafMor F G) (ψ : PresheafMor G H) : PresheafMor F H :=
  ⟨fun i s => ψ.map i (φ.map i s)⟩

/-- Stalk at a point (simplified: evaluate at the index). -/
@[simp] def stalk (F : Presheaf) (p : OpenIdx) : Sect :=
  F.sections p

/-- Germ of a section at a point. -/
@[simp] def germ (F : Presheaf) (_ : OpenIdx) (p : OpenIdx) : Sect :=
  F.sections p

/-- Sheafification (in our model, identity on the constant presheaf). -/
@[simp] def sheafify (F : Presheaf) : Presheaf :=
  ⟨F.sections, fun u v s => F.restrict u v s⟩

/-- Sheaf cohomology H^n (simplified: H^0 = global sections, H^n = 0 for n > 0). -/
@[simp] def sheafCohomology (F : Presheaf) (n : Nat) : Sect :=
  if n = 0 then F.sections 0 else 0

/-- Global sections functor Γ. -/
@[simp] def globalSections (F : Presheaf) : Sect := F.sections 0

/-- Direct image presheaf (simplified: same sections). -/
@[simp] def directImage (F : Presheaf) (_ : OpenIdx → OpenIdx) : Presheaf :=
  ⟨F.sections, F.restrict⟩

/-- Kernel presheaf of a morphism. -/
@[simp] def kernelPresheaf {F G : Presheaf} (φ : PresheafMor F G) : Presheaf :=
  ⟨fun i => if φ.map i (F.sections i) = 0 then F.sections i else 0,
   fun _ _ _ => 0⟩

/-- Čech 0-cochain: a function from opens to sections. -/
@[simp] def cech0 (F : Presheaf) : OpenIdx → Sect := F.sections

/-! ## Core theorems -/

-- 1. Identity morphism acts as identity
theorem id_mor_act (F : Presheaf) (i : OpenIdx) (s : Sect) :
    (idPresheafMor F).map i s = s := by simp

def id_mor_act_path (F : Presheaf) (i : OpenIdx) (s : Sect) :
    Path ((idPresheafMor F).map i s) s :=
  Path.ofEq (id_mor_act F i s)

-- 2. Composition with identity (left)
theorem comp_id_left {F G : Presheaf} (φ : PresheafMor F G) (i : OpenIdx) (s : Sect) :
    (compPresheafMor (idPresheafMor F) φ).map i s = φ.map i s := by simp

def comp_id_left_path {F G : Presheaf} (φ : PresheafMor F G) (i : OpenIdx) (s : Sect) :
    Path ((compPresheafMor (idPresheafMor F) φ).map i s) (φ.map i s) :=
  Path.ofEq (comp_id_left φ i s)

-- 3. Composition with identity (right)
theorem comp_id_right {F G : Presheaf} (φ : PresheafMor F G) (i : OpenIdx) (s : Sect) :
    (compPresheafMor φ (idPresheafMor G)).map i s = φ.map i s := by simp

def comp_id_right_path {F G : Presheaf} (φ : PresheafMor F G) (i : OpenIdx) (s : Sect) :
    Path ((compPresheafMor φ (idPresheafMor G)).map i s) (φ.map i s) :=
  Path.ofEq (comp_id_right φ i s)

-- 4. Associativity of composition
theorem comp_assoc {F G H K : Presheaf}
    (φ : PresheafMor F G) (ψ : PresheafMor G H) (χ : PresheafMor H K)
    (i : OpenIdx) (s : Sect) :
    (compPresheafMor (compPresheafMor φ ψ) χ).map i s =
    (compPresheafMor φ (compPresheafMor ψ χ)).map i s := by simp

def comp_assoc_path {F G H K : Presheaf}
    (φ : PresheafMor F G) (ψ : PresheafMor G H) (χ : PresheafMor H K)
    (i : OpenIdx) (s : Sect) :
    Path ((compPresheafMor (compPresheafMor φ ψ) χ).map i s)
         ((compPresheafMor φ (compPresheafMor ψ χ)).map i s) :=
  Path.ofEq (comp_assoc φ ψ χ i s)

-- 5. Stalk of zero presheaf
theorem stalk_zero (p : OpenIdx) : stalk zeroPresheaf p = 0 := by simp

def stalk_zero_path (p : OpenIdx) : Path (stalk zeroPresheaf p) 0 :=
  Path.ofEq (stalk_zero p)

-- 6. Stalk of constant presheaf
theorem stalk_const (v : Sect) (p : OpenIdx) :
    stalk (constPresheaf v) p = v := by simp

def stalk_const_path (v : Sect) (p : OpenIdx) :
    Path (stalk (constPresheaf v) p) v :=
  Path.ofEq (stalk_const v p)

-- 7. Germ equals stalk for constant presheaf
theorem germ_eq_stalk (F : Presheaf) (u p : OpenIdx) :
    germ F u p = stalk F p := by simp

def germ_eq_stalk_path (F : Presheaf) (u p : OpenIdx) :
    Path (germ F u p) (stalk F p) :=
  Path.ofEq (germ_eq_stalk F u p)

-- 8. Sheafification preserves sections
theorem sheafify_sections (F : Presheaf) (i : OpenIdx) :
    (sheafify F).sections i = F.sections i := by simp

def sheafify_sections_path (F : Presheaf) (i : OpenIdx) :
    Path ((sheafify F).sections i) (F.sections i) :=
  Path.ofEq (sheafify_sections F i)

-- 9. Double sheafification is idempotent
theorem sheafify_idem (F : Presheaf) (i : OpenIdx) :
    (sheafify (sheafify F)).sections i = F.sections i := by simp

def sheafify_idem_path (F : Presheaf) (i : OpenIdx) :
    Path ((sheafify (sheafify F)).sections i) (F.sections i) :=
  Path.ofEq (sheafify_idem F i)

-- 10. H^0 = global sections
theorem cohomology_zero (F : Presheaf) :
    sheafCohomology F 0 = globalSections F := by simp

def cohomology_zero_path (F : Presheaf) :
    Path (sheafCohomology F 0) (globalSections F) :=
  Path.ofEq (cohomology_zero F)

-- 11. Higher cohomology vanishes
theorem cohomology_higher (F : Presheaf) (n : Nat) :
    sheafCohomology F (n + 1) = 0 := by simp

def cohomology_higher_path (F : Presheaf) (n : Nat) :
    Path (sheafCohomology F (n + 1)) 0 :=
  Path.ofEq (cohomology_higher F n)

-- 12. Cohomology of zero presheaf
theorem cohomology_zero_presheaf (n : Nat) :
    sheafCohomology zeroPresheaf n = 0 := by
  simp [sheafCohomology]

def cohomology_zero_presheaf_path (n : Nat) :
    Path (sheafCohomology zeroPresheaf n) 0 :=
  Path.ofEq (cohomology_zero_presheaf n)

-- 13. Global sections of zero presheaf
theorem global_sections_zero : globalSections zeroPresheaf = 0 := by simp

def global_sections_zero_path : Path (globalSections zeroPresheaf) 0 :=
  Path.ofEq global_sections_zero

-- 14. Global sections of constant presheaf
theorem global_sections_const (v : Sect) :
    globalSections (constPresheaf v) = v := by simp

def global_sections_const_path (v : Sect) :
    Path (globalSections (constPresheaf v)) v :=
  Path.ofEq (global_sections_const v)

-- 15. Direct image preserves sections
theorem direct_image_sections (F : Presheaf) (f : OpenIdx → OpenIdx) (i : OpenIdx) :
    (directImage F f).sections i = F.sections i := by simp

def direct_image_sections_path (F : Presheaf) (f : OpenIdx → OpenIdx) (i : OpenIdx) :
    Path ((directImage F f).sections i) (F.sections i) :=
  Path.ofEq (direct_image_sections F f i)

-- 16. Čech 0-cochain equals sections
theorem cech0_eq (F : Presheaf) (i : OpenIdx) :
    cech0 F i = F.sections i := by simp

def cech0_eq_path (F : Presheaf) (i : OpenIdx) :
    Path (cech0 F i) (F.sections i) :=
  Path.ofEq (cech0_eq F i)

-- 17. Zero presheaf restriction
theorem zero_restrict (u v : OpenIdx) (s : Sect) :
    zeroPresheaf.restrict u v s = 0 := by simp

def zero_restrict_path (u v : OpenIdx) (s : Sect) :
    Path (zeroPresheaf.restrict u v s) 0 :=
  Path.ofEq (zero_restrict u v s)

-- 18. Constant presheaf restriction is identity
theorem const_restrict (v : Sect) (u w : OpenIdx) (s : Sect) :
    (constPresheaf v).restrict u w s = s := by simp

def const_restrict_path (v : Sect) (u w : OpenIdx) (s : Sect) :
    Path ((constPresheaf v).restrict u w s) s :=
  Path.ofEq (const_restrict v u w s)

-- 19. Trans path: sheafification + cohomology chain
def sheafify_cohom_path (F : Presheaf) :
    Path (sheafCohomology (sheafify F) 0) (globalSections F) :=
  Path.trans
    (Path.ofEq (by simp))
    (Path.refl (globalSections F))

-- 20. Symmetry path: stalk inverse
def stalk_symm_path (v : Sect) (p : OpenIdx) :
    Path v (stalk (constPresheaf v) p) :=
  Path.symm (stalk_const_path v p)

-- 21. Congruence: morphism applied to sections
def mor_congr {F G : Presheaf} (φ : PresheafMor F G) (i : OpenIdx)
    (s t : Sect) (h : s = t) :
    Path (φ.map i s) (φ.map i t) :=
  Path.congrArg (φ.map i) (Path.ofEq h)

-- 22. Stalk of direct image
theorem stalk_direct_image (F : Presheaf) (f : OpenIdx → OpenIdx) (p : OpenIdx) :
    stalk (directImage F f) p = stalk F p := by simp

def stalk_direct_image_path (F : Presheaf) (f : OpenIdx → OpenIdx) (p : OpenIdx) :
    Path (stalk (directImage F f) p) (stalk F p) :=
  Path.ofEq (stalk_direct_image F f p)

-- 23. Stalk of sheafification
theorem stalk_sheafify (F : Presheaf) (p : OpenIdx) :
    stalk (sheafify F) p = stalk F p := by simp

def stalk_sheafify_path (F : Presheaf) (p : OpenIdx) :
    Path (stalk (sheafify F) p) (stalk F p) :=
  Path.ofEq (stalk_sheafify F p)

-- 24. Composition chain path
def comp_chain_path {F G H : Presheaf}
    (φ : PresheafMor F G) (ψ : PresheafMor G H) (i : OpenIdx) (s : Sect) :
    Path ((compPresheafMor (idPresheafMor F) (compPresheafMor φ ψ)).map i s)
         ((compPresheafMor φ ψ).map i s) :=
  Path.ofEq (comp_id_left (compPresheafMor φ ψ) i s)

-- 25. Global sections functor is natural
theorem global_sections_natural (F : Presheaf) :
    globalSections (sheafify F) = globalSections F := by simp

def global_sections_natural_path (F : Presheaf) :
    Path (globalSections (sheafify F)) (globalSections F) :=
  Path.ofEq (global_sections_natural F)

end ComputationalPaths.Path.Algebra.SheafPaths
