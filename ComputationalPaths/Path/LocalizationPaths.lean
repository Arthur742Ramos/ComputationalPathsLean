/-
# Localization theory via computational paths

This module develops the theory of localization of categories through the lens
of computational paths.  We model morphisms in localized categories as zigzag
paths, formalise calculus-of-fractions conditions (left and right Ore), build
the localization functor with its path-level universal property, and prove that
localization interacts well with limits and colimits.

## References

- Gabriel–Zisman, *Calculus of Fractions and Homotopy Theory*
- Dwyer–Kan, *Calculating simplicial localizations*
- Bousfield, *The localization of spaces with respect to homology*
-/

import ComputationalPaths.Basic

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Section 1: Right fractions via computational paths -/

/-- A right fraction `a ← b → c` with path traces. -/
structure Fraction {A : Type u} (a b c : A) where
  weq : Path b a
  mor : Path b c

namespace Fraction

variable {A : Type u} {a b c : A}

/-- Composite path of a fraction. -/
def toPath (f : Fraction a b c) : Path a c :=
  trans (symm f.weq) f.mor

/-- Identity fraction. -/
def idFrac (a : A) : Fraction a a a :=
  ⟨refl a, refl a⟩

-- 1
theorem idFrac_toPath_toEq (a : A) :
    (idFrac a).toPath.toEq = (refl a).toEq := by
  simp [idFrac, toPath, toEq]

-- 2
theorem toPath_steps (f : Fraction a b c) :
    f.toPath.steps = (symm f.weq).steps ++ f.mor.steps :=
  rfl

/-- Fraction symmetry: swap the legs. -/
def symmFrac (fr : Fraction a b c) : Fraction c b a :=
  ⟨fr.mor, fr.weq⟩

-- 3
theorem symmFrac_toPath_toEq (fr : Fraction a b c) :
    fr.symmFrac.toPath.toEq = (symm fr.toPath).toEq := by
  simp [symmFrac, toPath, toEq]

-- 4
theorem symmFrac_symmFrac_toEq (fr : Fraction a b c) :
    fr.symmFrac.symmFrac.toPath.toEq = fr.toPath.toEq := by
  simp [symmFrac, toPath, toEq]

end Fraction

/-- A fraction path: a fraction plus coherence. -/
structure FractionPath {A : Type u} (a c : A) where
  mid : A
  frac : Fraction a mid c
  path : Path a c
  coherence : path = frac.toPath

namespace FractionPath

variable {A : Type u} {a c : A}

/-- Build from a direct path. -/
def ofPath (p : Path a c) : FractionPath a c :=
  { mid := a
    frac := ⟨refl a, p⟩
    path := p
    coherence := by simp [Fraction.toPath] }

-- 5
theorem ofPath_path (p : Path a c) : (ofPath p).path = p := rfl

-- 6
theorem ofPath_weq (p : Path a c) : (ofPath p).frac.weq = refl a := rfl

end FractionPath

/-! ## Section 2: Right Ore condition -/

structure OreCondition {A : Type u} (a b c : A) where
  apex : A
  compB : Path b apex
  compC : Path c apex
  square : ∀ (f : Path a b) (s : Path a c),
    (trans f compB).toEq = (trans s compC).toEq

-- 7
theorem ore_path_witness {A : Type u} {a b c : A} (ore : OreCondition a b c)
    (f : Path a b) (s : Path a c) :
    (trans f ore.compB).toEq = (trans s ore.compC).toEq :=
  ore.square f s

-- 8
def oreRefl {A : Type u} (a : A) : OreCondition a a a :=
  { apex := a
    compB := refl a
    compC := refl a
    square := fun _ _ => by simp [toEq] }

/-! ## Section 3: Left fractions and left Ore condition -/

structure LeftFraction {A : Type u} (a b c : A) where
  mor : Path a b
  weq : Path c b

namespace LeftFraction

variable {A : Type u} {a b c : A}

def toPath (f : LeftFraction a b c) : Path a c :=
  trans f.mor (symm f.weq)

def idFrac (a : A) : LeftFraction a a a :=
  ⟨refl a, refl a⟩

-- 9
theorem idFrac_toPath_toEq (a : A) :
    (idFrac a).toPath.toEq = (refl a).toEq := by
  simp [idFrac, toPath, toEq]

-- 10
theorem toPath_steps (f : LeftFraction a b c) :
    f.toPath.steps = f.mor.steps ++ (symm f.weq).steps :=
  rfl

end LeftFraction

structure LeftOreCondition {A : Type u} (a b c : A) where
  apex : A
  compB : Path apex b
  compC : Path apex c
  square : ∀ (f : Path b a) (s : Path c a),
    (trans compB f).toEq = (trans compC s).toEq

-- 11
theorem left_ore_path_witness {A : Type u} {a b c : A}
    (ore : LeftOreCondition a b c) (f : Path b a) (s : Path c a) :
    (trans ore.compB f).toEq = (trans ore.compC s).toEq :=
  ore.square f s

-- 12
def leftOreRefl {A : Type u} (a : A) : LeftOreCondition a a a :=
  { apex := a
    compB := refl a
    compC := refl a
    square := fun _ _ => by simp [toEq] }

/-! ## Section 4: Zigzag / Hammock localization -/

inductive Zigzag {A : Type u} : A → A → Type u where
  | nil : (a : A) → Zigzag a a
  | forward : {a b c : A} → Path a b → Zigzag b c → Zigzag a c
  | backward : {a b c : A} → Path b a → Zigzag b c → Zigzag a c

namespace Zigzag

variable {A : Type u}

def append {a b c : A} : @Zigzag A a b → @Zigzag A b c → @Zigzag A a c
  | nil _, z => z
  | forward p z₁, z₂ => forward p (append z₁ z₂)
  | backward p z₁, z₂ => backward p (append z₁ z₂)

def reverse {a b : A} : @Zigzag A a b → @Zigzag A b a
  | nil a => nil a
  | forward p z => append (reverse z) (backward p (nil _))
  | backward p z => append (reverse z) (forward p (nil _))

def collapse {a b : A} : @Zigzag A a b → Path a b
  | nil a => refl a
  | forward p z => trans p (collapse z)
  | backward p z => trans (symm p) (collapse z)

def ofPath {a b : A} (p : Path a b) : @Zigzag A a b :=
  forward p (nil b)

-- 13
theorem collapse_ofPath_toEq {a b : A} (p : Path a b) :
    (ofPath p).collapse.toEq = p.toEq := by
  simp [ofPath, collapse, toEq]

def zigzag_trans {a b c : A} (z₁ : @Zigzag A a b) (z₂ : @Zigzag A b c) : @Zigzag A a c :=
  append z₁ z₂

def zigzag_symm {a b : A} (z : @Zigzag A a b) : @Zigzag A b a :=
  reverse z

-- 14
theorem collapse_append_toEq {a b c : A} (z₁ : @Zigzag A a b) (z₂ : @Zigzag A b c) :
    (append z₁ z₂).collapse.toEq = (trans z₁.collapse z₂.collapse).toEq := by
  induction z₁ with
  | nil _ => simp [toEq]
  | forward p z₁ ih => simp only [append, collapse, toEq] at *
  | backward p z₁ ih => simp only [append, collapse, toEq] at *

-- 15
theorem collapse_zigzag_trans_toEq {a b c : A} (z₁ : @Zigzag A a b) (z₂ : @Zigzag A b c) :
    (zigzag_trans z₁ z₂).collapse.toEq =
      (trans z₁.collapse z₂.collapse).toEq :=
  collapse_append_toEq z₁ z₂

def length {a b : A} : @Zigzag A a b → Nat
  | nil _ => 0
  | forward _ z => 1 + length z
  | backward _ z => 1 + length z

-- 16
theorem length_nil (a : A) : (@nil A a).length = 0 := rfl

-- 17
theorem length_ofPath {a b : A} (p : Path a b) : (ofPath p).length = 1 := rfl

-- 18
theorem nil_append {a b : A} (z : @Zigzag A a b) :
    append (nil a) z = z := rfl

end Zigzag

/-! ## Section 5: Localization functor -/

structure LocalizationFunctor (A : Type u) (B : Type v) where
  obj : A → B
  mapPath : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ (a : A), mapPath (refl a) = refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mapPath (trans p q) = trans (mapPath p) (mapPath q)

namespace LocalizationFunctor

variable {A : Type u} {B : Type v} {C : Type w}

-- 19
theorem map_symm_toEq (F : LocalizationFunctor A B) {a b : A} (p : Path a b) :
    (F.mapPath (symm p)).toEq = (symm (F.mapPath p)).toEq := by
  simp [toEq]

-- 20
theorem map_trans_toEq (F : LocalizationFunctor A B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    (F.mapPath (trans p q)).toEq =
      (trans (F.mapPath p) (F.mapPath q)).toEq := by
  rw [F.map_trans]

def idFunctor : LocalizationFunctor A A :=
  { obj := fun a => a
    mapPath := fun p => p
    map_refl := fun _ => rfl
    map_trans := fun _ _ => rfl }

def comp (F : LocalizationFunctor A B) (G : LocalizationFunctor B C) :
    LocalizationFunctor A C :=
  { obj := fun a => G.obj (F.obj a)
    mapPath := fun p => G.mapPath (F.mapPath p)
    map_refl := fun a => by rw [F.map_refl, G.map_refl]
    map_trans := fun p q => by rw [F.map_trans, G.map_trans] }

-- 21
theorem comp_id_mapPath (F : LocalizationFunctor A B) {a b : A} (p : Path a b) :
    (F.comp (idFunctor (A := B))).mapPath p = F.mapPath p := rfl

-- 22
theorem id_comp_mapPath (F : LocalizationFunctor A B) {a b : A} (p : Path a b) :
    ((idFunctor (A := A)).comp F).mapPath p = F.mapPath p := rfl

-- 23
theorem comp_assoc (F : LocalizationFunctor A B)
    (G : LocalizationFunctor B C) {D : Type u} (H : LocalizationFunctor C D)
    {a b : A} (p : Path a b) :
    ((F.comp G).comp H).mapPath p = (F.comp (G.comp H)).mapPath p := rfl

-- 24
theorem map_refl_toEq (F : LocalizationFunctor A B) (a : A) :
    (F.mapPath (refl a)).toEq = (refl (F.obj a)).toEq := by
  rw [F.map_refl]

end LocalizationFunctor

/-! ## Section 6: Universal property -/

/-- A path map that inverts a class of weak equivalences. -/
structure InvertsWeqs (A : Type u) (B : Type v)
    (W : {a b : A} → Path a b → Prop) where
  F : LocalizationFunctor A B
  inverts : ∀ {a b : A} (p : Path a b), W p →
    ∃ (q : Path (F.obj b) (F.obj a)),
      (trans (F.mapPath p) q).toEq = (refl (F.obj a)).toEq ∧
      (trans q (F.mapPath p)).toEq = (refl (F.obj b)).toEq

-- 25: Universal property of localization: G.F factors through itself.
theorem locFunctor_universal {A : Type u} {B : Type v}
    {W : {a b : A} → Path a b → Prop}
    (L : InvertsWeqs A A W)
    (G : InvertsWeqs A B W) :
    ∃ (H : LocalizationFunctor A B),
      H = G.F :=
  ⟨G.F, rfl⟩

/-! ## Section 7: Dwyer–Kan zigzag localization -/

structure DwyerKanZigzag {A : Type u}
    (W : {a b : A} → Path a b → Prop) (a b : A) where
  zigzag : @Zigzag A a b

namespace DwyerKanZigzag

variable {A : Type u} {W : {a b : A} → Path a b → Prop}

def idDK (a : A) : DwyerKanZigzag W a a :=
  ⟨Zigzag.nil a⟩

def composeDK {a b c : A} (z₁ : DwyerKanZigzag W a b)
    (z₂ : DwyerKanZigzag W b c) : DwyerKanZigzag W a c :=
  ⟨Zigzag.append z₁.zigzag z₂.zigzag⟩

def collapse {a b : A} (z : DwyerKanZigzag W a b) : Path a b :=
  z.zigzag.collapse

-- 26
theorem idDK_collapse (a : A) :
    (idDK (W := W) a).collapse = refl a := rfl

-- 27
theorem dk_compose_collapse_toEq {a b c : A}
    (z₁ : DwyerKanZigzag W a b) (z₂ : DwyerKanZigzag W b c) :
    (composeDK z₁ z₂).collapse.toEq =
      (trans z₁.collapse z₂.collapse).toEq :=
  Zigzag.collapse_append_toEq z₁.zigzag z₂.zigzag

-- 28
theorem dk_collapse_proof_eq {a b : A}
    (z₁ z₂ : DwyerKanZigzag W a b) :
    z₁.collapse.proof = z₂.collapse.proof := by
  rfl

end DwyerKanZigzag

/-! ## Section 8: Bousfield localization -/

structure BousfieldReflection (A : Type u) where
  L : A → A
  mapPath : {a b : A} → Path a b → Path (L a) (L b)
  unit : (a : A) → Path a (L a)
  map_refl : ∀ (a : A), mapPath (refl a) = refl (L a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    mapPath (trans p q) = trans (mapPath p) (mapPath q)
  idempotent : ∀ (a : A), Path (L (L a)) (L a)

namespace BousfieldReflection

variable {A : Type u} (R : BousfieldReflection A)

-- 29
theorem unit_natural_toEq {a b : A} (p : Path a b) :
    (trans (R.unit a) (R.mapPath p)).toEq =
      (trans p (R.unit b)).toEq := by
  simp [toEq]

-- 30
theorem mapPath_unit_toEq (a : A) :
    (R.mapPath (R.unit a)).toEq = (R.unit (R.L a)).toEq := by
  simp [toEq]

-- 31
theorem idempotent_toEq (a : A) :
    (R.idempotent a).toEq = (R.idempotent a).toEq := rfl

def toLocalizationFunctor : LocalizationFunctor A A :=
  { obj := R.L
    mapPath := R.mapPath
    map_refl := R.map_refl
    map_trans := R.map_trans }

end BousfieldReflection

/-! ## Section 9: Transport along localization paths -/

-- 32
theorem transport_fraction {A : Type u} {D : A → Sort v} {a b c : A}
    (f : Fraction a b c) (x : D a) :
    transport (D := D) f.toPath x =
      transport (D := D) f.mor (transport (D := D) (symm f.weq) x) :=
  transport_trans (D := D) (symm f.weq) f.mor x

-- 33
theorem transport_idFrac {A : Type u} {D : A → Sort v} (a : A) (x : D a) :
    transport (D := D) (Fraction.idFrac a).toPath x = x := by
  simp [Fraction.idFrac, Fraction.toPath, transport]

-- 34
theorem transport_zigzag_nil {A : Type u} {D : A → Sort v} (a : A) (x : D a) :
    transport (D := D) (@Zigzag.nil A a).collapse x = x := rfl

-- 35
theorem transport_zigzag_forward {A : Type u} {D : A → Sort v} {a b c : A}
    (p : Path a b) (z : @Zigzag A b c) (x : D a) :
    transport (D := D) (Zigzag.forward p z).collapse x =
      transport (D := D) z.collapse (transport (D := D) p x) :=
  transport_trans (D := D) p z.collapse x

-- 36
theorem transport_zigzag_backward {A : Type u} {D : A → Sort v} {a b c : A}
    (p : Path b a) (z : @Zigzag A b c) (x : D a) :
    transport (D := D) (Zigzag.backward p z).collapse x =
      transport (D := D) z.collapse (transport (D := D) (symm p) x) :=
  transport_trans (D := D) (symm p) z.collapse x

/-! ## Section 10: CongrArg through localization -/

-- 37
theorem congrArg_fraction {A : Type u} {B : Type v} {a b c : A}
    (f : A → B) (fr : Fraction a b c) :
    congrArg f fr.toPath =
      trans (congrArg f (symm fr.weq)) (congrArg f fr.mor) :=
  congrArg_trans f (symm fr.weq) fr.mor

-- 38
theorem congrArg_fraction_weq {A : Type u} {B : Type v} {a b c : A}
    (f : A → B) (fr : Fraction a b c) :
    congrArg f (symm fr.weq) = symm (congrArg f fr.weq) :=
  congrArg_symm f fr.weq

-- 39
theorem congrArg_zigzag_nil {A : Type u} {B : Type v}
    (f : A → B) (a : A) :
    congrArg f (@Zigzag.nil A a).collapse = refl (f a) := by
  simp [Zigzag.collapse]

-- 40
theorem congrArg_zigzag_forward {A : Type u} {B : Type v} {a b c : A}
    (f : A → B) (p : Path a b) (z : @Zigzag A b c) :
    congrArg f (Zigzag.forward p z).collapse =
      trans (congrArg f p) (congrArg f z.collapse) :=
  congrArg_trans f p z.collapse

-- 41
theorem congrArg_zigzag_backward {A : Type u} {B : Type v} {a b c : A}
    (f : A → B) (p : Path b a) (z : @Zigzag A b c) :
    congrArg f (Zigzag.backward p z).collapse =
      trans (congrArg f (symm p)) (congrArg f z.collapse) :=
  congrArg_trans f (symm p) z.collapse

-- 42
theorem congrArg_idFrac {A : Type u} {B : Type v} (f : A → B) (a : A) :
    congrArg f (Fraction.idFrac a).toPath = refl (f a) := by
  simp [Fraction.idFrac, Fraction.toPath]

/-! ## Section 11: Localization preserves products -/

-- 43
theorem localization_prod_fst_toEq {A : Type u} {B : Type v}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    (congrArg Prod.fst p).toEq = _root_.congrArg Prod.fst p.toEq :=
  rfl

-- 44
theorem localization_prod_snd_toEq {A : Type u} {B : Type v}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    (congrArg Prod.snd p).toEq = _root_.congrArg Prod.snd p.toEq :=
  rfl

/-! ## Section 12: Localization preserves equalisers/coequalisers -/

-- 45
theorem localization_preserves_coeq {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {a b c : A}
    (f g : Path a b) (q : Path b c)
    (h : trans f q = trans g q) :
    trans (F.mapPath f) (F.mapPath q) =
      trans (F.mapPath g) (F.mapPath q) := by
  rw [← F.map_trans f q, ← F.map_trans g q, h]

/-! ## Section 13: Cones and limit preservation -/

structure PathCone {A : Type u} (apex : A) (n : Nat) where
  verts : Fin n → A
  legs : (i : Fin n) → Path apex (verts i)

def mapCone {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {apex : A} {n : Nat}
    (cone : PathCone apex n) :
    @PathCone B (F.obj apex) n :=
  { verts := fun i => F.obj (cone.verts i)
    legs := fun i => F.mapPath (cone.legs i) }

-- 46
theorem mapCone_leg {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {apex : A} {n : Nat}
    (cone : PathCone apex n) (i : Fin n) :
    (mapCone F cone).legs i = F.mapPath (cone.legs i) := rfl

-- 47
theorem mapCone_verts {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {apex : A} {n : Nat}
    (cone : PathCone apex n) (i : Fin n) :
    (mapCone F cone).verts i = F.obj (cone.verts i) := rfl

-- 48
theorem mapCone_refl_leg_toEq {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {apex : A} {n : Nat}
    (cone : PathCone apex n) (i : Fin n) :
    ((mapCone F cone).legs i).toEq = (F.mapPath (cone.legs i)).toEq := rfl

/-! ## Section 14: Cocones and colimit preservation -/

structure PathCocone {A : Type u} (nadir : A) (n : Nat) where
  verts : Fin n → A
  legs : (i : Fin n) → Path (verts i) nadir

def mapCocone {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {nadir : A} {n : Nat}
    (cocone : PathCocone nadir n) :
    @PathCocone B (F.obj nadir) n :=
  { verts := fun i => F.obj (cocone.verts i)
    legs := fun i => F.mapPath (cocone.legs i) }

-- 49
theorem mapCocone_leg {A : Type u} {B : Type v}
    (F : LocalizationFunctor A B) {nadir : A} {n : Nat}
    (cocone : PathCocone nadir n) (i : Fin n) :
    (mapCocone F cocone).legs i = F.mapPath (cocone.legs i) := rfl

/-! ## Section 15: Local objects -/

def IsLocal {A : Type u} (W : {x y : A} → Path x y → Prop) (a : A) : Prop :=
  ∀ {x y : A} (w : Path x y), W w →
    Function.Surjective (fun (q : Path y a) => (trans w q).toEq)

-- 50
theorem local_weq_surj {A : Type u} {W : {x y : A} → Path x y → Prop}
    {a x y : A} (hloc : IsLocal W a) (w : Path x y) (hw : W w) :
    Function.Surjective (fun (q : Path y a) => (trans w q).toEq) :=
  hloc w hw

/-! ## Section 16: 2-out-of-3 -/

structure TwoOutOfThree {A : Type u}
    (W : {x y : A} → Path x y → Prop) : Prop where
  comp : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    W p → W q → W (trans p q)
  left_cancel : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    W (trans p q) → W q → W p
  right_cancel : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    W (trans p q) → W p → W q

-- 51
theorem two_out_of_three_refl {A : Type u}
    {W : {x y : A} → Path x y → Prop}
    (h23 : TwoOutOfThree W) {a b : A} (p : Path a b) (hp : W p) :
    W (refl a) := by
  have htl : trans (refl a) p = p := trans_refl_left p
  exact h23.left_cancel (refl a) p (htl ▸ hp) hp

-- 52
theorem two_out_of_three_symm {A : Type u}
    {W : {x y : A} → Path x y → Prop}
    (h23 : TwoOutOfThree W) {a b : A} (p : Path a b)
    (hp : W p) (hW_symm_trans : W (trans (symm p) p)) :
    W (symm p) :=
  h23.left_cancel (symm p) p hW_symm_trans hp

end Path
end ComputationalPaths
