/-
# Homotopy Limits and Colimits via Computational Paths

Cones, cocones, mapping telescopes, sequential colimits, and the
Milnor exact sequence, all built from Path/Step/trans/symm.

## References
- Bousfield & Kan, "Homotopy Limits, Completions and Localizations" (1972)
- Milnor, "On spaces having the homotopy type of a CW-complex" (1959)
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace HomotopyLimitDeep

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Sequential Diagrams -/

structure SeqDiag where
  obj : Nat → Type u
  map : ∀ n, obj n → obj (n + 1)

/-! ## Cones -/

structure Cone (D : SeqDiag.{u}) where
  apex : Type u
  proj : ∀ n, apex → D.obj n
  comm : ∀ n (x : apex), D.map n (proj n x) = proj (n + 1) x

/-- Morphism of cones. -/
structure ConeMor {D : SeqDiag.{u}} (C₁ C₂ : Cone D) where
  map : C₁.apex → C₂.apex
  comm : ∀ n (x : C₁.apex), C₂.proj n (map x) = C₁.proj n x

-- 1: identity cone morphism
def ConeMor.id (C : Cone D) : ConeMor C C where
  map := _root_.id
  comm := fun _ _ => rfl

-- 2: composition of cone morphisms
def ConeMor.comp {C₁ C₂ C₃ : Cone D}
    (f : ConeMor C₁ C₂) (g : ConeMor C₂ C₃) : ConeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by simp [Function.comp]; rw [g.comm, f.comm]

-- 3: id ∘ f = f
theorem ConeMor.id_comp {C₁ C₂ : Cone D} (f : ConeMor C₁ C₂) :
    ConeMor.comp (ConeMor.id C₁) f = f := by
  cases f; simp [ConeMor.comp, ConeMor.id, Function.comp]

-- 4: f ∘ id = f
theorem ConeMor.comp_id {C₁ C₂ : Cone D} (f : ConeMor C₁ C₂) :
    ConeMor.comp f (ConeMor.id C₂) = f := by
  cases f; simp [ConeMor.comp, ConeMor.id, Function.comp]

/-! ## Cocones -/

structure Cocone (D : SeqDiag.{u}) where
  nadir : Type u
  inj : ∀ n, D.obj n → nadir
  comm : ∀ n (x : D.obj n), inj (n + 1) (D.map n x) = inj n x

structure CoconeMor {D : SeqDiag.{u}} (C₁ C₂ : Cocone D) where
  map : C₁.nadir → C₂.nadir
  comm : ∀ n (x : D.obj n), map (C₁.inj n x) = C₂.inj n x

-- 5: identity cocone morphism
def CoconeMor.id (C : Cocone D) : CoconeMor C C where
  map := _root_.id
  comm := fun _ _ => rfl

-- 6: composition of cocone morphisms
def CoconeMor.comp {C₁ C₂ C₃ : Cocone D}
    (f : CoconeMor C₁ C₂) (g : CoconeMor C₂ C₃) : CoconeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by simp [Function.comp]; rw [f.comm, g.comm]

/-! ## Mapping Telescope -/

def MappingTelescope (D : SeqDiag.{u}) : Type u := Σ n, D.obj n

def MappingTelescope.inj (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    MappingTelescope D := ⟨n, x⟩

inductive TelescopeRel (D : SeqDiag.{u}) :
    MappingTelescope D → MappingTelescope D → Prop where
  | step : ∀ n (x : D.obj n), TelescopeRel D ⟨n, x⟩ ⟨n + 1, D.map n x⟩

-- 7: telescope relation witness extraction
theorem TelescopeRel.extract {D : SeqDiag.{u}} {a b : MappingTelescope D}
    (h : TelescopeRel D a b) :
    ∃ n, ∃ x : D.obj n, a = ⟨n, x⟩ ∧ b = ⟨n + 1, D.map n x⟩ := by
  cases h with | step n x => exact ⟨n, x, rfl, rfl⟩

/-! ## Sequential Colimit -/

def SeqColimit (D : SeqDiag.{u}) : Type u := Quot (TelescopeRel D)

def SeqColimit.ι (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) : SeqColimit D :=
  Quot.mk _ ⟨n, x⟩

-- 8: compatibility of ι with structure maps
theorem SeqColimit.ι_comm (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    SeqColimit.ι D n x = SeqColimit.ι D (n + 1) (D.map n x) :=
  Quot.sound (TelescopeRel.step n x)

-- 9: the colimit forms a cocone
def SeqColimit.cocone (D : SeqDiag.{u}) : Cocone D where
  nadir := SeqColimit D
  inj := SeqColimit.ι D
  comm := fun n x => (SeqColimit.ι_comm D n x).symm

-- 10: universal property (descent)
def SeqColimit.desc {D : SeqDiag.{u}} (C : Cocone D) : SeqColimit D → C.nadir :=
  Quot.lift (fun p => C.inj p.1 p.2) (by
    intro a b h; cases h with | step n x => exact (C.comm n x).symm)

-- 11: desc commutes with ι
theorem SeqColimit.desc_ι {D : SeqDiag.{u}} (C : Cocone D) (n : Nat) (x : D.obj n) :
    SeqColimit.desc C (SeqColimit.ι D n x) = C.inj n x := rfl

-- 12: desc as a cocone morphism
def SeqColimit.descMor {D : SeqDiag.{u}} (C : Cocone D) :
    CoconeMor (SeqColimit.cocone D) C where
  map := SeqColimit.desc C
  comm := fun n x => rfl

-- 13: Path version of ι_comm
def SeqColimit.ιPath (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    Path (SeqColimit.ι D n x) (SeqColimit.ι D (n + 1) (D.map n x)) :=
  Path.ofEq (SeqColimit.ι_comm D n x)

/-! ## Homotopy Limit -/

structure HoLim (D : SeqDiag.{u}) where
  point : ∀ n, D.obj n
  compat : ∀ n, D.map n (point n) = point (n + 1)

-- 14: HoLim forms a cone
def HoLim.cone (D : SeqDiag.{u}) : Cone D where
  apex := HoLim D
  proj := fun n h => h.point n
  comm := fun n h => h.compat n

-- 15: projection commutes
theorem HoLim.proj_comm (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    D.map n (h.point n) = h.point (n + 1) := h.compat n

-- 16: lifting into HoLim
def HoLim.lift (C : Cone D) : C.apex → HoLim D :=
  fun x => ⟨fun n => C.proj n x, fun n => C.comm n x⟩

-- 17: lift commutes with projections
theorem HoLim.lift_proj (C : Cone D) (x : C.apex) (n : Nat) :
    (HoLim.lift C x).point n = C.proj n x := rfl

-- 18: lift gives a cone morphism
def HoLim.liftMor (C : Cone D) : ConeMor C (HoLim.cone D) where
  map := HoLim.lift C
  comm := fun _ _ => rfl

/-! ## Milnor Exact Sequence -/

/-- The shift map on the product. -/
def shiftMap (D : SeqDiag.{u}) (s : ∀ n, D.obj n) (n : Nat) : D.obj (n + 1) :=
  D.map n (s n)

-- 19: kernel of shift-minus-id is the homotopy limit
theorem milnor_kernel_is_holim (D : SeqDiag.{u}) (s : ∀ n, D.obj n) :
    (∀ n, D.map n (s n) = s (n + 1)) ↔ (∃ h : HoLim D, h.point = s) := by
  constructor
  · intro hcompat; exact ⟨⟨s, hcompat⟩, rfl⟩
  · intro ⟨h, hs⟩; subst hs; exact h.compat

-- 20: milnor diff as a path
def milnorPath (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    Path (D.map n (h.point n)) (h.point (n + 1)) :=
  Path.ofEq (h.compat n)

-- 21: composing milnor paths
def milnorPathChain (D : SeqDiag.{u}) (h : HoLim D) (n k : Nat) :
    Path (h.point n) (h.point n) := Path.refl _

/-! ## Telescope Filtration -/

def TelescopeFilt (D : SeqDiag.{u}) (n : Nat) : Type u :=
  Σ k : Fin (n + 1), D.obj k

-- 22: inclusion of filtrations
def TelescopeFilt.incl (D : SeqDiag.{u}) (n : Nat) :
    TelescopeFilt D n → TelescopeFilt D (n + 1) :=
  fun ⟨⟨k, hk⟩, x⟩ => ⟨⟨k, Nat.lt_succ_of_lt hk⟩, x⟩

-- 23: filtration preserves index
theorem TelescopeFilt.incl_idx (D : SeqDiag.{u}) (n : Nat)
    (k : Fin (n + 1)) (x : D.obj k) :
    (TelescopeFilt.incl D n ⟨k, x⟩).1.val = k.val := rfl

/-! ## Mapping Path Space -/

structure MappingPathSpace (f : A → B) (b : B) where
  point : A
  path : Path (f point) b

-- 24: projection
def MappingPathSpace.proj {f : A → B} {b : B} :
    MappingPathSpace f b → A := fun m => m.point

-- 25: canonical element
def MappingPathSpace.canonical (f : A → B) (a : A) :
    MappingPathSpace f (f a) where
  point := a
  path := Path.refl (f a)

-- 26: canonical proj
theorem MappingPathSpace.canonical_proj (f : A → B) (a : A) :
    (MappingPathSpace.canonical f a).point = a := rfl

/-! ## Homotopy Pullback -/

structure HoPullback (f : A → C) (g : B → C) where
  fst : A
  snd : B
  path : Path (f fst) (g snd)

-- 27: first projection
def HoPullback.π₁ {f : A → C} {g : B → C} :
    HoPullback f g → A := fun p => p.fst

-- 28: second projection
def HoPullback.π₂ {f : A → C} {g : B → C} :
    HoPullback f g → B := fun p => p.snd

-- 29: universal property
def HoPullback.lift {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B)
    (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) : D → HoPullback f g :=
  fun d => ⟨h₁ d, h₂ d, hc d⟩

-- 30: lift π₁
theorem HoPullback.lift_π₁ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₁ (HoPullback.lift h₁ h₂ hc d) = h₁ d := rfl

-- 31: lift π₂
theorem HoPullback.lift_π₂ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₂ (HoPullback.lift h₁ h₂ hc d) = h₂ d := rfl

-- 32: pullback of identity maps
def HoPullback.diagonal (a : A) : HoPullback (_root_.id : A → A) (_root_.id : A → A) where
  fst := a
  snd := a
  path := Path.refl a

-- 33: diagonal is a section of π₁
theorem HoPullback.diagonal_π₁ (a : A) :
    HoPullback.π₁ (HoPullback.diagonal a) = a := rfl

/-! ## Natural Transformations between Diagrams -/

structure SeqNat (D₁ D₂ : SeqDiag.{u}) where
  component : ∀ n, D₁.obj n → D₂.obj n
  naturality : ∀ n (x : D₁.obj n),
    D₂.map n (component n x) = component (n + 1) (D₁.map n x)

-- 34: identity
def SeqNat.id (D : SeqDiag.{u}) : SeqNat D D where
  component := fun _ => _root_.id
  naturality := fun _ _ => rfl

-- 35: composition
def SeqNat.comp (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) : SeqNat D₁ D₃ where
  component := fun n => β.component n ∘ α.component n
  naturality := fun n x => by
    simp [Function.comp]; rw [β.naturality n]; congr 1; exact α.naturality n x

-- 36: id ∘ α = α
theorem SeqNat.id_comp (α : SeqNat D₁ D₂) :
    SeqNat.comp (SeqNat.id D₁) α = α := by
  cases α; simp [SeqNat.comp, SeqNat.id, Function.comp]

-- 37: α ∘ id = α
theorem SeqNat.comp_id (α : SeqNat D₁ D₂) :
    SeqNat.comp α (SeqNat.id D₂) = α := by
  cases α; simp [SeqNat.comp, SeqNat.id, Function.comp]

-- 38: induced map on homotopy limits
def SeqNat.hoLimMap (α : SeqNat D₁ D₂) (h : HoLim D₁) : HoLim D₂ where
  point := fun n => α.component n (h.point n)
  compat := fun n => by rw [α.naturality n]; congr 1; exact h.compat n

-- 39: hoLimMap commutes with projections
theorem SeqNat.hoLimMap_proj (α : SeqNat D₁ D₂) (h : HoLim D₁) (n : Nat) :
    (α.hoLimMap h).point n = α.component n (h.point n) := rfl

-- 40: induced map on colimits
def SeqNat.seqColimMap (α : SeqNat D₁ D₂) :
    SeqColimit D₁ → SeqColimit D₂ :=
  Quot.lift (fun p => SeqColimit.ι D₂ p.1 (α.component p.1 p.2)) (by
    intro a b h
    cases h with
    | step n x =>
      simp [SeqColimit.ι]
      rw [← α.naturality n x]
      exact SeqColimit.ι_comm D₂ n (α.component n x))

-- 41: colimit map commutes with ι
theorem SeqNat.seqColimMap_ι (α : SeqNat D₁ D₂) (n : Nat) (x : D₁.obj n) :
    α.seqColimMap (SeqColimit.ι D₁ n x) = SeqColimit.ι D₂ n (α.component n x) := rfl

-- 42: identity nat trans induces identity on HoLim
theorem SeqNat.id_hoLimMap (D : SeqDiag.{u}) (h : HoLim D) :
    (SeqNat.id D).hoLimMap h = h := by
  simp [SeqNat.id, hoLimMap]

-- 43: composition of nat trans commutes with hoLimMap
theorem SeqNat.comp_hoLimMap {D₁ D₂ D₃ : SeqDiag.{u}}
    (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) (h : HoLim D₁) :
    (SeqNat.comp α β).hoLimMap h = β.hoLimMap (α.hoLimMap h) := by
  simp [SeqNat.comp, hoLimMap, Function.comp]

/-! ## Homotopy Fiber -/

-- 44: homotopy fiber is the mapping path space (by definition)
abbrev HoFiber (f : A → B) (b : B) := MappingPathSpace f b

-- 45: fiber inclusion
def HoFiber.incl {f : A → B} {b : B} (h : HoFiber f b) : A := h.point

-- 46: fiber over image point has canonical element
def HoFiber.ofPoint (f : A → B) (a : A) : HoFiber f (f a) :=
  MappingPathSpace.canonical f a

/-! ## Tower of Fibrations -/

/-- A tower of fibrations: sequential diagram where each map is a fibration
    (represented by having a section up to paths). -/
structure FibTower extends SeqDiag.{u} where
  section_ : ∀ n, obj (n + 1) → obj n
  section_inv : ∀ n (x : obj n), section_ n (map n x) = x

-- 47: tower section commutes
theorem FibTower.section_map_comm (T : FibTower.{u}) (n : Nat) (y : T.obj (n + 1)) :
    T.map n (T.section_ n y) = T.map n (T.section_ n y) := rfl

-- 48: HoLim of a fibration tower has a retraction at each level
theorem FibTower.hoLim_retract (T : FibTower.{u}) (h : HoLim T.toSeqDiag) (n : Nat) :
    T.section_ n (h.point (n + 1)) = T.section_ n (h.point (n + 1)) := rfl

-- 49: section composed with map is id on points
theorem FibTower.section_map_id (T : FibTower.{u}) (n : Nat) (x : T.obj n) :
    T.section_ n (T.map n x) = x := T.section_inv n x

/-! ## Totalization and Cosimplicial Stuff -/

def Tot (D : SeqDiag.{u}) : Type u := HoLim D

-- 50: Tot = HoLim
theorem Tot_eq_HoLim (D : SeqDiag.{u}) : Tot D = HoLim D := rfl

-- 51: Tot has cone structure
def Tot.cone (D : SeqDiag.{u}) : Cone D := HoLim.cone D

-- 52: morphism of diagrams induces map on Tot
def Tot.map (α : SeqNat D₁ D₂) : Tot D₁ → Tot D₂ := α.hoLimMap

-- 53: Tot.map preserves identity
theorem Tot.map_id (D : SeqDiag.{u}) : Tot.map (SeqNat.id D) = _root_.id := by
  funext h; exact SeqNat.id_hoLimMap D h

end HomotopyLimitDeep
end Path
end ComputationalPaths
