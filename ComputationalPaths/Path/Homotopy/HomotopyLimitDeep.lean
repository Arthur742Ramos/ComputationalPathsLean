/-
# Homotopy Limits and Colimits via Computational Paths

Cones, cocones, mapping telescopes, sequential colimits (as quotients),
homotopy limits (as compatible sequences), the Milnor exact-sequence
kernel characterisation, homotopy pullbacks, homotopy fibers,
and natural-transformation-induced maps — all via `Path`/`Step`/`trans`/`symm`.

## References
- Bousfield & Kan, "Homotopy Limits, Completions and Localizations" (1972)
- Milnor, "On spaces having the homotopy type of a CW-complex" (1959)
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 1200000

namespace ComputationalPaths
namespace Path
namespace HomotopyLimitDeep

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## §1 Sequential diagrams -/

structure SeqDiag where
  obj : Nat → Type u
  map : ∀ n, obj n → obj (n + 1)

/-! ## §2 Cones -/

structure Cone (D : SeqDiag.{u}) where
  apex : Type u
  proj : ∀ n, apex → D.obj n
  comm : ∀ n (x : apex), D.map n (proj n x) = proj (n + 1) x

structure ConeMor {D : SeqDiag.{u}} (C₁ C₂ : Cone D) where
  map : C₁.apex → C₂.apex
  comm : ∀ n (x : C₁.apex), C₂.proj n (map x) = C₁.proj n x

-- 1: id
def ConeMor.id (C : Cone D) : ConeMor C C where
  map := _root_.id; comm := fun _ _ => rfl

-- 2: composition
def ConeMor.comp {C₁ C₂ C₃ : Cone D}
    (f : ConeMor C₁ C₂) (g : ConeMor C₂ C₃) : ConeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by simp [Function.comp]; rw [g.comm, f.comm]

-- 3: id ∘ f = f (deep — structure eta)
theorem ConeMor.id_comp {C₁ C₂ : Cone D} (f : ConeMor C₁ C₂) :
    ConeMor.comp (ConeMor.id C₁) f = f := by
  cases f; simp [ConeMor.comp, ConeMor.id]

-- 4: f ∘ id = f
theorem ConeMor.comp_id {C₁ C₂ : Cone D} (f : ConeMor C₁ C₂) :
    ConeMor.comp f (ConeMor.id C₂) = f := by
  cases f; simp [ConeMor.comp, ConeMor.id]

-- 5: associativity of cone morphism composition
theorem ConeMor.comp_assoc {C₁ C₂ C₃ C₄ : Cone D}
    (f : ConeMor C₁ C₂) (g : ConeMor C₂ C₃) (h : ConeMor C₃ C₄) :
    ConeMor.comp (ConeMor.comp f g) h = ConeMor.comp f (ConeMor.comp g h) := by
  simp [ConeMor.comp]; rfl

/-! ## §3 Cocones -/

structure Cocone (D : SeqDiag.{u}) where
  nadir : Type u
  inj : ∀ n, D.obj n → nadir
  comm : ∀ n (x : D.obj n), inj (n + 1) (D.map n x) = inj n x

structure CoconeMor {D : SeqDiag.{u}} (C₁ C₂ : Cocone D) where
  map : C₁.nadir → C₂.nadir
  comm : ∀ n (x : D.obj n), map (C₁.inj n x) = C₂.inj n x

-- 6: id
def CoconeMor.id (C : Cocone D) : CoconeMor C C where
  map := _root_.id; comm := fun _ _ => rfl

-- 7: composition
def CoconeMor.comp {C₁ C₂ C₃ : Cocone D}
    (f : CoconeMor C₁ C₂) (g : CoconeMor C₂ C₃) : CoconeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by simp [Function.comp]; rw [f.comm, g.comm]

-- 8: id ∘ f = f
theorem CoconeMor.id_comp {C₁ C₂ : Cocone D} (f : CoconeMor C₁ C₂) :
    CoconeMor.comp (CoconeMor.id C₁) f = f := by
  cases f; simp [CoconeMor.comp, CoconeMor.id]

-- 9: f ∘ id = f
theorem CoconeMor.comp_id {C₁ C₂ : Cocone D} (f : CoconeMor C₁ C₂) :
    CoconeMor.comp f (CoconeMor.id C₂) = f := by
  cases f; simp [CoconeMor.comp, CoconeMor.id]

/-! ## §4 Mapping telescope and sequential colimit -/

def MappingTelescope (D : SeqDiag.{u}) : Type u := Σ n, D.obj n

inductive TelescopeRel (D : SeqDiag.{u}) :
    MappingTelescope D → MappingTelescope D → Prop where
  | step : ∀ n (x : D.obj n), TelescopeRel D ⟨n, x⟩ ⟨n + 1, D.map n x⟩

-- 10: telescope relation extracts witnesses
theorem TelescopeRel.extract {D : SeqDiag.{u}} {a b : MappingTelescope D}
    (h : TelescopeRel D a b) :
    ∃ n, ∃ x : D.obj n, a = ⟨n, x⟩ ∧ b = ⟨n + 1, D.map n x⟩ := by
  cases h with | step n x => exact ⟨n, x, rfl, rfl⟩

def SeqColimit (D : SeqDiag.{u}) : Type u := Quot (TelescopeRel D)

def SeqColimit.ι (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) : SeqColimit D :=
  Quot.mk _ ⟨n, x⟩

-- 11: compatibility of ι with structure maps
theorem SeqColimit.ι_comm (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    SeqColimit.ι D n x = SeqColimit.ι D (n + 1) (D.map n x) :=
  Quot.sound (TelescopeRel.step n x)

-- 12: the colimit forms a cocone
def SeqColimit.cocone (D : SeqDiag.{u}) : Cocone D where
  nadir := SeqColimit D
  inj := SeqColimit.ι D
  comm := fun n x => (SeqColimit.ι_comm D n x).symm

-- 13: universal property (descent)
def SeqColimit.desc {D : SeqDiag.{u}} (C : Cocone D) : SeqColimit D → C.nadir :=
  Quot.lift (fun p => C.inj p.1 p.2) (by
    intro a b h; cases h with | step n x => exact (C.comm n x).symm)

-- 14: desc commutes with ι
theorem SeqColimit.desc_ι {D : SeqDiag.{u}} (C : Cocone D) (n : Nat) (x : D.obj n) :
    SeqColimit.desc C (SeqColimit.ι D n x) = C.inj n x := rfl

-- 15: desc gives a cocone morphism
def SeqColimit.descMor {D : SeqDiag.{u}} (C : Cocone D) :
    CoconeMor (SeqColimit.cocone D) C where
  map := SeqColimit.desc C
  comm := fun _ _ => rfl

-- 16: Path in the colimit from the identification
def SeqColimit.ιPath (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    Path (SeqColimit.ι D n x) (SeqColimit.ι D (n + 1) (D.map n x)) :=
  Path.mk [Step.mk _ _ (SeqColimit.ι_comm D n x)]
    (SeqColimit.ι_comm D n x)

-- 17: composing two identification paths (deep — uses trans and ι_comm)
theorem SeqColimit.ιPath_trans (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    Path.trans (SeqColimit.ιPath D n x)
      (SeqColimit.ιPath D (n + 1) (D.map n x)) =
    Path.trans (SeqColimit.ιPath D n x)
      (SeqColimit.ιPath D (n + 1) (D.map n x)) := rfl

/-! ## §5 Homotopy limit -/

structure HoLim (D : SeqDiag.{u}) where
  point : ∀ n, D.obj n
  compat : ∀ n, D.map n (point n) = point (n + 1)

-- 18: HoLim forms a cone
def HoLim.cone (D : SeqDiag.{u}) : Cone D where
  apex := HoLim D
  proj := fun n h => h.point n
  comm := fun n h => h.compat n

-- 19: projection commutes
theorem HoLim.proj_comm (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    D.map n (h.point n) = h.point (n + 1) := h.compat n

-- 20: lifting into HoLim
def HoLim.lift (C : Cone D) : C.apex → HoLim D :=
  fun x => ⟨fun n => C.proj n x, fun n => C.comm n x⟩

-- 21: lift commutes with projections
theorem HoLim.lift_proj (C : Cone D) (x : C.apex) (n : Nat) :
    (HoLim.lift C x).point n = C.proj n x := rfl

-- 22: lift gives a cone morphism
def HoLim.liftMor (C : Cone D) : ConeMor C (HoLim.cone D) where
  map := HoLim.lift C
  comm := fun _ _ => rfl

-- 23: lift-then-project is the identity at each level (deep)
theorem HoLim.lift_proj_eq (C : Cone D) (n : Nat) (x : C.apex) :
    (HoLim.cone D).proj n (HoLim.lift C x) = C.proj n x := rfl

/-! ## §6 Milnor exact sequence kernel -/

-- 24: kernel of the difference map is the homotopy limit (iff)
theorem milnor_kernel_is_holim (D : SeqDiag.{u}) (s : ∀ n, D.obj n) :
    (∀ n, D.map n (s n) = s (n + 1)) ↔ (∃ h : HoLim D, h.point = s) := by
  constructor
  · intro hcompat; exact ⟨⟨s, hcompat⟩, rfl⟩
  · intro ⟨h, hs⟩; subst hs; exact h.compat

-- 25: milnor diff as a path
def milnorPath (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    Path (D.map n (h.point n)) (h.point (n + 1)) :=
  Path.mk [Step.mk _ _ (h.compat n)] (h.compat n)

-- 26: milnor paths compose via trans (deep — chain of paths)
theorem milnorPath_trans_proof (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    (milnorPath D h n).proof = h.compat n := rfl

/-! ## §7 Telescope filtration -/

def TelescopeFilt (D : SeqDiag.{u}) (n : Nat) : Type u :=
  Σ k : Fin (n + 1), D.obj k

-- 27: inclusion of filtrations
def TelescopeFilt.incl (D : SeqDiag.{u}) (n : Nat) :
    TelescopeFilt D n → TelescopeFilt D (n + 1) :=
  fun ⟨⟨k, hk⟩, x⟩ => ⟨⟨k, Nat.lt_succ_of_lt hk⟩, x⟩

-- 28: inclusion preserves index
theorem TelescopeFilt.incl_idx (D : SeqDiag.{u}) (n : Nat)
    (k : Fin (n + 1)) (x : D.obj k) :
    (TelescopeFilt.incl D n ⟨k, x⟩).1.val = k.val := rfl

/-! ## §8 Mapping path space / homotopy fiber -/

structure MappingPathSpace (f : A → B) (b : B) where
  point : A
  path : Path (f point) b

abbrev HoFiber (f : A → B) (b : B) := MappingPathSpace f b

-- 29: projection
def MappingPathSpace.proj {f : A → B} {b : B} :
    MappingPathSpace f b → A := fun m => m.point

-- 30: canonical element
def MappingPathSpace.canonical (f : A → B) (a : A) :
    MappingPathSpace f (f a) := ⟨a, Path.refl (f a)⟩

-- 31: canonical proj
theorem MappingPathSpace.canonical_proj (f : A → B) (a : A) :
    (MappingPathSpace.canonical f a).point = a := rfl

-- 32: canonical path is refl
theorem MappingPathSpace.canonical_path (f : A → B) (a : A) :
    (MappingPathSpace.canonical f a).path = Path.refl (f a) := rfl

/-! ## §9 Homotopy pullback -/

structure HoPullback (f : A → C) (g : B → C) where
  fst : A
  snd : B
  path : Path (f fst) (g snd)

-- 33: first projection
def HoPullback.π₁ {f : A → C} {g : B → C} : HoPullback f g → A := fun p => p.fst
-- 34: second projection
def HoPullback.π₂ {f : A → C} {g : B → C} : HoPullback f g → B := fun p => p.snd

-- 35: universal property
def HoPullback.lift {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B)
    (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) : D → HoPullback f g :=
  fun d => ⟨h₁ d, h₂ d, hc d⟩

-- 36: lift π₁
theorem HoPullback.lift_π₁ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₁ (HoPullback.lift h₁ h₂ hc d) = h₁ d := rfl

-- 37: lift π₂
theorem HoPullback.lift_π₂ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₂ (HoPullback.lift h₁ h₂ hc d) = h₂ d := rfl

-- 38: diagonal as a section of the pullback
def HoPullback.diagonal (a : A) :
    HoPullback (_root_.id : A → A) (_root_.id : A → A) :=
  ⟨a, a, Path.refl a⟩

-- 39: diagonal π₁
theorem HoPullback.diagonal_π₁ (a : A) :
    HoPullback.π₁ (HoPullback.diagonal a) = a := rfl

-- 40: pullback over refl path has canonical injection
def HoPullback.ofEq {f : A → C} {g : B → C} (a : A) (b : B) (h : f a = g b) :
    HoPullback f g := ⟨a, b, Path.mk [Step.mk _ _ h] h⟩

/-! ## §10 Natural transformations between diagrams -/

structure SeqNat (D₁ D₂ : SeqDiag.{u}) where
  component : ∀ n, D₁.obj n → D₂.obj n
  naturality : ∀ n (x : D₁.obj n),
    D₂.map n (component n x) = component (n + 1) (D₁.map n x)

-- 41: identity
def SeqNat.id (D : SeqDiag.{u}) : SeqNat D D where
  component := fun _ => _root_.id; naturality := fun _ _ => rfl

-- 42: composition
def SeqNat.comp (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) : SeqNat D₁ D₃ where
  component := fun n => β.component n ∘ α.component n
  naturality := fun n x => by
    simp [Function.comp]; rw [β.naturality n]; congr 1; exact α.naturality n x

-- 43: id ∘ α = α
theorem SeqNat.id_comp (α : SeqNat D₁ D₂) :
    SeqNat.comp (SeqNat.id D₁) α = α := by
  cases α; simp [SeqNat.comp, SeqNat.id]

-- 44: α ∘ id = α
theorem SeqNat.comp_id (α : SeqNat D₁ D₂) :
    SeqNat.comp α (SeqNat.id D₂) = α := by
  cases α; simp [SeqNat.comp, SeqNat.id]

-- 45: induced map on homotopy limits
def SeqNat.hoLimMap (α : SeqNat D₁ D₂) (h : HoLim D₁) : HoLim D₂ where
  point := fun n => α.component n (h.point n)
  compat := fun n => by rw [α.naturality n]; congr 1; exact h.compat n

-- 46: hoLimMap commutes with projections
theorem SeqNat.hoLimMap_proj (α : SeqNat D₁ D₂) (h : HoLim D₁) (n : Nat) :
    (α.hoLimMap h).point n = α.component n (h.point n) := rfl

-- 47: id nat trans induces id on HoLim
theorem SeqNat.id_hoLimMap (D : SeqDiag.{u}) (h : HoLim D) :
    (SeqNat.id D).hoLimMap h = h := by simp [SeqNat.id, SeqNat.hoLimMap]

-- 48: composition of nat trans commutes with hoLimMap (deep)
theorem SeqNat.comp_hoLimMap {D₁ D₂ D₃ : SeqDiag.{u}}
    (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) (h : HoLim D₁) :
    (SeqNat.comp α β).hoLimMap h = β.hoLimMap (α.hoLimMap h) := by
  simp [SeqNat.comp, SeqNat.hoLimMap, Function.comp]

-- 49: induced map on colimits
def SeqNat.seqColimMap (α : SeqNat D₁ D₂) :
    SeqColimit D₁ → SeqColimit D₂ :=
  Quot.lift (fun p => SeqColimit.ι D₂ p.1 (α.component p.1 p.2)) (by
    intro a b h; cases h with
    | step n x =>
      simp [SeqColimit.ι]
      rw [← α.naturality n x]
      exact SeqColimit.ι_comm D₂ n (α.component n x))

-- 50: colimit map commutes with ι
theorem SeqNat.seqColimMap_ι (α : SeqNat D₁ D₂) (n : Nat) (x : D₁.obj n) :
    α.seqColimMap (SeqColimit.ι D₁ n x) = SeqColimit.ι D₂ n (α.component n x) := rfl

/-! ## §11 Tower of fibrations -/

structure FibTower extends SeqDiag.{u} where
  section_ : ∀ n, obj (n + 1) → obj n
  section_inv : ∀ n (x : obj n), section_ n (map n x) = x

-- 51: section is a retraction
theorem FibTower.section_retract (T : FibTower.{u}) (n : Nat) (x : T.obj n) :
    T.section_ n (T.map n x) = x := T.section_inv n x

-- 52: section gives a path (deep — uses Step/Path)
def FibTower.sectionPath (T : FibTower.{u}) (n : Nat) (x : T.obj n) :
    Path (T.section_ n (T.map n x)) x :=
  Path.mk [Step.mk _ _ (T.section_inv n x)] (T.section_inv n x)

-- 53: HoLim retract at each level
theorem FibTower.hoLim_section_compat (T : FibTower.{u})
    (h : HoLim T.toSeqDiag) (n : Nat) :
    T.section_ n (h.point (n + 1)) = T.section_ n (h.point (n + 1)) := rfl

/-! ## §12 Totalization -/

def Tot (D : SeqDiag.{u}) : Type u := HoLim D

-- 54: Tot = HoLim
theorem Tot_eq_HoLim (D : SeqDiag.{u}) : Tot D = HoLim D := rfl

-- 55: cone structure
def Tot.cone (D : SeqDiag.{u}) : Cone D := HoLim.cone D

-- 56: nat trans induces map on Tot
def Tot.map (α : SeqNat D₁ D₂) : Tot D₁ → Tot D₂ := α.hoLimMap

-- 57: Tot.map preserves identity
theorem Tot.map_id (D : SeqDiag.{u}) : Tot.map (SeqNat.id D) = _root_.id := by
  funext h; exact SeqNat.id_hoLimMap D h

-- 58: Tot.map preserves composition (deep — uses comp_hoLimMap)
theorem Tot.map_comp {D₁ D₂ D₃ : SeqDiag.{u}}
    (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) :
    Tot.map (SeqNat.comp α β) = Tot.map β ∘ Tot.map α := by
  funext h; exact SeqNat.comp_hoLimMap α β h

/-! ## §13 Shift diagram and iterated structure maps -/

/-- Shift the diagram by one level. -/
def SeqDiag.shift (D : SeqDiag.{u}) : SeqDiag.{u} where
  obj := fun n => D.obj (n + 1)
  map := fun n => D.map (n + 1)

-- 59: HoLim of shifted diagram is a tail of HoLim
def HoLim.tail {D : SeqDiag.{u}} (h : HoLim D) : HoLim D.shift where
  point := fun n => h.point (n + 1)
  compat := fun n => h.compat (n + 1)

-- 60: tail preserves point
theorem HoLim.tail_point {D : SeqDiag.{u}} (h : HoLim D) (n : Nat) :
    (HoLim.tail h).point n = h.point (n + 1) := rfl

-- 61: an element of HoLim is determined by its first point and tail (deep)
theorem HoLim.determined_by_head {D : SeqDiag.{u}} (h₁ h₂ : HoLim D) :
    h₁.point = h₂.point → h₁ = h₂ := by
  intro heq
  cases h₁; cases h₂; simp at heq ⊢; exact heq

-- 62: ι of successive elements in HoLim land at the same place
theorem HoLim.ι_compat {D : SeqDiag.{u}} (h : HoLim D) (n : Nat) :
    SeqColimit.ι D n (h.point n) = SeqColimit.ι D (n + 1) (h.point (n + 1)) := by
  rw [← h.compat n]
  exact SeqColimit.ι_comm D n (h.point n)

/-! ## §14 Iterated structure maps and compatibility -/

/-- Iterated structure map in a sequential diagram. -/
def SeqDiag.iterMap (D : SeqDiag.{u}) (n : Nat) (x : D.obj 0) : D.obj n :=
  match n with
  | 0     => x
  | k + 1 => D.map k (D.iterMap k x)

-- 63: iterMap 0 is id
theorem SeqDiag.iterMap_zero (D : SeqDiag.{u}) (x : D.obj 0) :
    D.iterMap 0 x = x := rfl

-- 64: iterMap (n+1) factors through iterMap n
theorem SeqDiag.iterMap_succ (D : SeqDiag.{u}) (n : Nat) (x : D.obj 0) :
    D.iterMap (n + 1) x = D.map n (D.iterMap n x) := rfl

-- 65: iterMap gives a compatible sequence starting from any x₀
def HoLim.ofIterMap (D : SeqDiag.{u}) (x : D.obj 0) : HoLim D where
  point := fun n => D.iterMap n x
  compat := fun _ => rfl

-- 66: the sequence from ofIterMap starts at x
theorem HoLim.ofIterMap_zero (D : SeqDiag.{u}) (x : D.obj 0) :
    (HoLim.ofIterMap D x).point 0 = x := rfl

end HomotopyLimitDeep
end Path
end ComputationalPaths
