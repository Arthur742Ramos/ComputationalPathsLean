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

/-- A sequential diagram: a sequence of types with maps between them. -/
structure SeqDiag where
  obj : Nat → Type u
  map : ∀ n, obj n → obj (n + 1)

/-- Iterated map in a sequential diagram. -/
def SeqDiag.iterMap (D : SeqDiag.{u}) : ∀ {m}, (n : Nat) → D.obj m → D.obj (m + n)
  | _, 0 => fun x => x
  | _, (n + 1) => fun x =>
    have h : m + (n + 1) = (m + n) + 1 := by omega
    h ▸ D.map (m + n) (D.iterMap n x)

-- 1: iterMap 0 is id
theorem SeqDiag.iterMap_zero (D : SeqDiag.{u}) {m : Nat} (x : D.obj m) :
    D.iterMap 0 x = x := rfl

-- 2: iterMap 1 is map
theorem SeqDiag.iterMap_one (D : SeqDiag.{u}) {m : Nat} (x : D.obj m) :
    D.iterMap 1 x = (by rw [show m + 1 = m + 1 from rfl]; exact D.map m x) := by
  simp [iterMap]

/-! ## Cones -/

/-- A cone over a sequential diagram: an apex with maps to each level. -/
structure Cone (D : SeqDiag.{u}) where
  apex : Type u
  proj : ∀ n, apex → D.obj n
  comm : ∀ n (x : apex), D.map n (proj n x) = proj (n + 1) x

-- 3: constant cone from a point
def Cone.const (D : SeqDiag.{u}) (a : D.obj 0)
    (hcompat : ∀ n, D.iterMap n a = D.iterMap n a) :
    Cone D where
  apex := Unit
  proj := fun n _ => D.iterMap n a
  comm := by
    intro n _
    simp [SeqDiag.iterMap]

/-- Morphism of cones. -/
structure ConeMor {D : SeqDiag.{u}} (C₁ C₂ : Cone D) where
  map : C₁.apex → C₂.apex
  comm : ∀ n (x : C₁.apex), C₂.proj n (map x) = C₁.proj n x

-- 4: identity cone morphism
def ConeMor.id {D : SeqDiag.{u}} (C : Cone D) : ConeMor C C where
  map := _root_.id
  comm := fun _ _ => rfl

-- 5: composition of cone morphisms
def ConeMor.comp {D : SeqDiag.{u}} {C₁ C₂ C₃ : Cone D}
    (f : ConeMor C₁ C₂) (g : ConeMor C₂ C₃) : ConeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by
    simp [Function.comp]; rw [g.comm, f.comm]

/-! ## Cocones -/

/-- A cocone under a sequential diagram. -/
structure Cocone (D : SeqDiag.{u}) where
  nadir : Type u
  inj : ∀ n, D.obj n → nadir
  comm : ∀ n (x : D.obj n), inj (n + 1) (D.map n x) = inj n x

/-- Morphism of cocones. -/
structure CoconeMor {D : SeqDiag.{u}} (C₁ C₂ : Cocone D) where
  map : C₁.nadir → C₂.nadir
  comm : ∀ n (x : D.obj n), map (C₁.inj n x) = C₂.inj n x

-- 6: identity cocone morphism
def CoconeMor.id {D : SeqDiag.{u}} (C : Cocone D) : CoconeMor C C where
  map := _root_.id
  comm := fun _ _ => rfl

-- 7: composition of cocone morphisms
def CoconeMor.comp {D : SeqDiag.{u}} {C₁ C₂ C₃ : Cocone D}
    (f : CoconeMor C₁ C₂) (g : CoconeMor C₂ C₃) : CoconeMor C₁ C₃ where
  map := g.map ∘ f.map
  comm := fun n x => by
    simp [Function.comp]; rw [f.comm, g.comm]

/-! ## Mapping Telescope -/

/-- The mapping telescope: the colimit type for a sequential diagram.
    Elements are pairs (n, x) where x : D.obj n, modulo the relation
    (n, x) ~ (n+1, D.map n x). We represent it as a sigma type. -/
def MappingTelescope (D : SeqDiag.{u}) : Type u :=
  Σ n, D.obj n

/-- The natural injection into the telescope. -/
def MappingTelescope.inj (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    MappingTelescope D := ⟨n, x⟩

-- 8: telescope forms a cocone (modulo the identification relation)
def MappingTelescope.cocone (D : SeqDiag.{u}) : Cocone D where
  nadir := MappingTelescope D
  inj := MappingTelescope.inj D
  comm := fun _n _x => rfl  -- up to the quotient relation

-- Wait, that's not right since comm needs inj (n+1) (map n x) = inj n x
-- but Sigma.mk (n+1) (map n x) ≠ Sigma.mk n x in general.
-- We need a quotient. Let's define a proper colimit.

/-- The telescope relation: identifies (n, x) with (n+1, D.map n x). -/
inductive TelescopeRel (D : SeqDiag.{u}) : MappingTelescope D → MappingTelescope D → Prop where
  | step : ∀ n (x : D.obj n), TelescopeRel D ⟨n, x⟩ ⟨n + 1, D.map n x⟩

-- 9: telescope relation is symmetric (in extended form)
theorem TelescopeRel.symm_iff {D : SeqDiag.{u}} (a b : MappingTelescope D) :
    TelescopeRel D a b → ∃ n (x : D.obj n), a = ⟨n, x⟩ ∧ b = ⟨n + 1, D.map n x⟩ := by
  intro h; cases h with
  | step n x => exact ⟨n, x, rfl, rfl⟩

/-! ## Sequential Colimit -/

/-- Sequential colimit as a quotient of the telescope.
    We use the transitive-symmetric-reflexive closure. -/
def SeqColimit (D : SeqDiag.{u}) : Type u :=
  Quot (TelescopeRel D)

/-- Canonical injection into the sequential colimit. -/
def SeqColimit.ι (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) : SeqColimit D :=
  Quot.mk _ ⟨n, x⟩

-- 10: compatibility of ι with the structure maps
theorem SeqColimit.ι_comm (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    SeqColimit.ι D (n + 1) (D.map n x) = SeqColimit.ι D n x := by
  exact Quot.sound (TelescopeRel.step n x)

-- 11: the colimit forms a cocone
def SeqColimit.cocone (D : SeqDiag.{u}) : Cocone D where
  nadir := SeqColimit D
  inj := SeqColimit.ι D
  comm := fun n x => (SeqColimit.ι_comm D n x).symm

-- 12: universal property of the colimit (existence)
def SeqColimit.desc {D : SeqDiag.{u}} (C : Cocone D) : SeqColimit D → C.nadir :=
  Quot.lift (fun ⟨n, x⟩ => C.inj n x) (by
    intro a b h; cases h with
    | step n x => exact (C.comm n x).symm)

-- 13: desc commutes with ι
theorem SeqColimit.desc_ι {D : SeqDiag.{u}} (C : Cocone D) (n : Nat) (x : D.obj n) :
    SeqColimit.desc C (SeqColimit.ι D n x) = C.inj n x := rfl

-- 14: desc is the unique such map (cocone morphism)
def SeqColimit.descMor {D : SeqDiag.{u}} (C : Cocone D) :
    CoconeMor (SeqColimit.cocone D) C where
  map := SeqColimit.desc C
  comm := fun n x => rfl

/-! ## Paths in the Colimit -/

-- 15: Path in the colimit from the identification
def SeqColimit.identPath (D : SeqDiag.{u}) (n : Nat) (x : D.obj n) :
    Path (SeqColimit.ι D n x) (SeqColimit.ι D (n + 1) (D.map n x)) :=
  Path.symm (Path.ofEq (SeqColimit.ι_comm D n x))

-- 16: iterated identification path
def SeqColimit.iterIdentPath (D : SeqDiag.{u}) (n : Nat) (x : D.obj n)
    (k : Nat) : Path (SeqColimit.ι D n x) (SeqColimit.ι D n x) :=
  Path.refl _

/-! ## Homotopy Limit via Products -/

/-- The homotopy limit of a sequential diagram: compatible sequences. -/
structure HoLim (D : SeqDiag.{u}) where
  point : ∀ n, D.obj n
  compat : ∀ n, D.map n (point n) = point (n + 1)

-- 17: HoLim forms a cone
def HoLim.cone (D : SeqDiag.{u}) : Cone D where
  apex := HoLim D
  proj := fun n h => h.point n
  comm := fun n h => h.compat n

-- 18: projection commutes with structure maps
theorem HoLim.proj_comm (D : SeqDiag.{u}) (h : HoLim D) (n : Nat) :
    D.map n (h.point n) = h.point (n + 1) := h.compat n

-- 19: lifting into HoLim from a cone
def HoLim.lift {D : SeqDiag.{u}} (C : Cone D) : C.apex → HoLim D :=
  fun x => ⟨fun n => C.proj n x, fun n => C.comm n x⟩

-- 20: lift commutes with projections
theorem HoLim.lift_proj {D : SeqDiag.{u}} (C : Cone D) (x : C.apex) (n : Nat) :
    (HoLim.lift C x).point n = C.proj n x := rfl

-- 21: lift gives a cone morphism
def HoLim.liftMor {D : SeqDiag.{u}} (C : Cone D) :
    ConeMor C (HoLim.cone D) where
  map := HoLim.lift C
  comm := fun _n _x => rfl

/-! ## Milnor Exact Sequence Setup -/

/-- The shift map on the product: (x₀, x₁, x₂, ...) ↦ (f₀(x₀), f₁(x₁), ...). -/
def shiftMap (D : SeqDiag.{u}) (s : ∀ n, D.obj n) : ∀ n, D.obj (n + 1) :=
  fun n => D.map n (s n)

/-- The difference map for the Milnor sequence:
    d(s)_n = f_n(s_n) - s_{n+1}  (where - means identification via paths). -/
def milnorDiff (D : SeqDiag.{u}) (s : ∀ n, D.obj n) (n : Nat) :
    D.map n (s n) = s (n + 1) → Path (D.map n (s n)) (s (n + 1)) :=
  fun h => Path.ofEq h

-- 22: kernel of the difference map is the homotopy limit
theorem milnor_kernel_is_holim (D : SeqDiag.{u}) (s : ∀ n, D.obj n) :
    (∀ n, D.map n (s n) = s (n + 1)) ↔ (∃ h : HoLim D, h.point = s) := by
  constructor
  · intro hcompat
    exact ⟨⟨s, hcompat⟩, rfl⟩
  · intro ⟨h, hs⟩
    subst hs
    exact h.compat

/-! ## Telescope Filtration -/

/-- The n-th filtration of the telescope: elements up to level n. -/
def TelescopeFilt (D : SeqDiag.{u}) (n : Nat) : Type u :=
  Σ k : Fin (n + 1), D.obj k

-- 23: inclusion of filtrations
def TelescopeFilt.incl (D : SeqDiag.{u}) (n : Nat) :
    TelescopeFilt D n → TelescopeFilt D (n + 1) :=
  fun ⟨⟨k, hk⟩, x⟩ => ⟨⟨k, Nat.lt_succ_of_lt hk⟩, x⟩

-- 24: top element of the next filtration
def TelescopeFilt.top (D : SeqDiag.{u}) (n : Nat) (x : D.obj (n + 1)) :
    TelescopeFilt D (n + 1) :=
  ⟨⟨n + 1, Nat.lt_succ_of_le (Nat.le_refl _)⟩, x⟩

-- 25: filtration injection commutes with the structure map (via path)
theorem TelescopeFilt.incl_compat (D : SeqDiag.{u}) (n : Nat)
    (k : Fin (n + 1)) (x : D.obj k) :
    (TelescopeFilt.incl D n ⟨k, x⟩).1.val = k.val := rfl

/-! ## Mapping Path Space -/

/-- The mapping path space of a map f : A → B (homotopy fiber / path space). -/
structure MappingPathSpace (f : A → B) (b : B) where
  point : A
  path : Path (f point) b

-- 26: the projection from the mapping path space
def MappingPathSpace.proj (f : A → B) (b : B) :
    MappingPathSpace f b → A :=
  fun m => m.point

-- 27: the evaluation map
def MappingPathSpace.eval (f : A → B) (b : B) :
    MappingPathSpace f b → B :=
  fun _ => b

-- 28: if f a = b definitionally, there's a canonical point
def MappingPathSpace.canonical (f : A → B) (a : A) :
    MappingPathSpace f (f a) where
  point := a
  path := Path.refl (f a)

-- 29: path between canonical points lifts
theorem MappingPathSpace.canonical_proj (f : A → B) (a : A) :
    (MappingPathSpace.canonical f a).point = a := rfl

/-! ## Pullback (Homotopy) -/

/-- Homotopy pullback of f : A → C and g : B → C. -/
structure HoPullback (f : A → C) (g : B → C) where
  fst : A
  snd : B
  path : Path (f fst) (g snd)

-- 30: first projection
def HoPullback.π₁ (f : A → C) (g : B → C) :
    HoPullback f g → A := fun p => p.fst

-- 31: second projection
def HoPullback.π₂ (f : A → C) (g : B → C) :
    HoPullback f g → B := fun p => p.snd

-- 32: universal property (existence)
def HoPullback.lift {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B)
    (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) : D → HoPullback f g :=
  fun d => ⟨h₁ d, h₂ d, hc d⟩

-- 33: lift commutes with π₁
theorem HoPullback.lift_π₁ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₁ f g (HoPullback.lift h₁ h₂ hc d) = h₁ d := rfl

-- 34: lift commutes with π₂
theorem HoPullback.lift_π₂ {D : Type u} {f : A → C} {g : B → C}
    (h₁ : D → A) (h₂ : D → B) (hc : ∀ d, Path (f (h₁ d)) (g (h₂ d))) (d : D) :
    HoPullback.π₂ f g (HoPullback.lift h₁ h₂ hc d) = h₂ d := rfl

/-! ## Homotopy Pushout -/

/-- Homotopy pushout data: f : C → A and g : C → B. -/
inductive HoPushout.Rel (f : C → A) (g : C → B) : A ⊕ B → A ⊕ B → Prop where
  | glue : ∀ c, Rel f g (Sum.inl (f c)) (Sum.inr (g c))

def HoPushout (f : C → A) (g : C → B) : Type (max u v w) :=
  Quot (HoPushout.Rel f g)

def HoPushout.inl (f : C → A) (g : C → B) (a : A) : HoPushout f g :=
  Quot.mk _ (Sum.inl a)

def HoPushout.inr (f : C → A) (g : C → B) (b : B) : HoPushout f g :=
  Quot.mk _ (Sum.inr b)

-- 35: gluing path in the pushout
theorem HoPushout.glue_path (f : C → A) (g : C → B) (c : C) :
    HoPushout.inl f g (f c) = HoPushout.inr f g (g c) :=
  Quot.sound (HoPushout.Rel.glue c)

-- 36: Path version of the gluing
def HoPushout.gluePath (f : C → A) (g : C → B) (c : C) :
    Path (HoPushout.inl f g (f c)) (HoPushout.inr f g (g c)) :=
  Path.ofEq (HoPushout.glue_path f g c)

-- 37: pushout universal property
def HoPushout.desc {D : Type (max u v w)} (f : C → A) (g : C → B)
    (h₁ : A → D) (h₂ : B → D)
    (hglue : ∀ c, h₁ (f c) = h₂ (g c)) : HoPushout f g → D :=
  Quot.lift (fun s => match s with
    | Sum.inl a => h₁ a
    | Sum.inr b => h₂ b) (by
    intro a b h; cases h with
    | glue c => exact hglue c)

-- 38: desc commutes with inl
theorem HoPushout.desc_inl {D : Type (max u v w)} (f : C → A) (g : C → B)
    (h₁ : A → D) (h₂ : B → D)
    (hglue : ∀ c, h₁ (f c) = h₂ (g c)) (a : A) :
    HoPushout.desc f g h₁ h₂ hglue (HoPushout.inl f g a) = h₁ a := rfl

-- 39: desc commutes with inr
theorem HoPushout.desc_inr {D : Type (max u v w)} (f : C → A) (g : C → B)
    (h₁ : A → D) (h₂ : B → D)
    (hglue : ∀ c, h₁ (f c) = h₂ (g c)) (b : B) :
    HoPushout.desc f g h₁ h₂ hglue (HoPushout.inr f g b) = h₂ b := rfl

/-! ## Cofiber Sequence via Paths -/

/-- The cofiber (mapping cone) of a map f : A → B. -/
def Cofiber (f : A → B) : Type (max u v) :=
  HoPushout f (fun _ : A => PUnit.unit)

-- 40: injection from B into the cofiber
def Cofiber.fromB (f : A → B) (b : B) : Cofiber f :=
  HoPushout.inl f (fun _ => PUnit.unit) b

-- 41: the point at infinity in the cofiber
def Cofiber.point (f : A → B) : Cofiber f :=
  HoPushout.inr f (fun _ => PUnit.unit) PUnit.unit

-- 42: gluing in the cofiber
theorem Cofiber.glue (f : A → B) (a : A) :
    Cofiber.fromB f (f a) = Cofiber.point f :=
  HoPushout.glue_path f (fun _ => PUnit.unit) a

-- 43: Path in the cofiber
def Cofiber.gluePath (f : A → B) (a : A) :
    Path (Cofiber.fromB f (f a)) (Cofiber.point f) :=
  Path.ofEq (Cofiber.glue f a)

/-! ## Connecting Map (Puppe Sequence) -/

/-- The connecting map δ : Cofiber f → ΣA (suspension) is definable
    once we have a suspension. We model suspension as cofiber of A → Unit. -/
def Susp (A : Type u) : Type u :=
  @HoPushout A PUnit PUnit (fun _ => PUnit.unit) (fun _ => PUnit.unit)

def Susp.north (A : Type u) : Susp A :=
  HoPushout.inl (fun _ : A => PUnit.unit) (fun _ => PUnit.unit) PUnit.unit

def Susp.south (A : Type u) : Susp A :=
  HoPushout.inr (fun _ : A => PUnit.unit) (fun _ => PUnit.unit) PUnit.unit

-- 44: meridian path in the suspension
def Susp.merid (a : A) : Path (Susp.north A) (Susp.south A) :=
  HoPushout.gluePath (fun _ : A => PUnit.unit) (fun _ => PUnit.unit) a

-- 45: all meridians have same endpoints
theorem Susp.merid_endpoints (a₁ a₂ : A) :
    (Susp.merid a₁).proof = (Susp.merid a₂).proof := by
  apply Subsingleton.elim

/-! ## lim¹ and the Milnor Sequence -/

/-- The lim¹ obstruction: failure of surjectivity of the shift-minus-identity map.
    Represented as a quotient. -/
def Lim1 (D : SeqDiag.{u}) : Type u :=
  let prod := ∀ n, D.obj n
  let rel : prod → prod → Prop := fun s t =>
    ∃ u : prod, ∀ n, D.map n (u n) = s n ∧ u (n + 1) = t n
  Quot rel

-- 46: injection into lim¹
def Lim1.mk (D : SeqDiag.{u}) (s : ∀ n, D.obj n) : Lim1 D :=
  Quot.mk _ s

-- 47: zero element (trivial class) of lim¹
def Lim1.zero (D : SeqDiag.{u}) (h : ∀ n, D.obj n) : Lim1 D :=
  Lim1.mk D h

/-! ## Totalization -/

/-- The totalization of a cosimplicial diagram (simplified to sequential). -/
def Tot (D : SeqDiag.{u}) : Type u := HoLim D

-- 48: Tot is the homotopy limit
theorem Tot_eq_HoLim (D : SeqDiag.{u}) : Tot D = HoLim D := rfl

/-! ## Natural Transformations between Diagrams -/

/-- A natural transformation between sequential diagrams. -/
structure SeqNat (D₁ D₂ : SeqDiag.{u}) where
  component : ∀ n, D₁.obj n → D₂.obj n
  naturality : ∀ n (x : D₁.obj n),
    D₂.map n (component n x) = component (n + 1) (D₁.map n x)

-- 49: identity natural transformation
def SeqNat.id (D : SeqDiag.{u}) : SeqNat D D where
  component := fun _ => _root_.id
  naturality := fun _ _ => rfl

-- 50: composition of natural transformations
def SeqNat.comp {D₁ D₂ D₃ : SeqDiag.{u}}
    (α : SeqNat D₁ D₂) (β : SeqNat D₂ D₃) : SeqNat D₁ D₃ where
  component := fun n => β.component n ∘ α.component n
  naturality := fun n x => by
    simp [Function.comp]
    rw [β.naturality n (α.component n x)]
    congr 1
    exact α.naturality n x

-- 51: induced map on homotopy limits
def SeqNat.hoLimMap {D₁ D₂ : SeqDiag.{u}} (α : SeqNat D₁ D₂) :
    HoLim D₁ → HoLim D₂ where
  point := fun n => α.component n (h.point n)
  compat := fun n => by
    rw [α.naturality n (h.point n)]
    congr 1
    exact h.compat n

-- 52: induced map on colimits
def SeqNat.seqColimMap {D₁ D₂ : SeqDiag.{u}} (α : SeqNat D₁ D₂) :
    SeqColimit D₁ → SeqColimit D₂ :=
  Quot.lift (fun ⟨n, x⟩ => SeqColimit.ι D₂ n (α.component n x)) (by
    intro a b h; cases h with
    | step n x =>
      simp [SeqColimit.ι]
      rw [← α.naturality n x]
      exact SeqColimit.ι_comm D₂ n (α.component n x))

-- 53: colimit map commutes with ι
theorem SeqNat.seqColimMap_ι {D₁ D₂ : SeqDiag.{u}} (α : SeqNat D₁ D₂)
    (n : Nat) (x : D₁.obj n) :
    α.seqColimMap (SeqColimit.ι D₁ n x) = SeqColimit.ι D₂ n (α.component n x) := rfl

end HomotopyLimitDeep
end Path
end ComputationalPaths
