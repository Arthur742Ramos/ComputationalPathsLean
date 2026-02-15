/-
# Presheaves via Computational Paths

Presheaf as contravariant path functor, Yoneda embedding, representable
presheaves, natural transformations, presheaf categories, colimits.

## References

- Mac Lane–Moerdijk, *Sheaves in Geometry and Logic* (1992)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Category
namespace PresheafPaths

universe u v

/-! ## §1 Presheaf structure -/

/-- A presheaf on `A`: contravariant functor from equalities to types. -/
structure Presheaf (A : Type u) where
  obj : A → Type v
  restrict : {a b : A} → (a = b) → obj b → obj a
  restrict_id : ∀ (a : A) (x : obj a), restrict (Eq.refl a) x = x
  restrict_comp : ∀ {a b c : A} (p : a = b) (q : b = c) (x : obj c),
    restrict p (restrict q x) = restrict (p.trans q) x

/-- Natural transformation between presheaves. -/
structure PresheafNatTrans {A : Type u} (F G : Presheaf.{u, v} A) where
  app : ∀ a, F.obj a → G.obj a
  natural : ∀ {a b : A} (p : a = b) (x : F.obj b),
    app a (F.restrict p x) = G.restrict p (app b x)

/-- Restrict a presheaf along a computational Path. -/
def pathRestrict {A : Type u} (F : Presheaf.{u, v} A) {a b : A}
    (p : Path a b) : F.obj b → F.obj a :=
  F.restrict p.proof

/-- pathRestrict at refl is identity. -/
theorem pathRestrict_refl {A : Type u} (F : Presheaf.{u, v} A)
    (a : A) (x : F.obj a) : pathRestrict F (Path.refl a) x = x :=
  F.restrict_id a x

/-- pathRestrict is proof-irrelevant. -/
theorem pathRestrict_irrel {A : Type u} (F : Presheaf.{u, v} A)
    {a b : A} (p q : Path a b) (x : F.obj b) :
    pathRestrict F p x = pathRestrict F q x := by
  unfold pathRestrict; congr 1

/-! ## §2 Representable Presheaves -/

/-- Representable presheaf at `c`: sections over `a` are Paths from `a` to `c`. -/
def representable (A : Type u) (c : A) : Presheaf.{u, u} A where
  obj := fun a => Path a c
  restrict := fun {a b} p q => Path.mk q.steps (p.trans q.proof)
  restrict_id := by intro a x; cases x; congr 1
  restrict_comp := by intro a b d p q x; cases x; congr 1

/-- Obj of representable at c. -/
theorem representable_obj_at (A : Type u) (c : A) :
    (representable A c).obj c = Path c c := rfl

/-- The canonical section: refl. -/
def representable_id_section (A : Type u) (c : A) :
    (representable A c).obj c := Path.refl c

/-! ## §3 Yoneda Map -/

/-- Yoneda forward: F.obj c → Hom(repr(c), F). -/
def yonedaForward {A : Type u} (F : Presheaf.{u, u} A) (c : A) (x : F.obj c) :
    PresheafNatTrans (representable A c) F where
  app := fun a p => F.restrict p.proof x
  natural := by
    intro a b p q
    show F.restrict (Path.mk q.steps (p.trans q.proof)).proof x =
         F.restrict p (F.restrict q.proof x)
    rw [F.restrict_comp]

/-- Yoneda backward: evaluate at refl. -/
def yonedaBackward {A : Type u} (F : Presheaf.{u, u} A) (c : A)
    (η : PresheafNatTrans (representable A c) F) : F.obj c :=
  η.app c (Path.refl c)

/-- Yoneda round-trip: backward ∘ forward = id. -/
theorem yoneda_roundtrip {A : Type u} (F : Presheaf.{u, u} A) (c : A) (x : F.obj c) :
    yonedaBackward F c (yonedaForward F c x) = x := by
  unfold yonedaBackward yonedaForward; exact F.restrict_id c x

/-- Yoneda other direction at component. -/
theorem yoneda_other_direction {A : Type u} (F : Presheaf.{u, u} A)
    (c : A) (η : PresheafNatTrans (representable A c) F) (a : A) (p : Path a c) :
    (yonedaForward F c (yonedaBackward F c η)).app a p =
    η.app a ((representable A c).restrict p.proof (Path.refl c)) := by
  show F.restrict p.proof (η.app c (Path.refl c)) = _
  exact (η.natural p.proof (Path.refl c)).symm

/-! ## §4 Presheaf Category -/

/-- Identity nat trans. -/
def natTransId {A : Type u} (F : Presheaf.{u, v} A) : PresheafNatTrans F F where
  app := fun _ x => x
  natural := fun _ _ => rfl

/-- Composition of nat trans. -/
def natTransComp {A : Type u} {F G H : Presheaf.{u, v} A}
    (η : PresheafNatTrans F G) (θ : PresheafNatTrans G H) : PresheafNatTrans F H where
  app := fun a x => θ.app a (η.app a x)
  natural := by intro a b p x; rw [η.natural p x, θ.natural p (η.app b x)]

/-- Left identity. -/
theorem natTransComp_id_left {A : Type u} {F G : Presheaf.{u, v} A}
    (η : PresheafNatTrans F G) (a : A) (x : F.obj a) :
    (natTransComp (natTransId F) η).app a x = η.app a x := rfl

/-- Right identity. -/
theorem natTransComp_id_right {A : Type u} {F G : Presheaf.{u, v} A}
    (η : PresheafNatTrans F G) (a : A) (x : F.obj a) :
    (natTransComp η (natTransId G)).app a x = η.app a x := rfl

/-- Associativity. -/
theorem natTransComp_assoc {A : Type u} {F G H K : Presheaf.{u, v} A}
    (η : PresheafNatTrans F G) (θ : PresheafNatTrans G H) (ξ : PresheafNatTrans H K)
    (a : A) (x : F.obj a) :
    (natTransComp (natTransComp η θ) ξ).app a x =
    (natTransComp η (natTransComp θ ξ)).app a x := rfl

/-! ## §5 Yoneda Embedding -/

/-- Yoneda embedding: Path a→b gives nat trans repr(b) → repr(a). -/
def yonedaEmbedPath {A : Type u} {a b : A} (p : Path a b) :
    PresheafNatTrans (representable A b) (representable A a) where
  app := fun c q => Path.mk q.steps (q.proof.trans p.proof.symm)
  natural := by
    intro c d r q; simp only [representable]

/-- Yoneda embedding preserves identity. -/
theorem yonedaEmbed_refl {A : Type u} (a c : A) (q : Path c a) :
    (yonedaEmbedPath (Path.refl a)).app c q = q := by
  simp only [yonedaEmbedPath]

/-- Yoneda embedding is proof-irrelevant. -/
theorem yonedaEmbed_irrel {A : Type u} {a b : A} (p q : Path a b) (c : A) (r : Path c b) :
    (yonedaEmbedPath p).app c r = (yonedaEmbedPath q).app c r := by
  simp only [yonedaEmbedPath]

/-! ## §6 Mono/Epi -/

def isMonoNatTrans {A : Type u} {F G : Presheaf.{u, v} A} (η : PresheafNatTrans F G) : Prop :=
  ∀ a (x y : F.obj a), η.app a x = η.app a y → x = y

def isEpiNatTrans {A : Type u} {F G : Presheaf.{u, v} A} (η : PresheafNatTrans F G) : Prop :=
  ∀ a (y : G.obj a), ∃ x : F.obj a, η.app a x = y

theorem natTransId_isMono {A : Type u} (F : Presheaf.{u, v} A) :
    isMonoNatTrans (natTransId F) := fun _ _ _ h => h

theorem natTransId_isEpi {A : Type u} (F : Presheaf.{u, v} A) :
    isEpiNatTrans (natTransId F) := fun _ y => ⟨y, rfl⟩

theorem natTransComp_isMono {A : Type u} {F G H : Presheaf.{u, v} A}
    {η : PresheafNatTrans F G} {θ : PresheafNatTrans G H}
    (hη : isMonoNatTrans η) (hθ : isMonoNatTrans θ) :
    isMonoNatTrans (natTransComp η θ) :=
  fun a x y h => hη a x y (hθ a _ _ h)

theorem natTransComp_isEpi {A : Type u} {F G H : Presheaf.{u, v} A}
    {η : PresheafNatTrans F G} {θ : PresheafNatTrans G H}
    (hη : isEpiNatTrans η) (hθ : isEpiNatTrans θ) :
    isEpiNatTrans (natTransComp η θ) := by
  intro a z
  obtain ⟨y, hy⟩ := hθ a z
  obtain ⟨x, hx⟩ := hη a y
  exact ⟨x, by simp [natTransComp]; rw [hx, hy]⟩

/-! ## §7 Constant/Terminal/Product Presheaves -/

def constPresheaf (A : Type u) (S : Type u) : Presheaf.{u, u} A where
  obj := fun _ => S
  restrict := fun _ x => x
  restrict_id := fun _ _ => rfl
  restrict_comp := fun _ _ _ => rfl

def terminalPresheaf (A : Type u) : Presheaf.{u, u} A where
  obj := fun _ => PUnit
  restrict := fun _ _ => PUnit.unit
  restrict_id := fun _ x => by cases x; rfl
  restrict_comp := fun _ _ x => by cases x; rfl

def toTerminal {A : Type u} (F : Presheaf.{u, u} A) :
    PresheafNatTrans F (terminalPresheaf A) where
  app := fun _ _ => PUnit.unit
  natural := fun _ _ => rfl

theorem toTerminal_unique {A : Type u} (F : Presheaf.{u, u} A)
    (η θ : PresheafNatTrans F (terminalPresheaf A)) (a : A) (x : F.obj a) :
    η.app a x = θ.app a x := by cases η.app a x; cases θ.app a x; rfl

def presheafProd {A : Type u} (F G : Presheaf.{u, v} A) : Presheaf.{u, v} A where
  obj := fun a => F.obj a × G.obj a
  restrict := fun p ⟨x, y⟩ => (F.restrict p x, G.restrict p y)
  restrict_id := by intro a ⟨x, y⟩; simp [F.restrict_id, G.restrict_id]
  restrict_comp := by
    intro a b c p q ⟨x, y⟩; simp [F.restrict_comp, G.restrict_comp]

def presheafFst {A : Type u} (F G : Presheaf.{u, v} A) :
    PresheafNatTrans (presheafProd F G) F where
  app := fun _ ⟨x, _⟩ => x
  natural := fun _ _ => rfl

def presheafSnd {A : Type u} (F G : Presheaf.{u, v} A) :
    PresheafNatTrans (presheafProd F G) G where
  app := fun _ ⟨_, y⟩ => y
  natural := fun _ _ => rfl

theorem presheafProd_jointly_mono {A : Type u} (F G : Presheaf.{u, v} A)
    (a : A) (x y : (presheafProd F G).obj a)
    (h1 : (presheafFst F G).app a x = (presheafFst F G).app a y)
    (h2 : (presheafSnd F G).app a x = (presheafSnd F G).app a y) :
    x = y := by
  cases x; cases y; simp [presheafFst, presheafSnd] at h1 h2; exact Prod.ext h1 h2

/-! ## §8 Path-Transport and Coherence -/

def presheafTransport {A : Type u} (F : Presheaf.{u, v} A)
    {a b : A} (p : Path a b) (x : F.obj a) : F.obj b :=
  F.restrict p.proof.symm x

theorem presheafTransport_refl {A : Type u} (F : Presheaf.{u, v} A)
    (a : A) (x : F.obj a) : presheafTransport F (Path.refl a) x = x :=
  F.restrict_id a x

theorem presheafTransport_irrel {A : Type u} (F : Presheaf.{u, v} A)
    {a b : A} (p q : Path a b) (x : F.obj a) :
    presheafTransport F p x = presheafTransport F q x := by
  unfold presheafTransport; congr 1

theorem constPresheaf_restrict_trivial {A : Type u} (S : Type u)
    {a b : A} (p : a = b) (x : S) :
    (constPresheaf A S).restrict p x = x := rfl

def constNatTrans {A : Type u} (S : Type u) (F : Presheaf.{u, u} A)
    (f : ∀ a, S → F.obj a)
    (hnat : ∀ {a b : A} (p : a = b) (x : S), f a x = F.restrict p (f b x)) :
    PresheafNatTrans (constPresheaf A S) F where
  app := f
  natural := fun p x => hnat p x

end PresheafPaths
end Category
end Path
end ComputationalPaths
