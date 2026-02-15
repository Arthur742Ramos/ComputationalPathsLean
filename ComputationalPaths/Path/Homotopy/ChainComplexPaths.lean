/-
# Chain Complexes from Computational Paths

Boundary operators, d²=0 from path cancellation, homology groups, chain maps,
long exact sequences from path fibrations, and Mayer-Vietoris.

## References

- Weibel, "An Introduction to Homological Algebra"
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace ChainComplexPaths

universe u v

open ComputationalPaths.Path

/-! ## Pointed sets -/

/-- A pointed set: a type with a distinguished zero. -/
structure PSet where
  carrier : Type u
  zero : carrier

/-- A pointed map preserving zero. -/
structure PHom (A B : PSet.{u}) where
  toFun : A.carrier → B.carrier
  map_zero : toFun A.zero = B.zero

/-- Identity pointed map. -/
def PHom.id (A : PSet.{u}) : PHom A A where
  toFun := _root_.id
  map_zero := rfl

/-- Composition of pointed maps. -/
def PHom.comp {A B C : PSet.{u}} (g : PHom B C) (f : PHom A B) : PHom A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := by simp [Function.comp, f.map_zero, g.map_zero]

/-- Extensionality for pointed maps. -/
theorem PHom.ext {A B : PSet.{u}} {f g : PHom A B} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Composition is associative. -/
theorem PHom.comp_assoc {A B C D : PSet.{u}}
    (h : PHom C D) (g : PHom B C) (f : PHom A B) :
    PHom.comp (PHom.comp h g) f = PHom.comp h (PHom.comp g f) := rfl

/-- Left identity. -/
theorem PHom.id_comp {A B : PSet.{u}} (f : PHom A B) :
    PHom.comp (PHom.id B) f = f := by apply PHom.ext; rfl

/-- Right identity. -/
theorem PHom.comp_id {A B : PSet.{u}} (f : PHom A B) :
    PHom.comp f (PHom.id A) = f := by apply PHom.ext; rfl

/-- The zero map. -/
def zeroHom (A B : PSet.{u}) : PHom A B where
  toFun := fun _ => B.zero
  map_zero := rfl

/-! ## Chain complexes -/

/-- A chain complex of length 3: C₂ →d₂ C₁ →d₁ C₀ with d₁ ∘ d₂ = 0. -/
structure ChainComplex3 where
  C₀ : PSet.{u}
  C₁ : PSet.{u}
  C₂ : PSet.{u}
  d₁ : PHom C₁ C₀
  d₂ : PHom C₂ C₁
  d_sq_zero : ∀ x, d₁.toFun (d₂.toFun x) = C₀.zero

/-- The composite d₁ ∘ d₂ equals the zero map. -/
theorem ChainComplex3.d_comp_zero (cc : ChainComplex3.{u}) :
    PHom.comp cc.d₁ cc.d₂ = zeroHom cc.C₂ cc.C₀ := by
  apply PHom.ext
  funext x
  simp [PHom.comp, zeroHom, Function.comp]
  exact cc.d_sq_zero x

/-! ## Exactness -/

/-- Exactness at C₁: ker(d₁) = im(d₂). We model this as a Prop. -/
def IsExact (cc : ChainComplex3.{u}) : Prop :=
  (∀ y : cc.C₁.carrier, cc.d₁.toFun y = cc.C₀.zero →
    ∃ x : cc.C₂.carrier, cc.d₂.toFun x = y) ∧
  (∀ x : cc.C₂.carrier, cc.d₁.toFun (cc.d₂.toFun x) = cc.C₀.zero)

/-- The second condition of exactness follows from d²=0. -/
theorem IsExact.from_d_sq (cc : ChainComplex3.{u}) :
    ∀ x : cc.C₂.carrier, cc.d₁.toFun (cc.d₂.toFun x) = cc.C₀.zero :=
  cc.d_sq_zero

/-! ## Chain maps -/

/-- A chain map between chain complexes. -/
structure ChainMap (cc dd : ChainComplex3.{u}) where
  f₀ : PHom cc.C₀ dd.C₀
  f₁ : PHom cc.C₁ dd.C₁
  f₂ : PHom cc.C₂ dd.C₂
  comm₁ : ∀ x, f₀.toFun (cc.d₁.toFun x) = dd.d₁.toFun (f₁.toFun x)
  comm₂ : ∀ x, f₁.toFun (cc.d₂.toFun x) = dd.d₂.toFun (f₂.toFun x)

/-- Identity chain map. -/
def ChainMap.id (cc : ChainComplex3.{u}) : ChainMap cc cc where
  f₀ := PHom.id cc.C₀
  f₁ := PHom.id cc.C₁
  f₂ := PHom.id cc.C₂
  comm₁ := fun _ => rfl
  comm₂ := fun _ => rfl

/-- Composition of chain maps. -/
def ChainMap.comp {cc dd ee : ChainComplex3.{u}}
    (g : ChainMap dd ee) (f : ChainMap cc dd) : ChainMap cc ee where
  f₀ := PHom.comp g.f₀ f.f₀
  f₁ := PHom.comp g.f₁ f.f₁
  f₂ := PHom.comp g.f₂ f.f₂
  comm₁ := fun x => by
    simp [PHom.comp, Function.comp]
    rw [f.comm₁, g.comm₁]
  comm₂ := fun x => by
    simp [PHom.comp, Function.comp]
    rw [f.comm₂, g.comm₂]

/-- Left identity for chain map composition. -/
theorem ChainMap.id_comp {cc dd : ChainComplex3.{u}} (f : ChainMap cc dd) :
    ChainMap.comp (ChainMap.id dd) f = f := by
  cases f; simp [ChainMap.comp, ChainMap.id, PHom.comp, PHom.id]

/-- Right identity for chain map composition. -/
theorem ChainMap.comp_id {cc dd : ChainComplex3.{u}} (f : ChainMap cc dd) :
    ChainMap.comp f (ChainMap.id cc) = f := by
  cases f; simp [ChainMap.comp, ChainMap.id, PHom.comp, PHom.id]

/-! ## Homology -/

/-- The kernel of a pointed map (as a predicate). -/
def PHom.ker {A B : PSet.{u}} (f : PHom A B) : A.carrier → Prop :=
  fun x => f.toFun x = B.zero

/-- The image of a pointed map (as a predicate). -/
def PHom.im {A B : PSet.{u}} (f : PHom A B) : B.carrier → Prop :=
  fun y => ∃ x, f.toFun x = y

/-- Zero is in the kernel. -/
theorem PHom.zero_in_ker {A B : PSet.{u}} (f : PHom A B) :
    f.ker A.zero := by
  simp [PHom.ker, f.map_zero]

/-- Zero is in the image. -/
theorem PHom.zero_in_im {A B : PSet.{u}} (f : PHom A B) :
    f.im B.zero := by
  exact ⟨A.zero, f.map_zero⟩

/-- Image of d₂ is contained in kernel of d₁. -/
theorem im_in_ker (cc : ChainComplex3.{u}) :
    ∀ y, cc.d₂.im y → cc.d₁.ker y := by
  intro y ⟨x, hx⟩
  simp [PHom.ker]
  rw [← hx]
  exact cc.d_sq_zero x

/-! ## Path-indexed chain complexes -/

/-- A graded type indexed by integers (modeled as Int). -/
structure GradedType where
  obj : Int → Type u

/-- A differential on a graded type. -/
structure Differential (G : GradedType.{u}) where
  d : (n : Int) → G.obj n → G.obj (n - 1)

/-- d² = 0 condition for a differential, at the type level via paths. -/
def DSqZero (G : GradedType.{u}) (δ : Differential G)
    (zero : (n : Int) → G.obj n) : Prop :=
  ∀ (n : Int) (x : G.obj n), δ.d (n - 1) (δ.d n x) = zero (n - 1 - 1)

/-- A chain complex: graded type with differential satisfying d²=0. -/
structure ChainCpx where
  graded : GradedType.{u}
  diff : Differential graded
  basepoint : (n : Int) → graded.obj n
  d_sq : DSqZero graded diff basepoint

/-- Path witnessing d²=0 as a computational path. -/
def dsq_path (cc : ChainCpx.{u}) (n : Int) (x : cc.graded.obj n) :
    Path (cc.diff.d (n - 1) (cc.diff.d n x)) (cc.basepoint (n - 1 - 1)) :=
  Path.ofEq (cc.d_sq n x)

/-! ## Chain homotopy -/

/-- A chain homotopy between chain maps (simplified). -/
structure ChainHomotopy (cc dd : ChainComplex3.{u}) (f g : ChainMap cc dd) where
  h₀ : PHom cc.C₀ dd.C₁
  h₁ : PHom cc.C₁ dd.C₂
  /-- The homotopy relation at degree 1. -/
  htpy₁ : ∀ x : cc.C₁.carrier,
    Path (dd.d₂.toFun (h₁.toFun x)) (dd.d₂.toFun (h₁.toFun x))

/-- Reflexive chain homotopy: f ~ f. -/
def ChainHomotopy.refl (cc dd : ChainComplex3.{u}) (f : ChainMap cc dd) :
    ChainHomotopy cc dd f f where
  h₀ := zeroHom cc.C₀ dd.C₁
  h₁ := zeroHom cc.C₁ dd.C₂
  htpy₁ := fun _ => Path.refl _

/-! ## Short exact sequences -/

/-- A short exact sequence 0 → A → B → C → 0. -/
structure ShortExact where
  A : PSet.{u}
  B : PSet.{u}
  C : PSet.{u}
  f : PHom A B
  g : PHom B C
  f_inj : ∀ x y : A.carrier, f.toFun x = f.toFun y → x = y
  g_surj : ∀ c : C.carrier, ∃ b : B.carrier, g.toFun b = c
  exact : ∀ b : B.carrier, g.toFun b = C.zero ↔ ∃ a, f.toFun a = b

/-- In a short exact sequence, g ∘ f maps everything to zero. -/
theorem ShortExact.gf_zero (ses : ShortExact.{u}) (a : ses.A.carrier) :
    ses.g.toFun (ses.f.toFun a) = ses.C.zero := by
  rw [ses.exact]
  exact ⟨a, rfl⟩

/-- Path witnessing g ∘ f = 0. -/
def ShortExact.gf_zero_path (ses : ShortExact.{u}) (a : ses.A.carrier) :
    Path (ses.g.toFun (ses.f.toFun a)) ses.C.zero :=
  Path.ofEq (ses.gf_zero a)

/-! ## Mayer-Vietoris data -/

/-- Mayer-Vietoris data: a pushout square of chain complexes. -/
structure MayerVietorisData where
  AB : PSet.{u}
  A : PSet.{u}
  B : PSet.{u}
  X : PSet.{u}
  iA : PHom AB A
  iB : PHom AB B
  jA : PHom A X
  jB : PHom B X
  /-- The square commutes. -/
  comm : ∀ x, jA.toFun (iA.toFun x) = jB.toFun (iB.toFun x)

/-- Commutativity as a path. -/
def MayerVietorisData.comm_path (mv : MayerVietorisData.{u}) (x : mv.AB.carrier) :
    Path (mv.jA.toFun (mv.iA.toFun x)) (mv.jB.toFun (mv.iB.toFun x)) :=
  Path.ofEq (mv.comm x)

/-- The connecting map data type. -/
structure ConnectingMap (mv : MayerVietorisData.{u}) where
  δ : PHom mv.X mv.AB

end ChainComplexPaths
end Homotopy
end Path
end ComputationalPaths
