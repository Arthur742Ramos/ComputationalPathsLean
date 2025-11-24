/-
# HoTT primitives via computational paths

Basic groupoid laws for the identity type, phrased using computational paths.
These lemmas make it easy to port homotopy-style proofs into Lean without
replaying the raw `REWR` arguments every time.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT

universe u v w u' v' w'

variable {A : Type u}

/-- Witness for `Π a, Id a a`.  Matches the proof that the reflexive
path inhabits the first groupoid law. -/
def inhabIdRefl (A : Type u) : (a : A) → a = a :=
  fun _ => rfl

/-- Witness for `Π a b, Id(a,b) → Id(b,a)` using computational-path symmetry. -/
@[simp] def inhabIdSymm {a b : A} : Path a b → Path b a :=
  fun p => Path.symm p

/-- Translate the symmetry witness back to propositional equality. -/
theorem inhabIdSymm_toEq {a b : A} (p : Path a b) :
    (inhabIdSymm (a := a) (b := b) p).toEq = (p.toEq).symm :=
  rfl

/-- Witness for `Π a b c, Id(a,b) → Id(b,c) → Id(a,c)` using transitivity. -/
@[simp] def inhabIdTrans {a b c : A} :
    Path a b → Path b c → Path a c :=
  fun p q => Path.trans p q

/-- Translating the transitivity witness to propositional equality. -/
theorem inhabIdTrans_toEq
    {a b c : A} (p : Path a b) (q : Path b c) :
    (inhabIdTrans (a := a) (b := b) (c := c) p q).toEq =
      (p.toEq).trans (q.toEq) :=
  rfl

/-- Recover the symmetry law for `Id` directly from computational paths. -/
def inhabIdSymmEq {a b : A} :
    a = b → b = a :=
  fun h => h.symm

/-- Recover the transitivity law for `Id` from computational paths. -/
def inhabIdTransEq {a b c : A} :
    a = b → b = c → a = c :=
  fun h₁ h₂ => h₁.trans h₂

/-! ### Functoriality -/

section Functoriality

variable {B : Type v} {C : Type w}

/-- Action of a function on computational paths (`ap`). -/
@[simp] def ap (f : A → B) {x y : A} :
    Path x y → Path (f x) (f y) :=
  fun p => Path.congrArg f p

/-- Transport transitivity through `ap`. -/
@[simp] theorem ap_trans (f : A → B) {x y z : A}
    (p : Path x y) (q : Path y z) :
    ap (A := A) (B := B) f (Path.trans p q) =
      Path.trans (ap (A := A) (B := B) f p)
        (ap (A := A) (B := B) f q) :=
  Path.congrArg_trans (f := f) (p := p) (q := q)

/-- Transport symmetry through `ap`. -/
@[simp] theorem ap_symm (f : A → B) {x y : A} (p : Path x y) :
    ap (A := A) (B := B) f (Path.symm p) =
      Path.symm (ap (A := A) (B := B) f p) :=
  Path.congrArg_symm (f := f) (p := p)

/-- Compatibility with function composition. -/
@[simp] theorem ap_comp (f : A → B) (g : B → C)
    {x y : A} (p : Path x y) :
    ap (A := B) (B := C) g (ap (A := A) (B := B) f p) =
      ap (A := A) (B := C) (fun a => g (f a)) p := by
  dsimp [ap]
  exact
    (Path.congrArg_comp (A := A) (B := B) (C := C)
      (f := g) (g := f) (p := p)).symm

/-- `ap` for the identity function is the identity on paths. -/
@[simp] theorem ap_id {x y : A} (p : Path x y) :
    ap (A := A) (B := A) (fun a => a) p = p := by
  dsimp [ap]
  exact Path.congrArg_id (p := p)

/-- The familiar `ap` for propositional equality. -/
def apEq (f : A → B) {x y : A} :
    x = y → f x = f y :=
  fun h => _root_.congrArg f h

end Functoriality

/-! ### Transport and Leibniz-style substitution -/

section Transport

variable {P : A → Type v} {x y : A}

/-- Transport a dependent value along a computational path. -/
def transport (p : Path x y) (u : P x) : P y :=
  Path.transport (A := A) (D := P) p u

@[simp] theorem transport_refl (u : P x) :
    transport (A := A) (P := P) (p := Path.refl x) (u := u) = u :=
  Path.transport_refl (A := A) (D := P) (a := x) (x := u)

variable {B : Type v}

@[simp] theorem transport_const (p : Path x y) (b : B) :
    transport (A := A) (P := fun _ => B) p b = b :=
  Path.transport_const (p := p) (x := b)

/-- Leibniz substitution: transport witnesses `Id`-based substitution. -/
def leibniz {x y : A} (p : Path x y) : (P x → P y) :=
  fun hx => transport (A := A) (P := P) (p := p) (u := hx)

end Transport

/-! ### Transport via propositional equality -/

section TransportEq

variable {P : A → Type v} {x y : A}

/-- Transport phrased with propositional equality, implemented via path transport. -/
def transportEq (p : x = y) (u : P x) : P y :=
  transport (A := A) (P := P) (Path.ofEq p) u

@[simp] theorem transportEq_refl (u : P x) :
    transportEq (P := P) (p := rfl) (u := u) = u :=
  by
    simpa [transportEq] using
      (Path.transport_ofEq (A := A) (D := P)
        (a := x) (b := x) (h := rfl) (x := u))

@[simp] theorem transportEq_const {B : Type v} (p : x = y) (b : B) :
    transportEq (P := fun _ => B) (p := p) (u := b) = b := by
  simp [transportEq]

@[simp] theorem transport_toEq (p : Path x y) (u : P x) :
    transport (A := A) (P := P) p u =
      transportEq (P := P) (p := p.toEq) (u := u) := by
  have :
      transport (A := A) (P := P) p u =
        transport (A := A) (P := P) (Path.ofEq p.toEq) u :=
    Path.transport_of_toEq_eq (A := A) (D := P)
      (p := p) (q := Path.ofEq (A := A) (a := x) (b := y) p.toEq)
      (h := rfl) (x := u)
  simpa [transportEq] using this

def leibnizEq {x y : A} (p : x = y) : P x → P y :=
  fun hx => transportEq (P := P) (p := p) (u := hx)

end TransportEq

/-! ### Homotopies -/

section Homotopy

variable {P : A → Type v}

/-- A homotopy between dependent functions assigns a path for every point. -/
def Homotopy (f g : (x : A) → P x) : Type (max u v) :=
  (x : A) → Path (f x) (g x)

notation f " ~ᵖ " g => Homotopy f g

/-- Reflexivity of homotopies. -/
@[simp] def homotopy_refl (f : (x : A) → P x) :
    f ~ᵖ f :=
  fun _ => Path.refl _

/-- Symmetry of homotopies. -/
@[simp] def homotopy_symm {f g : (x : A) → P x}
    (H : f ~ᵖ g) : g ~ᵖ f :=
  fun x => Path.symm (H x)

/-- Transitivity of homotopies. -/
@[simp] def homotopy_trans {f g h : (x : A) → P x}
    (H₁ : f ~ᵖ g) (H₂ : g ~ᵖ h) : f ~ᵖ h :=
  fun x => Path.trans (H₁ x) (H₂ x)

variable {B : Type v}

/-- Naturality of homotopies with respect to precomposition by paths. -/
@[simp] theorem homotopy_naturality_toEq
    {f g : A → B} (H : f ~ᵖ g)
    {x y : A} (p : Path x y) :
    (Path.trans (H x) (ap (A := A) (B := B) g p)).toEq =
      (Path.trans (ap (A := A) (B := B) f p) (H y)).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

end Homotopy

/-- Homotopies between non-dependent functions. -/
abbrev FunHomotopy {A : Type u} {B : Type v}
    (f g : A → B) : Type (max u v) :=
  Homotopy (A := A) (P := fun _ => B) f g

section Equivalences

variable {A : Type u} {B : Type v}

/-- A quasi-inverse for a function `f` consists of the inverse function plus
homotopies witnessing the round-trip laws. -/
structure QuasiInverse (f : A → B) where
  inv : B → A
  leftHomotopy : FunHomotopy (fun b => f (inv b)) (fun b => b)
  rightHomotopy : FunHomotopy (fun a => inv (f a)) (fun a => a)

/-- A function is an equivalence if it admits a quasi-inverse. -/
structure IsEquiv (f : A → B) where
  toQuasiInverse : QuasiInverse f

namespace IsEquiv

variable {f : A → B}

/-- Extract the chosen inverse from an equivalence. -/
@[simp] def inv (hf : IsEquiv f) : B → A :=
  hf.toQuasiInverse.inv

end IsEquiv

@[simp] def IsEquiv.refl (A : Type u) :
    IsEquiv (fun x : A => x) where
  toQuasiInverse :=
  { inv := fun x => x
    leftHomotopy := fun _ => Path.refl _
    rightHomotopy := fun _ => Path.refl _ }

end Equivalences

/-! ### Cartesian products -/

section Prod

variable {Z : Type u} {A₀ : Z → Type v} {B₀ : Z → Type w}
variable {z₁ z₂ : Z}

/-- Transport along a path in the base of a product family splits componentwise. -/
theorem transport_prod (p : Path z₁ z₂)
    (x : A₀ z₁ × B₀ z₁) :
    transport (A := Z) (P := fun z => A₀ z × B₀ z) p x =
      (transport (A := Z) (P := A₀) p x.1,
        transport (A := Z) (P := B₀) p x.2) := by
  simp [transport, Path.transport_prod_fun]

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}

/-- Applying a product map to a path computed componentwise matches applying
`ap` to each component and rebuilding the product path. -/
@[simp] theorem prod_congrArg_toEq
    (g : A → A') (h : B → B')
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Path.congrArg (fun x : A × B => (g x.1, h x.2))
        (Path.prodMk p q)).toEq =
      (Path.prodMk (Path.congrArg g p)
        (Path.congrArg h q)).toEq := by
  simp

end Prod

/-! ### Unit type -/

section Unit

/-- The unit type is contractible: every pair of points is connected by a reflexive path. -/
@[simp] def unitPath (x y : Unit) : Path x y := by
  cases x
  cases y
  simpa using Path.refl ()

@[simp] theorem unitPath_eq_refl (x : Unit) :
    unitPath x x = Path.refl x := by
  cases x
  simp

@[simp] theorem unitPath_toEq (x y : Unit) :
    (unitPath x y).toEq = rfl := by
  cases x
  cases y
  simp

end Unit

/-! ### Function extensionality -/

section Funext

variable {A : Type u} {B : Type v}

/-- A pointwise family of computational paths assembles into a path between functions. -/
@[simp] def funextPath {f g : A → B}
    (H : (x : A) → Path (f x) (g x)) : Path f g :=
  Path.lamCongr H

/-- A path between functions restricts to pointwise paths. -/
@[simp] def funextPointwise {f g : A → B}
    (p : Path f g) : (x : A) → Path (f x) (g x) :=
  fun x => Path.app p x

/-- Weak function extensionality: given an inhabitant of `A`,
    pointwise paths between functions extend to a global path. -/
def weakFunext (a₀ : A) :
    (f g : A → B) →
      ((x : A) → Path (f x) (g x)) → Path f g :=
  fun f g H =>
    (show Path f g from
      (by
        let _ := a₀
        exact funextPath (A := A) (B := B) (f := f) (g := g) H))

@[simp] theorem funextPath_toEq {f g : A → B}
    (H : (x : A) → Path (f x) (g x)) :
    (funextPath (A := A) (B := B) (f := f) (g := g) H).toEq =
      funext fun x => (H x).toEq := rfl

@[simp] theorem funextPointwise_toEq {f g : A → B}
    (p : Path f g) (x : A) :
    (funextPointwise (A := A) (B := B) (f := f) (g := g) p x).toEq =
      _root_.congrArg (fun h => h x) p.toEq := rfl

end Funext

end HoTT
end Path
end ComputationalPaths
