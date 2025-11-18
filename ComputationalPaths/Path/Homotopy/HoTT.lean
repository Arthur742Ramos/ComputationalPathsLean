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

universe u v w

variable {A : Type u}

/-- Witness for `Π a, Id a a`.  Matches the thesis proof that the reflexive
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

end HoTT
end Path
end ComputationalPaths
