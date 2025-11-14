/-
# Quotients of computational paths by rewrite equality

Builds the setoid induced by `RwEq`, defines the quotient `PathRwQuot`,
relates it to propositional equality, and proves the beta/eta interaction lemmas
used throughout the library.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

open scoped Quot

universe u v w

section Setoid

/-- Rewrite equality induces a setoid on computational paths. -/
def rwEqSetoid (A : Type u) (a b : A) : Setoid (Path a b) where
  r := RwEq
  iseqv :=
    { refl := fun p => rweq_refl (p := p)
      symm := fun {_ _} h => rweq_symm h
      trans := fun {_ _ _} h₁ h₂ => rweq_trans h₁ h₂ }

@[simp] theorem rwEqSetoid_r {A : Type u} {a b : A} :
    (rwEqSetoid A a b).r = RwEq :=
  rfl

instance pathRwEqSetoid (A : Type u) (a b : A) :
    Setoid (Path a b) :=
  rwEqSetoid A a b

/-- Paths modulo rewrite equality, mirroring the paper's notion of canonical proofs. -/
abbrev PathRwQuot (A : Type u) (a b : A) :=
  Quot (rwEqSetoid A a b).r

end Setoid

namespace PathRwQuot

variable {A : Type u} {a b : A}

open Quot

/-- Reflexive element in the quotient. -/
def refl (a : A) : PathRwQuot A a a :=
  Quot.mk _ (Path.refl a)

/-- Symmetry descends to the quotient. -/
def symm {a b : A} :
    PathRwQuot A a b → PathRwQuot A b a := fun x =>
  Quot.liftOn x (fun p => Quot.mk _ (Path.symm p))
    (by
      intro p q h
      exact Quot.sound (rweq_symm_congr h))

/-- Composition descends to the quotient. -/
def trans {a b c : A} :
    PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c :=
  fun x y =>
    Quot.liftOn x (fun p : Path a b =>
      Quot.liftOn y (fun q : Path b c => Quot.mk _ (Path.trans p q))
        (by
          intro q₁ q₂ hq
          exact Quot.sound
            (rweq_trans_congr_right (a := a) (b := b) (c := c)
              (p := p) (q := q₁) (r := q₂) hq)))
      (by
        intro p₁ p₂ hp
        refine Quot.inductionOn y (fun q =>
          Quot.sound
            (rweq_trans_congr_left (a := a) (b := b) (c := c)
              (p := p₁) (q := p₂) (r := q) hp)))

/-- Coerce a propositional equality to the path quotient. -/
@[simp] def ofEq {a b : A} (h : a = b) : PathRwQuot A a b :=
  Quot.mk _ (Path.ofEq h)

/-- Forget the rewrite trace and recover the underlying equality. -/
def toEq {a b : A} : PathRwQuot A a b → a = b :=
  Quot.lift (fun p : Path a b => p.toEq)
    (by
      intro p q h
      exact rweq_toEq h)

@[simp] theorem toEq_mk {a b : A} (p : Path a b) :
    toEq (A := A) (Quot.mk _ p) = p.toEq := rfl

@[simp] theorem toEq_refl (a : A) :
    toEq (A := A) (refl (A := A) a) = rfl := rfl

@[simp] theorem toEq_ofEq {a b : A} (h : a = b) :
    toEq (A := A) (ofEq (A := A) h) = h := rfl

@[simp] theorem toEq_symm {a b : A} (x : PathRwQuot A a b) :
    toEq (A := A) (symm (A := A) x) = (toEq (A := A) x).symm := by
  refine Quot.inductionOn x (fun p => by simp)

@[simp] theorem toEq_trans {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    toEq (A := A) (trans (A := A) x y) =
      (toEq (A := A) x).trans (toEq (A := A) y) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q => by simp))

@[simp] theorem ofEq_refl (a : A) :
    ofEq (A := A) (a := a) (b := a) (rfl : a = a) =
      refl (A := A) a := by
  change Quot.mk _ (Path.ofEq (A := A) (a := a) (b := a) (rfl : a = a)) =
    Quot.mk _ (Path.refl a)
  apply Quot.sound
  have h := rweq_canon (p := Path.refl a)
  exact rweq_symm h

@[simp] theorem ofEq_symm {a b : A} (h : a = b) :
    ofEq (A := A) (a := b) (b := a) h.symm =
      symm (A := A) (ofEq (A := A) (a := a) (b := b) h) := by
  change Quot.mk _
      (Path.ofEq (A := A) (a := b) (b := a) h.symm) =
    Quot.mk _
      (Path.symm (Path.ofEq (A := A) (a := a) (b := b) h))
  apply Quot.sound
  have hcanon :=
  rweq_canon
      (p :=
        Path.symm (Path.ofEq (A := A) (a := a) (b := b) h))
  exact rweq_symm hcanon

@[simp] theorem ofEq_trans {a b c : A} (h : a = b) (k : b = c) :
    ofEq (A := A) (a := a) (b := c) (h.trans k) =
      trans (A := A)
        (ofEq (A := A) (a := a) (b := b) h)
        (ofEq (A := A) (a := b) (b := c) k) := by
  change Quot.mk _
      (Path.ofEq (A := A) (a := a) (b := c) (h.trans k)) =
    Quot.mk _
      (Path.trans
        (Path.ofEq (A := A) (a := a) (b := b) h)
        (Path.ofEq (A := A) (a := b) (b := c) k))
  apply Quot.sound
  have hcanon :=
  rweq_canon
      (p :=
        Path.trans
          (Path.ofEq (A := A) (a := a) (b := b) h)
          (Path.ofEq (A := A) (a := b) (b := c) k))
  exact rweq_symm hcanon

@[simp] theorem symm_mk {a b : A} (p : Path a b) :
    symm (A := A) (Quot.mk _ p) = Quot.mk _ (Path.symm p) := rfl

@[simp] theorem trans_mk {a b c : A}
    (p : Path a b) (q : Path b c) :
    trans (A := A) (Quot.mk _ p) (Quot.mk _ q) =
      Quot.mk _ (Path.trans p q) := rfl

@[simp] theorem mk_canon {a b : A} (p : Path a b) :
    (Quot.mk _ p : PathRwQuot A a b) = Quot.mk _ (Path.ofEq p.toEq) := by
  apply Quot.sound
  exact rweq_canon (p := p)

@[simp] theorem symm_symm {a b : A}
    (x : PathRwQuot A a b) :
    symm (A := A) (symm x) = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.symm_symm (A := A) p))

@[simp] theorem trans_refl_left {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (refl a) x = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_refl_left (A := A) p))

@[simp] theorem trans_refl_right {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (refl b) = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_refl_right (A := A) p))

@[simp] theorem trans_symm {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (symm x) = refl a := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_symm (A := A) p))

@[simp] theorem symm_trans {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (symm x) x = refl b := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.symm_trans (A := A) p))

@[simp] theorem trans_assoc {a b c d : A}
    (x : PathRwQuot A a b)
    (y : PathRwQuot A b c)
    (z : PathRwQuot A c d) :
    trans (A := A) (trans x y) z =
      trans x (trans y z) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q =>
      Quot.inductionOn z (fun r => by
        apply Quot.sound
        exact rweq_of_step
          (Step.trans_assoc (A := A) (p := p) (q := q) (r := r)))))

/-- Paper-style notation `cmpA` for quotient composition. -/
@[simp] def cmpA {a b c : A} :
    PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c :=
  trans (A := A)

/-- Paper-style notation `invA` for quotient inversion. -/
@[simp] def invA {a b : A} :
    PathRwQuot A a b → PathRwQuot A b a :=
  symm (A := A)

@[simp] theorem cmpA_refl_left {a b : A}
    (x : PathRwQuot A a b) :
    cmpA (A := A) (refl (A := A) a) x = x :=
  trans_refl_left (A := A) (x := x)

@[simp] theorem cmpA_refl_right {a b : A}
    (x : PathRwQuot A a b) :
    cmpA (A := A) x (refl (A := A) b) = x :=
  trans_refl_right (A := A) (x := x)

@[simp] theorem cmpA_assoc {a b c d : A}
    (x : PathRwQuot A a b)
    (y : PathRwQuot A b c)
    (z : PathRwQuot A c d) :
    cmpA (A := A) (cmpA x y) z =
      cmpA (A := A) x (cmpA y z) :=
  trans_assoc (A := A) (x := x) (y := y) (z := z)

@[simp] theorem cmpA_inv_right {a b : A}
    (x : PathRwQuot A a b) :
    cmpA (A := A) x (invA x) =
      refl (A := A) a :=
  trans_symm (A := A) (x := x)

@[simp] theorem cmpA_inv_left {a b : A}
    (x : PathRwQuot A a b) :
    cmpA (A := A) (invA x) x =
      refl (A := A) b :=
  symm_trans (A := A) (x := x)

@[simp] theorem toEq_cmpA_inv_right {a b : A}
    (x : PathRwQuot A a b) :
    toEq (A := A) (cmpA (A := A) x (invA x)) = rfl := by
  simp

@[simp] theorem toEq_cmpA_inv_left {a b : A}
    (x : PathRwQuot A a b) :
    toEq (A := A) (cmpA (A := A) (invA x) x) = rfl := by
  simp

@[simp] theorem canon_reduce {a b : A}
    (x : PathRwQuot A a b) :
    x = Quot.mk _ (Path.ofEq (toEq x)) := by
  refine Quot.inductionOn x (fun p => by
    change Quot.mk _ p = Quot.mk _ (Path.ofEq p.toEq)
    exact mk_canon (A := A) (p := p))

@[simp] def normalPath {a b : A} (x : PathRwQuot A a b) : Path a b :=
  Path.ofEq (A := A) (a := a) (b := b) (toEq x)

@[simp] theorem normalPath_isNormal {a b : A}
    (x : PathRwQuot A a b) :
    IsNormal (A := A) (a := a) (b := b) (normalPath (A := A) (x := x)) := by
  unfold normalPath IsNormal
  rfl

@[simp] theorem normalPath_mk {a b : A} (p : Path a b) :
    normalPath (A := A) (x := Quot.mk _ p) =
      normalize (A := A) (a := a) (b := b) p := rfl

@[simp] theorem canon_reduce_normalPath {a b : A}
    (x : PathRwQuot A a b) :
    x = Quot.mk _ (normalPath (A := A) (x := x)) := by
  unfold normalPath
  exact canon_reduce (A := A) (x := x)

@[simp] def normalForm {a b : A}
    (x : PathRwQuot A a b) : NormalForm A a b :=
  { path := normalPath (A := A) (x := x)
    isNormal := normalPath_isNormal (A := A) (x := x) }

@[simp] theorem normalForm_path {a b : A} (x : PathRwQuot A a b) :
    (normalForm (A := A) (x := x)).path =
      normalPath (A := A) (x := x) := rfl

@[simp] theorem normalForm_mk {a b : A} (p : Path a b) :
    normalForm (A := A) (x := Quot.mk _ p) =
      normalizeForm (A := A) (a := a) (b := b) p := by
  unfold normalForm normalizeForm normalPath normalize
  rfl

@[simp] theorem normalForm_reduce {a b : A}
    (x : PathRwQuot A a b) :
    x = Quot.mk _ (normalForm (A := A) (x := x)).path := by
  unfold normalForm normalPath
  exact canon_reduce (A := A) (x := x)

@[simp] theorem normalPath_toEq {a b : A}
    (x : PathRwQuot A a b) :
    (normalPath (A := A) (x := x)).toEq =
      PathRwQuot.toEq (A := A) x := rfl

@[simp] theorem rweq_normalPath_refl (a : A) :
    RwEq (normalPath (A := A) (x := PathRwQuot.refl (A := A) a))
      (Path.refl a) := by
  classical
  have h := rweq_canon (p := Path.refl a)
  unfold normalPath
  exact rweq_symm h

@[simp] theorem rweq_normalPath_symm {a b : A}
    (x : PathRwQuot A a b) :
    RwEq (Path.symm (normalPath (A := A) (x := x)))
      (normalPath (A := A)
        (x := PathRwQuot.symm (A := A) x)) := by
  classical
  have h :=
  rweq_canon
      (p := Path.symm (normalPath (A := A) (x := x)))
  have htarget :
      Path.ofEq (A := A)
          (a := _)
          (b := _)
          (Path.toEq
            (Path.symm (normalPath (A := A) (x := x)))) =
        normalPath (A := A)
          (x := PathRwQuot.symm (A := A) x) := by
    unfold normalPath
    simp
  exact rweq_trans h (rweq_of_eq htarget)

@[simp] theorem rweq_normalPath_trans {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    RwEq
      (Path.trans (normalPath (A := A) (x := x))
        (normalPath (A := A) (x := y)))
      (normalPath (A := A)
        (x := PathRwQuot.trans (A := A) x y)) := by
  classical
  have h :=
  rweq_canon
      (p :=
        Path.trans (normalPath (A := A) (x := x))
          (normalPath (A := A) (x := y)))
  have htarget :
      Path.ofEq (A := A)
          (a := _)
          (b := _)
          (Path.toEq (Path.trans (normalPath (A := A) (x := x))
            (normalPath (A := A) (x := y)))) =
        normalPath (A := A)
          (x := PathRwQuot.trans (A := A) x y) := by
    unfold normalPath
    simp
  exact rweq_trans h (rweq_of_eq htarget)

@[simp] theorem rweq_normalForm_trans {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    RwEq
      (Path.trans
        (normalForm (A := A) (x := x)).path
        (normalForm (A := A) (x := y)).path)
      (normalForm (A := A)
        (x := PathRwQuot.trans (A := A) x y)).path := by
  change RwEq
      (Path.trans (normalPath (A := A) (x := x))
        (normalPath (A := A) (x := y)))
      (normalPath (A := A)
        (x := PathRwQuot.trans (A := A) x y))
  exact rweq_normalPath_trans (A := A) (x := x) (y := y)

@[simp] theorem rweq_normalForm_symm {a b : A}
    (x : PathRwQuot A a b) :
    RwEq (Path.symm (normalForm (A := A) (x := x)).path)
      (normalForm (A := A)
        (x := PathRwQuot.symm (A := A) x)).path := by
  change RwEq
      (Path.symm (normalPath (A := A) (x := x)))
      (normalPath (A := A)
        (x := PathRwQuot.symm (A := A) x))
  exact rweq_normalPath_symm (A := A) (x := x)

theorem ofEq_toEq {a b : A}
    (x : PathRwQuot A a b) :
    ofEq (A := A) (toEq x) = x :=
  (canon_reduce (A := A) (x := x)).symm

/-- `PathRwQuot` is definitionally equivalent to propositional equality. -/
def equivEq (A : Type u) (a b : A) :
    SimpleEquiv (PathRwQuot A a b) (a = b) where
  toFun := toEq (A := A)
  invFun := fun h => ofEq (A := A) (a := a) (b := b) h
  left_inv := by
    intro x
    exact ofEq_toEq (A := A) (a := a) (b := b) x
  right_inv := by
    intro h
    exact toEq_ofEq (A := A) (a := a) (b := b) h

@[simp] theorem equivEq_apply (x : PathRwQuot A a b) :
    (equivEq (A := A) (a := a) (b := b)).toFun x =
      toEq (A := A) x := rfl

@[simp] theorem equivEq_symm_apply (h : a = b) :
    (equivEq (A := A) (a := a) (b := b)).invFun h =
      ofEq (A := A) (a := a) (b := b) h := rfl

@[simp] theorem eq_of_toEq_eq
    {x y : PathRwQuot A a b}
    (h : toEq (A := A) x = toEq (A := A) y) :
    x = y := by
  classical
  let e := equivEq (A := A) (a := a) (b := b)
  have hx : e.invFun (e.toFun x) = x := e.left_inv x
  have hy : e.invFun (e.toFun y) = y := e.left_inv y
  have hxEq : e.toFun x = toEq (A := A) x := by
    change e x = toEq (A := A) x
    simp
  have hyEq : e.toFun y = toEq (A := A) y := by
    change e y = toEq (A := A) y
    simp
  have h' : e.toFun x = e.toFun y := by
    calc
      e.toFun x = toEq (A := A) x := hxEq
      _ = toEq (A := A) y := h
      _ = e.toFun y := hyEq.symm
  have hx' : e.invFun (e.toFun x) = e.invFun (e.toFun y) :=
    _root_.congrArg e.invFun h'
  exact hx.symm.trans <| hx'.trans hy

@[simp] theorem eq_iff_toEq_eq
    (x y : PathRwQuot A a b) :
    x = y ↔ toEq (A := A) x = toEq (A := A) y := by
  constructor
  · intro h; cases h; rfl
  · exact eq_of_toEq_eq

instance rwQuot_subsingleton (A : Type u) (a b : A) :
    Subsingleton (PathRwQuot A a b) := by
  classical
  constructor
  intro x y
  have hxEq :
      PathRwQuot.toEq (A := A) x = PathRwQuot.toEq (A := A) y :=
    Subsingleton.elim _ _
  exact PathRwQuot.eq_of_toEq_eq (A := A) (a := a) (b := b) hxEq

end PathRwQuot

namespace PathRwQuot

@[simp] theorem sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p)) :
        PathRwQuot A (f a1) (f a2)) =
      Quot.mk _ (Path.congrArg f p) := by
  apply Quot.sound
  exact rweq_sum_rec_inl_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p)) :
        PathRwQuot A (g b1) (g b2)) =
      Quot.mk _ (Path.congrArg g p) := by
  apply Quot.sound
  exact rweq_sum_rec_inr_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    (Quot.mk _ (Path.prodMk (Path.fst p) (Path.snd p)) :
        PathRwQuot (Prod α β) (a₁, b₁) (a₂, b₂))
      = Quot.mk _ p := by
  apply Quot.sound
  exact rweq_prod_eta (α := α) (β := β) (p := p)

@[simp] theorem sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    (Quot.mk _ (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) :
        PathRwQuot (Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) =
      Quot.mk _ p := by
  apply Quot.sound
  exact rweq_sigma_eta (A := A) (B := B) (p := p)

@[simp] theorem sigma_snd_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    (Quot.mk _
        (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q)) :
        PathRwQuot (B a2)
          (transport (A := A) (D := fun a => B a) p b1) b2) =
      Quot.mk _ q := by
  apply Quot.sound
  exact rweq_sigmaSnd_sigmaMk (A := A) (B := B) (p := p) (q := q)

@[simp] theorem sigma_refl_ofEq {A : Type u} {B : A → Type u}
    (a : A) (b : B a) :
    (Quot.mk _
        (Path.sigmaMk (B := B) (Path.refl a)
          (Path.ofEq (A := B a) (a := b) (b := b) rfl)) :
        PathRwQuot (Sigma B) (Sigma.mk a b) (Sigma.mk a b)) =
      PathRwQuot.refl (A := Sigma B) (Sigma.mk a b) := by
  apply Quot.sound
  exact
    rweq_sigmaMk_refl (A := A) (B := B) (a := a) (b := b)

@[simp] theorem fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    (Quot.mk _ (Path.lamCongr (fun x => Path.app p x)) :
        PathRwQuot (α → β) f g) = Quot.mk _ p := by
  apply Quot.sound
  exact rweq_fun_eta (α := α) (β := β) (p := p)

end PathRwQuot

namespace Context

variable {A : Type u} {B : Type u}
variable (C : Context A B)

/-- Lift a unary context action to the quotient level. -/
@[simp] def mapQuot {a b : A} :
    PathRwQuot A a b → PathRwQuot B (C.fill a) (C.fill b) :=
  Quot.lift
    (fun p => Quot.mk _ (Context.map (A := A) (B := B) C p))
    (by
      intro p q h
      exact Quot.sound
        (rweq_context_map_of_rweq (A := A) (B := B) (Ctx := C) h))

variable {C}

@[simp] theorem mapQuot_mk {a b : A} (p : Path a b) :
    mapQuot (A := A) (B := B) C (Quot.mk _ p) =
      Quot.mk _ (Context.map (A := A) (B := B) C p) := rfl

@[simp] theorem toEq_mapQuot {a b : A}
    (x : PathRwQuot A a b) :
    PathRwQuot.toEq (A := B) (mapQuot (A := A) (B := B) C x) =
      _root_.congrArg C.fill (PathRwQuot.toEq (A := A) x) := by
  refine Quot.inductionOn x (fun p => ?_)
  change (Context.map (A := A) (B := B) C p).toEq =
    _root_.congrArg C.fill p.toEq
  exact Context.map_toEq (A := A) (B := B) (C := C) (p := p)

@[simp] theorem mapQuot_refl (a : A) :
    mapQuot (A := A) (B := B) C (PathRwQuot.refl (A := A) a) =
      PathRwQuot.refl (A := B) (C.fill a) := by
  change
    Quot.mk _ (Context.map (A := A) (B := B) C (Path.refl a)) =
      Quot.mk _ (Path.refl (C.fill a))
  apply Quot.sound
  exact
    (rweq_of_eq
      (Context.map_refl (A := A) (B := B) (C := C) (a := a)))

@[simp] theorem mapQuot_invA {a b : A}
    (x : PathRwQuot A a b) :
    mapQuot (A := A) (B := B) C (PathRwQuot.invA (A := A) x) =
      PathRwQuot.invA (A := B)
        (mapQuot (A := A) (B := B) C x) := by
  refine Quot.inductionOn x (fun p => ?_)
  change Quot.mk _ (Context.map (A := A) (B := B) C (Path.symm p)) =
    Quot.mk _ (Path.symm (Context.map (A := A) (B := B) C p))
  apply Quot.sound
  exact
    (rweq_of_eq
      (Context.map_symm (A := A) (B := B) (C := C) (p := p)))

@[simp] theorem mapQuot_ofEq {a b : A} (h : a = b) :
    mapQuot (A := A) (B := B) C
        (PathRwQuot.ofEq (A := A) (a := a) (b := b) h) =
      PathRwQuot.ofEq (A := B)
        (a := C.fill a) (b := C.fill b)
        (_root_.congrArg C.fill h) := by
  change
    Quot.mk _
        (Context.map (A := A) (B := B) C
          (Path.ofEq (A := A) (a := a) (b := b) h)) =
      Quot.mk _
        (Path.ofEq (A := B)
          (a := C.fill a) (b := C.fill b)
          (_root_.congrArg C.fill h))
  apply Quot.sound
  exact
    (rweq_of_eq
      (Context.map_ofEq (A := A) (B := B) (C := C) (h := h)))

@[simp] theorem mapQuot_cmpA {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    mapQuot (A := A) (B := B) C (PathRwQuot.cmpA (A := A) x y) =
      PathRwQuot.cmpA (A := B)
        (mapQuot (A := A) (B := B) C x)
        (mapQuot (A := A) (B := B) C y) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q => ?_))
  change Quot.mk _ (Context.map (A := A) (B := B) C (Path.trans p q)) =
    Quot.mk _
      (Path.trans
        (Context.map (A := A) (B := B) C p)
        (Context.map (A := A) (B := B) C q))
  apply Quot.sound
  exact
    (rweq_of_eq
      (Context.map_trans (A := A) (B := B) (C := C) (p := p) (q := q)))

end Context

end Path
end ComputationalPaths
