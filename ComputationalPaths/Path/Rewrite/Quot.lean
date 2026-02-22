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
abbrev rwEqRel (A : Type u) (a b : A) : Path a b → Path a b → Prop :=
  RwEqProp

noncomputable instance {A : Type u} {a b : A} {p q : Path a b} :
    Coe (RwEq p q) (rwEqRel A a b p q) where
  coe h := rweqProp_of_rweq h

noncomputable instance {A : Type u} {a b : A} {p q : Path a b} :
    Coe (rwEqRel A a b p q) (RwEq p q) where
  coe h := rweq_of_rweqProp h

/-- Rewrite equality induces a setoid on computational paths. -/
noncomputable def rwEqSetoid (A : Type u) (a b : A) : Setoid (Path a b) where
  r := rwEqRel A a b
  iseqv :=
    { refl := fun p => rweqProp_of_rweq (rweq_refl (p := p))
      symm := fun {_ _} h =>
        match h with
        | ⟨h'⟩ => rweqProp_of_rweq (rweq_symm h')
      trans := fun {_ _ _} h₁ h₂ =>
        match h₁, h₂ with
        | ⟨h₁'⟩, ⟨h₂'⟩ => rweqProp_of_rweq (rweq_trans h₁' h₂') }

@[simp] theorem rwEqSetoid_r {A : Type u} {a b : A} :
    (rwEqSetoid A a b).r = rwEqRel A a b :=
  rfl

noncomputable instance pathRwEqSetoid (A : Type u) (a b : A) :
    Setoid (Path a b) :=
  rwEqSetoid A a b

/-- Paths modulo rewrite equality, mirroring the paper's notion of canonical proofs. -/
abbrev PathRwQuot (A : Type u) (a b : A) :=
  Quot (rwEqRel A a b)

end Setoid

namespace PathRwQuot

variable {A : Type u} {a b : A}

open Quot

/-- Reflexive element in the quotient. -/
noncomputable def refl (a : A) : PathRwQuot A a a :=
  Quot.mk _ (Path.refl a)

/-- Symmetry descends to the quotient. -/
noncomputable def symm {a b : A} :
    PathRwQuot A a b → PathRwQuot A b a := fun x =>
  Quot.liftOn x (fun p => Quot.mk _ (Path.symm p))
    (by
      intro p q h
      exact Quot.sound (rweqProp_of_rweq (rweq_symm_congr (rweq_of_rweqProp h))))

/-- Composition descends to the quotient. -/
noncomputable def trans {a b c : A} :
    PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c :=
  fun x y =>
    Quot.liftOn x (fun p : Path a b =>
      Quot.liftOn y (fun q : Path b c => Quot.mk _ (Path.trans p q))
        (by
          intro q₁ q₂ hq
          exact Quot.sound
            (rweqProp_of_rweq (rweq_trans_congr_right p (rweq_of_rweqProp hq)))))
      (by
        intro p₁ p₂ hp
        refine Quot.inductionOn y (fun q =>
          Quot.sound
            (rweqProp_of_rweq (rweq_trans_congr_left q (rweq_of_rweqProp hp)))))

/-- Coerce a propositional equality to the path quotient. -/
@[simp] noncomputable def ofEq {a b : A} (h : a = b) : PathRwQuot A a b :=
  Quot.mk _ (Path.stepChain h)

/-- Forget the rewrite trace and recover the underlying equality. -/
noncomputable def toEq {a b : A} : PathRwQuot A a b → a = b :=
  Quot.lift (fun p : Path a b => p.toEq)
    (by
      intro p q h
      exact rweq_toEq (rweq_of_rweqProp h))

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

@[simp] theorem symm_mk {a b : A} (p : Path a b) :
    symm (A := A) (Quot.mk _ p) = Quot.mk _ (Path.symm p) := rfl

@[simp] theorem trans_mk {a b c : A}
    (p : Path a b) (q : Path b c) :
    trans (A := A) (Quot.mk _ p) (Quot.mk _ q) =
      Quot.mk _ (Path.trans p q) := rfl

@[simp] theorem symm_symm {a b : A}
    (x : PathRwQuot A a b) :
    symm (A := A) (symm x) = x := by
  refine Quot.inductionOn x (fun p => by
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_step (Step.symm_symm (A := A) p))

@[simp] theorem trans_refl_left {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (refl a) x = x := by
  refine Quot.inductionOn x (fun p => by
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_step (Step.trans_refl_left (A := A) p))

@[simp] theorem trans_refl_right {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (refl b) = x := by
  refine Quot.inductionOn x (fun p => by
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_step (Step.trans_refl_right (A := A) p))

@[simp] theorem trans_symm {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (symm x) = refl a := by
  refine Quot.inductionOn x (fun p => by
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_step (Step.trans_symm (A := A) p))

@[simp] theorem symm_trans {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (symm x) x = refl b := by
  refine Quot.inductionOn x (fun p => by
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
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
        apply (fun h => Quot.sound (rweqProp_of_rweq h))
        exact rweq_of_step
          (Step.trans_assoc (A := A) (p := p) (q := q) (r := r)))))

/-- Paper-style notation `cmpA` for quotient composition. -/
@[simp] noncomputable def cmpA {a b c : A} :
    PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c :=
  trans (A := A)

/-- Paper-style notation `invA` for quotient inversion. -/
@[simp] noncomputable def invA {a b : A} :
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

@[simp] noncomputable def normalPath {a b : A} (x : PathRwQuot A a b) : Path a b :=
  Path.stepChain (A := A) (a := a) (b := b) (toEq x)

@[simp] theorem normalPath_isNormal {a b : A}
    (x : PathRwQuot A a b) :
    IsNormal (A := A) (a := a) (b := b) (normalPath (A := A) (x := x)) := by
  unfold normalPath IsNormal
  rfl

@[simp] theorem normalPath_mk {a b : A} (p : Path a b) :
    normalPath (A := A) (x := Quot.mk _ p) =
      normalize (A := A) (a := a) (b := b) p := rfl

@[simp] noncomputable def normalForm {a b : A}
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

@[simp] theorem normalPath_toEq {a b : A}
    (x : PathRwQuot A a b) :
    (normalPath (A := A) (x := x)).toEq =
      PathRwQuot.toEq (A := A) x := rfl

/-! ## Functorial operations (congrArg) -/

/-- Apply a function to a quotient path (functorial action). -/
noncomputable def congrArg (A : Type u) (B : Type u) (f : A → B) {a a' : A}
    (x : PathRwQuot A a a') : PathRwQuot B (f a) (f a') :=
  Quot.lift
    (fun p => Quot.mk _ (Path.congrArg f p))
    (fun _ _ h => Quot.sound (rweqProp_of_rweq (rweq_congrArg_of_rweq f (rweq_of_rweqProp h))))
    x

@[simp] theorem congrArg_mk (A : Type u) (B : Type u) (f : A → B) {a a' : A}
    (p : Path a a') :
    congrArg A B f (Quot.mk _ p) = Quot.mk _ (Path.congrArg f p) := rfl

@[simp] theorem congrArg_refl (A : Type u) (B : Type u) (f : A → B) (a : A) :
    congrArg A B f (refl a) = refl (f a) := by
  change Quot.mk _ (Path.congrArg f (Path.refl a)) = Quot.mk _ (Path.refl (f a))
  rfl

@[simp] theorem congrArg_trans (A : Type u) (B : Type u) (f : A → B) {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    congrArg A B f (trans x y) = trans (congrArg A B f x) (congrArg A B f y) := by
  induction x using Quot.ind with
  | _ p =>
    induction y using Quot.ind with
    | _ q =>
      change Quot.mk _ (Path.congrArg f (Path.trans p q)) =
        Quot.mk _ (Path.trans (Path.congrArg f p) (Path.congrArg f q))
      apply (fun h => Quot.sound (rweqProp_of_rweq h))
      exact rweq_of_eq (Path.congrArg_trans f p q)

@[simp] theorem congrArg_symm (A : Type u) (B : Type u) (f : A → B) {a b : A}
    (x : PathRwQuot A a b) :
    congrArg A B f (symm x) = symm (congrArg A B f x) := by
  induction x using Quot.ind with
  | _ p =>
    change Quot.mk _ (Path.congrArg f (Path.symm p)) =
      Quot.mk _ (Path.symm (Path.congrArg f p))
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_eq (Path.congrArg_symm f p)

/-- Identity function preserves paths. -/
@[simp] theorem congrArg_id (A : Type u) (a a' : A) (x : PathRwQuot A a a') :
    congrArg A A id x = x := by
  induction x using Quot.ind with
  | _ p =>
    change Quot.mk _ (Path.congrArg id p) = Quot.mk _ p
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_of_eq (Path.congrArg_id p)

/-- Composition of functions composes on paths. -/
@[simp] theorem congrArg_comp (A : Type u) (B : Type u) (C : Type u)
    (f : A → B) (g : B → C) {a a' : A} (x : PathRwQuot A a a') :
    congrArg B C g (congrArg A B f x) = congrArg A C (g ∘ f) x := by
  induction x using Quot.ind with
  | _ p =>
    change Quot.mk _ (Path.congrArg g (Path.congrArg f p)) =
      Quot.mk _ (Path.congrArg (g ∘ f) p)
    apply (fun h => Quot.sound (rweqProp_of_rweq h))
    exact rweq_symm (rweq_of_eq (Path.congrArg_comp g f p))

end PathRwQuot

namespace PathRwQuot

@[simp] theorem sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p)) :
        PathRwQuot A (f a1) (f a2)) =
      Quot.mk _ (Path.congrArg f p) := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_sum_rec_inl_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p)) :
        PathRwQuot A (g b1) (g b2)) =
      Quot.mk _ (Path.congrArg g p) := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_sum_rec_inr_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    (Quot.mk _ (Path.prodMk (Path.fst p) (Path.snd p)) :
        PathRwQuot (Prod α β) (a₁, b₁) (a₂, b₂))
      = Quot.mk _ p := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_prod_eta (α := α) (β := β) (p := p)

@[simp] theorem fst_prodMk {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Quot.mk _ (Path.fst (Path.prodMk p q)) :
        PathRwQuot α a₁ a₂) =
      Quot.mk _ p := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_fst_prodMk (α := α) (β := β) (p := p) (q := q)

@[simp] theorem snd_prodMk {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Quot.mk _ (Path.snd (Path.prodMk p q)) :
        PathRwQuot β b₁ b₂) =
      Quot.mk _ q := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_snd_prodMk (α := α) (β := β) (p := p) (q := q)

@[simp] theorem congrArg_prod_map {α β α' β' : Type u}
    (g : α → α') (h : β → β')
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Quot.mk _ (Path.congrArg (fun x : α × β => (g x.1, h x.2)) (Path.prodMk p q)) :
        PathRwQuot (α' × β') (g a₁, h b₁) (g a₂, h b₂)) =
      Quot.mk _ (Path.prodMk (Path.congrArg g p) (Path.congrArg h q)) := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_congrArg_prod_map (α := α) (β := β) (α' := α') (β' := β') (g := g) (h := h) (p := p) (q := q)

@[simp] theorem sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    (Quot.mk _ (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) :
        PathRwQuot (Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) =
      Quot.mk _ p := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_sigma_eta (A := A) (B := B) (p := p)

@[simp] theorem sigma_refl_ofEq {A : Type u} {B : A → Type u}
    (a : A) (b : B a) :
    (Quot.mk _
        (Path.sigmaMk (B := B) (Path.refl a)
          (Path.stepChain (A := B a) (a := b) (b := b) rfl)) :
        PathRwQuot (Sigma B) (Sigma.mk a b) (Sigma.mk a b)) =
      PathRwQuot.refl (A := Sigma B) (Sigma.mk a b) := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact
    rweq_sigmaMk_refl (A := A) (B := B) (a := a) (b := b)

@[simp] theorem fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    (Quot.mk _ (Path.lamCongr (fun x => Path.app p x)) :
        PathRwQuot (α → β) f g) = Quot.mk _ p := by
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_fun_eta (α := α) (β := β) (p := p)

end PathRwQuot

namespace Context

variable {A : Type u} {B : Type u}
variable (C : Context A B)

/-- Lift a unary context action to the quotient level. -/
@[simp] noncomputable def mapQuot {a b : A} :
    PathRwQuot A a b → PathRwQuot B (C.fill a) (C.fill b) :=
  Quot.lift
    (fun p => Quot.mk _ (Context.map (A := A) (B := B) C p))
    (by
      intro p q h
      exact Quot.sound
        (rweqProp_of_rweq
          (rweq_context_map_of_rweq (A := A) (B := B) (Ctx := C) (rweq_of_rweqProp h))))

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
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
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
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
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
          (Path.stepChain (A := A) (a := a) (b := b) h)) =
      Quot.mk _
        (Path.stepChain (A := B)
          (a := C.fill a) (b := C.fill b)
          (_root_.congrArg C.fill h))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
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
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact
    (rweq_of_eq
      (Context.map_trans (A := A) (B := B) (C := C) (p := p) (q := q)))

end Context

set_option linter.unnecessarySimpa false

namespace DepContext

variable {A : Type u} {B : A → Type u}
variable (C : DepContext A B)

/-- Lift a dependent context to rewrite-quotiented paths. -/
@[simp] noncomputable def mapQuot {a₁ a₂ : A} (x : PathRwQuot A a₁ a₂) :
    PathRwQuot (B a₂)
      (Path.transport (A := A) (D := fun a => B a)
        (PathRwQuot.normalPath (A := A) (x := x)) (C.fill a₁))
      (C.fill a₂) :=
  Quot.mk _
    (DepContext.map (A := A) (B := B) C
      (PathRwQuot.normalPath (A := A) (x := x)))

variable {C}

@[simp] theorem toEq_mapQuot {a₁ a₂ : A}
    (x : PathRwQuot A a₁ a₂) :
    PathRwQuot.toEq
        (mapQuot (A := A) (B := B) C x) =
      (DepContext.map (A := A) (B := B) C
        (PathRwQuot.normalPath (A := A) (x := x))).toEq := rfl

@[simp] theorem mapQuot_refl (a : A) :
    mapQuot (A := A) (B := B) C (PathRwQuot.refl (A := A) a) =
      PathRwQuot.refl (C.fill a) := by
  change
    Quot.mk _ (DepContext.map (A := A) (B := B) C (Path.refl a)) =
      Quot.mk _ (Path.refl (C.fill a))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact
    (rweq_of_eq
      (DepContext.map_refl (A := A) (B := B) (C := C) (a := a)))

end DepContext

set_option linter.unnecessarySimpa false

namespace BiContext

variable {A : Type u} {B : Type u} {C : Type u}
variable (K : BiContext A B C)

/-- Lift substitution along the left hole of a binary context to the quotient level. -/
@[simp] noncomputable def mapLeftQuot {a₁ a₂ : A} (b : B) :
    PathRwQuot A a₁ a₂ →
      PathRwQuot C (K.fill a₁ b) (K.fill a₂ b) :=
  Quot.lift
    (fun p =>
      Quot.mk _
        (BiContext.mapLeft (A := A) (B := B) (C := C) K p b))
    (by
      intro p q h
      exact Quot.sound
        (rweqProp_of_rweq (rweq_biContext_mapLeft_of_rweq
          (A := A) (B := B) (C := C) (K := K) (b := b)
          (p := p) (q := q) (rweq_of_rweqProp h))))

/-- Lift substitution along the right hole of a binary context to the quotient level. -/
@[simp] noncomputable def mapRightQuot {b₁ b₂ : B} (a : A) :
    PathRwQuot B b₁ b₂ →
      PathRwQuot C (K.fill a b₁) (K.fill a b₂) :=
  Quot.lift
    (fun p =>
      Quot.mk _
        (BiContext.mapRight (A := A) (B := B) (C := C) K a p))
    (by
      intro p q h
      exact Quot.sound
        (rweqProp_of_rweq (rweq_biContext_mapRight_of_rweq
          (A := A) (B := B) (C := C) (K := K) (a := a)
          (p := p) (q := q) (rweq_of_rweqProp h))))

/-- Simultaneously substitute along both holes of a binary context in the quotient. -/
@[simp] noncomputable def map2Quot {a₁ a₂ : A} {b₁ b₂ : B}
    (x : PathRwQuot A a₁ a₂) (y : PathRwQuot B b₁ b₂) :
    PathRwQuot C (K.fill a₁ b₁) (K.fill a₂ b₂) :=
  PathRwQuot.cmpA
    (mapLeftQuot (A := A) (B := B) (C := C) K b₁ x)
    (mapRightQuot (A := A) (B := B) (C := C) K a₂ y)

variable {K}

@[simp] theorem mapLeftQuot_mk {a₁ a₂ : A} (b : B) (p : Path a₁ a₂) :
    mapLeftQuot (K := K) (b := b) (Quot.mk _ p) =
      Quot.mk _
        (BiContext.mapLeft (A := A) (B := B) (C := C) K p b) := rfl

@[simp] theorem mapRightQuot_mk {b₁ b₂ : B} (a : A) (p : Path b₁ b₂) :
    mapRightQuot (K := K) (a := a) (Quot.mk _ p) =
      Quot.mk _
        (BiContext.mapRight (A := A) (B := B) (C := C) K a p) := rfl

@[simp] theorem toEq_mapLeftQuot {a₁ a₂ : A} (b : B)
    (x : PathRwQuot A a₁ a₂) :
    PathRwQuot.toEq (A := C)
        (mapLeftQuot (A := A) (B := B) (C := C) (K := K) b x) =
      _root_.congrArg (fun a => K.fill a b)
        (PathRwQuot.toEq (A := A) x) := by
  refine Quot.inductionOn x (fun p => ?_)
  simp

@[simp] theorem toEq_mapRightQuot {b₁ b₂ : B} (a : A)
    (x : PathRwQuot B b₁ b₂) :
    PathRwQuot.toEq (A := C)
        (mapRightQuot (A := A) (B := B) (C := C) (K := K) a x) =
      _root_.congrArg (K.fill a)
        (PathRwQuot.toEq (A := B) x) := by
  refine Quot.inductionOn x (fun p => ?_)
  simp

@[simp] theorem mapLeftQuot_refl (b : B) (a : A) :
    mapLeftQuot (A := A) (B := B) (C := C) (K := K) b
        (PathRwQuot.refl (A := A) a) =
      PathRwQuot.refl (A := C) (K.fill a b) := by
  change Quot.mk _
      (BiContext.mapLeft (A := A) (B := B) (C := C) K (Path.refl a) b) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  have hmap :
      BiContext.mapLeft (A := A) (B := B) (C := C) K (Path.refl a) b =
        Path.refl (K.fill a b) := by
    exact BiContext.mapLeft_refl (A := A) (B := B) (C := C) K a b
  exact rweq_of_eq hmap

@[simp] theorem mapRightQuot_refl (a : A) (b : B) :
    mapRightQuot (A := A) (B := B) (C := C) (K := K) a
        (PathRwQuot.refl (A := B) b) =
      PathRwQuot.refl (A := C) (K.fill a b) := by
  change Quot.mk _
      (BiContext.mapRight (A := A) (B := B) (C := C) K a (Path.refl b)) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  have hmap :
      BiContext.mapRight (A := A) (B := B) (C := C) K a (Path.refl b) =
        Path.refl (K.fill a b) := by
    exact BiContext.mapRight_refl (A := A) (B := B) (C := C) K a b
  exact rweq_of_eq hmap

@[simp] theorem mapLeftQuot_invA {a₁ a₂ : A} (b : B)
    (x : PathRwQuot A a₁ a₂) :
    mapLeftQuot (A := A) (B := B) (C := C) (K := K) b
        (PathRwQuot.invA (A := A) x) =
      PathRwQuot.invA (A := C)
        (mapLeftQuot (A := A) (B := B) (C := C) (K := K) b x) := by
  refine Quot.inductionOn x (fun p => ?_)
  change Quot.mk _ (BiContext.mapLeft (A := A) (B := B) (C := C) K (Path.symm p) b) =
    Quot.mk _ (Path.symm (BiContext.mapLeft (A := A) (B := B) (C := C) K p b))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact
    (rweq_of_eq
      (BiContext.mapLeft_symm (A := A) (B := B) (C := C) (K := K)
        (p := p) (b := b)))

@[simp] theorem mapRightQuot_invA {b₁ b₂ : B} (a : A)
    (x : PathRwQuot B b₁ b₂) :
    mapRightQuot (A := A) (B := B) (C := C) (K := K) a
        (PathRwQuot.invA (A := B) x) =
      PathRwQuot.invA (A := C)
        (mapRightQuot (A := A) (B := B) (C := C) (K := K) a x) := by
  refine Quot.inductionOn x (fun p => ?_)
  change Quot.mk _ (BiContext.mapRight (A := A) (B := B) (C := C) K a (Path.symm p)) =
    Quot.mk _ (Path.symm (BiContext.mapRight (A := A) (B := B) (C := C) K a p))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact
    (rweq_of_eq
      (BiContext.mapRight_symm (A := A) (B := B) (C := C) (K := K)
        (a := a) (p := p)))

@[simp] theorem mapLeftQuot_ofEq {a₁ a₂ : A} (b : B) (h : a₁ = a₂) :
    mapLeftQuot (A := A) (B := B) (C := C) (K := K) b
        (PathRwQuot.ofEq (A := A) (a := a₁) (b := a₂) h) =
      PathRwQuot.ofEq (A := C)
        (a := K.fill a₁ b) (b := K.fill a₂ b)
        (_root_.congrArg (fun a => K.fill a b) h) := by
  change Quot.mk _
      (BiContext.mapLeft (A := A) (B := B) (C := C) K
        (Path.stepChain (A := A) (a := a₁) (b := a₂) h) b) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_of_eq
    (by
      simpa [BiContext.mapLeft, BiContext.fixRight]
        using Context.map_ofEq
          (A := A) (B := C)
          (C := BiContext.fixRight (A := A) (B := B) (C := C) K b)
          (a := a₁) (b := a₂) (h := h))

@[simp] theorem mapRightQuot_ofEq {b₁ b₂ : B} (a : A) (h : b₁ = b₂) :
    mapRightQuot (A := A) (B := B) (C := C) (K := K) a
        (PathRwQuot.ofEq (A := B) (a := b₁) (b := b₂) h) =
      PathRwQuot.ofEq (A := C)
        (a := K.fill a b₁) (b := K.fill a b₂)
        (_root_.congrArg (K.fill a) h) := by
  change Quot.mk _
      (BiContext.mapRight (A := A) (B := B) (C := C) K a
        (Path.stepChain (A := B) (a := b₁) (b := b₂) h)) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_of_eq
    (by
      simpa [BiContext.mapRight, BiContext.fixLeft]
        using Context.map_ofEq
          (A := B) (B := C)
          (C := BiContext.fixLeft (A := A) (B := B) (C := C) K a)
          (a := b₁) (b := b₂) (h := h))

@[simp] theorem mapLeftQuot_cmpA {a₁ a₂ a₃ : A} (b : B)
    (x : PathRwQuot A a₁ a₂) (y : PathRwQuot A a₂ a₃) :
    mapLeftQuot (A := A) (B := B) (C := C) (K := K) b
        (PathRwQuot.cmpA x y) =
      PathRwQuot.cmpA
        (mapLeftQuot (A := A) (B := B) (C := C) (K := K) b x)
        (mapLeftQuot (A := A) (B := B) (C := C) (K := K) b y) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q => ?_))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_of_eq
    (BiContext.mapLeft_trans (A := A) (B := B) (C := C) (K := K)
      (p := p) (q := q) (b := b))

@[simp] theorem mapRightQuot_cmpA {b₁ b₂ b₃ : B} (a : A)
    (x : PathRwQuot B b₁ b₂) (y : PathRwQuot B b₂ b₃) :
    mapRightQuot (A := A) (B := B) (C := C) (K := K) a
        (PathRwQuot.cmpA x y) =
      PathRwQuot.cmpA
        (mapRightQuot (A := A) (B := B) (C := C) (K := K) a x)
        (mapRightQuot (A := A) (B := B) (C := C) (K := K) a y) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q => ?_))
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  exact rweq_of_eq
    (BiContext.mapRight_trans (A := A) (B := B) (C := C) (K := K)
      (a := a) (p := p) (q := q))

@[simp] theorem map2Quot_mk {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    map2Quot (A := A) (B := B) (C := C) (K := K)
        (Quot.mk _ p) (Quot.mk _ q) =
      Quot.mk _ (BiContext.map2 (A := A) (B := B) (C := C) K p q) := by
  rfl

end BiContext

namespace DepBiContext

open Path

variable {A : Type u} {B : Type u} {C : A → B → Type u}
variable (K : DepBiContext A B C)

/-- Lift left-hole substitution of a dependent bi-context to the rewrite quotient. -/
@[simp] noncomputable def mapLeftQuot {a₁ a₂ : A} (b : B)
    (x : PathRwQuot A a₁ a₂) :
    PathRwQuot (C a₂ b)
      (Path.transport (A := A) (D := fun a => C a b)
        (PathRwQuot.normalPath (A := A) (x := x)) (K.fill a₁ b))
      (K.fill a₂ b) :=
  Quot.mk _
    (DepBiContext.mapLeft (A := A) (B := B) (C := C) K
      (PathRwQuot.normalPath (A := A) (x := x)) b)

/-- Lift right-hole substitution of a dependent bi-context to the rewrite quotient. -/
@[simp] noncomputable def mapRightQuot {b₁ b₂ : B} (a : A)
    (y : PathRwQuot B b₁ b₂) :
    PathRwQuot (C a b₂)
      (Path.transport (A := B) (D := fun b => C a b)
        (PathRwQuot.normalPath (A := B) (x := y)) (K.fill a b₁))
      (K.fill a b₂) :=
  Quot.mk _
    (DepBiContext.mapRight (A := A) (B := B) (C := C) K a
      (PathRwQuot.normalPath (A := B) (x := y)))

/-- Simultaneous substitution for a dependent bi-context in the rewrite quotient. -/
@[simp] noncomputable def map2Quot {a₁ a₂ : A} {b₁ b₂ : B}
    (x : PathRwQuot A a₁ a₂) (y : PathRwQuot B b₁ b₂) :
    PathRwQuot (C a₂ b₂)
      (Path.transport (A := B) (D := fun b => C a₂ b)
        (PathRwQuot.normalPath (A := B) (x := y))
        (Path.transport (A := A) (D := fun a => C a b₁)
          (PathRwQuot.normalPath (A := A) (x := x))
          (K.fill a₁ b₁)))
      (K.fill a₂ b₂) :=
  Quot.mk _
    (DepBiContext.map2 (A := A) (B := B) (C := C) K
      (PathRwQuot.normalPath (A := A) (x := x))
      (PathRwQuot.normalPath (A := B) (x := y)))

@[simp] theorem toEq_mapLeftQuot {a₁ a₂ : A} (b : B)
    (x : PathRwQuot A a₁ a₂) :
    PathRwQuot.toEq (A := C a₂ b)
        (mapLeftQuot (A := A) (B := B) (C := C) (K := K) b x) =
      (DepBiContext.mapLeft (A := A) (B := B) (C := C) K
        (PathRwQuot.normalPath (A := A) (x := x)) b).toEq := rfl

@[simp] theorem toEq_mapRightQuot {b₁ b₂ : B} (a : A)
    (y : PathRwQuot B b₁ b₂) :
    PathRwQuot.toEq (A := C a b₂)
        (mapRightQuot (A := A) (B := B) (C := C) (K := K) a y) =
      (DepBiContext.mapRight (A := A) (B := B) (C := C) K a
        (PathRwQuot.normalPath (A := B) (x := y))).toEq := rfl

@[simp] theorem toEq_map2Quot {a₁ a₂ : A} {b₁ b₂ : B}
    (x : PathRwQuot A a₁ a₂) (y : PathRwQuot B b₁ b₂) :
    PathRwQuot.toEq (A := C a₂ b₂)
        (map2Quot (A := A) (B := B) (C := C) (K := K) x y) =
      (DepBiContext.map2 (A := A) (B := B) (C := C) K
        (PathRwQuot.normalPath (A := A) (x := x))
        (PathRwQuot.normalPath (A := B) (x := y))).toEq := rfl

noncomputable def map2_rweq_left
    {a₁ a₂ : A} {b₁ b₂ : B}
    {p q : Path a₁ a₂} (r : Path b₁ b₂) (h : RwEq p q) :
    RwEq (DepBiContext.map2 (A := A) (B := B) (C := C) K p r)
      (DepBiContext.map2 (A := A) (B := B) (C := C) K q r) := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step step =>
      exact RwEq.step
        (Step.depBiContext_map2_congr_left (A := A) (B := B) (C := C)
          (K := K) (r := r) step)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

noncomputable def map2_rweq_right
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) {q r : Path b₁ b₂} (h : RwEq q r) :
    RwEq (DepBiContext.map2 (A := A) (B := B) (C := C) K p q)
      (DepBiContext.map2 (A := A) (B := B) (C := C) K p r) := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step step =>
      exact RwEq.step
        (Step.depBiContext_map2_congr_right (A := A) (B := B) (C := C)
          (K := K) (p := p) step)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

@[simp] theorem mapLeftQuot_refl (b : B) (a : A) :
    mapLeftQuot (A := A) (B := B) (C := C) (K := K) b
        (PathRwQuot.refl (A := A) a) =
      PathRwQuot.refl (A := C a b) (K.fill a b) := by
  change Quot.mk _
      (DepBiContext.mapLeft (A := A) (B := B) (C := C) K (Path.refl a) b) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  have hmap :
      DepBiContext.mapLeft (A := A) (B := B) (C := C) K (Path.refl a) b =
        Path.refl (K.fill a b) := by
    change
        Path.apd (A := A) (B := fun a => C a b)
          (f := fun a => K.fill a b) (Path.refl a) =
          Path.refl (K.fill a b)
    exact
      (Path.apd_refl (A := A) (B := fun a => C a b)
        (f := fun a => K.fill a b) a)
  exact rweq_of_eq hmap

@[simp] theorem mapRightQuot_refl (a : A) (b : B) :
    mapRightQuot (A := A) (B := B) (C := C) (K := K) a
        (PathRwQuot.refl (A := B) b) =
      PathRwQuot.refl (A := C a b) (K.fill a b) := by
  change Quot.mk _
      (DepBiContext.mapRight (A := A) (B := B) (C := C) K a (Path.refl b)) = _
  apply (fun h => Quot.sound (rweqProp_of_rweq h))
  have hmap :
      DepBiContext.mapRight (A := A) (B := B) (C := C) K a (Path.refl b) =
        Path.refl (K.fill a b) := by
    change
        Path.apd (A := B) (B := fun b' => C a b')
          (f := fun b' => K.fill a b') (Path.refl b) =
          Path.refl (K.fill a b)
    exact
      (Path.apd_refl (A := B) (B := fun b' => C a b')
        (f := fun b' => K.fill a b') b)
  exact rweq_of_eq hmap

end DepBiContext

end Path
end ComputationalPaths
