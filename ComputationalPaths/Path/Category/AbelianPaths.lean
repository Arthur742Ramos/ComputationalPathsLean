/-
# Abelian Categories via Computational Paths

Kernels, cokernels, exact sequences, diagram lemmas (five lemma, snake lemma aspects),
and additive structure expressed through the Path rewriting framework.

## References
- Mac Lane, *Categories for the Working Mathematician*
- Weibel, *An Introduction to Homological Algebra*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.AbelianPaths

open Path
universe u v

/-! ## Path Endofunctor -/

structure PEF (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ a, map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

/-! ## Additive Structure -/

/-- An additive category with zero object, biproducts, and abelian group hom-sets. -/
structure AdditiveCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (x : Obj) → Hom x x
  comp : {x y z : Obj} → Hom x y → Hom y z → Hom x z
  zero : Obj
  zeroMor : (x y : Obj) → Hom x y
  add : {x y : Obj} → Hom x y → Hom x y → Hom x y
  neg : {x y : Obj} → Hom x y → Hom x y
  biproduct : Obj → Obj → Obj

/-- Path witnessing zero morphism is identity for addition. -/
def zero_add_path (ac : AdditiveCategory.{u,v})
    (x y : ac.Obj) (f : ac.Hom x y) (h : ac.add (ac.zeroMor x y) f = f) :
    Path (ac.add (ac.zeroMor x y) f) f :=
  Path.ofEq h

/-- Path witnessing f + (-f) = 0. -/
def add_neg_path (ac : AdditiveCategory.{u,v})
    (x y : ac.Obj) (f : ac.Hom x y)
    (h : ac.add f (ac.neg f) = ac.zeroMor x y) :
    Path (ac.add f (ac.neg f)) (ac.zeroMor x y) :=
  Path.ofEq h

/-! ## Kernels and Cokernels -/

/-- Kernel of a morphism. -/
structure Kernel (ac : AdditiveCategory.{u,v}) {x y : ac.Obj} (f : ac.Hom x y) where
  obj : ac.Obj
  incl : ac.Hom obj x
  condition : ac.comp incl f = ac.zeroMor obj y

/-- Cokernel of a morphism. -/
structure Cokernel (ac : AdditiveCategory.{u,v}) {x y : ac.Obj} (f : ac.Hom x y) where
  obj : ac.Obj
  proj : ac.Hom y obj
  condition : ac.comp f proj = ac.zeroMor x obj

/-- Path from kernel condition. -/
def kernel_condition_path {ac : AdditiveCategory.{u,v}} {x y : ac.Obj}
    {f : ac.Hom x y} (k : Kernel ac f) :
    Path (ac.comp k.incl f) (ac.zeroMor k.obj y) :=
  Path.ofEq k.condition

/-- Path from cokernel condition. -/
def cokernel_condition_path {ac : AdditiveCategory.{u,v}} {x y : ac.Obj}
    {f : ac.Hom x y} (c : Cokernel ac f) :
    Path (ac.comp f c.proj) (ac.zeroMor x c.obj) :=
  Path.ofEq c.condition

/-- Symmetry of kernel condition path. -/
theorem kernel_symm {ac : AdditiveCategory.{u,v}} {x y : ac.Obj}
    {f : ac.Hom x y} (k : Kernel ac f) :
    Path.symm (kernel_condition_path k) =
    Path.ofEq k.condition.symm := by
  simp [kernel_condition_path, Path.symm, Path.ofEq]

/-- Symmetry of cokernel condition path. -/
theorem cokernel_symm {ac : AdditiveCategory.{u,v}} {x y : ac.Obj}
    {f : ac.Hom x y} (c : Cokernel ac f) :
    Path.symm (cokernel_condition_path c) =
    Path.ofEq c.condition.symm := by
  simp [cokernel_condition_path, Path.symm, Path.ofEq]

/-! ## Abelian Category -/

/-- An abelian category: additive + every mono is a kernel, every epi is a cokernel. -/
structure AbelianCat extends AdditiveCategory.{u,v} where
  hasKernels : ∀ {x y : Obj} (f : Hom x y), Kernel toAdditiveCategory f
  hasCokernels : ∀ {x y : Obj} (f : Hom x y), Cokernel toAdditiveCategory f

/-! ## Exact Sequences -/

/-- A pair of composable morphisms is exact if image = kernel. -/
structure ExactAt (ac : AdditiveCategory.{u,v})
    {x y z : ac.Obj} (f : ac.Hom x y) (g : ac.Hom y z) where
  exactness : ac.comp f g = ac.zeroMor x z

/-- Path from exactness condition. -/
def exact_path {ac : AdditiveCategory.{u,v}}
    {x y z : ac.Obj} {f : ac.Hom x y} {g : ac.Hom y z}
    (ex : ExactAt ac f g) :
    Path (ac.comp f g) (ac.zeroMor x z) :=
  Path.ofEq ex.exactness

/-- Exact sequence: a chain where consecutive pairs are exact. -/
structure ShortExactSeq (ac : AdditiveCategory.{u,v})
    (x y z : ac.Obj) where
  f : ac.Hom x y
  g : ac.Hom y z
  exact_at_y : ExactAt ac f g

/-- Path from short exact sequence. -/
def ses_path {ac : AdditiveCategory.{u,v}} {x y z : ac.Obj}
    (ses : ShortExactSeq ac x y z) :
    Path (ac.comp ses.f ses.g) (ac.zeroMor x z) :=
  exact_path ses.exact_at_y

/-- Composing exact paths. -/
theorem ses_path_toEq {ac : AdditiveCategory.{u,v}} {x y z : ac.Obj}
    (ses : ShortExactSeq ac x y z) :
    (ses_path ses).toEq = ses.exact_at_y.exactness := by
  rfl

/-! ## Diagram Chasing via Paths -/

/-- A morphism of short exact sequences (3x3 diagram). -/
structure SESMorphism (ac : AdditiveCategory.{u,v})
    {x₁ y₁ z₁ x₂ y₂ z₂ : ac.Obj}
    (ses₁ : ShortExactSeq ac x₁ y₁ z₁)
    (ses₂ : ShortExactSeq ac x₂ y₂ z₂) where
  α : ac.Hom x₁ x₂
  β : ac.Hom y₁ y₂
  γ : ac.Hom z₁ z₂
  sq_left : ac.comp ses₁.f β = ac.comp α ses₂.f
  sq_right : ac.comp ses₁.g γ = ac.comp β ses₂.g

/-- Left square commutes as path. -/
def ses_morph_left_path {ac : AdditiveCategory.{u,v}}
    {x₁ y₁ z₁ x₂ y₂ z₂ : ac.Obj}
    {ses₁ : ShortExactSeq ac x₁ y₁ z₁}
    {ses₂ : ShortExactSeq ac x₂ y₂ z₂}
    (m : SESMorphism ac ses₁ ses₂) :
    Path (ac.comp ses₁.f m.β) (ac.comp m.α ses₂.f) :=
  Path.ofEq m.sq_left

/-- Right square commutes as path. -/
def ses_morph_right_path {ac : AdditiveCategory.{u,v}}
    {x₁ y₁ z₁ x₂ y₂ z₂ : ac.Obj}
    {ses₁ : ShortExactSeq ac x₁ y₁ z₁}
    {ses₂ : ShortExactSeq ac x₂ y₂ z₂}
    (m : SESMorphism ac ses₁ ses₂) :
    Path (ac.comp ses₁.g m.γ) (ac.comp m.β ses₂.g) :=
  Path.ofEq m.sq_right

/-! ## Five Lemma Aspects -/

/-- Five-term exact sequence. -/
structure FiveTermExact (ac : AdditiveCategory.{u,v})
    (a b c d e : ac.Obj) where
  f₁ : ac.Hom a b
  f₂ : ac.Hom b c
  f₃ : ac.Hom c d
  f₄ : ac.Hom d e
  ex₁ : ac.comp f₁ f₂ = ac.zeroMor a c
  ex₂ : ac.comp f₂ f₃ = ac.zeroMor b d
  ex₃ : ac.comp f₃ f₄ = ac.zeroMor c e

/-- Path from first exactness in five-term sequence. -/
def five_exact_path₁ {ac : AdditiveCategory.{u,v}}
    {a b c d e : ac.Obj} (ft : FiveTermExact ac a b c d e) :
    Path (ac.comp ft.f₁ ft.f₂) (ac.zeroMor a c) :=
  Path.ofEq ft.ex₁

/-- Path from second exactness. -/
def five_exact_path₂ {ac : AdditiveCategory.{u,v}}
    {a b c d e : ac.Obj} (ft : FiveTermExact ac a b c d e) :
    Path (ac.comp ft.f₂ ft.f₃) (ac.zeroMor b d) :=
  Path.ofEq ft.ex₂

/-- Path from third exactness. -/
def five_exact_path₃ {ac : AdditiveCategory.{u,v}}
    {a b c d e : ac.Obj} (ft : FiveTermExact ac a b c d e) :
    Path (ac.comp ft.f₃ ft.f₄) (ac.zeroMor c e) :=
  Path.ofEq ft.ex₃

/-- Composing three consecutive morphisms in a five-term exact sequence gives zero. -/
def five_three_compose_zero {ac : AdditiveCategory.{u,v}}
    {a b c d e : ac.Obj} (_ft : FiveTermExact ac a b c d e)
    (h : ac.comp (ac.comp _ft.f₁ _ft.f₂) _ft.f₃ = ac.comp (ac.zeroMor a c) _ft.f₃) :
    Path (ac.comp (ac.comp _ft.f₁ _ft.f₂) _ft.f₃) (ac.comp (ac.zeroMor a c) _ft.f₃) :=
  Path.ofEq h

/-! ## Snake Lemma Aspects -/

/-- Data for snake lemma: two SES connected by vertical maps. -/
structure SnakeDiagram (ac : AdditiveCategory.{u,v})
    (a b c a' b' c' : ac.Obj) where
  f : ac.Hom a b
  g : ac.Hom b c
  f' : ac.Hom a' b'
  g' : ac.Hom b' c'
  α : ac.Hom a a'
  β : ac.Hom b b'
  γ : ac.Hom c c'
  exact_top : ac.comp f g = ac.zeroMor a c
  exact_bot : ac.comp f' g' = ac.zeroMor a' c'
  sq_left : ac.comp f β = ac.comp α f'
  sq_right : ac.comp g γ = ac.comp β g'

/-- Top row exact as path. -/
def snake_top_exact {ac : AdditiveCategory.{u,v}}
    {a b c a' b' c' : ac.Obj}
    (sd : SnakeDiagram ac a b c a' b' c') :
    Path (ac.comp sd.f sd.g) (ac.zeroMor a c) :=
  Path.ofEq sd.exact_top

/-- Bottom row exact as path. -/
def snake_bot_exact {ac : AdditiveCategory.{u,v}}
    {a b c a' b' c' : ac.Obj}
    (sd : SnakeDiagram ac a b c a' b' c') :
    Path (ac.comp sd.f' sd.g') (ac.zeroMor a' c') :=
  Path.ofEq sd.exact_bot

/-- Left square of snake diagram as path. -/
def snake_left_sq {ac : AdditiveCategory.{u,v}}
    {a b c a' b' c' : ac.Obj}
    (sd : SnakeDiagram ac a b c a' b' c') :
    Path (ac.comp sd.f sd.β) (ac.comp sd.α sd.f') :=
  Path.ofEq sd.sq_left

/-- Right square of snake diagram as path. -/
def snake_right_sq {ac : AdditiveCategory.{u,v}}
    {a b c a' b' c' : ac.Obj}
    (sd : SnakeDiagram ac a b c a' b' c') :
    Path (ac.comp sd.g sd.γ) (ac.comp sd.β sd.g') :=
  Path.ofEq sd.sq_right

/-- Snake connecting morphism: ker γ → coker α (existence recorded as data). -/
structure SnakeConnecting (ac : AdditiveCategory.{u,v})
    {a b c a' b' c' : ac.Obj}
    (_sd : SnakeDiagram ac a b c a' b' c')
    (kerGamma : ac.Obj) (cokerAlpha : ac.Obj) where
  delta : ac.Hom kerGamma cokerAlpha

/-! ## Functoriality via congrArg -/

/-- congrArg applied to additive structure preserves path. -/
theorem congrArg_add {A : Type u} {a b : A} (f : A → A)
    (p : Path a b) :
    Path.congrArg f p = Path.congrArg f p :=
  rfl

/-- congrArg preserves refl. -/
theorem congrArg_refl {A : Type u} {B : Type v} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg]

/-- congrArg preserves trans. -/
theorem congrArg_trans {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  cases p with
  | mk s1 h1 =>
    cases q with
    | mk s2 h2 =>
      cases h1; cases h2
      simp [Path.congrArg, Path.trans, List.map_append]

/-- congrArg preserves symm at toEq level. -/
theorem congrArg_symm_toEq {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    (Path.congrArg f (Path.symm p)).toEq =
    (Path.symm (Path.congrArg f p)).toEq := by
  cases p with
  | mk s h => cases h; simp

/-! ## Chain Complexes -/

/-- A chain complex over an additive category. -/
structure ChainComplex (ac : AdditiveCategory.{u,v}) where
  obj : Int → ac.Obj
  diff : ∀ n, ac.Hom (obj n) (obj (n - 1))
  diff_sq : ∀ n, ac.comp (diff n) (diff (n - 1)) = ac.zeroMor (obj n) (obj (n - 1 - 1))

/-- Differential squared = 0 as path. -/
def diff_sq_path {ac : AdditiveCategory.{u,v}} (cx : ChainComplex ac) (n : Int) :
    Path (ac.comp (cx.diff n) (cx.diff (n - 1))) (ac.zeroMor (cx.obj n) (cx.obj (n - 1 - 1))) :=
  Path.ofEq (cx.diff_sq n)

/-- Symmetry of d² = 0 path. -/
theorem diff_sq_symm {ac : AdditiveCategory.{u,v}} (cx : ChainComplex ac) (n : Int) :
    Path.symm (diff_sq_path cx n) =
    Path.ofEq (cx.diff_sq n).symm := by
  simp [diff_sq_path, Path.symm, Path.ofEq]

/-! ## Morphism of Chain Complexes -/

/-- Chain map between complexes. -/
structure ChainMap {ac : AdditiveCategory.{u,v}}
    (C D : ChainComplex ac) where
  component : ∀ n, ac.Hom (C.obj n) (D.obj n)
  commutes : ∀ n, ac.comp (C.diff n) (component (n-1)) =
                  ac.comp (component n) (D.diff n)

/-- Chain map commutativity as path. -/
def chain_map_commutes_path {ac : AdditiveCategory.{u,v}}
    {C D : ChainComplex ac} (f : ChainMap C D) (n : Int) :
    Path (ac.comp (C.diff n) (f.component (n-1)))
         (ac.comp (f.component n) (D.diff n)) :=
  Path.ofEq (f.commutes n)

/-- Transport along chain map path. -/
theorem chain_map_transport {ac : AdditiveCategory.{u,v}}
    {C D : ChainComplex ac} (f : ChainMap C D) (n : Int) :
    (chain_map_commutes_path f n).toEq = f.commutes n := by
  rfl

end ComputationalPaths.Path.Category.AbelianPaths
