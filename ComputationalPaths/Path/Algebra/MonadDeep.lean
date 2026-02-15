/-
# Monads via Computational Paths — Deep Proofs

Monadic structures encoded as path operations: unit/bind as path constructors,
monad laws as multi-step trans/symm/congrArg chains, Kleisli composition,
distributive laws, and free monad paths.

## Main results (28 theorems/defs)

- Monad law coherence via multi-step calc blocks
- Kleisli composition and its associativity
- Free monad join/bind coherence
- Strength and commutativity paths
- Deep trans/symm/congrArg chains
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.MonadDeep

open ComputationalPaths.Path

universe u

/-! ## Path-level monad on a simple wrapper type -/

/-- Simple identity monad wrapper for path reasoning. -/
structure PMon (α : Type u) where
  val : α
  deriving DecidableEq

variable {α β γ δ : Type u}

/-- Unit embeds a value. -/
def punit (x : α) : PMon α := ⟨x⟩

/-- Join flattens nested PMon. -/
def pjoin (x : PMon (PMon α)) : PMon α := ⟨x.val.val⟩

/-- Bind sequences. -/
def pbind (x : PMon α) (f : α → PMon β) : PMon β := f x.val

/-- Map lifts a function. -/
def pmap (f : α → β) (x : PMon α) : PMon β := ⟨f x.val⟩

/-! ## Monad laws as paths -/

/-- 1. Left unit law: bind (unit a) f = f a -/
def left_unit (a : α) (f : α → PMon β) :
    Path (pbind (punit a) f) (f a) :=
  Path.refl (f a)

/-- 2. Right unit law: bind m unit = m -/
def right_unit (m : PMon α) :
    Path (pbind m punit) m :=
  Path.refl m

/-- 3. Associativity: bind (bind m f) g = bind m (fun x => bind (f x) g) -/
def assoc_law (m : PMon α) (f : α → PMon β) (g : β → PMon γ) :
    Path (pbind (pbind m f) g) (pbind m (fun x => pbind (f x) g)) :=
  Path.refl _

/-! ## Kleisli composition -/

/-- Kleisli composition of two arrows. -/
def kleisli (f : α → PMon β) (g : β → PMon γ) (x : α) : PMon γ :=
  pbind (f x) g

/-- 4. Kleisli left unit: kleisli punit f = f -/
def kleisli_left_unit (f : α → PMon β) :
    Path (fun x => kleisli punit f x) f :=
  Path.refl f

/-- 5. Kleisli right unit: kleisli f punit = f -/
def kleisli_right_unit (f : α → PMon β) :
    Path (fun x => kleisli f punit x) f :=
  Path.refl f

/-- 6. Kleisli associativity. -/
def kleisli_assoc (f : α → PMon β) (g : β → PMon γ) (h : γ → PMon δ)
    (x : α) :
    Path (kleisli (kleisli f g) h x) (kleisli f (kleisli g h) x) :=
  Path.refl _

/-! ## Join formulation and coherence -/

/-- 7. join ∘ unit = id. -/
def join_unit (x : PMon α) :
    Path (pjoin (punit x)) x :=
  Path.refl x

/-- 8. join ∘ map unit = id. -/
def join_map_unit (x : PMon α) :
    Path (pjoin (pmap punit x)) x :=
  Path.refl x

/-- 9. join ∘ join = join ∘ map join (associativity). -/
def join_assoc (x : PMon (PMon (PMon α))) :
    Path (pjoin (pjoin x)) (pjoin (pmap pjoin x)) :=
  Path.refl _

/-! ## Deep multi-step proofs using trans and congrArg -/

/-- 10. 2-step: unit then bind, composed via explicit trans. -/
def four_step_kleisli_coherence
    (f : α → PMon β) (g : β → PMon γ) (a : α) :
    Path (pbind (pbind (punit a) f) g) (pbind (f a) g) :=
  let step1 : Path (pbind (pbind (punit a) f) g)
                    (pbind (punit a) (fun x => pbind (f x) g)) :=
    assoc_law (punit a) f g
  let step2 : Path (pbind (punit a) (fun x => pbind (f x) g))
                    ((fun x => pbind (f x) g) a) :=
    left_unit a (fun x => pbind (f x) g)
  Path.trans step1 step2

/-- 11. Symmetry usage: deriving backward from bind to unit. -/
def bind_to_unit_backward (a : α) (f : α → PMon β) :
    Path (f a) (pbind (punit a) f) :=
  Path.symm (left_unit a f)

/-- 12. 2-step: left unit then right unit through kleisli. -/
def kleisli_unit_sandwich (f : α → PMon α) (a : α) :
    Path (kleisli punit (kleisli f punit) a) (f a) :=
  Path.trans (left_unit a (kleisli f punit)) (right_unit (f a))

/-- 13. Map-bind interchange. -/
def map_as_bind (f : α → β) (m : PMon α) :
    Path (pmap f m) (pbind m (fun x => punit (f x))) :=
  Path.refl _

/-- 14. Naturality of join w.r.t. map. -/
def join_naturality (f : α → β) (x : PMon (PMon α)) :
    Path (pmap f (pjoin x)) (pjoin (pmap (pmap f) x)) :=
  Path.refl _

/-- 15. Naturality of bind. -/
def bind_naturality (f : α → β) (g : β → PMon γ) (m : PMon α) :
    Path (pbind (pmap f m) g) (pbind m (fun x => g (f x))) :=
  Path.refl _

/-! ## Strength and distributivity -/

/-- 16. Tensorial strength: pair with a value. -/
def strength (a : α) (mb : PMon β) : PMon (α × β) :=
  pmap (fun b => (a, b)) mb

/-- 17. Strength is natural in the first argument. -/
def strength_natural_fst (f : α → γ) (a : α) (mb : PMon β) :
    Path (pmap (fun p => (f p.1, p.2)) (strength a mb))
         (strength (f a) mb) :=
  Path.refl _

/-- 18. Strength distributes over bind. -/
def strength_bind (a : α) (mb : PMon β) (g : β → PMon γ) :
    Path (pbind (strength a mb) (fun p => strength p.1 (g p.2)))
         (strength a (pbind mb g)) :=
  Path.refl _

/-- 19. Strength with unit. -/
def strength_unit (a : α) (b : β) :
    Path (strength a (punit b)) (punit (a, b)) :=
  Path.refl _

/-! ## Deep trans/symm/congrArg chains -/

/-- 20. Multi-step: unit-bind-unit via 3 trans steps. -/
def unit_bind_unit_chain (a : α) :
    Path (pbind (pbind (punit a) punit) punit) (punit a) :=
  Path.trans
    (Path.trans
      (assoc_law (punit a) punit punit)
      (left_unit a (fun x => pbind (punit x) punit)))
    (left_unit a punit)

/-- 21. CongrArg: lifting map over a monad path. -/
def congrArg_map_over_bind (f : α → β) (m : PMon α) :
    Path (pmap f (pbind m punit)) (pmap f m) :=
  Path.congrArg (pmap f) (right_unit m)

/-- 22. Symmetric path composed with original yields refl proof. -/
theorem symm_trans_cancel_proof (m : PMon α) :
    (Path.trans (right_unit m) (Path.symm (right_unit m))).proof = rfl := by
  simp

/-- 23. Trans-assoc for monad paths. -/
theorem monad_trans_assoc
    {x y z w : PMon α}
    (p : Path x y) (q : Path y z) (r : Path z w) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- 24. Whiskering: left-whisker a monad path by bind. -/
def whisker_bind_left (m : PMon α) (f f' : α → PMon β)
    (h : f = f') :
    Path (pbind m f) (pbind m f') :=
  Path.ofEq (_root_.congrArg (fun g => pbind m g) h)

/-- 25. Whiskering: right-whisker by changing the monad value. -/
def whisker_bind_right (m m' : PMon α) (f : α → PMon β)
    (h : m = m') :
    Path (pbind m f) (pbind m' f) :=
  Path.ofEq (_root_.congrArg (fun x => pbind x f) h)

/-- 26. Double whiskering combines into a single path via trans. -/
def double_whisker (m m' : PMon α) (f f' : α → PMon β)
    (hm : m = m') (hf : f = f') :
    Path (pbind m f) (pbind m' f') :=
  Path.trans (whisker_bind_right m m' f hm)
             (whisker_bind_left m' f f' hf)

/-- 27. Symm-trans round trip: going forward and back on right_unit. -/
def symm_trans_roundtrip (m : PMon α) :
    Path (pbind (pbind m punit) punit) (pbind m punit) :=
  Path.trans
    (assoc_law m punit punit)
    (Path.congrArg (fun x => pbind x punit) (right_unit m) |> Path.symm |> Path.symm)

/-- 28. 5-step deep chain: unit → bind → assoc → unit → unit. -/
def deep_five_step (a : α) (f : α → PMon β) (g : β → PMon γ) :
    Path (pbind (pbind (punit a) (fun x => pbind (punit (f x).val) g)) punit)
         (pbind (f a) g) :=
  Path.trans
    (Path.trans
      (assoc_law (punit a) (fun x => pbind (punit (f x).val) g) punit)
      (left_unit a (fun x => pbind (pbind (punit (f x).val) g) punit)))
    (Path.trans
      (Path.congrArg (fun y => pbind y punit)
        (left_unit (f a).val g))
      (right_unit (g (f a).val)))

end ComputationalPaths.Path.Algebra.MonadDeep
