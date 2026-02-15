/-
# Cayley Graphs via Computational Paths

This module introduces lightweight Cayley graph data for group presentations in
the computational-paths setting. We model words in signed generators, quotient
them by a presentation relation, and define adjacency and word paths as
computational paths in the resulting graph.

## Key Definitions

- `GroupPresentation`
- `CayleyVertex`, `vertexMul`, `Adjacent`
- `WordPathEq`, `wordMetric`, `Geodesic`
- `CayleyGraphAutomorphism`

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Hatcher, "Algebraic Topology", Section 1.2
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CayleyGraphPaths

universe u

/-! ## Words in generators -/

/-- Signed generators with formal inverses. -/
inductive SignedGen (Gen : Type u) : Type u where
  | pos : Gen -> SignedGen Gen
  | neg : Gen -> SignedGen Gen

namespace SignedGen

/-- Invert a signed generator. -/
def inv {Gen : Type u} : SignedGen Gen -> SignedGen Gen
  | pos g => neg g
  | neg g => pos g

end SignedGen

/-- Words in signed generators. -/
abbrev Word (Gen : Type u) : Type u := List (SignedGen Gen)

namespace Word

/-- Append a generator to the right of a word. -/
def appendGen {Gen : Type u} (w : Word Gen) (g : SignedGen Gen) : Word Gen :=
  w ++ [g]

/-- Invert a word by reversing and flipping signs. -/
def inv {Gen : Type u} (w : Word Gen) : Word Gen :=
  w.reverse.map SignedGen.inv

@[simp] theorem length_appendGen {Gen : Type u} (w : Word Gen) (g : SignedGen Gen) :
    (appendGen w g).length = w.length + 1 := by
  simp [appendGen]

end Word

/-! ## Group presentations and Cayley vertices -/

/-- A group presentation with relations compatible with right append. -/
structure GroupPresentation where
  Gen : Type u
  Rel : Word Gen -> Word Gen -> Prop
  rel_refl : forall w, Rel w w
  rel_symm : forall {w1 w2}, Rel w1 w2 -> Rel w2 w1
  rel_trans : forall {w1 w2 w3}, Rel w1 w2 -> Rel w2 w3 -> Rel w1 w3
  rel_append_right :
    forall {w1 w2} (g : SignedGen Gen), Rel w1 w2 ->
      Rel (Word.appendGen w1 g) (Word.appendGen w2 g)
  rel_length : forall {w1 w2}, Rel w1 w2 -> List.length w1 = List.length w2

/-- Cayley graph vertices as a quotient of words by the presentation relation. -/
def CayleyVertex (P : GroupPresentation) : Type u :=
  Quot P.Rel

/-- Project a word to its Cayley vertex. -/
def wordToVertex (P : GroupPresentation) (w : Word P.Gen) : CayleyVertex P :=
  Quot.mk _ w

/-- Right action of a signed generator on a Cayley vertex. -/
def vertexMul (P : GroupPresentation) (v : CayleyVertex P) (g : SignedGen P.Gen) :
    CayleyVertex P :=
  Quot.lift
    (fun w => wordToVertex P (Word.appendGen w g))
    (by
      intro w1 w2 h
      exact Quot.sound (P.rel_append_right g h))
    v

/-! ## Adjacency and word paths -/

/-- Adjacency in the Cayley graph via a single generator. -/
def Adjacent (P : GroupPresentation) (v w : CayleyVertex P) : Type u :=
  Sigma fun g : SignedGen P.Gen => Path (vertexMul P v g) w

/-- Right action of a word on a Cayley vertex. -/
def wordAction (P : GroupPresentation) (v : CayleyVertex P) :
    Word P.Gen -> CayleyVertex P
  | [] => v
  | g :: rest => wordAction P (vertexMul P v g) rest

/-! ## Path composition for word actions -/

/-- Compose two adjacent generator steps into a length-two word path. -/
def composeAdjacentWord2 (P : GroupPresentation) {v w u : CayleyVertex P}
    (p : Adjacent P v w) (q : Adjacent P w u) :
    Path (wordAction P v [p.1, q.1]) u := by
  cases p with
  | mk g pg =>
    cases q with
    | mk h qg =>
      have step : Path (vertexMul P (vertexMul P v g) h) (vertexMul P w h) :=
        Path.congrArg (fun x => vertexMul P x h) pg
      have composed : Path (vertexMul P (vertexMul P v g) h) u :=
        Path.trans step qg
      simpa [wordAction] using composed

/-- Concatenating words corresponds to composing actions by `Path.trans`. -/
def wordAction_append_path (P : GroupPresentation) (v : CayleyVertex P)
    (w1 w2 : Word P.Gen) :
    Path (wordAction P v (w1 ++ w2)) (wordAction P (wordAction P v w1) w2) :=
  match w1 with
  | [] =>
      by
        simpa [wordAction] using (Path.refl (wordAction P v w2))
  | g :: rest =>
      by
        simpa [wordAction] using (wordAction_append_path P (vertexMul P v g) rest w2)

/-- Two words are equivalent if they give the same Cayley vertex. -/
def WordPathEq (P : GroupPresentation) (w1 w2 : Word P.Gen) : Type u :=
  Path (wordToVertex P w1) (wordToVertex P w2)

/-- A relation witness induces a computational path between vertices. -/
def rel_to_WordPathEq (P : GroupPresentation) {w1 w2 : Word P.Gen}
    (h : P.Rel w1 w2) : WordPathEq P w1 w2 :=
  Path.stepChain (Quot.sound h)

/-! ## Word path composition -/

/-- `Path.trans` composes word paths in the Cayley graph. -/
def wordPathEq_trans (P : GroupPresentation) {w1 w2 w3 : Word P.Gen}
    (p : WordPathEq P w1 w2) (q : WordPathEq P w2 w3) : WordPathEq P w1 w3 :=
  Path.trans p q

/-! ## Rewrite-equivalence example -/

/-- Two syntactically different word paths are rewrite-equivalent. -/
theorem wordPath_rweq_refl (P : GroupPresentation) (w : Word P.Gen) :
    RwEq
      (Path.trans (Path.refl (wordToVertex P w)) (Path.refl (wordToVertex P w)))
      (Path.refl (wordToVertex P w)) := by
  exact rweq_cmpA_refl_left (p := Path.refl (wordToVertex P w))

/-! ## Word metric and geodesics -/

/-- Word metric on words: the length of the word. -/
def wordMetric {Gen : Type u} (w : Word Gen) : Nat :=
  List.length w

/-- Word metric on Cayley vertices, well-defined by `rel_length`. -/
def vertexMetric (P : GroupPresentation) : CayleyVertex P -> Nat :=
  Quot.lift (fun w => List.length w) (fun _ _ h => P.rel_length h)

/-- A word is geodesic if no equivalent word is shorter. -/
def Geodesic (P : GroupPresentation) (w : Word P.Gen) : Prop :=
  forall w', P.Rel w w' -> List.length w <= List.length w'

/-! ## Graph automorphisms -/

/-- Automorphisms of the Cayley graph preserving adjacency. -/
structure CayleyGraphAutomorphism (P : GroupPresentation) where
  toFun : CayleyVertex P -> CayleyVertex P
  invFun : CayleyVertex P -> CayleyVertex P
  left_inv : forall v, Path (invFun (toFun v)) v
  right_inv : forall v, Path (toFun (invFun v)) v
  adj_preserve : forall {v w}, Adjacent P v w -> Adjacent P (toFun v) (toFun w)

namespace CayleyGraphAutomorphism

/-- Identity automorphism of a Cayley graph. -/
def id (P : GroupPresentation) : CayleyGraphAutomorphism P where
  toFun := fun v => v
  invFun := fun v => v
  left_inv := fun v => Path.refl v
  right_inv := fun v => Path.refl v
  adj_preserve := by
    intro v w h
    simpa using h

end CayleyGraphAutomorphism

/-! ## Deeper properties of Cayley graphs -/

/-- SignedGen inversion is involutive. -/
theorem SignedGen.inv_inv {Gen : Type u} (g : SignedGen Gen) :
    SignedGen.inv (SignedGen.inv g) = g := by
  cases g <;> rfl

/-- Word inversion is involutive. -/
theorem Word.inv_inv {Gen : Type u} (w : Word Gen) :
    Word.inv (Word.inv w) = w := by
  simp [Word.inv, List.map_reverse, List.reverse_reverse, List.map_map, Function.comp]
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp [SignedGen.inv_inv, ih]

/-- Word inversion reverses length. -/
theorem Word.length_inv {Gen : Type u} (w : Word Gen) :
    (Word.inv w).length = w.length := by
  simp [Word.inv]

/-- The identity automorphism composed with itself is the identity. -/
theorem CayleyGraphAutomorphism.id_comp_id (P : GroupPresentation) :
    ∀ v, (CayleyGraphAutomorphism.id P).toFun ((CayleyGraphAutomorphism.id P).toFun v) = v := by
  intro v; rfl

/-- Word action of the empty word is the identity. -/
theorem wordAction_nil (P : GroupPresentation) (v : CayleyVertex P) :
    wordAction P v [] = v := by
  rfl




/-- The word metric is always non-negative (trivially true for Nat). -/
theorem wordMetric_nonneg {Gen : Type u} (w : Word Gen) :
    0 ≤ wordMetric w :=
  Nat.zero_le _

/-- WordPathEq is reflexive. -/
def WordPathEq.refl (P : GroupPresentation) (w : Word P.Gen) :
    WordPathEq P w w :=
  Path.refl _

/-- WordPathEq is symmetric. -/
def WordPathEq.symm (P : GroupPresentation) {w₁ w₂ : Word P.Gen}
    (h : WordPathEq P w₁ w₂) : WordPathEq P w₂ w₁ :=
  Path.symm h

/-- WordPathEq is transitive. -/
def WordPathEq.trans (P : GroupPresentation) {w₁ w₂ w₃ : Word P.Gen}
    (h₁ : WordPathEq P w₁ w₂) (h₂ : WordPathEq P w₂ w₃) :
    WordPathEq P w₁ w₃ :=
  Path.trans h₁ h₂


/-! ## Summary -/

end CayleyGraphPaths
end Algebra
end Path
end ComputationalPaths
