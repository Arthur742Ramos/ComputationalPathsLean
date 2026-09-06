import ComputationalPaths.Path.OmegaGroupoid.AssocHigherBridge
import ComputationalPaths.Path.OmegaGroupoid.NativeOperadicOperations

/-!
# The independent associativity certificate in the operadic native tower

The existing certificate and its native `Derivation₃` interpretation are
reused unchanged. Raw `RwEq` boundaries are retained exactly. Higher
structural composition is interpreted recursively, but the target's
explicit coskeletal extension is not faithful on three-cell certificates.
The independent presentation-sensitive theorem is not replaced by this map.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u v

namespace NativeAssociativity

open OmegaGroupoid PalomarAssociativity

/-- The original primitive associator has exactly the boundaries formed
by the standard operadic composition of three heterogeneous paths. -/
noncomputable def operadicAssociator {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    { h : NativeTower.Cell A 2 //
      NativeTower.source h = NativeOperadic.compose (A := A) (n := 0)
        (NativeOperadic.compose (A := A) (n := 0)
          (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl)
        (ULift.up (⟨c, d, r⟩ : PathOne A))
        (NativeOperadic.compose_boundary (A := A) (n := 0)
          (ULift.up (⟨a, b, p⟩ : PathOne A)) (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl).2 ∧
      NativeTower.target h = NativeOperadic.compose (A := A) (n := 0)
        (ULift.up (⟨a, b, p⟩ : PathOne A))
        (NativeOperadic.compose (A := A) (n := 0)
          (ULift.up (⟨b, c, q⟩ : PathOne A)) (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl)
        (NativeOperadic.compose_boundary (A := A) (n := 0)
          (ULift.up (⟨b, c, q⟩ : PathOne A)) (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl).1.symm } := by
  refine ⟨NativeTower.associator p q r, ?_, ?_⟩
  · simp only [NativeOperadic.compose_paths]
    rfl
  · simp only [NativeOperadic.compose_paths]
    rfl

theorem operadicAssociator_derivation {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (operadicAssociator p q r).val.2.2.2.2 = RwEq.step (Step.trans_assoc p q r) := rfl

noncomputable def two {A : Type u} {a b : A} {p q : Path a b}
    (d : Derivation₂ p q) : NativeTower.Cell A 2 := ⟨a, b, p, q, d.toRwEq⟩

/-- Horizontal two-cell composition uses the full standard operadic input,
not a native vertical composite relabelled as horizontal. -/
noncomputable def horizontal {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (d : Derivation₂ p p') (e : Derivation₂ q q') : NativeTower.Cell A 2 :=
  NativeOperadic.composeAt (.bottom : Pasting.Cut 2) (two d) (two e) rfl

theorem horizontal_boundary {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (d : Derivation₂ p p') (e : Derivation₂ q q') :
    NativeTower.source (horizontal d e) = ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) ∧
      NativeTower.target (horizontal d e) = ULift.up (⟨a, c, Path.trans p' q'⟩ : PathOne A) :=
  ⟨(NativeOperadic.composeAt_source (.bottom : Pasting.Cut 1) (two d) (two e) rfl rfl).trans
      (NativeOperadic.composeAt_paths p q),
    (NativeOperadic.composeAt_target (.bottom : Pasting.Cut 1) (two d) (two e) rfl rfl).trans
      (NativeOperadic.composeAt_paths p' q')⟩

/-- A specified comparison to the original horizontal rewrite derivation.
This is a three-cell in the declared coskeletal target, not equality of the
two raw rewrite histories or a replacement for their independent proof. -/
noncomputable def horizontalComparison {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (d : Derivation₂ p p') (e : Derivation₂ q q') :
    { h : NativeTower.Cell A 3 // NativeTower.source h = horizontal d e ∧
      NativeTower.target h = two (OmegaGroupoid.hcomp d e) } :=
  ⟨NativeTower.fillPositive (horizontal d e) (two (OmegaGroupoid.hcomp d e))
      (horizontal_boundary d e).1 (horizontal_boundary d e).2,
    NativeTower.fillPositive_boundary _ _ _ _⟩

def onePath {A : Type u} {a b : A} (p : Path a b) : NativeTower.Cell A 1 := ULift.up ⟨a, b, p⟩

/-- Whiskering uses the selected operadic identity two-cell, not a raw
reflexive witness silently substituted for that choice. -/
noncomputable def operadicWhiskerRight {A : Type u} {a b c : A}
    {p p' : Path a b} (d : Derivation₂ p p') (q : Path b c) : NativeTower.Cell A 2 :=
  NativeOperadic.composeAt (.bottom : Pasting.Cut 2) (two d)
    (NativeOperadic.identity (onePath q))
    (_root_.congrArg (NativeTower.source (A := A) (n := 0))
      (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath q)).1).symm

noncomputable def operadicWhiskerLeft {A : Type u} {a b c : A}
    (p : Path a b) {q q' : Path b c} (e : Derivation₂ q q') : NativeTower.Cell A 2 :=
  NativeOperadic.composeAt (.bottom : Pasting.Cut 2)
    (NativeOperadic.identity (onePath p)) (two e)
    (_root_.congrArg (NativeTower.target (A := A) (n := 0))
      (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath p)).2)

theorem operadicWhiskerRight_boundary {A : Type u} {a b c : A}
    {p p' : Path a b} (d : Derivation₂ p p') (q : Path b c) :
    NativeTower.source (operadicWhiskerRight d q) = onePath (Path.trans p q) ∧
      NativeTower.target (operadicWhiskerRight d q) = onePath (Path.trans p' q) := by
  have hs := (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath q)).1
  have ht := (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath q)).2
  constructor
  · exact (NativeOperadic.composeAt_source (.bottom : Pasting.Cut 1) (two d)
      (NativeOperadic.identity (onePath q)) _
      (_root_.congrArg (NativeTower.source (A := A) (n := 0)) hs).symm).trans
      ((NativeOperadic.composeAt_congr (.bottom : Pasting.Cut 1)
        (p' := onePath p) (q' := onePath q) rfl hs _ rfl).trans (NativeOperadic.composeAt_paths p q))
  · exact (NativeOperadic.composeAt_target (.bottom : Pasting.Cut 1) (two d)
      (NativeOperadic.identity (onePath q)) _
      (_root_.congrArg (NativeTower.source (A := A) (n := 0)) ht).symm).trans
      ((NativeOperadic.composeAt_congr (.bottom : Pasting.Cut 1)
        (p' := onePath p') (q' := onePath q) rfl ht _ rfl).trans (NativeOperadic.composeAt_paths p' q))

theorem operadicWhiskerLeft_boundary {A : Type u} {a b c : A}
    (p : Path a b) {q q' : Path b c} (e : Derivation₂ q q') :
    NativeTower.source (operadicWhiskerLeft p e) = onePath (Path.trans p q) ∧
      NativeTower.target (operadicWhiskerLeft p e) = onePath (Path.trans p q') := by
  have hs := (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath p)).1
  have ht := (NativeOperadic.identity_boundary (A := A) (n := 1) (onePath p)).2
  constructor
  · exact (NativeOperadic.composeAt_source (.bottom : Pasting.Cut 1)
      (NativeOperadic.identity (onePath p)) (two e) _
      (_root_.congrArg (NativeTower.target (A := A) (n := 0)) hs)).trans
      ((NativeOperadic.composeAt_congr (.bottom : Pasting.Cut 1)
        (p' := onePath p) (q' := onePath q) hs rfl _ rfl).trans (NativeOperadic.composeAt_paths p q))
  · exact (NativeOperadic.composeAt_target (.bottom : Pasting.Cut 1)
      (NativeOperadic.identity (onePath p)) (two e) _
      (_root_.congrArg (NativeTower.target (A := A) (n := 0)) ht)).trans
      ((NativeOperadic.composeAt_congr (.bottom : Pasting.Cut 1)
        (p' := onePath p) (q' := onePath q') ht rfl _ rfl).trans (NativeOperadic.composeAt_paths p q'))

noncomputable def whiskerRightComparison {A : Type u} {a b c : A}
    {p p' : Path a b} (d : Derivation₂ p p') (q : Path b c) :
    { h : NativeTower.Cell A 3 // NativeTower.source h = operadicWhiskerRight d q ∧
      NativeTower.target h = two (OmegaGroupoid.whiskerRight d q) } :=
  ⟨NativeTower.fillPositive (operadicWhiskerRight d q) (two (OmegaGroupoid.whiskerRight d q))
      (operadicWhiskerRight_boundary d q).1 (operadicWhiskerRight_boundary d q).2,
    NativeTower.fillPositive_boundary _ _ _ _⟩

noncomputable def whiskerLeftComparison {A : Type u} {a b c : A}
    (p : Path a b) {q q' : Path b c} (e : Derivation₂ q q') :
    { h : NativeTower.Cell A 3 // NativeTower.source h = operadicWhiskerLeft p e ∧
      NativeTower.target h = two (OmegaGroupoid.whiskerLeft p e) } :=
  ⟨NativeTower.fillPositive (operadicWhiskerLeft p e) (two (OmegaGroupoid.whiskerLeft p e))
      (operadicWhiskerLeft_boundary p e).1 (operadicWhiskerLeft_boundary p e).2,
    NativeTower.fillPositive_boundary _ _ _ _⟩

theorem horizontalComparison_invertible {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (d : Derivation₂ p p') (e : Derivation₂ q q') :
    NativeOperadic.WeaklyInvertible 2 (horizontalComparison d e).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

theorem whiskerRightComparison_invertible {A : Type u} {a b c : A}
    {p p' : Path a b} (d : Derivation₂ p p') (q : Path b c) :
    NativeOperadic.WeaklyInvertible 2 (whiskerRightComparison d q).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

theorem whiskerLeftComparison_invertible {A : Type u} {a b c : A}
    (p : Path a b) {q q' : Path b c} (e : Derivation₂ q q') :
    NativeOperadic.WeaklyInvertible 2 (whiskerLeftComparison p e).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

/-- Native certificate concatenation and standard operadic two-cell
composition are related by a specified three-cell. -/
noncomputable def twoCompositionComparison {A : Type u} {a b : A}
    {p q r : Path a b} (d : Derivation₂ p q) (e : Derivation₂ q r) :
    { c : NativeTower.Cell A 3 //
      NativeTower.source c = NativeOperadic.compose (A := A) (n := 1) (two d) (two e) rfl ∧
      NativeTower.target c = two (.vcomp d e) } :=
  ⟨NativeOperadic.compareCompose (A := A) (n := 1) (two d) (two e) rfl,
    NativeOperadic.compareCompose_boundary _ _ _⟩

theorem twoCompositionComparison_invertible {A : Type u} {a b : A}
    {p q r : Path a b} (d : Derivation₂ p q) (e : Derivation₂ q r) :
    NativeOperadic.WeaklyInvertible 2 (twoCompositionComparison d e).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

/-- Interpret structural three-cell composition recursively. Primitive
meta-steps enter the declared coskeletal layer; no faithfulness is claimed. -/
noncomputable def three {A : Type u} {a b : A} {p q : Path a b}
    {d e : Derivation₂ p q} : Derivation₃ d e →
      { c : NativeTower.Cell A 3 // NativeTower.source c = two d ∧ NativeTower.target c = two e }
  | .refl d => ⟨NativeTower.identity (two d), NativeTower.source_identity _, NativeTower.target_identity _⟩
  | .step _ => ⟨NativeTower.higherCell (two d) (two e) rfl rfl,
      NativeTower.source_higherCell _ _ _ _, NativeTower.target_higherCell _ _ _ _⟩
  | .inv h =>
      let t := three h
      ⟨NativeTower.reverse t.val, (NativeTower.source_reverse t.val).trans t.property.2,
        (NativeTower.target_reverse t.val).trans t.property.1⟩
  | .vcomp h k =>
      let s := three h
      let t := three k
      ⟨NativeTower.compose s.val t.val (s.property.2.trans t.property.1.symm),
        (NativeTower.source_compose _ _ _).trans s.property.1,
        (NativeTower.target_compose _ _ _).trans t.property.2⟩

theorem three_vcomp {A : Type u} {a b : A} {p q : Path a b}
    {d e f : Derivation₂ p q} (h : Derivation₃ d e) (k : Derivation₃ e f) :
    (three (.vcomp h k)).val = NativeTower.compose (three h).val (three k).val
      ((three h).property.2.trans (three k).property.1.symm) := rfl

theorem three_inv {A : Type u} {a b : A} {p q : Path a b}
    {d e : Derivation₂ p q} (h : Derivation₃ d e) :
    (three (.inv h)).val = NativeTower.reverse (three h).val := rfl

/-- Semantic boundary of this bridge: parallel three-cell certificates
have equal images in the chosen coskeletal target, not in the source syntax. -/
theorem three_parallel_images {A : Type u} {a b : A} {p q : Path a b}
    {d e : Derivation₂ p q} (h k : Derivation₃ d e) : (three h).val = (three k).val :=
  NativeTower.higher_ext _ _ ((three h).property.1.trans (three k).property.1.symm)
    ((three h).property.2.trans (three k).property.2.symm)

noncomputable def trace {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) {x y : FreeMagma α} (p : AssocRwEq x y) :
    NativeTower.Cell A 2 := ⟨a, a, evalTree label x, evalTree label y, evalTrace label p⟩

noncomputable def rewriteSteps {A : Type u} {a b : A} :
    {p q : Path a b} → RwEq p q → Nat
  | _, _, .refl _ => 0
  | _, _, .step _ => 1
  | _, _, .symm h => rewriteSteps h
  | _, _, .trans h k => rewriteSteps h + rewriteSteps k

noncomputable def traceSteps {A : Type u} (c : NativeTower.Cell A 2) : Nat :=
  rewriteSteps c.2.2.2.2

/-- The two-edge and three-edge pentagon histories remain distinct even
after interpretation into the tower's raw two-cell carrier. -/
theorem pentagon_trace_counts {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) (w x y z : FreeMagma α) :
    traceSteps (trace label (pentagonShort w x y z).toRwEq) = 2 ∧
      traceSteps (trace label (pentagonLong w x y z).toRwEq) = 3 := ⟨rfl, rfl⟩

theorem pentagon_traces_distinct {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) (w x y z : FreeMagma α) :
    trace label (pentagonShort w x y z).toRwEq ≠ trace label (pentagonLong w x y z).toRwEq := by
  intro h
  have hc := _root_.congrArg traceSteps h
  change 2 = 3 at hc
  cases hc

theorem two_eval₂ {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) {x y : FreeMagma α} (p : AssocRwEq x y) :
    two (eval₂ label p) = trace label p :=
  _root_.congrArg (fun h => (⟨a, a, evalTree label x, evalTree label y, h⟩ : NativeTower.Cell A 2))
    (eval₂_toRwEq label p)

/-- Image of the actual existing higher certificate, through its verified
native interpretation, with the original raw trace endpoints preserved. -/
noncomputable def certificate {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) {x y : FreeMagma α} {p q : AssocRwEq x y}
    (h : AssocHigher p q) :
    { c : NativeTower.Cell A 3 //
      NativeTower.source c = trace label p ∧ NativeTower.target c = trace label q } :=
  let t := three (evalHigher label h)
  ⟨t.val, t.property.1.trans (two_eval₂ label p), t.property.2.trans (two_eval₂ label q)⟩

theorem certificate_pentagon {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) (w x y z : FreeMagma α) :
    (certificate label (AssocHigher.pentagon w x y z)).val =
      (three (nativePentagon label w x y z)).val := rfl

theorem certificate_interchange {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) {x x' y y' : FreeMagma α}
    (p : AssocRwEq x x') (q : AssocRwEq y y') :
    (certificate label (AssocHigher.interchange p q)).val =
      (three (nativeInterchange label p q)).val := rfl

theorem certificate_invertible {α : Type v} {A : Type u} {a : A}
    (label : α → Path a a) {x y : FreeMagma α} {p q : AssocRwEq x y}
    (h : AssocHigher p q) : NativeOperadic.WeaklyInvertible 2 (certificate label h).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

/-- Comparison of interpreted certificate composition with composition
chosen by the standard operadic instructions. -/
noncomputable def compositionComparison {A : Type u} {a b : A} {p q : Path a b}
    {d e f : Derivation₂ p q} (h : Derivation₃ d e) (k : Derivation₃ e f) :
    { c : NativeTower.Cell A 4 //
      NativeTower.source c = NativeOperadic.compose (A := A) (n := 2) (three h).val (three k).val
        ((three h).property.2.trans (three k).property.1.symm) ∧
      NativeTower.target c = (three (.vcomp h k)).val } :=
  ⟨NativeOperadic.compareCompose (A := A) (n := 2) (three h).val (three k).val
      ((three h).property.2.trans (three k).property.1.symm),
    NativeOperadic.compareCompose_boundary _ _ _⟩

theorem compositionComparison_invertible {A : Type u} {a b : A} {p q : Path a b}
    {d e f : Derivation₂ p q} (h : Derivation₃ d e) (k : Derivation₃ e f) :
    NativeOperadic.WeaklyInvertible 3 (compositionComparison h k).val :=
  NativeOperadic.all_cells_weaklyInvertible _ _

/-- The tree interpretation still uses the exact multi-step `Path.trans`
expression of the independent associativity certificate. -/
theorem tree_three {α : Type v} {A : Type u} {a : A} (label : α → Path a a)
    (x y z : FreeMagma α) : evalTree label ((x * y) * z) =
      Path.trans (Path.trans (evalTree label x) (evalTree label y)) (evalTree label z) := rfl

end NativeAssociativity

end ComputationalPaths.Path.OmegaFoundations
