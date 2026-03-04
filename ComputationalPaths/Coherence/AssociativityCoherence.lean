import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

open OmegaGroupoid

namespace Associativity

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- Type-valued 2-cells between computational paths (rewrite derivations). -/
abbrev TwoCell {a b : A} (p q : Path a b) : Type (u + 2) :=
  OmegaGroupoid.Derivation₂ p q

/-- Type-valued 3-cells between 2-cells (meta-derivations). -/
abbrev ThreeCell {a b : A} {p q : Path a b}
    (α β : TwoCell (A := A) (a := a) (b := b) p q) : Type (u + 2) :=
  OmegaGroupoid.Derivation₃ α β

/-- Associator 2-cell witnessing associativity of `Path.trans`. -/
noncomputable def associator (p : Path a b) (q : Path b c) (r : Path c d) :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  .step (Step.trans_assoc p q r)

/-- Left route in Mac Lane's pentagon (three-step route). -/
noncomputable def pentagon_left_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  OmegaGroupoid.Derivation₂.vcomp
    (OmegaGroupoid.Derivation₂.vcomp
      (.step (Step.trans_congr_left s (Step.trans_assoc p q r)))
      (.step (Step.trans_assoc p (Path.trans q r) s)))
    (.step (Step.trans_congr_right p (Step.trans_assoc q r s)))

/-- Right route in Mac Lane's pentagon (two-step route). -/
noncomputable def pentagon_right_route
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  OmegaGroupoid.Derivation₂.vcomp
    (.step (Step.trans_assoc (Path.trans p q) r s))
    (.step (Step.trans_assoc p q (Path.trans r s)))

/-- **Mac Lane pentagon coherence** as a genuine 3-cell connecting the two routes.

This is exactly the primitive coherence cell `MetaStep₃.pentagon` from
`OmegaGroupoid`.

Note the direction: it connects the right (two-step) route to the left
(three-step) route.
-/
noncomputable def mac_lane_pentagon
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    ThreeCell (A := A) (a := a) (b := e)
      (pentagon_right_route (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)
      (pentagon_left_route (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) :=
  .step (.pentagon p q r s)

end Associativity

end ComputationalPaths.Coherence
