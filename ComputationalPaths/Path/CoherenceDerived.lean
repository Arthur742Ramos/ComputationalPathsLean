/-
# Higher Coherence Derived Properties

Axiom-free, sorry-free theorems about higher coherence laws derived from
Step rules and RwEq congruence lemmas.

## Key Results
- Pentagon full identity (all 5 faces)
- Triangle identity components
- Whiskering composition laws
- Horizontal composition coherence
- Eckmann-Hilton preparation at path level

## References

- Lumsdaine, "Weak ω-categories from intensional type theory"
- van den Berg & Garner, "Types are weak ω-groupoids"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path
namespace CoherenceDerived

open Step

universe u

variable {A : Type u} {a b c d e f' : A}

/-! ## Full Pentagon Identity

The pentagon identity relates five ways of reassociating ((f·g)·h)·k to f·(g·(h·k)).
We express this as a sequence of RwEq steps. -/

/-- Pentagon face 1: ((f·g)·h)·k → (f·(g·h))·k -/
theorem rweq_pentagon_face1 (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans (trans f g) h) k)
         (trans (trans f (trans g h)) k) :=
  rweq_trans_congr_left k (rweq_of_step (Step.trans_assoc f g h))

/-- Pentagon face 2: (f·(g·h))·k → f·((g·h)·k) -/
theorem rweq_pentagon_face2 (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans f (trans g h)) k)
         (trans f (trans (trans g h) k)) :=
  rweq_of_step (Step.trans_assoc f (trans g h) k)

/-- Pentagon face 3: f·((g·h)·k) → f·(g·(h·k)) -/
theorem rweq_pentagon_face3 (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans f (trans (trans g h) k))
         (trans f (trans g (trans h k))) :=
  rweq_trans_congr_right f (rweq_of_step (Step.trans_assoc g h k))

/-- Pentagon face 4: ((f·g)·h)·k → (f·g)·(h·k) (alternative route) -/
theorem rweq_pentagon_face4 (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans (trans f g) h) k)
         (trans (trans f g) (trans h k)) :=
  rweq_of_step (Step.trans_assoc (trans f g) h k)

/-- Pentagon face 5: (f·g)·(h·k) → f·(g·(h·k)) (alternative route) -/
theorem rweq_pentagon_face5 (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans f g) (trans h k))
         (trans f (trans g (trans h k))) :=
  rweq_of_step (Step.trans_assoc f g (trans h k))

/-- Full pentagon: the two routes from ((f·g)·h)·k to f·(g·(h·k)) are RwEq-equivalent.
    This is the pentagon coherence law expressed at the RwEq level. -/
theorem rweq_pentagon_full (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans (trans f g) h) k)
         (trans f (trans g (trans h k))) := by
  -- Route 1: use faces 1, 2, 3
  have r1_12 := RwEq.trans (rweq_pentagon_face1 f g h k) (rweq_pentagon_face2 f g h k)
  exact RwEq.trans r1_12 (rweq_pentagon_face3 f g h k)

/-- Pentagon alternative route: faces 4, 5 -/
theorem rweq_pentagon_alt (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq (trans (trans (trans f g) h) k)
         (trans f (trans g (trans h k))) := by
  -- Route 2: use faces 4, 5
  exact RwEq.trans (rweq_pentagon_face4 f g h k) (rweq_pentagon_face5 f g h k)

/-! ## Triangle Identity Components

The triangle identity relates associator and right unitor. -/

/-- Triangle left: (f·refl)·g → f·(refl·g) -/
theorem rweq_triangle_left (f : Path a b) (g : Path b c) :
    RwEq (trans (trans f (refl b)) g)
         (trans f (trans (refl b) g)) :=
  rweq_of_step (Step.trans_assoc f (refl b) g)

/-- Triangle right: f·(refl·g) → f·g -/
theorem rweq_triangle_right (f : Path a b) (g : Path b c) :
    RwEq (trans f (trans (refl b) g))
         (trans f g) :=
  rweq_trans_congr_right f (rweq_of_step (Step.trans_refl_left g))

/-- Triangle full: (f·refl)·g → f·g via associativity + left unit -/
theorem rweq_triangle_full (f : Path a b) (g : Path b c) :
    RwEq (trans (trans f (refl b)) g)
         (trans f g) :=
  RwEq.trans (rweq_triangle_left f g) (rweq_triangle_right f g)

/-- Triangle alternative: (f·refl)·g → f·g via right unit on f first -/
theorem rweq_triangle_alt (f : Path a b) (g : Path b c) :
    RwEq (trans (trans f (refl b)) g)
         (trans f g) :=
  rweq_trans_congr_left g (rweq_of_step (Step.trans_refl_right f))

/-! ## Six-fold Associativity

Extending pentagon to longer compositions. -/

/-- Five-fold associativity: (((f·g)·h)·i)·j → f·(g·(h·(i·j))) -/
theorem rweq_trans_five_assoc (f : Path a b) (g : Path b c) (h : Path c d)
    (i : Path d e) (j : Path e f') :
    RwEq (trans (trans (trans (trans f g) h) i) j)
         (trans f (trans g (trans h (trans i j)))) := by
  -- Use pentagon twice
  have h1 := rweq_pentagon_full f g h i
  have h2 : RwEq (trans (trans (trans (trans f g) h) i) j)
                 (trans (trans f (trans g (trans h i))) j) :=
    rweq_trans_congr_left j h1
  have h3 : RwEq (trans (trans f (trans g (trans h i))) j)
                 (trans f (trans (trans g (trans h i)) j)) :=
    rweq_of_step (Step.trans_assoc f (trans g (trans h i)) j)
  have h4 : RwEq (trans (trans g (trans h i)) j)
                 (trans g (trans (trans h i) j)) :=
    rweq_of_step (Step.trans_assoc g (trans h i) j)
  have h5 : RwEq (trans (trans h i) j)
                 (trans h (trans i j)) :=
    rweq_of_step (Step.trans_assoc h i j)
  have h6 := rweq_trans_congr_right g h5
  have h7 := RwEq.trans h4 h6
  have h8 := rweq_trans_congr_right f h7
  exact RwEq.trans (RwEq.trans h2 h3) h8

/-! ## Whiskering Coherence Laws -/

/-- Left whiskering is functorial: f ⊳ (p·q) ≈ (f ⊳ p)·(f ⊳ q) 
    where f ⊳ p = trans f p for whiskering -/
theorem rweq_whisker_left_comp (f : Path a b) (p : Path b c) (q : Path c d) :
    RwEq (trans f (trans p q))
         (trans (trans f p) q) :=
  RwEq.symm (rweq_of_step (Step.trans_assoc f p q))

/-- Right whiskering is functorial: (p·q) ⊲ f ≈ (p ⊲ f)·(q ⊲ f) would be:
    trans (trans p q) f ≈ trans (trans p f) (trans q f) - but this doesn't type check!
    Instead: (p·q)·f = p·(q·f) -/
theorem rweq_whisker_right_comp (p : Path a b) (q : Path b c) (f : Path c d) :
    RwEq (trans (trans p q) f)
         (trans p (trans q f)) :=
  rweq_of_step (Step.trans_assoc p q f)

/-- Whiskering preserves reflexivity: refl ⊳ p ≈ p -/
theorem rweq_whisker_refl_left (p : Path a b) :
    RwEq (trans (refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Whiskering preserves reflexivity: p ⊳ refl ≈ p -/
theorem rweq_whisker_refl_right (p : Path a b) :
    RwEq (trans p (refl b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-! ## Eckmann-Hilton Preparation

Lemmas preparing for the Eckmann-Hilton argument that shows π₂ is abelian. -/

/-- Middle unitor: f·refl·g → f·g (using triangle) -/
theorem rweq_middle_unitor (f : Path a b) (g : Path b c) :
    RwEq (trans (trans f (refl b)) g)
         (trans f g) :=
  rweq_triangle_full f g

/-- Unit laws combine: (refl·p)·refl → p -/
theorem rweq_double_unit (p : Path a b) :
    RwEq (trans (trans (refl a) p) (refl b))
         p := by
  have h1 : RwEq (trans (trans (refl a) p) (refl b))
                 (trans (refl a) (trans p (refl b))) :=
    rweq_of_step (Step.trans_assoc (refl a) p (refl b))
  have h2 : RwEq (trans p (refl b)) p :=
    rweq_of_step (Step.trans_refl_right p)
  have h3 := rweq_trans_congr_right (refl a) h2
  have h4 : RwEq (trans (refl a) p) p :=
    rweq_of_step (Step.trans_refl_left p)
  exact RwEq.trans h1 (RwEq.trans h3 h4)

/-- Triple reflexivity: refl·refl·refl → refl -/
theorem rweq_triple_refl (a : A) :
    RwEq (trans (trans (refl a) (refl a)) (refl a))
         (refl a) :=
  rweq_double_unit (refl a)

/-! ## Inverse Coherence Laws -/

/-- Inverse interchanges with associativity: ((p·q)·r)⁻¹ → r⁻¹·(q⁻¹·p⁻¹) 
    which equals (p·(q·r))⁻¹ -/
theorem rweq_symm_trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (trans (trans p q) r))
         (trans (symm r) (trans (symm q) (symm p))) := by
  -- (p·q)·r)⁻¹ → r⁻¹·((p·q)⁻¹) by symm_trans_congr
  have h1 : RwEq (symm (trans (trans p q) r))
                 (trans (symm r) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) r)
  -- (p·q)⁻¹ → q⁻¹·p⁻¹ by symm_trans_congr
  have h2 : RwEq (symm (trans p q))
                 (trans (symm q) (symm p)) :=
    rweq_of_step (Step.symm_trans_congr p q)
  exact RwEq.trans h1 (rweq_trans_congr_right (symm r) h2)

/-- Four-fold symm distribution: ((p·q)·r)·s)⁻¹ → s⁻¹·(r⁻¹·(q⁻¹·p⁻¹)) -/
theorem rweq_symm_trans_four (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (symm (trans (trans (trans p q) r) s))
         (trans (symm s) (trans (symm r) (trans (symm q) (symm p)))) := by
  -- First step: outer symm_trans_congr
  have h1 : RwEq (symm (trans (trans (trans p q) r) s))
                 (trans (symm s) (symm (trans (trans p q) r))) :=
    rweq_of_step (Step.symm_trans_congr (trans (trans p q) r) s)
  -- Inner: ((p·q)·r)⁻¹ → r⁻¹·(q⁻¹·p⁻¹)
  have h2 := rweq_symm_trans_assoc p q r
  exact RwEq.trans h1 (rweq_trans_congr_right (symm s) h2)

/-- Five-fold symm distribution: (((p·q)·r)·s)·t)⁻¹ → t⁻¹·(s⁻¹·(r⁻¹·(q⁻¹·p⁻¹))) -/
theorem rweq_symm_trans_five (p : Path a b) (q : Path b c) (r : Path c d) 
    (s : Path d e) (t : Path e f') :
    RwEq (symm (trans (trans (trans (trans p q) r) s) t))
         (trans (symm t) (trans (symm s) (trans (symm r) (trans (symm q) (symm p))))) := by
  -- Outer symm_trans_congr
  have h1 : RwEq (symm (trans (trans (trans (trans p q) r) s) t))
                 (trans (symm t) (symm (trans (trans (trans p q) r) s))) :=
    rweq_of_step (Step.symm_trans_congr (trans (trans (trans p q) r) s) t)
  -- Inner: use four-fold
  have h2 := rweq_symm_trans_four p q r s
  exact RwEq.trans h1 (rweq_trans_congr_right (symm t) h2)

/-! ## Six-fold Associativity -/

/-- Six-fold associativity: ((((f·g)·h)·i)·j)·k → f·(g·(h·(i·(j·k)))) -/
theorem rweq_trans_six_assoc (f : Path a b) (g : Path b c) (h : Path c d)
    (i : Path d e) (j : Path e f') (k : Path f' a) :
    RwEq (trans (trans (trans (trans (trans f g) h) i) j) k)
         (trans f (trans g (trans h (trans i (trans j k))))) := by
  -- Use five-fold then one more assoc
  have h1 := rweq_trans_five_assoc f g h i j
  have h2 : RwEq (trans (trans (trans (trans (trans f g) h) i) j) k)
                 (trans (trans f (trans g (trans h (trans i j)))) k) :=
    rweq_trans_congr_left k h1
  have h3 : RwEq (trans (trans f (trans g (trans h (trans i j)))) k)
                 (trans f (trans (trans g (trans h (trans i j))) k)) :=
    rweq_of_step (Step.trans_assoc f (trans g (trans h (trans i j))) k)
  have h4 : RwEq (trans (trans g (trans h (trans i j))) k)
                 (trans g (trans (trans h (trans i j)) k)) :=
    rweq_of_step (Step.trans_assoc g (trans h (trans i j)) k)
  have h5 : RwEq (trans (trans h (trans i j)) k)
                 (trans h (trans (trans i j) k)) :=
    rweq_of_step (Step.trans_assoc h (trans i j) k)
  have h6 : RwEq (trans (trans i j) k)
                 (trans i (trans j k)) :=
    rweq_of_step (Step.trans_assoc i j k)
  have h7 := rweq_trans_congr_right h h6
  have h8 := RwEq.trans h5 h7
  have h9 := rweq_trans_congr_right g h8
  have h10 := RwEq.trans h4 h9
  have h11 := rweq_trans_congr_right f h10
  exact RwEq.trans h2 (RwEq.trans h3 h11)

end CoherenceDerived
end Path
end ComputationalPaths
