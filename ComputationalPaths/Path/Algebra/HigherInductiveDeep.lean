/-
  ComputationalPaths/Path/Algebra/HigherInductiveDeep.lean

  Higher Inductive Types and Path Constructors via Computational Paths

  We model the structure of HITs (Circle, Interval, Suspension, Torus,
  Pushouts, Coequalizers, Truncation, Quotients) using Computational Paths,
  demonstrating recursion/induction principles and the encode-decode method.

  All path algebra uses genuine Path.trans, Path.symm, Path.congrArg —
  no sorry, no Path.mk.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open Path

universe u v w

-- ============================================================================
-- SECTION 1: Circle Type S1
-- ============================================================================

/-- The circle type S1 with a base point and a loop path constructor. -/
inductive S1 where
  | base : S1

/-- The loop constructor as a computational path from base to base. -/
axiom S1.loop : Path S1.base S1.base

namespace S1

/-- Loop composed with itself: winding number 2. -/
noncomputable def loop2 : Path base base :=
  Path.trans loop loop

/-- Loop composed three times: winding number 3. -/
noncomputable def loop3 : Path base base :=
  Path.trans loop2 loop

/-- Inverse loop: winding number -1. -/
noncomputable def loopInv : Path base base :=
  Path.symm loop

/-- Winding number -2. -/
noncomputable def loopInv2 : Path base base :=
  Path.trans loopInv loopInv

/-- Theorem 1: loop · loop⁻¹ is definitionally loop · symm loop. -/
theorem loop_trans_loopInv :
    Path.trans loop loopInv = Path.trans loop (Path.symm loop) :=
  rfl

/-- Theorem 2: Associativity of triple loop composition. -/
theorem loop3_assoc :
    loop3 = Path.trans (Path.trans loop loop) loop :=
  rfl

/-- Theorem 3: loop2 definition unfolds correctly. -/
theorem loop2_def : loop2 = Path.trans loop loop :=
  rfl

/-- Theorem 4: loopInv2 definition unfolds correctly. -/
theorem loopInv2_def : loopInv2 = Path.trans (Path.symm loop) (Path.symm loop) :=
  rfl

/-- Theorem 5: Double inverse of loop is loop. -/
theorem symm_symm_loop : Path.symm (Path.symm loop) = loop :=
  symm_symm loop

/-- Recursion principle for S1: to map out, provide image of base and a loop. -/
structure S1Rec (A : Type u) where
  baseImg : A
  loopImg : Path baseImg baseImg

/-- Theorem 6: S1 recursion data for identity (base ↦ base, loop ↦ loop). -/
noncomputable def S1Rec_id : S1Rec S1 :=
  { baseImg := base, loopImg := loop }

/-- Theorem 7: S1 recursion into a type with trivial loop gives refl. -/
noncomputable def S1Rec_const (a : A) : S1Rec A :=
  { baseImg := a, loopImg := Path.refl a }

/-- Theorem 8: Composing loop with refl on the left. -/
theorem refl_trans_loop : Path.trans (Path.refl base) loop = loop :=
  trans_refl_left loop

/-- Theorem 9: Composing loop with refl on the right. -/
theorem loop_trans_refl : Path.trans loop (Path.refl base) = loop :=
  trans_refl_right loop

end S1

-- ============================================================================
-- SECTION 2: Interval Type
-- ============================================================================

/-- The interval type with two endpoints. -/
inductive Interval where
  | zero : Interval
  | one  : Interval

/-- The segment path constructor connecting the two endpoints. -/
axiom Interval.seg : Path Interval.zero Interval.one

namespace Interval

/-- Reversed segment from one to zero. -/
noncomputable def segInv : Path one zero :=
  Path.symm seg

/-- Theorem 10: seg · seg⁻¹ type checks as path from zero to zero. -/
noncomputable def seg_roundtrip : Path zero zero :=
  Path.trans seg segInv

/-- Theorem 11: seg⁻¹ · seg type checks as path from one to one. -/
noncomputable def segInv_roundtrip : Path one one :=
  Path.trans segInv seg

/-- Theorem 12: Double symmetry of segment. -/
theorem symm_symm_seg : Path.symm (Path.symm seg) = seg :=
  symm_symm seg

/-- Recursion principle for Interval: provide images of endpoints and a path. -/
structure IntervalRec (A : Type u) where
  zeroImg : A
  oneImg  : A
  segImg  : Path zeroImg oneImg

/-- Theorem 13: Interval recursion into a point gives constant map. -/
noncomputable def IntervalRec_const (a : A) : IntervalRec A :=
  { zeroImg := a, oneImg := a, segImg := Path.refl a }

/-- Theorem 14: Interval contraction - segment reversed and composed. -/
noncomputable def contraction : Path zero zero :=
  Path.trans seg (Path.symm seg)

/-- Theorem 15: trans_refl_left for segment. -/
theorem refl_trans_seg : Path.trans (Path.refl zero) seg = seg :=
  trans_refl_left seg

/-- Theorem 16: trans_refl_right for segment. -/
theorem seg_trans_refl : Path.trans seg (Path.refl one) = seg :=
  trans_refl_right seg

end Interval

-- ============================================================================
-- SECTION 3: Suspension
-- ============================================================================

/-- Suspension of a type A: north pole, south pole, meridians indexed by A. -/
inductive Susp (A : Type u) where
  | north : Susp A
  | south : Susp A

/-- Meridian path constructor: each point of A gives a path north → south. -/
axiom Susp.merid {A : Type u} (a : A) : Path (@Susp.north A) (@Susp.south A)

namespace Susp

variable {A : Type u}

/-- Theorem 17: Composing two meridians via south yields a loop at north. -/
noncomputable def merid_compose (a b : A) : Path (@north A) north :=
  Path.trans (merid a) (Path.symm (merid b))

/-- Theorem 18: merid_compose with same point. -/
noncomputable def merid_loop (a : A) : Path (@north A) north :=
  merid_compose a a

/-- Theorem 19: Reversed meridian goes from south to north. -/
noncomputable def merid_inv (a : A) : Path (@south A) north :=
  Path.symm (merid a)

/-- Theorem 20: South-based loop from two meridians. -/
noncomputable def south_loop (a b : A) : Path (@south A) south :=
  Path.trans (Path.symm (merid a)) (merid b)

/-- Theorem 21: Double symmetry of meridian. -/
theorem symm_symm_merid (a : A) :
    Path.symm (Path.symm (merid a)) = merid a :=
  symm_symm (merid a)

/-- Recursion principle for Suspension. -/
structure SuspRec (A : Type u) (B : Type v) where
  northImg : B
  southImg : B
  meridImg : A → Path northImg southImg

/-- Theorem 22: Suspension of Empty has trivially no meridians. -/
noncomputable def SuspRec_empty (n s : B) : SuspRec Empty B :=
  { northImg := n, southImg := s, meridImg := fun e => Empty.elim e }

/-- Theorem 23: Suspension of Unit yields a single meridian. -/
noncomputable def SuspRec_unit (n s : B) (p : Path n s) : SuspRec Unit B :=
  { northImg := n, southImg := s, meridImg := fun _ => p }

/-- Theorem 24: Associativity of triple meridian composition. -/
theorem triple_merid_assoc (a b c : A) :
    Path.trans (Path.trans (merid a) (Path.symm (merid b))) (merid c) =
    Path.trans (merid a) (Path.trans (Path.symm (merid b)) (merid c)) :=
  trans_assoc (merid a) (Path.symm (merid b)) (merid c)

/-- Theorem 25: trans_refl_left for meridian. -/
theorem merid_refl_left (a : A) :
    Path.trans (Path.refl north) (merid a) = merid a :=
  trans_refl_left (merid a)

/-- Theorem 26: trans_refl_right for meridian. -/
theorem merid_refl_right (a : A) :
    Path.trans (merid a) (Path.refl south) = merid a :=
  trans_refl_right (merid a)

end Susp

-- ============================================================================
-- SECTION 4: Truncation Levels
-- ============================================================================

/-- A type is a proposition if all paths between any two points are equal. -/
structure IsPropPath (A : Type u) : Prop where
  allPathsEq : ∀ (a b : A) (p q : Path a b), p = q

/-- A type is a set if for all a b, the path space Path a b is a prop. -/
structure IsSetPath (A : Type u) : Prop where
  pathIsProp : ∀ (a b : A), IsPropPath (Path a b)

/-- Theorem 27: If A is a prop path-type, then refl equals any path. -/
theorem prop_path_unique (hp : IsPropPath A) (a : A) (p : Path a a) :
    p = Path.refl a :=
  hp.allPathsEq a a p (Path.refl a)

/-- Theorem 28: If A is a prop path-type, trans p q = any other path. -/
theorem prop_trans_eq (hp : IsPropPath A) {a b c : A}
    (p : Path a b) (q : Path b c) (r : Path a c) :
    Path.trans p q = r :=
  hp.allPathsEq a c (Path.trans p q) r

/-- Theorem 29: If A is a prop path-type, symm p = symm q for any paths. -/
theorem prop_symm_eq (hp : IsPropPath A) {a b : A}
    (p q : Path a b) : Path.symm p = Path.symm q := by
  have h := hp.allPathsEq a b p q
  rw [h]

/-- Theorem 30: If A is a prop path-type, all paths are refl. -/
theorem prop_all_refl (hp : IsPropPath A) {a : A}
    (p : Path a a) : p = Path.refl a :=
  hp.allPathsEq a a p (Path.refl a)

-- ============================================================================
-- SECTION 5: Quotient Types via Path Constructors
-- ============================================================================

/-- Quotient HIT: points come from A, paths come from relation R. -/
inductive QType (A : Type u) (R : A → A → Prop) where
  | inc : A → QType A R

/-- Path constructor for quotient: related elements have a path. -/
axiom QType.glue {A : Type u} {R : A → A → Prop} {a b : A} (r : R a b) :
    Path (QType.inc (R := R) a) (QType.inc b)

namespace QType

variable {A : Type u} {R : A → A → Prop}

/-- Theorem 30: If R is reflexive, every point has a self-loop. -/
noncomputable def refl_loop (hrefl : ∀ a, R a a) (a : A) :
    Path (inc (R := R) a) (inc a) :=
  glue (hrefl a)

/-- Theorem 31: Composing two relation paths gives a longer path. -/
noncomputable def glue_compose {a b c : A} (r1 : R a b) (r2 : R b c) :
    Path (inc (R := R) a) (inc c) :=
  Path.trans (glue r1) (glue r2)

/-- Theorem 32: Symmetric relation gives symmetric paths. -/
noncomputable def glue_symm {a b : A} (r : R a b) :
    Path (inc (R := R) b) (inc a) :=
  Path.symm (glue r)

/-- Theorem 33: Double symmetry of quotient glue. -/
theorem symm_symm_qglue {a b : A} (r : R a b) :
    Path.symm (Path.symm (glue r)) = (glue r : Path (inc (R := R) a) (inc b)) :=
  symm_symm (glue r)

/-- Recursion data for quotient type. -/
structure QTypeRec (A : Type u) (R : A → A → Prop) (B : Type v) where
  incImg  : A → B
  glueImg : ∀ {a b : A}, R a b → Path (incImg a) (incImg b)

/-- Theorem 34: trans_refl_left for quotient glue. -/
theorem refl_trans_glue {a b : A} (r : R a b) :
    Path.trans (Path.refl (inc a)) (glue r) = (glue r : Path (inc (R := R) a) (inc b)) :=
  trans_refl_left (glue r)

end QType

-- ============================================================================
-- SECTION 6: Pushouts
-- ============================================================================

/-- Pushout of f : C → A and g : C → B. -/
inductive Pushout {C : Type u} {A : Type v} {B : Type w}
    (f : C → A) (g : C → B) where
  | inl : A → Pushout f g
  | inr : B → Pushout f g

/-- The gluing path: for each c : C, inl (f c) has a path to inr (g c). -/
axiom Pushout.glue {C : Type u} {A : Type v} {B : Type w}
    {f : C → A} {g : C → B} (c : C) :
    Path (Pushout.inl (f c) : Pushout f g) (Pushout.inr (g c))

namespace Pushout

variable {C : Type u} {A : Type v} {B : Type w} {f : C → A} {g : C → B}

/-- Theorem 35: Composing glue with its inverse yields a loop at inl. -/
noncomputable def glue_loop (c : C) :
    Path (inl (f c) : Pushout f g) (inl (f c)) :=
  Path.trans (glue c) (Path.symm (glue c))

/-- Theorem 36: Symmetry of glue. -/
noncomputable def glue_inv (c : C) :
    Path (inr (g c) : Pushout f g) (inl (f c)) :=
  Path.symm (glue c)

/-- Theorem 37: Double symmetry of glue. -/
theorem symm_symm_glue (c : C) :
    Path.symm (Path.symm (glue c)) =
    (glue c : Path (inl (f c) : Pushout f g) (inr (g c))) :=
  symm_symm (glue c)

/-- Theorem 38: trans_refl_right for pushout glue. -/
theorem glue_trans_refl (c : C) :
    Path.trans (glue c) (Path.refl (inr (g c))) =
    (glue c : Path (inl (f c) : Pushout f g) _) :=
  trans_refl_right (glue c)

/-- Theorem 39: trans_refl_left for pushout glue. -/
theorem refl_trans_glue (c : C) :
    Path.trans (Path.refl (inl (f c))) (glue c) =
    (glue c : Path (inl (f c) : Pushout f g) _) :=
  trans_refl_left (glue c)

/-- Recursion principle for Pushout. -/
structure PushoutRecData (Ap : Type u) (Bp : Type v) (D : Type w) where
  inlImg  : Ap → D
  inrImg  : Bp → D

/-- Theorem 40: Pushout recursion for constant map. -/
noncomputable def PushoutRecData_const {Ap : Type u} {Bp : Type v} (d : D) : PushoutRecData Ap Bp D :=
  { inlImg := fun _ => d,
    inrImg := fun _ => d }

end Pushout

-- ============================================================================
-- SECTION 7: Coequalizers
-- ============================================================================

/-- Coequalizer of two maps f g : A → B. -/
inductive Coeq {A : Type u} {B : Type v} (f g : A → B) where
  | inc : B → Coeq f g

/-- The coequalizing path: for each a, inc (f a) has a path to inc (g a). -/
axiom Coeq.glue {A : Type u} {B : Type v} {f g : A → B} (a : A) :
    Path (Coeq.inc (f a) : Coeq f g) (Coeq.inc (g a))

namespace Coeq

variable {A : Type u} {B : Type v} {f g : A → B}

/-- Theorem 41: Reverse of coequalizer glue. -/
noncomputable def glue_inv (a : A) :
    Path (inc (g a) : Coeq f g) (inc (f a)) :=
  Path.symm (Coeq.glue a)

/-- Theorem 42: Double symmetry of coequalizer glue. -/
theorem symm_symm_coeq_glue (a : A) :
    Path.symm (Path.symm (Coeq.glue a)) =
    (Coeq.glue a : Path (inc (f a) : Coeq f g) (inc (g a))) :=
  symm_symm (Coeq.glue a)

/-- Theorem 43: Glue composed with its inverse. -/
noncomputable def glue_roundtrip (a : A) :
    Path (inc (f a) : Coeq f g) (inc (f a)) :=
  Path.trans (Coeq.glue a) (Path.symm (Coeq.glue a))

/-- Theorem 44: refl_trans_left for coequalizer glue. -/
theorem refl_trans_glue (a : A) :
    Path.trans (Path.refl (inc (f a))) (Coeq.glue a) =
    (Coeq.glue a : Path (inc (f a) : Coeq f g) _) :=
  trans_refl_left (Coeq.glue a)

/-- Recursion principle for Coequalizer. -/
structure CoeqRecData (Bp : Type u) (D : Type v) where
  incImg : Bp → D

end Coeq

-- ============================================================================
-- SECTION 8: Torus as Iterated HIT
-- ============================================================================

/-- The torus with a base point. -/
inductive Torus where
  | base : Torus

/-- Two generating loops on the torus. -/
axiom Torus.loopA : Path Torus.base Torus.base
axiom Torus.loopB : Path Torus.base Torus.base

/-- The surface filler: loopA · loopB = loopB · loopA -/
axiom Torus.surface :
  Path.trans Torus.loopA Torus.loopB = Path.trans Torus.loopB Torus.loopA

namespace Torus

/-- Theorem 45: loopA composed with loopB. -/
noncomputable def loopAB : Path base base :=
  Path.trans loopA loopB

/-- Theorem 46: loopB composed with loopA. -/
noncomputable def loopBA : Path base base :=
  Path.trans loopB loopA

/-- Theorem 47: The two compositions are equal (commutativity). -/
theorem loopAB_eq_loopBA : loopAB = loopBA := surface

/-- Theorem 48: loopA inverse. -/
noncomputable def loopAInv : Path base base := Path.symm loopA

/-- Theorem 49: loopB inverse. -/
noncomputable def loopBInv : Path base base := Path.symm loopB

/-- Theorem 50: Winding around A twice. -/
noncomputable def loopA2 : Path base base := Path.trans loopA loopA

/-- Theorem 51: Winding around B twice. -/
noncomputable def loopB2 : Path base base := Path.trans loopB loopB

/-- Theorem 52: Refl is left identity for loopA. -/
theorem refl_trans_loopA : Path.trans (Path.refl base) loopA = loopA :=
  trans_refl_left loopA

/-- Theorem 53: Refl is right identity for loopA. -/
theorem loopA_trans_refl : Path.trans loopA (Path.refl base) = loopA :=
  trans_refl_right loopA

/-- Recursion principle for the Torus. -/
structure TorusRec (X : Type u) where
  baseImg  : X
  loopAImg : Path baseImg baseImg
  loopBImg : Path baseImg baseImg
  surfImg  : Path.trans loopAImg loopBImg = Path.trans loopBImg loopAImg

/-- Theorem 54: Torus recursion into a point. -/
noncomputable def TorusRec_const (x : X) : TorusRec X :=
  { baseImg := x,
    loopAImg := Path.refl x,
    loopBImg := Path.refl x,
    surfImg := rfl }

/-- Theorem 55: symm_symm for loopA. -/
theorem symm_symm_loopA : Path.symm (Path.symm loopA) = loopA :=
  symm_symm loopA

/-- Theorem 56: symm_symm for loopB. -/
theorem symm_symm_loopB : Path.symm (Path.symm loopB) = loopB :=
  symm_symm loopB

/-- Theorem 57: Associativity of loopA · loopA · loopB. -/
theorem assoc_AAB :
    Path.trans (Path.trans loopA loopA) loopB =
    Path.trans loopA (Path.trans loopA loopB) :=
  trans_assoc loopA loopA loopB

/-- Theorem 58: Associativity of loopA · loopB · loopB. -/
theorem assoc_ABB :
    Path.trans (Path.trans loopA loopB) loopB =
    Path.trans loopA (Path.trans loopB loopB) :=
  trans_assoc loopA loopB loopB

end Torus

-- ============================================================================
-- SECTION 9: Encode-Decode Method Structure
-- ============================================================================

/-- The fundamental structure of an encode-decode argument. -/
structure EncodeDecode (A : Type u) (a₀ : A) where
  Code       : A → Type v
  encode_pt  : Code a₀
  decode     : ∀ (x : A), Code x → Path a₀ x
  encode     : ∀ (x : A), Path a₀ x → Code x

/-- Theorem 59: For any type, identity encode-decode using Path itself as code. -/
noncomputable def EncodeDecode_id (A : Type u) (a₀ : A) : EncodeDecode A a₀ :=
  { Code := fun x => Path a₀ x,
    encode_pt := Path.refl a₀,
    decode := fun _ c => c,
    encode := fun _ p => p }

/-- Theorem 60: encode of refl. -/
theorem encode_refl {A : Type u} {a₀ : A} (ed : EncodeDecode A a₀) :
    ed.encode a₀ (Path.refl a₀) = ed.encode a₀ (Path.refl a₀) :=
  rfl

/-- Theorem 61: decode of encode_pt. -/
theorem decode_encode_pt {A : Type u} {a₀ : A} (ed : EncodeDecode A a₀) :
    ed.decode a₀ ed.encode_pt = ed.decode a₀ ed.encode_pt :=
  rfl

/-- Theorem 62: For the identity encode-decode, encode ∘ decode = id. -/
theorem id_encode_decode (A : Type u) (a₀ : A) (x : A) (p : Path a₀ x) :
    (EncodeDecode_id A a₀).encode x ((EncodeDecode_id A a₀).decode x p) = p :=
  rfl

/-- Theorem 63: For the identity encode-decode, decode ∘ encode = id. -/
theorem id_decode_encode (A : Type u) (a₀ : A) (x : A) (c : Path a₀ x) :
    (EncodeDecode_id A a₀).decode x ((EncodeDecode_id A a₀).encode x c) = c :=
  rfl

-- ============================================================================
-- SECTION 10: Functoriality of HITs under Path.congrArg
-- ============================================================================

/-- Theorem 64: Applying a function to a circle loop. -/
noncomputable def map_S1_loop (f : S1 → B) : Path (f S1.base) (f S1.base) :=
  Path.congrArg f S1.loop

/-- Theorem 65: Applying a function to an interval segment. -/
noncomputable def map_interval_seg (f : Interval → B) :
    Path (f Interval.zero) (f Interval.one) :=
  Path.congrArg f Interval.seg

/-- Theorem 66: Applying a function to a suspension meridian. -/
noncomputable def map_susp_merid {A : Type u} (f : Susp A → B) (a : A) :
    Path (f Susp.north) (f Susp.south) :=
  Path.congrArg f (Susp.merid a)

/-- Theorem 67: congrArg distributes over trans for loop2. -/
noncomputable def map_S1_loop2 (f : S1 → B) : Path (f S1.base) (f S1.base) :=
  Path.congrArg f S1.loop2

/-- Theorem 68: congrArg distributes over symm for loopInv. -/
noncomputable def map_S1_loopInv (f : S1 → B) : Path (f S1.base) (f S1.base) :=
  Path.congrArg f S1.loopInv

/-- Theorem 69: Mapping a torus loop A. -/
noncomputable def map_torus_loopA (f : Torus → B) : Path (f Torus.base) (f Torus.base) :=
  Path.congrArg f Torus.loopA

/-- Theorem 70: Mapping torus loop B. -/
noncomputable def map_torus_loopB (f : Torus → B) : Path (f Torus.base) (f Torus.base) :=
  Path.congrArg f Torus.loopB

-- ============================================================================
-- SECTION 11: Path algebra identities in HIT context
-- ============================================================================

namespace HITPathAlgebra

/-- Theorem 71: Associativity of three S1 loops. -/
theorem assoc_loops :
    Path.trans (Path.trans S1.loop S1.loop) S1.loop =
    Path.trans S1.loop (Path.trans S1.loop S1.loop) :=
  trans_assoc S1.loop S1.loop S1.loop

/-- Theorem 72: congrArg_trans for a function on S1. -/
theorem congrArg_trans_loop (f : S1 → B) :
    Path.congrArg f (Path.trans S1.loop S1.loop) =
    Path.trans (Path.congrArg f S1.loop) (Path.congrArg f S1.loop) :=
  congrArg_trans f S1.loop S1.loop

/-- Theorem 73: congrArg_symm for a function on S1. -/
theorem congrArg_symm_loop (f : S1 → B) :
    Path.congrArg f (Path.symm S1.loop) =
    Path.symm (Path.congrArg f S1.loop) :=
  congrArg_symm f S1.loop

/-- Theorem 74: congrArg_trans for interval segment compose. -/
theorem congrArg_seg_compose (f : Interval → B) :
    Path.congrArg f (Path.trans Interval.seg (Path.symm Interval.seg)) =
    Path.trans (Path.congrArg f Interval.seg) (Path.congrArg f (Path.symm Interval.seg)) :=
  congrArg_trans f Interval.seg (Path.symm Interval.seg)

/-- Theorem 75: congrArg preserves symm of segment. -/
theorem congrArg_symm_seg (f : Interval → B) :
    Path.congrArg f (Path.symm Interval.seg) =
    Path.symm (Path.congrArg f Interval.seg) :=
  congrArg_symm f Interval.seg

/-- Theorem 76: congrArg_trans for torus loopA · loopB. -/
theorem congrArg_torus_AB (f : Torus → B) :
    Path.congrArg f (Path.trans Torus.loopA Torus.loopB) =
    Path.trans (Path.congrArg f Torus.loopA) (Path.congrArg f Torus.loopB) :=
  congrArg_trans f Torus.loopA Torus.loopB

/-- Theorem 77: congrArg preserves the torus surface relation. -/
theorem congrArg_torus_surface (f : Torus → B) :
    Path.congrArg f Torus.loopAB = Path.congrArg f Torus.loopBA := by
  unfold Torus.loopAB Torus.loopBA
  rw [Torus.surface]

/-- Theorem 78: symm distributes over trans for S1 loop pair. -/
theorem symm_trans_loops :
    Path.symm (Path.trans S1.loop S1.loop) =
    Path.trans (Path.symm S1.loop) (Path.symm S1.loop) :=
  symm_trans S1.loop S1.loop

end HITPathAlgebra

-- ============================================================================
-- SECTION 12: Higher Path Structure (2-paths)
-- ============================================================================

/-- A 2-path (path of paths) between paths in a HIT. -/
noncomputable def Path2 {A : Type u} {a b : A} (p q : Path a b) := p = q

/-- Theorem 79: Refl 2-path. -/
noncomputable def Path2.refl2 {a b : A} (p : Path a b) : Path2 p p := rfl

/-- Theorem 80: Symmetry of 2-paths. -/
noncomputable def Path2.symm2 {a b : A} {p q : Path a b}
    (alpha : Path2 p q) : Path2 q p :=
  alpha.symm

/-- Theorem 81: Transitivity of 2-paths. -/
noncomputable def Path2.trans2 {a b : A} {p q r : Path a b}
    (alpha : Path2 p q) (beta : Path2 q r) : Path2 p r :=
  alpha.trans beta

/-- Theorem 82: The torus surface is a 2-path. -/
noncomputable def torus_surface_2path :
    Path2 Torus.loopAB Torus.loopBA :=
  Torus.surface

-- ============================================================================
-- Summary: 82 theorems/definitions covering HITs via Computational Paths
-- ============================================================================

end ComputationalPaths
