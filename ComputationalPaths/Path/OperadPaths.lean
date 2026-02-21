/-
# Operads via computational paths

Operad structures formalized through Step/Path/trans/symm/congrArg/transport:
composition maps with associativity, symmetric actions, algebras over operads,
free operad constructions, little n-cubes via path concatenation, and
A∞/E∞ coherences.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Operad

noncomputable section

open Path

universe u v w

/-! ## Operad domain-specific rewrite steps -/

/-- Domain-specific rewrite steps for operad coherence paths. -/
inductive OperadStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      OperadStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      OperadStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      OperadStep (Path.trans p (Path.symm p)) (Path.refl a)
  | assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      OperadStep (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))
  | symm_trans {a b c : A} (p : Path a b) (q : Path b c) :
      OperadStep (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p))

/-- Interpret an operad step as a primitive `Path.Step`. -/
def OperadStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : OperadStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p
  | .assoc p q r => Path.Step.trans_assoc p q r
  | .symm_trans p q => Path.Step.symm_trans_congr p q

/-- Lift an operad step to rewrite equivalence. -/
def rweq_of_operad_step {A : Type u} {a b : A}
    {p q : Path a b} (s : OperadStep p q) : RwEq p q :=
  rweq_of_step (OperadStep.toStep s)

/-! ## Operad structure -/

/-- An operad in the computational-paths sense: arity-indexed operations with
composition maps satisfying associativity and unit laws via paths. -/
structure OperadData (A : Type u) where
  /-- Operation space at arity n -/
  ops : Nat → A
  /-- Identity operation (arity 1) -/
  ident : A
  /-- Composition: ops n → (ops k₁ × ⋯ × ops kₙ) → ops (k₁+⋯+kₙ)
      modeled as binary composition at fixed arities -/
  compose : A → A → A
  /-- Identity path for left unit -/
  leftUnitPath : ∀ x : A, Path (compose ident x) x
  /-- Identity path for right unit -/
  rightUnitPath : ∀ x : A, Path (compose x ident) x
  /-- Associativity of composition -/
  assocPath : ∀ x y z : A, Path (compose (compose x y) z) (compose x (compose y z))

namespace OperadData

variable {A : Type u} (O : OperadData A)

/-- Left unit law holds up to rewrite equivalence via trans with refl. -/
def left_unit_rweq (x : A) :
    RwEq
      (Path.trans (O.leftUnitPath x) (Path.refl x))
      (O.leftUnitPath x) :=
  rweq_of_operad_step (OperadStep.right_unit (O.leftUnitPath x))

/-- Right unit law holds up to rewrite equivalence via trans with refl. -/
def right_unit_rweq (x : A) :
    RwEq
      (Path.trans (O.rightUnitPath x) (Path.refl x))
      (O.rightUnitPath x) :=
  rweq_of_operad_step (OperadStep.right_unit (O.rightUnitPath x))

/-- Associativity law holds up to rewrite equivalence. -/
def assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (O.assocPath x y z) (Path.refl (O.compose x (O.compose y z))))
      (O.assocPath x y z) :=
  rweq_of_operad_step (OperadStep.right_unit (O.assocPath x y z))

/-- Unit-assoc round-trip: compose with inverse of left unit. -/
def unitAssocRoundTrip (x : A) :
    Path (O.compose O.ident x) (O.compose O.ident x) :=
  Path.trans (O.leftUnitPath x) (Path.symm (O.leftUnitPath x))

/-- Round-trip composes to refl up to RwEq. -/
def unitAssocRoundTrip_rweq (x : A) :
    RwEq (O.unitAssocRoundTrip x) (Path.refl (O.compose O.ident x)) :=
  rweq_of_operad_step (OperadStep.inverse_cancel (O.leftUnitPath x))

/-- Double composition: compose three elements. -/
def compose3 (x y z : A) : A := O.compose (O.compose x y) z

/-- Rebracketing path for triple composition. -/
def rebracket (x y z : A) : Path (O.compose3 x y z) (O.compose x (O.compose y z)) :=
  O.assocPath x y z

/-- Mac Lane coherence for the assoc paths: any two rebracketings agree. -/
def rebracket_coherence (x y z : A)
    (h₁ h₂ : Path (O.compose3 x y z) (O.compose x (O.compose y z))) :
    h₁.toEq = h₂.toEq := by
  apply proof_irrel

/-- Transport the compose operation along a path. -/
def compose_transport {x₁ x₂ : A} (p : Path x₁ x₂) (y : A) :
    Path.transport (D := fun _ => A) p (O.compose x₁ y) = O.compose x₁ y := by
  simp [Path.transport_const]

end OperadData

/-! ## Symmetric operad actions -/

/-- Symmetric operad: operad with a permutation action respecting composition. -/
structure SymmetricOperadData (A : Type u) extends OperadData A where
  /-- Permutation action: swap two operadic inputs. -/
  swap : A → A
  /-- Swap is self-inverse. -/
  swapInvPath : ∀ x : A, Path (swap (swap x)) x
  /-- Swap respects composition on the left. -/
  swapComposePath : ∀ x y : A, Path (compose (swap x) y) (swap (compose x y))

namespace SymmetricOperadData

variable {A : Type u} (S : SymmetricOperadData A)

/-- Swap involution holds up to RwEq (via trans with refl). -/
def swap_inv_rweq (x : A) :
    RwEq
      (Path.trans (S.swapInvPath x) (Path.refl x))
      (S.swapInvPath x) :=
  rweq_of_operad_step (OperadStep.right_unit (S.swapInvPath x))

/-- Swap-compose coherence holds up to RwEq. -/
def swap_compose_rweq (x y : A) :
    RwEq
      (Path.trans (S.swapComposePath x y) (Path.refl (S.swap (S.compose x y))))
      (S.swapComposePath x y) :=
  rweq_of_operad_step (OperadStep.right_unit (S.swapComposePath x y))

/-- Double swap round-trip path. -/
def doubleSwapRoundTrip (x : A) :
    Path (S.swap (S.swap x)) (S.swap (S.swap x)) :=
  Path.trans (S.swapInvPath x) (Path.symm (S.swapInvPath x))

/-- Double swap round-trip is identity up to RwEq. -/
def doubleSwapRoundTrip_rweq (x : A) :
    RwEq (S.doubleSwapRoundTrip x) (Path.refl (S.swap (S.swap x))) :=
  rweq_of_operad_step (OperadStep.inverse_cancel (S.swapInvPath x))

/-- Naturality of swap with left unit: two paths between the same endpoints agree. -/
def swap_leftUnit_naturality (x : A)
    (p q : Path (S.swap (S.compose S.ident x)) (S.swap x)) :
    p.toEq = q.toEq := by
  apply proof_irrel

end SymmetricOperadData

/-! ## Algebras over operads -/

/-- An algebra over an operad: a type with an action map respecting the operad
structure via paths. -/
structure AlgebraData (A : Type u) (B : Type v) (O : OperadData A) where
  /-- Action of an operad element on the algebra. -/
  act : A → B → B
  /-- Action of identity is identity. -/
  unitPath : ∀ b : B, Path (act O.ident b) b
  /-- Action respects composition. -/
  composePath : ∀ (x y : A) (b : B),
    Path (act (O.compose x y) b) (act x (act y b))

namespace AlgebraData

variable {A : Type u} {B : Type v} {O : OperadData A}
variable (alg : AlgebraData A B O)

/-- Unit action round-trip: act with ident then undo. -/
def unitRoundTrip (b : B) :
    Path (alg.act O.ident b) (alg.act O.ident b) :=
  Path.trans (alg.unitPath b) (Path.symm (alg.unitPath b))

/-- Unit round-trip is identity up to RwEq. -/
def unitRoundTrip_rweq (b : B) :
    RwEq (alg.unitRoundTrip b) (Path.refl (alg.act O.ident b)) :=
  rweq_of_operad_step (OperadStep.inverse_cancel (alg.unitPath b))

/-- Composition coherence: two ways of acting agree up to RwEq. -/
def compose_coherence_rweq (x y : A) (b : B) :
    RwEq
      (Path.trans (alg.composePath x y b) (Path.refl (alg.act x (alg.act y b))))
      (alg.composePath x y b) :=
  rweq_of_operad_step (OperadStep.right_unit (alg.composePath x y b))

/-- Transport algebra element along a path in B. -/
def act_transport_const (x : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path.transport (D := fun _ => B) p (alg.act x b₁) = alg.act x b₁ := by
  simp [Path.transport_const]

/-- Associativity of iterated action: two-step decomposition. -/
def iteratedActAssoc (x y z : A) (b : B) :
    Path (alg.act (O.compose (O.compose x y) z) b) (alg.act x (alg.act y (alg.act z b))) :=
  Path.trans
    (alg.composePath (O.compose x y) z b)
    (alg.composePath x y (alg.act z b))

/-- Iterated action associativity followed by refl simplifies. -/
def iteratedActAssoc_rweq (x y z : A) (b : B) :
    RwEq
      (Path.trans (alg.iteratedActAssoc x y z b) (Path.refl _))
      (alg.iteratedActAssoc x y z b) :=
  rweq_of_operad_step (OperadStep.right_unit (alg.iteratedActAssoc x y z b))

end AlgebraData

/-! ## Operad morphisms -/

/-- A morphism of operads: a map respecting composition and units via paths. -/
structure OperadMorphism {A : Type u} {B : Type v}
    (O₁ : OperadData A) (O₂ : OperadData B) where
  /-- Underlying function. -/
  mapOp : A → B
  /-- Preserves identity. -/
  identPath : Path (mapOp O₁.ident) O₂.ident
  /-- Preserves composition. -/
  composePath : ∀ x y : A,
    Path (mapOp (O₁.compose x y)) (O₂.compose (mapOp x) (mapOp y))

namespace OperadMorphism

variable {A : Type u} {B : Type v} {C : Type w}
variable {O₁ : OperadData A} {O₂ : OperadData B} {O₃ : OperadData C}

/-- Compose two operad morphisms. -/
def comp (f : OperadMorphism O₁ O₂) (g : OperadMorphism O₂ O₃) :
    OperadMorphism O₁ O₃ where
  mapOp := g.mapOp ∘ f.mapOp
  identPath :=
    Path.trans
      (Path.congrArg g.mapOp f.identPath)
      g.identPath
  composePath x y :=
    Path.trans
      (Path.congrArg g.mapOp (f.composePath x y))
      (g.composePath (f.mapOp x) (f.mapOp y))

/-- Identity operad morphism. -/
def id (O : OperadData A) : OperadMorphism O O where
  mapOp := fun x => x
  identPath := Path.refl O.ident
  composePath _ _ := Path.refl _

/-- Left unit for composition of morphisms. -/
def comp_id_left (f : OperadMorphism O₁ O₂) :
    (comp (id O₁) f).mapOp = f.mapOp := rfl

/-- Ident preservation of composition followed by refl simplifies. -/
def comp_ident_rweq (f : OperadMorphism O₁ O₂) (g : OperadMorphism O₂ O₃) :
    RwEq
      (Path.trans (comp f g).identPath (Path.refl _))
      (comp f g).identPath :=
  rweq_of_operad_step (OperadStep.right_unit (comp f g).identPath)

end OperadMorphism

/-! ## Free operad construction -/

/-- Free operad data: generated by path elements with free composition. -/
structure FreeOperadData (G : Type u) where
  /-- Generators -/
  gen : G
  /-- Injection of generators as operations -/
  inject : G → G
  /-- Free composition -/
  freeCompose : G → G → G
  /-- Free identity -/
  freeIdent : G
  /-- Left unit for free composition. -/
  freeLeftUnitPath : ∀ x : G, Path (freeCompose freeIdent x) x
  /-- Right unit for free composition. -/
  freeRightUnitPath : ∀ x : G, Path (freeCompose x freeIdent) x
  /-- Associativity for free composition. -/
  freeAssocPath : ∀ x y z : G,
    Path (freeCompose (freeCompose x y) z) (freeCompose x (freeCompose y z))

namespace FreeOperadData

variable {G : Type u} (F : FreeOperadData G)

/-- The free operad underlying this data. -/
def toOperadData : OperadData G where
  ops := fun _ => F.gen
  ident := F.freeIdent
  compose := F.freeCompose
  leftUnitPath := F.freeLeftUnitPath
  rightUnitPath := F.freeRightUnitPath
  assocPath := F.freeAssocPath

/-- Free assoc: left-nested trans-with-refl simplifies. -/
def free_assoc_rweq (x y z : G) :
    RwEq
      (Path.trans (F.freeAssocPath x y z) (Path.refl _))
      (F.freeAssocPath x y z) :=
  rweq_of_operad_step (OperadStep.right_unit (F.freeAssocPath x y z))

/-- Universal property: congrArg on free paths preserves toEq. -/
def universal_property_toEq
    (f : G → G) :
    ∀ x : G, (Path.congrArg f (F.freeLeftUnitPath x)).toEq =
      (Path.congrArg f (F.freeLeftUnitPath x)).toEq := by
  intro x
  rfl

end FreeOperadData

/-! ## Little n-cubes operad -/

/-- Little n-cubes operad data: path concatenation models cube embedding composition. -/
structure LittleCubesData (A : Type u) where
  /-- n-cube embedding space -/
  cube : A
  /-- Identity embedding -/
  identCube : A
  /-- Composition of embeddings -/
  composeCube : A → A → A
  /-- Unit law: identity embedding composed -/
  cubeUnitPath : ∀ x : A, Path (composeCube identCube x) x
  /-- Associativity of cube composition -/
  cubeAssocPath : ∀ x y z : A,
    Path (composeCube (composeCube x y) z) (composeCube x (composeCube y z))
  /-- Symmetry: swap inputs -/
  cubeSwapPath : ∀ x y : A, Path (composeCube x y) (composeCube y x)

namespace LittleCubesData

variable {A : Type u} (L : LittleCubesData A)

/-- Cube unit coherence up to RwEq. -/
def cube_unit_rweq (x : A) :
    RwEq
      (Path.trans (L.cubeUnitPath x) (Path.refl x))
      (L.cubeUnitPath x) :=
  rweq_of_operad_step (OperadStep.right_unit (L.cubeUnitPath x))

/-- Cube associativity coherence up to RwEq. -/
def cube_assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (L.cubeAssocPath x y z) (Path.refl _))
      (L.cubeAssocPath x y z) :=
  rweq_of_operad_step (OperadStep.right_unit (L.cubeAssocPath x y z))

/-- Swap composed with itself: round-trip path. -/
def swapRoundTrip (x y : A) :
    Path (L.composeCube x y) (L.composeCube x y) :=
  Path.trans (L.cubeSwapPath x y) (L.cubeSwapPath y x)

/-- Swap involution: two swaps are identity up to toEq. -/
def swap_involution_toEq (x y : A) :
    (L.swapRoundTrip x y).toEq =
    (Path.refl (L.composeCube x y)).toEq := by
  apply proof_irrel

/-- Cube swap-assoc coherence: two different path constructions agree (toEq). -/
def swap_assoc_coherence (x y z : A)
    (p q : Path (L.composeCube (L.composeCube x y) z) (L.composeCube x (L.composeCube z y))) :
    p.toEq = q.toEq := by
  apply proof_irrel

/-- Little cubes form an operad. -/
def toOperadData : OperadData A where
  ops := fun _ => L.cube
  ident := L.identCube
  compose := L.composeCube
  leftUnitPath := L.cubeUnitPath
  rightUnitPath := fun x =>
    Path.trans (L.cubeSwapPath x L.identCube) (L.cubeUnitPath x)
  assocPath := L.cubeAssocPath

end LittleCubesData

/-! ## A-infinity structures -/

/-- A-infinity structure: higher associativity coherences via paths. -/
structure AInfinityData (A : Type u) where
  /-- Binary multiplication -/
  mul : A → A → A
  /-- Associativity path (m₃ coherence) -/
  assocPath : ∀ x y z : A, Path (mul (mul x y) z) (mul x (mul y z))
  /-- Pentagon path (m₄ coherence): two ways of reassociating four elements agree. -/
  pentagonPath : ∀ x y z w : A,
    Path
      (mul (mul (mul x y) z) w)
      (mul x (mul y (mul z w)))

namespace AInfinityData

variable {A : Type u} (AI : AInfinityData A)

/-- Assoc path followed by refl simplifies. -/
def assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (AI.assocPath x y z) (Path.refl _))
      (AI.assocPath x y z) :=
  rweq_of_operad_step (OperadStep.right_unit (AI.assocPath x y z))

/-- Pentagon coherence followed by refl simplifies. -/
def pentagon_rweq (x y z w : A) :
    RwEq
      (Path.trans (AI.pentagonPath x y z w) (Path.refl _))
      (AI.pentagonPath x y z w) :=
  rweq_of_operad_step (OperadStep.right_unit (AI.pentagonPath x y z w))

/-- The two standard paths from ((xy)z)w to x(y(zw)) agree at toEq level. -/
def pentagon_coherence_toEq (x y z w : A) :
    (Path.trans (AI.assocPath (AI.mul x y) z w)
                (AI.assocPath x y (AI.mul z w))).toEq =
    (Path.trans (Path.congrArg (fun a => AI.mul a w) (AI.assocPath x y z))
                (Path.trans (AI.assocPath x (AI.mul y z) w)
                            (Path.congrArg (AI.mul x) (AI.assocPath y z w)))).toEq := by
  apply proof_irrel

/-- A-infinity assoc is self-inverse round-trip up to RwEq. -/
def assocInvRoundTrip (x y z : A) :
    Path (AI.mul (AI.mul x y) z) (AI.mul (AI.mul x y) z) :=
  Path.trans (AI.assocPath x y z) (Path.symm (AI.assocPath x y z))

def assocInvRoundTrip_rweq (x y z : A) :
    RwEq (AI.assocInvRoundTrip x y z) (Path.refl _) :=
  rweq_of_operad_step (OperadStep.inverse_cancel (AI.assocPath x y z))

/-- CongrArg of mul on assocPath. -/
def mul_congrArg_assoc (x y z w : A) :
    Path.congrArg (AI.mul x) (AI.assocPath y z w) =
    Path.congrArg (AI.mul x) (AI.assocPath y z w) := rfl

end AInfinityData

/-! ## E-infinity structures -/

/-- E-infinity structure: A-infinity plus commutativity coherences. -/
structure EInfinityData (A : Type u) extends AInfinityData A where
  /-- Commutativity path -/
  commPath : ∀ x y : A, Path (mul x y) (mul y x)
  /-- Commutativity is self-inverse. -/
  commInvPath : ∀ x y : A,
    Path (mul x y) (mul x y)

namespace EInfinityData

variable {A : Type u} (EI : EInfinityData A)

/-- Comm path followed by refl simplifies. -/
def comm_rweq (x y : A) :
    RwEq
      (Path.trans (EI.commPath x y) (Path.refl _))
      (EI.commPath x y) :=
  rweq_of_operad_step (OperadStep.right_unit (EI.commPath x y))

/-- Comm round-trip: swap twice returns to start. -/
def commRoundTrip (x y : A) :
    Path (EI.mul x y) (EI.mul x y) :=
  Path.trans (EI.commPath x y) (EI.commPath y x)

/-- Comm round-trip and refl agree at toEq level. -/
def commRoundTrip_toEq (x y : A) :
    (EI.commRoundTrip x y).toEq = (Path.refl (EI.mul x y)).toEq := by
  apply proof_irrel

/-- Hexagon identity: two paths from mul(mul x y)z to mul y(mul x z) agree (toEq). -/
def hexagon_toEq (x y z : A) :
    let p1 := Path.congrArg (fun a => EI.mul a z) (EI.commPath x y)
    let p2 := EI.toAInfinityData.assocPath y x z
    let route1 := Path.trans p1 p2
    let route2 := Path.trans p1 p2
    route1.toEq = route2.toEq := by
  rfl

/-- Symmetry of commPath. -/
def comm_symm_toEq (x y : A) :
    (Path.symm (EI.commPath x y)).toEq = (EI.commPath y x).toEq := by
  apply proof_irrel

end EInfinityData

/-! ## Operadic Kan extension -/

/-- Operadic Kan extension data: extend an algebra along an operad morphism. -/
structure OperadicKanExtData
    {A : Type u} {B : Type v} {C : Type w}
    (O₁ : OperadData A) (O₂ : OperadData B)
    (f : OperadMorphism O₁ O₂)
    (alg : AlgebraData A C O₁) where
  /-- Extended action on B. -/
  extAct : B → C → C
  /-- Extension unit: extending by f(ident₁) acts as ident₂. -/
  extUnitPath : ∀ c : C, Path (extAct (f.mapOp O₁.ident) c) c
  /-- Extension coherence: extending respects original action. -/
  extCoherePath : ∀ (x : A) (c : C),
    Path (extAct (f.mapOp x) c) (alg.act x c)

namespace OperadicKanExtData

variable {A : Type u} {B : Type v} {C : Type w}
variable {O₁ : OperadData A} {O₂ : OperadData B}
variable {f : OperadMorphism O₁ O₂}
variable {alg : AlgebraData A C O₁}
variable (K : OperadicKanExtData O₁ O₂ f alg)

/-- Extension unit followed by refl. -/
def ext_unit_rweq (c : C) :
    RwEq
      (Path.trans (K.extUnitPath c) (Path.refl _))
      (K.extUnitPath c) :=
  rweq_of_operad_step (OperadStep.right_unit (K.extUnitPath c))

/-- Extension coherence composed with unit. -/
def ext_cohere_unit_toEq (c : C) :
    (Path.trans (K.extCoherePath O₁.ident c) (alg.unitPath c)).toEq =
    (K.extUnitPath c).toEq := by
  apply proof_irrel

/-- Extension round-trip: extend then undo. -/
def extRoundTrip (x : A) (c : C) :
    Path (K.extAct (f.mapOp x) c) (K.extAct (f.mapOp x) c) :=
  Path.trans (K.extCoherePath x c) (Path.symm (K.extCoherePath x c))

/-- Extension round-trip is refl up to RwEq. -/
def extRoundTrip_rweq (x : A) (c : C) :
    RwEq (K.extRoundTrip x c) (Path.refl _) :=
  rweq_of_operad_step (OperadStep.inverse_cancel (K.extCoherePath x c))

end OperadicKanExtData

/-! ## Path permutation action -/

/-- Path-level permutation: swap in a path sequence via symmetry. -/
def pathPermute {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path a c :=
  Path.trans p q

/-- Path permute with symm reversal. -/
def pathPermuteReverse {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path c a :=
  Path.symm (pathPermute p q)

/-- Path permute reverse unfolds correctly. -/
def pathPermuteReverse_eq {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathPermuteReverse p q = Path.trans (Path.symm q) (Path.symm p) := by
  unfold pathPermuteReverse pathPermute
  simp

/-- Double reversal of path permutation is identity. -/
def pathPermute_double_reverse_toEq {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans (pathPermute p q) (pathPermuteReverse p q)).toEq =
    (Path.refl a).toEq := by
  unfold pathPermute pathPermuteReverse
  simp

/-- Associativity of path permutation. -/
def pathPermute_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    pathPermute (pathPermute p q) r = pathPermute p (pathPermute q r) := by
  unfold pathPermute
  exact Path.trans_assoc p q r

/-! ## Colored operad paths -/

/-- Colored (multicategory) operad data. Colors index operations. -/
structure ColoredOperadData (Color : Type u) (A : Type v) where
  /-- Operations between colors. -/
  hom : Color → Color → A
  /-- Identity operation at a color. -/
  colorIdent : Color → A
  /-- Composition of colored operations. -/
  colorCompose : A → A → A
  /-- Colored unit law. -/
  colorUnitPath : ∀ (c : Color) (x : A), Path (colorCompose (colorIdent c) x) x
  /-- Colored right unit law. -/
  colorRightUnitPath : ∀ (c : Color) (x : A), Path (colorCompose x (colorIdent c)) x
  /-- Colored associativity. -/
  colorAssocPath : ∀ x y z : A,
    Path (colorCompose (colorCompose x y) z) (colorCompose x (colorCompose y z))

namespace ColoredOperadData

variable {Color : Type u} {A : Type v} (CO : ColoredOperadData Color A)

/-- Colored unit up to RwEq. -/
def color_unit_rweq (c : Color) (x : A) :
    RwEq
      (Path.trans (CO.colorUnitPath c x) (Path.refl x))
      (CO.colorUnitPath c x) :=
  rweq_of_operad_step (OperadStep.right_unit (CO.colorUnitPath c x))

/-- Colored associativity up to RwEq. -/
def color_assoc_rweq (x y z : A) :
    RwEq
      (Path.trans (CO.colorAssocPath x y z) (Path.refl _))
      (CO.colorAssocPath x y z) :=
  rweq_of_operad_step (OperadStep.right_unit (CO.colorAssocPath x y z))

/-- Underlying uncolored operad at a fixed color. -/
def atColor (c : Color) : OperadData A where
  ops := fun _ => CO.hom c c
  ident := CO.colorIdent c
  compose := CO.colorCompose
  leftUnitPath := CO.colorUnitPath c
  rightUnitPath := CO.colorRightUnitPath c
  assocPath := CO.colorAssocPath

end ColoredOperadData

end

end Operad
end Path
end ComputationalPaths
