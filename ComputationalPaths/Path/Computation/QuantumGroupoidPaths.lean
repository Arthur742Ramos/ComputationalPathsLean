/-
# Quantum Mechanics as a Groupoid via Computational Paths

Quantum states connected by unitary paths, gate composition IS trans,
gate inverse IS symm, measurement as path projection. All operations
structurally use Path, Step, trans, symm, congrArg, transport.

## Main results (34 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumGroupoidPaths

open ComputationalPaths.Path

/-! ## Quantum state space -/

/-- A quantum state with discrete labels. -/
structure QState where
  level : Nat
  phase : Nat
deriving DecidableEq, Repr

@[simp] def groundState : QState := ⟨0, 0⟩
@[simp] def excited1 : QState := ⟨1, 0⟩
@[simp] def excited2 : QState := ⟨2, 0⟩

/-! ## Quantum gates -/

/-- Pauli-X analogue: swap level bits. -/
@[simp] def pauliX (q : QState) : QState := ⟨q.phase, q.level⟩

/-- Phase shift. -/
@[simp] def phaseShift (q : QState) : QState := ⟨q.level, q.phase + 1⟩

/-- Identity gate. -/
@[simp] def gateId (q : QState) : QState := q

/-- Level doubling gate. -/
@[simp] def levelDouble (q : QState) : QState := ⟨q.level + q.level, q.phase⟩

/-- Phase reset (measurement projection). -/
@[simp] def measureProject (q : QState) : QState := ⟨q.level, 0⟩

/-- Level-phase swap. -/
@[simp] def lpSwap (q : QState) : QState := ⟨q.phase, q.level⟩

/-! ## Groupoid structure: morphisms ARE paths, composition IS trans, inverse IS symm -/

/-- A unitary morphism between quantum states IS a path. -/
abbrev UnitaryMorphism (a b : QState) := Path a b

/-- Identity morphism IS refl. -/
def idMorphism (a : QState) : UnitaryMorphism a a := Path.refl a

/-- Composition of morphisms IS trans. -/
def composeMorphism {a b c : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) : UnitaryMorphism a c :=
  Path.trans f g

/-- Inverse of a morphism IS symm. -/
def inverseMorphism {a b : QState}
    (f : UnitaryMorphism a b) : UnitaryMorphism b a :=
  Path.symm f

/-! ## Core groupoid laws -/

-- 1. Associativity of morphism composition (IS trans_assoc)
theorem morphism_assoc {a b c d : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) (h : UnitaryMorphism c d) :
    composeMorphism (composeMorphism f g) h =
    composeMorphism f (composeMorphism g h) :=
  Path.trans_assoc f g h

-- 2. Left identity (IS trans_refl_left)
theorem morphism_left_id {a b : QState} (f : UnitaryMorphism a b) :
    composeMorphism (idMorphism a) f = f :=
  Path.trans_refl_left f

-- 3. Right identity (IS trans_refl_right)
theorem morphism_right_id {a b : QState} (f : UnitaryMorphism a b) :
    composeMorphism f (idMorphism b) = f :=
  Path.trans_refl_right f

-- 4. Double inverse (IS symm_symm)
theorem morphism_double_inv {a b : QState} (f : UnitaryMorphism a b) :
    inverseMorphism (inverseMorphism f) = f :=
  Path.symm_symm f

-- 5. Inverse distributes over composition (IS symm_trans)
theorem morphism_inv_distrib {a b c : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) :
    inverseMorphism (composeMorphism f g) =
    composeMorphism (inverseMorphism g) (inverseMorphism f) :=
  Path.symm_trans f g

-- 6. Inverse of identity is identity (IS symm_refl)
theorem morphism_inv_id (a : QState) :
    inverseMorphism (idMorphism a) = idMorphism a :=
  Path.symm_refl a

-- 7. Semantic content: inverse-then-original has trivial equality
theorem morphism_inv_left_eq {a b : QState} (f : UnitaryMorphism a b) :
    (composeMorphism (inverseMorphism f) f).toEq = (idMorphism b).toEq := by
  simp

-- 8. Semantic content: original-then-inverse has trivial equality
theorem morphism_inv_right_eq {a b : QState} (f : UnitaryMorphism a b) :
    (composeMorphism f (inverseMorphism f)).toEq = (idMorphism a).toEq := by
  simp

/-! ## Functorial gate action IS congrArg -/

-- 9. Gate action IS congrArg
def gateAction (gate : QState → QState) {a b : QState}
    (p : UnitaryMorphism a b) : UnitaryMorphism (gate a) (gate b) :=
  Path.congrArg gate p

-- 10. Gate action preserves composition
theorem gateAction_compose (gate : QState → QState) {a b c : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) :
    gateAction gate (composeMorphism f g) =
    composeMorphism (gateAction gate f) (gateAction gate g) :=
  Path.congrArg_trans gate f g

-- 11. Gate action commutes with inverse
theorem gateAction_inverse (gate : QState → QState) {a b : QState}
    (f : UnitaryMorphism a b) :
    gateAction gate (inverseMorphism f) =
    inverseMorphism (gateAction gate f) :=
  Path.congrArg_symm gate f

-- 12. PauliX is an involution
theorem pauliX_involution (q : QState) : pauliX (pauliX q) = q := by
  cases q; simp

def pauliX_inv_path (q : QState) : Path (pauliX (pauliX q)) q :=
  Path.ofEq (pauliX_involution q)

-- 13. lpSwap = pauliX (definitional)
theorem lpSwap_eq_pauliX (q : QState) : lpSwap q = pauliX q := by rfl

-- 14. PauliX roundtrip path (trans of path and its symm-shift)
def pauliX_roundtrip (q : QState) : Path q q :=
  Path.trans (Path.symm (pauliX_inv_path q)) (pauliX_inv_path q)

-- 15. Measurement is idempotent
theorem measure_idempotent (q : QState) :
    measureProject (measureProject q) = measureProject q := by simp

def measure_idempotent_path (q : QState) :
    Path (measureProject (measureProject q)) (measureProject q) :=
  Path.ofEq (measure_idempotent q)

-- 16. Measurement kills phase shift
theorem measure_kills_phase (q : QState) :
    measureProject (phaseShift q) = measureProject q := by simp

def measure_kills_phase_path (q : QState) :
    Path (measureProject (phaseShift q)) (measureProject q) :=
  Path.ofEq (measure_kills_phase q)

-- 17. Transport along gate path
def quantum_transport {D : QState → Type} {a b : QState}
    (p : UnitaryMorphism a b) (x : D a) : D b :=
  Path.transport p x

-- 18. Step construction for pauliX involution
def pauliX_inv_step (q : QState) : Step QState :=
  ⟨pauliX (pauliX q), q, pauliX_involution q⟩

-- 19. CongrArg through pauliX
def pauliX_functorial {a b : QState} (p : Path a b) :
    Path (pauliX a) (pauliX b) :=
  Path.congrArg pauliX p

-- 20. CongrArg through measureProject
def measure_functorial {a b : QState} (p : Path a b) :
    Path (measureProject a) (measureProject b) :=
  Path.congrArg measureProject p

-- 21. Gate identity gives trivial path
theorem gateId_trivial (q : QState) : gateId q = q := by rfl

-- 22. Composition of gate actions
theorem gateAction_comp (f g : QState → QState) {a b : QState}
    (p : UnitaryMorphism a b) :
    gateAction f (gateAction g p) = gateAction (f ∘ g) p := by
  simp [gateAction]

-- 23. Gate composition path: (f ∘ f) applied = f applied twice
theorem pauliX_comp_id : pauliX ∘ pauliX = gateId := by
  funext q; cases q; simp

def pauliX_comp_path : Path (pauliX ∘ pauliX) gateId :=
  Path.ofEq pauliX_comp_id

-- 24. Level doubling preserves phase
theorem levelDouble_phase (q : QState) : (levelDouble q).phase = q.phase := by simp

-- 25. PauliX on ground state
theorem pauliX_ground : pauliX groundState = groundState := by rfl

-- 26. MeasureProject on ground state
theorem measure_ground : measureProject groundState = groundState := by rfl

-- 27. Three-morphism composition
def triple_compose {a b c d : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) (h : UnitaryMorphism c d) :
    UnitaryMorphism a d :=
  Path.trans f (Path.trans g h)

-- 28. Triple compose agrees with iterated compose
theorem triple_compose_eq {a b c d : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) (h : UnitaryMorphism c d) :
    triple_compose f g h = composeMorphism f (composeMorphism g h) := by
  rfl

-- 29. Whiskering: congrArg of identity path
theorem whisker_refl (gate : QState → QState) (a : QState) :
    Path.congrArg gate (Path.refl a) = Path.refl (gate a) := by
  simp [Path.congrArg]

-- 30. Morphism between measured states via measure_functorial
def measured_morphism {a b : QState} (p : UnitaryMorphism a b) :
    UnitaryMorphism (measureProject a) (measureProject b) :=
  measure_functorial p

-- 31. Measurement absorbs: measured_morphism of compose = compose of measured_morphisms
theorem measured_compose {a b c : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) :
    measured_morphism (composeMorphism f g) =
    composeMorphism (measured_morphism f) (measured_morphism g) :=
  Path.congrArg_trans measureProject f g

-- 32. Measurement respects inverse
theorem measured_inverse {a b : QState}
    (f : UnitaryMorphism a b) :
    measured_morphism (inverseMorphism f) =
    inverseMorphism (measured_morphism f) :=
  Path.congrArg_symm measureProject f

-- 33. PauliX functorial preserves composition
theorem pauliX_func_compose {a b c : QState}
    (f : UnitaryMorphism a b) (g : UnitaryMorphism b c) :
    pauliX_functorial (composeMorphism f g) =
    composeMorphism (pauliX_functorial f) (pauliX_functorial g) :=
  Path.congrArg_trans pauliX f g

-- 34. PauliX functorial preserves inverse
theorem pauliX_func_inverse {a b : QState}
    (f : UnitaryMorphism a b) :
    pauliX_functorial (inverseMorphism f) =
    inverseMorphism (pauliX_functorial f) :=
  Path.congrArg_symm pauliX f

end ComputationalPaths.Path.Computation.QuantumGroupoidPaths
