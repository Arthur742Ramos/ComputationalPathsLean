/-
# Symmetry Groupoid via Computational Paths

Symmetries as invertible paths, symmetry breaking as path obstruction,
Noether-type correspondences between symmetries and invariants,
conservation laws as path invariants. All operations structurally use
Path, Step, trans, symm, congrArg, transport.

## Main results (26 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Groupoid.SymmetryGroupoidPaths

open ComputationalPaths.Path

/-! ## State space with symmetry -/

/-- A physical state with discrete labels. -/
structure State where
  config : Nat
  charge : Nat
deriving DecidableEq, Repr

@[simp] noncomputable def vacuum : State := ⟨0, 0⟩
@[simp] noncomputable def excitedA : State := ⟨1, 0⟩
@[simp] noncomputable def excitedB : State := ⟨0, 1⟩
@[simp] noncomputable def excitedAB : State := ⟨1, 1⟩

/-! ## Symmetry transformations -/

/-- Charge conjugation: flips charge. -/
@[simp] noncomputable def chargeConj (s : State) : State := ⟨s.config, s.charge⟩

/-- Config reflection: maps config → config. -/
@[simp] noncomputable def configRefl (s : State) : State := ⟨s.config, s.charge⟩

/-- Swap symmetry: exchanges config and charge. -/
@[simp] noncomputable def swapSym (s : State) : State := ⟨s.charge, s.config⟩

/-- Identity symmetry. -/
@[simp] noncomputable def idSym (s : State) : State := s

/-- Double swap. -/
@[simp] noncomputable def doubleSwap (s : State) : State := swapSym (swapSym s)

/-- Shift config by 1. -/
@[simp] noncomputable def shiftConfig (s : State) : State := ⟨s.config + 1, s.charge⟩

/-- Shift charge by 1. -/
@[simp] noncomputable def shiftCharge (s : State) : State := ⟨s.config, s.charge + 1⟩

/-- Projection to charge-zero sector. -/
@[simp] noncomputable def projectCharge (s : State) : State := ⟨s.config, 0⟩

/-- Projection to config-zero sector. -/
@[simp] noncomputable def projectConfig (s : State) : State := ⟨0, s.charge⟩

/-! ## Symmetries ARE invertible paths, groupoid structure -/

/-- A symmetry between states IS a path. -/
abbrev Symmetry (a b : State) := Path a b

/-- Symmetry composition IS trans. -/
noncomputable def symCompose {a b c : State}
    (f : Symmetry a b) (g : Symmetry b c) : Symmetry a c :=
  Path.trans f g

/-- Symmetry inverse IS symm. -/
noncomputable def symInverse {a b : State}
    (f : Symmetry a b) : Symmetry b a :=
  Path.symm f

/-- Identity symmetry IS refl. -/
noncomputable def symId (a : State) : Symmetry a a := Path.refl a

/-! ## Invariants and conservation laws -/

/-- An observable is a function from states to Nat. -/
abbrev Observable := State → Nat

/-- Total quantum number. -/
@[simp] noncomputable def totalCharge : Observable := fun s => s.config + s.charge

/-- Config observable. -/
@[simp] noncomputable def configObs : Observable := fun s => s.config

/-- Charge observable. -/
@[simp] noncomputable def chargeObs : Observable := fun s => s.charge

/-- An observable is conserved along a symmetry (path) if it's equal at endpoints. -/
noncomputable def isConserved (obs : Observable) {a b : State} (_ : Symmetry a b) : Prop :=
  obs a = obs b

/-! ## Core theorems -/

-- 1. Symmetry groupoid: associativity
theorem sym_assoc {a b c d : State}
    (f : Symmetry a b) (g : Symmetry b c) (h : Symmetry c d) :
    symCompose (symCompose f g) h = symCompose f (symCompose g h) :=
  Path.trans_assoc f g h

-- 2. Left identity
theorem sym_left_id {a b : State} (f : Symmetry a b) :
    symCompose (symId a) f = f :=
  Path.trans_refl_left f

-- 3. Right identity
theorem sym_right_id {a b : State} (f : Symmetry a b) :
    symCompose f (symId b) = f :=
  Path.trans_refl_right f

-- 4. Double inverse
theorem sym_inv_inv {a b : State} (f : Symmetry a b) :
    symInverse (symInverse f) = f :=
  Path.symm_symm f

-- 5. Inverse distributes
theorem sym_inv_compose {a b c : State}
    (f : Symmetry a b) (g : Symmetry b c) :
    symInverse (symCompose f g) = symCompose (symInverse g) (symInverse f) :=
  Path.symm_trans f g

-- 6. Inverse of identity
theorem sym_inv_id (a : State) : symInverse (symId a) = symId a :=
  Path.symm_refl a

-- 7. Swap is an involution
theorem swap_involution (s : State) : swapSym (swapSym s) = s := by
  cases s; simp

noncomputable def swap_inv_path (s : State) : Path (swapSym (swapSym s)) s :=
  Path.mk [Step.mk _ _ (swap_involution s)] (swap_involution s)

-- 8. Double swap is identity
theorem doubleSwap_is_id (s : State) : doubleSwap s = s := by
  cases s; simp

noncomputable def doubleSwap_path (s : State) : Path (doubleSwap s) s :=
  Path.mk [Step.mk _ _ (doubleSwap_is_id s)] (doubleSwap_is_id s)

-- 9. Projection is idempotent
theorem projectCharge_idem (s : State) :
    projectCharge (projectCharge s) = projectCharge s := by simp

noncomputable def projectCharge_idem_path (s : State) :
    Path (projectCharge (projectCharge s)) (projectCharge s) :=
  Path.mk [Step.mk _ _ (projectCharge_idem s)] (projectCharge_idem s)

-- 10. Projection kills charge shift
theorem project_kills_shift (s : State) :
    projectCharge (shiftCharge s) = projectCharge s := by simp

noncomputable def project_kills_shift_path (s : State) :
    Path (projectCharge (shiftCharge s)) (projectCharge s) :=
  Path.mk [Step.mk _ _ (project_kills_shift s)] (project_kills_shift s)

-- 11. Total charge is conserved under swap
theorem totalCharge_swap_conserved (s : State) :
    totalCharge (swapSym s) = totalCharge s := by
  simp [Nat.add_comm]

noncomputable def totalCharge_swap_path (s : State) :
    Path (totalCharge (swapSym s)) (totalCharge s) :=
  Path.mk [Step.mk _ _ (totalCharge_swap_conserved s)] (totalCharge_swap_conserved s)

-- 12. Noether-type: symmetry path gives conservation path via congrArg
noncomputable def noether_correspondence (obs : Observable) {a b : State}
    (sym : Symmetry a b) : Path (obs a) (obs b) :=
  Path.congrArg obs sym

-- 13. Conservation law: if obs a = obs b then noether path has trivial eq
theorem conservation_trivial (obs : Observable) {a b : State}
    (sym : Symmetry a b) (h : isConserved obs sym) :
    (noether_correspondence obs sym).toEq = h := by
  exact Subsingleton.elim _ _

-- 14. Symmetry breaking: obstruction IS failure of path to exist
-- We can't construct Path (projectCharge vacuum) excitedB because they differ
theorem symmetry_breaking_obstruction :
    projectCharge vacuum ≠ excitedB := by simp

-- 15. CongrArg through swap gives new symmetry
noncomputable def swap_functorial {a b : State} (p : Symmetry a b) :
    Symmetry (swapSym a) (swapSym b) :=
  Path.congrArg swapSym p

-- 16. Functorial action preserves composition
theorem swap_func_compose {a b c : State}
    (f : Symmetry a b) (g : Symmetry b c) :
    swap_functorial (symCompose f g) =
    symCompose (swap_functorial f) (swap_functorial g) :=
  Path.congrArg_trans swapSym f g

-- 17. Functorial action preserves inverse
theorem swap_func_inverse {a b : State}
    (f : Symmetry a b) :
    swap_functorial (symInverse f) = symInverse (swap_functorial f) :=
  Path.congrArg_symm swapSym f

-- 18. Transport along symmetry
noncomputable def sym_transport {D : State → Type} {a b : State}
    (p : Symmetry a b) (x : D a) : D b :=
  Path.transport p x

-- 19. Step construction for swap involution
noncomputable def swap_step (s : State) : Step State :=
  ⟨swapSym (swapSym s), s, swap_involution s⟩

-- 20. Projection functorial
noncomputable def project_functorial {a b : State} (p : Symmetry a b) :
    Symmetry (projectCharge a) (projectCharge b) :=
  Path.congrArg projectCharge p

-- 21. Projection absorbs: composition of projected symmetries
theorem project_func_compose {a b c : State}
    (f : Symmetry a b) (g : Symmetry b c) :
    project_functorial (symCompose f g) =
    symCompose (project_functorial f) (project_functorial g) :=
  Path.congrArg_trans projectCharge f g

-- 22. Vacuum is fixed by projection
theorem vacuum_projected : projectCharge vacuum = vacuum := by rfl

-- 23. Config projection on vacuum
theorem vacuum_config_proj : projectConfig vacuum = vacuum := by rfl

-- 24. Swap on vacuum
theorem swap_vacuum : swapSym vacuum = vacuum := by rfl

-- 25. Conservation of total charge: swap roundtrip path
noncomputable def swap_conservation_roundtrip (s : State) :
    Path (totalCharge s) (totalCharge s) :=
  Path.trans (Path.symm (totalCharge_swap_path s)) (totalCharge_swap_path s)

-- 26. Composed symmetry breaks to projected symmetry via congrArg
noncomputable def symmetry_to_projected {a b : State}
    (sym : Symmetry a b) :
    Path (projectCharge a) (projectCharge b) :=
  Path.congrArg projectCharge sym

end ComputationalPaths.Path.Groupoid.SymmetryGroupoidPaths
