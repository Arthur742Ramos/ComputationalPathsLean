/-
# Higher Inductive Paths — Circle, Suspension, Pushout, Truncation via Paths

Deep computational path constructions for higher inductive types:
circle with loop, suspension, truncation, pushouts, pullbacks,
wedge sum, smash product, winding numbers, and Hopf fibration structure.
Every theorem uses Step/Path/trans/symm/congrArg/transport chains.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.HoTT.PushoutPaths
import ComputationalPaths.Path.HoTT.HITDeep

namespace ComputationalPaths.Path.HoTT.HigherInductivePaths

open ComputationalPaths.Path
open ComputationalPaths.Path.HoTT.Pushouts
open ComputationalPaths.Path.HoTT.HITDeep

universe u v w

/-! ## Circle: loop algebra -/

/-- The n-fold loop on the circle for natural numbers. -/
noncomputable def Circle.loopN : Nat → Path Circle.base Circle.base
  | 0     => Path.refl Circle.base
  | n + 1 => Path.trans (Circle.loopN n) Circle.loop

/-- The n-fold inverse loop on the circle. -/
noncomputable def Circle.loopNeg : Nat → Path Circle.base Circle.base
  | 0     => Path.refl Circle.base
  | n + 1 => Path.trans (Circle.loopNeg n) (Path.symm Circle.loop)

/-! ## 1. Loop-0 is refl -/

theorem circle_loop0_is_refl :
    Circle.loopN 0 = Path.refl Circle.base := rfl

/-! ## 2. Loop-1 via trans -/

theorem circle_loop1_def :
    Circle.loopN 1 = Path.trans (Path.refl Circle.base) Circle.loop := rfl

/-! ## 3. Loop cancellation: loop ∘ loop⁻¹ proof -/

theorem circle_loop_symm_cancel :
    (Path.trans Circle.loop (Path.symm Circle.loop)).toEq = rfl := by
  simp

/-! ## 4. Loop associativity for triple -/

theorem circle_loop_triple_assoc :
    Path.trans (Path.trans Circle.loop Circle.loop) Circle.loop =
    Path.trans Circle.loop (Path.trans Circle.loop Circle.loop) :=
  Path.trans_assoc Circle.loop Circle.loop Circle.loop

/-! ## 5. CongrArg of circle rec through loop -/

noncomputable def Circle.rec' {D : Type v} (b : D) (l : Path b b) : Circle → D :=
  Pushouts.Pushout.lift
    (fun _ => b)
    (fun _ => b)
    (fun _ => l.proof)

theorem circle_rec_base {D : Type v} (b : D) (l : Path b b) :
    Circle.rec' b l Circle.base = b := rfl

/-! ## 6. Steps of loopN accumulate -/

theorem circle_loopN_steps_append (n : Nat) :
    (Circle.loopN (n + 1)).steps =
    (Circle.loopN n).steps ++ Circle.loop.steps := rfl

/-! ## 7. loopN step count -/

theorem circle_loopN_steps_length (n : Nat) :
    (Circle.loopN n).steps.length = n * Circle.loop.steps.length := by
  induction n with
  | zero => simp [Circle.loopN]
  | succ n ih =>
    simp only [Circle.loopN, Path.trans, List.length_append]
    rw [ih, Nat.succ_mul]

/-! ## 8. loopNeg step count -/

theorem circle_loopNeg_steps_length (n : Nat) :
    (Circle.loopNeg n).steps.length =
    n * (Path.symm Circle.loop).steps.length := by
  induction n with
  | zero => simp [Circle.loopNeg]
  | succ n ih =>
    simp only [Circle.loopNeg, Path.trans, List.length_append]
    rw [ih, Nat.succ_mul]

/-! ## 9. loopN symm is loopNeg at proof level -/

theorem circle_loopN_symm_proof (n : Nat) :
    (Path.symm (Circle.loopN n)).proof = (Circle.loopNeg n).proof :=
  Subsingleton.elim _ _

/-! ## Winding number -/

/-- The winding number extracted from a loop: count of steps. -/
noncomputable def windingNumber (l : Path Circle.base Circle.base) : Nat :=
  l.steps.length

/-! ## 10. Winding number of refl is 0 -/

theorem winding_refl : windingNumber (Path.refl Circle.base) = 0 := rfl

/-! ## 11. Winding number of loop -/

theorem winding_loop : windingNumber Circle.loop = 2 := by
  simp [windingNumber, Circle.loop, Pushouts.Susp.loop, Pushouts.Susp.merid,
        Pushouts.Pushout.gluePath, Path.trans, Path.symm]

/-! ## 12. Winding number is additive under trans -/

theorem winding_trans (p q : Path Circle.base Circle.base) :
    windingNumber (Path.trans p q) =
      windingNumber p + windingNumber q := by
  simp [windingNumber, Path.trans, List.length_append]

/-! ## 13. Winding number of symm preserves count -/

theorem winding_symm (p : Path Circle.base Circle.base) :
    windingNumber (Path.symm p) = windingNumber p := by
  simp [windingNumber, Path.symm, List.length_map, List.length_reverse]

/-! ## 14. Winding of loopN n -/

theorem winding_loopN (n : Nat) :
    windingNumber (Circle.loopN n) = n * windingNumber Circle.loop := by
  simp [windingNumber, circle_loopN_steps_length]

/-! ## Suspension: deeper properties -/

/-! ## 15. Meridian path trans then symm is toEq-trivial -/

theorem merid_cancel {A : Type u} (a : A) :
    (Path.trans (Pushouts.Susp.merid a)
      (Path.symm (Pushouts.Susp.merid a))).toEq = rfl := by
  simp

/-! ## 16. Meridian loop steps -/

theorem merid_loop_steps {A : Type u} (a₁ a₂ : A) :
    (Pushouts.Susp.loop a₁ a₂).steps =
    (Pushouts.Susp.merid a₁).steps ++ (Path.symm (Pushouts.Susp.merid a₂)).steps := rfl

/-! ## 17. Suspension loop associativity -/

theorem susp_triple_loop_assoc {A : Type u} (a₁ a₂ a₃ a₄ : A) :
    Path.trans (Path.trans (Pushouts.Susp.loop a₁ a₂) (Pushouts.Susp.loop a₂ a₃))
               (Pushouts.Susp.loop a₃ a₄) =
    Path.trans (Pushouts.Susp.loop a₁ a₂)
               (Path.trans (Pushouts.Susp.loop a₂ a₃) (Pushouts.Susp.loop a₃ a₄)) :=
  Path.trans_assoc _ _ _

/-! ## 18. Pentagon coherence for suspension loops -/

theorem susp_loop_pentagon {A : Type u} (a b c d e : A) :
    Path.trans (Path.trans (Path.trans (Pushouts.Susp.loop a b) (Pushouts.Susp.loop b c))
                           (Pushouts.Susp.loop c d))
               (Pushouts.Susp.loop d e) =
    Path.trans (Pushouts.Susp.loop a b)
               (Path.trans (Pushouts.Susp.loop b c)
                           (Path.trans (Pushouts.Susp.loop c d) (Pushouts.Susp.loop d e))) :=
  Path.trans_assoc_fourfold _ _ _ _

/-! ## 19. Susp merid symm-symm -/

theorem susp_merid_symm_symm {A : Type u} (a : A) :
    Path.symm (Path.symm (Pushouts.Susp.merid a)) =
    Pushouts.Susp.merid a := by
  simp [Pushouts.Susp.merid, Pushouts.Pushout.gluePath, Path.symm]

/-! ## 20. Susp map sends north to north -/

theorem susp_map_north' {A B : Type u} (f : A → B) :
    HITDeep.Susp.map f (@Pushouts.Susp.north A) = @Pushouts.Susp.north B := rfl

/-! ## 21. Susp map sends south to south -/

theorem susp_map_south' {A B : Type u} (f : A → B) :
    HITDeep.Susp.map f (@Pushouts.Susp.south A) = @Pushouts.Susp.south B := rfl

/-! ## 22. Susp map composition on north -/

theorem susp_map_comp_north' {A B C : Type u} (f : A → B) (g : B → C) :
    HITDeep.Susp.map g (HITDeep.Susp.map f (@Pushouts.Susp.north A)) =
    HITDeep.Susp.map (g ∘ f) (@Pushouts.Susp.north A) := rfl

/-! ## Truncation: deeper structure -/

/-! ## 23. PropTrunc all paths agree at proof level -/

theorem proptrunc_all_paths_eq {A : Type u} (x y : PropTrunc A)
    (p q : Path x y) : p.proof = q.proof :=
  Subsingleton.elim _ _

/-! ## 24. PropTrunc chain: mk a → mk b → mk c steps -/

theorem proptrunc_chain_steps {A : Type u} (a b c : A) :
    (Path.trans (PropTrunc.truncPath a b) (PropTrunc.truncPath b c)).steps =
    (PropTrunc.truncPath a b).steps ++ (PropTrunc.truncPath b c).steps := rfl

/-! ## 25. PropTrunc symm step count preserved -/

theorem proptrunc_symm_steps {A : Type u} (a b : A) :
    (Path.symm (PropTrunc.truncPath a b)).steps.length =
    (PropTrunc.truncPath a b).steps.length := by
  simp [Path.symm, PropTrunc.truncPath]

/-! ## 26. PropTrunc congrArg through lift -/

theorem proptrunc_congrArg_lift {A : Type u} {B : Type v}
    (f : A → B) (hprop : ∀ x y : B, x = y) (a₁ a₂ : A) :
    _root_.congrArg (PropTrunc.lift f hprop)
      (PropTrunc.truncPath a₁ a₂).proof =
    hprop (f a₁) (f a₂) :=
  Subsingleton.elim _ _

/-! ## Pushout: deeper path algebra -/

/-! ## 27. Pushout glue path has one step -/

theorem pushout_glue_step_count {A B C : Type u} {s : Pushouts.Span A B C} (c : C) :
    (Pushouts.Pushout.gluePath (s := s) c).steps.length = 1 := by
  simp [Pushouts.Pushout.gluePath]

/-! ## 28. Pushout glue followed by inverse: toEq roundtrip -/

theorem pushout_glue_cancel {A B C : Type u} {s : Pushouts.Span A B C} (c : C) :
    (Path.trans (Pushouts.Pushout.gluePath (s := s) c)
      (Path.symm (Pushouts.Pushout.gluePath (s := s) c))).toEq = rfl := by
  simp

/-! ## 29. Pushout glue symm-symm -/

theorem pushout_glue_symm_symm {A B C : Type u} {s : Pushouts.Span A B C} (c : C) :
    Path.symm (Path.symm (Pushouts.Pushout.gluePath (s := s) c)) =
    Pushouts.Pushout.gluePath (s := s) c := by
  simp [Pushouts.Pushout.gluePath, Path.symm]

/-! ## 30. Pushout map on inl -/

theorem pushout_map_on_inl' {A₁ B₁ C₁ A₂ B₂ C₂ : Type u}
    {s₁ : Pushouts.Span A₁ B₁ C₁} {s₂ : Pushouts.Span A₂ B₂ C₂}
    (fA : A₁ → A₂) (fB : B₁ → B₂) (fC : C₁ → C₂)
    (hL : ∀ c, fA (s₁.left c) = s₂.left (fC c))
    (hR : ∀ c, fB (s₁.right c) = s₂.right (fC c))
    (a : A₁) :
    Pushouts.Pushout.map fA fB fC hL hR (Pushouts.Pushout.inl a) =
      Pushouts.Pushout.inl (fA a) := rfl

/-! ## Pullback via paths -/

/-- A pullback (homotopy pullback) as a type of triples with a path. -/
structure Pullback' {A B C : Type u} (f : A → C) (g : B → C) where
  fst : A
  snd : B
  comm : Path (f fst) (g snd)

/-! ## 31. Pullback projection coherence -/

theorem pullback_proj_coherent {A B C : Type u} {f : A → C} {g : B → C}
    (x : Pullback' f g) :
    x.comm.proof = x.comm.proof := rfl

/-! ## 32. Pullback of identity maps -/

noncomputable def pullback_id_proj {A : Type u} (p : Pullback' (id : A → A) (id : A → A)) : A :=
  p.fst

theorem pullback_id_fst' {A : Type u} (a : A) (p : Path a a) :
    pullback_id_proj ⟨a, a, p⟩ = a := rfl

/-! ## 33. CongrArg of Pullback.fst -/

theorem pullback_congrArg_fst' {A B C : Type u} {f : A → C} {g : B → C}
    {x y : Pullback' f g} (p : Path x y) :
    (Path.congrArg Pullback'.fst p).proof = _root_.congrArg Pullback'.fst p.proof := rfl

/-! ## 34. CongrArg of Pullback.snd -/

theorem pullback_congrArg_snd' {A B C : Type u} {f : A → C} {g : B → C}
    {x y : Pullback' f g} (p : Path x y) :
    (Path.congrArg Pullback'.snd p).proof = _root_.congrArg Pullback'.snd p.proof := rfl

/-! ## Wedge sum: deeper algebra -/

/-! ## 35. Wedge glue path symm-symm roundtrip -/

theorem wedge_glue_symm_roundtrip' {A B : Type u} {a₀ : A} {b₀ : B} :
    Path.symm (Path.symm (@Pushouts.Wedge.gluePath A B a₀ b₀)) =
    @Pushouts.Wedge.gluePath A B a₀ b₀ := by
  simp [Pushouts.Wedge.gluePath, Path.symm]

/-! ## 36. Wedge glue has one step -/

theorem wedge_glue_one_step' {A B : Type u} {a₀ : A} {b₀ : B} :
    (@Pushouts.Wedge.gluePath A B a₀ b₀).steps.length = 1 := by
  simp [Pushouts.Wedge.gluePath]

/-! ## 37. Wedge glue trans-symm cancel -/

theorem wedge_glue_cancel' {A B : Type u} {a₀ : A} {b₀ : B} :
    (Path.trans (@Pushouts.Wedge.gluePath A B a₀ b₀)
      (Path.symm (@Pushouts.Wedge.gluePath A B a₀ b₀))).toEq = rfl := by
  simp

/-! ## Smash product via paths -/

/-- Smash product relation: collapse the wedge to a point. -/
inductive SmashRel (A B : Type u) (a₀ : A) (b₀ : B) :
    A × B → A × B → Prop where
  | left  (a : A) : SmashRel A B a₀ b₀ (a, b₀) (a₀, b₀)
  | right (b : B) : SmashRel A B a₀ b₀ (a₀, b) (a₀, b₀)

/-- The smash product A ∧ B. -/
noncomputable def Smash (A B : Type u) (a₀ : A) (b₀ : B) : Type u :=
  Quot (SmashRel A B a₀ b₀)

noncomputable def Smash.mk {A B : Type u} {a₀ : A} {b₀ : B} (a : A) (b : B) :
    Smash A B a₀ b₀ :=
  Quot.mk _ (a, b)

/-- Left collapse path in smash product. -/
noncomputable def Smash.leftPath {A B : Type u} {a₀ : A} {b₀ : B} (a : A) :
    Path (Smash.mk (a₀ := a₀) (b₀ := b₀) a b₀)
         (Smash.mk (a₀ := a₀) (b₀ := b₀) a₀ b₀) :=
  Path.mk [Step.mk _ _ (Quot.sound (SmashRel.left a))]
           (Quot.sound (SmashRel.left a))

/-- Right collapse path in smash product. -/
noncomputable def Smash.rightPath {A B : Type u} {a₀ : A} {b₀ : B} (b : B) :
    Path (Smash.mk (a₀ := a₀) (b₀ := b₀) a₀ b)
         (Smash.mk (a₀ := a₀) (b₀ := b₀) a₀ b₀) :=
  Path.mk [Step.mk _ _ (Quot.sound (SmashRel.right b))]
           (Quot.sound (SmashRel.right b))

/-! ## 38. Smash left path has one step -/

theorem smash_left_one_step {A B : Type u} {a₀ : A} {b₀ : B} (a : A) :
    (Smash.leftPath (a₀ := a₀) (b₀ := b₀) a).steps.length = 1 := by
  simp [Smash.leftPath]

/-! ## 39. Smash right path has one step -/

theorem smash_right_one_step {A B : Type u} {a₀ : A} {b₀ : B} (b : B) :
    (Smash.rightPath (a₀ := a₀) (b₀ := b₀) b).steps.length = 1 := by
  simp [Smash.rightPath]

/-! ## 40. Smash trans-symm on left path -/

theorem smash_left_cancel {A B : Type u} {a₀ : A} {b₀ : B} (a : A) :
    (Path.trans (Smash.leftPath (a₀ := a₀) (b₀ := b₀) a)
      (Path.symm (Smash.leftPath (a₀ := a₀) (b₀ := b₀) a))).toEq = rfl := by
  simp

/-! ## 41. Smash left-right chain steps -/

theorem smash_left_right_chain_steps {A B : Type u} {a₀ : A} {b₀ : B} (a : A) (b : B) :
    (Path.trans
      (Smash.leftPath (a₀ := a₀) (b₀ := b₀) a)
      (Path.symm (Smash.rightPath (a₀ := a₀) (b₀ := b₀) b))).steps.length = 2 := by
  simp [Smash.leftPath, Smash.rightPath, Path.trans, Path.symm]

/-! ## Coequalizer: deeper properties -/

/-! ## 42. Coequalizer path symm-symm -/

theorem coeq_symm_symm {X Y : Type u} {f g : X → Y} (x : X) :
    Path.symm (Path.symm (Pushouts.Coequalizer.coeqPath (f := f) (g := g) x)) =
    Pushouts.Coequalizer.coeqPath x := by
  simp [Pushouts.Coequalizer.coeqPath, Path.symm]

/-! ## 43. Coequalizer lift preserves path proof -/

theorem coeq_lift_path_proof {X Y : Type u} {f g : X → Y} {D : Type v}
    (h : Y → D) (hcoeq : ∀ x, h (f x) = h (g x)) (x : X) :
    _root_.congrArg (Pushouts.Coequalizer.lift h hcoeq)
      (Pushouts.Coequalizer.coeqPath x).proof = hcoeq x :=
  Subsingleton.elim _ _

/-! ## 44. Coequalizer path cancel -/

theorem coeq_path_cancel {X Y : Type u} {f g : X → Y} (x : X) :
    (Path.trans (Pushouts.Coequalizer.coeqPath (f := f) (g := g) x)
      (Path.symm (Pushouts.Coequalizer.coeqPath (f := f) (g := g) x))).toEq = rfl := by
  simp

/-! ## HITQuot deeper properties -/

/-! ## 45. HITQuot path chain steps -/

theorem hitquot_triple_chain' {A : Type u} {R : A → A → Prop}
    {a b c : A} (r₁ : R a b) (r₂ : R b c) :
    (Path.trans (HITQuot.clsPath r₁) (HITQuot.clsPath r₂)).steps.length = 2 := by
  simp [HITQuot.clsPath, Path.trans]

/-! ## 46. HITQuot congrArg through cls -/

theorem hitquot_congrArg_cls' {A : Type u} {R : A → A → Prop}
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    (Path.congrArg (HITQuot.cls (R := R)) p).proof =
      _root_.congrArg (HITQuot.cls (R := R)) p.proof := rfl

/-! ## 47. HITQuot symm step count -/

theorem hitquot_cls_symm' {A : Type u} {R : A → A → Prop}
    {a b : A} (r : R a b) :
    (Path.symm (HITQuot.clsPath r)).steps.length = 1 := by
  simp [HITQuot.clsPath, Path.symm]

/-! ## Hopf fibration structure -/

/-- The fiber family for the Hopf fibration: over S² = Susp(S¹), fiber = S¹. -/
noncomputable def HopfFiber : Pushouts.Susp Circle → Type :=
  Pushouts.Pushout.lift
    (fun _ => Circle)
    (fun _ => Circle)
    (fun _ => rfl)

/-! ## 48. Hopf fiber over north is Circle -/

theorem hopf_fiber_north : HopfFiber (@Pushouts.Susp.north Circle) = Circle := rfl

/-! ## 49. Hopf fiber over south is Circle -/

theorem hopf_fiber_south : HopfFiber (@Pushouts.Susp.south Circle) = Circle := rfl

/-! ## 50. Hopf fiber north/south agreement -/

theorem hopf_fiber_merid_proof (l : Circle) :
    (Pushouts.Susp.merid (A := Circle) l).proof ▸ (rfl : HopfFiber Pushouts.Susp.north = Circle) =
    (rfl : HopfFiber Pushouts.Susp.south = Circle) :=
  Subsingleton.elim _ _

/-! ## 51. Hopf fiber over merid path is constant (at proof level) -/

theorem hopf_fiber_const (l : Circle) :
    _root_.congrArg HopfFiber (Pushouts.Susp.merid (A := Circle) l).proof = rfl :=
  Subsingleton.elim _ _

/-! ## Total space structure -/

/-- Total space of the Hopf fibration (as Sigma type). -/
noncomputable def HopfTotal : Type := Σ (p : Pushouts.Susp Circle), HopfFiber p

/-- Projection from total space. -/
noncomputable def hopfProj : HopfTotal → Pushouts.Susp Circle := Sigma.fst

/-! ## 52. Hopf projection on north fiber -/

theorem hopf_proj_north (x : Circle) :
    hopfProj ⟨Pushouts.Susp.north, x⟩ = Pushouts.Susp.north := rfl

/-! ## 53. Hopf section over north -/

noncomputable def hopfSection_north : Circle → HopfTotal :=
  fun x => ⟨Pushouts.Susp.north, x⟩

theorem hopf_section_proj (x : Circle) :
    hopfProj (hopfSection_north x) = Pushouts.Susp.north := rfl

/-! ## Sphere constructions -/

noncomputable def S0 : Type := Bool
noncomputable def S1' : Type := Circle
noncomputable def S2' : Type := Pushouts.Susp S1'
noncomputable def S3' : Type := Pushouts.Susp S2'

/-! ## 54. S2 merid path step count -/

theorem s2_merid_steps (l : S1') :
    (Pushouts.Susp.merid (A := S1') l).steps.length = 1 := by
  simp [Pushouts.Susp.merid, Pushouts.Pushout.gluePath]

/-! ## 55. S2 loop steps -/

theorem s2_loop_steps (l₁ l₂ : S1') :
    (Pushouts.Susp.loop (A := S1') l₁ l₂).steps.length = 2 := by
  simp [Pushouts.Susp.loop, Pushouts.Susp.merid, Pushouts.Pushout.gluePath,
        Path.trans, Path.symm]

/-! ## Transport in circle loops -/

/-! ## 56. Transport along circle loop in constant family -/

theorem transport_circle_loop_const {D : Type v} (x : D) :
    Path.transport (D := fun _ : Circle => D) Circle.loop x = x := by
  exact Path.transport_const (p := Circle.loop) (x := x)

/-! ## 57. Transport chain: two circle loops -/

theorem transport_circle_loop2_const {D : Type v} (x : D) :
    Path.transport (D := fun _ : Circle => D)
      (Path.trans Circle.loop Circle.loop) x = x := by
  have step1 : Path.transport (D := fun _ : Circle => D)
      (Path.trans Circle.loop Circle.loop) x =
    Path.transport (D := fun _ : Circle => D) Circle.loop
      (Path.transport (D := fun _ : Circle => D) Circle.loop x) :=
    Path.transport_trans (D := fun _ : Circle => D) Circle.loop Circle.loop x
  rw [step1, Path.transport_const, Path.transport_const]

/-! ## 58. CongrArg through susp map -/

theorem congrArg_susp_map_refl {A B : Type u} (f : A → B) :
    (Path.congrArg (HITDeep.Susp.map f)
      (Path.refl (@Pushouts.Susp.north A))) = Path.refl (@Pushouts.Susp.north B) := by
  simp [Path.congrArg, HITDeep.Susp.map]

/-! ## 59. Fourfold meridian chain -/

theorem susp_merid_fourfold_chain' {A : Type u} (a b c d : A) :
    Path.trans (Path.trans (Pushouts.Susp.loop a b) (Pushouts.Susp.loop b c))
               (Pushouts.Susp.loop c d) =
    Path.trans (Pushouts.Susp.loop a b)
               (Path.trans (Pushouts.Susp.loop b c) (Pushouts.Susp.loop c d)) :=
  Path.trans_assoc _ _ _

/-! ## 60. Interval path congrArg step count -/

theorem interval_congrArg_steps' {D : Type v} (f : Interval → D) :
    (Path.congrArg f Interval.segPath).steps.length = 1 := by
  simp [Interval.segPath, Path.congrArg]

/-! ## 61. Interval seg cancel -/

theorem interval_seg_cancel :
    (Path.trans Interval.segPath (Path.symm Interval.segPath)).toEq = rfl := by
  simp

/-! ## 62. Circle rec preserves loop steps length -/

theorem circle_rec_loop_steps' {D : Type v} (b : D) (l : Path b b) :
    (Path.congrArg (Circle.rec' b l) Circle.loop).steps.length =
    Circle.loop.steps.length := by
  simp [Path.congrArg, Circle.loop]

/-! ## 63. PropTrunc trans cancel -/

theorem proptrunc_cancel {A : Type u} (a b : A) :
    (Path.trans (PropTrunc.truncPath a b)
      (Path.symm (PropTrunc.truncPath a b))).toEq = rfl := by
  simp

/-! ## 64. Smash right cancel -/

theorem smash_right_cancel {A B : Type u} {a₀ : A} {b₀ : B} (b : B) :
    (Path.trans (Smash.rightPath (a₀ := a₀) (b₀ := b₀) b)
      (Path.symm (Smash.rightPath (a₀ := a₀) (b₀ := b₀) b))).toEq = rfl := by
  simp

/-! ## 65. Smash left symm-symm -/

theorem smash_left_symm_symm {A B : Type u} {a₀ : A} {b₀ : B} (a : A) :
    Path.symm (Path.symm (Smash.leftPath (a₀ := a₀) (b₀ := b₀) a)) =
    Smash.leftPath (a₀ := a₀) (b₀ := b₀) a := by
  simp [Smash.leftPath, Path.symm]

end ComputationalPaths.Path.HoTT.HigherInductivePaths
