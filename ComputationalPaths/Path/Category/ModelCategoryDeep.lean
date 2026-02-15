/-
# Model Category Theory — Deep Computational Paths

Every theorem uses Path.trans, Path.symm, Path.congrArg, Path.transport,
or multi-step equational/calc chains. Zero sorries.
-/

import ComputationalPaths.Path.Basic.Core

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Category.ModelCategoryDeep

open ComputationalPaths.Path

universe u v

variable {A : Type u}

/-! §1 PATH ENDOFUNCTORS -/

structure PEF (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ a, map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

-- 1
theorem pef_map_trans3 (F : PEF A) {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    F.map (Path.trans p (Path.trans q r)) =
    Path.trans (F.map p) (Path.trans (F.map q) (F.map r)) := by
  rw [F.map_trans, F.map_trans]

-- 2
theorem pef_map_trans4 (F : PEF A) {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    F.map (Path.trans p (Path.trans q (Path.trans r s))) =
    Path.trans (F.map p) (Path.trans (F.map q) (Path.trans (F.map r) (F.map s))) := by
  rw [F.map_trans, F.map_trans, F.map_trans]

-- 3
theorem pef_map_assoc4 (F : PEF A) {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    F.map (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (F.map p) (Path.trans (F.map q) (Path.trans (F.map r) (F.map s))) := by
  calc F.map (Path.trans (Path.trans (Path.trans p q) r) s)
      = F.map (Path.trans p (Path.trans q (Path.trans r s))) := by
          rw [Path.trans_assoc, Path.trans_assoc]
    _ = Path.trans (F.map p) (Path.trans (F.map q) (Path.trans (F.map r) (F.map s))) :=
          pef_map_trans4 F p q r s

-- 4
theorem pef_compose_trans (F G : PEF A) {a b c : A}
    (p : Path a b) (q : Path b c) :
    F.map (G.map (Path.trans p q)) =
    Path.trans (F.map (G.map p)) (F.map (G.map q)) := by
  rw [G.map_trans, F.map_trans]

-- 5
theorem pef_self_compose_refl (F : PEF A) (a : A) :
    F.map (F.map (Path.refl a)) = Path.refl (F.obj (F.obj a)) := by
  rw [F.map_refl, F.map_refl]

/-! §2 FACTORISATION -/

structure Factorisation {a b : A} (p : Path a b) where
  mid : A
  left_leg : Path a mid
  right_leg : Path mid b
  compose_eq : Path.trans left_leg right_leg = p

-- 6
theorem factorisation_transport {a b : A} {p : Path a b}
    (f : Factorisation p) {D : A → Sort v} (x : D a) :
    Path.transport (D := D) p x =
    Path.transport (D := D) f.right_leg (Path.transport (D := D) f.left_leg x) := by
  calc Path.transport (D := D) p x
      = Path.transport (D := D) (Path.trans f.left_leg f.right_leg) x := by
          rw [f.compose_eq]
    _ = Path.transport (D := D) f.right_leg (Path.transport (D := D) f.left_leg x) :=
          Path.transport_trans f.left_leg f.right_leg x

-- 7
theorem factorisation_symm {a b : A} {p : Path a b} (f : Factorisation p) :
    Path.symm p = Path.trans (Path.symm f.right_leg) (Path.symm f.left_leg) := by
  calc Path.symm p
      = Path.symm (Path.trans f.left_leg f.right_leg) := by rw [f.compose_eq]
    _ = Path.trans (Path.symm f.right_leg) (Path.symm f.left_leg) := by simp

-- 8
theorem factorisation_congrArg {a b : A} {p : Path a b}
    (f : Factorisation p) (g : A → A) :
    Path.congrArg g p =
    Path.trans (Path.congrArg g f.left_leg) (Path.congrArg g f.right_leg) := by
  calc Path.congrArg g p
      = Path.congrArg g (Path.trans f.left_leg f.right_leg) := by rw [f.compose_eq]
    _ = Path.trans (Path.congrArg g f.left_leg) (Path.congrArg g f.right_leg) :=
          Path.congrArg_trans g f.left_leg f.right_leg

/-! §3 CYLINDER AND PATH OBJECTS -/

structure CylinderObj (a : A) where
  cyl : A
  i₀ : Path a cyl
  i₁ : Path a cyl
  σ  : Path cyl a
  retract₀ : Path.trans i₀ σ = Path.refl a
  retract₁ : Path.trans i₁ σ = Path.refl a

structure PathObj (a : A) where
  pa : A
  ev₀ : Path pa a
  ev₁ : Path pa a
  s   : Path a pa
  section₀ : Path.trans s ev₀ = Path.refl a
  section₁ : Path.trans s ev₁ = Path.refl a

-- 9
theorem cylinder_double_fold (C : CylinderObj a) :
    Path.trans (Path.trans C.i₀ C.σ) (Path.trans C.i₁ C.σ) = Path.refl a := by
  calc Path.trans (Path.trans C.i₀ C.σ) (Path.trans C.i₁ C.σ)
      = Path.trans (Path.refl a) (Path.trans C.i₁ C.σ) := by rw [C.retract₀]
    _ = Path.trans C.i₁ C.σ := by simp
    _ = Path.refl a := C.retract₁

-- 10
theorem cylinder_fold_then_i₁ (C : CylinderObj a) :
    Path.trans (Path.trans C.i₀ C.σ) C.i₁ = C.i₁ := by
  rw [C.retract₀]; simp

-- 11
theorem cylinder_fold_then_i₀ (C : CylinderObj a) :
    Path.trans (Path.trans C.i₁ C.σ) C.i₀ = C.i₀ := by
  rw [C.retract₁]; simp

-- 12
theorem pathobj_double_section (P : PathObj a) :
    Path.trans (Path.trans P.s P.ev₀) (Path.trans P.s P.ev₁) = Path.refl a := by
  calc Path.trans (Path.trans P.s P.ev₀) (Path.trans P.s P.ev₁)
      = Path.trans (Path.refl a) (Path.trans P.s P.ev₁) := by rw [P.section₀]
    _ = Path.trans P.s P.ev₁ := by simp
    _ = Path.refl a := P.section₁

-- 13
theorem pathobj_fold_then_s (P : PathObj a) :
    Path.trans (Path.trans P.s P.ev₀) P.s = P.s := by
  rw [P.section₀]; simp

-- 14
theorem cylinder_triple_fold (C : CylinderObj a) :
    Path.trans (Path.trans (Path.trans C.i₀ C.σ) C.i₁) C.σ = Path.refl a := by
  rw [cylinder_fold_then_i₁]; exact C.retract₁

/-! §4 LEFT AND RIGHT HOMOTOPY -/

structure LeftHtpy {a b : A} (f g : Path a b) where
  cyl : CylinderObj a
  H : Path cyl.cyl b
  on_i₀ : Path.trans cyl.i₀ H = f
  on_i₁ : Path.trans cyl.i₁ H = g

structure RightHtpy {a b : A} (f g : Path a b) where
  po : PathObj b
  H : Path a po.pa
  on_ev₀ : Path.trans H po.ev₀ = f
  on_ev₁ : Path.trans H po.ev₁ = g

-- 15
def LeftHtpy.rfl (C : CylinderObj a) (f : Path a b) : LeftHtpy f f where
  cyl := C
  H := Path.trans C.σ f
  on_i₀ := by
    calc Path.trans C.i₀ (Path.trans C.σ f)
        = Path.trans (Path.trans C.i₀ C.σ) f := (Path.trans_assoc _ _ _).symm
      _ = Path.trans (Path.refl a) f := by rw [C.retract₀]
      _ = f := by simp
  on_i₁ := by
    calc Path.trans C.i₁ (Path.trans C.σ f)
        = Path.trans (Path.trans C.i₁ C.σ) f := (Path.trans_assoc _ _ _).symm
      _ = Path.trans (Path.refl a) f := by rw [C.retract₁]
      _ = f := by simp

-- 16
def LeftHtpy.symm' {f g : Path a b} (h : LeftHtpy f g) : LeftHtpy g f where
  cyl := { cyl := h.cyl.cyl, i₀ := h.cyl.i₁, i₁ := h.cyl.i₀, σ := h.cyl.σ,
            retract₀ := h.cyl.retract₁, retract₁ := h.cyl.retract₀ }
  H := h.H
  on_i₀ := h.on_i₁
  on_i₁ := h.on_i₀

-- 17
def RightHtpy.rfl (P : PathObj b) (f : Path a b) : RightHtpy f f where
  po := P
  H := Path.trans f P.s
  on_ev₀ := by
    calc Path.trans (Path.trans f P.s) P.ev₀
        = Path.trans f (Path.trans P.s P.ev₀) := by simp
      _ = Path.trans f (Path.refl b) := by rw [P.section₀]
      _ = f := by simp
  on_ev₁ := by
    calc Path.trans (Path.trans f P.s) P.ev₁
        = Path.trans f (Path.trans P.s P.ev₁) := by simp
      _ = Path.trans f (Path.refl b) := by rw [P.section₁]
      _ = f := by simp

-- 18
def LeftHtpy.postcomp {f g : Path a b} (h : LeftHtpy f g)
    (q : Path b c) : LeftHtpy (Path.trans f q) (Path.trans g q) where
  cyl := h.cyl
  H := Path.trans h.H q
  on_i₀ := by
    calc Path.trans h.cyl.i₀ (Path.trans h.H q)
        = Path.trans (Path.trans h.cyl.i₀ h.H) q := (Path.trans_assoc _ _ _).symm
      _ = Path.trans f q := by rw [h.on_i₀]
  on_i₁ := by
    calc Path.trans h.cyl.i₁ (Path.trans h.H q)
        = Path.trans (Path.trans h.cyl.i₁ h.H) q := (Path.trans_assoc _ _ _).symm
      _ = Path.trans g q := by rw [h.on_i₁]

-- 19
def RightHtpy.precomp (p : Path c a) {f g : Path a b}
    (h : RightHtpy f g) : RightHtpy (Path.trans p f) (Path.trans p g) where
  po := h.po
  H := Path.trans p h.H
  on_ev₀ := by
    calc Path.trans (Path.trans p h.H) h.po.ev₀
        = Path.trans p (Path.trans h.H h.po.ev₀) := by simp
      _ = Path.trans p f := by rw [h.on_ev₀]
  on_ev₁ := by
    calc Path.trans (Path.trans p h.H) h.po.ev₁
        = Path.trans p (Path.trans h.H h.po.ev₁) := by simp
      _ = Path.trans p g := by rw [h.on_ev₁]

/-! §5 HOMOTOPY CATEGORY -/

structure HoMor (a b : A) where
  repr : Path a b

def HoMor.comp {a b c : A} (f : HoMor a b) (g : HoMor b c) : HoMor a c :=
  ⟨Path.trans f.repr g.repr⟩
def HoMor.id' (a : A) : HoMor a a := ⟨Path.refl a⟩

-- 20
theorem hoMor_id_comp {a b : A} (f : HoMor a b) :
    HoMor.comp (HoMor.id' a) f = f := by simp [HoMor.comp, HoMor.id']
-- 21
theorem hoMor_comp_id {a b : A} (f : HoMor a b) :
    HoMor.comp f (HoMor.id' b) = f := by simp [HoMor.comp, HoMor.id']
-- 22
theorem hoMor_assoc {a b c d : A}
    (f : HoMor a b) (g : HoMor b c) (h : HoMor c d) :
    HoMor.comp (HoMor.comp f g) h = HoMor.comp f (HoMor.comp g h) := by
  simp [HoMor.comp]
-- 23
theorem hoMor_assoc4 {a b c d e : A}
    (f : HoMor a b) (g : HoMor b c) (h : HoMor c d) (k : HoMor d e) :
    HoMor.comp (HoMor.comp (HoMor.comp f g) h) k =
    HoMor.comp f (HoMor.comp g (HoMor.comp h k)) := by
  calc HoMor.comp (HoMor.comp (HoMor.comp f g) h) k
      = HoMor.comp (HoMor.comp f g) (HoMor.comp h k) := hoMor_assoc _ _ _
    _ = HoMor.comp f (HoMor.comp g (HoMor.comp h k)) := hoMor_assoc _ _ _

/-! §6 HOMOTOPY EQUIVALENCE (WHITEHEAD) -/

structure HtpyEquiv (a b : A) where
  fwd : Path a b
  bwd : Path b a
  left_inv  : Path.trans fwd bwd = Path.refl a
  right_inv : Path.trans bwd fwd = Path.refl b

-- 24
def HtpyEquiv.compose {a b c : A}
    (e₁ : HtpyEquiv a b) (e₂ : HtpyEquiv b c) : HtpyEquiv a c where
  fwd := Path.trans e₁.fwd e₂.fwd
  bwd := Path.trans e₂.bwd e₁.bwd
  left_inv := by
    calc Path.trans (Path.trans e₁.fwd e₂.fwd) (Path.trans e₂.bwd e₁.bwd)
        = Path.trans e₁.fwd (Path.trans (Path.trans e₂.fwd e₂.bwd) e₁.bwd) := by
            rw [Path.trans_assoc, Path.trans_assoc, ← Path.trans_assoc e₂.fwd]
      _ = Path.trans e₁.fwd (Path.trans (Path.refl b) e₁.bwd) := by rw [e₂.left_inv]
      _ = Path.trans e₁.fwd e₁.bwd := by simp
      _ = Path.refl a := e₁.left_inv
  right_inv := by
    calc Path.trans (Path.trans e₂.bwd e₁.bwd) (Path.trans e₁.fwd e₂.fwd)
        = Path.trans e₂.bwd (Path.trans (Path.trans e₁.bwd e₁.fwd) e₂.fwd) := by
            rw [Path.trans_assoc, Path.trans_assoc, ← Path.trans_assoc e₁.bwd]
      _ = Path.trans e₂.bwd (Path.trans (Path.refl b) e₂.fwd) := by rw [e₁.right_inv]
      _ = Path.trans e₂.bwd e₂.fwd := by simp
      _ = Path.refl c := e₂.right_inv

-- 25
def HtpyEquiv.inv {a b : A} (e : HtpyEquiv a b) : HtpyEquiv b a where
  fwd := e.bwd; bwd := e.fwd; left_inv := e.right_inv; right_inv := e.left_inv

-- 26
theorem htpyEquiv_transport_roundtrip {a b : A} (e : HtpyEquiv a b)
    {D : A → Sort v} (x : D a) :
    Path.transport (D := D) e.bwd (Path.transport (D := D) e.fwd x) = x := by
  simp only [← Path.transport_trans, e.left_inv, Path.transport_refl]

-- 27
theorem htpyEquiv_compose_assoc_fwd {a b c d : A}
    (e₁ : HtpyEquiv a b) (e₂ : HtpyEquiv b c) (e₃ : HtpyEquiv c d) :
    (HtpyEquiv.compose (HtpyEquiv.compose e₁ e₂) e₃).fwd =
    (HtpyEquiv.compose e₁ (HtpyEquiv.compose e₂ e₃)).fwd := by
  show Path.trans (Path.trans e₁.fwd e₂.fwd) e₃.fwd =
       Path.trans e₁.fwd (Path.trans e₂.fwd e₃.fwd)
  simp

/-! §7 QUILLEN ADJUNCTION -/

structure QuillenAdj (A : Type u) where
  L : PEF A
  R : PEF A
  η : ∀ a, Path a (R.obj (L.obj a))
  ε : ∀ a, Path (L.obj (R.obj a)) a
  tri_L : ∀ a, Path.trans (L.map (η a)) (ε (L.obj a)) = Path.refl (L.obj a)
  tri_R : ∀ a, Path.trans (η (R.obj a)) (R.map (ε a)) = Path.refl (R.obj a)

-- 28
theorem quillen_tri_L_postcomp (Q : QuillenAdj A) (a : A)
    (p : Path (Q.L.obj a) (Q.L.obj a)) :
    Path.trans (Path.trans (Q.L.map (Q.η a)) (Q.ε (Q.L.obj a))) p = p := by
  rw [Q.tri_L]; simp
-- 29
theorem quillen_tri_R_precomp (Q : QuillenAdj A) (a : A)
    (p : Path (Q.R.obj a) (Q.R.obj a)) :
    Path.trans (Path.trans (Q.η (Q.R.obj a)) (Q.R.map (Q.ε a))) p = p := by
  rw [Q.tri_R]; simp
-- 30
theorem quillen_double_tri_L (Q : QuillenAdj A) (a : A) :
    Path.trans (Path.trans (Q.L.map (Q.η a)) (Q.ε (Q.L.obj a)))
               (Path.trans (Q.L.map (Q.η a)) (Q.ε (Q.L.obj a)))
    = Path.refl (Q.L.obj a) := by
  rw [Q.tri_L]; simp

/-! §8 RETRACT ARGUMENTS -/

structure RetractData (a b : A) where
  sec : Path a b
  ret : Path b a
  id_eq : Path.trans sec ret = Path.refl a

-- 31
theorem retract_transport {D : A → Sort v}
    (r : RetractData a b) (x : D a) :
    Path.transport (D := D) r.ret (Path.transport (D := D) r.sec x) = x := by
  simp only [← Path.transport_trans, r.id_eq, Path.transport_refl]
-- 32
theorem retract_double_fold (r : RetractData a b) :
    Path.trans (Path.trans r.sec r.ret) (Path.trans r.sec r.ret) = Path.refl a := by
  rw [r.id_eq]; simp
-- 33
theorem retract_sec_ret_sec (r : RetractData a b) :
    Path.trans (Path.trans r.sec r.ret) r.sec = r.sec := by
  rw [r.id_eq]; simp
-- 34
theorem retract_congrArg (r : RetractData a b) (f : A → A) :
    Path.trans (Path.congrArg f r.sec) (Path.congrArg f r.ret) =
    Path.congrArg f (Path.refl a) := by
  rw [← Path.congrArg_trans, r.id_eq]

/-! §9 congrArg COHERENCE -/

-- 35
theorem mc_congrArg_trans (f : A → A) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q
-- 36
theorem mc_congrArg_symm (f : A → A) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p
-- 37
theorem mc_congrArg_comp (f g : A → A) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p
-- 38
theorem mc_congrArg_id {a b : A} (p : Path a b) :
    Path.congrArg (fun x => x) p = p := Path.congrArg_id p
-- 39
theorem mc_congrArg_trans3 (f : A → A) {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (Path.trans p (Path.trans q r)) =
    Path.trans (Path.congrArg f p) (Path.trans (Path.congrArg f q) (Path.congrArg f r)) := by
  rw [Path.congrArg_trans, Path.congrArg_trans]

/-! §10 HOMOTOPY PUSHOUT / PULLBACK -/

structure HoPushout {a b c : A} (f : Path a b) (g : Path a c) where
  po : A
  inl : Path b po
  inr : Path c po
  glue : Path.trans f inl = Path.trans g inr

-- 40
theorem hoPushout_glue_post {a b c : A} {f : Path a b} {g : Path a c}
    (hp : HoPushout f g) {d : A} (q : Path hp.po d) :
    Path.trans f (Path.trans hp.inl q) =
    Path.trans g (Path.trans hp.inr q) := by
  calc Path.trans f (Path.trans hp.inl q)
      = Path.trans (Path.trans f hp.inl) q := (Path.trans_assoc _ _ _).symm
    _ = Path.trans (Path.trans g hp.inr) q := by rw [hp.glue]
    _ = Path.trans g (Path.trans hp.inr q) := Path.trans_assoc _ _ _

structure HoPullback {a b c : A} (f : Path a c) (g : Path b c) where
  pb : A
  π₁ : Path pb a
  π₂ : Path pb b
  glue : Path.trans π₁ f = Path.trans π₂ g

-- 41
theorem hoPullback_glue_pre {a b c : A} {f : Path a c} {g : Path b c}
    (hp : HoPullback f g) {d : A} (p : Path d hp.pb) :
    Path.trans p (Path.trans hp.π₁ f) =
    Path.trans p (Path.trans hp.π₂ g) := by
  rw [hp.glue]
-- 42
theorem hoPushout_symm_glue {a b c : A} {f : Path a b} {g : Path a c}
    (hp : HoPushout f g) :
    Path.symm (Path.trans f hp.inl) = Path.symm (Path.trans g hp.inr) := by
  rw [hp.glue]

/-! §11 TRANSPORT COHERENCE -/

-- 43
theorem transport_trans_split {D : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (D := D) (Path.trans p q) x =
    Path.transport (D := D) q (Path.transport (D := D) p x) :=
  Path.transport_trans p q x

-- 44
theorem transport_const_family {D : Type v} {a b : A}
    (p : Path a b) (x : D) :
    Path.transport (D := fun _ => D) p x = x :=
  Path.transport_const p x

-- 45
theorem transport_symm_cancel {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    Path.transport (D := D) (Path.symm p) (Path.transport (D := D) p x) = x :=
  Path.transport_symm_left p x

end ComputationalPaths.Path.Category.ModelCategoryDeep
