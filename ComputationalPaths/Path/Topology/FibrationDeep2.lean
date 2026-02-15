/-
# Deep Fibration Theory via Computational Paths

Serre fibrations, path lifting, fiber transport functoriality,
homotopy long exact sequence structures, pullback fibrations,
principal fibrations, sections and retractions — all formalized
with multi-step computational path reasoning.

## References
- Hatcher, "Algebraic Topology", Ch. 4
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Topology
namespace FibrationDeep2

open ComputationalPaths.Path

universe u v

/-! ## Core fibration infrastructure -/

structure Fibration where
  B : Type u
  E : Type u
  F : Type u
  proj : E → B
  lift : B → F → E
  proj_lift : ∀ b f, Path (proj (lift b f)) b
  section_ : B → E
  section_proj : ∀ b, Path (proj (section_ b)) b

/-! ## Fiber transport -/

def fiberTransport (fib : Fibration.{u}) {b₁ b₂ : fib.B}
    (p : Path b₁ b₂) (f : fib.F) : fib.F :=
  Path.transport (D := fun _ => fib.F) p f

/-! ## 1: Fiber transport over refl -/

def fiberTransport_refl (fib : Fibration.{u}) (b : fib.B) (f : fib.F) :
    Path (fiberTransport fib (Path.refl b) f) f := by
  unfold fiberTransport
  simp [Path.transport]
  exact Path.refl f

/-! ## 2: Fiber transport over trans -/

def fiberTransport_trans (fib : Fibration.{u}) {b₁ b₂ b₃ : fib.B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (f : fib.F) :
    Path (fiberTransport fib (Path.trans p q) f)
         (fiberTransport fib q (fiberTransport fib p f)) := by
  unfold fiberTransport
  exact Path.ofEq (Path.transport_trans (D := fun _ => fib.F) p q f)

/-! ## 3: Fiber transport over symm left -/

def fiberTransport_symm_left (fib : Fibration.{u}) {b₁ b₂ : fib.B}
    (p : Path b₁ b₂) (f : fib.F) :
    Path (fiberTransport fib (Path.symm p) (fiberTransport fib p f)) f := by
  unfold fiberTransport
  exact Path.ofEq (Path.transport_symm_left (D := fun _ => fib.F) p f)

/-! ## 4: Fiber transport over symm right -/

def fiberTransport_symm_right (fib : Fibration.{u}) {b₁ b₂ : fib.B}
    (p : Path b₁ b₂) (g : fib.F) :
    Path (fiberTransport fib p (fiberTransport fib (Path.symm p) g)) g := by
  unfold fiberTransport
  exact Path.ofEq (Path.transport_symm_right (D := fun _ => fib.F) p g)

/-! ## Path lifting structure -/

structure PathLifting (fib : Fibration.{u}) {b₁ b₂ : fib.B}
    (γ : Path b₁ b₂) (e₀ : fib.E) where
  endpoint : fib.E
  liftPath : Path e₀ endpoint
  over_start : Path (fib.proj e₀) b₁
  over_end : Path (fib.proj endpoint) b₂

structure SerreFibration extends Fibration.{u} where
  homotopyLifting : ∀ {b₁ b₂ : toFibration.B} (γ : Path b₁ b₂)
    (e₀ : toFibration.E) (over : Path (toFibration.proj e₀) b₁),
    PathLifting toFibration γ e₀

/-! ## 5: Lifting the identity path -/

def lift_refl_path (sfib : SerreFibration.{u}) (e₀ : sfib.E)
    (over : Path (sfib.proj e₀) (sfib.proj e₀)) :
    PathLifting sfib.toFibration (Path.refl (sfib.proj e₀)) e₀ :=
  sfib.homotopyLifting (Path.refl _) e₀ over

/-! ## 6: Lifting a composed path -/

def lift_trans_path (sfib : SerreFibration.{u})
    {b₁ b₂ b₃ : sfib.B}
    (γ₁ : Path b₁ b₂) (γ₂ : Path b₂ b₃)
    (e₀ : sfib.E) (over : Path (sfib.proj e₀) b₁) :
    PathLifting sfib.toFibration (Path.trans γ₁ γ₂) e₀ :=
  sfib.homotopyLifting (Path.trans γ₁ γ₂) e₀ over

/-! ## 7: Lift endpoint lies over target -/

def lift_trans_endpoint_over (sfib : SerreFibration.{u})
    {b₁ b₂ b₃ : sfib.B}
    (γ₁ : Path b₁ b₂) (γ₂ : Path b₂ b₃)
    (e₀ : sfib.E) (over : Path (sfib.proj e₀) b₁) :
    Path (sfib.proj (lift_trans_path sfib γ₁ γ₂ e₀ over).endpoint) b₃ :=
  (lift_trans_path sfib γ₁ γ₂ e₀ over).over_end

/-! ## Fibration morphisms -/

structure FibrationMorphism (fib₁ fib₂ : Fibration.{u}) where
  baseMap : fib₁.B → fib₂.B
  totalMap : fib₁.E → fib₂.E
  fiberMap : fib₁.F → fib₂.F
  proj_commutes : ∀ e, Path (fib₂.proj (totalMap e)) (baseMap (fib₁.proj e))
  section_commutes : ∀ b, Path (totalMap (fib₁.section_ b)) (fib₂.section_ (baseMap b))

/-! ## 8: Identity morphism -/

def fibMorphism_id (fib : Fibration.{u}) : FibrationMorphism fib fib where
  baseMap := id
  totalMap := id
  fiberMap := id
  proj_commutes := fun e => Path.refl _
  section_commutes := fun b => Path.refl _

/-! ## 9: Composition of morphisms -/

def fibMorphism_comp {fib₁ fib₂ fib₃ : Fibration.{u}}
    (φ : FibrationMorphism fib₁ fib₂) (ψ : FibrationMorphism fib₂ fib₃) :
    FibrationMorphism fib₁ fib₃ where
  baseMap := ψ.baseMap ∘ φ.baseMap
  totalMap := ψ.totalMap ∘ φ.totalMap
  fiberMap := ψ.fiberMap ∘ φ.fiberMap
  proj_commutes := fun e =>
    Path.trans (ψ.proj_commutes (φ.totalMap e))
              (Path.congrArg ψ.baseMap (φ.proj_commutes e))
  section_commutes := fun b =>
    Path.trans (Path.congrArg ψ.totalMap (φ.section_commutes b))
              (ψ.section_commutes (φ.baseMap b))

/-! ## 10: Comp projection coherence -/

def fibMorphism_comp_proj {fib₁ fib₂ fib₃ : Fibration.{u}}
    (φ : FibrationMorphism fib₁ fib₂) (ψ : FibrationMorphism fib₂ fib₃)
    (e : fib₁.E) :
    Path (fib₃.proj (ψ.totalMap (φ.totalMap e)))
         (ψ.baseMap (φ.baseMap (fib₁.proj e))) :=
  (fibMorphism_comp φ ψ).proj_commutes e

/-! ## 11: Left unit law -/

def fibMorphism_comp_id_left (fib₁ fib₂ : Fibration.{u})
    (φ : FibrationMorphism fib₁ fib₂) (e : fib₁.E) :
    Path (fib₂.proj ((fibMorphism_comp (fibMorphism_id fib₁) φ).totalMap e))
         (φ.baseMap (fib₁.proj e)) :=
  (fibMorphism_comp (fibMorphism_id fib₁) φ).proj_commutes e

/-! ## 12: Section commutes under composition -/

def fibMorphism_comp_section {fib₁ fib₂ fib₃ : Fibration.{u}}
    (φ : FibrationMorphism fib₁ fib₂) (ψ : FibrationMorphism fib₂ fib₃)
    (b : fib₁.B) :
    Path (ψ.totalMap (φ.totalMap (fib₁.section_ b)))
         (fib₃.section_ (ψ.baseMap (φ.baseMap b))) :=
  (fibMorphism_comp φ ψ).section_commutes b

/-! ## Pullback fibrations -/

structure PullbackFibration (fib : Fibration.{u}) (A : Type u) where
  pullMap : A → fib.B
  pullE : Type u
  pullProj : pullE → A
  pullLift : A → fib.F → pullE
  pullProj_pullLift : ∀ a f, Path (pullProj (pullLift a f)) a
  fiberPreserved : ∀ a f, Path (fib.proj (fib.lift (pullMap a) f)) (pullMap a)

/-! ## 13: Pullback fiber transport -/

def pullback_fiberTransport (fib : Fibration.{u}) (A : Type u)
    (pb : PullbackFibration fib A) {a₁ a₂ : A}
    (p : Path a₁ a₂) (f : fib.F) : fib.F :=
  fiberTransport fib (Path.congrArg pb.pullMap p) f

/-! ## 14: Pullback transport over refl -/

def pullback_transport_refl (fib : Fibration.{u}) (A : Type u)
    (pb : PullbackFibration fib A) (a : A) (f : fib.F) :
    Path (pullback_fiberTransport fib A pb (Path.refl a) f) f := by
  unfold pullback_fiberTransport fiberTransport
  simp [Path.congrArg, Path.transport]
  exact Path.refl f

/-! ## 15: Pullback transport over trans -/

def pullback_transport_trans (fib : Fibration.{u}) (A : Type u)
    (pb : PullbackFibration fib A) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (f : fib.F) :
    Path (pullback_fiberTransport fib A pb (Path.trans p q) f)
         (pullback_fiberTransport fib A pb q
           (pullback_fiberTransport fib A pb p f)) := by
  unfold pullback_fiberTransport fiberTransport
  have h1 : Path.congrArg pb.pullMap (Path.trans p q) =
             Path.trans (Path.congrArg pb.pullMap p) (Path.congrArg pb.pullMap q) :=
    Path.congrArg_trans pb.pullMap p q
  rw [h1]
  exact Path.ofEq (Path.transport_trans (D := fun _ => fib.F)
    (Path.congrArg pb.pullMap p) (Path.congrArg pb.pullMap q) f)

/-! ## Fiber sequences -/

structure FiberSequence where
  B : Type u
  E : Type u
  F : Type u
  incl : F → E
  proj : E → B
  connecting : B → F
  exact_at_E : ∀ f, Path (proj (incl f)) (proj (incl (connecting (proj (incl f)))))
  incl_connecting : ∀ b, Path (proj (incl (connecting b))) b

/-! ## 16: Fiber sequence exactness -/

def fiberSeq_exact (fs : FiberSequence.{u}) (f : fs.F) :
    Path (fs.proj (fs.incl f))
         (fs.proj (fs.incl (fs.connecting (fs.proj (fs.incl f))))) :=
  fs.exact_at_E f

/-! ## 17: Connecting map roundtrip -/

def connecting_roundtrip (fs : FiberSequence.{u}) (b : fs.B) :
    Path (fs.proj (fs.incl (fs.connecting b))) b :=
  fs.incl_connecting b

/-! ## 18: Connecting map via congrArg chain -/

def connecting_congrArg_chain (fs : FiberSequence.{u}) (b : fs.B) :
    Path (fs.connecting (fs.proj (fs.incl (fs.connecting b))))
         (fs.connecting b) :=
  Path.congrArg fs.connecting (fs.incl_connecting b)

/-! ## 19: Double connecting via exactness + connecting roundtrip -/

def double_connecting_path (fs : FiberSequence.{u}) (b : fs.B) :
    Path (fs.proj (fs.incl (fs.connecting (fs.proj (fs.incl (fs.connecting b))))))
         b :=
  Path.trans (fs.incl_connecting (fs.proj (fs.incl (fs.connecting b))))
             (fs.incl_connecting b)

/-! ## Long exact sequence data -/

structure LongExactData where
  B : Type u
  E : Type u
  F : Type u
  incl_n : (n : Nat) → F → E
  proj_n : (n : Nat) → E → B
  boundary : (n : Nat) → B → F
  exact_incl_proj : (n : Nat) → ∀ f,
    Path (proj_n n (incl_n n f)) (proj_n n (incl_n n (boundary n (proj_n n (incl_n n f)))))
  exact_proj_bound : (n : Nat) → ∀ e,
    Path (boundary n (proj_n n e)) (boundary n (proj_n n (incl_n n (boundary n (proj_n n e)))))

/-! ## 20: LES exactness at E -/

def les_exact_at_E (led : LongExactData.{u}) (n : Nat) (f : led.F) :
    Path (led.proj_n n (led.incl_n n f))
         (led.proj_n n (led.incl_n n (led.boundary n (led.proj_n n (led.incl_n n f))))) :=
  led.exact_incl_proj n f

/-! ## 21: LES exactness at B -/

def les_exact_at_B (led : LongExactData.{u}) (n : Nat) (e : led.E) :
    Path (led.boundary n (led.proj_n n e))
         (led.boundary n (led.proj_n n (led.incl_n n (led.boundary n (led.proj_n n e))))) :=
  led.exact_proj_bound n e

/-! ## 22: LES boundary via congrArg -/

def les_boundary_congrArg (led : LongExactData.{u}) (n : Nat) (f : led.F) :
    Path (led.boundary n (led.proj_n n (led.incl_n n f)))
         (led.boundary n (led.proj_n n (led.incl_n n (led.boundary n (led.proj_n n (led.incl_n n f)))))) :=
  Path.congrArg (led.boundary n) (led.exact_incl_proj n f)

/-! ## LES morphism -/

structure LESMorphism (led₁ led₂ : LongExactData.{u}) where
  mapF : led₁.F → led₂.F
  mapE : led₁.E → led₂.E
  mapB : led₁.B → led₂.B
  commutes_incl : (n : Nat) → ∀ f,
    Path (led₂.incl_n n (mapF f)) (mapE (led₁.incl_n n f))
  commutes_proj : (n : Nat) → ∀ e,
    Path (led₂.proj_n n (mapE e)) (mapB (led₁.proj_n n e))
  commutes_boundary : (n : Nat) → ∀ b,
    Path (led₂.boundary n (mapB b)) (mapF (led₁.boundary n b))

/-! ## 23: LES morphism inclusion naturality -/

def les_morphism_incl_nat (led₁ led₂ : LongExactData.{u})
    (m : LESMorphism led₁ led₂) (n : Nat) (f : led₁.F) :
    Path (led₂.incl_n n (m.mapF f)) (m.mapE (led₁.incl_n n f)) :=
  m.commutes_incl n f

/-! ## 24: LES morphism proj naturality -/

def les_morphism_proj_nat (led₁ led₂ : LongExactData.{u})
    (m : LESMorphism led₁ led₂) (n : Nat) (e : led₁.E) :
    Path (led₂.proj_n n (m.mapE e)) (m.mapB (led₁.proj_n n e)) :=
  m.commutes_proj n e

/-! ## 25: LES morphism boundary naturality -/

def les_morphism_boundary_nat (led₁ led₂ : LongExactData.{u})
    (m : LESMorphism led₁ led₂) (n : Nat) (b : led₁.B) :
    Path (led₂.boundary n (m.mapB b)) (m.mapF (led₁.boundary n b)) :=
  m.commutes_boundary n b

/-! ## 26: LES morphism proj-incl composition naturality -/

def les_morphism_proj_incl (led₁ led₂ : LongExactData.{u})
    (m : LESMorphism led₁ led₂) (n : Nat) (f : led₁.F) :
    Path (led₂.proj_n n (led₂.incl_n n (m.mapF f)))
         (m.mapB (led₁.proj_n n (led₁.incl_n n f))) :=
  let step1 : Path (led₂.proj_n n (led₂.incl_n n (m.mapF f)))
                   (led₂.proj_n n (m.mapE (led₁.incl_n n f))) :=
    Path.congrArg (led₂.proj_n n) (m.commutes_incl n f)
  let step2 : Path (led₂.proj_n n (m.mapE (led₁.incl_n n f)))
                   (m.mapB (led₁.proj_n n (led₁.incl_n n f))) :=
    m.commutes_proj n (led₁.incl_n n f)
  Path.trans step1 step2

/-! ## Sections and retractions -/

structure FibrationSection (fib : Fibration.{u}) where
  sec : fib.B → fib.E
  is_section : ∀ b, Path (fib.proj (sec b)) b

structure FibrationRetraction (fib : Fibration.{u}) where
  incl : fib.F → fib.E
  retr : fib.E → fib.F
  is_retraction : ∀ f, Path (retr (incl f)) f

/-! ## 27: Section proj is identity -/

def section_proj_id (fib : Fibration.{u}) (s : FibrationSection fib) (b : fib.B) :
    Path (fib.proj (s.sec b)) b :=
  s.is_section b

/-! ## 28: Retraction roundtrip -/

def retraction_roundtrip (fib : Fibration.{u}) (r : FibrationRetraction fib) (f : fib.F) :
    Path (r.retr (r.incl f)) f :=
  r.is_retraction f

/-! ## 29: Section transport coherence -/

def section_transport_coherence (fib : Fibration.{u}) (s : FibrationSection fib)
    {b₁ b₂ : fib.B} (p : Path b₁ b₂) :
    Path (fib.proj (Path.transport (D := fun _ => fib.E) p (s.sec b₁)))
         (fib.proj (s.sec b₂)) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]
    exact Path.refl _

/-! ## 30: Double section via trans -/

def section_double_proj (fib : Fibration.{u}) (s : FibrationSection fib)
    (b : fib.B) :
    Path (fib.proj (s.sec (fib.proj (s.sec b)))) b :=
  let step1 : Path (fib.proj (s.sec (fib.proj (s.sec b)))) (fib.proj (s.sec b)) :=
    Path.congrArg (fun x => fib.proj (s.sec x)) (s.is_section b)
  let step2 : Path (fib.proj (s.sec b)) b := s.is_section b
  Path.trans step1 step2

/-! ## 31: Triple section -/

def section_triple_proj (fib : Fibration.{u}) (s : FibrationSection fib) (b : fib.B) :
    Path (fib.proj (s.sec (fib.proj (s.sec (fib.proj (s.sec b)))))) b :=
  let step1 := Path.congrArg (fun x => fib.proj (s.sec (fib.proj (s.sec x)))) (s.is_section b)
  let step2 := section_double_proj fib s b
  Path.trans step1 step2

/-! ## Principal fibrations -/

structure PrincipalFibration extends Fibration.{u} where
  G : Type u
  action : G → E → E
  action_proj : ∀ g e, Path (proj (action g e)) (proj e)
  action_free : ∀ g₁ g₂ e, Path (action g₁ e) (action g₂ e) → Path g₁ g₂

/-! ## 32: Principal action preserves fibers -/

def principal_action_fiber (pfib : PrincipalFibration.{u}) (g : pfib.G) (e : pfib.E) :
    Path (pfib.proj (pfib.action g e)) (pfib.proj e) :=
  pfib.action_proj g e

/-! ## 33: Two-step action preservation -/

def principal_action_fiber_two (pfib : PrincipalFibration.{u})
    (g₁ g₂ : pfib.G) (e : pfib.E) :
    Path (pfib.proj (pfib.action g₁ (pfib.action g₂ e))) (pfib.proj e) :=
  Path.trans (pfib.action_proj g₁ (pfib.action g₂ e)) (pfib.action_proj g₂ e)

/-! ## 34: Free action injectivity -/

def principal_free_action (pfib : PrincipalFibration.{u})
    (g₁ g₂ : pfib.G) (e : pfib.E)
    (h : Path (pfib.action g₁ e) (pfib.action g₂ e)) :
    Path g₁ g₂ :=
  pfib.action_free g₁ g₂ e h

/-! ## Covering spaces -/

structure CoveringSpace extends Fibration.{u} where
  fiberDiscrete : ∀ (f₁ f₂ : F), Path f₁ f₂ → f₁ = f₂

/-! ## 35: Covering discreteness -/

def covering_fiber_discrete (cov : CoveringSpace.{u}) (f₁ f₂ : cov.F)
    (p : Path f₁ f₂) : f₁ = f₂ :=
  cov.fiberDiscrete f₁ f₂ p

/-! ## Hurewicz fibrations -/

structure HurewiczFibration extends Fibration.{u} where
  fullLifting : ∀ {b₁ b₂ : B} (γ : Path b₁ b₂) (e₀ : E)
    (over : Path (proj e₀) b₁),
    Σ' (e₁ : E), (Path e₀ e₁) × (Path (proj e₁) b₂)

/-! ## 36: Hurewicz lift endpoint -/

def hurewicz_lift_endpoint (hfib : HurewiczFibration.{u})
    {b₁ b₂ : hfib.B} (γ : Path b₁ b₂) (e₀ : hfib.E)
    (over : Path (hfib.proj e₀) b₁) :
    Path (hfib.proj (hfib.fullLifting γ e₀ over).1) b₂ :=
  (hfib.fullLifting γ e₀ over).2.2

/-! ## 37: Hurewicz to Serre -/

def hurewicz_to_serre (hfib : HurewiczFibration.{u}) : SerreFibration.{u} where
  toFibration := hfib.toFibration
  homotopyLifting := fun γ e₀ over =>
    let lifted := hfib.fullLifting γ e₀ over
    { endpoint := lifted.1
      liftPath := lifted.2.1
      over_start := over
      over_end := lifted.2.2 }

/-! ## Connection structure -/

structure FibrationConnection (fib : Fibration.{u}) where
  horizontalLift : {b₁ b₂ : fib.B} → Path b₁ b₂ → fib.E → fib.E
  lift_proj : ∀ {b₁ b₂ : fib.B} (γ : Path b₁ b₂) (e : fib.E),
    Path (fib.proj e) b₁ → Path (fib.proj (horizontalLift γ e)) b₂
  lift_refl : ∀ (e : fib.E),
    Path (horizontalLift (Path.refl (fib.proj e)) e) e

/-! ## 38: Connection lift over refl -/

def connection_lift_refl (fib : Fibration.{u}) (conn : FibrationConnection fib)
    (e : fib.E) :
    Path (conn.horizontalLift (Path.refl (fib.proj e)) e) e :=
  conn.lift_refl e

/-! ## 39: Connection lift projects correctly -/

def connection_lift_proj (fib : Fibration.{u}) (conn : FibrationConnection fib)
    {b₁ b₂ : fib.B} (γ : Path b₁ b₂) (e : fib.E) (over : Path (fib.proj e) b₁) :
    Path (fib.proj (conn.horizontalLift γ e)) b₂ :=
  conn.lift_proj γ e over

/-! ## 40: Morphism preserves section -/

def fibMorphism_preserves_section {fib₁ fib₂ : Fibration.{u}}
    (φ : FibrationMorphism fib₁ fib₂)
    (s : FibrationSection fib₁) (b : fib₁.B) :
    Path (fib₂.proj (φ.totalMap (s.sec b))) (φ.baseMap b) :=
  Path.trans (φ.proj_commutes (s.sec b))
             (Path.congrArg φ.baseMap (s.is_section b))

/-! ## 41: Morphism preserves retraction -/

def fibMorphism_preserves_retraction {fib₁ fib₂ : Fibration.{u}}
    (φ : FibrationMorphism fib₁ fib₂)
    (r : FibrationRetraction fib₁) (f : fib₁.F) :
    Path (φ.fiberMap (r.retr (r.incl f))) (φ.fiberMap f) :=
  Path.congrArg φ.fiberMap (r.is_retraction f)

/-! ## 42: Fiber sequence transport -/

def fiberSeq_transport (fs : FiberSequence.{u}) {b₁ b₂ : fs.B}
    (p : Path b₁ b₂) :
    Path (Path.transport (D := fun _ => fs.F) p (fs.connecting b₁))
         (fs.connecting b₂) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]
    exact Path.refl _

/-! ## 43: Fiber transport functoriality (three-step) -/

def fiberTransport_three_step (fib : Fibration.{u})
    {b₁ b₂ b₃ b₄ : fib.B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (r : Path b₃ b₄) (f : fib.F) :
    Path (fiberTransport fib (Path.trans (Path.trans p q) r) f)
         (fiberTransport fib r (fiberTransport fib q (fiberTransport fib p f))) :=
  let step1 := fiberTransport_trans fib (Path.trans p q) r f
  let step2 := Path.congrArg (fiberTransport fib r) (fiberTransport_trans fib p q f)
  Path.trans step1 step2

/-! ## 44: Fiber transport inverse roundtrip -/

def fiberTransport_inverse_roundtrip (fib : Fibration.{u})
    {b₁ b₂ : fib.B} (p : Path b₁ b₂) (f : fib.F) :
    Path (fiberTransport fib (Path.trans p (Path.symm p)) f) f :=
  let step1 := fiberTransport_trans fib p (Path.symm p) f
  let step2 := fiberTransport_symm_left fib p f
  Path.trans step1 step2

/-! ## 45: LES morphism boundary-incl composition -/

def les_morphism_boundary_incl (led₁ led₂ : LongExactData.{u})
    (m : LESMorphism led₁ led₂) (n : Nat) (b : led₁.B) :
    Path (led₂.incl_n n (led₂.boundary n (m.mapB b)))
         (m.mapE (led₁.incl_n n (led₁.boundary n b))) :=
  let step1 : Path (led₂.incl_n n (led₂.boundary n (m.mapB b)))
                   (led₂.incl_n n (m.mapF (led₁.boundary n b))) :=
    Path.congrArg (led₂.incl_n n) (m.commutes_boundary n b)
  let step2 : Path (led₂.incl_n n (m.mapF (led₁.boundary n b)))
                   (m.mapE (led₁.incl_n n (led₁.boundary n b))) :=
    m.commutes_incl n (led₁.boundary n b)
  Path.trans step1 step2

end FibrationDeep2
end Topology
end Path
end ComputationalPaths
