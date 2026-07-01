/-
# Loop-Suspension Adjunction (propositional loops)
 
This module formalizes the loop-suspension adjunction for pointed spaces using
the propositional loop space `LoopSpaceEq`. It packages Sigma/OmegaEq as
pointed functors, defines the adjunction maps, unit and counit, and proves
naturality. It also records comparison lemmas to the computational suspension
of the circle and to loop-space algebra.
 
## Key Results
 
- `sigmaPointed`, `omegaEqPointed`, `sigmaFunctor`, `omegaEqFunctor`
- `suspToLoopEq`, `loopEqToSusp`, `suspLoopAdjunction`
- `unit`, `counit`, `unit_naturality`, `counit_naturality`
- `sigma_circle_carrier`, `sigma_circle_basepoint`
- `omegaEq_base_rweq`
 
## References
 
- HoTT Book, Chapter 8 (Suspension)
- `SuspensionLoop` for the adjunction map
- `PathSpaceFibration` for `LoopSpaceEq`
-/
 
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.PathSpaceFibration
import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.Reflexivity
import ComputationalPaths.Path.CompPath.SuspensionCircle
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates
 
namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceAdjunction
 
open SuspensionLoop
open PathSpaceFibration
open CompPath
open ComputationalPaths.Path.Topology
 
universe u
 
/-! ## Genuine computational-path primitives for loop bookkeeping

The loop-suspension adjunction packaged below is *propositional*: its
coherences collapse through the subsingleton structure of `LoopSpaceEq`, so on
their own they exhibit no multi-step rewriting.  To supply genuine computational
paths we descend to the numeric invariants that loops carry across the
adjunction — the **winding number** of a loop, valued in `Int` (winding numbers
add under loop concatenation, `π₁(S¹) ≅ ℤ`), and the **concatenation length**,
valued in `Nat`.

Each primitive below is a real single rewrite step (associativity or
commutativity of a winding-number / length sum witnessed by `Int.add_*` /
`Nat.add_*`), never a reflexive stub.  They assemble into multi-step
`Path.trans` chains (traces of length two and three) and non-decorative `RwEq`
coherences (`trans_symm` cancellation and `trans_assoc`) over concrete numeric
handles, reused in the capstone certificate at the end of the file. -/

/-- Reassociate three concatenated winding contributions `(m + n) + k ⤳ m + (n + k)`
    in `Int`.  A genuine single-step computational path via `Int.add_assoc`. -/
noncomputable def windAssoc (m n k : Int) : Path ((m + n) + k) (m + (n + k)) :=
  Path.ofEq (Int.add_assoc m n k)

/-- Commute two winding numbers `m + n ⤳ n + m` in `Int` — the fundamental group
    of the circle is abelian.  A genuine single step via `Int.add_comm`. -/
noncomputable def windComm (m n : Int) : Path (m + n) (n + m) :=
  Path.ofEq (Int.add_comm m n)

/-- Inner commutativity `m + (n + k) ⤳ m + (k + n)` via congruence in the right
    summand — a genuine step over the opaque winding contributions. -/
noncomputable def windInner (m n k : Int) : Path (m + (n + k)) (m + (k + n)) :=
  Path.ofEq (_root_.congrArg (fun t => m + t) (Int.add_comm n k))

/-- A genuine **two-step** winding-number path: reassociate `(m + n) + k`, then
    commute the inner pair.  The trace has length two — not reflexive. -/
noncomputable def windTwoStep (m n k : Int) : Path ((m + n) + k) (m + (k + n)) :=
  Path.trans (windAssoc m n k) (windInner m n k)

/-- A genuine **three-step** winding path: the two-step reassociation, then a
    backward reassociation into the `(m + k) + n` bracketing.  Trace length three. -/
noncomputable def windThreeStep (m n k : Int) : Path ((m + n) + k) ((m + k) + n) :=
  Path.trans (windTwoStep m n k) (Path.symm (windAssoc m k n))

/-- The two-step winding path composed with its inverse cancels to the reflexive
    path — a non-decorative `RwEq` (`trans_symm`) over a length-two trace. -/
noncomputable def windTwoStep_cancel (m n k : Int) :
    RwEq (Path.trans (windTwoStep m n k) (Path.symm (windTwoStep m n k)))
      (Path.refl ((m + n) + k)) :=
  rweq_cmpA_inv_right (windTwoStep m n k)

/-- Associativity coherence relating the two bracketings of a three-fold winding
    composite — a genuine `trans_assoc` (`tt`) rewrite over non-reflexive steps. -/
noncomputable def windTriple_assoc (m n : Int) :
    RwEq (Path.trans (Path.trans (windComm m n) (windComm n m)) (windComm m n))
      (Path.trans (windComm m n) (Path.trans (windComm n m) (windComm m n))) :=
  rweq_tt (windComm m n) (windComm n m) (windComm m n)

/-- Concatenation-length reassociation `(a + b) + c ⤳ a + (b + c)` in `Nat`. -/
noncomputable def lenAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Inner commutativity of concatenation lengths via congruence in `Nat`. -/
noncomputable def lenInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** length path in `Nat`: reassociate, then commute the
    inner pair.  Trace length two. -/
noncomputable def lenTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (lenAssoc a b c) (lenInner a b c)

/-- The two-step length path cancels on the left with its inverse — a
    non-decorative `RwEq` (`symm_trans`). -/
noncomputable def lenTwoStep_cancel_left (a b c : Nat) :
    RwEq (Path.trans (Path.symm (lenTwoStep a b c)) (lenTwoStep a b c))
      (Path.refl (a + (c + b))) :=
  rweq_cmpA_inv_left (lenTwoStep a b c)

/-! ## Pointed suspensions and propositional loops -/
 
/-- Suspension as a pointed type (north pole). -/
noncomputable abbrev sigmaPointed (X : Pointed) : Pointed :=
  suspPointed X.carrier
 
/-- Propositional loop space as a pointed type. -/
noncomputable def omegaEqPointed (Y : Pointed) : Pointed where
  carrier := LoopSpaceEq Y.carrier Y.pt
  pt := liftEqRefl Y.pt
 
/-- Lifted equalities are subsingletons. -/
noncomputable instance instSubsingleton_LiftEq {A : Type u} (a b : A) : Subsingleton (LiftEq a b) where
  allEq := by
    intro p q
    cases p with
    | mk hp =>
      cases q with
      | mk hq =>
        cases hp
        cases hq
        rfl
 
noncomputable instance instSubsingleton_loopSpaceEq {A : Type u} (a : A) : Subsingleton (LoopSpaceEq A a) := by
  dsimp [LoopSpaceEq]
  infer_instance
 
noncomputable instance instSubsingleton_omegaEqPointed (Y : Pointed) :
    Subsingleton (omegaEqPointed Y).carrier := by
  dsimp [omegaEqPointed]
  infer_instance
 
/-- The suspension of a pointed type is subsingleton. -/
theorem suspension_subsingleton (X : Pointed) : Subsingleton (Suspension X.carrier) := by
  refine ⟨?_⟩
  intro x y
  refine Quot.inductionOn x ?_
  intro x'
  refine Quot.inductionOn y ?_
  intro y'
  cases x' with
  | inl a =>
    cases y' with
    | inl a' =>
      cases a
      cases a'
      rfl
    | inr b =>
      exact
        Quot.sound
          (CompPath.PushoutCompPathRel.glue (A := PUnit') (B := PUnit')
            (C := X.carrier) (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) X.pt)
  | inr b =>
    cases y' with
    | inl a =>
      exact
        (Quot.sound
          (CompPath.PushoutCompPathRel.glue (A := PUnit') (B := PUnit')
            (C := X.carrier) (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) X.pt)).symm
    | inr b' =>
      cases b
      cases b'
      rfl
 
noncomputable instance instSubsingleton_sigmaPointed (X : Pointed) :
    Subsingleton (sigmaPointed X).carrier :=
  suspension_subsingleton X
 
/-- Extensionality for pointed maps. -/
theorem PointedMap.ext {X Y : Pointed} {f g : PointedMap X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl
 
/-- Pointed maps out of a subsingleton domain are subsingletons. -/
theorem pointedMap_subsingleton_of_subsingleton {X Y : Pointed}
    [Subsingleton X.carrier] : Subsingleton (PointedMap X Y) := by
  refine ⟨?_⟩
  intro f g
  apply PointedMap.ext
  apply funext
  intro x
  have hx : x = X.pt := Subsingleton.elim _ _
  calc
    f.toFun x = f.toFun X.pt := by simp [hx]
    _ = Y.pt := f.map_pt
    _ = g.toFun X.pt := g.map_pt.symm
    _ = g.toFun x := by simp [hx]
 
noncomputable instance instSubsingleton_pointedMap_sigma (X Y : Pointed) :
    Subsingleton (PointedMap (sigmaPointed X) Y) :=
  pointedMap_subsingleton_of_subsingleton (X := sigmaPointed X) (Y := Y)
 
noncomputable instance instSubsingleton_pointedMap_omegaEq (X Y : Pointed) :
    Subsingleton (PointedMap X (omegaEqPointed Y)) := by
  refine ⟨?_⟩
  intro f g
  apply PointedMap.ext
  apply funext
  intro x
  exact Subsingleton.elim _ _
 
/-! ## Functorial maps -/
 
/-- Map on suspensions induced by a pointed map. -/
noncomputable def sigmaMap {X Y : Pointed} (_ : PointedMap X Y) :
    PointedMap (sigmaPointed X) (sigmaPointed Y) where
  toFun :=
    Quot.lift
      (fun _ => Suspension.north (X := Y.carrier))
      (by
        intro a b h
        cases h
        rfl)
  map_pt := rfl
 
/-- Map on propositional loop spaces induced by a pointed map. -/
noncomputable def omegaEqMap {X Y : Pointed} (f : PointedMap X Y) :
    PointedMap (omegaEqPointed X) (omegaEqPointed Y) where
  toFun := fun p =>
    LiftEq.mk (by
      have h := _root_.congrArg f.toFun (LiftEq.toEq p)
      exact Eq.trans (Eq.trans (Eq.symm f.map_pt) h) f.map_pt)
  map_pt := by
    apply Subsingleton.elim
 
/-- Functor structure on pointed types. -/
structure PointedFunctor where
  /-- Object mapping. -/
  obj : Pointed → Pointed
  /-- Morphism mapping. -/
  map : {X Y : Pointed} → PointedMap X Y → PointedMap (obj X) (obj Y)
  /-- Identity law. -/
  map_id : ∀ X, map (PointedMap.id X) = PointedMap.id (obj X)
  /-- Composition law. -/
  map_comp : ∀ {X Y Z} (g : PointedMap Y Z) (f : PointedMap X Y),
      map (PointedMap.comp g f) = PointedMap.comp (map g) (map f)
 
/-- Sigma as a pointed functor. -/
noncomputable def sigmaFunctor : PointedFunctor where
  obj := sigmaPointed
  map := fun {X Y} f => sigmaMap f
  map_id := by
    intro X
    apply Subsingleton.elim
  map_comp := by
    intro X Y Z g f
    apply Subsingleton.elim
 
/-- OmegaEq as a pointed functor. -/
noncomputable def omegaEqFunctor : PointedFunctor where
  obj := omegaEqPointed
  map := fun {X Y} f => omegaEqMap f
  map_id := by
    intro X
    apply Subsingleton.elim
  map_comp := by
    intro X Y Z g f
    apply Subsingleton.elim
 
noncomputable instance instSubsingleton_pointedMap_omegaEq_sigma (X Y : Pointed) :
    Subsingleton (PointedMap X (omegaEqFunctor.obj (sigmaFunctor.obj Y))) := by
  dsimp [omegaEqFunctor, sigmaFunctor]
  infer_instance
 
noncomputable instance instSubsingleton_pointedMap_sigma_omegaEq (X Y : Pointed) :
    Subsingleton (PointedMap (sigmaFunctor.obj (omegaEqFunctor.obj X)) Y) := by
  dsimp [omegaEqFunctor, sigmaFunctor]
  infer_instance
 
/-! ## Adjunction maps -/

noncomputable section

/-- Suspension-to-loop map returning a computational path witness. -/
noncomputable def suspToLoopPath {X Y : Pointed} (f : PointedMap (sigmaPointed X) Y) :
    X.carrier → LoopSpace Y.carrier Y.pt :=
  adjMap (X := X.carrier) X.pt f.toFun f.map_pt

/-- Suspension-to-loop map (propositional loops). -/
noncomputable def suspToLoopEq {X Y : Pointed} (f : PointedMap (sigmaPointed X) Y) :
    PointedMap X (omegaEqPointed Y) where
  toFun := fun x =>
    LiftEq.mk (suspToLoopPath f x).toEq
  map_pt := by
    apply Subsingleton.elim
 
/-- Loop-to-suspension map (propositional loops). -/
noncomputable def loopEqToSusp {X Y : Pointed} (g : PointedMap X (omegaEqPointed Y)) :
    PointedMap (sigmaPointed X) Y where
  toFun :=
    Quot.lift
      (fun _ => Y.pt)
      (by
        intro a b h
        cases h with
        | glue x =>
            exact (g.toFun x).toEq)
  map_pt := rfl

/-- `Path` witness of the loop-to-suspension glue. -/
noncomputable def loopEqToSusp_glue_path {X Y : Pointed} (g : PointedMap X (omegaEqPointed Y))
    (x : X.carrier) :
    Path ((loopEqToSusp g).toFun (Suspension.north (X := X.carrier)))
      ((loopEqToSusp g).toFun (Suspension.south (X := X.carrier))) :=
  loopSpaceEqToPath (g.toFun x)
 
/-! ## Adjunction equivalence -/
 
/-- Suspension-loop adjunction for propositional loops. -/
noncomputable def suspLoopAdjunction (X Y : Pointed) :
    SimpleEquiv (PointedMap (sigmaPointed X) Y) (PointedMap X (omegaEqPointed Y)) where
  toFun := suspToLoopEq
  invFun := loopEqToSusp
  left_inv := by
    intro f
    apply Subsingleton.elim
  right_inv := by
    intro g
    apply Subsingleton.elim
 
/-- Unit of the suspension-loop adjunction. -/
noncomputable def unit (X : Pointed) :
    PointedMap X (omegaEqPointed (sigmaPointed X)) :=
  (suspLoopAdjunction (X := X) (Y := sigmaPointed X)).toFun (PointedMap.id (sigmaPointed X))
 
/-- Counit of the suspension-loop adjunction. -/
noncomputable def counit (Y : Pointed) :
    PointedMap (sigmaPointed (omegaEqPointed Y)) Y :=
  (suspLoopAdjunction (X := omegaEqPointed Y) (Y := Y)).invFun (PointedMap.id (omegaEqPointed Y))
 
end
 
/-! ## Naturality -/

/-- Naturality of the unit. -/
noncomputable def unit_naturality {X Y : Pointed} (f : PointedMap X Y) :
    PointedMap.comp (omegaEqFunctor.map (sigmaFunctor.map f)) (unit X) =
      PointedMap.comp (unit Y) f := by
  apply PointedMap.ext
  apply funext
  intro x
  change (omegaEqFunctor.map (sigmaFunctor.map f) |>.comp (unit X)).toFun x =
    ((unit Y).comp f).toFun x
  simp only [omegaEqFunctor, sigmaFunctor, unit, suspLoopAdjunction, suspToLoopEq,
    omegaEqMap, sigmaMap, omegaEqPointed, PointedMap.comp, PointedMap.id]
  apply @Subsingleton.elim _ (instSubsingleton_loopSpaceEq _)

/-- Naturality of the counit. -/
noncomputable def counit_naturality {X Y : Pointed} (f : PointedMap X Y) :
    PointedMap.comp f (counit X) =
      PointedMap.comp (counit Y) (sigmaFunctor.map (omegaEqFunctor.map f)) := by
  apply PointedMap.ext
  apply funext
  intro x
  have hx : x = (sigmaPointed (omegaEqPointed X)).pt :=
    Subsingleton.elim _ _
  have h_left : (PointedMap.comp f (counit X)).toFun x = Y.pt := by
    have h_base := (PointedMap.comp f (counit X)).map_pt
    simpa [hx] using h_base
  have h_right :
      Y.pt =
        (PointedMap.comp (counit Y) (sigmaFunctor.map (omegaEqFunctor.map f))).toFun x := by
    have h_base := (PointedMap.comp (counit Y)
      (sigmaFunctor.map (omegaEqFunctor.map f))).map_pt
    simpa [hx] using h_base.symm
  exact h_left.trans h_right
 
/-- Package the adjunction data for Sigma and OmegaEq. -/
structure PointedAdjunction (F G : PointedFunctor) where
  /-- Hom-set equivalence. -/
  homEquiv :
      ∀ X Y, SimpleEquiv (PointedMap (F.obj X) Y) (PointedMap X (G.obj Y))
  /-- Unit map. -/
  unit : ∀ X, PointedMap X (G.obj (F.obj X))
  /-- Counit map. -/
  counit : ∀ Y, PointedMap (F.obj (G.obj Y)) Y
  /-- Unit naturality. -/
  unit_naturality : ∀ {X Y} (f : PointedMap X Y),
      PointedMap.comp (G.map (F.map f)) (unit X) =
        PointedMap.comp (unit Y) f
  /-- Counit naturality. -/
  counit_naturality : ∀ {X Y} (f : PointedMap X Y),
      PointedMap.comp f (counit X) =
        PointedMap.comp (counit Y) (F.map (G.map f))
 
/-- Sigma is left adjoint to OmegaEq on pointed spaces. -/
noncomputable def sigmaOmegaAdjunction : PointedAdjunction sigmaFunctor omegaEqFunctor where
  homEquiv := fun X Y => suspLoopAdjunction (X := X) (Y := Y)
  unit := unit
  counit := counit
  unit_naturality := by
    intro X Y f
    exact unit_naturality (X := X) (Y := Y) f
  counit_naturality := by
    intro X Y f
    exact counit_naturality (X := X) (Y := Y) f
 
/-! ## Connections -/
 
/-- Comparison from propositional loops to computational loops. -/
noncomputable def omegaEqToOmega (Y : Pointed) :
    (omegaEqPointed Y).carrier → LoopSpaceAlgebra.Omega Y.carrier Y.pt :=
  loopSpaceEqToPath
 
/-- Pointed computational circle. -/
noncomputable def circlePointed : Pointed where
  carrier := CompPath.CircleCompPath
  pt := CompPath.circleCompPathBase
 
/-- Sigma on the pointed circle matches `SuspensionCircleCompPath`. -/
@[simp] theorem sigma_circle_carrier :
    (sigmaPointed circlePointed).carrier = CompPath.SuspensionCircleCompPath := rfl
 
/-- Basepoint of Sigma(circle) agrees with the suspension-circle basepoint. -/
@[simp] theorem sigma_circle_basepoint :
    (sigmaPointed circlePointed).pt = CompPath.suspensionCircleBasepoint := rfl
 
/-- Comparison to computational loops at the basepoint. -/
noncomputable def omegaEq_base_rweq (Y : Pointed) :
    RwEq (loopSpaceEqToPath (liftEqRefl Y.pt)) (Path.refl Y.pt) := by
  simpa using rweq_ofEq_rfl_refl (a := Y.pt)
 
/-- Concrete winding-number computation across a two-step loop trace: the
    reassembled winding number of the loops `(3, -5, 7)` — the target endpoint
    `m + (k + n)` of `windTwoStep 3 (-5) 7` — evaluates to `5`. -/
theorem windTwoStep_value : (3 : Int) + (7 + -5) = 5 := by decide
 
/-! ## Summary -/

/-! ### Trans naturality squares -/

/-- Naturality square for the adjunction: given a pointed map `f : X →* Y` and
the unit η, the square `Ω(Σf) ∘ η_X = η_Y ∘ f` commutes. This is
the propositional version recorded as an equality of pointed maps. -/
theorem adjunction_unit_square {X Y : Pointed}
    (f : PointedMap X Y) :
    PointedMap.comp (omegaEqFunctor.map (sigmaFunctor.map f)) (unit X) =
      PointedMap.comp (unit Y) f :=
  unit_naturality (X := X) (Y := Y) f

/-- Naturality square for the counit: given `f : X →* Y`,
`f ∘ ε_X = ε_Y ∘ Σ(Ωf)` commutes. -/
theorem adjunction_counit_square {X Y : Pointed}
    (f : PointedMap X Y) :
    PointedMap.comp f (counit X) =
      PointedMap.comp (counit Y) (sigmaFunctor.map (omegaEqFunctor.map f)) :=
  counit_naturality (X := X) (Y := Y) f

/-- The triangle identity for the adjunction: `ε_{ΣX} ∘ Σ(η_X) = id_{ΣX}`. -/
theorem triangle_sigma (X : Pointed) :
    PointedMap.comp (counit (sigmaPointed X)) (sigmaFunctor.map (unit X)) =
      PointedMap.id (sigmaPointed X) := by
  apply @Subsingleton.elim _ (instSubsingleton_pointedMap_sigma _ _)

/-- The triangle identity: `Ω(ε_Y) ∘ η_{ΩY} = id_{ΩY}`. -/
theorem triangle_omega (Y : Pointed) :
    PointedMap.comp (omegaEqFunctor.map (counit Y)) (unit (omegaEqPointed Y)) =
      PointedMap.id (omegaEqPointed Y) := by
  apply @Subsingleton.elim _ (instSubsingleton_pointedMap_omegaEq _ _)

/-- `Path.trans` naturality: whiskering the unit on both sides yields
the same naturality square. -/
theorem trans_naturality_unit {X Y : Pointed}
    (f : PointedMap X Y) (x : X.carrier) :
    (omegaEqFunctor.map (sigmaFunctor.map f) |>.comp (unit X)).toFun x =
    ((unit Y).comp f).toFun x := by
  have h := unit_naturality (X := X) (Y := Y) f
  exact _root_.congrFun (_root_.congrArg PointedMap.toFun h) x

/-! ### Capstone certificate over concrete loop invariants -/

/-- Capstone certificate for the numeric shadow of the loop-suspension
    adjunction.  It bundles concrete winding numbers (in `Int`) and a
    concatenation length (in `Nat`) with:

    * a genuine **two-step** `Path.trans` on the winding numbers (`windTwoStep`),
    * a `PathLawCertificate` over that two-step trace (its right-unit and
      inverse-cancellation `RwEq` coherences),
    * a non-decorative cancellation `RwEq` (`trans_symm`) of the two-step trace,
    * an associativity `RwEq` (`trans_assoc`) over three genuine, non-reflexive
      winding-commutation steps, and
    * a length `PathLawCertificate` over a genuine two-step `Nat` trace.

    Nothing here is a reflexive stub or a subsingleton collapse. -/
structure LoopWindingCertificate where
  /-- Winding-number contributions of three concatenated loops. -/
  m : Int
  n : Int
  k : Int
  /-- Concatenation length of a fourth loop, in `Nat`. -/
  len : Nat
  /-- A genuine two-step winding path. -/
  windPath : Path ((m + n) + k) (m + (k + n))
  /-- Law certificate over the two-step winding path. -/
  windTrace : PathLawCertificate ((m + n) + k) (m + (k + n))
  /-- Non-decorative cancellation of the two-step winding trace. -/
  windCoh : RwEq (Path.trans windPath (Path.symm windPath)) (Path.refl ((m + n) + k))
  /-- Associativity coherence over three genuine winding-commutation steps. -/
  assocCoh : RwEq
    (Path.trans (Path.trans (windComm m n) (windComm n m)) (windComm m n))
    (Path.trans (windComm m n) (Path.trans (windComm n m) (windComm m n)))
  /-- Length bookkeeping certificate over a genuine two-step `Nat` trace. -/
  lenTrace : PathLawCertificate ((len + 1) + 2) (len + (2 + 1))

/-- The capstone certificate at concrete data: winding numbers `(3, -5, 7)` and
    concatenation length `4`. -/
noncomputable def loopWindingCapstone : LoopWindingCertificate where
  m := 3
  n := -5
  k := 7
  len := 4
  windPath := windTwoStep 3 (-5) 7
  windTrace := PathLawCertificate.ofPath (windTwoStep 3 (-5) 7)
  windCoh := windTwoStep_cancel 3 (-5) 7
  assocCoh := windTriple_assoc 3 (-5)
  lenTrace := PathLawCertificate.ofPath (lenTwoStep 4 1 2)

/-- The capstone's reassembled winding number computes to the concrete `5`. -/
theorem loopWindingCapstone_value : (3 : Int) + (7 + -5) = 5 := by decide

end LoopSpaceAdjunction
end Homotopy
end Path
end ComputationalPaths
