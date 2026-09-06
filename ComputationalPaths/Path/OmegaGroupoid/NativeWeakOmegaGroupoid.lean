import ComputationalPaths.Path.OmegaGroupoid.NativeAssociativityBridge
import ComputationalPaths.Path.OmegaGroupoid.NativeUniversalInvertibility

/-!
# The native weak omega-groupoid, in normalized contractible-operad form

The convention is van den Berg--Garner, Definitions 2.1.1 and 2.1.4:
an algebra for a normalized contractible globular operad, with every
positive cell invertible for every system of compositions. The collection
presentation below is connected to the actual cartesian monad arity map.
The underlying free strict-category monad is the verified pasting monad.

The native instance preserves the raw Path/RwEq two-skeleton. Its higher
cells are the declared recursive coskeletal extension, not an assertion
about nontrivial homotopy groups or faithful higher rewrite derivations.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

/-- The collection presentation of a normalized contractible globular
operad. The stored multiplication is a lawful monoid for substitution. -/
structure NormalizedContractibleOperad where
  collection : GlobularCollection.{u}
  monoid : CategoryTheory.MonObj collection
  contraction : GlobularSet.Contraction collection.arity
  objectUnique : Unique (collection.operations.Cell 0)

namespace NormalizedContractibleOperad

noncomputable def monad (P : NormalizedContractibleOperad.{u}) : CategoryTheory.Monad GlobularSet.{u} :=
  letI := P.monoid
  P.collection.operadMonad

noncomputable def arityMonadHom (P : NormalizedContractibleOperad.{u}) :
    CategoryTheory.MonadHom P.monad Pasting.pastingMonad :=
  letI := P.monoid
  P.collection.operadArityMonadHom

theorem arityMonadHom_app (P : NormalizedContractibleOperad.{u}) (G : GlobularSet.{u}) :
    P.arityMonadHom.toNatTrans.app G = P.collection.inputs G := rfl

theorem arity_globular_pullback (P : NormalizedContractibleOperad.{u})
    {G H X : GlobularSet.{u}} (f : GlobularSet.Map G H)
    (p : GlobularSet.Map X (Pasting.globular G)) (q : GlobularSet.Map X (P.collection.application H))
    (h : GlobularSet.Map.comp (Pasting.mapGlobular f) p =
      GlobularSet.Map.comp (P.collection.inputs H) q) :
    ∃! d : GlobularSet.Map X (P.collection.application G),
      GlobularSet.Map.comp (P.collection.inputs G) d = p ∧
      GlobularSet.Map.comp (P.collection.map f) d = q :=
  P.collection.arity_globular_pullback f p q h

/-- The actual arity monad morphism is cartesian, including uniqueness of
the operation together with its complete relabelled input. -/
theorem arity_cartesian (P : NormalizedContractibleOperad.{u})
    {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) {n : Nat}
    (d : Pasting n G) (q : (P.collection.application H).Cell n)
    (h : Pasting.map f d = (P.collection.inputs H).app q) :
    ∃! r : (P.collection.application G).Cell n,
      (P.collection.inputs G).app r = d ∧ (P.collection.map f).app r = q :=
  P.collection.arity_cartesian f d q h

/-- Normalization is an equivalence on objects for every input globular
set, not just the assertion that the chosen carrier has a unique object. -/
def objectsEquiv (P : NormalizedContractibleOperad.{u}) (G : GlobularSet.{u}) :
    (P.collection.application G).Cell 0 ≃ G.Cell 0 := by
  letI := P.objectUnique
  exact {
    toFun := fun p => p.val.2
    invFun := fun p => ⟨⟨default, p⟩, @Subsingleton.elim PUnit _ _ _⟩
    left_inv := fun p => Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
    right_inv := fun _ => rfl }

theorem objectsEquiv_natural (P : NormalizedContractibleOperad.{u})
    {G H : GlobularSet.{u}} (f : GlobularSet.Map G H) (p : (P.collection.application G).Cell 0) :
    P.objectsEquiv H ((P.collection.map f).app p) = f.app (P.objectsEquiv G p) := rfl

/-- Transfer the operation contraction to the component at the terminal
object of the monad's arity map. This is the map used in the monad definition
of a globular operad, rather than an unconnected collection property. -/
noncomputable def terminalContraction (P : NormalizedContractibleOperad.{u}) :
    GlobularSet.Contraction (P.collection.inputs GlobularSet.terminal) where
  lift {n} p := by
    let C := P.collection
    let op := C.operation GlobularSet.terminal
    let a : GlobularSet.LiftingProblem C.arity n :=
      ⟨⟨op.app p.boundary.left, op.app p.boundary.right, op.parallel p.boundary.parallel⟩,
        p.arity,
        p.boundary.left.property.trans ((GlobularCollection.shape_terminal _).trans p.source_arity),
        p.boundary.right.property.trans ((GlobularCollection.shape_terminal _).trans p.target_arity)⟩
    let l := P.contraction.lift a
    have hs := _root_.congrArg
      (fun f : GlobularSet.Map (C.application GlobularSet.terminal) (C.application GlobularSet.terminal) =>
        f.app (n := n) p.boundary.left) C.applicationTerminalIso.hom_inv_id
    have ht := _root_.congrArg
      (fun f : GlobularSet.Map (C.application GlobularSet.terminal) (C.application GlobularSet.terminal) =>
        f.app (n := n) p.boundary.right) C.applicationTerminalIso.hom_inv_id
    exact ⟨C.atTerminal.app l.cell,
      (C.atTerminal.source_app l.cell).trans ((_root_.congrArg C.atTerminal.app l.source_cell).trans hs),
      (C.atTerminal.target_app l.cell).trans ((_root_.congrArg C.atTerminal.app l.target_cell).trans ht),
      l.arity_cell⟩

end NormalizedContractibleOperad

/-- The published normalized contractible-operad definition of weak
omega-category, using the actual associated monad and its algebra laws. -/
structure GlobularWeakCategory where
  operad : NormalizedContractibleOperad.{u}
  algebra : CategoryTheory.Monad.Algebra operad.monad

namespace NativeWeakOmega

set_option backward.isDefEq.respectTransparency.types false in
/-- The nullary operadic operation at an object is the original empty
rewrite trace, not merely a parallel one-cell. -/
theorem identity_objects {A : Type u} (a : A) :
    NativeOperadic.identity (A := A) (n := 0) (ULift.up a) =
      ULift.up (⟨a, a, Path.refl a⟩ : PathOne A) := by
  let d : Pasting 1 (NativeOperadic.carrier A) := Pasting.identity
    (Pasting.singleton (G := NativeOperadic.carrier A) (n := 0) (ULift.up a))
  have hd : (GlobularCollection.shape (NativeOperadic.carrier A)).app (n := 1) d ≠
      Pasting.singleton (G := GlobularSet.terminal) (n := 1) PUnit.unit := by
    intro h
    have hc := _root_.congrArg (Pasting.atom? (G := GlobularSet.terminal) (n := 1)) h
    change none = some PUnit.unit at hc
    cases hc
  change (NativeOperadic.standardEvaluation A).app (n := 1) d = _
  refine (NativeOperadic.standardEvaluation_one_nonsingleton d hd).trans ?_
  rfl

/-- The original primitive left unitor has exactly the boundary computed
by the selected operadic operations. This does not identify arbitrary
choices of two-dimensional coherence syntax. -/
theorem leftUnitor_operadic_boundary {A : Type u} {a b : A} (p : Path a b) :
    NativeTower.source (NativeTower.leftUnitor (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val =
        NativeOperadic.compose (A := A) (n := 0) (NativeOperadic.identity (ULift.up a))
          (ULift.up (⟨a, b, p⟩ : PathOne A)) (NativeOperadic.identity_boundary _).2 := by
  simp only [identity_objects, NativeOperadic.compose_paths]
  rfl

theorem rightUnitor_operadic_boundary {A : Type u} {a b : A} (p : Path a b) :
    NativeTower.source (NativeTower.rightUnitor (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val =
        NativeOperadic.compose (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
          (NativeOperadic.identity (ULift.up b)) (NativeOperadic.identity_boundary _).1.symm := by
  simp only [identity_objects, NativeOperadic.compose_paths]
  rfl

/-- The primitive cancellation trace has the operadic composite as source
and the operadic nullary operation as target. -/
theorem cancelRight_operadic_boundary {A : Type u} {a b : A} (p : Path a b) :
    NativeTower.source (NativeTower.cancelRight (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val =
        NativeOperadic.compose (A := A) (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
          (ULift.up (⟨b, a, Path.symm p⟩ : PathOne A)) rfl ∧
    NativeTower.target (NativeTower.cancelRight (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val = NativeOperadic.identity (A := A) (n := 0) (ULift.up a) := by
  rw [NativeOperadic.compose_paths, identity_objects]
  exact ⟨rfl, rfl⟩

theorem cancelLeft_operadic_boundary {A : Type u} {a b : A} (p : Path a b) :
    NativeTower.source (NativeTower.cancelLeft (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val =
        NativeOperadic.compose (A := A) (n := 0) (ULift.up (⟨b, a, Path.symm p⟩ : PathOne A))
          (ULift.up (⟨a, b, p⟩ : PathOne A)) rfl ∧
    NativeTower.target (NativeTower.cancelLeft (A := A) (n := 0)
      (ULift.up (⟨a, b, p⟩ : PathOne A))).val = NativeOperadic.identity (A := A) (n := 0) (ULift.up b) := by
  rw [NativeOperadic.compose_paths, identity_objects]
  exact ⟨rfl, rfl⟩

noncomputable def operad (A : Type u) : NormalizedContractibleOperad.{u + 1} where
  collection := NativeOperadic.collection A
  monoid := Endomorphism.operad (NativeTower.globular A)
  contraction := Endomorphism.nativeContraction A
  objectUnique := inferInstanceAs (Unique PUnit)

noncomputable def category (A : Type u) : GlobularWeakCategory.{u + 1} where
  operad := operad A
  algebra := Endomorphism.algebra (NativeTower.globular A)

theorem category_carrier (A : Type u) : (category A).algebra.A = NativeTower.globular A := rfl

theorem category_action (A : Type u) :
    (category A).algebra.a = Endomorphism.evaluation (NativeTower.globular A) := rfl

/-- The category's actual algebra carrier realizes the original raw
computational-path skeleton, with all four boundary correspondences. -/
def realizes (A : Type u) : RealizesPathSkeleton (category A).algebra.A A := NativeTower.realizes A

/-- The universal positive-dimensional groupoid condition for this very
operad and its action, including existence of a composition system. -/
theorem all_systems_invertible (A : Type u) :
    Nonempty (NativeUniversal.OperadicSystem A) ∧
      ∀ (S : NativeUniversal.OperadicSystem A) (n : Nat) (p : (category A).algebra.A.Cell (n + 1)),
        S.boundaryOperations.WeaklyInvertible n p :=
  NativeUniversal.every_operadic_system_invertible A

/-- The full native structural theorem. The category includes the lawful
normalized contractible operad and its actual monad algebra; its carrier
is the raw recursive native tower. Invertibility quantifies over every
composition system interpreted by that operad on this same carrier. -/
theorem fullWeakOmegaGroupoid (A : Type u) :
    Nonempty (RealizesPathSkeleton (category A).algebra.A A) ∧
    (category A).algebra.A = NativeTower.globular A ∧
    (category A).algebra.a = Endomorphism.evaluation (NativeTower.globular A) ∧
    Nonempty (NativeUniversal.OperadicSystem A) ∧
    ∀ (S : NativeUniversal.OperadicSystem A) (n : Nat) (p : (category A).algebra.A.Cell (n + 1)),
      S.boundaryOperations.WeaklyInvertible n p :=
  ⟨⟨realizes A⟩, rfl, rfl, all_systems_invertible A⟩

end NativeWeakOmega

namespace NativeWeakOmega.Semantics

/-- A diagnostic quotient only: the constructed carrier is not replaced
by this quotient. Its relation is the actual inhabited rewrite type. -/
def pathSetoid {A : Type u} (a b : A) : Setoid (Path a b) where
  r p q := Nonempty (RwEq p q)
  iseqv := ⟨fun p => QuotientPathInduction.rweq_total p p,
    fun {_ _} _ => QuotientPathInduction.rweq_total _ _,
    fun {_ _ _} _ _ => QuotientPathInduction.rweq_total _ _⟩

/-- The one-dimensional homotopy quotient is precisely ambient equality,
not a source of nontrivial fundamental groups. Raw paths are still retained
before taking this explicitly separate diagnostic quotient. -/
noncomputable def pathComponentsEquiv {A : Type u} (a b : A) :
    Quotient (pathSetoid a b) ≃ PLift (a = b) where
  toFun := Quotient.lift (fun p => PLift.up p.proof) (fun _ _ _ => Subsingleton.elim _ _)
  invFun h := Quotient.mk _ (QuotientPathInduction.emptyTrace h.down)
  left_inv p := Quotient.inductionOn p (fun _ => Quotient.sound (QuotientPathInduction.rweq_total _ _))
  right_inv _ := Subsingleton.elim _ _

def LoopCell {A : Type u} (n : Nat) (a : NativeTower.Cell A n) :=
  { p : NativeTower.Cell A (n + 1) // NativeTower.source p = a ∧ NativeTower.target p = a }

def LoopRelated {A : Type u} {n : Nat} {a : NativeTower.Cell A n} (p q : LoopCell n a) : Prop :=
  ∃ h : NativeTower.Cell A (n + 2), NativeTower.source h = p.val ∧ NativeTower.target h = q.val

theorem loopRelated_total {A : Type u} {n : Nat} {a : NativeTower.Cell A n} (p q : LoopCell n a) :
    LoopRelated p q :=
  ⟨NativeTower.fillPositive p.val q.val (p.property.1.trans q.property.1.symm)
    (p.property.2.trans q.property.2.symm), NativeTower.fillPositive_boundary _ _ _ _⟩

def loopSetoid {A : Type u} (n : Nat) (a : NativeTower.Cell A n) : Setoid (LoopCell n a) where
  r := LoopRelated
  iseqv := ⟨fun p => loopRelated_total p p, fun {_ _} _ => loopRelated_total _ _,
    fun {_ _ _} _ _ => loopRelated_total _ _⟩

/-- At every dimension the based loop classes have exactly one element.
This is a semantic audit theorem, not a quotient used to build the model. -/
@[instance_reducible] noncomputable def loopClassesUnique {A : Type u} (n : Nat) (a : NativeTower.Cell A n) :
    Unique (Quotient (loopSetoid n a)) where
  default := Quotient.mk _ ⟨NativeTower.identity a, NativeTower.source_identity a, NativeTower.target_identity a⟩
  uniq p := Quotient.inductionOn p (fun _ => Quotient.sound (loopRelated_total _ _))

theorem higher_cells_determined_by_boundary {A : Type u} {n : Nat}
    (p q : NativeTower.Cell A (n + 3))
    (hs : NativeTower.source p = NativeTower.source q) (ht : NativeTower.target p = NativeTower.target q) :
    p = q := NativeTower.higher_ext p q hs ht

/-- The collapse of higher homotopy classes does not identify raw rewrite
syntax in dimension two. This explicit multistep witness stays distinct. -/
theorem raw_rewrites_still_distinct {A : Type u} {a b : A} (p : Path a b) :
    (⟨a, b, p, p, RwEq.refl p⟩ : NativeTower.Cell A 2) ≠
      (⟨a, b, p, p, RwEq.trans (RwEq.refl p) (RwEq.refl p)⟩ : NativeTower.Cell A 2) :=
  NativeTower.distinct_rewrite_cells p

end NativeWeakOmega.Semantics

end ComputationalPaths.Path.OmegaFoundations
