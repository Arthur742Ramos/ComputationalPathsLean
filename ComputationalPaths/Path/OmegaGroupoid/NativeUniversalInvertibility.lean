import ComputationalPaths.Path.OmegaGroupoid.NativeOperadicOperations

/-!
# Invertibility for every boundary-compatible composition system

The quantifier over systems is essential in van den Berg--Garner,
Definitions 2.1.3--2.1.4 (arXiv:0812.0298). This file proves a stronger
carrier-level statement: any adjacent identity and composition operations
with the specified globular boundaries make every positive native cell
coinductively invertible. The carrier remains the raw Path/RwEq two-skeleton
with its explicitly declared recursive coskeletal extension.
-/

namespace ComputationalPaths.Path.OmegaFoundations

universe u

namespace NativeUniversal

/-- The boundary laws required to interpret a system of compositions.
No associativity or chosen filler is assumed by this interface. -/
structure BoundaryOperations (A : Type u) where
  identity : {n : Nat} → NativeTower.Cell A n → NativeTower.Cell A (n + 1)
  source_identity : ∀ {n} (p : NativeTower.Cell A n), NativeTower.source (identity p) = p
  target_identity : ∀ {n} (p : NativeTower.Cell A n), NativeTower.target (identity p) = p
  compose : {n : Nat} → (p q : NativeTower.Cell A (n + 1)) →
    NativeTower.target p = NativeTower.source q → NativeTower.Cell A (n + 1)
  source_compose : ∀ {n} (p q : NativeTower.Cell A (n + 1)) h,
    NativeTower.source (compose p q h) = NativeTower.source p
  target_compose : ∀ {n} (p q : NativeTower.Cell A (n + 1)) h,
    NativeTower.target (compose p q h) = NativeTower.target q

namespace BoundaryOperations

variable {A : Type u}

/-- A right cancellation cell for the supplied operations, not for an
independently fixed composition on the carrier. -/
noncomputable def cancelRight (C : BoundaryOperations A) {n : Nat}
    (p : NativeTower.Cell A (n + 1)) :
    { r : NativeTower.Cell A (n + 2) //
      NativeTower.source r = C.compose p (NativeTower.reverse p) (NativeTower.source_reverse p).symm ∧
      NativeTower.target r = C.identity (NativeTower.source p) } := by
  let l := C.compose p (NativeTower.reverse p) (NativeTower.source_reverse p).symm
  let r := C.identity (NativeTower.source p)
  have hs : NativeTower.source l = NativeTower.source r :=
    (C.source_compose _ _ _).trans (C.source_identity _).symm
  have ht : NativeTower.target l = NativeTower.target r :=
    (C.target_compose _ _ _).trans ((NativeTower.target_reverse p).trans (C.target_identity _).symm)
  exact ⟨NativeTower.fillPositive l r hs ht, NativeTower.fillPositive_boundary l r hs ht⟩

noncomputable def cancelLeft (C : BoundaryOperations A) {n : Nat}
    (p : NativeTower.Cell A (n + 1)) :
    { r : NativeTower.Cell A (n + 2) //
      NativeTower.source r = C.compose (NativeTower.reverse p) p (NativeTower.target_reverse p) ∧
      NativeTower.target r = C.identity (NativeTower.target p) } := by
  let l := C.compose (NativeTower.reverse p) p (NativeTower.target_reverse p)
  let r := C.identity (NativeTower.target p)
  have hs : NativeTower.source l = NativeTower.source r :=
    (C.source_compose _ _ _).trans ((NativeTower.source_reverse p).trans (C.source_identity _).symm)
  have ht : NativeTower.target l = NativeTower.target r :=
    (C.target_compose _ _ _).trans (C.target_identity _).symm
  exact ⟨NativeTower.fillPositive l r hs ht, NativeTower.fillPositive_boundary l r hs ht⟩

/-- The monotone cancellation operator for the supplied system. -/
def InvertibilityStep (C : BoundaryOperations A) (S : NativeTower.CellPredicate A)
    (n : Nat) (p : NativeTower.Cell A (n + 1)) : Prop :=
  ∃ (q : NativeTower.Cell A (n + 1))
    (hs : NativeTower.source q = NativeTower.target p) (ht : NativeTower.target q = NativeTower.source p),
    ∃ (r l : NativeTower.Cell A (n + 2)),
      NativeTower.source r = C.compose p q hs.symm ∧ NativeTower.target r = C.identity (NativeTower.source p) ∧
      NativeTower.source l = C.compose q p ht ∧ NativeTower.target l = C.identity (NativeTower.target p) ∧
      S (n + 1) r ∧ S (n + 1) l

theorem invertibilityStep_mono (C : BoundaryOperations A) {S T : NativeTower.CellPredicate A}
    (h : ∀ n p, S n p → T n p) {n : Nat} {p : NativeTower.Cell A (n + 1)} :
    C.InvertibilityStep S n p → C.InvertibilityStep T n p := by
  rintro ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, sr, sl⟩
  exact ⟨q, hs, ht, r, l, hr, hrt, hl, hlt, h _ _ sr, h _ _ sl⟩

/-- The greatest postfixed predicate, not a finite-stage approximation. -/
def WeaklyInvertible (C : BoundaryOperations A) (n : Nat) (p : NativeTower.Cell A (n + 1)) : Prop :=
  ∃ S : NativeTower.CellPredicate A, (∀ m c, S m c → C.InvertibilityStep S m c) ∧ S n p

theorem weaklyInvertible_coinduction (C : BoundaryOperations A) (S : NativeTower.CellPredicate A)
    (h : ∀ n p, S n p → C.InvertibilityStep S n p) {n : Nat} {p : NativeTower.Cell A (n + 1)}
    (hp : S n p) : C.WeaklyInvertible n p := ⟨S, h, hp⟩

theorem weaklyInvertible_unfold (C : BoundaryOperations A) {n : Nat} {p : NativeTower.Cell A (n + 1)} :
    C.WeaklyInvertible n p ↔ C.InvertibilityStep C.WeaklyInvertible n p := by
  constructor
  · rintro ⟨S, closed, hp⟩
    exact C.invertibilityStep_mono (fun m c hc => ⟨S, closed, hc⟩) (closed n p hp)
  · intro hp
    let T := C.InvertibilityStep C.WeaklyInvertible
    have inclusion : ∀ m c, C.WeaklyInvertible m c → T m c := by
      rintro m c ⟨S, closed, hc⟩
      exact C.invertibilityStep_mono (fun k d hd => ⟨S, closed, hd⟩) (closed m c hc)
    exact ⟨T, fun m c hc => C.invertibilityStep_mono inclusion hc, hp⟩

/-- Every positive cell is invertible for every boundary-compatible system.
Higher witnesses use the same supplied system at each recursive stage. -/
theorem all_cells_weaklyInvertible (C : BoundaryOperations A)
    (n : Nat) (p : NativeTower.Cell A (n + 1)) : C.WeaklyInvertible n p := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro m c _
  exact ⟨NativeTower.reverse c, NativeTower.source_reverse c, NativeTower.target_reverse c,
    (C.cancelRight c).val, (C.cancelLeft c).val,
    (C.cancelRight c).property.1, (C.cancelRight c).property.2,
    (C.cancelLeft c).property.1, (C.cancelLeft c).property.2, trivial, trivial⟩

end BoundaryOperations

/-- The previously audited contraction-selected operations instantiate the
universal interface with exactly their existing functions. -/
noncomputable def selected (A : Type u) : BoundaryOperations A where
  identity := NativeOperadic.identity
  source_identity p := (NativeOperadic.identity_boundary p).1
  target_identity p := (NativeOperadic.identity_boundary p).2
  compose := NativeOperadic.compose
  source_compose p q h := (NativeOperadic.compose_boundary p q h).1
  target_compose p q h := (NativeOperadic.compose_boundary p q h).2

theorem selected_invertibility_iff {A : Type u} {n : Nat} {p : NativeTower.Cell A (n + 1)} :
    (selected A).WeaklyInvertible n p ↔ NativeOperadic.WeaklyInvertible n p := Iff.rfl

/-- The selected instance still uses the exact raw path composition. -/
theorem selected_compose_paths {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    (selected A).compose (n := 0) (ULift.up (⟨a, b, p⟩ : PathOne A))
      (ULift.up (⟨b, c, q⟩ : PathOne A)) rfl = ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A) :=
  NativeOperadic.compose_paths p q

theorem selected_compose_three_paths {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (selected A).compose (n := 0) (ULift.up (⟨a, c, Path.trans p q⟩ : PathOne A))
      (ULift.up (⟨c, d, r⟩ : PathOne A)) rfl =
      ULift.up (⟨a, d, Path.trans (Path.trans p q) r⟩ : PathOne A) := selected_compose_paths _ _

open NativeOperadic

theorem binaryDiagram_top_source (G : GlobularSet.{u + 1}) {n : Nat}
    (p q : G.Cell (n + 1)) h :
    Pasting.source (binaryDiagramOn G (Pasting.Cut.top n) p q h) = Pasting.singleton (G.source p) := by
  let d := binaryDiagramOn G (Pasting.Cut.top n) p q h
  have hc := (Pasting.cutOperations G).source_compose (Pasting.Cut.top n)
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map _ (Pasting.singletonGlobular G) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
        (Pasting.CutBoundary.source_map _ (Pasting.singletonGlobular G) q).symm))
  exact (eq_of_heq ((Pasting.CutBoundary.source_top (Pasting.globular G) d).symm.trans
    ((heq_of_eq hc).trans (Pasting.CutBoundary.source_top (Pasting.globular G) (Pasting.singleton p))))).trans
    (Pasting.source_singleton G p)

theorem binaryDiagram_top_target (G : GlobularSet.{u + 1}) {n : Nat}
    (p q : G.Cell (n + 1)) h :
    Pasting.target (binaryDiagramOn G (Pasting.Cut.top n) p q h) = Pasting.singleton (G.target q) := by
  let d := binaryDiagramOn G (Pasting.Cut.top n) p q h
  have hc := (Pasting.cutOperations G).target_compose (Pasting.Cut.top n)
    (Pasting.singleton p) (Pasting.singleton q)
    ((Pasting.CutBoundary.target_map _ (Pasting.singletonGlobular G) p).trans
      ((_root_.congrArg (Pasting.singletonGlobular G).app h).trans
        (Pasting.CutBoundary.source_map _ (Pasting.singletonGlobular G) q).symm))
  exact (eq_of_heq ((Pasting.CutBoundary.target_top (Pasting.globular G) d).symm.trans
    ((heq_of_eq hc).trans (Pasting.CutBoundary.target_top (Pasting.globular G) (Pasting.singleton q))))).trans
    (Pasting.target_singleton G q)

def identityShape (n : Nat) : Pasting (n + 1) GlobularSet.terminal.{u + 1} :=
  Pasting.identity (Pasting.singleton (n := n) PUnit.unit)

noncomputable def binaryShape (n : Nat) : Pasting (n + 1) GlobularSet.terminal.{u + 1} :=
  binaryDiagramOn GlobularSet.terminal (Pasting.Cut.top n) PUnit.unit PUnit.unit
    (@Subsingleton.elim PUnit _ _ _)

/-- A system chooses operad operations over the nullary and adjacent binary
shapes, with trivial boundary operations. These boundary conditions make
the interpreted operations identities and composites on the given cells. -/
structure OperadicSystem (A : Type u) where
  identityOp : (n : Nat) → (collection A).operations.Cell (n + 1)
  identity_arity : ∀ n, (collection A).arity.app (identityOp n) = identityShape n
  identity_source : ∀ n, (collection A).operations.source (identityOp n) = one A n
  identity_target : ∀ n, (collection A).operations.target (identityOp n) = one A n
  composeOp : (n : Nat) → (collection A).operations.Cell (n + 1)
  compose_arity : ∀ n, (collection A).arity.app (composeOp n) = binaryShape n
  compose_source : ∀ n, (collection A).operations.source (composeOp n) = one A n
  compose_target : ∀ n, (collection A).operations.target (composeOp n) = one A n

namespace OperadicSystem

variable {A : Type u}

theorem identityInput_arity (S : OperadicSystem A) {n : Nat} (p : NativeTower.Cell A n) :
    (collection A).arity.app (n := n + 1) (S.identityOp n) =
      (GlobularCollection.shape (carrier A)).app (n := n + 1)
        (Pasting.identity (Pasting.singleton (G := carrier A) (n := n) p)) :=
  (S.identity_arity n).trans
    ((_root_.congrArg (Pasting.identity (n := n))
      (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) p).symm).trans
      (map_identityDiagram (GlobularSet.terminalMap (carrier A)) (Pasting.singleton p)).symm)

theorem top_matching {n : Nat} (p q : NativeTower.Cell A (n + 1))
    (h : NativeTower.target p = NativeTower.source q) :
    Pasting.CutBoundary.target (Pasting.Cut.top n) (carrier A) p =
      Pasting.CutBoundary.source (Pasting.Cut.top n) (carrier A) q :=
  eq_of_heq ((Pasting.CutBoundary.target_top (carrier A) p).trans
    ((heq_of_eq h).trans (Pasting.CutBoundary.source_top (carrier A) q).symm))

theorem composeInput_arity (S : OperadicSystem A) {n : Nat} (p q : NativeTower.Cell A (n + 1))
    (h : NativeTower.target p = NativeTower.source q) :
    (collection A).arity.app (n := n + 1) (S.composeOp n) =
      (GlobularCollection.shape (carrier A)).app
        (binaryDiagramOn (carrier A) (Pasting.Cut.top n) p q (top_matching p q h)) :=
  (S.compose_arity n).trans
    (binaryDiagramOn_map (GlobularSet.terminalMap (carrier A)) (Pasting.Cut.top n) p q
      (top_matching p q h) (@Subsingleton.elim PUnit _ _ _)).symm

noncomputable def identity (S : OperadicSystem A) {n : Nat} (p : NativeTower.Cell A n) :
    NativeTower.Cell A (n + 1) :=
  applyOperation (S.identityOp n) (Pasting.identity (Pasting.singleton p)) (S.identityInput_arity p)

noncomputable def compose (S : OperadicSystem A) {n : Nat} (p q : NativeTower.Cell A (n + 1))
    (h : NativeTower.target p = NativeTower.source q) : NativeTower.Cell A (n + 1) :=
  applyOperation (S.composeOp n) (binaryDiagramOn (carrier A) (Pasting.Cut.top n) p q (top_matching p q h))
    (S.composeInput_arity p q h)

theorem operation_boundary {n : Nat} (o : (collection A).operations.Cell (n + 1))
    (d : Pasting (n + 1) (carrier A)) ha (p q : NativeTower.Cell A n)
    (ho : (collection A).operations.source o = one A n)
    (ht : (collection A).operations.target o = one A n)
    (hsd : Pasting.source d = Pasting.singleton p) (htd : Pasting.target d = Pasting.singleton q) :
    NativeTower.source (applyOperation o d ha) = p ∧ NativeTower.target (applyOperation o d ha) = q := by
  let hp := (one_arity A n).trans (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) p).symm
  let hq := (one_arity A n).trans (Pasting.map_singleton (GlobularSet.terminalMap (carrier A)) q).symm
  let hs := (_root_.congrArg ((collection A).arity.app (n := n)) ho).trans
    (hp.trans (_root_.congrArg ((GlobularCollection.shape (carrier A)).app (n := n)) hsd.symm))
  let ht' := (_root_.congrArg ((collection A).arity.app (n := n)) ht).trans
    (hq.trans (_root_.congrArg ((GlobularCollection.shape (carrier A)).app (n := n)) htd.symm))
  exact ⟨(applyOperation_source o d ha hs).trans
      ((applyOperation_congr ho hsd hs hp).trans (Endomorphism.evaluation_unit_input (carrier A) (n := n) p)),
    (applyOperation_target o d ha ht').trans
      ((applyOperation_congr ht htd ht' hq).trans (Endomorphism.evaluation_unit_input (carrier A) (n := n) q))⟩

theorem identity_boundary (S : OperadicSystem A) {n : Nat} (p : NativeTower.Cell A n) :
    NativeTower.source (S.identity p) = p ∧ NativeTower.target (S.identity p) = p :=
  operation_boundary _ _ (S.identityInput_arity p) p p (S.identity_source n) (S.identity_target n)
    (Pasting.source_identity (carrier A) (Pasting.singleton p))
    (Pasting.target_identity (carrier A) (Pasting.singleton p))

theorem compose_boundary (S : OperadicSystem A) {n : Nat} (p q : NativeTower.Cell A (n + 1))
    (h : NativeTower.target p = NativeTower.source q) :
    NativeTower.source (S.compose p q h) = NativeTower.source p ∧
      NativeTower.target (S.compose p q h) = NativeTower.target q :=
  operation_boundary _ _ (S.composeInput_arity p q h) _ _ (S.compose_source n) (S.compose_target n)
    (binaryDiagram_top_source (carrier A) p q (top_matching p q h))
    (binaryDiagram_top_target (carrier A) p q (top_matching p q h))

/-- Every operadic system induces boundary-compatible carrier operations;
this map is proved from the action and unit laws, not assumed. -/
noncomputable def boundaryOperations (S : OperadicSystem A) : BoundaryOperations A where
  identity := S.identity
  source_identity p := (S.identity_boundary p).1
  target_identity p := (S.identity_boundary p).2
  compose := S.compose
  source_compose p q h := (S.compose_boundary p q h).1
  target_compose p q h := (S.compose_boundary p q h).2

/-- Universal quantification over actual operad-operation choices. -/
theorem all_cells_weaklyInvertible (S : OperadicSystem A)
    (n : Nat) (p : NativeTower.Cell A (n + 1)) : S.boundaryOperations.WeaklyInvertible n p :=
  S.boundaryOperations.all_cells_weaklyInvertible n p

end OperadicSystem

theorem identityShape_source (A : Type u) (n : Nat) :
    Pasting.source (identityShape.{u} n) = (collection A).arity.app (n := n) (one A n) :=
  (Pasting.source_identity GlobularSet.terminal _).trans (one_arity A n).symm

theorem identityShape_target (A : Type u) (n : Nat) :
    Pasting.target (identityShape.{u} n) = (collection A).arity.app (n := n) (one A n) :=
  (Pasting.target_identity GlobularSet.terminal _).trans (one_arity A n).symm

theorem binaryShape_source (A : Type u) (n : Nat) :
    Pasting.source (binaryShape.{u} n) = (collection A).arity.app (n := n) (one A n) :=
  (binaryDiagram_top_source GlobularSet.terminal (n := n) PUnit.unit PUnit.unit _).trans (one_arity A n).symm

theorem binaryShape_target (A : Type u) (n : Nat) :
    Pasting.target (binaryShape.{u} n) = (collection A).arity.app (n := n) (one A n) :=
  (binaryDiagram_top_target GlobularSet.terminal (n := n) PUnit.unit PUnit.unit _).trans (one_arity A n).symm

/-- Contractibility supplies a system, so the universal theorem is not
vacuous. Its choices are actual operations of the native endomorphism operad. -/
noncomputable def canonicalSystem (A : Type u) : OperadicSystem A where
  identityOp n := operation (identityShape n) (identityShape_source A n) (identityShape_target A n)
  identity_arity n := (NativeOperadic.operation_boundary _ _ _).2.2
  identity_source n := (NativeOperadic.operation_boundary _ _ _).1
  identity_target n := (NativeOperadic.operation_boundary _ _ _).2.1
  composeOp n := operation (binaryShape n) (binaryShape_source A n) (binaryShape_target A n)
  compose_arity n := (NativeOperadic.operation_boundary _ _ _).2.2
  compose_source n := (NativeOperadic.operation_boundary _ _ _).1
  compose_target n := (NativeOperadic.operation_boundary _ _ _).2.1

theorem every_operadic_system_invertible (A : Type u) :
    Nonempty (OperadicSystem A) ∧ ∀ (S : OperadicSystem A) (n : Nat) (p : NativeTower.Cell A (n + 1)),
      S.boundaryOperations.WeaklyInvertible n p :=
  ⟨⟨canonicalSystem A⟩, fun S n p => S.all_cells_weaklyInvertible n p⟩

end NativeUniversal

end ComputationalPaths.Path.OmegaFoundations
