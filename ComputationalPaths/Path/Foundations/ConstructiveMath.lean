import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace ConstructiveMath

universe u

structure BishopSet (α : Type u) where
  apart : α → α → Prop
  apart_irrefl : (x : α) → ¬ apart x x
  apart_symm : {x y : α} → apart x y → apart y x

noncomputable def bishopCarrier (α : Type u) : Type u := α
noncomputable def bishopApart {α : Type u} (B : BishopSet α) (x y : α) : Prop := B.apart x y
noncomputable def bishopEq {α : Type u} (B : BishopSet α) (x y : α) : Prop := ¬ bishopApart B x y
noncomputable def bishopReflPath {α : Type u} (x : α) : Path x x := Path.refl x
noncomputable def bishopPathChain {α : Type u} (x : α) : Path x x :=
  Path.trans (Path.refl x) (Path.refl x)

structure ConstructiveSequence (α : Type u) where
  term : Nat → α

noncomputable def seqEval {α : Type u} (s : ConstructiveSequence α) (n : Nat) : α := s.term n
noncomputable def seqHead {α : Type u} (s : ConstructiveSequence α) : α := seqEval s 0
noncomputable def seqNext {α : Type u} (s : ConstructiveSequence α) (n : Nat) : α := seqEval s (n + 1)

structure ConstructiveReal where
  approx : Nat → Int

noncomputable def realApprox (r : ConstructiveReal) (n : Nat) : Int := r.approx n
noncomputable def realApprox0 (r : ConstructiveReal) : Int := realApprox r 0
noncomputable def realApprox1 (r : ConstructiveReal) : Int := realApprox r 1

structure BrouwerMap (α : Type u) (β : Type u) where
  map : (Nat → α) → β
  continuity : Prop

noncomputable def brouwerApply {α : Type u} {β : Type u} (F : BrouwerMap α β) (s : Nat → α) : β := F.map s
noncomputable def brouwerContinuous {α : Type u} {β : Type u} (F : BrouwerMap α β) : Prop := F.continuity

structure BarPredicate (α : Type u) where
  holds : List α → Prop
  monotone : Prop

noncomputable def barHolds {α : Type u} (B : BarPredicate α) (xs : List α) : Prop := B.holds xs
noncomputable def barEmpty {α : Type u} (B : BarPredicate α) : Prop := barHolds B []

structure Fan (α : Type u) where
  branch : Nat → List α
  finiteBranching : Prop

noncomputable def fanBranch {α : Type u} (F : Fan α) (n : Nat) : List α := F.branch n
noncomputable def fanRoot {α : Type u} (F : Fan α) : List α := fanBranch F 0

structure FormalTopology (α : Type u) where
  cover : α → List α → Prop
  transitive : Prop

noncomputable def formalCover {α : Type u} (T : FormalTopology α) (a : α) (u : List α) : Prop := T.cover a u
noncomputable def formalReflexive {α : Type u} (T : FormalTopology α) (a : α) : Prop := formalCover T a [a]

structure PointFreeSpace (α : Type u) where
  isOpen : α → Prop
  top : α
  bottom : α
  top_open : isOpen top
  bottom_open : isOpen bottom

noncomputable def pointFreeOpen {α : Type u} (S : PointFreeSpace α) (a : α) : Prop := S.isOpen a
noncomputable def pointFreeTop {α : Type u} (S : PointFreeSpace α) : α := S.top
noncomputable def pointFreeBottom {α : Type u} (S : PointFreeSpace α) : α := S.bottom
noncomputable def pointFreeIsTopOpen {α : Type u} (S : PointFreeSpace α) : Prop := pointFreeOpen S (pointFreeTop S)
noncomputable def pointFreeIsBottomOpen {α : Type u} (S : PointFreeSpace α) : Prop := pointFreeOpen S (pointFreeBottom S)

theorem bishop_apart_irrefl {α : Type u} (B : BishopSet α) (x : α) :
    ¬ bishopApart B x x := B.apart_irrefl x

theorem bishop_eq_refl {α : Type u} (B : BishopSet α) (x : α) : bishopEq B x x :=
  bishop_apart_irrefl B x

theorem bishop_apart_symm {α : Type u} (B : BishopSet α) {x y : α} :
    bishopApart B x y → bishopApart B y x := B.apart_symm

theorem bishopReflPath_toEq {α : Type u} (x : α) : (bishopReflPath x).toEq = rfl := rfl

theorem bishopPathChain_toEq {α : Type u} (x : α) : (bishopPathChain x).toEq = rfl := rfl

theorem seqEval_zero {α : Type u} (s : ConstructiveSequence α) : seqEval s 0 = s.term 0 := rfl

theorem seqEval_succ {α : Type u} (s : ConstructiveSequence α) (n : Nat) :
    seqEval s (n + 1) = s.term (n + 1) := rfl

theorem seqHead_eq {α : Type u} (s : ConstructiveSequence α) : seqHead s = s.term 0 := rfl

theorem seqNext_eq {α : Type u} (s : ConstructiveSequence α) (n : Nat) :
    seqNext s n = s.term (n + 1) := rfl

theorem realApprox0_eq (r : ConstructiveReal) : realApprox0 r = r.approx 0 := rfl

theorem realApprox1_eq (r : ConstructiveReal) : realApprox1 r = r.approx 1 := rfl

theorem brouwerApply_eq {α : Type u} {β : Type u} (F : BrouwerMap α β) (s : Nat → α) :
    brouwerApply F s = F.map s := rfl

theorem brouwerContinuous_spec {α : Type u} {β : Type u} (F : BrouwerMap α β) :
    brouwerContinuous F = F.continuity := rfl

theorem barEmpty_eq {α : Type u} (B : BarPredicate α) : barEmpty B = B.holds [] := rfl

theorem fanRoot_eq {α : Type u} (F : Fan α) : fanRoot F = F.branch 0 := rfl

theorem formalReflexive_eq {α : Type u} (T : FormalTopology α) (a : α) :
    formalReflexive T a = T.cover a [a] := rfl

theorem pointFreeTop_open {α : Type u} (S : PointFreeSpace α) : pointFreeIsTopOpen S :=
  S.top_open

theorem pointFreeBottom_open {α : Type u} (S : PointFreeSpace α) : pointFreeIsBottomOpen S :=
  S.bottom_open

theorem pointFreeTop_def {α : Type u} (S : PointFreeSpace α) : pointFreeTop S = S.top := rfl

theorem pointFreeBottom_def {α : Type u} (S : PointFreeSpace α) :
    pointFreeBottom S = S.bottom := rfl

end ConstructiveMath
end Foundations
end Path
end ComputationalPaths
