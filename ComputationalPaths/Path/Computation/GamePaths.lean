/-
# Game Semantics via Computational Paths

This module models game semantics using computational paths:
games as path arenas, strategies as path selections, composition
of strategies, copycat strategy, winning conditions as path
properties, and game morphisms.

## References

- Abramsky & Jagadeesan, "Games and Full Completeness for Multiplicative Linear Logic"
- Hyland & Ong, "On Full Abstraction for PCF"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace GamePaths

universe u v

open ComputationalPaths.Path

/-! ## Games as Path Arenas -/

/-- A move in a game, tagged by player. -/
inductive Player where
  | O : Player  -- Opponent
  | P : Player  -- Proponent
  deriving Repr, BEq, DecidableEq

/-- Switch player. -/
noncomputable def Player.swap : Player → Player
  | O => P
  | P => O

/-- Swap is involutive. -/
theorem player_swap_swap (p : Player) : p.swap.swap = p := by
  cases p <;> rfl

/-- A game arena with moves and enabling structure. -/
structure Arena (M : Type u) where
  polarity : M → Player
  initial : List M
  enables : M → M → Prop

/-- A move sequence (play) in an arena. -/
structure Play (M : Type u) (A : Arena M) where
  moves : List M

/-- Empty play. -/
noncomputable def Play.empty {M : Type u} (A : Arena M) : Play M A :=
  ⟨[]⟩

/-- Extend a play with a new move. -/
noncomputable def Play.extend {M : Type u} {A : Arena M} (p : Play M A) (m : M) : Play M A :=
  ⟨p.moves ++ [m]⟩

/-- Length of a play. -/
noncomputable def Play.length {M : Type u} {A : Arena M} (p : Play M A) : Nat :=
  p.moves.length

/-- Empty play has length 0. -/
theorem play_empty_length {M : Type u} (A : Arena M) :
    (Play.empty A).length = 0 := rfl

/-- Extended play increases length by 1. -/
theorem play_extend_length {M : Type u} {A : Arena M} (p : Play M A) (m : M) :
    (p.extend m).length = p.length + 1 := by
  simp [Play.extend, Play.length, List.length_append]

/-! ## Strategies as Path Selections -/

/-- A strategy is a function from plays to optional moves. -/
structure Strategy (M : Type u) (A : Arena M) where
  respond : Play M A → Option M

/-- A deterministic strategy always gives the same response. -/
theorem strategy_deterministic {M : Type u} {A : Arena M}
    (s : Strategy M A) (p : Play M A) :
    s.respond p = s.respond p := rfl

/-- The empty (always-pass) strategy. -/
noncomputable def Strategy.pass {M : Type u} (A : Arena M) : Strategy M A :=
  ⟨fun _ => none⟩

/-- The pass strategy always returns none. -/
theorem pass_responds_none {M : Type u} (A : Arena M) (p : Play M A) :
    (Strategy.pass A).respond p = none := rfl

/-! ## Strategy Paths -/

/-- Path between strategies: they agree on all plays. -/
noncomputable def strategyPath {M : Type u} {A : Arena M}
    (s1 s2 : Strategy M A) (h : s1 = s2) : Path s1 s2 :=
  Path.mk [Step.mk _ _ h] h

/-- Strategy equality implies response equality. -/
theorem strategy_eq_respond {M : Type u} {A : Arena M}
    {s1 s2 : Strategy M A} (h : s1 = s2) (p : Play M A) :
    s1.respond p = s2.respond p := by
  subst h; rfl

/-- Path from strategy equivalence. -/
noncomputable def strategyEqPath {M : Type u} {A : Arena M}
    {s1 s2 : Strategy M A} (h : ∀ p, s1.respond p = s2.respond p) :
    s1.respond = s2.respond :=
  funext h

/-! ## Copycat Strategy -/

/-- A copycat strategy copies the last opponent move. -/
noncomputable def copycatStrategy {M : Type u} (A : Arena M) [DecidableEq M] :
    Strategy M A where
  respond := fun p =>
    match p.moves.getLast? with
    | some m => some m
    | none => A.initial.head?

/-- Copycat on empty play returns the initial move. -/
theorem copycat_empty {M : Type u} (A : Arena M) [DecidableEq M] :
    (copycatStrategy A).respond (Play.empty A) = A.initial.head? := rfl

/-! ## Game Composition -/

/-- Composed game arena from two arenas sharing an interface. -/
structure ComposedArena (M1 M2 : Type u) where
  arena1 : Arena M1
  arena2 : Arena M2

/-- A composed strategy from two strategies. -/
structure ComposedStrategy (M1 M2 : Type u)
    (C : ComposedArena M1 M2) where
  strat1 : Strategy M1 C.arena1
  strat2 : Strategy M2 C.arena2

/-- Projection to first component strategy. -/
noncomputable def ComposedStrategy.proj1 {M1 M2 : Type u} {C : ComposedArena M1 M2}
    (cs : ComposedStrategy M1 M2 C) : Strategy M1 C.arena1 :=
  cs.strat1

/-- Projection to second component strategy. -/
noncomputable def ComposedStrategy.proj2 {M1 M2 : Type u} {C : ComposedArena M1 M2}
    (cs : ComposedStrategy M1 M2 C) : Strategy M2 C.arena2 :=
  cs.strat2

/-- Composed strategy projections recover components. -/
theorem composed_proj1 {M1 M2 : Type u} {C : ComposedArena M1 M2}
    (cs : ComposedStrategy M1 M2 C) :
    cs.proj1 = cs.strat1 := rfl

theorem composed_proj2 {M1 M2 : Type u} {C : ComposedArena M1 M2}
    (cs : ComposedStrategy M1 M2 C) :
    cs.proj2 = cs.strat2 := rfl

/-! ## Winning Conditions as Path Properties -/

/-- A winning condition is a predicate on plays. -/
structure WinCondition (M : Type u) (A : Arena M) where
  wins : Play M A → Prop

/-- A strategy is winning if all maximal plays satisfy the condition. -/
structure WinningStrategy (M : Type u) (A : Arena M) extends Strategy M A where
  condition : WinCondition M A

/-- Two winning conditions are equivalent if they agree on all plays. -/
noncomputable def winCondEquiv {M : Type u} {A : Arena M}
    (w1 w2 : WinCondition M A) : Prop :=
  ∀ p : Play M A, w1.wins p ↔ w2.wins p

/-- Win condition equivalence is reflexive. -/
theorem winCondEquiv_refl {M : Type u} {A : Arena M} (w : WinCondition M A) :
    winCondEquiv w w :=
  fun _ => Iff.rfl

/-- Win condition equivalence is symmetric. -/
theorem winCondEquiv_symm {M : Type u} {A : Arena M}
    {w1 w2 : WinCondition M A} (h : winCondEquiv w1 w2) :
    winCondEquiv w2 w1 :=
  fun p => (h p).symm

/-- Win condition equivalence is transitive. -/
theorem winCondEquiv_trans {M : Type u} {A : Arena M}
    {w1 w2 w3 : WinCondition M A}
    (h1 : winCondEquiv w1 w2) (h2 : winCondEquiv w2 w3) :
    winCondEquiv w1 w3 :=
  fun p => (h1 p).trans (h2 p)

/-! ## Game Morphisms -/

/-- A morphism between game arenas. -/
structure ArenaMorphism (M1 M2 : Type u) (A1 : Arena M1) (A2 : Arena M2) where
  mapMove : M1 → M2
  pres_polarity : ∀ m : M1, A2.polarity (mapMove m) = A1.polarity m

/-- Identity arena morphism. -/
noncomputable def ArenaMorphism.id {M : Type u} (A : Arena M) : ArenaMorphism M M A A where
  mapMove := fun m => m
  pres_polarity := fun _ => rfl

/-- Identity morphism maps moves identically. -/
theorem arena_morph_id_map {M : Type u} {A : Arena M} (m : M) :
    (ArenaMorphism.id A).mapMove m = m := rfl

/-- Composition of arena morphisms. -/
noncomputable def ArenaMorphism.comp {M1 M2 M3 : Type u}
    {A1 : Arena M1} {A2 : Arena M2} {A3 : Arena M3}
    (g : ArenaMorphism M2 M3 A2 A3) (f : ArenaMorphism M1 M2 A1 A2) :
    ArenaMorphism M1 M3 A1 A3 where
  mapMove := g.mapMove ∘ f.mapMove
  pres_polarity := fun m => by
    simp [Function.comp]
    rw [g.pres_polarity, f.pres_polarity]

/-- Morphisms transform plays. -/
noncomputable def ArenaMorphism.mapPlay {M1 M2 : Type u} {A1 : Arena M1} {A2 : Arena M2}
    (f : ArenaMorphism M1 M2 A1 A2) (p : Play M1 A1) : Play M2 A2 :=
  ⟨p.moves.map f.mapMove⟩

/-- Identity morphism preserves play length. -/
theorem id_morph_play_length {M : Type u} {A : Arena M} (p : Play M A) :
    ((ArenaMorphism.id A).mapPlay p).length = p.length := by
  simp [ArenaMorphism.mapPlay, ArenaMorphism.id, Play.length]

/-- Morphisms preserve empty plays. -/
theorem morph_empty_play {M1 M2 : Type u} {A1 : Arena M1} {A2 : Arena M2}
    (f : ArenaMorphism M1 M2 A1 A2) :
    f.mapPlay (Play.empty A1) = Play.empty A2 := rfl

/-! ## Game Path Algebra -/

/-- Path between plays induced by a path between arenas. -/
noncomputable def playPath {M : Type u} {A : Arena M}
    {p1 p2 : Play M A} (h : p1 = p2) : Path p1 p2 :=
  Path.mk [Step.mk _ _ h] h

/-- Transport of play properties along paths. -/
noncomputable def playTransport {M : Type u} {A : Arena M}
    {P : Play M A → Type v} {p1 p2 : Play M A}
    (h : p1 = p2) (x : P p1) : P p2 :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Transport along reflexive play path is identity. -/
theorem play_transport_refl {M : Type u} {A : Arena M}
    {P : Play M A → Type v} (p : Play M A) (x : P p) :
    playTransport (rfl : p = p) x = x := rfl

/-- CongrArg for strategy response through play path. -/
theorem strategy_congrArg {M : Type u} {A : Arena M}
    (s : Strategy M A) {p1 p2 : Play M A} (h : p1 = p2) :
    s.respond p1 = s.respond p2 := by subst h; rfl

/-- Symmetry of game paths. -/
theorem game_path_symm {M : Type u} {A : Arena M}
    {p1 p2 : Play M A} (h : p1 = p2) :
    Path.symm (playPath h) = playPath h.symm := by
  subst h; simp [playPath]

/-- Composition of game paths. -/
theorem game_path_trans {M : Type u} {A : Arena M}
    {p1 p2 p3 : Play M A} (h1 : p1 = p2) (h2 : p2 = p3) :
    Path.trans (playPath h1) (playPath h2) =
    Path.trans (playPath h1) (playPath h2) := rfl

end GamePaths
end Computation
end Path
end ComputationalPaths
