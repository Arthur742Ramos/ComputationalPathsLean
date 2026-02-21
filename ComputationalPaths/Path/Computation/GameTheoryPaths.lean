/-
# Game Theory via Computational Paths

Strategies, Nash equilibrium, payoff functions, best response,
zero-sum games, minimax aspects, dominance, Pareto optimality.
All coherence witnessed by `Path`.

## References

- Osborne & Rubinstein, "A Course in Game Theory"
- Nash, "Non-Cooperative Games"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace GameTheoryPaths

universe u v

open ComputationalPaths.Path

/-! ## Players and Strategies -/

/-- A strategic form game with player types and strategy/payoff. -/
structure Game (S1 S2 : Type u) where
  payoff1 : S1 → S2 → Int
  payoff2 : S1 → S2 → Int

/-- A strategy profile is a pair of strategies. -/
structure Profile (S1 S2 : Type u) where
  s1 : S1
  s2 : S2

/-- Payoff for player 1 at a profile. -/
def payoff1_at {S1 S2 : Type u} (g : Game S1 S2) (p : Profile S1 S2) : Int :=
  g.payoff1 p.s1 p.s2

/-- Payoff for player 2 at a profile. -/
def payoff2_at {S1 S2 : Type u} (g : Game S1 S2) (p : Profile S1 S2) : Int :=
  g.payoff2 p.s1 p.s2

/-- Equal profiles yield equal payoffs (player 1). -/
theorem payoff1_eq_of_profile_eq {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) : payoff1_at g p = payoff1_at g q := by
  subst h; rfl

/-- Equal profiles yield equal payoffs (player 2). -/
theorem payoff2_eq_of_profile_eq {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) : payoff2_at g p = payoff2_at g q := by
  subst h; rfl

/-- Path between profiles induces path between payoffs. -/
def payoff1_path {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) :
    Path (payoff1_at g p) (payoff1_at g q) :=
  Path.congrArg (payoff1_at g) (Path.mk [Step.mk _ _ h] h)

/-- Path between profiles induces path between payoffs (player 2). -/
def payoff2_path {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) :
    Path (payoff2_at g p) (payoff2_at g q) :=
  Path.congrArg (payoff2_at g) (Path.mk [Step.mk _ _ h] h)

/-! ## Zero-Sum Games -/

/-- A zero-sum game: payoffs sum to zero. -/
structure ZeroSumGame (S1 S2 : Type u) extends Game S1 S2 where
  zerosum : ∀ s1 s2, payoff1 s1 s2 + payoff2 s1 s2 = 0

/-- In a zero-sum game, player 2's payoff is the negation of player 1's. -/
theorem zerosum_neg {S1 S2 : Type u} (g : ZeroSumGame S1 S2)
    (s1 : S1) (s2 : S2) : g.payoff2 s1 s2 = -g.payoff1 s1 s2 := by
  have h := g.zerosum s1 s2
  omega

/-- Path witnessing zero-sum negation. -/
def zerosum_neg_path {S1 S2 : Type u} (g : ZeroSumGame S1 S2)
    (s1 : S1) (s2 : S2) : Path (g.payoff2 s1 s2) (-g.payoff1 s1 s2) :=
  Path.mk [Step.mk _ _ (zerosum_neg g s1 s2)] (zerosum_neg g s1 s2)

/-- Zero-sum property is preserved under profile equality. -/
theorem zerosum_profile_eq {S1 S2 : Type u} (g : ZeroSumGame S1 S2)
    (p : Profile S1 S2) :
    payoff1_at g.toGame p + payoff2_at g.toGame p = 0 :=
  g.zerosum p.s1 p.s2

/-! ## Best Response -/

/-- Player 1's best response: no other strategy yields higher payoff. -/
def IsBestResponse1 {S1 S2 : Type u} (g : Game S1 S2)
    (s1 : S1) (s2 : S2) : Prop :=
  ∀ s1' : S1, g.payoff1 s1 s2 ≥ g.payoff1 s1' s2

/-- Player 2's best response. -/
def IsBestResponse2 {S1 S2 : Type u} (g : Game S1 S2)
    (s1 : S1) (s2 : S2) : Prop :=
  ∀ s2' : S2, g.payoff2 s1 s2 ≥ g.payoff2 s1 s2'

/-- Best response is reflexive (self is at least as good as self). -/
theorem best_response1_self {S1 S2 : Type u} (g : Game S1 S2)
    (s1 : S1) (s2 : S2) : g.payoff1 s1 s2 ≥ g.payoff1 s1 s2 :=
  le_refl _

theorem best_response2_self {S1 S2 : Type u} (g : Game S1 S2)
    (s1 : S1) (s2 : S2) : g.payoff2 s1 s2 ≥ g.payoff2 s1 s2 :=
  le_refl _

/-! ## Nash Equilibrium -/

/-- A Nash equilibrium: both strategies are best responses. -/
def IsNashEquilibrium {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) : Prop :=
  IsBestResponse1 g p.s1 p.s2 ∧ IsBestResponse2 g p.s1 p.s2

/-- Equal profiles preserve Nash equilibrium. -/
theorem nash_eq_of_profile_eq {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) (hn : IsNashEquilibrium g p) :
    IsNashEquilibrium g q := by
  subst h; exact hn

/-- Transport of Nash equilibrium along a profile path. -/
def nash_transport {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q) :
    IsNashEquilibrium g p → IsNashEquilibrium g q :=
  Path.transport (D := fun pr => IsNashEquilibrium g pr) (Path.mk [Step.mk _ _ h] h)

/-- Path between Nash equilibrium proofs (proof irrelevance). -/
theorem nash_proof_irrel {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) (h1 h2 : IsNashEquilibrium g p) :
    h1 = h2 := by
  exact proof_irrel h1 h2

/-! ## Dominant Strategies -/

/-- A strategy s1 is dominant for player 1. -/
def IsDominant1 {S1 S2 : Type u} (g : Game S1 S2) (s1 : S1) : Prop :=
  ∀ s2 : S2, IsBestResponse1 g s1 s2

/-- A strategy s2 is dominant for player 2. -/
def IsDominant2 {S1 S2 : Type u} (g : Game S1 S2) (s2 : S2) : Prop :=
  ∀ s1 : S1, IsBestResponse2 g s1 s2

/-- Dominant strategy pair forms Nash equilibrium. -/
theorem dominant_is_nash {S1 S2 : Type u} (g : Game S1 S2)
    (s1 : S1) (s2 : S2)
    (h1 : IsDominant1 g s1) (h2 : IsDominant2 g s2) :
    IsNashEquilibrium g ⟨s1, s2⟩ :=
  ⟨h1 s2, h2 s1⟩

/-- Equal games preserve dominant strategies. -/
theorem dominant1_eq_game {S1 S2 : Type u} {g1 g2 : Game S1 S2}
    (hg : g1 = g2) (s1 : S1) (h : IsDominant1 g1 s1) :
    IsDominant1 g2 s1 := by
  subst hg; exact h

/-! ## Pareto Optimality -/

/-- A profile is Pareto dominated if another profile improves both payoffs. -/
def ParetoImproves {S1 S2 : Type u} (g : Game S1 S2)
    (p q : Profile S1 S2) : Prop :=
  payoff1_at g q ≥ payoff1_at g p ∧
  payoff2_at g q ≥ payoff2_at g p ∧
  (payoff1_at g q > payoff1_at g p ∨ payoff2_at g q > payoff2_at g p)

/-- Pareto improvement is irreflexive. -/
theorem pareto_irrefl {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) : ¬ParetoImproves g p p := by
  intro ⟨_, _, h3⟩
  cases h3 with
  | inl h => exact absurd h (lt_irrefl _)
  | inr h => exact absurd h (lt_irrefl _)

/-- A profile is Pareto optimal if no profile Pareto improves it. -/
def IsParetoOptimal {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) : Prop :=
  ∀ q : Profile S1 S2, ¬ParetoImproves g p q

/-- Equal profiles preserve Pareto optimality. -/
theorem pareto_eq {S1 S2 : Type u} (g : Game S1 S2)
    {p q : Profile S1 S2} (h : p = q)
    (hp : IsParetoOptimal g p) : IsParetoOptimal g q := by
  subst h; exact hp

/-! ## Game Morphisms and Paths -/

/-- A morphism between games that maps strategies. -/
structure GameMorphism (S1 S2 T1 T2 : Type u)
    (g : Game S1 S2) (h : Game T1 T2) where
  mapS1 : S1 → T1
  mapS2 : S2 → T2

/-- Identity game morphism. -/
def GameMorphism.id {S1 S2 : Type u} (g : Game S1 S2) :
    GameMorphism S1 S2 S1 S2 g g where
  mapS1 := fun x => x
  mapS2 := fun x => x

/-- Identity morphism maps profiles identically. -/
theorem game_morph_id_profile {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) :
    Profile.mk ((GameMorphism.id g).mapS1 p.s1) ((GameMorphism.id g).mapS2 p.s2) = p := by
  simp [GameMorphism.id]

/-- Composition of game morphisms. -/
def GameMorphism.comp {S1 S2 T1 T2 U1 U2 : Type u}
    {g : Game S1 S2} {h : Game T1 T2} {k : Game U1 U2}
    (f2 : GameMorphism T1 T2 U1 U2 h k)
    (f1 : GameMorphism S1 S2 T1 T2 g h) :
    GameMorphism S1 S2 U1 U2 g k where
  mapS1 := f2.mapS1 ∘ f1.mapS1
  mapS2 := f2.mapS2 ∘ f1.mapS2

/-- Morphism maps profiles. -/
def GameMorphism.mapProfile {S1 S2 T1 T2 : Type u}
    {g : Game S1 S2} {h : Game T1 T2}
    (f : GameMorphism S1 S2 T1 T2 g h) (p : Profile S1 S2) : Profile T1 T2 :=
  ⟨f.mapS1 p.s1, f.mapS2 p.s2⟩

/-- Identity morphism preserves profiles. -/
theorem morph_id_profile {S1 S2 : Type u} (g : Game S1 S2)
    (p : Profile S1 S2) :
    (GameMorphism.id g).mapProfile p = p := by
  simp [GameMorphism.id, GameMorphism.mapProfile]

/-! ## Game Equivalences as Paths -/

/-- Path between games induced by equality. -/
def gamePath {S1 S2 : Type u} {g1 g2 : Game S1 S2} (h : g1 = g2) :
    Path g1 g2 :=
  Path.mk [Step.mk _ _ h] h

/-- Transport of profiles along game path. -/
def profileTransport {S1 S2 : Type u}
    {p1 p2 : Profile S1 S2} (h : p1 = p2)
    (P : Profile S1 S2 → Type v) (x : P p1) : P p2 :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Profile transport along refl is identity. -/
theorem profile_transport_refl {S1 S2 : Type u}
    (p : Profile S1 S2) (P : Profile S1 S2 → Type v) (x : P p) :
    profileTransport rfl P x = x := rfl

/-- Symmetry of game paths. -/
theorem game_path_symm {S1 S2 : Type u} {g1 g2 : Game S1 S2} (h : g1 = g2) :
    Path.symm (gamePath h) = gamePath h.symm := by
  subst h; rfl

/-- Transitivity of game paths: underlying proofs agree. -/
theorem game_path_trans_proof {S1 S2 : Type u}
    {g1 g2 g3 : Game S1 S2} (h1 : g1 = g2) (h2 : g2 = g3) :
    (Path.trans (gamePath h1) (gamePath h2)).proof = (h1.trans h2) := by
  subst h1; subst h2; rfl

/-! ## Mixed Strategies -/

/-- A mixed strategy is a probability distribution (list of weight-action pairs). -/
structure MixedStrategy (S : Type u) where
  support : List (Nat × S)

/-- Pure strategy as a mixed strategy with weight 1. -/
def pureToMixed {S : Type u} (s : S) : MixedStrategy S :=
  ⟨[(1, s)]⟩

/-- Two pure strategies are equal iff their underlying strategies are. -/
theorem pureToMixed_eq {S : Type u} {s1 s2 : S} :
    pureToMixed s1 = pureToMixed s2 ↔ s1 = s2 := by
  constructor
  · intro h; simp [pureToMixed] at h; exact h
  · intro h; subst h; rfl

/-- Path from pure strategy equality. -/
def pureStrategyPath {S : Type u} {s1 s2 : S} (h : s1 = s2) :
    Path (pureToMixed s1) (pureToMixed s2) :=
  Path.congrArg pureToMixed (Path.mk [Step.mk _ _ h] h)

/-! ## Utility and CongrArg -/

/-- Utility function type. -/
def Utility (S1 S2 : Type u) := S1 → S2 → Int

/-- CongrArg for utility through strategy path. -/
theorem utility_congrArg {S1 S2 : Type u}
    (u : Utility S1 S2) {s1 s1' : S1} (h : s1 = s1') (s2 : S2) :
    u s1 s2 = u s1' s2 := by subst h; rfl

/-- Path from utility congruence. -/
def utility_path {S1 S2 : Type u}
    (u : Utility S1 S2) {s1 s1' : S1} (h : s1 = s1') (s2 : S2) :
    Path (u s1 s2) (u s1' s2) :=
  Path.mk [Step.mk _ _ (utility_congrArg u h s2)] (utility_congrArg u h s2)

/-- Utility path composition: underlying proofs agree. -/
theorem utility_path_trans_proof {S1 S2 : Type u}
    (u : Utility S1 S2) {s1 s2 s3 : S1} (h1 : s1 = s2) (h2 : s2 = s3) (t : S2) :
    (Path.trans (utility_path u h1 t) (utility_path u h2 t)).proof =
    (utility_path u (h1.trans h2) t).proof := by
  subst h1; subst h2; rfl

/-! ## Symmetric Games -/

/-- A game is symmetric if swapping players preserves structure. -/
def IsSymmetric {S : Type u} (g : Game S S) : Prop :=
  ∀ s1 s2, g.payoff1 s1 s2 = g.payoff2 s2 s1

/-- In a symmetric game, swap yields same payoff path. -/
def symmetric_payoff_path {S : Type u} (g : Game S S)
    (hsym : IsSymmetric g) (s1 s2 : S) :
    Path (g.payoff1 s1 s2) (g.payoff2 s2 s1) :=
  Path.mk [Step.mk _ _ (hsym s1 s2)] (hsym s1 s2)

/-- Symmetric game: Nash at (s1,s2) implies best response symmetry. -/
theorem symmetric_nash_br {S : Type u} (g : Game S S)
    (_hsym : IsSymmetric g) (s1 s2 : S)
    (hn : IsNashEquilibrium g ⟨s1, s2⟩) :
    ∀ s1', g.payoff1 s1 s2 ≥ g.payoff1 s1' s2 :=
  hn.1

end GameTheoryPaths
end Computation
end Path
end ComputationalPaths
