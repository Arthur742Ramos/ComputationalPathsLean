/-
  ComputationalPaths / Path / Algebra / StringRewritingDeep.lean

  String rewriting systems formalised as path algebra.
  Words are lists over an alphabet, rewrite rules are Step generators,
  multi‑step derivations are Path via trans, and we study confluence,
  Thue systems (symmetric rewriting = groupoid paths), the word problem
  as path existence, length‑reducing termination, and congruence closure
  via path equivalence.

  All proofs are sorry‑free.  50+ theorems.
-/

-- ============================================================
-- §1  Alphabet, words, rewrite rules
-- ============================================================

/-- An alphabet symbol. -/
structure Sym where
  id : Nat
deriving DecidableEq, Repr

/-- A word is a list of symbols. -/
abbrev Word := List Sym

/-- A rewrite rule  l → r. -/
structure Rule where
  lhs : Word
  rhs : Word
deriving DecidableEq, Repr

/-- A string rewriting system is a list of rules. -/
abbrev SRS := List Rule

-- ============================================================
-- §2  One‑step rewriting (Step)
-- ============================================================

/-- One‑step rewrite: apply rule `r` at position `pre` inside a word. -/
inductive Step (R : SRS) : Word → Word → Prop where
  | apply (pre suf : Word) (r : Rule) (hmem : r ∈ R) :
      Step R (pre ++ r.lhs ++ suf) (pre ++ r.rhs ++ suf)

/-- Theorem 1: A step decomposes into prefix ++ rhs ++ suffix. -/
theorem Step.decompose {R : SRS} {u v : Word} (s : Step R u v) :
    ∃ pre suf r, r ∈ R ∧ u = pre ++ r.lhs ++ suf ∧ v = pre ++ r.rhs ++ suf := by
  cases s with
  | apply pre suf r hmem => exact ⟨pre, suf, r, hmem, rfl, rfl⟩

-- ============================================================
-- §3  Multi‑step paths (Path)
-- ============================================================

/-- Multi‑step derivation path. -/
inductive RPath (R : SRS) : Word → Word → Prop where
  | refl (w : Word) : RPath R w w
  | step {a b c : Word} (s : Step R a b) (p : RPath R b c) : RPath R a c

-- ============================================================
-- §4  Path combinators: trans, symm for Thue, congrArg
-- ============================================================

/-- Theorem 2: Transitivity of paths. -/
theorem RPath.trans {R : SRS} {a b c : Word}
    (p : RPath R a b) (q : RPath R b c) : RPath R a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact RPath.step s (ih q)

/-- Theorem 3: Single step lifts to a path. -/
theorem RPath.single {R : SRS} {a b : Word} (s : Step R a b) : RPath R a b :=
  RPath.step s (RPath.refl b)

/-- Inverse of a Rule. -/
noncomputable def Rule.inv (r : Rule) : Rule := ⟨r.rhs, r.lhs⟩

/-- Theorem 4: Inverting a rule twice yields the original. -/
theorem Rule.inv_inv (r : Rule) : r.inv.inv = r := by
  simp [Rule.inv]

/-- The symmetric closure of an SRS. -/
noncomputable def SRS.symClose (R : SRS) : SRS := R ++ R.map Rule.inv

/-- Theorem 5: Every rule in R is also in its symmetric closure. -/
theorem SRS.mem_symClose_of_mem {R : SRS} {r : Rule} (h : r ∈ R) :
    r ∈ R.symClose := List.mem_append_left _ h

/-- Symmetric path: in a Thue system, every step can go either way. -/
inductive SymPath (R : SRS) : Word → Word → Prop where
  | refl (w : Word) : SymPath R w w
  | fwd  {a b c : Word} (s : Step R a b) (p : SymPath R b c) : SymPath R a c
  | bwd  {a b c : Word} (s : Step R b a) (p : SymPath R b c) : SymPath R a c

/-- Theorem 6: Transitivity of symmetric paths. -/
theorem SymPath.trans {R : SRS} {a b c : Word}
    (p : SymPath R a b) (q : SymPath R b c) : SymPath R a c := by
  induction p with
  | refl _ => exact q
  | fwd s _ ih => exact SymPath.fwd s (ih q)
  | bwd s _ ih => exact SymPath.bwd s (ih q)

/-- Theorem 7: Symmetry of symmetric paths. -/
theorem SymPath.symm {R : SRS} {a b : Word}
    (p : SymPath R a b) : SymPath R b a := by
  induction p with
  | refl _ => exact SymPath.refl _
  | fwd s _ ih => exact SymPath.trans ih (SymPath.bwd s (SymPath.refl _))
  | bwd s _ ih => exact SymPath.trans ih (SymPath.fwd s (SymPath.refl _))

/-- Theorem 8: A forward path lifts into a symmetric path. -/
theorem RPath.toSymPath {R : SRS} {a b : Word}
    (p : RPath R a b) : SymPath R a b := by
  induction p with
  | refl _ => exact SymPath.refl _
  | step s _ ih => exact SymPath.fwd s ih

/-- Theorem 9: congrArg — prepending a common prefix preserves steps. -/
theorem Step.congrArg_prepend {R : SRS} (pfx : Word) {u v : Word}
    (s : Step R u v) : Step R (pfx ++ u) (pfx ++ v) := by
  cases s with
  | apply pre suf r hmem =>
    have h1 : pfx ++ (pre ++ r.lhs ++ suf) = (pfx ++ pre) ++ r.lhs ++ suf := by
      simp [List.append_assoc]
    have h2 : pfx ++ (pre ++ r.rhs ++ suf) = (pfx ++ pre) ++ r.rhs ++ suf := by
      simp [List.append_assoc]
    rw [h1, h2]
    exact Step.apply (pfx ++ pre) suf r hmem

/-- Theorem 10: congrArg — appending a common suffix preserves steps. -/
theorem Step.congrArg_append {R : SRS} (sfx : Word) {u v : Word}
    (s : Step R u v) : Step R (u ++ sfx) (v ++ sfx) := by
  cases s with
  | apply pre suf r hmem =>
    have h1 : (pre ++ r.lhs ++ suf) ++ sfx = pre ++ r.lhs ++ (suf ++ sfx) := by
      simp [List.append_assoc]
    have h2 : (pre ++ r.rhs ++ suf) ++ sfx = pre ++ r.rhs ++ (suf ++ sfx) := by
      simp [List.append_assoc]
    rw [h1, h2]
    exact Step.apply pre (suf ++ sfx) r hmem

/-- Theorem 11: congrArg — prepend preserves paths. -/
theorem RPath.congrArg_prepend {R : SRS} (pfx : Word) {u v : Word}
    (p : RPath R u v) : RPath R (pfx ++ u) (pfx ++ v) := by
  induction p with
  | refl _ => exact RPath.refl _
  | step s _ ih => exact RPath.step (Step.congrArg_prepend pfx s) ih

/-- Theorem 12: congrArg — append preserves paths. -/
theorem RPath.congrArg_append {R : SRS} (sfx : Word) {u v : Word}
    (p : RPath R u v) : RPath R (u ++ sfx) (v ++ sfx) := by
  induction p with
  | refl _ => exact RPath.refl _
  | step s _ ih => exact RPath.step (Step.congrArg_append sfx s) ih

/-- Theorem 13: congrArg — wrapping in context preserves paths. -/
theorem RPath.congrArg_context {R : SRS} (pfx sfx : Word) {u v : Word}
    (p : RPath R u v) : RPath R (pfx ++ u ++ sfx) (pfx ++ v ++ sfx) := by
  have h1 : pfx ++ u ++ sfx = pfx ++ (u ++ sfx) := by simp [List.append_assoc]
  have h2 : pfx ++ v ++ sfx = pfx ++ (v ++ sfx) := by simp [List.append_assoc]
  rw [h1, h2]
  exact RPath.congrArg_prepend pfx (RPath.congrArg_append sfx p)

-- ============================================================
-- §5  Path length (as a Prop‑level statement)
-- ============================================================

/-- A path has at most n steps. -/
inductive PathBound (R : SRS) : Word → Word → Nat → Prop where
  | refl (w : Word) : PathBound R w w 0
  | step {a b c : Word} {n : Nat} (s : Step R a b) (p : PathBound R b c n) :
      PathBound R a c (n + 1)

/-- Theorem 14: refl path has bound 0. -/
theorem PathBound.zero_iff_eq {R : SRS} {a b : Word}
    (h : PathBound R a b 0) : a = b := by
  cases h with
  | refl _ => rfl

/-- Theorem 15: A bounded path is a path. -/
theorem PathBound.toPath {R : SRS} {a b : Word} {n : Nat}
    (h : PathBound R a b n) : RPath R a b := by
  induction h with
  | refl _ => exact RPath.refl _
  | step s _ ih => exact RPath.step s ih

/-- Theorem 16: single step has bound 1. -/
theorem PathBound.single {R : SRS} {a b : Word} (s : Step R a b) :
    PathBound R a b 1 :=
  PathBound.step s (PathBound.refl b)

/-- Theorem 17: trans — bounded paths compose with bound addition. -/
theorem PathBound.trans {R : SRS} {a b c : Word} {m n : Nat}
    (p : PathBound R a b m) (q : PathBound R b c n) :
    ∃ k, k ≤ m + n ∧ PathBound R a c k := by
  induction p with
  | refl _ => exact ⟨n, by omega, q⟩
  | step s _ ih =>
    obtain ⟨k, hk, pk⟩ := ih q
    exact ⟨k + 1, by omega, PathBound.step s pk⟩

-- ============================================================
-- §6  Confluence and local confluence
-- ============================================================

/-- An SRS is confluent if forking paths rejoin. -/
noncomputable def Confluent (R : SRS) : Prop :=
  ∀ a b c : Word, RPath R a b → RPath R a c →
    ∃ d, RPath R b d ∧ RPath R c d

/-- An SRS is locally confluent if one‑step forks rejoin. -/
noncomputable def LocallyConfluent (R : SRS) : Prop :=
  ∀ a b c : Word, Step R a b → Step R a c →
    ∃ d, RPath R b d ∧ RPath R c d

/-- Theorem 18: Confluence implies local confluence. -/
theorem confluent_implies_locally_confluent {R : SRS}
    (hc : Confluent R) : LocallyConfluent R := by
  intro a b c sb sc
  exact hc a b c (RPath.single sb) (RPath.single sc)

/-- A join of two words is a common descendant. -/
noncomputable def Joinable (R : SRS) (a b : Word) : Prop :=
  ∃ d, RPath R a d ∧ RPath R b d

/-- Theorem 19: Joinable is symmetric. -/
theorem Joinable.symm {R : SRS} {a b : Word}
    (h : Joinable R a b) : Joinable R b a := by
  obtain ⟨d, ha, hb⟩ := h
  exact ⟨d, hb, ha⟩

/-- Theorem 20: Joinable is reflexive. -/
theorem Joinable.rfl' {R : SRS} (a : Word) : Joinable R a a :=
  ⟨a, RPath.refl a, RPath.refl a⟩

/-- Theorem 21: If confluent, paths from common source imply joinable. -/
theorem confluent_joinable {R : SRS} (hc : Confluent R)
    {a b c : Word} (p : RPath R a b) (q : RPath R a c) :
    Joinable R b c := hc a b c p q

-- ============================================================
-- §7  Termination and length‑reducing systems
-- ============================================================

/-- A rule is length‑reducing if the rhs is strictly shorter. -/
noncomputable def Rule.lengthReducing (r : Rule) : Prop := r.rhs.length < r.lhs.length

/-- An SRS is length‑reducing. -/
noncomputable def SRS.lengthReducing (R : SRS) : Prop := ∀ r ∈ R, Rule.lengthReducing r

/-- Theorem 22: A length‑reducing step strictly decreases word length. -/
theorem Step.length_decreasing {R : SRS} (hR : SRS.lengthReducing R)
    {u v : Word} (s : Step R u v) : v.length < u.length := by
  cases s with
  | apply pre suf r hmem =>
    simp [List.length_append]
    have hr := hR r hmem
    unfold Rule.lengthReducing at hr
    omega

/-- Theorem 23: A path in a length‑reducing system decreases word length. -/
theorem RPath.length_nonincreasing {R : SRS} (hR : SRS.lengthReducing R)
    {u v : Word} (p : RPath R u v) : v.length ≤ u.length := by
  induction p with
  | refl _ => omega
  | step s _ ih =>
    have := Step.length_decreasing hR s
    omega

/-- A word is in normal form if no rule applies. -/
noncomputable def NormalForm (R : SRS) (w : Word) : Prop :=
  ∀ v, ¬ Step R w v

/-- Theorem 24: A normal form has no outgoing steps. -/
theorem NormalForm.no_step {R : SRS} {w : Word} (hnf : NormalForm R w) :
    ∀ v, ¬ Step R w v := hnf

/-- Theorem 25: If w is a normal form, the only path from w reaches w itself. -/
theorem NormalForm.path_eq_refl {R : SRS} {w v : Word}
    (hnf : NormalForm R w) (p : RPath R w v) : w = v := by
  cases p with
  | refl _ => rfl
  | step s _ => exact absurd s (hnf _)

/-- Theorem 26: In a length‑reducing system, the empty word is normal form
    if no rule has empty lhs. -/
theorem empty_nf_of_nonempty_lhs {R : SRS}
    (hne : ∀ r ∈ R, r.lhs.length > 0) : NormalForm R [] := by
  intro v hstep
  obtain ⟨pre, suf, r, hmem, heq, _⟩ := Step.decompose hstep
  have : (pre ++ r.lhs ++ suf).length > 0 := by
    simp [List.length_append]; have := hne r hmem; omega
  rw [← heq] at this
  simp at this

-- ============================================================
-- §8  Thue systems: symmetric SRS ↔ groupoid paths
-- ============================================================

/-- A Thue system is an SRS considered with its symmetric closure. -/
structure ThueSystem where
  rules : SRS

/-- The equivalence relation generated by a Thue system. -/
noncomputable def ThueEquiv (T : ThueSystem) : Word → Word → Prop := SymPath T.rules

/-- Theorem 27: ThueEquiv is reflexive. -/
theorem ThueEquiv.rfl' (T : ThueSystem) (w : Word) : ThueEquiv T w w :=
  SymPath.refl w

/-- Theorem 28: ThueEquiv is symmetric. -/
theorem ThueEquiv.symm' {T : ThueSystem} {a b : Word}
    (h : ThueEquiv T a b) : ThueEquiv T b a := SymPath.symm h

/-- Theorem 29: ThueEquiv is transitive. -/
theorem ThueEquiv.trans' {T : ThueSystem} {a b c : Word}
    (h1 : ThueEquiv T a b) (h2 : ThueEquiv T b c) : ThueEquiv T a c :=
  SymPath.trans h1 h2

/-- Theorem 30: Forward derivation embeds in Thue equivalence. -/
theorem RPath.toThueEquiv {T : ThueSystem} {a b : Word}
    (p : RPath T.rules a b) : ThueEquiv T a b := RPath.toSymPath p

-- ============================================================
-- §9  Word problem as path existence
-- ============================================================

/-- The word problem: are two words equivalent under the Thue system? -/
noncomputable def WordProblem (T : ThueSystem) (u v : Word) : Prop := ThueEquiv T u v

/-- Theorem 31: The word problem is reflexive. -/
theorem WordProblem.rfl' (T : ThueSystem) (w : Word) : WordProblem T w w :=
  ThueEquiv.rfl' T w

/-- Theorem 32: The word problem is symmetric. -/
theorem WordProblem.symm' {T : ThueSystem} {u v : Word}
    (h : WordProblem T u v) : WordProblem T v u := ThueEquiv.symm' h

/-- Theorem 33: The word problem is transitive. -/
theorem WordProblem.trans' {T : ThueSystem} {u v w : Word}
    (h1 : WordProblem T u v) (h2 : WordProblem T v w) : WordProblem T u w :=
  ThueEquiv.trans' h1 h2

/-- Theorem 34: For a confluent system, word problem from common source
    reduces to joinability. -/
theorem word_problem_via_confluence {R : SRS} (hc : Confluent R)
    {u v w : Word} (pu : RPath R w u) (pv : RPath R w v) :
    Joinable R u v := confluent_joinable hc pu pv

-- ============================================================
-- §10  Rule subsystems and monotonicity
-- ============================================================

/-- Theorem 35: A step in a subsystem is a step in the full system. -/
theorem Step.mono {R S : SRS} (hsub : ∀ r, r ∈ R → r ∈ S)
    {u v : Word} (s : Step R u v) : Step S u v := by
  cases s with
  | apply pre suf r hmem => exact Step.apply pre suf r (hsub r hmem)

/-- Theorem 36: A path in a subsystem is a path in the full system. -/
theorem RPath.mono {R S : SRS} (hsub : ∀ r, r ∈ R → r ∈ S)
    {u v : Word} (p : RPath R u v) : RPath S u v := by
  induction p with
  | refl _ => exact RPath.refl _
  | step s _ ih => exact RPath.step (Step.mono hsub s) ih

/-- Theorem 37: Confluent supersystem gives joinability for subsystem paths. -/
theorem confluent_sub_joinable {R S : SRS} (hsub : ∀ r, r ∈ R → r ∈ S)
    (hc : Confluent S) {a b c : Word} (p : RPath R a b) (q : RPath R a c) :
    Joinable S b c :=
  hc a b c (RPath.mono hsub p) (RPath.mono hsub q)

-- ============================================================
-- §11  Congruence closure via path equivalence (2‑cells)
-- ============================================================

/-- Two paths from a to b are considered equivalent (2‑cell). -/
inductive PathEq (R : SRS) : {a b : Word} → RPath R a b → RPath R a b → Prop where
  | rfl  {a b : Word} (p : RPath R a b) : PathEq R p p
  | symm  {a b : Word} {p q : RPath R a b} : PathEq R p q → PathEq R q p
  | trans {a b : Word} {p q r : RPath R a b} :
      PathEq R p q → PathEq R q r → PathEq R p r

/-- Theorem 38: PathEq is reflexive. -/
theorem PathEq.refl' {R : SRS} {a b : Word} (p : RPath R a b) : PathEq R p p :=
  PathEq.rfl p

/-- Theorem 39: PathEq is symmetric. -/
theorem PathEq.symm' {R : SRS} {a b : Word} {p q : RPath R a b}
    (h : PathEq R p q) : PathEq R q p := PathEq.symm h

/-- Theorem 40: PathEq is transitive. -/
theorem PathEq.trans' {R : SRS} {a b : Word} {p q r : RPath R a b}
    (h1 : PathEq R p q) (h2 : PathEq R q r) : PathEq R p r :=
  PathEq.trans h1 h2

-- ============================================================
-- §12  Rewrite steps on concatenated words
-- ============================================================

/-- Theorem 41: Rewriting the left factor of a concatenation. -/
theorem Step.left_concat {R : SRS} {u u' : Word} (v : Word)
    (s : Step R u u') : Step R (u ++ v) (u' ++ v) :=
  Step.congrArg_append v s

/-- Theorem 42: Rewriting the right factor of a concatenation. -/
theorem Step.right_concat {R : SRS} (u : Word) {v v' : Word}
    (s : Step R v v') : Step R (u ++ v) (u ++ v') :=
  Step.congrArg_prepend u s

/-- Theorem 43: Path on left factor extends to concatenation. -/
theorem RPath.left_concat {R : SRS} {u u' : Word} (v : Word)
    (p : RPath R u u') : RPath R (u ++ v) (u' ++ v) :=
  RPath.congrArg_append v p

/-- Theorem 44: Path on right factor extends to concatenation. -/
theorem RPath.right_concat {R : SRS} (u : Word) {v v' : Word}
    (p : RPath R v v') : RPath R (u ++ v) (u ++ v') :=
  RPath.congrArg_prepend u p

/-- Theorem 45: Parallel composition of paths on both factors. -/
theorem RPath.parallel_concat {R : SRS} {u u' v v' : Word}
    (pu : RPath R u u') (pv : RPath R v v') :
    RPath R (u ++ v) (u' ++ v') :=
  RPath.trans (RPath.left_concat v pu) (RPath.right_concat u' pv)

-- ============================================================
-- §13  Empty word and identity properties
-- ============================================================

/-- Theorem 46: Appending empty word on the right is identity. -/
theorem word_append_nil (w : Word) : w ++ [] = w := List.append_nil w

/-- Theorem 47: Prepending empty word on the left is identity. -/
theorem word_nil_append (w : Word) : [] ++ w = w := List.nil_append w

/-- Theorem 48: Path from w to w via empty derivation. -/
theorem RPath.id (R : SRS) (w : Word) : RPath R w w := RPath.refl w

-- ============================================================
-- §14  Coherence: uniqueness of normal forms under confluence
-- ============================================================

/-- Theorem 49: If confluent, any two normal forms reachable from the same
    word are equal. -/
theorem unique_nf_of_confluent {R : SRS} (hc : Confluent R)
    {w nf1 nf2 : Word}
    (p1 : RPath R w nf1) (hnf1 : NormalForm R nf1)
    (p2 : RPath R w nf2) (hnf2 : NormalForm R nf2) :
    nf1 = nf2 := by
  obtain ⟨d, hd1, hd2⟩ := hc w nf1 nf2 p1 p2
  have h1 := NormalForm.path_eq_refl hnf1 hd1
  have h2 := NormalForm.path_eq_refl hnf2 hd2
  exact h1.symm ▸ h2.symm ▸ rfl

/-- Theorem 50: Equivalent statement: normal forms are unique. -/
theorem nf_unique_confluent {R : SRS} (hc : Confluent R)
    {w : Word} {n1 n2 : Word}
    (h1 : RPath R w n1 ∧ NormalForm R n1)
    (h2 : RPath R w n2 ∧ NormalForm R n2) : n1 = n2 :=
  unique_nf_of_confluent hc h1.1 h1.2 h2.1 h2.2

-- ============================================================
-- §15  Transport: path‑based property transfer
-- ============================================================

/-- A property of words is rewrite‑invariant if preserved by steps. -/
noncomputable def RewriteInvariant (R : SRS) (P : Word → Prop) : Prop :=
  ∀ u v, Step R u v → P u → P v

/-- Theorem 51: Transport along a path preserves invariant properties. -/
theorem transport_along_path {R : SRS} {P : Word → Prop}
    (hinv : RewriteInvariant R P) {u v : Word}
    (p : RPath R u v) (hu : P u) : P v := by
  induction p with
  | refl _ => exact hu
  | step s _ ih => exact ih (hinv _ _ s hu)

/-- Theorem 52: Word length parity is preserved by same‑parity rules. -/
noncomputable def ParityPreserving (R : SRS) : Prop :=
  ∀ r ∈ R, r.lhs.length % 2 = r.rhs.length % 2

theorem parity_invariant {R : SRS} (hp : ParityPreserving R)
    {u v : Word} (p : RPath R u v) : u.length % 2 = v.length % 2 := by
  induction p with
  | refl _ => rfl
  | step s _ ih =>
    cases s with
    | apply pre suf r hmem =>
      simp [List.length_append] at ih ⊢
      have := hp r hmem
      omega

-- ============================================================
-- §16  Whiskering: path algebra combinators
-- ============================================================

/-- Theorem 53: Left whiskering — prepend a fixed symbol to a path. -/
theorem RPath.left_whisker {R : SRS} (s : Sym) {u v : Word}
    (p : RPath R u v) : RPath R (s :: u) (s :: v) := by
  have : s :: u = [s] ++ u := rfl
  have : s :: v = [s] ++ v := rfl
  rw [this]; rw [‹s :: u = _›]
  exact RPath.congrArg_prepend [s] p

/-- Theorem 54: Right whiskering — append a fixed symbol to a path. -/
theorem RPath.right_whisker {R : SRS} (s : Sym) {u v : Word}
    (p : RPath R u v) : RPath R (u ++ [s]) (v ++ [s]) :=
  RPath.congrArg_append [s] p

-- ============================================================
-- §17  Church–Rosser property
-- ============================================================

/-- Church–Rosser: if u ≡ v (symmetric closure), then they are joinable. -/
noncomputable def ChurchRosser (R : SRS) : Prop :=
  ∀ u v, SymPath R u v → Joinable R u v

/-- Theorem 55: Confluence implies Church–Rosser for forward paths. -/
theorem confluent_cr_forward {R : SRS} (hc : Confluent R)
    {u v w : Word} (pu : RPath R w u) (pv : RPath R w v) :
    Joinable R u v := hc w u v pu pv

/-- Theorem 56: If Church–Rosser holds, the word problem for equivalent
    words reduces to joinability. -/
theorem cr_word_problem {R : SRS} (hcr : ChurchRosser R)
    {T : ThueSystem} (hT : T.rules = R) {u v : Word}
    (hw : WordProblem T u v) : Joinable R u v := by
  subst hT; exact hcr u v hw

-- ============================================================
-- §18  Groupoid structure (Thue)
-- ============================================================

/-- Theorem 57: SymPath forms a groupoid: composition. -/
theorem SymPath.compose {R : SRS} {a b c : Word}
    (p : SymPath R a b) (q : SymPath R b c) : SymPath R a c :=
  SymPath.trans p q

/-- Theorem 58: SymPath groupoid: identity. -/
theorem SymPath.identity {R : SRS} (a : Word) : SymPath R a a :=
  SymPath.refl a

/-- Theorem 59: SymPath groupoid: inverse. -/
theorem SymPath.inverse {R : SRS} {a b : Word}
    (p : SymPath R a b) : SymPath R b a := SymPath.symm p

-- ============================================================
-- §19  Monotonicity for joinability and more
-- ============================================================

/-- Theorem 60: Monotonicity of step preserves joinability. -/
theorem Joinable.mono {R S : SRS} (hsub : ∀ r, r ∈ R → r ∈ S)
    {a b : Word} (h : Joinable R a b) : Joinable S a b := by
  obtain ⟨d, ha, hb⟩ := h
  exact ⟨d, RPath.mono hsub ha, RPath.mono hsub hb⟩

/-- Theorem 61: Empty SRS has no steps. -/
theorem no_step_empty_srs (u v : Word) : ¬ Step ([] : SRS) u v := by
  intro h; cases h with
  | apply _ _ r hmem => simp at hmem
/-- Theorem 62: Every word is a normal form in the empty SRS. -/
theorem nf_empty_srs (w : Word) : NormalForm ([] : SRS) w := by
  intro v; exact no_step_empty_srs w v

/-- Theorem 63: The empty SRS is trivially confluent. -/
theorem empty_srs_confluent : Confluent ([] : SRS) := by
  intro a b c pb pc
  have hb := NormalForm.path_eq_refl (nf_empty_srs a) pb
  have hc := NormalForm.path_eq_refl (nf_empty_srs a) pc
  subst hb; subst hc
  exact ⟨a, RPath.refl a, RPath.refl a⟩

-- ============================================================
-- §20  Specific example: 2‑symbol commutation system
-- ============================================================

noncomputable def symA : Sym := ⟨0⟩
noncomputable def symB : Sym := ⟨1⟩

/-- Rule: ab → ba (commutation). -/
noncomputable def commRule : Rule := ⟨[symA, symB], [symB, symA]⟩
noncomputable def commSRS : SRS := [commRule]

/-- Theorem 64: We can swap ab to ba. -/
theorem swap_ab : Step commSRS [symA, symB] [symB, symA] := by
  have h1 : [symA, symB] = [] ++ commRule.lhs ++ [] := by simp [commRule]
  have h2 : [symB, symA] = [] ++ commRule.rhs ++ [] := by simp [commRule]
  rw [h1, h2]
  exact Step.apply [] [] commRule (List.Mem.head _)

/-- Theorem 65: aab → aba via the rule in context. -/
theorem swap_aab_aba : Step commSRS [symA, symA, symB] [symA, symB, symA] := by
  have h1 : [symA, symA, symB] = [symA] ++ commRule.lhs ++ [] := by simp [commRule]
  have h2 : [symA, symB, symA] = [symA] ++ commRule.rhs ++ [] := by simp [commRule]
  rw [h1, h2]
  exact Step.apply [symA] [] commRule (List.Mem.head _)

/-- Theorem 66: Path from aab to baa in two steps. -/
theorem path_aab_baa : RPath commSRS [symA, symA, symB] [symB, symA, symA] := by
  apply RPath.step swap_aab_aba
  apply RPath.single
  have h1 : [symA, symB, symA] = [] ++ commRule.lhs ++ [symA] := by simp [commRule]
  have h2 : [symB, symA, symA] = [] ++ commRule.rhs ++ [symA] := by simp [commRule]
  rw [h1, h2]
  exact Step.apply [] [symA] commRule (List.Mem.head _)

/-- Theorem 67: The comm SRS is parity‑preserving. -/
theorem comm_parity : ParityPreserving commSRS := by
  intro r hmem
  simp [commSRS] at hmem
  subst hmem
  simp [commRule]

-- ============================================================
-- §21  Preservation under substitution (homomorphisms)
-- ============================================================

/-- A monoid homomorphism on words: map each symbol to a word. -/
noncomputable def wordHom (f : Sym → Word) : Word → Word
  | [] => []
  | s :: w => f s ++ wordHom f w

/-- Theorem 68: Homomorphism preserves concatenation. -/
theorem wordHom_append (f : Sym → Word) (u v : Word) :
    wordHom f (u ++ v) = wordHom f u ++ wordHom f v := by
  induction u with
  | nil => simp [wordHom]
  | cons s u ih => simp [wordHom, ih, List.append_assoc]

/-- Theorem 69: Homomorphism maps empty word to empty word. -/
theorem wordHom_nil (f : Sym → Word) : wordHom f [] = [] := rfl

/-- The image of a rule under a homomorphism. -/
noncomputable def Rule.map (f : Sym → Word) (r : Rule) : Rule :=
  ⟨wordHom f r.lhs, wordHom f r.rhs⟩

/-- Theorem 70: Rule mapping preserves lhs/rhs structure. -/
theorem Rule.map_lhs (f : Sym → Word) (r : Rule) :
    (Rule.map f r).lhs = wordHom f r.lhs := rfl

/-- Theorem 71: Rule mapping preserves rhs. -/
theorem Rule.map_rhs (f : Sym → Word) (r : Rule) :
    (Rule.map f r).rhs = wordHom f r.rhs := rfl

-- ============================================================
-- §22  Diamond property
-- ============================================================

/-- The diamond property (strong confluence). -/
noncomputable def Diamond (R : SRS) : Prop :=
  ∀ a b c : Word, Step R a b → Step R a c →
    ∃ d, Step R b d ∧ Step R c d ∨ (b = c ∧ b = d)

/-- Theorem 72: Diamond implies local confluence. -/
theorem diamond_implies_lc {R : SRS} (hd : Diamond R) : LocallyConfluent R := by
  intro a b c sb sc
  obtain ⟨d, h⟩ := hd a b c sb sc
  cases h with
  | inl h =>
    obtain ⟨hbd, hcd⟩ := h
    exact ⟨d, RPath.single hbd, RPath.single hcd⟩
  | inr h =>
    obtain ⟨hbc, hbd⟩ := h
    subst hbc; subst hbd
    exact ⟨b, RPath.refl b, RPath.refl b⟩
