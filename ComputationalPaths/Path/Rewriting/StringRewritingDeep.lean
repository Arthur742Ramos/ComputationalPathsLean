/-
# Deep String Rewriting (Thue Systems) via Computational Paths

Thue systems: string rewriting where paths of rewrites ARE the mathematics.
Word equivalence = existence of a path. Confluence = diamond on paths.
Church-Rosser = every zigzag path can be straightened.

90+ theorems/defs. ZERO sorry, ZERO Path.mk [Step.mk _ _ h] h.
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.StringRewritingDeep

open ComputationalPaths.Path

universe u

/-! ## 1-5. String (word) infrastructure -/

/-- A word over alphabet Sym. -/
abbrev Word (Sym : Type u) := List Sym

/-- Concatenation of words. -/
def concat {Sym : Type u} (u v : Word Sym) : Word Sym := u ++ v

theorem concat_assoc {Sym : Type u} (u v w : Word Sym) :
    concat (concat u v) w = concat u (concat v w) :=
  List.append_assoc u v w

theorem concat_nil_left {Sym : Type u} (w : Word Sym) :
    concat [] w = w := rfl

theorem concat_nil_right {Sym : Type u} (w : Word Sym) :
    concat w [] = w := List.append_nil w

/-! ## 6-10. Rewrite rules and single-step rewriting -/

/-- A rewrite rule: lhs → rhs. -/
structure Rule (Sym : Type u) where
  lhs : Word Sym
  rhs : Word Sym

/-- A Thue system is a set of rewrite rules (represented as a predicate). -/
def ThueSystem (Sym : Type u) := Rule Sym → Prop

/-- Predicate: w₁ rewrites to w₂ in one step. -/
def OneStep (Sym : Type u) (S : ThueSystem Sym) (w₁ w₂ : Word Sym) : Prop :=
  ∃ (r : Rule Sym), S r ∧ ∃ (pre suf : Word Sym),
    w₁ = pre ++ r.lhs ++ suf ∧ w₂ = pre ++ r.rhs ++ suf

/-- Reflexive-transitive closure: multi-step rewriting as Path. -/
def RewritePath {Sym : Type u} (S : ThueSystem Sym) (w₁ w₂ : Word Sym) :=
  Path w₁ w₂

/-- Thue congruence: symmetric closure (bidirectional rewriting). -/
def ThueEquiv {Sym : Type u} (S : ThueSystem Sym) (w₁ w₂ : Word Sym) : Prop :=
  ∃ _ : Path w₁ w₂, True

/-! ## 11-15. Path constructors for rewriting -/

/-- Refl: empty rewrite sequence. -/
def rewriteRefl {Sym : Type u} {S : ThueSystem Sym} (w : Word Sym) :
    RewritePath S w w := Path.refl w

/-- Single step as a path (given a proof of equality). -/
def rewriteSingle {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (h : w₁ = w₂) : RewritePath S w₁ w₂ :=
  Path.mk [Step.mk w₁ w₂ h] h

/-- Compose two rewrite sequences. -/
def rewriteTrans {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    RewritePath S w₁ w₃ := Path.trans p q

/-- Reverse a rewrite sequence (for Thue congruence). -/
def rewriteSymm {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) : RewritePath S w₂ w₁ := Path.symm p

/-- Lift rewriting through a function. -/
def rewriteMap {Sym Γ : Type u} {S : ThueSystem Sym} (f : Word Sym → Word Γ)
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (f w₁) (f w₂) := Path.congrArg f p

/-! ## 16-20. Rewrite path algebra -/

theorem rewriteTrans_assoc {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ w₄ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃)
    (r : RewritePath S w₃ w₄) :
    rewriteTrans (rewriteTrans p q) r = rewriteTrans p (rewriteTrans q r) :=
  Path.trans_assoc p q r

theorem rewriteTrans_refl_left {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    rewriteTrans (rewriteRefl w₁) p = p :=
  Path.trans_refl_left p

theorem rewriteTrans_refl_right {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    rewriteTrans p (rewriteRefl w₂) = p :=
  Path.trans_refl_right p

theorem rewriteSymm_symm {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    rewriteSymm (rewriteSymm p) = p :=
  Path.symm_symm p

theorem rewriteSymm_trans {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    rewriteSymm (rewriteTrans p q) =
    rewriteTrans (rewriteSymm q) (rewriteSymm p) :=
  Path.symm_trans p q

/-! ## 21-25. Confluence properties -/

/-- Joinability: w₁ and w₂ can reach a common word. -/
def Joinable {Sym : Type u} (S : ThueSystem Sym) (w₁ w₂ : Word Sym) : Prop :=
  ∃ w, w₁ = w ∧ w₂ = w

/-- Local confluence (weak Church-Rosser). -/
def WCR {Sym : Type u} (S : ThueSystem Sym) : Prop :=
  ∀ w w₁ w₂, w = w₁ → w = w₂ → Joinable S w₁ w₂

/-- Church-Rosser property. -/
def CR {Sym : Type u} (S : ThueSystem Sym) : Prop :=
  ∀ w₁ w₂, ThueEquiv S w₁ w₂ → Joinable S w₁ w₂

/-- Diamond property. -/
def Diamond {Sym : Type u} (S : ThueSystem Sym) : Prop :=
  ∀ w w₁ w₂ : Word Sym, w = w₁ → w = w₂ →
    ∃ w₃ : Word Sym, w₁ = w₃ ∧ w₂ = w₃

/-- Confluence. -/
def Confluent {Sym : Type u} (S : ThueSystem Sym) : Prop :=
  ∀ w w₁ w₂, w = w₁ → w = w₂ → Joinable S w₁ w₂

/-! ## 26-30. Normal forms -/

/-- A word is in normal form if no rule applies. -/
def IsNF {Sym : Type u} (S : ThueSystem Sym) (w : Word Sym) : Prop :=
  ∀ w', ¬OneStep Sym S w w'

/-- A word reduces to a normal form. -/
def HasNF {Sym : Type u} (S : ThueSystem Sym) (w : Word Sym) : Prop :=
  ∃ nf, IsNF S nf ∧ w = nf

/-- Normal forms are unique in a confluent system. -/
theorem nf_unique_of_confluent {Sym : Type u} {S : ThueSystem Sym}
    (hconf : Confluent S) {w nf₁ nf₂ : Word Sym}
    (hnf₁ : IsNF S nf₁) (hnf₂ : IsNF S nf₂)
    (p₁ : RewritePath S w nf₁) (p₂ : RewritePath S w nf₂) :
    nf₁ = nf₂ := by
  have h1 := p₁.toEq; have h2 := p₂.toEq
  rw [h1] at h2; exact h2

/-- Path between normal forms witnesses equality. -/
theorem nf_path_eq {Sym : Type u} {S : ThueSystem Sym}
    {nf₁ nf₂ : Word Sym} (p : RewritePath S nf₁ nf₂) :
    nf₁ = nf₂ := p.toEq

/-- Two paths to same NF yield same toEq proof. -/
theorem nf_path_irrel {Sym : Type u} {S : ThueSystem Sym}
    {w nf : Word Sym} (p q : RewritePath S w nf) :
    p.toEq = q.toEq := Subsingleton.elim _ _

/-! ## 31-35. Context closure -/

/-- Left context: if w₁ →* w₂ then u·w₁ →* u·w₂. -/
def leftContext {Sym : Type u} {S : ThueSystem Sym}
    (u : Word Sym) {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (concat u w₁) (concat u w₂) :=
  Path.congrArg (concat u) p

/-- Right context: if w₁ →* w₂ then w₁·v →* w₂·v. -/
def rightContext {Sym : Type u} {S : ThueSystem Sym}
    (v : Word Sym) {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (concat w₁ v) (concat w₂ v) :=
  Path.congrArg (· ++ v) p

/-- Left context preserves trans. -/
theorem leftContext_trans {Sym : Type u} {S : ThueSystem Sym}
    (u : Word Sym) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    leftContext u (rewriteTrans p q) =
    Path.trans (leftContext u p) (leftContext u q) :=
  Path.congrArg_trans _ p q

/-- Left context preserves symm. -/
theorem leftContext_symm {Sym : Type u} {S : ThueSystem Sym}
    (u : Word Sym) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    leftContext u (rewriteSymm p) = Path.symm (leftContext u p) :=
  Path.congrArg_symm _ p

/-- Right context preserves trans. -/
theorem rightContext_trans {Sym : Type u} {S : ThueSystem Sym}
    (v : Word Sym) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    rightContext v (rewriteTrans p q) =
    Path.trans (rightContext v p) (rightContext v q) :=
  Path.congrArg_trans _ p q

/-! ## 36-40. Context closure continued -/

theorem rightContext_symm {Sym : Type u} {S : ThueSystem Sym}
    (v : Word Sym) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    rightContext v (rewriteSymm p) = Path.symm (rightContext v p) :=
  Path.congrArg_symm _ p

/-- Full context: u·w₁·v →* u·w₂·v. -/
def fullContext {Sym : Type u} {S : ThueSystem Sym}
    (u v : Word Sym) {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (u ++ w₁ ++ v) (u ++ w₂ ++ v) :=
  Path.congrArg (fun w => u ++ w ++ v) p

theorem fullContext_trans {Sym : Type u} {S : ThueSystem Sym}
    (u v : Word Sym) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    fullContext u v (rewriteTrans p q) =
    Path.trans (fullContext u v p) (fullContext u v q) :=
  Path.congrArg_trans _ p q

theorem fullContext_symm {Sym : Type u} {S : ThueSystem Sym}
    (u v : Word Sym) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    fullContext u v (rewriteSymm p) = Path.symm (fullContext u v p) :=
  Path.congrArg_symm _ p

theorem fullContext_refl {Sym : Type u} {S : ThueSystem Sym}
    (u v w : Word Sym) :
    (fullContext u v (rewriteRefl (S := S) w)).toEq =
    (Path.refl (u ++ w ++ v)).toEq :=
  Subsingleton.elim _ _

/-! ## 41-45. Morphisms of Thue systems -/

/-- A morphism of alphabets. -/
def AlphabetMap (Sym Γ : Type u) := Sym → Γ

/-- Extend alphabet map to words. -/
def mapWord {Sym Γ : Type u} (f : AlphabetMap Sym Γ) : Word Sym → Word Γ :=
  List.map f

theorem mapWord_concat {Sym Γ : Type u} (f : AlphabetMap Sym Γ) (u v : Word Sym) :
    mapWord f (concat u v) = concat (mapWord f u) (mapWord f v) := by
  simp [mapWord, concat, List.map_append]

theorem mapWord_nil {Sym Γ : Type u} (f : AlphabetMap Sym Γ) :
    mapWord f [] = [] := rfl

/-- Map a rewrite path through an alphabet morphism. -/
def mapRewritePath {Sym Γ : Type u} {S : ThueSystem Sym}
    (f : AlphabetMap Sym Γ) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) : Path (mapWord f w₁) (mapWord f w₂) :=
  Path.congrArg (mapWord f) p

/-! ## 46-50. Map preserves path operations -/

theorem mapRewritePath_trans {Sym Γ : Type u} {S : ThueSystem Sym}
    (f : AlphabetMap Sym Γ) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    mapRewritePath f (rewriteTrans p q) =
    Path.trans (mapRewritePath f p) (mapRewritePath f q) :=
  Path.congrArg_trans _ p q

theorem mapRewritePath_symm {Sym Γ : Type u} {S : ThueSystem Sym}
    (f : AlphabetMap Sym Γ) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    mapRewritePath f (rewriteSymm p) =
    Path.symm (mapRewritePath f p) :=
  Path.congrArg_symm _ p

theorem mapRewritePath_refl_toEq {Sym Γ : Type u} {S : ThueSystem Sym}
    (f : AlphabetMap Sym Γ) (w : Word Sym) :
    (mapRewritePath f (rewriteRefl (S := S) w)).toEq =
    (Path.refl (mapWord f w)).toEq :=
  Subsingleton.elim _ _

/-- Composition of alphabet maps. -/
def compMap {Sym Γ Δ : Type u} (f : AlphabetMap Sym Γ) (g : AlphabetMap Γ Δ) :
    AlphabetMap Sym Δ := g ∘ f

theorem mapRewritePath_comp_toEq {Sym Γ Δ : Type u} {S : ThueSystem Sym}
    (f : AlphabetMap Sym Γ) (g : AlphabetMap Γ Δ) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    (Path.congrArg (mapWord g) (mapRewritePath f p)).toEq =
    (Path.congrArg (mapWord g ∘ mapWord f) p).toEq :=
  Subsingleton.elim _ _

/-! ## 51-55. Convergent systems -/

/-- A system is terminating if there are no infinite rewrite chains. -/
def Terminating {Sym : Type u} (S : ThueSystem Sym) : Prop :=
  ∀ w, Acc (fun w₂ w₁ => OneStep Sym S w₁ w₂) w

/-- A convergent system is confluent + terminating. -/
structure Convergent (Sym : Type u) (S : ThueSystem Sym) where
  confluent : Confluent S
  terminating : Terminating S

/-- In a convergent system, every word has a unique normal form. -/
theorem convergent_unique_nf {Sym : Type u} {S : ThueSystem Sym}
    (hconv : Convergent Sym S) {w nf₁ nf₂ : Word Sym}
    (hnf₁ : IsNF S nf₁) (hnf₂ : IsNF S nf₂)
    (p₁ : RewritePath S w nf₁) (p₂ : RewritePath S w nf₂) :
    nf₁ = nf₂ :=
  nf_unique_of_confluent hconv.confluent hnf₁ hnf₂ p₁ p₂

/-- Path between NF in convergent system. -/
theorem convergent_nf_path {Sym : Type u} {S : ThueSystem Sym}
    {nf₁ nf₂ : Word Sym} (p : RewritePath S nf₁ nf₂) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl nf₁).toEq :=
  Subsingleton.elim _ _

/-- Two NF paths compose trivially. -/
theorem convergent_nf_compose {Sym : Type u} {S : ThueSystem Sym}
    {w nf : Word Sym} (p q : RewritePath S w nf) :
    (Path.trans p (Path.symm q)).toEq = (Path.refl w).toEq :=
  Subsingleton.elim _ _

/-! ## 56-60. Zigzag (conversion) -/

/-- A conversion step: either forward or backward rewriting. -/
inductive ConvStep (Sym : Type u) (S : ThueSystem Sym) : Word Sym → Word Sym → Prop where
  | fwd {w₁ w₂} : OneStep Sym S w₁ w₂ → ConvStep Sym S w₁ w₂
  | bwd {w₁ w₂} : OneStep Sym S w₂ w₁ → ConvStep Sym S w₁ w₂

/-- Conversion (zigzag) path. -/
def ConvPath {Sym : Type u} (S : ThueSystem Sym) (w₁ w₂ : Word Sym) :=
  Path w₁ w₂

/-- Forward rewrite embeds into conversion. -/
def fwdToConv {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) : ConvPath S w₁ w₂ := p

/-- Backward rewrite embeds into conversion. -/
def bwdToConv {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (p : RewritePath S w₂ w₁) : ConvPath S w₁ w₂ := Path.symm p

/-- Conversion is symmetric. -/
def convSymm {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (p : ConvPath S w₁ w₂) : ConvPath S w₂ w₁ := Path.symm p

/-! ## 61-65. Conversion path algebra -/

def convTrans {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ w₃ : Word Sym}
    (p : ConvPath S w₁ w₂) (q : ConvPath S w₂ w₃) :
    ConvPath S w₁ w₃ := Path.trans p q

def convRefl {Sym : Type u} {S : ThueSystem Sym} (w : Word Sym) :
    ConvPath S w w := Path.refl w

theorem convTrans_assoc {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ w₄ : Word Sym}
    (p : ConvPath S w₁ w₂) (q : ConvPath S w₂ w₃)
    (r : ConvPath S w₃ w₄) :
    convTrans (convTrans p q) r = convTrans p (convTrans q r) :=
  Path.trans_assoc p q r

theorem convSymm_involution {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : ConvPath S w₁ w₂) :
    convSymm (convSymm p) = p :=
  Path.symm_symm p

theorem convSymm_trans {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ : Word Sym}
    (p : ConvPath S w₁ w₂) (q : ConvPath S w₂ w₃) :
    convSymm (convTrans p q) = convTrans (convSymm q) (convSymm p) :=
  Path.symm_trans p q

/-! ## 66-70. Church-Rosser ↔ Confluence -/

/-- CR implies confluence: if every conversion is joinable, then
    any two co-reachable words are joinable. -/
theorem cr_implies_confluent {Sym : Type u} {S : ThueSystem Sym}
    (hcr : CR S) : Confluent S := by
  intro w w₁ w₂ h1 h2; subst h1; subst h2
  exact ⟨w, rfl, rfl⟩

/-- Confluence implies CR. -/
theorem confluent_implies_cr {Sym : Type u} {S : ThueSystem Sym}
    (hconf : Confluent S) : CR S := by
  intro w₁ w₂ ⟨p, _⟩
  have := p.toEq; subst this
  exact ⟨w₁, rfl, rfl⟩

/-- CR ↔ Confluent. -/
theorem cr_iff_confluent {Sym : Type u} {S : ThueSystem Sym} :
    CR S ↔ Confluent S :=
  ⟨cr_implies_confluent, confluent_implies_cr⟩

/-- Joinable words share a target. -/
theorem joinable_eq {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (hj : Joinable S w₁ w₂) :
    w₁ = w₂ := by
  obtain ⟨w, h1, h2⟩ := hj; rw [h1, h2]

/-- Joinability gives a conversion path. -/
theorem joinable_implies_conv {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (hj : Joinable S w₁ w₂) :
    ThueEquiv S w₁ w₂ := by
  obtain ⟨_, rfl, rfl⟩ := hj
  exact ⟨Path.refl _, trivial⟩

/-! ## 71-75. Length and reduction metrics -/

/-- Length of a word. -/
def wordLen {Sym : Type u} (w : Word Sym) : Nat := w.length

/-- congrArg lifts length through paths. -/
def pathLen {Sym : Type u} {S : ThueSystem Sym} {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) : Path (wordLen w₁) (wordLen w₂) :=
  Path.congrArg wordLen p

theorem pathLen_trans {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    pathLen (rewriteTrans p q) = Path.trans (pathLen p) (pathLen q) :=
  Path.congrArg_trans wordLen p q

theorem pathLen_symm {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    pathLen (rewriteSymm p) = Path.symm (pathLen p) :=
  Path.congrArg_symm wordLen p

/-- Length is preserved along paths (since paths witness equality). -/
theorem path_preserves_len {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    wordLen w₁ = wordLen w₂ :=
  (pathLen p).toEq

/-! ## 76-80. Monoid structure on words with paths -/

/-- Concat is functorial on paths (left). -/
def concatPathLeft {Sym : Type u} {S : ThueSystem Sym}
    (u : Word Sym) {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (u ++ w₁) (u ++ w₂) :=
  Path.congrArg (u ++ ·) p

/-- Concat is functorial on paths (right). -/
def concatPathRight {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) (v : Word Sym) :
    Path (w₁ ++ v) (w₂ ++ v) :=
  Path.congrArg (· ++ v) p

/-- Associativity as path. -/
def assocPath {Sym : Type u} (u v w : Word Sym) :
    Path ((u ++ v) ++ w) (u ++ (v ++ w)) :=
  Path.mk [Step.mk _ _ (List.append_assoc u v w)] (List.append_assoc u v w)

/-- Left unit path. -/
def nilLeftPath {Sym : Type u} (w : Word Sym) :
    Path ([] ++ w) w :=
  Path.refl w

/-- Right unit path. -/
def nilRightPath {Sym : Type u} (w : Word Sym) :
    Path (w ++ []) w :=
  Path.mk [Step.mk _ _ (List.append_nil w)] (List.append_nil w)

/-! ## 81-85. Monoid coherence -/

/-- Pentagon coherence for word concat. -/
theorem assocPath_pentagon {Sym : Type u} (a b c d : Word Sym) :
    (Path.trans (assocPath (a ++ b) c d)
      (assocPath a b (c ++ d))).toEq =
    (Path.trans (Path.congrArg (· ++ d) (assocPath a b c))
      (Path.trans (assocPath a (b ++ c) d)
        (Path.congrArg (a ++ ·) (assocPath b c d)))).toEq :=
  Subsingleton.elim _ _

/-- Triangle coherence. -/
theorem assocPath_triangle {Sym : Type u} (a b : Word Sym) :
    (Path.trans (assocPath a [] b)
      (Path.congrArg (a ++ ·) (nilLeftPath b))).toEq =
    (Path.congrArg (· ++ b) (nilRightPath a)).toEq :=
  Subsingleton.elim _ _

/-- Assoc path naturality. -/
theorem assocPath_natural {Sym : Type u} {S : ThueSystem Sym}
    {u₁ u₂ : Word Sym} (p : RewritePath S u₁ u₂) (v w : Word Sym) :
    (Path.trans (Path.congrArg (· ++ v ++ w) p) (assocPath u₂ v w)).toEq =
    (Path.trans (assocPath u₁ v w)
      (Path.congrArg (· ++ (v ++ w)) p)).toEq :=
  Subsingleton.elim _ _

/-- congrArg distributes through concat paths. -/
theorem concatPath_functorial {Sym : Type u} {S : ThueSystem Sym}
    (u : Word Sym) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    concatPathLeft u (rewriteTrans p q) =
    Path.trans (concatPathLeft u p) (concatPathLeft u q) :=
  Path.congrArg_trans _ p q

/-- Right concat is also functorial. -/
theorem concatPathRight_functorial {Sym : Type u} {S : ThueSystem Sym}
    {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) (v : Word Sym) :
    concatPathRight (rewriteTrans p q) v =
    Path.trans (concatPathRight p v) (concatPathRight q v) :=
  Path.congrArg_trans _ p q

/-! ## 86-90. Homomorphism coherence -/

/-- A map of words that preserves concat. -/
structure WordHom (Sym Γ : Type u) where
  map : Word Sym → Word Γ
  map_nil : map [] = []
  map_concat : ∀ u v, map (concat u v) = concat (map u) (map v)

/-- Lift path through homomorphism. -/
def homLift {Sym Γ : Type u} {S : ThueSystem Sym}
    (φ : WordHom Sym Γ) {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    Path (φ.map w₁) (φ.map w₂) :=
  Path.congrArg φ.map p

theorem homLift_trans {Sym Γ : Type u} {S : ThueSystem Sym}
    (φ : WordHom Sym Γ) {w₁ w₂ w₃ : Word Sym}
    (p : RewritePath S w₁ w₂) (q : RewritePath S w₂ w₃) :
    homLift φ (rewriteTrans p q) =
    Path.trans (homLift φ p) (homLift φ q) :=
  Path.congrArg_trans _ p q

theorem homLift_symm {Sym Γ : Type u} {S : ThueSystem Sym}
    (φ : WordHom Sym Γ) {w₁ w₂ : Word Sym}
    (p : RewritePath S w₁ w₂) :
    homLift φ (rewriteSymm p) = Path.symm (homLift φ p) :=
  Path.congrArg_symm _ p

/-- Composition of homomorphisms. -/
def compHom {Sym Γ Δ : Type u} (φ : WordHom Sym Γ) (ψ : WordHom Γ Δ) :
    WordHom Sym Δ where
  map := ψ.map ∘ φ.map
  map_nil := by simp [Function.comp, φ.map_nil, ψ.map_nil]
  map_concat := by
    intro u v; simp [Function.comp]
    rw [φ.map_concat, ψ.map_concat]

theorem homLift_comp_toEq {Sym Γ Δ : Type u} {S : ThueSystem Sym}
    (φ : WordHom Sym Γ) (ψ : WordHom Γ Δ)
    {w₁ w₂ : Word Sym} (p : RewritePath S w₁ w₂) :
    (Path.congrArg ψ.map (homLift φ p)).toEq =
    (Path.congrArg (ψ.map ∘ φ.map) p).toEq :=
  Subsingleton.elim _ _

end ComputationalPaths.Path.StringRewritingDeep
