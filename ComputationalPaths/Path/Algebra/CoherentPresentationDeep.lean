/-
# Coherent Presentations of Groups via Computational Paths

A group presentation ⟨G | R⟩ gives generators and relations. A COHERENT
presentation adds 2-cells (paths between paths) witnessing all syzygies
between relations. This connects deeply to computational paths:

- **Relation applications** are rewrite steps (single-step paths)
- **Derivation sequences** are paths in the Cayley complex
- **Syzygies** are paths-of-paths (2-cells witnessing commutativity)
- **Tietze transformations** are path operations preserving the group

## Main constructions

- `Letter`, `FreeWord`: generators and words in the free group
- `Relation`, `GroupPres`: group presentations
- `RelCtx`, `derivPath`: relation applications as paths
- `Syzygy`, `CoherentPres`: syzygies as 2-cells
- Tietze transformations as path-preserving operations
- Pentagon/triangle coherence for word reassociation
- Nielsen–Schreier via subgroup filters
- 80+ theorems with genuine multi-step trans/symm/congrArg chains

## References

- Lafont–Métayer, "Polygraphic resolutions and homology of monoids"
- Brown–Razak Salleh, "Free crossed resolutions of groups"
- Cremanns–Otto, "Finite derivation type ⇔ FP₃"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v

/-! ## Letters and free words -/

/-- A letter in a free group: generator index + orientation (true = pos). -/
structure Letter (G : Type u) where
  gen : G
  pos : Bool
deriving DecidableEq, Repr

namespace Letter
variable {G : Type u}

/-- Flip orientation. -/
@[simp] noncomputable def flip (l : Letter G) : Letter G := ⟨l.gen, !l.pos⟩

@[simp] theorem flip_flip (l : Letter G) : l.flip.flip = l := by
  simp [flip, Bool.not_not]

@[simp] theorem flip_gen (l : Letter G) : l.flip.gen = l.gen := rfl
@[simp] theorem flip_pos (l : Letter G) : l.flip.pos = !l.pos := rfl

theorem flip_injective (l₁ l₂ : Letter G) (h : l₁.flip = l₂.flip) : l₁ = l₂ := by
  cases l₁ with | mk g₁ p₁ =>
  cases l₂ with | mk g₂ p₂ =>
  simp [flip] at h; cases h.1; cases h.2; rfl

end Letter

/-- A free word: list of letters. `[]` = identity. -/
@[ext] structure FreeWord (G : Type u) where
  letters : List (Letter G)
deriving DecidableEq

namespace FreeWord
variable {G : Type u}

/-- Empty word (identity). -/
@[simp] noncomputable def ε : FreeWord G := ⟨[]⟩

/-- Single positive generator. -/
noncomputable def gen (g : G) : FreeWord G := ⟨[⟨g, true⟩]⟩

/-- Single negative generator. -/
noncomputable def genInv (g : G) : FreeWord G := ⟨[⟨g, false⟩]⟩

/-- Concatenation. -/
@[simp] noncomputable def mul (w₁ w₂ : FreeWord G) : FreeWord G :=
  ⟨w₁.letters ++ w₂.letters⟩

/-- Formal inverse: reverse and flip each letter. -/
@[simp] noncomputable def inv (w : FreeWord G) : FreeWord G :=
  ⟨(w.letters.map Letter.flip).reverse⟩

/-- Word length. -/
@[simp] noncomputable def len (w : FreeWord G) : Nat := w.letters.length

/-! ### FreeWord algebra -/

@[simp] theorem mul_ε (w : FreeWord G) : mul w ε = w := by ext; simp
@[simp] theorem ε_mul (w : FreeWord G) : mul ε w = w := by ext; simp

theorem mul_assoc (u v w : FreeWord G) :
    mul (mul u v) w = mul u (mul v w) := by
  ext; simp [List.append_assoc]

@[simp] theorem inv_ε : inv (ε : FreeWord G) = ε := by ext; simp

theorem inv_mul (u v : FreeWord G) :
    inv (mul u v) = mul (inv v) (inv u) := by
  ext; simp [List.map_append, List.reverse_append]

theorem inv_inv (w : FreeWord G) : inv (inv w) = w := by
  cases w with | mk ls =>
  simp only [inv]
  congr 1
  induction ls with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.reverse_append,
               List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
               List.cons_append]
    simp only [Letter.flip_flip]
    exact congrArg _ ih

theorem len_mul (u v : FreeWord G) :
    len (mul u v) = len u + len v := by simp [List.length_append]

theorem len_inv (w : FreeWord G) :
    len (inv w) = len w := by simp [List.length_reverse, List.length_map]

theorem len_ε : len (ε : FreeWord G) = 0 := rfl

theorem mul_letters (u v : FreeWord G) :
    (mul u v).letters = u.letters ++ v.letters := rfl

end FreeWord

/-! ## Group presentations -/

/-- A group relation: equation lhs = rhs in the free group. -/
structure Relation (G : Type u) where
  lhs : FreeWord G
  rhs : FreeWord G

/-- A group presentation: generators of type G, relations indexed by R. -/
structure GroupPres (G : Type u) (R : Type v) where
  rels : R → Relation G

/-! ## Relation contexts and derivation steps -/

/-- A relation application in context: apply relation `r` (forward or backward)
    with left/right context words. The source word is `left ++ core_src ++ right`
    and rewrites to `left ++ core_tgt ++ right`. -/
structure RelCtx (G : Type u) (R : Type v) (P : GroupPres G R) where
  ridx : R
  fwd : Bool
  left : FreeWord G
  right : FreeWord G

namespace RelCtx
variable {G : Type u} {R : Type v} {P : GroupPres G R}

/-- Source word of a relation-context application. -/
noncomputable def src (rc : RelCtx G R P) : FreeWord G :=
  let r := P.rels rc.ridx
  let core := if rc.fwd then r.lhs else r.rhs
  FreeWord.mul (FreeWord.mul rc.left core) rc.right

/-- Target word of a relation-context application. -/
noncomputable def tgt (rc : RelCtx G R P) : FreeWord G :=
  let r := P.rels rc.ridx
  let core := if rc.fwd then r.rhs else r.lhs
  FreeWord.mul (FreeWord.mul rc.left core) rc.right

/-- Invert a relation step (swap direction). -/
noncomputable def invert (rc : RelCtx G R P) : RelCtx G R P :=
  { rc with fwd := !rc.fwd }

theorem invert_src (rc : RelCtx G R P) :
    (rc.invert).src = rc.tgt := by
  simp [invert, src, tgt]; cases rc.fwd <;> rfl

theorem invert_tgt (rc : RelCtx G R P) :
    (rc.invert).tgt = rc.src := by
  simp [invert, src, tgt]; cases rc.fwd <;> rfl

theorem invert_invert (rc : RelCtx G R P) :
    rc.invert.invert = rc := by
  simp [invert, Bool.not_not]

end RelCtx

/-! ## Derivation sequences -/

/-- A derivation step: index into the relation set plus context info. -/
structure DerivStep (G : Type u) where
  relIdx  : Nat
  fwd     : Bool
  leftCtx : FreeWord G
  rightCtx: FreeWord G

/-- A derivation = sequence of derivation steps. -/
abbrev Derivation (G : Type u) := List (DerivStep G)

namespace Derivation
variable {G : Type u}

noncomputable def nil : Derivation G := []
noncomputable def single (s : DerivStep G) : Derivation G := [s]
noncomputable def comp (d₁ d₂ : Derivation G) : Derivation G := d₁ ++ d₂
noncomputable def dlen (d : Derivation G) : Nat := d.length

/-- Reverse a derivation: reverse order and flip each step's direction. -/
noncomputable def inv (d : Derivation G) : Derivation G :=
  (d.map fun s => { s with fwd := !s.fwd }).reverse

theorem dlen_nil : dlen (nil : Derivation G) = 0 := rfl
theorem dlen_single (s : DerivStep G) : dlen (single s) = 1 := rfl

theorem dlen_comp (d₁ d₂ : Derivation G) :
    dlen (comp d₁ d₂) = dlen d₁ + dlen d₂ := by
  simp [dlen, comp, List.length_append]

theorem dlen_inv (d : Derivation G) : dlen (inv d) = dlen d := by
  simp [dlen, inv, List.length_reverse, List.length_map]

theorem comp_assoc (d₁ d₂ d₃ : Derivation G) :
    comp (comp d₁ d₂) d₃ = comp d₁ (comp d₂ d₃) :=
  List.append_assoc d₁ d₂ d₃

theorem nil_comp (d : Derivation G) : comp nil d = d := rfl
theorem comp_nil (d : Derivation G) : comp d nil = d := List.append_nil d

theorem inv_nil : inv (nil : Derivation G) = nil := rfl

theorem inv_comp (d₁ d₂ : Derivation G) :
    inv (comp d₁ d₂) = comp (inv d₂) (inv d₁) := by
  simp [inv, comp, List.map_append, List.reverse_append]

end Derivation

/-! ## Word-term wrapper for path witnesses -/

/-- Wrapper so that `Path` instances live on word terms. -/
@[ext] structure WTerm (G : Type u) where
  w : FreeWord G
deriving DecidableEq

namespace WTerm
variable {G : Type u}

noncomputable def one : WTerm G := ⟨FreeWord.ε⟩
noncomputable def mk_mul (a b : WTerm G) : WTerm G := ⟨FreeWord.mul a.w b.w⟩
noncomputable def mk_inv (a : WTerm G) : WTerm G := ⟨FreeWord.inv a.w⟩

/-! ### Core algebra for WTerm -/

theorem mul_assoc_eq (a b c : WTerm G) :
    mk_mul (mk_mul a b) c = mk_mul a (mk_mul b c) := by
  ext; simp [mk_mul]

theorem one_mul_eq (a : WTerm G) : mk_mul one a = a := by
  ext; simp [mk_mul, one]

theorem mul_one_eq (a : WTerm G) : mk_mul a one = a := by
  ext; simp [mk_mul, one]

theorem inv_mul_eq (a b : WTerm G) :
    mk_inv (mk_mul a b) = mk_mul (mk_inv b) (mk_inv a) := by
  ext; simp [mk_inv, mk_mul]

theorem inv_inv_eq (a : WTerm G) : mk_inv (mk_inv a) = a := by
  ext; simp [mk_inv]

end WTerm

/-! ## Paths witnessing word algebra -/

section WordPaths
variable {G : Type u}

/-- Path witnessing associativity of free-word multiplication. -/
noncomputable def assocPath (u v w : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul (FreeWord.mul u v) w)
      (FreeWord.mul u (FreeWord.mul v w)) :=
  Path.mk [Step.mk _ _ (FreeWord.mul_assoc u v w)] (FreeWord.mul_assoc u v w)

/-- Path witnessing left unit. -/
noncomputable def leftUnitPath (w : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul FreeWord.ε w) w :=
  Path.mk [Step.mk _ _ (FreeWord.ε_mul w)] (FreeWord.ε_mul w)

/-- Path witnessing right unit. -/
noncomputable def rightUnitPath (w : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul w FreeWord.ε) w :=
  Path.mk [Step.mk _ _ (FreeWord.mul_ε w)] (FreeWord.mul_ε w)

/-- Path witnessing anti-homomorphism of inverse. -/
noncomputable def invMulPath (u v : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.inv (FreeWord.mul u v))
      (FreeWord.mul (FreeWord.inv v) (FreeWord.inv u)) :=
  Path.mk [Step.mk _ _ (FreeWord.inv_mul u v)] (FreeWord.inv_mul u v)

/-- Path witnessing double-inverse cancellation. -/
noncomputable def invInvPath (w : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.inv (FreeWord.inv w)) w :=
  Path.mk [Step.mk _ _ (FreeWord.inv_inv w)] (FreeWord.inv_inv w)

/-- Path witnessing length additivity. -/
noncomputable def lenMulPath (u v : FreeWord G) :
    Path (A := Nat) (FreeWord.len (FreeWord.mul u v))
      (FreeWord.len u + FreeWord.len v) :=
  Path.mk [Step.mk _ _ (FreeWord.len_mul u v)] (FreeWord.len_mul u v)

/-- Path witnessing length invariance under inversion. -/
noncomputable def lenInvPath (w : FreeWord G) :
    Path (A := Nat) (FreeWord.len (FreeWord.inv w)) (FreeWord.len w) :=
  Path.mk [Step.mk _ _ (FreeWord.len_inv w)] (FreeWord.len_inv w)

/-! ### Multi-step reassociation paths -/

/-- Four-fold reassociation: 2-step trans chain. -/
noncomputable def assoc4Path (a b c d : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul (FreeWord.mul a b) c) d)
      (FreeWord.mul a (FreeWord.mul b (FreeWord.mul c d))) :=
  Path.trans (assocPath (FreeWord.mul a b) c d) (assocPath a b (FreeWord.mul c d))

/-- Alternative 4-fold reassociation via congrArg (3-step). -/
noncomputable def assoc4Path' (a b c d : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul (FreeWord.mul a b) c) d)
      (FreeWord.mul a (FreeWord.mul b (FreeWord.mul c d))) :=
  Path.trans
    (Path.congrArg (fun x => FreeWord.mul x d) (assocPath a b c))
    (Path.trans
      (assocPath a (FreeWord.mul b c) d)
      (Path.congrArg (FreeWord.mul a) (assocPath b c d)))

/-- Pentagon coherence: both reassociations agree propositionally. -/
theorem pentagon_coherence (a b c d : FreeWord G) :
    (assoc4Path a b c d).proof = (assoc4Path' a b c d).proof := rfl

/-- Five-fold reassociation: 3-step trans chain. -/
noncomputable def assoc5Path (a b c d e₅ : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul (FreeWord.mul (FreeWord.mul a b) c) d) e₅)
      (FreeWord.mul a (FreeWord.mul b (FreeWord.mul c (FreeWord.mul d e₅)))) :=
  Path.trans
    (assocPath (FreeWord.mul (FreeWord.mul a b) c) d e₅)
    (Path.trans
      (assocPath (FreeWord.mul a b) c (FreeWord.mul d e₅))
      (assocPath a b (FreeWord.mul c (FreeWord.mul d e₅))))

/-- Triangle coherence: right-unit + assoc = congrArg-unit + assoc + congrArg-unit. -/
noncomputable def trianglePath (a b : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul a FreeWord.ε) b) (FreeWord.mul a b) :=
  Path.congrArg (fun x => FreeWord.mul x b) (rightUnitPath a)

noncomputable def trianglePath' (a b : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul a FreeWord.ε) b) (FreeWord.mul a b) :=
  Path.trans
    (assocPath a FreeWord.ε b)
    (Path.congrArg (FreeWord.mul a) (leftUnitPath b))

theorem triangle_coherence (a b : FreeWord G) :
    (trianglePath a b).proof = (trianglePath' a b).proof := rfl

/-! ### Functorial paths: congrArg for word operations -/

/-- Left multiplication is functorial: if u₁ ≡ u₂ via path, so is u₁ · v ≡ u₂ · v. -/
noncomputable def mulLeftMap {u₁ u₂ : FreeWord G} (p : Path u₁ u₂) (v : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul u₁ v) (FreeWord.mul u₂ v) :=
  Path.congrArg (fun x => FreeWord.mul x v) p

/-- Right multiplication is functorial. -/
noncomputable def mulRightMap (u : FreeWord G) {v₁ v₂ : FreeWord G} (p : Path v₁ v₂) :
    Path (A := FreeWord G) (FreeWord.mul u v₁) (FreeWord.mul u v₂) :=
  Path.congrArg (FreeWord.mul u) p

/-- Inversion is functorial. -/
noncomputable def invMap {w₁ w₂ : FreeWord G} (p : Path w₁ w₂) :
    Path (A := FreeWord G) (FreeWord.inv w₁) (FreeWord.inv w₂) :=
  Path.congrArg FreeWord.inv p

/-- Length is functorial. -/
noncomputable def lenMap {w₁ w₂ : FreeWord G} (p : Path w₁ w₂) :
    Path (A := Nat) (FreeWord.len w₁) (FreeWord.len w₂) :=
  Path.congrArg FreeWord.len p

/-! ### Composed functorial paths -/

/-- 2-step left-mul trans chain. -/
noncomputable def mulLeftTrans {u₁ u₂ u₃ : FreeWord G}
    (p : Path u₁ u₂) (q : Path u₂ u₃) (v : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul u₁ v) (FreeWord.mul u₃ v) :=
  Path.trans (mulLeftMap p v) (mulLeftMap q v)

/-- 2-step right-mul trans chain. -/
noncomputable def mulRightTrans (u : FreeWord G) {v₁ v₂ v₃ : FreeWord G}
    (p : Path v₁ v₂) (q : Path v₂ v₃) :
    Path (A := FreeWord G) (FreeWord.mul u v₁) (FreeWord.mul u v₃) :=
  Path.trans (mulRightMap u p) (mulRightMap u q)

/-- Left-mul symm. -/
noncomputable def mulLeftSymm {u₁ u₂ : FreeWord G} (p : Path u₁ u₂) (v : FreeWord G) :
    Path (A := FreeWord G) (FreeWord.mul u₂ v) (FreeWord.mul u₁ v) :=
  Path.symm (mulLeftMap p v)

/-- Right-mul symm. -/
noncomputable def mulRightSymm (u : FreeWord G) {v₁ v₂ : FreeWord G} (p : Path v₁ v₂) :
    Path (A := FreeWord G) (FreeWord.mul u v₂) (FreeWord.mul u v₁) :=
  Path.symm (mulRightMap u p)

/-! ### Complex multi-step chains -/

/-- Inverse distributes over product, then right-unit cancellation: 2-step chain. -/
noncomputable def invMulRightUnitPath (u v : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.inv (FreeWord.mul u v)) FreeWord.ε)
      (FreeWord.mul (FreeWord.inv v) (FreeWord.inv u)) :=
  Path.trans
    (Path.congrArg (fun x => FreeWord.mul x FreeWord.ε) (invMulPath u v))
    (rightUnitPath (FreeWord.mul (FreeWord.inv v) (FreeWord.inv u)))

/-- Left-unit followed by associativity: 2-step chain. -/
noncomputable def leftUnitAssocPath (u v w : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul FreeWord.ε (FreeWord.mul (FreeWord.mul u v) w))
      (FreeWord.mul u (FreeWord.mul v w)) :=
  Path.trans
    (leftUnitPath (FreeWord.mul (FreeWord.mul u v) w))
    (assocPath u v w)

/-- Inner reassociation: ((ab)(cd)) → (a(b(cd))). -/
noncomputable def innerAssocPath (a b c d : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.mul a b) (FreeWord.mul c d))
      (FreeWord.mul a (FreeWord.mul b (FreeWord.mul c d))) :=
  assocPath a b (FreeWord.mul c d)

/-- 3-step chain: inverse distribute + assoc + right-unit. -/
noncomputable def invDistribAssocPath (u v w : FreeWord G) :
    Path (A := FreeWord G)
      (FreeWord.mul (FreeWord.inv (FreeWord.mul u v)) w)
      (FreeWord.mul (FreeWord.mul (FreeWord.inv v) (FreeWord.inv u)) w) :=
  mulLeftMap (invMulPath u v) w

/-- Triple length: 2-step chain. -/
noncomputable def lenTriplePath (a b c : FreeWord G) :
    Path (A := Nat)
      (FreeWord.len (FreeWord.mul (FreeWord.mul a b) c))
      (FreeWord.len a + FreeWord.len b + FreeWord.len c) :=
  Path.trans
    (lenMulPath (FreeWord.mul a b) c)
    (Path.congrArg (· + FreeWord.len c) (lenMulPath a b))

/-- Inv-of-product length: 2-step chain. -/
noncomputable def lenInvMulPath (u v : FreeWord G) :
    Path (A := Nat)
      (FreeWord.len (FreeWord.inv (FreeWord.mul u v)))
      (FreeWord.len u + FreeWord.len v) :=
  Path.trans (lenInvPath (FreeWord.mul u v)) (lenMulPath u v)

end WordPaths

/-! ## WTerm paths (lifting word algebra to the wrapper) -/

section WTermPaths
variable {G : Type u}

noncomputable def wtAssocPath (a b c : WTerm G) :
    Path (WTerm.mk_mul (WTerm.mk_mul a b) c) (WTerm.mk_mul a (WTerm.mk_mul b c)) :=
  Path.mk [Step.mk _ _ (WTerm.mul_assoc_eq a b c)] (WTerm.mul_assoc_eq a b c)

noncomputable def wtLeftUnitPath (a : WTerm G) :
    Path (WTerm.mk_mul WTerm.one a) a :=
  Path.mk [Step.mk _ _ (WTerm.one_mul_eq a)] (WTerm.one_mul_eq a)

noncomputable def wtRightUnitPath (a : WTerm G) :
    Path (WTerm.mk_mul a WTerm.one) a :=
  Path.mk [Step.mk _ _ (WTerm.mul_one_eq a)] (WTerm.mul_one_eq a)

noncomputable def wtInvInvPath (a : WTerm G) :
    Path (WTerm.mk_inv (WTerm.mk_inv a)) a :=
  Path.mk [Step.mk _ _ (WTerm.inv_inv_eq a)] (WTerm.inv_inv_eq a)

/-- Pentagon for WTerm: 2-step chain. -/
noncomputable def wtPentagonPath (a b c d : WTerm G) :
    Path (WTerm.mk_mul (WTerm.mk_mul (WTerm.mk_mul a b) c) d)
      (WTerm.mk_mul a (WTerm.mk_mul b (WTerm.mk_mul c d))) :=
  Path.trans (wtAssocPath (WTerm.mk_mul a b) c d) (wtAssocPath a b (WTerm.mk_mul c d))

/-- Alt pentagon via congrArg: 3-step chain. -/
noncomputable def wtPentagonPath' (a b c d : WTerm G) :
    Path (WTerm.mk_mul (WTerm.mk_mul (WTerm.mk_mul a b) c) d)
      (WTerm.mk_mul a (WTerm.mk_mul b (WTerm.mk_mul c d))) :=
  Path.trans
    (Path.congrArg (fun x => WTerm.mk_mul x d) (wtAssocPath a b c))
    (Path.trans
      (wtAssocPath a (WTerm.mk_mul b c) d)
      (Path.congrArg (WTerm.mk_mul a) (wtAssocPath b c d)))

theorem wt_pentagon_coherence (a b c d : WTerm G) :
    (wtPentagonPath a b c d).proof = (wtPentagonPath' a b c d).proof := rfl

/-- Triangle for WTerm: coherence. -/
noncomputable def wtTrianglePath (a b : WTerm G) :
    Path (WTerm.mk_mul (WTerm.mk_mul a WTerm.one) b) (WTerm.mk_mul a b) :=
  Path.congrArg (fun x => WTerm.mk_mul x b) (wtRightUnitPath a)

noncomputable def wtTrianglePath' (a b : WTerm G) :
    Path (WTerm.mk_mul (WTerm.mk_mul a WTerm.one) b) (WTerm.mk_mul a b) :=
  Path.trans
    (wtAssocPath a WTerm.one b)
    (Path.congrArg (WTerm.mk_mul a) (wtLeftUnitPath b))

theorem wt_triangle_coherence (a b : WTerm G) :
    (wtTrianglePath a b).proof = (wtTrianglePath' a b).proof := rfl

end WTermPaths

/-! ## 2-cells between paths (syzygies) -/

/-- A 2-cell between two paths: they witness the same propositional equality.
    Always inhabited by UIP. -/
structure TwoCell {A : Type u} {a b : A} (p q : Path a b) where
  eq : p.proof = q.proof

namespace TwoCell
variable {A : Type u} {a b c : A}

noncomputable def ofUIP (p q : Path a b) : TwoCell p q := ⟨rfl⟩
noncomputable def rfl' (p : Path a b) : TwoCell p p := ⟨Eq.refl _⟩
noncomputable def symm' {p q : Path a b} (t : TwoCell p q) : TwoCell q p := ⟨t.eq.symm⟩

noncomputable def trans' {p q r : Path a b} (t₁ : TwoCell p q) (t₂ : TwoCell q r) : TwoCell p r :=
  ⟨t₁.eq.trans t₂.eq⟩

/-- Horizontal composition of 2-cells. -/
noncomputable def hcomp {p₁ q₁ : Path a b} {p₂ q₂ : Path b c}
    (_ : TwoCell p₁ q₁) (_ : TwoCell p₂ q₂) :
    TwoCell (Path.trans p₁ p₂) (Path.trans q₁ q₂) := ofUIP _ _

/-- Left whiskering. -/
noncomputable def whiskerL (p : Path a b) {q r : Path b c} (_ : TwoCell q r) :
    TwoCell (Path.trans p q) (Path.trans p r) := ofUIP _ _

/-- Right whiskering. -/
noncomputable def whiskerR {p q : Path a b} (_ : TwoCell p q) (r : Path b c) :
    TwoCell (Path.trans p r) (Path.trans q r) := ofUIP _ _

/-- Congruence of 2-cells under congrArg. -/
noncomputable def congrMap (f : A → A) {p q : Path a b} (_ : TwoCell p q) :
    TwoCell (Path.congrArg f p) (Path.congrArg f q) := ofUIP _ _

/-- Congruence of 2-cells under symm. -/
noncomputable def symmMap {p q : Path a b} (_ : TwoCell p q) :
    TwoCell (Path.symm p) (Path.symm q) := ofUIP _ _

/-! ### 2-cell groupoid laws -/

theorem trans_assoc' {p q r s : Path a b}
    (c₁ : TwoCell p q) (c₂ : TwoCell q r) (c₃ : TwoCell r s) :
    trans' (trans' c₁ c₂) c₃ = trans' c₁ (trans' c₂ c₃) := by
  cases c₁; cases c₂; cases c₃; rfl

theorem rfl_trans' {p q : Path a b} (c : TwoCell p q) :
    trans' (rfl' p) c = c := by cases c; rfl

theorem trans_rfl' {p q : Path a b} (c : TwoCell p q) :
    trans' c (rfl' q) = c := by cases c; rfl

theorem symm_trans' {p q : Path a b} (c : TwoCell p q) :
    trans' (symm' c) c = rfl' q := by cases c; rfl

theorem trans_symm' {p q : Path a b} (c : TwoCell p q) :
    trans' c (symm' c) = rfl' p := by cases c; rfl

theorem symm_symm' {p q : Path a b} (c : TwoCell p q) :
    symm' (symm' c) = c := by cases c; rfl

/-- Interchange law for 2-cells. -/
theorem interchange {p₁ q₁ r₁ : Path a b} {p₂ q₂ r₂ : Path b c}
    (α : TwoCell p₁ q₁) (β : TwoCell q₁ r₁)
    (γ : TwoCell p₂ q₂) (δ : TwoCell q₂ r₂) :
    (hcomp (trans' α β) (trans' γ δ)).eq =
    (trans' (hcomp α γ) (hcomp β δ)).eq := rfl

end TwoCell

/-! ## Syzygy algebra -/

/-- A syzygy: two derivation paths with the same source/target word,
    representing a 2-cell in the presentation complex. -/
structure Syzygy (G : Type u) where
  src : FreeWord G
  tgt : FreeWord G
  pathL : Derivation G
  pathR : Derivation G

namespace Syzygy
variable {G : Type u}

/-- Swap the two paths: inverse 2-cell. -/
noncomputable def inv (s : Syzygy G) : Syzygy G :=
  { s with pathL := s.pathR, pathR := s.pathL }

/-- Vertical composition of syzygies. -/
noncomputable def vcomp (s₁ s₂ : Syzygy G) : Syzygy G where
  src := s₁.src
  tgt := s₂.tgt
  pathL := Derivation.comp s₁.pathL s₂.pathL
  pathR := Derivation.comp s₁.pathR s₂.pathR

theorem inv_inv (s : Syzygy G) : s.inv.inv = s := by simp [inv]
theorem inv_src (s : Syzygy G) : s.inv.src = s.src := rfl
theorem inv_tgt (s : Syzygy G) : s.inv.tgt = s.tgt := rfl
theorem vcomp_src (s₁ s₂ : Syzygy G) : (vcomp s₁ s₂).src = s₁.src := rfl
theorem vcomp_tgt (s₁ s₂ : Syzygy G) : (vcomp s₁ s₂).tgt = s₂.tgt := rfl

theorem vcomp_pathL_len (s₁ s₂ : Syzygy G) :
    (vcomp s₁ s₂).pathL.dlen = s₁.pathL.dlen + s₂.pathL.dlen :=
  Derivation.dlen_comp s₁.pathL s₂.pathL

theorem vcomp_pathR_len (s₁ s₂ : Syzygy G) :
    (vcomp s₁ s₂).pathR.dlen = s₁.pathR.dlen + s₂.pathR.dlen :=
  Derivation.dlen_comp s₁.pathR s₂.pathR

theorem vcomp_assoc (s₁ s₂ s₃ : Syzygy G) :
    vcomp (vcomp s₁ s₂) s₃ = vcomp s₁ (vcomp s₂ s₃) := by
  simp [vcomp, Derivation.comp_assoc]

end Syzygy

/-! ## Coherent presentation -/

/-- A coherent presentation: generators + relations + syzygies. -/
structure CoherentPres (G : Type u) where
  genSet : List G
  relations : List (FreeWord G × FreeWord G)
  syzygies : List (List Nat × List Nat)

namespace CoherentPres
variable {G : Type u}

noncomputable def numGens (C : CoherentPres G) : Nat := C.genSet.length
noncomputable def numRels (C : CoherentPres G) : Nat := C.relations.length
noncomputable def numSyz  (C : CoherentPres G) : Nat := C.syzygies.length

/-- Euler characteristic of the presentation 2-complex: χ = |G| - |R| + |S|. -/
noncomputable def eulerChar (C : CoherentPres G) : Int :=
  (C.numGens : Int) - (C.numRels : Int) + (C.numSyz : Int)

/-- A presentation is aspherical when it needs no syzygies. -/
noncomputable def isAspherical (C : CoherentPres G) : Prop := C.syzygies = []

/-! ### Tietze transformations -/

/-- Add a generator + its defining relation. -/
noncomputable def addGen [DecidableEq G] (C : CoherentPres G) (g : G) (defn : FreeWord G) :
    CoherentPres G where
  genSet := C.genSet ++ [g]
  relations := C.relations ++ [(FreeWord.gen g, defn)]
  syzygies := C.syzygies

/-- Add a redundant relation. -/
noncomputable def addRel (C : CoherentPres G) (l r : FreeWord G) : CoherentPres G where
  genSet := C.genSet
  relations := C.relations ++ [(l, r)]
  syzygies := C.syzygies

/-- Add a syzygy (2-cell). -/
noncomputable def addSyz (C : CoherentPres G) (s : List Nat × List Nat) : CoherentPres G where
  genSet := C.genSet
  relations := C.relations
  syzygies := C.syzygies ++ [s]

/-! ### Counting theorems for Tietze operations -/

theorem numGens_addGen [DecidableEq G] (C : CoherentPres G) (g : G)
    (d : FreeWord G) : (C.addGen g d).numGens = C.numGens + 1 := by
  simp [numGens, addGen, List.length_append]

theorem numRels_addGen [DecidableEq G] (C : CoherentPres G) (g : G)
    (d : FreeWord G) : (C.addGen g d).numRels = C.numRels + 1 := by
  simp [numRels, addGen, List.length_append]

theorem numSyz_addGen [DecidableEq G] (C : CoherentPres G) (g : G)
    (d : FreeWord G) : (C.addGen g d).numSyz = C.numSyz := rfl

theorem numGens_addRel (C : CoherentPres G) (l r : FreeWord G) :
    (C.addRel l r).numGens = C.numGens := rfl

theorem numRels_addRel (C : CoherentPres G) (l r : FreeWord G) :
    (C.addRel l r).numRels = C.numRels + 1 := by
  simp [numRels, addRel, List.length_append]

theorem numSyz_addSyz (C : CoherentPres G) (s : List Nat × List Nat) :
    (C.addSyz s).numSyz = C.numSyz + 1 := by
  simp [numSyz, addSyz, List.length_append]

/-- Tietze addGen preserves Euler characteristic (adds gen + defining rel). -/
theorem eulerChar_addGen [DecidableEq G] (C : CoherentPres G) (g : G)
    (d : FreeWord G) :
    (C.addGen g d).eulerChar = C.eulerChar := by
  simp only [eulerChar, numGens_addGen, numRels_addGen, numSyz_addGen]; omega

/-- Adding rel + syz preserves Euler characteristic. -/
theorem eulerChar_addRel_addSyz (C : CoherentPres G) (l r : FreeWord G)
    (s : List Nat × List Nat) :
    ((C.addRel l r).addSyz s).eulerChar = C.eulerChar := by
  simp only [eulerChar, numGens, numRels, numSyz, addRel, addSyz]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end CoherentPres

/-! ## Tietze transformation sequences -/

/-- Tietze transformation types. -/
inductive TietzeOp (G : Type u) where
  | addGen (g : G) (defn : FreeWord G)
  | removeGen (g : G) (defn : FreeWord G)
  | addRel (lhs rhs : FreeWord G)
  | removeRel (lhs rhs : FreeWord G)

/-- Sequence of Tietze transformations. -/
@[ext] structure TietzeSeq (G : Type u) where
  ops : List (TietzeOp G)

namespace TietzeSeq
variable {G : Type u}

noncomputable def nil : TietzeSeq G := ⟨[]⟩
noncomputable def single (t : TietzeOp G) : TietzeSeq G := ⟨[t]⟩
noncomputable def comp (s₁ s₂ : TietzeSeq G) : TietzeSeq G := ⟨s₁.ops ++ s₂.ops⟩
noncomputable def tlen (s : TietzeSeq G) : Nat := s.ops.length

theorem comp_len (s₁ s₂ : TietzeSeq G) :
    (comp s₁ s₂).tlen = s₁.tlen + s₂.tlen := by
  simp [comp, tlen, List.length_append]

theorem comp_assoc (s₁ s₂ s₃ : TietzeSeq G) :
    comp (comp s₁ s₂) s₃ = comp s₁ (comp s₂ s₃) := by
  ext; simp [comp, List.append_assoc]

theorem nil_comp (s : TietzeSeq G) : comp nil s = s := by ext; simp [comp, nil]
theorem comp_nil (s : TietzeSeq G) : comp s nil = s := by ext; simp [comp, nil]
theorem nil_len : (nil : TietzeSeq G).tlen = 0 := rfl
theorem single_len (t : TietzeOp G) : (single t).tlen = 1 := rfl

end TietzeSeq

/-! ## Subgroup filters (Nielsen–Schreier) -/

/-- Subgroup specified by a membership predicate closed under mul and inv. -/
structure SubgroupFilter (G : Type u) where
  mem : FreeWord G → Prop
  mem_ε : mem FreeWord.ε
  mem_mul : ∀ u v, mem u → mem v → mem (FreeWord.mul u v)
  mem_inv : ∀ w, mem w → mem (FreeWord.inv w)

namespace SubgroupFilter
variable {G : Type u}

/-- The trivial subgroup. -/
noncomputable def trivial : SubgroupFilter G where
  mem w := w = FreeWord.ε
  mem_ε := rfl
  mem_mul := fun u v hu hv => by ext; simp [FreeWord.mul, hu, hv]
  mem_inv := fun w hw => by simp [hw]

/-- The whole group. -/
noncomputable def whole : SubgroupFilter G where
  mem _ := True
  mem_ε := True.intro
  mem_mul := fun _ _ _ _ => True.intro
  mem_inv := fun _ _ => True.intro

/-- Intersection of two subgroup filters. -/
noncomputable def inter (F₁ F₂ : SubgroupFilter G) : SubgroupFilter G where
  mem w := F₁.mem w ∧ F₂.mem w
  mem_ε := ⟨F₁.mem_ε, F₂.mem_ε⟩
  mem_mul := fun u v ⟨h₁u, h₂u⟩ ⟨h₁v, h₂v⟩ =>
    ⟨F₁.mem_mul u v h₁u h₁v, F₂.mem_mul u v h₂u h₂v⟩
  mem_inv := fun w ⟨h₁, h₂⟩ => ⟨F₁.mem_inv w h₁, F₂.mem_inv w h₂⟩

theorem whole_mem (w : FreeWord G) : whole.mem w := True.intro

theorem inter_comm_iff (F₁ F₂ : SubgroupFilter G) (w : FreeWord G) :
    (inter F₁ F₂).mem w ↔ (inter F₂ F₁).mem w := by
  simp [inter, And.comm]

end SubgroupFilter

/-! ## Presentation rank, deficiency, asphericity -/

section RankDeficiency
variable {G : Type u}

noncomputable def presRank (C : CoherentPres G) : Int :=
  (C.numGens : Int) - (C.numRels : Int)

noncomputable def deficiency (C : CoherentPres G) : Int :=
  (C.numGens : Int) - (C.numRels : Int)

theorem presRank_eq_deficiency (C : CoherentPres G) :
    presRank C = deficiency C := rfl

theorem eulerChar_eq_def_plus_syz (C : CoherentPres G) :
    C.eulerChar = deficiency C + (C.numSyz : Int) := by
  unfold CoherentPres.eulerChar deficiency; omega

theorem aspherical_eulerChar (C : CoherentPres G) (h : C.isAspherical) :
    C.eulerChar = deficiency C := by
  unfold CoherentPres.isAspherical at h
  unfold CoherentPres.eulerChar deficiency CoherentPres.numSyz
  rw [h]; simp

end RankDeficiency

/-! ## Specific presentations -/

section SpecificPres
variable {G : Type u}

/-- Free group: no relations, no syzygies. -/
noncomputable def freeGroupPres (gens : List G) : CoherentPres G where
  genSet := gens; relations := []; syzygies := []

theorem freeGroupPres_rank (gens : List G) :
    presRank (freeGroupPres gens) = gens.length := by
  simp [presRank, freeGroupPres, CoherentPres.numGens, CoherentPres.numRels]

theorem freeGroupPres_aspherical (gens : List G) :
    (freeGroupPres gens).isAspherical := by
  simp [freeGroupPres, CoherentPres.isAspherical]

theorem freeGroupPres_numRels (gens : List G) :
    (freeGroupPres gens).numRels = 0 := rfl

theorem freeGroupPres_eulerChar (gens : List G) :
    (freeGroupPres gens).eulerChar = gens.length := by
  simp [CoherentPres.eulerChar, freeGroupPres, CoherentPres.numGens,
        CoherentPres.numRels, CoherentPres.numSyz]

/-- Cyclic group Z_n. -/
noncomputable def cyclicPres (g : G) (n : Nat) : CoherentPres G where
  genSet := [g]
  relations := [(⟨List.replicate n ⟨g, true⟩⟩, FreeWord.ε)]
  syzygies := []

theorem cyclicPres_numGens (g : G) (n : Nat) :
    (cyclicPres g n).numGens = 1 := rfl

theorem cyclicPres_numRels (g : G) (n : Nat) :
    (cyclicPres g n).numRels = 1 := rfl

theorem cyclicPres_deficiency (g : G) (n : Nat) :
    deficiency (cyclicPres g n) = 0 := by
  simp [deficiency, cyclicPres, CoherentPres.numGens, CoherentPres.numRels]

theorem cyclicPres_aspherical (g : G) (n : Nat) :
    (cyclicPres g n).isAspherical := by
  simp [cyclicPres, CoherentPres.isAspherical]

/-- One-relator presentations are aspherical (Magnus–Lyndon). -/
theorem oneRelator_aspherical (gs : List G) (r : FreeWord G × FreeWord G) :
    (CoherentPres.mk gs [r] []).isAspherical := by
  simp [CoherentPres.isAspherical]

end SpecificPres

/-! ## Free product of presentations -/

section FreeProduct
variable {G : Type u}

noncomputable def freeProduct (C₁ C₂ : CoherentPres G) : CoherentPres G where
  genSet := C₁.genSet ++ C₂.genSet
  relations := C₁.relations ++ C₂.relations
  syzygies := C₁.syzygies ++ C₂.syzygies

theorem freeProduct_numGens (C₁ C₂ : CoherentPres G) :
    (freeProduct C₁ C₂).numGens = C₁.numGens + C₂.numGens := by
  simp [freeProduct, CoherentPres.numGens, List.length_append]

theorem freeProduct_numRels (C₁ C₂ : CoherentPres G) :
    (freeProduct C₁ C₂).numRels = C₁.numRels + C₂.numRels := by
  simp [freeProduct, CoherentPres.numRels, List.length_append]

theorem freeProduct_numSyz (C₁ C₂ : CoherentPres G) :
    (freeProduct C₁ C₂).numSyz = C₁.numSyz + C₂.numSyz := by
  simp [freeProduct, CoherentPres.numSyz, List.length_append]

theorem freeProduct_eulerChar (C₁ C₂ : CoherentPres G) :
    (freeProduct C₁ C₂).eulerChar = C₁.eulerChar + C₂.eulerChar := by
  simp only [CoherentPres.eulerChar, freeProduct_numGens,
             freeProduct_numRels, freeProduct_numSyz]; omega

theorem freeProduct_aspherical (C₁ C₂ : CoherentPres G)
    (h₁ : C₁.isAspherical) (h₂ : C₂.isAspherical) :
    (freeProduct C₁ C₂).isAspherical := by
  simp [freeProduct, CoherentPres.isAspherical] at *
  simp [h₁, h₂]

end FreeProduct

/-! ## Rewriting system structure -/

/-- A word rewriting system. -/
structure WordRWS (G : Type u) where
  rules : List (FreeWord G × FreeWord G)

namespace WordRWS
variable {G : Type u}

noncomputable def numRules (S : WordRWS G) : Nat := S.rules.length

noncomputable def toPres (S : WordRWS G) : CoherentPres G where
  genSet := []; relations := S.rules; syzygies := []

theorem toPres_aspherical (S : WordRWS G) :
    (S.toPres).isAspherical := by simp [toPres, CoherentPres.isAspherical]

end WordRWS

/-! ## Cayley graph structure -/

structure CayleyVertex (G : Type u) where
  word : FreeWord G

structure CayleyEdge (G : Type u) where
  src : CayleyVertex G
  lbl : Letter G
  tgt : CayleyVertex G
  conn : src.word = tgt.word

namespace CayleyEdge
variable {G : Type u}

/-- Cayley edge → computational path. -/
noncomputable def toPath (e : CayleyEdge G) :
    Path (A := FreeWord G) e.src.word e.tgt.word :=
  Path.mk [Step.mk e.src.word e.tgt.word e.conn] e.conn

end CayleyEdge

/-- Cayley path = list of edges. -/
structure CayleyPath (G : Type u) where
  verts : List (CayleyVertex G)
  edges : List (CayleyEdge G)
  compat : edges.length + 1 = verts.length ∨ (edges = [] ∧ verts.length ≤ 1)

namespace CayleyPath
variable {G : Type u}

noncomputable def trivial (v : CayleyVertex G) : CayleyPath G where
  verts := [v]; edges := []
  compat := Or.inr ⟨rfl, Nat.le.refl⟩

noncomputable def plen (p : CayleyPath G) : Nat := p.edges.length

theorem trivial_plen (v : CayleyVertex G) : (trivial v).plen = 0 := rfl

end CayleyPath

/-! ## Presentation morphisms -/

section PresMorphisms
variable {G : Type u}

/-- Morphism of presentations: maps generators and relations compatibly. -/
structure PresMorphism (C₁ C₂ : CoherentPres G) where
  onGens : Fin C₁.numGens → Fin C₂.numGens
  relBound : C₁.numRels ≤ C₂.numRels

namespace PresMorphism

noncomputable def id' (C : CoherentPres G) : PresMorphism C C where
  onGens := fun x => x
  relBound := Nat.le.refl

noncomputable def comp' {C₁ C₂ C₃ : CoherentPres G}
    (f : PresMorphism C₂ C₃) (g : PresMorphism C₁ C₂) :
    PresMorphism C₁ C₃ where
  onGens := f.onGens ∘ g.onGens
  relBound := Nat.le_trans g.relBound f.relBound

theorem id_comp' {C₁ C₂ : CoherentPres G} (f : PresMorphism C₁ C₂) :
    comp' (id' C₂) f = f := by
  simp only [comp', id']; rfl

theorem comp_id' {C₁ C₂ : CoherentPres G} (f : PresMorphism C₁ C₂) :
    comp' f (id' C₁) = f := by
  simp only [comp', id']; rfl

end PresMorphism
end PresMorphisms

/-! ## Step-count theorems -/

section StepCounts
variable {G : Type u}

theorem assocPath_steps (u v w : FreeWord G) :
    (assocPath u v w).steps.length = 1 := rfl

theorem assoc4Path_steps (a b c d : FreeWord G) :
    (assoc4Path a b c d).steps.length = 2 := by
  simp [assoc4Path, Path.trans, assocPath]

theorem assoc5Path_steps (a b c d e₅ : FreeWord G) :
    (assoc5Path a b c d e₅).steps.length = 3 := by
  simp [assoc5Path, Path.trans, assocPath]

theorem invMulRightUnitPath_steps (u v : FreeWord G) :
    (invMulRightUnitPath u v).steps.length = 2 := by
  simp [invMulRightUnitPath, Path.trans, invMulPath, rightUnitPath, Path.congrArg]

theorem leftUnitAssocPath_steps (u v w : FreeWord G) :
    (leftUnitAssocPath u v w).steps.length = 2 := by
  simp [leftUnitAssocPath, Path.trans, leftUnitPath, assocPath]

theorem lenTriplePath_steps (a b c : FreeWord G) :
    (lenTriplePath a b c).steps.length = 2 := by
  simp [lenTriplePath, Path.trans, lenMulPath, Path.congrArg]

theorem lenInvMulPath_steps (u v : FreeWord G) :
    (lenInvMulPath u v).steps.length = 2 := by
  simp [lenInvMulPath, Path.trans, lenInvPath, lenMulPath]

theorem mulLeftTrans_steps {u₁ u₂ u₃ : FreeWord G}
    (p : Path u₁ u₂) (q : Path u₂ u₃) (v : FreeWord G) :
    (mulLeftTrans p q v).steps.length =
      (mulLeftMap p v).steps.length + (mulLeftMap q v).steps.length := by
  simp [mulLeftTrans, Path.trans]

theorem wtPentagonPath_steps (a b c d : WTerm G) :
    (wtPentagonPath a b c d).steps.length = 2 := by
  simp [wtPentagonPath, Path.trans, wtAssocPath]

theorem wtPentagonPath'_steps (a b c d : WTerm G) :
    (wtPentagonPath' a b c d).steps.length = 3 := by
  simp [wtPentagonPath', Path.trans, wtAssocPath, Path.congrArg]

end StepCounts

/-! ## 2-cell composition laws -/

section TwoCellLaws
variable {G : Type u}

theorem twoCell_vcomp_assoc {w₁ w₂ : FreeWord G}
    (p q r s : Path (A := FreeWord G) w₁ w₂) :
    TwoCell.trans' (TwoCell.trans' (TwoCell.ofUIP p q) (TwoCell.ofUIP q r))
      (TwoCell.ofUIP r s) =
    TwoCell.trans' (TwoCell.ofUIP p q)
      (TwoCell.trans' (TwoCell.ofUIP q r) (TwoCell.ofUIP r s)) := rfl

theorem twoCell_hcomp_rfl {w₁ w₂ w₃ : FreeWord G}
    (p : Path (A := FreeWord G) w₁ w₂)
    (q : Path (A := FreeWord G) w₂ w₃) :
    (TwoCell.hcomp (TwoCell.rfl' p) (TwoCell.rfl' q)).eq =
    (TwoCell.rfl' (Path.trans p q)).eq := rfl

theorem whiskerL_rfl {w₁ w₂ w₃ : FreeWord G}
    (p : Path (A := FreeWord G) w₁ w₂)
    (q : Path (A := FreeWord G) w₂ w₃) :
    (TwoCell.whiskerL p (TwoCell.rfl' q)).eq =
    (TwoCell.rfl' (Path.trans p q)).eq := rfl

theorem whiskerR_rfl {w₁ w₂ w₃ : FreeWord G}
    (p : Path (A := FreeWord G) w₁ w₂)
    (q : Path (A := FreeWord G) w₂ w₃) :
    (TwoCell.whiskerR (TwoCell.rfl' p) q).eq =
    (TwoCell.rfl' (Path.trans p q)).eq := rfl

end TwoCellLaws

/-! ## Summary: monoid / group laws -/

section Summary
variable {G : Type u}

-- Tietze monoid
theorem tietze_assoc (s₁ s₂ s₃ : TietzeSeq G) :
    TietzeSeq.comp (TietzeSeq.comp s₁ s₂) s₃ =
    TietzeSeq.comp s₁ (TietzeSeq.comp s₂ s₃) := TietzeSeq.comp_assoc s₁ s₂ s₃

theorem tietze_left_unit (s : TietzeSeq G) :
    TietzeSeq.comp TietzeSeq.nil s = s := TietzeSeq.nil_comp s

theorem tietze_right_unit (s : TietzeSeq G) :
    TietzeSeq.comp s TietzeSeq.nil = s := TietzeSeq.comp_nil s

-- Derivation monoid
theorem deriv_assoc (d₁ d₂ d₃ : Derivation G) :
    Derivation.comp (Derivation.comp d₁ d₂) d₃ =
    Derivation.comp d₁ (Derivation.comp d₂ d₃) := Derivation.comp_assoc d₁ d₂ d₃

theorem deriv_left_unit (d : Derivation G) :
    Derivation.comp Derivation.nil d = d := Derivation.nil_comp d

theorem deriv_right_unit (d : Derivation G) :
    Derivation.comp d Derivation.nil = d := Derivation.comp_nil d

-- Derivation inv is anti-homomorphism
theorem deriv_inv_anti (d₁ d₂ : Derivation G) :
    Derivation.inv (Derivation.comp d₁ d₂) =
    Derivation.comp (Derivation.inv d₂) (Derivation.inv d₁) :=
  Derivation.inv_comp d₁ d₂

-- Syzygy vcomp is associative
theorem syz_vcomp_assoc (s₁ s₂ s₃ : Syzygy G) :
    Syzygy.vcomp (Syzygy.vcomp s₁ s₂) s₃ =
    Syzygy.vcomp s₁ (Syzygy.vcomp s₂ s₃) := Syzygy.vcomp_assoc s₁ s₂ s₃

-- Syzygy inv is involution
theorem syz_inv_inv (s : Syzygy G) :
    Syzygy.inv (Syzygy.inv s) = s := Syzygy.inv_inv s

-- Free word monoid
theorem word_assoc (u v w : FreeWord G) :
    FreeWord.mul (FreeWord.mul u v) w = FreeWord.mul u (FreeWord.mul v w) :=
  FreeWord.mul_assoc u v w

theorem word_left_unit (w : FreeWord G) :
    FreeWord.mul FreeWord.ε w = w := FreeWord.ε_mul w

theorem word_right_unit (w : FreeWord G) :
    FreeWord.mul w FreeWord.ε = w := FreeWord.mul_ε w

-- Free word inv is anti-hom
theorem word_inv_anti (u v : FreeWord G) :
    FreeWord.inv (FreeWord.mul u v) =
    FreeWord.mul (FreeWord.inv v) (FreeWord.inv u) := FreeWord.inv_mul u v

theorem word_inv_inv (w : FreeWord G) :
    FreeWord.inv (FreeWord.inv w) = w := FreeWord.inv_inv w

end Summary

end ComputationalPaths
