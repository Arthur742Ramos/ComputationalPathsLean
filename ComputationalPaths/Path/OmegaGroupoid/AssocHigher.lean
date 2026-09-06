import Solution
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Explicit higher associativity rewrites

The objects and one-dimensional traces are those of the checked free-magma
certificate. Higher cells are generated locally: the pentagon, disjoint
interchange, naturality in each input of a rotation, and groupoid syntax laws.
There is deliberately no constructor filling arbitrary parallel traces.

`evalTrace` interprets every generator of a trace as an actual computational
path rewrite. Labels denote loops at a fixed point: this homogeneous interface
does not claim to encode arbitrary heterogeneously composable path strings.
-/

namespace ComputationalPaths.Path.PalomarAssociativity

universe u v

namespace AssocRwEq

def congrLeft {α : Type u} {x x' : FreeMagma α}
    (p : AssocRwEq x x') (y : FreeMagma α) : AssocRwEq (x * y) (x' * y) :=
  match p with
  | .refl _ => .refl _
  | .step s => .step (.congrLeft s y)
  | .symm p => .symm (congrLeft p y)
  | .trans p q => .trans (congrLeft p y) (congrLeft q y)

def congrRight {α : Type u} (x : FreeMagma α)
    {y y' : FreeMagma α} (p : AssocRwEq y y') : AssocRwEq (x * y) (x * y') :=
  match p with
  | .refl _ => .refl _
  | .step s => .step (.congrRight x s)
  | .symm p => .symm (congrRight x p)
  | .trans p q => .trans (congrRight x p) (congrRight x q)

end AssocRwEq

/-- A rotation regarded as an invertible trace generator. -/
def rotation {α : Type u} (x y z : FreeMagma α) :
    AssocRwEq ((x * y) * z) (x * (y * z)) := .step (.rotate x y z)

/-- The locally presented two-dimensional rewrite system on trace syntax.
The three naturality squares cover nested but noncritical overlaps; the
pentagon covers the critical overlap and interchange covers disjoint ones.
Structural laws concern composition/inversion of traces, not tree equality.
-/
inductive AssocHigher {α : Type u} : {x y : FreeMagma α} →
    AssocRwEq x y → AssocRwEq x y → Type u where
  | refl {x y} (p : AssocRwEq x y) : AssocHigher p p
  | symm {x y} {p q : AssocRwEq x y} : AssocHigher p q → AssocHigher q p
  | trans {x y} {p q r : AssocRwEq x y} :
      AssocHigher p q → AssocHigher q r → AssocHigher p r
  | comp {x y z} {p p' : AssocRwEq x y} {q q' : AssocRwEq y z} :
      AssocHigher p p' → AssocHigher q q' →
      AssocHigher (.trans p q) (.trans p' q')
  | inv {x y} {p q : AssocRwEq x y} :
      AssocHigher p q → AssocHigher (.symm p) (.symm q)
  | left {x x'} {p q : AssocRwEq x x'} (y : FreeMagma α) :
      AssocHigher p q → AssocHigher (p.congrLeft y) (q.congrLeft y)
  | right (x : FreeMagma α) {y y'} {p q : AssocRwEq y y'} :
      AssocHigher p q → AssocHigher (p.congrRight x) (q.congrRight x)
  | assoc {w x y z} (p : AssocRwEq w x) (q : AssocRwEq x y)
      (r : AssocRwEq y z) :
      AssocHigher (.trans (.trans p q) r) (.trans p (.trans q r))
  | unitLeft {x y} (p : AssocRwEq x y) : AssocHigher (.trans (.refl x) p) p
  | unitRight {x y} (p : AssocRwEq x y) : AssocHigher (.trans p (.refl y)) p
  | cancel {x y} (p : AssocRwEq x y) :
      AssocHigher (.trans p (.symm p)) (.refl x)
  | cancelRev {x y} (p : AssocRwEq x y) :
      AssocHigher (.trans (.symm p) p) (.refl y)
  | invRefl (x : FreeMagma α) : AssocHigher (.symm (.refl x)) (.refl x)
  | invInv {x y} (p : AssocRwEq x y) : AssocHigher (.symm (.symm p)) p
  | invComp {x y z} (p : AssocRwEq x y) (q : AssocRwEq y z) :
      AssocHigher (.symm (.trans p q)) (.trans (.symm q) (.symm p))
  | pentagon (w x y z : FreeMagma α) :
      AssocHigher ((pentagonShort w x y z).toRwEq)
        ((pentagonLong w x y z).toRwEq)
  | interchange {x x' y y'} (p : AssocRwEq x x') (q : AssocRwEq y y') :
      AssocHigher (.trans (p.congrLeft y) (q.congrRight x'))
        (.trans (q.congrRight x) (p.congrLeft y'))
  | naturalLeft {x x'} (p : AssocRwEq x x') (y z : FreeMagma α) :
      AssocHigher (.trans ((p.congrLeft y).congrLeft z) (rotation x' y z))
        (.trans (rotation x y z) (p.congrLeft (y * z)))
  | naturalMiddle (x : FreeMagma α) {y y'} (p : AssocRwEq y y')
      (z : FreeMagma α) :
      AssocHigher (.trans ((p.congrRight x).congrLeft z) (rotation x y' z))
        (.trans (rotation x y z) ((p.congrLeft z).congrRight x))
  | naturalRight (x y : FreeMagma α) {z z'} (p : AssocRwEq z z') :
      AssocHigher (.trans (p.congrRight (x * y)) (rotation x y z'))
        (.trans (rotation x y z) ((p.congrRight y).congrRight x))

namespace AssocHigher

variable {α : Type u} {w x y z : FreeMagma α}

/-- Remove an explicitly followed-and-reversed suffix using only the local
groupoid laws. This is the cancellation step needed by normalization coherence. -/
def eraseSuffix (p : AssocRwEq x y) (r : AssocRwEq y z) :
    AssocHigher (.trans (.trans p r) (.symm r)) p :=
  .trans (.assoc p r (.symm r))
    (.trans (.comp (.refl p) (.cancel r)) (.unitRight p))

/-- Coherent extensions by a common suffix imply coherence of the original
traces. No cancellation axiom for higher cells is assumed. -/
def cancelSuffix {p q : AssocRwEq x y} (r : AssocRwEq y z)
    (h : AssocHigher (.trans p r) (.trans q r)) : AssocHigher p q :=
  .trans (.symm (eraseSuffix p r))
    (.trans (.comp h (.refl (.symm r))) (eraseSuffix q r))

/-- It suffices to compare traces after extending them to a chosen normal
form. The normalizing extension is data, not a universal coherence premise. -/
def compareVia {p q : AssocRwEq x y} (r : AssocRwEq y z)
    (n : AssocRwEq x z)
    (hp : AssocHigher (.trans p r) n)
    (hq : AssocHigher (.trans q r) n) : AssocHigher p q :=
  cancelSuffix r (.trans hp (.symm hq))

end AssocHigher

namespace AssocReduces

@[simp] theorem toRwEq_congrLeft {α : Type u} {x x' : FreeMagma α}
    (p : AssocReduces x x') (y : FreeMagma α) :
    (p.congrLeft y).toRwEq = p.toRwEq.congrLeft y := by
  induction p with
  | refl => rfl
  | step => rfl
  | trans p q hp hq => simp [congrLeft, toRwEq, AssocRwEq.congrLeft, hp, hq]

@[simp] theorem toRwEq_congrRight {α : Type u} (x : FreeMagma α)
    {y y' : FreeMagma α} (p : AssocReduces y y') :
    (p.congrRight x).toRwEq = p.toRwEq.congrRight x := by
  induction p with
  | refl => rfl
  | step => rfl
  | trans p q hp hq => simp [congrRight, toRwEq, AssocRwEq.congrRight, hp, hq]

end AssocReduces

/-- A local confluence square with a higher certificate of its boundary.
Unlike ordinary confluence this retains the comparison of the two histories. -/
structure CoherentPeak {α : Type u} {x y z : FreeMagma α}
    (p : AssocStep x y) (q : AssocStep x z) where
  target : FreeMagma α
  left : AssocReduces y target
  right : AssocReduces z target
  cell : AssocHigher (.trans (.step p) left.toRwEq) (.trans (.step q) right.toRwEq)

namespace CoherentPeak

def flip {α : Type u} {x y z : FreeMagma α}
    {p : AssocStep x y} {q : AssocStep x z} (h : CoherentPeak p q) : CoherentPeak q p :=
  ⟨h.target, h.right, h.left, .symm h.cell⟩

/-- All overlaps with a root rotation: identical, critical pentagon,
or a rewrite contained in one of the three independent arguments. -/
def atRoot {α : Type u} (x y z : FreeMagma α) {t : FreeMagma α}
    (q : AssocStep ((x * y) * z) t) : CoherentPeak (.rotate x y z) q := by
  cases q with
  | rotate => exact ⟨_, .refl _, .refl _, .refl _⟩
  | congrLeft s z =>
    cases s with
    | rotate a b c =>
      exact ⟨_, .step (.rotate a b (y * z)),
        .trans (.step (.rotate a (b * y) z)) (.step (.congrRight a (.rotate b y z))),
        .pentagon a b y z⟩
    | congrLeft s b =>
      exact ⟨_, .step (.congrLeft s (y * z)), .step (.rotate _ y z),
        .symm (.naturalLeft (.step s) y z)⟩
    | congrRight a s =>
      exact ⟨_, .step (.congrRight x (.congrLeft s z)), .step (.rotate x _ z),
        .symm (.naturalMiddle x (.step s) z)⟩
  | congrRight xy s =>
    exact ⟨_, .step (.congrRight x (.congrRight y s)), .step (.rotate x y _),
      .symm (.naturalRight x y (.step s))⟩

/-- Exhaustive local coherence, recursively lifting smaller overlaps through
contexts. The only nonstructural cells used are the named local generators. -/
noncomputable def fill {α : Type u} {x y : FreeMagma α} (p : AssocStep x y) :
    {z : FreeMagma α} → (q : AssocStep x z) → CoherentPeak p q := by
  induction p with
  | rotate a b c => exact fun q => atRoot a b c q
  | congrLeft p b ih =>
    intro z q
    cases q with
    | rotate a b c => exact (atRoot _ _ _ (.congrLeft p _)).flip
    | congrLeft q b =>
      let h := ih q
      refine ⟨h.target * b, h.left.congrLeft b, h.right.congrLeft b, ?_⟩
      simpa only [AssocReduces.toRwEq_congrLeft, AssocRwEq.congrLeft] using
        AssocHigher.left b h.cell
    | congrRight a q =>
      exact ⟨_, .step (.congrRight _ q), .step (.congrLeft p _),
        .interchange (.step p) (.step q)⟩
  | congrRight a p ih =>
    intro z q
    cases q with
    | rotate a b c => exact (atRoot _ _ _ (.congrRight _ p)).flip
    | congrLeft q b =>
      exact ⟨_, .step (.congrLeft q _), .step (.congrRight _ p),
        .symm (.interchange (.step q) (.step p))⟩
    | congrRight a q =>
      let h := ih q
      refine ⟨a * h.target, h.left.congrRight a, h.right.congrRight a, ?_⟩
      simpa only [AssocReduces.toRwEq_congrRight, AssocRwEq.congrRight] using
        AssocHigher.right a h.cell

end CoherentPeak

/-- Sequential directed traces used by the well-founded comparison algorithm. -/
inductive AssocSeq {α : Type u} : FreeMagma α → FreeMagma α → Type u where
  | nil (x) : AssocSeq x x
  | cons {x y z} : AssocStep x y → AssocSeq y z → AssocSeq x z

/-- The same decreasing-weight termination argument, eliminating `Nonempty`
inside `Prop` rather than selecting a witness with classical choice. -/
theorem coherentStep_wellFounded (α : Type u) :
    WellFounded (fun y x : FreeMagma α => Nonempty (AssocStep x y)) :=
  Subrelation.wf (fun ⟨h⟩ => assocStep_weight_decreases h) (measure assocWeight).wf

namespace AssocSeq

variable {α : Type u} {w x y z : FreeMagma α}

def toTrace {x y : FreeMagma α} : AssocSeq x y → AssocRwEq x y
  | .nil _ => .refl _
  | .cons p q => .trans (.step p) q.toTrace

def append {x y z : FreeMagma α} (p : AssocSeq x y) (q : AssocSeq y z) : AssocSeq x z :=
  match p with
  | .nil _ => q
  | .cons s p => .cons s (p.append q)

def appendCell {x y z : FreeMagma α} (p : AssocSeq x y) (q : AssocSeq y z) :
    AssocHigher (.trans p.toTrace q.toTrace) (p.append q).toTrace :=
  match p, q with
  | .nil _, q => .unitLeft q.toTrace
  | .cons s p, q => .trans (.assoc (.step s) p.toTrace q.toTrace)
      (.comp (.refl (.step s)) (appendCell p q))

def ofReduces {x y : FreeMagma α} : AssocReduces x y → AssocSeq x y
  | .refl _ => .nil _
  | .step s => .cons s (.nil _)
  | .trans p q => (ofReduces p).append (ofReduces q)

def flattenCell {x y : FreeMagma α} (p : AssocReduces x y) : AssocHigher p.toRwEq (ofReduces p).toTrace :=
  match p with
  | .refl _ => .refl _
  | .step s => .symm (.unitRight (.step s))
  | .trans p q => .trans (.comp (flattenCell p) (flattenCell q))
      (appendCell (ofReduces p) (ofReduces q))

theorem word_eq (p : AssocSeq x y) : word x = word y :=
  (assoc_rwEq_iff_freeSemigroup_eq x y).mp ⟨p.toTrace⟩

theorem endpoint_eq (p : AssocSeq x y)
    (hn : ∀ {z}, AssocStep x z → False) : x = y := by
  cases p with
  | nil => rfl
  | cons s _ => exact False.elim (hn s)

/-- Normalize to any reachable irreducible target, with no choice of a trace. -/
def normalizeTo (p : AssocRwEq x y)
    (hn : ∀ {z}, AssocStep y z → False) : AssocSeq x y := by
  have hw := (assoc_rwEq_iff_freeSemigroup_eq x y).mp ⟨p⟩
  have he := (ofReduces (assocNormalization y)).endpoint_eq hn
  have hxy : rightComb (word x) = y := (_root_.congrArg rightComb hw).trans he.symm
  exact hxy ▸ ofReduces (assocNormalization x)

/-- Coherence of complete directed reductions. The recursive calls are at
strict one-step reducts of the common source; local peaks supply the cells. -/
noncomputable def terminalCoherence (x : FreeMagma α) :
    ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (p q : AssocSeq x n) → AssocHigher p.toTrace q.toTrace := by
  exact (coherentStep_wellFounded α).fix
    (C := fun x => ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (p q : AssocSeq x n) → AssocHigher p.toTrace q.toTrace) (fun x ih => by
    intro n hn p q
    cases p with
    | nil =>
      cases q with
      | nil => exact .refl _
      | cons s _ => exact False.elim (hn s)
    | @cons x y n s p =>
      cases q with
      | nil => exact False.elim (hn s)
      | @cons x z n t q =>
        let h := CoherentPeak.fill s t
        let k := normalizeTo (.trans (.symm h.left.toRwEq) p.toTrace) hn
        let l := ofReduces h.left
        let r := ofReduces h.right
        have hp := ih y ⟨s⟩ hn p (l.append k)
        have hq := ih z ⟨t⟩ hn q (r.append k)
        have hc : AssocHigher (.trans (.step s) l.toTrace)
            (.trans (.step t) r.toTrace) :=
          .trans (.comp (.refl _) (.symm (flattenCell h.left)))
            (.trans h.cell (.comp (.refl _) (flattenCell h.right)))
        exact .trans (.comp (.refl _) hp)
          (.trans (.comp (.refl _) (.symm (appendCell l k)))
          (.trans (.symm (.assoc (.step s) l.toTrace k.toTrace))
          (.trans (.comp hc (.refl _))
          (.trans (.assoc (.step t) r.toTrace k.toTrace)
          (.trans (.comp (.refl _) (appendCell r k))
            (.comp (.refl _) (.symm hq)))))))) x

end AssocSeq

namespace AssocHigher

variable {α : Type u}

/-- Every signed trace commutes with directed normalization. Inverse and
composition cases use only groupoid laws and the already proved directed
comparison; no higher coherence assumption enters the induction. -/
noncomputable def normalizationSquare {x y : FreeMagma α} (p : AssocRwEq x y) :
    ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (nx : AssocSeq x n) → (ny : AssocSeq y n) →
      AssocHigher (.trans p ny.toTrace) nx.toTrace := by
  induction p with
  | refl x =>
    intro n hn nx ny
    exact .trans (.unitLeft _) (AssocSeq.terminalCoherence x hn ny nx)
  | step s =>
    intro n hn nx ny
    exact AssocSeq.terminalCoherence _ hn (.cons s ny) nx
  | symm p ih =>
    intro n hn nx ny
    have h := ih hn ny nx
    exact .trans (.comp (.refl _) (.symm h))
      (.trans (.symm (.assoc (.symm p) p nx.toTrace))
        (.trans (.comp (.cancelRev p) (.refl _)) (.unitLeft _)))
  | trans p q ihp ihq =>
    intro n hn nx ny
    let nm := AssocSeq.normalizeTo (.trans q ny.toTrace) hn
    exact .trans (.assoc p q ny.toTrace)
      (.trans (.comp (.refl _) (ihq hn nm ny)) (ihp hn nx nm))

/-- All parallel signed associativity traces are connected by the explicitly
presented higher rewrites. This is a derived theorem, not a filler constructor. -/
noncomputable def allParallel {x y : FreeMagma α} (p q : AssocRwEq x y) :
    AssocHigher p q := by
  let ny := AssocSeq.ofReduces (assocNormalization y)
  have hn : ∀ {z}, AssocStep (rightComb (word y)) z → False :=
    fun s => rightComb_irreducible (word y) s
  let nx := AssocSeq.normalizeTo (.trans p ny.toTrace) hn
  exact compareVia ny.toTrace nx.toTrace
    (normalizationSquare p hn nx ny) (normalizationSquare q hn nx ny)

/-- Original binary reduction syntax is covered without replacing its traces
by proof-irrelevant reachability propositions. -/
noncomputable def directedParallel {x y : FreeMagma α} (p q : AssocReduces x y) :
    AssocHigher p.toRwEq q.toRwEq := allParallel p.toRwEq q.toRwEq

end AssocHigher

section Interpretation

variable {α : Type u} {A : Type v} {a : A}

/-- Evaluate a bracketed word as a composite of computational loops. -/
noncomputable def evalTree (label : α → Path a a) : FreeMagma α → Path a a
  | .of x => label x
  | .mul x y => Path.trans (evalTree label x) (evalTree label y)

/-- Every primitive rotation maps to the existing `Path.Step` rule, and
contexts map to the existing congruence rules, preserving the rewrite tree. -/
noncomputable def evalStep (label : α → Path a a) {x y : FreeMagma α} :
    AssocStep x y → Step (evalTree label x) (evalTree label y)
  | .rotate x y z => .trans_assoc (evalTree label x) (evalTree label y) (evalTree label z)
  | .congrLeft s y => .trans_congr_left (evalTree label y) (evalStep label s)
  | .congrRight x s => .trans_congr_right (evalTree label x) (evalStep label s)

/-- Interpretation retains the composition/inversion tree of the witness;
it never appeals to equality of normalizations or proof irrelevance. -/
noncomputable def evalTrace (label : α → Path a a) {x y : FreeMagma α} :
    AssocRwEq x y → RwEq (evalTree label x) (evalTree label y)
  | .refl _ => .refl _
  | .step s => .step (evalStep label s)
  | .symm p => .symm (evalTrace label p)
  | .trans p q => .trans (evalTrace label p) (evalTrace label q)

/-- A concrete multi-step bridge for the short pentagon route. -/
noncomputable def evalPentagonShort (label : α → Path a a) (w x y z : FreeMagma α) :
    RwEq (Path.trans (Path.trans (Path.trans (evalTree label w) (evalTree label x))
      (evalTree label y)) (evalTree label z))
      (Path.trans (evalTree label w) (Path.trans (evalTree label x)
        (Path.trans (evalTree label y) (evalTree label z)))) :=
  evalTrace label (pentagonShort w x y z).toRwEq

end Interpretation

end ComputationalPaths.Path.PalomarAssociativity
