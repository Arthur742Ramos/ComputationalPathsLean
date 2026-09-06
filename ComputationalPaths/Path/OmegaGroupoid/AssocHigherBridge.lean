import ComputationalPaths.Path.OmegaGroupoid.AssocHigher
import ComputationalPaths.Path.OmegaGroupoid

/-!
# Native computational-path interpretation of associativity coherence

This module compares the explicit free-magma certificate with the existing
`OmegaGroupoid` cell presentation. Named native pentagon and interchange
generators are used directly, not the general contractibility theorem or
proof-irrelevant transport filler.
-/

namespace ComputationalPaths.Path.PalomarAssociativity

open OmegaGroupoid

universe u v

variable {α : Type u} {A : Type v} {a : A}

/-- The trace interpretation reified in the actual native 2-cell type. -/
noncomputable def eval₂ (label : α → Path a a) {x y : FreeMagma α}
    (p : AssocRwEq x y) : Derivation₂ (evalTree label x) (evalTree label y) :=
  Derivation₂.ofRwEq (evalTrace label p)

@[simp] theorem eval₂_refl (label : α → Path a a) (x : FreeMagma α) :
    eval₂ label (.refl x) = .refl (evalTree label x) := rfl

@[simp] theorem eval₂_step (label : α → Path a a) {x y : FreeMagma α}
    (s : AssocStep x y) : eval₂ label (.step s) = .step (evalStep label s) := rfl

@[simp] theorem eval₂_trans (label : α → Path a a) {x y z : FreeMagma α}
    (p : AssocRwEq x y) (q : AssocRwEq y z) :
    eval₂ label (.trans p q) = .vcomp (eval₂ label p) (eval₂ label q) := rfl

@[simp] theorem eval₂_symm (label : α → Path a a) {x y : FreeMagma α}
    (p : AssocRwEq x y) : eval₂ label (.symm p) = .inv (eval₂ label p) := rfl

@[simp] theorem eval₂_left (label : α → Path a a) {x x' : FreeMagma α}
    (p : AssocRwEq x x') (y : FreeMagma α) :
    eval₂ label (p.congrLeft y) = OmegaGroupoid.whiskerRight (eval₂ label p) (evalTree label y) := by
  induction p with
  | refl => rfl
  | step => rfl
  | symm p ih => exact _root_.congrArg Derivation₂.inv ih
  | trans p q hp hq => exact _root_.congrArg₂ Derivation₂.vcomp hp hq

@[simp] theorem eval₂_right (label : α → Path a a) (x : FreeMagma α)
    {y y' : FreeMagma α} (p : AssocRwEq y y') :
    eval₂ label (p.congrRight x) = OmegaGroupoid.whiskerLeft (evalTree label x) (eval₂ label p) := by
  induction p with
  | refl => rfl
  | step => rfl
  | symm p ih => exact _root_.congrArg Derivation₂.inv ih
  | trans p q hp hq => exact _root_.congrArg₂ Derivation₂.vcomp hp hq

/-- The two-edge/three-edge source pentagon maps to the named native pentagon
followed by one structural reassociation of the three-edge history. -/
noncomputable def nativePentagon (label : α → Path a a) (w x y z : FreeMagma α) :
    Derivation₃ (eval₂ label (pentagonShort w x y z).toRwEq)
      (eval₂ label (pentagonLong w x y z).toRwEq) :=
  .vcomp (.step (.pentagon (evalTree label w) (evalTree label x)
    (evalTree label y) (evalTree label z)))
    (.step (.vcomp_assoc _ _ _))

/-- Independent rewriting maps to the existing native interchange cell,
with arbitrary signed traces in each branch. -/
noncomputable def nativeInterchange (label : α → Path a a)
    {x x' y y' : FreeMagma α} (p : AssocRwEq x x') (q : AssocRwEq y y') :
    Derivation₃ (eval₂ label (.trans (p.congrLeft y) (q.congrRight x')))
      (eval₂ label (.trans (q.congrRight x) (p.congrLeft y'))) := by
  simp only [eval₂_trans, eval₂_left, eval₂_right]
  exact Derivation₃.step (MetaStep₃.interchange (eval₂ label p) (eval₂ label q))

/-- Native 3-cells with the source trace boundary retained in their type. -/
structure NativeCell (label : α → Path a a) {x y : FreeMagma α}
    (p q : AssocRwEq x y) where
  witness : Derivation₃ (eval₂ label p) (eval₂ label q)

namespace NativeCell

variable {label : α → Path a a} {w x y z : FreeMagma α}

noncomputable def refl (p : AssocRwEq x y) : NativeCell label p p := ⟨.refl _⟩
noncomputable def symm {p q : AssocRwEq x y} (h : NativeCell label p q) :
    NativeCell label q p := ⟨.inv h.witness⟩
noncomputable def trans {p q r : AssocRwEq x y}
    (h : NativeCell label p q) (k : NativeCell label q r) : NativeCell label p r :=
  ⟨.vcomp h.witness k.witness⟩
noncomputable def comp {p p' : AssocRwEq x y} {q q' : AssocRwEq y z}
    (h : NativeCell label p p') (k : NativeCell label q q') :
    NativeCell label (.trans p q) (.trans p' q') :=
  ⟨.vcomp (Derivation₃.whiskerRight₃ h.witness (eval₂ label q))
    (Derivation₃.whiskerLeft₃ (eval₂ label p') k.witness)⟩
noncomputable def assoc (p : AssocRwEq w x) (q : AssocRwEq x y) (r : AssocRwEq y z) :
    NativeCell label (.trans (.trans p q) r) (.trans p (.trans q r)) :=
  ⟨.step (.vcomp_assoc _ _ _)⟩
noncomputable def unitLeft (p : AssocRwEq x y) : NativeCell label (.trans (.refl x) p) p :=
  ⟨.step (.vcomp_refl_left _)⟩
noncomputable def unitRight (p : AssocRwEq x y) : NativeCell label (.trans p (.refl y)) p :=
  ⟨.step (.vcomp_refl_right _)⟩
noncomputable def cancel (p : AssocRwEq x y) :
    NativeCell label (.trans p (.symm p)) (.refl x) := ⟨.step (.vcomp_inv_right _)⟩
noncomputable def cancelRev (p : AssocRwEq x y) :
    NativeCell label (.trans (.symm p) p) (.refl y) := ⟨.step (.vcomp_inv_left _)⟩

noncomputable def eraseSuffix (p : AssocRwEq x y) (r : AssocRwEq y z) :
    NativeCell label (.trans (.trans p r) (.symm r)) p :=
  .trans (.assoc p r (.symm r))
    (.trans (.comp (.refl p) (.cancel r)) (.unitRight p))

noncomputable def cancelSuffix {p q : AssocRwEq x y} (r : AssocRwEq y z)
    (h : NativeCell label (.trans p r) (.trans q r)) : NativeCell label p q :=
  .trans (.symm (eraseSuffix p r))
    (.trans (.comp h (.refl (.symm r))) (eraseSuffix q r))

noncomputable def appendCell {x y z : FreeMagma α} (p : AssocSeq x y) (q : AssocSeq y z) :
    NativeCell label (.trans p.toTrace q.toTrace) (p.append q).toTrace :=
  match p, q with
  | .nil _, q => .unitLeft q.toTrace
  | .cons s p, q => .trans (.assoc (.step s) p.toTrace q.toTrace)
      (.comp (.refl (.step s)) (appendCell p q))

noncomputable def flattenCell {x y : FreeMagma α} (p : AssocReduces x y) :
    NativeCell label p.toRwEq (AssocSeq.ofReduces p).toTrace :=
  match p with
  | .refl _ => .refl _
  | .step s => .symm (.unitRight (.step s))
  | .trans p q => .trans (.comp (flattenCell p) (flattenCell q))
      (appendCell (AssocSeq.ofReduces p) (AssocSeq.ofReduces q))

end NativeCell

/-- Directed source traces interpreted as the native tail-based step closure. -/
noncomputable def evalStar (label : α → Path a a) {x y : FreeMagma α} :
    AssocReduces x y → StepStar (evalTree label x) (evalTree label y)
  | .refl _ => .refl _
  | .step s => .tail (.refl _) (evalStep label s)
  | .trans p q => stepstar_append (evalStar label p) (evalStar label q)

/-- Rebracketing of the native tail representation uses only groupoid syntax
laws; it does not collapse the derivations through equality proofs. -/
noncomputable def evalStarCell (label : α → Path a a) {x y : FreeMagma α}
    (p : AssocReduces x y) :
    Derivation₃ (derivation₂_of_stepstar (evalStar label p)) (eval₂ label p.toRwEq) :=
  match p with
  | .refl _ => .refl _
  | .step s => .step (.vcomp_refl_left _)
  | .trans p q => .vcomp (derivation₂_of_stepstar_append₃ (evalStar label p) (evalStar label q))
      (.vcomp (Derivation₃.whiskerRight₃ (evalStarCell label p)
        (derivation₂_of_stepstar (evalStar label q)))
        (Derivation₃.whiskerLeft₃ (eval₂ label p.toRwEq) (evalStarCell label q)))

/-- Each exhaustively classified source peak gives an actual native diamond
with exactly the explicit directed joining tails, including contextual peaks. -/
noncomputable def nativePeak (label : α → Path a a) {x y z : FreeMagma α}
    {s : AssocStep x y} {t : AssocStep x z} (h : CoherentPeak s t) :
    NativeCell label (.trans (.step s) h.left.toRwEq) (.trans (.step t) h.right.toRwEq) :=
  ⟨.vcomp (.inv (Derivation₃.whiskerLeft₃ (.step (evalStep label s)) (evalStarCell label h.left)))
    (.vcomp (.step (.diamond_filler (evalStep label s) (evalStep label t)
      (evalStar label h.left) (evalStar label h.right)))
      (Derivation₃.whiskerLeft₃ (.step (evalStep label t)) (evalStarCell label h.right)))⟩

namespace NativeCell

variable {label : α → Path a a}

/-- Replay the terminating local-peak comparison in actual native 3-cells.
Only explicit local diamonds and structural composition cells are used. -/
noncomputable def terminalCoherence (x : FreeMagma α) :
    ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (p q : AssocSeq x n) → NativeCell label p.toTrace q.toTrace := by
  exact (coherentStep_wellFounded α).fix
    (C := fun x => ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (p q : AssocSeq x n) → NativeCell label p.toTrace q.toTrace) (fun x ih => by
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
        let k := AssocSeq.normalizeTo (.trans (.symm h.left.toRwEq) p.toTrace) hn
        let l := AssocSeq.ofReduces h.left
        let r := AssocSeq.ofReduces h.right
        have hp := ih y ⟨s⟩ hn p (l.append k)
        have hq := ih z ⟨t⟩ hn q (r.append k)
        have hc : NativeCell label (.trans (.step s) l.toTrace)
            (.trans (.step t) r.toTrace) :=
          .trans (.comp (.refl _) (.symm (flattenCell h.left)))
            (.trans (nativePeak label h) (.comp (.refl _) (flattenCell h.right)))
        exact .trans (.comp (.refl _) hp)
          (.trans (.comp (.refl _) (.symm (appendCell l k)))
          (.trans (.symm (.assoc (.step s) l.toTrace k.toTrace))
          (.trans (.comp hc (.refl _))
          (.trans (.assoc (.step t) r.toTrace k.toTrace)
          (.trans (.comp (.refl _) (appendCell r k))
            (.comp (.refl _) (.symm hq)))))))) x

noncomputable def normalizationSquare {x y : FreeMagma α} (p : AssocRwEq x y) :
    ∀ {n : FreeMagma α}, (∀ {z}, AssocStep n z → False) →
      (nx : AssocSeq x n) → (ny : AssocSeq y n) →
      NativeCell label (.trans p ny.toTrace) nx.toTrace := by
  induction p with
  | refl x =>
    intro n hn nx ny
    exact .trans (.unitLeft _) (terminalCoherence x hn ny nx)
  | step s =>
    intro n hn nx ny
    exact terminalCoherence _ hn (.cons s ny) nx
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

/-- Native higher coherence for all interpreted source traces, derived from
their local diamonds. No native arbitrary-parallel filler is invoked. -/
noncomputable def allParallel {x y : FreeMagma α} (p q : AssocRwEq x y) :
    NativeCell label p q := by
  let ny := AssocSeq.ofReduces (assocNormalization y)
  have hn : ∀ {z}, AssocStep (rightComb (word y)) z → False :=
    fun s => rightComb_irreducible (word y) s
  let nx := AssocSeq.normalizeTo (.trans p ny.toTrace) hn
  exact cancelSuffix ny.toTrace
    (.trans (normalizationSquare p hn nx ny) (.symm (normalizationSquare q hn nx ny)))

end NativeCell

/-- A higher-cell bridge into the existing computational-path tower. -/
noncomputable def nativeAllParallel (label : α → Path a a)
    {x y : FreeMagma α} (p q : AssocRwEq x y) :
    Derivation₃ (eval₂ label p) (eval₂ label q) :=
  (NativeCell.allParallel (label := label) p q).witness

/-- Interpret each higher generator in the native tower. Structural operations,
pentagon and interchange use their corresponding native operations. Context
and naturality cases use the derived local-diamond comparison above, since the
native presentation has no primitive horizontal 3-cell/naturality constructor.
This is a map of presented witnesses, not a claimed faithful higher functor. -/
noncomputable def evalHigher (label : α → Path a a) {x y : FreeMagma α}
    {p q : AssocRwEq x y} (h : AssocHigher p q) :
    Derivation₃ (eval₂ label p) (eval₂ label q) := by
  induction h with
  | refl p => exact .refl _
  | symm h ih => exact .inv ih
  | trans h k ih ik => exact .vcomp ih ik
  | comp h k ih ik =>
    exact .vcomp (Derivation₃.whiskerRight₃ ih _) (Derivation₃.whiskerLeft₃ _ ik)
  | inv h ih => exact Derivation₃.inv_congr₃ ih
  | left y h ih => exact nativeAllParallel label _ _
  | right x h ih => exact nativeAllParallel label _ _
  | assoc p q r => exact .step (.vcomp_assoc _ _ _)
  | unitLeft p => exact .step (.vcomp_refl_left _)
  | unitRight p => exact .step (.vcomp_refl_right _)
  | cancel p => exact .step (.vcomp_inv_right _)
  | cancelRev p => exact .step (.vcomp_inv_left _)
  | invRefl x =>
    exact .vcomp (.inv (.step (.vcomp_refl_right (.inv (.refl _)))))
      (.step (.vcomp_inv_left (.refl _)))
  | invInv p => exact .step (.inv_inv _)
  | invComp p q => exact .step (.inv_vcomp _ _)
  | pentagon w x y z => exact nativePentagon label w x y z
  | interchange p q => exact nativeInterchange label p q
  | naturalLeft p y z => exact nativeAllParallel label _ _
  | naturalMiddle x p z => exact nativeAllParallel label _ _
  | naturalRight x y p => exact nativeAllParallel label _ _

/-- The higher interpretation has exactly the existing `RwEq₃` interface,
whose boundaries are the actual `RwEq` witnesses produced by `evalTrace`. -/
noncomputable def evalHigherRwEq (label : α → Path a a) {x y : FreeMagma α}
    {p q : AssocRwEq x y} (h : AssocHigher p q) :
    OmegaGroupoid.RwEq₃ (evalTrace label p) (evalTrace label q) :=
  evalHigher label h

@[simp] theorem eval₂_toRwEq (label : α → Path a a) {x y : FreeMagma α}
    (p : AssocRwEq x y) : (eval₂ label p).toRwEq = evalTrace label p := by
  induction p with
  | refl => rfl
  | step => rfl
  | symm p ih => exact _root_.congrArg RwEq.symm ih
  | trans p q hp hq => exact _root_.congrArg₂ RwEq.trans hp hq

end ComputationalPaths.Path.PalomarAssociativity
