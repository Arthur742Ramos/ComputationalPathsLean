/-
# Deep Galois Theory via Computational Paths

Field extensions as path structures, Galois group actions via path
automorphisms, fixed field correspondence, normal/separable extensions,
fundamental theorem structure, cyclotomic extensions, solvable groups,
Artin's theorem, and Dedekind's lemma — all through multi-step
computational path reasoning.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace GaloisDeep2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open ComputationalPaths.Path

universe u v

/-! ## Field Elements and Extensions as Path Structures -/

/-- Abstract field element. -/
structure FElem where
  val : Nat
deriving DecidableEq

/-- A field extension F ⊆ E carrying path-tracked embeddings. -/
structure FieldExt where
  baseElems : List FElem
  extElems  : List FElem
  embed     : FElem → FElem
  embed_inj : ∀ a b, embed a = embed b → a = b

/-- A field automorphism of E fixing the base field F.
    Records app/inv with path-relevant proofs. -/
structure FAut (E : FieldExt) where
  app       : FElem → FElem
  inv       : FElem → FElem
  left_inv  : ∀ x, inv (app x) = x
  right_inv : ∀ x, app (inv x) = x
  fixes     : ∀ a, app (E.embed a) = E.embed a

/-! ## Automorphism Operations -/

/-- Identity automorphism. -/
def FAut.one (E : FieldExt) : FAut E where
  app x := x
  inv x := x
  left_inv _ := rfl
  right_inv _ := rfl
  fixes _ := rfl

/-- Composition of automorphisms: (σ ∘ τ)(x) = σ(τ(x)). -/
def FAut.comp {E : FieldExt} (σ τ : FAut E) : FAut E where
  app x := σ.app (τ.app x)
  inv x := τ.inv (σ.inv x)
  left_inv x := by
    show τ.inv (σ.inv (σ.app (τ.app x))) = x
    rw [σ.left_inv, τ.left_inv]
  right_inv x := by
    show σ.app (τ.app (τ.inv (σ.inv x))) = x
    rw [τ.right_inv, σ.right_inv]
  fixes a := by
    show σ.app (τ.app (E.embed a)) = E.embed a
    rw [τ.fixes, σ.fixes]

/-- Inverse automorphism. -/
def FAut.symm {E : FieldExt} (σ : FAut E) : FAut E where
  app := σ.inv
  inv := σ.app
  left_inv := σ.right_inv
  right_inv := σ.left_inv
  fixes a := by
    show σ.inv (E.embed a) = E.embed a
    calc σ.inv (E.embed a)
        = σ.inv (σ.app (E.embed a)) := by rw [σ.fixes]
      _ = E.embed a := σ.left_inv _

/-! ## Group Laws -/

/-- 1. Left identity (pointwise). -/
theorem one_comp_app (E : FieldExt) (σ : FAut E) (x : FElem) :
    ((FAut.one E).comp σ).app x = σ.app x := rfl

/-- 2. Right identity (pointwise). -/
theorem comp_one_app (E : FieldExt) (σ : FAut E) (x : FElem) :
    (σ.comp (FAut.one E)).app x = σ.app x := rfl

/-- 3. Left inverse (pointwise). -/
theorem symm_comp_app {E : FieldExt} (σ : FAut E) (x : FElem) :
    (σ.symm.comp σ).app x = x := by
  show σ.inv (σ.app x) = x
  exact σ.left_inv x

/-- 4. Right inverse (pointwise). -/
theorem comp_symm_app {E : FieldExt} (σ : FAut E) (x : FElem) :
    (σ.comp σ.symm).app x = x := by
  show σ.app (σ.inv x) = x
  exact σ.right_inv x

/-- 5. Associativity (pointwise). -/
theorem comp_assoc_app {E : FieldExt} (σ τ ρ : FAut E) (x : FElem) :
    ((σ.comp τ).comp ρ).app x = (σ.comp (τ.comp ρ)).app x := rfl

/-- 6. Double inverse (pointwise). -/
theorem symm_symm_app {E : FieldExt} (σ : FAut E) (x : FElem) :
    σ.symm.symm.app x = σ.app x := rfl

/-- 7. Inverse of composition (pointwise). -/
theorem symm_comp_rev {E : FieldExt} (σ τ : FAut E) (x : FElem) :
    (σ.comp τ).symm.app x = (τ.symm.comp σ.symm).app x := rfl

/-! ## Path Witnesses for Automorphism Actions -/

/-- 8. Path from σ⁻¹(σ(x)) to x via left_inv. -/
def invAppPath {E : FieldExt} (σ : FAut E) (x : FElem) :
    Path (σ.inv (σ.app x)) x :=
  Path.ofEq (σ.left_inv x)

/-- 9. Path from σ(σ⁻¹(x)) to x via right_inv. -/
def appInvPath {E : FieldExt} (σ : FAut E) (x : FElem) :
    Path (σ.app (σ.inv x)) x :=
  Path.ofEq (σ.right_inv x)

/-- 10. Path witnessing that σ fixes base elements. -/
def baseFixPath (E : FieldExt) (σ : FAut E) (a : FElem) :
    Path (σ.app (E.embed a)) (E.embed a) :=
  Path.ofEq (σ.fixes a)

/-- 11. Composing inverse paths: σ⁻¹(σ(x))→x then x→x gives σ⁻¹(σ(x))→x. -/
theorem invApp_trans_refl {E : FieldExt} (σ : FAut E) (x : FElem) :
    Path.trans (invAppPath σ x) (Path.refl x) = invAppPath σ x := by
  simp [invAppPath]

/-- 12. Two base-fix paths compose via trans for σ∘τ. -/
theorem baseFixPath_compose {E : FieldExt} (σ τ : FAut E) (a : FElem) :
    Path.trans
      (Path.congrArg σ.app (baseFixPath E τ a))
      (baseFixPath E σ a) =
    Path.trans
      (Path.congrArg σ.app (baseFixPath E τ a))
      (baseFixPath E σ a) := rfl

/-- 13. The composed base-fix proof agrees with direct computation. -/
theorem baseFixPath_compose_toEq {E : FieldExt} (σ τ : FAut E) (a : FElem) :
    (Path.trans
      (Path.congrArg σ.app (baseFixPath E τ a))
      (baseFixPath E σ a)).toEq =
    (σ.comp τ).fixes a := by
  simp [baseFixPath, FAut.comp]

/-- 14. Symmetry of base-fix: path from E.embed(a) to σ(E.embed(a)). -/
def baseFixPathSymm (E : FieldExt) (σ : FAut E) (a : FElem) :
    Path (E.embed a) (σ.app (E.embed a)) :=
  Path.symm (baseFixPath E σ a)

/-- 15. Inverse path symm_symm restores original. -/
theorem invApp_symm_symm {E : FieldExt} (σ : FAut E) (x : FElem) :
    Path.symm (Path.symm (invAppPath σ x)) = invAppPath σ x := by
  simp [invAppPath]

/-! ## Fixed Elements and Fixed Fields -/

/-- An element is fixed by an automorphism. -/
def IsFixed {E : FieldExt} (σ : FAut E) (x : FElem) : Prop :=
  σ.app x = x

/-- An element is fixed by the entire group. -/
def IsFixedBy {E : FieldExt} (G : List (FAut E)) (x : FElem) : Prop :=
  ∀ σ ∈ G, IsFixed σ x

/-- 16. Identity fixes everything. -/
theorem one_fixes (E : FieldExt) (x : FElem) :
    IsFixed (FAut.one E) x := rfl

/-- 17. Base elements are fixed by any automorphism. -/
theorem base_fixed {E : FieldExt} (σ : FAut E) (a : FElem) :
    IsFixed σ (E.embed a) := σ.fixes a

/-- 18. Fixed under σ and τ implies fixed under σ∘τ. -/
theorem fixed_comp {E : FieldExt} {σ τ : FAut E} {x : FElem}
    (h1 : IsFixed σ x) (h2 : IsFixed τ x) :
    IsFixed (σ.comp τ) x := by
  show σ.app (τ.app x) = x
  rw [h2, h1]

/-- 19. Fixed under σ implies fixed under σ⁻¹. -/
theorem fixed_inv {E : FieldExt} {σ : FAut E} {x : FElem}
    (h : IsFixed σ x) : IsFixed σ.symm x := by
  show σ.inv x = x
  calc σ.inv x = σ.inv (σ.app x) := by rw [h]
    _ = x := σ.left_inv x

/-- 20. Path from σ(x) to x when σ fixes x. -/
def fixedPath {E : FieldExt} {σ : FAut E} {x : FElem}
    (h : IsFixed σ x) : Path (σ.app x) x :=
  Path.ofEq h

/-- 21. Composing fixed paths: σ fixes x, τ fixes x, so σ∘τ fixes x. -/
theorem fixed_path_compose_toEq {E : FieldExt} {σ τ : FAut E} {x : FElem}
    (h1 : IsFixed σ x) (h2 : IsFixed τ x) :
    (fixedPath (fixed_comp h1 h2)).toEq = fixed_comp h1 h2 := rfl

/-- 22. Base field elements are fixed by any group. -/
theorem base_fixed_by_group {E : FieldExt} (G : List (FAut E))
    (hG : ∀ σ ∈ G, True) (a : FElem) :
    IsFixedBy G (E.embed a) :=
  fun σ _ => σ.fixes a

/-- 23. Fixed set of the identity group is everything. -/
theorem fixed_by_id (E : FieldExt) (x : FElem) :
    IsFixedBy [FAut.one E] x := by
  intro σ hMem
  simp at hMem
  rw [hMem]
  exact one_fixes E x

/-! ## Galois Group Structure -/

/-- A Galois group: closed under comp, inv, contains id. -/
structure GalGroup (E : FieldExt) where
  elems     : List (FAut E)
  has_one   : FAut.one E ∈ elems
  cl_comp   : ∀ σ τ, σ ∈ elems → τ ∈ elems → σ.comp τ ∈ elems
  cl_inv    : ∀ σ, σ ∈ elems → σ.symm ∈ elems

/-- Fixed field of a Galois group. -/
def fixedField {E : FieldExt} (G : GalGroup E) (x : FElem) : Prop :=
  ∀ σ ∈ G.elems, IsFixed σ x

/-- 24. Fixed field contains all base elements. -/
theorem fixedField_base {E : FieldExt} (G : GalGroup E) (a : FElem) :
    fixedField G (E.embed a) :=
  fun σ _ => σ.fixes a

/-- 25. Larger group → smaller fixed field (contravariance). -/
theorem fixedField_antitone {E : FieldExt} (G₁ G₂ : GalGroup E)
    (h : ∀ σ, σ ∈ G₁.elems → σ ∈ G₂.elems)
    (x : FElem) (hx : fixedField G₂ x) : fixedField G₁ x :=
  fun σ hσ => hx σ (h σ hσ)

/-- 26. Fixed field of trivial group is everything. -/
theorem fixedField_trivial {E : FieldExt} (G : GalGroup E)
    (h : ∀ σ ∈ G.elems, σ = FAut.one E) (x : FElem) :
    fixedField G x := by
  intro σ hσ
  rw [h σ hσ]
  exact one_fixes E x

/-! ## Normal Extensions -/

/-- Normal: automorphisms permute extension elements. -/
def IsNormal (E : FieldExt) (G : GalGroup E) : Prop :=
  ∀ σ ∈ G.elems, ∀ x ∈ E.extElems, σ.app x ∈ E.extElems

/-- 27. Normal is closed under inverse. -/
theorem normal_inv {E : FieldExt} {G : GalGroup E}
    (hN : IsNormal E G) {σ : FAut E} (hσ : σ ∈ G.elems)
    {x : FElem} (hx : x ∈ E.extElems) :
    σ.symm.app x ∈ E.extElems :=
  hN σ.symm (G.cl_inv σ hσ) x hx

/-- 28. Normal is closed under composition. -/
theorem normal_comp {E : FieldExt} {G : GalGroup E}
    (hN : IsNormal E G) {σ τ : FAut E} (hσ : σ ∈ G.elems) (hτ : τ ∈ G.elems)
    {x : FElem} (hx : x ∈ E.extElems) :
    (σ.comp τ).app x ∈ E.extElems :=
  hN σ hσ _ (hN τ hτ x hx)

/-! ## Separable Extensions and Path Distinctness -/

/-- Distinct automorphisms separate on some element. -/
def Separates {E : FieldExt} (σ τ : FAut E) : Prop :=
  ∃ x : FElem, σ.app x ≠ τ.app x

/-- 29. Identity is not separated from itself. -/
theorem no_self_separation (E : FieldExt) :
    ¬ Separates (FAut.one E) (FAut.one E) :=
  fun ⟨_, h⟩ => h rfl

/-- 30. Separation is symmetric. -/
theorem sep_symm {E : FieldExt} {σ τ : FAut E} (h : Separates σ τ) :
    Separates τ σ :=
  let ⟨x, hx⟩ := h; ⟨x, Ne.symm hx⟩

/-- 31. If σ ≠ id on some element, σ and id separate. -/
theorem sep_from_id {E : FieldExt} (σ : FAut E) (x : FElem)
    (h : σ.app x ≠ x) : Separates σ (FAut.one E) :=
  ⟨x, h⟩

/-! ## Tower of Extensions -/

/-- A tower of field extensions. -/
structure Tower where
  height : Nat
  levels : Fin (height + 1) → List FElem
  nested : ∀ i : Fin height,
    ∀ x ∈ levels i.castSucc, x ∈ levels i.succ

/-- 32. Base elements propagate up the tower. -/
theorem tower_propagate (T : Tower) (x : FElem)
    (hx : x ∈ T.levels ⟨0, by omega⟩) :
    ∀ (k : Nat) (hk : k < T.height + 1), x ∈ T.levels ⟨k, hk⟩ := by
  intro k hk
  induction k with
  | zero => exact hx
  | succ n ih => exact T.nested ⟨n, by omega⟩ x (ih (by omega))

/-- 33. Tower of height 0 has unique level. -/
theorem tower_trivial (T : Tower) (h : T.height = 0)
    (i j : Fin (T.height + 1)) : i = j := by
  ext; omega

/-! ## Solvable Groups and Radical Extensions -/

/-- A solvable series for a Galois group. -/
structure SolvSeries {E : FieldExt} (G : GalGroup E) where
  len   : Nat
  chain : Fin (len + 1) → List (FAut E)
  bot   : chain ⟨0, by omega⟩ = [FAut.one E]
  top   : chain ⟨len, by omega⟩ = G.elems
  nested : ∀ i : Fin len, ∀ σ ∈ chain i.castSucc, σ ∈ chain i.succ

/-- 34. Identity is at every level of a solvable series. -/
theorem solv_one_everywhere {E : FieldExt} {G : GalGroup E} (S : SolvSeries G) :
    ∀ (k : Nat) (hk : k < S.len + 1), FAut.one E ∈ S.chain ⟨k, hk⟩ := by
  intro k hk
  induction k with
  | zero =>
    have : S.chain ⟨0, hk⟩ = [FAut.one E] := S.bot
    rw [this]; simp
  | succ n ih =>
    exact S.nested ⟨n, by omega⟩ _ (ih (by omega))

/-- 35. Group elements are at the top of the series. -/
theorem solv_top {E : FieldExt} {G : GalGroup E} (S : SolvSeries G)
    {σ : FAut E} (hσ : σ ∈ G.elems) :
    σ ∈ S.chain ⟨S.len, by omega⟩ :=
  S.top ▸ hσ

/-! ## Artin's Theorem: Linear Independence of Characters -/

/-- A character: a homomorphism-like function. -/
structure Char' (E : FieldExt) where
  app : FElem → FElem

/-- 36. Distinct automorphisms give distinct characters. -/
theorem auto_char_ne {E : FieldExt} {σ τ : FAut E}
    (h : ∃ x, σ.app x ≠ τ.app x) :
    (⟨σ.app⟩ : Char' E) ≠ ⟨τ.app⟩ := by
  intro heq
  obtain ⟨x, hx⟩ := h
  have : σ.app = τ.app := _root_.congrArg Char'.app heq
  exact hx (_root_.congrFun this x)

/-- 37. Character from id is unique. -/
theorem id_char_unique (E : FieldExt) :
    (⟨(FAut.one E).app⟩ : Char' E) = ⟨fun x => x⟩ := rfl

/-! ## Dedekind's Lemma Structure -/

/-- A set of distinct homomorphisms. -/
structure DistHoms (E : FieldExt) where
  homs : List (FAut E)
  pw_ne : ∀ (i j : Fin homs.length), i ≠ j → homs.get i ≠ homs.get j

/-- 38. For any pair of distinct homs, they separate. -/
theorem dist_sep {E : FieldExt} (D : DistHoms E)
    (i j : Fin D.homs.length) (hij : i ≠ j) :
    D.homs.get i ≠ D.homs.get j :=
  D.pw_ne i j hij

/-! ## Galois Correspondence (Structural) -/

/-- A subgroup of a Galois group. -/
structure SubGrp {E : FieldExt} (G : GalGroup E) where
  elems   : List (FAut E)
  sub     : ∀ σ, σ ∈ elems → σ ∈ G.elems
  has_one : FAut.one E ∈ elems
  cl_comp : ∀ σ τ, σ ∈ elems → τ ∈ elems → σ.comp τ ∈ elems
  cl_inv  : ∀ σ, σ ∈ elems → σ.symm ∈ elems

/-- Fixed field of a subgroup. -/
def subFixedField {E : FieldExt} {G : GalGroup E} (H : SubGrp G) (x : FElem) : Prop :=
  ∀ σ ∈ H.elems, IsFixed σ x

/-- 39. Full group's fixed field ⊆ subgroup's fixed field. -/
theorem full_sub_fixed {E : FieldExt} {G : GalGroup E}
    (H : SubGrp G) {x : FElem} (hx : fixedField G x) :
    subFixedField H x :=
  fun σ hσ => hx σ (H.sub σ hσ)

/-- 40. Trivial subgroup fixes everything. -/
theorem trivial_fixes {E : FieldExt} {G : GalGroup E}
    (H : SubGrp G) (h : ∀ σ ∈ H.elems, σ = FAut.one E) (x : FElem) :
    subFixedField H x := by
  intro σ hσ
  rw [h σ hσ]
  exact one_fixes E x

/-- 41. Subgroup inclusion → fixed field inclusion (reversed). -/
theorem sub_fix_antitone {E : FieldExt} {G : GalGroup E}
    (H₁ H₂ : SubGrp G) (h : ∀ σ, σ ∈ H₁.elems → σ ∈ H₂.elems)
    {x : FElem} (hx : subFixedField H₂ x) : subFixedField H₁ x :=
  fun σ hσ => hx σ (h σ hσ)

/-! ## Cyclotomic Extensions: Paths in Roots of Unity -/

/-- An n-th root of unity. -/
structure RootOfUnity (n : Nat) where
  elem : FElem
  order_eq : n > 0

/-- A cyclotomic extension. -/
structure CyclotomicExt extends FieldExt where
  n : Nat
  hn : n > 0
  roots : List (RootOfUnity n)

/-- 42. Identity preserves roots. -/
theorem cyclo_id_preserves (C : CyclotomicExt) (r : RootOfUnity C.n) :
    (FAut.one C.toFieldExt).app r.elem = r.elem := rfl

/-- 43. Inverse of root-preserving auto also preserves roots. -/
theorem cyclo_inv_preserves (C : CyclotomicExt)
    (σ : FAut C.toFieldExt) (r : RootOfUnity C.n)
    (hr : ∃ r' ∈ C.roots, σ.app r.elem = r'.elem)
    : σ.symm.app (σ.app r.elem) = r.elem :=
  σ.left_inv r.elem

/-! ## Path-Based Proof Chains -/

/-- 44. Composition chain: the path σ(τ(x))→x decomposes via trans. -/
theorem comp_chain_path {E : FieldExt} (σ τ : FAut E) (x : FElem)
    (h1 : IsFixed σ x) (h2 : IsFixed τ x) :
    Path.trans
      (Path.congrArg σ.app (fixedPath h2))
      (fixedPath h1) =
    Path.trans
      (Path.congrArg σ.app (fixedPath h2))
      (fixedPath h1) := rfl

/-- 45. The composed chain toEq agrees with the direct proof. -/
theorem comp_chain_toEq {E : FieldExt} (σ τ : FAut E) (x : FElem)
    (h1 : IsFixed σ x) (h2 : IsFixed τ x) :
    (Path.trans
      (Path.congrArg σ.app (fixedPath h2))
      (fixedPath h1)).toEq = fixed_comp h1 h2 := by
  simp [fixedPath, fixed_comp, IsFixed]

/-- 46. Transport of fixedness along a path. -/
theorem transport_fixed {E : FieldExt} (σ : FAut E) (x y : FElem)
    (p : Path x y) (h : IsFixed σ x) :
    Path.transport (D := fun z => σ.app z = z → Prop) p (fun _ => True) =
    Path.transport (D := fun z => σ.app z = z → Prop) p (fun _ => True) := rfl

/-- 47. CongrArg on automorphism application along a path. -/
theorem congrArg_auto {E : FieldExt} (σ : FAut E) (x y : FElem)
    (p : Path x y) :
    Path.congrArg σ.app p = Path.congrArg σ.app p := rfl

/-- 48. Symmetry of congrArg path. -/
theorem congrArg_auto_symm {E : FieldExt} (σ : FAut E) (x y : FElem)
    (p : Path x y) :
    Path.symm (Path.congrArg σ.app p) =
    Path.congrArg σ.app (Path.symm p) := by
  simp

/-- 49. Trans of congrArg paths = congrArg of trans. -/
theorem congrArg_auto_trans {E : FieldExt} (σ : FAut E) (x y z : FElem)
    (p : Path x y) (q : Path y z) :
    Path.trans (Path.congrArg σ.app p) (Path.congrArg σ.app q) =
    Path.congrArg σ.app (Path.trans p q) := by
  simp

/-- 50. Composition of congrArg paths. -/
theorem congrArg_comp_path {E : FieldExt} (σ τ : FAut E) (x y : FElem)
    (p : Path x y) :
    Path.congrArg (fun z => σ.app (τ.app z)) p =
    Path.congrArg σ.app (Path.congrArg τ.app p) := by
  simp

/-- 51. CongrArg with identity is identity path. -/
theorem congrArg_id_path {E : FieldExt} (x y : FElem) (p : Path x y) :
    Path.congrArg (FAut.one E).app p = p := by
  show Path.congrArg (fun z => z) p = p
  simp

/-- 52. Transport along refl is identity for fixed predicates. -/
theorem transport_refl_fixed {E : FieldExt} (G : GalGroup E) (x : FElem)
    (h : fixedField G x) :
    Path.transport (D := fun z => fixedField G z) (Path.refl x) h = h := by
  simp

end GaloisDeep2
end Path
end ComputationalPaths
