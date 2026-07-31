/-
# Open core-face stars in topological simplices

This module defines the point-set neighborhoods used to trivialize realized
simplicial coverings.  A core face consists of a face inclusion followed by a
degeneracy onto a fixed simplex.  Its open neighborhood consists of points for
which every barycentric mass over a core vertex is strictly larger than the
largest coordinate outside the face.  The natural core-simplex star uses the
smaller total-outside refinement, because simplex degeneracies sum coordinates
in each fiber.

Unlike a naive vertex star, these neighborhoods are stable under degeneracy:
coordinates which a degeneracy identifies are summed before the strict
inequality is tested.
-/

import ComputationalPaths.Path.Homotopy.TopologicalRealizationOpen
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

/-- Summing coordinates after a simplex map is the same as summing over
the inverse image of the selected target coordinates. -/
theorem sum_toTopMap_filter {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (p : ⦋m⦌.toTopObj)
    (P : Fin (n + 1) → Prop) [DecidablePred P] :
    ∑ i ∈ Finset.univ.filter P, toTopMap f p i =
      ∑ j ∈ Finset.univ.filter (fun j => P (f.toOrderHom j)), p j := by
  classical
  simp only [coe_toTopMap]
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr
    · ext j
      simp
      change P (f.toOrderHom j) ↔ P (f.toOrderHom j)
      rfl
    · intro i hi
      rfl
  · exact Set.pairwiseDisjoint_filter _ _ _

/-- The finite epi-mono image factorization of a map of standard simplices. -/
structure FiniteImage {d n : ℕ} (u : ⦋d⦌ ⟶ ⦋n⦌) where
  dim : ℕ
  epi : ⦋d⦌ ⟶ ⦋dim⦌
  face : ⦋dim⦌ ⟶ ⦋n⦌
  epi_surjective : Function.Surjective epi.toOrderHom
  face_injective : Function.Injective face.toOrderHom
  fac : epi ≫ face = u

/-- Construct the image factorization by increasingly enumerating the finite
range of the underlying monotone map. -/
noncomputable def finiteImage {d n : ℕ} (u : ⦋d⦌ ⟶ ⦋n⦌) :
    FiniteImage u := by
  classical
  let B : Finset (Fin (n + 1)) :=
    Finset.univ.image u.toOrderHom
  have hB : B.Nonempty :=
    ⟨u.toOrderHom 0, by simp [B]⟩
  let r := B.card - 1
  have hcard : B.card = r + 1 := by
    have hpos := hB.card_pos
    dsimp [r]
    omega
  let eFun : Fin (d + 1) → Fin (r + 1) := fun x =>
    (B.orderIsoOfFin hcard).symm
      ⟨u.toOrderHom x, by simp [B]⟩
  have eMono : Monotone eFun := by
    intro x y hxy
    exact (B.orderIsoOfFin hcard).symm.monotone
      (u.toOrderHom.monotone hxy)
  let e : ⦋d⦌ ⟶ ⦋r⦌ :=
    SimplexCategory.mkHom ⟨eFun, eMono⟩
  let a : ⦋r⦌ ⟶ ⦋n⦌ :=
    SimplexCategory.mkHom
      (B.orderEmbOfFin hcard).toOrderHom
  refine
    { dim := r
      epi := e
      face := a
      epi_surjective := ?_
      face_injective := (B.orderEmbOfFin hcard).injective
      fac := ?_ }
  · intro i
    have hi : B.orderEmbOfFin hcard i ∈ B :=
      B.orderEmbOfFin_mem hcard i
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hi
    refine ⟨x, ?_⟩
    change eFun x = i
    rw [← (B.orderIsoOfFin hcard).symm_apply_apply i]
    apply congrArg (B.orderIsoOfFin hcard).symm
    apply Subtype.ext
    exact hx
  · ext x
    dsimp [e, a]
    exact congrArg Fin.val
      (congrArg Subtype.val
        ((B.orderIsoOfFin hcard).apply_symm_apply
          ⟨u.toOrderHom x, by simp [B]⟩))

/-- A nonempty inverse image of a face, increasingly enumerated as a standard
simplex. -/
structure FiniteFacePreimage {m n d : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (a : ⦋d⦌ ⟶ ⦋n⦌) where
  dim : ℕ
  face : ⦋dim⦌ ⟶ ⦋m⦌
  toFace : ⦋dim⦌ ⟶ ⦋d⦌
  face_injective : Function.Injective face.toOrderHom
  fac : face ≫ f = toFace ≫ a
  range_face :
    Set.range face.toOrderHom =
      {j | f.toOrderHom j ∈ Set.range a.toOrderHom}

/-- Construct the finite inverse image of an injective simplex map. -/
noncomputable def finiteFacePreimage {m n d : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (a : ⦋d⦌ ⟶ ⦋n⦌)
    (ha : Function.Injective a.toOrderHom)
    (hne : Set.Nonempty
      {j | f.toOrderHom j ∈ Set.range a.toOrderHom}) :
    FiniteFacePreimage f a := by
  classical
  let B : Finset (Fin (n + 1)) :=
    Finset.univ.image a.toOrderHom
  have hBcard : B.card = d + 1 := by
    dsimp [B]
    exact (Finset.card_image_of_injective Finset.univ ha).trans
      (by simp)
  let aEmb : Fin (d + 1) ↪o Fin (n + 1) :=
    OrderEmbedding.ofStrictMono a.toOrderHom
      (a.toOrderHom.monotone.strictMono_of_injective ha)
  have haEmb : aEmb = B.orderEmbOfFin hBcard := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    simp [B, aEmb]
  let A : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun j => f.toOrderHom j ∈ B)
  have hA : A.Nonempty := by
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [B, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range] using hj
  let r := A.card - 1
  have hAcard : A.card = r + 1 := by
    have hpos := hA.card_pos
    dsimp [r]
    omega
  let bEmb : Fin (r + 1) ↪o Fin (m + 1) :=
    A.orderEmbOfFin hAcard
  let b : ⦋r⦌ ⟶ ⦋m⦌ :=
    SimplexCategory.mkHom bEmb.toOrderHom
  let gFun : Fin (r + 1) → Fin (d + 1) := fun x =>
    (B.orderIsoOfFin hBcard).symm
      ⟨f.toOrderHom (bEmb x), by
        have hx : bEmb x ∈ A :=
          A.orderEmbOfFin_mem hAcard x
        simpa only [A, Finset.mem_filter, Finset.mem_univ,
          true_and] using hx⟩
  have gMono : Monotone gFun := by
    intro x y hxy
    exact (B.orderIsoOfFin hBcard).symm.monotone
      (f.toOrderHom.monotone (bEmb.monotone hxy))
  let g : ⦋r⦌ ⟶ ⦋d⦌ :=
    SimplexCategory.mkHom ⟨gFun, gMono⟩
  refine
    { dim := r
      face := b
      toFace := g
      face_injective := bEmb.injective
      fac := ?_
      range_face := ?_ }
  · ext x
    dsimp [b, g]
    have happly :=
      congrArg Subtype.val
        ((B.orderIsoOfFin hBcard).apply_symm_apply
          ⟨f.toOrderHom (bEmb x), by
            have hx : bEmb x ∈ A :=
              A.orderEmbOfFin_mem hAcard x
            simpa only [A, Finset.mem_filter, Finset.mem_univ,
              true_and] using hx⟩)
    have ha_point :
        a.toOrderHom (gFun x) =
          B.orderEmbOfFin hBcard (gFun x) :=
      congrArg (fun e : Fin (d + 1) ↪o Fin (n + 1) =>
        e (gFun x)) haEmb
    exact congrArg Fin.val (happly.symm.trans ha_point.symm)
  · have hbRange :
        Set.range b.toOrderHom =
          (A : Set (Fin (m + 1))) :=
      Finset.range_orderEmbOfFin A hAcard
    rw [hbRange]
    ext j
    simp only [Finset.mem_coe, A, Finset.mem_filter,
      Finset.mem_univ, true_and, B, Finset.mem_image,
      Set.mem_range]
    simp

/-- The face spanned by the positive barycentric coordinates of a point. -/
structure PositiveSupportFace {n : ℕ} (p : ⦋n⦌.toTopObj) where
  dim : ℕ
  face : ⦋dim⦌ ⟶ ⦋n⦌
  face_injective : Function.Injective face.toOrderHom
  range_face :
    Set.range face.toOrderHom = {i | 0 < p i}

/-- Increasing enumeration of the positive support of a barycentric point. -/
noncomputable def positiveSupportFace {n : ℕ} (p : ⦋n⦌.toTopObj) :
    PositiveSupportFace p := by
  classical
  let A : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i => 0 < p i)
  have hA : A.Nonempty := by
    by_contra h
    have hzero (i : Fin (n + 1)) : p i = 0 := by
      have hi : i ∉ A := by
        rw [Finset.not_nonempty_iff_eq_empty.mp h]
        simp
      simp only [A, Finset.mem_filter, Finset.mem_univ,
        true_and, not_lt] at hi
      exact le_antisymm hi bot_le
    have hp : ∑ i, p i = 0 := by simp [hzero]
    rw [p.2] at hp
    exact one_ne_zero hp
  let r := A.card - 1
  have hcard : A.card = r + 1 := by
    have hpos := hA.card_pos
    dsimp [r]
    omega
  let emb : Fin (r + 1) ↪o Fin (n + 1) :=
    A.orderEmbOfFin hcard
  let face : ⦋r⦌ ⟶ ⦋n⦌ :=
    SimplexCategory.mkHom emb.toOrderHom
  refine
    { dim := r
      face := face
      face_injective := emb.injective
      range_face := ?_ }
  rw [show Set.range face.toOrderHom =
      (A : Set (Fin (n + 1))) by
    exact Finset.range_orderEmbOfFin A hcard]
  ext i
  change (i ∈ A) ↔ 0 < p i
  simp [A]

theorem positiveSupportFace_pos {n : ℕ} (p : ⦋n⦌.toTopObj)
    (i : Fin ((positiveSupportFace p).dim + 1)) :
    0 < p ((positiveSupportFace p).face.toOrderHom i) := by
  have hi :
      (positiveSupportFace p).face.toOrderHom i ∈
        Set.range (positiveSupportFace p).face.toOrderHom :=
    ⟨i, rfl⟩
  rw [(positiveSupportFace p).range_face] at hi
  exact hi

theorem positiveSupportFace_eq_zero_of_notMem {n : ℕ}
    (p : ⦋n⦌.toTopObj) (i : Fin (n + 1))
    (hi : i ∉ Set.range (positiveSupportFace p).face.toOrderHom) :
    p i = 0 := by
  have hi' : ¬ 0 < p i := by
    simpa only [(positiveSupportFace p).range_face] using hi
  exact le_antisymm (not_lt.mp hi') bot_le

end SimplexCategory

namespace SSet

universe u

/-- If an epi pullback of a simplex has nondegenerate core `c`, then the
simplex itself is a degeneracy of `c`, and the core map factors through the
epi. -/
theorem coreFactorsThroughEpi
    (X : SSet.{u}) {d r k : ℕ}
    (e : ⦋d⦌ ⟶ ⦋r⦌)
    (he : Function.Surjective e.toOrderHom)
    (q : ⦋d⦌ ⟶ ⦋k⦌)
    (hq : Function.Surjective q.toOrderHom)
    (c : X _⦋k⦌) (hc : c ∈ X.nonDegenerate k)
    (y : X _⦋r⦌)
    (h : X.map e.op y = X.map q.op c) :
    ∃ q' : ⦋r⦌ ⟶ ⦋k⦌,
      Function.Surjective q'.toOrderHom ∧
      y = X.map q'.op c ∧ e ≫ q' = q := by
  letI : Epi e := SimplexCategory.epi_iff_surjective.mpr he
  letI : Epi q := SimplexCategory.epi_iff_surjective.mpr hq
  obtain ⟨l, q', hq', z, hz⟩ := X.exists_nonDegenerate y
  have hx :
      X.map e.op y =
        X.map (e ≫ q').op z := by
    rw [hz, op_comp, FunctorToTypes.map_comp_apply]
  have hdim : k = l :=
    X.unique_nonDegenerate_dim (X.map e.op y)
      q ⟨c, hc⟩ h (e ≫ q') z hx
  subst l
  have hz_eq : (⟨c, hc⟩ : X.nonDegenerate k) = z :=
    X.unique_nonDegenerate_simplex (X.map e.op y)
      q ⟨c, hc⟩ h (e ≫ q') z hx
  subst z
  have hmap : q = e ≫ q' :=
    X.unique_nonDegenerate_map (X.map e.op y)
      q ⟨c, hc⟩ h (e ≫ q') ⟨c, hc⟩ hx
  refine ⟨q', ?_, hz, hmap.symm⟩
  exact SimplexCategory.epi_iff_surjective.mp hq'

end SSet

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

/-- A face of `t` whose simplicial core is the simplex `c`. -/
structure SimplexCoreFace
    (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) where
  /-- Dimension of the possibly degenerate face. -/
  dim : ℕ
  /-- Inclusion of the face into `t`. -/
  face : ⦋dim⦌ ⟶ ⦋n⦌
  /-- The face map is injective. -/
  face_injective : Function.Injective face.toOrderHom
  /-- Degeneracy collapsing the face to its core. -/
  collapse : ⦋dim⦌ ⟶ ⦋k⦌
  /-- Every core vertex has a preimage. -/
  collapse_surjective : Function.Surjective collapse.toOrderHom
  /-- The selected face is the indicated degeneracy of `c`. -/
  face_eq :
    X.map face.op t = X.map collapse.op c

namespace SimplexCoreFace

variable {X : SSet.{u}} {k n : ℕ}
  {c : X _⦋k⦌} {t : X _⦋n⦌}

/-- Largest barycentric coordinate outside the selected face. -/
noncomputable def outsideMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) : NNReal :=
  (Finset.univ.filter
      (fun j : Fin (n + 1) =>
        j ∉ Set.range h.face.toOrderHom)).sup p

/-- Total barycentric coordinate mass outside the selected face.

Unlike `outsideMass`, this quantity is preserved by the fiber sums in
`toTopMap`; it therefore defines the natural refinement below. -/
noncomputable def totalOutsideMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) : NNReal :=
  ∑ j ∈ Finset.univ.filter
      (fun j : Fin (n + 1) =>
        j ∉ Set.range h.face.toOrderHom),
    p j

/-- Barycentric mass over one vertex of the nondegenerate core. -/
noncomputable def coreMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj)
    (i : Fin (k + 1)) : NNReal :=
  ∑ j ∈ Finset.univ.filter
      (fun j : Fin (h.dim + 1) =>
        h.collapse.toOrderHom j = i),
    p (h.face.toOrderHom j)

theorem continuous_outsideMass
    (h : SimplexCoreFace X c t) :
    Continuous h.outsideMass := by
  unfold outsideMass
  change Continuous (fun p : ⦋n⦌.toTopObj =>
    (Finset.univ.filter
      (fun j : Fin (n + 1) =>
        j ∉ Set.range h.face.toOrderHom)).sup
      (fun i => p.1 i))
  simpa only [Function.comp_apply] using
    (Continuous.finset_sup_apply (L := NNReal)
      (X := ⦋n⦌.toTopObj)
      (s := Finset.univ.filter
        (fun j : Fin (n + 1) =>
          j ∉ Set.range h.face.toOrderHom))
      (f := fun i (p : ⦋n⦌.toTopObj) => p.1 i)
      (fun i _ =>
        (continuous_apply i).comp continuous_subtype_val))

theorem continuous_totalOutsideMass
    (h : SimplexCoreFace X c t) :
    Continuous h.totalOutsideMass := by
  unfold totalOutsideMass
  fun_prop

theorem continuous_coreMass
    (h : SimplexCoreFace X c t) (i : Fin (k + 1)) :
    Continuous (fun p => h.coreMass p i) := by
  unfold coreMass
  exact continuous_finset_sum _ fun j _ =>
    (continuous_apply (h.face.toOrderHom j)).comp
      continuous_subtype_val

/-- Open dominance condition defining the star of a core face. -/
def starSet (h : SimplexCoreFace X c t) : Set ⦋n⦌.toTopObj :=
  {p | ∀ i : Fin (k + 1), h.outsideMass p < h.coreMass p i}

theorem isOpen_starSet (h : SimplexCoreFace X c t) :
    IsOpen h.starSet := by
  rw [show h.starSet =
      ⋂ i : Fin (k + 1),
        {p | h.outsideMass p < h.coreMass p i} by
    ext p
    simp [starSet]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (continuous_outsideMass h)
    (continuous_coreMass h i)

/-- The total-outside refinement of a core-face star.  This is the version
stable under all simplex maps. -/
def naturalStarSet (h : SimplexCoreFace X c t) :
    Set ⦋n⦌.toTopObj :=
  {p | ∀ i : Fin (k + 1),
    h.totalOutsideMass p < h.coreMass p i}

theorem isOpen_naturalStarSet (h : SimplexCoreFace X c t) :
    IsOpen h.naturalStarSet := by
  rw [show h.naturalStarSet =
      ⋂ i : Fin (k + 1),
        {p | h.totalOutsideMass p < h.coreMass p i} by
    ext p
    simp [naturalStarSet]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (continuous_totalOutsideMass h)
    (continuous_coreMass h i)

theorem outsideMass_le_totalOutsideMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) :
    h.outsideMass p ≤ h.totalOutsideMass p := by
  unfold outsideMass totalOutsideMass
  apply Finset.sup_le
  intro j hj
  exact Finset.single_le_sum (fun _ _ => bot_le) hj

theorem naturalStarSet_subset_starSet
    (h : SimplexCoreFace X c t) :
    h.naturalStarSet ⊆ h.starSet := by
  intro p hp i
  exact lt_of_le_of_lt (outsideMass_le_totalOutsideMass h p) (hp i)

/-- The whole simplex is a core face of itself. -/
noncomputable def identity
    (s : X _⦋n⦌) :
    SimplexCoreFace X s s where
  dim := n
  face := 𝟙 _
  face_injective := Function.injective_id
  collapse := 𝟙 _
  collapse_surjective := Function.surjective_id
  face_eq := by simp

theorem mem_identity_starSet_iff
    (s : X _⦋n⦌) (p : ⦋n⦌.toTopObj) :
    p ∈ (identity s).starSet ↔ ∀ i, 0 < p i := by
  have hcore (i : Fin (n + 1)) :
      (identity s).coreMass p i = p i := by
    unfold coreMass identity
    have hf :
        Finset.univ.filter (fun j : Fin (n + 1) => j = i) =
          {i} := by
      ext j
      simp
    change
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + 1) => j = i), p j = p i
    rw [hf]
    simp
  constructor
  · intro hp i
    have hi := hp i
    rw [hcore] at hi
    simpa [outsideMass, identity] using hi
  · intro hp
    change ∀ i, (identity s).outsideMass p <
      (identity s).coreMass p i
    intro i
    rw [hcore]
    simpa [outsideMass, identity] using hp i

/-- The union of the natural total-outside refinements of all core-face stars
of `c` inside `t`. -/
def simplexStar (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) : Set ⦋n⦌.toTopObj :=
  ⋃ h : SimplexCoreFace X c t, h.naturalStarSet

theorem isOpen_simplexStar (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) :
    IsOpen (simplexStar X c t) :=
  isOpen_iUnion fun h => h.isOpen_naturalStarSet

/-- Reindex a core mass as a sum over ambient vertices. -/
theorem coreMass_eq_sum_filter
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj)
    (i : Fin (k + 1)) :
    h.coreMass p i =
      ∑ j ∈ Finset.univ.filter (fun j =>
        ∃ x : Fin (h.dim + 1),
          h.collapse.toOrderHom x = i ∧
          h.face.toOrderHom x = j), p j := by
  classical
  unfold coreMass
  apply Finset.sum_bij
    (fun x _ => h.face.toOrderHom x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨x, hx, rfl⟩
  · intro x₁ _ x₂ _ hface
    exact h.face_injective hface
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · intro x hx
    rfl

/-- A source core-face star maps into the target core-simplex star.  The image
of the source face may identify vertices; nondegeneracy of `c` makes the
resulting collapse factor through that finite image. -/
theorem simplexStar_map
    (X : SSet.{u}) {k m n : ℕ}
    (c : X _⦋k⦌) (hc : c ∈ X.nonDegenerate k)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (t : X _⦋n⦌)
    (p : ⦋m⦌.toTopObj)
    (hp : p ∈ simplexStar X c (X.map f.op t)) :
    SimplexCategory.toTopMap f p ∈ simplexStar X c t := by
  classical
  rw [simplexStar, Set.mem_iUnion] at hp ⊢
  obtain ⟨h, hp⟩ := hp
  let I := SimplexCategory.finiteImage (h.face ≫ f)
  let y : X _⦋I.dim⦌ := X.map I.face.op t
  have hcomp :
      X.map I.epi.op y = X.map h.collapse.op c := by
    calc
      X.map I.epi.op y =
          X.map (I.epi ≫ I.face).op t := by
            rw [op_comp, FunctorToTypes.map_comp_apply]
      _ = X.map (h.face ≫ f).op t := by rw [I.fac]
      _ = X.map h.face.op (X.map f.op t) := by
            rw [op_comp, FunctorToTypes.map_comp_apply]
      _ = X.map h.collapse.op c := h.face_eq
  obtain ⟨q, hq, hy, hfac⟩ :=
    SSet.coreFactorsThroughEpi X I.epi I.epi_surjective
      h.collapse h.collapse_surjective c hc y hcomp
  let H : SimplexCoreFace X c t :=
    { dim := I.dim
      face := I.face
      face_injective := I.face_injective
      collapse := q
      collapse_surjective := hq
      face_eq := hy }
  refine ⟨H, ?_⟩
  intro i
  have hout :
      H.totalOutsideMass (SimplexCategory.toTopMap f p) ≤
        h.totalOutsideMass p := by
    unfold totalOutsideMass
    rw [SimplexCategory.sum_toTopMap_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hj
      contrapose! hj
      obtain ⟨x, rfl⟩ := hj
      exact ⟨I.epi.toOrderHom x,
        SimplexCategory.congr_toOrderHom_apply I.fac x⟩
    · simp
  have hcore :
      h.coreMass p i ≤
        H.coreMass (SimplexCategory.toTopMap f p) i := by
    rw [coreMass_eq_sum_filter, coreMass_eq_sum_filter,
      SimplexCategory.sum_toTopMap_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨x, hx, rfl⟩
      refine ⟨I.epi.toOrderHom x, ?_, ?_⟩
      · have hx' :=
          SimplexCategory.congr_toOrderHom_apply hfac x
        exact hx' ▸ hx
      · have hh :=
          SimplexCategory.congr_toOrderHom_apply I.fac x
        change
          I.face.toOrderHom (I.epi.toOrderHom x) =
            f.toOrderHom (h.face.toOrderHom x) at hh
        exact hh
    · simp
  exact lt_of_le_of_lt hout (lt_of_lt_of_le (hp i) hcore)

/-- The inverse image of a target core-face star lies in the source
core-simplex star.  Positivity forces every core vertex to occur in the finite
inverse-image face. -/
theorem simplexStar_preimage
    (X : SSet.{u}) {k m n : ℕ}
    (c : X _⦋k⦌)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (t : X _⦋n⦌)
    (p : ⦋m⦌.toTopObj)
    (hp : SimplexCategory.toTopMap f p ∈ simplexStar X c t) :
    p ∈ simplexStar X c (X.map f.op t) := by
  classical
  rw [simplexStar, Set.mem_iUnion] at hp ⊢
  obtain ⟨h, hp⟩ := hp
  have hhit (i : Fin (k + 1)) :
      ∃ (j : Fin (m + 1)) (x : Fin (h.dim + 1)),
        h.collapse.toOrderHom x = i ∧
          h.face.toOrderHom x = f.toOrderHom j := by
    have hpos : 0 <
        h.coreMass (SimplexCategory.toTopMap f p) i :=
      lt_of_le_of_lt bot_le (hp i)
    rw [coreMass_eq_sum_filter,
      SimplexCategory.sum_toTopMap_filter] at hpos
    let S : Finset (Fin (m + 1)) :=
      Finset.univ.filter (fun j =>
        ∃ x : Fin (h.dim + 1),
          h.collapse.toOrderHom x = i ∧
            h.face.toOrderHom x = f.toOrderHom j)
    have hS : S.Nonempty := by
      by_contra hne
      have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change 0 < ∑ j ∈ S, p j at hpos
      rw [hempty] at hpos
      simp at hpos
    obtain ⟨j, hj⟩ := hS
    simp only [S, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    obtain ⟨x, hx, hface⟩ := hj
    exact ⟨j, x, hx, hface⟩
  have hne : Set.Nonempty
      {j : Fin (m + 1) |
        f.toOrderHom j ∈ Set.range h.face.toOrderHom} := by
    obtain ⟨j, x, _, hx⟩ := hhit 0
    exact ⟨j, x, hx⟩
  let F := SimplexCategory.finiteFacePreimage
    f h.face h.face_injective hne
  have hcollapse :
      Function.Surjective
        (F.toFace ≫ h.collapse).toOrderHom := by
    intro i
    obtain ⟨j, x, hx, hface⟩ := hhit i
    have hjTarget :
        f.toOrderHom j ∈ Set.range h.face.toOrderHom :=
      ⟨x, hface⟩
    have hjSource : j ∈ Set.range F.face.toOrderHom := by
      rw [F.range_face]
      exact hjTarget
    obtain ⟨z, hz⟩ := hjSource
    refine ⟨z, ?_⟩
    change h.collapse.toOrderHom (F.toFace.toOrderHom z) = i
    have hsquare :=
      SimplexCategory.congr_toOrderHom_apply F.fac z
    change
      f.toOrderHom (F.face.toOrderHom z) =
        h.face.toOrderHom (F.toFace.toOrderHom z) at hsquare
    have hto : F.toFace.toOrderHom z = x := by
      apply h.face_injective
      rw [← hsquare, hz, ← hface]
    rw [hto, hx]
  let H : SimplexCoreFace X c (X.map f.op t) :=
    { dim := F.dim
      face := F.face
      face_injective := F.face_injective
      collapse := F.toFace ≫ h.collapse
      collapse_surjective := hcollapse
      face_eq := by
        calc
          X.map F.face.op (X.map f.op t) =
              X.map (F.face ≫ f).op t := by
                rw [op_comp, FunctorToTypes.map_comp_apply]
          _ = X.map (F.toFace ≫ h.face).op t := by
                rw [F.fac]
          _ = X.map F.toFace.op (X.map h.face.op t) := by
                rw [op_comp, FunctorToTypes.map_comp_apply]
          _ = X.map F.toFace.op (X.map h.collapse.op c) := by
                rw [h.face_eq]
          _ = X.map (F.toFace ≫ h.collapse).op c := by
                rw [op_comp, FunctorToTypes.map_comp_apply] }
  refine ⟨H, ?_⟩
  intro i
  have hout :
      H.totalOutsideMass p =
        h.totalOutsideMass (SimplexCategory.toTopMap f p) := by
    unfold totalOutsideMass
    rw [SimplexCategory.sum_toTopMap_filter]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrange :
          (j ∈ Set.range F.face.toOrderHom) ↔
            (f.toOrderHom j ∈ Set.range h.face.toOrderHom) := by
        rw [F.range_face]
        rfl
      exact not_congr hrange
    · intro j hj
      rfl
  have hcore :
      H.coreMass p i =
        h.coreMass (SimplexCategory.toTopMap f p) i := by
    rw [coreMass_eq_sum_filter, coreMass_eq_sum_filter,
      SimplexCategory.sum_toTopMap_filter]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨F.toFace.toOrderHom z, ?_, ?_⟩
        · exact hz
        · have hsquare :=
            SimplexCategory.congr_toOrderHom_apply F.fac z
          change
            f.toOrderHom (F.face.toOrderHom z) =
              h.face.toOrderHom (F.toFace.toOrderHom z) at hsquare
          exact hsquare.symm
      · rintro ⟨x, hx, hface⟩
        have hjTarget :
            f.toOrderHom j ∈ Set.range h.face.toOrderHom :=
          ⟨x, hface⟩
        have hjSource : j ∈ Set.range F.face.toOrderHom := by
          rw [F.range_face]
          exact hjTarget
        obtain ⟨z, hz⟩ := hjSource
        refine ⟨z, ?_, hz⟩
        change
          h.collapse.toOrderHom (F.toFace.toOrderHom z) = i
        have hsquare :=
          SimplexCategory.congr_toOrderHom_apply F.fac z
        change
          f.toOrderHom (F.face.toOrderHom z) =
            h.face.toOrderHom (F.toFace.toOrderHom z) at hsquare
        have hto : F.toFace.toOrderHom z = x := by
          apply h.face_injective
          rw [hz] at hsquare
          exact hsquare.symm.trans hface.symm
        rw [hto, hx]
    · intro j hj
      rfl
  rw [hout, hcore]
  exact hp i

/-- Exact naturality of the open core-simplex star under every morphism of
standard simplices. -/
theorem simplexStar_naturality
    (X : SSet.{u}) {k m n : ℕ}
    (c : X _⦋k⦌) (hc : c ∈ X.nonDegenerate k)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (t : X _⦋n⦌) :
    simplexStar X c (X.map f.op t) =
      SimplexCategory.toTopMap f ⁻¹'
        simplexStar X c t := by
  ext p
  change
    p ∈ simplexStar X c (X.map f.op t) ↔
      SimplexCategory.toTopMap f p ∈ simplexStar X c t
  exact ⟨simplexStar_map X c hc f t p,
    simplexStar_preimage X c f t p⟩

/-- Overlapping natural stars with same-dimensional nondegenerate cores have
the same core, and their selected faces share a vertex lying over the zeroth
vertex of that core on both sides. -/
theorem eq_and_exists_commonZero_of_mem_naturalStarSet
    (X : SSet.{u}) {k n : ℕ}
    {c d : X _⦋k⦌} {t : X _⦋n⦌}
    (hc : c ∈ X.nonDegenerate k)
    (hd : d ∈ X.nonDegenerate k)
    (h : SimplexCoreFace X c t)
    (g : SimplexCoreFace X d t)
    (p : ⦋n⦌.toTopObj)
    (hp : p ∈ h.naturalStarSet)
    (hg : p ∈ g.naturalStarSet) :
    c = d ∧
      ∃ (a : Fin (h.dim + 1)) (b : Fin (g.dim + 1)),
        h.face.toOrderHom a = g.face.toOrderHom b ∧
        h.collapse.toOrderHom a = 0 ∧
        g.collapse.toOrderHom b = 0 := by
  classical
  have coreMass_le_outside
      {aCore bCore : X _⦋k⦌}
      (a : SimplexCoreFace X aCore t)
      (b : SimplexCoreFace X bCore t)
      (i : Fin (k + 1))
      (hmiss : ∀ j : Fin (a.dim + 1),
        a.collapse.toOrderHom j = i →
          a.face.toOrderHom j ∉ Set.range b.face.toOrderHom) :
      a.coreMass p i ≤ b.totalOutsideMass p := by
    rw [a.coreMass_eq_sum_filter]
    unfold totalOutsideMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨z, hz, rfl⟩
      exact hmiss z hz
    · simp
  have hinter :
      Set.Nonempty
        {j : Fin (h.dim + 1) |
          h.face.toOrderHom j ∈ Set.range g.face.toOrderHom} := by
    by_contra hnone
    have hhmiss (j : Fin (h.dim + 1))
        (hj : h.collapse.toOrderHom j = (0 : Fin (k + 1))) :
        h.face.toOrderHom j ∉ Set.range g.face.toOrderHom := by
      intro hjg
      exact hnone ⟨j, hjg⟩
    have hgmiss (j : Fin (g.dim + 1))
        (hj : g.collapse.toOrderHom j = (0 : Fin (k + 1))) :
        g.face.toOrderHom j ∉ Set.range h.face.toOrderHom := by
      intro hjh
      obtain ⟨z, hz⟩ := hjh
      apply hnone
      refine ⟨z, ?_⟩
      exact ⟨j, hz.symm⟩
    have hh :=
      coreMass_le_outside h g 0 hhmiss
    have hgg :=
      coreMass_le_outside g h 0 hgmiss
    have hcontra : h.totalOutsideMass p <
        h.totalOutsideMass p := by
      calc
        h.totalOutsideMass p < h.coreMass p 0 := hp 0
        _ ≤ g.totalOutsideMass p := hh
        _ < g.coreMass p 0 := hg 0
        _ ≤ h.totalOutsideMass p := hgg
    exact (lt_irrefl _ hcontra)
  let F := SimplexCategory.finiteFacePreimage
    h.face g.face g.face_injective hinter
  let qh : ⦋F.dim⦌ ⟶ ⦋k⦌ := F.face ≫ h.collapse
  let qg : ⦋F.dim⦌ ⟶ ⦋k⦌ := F.toFace ≫ g.collapse
  let y : X _⦋F.dim⦌ :=
    X.map (F.face ≫ h.face).op t
  have hyh : y = X.map qh.op c := by
    calc
      y = X.map F.face.op (X.map h.face.op t) := by
        rw [show y = X.map (F.face ≫ h.face).op t by rfl,
          op_comp, FunctorToTypes.map_comp_apply]
      _ = X.map F.face.op (X.map h.collapse.op c) := by
        rw [h.face_eq]
      _ = X.map qh.op c := by
        rw [show qh = F.face ≫ h.collapse by rfl,
          op_comp, FunctorToTypes.map_comp_apply]
  have hyg : y = X.map qg.op d := by
    calc
      y = X.map (F.toFace ≫ g.face).op t := by
        rw [show y = X.map (F.face ≫ h.face).op t by rfl,
          F.fac]
      _ = X.map F.toFace.op (X.map g.face.op t) := by
        rw [op_comp, FunctorToTypes.map_comp_apply]
      _ = X.map F.toFace.op (X.map g.collapse.op d) := by
        rw [g.face_eq]
      _ = X.map qg.op d := by
        rw [show qg = F.toFace ≫ g.collapse by rfl,
          op_comp, FunctorToTypes.map_comp_apply]
  have surjective_of_surjective
      {a b : X _⦋k⦌}
      (ha : a ∈ X.nonDegenerate k)
      (hb : b ∈ X.nonDegenerate k)
      (qa qb : ⦋F.dim⦌ ⟶ ⦋k⦌)
      (hya : y = X.map qa.op a)
      (hyb : y = X.map qb.op b)
      (hqa : Function.Surjective qa.toOrderHom) :
      Function.Surjective qb.toOrderHom := by
    let I := SimplexCategory.finiteImage qb
    let z : X _⦋I.dim⦌ := X.map I.face.op b
    have hIz :
        X.map I.epi.op z = X.map qa.op a := by
      calc
        X.map I.epi.op z =
            X.map (I.epi ≫ I.face).op b := by
          rw [show z = X.map I.face.op b by rfl,
            op_comp, FunctorToTypes.map_comp_apply]
        _ = X.map qb.op b := by rw [I.fac]
        _ = y := hyb.symm
        _ = X.map qa.op a := hya
    obtain ⟨q, hq, _, _⟩ :=
      SSet.coreFactorsThroughEpi X I.epi I.epi_surjective
        qa hqa a ha z hIz
    have hk_le : k ≤ I.dim := by
      letI : Epi q :=
        SimplexCategory.epi_iff_surjective.mpr hq
      exact SimplexCategory.len_le_of_epi q
    have hI_le : I.dim ≤ k := by
      letI : Mono I.face :=
        SimplexCategory.mono_iff_injective.mpr I.face_injective
      exact SimplexCategory.len_le_of_mono I.face
    have hcard :
        Fintype.card (Fin (I.dim + 1)) =
          Fintype.card (Fin (k + 1)) := by
      simp [le_antisymm hI_le hk_le]
    have hfaceSurjective :
        Function.Surjective I.face.toOrderHom :=
      ((Fintype.bijective_iff_injective_and_card
        I.face.toOrderHom).2 ⟨I.face_injective, hcard⟩).2
    intro i
    obtain ⟨j, hj⟩ := hfaceSurjective i
    obtain ⟨l, hl⟩ := I.epi_surjective j
    refine ⟨l, ?_⟩
    have hfac :=
      SimplexCategory.congr_toOrderHom_apply I.fac l
    change
      I.face.toOrderHom (I.epi.toOrderHom l) =
        qb.toOrderHom l at hfac
    rw [hl, hj] at hfac
    exact hfac.symm
  by_cases hqh : Function.Surjective qh.toOrderHom
  · have hqg : Function.Surjective qg.toOrderHom :=
      surjective_of_surjective hc hd qh qg hyh hyg hqh
    letI : Epi qh :=
      SimplexCategory.epi_iff_surjective.mpr hqh
    have hcoreEq :=
      X.unique_nonDegenerate_simplex y qh ⟨c, hc⟩ hyh
        qg ⟨d, hd⟩ hyg
    have hqh_zero : qh.toOrderHom 0 = 0 := by
      obtain ⟨z, hz⟩ := hqh 0
      have hle :=
        qh.toOrderHom.monotone (Fin.zero_le z)
      rw [hz] at hle
      exact Fin.le_zero_iff.mp hle
    have hqg_zero : qg.toOrderHom 0 = 0 := by
      obtain ⟨z, hz⟩ := hqg 0
      have hle :=
        qg.toOrderHom.monotone (Fin.zero_le z)
      rw [hz] at hle
      exact Fin.le_zero_iff.mp hle
    refine ⟨_root_.congrArg Subtype.val hcoreEq,
      F.face.toOrderHom 0, F.toFace.toOrderHom 0, ?_, ?_, ?_⟩
    · exact SimplexCategory.congr_toOrderHom_apply F.fac 0
    · exact hqh_zero
    · exact hqg_zero
  · have hnqg : ¬ Function.Surjective qg.toOrderHom := by
      intro hqg
      exact hqh
        (surjective_of_surjective hd hc qg qh hyg hyh hqg)
    simp only [Function.Surjective] at hqh hnqg
    push_neg at hqh hnqg
    obtain ⟨i, hi⟩ := hqh
    obtain ⟨j, hj⟩ := hnqg
    have hhmiss (z : Fin (h.dim + 1))
        (hz : h.collapse.toOrderHom z = i) :
        h.face.toOrderHom z ∉ Set.range g.face.toOrderHom := by
      intro hzg
      have hzF : z ∈ Set.range F.face.toOrderHom := by
        rw [F.range_face]
        exact hzg
      obtain ⟨w, hw⟩ := hzF
      apply hi w
      change h.collapse.toOrderHom (F.face.toOrderHom w) = i
      rw [hw]
      exact hz
    have hgmiss (z : Fin (g.dim + 1))
        (hz : g.collapse.toOrderHom z = j) :
        g.face.toOrderHom z ∉ Set.range h.face.toOrderHom := by
      intro hzh
      obtain ⟨w, hw⟩ := hzh
      have hwF : w ∈ Set.range F.face.toOrderHom := by
        rw [F.range_face]
        exact ⟨z, hw.symm⟩
      obtain ⟨v, hv⟩ := hwF
      apply hj v
      change g.collapse.toOrderHom (F.toFace.toOrderHom v) = j
      have hfac :=
        SimplexCategory.congr_toOrderHom_apply F.fac v
      change
        h.face.toOrderHom (F.face.toOrderHom v) =
          g.face.toOrderHom (F.toFace.toOrderHom v) at hfac
      have hto : F.toFace.toOrderHom v = z := by
        apply g.face_injective
        rw [← hfac, hv, hw]
      rw [hto]
      exact hz
    have hh := coreMass_le_outside h g i hhmiss
    have hgg := coreMass_le_outside g h j hgmiss
    have hcontra : h.totalOutsideMass p <
        h.totalOutsideMass p := by
      calc
        h.totalOutsideMass p < h.coreMass p i := hp i
        _ ≤ g.totalOutsideMass p := hh
        _ < g.coreMass p j := hg j
        _ ≤ h.totalOutsideMass p := hgg
    exact (lt_irrefl _ hcontra).elim

/-- Two natural core-face stars with nondegenerate cores of the same dimension
can meet only when their cores are equal. -/
theorem eq_of_mem_naturalStarSet
    (X : SSet.{u}) {k n : ℕ}
    {c d : X _⦋k⦌} {t : X _⦋n⦌}
    (hc : c ∈ X.nonDegenerate k)
    (hd : d ∈ X.nonDegenerate k)
    (h : SimplexCoreFace X c t)
    (g : SimplexCoreFace X d t)
    (p : ⦋n⦌.toTopObj)
    (hp : p ∈ h.naturalStarSet)
    (hg : p ∈ g.naturalStarSet) :
    c = d :=
  (eq_and_exists_commonZero_of_mem_naturalStarSet
    X hc hd h g p hp hg).1

/-- The core-simplex star on a simplex object, with the universe lift used by
the realization adjunction. -/
noncomputable def simplexStarObj
    (X : SSet.{u}) {k : ℕ}
    (c : X _⦋k⦌) (n : SimplexCategory)
    (t : X.obj (op n)) :
    Set (SimplexCategory.toTop.{u}.obj n) := by
  induction n using SimplexCategory.rec with
  | _ n =>
      exact {p | p.down ∈ simplexStar X c t}

/-- The compatible open family determined by a nondegenerate core simplex. -/
noncomputable def simplexStarOpenFamily
    (X : SSet.{u}) {k : ℕ}
    (c : X _⦋k⦌) (hc : c ∈ X.nonDegenerate k) :
    OpenFamily X where
  set n t := simplexStarObj X c n t
  isOpen n t := by
    induction n using SimplexCategory.rec with
    | _ n =>
        exact (isOpen_simplexStar X c t).preimage
          continuous_uliftDown
  naturality := by
    intro m n f t
    induction m using SimplexCategory.rec with
    | _ m =>
      induction n using SimplexCategory.rec with
      | _ n =>
        ext p
        obtain ⟨p⟩ := p
        change
          p ∈ simplexStar X c (X.map f.op t) ↔
            SimplexCategory.toTopMap f p ∈ simplexStar X c t
        exact Set.ext_iff.mp (simplexStar_naturality X c hc f t) p

/-! ## Global realization stars -/

/-- The quotient-saturated open star of a nondegenerate simplex in the genuine
geometric realization. -/
noncomputable def realizationStar
    (X : SSet.{u}) {k : ℕ} (c : X _⦋k⦌)
    (hc : c ∈ X.nonDegenerate k) :
    Set (SSet.toTop.obj X) :=
  (simplexStarOpenFamily X c hc).descSet

theorem isOpen_realizationStar
    (X : SSet.{u}) {k : ℕ} (c : X _⦋k⦌)
    (hc : c ∈ X.nonDegenerate k) :
    IsOpen (realizationStar X c hc) :=
  (simplexStarOpenFamily X c hc).isOpen_descSet

theorem realizeSimplex_mem_realizationStar_iff
    (X : SSet.{u}) {k : ℕ} (c : X _⦋k⦌)
    (hc : c ∈ X.nonDegenerate k)
    {n : SimplexCategory} (t : X.obj (op n))
    (p : SimplexCategory.toTop.{u}.obj n) :
    realizeSimplex t p ∈ realizationStar X c hc ↔
      p ∈ simplexStarObj X c n t :=
  (simplexStarOpenFamily X c hc).mem_descSet t p

/-- Every barycentric point belongs to the star of the nondegenerate core of
its positive-support face. -/
theorem exists_nonDegenerate_mem_simplexStar
    (X : SSet.{u}) {n : ℕ} (t : X _⦋n⦌)
    (p : ⦋n⦌.toTopObj) :
    ∃ (k : ℕ) (c : X _⦋k⦌)
      (_hc : c ∈ X.nonDegenerate k),
      p ∈ simplexStar X c t := by
  classical
  let F := SimplexCategory.positiveSupportFace p
  let y : X _⦋F.dim⦌ := X.map F.face.op t
  obtain ⟨k, q, hq, c, hc⟩ := X.exists_nonDegenerate y
  have hq' : Function.Surjective q.toOrderHom :=
    SimplexCategory.epi_iff_surjective.mp hq
  let h : SimplexCoreFace X c.1 t :=
    { dim := F.dim
      face := F.face
      face_injective := F.face_injective
      collapse := q
      collapse_surjective := hq'
      face_eq := hc }
  refine ⟨k, c.1, c.2, ?_⟩
  rw [simplexStar, Set.mem_iUnion]
  refine ⟨h, ?_⟩
  intro i
  have hout : h.totalOutsideMass p = 0 := by
    unfold totalOutsideMass
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    exact SimplexCategory.positiveSupportFace_eq_zero_of_notMem
      p j hj
  have hcore : 0 < h.coreMass p i := by
    obtain ⟨j, hj⟩ := hq' i
    have hpos :
        0 < p (h.face.toOrderHom j) := by
      exact SimplexCategory.positiveSupportFace_pos p j
    have hmem :
        j ∈ Finset.univ.filter
          (fun j : Fin (h.dim + 1) =>
            h.collapse.toOrderHom j = i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change q.toOrderHom j = i
      exact hj
    have hle :
        p (h.face.toOrderHom j) ≤ h.coreMass p i := by
      unfold coreMass
      have hnonneg :
          ∀ a ∈ Finset.univ.filter
              (fun a : Fin (h.dim + 1) =>
                h.collapse.toOrderHom a = i),
            (0 : NNReal) ≤ p (h.face.toOrderHom a) :=
        fun _ _ => bot_le
      exact Finset.single_le_sum hnonneg hmem
    exact lt_of_lt_of_le hpos hle
  rw [hout]
  exact hcore

/-- The descended nondegenerate-simplex stars cover every point of geometric
realization. -/
theorem exists_mem_realizationStar
    (X : SSet.{u}) (z : SSet.toTop.obj X) :
    ∃ (k : ℕ) (c : X _⦋k⦌)
      (hc : c ∈ X.nonDegenerate k),
      z ∈ realizationStar X c hc := by
  obtain ⟨n, t, p, rfl⟩ := realization_point_representation X z
  induction n using SimplexCategory.rec with
  | _ n =>
      obtain ⟨k, c, hc, hp⟩ :=
        exists_nonDegenerate_mem_simplexStar X t p.down
      refine ⟨k, c, hc, ?_⟩
      rw [realizeSimplex_mem_realizationStar_iff]
      exact hp

/-- Distinct nondegenerate simplices of the same dimension have disjoint
descended realization stars. -/
theorem disjoint_realizationStar
    (X : SSet.{u}) {k : ℕ} {c d : X _⦋k⦌}
    (hc : c ∈ X.nonDegenerate k)
    (hd : d ∈ X.nonDegenerate k)
    (hcd : c ≠ d) :
    Disjoint (realizationStar X c hc)
      (realizationStar X d hd) := by
  rw [Set.disjoint_left]
  intro z hzc hzd
  obtain ⟨n, t, p, hpz⟩ :=
    realization_point_representation X z
  rw [← hpz, realizeSimplex_mem_realizationStar_iff] at hzc hzd
  induction n using SimplexCategory.rec with
  | _ n =>
      change p.down ∈ simplexStar X c t at hzc
      change p.down ∈ simplexStar X d t at hzd
      rw [simplexStar, Set.mem_iUnion] at hzc hzd
      obtain ⟨h, hh⟩ := hzc
      obtain ⟨g, hg⟩ := hzd
      exact hcd (eq_of_mem_naturalStarSet
        X hc hd h g p.down hh hg)

end SimplexCoreFace

/-! ## Computational-path certificate -/

/-- Reflexive path certificate for the nonnegative outside mass. -/
noncomputable def outsideMassNonnegativePath
    {X : SSet.{u}} {k n : ℕ}
    {c : X _⦋k⦌} {t : X _⦋n⦌}
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) :
    Path (0 + h.outsideMass p) (h.outsideMass p) :=
  Path.stepChain (zero_add _)

/-- Coherence of the outside-mass certificate. -/
noncomputable def outsideMassNonnegativeCoherence
    {X : SSet.{u}} {k n : ℕ}
    {c : X _⦋k⦌} {t : X _⦋n⦌}
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) :
    RwEq
      (Path.trans (outsideMassNonnegativePath h p)
        (Path.refl (h.outsideMass p)))
      (outsideMassNonnegativePath h p) :=
  rweq_cmpA_refl_right (outsideMassNonnegativePath h p)

end TopologicalNerve
end Path
end ComputationalPaths
