/-
# Deep Simplicial Homotopy Theory via Computational Paths

A self-contained simplicial-flavoured development built from the core
computational-path primitives (`Path`, `Step`, `trans`, `symm`).

We model simplices as chains of composable edges, define basic face and
degeneracy operators, build 2-simplices (triangles) and 3-simplices
(associativity tetrahedra), and prove Kan-style horn fillability in a form
compatible with `Path`'s trace-carrying structure.
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace SimplicialDeep

universe u v

/-! ## 0. Chains (simplices as edge-chains) -/

/-- A simplex of dimension `n` is a chain of `n` edges connecting `n+1` vertices.
This is a lightweight representation suitable for Path-based rewriting.
-/
inductive Chain (A : Type u) : Nat → Type u where
  | vertex : A → Chain A 0
  | edge   : {n : Nat} → Chain A n → (src tgt : A) → Path src tgt → Chain A (n + 1)

/-- Drop the last edge (the last face). -/
def faceLast {A : Type u} : {n : Nat} → Chain A (n + 1) → Chain A n
  | _, Chain.edge c _ _ _ => c

/-- Insert a reflexivity edge at the end (last degeneracy). -/
def degenLast {A : Type u} : {n : Nat} → Chain A n → Chain A (n + 1)
  | 0, Chain.vertex a => Chain.edge (Chain.vertex a) a a (Path.refl a)
  | _, Chain.edge c s t p =>
      Chain.edge (Chain.edge c s t p) t t (Path.refl t)

/-! ## 1–4. Simplicial identities for face/degeneracy -/

theorem faceLast_degenLast {A : Type u} {n : Nat} (c : Chain A n) :
    faceLast (degenLast c) = c := by
  cases c with
  | vertex a => rfl
  | edge c s t p => rfl

theorem faceLast_degenLast_vertex {A : Type u} (a : A) :
    faceLast (degenLast (Chain.vertex a)) = Chain.vertex a := rfl

theorem double_degen_double_face {A : Type u} {a : A} :
    faceLast (faceLast (degenLast (degenLast (Chain.vertex a)))) =
    Chain.vertex a := rfl

theorem triple_face_triple_degen {A : Type u} {a : A} :
    faceLast (faceLast (faceLast
      (degenLast (degenLast (degenLast (Chain.vertex a)))))) =
    Chain.vertex a := rfl

/-! ## 5. 2-simplices: triangles encoding composition -/

structure Triangle (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂
  e₀₂ : Path v₀ v₂
  filler : Path.trans e₀₁ e₁₂ = e₀₂

/-- Degenerate triangle (left): refl then `p`. -/
def Triangle.degenLeft {A : Type u} {a b : A} (p : Path a b) : Triangle A :=
  { v₀ := a, v₁ := a, v₂ := b
    e₀₁ := Path.refl a
    e₁₂ := p
    e₀₂ := p
    filler := Path.trans_refl_left p }

/-- Degenerate triangle (right): `p` then refl. -/
def Triangle.degenRight {A : Type u} {a b : A} (p : Path a b) : Triangle A :=
  { v₀ := a, v₁ := b, v₂ := b
    e₀₁ := p
    e₁₂ := Path.refl b
    e₀₂ := p
    filler := Path.trans_refl_right p }

/-! ## 6–9. Triangle computations -/

theorem degenLeft_e₀₂ {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenLeft p).e₀₂ = p := rfl

theorem degenRight_e₀₂ {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenRight p).e₀₂ = p := rfl

theorem degenLeft_filler {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenLeft p).filler = Path.trans_refl_left p := rfl

theorem degenRight_filler {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenRight p).filler = Path.trans_refl_right p := rfl

/-! ## 10. 3-simplices: associativity tetrahedron -/

structure Tetrahedron (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A
  v₃ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂
  e₂₃ : Path v₂ v₃
  assoc_witness : Path.trans (Path.trans e₀₁ e₁₂) e₂₃ =
                  Path.trans e₀₁ (Path.trans e₁₂ e₂₃)

def mkTetrahedron {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Tetrahedron A :=
  { v₀ := a, v₁ := b, v₂ := c, v₃ := d
    e₀₁ := p, e₁₂ := q, e₂₃ := r
    assoc_witness := Path.trans_assoc p q r }

theorem tetrahedron_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (mkTetrahedron p q r).assoc_witness = Path.trans_assoc p q r := rfl

/-! ## 11–14. Horns and fillers (Kan-style) -/

/-- Inner 2-horn Λ²₁: composable edges with missing composite. -/
structure Horn21 (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂

/-- Fill Λ²₁ by composing. -/
def fillHorn21 {A : Type u} (h : Horn21 A) : Triangle A :=
  { v₀ := h.v₀, v₁ := h.v₁, v₂ := h.v₂
    e₀₁ := h.e₀₁
    e₁₂ := h.e₁₂
    e₀₂ := Path.trans h.e₀₁ h.e₁₂
    filler := rfl }

theorem horn21_filler_composite {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (fillHorn21 { v₀ := a, v₁ := b, v₂ := c, e₀₁ := p, e₁₂ := q }).e₀₂ =
      Path.trans p q := rfl

theorem kan_inner_horn {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    ∃ r : Path a c, r = Path.trans p q :=
  ⟨Path.trans p q, rfl⟩

theorem horn21_inverse_filler {A : Type u} {a b : A} (p : Path a b) :
    (fillHorn21 { v₀ := b, v₁ := a, v₂ := b, e₀₁ := Path.symm p, e₁₂ := p }).e₀₂ =
      Path.trans (Path.symm p) p := rfl

/-! ## 15–18. Nerve (0,1,2-simplices) -/

def nerve₀ {A : Type u} (a : A) : Chain A 0 := Chain.vertex a

def nerve₁ {A : Type u} {a b : A} (p : Path a b) : Chain A 1 :=
  Chain.edge (Chain.vertex a) a b p

def nerve₂ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) : Triangle A :=
  { v₀ := a, v₁ := b, v₂ := c
    e₀₁ := p
    e₁₂ := q
    e₀₂ := Path.trans p q
    filler := rfl }

theorem nerve₁_faceLast {A : Type u} {a b : A} (p : Path a b) :
    faceLast (nerve₁ p) = nerve₀ a := rfl

theorem nerve₂_filler {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    (nerve₂ p q).filler = rfl := rfl

/-! ## 19–21. Triangle reversal and whiskering -/

def Triangle.reverse {A : Type u} (t : Triangle A) : Triangle A :=
  { v₀ := t.v₂, v₁ := t.v₁, v₂ := t.v₀
    e₀₁ := Path.symm t.e₁₂
    e₁₂ := Path.symm t.e₀₁
    e₀₂ := Path.symm t.e₀₂
    filler := by
      rw [← Path.symm_trans t.e₀₁ t.e₁₂, t.filler] }

theorem triangle_reverse_vertices {A : Type u} (t : Triangle A) :
    (t.reverse.reverse).v₀ = t.v₀ ∧
    (t.reverse.reverse).v₁ = t.v₁ ∧
    (t.reverse.reverse).v₂ = t.v₂ :=
  ⟨rfl, rfl, rfl⟩

theorem whisker_left_triangle {A : Type u} {a b c : A}
    (p : Path a b) (q q' : Path b c) (h : q = q') :
    (nerve₂ p q).e₀₂ = (nerve₂ p q').e₀₂ := by subst h; rfl

theorem whisker_right_triangle {A : Type u} {a b c : A}
    (p p' : Path a b) (q : Path b c) (h : p = p') :
    (nerve₂ p q).e₀₂ = (nerve₂ p' q).e₀₂ := by subst h; rfl

/-! ## 22–28. Simplicial homotopies -/

@[ext]
structure SimplicialHomotopy {A : Type u} {B : Type v} (f g : A → B) where
  homotopy : (a : A) → Path (f a) (g a)

def SimplicialHomotopy.reverse {A : Type u} {B : Type v} {f g : A → B}
    (h : SimplicialHomotopy f g) : SimplicialHomotopy g f :=
  ⟨fun a => Path.symm (h.homotopy a)⟩

theorem homotopy_reverse_reverse {A : Type u} {B : Type v}
    {f g : A → B} (h : SimplicialHomotopy f g) :
    h.reverse.reverse = h := by
  ext a
  exact Path.symm_symm (h.homotopy a)

def SimplicialHomotopy.comp {A : Type u} {B : Type v} {f g h : A → B}
    (H₁ : SimplicialHomotopy f g) (H₂ : SimplicialHomotopy g h) :
    SimplicialHomotopy f h :=
  ⟨fun a => Path.trans (H₁.homotopy a) (H₂.homotopy a)⟩

theorem homotopy_comp_assoc {A : Type u} {B : Type v} {f g h k : A → B}
    (H₁ : SimplicialHomotopy f g) (H₂ : SimplicialHomotopy g h)
    (H₃ : SimplicialHomotopy h k) :
    (H₁.comp H₂).comp H₃ = H₁.comp (H₂.comp H₃) := by
  ext a
  exact Path.trans_assoc _ _ _

theorem homotopy_comp_refl_right {A : Type u} {B : Type v} {f g : A → B}
    (H : SimplicialHomotopy f g) :
    H.comp ⟨fun a => Path.refl (g a)⟩ = H := by
  ext a
  simp [SimplicialHomotopy.comp]

theorem homotopy_comp_refl_left {A : Type u} {B : Type v} {f g : A → B}
    (H : SimplicialHomotopy f g) :
    (⟨fun a => Path.refl (f a)⟩ : SimplicialHomotopy f f).comp H = H := by
  ext a
  simp [SimplicialHomotopy.comp]

def SimplicialHomotopy.ofPathFamily {A : Type u} {B : Type v} {f g : A → B}
    (H : ∀ a, f a = g a) : SimplicialHomotopy f g :=
  ⟨fun a => Path.ofEq (H a)⟩

/-! ## 29–33. Functoriality on triangles -/

/-- Map a triangle along a function using `congrArg`. -/
def Triangle.mapF {A : Type u} {B : Type v} (f : A → B) (t : Triangle A) : Triangle B :=
  { v₀ := f t.v₀
    v₁ := f t.v₁
    v₂ := f t.v₂
    e₀₁ := Path.congrArg f t.e₀₁
    e₁₂ := Path.congrArg f t.e₁₂
    e₀₂ := Path.congrArg f t.e₀₂
    filler := by
      rw [← Path.congrArg_trans f t.e₀₁ t.e₁₂]
      exact _root_.congrArg (Path.congrArg f) t.filler }

theorem triangle_mapF_id_vertices {A : Type u} (t : Triangle A) :
    (Triangle.mapF id t).v₀ = t.v₀ ∧
    (Triangle.mapF id t).v₁ = t.v₁ ∧
    (Triangle.mapF id t).v₂ = t.v₂ :=
  ⟨rfl, rfl, rfl⟩

theorem mapF_nerve₂ {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (Triangle.mapF f (nerve₂ p q)).e₀₂ =
      Path.congrArg f (Path.trans p q) := rfl

/-! ## 34–36. Deep calc: pentagon and inverse distribution -/

theorem simplicial_pentagon {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s)) := by
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) :=
        Path.trans_assoc (Path.trans p q) r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)

theorem inv_triple_simplicial {A : Type u} {a : A} (p q r : Path a a) :
    Path.symm (Path.trans (Path.trans p q) r) =
      Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) :=
        Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

theorem simplicial_sixfold {A : Type u} {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
      Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
        Path.trans_assoc _ s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) :=
        Path.trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
        Path.trans_assoc p q _

/-! ## 37. A filler is determined by an equality target -/

theorem filler_determined {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c)
    (r₁ r₂ : Path a c)
    (h₁ : Path.trans p q = r₁) (h₂ : Path.trans p q = r₂) :
    r₁ = r₂ := by
  rw [← h₁, ← h₂]

end SimplicialDeep
end Path
end ComputationalPaths
