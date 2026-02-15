/-
# Deep Simplicial Homotopy Theory via Computational Paths

Face and degeneracy operators on path-level simplicial structures, simplicial
identities proved via multi-step calc chains, Kan conditions, horn fillers,
and the nerve construction — all built from Path/Step/trans/symm.

## References
- May, "Simplicial Objects in Algebraic Topology"
- Goerss–Jardine, "Simplicial Homotopy Theory"
-/

import ComputationalPaths.Path.Basic.Core

set_option maxHeartbeats 800000

namespace ComputationalPaths
namespace Path
namespace SimplicialDeep

universe u v

/-! ## Simplicial chain type -/

/-- A simplex of dimension n is a chain of (n+1) vertices connected by n paths. -/
inductive Chain (A : Type u) : Nat → Type u where
  | vertex : A → Chain A 0
  | edge   : {n : Nat} → Chain A n → (src tgt : A) → Path src tgt → Chain A (n + 1)

def Chain.lastVertex {A : Type u} : {n : Nat} → Chain A n → A
  | 0, Chain.vertex a => a
  | _ + 1, Chain.edge _ _ tgt _ => tgt

def Chain.firstVertex {A : Type u} : {n : Nat} → Chain A n → A
  | 0, Chain.vertex a => a
  | _ + 1, Chain.edge c _ _ _ => c.firstVertex

/-! ## Face and degeneracy operators -/

def faceLast {A : Type u} : {n : Nat} → Chain A (n + 1) → Chain A n
  | _, Chain.edge c _ _ _ => c

def degenLast {A : Type u} : {n : Nat} → Chain A n → Chain A (n + 1)
  | 0, Chain.vertex a => Chain.edge (Chain.vertex a) a a (Path.refl a)
  | _, Chain.edge c s t p => Chain.edge (Chain.edge c s t p) t t (Path.refl t)

/-! ## 1. faceLast ∘ degenLast = id -/

theorem faceLast_degenLast {A : Type u} {n : Nat} (c : Chain A n) :
    faceLast (degenLast c) = c := by
  cases c with
  | vertex a => rfl
  | edge c s t p => rfl

/-! ## 2-simplex: Triangle -/

structure Triangle (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂
  e₀₂ : Path v₀ v₂
  filler : Path.trans e₀₁ e₁₂ = e₀₂

/-! ## 2–3. Degenerate triangles -/

def Triangle.degenLeft {A : Type u} {a b : A} (p : Path a b) : Triangle A :=
  ⟨a, a, b, Path.refl a, p, p, Path.trans_refl_left p⟩

def Triangle.degenRight {A : Type u} {a b : A} (p : Path a b) : Triangle A :=
  ⟨a, b, b, p, Path.refl b, p, Path.trans_refl_right p⟩

theorem degen_left_filler_eq {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenLeft p).filler = Path.trans_refl_left p := rfl

theorem degen_right_filler_eq {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenRight p).filler = Path.trans_refl_right p := rfl

/-! ## 4. 3-simplex: Tetrahedron (associativity witness) -/

structure Tetrahedron (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A; v₃ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂
  e₂₃ : Path v₂ v₃
  assoc_witness : Path.trans (Path.trans e₀₁ e₁₂) e₂₃ =
                  Path.trans e₀₁ (Path.trans e₁₂ e₂₃)

def mkTetrahedron {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Tetrahedron A :=
  ⟨a, b, c, d, p, q, r, Path.trans_assoc p q r⟩

/-! ## 5. Tetrahedron boundary -/

theorem tetrahedron_assoc_is_std {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (mkTetrahedron p q r).assoc_witness = Path.trans_assoc p q r := rfl

/-! ## 6–7. Horn21 and its filler -/

structure Horn21 (A : Type u) where
  v₀ : A
  v₁ : A
  v₂ : A
  e₀₁ : Path v₀ v₁
  e₁₂ : Path v₁ v₂

def fillHorn21 {A : Type u} (h : Horn21 A) : Triangle A :=
  ⟨h.v₀, h.v₁, h.v₂, h.e₀₁, h.e₁₂, Path.trans h.e₀₁ h.e₁₂, rfl⟩

theorem horn21_filler_composite {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (fillHorn21 ⟨a, b, c, p, q⟩).e₀₂ = Path.trans p q := rfl

/-! ## 8. Degenerate horn fill -/

theorem degen_horn_fill {A : Type u} {a : A} :
    (fillHorn21 ⟨a, a, a, Path.refl a, Path.refl a⟩).e₀₂ =
    Path.trans (Path.refl a) (Path.refl a) := rfl

/-! ## 9–10. Nerve construction -/

def nerve₀ {A : Type u} (a : A) : Chain A 0 := Chain.vertex a

def nerve₁ {A : Type u} {a b : A} (p : Path a b) : Chain A 1 :=
  Chain.edge (Chain.vertex a) a b p

theorem nerve₁_faceLast {A : Type u} {a b : A} (p : Path a b) :
    faceLast (nerve₁ p) = nerve₀ a := rfl

def nerve₂ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) : Triangle A :=
  ⟨a, b, c, p, q, Path.trans p q, rfl⟩

theorem nerve₂_filler {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    (nerve₂ p q).filler = rfl := rfl

/-! ## 11. Simplicial identity: d_last ∘ s_last = id on nerve₁ -/

theorem simplicial_id_degen_face {A : Type u} {a b : A} (p : Path a b) :
    faceLast (degenLast (nerve₁ p)) = nerve₁ p := by
  calc faceLast (degenLast (nerve₁ p))
      = faceLast (Chain.edge (nerve₁ p) b b (Path.refl b)) := by rfl
    _ = nerve₁ p := by rfl

/-! ## 12. Double degen / double face calc -/

theorem double_degen_double_face {A : Type u} {a : A} :
    faceLast (faceLast (degenLast (degenLast (Chain.vertex a)))) =
    Chain.vertex a := by
  calc faceLast (faceLast (degenLast (degenLast (Chain.vertex a))))
      = faceLast (faceLast (degenLast
          (Chain.edge (Chain.vertex a) a a (Path.refl a)))) := by rfl
    _ = faceLast (faceLast (Chain.edge
          (Chain.edge (Chain.vertex a) a a (Path.refl a)) a a (Path.refl a))) := by rfl
    _ = faceLast (Chain.edge (Chain.vertex a) a a (Path.refl a)) := by rfl
    _ = Chain.vertex a := by rfl

/-! ## 13. Triple face / triple degen calc -/

theorem triple_face_triple_degen {A : Type u} {a : A} :
    faceLast (faceLast (faceLast
      (degenLast (degenLast (degenLast (Chain.vertex a)))))) =
    Chain.vertex a := by
  calc faceLast (faceLast (faceLast
        (degenLast (degenLast (degenLast (Chain.vertex a))))))
      = faceLast (faceLast (faceLast
          (degenLast (degenLast
            (Chain.edge (Chain.vertex a) a a (Path.refl a)))))) := by rfl
    _ = faceLast (faceLast (faceLast
          (degenLast (Chain.edge
            (Chain.edge (Chain.vertex a) a a (Path.refl a))
            a a (Path.refl a))))) := by rfl
    _ = faceLast (faceLast (faceLast
          (Chain.edge
            (Chain.edge
              (Chain.edge (Chain.vertex a) a a (Path.refl a))
              a a (Path.refl a))
            a a (Path.refl a)))) := by rfl
    _ = faceLast (faceLast
          (Chain.edge
            (Chain.edge (Chain.vertex a) a a (Path.refl a))
            a a (Path.refl a))) := by rfl
    _ = faceLast (Chain.edge (Chain.vertex a) a a (Path.refl a)) := by rfl
    _ = Chain.vertex a := by rfl

/-! ## 14. Kan condition: inner horn -/

theorem kan_inner_horn {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    ∃ t : Triangle A, t.e₀₁ = p ∧ t.e₁₂ = q ∧
      t.e₀₂ = Path.trans p q :=
  ⟨⟨a, b, c, p, q, Path.trans p q, rfl⟩, rfl, rfl, rfl⟩

/-! ## 15. Kan condition: left horn (given e₀₁, e₀₂, find e₁₂) -/

theorem kan_left_horn {A : Type u} {a b c : A}
    (p : Path a b) (r : Path a c) :
    ∃ q : Path b c, Path.trans p q = r := by
  cases p with
  | mk sp hp =>
    cases hp
    exact ⟨r, Path.trans_refl_left r⟩

/-! ## 16. Kan condition: right horn (given e₁₂, e₀₂, find e₀₁) -/

theorem kan_right_horn {A : Type u} {a b c : A}
    (q : Path b c) (r : Path a c) :
    ∃ p : Path a b, Path.trans p q = r := by
  cases q with
  | mk sq hq =>
    cases hq
    exact ⟨r, Path.trans_refl_right r⟩

/-! ## 17. Triangle reversal -/

def Triangle.reverse {A : Type u} (t : Triangle A) : Triangle A :=
  ⟨t.v₂, t.v₁, t.v₀,
   Path.symm t.e₁₂, Path.symm t.e₀₁, Path.symm t.e₀₂,
   by rw [← Path.symm_trans t.e₀₁ t.e₁₂, t.filler]⟩

/-! ## 18. Double reversal preserves vertices -/

theorem triangle_reverse_reverse_vertices {A : Type u} (t : Triangle A) :
    (t.reverse.reverse).v₀ = t.v₀ ∧
    (t.reverse.reverse).v₁ = t.v₁ ∧
    (t.reverse.reverse).v₂ = t.v₂ :=
  ⟨rfl, rfl, rfl⟩

/-! ## 19–20. Whiskering in simplicial context -/

theorem whisker_left_triangle {A : Type u} {a b c : A}
    (p : Path a b) (q q' : Path b c) (h : q = q') :
    (nerve₂ p q).e₀₂ = (nerve₂ p q').e₀₂ := by subst h; rfl

theorem whisker_right_triangle {A : Type u} {a b c : A}
    (p p' : Path a b) (q : Path b c) (h : p = p') :
    (nerve₂ p q).e₀₂ = (nerve₂ p' q).e₀₂ := by subst h; rfl

/-! ## 21. Simplicial homotopy -/

@[ext]
structure SimplicialHomotopy {A : Type u} {B : Type v} (f g : A → B) where
  homotopy : (a : A) → Path (f a) (g a)

/-! ## 22. Reverse homotopy, double reversal -/

def SimplicialHomotopy.reverse {A : Type u} {B : Type v} {f g : A → B}
    (h : SimplicialHomotopy f g) : SimplicialHomotopy g f :=
  ⟨fun a => Path.symm (h.homotopy a)⟩

theorem homotopy_reverse_reverse {A : Type u} {B : Type v}
    {f g : A → B} (h : SimplicialHomotopy f g) :
    h.reverse.reverse = h := by
  ext a; exact Path.symm_symm (h.homotopy a)

/-! ## 23. Homotopy composition -/

def SimplicialHomotopy.comp {A : Type u} {B : Type v} {f g h : A → B}
    (H₁ : SimplicialHomotopy f g) (H₂ : SimplicialHomotopy g h) :
    SimplicialHomotopy f h :=
  ⟨fun a => Path.trans (H₁.homotopy a) (H₂.homotopy a)⟩

/-! ## 24. Homotopy composition associativity -/

theorem homotopy_comp_assoc {A : Type u} {B : Type v} {f g h k : A → B}
    (H₁ : SimplicialHomotopy f g) (H₂ : SimplicialHomotopy g h)
    (H₃ : SimplicialHomotopy h k) :
    (H₁.comp H₂).comp H₃ = H₁.comp (H₂.comp H₃) := by
  ext a; exact Path.trans_assoc _ _ _

/-! ## 25. Homotopy unit laws -/

theorem homotopy_comp_refl_right {A : Type u} {B : Type v} {f g : A → B}
    (H : SimplicialHomotopy f g) :
    H.comp ⟨fun a => Path.refl (g a)⟩ = H := by
  ext a; simp [SimplicialHomotopy.comp]

theorem homotopy_comp_refl_left {A : Type u} {B : Type v} {f g : A → B}
    (H : SimplicialHomotopy f g) :
    (⟨fun a => Path.refl (f a)⟩ : SimplicialHomotopy f f).comp H = H := by
  ext a; simp [SimplicialHomotopy.comp]

/-! ## 26. congrArg preserves triangles (functoriality) -/

def Triangle.map {A : Type u} {B : Type v} (f : A → B) (t : Triangle A) : Triangle B :=
  ⟨f t.v₀, f t.v₁, f t.v₂,
   Path.congrArg f t.e₀₁, Path.congrArg f t.e₁₂, Path.congrArg f t.e₀₂,
   by rw [← Path.congrArg_trans f t.e₀₁ t.e₁₂]
      exact _root_.congrArg (Path.congrArg f) t.filler⟩

/-! ## 27. Triangle.map preserves identity -/

theorem triangle_map_id {A : Type u} (t : Triangle A) :
    (Triangle.map id t).v₀ = t.v₀ ∧
    (Triangle.map id t).v₁ = t.v₁ ∧
    (Triangle.map id t).v₂ = t.v₂ :=
  ⟨rfl, rfl, rfl⟩

/-! ## 28. Pentagon via simplicial calc -/

theorem simplicial_pentagon {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) :=
        Path.trans_assoc (Path.trans p q) r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)

/-! ## 29. Sixfold reassociation via calc -/

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

/-! ## 30. Inverse horn filler -/

theorem horn21_inverse_filler {A : Type u} {a b : A} (p : Path a b) :
    (fillHorn21 ⟨b, a, b, Path.symm p, p⟩).e₀₂ =
    Path.trans (Path.symm p) p := rfl

/-! ## 31. Degenerate triangle edge recovery -/

theorem degen_left_e₀₂ {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenLeft p).e₀₂ = p := rfl

theorem degen_right_e₀₂ {A : Type u} {a b : A} (p : Path a b) :
    (Triangle.degenRight p).e₀₂ = p := rfl

/-! ## 32. Inverse distribution over triple trans -/

theorem inv_triple_simplicial {A : Type u} {a : A} (p q r : Path a a) :
    Path.symm (Path.trans (Path.trans p q) r) =
    Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) :=
        Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-! ## 33. Inverse distribution over fourfold trans -/

theorem inv_four_simplicial {A : Type u} {a : A} (p q r s : Path a a) :
    Path.symm (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.symm s)
      (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
  calc Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (Path.symm s) (Path.symm (Path.trans (Path.trans p q) r)) :=
        Path.symm_trans _ s
    _ = Path.trans (Path.symm s)
          (Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p))) := by
        rw [inv_triple_simplicial p q r]

/-! ## 34. Nerve₂ of refl -/

theorem nerve₂_refl {A : Type u} {a : A} :
    nerve₂ (Path.refl a) (Path.refl a) =
    ⟨a, a, a, Path.refl a, Path.refl a,
     Path.trans (Path.refl a) (Path.refl a), rfl⟩ := rfl

/-! ## 35. Simplicial homotopy from path family -/

def SimplicialHomotopy.ofPathFamily {A : Type u} {B : Type v} {f g : A → B}
    (H : ∀ a, f a = g a) : SimplicialHomotopy f g :=
  ⟨fun a => Path.ofEq (H a)⟩

/-! ## 36. Degenerate tetrahedron -/

def degenTetrahedron {A : Type u} {a b : A} (p : Path a b) : Tetrahedron A :=
  ⟨a, a, b, b, Path.refl a, p, Path.refl b, by simp⟩

/-! ## 37. Chain length function -/

def Chain.dim {A : Type u} : {n : Nat} → Chain A n → Nat
  | n, _ => n

theorem chain_dim_vertex {A : Type u} (a : A) :
    Chain.dim (Chain.vertex a) = 0 := rfl

theorem chain_dim_degenLast {A : Type u} {n : Nat} (c : Chain A n) :
    Chain.dim (degenLast c) = n + 1 := rfl

/-! ## 38. Degeneracy raises dimension -/

theorem degen_raises_dim {A : Type u} {n : Nat} (c : Chain A n) :
    Chain.dim (degenLast c) = Chain.dim c + 1 := rfl

/-! ## 39. Face lowers dimension -/

theorem face_lowers_dim {A : Type u} {n : Nat} (c : Chain A (n + 1)) :
    Chain.dim (faceLast c) = Chain.dim c - 1 := by
  simp [Chain.dim]

/-! ## 40. Filler determined by boundary edges -/

theorem filler_determined {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c)
    (r₁ r₂ : Path a c)
    (h₁ : Path.trans p q = r₁) (h₂ : Path.trans p q = r₂) :
    r₁ = r₂ := by
  rw [← h₁, ← h₂]

end SimplicialDeep
end Path
end ComputationalPaths
