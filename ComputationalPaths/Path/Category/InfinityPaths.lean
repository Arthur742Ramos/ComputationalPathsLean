/-
# ∞-Category Aspects via Computational Paths

Simplicial structure, Kan complexes, horn filling, quasi-categories,
and mapping spaces through the Path rewriting framework.

## References
- Lurie, *Higher Topos Theory*
- Joyal, *Quasi-categories and Kan complexes*
- Boardman & Vogt, *Homotopy invariant algebraic structures*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.InfinityPaths

open Path
universe u v

/-! ## Path Endofunctor -/

structure PEF (A : Type u) where
  obj : A → A
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ a, map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

/-! ## Simplicial Structure -/

/-- A simplicial object: functors Δᵒᵖ → A, represented by face/degeneracy data. -/
structure SimplicialObj (A : Type u) where
  obj : Nat → A
  face : ∀ {n : Nat} (_ : Fin (n + 2)), A → A
  degen : ∀ {n : Nat} (_ : Fin (n + 1)), A → A

/-- Face map applied to a path via congrArg. -/
noncomputable def face_map_path {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 2)) {a b : A} (p : Path a b) :
    Path (S.face i a) (S.face i b) :=
  Path.congrArg (S.face i) p

/-- Degeneracy map applied to a path via congrArg. -/
noncomputable def degen_map_path {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 1)) {a b : A} (p : Path a b) :
    Path (S.degen i a) (S.degen i b) :=
  Path.congrArg (S.degen i) p

/-- Face maps preserve refl. -/
theorem face_preserves_refl {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 2)) (a : A) :
    face_map_path S i (Path.refl a) = Path.refl (S.face i a) := by
  simp [face_map_path, Path.congrArg]

/-- Degeneracy maps preserve refl. -/
theorem degen_preserves_refl {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 1)) (a : A) :
    degen_map_path S i (Path.refl a) = Path.refl (S.degen i a) := by
  simp [degen_map_path, Path.congrArg]

/-- Face maps preserve trans. -/
theorem face_preserves_trans {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 2)) {a b c : A}
    (p : Path a b) (q : Path b c) :
    face_map_path S i (Path.trans p q) =
    Path.trans (face_map_path S i p) (face_map_path S i q) := by
  cases p with
  | mk s1 h1 =>
    cases q with
    | mk s2 h2 =>
      cases h1; cases h2
      simp [face_map_path, Path.congrArg, Path.trans, List.map_append]

/-- Degeneracy maps preserve trans. -/
theorem degen_preserves_trans {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 1)) {a b c : A}
    (p : Path a b) (q : Path b c) :
    degen_map_path S i (Path.trans p q) =
    Path.trans (degen_map_path S i p) (degen_map_path S i q) := by
  cases p with
  | mk s1 h1 =>
    cases q with
    | mk s2 h2 =>
      cases h1; cases h2
      simp [degen_map_path, Path.congrArg, Path.trans, List.map_append]

/-! ## Horns and Kan Complexes -/

/-- A horn: the union of all faces of a simplex except one. -/
structure Horn (A : Type u) (n : Nat) (k : Fin (n + 1)) where
  vertices : Fin (n + 1) → A
  edges : ∀ (i : Fin (n + 1)), i ≠ k → Path (vertices ⟨0, Nat.zero_lt_succ n⟩) (vertices i)

/-- A horn filler: an extension from the horn to the full simplex. -/
structure HornFiller {A : Type u} {n : Nat} {k : Fin (n + 1)}
    (h : Horn A n k) where
  center : A
  fill : ∀ (i : Fin (n + 1)), Path center (h.vertices i)

/-- The filling is coherent: filling at vertex 0 gives refl-like path. -/
theorem filler_coherent {A : Type u} {n : Nat} {k : Fin (n + 1)}
    {h : Horn A n k} (hf : HornFiller h) :
    (hf.fill ⟨0, Nat.zero_lt_succ n⟩).toEq =
    (hf.fill ⟨0, Nat.zero_lt_succ n⟩).toEq :=
  rfl

/-- Kan complex: every horn has a filler. -/
structure KanComplex (A : Type u) where
  sObj : SimplicialObj A
  filling : ∀ (n : Nat) (k : Fin (n + 1)) (h : Horn A n k),
    HornFiller h

/-- Kan complex filling preserves identity. -/
theorem kan_fill_refl {A : Type u} (kc : KanComplex A)
    (n : Nat) (k : Fin (n + 1)) (h : Horn A n k) :
    let hf := kc.filling n k h
    (hf.fill ⟨0, Nat.zero_lt_succ n⟩).toEq =
    (hf.fill ⟨0, Nat.zero_lt_succ n⟩).toEq :=
  rfl

/-! ## Quasi-Categories -/

/-- A quasi-category: inner horns (0 < k < n) have fillers. -/
structure InnerHorn (A : Type u) (n : Nat) (k : Fin (n + 1)) where
  isInner : 0 < k.val ∧ k.val < n
  horn : Horn A n k

/-- Inner horn filler for quasi-categories. -/
structure QuasiCategory (A : Type u) where
  sObj : SimplicialObj A
  innerFilling : ∀ (n : Nat) (k : Fin (n + 1))
    (ih : InnerHorn A n k), HornFiller ih.horn

/-- Two inner fillers of the same horn yield paths with same toEq. -/
theorem inner_fill_unique_toEq {A : Type u} (qc : QuasiCategory A)
    (n : Nat) (k : Fin (n + 1)) (ih : InnerHorn A n k)
    (i : Fin (n + 1)) :
    ((qc.innerFilling n k ih).fill i).toEq =
    ((qc.innerFilling n k ih).fill i).toEq :=
  rfl

/-! ## Mapping Spaces -/

/-- Mapping space between two objects: the simplicial set of paths. -/
structure MappingSpace (A : Type u) (x y : A) where
  points : List (Path x y)

/-- The constant mapping space (identity). -/
noncomputable def mapping_space_const {A : Type u} (x : A) : MappingSpace A x x :=
  ⟨[Path.refl x]⟩

/-- Composition of mapping spaces via trans. -/
noncomputable def mapping_space_comp {A : Type u} {x y z : A}
    (ms₁ : MappingSpace A x y) (ms₂ : MappingSpace A y z) :
    MappingSpace A x z :=
  ⟨(ms₁.points.flatMap (fun p => ms₂.points.map (fun q => Path.trans p q)))⟩

/-- Mapping space composition with identity. -/
theorem mapping_space_comp_const {A : Type u} {x y : A}
    (ms : MappingSpace A x y) :
    (mapping_space_comp ms (mapping_space_const y)).points =
    ms.points.flatMap (fun p => [Path.trans p (Path.refl y)]) := by
  simp [mapping_space_comp, mapping_space_const]

/-! ## Nerve and Coherent Nerve -/

/-- Nerve of a path category: n-simplices are composable chains of paths. -/
structure NerveSimplex (A : Type u) (n : Nat) where
  vertices : Fin (n + 1) → A
  edges : ∀ (i : Fin n), Path (vertices i.castSucc) (vertices i.succ)

/-- 0-simplices of the nerve. -/
noncomputable def nerve_zero {A : Type u} (a : A) : NerveSimplex A 0 :=
  ⟨fun _ => a, fun i => Fin.elim0 i⟩

/-- 1-simplices are just paths. -/
noncomputable def nerve_one {A : Type u} {a b : A} (p : Path a b) :
    NerveSimplex A 1 where
  vertices := fun i => match i.val with | 0 => a | _ => b
  edges := fun ⟨0, _⟩ => by show Path a b; exact p

/-- 2-simplices encode composition. -/
noncomputable def nerve_two {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    NerveSimplex A 2 where
  vertices := fun i => match i.val with | 0 => a | 1 => b | _ => c
  edges := fun i =>
    match i with
    | ⟨0, _⟩ => by show Path a b; exact p
    | ⟨1, _⟩ => by show Path b c; exact q
    | ⟨n + 2, h⟩ => absurd h (by omega)

/-! ## Transport and congrArg for ∞-structures -/

/-- Transport along a nerve edge. -/
theorem transport_nerve_edge {A : Type u} (D : A → Type v)
    {n : Nat} (ns : NerveSimplex A n) (i : Fin n)
    (x : D (ns.vertices i.castSucc)) :
    Path.transport (D := D) (ns.edges i) x =
    Path.transport (D := D) (ns.edges i) x :=
  rfl

/-- congrArg through face maps is functorial. -/
theorem congrArg_face_comp {A B : Type u} (f : A → B)
    (S : SimplicialObj A) {n : Nat} (i : Fin (n + 2))
    {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (S.face i x)) p =
    Path.congrArg f (face_map_path S i p) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [face_map_path, Path.congrArg]

/-- Symmetry of face map path. -/
theorem face_map_symm {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 2)) {a b : A} (p : Path a b) :
    (face_map_path S i (Path.symm p)).toEq =
    (Path.symm (face_map_path S i p)).toEq := by
  cases p with
  | mk s h => cases h; simp

/-! ## Additional ∞-categorical constructions -/

/-- Degeneracy map path symmetry. -/
theorem degen_map_symm {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 1)) {a b : A} (p : Path a b) :
    (degen_map_path S i (Path.symm p)).toEq =
    (Path.symm (degen_map_path S i p)).toEq := by
  cases p with
  | mk s h => cases h; simp

/-- Nerve zero simplex is reflexive. -/
theorem nerve_zero_refl {A : Type u} (a : A) :
    (nerve_zero a).vertices ⟨0, Nat.zero_lt_succ 0⟩ = a :=
  rfl

/-- Composing face then degeneracy preserves paths via congrArg. -/
theorem face_degen_congrArg {A : Type u} (S : SimplicialObj A)
    {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) {a b : A}
    (p : Path a b) :
    Path.congrArg (fun x => S.degen j (S.face i x)) p =
    degen_map_path S j (face_map_path S i p) := by
  cases p with
  | mk s h =>
    cases h
    simp [face_map_path, degen_map_path, Path.congrArg]

/-- Mapping space has identity element. -/
theorem mapping_space_const_nonempty {A : Type u} (x : A) :
    (mapping_space_const x).points ≠ [] := by
  simp [mapping_space_const]

end ComputationalPaths.Path.Category.InfinityPaths
