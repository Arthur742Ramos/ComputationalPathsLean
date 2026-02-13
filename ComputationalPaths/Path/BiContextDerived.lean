/-
# Derived Bi-Context Lemmas

Derived lemmas for bi-contextual rewriting.  We prove coherence results for
the `BiContext` and `DepBiContext` structures, including interactions with
path composition, symmetry, and the rewrite system.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace BiContextDerived

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## BiContext map coherence -/

/-- `mapLeft` with refl produces `refl`. -/
theorem mapLeft_refl_eq (K : BiContext A B C) (a : A) (b : B) :
    BiContext.mapLeft K (Path.refl a) b = Path.refl (K.fill a b) := by
  simp

/-- `mapRight` with refl produces `refl`. -/
theorem mapRight_refl_eq (K : BiContext A B C) (a : A) (b : B) :
    BiContext.mapRight K a (Path.refl b) = Path.refl (K.fill a b) := by
  simp

/-- `map2` with both refl produces `refl`. -/
theorem map2_refl_refl_eq (K : BiContext A B C) (a : A) (b : B) :
    BiContext.map2 K (Path.refl a) (Path.refl b) = Path.refl (K.fill a b) := by
  simp

/-- `mapLeft` commutes with symmetry. -/
theorem mapLeft_symm_eq (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    BiContext.mapLeft K (Path.symm p) b =
      Path.symm (BiContext.mapLeft K p b) := by
  simp

/-- `mapRight` commutes with symmetry. -/
theorem mapRight_symm_eq (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    BiContext.mapRight K a (Path.symm p) =
      Path.symm (BiContext.mapRight K a p) := by
  simp

/-- `mapLeft` distributes over composition. -/
theorem mapLeft_trans_eq (K : BiContext A B C)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B) :
    BiContext.mapLeft K (Path.trans p q) b =
      Path.trans (BiContext.mapLeft K p b) (BiContext.mapLeft K q b) := by
  simp

/-- `mapRight` distributes over composition. -/
theorem mapRight_trans_eq (K : BiContext A B C)
    (a : A) {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    BiContext.mapRight K a (Path.trans p q) =
      Path.trans (BiContext.mapRight K a p) (BiContext.mapRight K a q) := by
  simp

/-! ## BiContext fixLeft/fixRight interactions -/

/-- Mapping through `fixRight` yields `mapLeft`. -/
theorem map_fixRight_eq (K : BiContext A B C) (b : B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Context.map (BiContext.fixRight K b) p = BiContext.mapLeft K p b := by
  simp

/-- Mapping through `fixLeft` yields `mapRight`. -/
theorem map_fixLeft_eq (K : BiContext A B C) (a : A)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    Context.map (BiContext.fixLeft K a) p = BiContext.mapRight K a p := by
  simp

/-! ## BiContext substitution lemmas -/

/-- Left substitution through a fixed-right context. -/
theorem substLeft_fixRight (K : BiContext A B C)
    (b : B) {x : C} {a₁ a₂ : A}
    (h : Path x (K.fill a₁ b)) (p : Path a₁ a₂) :
    Context.substLeft (BiContext.fixRight K b) h p =
      Path.trans h (BiContext.mapLeft K p b) := by
  simp [Context.substLeft]

/-- Right substitution through a fixed-right context. -/
theorem substRight_fixRight (K : BiContext A B C)
    (b : B) {a₁ a₂ : A} {y : C}
    (p : Path a₁ a₂) (h : Path (K.fill a₂ b) y) :
    Context.substRight (BiContext.fixRight K b) p h =
      Path.trans (BiContext.mapLeft K p b) h := by
  simp [Context.substRight]

/-- Left substitution through a fixed-left context. -/
theorem substLeft_fixLeft (K : BiContext A B C)
    (a : A) {x : C} {b₁ b₂ : B}
    (h : Path x (K.fill a b₁)) (p : Path b₁ b₂) :
    Context.substLeft (BiContext.fixLeft K a) h p =
      Path.trans h (BiContext.mapRight K a p) := by
  simp [Context.substLeft]

/-- Right substitution through a fixed-left context. -/
theorem substRight_fixLeft (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} {y : C}
    (p : Path b₁ b₂) (h : Path (K.fill a b₂) y) :
    Context.substRight (BiContext.fixLeft K a) p h =
      Path.trans (BiContext.mapRight K a p) h := by
  simp [Context.substRight]

/-! ## map2 interaction with path algebra -/

/-- `map2` with `refl` on the left has the same `toEq` as `mapRight`. -/
theorem map2_refl_left_toEq (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (q : Path b₁ b₂) :
    (BiContext.map2 K (Path.refl a) q).toEq =
      (BiContext.mapRight K a q).toEq := by
  simp

/-- `map2` with `refl` on the right has the same `toEq` as `mapLeft`. -/
theorem map2_refl_right_toEq (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    (BiContext.map2 K p (Path.refl b)).toEq =
      (BiContext.mapLeft K p b).toEq := by
  simp

/-! ## Concrete BiContext constructions -/

/-- The addition bi-context on natural numbers. -/
def addContext : BiContext Nat Nat Nat :=
  ⟨fun a b => a + b⟩

/-- Mapping a path through the left component of addition. -/
theorem addContext_mapLeft_toEq (a₁ a₂ : Nat) (b : Nat)
    (p : Path a₁ a₂) :
    (BiContext.mapLeft addContext p b).toEq =
      _root_.congrArg (· + b) p.toEq := by
  simp [addContext]

/-- Mapping a path through the right component of addition. -/
theorem addContext_mapRight_toEq (a : Nat) (b₁ b₂ : Nat)
    (p : Path b₁ b₂) :
    (BiContext.mapRight addContext a p).toEq =
      _root_.congrArg (a + ·) p.toEq := by
  simp [addContext]

/-- The multiplication bi-context on natural numbers. -/
def mulContext : BiContext Nat Nat Nat :=
  ⟨fun a b => a * b⟩

/-- The pairing bi-context (same universe). -/
def pairContext' {α β : Type u} : BiContext α β (α × β) :=
  ⟨fun a b => (a, b)⟩

/-- Mapping through pairContext gives prodMk at toEq level. -/
theorem pairContext_map2_toEq {α β : Type u} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (BiContext.map2 (pairContext' (α := α) (β := β)) p q).toEq =
      (Path.prodMk p q).toEq := by
  simp [pairContext']

/-! ## Context composition -/

/-- The identity context. -/
def idContext : Context A A := ⟨fun a => a⟩

/-- Mapping through the identity context is the identity on paths. -/
theorem idContext_map {a b : A} (p : Path a b) :
    Context.map idContext p = Path.congrArg (fun x => x) p := rfl

/-- Composing with the identity context on the right. -/
theorem comp_idContext_right {B' : Type v} (C' : Context A B') :
    Context.comp C' idContext = C' := by
  simp [Context.comp, idContext]

/-- Composing with the identity context on the left. -/
theorem comp_idContext_left {B' : Type v} (C' : Context A B') :
    Context.comp idContext C' = C' := by
  simp [Context.comp, idContext]

/-! ## Path coherence witnesses -/

/-- Path witness: `mapLeft` with `refl` yields `refl`. -/
def mapLeft_refl_path (K : BiContext A B C) (a : A) (b : B) :
    Path (K.fill a b) (K.fill a b) :=
  Path.refl (K.fill a b)

/-- Path witness: `map2` symmetry decomposition. -/
def map2_symm_path (K : BiContext A B C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (K.fill a₂ b₂) (K.fill a₁ b₁) :=
  BiContext.map2 K (Path.symm p) (Path.symm q)

/-- The symmetry of `map2` decomposes into right-then-left at toEq level. -/
theorem map2_symm_decomp (K : BiContext A B C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Path.symm (BiContext.map2 K p q)).toEq =
      (Path.trans
        (BiContext.mapRight K a₂ (Path.symm q))
        (BiContext.mapLeft K (Path.symm p) b₁)).toEq := by
  simp

/-! ## toEq-level bicontext lemmas -/

/-- `mapLeft` preserves `toEq`. -/
theorem mapLeft_toEq (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    (BiContext.mapLeft K p b).toEq =
      _root_.congrArg (fun a => K.fill a b) p.toEq := by
  simp

/-- `mapRight` preserves `toEq`. -/
theorem mapRight_toEq (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    (BiContext.mapRight K a p).toEq =
      _root_.congrArg (fun b => K.fill a b) p.toEq := by
  simp

/-- `mapLeft` on `ofEq h` gives `ofEq (congrArg _ h)` at toEq. -/
theorem mapLeft_ofEq_toEq (K : BiContext A B C)
    {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
    (BiContext.mapLeft K (Path.stepChain h) b).toEq =
      _root_.congrArg (fun a => K.fill a b) h := by
  simp

/-- `mapRight` on `ofEq h` gives `ofEq (congrArg _ h)` at toEq. -/
theorem mapRight_ofEq_toEq (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (h : b₁ = b₂) :
    (BiContext.mapRight K a (Path.stepChain h)).toEq =
      _root_.congrArg (fun b => K.fill a b) h := by
  simp

/-! ## Concrete examples -/

/-- A concrete bi-context map on Nat addition. -/
example : Path (2 + 3) (2 + 3) :=
  BiContext.mapLeft addContext (Path.refl 2) 3

/-- A concrete bi-context map on multiplication. -/
example : Path (2 * 3) (2 * 3) :=
  BiContext.mapRight mulContext 2 (Path.refl 3)

end BiContextDerived
end Path
end ComputationalPaths
