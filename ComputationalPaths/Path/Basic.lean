/-
# Basic combinators for computational paths

We refine the notion of a computational path so that, in addition to the
underlying propositional equality, each path records an explicit sequence of
rewrite steps.  This mirrors the presentation in
*Propositional Equality, Identity Types, and Computational Paths* where a proof
of equality is witnessed by a concrete list of rewrites.
-/

namespace List

@[simp] theorem map_reverse_eq_reverse_map {α β : Type _}
    (f : α → β) (xs : List α) :
    xs.reverse.map f = (xs.map f).reverse := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.reverse_cons, ih, List.map_append, List.map_cons]

end List

namespace ComputationalPaths

open List Function

universe u v w

/-- An elementary rewrite step between two elements of `A`.  The fields record
the source, the target, and the propositional equality justifying the step. -/
structure Step (A : Type u) where
  src : A
  tgt : A
  proof : src = tgt

namespace Step

variable {A : Type u} {B : Type v}

/-- Reverse the direction of a rewrite step. -/
@[simp] def symm (s : Step A) : Step A :=
  ⟨s.tgt, s.src, s.proof.symm⟩

/-- Map a rewrite step through a function. -/
@[simp] def map (f : A → B) (s : Step A) : Step B :=
  ⟨f s.src, f s.tgt, congrArg f s.proof⟩

@[simp] theorem symm_symm (s : Step A) : symm (symm s) = s := by
  cases s
  rfl

@[simp] theorem map_symm (f : A → B) (s : Step A) :
    map f (symm s) = symm (map f s) := by
  cases s
  rfl

@[simp] theorem map_id (s : Step A) :
    map (fun x : A => x) s = s := by
  cases s
  simp [map]

end Step

/-- A computational path from `a` to `b`.  Besides the derived equality proof,
we store the explicit list of rewrite steps.  When composing paths we append
these lists, and when inverting a path we reverse the list and take the symmetric
of each step. -/
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b

namespace Path

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c d : A}
variable {a1 a2 a3 : A} {b1 b2 b3 : B}

/-- Helper showing that mapping the identity over step lists is a no-op. -/
@[simp] theorem steps_map_id (steps : List (Step A)) :
    steps.map (Step.map fun x : A => x) = steps := by
  induction steps with
  | nil => simp
  | cons s tail ih =>
      cases s
      simp [Step.map, ih]

/-- Extract the propositional equality witnessed by a path. -/
@[simp] def toEq (p : Path a b) : a = b :=
  p.proof

/-- Reflexive path (empty sequence of rewrites). -/
@[simp] def refl (a : A) : Path a a :=
  ⟨[], rfl⟩

/-- Path consisting of a single rewrite step. -/
@[simp] def ofEq (h : a = b) : Path a b :=
  ⟨[⟨a, b, h⟩], h⟩

@[simp] theorem toEq_ofEq (h : a = b) : toEq (ofEq h) = h := rfl

/-- Compose two paths, concatenating their step lists. -/
@[simp] def trans (p : Path a b) (q : Path b c) : Path a c :=
  ⟨p.steps ++ q.steps, p.proof.trans q.proof⟩

/-- Reverse a path by reversing and inverting each step. -/
@[simp] def symm (p : Path a b) : Path b a :=
  ⟨p.steps.reverse.map Step.symm, p.proof.symm⟩

@[simp] theorem trans_steps (p : Path a b) (q : Path b c) :
    (trans p q).steps = p.steps ++ q.steps := rfl

@[simp] theorem symm_steps (p : Path a b) :
    (symm p).steps = p.steps.reverse.map Step.symm := rfl

@[simp] theorem symm_trans (p : Path a b) (q : Path b c) :
    symm (trans p q) = trans (symm q) (symm p) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [symm, trans, List.reverse_append, List.map_append]

@[simp] theorem trans_refl_left (p : Path a b) : trans (refl a) p = p := by
  cases p
  simp

@[simp] theorem trans_refl_right (p : Path a b) : trans p (refl b) = p := by
  cases p
  simp

/-- Associativity of path composition. -/
@[simp] theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases r with
          | mk steps3 proof3 =>
              cases proof1
              cases proof2
              cases proof3
              simp [trans, List.append_assoc]

@[simp] theorem symm_refl (a : A) : symm (refl a) = refl a := by
  simp [symm, refl]

/-- Taking symmetry twice yields the original path. -/
@[simp] theorem symm_symm (p : Path a b) : symm (symm p) = p := by
  cases p with
  | mk steps proof =>
      cases proof
      have hcomp :
          Step.symm ∘ Step.symm = fun s : Step A => s := by
            funext s
            simp [Function.comp]
      simp [symm, List.reverse_reverse, List.map_map, hcomp]

@[simp] theorem toEq_trans (p : Path a b) (q : Path b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := rfl

@[simp] theorem toEq_symm (p : Path a b) : toEq (symm p) = (toEq p).symm := rfl

@[simp] theorem toEq_trans_symm (p : Path a b) :
    toEq (trans p (symm p)) = rfl := by
  cases p
  simp

@[simp] theorem toEq_symm_trans (p : Path a b) :
    toEq (trans (symm p) p) = rfl := by
  cases p
  simp

/-- Transport along a path. -/
def transport {D : A → Sort v} (p : Path a b) (x : D a) : D b :=
  p.proof ▸ x

@[simp] theorem transport_refl {D : A → Sort v} (x : D a) :
    transport (refl a) x = x := rfl

@[simp] theorem transport_trans {D : A → Sort v}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (trans p q) x =
      transport q (transport p x) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          rfl

@[simp] theorem transport_symm_left {D : A → Sort v}
    (p : Path a b) (x : D a) :
    transport (symm p) (transport p x) = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem transport_symm_right {D : A → Sort v}
    (p : Path a b) (y : D b) :
    transport p (transport (symm p) y) = y := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem transport_const {D : Type v} (p : Path a b) (x : D) :
    transport (a := a) (b := b) (D := fun _ => D) p x = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Substitution along a path, following the paper's notation. -/
def subst {D : A → Sort v} (x : D a) (p : Path a b) : D b :=
  transport p x

@[simp] theorem subst_refl {D : A → Sort v} (x : D a) :
    subst (D := D) x (Path.refl a) = x := rfl

@[simp] theorem subst_trans {D : A → Sort v}
    (x : D a) (p : Path a b) (q : Path b c) :
    subst (D := D) x (Path.trans p q) =
      subst (D := D) (subst (D := D) x p) q :=
  transport_trans (D := D) p q x

@[simp] theorem subst_symm_left {D : A → Sort v}
    (x : D a) (p : Path a b) :
    subst (D := D) (subst (D := D) x p) (Path.symm p) = x :=
  transport_symm_left (D := D) p x

@[simp] theorem subst_symm_right {D : A → Sort v}
    (y : D b) (p : Path a b) :
    subst (D := D) (subst (D := D) y (Path.symm p)) p = y :=
  transport_symm_right (D := D) p y

@[simp] theorem subst_const {D : Type v} (x : D) (p : Path a b) :
    subst (D := fun _ => D) x p = x :=
  transport_const (D := D) p x

@[simp] theorem subst_ofEq {D : A → Sort v} (x : D a) (h : a = b) :
    subst (D := D) x (Path.ofEq h) = h ▸ x := rfl

@[simp] theorem subst_symm_ofEq {D : A → Sort v} (y : D b) (h : a = b) :
    subst (D := D) y (Path.symm (Path.ofEq h)) = h.symm ▸ y := rfl

/-- Congruence of unary functions along paths. -/
@[simp] def congrArg (f : A → B) (p : Path a b) : Path (f a) (f b) :=
  ⟨p.steps.map (Step.map f), _root_.congrArg f p.proof⟩

/-- Unary congruence preserves concatenation. -/
@[simp] theorem congrArg_trans (f : A → B)
    (p : Path a b) (q : Path b c) :
    congrArg f (Path.trans p q) =
      Path.trans (congrArg f p) (congrArg f q) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [congrArg, Path.trans, List.map_append]

/-- Unary congruence commutes with symmetry. -/
@[simp] theorem congrArg_symm (f : A → B)
    (p : Path a b) :
    congrArg f (Path.symm p) =
      Path.symm (congrArg f p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [congrArg, Path.symm]

@[simp] theorem congrArg_id (p : Path a b) :
    congrArg (fun x : A => x) p = p := by
  cases p with
  | mk steps proof =>
      cases proof
      have h := steps_map_id (A := A) steps
      simp [congrArg, h]

/-- Congruence in the first argument of a binary function. -/
@[simp] def mapLeft (f : A → B → C) {a1 a2 : A} (p : Path a1 a2) (b : B) :
    Path (f a1 b) (f a2 b) :=
  ⟨p.steps.map (Step.map fun x => f x b), _root_.congrArg (fun x => f x b) p.proof⟩

/-- `mapLeft` is the unary congruence for the partial application `fun a => f a b`. -/
@[simp] theorem mapLeft_eq_congrArg (f : A → B → C) {a1 a2 : A}
    (p : Path a1 a2) (b : B) :
    mapLeft f p b = congrArg (fun x => f x b) p := rfl

/-- `mapLeft` preserves concatenation of paths. -/
@[simp] theorem mapLeft_trans (f : A → B → C)
    {a1 a2 a3 : A} (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    mapLeft f (Path.trans p q) b =
      Path.trans (mapLeft f p b) (mapLeft f q b) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [mapLeft, Path.trans, List.map_append]

/-- `mapLeft` commutes with symmetry. -/
@[simp] theorem mapLeft_symm (f : A → B → C)
    {a1 a2 : A} (p : Path a1 a2) (b : B) :
    mapLeft f (Path.symm p) b =
      Path.symm (mapLeft f p b) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapLeft, Path.symm]

/-- Congruence in the second argument of a binary function. -/
@[simp] def mapRight (f : A → B → C) (a : A) {b1 b2 : B} (p : Path b1 b2) :
    Path (f a b1) (f a b2) :=
  ⟨p.steps.map (Step.map (f a)), _root_.congrArg (f a) p.proof⟩

/-- `mapRight` is the unary congruence for the partial application `f a`. -/
@[simp] theorem mapRight_eq_congrArg (f : A → B → C) (a : A)
    {b1 b2 : B} (p : Path b1 b2) :
    mapRight f a p = congrArg (f a) p := rfl

/-- `mapRight` preserves concatenation of paths. -/
@[simp] theorem mapRight_trans (f : A → B → C)
    (a : A) {b1 b2 b3 : B} (p : Path b1 b2) (q : Path b2 b3) :
    mapRight f a (Path.trans p q) =
      Path.trans (mapRight f a p) (mapRight f a q) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [mapRight, Path.trans, List.map_append]

/-- `mapRight` commutes with symmetry. -/
@[simp] theorem mapRight_symm (f : A → B → C)
    (a : A) {b1 b2 : B} (p : Path b1 b2) :
    mapRight f a (Path.symm p) =
      Path.symm (mapRight f a p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapRight, Path.symm]

/-- Congruence in both arguments of a binary function. -/
@[simp] def map2 (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Path (f a1 b1) (f a2 b2) :=
  Path.trans (mapLeft f p b1) (mapRight f a2 q)

/-- `map2` preserves concatenation of paths in both arguments. -/
@[simp] theorem map2_trans (f : A → B → C)
    {a1 a2 a3 : A} {b1 b2 b3 : B}
    (p1 : Path a1 a2) (p2 : Path a2 a3)
    (q1 : Path b1 b2) (q2 : Path b2 b3) :
    map2 f (Path.trans p1 p2) (Path.trans q1 q2) =
      Path.trans
        (mapLeft f p1 b1)
        (Path.trans
          (mapLeft f p2 b1)
          (Path.trans
            (mapRight f a3 q1)
            (mapRight f a3 q2))) := by
  cases p1 with
  | mk steps1 proof1 =>
      cases p2 with
      | mk steps2 proof2 =>
          cases q1 with
          | mk steps3 proof3 =>
              cases q2 with
              | mk steps4 proof4 =>
                  cases proof1
                  cases proof2
                  cases proof3
                  cases proof4
                  simp [map2, mapLeft, mapRight, Path.trans,
                    List.map_append, List.append_assoc]

/-- `map2` commutes with symmetry. -/
@[simp] theorem map2_symm (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Path.symm (map2 f p q) =
      Path.trans
        (mapRight f a2 (Path.symm q))
        (mapLeft f (Path.symm p) b1) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          have hfun1 :
              Function.comp Step.symm (Step.map (f a1)) =
                Function.comp (Step.map (f a1)) Step.symm := by
            funext s
            exact (Step.map_symm (f := f a1) (s := s)).symm
          have hfun2 :
              Function.comp Step.symm (Step.map fun x => f x b1) =
                Function.comp (Step.map fun x => f x b1) Step.symm := by
            funext s
            exact (Step.map_symm (f := fun x => f x b1) (s := s)).symm
          simp [map2, mapLeft, mapRight, Path.symm, Path.trans,
            List.reverse_append, List.map_append, hfun1, hfun2]

@[simp] theorem mapLeft_refl (f : A → B → C) (a : A) (b : B) :
    mapLeft f (Path.refl a) b = Path.refl (f a b) := by
  simp [mapLeft]

@[simp] theorem mapRight_refl (f : A → B → C) (a : A) (b : B) :
    mapRight f a (Path.refl b) = Path.refl (f a b) := by
  simp [mapRight]

@[simp] theorem map2_refl (f : A → B → C) (a : A) (b : B) :
    map2 f (Path.refl a) (Path.refl b) = Path.refl (f a b) := by
  simp [map2]

@[simp] theorem steps_refl (a : A) : (Path.refl a).steps = [] := rfl

@[simp] theorem steps_ofEq (h : a = b) :
    (Path.ofEq h).steps = [⟨a, b, h⟩] := rfl

theorem refl_ne_ofEq (a : A) :
    Path.refl a ≠ Path.ofEq (rfl : a = a) := by
  intro h
  have : False := by simpa [Path.refl, Path.ofEq] using h
  exact this

section Prod

variable {A : Type u} {B : Type v}
variable {a₁ a₂ : A} {b₁ b₂ : B}

/-- Path on product values built componentwise. -/
@[simp] def prodMk (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (Prod.mk a₁ b₁) (Prod.mk a₂ b₂) :=
  Path.map2 Prod.mk p q

/-- Project a path on pairs to a path on the first component. -/
@[simp] def fst (p : Path (a₁, b₁) (a₂, b₂)) : Path a₁ a₂ :=
  Path.congrArg Prod.fst p

/-- Project a path on pairs to a path on the second component. -/
@[simp] def snd (p : Path (a₁, b₁) (a₂, b₂)) : Path b₁ b₂ :=
  Path.congrArg Prod.snd p

@[simp] theorem prodMk_refl_refl (a : A) (b : B) :
    prodMk (Path.refl a) (Path.refl b) = Path.refl (a, b) := by
  simp [prodMk]

@[simp] theorem toEq_prodMk {A : Type u} {B : Type v}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (A := Prod A B) (a₁, b₁) (a₂, b₂)) :
    (prodMk (fst p) (snd p)).toEq = p.toEq := by
  cases p
  simp [prodMk, fst, snd, map2, mapLeft, mapRight, Path.trans]

end Prod

section Sum

variable {A : Type u} {B : Type v}
variable {a₁ a₂ : A} {b₁ b₂ : B}

/-- Lift a path on the left summand to a path on the coproduct. -/
@[simp] def inlCongr (p : Path a₁ a₂) :
    Path (Sum.inl a₁ : Sum A B) (Sum.inl a₂) :=
  Path.congrArg Sum.inl p

/-- Lift a path on the right summand to a path on the coproduct. -/
@[simp] def inrCongr (p : Path b₁ b₂) :
    Path (Sum.inr b₁ : Sum A B) (Sum.inr b₂) :=
  Path.congrArg Sum.inr p

end Sum

section Function

variable {A : Type u} {B : Type v}
variable {f g h : A → B}

/-- Package pointwise paths into a path between functions. -/
@[simp] def lamCongr (p : ∀ x : A, Path (f x) (g x)) : Path f g :=
  ⟨[], funext (fun x => (p x).proof)⟩

@[simp] def app (p : Path f g) (a : A) : Path (f a) (g a) :=
  Path.congrArg (fun h => h a) p

@[simp] theorem lamCongr_refl (f : A → B) :
    lamCongr (fun x => Path.refl (f x)) = Path.refl f := rfl

@[simp] theorem lamCongr_trans
    (p : ∀ x : A, Path (f x) (g x))
    (q : ∀ x : A, Path (g x) (h x)) :
    Path.trans (lamCongr (f := f) (g := g) p) (lamCongr (f := g) (g := h) q) =
      lamCongr (f := f) (g := h) (fun x => Path.trans (p x) (q x)) := by
  classical
  simp [lamCongr, Path.trans]

@[simp] theorem lamCongr_symm
    (p : ∀ x : A, Path (f x) (g x)) :
    Path.symm (lamCongr (f := f) (g := g) p) =
      lamCongr (f := g) (g := f) (fun x => Path.symm (p x)) := by
  classical
  simp [lamCongr, Path.symm]

@[simp] theorem app_refl (f : A → B) (a : A) :
    app (Path.refl f) a = Path.refl (f a) := by
  simp [app]

@[simp] theorem app_trans (p : Path f g) (q : Path g h) (a : A) :
    app (Path.trans p q) a =
      Path.trans (app p a) (app q a) := by
  simp [app]

@[simp] theorem app_symm (p : Path f g) (a : A) :
    app (Path.symm p) a = Path.symm (app p a) := by
  simp [app]

@[simp] theorem toEq_lam_app {A : Type u} {B : Type v}
    {f g : A → B} (p : Path f g) :
    (lamCongr (fun x => app p x)).toEq = p.toEq := by
  cases p
  simp [lamCongr, app]

end Function

end Path

/-- Uniqueness of identity proofs for computational paths. -/
def UIP (A : Type u) : Prop :=
  ∀ ⦃a b : A⦄, ∀ p q : Path a b, p = q

theorem not_uip_of_inhabited {A : Type u} (a : A) : ¬ UIP A := by
  intro h
  have := h (p := Path.refl a) (q := Path.ofEq (rfl : a = a))
  exact Path.refl_ne_ofEq (A := A) a this

theorem not_uip_of_nonempty {A : Type u} (hA : Nonempty A) : ¬ UIP A := by
  classical
  rcases hA with ⟨a⟩
  exact not_uip_of_inhabited (A := A) a

end ComputationalPaths
