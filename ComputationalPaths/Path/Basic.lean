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
  Step.mk s.tgt s.src s.proof.symm

/-- Map a rewrite step through a function. -/
@[simp] def map (f : A → B) (s : Step A) : Step B :=
  Step.mk (f s.src) (f s.tgt) (_root_.congrArg f s.proof)

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
  Path.mk [] rfl

/-- Path consisting of a single rewrite step. -/
@[simp] def ofEq (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem toEq_ofEq (h : a = b) : toEq (ofEq h) = h := rfl

/-- Compose two paths, concatenating their step lists. -/
@[simp] def trans (p : Path a b) (q : Path b c) : Path a c :=
  Path.mk (p.steps ++ q.steps) (p.proof.trans q.proof)

/-- Reverse a path by reversing and inverting each step. -/
@[simp] def symm (p : Path a b) : Path b a :=
  Path.mk (p.steps.reverse.map Step.symm) p.proof.symm

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
  simp [trans, refl]

@[simp] theorem trans_refl_right (p : Path a b) : trans p (refl b) = p := by
  cases p
  simp [trans, refl]

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
      have hmap :
          List.map Step.symm (List.map Step.symm steps) = steps := by
        induction steps with
        | nil => simp
        | cons s tail ih =>
            cases s
            simp [Step.symm, ih]
      calc
        symm (symm (Path.mk steps rfl))
            = Path.mk ((steps.reverse.map Step.symm).reverse.map Step.symm) rfl := rfl
        _ = Path.mk (List.map Step.symm (List.map Step.symm steps)) rfl := by
              simp
        _ = Path.mk steps rfl := by
              simp [hmap]

@[simp] theorem toEq_trans (p : Path a b) (q : Path b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := rfl

@[simp] theorem toEq_symm (p : Path a b) :
    toEq (symm p) = (toEq p).symm := rfl

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
  Eq.recOn p.proof x

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
    transport (D := fun _ => D) p x = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Substitution along a path, following the paper's notation. -/
def subst {D : A → Sort v} (x : D a) (p : Path a b) : D b :=
  transport p x

@[simp] theorem subst_refl {D : A → Sort v} (x : D a) :
    subst (D := D) x (refl a) = x := rfl

@[simp] theorem subst_trans {D : A → Sort v}
    (x : D a) (p : Path a b) (q : Path b c) :
    subst (D := D) x (trans p q) =
      subst (D := D) (subst (D := D) x p) q :=
  transport_trans (D := D) p q x

@[simp] theorem subst_symm_left {D : A → Sort v}
    (x : D a) (p : Path a b) :
    subst (D := D) (subst (D := D) x p) (symm p) = x :=
  transport_symm_left (D := D) p x

@[simp] theorem subst_symm_right {D : A → Sort v}
    (y : D b) (p : Path a b) :
    subst (D := D) (subst (D := D) y (symm p)) p = y :=
  transport_symm_right (D := D) p y

@[simp] theorem subst_const {D : Type v} (x : D) (p : Path a b) :
    subst (D := fun _ => D) x p = x :=
  transport_const (p := p) (x := x)

@[simp] theorem subst_ofEq {D : A → Sort v} (x : D a) (h : a = b) :
    subst (D := D) x (ofEq h) = Eq.recOn h x := rfl

@[simp] theorem subst_symm_ofEq {D : A → Sort v}
    (y : D b) (h : a = b) :
    subst (D := D) y (symm (ofEq h)) = Eq.recOn h.symm y := rfl

/-- Congruence of unary functions along paths. -/
@[simp] def congrArg (f : A → B) (p : Path a b) :
    Path (f a) (f b) :=
  Path.mk (p.steps.map (Step.map f)) (_root_.congrArg f p.proof)

/-- Unary congruence preserves concatenation. -/
@[simp] theorem congrArg_trans (f : A → B)
    (p : Path a b) (q : Path b c) :
    congrArg f (trans p q) =
      trans (congrArg f p) (congrArg f q) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [congrArg, trans, List.map_append]

/-- Unary congruence commutes with symmetry. -/
@[simp] theorem congrArg_symm (f : A → B)
    (p : Path a b) :
    congrArg f (symm p) =
      symm (congrArg f p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [congrArg, symm]

@[simp] theorem congrArg_id (p : Path a b) :
    congrArg (fun x : A => x) p = p := by
  cases p with
  | mk steps proof =>
      cases proof
      have h := steps_map_id (A := A) steps
      simp [congrArg, h]

/-- Congruence in the first argument of a binary function. -/
@[simp] def mapLeft (f : A → B → C) {a1 a2 : A}
    (p : Path a1 a2) (b : B) :
    Path (f a1 b) (f a2 b) :=
  Path.mk (p.steps.map (Step.map fun x => f x b))
    (_root_.congrArg (fun x => f x b) p.proof)

@[simp] theorem mapLeft_eq_congrArg (f : A → B → C) {a1 a2 : A}
    (p : Path a1 a2) (b : B) :
    mapLeft f p b = congrArg (fun x => f x b) p := rfl

/-- `mapLeft` preserves concatenation of paths. -/
@[simp] theorem mapLeft_trans (f : A → B → C)
    {a1 a2 a3 : A} (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    mapLeft f (trans p q) b =
      trans (mapLeft f p b) (mapLeft f q b) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [mapLeft, trans, List.map_append]

/-- `mapLeft` commutes with symmetry. -/
@[simp] theorem mapLeft_symm (f : A → B → C)
    {a1 a2 : A} (p : Path a1 a2) (b : B) :
    mapLeft f (symm p) b =
      symm (mapLeft f p b) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapLeft, symm]

/-- Congruence in the second argument of a binary function. -/
@[simp] def mapRight (f : A → B → C) (a : A)
    {b1 b2 : B} (p : Path b1 b2) :
    Path (f a b1) (f a b2) :=
  Path.mk (p.steps.map (Step.map (f a))) (_root_.congrArg (f a) p.proof)

@[simp] theorem mapRight_eq_congrArg (f : A → B → C) (a : A)
    {b1 b2 : B} (p : Path b1 b2) :
    mapRight f a p = congrArg (f a) p := rfl

/-- `mapRight` preserves concatenation of paths. -/
@[simp] theorem mapRight_trans (f : A → B → C)
    (a : A) {b1 b2 b3 : B} (p : Path b1 b2) (q : Path b2 b3) :
    mapRight f a (trans p q) =
      trans (mapRight f a p) (mapRight f a q) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [mapRight, trans, List.map_append]

/-- `mapRight` commutes with symmetry. -/
@[simp] theorem mapRight_symm (f : A → B → C)
    (a : A) {b1 b2 : B} (p : Path b1 b2) :
    mapRight f a (symm p) =
      symm (mapRight f a p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [mapRight, symm]

/-- Congruence in both arguments of a binary function. -/
@[simp] def map2 (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Path (f a1 b1) (f a2 b2) :=
  trans (mapLeft f p b1) (mapRight f a2 q)

/-- `map2` preserves concatenation of paths in both arguments. -/
@[simp] theorem map2_trans (f : A → B → C)
    {a1 a2 a3 : A} {b1 b2 b3 : B}
    (p1 : Path a1 a2) (p2 : Path a2 a3)
    (q1 : Path b1 b2) (q2 : Path b2 b3) :
    map2 f (trans p1 p2) (trans q1 q2) =
      trans
        (mapLeft f p1 b1)
        (trans
          (mapLeft f p2 b1)
          (trans
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
                  simp [map2, mapLeft, mapRight, trans,
                    List.map_append, List.append_assoc]

/-- `map2` commutes with symmetry. -/
@[simp] theorem map2_symm (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    symm (map2 f p q) =
      trans
        (mapRight f a2 (symm q))
        (mapLeft f (symm p) b1) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          have h1 :
              Function.comp Step.symm (Step.map (f a1)) =
                Function.comp (Step.map (f a1)) Step.symm := by
            funext s
            exact (Step.map_symm (f := f a1) (s := s)).symm
          have h2 :
              Function.comp Step.symm (Step.map fun x => f x b1) =
                Function.comp (Step.map fun x => f x b1) Step.symm := by
            funext s
            exact (Step.map_symm (f := fun x => f x b1) (s := s)).symm
          simp [map2, mapLeft, mapRight, symm, trans,
            List.reverse_append, List.map_append, List.map_map, h1, h2]

@[simp] theorem mapLeft_refl (f : A → B → C) (a : A) (b : B) :
    mapLeft f (refl a) b = refl (f a b) := by
  simp [mapLeft, refl]

@[simp] theorem mapRight_refl (f : A → B → C) (a : A) (b : B) :
    mapRight f a (refl b) = refl (f a b) := by
  simp [mapRight, refl]

@[simp] theorem map2_refl (f : A → B → C) (a : A) (b : B) :
    map2 f (refl a) (refl b) = refl (f a b) := by
  simp [map2, refl]

@[simp] theorem steps_refl (a : A) : (refl a).steps = [] := rfl

@[simp] theorem steps_ofEq (h : a = b) :
    (ofEq h).steps = [Step.mk a b h] := rfl

theorem refl_ne_ofEq (a : A) :
    refl a ≠ ofEq (rfl : a = a) := by
  intro h
  have := _root_.congrArg Path.steps h
  simp [refl, ofEq] at this

section Prod

variable {A : Type u} {B : Type v}
variable {a1 a2 : A} {b1 b2 : B}

/-- Path on product values built componentwise. -/
@[simp] def prodMk (p : Path a1 a2) (q : Path b1 b2) :
    Path (Prod.mk a1 b1) (Prod.mk a2 b2) :=
  map2 Prod.mk p q

/-- Project a path on pairs to a path on the first component. -/
@[simp] def fst (p : Path (a1, b1) (a2, b2)) : Path a1 a2 :=
  congrArg Prod.fst p

/-- Project a path on pairs to a path on the second component. -/
@[simp] def snd (p : Path (a1, b1) (a2, b2)) : Path b1 b2 :=
  congrArg Prod.snd p

@[simp] theorem prodMk_refl_refl (a : A) (b : B) :
    prodMk (refl a) (refl b) = refl (a, b) := by
  simp [prodMk]

@[simp] theorem toEq_prodMk
    {p : Path (Prod.mk a1 b1) (Prod.mk a2 b2)} :
    (prodMk (fst p) (snd p)).toEq = p.toEq := by
  cases p
  rfl

end Prod

section Sum

variable {A : Type u} {B : Type v}
variable {a1 a2 : A} {b1 b2 : B}

/-- Lift a path on the left summand to a path on the coproduct. -/
@[simp] def inlCongr (p : Path a1 a2) :
    Path (Sum.inl a1 : Sum A B) (Sum.inl a2) :=
  congrArg Sum.inl p

/-- Lift a path on the right summand to a path on the coproduct. -/
@[simp] def inrCongr (p : Path b1 b2) :
    Path (Sum.inr b1 : Sum A B) (Sum.inr b2) :=
  congrArg Sum.inr p

end Sum

section Sigma

variable {A : Type u} {B : A → Type u}
variable {a1 a2 : A}
variable {b1 : B a1} {b2 : B a2}

/-- Build a path between dependent pairs from a base path and a fibre path. -/
@[simp] def sigmaMk (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Path (Sigma.mk a1 b1) (Sigma.mk a2 b2) :=
  Path.ofEq <| by
    classical
    cases p with
    | mk steps1 h1 =>
        cases h1
        cases q with
        | mk steps2 h2 =>
            cases h2
            simp [transport]

/-- Project a path on dependent pairs to the path on the first component. -/
@[simp] def sigmaFst (p : Path (Sigma.mk a1 b1) (Sigma.mk a2 b2)) :
    Path a1 a2 :=
  congrArg Sigma.fst p

/-- Project a path on dependent pairs to a path in the fibre of the second component. -/
@[simp] def sigmaSnd (p : Path (Sigma.mk a1 b1) (Sigma.mk a2 b2)) :
    Path
      (transport (A := A) (D := fun a => B a) (sigmaFst (B := B) p) b1)
      b2 :=
  Path.ofEq <| by
    classical
    cases p with
    | mk steps h =>
        cases h
        simp [transport]

end Sigma

section Dependent

variable {A : Type u} {B : A → Type u}
variable (f : ∀ x : A, B x)
variable {a b : A}

/-- Apply a dependent function to a path, yielding the transported result. -/
@[simp] def apd (p : Path a b) :
    Path (transport (A := A) (D := fun x => B x) p (f a)) (f b) := by
  cases p with
  | mk steps h =>
      cases h
      simpa [transport] using (refl (f a))

@[simp] theorem apd_refl (a : A) :
    apd (f := f) (refl a) = refl (f a) := by
  simp [apd, transport]

end Dependent

section Function

variable {A : Type u} {B : Type v}
variable {f g h : A → B}

/-- Package pointwise paths into a path between functions. -/
@[simp] def lamCongr (p : ∀ x : A, Path (f x) (g x)) : Path f g :=
  Path.mk [] (funext fun x => (p x).proof)

@[simp] def app (p : Path f g) (a : A) : Path (f a) (g a) :=
  congrArg (fun h => h a) p

@[simp] theorem lamCongr_refl (f : A → B) :
    lamCongr (fun x => refl (f x)) = refl f := rfl

@[simp] theorem lamCongr_trans
    (p : ∀ x : A, Path (f x) (g x))
    (q : ∀ x : A, Path (g x) (h x)) :
    trans (lamCongr (f := f) (g := g) p) (lamCongr (f := g) (g := h) q) =
      lamCongr (f := f) (g := h) (fun x => trans (p x) (q x)) := by
  classical
  simp [lamCongr, trans]

@[simp] theorem lamCongr_symm
    (p : ∀ x : A, Path (f x) (g x)) :
    symm (lamCongr (f := f) (g := g) p) =
      lamCongr (f := g) (g := f) (fun x => symm (p x)) := by
  classical
  simp [lamCongr, symm]

@[simp] theorem app_refl (f : A → B) (a : A) :
    app (refl f) a = refl (f a) := by
  simp [app]

@[simp] theorem app_trans (p : Path f g) (q : Path g h) (a : A) :
    app (trans p q) a =
      trans (app p a) (app q a) := by
  simp [app]

@[simp] theorem app_symm (p : Path f g) (a : A) :
    app (symm p) a = symm (app p a) := by
  simp [app]

@[simp] theorem toEq_lam_app {f g : A → B} (p : Path f g) :
    (lamCongr (fun x => app p x)).toEq = p.toEq := by
  cases p
  rfl

end Function

end Path

/-- Uniqueness of identity proofs for computational paths. -/
def UIP (A : Type u) : Prop :=
  ∀ {a b : A}, ∀ (p q : Path a b), p = q

theorem not_uip_of_inhabited {A : Type u} (a : A) : ¬ UIP A := by
  intro h
  have := h (p := Path.refl a) (q := Path.ofEq (rfl : a = a))
  exact Path.refl_ne_ofEq (A := A) a this

theorem not_uip_of_nonempty {A : Type u} (hA : Nonempty A) : ¬ UIP A := by
  classical
  obtain ⟨a⟩ := hA
  exact not_uip_of_inhabited (A := A) a

end ComputationalPaths
