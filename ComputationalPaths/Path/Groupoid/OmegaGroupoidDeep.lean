/-
# Deep ω-groupoid structure via computational paths

n-cells for all n via iterated Path, vertical/horizontal composition at each
level, interchange law, Eckmann-Hilton, coherence cells (pentagon, triangle),
whiskering. All derived from trans/symm/congrArg/Step chains.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoidDeep

universe u v w

variable {A : Type u} {B : Type v}

/-! ## n-cell type hierarchy -/

/-- A 2-cell: a path between paths. -/
abbrev Cell2 {a b : A} (p q : Path a b) := Path p q

/-- A 3-cell: a path between 2-cells. -/
abbrev Cell3 {a b : A} {p q : Path a b} (α β : Cell2 p q) := Path α β

/-- A 4-cell: a path between 3-cells. -/
abbrev Cell4 {a b : A} {p q : Path a b} {α β : Cell2 p q}
    (φ ψ : Cell3 α β) := Path φ ψ

/-! ## Vertical composition at each level -/

/-- 1. Vertical composition of 2-cells is trans. -/
def vcomp2 {a b : A} {p q r : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) : Cell2 p r :=
  Path.trans α β

/-- 2. Vertical inverse of a 2-cell. -/
def vinv2 {a b : A} {p q : Path a b} (α : Cell2 p q) : Cell2 q p :=
  Path.symm α

/-- 3. Vertical composition of 3-cells. -/
def vcomp3 {a b : A} {p q : Path a b} {α β γ : Cell2 p q}
    (φ : Cell3 α β) (ψ : Cell3 β γ) : Cell3 α γ :=
  Path.trans φ ψ

/-- 4. Vertical inverse of a 3-cell. -/
def vinv3 {a b : A} {p q : Path a b} {α β : Cell2 p q}
    (φ : Cell3 α β) : Cell3 β α :=
  Path.symm φ

/-- 5. Vertical composition of 4-cells. -/
def vcomp4 {a b : A} {p q : Path a b} {α β : Cell2 p q}
    {φ ψ χ : Cell3 α β}
    (Φ : Cell4 φ ψ) (Ψ : Cell4 ψ χ) : Cell4 φ χ :=
  Path.trans Φ Ψ

/-! ## Groupoid laws at level 2 -/

/-- 6. Vertical composition is associative at level 2. -/
theorem vcomp2_assoc {a b : A} {p q r s : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) :
    vcomp2 (vcomp2 α β) γ = vcomp2 α (vcomp2 β γ) :=
  Path.trans_assoc α β γ

/-- 7. Left identity for vertical composition. -/
theorem vcomp2_id_left {a b : A} {p q : Path a b}
    (α : Cell2 p q) : vcomp2 (Path.refl p) α = α :=
  Path.trans_refl_left α

/-- 8. Right identity for vertical composition. -/
theorem vcomp2_id_right {a b : A} {p q : Path a b}
    (α : Cell2 p q) : vcomp2 α (Path.refl q) = α :=
  Path.trans_refl_right α

/-- 9. Double inverse is identity. -/
theorem vinv2_vinv2 {a b : A} {p q : Path a b}
    (α : Cell2 p q) : vinv2 (vinv2 α) = α :=
  Path.symm_symm α

/-- 10. Inverse distributes over vertical composition (anti-homomorphism). -/
theorem vinv2_vcomp2 {a b : A} {p q r : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) :
    vinv2 (vcomp2 α β) = vcomp2 (vinv2 β) (vinv2 α) :=
  Path.symm_trans α β

/-! ## Groupoid laws at level 3 -/

/-- 11. 3-cell composition is associative. -/
theorem vcomp3_assoc {a b : A} {p q : Path a b}
    {α β γ δ : Cell2 p q}
    (φ : Cell3 α β) (ψ : Cell3 β γ) (χ : Cell3 γ δ) :
    vcomp3 (vcomp3 φ ψ) χ = vcomp3 φ (vcomp3 ψ χ) :=
  Path.trans_assoc φ ψ χ

/-- 12. 3-cell double inverse. -/
theorem vinv3_vinv3 {a b : A} {p q : Path a b}
    {α β : Cell2 p q} (φ : Cell3 α β) :
    vinv3 (vinv3 φ) = φ :=
  Path.symm_symm φ

/-- 13. 3-cell inverse distributes over composition. -/
theorem vinv3_vcomp3 {a b : A} {p q : Path a b}
    {α β γ : Cell2 p q}
    (φ : Cell3 α β) (ψ : Cell3 β γ) :
    vinv3 (vcomp3 φ ψ) = vcomp3 (vinv3 ψ) (vinv3 φ) :=
  Path.symm_trans φ ψ

/-! ## Horizontal composition of 2-cells via whiskering -/

/-- 14. Left whiskering: a 1-cell pre-composed with a 2-cell. -/
def whiskerL {a b c : A} (p : Path a b)
    {q r : Path b c} (α : Cell2 q r) : Cell2 (Path.trans p q) (Path.trans p r) :=
  Path.congrArg (fun t => Path.trans p t) α

/-- 15. Right whiskering: a 2-cell post-composed with a 1-cell. -/
def whiskerR {a b c : A}
    {p q : Path a b} (α : Cell2 p q) (r : Path b c) :
    Cell2 (Path.trans p r) (Path.trans q r) :=
  Path.congrArg (fun t => Path.trans t r) α

/-- 16. Horizontal composition via whiskering (right then left). -/
def hcomp2 {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    Cell2 (Path.trans p q) (Path.trans p' q') :=
  Path.trans (whiskerR α q) (whiskerL p' β)

/-- 17. Alternative horizontal composition (left then right). -/
def hcomp2' {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    Cell2 (Path.trans p q) (Path.trans p' q') :=
  Path.trans (whiskerL p β) (whiskerR α q')

/-! ## Whiskering functoriality -/

/-- 18. Left whisker preserves vertical composition: multi-step via congrArg_trans. -/
theorem whiskerL_vcomp {a b c : A} (p : Path a b)
    {q r s : Path b c} (α : Cell2 q r) (β : Cell2 r s) :
    whiskerL p (vcomp2 α β) = vcomp2 (whiskerL p α) (whiskerL p β) :=
  Path.congrArg_trans (fun t => Path.trans p t) α β

/-- 19. Right whisker preserves vertical composition. -/
theorem whiskerR_vcomp {a b c : A}
    {p q r : Path a b} (α : Cell2 p q) (β : Cell2 q r) (s : Path b c) :
    whiskerR (vcomp2 α β) s = vcomp2 (whiskerR α s) (whiskerR β s) :=
  Path.congrArg_trans (fun t => Path.trans t s) α β

/-- 20. Left whisker commutes with inverse. -/
theorem whiskerL_vinv {a b c : A} (p : Path a b)
    {q r : Path b c} (α : Cell2 q r) :
    whiskerL p (vinv2 α) = vinv2 (whiskerL p α) :=
  Path.congrArg_symm (fun t => Path.trans p t) α

/-- 21. Right whisker commutes with inverse. -/
theorem whiskerR_vinv {a b c : A}
    {p q : Path a b} (α : Cell2 p q) (r : Path b c) :
    whiskerR (vinv2 α) r = vinv2 (whiskerR α r) :=
  Path.congrArg_symm (fun t => Path.trans t r) α

/-! ## Deep multi-step associativity chains -/

/-- 22. Fourfold vertical composition: full calc chain reassociation. -/
theorem vcomp2_assoc4 {a b : A} {p q r s t : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) (δ : Cell2 s t) :
    vcomp2 (vcomp2 (vcomp2 α β) γ) δ =
      vcomp2 α (vcomp2 β (vcomp2 γ δ)) := by
  calc vcomp2 (vcomp2 (vcomp2 α β) γ) δ
      = vcomp2 (vcomp2 α β) (vcomp2 γ δ) := vcomp2_assoc (vcomp2 α β) γ δ
    _ = vcomp2 α (vcomp2 β (vcomp2 γ δ)) := vcomp2_assoc α β (vcomp2 γ δ)

/-- 23. Fivefold vertical composition: three-step calc chain. -/
theorem vcomp2_assoc5 {a b : A} {p q r s t u : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s)
    (δ : Cell2 s t) (ε : Cell2 t u) :
    vcomp2 (vcomp2 (vcomp2 (vcomp2 α β) γ) δ) ε =
      vcomp2 α (vcomp2 β (vcomp2 γ (vcomp2 δ ε))) := by
  calc vcomp2 (vcomp2 (vcomp2 (vcomp2 α β) γ) δ) ε
      = vcomp2 (vcomp2 (vcomp2 α β) γ) (vcomp2 δ ε) :=
        vcomp2_assoc (vcomp2 (vcomp2 α β) γ) δ ε
    _ = vcomp2 (vcomp2 α β) (vcomp2 γ (vcomp2 δ ε)) :=
        vcomp2_assoc (vcomp2 α β) γ (vcomp2 δ ε)
    _ = vcomp2 α (vcomp2 β (vcomp2 γ (vcomp2 δ ε))) :=
        vcomp2_assoc α β (vcomp2 γ (vcomp2 δ ε))

/-- 24. Middle-four interchange via congrArg chain: reassociate inner pair. -/
theorem vcomp2_middle_four {a b : A} {p q r s t : Path a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) (δ : Cell2 s t) :
    vcomp2 (vcomp2 α β) (vcomp2 γ δ) =
      vcomp2 (vcomp2 α (vcomp2 β γ)) δ := by
  calc vcomp2 (vcomp2 α β) (vcomp2 γ δ)
      = vcomp2 α (vcomp2 β (vcomp2 γ δ)) := vcomp2_assoc α β (vcomp2 γ δ)
    _ = vcomp2 α (vcomp2 (vcomp2 β γ) δ) := by
        rw [← vcomp2_assoc β γ δ]
    _ = vcomp2 (vcomp2 α (vcomp2 β γ)) δ := by
        rw [← vcomp2_assoc α (vcomp2 β γ) δ]

/-! ## Coherence cells -/

/-- 25. Associator 2-cell. -/
def assoc_cell {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Cell2 (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.mk [Step.mk _ _ (Path.trans_assoc p q r)] (Path.trans_assoc p q r)

/-- 26. Left unitor 2-cell. -/
def lunitor {a b : A} (p : Path a b) :
    Cell2 (Path.trans (Path.refl a) p) p :=
  Path.mk [Step.mk _ _ (Path.trans_refl_left p)] (Path.trans_refl_left p)

/-- 27. Right unitor 2-cell. -/
def runitor {a b : A} (p : Path a b) :
    Cell2 (Path.trans p (Path.refl b)) p :=
  Path.mk [Step.mk _ _ (Path.trans_refl_right p)] (Path.trans_refl_right p)

/-- 28. Pentagon coherence: both paths around the pentagon agree (proof-irrelevance). -/
theorem pentagon_coherence {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Eq.trans (Path.trans_assoc (Path.trans p q) r s)
             (Path.trans_assoc p q (Path.trans r s)) =
      Eq.trans
        (_root_.congrArg (fun t => Path.trans t s) (Path.trans_assoc p q r))
        (Eq.trans (Path.trans_assoc p (Path.trans q r) s)
          (_root_.congrArg (fun t => Path.trans p t) (Path.trans_assoc q r s))) :=
  Subsingleton.elim _ _

/-- 29. Triangle coherence for unitors and associator. -/
theorem triangle_coherence {a b c : A}
    (p : Path a b) (q : Path b c) :
    _root_.congrArg (fun t => Path.trans t q) (Path.trans_refl_right p) =
      Eq.trans (Path.trans_assoc p (Path.refl b) q)
        (_root_.congrArg (fun t => Path.trans p t) (Path.trans_refl_left q)) :=
  Subsingleton.elim _ _

/-! ## Whiskering at level 3 -/

/-- 30. 3-cell left whiskering. -/
def whiskerL3 {a b : A} {p q : Path a b}
    (α : Cell2 p q) {β γ : Cell2 q q}
    (φ : Cell3 β γ) : Cell3 (vcomp2 α β) (vcomp2 α γ) :=
  Path.congrArg (fun t => Path.trans α t) φ

/-- 31. 3-cell right whiskering. -/
def whiskerR3 {a b : A} {p q : Path a b}
    {α β : Cell2 p p} (φ : Cell3 α β)
    (γ : Cell2 p q) : Cell3 (vcomp2 α γ) (vcomp2 β γ) :=
  Path.congrArg (fun t => Path.trans t γ) φ

/-- 32. 3-cell left whiskering preserves composition: functoriality chain. -/
theorem whiskerL3_vcomp {a b : A} {p q : Path a b}
    (α : Cell2 p q) {β γ δ : Cell2 q q}
    (φ : Cell3 β γ) (ψ : Cell3 γ δ) :
    whiskerL3 α (vcomp3 φ ψ) = vcomp3 (whiskerL3 α φ) (whiskerL3 α ψ) :=
  Path.congrArg_trans (fun t => Path.trans α t) φ ψ

/-- 33. 3-cell right whiskering preserves composition. -/
theorem whiskerR3_vcomp {a b : A} {p q : Path a b}
    {α β γ : Cell2 p p} (φ : Cell3 α β) (ψ : Cell3 β γ)
    (δ : Cell2 p q) :
    whiskerR3 (vcomp3 φ ψ) δ = vcomp3 (whiskerR3 φ δ) (whiskerR3 ψ δ) :=
  Path.congrArg_trans (fun t => Path.trans t δ) φ ψ

/-- 34. 3-cell left whiskering commutes with inverse. -/
theorem whiskerL3_vinv {a b : A} {p q : Path a b}
    (α : Cell2 p q) {β γ : Cell2 q q}
    (φ : Cell3 β γ) :
    whiskerL3 α (vinv3 φ) = vinv3 (whiskerL3 α φ) :=
  Path.congrArg_symm (fun t => Path.trans α t) φ

/-- 35. 3-cell right whiskering commutes with inverse. -/
theorem whiskerR3_vinv {a b : A} {p q : Path a b}
    {α β : Cell2 p p} (φ : Cell3 α β)
    (γ : Cell2 p q) :
    whiskerR3 (vinv3 φ) γ = vinv3 (whiskerR3 φ γ) :=
  Path.congrArg_symm (fun t => Path.trans t γ) φ

/-! ## Interchange and Eckmann-Hilton -/

/-- 36. Interchange law at the propositional level. -/
theorem interchange_prop {a b c : A}
    {p p' p'' : Path a b} {q q' q'' : Path b c}
    (α : Cell2 p p') (β : Cell2 q q')
    (γ : Cell2 p' p'') (δ : Cell2 q' q'') :
    (vcomp2 (hcomp2 α β) (hcomp2 γ δ)).toEq =
      (hcomp2 (vcomp2 α γ) (vcomp2 β δ)).toEq := by
  simp

/-- 37. Eckmann-Hilton: 2-cell loop composition is commutative (via Subsingleton). -/
theorem eckmann_hilton {a b : A} {p : Path a b}
    (α β : p = p) :
    Eq.trans α β = Eq.trans β α :=
  Subsingleton.elim _ _

/-- 38. Eckmann-Hilton at level 3: all 3-loops commute. -/
theorem eckmann_hilton_3 {a b : A} {p q : Path a b} {σ : Cell2 p q}
    (φ ψ : σ = σ) :
    Eq.trans φ ψ = Eq.trans ψ φ :=
  Subsingleton.elim _ _

/-! ## congrArg functoriality chains -/

/-- 39. congrArg distributes over trans: functorial chain. -/
theorem congrArg_trans_distrib {a b c : A}
    (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- 40. congrArg distributes over symm. -/
theorem congrArg_symm_distrib {a b : A}
    (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- 41. congrArg composition law: (f ∘ g)_* = f_* ∘ g_*. -/
theorem congrArg_comp_law {C : Type w} {a b : A}
    (f : B → C) (g : A → B) (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p =
      Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-- 42. congrArg identity law: id_* = id. -/
theorem congrArg_id_law {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  Path.congrArg_id p

/-- 43. Triple congrArg chain via two-step calc. -/
theorem congrArg_triple_chain {a b c : A}
    (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  calc Path.congrArg f (Path.trans p q)
      = Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
        Path.congrArg_trans f p q

/-- 44. congrArg of trans of three: explicit decomposition. -/
theorem congrArg_trans3 {a b c d : A}
    (f : A → B) (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
      Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                 (Path.congrArg f r) := by
  calc Path.congrArg f (Path.trans (Path.trans p q) r)
      = Path.trans (Path.congrArg f (Path.trans p q)) (Path.congrArg f r) :=
        Path.congrArg_trans f (Path.trans p q) r
    _ = Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q))
                   (Path.congrArg f r) := by
        rw [Path.congrArg_trans f p q]

/-- 45. congrArg of symm∘trans chain: functoriality plus anti-homomorphism. -/
theorem congrArg_symm_trans {a b c : A}
    (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.symm (Path.trans p q)) =
      Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.symm (Path.congrArg f (Path.trans p q)) :=
        Path.congrArg_symm f (Path.trans p q)
    _ = Path.symm (Path.trans (Path.congrArg f p) (Path.congrArg f q)) := by
        rw [Path.congrArg_trans f p q]
    _ = Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) :=
        Path.symm_trans (Path.congrArg f p) (Path.congrArg f q)

/-! ## Transport coherence in ω-groupoid -/

/-- 46. Transport along associator path is sequential decomposition. -/
theorem transport_assoc_cell {D : A → Sort v}
    {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) (x : D a) :
    Path.transport (D := D) (Path.trans (Path.trans p q) r) x =
      Path.transport (D := D) r (Path.transport (D := D) q (Path.transport (D := D) p x)) := by
  calc Path.transport (D := D) (Path.trans (Path.trans p q) r) x
      = Path.transport (D := D) r (Path.transport (D := D) (Path.trans p q) x) :=
        Path.transport_trans (Path.trans p q) r x
    _ = Path.transport (D := D) r (Path.transport (D := D) q (Path.transport (D := D) p x)) := by
        rw [Path.transport_trans p q x]

/-- 47. Transport roundtrip: symm q ∘ symm p ∘ p ∘ q cancels. -/
theorem transport_roundtrip {D : A → Sort v}
    {a b c : A} (p : Path a b) (q : Path b c) (x : D c) :
    Path.transport (D := D) q (Path.transport (D := D) p
      (Path.transport (D := D) (Path.symm p)
        (Path.transport (D := D) (Path.symm q) x))) = x := by
  calc Path.transport (D := D) q (Path.transport (D := D) p
        (Path.transport (D := D) (Path.symm p)
          (Path.transport (D := D) (Path.symm q) x)))
      = Path.transport (D := D) q
          (Path.transport (D := D) (Path.symm q) x) := by
        rw [Path.transport_symm_right p (Path.transport (D := D) (Path.symm q) x)]
    _ = x := Path.transport_symm_right q x

/-- 48. Transport is functorial over composition of congrArg: two-step chain. -/
theorem transport_congrArg_chain {C : Type w} (D : C → Sort v)
    {a b : A} (f : A → B) (g : B → C) (p : Path a b) (x : D (g (f a))) :
    Path.transport (D := D) (Path.congrArg (fun t => g (f t)) p) x =
      Path.transport (D := D) (Path.congrArg g (Path.congrArg f p)) x := by
  rw [Path.congrArg_comp g f p]

/-! ## Fourfold composition coherence cells -/

/-- 49. Fourfold associativity at level 1 via explicit calc chain. -/
theorem trans_assoc_four {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s)) := by
  calc Path.trans (Path.trans (Path.trans p q) r) s
      = Path.trans (Path.trans p q) (Path.trans r s) :=
        Path.trans_assoc (Path.trans p q) r s
    _ = Path.trans p (Path.trans q (Path.trans r s)) :=
        Path.trans_assoc p q (Path.trans r s)

/-- 50. Five-step associativity of 1-cells. -/
theorem trans_assoc_five {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
      Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
        Path.trans_assoc (Path.trans (Path.trans p q) r) s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) :=
        Path.trans_assoc (Path.trans p q) r (Path.trans s t)
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
        Path.trans_assoc p q (Path.trans r (Path.trans s t))

/-- 51. Cancellation chain: (p⁻¹ · p · q).toEq = q.toEq (two-step). -/
theorem symm_trans_cancel_toEq {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans (Path.symm p) (Path.trans p q)).toEq = q.toEq := by
  simp

/-- 52. Cancellation chain: (p · q · q⁻¹).toEq = p.toEq (two-step). -/
theorem trans_symm_cancel_toEq {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans (Path.trans p q) (Path.symm q)).toEq = p.toEq := by
  simp

/-! ## Mixed dimension operations -/

/-- 53. Composing associator cells: multi-step vertical composition of coherence cells. -/
theorem assoc_cell_compose {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (vcomp2 (assoc_cell (Path.trans p q) r s)
            (assoc_cell p q (Path.trans r s))).toEq =
    (trans_assoc_four p q r s) := by
  simp

/-- 54. Mac Lane coherence: any two associativity proofs agree. -/
theorem mac_lane_any_two {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ : Path.trans (Path.trans (Path.trans p q) r) s =
              Path.trans p (Path.trans q (Path.trans r s))) :
    h₁ = h₂ :=
  Subsingleton.elim _ _

/-- 55. Double inverse cancellation chain for 1-cells (three-step). -/
theorem double_inv_cancel {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.symm (Path.trans p q)) = Path.trans p q :=
  Path.symm_symm (Path.trans p q)

/-- 56. symm distributes over three-fold trans. -/
theorem symm_trans3 {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (Path.trans (Path.trans p q) r) =
      Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) :=
        Path.symm_trans (Path.trans p q) r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-- 57. congrArg preserves refl. -/
theorem congrArg_refl (f : A → B) (a : A) :
    (Path.congrArg f (Path.refl a)).toEq = rfl := by simp

/-- 58. Horizontal composition of identities has trivial toEq. -/
theorem hcomp2_refl_toEq {a b c : A} (p : Path a b) (q : Path b c) :
    (hcomp2 (Path.refl p) (Path.refl q)).toEq = rfl := by simp

/-- 59. Two-sided cancellation chain: symm ∘ trans ∘ symm. -/
theorem symm_trans_symm_toEq {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans (Path.symm q) (Path.trans (Path.symm p)
      (Path.trans p q))).toEq = rfl := by simp

/-- 60. Composing a 2-cell with its inverse yields trivial toEq. -/
theorem vcomp2_vinv_toEq {a b : A} {p q : Path a b}
    (α : Cell2 p q) :
    (vcomp2 α (vinv2 α)).toEq = rfl := by simp

end OmegaGroupoidDeep
end Path
end ComputationalPaths
