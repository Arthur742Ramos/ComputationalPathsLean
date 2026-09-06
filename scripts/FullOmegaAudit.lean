import ComputationalPaths.Path.OmegaGroupoid.GlobularPasting

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaFoundations

/-! Incremental audit. This checks the foundations only; it is not yet a
completion gate for the full weak omega-groupoid theorem. -/

example (G : GlobularSet) (n k : Nat) (c : G.Cell (n + (k + 2))) :
    G.sourceIter (k + 1) (G.source c) = G.sourceIter (k + 1) (G.target c) :=
  G.sourceIter_globular k c

example (G : GlobularSet) {n : Nat} (p q : G.Cell (n + 1))
    (h : G.target p = G.source q) :
    GlobularSet.Parallel G n (G.source p) (G.target q) :=
  (G.compositeBoundary p q h).parallel

example (G : GlobularSet) : GlobularSet.Contraction (GlobularSet.Map.id G) :=
  GlobularSet.Contraction.identity G

noncomputable example {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  (associatorCell p q r).2.2.2.2

#print axioms GlobularSet.sourceIter_globular
#print axioms GlobularSet.targetIter_globular
#print axioms GlobularSet.compositeBoundary
#print axioms GlobularSet.Contraction.comp
#print axioms associatorCell

example (G : GlobularSet) (n : Nat) (c : Pasting n G) :
    Pasting.source (Pasting.identity c) = c := Pasting.source_identity G c

example (G : GlobularSet) (c : Pasting 7 G) :
    Pasting.target (Pasting.identity c) = c := Pasting.target_identity G c

#print axioms GlobularSet.hom
#print axioms GlobularSet.Map.hom
#print axioms Pasting.globular
#print axioms Pasting.identities

example {G H K : GlobularSet} (f : GlobularSet.Map G H) (g : GlobularSet.Map H K)
    (n : Nat) (c : Pasting n G) :
    Pasting.map g (Pasting.map f c) = Pasting.map (GlobularSet.Map.comp g f) c :=
  Pasting.map_comp f g c

#print axioms Pasting.pastingFunctor

example {O : Type} {E F D : O → O → Type}
    (f : {a b : O} → E a b → Chain F a b)
    (g : {a b : O} → F a b → Chain D a b) {a b : O} (p : Chain E a b) :
    (p.bind f).bind g = p.bind (fun e => (f e).bind g) := Chain.bind_assoc f g p

#print axioms Chain.bind_assoc
#print axioms evalPathChain_bind

example (G : GlobularSet) (n : Nat) (c d : G.Cell n)
    (h : Pasting.singleton c = Pasting.singleton d) : c = d :=
  Pasting.singleton_injective G h

example (G : GlobularSet) (c : G.Cell 8) :
    Pasting.source (Pasting.singleton c) = Pasting.singleton (G.source c) :=
  Pasting.source_singleton G c

example {G H : GlobularSet} (f : GlobularSet.Map G H) (n : Nat) (c : G.Cell n) :
    Pasting.map f (Pasting.singleton c) = Pasting.singleton (f.app c) :=
  Pasting.map_singleton f c

#print axioms Pasting.singleton_injective
#print axioms Pasting.singletonGlobular
#print axioms Pasting.singleton_natural

example {G : GlobularSet} (n : Nat) {a b c d : G.Cell 0}
    (p : Pasting.Horizontal n G a b) (q : Pasting.Horizontal n G b c)
    (r : Pasting.Horizontal n G c d) :
    Pasting.horizontal (Pasting.horizontal p q) r =
      Pasting.horizontal p (Pasting.horizontal q r) := Pasting.horizontal_assoc p q r

example {G : GlobularSet} {a b c : G.Cell 0}
    (p : Pasting.Horizontal 8 G a b) (q : Pasting.Horizontal 8 G b c) :
    (Pasting.globular G).sourceZero (n := 9) (Pasting.pack (Pasting.horizontal p q)) = a :=
  Pasting.sourceZero_pack _

#print axioms Pasting.horizontal_assoc
#print axioms Pasting.source_horizontal
#print axioms Pasting.target_horizontal
#print axioms Pasting.identity_horizontal
#print axioms Pasting.map_horizontal
#print axioms Pasting.sourceZero_pack
