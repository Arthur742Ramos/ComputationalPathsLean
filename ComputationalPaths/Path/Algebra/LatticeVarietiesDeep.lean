import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LatticeVarietiesDeep

open ComputationalPaths.Path

universe u v w x

structure LatticeSignature where
  Carrier : Type u
  meet : Carrier → Carrier → Carrier
  join : Carrier → Carrier → Carrier
  bot : Carrier
  top : Carrier

structure LatticeAxioms (L : LatticeSignature) where
  meet_comm : ∀ a b : L.Carrier, Path (L.meet a b) (L.meet b a)
  join_comm : ∀ a b : L.Carrier, Path (L.join a b) (L.join b a)
  meet_assoc :
    ∀ a b c : L.Carrier, Path (L.meet (L.meet a b) c) (L.meet a (L.meet b c))
  join_assoc :
    ∀ a b c : L.Carrier, Path (L.join (L.join a b) c) (L.join a (L.join b c))
  meet_idem : ∀ a : L.Carrier, Path (L.meet a a) a
  join_idem : ∀ a : L.Carrier, Path (L.join a a) a
  absorb_meet_join :
    ∀ a b : L.Carrier, Path (L.meet a (L.join a b)) a
  absorb_join_meet :
    ∀ a b : L.Carrier, Path (L.join a (L.meet a b)) a

structure DistributiveAxioms (L : LatticeSignature) where
  meet_over_join :
    ∀ a b c : L.Carrier,
      Path (L.meet a (L.join b c)) (L.join (L.meet a b) (L.meet a c))
  join_over_meet :
    ∀ a b c : L.Carrier,
      Path (L.join a (L.meet b c)) (L.meet (L.join a b) (L.join a c))

structure ModularAxioms (L : LatticeSignature) where
  modular_identity :
    ∀ a b c : L.Carrier,
      Path (L.join a (L.meet b c)) (L.meet (L.join a b) c)

structure ComplementedAxioms (L : LatticeSignature) where
  comp : L.Carrier → L.Carrier
  meet_compl : ∀ a : L.Carrier, Path (L.meet a (comp a)) L.bot
  join_compl : ∀ a : L.Carrier, Path (L.join a (comp a)) L.top

structure WhitmanAxioms (L : LatticeSignature) where
  whitman :
    ∀ a b c d : L.Carrier,
      Path (L.meet (L.join a b) (L.join c d))
        (L.join (L.meet (L.join a b) c) (L.meet (L.join a b) d))

private noncomputable def pathOfEq {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

section LatticeDerived

variable {L : LatticeSignature}
variable (Lat : LatticeAxioms L)
variable {a b c d : L.Carrier}

noncomputable def meet_comm_path (a b : L.Carrier) :
    Nonempty (Path (L.meet a b) (L.meet b a)) :=
  ⟨Lat.meet_comm a b⟩

noncomputable def join_comm_path (a b : L.Carrier) :
    Nonempty (Path (L.join a b) (L.join b a)) :=
  ⟨Lat.join_comm a b⟩

noncomputable def meet_assoc_path (a b c : L.Carrier) :
    Nonempty (Path (L.meet (L.meet a b) c) (L.meet a (L.meet b c))) :=
  ⟨Lat.meet_assoc a b c⟩

noncomputable def join_assoc_path (a b c : L.Carrier) :
    Nonempty (Path (L.join (L.join a b) c) (L.join a (L.join b c))) :=
  ⟨Lat.join_assoc a b c⟩

noncomputable def meet_idem_path (a : L.Carrier) :
    Nonempty (Path (L.meet a a) a) :=
  ⟨Lat.meet_idem a⟩

noncomputable def join_idem_path (a : L.Carrier) :
    Nonempty (Path (L.join a a) a) :=
  ⟨Lat.join_idem a⟩

noncomputable def absorb_meet_join_path (a b : L.Carrier) :
    Nonempty (Path (L.meet a (L.join a b)) a) :=
  ⟨Lat.absorb_meet_join a b⟩

noncomputable def absorb_join_meet_path (a b : L.Carrier) :
    Nonempty (Path (L.join a (L.meet a b)) a) :=
  ⟨Lat.absorb_join_meet a b⟩

noncomputable def meet_comm_symm (a b : L.Carrier) :
    Nonempty (Path (L.meet b a) (L.meet a b)) :=
  ⟨Path.symm (Lat.meet_comm a b)⟩

noncomputable def join_comm_symm (a b : L.Carrier) :
    Nonempty (Path (L.join b a) (L.join a b)) :=
  ⟨Path.symm (Lat.join_comm a b)⟩

noncomputable def meet_assoc_symm (a b c : L.Carrier) :
    Nonempty (Path (L.meet a (L.meet b c)) (L.meet (L.meet a b) c)) :=
  ⟨Path.symm (Lat.meet_assoc a b c)⟩

noncomputable def join_assoc_symm (a b c : L.Carrier) :
    Nonempty (Path (L.join a (L.join b c)) (L.join (L.join a b) c)) :=
  ⟨Path.symm (Lat.join_assoc a b c)⟩

noncomputable def meet_idem_symm (a : L.Carrier) :
    Nonempty (Path a (L.meet a a)) :=
  ⟨Path.symm (Lat.meet_idem a)⟩

noncomputable def join_idem_symm (a : L.Carrier) :
    Nonempty (Path a (L.join a a)) :=
  ⟨Path.symm (Lat.join_idem a)⟩

noncomputable def absorb_meet_join_symm (a b : L.Carrier) :
    Nonempty (Path a (L.meet a (L.join a b))) :=
  ⟨Path.symm (Lat.absorb_meet_join a b)⟩

noncomputable def absorb_join_meet_symm (a b : L.Carrier) :
    Nonempty (Path a (L.join a (L.meet a b))) :=
  ⟨Path.symm (Lat.absorb_join_meet a b)⟩

theorem meet_comm_roundtrip_toEq (a b : L.Carrier) :
    (Path.trans (Lat.meet_comm a b) (Path.symm (Lat.meet_comm a b))).toEq = rfl := by
  simp

theorem join_comm_roundtrip_toEq (a b : L.Carrier) :
    (Path.trans (Lat.join_comm a b) (Path.symm (Lat.join_comm a b))).toEq = rfl := by
  simp

noncomputable def meet_left_congr (p : Path a b) :
    Nonempty (Path (L.meet a c) (L.meet b c)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet x c) p⟩

noncomputable def meet_right_congr (p : Path c d) :
    Nonempty (Path (L.meet a c) (L.meet a d)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet a x) p⟩

noncomputable def join_left_congr (p : Path a b) :
    Nonempty (Path (L.join a c) (L.join b c)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join x c) p⟩

noncomputable def join_right_congr (p : Path c d) :
    Nonempty (Path (L.join a c) (L.join a d)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join a x) p⟩

noncomputable def meet_bimap_congr (p : Path a b) (q : Path c d) :
    Nonempty (Path (L.meet a c) (L.meet b d)) := by
  have hp : a = b := p.toEq
  have hq : c = d := q.toEq
  refine ⟨pathOfEq ?_⟩
  simpa [hp, hq]

noncomputable def join_bimap_congr (p : Path a b) (q : Path c d) :
    Nonempty (Path (L.join a c) (L.join b d)) := by
  have hp : a = b := p.toEq
  have hq : c = d := q.toEq
  refine ⟨pathOfEq ?_⟩
  simpa [hp, hq]

noncomputable def absorb_meet_join_swapped (a b : L.Carrier) :
    Nonempty (Path (L.meet (L.join a b) a) a) := by
  exact ⟨Path.trans (Lat.meet_comm (L.join a b) a) (Lat.absorb_meet_join a b)⟩

noncomputable def absorb_join_meet_swapped (a b : L.Carrier) :
    Nonempty (Path (L.join (L.meet a b) a) a) := by
  exact ⟨Path.trans (Lat.join_comm (L.meet a b) a) (Lat.absorb_join_meet a b)⟩

noncomputable def meet_idem_from_absorb (a : L.Carrier) :
    Nonempty (Path (L.meet a a) a) := by
  refine ⟨Path.trans ?_ (Lat.absorb_meet_join a a)⟩
  simpa using Path.congrArg (fun x => L.meet a x) (Path.symm (Lat.join_idem a))

noncomputable def join_idem_from_absorb (a : L.Carrier) :
    Nonempty (Path (L.join a a) a) := by
  refine ⟨Path.trans ?_ (Lat.absorb_join_meet a a)⟩
  simpa using Path.congrArg (fun x => L.join a x) (Path.symm (Lat.meet_idem a))

noncomputable def meet_assoc_congr_left (p : Path a b) :
    Nonempty (Path (L.meet (L.meet a c) d) (L.meet (L.meet b c) d)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet (L.meet x c) d) p⟩

noncomputable def meet_assoc_congr_right (p : Path c d) :
    Nonempty (Path (L.meet a (L.meet b c)) (L.meet a (L.meet b d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet a (L.meet b x)) p⟩

noncomputable def join_assoc_congr_left (p : Path a b) :
    Nonempty (Path (L.join (L.join a c) d) (L.join (L.join b c) d)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join (L.join x c) d) p⟩

noncomputable def join_assoc_congr_right (p : Path c d) :
    Nonempty (Path (L.join a (L.join b c)) (L.join a (L.join b d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join a (L.join b x)) p⟩

noncomputable def absorb_meet_join_right_congr (p : Path b c) :
    Nonempty (Path (L.meet a (L.join a b)) (L.meet a (L.join a c))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet a (L.join a x)) p⟩

noncomputable def absorb_join_meet_right_congr (p : Path b c) :
    Nonempty (Path (L.join a (L.meet a b)) (L.join a (L.meet a c))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join a (L.meet a x)) p⟩

end LatticeDerived

section DistributiveDerived

variable {L : LatticeSignature}
variable (Dist : DistributiveAxioms L) (Lat : LatticeAxioms L)
variable {a b c d : L.Carrier}

noncomputable def meet_over_join_path (a b c : L.Carrier) :
    Nonempty (Path (L.meet a (L.join b c)) (L.join (L.meet a b) (L.meet a c))) :=
  ⟨Dist.meet_over_join a b c⟩

noncomputable def join_over_meet_path (a b c : L.Carrier) :
    Nonempty (Path (L.join a (L.meet b c)) (L.meet (L.join a b) (L.join a c))) :=
  ⟨Dist.join_over_meet a b c⟩

noncomputable def meet_over_join_symm (a b c : L.Carrier) :
    Nonempty (Path (L.join (L.meet a b) (L.meet a c)) (L.meet a (L.join b c))) :=
  ⟨Path.symm (Dist.meet_over_join a b c)⟩

noncomputable def join_over_meet_symm (a b c : L.Carrier) :
    Nonempty (Path (L.meet (L.join a b) (L.join a c)) (L.join a (L.meet b c))) :=
  ⟨Path.symm (Dist.join_over_meet a b c)⟩

theorem meet_over_join_roundtrip_toEq (a b c : L.Carrier) :
    (Path.trans (Dist.meet_over_join a b c) (Path.symm (Dist.meet_over_join a b c))).toEq = rfl := by
  simp

theorem join_over_meet_roundtrip_toEq (a b c : L.Carrier) :
    (Path.trans (Dist.join_over_meet a b c) (Path.symm (Dist.join_over_meet a b c))).toEq = rfl := by
  simp

noncomputable def meet_over_join_congr_left (p : Path a b) :
    Nonempty (Path (L.meet a (L.join c d)) (L.meet b (L.join c d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet x (L.join c d)) p⟩

noncomputable def join_over_meet_congr_left (p : Path a b) :
    Nonempty (Path (L.join a (L.meet c d)) (L.join b (L.meet c d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join x (L.meet c d)) p⟩

noncomputable def meet_over_join_with_comm (a b c : L.Carrier) :
    Nonempty (Path (L.meet a (L.join b c)) (L.join (L.meet a c) (L.meet a b))) := by
  exact ⟨Path.trans (Dist.meet_over_join a b c) (Lat.join_comm (L.meet a b) (L.meet a c))⟩

noncomputable def join_over_meet_with_comm (a b c : L.Carrier) :
    Nonempty (Path (L.join a (L.meet b c)) (L.meet (L.join a c) (L.join a b))) := by
  exact ⟨Path.trans (Dist.join_over_meet a b c) (Lat.meet_comm (L.join a b) (L.join a c))⟩

noncomputable def meet_over_join_right_congr (p : Path c d) :
    Nonempty (Path (L.join (L.meet a b) (L.meet a c)) (L.join (L.meet a b) (L.meet a d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join (L.meet a b) (L.meet a x)) p⟩

noncomputable def join_over_meet_right_congr (p : Path c d) :
    Nonempty (Path (L.meet (L.join a b) (L.join a c)) (L.meet (L.join a b) (L.join a d))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet (L.join a b) (L.join a x)) p⟩

end DistributiveDerived

section ModularComplementedDerived

variable {L : LatticeSignature}
variable (ModAx : ModularAxioms L) (Lat : LatticeAxioms L)
variable (Cmp : ComplementedAxioms L)
variable {a b c : L.Carrier}

noncomputable def modular_identity_path (a b c : L.Carrier) :
    Nonempty (Path (L.join a (L.meet b c)) (L.meet (L.join a b) c)) :=
  ⟨ModAx.modular_identity a b c⟩

noncomputable def modular_identity_symm (a b c : L.Carrier) :
    Nonempty (Path (L.meet (L.join a b) c) (L.join a (L.meet b c))) :=
  ⟨Path.symm (ModAx.modular_identity a b c)⟩

theorem modular_roundtrip_toEq (a b c : L.Carrier) :
    (Path.trans (ModAx.modular_identity a b c) (Path.symm (ModAx.modular_identity a b c))).toEq = rfl := by
  simp

theorem modular_congr_left (p : Path a b) :
    Nonempty (Path (L.join a (L.meet c c)) (L.join b (L.meet c c))) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.join x (L.meet c c)) p⟩

theorem modular_congr_right (p : Path b c) :
    Nonempty (Path (L.meet (L.join a b) c) (L.meet (L.join a c) c)) := by
  exact ⟨by simpa using Path.congrArg (fun x => L.meet (L.join a x) c) p⟩

theorem meet_compl_path (a : L.Carrier) :
    Nonempty (Path (L.meet a (Cmp.comp a)) L.bot) :=
  ⟨Cmp.meet_compl a⟩

theorem join_compl_path (a : L.Carrier) :
    Nonempty (Path (L.join a (Cmp.comp a)) L.top) :=
  ⟨Cmp.join_compl a⟩

theorem meet_compl_symm (a : L.Carrier) :
    Nonempty (Path L.bot (L.meet a (Cmp.comp a))) :=
  ⟨Path.symm (Cmp.meet_compl a)⟩

theorem join_compl_symm (a : L.Carrier) :
    Nonempty (Path L.top (L.join a (Cmp.comp a))) :=
  ⟨Path.symm (Cmp.join_compl a)⟩

noncomputable def meet_compl_commuted (a : L.Carrier) :
    Nonempty (Path (L.meet (Cmp.comp a) a) L.bot) := by
  exact ⟨Path.trans (Lat.meet_comm (Cmp.comp a) a) (Cmp.meet_compl a)⟩

noncomputable def join_compl_commuted (a : L.Carrier) :
    Nonempty (Path (L.join (Cmp.comp a) a) L.top) := by
  exact ⟨Path.trans (Lat.join_comm (Cmp.comp a) a) (Cmp.join_compl a)⟩

theorem meet_compl_roundtrip_toEq (a : L.Carrier) :
    (Path.trans (Cmp.meet_compl a) (Path.symm (Cmp.meet_compl a))).toEq = rfl := by
  simp

theorem join_compl_roundtrip_toEq (a : L.Carrier) :
    (Path.trans (Cmp.join_compl a) (Path.symm (Cmp.join_compl a))).toEq = rfl := by
  simp

end ModularComplementedDerived

structure LatticeHom (L : LatticeSignature.{u}) (M : LatticeSignature.{v}) where
  toFun : L.Carrier → M.Carrier
  map_meet :
    ∀ a b : L.Carrier,
      Path (toFun (L.meet a b)) (M.meet (toFun a) (toFun b))
  map_join :
    ∀ a b : L.Carrier,
      Path (toFun (L.join a b)) (M.join (toFun a) (toFun b))
  map_bot : Path (toFun L.bot) M.bot
  map_top : Path (toFun L.top) M.top

namespace LatticeHom

variable {L : LatticeSignature.{u}}
variable {M : LatticeSignature.{v}}
variable {N : LatticeSignature.{w}}

noncomputable def idHom (L : LatticeSignature.{u}) : LatticeHom L L where
  toFun := fun x => x
  map_meet := by
    intro a b
    exact Path.refl (L.meet a b)
  map_join := by
    intro a b
    exact Path.refl (L.join a b)
  map_bot := Path.refl L.bot
  map_top := Path.refl L.top

noncomputable def comp (g : LatticeHom M N) (f : LatticeHom L M) : LatticeHom L N where
  toFun := fun x => g.toFun (f.toFun x)
  map_meet := by
    intro a b
    exact Path.trans
      (Path.congrArg g.toFun (f.map_meet a b))
      (g.map_meet (f.toFun a) (f.toFun b))
  map_join := by
    intro a b
    exact Path.trans
      (Path.congrArg g.toFun (f.map_join a b))
      (g.map_join (f.toFun a) (f.toFun b))
  map_bot := by
    exact Path.trans
      (Path.congrArg g.toFun f.map_bot)
      g.map_bot
  map_top := by
    exact Path.trans
      (Path.congrArg g.toFun f.map_top)
      g.map_top

theorem id_apply (L : LatticeSignature.{u}) (x : L.Carrier) :
    (idHom L).toFun x = x :=
  rfl

theorem comp_apply (g : LatticeHom M N) (f : LatticeHom L M) (x : L.Carrier) :
    (comp g f).toFun x = g.toFun (f.toFun x) :=
  rfl

theorem id_map_meet (L : LatticeSignature.{u}) (a b : L.Carrier) :
    Nonempty (Path ((idHom L).toFun (L.meet a b))
      (L.meet ((idHom L).toFun a) ((idHom L).toFun b))) :=
  ⟨(idHom L).map_meet a b⟩

theorem id_map_join (L : LatticeSignature.{u}) (a b : L.Carrier) :
    Nonempty (Path ((idHom L).toFun (L.join a b))
      (L.join ((idHom L).toFun a) ((idHom L).toFun b))) :=
  ⟨(idHom L).map_join a b⟩

theorem comp_map_meet (g : LatticeHom M N) (f : LatticeHom L M) (a b : L.Carrier) :
    Nonempty (Path ((comp g f).toFun (L.meet a b))
      (N.meet ((comp g f).toFun a) ((comp g f).toFun b))) :=
  ⟨(comp g f).map_meet a b⟩

theorem comp_map_join (g : LatticeHom M N) (f : LatticeHom L M) (a b : L.Carrier) :
    Nonempty (Path ((comp g f).toFun (L.join a b))
      (N.join ((comp g f).toFun a) ((comp g f).toFun b))) :=
  ⟨(comp g f).map_join a b⟩

theorem comp_map_bot (g : LatticeHom M N) (f : LatticeHom L M) :
    Nonempty (Path ((comp g f).toFun L.bot) N.bot) :=
  ⟨(comp g f).map_bot⟩

theorem comp_map_top (g : LatticeHom M N) (f : LatticeHom L M) :
    Nonempty (Path ((comp g f).toFun L.top) N.top) :=
  ⟨(comp g f).map_top⟩

end LatticeHom

structure LatticeCongruence (L : LatticeSignature) where
  Rel : L.Carrier → L.Carrier → Prop
  refl : ∀ a : L.Carrier, Rel a a
  symm : ∀ {a b : L.Carrier}, Rel a b → Rel b a
  trans : ∀ {a b c : L.Carrier}, Rel a b → Rel b c → Rel a c
  meet_closed :
    ∀ {a b c d : L.Carrier}, Rel a b → Rel c d → Rel (L.meet a c) (L.meet b d)
  join_closed :
    ∀ {a b c d : L.Carrier}, Rel a b → Rel c d → Rel (L.join a c) (L.join b d)

namespace LatticeCongruence

variable {L : LatticeSignature}
variable (Gam : LatticeCongruence L)
variable {a b c d : L.Carrier}

theorem rel_refl (a : L.Carrier) : Gam.Rel a a :=
  Gam.refl a

theorem rel_symm (h : Gam.Rel a b) : Gam.Rel b a :=
  Gam.symm h

theorem rel_trans (h1 : Gam.Rel a b) (h2 : Gam.Rel b c) : Gam.Rel a c :=
  Gam.trans h1 h2

theorem rel_meet_closed (h1 : Gam.Rel a b) (h2 : Gam.Rel c d) :
    Gam.Rel (L.meet a c) (L.meet b d) :=
  Gam.meet_closed h1 h2

theorem rel_join_closed (h1 : Gam.Rel a b) (h2 : Gam.Rel c d) :
    Gam.Rel (L.join a c) (L.join b d) :=
  Gam.join_closed h1 h2

theorem rel_meet_left (h : Gam.Rel a b) :
    Gam.Rel (L.meet a c) (L.meet b c) :=
  Gam.meet_closed h (Gam.refl c)

theorem rel_meet_right (h : Gam.Rel c d) :
    Gam.Rel (L.meet a c) (L.meet a d) :=
  Gam.meet_closed (Gam.refl a) h

theorem rel_join_left (h : Gam.Rel a b) :
    Gam.Rel (L.join a c) (L.join b c) :=
  Gam.join_closed h (Gam.refl c)

theorem rel_join_right (h : Gam.Rel c d) :
    Gam.Rel (L.join a c) (L.join a d) :=
  Gam.join_closed (Gam.refl a) h

theorem rel_bot : Gam.Rel L.bot L.bot :=
  Gam.refl L.bot

theorem rel_top : Gam.Rel L.top L.top :=
  Gam.refl L.top

end LatticeCongruence

inductive LatticePolynomial (L : LatticeSignature.{u}) (Gam : Type v) where
  | var : Gam → LatticePolynomial L Gam
  | bot : LatticePolynomial L Gam
  | top : LatticePolynomial L Gam
  | meet : LatticePolynomial L Gam → LatticePolynomial L Gam → LatticePolynomial L Gam
  | join : LatticePolynomial L Gam → LatticePolynomial L Gam → LatticePolynomial L Gam
deriving DecidableEq

namespace LatticePolynomial

variable {L : LatticeSignature.{u}}
variable {Gam : Type v}
variable {Del : Type w}

noncomputable def eval (Sym : Gam → L.Carrier) : LatticePolynomial L Gam → L.Carrier
  | .var g => Sym g
  | .bot => L.bot
  | .top => L.top
  | .meet p q => L.meet (eval Sym p) (eval Sym q)
  | .join p q => L.join (eval Sym p) (eval Sym q)

@[simp] theorem eval_var (Sym : Gam → L.Carrier) (g : Gam) :
    eval Sym (.var g) = Sym g :=
  rfl

@[simp] theorem eval_bot (Sym : Gam → L.Carrier) :
    eval Sym (.bot : LatticePolynomial L Gam) = L.bot :=
  rfl

@[simp] theorem eval_top (Sym : Gam → L.Carrier) :
    eval Sym (.top : LatticePolynomial L Gam) = L.top :=
  rfl

@[simp] theorem eval_meet (Sym : Gam → L.Carrier)
    (p q : LatticePolynomial L Gam) :
    eval Sym (.meet p q) = L.meet (eval Sym p) (eval Sym q) :=
  rfl

@[simp] theorem eval_join (Sym : Gam → L.Carrier)
    (p q : LatticePolynomial L Gam) :
    eval Sym (.join p q) = L.join (eval Sym p) (eval Sym q) :=
  rfl

noncomputable def map (Sym : Gam → Del) : LatticePolynomial L Gam → LatticePolynomial L Del
  | .var g => .var (Sym g)
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet (map Sym p) (map Sym q)
  | .join p q => .join (map Sym p) (map Sym q)

@[simp] theorem map_var (Sym : Gam → Del) (g : Gam) :
    map Sym (.var g) = (.var (Sym g) : LatticePolynomial L Del) :=
  rfl

@[simp] theorem map_bot (Sym : Gam → Del) :
    map Sym (.bot : LatticePolynomial L Gam) = (.bot : LatticePolynomial L Del) :=
  rfl

@[simp] theorem map_top (Sym : Gam → Del) :
    map Sym (.top : LatticePolynomial L Gam) = (.top : LatticePolynomial L Del) :=
  rfl

@[simp] theorem map_meet (Sym : Gam → Del)
    (p q : LatticePolynomial L Gam) :
    map Sym (.meet p q) = (.meet (map Sym p) (map Sym q) : LatticePolynomial L Del) :=
  rfl

@[simp] theorem map_join (Sym : Gam → Del)
    (p q : LatticePolynomial L Gam) :
    map Sym (.join p q) = (.join (map Sym p) (map Sym q) : LatticePolynomial L Del) :=
  rfl

@[simp] theorem eval_map (Val : Del → L.Carrier) (Sym : Gam → Del)
    (p : LatticePolynomial L Gam) :
    eval Val (map Sym p) = eval (fun g => Val (Sym g)) p := by
  induction p with
  | var g => rfl
  | bot => rfl
  | top => rfl
  | meet p q ihp ihq => simp [map, eval, ihp, ihq]
  | join p q ihp ihq => simp [map, eval, ihp, ihq]

@[simp] theorem map_id (p : LatticePolynomial L Gam) :
    map (fun g => g) p = p := by
  induction p with
  | var g => rfl
  | bot => rfl
  | top => rfl
  | meet p q ihp ihq => simp [map, ihp, ihq]
  | join p q ihp ihq => simp [map, ihp, ihq]

@[simp] theorem map_comp (Sym : Gam → Del) (Tau : Del → L.Carrier)
    (p : LatticePolynomial L Gam) :
    eval Tau (map Sym p) = eval (fun g => Tau (Sym g)) p := by
  simpa using eval_map (L := L) Tau Sym p

noncomputable def subst (Sym : Gam → LatticePolynomial L Del) :
    LatticePolynomial L Gam → LatticePolynomial L Del
  | .var g => Sym g
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet (subst Sym p) (subst Sym q)
  | .join p q => .join (subst Sym p) (subst Sym q)

@[simp] theorem subst_var (Sym : Gam → LatticePolynomial L Del) (g : Gam) :
    subst Sym (.var g) = Sym g :=
  rfl

@[simp] theorem subst_bot (Sym : Gam → LatticePolynomial L Del) :
    subst Sym (.bot : LatticePolynomial L Gam) = (.bot : LatticePolynomial L Del) :=
  rfl

@[simp] theorem subst_top (Sym : Gam → LatticePolynomial L Del) :
    subst Sym (.top : LatticePolynomial L Gam) = (.top : LatticePolynomial L Del) :=
  rfl

@[simp] theorem subst_meet (Sym : Gam → LatticePolynomial L Del)
    (p q : LatticePolynomial L Gam) :
    subst Sym (.meet p q) = (.meet (subst Sym p) (subst Sym q) : LatticePolynomial L Del) :=
  rfl

@[simp] theorem subst_join (Sym : Gam → LatticePolynomial L Del)
    (p q : LatticePolynomial L Gam) :
    subst Sym (.join p q) = (.join (subst Sym p) (subst Sym q) : LatticePolynomial L Del) :=
  rfl

@[simp] theorem eval_subst (Val : Del → L.Carrier) (Sym : Gam → LatticePolynomial L Del)
    (p : LatticePolynomial L Gam) :
    eval Val (subst Sym p) = eval (fun g => eval Val (Sym g)) p := by
  induction p with
  | var g => rfl
  | bot => rfl
  | top => rfl
  | meet p q ihp ihq => simp [subst, eval, ihp, ihq]
  | join p q ihp ihq => simp [subst, eval, ihp, ihq]

@[simp] theorem subst_id (p : LatticePolynomial L Gam) :
    subst (fun g => .var g) p = p := by
  induction p with
  | var g => rfl
  | bot => rfl
  | top => rfl
  | meet p q ihp ihq => simp [subst, ihp, ihq]
  | join p q ihp ihq => simp [subst, ihp, ihq]

@[simp] theorem subst_comp
    {Eta : Type x}
    (Sym : Gam → LatticePolynomial L Del)
    (Tau : Del → LatticePolynomial L Eta)
    (p : LatticePolynomial L Gam) :
    subst Tau (subst Sym p) = subst (fun g => subst Tau (Sym g)) p := by
  induction p with
  | var g => rfl
  | bot => rfl
  | top => rfl
  | meet p q ihp ihq => simp [subst, ihp, ihq]
  | join p q ihp ihq => simp [subst, ihp, ihq]

end LatticePolynomial

noncomputable def PolyRel {L : LatticeSignature.{u}} {Gam : Type v}
    (p q : LatticePolynomial L Gam) : Prop :=
  ∀ Sym : Gam → L.Carrier,
    Nonempty (Path (LatticePolynomial.eval Sym p) (LatticePolynomial.eval Sym q))

section PolyRelTheorems

variable {L : LatticeSignature.{u}}
variable {Gam : Type v}
variable {Del : Type w}
variable {p q r p1 p2 q1 q2 : LatticePolynomial L Gam}

theorem polyRel_refl (p : LatticePolynomial L Gam) :
    PolyRel (L := L) p p := by
  intro Sym
  exact ⟨Path.refl (LatticePolynomial.eval Sym p)⟩

theorem polyRel_symm (h : PolyRel (L := L) p q) :
    PolyRel (L := L) q p := by
  intro Sym
  rcases h Sym with ⟨pq⟩
  exact ⟨Path.symm pq⟩

theorem polyRel_trans (h1 : PolyRel (L := L) p q) (h2 : PolyRel (L := L) q r) :
    PolyRel (L := L) p r := by
  intro Sym
  rcases h1 Sym with ⟨pq⟩
  rcases h2 Sym with ⟨qr⟩
  exact ⟨Path.trans pq qr⟩

theorem polyRel_meet (h1 : PolyRel (L := L) p1 q1) (h2 : PolyRel (L := L) p2 q2) :
    PolyRel (L := L) (.meet p1 p2) (.meet q1 q2) := by
  intro Sym
  rcases h1 Sym with ⟨pq1⟩
  rcases h2 Sym with ⟨pq2⟩
  have hEq1 : LatticePolynomial.eval Sym p1 = LatticePolynomial.eval Sym q1 := pq1.toEq
  have hEq2 : LatticePolynomial.eval Sym p2 = LatticePolynomial.eval Sym q2 := pq2.toEq
  refine ⟨pathOfEq ?_⟩
  simpa [LatticePolynomial.eval, hEq1, hEq2]

theorem polyRel_join (h1 : PolyRel (L := L) p1 q1) (h2 : PolyRel (L := L) p2 q2) :
    PolyRel (L := L) (.join p1 p2) (.join q1 q2) := by
  intro Sym
  rcases h1 Sym with ⟨pq1⟩
  rcases h2 Sym with ⟨pq2⟩
  have hEq1 : LatticePolynomial.eval Sym p1 = LatticePolynomial.eval Sym q1 := pq1.toEq
  have hEq2 : LatticePolynomial.eval Sym p2 = LatticePolynomial.eval Sym q2 := pq2.toEq
  refine ⟨pathOfEq ?_⟩
  simpa [LatticePolynomial.eval, hEq1, hEq2]

theorem polyRel_subst
    (h : PolyRel (L := L) p q)
    (Sym : Gam → LatticePolynomial L Del) :
    PolyRel (L := L) (LatticePolynomial.subst Sym p) (LatticePolynomial.subst Sym q) := by
  intro Val
  rcases h (fun g => LatticePolynomial.eval Val (Sym g)) with ⟨pq⟩
  exact ⟨by simpa [LatticePolynomial.eval_subst] using pq⟩

end PolyRelTheorems

structure LatticeIdentity (L : LatticeSignature.{u}) (Gam : Type v) where
  lhs : LatticePolynomial L Gam
  rhs : LatticePolynomial L Gam

noncomputable def SatisfiesIdentity {L : LatticeSignature.{u}} {Gam : Type v}
    (Id : LatticeIdentity L Gam) : Prop :=
  PolyRel (L := L) Id.lhs Id.rhs

noncomputable def symmIdentity {L : LatticeSignature.{u}} {Gam : Type v}
    (Id : LatticeIdentity L Gam) : LatticeIdentity L Gam where
  lhs := Id.rhs
  rhs := Id.lhs

noncomputable def substIdentity {L : LatticeSignature.{u}} {Gam : Type v} {Del : Type w}
    (Sym : Gam → LatticePolynomial L Del)
    (Id : LatticeIdentity L Gam) : LatticeIdentity L Del where
  lhs := LatticePolynomial.subst Sym Id.lhs
  rhs := LatticePolynomial.subst Sym Id.rhs

section IdentityTheorems

variable {L : LatticeSignature.{u}}
variable {Gam : Type v}
variable {Del : Type w}
variable {p q r : LatticePolynomial L Gam}

theorem satisfies_refl (p : LatticePolynomial L Gam) :
    SatisfiesIdentity (L := L) { lhs := p, rhs := p } :=
  polyRel_refl (L := L) p

theorem satisfies_symm (Id : LatticeIdentity L Gam)
    (h : SatisfiesIdentity (L := L) Id) :
    SatisfiesIdentity (L := L) (symmIdentity Id) :=
  polyRel_symm (L := L) h

theorem satisfies_trans
    (h1 : PolyRel (L := L) p q) (h2 : PolyRel (L := L) q r) :
    PolyRel (L := L) p r :=
  polyRel_trans (L := L) h1 h2

theorem satisfies_meet_congr
    {p1 q1 p2 q2 : LatticePolynomial L Gam}
    (h1 : PolyRel (L := L) p1 q1) (h2 : PolyRel (L := L) p2 q2) :
    PolyRel (L := L) (.meet p1 p2) (.meet q1 q2) :=
  polyRel_meet (L := L) h1 h2

theorem satisfies_join_congr
    {p1 q1 p2 q2 : LatticePolynomial L Gam}
    (h1 : PolyRel (L := L) p1 q1) (h2 : PolyRel (L := L) p2 q2) :
    PolyRel (L := L) (.join p1 p2) (.join q1 q2) :=
  polyRel_join (L := L) h1 h2

theorem satisfies_subst (Id : LatticeIdentity L Gam)
    (h : SatisfiesIdentity (L := L) Id)
    (Sym : Gam → LatticePolynomial L Del) :
    SatisfiesIdentity (L := L) (substIdentity Sym Id) := by
  exact polyRel_subst (L := L) h Sym

end IdentityTheorems

abbrev EquationalTheory (L : LatticeSignature.{u}) (Gam : Type v) :=
  List (LatticeIdentity L Gam)

noncomputable def ModelsTheory {L : LatticeSignature.{u}} {Gam : Type v}
    (Theory : EquationalTheory L Gam) : Prop :=
  ∀ Id : LatticeIdentity L Gam, Id ∈ Theory → SatisfiesIdentity (L := L) Id

section BirkhoffTheorems

variable {L : LatticeSignature.{u}}
variable {Gam : Type v}
variable (Theory : EquationalTheory L Gam)

theorem satisfies_in_theory
    (h : ModelsTheory (L := L) Theory)
    (Id : LatticeIdentity L Gam) (hMem : Id ∈ Theory) :
    SatisfiesIdentity (L := L) Id :=
  h Id hMem

theorem birkhoff_sound
    (h : ModelsTheory (L := L) Theory) :
    ∀ Id : LatticeIdentity L Gam, Id ∈ Theory → SatisfiesIdentity (L := L) Id :=
  h

theorem birkhoff_complete
    (h : ∀ Id : LatticeIdentity L Gam, Id ∈ Theory → SatisfiesIdentity (L := L) Id) :
    ModelsTheory (L := L) Theory :=
  h

theorem birkhoff_theorem :
    ModelsTheory (L := L) Theory ↔
      (∀ Id : LatticeIdentity L Gam, Id ∈ Theory → SatisfiesIdentity (L := L) Id) :=
  Iff.rfl

end BirkhoffTheorems

abbrev FreeLattice (L : LatticeSignature.{u}) (Gam : Type v) :=
  LatticePolynomial L Gam

noncomputable def freeVar {L : LatticeSignature.{u}} {Gam : Type v} (g : Gam) : FreeLattice L Gam :=
  .var g

section FreeLatticeTheorems

variable {L : LatticeSignature.{u}}
variable {Gam : Type v}

theorem freeVar_eval (Sym : Gam → L.Carrier) (g : Gam) :
    LatticePolynomial.eval Sym (freeVar (L := L) g) = Sym g :=
  rfl

theorem freeMeet_eval (Sym : Gam → L.Carrier) (p q : FreeLattice L Gam) :
    LatticePolynomial.eval Sym (.meet p q) =
      L.meet (LatticePolynomial.eval Sym p) (LatticePolynomial.eval Sym q) :=
  rfl

theorem freeJoin_eval (Sym : Gam → L.Carrier) (p q : FreeLattice L Gam) :
    LatticePolynomial.eval Sym (.join p q) =
      L.join (LatticePolynomial.eval Sym p) (LatticePolynomial.eval Sym q) :=
  rfl

theorem freeBot_eval (Sym : Gam → L.Carrier) :
    LatticePolynomial.eval Sym (.bot : FreeLattice L Gam) = L.bot :=
  rfl

theorem freeTop_eval (Sym : Gam → L.Carrier) :
    LatticePolynomial.eval Sym (.top : FreeLattice L Gam) = L.top :=
  rfl

end FreeLatticeTheorems

noncomputable def WhitmanCondition (L : LatticeSignature.{u}) : Prop :=
  ∀ a b c d : L.Carrier,
    Nonempty (Path (L.meet (L.join a b) (L.join c d))
      (L.join (L.meet (L.join a b) c) (L.meet (L.join a b) d)))

section WhitmanTheorems

variable {L : LatticeSignature.{u}}
variable (W : WhitmanAxioms L)

noncomputable def whitman_path (a b c d : L.Carrier) :
    Nonempty (Path (L.meet (L.join a b) (L.join c d))
      (L.join (L.meet (L.join a b) c) (L.meet (L.join a b) d))) :=
  ⟨W.whitman a b c d⟩

noncomputable def whitman_condition_holds : WhitmanCondition L := by
  intro a b c d
  exact ⟨W.whitman a b c d⟩

noncomputable def whitman_symm (a b c d : L.Carrier) :
    Nonempty (Path (L.join (L.meet (L.join a b) c) (L.meet (L.join a b) d))
      (L.meet (L.join a b) (L.join c d))) :=
  ⟨Path.symm (W.whitman a b c d)⟩

theorem whitman_roundtrip_toEq (a b c d : L.Carrier) :
    (Path.trans (W.whitman a b c d) (Path.symm (W.whitman a b c d))).toEq = rfl := by
  simp

end WhitmanTheorems

end ComputationalPaths.Path.Algebra.LatticeVarietiesDeep
