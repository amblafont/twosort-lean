import CartexpAristotle.SliceExponentiable

open CategoryTheory Limits

universe v u v₂ u₂

namespace SliceExp

section MapSetup

variable {C : Type u} [Category.{v} C] {E : Type u₂} [Category.{v₂} E] (F : C ⥤ E)
  [PreservesLimitsOfShape WalkingCospan F]
variable {X Y X' Y' c Z : C} {u : Y ⟶ X} {u' : Y' ⟶ X'} {p₁' : Y' ⟶ Y} {e : X' ⟶ X}

lemma functor_on_FBF (D : Data u c) {d : C} {f : d ⟶ D.P} {h : d ⟶ X} (K : ChosenPullback u h)
    (eq : h = f ≫ D.pi) :
    F.map (FBF_on_mor D K eq) = FBF_on_mor (functor_on F D) (functPullback F K)
      (f := F.map f) (by simp only [functor_on]; rw [eq, F.map_comp]) := by
  apply (functor_on F D).Pbk.hom_ext
  · refine Eq.trans ?_ (FBF_on_mor_fst (functor_on F D) (functPullback F K) _).symm
    change F.map (FBF_on_mor D K eq) ≫ F.map D.Pbk.p₁ = F.map K.p₁
    rw [← F.map_comp, FBF_on_mor_fst]
  · refine Eq.trans ?_ (FBF_on_mor_snd (functor_on F D) (functPullback F K) _).symm
    change F.map (FBF_on_mor D K eq) ≫ F.map D.Pbk.p₂ = F.map K.p₂ ≫ F.map f
    rw [← F.map_comp, FBF_on_mor_snd, F.map_comp]

lemma functor_on_liftPbk {hpb : IsPullback p₁' u' u e} {dc : Data u c} {D : Data u' c}
    {ω : D.P ⟶ dc.P} (hω : ω ≫ dc.pi = D.pi ≫ e) (hpb' : IsPullback (F.map p₁') (F.map u')
      (F.map u) (F.map e)) (hω' : F.map ω ≫ (functor_on F dc).pi = (functor_on F D).pi ≫ F.map e) :
    F.map (liftPbk hpb dc D ω hω) = liftPbk hpb' (functor_on F dc) (functor_on F D) (F.map ω) hω' := by
  apply (functor_on F dc).Pbk.hom_ext
  · have h1 : liftPbk hpb dc D ω hω ≫ dc.Pbk.p₁ = D.Pbk.p₁ ≫ p₁' := IsPullback.lift_fst _ _ _ _
    have h2 : liftPbk hpb' (functor_on F dc) (functor_on F D) (F.map ω) hω' ≫
        (functor_on F dc).Pbk.p₁ = (functor_on F D).Pbk.p₁ ≫ F.map p₁' :=
      IsPullback.lift_fst _ _ _ _
    refine Eq.trans ?_ h2.symm
    change F.map (liftPbk hpb dc D ω hω) ≫ F.map dc.Pbk.p₁ = F.map D.Pbk.p₁ ≫ F.map p₁'
    rw [← F.map_comp, h1, F.map_comp]
  · have h1 : liftPbk hpb dc D ω hω ≫ dc.Pbk.p₂ = D.Pbk.p₂ ≫ ω := IsPullback.lift_snd _ _ _ _
    have h2 : liftPbk hpb' (functor_on F dc) (functor_on F D) (F.map ω) hω' ≫
        (functor_on F dc).Pbk.p₂ = (functor_on F D).Pbk.p₂ ≫ F.map ω :=
      IsPullback.lift_snd _ _ _ _
    refine Eq.trans ?_ h2.symm
    change F.map (liftPbk hpb dc D ω hω) ≫ F.map dc.Pbk.p₂ = F.map D.Pbk.p₂ ≫ F.map ω
    rw [← F.map_comp, h1, F.map_comp]

variable {hpb : IsPullback p₁' u' u e} {dc : Data u c} {dZ : Data u Z} {q : c ⟶ Z} {w : X' ⟶ Z}
  {D : Data u' c}

/-- The image of a `Setup` under a functor preserving pullbacks. -/
noncomputable def Setup.map (S : Setup hpb dc dZ q w D) :
    Setup (F.map_isPullback hpb) (functor_on F dc) (functor_on F dZ) (F.map q) (F.map w)
      (functor_on F D) where
  Pq := F.map S.Pq
  τ := F.map S.τ
  ω := F.map S.ω
  hPq := by
    change F.map dc.pi = F.map S.Pq ≫ F.map dZ.pi
    rw [← F.map_comp, ← S.hPq]
  hPqε := by
    have := congrArg F.map S.hPqε
    rw [F.map_comp, F.map_comp, functor_on_FBF] at this
    exact this
  hτ := by
    change F.map e = F.map S.τ ≫ F.map dZ.pi
    rw [← F.map_comp, ← S.hτ]
  hτε := by
    have := congrArg F.map S.hτε
    rw [F.map_comp, F.map_comp, functor_on_FBF] at this
    refine this.trans ?_
    congr 1
  hω := by
    change F.map S.ω ≫ F.map dc.pi = F.map D.pi ≫ F.map e
    rw [← F.map_comp, ← F.map_comp, S.hω]
  hW := S.hW.map F
  hε := by
    have := congrArg F.map S.hε
    rw [F.map_comp, functor_on_liftPbk F S.hω] at this
    exact this

end MapSetup

section Preserve

variable {C : Type u} [Category.{v} C] {E : Type u₂} [Category.{v₂} E]

lemma SliceUniv.postcomp {X' Y' c Z Z' : E} {u' : Y' ⟶ X'} {D : Data u' c} {q : c ⟶ Z}
    {w : X' ⟶ Z} (h : SliceUniv D q w) (θ : Z ⟶ Z') [Mono θ] : SliceUniv D (q ≫ θ) (w ≫ θ) where
  exists_mor K g hg := h.exists_mor K g (by
    rw [← cancel_mono θ]; simpa using hg)
  uniq := h.uniq

instance preservesCospan_post (F : C ⥤ E) [PreservesLimitsOfShape WalkingCospan F] {Z : C} :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := Z) F) :=
  haveI : PreservesLimitsOfShape WalkingCospan (Over.post (X := Z) F ⋙ Over.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget Z ⋙ F))
  preservesLimitsOfShape_of_reflects_of_preserves (Over.post (X := Z) F) (Over.forget _)

section SlicePreserves

variable [HasPullbacks C] (F : C ⥤ E) [PreservesLimitsOfShape WalkingCospan F] {X Y : C}
  (u : Y ⟶ X) [IsExpArr u] [FunctorPreserves u F] {Z' : E} (θ : F.obj (sZ u) ⟶ Z') [IsIso θ]

/-- The functor `C/PX ⥤ E/Z'` induced by `F` and an isomorphism `θ`. -/
noncomputable abbrev sliceMap : Over (sZ u) ⥤ Over Z' := Over.post F ⋙ Over.map θ

@[instance_reducible]
noncomputable def sliceUnivMap (c : Over (sZ u)) :
    Universal (functor_on (sliceMap F u θ) (sOverData u c)) := by
  haveI : Universal (sdc u c) := inferInstance
  haveI : Universal (functor_on F (sdc u c)) :=
    FunctorPreserves.functor_preserves (sdc u c) inferInstance
  haveI : Universal (functor_on F (sdZ u)) :=
    FunctorPreserves.functor_preserves (sdZ u) inferInstance
  let S := (sSetup u c).map F
  refine universal_of_sliceUniv _ _ ?_
  exact (sliceUniv_of_isPullback (F.map_isPullback (shpb u)) (functor_on F (sdc u c))
    (functor_on F (sdZ u)) (F.map c.hom) (F.map (sW u)) S.Pq S.hPq S.hPqε S.τ S.hτ S.hτε _ S.ω
    S.hω S.hW S.hε).postcomp θ

noncomputable instance sliceFunctorPreserves : FunctorPreserves (sArr u) (sliceMap F u θ) :=
  functor_preserves_1_is_enough (sArr u) (sliceMap F u θ) (sOverData u) (sOverUniv u)
    (sliceUnivMap F u θ)

end SlicePreserves

end Preserve

end SliceExp
