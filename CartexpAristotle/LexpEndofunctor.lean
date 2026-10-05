import CartexpAristotle.LexpTheta

/-!
# The endofunctor `- / PX` of `Lexp`

`Lexp.Φ` sends a `Lexp`-category `(C, p : Y ⟶ X)` to `(C / P X, p̲ : Y̲ ⟶ X̲)`, where `p̲` is the
pullback of `p` along the counit `ε_X : X̲ = Y ×_X P X ⟶ X`, and a `Lexp`-functor `F` to
`Z ↦ (F Z ⟶ F (P X) ≅ P X')`.

## References

* [Paper, §4.2, Prop. `prop:lexp-functor-p2`]: `Lexp.Φ` is the endofunctor `MFunctor{-}`
  (written `- / PX` in the paper) of `Lexp`.
* [Paper, §3.1, Props. `prop:p2-construction` and `prop:p2-exponentiable`]: `Lexp.Φobj`.
-/

open CategoryTheory Limits

universe v u

section OverExt

variable {C : Type*} [Category C] {D : Type*} [Category D] {Z : C} {Z' : D}

lemma over_obj_ext (a b : Over Z') (hl : a.left = b.left) (hh : a.hom = eqToHom hl ≫ b.hom) :
    a = b := by
  obtain ⟨al, ar, ah⟩ := a
  obtain ⟨bl, br, bh⟩ := b
  obtain rfl : ar = br := Subsingleton.elim _ _
  change al = bl at hl
  subst hl
  change ah = eqToHom rfl ≫ bh at hh
  simp at hh
  subst hh
  rfl

lemma over_functor_ext {H K : Over Z ⥤ Over Z'}
    (hl : ∀ c, (H.obj c).left = (K.obj c).left)
    (hh : ∀ c, (H.obj c).hom = eqToHom (hl c) ≫ (K.obj c).hom)
    (hm : ∀ {c d} (f : c ⟶ d), (H.map f).left = eqToHom (hl c) ≫ (K.map f).left ≫
      eqToHom (hl d).symm) : H = K := by
  refine CategoryTheory.Functor.ext (fun c => over_obj_ext _ _ (hl c) (hh c)) (fun c d f => ?_)
  ext
  simp [Over.eqToHom_left, hm]

end OverExt

namespace Lexp

variable {A B : Lexp.{v, u}} (F : A ⟶ B)

/-- The left component of `F.iso`. -/
noncomputable def isoL : F.functor.obj A.dom ≅ B.dom := Arrow.leftFunc.mapIso F.iso

/-- The right component of `F.iso`. -/
noncomputable def isoR : F.functor.obj A.cod ≅ B.cod := Arrow.rightFunc.mapIso F.iso

@[simp] lemma isoL_hom : (isoL F).hom = F.iso.hom.left := rfl

@[simp] lemma isoR_hom : (isoR F).hom = F.iso.hom.right := rfl

lemma isoL_hom_arr : F.functor.map A.arr ≫ (isoR F).hom = (isoL F).hom ≫ B.arr :=
  w_hom F.iso

/-- `θ` as an isomorphism. -/
noncomputable def isoθ : F.functor.obj (SliceExp.sZ A.arr) ≅ SliceExp.sZ B.arr := asIso (θ F)

@[simp] lemma isoθ_hom : (isoθ F).hom = θ F := rfl

/-- The square exhibiting `F (Y ×_X P X) ≅ Y ×_X P X` for the second arrow. -/
lemma sqX : IsPullback (Eθ F).Pbk.p₁ ((Eθ F).Pbk.p₂ ≫ θ F) B.arr (dX B).pi :=
  (Eθ F).Pbk.isPullback.of_iso (Iso.refl _) (Iso.refl _) (isoθ F) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp only [Iso.refl_hom, Category.comp_id]; exact (θ_pi F).symm)

/-- The comparison `F (Y ×_X P X) ≅ Y ×_X P X`. -/
noncomputable def ιX : F.functor.obj (dX A).Pbk.pullback ≅ (dX B).Pbk.pullback :=
  (sqX F).isoIsPullback _ _ (dX B).Pbk.isPullback

lemma ιX_fst : (ιX F).hom ≫ (dX B).Pbk.p₁ = F.functor.map (dX A).Pbk.p₁ ≫ F.iso.hom.left :=
  (sqX F).isoIsPullback_hom_fst _ _ (dX B).Pbk.isPullback

lemma ιX_snd : (ιX F).hom ≫ (dX B).Pbk.p₂ = F.functor.map (dX A).Pbk.p₂ ≫ θ F :=
  (sqX F).isoIsPullback_hom_snd _ _ (dX B).Pbk.isPullback

lemma ιX_eps : F.functor.map (dX A).epsilon ≫ F.iso.hom.right = (ιX F).hom ≫ (dX B).epsilon := by
  rw [θ_eps F]
  congr 1

open SliceExp in
lemma sqY : IsPullback (F.functor.map (pullback.fst A.arr (sE A.arr)) ≫ (isoL F).hom)
    (F.functor.map (su' A.arr) ≫ (ιX F).hom) B.arr (sE B.arr) :=
  (F.functor.map_isPullback (shpb A.arr)).of_iso (Iso.refl _) (isoL F) (ιX F) (isoR F)
    (by simp) (by simp) (isoL_hom_arr F) (ιX_eps F)

open SliceExp in
/-- The comparison `F (Y') ≅ Y'` of the domains of the pulled back arrows. -/
noncomputable def ιY : F.functor.obj (sY' A.arr) ≅ sY' B.arr :=
  (sqY F).isoIsPullback _ _ (shpb B.arr)

open SliceExp in
lemma ιY_fst : (ιY F).hom ≫ pullback.fst B.arr (sE B.arr) =
    F.functor.map (pullback.fst A.arr (sE A.arr)) ≫ F.iso.hom.left :=
  (sqY F).isoIsPullback_hom_fst _ _ (shpb B.arr)

open SliceExp in
lemma ιY_snd : (ιY F).hom ≫ su' B.arr = F.functor.map (su' A.arr) ≫ (ιX F).hom :=
  (sqY F).isoIsPullback_hom_snd _ _ (shpb B.arr)

/-- `θ` is characterized by its compatibility with the projection and the counit. -/
lemma θ_unique (θ' : F.functor.obj (SliceExp.sZ A.arr) ⟶ SliceExp.sZ B.arr)
    (h : (Eθ F).pi = θ' ≫ (dX B).pi)
    (h2 : (Eθ F).epsilon ≫ F.iso.hom.right = FBF_on_mor (dX B) (Eθ F).Pbk h ≫ (dX B).epsilon) :
    θ' = θ F :=
  mor_unique (d1 := dX B) ((Eθ F).epsilon ≫ F.iso.hom.right) θ' h h2

lemma θ_id (A : Lexp.{v, u}) : θ (𝟙 A) = 𝟙 _ := by
  have h : (Eθ (𝟙 A)).pi = 𝟙 _ ≫ (dX A).pi := by
    change (dX A).pi ≫ 𝟙 _ = 𝟙 _ ≫ (dX A).pi
    simp
  refine (θ_unique (𝟙 A) (𝟙 _) h ?_).symm
  have hF : FBF_on_mor (dX A) (Eθ (𝟙 A)).Pbk h = 𝟙 _ := by
    apply (dX A).Pbk.hom_ext
    · refine (SliceExp.FBF_on_mor_fst _ _ h).trans ?_
      change (dX A).Pbk.p₁ ≫ 𝟙 _ = 𝟙 _ ≫ (dX A).Pbk.p₁
      simp
    · refine (SliceExp.FBF_on_mor_snd _ _ h).trans ?_
      change (dX A).Pbk.p₂ ≫ 𝟙 _ = 𝟙 _ ≫ (dX A).Pbk.p₂
      simp
  rw [hF]
  change (dX A).epsilon ≫ 𝟙 _ = 𝟙 _ ≫ (dX A).epsilon
  simp

variable {C' : Lexp.{v, u}} (G : B ⟶ C')

lemma FBF_Eθ_comp (h : (Eθ (F ≫ G)).pi = (G.functor.map (θ F) ≫ θ G) ≫ (dX C').pi) :
    FBF_on_mor (dX C') (Eθ (F ≫ G)).Pbk h = G.functor.map (ιX F).hom ≫ (ιX G).hom := by
  apply (dX C').Pbk.hom_ext
  · refine (SliceExp.FBF_on_mor_fst _ _ h).trans ?_
    change G.functor.map (F.functor.map (dX A).Pbk.p₁) ≫ G.functor.map F.iso.hom.left ≫
      G.iso.hom.left = (G.functor.map (ιX F).hom ≫ (ιX G).hom) ≫ (dX C').Pbk.p₁
    rw [Category.assoc, ιX_fst G, ← Category.assoc (G.functor.map (ιX F).hom),
      ← G.functor.map_comp, ιX_fst F, G.functor.map_comp, Category.assoc]
  · refine (SliceExp.FBF_on_mor_snd _ _ h).trans ?_
    change G.functor.map (F.functor.map (dX A).Pbk.p₂) ≫ G.functor.map (θ F) ≫ θ G =
      (G.functor.map (ιX F).hom ≫ (ιX G).hom) ≫ (dX C').Pbk.p₂
    rw [Category.assoc, ιX_snd G, ← Category.assoc (G.functor.map (ιX F).hom),
      ← G.functor.map_comp, ιX_snd F, G.functor.map_comp, Category.assoc]

lemma θ_comp : θ (F ≫ G) = G.functor.map (θ F) ≫ θ G := by
  have h : (Eθ (F ≫ G)).pi = (G.functor.map (θ F) ≫ θ G) ≫ (dX C').pi := by
    change G.functor.map (F.functor.map (dX A).pi) ≫ G.functor.map F.iso.hom.right ≫
      G.iso.hom.right = _
    rw [Category.assoc, θ_pi G, ← Category.assoc (G.functor.map (θ F)), ← G.functor.map_comp,
      θ_pi F, G.functor.map_comp, Category.assoc]
  refine (θ_unique (F ≫ G) _ h ?_).symm
  rw [FBF_Eθ_comp F G h]
  change G.functor.map (F.functor.map (dX A).epsilon) ≫ G.functor.map F.iso.hom.right ≫
    G.iso.hom.right = (G.functor.map (ιX F).hom ≫ (ιX G).hom) ≫ (dX C').epsilon
  rw [Category.assoc, ← ιX_eps G, ← Category.assoc (G.functor.map (ιX F).hom),
    ← G.functor.map_comp, ← ιX_eps F, G.functor.map_comp, Category.assoc]

lemma ιX_id (A : Lexp.{v, u}) : (ιX (𝟙 A)).hom = 𝟙 _ := by
  apply (dX A).Pbk.hom_ext
  · refine (ιX_fst (𝟙 A)).trans ?_
    change (dX A).Pbk.p₁ ≫ 𝟙 _ = 𝟙 _ ≫ (dX A).Pbk.p₁
    simp
  · refine (ιX_snd (𝟙 A)).trans ?_
    change (dX A).Pbk.p₂ ≫ θ (𝟙 A) = 𝟙 _ ≫ (dX A).Pbk.p₂
    rw [θ_id]
    simp

lemma ιX_comp : (ιX (F ≫ G)).hom = G.functor.map (ιX F).hom ≫ (ιX G).hom := by
  apply (dX C').Pbk.hom_ext
  · refine (ιX_fst (F ≫ G)).trans ?_
    change G.functor.map (F.functor.map (dX A).Pbk.p₁) ≫ G.functor.map F.iso.hom.left ≫
      G.iso.hom.left = (G.functor.map (ιX F).hom ≫ (ιX G).hom) ≫ (dX C').Pbk.p₁
    rw [Category.assoc, ιX_fst G, ← Category.assoc (G.functor.map (ιX F).hom),
      ← G.functor.map_comp, ιX_fst F, G.functor.map_comp, Category.assoc]
  · refine (ιX_snd (F ≫ G)).trans ?_
    change G.functor.map (F.functor.map (dX A).Pbk.p₂) ≫ θ (F ≫ G) =
      (G.functor.map (ιX F).hom ≫ (ιX G).hom) ≫ (dX C').Pbk.p₂
    rw [θ_comp, Category.assoc, ιX_snd G, ← Category.assoc (G.functor.map (ιX F).hom),
      ← G.functor.map_comp, ιX_snd F, G.functor.map_comp, Category.assoc]

open SliceExp in
lemma ιY_id (A : Lexp.{v, u}) : (ιY (𝟙 A)).hom = 𝟙 _ := by
  apply (shpb A.arr).hom_ext
  · refine (ιY_fst (𝟙 A)).trans ?_
    change pullback.fst A.arr (sE A.arr) ≫ 𝟙 _ = 𝟙 _ ≫ pullback.fst A.arr (sE A.arr)
    simp
  · refine (ιY_snd (𝟙 A)).trans ?_
    change su' A.arr ≫ (ιX (𝟙 A)).hom = 𝟙 _ ≫ su' A.arr
    rw [ιX_id]
    simp

open SliceExp in
lemma ιY_comp : (ιY (F ≫ G)).hom = G.functor.map (ιY F).hom ≫ (ιY G).hom := by
  apply (shpb C'.arr).hom_ext
  · refine (ιY_fst (F ≫ G)).trans ?_
    change G.functor.map (F.functor.map (pullback.fst A.arr (sE A.arr))) ≫
      G.functor.map F.iso.hom.left ≫ G.iso.hom.left =
      (G.functor.map (ιY F).hom ≫ (ιY G).hom) ≫ pullback.fst C'.arr (sE C'.arr)
    rw [Category.assoc, ιY_fst G, ← Category.assoc (G.functor.map (ιY F).hom),
      ← G.functor.map_comp, ιY_fst F, G.functor.map_comp, Category.assoc]
  · refine (ιY_snd (F ≫ G)).trans ?_
    change G.functor.map (F.functor.map (su' A.arr)) ≫ (ιX (F ≫ G)).hom =
      (G.functor.map (ιY F).hom ≫ (ιY G).hom) ≫ su' C'.arr
    rw [ιX_comp, Category.assoc, ιY_snd G, ← Category.assoc (G.functor.map (ιY F).hom),
      ← G.functor.map_comp, ιY_snd F, G.functor.map_comp, Category.assoc]

end Lexp

namespace Lexp

open SliceExp

/-- The object part of the endofunctor: `(C, p : Y ⟶ X)` is sent to `C / P X` with the pullback
of `p` along the counit `Y ×_X P X ⟶ X`.

[Paper, §3.1, Prop. `prop:p2-exponentiable`]: the `Lexp`-category `(C / P X, p̲)`. -/
noncomputable def Φobj (A : Lexp.{v, max u v}) : Lexp.{v, max u v} where
  carrier := Over (sZ A.arr)
  arr := sArr A.arr

variable {A B : Lexp.{v, max u v}} (F : A ⟶ B)

/-- The underlying functor of `Φ F`. -/
noncomputable abbrev Φfun : Over (sZ A.arr) ⥤ Over (sZ B.arr) := sliceMap F.functor A.arr (θ F)

noncomputable instance Φfun_preservesCospan : PreservesLimitsOfShape WalkingCospan (Φfun F) :=
  haveI := θ_isIso F
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.post F.functor ⋙ Over.map (θ F)))

noncomputable instance Φfun_preservesTerminal :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Φfun F) :=
  have : PreservesLimit (Functor.empty.{0} (Over (sZ A.arr))) (Φfun F) :=
    preservesTerminal_of_iso (Φfun F)
      ((Φfun F).mapIso (terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal) ≪≫
        Over.isoMk (g := Over.mk (𝟙 (sZ B.arr))) (isoθ F)
          (by change θ F ≫ 𝟙 _ = F.functor.map (𝟙 _) ≫ θ F; simp) ≪≫
        Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal)
  preservesLimitsOfShape_pempty_of_preservesTerminal (Φfun F)

/-- The left component of the isomorphism of arrows for `Φ F`. -/
noncomputable def Φisoleft : (Φfun F).obj (Over.mk (su' A.arr ≫ sW A.arr)) ≅
    Over.mk (su' B.arr ≫ sW B.arr) :=
  Over.isoMk (ιY F) (by
    change (ιY F).hom ≫ su' B.arr ≫ sW B.arr = F.functor.map (su' A.arr ≫ sW A.arr) ≫ θ F
    rw [← Category.assoc, ιY_snd, Category.assoc, ιX_snd, Functor.map_comp, Category.assoc])

/-- The right component of the isomorphism of arrows for `Φ F`. -/
noncomputable def Φisoright : (Φfun F).obj (Over.mk (sW A.arr)) ≅ Over.mk (sW B.arr) :=
  Over.isoMk (ιX F) (ιX_snd F)

/-- The isomorphism of arrows for `Φ F`. -/
noncomputable def Φiso : Arrow.mk ((Φfun F).map (sArr A.arr)) ≅ Arrow.mk (sArr B.arr) :=
  Arrow.isoMk (Φisoleft F) (Φisoright F) (Over.OverMorphism.ext (ιY_snd F))

/-- The morphism `Φ F`. -/
noncomputable def Φmap : Φobj A ⟶ Φobj B where
  functor := Φfun F
  preservesPullbacks := Φfun_preservesCospan F
  preservesTerminal := Φfun_preservesTerminal F
  preservesArr := sliceFunctorPreserves F.functor A.arr (θ F)
  iso := Φiso F

lemma Φfun_id (A : Lexp.{v, max u v}) : Φfun (𝟙 A) = 𝟭 _ :=
  over_functor_ext (H := Φfun (𝟙 A)) (K := 𝟭 _) (fun _ => rfl)
    (fun c => by
      change c.hom ≫ θ (𝟙 A) = 𝟙 _ ≫ c.hom
      rw [θ_id]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (fun f => by
      change f.left = 𝟙 _ ≫ f.left ≫ 𝟙 _
      simp)

lemma Φfun_comp {A B C' : Lexp.{v, max u v}} (F : A ⟶ B) (G : B ⟶ C') :
    (Φfun (F ≫ G) : Over (sZ A.arr) ⥤ Over (sZ C'.arr)) = Φfun F ⋙ Φfun G :=
  by
  refine over_functor_ext (fun _ => rfl) (fun c => ?_) (fun f => ?_)
  · change G.functor.map (F.functor.map c.hom) ≫ θ (F ≫ G) =
      𝟙 _ ≫ G.functor.map (F.functor.map c.hom ≫ θ F) ≫ θ G
    rw [θ_comp, G.functor.map_comp, Category.assoc, Category.id_comp]
  · change G.functor.map (F.functor.map f.left) =
      𝟙 _ ≫ G.functor.map (F.functor.map f.left) ≫ 𝟙 _
    simp

lemma Φmap_id (A : Lexp.{v, max u v}) : Φmap (𝟙 A) = 𝟙 (Φobj A) :=
  Hom.ext' (Φfun_id A)
    (Over.OverMorphism.ext (by
      erw [Over.comp_left, Over.eqToHom_left]
      change (ιY (𝟙 A)).hom = 𝟙 _ ≫ 𝟙 _
      rw [ιY_id]; simp))
    (Over.OverMorphism.ext (by
      erw [Over.comp_left, Over.eqToHom_left]
      change (ιX (𝟙 A)).hom = 𝟙 _ ≫ 𝟙 _
      rw [ιX_id]; simp))

lemma Φmap_comp {A B C' : Lexp.{v, max u v}} (F : A ⟶ B) (G : B ⟶ C') :
    Φmap (F ≫ G) = Φmap F ≫ Φmap G :=
  Hom.ext' (Φfun_comp F G)
    (Over.OverMorphism.ext (by
      erw [Over.comp_left, Over.eqToHom_left]
      change (ιY (F ≫ G)).hom = 𝟙 _ ≫ (G.functor.map (ιY F).hom ≫ (ιY G).hom)
      rw [ιY_comp, Category.id_comp]))
    (Over.OverMorphism.ext (by
      erw [Over.comp_left, Over.eqToHom_left]
      change (ιX (F ≫ G)).hom = 𝟙 _ ≫ (G.functor.map (ιX F).hom ≫ (ιX G).hom)
      rw [ιX_comp, Category.id_comp]))

/-- The endofunctor of `Lexp` sending `(C, p : Y ⟶ X)` to `(C / P X, p')`, where `p'` is the
pullback of `p` along the counit `Y ×_X P X ⟶ X`.

[Paper, §4.2, Prop. `prop:lexp-functor-p2`]: the endofunctor `- / PX` of `Lexp`. -/
noncomputable def Φ : Lexp.{v, max u v} ⥤ Lexp.{v, max u v} where
  obj := Φobj
  map := Φmap
  map_id := Φmap_id
  map_comp := Φmap_comp

end Lexp
