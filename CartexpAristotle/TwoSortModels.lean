import CartexpAristotle.FamilyFunctor
import CartexpAristotle.TwoSortificationCounit

/-!
# Models of the two-sortification

Let `FinGat` be a bi-initial object of `ExpArrCat` (a *GAT* is an object of `FinGat`), `M` the model
functor, `T` the two-sortification functor and `F_Γ = familyFunctor Γ : M Γ ⥤ Fam` the family
functor of a GAT `Γ`, obtained from the bi-initial morphism `famFunctor : FinGat ⟶ FamSliceExp`
into the cartesian colax slice over `Fam`.

* `modelsTwoSortIso Γ` (Theorem "characterisation-models-two-sortification"): the category of
  models of the two-sortification of `Γ`, `M (T Γ)`, is isomorphic to the cartesian comma category
  `F_Γ / Fam` (`FamSlice.CartComma`), compatibly with the projections to `Fam`
  (`modelsTwoSortIso_hom_comp_proj`).
* `modelsTwoSortIso_hom_comp_counit`: through this isomorphism, the projection
  `F_Γ / Fam ⥤ M Γ`, `(M, T, f) ↦ M`, corresponds to the image under the model functor of the
  component at `Γ` of `twoSortCounit : T ⋙ Over.forget ⟶ 𝟭`. Equivalently
  (`coreProjection_eq`), the core projection natural transformation is the whiskering of
  `twoSortCounit` by the model functor.

Both are deduced from bi-initiality: the first by comparing the two morphisms
`famFunctor ≫ toOverHom` and `T ≫ Φ M ≫ (Φ CatExp ≃ FamOverExp)` from `FinGat` to
`FamOverExp`, the second by `IsBiInitial.existsUnique_natTrans_gen`.
-/

universe w v u

open CategoryTheory Limits FamSlice FamOverExpArr FamSliceForget SliceExp PointedForget
  FamPointedForget FamOverFrobenius

namespace ExpArrCat

/-- The natural isomorphism underlying an invertible 2-cell of `ExpArrCat`. -/
@[simps]
def Hom₂.natIsoOfIso {A B : ExpArrCat.{v, u}} {F G : A ⟶ B} (e : F ≅ G) :
    F.functor ≅ G.functor where
  hom := e.hom.nat
  inv := e.inv.nat
  hom_inv_id := congrArg Hom₂.nat e.hom_inv_id
  inv_hom_id := congrArg Hom₂.nat e.inv_hom_id

/-- The (strict) morphism `Φ CatExp ⟶ FamOverExp` given by the identification of families of
types with formal coproducts of types. -/
noncomputable def famOverHom : Φobj.{w + 1, w + 2} CatExp.{w} ⟶ FamOverExp.{w} :=
  letI : FunctorPreserves (Φobj.{w + 1, w + 2} CatExp.{w}).arr (Over.mapIso famFC.{w}).inverse :=
    functorPreserves_of_adjunction (frobenius_equivalence (Over.mapIso famFC.{w}) _)
  { functor := (Over.mapIso famFC.{w}).inverse
    iso := Iso.refl _ }

section Main

variable {FinGat : ExpArrCat.{w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- `Γ ↦ (F_Γ / Fam ⥤ Fam)`, as a morphism `FinGat ⟶ FamOverExp`. -/
noncomputable abbrev cartCommaHom : FinGat ⟶ FamOverExp.{w} := famFunctor hFinGat ≫ toOverHom

/-- `Γ ↦ (M (T Γ) ⥤ Fam)`, as a morphism `FinGat ⟶ FamOverExp`. -/
noncomputable abbrev twoSortModelsHom : FinGat ⟶ FamOverExp.{w} :=
  twoSortification.{w + 1, w + 2} hFinGat ≫ Φmap.{w + 1, w + 2} (modelFunctor hFinGat) ≫ famOverHom

/-- The invertible 2-cell between the two morphisms, given by bi-initiality. -/
noncomputable def cartCommaIso : cartCommaHom hFinGat ≅ twoSortModelsHom hFinGat :=
  (hFinGat.nonempty_iso _ _).some

/-- The functor from the models of the two-sortification of `Γ` to families of types. -/
noncomputable abbrev twoSortModelsFam (Γ : FinGat.carrier) :
    modelCat hFinGat ((twoSortification.{w + 1, w + 2} hFinGat).functor.obj Γ).left ⟶ Cat.of Fam.{w} :=
  ((twoSortModelsHom hFinGat).functor.obj Γ).hom

lemma twoSortModelsFam_eq (Γ : FinGat.carrier) :
    twoSortModelsFam hFinGat Γ = (modelFunctor hFinGat).functor.map
      ((twoSortification.{w + 1, w + 2} hFinGat).functor.obj Γ).hom ≫ θ (modelFunctor hFinGat) ≫ famFC.inv :=
  rfl

/-- **Models of the two-sortification.** For a GAT `Γ`, the category of models of the
two-sortification `T Γ` of `Γ` is isomorphic to the cartesian comma category `F_Γ / Fam` of the
family functor `F_Γ : M Γ ⥤ Fam` of `Γ`. -/
noncomputable def modelsTwoSortIso (Γ : FinGat.carrier) :
    Cat.of (CartComma ((famFunctor hFinGat).functor.obj Γ)) ≅
      modelCat hFinGat ((twoSortification.{w + 1, w + 2} hFinGat).functor.obj Γ).left :=
  (Over.forget _).mapIso ((Hom₂.natIsoOfIso (cartCommaIso hFinGat)).app Γ)

/-- The isomorphism `modelsTwoSortIso` commutes with the projections to `Fam`. -/
theorem modelsTwoSortIso_hom_comp_proj (Γ : FinGat.carrier) :
    (modelsTwoSortIso hFinGat Γ).hom ≫ twoSortModelsFam hFinGat Γ =
      (CartComma.proj ((famFunctor hFinGat).functor.obj Γ)).toCatHom :=
  Over.w ((cartCommaIso hFinGat).hom.nat.app Γ)

/-- The isomorphism `modelsTwoSortIso` is natural in the GAT `Γ`. -/
theorem modelsTwoSortIso_natural {Γ Γ' : FinGat.carrier} (σ : Γ ⟶ Γ') :
    (CartComma.map ((famFunctor hFinGat).functor.map σ)).toCatHom ≫
        (modelsTwoSortIso hFinGat Γ').hom =
      (modelsTwoSortIso hFinGat Γ).hom ≫
        (modelFunctor hFinGat).functor.map ((twoSortification.{w + 1, w + 2} hFinGat).functor.map σ).left := by
  have h := congrArg CommaMorphism.left ((cartCommaIso hFinGat).hom.nat.naturality σ)
  erw [Over.comp_left, Over.comp_left] at h
  exact h

/-- The projection `(M, T, f) ↦ M` from `F_Γ / Fam` to the category of models of `Γ`. -/
noncomputable abbrev cartCommaFst (Γ : FinGat.carrier) :
    Cat.of (CartComma ((famFunctor hFinGat).functor.obj Γ)) ⟶ modelCat hFinGat Γ :=
  (CartComma.objFunctor ((famFunctor hFinGat).functor.obj Γ)).toCatHom

lemma famFunctor_iso_right : FamSlice.forget.map (famFunctor hFinGat).iso.hom.right =
    (modelFunctor hFinGat).iso.hom.right := by
  have h := (famFunctor₀Iso hFinGat).inv.right_comm
  simp only [Hom.comp_iso_hom_right, forgetHom_iso_hom_right] at h
  rw [← h]
  rfl

lemma famFunctor_iso_left : FamSlice.forget.map (famFunctor hFinGat).iso.hom.left =
    (modelFunctor hFinGat).iso.hom.left := by
  have h := (famFunctor₀Iso hFinGat).inv.left_comm
  simp only [Hom.comp_iso_hom_left, forgetHom_iso_hom_left] at h
  rw [← h]
  rfl

/-- The component at `X` of the core projection. -/
lemma core_cod : ((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ cartCommaFst hFinGat _ =
    (modelFunctor hFinGat).functor.map ((twoSortCounit.{w + 1, w + 2} hFinGat).app FinGat.cod) := by
  set φ := (famFunctor hFinGat).iso.hom.right
  have hK := congrArg CommaMorphism.left (cartCommaIso hFinGat).inv.right_comm
  erw [Over.comp_left] at hK
  have hK1 : ((cartCommaHom hFinGat).iso.hom.right).left =
      (CartComma.map φ).toCatHom ≫ rc.hom := rfl
  have hK2 : ((twoSortModelsHom hFinGat).iso.hom.right).left =
      (modelFunctor hFinGat).functor.map
        ((twoSortification.{w + 1, w + 2} hFinGat).iso.hom.right.left) ≫
        (ιX (modelFunctor hFinGat)).hom ≫ 𝟙 _ := rfl
  have he : rc.inv ≫ (CartComma.objFunctor SetObj.{w}).toCatHom = sE U.{w} := rfl
  rw [← cancel_mono (FamSlice.forget.map φ)]
  calc (((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ cartCommaFst hFinGat _) ≫
        FamSlice.forget.map φ
      = ((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ (CartComma.map φ).toCatHom ≫
          rc.hom ≫ rc.inv ≫ (CartComma.objFunctor SetObj.{w}).toCatHom := by
        rw [Iso.hom_inv_id_assoc]; rfl
    _ = ((twoSortModelsHom hFinGat).iso.hom.right).left ≫ sE U.{w} := by
        rw [← hK, hK1, ← he]; simp only [Category.assoc]
    _ = (modelFunctor hFinGat).functor.map
          ((twoSortification.{w + 1, w + 2} hFinGat).iso.hom.right.left) ≫
          (modelFunctor hFinGat).functor.map (sE FinGat.arr) ≫
          (modelFunctor hFinGat).iso.hom.right := by
        rw [hK2, Category.comp_id, Category.assoc]
        congr 1
        exact (ιX_eps (modelFunctor hFinGat)).symm
    _ = _ := by
        rw [twoSortCounit_app_cod, Functor.map_comp, Category.assoc, famFunctor_iso_right]

/-- The component at `Y` of the core projection. -/
lemma core_dom : ((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ cartCommaFst hFinGat _ =
    (modelFunctor hFinGat).functor.map ((twoSortCounit.{w + 1, w + 2} hFinGat).app FinGat.dom) := by
  set ψ := (famFunctor hFinGat).iso.hom.left
  have hK := congrArg CommaMorphism.left (cartCommaIso hFinGat).inv.left_comm
  erw [Over.comp_left] at hK
  have hK1 : ((cartCommaHom hFinGat).iso.hom.left).left =
      (CartComma.map ψ).toCatHom ≫ FamOverExpArr.isoL.{w}.hom.left := rfl
  have hK2 : ((twoSortModelsHom hFinGat).iso.hom.left).left =
      (modelFunctor hFinGat).functor.map
        ((twoSortification.{w + 1, w + 2} hFinGat).iso.hom.left.left) ≫
        (ιY (modelFunctor hFinGat)).hom ≫ 𝟙 _ := rfl
  have hkey : FamOverExpArr.isoL.{w}.hom.left ≫ pullback.fst U.{w} (sE U.{w}) =
      (CartComma.objFunctor PtObj.{w}).toCatHom := by
    have h1 : isoφ.hom ≫ pullback.fst U.{w} (sE U.{w}) =
        (K0p₁ FamOverExpArr.isoR.{w}.inv).left ≫ (CartComma.objFunctor PtObj.{w}).toCatHom :=
      (elChosen (sE U.{w})).isPullback.isoIsPullback_hom_fst _ _ (shpb U.{w})
    change ((inv (K0p₁ FamOverExpArr.isoR.{w}.inv)).left ≫ isoφ.hom) ≫ _ = _
    rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id]
    rfl
  rw [← cancel_mono (FamSlice.forget.map ψ)]
  calc (((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ cartCommaFst hFinGat _) ≫
        FamSlice.forget.map ψ
      = ((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ (CartComma.map ψ).toCatHom ≫
          (CartComma.objFunctor PtObj.{w}).toCatHom := rfl
    _ = ((twoSortModelsHom hFinGat).iso.hom.left).left ≫ pullback.fst U.{w} (sE U.{w}) := by
        rw [← hkey, ← hK, hK1]; simp only [Category.assoc]
    _ = (modelFunctor hFinGat).functor.map
          ((twoSortification.{w + 1, w + 2} hFinGat).iso.hom.left.left) ≫
          (modelFunctor hFinGat).functor.map (pullback.fst FinGat.arr (sE FinGat.arr)) ≫
          (modelFunctor hFinGat).iso.hom.left := by
        rw [hK2, Category.comp_id, Category.assoc]
        congr 1
        exact ιY_fst (modelFunctor hFinGat)
    _ = _ := by
        rw [twoSortCounit_app_dom, Functor.map_comp, Category.assoc, famFunctor_iso_left]

/-- **The core projection** `M (T Γ) ≅ F_Γ / Fam ⥤ M Γ`, as a natural transformation. -/
noncomputable def coreProjection :
    twoSortProj.{w + 1, w + 2} hFinGat ⋙ (modelFunctor hFinGat).functor ⟶ (modelFunctor hFinGat).functor where
  app Γ := (modelsTwoSortIso hFinGat Γ).inv ≫ cartCommaFst hFinGat Γ
  naturality Γ Γ' σ := by
    have h := congrArg CommaMorphism.left ((cartCommaIso hFinGat).inv.nat.naturality σ)
    change (modelFunctor hFinGat).functor.map ((twoSortProj.{w + 1, w + 2} hFinGat).map σ) ≫
        ((cartCommaIso hFinGat).inv.nat.app Γ').left ≫ cartCommaFst hFinGat Γ' =
      (((cartCommaIso hFinGat).inv.nat.app Γ).left ≫ cartCommaFst hFinGat Γ) ≫
        (modelFunctor hFinGat).functor.map σ
    have hF : FamSlice.forget.map ((famFunctor hFinGat).functor.map σ) =
        (modelFunctor hFinGat).functor.map σ := by
      simpa using CategoryTheory.Functor.congr_hom (famFunctorFun_forget hFinGat) σ
    have h' : (modelFunctor hFinGat).functor.map ((twoSortProj.{w + 1, w + 2} hFinGat).map σ) ≫
        ((cartCommaIso hFinGat).inv.nat.app Γ').left =
        ((cartCommaIso hFinGat).inv.nat.app Γ).left ≫
          (CartComma.map ((famFunctor hFinGat).functor.map σ)).toCatHom := by
      erw [Over.comp_left, Over.comp_left] at h
      exact h
    rw [← Category.assoc, h', Category.assoc, Category.assoc, ← hF]
    rfl

/-- **The core projection is the image of the counit.** The core projection, i.e. the
projection `F_Γ / Fam ⥤ M Γ` transported along `modelsTwoSortIso`, is the whiskering of
`twoSortCounit` by the model functor. -/
theorem coreProjection_eq :
    coreProjection hFinGat =
      Functor.whiskerRight (twoSortCounit.{w + 1, w + 2} hFinGat) (modelFunctor hFinGat).functor := by
  let α := Functor.whiskerRight (twoSortCounit.{w + 1, w + 2} hFinGat) (modelFunctor hFinGat).functor
  have hsq : IsPullback (α.app FinGat.dom)
      ((twoSortProj.{w + 1, w + 2} hFinGat ⋙ (modelFunctor hFinGat).functor).map FinGat.arr)
      ((modelFunctor hFinGat).functor.map FinGat.arr) (α.app FinGat.cod) := by
    have h₁ : α.app FinGat.dom = (modelFunctor hFinGat).functor.map
        (twoSortSquare.{w + 1, w + 2} hFinGat).left := by
      simp only [α, Functor.whiskerRight_app, twoSortCounit_app_dom, twoSortSquare_left]
    have h₂ : α.app FinGat.cod = (modelFunctor hFinGat).functor.map
        (twoSortSquare.{w + 1, w + 2} hFinGat).right := by
      simp only [α, Functor.whiskerRight_app, twoSortCounit_app_cod, twoSortSquare_right]
    rw [h₁, h₂]
    exact (modelFunctor hFinGat).functor.map_isPullback (twoSortSquare_isPullback hFinGat)
  obtain ⟨_, _, hu⟩ := IsBiInitial.existsUnique_natTrans_gen.{w + 1, w + 2} hFinGat
    (twoSortProj.{w + 1, w + 2} hFinGat ⋙ (modelFunctor hFinGat).functor) (modelFunctor hFinGat)
    (Arrow.homMk (α.app FinGat.dom) (α.app FinGat.cod) (α.naturality FinGat.arr).symm) hsq
  exact (hu (coreProjection hFinGat) ⟨core_dom hFinGat, core_cod hFinGat⟩).trans
    (hu α ⟨rfl, rfl⟩).symm

/-- **The projection corresponds to the counit.** Through the isomorphism `modelsTwoSortIso`,
the projection `F_Γ / Fam ⥤ M Γ` corresponds to the image under the model functor of the
component at `Γ` of `twoSortCounit`. -/
theorem modelsTwoSortIso_hom_comp_counit (Γ : FinGat.carrier) :
    (modelsTwoSortIso hFinGat Γ).hom ≫
        (modelFunctor hFinGat).functor.map ((twoSortCounit.{w + 1, w + 2} hFinGat).app Γ) =
      cartCommaFst hFinGat Γ := by
  have h := congrArg (fun α => (modelsTwoSortIso hFinGat Γ).hom ≫ NatTrans.app α Γ)
    (coreProjection_eq hFinGat)
  simp only [coreProjection, Iso.hom_inv_id_assoc, Functor.whiskerRight_app] at h
  exact h.symm

end Main

end ExpArrCat
