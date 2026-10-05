/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.TwoSortification
import CartexpAristotle.CompExp.ColaxSliceCartWidePullbacks
import CartexpAristotle.CharacterisationModelsTwoSort

/-!
# Models of the two-sortification, for `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.CoreProjectionMorphism`,
`CartexpAristotle.FamilyFunctor` and `CartexpAristotle.CharacterisationModelsTwoSort`.

Let `FinGat` be a bi-initial object of `CompExp`, `M` the model functor, `T` the
two-sortification functor and `F_Γ = familyFunctor Γ : M Γ ⥤ Fam` the family functor of an object
`Γ`, obtained from the bi-initial morphism `famFunctor : FinGat ⟶ ColaxSliceCartCompExp` into the
cartesian colax slice over `Fam`.

* The objects `ColaxSliceCartCompExp` (the cartesian colax slice, which has all `w`-small wide
  pullbacks, `ColaxSliceCart.hasWidePullbacks`) and `CatOverFamCompExp` (the slice of `Cat` over
  `Fam`), and the morphisms `forgetHomC`, `toOverHomC` and `famOverHomC` of `CompExp`, whose
  underlying objects and morphisms of `Lexp` are those of the `Lexp` development.
* `coreProjectionMorphism : T ⋙ Over.forget ⟶ 𝟭`: the core projection morphism.
* `famFunctor`: the family functor, lying over the model functor on the nose
  (`famFunctor_comp_forget`).
* `modelsTwoSortIso Γ` (Theorem "characterisation-models-two-sortification"): the category of
  models of the two-sortification of `Γ`, `M (T Γ)`, is isomorphic to the cartesian comma category
  `F_Γ / Fam`, compatibly with the projections to `Fam` (`modelsTwoSortIso_hom_comp_proj`) and
  naturally in `Γ` (`modelsTwoSortIso_natural`).
* `modelsTwoSortIso_hom_comp_coreProjectionMorphism` and `coreProjectionFunctor_eq`: through this
  isomorphism, the projection `F_Γ / Fam ⥤ M Γ` corresponds to the image under the model functor of
  the core projection morphism.

The proofs are those for `Lexp`, using bi-initiality in `CompExp` instead of `Lexp`: the four
objects of `CompExp` involved (`Φ FinGat`, `Cat`, the cartesian colax slice and the slice of `Cat`
over `Fam`) are complete, and the morphisms involved preserve wide pullbacks.

## References

* [Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`],
  [Paper, §5.2, Def. `def:core-projection-morphism`] and [Paper, §5.2, final Corollary], for
  `CompExp`.
-/

universe w

open CategoryTheory Limits ColaxSliceCart SemanticTwoSortFunctor ColaxSliceCartForget SliceExp
  PointedForget ColaxSliceCartExponentiable SemanticTwoSortFrobenius

namespace CompExp

/-! ### The objects and morphisms of `CompExp` -/

/-- `ColaxSliceCart` with the exponentiable arrow `UFam`, as an object of `CompExp`.

[Paper, §4.1, Thm. `thm:colax-exponentiable`] and [Paper, App. A.4, Prop.
`prop:colax-slice-limits`]: `CAT //_c Fam`, which is complete. -/
noncomputable def ColaxSliceCartCompExp : CompExp.{w, w + 1, w + 2} where
  toLexp := ColaxSliceCartLexp.{w}
  hasWidePullbacks := ColaxSliceCart.hasWidePullbacks.{w}

/-- The slice `Over (Cat.of Fam)` with the structure of `CatOverFamLexp`, as an object of
`CompExp`. -/
noncomputable def CatOverFamCompExp : CompExp.{w, w + 1, w + 2} where
  toLexp := CatOverFamLexp.{w}
  hasWidePullbacks J :=
    inferInstanceAs (HasLimitsOfShape (WidePullbackShape J) (Over (Cat.of Fam.{w})))

/-- The projection from the cartesian colax slice to `Cat`, as a morphism of `CompExp`. -/
noncomputable def forgetHomC : ColaxSliceCartCompExp.{w} ⟶ CatCompExp.{w} where
  toHom := forgetHom.{w}
  preservesWidePullbacks J := ColaxSliceCart.forget_preservesWidePullbacks J

/-- The functor `ColaxSliceCart.toOver`, as a morphism of `CompExp` (it preserves all limits, being
a right adjoint). -/
noncomputable def toOverHomC : ColaxSliceCartCompExp.{w} ⟶ CatOverFamCompExp.{w} where
  toHom := toOverHom.{w}
  preservesWidePullbacks J :=
    haveI : PreservesLimitsOfSize.{w, w} toOver.{w} := ofOverAdj.{w}.rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesLimitsOfShape (F := toOver.{w}) (J := WidePullbackShape J)

/-- The identification `Φ CatCompExp ⟶ CatOverFamCompExp`, as a morphism of `CompExp` (its functor
is an equivalence). -/
noncomputable def famOverHomC : Φobj.{w, w + 1, w + 2} CatCompExp.{w} ⟶ CatOverFamCompExp.{w} where
  toHom := Lexp.famOverHom.{w}
  preservesWidePullbacks J :=
    inferInstanceAs (PreservesLimitsOfShape (WidePullbackShape J) (Over.mapIso famFC.{w}).inverse)

variable {FinGat : CompExp.{w, w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The underlying morphism of `Lexp` of the two-sortification functor. -/
noncomputable abbrev Tw : FinGat.toLexp ⟶ Lexp.Φobj.{w + 1, w + 2} FinGat.toLexp :=
  (twoSortification.{w, w + 1, w + 2} hFinGat).toLexpHom

/-- The underlying morphism of `Lexp` of the model functor. -/
noncomputable abbrev Mf : FinGat.toLexp ⟶ CatLexp.{w} := (modelFunctor hFinGat).toLexpHom

/-! ### The core projection morphism -/

section CoreProjection

/-- The composite of the two-sortification functor `FinGat ⥤ Φ FinGat = FinGat / P X` with the
projection `FinGat / P X ⥤ FinGat`. -/
noncomputable abbrev twoSortProj : FinGat.carrier ⥤ FinGat.carrier :=
  (Tw hFinGat).functor ⋙ Over.forget (sZ FinGat.arr)

instance : PreservesLimitsOfShape WalkingCospan (twoSortProj hFinGat) := by
  haveI : PreservesLimitsOfShape WalkingCospan (Over.forget (sZ FinGat.arr)) :=
    Over.preservesLimitsOfShape_forget_of_isConnected
  exact comp_preservesLimitsOfShape _ _

/-- The square from the image of `p` under `twoSortProj` to `p`. -/
noncomputable def twoSortSquare :
    Arrow.mk ((twoSortProj hFinGat).map FinGat.arr) ⟶ Arrow.mk FinGat.arr :=
  Arrow.homMk ((Tw hFinGat).iso.hom.left.left ≫ (Lexp.ΦchosenSquare.{w + 1, w + 2} FinGat.toLexp).left)
    ((Tw hFinGat).iso.hom.right.left ≫ (Lexp.ΦchosenSquare.{w + 1, w + 2} FinGat.toLexp).right) (by
      have h := congrArg CommaMorphism.left (Tw hFinGat).iso.hom.w
      have h' := (Lexp.ΦchosenSquare.{w + 1, w + 2} FinGat.toLexp).w
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Functor.id_obj, Functor.id_map]
        at h h' ⊢
      erw [Over.comp_left, Over.comp_left] at h
      rw [Category.assoc, h', ← Category.assoc, ← Category.assoc]
      congr 1)

lemma twoSortSquare_left : (twoSortSquare hFinGat).left =
    (Tw hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr) := rfl

lemma twoSortSquare_right : (twoSortSquare hFinGat).right =
    (Tw hFinGat).iso.hom.right.left ≫ sE FinGat.arr := rfl

/-- The square `twoSortSquare` is a pullback square. -/
lemma twoSortSquare_isPullback :
    IsPullback (twoSortSquare hFinGat).left ((twoSortProj hFinGat).map FinGat.arr) FinGat.arr
      (twoSortSquare hFinGat).right := by
  let e := (Over.forget (sZ FinGat.arr)).mapArrow.mapIso (Tw hFinGat).iso
  have h₁ : IsPullback e.hom.left ((twoSortProj hFinGat).map FinGat.arr) (su' FinGat.arr)
      e.hom.right :=
    IsPullback.of_horiz_isIso ⟨e.hom.w⟩
  exact h₁.paste_horiz (shpb FinGat.arr)

/-- Existence and uniqueness of a natural transformation `twoSortProj ⟶ 𝟭 FinGat` extending the
square `twoSortSquare`. -/
theorem existsUnique_coreProjectionMorphism :
    ∃! α : twoSortProj hFinGat ⟶ (𝟙 FinGat.toLexp : FinGat.toLexp ⟶ FinGat.toLexp).functor,
      α.app FinGat.dom = (twoSortSquare hFinGat).left ∧
        α.app FinGat.cod = (twoSortSquare hFinGat).right :=
  IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat (𝟙 FinGat) (twoSortProj hFinGat)
    (twoSortSquare hFinGat) (twoSortSquare_isPullback hFinGat)

/-- **The core projection morphism** for `CompExp`: the natural transformation from the composite
of the two-sortification functor and the projection `Φ FinGat ⥤ FinGat` to the identity functor of
`FinGat`, extending the pullback square defining the chosen arrow of `Φ FinGat`.

[Paper, §5.2, Def. `def:core-projection-morphism`], for `CompExp`. -/
noncomputable def coreProjectionMorphism : twoSortProj hFinGat ⟶ 𝟭 FinGat.carrier :=
  (existsUnique_coreProjectionMorphism hFinGat).exists.choose

/-- The component of `coreProjectionMorphism` at `Y`. -/
theorem coreProjectionMorphism_app_dom : (coreProjectionMorphism hFinGat).app FinGat.dom =
    (Tw hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr) :=
  (existsUnique_coreProjectionMorphism hFinGat).exists.choose_spec.1

/-- The component of `coreProjectionMorphism` at `X`. -/
theorem coreProjectionMorphism_app_cod : (coreProjectionMorphism hFinGat).app FinGat.cod =
    (Tw hFinGat).iso.hom.right.left ≫ sE FinGat.arr :=
  (existsUnique_coreProjectionMorphism hFinGat).exists.choose_spec.2

/-- `coreProjectionMorphism` is the unique natural transformation with these components. -/
theorem coreProjectionMorphism_unique (α : twoSortProj hFinGat ⟶ 𝟭 FinGat.carrier)
    (hY : α.app FinGat.dom =
      (Tw hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr))
    (hX : α.app FinGat.cod = (Tw hFinGat).iso.hom.right.left ≫ sE FinGat.arr) :
    α = coreProjectionMorphism hFinGat :=
  (existsUnique_coreProjectionMorphism hFinGat).unique ⟨hY, hX⟩
    ⟨coreProjectionMorphism_app_dom hFinGat, coreProjectionMorphism_app_cod hFinGat⟩

end CoreProjection

/-! ### The family functor -/

section FamilyFunctor

/-- The chosen strict morphism from `FinGat` to the cartesian colax slice. -/
noncomputable abbrev famFunctor₀ : FinGat ⟶ ColaxSliceCartCompExp.{w} :=
  hFinGat.strictHom ColaxSliceCartCompExp

/-- The invertible 2-cell `famFunctor₀ ≫ forgetHom ≅ M` given by bi-initiality. -/
noncomputable def famFunctor₀Iso : (famFunctor₀ hFinGat).toLexpHom ≫ forgetHom ≅ Mf hFinGat :=
  Hom.isoToHom (hFinGat.nonempty_iso (famFunctor₀ hFinGat ≫ forgetHomC) (modelFunctor hFinGat)).some

/-- The natural isomorphism underlying `famFunctor₀Iso`. -/
noncomputable def famFunctor₀NatIso :
    (famFunctor₀ hFinGat).functor ⋙ ColaxSliceCart.forget ≅ (modelFunctor hFinGat).functor where
  hom := (famFunctor₀Iso hFinGat).hom.nat
  inv := (famFunctor₀Iso hFinGat).inv.nat
  hom_inv_id := congrArg Lexp.Hom₂.nat (famFunctor₀Iso hFinGat).hom_inv_id
  inv_hom_id := congrArg Lexp.Hom₂.nat (famFunctor₀Iso hFinGat).inv_hom_id

/-- The object part of `famFunctor`: `F₀(Γ)` transported to `M Γ`. -/
noncomputable def famFunctorObj (Γ : FinGat.carrier) : ColaxSliceCart.{w, w, w + 1} :=
  transportObj ((famFunctor₀ hFinGat).functor.obj Γ) ((famFunctor₀NatIso hFinGat).app Γ)

/-- The isomorphism `F₀(Γ) ≅ famFunctorObj Γ`. -/
noncomputable def famFunctorObjIso (Γ : FinGat.carrier) :
    (famFunctor₀ hFinGat).functor.obj Γ ≅ famFunctorObj hFinGat Γ :=
  transportIso _ ((famFunctor₀NatIso hFinGat).app Γ)

/-- The underlying functor of `famFunctor`. -/
noncomputable def famFunctorFun : FinGat.carrier ⥤ ColaxSliceCart.{w, w, w + 1} :=
  (famFunctor₀ hFinGat).functor.copyObj (famFunctorObj hFinGat) (famFunctorObjIso hFinGat)

/-- **The family functor** `FinGat ⟶ ColaxSliceCartCompExp`: the bi-initial morphism to the
cartesian colax slice over `Fam` that lies over the model functor on the nose.

[Paper, §4.1, Cor. `cor:family-functor-gat`], for `CompExp`. -/
noncomputable def famFunctor : FinGat ⟶ ColaxSliceCartCompExp.{w} where
  toHom := Lexp.Hom.ofNatIso (famFunctor₀ hFinGat).toLexpHom
    ((famFunctor₀ hFinGat).functor.isoCopyObj (famFunctorObj hFinGat) (famFunctorObjIso hFinGat))
  preservesWidePullbacks _ := preservesLimitsOfShape_of_natIso
    ((famFunctor₀ hFinGat).functor.isoCopyObj (famFunctorObj hFinGat) (famFunctorObjIso hFinGat))

/-- The category of models of `Γ`: its image under the model functor. -/
noncomputable abbrev modelCat (Γ : FinGat.carrier) : Cat.{w, w + 1} :=
  (modelFunctor hFinGat).functor.obj Γ

lemma famFunctor_functor : (famFunctor hFinGat).functor = famFunctorFun hFinGat := rfl

/-- **The family functor of `Γ`**: a functor from the category of models of `Γ` to the category
`Fam` of families of types.

[Paper, §4.1, Cor. `cor:family-functor-gat`], for `CompExp`. -/
noncomputable def familyFunctor (Γ : FinGat.carrier) : modelCat hFinGat Γ ⥤ Fam.{w} :=
  ((famFunctor hFinGat).functor.obj Γ).F

lemma famFunctor_obj (Γ : FinGat.carrier) :
    (famFunctor hFinGat).functor.obj Γ = ⟨modelCat hFinGat Γ, familyFunctor hFinGat Γ⟩ :=
  rfl

lemma famFunctorFun_forget :
    famFunctorFun hFinGat ⋙ ColaxSliceCart.forget = (modelFunctor hFinGat).functor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun Γ Γ' σ => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((famFunctor₀NatIso hFinGat).app Γ).inv ≫
      ColaxSliceCart.forget.map ((famFunctor₀ hFinGat).functor.map σ) ≫
      ((famFunctor₀NatIso hFinGat).app Γ').hom = _
  exact NatIso.naturality_1 (famFunctor₀NatIso hFinGat) σ

/-- The family functor lies over the model functor: its composite with the projection from the
cartesian colax slice to `Cat` is the model functor.

[Paper, §4.1, Cor. `cor:family-functor-gat`] and its proof, for `CompExp`. -/
theorem famFunctor_comp_forget : famFunctor hFinGat ≫ forgetHomC = modelFunctor hFinGat := by
  refine Hom.ext (Lexp.Hom.ext' (famFunctorFun_forget hFinGat) ?_ ?_)
  · have h := (famFunctor₀Iso hFinGat).inv.left_comm
    simp only [Lexp.Hom.comp_iso_hom_left, forgetHom_iso_hom_left] at h
    change ColaxSliceCart.forget.map (famFunctor hFinGat).iso.hom.left ≫ 𝟙 _ = _
    rw [eqToHom_refl, Category.id_comp, ← h]
    rfl
  · have h := (famFunctor₀Iso hFinGat).inv.right_comm
    simp only [Lexp.Hom.comp_iso_hom_right, forgetHom_iso_hom_right] at h
    change ColaxSliceCart.forget.map (famFunctor hFinGat).iso.hom.right ≫ 𝟙 _ = _
    rw [eqToHom_refl, Category.id_comp, ← h]
    rfl

/-- The family functor is isomorphic to any morphism `FinGat ⟶ ColaxSliceCartCompExp`. -/
theorem nonempty_iso_famFunctor (F : FinGat ⟶ ColaxSliceCartCompExp.{w}) :
    Nonempty (F ≅ famFunctor hFinGat) :=
  hFinGat.nonempty_iso _ _

end FamilyFunctor

/-! ### Models of the two-sortification -/

section Main

/-- `Γ ↦ (F_Γ / Fam ⥤ Fam)`, as a morphism `FinGat ⟶ CatOverFamCompExp`.

[Paper, §4.2, Cor. `cor:models-two-sortification-lax-slice-cart`], for `CompExp`. -/
noncomputable abbrev cartCommaHom : FinGat ⟶ CatOverFamCompExp.{w} :=
  famFunctor hFinGat ≫ toOverHomC

/-- `Γ ↦ (M (T Γ) ⥤ Fam)`, as a morphism `FinGat ⟶ CatOverFamCompExp`.

[Paper, §4.2, Cor. `cor:models-two-sortification-lexp-functor`], for `CompExp`. -/
noncomputable abbrev twoSortModelsHom : FinGat ⟶ CatOverFamCompExp.{w} :=
  twoSortification.{w, w + 1, w + 2} hFinGat ≫ Φmap.{w, w + 1, w + 2} (modelFunctor hFinGat) ≫
    famOverHomC

/-- The invertible 2-cell between the two morphisms, given by bi-initiality. -/
noncomputable def cartCommaIso :
    (cartCommaHom hFinGat).toLexpHom ≅ (twoSortModelsHom hFinGat).toLexpHom :=
  Hom.isoToHom (hFinGat.nonempty_iso _ _).some

/-- The functor from the models of the two-sortification of `Γ` to families of types. -/
noncomputable abbrev twoSortModelsFam (Γ : FinGat.carrier) :
    modelCat hFinGat ((Tw hFinGat).functor.obj Γ).left ⟶ Cat.of Fam.{w} :=
  ((twoSortModelsHom hFinGat).functor.obj Γ).hom

lemma twoSortModelsFam_eq (Γ : FinGat.carrier) :
    twoSortModelsFam hFinGat Γ = (modelFunctor hFinGat).functor.map
      ((Tw hFinGat).functor.obj Γ).hom ≫ Lexp.θ (Mf hFinGat) ≫ famFC.inv :=
  rfl

/-- **Models of the two-sortification.** For an object `Γ` of a bi-initial `FinGat` of
`CompExp`, the category of models of the two-sortification `T Γ` of `Γ` is isomorphic to the
cartesian comma category `F_Γ / Fam` of the family functor `F_Γ : M Γ ⥤ Fam` of `Γ`.

[Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`], for `CompExp`. -/
noncomputable def modelsTwoSortIso (Γ : FinGat.carrier) :
    Cat.of (CartComma ((famFunctor hFinGat).functor.obj Γ)) ≅
      modelCat hFinGat ((Tw hFinGat).functor.obj Γ).left :=
  (Over.forget _).mapIso ((Lexp.Hom₂.natIsoOfIso (cartCommaIso hFinGat)).app Γ)

/-- The isomorphism `modelsTwoSortIso` commutes with the projections to `Fam`.

[Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`]: compatibility with the
projections to `Fam`, for `CompExp`. -/
theorem modelsTwoSortIso_hom_comp_proj (Γ : FinGat.carrier) :
    (modelsTwoSortIso hFinGat Γ).hom ≫ twoSortModelsFam hFinGat Γ =
      (CartComma.proj ((famFunctor hFinGat).functor.obj Γ)).toCatHom :=
  Over.w ((cartCommaIso hFinGat).hom.nat.app Γ)

/-- The isomorphism `modelsTwoSortIso` is natural in `Γ`.

[Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`]: naturality in `Γ`, for
`CompExp`. -/
theorem modelsTwoSortIso_natural {Γ Γ' : FinGat.carrier} (σ : Γ ⟶ Γ') :
    (CartComma.map ((famFunctor hFinGat).functor.map σ)).toCatHom ≫
        (modelsTwoSortIso hFinGat Γ').hom =
      (modelsTwoSortIso hFinGat Γ).hom ≫
        (modelFunctor hFinGat).functor.map ((Tw hFinGat).functor.map σ).left := by
  have h := congrArg CommaMorphism.left ((cartCommaIso hFinGat).hom.nat.naturality σ)
  erw [Over.comp_left, Over.comp_left] at h
  exact h

/-- The projection `(M, T, f) ↦ M` from `F_Γ / Fam` to the category of models of `Γ`.

[Paper, §5]: the projection `F_Γ/_c Fam → Mod(Γ)`. -/
noncomputable abbrev cartCommaFst (Γ : FinGat.carrier) :
    Cat.of (CartComma ((famFunctor hFinGat).functor.obj Γ)) ⟶ modelCat hFinGat Γ :=
  (CartComma.objFunctor ((famFunctor hFinGat).functor.obj Γ)).toCatHom

lemma famFunctor_iso_right : ColaxSliceCart.forget.map (famFunctor hFinGat).iso.hom.right =
    (modelFunctor hFinGat).iso.hom.right := by
  have h := (famFunctor₀Iso hFinGat).inv.right_comm
  simp only [Lexp.Hom.comp_iso_hom_right, forgetHom_iso_hom_right] at h
  rw [← h]
  rfl

lemma famFunctor_iso_left : ColaxSliceCart.forget.map (famFunctor hFinGat).iso.hom.left =
    (modelFunctor hFinGat).iso.hom.left := by
  have h := (famFunctor₀Iso hFinGat).inv.left_comm
  simp only [Lexp.Hom.comp_iso_hom_left, forgetHom_iso_hom_left] at h
  rw [← h]
  rfl

/-- The component at `X` of the core projection. -/
lemma core_cod : ((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ cartCommaFst hFinGat _ =
    (modelFunctor hFinGat).functor.map ((coreProjectionMorphism hFinGat).app FinGat.cod) := by
  set φ := (famFunctor hFinGat).iso.hom.right
  have hK := congrArg CommaMorphism.left (cartCommaIso hFinGat).inv.right_comm
  erw [Over.comp_left] at hK
  have hK1 : ((cartCommaHom hFinGat).iso.hom.right).left =
      (CartComma.map φ).toCatHom ≫ rc.hom := rfl
  have hK2 : ((twoSortModelsHom hFinGat).iso.hom.right).left =
      (modelFunctor hFinGat).functor.map
        ((Tw hFinGat).iso.hom.right.left) ≫
        (Lexp.ιX (Mf hFinGat)).hom ≫ 𝟙 _ := rfl
  have he : rc.inv ≫ (CartComma.objFunctor SetObj.{w}).toCatHom = sE U.{w} := rfl
  rw [← cancel_mono (ColaxSliceCart.forget.map φ)]
  calc (((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ cartCommaFst hFinGat _) ≫
        ColaxSliceCart.forget.map φ
      = ((cartCommaIso hFinGat).inv.nat.app FinGat.cod).left ≫ (CartComma.map φ).toCatHom ≫
          rc.hom ≫ rc.inv ≫ (CartComma.objFunctor SetObj.{w}).toCatHom := by
        rw [Iso.hom_inv_id_assoc]; rfl
    _ = ((twoSortModelsHom hFinGat).iso.hom.right).left ≫ sE U.{w} := by
        rw [← hK, hK1, ← he]; simp only [Category.assoc]
    _ = (modelFunctor hFinGat).functor.map
          ((Tw hFinGat).iso.hom.right.left) ≫
          (modelFunctor hFinGat).functor.map (sE FinGat.arr) ≫
          (modelFunctor hFinGat).iso.hom.right := by
        rw [hK2, Category.comp_id, Category.assoc]
        congr 1
        exact (Lexp.ιX_eps (Mf hFinGat)).symm
    _ = _ := by
        rw [coreProjectionMorphism_app_cod, Functor.map_comp, Category.assoc,
          famFunctor_iso_right]

/-- The component at `Y` of the core projection. -/
lemma core_dom : ((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ cartCommaFst hFinGat _ =
    (modelFunctor hFinGat).functor.map ((coreProjectionMorphism hFinGat).app FinGat.dom) := by
  set ψ := (famFunctor hFinGat).iso.hom.left
  have hK := congrArg CommaMorphism.left (cartCommaIso hFinGat).inv.left_comm
  erw [Over.comp_left] at hK
  have hK1 : ((cartCommaHom hFinGat).iso.hom.left).left =
      (CartComma.map ψ).toCatHom ≫ SemanticTwoSortFunctor.isoL.{w}.hom.left := rfl
  have hK2 : ((twoSortModelsHom hFinGat).iso.hom.left).left =
      (modelFunctor hFinGat).functor.map
        ((Tw hFinGat).iso.hom.left.left) ≫
        (Lexp.ιY (Mf hFinGat)).hom ≫ 𝟙 _ := rfl
  have hkey : SemanticTwoSortFunctor.isoL.{w}.hom.left ≫ pullback.fst U.{w} (sE U.{w}) =
      (CartComma.objFunctor PtObj.{w}).toCatHom := by
    have h1 : isoφ.hom ≫ pullback.fst U.{w} (sE U.{w}) =
        (K0p₁ SemanticTwoSortFunctor.isoR.{w}.inv).left ≫
          (CartComma.objFunctor PtObj.{w}).toCatHom :=
      (elChosen (sE U.{w})).isPullback.isoIsPullback_hom_fst _ _ (shpb U.{w})
    change ((inv (K0p₁ SemanticTwoSortFunctor.isoR.{w}.inv)).left ≫ isoφ.hom) ≫ _ = _
    rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id]
    rfl
  rw [← cancel_mono (ColaxSliceCart.forget.map ψ)]
  calc (((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ cartCommaFst hFinGat _) ≫
        ColaxSliceCart.forget.map ψ
      = ((cartCommaIso hFinGat).inv.nat.app FinGat.dom).left ≫ (CartComma.map ψ).toCatHom ≫
          (CartComma.objFunctor PtObj.{w}).toCatHom := rfl
    _ = ((twoSortModelsHom hFinGat).iso.hom.left).left ≫ pullback.fst U.{w} (sE U.{w}) := by
        rw [← hkey, ← hK, hK1]; simp only [Category.assoc]
    _ = (modelFunctor hFinGat).functor.map
          ((Tw hFinGat).iso.hom.left.left) ≫
          (modelFunctor hFinGat).functor.map (pullback.fst FinGat.arr (sE FinGat.arr)) ≫
          (modelFunctor hFinGat).iso.hom.left := by
        rw [hK2, Category.comp_id, Category.assoc]
        congr 1
        exact Lexp.ιY_fst (Mf hFinGat)
    _ = _ := by
        rw [coreProjectionMorphism_app_dom, Functor.map_comp, Category.assoc,
          famFunctor_iso_left]

/-- **The core projection** `M (T Γ) ≅ F_Γ / Fam ⥤ M Γ`, as a natural transformation.

[Paper, §5]: the core projection functors `β_Γ`, for `CompExp`. -/
noncomputable def coreProjectionFunctor :
    twoSortProj hFinGat ⋙ (modelFunctor hFinGat).functor ⟶ (modelFunctor hFinGat).functor where
  app Γ := (modelsTwoSortIso hFinGat Γ).inv ≫ cartCommaFst hFinGat Γ
  naturality Γ Γ' σ := by
    have h := congrArg CommaMorphism.left ((cartCommaIso hFinGat).inv.nat.naturality σ)
    change (modelFunctor hFinGat).functor.map ((twoSortProj hFinGat).map σ) ≫
        ((cartCommaIso hFinGat).inv.nat.app Γ').left ≫ cartCommaFst hFinGat Γ' =
      (((cartCommaIso hFinGat).inv.nat.app Γ).left ≫ cartCommaFst hFinGat Γ) ≫
        (modelFunctor hFinGat).functor.map σ
    have hF : ColaxSliceCart.forget.map ((famFunctor hFinGat).functor.map σ) =
        (modelFunctor hFinGat).functor.map σ := by
      simpa using CategoryTheory.Functor.congr_hom (famFunctorFun_forget hFinGat) σ
    have h' : (modelFunctor hFinGat).functor.map ((twoSortProj hFinGat).map σ) ≫
        ((cartCommaIso hFinGat).inv.nat.app Γ').left =
        ((cartCommaIso hFinGat).inv.nat.app Γ).left ≫
          (CartComma.map ((famFunctor hFinGat).functor.map σ)).toCatHom := by
      erw [Over.comp_left, Over.comp_left] at h
      exact h
    rw [← Category.assoc, h', Category.assoc, Category.assoc, ← hF]
    rfl

/-- **The core projection functor is the image of the core projection morphism**, for `CompExp`.

[Paper, §5.2, final Corollary]: `α = β`, for `CompExp`. -/
theorem coreProjectionFunctor_eq :
    coreProjectionFunctor hFinGat =
      Functor.whiskerRight (coreProjectionMorphism hFinGat) (modelFunctor hFinGat).functor := by
  let α := Functor.whiskerRight (coreProjectionMorphism hFinGat) (modelFunctor hFinGat).functor
  have hsq : IsPullback (α.app FinGat.dom)
      ((twoSortProj hFinGat ⋙ (modelFunctor hFinGat).functor).map FinGat.arr)
      ((modelFunctor hFinGat).functor.map FinGat.arr) (α.app FinGat.cod) := by
    have h₁ : α.app FinGat.dom = (modelFunctor hFinGat).functor.map
        (twoSortSquare hFinGat).left := by
      simp only [α, Functor.whiskerRight_app, coreProjectionMorphism_app_dom, twoSortSquare_left]
    have h₂ : α.app FinGat.cod = (modelFunctor hFinGat).functor.map
        (twoSortSquare hFinGat).right := by
      simp only [α, Functor.whiskerRight_app, coreProjectionMorphism_app_cod, twoSortSquare_right]
    rw [h₁, h₂]
    exact (modelFunctor hFinGat).functor.map_isPullback (twoSortSquare_isPullback hFinGat)
  obtain ⟨_, _, hu⟩ := IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat
    (modelFunctor hFinGat) (twoSortProj hFinGat ⋙ (modelFunctor hFinGat).functor)
    (Arrow.homMk (α.app FinGat.dom) (α.app FinGat.cod) (α.naturality FinGat.arr).symm) hsq
  exact (hu (coreProjectionFunctor hFinGat) ⟨core_dom hFinGat, core_cod hFinGat⟩).trans
    (hu α ⟨rfl, rfl⟩).symm

/-- **The projection corresponds to the core projection morphism**, for `CompExp`: through the
isomorphism `modelsTwoSortIso`, the projection `F_Γ / Fam ⥤ M Γ` corresponds to the image under
the model functor of the component at `Γ` of `coreProjectionMorphism`.

[Paper, §5.2, final Corollary], for `CompExp`. -/
theorem modelsTwoSortIso_hom_comp_coreProjectionMorphism (Γ : FinGat.carrier) :
    (modelsTwoSortIso hFinGat Γ).hom ≫
        (modelFunctor hFinGat).functor.map ((coreProjectionMorphism hFinGat).app Γ) =
      cartCommaFst hFinGat Γ := by
  have h := congrArg (fun α => (modelsTwoSortIso hFinGat Γ).hom ≫ NatTrans.app α Γ)
    (coreProjectionFunctor_eq hFinGat)
  simp only [coreProjectionFunctor, Iso.hom_inv_id_assoc, Functor.whiskerRight_app] at h
  exact h.symm

end Main

end CompExp
