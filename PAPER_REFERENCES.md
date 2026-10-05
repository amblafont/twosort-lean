# Correspondence between the paper and the Lean development

Paper: *For Generalised Algebraic Theories, Two Sorts Are Enough* (`s_csl.tex`, appendices
`s-appendices_csl.tex`). Results are identified by section and by their LaTeX `\label`. In the Lean
docstrings they are cited as `[Paper, §n, Kind `label`]`.

All Lean names below are in the namespace `Lexp` unless they are written with an explicit namespace.
`FinGat` is an arbitrary bi-initial object of `Lexp` (`hFinGat : IsBiInitial FinGat`), so every
result holds for the category of finite GATs by Uemura's theorem (Thm. `thm:uemura`), which is not
itself formalised.

## Naming

| Paper | Lean |
|---|---|
| 2-category \(\mathbf{Lexp}\), \(\Lexp\)-category, \(\Lexp\)-functor | `Lexp`, `Lexp.Hom` |
| exponentiable morphism, \(P_f\) | `IsExpArr`, `Data` / `Universal` |
| preserves pushforwards | `FunctorPreserves` |
| strict \(\Lexp\)-functor | `Lexp.Hom.IsStrict` |
| \(\CAT\) with \(\PtdSet \to \mathbf{Set}\) | `CatLexp` (arrow `PointedForget.U`) |
| \(\FamS = \mathrm{Fam}(\mathbf{Set})\) | `Fam` |
| cartesian colax slice \(\CAT /\!/_c \FamS\) | `ColaxSliceCart`, as a \(\Lexp\)-category `ColaxSliceCartLexp` |
| \(\CAT/\FamS\) as a \(\Lexp\)-category | `CatOverFamLexp` |
| endofunctor \(- / PX\) of \(\Lexp\) | `Φ` |
| model functor \(\mathcal M\) | `modelFunctor`, `modelCat Γ` |
| two-sortification \(T\) | `twoSortification` |
| family functor \(F\), \(F_Γ\) | `famFunctor`, `familyFunctor Γ` |
| \(F_Γ/_c\FamS\) | `ColaxSliceCart.CartComma (familyFunctor Γ)` |
| core projection morphism \(\mathrm{coref}_Γ\) | `coreProjectionMorphism` |
| core projection functor | `cartCommaFst`, `coreProjectionFunctor` |
| \(\mathrm{Tm}(A)\), \(0_Ω\), \(i : 0_Ω \to ω\) | `InitialModel.Tm`, `InitialModel.zero`, `InitialModel.toModel` |
| \(\mathrm{Tm}_Ω\), \(\M{Ω}\) | `TwoSortFF.TmFam`, `TwoSortFF.MOmega` |

## Main text

| Paper | Lean | File |
|---|---|---|
| §2.1 Def. `def:exp-mor`, Prop. `prop:exp-mor-P-def` | `IsExpArr` (defined directly through \(P_f\)) | `PartialExponentiability.lean` |
| §2.1 Def. `def:preserves-pushforwards`, Lemma `lem:preservation_pushforward` | `FunctorPreserves` (the form of the lemma) | `PartialExponentiability.lean` |
| §2.2 Thm. `thm:uemura` (definition of \(\Lexp\)) | `Lexp`, `Lexp.Hom`, `Lexp.Hom₂` | `Lexp.lean` |
| §2.2 bi-initiality | `Lexp.IsBiInitial` | `UniversalNatTrans.lean` |
| §2.2 Prop. `prop:strictification` | `Hom.IsStrict`, `strictify`, `exists_strict_iso`, `IsBiInitial.dom_ne_cod`, `IsBiInitial.exists_strict_hom`, `IsBiInitial.strictHom` | `Strictification.lean`, `BiInitialDomCod.lean`, `TwoSortification.lean` |
| §2.2 Prop. `prop:CAT` | `CatLexp`, `PointedForget.expData`, `PointedForget.expUniversal`, `CatPullbacks.isLimit` | `CatExponentiable.lean`, `CatPullbacks.lean`, `SemanticTwoSortFunctor.lean` |
| §2.2 Def. of the model functor | `modelFunctor` | `TwoSortification.lean` |
| §2.2 Thm. `thm:universal-property-natural-transformation` | `IsBiInitial.existsUnique_natTrans` (and `_gen`, `_iso`) | `UniversalNatTrans.lean` |
| §3.1 Prop. (\(\FinGat/\FamG\) is a Lex-category) | Mathlib instances on `Over` | — |
| §3.1 Prop. `prop:p2-construction` | `SliceExp.sZ`, `sE`, `sW`, `su'` | `SliceExponentiable.lean` |
| §3.1 Prop. `prop:p2-exponentiable` | `SliceExp.sIsExpArr`, `Φobj` | `SliceExponentiable.lean`, `LexpEndofunctor.lean` |
| §3.1 Def. `def:two-sortification` | `twoSortification` | `TwoSortification.lean` |
| §3.2 family GATs, Prop. `prop:family-gats` | not formalised | — |
| §4 Example `ex:main-thms` | `ColaxSliceCartExponentiable.setFam`, `ptFam` | `ColaxSliceCartExponentiable.lean` |
| §4.1 Def. of \(\CAT /\!/_c \FamS\) | `ColaxSliceCart` | `ColaxSliceCart.lean` |
| §4.1 Thm. `thm:colax-exponentiable` | `ColaxSliceCart.isTerminal`, `pullbackConeIsLimit`, `UFam`, `ColaxSliceCartExponentiable.expUniversal`, `ColaxSliceCartForget.forgetHom`, `ColaxSliceCartLexp` | `ColaxSliceCartLimits.lean`, `ColaxSliceCartExponentiable.lean`, `ColaxSliceCartForget.lean` |
| §4.1 Cor. `cor:family-functor-gat` | `famFunctor`, `famFunctor_comp_forget`, `familyFunctor` | `FamilyFunctor.lean` |
| §4.2 Thm. `thm:characterisation-models-two-sortification` | `modelsTwoSortIso`, `modelsTwoSortIso_hom_comp_proj`, `modelsTwoSortIso_natural` | `CharacterisationModelsTwoSort.lean` |
| §4.2 Prop. `prop:lexp-functor-p2` | `Φ`, `θ`, `SliceExp.sliceMap` | `LexpEndofunctor.lean`, `LexpTheta.lean`, `SliceFunctor.lean` |
| §4.2 Cor. `cor:models-two-sortification-lexp-functor` | `twoSortModelsHom` | `CharacterisationModelsTwoSort.lean` |
| §4.2 Prop. `prop:semantic-twosort-functor` | `ColaxSliceCart.toOver`, `toOverHom` | `ColaxSliceCartToOver.lean`, `SemanticTwoSortFunctor.lean` |
| §4.2 Cor. `cor:models-two-sortification-lax-slice-cart` | `cartCommaHom` | `CharacterisationModelsTwoSort.lean` |
| §5 core projection functor | `cartCommaFst`, `coreProjectionFunctor` | `CharacterisationModelsTwoSort.lean` |
| §5.1 Prop. `prop:core_projection_preserves_initial` | not formalised | — |
| §5.2 Def. `def:core-projection-morphism` | `coreProjectionMorphism`, `coreProjectionMorphism_unique` | `CoreProjectionMorphism.lean` |
| §5.2 Example `ex:core-projection-simple-gats` | `coreProjectionMorphism_app_cod`, `coreProjectionMorphism_app_dom` | `CoreProjectionMorphism.lean` |
| §5.2 final Proposition and Corollary (\(α = β\)) | `coreProjectionFunctor_eq`, `modelsTwoSortIso_hom_comp_coreProjectionMorphism` | `CharacterisationModelsTwoSort.lean` |

## Appendices

| Paper | Lean | File |
|---|---|---|
| App. A.1 Prop. `prop:p2-description-polynomial` | `SliceExp.sOverData` | `SliceExponentiable.lean` |
| App. A.2 (proof of Prop. `prop:family-gats`) | not formalised | — |
| App. A.3 Prop. `prop:comma-lexp` | `Lexp.comma` | `CommaLexp.lean` |
| App. A.3 proof of Thm. `thm:universal-property-natural-transformation` | `natTrans_exists`, `natTrans_unique` | `UniversalNatTrans.lean` |
| App. A.4 Props. `prop:colax-slice-limits`, `prop:cartesian-colax-lexp` | `ColaxSliceCart.isTerminal`, `pullbackConeIsLimit` (directly for the cartesian colax slice) | `ColaxSliceCartLimits.lean` |
| App. A.4 proof of Prop. `prop:semantic-twosort-functor` | `ColaxSliceCart.ofOverAdj`, `functorPreserves_of_adjunction`, `frobenius_UFam` | `ColaxSliceCartAdjunction.lean`, `AdjointExp.lean`, `SemanticTwoSortFrobenius.lean` |
| App. B Notation `not:mor-terms-set` | `InitialModel.Tm` | `InitialModel.lean` |
| App. B Lemma `lem:model-term-natural` | `InitialModel.el_theta` | `InitialModelUnique.lean` |
| App. B Prop. `prop:initial-model-gat-existence` | `InitialModel.alpha`, `InitialModel.zero` | `InitialModel.lean` |
| App. B Prop. `prop:arrow-functor-lexp` | not needed (replaced by collages) | `Collage.lean` |
| App. B Prop. `prop:initial-model-gat-morphism-existence` | `InitialModel.toModel` | `InitialModelMorphisms.lean` |
| App. B Lemma after it | `InitialModel.hom_eq_toModel` | `InitialModelUnique.lean` |
| App. B Cor. `cor:initial-model-gat` | `InitialModel.isInitialZero`, `modelFunctor_hasInitial` | `InitialModelUnique.lean`, `InitialModelGat.lean` |
| App. C Prop. `prop:faithful-at-XGAT-YGAT` | `IsBiInitial.induction`, `TwoSortBij`, `twoSortBij_all` | `BiInitialInduction.lean`, `TwoSortificationFullyFaithful.lean`, `TwoSortFFMain.lean` |
| App. C Cor. `cor:faithful-via-terms` | not used | — |
| App. C.1 Prop. `prop:model-faithful` | `TwoSortFF.MOmega`, `famF_MOmega`, `isoX_MOmega`, `gY_MOmega` | `TwoSortFFGamma.lean` |
| App. C.1 Cor. `cor:two-sortification-faithful` | `twoSort_faithful_cod`, `twoSort_faithful_dom`, `twoSortification_faithful` | `TwoSortFFMain.lean` |
| App. C.2 Prop. `prop:two-sortification-terms-isomorphic` | not used | — |
| App. C.2 Prop. `prop:initial-object-two-sortification`, App. C.3 Prop. `prop:initial-value-fam` | only the consequence `Rd_zero_injective`, `Qd_zero_injective` | `TwoSortFFReadout.lean` |
| App. C.2 Prop. `prop:section-terms-two-sortification` | `twoSort_full_cod`, `twoSort_full_dom` (via `jHom`) | `TwoSortFFMain.lean`, `TwoSortFFGamma.lean` |
| App. C.2 final Corollary (\(T\) fully faithful) | `twoSortification_full`, `twoSortificationFullyFaithful` | `TwoSortFFMain.lean` |
| App. D, Thm. `thm:infinite-GATs` (infinite GATs) | `InfiniteGat.gatCat_isBiInitial` | `CartexpAristotle/InfiniteGat/Main.lean` |

For the places where the Lean proofs differ from the paper, see `INITIALITY_PROOF_COMPARISON.md`
and `FULL_FAITHFULNESS_PROOF_COMPARISON.md`.

## Auxiliary files not from the paper

| Lean | File | Why |
|---|---|---|
| `CategoryTheory.Limits.ChosenPullback` | `ChosenPullback.lean` | local stand-in for the Mathlib structure of the same name, which the pinned Mathlib lacks |
| `CategoryTheory.Comma.fstSndJointlyReflectLimit` | `UniversalNatTrans.lean` | the projections of a comma category jointly reflect limits; missing from the pinned Mathlib, proved locally with the extra assumption that the right-hand functor preserves the relevant limit (it is the identity at the only use) |

## Renamings

Files and declarations were renamed to follow the paper. Former names:

| Former name | New name |
|---|---|
| `ExpArrCat` (structure and namespace), `ExpArrCat.lean` | `Lexp`, `Lexp.lean` |
| `CatExp` | `CatLexp` |
| `FamSlice` (and `FamSlice*` namespaces/files) | `ColaxSliceCart` (and `ColaxSliceCart*`) |
| `FamSliceExp` | `ColaxSliceCartLexp` |
| `FamOverExp` | `CatOverFamLexp` |
| `FamPointedForget` (namespace), `FamPointedForget.lean` | `ColaxSliceCartExponentiable` |
| `FamOverExpArr` (namespace), `FamOverExpArr.lean` | `SemanticTwoSortFunctor` |
| `FamOverFrobenius` (namespace), `FamOverFrobenius.lean` | `SemanticTwoSortFrobenius` |
| `ExpArrEndofunctor.lean`, `ExpArrTheta.lean`, `CommaExpArr.lean` | `LexpEndofunctor.lean`, `LexpTheta.lean`, `CommaLexp.lean` |
| `FinGAT.lean` | `UniversalNatTrans.lean` |
| `PointedForget.lean` (namespace `PointedForget` unchanged) | `CatExponentiable.lean` |
| `StrictHom.lean` | `Strictification.lean` |
| `ModelInitial.lean` | `InitialModelGat.lean` |
| `TwoSortModels.lean` | `CharacterisationModelsTwoSort.lean` |
| `TwoSortificationCounit.lean`, `twoSortCounit*` | `CoreProjectionMorphism.lean`, `coreProjectionMorphism*` |
| `coreProjection`, `coreProjection_eq` | `coreProjectionFunctor`, `coreProjectionFunctor_eq` |
| `modelsTwoSortIso_hom_comp_counit` | `modelsTwoSortIso_hom_comp_coreProjectionMorphism` |
| `TwoSortFF.NM` (and `*_NM` lemmas) | `TwoSortFF.MOmega` (and `*_MOmega`) |
