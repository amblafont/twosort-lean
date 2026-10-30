-- This module serves as the root of the `CartexpAristotle` library.
-- Import modules here that should be built as part of the library.
import CartexpAristotle.AdjointExp
import CartexpAristotle.Basic
import CartexpAristotle.BiInitialDomCod
import CartexpAristotle.BiInitialInduction
import CartexpAristotle.CatPullbacks
import CartexpAristotle.CommaLexp
import CartexpAristotle.Lexp
import CartexpAristotle.LexpEndofunctor
import CartexpAristotle.LexpTheta
import CartexpAristotle.SemanticTwoSortFunctor
import CartexpAristotle.SemanticTwoSortFrobenius
import CartexpAristotle.ColaxSliceCartExponentiable
import CartexpAristotle.ColaxSliceCart
import CartexpAristotle.ColaxSliceCartAdjunction
import CartexpAristotle.ColaxSliceCartLimits
import CartexpAristotle.ColaxSliceCartToOver
import CartexpAristotle.UniversalNatTrans
import CartexpAristotle.PartialExponentiability
import CartexpAristotle.CatExponentiable
import CartexpAristotle.SliceExponentiable
import CartexpAristotle.SliceFunctor
import CartexpAristotle.Strictification
import CartexpAristotle.TwoSortification
import CartexpAristotle.FamilyGat
import CartexpAristotle.CoreProjectionMorphism
import CartexpAristotle.TwoSortificationFullyFaithful
import CartexpAristotle.Collage
import CartexpAristotle.CatPullbackCriterion
import CartexpAristotle.PointifyPullback
import CartexpAristotle.InitialModel
import CartexpAristotle.InitialModelMorphisms
import CartexpAristotle.InitialModelUnique
import CartexpAristotle.InitialModelGat
import CartexpAristotle.TwoSortFFSetup
import CartexpAristotle.TwoSortFFCollage
import CartexpAristotle.TwoSortFFSquare
import CartexpAristotle.TwoSortFFGamma
import CartexpAristotle.TwoSortFFReadout
import CartexpAristotle.TwoSortFFMain
import CartexpAristotle.ColaxSliceCartForget
import CartexpAristotle.FamilyFunctor
import CartexpAristotle.CharacterisationModelsTwoSort
import CartexpAristotle.CompExp.Basic
import CartexpAristotle.CompExp.UniversalNatTrans
import CartexpAristotle.CompExp.Strictification
import CartexpAristotle.CompExp.CatWidePullbacks
import CartexpAristotle.CompExp.TwoSortification
import CartexpAristotle.CompExp.InitialModel
import CartexpAristotle.CompExp.BiInitialInduction
import CartexpAristotle.CompExp.TwoSortificationFullyFaithful
import CartexpAristotle.CompExp.ColaxSliceCartWidePullbacks
import CartexpAristotle.CompExp.CharacterisationModelsTwoSort
import CartexpAristotle.InfiniteGat.Pro
import CartexpAristotle.InfiniteGat.ProExtension
import CartexpAristotle.InfiniteGat.ExpData
import CartexpAristotle.InfiniteGat.ProExponentiable
import CartexpAristotle.InfiniteGat.ProExtendExp
import CartexpAristotle.InfiniteGat.Limits
import CartexpAristotle.InfiniteGat.Main

/-!
# For Generalised Algebraic Theories, Two Sorts Are Enough

This library formalises results of the paper *For Generalised Algebraic Theories, Two Sorts Are
Enough* (main text `s_csl.tex`, appendices `s-appendices_csl.tex`).

## Citation convention

Docstrings cite the paper as `[Paper, §n, Kind `label`]`, where `§n` is the section (`§A`–`§D`
for the appendices) and `label` is the LaTeX `\label` of the result in the sources, e.g.
`[Paper, §2.2, Thm. `thm:uemura`]`. Results without a label are named by their position
(e.g. "final Corollary of §5.2"). `PAPER_REFERENCES.md` gives the full table from the paper to
the Lean declarations.

## Correspondence between the paper and the files

* §2.1 Exponentiable morphisms: `PartialExponentiability`, `ChosenPullback`.
* §2.2 GATs: `Lexp` (the 2-category `Lexp` of Thm. `thm:uemura`), `UniversalNatTrans`
  (bi-initiality and Thm. `thm:universal-property-natural-transformation`), `CommaLexp`
  (App. A.3, Prop. `prop:comma-lexp`), `Strictification` and `BiInitialDomCod`
  (Prop. `prop:strictification`), `CatPullbacks` and `CatExponentiable` (Prop. `prop:CAT`),
  `TwoSortification` (the model functor).
* §3.1 Two-sortification: `SliceExponentiable` (Props. `prop:p2-construction`,
  `prop:p2-exponentiable`), `TwoSortification` (Def. `def:two-sortification`).
* §3.2 Soundness (family GATs): `FamilyGat` (Def. of family GATs, Prop. `prop:family-gats` and
  App. A.2, soundness Corollary).
* §4.1 The family functor: `ColaxSliceCart`, `ColaxSliceCartLimits`,
  `ColaxSliceCartExponentiable`, `ColaxSliceCartForget` (Thm. `thm:colax-exponentiable`),
  `FamilyFunctor` (Cor. `cor:family-functor-gat`).
* §4.2 Models of the two-sortification: `LexpTheta`, `SliceFunctor`, `LexpEndofunctor`
  (Prop. `prop:lexp-functor-p2`), `ColaxSliceCartToOver`, `ColaxSliceCartAdjunction`,
  `AdjointExp`, `SemanticTwoSortFrobenius`, `SemanticTwoSortFunctor`
  (Prop. `prop:semantic-twosort-functor`), `CharacterisationModelsTwoSort`
  (Thm. `thm:characterisation-models-two-sortification`).
* §5 The core projection: `CoreProjectionMorphism` (Def. `def:core-projection-morphism`),
  `CharacterisationModelsTwoSort` (core projection functor, final Corollary of §5.2).
* App. B Initial models: `Collage`, `CatPullbackCriterion`, `PointifyPullback`, `InitialModel`,
  `InitialModelMorphisms`, `InitialModelUnique`, `InitialModelGat` (Cor. `cor:initial-model-gat`).
* App. C Full faithfulness of two-sortification: `BiInitialInduction`,
  `TwoSortificationFullyFaithful` (Prop. `prop:faithful-at-XGAT-YGAT`), `TwoSortFFSetup`,
  `TwoSortFFCollage`, `TwoSortFFSquare`, `TwoSortFFGamma`, `TwoSortFFReadout`, `TwoSortFFMain`.

## The complete variant `CompExp`

The subdirectory `CompExp` contains a variant of the development where `Lexp` is replaced by the
2-category `CompExp` of categories with all `w`-small wide pullbacks (hence, having a terminal
object, all `w`-small limits) and a chosen exponentiable arrow, and functors preserving them:
`CompExp.Basic` (definition, completeness `CompExp.hasLimitsOfSize`), `CompExp.UniversalNatTrans`,
`CompExp.Strictification`, `CompExp.CatWidePullbacks` (wide pullbacks in `Cat`),
`CompExp.TwoSortification`, `CompExp.InitialModel` (initiality), `CompExp.BiInitialInduction`,
`CompExp.TwoSortificationFullyFaithful` (full faithfulness), `CompExp.ColaxSliceCartWidePullbacks`
and `CompExp.CharacterisationModelsTwoSort`.

## Infinite GATs

The subdirectory `InfiniteGat` proves Thm. `thm:infinite-GATs` of App. D: the pro-completion
`GatCat` of `FinGat` is bi-initial in `CompExp` (`InfiniteGat.gatCat_isBiInitial`, in
`InfiniteGat.Main`). Supporting files: `InfiniteGat.Pro` (pro-completion, co-density),
`InfiniteGat.ProExtension` (extension of finite-limit-preserving functors), `InfiniteGat.ExpData`,
`InfiniteGat.ProExponentiable` (Cor. `cor:exponentiable-free-filtered`),
`InfiniteGat.ProExtendExp` (Prop. `prop:lift-lexp-functor`), `InfiniteGat.Limits`.

Not formalised: Prop. `prop:core_projection_preserves_initial`
of §5.1, the remaining results of App. D (infinite GATs) beyond
Thm. `thm:infinite-GATs`, and the description of `FinGat` as a syntactic category
(here `FinGat` is any bi-initial object of `Lexp`, as allowed by Thm. `thm:uemura`).
-/
