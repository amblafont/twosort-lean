# How the Lean proof of initial models differs from the appendix

This note compares the Lean proof that every theory has an initial model
(`modelFunctor_hasInitial` in `CartexpAristotle/InitialModelGat.lean`, which uses the general result
`InitialModel.isInitialZero` in `CartexpAristotle/InitialModelUnique.lean`) with the proof in the
appendix section "Initial Models of GATs" (`s-appendices_csl.tex`).

## Overview

| Step | Appendix | Lean |
|---|---|---|
| Candidate model \(0_Ω\) | Use Thm. *universal-property-natural-transformation* to get a nat. trans. \(\hom(Ω,-) ⇒ \mathcal M\), then evaluate at \(\mathrm{id}_Ω\) (Yoneda) | The same idea (`alpha`, `zero` in `InitialModel.lean`) |
| Existence of \(0_Ω → ω\) | Nat. trans. into \(\mathrm{cod}_- ∘ \mathcal M : \FinGat → \CAT^→\), with a new \(\Lexp\)-structure on \(\CAT^→\) (Prop. *arrow-functor-lexp*) | Nat. trans. **out of a collage** into \(\mathcal M\) itself, with \(\CAT\)'s usual structure (`gamma`, `toModel` in `InitialModelMorphisms.lean`) |
| Uniqueness | "Any morphism satisfies the condition of Prop. *initial-model-gat-morphism-existence*", plus the Yoneda correspondence | Every `g : zero ⟶ ω` is turned into a nat. trans. `gammaOf g` out of the collage. Its square at `p` is the same one, so `gammaOf g = gamma`. Then `g` is read back from it (`InitialModelUnique.lean`) |
| Scope | The model functor | Any \(\Lexp\)-morphism `G : A ⟶ CatLexp` out of a bi-initial `A` |
| Size | Not discussed | Assumes `LocallySmall.{w}` so that the term sets \(\mathrm{Tm}(B)\) live in `Type w` |

## 1. The candidate model: same idea, more details checked

As in the appendix, bi-initiality (`IsBiInitial.existsUnique_natTrans_iso`) gives a unique
natural transformation `alpha : Disc (a ⟶ -) ⟶ G`. Its square at `p` sends a sort
`B : a ⟶ X` to `Tm a B = {t : a ⟶ Y // t ≫ p = B}`, and a term `t : a ⟶ Y` to `Tm a (t ≫ p)`
pointed at `t`. The model is `zero = alpha_a (𝟙 a)`, i.e. Yoneda evaluated at the identity.

The appendix leaves some side conditions implicit. The Lean proof checks each of them:

* **The square is a pullback.** The theorem needs the square at `p` to be a pullback in `Cat`.
  The appendix says only that "the two conditions determine the naturality square". In Lean this
  is `hf0`. It is proved through a concrete criterion for pullbacks against
  `U : Pointed ⥤ Type` (`PointifyCrit`, `PointifyPullback.lean`, `CatPullbackCriterion.lean`).
  For every `B` and every `z : Tm a B` there is exactly one `t` over `B` whose point is `z`,
  namely the `t` underlying `z`.
* **`Disc (a ⟶ -)` preserves pullbacks.** This is needed to apply the theorem. It is proved in
  `Collage.lean` (`homDiscFunctor_isPullback`).
* **`G p` equals `U` only up to isomorphism.** The model functor is an \(\Lexp\)-morphism, so
  `G p` is isomorphic to `U : Pointed ⥤ Type` but not equal to it. I added the variant
  `IsBiInitial.existsUnique_natTrans_iso`, which states the square through this isomorphism
  `G.iso`.
* **Size.** \(\mathrm{Tm}(B)\) is a hom-set of `FinGat`, while models take values in `Type w`.
  So `Tm` is shrunk with `Shrink`, which needs the hypothesis `LocallySmall.{w} FinGat.carrier`.

The appendix also says that \(0_Ω\) is the *unique* model with these two properties. Lean does
not state that uniqueness separately. It uses only the uniqueness of `alpha` (`alpha_unique`),
which is all the later steps need.

## 2. Existence of a morphism \(0_Ω → ω\): the main difference

**Appendix.** A morphism of models is an object of \(\mathcal M(Ω)^→\). So the appendix builds a
natural transformation from \(Γ ↦ (\hom(Ω,Γ) \xrightarrow{\mathcal M(-)(ω)} \mathcal M Γ)\) into
\(\mathrm{cod}_- ∘ \mathcal M : \FinGat → \CAT^→\). The target must be an \(\Lexp\)-functor, so
the appendix needs Proposition *arrow-functor-lexp*: \(\mathrm{cod}_-\) is an \(\Lexp\)-functor
from \((\CAT, p_\CAT)\) to \((\CAT^→, \mathrm{cod}_-(p_\CAT))\). That in turn requires describing
pushforwards in \(\CAT^→\) (the categories \(\mathbf{Set}/\mathrm{Fam}(C)\)) and checking that
\(\mathrm{cod}_-\) preserves them. The appendix only sketches this ("It can be checked that…").

**Lean.** The proof never leaves \(\CAT\), and it keeps the *target* functor `G` with its usual
\(\Lexp\)-structure. What changes is the *source* functor:

* The model `ω` gives a natural transformation `beta ω : Disc (a ⟶ -) ⟶ G`, `σ ↦ G σ ω`.
* `K ω = Collage.functor (beta ω)` sends `Γ` to the **collage** (cograph) of
  `beta_Γ : Disc (a ⟶ Γ) ⥤ G Γ`. Its objects are the `σ : a ⟶ Γ` together with the models of `Γ`.
  A morphism `σ ⟶ e` is a morphism `G σ ω ⟶ e` in `G Γ`, and there are no morphisms back.
* The source of the universal property only needs to **preserve pullbacks**. It does not need to
  be an \(\Lexp\)-functor. `Collage.functor_isPullback` shows that the collage preserves
  pullbacks whenever both of its pieces do: `Disc (a ⟶ -)` does, and `G` does as an
  \(\Lexp\)-morphism.
* The square at `p` (`f1`) restricts to the term-model square on the `Disc` part, and to `G.iso`
  on the `G` part. On the cross morphisms it is the interpretation of terms in `ω`
  (`termAt`, `termNat`). Its pullback property (`f1_crit`) is checked case by case on
  `inl`/`inr`, again with `PointifyCrit`.
* Bi-initiality gives a unique `gamma ω : K ω ⟶ G`. Uniqueness then gives the two restriction
  facts: `gamma` is `alpha` on the `Disc` part (`gamma_restrict₁`) and the identity on the `G`
  part (`gamma_restrict₂`).
* The morphism `toModel : zero ⟶ ω` is the image under the component `(gamma ω).app a` of the canonical cross morphism
  `inl (𝟙 a) ⟶ inr ω` (`crossHom`). By the two restriction facts, that image goes from `zero` to
  `ω`.

So Lean uses a collage functor into \(\CAT\) in place of the arrow-category target
\(\CAT^→\) with its new \(\Lexp\)-structure. As a result, Proposition *arrow-functor-lexp* and its
description of pushforwards in \(\CAT^→\) are **not needed and were not formalised**.

## 3. Uniqueness

**Appendix.** By Lemma *model-term-natural* and \(⟦t⟧_{0_Ω} = t\), any \(f : 0_Ω → ω\) sends
\(t\) to \(⟦t⟧_ω\). So it satisfies the condition that characterises the morphism of
Proposition *initial-model-gat-morphism-existence*, and uniqueness follows from the Yoneda
correspondence between such morphisms and natural transformations.

**Lean.** There is no Yoneda correspondence for collages to cite, so it is built by hand:

* From any `g : zero ⟶ ω`, `gammaOf g : K ω ⟶ G` has components
  `Collage.lift (alpha_Γ) (𝟭) (theta g Γ)`, where `theta` sends `σ` to `G σ g`. Naturality is
  proved directly.
* `el_theta` is the Lean counterpart of the appendix's key observation: `g` sends the term `t` to
  its interpretation in `ω`. It combines naturality of points (`mpt_map`, the analogue of Lemma
  *model-term-natural*) with `mpt_alpha` (the point of `zero` at `t` is `t` itself).
* So `gammaOf g` has the same square at `p` as `gamma ω` (`gammaOf_left`, `gammaOf_right`), and
  uniqueness gives `gammaOf g = gamma ω` (`gammaOf_eq`).
* Evaluating at the cross morphism recovers `g` (`gammaOf_crossHom`), so `g = toModel`
  (`hom_eq_toModel`).

The logic matches the appendix: "any morphism meets the characterising condition, and that
condition is unique". In Lean the uniqueness comes from the natural transformation out of the
collage, not from a separate Yoneda argument.

## 4. Other differences

* **Generality.** `isInitialZero` holds for any \(\Lexp\)-morphism `G : A ⟶ CatLexp` out of a
  bi-initial `A` with small hom-sets. It is not limited to the model functor. The model functor
  is fixed only up to isomorphism by a noncomputable choice, so the general statement is the
  natural one.
* **Abandoned induction.** An earlier `InitialModelGat.lean` tried an induction over the objects of
  `FinGat`. Its pullback step does not follow from its hypotheses, since a pullback of categories
  with initial objects need not have one. That step is commented out in the file with an
  explanation, and the direct construction above replaces it.
* **Ingredients the appendix uses without proof** (pullbacks in `Cat`, pointed-set pullbacks,
  collages) are proved in `CatPullbackCriterion.lean`, `PointifyPullback.lean` and
  `Collage.lean`.
