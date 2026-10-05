# How the Lean proof of full faithfulness differs from the appendix

This note compares the Lean proof that the two-sortification functor
\(T : \FinGat → \FinGat/P X\) is fully faithful (`Lexp.twoSortificationFullyFaithful` in
`CartexpAristotle/TwoSortFFMain.lean`) with the appendix section "Two-sortification is Fully
Faithful" of `s-appendices_csl.tex`.

Notation: \(Ω\) (Lean: `a`) is a theory, \(p : Y → X\) (Lean: `FinGat.arr : FinGat.dom ⟶ FinGat.cod`)
is the chosen arrow, and \(\mathrm{Tm}(B) = \{t : Ω → Y \mid p ∘ t = B\}\).

## Overview

| Step | Appendix | Lean |
|---|---|---|
| Reduction to \(X\) and \(Y\) | Prop. *faithful-at-XGAT-YGAT*: full \(\Lexp\)-subcategory \(S\) + bi-initiality | Same idea, packaged as a general induction principle `IsBiInitial.induction` (`BiInitialInduction.lean`, `TwoSortificationFullyFaithful.lean`) |
| Base cases as families | Cor. *faithful-via-terms*: one family morphism \(\mathrm{Tm}_Ω → \mathrm{Tm}^{\TW}_Ω\) must be mono / iso | Not used. Four separate statements: faithful/full at \(X\), faithful/full at \(Y\); fullness at \(Y\) uses fullness at \(X\) |
| Which functor of models | \(\TWb\) (cartesian comma of \(\FamFunctor{Γ}\)), linked to \(\model{\TW-}\) by Uemura's theorem | \(G = Φ\mathcal M ∘ T\), i.e. \(\model{\TW -}\) itself; Uemura's theorem is not formalised and not needed |
| Model \(\M{Ω}\) | Nat. trans. from the constant functor \(\hom(Ω,Γ) ↦ \mathrm{Tm}_Ω\) into \(\TWb\), then Yoneda | Nat. trans. `gammaT` **out of a collage** into \(G\); \(\M{Ω}\) = `MOmega` is the image of `inl (𝟙 a)` |
| Faithfulness | Read \(f\) off \(\TWb f(\M{Ω})\) | Same (`twoSort_faithful_cod`, `twoSort_faithful_dom`) |
| Initial object \(\Z{Ω}\) | Prop. *initial-object-two-sortification* (full description of \(\bang\Z{Ω}\) as \(\mathrm{TmEl}_Ω\)), proved through Prop. *initial-value-fam* and Lemma *nat-universal-pullback-P* | Only the initial model `Zm a` of the underlying theory of \(TΩ\), and only *one* fact about it: the index that \(h\) picks in its family determines \(h\) (`Rd_zero_injective`, `Qd_zero_injective`) |
| Section / fullness | \(\bang i\) is a section, proved by uniqueness of two nat. trans. into the colax slice \(\colaxSlice\) | A model morphism \(j : \M{Ω} → \Z{Ω}\) whose family part is "interpret the sorts and terms of \(Ω\)"; \(i ≫ j = \mathrm{id}\) by initiality of \(\Z{Ω}\) |
| Size | Not discussed | Assumes `LocallySmall.{w}` so that \(\mathrm{Tm}(B)\) lives in `Type w` |

The rest of this note explains each row.

## 1. Reduction to the base cases \(X\) and \(Y\)

**Appendix.** Prop. *faithful-at-XGAT-YGAT*: the full subcategory \(S\) of theories \(Γ\) at which
\(I\) is (fully) faithful is closed under limits preserved by \(I\) and under \(P\), so it is a full
\(\Lexp\)-subcategory; bi-initiality gives a functor \(\FinGat → S\) whose composite with the
inclusion is isomorphic to the identity.

**Lean.** The same argument, split in two:

* `Lexp.IsBiInitial.induction` (`BiInitialInduction.lean`) is a general induction
  principle for any bi-initial `A`: a property that is invariant under isomorphism, holds for the
  terminal object, is closed under pullbacks and under the chosen exponentials along `p`, and holds
  for `Y` and `X`, holds for every object. Its proof is exactly the appendix's "full
  \(\Lexp\)-subcategory + bi-initiality" argument.
* It is applied (`twoSortBij_all`) to the property `TwoSortBij b`: "for every `a`, the map
  `(a ⟶ b) → (T a ⟶ T b)` is bijective". The closure steps are in
  `TwoSortificationFullyFaithful.lean`: `twoSortBij_of_iso`, `twoSortBij_terminal`,
  `twoSortBij_pullback` and `twoSortBij_exp`.

One detail the appendix leaves implicit: the exponential step (`twoSortBij_exp`) does not only use
the property at `c`; it also uses the base case at `X`. To transport a morphism into
\(P c\) one first needs its composite with \(P c → X\), and this is where bijectivity at `X` is
used. So the induction is run with the base case at `X` already available.

I worked with bijectivity directly instead of handling "faithful" and "fully faithful" as two
separate subcategories.

## 2. No reformulation through families (Cor. *faithful-via-terms*)

The appendix restates the base cases as a single statement: the family morphism
\(\mathrm{Tm}_Ω → \mathrm{Tm}^{\TW}_Ω\) is a monomorphism (resp. an isomorphism). Fullness then
becomes "this mono has a section".

The Lean proof does not use this corollary or the equivalence \(\mathbf{Set}^→ ≃ \FamS\). It proves
four separate statements in `TwoSortFFMain.lean`:

* `twoSort_faithful_cod`: \(TB_1 = TB_2 ⇒ B_1 = B_2\) for \(B_i : Ω → X\);
* `twoSort_full_cod`: every \(h : TΩ → TX\) is \(TB\) for some \(B\);
* `twoSort_faithful_dom`: \(Tt_1 = Tt_2 ⇒ t_1 = t_2\) for \(t_i : Ω → Y\). This first uses
  faithfulness at \(X\) to get \(p t_1 = p t_2\);
* `twoSort_full_dom`: every \(h : TΩ → TY\) is \(Tt\) for some \(t\). This first uses
  fullness at \(X\) to find \(B\) with \(TB = h ≫ Tp\), and then finds the term \(t\) of sort
  \(B\).

Proving the \(Y\) case after the \(X\) case in this way is the hom-set version of "a morphism of
families is an iso iff it is an iso on indices and on each fibre".

## 3. Which functor of models

**Appendix.** It works with \(\TWb\), which sends \(Γ\) to the cartesian comma
\(\cartCommaFam{\FamFunctor{Γ}}\), because it has an exact description of the images of \(X\) and
\(Y\). It is related to \(\model{\TW -}\) by Uemura's theorem (Thm. *uemura*). The colax slice
\(\colaxSlice\) is also needed for the fullness step.

**Lean.** It works with `GT = Tw ≫ Φmap Mf` (`TwoSortFFReadout.lean`), that is, the functor
\(Γ ↦ \model{\TW Γ}\) itself, viewed as an object of \(\CAT/\FamS\) through
\(\model{TΓ → P X}\). Uemura's theorem, \(\TWb\) and the colax slice are not formalised.

The "exact description of the images of \(X\) and \(Y\)" that motivated \(\TWb\) comes in Lean
from the fact that `GT` is a morphism of `Lexp`. Its isomorphism data `GT.iso` identify
`GT X` with families with a chosen index, and `GT Y` with the pullback of
\(U : \mathbf{Pointed} → \mathbf{Set}\) along evaluation. These are `isoX`, `isoY`, `gX`, `gY` and
`gIsPullback` in `TwoSortFFSetup.lean`. All of `TwoSortFFSetup`, `TwoSortFFCollage`,
`TwoSortFFSquare` and `TwoSortFFGamma` work for an arbitrary `G : A ⟶ Φ CatLexp` out of a
bi-initial `A`. The two-sortification functor appears only in `TwoSortFFReadout` and
`TwoSortFFMain`.

## 4. The model \(\M{Ω}\) (Prop. *model-faithful*) and faithfulness

**Appendix.** Apply the universal property to get a natural transformation from
\(Γ ↦ (\hom(Ω,Γ) → \FamS\), constant at \(\mathrm{Tm}_Ω)\) to \(\TWb\). Yoneda then gives
\(\M{Ω}\). Its family is \(\mathrm{Tm}_Ω\), and \(\TWb B(\M{Ω})\) (resp. \(\TWb t(\M{Ω})\)) is
\(\mathrm{Tm}_Ω\) with the index \(B\) (resp. the index \(p t\) and the element \(t\)).

**Lean.** Here the source functor is larger. Given any model `K` of `G a`, `D G K`
(`TwoSortFFCollage.lean`) sends \(Γ\) to the **collage** of
\(σ ↦ Gσ(K)\) for \(σ : Ω → Γ\):

* objects are either a morphism `σ : a ⟶ Γ` (`inl σ`) or a model `e` of `G Γ` (`inr e`);
* morphisms `inl σ ⟶ inr e` are model morphisms `G σ K ⟶ e`, and there are none in the other
  direction;
* over families, `inl σ` lies over the constant family `TmFam a` \(= \mathrm{Tm}_Ω\), and an
  arrow `inl σ ⟶ inr e` lies over `psiF G K` followed by the family part of the arrow. Here
  `psiF G K : TmFam a ⟶ fam K` interprets every sort \(B\) and term \(t\) of \(Ω\) in `K`
  (`ixX`, `elY`).

The `inl` part of this collage is exactly the appendix's constant functor. I proved that `D G K`
preserves pullbacks (`preservesPullbacks_D`) and that its square at `p` is a pullback
(`isPullback_sq`, via the concrete pullback criterion `PointifyCrit`). Bi-initiality
(`IsBiInitial.existsUnique_natTrans_iso`) then gives a unique `gammaT : D G K ⟶ G`
(`TwoSortFFGamma.lean`), and

* `MOmega = gammaT_a (inl (𝟙 a))` is \(\M{Ω}\). `famF_MOmega`, `isoX_MOmega` and `gY_MOmega` are exactly the
  three bullet points of Prop. *model-faithful*.
* By uniqueness, `gammaT` is the identity on the `inr` part (`gamma_restrict₂`,
  `gammaT_obj_inr`).

**Faithfulness** is then the same argument as in the appendix. By `isoX_MOmega`, the image of
`MOmega` under `T B` is `TmFam a` with the index `B`, so `T B₁ = T B₂` forces `B₁ = B₂`. The case of
\(Y\) uses the point instead (`gY_MOmega`). One small difference: the appendix first proves that
\(\model{\TW -}\) is faithful and deduces that \(\TW\) is faithful. Lean reads `B` off directly
from `T B`, because the model only depends on `T B`.

## 5. The initial object \(\Z{Ω}\): much less is computed

**Appendix.** Prop. *initial-object-two-sortification* describes \(\bang\Z{Ω}\) completely as
\(\mathrm{TmEl}_Ω = (\mathrm{Tm}(\El A))_{A ∈ \mathrm{Tm}(\U_Ω)}\), with the cartesian morphisms
\(\TWb A(\Z{Ω})\) and \(\TWb t(\Z{Ω})\). This goes through Prop. *initial-value-fam*, which needs
Lemma *nat-universal-pullback-P* (an explicit formula for \(α_{PΓ}\) through transposition), and
Prop. *two-sortification-terms-isomorphic*, which identifies \(\mathrm{Tm}^{\TW}_Ω\) with
\(\mathrm{TmEl}_Ω\).

**Lean.** \(\Z{Ω}\) is `Zm a`, the initial model `zero` (from `InitialModel.lean`) of the
underlying theory `(T a).left`. Because `GT` is \(\model{\TW -}\) itself, there is no
transport along Uemura's isomorphism. The proof uses only one property of it
(`TwoSortFFReadout.lean`):

* For `h : T a ⟶ T X`, write `AX h : (T a).left ⟶ Y` for the composite of `h` with
  \(TX ≅ P X ×_X Y → Y\) (the appendix's \(A'\)). Then `elToPt_Rd` says that the index that
  \(h\) selects in the family of a model `K`, seen as a pointed set, is
  \(\mathrm{pt}(\mathcal M(AX\,h)(K))\).
* For `K = zero` this pointed set is \(\mathrm{Tm}(AX\,h ≫ p)\) pointed at \(AX\,h\)
  (`pt_zero`). This holds directly by construction of `zero`.
* So \(h\) is determined by the index it selects in the family of `zero`, because
  \(AX\,h\) is recovered from it and \(h\) is recovered from \(AX\,h\) by the pullback defining
  \(TX\) (`Rd_zero_injective`). The same holds for `h : T a ⟶ T Y`, given `h ≫ T p`, using
  the selected element (`Qd_zero_injective`).

In particular, Lean never computes the fibres \(\mathrm{Tm}(\El A)\) of \(\bang\Z{Ω}\) as a whole.
It never uses Lemma *nat-universal-pullback-P* or Prop. *initial-value-fam* in their general form,
and never builds the isomorphism \(\mathrm{Tm}^{\TW}_Ω ≅ \mathrm{TmEl}_Ω\). Its role is played by
`AX`, `AY` and the pullback extensionality in `Rd_zero_injective` / `Qd_zero_injective`.

## 6. Fullness: the main difference

Both proofs use the same equation. Let \(i : \Z{Ω} → \M{Ω}\) be the initial morphism, and let
\(ψ : \mathrm{Tm}_Ω → \bang\Z{Ω}\) send a sort/term of \(Ω\) to its interpretation in \(\Z{Ω}\)
(up to the identifications above, this is \(\mathrm{Tm}_Ω → \mathrm{Tm}^{\TW}_Ω ≅ \mathrm{TmEl}_Ω\)).
Then
\[ \bang i ≫ ψ = \mathrm{id}_{\bang\Z{Ω}}. \]
They prove it differently.

**Appendix (Prop. *section-terms-two-sortification*).** It considers two natural
transformations, from the functor \(Γ ↦ (\hom(Ω,Γ) → \FamS\), constant at
\(\mathrm{TmEl}_Ω)\) to the strict initial functor into the colax slice \(\colaxSlice\). One uses
\(\TWb σ(\Z{Ω})\), the other postcomposes with \(\mathrm{TmEl}_Ω → \mathrm{Tm}_Ω → \mathrm{TmEl}_Ω\).
It shows they are equal by the uniqueness part of the universal property. This needs:

* the \(\Lexp\)-structure on \(\colaxSlice\) (Thm. *colax-exponentiable*) and on
  \(\colaxSliceCart\) (Prop. *cartesian-colax-lexp*), and the strict initial functor of
  Cor. *family-functor-gat*;
* that the squares at \(p\) are pullbacks, using that \(\coref{}\Z{Ω}\) is initial and so
  isomorphic to \(0_Ω\);
* a check on \(σ : Ω → X\) and \(σ : Ω → Y\), using the description of \(\Z{Ω}\) from
  Prop. *initial-object-two-sortification*.

**Lean.** It turns \(ψ\) into the family part of a **model morphism**, and then uses only
initiality:

1. Apply the collage construction of §4 with `K := Zm a`. It gives a model morphism
   \[ j = \texttt{jHom} : \M{Ω} → \Z{Ω}, \]
   the image under `gammaT` of the canonical collage arrow `inl (𝟙 a) ⟶ inr Z` (`crossT`).
   Because collage arrows `inl σ ⟶ inr e` lie over `psiF`, the family part of \(j\) is
   \(ψ\) = `psiF G Z` (`famF_jHom`).
2. \(i ≫ j = \mathrm{id}_{\Z{Ω}}\), since both are endomorphisms of the initial object `Zm a`
   (`isInitialZero … |>.hom_ext`). Applying the family functor gives `hfam`, i.e.
   \(\bang i ≫ ψ = \mathrm{id}\).
3. **Full at \(X\)** (`twoSort_full_cod`). Given \(h : TΩ → TX\), let \(x\) be the index that
   \(h\) selects in the family of \(\Z{Ω}\). This selection is natural in model morphisms
   (`Rd_map`), so \(\bang i(x)\) is the index \(h\) selects in \(\M{Ω}\). That index is an element
   of `TmFam a`, i.e. a sort \(B : Ω → X\). By step 2, \(x = ψ(B)\), which is the index that
   \(TB\) selects in \(\Z{Ω}\) (`ixX_heq`). By `Rd_zero_injective`, \(h = TB\).
4. **Full at \(Y\)** (`twoSort_full_dom`). The same argument on the selected element: get \(B\)
   with \(TB = h ≫ Tp\) from step 3, read off a term \(t\) of sort \(B\) from the element
   \(h\) selects in \(\M{Ω}\) (`Qd_map`), and conclude \(h = Tt\) with `Qd_zero_injective`.

So the extra category \(\colaxSlice\) and its \(\Lexp\)-structure are replaced by a collage in
\(\CAT/\FamS\) and the trivial fact that an initial object has only the identity endomorphism. The
same trick (a collage instead of a new \(\Lexp\)-structure on an auxiliary category) was used for
existence of morphisms out of the initial model; see `INITIALITY_PROOF_COMPARISON.md`.
One construction (`gammaT` for `K = Zm a`) gives both \(\M{Ω}\) (§4) and \(j\) (§6).

The trade-off: the appendix's fullness argument is short on paper but relies on a lot of
infrastructure (Uemura's theorem, the colax slice and its exponentials, the description of
\(\Z{Ω}\)). The Lean argument needs none of these. Instead it pays with the collage
construction: its functor to families (`ell`, `kappa`), preservation of pullbacks, the pullback
square at \(p\), and many dependent-type `HEq` transports in `TwoSortFFMain.lean`.

## 7. Size assumption

Both the family `TmFam a` and the initial model need the term sets \(\mathrm{Tm}(B)\) as types in
`Type w`, but `FinGat : Lexp.{w+1, w+2}` has hom-sets in `Type (w+1)`. The Lean statements
therefore assume `[LocallySmall.{w} FinGat.carrier]` and use `Shrink` (`shX`, `unX`, `TmS` in
`TwoSortFFCollage.lean`). This is the same hypothesis as for initial models. The appendix does not
discuss sizes.
