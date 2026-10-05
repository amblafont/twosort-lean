/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.TwoSortification
import CartexpAristotle.CompExp.BiInitialInduction
import CartexpAristotle.TwoSortFFMain

/-!
# Full faithfulness of the two-sortification functor for `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.TwoSortificationFullyFaithful` and
`CartexpAristotle.TwoSortFFMain`.

Let `FinGat` be a bi-initial object of `CompExp` with `w`-small hom-types, and `T` the
two-sortification functor. Then `T` is fully faithful (`CompExp.twoSortificationFullyFaithful`).

The proof is the one for `Lexp`:

* the base cases `X` and `Y` (`Lexp.TwoSortFF.twoSortBij_cod`, `Lexp.TwoSortFF.twoSortBij_dom`)
  only use the two-sortification functor, the model functor and the universal property of natural
  transformations into the model functor and into `T ≫ Φ M` (`Lexp.TwoSortFF.TwoSortData`); all
  these are available for a bi-initial object of `CompExp` (`CompExp.twoSortData`);
* the induction is over the objects of a bi-initial `CompExp` (`CompExp.IsBiInitial.induction`),
  which also requires closure under wide pullbacks; this holds since `T` preserves them
  (`Lexp.twoSortBij_of_isLimit`).

## References

* [Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`] and [Paper, App. C.2, final Corollary],
  for `CompExp`.
-/

open CategoryTheory Limits

universe w v u

namespace Lexp

variable {FinGat B : Lexp.{v, u}} (T : FinGat ⟶ B)

/-- If `T` preserves limits of shape `J`, the objects at which `T` is fully faithful are closed
under limits of shape `J`. -/
lemma twoSortBij_of_isLimit {J : Type*} [Category J] [PreservesLimitsOfShape J T.functor]
    {K : J ⥤ FinGat.carrier} {c : Cone K} (hc : IsLimit c) (h : ∀ j, TwoSortBij T (K.obj j)) :
    TwoSortBij T c.pt := by
  have hTc := isLimitOfPreserves T.functor hc
  intro a
  constructor
  · intro k₁ k₂ hk
    simp only at hk
    refine hc.hom_ext fun j => (h j a).1 ?_
    simp only [CategoryTheory.Functor.map_comp, hk]
  · intro f
    choose g hg using fun j => (h j a).2 (f ≫ T.functor.map (c.π.app j))
    simp only at hg
    let s : Cone K :=
      { pt := a
        π :=
          { app := g
            naturality := fun j j' φ => by
              have hg' : ∀ j, T.functor.map (g j) = f ≫ T.functor.map (c.π.app j) := hg
              apply (h j' a).1
              change T.functor.map (𝟙 a ≫ g j') = T.functor.map (g j ≫ K.map φ)
              rw [Category.id_comp, T.functor.map_comp, hg', hg', Category.assoc,
                ← T.functor.map_comp, Cone.w] } }
    refine ⟨hc.lift s, hTc.hom_ext fun j => ?_⟩
    simp only [Functor.mapCone_π_app, ← CategoryTheory.Functor.map_comp, IsLimit.fac]
    exact hg j

end Lexp

namespace CompExp

variable {FinGat : CompExp.{w, w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The data of `Lexp.TwoSortFF.TwoSortData` for a bi-initial `FinGat` of `CompExp`: the
(underlying `Lexp`-morphisms of the) two-sortification functor and the model functor, which have
the universal property of natural transformations. -/
noncomputable def twoSortData : Lexp.TwoSortFF.TwoSortData FinGat.toLexp where
  tw := (twoSortification.{w, w + 1, w + 2} hFinGat).toLexpHom
  mf := (modelFunctor hFinGat).toLexpHom
  univM := IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat _
  univG := IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat
    (twoSortification.{w, w + 1, w + 2} hFinGat ≫ Φmap.{w, w + 1, w + 2} (modelFunctor hFinGat))

variable [LocallySmall.{w} FinGat.carrier]

/-- The two-sortification functor induces bijections on all hom-sets.

[Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`], for `CompExp`. -/
theorem twoSortBij_all (b : FinGat.carrier) :
    Lexp.TwoSortBij (twoSortification.{w, w + 1, w + 2} hFinGat).toLexpHom b :=
  hFinGat.induction
    { of_iso := fun i hb => Lexp.twoSortBij_of_iso _ i hb
      terminal := Lexp.twoSortBij_terminal _
      pullback := fun hpb h₁ h₂ hS => Lexp.twoSortBij_pullback _ hpb h₁ h₂ hS
      exp := fun c hc => Lexp.twoSortBij_exp _ c
        (Lexp.TwoSortFF.twoSortBij_cod (hFinGat := twoSortData hFinGat)) hc
      dom := Lexp.TwoSortFF.twoSortBij_dom (hFinGat := twoSortData hFinGat)
      cod := Lexp.TwoSortFF.twoSortBij_cod (hFinGat := twoSortData hFinGat)
      widePullback := fun J _ _ hc h =>
        haveI := (twoSortification.{w, w + 1, w + 2} hFinGat).preservesWidePullbacks J
        Lexp.twoSortBij_of_isLimit (twoSortification.{w, w + 1, w + 2} hFinGat).toLexpHom hc h } b

/-- **The two-sortification functor of a bi-initial `CompExp` is full.** -/
instance twoSortification_full : (twoSortification.{w, w + 1, w + 2} hFinGat).functor.Full :=
  ⟨fun {a b} f => (twoSortBij_all hFinGat b a).2 f⟩

/-- **The two-sortification functor of a bi-initial `CompExp` is faithful.** -/
instance twoSortification_faithful : (twoSortification.{w, w + 1, w + 2} hFinGat).functor.Faithful :=
  ⟨fun {a b} _ _ h => (twoSortBij_all hFinGat b a).1 h⟩

/-- **The two-sortification functor of a bi-initial `CompExp` is fully faithful.**

[Paper, App. C.2, final Corollary], for `CompExp`. -/
noncomputable def twoSortificationFullyFaithful :
    (twoSortification.{w, w + 1, w + 2} hFinGat).functor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end CompExp
