/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.UniversalNatTrans
import CartexpAristotle.BiInitialInduction

/-!
# Induction over the objects of a bi-initial `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.BiInitialInduction`.

Let `A` be a bi-initial object of `CompExp` and `Q` a property of the objects of `A` which is
invariant under isomorphism, holds for the terminal object, is closed under pullbacks, under
`w`-small wide pullbacks and under the chosen exponentials along the chosen arrow `p : Y ⟶ X`,
and holds for `Y` and `X`. Then `Q` holds for every object of `A`
(`CompExp.IsBiInitial.induction`).

As for `Lexp`, the full subcategory on the objects satisfying `Q` is an object of `CompExp`, and
the bi-initial morphism into it, followed by the inclusion, is isomorphic to the identity.
-/

open CategoryTheory Limits

universe w v u

namespace CompExp

/-- A property of objects of a `CompExp` which is closed under all the constructions of `CompExp`
(isomorphisms, the terminal object, pullbacks, `w`-small wide pullbacks, the chosen exponentials
along the chosen arrow) and holds for the domain and codomain of the chosen arrow. -/
structure InductiveProperty (A : CompExp.{w, v, u}) (Q : A.carrier → Prop) : Prop
    extends Lexp.InductiveProperty A.toLexp Q where
  widePullback : ∀ (J : Type w) (K : WidePullbackShape J ⥤ A.carrier) (c : Cone K), IsLimit c →
    (∀ j, Q (K.obj j)) → Q c.pt

namespace InductiveProperty

variable {A : CompExp.{w, v, u}} {Q : A.carrier → Prop} (hQ : InductiveProperty A Q)

lemma closedWidePullback (J : Type w) :
    (hQ.toInductiveProperty.prop).IsClosedUnderLimitsOfShape (WidePullbackShape J) where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    exact hQ.widePullback J h.diag _ h.isLimit h.prop_diag_obj

/-- The full subcategory on the objects satisfying `Q`, as an object of `CompExp`. -/
noncomputable def subExp : CompExp.{w, v, u} where
  toLexp := hQ.toInductiveProperty.subExp
  hasWidePullbacks J :=
    haveI := hQ.closedWidePullback J
    hasLimitsOfShape_of_closedUnderLimits (WidePullbackShape J) hQ.toInductiveProperty.prop

/-- The inclusion of the full subcategory, as a morphism of `CompExp`. -/
noncomputable def ιHom : hQ.subExp ⟶ A where
  toHom := hQ.toInductiveProperty.ιHom
  preservesWidePullbacks J :=
    haveI := hQ.closedWidePullback J
    (⟨fun {_} => inferInstance⟩ :
      PreservesLimitsOfShape (WidePullbackShape J) (hQ.toInductiveProperty.prop).ι)

end InductiveProperty

/-- **Induction over the objects of a bi-initial `CompExp`.** A property of objects which is
invariant under isomorphism, holds for the terminal object, is closed under pullbacks, `w`-small
wide pullbacks and the chosen exponentials along the chosen arrow `p : Y ⟶ X`, and holds for `Y`
and `X`, holds for every object.

[Paper, App. C, proof of Prop. `prop:faithful-at-XGAT-YGAT`] (full subcategory argument), for
`CompExp`. -/
theorem IsBiInitial.induction {A : CompExp.{w, v, u}} (hA : IsBiInitial A) {Q : A.carrier → Prop}
    (hQ : InductiveProperty A Q) (a : A.carrier) : Q a := by
  obtain ⟨s⟩ := hA.nonempty_hom hQ.subExp
  obtain ⟨e⟩ := hA.nonempty_iso (s ≫ hQ.ιHom) (𝟙 A)
  let e' := Hom.isoToHom e
  have i : (s.functor.obj a).obj ≅ a :=
    { hom := e'.hom.nat.app a
      inv := e'.inv.nat.app a
      hom_inv_id := congrArg (fun t => t.nat.app a) e'.hom_inv_id
      inv_hom_id := congrArg (fun t => t.nat.app a) e'.inv_hom_id }
  exact hQ.of_iso i (s.functor.obj a).property

end CompExp
