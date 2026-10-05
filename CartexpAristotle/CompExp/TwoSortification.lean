/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.Strictification
import CartexpAristotle.CompExp.CatWidePullbacks
import CartexpAristotle.TwoSortification

/-!
# The endofunctor `- / PX`, the two-sortification functor and the model functor for `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.LexpEndofunctor` and
`CartexpAristotle.TwoSortification`.

* `CompExp.Φ`: the endofunctor of `CompExp` sending `(C, p : Y ⟶ X)` to `(C / P X, p̲)`. A slice
  of a category with all `w`-small wide pullbacks has all `w`-small wide pullbacks (they are
  connected limits, created by the forgetful functor), and the functor `Φ F` preserves them if `F`
  does.
* `CompExp.CatCompExp`: `Cat.{w, w + 1}` with the exponentiable arrow `U : Pointed ⥤ Type w`
  (it has all `w`-small wide pullbacks, `CatWidePullback.hasWidePullbacks`).
* `CompExp.twoSortification`: the bi-initial strict morphism `FinGat ⟶ Φ FinGat`.
* `CompExp.modelFunctor`: the bi-initial strict morphism `FinGat ⟶ CatCompExp`.

The underlying objects and morphisms of `Lexp` are the ones of the `Lexp` development:
`(Φobj A).toLexp = Lexp.Φobj A.toLexp`, `(Φmap F).toLexpHom = Lexp.Φmap F.toLexpHom` and
`CatCompExp.toLexp = CatLexp`.

## References

* [Paper, §4.2, Prop. `prop:lexp-functor-p2`], [Paper, §3.1, Def. `def:two-sortification`] and
  [Paper, §2.2, Definition of the model functor], adapted to `CompExp`.
-/

open CategoryTheory Limits SemanticTwoSortFunctor

universe w v u

/-- A functor between slices which commutes with the forgetful functors (up to a natural
isomorphism) with a functor `F` preserves the connected limits that `F` preserves. -/
lemma Over.preservesLimitsOfShape_of_forget {C : Type*} [Category C] {D : Type*} [Category D]
    {Z : C} {Z' : D} (H : Over Z ⥤ Over Z') (F : C ⥤ D)
    (e : H ⋙ Over.forget Z' ≅ Over.forget Z ⋙ F) (J : Type*) [Category J] [IsConnected J]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J H where
  preservesLimit {K} :=
    haveI : PreservesLimit K (H ⋙ Over.forget Z') :=
      preservesLimit_of_natIso K e.symm
    preservesLimit_of_reflects_of_preserves H (Over.forget Z')

namespace CompExp

open SliceExp

/-- The object part of the endofunctor `- / PX` of `CompExp`. -/
noncomputable def Φobj (A : CompExp.{w, v, max u v}) : CompExp.{w, v, max u v} where
  toLexp := Lexp.Φobj A.toLexp
  hasWidePullbacks J :=
    inferInstanceAs (HasLimitsOfShape (WidePullbackShape J) (Over (sZ A.arr)))

/-- The functor `Φ F` preserves wide pullbacks. -/
noncomputable instance Φfun_preservesWidePullbacks {A B : CompExp.{w, v, max u v}} (F : A ⟶ B)
    (J : Type w) : PreservesLimitsOfShape (WidePullbackShape J) (Lexp.Φfun F.toLexpHom) :=
  Over.preservesLimitsOfShape_of_forget _ F.functor (Iso.refl _) _

/-- The morphism part of the endofunctor `- / PX` of `CompExp`. -/
noncomputable def Φmap {A B : CompExp.{w, v, max u v}} (F : A ⟶ B) : Φobj A ⟶ Φobj B where
  toHom := Lexp.Φmap F.toLexpHom
  preservesWidePullbacks J := Φfun_preservesWidePullbacks F J

/-- The endofunctor of `CompExp` sending `(C, p : Y ⟶ X)` to `(C / P X, p')`.

[Paper, §4.2, Prop. `prop:lexp-functor-p2`], for `CompExp`. -/
noncomputable def Φ : CompExp.{w, v, max u v} ⥤ CompExp.{w, v, max u v} where
  obj := Φobj
  map := Φmap
  map_id A := Hom.ext (Lexp.Φmap_id A.toLexp)
  map_comp F G := Hom.ext (Lexp.Φmap_comp F.toLexpHom G.toLexpHom)

/-- `Cat.{w, w+1}` with the exponentiable arrow `U : Pointed ⥤ Type w`, as an object of
`CompExp`.

[Paper, §2.2, Prop. `prop:CAT`]: `CAT`, which is complete. -/
noncomputable def CatCompExp : CompExp.{w, w + 1, w + 2} where
  toLexp := CatLexp.{w}
  hasWidePullbacks := CatWidePullback.hasWidePullbacks.{w}

section TwoSortification

variable {FinGat : CompExp.{w, v, max u v}} (hFinGat : IsBiInitial FinGat)

/-- **The two-sortification functor** for `CompExp`: the bi-initial strict morphism from a
bi-initial `FinGat` to `Φ FinGat`.

[Paper, §3.1, Def. `def:two-sortification`], for `CompExp`. -/
noncomputable def twoSortification : FinGat ⟶ Φobj FinGat :=
  hFinGat.strictHom (Φobj FinGat)

/-- The two-sortification functor is strict. -/
theorem twoSortification_isStrict : (twoSortification hFinGat).toLexpHom.IsStrict :=
  hFinGat.strictHom_isStrict _

/-- Every morphism `FinGat ⟶ Φ FinGat` is isomorphic to the two-sortification functor. -/
theorem nonempty_iso_twoSortification (F : FinGat ⟶ Φobj FinGat) :
    Nonempty (F ≅ twoSortification hFinGat) :=
  hFinGat.nonempty_iso_strictHom _ F

end TwoSortification

section ModelFunctor

variable {FinGat : CompExp.{w, w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- **The model functor** for `CompExp`: the bi-initial strict morphism from a bi-initial `FinGat`
to `Cat` (with the exponentiable arrow `U : Pointed ⥤ Type w`).

[Paper, §2.2, Definition of the model functor], for `CompExp`. -/
noncomputable def modelFunctor : FinGat ⟶ CatCompExp.{w} :=
  hFinGat.strictHom CatCompExp.{w}

/-- The model functor is strict. -/
theorem modelFunctor_isStrict : (modelFunctor hFinGat).toLexpHom.IsStrict :=
  hFinGat.strictHom_isStrict _

/-- Every morphism `FinGat ⟶ CatCompExp` is isomorphic to the model functor. -/
theorem nonempty_iso_modelFunctor (F : FinGat ⟶ CatCompExp.{w}) :
    Nonempty (F ≅ modelFunctor hFinGat) :=
  hFinGat.nonempty_iso_strictHom _ F

end ModelFunctor

end CompExp
