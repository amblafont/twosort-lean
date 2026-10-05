/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.TwoSortification
import CartexpAristotle.InitialModelGat

/-!
# Initial models for a bi-initial `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.InitialModelGat`.

Let `FinGat` be a bi-initial object of `CompExp` and `M : FinGat ⟶ CatCompExp` the model functor.
For every object `a` of `FinGat` (whose hom-types are `w`-small), the category `M a` has an initial
object: the term model of `a`.

The construction of the term model and the proof that it is initial
(`Lexp.InitialModel.isInitialZero`) only use the universal property of natural transformations
into the underlying `Lexp`-morphism of `M` (`Lexp.HasUniversalNatTrans`), which holds for every
morphism out of a bi-initial object of `CompExp` (`CompExp.IsBiInitial.hasUniversalNatTrans`).
The functor out of the collage used in the proof only needs to preserve pullbacks, so the proof
carries over to `CompExp` unchanged.

## References

* [Paper, App. B, Cor. `cor:initial-model-gat`], for `CompExp`.
-/

open CategoryTheory Limits

universe w

namespace CompExp

variable {FinGat : CompExp.{w, w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The underlying functor of the model functor. -/
noncomputable abbrev modelFun : FinGat.carrier ⥤ Cat.{w, w + 1} := (modelFunctor hFinGat).functor

/-- The term model of `a`: an object of `M a`, where `M` is the model functor. -/
noncomputable abbrev initialModel [LocallySmall.{w} FinGat.carrier] (a : FinGat.carrier) :
    ↑(show Cat.{w, w + 1} from (modelFun hFinGat).obj a) :=
  Lexp.InitialModel.zero (a := a) (modelFunctor hFinGat).toLexpHom
    (IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat _)

/-- The term model of `a` is an initial object of `M a`. -/
noncomputable def isInitialInitialModel [LocallySmall.{w} FinGat.carrier] (a : FinGat.carrier) :
    IsInitial (initialModel hFinGat a) :=
  Lexp.InitialModel.isInitialZero (a := a) (modelFunctor hFinGat).toLexpHom
    (IsBiInitial.hasUniversalNatTrans.{w, w + 1, w + 2} hFinGat _)

/-- **The images of the model functor have initial objects.** For every object `a` of a
bi-initial object `FinGat` of `CompExp` whose hom-types are `w`-small, the category `M a` has an
initial object, where `M` is the model functor.

[Paper, App. B, Cor. `cor:initial-model-gat`], for `CompExp`. -/
theorem modelFunctor_hasInitial [LocallySmall.{w} FinGat.carrier] (a : FinGat.carrier) :
    HasInitial ((modelFun hFinGat).obj a) :=
  (isInitialInitialModel hFinGat a).hasInitial

end CompExp
