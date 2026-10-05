/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.BiInitialDomCod
import CartexpAristotle.SemanticTwoSortFunctor

/-!
# The two-sortification functor and the model functor

Let `FinGat` be a bi-initial object of the 2-category `Lexp`.

* `Lexp.IsBiInitial.strictHom`: the chosen strict morphism `FinGat ⟶ B`, for any `B`. It is
  obtained by strictifying (`Lexp.strictify`) an arbitrary morphism `FinGat ⟶ B`, which is
  possible since the domain and codomain of the chosen arrow of `FinGat` differ. By bi-initiality it
  is unique up to a unique invertible 2-cell.
* `Lexp.twoSortification`: the bi-initial strict morphism `FinGat ⟶ Φ FinGat`, where `Φ` is
  the endofunctor of `Lexp` from `LexpEndofunctor`.
* `Lexp.modelFunctor`: the bi-initial strict morphism `FinGat ⟶ CatLexp`, where `CatLexp` is
  `Cat` with the exponentiable arrow `U : Pointed ⥤ Type`.

## References

* [Paper, §2.2, Prop. `prop:strictification`]: `Lexp.IsBiInitial.strictHom` (the strict
  bi-initial functor).
* [Paper, §2.2, Definition of the model functor] (after Prop. `prop:CAT`):
  `Lexp.modelFunctor`.
* [Paper, §3.1, Def. `def:two-sortification`]: `Lexp.twoSortification`, the strict bi-initial
  `Lexp`-functor `T : FinGat → FinGat/Fam` (here `Φ FinGat`, see
  [Paper, §3.1, Props. `prop:p2-construction` and `prop:p2-exponentiable`]).
-/

open CategoryTheory

universe w v u

namespace Lexp

namespace IsBiInitial

variable {A : Lexp.{v, u}} (hA : IsBiInitial A) (B : Lexp.{v, u})

/-- The chosen strict morphism out of a bi-initial `Lexp`: the strictification of some
morphism `A ⟶ B`.

[Paper, §2.2, Prop. `prop:strictification`]. -/
noncomputable def strictHom : A ⟶ B :=
  strictify (Classical.choice (hA.nonempty_hom B)) hA.dom_ne_cod

/-- The chosen morphism out of a bi-initial object is strict. -/
theorem strictHom_isStrict : (hA.strictHom B).IsStrict :=
  strictify_isStrict _ _

/-- Every morphism out of a bi-initial object is isomorphic to the chosen strict one. -/
theorem nonempty_iso_strictHom (F : A ⟶ B) : Nonempty (F ≅ hA.strictHom B) :=
  hA.nonempty_iso _ _

/-- The invertible 2-cell between a morphism out of a bi-initial object and the chosen strict one
is unique. -/
theorem subsingleton_iso_strictHom (F : A ⟶ B) : Subsingleton (F ≅ hA.strictHom B) :=
  ⟨fun _ _ => Iso.ext (hA.hom₂_ext _ _)⟩

end IsBiInitial

section TwoSortification

variable {FinGat : Lexp.{v, max u v}} (hFinGat : IsBiInitial FinGat)

/-- **The two-sortification functor**: the bi-initial strict morphism from a bi-initial `FinGat`
to its image `Φ FinGat` under the endofunctor of `Lexp`.

[Paper, §3.1, Def. `def:two-sortification`]: the two-sortification functor `T`. -/
noncomputable def twoSortification : FinGat ⟶ Φ.obj FinGat :=
  hFinGat.strictHom (Φ.obj FinGat)

/-- The two-sortification functor is strict: it sends the chosen arrow of `FinGat` exactly to the
chosen arrow of `Φ FinGat`. -/
theorem twoSortification_isStrict : (twoSortification hFinGat).IsStrict :=
  hFinGat.strictHom_isStrict _

/-- Every morphism `FinGat ⟶ Φ FinGat` is isomorphic to the two-sortification functor. -/
theorem nonempty_iso_twoSortification (F : FinGat ⟶ Φ.obj FinGat) :
    Nonempty (F ≅ twoSortification hFinGat) :=
  hFinGat.nonempty_iso_strictHom _ F

end TwoSortification

section ModelFunctor

open SemanticTwoSortFunctor

variable {FinGat : Lexp.{w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- **The model functor**: the bi-initial strict morphism from a bi-initial `FinGat` to `Cat`
(with the exponentiable arrow `U : Pointed ⥤ Type w`).

[Paper, §2.2, Definition of the model functor]. -/
noncomputable def modelFunctor : FinGat ⟶ CatLexp.{w} :=
  hFinGat.strictHom CatLexp.{w}

/-- The model functor is strict: it sends the chosen arrow of `FinGat` exactly to
`U : Pointed ⥤ Type w`. -/
theorem modelFunctor_isStrict : (modelFunctor hFinGat).IsStrict :=
  hFinGat.strictHom_isStrict _

/-- Every morphism `FinGat ⟶ CatLexp` is isomorphic to the model functor. -/
theorem nonempty_iso_modelFunctor (F : FinGat ⟶ CatLexp.{w}) :
    Nonempty (F ≅ modelFunctor hFinGat) :=
  hFinGat.nonempty_iso_strictHom _ F

end ModelFunctor

end Lexp
