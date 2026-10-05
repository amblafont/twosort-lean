/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CatExponentiable
import CartexpAristotle.CatPullbackCriterion

/-!
# Pullbacks of `U : Pointed ⥤ Type` along functors to types

A functor `F : S ⥤ Type w` together with a natural choice of elements `s x : F x` gives a functor
`pointify F s : S ⥤ Pointed` lifting `F` along the forgetful functor `U`.

For `snd : W ⥤ X` and `g : X ⥤ Type w`, a square
```
W ──pointify (snd ⋙ g) s──▶ Pointed
│snd                          │U
▼                             ▼
X ────────────g────────────▶ Type
```
is a pullback in `Cat` if and only if
* for every `x : X` and `z : g x`, there is a unique `w` with `snd w = x` and `s w = z`, and
* for all `w`, `w'` and `h : snd w ⟶ snd w'` with `g h (s w) = s w'`, there is a unique
  `k : w ⟶ w'` with `snd k = h`.

## References

* Auxiliary, not in the paper. It describes the naturality squares at `p` of the natural
  transformations into the model functor built in [Paper, App. B, Prop.
  `prop:initial-model-gat-existence`], which must be pullbacks for
  [Paper, Thm. `thm:universal-property-natural-transformation`] to apply.
-/

open CategoryTheory Limits

universe w

namespace PointedForget

section Pointify

variable {S : Type (w + 1)} [Category.{w} S]

/-- The lift of a functor to types along `U`, given a natural choice of elements. -/
def pointify (F : S ⥤ Type w) (s : ∀ x, F.obj x)
    (hs : ∀ {x y : S} (f : x ⟶ y), F.map f (s x) = s y) : S ⥤ Pointed.{w} where
  obj x := ⟨F.obj x, s x⟩
  map f := ⟨F.map f, hs f⟩
  map_id x := by
    apply Pointed.Hom.ext
    funext a
    simp
  map_comp f g := by
    apply Pointed.Hom.ext
    funext a
    simp

lemma pointify_forget (F : S ⥤ Type w) (s : ∀ x, F.obj x)
    (hs : ∀ {x y : S} (f : x ⟶ y), F.map f (s x) = s y) :
    pointify F s hs ⋙ forget Pointed = F := rfl

lemma pointed_eq_of_heq {P Q : Pointed.{w}} (hX : P.X = Q.X) (hp : P.point ≍ Q.point) : P = Q := by
  cases P; cases Q; cases hX; cases hp; rfl

lemma point_heq_of_eq {P Q : Pointed.{w}} (h : P = Q) : P.point ≍ Q.point := by
  subst h; rfl

lemma pointify_ext {F F' : S ⥤ Type w} {s : ∀ x, F.obj x} {s' : ∀ x, F'.obj x}
    {hs : ∀ {x y : S} (f : x ⟶ y), F.map f (s x) = s y}
    {hs' : ∀ {x y : S} (f : x ⟶ y), F'.map f (s' x) = s' y} (hF : F = F')
    (hsec : ∀ x, s x ≍ s' x) : pointify F s hs = pointify F' s' hs' := by
  subst hF
  have : s = s' := funext fun x => eq_of_heq (hsec x)
  subst this
  rfl

end Pointify

section Pullback

variable {W X : Cat.{w, w + 1}} (snd : W ⟶ X) (g : X ⟶ Cat.of (Type w))
  (s : ∀ x : W, g.toFunctor.obj (snd.toFunctor.obj x))
  (hs : ∀ {x y : W} (f : x ⟶ y), g.toFunctor.map (snd.toFunctor.map f) (s x) = s y)

/-- The concrete condition for the square of `pointify` to be a pullback. -/
structure PointifyCrit : Prop where
  obj : ∀ (x : X) (z : g.toFunctor.obj x), ∃! w : W, snd.toFunctor.obj w = x ∧ s w ≍ z
  hom : ∀ (w w' : W) (h : snd.toFunctor.obj w ⟶ snd.toFunctor.obj w'),
    g.toFunctor.map h (s w) = s w' → ∃! k : w ⟶ w', snd.toFunctor.map k = h

/-- The lift `pointify (snd ⋙ g) s` as a morphism of `Cat`. -/
abbrev pointifyHom : W ⟶ Cat.of Pointed.{w} :=
  (pointify (snd.toFunctor ⋙ g.toFunctor) s hs).toCatHom

lemma pointifyHom_comm : pointifyHom snd g s hs ≫ U = snd ≫ g := rfl

theorem isPullback_pointify (hc : PointifyCrit snd g s) :
    IsPullback (pointifyHom snd g s hs) snd U g := by
  refine CatPullback.isPullback_of_crit ⟨?_, ?_⟩ (pointifyHom_comm snd g s hs)
  · intro x₁ x₂ h
    obtain ⟨w, ⟨hw₁, hw₂⟩, hu⟩ := hc.obj x₂ (cast h x₁.point)
    refine ⟨w, ⟨?_, hw₁⟩, fun w' hw' => hu w' ⟨hw'.2, ?_⟩⟩
    · refine pointed_eq_of_heq ?_ (hw₂.trans (cast_heq _ _))
      change g.toFunctor.obj (snd.toFunctor.obj w) = x₁.X
      rw [hw₁]; exact h.symm
    · exact (point_heq_of_eq hw'.1).trans (cast_heq _ _).symm
  · intro w w' h₁ h₂ h
    have e : (h₁ : Pointed.Hom _ _).toFun = g.toFunctor.map h₂ := eq_of_heq h
    have hcond : g.toFunctor.map h₂ (s w) = s w' := by
      rw [← e]; exact (h₁ : Pointed.Hom _ _).map_point
    obtain ⟨k, hk, hu⟩ := hc.hom w w' h₂ hcond
    refine ⟨k, ⟨?_, hk⟩, fun k' hk' => hu k' hk'.2⟩
    apply Pointed.Hom.ext
    change g.toFunctor.map (snd.toFunctor.map k) = _
    rw [hk, e]

theorem pointifyCrit_of_isPullback (h : IsPullback (pointifyHom snd g s hs) snd U g) :
    PointifyCrit snd g s := by
  have hc := CatPullback.crit_of_isPullback h
  constructor
  · intro x z
    obtain ⟨w, ⟨hw₁, hw₂⟩, hu⟩ := hc.obj (⟨g.toFunctor.obj x, z⟩ : Pointed.{w}) x rfl
    refine ⟨w, ⟨hw₂, point_heq_of_eq hw₁⟩, fun w' hw' => hu w' ⟨?_, hw'.1⟩⟩
    refine pointed_eq_of_heq ?_ hw'.2
    change g.toFunctor.obj (snd.toFunctor.obj w') = g.toFunctor.obj x
    rw [hw'.1]
  · intro w w' h₂ hcond
    let h₁ : (pointifyHom snd g s hs).toFunctor.obj w ⟶ (pointifyHom snd g s hs).toFunctor.obj w' :=
      { toFun := fun a => g.toFunctor.map h₂ a, map_point := hcond }
    obtain ⟨k, hk, hu⟩ := hc.hom w w' h₁ h₂ HEq.rfl
    refine ⟨k, hk.2, fun k' hk' => hu k' ⟨?_, hk'⟩⟩
    apply Pointed.Hom.ext
    change g.toFunctor.map (snd.toFunctor.map k') = _
    rw [hk']
    rfl

end Pullback

end PointedForget
