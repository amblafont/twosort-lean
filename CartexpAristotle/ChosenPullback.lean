module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
/-!
# Chosen pullbacks
A `ChosenPullback f₁ f₂` packages an object together with two projections forming a
pullback square over `f₁` and `f₂`. The pullback property is stored as a limit cone,
and repackaged as an `IsPullback` statement.
This module is a local stand-in for the `ChosenPullback` structure used by `Basic.lean`,
since `Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback` is not available in the
Mathlib version this project is pinned to.
-/
@[expose] public section
namespace CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C]
/-- A chosen pullback of `f₁` and `f₂`. -/
structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  /-- The pullback object. -/
  pullback : C
  /-- The first projection. -/
  p₁ : pullback ⟶ X₁
  /-- The second projection. -/
  p₂ : pullback ⟶ X₂
  condition : p₁ ≫ f₁ = p₂ ≫ f₂
  /-- The square is a limit cone. -/
  isLimit : IsLimit (PullbackCone.mk p₁ p₂ condition)
namespace ChosenPullback
variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
attribute [reassoc] condition
lemma isPullback (h : ChosenPullback f₁ f₂) : IsPullback h.p₁ h.p₂ f₁ f₂ :=
  IsPullback.of_isLimit h.isLimit
@[ext]
lemma hom_ext (h : ChosenPullback f₁ f₂) {Z : C} {a b : Z ⟶ h.pullback}
    (h₁ : a ≫ h.p₁ = b ≫ h.p₁) (h₂ : a ≫ h.p₂ = b ≫ h.p₂) : a = b :=
  h.isPullback.hom_ext h₁ h₂
end ChosenPullback
end CategoryTheory.Limits
