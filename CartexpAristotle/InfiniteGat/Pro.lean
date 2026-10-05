/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib

/-!
# The pro-completion of a small category

For a small category `C`, the pro-completion (free cofiltered-limit completion) of `C` is
`Pro C = (Ind Cᵒᵖ)ᵒᵖ`, with the embedding `proYoneda C : C ⥤ Pro C`.

We record the basic properties used in the proof of [Paper, App., Thm. `thm:infinite-GATs`]:

* if `C` has finite limits, `Pro C` has all small limits and `proYoneda C` preserves finite limits
  ([Paper, App., Prop. `prop:free-filtered-preserves-lim`]);
* `proYoneda C` is fully faithful;
* the objects `proYoneda C c` are *co-compact*: morphisms from a small cofiltered limit to
  `proYoneda C c` factor through a stage of the limit, essentially uniquely (`proYoneda_cc_exists`,
  `proYoneda_cc_eq`);
* `proYoneda C` is *codense*: every object `A` is the limit of the canonical diagram
  `StructuredArrow A (proYoneda C) ⥤ Pro C` (`proYoneda_codense`);
* if `C` has finite limits, the categories `StructuredArrow A (proYoneda C)` are cofiltered.
-/

open CategoryTheory Limits Opposite

universe w

namespace InfiniteGat

variable (C : Type w) [SmallCategory C]

/-- The pro-completion `Pro C = (Ind Cᵒᵖ)ᵒᵖ` of a small category `C`.

[Paper, App., §Infinite GATs]: the free filtered (limit) completion of `C`. -/
abbrev Pro : Type (w + 1) := (Ind Cᵒᵖ)ᵒᵖ

/-- The embedding `C ⥤ Pro C`. -/
noncomputable def proYoneda : C ⥤ Pro C := (Ind.yoneda (C := Cᵒᵖ)).rightOp

instance : (proYoneda C).Full := by unfold proYoneda; infer_instance

instance : (proYoneda C).Faithful := by unfold proYoneda; infer_instance

instance [HasFiniteLimits C] : HasLimitsOfSize.{w, w} (Pro C) := inferInstance

instance [HasFiniteLimits C] : PreservesFiniteLimits (proYoneda C) := by
  unfold proYoneda
  exact preservesFiniteLimits_rightOp _

instance [HasFiniteLimits C] : HasFiniteLimits (Pro C) := inferInstance

variable {C}

/-! ### Elements of ind-objects -/

/-- Morphisms from a representable ind-object are elements of the underlying presheaf. -/
noncomputable def indHomEquiv (k : Cᵒᵖ) (X : Ind Cᵒᵖ) :
    (Ind.yoneda.obj k ⟶ X) ≃ ((Ind.inclusion Cᵒᵖ).obj X).obj (op k) :=
  Ind.inclusion.fullyFaithful.homEquiv.trans
    (((Ind.yonedaCompInclusion.app k).homCongr (Iso.refl _)).trans yonedaEquiv)

lemma indHomEquiv_comp (k : Cᵒᵖ) {X X' : Ind Cᵒᵖ} (f : Ind.yoneda.obj k ⟶ X) (g : X ⟶ X') :
    indHomEquiv k X' (f ≫ g) = ((Ind.inclusion Cᵒᵖ).map g).app _ (indHomEquiv k X f) := by
  simp only [indHomEquiv, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply]
  dsimp [Iso.homCongr]
  simp only [Functor.map_comp, Category.comp_id, ← Category.assoc, yonedaEquiv_comp]

lemma indHomEquiv_naturality {k k' : Cᵒᵖ} (φ : k' ⟶ k) (X : Ind Cᵒᵖ)
    (f : Ind.yoneda.obj k ⟶ X) :
    indHomEquiv k' X (Ind.yoneda.map φ ≫ f) =
      ((Ind.inclusion Cᵒᵖ).obj X).map φ.op (indHomEquiv k X f) := by
  simp only [indHomEquiv, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply]
  dsimp [Iso.homCongr]
  have := Ind.yonedaCompInclusion.inv.naturality φ
  simp only [Functor.comp_map] at this
  simp only [Category.comp_id, Functor.map_comp]
  rw [← Category.assoc, ← this, Category.assoc, yonedaEquiv_naturality]

/-- Morphisms into `proYoneda C c` are elements of the underlying presheaf. -/
noncomputable def proHomEquiv (A : Pro C) (c : C) :
    (A ⟶ (proYoneda C).obj c) ≃ ((Ind.inclusion Cᵒᵖ).obj A.unop).obj (op (op c)) :=
  (opEquiv A _).trans (indHomEquiv (op c) A.unop)

lemma proHomEquiv_comp {A A' : Pro C} (g : A' ⟶ A) (c : C) (f : A ⟶ (proYoneda C).obj c) :
    proHomEquiv A' c (g ≫ f) =
      ((Ind.inclusion Cᵒᵖ).map g.unop).app _ (proHomEquiv A c f) := by
  simp only [proHomEquiv, Equiv.trans_apply, opEquiv_apply, unop_comp]
  exact indHomEquiv_comp _ _ _

lemma proHomEquiv_naturality (A : Pro C) {c c' : C} (φ : c ⟶ c')
    (f : A ⟶ (proYoneda C).obj c) :
    proHomEquiv A c' (f ≫ (proYoneda C).map φ) =
      ((Ind.inclusion Cᵒᵖ).obj A.unop).map φ.op.op (proHomEquiv A c f) := by
  simp only [proHomEquiv, Equiv.trans_apply, opEquiv_apply, unop_comp]
  exact indHomEquiv_naturality φ.op _ _

/-! ### Co-compactness of the representable pro-objects -/

section CoCompact

variable {K : Type w} [SmallCategory K] [IsCofiltered K] {B : K ⥤ Pro C} {L : Cone B}
  (hL : IsLimit L)

include hL in
/-- The cocone of elements associated to a cofiltered limit in `Pro C` is a colimit. -/
lemma proYoneda_cc_isColimit (c : C) :
    Nonempty (IsColimit ((Ind.inclusion Cᵒᵖ ⋙ (evaluation _ _).obj (op (op c))).mapCocone
      (coconeLeftOpOfCone L))) :=
  ⟨isColimitOfPreserves _ (isColimitCoconeLeftOpOfCone B hL)⟩

include hL in
/-- Every morphism from a cofiltered limit to `proYoneda C c` factors through a stage. -/
lemma proYoneda_cc_exists {c : C} (g : L.pt ⟶ (proYoneda C).obj c) :
    ∃ (k : K) (g' : B.obj k ⟶ (proYoneda C).obj c), g = L.π.app k ≫ g' := by
  obtain ⟨hT⟩ := proYoneda_cc_isColimit hL c
  obtain ⟨k, x, hx⟩ := Types.jointly_surjective_of_isColimit hT (proHomEquiv L.pt c g)
  refine ⟨k.unop, (proHomEquiv (B.obj k.unop) c).symm x, ?_⟩
  apply (proHomEquiv L.pt c).injective
  rw [proHomEquiv_comp, Equiv.apply_symm_apply, ← hx]
  rfl

include hL in
/-- Two morphisms from a stage of a cofiltered limit to `proYoneda C c` which agree on the limit
agree at an earlier stage. -/
lemma proYoneda_cc_eq {c : C} {k : K} (g g' : B.obj k ⟶ (proYoneda C).obj c)
    (h : L.π.app k ≫ g = L.π.app k ≫ g') :
    ∃ (k' : K) (t : k' ⟶ k), B.map t ≫ g = B.map t ≫ g' := by
  obtain ⟨hT⟩ := proYoneda_cc_isColimit hL c
  have h' := congrArg (proHomEquiv L.pt c) h
  rw [proHomEquiv_comp, proHomEquiv_comp] at h'
  obtain ⟨k'', f₁, f₂, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hT).1 h'
  refine ⟨IsCofiltered.eq f₁.unop f₂.unop, IsCofiltered.eqHom f₁.unop f₂.unop ≫ f₁.unop, ?_⟩
  have hf' : B.map f₁.unop ≫ g = B.map f₂.unop ≫ g' := by
    apply (proHomEquiv _ c).injective
    rw [proHomEquiv_comp, proHomEquiv_comp]
    exact hf
  rw [B.map_comp, Category.assoc, hf', ← Category.assoc, ← B.map_comp,
    ← IsCofiltered.eq_condition, B.map_comp, Category.assoc]

end CoCompact

/-! ### Codensity -/

/-- `proYoneda C` is codense: every object of `Pro C` is the canonical limit of the objects
`proYoneda C c` under it. -/
noncomputable def proYonedaCodenseAt (A : Pro C) :
    (Functor.RightExtension.mk (𝟭 (Pro C)) (proYoneda C).rightUnitor.hom).IsPointwiseRightKanExtensionAt
      A where
  lift s := by
    refine (Ind.inclusion.fullyFaithful.preimage
      { app := fun (k : Cᵒᵖᵒᵖ) x => proHomEquiv s.pt k.unop.unop
          (show s.pt ⟶ (proYoneda C).obj k.unop.unop from
            s.π.app (StructuredArrow.mk ((proHomEquiv A k.unop.unop).symm x)))
        naturality := ?_ }).op
    intro k k' ψ
    ext x
    obtain ⟨f, rfl⟩ := (proHomEquiv A k.unop.unop).surjective x
    dsimp
    have e := proHomEquiv_naturality A ψ.unop.unop f
    erw [← e]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hw := s.w (StructuredArrow.homMk (f := StructuredArrow.mk f)
      (f' := StructuredArrow.mk (f ≫ (proYoneda C).map ψ.unop.unop)) ψ.unop.unop rfl)
    dsimp at hw
    rw [← hw, proHomEquiv_naturality]
    rfl
  fac s g := by
    apply (proHomEquiv s.pt g.right).injective
    dsimp
    rw [Category.comp_id, proHomEquiv_comp]
    simp only [Quiver.Hom.unop_op, Functor.FullyFaithful.map_preimage]
    rw [Equiv.symm_apply_apply]
    rfl
  uniq s m hm := by
    apply Quiver.Hom.unop_inj
    apply (Ind.inclusion Cᵒᵖ).map_injective
    ext k x
    obtain ⟨f, rfl⟩ := (proHomEquiv A k.unop.unop).surjective x
    simp only [Quiver.Hom.unop_op, Functor.FullyFaithful.map_preimage]
    dsimp
    rw [Equiv.symm_apply_apply, ← hm (StructuredArrow.mk f)]
    dsimp
    rw [Category.comp_id, proHomEquiv_comp]

/-- `proYoneda C` is codense. -/
noncomputable def proYonedaCodense :
    (Functor.RightExtension.mk (𝟭 (Pro C)) (proYoneda C).rightUnitor.hom).IsPointwiseRightKanExtension :=
  fun A => proYonedaCodenseAt A

/-! ### Cofilteredness -/

instance [HasFiniteLimits C] (A : Pro C) : HasFiniteLimits (StructuredArrow A (proYoneda C)) :=
  ⟨fun _ _ _ => inferInstance⟩

instance [HasFiniteLimits C] (A : Pro C) : IsCofiltered (StructuredArrow A (proYoneda C)) :=
  IsCofiltered.of_hasFiniteLimits _

end InfiniteGat
