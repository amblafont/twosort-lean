/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InfiniteGat.Pro

/-!
# The universal property of the pro-completion

Let `C` be a small category with finite limits and `D` a category with all small limits.

* Every functor `H : Pro C ⥤ D` preserving small limits is the pointwise right Kan extension of
  its restriction `proYoneda C ⋙ H` (`isPointwiseRightKanExtension_of_preservesLimits`); hence
  natural transformations `G ⟶ H` into such a functor correspond bijectively to natural
  transformations `proYoneda C ⋙ G ⟶ proYoneda C ⋙ H` (`proRestrictEquiv`).
* Every functor `F : C ⥤ D` extends along `proYoneda C` (`proExtend F`, a pointwise right Kan
  extension) with `proYoneda C ⋙ proExtend F ≅ F` (`proExtendIso`), and if `F` preserves finite
  limits then `proExtend F` preserves all small limits (`proExtend_preservesLimits`).

## References

* [Paper, App., Prop. `prop:carGATs`], [Paper, App., Prop. `prop:def-lex`] and
  [Paper, App., Prop. `prop:free-filtered-preserves-lim`] (via [Paper, App., Prop.
  `prop:lift-lexp-functor`]): the free filtered completion of a small Lex-category, and the fact
  that the extension of a finite-limit-preserving functor preserves all limits.
-/

open CategoryTheory Limits Opposite Functor

universe w u

namespace InfiniteGat

variable {C : Type w} [SmallCategory C]

section KanAux

variable {A' : Type*} {B' : Type*} {E' : Type*} {G' : Type*} [Category A'] [Category B']
  [Category E'] [Category G'] {L : A' ⥤ B'} {F : A' ⥤ E'}

/-- Postcomposing a pointwise right Kan extension with a functor preserving the relevant limit. -/
noncomputable def isPointwiseRightKanExtensionAt_postcomp {E : RightExtension L F} {b : B'}
    (hE : E.IsPointwiseRightKanExtensionAt b) (G : E' ⥤ G')
    [PreservesLimit (StructuredArrow.proj b L ⋙ F) G] :
    (RightExtension.mk (E.left ⋙ G) (whiskerRight E.hom G)).IsPointwiseRightKanExtensionAt b :=
  (isLimitOfPreserves G hE).ofIsoLimit (Cones.ext (Iso.refl _) (by simp))

/-- Changing the functor being extended along an isomorphism. -/
noncomputable def isPointwiseRightKanExtensionAt_compIso {F₂ : A' ⥤ E'} {E : RightExtension L F}
    {b : B'} (hE : E.IsPointwiseRightKanExtensionAt b) (e : F ≅ F₂) :
    (RightExtension.mk E.left (E.hom ≫ e.hom)).IsPointwiseRightKanExtensionAt b :=
  ((IsLimit.postcomposeHomEquiv (isoWhiskerLeft (StructuredArrow.proj b L) e) _).symm hE).ofIsoLimit
    (Cones.ext (Iso.refl _) (by simp))

end KanAux

variable {D : Type u} [Category.{w} D]

/-- A functor preserving small limits is the pointwise right Kan extension of its restriction
along `proYoneda C`. -/
noncomputable def isPointwiseRightKanExtension_of_preservesLimits (H : Pro C ⥤ D)
    [PreservesLimitsOfSize.{w, w} H] :
    (RightExtension.mk H (𝟙 (proYoneda C ⋙ H))).IsPointwiseRightKanExtension := fun A =>
  (isPointwiseRightKanExtensionAt_postcomp (proYonedaCodenseAt A) H).ofIsoLimit
    (Cones.ext (Iso.refl _) (by simp))

instance (H : Pro C ⥤ D) [PreservesLimitsOfSize.{w, w} H] :
    H.IsRightKanExtension (𝟙 (proYoneda C ⋙ H)) :=
  (isPointwiseRightKanExtension_of_preservesLimits H).isRightKanExtension

/-- Natural transformations into a limit-preserving functor `H : Pro C ⥤ D` are determined by
their restriction along `proYoneda C`. -/
noncomputable def proRestrictEquiv (G H : Pro C ⥤ D) [PreservesLimitsOfSize.{w, w} H] :
    (G ⟶ H) ≃ (proYoneda C ⋙ G ⟶ proYoneda C ⋙ H) :=
  Functor.homEquivOfIsRightKanExtension H (𝟙 (proYoneda C ⋙ H)) G

lemma proRestrictEquiv_apply (G H : Pro C ⥤ D) [PreservesLimitsOfSize.{w, w} H] (α : G ⟶ H) :
    proRestrictEquiv G H α = whiskerLeft (proYoneda C) α := by
  simp [proRestrictEquiv, homEquivOfIsRightKanExtension]

/-! ### The extension of a functor along `proYoneda C` -/

variable [HasLimitsOfSize.{w, w} D] (F : C ⥤ D)

/-- The extension of `F : C ⥤ D` to `Pro C`, as a pointwise right Kan extension. -/
noncomputable def proExtend : Pro C ⥤ D := (proYoneda C).pointwiseRightKanExtension F

/-- The counit `proYoneda C ⋙ proExtend F ⟶ F`. -/
noncomputable def proExtendCounit : proYoneda C ⋙ proExtend F ⟶ F :=
  (proYoneda C).pointwiseRightKanExtensionCounit F

/-- `proExtend F` is a pointwise right Kan extension. -/
noncomputable def proExtendIsPointwise :
    (RightExtension.mk (proExtend F) (proExtendCounit F)).IsPointwiseRightKanExtension :=
  (proYoneda C).pointwiseRightKanExtensionIsPointwiseRightKanExtension F

instance : IsIso (proExtendCounit F) :=
  (proExtendIsPointwise F).isIso_hom

/-- `proExtend F` extends `F`. -/
noncomputable def proExtendIso : proYoneda C ⋙ proExtend F ≅ F :=
  asIso (proExtendCounit F)

/-! ### Preservation of limits -/

section Preservation

variable [HasFiniteLimits C] [PreservesFiniteLimits F]

/-- The presheaf on `Cᵒᵖ` given by `c ↦ (T ⟶ F c)`. -/
def homPresheaf (T : D) : Cᵒᵖᵒᵖ ⥤ Type w := unopUnop C ⋙ F ⋙ coyoneda.obj (op T)

instance (T : D) : PreservesFiniteLimits (homPresheaf F T) := by
  unfold homPresheaf
  infer_instance

omit [HasLimitsOfSize.{w, w} D] in
lemma isIndObject_homPresheaf (T : D) : IsIndObject (homPresheaf F T) :=
  (isIndObject_iff_preservesFiniteLimits _).2 inferInstance

/-- The ind-object corresponding to `homPresheaf F T`. -/
noncomputable def homInd (T : D) : Ind Cᵒᵖ :=
  (Ind.equivalence Cᵒᵖ).inverse.obj ⟨homPresheaf F T, isIndObject_homPresheaf F T⟩

/-- The underlying presheaf of `homInd F T`. -/
noncomputable def homIndIso (T : D) : (Ind.inclusion Cᵒᵖ).obj (homInd F T) ≅ homPresheaf F T :=
  (ObjectProperty.ι _).mapIso ((Ind.equivalence Cᵒᵖ).counitIso.app _)

/-- The restriction of `yoneda.obj (homInd F T)` along `proYoneda C`. -/
noncomputable def homIndRestrictIso (T : D) :
    proYoneda C ⋙ yoneda.obj (homInd F T) ≅ F ⋙ coyoneda.obj (op T) :=
  NatIso.ofComponents (fun c => Equiv.toIso ((indHomEquiv (op c) (homInd F T)).trans
      (((homIndIso F T).app (op (op c))).toEquiv))) (by
    intro c c' φ
    ext (f : Ind.yoneda.obj (op c) ⟶ homInd F T)
    dsimp
    have h₁ := indHomEquiv_naturality φ.op (homInd F T) f
    have h₂ := congrFun ((homIndIso F T).hom.naturality φ.op.op)
      (indHomEquiv (op c) (homInd F T) f)
    dsimp [proYoneda] at h₁ h₂ ⊢
    rw [h₁]
    exact h₂)

/-- `proExtend F ⋙ coyoneda.obj (op T)` is representable. -/
noncomputable def proExtendCoyonedaIso (T : D) :
    proExtend F ⋙ coyoneda.obj (op T) ≅ yoneda.obj (homInd F T) := by
  let E₁ : RightExtension (proYoneda C) (F ⋙ coyoneda.obj (op T)) :=
    RightExtension.mk (proExtend F ⋙ coyoneda.obj (op T))
      (whiskerRight (proExtendCounit F) (coyoneda.obj (op T)))
  let E₂ : RightExtension (proYoneda C) (F ⋙ coyoneda.obj (op T)) :=
    RightExtension.mk (yoneda.obj (homInd F T)) (𝟙 _ ≫ (homIndRestrictIso F T).hom)
  have h₁ : E₁.IsPointwiseRightKanExtension := fun A =>
    isPointwiseRightKanExtensionAt_postcomp (proExtendIsPointwise F A) _
  have h₂ : E₂.IsPointwiseRightKanExtension := fun A =>
    isPointwiseRightKanExtensionAt_compIso
      (isPointwiseRightKanExtension_of_preservesLimits (yoneda.obj (homInd F T)) A) _
  exact (CostructuredArrow.proj _ _).mapIso (h₁.isUniversal.uniqueUpToIso h₂.isUniversal)

/-- **The extension of a finite-limit-preserving functor preserves all small limits.**

[Paper, App., Prop. `prop:lift-lexp-functor`] (preservation of limits). -/
instance proExtend_preservesLimits : PreservesLimitsOfSize.{w, w} (proExtend F) where
  preservesLimitsOfShape {J} _ := ⟨fun {K} => ⟨fun {c} hc => ⟨by
    refine coyonedaJointlyReflectsLimits _ _ (fun T => ?_)
    have : PreservesLimitsOfSize.{w, w} (proExtend F ⋙ coyoneda.obj T) :=
      preservesLimits_of_natIso (proExtendCoyonedaIso F T.unop).symm
    exact isLimitOfPreserves (proExtend F ⋙ coyoneda.obj T) hc⟩⟩⟩

end Preservation

end InfiniteGat
