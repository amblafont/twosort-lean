/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Limits.Comma
import CartexpAristotle.Lexp

/-!
# Comma categories as categories with a chosen exponentiable arrow

Let `F : C ⥤ C'` be a functor preserving pullbacks between categories with a chosen exponentiable
arrow `p : Y ⟶ X` in `C` and `p' : Y' ⟶ X'` in `C'`, and let `y : F Y ⟶ Y'`, `x : F X ⟶ X'` be
such that the square
```
F Y --y--> Y'
 |          |
F p         p'
 |          |
F X --x--> X'
```
is a pullback. Then the comma category `Comma F (𝟭 C')` is again a category with pullbacks and a
terminal object, and the morphism `(p, p') : (Y, Y', y) ⟶ (X, X', x)` is exponentiable. This gives
an `Lexp` structure on `Comma F (𝟭 C')` (`Lexp.comma`).

## References

* [Paper, App. A.3, Prop. `prop:comma-lexp`] (`Lexp`-structure on the comma category `F/C`):
  `Lexp.comma`. This is the key ingredient of the proof of
  [Paper, §2.2, Thm. `thm:universal-property-natural-transformation`].
-/

open CategoryTheory Limits

namespace CommaLexp

universe v₁ v₂ u₁ u₂

section Generic

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C'] {F : C ⥤ C'}

/-- A `ChosenPullback` from a pullback square. -/
noncomputable abbrev chosenPullbackOfIsPullback {X₁ X₂ S P : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    {p₁ : P ⟶ X₁} {p₂ : P ⟶ X₂} (h : IsPullback p₁ p₂ f₁ f₂) : ChosenPullback f₁ f₂ where
  pullback := P
  p₁ := p₁
  p₂ := p₂
  condition := h.w
  isLimit := h.isLimit

/-- A square in `Comma F (𝟭 C')` is a pullback if it is so componentwise. -/
lemma isPullback_comma {A B S P : Comma F (𝟭 C')} {m₁ : A ⟶ S} {m₂ : B ⟶ S} {q₁ : P ⟶ A}
    {q₂ : P ⟶ B} (w : q₁ ≫ m₁ = q₂ ≫ m₂) (hL : IsPullback q₁.left q₂.left m₁.left m₂.left)
    (hR : IsPullback q₁.right q₂.right m₁.right m₂.right) : IsPullback q₁ q₂ m₁ m₂ := by
  have wL : q₁.left ≫ m₁.left = q₂.left ≫ m₂.left := congrArg CommaMorphism.left w
  have wR : q₁.right ≫ m₁.right = q₂.right ≫ m₂.right := congrArg CommaMorphism.right w
  have key : ∀ s : PullbackCone m₁ m₂,
      F.map (hL.lift s.fst.left s.snd.left (by simpa using congrArg CommaMorphism.left s.condition))
        ≫ P.hom =
      s.pt.hom ≫ hR.lift s.fst.right s.snd.right
        (by simpa using congrArg CommaMorphism.right s.condition) := fun s => by
    refine hR.hom_ext ?_ ?_
    · have h1 := q₁.w
      have h2 := s.fst.w
      simp only [Functor.id_map] at h1 h2
      simp only [Category.assoc, IsPullback.lift_fst]
      rw [← h1, ← F.map_comp_assoc, hL.lift_fst]
      exact h2
    · have h1 := q₂.w
      have h2 := s.snd.w
      simp only [Functor.id_map] at h1 h2
      simp only [Category.assoc, IsPullback.lift_snd]
      rw [← h1, ← F.map_comp_assoc, hL.lift_snd]
      exact h2
  refine IsPullback.of_isLimit (c := PullbackCone.mk q₁ q₂ w) (PullbackCone.IsLimit.mk w
    (fun s => ⟨hL.lift s.fst.left s.snd.left
        (by simpa using congrArg CommaMorphism.left s.condition),
      hR.lift s.fst.right s.snd.right (by simpa using congrArg CommaMorphism.right s.condition),
      key s⟩) ?_ ?_ ?_)
  · intro s
    exact CommaMorphism.ext (by simp) (by simp)
  · intro s
    exact CommaMorphism.ext (by simp) (by simp)
  · intro s m h₁ h₂
    refine CommaMorphism.ext (hL.hom_ext ?_ ?_) (hR.hom_ext ?_ ?_)
    · simpa using congrArg CommaMorphism.left h₁
    · simpa using congrArg CommaMorphism.left h₂
    · simpa using congrArg CommaMorphism.right h₁
    · simpa using congrArg CommaMorphism.right h₂

section
variable [HasPullbacks C] [HasPullbacks C']

noncomputable instance : PreservesLimitsOfShape WalkingCospan (Comma.fst F (𝟭 C')) where
  preservesLimit := preservesLimit_of_preserves_limit_cone
    (Comma.coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)) (limit.isLimit _)

noncomputable instance : PreservesLimitsOfShape WalkingCospan (Comma.snd F (𝟭 C')) where
  preservesLimit := preservesLimit_of_preserves_limit_cone
    (Comma.coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)) (limit.isLimit _)

variable {A B S : Comma F (𝟭 C')} {m₁ : A ⟶ S} {m₂ : B ⟶ S}

lemma isPullback_left (K : ChosenPullback m₁ m₂) :
    IsPullback K.p₁.left K.p₂.left m₁.left m₂.left :=
  Functor.map_isPullback (Comma.fst F (𝟭 C')) K.isPullback

lemma isPullback_right (K : ChosenPullback m₁ m₂) :
    IsPullback K.p₁.right K.p₂.right m₁.right m₂.right :=
  Functor.map_isPullback (Comma.snd F (𝟭 C')) K.isPullback

/-- The left component of a chosen pullback in the comma category. -/
noncomputable abbrev leftChosen (K : ChosenPullback m₁ m₂) : ChosenPullback m₁.left m₂.left :=
  chosenPullbackOfIsPullback (isPullback_left K)

/-- The right component of a chosen pullback in the comma category. -/
noncomputable abbrev rightChosen (K : ChosenPullback m₁ m₂) : ChosenPullback m₁.right m₂.right :=
  chosenPullbackOfIsPullback (isPullback_right K)

end

variable {A B S : Comma F (𝟭 C')} {m₁ : A ⟶ S} {m₂ : B ⟶ S}

/-- The componentwise lift of the pullback of `m₁.right` and `m₂.right` -/
noncomputable def pullbackHom (K : ChosenPullback m₁.left m₂.left)
    (K' : ChosenPullback m₁.right m₂.right) : F.obj K.pullback ⟶ K'.pullback :=
  K'.isPullback.lift (F.map K.p₁ ≫ A.hom) (F.map K.p₂ ≫ B.hom) (by
    have h₁ := m₁.w
    have h₂ := m₂.w
    simp only [Functor.id_map] at h₁ h₂
    rw [Category.assoc, Category.assoc, ← h₁, ← h₂, ← F.map_comp_assoc, ← F.map_comp_assoc,
      K.condition])

/-- A chosen pullback in a comma category from chosen pullbacks of the components. -/
noncomputable def chosenPullbackOfComponents (K : ChosenPullback m₁.left m₂.left)
    (K' : ChosenPullback m₁.right m₂.right) : ChosenPullback m₁ m₂ :=
  chosenPullbackOfIsPullback (P := ⟨K.pullback, K'.pullback, pullbackHom K K'⟩)
    (p₁ := ⟨K.p₁, K'.p₁, by simp [pullbackHom]⟩) (p₂ := ⟨K.p₂, K'.p₂, by simp [pullbackHom]⟩)
    (isPullback_comma (by ext <;> simp [K.condition, K'.condition]) K.isPullback K'.isPullback)

end Generic

section Exponentiable

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C'] (F : C ⥤ C')
  [PreservesLimitsOfShape WalkingCospan F] {Y X : C} (u : Y ⟶ X) {Y' X' : C'} (u' : Y' ⟶ X')
  [IsExpArr u] [IsExpArr u'] {y : F.obj Y ⟶ Y'} {x : F.obj X ⟶ X'}
  (hsq : IsPullback y (F.map u) u' x)

/-- The object `(Y, Y', y)` of the comma category. -/
@[reducible] def commaDom (y : F.obj Y ⟶ Y') : Comma F (𝟭 C') := ⟨Y, Y', y⟩

/-- The object `(X, X', x)` of the comma category. -/
@[reducible] def commaCod (x : F.obj X ⟶ X') : Comma F (𝟭 C') := ⟨X, X', x⟩

include hsq in
/-- The morphism `(u, u')` of the comma category. -/
def commaArr : commaDom F y ⟶ commaCod F x := ⟨u, u', by simpa using hsq.w.symm⟩

include hsq in
/-- Pasting the pullback square `hsq` with the image of a chosen pullback. -/
noncomputable abbrev pastePullback {d : C} {a : d ⟶ X} (K : ChosenPullback u a) :
    ChosenPullback u' (F.map a ≫ x) :=
  chosenPullbackOfIsPullback (IsPullback.paste_horiz (Functor.map_isPullback F K.isPullback) hsq)

/-- The chosen exponential data of `u` at `c`. -/
abbrev dataL (c : C) : Data u c := IsExpArr.isExpArrowData (u := u) c

/-- The chosen exponential data of `u'` at `c'`. -/
abbrev dataR (c' : C') : Data u' c' := IsExpArr.isExpArrowData (u := u') c'

variable {c : C} {c' : C'} (f : F.obj c ⟶ c')

/-- The map `F (Π_u c) ⟶ Π_{u'} c'` underlying the exponential of `(c, c', f)`. -/
noncomputable def phi : F.obj (dataL u c).P ⟶ (dataR u' c').P :=
  Universal.mor (data := dataR u' c') (Kuf := pastePullback F u u' hsq (dataL u c).Pbk)
    (F.map (dataL u c).epsilon ≫ f)

lemma phi_slice : F.map (dataL u c).pi ≫ x = phi F u u' hsq f ≫ (dataR u' c').pi :=
  Universal.isSlice (data := dataR u' c') (Kuf := pastePullback F u u' hsq (dataL u c).Pbk)
    (F.map (dataL u c).epsilon ≫ f)

/-- The object `(Π_u c, Π_{u'} c', φ)` of the comma category. -/
@[reducible] noncomputable def commaP : Comma F (𝟭 C') :=
  ⟨(dataL u c).P, (dataR u' c').P, phi F u u' hsq f⟩

/-- The structure map of `commaP` to `(X, X', x)`. -/
noncomputable def commaPi : commaP F u u' hsq f ⟶ commaCod F x :=
  ⟨(dataL u c).pi, (dataR u' c').pi, by simpa using phi_slice F u u' hsq f⟩

lemma phi_comm : F.map (dataL u c).epsilon ≫ f =
    pullbackHom (m₁ := commaArr F u u' hsq) (m₂ := commaPi F u u' hsq f)
      (dataL u c).Pbk (dataR u' c').Pbk ≫ (dataR u' c').epsilon :=
  Universal.comm (data := dataR u' c') (Kuf := pastePullback F u u' hsq (dataL u c).Pbk)
    (F.map (dataL u c).epsilon ≫ f)

/-- The exponential data of `(u, u')` at `(c, c', f)`. -/
noncomputable def commaData : Data (commaArr F u u' hsq) (⟨c, c', f⟩ : Comma F (𝟭 C')) where
  P := commaP F u u' hsq f
  pi := commaPi F u u' hsq f
  Pbk := chosenPullbackOfComponents (dataL u c).Pbk (dataR u' c').Pbk
  epsilon := ⟨(dataL u c).epsilon, (dataR u' c').epsilon, phi_comm F u u' hsq f⟩

section Universal

set_option linter.unusedSectionVars false

variable [HasPullbacks C] [HasPullbacks C'] {d : Comma F (𝟭 C')} {a : d ⟶ commaCod F x}
  (K : ChosenPullback (commaArr F u u' hsq) a) (g : K.pullback ⟶ ⟨c, c', f⟩)

lemma FBF_on_mor_p₁ {C : Type*} [Category C] {X Y c : C} {u : Y ⟶ X} (data : Data u c) {d : C}
    {f : d ⟶ data.P} {h : d ⟶ X} (Kufp : ChosenPullback u h) (eq_fp : h = f ≫ data.pi) :
    FBF_on_mor data Kufp eq_fp ≫ data.Pbk.p₁ = Kufp.p₁ :=
  IsPullback.lift_fst _ _ _ _

lemma FBF_on_mor_p₂ {C : Type*} [Category C] {X Y c : C} {u : Y ⟶ X} (data : Data u c) {d : C}
    {f : d ⟶ data.P} {h : d ⟶ X} (Kufp : ChosenPullback u h) (eq_fp : h = f ≫ data.pi) :
    FBF_on_mor data Kufp eq_fp ≫ data.Pbk.p₂ = Kufp.p₂ ≫ f :=
  IsPullback.lift_snd _ _ _ _

lemma pastePullback_p₁ {d : C} {a : d ⟶ X} (K : ChosenPullback u a) :
    (pastePullback F u u' hsq K).p₁ = F.map K.p₁ ≫ y := rfl

lemma pastePullback_p₂ {d : C} {a : d ⟶ X} (K : ChosenPullback u a) :
    (pastePullback F u u' hsq K).p₂ = F.map K.p₂ := rfl

/-- The left component of a chosen pullback, with the expected type. -/
noncomputable abbrev chosenL : ChosenPullback u a.left := leftChosen K

/-- The right component of a chosen pullback, with the expected type. -/
noncomputable abbrev chosenR : ChosenPullback u' a.right := rightChosen K

/-- `pullbackHom` for the pair of chosen pullbacks of exponentials, with the expected type. -/
noncomputable def pbHom : F.obj (dataL u c).Pbk.pullback ⟶ (dataR u' c').Pbk.pullback :=
  pullbackHom (m₁ := commaArr F u u' hsq) (m₂ := commaPi F u u' hsq f)
    (dataL u c).Pbk (dataR u' c').Pbk

lemma pbHom_p₁ : pbHom F u u' hsq f ≫ (dataR u' c').Pbk.p₁ = F.map (dataL u c).Pbk.p₁ ≫ y :=
  IsPullback.lift_fst _ _ _ _

lemma pbHom_p₂ :
    pbHom F u u' hsq f ≫ (dataR u' c').Pbk.p₂ = F.map (dataL u c).Pbk.p₂ ≫ phi F u u' hsq f :=
  IsPullback.lift_snd _ _ _ _

lemma phi_comm' : F.map (dataL u c).epsilon ≫ f = pbHom F u u' hsq f ≫ (dataR u' c').epsilon :=
  phi_comm F u u' hsq f

/-- The structure map of the pullback object of `K`, with the expected type. -/
noncomputable abbrev homK : F.obj K.pullback.left ⟶ K.pullback.right := K.pullback.hom

/-- The left component of the morphism into the exponential. -/
noncomputable def morL : d.left ⟶ (dataL u c).P :=
  Universal.mor (data := dataL u c) (Kuf := chosenL F u u' hsq K) g.left

/-- The right component of the morphism into the exponential. -/
noncomputable def morR : d.right ⟶ (dataR u' c').P :=
  Universal.mor (data := dataR u' c') (Kuf := chosenR F u u' hsq K) g.right

lemma morL_slice : a.left = morL F u u' hsq f K g ≫ (dataL u c).pi :=
  Universal.isSlice (data := dataL u c) (Kuf := chosenL F u u' hsq K) g.left

lemma morR_slice : a.right = morR F u u' hsq f K g ≫ (dataR u' c').pi :=
  Universal.isSlice (data := dataR u' c') (Kuf := chosenR F u u' hsq K) g.right

lemma morL_phi_slice : F.map a.left ≫ x =
    (F.map (morL F u u' hsq f K g) ≫ phi F u u' hsq f) ≫ (dataR u' c').pi := by
  rw [Category.assoc, ← phi_slice, ← F.map_comp_assoc, ← morL_slice]

lemma morR_slice' : F.map a.left ≫ x = (d.hom ≫ morR F u u' hsq f K g) ≫ (dataR u' c').pi := by
  rw [Category.assoc, ← morR_slice]
  simpa using a.w

lemma lhs_eq : FBF_on_mor (dataR u' c') (pastePullback F u u' hsq (chosenL F u u' hsq K))
      (morL_phi_slice F u u' hsq f K g) ≫ (dataR u' c').epsilon = F.map g.left ≫ f := by
  have hΦ := Universal.comm (data := dataL u c) (Kuf := chosenL F u u' hsq K) g.left
  have h1 : FBF_on_mor (dataR u' c') (pastePullback F u u' hsq (chosenL F u u' hsq K))
      (morL_phi_slice F u u' hsq f K g) =
      F.map (FBF_on_mor (dataL u c) (chosenL F u u' hsq K) (morL_slice F u u' hsq f K g)) ≫
        pbHom F u u' hsq f := by
    refine (dataR u' c').Pbk.isPullback.hom_ext ?_ ?_
    · rw [FBF_on_mor_p₁, Category.assoc, pbHom_p₁, pastePullback_p₁, ← F.map_comp_assoc,
        FBF_on_mor_p₁]
    · rw [FBF_on_mor_p₂, Category.assoc, pbHom_p₂, pastePullback_p₂,
        ← F.map_comp_assoc, ← F.map_comp_assoc, FBF_on_mor_p₂]
  have h2 : (F.map (FBF_on_mor (dataL u c) (chosenL F u u' hsq K) (morL_slice F u u' hsq f K g)) ≫
      pbHom F u u' hsq f) ≫ (dataR u' c').epsilon = F.map g.left ≫ f := by
    rw [Category.assoc, ← phi_comm', ← F.map_comp_assoc]
    exact congrArg (fun t => F.map t ≫ f) hΦ.symm
  exact (congrArg (· ≫ (dataR u' c').epsilon) h1).trans h2

lemma rhs_eq : FBF_on_mor (dataR u' c') (pastePullback F u u' hsq (chosenL F u u' hsq K))
      (morR_slice' F u u' hsq f K g) ≫ (dataR u' c').epsilon = F.map g.left ≫ f := by
  have hΨ := Universal.comm (data := dataR u' c') (Kuf := chosenR F u u' hsq K) g.right
  have h1 : FBF_on_mor (dataR u' c') (pastePullback F u u' hsq (chosenL F u u' hsq K))
      (morR_slice' F u u' hsq f K g) =
      homK F u u' hsq K ≫
        FBF_on_mor (dataR u' c') (chosenR F u u' hsq K) (morR_slice F u u' hsq f K g) := by
    refine (dataR u' c').Pbk.isPullback.hom_ext ?_ ?_
    · rw [FBF_on_mor_p₁, pastePullback_p₁]
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      rw [FBF_on_mor_p₁]
      simpa using K.p₁.w
    · rw [FBF_on_mor_p₂, pastePullback_p₂]
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      rw [FBF_on_mor_p₂]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ morR F u u' hsq f K g) K.p₂.w).trans (Category.assoc _ _ _))
  have h2 : (homK F u u' hsq K ≫ FBF_on_mor (dataR u' c') (chosenR F u u' hsq K)
      (morR_slice F u u' hsq f K g)) ≫ (dataR u' c').epsilon = F.map g.left ≫ f := by
    refine (Category.assoc _ _ _).trans
      ((congrArg (fun t => homK F u u' hsq K ≫ t) hΨ).symm.trans ?_)
    simpa using g.w.symm
  exact (congrArg (· ≫ (dataR u' c').epsilon) h1).trans h2

lemma mor_w : F.map (morL F u u' hsq f K g) ≫ phi F u u' hsq f = d.hom ≫ morR F u u' hsq f K g := by
  refine Universal.uniq (data := dataR u' c') (pastePullback F u u' hsq (chosenL F u u' hsq K))
    (morL_phi_slice F u u' hsq f K g) (morR_slice' F u u' hsq f K g) ?_
  exact (lhs_eq F u u' hsq f K g).trans (rhs_eq F u u' hsq f K g).symm

lemma FBF_left {m : d ⟶ (commaData F u u' hsq f).P}
    (h : a = m ≫ (commaData F u u' hsq f).pi) :
    (FBF_on_mor (commaData F u u' hsq f) K h).left =
      FBF_on_mor (dataL u c) (chosenL F u u' hsq K) (congrArg CommaMorphism.left h) := by
  refine (dataL u c).Pbk.isPullback.hom_ext ?_ ?_
  · refine Eq.trans ?_ (FBF_on_mor_p₁ (dataL u c) (chosenL F u u' hsq K)
      (congrArg CommaMorphism.left h)).symm
    exact congrArg CommaMorphism.left (FBF_on_mor_p₁ (commaData F u u' hsq f) K h)
  · refine Eq.trans ?_ (FBF_on_mor_p₂ (dataL u c) (chosenL F u u' hsq K)
      (congrArg CommaMorphism.left h)).symm
    exact congrArg CommaMorphism.left (FBF_on_mor_p₂ (commaData F u u' hsq f) K h)

lemma FBF_right {m : d ⟶ (commaData F u u' hsq f).P}
    (h : a = m ≫ (commaData F u u' hsq f).pi) :
    (FBF_on_mor (commaData F u u' hsq f) K h).right =
      FBF_on_mor (dataR u' c') (chosenR F u u' hsq K) (congrArg CommaMorphism.right h) := by
  refine (dataR u' c').Pbk.isPullback.hom_ext ?_ ?_
  · refine Eq.trans ?_ (FBF_on_mor_p₁ (dataR u' c') (chosenR F u u' hsq K)
      (congrArg CommaMorphism.right h)).symm
    exact congrArg CommaMorphism.right (FBF_on_mor_p₁ (commaData F u u' hsq f) K h)
  · refine Eq.trans ?_ (FBF_on_mor_p₂ (dataR u' c') (chosenR F u u' hsq K)
      (congrArg CommaMorphism.right h)).symm
    exact congrArg CommaMorphism.right (FBF_on_mor_p₂ (commaData F u u' hsq f) K h)

end Universal

section Universal'

variable [HasPullbacks C] [HasPullbacks C']

/-- The universality of the exponential data of `(u, u')` at `(c, c', f)`. -/
@[reducible]
noncomputable def commaUniversal : Universal (commaData F u u' hsq f) where
  mor := fun {d a K} g => ⟨morL F u u' hsq f K g, morR F u u' hsq f K g, mor_w F u u' hsq f K g⟩
  isSlice := fun {d a K} g =>
    CommaMorphism.ext (morL_slice F u u' hsq f K g) (morR_slice F u u' hsq f K g)
  comm := fun {d a K} g => by
    let m : d ⟶ commaP F u u' hsq f :=
      ⟨morL F u u' hsq f K g, morR F u u' hsq f K g, mor_w F u u' hsq f K g⟩
    refine CommaMorphism.ext ?_ ?_
    · refine (Universal.comm (data := dataL u c) (Kuf := chosenL F u u' hsq K) g.left).trans ?_
      exact congrArg (· ≫ (dataL u c).epsilon) (FBF_left F u u' hsq f K (m := m) _).symm
    · refine (Universal.comm (data := dataR u' c') (Kuf := chosenR F u u' hsq K) g.right).trans ?_
      exact congrArg (· ≫ (dataR u' c').epsilon) (FBF_right F u u' hsq f K (m := m) _).symm
  uniq := fun {d f₁ f₂ h} K eq_fp eq_gp eq_eps => by
    have hl : (FBF_on_mor (commaData F u u' hsq f) K eq_fp).left ≫ (dataL u c).epsilon =
        (FBF_on_mor (commaData F u u' hsq f) K eq_gp).left ≫ (dataL u c).epsilon :=
      congrArg CommaMorphism.left eq_eps
    have hr : (FBF_on_mor (commaData F u u' hsq f) K eq_fp).right ≫ (dataR u' c').epsilon =
        (FBF_on_mor (commaData F u u' hsq f) K eq_gp).right ≫ (dataR u' c').epsilon :=
      congrArg CommaMorphism.right eq_eps
    rw [FBF_left, FBF_left] at hl
    rw [FBF_right, FBF_right] at hr
    exact CommaMorphism.ext
      (Universal.uniq (data := dataL u c) (chosenL F u u' hsq K) _ _ hl)
      (Universal.uniq (data := dataR u' c') (chosenR F u u' hsq K) _ _ hr)

/-- The morphism `(u, u')` is exponentiable in the comma category. -/
@[reducible]
noncomputable def commaIsExpArr : IsExpArr (commaArr F u u' hsq) where
  isExpArrowData := fun c => commaData F u u' hsq c.hom
  isExpArrow := fun c => commaUniversal F u u' hsq c.hom

end Universal'

end Exponentiable

end CommaLexp

open CommaLexp in
/-- Given a functor `F : C ⥤ C'` preserving pullbacks between categories with pullbacks and a
terminal object, with exponentiable arrows `u : Y ⟶ X` and `u' : Y' ⟶ X'` and maps
`y : F Y ⟶ Y'`, `x : F X ⟶ X'` making the evident square a pullback, the comma category
`Comma F (𝟭 C')` is a category with a chosen exponentiable arrow, namely `(u, u')`.

[Paper, App. A.3, Prop. `prop:comma-lexp`]. -/
noncomputable def Lexp.comma {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] [HasTerminal C]
    {C' : Type u₂} [Category.{v₂} C'] [HasPullbacks C'] [HasTerminal C'] (F : C ⥤ C')
    [PreservesLimitsOfShape WalkingCospan F] {Y X : C} (u : Y ⟶ X) {Y' X' : C'} (u' : Y' ⟶ X')
    [IsExpArr u] [IsExpArr u'] {y : F.obj Y ⟶ Y'} {x : F.obj X ⟶ X'}
    (hsq : IsPullback y (F.map u) u' x) : Lexp.{max v₁ v₂, max u₁ u₂ v₂} where
  carrier := Comma F (𝟭 C')
  arr := commaArr F u u' hsq
  isExpArr := commaIsExpArr F u u' hsq
