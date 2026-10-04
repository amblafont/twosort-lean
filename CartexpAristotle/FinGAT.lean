/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CommaExpArr

/-!
# Maps out of a bi-initial `ExpArrCat`

Let `FinGAT` be a bi-initial object of the 2-category `ExpArrCat`, with chosen exponentiable arrow
`p : Y ⟶ X`.  Given an `ExpArrCat` `C`, a pullback-preserving functor `F : FinGAT ⥤ C`, an
`ExpArrCat`-morphism `G : FinGAT ⟶ C` and a morphism `f : F p ⟶ G p` of arrows which forms a
pullback square, there is a unique natural transformation `F ⟶ G` restricting to `f`
(`ExpArrCat.IsBiInitial.existsUnique_natTrans`).
-/

open CategoryTheory Limits
namespace CategoryTheory.Comma
universe wJ' vA vB vT uA uB uT wJ
variable {J : Type wJ} [Category.{wJ'} J] {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {T : Type uT} [Category.{vT} T] {L : A ⥤ T} {R : B ⥤ T} {F : J ⥤ Comma L R}

/-- The projections of a comma category jointly reflect limits, provided `R` preserves the
limit of the second projection of the diagram. -/
noncomputable def fstSndJointlyReflectLimit {c : Cone F} [PreservesLimit (F ⋙ snd L R) R]
    (h₁ : IsLimit ((fst L R).mapCone c)) (h₂ : IsLimit ((snd L R).mapCone c)) : IsLimit c where
  lift s :=
    { left := h₁.lift ((fst L R).mapCone s)
      right := h₂.lift ((snd L R).mapCone s)
      w := (isLimitOfPreserves R h₂).hom_ext fun j => by
        have hc := (c.π.app j).w
        have hs := (s.π.app j).w
        have e₁ := h₁.fac ((fst L R).mapCone s) j
        have e₂ := h₂.fac ((snd L R).mapCone s) j
        simp only [Functor.mapCone_π_app, fst_map, snd_map, Functor.const_obj_obj,
          Functor.comp_obj, fst_obj, snd_obj] at e₁ e₂ hc hs
        simp only [Functor.mapCone_π_app, Functor.comp_obj, snd_obj, snd_map, Category.assoc]
        rw [← R.map_comp, e₂, ← hc, ← Category.assoc, ← L.map_comp, e₁, hs] }
  fac s j := by
    ext
    · exact h₁.fac ((fst L R).mapCone s) j
    · exact h₂.fac ((snd L R).mapCone s) j
  uniq s m hm := by
    ext
    · exact h₁.uniq ((fst L R).mapCone s) m.left fun j => congrArg CommaMorphism.left (hm j)
    · exact h₂.uniq ((snd L R).mapCone s) m.right fun j => congrArg CommaMorphism.right (hm j)

end CategoryTheory.Comma


/-- A `ChosenPullback` is determined by its pullback object and projections. -/
lemma ChosenPullback.eq_default {C : Type*} [Category C] {X₁ X₂ S : C} {f₁ : X₁ ⟶ S}
    {f₂ : X₂ ⟶ S} (h : ChosenPullback f₁ f₂) :
    h = { pullback := h.pullback, p₁ := h.p₁, p₂ := h.p₂, condition := h.condition,
          isLimit := h.isLimit } := by
  cases h
  rfl

/-- Two `ChosenPullback`s with the same object and projections are equal. -/
lemma ChosenPullback.ext_of_eq {C : Type*} [Category C] {X₁ X₂ S : C} {f₁ : X₁ ⟶ S}
    {f₂ : X₂ ⟶ S} {h h' : ChosenPullback f₁ f₂} (hpb : h.pullback = h'.pullback)
    (h1 : HEq h.p₁ h'.p₁) (h2 : HEq h.p₂ h'.p₂) : h = h' := by
  obtain ⟨pb, p1, p2, c, il⟩ := h
  obtain ⟨pb', p1', p2', c', il'⟩ := h'
  dsimp only at hpb h1 h2
  subst hpb
  cases h1
  cases h2
  congr
  exact Subsingleton.elim _ _

/-- The canonical comparison between two universal `Data` is an isomorphism. -/
lemma isIso_canonical_mor {C : Type*} [Category C] {Y X c : C} {u : Y ⟶ X}
    (d₁ d₂ : Data u c) [Universal d₁] [Universal d₂] : IsIso (canonical_mor d₁ d₂) :=
  ⟨canonical_mor d₂ d₁, canonical_mor_isIso d₁ d₂, canonical_mor_isIso d₂ d₁⟩

/-- `Universal.mor` only depends on the chosen pullback up to equality. -/
lemma Universal.mor_congr {C : Type*} [Category C] {Y X c : C} {u : Y ⟶ X} {d : Data u c}
    [Universal d] {e : C} {f : e ⟶ X} {K K' : ChosenPullback u f} (hK : K = K')
    (g : (K : C) ⟶ c) (g' : (K' : C) ⟶ c) (hg : HEq g g') :
    Universal.mor (data := d) (Kuf := K) g = Universal.mor (data := d) (Kuf := K') g' := by
  subst hK
  cases hg
  rfl

namespace CommaExpArr

universe v₁ v₂ u₁ u₂

/-- A morphism in a comma category with isomorphic components is an isomorphism. -/
lemma isIso_of_isIso_left_right {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
    {F : C ⥤ C'} {A B : Comma F (𝟭 C')} (m : A ⟶ B) [IsIso m.left] [IsIso m.right] : IsIso m :=
  ⟨⟨inv m.left, inv m.right, by
    have := m.w
    simp only [Functor.id_map] at this ⊢
    rw [Functor.map_inv, IsIso.inv_comp_eq, ← Category.assoc, this, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]⟩,
    CommaMorphism.ext (by simp) (by simp), CommaMorphism.ext (by simp) (by simp)⟩

section Preservation

variable {J : Type*} [Category J] {A : Type*} [Category A] {C : Type u₁} [Category.{v₁} C]
  {C' : Type u₂} [Category.{v₂} C'] {F : C ⥤ C'}

/-- The projections of a comma category jointly reflect preservation of limits. -/
lemma preservesLimitsOfShape_of_comp_fst_snd (H : A ⥤ Comma F (𝟭 C'))
    [PreservesLimitsOfShape J (H ⋙ Comma.fst F (𝟭 C'))]
    [PreservesLimitsOfShape J (H ⋙ Comma.snd F (𝟭 C'))] : PreservesLimitsOfShape J H where
  preservesLimit := ⟨fun {_} hc => ⟨Comma.fstSndJointlyReflectLimit
    (isLimitOfPreserves (H ⋙ Comma.fst F (𝟭 C')) hc)
    (isLimitOfPreserves (H ⋙ Comma.snd F (𝟭 C')) hc)⟩⟩

instance preservesLimitsOfShape_fst_of_hasLimits [HasLimitsOfShape J C] [HasLimitsOfShape J C'] :
    PreservesLimitsOfShape J (Comma.fst F (𝟭 C')) where
  preservesLimit := preservesLimit_of_preserves_limit_cone
    (Comma.coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)) (limit.isLimit _)

instance preservesLimitsOfShape_snd_of_hasLimits [HasLimitsOfShape J C] [HasLimitsOfShape J C'] :
    PreservesLimitsOfShape J (Comma.snd F (𝟭 C')) where
  preservesLimit := preservesLimit_of_preserves_limit_cone
    (Comma.coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)) (limit.isLimit _)

end Preservation

section Components

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {C' : Type u₂} [Category.{v₂} C']
  [HasPullbacks C'] (F : C ⥤ C') [PreservesLimitsOfShape WalkingCospan F] {Y X : C} (u : Y ⟶ X)
  {Y' X' : C'} (u' : Y' ⟶ X') [IsExpArr u] [IsExpArr u'] {y : F.obj Y ⟶ Y'} {x : F.obj X ⟶ X'}
  (hsq : IsPullback y (F.map u) u' x)

lemma canonical_comma_left {c : Comma F (𝟭 C')} (D : Data (commaArr F u u' hsq) c) :
    (@canonical_mor _ _ _ _ _ _ (commaData F u u' hsq c.hom) (commaUniversal F u u' hsq c.hom)
      D).left =
      canonical_mor (dataL u c.left) (functor_on (Comma.fst F (𝟭 C')) D) := by
  refine Universal.mor_congr ((ChosenPullback.eq_default _).trans
    (ChosenPullback.eq_default _).symm) _ _ HEq.rfl

lemma canonical_comma_right {c : Comma F (𝟭 C')} (D : Data (commaArr F u u' hsq) c) :
    (@canonical_mor _ _ _ _ _ _ (commaData F u u' hsq c.hom) (commaUniversal F u u' hsq c.hom)
      D).right =
      canonical_mor (dataR u' c.right) (functor_on (Comma.snd F (𝟭 C')) D) := by
  refine Universal.mor_congr ((ChosenPullback.eq_default _).trans
    (ChosenPullback.eq_default _).symm) _ _ HEq.rfl

/-- A `Data` in the comma category whose two components are universal is universal. -/
@[reducible]
noncomputable def universal_of_components {c : Comma F (𝟭 C')} (D : Data (commaArr F u u' hsq) c)
    (hL : Universal (functor_on (Comma.fst F (𝟭 C')) D))
    (hR : Universal (functor_on (Comma.snd F (𝟭 C')) D)) : Universal D := by
  have iL : IsIso (canonical_mor (dataL u c.left) (functor_on (Comma.fst F (𝟭 C')) D)) :=
    @isIso_canonical_mor _ _ _ _ _ _ _ _ _ hL
  have iR : IsIso (canonical_mor (dataR u' c.right) (functor_on (Comma.snd F (𝟭 C')) D)) :=
    @isIso_canonical_mor _ _ _ _ _ _ _ _ _ hR
  have h₁ := canonical_comma_left F u u' hsq D
  have h₂ := canonical_comma_right F u u' hsq D
  have iL' : IsIso (@canonical_mor _ _ _ _ _ _ (commaData F u u' hsq c.hom)
      (commaUniversal F u u' hsq c.hom) D).left := by rw [h₁]; exact iL
  have iR' : IsIso (@canonical_mor _ _ _ _ _ _ (commaData F u u' hsq c.hom)
      (commaUniversal F u u' hsq c.hom) D).right := by rw [h₂]; exact iR
  have : IsIso (@canonical_mor _ _ _ _ _ _ (commaData F u u' hsq c.hom)
      (commaUniversal F u u' hsq c.hom) D) := isIso_of_isIso_left_right _
  exact @canonical_mor_iso_lift _ _ _ _ _ _ (commaData F u u' hsq c.hom)
    (commaUniversal F u u' hsq c.hom) D this

variable {c : C} {c' : C'} (f : F.obj c ⟶ c')

lemma functor_on_fst_commaData :
    (functor_on (Comma.fst F (𝟭 C')) (commaData F u u' hsq f) : Data u c) = dataL u c := by
  change Data.mk _ _ _ _ = Data.mk _ _ _ _
  congr 1
  exact ChosenPullback.ext_of_eq rfl HEq.rfl HEq.rfl

lemma functor_on_snd_commaData :
    (functor_on (Comma.snd F (𝟭 C')) (commaData F u u' hsq f) : Data u' c') = dataR u' c' := by
  change Data.mk _ _ _ _ = Data.mk _ _ _ _
  congr 1
  exact ChosenPullback.ext_of_eq rfl HEq.rfl HEq.rfl

/-- The first projection of the comma category preserves exponentiable arrows. -/
@[reducible]
noncomputable def fstPreserves :
    FunctorPreserves (commaArr F u u' hsq) (Comma.fst F (𝟭 C')) :=
  functor_preserves_1_is_enough _ _ (fun c => commaData F u u' hsq c.hom)
    (fun c => commaUniversal F u u' hsq c.hom) (fun c => by
      rw [functor_on_fst_commaData]
      exact IsExpArr.isExpArrow (u := u) c.left)

/-- The second projection of the comma category preserves exponentiable arrows. -/
@[reducible]
noncomputable def sndPreserves :
    FunctorPreserves (commaArr F u u' hsq) (Comma.snd F (𝟭 C')) :=
  functor_preserves_1_is_enough _ _ (fun c => commaData F u u' hsq c.hom)
    (fun c => commaUniversal F u u' hsq c.hom) (fun c => by
      rw [functor_on_snd_commaData]
      exact IsExpArr.isExpArrow (u := u') c.right)

end Components

section Sections

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {C' : Type u₂} [Category.{v₂} C']
  [HasPullbacks C'] {F G : C ⥤ C'} (α : F ⟶ G)

/-- The functor `C ⥤ Comma F (𝟭 C')` sending `Z` to `(Z, G Z, α_Z)`. -/
@[simps] def toComma : C ⥤ Comma F (𝟭 C') where
  obj Z := ⟨Z, G.obj Z, α.app Z⟩
  map g := ⟨g, G.map g, α.naturality g⟩

instance preservesLimitsOfShape_toComma {J : Type*} [Category J] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (toComma α) :=
  have : PreservesLimitsOfShape J (toComma α ⋙ Comma.fst F (𝟭 C')) :=
    inferInstanceAs (PreservesLimitsOfShape J (𝟭 C))
  have : PreservesLimitsOfShape J (toComma α ⋙ Comma.snd F (𝟭 C')) :=
    inferInstanceAs (PreservesLimitsOfShape J G)
  preservesLimitsOfShape_of_comp_fst_snd (toComma α)

/-- A natural transformation `F ⟶ G` built from a section `T` of the comma category up to
natural isomorphism. -/
@[simps] def natTransOfSection (T : C ⥤ Comma F (𝟭 C'))
    (a : 𝟭 C ⟶ T ⋙ Comma.fst F (𝟭 C')) (b : T ⋙ Comma.snd F (𝟭 C') ⟶ G) : F ⟶ G where
  app Z := F.map (a.app Z) ≫ (T.obj Z).hom ≫ b.app Z
  naturality Z Z' g := by
    have hw := (T.map g).w
    have ha := a.naturality g
    have hb := b.naturality g
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
      Comma.fst_map, Comma.snd_map] at ha hb hw ⊢
    rw [← F.map_comp_assoc, ha, F.map_comp_assoc, reassoc_of% hw, hb]
    simp only [Category.assoc]

variable [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]
  {Y X : C} (u : Y ⟶ X) [IsExpArr u] [IsExpArr (G.map u)] [FunctorPreserves u G]
  (hsq : IsPullback (α.app Y) (F.map u) (G.map u) (α.app X))

/-- If `α : F ⟶ G` is a natural transformation whose component at an exponentiable arrow `u` is
a pullback square, then `toComma α` preserves the exponentiable arrow `u`. -/
@[reducible]
noncomputable def toCommaPreserves : FunctorPreserves u (toComma α) where
  functor_preserves {c} d univ := by
    refine universal_of_components F u (G.map u) hsq (functor_on (toComma α) d) ?_ ?_
    · have e : (functor_on (Comma.fst F (𝟭 C')) (functor_on (toComma α) d) : Data u c) =
          functor_on (𝟭 C) d := by
        change Data.mk _ _ _ _ = Data.mk _ _ _ _
        congr 1
      have h := (functor_preserves_id u).functor_preserves d univ
      rw [← e] at h
      exact h
    · have e : (functor_on (Comma.snd F (𝟭 C')) (functor_on (toComma α) d) : Data (G.map u) _) =
          functor_on G d := by
        change Data.mk _ _ _ _ = Data.mk _ _ _ _
        congr 1
      have h := FunctorPreserves.functor_preserves (F := G) d univ
      rw [← e] at h
      exact h

end Sections

end CommaExpArr

namespace ExpArrCat

universe v u

/-- An object `A` of `ExpArrCat` is bi-initial if every hom-category `A ⟶ B` is equivalent to the
terminal category. -/
def IsBiInitial (A : ExpArrCat.{v, u}) : Prop :=
  ∀ B : ExpArrCat.{v, u}, Nonempty ((A ⟶ B) ≌ Discrete PUnit.{1})

namespace IsBiInitial

variable {A : ExpArrCat.{v, u}} {B : ExpArrCat.{v, u}}

/-- A bi-initial object has a morphism to every object. -/
lemma nonempty_hom (hA : IsBiInitial A) (B : ExpArrCat.{v, u}) : Nonempty (A ⟶ B) :=
  ⟨(hA B).some.inverse.obj ⟨⟨⟩⟩⟩

/-- Any two parallel 2-cells out of a bi-initial object coincide. -/
lemma hom₂_ext (hA : IsBiInitial A) {F G : A ⟶ B} (α β : F ⟶ G) : α = β := by
  have := (hA B).some.faithful_functor
  exact (hA B).some.functor.map_injective (Subsingleton.elim _ _)

/-- Any two morphisms out of a bi-initial object are isomorphic. -/
lemma nonempty_iso (hA : IsBiInitial A) (F G : A ⟶ B) : Nonempty (F ≅ G) :=
  ⟨((hA B).some.unitIso.app F) ≪≫
    (hA B).some.inverse.mapIso (eqToIso (Subsingleton.elim _ _)) ≪≫
    ((hA B).some.unitIso.app G).symm⟩

end IsBiInitial

/-- Exponentiability transfers along an isomorphism of arrows. -/
@[reducible]
noncomputable def _root_.IsExpArr.ofIso {D : Type*} [Category D] {Y X Y' X' : D} (u : Y ⟶ X)
    (v : Y' ⟶ X') [IsExpArr u] (i : Arrow.mk u ≅ Arrow.mk v) : IsExpArr v where
  isExpArrowData c := lift_arrow_iso i (IsExpArr.isExpArrowData (u := u) c)
  isExpArrow _ := lift_arrow_iso_univ i _

section Comma

variable {A C : ExpArrCat.{v, max u v}} (F : A ⥤ C) [PreservesLimitsOfShape WalkingCospan F]
  (G : A ⟶ C) [IsExpArr (G.functor.map A.arr)] {y : F.obj A.dom ⟶ G.functor.obj A.dom}
  {x : F.obj A.cod ⟶ G.functor.obj A.cod}
  (hsq : IsPullback y (F.map A.arr) (G.functor.map A.arr) x)

/-- The comma category `Comma F (𝟭 C)` as an `ExpArrCat`, with the arrow `(p, G p)`. -/
noncomputable abbrev commaOf : ExpArrCat.{v, max u v} :=
  comma F A.arr (G.functor.map A.arr) hsq

/-- The first projection from the comma category. -/
noncomputable def commaFst : commaOf F G hsq ⟶ A :=
  { functor := Comma.fst F (𝟭 C)
    preservesPullbacks := inferInstanceAs
      (PreservesLimitsOfShape WalkingCospan (Comma.fst F (𝟭 C.carrier)))
    preservesTerminal := inferInstanceAs
      (PreservesLimitsOfShape (Discrete PEmpty.{1}) (Comma.fst F (𝟭 C.carrier)))
    preservesArr := CommaExpArr.fstPreserves F A.arr (G.functor.map A.arr) hsq
    iso := Iso.refl _ }

/-- The second projection from the comma category. -/
noncomputable def commaSnd : commaOf F G hsq ⟶ C :=
  { functor := Comma.snd F (𝟭 C)
    preservesPullbacks := inferInstanceAs
      (PreservesLimitsOfShape WalkingCospan (Comma.snd F (𝟭 C.carrier)))
    preservesTerminal := inferInstanceAs
      (PreservesLimitsOfShape (Discrete PEmpty.{1}) (Comma.snd F (𝟭 C.carrier)))
    preservesArr := CommaExpArr.sndPreserves F A.arr (G.functor.map A.arr) hsq
    iso := G.iso }

/-- The `ExpArrCat`-morphism `A ⟶ commaOf F G hsq` associated to a natural transformation
`α : F ⟶ G` restricting to the pullback square `hsq`. -/
noncomputable def commaSec (α : F ⟶ G.functor) (hα : α.app A.dom = y) (hαx : α.app A.cod = x) :
    A ⟶ commaOf F G hsq :=
  { functor := CommaExpArr.toComma α
    preservesPullbacks := inferInstanceAs
      (PreservesLimitsOfShape WalkingCospan (CommaExpArr.toComma α))
    preservesTerminal := inferInstanceAs
      (PreservesLimitsOfShape (Discrete PEmpty.{1}) (CommaExpArr.toComma α))
    preservesArr := CommaExpArr.toCommaPreserves α A.arr (by subst hα hαx; exact hsq)
    iso := Arrow.isoMk
      (Comma.isoMk (X := (CommaExpArr.toComma α).obj A.dom) (Y := CommaExpArr.commaDom F y)
        (Iso.refl _) (Iso.refl _) (by simp [hα, CommaExpArr.toComma]))
      (Comma.isoMk (X := (CommaExpArr.toComma α).obj A.cod) (Y := CommaExpArr.commaCod F x)
        (Iso.refl _) (Iso.refl _) (by simp [hαx, CommaExpArr.toComma]))
      (CommaMorphism.ext
        (by change 𝟙 A.dom ≫ A.arr = A.arr ≫ 𝟙 A.cod; simp)
        (by change 𝟙 (G.functor.obj A.dom) ≫ G.functor.map A.arr =
          G.functor.map A.arr ≫ 𝟙 (G.functor.obj A.cod); simp)) }

variable {F G}

@[simp] lemma commaSec_functor (α : F ⟶ G.functor) (hα : α.app A.dom = y)
    (hαx : α.app A.cod = x) : (commaSec F G hsq α hα hαx).functor = CommaExpArr.toComma α := rfl

@[simp] lemma commaSec_iso_hom_left_left (α : F ⟶ G.functor) (hα : α.app A.dom = y)
    (hαx : α.app A.cod = x) : (commaSec F G hsq α hα hαx).iso.hom.left.left = 𝟙 A.dom := rfl

@[simp] lemma commaSec_iso_hom_left_right (α : F ⟶ G.functor) (hα : α.app A.dom = y)
    (hαx : α.app A.cod = x) :
    (commaSec F G hsq α hα hαx).iso.hom.left.right = 𝟙 (G.functor.obj A.dom) := rfl

@[simp] lemma commaSec_iso_hom_right_left (α : F ⟶ G.functor) (hα : α.app A.dom = y)
    (hαx : α.app A.cod = x) : (commaSec F G hsq α hα hαx).iso.hom.right.left = 𝟙 A.cod := rfl

@[simp] lemma commaSec_iso_hom_right_right (α : F ⟶ G.functor) (hα : α.app A.dom = y)
    (hαx : α.app A.cod = x) :
    (commaSec F G hsq α hα hαx).iso.hom.right.right = 𝟙 (G.functor.obj A.cod) := rfl

include hsq in
/-- A natural transformation `F ⟶ G` restricting to a given pullback square is unique. -/
lemma natTrans_unique (hA : IsBiInitial A) {α α' : F ⟶ G.functor}
    (hα : α.app A.dom = y) (hαx : α.app A.cod = x)
    (hα' : α'.app A.dom = y) (hαx' : α'.app A.cod = x) : α = α' := by
  let K := commaSec F G hsq α hα hαx
  let K' := commaSec F G hsq α' hα' hαx'
  let η : K ⟶ K' := (hA.nonempty_iso K K').some.hom
  have hL : ∀ Z, (η.nat.app Z).left = 𝟙 Z := by
    let c₁ : K ≫ commaFst F G hsq ⟶ K' ≫ commaFst F G hsq :=
      ⟨𝟙 (𝟭 A.carrier),
        by change 𝟙 A.dom ≫ (𝟙 A.dom ≫ 𝟙 A.dom) = 𝟙 A.dom ≫ 𝟙 A.dom; simp,
        by change 𝟙 A.cod ≫ (𝟙 A.cod ≫ 𝟙 A.cod) = 𝟙 A.cod ≫ 𝟙 A.cod; simp⟩
    have := hA.hom₂_ext (Hom₂.whiskerRight η (commaFst F G hsq)) c₁
    intro Z
    exact congrArg (fun t => t.nat.app Z) this
  have hR : ∀ Z, (η.nat.app Z).right = 𝟙 (G.functor.obj Z) := by
    let c₂ : K ≫ commaSnd F G hsq ⟶ K' ≫ commaSnd F G hsq :=
      ⟨𝟙 G.functor,
        by change 𝟙 _ ≫ (𝟙 _ ≫ G.iso.hom.left) = 𝟙 _ ≫ G.iso.hom.left; simp,
        by change 𝟙 _ ≫ (𝟙 _ ≫ G.iso.hom.right) = 𝟙 _ ≫ G.iso.hom.right; simp⟩
    have := hA.hom₂_ext (Hom₂.whiskerRight η (commaSnd F G hsq)) c₂
    intro Z
    exact congrArg (fun t => t.nat.app Z) this
  refine NatTrans.ext (funext fun Z => ?_)
  have w : F.map (η.nat.app Z).left ≫ α'.app Z = α.app Z ≫ (η.nat.app Z).right :=
    (η.nat.app Z).w
  rw [hL, hR] at w
  have w' : F.map (𝟙 Z) ≫ α'.app Z = α.app Z ≫ 𝟙 (G.functor.obj Z) := w
  rw [F.map_id, Category.id_comp, Category.comp_id] at w'
  exact w'.symm

include hsq in
/-- Existence of a natural transformation restricting to a given pullback square. -/
lemma natTrans_exists (hA : IsBiInitial A) :
    ∃ α : F ⟶ G.functor, α.app A.dom = y ∧ α.app A.cod = x := by
  obtain ⟨K⟩ := hA.nonempty_hom (commaOf F G hsq)
  obtain ⟨e₁⟩ := hA.nonempty_iso (K ≫ commaFst F G hsq) (𝟙 A)
  obtain ⟨e₂⟩ := hA.nonempty_iso (K ≫ commaSnd F G hsq) G
  let T : A.carrier ⥤ Comma F (𝟭 C.carrier) := K.functor
  let α : F ⟶ G.functor := CommaExpArr.natTransOfSection T e₁.inv.nat e₂.hom.nat
  let k : T.obj A.dom ⟶ CommaExpArr.commaDom F y := K.iso.hom.left
  let k' : T.obj A.cod ⟶ CommaExpArr.commaCod F x := K.iso.hom.right
  let a : A.dom ⟶ (T.obj A.dom).left := e₁.inv.nat.app A.dom
  let a' : A.cod ⟶ (T.obj A.cod).left := e₁.inv.nat.app A.cod
  let b : (T.obj A.dom).right ⟶ G.functor.obj A.dom := e₂.hom.nat.app A.dom
  let b' : (T.obj A.cod).right ⟶ G.functor.obj A.cod := e₂.hom.nat.app A.cod
  have c1 : a ≫ k.left = 𝟙 A.dom := by
    have h : a ≫ (k.left ≫ 𝟙 A.dom) = 𝟙 A.dom := e₁.inv.left_comm
    exact (congrArg (a ≫ ·) (Category.comp_id k.left)).symm.trans h
  have c1' : a' ≫ k'.left = 𝟙 A.cod := by
    have h : a' ≫ (k'.left ≫ 𝟙 A.cod) = 𝟙 A.cod := e₁.inv.right_comm
    exact (congrArg (a' ≫ ·) (Category.comp_id k'.left)).symm.trans h
  have c2 : b = k.right := by
    have h : b ≫ G.iso.hom.left = k.right ≫ G.iso.hom.left := e₂.hom.left_comm
    exact (cancel_mono _).1 h
  have c2' : b' = k'.right := by
    have h : b' ≫ G.iso.hom.right = k'.right ≫ G.iso.hom.right := e₂.hom.right_comm
    exact (cancel_mono _).1 h
  refine ⟨α, ?_, ?_⟩
  · have hw : F.map k.left ≫ y = (T.obj A.dom).hom ≫ k.right := k.w
    change F.map a ≫ (T.obj A.dom).hom ≫ b = y
    rw [c2, ← hw, ← F.map_comp_assoc, c1, F.map_id, Category.id_comp]
  · have hw : F.map k'.left ≫ x = (T.obj A.cod).hom ≫ k'.right := k'.w
    change F.map a' ≫ (T.obj A.cod).hom ≫ b' = x
    rw [c2', ← hw, ← F.map_comp_assoc, c1', F.map_id, Category.id_comp]

end Comma

/-- **Main theorem.** Let `A` (`FinGAT`) be a bi-initial `ExpArrCat`, with chosen exponentiable
arrow `p = A.arr : Y ⟶ X`. Let `C` be an `ExpArrCat`, `F : A ⥤ C` a functor preserving pullbacks,
`G : A ⟶ C` a morphism of `ExpArrCat`, and `f : F p ⟶ G p` a morphism of arrows whose underlying
square is a pullback. Then there is a unique natural transformation `α : F ⟶ G` whose components
at `Y` and `X` are the components of `f`. -/
theorem IsBiInitial.existsUnique_natTrans_gen {A C : ExpArrCat.{v, max u v}} (hA : IsBiInitial A)
    (F : A.carrier ⥤ C.carrier) [PreservesLimitsOfShape WalkingCospan F] (G : A ⟶ C)
    (f : Arrow.mk (F.map A.arr) ⟶ Arrow.mk (G.functor.map A.arr))
    (hf : IsPullback f.left (F.map A.arr) (G.functor.map A.arr) f.right) :
    ∃! α : F ⟶ G.functor, α.app A.dom = f.left ∧ α.app A.cod = f.right := by
  let _ : IsExpArr (G.functor.map A.arr) := IsExpArr.ofIso C.arr (G.functor.map A.arr) G.iso.symm
  obtain ⟨α, h₁, h₂⟩ := natTrans_exists (hsq := hf) hA
  exact ⟨α, ⟨h₁, h₂⟩, fun α' h' => natTrans_unique hf hA h'.1 h'.2 h₁ h₂⟩

/-- `IsBiInitial.existsUnique_natTrans_gen` for objects of `ExpArrCat.{u, u}`. -/
theorem IsBiInitial.existsUnique_natTrans {A C : ExpArrCat.{u, u}} (hA : IsBiInitial A)
    (F : A.carrier ⥤ C.carrier) [PreservesLimitsOfShape WalkingCospan F] (G : A ⟶ C)
    (f : Arrow.mk (F.map A.arr) ⟶ Arrow.mk (G.functor.map A.arr))
    (hf : IsPullback f.left (F.map A.arr) (G.functor.map A.arr) f.right) :
    ∃! α : F ⟶ G.functor, α.app A.dom = f.left ∧ α.app A.cod = f.right :=
  IsBiInitial.existsUnique_natTrans_gen.{u, u} hA F G f hf

/-- Variant of `IsBiInitial.existsUnique_natTrans_gen` where the square is given as a morphism of
arrows to the chosen arrow of `C`, through the isomorphism `G.iso`. -/
theorem IsBiInitial.existsUnique_natTrans_iso {A C : ExpArrCat.{v, max u v}} (hA : IsBiInitial A)
    (F : A.carrier ⥤ C.carrier) [PreservesLimitsOfShape WalkingCospan F] (G : A ⟶ C)
    (f : Arrow.mk (F.map A.arr) ⟶ Arrow.mk C.arr)
    (hf : IsPullback f.left (F.map A.arr) C.arr f.right) :
    ∃! α : F ⟶ G.functor, α.app A.dom ≫ G.iso.hom.left = f.left ∧
      α.app A.cod ≫ G.iso.hom.right = f.right := by
  have hf' : IsPullback (f ≫ G.iso.inv).left (F.map A.arr) (G.functor.map A.arr)
      (f ≫ G.iso.inv).right := by
    exact hf.paste_horiz (IsPullback.of_horiz_isIso ⟨G.iso.inv.w⟩)
  obtain ⟨α, ⟨h₁, h₂⟩, hu⟩ := hA.existsUnique_natTrans_gen F G (f ≫ G.iso.inv) hf'
  refine ⟨α, ⟨?_, ?_⟩, fun β hβ => hu β ⟨?_, ?_⟩⟩
  · rw [h₁, Arrow.comp_left, Category.assoc, ← Arrow.comp_left, Iso.inv_hom_id]; simp
  · rw [h₂, Arrow.comp_right, Category.assoc, ← Arrow.comp_right, Iso.inv_hom_id]; simp
  · rw [Arrow.comp_left, ← hβ.1, Category.assoc, ← Arrow.comp_left, Iso.hom_inv_id]; simp
  · rw [Arrow.comp_right, ← hβ.2, Category.assoc, ← Arrow.comp_right, Iso.hom_inv_id]; simp

end ExpArrCat
