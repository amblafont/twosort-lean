import CartexpAristotle.Lexp
import CartexpAristotle.SliceExponentiable

/-!
# Right adjoints preserving exponentiable arrows, and transport along equivalences

* `functorPreserves_of_adjunction`: a right adjoint `R` (with left adjoint `L`) preserves the
  exponentiability of `u : Y ⟶ X` as soon as `L` satisfies the following *Frobenius condition*:
  for every pullback `K` of `R u` along `f : d ⟶ R X`, the image under `L` of `K` (with its
  projections transposed) is a pullback of `u` along the transpose of `f`.
* An equivalence satisfies this condition, so exponentiable arrows can be transported along
  equivalences of categories (`IsExpArr.ofEquivalence`), and so can the whole structure of an
  object of `Lexp` (`Lexp.ofEquivalence`).

## References

* [Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`]: a right adjoint whose left
  adjoint preserves pullbacks and satisfies the counit-pullback (Frobenius) condition preserves
  pushforwards along the exponentiable morphism. `functorPreserves_of_adjunction` is the Lean
  version of this abstract argument.
* `Lexp.ofEquivalence` is auxiliary (transport of a `Lexp`-structure along an equivalence); it is
  used to identify `CAT/Fam` with the `Lexp`-category `Φ CatLexp` of [Paper, Prop. `prop:p2-exponentiable`].
-/

open CategoryTheory Limits

section EpsIso

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {u : Y ⟶ X}

/-- Post-composing the counit of partial exponential data with an isomorphism. -/
def Data.compIso {c c' : C} (d : Data u c) (e : c ≅ c') : Data u c' where
  P := d.P
  pi := d.pi
  Pbk := d.Pbk
  epsilon := d.epsilon ≫ e.hom

/-- Universality is preserved by post-composing the counit with an isomorphism. -/
@[reducible]
def Data.compIsoUniversal {c c' : C} (d : Data u c) [Universal d] (e : c ≅ c') :
    Universal (d.compIso e) where
  mor g := Universal.mor (data := d) (g ≫ e.inv)
  isSlice g := Universal.isSlice (data := d) (g ≫ e.inv)
  comm {_ _ Kuf} g := by
    have h := Universal.comm (data := d) (Kuf := Kuf) (g ≫ e.inv)
    change g = FBF_on_mor d Kuf _ ≫ d.epsilon ≫ e.hom
    rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  uniq Kufp eq_fp eq_gp H := by
    refine Universal.uniq (data := d) Kufp eq_fp eq_gp ?_
    have H' : FBF_on_mor d Kufp eq_fp ≫ d.epsilon ≫ e.hom =
        FBF_on_mor d Kufp eq_gp ≫ d.epsilon ≫ e.hom := H
    simpa using H'

end EpsIso

section Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) [PreservesLimitsOfShape WalkingCospan R]
  {X Y : C} (u : Y ⟶ X)

/-- The Frobenius condition for `L ⊣ R` and `u`: the image under `L` of a pullback of `R u` along
`f`, with the transposed projections, is a pullback of `u` along the transpose of `f`. -/
def Frobenius : Prop :=
  ∀ (d : D) (f : d ⟶ R.obj X) (K : ChosenPullback (R.map u) f),
    IsPullback ((adj.homEquiv _ _).symm K.p₁) (L.map K.p₂) u ((adj.homEquiv _ _).symm f)

variable {adj u}

omit [PreservesLimitsOfShape WalkingCospan R] in
/-- The Frobenius condition only has to be checked on one pullback for each `f`. -/
lemma Frobenius.of_chosen
    (K₀ : ∀ {d : D} (f : d ⟶ R.obj X), ChosenPullback (R.map u) f)
    (h : ∀ {d : D} (f : d ⟶ R.obj X),
      IsPullback ((adj.homEquiv _ _).symm (K₀ f).p₁) (L.map (K₀ f).p₂) u
        ((adj.homEquiv _ _).symm f)) :
    Frobenius adj u := by
  intro d f K
  let e := K.isPullback.isoIsPullback _ _ (K₀ f).isPullback
  have e₁ : e.hom ≫ (K₀ f).p₁ = K.p₁ := K.isPullback.isoIsPullback_hom_fst _ _ _
  have e₂ : e.hom ≫ (K₀ f).p₂ = K.p₂ := K.isPullback.isoIsPullback_hom_snd _ _ _
  refine (h f).of_iso (L.mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    rw [← adj.homEquiv_naturality_left_symm, ← e₁, ← Category.assoc]
    simp
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    rw [← e₂, Functor.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    simp

variable (hF : Frobenius adj u)
include hF

/-- The pullback of `u` along the transpose of `f` given by the Frobenius condition. -/
@[reducible]
noncomputable def frobPullback {d : D} {f : d ⟶ R.obj X} (K : ChosenPullback (R.map u) f) :
    ChosenPullback u ((adj.homEquiv _ _).symm f) :=
  SliceExp.chosenOfIsPullback (hF _ _ K)

omit [PreservesLimitsOfShape WalkingCospan R] hF in
lemma transpose_isSlice {P : C} {pi : P ⟶ X} {d' : D} {h : d' ⟶ R.obj X} {φ : d' ⟶ R.obj P}
    (eq : h = φ ≫ R.map pi) :
    (adj.homEquiv _ _).symm h = (adj.homEquiv _ _).symm φ ≫ pi := by
  rw [eq, adj.homEquiv_naturality_right_symm]

lemma fbf_transpose {c : C} (d : Data u c) {d' : D} {h : d' ⟶ R.obj X} {φ : d' ⟶ R.obj d.P}
    (K : ChosenPullback (R.map u) h) (eq : h = φ ≫ (functor_on R d).pi)
    (eq' : (adj.homEquiv _ _).symm h = (adj.homEquiv _ _).symm φ ≫ d.pi) :
    FBF_on_mor d (frobPullback hF K) eq' =
      (adj.homEquiv _ _).symm (FBF_on_mor (functor_on R d) K eq) := by
  apply d.Pbk.hom_ext
  · simp only [FBF_on_mor, pullbackMor1, IsPullback.lift_fst]
    rw [← adj.homEquiv_naturality_right_symm]
    congr 1
    exact ((functor_on R d).Pbk.isPullback.lift_fst _ _ _).symm
  · simp only [FBF_on_mor, pullbackMor1, IsPullback.lift_snd]
    rw [← adj.homEquiv_naturality_right_symm]
    have := (functor_on R d).Pbk.isPullback.lift_snd K.p₁ (K.p₂ ≫ φ)
      (by rw [Category.assoc, ← eq, K.condition])
    change _ = (adj.homEquiv _ _).symm
      ((functor_on R d).Pbk.isPullback.lift K.p₁ (K.p₂ ≫ φ) _ ≫ (functor_on R d).Pbk.p₂)
    rw [this, adj.homEquiv_naturality_left_symm]

/-- The universality of the image under `R` of universal data, under the Frobenius condition. -/
@[reducible]
noncomputable def universal_functor_on {c : C} (d : Data u c) [Universal d] :
    Universal (functor_on R d) where
  mor {_ _ Kuf} g :=
    adj.homEquiv _ _ (Universal.mor (data := d) (Kuf := frobPullback hF Kuf)
      ((adj.homEquiv _ _).symm g))
  isSlice {_ f Kuf} g := by
    change f = _ ≫ R.map d.pi
    rw [← adj.homEquiv_naturality_right, ← Universal.isSlice, Equiv.apply_symm_apply]
  comm {_ f Kuf} g := by
    apply (adj.homEquiv _ _).symm.injective
    change _ = (adj.homEquiv _ _).symm (_ ≫ R.map d.epsilon)
    rw [adj.homEquiv_naturality_right_symm, ← fbf_transpose hF d Kuf _
      (transpose_isSlice (by
        rw [← adj.homEquiv_naturality_right, ← Universal.isSlice, Equiv.apply_symm_apply]))]
    have h := Universal.comm (data := d) (Kuf := frobPullback hF Kuf)
      ((adj.homEquiv _ _).symm g)
    refine h.trans ?_
    congr 2
    simp
  uniq {_ f g h} Kufp eq_fp eq_gp H := by
    apply (adj.homEquiv _ _).symm.injective
    have e₁ := transpose_isSlice (adj := adj) eq_fp
    have e₂ := transpose_isSlice (adj := adj) eq_gp
    refine Universal.uniq (data := d) (frobPullback hF Kufp) e₁ e₂ ?_
    rw [fbf_transpose hF d Kufp eq_fp e₁, fbf_transpose hF d Kufp eq_gp e₂,
      ← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_right_symm]
    exact congrArg _ H

/-- A right adjoint satisfying the Frobenius condition for `u` preserves exponentiability of
`u`.

[Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`] (abstract adjunction argument). -/
@[reducible]
noncomputable def functorPreserves_of_adjunction : FunctorPreserves u R where
  functor_preserves d _ := universal_functor_on hF d

end Adjunction

section Equivalence

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (E : C ≌ D)

/-- An equivalence satisfies the Frobenius condition (for its inverse as right adjoint). -/
lemma frobenius_equivalence {X Y : D} (u : Y ⟶ X) :
    Frobenius E.toAdjunction u := by
  intro d f K
  have hK : IsPullback (E.functor.map K.p₁) (E.functor.map K.p₂)
      (E.functor.map (E.inverse.map u)) (E.functor.map f) :=
    E.functor.map_isPullback K.isPullback
  refine hK.of_iso (Iso.refl _) (E.counitIso.app _) (Iso.refl _) (E.counitIso.app _) ?_ ?_ ?_ ?_
  · simp [Adjunction.homEquiv_counit]
  · simp
  · simp
  · simp [Adjunction.homEquiv_counit]

variable [PreservesLimitsOfShape WalkingCospan E.inverse]

/-- Transport of an exponentiable arrow along an equivalence. -/
@[reducible]
noncomputable def IsExpArr.ofEquivalence {X Y : D} (u : Y ⟶ X) [IsExpArr u] :
    IsExpArr (E.inverse.map u) :=
  letI : FunctorPreserves u E.inverse :=
    functorPreserves_of_adjunction (frobenius_equivalence E u)
  { isExpArrowData c :=
      (functor_on E.inverse (IsExpArr.isExpArrowData (E.functor.obj c))).compIso
        (E.unitIso.app c).symm
    isExpArrow c :=
      letI := FunctorPreserves.functor_preserves (u := u) (F := E.inverse)
        (IsExpArr.isExpArrowData (E.functor.obj c)) (IsExpArr.isExpArrow (E.functor.obj c))
      Data.compIsoUniversal (functor_on E.inverse (IsExpArr.isExpArrowData (E.functor.obj c)))
        (E.unitIso.app c).symm }

end Equivalence

namespace Lexp

universe v u

/-- Transport of the structure of an object of `Lexp` along an equivalence. -/
noncomputable def ofEquivalence (A : Lexp.{v, u}) (C : Type u) [Category.{v} C]
    (E : C ≌ A) : Lexp.{v, u} :=
  haveI : HasPullbacks C := Adjunction.hasLimitsOfShape_of_equivalence E.functor
  haveI : HasTerminal C := Adjunction.hasLimitsOfShape_of_equivalence E.functor
  { carrier := C
    arr := E.inverse.map A.arr
    isExpArr := IsExpArr.ofEquivalence E A.arr }

end Lexp
