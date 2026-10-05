module

public import CartexpAristotle.CatPullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A concrete criterion for pullback squares in `Cat`

A commutative square of categories
```
W ──fst──▶ X₁
│snd        │f
▼           ▼
X₂ ───g───▶ S
```
is a pullback in `Cat` if and only if
* for all objects `x₁`, `x₂` with `f x₁ = g x₂` there is a unique `w` with `fst w = x₁` and
  `snd w = x₂`, and
* for all objects `w`, `w'` and morphisms `h₁ : fst w ⟶ fst w'`, `h₂ : snd w ⟶ snd w'` with
  `f h₁ ≍ g h₂` there is a unique `k : w ⟶ w'` with `fst k = h₁` and `snd k = h₂`.

## References

* Auxiliary. [Paper, App. B] (initial models) and [Paper, App. C] (full faithfulness) need
  to check that certain naturality squares in `CAT` are pullbacks, in order to apply
  [Paper, Thm. `thm:universal-property-natural-transformation`]; this is the concrete criterion
  used for that purpose. The paper uses it implicitly.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CatPullback

variable {W X₁ X₂ S : Cat.{v, u}} {fst : W ⟶ X₁} {snd : W ⟶ X₂} {f : X₁ ⟶ S} {g : X₂ ⟶ S}

/-- The concrete pullback condition on a square of categories. -/
structure Crit (fst : W ⟶ X₁) (snd : W ⟶ X₂) (f : X₁ ⟶ S) (g : X₂ ⟶ S) : Prop where
  obj : ∀ (x₁ : X₁) (x₂ : X₂), f.toFunctor.obj x₁ = g.toFunctor.obj x₂ →
    ∃! w : W, fst.toFunctor.obj w = x₁ ∧ snd.toFunctor.obj w = x₂
  hom : ∀ (w w' : W) (h₁ : fst.toFunctor.obj w ⟶ fst.toFunctor.obj w')
    (h₂ : snd.toFunctor.obj w ⟶ snd.toFunctor.obj w'),
    f.toFunctor.map h₁ ≍ g.toFunctor.map h₂ →
    ∃! k : w ⟶ w', fst.toFunctor.map k = h₁ ∧ snd.toFunctor.map k = h₂

lemma conj_heq {D : Type*} [Category D] {a b c d : D} (e₁ : a = b) (e₂ : c = d) (x : b ⟶ c) :
    (eqToHom e₁ ≫ x ≫ eqToHom e₂) ≍ x := by
  subst e₁ e₂; simp

lemma heq_conj {D : Type*} [Category D] {a b c d : D} {x : a ⟶ d} {y : b ⟶ c} (e₁ : a = b)
    (e₂ : c = d) (h : x ≍ y) : x = eqToHom e₁ ≫ y ≫ eqToHom e₂ := by
  subst e₁ e₂; simpa using eq_of_heq h

section Forward

variable (hc : Crit fst snd f g)
include hc

lemma liftObj_spec (s : PullbackCone f g) (t : s.pt) :
    ∃! w : W, fst.toFunctor.obj w = s.fst.toFunctor.obj t ∧
      snd.toFunctor.obj w = s.snd.toFunctor.obj t :=
  hc.obj _ _ (Functor.congr_obj (congrArg Cat.Hom.toFunctor s.condition) t)

/-- The object part of the lift. -/
noncomputable def liftObj (s : PullbackCone f g) (t : s.pt) : W :=
  (liftObj_spec hc s t).exists.choose

lemma liftObj_fst (s : PullbackCone f g) (t : s.pt) :
    fst.toFunctor.obj (liftObj hc s t) = s.fst.toFunctor.obj t :=
  (liftObj_spec hc s t).exists.choose_spec.1

lemma liftObj_snd (s : PullbackCone f g) (t : s.pt) :
    snd.toFunctor.obj (liftObj hc s t) = s.snd.toFunctor.obj t :=
  (liftObj_spec hc s t).exists.choose_spec.2

lemma liftMap_spec (s : PullbackCone f g) {t t' : s.pt} (φ : t ⟶ t') :
    ∃! k : liftObj hc s t ⟶ liftObj hc s t',
      fst.toFunctor.map k = eqToHom (liftObj_fst hc s t) ≫ s.fst.toFunctor.map φ ≫
        eqToHom (liftObj_fst hc s t').symm ∧
      snd.toFunctor.map k = eqToHom (liftObj_snd hc s t) ≫ s.snd.toFunctor.map φ ≫
        eqToHom (liftObj_snd hc s t').symm := by
  apply hc.hom
  simp only [Functor.map_comp, eqToHom_map]
  refine ((conj_heq _ _ _).trans ?_).trans (conj_heq _ _ _).symm
  exact Functor.hcongr_hom (congrArg Cat.Hom.toFunctor s.condition) φ

/-- The morphism part of the lift. -/
noncomputable def liftMap (s : PullbackCone f g) {t t' : s.pt} (φ : t ⟶ t') :
    liftObj hc s t ⟶ liftObj hc s t' :=
  (liftMap_spec hc s φ).exists.choose

lemma liftMap_fst (s : PullbackCone f g) {t t' : s.pt} (φ : t ⟶ t') :
    fst.toFunctor.map (liftMap hc s φ) = eqToHom (liftObj_fst hc s t) ≫
      s.fst.toFunctor.map φ ≫ eqToHom (liftObj_fst hc s t').symm :=
  (liftMap_spec hc s φ).exists.choose_spec.1

lemma liftMap_snd (s : PullbackCone f g) {t t' : s.pt} (φ : t ⟶ t') :
    snd.toFunctor.map (liftMap hc s φ) = eqToHom (liftObj_snd hc s t) ≫
      s.snd.toFunctor.map φ ≫ eqToHom (liftObj_snd hc s t').symm :=
  (liftMap_spec hc s φ).exists.choose_spec.2

/-- The lift into `W`. -/
noncomputable def liftFunctor (s : PullbackCone f g) : s.pt ⥤ W where
  obj := liftObj hc s
  map := liftMap hc s
  map_id t := (liftMap_spec hc s (𝟙 t)).unique ⟨liftMap_fst hc s _, liftMap_snd hc s _⟩
    ⟨by simp, by simp⟩
  map_comp φ ψ := (liftMap_spec hc s (φ ≫ ψ)).unique
    ⟨liftMap_fst hc s _, liftMap_snd hc s _⟩
    ⟨by simp [liftMap_fst], by simp [liftMap_snd]⟩

lemma liftFunctor_fst (s : PullbackCone f g) :
    liftFunctor hc s ⋙ fst.toFunctor = s.fst.toFunctor :=
  Functor.hext (liftObj_fst hc s) fun t t' φ => by
    change fst.toFunctor.map (liftMap hc s φ) ≍ _
    rw [liftMap_fst]; exact conj_heq _ _ _

lemma liftFunctor_snd (s : PullbackCone f g) :
    liftFunctor hc s ⋙ snd.toFunctor = s.snd.toFunctor :=
  Functor.hext (liftObj_snd hc s) fun t t' φ => by
    change snd.toFunctor.map (liftMap hc s φ) ≍ _
    rw [liftMap_snd]; exact conj_heq _ _ _

lemma liftFunctor_uniq (s : PullbackCone f g) (m : s.pt ⥤ W) (h₁ : m ⋙ fst.toFunctor = s.fst.toFunctor)
    (h₂ : m ⋙ snd.toFunctor = s.snd.toFunctor) : m = liftFunctor hc s := by
  have hobj : ∀ t, m.obj t = liftObj hc s t := fun t =>
    (liftObj_spec hc s t).unique ⟨Functor.congr_obj h₁ t, Functor.congr_obj h₂ t⟩
      ⟨liftObj_fst hc s t, liftObj_snd hc s t⟩
  refine Functor.hext hobj fun t t' φ => ?_
  have key : eqToHom (hobj t).symm ≫ m.map φ ≫ eqToHom (hobj t') = liftMap hc s φ := by
    refine (liftMap_spec hc s φ).unique ?_ ⟨liftMap_fst hc s _, liftMap_snd hc s _⟩
    constructor
    · have := Functor.congr_hom h₁ φ
      simp only [Functor.comp_map] at this
      simp only [Functor.map_comp, eqToHom_map, this, Category.assoc, eqToHom_trans,
        eqToHom_trans_assoc]
    · have := Functor.congr_hom h₂ φ
      simp only [Functor.comp_map] at this
      simp only [Functor.map_comp, eqToHom_map, this, Category.assoc, eqToHom_trans,
        eqToHom_trans_assoc]
  change m.map φ ≍ liftMap hc s φ
  rw [← key]; exact (conj_heq _ _ _).symm

/-- **Criterion.** A commutative square satisfying `Crit` is a pullback in `Cat`. -/
theorem isPullback_of_crit (comm : fst ≫ f = snd ≫ g) : IsPullback fst snd f g :=
  IsPullback.of_isLimit' ⟨comm⟩ (PullbackCone.IsLimit.mk comm
    (fun s => (liftFunctor hc s).toCatHom)
    (fun s => Cat.Hom.ext (liftFunctor_fst hc s))
    (fun s => Cat.Hom.ext (liftFunctor_snd hc s))
    (fun s m hm₁ hm₂ => Cat.Hom.ext (liftFunctor_uniq hc s m.toFunctor
      (congrArg Cat.Hom.toFunctor hm₁) (congrArg Cat.Hom.toFunctor hm₂))))

end Forward

section Backward

/-- The strict pullback satisfies the criterion. -/
lemma crit_strict (f : X₁ ⟶ S) (g : X₂ ⟶ S) :
    Crit (CatPullback.fst f g) (CatPullback.snd f g) f g where
  obj x₁ x₂ h := ⟨⟨x₁, x₂, h⟩, ⟨rfl, rfl⟩, fun w hw => Obj.ext hw.1 hw.2⟩
  hom w w' h₁ h₂ h := ⟨⟨h₁, h₂, h⟩, ⟨rfl, rfl⟩, fun k hk => Hom.ext hk.1 hk.2⟩

/-- The criterion is invariant under replacing the corner by an isomorphic one. -/
lemma crit_of_iso {W' : Cat.{v, u}} (e : W ≅ W') {fst' : W' ⟶ X₁} {snd' : W' ⟶ X₂}
    (h₁ : e.hom ≫ fst' = fst) (h₂ : e.hom ≫ snd' = snd) (hc : Crit fst' snd' f g) :
    Crit fst snd f g := by
  subst h₁ h₂
  have hi : e.hom.toFunctor ⋙ e.inv.toFunctor = 𝟭 _ := congrArg Cat.Hom.toFunctor e.hom_inv_id
  have hi' : e.inv.toFunctor ⋙ e.hom.toFunctor = 𝟭 _ := congrArg Cat.Hom.toFunctor e.inv_hom_id
  have ff := (Cat.equivOfIso e).fullyFaithfulFunctor
  constructor
  · intro x₁ x₂ h
    obtain ⟨w', hw', hu⟩ := hc.obj x₁ x₂ h
    have hw'' : e.hom.toFunctor.obj (e.inv.toFunctor.obj w') = w' := Functor.congr_obj hi' w'
    refine ⟨e.inv.toFunctor.obj w', ⟨?_, ?_⟩, fun w hw => ?_⟩
    · change fst'.toFunctor.obj (e.hom.toFunctor.obj _) = _
      rw [hw'']; exact hw'.1
    · change snd'.toFunctor.obj (e.hom.toFunctor.obj _) = _
      rw [hw'']; exact hw'.2
    · have : e.hom.toFunctor.obj w = w' := hu _ hw
      rw [← this]; exact (Functor.congr_obj hi w).symm
  · intro w w' k₁ k₂ h
    obtain ⟨k', hk', hu⟩ := hc.hom (e.hom.toFunctor.obj w) (e.hom.toFunctor.obj w') k₁ k₂ h
    refine ⟨ff.preimage k', ?_, fun k hk => ff.map_injective ?_⟩
    · change fst'.toFunctor.map (e.hom.toFunctor.map _) = _ ∧
        snd'.toFunctor.map (e.hom.toFunctor.map _) = _
      have : e.hom.toFunctor.map (ff.preimage k') = k' := ff.map_preimage k'
      rw [this]; exact hk'
    · have : (Cat.equivOfIso e).functor.map (ff.preimage k') = k' := ff.map_preimage k'
      rw [this]; exact hu _ hk

/-- **Criterion (converse).** A pullback square in `Cat` satisfies `Crit`. -/
theorem crit_of_isPullback (h : IsPullback fst snd f g) : Crit fst snd f g :=
  crit_of_iso (h.isoIsPullback _ _ (IsPullback.of_isLimit (isLimit f g)))
    (IsPullback.isoIsPullback_hom_fst _ _ _ _) (IsPullback.isoIsPullback_hom_snd _ _ _ _)
    (crit_strict f g)

end Backward

end CatPullback
