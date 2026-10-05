/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.ChosenPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
/-!
# Partial exponentiability of an arrow

Translation of Rocq code defining _partial_ exponentiability of an arrow.

The declarations mirror the Rocq originals:
* `Data` packages the would-be right adjoint together with a counit,
* `FBF_on_mor` morally corresponds to the behaviour of the fiber product functor
  on morphisms,
* `Universal` equips the data with the universal property needed to promote it
  to a structure of an adjoint.

## References

* [Paper, §2.1, Def. `def:exp-mor`] and [Paper, §2.1, Prop. `prop:exp-mor-P-def`]: a morphism
  `f : Y → X` is exponentiable iff `dom ∘ f^* : C/X → C` has a right adjoint `P_f`. `Data u c`
  with `Universal` is a value `P_f(c)` of this right adjoint with its counit, and `IsExpArr u` says
  that it exists for every `c`.
* [Paper, §2.1, Def. `def:preserves-pushforwards`] and [Paper, §2.1, Lemma
  `lem:preservation_pushforward`]: `FunctorPreserves u F` says that `F` commutes with `P_u` and
  `P_{F u}`.
-/

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

instance {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} : CoeTC (ChosenPullback f₁ f₂) C :=
  ⟨fun h ↦ h.pullback⟩

variable {X Y : C}

/-- We define **partial** exponentiability of an arrow `u : Y ⟶ X` as the following data:
* an object `P` which intuitively corresponds to the action on objects of the
  right adjoint,
* a projection `pi` over the codomain of the arrow, which makes it an object of
  the slice category,
* a pullback `Pbk` which morally is the data of the fiber product over `P`, and
* a counit `epsilon` which sends `Pbk` back to the starting point `c`.

[Paper, §2.1, Prop. `prop:exp-mor-P-def`]: candidate value `P_u(c)` of the right adjoint of `dom ∘ u^*`, with its counit. -/
structure Data (u : Y ⟶ X) (c : C) where
  P : C
  pi : P ⟶ X
  Pbk : ChosenPullback u pi
  epsilon : (Pbk : C) ⟶ c

variable {u : Y ⟶ X} {c : C}

/-- Morphism between pullbacks along a factorization `h = f ≫ pi`. -/
noncomputable def pullbackMor1 {P d : C} {f : d ⟶ P} {h : d ⟶ X} {pi : P ⟶ X}
    (Kufp : ChosenPullback u h) (Pbk : ChosenPullback u pi) (eq_fp : h = f ≫ pi) :
    (Kufp : C) ⟶ (Pbk : C) :=
  Pbk.isPullback.lift Kufp.p₁ (Kufp.p₂ ≫ f) (by
    rw [Category.assoc, ← eq_fp, Kufp.condition])

/-- This morally corresponds to the behaviour of the `FiberProductFunctor` on morphisms. -/
noncomputable def FBF_on_mor (data : Data u c) {d : C} {f : d ⟶ data.P} {h : d ⟶ X}
    (Kufp : ChosenPullback u h) (eq_fp : h = f ≫ data.pi) :
    (Kufp : C) ⟶ (data.Pbk : C) :=
  pullbackMor1 Kufp data.Pbk eq_fp

/-- Then, to equip it with a structure of an adjoint, we require it to be universal in the
following sense:
* for every `Kuf : ChosenPullback u f` and morphism `Kuf ⟶ c`, we can give a morphism
  `d ⟶ data.P` (which is the first function of the hom-bijection),
* the morphism `d ⟶ data.P` is a morphism in the slice category,
* the data satisfies the left triangle operation (denoted `comm` here), and
* there is a unique morphism satisfying the previous property.

[Paper, §2.1, Prop. `prop:exp-mor-P-def`]: universality of the counit, i.e. `D.P` is `P_u(c)`. -/
class Universal (data : Data u c) where
  mor : ∀ {d : C} {f : d ⟶ X} {Kuf : ChosenPullback u f},
      ((Kuf : C) ⟶ c) → (d ⟶ data.P)
  isSlice : ∀ {d : C} {f : d ⟶ X} {Kuf : ChosenPullback u f} (g : (Kuf : C) ⟶ c),
      f = mor g ≫ data.pi
  comm : ∀ {d : C} {f : d ⟶ X} {Kuf : ChosenPullback u f} (g : (Kuf : C) ⟶ c),
      g = FBF_on_mor data Kuf (isSlice g) ≫ data.epsilon
  uniq : ∀ {d : C} {f g : d ⟶ data.P} {h : d ⟶ X} (Kufp : ChosenPullback u h)
      (eq_fp : h = f ≫ data.pi) (eq_gp : h = g ≫ data.pi),
      FBF_on_mor data Kufp eq_fp ≫ data.epsilon = FBF_on_mor data Kufp eq_gp ≫ data.epsilon →
      f = g

/-- The last property can be simply seen as requiring `mor` to be unique. -/
lemma mor_unique {d1 : Data u c} [Universal d1] {d : C} {f : d ⟶ X} {Kuf : ChosenPullback u f}
    (g : (Kuf : C) ⟶ c) (h : d ⟶ d1.P) (isSlice_f : f = h ≫ d1.pi)
    (hg : g = pullbackMor1 Kuf d1.Pbk isSlice_f ≫ d1.epsilon) :
    h = Universal.mor g := by
  apply Universal.uniq Kuf isSlice_f (Universal.isSlice g)
  have hg' : g = FBF_on_mor d1 Kuf isSlice_f ≫ d1.epsilon := hg
  rw [← hg', ← Universal.comm]

/-- We can define the canonical morphism between two instances of `Data` for `c` by
the universal property quite easily. -/
def canonical_mor (udata : Data u c) [Universal udata] (data' : Data u c) :
    data'.P ⟶ udata.P :=
  Universal.mor data'.epsilon

/-- We can define the canonical morphism between an instance of `Data` for `c` and an
instance for `c'` also using the universal property. -/
def canonical_mor' {c c' : C} (f : c ⟶ c') (udata : Data u c') [Universal udata]
    (data' : Data u c) : data'.P ⟶ udata.P :=
  Universal.mor (data'.epsilon ≫ f)

/-- We can show that the action of the fiber product functor on morphisms preserves the
`epsilon` (coUnit). -/
lemma FBF_on_mor_epsilon (d1 : Data u c) [Universal d1] (d2 : Data u c) :
    d2.epsilon = FBF_on_mor d1 d2.Pbk (Universal.isSlice d2.epsilon) ≫ d1.epsilon :=
  Universal.comm d2.epsilon

lemma FBF_on_mor_epsilon' {c c' : C} (f : c ⟶ c') (d1 : Data u c') [Universal d1]
    (d2 : Data u c) :
    d2.epsilon ≫ f = FBF_on_mor d1 d2.Pbk (Universal.isSlice (d2.epsilon ≫ f)) ≫ d1.epsilon :=
  Universal.comm (d2.epsilon ≫ f)

/-- Conversely, if a canonical morphism has an inverse, then
the domain data was already universal. -/
@[reducible]
noncomputable def canonical_mor_iso_lift (d1 : Data u c) [Universal d1] (d2 : Data u c)
    [IsIso (canonical_mor d1 d2)] : Universal d2 where
  mor g := Universal.mor g ≫ inv (canonical_mor d1 d2)
  isSlice {d} {f} {Kuf} g := by
    have h1 := Universal.isSlice g (data := d1)
    have h2 : d2.pi = canonical_mor d1 d2 ≫ d1.pi := Universal.isSlice d2.epsilon (data := d1)
    rw [Category.assoc]
    have h_inv : inv (canonical_mor d1 d2) ≫ d2.pi = d1.pi := by
      rw [IsIso.inv_comp_eq]
      exact h2
    rw [h_inv]
    exact h1
  comm {d} {f} {Kuf} g := by
    suffices ∀ (h : d ⟶ d2.P) (isSlice_g_d2 : f = h ≫ d2.pi) (h1 : d ⟶ d1.P)
        (isSlice_g_d1 : f = h1 ≫ d1.pi) (h2 : d2.P ⟶ d1.P) (eps2 : d2.pi = h2 ≫ d1.pi),
        h ≫ h2 = h1 →
        g = FBF_on_mor d1 Kuf isSlice_g_d1 ≫ d1.epsilon →
        d2.epsilon = FBF_on_mor d1 d2.Pbk eps2 ≫ d1.epsilon →
        g = FBF_on_mor d2 Kuf isSlice_g_d2 ≫ d2.epsilon by
      apply this (Universal.mor g ≫ inv (canonical_mor d1 d2)) _ (Universal.mor g) _ (canonical_mor d1 d2) _
      · simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      · exact Universal.comm g (data := d1)
      · exact Universal.comm d2.epsilon (data := d1)
    intro h isSlice_g_d2 h1 isSlice_g_d1 h2 eps2 h_eq g_eq d2_eps_eq
    rw [d2_eps_eq, ← Category.assoc, g_eq]
    congr 1
    dsimp [FBF_on_mor, pullbackMor1]
    ext
    · simp only [IsPullback.lift_fst, Category.assoc]
    · simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
      rw [h_eq]
  uniq {d} {f g} {h} Kufp eq_fp eq_gp eq_eps := by
    let f' := f ≫ canonical_mor d1 d2
    let g' := g ≫ canonical_mor d1 d2
    have eps2 : d2.pi = canonical_mor d1 d2 ≫ d1.pi := Universal.isSlice d2.epsilon (data := d1)
    have eq_fp' : h = f' ≫ d1.pi := by
      dsimp [f']
      rw [Category.assoc, ← eps2, eq_fp]
    have eq_gp' : h = g' ≫ d1.pi := by
      dsimp [g']
      rw [Category.assoc, ← eps2, eq_gp]
    have h1 := Universal.uniq Kufp eq_fp' eq_gp' (data := d1)
    have d2_eps_eq : d2.epsilon = FBF_on_mor d1 d2.Pbk eps2 ≫ d1.epsilon :=
      Universal.comm d2.epsilon (data := d1)
    have h_eq_f : FBF_on_mor d2 Kufp eq_fp ≫ d2.epsilon = FBF_on_mor d1 Kufp eq_fp' ≫ d1.epsilon := by
      rw [d2_eps_eq, ← Category.assoc]
      congr 1
      dsimp [FBF_on_mor, pullbackMor1, f']
      ext
      · simp only [IsPullback.lift_fst, Category.assoc]
      · simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
    have h_eq_g : FBF_on_mor d2 Kufp eq_gp ≫ d2.epsilon = FBF_on_mor d1 Kufp eq_gp' ≫ d1.epsilon := by
      rw [d2_eps_eq, ← Category.assoc]
      congr 1
      dsimp [FBF_on_mor, pullbackMor1, g']
      ext
      · simp only [IsPullback.lift_fst, Category.assoc]
      · simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
    rw [h_eq_f, h_eq_g] at eq_eps
    have eq_f_g := h1 eq_eps
    dsimp [f', g'] at eq_f_g
    rw [← cancel_mono (canonical_mor d1 d2)]
    exact eq_f_g

/-- Two universal `Data`s for the same morphism are isomorphic:
the morphisms are the canonical comparison morphisms. -/
lemma canonical_mor_isIso (d1 : Data u c) [Universal d1] (d2 : Data u c) [Universal d2] :
    canonical_mor d1 d2 ≫ canonical_mor d2 d1 = 𝟙 d2.P := by
  have H1 : d2.pi = canonical_mor d1 d2 ≫ d1.pi := Universal.isSlice d2.epsilon
  have H2 : d1.pi = canonical_mor d2 d1 ≫ d2.pi := Universal.isSlice d1.epsilon
  have eq_fp : d2.pi = (canonical_mor d1 d2 ≫ canonical_mor d2 d1) ≫ d2.pi := by
    rw [Category.assoc, ← H2, ← H1]
  have eq_gp : d2.pi = 𝟙 d2.P ≫ d2.pi := by simp
  apply Universal.uniq d2.Pbk eq_fp eq_gp
  have rhs : FBF_on_mor d2 d2.Pbk eq_gp = 𝟙 (d2.Pbk : C) := by
    dsimp [FBF_on_mor, pullbackMor1]; ext <;> simp
  rw [rhs, Category.id_comp]
  have lhs : FBF_on_mor d2 d2.Pbk eq_fp =
      FBF_on_mor d1 d2.Pbk H1 ≫ FBF_on_mor d2 d1.Pbk H2 := by
    dsimp [FBF_on_mor, pullbackMor1]; ext <;> simp
  rw [lhs, Category.assoc]
  have h2_eq : FBF_on_mor d2 d1.Pbk H2 ≫ d2.epsilon = d1.epsilon :=
    (Universal.comm d1.epsilon).symm
  rw [h2_eq]
  exact (Universal.comm d2.epsilon).symm

/-- Unicity of canonical morphisms. -/
lemma canonical_mor_unique (d1 : Data u c) [Universal d1] (d2 : Data u c) [Universal d2]
    (f : d2.P ⟶ d1.P) (hf_pi : d2.pi = f ≫ d1.pi)
    (hf_eps : d2.epsilon = FBF_on_mor d1 d2.Pbk hf_pi ≫ d1.epsilon) :
    f = canonical_mor d1 d2 :=
  mor_unique (d1 := d1) d2.epsilon f hf_pi hf_eps

lemma canonical_mor_unique' {c' : C} (g : c ⟶ c') (d1 : Data u c') [Universal d1]
    (d2 : Data u c) [Universal d2] (f : d2.P ⟶ d1.P)
    (hf_pi : d2.pi = f ≫ d1.pi)
    (hf_eps : d2.epsilon ≫ g = FBF_on_mor d1 d2.Pbk hf_pi ≫ d1.epsilon) :
    f = canonical_mor' g d1 d2 :=
  mor_unique (d1 := d1) (d2.epsilon ≫ g) f hf_pi hf_eps


section IsomorphicArrows
variable {C : Type*} [Category C] {X X' Y Y' : C} {u : Y ⟶ X} {u' : Y' ⟶ X'}
  (f : Arrow.mk u ≅ Arrow.mk u')

lemma w_hom : u ≫ f.hom.right = f.hom.left ≫ u' := by
  have := f.hom.w
  exact this.symm

lemma w_inv : u' ≫ f.inv.right = f.inv.left ≫ u := by
  have := f.inv.w
  exact this.symm

lemma right_hom_inv : f.hom.right ≫ f.inv.right = 𝟙 X := congrArg CommaMorphism.right f.hom_inv_id
lemma left_hom_inv : f.hom.left ≫ f.inv.left = 𝟙 Y := congrArg CommaMorphism.left f.hom_inv_id
lemma right_inv_hom : f.inv.right ≫ f.hom.right = 𝟙 X' := congrArg CommaMorphism.right f.inv_hom_id
lemma left_inv_hom : f.inv.left ≫ f.hom.left = 𝟙 Y' := congrArg CommaMorphism.left f.inv_hom_id

noncomputable def pullBackTransform {d_obj : C} {f_d : d_obj ⟶ X'}
  (Kuf' : ChosenPullback u' f_d) : ChosenPullback u (f_d ≫ f.inv.right) where
  pullback := Kuf'.pullback
  p₁ := Kuf'.p₁ ≫ f.inv.left
  p₂ := Kuf'.p₂
  condition := by
    have w_inv_loc : u' ≫ f.inv.right = f.inv.left ≫ u := by
      have := f.inv.w
      exact this.symm
    rw [Category.assoc, ← w_inv_loc, ← Category.assoc, Kuf'.condition, Category.assoc]
  isLimit := by
    have w_inv_loc : u' ≫ f.inv.right = f.inv.left ≫ u := by
      have := f.inv.w
      exact this.symm
    have pb1 : IsPullback Kuf'.p₁ Kuf'.p₂ u' f_d := IsPullback.of_isLimit Kuf'.isLimit
    have pb2 : IsPullback f.inv.left u' u f.inv.right := IsPullback.of_horiz_isIso ⟨w_inv_loc.symm⟩
    exact (IsPullback.paste_horiz pb1 pb2).isLimit

/-- Transporting `FBF_on_mor` along the isomorphism of arrows: computing the morphism induced
by the new pullback data is the same as computing it with the original data after transporting
the pullback back along `f`. -/
private lemma fbt_transport {c : C} (d : Data u c) {pi' : d.P ⟶ X'}
    {w : (d.Pbk : C) ⟶ Y'} (sq : w ≫ u' = d.Pbk.p₂ ≫ pi')
    (upbk : IsLimit (PullbackCone.mk w d.Pbk.p₂ sq))
    (hw : w = d.Pbk.p₁ ≫ f.hom.left)
    {d_obj : C} {h : d_obj ⟶ X'} (Kufp : ChosenPullback u' h) {k : d_obj ⟶ d.P}
    (eqk : h = k ≫ pi') (eqk' : h ≫ f.inv.right = k ≫ d.pi) :
    FBF_on_mor (u := u') (c := c) {
      P := d.P
      pi := pi'
      Pbk := {
        pullback := d.Pbk.pullback
        p₁ := w
        p₂ := d.Pbk.p₂
        condition := sq
        isLimit := upbk
      }
      epsilon := d.epsilon
    } Kufp eqk = FBF_on_mor d (pullBackTransform f Kufp) eqk' := by
  dsimp [FBF_on_mor, pullbackMor1, pullBackTransform]
  have ipb : IsPullback w d.Pbk.p₂ u' pi' := IsPullback.of_isLimit upbk
  refine ipb.hom_ext ?_ ?_
  · rw [IsPullback.lift_fst, hw, ← Category.assoc, IsPullback.lift_fst, Category.assoc,
      left_inv_hom, Category.comp_id]
  · simp only [IsPullback.lift_snd]

@[reducible]
noncomputable def lift_arrow_iso_univ_helper {c : C} (d : Data u c) [Universal d] {pi' : d.P ⟶ X'}
   (eq_pi' : pi' = d.pi ≫ f.hom.right) {w : (d.Pbk : C) ⟶ Y'}
   (sq : w ≫ u' = d.Pbk.p₂ ≫ pi')
   (upbk : IsLimit (PullbackCone.mk w d.Pbk.p₂ sq))
   (hw : w = d.Pbk.p₁ ≫ f.hom.left) :
   Universal (u := u') (c := c) {
     P := d.P
     pi := pi'
     Pbk := {
       pullback := d.Pbk.pullback
       p₁ := w
       p₂ := d.Pbk.p₂
       condition := sq
       isLimit := upbk
     }
     epsilon := d.epsilon
   } where
  mor := fun {_ _ Kuf'} g' => Universal.mor (data := d) (Kuf := pullBackTransform f Kuf') g'
  isSlice := by
    intro d' f' Kuf' g'
    change f' = Universal.mor (data := d) (Kuf := pullBackTransform f Kuf') g' ≫ pi'
    have hs := Universal.isSlice (data := d) (Kuf := pullBackTransform f Kuf')
      (f := f' ≫ f.inv.right) (g := g')
    rw [eq_pi', ← reassoc_of% hs, right_inv_hom, Category.comp_id]
  comm := by
    intro d' f' Kuf' g'
    have hs' := Universal.isSlice (data := d) (Kuf := pullBackTransform f Kuf')
      (f := f' ≫ f.inv.right) (g := g')
    have eqk : f' = Universal.mor (data := d) (Kuf := pullBackTransform f Kuf') g' ≫ pi' := by
      rw [eq_pi', ← reassoc_of% hs', right_inv_hom, Category.comp_id]
    refine (Universal.comm (data := d) (Kuf := pullBackTransform f Kuf')
      (f := f' ≫ f.inv.right) (g := g')).trans ?_
    rw [← fbt_transport f d sq upbk hw Kuf' eqk hs']
  uniq := by
    intro d' f'' g'' h'' Kufp eq_fp eq_gp eq_eps
    have pifix : pi' ≫ f.inv.right = d.pi := by
      rw [eq_pi', Category.assoc, right_hom_inv, Category.comp_id]
    have hsF : h'' ≫ f.inv.right = f'' ≫ d.pi := by
      simp only [eq_fp, Category.assoc, pifix]
    have hsG : h'' ≫ f.inv.right = g'' ≫ d.pi := by
      simp only [eq_gp, Category.assoc, pifix]
    rw [fbt_transport f d sq upbk hw Kufp eq_fp hsF,
      fbt_transport f d sq upbk hw Kufp eq_gp hsG] at eq_eps
    exact Universal.uniq (data := d) (Kufp := pullBackTransform f Kufp) hsF hsG eq_eps

/-- Transport `Data` along an isomorphism of arrows. -/
noncomputable def lift_arrow_iso {c : C} (d : Data u c) : Data u' c where
  P := d.P
  pi := d.pi ≫ f.hom.right
  Pbk := {
    pullback := d.Pbk.pullback
    p₁ := d.Pbk.p₁ ≫ f.hom.left
    p₂ := d.Pbk.p₂
    condition := by
      rw [Category.assoc, ← w_hom f, ← Category.assoc, d.Pbk.condition, Category.assoc]
    isLimit := by
      have pb1 : IsPullback d.Pbk.p₁ d.Pbk.p₂ u d.pi := IsPullback.of_isLimit d.Pbk.isLimit
      have pb2 : IsPullback f.hom.left u u' f.hom.right :=
        IsPullback.of_horiz_isIso ⟨(w_hom f).symm⟩
      exact (IsPullback.paste_horiz pb1 pb2).isLimit
  }
  epsilon := d.epsilon

/-- If two arrows are isomorphic, then the universality of an arrow can be recovered from
the universality of the other arrow. -/
@[reducible]
noncomputable def lift_arrow_iso_univ {c : C} (d : Data u c) [Universal d] :
    Universal (lift_arrow_iso f d) :=
  lift_arrow_iso_univ_helper f d (pi' := (lift_arrow_iso f d).pi) rfl
    (w := (lift_arrow_iso f d).Pbk.p₁) (lift_arrow_iso f d).Pbk.condition
    (lift_arrow_iso f d).Pbk.isLimit rfl

/-- ...and conversely. -/
@[reducible]
noncomputable def lift_arrow_iso_univ' {c : C} (d : Data u c)
    [Universal (lift_arrow_iso f d)] : Universal d := by
  obtain ⟨P, pi, ⟨pb, p1, p2, cond, il⟩, eps⟩ := d
  exact lift_arrow_iso_univ_helper f.symm
    (lift_arrow_iso f ⟨P, pi, { pullback := pb, p₁ := p1, p₂ := p2, condition := cond,
                                isLimit := il }, eps⟩) (pi' := pi)
    (by
      change pi = (pi ≫ f.hom.right) ≫ f.inv.right
      rw [Category.assoc, right_hom_inv, Category.comp_id])
    (w := p1) cond il
    (by
      change p1 = (p1 ≫ f.hom.left) ≫ f.inv.left
      rw [Category.assoc, left_hom_inv, Category.comp_id])

end IsomorphicArrows

section FunctorPreservation

variable {C : Type*} [Category C] {D : Type*} [Category D] {X Y : C}

/-- The image of a chosen pullback under a functor preserving pullbacks. -/
noncomputable def functPullback (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} (h : ChosenPullback f₁ f₂) :
    ChosenPullback (F.map f₁) (F.map f₂) where
  pullback := F.obj h.pullback
  p₁ := F.map h.p₁
  p₂ := F.map h.p₂
  condition := by rw [← F.map_comp, ← F.map_comp, h.condition]
  isLimit := (Functor.map_isPullback F h.isPullback).isLimit

/-- The image of `Data` under a functor preserving pullbacks. -/
noncomputable def functor_on {u : Y ⟶ X} (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {c : C} (d : Data u c) : Data (F.map u) (F.obj c) where
  P := F.obj d.P
  pi := F.map d.pi
  Pbk := functPullback F d.Pbk
  epsilon := F.map d.epsilon

/-- The functor `F` sends universal `Data` for `u` to universal `Data` for `F u`.

[Paper, §2.1, Def. `def:preserves-pushforwards`], in the form of [Paper, §2.1, Lemma `lem:preservation_pushforward`]. -/
class FunctorPreserves (u : Y ⟶ X) (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F] where
  functor_preserves : ∀ {c : C} (d : Data u c), Universal d → Universal (functor_on F d)

lemma Universal.ext_mor {u : Y ⟶ X} {c : C} {d : Data u c} (U₀ U₁ : Universal d)
    (h : ∀ {d' : C} {f : d' ⟶ X} {Kuf : ChosenPullback u f} (g : (Kuf : C) ⟶ c),
      U₀.mor g = U₁.mor g) : U₀ = U₁ := by
  obtain ⟨m₀, _, _, _⟩ := U₀
  obtain ⟨m₁, _, _, _⟩ := U₁
  have hm : @m₀ = @m₁ := by
    funext d' f Kuf g
    exact h g
  subst hm
  rfl

lemma isProp_FunctorPreserves (u : Y ⟶ X) (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] (pres₀ pres₁ : FunctorPreserves u F)
    (h : ∀ (c : C) (d : Data u c) (univ : Universal d) (d' : D) (f : d' ⟶ F.obj X)
      (Kuf : ChosenPullback (F.map u) f) (g : (Kuf : D) ⟶ F.obj c),
      (pres₀.functor_preserves d univ).mor g = (pres₁.functor_preserves d univ).mor g) :
    pres₀ = pres₁ := by
  obtain ⟨p₀⟩ := pres₀
  obtain ⟨p₁⟩ := pres₁
  congr
  funext c d univ
  exact Universal.ext_mor _ _ fun g => h c d univ _ _ _ g

noncomputable instance functor_preserves_id (u : Y ⟶ X) : FunctorPreserves u (𝟭 C) where
  functor_preserves d univ :=
    have := univ
    lift_arrow_iso_univ_helper (Iso.refl (Arrow.mk u)) d
      (pi' := (functor_on (𝟭 C) d).pi) (by simp [functor_on])
      (w := (functor_on (𝟭 C) d).Pbk.p₁) (functor_on (𝟭 C) d).Pbk.condition
      (functor_on (𝟭 C) d).Pbk.isLimit (by simp [functor_on, functPullback])

noncomputable instance functor_preserves_comp (u : Y ⟶ X) {E : Type*} [Category E]
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]
    [FunctorPreserves u F] [FunctorPreserves (F.map u) G] : FunctorPreserves u (F ⋙ G) where
  functor_preserves d univ :=
    FunctorPreserves.functor_preserves (F := G) (functor_on F d)
      (FunctorPreserves.functor_preserves (F := F) d univ)

/-- It suffices to check preservation of universality on one universal `Data` for each `c`. -/
@[reducible]
noncomputable def functor_preserves_1_is_enough (u : Y ⟶ X) (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] (dc : ∀ c, Data u c) (uc : ∀ c, Universal (dc c))
    (hF : ∀ c, Universal (functor_on F (dc c))) : FunctorPreserves u F where
  functor_preserves {c} d univ := by
    have := uc c
    have := hF c
    have : IsIso (canonical_mor (dc c) d) :=
      ⟨canonical_mor d (dc c), canonical_mor_isIso (dc c) d, canonical_mor_isIso d (dc c)⟩
    have hpi : d.pi = canonical_mor (dc c) d ≫ (dc c).pi := Universal.isSlice d.epsilon
    have hpi' : F.map d.pi = F.map (canonical_mor (dc c) d) ≫ F.map (dc c).pi := by
      rw [← F.map_comp, ← hpi]
    have key : F.map (canonical_mor (dc c) d) =
        canonical_mor (functor_on F (dc c)) (functor_on F d) := by
      refine mor_unique (d1 := functor_on F (dc c)) (functor_on F d).epsilon _ hpi' ?_
      have heps : d.epsilon = FBF_on_mor (dc c) d.Pbk hpi ≫ (dc c).epsilon :=
        Universal.comm d.epsilon
      change F.map d.epsilon = _ ≫ F.map (dc c).epsilon
      rw [heps, F.map_comp]
      congr 1
      apply ChosenPullback.hom_ext (functor_on F (dc c)).Pbk
      · change F.map _ ≫ F.map _ = _
        rw [← F.map_comp]
        simp only [pullbackMor1, FBF_on_mor, IsPullback.lift_fst]
        rfl
      · change F.map _ ≫ F.map _ = _
        rw [← F.map_comp]
        simp only [pullbackMor1, FBF_on_mor, IsPullback.lift_snd, F.map_comp]
        rfl
    have : IsIso (canonical_mor (functor_on F (dc c)) (functor_on F d)) := by
      rw [← key]; exact Functor.map_isIso F _
    exact canonical_mor_iso_lift (functor_on F (dc c)) (functor_on F d)

/-- Universality of `functor_on F (lift_arrow_iso i d)` gives universality of the transport of
`functor_on F d` along the image of `i`. -/
@[reducible]
noncomputable def lift_arrow_iso_on_functor {X' Y' : C} {u : Y ⟶ X} {v : Y' ⟶ X'} (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] (i : Arrow.mk v ≅ Arrow.mk u) {c : C} (d : Data v c)
    (huniv : Universal (functor_on F (lift_arrow_iso i d))) :
    Universal (lift_arrow_iso (F.mapArrow.mapIso i) (functor_on F d)) :=
  have := huniv
  lift_arrow_iso_univ_helper (Iso.refl (Arrow.mk (F.map u))) (functor_on F (lift_arrow_iso i d))
    (pi' := (lift_arrow_iso (F.mapArrow.mapIso i) (functor_on F d)).pi)
    (by simp [lift_arrow_iso, functor_on])
    (w := (lift_arrow_iso (F.mapArrow.mapIso i) (functor_on F d)).Pbk.p₁)
    (lift_arrow_iso (F.mapArrow.mapIso i) (functor_on F d)).Pbk.condition
    (lift_arrow_iso (F.mapArrow.mapIso i) (functor_on F d)).Pbk.isLimit
    (by simp [lift_arrow_iso, functor_on, functPullback])

@[reducible]
noncomputable def functor_preserves_iso {X' Y' : C} (u : Y ⟶ X) (v : Y' ⟶ X') (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] (i : Arrow.mk v ≅ Arrow.mk u)
    [FunctorPreserves u F] : FunctorPreserves v F where
  functor_preserves {c} d huniv := by
    have := huniv
    have h₁ := FunctorPreserves.functor_preserves (u := u) (F := F) (lift_arrow_iso i d)
      (lift_arrow_iso_univ i d)
    have := lift_arrow_iso_on_functor F i d h₁
    exact lift_arrow_iso_univ' (F.mapArrow.mapIso i) (functor_on F d)

end FunctorPreservation

/-- An arrow `u` is partially exponentiable when every `c` has universal `Data`.

[Paper, §2.1, Def. `def:exp-mor`] and [Paper, §2.1, Prop. `prop:exp-mor-P-def`]: exponentiable morphism. -/
class IsExpArr (u : Y ⟶ X) where
  isExpArrowData : ∀ c : C, Data u c
  isExpArrow : ∀ c : C, Universal (isExpArrowData c)

attribute [instance] IsExpArr.isExpArrow
