/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import CartexpAristotle.PartialExponentiability

/-!
# Exponentiable arrows in slices and under base change

If `u : Y ⟶ X` is exponentiable in `C`, `u' : Y' ⟶ X'` is a pullback of `u` along `e : X' ⟶ X`,
and `w : X' ⟶ Z`, then `u'` is exponentiable as an arrow `Over.mk (u' ≫ w) ⟶ Over.mk w` in `Over Z`.

## References

* [Paper, §3.1, Prop. `prop:p2-construction`] (Eq. `eq:p2-diagram`): `sZ = P X`,
  `sE : X̲ → X` the counit `ε_X`, `sW : X̲ → P X`, and `su' : Y̲ → X̲` the morphism `p̲`.
* [Paper, §3.1, Prop. `prop:p2-exponentiable`] and its proof sketch: `p̲` is exponentiable in
  `C / P X` (`SliceExp.sIsExpArr`); more generally a pullback of an exponentiable morphism is
  exponentiable in any slice.
* [Paper, App. A.1, Prop. `prop:p2-description-polynomial`]: explicit description of the
  pushforward along `p̲` (`SliceExp.sOverData`).
-/

open CategoryTheory Limits

universe v u

namespace SliceExp

variable {C : Type u} [Category.{v} C]

section FBF

variable {X Y : C} {u : Y ⟶ X} {c : C}

@[reassoc (attr := simp)]
lemma FBF_on_mor_fst (D : Data u c) {d : C} {f : d ⟶ D.P} {h : d ⟶ X} (K : ChosenPullback u h)
    (eq : h = f ≫ D.pi) : FBF_on_mor D K eq ≫ D.Pbk.p₁ = K.p₁ := by
  simp [FBF_on_mor, pullbackMor1]

@[reassoc (attr := simp)]
lemma FBF_on_mor_snd (D : Data u c) {d : C} {f : d ⟶ D.P} {h : d ⟶ X} (K : ChosenPullback u h)
    (eq : h = f ≫ D.pi) : FBF_on_mor D K eq ≫ D.Pbk.p₂ = K.p₂ ≫ f := by
  simp [FBF_on_mor, pullbackMor1]

lemma FBF_on_mor_map (D : Data u c) {d₁ d₂ : C} {h₁ : d₁ ⟶ X} {h₂ : d₂ ⟶ X}
    (K₁ : ChosenPullback u h₁) (K₂ : ChosenPullback u h₂) (a : d₁ ⟶ d₂)
    (φ : K₁.pullback ⟶ K₂.pullback) (hφ₁ : φ ≫ K₂.p₁ = K₁.p₁) (hφ₂ : φ ≫ K₂.p₂ = K₁.p₂ ≫ a)
    {m₁ : d₁ ⟶ D.P} {m₂ : d₂ ⟶ D.P} (e₁ : h₁ = m₁ ≫ D.pi) (e₂ : h₂ = m₂ ≫ D.pi)
    (hm : a ≫ m₂ = m₁) : FBF_on_mor D K₁ e₁ = φ ≫ FBF_on_mor D K₂ e₂ := by
  apply D.Pbk.hom_ext
  · simp [hφ₁]
  · simp only [FBF_on_mor_snd, Category.assoc]
    rw [reassoc_of% hφ₂, hm]

lemma FBF_on_mor_congr (D : Data u c) {d : C} {h : d ⟶ X} (K : ChosenPullback u h)
    {m m' : d ⟶ D.P} (hm : m = m') (e : h = m ≫ D.pi) (e' : h = m' ≫ D.pi) :
    FBF_on_mor D K e = FBF_on_mor D K e' := by
  subst hm
  rfl

/-- A chosen pullback from a pullback square. -/
@[reducible] noncomputable def chosenOfIsPullback {X₁ X₂ S P : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {p₁ : P ⟶ X₁}
    {p₂ : P ⟶ X₂} (h : IsPullback p₁ p₂ f₁ f₂) : ChosenPullback f₁ f₂ where
  pullback := P
  p₁ := p₁
  p₂ := p₂
  condition := h.w
  isLimit := h.isLimit

/-- Pasting a chosen pullback with a pullback square. -/
@[reducible] noncomputable def pasteCP {X' Y' : C} {u' : Y' ⟶ X'} {p₁' : Y' ⟶ Y} {e : X' ⟶ X}
    (hpb : IsPullback p₁' u' u e) {d : C} {f : d ⟶ X'} (K : ChosenPullback u' f) :
    ChosenPullback u (f ≫ e) :=
  chosenOfIsPullback (IsPullback.paste_horiz K.isPullback hpb)

end FBF

section CLevel

/-- Universality of `D` restricted to the maps over `Z` (the property that makes it universal in
`Over Z`). -/
structure SliceUniv {X' Y' : C} {u' : Y' ⟶ X'} {c Z : C} (D : Data u' c) (q : c ⟶ Z)
    (w : X' ⟶ Z) : Prop where
  exists_mor : ∀ {d : C} {f : d ⟶ X'} (K : ChosenPullback u' f) (g : K.pullback ⟶ c),
    g ≫ q = K.p₂ ≫ f ≫ w →
      ∃ (m : d ⟶ D.P) (h : f = m ≫ D.pi), g = FBF_on_mor D K h ≫ D.epsilon
  uniq : ∀ {d : C} {f : d ⟶ X'} (K : ChosenPullback u' f) {m m' : d ⟶ D.P}
    (h : f = m ≫ D.pi) (h' : f = m' ≫ D.pi),
    FBF_on_mor D K h ≫ D.epsilon = FBF_on_mor D K h' ≫ D.epsilon → m = m'

variable {X Y X' Y' c Z : C} {u : Y ⟶ X} {u' : Y' ⟶ X'} {p₁' : Y' ⟶ Y} {e : X' ⟶ X}

/-- The comparison from the pullback of `u'` along `pi'` to the pullback of `u` along `dc.pi`. -/
noncomputable def liftPbk' (hpb : IsPullback p₁' u' u e) (dc : Data u c) {P : C} {pi' : P ⟶ X'}
    (K : ChosenPullback u' pi') (ω : P ⟶ dc.P) (hω : ω ≫ dc.pi = pi' ≫ e) :
    K.pullback ⟶ dc.Pbk.pullback :=
  dc.Pbk.isPullback.lift (K.p₁ ≫ p₁') (K.p₂ ≫ ω) (by
    rw [Category.assoc, hpb.w, ← Category.assoc, K.condition, Category.assoc, Category.assoc,
      hω])

/-- The comparison from the pullback of `u'` along `D.pi` to the pullback of `u` along `dc.pi`. -/
noncomputable def liftPbk (hpb : IsPullback p₁' u' u e) (dc : Data u c) (D : Data u' c)
    (ω : D.P ⟶ dc.P) (hω : ω ≫ dc.pi = D.pi ≫ e) : D.Pbk.pullback ⟶ dc.Pbk.pullback :=
  liftPbk' hpb dc D.Pbk ω hω

lemma FBF_liftPbk (hpb : IsPullback p₁' u' u e) (dc : Data u c) (D : Data u' c) (ω : D.P ⟶ dc.P)
    (hω : ω ≫ dc.pi = D.pi ≫ e) {d : C} {f : d ⟶ X'} (K : ChosenPullback u' f) {m : d ⟶ D.P}
    (h : f = m ≫ D.pi) (h' : f ≫ e = (m ≫ ω) ≫ dc.pi) :
    FBF_on_mor D K h ≫ liftPbk hpb dc D ω hω = FBF_on_mor dc (pasteCP hpb K) h' := by
  apply dc.Pbk.hom_ext
  · simp [liftPbk, liftPbk', pasteCP, chosenOfIsPullback]
  · simp [liftPbk, liftPbk', pasteCP, chosenOfIsPullback]

theorem sliceUniv_of_isPullback (hpb : IsPullback p₁' u' u e) (dc : Data u c) [Universal dc]
    (dZ : Data u Z) [Universal dZ] (q : c ⟶ Z) (w : X' ⟶ Z)
    (Pq : dc.P ⟶ dZ.P) (hPq : dc.pi = Pq ≫ dZ.pi)
    (hPqε : FBF_on_mor dZ dc.Pbk hPq ≫ dZ.epsilon = dc.epsilon ≫ q)
    (τ : X' ⟶ dZ.P) (hτ : e = τ ≫ dZ.pi)
    (hτε : u' ≫ w = FBF_on_mor dZ (chosenOfIsPullback hpb) hτ ≫ dZ.epsilon)
    (D : Data u' c) (ω : D.P ⟶ dc.P) (hω : ω ≫ dc.pi = D.pi ≫ e)
    (hW : IsPullback ω D.pi Pq τ)
    (hε : D.epsilon = liftPbk hpb dc D ω hω ≫ dc.epsilon) :
    SliceUniv D q w := by
  refine ⟨fun {d f} K g hg => ?_, fun {d f} K {m m'} h h' H => ?_⟩
  · obtain ⟨m₀, hs, hc⟩ : ∃ (m₀ : d ⟶ dc.P) (hs : f ≫ e = m₀ ≫ dc.pi),
        g = FBF_on_mor dc (pasteCP hpb K) hs ≫ dc.epsilon :=
      ⟨_, Universal.isSlice (data := dc) (Kuf := pasteCP hpb K) g, Universal.comm (data := dc) (Kuf := pasteCP hpb K) g⟩
    have eq1 : f ≫ e = (m₀ ≫ Pq) ≫ dZ.pi := by rw [Category.assoc, ← hPq]; exact hs
    have eq2 : f ≫ e = (f ≫ τ) ≫ dZ.pi := by rw [Category.assoc, ← hτ]
    have key : m₀ ≫ Pq = f ≫ τ := by
      refine Universal.uniq (data := dZ) (pasteCP hpb K) eq1 eq2 ?_
      have L := FBF_on_mor_map dZ (pasteCP hpb K) dc.Pbk m₀ (FBF_on_mor dc (pasteCP hpb K) hs)
        (FBF_on_mor_fst _ _ _) (FBF_on_mor_snd _ _ _) eq1 hPq rfl
      have R := FBF_on_mor_map dZ (pasteCP hpb K) (chosenOfIsPullback hpb) f K.p₁
        (by simp [pasteCP, chosenOfIsPullback]) (by simp [pasteCP, chosenOfIsPullback, K.condition]) eq2 hτ rfl
      rw [L, R]
      simp only [Category.assoc]
      rw [hPqε, ← hτε, ← Category.assoc, ← hc]
      exact hg.trans (K.condition_assoc w).symm
    have hm1 : hW.lift m₀ f (by simpa using key) ≫ ω = m₀ := hW.lift_fst _ _ _
    have hm2 : hW.lift m₀ f (by simpa using key) ≫ D.pi = f := hW.lift_snd _ _ _
    refine ⟨hW.lift m₀ f (by simpa using key), hm2.symm, ?_⟩
    rw [hε, ← Category.assoc, FBF_liftPbk hpb dc D ω hω K hm2.symm (by rw [hm1]; exact hs),
      FBF_on_mor_congr dc _ hm1 _ hs]
    exact hc
  · have h1 : f ≫ e = (m ≫ ω) ≫ dc.pi := by rw [Category.assoc, hω, ← Category.assoc, ← h]
    have h2 : f ≫ e = (m' ≫ ω) ≫ dc.pi := by rw [Category.assoc, hω, ← Category.assoc, ← h']
    refine hW.hom_ext ?_ (h.symm.trans h')
    refine Universal.uniq (data := dc) (pasteCP hpb K) h1 h2 ?_
    rw [← FBF_liftPbk hpb dc D ω hω K h h1, ← FBF_liftPbk hpb dc D ω hω K h' h2,
      Category.assoc, Category.assoc, ← hε]
    exact H

end CLevel

section OverLevel

variable {Z : C} {A B : Over Z} (U : A ⟶ B)

/-- A chosen pullback in `Over Z` gives one in `C`. -/
noncomputable def forgetCP {d : Over Z} {f : d ⟶ B} (K : ChosenPullback U f) :
    ChosenPullback U.left f.left where
  pullback := K.pullback.left
  p₁ := K.p₁.left
  p₂ := K.p₂.left
  condition := congrArg CommaMorphism.left K.condition
  isLimit := (Functor.map_isPullback (Over.forget Z) K.isPullback).isLimit

/-- The underlying `Data` in `C` of a `Data` in `Over Z`. -/
noncomputable def forgetData {c : Over Z} (D : Data U c) : Data U.left c.left where
  P := D.P.left
  pi := D.pi.left
  Pbk := forgetCP U D.Pbk
  epsilon := D.epsilon.left

lemma forget_FBF {c : Over Z} (D : Data U c) {d : Over Z} {f : d ⟶ D.P} {h : d ⟶ B}
    (K : ChosenPullback U h) (e : h = f ≫ D.pi) :
    (FBF_on_mor D K e).left =
      FBF_on_mor (forgetData U D) (forgetCP U K) (f := f.left) (congrArg CommaMorphism.left e) := by
  apply (forgetData U D).Pbk.hom_ext
  · exact (congrArg CommaMorphism.left (FBF_on_mor_fst D K e)).trans
      (FBF_on_mor_fst (forgetData U D) (forgetCP U K) _).symm
  · exact (congrArg CommaMorphism.left (FBF_on_mor_snd D K e)).trans
      (FBF_on_mor_snd (forgetData U D) (forgetCP U K) _).symm

lemma over_exists {c : Over Z} (D : Data U c)
    (h : SliceUniv (forgetData U D) c.hom B.hom) {d : Over Z} {f : d ⟶ B}
    (K : ChosenPullback U f) (g : K.pullback ⟶ c) :
    ∃ (m : d ⟶ D.P) (hm : f = m ≫ D.pi), g = FBF_on_mor D K hm ≫ D.epsilon := by
  have hg : g.left ≫ c.hom = (forgetCP U K).p₂ ≫ f.left ≫ B.hom := by
    have h1 : g.left ≫ c.hom = K.pullback.hom := Over.w g
    have h2 : K.p₂.left ≫ d.hom = K.pullback.hom := Over.w K.p₂
    have h3 : f.left ≫ B.hom = d.hom := Over.w f
    change g.left ≫ c.hom = K.p₂.left ≫ f.left ≫ B.hom
    rw [h1, h3, h2]
  obtain ⟨m, hm, hc⟩ : ∃ (m : d.left ⟶ D.P.left) (hm : f.left = m ≫ D.pi.left),
      g.left = FBF_on_mor (forgetData U D) (forgetCP U K) hm ≫ D.epsilon.left :=
    h.exists_mor (forgetCP U K) g.left hg
  have hmw : m ≫ D.P.hom = d.hom := by
    have h4 : D.pi.left ≫ B.hom = D.P.hom := Over.w D.pi
    have h3 : f.left ≫ B.hom = d.hom := Over.w f
    rw [← h4, ← Category.assoc, ← hm, h3]
  have hm2 : f = Over.homMk (m : d.left ⟶ D.P.left) hmw ≫ D.pi := Over.OverMorphism.ext hm
  refine ⟨Over.homMk (m : d.left ⟶ D.P.left) hmw, hm2, ?_⟩
  refine Over.OverMorphism.ext ?_
  have := forget_FBF U D K hm2
  change g.left = (FBF_on_mor D K hm2 ≫ D.epsilon).left
  rw [Over.comp_left, this]
  exact hc

/-- A chosen pullback in `C` of the underlying maps gives a chosen pullback in `Over Z`. -/
noncomputable def overCP {d : Over Z} (f : d ⟶ B) (K : ChosenPullback U.left f.left) :
    ChosenPullback U f :=
  chosenOfIsPullback (P := Over.mk (K.p₂ ≫ d.hom))
    (p₁ := Over.homMk K.p₁ (by
      change K.p₁ ≫ A.hom = K.p₂ ≫ d.hom
      rw [← Over.w U, ← Category.assoc, K.condition, Category.assoc, Over.w f]))
    (p₂ := Over.homMk K.p₂)
    (IsPullback.of_map_of_faithful (Over.forget Z) K.isPullback)

/-- The projection of `overData`. -/
def overPi {P : C} (pi : P ⟶ B.left) : Over.mk (pi ≫ B.hom) ⟶ B :=
  Over.homMk pi rfl

/-- `Data` in `Over Z` built from `Data` in `C` whose counit lies over `Z`. -/
noncomputable def overData {c : Over Z} (D : Data U.left c.left)
    (he : D.epsilon ≫ c.hom = D.Pbk.p₂ ≫ D.pi ≫ B.hom) : Data U c where
  P := Over.mk (D.pi ≫ B.hom)
  pi := overPi D.pi
  Pbk := overCP U (overPi D.pi) D.Pbk
  epsilon := Over.homMk D.epsilon he

/-- Universality in `Over Z` follows from universality in `C` of maps over `Z`. -/
@[reducible]
noncomputable def universal_of_sliceUniv {c : Over Z} (D : Data U c)
    (h : SliceUniv (forgetData U D) c.hom B.hom) : Universal D where
  mor {d f K} g := Classical.choose (over_exists U D h K g)
  isSlice {d f K} g := (Classical.choose_spec (over_exists U D h K g)).1
  comm {d f K} g := (Classical.choose_spec (over_exists U D h K g)).2
  uniq {d f g' k} K eq_fp eq_gp H := by
    refine Over.OverMorphism.ext ?_
    refine h.uniq (forgetCP U K) (congrArg CommaMorphism.left eq_fp)
      (congrArg CommaMorphism.left eq_gp) ?_
    have := congrArg CommaMorphism.left H
    change (FBF_on_mor D K eq_fp ≫ D.epsilon).left = (FBF_on_mor D K eq_gp ≫ D.epsilon).left
      at this
    rw [Over.comp_left, Over.comp_left, forget_FBF U D K eq_fp, forget_FBF U D K eq_gp] at this
    exact this

end OverLevel

section Setup

variable {X Y X' Y' c Z : C} {u : Y ⟶ X} {u' : Y' ⟶ X'} {p₁' : Y' ⟶ Y} {e : X' ⟶ X}

/-- Comparison data witnessing that `D` is the `Data` for `u'` obtained from `dc` by base change
and slicing. -/
structure Setup (hpb : IsPullback p₁' u' u e) (dc : Data u c) (dZ : Data u Z) (q : c ⟶ Z)
    (w : X' ⟶ Z) (D : Data u' c) where
  Pq : dc.P ⟶ dZ.P
  τ : X' ⟶ dZ.P
  ω : D.P ⟶ dc.P
  hPq : dc.pi = Pq ≫ dZ.pi
  hPqε : FBF_on_mor dZ dc.Pbk hPq ≫ dZ.epsilon = dc.epsilon ≫ q
  hτ : e = τ ≫ dZ.pi
  hτε : u' ≫ w = FBF_on_mor dZ (chosenOfIsPullback hpb) hτ ≫ dZ.epsilon
  hω : ω ≫ dc.pi = D.pi ≫ e
  hW : IsPullback ω D.pi Pq τ
  hε : D.epsilon = liftPbk hpb dc D ω hω ≫ dc.epsilon

variable {hpb : IsPullback p₁' u' u e} {dc : Data u c} {dZ : Data u Z} {q : c ⟶ Z} {w : X' ⟶ Z}
  {D : Data u' c}

theorem Setup.sliceUniv (S : Setup hpb dc dZ q w D) [Universal dc] [Universal dZ] :
    SliceUniv D q w :=
  sliceUniv_of_isPullback hpb dc dZ q w S.Pq S.hPq S.hPqε S.τ S.hτ S.hτε D S.ω S.hω S.hW S.hε

/-- `D.epsilon` lies over `Z`. -/
theorem Setup.eps_over (S : Setup hpb dc dZ q w D) [Universal dZ] :
    D.epsilon ≫ q = D.Pbk.p₂ ≫ D.pi ≫ w := by
  have eq1 : D.pi ≫ e = (S.ω ≫ S.Pq) ≫ dZ.pi := by rw [Category.assoc, ← S.hPq, S.hω]
  have eq2 : D.pi ≫ e = (D.pi ≫ S.τ) ≫ dZ.pi := by rw [Category.assoc, ← S.hτ]
  have L := FBF_on_mor_map dZ (pasteCP hpb D.Pbk) dc.Pbk S.ω (liftPbk hpb dc D S.ω S.hω)
    (by simp [liftPbk, liftPbk', pasteCP, chosenOfIsPullback])
    (by simp [liftPbk, liftPbk', pasteCP, chosenOfIsPullback]) eq1 S.hPq rfl
  have R := FBF_on_mor_map dZ (pasteCP hpb D.Pbk) (chosenOfIsPullback hpb) D.pi D.Pbk.p₁
    (by simp [pasteCP, chosenOfIsPullback])
    (by simp [pasteCP, chosenOfIsPullback, D.Pbk.condition]) eq2 S.hτ rfl
  have hm : FBF_on_mor dZ (pasteCP hpb D.Pbk) eq1 = FBF_on_mor dZ (pasteCP hpb D.Pbk) eq2 :=
    FBF_on_mor_congr dZ _ S.hW.w eq1 eq2
  rw [S.hε, Category.assoc, ← S.hPqε, ← reassoc_of% L, hm, R, Category.assoc, ← S.hτε]
  exact D.Pbk.condition_assoc w

end Setup

section Construct

variable [HasPullbacks C] {X Y : C} (u : Y ⟶ X) [IsExpArr u]

/-- The chosen universal `Data` for `X`. -/
noncomputable abbrev sX : Data u X := IsExpArr.isExpArrowData X

/-- The base `P X` of the slice.

[Paper, §3.1, Prop. `prop:p2-construction`]: `P X`. -/
noncomputable abbrev sZ : C := (sX u).P

/-- The counit `Y ×_X P X ⟶ X`.

[Paper, §3.1, Prop. `prop:p2-construction`]: the counit `ε_X : X̲ ⟶ X`. -/
noncomputable abbrev sE : (sX u).Pbk.pullback ⟶ X := (sX u).epsilon

/-- The projection `Y ×_X P X ⟶ P X`. -/
noncomputable abbrev sW : (sX u).Pbk.pullback ⟶ sZ u := (sX u).Pbk.p₂

/-- The domain of the pulled back arrow. -/
noncomputable abbrev sY' : C := pullback u (sE u)

/-- The pullback of `u` along the counit.

[Paper, §3.1, Prop. `prop:p2-construction`]: the morphism `p̲ : Y̲ ⟶ X̲`. -/
noncomputable abbrev su' : sY' u ⟶ (sX u).Pbk.pullback := pullback.snd u (sE u)

lemma shpb : IsPullback (pullback.fst u (sE u)) (su' u) u (sE u) :=
  IsPullback.of_hasPullback u (sE u)

/-- The pulled back arrow, as an arrow of `Over (P X)`.

[Paper, §3.1, Prop. `prop:p2-exponentiable`]: `p̲` as a morphism of `C / P X`. -/
noncomputable def sArr : Over.mk (su' u ≫ sW u) ⟶ Over.mk (sW u) :=
  Over.homMk (su' u)

variable (c : Over (sZ u))

/-- The chosen `Data` for `c.left`. -/
noncomputable abbrev sdc : Data u c.left := IsExpArr.isExpArrowData c.left

/-- The chosen `Data` for `P X`. -/
noncomputable abbrev sdZ : Data u (sZ u) := IsExpArr.isExpArrowData (sZ u)

noncomputable instance : Universal (sdZ u) := IsExpArr.isExpArrow _

noncomputable def sPq : (sdc u c).P ⟶ (sdZ u).P := canonical_mor' c.hom (sdZ u) (sdc u c)

lemma shPq : (sdc u c).pi = sPq u c ≫ (sdZ u).pi := Universal.isSlice ((sdc u c).epsilon ≫ c.hom)

lemma shPqε : FBF_on_mor (sdZ u) (sdc u c).Pbk (shPq u c) ≫ (sdZ u).epsilon =
    (sdc u c).epsilon ≫ c.hom :=
  (FBF_on_mor_epsilon' c.hom (sdZ u) (sdc u c)).symm

noncomputable def sτ : (sX u).Pbk.pullback ⟶ (sdZ u).P :=
  Universal.mor (data := sdZ u) (Kuf := chosenOfIsPullback (shpb u)) (su' u ≫ sW u)

lemma shτ : sE u = sτ u ≫ (sdZ u).pi :=
  Universal.isSlice (data := sdZ u) (Kuf := chosenOfIsPullback (shpb u)) (su' u ≫ sW u)

lemma shτε : su' u ≫ sW u = FBF_on_mor (sdZ u) (chosenOfIsPullback (shpb u)) (shτ u) ≫
    (sdZ u).epsilon :=
  Universal.comm (data := sdZ u) (Kuf := chosenOfIsPullback (shpb u)) (su' u ≫ sW u)

noncomputable def sP : C := pullback (sPq u c) (sτ u)

noncomputable abbrev sπ : sP u c ⟶ (sX u).Pbk.pullback := pullback.snd _ _

noncomputable abbrev sω : sP u c ⟶ (sdc u c).P := pullback.fst _ _

lemma shω : sω u c ≫ (sdc u c).pi = sπ u c ≫ sE u := by
  rw [shPq u c, ← Category.assoc,
    show sω u c ≫ sPq u c = sπ u c ≫ sτ u from pullback.condition, Category.assoc, ← shτ u]

noncomputable def sK : ChosenPullback (su' u) (sπ u c) :=
  chosenOfIsPullback (IsPullback.of_hasPullback (su' u) (sπ u c))

noncomputable def sD : Data (su' u) c.left where
  P := sP u c
  pi := sπ u c
  Pbk := sK u c
  epsilon := liftPbk' (shpb u) (sdc u c) (sK u c) (sω u c) (shω u c) ≫ (sdc u c).epsilon

noncomputable def sSetup : Setup (shpb u) (sdc u c) (sdZ u) c.hom (sW u) (sD u c) where
  Pq := sPq u c
  τ := sτ u
  ω := sω u c
  hPq := shPq u c
  hPqε := shPqε u c
  hτ := shτ u
  hτε := shτε u
  hω := shω u c
  hW := IsPullback.of_hasPullback _ _
  hε := rfl

/-- The universal `Data` in `Over (P X)` for the pulled back arrow.

[Paper, App. A.1, Prop. `prop:p2-description-polynomial`]. -/
noncomputable def sOverData : Data (sArr u) c :=
  overData (sArr u) (sD u c) (sSetup u c).eps_over

@[reducible]
noncomputable def sOverUniv : Universal (sOverData u c) :=
  universal_of_sliceUniv (sArr u) (sOverData u c)
    (sliceUniv_of_isPullback (shpb u) (sdc u c) (sdZ u) c.hom (sW u) (sPq u c) (shPq u c)
      (shPqε u c) (sτ u) (shτ u) (shτε u) _ (sω u c) (shω u c)
      (IsPullback.of_hasPullback _ _) rfl)

/-- [Paper, §3.1, Prop. `prop:p2-exponentiable`]: `p̲` is exponentiable in `C / P X`. -/
noncomputable instance sIsExpArr : IsExpArr (sArr u) where
  isExpArrowData := sOverData u
  isExpArrow := sOverUniv u

end Construct

end SliceExp
