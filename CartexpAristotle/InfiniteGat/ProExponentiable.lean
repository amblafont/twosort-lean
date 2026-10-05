/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InfiniteGat.ProExtension
import CartexpAristotle.InfiniteGat.ExpData

/-!
# Exponentiability in the pro-completion

Let `C` be a small category with finite limits and `p : Y ⟶ X` an exponentiable arrow of `C`.

* `proYoneda C` preserves pushforwards along `p` (`proYoneda_functorPreserves`);
* `(proYoneda C).map p` is exponentiable in `Pro C` (`proYoneda_isExpArr`);
* if `F : C ⥤ D` preserves finite limits and pushforwards along `p`, and `D` is complete, then
  the extension `proExtend F` preserves pushforwards along `(proYoneda C).map p`
  (`proExtend_functorPreserves`).

## References

* [Paper, App., Cor. `cor:exponentiable-free-filtered`] and
  [Paper, App., Prop. `prop:lift-lexp-functor`] (preservation of pushforwards).
-/

open CategoryTheory Limits Opposite Functor SliceExp

universe w u

namespace InfiniteGat

variable {C : Type w} [SmallCategory C] [HasFiniteLimits C]

/-- A chosen pullback in `C`, from Mathlib's pullbacks. -/
noncomputable def chosenPb {X Y Z : C} (p : Y ⟶ X) (g : Z ⟶ X) : ChosenPullback p g where
  pullback := pullback p g
  p₁ := pullback.fst p g
  p₂ := pullback.snd p g
  condition := pullback.condition
  isLimit := pullbackIsPullback p g

section Representable

variable {X Y : C} (p : Y ⟶ X) {c : C} (U : Data p c) [Universal U]
  {d' : Pro C} (f : d' ⟶ (proYoneda C).obj X)

/-- The cofiltered category presenting `d'` over `proYoneda C X`. -/
abbrev Stage := Over (StructuredArrow.mk f : StructuredArrow d' (proYoneda C))

variable {f}

/-- The object of `C` at a stage. -/
abbrev Stage.e (s : Stage f) : C := s.left.right

/-- The projection of `d'` to a stage. -/
abbrev Stage.lam (s : Stage f) : d' ⟶ (proYoneda C).obj s.e := s.left.hom

/-- The map to `X` at a stage. -/
abbrev Stage.g (s : Stage f) : s.e ⟶ X := s.hom.right

omit [HasFiniteLimits C] in
lemma Stage.lam_g (s : Stage f) : s.lam ≫ (proYoneda C).map s.g = f :=
  StructuredArrow.w s.hom

omit [HasFiniteLimits C] in
lemma Stage.map_g {s s' : Stage f} (t : s ⟶ s') : t.left.right ≫ s'.g = s.g :=
  congrArg CommaMorphism.right (Over.w t)

omit [HasFiniteLimits C] in
lemma Stage.lam_map {s s' : Stage f} (t : s ⟶ s') :
    s.lam ≫ (proYoneda C).map t.left.right = s'.lam :=
  StructuredArrow.w t.left

variable (f)

/-- The diagram of stages. -/
noncomputable abbrev stageDiagram : Stage f ⥤ Pro C :=
  Over.forget _ ⋙ StructuredArrow.proj d' (proYoneda C) ⋙ proYoneda C

/-- The limit cone of stages. -/
noncomputable abbrev stageCone : Cone (stageDiagram f) :=
  ((Functor.RightExtension.mk (𝟭 (Pro C)) (proYoneda C).rightUnitor.hom).coneAt d').whisker
    (Over.forget _)

omit [HasFiniteLimits C] in
lemma stageCone_π (s : Stage f) : (stageCone f).π.app s = s.lam := by simp

/-- `d'` is the limit of its stages. -/
noncomputable def stageCone_isLimit : IsLimit (stageCone f) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget _) _).symm (proYonedaCodenseAt d')

variable {f} (K : ChosenPullback ((proYoneda C).map p) f)

/-- The pullbacks at the stages. -/
noncomputable abbrev stageQ (s : Stage f) :
    ChosenPullback ((proYoneda C).map p) ((proYoneda C).map s.g) :=
  functPullback (proYoneda C) (chosenPb p s.g)

omit [HasFiniteLimits C] in
lemma stage_hv {s s' : Stage f} (t : s ⟶ s') :
    (stageDiagram f).map t ≫ (proYoneda C).map s'.g = (proYoneda C).map s.g := by
  dsimp
  rw [← Functor.map_comp, Stage.map_g]

omit [HasFiniteLimits C] in
lemma stage_hf (s : Stage f) : (stageCone f).π.app s ≫ (proYoneda C).map s.g = f := by
  rw [stageCone_π]; exact s.lam_g

/-- The pullback `K` is the limit of the pullbacks at the stages. -/
noncomputable def stagePbIsLimit :=
  pbCone_isLimit (stageDiagram f) (fun s => (proYoneda C).map s.g) stage_hv (stageQ p)
    (stageCone f) (stageCone_isLimit f) f stage_hf K

/-- The leg of `K` to a stage. -/
noncomputable abbrev stageLeg (s : Stage f) : K.pullback ⟶ (stageQ p s).pullback :=
  (pbCone (stageDiagram f) (fun s => (proYoneda C).map s.g) stage_hv (stageQ p)
    (stageCone f) f stage_hf K).π.app s

variable {p}

omit [Universal U] in
/-- The transpose of a morphism given at a stage. -/
lemma fbf_stage (s : Stage f) (a : s.e ⟶ U.P) (ha : s.g = a ≫ U.pi)
    (hm : f = (s.lam ≫ (proYoneda C).map a) ≫ (proYoneda C).map U.pi) :
    FBF_on_mor (functor_on (proYoneda C) U) K hm =
      stageLeg p K s ≫ (proYoneda C).map (FBF_on_mor U (chosenPb p s.g) ha) := by
  have e₂ : (proYoneda C).map s.g = (proYoneda C).map a ≫ (proYoneda C).map U.pi := by
    rw [ha, Functor.map_comp]
  rw [← functor_on_FBF' (proYoneda C) U (chosenPb p s.g) ha e₂]
  refine FBF_on_mor_map (functor_on (proYoneda C) U) K (stageQ p s) s.lam (stageLeg p K s)
    ?_ ?_ (m₁ := s.lam ≫ (proYoneda C).map a) (m₂ := (proYoneda C).map a) hm e₂ rfl
  · exact IsPullback.lift_fst (stageQ p s).isPullback _ _ _
  · refine (IsPullback.lift_snd (stageQ p s).isPullback _ _ _).trans ?_
    rw [stageCone_π]

omit [Universal U] in
lemma stage_exists (m : d' ⟶ (proYoneda C).obj U.P) (hm : f = m ≫ (proYoneda C).map U.pi) :
    ∃ (s : Stage f) (a : s.e ⟶ U.P), m = s.lam ≫ (proYoneda C).map a ∧ s.g = a ≫ U.pi := by
  obtain ⟨s₁, m₁, h₁⟩ := proYoneda_cc_exists (stageCone_isLimit f) m
  obtain ⟨a₁, rfl⟩ := (proYoneda C).map_surjective m₁
  rw [stageCone_π] at h₁
  have e : (stageCone f).π.app s₁ ≫ (proYoneda C).map (a₁ ≫ U.pi) =
      (stageCone f).π.app s₁ ≫ (proYoneda C).map s₁.g := by
    rw [stageCone_π, Functor.map_comp, ← Category.assoc, ← h₁, ← hm, s₁.lam_g]
  obtain ⟨s₂, t, ht⟩ := proYoneda_cc_eq (stageCone_isLimit f) _ _ e
  refine ⟨s₂, t.left.right ≫ a₁, ?_, ?_⟩
  · rw [h₁, Functor.map_comp, ← Category.assoc, Stage.lam_map]
  · apply (proYoneda C).map_injective
    dsimp at ht
    rw [← Functor.map_comp, ← Functor.map_comp] at ht
    rw [Category.assoc, ht, Stage.map_g]

omit [HasFiniteLimits C] [Universal U] in
lemma stage_restrict {s s' : Stage f} (t : s' ⟶ s) {m : d' ⟶ (proYoneda C).obj U.P}
    {a : s.e ⟶ U.P} (h : m = s.lam ≫ (proYoneda C).map a ∧ s.g = a ≫ U.pi) :
    m = s'.lam ≫ (proYoneda C).map (t.left.right ≫ a) ∧ s'.g = (t.left.right ≫ a) ≫ U.pi := by
  refine ⟨?_, ?_⟩
  · rw [h.1, Functor.map_comp, ← Category.assoc, Stage.lam_map]
  · rw [Category.assoc, ← h.2, Stage.map_g]

variable (p) in
/-- **`proYoneda C` preserves pushforwards along `p`**: the image of universal data is universal.

[Paper, App., Cor. `cor:exponentiable-free-filtered`]. -/
noncomputable def proYoneda_universal : Universal (functor_on (proYoneda C) U) := by
  refine Universal.ofBijective _ (fun {d' f} K g => ?_) (fun {d' m m' f} K hm hm' H => ?_)
  · obtain ⟨s, g', hg⟩ := proYoneda_cc_exists (stagePbIsLimit p K) g
    obtain ⟨g'', rfl⟩ := (proYoneda C).map_surjective g'
    let a := Universal.mor (data := U) (Kuf := chosenPb p s.g) g''
    have ha : s.g = a ≫ U.pi := Universal.isSlice _
    have hm : f = (s.lam ≫ (proYoneda C).map a) ≫ (proYoneda C).map U.pi := by
      rw [Category.assoc, ← Functor.map_comp, ← ha, s.lam_g]
    refine ⟨_, hm, ?_⟩
    rw [fbf_stage U K s a ha hm, hg, Category.assoc]
    change _ ≫ (proYoneda C).map g'' = _ ≫ _ ≫ (proYoneda C).map U.epsilon
    rw [← Functor.map_comp, ← Universal.comm]
  · obtain ⟨s₁, a₁, h₁⟩ := stage_exists U m hm
    obtain ⟨s₂, a₂, h₂⟩ := stage_exists U m' hm'
    let s₃ := IsCofiltered.min s₁ s₂
    obtain ⟨a, h₁'⟩ : ∃ a : s₃.e ⟶ U.P, m = s₃.lam ≫ (proYoneda C).map a ∧ s₃.g = a ≫ U.pi :=
      ⟨_, stage_restrict U (IsCofiltered.minToLeft s₁ s₂) h₁⟩
    obtain ⟨b, h₂'⟩ : ∃ b : s₃.e ⟶ U.P, m' = s₃.lam ≫ (proYoneda C).map b ∧ s₃.g = b ≫ U.pi :=
      ⟨_, stage_restrict U (IsCofiltered.minToRight s₁ s₂) h₂⟩
    have hma : f = (s₃.lam ≫ (proYoneda C).map a) ≫ (proYoneda C).map U.pi := h₁'.1 ▸ hm
    have hmb : f = (s₃.lam ≫ (proYoneda C).map b) ≫ (proYoneda C).map U.pi := h₂'.1 ▸ hm'
    have H' : stageLeg p K s₃ ≫ (proYoneda C).map (FBF_on_mor U (chosenPb p s₃.g) h₁'.2 ≫
        U.epsilon) = stageLeg p K s₃ ≫ (proYoneda C).map (FBF_on_mor U (chosenPb p s₃.g) h₂'.2 ≫
        U.epsilon) := by
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
        ← fbf_stage U K s₃ a h₁'.2 hma, ← fbf_stage U K s₃ b h₂'.2 hmb]
      have e₁ := FBF_on_mor_congr (functor_on (proYoneda C) U) K h₁'.1 hm hma
      have e₂ := FBF_on_mor_congr (functor_on (proYoneda C) U) K h₂'.1 hm' hmb
      rw [← e₁, ← e₂]
      exact H
    obtain ⟨s₄, t, ht⟩ := proYoneda_cc_eq (stagePbIsLimit p K) _ _ H'
    let ρ : (chosenPb p s₄.g).pullback ⟶ (chosenPb p s₃.g).pullback :=
      (chosenPb p s₃.g).isPullback.lift (chosenPb p s₄.g).p₁
        ((chosenPb p s₄.g).p₂ ≫ t.left.right) (by
          rw [(chosenPb p s₄.g).condition, Category.assoc, Stage.map_g])
    have hρ : (pbDiagram (stageDiagram f) (fun s => (proYoneda C).map s.g) stage_hv
        (stageQ p)).map t = (proYoneda C).map ρ := by
      apply (stageQ p s₃).hom_ext
      · dsimp
        simp only [pbTrans_p₁]
        change (proYoneda C).map _ = (proYoneda C).map ρ ≫ (proYoneda C).map _
        rw [← Functor.map_comp]
        exact congrArg _ (IsPullback.lift_fst _ _ _ _).symm
      · dsimp
        simp only [pbTrans_p₂]
        change (proYoneda C).map _ ≫ (proYoneda C).map _ =
          (proYoneda C).map ρ ≫ (proYoneda C).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg _ (IsPullback.lift_snd _ _ _ _).symm
    rw [hρ, ← Functor.map_comp, ← Functor.map_comp] at ht
    replace ht := (proYoneda C).map_injective ht
    have ha₄ : s₄.g = (t.left.right ≫ a) ≫ U.pi := by
      rw [Category.assoc, ← h₁'.2, Stage.map_g]
    have hb₄ : s₄.g = (t.left.right ≫ b) ≫ U.pi := by
      rw [Category.assoc, ← h₂'.2, Stage.map_g]
    have eρa := FBF_on_mor_map U (chosenPb p s₄.g) (chosenPb p s₃.g) t.left.right ρ
      (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) ha₄ h₁'.2 rfl
    have eρb := FBF_on_mor_map U (chosenPb p s₄.g) (chosenPb p s₃.g) t.left.right ρ
      (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) hb₄ h₂'.2 rfl
    have key : t.left.right ≫ a = t.left.right ≫ b := by
      refine Universal.uniq (chosenPb p s₄.g) ha₄ hb₄ ?_
      rw [eρa, eρb, Category.assoc, Category.assoc]
      exact ht
    rw [h₁'.1, h₂'.1, ← Stage.lam_map t, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, key]

end Representable

section Exponentiable

variable {X Y : C} (p : Y ⟶ X) [IsExpArr p]

/-- `proYoneda C` preserves pushforwards along `p`. -/
noncomputable instance proYoneda_functorPreserves : FunctorPreserves p (proYoneda C) where
  functor_preserves d _ := proYoneda_universal p d

variable (A : Pro C)

/-- The chosen universal data for `p` at `c`. -/
noncomputable abbrev expD (c : C) : Data p c := IsExpArr.isExpArrowData c

/-- The transition maps of the canonical diagram of `A`. -/
noncomputable abbrev proγ {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j') :
    (proYoneda C).obj j.right ⟶ (proYoneda C).obj j'.right :=
  (proYoneda C).map t.right

/-- The universal data at the stages of `A`. -/
noncomputable abbrev proD (j : StructuredArrow A (proYoneda C)) :
    Data ((proYoneda C).map p) ((proYoneda C).obj j.right) :=
  functor_on (proYoneda C) (expD p j.right)

/-- The transition maps between the universal data at the stages of `A`. -/
noncomputable abbrev proτ {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j') :
    (proD p A j).P ⟶ (proD p A j').P :=
  (proYoneda C).map ((pushforward p).map t.right)

/-- The diagram whose limit is the pushforward of `A` along `(proYoneda C).map p`. -/
noncomputable abbrev proPDiagram : StructuredArrow A (proYoneda C) ⥤ Pro C :=
  StructuredArrow.proj A (proYoneda C) ⋙ pushforward p ⋙ proYoneda C

/-- The pushforward of `A` along `(proYoneda C).map p`. -/
noncomputable def proExpP : Pro C := limit (proPDiagram p A)

/-- The projections of `proExpP p A`. -/
noncomputable def proExpH (j : StructuredArrow A (proYoneda C)) :
    proExpP p A ⟶ (proD p A j).P :=
  limit.π (proPDiagram p A) j

lemma proExpH_τ {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j') :
    proExpH p A j ≫ proτ p A t = proExpH p A j' :=
  limit.w (proPDiagram p A) t

lemma proτpi {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j') :
    (proD p A j).pi = proτ p A t ≫ (proD p A j').pi := by
  change (proYoneda C).map _ = _ ≫ (proYoneda C).map _
  rw [← Functor.map_comp, ← pushforward_map_pi]

lemma proτε {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j') :
    FBF_on_mor (proD p A j') (proD p A j).Pbk (proτpi p A t) ≫ (proD p A j').epsilon =
      (proD p A j).epsilon ≫ proγ A t := by
  change FBF_on_mor (functor_on (proYoneda C) (expD p j'.right))
    (functPullback (proYoneda C) (expD p j.right).Pbk) _ ≫ (proYoneda C).map _ =
      (proYoneda C).map _ ≫ (proYoneda C).map _
  rw [functor_on_FBF' (proYoneda C) _ _ (pushforward_map_pi p t.right), ← Functor.map_comp,
    ← Functor.map_comp, pushforward_map_epsilon]

/-- The structure map of `proExpP p A` to `proYoneda C X`. -/
noncomputable def proExpPi : proExpP p A ⟶ (proYoneda C).obj X :=
  proExpH p A IsCofiltered.nonempty.some ≫ (proD p A IsCofiltered.nonempty.some).pi

lemma proExpH_pi (j : StructuredArrow A (proYoneda C)) :
    proExpPi p A = proExpH p A j ≫ (proD p A j).pi := by
  have h : ∀ k k' (t : k ⟶ k'), proExpH p A k ≫ (proD p A k).pi =
      proExpH p A k' ≫ (proD p A k').pi := fun k k' t => by
    rw [proτpi p A t, ← Category.assoc, proExpH_τ]
  rw [proExpPi, ← h _ _ (IsCofiltered.minToLeft _ j), h _ _ (IsCofiltered.minToRight _ j)]

/-- The chosen pullback for the pushforward of `A`. -/
noncomputable def proExpPbk : ChosenPullback ((proYoneda C).map p) (proExpPi p A) where
  pullback := pullback ((proYoneda C).map p) (proExpPi p A)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := pullbackIsPullback _ _

/-- The cone defining the counit of the pushforward of `A`. -/
noncomputable def proExpEpsCone :
    Cone (StructuredArrow.proj A (proYoneda C) ⋙ proYoneda C) where
  pt := (proExpPbk p A).pullback
  π :=
    { app j := FBF_on_mor (proD p A j) (proExpPbk p A) (proExpH_pi p A j) ≫ (proD p A j).epsilon
      naturality j j' t := by
        dsimp
        rw [Category.id_comp]
        exact (fbf_family_compat (proγ A) (proD p A) (proτ p A) (proτpi p A) (proτε p A)
          (proExpPbk p A) (proExpH p A) (proExpH_pi p A) (fun t => proExpH_τ p A t) t).symm }

/-- The counit of the pushforward of `A`. -/
noncomputable def proExpEps : (proExpPbk p A).pullback ⟶ A :=
  (proYonedaCodenseAt A).lift (proExpEpsCone p A)

lemma proExpEps_fac (j : StructuredArrow A (proYoneda C)) :
    FBF_on_mor (proD p A j) (proExpPbk p A) (proExpH_pi p A j) ≫ (proD p A j).epsilon =
      proExpEps p A ≫ j.hom := by
  have := (proYonedaCodenseAt A).fac (proExpEpsCone p A) j
  dsimp at this
  rw [Category.comp_id] at this
  exact this.symm

/-- The pushforward data of `A` along `(proYoneda C).map p`. -/
noncomputable def proExpData : Data ((proYoneda C).map p) A where
  P := proExpP p A
  pi := proExpPi p A
  Pbk := proExpPbk p A
  epsilon := proExpEps p A

omit [HasFiniteLimits C] in
lemma proA_ext {T : Pro C} (f f' : T ⟶ A)
    (h : ∀ j : StructuredArrow A (proYoneda C), f ≫ j.hom = f' ≫ j.hom) : f = f' :=
  (proYonedaCodenseAt A).hom_ext (fun j => by simpa using h j)

lemma proExpP_lift {T : Pro C} (m : ∀ j, T ⟶ (proD p A j).P)
    (hm : ∀ {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j'), m j ≫ proτ p A t = m j') :
    ∃ m' : T ⟶ proExpP p A, ∀ j, m' ≫ proExpH p A j = m j :=
  ⟨limit.lift _ ⟨_,
    { app := m
      naturality := fun _ _ t => by
        dsimp
        rw [Category.id_comp]
        exact (hm t).symm }⟩, fun j => limit.lift_π _ j⟩

/-- The pushforward data of `A` is universal. -/
noncomputable def proExpUniversal : Universal (proExpData p A) :=
  haveI : Nonempty (StructuredArrow A (proYoneda C)) := IsCofiltered.nonempty
  haveI : ∀ j, Universal (proD p A j) := fun _ => proYoneda_universal p _
  Universal.ofLimit (proγ A) (fun j => j.hom) (proD p A) (proτ p A) (proτpi p A) (proτε p A)
    (proExpData p A) (proExpH p A) (proExpH_pi p A)
    (fun t => StructuredArrow.w t) (proA_ext A) (proExpEps_fac p A)
    (proExpP_lift p A) (fun _ _ h => limit.hom_ext h)

/-- **`(proYoneda C).map p` is exponentiable in `Pro C`.**

[Paper, App., Cor. `cor:exponentiable-free-filtered`]. -/
noncomputable instance proYoneda_isExpArr : IsExpArr ((proYoneda C).map p) where
  isExpArrowData := proExpData p
  isExpArrow := proExpUniversal p

end Exponentiable

end InfiniteGat
