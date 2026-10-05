/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.LexpTheta

/-!
# General facts about universal exponential data

Auxiliary results for the proof of [Paper, App., Thm. `thm:infinite-GATs`]:

* `Universal.ofBijective`: universality of partial exponential data `d : Data u c` can be
  checked by showing that `m ↦ FBF_on_mor d K _ ≫ d.epsilon` is bijective;
* `Universal.ofLimit`: a limit of universal data is universal (the pushforward `P_u` is a right
  adjoint, hence preserves limits);
* `chosenPullbackOfLimit_isLimit`: pulling back a cofiltered limit along a fixed arrow gives the
  limit of the pullbacks;
* `pushforward`: the functor `c ↦ P_u(c)` attached to an exponentiable arrow `u`.
-/

open CategoryTheory Limits SliceExp

namespace InfiniteGat

variable {E : Type*} [Category E] {X Y : E} {u : Y ⟶ X}

section Bijective

/-- Universality of data from bijectivity of the transposition map. -/
noncomputable def Universal.ofBijective {c : E} (d : Data u c)
    (hsurj : ∀ {d' : E} {f : d' ⟶ X} (K : ChosenPullback u f) (g : K.pullback ⟶ c),
      ∃ (m : d' ⟶ d.P) (hm : f = m ≫ d.pi), g = FBF_on_mor d K hm ≫ d.epsilon)
    (hinj : ∀ {d' : E} {m m' : d' ⟶ d.P} {f : d' ⟶ X} (K : ChosenPullback u f)
      (hm : f = m ≫ d.pi) (hm' : f = m' ≫ d.pi),
      FBF_on_mor d K hm ≫ d.epsilon = FBF_on_mor d K hm' ≫ d.epsilon → m = m') :
    Universal d where
  mor {_ _ K} g := (hsurj K g).choose
  isSlice {_ _ K} g := (hsurj K g).choose_spec.choose
  comm {_ _ K} g := (hsurj K g).choose_spec.choose_spec
  uniq K hm hm' h := hinj K hm hm' h

end Bijective

section Limit

variable {J : Type*} [Category J] {cj : J → E} (γ : ∀ {j j' : J}, (j ⟶ j') → (cj j ⟶ cj j'))
  {A : E} (a : ∀ j, A ⟶ cj j)
  (Dj : ∀ j, Data u (cj j)) (τ : ∀ {j j' : J} (_ : j ⟶ j'), (Dj j).P ⟶ (Dj j').P)
  (hτpi : ∀ {j j' : J} (t : j ⟶ j'), (Dj j).pi = τ t ≫ (Dj j').pi)
  (hτε : ∀ {j j' : J} (t : j ⟶ j'),
    FBF_on_mor (Dj j') (Dj j).Pbk (hτpi t) ≫ (Dj j').epsilon = (Dj j).epsilon ≫ γ t)

include hτε in
/-- Compatibility of the transposes of a family of morphisms to the `cj j`. -/
lemma mor_comp_τ [∀ j, Universal (Dj j)] {d' : E} {f : d' ⟶ X} (K : ChosenPullback u f)
    (g : ∀ j, K.pullback ⟶ cj j) (hg : ∀ {j j' : J} (t : j ⟶ j'), g j ≫ γ t = g j')
    {j j' : J} (t : j ⟶ j') :
    Universal.mor (data := Dj j) (g j) ≫ τ t = Universal.mor (data := Dj j') (g j') := by
  have h₁ : f = (Universal.mor (data := Dj j) (g j) ≫ τ t) ≫ (Dj j').pi := by
    rw [Category.assoc, ← hτpi, ← Universal.isSlice]
  refine mor_unique (d1 := Dj j') (g j') _ h₁ ?_
  have e := FBF_on_mor_map (Dj j') K (Dj j).Pbk (Universal.mor (data := Dj j) (g j))
    (FBF_on_mor (Dj j) K (Universal.isSlice (data := Dj j) (g j))) (by simp) (by simp) h₁
    (hτpi t) rfl
  change g j' = FBF_on_mor (Dj j') K h₁ ≫ (Dj j').epsilon
  rw [e, Category.assoc, hτε, ← Category.assoc, ← Universal.comm, hg]

include hτε in
/-- The family `FBF_on_mor (Dj j) Pb _ ≫ (Dj j).epsilon` is compatible. -/
lemma fbf_family_compat {P : E} {π : P ⟶ X} (Pb : ChosenPullback u π) (h : ∀ j, P ⟶ (Dj j).P)
    (hhpi : ∀ j, π = h j ≫ (Dj j).pi) (hhτ : ∀ {j j' : J} (t : j ⟶ j'), h j ≫ τ t = h j')
    {j j' : J} (t : j ⟶ j') :
    (FBF_on_mor (Dj j) Pb (hhpi j) ≫ (Dj j).epsilon) ≫ γ t =
      FBF_on_mor (Dj j') Pb (hhpi j') ≫ (Dj j').epsilon := by
  have e := FBF_on_mor_map (Dj j') Pb (Dj j).Pbk (h j)
    (FBF_on_mor (Dj j) Pb (hhpi j)) (by simp) (by simp) (hhpi j') (hτpi t) (hhτ t)
  rw [e, Category.assoc, Category.assoc, hτε]

variable (d : Data u A) (h : ∀ j, d.P ⟶ (Dj j).P) (hhpi : ∀ j, d.pi = h j ≫ (Dj j).pi)

include hτε in
/-- **A limit of universal data is universal.** -/
noncomputable def Universal.ofLimit [Nonempty J] [∀ j, Universal (Dj j)]
    (ha : ∀ {j j' : J} (t : j ⟶ j'), a j ≫ γ t = a j')
    (hAext : ∀ {T : E} (f f' : T ⟶ A), (∀ j, f ≫ a j = f' ≫ a j) → f = f')
    (hhε : ∀ j, FBF_on_mor (Dj j) d.Pbk (hhpi j) ≫ (Dj j).epsilon = d.epsilon ≫ a j)
    (hPlift : ∀ {T : E} (m : ∀ j, T ⟶ (Dj j).P),
      (∀ {j j' : J} (t : j ⟶ j'), m j ≫ τ t = m j') → ∃ m' : T ⟶ d.P, ∀ j, m' ≫ h j = m j)
    (hPext : ∀ {T : E} (m m' : T ⟶ d.P), (∀ j, m ≫ h j = m' ≫ h j) → m = m') :
    Universal d := by
  refine Universal.ofBijective d (fun {d' f} K g => ?_) (fun {d' m m' f} K hm hm' H => ?_)
  · have hg : ∀ {j j' : J} (t : j ⟶ j'), (g ≫ a j) ≫ γ t = g ≫ a j' := fun t => by
      rw [Category.assoc, ha]
    obtain ⟨m, hm⟩ := hPlift (fun j => Universal.mor (data := Dj j) (g ≫ a j))
      (fun t => mor_comp_τ γ Dj τ hτpi hτε K (fun j => g ≫ a j) hg t)
    have hmpi : f = m ≫ d.pi := by
      obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
      rw [hhpi j₀, ← Category.assoc, hm]
      exact Universal.isSlice _
    refine ⟨m, hmpi, hAext _ _ (fun j => ?_)⟩
    have e := FBF_on_mor_map (Dj j) K d.Pbk m (FBF_on_mor d K hmpi) (by simp) (by simp)
      (Universal.isSlice (data := Dj j) (g ≫ a j)) (hhpi j) (hm j)
    rw [Category.assoc, ← hhε, ← Category.assoc, ← e]
    exact Universal.comm _
  · refine hPext _ _ (fun j => ?_)
    have h₁ : f = (m ≫ h j) ≫ (Dj j).pi := by rw [Category.assoc, ← hhpi]; exact hm
    have h₂ : f = (m' ≫ h j) ≫ (Dj j).pi := by rw [Category.assoc, ← hhpi]; exact hm'
    refine Universal.uniq K h₁ h₂ ?_
    have e₁ := FBF_on_mor_map (Dj j) K d.Pbk m (FBF_on_mor d K hm) (by simp) (by simp) h₁
      (hhpi j) rfl
    have e₂ := FBF_on_mor_map (Dj j) K d.Pbk m' (FBF_on_mor d K hm') (by simp) (by simp) h₂
      (hhpi j) rfl
    rw [e₁, e₂, Category.assoc, Category.assoc, hhε, ← Category.assoc, H, Category.assoc]

end Limit

section Functor

variable {E' : Type*} [Category E'] (F : E ⥤ E') [PreservesLimitsOfShape WalkingCospan F]

lemma functor_on_FBF' {c : E} (D : Data u c) {d : E} {f : d ⟶ D.P} {h : d ⟶ X}
    (K : ChosenPullback u h) (eq : h = f ≫ D.pi) (eq' : F.map h = F.map f ≫ F.map D.pi) :
    FBF_on_mor (functor_on F D) (functPullback F K) eq' = F.map (FBF_on_mor D K eq) :=
  (functor_on_FBF F D K eq).symm

end Functor

section PullbackLimit

variable {J : Type*} [Category J] (V : J ⥤ E) (v : ∀ j, V.obj j ⟶ X)
  (hv : ∀ {j j' : J} (t : j ⟶ j'), V.map t ≫ v j' = v j)
  (Q : ∀ j, ChosenPullback u (v j))

/-- The transition maps between the pullbacks `Q j`. -/
noncomputable def pbTrans {j j' : J} (t : j ⟶ j') : (Q j).pullback ⟶ (Q j').pullback :=
  (Q j').isPullback.lift (Q j).p₁ ((Q j).p₂ ≫ V.map t) (by
    rw [(Q j).condition, Category.assoc, hv])

@[reassoc (attr := simp)]
lemma pbTrans_p₁ {j j' : J} (t : j ⟶ j') : pbTrans V v hv Q t ≫ (Q j').p₁ = (Q j).p₁ :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma pbTrans_p₂ {j j' : J} (t : j ⟶ j') :
    pbTrans V v hv Q t ≫ (Q j').p₂ = (Q j).p₂ ≫ V.map t :=
  IsPullback.lift_snd _ _ _ _

/-- The diagram of pullbacks. -/
@[simps]
noncomputable def pbDiagram : J ⥤ E where
  obj j := (Q j).pullback
  map t := pbTrans V v hv Q t
  map_id j := (Q j).hom_ext (by simp) (by simp)
  map_comp t t' := (Q _).hom_ext (by simp) (by simp)

variable (cV : Cone V) (hcV : IsLimit cV) (f : cV.pt ⟶ X) (hf : ∀ j, cV.π.app j ≫ v j = f)
  (K : ChosenPullback u f)

/-- The cone exhibiting a pullback of a limit as a limit of pullbacks. -/
@[simps]
noncomputable def pbCone : Cone (pbDiagram V v hv Q) where
  pt := K.pullback
  π :=
    { app j := (Q j).isPullback.lift K.p₁ (K.p₂ ≫ cV.π.app j) (by
        rw [K.condition, Category.assoc, hf])
      naturality j j' t := (Q j').hom_ext (by simp) (by simp) }

include hcV in
/-- **Pullbacks commute with cofiltered limits.** -/
noncomputable def pbCone_isLimit [IsCofiltered J] : IsLimit (pbCone V v hv Q cV f hf K) := by
  have hp₁ : ∀ (s : Cone (pbDiagram V v hv Q)) (j j' : J),
      s.π.app j ≫ (Q j).p₁ = s.π.app j' ≫ (Q j').p₁ := fun s j j' => by
    have e₁ := s.w (IsCofiltered.minToLeft j j')
    have e₂ := s.w (IsCofiltered.minToRight j j')
    dsimp at e₁ e₂
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, pbTrans_p₁, pbTrans_p₁]
  let j₀ : J := IsCofiltered.nonempty.some
  let lift₂ : ∀ s : Cone (pbDiagram V v hv Q), s.pt ⟶ cV.pt := fun s =>
    hcV.lift ⟨s.pt,
      { app j := s.π.app j ≫ (Q j).p₂
        naturality j j' t := by
          have e := s.w t
          dsimp at e ⊢
          rw [Category.id_comp, ← e, Category.assoc, pbTrans_p₂, Category.assoc] }⟩
  have hlift₂ : ∀ s j, lift₂ s ≫ cV.π.app j = s.π.app j ≫ (Q j).p₂ := fun s j => hcV.fac _ j
  have hcond : ∀ s : Cone (pbDiagram V v hv Q),
      (s.π.app j₀ ≫ (Q j₀).p₁) ≫ u = lift₂ s ≫ f := fun s => by
    rw [← hf j₀, ← Category.assoc, hlift₂, Category.assoc, Category.assoc, (Q j₀).condition]
  refine
    { lift s := K.isPullback.lift (s.π.app j₀ ≫ (Q j₀).p₁) (lift₂ s) (hcond s)
      fac s j := (Q j).hom_ext ?_ ?_
      uniq s m hm := K.hom_ext ?_ ?_ }
  · simp only [pbCone_π_app, Category.assoc, IsPullback.lift_fst]
    exact hp₁ s j₀ j
  · simp only [pbCone_π_app, Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc]
    exact hlift₂ s j
  · rw [IsPullback.lift_fst, ← hm j₀]
    simp
  · rw [IsPullback.lift_snd]
    refine hcV.hom_ext (fun j => ?_)
    rw [hlift₂, ← hm j, Category.assoc, Category.assoc]
    simp

end PullbackLimit

section Pushforward

variable (u) [IsExpArr u]

/-- The pushforward functor `c ↦ P_u(c)` of an exponentiable arrow `u`. -/
@[simps]
noncomputable def pushforward : E ⥤ E where
  obj c := (IsExpArr.isExpArrowData (u := u) c).P
  map {c c'} f := canonical_mor' f (IsExpArr.isExpArrowData c') (IsExpArr.isExpArrowData c)
  map_id _ := canonical_mor'_id _
  map_comp f g := (canonical_mor'_comp f g _ _ _).symm

lemma pushforward_map_pi {c c' : E} (f : c ⟶ c') :
    (IsExpArr.isExpArrowData (u := u) c).pi =
      (pushforward u).map f ≫ (IsExpArr.isExpArrowData (u := u) c').pi :=
  Universal.isSlice _

lemma pushforward_map_epsilon {c c' : E} (f : c ⟶ c') :
    FBF_on_mor (IsExpArr.isExpArrowData (u := u) c') (IsExpArr.isExpArrowData c).Pbk
        (pushforward_map_pi u f) ≫ (IsExpArr.isExpArrowData c').epsilon =
      (IsExpArr.isExpArrowData c).epsilon ≫ f :=
  (Universal.comm _).symm

end Pushforward

end InfiniteGat
