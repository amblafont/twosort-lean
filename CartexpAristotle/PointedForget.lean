/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import CartexpAristotle.PartialExponentiability

/-!
# The forgetful functor from pointed types to types is an exponentiable arrow in `Cat`

The forgetful functor `U : Pointed ⥤ Type` is the discrete opfibration classifying the identity
of `Type`, so the pullback of a functor `f : D ⥤ Type` along `U` is the category of elements of
`f`. The partial exponential `P c` of a category `c` has as objects the types `X` together with
a family `X → c`.
-/

open CategoryTheory Limits

section Transfer

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {u : Y ⟶ X} {c : C}

lemma FBF_on_mor_iso (data : Data u c) {d : C} {h : d ⟶ X} {f : d ⟶ data.P}
    (Kuf K : ChosenPullback u h) (φ : Kuf.pullback ⟶ K.pullback)
    (h₁ : φ ≫ K.p₁ = Kuf.p₁) (h₂ : φ ≫ K.p₂ = Kuf.p₂) (eq : h = f ≫ data.pi) :
    FBF_on_mor data Kuf eq = φ ≫ FBF_on_mor data K eq := by
  apply data.Pbk.hom_ext
  · simp [FBF_on_mor, pullbackMor1, h₁]
  · simp only [FBF_on_mor, pullbackMor1, Category.assoc, IsPullback.lift_snd]
    rw [← Category.assoc, h₂]

/-- Universality only has to be checked against one chosen pullback for each `f`. -/
@[instance_reducible]
noncomputable def universal_of_chosen (data : Data u c)
    (K : ∀ {d : C} (f : d ⟶ X), ChosenPullback u f)
    (mor : ∀ {d : C} {f : d ⟶ X}, ((K f).pullback ⟶ c) → (d ⟶ data.P))
    (isSlice : ∀ {d : C} {f : d ⟶ X} (g : (K f).pullback ⟶ c), f = mor g ≫ data.pi)
    (comm : ∀ {d : C} {f : d ⟶ X} (g : (K f).pullback ⟶ c),
      g = FBF_on_mor data (K f) (isSlice g) ≫ data.epsilon)
    (uniq : ∀ {d : C} {f g : d ⟶ data.P} {h : d ⟶ X}
      (eq_fp : h = f ≫ data.pi) (eq_gp : h = g ≫ data.pi),
      FBF_on_mor data (K h) eq_fp ≫ data.epsilon = FBF_on_mor data (K h) eq_gp ≫ data.epsilon →
      f = g) :
    Universal data where
  mor {d f Kuf} g :=
    mor ((Kuf.isPullback.isoIsPullback _ _ (K f).isPullback).inv ≫ g)
  isSlice {d f Kuf} g := isSlice _
  comm {d f Kuf} g := by
    set φ := Kuf.isPullback.isoIsPullback _ _ (K f).isPullback
    have h := comm (φ.inv ≫ g)
    rw [FBF_on_mor_iso data Kuf (K f) φ.hom (by simp [φ]) (by simp [φ]) (isSlice (φ.inv ≫ g)),
      Category.assoc, ← h]
    simp
  uniq {d f g h} Kufp eq_fp eq_gp H := by
    set φ := Kufp.isPullback.isoIsPullback _ _ (K h).isPullback
    rw [FBF_on_mor_iso data Kufp (K h) φ.hom (by simp [φ]) (by simp [φ]) eq_fp,
      FBF_on_mor_iso data Kufp (K h) φ.hom (by simp [φ]) (by simp [φ]) eq_gp,
      Category.assoc, Category.assoc, cancel_epi] at H
    exact uniq eq_fp eq_gp H

end Transfer

universe w

namespace PointedForget

section Elements

variable {D : Type (w + 1)} [Category.{w} D] (F : D ⥤ Type w)

/-- The functor from the category of elements to pointed types. -/
def elToPt : F.Elements ⥤ Pointed.{w} where
  obj x := ⟨F.obj x.1, x.2⟩
  map {x y} f := ⟨F.map f.1, f.2⟩
  map_id x := by
    apply Pointed.Hom.ext
    funext a
    simp
  map_comp f g := by
    apply Pointed.Hom.ext
    funext a
    simp

variable {F} {S : Type (w + 1)} [Category.{w} S]
  (A : S ⥤ Pointed.{w}) (B : S ⥤ D) (h : A ⋙ forget Pointed.{w} = B ⋙ F)

def elPt (x : S) : F.obj (B.obj x) :=
  cast (Functor.congr_obj h x) (A.obj x).point

lemma transport_point {A' B' : S ⥤ Type w} (h : A' = B') (p : ∀ x, A'.obj x)
    (hp : ∀ {x y : S} (g : x ⟶ y), A'.map g (p x) = p y) {x y : S} (g : x ⟶ y) :
    B'.map g (cast (Functor.congr_obj h x) (p x)) = cast (Functor.congr_obj h y) (p y) := by
  subst h; exact hp g

lemma elPt_map {x y : S} (g : x ⟶ y) :
    F.map (B.map g) (elPt A B h x) = elPt A B h y :=
  transport_point h (fun x => (A.obj x).point) (fun g => (A.map g).map_point) g

def elLift : S ⥤ F.Elements where
  obj x := ⟨B.obj x, elPt A B h x⟩
  map {x y} g := ⟨B.map g, elPt_map A B h g⟩
  map_id x := by apply Subtype.ext; exact B.map_id x
  map_comp f g := by apply Subtype.ext; exact B.map_comp f g

lemma pointed_mk_cast (P : Pointed.{w}) (Y : Type w) (e : P.X = Y) :
    (⟨Y, cast e P.point⟩ : Pointed.{w}) = P := by
  cases P; subst e; rfl

lemma pointed_hom_heq {P P' Q Q' : Pointed.{w}} (hP : P = P') (hQ : Q = Q') (f : P ⟶ Q)
    (f' : P' ⟶ Q') (H : ∀ (a : P) (a' : P'), HEq a a' → HEq (f.toFun a) (f'.toFun a')) :
    HEq f f' := by
  subst hP hQ
  apply heq_of_eq
  apply Pointed.Hom.ext
  funext a
  exact eq_of_heq (H a a HEq.rfl)

lemma heq_map {A' B' : S ⥤ Type w} (h : A' = B') {x y : S} (g : x ⟶ y) (a : A'.obj x)
    (b : B'.obj x) (hab : HEq a b) : HEq (A'.map g a) (B'.map g b) := by
  subst h
  exact heq_of_eq (congrArg _ (eq_of_heq hab))

lemma elLift_fac_left : elLift A B h ⋙ elToPt F = A := by
  have hobj : ∀ x, (elLift A B h ⋙ elToPt F).obj x = A.obj x :=
    fun x => pointed_mk_cast _ _ (Functor.congr_obj h x)
  refine Functor.hext hobj ?_
  intro x y g
  refine pointed_hom_heq (hobj x) (hobj y) _ _ ?_
  intro a a' haa
  exact heq_map h.symm g a a' haa

lemma elLift_uniq (m : S ⥤ F.Elements) (hA : m ⋙ elToPt F = A)
    (hB : m ⋙ CategoryOfElements.π F = B) : m = elLift A B h := by
  subst hA hB; rfl

end Elements

/-- The forgetful functor from pointed types to types, as a morphism of `Cat`. -/
def U : Cat.of Pointed.{w} ⟶ Cat.of (Type w) := (forget Pointed.{w}).toCatHom

/-- The strict pullback of `U` along `f` in `Cat` is the category of elements of `f`. -/
def elChosen {d : Cat.{w, w + 1}} (f : d ⟶ Cat.of (Type w)) : ChosenPullback U f where
  pullback := Cat.of f.toFunctor.Elements
  p₁ := (elToPt f.toFunctor).toCatHom
  p₂ := (CategoryOfElements.π f.toFunctor).toCatHom
  condition := rfl
  isLimit := PullbackCone.IsLimit.mk _
    (fun s => (elLift s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom)
    (fun s => Cat.Hom.ext (elLift_fac_left _ _ _))
    (fun s => rfl)
    (fun s m hm₁ hm₂ => Cat.Hom.ext
      (elLift_uniq _ _ _ m.toFunctor (congrArg Cat.Hom.toFunctor hm₁)
        (congrArg Cat.Hom.toFunctor hm₂)))

section FC

variable (C : Type (w + 1)) [Category.{w} C]

/-- The indexing set of a formal coproduct. -/
def idx : FormalCoproduct.{w} C ⥤ Type w where
  obj X := X.I
  map f := ↾f.f

/-- The counit: evaluate a formal coproduct at one of its indices. -/
def eps : (idx C).Elements ⥤ C where
  obj x := x.1.obj x.2
  map {x y} f := f.1.φ x.2 ≫ eqToHom (congrArg y.1.obj (f.2 : f.1.f x.2 = y.2))
  map_id x := by
    simp; rfl
  map_comp {x y z} f g := by
    obtain ⟨X, i⟩ := x
    obtain ⟨Y, j⟩ := y
    obtain ⟨Z, k⟩ := z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    change X ⟶ Y at f
    change Y ⟶ Z at g
    obtain rfl : j = f.f i := hf.symm
    obtain rfl : k = g.f (f.f i) := hg.symm
    simp; rfl

lemma fc_hom_ext' {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ i, HEq (f.φ i) (g.φ i)) : f = g := by
  obtain ⟨f₁, φ₁⟩ := f
  obtain ⟨f₂, φ₂⟩ := g
  dsimp only at h₁ h₂
  subst h₁
  congr
  funext i
  exact eq_of_heq (h₂ i)

variable {C} {D : Type (w + 1)} [Category.{w} D] (h : D ⥤ Type w) (G : h.Elements ⥤ C)

lemma map_heq {X Y : D} (g : X ⟶ Y) (a : h.obj X) {b b' : h.obj Y} (e : h.map g a = b)
    (e' : h.map g a = b') :
    HEq (G.map (CategoryOfElements.homMk (h.elementsMk X a) (h.elementsMk Y b) g e))
      (G.map (CategoryOfElements.homMk (h.elementsMk X a) (h.elementsMk Y b') g e')) := by
  subst e; subst e'; rfl

/-- The functor sending `G` on the elements of `h` to the family of objects it defines. -/
def morF : D ⥤ FormalCoproduct.{w} C where
  obj x := ⟨h.obj x, fun a => G.obj ⟨x, a⟩⟩
  map {x y} g := ⟨h.map g, fun a => G.map ⟨g, rfl⟩⟩
  map_id x := by
    apply fc_hom_ext'
    · simp; rfl
    · intro a
      exact (map_heq h G (𝟙 x) a rfl (by simp)).trans (heq_of_eq (G.map_id ⟨x, a⟩))
  map_comp {x y z} g g' := by
    apply fc_hom_ext'
    · simp; rfl
    · intro a
      exact (map_heq h G (g ≫ g') a rfl (by simp)).trans (heq_of_eq (G.map_comp
        (CategoryOfElements.homMk (h.elementsMk x a) (h.elementsMk y (h.map g a)) g rfl)
        (CategoryOfElements.homMk (h.elementsMk y (h.map g a))
          (h.elementsMk z (h.map g' (h.map g a))) g' rfl)))

end FC

section Recon

variable {C : Type (w + 1)} [Category.{w} C] {D : Type (w + 1)} [Category.{w} D]

/-- The functor on elements induced by `k : D ⥤ FormalCoproduct C`. -/
def Psi (k : D ⥤ FormalCoproduct.{w} C) {h : D ⥤ Type w} (e : k ⋙ idx C = h) :
    h.Elements ⥤ (idx C).Elements :=
  elLift (F := idx C) (elToPt h) (CategoryOfElements.π h ⋙ k) (by subst e; rfl)

lemma recon (k : D ⥤ FormalCoproduct.{w} C) {h : D ⥤ Type w} (e : k ⋙ idx C = h) :
    k = morF h (Psi k e ⋙ eps C) := by
  subst e
  refine CategoryTheory.Functor.hext (fun x => rfl) (fun x y g => heq_of_eq ?_)
  apply fc_hom_ext'
  · rfl
  · intro a
    exact heq_of_eq (Category.comp_id _).symm

lemma psi_eps (h : D ⥤ Type w) (G : h.Elements ⥤ C) :
    Psi (morF h G) (rfl : morF h G ⋙ idx C = h) ⋙ eps C = G := by
  have key : ∀ (x y : D) (a : h.obj x) (b : h.obj y) (v : x ⟶ y) (p : h.map v a = b),
      (Psi (morF h G) (rfl : morF h G ⋙ idx C = h) ⋙ eps C).map
        (CategoryOfElements.homMk (h.elementsMk x a) (h.elementsMk y b) v p) =
      G.map (CategoryOfElements.homMk (h.elementsMk x a) (h.elementsMk y b) v p) := by
    intro x y a b v p
    subst p
    exact Category.comp_id _
  exact CategoryTheory.Functor.hext (fun x => rfl)
    (fun x y g => heq_of_eq (key x.1 y.1 x.2 y.2 g.1 g.2))

end Recon

section Final

variable (c : Cat.{w, w + 1})

/-- The partial exponential of `c` along `U` consists of families of objects of `c`. -/
noncomputable def expData : Data U c where
  P := Cat.of (FormalCoproduct.{w} c)
  pi := (idx c).toCatHom
  Pbk := elChosen (idx c).toCatHom
  epsilon := (eps c).toCatHom

variable {c}

lemma idx_eq {d : Cat.{w, w + 1}} (k : d ⟶ (expData c).P) (h : d ⟶ Cat.of (Type w))
    (e : h = k ≫ (expData c).pi) : k.toFunctor ⋙ idx c = h.toFunctor := by
  subst e; rfl

lemma fbf_eq {d : Cat.{w, w + 1}} (k : d ⟶ (expData c).P) (h : d ⟶ Cat.of (Type w))
    (e : h = k ≫ (expData c).pi) :
    FBF_on_mor (expData c) (elChosen h) e = (Psi k.toFunctor (idx_eq k h e)).toCatHom := by
  subst e
  apply (expData c).Pbk.isPullback.hom_ext
  · rw [FBF_on_mor, pullbackMor1, IsPullback.lift_fst]
    exact Cat.Hom.ext (elLift_fac_left _ _ _).symm
  · rw [FBF_on_mor, pullbackMor1, IsPullback.lift_snd]
    rfl

lemma slice_eq {d : Cat.{w, w + 1}} (h : d ⥤ Type w) (G : h.Elements ⥤ c) :
    morF h G ⋙ idx c = h := rfl

/-- `expData c` is universal, making `U` an exponentiable arrow in `Cat`. -/
@[instance_reducible]
noncomputable def expUniversal : Universal (expData c) :=
  universal_of_chosen (expData c) (fun f => elChosen f)
    (fun {d f} g => (morF f.toFunctor g.toFunctor).toCatHom)
    (fun {d f} g => Cat.Hom.ext (slice_eq f.toFunctor g.toFunctor).symm)
    (fun {d f} g => Cat.Hom.ext
      ((psi_eps f.toFunctor g.toFunctor).symm.trans
        (congrArg (fun m => (m ≫ (expData c).epsilon).toFunctor)
          (fbf_eq (morF f.toFunctor g.toFunctor).toCatHom f
            (Cat.Hom.ext (slice_eq f.toFunctor g.toFunctor).symm)).symm)))
    (fun {d f g h} eq_fp eq_gp H => by
      rw [fbf_eq _ _ eq_fp, fbf_eq _ _ eq_gp] at H
      have H' := congrArg Cat.Hom.toFunctor H
      refine Cat.Hom.ext ?_
      rw [recon f.toFunctor (idx_eq f h eq_fp), recon g.toFunctor (idx_eq g h eq_gp)]
      congr 1)

noncomputable instance : IsExpArr (U.{w}) where
  isExpArrowData c := expData c
  isExpArrow _ := expUniversal

end Final

end PointedForget
