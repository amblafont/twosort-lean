/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import CartexpAristotle.CatPullbacks

/-!
# Wide pullbacks in `Cat`

The wide pullback of a family of functors `F j : A j ⥤ B` (indexed by `J : Type w`) is the strict
wide pullback category, whose objects are an object `b : B` together with objects `a j : A j`
with `F j (a j) = b`, and whose morphisms are a morphism `g` of `B` together with morphisms `f j`
of the `A j` with `F j (f j) = g`.

As `Cat.{v, u}` is only known to Mathlib to have limits for `u = v`, we construct these wide
pullbacks by hand (`CatWidePullback.isLimit`). The diagrams live in `Cat.{max v w, max u w}`; in
particular `Cat.{w, w + 1}` has all `w`-small wide pullbacks (`CatWidePullback.hasWidePullbacks`).
-/

universe w v u

open CategoryTheory Limits

namespace CatWidePullback

variable {J : Type w} (K : WidePullbackShape J ⥤ Cat.{max v w, max u w})

/-- The leg `K (some j) ⥤ K none` of the diagram. -/
abbrev leg (j : J) : K.obj (some j) ⥤ K.obj none := (K.map (WidePullbackShape.Hom.term j)).toFunctor

/-- Objects of the strict wide pullback. -/
@[ext]
structure Obj where
  /-- The object of the base. -/
  b : K.obj none
  /-- The objects of the components. -/
  a : ∀ j, K.obj (some j)
  /-- All components lie over the base. -/
  h : ∀ j, (leg K j).obj (a j) = b

/-- Morphisms of the strict wide pullback. -/
@[ext]
structure Hom (p q : Obj K) where
  /-- The morphism of the base. -/
  base : p.b ⟶ q.b
  /-- The morphisms of the components. -/
  comp : ∀ j, p.a j ⟶ q.a j
  /-- All components lie over the base morphism. -/
  w : ∀ j, HEq ((leg K j).map (comp j)) base

instance : Category.{max v w} (Obj K) where
  Hom := Hom K
  id p := ⟨𝟙 p.b, fun j => 𝟙 (p.a j), fun j => by
    rw [Functor.map_id]; exact CatPullback.heq_id_of_eq (p.h j)⟩
  comp {p q r} φ ψ := ⟨φ.base ≫ ψ.base, fun j => φ.comp j ≫ ψ.comp j, fun j => by
    rw [Functor.map_comp]
    exact CatPullback.heq_comp_of_heq (p.h j) (q.h j) (r.h j) (φ.w j) (ψ.w j)⟩
  id_comp _ := Hom.ext (Category.id_comp _) (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (funext fun _ => Category.assoc _ _ _)

variable {K}

lemma Hom.hext {p p' q q' : Obj K} (hp : p = p') (hq : q = q') {φ : Hom K p q}
    {ψ : Hom K p' q'} (h₁ : HEq φ.base ψ.base) (h₂ : ∀ j, HEq (φ.comp j) (ψ.comp j)) :
    HEq φ ψ := by
  subst hp hq
  rcases φ with ⟨φ₁, φ₂, _⟩
  rcases ψ with ⟨ψ₁, ψ₂, _⟩
  obtain rfl := eq_of_heq h₁
  obtain rfl : φ₂ = ψ₂ := funext fun j => eq_of_heq (h₂ j)
  rfl

variable (K)

/-- The projection to the base. -/
def base : Cat.of (Obj K) ⟶ K.obj none :=
  Functor.toCatHom
    { obj p := p.b
      map φ := (φ : Hom K _ _).base }

/-- The projection to a component. -/
def proj (j : J) : Cat.of (Obj K) ⟶ K.obj (some j) :=
  Functor.toCatHom
    { obj p := p.a j
      map φ := (φ : Hom K _ _).comp j }

lemma proj_comp (j : J) : proj K j ≫ K.map (WidePullbackShape.Hom.term j) = base K :=
  Cat.Hom.ext (Functor.hext (fun p => p.h j) (fun _ _ φ => (φ : Hom K _ _).w j))

/-- The wide pullback cone. -/
def cone : Cone K := WidePullbackShape.mkCone (base K) (proj K) (proj_comp K)

variable {K}

/-- The lift into the strict wide pullback. -/
def lift (s : Cone K) : s.pt ⟶ Cat.of (Obj K) :=
  Functor.toCatHom
    { obj q := ⟨(s.π.app none).toFunctor.obj q, fun j => (s.π.app (some j)).toFunctor.obj q,
        fun j => Functor.congr_obj (congrArg Cat.Hom.toFunctor
          (s.π.naturality (WidePullbackShape.Hom.term j))).symm q⟩
      map φ := ⟨(s.π.app none).toFunctor.map φ, fun j => (s.π.app (some j)).toFunctor.map φ,
        fun j => by
          have := Functor.hcongr_hom (congrArg Cat.Hom.toFunctor
            (s.π.naturality (WidePullbackShape.Hom.term j))).symm φ
          simpa using this⟩
      map_id q := Hom.ext ((s.π.app none).toFunctor.map_id q)
        (funext fun j => (s.π.app (some j)).toFunctor.map_id q)
      map_comp φ ψ := Hom.ext ((s.π.app none).toFunctor.map_comp φ ψ)
        (funext fun j => (s.π.app (some j)).toFunctor.map_comp φ ψ) }

lemma lift_base (s : Cone K) : lift s ≫ base K = s.π.app none := rfl

lemma lift_proj (s : Cone K) (j : J) : lift s ≫ proj K j = s.π.app (some j) := rfl

lemma lift_uniq (s : Cone K) (m : s.pt ⟶ Cat.of (Obj K))
    (h₀ : m ≫ base K = s.π.app none) (h : ∀ j, m ≫ proj K j = s.π.app (some j)) :
    m = lift s := by
  have e₀ := congrArg Cat.Hom.toFunctor h₀
  have e := fun j => congrArg Cat.Hom.toFunctor (h j)
  have hobj : ∀ c, m.toFunctor.obj c = (lift s).toFunctor.obj c := fun c =>
    Obj.ext (Functor.congr_obj e₀ c) (funext fun j => Functor.congr_obj (e j) c)
  exact Cat.Hom.ext (Functor.hext hobj (fun c c' φ =>
    Hom.hext (hobj c) (hobj c') (Functor.hcongr_hom e₀ φ)
      (fun j => Functor.hcongr_hom (e j) φ)))

variable (K)

/-- The strict wide pullback is a wide pullback in `Cat`. -/
def isLimit : IsLimit (cone K) where
  lift := lift
  fac s j := by
    cases j
    · exact lift_base s
    · exact lift_proj s _
  uniq s m h := lift_uniq s m (h none) (fun j => h (some j))

end CatWidePullback

/-- `Cat.{w, w + 1}` has all `w`-small wide pullbacks. -/
instance CatWidePullback.hasWidePullbacks : HasWidePullbacks.{w} Cat.{w, w + 1} := fun _ =>
  ⟨fun K => HasLimit.mk ⟨CatWidePullback.cone.{w, w, w + 1} K,
    CatWidePullback.isLimit.{w, w, w + 1} K⟩⟩
