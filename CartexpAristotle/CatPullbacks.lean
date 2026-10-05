module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks in `Cat`

The category `Cat.{v, u}` has all pullbacks: the pullback of `F : A ⥤ C` and `G : B ⥤ C` is the
strict pullback category, whose objects are pairs `(a, b)` with `F a = G b` and whose morphisms
are pairs of morphisms with the same image in `C`.

## References

* [Paper, §2.2, Prop. `prop:CAT`]: `CAT` is a Lex-category. This file provides the pullbacks;
  the terminal object comes from Mathlib.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CatPullback

variable {A B C : Cat.{v, u}} (F : A ⟶ C) (G : B ⟶ C)

/-- Objects of the strict pullback. -/
@[ext]
structure Obj where
  /-- The first component. -/
  a : A
  /-- The second component. -/
  b : B
  /-- Both components have the same image. -/
  h : F.toFunctor.obj a = G.toFunctor.obj b

/-- Morphisms of the strict pullback. -/
@[ext]
structure Hom (p q : Obj F G) where
  /-- The first component. -/
  fst : p.a ⟶ q.a
  /-- The second component. -/
  snd : p.b ⟶ q.b
  /-- Both components have the same image. -/
  w : HEq (F.toFunctor.map fst) (G.toFunctor.map snd)

lemma heq_id_of_eq {D : Type*} [Category D] {c c' : D} (h : c = c') :
    HEq (𝟙 c) (𝟙 c') := by
  subst h; rfl

lemma heq_comp_of_heq {D : Type*} [Category D] {a b c a' b' c' : D}
    (ha : a = a') (hb : b = b') (hc : c = c') {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'}
    {g' : b' ⟶ c'} (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst ha hb hc
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

instance : Category.{v} (Obj F G) where
  Hom := Hom F G
  id p := ⟨𝟙 p.a, 𝟙 p.b, by rw [Functor.map_id, Functor.map_id]; exact heq_id_of_eq p.h⟩
  comp {p q r} φ ψ := ⟨φ.fst ≫ ψ.fst, φ.snd ≫ ψ.snd, by
    rw [Functor.map_comp, Functor.map_comp]; exact heq_comp_of_heq p.h q.h r.h φ.w ψ.w⟩
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

variable {F G}

lemma Hom.hext {p p' q q' : Obj F G} (hp : p = p') (hq : q = q') {φ : Hom F G p q}
    {ψ : Hom F G p' q'} (h₁ : HEq φ.fst ψ.fst) (h₂ : HEq φ.snd ψ.snd) : HEq φ ψ := by
  subst hp hq
  rcases φ with ⟨φ₁, φ₂, _⟩
  rcases ψ with ⟨ψ₁, ψ₂, _⟩
  obtain rfl := eq_of_heq h₁
  obtain rfl := eq_of_heq h₂
  rfl

variable (F G)

/-- The first projection. -/
def fst : Cat.of (Obj F G) ⟶ A :=
  Functor.toCatHom
    { obj p := p.a
      map φ := (φ : Hom F G _ _).fst }

/-- The second projection. -/
def snd : Cat.of (Obj F G) ⟶ B :=
  Functor.toCatHom
    { obj p := p.b
      map φ := (φ : Hom F G _ _).snd }

lemma condition : fst F G ≫ F = snd F G ≫ G :=
  Cat.Hom.ext (Functor.hext (fun p => p.h) (fun _ _ φ => (φ : Hom F G _ _).w))

/-- The pullback cone. -/
def cone : PullbackCone F G := PullbackCone.mk (fst F G) (snd F G) (condition F G)

variable {F G}

/-- The lift into the strict pullback. -/
def lift (s : PullbackCone F G) : s.pt ⟶ Cat.of (Obj F G) :=
  Functor.toCatHom
    { obj q := ⟨s.fst.toFunctor.obj q, s.snd.toFunctor.obj q,
        Functor.congr_obj (congrArg Cat.Hom.toFunctor s.condition) q⟩
      map φ := ⟨s.fst.toFunctor.map φ, s.snd.toFunctor.map φ,
        Functor.hcongr_hom (congrArg Cat.Hom.toFunctor s.condition) φ⟩
      map_id q := Hom.ext (s.fst.toFunctor.map_id q) (s.snd.toFunctor.map_id q)
      map_comp φ ψ := Hom.ext (s.fst.toFunctor.map_comp φ ψ) (s.snd.toFunctor.map_comp φ ψ) }

lemma lift_uniq (s : PullbackCone F G) (m : s.pt ⟶ Cat.of (Obj F G))
    (h₁ : m ≫ fst F G = s.fst) (h₂ : m ≫ snd F G = s.snd) : m = lift s := by
  have e₁ := congrArg Cat.Hom.toFunctor h₁
  have e₂ := congrArg Cat.Hom.toFunctor h₂
  have hobj : ∀ c, m.toFunctor.obj c = (lift s).toFunctor.obj c := fun c =>
    Obj.ext (Functor.congr_obj e₁ c) (Functor.congr_obj e₂ c)
  exact Cat.Hom.ext (Functor.hext hobj (fun c c' φ =>
    Hom.hext (hobj c) (hobj c') (Functor.hcongr_hom e₁ φ) (Functor.hcongr_hom e₂ φ)))

variable (F G)

/-- The strict pullback is a pullback in `Cat`. -/
def isLimit : IsLimit (cone F G) :=
  PullbackCone.IsLimit.mk (condition F G) lift (fun _ => rfl) (fun _ => rfl)
    (fun s m h₁ h₂ => lift_uniq s m h₁ h₂)

end CatPullback

instance CatPullback.hasPullbacks : HasPullbacks Cat.{v, u} :=
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} F G =>
    HasLimit.mk ⟨CatPullback.cone F G, CatPullback.isLimit F G⟩
