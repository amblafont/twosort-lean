module

public import CartexpAristotle.CatPullbackCriterion

/-!
# The collage of a functor

For a functor `β : D ⥤ E`, the collage `Collage β` is the category whose objects are the objects
of `D` and of `E`, with morphisms
* `d ⟶ d'` the morphisms of `D`,
* `e ⟶ e'` the morphisms of `E`,
* `d ⟶ e` the morphisms `β d ⟶ e` of `E`,
* no morphisms `e ⟶ d`.

Given functors `P Q : C ⥤ Cat` and a natural transformation `β : P ⟶ Q`, the collages of the
components of `β` assemble into a functor `Collage.functor β : C ⥤ Cat`, which preserves any
pullback square preserved by both `P` and `Q`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

lemma eqToHom_comp_heq' {X : Type*} [Category X] {a b c : X} (e : a = b) (x : b ⟶ c) :
    (eqToHom e ≫ x) ≍ x := by
  subst e; simp

/-- The collage of a functor `β : D ⥤ E`. -/
def Collage {D E : Type u} [Category.{v} D] [Category.{v} E] (_β : D ⥤ E) : Type u := D ⊕ E

namespace Collage

variable {D E : Type u} [Category.{v} D] [Category.{v} E] (β : D ⥤ E)

/-- Morphisms of the collage. -/
def Hom : Collage β → Collage β → Type v
  | .inl d, .inl d' => d ⟶ d'
  | .inl d, .inr e => β.obj d ⟶ e
  | .inr e, .inr e' => e ⟶ e'
  | .inr _, .inl _ => PEmpty

/-- Identities of the collage. -/
def id : (X : Collage β) → Hom β X X
  | .inl d => 𝟙 d
  | .inr e => 𝟙 e

/-- Composition in the collage. -/
def comp : {X Y Z : Collage β} → Hom β X Y → Hom β Y Z → Hom β X Z
  | .inl _, .inl _, .inl _, f, g => (f ≫ g : _ ⟶ _)
  | .inl _, .inl _, .inr _, f, g => (β.map f ≫ g : _ ⟶ _)
  | .inl _, .inr _, .inr _, f, g => (f ≫ g : _ ⟶ _)
  | .inr _, .inr _, .inr _, f, g => (f ≫ g : _ ⟶ _)
  | .inr _, .inl _, _, f, _ => PEmpty.elim f
  | .inl _, .inr _, .inl _, _, g => PEmpty.elim g
  | .inr _, .inr _, .inl _, _, g => PEmpty.elim g

instance : Category.{v} (Collage β) where
  Hom := Hom β
  id := id β
  comp := comp β
  id_comp {X Y} f := by
    rcases X with X | X <;> rcases Y with Y | Y
    · exact Category.id_comp (obj := D) _
    · exact (congrArg (· ≫ _) (β.map_id X)).trans (Category.id_comp (obj := E) _)
    · exact PEmpty.elim f
    · exact Category.id_comp (obj := E) _
  comp_id {X Y} f := by
    rcases X with X | X <;> rcases Y with Y | Y
    · exact Category.comp_id (obj := D) _
    · exact Category.comp_id (obj := E) _
    · exact PEmpty.elim f
    · exact Category.comp_id (obj := E) _
  assoc {W X Y Z} f g h := by
    rcases W with W | W <;> rcases X with X | X <;> rcases Y with Y | Y <;>
      rcases Z with Z | Z <;>
      first
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | exact PEmpty.elim h
      | skip
    · exact Category.assoc (obj := D) _ _ _
    · exact (congrArg (· ≫ _) (β.map_comp _ _)).trans (Category.assoc (obj := E) _ _ _)
    · exact Category.assoc (obj := E) _ _ _
    · exact Category.assoc (obj := E) _ _ _
    · exact Category.assoc (obj := E) _ _ _

/-- The inclusion of `D` into the collage. -/
def incl₁ : D ⥤ Collage β where
  obj d := Sum.inl d
  map f := (f : Hom β (.inl _) (.inl _))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion of `E` into the collage. -/
def incl₂ : E ⥤ Collage β where
  obj e := Sum.inr e
  map f := (f : Hom β (.inr _) (.inr _))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical morphism `inl d ⟶ inr (β d)`. -/
def cross (d : D) : (incl₁ β).obj d ⟶ (incl₂ β).obj (β.obj d) :=
  (𝟙 (β.obj d) : Hom β (.inl d) (.inr (β.obj d)))

section Map

variable {β} {D' E' : Type u} [Category.{v} D'] [Category.{v} E'] {β' : D' ⥤ E'}
  (P : D ⥤ D') (Q : E ⥤ E') (h : P ⋙ β' = β ⋙ Q)

/-- The object part of the functor between collages induced by a commutative square. -/
def mapObj : Collage β → Collage β'
  | .inl d => .inl (P.obj d)
  | .inr e => .inr (Q.obj e)

/-- The morphism part of the functor between collages induced by a commutative square. -/
def mapHom : {X Y : Collage β} → Hom β X Y → Hom β' (mapObj P Q X) (mapObj P Q Y)
  | .inl _, .inl _, f => (P.map f : _ ⟶ _)
  | .inl d, .inr _, f => (eqToHom (Functor.congr_obj h d) ≫ Q.map f : _ ⟶ _)
  | .inr _, .inr _, f => (Q.map f : _ ⟶ _)
  | .inr _, .inl _, f => PEmpty.elim f

/-- The functor between collages induced by a commutative square. -/
def map : Collage β ⥤ Collage β' where
  obj := mapObj P Q
  map := mapHom P Q h
  map_id X := by
    rcases X with X | X
    · exact P.map_id X
    · exact Q.map_id X
  map_comp {X Y Z} f g := by
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z <;>
      first
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | skip
    · exact P.map_comp f g
    · change eqToHom _ ≫ Q.map (β.map f ≫ g) = β'.map (P.map f) ≫ eqToHom _ ≫ Q.map g
      have := Functor.congr_hom h f
      simp only [Functor.comp_map] at this
      rw [this]; simp
    · change eqToHom _ ≫ Q.map (f ≫ g) = (eqToHom _ ≫ Q.map f) ≫ Q.map g
      simp
    · exact Q.map_comp f g

@[simp] lemma map_obj_inl (d : D) : (map P Q h).obj (.inl d) = .inl (P.obj d) := rfl
@[simp] lemma map_obj_inr (e : E) : (map P Q h).obj (.inr e) = .inr (Q.obj e) := rfl

lemma incl₁_comp_map : incl₁ β ⋙ map P Q h = P ⋙ incl₁ β' := rfl
lemma incl₂_comp_map : incl₂ β ⋙ map P Q h = Q ⋙ incl₂ β' := rfl

end Map

section Lift

variable {β} {T : Type*} [Category T] (F₁ : D ⥤ T) (F₂ : E ⥤ T) (θ : F₁ ⟶ β ⋙ F₂)

/-- The object part of the functor out of a collage. -/
def liftObj : Collage β → T
  | .inl d => F₁.obj d
  | .inr e => F₂.obj e

/-- The morphism part of the functor out of a collage. -/
def liftHom : {X Y : Collage β} → Hom β X Y → (liftObj F₁ F₂ X ⟶ liftObj F₁ F₂ Y)
  | .inl _, .inl _, f => F₁.map f
  | .inl d, .inr _, f => θ.app d ≫ F₂.map f
  | .inr _, .inr _, f => F₂.map f
  | .inr _, .inl _, f => PEmpty.elim f

/-- The functor out of a collage given by functors out of `D` and `E` and a natural
transformation `F₁ ⟶ β ⋙ F₂`. -/
def lift : Collage β ⥤ T where
  obj := liftObj F₁ F₂
  map := liftHom F₁ F₂ θ
  map_id X := by
    rcases X with X | X
    · exact F₁.map_id X
    · exact F₂.map_id X
  map_comp {X Y Z} f g := by
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z <;>
      first
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | skip
    · exact F₁.map_comp f g
    · change θ.app X ≫ F₂.map (β.map f ≫ g) = F₁.map f ≫ θ.app Y ≫ F₂.map g
      rw [F₂.map_comp, ← Category.assoc, ← Category.assoc]
      congr 1
      exact (θ.naturality f).symm
    · change θ.app X ≫ F₂.map (f ≫ g) = (θ.app X ≫ F₂.map f) ≫ F₂.map g
      simp
    · exact F₂.map_comp f g

@[simp] lemma lift_obj_inl (d : D) : (lift F₁ F₂ θ).obj (.inl d) = F₁.obj d := rfl
@[simp] lemma lift_obj_inr (e : E) : (lift F₁ F₂ θ).obj (.inr e) = F₂.obj e := rfl

lemma incl₁_comp_lift : incl₁ β ⋙ lift F₁ F₂ θ = F₁ := rfl
lemma incl₂_comp_lift : incl₂ β ⋙ lift F₁ F₂ θ = F₂ := rfl

end Lift

lemma map_id : map (β := β) (𝟭 D) (𝟭 E) rfl = 𝟭 _ := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro X; rcases X with X | X <;> rfl
  intro X Y f
  rcases X with X | X <;> rcases Y with Y | Y
  · exact HEq.rfl
  · exact eqToHom_comp_heq' _ _
  · exact PEmpty.elim f
  · exact HEq.rfl

lemma map_comp {D' E' D'' E'' : Type u} [Category.{v} D'] [Category.{v} E'] [Category.{v} D'']
    [Category.{v} E''] {β' : D' ⥤ E'} {β'' : D'' ⥤ E''} (P : D ⥤ D') (Q : E ⥤ E')
    (h : P ⋙ β' = β ⋙ Q) (P' : D' ⥤ D'') (Q' : E' ⥤ E'') (h' : P' ⋙ β'' = β' ⋙ Q') :
    map (P ⋙ P') (Q ⋙ Q') (by rw [Functor.assoc, h', ← Functor.assoc, h]; rfl) =
      map P Q h ⋙ map P' Q' h' := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro X; rcases X with X | X <;> rfl
  intro X Y f
  rcases X with X | X <;> rcases Y with Y | Y
  · exact HEq.rfl
  · refine (eqToHom_comp_heq' _ _).trans ?_
    change _ ≍ (eqToHom _ ≫ Q'.map (eqToHom _ ≫ Q.map f))
    rw [Functor.map_comp, eqToHom_map, ← Category.assoc, eqToHom_trans]
    exact (eqToHom_comp_heq' _ _).symm
  · exact PEmpty.elim f
  · exact HEq.rfl

lemma map_congr {D' E' : Type u} [Category.{v} D'] [Category.{v} E'] {β' : D' ⥤ E'}
    {P P' : D ⥤ D'} {Q Q' : E ⥤ E'} (h : P ⋙ β' = β ⋙ Q) (h' : P' ⋙ β' = β ⋙ Q') (hP : P = P')
    (hQ : Q = Q') : map P Q h = map P' Q' h' := by
  subst hP hQ; rfl

section Functor

variable {C : Type u'} [Category.{v'} C] {P Q : C ⥤ Cat.{v, u}} (α : P ⟶ Q)

/-- The collages of the components of a natural transformation `α : P ⟶ Q` between functors to
`Cat`, as a functor to `Cat`. -/
def functor : C ⥤ Cat.{v, u} where
  obj c := Cat.of (Collage (α.app c).toFunctor)
  map {c c'} f := (map (P.map f).toFunctor (Q.map f).toFunctor
    (congrArg Cat.Hom.toFunctor (α.naturality f))).toCatHom
  map_id c := by
    ext1
    have e₁ : (P.map (𝟙 c)).toFunctor = 𝟭 _ := by rw [P.map_id]; rfl
    have e₂ : (Q.map (𝟙 c)).toFunctor = 𝟭 _ := by rw [Q.map_id]; rfl
    exact (map_congr (hP := e₁) (hQ := e₂) ..).trans (map_id _)
  map_comp {c c' c''} f g := by
    ext1
    have e₁ : (P.map (f ≫ g)).toFunctor = (P.map f).toFunctor ⋙ (P.map g).toFunctor := by
      rw [P.map_comp]; rfl
    have e₂ : (Q.map (f ≫ g)).toFunctor = (Q.map f).toFunctor ⋙ (Q.map g).toFunctor := by
      rw [Q.map_comp]; rfl
    exact (map_congr (hP := e₁) (hQ := e₂) ..).trans (map_comp _ _ _ _ _ _ _)

@[simp] lemma functor_obj (c : C) : (functor α).obj c = Cat.of (Collage (α.app c).toFunctor) :=
  rfl

lemma functor_map_toFunctor {c c' : C} (f : c ⟶ c') : ((functor α).map f).toFunctor =
    map (P.map f).toFunctor (Q.map f).toFunctor (congrArg Cat.Hom.toFunctor (α.naturality f)) :=
  rfl

/-- The inclusion `P ⟶ functor α`. -/
def ι₁ : P ⟶ functor α where
  app c := (incl₁ (α.app c).toFunctor).toCatHom
  naturality _ _ _ := rfl

/-- The inclusion `Q ⟶ functor α`. -/
def ι₂ : Q ⟶ functor α where
  app c := (incl₂ (α.app c).toFunctor).toCatHom
  naturality _ _ _ := rfl

end Functor

section Pullback

variable {C : Type u'} [Category.{v'} C] {P Q : C ⥤ Cat.{v, u}} (α : P ⟶ Q)
  {W X₁ X₂ S : C} {fst : W ⟶ X₁} {snd : W ⟶ X₂} {f : X₁ ⟶ S} {g : X₂ ⟶ S}

/-- The collage functor preserves the pullback squares preserved by `P` and `Q`. -/
theorem functor_isPullback (comm : fst ≫ f = snd ≫ g)
    (hP : IsPullback (P.map fst) (P.map snd) (P.map f) (P.map g))
    (hQ : IsPullback (Q.map fst) (Q.map snd) (Q.map f) (Q.map g)) :
    IsPullback ((functor α).map fst) ((functor α).map snd) ((functor α).map f)
      ((functor α).map g) := by
  have cP := CatPullback.crit_of_isPullback hP
  have cQ := CatPullback.crit_of_isPullback hQ
  have hcomm : (functor α).map fst ≫ (functor α).map f = (functor α).map snd ≫ (functor α).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  refine CatPullback.isPullback_of_crit ⟨?_, ?_⟩ hcomm
  · intro x₁ x₂ h
    rcases x₁ with d₁ | e₁ <;> rcases x₂ with d₂ | e₂
    · obtain ⟨d, hd, hu⟩ := cP.obj d₁ d₂ (Sum.inl.inj h)
      refine ⟨Sum.inl d, ⟨congrArg Sum.inl hd.1, congrArg Sum.inl hd.2⟩, ?_⟩
      rintro (d' | e') ⟨h₁, h₂⟩
      · exact congrArg Sum.inl (hu d' ⟨Sum.inl.inj h₁, Sum.inl.inj h₂⟩)
      · cases h₁
    · cases h
    · cases h
    · obtain ⟨e, he, hu⟩ := cQ.obj e₁ e₂ (Sum.inr.inj h)
      refine ⟨Sum.inr e, ⟨congrArg Sum.inr he.1, congrArg Sum.inr he.2⟩, ?_⟩
      rintro (d' | e') ⟨h₁, h₂⟩
      · cases h₁
      · exact congrArg Sum.inr (hu e' ⟨Sum.inr.inj h₁, Sum.inr.inj h₂⟩)
  · intro w w' h₁ h₂ h
    rcases w with d | e <;> rcases w' with d' | e'
    · obtain ⟨k, hk, hu⟩ := cP.hom d d' h₁ h₂ h
      exact ⟨k, hk, fun k' hk' => hu k' hk'⟩
    · have a₁ : (α.app X₁).toFunctor.obj ((P.map fst).toFunctor.obj d) =
          (Q.map fst).toFunctor.obj ((α.app W).toFunctor.obj d) :=
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality fst)) d
      have a₂ : (α.app X₂).toFunctor.obj ((P.map snd).toFunctor.obj d) =
          (Q.map snd).toFunctor.obj ((α.app W).toFunctor.obj d) :=
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality snd)) d
      have h₁e : h₁ = (eqToHom a₁ ≫ (eqToHom a₁.symm ≫ h₁ :
          (Q.map fst).toFunctor.obj ((α.app W).toFunctor.obj d) ⟶ _) :) := by simp
      obtain ⟨k, hk, hu⟩ := cQ.hom ((α.app W).toFunctor.obj d) e'
        (eqToHom a₁.symm ≫ h₁) (eqToHom a₂.symm ≫ h₂) (by
          simp only [Functor.map_comp, eqToHom_map]
          refine (eqToHom_comp_heq' _ _).trans ?_
          refine HEq.trans ?_ (eqToHom_comp_heq' _ _).symm
          exact ((eqToHom_comp_heq' _ _).symm.trans h).trans (eqToHom_comp_heq' _ _))
      refine ⟨(k : Hom _ (.inl d) (.inr e')), ⟨?_, ?_⟩, fun k' hk' => hu k' ⟨?_, ?_⟩⟩
      · change eqToHom _ ≫ (Q.map fst).toFunctor.map k = h₁
        rw [hk.1]; simp
      · change eqToHom _ ≫ (Q.map snd).toFunctor.map k = h₂
        rw [hk.2]; simp
      · have := hk'.1
        change eqToHom _ ≫ (Q.map fst).toFunctor.map k' = h₁ at this
        rw [← this]; simp
      · have := hk'.2
        change eqToHom _ ≫ (Q.map snd).toFunctor.map k' = h₂ at this
        rw [← this]; simp
    · exact PEmpty.elim h₁
    · obtain ⟨k, hk, hu⟩ := cQ.hom e e' h₁ h₂ h
      exact ⟨k, hk, fun k' hk' => hu k' hk'⟩

end Pullback

end Collage

/-! ### Discrete categories on hom-types -/

/-- The discrete category on a type `S`, with morphisms in `Type v`. -/
def Disc (S : Type u) : Type u := S

namespace Disc

instance (S : Type u) : Category.{v} (Disc S) where
  Hom x y := ULift.{v} (PLift (x = y))
  id _ := ⟨⟨rfl⟩⟩
  comp f g := ⟨⟨f.down.down.trans g.down.down⟩⟩

variable {S T : Type u}

lemma eq_of_hom {x y : Disc S} (f : x ⟶ y) : x = y := f.down.down

/-- The morphism of a discrete category given by an equality. -/
def homOfEq {x y : Disc S} (h : x = y) : x ⟶ y := ⟨⟨h⟩⟩

lemma hom_ext {x y : Disc S} (f g : x ⟶ y) : f = g := by
  rcases f with ⟨⟨_⟩⟩; rcases g with ⟨⟨_⟩⟩; rfl

instance {x y : Disc S} : Subsingleton (x ⟶ y) := ⟨hom_ext⟩

/-- A functor out of a discrete category. -/
def functor {E : Type*} [Category E] (o : S → E) : Disc S ⥤ E where
  obj := o
  map f := eqToHom (congrArg o (eq_of_hom f))

/-- The functor between discrete categories induced by a function. -/
def map (φ : S → T) : Disc S ⥤ Disc T where
  obj := φ
  map f := homOfEq (congrArg φ (eq_of_hom f))

end Disc

section HomFunctor

variable {C : Type u'} [Category.{u} C]

/-- The functor `Γ ↦ Disc (a ⟶ Γ)` to `Cat`. -/
def homDiscFunctor (a : C) : C ⥤ Cat.{v, u} where
  obj Γ := Cat.of (Disc (a ⟶ Γ))
  map σ := (Disc.map (fun t : a ⟶ _ => t ≫ σ)).toCatHom
  map_id Γ := by
    ext1
    exact CategoryTheory.Functor.ext (fun t => Category.comp_id t) (fun _ _ _ => Disc.hom_ext _ _)
  map_comp σ τ := by
    ext1
    exact CategoryTheory.Functor.ext (fun t => (Category.assoc t σ τ).symm) (fun _ _ _ => Disc.hom_ext _ _)

lemma homDiscFunctor_map_obj (a : C) {Γ Γ' : C} (σ : Γ ⟶ Γ') (t : a ⟶ Γ) :
    ((homDiscFunctor.{v} a).map σ).toFunctor.obj t = t ≫ σ := rfl

/-- `homDiscFunctor a` preserves pullback squares. -/
theorem homDiscFunctor_isPullback (a : C) {W X₁ X₂ S : C} {fst : W ⟶ X₁} {snd : W ⟶ X₂}
    {f : X₁ ⟶ S} {g : X₂ ⟶ S} (hpb : IsPullback fst snd f g) :
    IsPullback ((homDiscFunctor.{v} a).map fst) ((homDiscFunctor.{v} a).map snd)
      ((homDiscFunctor.{v} a).map f) ((homDiscFunctor.{v} a).map g) := by
  have hcomm : (homDiscFunctor.{v} a).map fst ≫ (homDiscFunctor.{v} a).map f =
      (homDiscFunctor.{v} a).map snd ≫ (homDiscFunctor.{v} a).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]
  refine CatPullback.isPullback_of_crit ⟨?_, ?_⟩ hcomm
  · intro x₁ x₂ h
    refine ⟨hpb.lift x₁ x₂ h, ⟨hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩, fun w hw => ?_⟩
    exact hpb.hom_ext (hw.1.trans (hpb.lift_fst _ _ _).symm) (hw.2.trans (hpb.lift_snd _ _ _).symm)
  · intro w w' h₁ h₂ _
    have : w = w' := hpb.hom_ext (Disc.eq_of_hom h₁) (Disc.eq_of_hom h₂)
    exact ⟨Disc.homOfEq this, ⟨Disc.hom_ext _ _, Disc.hom_ext _ _⟩, fun _ _ => Disc.hom_ext _ _⟩

end HomFunctor
