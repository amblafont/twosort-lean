module

public import CartexpAristotle.FamSlice
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Pullbacks and a terminal object in `FamSlice`

* The terminal object of `FamSlice` is the one-object category equipped with the functor
  constant at the empty family.
* The pullback of `(H, n) : (A, F) ⟶ (C, E)` and `(K, m) : (B, G) ⟶ (C, E)` has as underlying
  category the strict pullback `A ×_C B` (pairs `(a, b)` with `H a = K b`), and the functor to
  `Fam` sends `(a, b)` to the pushout of `F a ← E (H a) = E (K b) → G b` along the cartesian
  maps `n`, `m`: its base is the pushout of the base types, and its fibres are those of `F a`
  resp. `G b` (which agree on glued indices because `n` and `m` are cartesian).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace Fam

lemma Hom.congr_fiber {X Y : Fam.{w}} {φ ψ : X ⟶ Y} (h : φ = ψ) (i : X.base) (x : X.fiber i) :
    HEq ((φ : Hom X Y).fiber i x) ((ψ : Hom X Y).fiber i x) := by
  subst h; rfl

lemma Hom.congr_base {X Y : Fam.{w}} {φ ψ : X ⟶ Y} (h : φ = ψ) (i : X.base) :
    (φ : Hom X Y).base i = (ψ : Hom X Y).base i := by
  subst h; rfl

lemma Hom.IsCartesian.fiber_heq {X Y : Fam.{w}} {φ : X ⟶ Y} (hφ : φ.IsCartesian) (i : X.base)
    (x : X.fiber i) : HEq ((φ : Hom X Y).fiber i x) x := by
  obtain ⟨h, hx⟩ := hφ i
  rw [hx]
  exact cast_heq _ _

lemma Hom.IsCartesian.fiber_eq {X Y : Fam.{w}} {φ : X ⟶ Y} (hφ : φ.IsCartesian) (i : X.base) :
    X.fiber i = Y.fiber ((φ : Hom X Y).base i) := by
  obtain ⟨h, -⟩ := hφ i
  exact h

lemma Hom.ext' {X Y : Fam.{w}} {φ ψ : X ⟶ Y} (h : (φ : Hom X Y).base = (ψ : Hom X Y).base)
    (h' : ∀ i x, HEq ((φ : Hom X Y).fiber i x) ((ψ : Hom X Y).fiber i x)) : φ = ψ := by
  apply Hom.ext (x := φ) (y := ψ) h
  apply Function.hfunext rfl
  intro i i' hi
  obtain rfl := eq_of_heq hi
  apply Function.hfunext rfl
  intro x x' hx
  obtain rfl := eq_of_heq hx
  exact h' i x

lemma Hom.ext_of_isCartesian {X Y : Fam.{w}} {φ ψ : X ⟶ Y} (hφ : φ.IsCartesian)
    (hψ : ψ.IsCartesian) (h : (φ : Hom X Y).base = (ψ : Hom X Y).base) : φ = ψ :=
  Hom.ext' h fun i x => (hφ.fiber_heq i x).trans (hψ.fiber_heq i x).symm

section Functor

variable {C : Type u} [Category.{v} C]

lemma obj_fiber_congr (G : C ⥤ Fam.{w}) {c c' : C} (h : c = c') {i : (G.obj c).base}
    {j : (G.obj c').base} (hij : HEq i j) : (G.obj c).fiber i = (G.obj c').fiber j := by
  subst h
  obtain rfl := eq_of_heq hij
  rfl

lemma obj_base_congr (G : C ⥤ Fam.{w}) {c c' : C} (h : c = c') :
    (G.obj c).base = (G.obj c').base := by
  subst h; rfl

lemma map_base_heq (G : C ⥤ Fam.{w}) {c₁ c₂ c₁' c₂' : C} (h₁ : c₁ = c₁') (h₂ : c₂ = c₂')
    {g : c₁ ⟶ c₂} {g' : c₁' ⟶ c₂'} (hg : HEq g g') {i : (G.obj c₁).base}
    {i' : (G.obj c₁').base} (hi : HEq i i') :
    HEq ((G.map g : Hom _ _).base i) ((G.map g' : Hom _ _).base i') := by
  subst h₁ h₂
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hi
  rfl

lemma map_fiber_heq (G : C ⥤ Fam.{w}) {c₁ c₂ c₁' c₂' : C} (h₁ : c₁ = c₁') (h₂ : c₂ = c₂')
    {g : c₁ ⟶ c₂} {g' : c₁' ⟶ c₂'} (hg : HEq g g') {i : (G.obj c₁).base}
    {i' : (G.obj c₁').base} (hi : HEq i i') {x : (G.obj c₁).fiber i}
    {x' : (G.obj c₁').fiber i'} (hx : HEq x x') :
    HEq ((G.map g : Hom _ _).fiber i x) ((G.map g' : Hom _ _).fiber i' x') := by
  subst h₁ h₂
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hx
  rfl

lemma nat_base {F G : C ⥤ Fam.{w}} (n : F ⟶ G) {c c' : C} (f : c ⟶ c') (i : (F.obj c).base) :
    (G.map f : Hom _ _).base ((n.app c : Hom _ _).base i) =
      (n.app c' : Hom _ _).base ((F.map f : Hom _ _).base i) :=
  (Hom.congr_base (n.naturality f) i).symm

lemma nat_fiber {F G : C ⥤ Fam.{w}} (n : F ⟶ G) {c c' : C} (f : c ⟶ c') (i : (F.obj c).base)
    (x : (F.obj c).fiber i) :
    HEq ((G.map f : Hom _ _).fiber ((n.app c : Hom _ _).base i) ((n.app c : Hom _ _).fiber i x))
      ((n.app c' : Hom _ _).fiber ((F.map f : Hom _ _).base i) ((F.map f : Hom _ _).fiber i x)) :=
  (Hom.congr_fiber (n.naturality f) i x).symm

end Functor

end Fam

lemma CategoryTheory.heq_id_of_eq' {C : Type u} [Category.{v} C] {c c' : C} (h : c = c') :
    HEq (𝟙 c) (𝟙 c') := by
  subst h; rfl

lemma CategoryTheory.heq_comp_of_heq {C : Type u} [Category.{v} C] {a b c a' b' c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c') {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'}
    {g' : b' ⟶ c'} (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst ha hb hc
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

lemma heq_apply_of_heq {α α' β : Sort _} (hα : α = α') {F : α → β} {G : α' → β} (h : HEq F G)
    {a : α} {a' : α'} (ha : HEq a a') : F a = G a' := by
  subst hα
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq ha
  rfl

namespace FamSlice

lemma Hom.ext_of_functor_eq {X Y : FamSlice.{w, v, u}} {f g : Hom X Y}
    (hF : f.functor = g.functor)
    (h : ∀ c, HEq (f.nat.app c : Fam.Hom _ _).base (g.nat.app c : Fam.Hom _ _).base) : f = g := by
  rcases f with ⟨F, n, hn⟩
  rcases g with ⟨G, m, hm⟩
  dsimp only at hF h
  subst hF
  congr 1
  exact NatTrans.ext (funext fun c => Fam.Hom.ext_of_isCartesian (hn c) (hm c) (eq_of_heq (h c)))

lemma Hom.base_heq_of_eq {X Y : FamSlice.{w, v, u}} {f g : Hom X Y} (h : f = g) (c : X.cat) :
    HEq (f.nat.app c : Fam.Hom _ _).base (g.nat.app c : Fam.Hom _ _).base := by
  subst h; rfl

lemma Hom.functor_eq_of_eq {X Y : FamSlice.{w, v, u}} {f g : Hom X Y} (h : f = g) :
    f.functor = g.functor := by
  subst h; rfl

end FamSlice

namespace FamSlice

/-! ### The terminal object -/

/-- The type with a single object, used as the underlying category of the terminal object. -/
inductive Pt : Type u
  | star

/-- `Pt` is a category with exactly one morphism between any two objects. -/
instance : Category.{v} Pt.{u} where
  Hom _ _ := PUnit.{v + 1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- The empty family. -/
def emptyFam : Fam.{w} := ⟨PEmpty, fun i => i.elim⟩

/-- The terminal object of `FamSlice`: the one-object category with the functor constant at the
empty family. -/
def terminal : FamSlice.{w, v, u} :=
  ⟨Cat.of Pt.{u}, (Functor.const _).obj emptyFam⟩

/-- The unique morphism into `terminal`. -/
def toTerminal (X : FamSlice.{w, v, u}) : Hom X terminal where
  functor := (Functor.const X.cat).obj (Pt.star : Pt.{u})
  nat :=
    { app := fun c => (⟨fun i => i.elim, fun i => i.elim⟩ : Fam.Hom emptyFam (X.F.obj c))
      naturality := fun _ _ _ => Fam.Hom.ext' (funext fun i => i.elim) (fun i => i.elim) }
  isPointwiseCartesian := fun _ i => i.elim

lemma eq_toTerminal {X : FamSlice.{w, v, u}} (m : Hom X terminal) : m = toTerminal X := by
  refine Hom.ext_of_functor_eq ?_ (fun c => heq_of_eq (funext fun i => i.elim))
  refine Functor.ext (fun c => ?_) (fun _ _ _ => rfl)
  cases m.functor.obj c
  rfl

/-- `terminal` is a terminal object of `FamSlice`. -/
def isTerminal : IsTerminal (terminal : FamSlice.{w, v, u}) :=
  IsTerminal.ofUniqueHom (fun X => toTerminal X) (fun _ m => eq_toTerminal m)

/-- `FamSlice` has a terminal object. -/
instance hasTerminal : HasTerminal FamSlice.{w, v, u} := isTerminal.hasTerminal

end FamSlice

namespace FamSlice

/-! ### Pullbacks -/

section Pullback

variable {X Y Z : FamSlice.{w, v, u}} (f : Hom X Z) (g : Hom Y Z)

/-- Objects of the strict pullback of the underlying categories. -/
@[ext]
structure PbObj where
  /-- The first component. -/
  a : X.cat
  /-- The second component. -/
  b : Y.cat
  /-- Both components have the same image. -/
  h : f.functor.obj a = g.functor.obj b

/-- Morphisms of the strict pullback of the underlying categories. -/
@[ext]
structure PbHom (p q : PbObj f g) where
  /-- The first component. -/
  fst : p.a ⟶ q.a
  /-- The second component. -/
  snd : p.b ⟶ q.b
  /-- Both components have the same image. -/
  w : HEq (f.functor.map fst) (g.functor.map snd)

instance : Category.{v} (PbObj f g) where
  Hom := PbHom f g
  id p := ⟨𝟙 p.a, 𝟙 p.b, by rw [Functor.map_id, Functor.map_id]; exact heq_id_of_eq' p.h⟩
  comp {p q r} φ ψ := ⟨φ.fst ≫ ψ.fst, φ.snd ≫ ψ.snd, by
    rw [Functor.map_comp, Functor.map_comp]; exact heq_comp_of_heq p.h q.h r.h φ.w ψ.w⟩
  id_comp _ := PbHom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := PbHom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := PbHom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

variable {f g}

lemma PbHom.hext {p p' q q' : PbObj f g} (hp : p = p') (hq : q = q') {φ : PbHom f g p q}
    {ψ : PbHom f g p' q'} (h₁ : HEq φ.fst ψ.fst) (h₂ : HEq φ.snd ψ.snd) : HEq φ ψ := by
  subst hp hq
  rcases φ with ⟨φ₁, φ₂, _⟩
  rcases ψ with ⟨ψ₁, ψ₂, _⟩
  obtain rfl := eq_of_heq h₁
  obtain rfl := eq_of_heq h₂
  rfl

/-- The gluing relation on `F a ⊕ G b` defining the base of the pushout family. -/
def pbRel (p : PbObj f g) (s t : (X.F.obj p.a).base ⊕ (Y.F.obj p.b).base) : Prop :=
  ∃ (i : (Z.F.obj (f.functor.obj p.a)).base) (j : (Z.F.obj (g.functor.obj p.b)).base),
    HEq i j ∧ s = Sum.inl ((f.nat.app p.a : Fam.Hom _ _).base i) ∧
      t = Sum.inr ((g.nat.app p.b : Fam.Hom _ _).base j)

lemma fiber_left_eq (p : PbObj f g) (i : (Z.F.obj (f.functor.obj p.a)).base) :
    (X.F.obj p.a).fiber ((f.nat.app p.a : Fam.Hom _ _).base i) =
      (Z.F.obj (f.functor.obj p.a)).fiber i :=
  ((f.isPointwiseCartesian p.a).fiber_eq i).symm

lemma fiber_right_eq (p : PbObj f g) (j : (Z.F.obj (g.functor.obj p.b)).base) :
    (Y.F.obj p.b).fiber ((g.nat.app p.b : Fam.Hom _ _).base j) =
      (Z.F.obj (g.functor.obj p.b)).fiber j :=
  ((g.isPointwiseCartesian p.b).fiber_eq j).symm

/-- The fibres of the pushout family. -/
def pbFiber (p : PbObj f g) : Quot (pbRel p) → Type w :=
  Quot.lift (Sum.elim (X.F.obj p.a).fiber (Y.F.obj p.b).fiber) (by
    rintro _ _ ⟨i, j, hij, rfl, rfl⟩
    exact (fiber_left_eq p i).trans
      ((Fam.obj_fiber_congr Z.F p.h hij).trans (fiber_right_eq p j).symm))

/-- The pushout family over an object of the strict pullback. -/
def pbFamObj (p : PbObj f g) : Fam.{w} := ⟨Quot (pbRel p), pbFiber p⟩

lemma pbRel_map {p q : PbObj f g} (φ : PbHom f g p q) (s t) (hst : pbRel p s t) :
    pbRel q (Sum.map (X.F.map φ.fst : Fam.Hom _ _).base (Y.F.map φ.snd : Fam.Hom _ _).base s)
      (Sum.map (X.F.map φ.fst : Fam.Hom _ _).base (Y.F.map φ.snd : Fam.Hom _ _).base t) := by
  obtain ⟨i, j, hij, rfl, rfl⟩ := hst
  refine ⟨(Z.F.map (f.functor.map φ.fst) : Fam.Hom _ _).base i,
    (Z.F.map (g.functor.map φ.snd) : Fam.Hom _ _).base j,
    Fam.map_base_heq Z.F p.h q.h φ.w hij, ?_, ?_⟩
  · exact congrArg Sum.inl (Fam.nat_base f.nat φ.fst i)
  · exact congrArg Sum.inr (Fam.nat_base g.nat φ.snd j)

/-- The base map of the pushout family along a morphism. -/
def pbFamMapBase {p q : PbObj f g} (φ : PbHom f g p q) : Quot (pbRel p) → Quot (pbRel q) :=
  Quot.lift
    (fun s => Quot.mk _
      (Sum.map (X.F.map φ.fst : Fam.Hom _ _).base (Y.F.map φ.snd : Fam.Hom _ _).base s))
    (fun s t h => Quot.sound (pbRel_map φ s t h))

lemma pbFamMap_compat {p q : PbObj f g} (φ : PbHom f g p q)
    (i : (Z.F.obj (f.functor.obj p.a)).base) (j : (Z.F.obj (g.functor.obj p.b)).base)
    (hij : HEq i j) :
    HEq ((X.F.map φ.fst : Fam.Hom _ _).fiber ((f.nat.app p.a : Fam.Hom _ _).base i))
      ((Y.F.map φ.snd : Fam.Hom _ _).fiber ((g.nat.app p.b : Fam.Hom _ _).base j)) := by
  apply Function.hfunext ((fiber_left_eq p i).trans
      ((Fam.obj_fiber_congr Z.F p.h hij).trans (fiber_right_eq p j).symm))
  intro x y hxy
  obtain ⟨z, rfl⟩ : ∃ z, (f.nat.app p.a : Fam.Hom _ _).fiber i z = x :=
    ⟨cast (fiber_left_eq p i) x, eq_of_heq
      (((f.isPointwiseCartesian p.a).fiber_heq i _).trans (cast_heq _ _))⟩
  obtain ⟨z', rfl⟩ : ∃ z', (g.nat.app p.b : Fam.Hom _ _).fiber j z' = y :=
    ⟨cast (fiber_right_eq p j) y, eq_of_heq
      (((g.isPointwiseCartesian p.b).fiber_heq j _).trans (cast_heq _ _))⟩
  have hzz : HEq z z' :=
    (((f.isPointwiseCartesian p.a).fiber_heq i z).symm.trans hxy).trans
      ((g.isPointwiseCartesian p.b).fiber_heq j z')
  refine (Fam.nat_fiber f.nat φ.fst i z).trans ?_
  refine HEq.trans ((f.isPointwiseCartesian q.a).fiber_heq _ _) ?_
  refine HEq.trans ?_ (Fam.nat_fiber g.nat φ.snd j z').symm
  refine HEq.trans ?_ ((g.isPointwiseCartesian q.b).fiber_heq _ _).symm
  exact Fam.map_fiber_heq Z.F p.h q.h φ.w hij hzz

/-- The fibre maps of the pushout family along a morphism. -/
def pbFamMapFiber {p q : PbObj f g} (φ : PbHom f g p q) :
    ∀ x, pbFiber p x → pbFiber q (pbFamMapBase φ x) := fun x =>
  Quot.hrecOn (motive := fun x => pbFiber p x → pbFiber q (pbFamMapBase φ x)) x
    (fun s => Sum.rec
      (motive := fun s => pbFiber p (Quot.mk _ s) → pbFiber q (pbFamMapBase φ (Quot.mk _ s)))
      (fun a => (X.F.map φ.fst : Fam.Hom _ _).fiber a)
      (fun b => (Y.F.map φ.snd : Fam.Hom _ _).fiber b) s)
    (by
      rintro _ _ ⟨i, j, hij, rfl, rfl⟩
      exact pbFamMap_compat φ i j hij)

/-- The pushout family along a morphism. -/
def pbFamMap {p q : PbObj f g} (φ : PbHom f g p q) : Fam.Hom (pbFamObj p) (pbFamObj q) :=
  ⟨pbFamMapBase φ, pbFamMapFiber φ⟩

variable (f g) in
/-- The functor from the strict pullback to `Fam` sending `(a, b)` to the pushout family. -/
def pbFam : PbObj f g ⥤ Fam.{w} where
  obj := pbFamObj
  map φ := pbFamMap φ
  map_id p := by
    refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | b
        · exact congrArg (fun t => Quot.mk _ (Sum.inl t))
            (Fam.Hom.congr_base (X.F.map_id p.a) a)
        · exact congrArg (fun t => Quot.mk _ (Sum.inr t))
            (Fam.Hom.congr_base (Y.F.map_id p.b) b)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | b
        · exact fun y => Fam.Hom.congr_fiber (X.F.map_id p.a) a y
        · exact fun y => Fam.Hom.congr_fiber (Y.F.map_id p.b) b y
  map_comp {p q r} φ ψ := by
    refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | b
        · exact congrArg (fun t => Quot.mk _ (Sum.inl t))
            (Fam.Hom.congr_base (X.F.map_comp φ.fst ψ.fst) a)
        · exact congrArg (fun t => Quot.mk _ (Sum.inr t))
            (Fam.Hom.congr_base (Y.F.map_comp φ.snd ψ.snd) b)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | b
        · exact fun y => Fam.Hom.congr_fiber (X.F.map_comp φ.fst ψ.fst) a y
        · exact fun y => Fam.Hom.congr_fiber (Y.F.map_comp φ.snd ψ.snd) b y

end Pullback

end FamSlice

namespace FamSlice

section PullbackCone

variable {X Y Z : FamSlice.{w, v, u}} (f : Hom X Z) (g : Hom Y Z)

/-- The pullback object in `FamSlice`. -/
def pbObj : FamSlice.{w, v, u} := ⟨Cat.of (PbObj f g), pbFam f g⟩

/-- The first projection out of the pullback. -/
def pbFst : Hom (pbObj f g) X where
  functor :=
    { obj := PbObj.a
      map := PbHom.fst
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  nat :=
    { app := fun p =>
        (⟨fun a => Quot.mk _ (Sum.inl a), fun _ x => x⟩ : Fam.Hom (X.F.obj p.a) (pbFamObj p))
      naturality := fun _ _ _ => rfl }
  isPointwiseCartesian := fun _ _ => ⟨rfl, fun _ => rfl⟩

/-- The second projection out of the pullback. -/
def pbSnd : Hom (pbObj f g) Y where
  functor :=
    { obj := PbObj.b
      map := PbHom.snd
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  nat :=
    { app := fun p =>
        (⟨fun b => Quot.mk _ (Sum.inr b), fun _ x => x⟩ : Fam.Hom (Y.F.obj p.b) (pbFamObj p))
      naturality := fun _ _ _ => rfl }
  isPointwiseCartesian := fun _ _ => ⟨rfl, fun _ => rfl⟩

lemma pb_condition : Hom.comp (pbFst f g) f = Hom.comp (pbSnd f g) g := by
  refine Hom.ext_of_functor_eq (Functor.hext (fun p => p.h) (fun _ _ φ => φ.w)) (fun p => ?_)
  apply Function.hfunext (Fam.obj_base_congr Z.F p.h)
  intro i j hij
  exact heq_of_eq (Quot.sound ⟨i, j, hij, rfl, rfl⟩)

end PullbackCone

end FamSlice

namespace FamSlice

section PullbackLift

variable {X Y Z Q : FamSlice.{w, v, u}} {f : Hom X Z} {g : Hom Y Z} (L : Hom Q X) (M : Hom Q Y)
  (hw : Hom.comp L f = Hom.comp M g)

include hw in
lemma pbLift_functor_eq : L.functor ⋙ f.functor = M.functor ⋙ g.functor :=
  Hom.functor_eq_of_eq hw

/-- The functor part of the induced map into the pullback. -/
def pbLiftFunctor : Q.cat ⥤ PbObj f g where
  obj q := ⟨L.functor.obj q, M.functor.obj q, Functor.congr_obj (pbLift_functor_eq L M hw) q⟩
  map φ := ⟨L.functor.map φ, M.functor.map φ, Functor.hcongr_hom (pbLift_functor_eq L M hw) φ⟩
  map_id q := PbHom.ext (L.functor.map_id q) (M.functor.map_id q)
  map_comp φ ψ := PbHom.ext (L.functor.map_comp φ ψ) (M.functor.map_comp φ ψ)

/-- The base map of the induced natural transformation. -/
def pbLiftBase (q : Q.cat) : Quot (pbRel ((pbLiftFunctor L M hw).obj q)) → (Q.F.obj q).base :=
  Quot.lift (Sum.elim (L.nat.app q : Fam.Hom _ _).base (M.nat.app q : Fam.Hom _ _).base) (by
    rintro _ _ ⟨i, j, hij, rfl, rfl⟩
    exact heq_apply_of_heq
      (Fam.obj_base_congr Z.F (Functor.congr_obj (pbLift_functor_eq L M hw) q))
      (Hom.base_heq_of_eq hw q) hij)

lemma pbLift_fiber_eq (q : Q.cat) (x : Quot (pbRel ((pbLiftFunctor L M hw).obj q))) :
    pbFiber ((pbLiftFunctor L M hw).obj q) x = (Q.F.obj q).fiber (pbLiftBase L M hw q x) := by
  induction x using Quot.ind with
  | mk s =>
    rcases s with a | b
    · exact (L.isPointwiseCartesian q).fiber_eq a
    · exact (M.isPointwiseCartesian q).fiber_eq b

/-- The components of the induced natural transformation. -/
def pbLiftApp (q : Q.cat) : Fam.Hom (pbFamObj ((pbLiftFunctor L M hw).obj q)) (Q.F.obj q) :=
  ⟨pbLiftBase L M hw q, fun x y => cast (pbLift_fiber_eq L M hw q x) y⟩

lemma pbLiftApp_isCartesian (q : Q.cat) :
    Fam.Hom.IsCartesian (X := pbFamObj ((pbLiftFunctor L M hw).obj q)) (pbLiftApp L M hw q) :=
  fun x => ⟨pbLift_fiber_eq L M hw q x, fun _ => rfl⟩

/-- The induced map into the pullback. -/
def pbLift : Hom Q (pbObj f g) where
  functor := pbLiftFunctor L M hw
  nat :=
    { app := pbLiftApp L M hw
      naturality := fun q q' φ => by
        refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
        · induction x using Quot.ind with
          | mk s =>
            rcases s with a | b
            · exact Fam.Hom.congr_base (L.nat.naturality φ) a
            · exact Fam.Hom.congr_base (M.nat.naturality φ) b
        · induction x using Quot.ind with
          | mk s =>
            rcases s with a | b
            · intro y
              refine (cast_heq _ _).trans ?_
              have hy : cast (pbLift_fiber_eq L M hw q (Quot.mk _ (Sum.inl a))) y =
                  (L.nat.app q : Fam.Hom _ _).fiber a y :=
                eq_of_heq ((cast_heq _ _).trans ((L.isPointwiseCartesian q).fiber_heq a y).symm)
              refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
              refine HEq.trans ?_ (Fam.nat_fiber L.nat φ a y).symm
              exact ((L.isPointwiseCartesian q').fiber_heq _ _).symm
            · intro y
              refine (cast_heq _ _).trans ?_
              have hy : cast (pbLift_fiber_eq L M hw q (Quot.mk _ (Sum.inr b))) y =
                  (M.nat.app q : Fam.Hom _ _).fiber b y :=
                eq_of_heq ((cast_heq _ _).trans ((M.isPointwiseCartesian q).fiber_heq b y).symm)
              refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
              refine HEq.trans ?_ (Fam.nat_fiber M.nat φ b y).symm
              exact ((M.isPointwiseCartesian q').fiber_heq _ _).symm }
  isPointwiseCartesian := pbLiftApp_isCartesian L M hw

lemma pbLift_fst : Hom.comp (pbLift L M hw) (pbFst f g) = L :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma pbLift_snd : Hom.comp (pbLift L M hw) (pbSnd f g) = M :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma pbLift_uniq (m : Hom Q (pbObj f g)) (h₁ : Hom.comp m (pbFst f g) = L)
    (h₂ : Hom.comp m (pbSnd f g) = M) : m = pbLift L M hw := by
  have e₁ := Hom.functor_eq_of_eq h₁
  have e₂ := Hom.functor_eq_of_eq h₂
  have hobj : ∀ c, m.functor.obj c = (pbLiftFunctor L M hw).obj c := fun c =>
    PbObj.ext (Functor.congr_obj e₁ c) (Functor.congr_obj e₂ c)
  have hF : m.functor = pbLiftFunctor L M hw :=
    Functor.hext hobj (fun c c' φ =>
      PbHom.hext (hobj c) (hobj c') (Functor.hcongr_hom e₁ φ) (Functor.hcongr_hom e₂ φ))
  rcases m with ⟨G, ν, hν⟩
  dsimp only at hF
  subst hF
  refine Hom.ext_of_functor_eq rfl (fun q => heq_of_eq (funext fun x => ?_))
  induction x using Quot.ind with
  | mk s =>
    rcases s with a | b
    · exact congrFun (eq_of_heq (Hom.base_heq_of_eq h₁ q)) a
    · exact congrFun (eq_of_heq (Hom.base_heq_of_eq h₂ q)) b

end PullbackLift

end FamSlice

namespace FamSlice

section HasPullbacks

variable {X Y Z : FamSlice.{w, v, u}} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The pullback cone in `FamSlice`. -/
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (W := pbObj f g) (pbFst f g) (pbSnd f g) (pb_condition f g)

/-- The pullback cone in `FamSlice` is a limit cone. -/
def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk (pb_condition f g)
    (fun s => pbLift s.fst s.snd s.condition)
    (fun s => pbLift_fst s.fst s.snd s.condition)
    (fun s => pbLift_snd s.fst s.snd s.condition)
    (fun s m h₁ h₂ => pbLift_uniq s.fst s.snd s.condition m h₁ h₂)

instance hasPullback : HasPullback f g :=
  HasLimit.mk ⟨pullbackCone f g, pullbackConeIsLimit f g⟩

end HasPullbacks

/-- `FamSlice` has all pullbacks. -/
instance hasPullbacks : HasPullbacks FamSlice.{w, v, u} :=
  hasPullbacks_of_hasLimit_cospan _

end FamSlice
