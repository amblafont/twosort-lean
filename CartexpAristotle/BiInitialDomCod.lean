/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.UniversalNatTrans
import CartexpAristotle.Strictification

/-!
# The chosen arrow of a bi-initial `Lexp` has distinct domain and codomain

We exhibit an object of `Lexp` (in every universe) whose chosen arrow `⊥ ⟶ ⊤` has a
domain and codomain which are not isomorphic: the two-element linear order `Bool`, seen as a
thin category, where every arrow with codomain `⊤` is exponentiable.

The unique-up-to-iso morphism from a bi-initial `A` to it sends the chosen arrow of `A` to an
arrow isomorphic to `⊥ ⟶ ⊤`. If the domain and codomain of the chosen arrow of `A` were equal,
this would give a morphism `⊤ ⟶ ⊥`, which does not exist.

## References

* [Paper, §2.2, Prop. `prop:strictification`] requires the chosen exponentiable arrow `p : Y → X`
  to satisfy `X ≠ Y`. This file proves this hypothesis for any bi-initial `Lexp`-category
  (`Lexp.IsBiInitial.dom_ne_cod`), and deduces the last sentence of
  Prop. `prop:strictification`: there is a strict morphism out of `FinGat` to any `Lexp`-category
  (`Lexp.IsBiInitial.exists_strict_hom`).
-/

open CategoryTheory Limits

universe v u

namespace Lexp

/-- The two-element linear order `false < true`, as a thin category in arbitrary universes. -/
structure TwoCat : Type u where
  /-- The underlying boolean. -/
  val : Bool

namespace TwoCat

instance : Category.{v} TwoCat.{u} where
  Hom a b := ULift.{v} (PLift (a.val ≤ b.val))
  id a := ⟨⟨le_refl a.val⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

instance (a b : TwoCat.{u}) : Subsingleton (a ⟶ b) :=
  ⟨fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl⟩

/-- A morphism from an inequality. -/
def homOfLE' {a b : TwoCat.{u}} (h : a.val ≤ b.val) : a ⟶ b := ⟨⟨h⟩⟩

lemma le_of_hom' {a b : TwoCat.{u}} (f : a ⟶ b) : a.val ≤ b.val := f.down.down

/-- The bottom element. -/
def bot : TwoCat.{u} := ⟨false⟩

/-- The top element. -/
def top : TwoCat.{u} := ⟨true⟩

/-- The terminal object `top`. -/
def isTerminalTop : IsTerminal (top : TwoCat.{u}) :=
  IsTerminal.ofUniqueHom (fun a => homOfLE' (Bool.le_true a.val))
    (fun _ _ => Subsingleton.elim _ _)

instance : HasTerminal TwoCat.{u} := isTerminalTop.hasTerminal

/-- The pullback cone given by the meet. -/
def meetCone {X Y Z : TwoCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (W := ⟨X.val && Y.val⟩) (homOfLE' (Bool.and_le_left _ _))
    (homOfLE' (Bool.and_le_right _ _)) (Subsingleton.elim _ _)

/-- The meet is a pullback. -/
def meetConeIsLimit {X Y Z : TwoCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (meetCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun s => homOfLE' (Bool.le_and (le_of_hom' s.fst) (le_of_hom' s.snd)))
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

instance : HasPullbacks TwoCat.{u} :=
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _ f g} =>
    ⟨⟨⟨meetCone f g, meetConeIsLimit f g⟩⟩⟩

/-- The chosen pullback given by the meet. -/
def meetPullback {X Y Z : TwoCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : ChosenPullback f g where
  pullback := ⟨X.val && Y.val⟩
  p₁ := homOfLE' (Bool.and_le_left _ _)
  p₂ := homOfLE' (Bool.and_le_right _ _)
  condition := Subsingleton.elim _ _
  isLimit := meetConeIsLimit f g

/-- The arrow `bot ⟶ top`. -/
def botTop : (bot : TwoCat.{u}) ⟶ top := homOfLE' (Bool.le_true _)

/-- The arrow `bot ⟶ top` is exponentiable: the exponential of any `c` is `top`. -/
instance : IsExpArr (botTop : (bot : TwoCat.{u}) ⟶ top) where
  isExpArrowData _ :=
    { P := top
      pi := 𝟙 _
      Pbk := meetPullback _ _
      epsilon := homOfLE' (Bool.false_le _) }
  isExpArrow _ :=
    { mor := fun _ => homOfLE' (Bool.le_true _)
      isSlice := fun _ => Subsingleton.elim _ _
      comm := fun _ => Subsingleton.elim _ _
      uniq := fun _ _ _ _ => Subsingleton.elim _ _ }

end TwoCat

/-- The object of `Lexp` given by the two-element linear order with chosen arrow
`⊥ ⟶ ⊤`. -/
def twoExp : Lexp.{v, u} where
  carrier := TwoCat.{u}
  arr := TwoCat.botTop

/-- **The domain and codomain of the chosen exponentiable arrow of a bi-initial `Lexp`
are different.**

Hypothesis `X ≠ Y` of [Paper, §2.2, Prop. `prop:strictification`]. -/
theorem IsBiInitial.dom_ne_cod {A : Lexp.{v, u}} (hA : IsBiInitial A) : A.dom ≠ A.cod := by
  intro h
  obtain ⟨F⟩ := hA.nonempty_hom twoExp.{v, u}
  have f : (TwoCat.top : TwoCat.{u}) ⟶ TwoCat.bot :=
    F.iso.inv.right ≫ eqToHom (congrArg F.functor.obj h.symm) ≫ F.iso.hom.left
  exact absurd (TwoCat.le_of_hom' f) (by decide)

/-- Consequently, every morphism out of a bi-initial `Lexp` is isomorphic to a strict
one. -/
theorem IsBiInitial.exists_strict_iso {A B : Lexp.{v, u}} (hA : IsBiInitial A)
    (F : A ⟶ B) : ∃ G : A ⟶ B, G.IsStrict ∧ Nonempty (F ≅ G) :=
  Lexp.exists_strict_iso F hA.dom_ne_cod

/-- **There is a strict morphism from a bi-initial `Lexp` to any other `Lexp`.**
Bi-initiality gives some morphism `A ⟶ B`; since `A.dom ≠ A.cod`, it is isomorphic to a strict
one.

[Paper, §2.2, Prop. `prop:strictification`], last sentence. -/
theorem IsBiInitial.exists_strict_hom {A : Lexp.{v, u}} (hA : IsBiInitial A)
    (B : Lexp.{v, u}) : ∃ G : A ⟶ B, G.IsStrict := by
  obtain ⟨F⟩ := hA.nonempty_hom B
  obtain ⟨G, hG, -⟩ := Lexp.exists_strict_iso F hA.dom_ne_cod
  exact ⟨G, hG⟩

end Lexp
