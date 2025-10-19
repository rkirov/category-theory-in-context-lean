import CategoryTheoryInContextLean.Section_1_1
import CategoryTheoryInContextLean.Section_1_2
import CategoryTheoryInContextLean.Section_1_3

/-!
# Category Theory in Context - Section 1.4

We introduce natural transformations.

We continue to use the custom definition of a category, functor, etc, from Chapter 1.
-/

namespace CategoryInContext
open Category

-- definition 1.4.1
class NaturalTransformation {α β : Type*} [C : Category α] [D : Category β]
    (F G : Functor α β) where
  arrow : (X : α) → D.Hom (F.F X) (G.F X)
  naturality : ∀ {X Y : α} (f : C.Hom X Y),
    arrow X ≫ G.homF f = F.homF f ≫ arrow Y

def IsNatIso {α β : Type*} [C : Category α] [D : Category β]
    {F G : Functor α β} (η : NaturalTransformation F G) : Prop :=
  ∀ (X : α), IsIso (η.arrow X)

-- example 1.4.3iii
def NatTrans_Id_PowerSet : NaturalTransformation IdFunctor PowerSetFunctor where
  arrow X := fun x => ({x} : Set X)
  naturality {X Y} f := by
    funext x
    simp only [Category.comp, Function.comp_apply, IdFunctor, PowerSetFunctor]
    rw [Set.image]
    simp

-- todo: add more examples from 1.4.3
-- todo: add examples 1.4.4-6

-- example 1.4.7
def NatTrans_Hom_c_?_Hom_?_c {α : Type*} [C : Category α] (c d : α) (h : Hom c d) :
    NaturalTransformation (Hom_c_? d) (Hom_c_? c) where
  arrow X := fun f => h ≫ f
  naturality {X Y} f := by
    funext g
    simp only [Category.comp, Function.comp_apply, Hom_c_?]
    rw [assoc]

-- technically we haven't defined natural transformations for contravariant functors.
-- def NatTrans_Hom_?_c_Hom_c_? {α : Type*} [C : Category α] (c d : α) (h : Hom c d) :
--     NaturalTransformation (Hom_?_c d) (Hom_?_c c) where

-- todo: add example 1.4.8
-- exercise 1.4.i
noncomputable def NatIso_inverse {α β : Type*} [C : Category α] [D : Category β]
    {F G : Functor α β} (η : NaturalTransformation F G) (h : IsNatIso η) :
    NaturalTransformation G F where
  arrow X := by
    have := h X
    rw [iso_iff_isIso] at this
    choose f hf using this
    exact f.inv

  naturality {X Y} f := by
    sorry

theorem NatIso_inverse_isNatIso {α β : Type*} [C : Category α] [D : Category β]
    {F G : Functor α β} (η : NaturalTransformation F G) (h : IsNatIso η) :
    IsNatIso (NatIso_inverse η h) := by sorry

-- todo: exercise 1.4.ii, iii - are "what" problems formalizable in Lean?

-- exercise 1.4.iv
theorem NatTrans_Hom_c_?_Hom_?_c_distinct {α : Type*} [C : Category α] (c d : α)
    (h1 h2 : Hom c d) (h : h1 ≠ h2) :
    NatTrans_Hom_c_?_Hom_?_c c d h1 ≠ NatTrans_Hom_c_?_Hom_?_c c d h2 := by sorry

-- exercise 1.4.v
-- Natural transformation from G ∘ π₂ to F ∘ π₁ for comma category (F ↓ G)
def Comma_NatTrans {C D E : Type*} [CC : Category C] [CD : Category D] [CE : Category E]
    (F : Functor D C) (G : Functor E C) :
    let CommaType := Σ (d : D) (e : E), Category.Hom (F.F d) (G.F e)
    letI : Category CommaType := Comma_category F G
    NaturalTransformation
      (Functor.comp (Comma_category_cod F G) G)
      (Functor.comp (Comma_category_dom F G) F) where
  arrow X := sorry
  naturality {X Y} f := by sorry

-- exercise 1.4.vi
class ExtraNatrualTransformation {α β γ δ : Type*} [Category α] [Category β] [Category γ]
    [Category δ] (F : Functor (α × β × Opposite β) δ) (G : Functor (α × γ × Opposite γ) δ) where

  arrow : (a : α) → (b : β) → (c : γ) → Hom (F.F (a, b, b)) (G.F (a, c, c))

  lhs_prop {a a': α} {b : β} {c: γ} (f: Hom a a') :
    (arrow a b c) ≫ G.homF (f, id c, id c) = F.homF (f, id b, id b) ≫ (arrow a' b c)

  -- type cast needed to avoid a mysterious error
  mid_prop {a : α} {b b' : β} {c : γ} (g : Hom b b') :
    F.homF (id a, g, id b') ≫ (arrow a b' c) = F.homF ((id a, id b, g) :
      @Category.Hom (α × β × Opposite β) _ (a, b, b') (a, b, b)) ≫ (arrow a b c)

  -- type cast needed to avoid a mysterious error
  rhs_prop {a : α} {b : β} {c c' : γ} (h : Hom c c') :
    arrow a b c ≫ G.homF (id a, h, id c) = arrow a b c' ≫ G.homF ((id a, id c', h) :
      @Category.Hom (α × γ × Opposite γ) _ (a, c', c') (a, c', c))

end CategoryInContext
