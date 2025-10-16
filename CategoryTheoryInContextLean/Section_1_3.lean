import CategoryTheoryInContextLean.Section_1_1
import CategoryTheoryInContextLean.Section_1_2

/-!
# Category Theory in Context - Section 1.3

We introduce functors, contravariant functors and the category of small categories.
We continue to use the custom definition of a category from Section 1.1.

-/

namespace CategoryInContext

open Category

-- definition 1.3.1
class Functor (α β : Type*) [C : Category α] [D : Category β] where
  -- data
  -- map on objects
  F : α → β
  -- map on morphisms
  homF {X Y : α} : C.Hom X Y → D.Hom (F X) (F Y)
  -- properties / laws
  -- need to qualify id to avoid clash with id in root namespace.
  map_id (X : α) : homF (id X) = Category.id (F X)
  map_comp {X Y Z : α} (f : C.Hom X Y) (g : C.Hom Y Z) :
    homF (f ≫ g) = homF f ≫ homF g

def EndoFunctor (α : Type*) [Category α] := @Functor α α

-- examples 1.3.2.i
def PowerSetFunctor : Functor Type Type where
  F X := Set X
  homF f := Set.image f
  map_id X := by
    simp [Category.id]
    funext x
    simp only [Set.image_id']
  map_comp f g := by
    simp [Category.comp]
    funext x
    simp only [Function.comp_apply]
    exact Eq.symm (Set.image_image g f x)

-- todo: add 1.3.2.ii-xi, once we have appropriate categories defined
-- todo: add theorem 1.3.3

-- definition 1.3.5
class ContraFunctor (α β : Type*) [C : Category α] [D : Category β] where
  -- data
  -- map on objects
  F : α → β
  -- map on morphisms
  homF {X Y : α} : C.Hom X Y → D.Hom (F Y) (F X)
  -- properties / laws
  -- need to qualify id to avoid clash with id in root namespace.
  map_id (X : α) : homF (id X) = Category.id (F X)
  map_comp {X Y Z : α} (f : C.Hom X Y) (g : C.Hom Y Z) :
    homF (f ≫ g) = homF g ≫ homF f

-- example 1.3.7.i
def PowerSetContraFunctor : ContraFunctor Type Type where
  F X := Set X
  homF f := Set.preimage f
  map_id X := by
    simp [Category.id]
    funext x
    simp only [Set.preimage_id']
  map_comp f g := by
    simp [Category.comp]
    funext x
    simp only [Function.comp_apply]
    rfl

-- todo: add 1.3.7.ii-vi, once we have appropriate categories defined

-- lemma 1.3.8
theorem Functor.iso_preserve {α β : Type*} [C : Category α] [D : Category β]
    (F : Functor α β) {X Y : α} (f : C.Hom X Y) (hf : IsIso f) :
    IsIso (F.homF f) := by
  rw [iso_iff_isIso] at hf
  obtain ⟨⟨f, g, hg, hf⟩, rfl⟩ := hf
  use F.homF g
  simp only
  constructor
  · rw [← F.map_comp]
    rw [hg]
    rw [F.map_id]
  · rw [← F.map_comp]
    rw [hf]
    rw [F.map_id]

-- example 1.3.9
def g_set_left_action (α : Type*) [Group α] (β : Type*) :
  @Functor Unit (Set β) (Category.Monoid α) _ := by sorry

def g_set_right_action (α : Type*) [Group α] (β : Type*) :
  @ContraFunctor Unit (Set β) (Category.Monoid α) _ := by sorry

-- todo: corollary 1.3.10, we haven't defined ⁻¹ on isomorphisms yet

-- definition 1.3.11 / exercise 1.3.iv
def Hom_c_? (α : Type*) [Category α] (c : α) : Functor α Type where
  F Y := Hom c Y
  homF {Y Z : α} (f : Hom Y Z) (g : Hom c Y) := g ≫ f
  map_id Y := by sorry
  map_comp {Y Z W : α} (f : Hom Y Z) (g : Hom Z W) := by sorry

def Hom_?_c (α : Type*) [Category α] (c : α) : ContraFunctor α Type where
  F X := Hom X c
  homF {X Y : α} (f: Hom X Y) (g : Hom Y c) := f ≫ g
  map_id X := by sorry
  map_comp {X Y Z : α} (f : Hom X Y) (g : Hom Y Z) := by sorry

-- definition 1.3.12
instance CatProduct {α β : Type*} [C : Category α] [D : Category β] : Category (Prod α β) where
  Hom X Y := (C.Hom X.1 Y.1) × (D.Hom X.2 Y.2)
  id X := (id X.1, id X.2)
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp _ := by repeat rw [id_comp]
  comp_id _ := by repeat rw [comp_id]
  assoc _ _ _ := by repeat rw [assoc]

/--
A functor from the product category (bifunctor) to another category gives
rise to functors from each factor category to the target category when
fixing an object in the other factor.

this is not proved in the book, but it is easy to prove and useful
-/
def prod_functor_functorial_1 {α β γ : Type*} [C : Category α] [D : Category β]
    [Inhabited β] [E : Category γ] (F : Functor (Prod α β) γ) : Functor α γ where
  F := fun X => F.F (X, default)
  homF := fun {X Y} f => F.homF (f, id default)
  map_id X := by
    rw [← F.map_id]
    congr
  map_comp f g := by
    rw [← F.map_comp]
    congr
    rw [id_comp]

def prod_functor_functorial_2 {α β γ : Type*} [C : Category α] [D : Category β]
    [Inhabited α] [E : Category γ] (F : Functor (Prod α β) γ) : Functor β γ where
  -- todo: find a clever way to prove using prod_functor_functorial_1
  F := fun Y => F.F (default, Y)
  homF := fun {Y Z} f => F.homF (id default, f)
  map_id Y := by
    rw [← F.map_id]
    congr
  map_comp f g := by
    rw [← F.map_comp]
    congr
    rw [comp_id]

-- definition 1.3.13
def Hom_bifunctor (α : Type*) [C : Category α] : Functor (Prod (Opposite α) α) Type where
  -- without the C. qualification Lean picks up C.opp.Hom and hilarity ensues
  F X := C.Hom X.1 X.2
  homF {X Y} f g := f.1 ≫ g ≫ f.2
  map_id X := by
    funext g
    simp [Category.id]
    rw [id_comp]
    rw [comp_id]
  map_comp f g := by
    funext h
    simp [comp]
    repeat rw [assoc]

-- Category of small (and locally small) categories, which is locally small but not small.
-- A small category is a category whose objects form a set, which in Lean we take
-- to mean a Type in some universe. Large categories are not expressable in Lean
-- as they would lead to inconsistencies.
-- objects are pairs (α, C) where α is a Type and C is a Category structure on α
-- categories need two universes, one for objects and one for morphisms.
def Cat.{u, v} : Type (max (u+1) (v+1)) :=
  Σ (α : Type u), Category.{u, v} α

universe u v
instance : Category Cat.{u, v} where
  Hom C D := @Functor C.1 D.1 C.2 D.2
  -- adding explicit letI to help typeclass resolution as suggested by Claude.
  id C := letI := C.2; {
    F x := x
    homF f := f
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  comp {C D E} F G := letI := C.2; letI := D.2; letI := E.2; {
    F x := G.F (F.F x)
    homF f := G.homF (F.homF f)
    map_id X := by simp [F.map_id, G.map_id]
    map_comp f g := by simp [F.map_comp, G.map_comp]
  }
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

def Category.CatIsomorphism (C D : Cat) := Isomorphism C.1 D.1
def Category.CatIsomorphic (C D : Cat) := Isomorphic C.1 D.1

-- example 1.3.14.i
def Op : Functor Cat Cat where
  F C := ⟨Opposite C.1, @Category.opp (Opposite C.1) C.2⟩
  homF {C D} F := letI := C.2; letI := D.2; {
    F := F.F
    homF := F.homF
    map_id X := F.map_id X
    map_comp f g := by
      rw [Functor.homF]
      repeat rw [comp]
      simp only
      apply F.map_comp
  }
  map_id C := by sorry
  map_comp {C D E} F G := by sorry

-- todo: add rest of examples from 1.3.14
-- todo: add example 1.3.15
-- todo: add example of sets with partial functions and
-- pointed sets

-- exercise 1.3.i
-- the answer to what is a group homomorphism, but you need to
-- provide the proof.
theorem group_cat_functor {α β: Type*} [Group α] [Group β]
    (F : @Functor Unit Unit (Category.Monoid α) (Category.Monoid β)) :
    ∃ f: α →* β, ∀ x: α, F.homF (X := ()) (Y := ()) x = f x := by sorry

-- exercise 1.3.ii
-- we didn't define the category of preorders in section 1.1, so we do it here
noncomputable instance Category.Preorder (α : Type*) [Preorder α] : Category α where
  Hom X Y := PLift (X ≤ Y) -- some universe gymnastics to move between Prop and Type
  id X := ⟨le_refl X⟩
  comp f g := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem preorder_cat_functor {α β: Type*} [Preorder α] [Preorder β]
    (F : Functor α β) :
    ∃ f: α → β, (Monotone f ∧ ∀ x: α, F.F x = f x) := by sorry

-- exercise 1.3.ii
-- because we can't construct the subcategory from the image, we realize
-- the definition of a subcategory have only two properties:
-- closed under identities and closed under composition.
-- and closed under identity is automatic for the image of a functor.
-- -- so we just need to show not closed under composition.
--
-- can't get the statement to compile, leaving as a comment
-- theorem not_subgroup : ∃ α β : Type*, ∃ C : Category α, ∃ D : Category β,
--     ∃ F : Functor α β, ∃ X Y Z : F.F '' Set.univ, ∃ f: D.Hom X Y, ∃ g: D.Hom Y Z,
--     ∃ f', f' = F.homF ∧ ∃ g', g' = F.homF ∧ ¬ ∃ h', (f ≫ g = F.homF h') := by sorry

-- exercise 1.3.v - can't formalize a question that start with "what"

-- exercise 1.3.vi
-- using exercise notation, instead of mathlib style
instance Comma_category {D C E : Type*} [CC : Category C] [CD : Category D] [CE : Category E]
    (F : Functor D C) (G : Functor E C) :
    Category (Σ (d : D) (e : E), Category.Hom (F.F d) (G.F e)) where

  Hom := fun ⟨d, e, f⟩ ⟨d', e', f'⟩ =>
    {hk : (CD.Hom d d' × CE.Hom e e') // (F.homF hk.1) ≫ f' = f ≫ (G.homF hk.2)}

  id := fun ⟨d, e, f⟩ => ⟨(id d, id e), by
    simp only
    rw [F.map_id, G.map_id]
    rw [id_comp, comp_id]
  ⟩

  comp := fun ⟨f, hf⟩ ⟨f', hf'⟩ => ⟨(f.1 ≫ f'.1, f.2 ≫ f'.2), by
    rw [Functor.map_comp, Functor.map_comp]
    rw [Category.assoc]
    rw [hf']
    rw [← Category.assoc]
    rw [hf]
    rw [Category.assoc]
  ⟩

  id_comp := sorry
  comp_id := sorry
  assoc := sorry

--todo: how to refactor the comma category type to avoid spelling it out.
def Comma_category_dom {D C E : Type*} [CC : Category C] [CD : Category D] [CE : Category E]
    (F : Functor D C) (G : Functor E C) :
    Functor (Σ (d : D) (e : E), Category.Hom (F.F d) (G.F e)) D where
  F := fun ⟨X, _, _⟩ => X
  homF := fun ⟨hk, _⟩ => hk.1
  map_id X := by sorry
  map_comp f g := by sorry

def Comma_category_cod {D C E : Type*} [CC : Category C] [CD : Category D] [CE : Category E]
    (F : Functor D C) (G : Functor E C) :
    Functor (Σ (d : D) (e : E), Category.Hom (F.F d) (G.F e)) E where
  F := fun ⟨_, Y, _⟩ => Y
  homF := fun ⟨hk, _⟩ => hk.2
  map_id X := by sorry
  map_comp f g := by sorry

-- exercise 1.3.vii
section Exercise_1_3_vii
variable {D C E : Type*} [CC : Category C] [CD : Category D] [CE : Category E]

def slice_over_F (c : C) : Functor D C := by sorry
def slice_over_G (c : C) : Functor E C := by sorry
def slice_over_comma_cat (c : C) := @Comma_category D C E CC CD CE
  (slice_over_F c) (slice_over_G c)

-- todo: fix the universes error here
-- theorem slice_over_equiv_comma_category (c : C) :
--   CatIsomorphic
--   ⟨_, slice_over_comma_cat c⟩
--   ⟨_, slice_over c⟩ := by sorry

def slice_under_F (c : C) : Functor D C := by sorry
def slice_under_G (c : C) : Functor E C := by sorry
def slice_under_comma_cat (c : C) := @Comma_category D C E CC CD CE
  (slice_under_F c) (slice_under_G c)

-- todo: fix the universes error here
-- theorem slice_under_equiv_comma_category (c : C) :
--   CatIsomorphic
--   ⟨_, slice_under_comma_cat c⟩
--   ⟨_, slice_under c⟩ := by sorry
end Exercise_1_3_vii

-- exercise 1.3.viii
example : ∃ α β: Type*, ∃ C: Category α, ∃ D: Category β,
    ∃ F : Functor α β, ∃ X Y: α, ∃ f: C.Hom X Y, ¬ IsIso f ∧ IsIso (F.homF f) := by sorry

-- exercise 1.3.ix and 1.3.x
-- todo: mathlib has a definition of center, commutator, and automorphisms, but
-- we haven't defined the category of groups.

end CategoryInContext
