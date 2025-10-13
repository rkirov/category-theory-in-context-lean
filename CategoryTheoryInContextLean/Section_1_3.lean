import CategoryTheoryInContextLean.Section_1_1
import CategoryTheoryInContextLean.Section_1_2

/-!
# Category Theory in Context - Section 1.3

We introduce functors

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

-- definition 1.3.11
def Hom_c_? (α : Type*) [Category α] (c : α) : Functor α Type where
  F Y := Hom c Y
  homF {Y Z : α} (f : Hom Y Z) (g : Hom c Y) := g ≫ f
  map_id Y := by
    funext g
    simp [Category.id]
    rw [comp_id]
  map_comp {Y Z W : α} (f : Hom Y Z) (g : Hom Z W) := by
    funext h
    simp [comp]
    rw [assoc]

def Hom_?_c (α : Type*) [Category α] (c : α) : ContraFunctor α Type where
  F X := Hom X c
  homF {X Y : α} (f: Hom X Y) (g : Hom Y c) := f ≫ g
  map_id X := by
    funext g
    simp [Category.id]
    rw [id_comp]
  map_comp {X Y Z : α} (f : Hom X Y) (g : Hom Y Z) := by
    funext h
    simp [comp]
    rw [assoc]

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

-- definition 1.3.13 WIP
-- def Hom_bifunctor (α : Type*) [C: Category α] :
--   @Functor (Prod α α) Type (@CatProduct α α C.opp C) _ where sorry

end CategoryInContext
