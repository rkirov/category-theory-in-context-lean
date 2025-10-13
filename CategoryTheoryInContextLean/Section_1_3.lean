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

variable {α : Type*} [C : Category α]

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

-- todo: corollary 1.3.10

end CategoryInContext
