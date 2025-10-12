import Mathlib.Data.Matrix.Mul  -- use #min_imports to update

/-!
# Category Theory in Context - Section 1.1

We introduce the basic definition of a category and examples from different areas of math.
We also define isomorphisms, groupoids and subcategories.
-/

-- to avoid name clash with Mathlib.CategoryTheory.Category
namespace CategoryInContext

/--
A category consists of a collection of objects and morphisms between them.
The morphisms can be composed and there is an identity morphism for each object.
The composition is associative and the identity morphisms act as identities for composition.

Note: We stray slightly from definition in 1.1 by using Hom objects as types, instead
of domain and codomain function out of generic morphism type.

definition 1.1.1
we use α instead of Obj following https://leanprover-community.github.io/contribute/style.html
-/
class Category (α : Type*) where
  -- objects
  Hom : α → α → Type*
  id : (X : α) → Hom X X
  comp : {X Y Z : α} → Hom X Y → Hom Y Z → Hom X Z
  -- propositions / laws
  id_comp : ∀ {X Y : α} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : α} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : α} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)


-- -- not in the book, doesn't work for some universe reason, that I don't understand
-- instance Category.Types : Category (Type u) where
--   Hom := fun X Y => X → Y
--   id := fun X x => x
--   comp := fun f g => g ∘ f
--   id_comp := by intros; rfl
--   comp_id := by intros; rfl
--   assoc := by intros; rfl

-- example 1.1.3.i
-- difference from the book, we use Sets from a fixed Type X, not all sets
instance Category.Sets (α : Type*) : Category (Set α) where
  Hom := fun X Y => X → Y
  id := fun X x => x
  comp := fun f g => g ∘ f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

-- todo: add more examples from mathlib

-- example 1.1.4.i
def Category.MatR (α : Type*) [Ring α] : Category ℕ where
  Hom := fun n m => Matrix (Fin m) (Fin n) α
  id := 1
  comp := fun f g => g * f
  id_comp := by simp
  comp_id := by simp
  assoc := by sorry -- not sure why simp doesn't work here

-- example 1.1.4.ii
def Category.Monoid (α : Type*) [Monoid α] : Category Unit where
  Hom _ _ := α
  id _ := 1
  comp f g := f * g
  id_comp := by simp
  comp_id := by simp
  assoc f g h := mul_assoc f g h

-- example 1.1.4.iii
noncomputable instance Category.Poset (α : Type*) [PartialOrder α] : Category α where
  Hom X Y := PLift (X ≤ Y) -- some universe gymnastics to move between Prop and Type
  id X := ⟨le_refl X⟩
  comp f g := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- example 1.1.4.v
-- slight difference, swap Set with Type, since we are working with type theory in Lean.
def Category.TrivialType (α : Type) : Category α where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- definition 1.1.6 (small categories) and 1.1.7 (locally small categories)
-- not sure if even possible to state in Lean, or what is the
-- right definition when working with type theory instead of set theory as foundation.

variable {α : Type*} [Category α]

-- definition 1.1.9
-- we defined structure and a prop separate, as they might be useful separately
structure Category.Isomorphism (X Y : α) where
  f : Hom X Y
  inv : Hom Y X
  hom_inv_id : comp f inv = id X
  inv_hom_id : comp inv f = id Y

def Category.id_iso (X : α) : Category.Isomorphism X X :=
  { f := Category.id X
    inv := Category.id X
    hom_inv_id := by rw [Category.id_comp]
    inv_hom_id := by rw [Category.comp_id] }

def Category.IsIso {X Y : α} (f : Hom X Y) : Prop :=
  ∃ g : Hom Y X, comp f g = id X ∧ comp g f = id Y

lemma Category.iso_iff_isIso {X Y : α} (f : Hom X Y) :
  Category.IsIso f ↔ ∃ (iso : Category.Isomorphism X Y), iso.f = f := by
  constructor
  · rintro ⟨g, hg, hf⟩
    use Category.Isomorphism.mk f g hg hf
  · rintro ⟨⟨f, g, hg, hf⟩, rfl⟩
    exact ⟨g, hg, hf⟩

def Category.Isomorphic (X Y : α) := Inhabited (Isomorphism X Y)

def Category.Endomorphism (X : α) := Hom X X
def Category.Automorphism (X : α) := Isomorphism X X

-- example 1.1.10
-- todo: add more examples from mathlib
-- example 1.1.10.v
lemma Category.poset_trivial (α : Type) [PartialOrder α] [Category α] (X Y : α) (f : Hom X Y) :
  Category.IsIso f ↔ X = Y := by
  constructor
  ·  sorry
  · intro h
    subst X
    rw [iso_iff_isIso]
    use id_iso Y
    sorry -- use the fact that Hom Y Y is a single element type since it was a lift of a Prop

-- definition 1.1.11
def Category.Groupoid (α : Type*) [Category α] :=
  ∀ {X Y : α} (f : Hom X Y), Category.IsIso f

-- example 1.1.12.i
def Category.group_groupoid (α : Type*) [Group α] :
  @Category.Groupoid Unit (Category.Monoid α) := by
  intro X Y f
  unfold Category.IsIso
  use (f⁻¹ : α) -- explict cast needed for some reason
  simp [Category.Monoid]

-- definition 1.1.13
-- again because of type theory foundations, we define subcategory as a map to Prop
structure Category.Subcategory (α : Type*) [Category α] where
  obj : α → Prop
  hom : {X Y : α} → Hom X Y → Prop
  id_mem : ∀ {X}, obj X → hom (Category.id X)
  comp_mem : ∀ {X Y Z} {f : Hom X Y} {g : Hom Y Z},
    obj X → obj Y → obj Z → hom f → hom g → hom (Category.comp f g)

-- Define subset relation between subcategories as Prop implication
def Category.Subcategory.subset {α : Type*} [Category α] (S T : Subcategory α) : Prop :=
  (∀ X, S.obj X → T.obj X) ∧
  (∀ {X Y} (f : Hom X Y), S.hom f → T.hom f)

-- Overload ⊆ notation
instance {α : Type*} [Category α] : HasSubset (Category.Subcategory α) where
  Subset := Category.Subcategory.subset

-- not in the book
def Category.full_subcategory (α : Type*) [Category α] : Subcategory α where
  obj := fun _ => True
  hom := fun _ => True
  id_mem _ := trivial
  comp_mem _ _ _ _ _ := trivial

def Category.empty_subcategory (α : Type*) [Category α] : Subcategory α where
  obj := fun X => False
  hom := fun f => False
  id_mem := by intros; contradiction
  comp_mem := by intros; contradiction

lemma Category.empty_subcategory_subset {α : Type*} [Category α] :
  empty_subcategory α ⊆ full_subcategory α := by
  constructor
  · intro X h; contradiction
  · intros X Y f h; contradiction

-- lemma 1.1.13 and exercise 1.1.ii
def Category.maximal_subgroupoid {α : Type*} [Category α] : Subcategory α where
  obj := fun X => True
  hom := fun f => Category.IsIso f
  id_mem x := by sorry
  comp_mem _ _ _ hf hg := by sorry

-- exercise 1.1.i
theorem Category.pair_inverse_iso {X Y : α} (f : Hom X Y) (g : Hom Y X) (h : Hom Y X)
  (hg : comp f g = id X) (hf : comp h f = id Y) : g = h ∧ IsIso f := by sorry

-- exercise 1.1.iii.i
def Category.slice_under (c : α) : Category (Σ X : α, Hom c X) where
  Hom := fun ⟨X, f⟩ ⟨Y, g⟩ => {h : Hom X Y // comp f h = g}
  id := fun ⟨X, f⟩ => ⟨Category.id X, by rw [Category.comp_id]⟩
  comp := fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨ comp k l, by
      rw [← Category.assoc]
      rw [hk, hl]
    ⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

def Category.slice_over (c : α) : Category (Σ X : α, Hom X c) where
  Hom := fun ⟨X, f⟩ ⟨Y, g⟩ => {h : Hom X Y // comp h g = f}
  id := fun ⟨X, f⟩ => ⟨Category.id X, by rw [Category.id_comp]⟩
  comp := fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨ comp k l, by
      rw [Category.assoc]
      rw [hl, hk]
    ⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

end CategoryInContext
