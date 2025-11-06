import CategoryTheoryInContextLean.Section_1_1

/-!
# Category Theory in Context - Section 1.2

We introduce the opposite category, monomorphisms and epimorphisms.
Also we define sections, retractions, retracts, split monos and split epis.
We continue to use the custom definition of a category from Section 1.1.
-/

namespace CategoryInContext

open Category

-- need a type synomym the types in the opposite category
-- so that typeclass resolution doesn't get confused
-- by having two instances of Category on the same type.
def Opposite (α : Type*) := α

-- definition 1.2.1
instance Category.opp {α : Type*} [C : Category α] : Category (Opposite α) where
  Hom X Y := C.Hom Y X
  id X := C.id X
  comp f g := C.comp g f
  id_comp := by simp [comp_id]
  comp_id := by simp [id_comp]
  assoc := by simp [← assoc]

-- exmaple 1.2.2.i
def Category.MatR' (α : Type*) [Ring α] : Category ℕ where
  Hom m n := Matrix (Fin m) (Fin n) α
  id := 1
  comp f g := f * g
  id_comp := by simp
  comp_id := by simp
  assoc _ _ _ := by rw [Matrix.mul_assoc]

variable {α : Type*} [C : Category α]

theorem Category.MatR_opp_eq_MatR' [Ring α] : (MatR α).opp = MatR' α := by sorry

-- exmaple 1.2.2.ii
noncomputable instance Category.Poset' (α : Type*) [PartialOrder α] : Category α where
  Hom X Y := PLift (Y ≤ X) -- some universe gymnastics to move between Prop and Type
  id X := ⟨le_refl X⟩
  comp f g := ⟨le_trans g.down f.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem Category.Poset_opp_eq_Poset' [PartialOrder α] : (Poset α).opp = Poset' α := by sorry

-- todo add 1.2.2.iii

-- lemma 1.2.3
lemma Category.iso_equiv {X Y : α} (f : Hom X Y) :
  [ IsIso f,
    ∀ c : α, Function.Bijective (fun g : Hom c X => g ≫ f),
    ∀ c : α, Function.Bijective (fun g : Hom Y c => f ≫ g)
  ].TFAE := by sorry

-- definition 1.2.7
def Category.Mono {X Y : α} (f : Hom X Y) : Prop :=
  ∀ {W} (h k : Hom W X), h ≫ f = k ≫ f → h = k
def Category.Epi {X Y : α} (f : Hom X Y) : Prop :=
  ∀ {Z} (h k : Hom Y Z), f ≫ h = f ≫ k → h = k

lemma Category.mono_op_epi {X Y : α} (f : Hom X Y) :
    Mono f ↔ @Epi (Opposite α) _ Y X f := by
  sorry

lemma Category.epi_op_mono {X Y : α} (f : Hom X Y) :
    Epi f ↔ @Mono (Opposite α) _ Y X f := by
  sorry

-- todo: add support for custom notation: X → Y for Hom X Y and X ↣ Y for {f: Hom X Y // Epi f}
-- and X ↠ Y for {f: Hom X Y // Mono f}

theorem Category.Mono_injection {X Y : α} (f : Hom X Y) (hf : Mono f) :
    ∀ c : α, Function.Injective (fun g : Hom c X => g ≫ f) := by
  intros g1 g2 h
  apply hf

theorem Category.Epi_surjection {X Y : α} (f : Hom X Y) (hf : Epi f) :
    ∀ c : α, Function.Injective (fun g : Hom Y c => f ≫ g) := by
  intros g1 g2 h
  apply hf

-- example 1.2.8
-- note we need to use Category.Hom and not just Hom,
-- because we are not in the namespace Category.
example {X Y : Set α} (f : Category.Hom X Y) (hf : Category.Mono f) :
    Function.Injective f := by sorry
example {X Y : Set α} (f : Category.Hom X Y) (hf : Category.Epi f) :
    Function.Surjective f := by sorry

-- example 1.2.9
def Category.IsSection {X Y : α} (f : Hom X Y) (g : Hom Y X) := f ≫ g = id X 
def Category.IsRetraction {X Y : α} (f : Hom Y X) (g : Hom X Y) := g ≫ f = id X
def Category.IsRetract (X Y : α) := ∃ (f : Hom X Y), ∃ (g : Hom Y X), f ≫ g = id X

alias Category.IsRightInverse := Category.IsSection
alias Category.IsLeftInverse := Category.IsRetraction

theorem Category.section_mono {X Y : α} (f : Hom Y X) (g : Hom X Y) (h : IsSection f g) :
    Mono f := by sorry

theorem Category.retraction_epi {X Y : α} (f : Hom X Y) (g : Hom Y X)
    (h : IsRetraction f g) : Epi f := by sorry

def Category.split_epi {X Y : α} (f : Hom X Y) := ∃ (g : Hom Y X), IsRetraction f g
def Category.split_mono {X Y : α} (f : Hom Y X) := ∃ (g : Hom X Y), IsSection f g

-- example 1.2.10
theorem Category.iso_mono_epi {X Y : α} (f : Hom X Y) (hf : IsIso f) :
    Mono f ∧ Epi f := by sorry

example : ∃ α : Type*, ∃ C : Category α, ∃ X Y : α, ∃ f : C.Hom X Y,
    Category.Mono f ∧ Category.Epi f ∧ ¬Category.IsIso f := by sorry

-- lemma 1.2.11 / exercise 1.2.iii
lemma Category.comp_mono_of_mono_mono {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by sorry
lemma Category.mono_of_comp_mono {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hfg : Mono (f ≫ g)) : Mono f := by sorry
-- use duality tp prove epi versions
lemma Category.comp_epi_of_epi_epi {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) := by sorry
lemma Category.epi_of_comp_epi {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hfg : Epi (f ≫ g)) : Epi g := by sorry

-- -- exercise 1.2.i
def Category.slice_over' (c : α) := @slice_under (Opposite α) (C.opp) c
theorem Category.slice_over_equiv_slice_over' (c : α) :
  slice_over c = slice_over' c := by sorry

-- exercise 1.2.ii.i
theorem Category.split_epi_iff {X Y : α} (f : Hom X Y) :
    split_epi f ↔
    ∀ c : α, Function.Surjective (fun g : Hom Y c => f ≫ g) := by sorry

-- exercise 1.2.ii.ii
theorem Category.split_mono_iff {X Y : α} (f : Hom X Y) :
    split_mono f ↔
    ∀ c : α, Function.Surjective (fun g : Hom c X => g ≫ f) := by sorry

-- final part of exercise 1.2.2
def Category.Subcategory.mono : Subcategory α where
  obj := fun X => True
  hom := fun f => Mono f
  id_mem X := by sorry
  comp_mem hX hY hZ hf hg := by sorry

def Category.Subcategory.epi : Subcategory α where
  obj := fun X => True
  hom := fun f => Epi f
  id_mem X := by sorry
  comp_mem hX hY hZ hf hg := by sorry

-- todo: exercise 1.2.iv, we are missing the category of fields in 1.1 first
-- todo: exercise 1.2.v, need to define category of rings in 1.1 first

-- exercise 1.2.vi
theorem Category.iso_of_mono_and_split_epi {X Y : α} (f : Hom X Y)
    (hm : Mono f) (he : split_epi f) : IsIso f := by sorry

-- prove by duality
theorem Category.iso_of_epi_and_split_mono {X Y : α} (f : Hom X Y)
    (he : Epi f) (hm : split_mono f) : IsIso f := by sorry

-- todo: exercise 1.2.vii

end CategoryInContext
