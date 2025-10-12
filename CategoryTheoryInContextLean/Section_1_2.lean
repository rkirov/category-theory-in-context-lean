import CategoryTheoryInContextLean.Section_1_1
import Mathlib.Tactic.TFAE

namespace CategoryInContext

variable {α : Type*} [C : Category α]

-- definition 1.2.1
def Category.opp (C : Category α) : Category α where
  Hom := fun X Y => C.Hom Y X
  id := fun X => Category.id X
  comp := fun f g => C.comp g f
  id_comp := by simp [Category.comp_id]
  comp_id := by simp [Category.id_comp]
  assoc := by simp [← Category.assoc]

-- exmaple 1.2.2.i
def Category.MatR' (α : Type*) [Ring α] : Category ℕ where
  Hom := fun m n => Matrix (Fin m) (Fin n) α
  id := 1
  comp := fun f g => f * g
  id_comp := by simp
  comp_id := by simp
  assoc := by sorry -- not sure why simp doesn't work here

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
    ∀ c : α, Function.Bijective (fun g : Hom c X => Category.comp g f),
    ∀ c : α, Function.Bijective (fun g : Hom Y c => Category.comp f g)
  ].TFAE := by sorry

-- definition 1.2.7
def Category.Mono {X Y : α} (f : Hom X Y) : Prop :=
  ∀ {W} (h k : Hom W X), Category.comp h f = Category.comp k f → h = k
def Category.Epi {X Y : α} (f : Hom X Y) : Prop :=
  ∀ {Z} (h k : Hom Y Z), Category.comp f h = Category.comp f k → h = k

lemma Category.mono_op_epi {X Y : α} (f : Hom X Y) :
    Category.Mono f ↔ @Category.Epi α (Category.opp C) Y X f := by
  sorry

lemma Category.epi_op_mono {X Y : α} (f : Hom X Y) :
    Category.Epi f ↔ @Category.Mono α (Category.opp C) Y X f := by
  sorry

-- todo: add support for custom notation: X → Y for Hom X Y and X ↣ Y for {f: Hom X Y // Epi f}
-- and X ↠ Y for {f: Hom X Y // Mono f}

theorem Category.Mono_injection {X Y : α} (f : Hom X Y) (hf : Category.Mono f) :
    ∀ c : α, Function.Injective (fun g : Hom c X => Category.comp g f) := by
  intros g1 g2 h
  apply hf

theorem Category.Epi_surjection {X Y : α} (f : Hom X Y) (hf : Category.Epi f) :
    ∀ c : α, Function.Injective (fun g : Hom Y c => Category.comp f g) := by
  intros g1 g2 h
  apply hf

-- example 1.2.8
example {X Y : Set α} (f : Category.Hom X Y) (hf : Category.Mono f) :
    Function.Injective f := by sorry
example {X Y : Set α} (f : Category.Hom X Y) (hf : Category.Epi f) :
    Function.Surjective f := by sorry

-- example 1.2.9
def Category.IsSection {X Y : α} (f : Hom Y X) (g : Hom X Y) := comp g f = id X
def Category.IsRetraction {X Y : α} (f : Hom X Y) (g : Hom Y X) := comp f g = id X
def Category.IsRetract (X Y : α) := ∃ (f : Hom X Y), ∃ (g : Hom Y X), comp f g = id X

alias Category.IsRightInverse := Category.IsSection
alias Category.IsLeftInverse := Category.IsRetraction

theorem Category.section_mono {X Y : α} (f : Hom Y X) (g : Hom X Y) (h : Category.IsSection f g) :
    Category.Mono f := by sorry

theorem Category.retraction_epi {X Y : α} (f : Hom X Y) (g : Hom Y X)
    (h : Category.IsRetraction f g) : Category.Epi f := by sorry

def Category.split_epi {X Y : α} (f : Hom X Y) := ∃ (g : Hom Y X), Category.IsRetraction f g
def Category.split_mono {X Y : α} (f : Hom Y X) := ∃ (g : Hom X Y), Category.IsSection f g

-- example 1.2.10
theorem Category.iso_mono_epi {X Y : α} (f : Hom X Y) (hf : Category.IsIso f) :
    Category.Mono f ∧ Category.Epi f := by sorry

example : ∃ α : Type*, ∃ C : Category α, ∃ X Y : α, ∃ f : C.Hom X Y,
    Category.Mono f ∧ Category.Epi f ∧ ¬Category.IsIso f := by sorry

-- lemma 1.2.11 / exercise 1.2.iii
lemma Category.comp_mono_of_mono_mono {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hf : Category.Mono f) (hg : Category.Mono g) : Category.Mono (comp f g) := by sorry
lemma Category.mono_of_comp_mono {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hfg : Category.Mono (comp f g)) : Category.Mono f := by sorry
-- use duality tp prove epi versions
lemma Category.comp_epi_of_epi_epi {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hf : Category.Epi f) (hg : Category.Epi g) : Category.Epi (comp f g) := by sorry
lemma Category.epi_of_comp_epi {X Y Z : α} (f : Hom X Y) (g : Hom Y Z)
    (hfg : Category.Epi (comp f g)) : Category.Epi g := by sorry

-- exercise 1.2.i
def Category.slice_over' (c : α) : Category (Σ X : α, Hom X c) :=
    opp (@Category.slice_under α (opp C) c)
theorem Category.slice_over_equiv_slice_over' (c : α) :
  Category.slice_over c = Category.slice_over' c := by sorry

-- exercise 1.2.ii.i
theorem Category.split_epi_iff {X Y : α} (f : Hom X Y) :
    Category.split_epi f ↔
    ∀ c : α, Function.Surjective (fun g : Hom Y c => Category.comp f g) := by sorry

-- exercise 1.2.ii.ii
theorem Category.split_mono_iff {X Y : α} (f : Hom X Y) :
    Category.split_mono f ↔
    ∀ c : α, Function.Surjective (fun g : Hom c X => Category.comp g f) := by sorry

-- final part of exercise 1.2.2
def Category.Subcategory.mono : Subcategory α where
  obj := fun X => True
  hom := fun f => Category.Mono f
  id_mem X := by sorry
  comp_mem hX hY hZ hf hg := by sorry

def Category.Subcategory.epi : Subcategory α where
  obj := fun X => True
  hom := fun f => Category.Epi f
  id_mem X := by sorry
  comp_mem hX hY hZ hf hg := by sorry

-- todo: exercise 1.2.iv, we are missing the category of fields in 1.1 first
-- todo: exercise 1.2.v, need to define category of rings in 1.1 first

-- exercise 1.2.vi
theorem Category.iso_of_mono_and_split_epi {X Y : α} (f : Hom X Y)
    (hm : Category.Mono f) (he : Category.split_epi f) : Category.IsIso f := by sorry

-- prove by duality
theorem Category.iso_of_epi_and_split_mono {X Y : α} (f : Hom X Y)
    (he : Category.Epi f) (hm : Category.split_mono f) : Category.IsIso f := by sorry

-- todo: exercise 1.2.vii

end CategoryInContext
