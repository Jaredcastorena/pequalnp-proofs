import Mathlib

namespace Case27SecondCollision

abbrev Vert := Fin 7
abbrev Input := Finset Vert

def hub (U : Input) : Prop := 0 ∈ U ∨ 1 ∈ U

def form (A : Input) (b : Bool) (U : Input) : Prop :=
  A ⊆ U ∧ (b = false ∨ hub U)

def centralFree (A : Input) : Prop :=
  ¬ ({0,1} : Input) ⊆ A ∧ ¬ ({0,2} : Input) ⊆ A ∧ ¬ ({1,2} : Input) ⊆ A

def leForm (A : Input) (b : Bool) (B : Input) (c : Bool) : Prop :=
  if b then form B c (A ∪ {0}) ∧ form B c (A ∪ {1}) else form B c A

def bit (A : Input) (b : Bool) (B : Input) (c : Bool) (U : Input) : Prop :=
  form A b U ∨ form B c U

def sameHub (A : Input) (b : Bool) (B : Input) (c : Bool) : Prop :=
  leForm A b ∅ true ∧ leForm B c ∅ true ∧ bit A b B c {0} ∧ bit A b B c {1}

abbrev edge (U : Input) : Prop :=
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨
  (0 ∈ U ∧ 4 ∈ U) ∨ (1 ∈ U ∧ 2 ∈ U) ∨ (1 ∈ U ∧ 5 ∈ U) ∨
  (1 ∈ U ∧ 6 ∈ U) ∨ (3 ∈ U ∧ 4 ∈ U) ∨ (5 ∈ U ∧ 6 ∈ U)

def pool : List Input := [{0},{1},{0,2},{1,2},{3},{0,3},{1,3},{2,3},{4},{0,4},{1,4},{2,4},{3,4},{1,3,4},{5},{0,5},{1,5},{2,5},{6},{0,6},{1,6},{2,6},{5,6},{0,5,6}]
def pick (i : Fin 24) : Input := pool.getD i.val ∅

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 40000 in
theorem small_certificate : ∀ A B : Input, ∀ b c : Bool,
    centralFree A → centralFree B → ¬ leForm A b B c → ¬ leForm B c A b →
    ¬ sameHub A b B c → ∃ u v : Fin 24,
      pick u \ ((A ∪ B) ∩ {2,3,4,5,6}) = pick v \ ((A ∪ B) ∩ {2,3,4,5,6}) ∧
      (bit A b B c (pick u) ↔ bit A b B c (pick v)) ∧
      ¬ (edge (pick u) ↔ edge (pick v)) := by
  unfold centralFree sameHub leForm bit form hub edge pick pool
  decide +kernel

#print axioms small_certificate
theorem form_mono {A U V : Input} {b : Bool} (huv : U ⊆ V) :
    form A b U → form A b V := by
  rintro ⟨hA, hb | hU⟩
  · exact ⟨Finset.Subset.trans hA huv, Or.inl hb⟩
  · refine ⟨Finset.Subset.trans hA huv, Or.inr ?_⟩
    exact hU.elim (fun h => Or.inl (huv h)) (fun h => Or.inr (huv h))

theorem bit_mono {A B U V : Input} {b c : Bool} (huv : U ⊆ V) :
    bit A b B c U → bit A b B c V := by
  exact Or.imp (form_mono huv) (form_mono huv)

theorem leForm_iff (A B : Input) (b c : Bool) :
    leForm A b B c ↔ ∀ U, form A b U → form B c U := by
  cases b with
  | false =>
    change form B c A ↔ ∀ U, form A false U → form B c U
    constructor
    · intro h U hU
      exact form_mono hU.1 h
    · intro h
      exact h A (by simp [form])
  | true =>
    change (form B c (A ∪ {0}) ∧ form B c (A ∪ {1})) ↔
      ∀ U, form A true U → form B c U
    constructor
    · rintro ⟨h0,h1⟩ U ⟨hAU,hU⟩
      have hhub : hub U := hU.resolve_left (by decide)
      rcases hhub with h0U | h1U
      · exact form_mono (Finset.union_subset hAU (by simpa using h0U)) h0
      · exact form_mono (Finset.union_subset hAU (by simpa using h1U)) h1
    · intro h
      constructor
      · exact h (A ∪ {0}) (by simp [form,hub])
      · exact h (A ∪ {1}) (by simp [form,hub])

theorem empty_true_form (U : Input) : form ∅ true U ↔ hub U := by
  simp [form]

theorem sameHub_iff (A B : Input) (b c : Bool) :
    sameHub A b B c ↔ ∀ U, bit A b B c U ↔ hub U := by
  constructor
  · rintro ⟨hA,hB,h0,h1⟩ U
    constructor
    · rintro (h | h)
      · exact (empty_true_form U).mp ((leForm_iff A ∅ b true).mp hA U h)
      · exact (empty_true_form U).mp ((leForm_iff B ∅ c true).mp hB U h)
    · rintro (h | h)
      · exact bit_mono (by simpa using h : ({0} : Input) ⊆ U) h0
      · exact bit_mono (by simpa using h : ({1} : Input) ⊆ U) h1
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · apply (leForm_iff A ∅ b true).mpr
      intro U hU
      exact (empty_true_form U).mpr ((h U).mp (Or.inl hU))
    · apply (leForm_iff B ∅ c true).mpr
      intro U hU
      exact (empty_true_form U).mpr ((h U).mp (Or.inr hU))
    · exact (h {0}).mpr (by simp [hub])
    · exact (h {1}).mpr (by simp [hub])

def noCentral (A : Input) (b : Bool) : Prop :=
  ¬ (∀ U, form A b U → 0 ∈ U ∧ 1 ∈ U) ∧
  ¬ (∀ U, form A b U → 0 ∈ U ∧ 2 ∈ U) ∧
  ¬ (∀ U, form A b U → 1 ∈ U ∧ 2 ∈ U)

theorem pair_dominated {A : Input} {b : Bool} {p q : Vert}
    (hpq : ({p,q} : Input) ⊆ A) : ∀ U, form A b U → p ∈ U ∧ q ∈ U := by
  intro U hU
  have h := Finset.Subset.trans hpq hU.1
  exact ⟨h (by simp),h (by simp)⟩

theorem centralFree_of_noCentral (A : Input) (b : Bool) (h : noCentral A b) :
    centralFree A := by
  refine ⟨fun hA => h.1 (pair_dominated hA), fun hA => h.2.1 (pair_dominated hA),
    fun hA => h.2.2 (pair_dominated hA)⟩

#print axioms leForm_iff
#print axioms sameHub_iff
#print axioms centralFree_of_noCentral

/-- Semantic collision certificate for a second OR after h=x0 OR x1. -/
theorem second_collision_sets (A B : Input) (b c : Bool)
    (hA : noCentral A b) (hB : noCentral B c)
    (hab : ¬ (∀ U, form A b U → form B c U))
    (hba : ¬ (∀ U, form B c U → form A b U))
    (hnew : ¬ (∀ U, bit A b B c U ↔ hub U)) :
    ∃ U V : Input,
      U \ ((A ∪ B) ∩ {2,3,4,5,6}) = V \ ((A ∪ B) ∩ {2,3,4,5,6}) ∧
      (bit A b B c U ↔ bit A b B c V) ∧ ¬ (edge U ↔ edge V) := by
  have ha := centralFree_of_noCentral A b hA
  have hb := centralFree_of_noCentral B c hB
  have hab' : ¬ leForm A b B c := fun h => hab ((leForm_iff A B b c).mp h)
  have hba' : ¬ leForm B c A b := fun h => hba ((leForm_iff B A c b).mp h)
  have hnew' : ¬ sameHub A b B c := fun h => hnew ((sameHub_iff A B b c).mp h)
  obtain ⟨u,v,h⟩ := small_certificate A B b c ha hb hab' hba' hnew'
  exact ⟨pick u,pick v,h⟩

theorem second_collision (A B : Input) (b c : Bool)
    (hA : noCentral A b) (hB : noCentral B c)
    (hab : ¬ (∀ U, form A b U → form B c U))
    (hba : ¬ (∀ U, form B c U → form A b U))
    (hnew : ¬ (∀ U, bit A b B c U ↔ hub U)) :
    ∃ U V : Input,
      (∀ p, p ∉ (A ∪ B) ∩ {2,3,4,5,6} → (p ∈ U ↔ p ∈ V)) ∧
      (bit A b B c U ↔ bit A b B c V) ∧ ¬ (edge U ↔ edge V) := by
  obtain ⟨U,V,hd,hbit,hneq⟩ := second_collision_sets A B b c hA hB hab hba hnew
  refine ⟨U,V,?_,hbit,hneq⟩
  intro p hp
  have hh := congrArg (fun S : Input => p ∈ S) hd
  simpa [Finset.mem_sdiff,hp] using iff_of_eq hh

#print axioms second_collision_sets
#print axioms second_collision
end Case27SecondCollision
