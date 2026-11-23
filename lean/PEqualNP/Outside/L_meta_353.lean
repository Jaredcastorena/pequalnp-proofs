import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_353_aux

def A : Fin 7 → Finset (Fin 12) := ![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}]
def B : Fin 7 → Finset (Fin 12) := ![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}]
def hit (X S : Finset (Fin 12)) : Prop := ∃ v ∈ S, v ∈ X

theorem prefix_mono (a b : Fin 7 → Finset (Fin 12))
    (PG RG : Fin 7 → Finset (Fin 7)) (val : Finset (Fin 12) → Fin 7 → Prop)
    (hp : ∀ i, ∀ j ∈ PG i, j < i) (hr : ∀ i, ∀ j ∈ RG i, j < i)
    (hv : ∀ X i, val X i ↔ ((hit X (a i) ∨ ∃ j ∈ PG i, val X j) ∧
      (hit X (b i) ∨ ∃ j ∈ RG i, val X j))) (X Y : Finset (Fin 12)) :
    ∀ n : ℕ, (∀ i : Fin 7, i.val < n → (hit X (a i) → hit Y (a i)) ∧
      (hit X (b i) → hit Y (b i))) → ∀ i : Fin 7, i.val < n → val X i → val Y i := by
  intro n
  induction n with
  | zero => intro hb i hi; omega
  | succ n ih =>
    intro hb i hi hx
    apply (hv Y i).2
    obtain ⟨ha, hb'⟩ := (hv X i).1 hx
    have lower (j : Fin 7) (hj : j < i) : j.val < n := by omega
    have base : ∀ j : Fin 7, j.val < n → (hit X (a j) → hit Y (a j)) ∧
        (hit X (b j) → hit Y (b j)) := fun j hj => hb j (by omega)
    constructor
    · rcases ha with ha | ⟨j, hj, hvj⟩
      · exact Or.inl ((hb i hi).1 ha)
      · exact Or.inr ⟨j, hj, ih base j (lower j (hp i j hj)) hvj⟩
    · rcases hb' with hb' | ⟨j, hj, hvj⟩
      · exact Or.inl ((hb i hi).2 hb')
      · exact Or.inr ⟨j, hj, ih base j (lower j (hr i j hj)) hvj⟩

theorem except_mono (a b : Fin 7 → Finset (Fin 12))
    (PG RG : Fin 7 → Finset (Fin 7)) (val : Finset (Fin 12) → Fin 7 → Prop)
    (hp : ∀ i, ∀ j ∈ PG i, j < i) (hr : ∀ i, ∀ j ∈ RG i, j < i)
    (hv : ∀ X i, val X i ↔ ((hit X (a i) ∨ ∃ j ∈ PG i, val X j) ∧
      (hit X (b i) ∨ ∃ j ∈ RG i, val X j))) (X Y : Finset (Fin 12))
    (k : Fin 7) (hk : val X k → val Y k)
    (hb : ∀ i, i ≠ k → (hit X (a i) → hit Y (a i)) ∧
      (hit X (b i) → hit Y (b i))) : ∀ i, val X i → val Y i := by
  have go : ∀ n : ℕ, ∀ i : Fin 7, i.val < n → val X i → val Y i := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi hx
      by_cases hik : i = k
      · subst i; exact hk hx
      · apply (hv Y i).2
        obtain ⟨ha, hb'⟩ := (hv X i).1 hx
        have lower (j : Fin 7) (hj : j < i) : j.val < n := by omega
        constructor
        · rcases ha with ha | ⟨j, hj, hvj⟩
          · exact Or.inl ((hb i hik).1 ha)
          · exact Or.inr ⟨j, hj, ih j (lower j (hp i j hj)) hvj⟩
        · rcases hb' with hb' | ⟨j, hj, hvj⟩
          · exact Or.inl ((hb i hik).2 hb')
          · exact Or.inr ⟨j, hj, ih j (lower j (hr i j hj)) hvj⟩
  intro i
  exact go 7 i i.isLt

def chosen : Finset (Fin 7) := {2,3,4,6}
def u : Fin 7 → Fin 12 := ![0,0,1,4,6,0,9]
def v : Fin 7 → Fin 12 := ![0,0,2,5,7,0,10]
def p : Fin 7 → Fin 12 := ![0,0,6,7,1,0,2]
def q : Fin 7 → Fin 12 := ![0,0,9,10,4,0,5]
def xp (t : Fin 7) : Finset (Fin 12) := {u t,p t}
def yp (t : Fin 7) : Finset (Fin 12) := {v t,p t}
def xq (t : Fin 7) : Finset (Fin 12) := {u t,q t}
def yq (t : Fin 7) : Finset (Fin 12) := {v t,q t}
def edges : List (Fin 12 × Fin 12) :=
  [(0,1),(0,2),(0,3),(1,2),(1,6),(2,9),(3,4),(3,5),(4,5),(4,7),(5,10),
   (6,7),(6,8),(7,8),(8,11),(9,10),(9,11),(10,11)]
def good (X : Finset (Fin 12)) : Prop := ∃ e ∈ edges, e.1 ∈ X ∧ e.2 ∈ X

set_option maxRecDepth 10000 in
lemma singleton_bad : ∀ x : Fin 12, ¬ good {x} := by
  unfold good
  decide

set_option maxRecDepth 10000 in
lemma pattern : ∀ t ∈ chosen, good (xp t) ∧ ¬ good (yp t) ∧ good (yq t) ∧ ¬ good (xq t) := by
  unfold good
  decide

set_option maxRecDepth 10000 in
lemma column_base : ∀ t ∈ chosen, ∀ s : Fin 7, s ∉ chosen ∨ s = t →
    (hit (xp t) (A s) ↔ hit (xq t) (A s)) ∧
    (hit (xp t) (B s) ↔ hit (xq t) (B s)) := by
  unfold hit
  decide

set_option maxRecDepth 10000 in
lemma row_base : ∀ t ∈ chosen, ∀ s : Fin 7, s ≠ t →
    ((hit (xp t) (A s) ↔ hit (yp t) (A s)) ∧
     (hit (xp t) (B s) ↔ hit (yp t) (B s))) ∧
    ((hit (yq t) (A s) ↔ hit (xq t) (A s)) ∧
     (hit (yq t) (B s) ↔ hit (xq t) (B s))) := by
  unfold hit
  decide

end PEqualNP.Outside.L_meta_353_aux

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_353 : ∀ E : List (Fin 12 × Fin 12), E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 6), (2, 9), (3, 4), (3, 5), (4, 5), (4, 7), (5, 10), (6, 7), (6, 8), (7, 8), (8, 11), (9, 10), (9, 11), (10, 11)] → ∀ (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7)) (OV : Finset (Fin 12)) (OG : Finset (Fin 7)) (val : Finset (Fin 12) → Fin 7 → Prop), (∀ i : Fin 7, ∀ j ∈ PG i, j < i) → (∀ i : Fin 7, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin 12)) (i : Fin 7), val X i ↔ (((∃ v ∈ (![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}] : Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ (![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}] : Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → ¬ ∀ X : Finset (Fin 12), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X := by
  classical
  intro E hE σ PG RG OV OG val hp hr hv hcorrect
  subst E
  let a : Fin 7 → Finset (Fin 12) := fun i => PEqualNP.Outside.L_meta_353_aux.A (σ i)
  let b : Fin 7 → Finset (Fin 12) := fun i => PEqualNP.Outside.L_meta_353_aux.B (σ i)
  have hv' : ∀ X i, val X i ↔ ((PEqualNP.Outside.L_meta_353_aux.hit X (a i) ∨ ∃ j ∈ PG i, val X j) ∧
      (PEqualNP.Outside.L_meta_353_aux.hit X (b i) ∨ ∃ j ∈ RG i, val X j)) := hv
  have hout : ∀ X, (PEqualNP.Outside.L_meta_353_aux.hit X OV ∨ ∃ j ∈ OG, val X j) ↔
      PEqualNP.Outside.L_meta_353_aux.good X := hcorrect
  have hov : OV = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact PEqualNP.Outside.L_meta_353_aux.singleton_bad w
      ((hout {w}).1 (Or.inl ⟨w, hw, by simp⟩))
  have hout' : ∀ X, (∃ j ∈ OG, val X j) ↔ PEqualNP.Outside.L_meta_353_aux.good X := by
    simpa [PEqualNP.Outside.L_meta_353_aux.hit, hov] using hout
  have deliver (X Y : Finset (Fin 12)) (hm : ∀ i, val X i → val Y i)
      (hx : PEqualNP.Outside.L_meta_353_aux.good X) : PEqualNP.Outside.L_meta_353_aux.good Y := by
    obtain ⟨j,hj,hv⟩ := (hout' X).2 hx
    exact (hout' Y).1 ⟨j,hj,hm j hv⟩
  let S : Finset (Fin 7) := Finset.univ.filter (fun i => σ i ∈ PEqualNP.Outside.L_meta_353_aux.chosen)
  have hs : S.Nonempty := by
    refine ⟨σ.symm 2, ?_⟩
    simp [S, PEqualNP.Outside.L_meta_353_aux.chosen]
  let k : Fin 7 := S.min' hs
  have hk : σ k ∈ PEqualNP.Outside.L_meta_353_aux.chosen := by
    have hm := Finset.min'_mem S hs
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have before (i : Fin 7) (hi : i < k) : σ i ∉ PEqualNP.Outside.L_meta_353_aux.chosen := by
    intro hsi
    have hm : i ∈ S := by simp [S,hsi]
    have hki : k ≤ i := Finset.min'_le S i hm
    exact (not_lt_of_ge hki) hi
  have cols : ∀ i : Fin 7, i.val < k.val + 1 →
      (PEqualNP.Outside.L_meta_353_aux.hit (PEqualNP.Outside.L_meta_353_aux.xp (σ k)) (a i) ↔
       PEqualNP.Outside.L_meta_353_aux.hit (PEqualNP.Outside.L_meta_353_aux.xq (σ k)) (a i)) ∧
      (PEqualNP.Outside.L_meta_353_aux.hit (PEqualNP.Outside.L_meta_353_aux.xp (σ k)) (b i) ↔
       PEqualNP.Outside.L_meta_353_aux.hit (PEqualNP.Outside.L_meta_353_aux.xq (σ k)) (b i)) := by
    intro i hi
    apply PEqualNP.Outside.L_meta_353_aux.column_base (σ k) hk (σ i)
    by_cases hik : i = k
    · exact Or.inr (congrArg σ hik)
    · apply Or.inl
      apply before i
      change i.val < k.val
      have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
      omega
  have col : val (PEqualNP.Outside.L_meta_353_aux.xp (σ k)) k →
      val (PEqualNP.Outside.L_meta_353_aux.xq (σ k)) k :=
    PEqualNP.Outside.L_meta_353_aux.prefix_mono a b PG RG val hp hr hv' _ _ (k.val+1)
      (fun i hi => ⟨(cols i hi).1.mp,(cols i hi).2.mp⟩) k (by omega)
  have rows (i : Fin 7) (hi : i ≠ k) :=
    PEqualNP.Outside.L_meta_353_aux.row_base (σ k) hk (σ i) (fun h => hi (σ.injective h))
  have pat := PEqualNP.Outside.L_meta_353_aux.pattern (σ k) hk
  by_cases hc : val (PEqualNP.Outside.L_meta_353_aux.xp (σ k)) k
  · apply pat.2.2.2
    apply deliver (PEqualNP.Outside.L_meta_353_aux.yq (σ k)) (PEqualNP.Outside.L_meta_353_aux.xq (σ k))
    · apply PEqualNP.Outside.L_meta_353_aux.except_mono a b PG RG val hp hr hv' _ _ k
      · exact fun _ => col hc
      · exact fun i hi => ⟨(rows i hi).2.1.mp,(rows i hi).2.2.mp⟩
    · exact pat.2.2.1
  · apply pat.2.1
    apply deliver (PEqualNP.Outside.L_meta_353_aux.xp (σ k)) (PEqualNP.Outside.L_meta_353_aux.yp (σ k))
    · apply PEqualNP.Outside.L_meta_353_aux.except_mono a b PG RG val hp hr hv' _ _ k
      · exact fun h => False.elim (hc h)
      · exact fun i hi => ⟨(rows i hi).1.1.mp,(rows i hi).1.2.mp⟩
    · exact pat.1
