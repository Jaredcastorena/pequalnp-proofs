import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_982_aux.Base

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p

    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)





theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def rows1004 : List ℕ := [10, 9, 9, 34, 9, 10, 4, 17, 34, 10, 4, 33, 36, 32, 32, 4, 36, 9, 1, 2, 2, 0, 1, 0, 10, 9, 9, 18, 9, 10, 4, 33, 18, 10, 4, 17, 20, 16, 16, 4, 20, 9, 1, 2, 2, 0, 1, 0, 9, 10, 10, 33, 10, 9, 4, 18, 33, 9, 4, 34, 36, 32, 32, 4, 36, 10, 2, 1, 1, 0, 2, 0, 9, 10, 10, 17, 10, 9, 4, 34, 17, 9, 4, 18, 20, 16, 16, 4, 20, 10, 2, 1, 1, 0, 2, 0, 36, 20, 20, 34, 20, 36, 8, 17, 34, 36, 8, 18, 10, 2, 2, 8, 10, 20, 16, 32, 32, 0, 16, 0, 20, 36, 36, 18, 36, 20, 8, 33, 18, 20, 8, 34, 10, 2, 2, 8, 10, 36, 32, 16, 16, 0, 32, 0, 36, 20, 20, 33, 20, 36, 8, 18, 33, 36, 8, 17, 9, 1, 1, 8, 9, 20, 16, 32, 32, 0, 16, 0, 20, 36, 36, 17, 36, 20, 8, 34, 17, 20, 8, 33, 9, 1, 1, 8, 9, 36, 32, 16, 16, 0, 32, 0, 11, 5, 12, 38, 13, 3, 12, 19, 6, 26, 6, 3, 5, 48, 40, 52, 35, 21, 6, 48, 35, 24, 37, 12, 11, 5, 12, 22, 13, 3, 12, 35, 6, 42, 6, 3, 5, 48, 24, 52, 19, 37, 6, 48, 19, 40, 21, 12, 11, 6, 12, 37, 14, 3, 12, 19, 5, 25, 5, 3, 6, 48, 40, 52, 35, 22, 5, 48, 35, 24, 38, 12, 11, 6, 12, 21, 14, 3, 12, 35, 5, 41, 5, 3, 6, 48, 24, 52, 19, 38, 5, 48, 19, 40, 22, 12, 52, 24, 12, 42, 28, 48, 12, 49, 40, 37, 40, 48, 24, 3, 6, 11, 50, 25, 40, 3, 50, 5, 26, 12, 52, 40, 12, 26, 44, 48, 12, 49, 24, 21, 24, 48, 40, 3, 6, 11, 50, 41, 24, 3, 50, 5, 42, 12, 52, 24, 12, 41, 28, 48, 12, 50, 40, 38, 40, 48, 24, 3, 5, 11, 49, 26, 40, 3, 49, 6, 25, 12, 52, 40, 12, 25, 44, 48, 12, 50, 24, 22, 24, 48, 40, 3, 5, 11, 49, 42, 24, 3, 49, 6, 41, 12]

def xs1004 : List ℕ := [0x59e00859e0082aa2802aa280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896, 0x2aa2802aa28059e00859e0085318b35318b3150fa9150fa9000080000080017908017908460896460896180329180329, 0xa04255a04255a04255a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440, 0xc6955ec6955ec6955ec6955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237, 0x150fa95318b3150fa95318b359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080, 0x5318b3150fa95318b3150fa92aa28059e0082aa28059e008460896180329460896180329000080017908000080017908]

abbrev f1004 : BFn 6 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5))

theorem rows1004_len : rows1004.length = 384 := by decide +kernel

theorem enc_inputs1004 :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rows1004)
      = xs1004 := by decide +kernel

theorem enc_goal1004 : encL f1004 rows1004 = goal 192 := by decide +kernel

theorem mask1004 : mask 192 = 2 ^ rows1004.length - 1 := by decide +kernel

theorem proper_fail1004 : ∀ zs ∈ xs1004.sublists, zs ≠ xs1004 →
    (cov 192 zs &&& lo 192) ≠ lo 192 := by decide +kernel

theorem no_sub1004 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 192) (goal 192) s xs1004) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xs1004 → NatRun (mask 192) (goal 192) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs1004
  · subst e; exact noRunFull s hs h
  · exact proper_fail1004 zs (List.mem_sublists.2 hz) e (required h)

theorem main1004 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 192) (goal 192) s xs1004) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)) 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f1004 ⟨fun _ => false, fun _ => true, by decide⟩ 9 h
  have hr : NatRun (mask 192) (encL f1004 rows1004) s' (ws.map fun a => encL a rows1004) :=
    Run.map (fun a : BFn 6 => encL a rows1004)
      (fun a => by rw [mask1004]; exact encL_inv a rows1004)
      (fun a b => encL_and a b rows1004) (fun a b => encL_or a b rows1004) hrun
  rw [enc_goal1004] at hr
  refine no_sub1004 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs1004]
  exact hsub.map _





def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h





theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]





def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]





def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih





def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h





def t1 : Nat := 0x0

def t2 : Nat := 0x10000010000000000000000000000000000000000000000000000000

def t3 : Nat := 0x80110000000080110000000000000000000000000000000000000000000000000000

def t4 : Nat := 0x200000000000008020000400000000000000000000000000000000000000000000000000000

def t5 : Nat := 0x1000001000001000001008000008000008000008000000000000000000000000000000000000000000000000000

def t6 : Nat := 0x11000201000011000201028000408008028000408008020016000221020016000221000000011000000000011000

def t7 : Nat := 0x211000211000211000211428008428008428008428008020237020237020237020237011000011000011000011000

def t8 : Nat := 0x280020080110008510000510000020080110008000280000000000080000108000800000800000080000108000000

def t9 : Nat := 0x281020091110209510011518008028080518008028280000221020096000329020816011800000080011108000000

def t10 : Nat := 0x4000004000200200200200040508040508421012421012000000000000000000000000000000000000000000000000

def t11 : Nat := 0x401100420120021120020106850844850842901242901a020016000221020016000221000000011000000000011000

def t12 : Nat := 0x20280020280510008510008530080530080110288110288000080000080000908000908000880000880000108000108

def t13 : Nat := 0x218b3040fa1511833150d292aa00048e00028a20008e008460096180221460816180329000080017800000000017108

def t14 : Nat := 0x40708421012040708421012514008220280514008220280180329460896180329460896017908000080017908000080

def t15 : Nat := 0x4070942101304070942101340c00822820040c008228200000221020016000221020016011000000000011000000000

def t16 : Nat := 0x40788421092150508531012514000220280114008200280000000000080000108000800000800000080000108000000

def t17 : Nat := 0x61da2061da2551d2a551d2a286000286000286200286200fc84c0fc84c0fdfd48fdfd48e66896e66896b86329b86329

def t18 : Nat := 0x8a00008a00008a00008a0001108a11108a11108a11108a1000000000000000000000000000000000000000000000000

def t19 : Nat := 0x8a2800aa08019a00859a0005108a11308a11108a9110aa1000000000080000108000800000800000080000108000000

def t20 : Nat := 0x8e00008e00028a20028a200150da9150da95318b35318b3000000000000000000000000000000000000000000000000

def t21 : Nat := 0xaa0000aa00048a00848a0081108b11108b1110aa1110aa1000000000000011000011000020016020016000221000221

def t22 : Nat := 0xaa0800aa08059a00859a0081108a11108a1110aa1110aa1000080000080017908017908460896460896180329180329

def t23 : Nat := 0xca5084ab0020ca5084ab002114821200aa1114821200aa1b9f548e5fcc0b9f548e5fcc0fe6b3ffe02b7fe6b3ffe02b7

def t24 : Nat := 0x150da85318a2150da85318a2196000282280196000282280180108440880180108440880006908000080006908000080

def t25 : Nat := 0x150da95318a3150da95318a319e00028a28019e00028a280180108440880180108440880006908000080006908000080

def t26 : Nat := 0x150da95318b3150fa95318b319e00828a28059e0002aa280000108000800000000000080000108000000000800000080

def t27 : Nat := 0x150da95318b3150fa95318b319e00828a28059e0002aa280180329460896180329460896017908000080017908000080

def t28 : Nat := 0x150fa95318a3150fa95318a359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080

def t29 : Nat := 0x150fa95318b3150fa95318b348e0082aa20048e0082aa200000221020016000221020016011000000000011000000000

def t30 : Nat := 0x150fa95318b3150fa95318b348e0082aa20048e0082aa200180329460896180329460896017908000080017908000080

def t31 : Nat := 0x150fa95318b3150fa95318b359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080

def t32 : Nat := 0x150fb9531ab3150fb9531ab35be0086aa2885be0086aa2881a033f460ab71a033f460ab7017908011080017908011080

def t33 : Nat := 0x154fa95358b3350fa9731ab35de5082ea7885bf01a6ab292180329460896180329460896017908000080017908000080

def t34 : Nat := 0x170fa9531ab3550fa95318bb5be0887ba28059e2883ba2881803a9460896180b2946099e017988000880017908000188

def t35 : Nat := 0x178fa95398b3558fa95398bb59e0192aa29159e2092aa28118032946089619132947189603791e020096017b290002a1

def t36 : Nat := 0x1928a01928a01928a01928a01928a01928a01928a01928a0fc6988fc6988fc6988fc6988fc6988fc6988fc6988fc6988

def t37 : Nat := 0x1968a11968a1392aa1392aa11dada81dada85bb8a25bb8a2fe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t38 : Nat := 0x1dafa95bb8b31dafa95bb8b359e8a93baaa159e8a93baaa1180329460896180329460896017908000080017908000080

def t39 : Nat := 0x20420020420020420020420046151a46151a46151a46151a000000000000000000000000000000000000000000000000

def t40 : Nat := 0x20420120420120420120420146950a46950a46950a46950a020237020237020237020237019440019440019440019440

def t41 : Nat := 0x261fa3261fa3555d2b555d2b6af0026af0022ce7082ce708fe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t42 : Nat := 0x286200286200286200286200571daa571daa571daa571daafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t43 : Nat := 0x28a20028a20008e00008e0005318b35318b3150da9150da9000000000000000000000000000000000000000000000000

def t44 : Nat := 0x28e20028e20028e20028e200571dbb571dbb571dbb571dbb000000000000000000000000000000000000000000000000

def t45 : Nat := 0x2aa2802aa28059e00859e0085318b35318b3150fa9150fa9000080000080017908017908460896460896180329180329

def t46 : Nat := 0x2ae2802ae28079e20879e208571dbb571dbb571fbb571fbb000080000080017908017908460896460896180329180329

def t47 : Nat := 0x2ea7886ab2925de5085bf01a5358b3731ab3154fa9350fa9000080000080017908017908460896460896180329180329

def t48 : Nat := 0x314aa1314aa1314aa1314aa14eb50a4eb50a4eb50a4eb50afe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t49 : Nat := 0x396aa1396aa1396aa1396aa15fbdaa5fbdaa5fbdaa5fbdaafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t50 : Nat := 0x396aa1396aa1396aa1396aa15fbdaa5fbdaa5fbdba5fbdbafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t51 : Nat := 0x39eaa139eaa139eaa139eaa15fbdab5fbdab5fbdab5fbdabfe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t52 : Nat := 0x3baaa13baaa159e8a959e8a95bb8b35bb8b31dafa91dafa9000080000080017908017908460896460896180329180329

def t53 : Nat := 0x3beaa13beaa179eaa979eaa95fbdbb5fbdbb5fbfab5fbfabfe6bbffe6bbfff7bbfff7bbffffddefffddefdffe9fdffe9

def t54 : Nat := 0x3d6fa97b7ab33d6fa97b7ab35ffdaa7fbfaa5ffdaa7fbfaafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t55 : Nat := 0x3fafa97bbab35defa95bf8bb5bf8bb7bbab35defa93fafa91803a9460896197b2947799e47799e460896197b291803a9

def t56 : Nat := 0x5318b3150fa95318b3150fa92aa28059e0082aa28059e008460896180329460896180329000080017908000080017908

def t57 : Nat := 0x5358b3154fa9731ab3350fa92ea7885de5086ab2925bf01a460896180329460896180329000080017908000080017908

def t58 : Nat := 0x571daa571daa571daa571daa286200286200286200286200fdfdc8fdfdc8fdfdc8fdfdc8fe6bbffe6bbffe6bbffe6bbf

def t59 : Nat := 0x571dbb571fbb571dbb571fbb2ae28079e2082ae28079e208460896180329460896180329000080017908000080017908

def t60 : Nat := 0x571fbb571fbb571fbb571fbb7be2887be2887be2887be2885e0bbf5e0bbf5e0bbf5e0bbf017988017988017988017988

def t61 : Nat := 0x59e00859e0082aa2802aa280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t62 : Nat := 0x59e00859e0082aa2802aa280150fb9150fb95318b35318b3017908017908000080000080180329180329460896460896

def t63 : Nat := 0x59e00859e0182aa2802aa290150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t64 : Nat := 0x59e00859e2082aa2802aa280170fa9550fa95318b35318bb017908017908000080000080180329180329460896460896

def t65 : Nat := 0x59e0085be0082aa2886aa280150fa9150fa95318b3531ab3017908017908000080000080180329180329460896460896

def t66 : Nat := 0x59e00959e0092aa2812aa281158fa9158fa95398b35398b3017908017908000080000080180329180329460896460896

def t67 : Nat := 0x59e08859e0883ba2803ba280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t68 : Nat := 0x59e8a959e8a93baaa13baaa11dafa91dafa95bb8b35bb8b3017908017908000080000080180329180329460896460896

def t69 : Nat := 0x5bb8b31dafa95bb8b31dafa93baaa159e8a93baaa159e8a9460896180329460896180329000080017908000080017908

def t70 : Nat := 0x5bf01a5de5086ab2922ea788350fa9154fa9731ab35358b3017908017908000080000080180329180329460896460896

def t71 : Nat := 0x5bf8b31defa97bbab33dafa93fafa95deda97bbab35bf8bb460896180329460896180329000080017908000080017908

def t72 : Nat := 0x5bf8bb5deda97bbab33fafa93dafa91defa97bbab35bf8b3017908017908000080000080180329180329460896460896

def t73 : Nat := 0x5bf8bb5defa97bbab33fafa93fafa95defa97bbab35bf8bb47799e197b294608961803a91803a9197b2946089647799e

def t74 : Nat := 0x5de5085bf01a2ea7886ab292154fa9350fa95358b3731ab3017908017908000080000080180329180329460896460896

def t75 : Nat := 0x5defa95bf8bb3fafa97bbab35defa93fafa95bf8bb7bbab3197b2947799e1803a9460896197b291803a947799e460896

def t76 : Nat := 0x5dfd2a5dfd2a2ebfa22ebfa23d6fa93d6fa97b78b37b78b3fdfd48fdfd48fc84c0fc84c0b86329b86329e66896e66896

def t77 : Nat := 0x5fbdaa5fbdaa5fbdaa5fbdaa396aa1396aa1396aa1396aa1fdfdc8fdfdc8fdfdc8fdfdc8fe6bbffe6bbffe6bbffe6bbf

def t78 : Nat := 0x5ff51a5ff51a6eb79a6eb79a354fa9354fa9735ab3735ab3017908017908000080000080180329180329460896460896

def t79 : Nat := 0x5fffbb5fffbb7fbfbb7fbfbb7fefa97fefa97bfabb7bfabb5f7bbf5f7bbf5e0bbf5e0bbf197ba9197ba947799e47799e

def t80 : Nat := 0x79e20879e2082ae2802ae280571fbb571fbb571dbb571dbb017908017908000080000080180329180329460896460896

def t81 : Nat := 0x7bbab33fafa95bf8bb5deda97bbab35bf8b33dafa91defa9000080000080017908017908460896460896180329180329

def t82 : Nat := 0x7be2887be2887be2887be288571fbb571fbb571fbb571fbb0179880179880179880179885e0bbf5e0bbf5e0bbf5e0bbf

def t83 : Nat := 0x7fffab7fffab7fffab7fffab7fffab7fffab7fffab7fffabffffffffffffffffffffffffffffffffffffffffffffffff

def t84 : Nat := 0x800054800054800054800054800054800054800054800054000000000000000000000000000000000000000000000000

def t85 : Nat := 0x800055800255800055800255828054c0805c828054c0805c020016000221020016000221000000011000000000011000

def t86 : Nat := 0x804054804054a00254a0025484055c84055cc21056c21056000000000000000000000000000000000000000000000000

def t87 : Nat := 0x804055804055a00255a0025584854c84854cc29056c29056020237020237020237020237019440019440019440019440

def t88 : Nat := 0x841d77841d77841d77841d77a8e044a8e044a8e044a8e044fe8677fe8677fe8677fe8677a1f440a1f440a1f440a1f440

def t89 : Nat := 0x84454cc05056a40744a2105684454ca40744c05056a21056b9f769e7fc56b88661e684d6b9f769b88661e7fc56e684d6

def t90 : Nat := 0x861556861556c4155ec4155ea04054a04054a04244a04244008440008440019440019440020016020016000221000221

def t91 : Nat := 0x861df7861df7d51d7fd51d7fa8e044a8e044a8e244a8e244fe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t92 : Nat := 0x950ffdd318f7950ffdd318f7d9e05caaa2d4d9e05caaa2d4180329460896180329460896017908000080017908000080

def t93 : Nat := 0xa00254a00254804054804054c21056c2105684055c84055c000000000000000000000000000000000000000000000000

def t94 : Nat := 0xa00255a00255804055804055c29056c2905684854c84854c020237020237020237020237019440019440019440019440

def t95 : Nat := 0xa04245a04255a04245a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440

def t96 : Nat := 0xa04254a04254a04254a04254c6155ec6155ec6155ec6155e000000000000000000000000000000000000000000000000

def t97 : Nat := 0xa04254a04254a04254a04254c6155ec6155ec6155ec6155e020237020237020237020237019440019440019440019440

def t98 : Nat := 0xa04255a04255a04255a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440

def t99 : Nat := 0xa042d5a242d5b1425df14255d7955ec695ded7955ec697de0202370202b702033f020a37019c400194c0019548019440

def t100 : Nat := 0xa202d5a202d5d1405dd1405dc29056c2905684874c84874c0202b70202b7037b3f037b3f479cd6479cd6199769199769

def t101 : Nat := 0xa21af7a40fe5d15877954d6deab056caf056aca74c8ce54cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t102 : Nat := 0xa2c255a2c255e0c25de0c25dc6955fc6955fc6975fc6975f020237020237031237031237039456039456019661019661

def t103 : Nat := 0xa4475de25257a4475de25257c6d55ee6975ec6d55ee6975e020237020237020237020237019440019440019440019440

def t104 : Nat := 0xa61756a61756c4555ec4555ee25056e25056a4474ca4474cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t105 : Nat := 0xa61ff7a61ff7d55d7fd55d7feaf056eaf056ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t106 : Nat := 0xa61ff7a61ff7d55d7fd55d7feaf056eaf056ace75cace75cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t107 : Nat := 0xa61fffe61ff7d55d7fd75d7feaf056eaf256ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t108 : Nat := 0xa65ff7a65ff7f55f7ff55f7feef55eeef55eeef75eeef75efe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t109 : Nat := 0xa8e254a8e254a8e254a8e254d71dffd71dffd71dffd71dff000000000000000000000000000000000000000000000000

def t110 : Nat := 0xa8e255a8e255a8e255a8e255d79dffd79dffd79dffd79dff020237020237020237020237019440019440019440019440

def t111 : Nat := 0xaaa2d4aaa2d4d9e05cd9e05cd318f7d318f7950ffd950ffd000080000080017908017908460896460896180329180329

def t112 : Nat := 0xaae2d4aae2d4f9e25cf9e25cd71dffd71dffd71fffd71fff000080000080017908017908460896460896180329180329

def t113 : Nat := 0xaae2d5aae2d5f9e25df9e25dd79dffd79dffd79fffd79fff0202b70202b7037b3f037b3f479cd6479cd6199769199769

def t114 : Nat := 0xace74ceaf056ace74ceaf056d55d7fa61ff7d55d7fa61ff7b9f769e7fcd6b9f769e7fcd6ffff7ffe86f7ffff7ffe86f7

def t115 : Nat := 0xace75deaf257ace75deaf257d7dd7fe69fffd7dd7fe69fffbbf77fe7fef7bbf77fe7fef7ffff7fff96f7ffff7fff96f7

def t116 : Nat := 0xaeb7d6aeb7d6ddf55eddf55ef358f7f358f7b54fedb54fed0084c00084c001fd4801fd48460896460896180329180329

def t117 : Nat := 0xaebff7aebff7ddfd7fddfd7ffbf8f7fbf8f7bdefedbdefedfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t118 : Nat := 0xaee7cceaf2d6fde74cfbf05ed75dfff71ff7d55fffb71fffb9f7e9e7fcd6b9ff69e7fddefffffffe8ef7ffff7ffe87ff

def t119 : Nat := 0xaeffffeefff7fdff7ffffd7ffffd7feefff7fdff7faefffffff7fffffef7ffff7ffffffffffffffffef7ffff7ffff7ff

def t120 : Nat := 0xb14af5b14af5b14af5b14af5ceb55eceb55eceb55eceb55e020237020237020237020237019440019440019440019440

def t121 : Nat := 0xb54ffdf35af7b54ffdf35af7dff55eeeb7dedff55eeeb7de1a033f460ab71a033f460ab701fd480194c001fd480194c0

def t122 : Nat := 0xb71ff7b71ff7d55dffd55dffeaf056eaf056ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t123 : Nat := 0xb71ffff71ff7d55fffd75dfffbf05eeaf2d6fde74caee7ccfe87fffe8ef7ffff7fffffffe7fddee7fcd6b9ff69b9f7e9

def t124 : Nat := 0xb96af5b96af5b96af5b96af5dfbdfedfbdfedfbdfedfbdfefe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t125 : Nat := 0xbdefedfbfaf7bdefedfbfaf7dffdffffbfffdffdffffbfffffffffffffffffffffffffffffffffffffffffffffffffff

def t126 : Nat := 0xbf7ff7bf7ff7fd7ffffd7ffffffdfefffdfeffffeeffffeefeeffffeeffffffffffffffffffddefffddefdffe9fdffe9

def t127 : Nat := 0xbfeffdfbfaf7fdeffdfbfaffdffdffffbfffdfffffffbfff1a03bf460ab71b7b3f477bbf47fdde479cd619ff691997e9

def t128 : Nat := 0xc6955ec6955ec6955ec6955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237

def t129 : Nat := 0xc6955ec6955ec6955ec6955ea042d5b14255a042d5b14255019440019440019440019440020237020237020237020237

def t130 : Nat := 0xc6955ec6955ec6955ec6975ea04255a0425da24255e04255019440019440019440019440020237020237020237020237

def t131 : Nat := 0xc6955fc6955fc6955fc6955fa0c255a0c255a0c255a0c255019440019440019440019440020237020237020237020237

def t132 : Nat := 0xc695dec695ded7955ed7955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237

def t133 : Nat := 0xc6d55ec6d55ee6975ee6975ea4475da4475de25257e25257019440019440019440019440020237020237020237020237

def t134 : Nat := 0xceb55eceb55eceb55eceb55eb14af5b14af5b14af5b14af5019440019440019440019440020237020237020237020237

def t135 : Nat := 0xcef55ecef55eeeb75eeeb75eb54ffdb54ffdf35af7f35af7019440019440019440019440020237020237020237020237

def t136 : Nat := 0xd318f7950ffdd318f7950ffdaaa2d4d9e05caaa2d4d9e05c460896180329460896180329000080017908000080017908

def t137 : Nat := 0xd55d7fd55d7fa61ff7a61ff7ace74cace74ceaf056eaf056ffff7fffff7ffe86f7fe86f7b9f769b9f769e7fcd6e7fcd6

def t138 : Nat := 0xd79dffd79dffd79dffd79dffa8e255a8e255a8e255a8e255019440019440019440019440020237020237020237020237

def t139 : Nat := 0xd79dffd79fffd79dffd79fffaae2d5f9e25daae2d5f9e25d479cd6199769479cd61997690202b7037b3f0202b7037b3f

def t140 : Nat := 0xd79fffd79dffd79fffd79dfff9e25daae2d5f9e25daae2d5199769479cd6199769479cd6037b3f0202b7037b3f0202b7

def t141 : Nat := 0xd79fffd79fffd79fffd79ffffbe2ddfbe2ddfbe2ddfbe2dd5f9fff5f9fff5f9fff5f9fff037bbf037bbf037bbf037bbf

def t142 : Nat := 0xd9e05cd9e05caaa2d4aaa2d4950ffd950ffdd318f7d318f7017908017908000080000080180329180329460896460896

def t143 : Nat := 0xdbf05edde55ceab2d6aea7dcb50ffd954ffdf31af7d358f7017908017908000080000080180329180329460896460896

def t144 : Nat := 0xddf55eddf55eaeb7d6aeb7d6b54fedb54fedf358f7f358f701fd4801fd480084c00084c0180329180329460896460896

def t145 : Nat := 0xdff55edff55eeeb7deeeb7deb54ffdb54ffdf35af7f35af701fd4801fd480194c00194c01a033f1a033f460ab7460ab7

def t146 : Nat := 0xe25257a4475de25257a4475de6975ec6d55ee6975ec6d55e020237020237020237020237019440019440019440019440

def t147 : Nat := 0xe6975ee6975ec6d55ec6d55ee25257e25257a4475da4475d019440019440019440019440020237020237020237020237

def t148 : Nat := 0xe69fffe69fffd7dd7fd7dd7feaf257eaf257ace75dace75dff96f7ff96f7ffff7fffff7fe7fef7e7fef7bbf77fbbf77f

def t149 : Nat := 0xe6d75ee6d75ee6d75ee6d75ee6575fe6575fe6575fe6575f019440019440019440019440020237020237020237020237

def t150 : Nat := 0xe6d75fe6d75fe6d75fe6d75fe6d75fe6d75fe6d75fe6d75f039677039677039677039677039677039677039677039677

def t151 : Nat := 0xeaf056ace74ceaf056ace74ca61ff7d55d7fa61ff7d55d7fe7fcd6b9f769e7fcd6b9f769fe86f7ffff7ffe86f7ffff7f

def t152 : Nat := 0xeeb7deeeb7dedff55edff55ef35af7f35af7b54ffdb54ffd0194c00194c001fd4801fd48460ab7460ab71a033f1a033f

def t153 : Nat := 0xeef75eeef75eeef75eeef75ef75ffff75ffff75ffff75fff019440019440019440019440020237020237020237020237

def t154 : Nat := 0xeef75eeef75eeef75eeef75ef75ffff75ffff75ffff75fffffffffffffffffffffffffffffffffffffffffffffffffff

def t155 : Nat := 0xeef7dfeef7dffff75ffff75ff7dffff7dffff7dffff7dfff0396f70396f703ff7f03ff7f479ef7479ef71b977f1b977f

def t156 : Nat := 0xf35af7b54ffdf35af7b54ffdeeb7dedff55eeeb7dedff55e460ab71a033f460ab71a033f0194c001fd480194c001fd48

def t157 : Nat := 0xf71ffff71fffd75dffd75dffeaf256eaf256ace74cace74cffffffffffffffffffffffffffffffffffffffffffffffff

def t158 : Nat := 0xf75ffff75ffff75ffff75fffeef75eeef75eeef75eeef75effffffffffffffffffffffffffffffffffffffffffffffff

def t159 : Nat := 0xf75ffff75ffff75ffff75ffffff7defff7defff7defff7de5e0bbf5e0bbf5e0bbf5e0bbf01fdc801fdc801fdc801fdc8

def t160 : Nat := 0xf9e25cf9e25caae2d4aae2d4d71fffd71fffd71dffd71dff017908017908000080000080180329180329460896460896

def t161 : Nat := 0xf9e25df9e25daae2d5aae2d5d79fffd79fffd79dffd79dff037b3f037b3f0202b70202b7199769199769479cd6479cd6

def t162 : Nat := 0xfff7defff7defff7defff7def75ffff75ffff75ffff75fff01fdc801fdc801fdc801fdc85e0bbf5e0bbf5e0bbf5e0bbf

def t163 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [t31,t56,t109,t128] else [t31,t56,t110,t153]) else (if i < 7 then [t18,t31,t56,t96,t128] else [t18,t31,t56,t98,t149]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t20,t31,t56,t93,t128] else [t20,t31,t56,t98,t147]) else (if i < 11 then [t31,t44,t56,t98,t128] else [t31,t44,t56,t110,t128])) else (if i < 14 then (if i < 13 then [t31,t45,t56,t110,t133] else [t31,t45,t56,t110,t135]) else (if i < 15 then [t31,t45,t71,t98,t135] else [t31,t46,t56,t110,t128])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t31,t49,t56,t82,t110] else [t31,t56,t58,t82,t128]) else (if i < 19 then [t31,t56,t82,t110,t128] else [t31,t56,t82,t110,t134])) else (if i < 22 then (if i < 21 then [t31,t56,t88,t110,t128] else [t31,t56,t110,t128,t162]) else (if i < 23 then [t31,t56,t110,t145,t152] else [t31,t56,t112,t128,t161]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t31,t69,t82,t98,t134] else [t31,t69,t82,t110,t128]) else (if i < 27 then [t31,t69,t98,t145,t152] else [t31,t72,t81,t98,t128])) else (if i < 30 then (if i < 29 then [t31,t82,t110,t114,t128] else [t38,t69,t82,t98,t128]) else (if i < 31 then [t10,t31,t43,t56,t98,t128] else [t10,t31,t45,t56,t110,t128]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t18,t31,t39,t56,t98,t128] else [t18,t31,t45,t56,t98,t133]) else (if i < 35 then [t18,t31,t46,t56,t98,t128] else [t18,t31,t49,t56,t82,t98])) else (if i < 38 then (if i < 37 then [t18,t31,t56,t77,t82,t128] else [t18,t31,t56,t82,t98,t128]) else (if i < 39 then [t18,t31,t56,t82,t98,t134] else [t18,t31,t56,t82,t110,t128]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t18,t31,t56,t88,t98,t128] else [t18,t31,t56,t98,t128,t162]) else (if i < 43 then [t18,t31,t56,t98,t145,t152] else [t18,t31,t69,t82,t98,t128])) else (if i < 46 then (if i < 45 then [t18,t31,t82,t98,t114,t128] else [t20,t31,t45,t49,t56,t98]) else (if i < 47 then [t20,t31,t45,t56,t77,t128] else [t20,t31,t45,t56,t98,t128])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t20,t31,t45,t56,t98,t135] else [t20,t31,t45,t56,t110,t128]) else (if i < 51 then [t20,t31,t45,t71,t98,t128] else [t20,t31,t45,t98,t114,t128])) else (if i < 54 then (if i < 53 then [t20,t31,t46,t56,t98,t128] else [t20,t31,t56,t82,t98,t128]) else (if i < 55 then [t20,t31,t56,t98,t128,t137] else [t20,t31,t56,t98,t128,t152]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t25,t45,t56,t61,t77,t128] else [t25,t45,t56,t61,t98,t128]) else (if i < 59 then [t26,t45,t56,t61,t98,t128] else [t27,t45,t56,t61,t98,t128])) else (if i < 62 then (if i < 61 then [t28,t45,t56,t61,t98,t128] else [t29,t45,t56,t61,t98,t128]) else (if i < 63 then [t30,t45,t56,t61,t98,t128] else [t31,t37,t45,t56,t61,t98])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t31,t41,t45,t56,t98,t128] else [t31,t42,t45,t56,t61,t98]) else (if i < 67 then [t31,t45,t48,t56,t61,t98] else [t31,t45,t49,t56,t61,t77])) else (if i < 70 then (if i < 69 then [t31,t45,t49,t56,t61,t98] else [t31,t45,t49,t56,t61,t103]) else (if i < 71 then [t31,t45,t49,t56,t61,t110] else [t31,t45,t49,t56,t61,t120]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t31,t45,t49,t56,t68,t98] else [t31,t45,t49,t56,t70,t98]) else (if i < 75 then [t31,t45,t49,t56,t77,t105] else [t31,t45,t49,t56,t80,t98])) else (if i < 78 then (if i < 77 then [t31,t45,t49,t56,t98,t105] else [t31,t45,t49,t56,t98,t142]) else (if i < 79 then [t31,t45,t49,t57,t61,t98] else [t31,t45,t49,t59,t61,t98])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t31,t45,t49,t61,t69,t98] else [t31,t45,t49,t61,t98,t114]) else (if i < 83 then [t31,t45,t49,t61,t98,t136] else [t31,t45,t49,t98,t105,t114])) else (if i < 86 then (if i < 85 then [t31,t45,t50,t56,t61,t98] else [t31,t45,t51,t56,t61,t98]) else (if i < 87 then [t31,t45,t56,t61,t95,t128] else [t31,t45,t56,t61,t96,t128]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t31,t45,t56,t61,t97,t128] else [t31,t45,t56,t61,t98,t128]) else (if i < 91 then [t31,t45,t56,t61,t98,t129] else [t31,t45,t56,t61,t98,t130])) else (if i < 94 then (if i < 93 then [t31,t45,t56,t61,t98,t131] else [t31,t45,t56,t61,t98,t132]) else (if i < 95 then [t31,t45,t56,t61,t98,t133] else [t31,t45,t56,t61,t98,t134]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t31,t45,t56,t61,t98,t135] else [t31,t45,t56,t61,t98,t138]) else (if i < 99 then [t31,t45,t56,t61,t98,t149] else [t31,t45,t56,t61,t110,t134])) else (if i < 102 then (if i < 101 then [t31,t45,t56,t62,t98,t128] else [t31,t45,t56,t63,t98,t128]) else (if i < 103 then [t31,t45,t56,t64,t98,t128] else [t31,t45,t56,t65,t98,t128]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t31,t45,t56,t66,t98,t128] else [t31,t45,t56,t67,t98,t128]) else (if i < 107 then [t31,t45,t56,t68,t98,t128] else [t31,t45,t56,t68,t98,t138])) else (if i < 110 then (if i < 109 then [t31,t45,t56,t68,t120,t128] else [t31,t45,t56,t70,t98,t128]) else (if i < 111 then [t31,t45,t56,t70,t128,t146] else [t31,t45,t56,t72,t98,t128])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t31,t45,t56,t76,t98,t128] else [t31,t45,t56,t78,t98,t128]) else (if i < 115 then [t31,t45,t56,t80,t98,t128] else [t31,t45,t56,t80,t98,t147])) else (if i < 118 then (if i < 117 then [t31,t45,t56,t80,t113,t128] else [t31,t45,t56,t82,t110,t128]) else (if i < 119 then [t31,t45,t56,t86,t128,t161] else [t31,t45,t56,t91,t98,t128]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t31,t45,t56,t98,t100,t128] else [t31,t45,t56,t98,t101,t128]) else (if i < 123 then [t31,t45,t56,t98,t104,t128] else [t31,t45,t56,t98,t105,t128])) else (if i < 126 then (if i < 125 then [t31,t45,t56,t98,t105,t133] else [t31,t45,t56,t98,t105,t134]) else (if i < 127 then [t31,t45,t56,t98,t105,t138] else [t31,t45,t56,t98,t105,t147]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t31,t45,t56,t98,t106,t128] else [t31,t45,t56,t98,t107,t128]) else (if i < 131 then [t31,t45,t56,t98,t122,t128] else [t31,t45,t56,t98,t128,t142])) else (if i < 134 then (if i < 133 then [t31,t45,t56,t98,t128,t143] else [t31,t45,t56,t98,t128,t144]) else (if i < 135 then [t31,t45,t56,t98,t128,t157] else [t31,t45,t56,t98,t128,t160]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t31,t45,t56,t98,t133,t161] else [t31,t45,t56,t98,t142,t150]) else (if i < 139 then [t31,t45,t56,t103,t105,t128] else [t31,t45,t56,t105,t110,t128])) else (if i < 142 then (if i < 141 then [t31,t45,t56,t105,t120,t128] else [t31,t45,t56,t110,t128,t145]) else (if i < 143 then [t31,t45,t57,t98,t105,t128] else [t31,t45,t59,t74,t98,t128])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t31,t45,t59,t98,t105,t128] else [t31,t45,t68,t98,t114,t128]) else (if i < 147 then [t31,t45,t68,t98,t128,t156] else [t31,t45,t74,t98,t114,t128])) else (if i < 150 then (if i < 149 then [t31,t45,t98,t105,t114,t128] else [t31,t45,t98,t105,t128,t136]) else (if i < 151 then [t31,t45,t98,t128,t136,t142] else [t31,t46,t56,t98,t105,t128]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t31,t46,t56,t98,t128,t161] else [t31,t47,t56,t74,t98,t128]) else (if i < 155 then [t31,t47,t56,t98,t105,t128] else [t31,t49,t56,t98,t105,t137])) else (if i < 158 then (if i < 157 then [t31,t52,t56,t68,t98,t128] else [t31,t52,t56,t98,t105,t128]) else (if i < 159 then [t31,t56,t77,t105,t128,t137] else [t31,t56,t82,t98,t110,t128]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t31,t56,t82,t98,t128,t158] else [t31,t56,t82,t110,t128]) else (if i < 163 then [t31,t56,t82,t113,t128,t161] else [t31,t56,t98,t105,t111,t128])) else (if i < 166 then (if i < 165 then [t31,t56,t98,t105,t116,t128] else [t31,t56,t98,t105,t128,t137]) else (if i < 167 then [t31,t56,t98,t111,t128,t142] else [t31,t98,t105,t114,t128,t137]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t1,t31,t45,t49,t56,t61,t98] else [t1,t31,t45,t56,t61,t98,t128]) else (if i < 171 then [t1,t31,t45,t56,t98,t105,t128] else [t2,t31,t45,t56,t61,t98,t128])) else (if i < 174 then (if i < 173 then [t3,t31,t45,t56,t61,t98,t128] else [t4,t31,t45,t56,t61,t98,t128]) else (if i < 175 then [t5,t31,t45,t56,t61,t98,t128] else [t6,t31,t45,t49,t56,t61,t98])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t6,t31,t45,t56,t61,t77,t128] else [t6,t31,t45,t56,t61,t98,t128]) else (if i < 179 then [t6,t31,t45,t56,t61,t128,t156] else [t6,t31,t45,t56,t98,t105,t128])) else (if i < 182 then (if i < 181 then [t6,t31,t45,t61,t98,t114,t128] else [t6,t31,t45,t61,t98,t128,t156]) else (if i < 183 then [t6,t45,t56,t61,t98,t128,t151] else [t7,t31,t45,t56,t61,t98,t128]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t8,t31,t45,t49,t56,t61,t98] else [t8,t31,t45,t56,t61,t98,t128]) else (if i < 187 then [t8,t31,t45,t56,t98,t105,t128] else [t8,t31,t55,t56,t61,t98,t128])) else (if i < 190 then (if i < 189 then [t8,t31,t56,t61,t98,t128,t137] else [t9,t31,t45,t56,t61,t98,t128]) else (if i < 191 then [t10,t18,t31,t45,t56,t98,t128] else [t10,t31,t45,t49,t56,t61,t98])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t10,t31,t45,t56,t61,t77,t128] else [t10,t31,t45,t56,t61,t98,t128]) else (if i < 195 then [t10,t31,t45,t56,t61,t98,t133] else [t10,t31,t45,t56,t61,t128,t161])) else (if i < 198 then (if i < 197 then [t10,t31,t45,t56,t98,t105,t128] else [t10,t31,t45,t56,t98,t128,t161]) else (if i < 199 then [t10,t31,t45,t57,t61,t98,t128] else [t10,t31,t45,t61,t98,t114,t128]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t10,t31,t46,t56,t61,t98,t128] else [t10,t31,t56,t61,t98,t128,t137]) else (if i < 203 then [t11,t31,t45,t56,t61,t98,t128] else [t12,t31,t45,t56,t61,t98,t128])) else (if i < 206 then (if i < 205 then [t13,t31,t45,t56,t61,t98,t128] else [t13,t31,t45,t56,t98,t105,t128]) else (if i < 207 then [t14,t31,t45,t56,t61,t98,t128] else [t14,t31,t45,t61,t98,t114,t128])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t15,t31,t45,t56,t61,t98,t128] else [t16,t31,t45,t56,t61,t98,t128]) else (if i < 211 then [t17,t31,t45,t56,t61,t98,t128] else [t18,t31,t45,t49,t56,t61,t98])) else (if i < 214 then (if i < 213 then [t18,t31,t45,t56,t61,t77,t128] else [t18,t31,t45,t56,t61,t98,t128]) else (if i < 215 then [t18,t31,t45,t56,t61,t98,t134] else [t18,t31,t45,t56,t61,t110,t128]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t18,t31,t45,t56,t82,t98,t128] else [t18,t31,t45,t56,t98,t105,t128]) else (if i < 219 then [t18,t31,t45,t56,t98,t128,t145] else [t18,t31,t45,t61,t69,t98,t128])) else (if i < 222 then (if i < 221 then [t18,t31,t45,t61,t98,t114,t128] else [t18,t31,t56,t82,t98,t128]) else (if i < 223 then [t19,t31,t45,t56,t61,t98,t128] else [t20,t31,t45,t56,t61,t98,t128]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t20,t31,t45,t56,t98,t113,t128] else [t20,t31,t45,t56,t98,t128]) else (if i < 227 then [t21,t31,t45,t56,t61,t98,t128] else [t22,t31,t45,t56,t61,t77,t128])) else (if i < 230 then (if i < 229 then [t22,t31,t45,t56,t61,t98,t128] else [t23,t31,t45,t56,t61,t98,t128]) else (if i < 231 then [t24,t31,t45,t56,t61,t77,t128] else [t24,t31,t45,t56,t61,t98,t128]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t31,t31,t45,t49,t56,t61,t98] else [t31,t31,t45,t56,t61,t77,t128]) else (if i < 235 then [t31,t31,t45,t56,t61,t98,t128] else [t31,t31,t45,t56,t98,t105,t128])) else (if i < 238 then (if i < 237 then [t31,t31,t45,t61,t98,t114,t128] else [t31,t32,t45,t56,t61,t98,t128]) else (if i < 239 then [t31,t33,t45,t56,t61,t98,t128] else [t31,t34,t45,t56,t61,t98,t128])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t31,t35,t45,t56,t61,t98,t128] else [t31,t36,t45,t56,t61,t98,t128]) else (if i < 243 then [t31,t38,t45,t56,t61,t98,t128] else [t31,t39,t45,t56,t61,t98,t128])) else (if i < 246 then (if i < 245 then [t31,t40,t45,t49,t56,t61,t98] else [t31,t40,t45,t56,t61,t98,t128]) else (if i < 247 then [t31,t45,t46,t56,t61,t98,t128] else [t31,t45,t49,t49,t56,t61,t98]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t31,t45,t49,t53,t56,t61,t98] else [t31,t45,t49,t54,t56,t61,t98]) else (if i < 251 then [t31,t45,t49,t55,t56,t61,t98] else [t31,t45,t49,t56,t60,t61,t98])) else (if i < 254 then (if i < 253 then [t31,t45,t49,t56,t61,t77] else [t31,t45,t49,t56,t61,t77,t98]) else (if i < 255 then [t31,t45,t49,t56,t61,t82,t98] else [t31,t45,t49,t56,t61,t84,t98])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t31,t45,t49,t56,t61,t98] else [t31,t45,t49,t56,t61,t98,t98]) else (if i < 259 then [t31,t45,t49,t56,t61,t98,t105] else [t31,t45,t49,t56,t61,t98,t113])) else (if i < 262 then (if i < 261 then [t31,t45,t49,t56,t61,t98,t114] else [t31,t45,t49,t56,t61,t98,t121]) else (if i < 263 then [t31,t45,t49,t56,t61,t98,t124] else [t31,t45,t49,t56,t61,t98,t128]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t31,t45,t49,t56,t61,t98,t139] else [t31,t45,t49,t56,t61,t98,t145]) else (if i < 267 then [t31,t45,t49,t56,t61,t98,t150] else [t31,t45,t49,t56,t61,t98,t163])) else (if i < 270 then (if i < 269 then [t31,t45,t49,t56,t98,t105] else [t31,t45,t49,t56,t98,t105,t128]) else (if i < 271 then [t31,t45,t49,t61,t98,t114] else [t31,t45,t49,t61,t98,t114,t128])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t31,t45,t53,t56,t61,t98,t128] else [t31,t45,t54,t56,t61,t98,t128]) else (if i < 275 then [t31,t45,t55,t56,t61,t98,t128] else [t31,t45,t55,t56,t98,t105,t128])) else (if i < 278 then (if i < 277 then [t31,t45,t56,t60,t61,t98,t128] else [t31,t45,t56,t60,t98,t105,t128]) else (if i < 279 then [t31,t45,t56,t61,t79,t98,t128] else [t31,t45,t56,t61,t83,t98,t128]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t31,t45,t56,t61,t84,t98,t128] else [t31,t45,t56,t61,t84,t98,t150]) else (if i < 283 then [t31,t45,t56,t61,t85,t98,t128] else [t31,t45,t56,t61,t86,t98,t128])) else (if i < 286 then (if i < 285 then [t31,t45,t56,t61,t87,t98,t128] else [t31,t45,t56,t61,t88,t98,t128]) else (if i < 287 then [t31,t45,t56,t61,t89,t98,t128] else [t31,t45,t56,t61,t90,t98,t128]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t31,t45,t56,t61,t92,t98,t128] else [t31,t45,t56,t61,t98,t98,t128]) else (if i < 291 then [t31,t45,t56,t61,t98,t99,t128] else [t31,t45,t56,t61,t98,t102,t128])) else (if i < 294 then (if i < 293 then [t31,t45,t56,t61,t98,t103,t128] else [t31,t45,t56,t61,t98,t105,t128]) else (if i < 295 then [t31,t45,t56,t61,t98,t108,t128] else [t31,t45,t56,t61,t98,t110,t128]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t31,t45,t56,t61,t98,t113,t128] else [t31,t45,t56,t61,t98,t115,t128]) else (if i < 299 then [t31,t45,t56,t61,t98,t117,t128] else [t31,t45,t56,t61,t98,t118,t128])) else (if i < 302 then (if i < 301 then [t31,t45,t56,t61,t98,t119,t128] else [t31,t45,t56,t61,t98,t120,t128]) else (if i < 303 then [t31,t45,t56,t61,t98,t121,t128] else [t31,t45,t56,t61,t98,t124,t128])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t31,t45,t56,t61,t98,t125,t128] else [t31,t45,t56,t61,t98,t126,t128]) else (if i < 307 then [t31,t45,t56,t61,t98,t127,t128] else [t31,t45,t56,t61,t98,t128])) else (if i < 310 then (if i < 309 then [t31,t45,t56,t61,t98,t128,t141] else [t31,t45,t56,t61,t98,t128,t150]) else (if i < 311 then [t31,t45,t56,t61,t98,t128,t154] else [t31,t45,t56,t61,t98,t128,t155]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t31,t45,t56,t61,t98,t128,t159] else [t31,t45,t56,t61,t98,t128,t163]) else (if i < 315 then [t31,t45,t56,t61,t98,t133] else [t31,t45,t56,t61,t98,t134])) else (if i < 318 then (if i < 317 then [t31,t45,t56,t61,t98,t138] else [t31,t45,t56,t61,t98,t139,t140]) else (if i < 319 then [t31,t45,t56,t61,t98,t145,t150] else [t31,t45,t56,t61,t98,t145,t152])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t31,t45,t56,t68,t98,t128] else [t31,t45,t56,t70,t98,t128]) else (if i < 323 then [t31,t45,t56,t73,t75,t98,t128] else [t31,t45,t56,t73,t98,t105,t128])) else (if i < 326 then (if i < 325 then [t31,t45,t56,t73,t98,t128,t145] else [t31,t45,t56,t80,t98,t128]) else (if i < 327 then [t31,t45,t56,t82,t98,t105,t128] else [t31,t45,t56,t82,t98,t128,t161]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t31,t45,t56,t84,t98,t105,t128] else [t31,t45,t56,t84,t98,t128,t142]) else (if i < 331 then [t31,t45,t56,t90,t98,t105,t128] else [t31,t45,t56,t94,t98,t105,t128])) else (if i < 334 then (if i < 333 then [t31,t45,t56,t98,t98,t105,t128] else [t31,t45,t56,t98,t105,t105,t128]) else (if i < 335 then [t31,t45,t56,t98,t105,t108,t128] else [t31,t45,t56,t98,t105,t113,t128])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t31,t45,t56,t98,t105,t114,t128] else [t31,t45,t56,t98,t105,t117,t128]) else (if i < 339 then [t31,t45,t56,t98,t105,t121,t128] else [t31,t45,t56,t98,t105,t123,t128])) else (if i < 342 then (if i < 341 then [t31,t45,t56,t98,t105,t128] else [t31,t45,t56,t98,t105,t128,t128]) else (if i < 343 then [t31,t45,t56,t98,t105,t128,t137] else [t31,t45,t56,t98,t105,t128,t139]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t31,t45,t56,t98,t105,t128,t145] else [t31,t45,t56,t98,t105,t128,t148]) else (if i < 347 then [t31,t45,t56,t98,t105,t128,t150] else [t31,t45,t56,t98,t105,t128,t152])) else (if i < 350 then (if i < 349 then [t31,t45,t56,t98,t105,t128,t161] else [t31,t45,t56,t98,t105,t128,t163]) else (if i < 351 then [t31,t45,t56,t98,t128,t142] else [t31,t45,t56,t98,t128,t145,t161]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t31,t45,t98,t105,t114,t128] else [t31,t56,t98,t105,t128,t137]) else (if i < 355 then [t6,t31,t45,t56,t61,t98,t128] else [t8,t31,t45,t56,t61,t98,t128])) else (if i < 358 then (if i < 357 then [t10,t31,t45,t56,t61,t98,t128] else [t18,t31,t45,t56,t61,t98,t128]) else (if i < 359 then [t31,t31,t45,t56,t61,t98,t128] else [t31,t45,t49,t56,t61,t98]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t31,t45,t49,t56,t61,t98,t128] else [t31,t45,t55,t56,t61,t98,t128]) else (if i < 363 then [t31,t45,t56,t60,t61,t98,t128] else [t31,t45,t56,t61,t84,t98,t128])) else (if i < 366 then (if i < 365 then [t31,t45,t56,t61,t98,t98,t128] else [t31,t45,t56,t61,t98,t105,t128]) else (if i < 367 then [t31,t45,t56,t61,t98,t113,t128] else [t31,t45,t56,t61,t98,t121,t128])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t31,t45,t56,t61,t98,t128] else [t31,t45,t56,t61,t98,t128,t150]) else (if i < 371 then [t31,t45,t56,t98,t105,t128] else [t31,t45,t56,t61,t98,t128])) else []) else [])))) else []))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x2c0972c5715057b2c0b125d71471762d8b12210c5ed762c4972c11c5057d2c4b62217b5f5762c0b12210c5ed762e4b62217b431762ccb12bd7d43d762d8b12bd7d43d762e4af2e177371592d8b12217f5dd762d8b12210c5dd762c4b72c16b5057f2f8bc2217a5e5732c4b72bd745f57f2c4882e17b5fd7d2c4b72bd795657f2c4b725d7a5c57f2e4af2e17b5fd592e4b72bd795f57f2f8b72c16b5f174220972bd6f5e5612e4af2e17b371592c4b625d1c5c5762e4b62bd0f5f5762c4b62217b5fd762c4882bd795f57f2c4972e17b3717d2c4b82c16b5057f2c4b72bd795f57f2e08815d7d5d9772c4b62217b43176 else 0x2c4b72bd7e4a57f2e0b715d7d5d9772e0882c57d5d9772c4b62217e431762e0882e57d5d9772e0b12f9735e57a2f8b72c56b5f1742c4b72bd7943d7f2e0882e57d4a5772e0882c571505772e4b12217a5e57c2c4b82bd794a57f2e0972bd6f5f97a2e0b12f97c5f97a2c4b82bd795f57f2c4b82217b5fd762c4882e17b3717d2c4b025d1c5c5762c4882bd745f57f2e4882bd795f57f2dcbe2c17c5ad742c4882bd795657f2c48825d7a5c57f2f0be221795e9732d8af2e57d4a57b2d8972c5715057b2d89715d7d5d97b2cc972e57d4a57b2e4af2e17b5d9592d8b12217f5ed762c4b62bd0f5f5762c4b82217b43176) else (if i < 96 then 0x2c4b02217b431762e0882c5715d9772c4b62217b551762c4b825d7a5c57f2c4b82bd7e5f57f2e4b82bd795f57f2e4b82f17a5f17e2c4b82bd795657f220b12bd6f5e5612e4b32bd0f5f5762c4b72bd7e5f57f2c4b625d7b5c5762c4b82cd7e5657f2c4b72cd745657f2dcbe2c17c5e9742e4b72cd7e5657f2e0b02cd7c5f96b2dcb12cd595f97f2c4b72c17a5c57f2c4b62bd7b5f5762f0be2e17e5e9732e0b02cd6f5f97a2e0b02cd7c5f97a2c4b62bd795f5762c4882bd7e5657f2c4b72cd7e5f57f2e0972bd6f5f96b2c4b72cd7e4a57f2c4b72cd7e5657f220972bd6f5f9612e08815d7d5d97b2e0972bd6f5e57a else 0x2c4882bd794a57f2e4b62217b5fd762e4b62bd7b5f576220b82c5685c5772e4b62217a431762c4b622179431762c4972c17a5057d2c4b72bd795f5762e4b62bd795f5762e4af2c16b505592e4af2c11c5ad592d89715d7d5fd7b2d8af15d7d5fd7b2cc9715d7d5d97b2c4b82217b5f5762c4b02217b5f5762c4b025d7b5c5762c4b6221775fd762c4b62dd7b5f5762c4b62dd7b5fd762e0972bd6f5e5612c4b82cd7e4a57f2ccb12210c5ed762dcb815d765f57725c882bd795bd61220b815d765f5772c0b125d7d471762c4b622177431762e4b32217b431762c4b625d7b5f5762e4b625d1c5c5762c4b62211c43176)) else (if i < 192 then (if i < 160 then 0x2e0882e57d5d97e2ccaf15d7d5d97e2e0b32c17c5e97e2d8b12bd7d5f9762e0af25d6f5e97e220af2f17c5e97b2e0b92f17c5e97e2f0b82f97e5f17a2c4b82c16b5c57f220b815d765f57a2e0882c57d5d97a2dcbe2c57c5ad74220b82e57c5f5772dcbe2c57c5e9742e08815d7d5fd772d8b12217d5ed76220972bd6f5d161220b82c5765f5772e0af15d7d5fd7b2e09715d7d5fd7b2e0bc2f9735e57a220b82e5765f5772c4b92217e5e97c2f0be2e1745e9732c09715d7d5d97b2ccaf15d7d5d97b2c4b62bd7e5f5762c4b72cd7e5ed7f2c4b72cd7e43d7f2c4b9221795e97c2c4b92e17e5e97c2e0bc2f97c5f97a else 0x2c4b82f97e5f17a2c0b32e17e5e97c) else 0))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x10101010131010101010101010102000304030805 else 0x101000000650065006500650133014303040000040805) else (if i < 7 then 0x101010101010131000000000101010101010101010101010101010101010702000100040002010f09 else 0x650065006500650101006500650065006500650000006501330000020a000000040d08))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x101010101010131000000000101010101010101010101010101010101010702000100040002010f09 else 0x650065006500650101006500650065006500650000006501330000020a000000040d08) else (if i < 11 then 0x13300000065010100650065006500650065006500650065006500000302000001050d08 else 0x100065006500650065000000650133006501030065010100650065006500650e00010003010700051009)) else (if i < 14 then (if i < 13 then 0x6300650063006700630063006300050001010805 else 0x6300650063006700630063006300050001010805) else (if i < 15 then 0x13501330135013701350135013500050001010805 else 0xb1006500b1006700b100b100b100050001010805)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x87000101 else 0x87000101) else (if i < 19 then 0x65000000930087008700870087008704000000000805 else 0x65000000930087008700870087008704000000000805)) else (if i < 22 then (if i < 21 then 0x87000101 else 0x930093000000930093006500930093009300930093000601080002000c07) else (if i < 23 then 0x1390139013901390139000000000604 else 0x117001500150000001500150015000000150204000200000906))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x1330000013b013b013b013b013b013b04000000000805 else 0x65000000930109010901090109010904000000000805) else (if i < 27 then 0x13d013d013d013d013d000000000604 else 0x13f013f013f013f013f013f013f01030003000805)) else (if i < 30 then (if i < 29 then 0x87000101 else 0x103000001410087008700870087008704000000000805) else (if i < 31 then 0x101000000650065006500b3003400650103006500650065006500650065006500400065006500650065006500650065050a080f080200000000000602180d else 0x1050000006700600065006300630063006900630063009000630063006300630063006300630400000401080300000108130b))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x650065010100650065001000650065010300650065006500b30065006500400065006500650065006500650065160a050e000204000400030302180d else 0x67000000000060006500630015006300630063006300630063006300630063006300630201000300060900000301120b) else (if i < 35 then 0x67000000000090006500b1001500b100b100b100b100b100b100b100b100b100b100b10201000300060900000301120b else 0xa0000000870000000303)) else (if i < 38 then (if i < 37 then 0x87000101 else 0x9300000087006500c00087009f000000870087008700870087008700870087008700870001000200000700000303120b) else (if i < 39 then 0x870087009f00870093008700650087008700d00087008700870087008701200122008700870087008709020d0e03000d060005000202170d else 0x8700d000870087008700870087009f00c000c0008700870087010901320093008700970087006500870087008700870130010700870087008702121314170f0e0c1809020b00000300081f11))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x8700e00000000303 else 0x930093000000930093009300000065009300930093009300f000930093009300930093009300930093000000050012030200010300150c) else (if i < 43 then 0x10b010d010b010b0140010b010b010b0067010b0100010f010b0142010b010b010b010b010b0a02000b08010b04020004140b else 0x870087009300870087006501110130012000870087009f00870087017000870087008700870087008700040d0e110304030202000301170d)) else (if i < 46 then (if i < 45 then 0x160000000870000000303 else 0x63000101) else (if i < 47 then 0x63000101 else 0x63000000000063006300630063006700630063006300650063006300630109000200080000050f09)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x7000630063006300630067008000630065006300150063006300630063006300820063006300630063010b000e120201070001000307170d else 0x1050000006700700065006300630063006900630063009000630063006300630063006300630400000401080300000108130b) else (if i < 51 then 0x6300800067011300630065000000630063006300630063015c0063006300630063006300630200080000030002000103130b else 0x63000101)) else (if i < 54 then (if i < 53 then 0x67000000000090006500630015006300630063006300630063006300630063006300630201000300060900000301120b else 0x930000008d006500c0008d009f0000008d008d008d008d008d008d008d008d008d008d0001000200000700000303120b) else (if i < 55 then 0x63000101 else 0x650020000000670067000000670067006700670067006700670067006700670067006700670700060b00080303000600130b))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x7b000101 else 0x7b0115007b007b007b007b007b06000000000805) else (if i < 59 then 0x115007b007b0000007b007b007b007b007b0004000002000906 else 0x30003000300030003000305000000000705)) else (if i < 62 then (if i < 61 then 0x30003000300030003000305000000000705 else 0x300030003000300030003000306000300000805) else (if i < 63 then 0x30003000300030003000305000000000705 else 0x37000101)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x3000101 else 0x300b8000000000404) else (if i < 67 then 0x83000101 else 0x101)) else (if i < 70 then (if i < 69 then 0x3000101 else 0x3000101) else (if i < 71 then 0x500a000000000000100000404 else 0x3000101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x3000101 else 0x3000101) else (if i < 75 then 0x101 else 0xd000101)) else (if i < 78 then (if i < 77 then 0x101 else 0x3000101) else (if i < 79 then 0x77000101 else 0x3000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x99000101 else 0x101) else (if i < 83 then 0xcd000101 else 0x101)) else (if i < 86 then (if i < 85 then 0x3000101 else 0x4b000101) else (if i < 87 then 0x30003000300030003000305000000000705 else 0x150015000000000015001500150015001500cf011700150015001500150a0800000e060107000f09))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 91 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705)) else (if i < 94 then (if i < 93 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 95 then 0x15000500000005000500050005000500630005010000020906 else 0x830083008300830083008305000000000705))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x500000063011b0015011900050005000500050005000500090003000701000d08 else 0x770003007b000300c800030003000301150000011d00030003000300000406000301000e08) else (if i < 99 then 0x7500150015000000150015001500150015001500a300100015011f00af0a06000005080002060f09 else 0xd000000005000500050005007f006300510007008100050005000500000109000809000e08)) else (if i < 102 then (if i < 101 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 103 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 107 then 0x1150003011d000300030003000300030004020001000906 else 0x770003007b0003013c00030003000301150000011d00030003000300000406000301000e08)) else (if i < 110 then (if i < 109 then 0x770003007b0003012c00030003000301150000011d00030003000300000406000301000e08 else 0x30003000300030003000305000000000705) else (if i < 111 then 0x300cd0003007700030003000300030005000000000906 else 0x1150003011d0003007700030003000300030079060006000202020b07)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x30003000300030003000305000000000705 else 0x300030003012100030003000306000002000805) else (if i < 115 then 0xaf000d0007000d000d000d000d000d0304000005000906 else 0xaf000d0007000d000d000d000d000d0304000005000906)) else (if i < 118 then (if i < 117 then 0x27000101 else 0x7f00000005008f007f00150087008b00150087008900c0007f0087007f008d007f007f007f007f007f007f000d00020013070400070000160c) else (if i < 119 then 0x240015011700150015000000cf0015001501100000001500150015001500150015001500150904060601000201000200130b else 0xd000101))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x3000101 else 0x3000101) else (if i < 123 then 0x3000101 else 0x3000101)) else (if i < 126 then (if i < 125 then 0x5000101 else 0x83000101) else (if i < 127 then 0x16c00000003000000000404 else 0x37000101))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x3000101 else 0x3000101) else (if i < 131 then 0xcd000101 else 0x30003000300030003000305000000000705)) else (if i < 134 then (if i < 133 then 0x30003000300030003000305000000000705 else 0x123000000030003000300030003000301040000000805) else (if i < 135 then 0x63000101 else 0xaf01140015000000000000001500750015001500150015001500150000020105030100020e09))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x1500150015000b0125001500750015003400150015001500150015001500000208030b0504021009 else 0x101) else (if i < 139 then 0x3000101 else 0x5000101)) else (if i < 142 then (if i < 141 then 0x3000101 else 0x150100000000950091009300510097005100510051005100510051005100f00015005102000f03070b00050003120a) else (if i < 143 then 0x77000101 else 0x7b000300cd000300030003000300030404000004000906)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x3000101 else 0x3000101) else (if i < 147 then 0x14c0127011500000115011501150115011501150115011501150001020106040100010e09 else 0x3000101)) else (if i < 150 then (if i < 149 then 0x101 else 0xcd000101) else (if i < 151 then 0x30003000300030003000305000000000705 else 0x5000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x150015001500550129001500750015004000150015001500150015001500000208030b0504021009 else 0x12b0003012d000300030003000300030404000004000906) else (if i < 155 then 0x3000101 else 0x101)) else (if i < 158 then (if i < 157 then 0x770003007b0003017800030003000301150000011d00030003000300000406000301000e08 else 0x3000101) else (if i < 159 then 0x101 else 0xc0006500a7009f0107009700400093009f009f009f009f008700a301070000009f009f009f009f009f009f0107009f07040d0c06030b060502050002180d))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x87000101 else 0x9f008700c000c00087008d009b00a0009f0087008700c0008700b00087009f009b0087009d00a100e000870087009f005000a700a1009700c0016200c000870087009700a500f0008700a300870160009f00870023232022081e1d1c0127171514260002130d160c090b2b17) else (if i < 163 then 0x8f00c0005500000015012f012f00550055005500550055005500010900000003030d08 else 0xcd000101)) else (if i < 166 then (if i < 165 then 0xd1000101 else 0x101) else (if i < 167 then 0x30003000300030003000305000000000705 else 0x101))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x26000000260000302600260026002600000000200000906 else 0x300030003000000030003000303b000050003000303b000030003000300030003000303b000030003000300010003000303b003b00003000303b0000300030003001a000000081700001606101a10110006022112) else (if i < 171 then 0x5d0000005d0000305d005d005d005d00001000200000906 else 0x300030003000000030003000303b0000500030003047a00030003000300030003000303b000030003000300010003000303b00464000300030478000300030003001a000000081700001606101a10110006022112)) else (if i < 174 then (if i < 173 then 0x300030003000000030003000303f800050003000303b000030003000300030003000303c000030003000300010003000303b003b00003000304b8000300030003001a000000081700001606101a10110006022112 else 0x300030003000000030003000303b000050003000303b000030003000300030003000303d000030003000300010003000303b00484000300030498000300030003001a000000081700001606101a10110006022112) else (if i < 175 then 0x300030003000000030003000303b000050003000303b000030003000300030003000303e000030003000300010003000304a004a40003000303b0000300030003001a000000081700001606101a10110006022112 else 0x260026000030000010403)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x268000300000000000303 else 0x3b0000300030003000300030003000300030003000303b00003000500030003000300010003000300030003000300030f110511001000030a0301010700190e) else (if i < 179 then 0x101 else 0x305d0000005d00000000403)) else (if i < 182 then (if i < 181 then 0x305da0000000303 else 0x101) else (if i < 183 then 0x5d805d800030000010403 else 0x30003000300030003000300030003000103b000030003000500030003000300030003000300030003000300140d03081003020301040201170d))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x260026000030000010403 else 0x300030003000300030003000300030003000303b0000300030005000300030003000103b0000300030003000300031015030f000302010b0e01000809190e) else (if i < 187 then 0x305d0000005d00000000403 else 0x101)) else (if i < 190 then (if i < 189 then 0x3000005d40000000303 else 0x300030003000300030003000100030003000300110003000300030003000303b00003000300030003000302140d000a12020e0102080000170d) else (if i < 191 then 0x630063006700650015001000630063006300630069003000400063006b00630063006300630063006300630063006300630063006301100063006300001108111000170f1100060f0d0002130004072012 else 0x36000000300000502d40302026002600000000200000906)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x502be02bc000003180278026800030200000705 else 0x3b00015000500050003040000130003000504fc000505440005000300630005006f00050005000503b000030005006d0003000500050005000504fe00030005000500050000170d06141c00131700151112160107130d00082313) else (if i < 195 then 0x40000150005000500050400001b00050005050c0005055400050015006300050005000500050005040000050005000500050005000500050005050e00050005000500050000170d06141c00131700151112160107130d00082313 else 0x56400000071000000000404)) else (if i < 198 then (if i < 197 then 0x5070007020000079005e005d000030200000705 else 0x51001500150015000b0015001500150015007500150015001500000015001506a00015001500730015001507a000150015001500150015000c04000000110100000418000e00061d10) else (if i < 199 then 0x4fe0015000500050077050e001b0005000507b80005071a0005007700630005007700050005000504fe0077000500050077000500050005000504fe00770005000500050000170d06141c00131700151112160107130d00082313 else 0x5da000005da0005072a07ca063a06ca0001000200000906))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x54400150005000500050554001b0005000507180005054400050015006300050005000500050005054400050005000500050005000500050005071a00050005000500050000170d06141c00131700151112160107130d00082313 else 0x5d4000505d40000075a0758061405d40000000200000906) else (if i < 203 then 0x4fe006f006f00030003006f006f006f006f0003006f03b0006f000500050003007700050003006f006f006f0003006f0f110511001000030a0301010700190e else 0x30003000300030003000300030001000303b000030005000300030003000300030003000300030003000301140c0009070b0b0701030000170d)) else (if i < 206 then (if i < 205 then 0x3b000030003000300030003000300030003000300030003000300030003000f00790003000300010003000300030003000311120213000401020a020000090c1a0e else 0x5d0000005d000000003000000000504) else (if i < 207 then 0x300030003000300030003000300030003000303b000030003001100030003000300010003000300030003000300030f140812001202020a0001010009190e else 0x305da000005da0000000403)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x300000003000300030003000300030005040800030000000100030003000303b0000300030003000300030003000300030003000300030000000c00110b0800001b1600020b001c10 else 0x30003000300030003000300030000000500030003000300010003000304f603b00003000300030000007b0003000300030003000300030000000500170b0800000a1600020b001c10) else (if i < 211 then 0x3000300030003000300030003000100030524000300050003000300030003007d0003000700030003000301140c0009070b0b0701030000170d else 0x37000500320000502600322026002800003000200000906)) else (if i < 214 then (if i < 213 then 0x2aa006002680005026802a8026802980001000200000906 else 0x300110043000103b00410007f00030015002500010005000500050070000304ca00050003000500050005000500050063000500050081000704380005000503b000050005000504c8000500031a151222052300201212201f0f0a17170d0b0016012815) else (if i < 215 then 0x8300050005000104100410007f00830015002500050005000500050080008304ea000500830005000500050005000500630005000500810007045000050005041000050005000504e8000500831a151222052300201212201f0f0a17170d0b0016012815 else 0x500050005000504380450007f00050015002500050005000500050090000504da000500510005000500050005000500630005000500810007043800050005043800050005000504d8000500051a151222052300201212201f0f0a17170d0b0016012815))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x15008f0085007f0087008b0070007f0087007f007f007f000500150087007f007f007f007f0089007f007f0087008d00700570007f007f007f007f007f007f007f007f0517001717171614150718001310020a0700052313 else 0x5073e073c000005d005f006d000030200000705) else (if i < 219 then 0x2500c00025002500250015001500b000250043074c0091001100950051002500930025002500250025002500970025002506f0074e00250025002500250025131c080b001500100011020d0d060c121100102213 else 0x50099000500050099002504ca04ea0099000500050005007f009904ca000500250005000507e8000500d0000704da0005006300150081009900050005000504ca000500050005000500050099262300200100111f1c181615040c151617040004072815)) else (if i < 222 then (if i < 221 then 0x60a07fa000000e005da064a0005000005da06ea000200000100000a07 else 0x87007000900810083000d200500070009f0080006000700087009700700087007000a500a0009f0070008700b0009f009b002000d0008700e2009700a700a100870087008700e0009f008d008700870087009d00700087009f009b008700870087008700870087007000a10087009f008700a30097008700870087082000872d003d3c293a39383239243922381d351b34162d142b0f1c0d150a23040b020100314122) else (if i < 223 then 0x1100a90005000000030005000500010043000700030011001100110011000300110003005103b004c80011001100110001001100030011001100000807001800050000121000020e001d10 else 0x500050005000500750005006300ab051e0025000300ab0005000500050170000100810015005d0013000500050005000503b00003000500050005001504380063000500ad006304200005051c00050005006301100063000500050544000300051713232e2d000b2528241e1c180b0025140425291b080a010015321a))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x15000b000b000b000b006b000b00630063000b00630110006300af000b0110000b000b00150110000b000b000b000b000b000b000b000b0063000b000b00000063000b151f0016001e140d0e0401070c00000f000a2212 else 0x142019000f0011001000015011000b700630150006300630015001501200110006301600004018001300140006b00b9068000630063006300b500b50015006301100152006300630015006300630063006300b9000b006300630110006300150063006300630063006300b1006b006b00b30063006301100063300000002b3b3600143a26390e3837360733322d0029211c1f1b150f1a2408013e20) else (if i < 227 then 0x10001000300050023041000510001000100030001000100010003000d0003000100010023000303b0000100010001000100010001160f020b0d00000a070909000d03031c0f else 0x268026800000001000000000504)) else (if i < 230 then (if i < 229 then 0x10001000b00010001000300370005000100030001000d00050003000300050001000103b00001000100010001000300011217050602040002071003010a001a0e else 0x300030003000500030003000300030043000300030003000100010003000300030003000300030000060c0000010300110000150c) else (if i < 231 then 0x30268000002680000000403 else 0x30000000300bb0003000300030003000300030003000100030003000300030003007b001103b000030005000300030003000300030003000c1605001a0707131603000000021c0f))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x3026002600200000403 else 0x30000026802680000000403) else (if i < 235 then 0x3000300030003000300030003000300010003000300030011000300030003000303b003b000030003000300030112050209150d000301030b00180d else 0x3000005d005d00000000403)) else (if i < 238 then (if i < 237 then 0x3000005da05da0000000403 else 0x30003000300030003000100030003000300030003000100030003001100110003000300030003000303b0000300030003000300100c1313021607091001000201001b0f) else (if i < 239 then 0x4fc00bd00bd006d006d005d000300030005006d03b000bf006d006f006d006d00bf00030003006d006d001100bd0003006d006d00bd0003006d006d00bd007b006d006d006d0000211915181800170011181400080f07160600022413 else 0x30003000303b000030003000300430003001100010003000300030003000300030003000300030003000300030003000300030000000b190b09130b00140b0407000a021d11)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x10001003d0003006d00010001000100c103b000030003000100010035000300010011000100010001000300010001000100010013040d00110d1800040402000000001c10 else 0x30003000300050003000300030003000300030003000300030001000300030003000300030003000d000c000a050300000000150c) else (if i < 243 then 0x100a9001100a9003d0003001100110011001100030011001104c8001100a9001100110003001100a900c500a900110011003d0003001100c3001100050043000103b000a9000300111d1a011f19001512220b1e181e0a01070d080803002715 else 0x150000000300150005001500150075000d006f0544006d001505380003001500af0015000500150051001500150003002704400015000300150540001503b00003001700200015053a001500150015001522251d061b00211b211900001002000d0a05191409012916)) else (if i < 246 then (if i < 245 then 0x260000000000000000300000260000000000000000807 else 0x3000303b000010003000300030003000300030003000300030027000300050003000300030005000300030003000300030c040c0b10131300000303000201011b0f) else (if i < 247 then 0x50005000500030005000500690005000b0544000500630003001503b00005000100c70110000500050005000500150005001500230005000b00150005001500400005000100bf0003000500050005230223160d0f221b0600001b03011f230022111f17142916 else 0x30260026000000000000403))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x260026001a8003b0000000000010000000605 else 0x30260026000000000000403) else (if i < 251 then 0x10000026002600000000403 else 0x2600260000300000068000000000504)) else (if i < 254 then (if i < 253 then 0x26002ca02c402500250025002c0026802c802500250025000090006000300000d08 else 0x3000101) else (if i < 255 then 0x2600050000000050000026001000000000605 else 0x34202f003400260000302f4000000010101000705)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x30250033002e402600260026002e003b00332026002600260000900060b0300000e08 else 0x30260026000000000000403) else (if i < 259 then 0x3000101 else 0xb00f0026000000260000200000504)) else (if i < 262 then (if i < 261 then 0x3000101 else 0x30260026000000000000403) else (if i < 263 then 0x2600000000300000260000000000504 else 0x300030000004300030003000300030005003b00030003000300c900030003000300030003000300030005010d0002000300000500150c))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x302600108000000000504 else 0x1302600001000303) else (if i < 267 then 0x260000000030000000303 else 0x26002600000026002600260000302600000000000000906)) else (if i < 270 then (if i < 269 then 0x260035007d002e002e002e002c005d0035202e002e002e000090006000300000d08 else 0x3000101) else (if i < 271 then 0x2600350035403300330033002ca05da080803300330033000090006000300000d08 else 0x3000101)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x3b00010003003b0003003b003b0003003b00030005003b0001000101b803b0003b003b003b0003003b003b003b0003003b0713000104000903070d080600031a0e else 0x3000000030003000300030005000303b00003000300030003004300030003007b000300c900030003000300030003003b051400030811000b010201000b0a190e) else (if i < 275 then 0x1000103b0006d0001000500010003006d00010001003500cb00010001000100010001006d00a90001000303b00003000100010001000100000d150006050c00150d00001200021d10 else 0x1000005d005d00000000403)) else (if i < 278 then (if i < 277 then 0x3b00003000303b00003000000030003000300030003000300030003000300030003000300780003000300430003000100030003000300030000000300030f16181105000f130803020001020000001f11 else 0x5d0000300ec05d00000000000000000000605) else (if i < 279 then 0x43006f00430003000500430043006f004300430043000100430043004303b0006f000303b0004303b0000000430043000300430043004310001b0d0d040d09020004020001001c0f else 0x30000000000030001000300030003000301e0000500030003000301e8000300030003000301ec000301e200030003000300030003000300030003060f060d000912000503110a02061000031e11))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x3000306580003000300cd065a000100cd000303b0000300030003000300030003065403b000030650001300cd00030003000300030003000300030003000305180014171402120b0c0400091110070200032213 else 0x6b0000006b40000000303) else (if i < 283 then 0x300030003000300030003000300cd0003000303b000b500030003065a00030001000300030000000300030003000300030018051605140002070000050002190e else 0x15069400150015000500150015001500130003040000030580001306500003066c0003001500cf001500150015001500150015000303b0066e006f0003006d001500000015001500150015001a1d1e00160a1000000c0f00011b0200040a002614)) else (if i < 286 then (if i < 285 then 0x3000300030007000300030003000b0003000d03b00063000300050003000300030000000300030003000300030001000300080d150a140002090000090002190e else 0x3000000030003000300050003000100030003000300030003000300a00003000000030003000300050003000316060300050301010002000001170d) else (if i < 287 then 0x300030003000300050003000300030003006f00030003000000030003000000030003000300010003000308060600050301010300000000160d else 0x300030001000300030003000303b0000300030013000100030003000300d100010674000300030003000300030003004300030003000a00100406030e080406010200041c0f))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x658000303b000cd0003000300030003000300cd000300cd0003000100030003000300030003000300030003000300030003000300030011000300370011000300030000000300cd1b120c121d18171400161500060f11000000032413 else 0x300030003000300030003000300030005000303b003b0000b0003000d00000003000300030003000700030003000317101109010907060005030004180d) else (if i < 291 then 0x3000b0003000500030003000300030003000300030007000303b0000d0003000d0000000300110003000300030003000300030003160e060d080004010707050a0002001b0f else 0x300030001000b0031004b000500d3003500030007004b000303b000010003003d0003004b0000004b0000004b004b004b004b004b0d0c040d02000308070706070001001b0f)) else (if i < 294 then (if i < 293 then 0x3000000cd0003000303b0000300030003007b0003000300030003000300030007000300d5000300030003000300030003000d0408000d0005000b0005000b00030003000300030003000300001922000c13050008110300110f16000314012614 else 0x30003000100030003000100030000000300030003000300030003000300050003000300030003000300040c09000d0b0300000000150c) else (if i < 295 then 0x3000300030003000300050003000303b000010005000500000003000300030003000300030003000300030005000309010f00080600040503000700180d else 0x300810015001500510015001503b0000b007500050015008500050003043800030005001500150110003d000500070015002700030031000b0005001500370014001500150015005100d7000301140007002700100057081000150000007500152c032722001e241a271823150012220b000f0300000e00200700311a))) else (if i < 300 then (if i < 298 then (if i < 297 then 0xb000301100001000b000b0005000b000b03b0000b000b0003000b00150003000b000303b00003003500af0000000b000b00d30001000b0003000b000b1a1b0000190d0b1114120c0103000305001f11 else 0x300030003000300030003000103b0000500030003000000030003000300030003000300030003000300030003000309070f010704000b0400000003180d) else (if i < 299 then 0x300010003000300030005000300010005000100db0001000103b0000100d900010000000500010005000100010001000100010d0d060a0a080404010002070402001b0f else 0x30003000300030001000300030003000503b0000300030000000300030003000300cd00030003000300030003000304010f0b0907000e0700000005180d)) else (if i < 302 then (if i < 301 then 0x30003000300030003000100030000000300030003000300050003000300030003000300030003000300040c09000d0b0300000000150c else 0x3000300030003000b0003000300030003000503b0000300030003000b04180003000d0005000300030003000700030003000300070003000d00030000000300030003000300031b1a00140f1918090a001016090e03030101012413) else (if i < 303 then 0x11000300cd000d0003000300030003005d00050003000300030003000300030003000303b003b000030003000300cb007b00030003000000350003000319120010110a0102171304000804010e001f11 else 0x4300030003000300dd003b000300050003000303b000030000000300000003000300030003000300030003000300030003000b0e07090000040a0900030007190e)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x301d8000300030003000300050003000301dc0003000300030003000300030003038003b0000300030003000300030003000100000000000300031a120000180c0a1109070c000704010d001e11 else 0x30003003b00030003000100030000000300030003000300050003000300010003000300030003000300040c09000d0b0300000000150c) else (if i < 307 then 0x1003500010005003500bf03b000df0035003500e1000300350003000300030035000303b003b00035003500d3003500000035003501c80003003500351d18000012100e1716080f0107040109001f11 else 0xf000d000300050260026800030001000b03b000050001000303b000030003000500030003000303b005d0000300110007000103b00003000505da0013000305d4000300030003000300030001000303b00003000300030001000300030003000300010003000305d803b032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else (if i < 310 then (if i < 309 then 0x3006f0003000300010003000303b0000303b0006f0001000300000003000300030003000303b000030003000300030003000300031717060414090012060004090901031b0f else 0x3000300030003000303b00003000303b0000100030003000300030003000500030003002100e300030003000300000000000300030003000300030c0f0a0f0900130700000a0604020000021e11) else (if i < 311 then 0x3000303a00003000300030003020803b0000300030003000500030003000300cd020c00030003000000000001000308280003000300030003000300031d140e120b00001a0400090702060011051f11 else 0x3b0000300cd00030003000300030003000300030003000503b001f803b0000300030003000300030003000300030003000300050001000300030016030d0009000b00120b00000500081e10))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x50003000300d30003000300cd0398000300030003000303b0000303b00003000300e50043000d000300cd03b000030003000300030077007b00b8000300030003000315132012030d1900110b09070506030f0201002313 else 0x300030003000300030003000303b00003000300030003000303b003b0000303b00003000303b0000300030003000503b000030000000100030003000300030003001f001a151d130c1002000910070e0008042112) else (if i < 315 then 0x2140278040005e0040006ca040000050614000500300019000504000015001500050005001500050005000500050015001d0015000500050400001b0005001d00050057002100050015001f000506c800050005001b000b00050005000500050005002306a00005040000050005001920001a002b000f371a2a083628350734013312321431262f241b00102203391e else 0x5000d008300050240029800830005000b04100005000100830410008300830005008300830083041005f0008300050007000104100083000506ea0013008305f4008300830083008300830001008304100083008300830001008300830083008300010083008306e8041032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else (if i < 318 then (if i < 317 then 0x13a02300003043006fa0288043006000003057a057806da000306f808380430043000030003000500030007000300010001000300030138001300030003001100050604000300010003000300030001000300010003000f00010430000300030003000d0005000306d8000300030003000b00050003043000032500370023000000143b3a390e37343607351c2d0031302c1f1b150f1a082b013e20 else 0x3000300030003000000030003000300cd0003000300cd0003000300030848000300030430000300030003000a00040001000b00020100160c) else (if i < 319 then 0x21001b0400002100210005002100510025001500e700eb002100e900000021002100210021002100210021002104060400060206000500010200170d else 0xef000000150005001300010015001500370015041000f100ed00f3001500ed001500ed001500c0009100910015001500150015001500150d0b030008140006050005010003021c0f)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x2a004c0032c04c005c0000504c007300003000300070003000504c007f40001000300010003000300030001000300030740000f00030003000504c00003000300030003000100030003000d000300010003000300010013000b00030003000300030003000507420011073204c0000321001f001b000e37183607352f3406332b311330002a1629281a0f022701391e else 0xf000d0003002702b0030e00030001005304f000270001000304f000030003001d00030003000304f005b2000300110007000104f000030027070e0013000307c6000300030003000300030001000304f000030003000300010003000300030003000100030003075204f032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d) else (if i < 323 then 0x6d00ad005d0011000f000f000f04c00000000f00f5000f000f000f000f000f00f7006f000f000f000f000400070002040500030400150c else 0x5d0000f00000000000303)) else (if i < 326 then (if i < 325 then 0xf000f000f001304f00000006d00e700ef004300f9004300fb000f000f0043000f000f000f000f000f000f000f03010001060005000404010200170d else 0x2d00540054005900540072e000d056000270540000d031c000d0007079400270027000d000d000d0015000d0015000d000d002707a40027000d000d001500570540000d0015000d0027000d000d000d072c000d006100fd000d0051000d000d002b0045000d000d00150164000d0540000d22001e002d0008381c37002d1a36053529341533112f282a26180d1012013a1e) else (if i < 327 then 0x505d00000000303 else 0x7054000070007007f0174001500000840001500ff0007001500070007000700270007000700070007000700070b020301020004010703000105170d))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x5d007720003062005d007700000000008500003000100000906 else 0x300030003003700030003001b00030003000300030003000307800003088000030650065000030003065000030003000300030782000300030003000300031517190b1004100e13020c000d0c000200002112) else (if i < 331 then 0x5d00003086005d0000200000504 else 0x305d0000005d00000000403)) else (if i < 334 then (if i < 333 then 0x3000005d005d00000000403 else 0x5d0000305d000000100000403) else (if i < 335 then 0x305d005d00000000403 else 0x5d00000000b05a005d0000300000504)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x3000101 else 0x10000000005d005d0000000000504) else (if i < 339 then 0x5d005d0000000000003000100000504 else 0x305d005d00000000403)) else (if i < 342 then (if i < 341 then 0x302e0033c087005d005d005d003b00760076205d005d005d0000900060a0300000e08 else 0x5d0000305d000000100000403) else (if i < 343 then 0x3000101 else 0x5d005d00003015c0000000000000000000605))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x5d0000000130000000303 else 0x5d00003000005d00100000403) else (if i < 347 then 0x5d0000305d000000100000403 else 0x5d00001000005d00100000403)) else (if i < 350 then (if i < 349 then 0x705d001840000000403 else 0x5d0000005d005d005d0000305d005d000000001000100000906) else (if i < 351 then 0x30037001100150015022002f000370037001500030003065000030003000300030003065006500003000f034c0003003700030650000300030015077e0650000300030003001b001506b0000300150003000300030003000300370003001b00030854003700030003077c065033312f2c302b31132a28300e2422201b1c29180c230d05091716010200381d else 0x51009301940051001500430051001100150650005100250580005100000015005100510051005100150051001b0051005100510051000009000006050e10000a090a01031b0f))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0x35005da089007600760076005d0035e089c07600760076000090006000300000d08 else 0x5d005d4089008700870087007d00800089208700870087000090006000300000d08) else (if i < 355 then 0x3009008b000700090008000900003000300030005000300900003000100b00790000100540003009008b000e000900003005000030003048c00030005000900010003000300070003000300900003000d000300030011000300c00003003a000304880001000307b8000300030003000f00a000030005000300b4000300600003000300900005000b00030003000300030003045000030001009000030422089a0003000100d0000500900090000154004c003c004b00240048001f53445245003a5444533552335130481c31172a11150c1a000a2b4106400f072901592e else 0x3013001100110010e011001200003000300030005000307a001100110000108b001000110011008b0014000030042000300030056012e013e0003042c00030005001300010003000300070003000301100003000d0003000300110003014e000300580003047a0001000307ae000300030003000f01100003000500030001000301100003000300030005000b0003000300030003000304200003000108460005004800010001000304720110000354004c003e004b0022553a001d004800475438461354335331522e511a4a153c0f440a42042f2928001c0d082701592e)) else (if i < 358 then (if i < 357 then 0x1e0099e00150015019008b00170000501f000050019002300050005000b0015000500050200019009d40180019007c80190019001600005001d019000050462000501900005001704280005001d01e2019000100005000502100005001b00300015099c01f2001501a008b00015000501c0000500050005000500520005000500050005001f0015000500050920000500050190019004e00005001b0790000500210005000501b0000500050005088c000504600019001b01d00005005001900005565f405e5b0052005a0051004f004d003d00255a3a59365a324d144b2d470f2845161e58254822340b38062e1c01190900436232 else 0x33004a2098a03000350016402d00310016003200040030402d008b002b002d002d002c0042c0015001008b002d0000502f002e00930034002d0031402d00332034204a0000500250005000500270015000500270005098802d00005006807f0085808e80005004200050005000500190025000500050005000500070005000500190027000500050023000b0005000503240005042802d000250005001702d0000500050005001500050025001f000500050005001509480005000502d000050015000500050005000528005900246362613d5f575e3a00000020005c001c005c00005618551353514e375d4d480e4932060b4730462d44423805331b156634) else (if i < 359 then 0x3040000050003000100050003019802d8042000030420042008b004400420042008b00434000100030003000b0007000106a004100003000304200003000f00030003000300030001080a042000130003000300030003043000030092000306c0000300030003011400030420000306a407d804200003000d0420000101100003000300050860001100010003000542002d003f003b0042001d463d3e1a2d1521101b003b0c392b37293502112e002200240e060a4926 else 0x51202b005d001020540064005f0007005600580052205000550058001040524010602c805a005c00580066005e0053005260174058003e8040208b005d204f00644017003ba03b8059004c005b005c20580051001000418041c007205b4050405a4052003ec04000662058032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x3060000050003000300030003002b0029000b0003002906840088000004d00029001106800614000300100003000500030690000300030003060205f003ca000305580003000303c800030003065000030005069205f000030003000f0007002d05f00003000300030654063008700003002909100188000303fc000304f0057000050003000305f00005000306700620002f002f000305f0000300290798008c061005f000290003000300290003018a03f805f00003067200035a4f585957554b445553231f53514c4a514e463d28451e433f3d3c380b3736180331161032300e082c2a280719250100115f31 else 0x42c06a008b006a0042006a008b006a0052e06a006b00228022608ae08a009c606a009a809c806a005200001036c06e4003f0005013006be013e000109a406a00001036406e80762000100010001000d00050001003500050001000106a000010037004109b600010001000100010001000d000100010001000b001100010001003d06a000010029000100010005000109b80001000100310001003b06a0003300010005000100010001000100390007000f00010001003331004c002e004a00205a59581c5748002b56555418474654265343522551424b06403e3c00383b2d1229371a0c13360d5d30) else (if i < 363 then 0x3003b004500030003003b000b0011003b000309fa000300050003030a030809f800030003035800030003000306c008b0000305680005000300030003000306d0000700030043000500030758003b00030003000300030003000300050003000309e806c00422000106c004b806c0000306c000f009ea00030003000300030420000306c006c00900000300030003003b053006c008c006c0000f08b0001306d402340230000306c00003000306e006e4003b06c0574c0055555555515151514d45002f4b4a46441b11442541403c213b3a3606353431002e1f1c18150a120e2b2904285c2f else 0x8b007820b6a00340003078c0b64003807800b680570003707000003004700030003003700030015000300370037003700030003000300030003000f000300030788079800150700001100030a14000300150a18000300030578000300030003000300030700000300030047071006f0003007000b60070000030a08000300030037000307180003001500150003000300030700004707000a00003700030790000307000a0a0003070008b0003a00150a1a0700070000030a1000030a0400033a5b505c055b4d5a58004c5837574956490044553454455531534333412d2c28201440132a0e190d1e241801123c00220c066132)) else (if i < 366 then (if i < 365 then 0x90001508620015019405900003009200030800000305f807900003004d004b0003086007900790079000030a40001508b00790079008b007900ada000307900003019008040015004f0a440ad8000300150003000307900003000308d00003079000030700003f0051001500030003000300030003000300030003001500030003004b0015001500490003000300031a4444003c424200064018420f3b3700133d323c37330d31302b082a29280122241c002120174926 else 0x30b500003000b000300030003000100010003001309100b000001000d000302400003083c0001026c00010820000305a000030003000307d000030146000f07d000030005000300050003000500030003000300030001000302420003000300030003083e07700428000509b0000307d0001509e0000307d000030144000307d00001001000030a5000200a8c0011081c000300050310000307d0000307e00b40000300cc0ae4000309b2000307d00003074401c005cc00010a8e5a4f594d584a005856485755534654524d444200352d452e412829403d11023c250c193910360035212f0a321d221714065f31) else (if i < 367 then 0x1d408a2042c080008b008000b7401500051080002a40800072808a0060808f005b0000b07900800001508b00a70000b09f40800000b03700380039008000b44000b08000053000b00150059000b000b000b000b08c8000b0051000b0af8000b000b000b000b08000958015201b40afa005b000b000b000b0015000b0057000b0053000b0800000b000b000b000b000b000b000b00150051000b0015000b0800005900150015000b000b000b000b0051000b0015000b000b005536245a0033580000205756551c54520030520000184c54532b524b512a4e483e064645430025421a123d3c3b0c2e130d5e30 else 0x1700030057000300030003003d003908a4000303a800030900003d00a2003d08a000030003032808b00003003d00030860004f00030003001700030039061800030003003900030003003d0003003d097809cc003d029e00d200030420000308600003000305d00003086003d2073800030b78000300030860000300030aa008fa005d0017000308600860005708600003000308600968000300030aa408600860003d029a0003079000030b08003d0b3a08b00057000309c808603352005b59500059574e58564d2f5649444a2d00492c2a464525272016083e4221021e3f183c051500390f380d37071a0e5f31)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x6a60194080a02d00580058807da009c080008b006c806a205f008b0009208600190011405f807d008b00ac0080806a40804009808b0009004280aca086804220ac4070002d801160798019a086c07d808b006c001100790042c019808d0086207d406a0011204200ac808b032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d else 0x28208f8028c0280079808d0000308d000030620000308b008d008b008d0028808d0062808d00b2a0b2400030003006100030003005108f0096409680003000308fa00030003000304900003004f000300030790071008d0071808d00b200003005f004100410003000300030041000300410003000308d00003000308f40960096a004108d00b28005f004100030003000300030003005f0003004d08d00003000300030021002500030003000300030051005100410003425700003f56000026550000223c0000395400001e3755543452514b334a532e062d2b4900482c2012471a190c18130d5d30) else (if i < 371 then 0xaa2027c0af20214064008b00a800a000a900ac00a7006b206500ac002520ab00a3000b207d0067c0ac0066c0af00aa00a6000e80ac002500a400b800b2004320b900a20034c00b00ad001fe0b300a820ac006d001200a50044c01fc0b100ab20ae006b0012204300b820ac032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d else 0x76002400ca00300050005800ba000c00c000e000880072006000e0000200d000200014006800b000e0010000c8007400c4000800e000000048010a00d80042010400900038001600a8002a00dc00b800e00080001000a0004c002800f000d200b4007000120040010800e032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else 0) else 0)))) else 0))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 24
  | 6 => 138
  | 7 => 186
  | 8 => 17
  | 9 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 30
  | 7 => 168
  | 8 => 354
  | 9 => 371
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+16*((h/a+d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with

  | 1 => ws.map (blockWord 24 [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14])

  | 2 => ws.map (blockWord 24 [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13])

  | 3 => ws.map (blockWord 24 [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12])

  | 4 => ws.map (blockWord 24 [4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 13, 15, 8, 10, 9, 11])

  | 5 => ws.map (blockWord 24 [5, 7, 4, 6, 1, 3, 0, 2, 13, 15, 12, 14, 9, 11, 8, 10])

  | 6 => ws.map (blockWord 24 [6, 4, 7, 5, 2, 0, 3, 1, 14, 12, 15, 13, 10, 8, 11, 9])

  | 7 => ws.map (blockWord 24 [7, 5, 6, 4, 3, 1, 2, 0, 15, 13, 14, 12, 11, 9, 10, 8])

  | _ => ws

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 192) (goal 192) s ws) : NatRun (mask 192) (goal 192) s (rotateE g ws) := by
  unfold rotateE

  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 192 stateE nsE actionE sixE rotateE s




theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 2 0 = true := by decide +kernel

theorem z4 : span (Z 4) 2 0 = true := h4y0

theorem h5y0 : span (Z 5) 6 0 = true := by decide +kernel

theorem h5y1 : span (Z 5) 6 6 = true := by decide +kernel

theorem h5y2 : span (Z 5) 6 12 = true := by decide +kernel

theorem h5y3 : span (Z 5) 6 18 = true := by decide +kernel

theorem z5 : span (Z 5) 24 0 = true := (@span_join (Z 5) 12 0 12 (@span_join (Z 5) 6 0 6 h5y0 h5y1) (@span_join (Z 5) 6 12 6 h5y2 h5y3))

theorem h6y0 : span (Z 6) 6 0 = true := by decide +kernel

theorem h6y1 : span (Z 6) 6 6 = true := by decide +kernel

theorem h6y2 : span (Z 6) 6 12 = true := by decide +kernel

theorem h6y3 : span (Z 6) 6 18 = true := by decide +kernel

theorem h6y4 : span (Z 6) 6 24 = true := by decide +kernel

theorem h6y5 : span (Z 6) 6 30 = true := by decide +kernel

theorem h6y6 : span (Z 6) 6 36 = true := by decide +kernel

theorem h6y7 : span (Z 6) 6 42 = true := by decide +kernel

theorem h6y8 : span (Z 6) 6 48 = true := by decide +kernel

theorem h6y9 : span (Z 6) 6 54 = true := by decide +kernel

theorem h6y10 : span (Z 6) 6 60 = true := by decide +kernel

theorem h6y11 : span (Z 6) 6 66 = true := by decide +kernel

theorem h6y12 : span (Z 6) 6 72 = true := by decide +kernel

theorem h6y13 : span (Z 6) 6 78 = true := by decide +kernel

theorem h6y14 : span (Z 6) 6 84 = true := by decide +kernel

theorem h6y15 : span (Z 6) 6 90 = true := by decide +kernel

theorem h6y16 : span (Z 6) 6 96 = true := by decide +kernel

theorem h6y17 : span (Z 6) 6 102 = true := by decide +kernel

theorem h6y18 : span (Z 6) 6 108 = true := by decide +kernel

theorem h6y19 : span (Z 6) 6 114 = true := by decide +kernel

theorem h6y20 : span (Z 6) 6 120 = true := by decide +kernel

theorem h6y21 : span (Z 6) 6 126 = true := by decide +kernel

theorem h6y22 : span (Z 6) 6 132 = true := by decide +kernel

theorem z6 : span (Z 6) 138 0 = true := (@span_join (Z 6) 96 0 42 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 (@span_join (Z 6) 6 0 6 h6y0 h6y1) (@span_join (Z 6) 6 12 6 h6y2 h6y3)) (@span_join (Z 6) 12 24 12 (@span_join (Z 6) 6 24 6 h6y4 h6y5) (@span_join (Z 6) 6 36 6 h6y6 h6y7))) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 (@span_join (Z 6) 6 48 6 h6y8 h6y9) (@span_join (Z 6) 6 60 6 h6y10 h6y11)) (@span_join (Z 6) 12 72 12 (@span_join (Z 6) 6 72 6 h6y12 h6y13) (@span_join (Z 6) 6 84 6 h6y14 h6y15)))) (@span_join (Z 6) 24 96 18 (@span_join (Z 6) 12 96 12 (@span_join (Z 6) 6 96 6 h6y16 h6y17) (@span_join (Z 6) 6 108 6 h6y18 h6y19)) (@span_join (Z 6) 12 120 6 (@span_join (Z 6) 6 120 6 h6y20 h6y21) h6y22)))

theorem h7y0 : span (Z 7) 6 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 6 6 = true := by decide +kernel

theorem h7y2 : span (Z 7) 6 12 = true := by decide +kernel

theorem h7y3 : span (Z 7) 6 18 = true := by decide +kernel

theorem h7y4 : span (Z 7) 6 24 = true := by decide +kernel

theorem h7y5 : span (Z 7) 6 30 = true := by decide +kernel

theorem h7y6 : span (Z 7) 6 36 = true := by decide +kernel

theorem h7y7 : span (Z 7) 6 42 = true := by decide +kernel

theorem h7y8 : span (Z 7) 6 48 = true := by decide +kernel

theorem h7y9 : span (Z 7) 6 54 = true := by decide +kernel

theorem h7y10 : span (Z 7) 6 60 = true := by decide +kernel

theorem h7y11 : span (Z 7) 6 66 = true := by decide +kernel

theorem h7y12 : span (Z 7) 6 72 = true := by decide +kernel

theorem h7y13 : span (Z 7) 6 78 = true := by decide +kernel

theorem h7y14 : span (Z 7) 6 84 = true := by decide +kernel

theorem h7y15 : span (Z 7) 6 90 = true := by decide +kernel

theorem h7y16 : span (Z 7) 6 96 = true := by decide +kernel

theorem h7y17 : span (Z 7) 6 102 = true := by decide +kernel

theorem h7y18 : span (Z 7) 6 108 = true := by decide +kernel

theorem h7y19 : span (Z 7) 6 114 = true := by decide +kernel

theorem h7y20 : span (Z 7) 6 120 = true := by decide +kernel

theorem h7y21 : span (Z 7) 6 126 = true := by decide +kernel

theorem h7y22 : span (Z 7) 6 132 = true := by decide +kernel

theorem h7y23 : span (Z 7) 6 138 = true := by decide +kernel

theorem h7y24 : span (Z 7) 6 144 = true := by decide +kernel

theorem h7y25 : span (Z 7) 6 150 = true := by decide +kernel

theorem h7y26 : span (Z 7) 6 156 = true := by decide +kernel

theorem h7y27 : span (Z 7) 6 162 = true := by decide +kernel

theorem h7y28 : span (Z 7) 6 168 = true := by decide +kernel

theorem h7y29 : span (Z 7) 6 174 = true := by decide +kernel

theorem h7y30 : span (Z 7) 6 180 = true := by decide +kernel

theorem z7 : span (Z 7) 186 0 = true := (@span_join (Z 7) 96 0 90 (@span_join (Z 7) 48 0 48 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 (@span_join (Z 7) 6 0 6 h7y0 h7y1) (@span_join (Z 7) 6 12 6 h7y2 h7y3)) (@span_join (Z 7) 12 24 12 (@span_join (Z 7) 6 24 6 h7y4 h7y5) (@span_join (Z 7) 6 36 6 h7y6 h7y7))) (@span_join (Z 7) 24 48 24 (@span_join (Z 7) 12 48 12 (@span_join (Z 7) 6 48 6 h7y8 h7y9) (@span_join (Z 7) 6 60 6 h7y10 h7y11)) (@span_join (Z 7) 12 72 12 (@span_join (Z 7) 6 72 6 h7y12 h7y13) (@span_join (Z 7) 6 84 6 h7y14 h7y15)))) (@span_join (Z 7) 48 96 42 (@span_join (Z 7) 24 96 24 (@span_join (Z 7) 12 96 12 (@span_join (Z 7) 6 96 6 h7y16 h7y17) (@span_join (Z 7) 6 108 6 h7y18 h7y19)) (@span_join (Z 7) 12 120 12 (@span_join (Z 7) 6 120 6 h7y20 h7y21) (@span_join (Z 7) 6 132 6 h7y22 h7y23))) (@span_join (Z 7) 24 144 18 (@span_join (Z 7) 12 144 12 (@span_join (Z 7) 6 144 6 h7y24 h7y25) (@span_join (Z 7) 6 156 6 h7y26 h7y27)) (@span_join (Z 7) 12 168 6 (@span_join (Z 7) 6 168 6 h7y28 h7y29) h7y30))))

theorem h8y0 : span (Z 8) 6 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 6 6 = true := by decide +kernel

theorem h8y2 : span (Z 8) 5 12 = true := by decide +kernel

theorem z8 : span (Z 8) 17 0 = true := (@span_join (Z 8) 12 0 5 (@span_join (Z 8) 6 0 6 h8y0 h8y1) h8y2)

theorem h9y0 : span (Z 9) 1 0 = true := by decide +kernel

theorem z9 : span (Z 9) 1 0 = true := h9y0

theorem checkedE (s : Nat) (hs : s ≤ 9) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 192) (goal 192) s xs1004) : False := by
  have h10 : NatRun (mask 192) (goal 192) 9 xs1004 := extend_run h hs
  have p : xs1004.Perm (stateE 9 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 9 (by decide) 0 (by decide) (Run.perm p h10)



end PEqualNP.Outside.L_meta_982_aux.Base
open PEqualNP.Outside.L_meta_982_aux.Base in
theorem PEqualNP.Outside.L_meta_982_aux.Base.barbell_lower : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)) 9 := by
  exact main1004 noRunFull


namespace PEqualNP.Outside.L_meta_982_aux.Relabel
open PEqualNP.Outside.L_meta_982_aux.Base
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this


end PEqualNP.Outside.L_meta_982_aux.Relabel

namespace PEqualNP.Outside.L_meta_982_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def shard21 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)

def perm21 : Fin 7 → Fin 7 := ![2,0,1,3,6,4,5]

def barbell (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)

theorem shard21_lower (s : ℕ) (h : HasCircuitSize 7 shard21 s) : 11 ≤ s := by
  by_contra hs
  have h10 : HasCircuitSize 7 shard21 10 := by
    obtain ⟨C,hC,hsize,heval⟩ := h
    exact ⟨C,hC,by omega,heval⟩
  have hr := Relabel.relabel_size perm21 shard21 10 h10
  have hd : ∃ x : Fin 7 → Bool,
      (fun y => shard21 (y ∘ perm21)) (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠
        (fun y => shard21 (y ∘ perm21)) x := by
    refine ⟨![true,false,false,false,false,false,false], ?_⟩
    decide +kernel
  have hn : ∃ y y' : Fin 6 → Bool,
      (fun x => shard21 (x ∘ perm21)) (Fin.snoc y false) ≠
        (fun x => shard21 (x ∘ perm21)) (Fin.snoc y' false) := by
    refine ⟨![false,false,false,false,false,false], ![true,true,false,false,false,false], ?_⟩
    decide +kernel
  have he := Base.gate_elim 6 (fun x => shard21 (x ∘ perm21)) false 9 hd hn hr
  have hf : (fun y : Fin 6 → Bool => shard21 ((Fin.snoc y false) ∘ perm21)) = barbell := by
    funext y
    revert y
    decide +kernel
  rw [hf] at he
  exact Base.barbell_lower he


def case0 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)

def perm0 : Fin 6 → Fin 6 := ![2,0,1,3,4,5]

theorem case0_lower (s : ℕ) (h : HasCircuitSize 6 case0 s) : 10 ≤ s := by
  by_contra hs
  have h9 : HasCircuitSize 6 case0 9 := by
    obtain ⟨C,hC,hsize,heval⟩ := h
    exact ⟨C,hC,by omega,heval⟩
  have hr := Relabel.relabel_size perm0 case0 9 h9
  have hf : (fun y : Fin 6 → Bool => case0 (y ∘ perm0)) = barbell := by
    funext y
    revert y
    decide +kernel
  rw [hf] at hr
  exact Base.barbell_lower hr

def case17 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)

theorem case17_lower (s : ℕ) (h : HasCircuitSize 7 case17 s) : 11 ≤ s := by
  by_contra hs
  have h10 : HasCircuitSize 7 case17 10 := by
    obtain ⟨C,hC,hsize,heval⟩ := h
    exact ⟨C,hC,by omega,heval⟩
  have hr := Relabel.relabel_size perm21 case17 10 h10
  have hd : ∃ x : Fin 7 → Bool,
      (fun y => case17 (y ∘ perm21)) (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠
        (fun y => case17 (y ∘ perm21)) x := by
    refine ⟨![false,false,true,false,false,false,false], ?_⟩
    decide +kernel
  have hn : ∃ y y' : Fin 6 → Bool,
      (fun x => case17 (x ∘ perm21)) (Fin.snoc y false) ≠
        (fun x => case17 (x ∘ perm21)) (Fin.snoc y' false) := by
    refine ⟨![false,false,false,false,false,false], ![true,true,false,false,false,false], ?_⟩
    decide +kernel
  have he := Base.gate_elim 6 (fun x => case17 (x ∘ perm21)) false 9 hd hn hr
  have hf : (fun y : Fin 6 → Bool => case17 ((Fin.snoc y false) ∘ perm21)) = barbell := by
    funext y
    revert y
    decide +kernel
  rw [hf] at he
  exact Base.barbell_lower he

#print axioms case0_lower
#print axioms case17_lower

#print axioms shard21_lower
end PEqualNP.Outside.L_meta_982_aux

-- The C7 certificate below is adapted from accepted L_meta_611 (8ebf8f1).
open PEqualNP.Outside.L_meta_982_aux.Base
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_982_aux.Cycle7
abbrev fG : BFn 7 := (fun x : Fin 7 → Bool => ((x 0 || x 1) && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1))

def circuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.and,[7,2]⟩, ⟨.or,[0,4]⟩, ⟨.and,[9,3]⟩,
    ⟨.or,[4,6]⟩, ⟨.and,[11,5]⟩, ⟨.and,[6,1]⟩, ⟨.or,[8,10]⟩,
    ⟨.or,[12,13]⟩, ⟨.or,[14,15]⟩], 16⟩

theorem upper : HasCircuitSize 7 fG 10 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

-- Each successor must fail a necessary condition or match a state in the next layer.
def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

end PEqualNP.Outside.L_meta_982_aux.Cycle7


namespace PEqualNP.Outside.L_meta_982_aux.Cycle7
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- Corresponding positions in the two halves are negative and positive assignments.
def rowsG : List ℕ := [1, 4, 19, 35, 42, 44, 76, 81, 84, 2, 4, 19, 35, 42, 44, 76, 81, 84, 3, 3, 10, 12, 10, 12, 18, 20, 19, 33, 36, 34, 36, 35, 33, 40, 35, 42, 44, 42, 44, 16, 19, 32, 35, 42, 44, 76, 81, 84, 17, 33, 18, 34, 19, 35, 20, 36, 40, 42, 44, 19, 32, 35, 42, 44, 33, 34, 35, 36, 68, 42, 44, 1, 8, 19, 81, 84, 76, 44, 35, 42, 16, 8, 19, 81, 84, 76, 44, 35, 42, 17, 17, 20, 12, 20, 12, 18, 10, 19, 65, 72, 80, 72, 81, 65, 68, 81, 84, 76, 84, 76, 2, 19, 64, 81, 84, 76, 44, 35, 42, 3, 65, 18, 80, 19, 81, 10, 72, 68, 84, 76, 19, 64, 81, 84, 76, 65, 80, 81, 72, 40, 84, 76, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 11, 11, 13, 14, 14, 22, 22, 23, 37, 37, 38, 38, 39, 41, 41, 43, 43, 45, 46, 46, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 50, 50, 51, 51, 52, 52, 56, 58, 60, 96, 96, 96, 96, 96, 97, 98, 99, 100, 100, 106, 108, 9, 9, 9, 9, 9, 9, 9, 9, 9, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 21, 21, 13, 28, 28, 26, 26, 27, 73, 73, 88, 88, 89, 69, 69, 85, 85, 77, 92, 92, 66, 66, 66, 66, 66, 66, 66, 66, 66, 67, 67, 82, 82, 83, 83, 74, 74, 70, 86, 78, 96, 96, 96, 96, 96, 97, 112, 113, 104, 104, 116, 108]

def xsG : List ℕ := [0xa0066003f387803fe1400cc007e70f007fc29419a282c6068c4685283345058c0d188d, 0xfffff000e0000009808f001b39f7ff8000042ae0c0038184c2266a3c0d2ca55c3a1c, 0xc00e0000fe01f0000160130001c3ff9fffff063801c3d007870385884c0b05052a2c562, 0xb0098000e1ffcfffff801c0001fc03e00002c42605828295162b160c700387a00f0e070, 0x4c047800d9cfbffc00001ffffe001c0000013351e069652ae1d0e000855c18007030984, 0xfff000000000000001ffffffffffe00000008000070000001c0e06ff7aa1e7ff8007038, 0xfffffffffff0000001ffe0000000000000037fbd50f3ffc00381c100000e000000381c0]

theorem rowsG_len : rowsG.length = 284 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 142 := by decide +kernel

theorem maskG : mask 142 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; rfl

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 142 zs &&& lo 142) ≠ lo 142 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 142) (goal 142) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 142) (goal 142) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 142) (goal 142) s xsG) :
    ∀ s : ℕ, HasCircuitSize 7 fG s → 10 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 142) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 7 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

-- The certificate stores state counts, lookup keys and parent moves by remaining budget.
def NN : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 55
  | 8 => 37
  | 9 => 1
  | _ => 0

def HT : Nat → Nat
  | 7 => 0xf6c4db7ae02d371fdf755047dbaf8573b7508032b726d38eb4b9e951b028d21dadcfd211abb02f65a95a4af2a2f8add3a262d6409eb466a596d2234c962f9c3687b6a5e97eacadda7449937671d3f165709b48c566ef529c639f07f05f7479fa5eb340cc55011797524b54c24cd786224c97a88d4c64b6c04a6b6b6a46a73a44452e81b243b4375a39664f263692787d2dbbb40e2cb701512b96a9e5266a7ea41ee97a181b9032861543afd91405510c13f6740a13ae2ab51340771d133bae710bcdbb850a3967bc05c18a950558dc060351118903373d7800c05b06
  | 8 => 0xe4f32979e02d371fe0162d88d0feaeddb295c46bb2020fe8b130850dafa0880caa1187c4a436f034a2f8add39dc1f2779b1ebc2a9ab9979d99c6c4159586922b82711c8a78ad98a07587f2d3709b48c56bd320476698eeb662d27319563237965069ca134db9800d4aa672c332502b812df543b22cb701512803da00266a7ea41cdb89571a9b289217fb09c80afb4451088340bb
  | 9 => 0xa2f8add3
  | _ => 0

def PT : Nat → Nat
  | 7 => 0x94d41a880893213a6e070d0129b02a221142088c404e1982437004402088852998333051e20280c856110bf3701420488000d9a80a10516202c0885f9980e1035c6c0f8d80c981942213a6c074d406110bc207844081c8847000461041400048c8458818a1067e6a03c40989283f3406660890d0029108f1045040658c85019832303
  | 8 => 0x4000220203d040fb10050001cc207d440720014010280400000073280f4001c6203d9407b080f230280a07880008000e4100a0a078840f2900e5001c4607cc40f31015020220407d40008280e5101e4203c8007a900501
  | _ => 0

def dA : Nat := 0x1fffffffffffffffffc000000000000000007fffffffffffffffff

def setA (xs : List Nat) : List Nat := xs.map (moveBits dA 71)

theorem runA {s ws} (h : NatRun (mask 142) (goal 142) s ws) :
    NatRun (mask 142) (goal 142) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)


def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 19 j
    let r := mv (mask 142) (e % 4096) (St d (s + 1) (e / 8192))
    if e / 4096 % 2 = 1 then setA r else r

def S (s j : Nat) : List Nat := St (9 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 20 0 (NN s)

def ori (zs : List Nat) : List Nat := if hk zs ≤ hk (setA zs) then zs else setA zs

theorem ori_ok {u ys} (h : NatRun (mask 142) (goal 142) u ys) :
    NatRun (mask 142) (goal 142) u (ori ys) := by
  unfold ori
  split
  · exact h
  · exact runA h

def poolG : List Nat := [0x400010a125c8e, 0x80101cfc23897, 0x1002020de238a1, 0xc02018de324b5, 0x1803008fc2d4c9, 0x1403010a125c8e, 0x1802014c925cfc, 0x100200cb5284de]

def Z (s : Nat) := bar 142 S NN idx ori poolG s

end PEqualNP.Outside.L_meta_982_aux.Cycle7

namespace PEqualNP.Outside.L_meta_982_aux.Cycle7

theorem h9y0 : span (Z 9) 1 0 = true := by decide +kernel
theorem z9 : span (Z 9) 1 0 = true := h9y0
theorem h8y0 : span (Z 8) 12 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 12 12 = true := by decide +kernel
theorem h8y2 : span (Z 8) 12 24 = true := by decide +kernel
theorem h8y3 : span (Z 8) 1 36 = true := by decide +kernel
theorem z8 : span (Z 8) 37 0 = true := (@span_join (Z 8) 24 0 13 (@span_join (Z 8) 12 0 12 h8y0 h8y1) (@span_join (Z 8) 12 24 1 h8y2 h8y3))
theorem h7y0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 12 12 = true := by decide +kernel
theorem h7y2 : span (Z 7) 12 24 = true := by decide +kernel
theorem h7y3 : span (Z 7) 12 36 = true := by decide +kernel
theorem h7y4 : span (Z 7) 7 48 = true := by decide +kernel
theorem z7 : span (Z 7) 55 0 = true := (@span_join (Z 7) 48 0 7 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 h7y0 h7y1) (@span_join (Z 7) 12 24 12 h7y2 h7y3)) h7y4)
theorem z6 : span (Z 6) 0 0 = true := rfl
theorem z5 : span (Z 5) 0 0 = true := rfl
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 142) (goal 142) s xsG) : False := by
  have h9 : NatRun (mask 142) (goal 142) 9 xsG := extend_run h hs
  have p : xsG.Perm (S 9 0) := List.Perm.refl _
  exact bar_all ori_ok checked 9 (by decide) 0 (by decide) (Run.perm p h9)

end PEqualNP.Outside.L_meta_982_aux.Cycle7


namespace PEqualNP.Outside.L_meta_982_aux
open PEqualNP.MetaComplexity

def case8 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)

def perm8 : Fin 7 → Fin 7 := ![0,2,3,1,4,6,5]

theorem case8_lower (s : ℕ) (h : HasCircuitSize 7 case8 s) : 10 ≤ s := by
  have hr := Relabel.relabel_size perm8 case8 s h
  have hf : (fun y : Fin 7 → Bool => case8 (y ∘ perm8)) = Cycle7.fG := by
    funext y
    revert y
    decide +kernel
  rw [hf] at hr
  exact Cycle7.mainG Cycle7.noRunFull s hr

#print axioms case8_lower
end PEqualNP.Outside.L_meta_982_aux

-- Exact source adaptation of accepted 722 and 517; original attribution retained.


/- The normalization, finite frontier certificate, and its kernel proofs are
by Digger-Rockwell, from public PR 801:
https://github.com/brilliant-hq/pequalnp-proofs/pull/801
Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
This file renames the helper namespace and adds the positive bound wrapper
requested by L-meta-722. The certificate data is unchanged. -/

namespace PEqualNP.Outside.L_meta_982_aux.Case23Base

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

abbrev fG : BFn 7 := fun x : Fin 7 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def rowsG : List ℕ := [72, 1, 44, 42, 42, 17, 44, 18, 18, 12, 18, 76, 18, 18, 44, 44, 42, 42, 72, 76, 42, 42, 20, 20, 18, 42, 42, 18, 18, 44, 10, 44, 18, 10, 76, 10, 10, 20, 10, 12, 44, 42, 44, 20, 20, 42, 18, 17, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 17, 20, 44, 0, 0, 1, 1, 8, 10, 12, 16, 42, 44, 44, 72, 76, 76, 4, 72, 2, 84, 81, 81, 34, 84, 33, 33, 68, 33, 76, 33, 33, 84, 84, 81, 81, 72, 76, 81, 81, 36, 36, 33, 81, 81, 33, 33, 84, 65, 84, 33, 65, 76, 65, 65, 36, 65, 68, 84, 81, 84, 36, 36, 81, 33, 34, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 34, 36, 84, 0, 0, 2, 2, 64, 65, 68, 32, 81, 84, 84, 72, 76, 76, 4, 88, 9, 46, 46, 43, 49, 108, 26, 50, 28, 82, 9, 19, 22, 37, 52, 66, 26, 73, 24, 6, 9, 22, 24, 48, 104, 106, 24, 66, 60, 24, 41, 3, 26, 92, 9, 14, 48, 74, 13, 100, 3, 6, 52, 28, 48, 6, 9, 5, 9, 24, 3, 11, 13, 19, 21, 35, 41, 24, 6, 24, 3, 48, 5, 73, 9, 6, 6, 24, 58, 45, 96, 24, 5, 77, 88, 104, 66, 85, 85, 83, 50, 92, 97, 49, 100, 41, 66, 35, 37, 22, 52, 9, 97, 74, 96, 5, 66, 37, 96, 48, 88, 89, 96, 9, 116, 96, 82, 3, 97, 108, 66, 69, 48, 73, 70, 28, 3, 5, 52, 100, 48, 5, 66, 6, 66, 96, 3, 67, 70, 35, 38, 19, 82, 96, 5, 96, 3, 48, 6, 74, 66, 5, 5, 96, 113, 86, 24, 96, 6, 78, 104]

def xsG : List ℕ := [0x2c295846531453359c643a3fb8289802458320240000625b5f33359800187f8800000000022, 0x643a3fb82898024583202c295846531453359c00187f88000000000220240000625b5f333598, 0x64c88a15d942050e24c64c88a15d942050e24cec818001da4a0c8ca44ec818001da4a0c8ca44, 0xc810000014416050441d73163690deeeae0adf70000000004000c08017ee100027dee63fca5d, 0xe043002920a700c17c93054c4382669cab7a10e010002700a633c05c0100c00d82119c035a0, 0x93054c4382669cab7a10e043002920a700c17c0100c00d82119c035a00e010002700a633c05c, 0xd73163690deeeae0adfc8100000144160504417ee100027dee63fca5d70000000004000c0801]

theorem rowsG_len : rowsG.length = 304 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 152 := by decide +kernel

theorem maskG : mask 152 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 152 zs &&& lo 152) ≠ lo 152 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 152) (goal 152) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 152) (goal 152) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 152) (goal 152) s xsG) :
    ¬ HasCircuitSize 7 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 10 h
  have hr : NatRun (mask 152) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 7 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 1
  | 6 => 33
  | 7 => 538
  | 8 => 598
  | 9 => 33
  | 10 => 1
  | _ => 0

def HT : Nat → Nat
  | 5 => 0xdd611f
  | 6 => 0xfe53d3a3d64f1a63c594f978b6e0a5adb61f2113a4a530079d85540f8bba5dd2886a48b285ee035564f9e51854d18ed04fba46784a6e940236183c8f33c93aea318daced2e2562d129c16e89271af4e1236a0ade220d47f71fe8f843157c290e0dfcddae0df576c20ccb5e260810c1cc078bbeac0713d0e806c4fd940610c25400062461
  | 7 => 0xfd96343dfb9783a0f5283f55f236e75ff1b60d88f17b05dcecf766c0ecf248d5ecc9c4b8ec3bdc78eae7ba6ce9bd6337e62dd1bfe5ac1669dff3fcf5deacc987dc773d50dc0aad49db3fd8bcd9910c14d78910fbd6ae5b78d5a2fcaed33cc1e9d26dfc1acfcb0c08cfbc9f39cedb0afbce92a99fcd031a03cc80da0ccb401a39cb008f84c95d108fc8bb62fdc7bfdd09c6278029c5a6782fc56ac579c54bc3c1c4ee630bc41e167ec3ae903bc29a700cc21613edc1a69267c163e0f0c136d903c13368a3c10aeb3bc0f38f1fbfeb81f0bf7ebbefbbd8d72ebb16946cb9254f3cb924e0bab7ab970fb79d5131b76cd2cbb607e29ab2115fa8b08fcb2fb065ab5caf9f313baf3f0fa0af1a9febae11d4c9accf2d42ac0d4dc2abd5c216abaf6c63ab56c7e4a8f88c49a8612040a85794f5a7f7cc56a7b60965a76f74f3a723d088a5dd00e7a4688f14a3c71584a35e2825a3190520a17c0f24a125de98a0e670eda064b9eea05017799fb102b49eaa2add9e69978b9e57df0a9ce57ba69cb252009be09b979b2845d19a657a4e9a37f4c799e0e2dc9958f94b98b6c50e9882c6ec97eb1110974ce91b96f5fdb896e7e80296e5debb96ca047596c69a9a95a7c17e950c4aab948686ba93e313ab936a9e8192b28c3d92542ea69248aad891d107cd9017c6769002d4218fdf9a238f1c08648ea9377c8ea44f308dfe1da58d7e73938d236d948cebd1398c93c9548a7d45848a466f868a2407c48921ecb788da42f388cc7828878d837785b7423a8585081d854268648512c72e84eaf1c38496c9af84788b18839a1f7c835188ac832d036c8312f79c80b3c4f680a722917ffa18eb7e6c3f307e0776f47dad418e7d5391e07d2f66907befe7a27bab044e7ad6f9a37a8a06df7a2ac0f079271a60790e446c788b7bdc785d4c7e78212b1277b5102f77927fc6771360c376d2f74275891b0f752df6bd74e9988c7462fdfa732313d772691a9172236ed171dd4fea71d742ad71c1a12271809fb77141c89170e38f3570d7e3f4708907936f8f320d6f647eff6f4708746e5104176d307bc36b4e62c26aca4c896ab8c48b6a2cdd6e69958d08695687b36778624f675dba75673c336266e9479d66782cd76611036665d570cc65ce8e1065a44656658d31556585f0d7657a23fa653334056515b07f64c25f1864a4287263a6e7c963a0bce7634b8974628cb536626cfdcc623cd0c06209485961e5276b61c98c59611f3cb9604e23525fee6dcb5f7af4145f4e3b745f446cc35f2fdaac5f2164d45eda2c125ebd7c575e74df1e5e2220545e12bed15dbb742b5db567495d0430b75c5c95495b3c2df45aa854c15a37b4e95a11b6b758ef4a3d587ec319587b3a195838e3e05804ac4557f477c957607c3756f13806566fc32d55edcaac55a409c15538b87a5506be2654b43b2154aa01f4541295e453b5def553ad85a65385665352d5cb0452276b0b522747135211ef0d516bbd825155caa35132ecbe50f9ee88509619b550833c8d5049705f4f8995d84f2fa5ba4f03e43e4ee609074e9c92844e770d3b4e6f7b334e27a6c14dfdfaf14daf9f864d817e4a4d2155fc4c7d16344c6c05e74b2acac34b1659524ad9140e4abf659849fe06c9498e2f72496a896a493ffddf48a832294839ea2147d9ca92473e5aeb4684d09d4627c4c14626f4ff44e82467441e658b42abcbe9427bb2f6425762d9418d50f1410d181c40a54ae0403b77b43fa8632c3f29ad063f263fc03eee8b763e9ef0f33e92fec93e54328a3e52b2b13e4499803e23e8fe3d5a09743d59124b3c954c973c5d837e3b65837e3b52f3553a334cb2396185ab39378dcb38ffdb2538e2a866388672e3382ad20338005e5b37965656378bd75a3779f1e0376d9a1a3764e4523763737436f046e136847c523677f0e7357cc2493541e30f3514d0df3463d30b34553a1c33ff310c331f73f6330ecdaf32728a4f3226c88732130ade31dc63ce30f577fb30e284a830aeec71302f1d942fada3ef2fa1e1282f614b182f5844752ec2ea062e95a0f12e94b2b62e85fbde2e794d532e263ca92d5d19702d1f09912d032ce52cf7410d2c798f3f2b79f8622a93a7b529e4664229793b5a2961de482916c061289654cc2890cf6f284732bc27f473f2272305492719be3c271487a62692bd382649208525f21b2c25d056db258302542526307f25122b9724eef5622489406a24816d44242e7e172422e17b23cdfd75236b8b6822bf1c92226378312250dab621887bfc20be5f4520bcb00620aa000c2063aef5201a9e9a1fdb250c1f9d7f091f053a371ee8ec381e878e391e5c5c0e1e4e88dd1de4e9821da8c2aa1d5c1a861c8c66c71c44e4811c2ca3681c062ced1bedd1421be8d9f61bc3ee661bc1160c1bb9b09e1b7e87cb1b08de681ace1c141aa837701a97806b1a7561cd1a5a16291a241b4019ac366d198f4971194f1ce81929eb801918cc5519098ce1189d0d7117fd0fdc17fb359e17e9285d176bbf8c173798a716fa722a166a0e0e15dc9b2b156c0b0b14ff0da214d5466a148881c5140c4a9d1376f37c133013ac131385a812d4ad9f12d353e2120a3261118bfbb811606d131127e8471127dc8710fd7a7a10ed010f10eca7d410d816a410c4e517108ec73a10484a76102295ec0ffa185f0f957bbb0f188c360f090b640f07dc5f0f004bab0eaef3c40e9596dd0e68266d0e6333d30df3cea60deae7480dc980d10da8c1620da81bcf0d7587f00c4c59590c354a1c0c2d98a80c2c7df50b8f18910b327f680b312c8909499bce093f7c8d08dffe480855c444084d3eb2083cf03907f6caa607cb57bb07b8000c0782ba820761c02e06e3bfd906e1952306ced56e06b4d7a80664569a064d00c5064292490611512e05f8b86f05639b27054941800505dba70502e6f6044a095804218d7b031613a00311184c02b59792028eeffe01fd25a101e5a81e01b0c16201ad7fd6011e4dc0011c3b7a010201fb0080ceb3000fba77
  | 8 => 0xf844eb18f75b7806f68a4f60f471fe0bf298e003f010bda3ee57469dee3b3ffceb48a7a1e9bd6337e49a36d4e295095de2847438e066f18dddf519bbdd3f0a5cd7a1a777d70b2e22d607f0f0d4c7fc1ed3e1e5c4d31c2be9d193e500cfcb0c08cefc8e4bce4b95f9cc59c06fcaf83f8bcaaa77fcc9a5eeafc95d108fc928233ec7bfdd09c7734453c68d3205c58eef19c56ac579c472ba57c423c0c7c32d7ec4c31c9544c2235909c2173eb6c1d6dd10c19d3d19c057e972c02a2b5bc0278946bec3f443bdea7445bc6b33a1bbbc8696bb92301cbaf9af33ba83d9fbb99a5a5fb84c6ac0b76cd2cbb591cac0b188eee6b1330ff2b0c2ecdeb065ab5cafa01d56af9400adaf84c1c8aef4ed79aeb0bf2eac56c7d6ac095859aacabe7daa9b227aaa8f91cdaa86b36baa39452baa0fb79eaa0e6470a974ef36a9558699a83d5a87a76f74f3a62db652a5ec56b0a5dd00e7a46b5062a45da683a44aa94ea3b55f9ca3b1bceaa29cc882a249187ea1f3ca0fa1dcbb6ea1920403a16299eca09238b0a091e144a06f10319f9323909f67d2219eaa2add9d48183a9d3af5819cb84ab09cac4b569c9fc5cb9b8894d19b541f2f9ac376ae9a5ea04099ff604798b617f9975958b6973bc578966ec7b696185b7b95f89e9595df916a94ca93299491a0439401996693a059f9929684959281dfca926a2e28925527eb921ec29d91e5743591b935d691416b74913886d0912da89890304f2b8fd0176c8f9899cc8f879c278ef96d818e8ff4728d23f2d78ceee8e28c65d4fd8c1b89898bffdbae8bce1e378baa95d48b7d14de8b73a33d8b5f769e8b01cd3b8a8933fa89bf4f8888ac0b2288ab77ab88383d818790d2b5877ae6e88658568084c9408384a5f16b8468915584674ed783c5201483ac0fb8838d30628264224f825c93c781ec0a3481c4dd0180d0afd58093a509808ff3788080f8668041792e7f8332737f70dd097e4862bf7cbd0b497befe7a27bddcfaa7b0563907ad6f9a379e31172799dabdf799ab6a178ff6a9d78c741177807d7677804ba9b77881d007748a92f771dea927708f0a076198e2175dbabf77579f13d7564e56a75616bfa753a58357467a984737ba1a37327da377309cbae72972da0728f050772461c7f72236ed171abba1d717ef6307141c891712ad972704cad7c7002a4ae6fcd139e6ea0ef846e616d646df0627e6da58baa6d61f8ac6d307bc36c104ceb6b4e62c26b3a47bf6b0a0e626b02621a6ab8c48b6a2d6e3e6a01b083696d9441696319386962df9c68ca5d00671a6bd8670fbd6166acf40f65f489ed65b72d7264ee198c6469fc0e6416c52e63f4022063d71a9863caa3f663b05acf638f00fe637e5fdf631c334962f7f8a162da4b9d62c93f0062b1b5f7620c9c65620c2bb161f22f6f61cd64186187c3d76185a49e617474eb611f3cb960cf33886087f5716037868660161a845fd3858b5ef9b7155e59d3765dcc401d5db83f975db567495d740adb5d26d4385c9ed6775c74e8c65c545a6f5bee281c5bb82d475b87bd555b0ada6e5a54a78a5a11b6b759dc679359b67e9f59663e725929515a58ef4a3d5810af9857ebaf8b56cd827c56c2a3f95650920055d3a76855298927546de3a75447abb8543f279c53e287b653c3328e53a8fdde5391a326527351e651aeec11517d531a50ff9ddf504e4f3c4ff27dd84fa4b7364f8c27894f8995d84f6500014f0caaff4ee609074e6f7b334e68f8104df6d3d74dcc94d64dc3b5084d8ce2a84c946ceb4c8d89374c85a47a4bdc90e54bbfe4d54af5730c4acc59104a53aac24a13cccc49ca858649ca834149c5f65d493d6ab448e5bd5248b19445488cbd67482a7ffd4826ceeb47d9ca92471c50dc46f65ca9468ed220456054fa4526c8db44b9547944925e224445e229444548d84421c1d143915f9f437cb5b042de7ce6422a8208421f851541f9ff45411f4c224110d1e440db443e40a54ae0402aab263fa8cf0f3f29ad063ecbfa643e68c3203e4f43413e4499803e1d8db53d9b91793d99b6473c8963e43c60638a3c18701d3c0fd2a43b725a783b52f3553afd2d103ab1b7373ab0b1173a4b5ab63a28ba0d3a1f011a396185ab38d448fa38b3b281381c8b8b3817f5a737859f553764522c3710e57836c6495436876b84361a2b3c361328ef35dc16a634dbf99b3446020b343ac7bd33ff310c33b55681337cf3d43322c5ac3317a8543248a15e31cce117318ca120317595ef315f7129315e83fb31314c51312fc38c311fc44730dfac562f99e1002f5844752ee594f92ece9e922e95a0f12e94b2b62e35f0762dff1e162d81fa032cffc4a52cfe96e62cd91e732c896fc32c75d1222c4ecc532bde7f4f2b46c8892b46109b2a765ff42a35072c29e0524e29afa622290e671e28f5bdca28a73f7e28910dd7284732bc2837b005281215d5280dab5d27f473f227f3224727f050de278a9335277e62a72724debd27100eb626b1200626ae719d26a5f493264715dc2646e37e2644212b2626ae0d261f55d425eeb2ec25c4ab8d2549d4c1253dba9a25022efa24f8441c24ee807a24e7b7b224bdc48324b22d5c2468ec63243ef5db24049f4824039b0d23d343b6236965d422b9d6ea222121fc2216386221f549fb2128927520d92bab209fd61a209474151fa00e4d1f7dd0991f3659131f0629771efbdcc51e826cdd1de4e9821dcd259f1d63f6c41d1b9d871ce4cb271c98a1981c8f25171c66bd881bf0bf271bedd1421be8e64b1be571b61b3479641aa8ec261a8a9fb519e07f54197b53e9192bc4fd1929eb801916563118955333182ab7c617ef9b2c17169dbb16affb5816a1122a15e89f871596cd17159238731583769814c13473143311d713ffc2a213f599f513ef2f4213d3a8c613c29c7d138a40a313899981131431b312f44bf512e9481e1260199c122999ca11d1ac97110a798610c92f1e10c4e5170ffa185f0fd237200f44e1f50f1dd2520f07dc5f0eb8e78b0e55dc110e10f3970dde152d0da60b6a0d8f50140d72285e0d2eb0410d1da50b0cd0dd4d0c83ef610c5d99290b981fda0b3a57aa0af5a8850ad2de9709f111d5093f7c8d091b410c090ef41d08de816708c288a708bdff080898958c084248f5082854bd081f7b8f081a2ee60810f5dc07fffdff07f6caa607dbf4a307b3820607469d600721d2090646dbcd0633e4ea058d81b7055e92f9053d418a0524bd0404c608ab0499596a048469db042165a003edc27803e9516c0355853a02ed397402d4dc53029506d70282d467027aae2b022dda50022b8f8e0217631001fd25a101d9d47d01d52cda013f3f480100f65b00b759a8
  | 9 => 0xee3b3ffcd4c7fc1ec7bfdd09c2173eb6bc6b33a1aa39452ba76f74f394ca9329925527eb88ac0b227b0563907ad6f9a378c7411775dbabf77141c891671a6bd85b0ada6e5391a3264a13cccc40db443e3e4499803c18701d3afd2d103ab0b1173a1f011a2bde7f4f2b46c8892837b005278a9335236965d4209fd61a1efbdcc515923873
  | 10 => 0x7141c891
  | _ => 0

def PT : Nat → Nat
  | 5 => 0x29320
  | 6 => 0x1843615ec640760c0e0b18a9723132c66a2bacc482d18a2352063d0684608881af98907e2065e26a2bacc542d98ab9b33102c44c7a0c84c218917331408a6a0d78c509718b12f31420c4402dcd80c21a085b3612e662a110c10c413114d313
  | 7 => 0x13f08015f371000660ae4c055c1b890c33085860c9f0c05a9980b852071c820292080cda1a02f6a02930ea0130d05a408187c105840402c74d41e41a02957241b440c0e4989a408205030118e6c091c409ab9b00597301cc6a0ba841175ba815d34138e200000c40d69b09ec3513b020c7b4d04381b004d3715ec202c14810011b88f03616ce40cba840c6d1021e710635e6e26a8d81929820d63401566e0f7cd805493814a36215c6c0128c041d9b0bc63104046a0570d45ab1a82eaa6127c2043b4dc1ef1b808510094a60206c9001c1b03672702f22086d0d402c580bc836007c200f74d80ec082bf03705e6200ad4cc5758812f21032c46e0aa885db11818c01063ae680428880399281b910448d6c2b8cd44728830e63405d6e20a34d44d51a02283160066830d8840430812973610b2e80be8818428829a731529a68078040c469a819810152820a9a8d402c39018733016c62871840c5298a0d736028e208334dc41d9809e11022fc6c24b8d854698b1802076a86e066040c8498285810029a6c0bb8d01479038c010048c208488dc1a39a811b37034c62c358d40311a896b37008c6288649c04a9a80c830547f642d9c8147208207d1043c2c484fc4156a9a006c320492462028401f81b02eab0495460601481575bb00861046ce40639cd8042080b9d3613cc202588d02531281e07211c8206b8cd85f89a00c93207d4602211c90171a810c340000000d3c8502c08114d35007c2080148112d98b16335002244000cc06299b80c821033020402c414da1b83c03602ec60cd54d00d79a88841031006a263881c698828d2b6232c40c0fc4145b18a8273503f840e5c04104331227f105722602ee88110c92020d30409a6a25c4418521b09e01001a06070bc4024c0802ee3301ca2051689409f0801863503fe60234c4041f0810e3371070680f00d00bb181af937010068275cd410b1821ac351064602d0c405ee1b800a10225c62e8f8409dd90299910430c6c11a4d807253110136018220a216d84698819ab3701c820af7cd010c1032f71058386020dc984641a01e11042626e27d4811089a8aac270226680290d44649b805530130c6e0bf8dc1a18811c71058f2602704d446088082736007668235cdc1359a00c332348e20c36c81c2c881a6d3507da40cc45c950b1b83d53703d86e2c4440c599b01d81044d46e0219c84420820e4a0138c20c30440d0c102be210085e20a9f4d44091028143308ec40696cdc4261808b63161006e2c444110d182a3f10011a6600ac804449021af36105e6e021c4040e13046f1000ee6029f0c50ec880a477247f840a2144083710380a1047b86a068cd09e39a8b313505a86a0368814461b00383700a06c3265cc181983af610048e20034c4090b1a80a63013ce2007208402cba802e34016668051840e370828e33511b26e0118c581311388c37034e62e764408011b0b431030d6660bded88001b008472329a6e06d4c850788284d36164466112480dd79a83613411646e036c80dca1282d53600026e11a8404241809701000b2ec09a4d40011a88003502f220c618d006908212e31410c200fdcc05b71023f035075840f0e8d44608822a9721180204aa0400739b80e5b1204e6e0164410cf90b8e330116e6e2e4cd015c9b0950306290602000d014a880311105102602f7cd417c9a812234010e2065c44140818992a22037220c91c40c231b89ea2071a620001cd40cc882847315406660d50d404308319810032c40e210418d51a809c2205d86a2a5440c3e0831e710310b4a20ecdc4728804693504d46c0688c8d08180b55360244660b90d41f69038eb30735e6291f4402375b105810664a6a071c4041f083324360620200ba9c4e24102b9235056a6a24fc40c591903481000b36c4ad0d0423980c482068746822c8d40ec881a9510464a6e04f4d40899b002e3603ce2082f0c55251b82f71033cc20abadc9575b981e11062c66c00e8d4554882adb3705f2680d988108e9082d437038c204c4188d7c9b040a10114a62ebac4001f8819123506c06a26d4d809f8808813612f220ac45c90461a04381008f8206144d05311b80a92061486207f8d8434991a5b31504c608320d810b1b03421064986086a4c1a309b03dd3405d62026604181c9a8123360
  | 8 => 0x1a73180d72707420003c4181a7a880170404d40609395019881826203057c600004180f580834e210614e00c6d401b39804075001a202093cd0075b900c6040642000dcd401038a0291070036420c84140ddb8801a0101e680085c1812880018e0200ec420afcc00c083022604024ea0086c801af82014102049cc60484081630282e6050214c0011814015b8040100049ea005c4001008181d725018e2e05ecc02039803a30502220a0804080f38903a70601c6a00869c01efb000671705020802041400380826103031cc607041003081012b50049c2007c40802b03020a5003d4020ded0012081003106028e080604140d38b011b50079c0200c40016d3002da4002420a0f98180c700808a5003420601dc180e08180170505e20207d8081b19801eb410214a003a90018db8000a6105ee0403988c1f302001104021684076dc00d082002a6001e20800acc010883826603049ea8039d001b080018f3102c20603ad800c7a1825e32034c080a44000c7290046210402080544140db8180a1070076c004dd801e701012625018e4a07dc140051880910605ec0e03041015f0280270402b4e00abd800308381b10503c20206540017b0300410600ce0e035c4c0b882803750042e060e9c0c133818156060382000b69c01308000e1030256c003040c08da903110005cc0602981c0e08280210404e208067c141030801d305072c06093c8012881803b1207be0402840008881025e40064c0a03440804d9800662700a20606840400080824f1000420602d81015f22829b70034c060f78140030080070205166007ed000b08201c30605cc0404ec8400000014104020208019c1006530823713028c0a03ad000408000ba6001e6600004081b1a000a70304ec42039d4006103819f40055c2006780c07bb800b70707e200089c040db030041000176c000981010b0a00772406f6a0022d400d88001db050436a00e9c140330200c60300f442046cc80588081d107006e2403840819b1082fb61057eca063c08060828093600516800af900075a8031704058200019c4c0d383001105010208070dc010d2001f10400ae0c04dcc01a718021715016206011c1412a818137210806a003c41415a8281850600ce460ac4040388302f70400820a0444000451802ea610042020f3c041fb0180d6050654c0075c0c0e08102450201168002c4100fb81000b71057e0a00181c08d2000eb3003a6080f78100038382b1020266a00018100c79a801602057e640afd080db83823107033c0a0a44140008181cb0606d6600afc400e388019e6002144205c41810b0b80f10000546002ec84018838131030302080f39800388183cf30033c860bdc1c1e72281410702420e086dc00453002bf15061660063c481f538022100033eca039cc01738181a7010046a00be8040308001234000ae46086d001888182510400348208d81c0239303810005d6a2059c400238180d107080660051c04043b001271000220006541408380819101079c6008980c0ab92011b6101eec0076c100b53002be60038ee00a1dc007b90811b5101820c0c4410045b000e37007be0a085c400888382f10301ae080284181ef82014604057c2402c41409da000d7050102040f3cd000301819102018c0c05ad8015881828370033e640bacc411b02819f6300c20a05ad4016b0181e605052204039c400638083cf65064c0601440409d98019e4605e2040269c00eb90802105078202029c400eb828185040246e00e58100cf200087100454420b440c1f302809107026ee001c4100db91840b6003ac2c07a9000c73282310400cc0e0459400052880a7040714a0063c0c0952800ca0702a2060d395016391807605033e2a0d380403380826a40036c0a05dc840e383016b700056a0011c040c281809103055c04045884060800027100054e0104d8009882002b10003662006d84090800396060114800afd14079b0011a700462060a440c00da080c60700ac060af98c07d90813360000e060ec40c05b908011070382020b9c18033018206030034e20914001cd3800170601d6e003c41c0f52082eb010074a0035c501a79802110104f4c00018181c08180d707031ec0067848145a8007703024660074c0c15a820407600456e206440c08d18035e04083660068408085a001560300ee4c06d81c03b0301db210222060d3c0401881014100069e6805ed00145b001025002c204071c100bd9083775005e208049d001d582812b7003960606c41c045b801410606820202dc1409083010a6202020c08d884205a8003b2002f4600118040cf8080b10201ac4808581810d1000160502e20e042d8015781001b0105ce0a08d81800da8827b31057e620abd001508303170605cc08046cc01bba0001a21
  | 9 => 0xe54001e6800440000731800f50001c20000408007aa001e32000a08003c8000881801e40001e2000000000799001503000a040078d0007a9001104001ca0003cc000718000f40001c40007d9000f32000e60003ec0003d8c00f29000500
  | _ => 0

def dA : Nat := 0xfffffffffffffffffff0000000000000000000fffffffffffffffffff

def setA (xs : List Nat) : List Nat := xs.map (moveBits dA 76)

theorem runA {s ws} (h : NatRun (mask 152) (goal 152) s ws) :
    NatRun (mask 152) (goal 152) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 23 j
    if e = 0 then xsG else
      let r := mv (mask 152) (e % 4096) (St d (s + 1) (e / 8192))
      if e / 4096 % 2 = 1 then setA r else r

def S (s j : Nat) : List Nat := St (10 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def ori (zs : List Nat) : List Nat :=
  let az := setA zs
  if hk zs ≤ hk az then zs else az

theorem ori_ok {u ys} (h : NatRun (mask 152) (goal 152) u ys) :
    NatRun (mask 152) (goal 152) u (ori ys) := by
  unfold ori
  dsimp only
  split
  · exact h
  · exact runA h

def poolG : List Nat := [0xc53008ac320b8, 0x1380202cdf2acb0, 0x1380713ca8320ac, 0xc5301cab2e099, 0x2c03008df2b0a8, 0x1384f01cac2e0c8, 0x13c0714cdf2e0a8, 0x2c53138ab32099, 0xc0714cb0264ab, 0x2c5301ca82c0df, 0x13c07138ac320b8, 0x85300cac2e0c8, 0x1380714cc82e0ac, 0x14c0702ca8264b8, 0x80714cc82e0ac, 0x1340112cac320b8, 0x24044000df2acb0]

def Z (s : Nat) := bar 152 S NN idx ori poolG s

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel
theorem z10 : span (Z 10) 1 0 = true := h10y0
theorem h9y0 : span (Z 9) 11 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 11 11 = true := by decide +kernel
theorem h9y2 : span (Z 9) 11 22 = true := by decide +kernel
theorem z9 : span (Z 9) 33 0 = true := (@span_join (Z 9) 22 0 11 (@span_join (Z 9) 11 0 11 h9y0 h9y1) h9y2)
theorem h8y0 : span (Z 8) 12 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 12 12 = true := by decide +kernel
theorem h8y2 : span (Z 8) 12 24 = true := by decide +kernel
theorem h8y3 : span (Z 8) 12 36 = true := by decide +kernel
theorem h8y4 : span (Z 8) 12 48 = true := by decide +kernel
theorem h8y5 : span (Z 8) 12 60 = true := by decide +kernel
theorem h8y6 : span (Z 8) 12 72 = true := by decide +kernel
theorem h8y7 : span (Z 8) 12 84 = true := by decide +kernel
theorem h8y8 : span (Z 8) 12 96 = true := by decide +kernel
theorem h8y9 : span (Z 8) 12 108 = true := by decide +kernel
theorem h8y10 : span (Z 8) 12 120 = true := by decide +kernel
theorem h8y11 : span (Z 8) 12 132 = true := by decide +kernel
theorem h8y12 : span (Z 8) 12 144 = true := by decide +kernel
theorem h8y13 : span (Z 8) 12 156 = true := by decide +kernel
theorem h8y14 : span (Z 8) 12 168 = true := by decide +kernel
theorem h8y15 : span (Z 8) 12 180 = true := by decide +kernel
theorem h8y16 : span (Z 8) 12 192 = true := by decide +kernel
theorem h8y17 : span (Z 8) 12 204 = true := by decide +kernel
theorem h8y18 : span (Z 8) 12 216 = true := by decide +kernel
theorem h8y19 : span (Z 8) 12 228 = true := by decide +kernel
theorem h8y20 : span (Z 8) 12 240 = true := by decide +kernel
theorem h8y21 : span (Z 8) 12 252 = true := by decide +kernel
theorem h8y22 : span (Z 8) 12 264 = true := by decide +kernel
theorem h8y23 : span (Z 8) 12 276 = true := by decide +kernel
theorem h8y24 : span (Z 8) 12 288 = true := by decide +kernel
theorem h8y25 : span (Z 8) 12 300 = true := by decide +kernel
theorem h8y26 : span (Z 8) 12 312 = true := by decide +kernel
theorem h8y27 : span (Z 8) 12 324 = true := by decide +kernel
theorem h8y28 : span (Z 8) 12 336 = true := by decide +kernel
theorem h8y29 : span (Z 8) 12 348 = true := by decide +kernel
theorem h8y30 : span (Z 8) 12 360 = true := by decide +kernel
theorem h8y31 : span (Z 8) 12 372 = true := by decide +kernel
theorem h8y32 : span (Z 8) 12 384 = true := by decide +kernel
theorem h8y33 : span (Z 8) 12 396 = true := by decide +kernel
theorem h8y34 : span (Z 8) 12 408 = true := by decide +kernel
theorem h8y35 : span (Z 8) 12 420 = true := by decide +kernel
theorem h8y36 : span (Z 8) 12 432 = true := by decide +kernel
theorem h8y37 : span (Z 8) 12 444 = true := by decide +kernel
theorem h8y38 : span (Z 8) 12 456 = true := by decide +kernel
theorem h8y39 : span (Z 8) 12 468 = true := by decide +kernel
theorem h8y40 : span (Z 8) 12 480 = true := by decide +kernel
theorem h8y41 : span (Z 8) 12 492 = true := by decide +kernel
theorem h8y42 : span (Z 8) 12 504 = true := by decide +kernel
theorem h8y43 : span (Z 8) 12 516 = true := by decide +kernel
theorem h8y44 : span (Z 8) 12 528 = true := by decide +kernel
theorem h8y45 : span (Z 8) 12 540 = true := by decide +kernel
theorem h8y46 : span (Z 8) 12 552 = true := by decide +kernel
theorem h8y47 : span (Z 8) 12 564 = true := by decide +kernel
theorem h8y48 : span (Z 8) 12 576 = true := by decide +kernel
theorem h8y49 : span (Z 8) 10 588 = true := by decide +kernel
theorem z8 : span (Z 8) 598 0 = true := (@span_join (Z 8) 384 0 214 (@span_join (Z 8) 192 0 192 (@span_join (Z 8) 96 0 96 (@span_join (Z 8) 48 0 48 (@span_join (Z 8) 24 0 24 (@span_join (Z 8) 12 0 12 h8y0 h8y1) (@span_join (Z 8) 12 24 12 h8y2 h8y3)) (@span_join (Z 8) 24 48 24 (@span_join (Z 8) 12 48 12 h8y4 h8y5) (@span_join (Z 8) 12 72 12 h8y6 h8y7))) (@span_join (Z 8) 48 96 48 (@span_join (Z 8) 24 96 24 (@span_join (Z 8) 12 96 12 h8y8 h8y9) (@span_join (Z 8) 12 120 12 h8y10 h8y11)) (@span_join (Z 8) 24 144 24 (@span_join (Z 8) 12 144 12 h8y12 h8y13) (@span_join (Z 8) 12 168 12 h8y14 h8y15)))) (@span_join (Z 8) 96 192 96 (@span_join (Z 8) 48 192 48 (@span_join (Z 8) 24 192 24 (@span_join (Z 8) 12 192 12 h8y16 h8y17) (@span_join (Z 8) 12 216 12 h8y18 h8y19)) (@span_join (Z 8) 24 240 24 (@span_join (Z 8) 12 240 12 h8y20 h8y21) (@span_join (Z 8) 12 264 12 h8y22 h8y23))) (@span_join (Z 8) 48 288 48 (@span_join (Z 8) 24 288 24 (@span_join (Z 8) 12 288 12 h8y24 h8y25) (@span_join (Z 8) 12 312 12 h8y26 h8y27)) (@span_join (Z 8) 24 336 24 (@span_join (Z 8) 12 336 12 h8y28 h8y29) (@span_join (Z 8) 12 360 12 h8y30 h8y31))))) (@span_join (Z 8) 192 384 22 (@span_join (Z 8) 96 384 96 (@span_join (Z 8) 48 384 48 (@span_join (Z 8) 24 384 24 (@span_join (Z 8) 12 384 12 h8y32 h8y33) (@span_join (Z 8) 12 408 12 h8y34 h8y35)) (@span_join (Z 8) 24 432 24 (@span_join (Z 8) 12 432 12 h8y36 h8y37) (@span_join (Z 8) 12 456 12 h8y38 h8y39))) (@span_join (Z 8) 48 480 48 (@span_join (Z 8) 24 480 24 (@span_join (Z 8) 12 480 12 h8y40 h8y41) (@span_join (Z 8) 12 504 12 h8y42 h8y43)) (@span_join (Z 8) 24 528 24 (@span_join (Z 8) 12 528 12 h8y44 h8y45) (@span_join (Z 8) 12 552 12 h8y46 h8y47)))) (@span_join (Z 8) 12 576 10 h8y48 h8y49)))
theorem h7y0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 12 12 = true := by decide +kernel
theorem h7y2 : span (Z 7) 12 24 = true := by decide +kernel
theorem h7y3 : span (Z 7) 12 36 = true := by decide +kernel
theorem h7y4 : span (Z 7) 12 48 = true := by decide +kernel
theorem h7y5 : span (Z 7) 12 60 = true := by decide +kernel
theorem h7y6 : span (Z 7) 12 72 = true := by decide +kernel
theorem h7y7 : span (Z 7) 12 84 = true := by decide +kernel
theorem h7y8 : span (Z 7) 12 96 = true := by decide +kernel
theorem h7y9 : span (Z 7) 12 108 = true := by decide +kernel
theorem h7y10 : span (Z 7) 12 120 = true := by decide +kernel
theorem h7y11 : span (Z 7) 12 132 = true := by decide +kernel
theorem h7y12 : span (Z 7) 12 144 = true := by decide +kernel
theorem h7y13 : span (Z 7) 12 156 = true := by decide +kernel
theorem h7y14 : span (Z 7) 12 168 = true := by decide +kernel
theorem h7y15 : span (Z 7) 12 180 = true := by decide +kernel
theorem h7y16 : span (Z 7) 12 192 = true := by decide +kernel
theorem h7y17 : span (Z 7) 12 204 = true := by decide +kernel
theorem h7y18 : span (Z 7) 12 216 = true := by decide +kernel
theorem h7y19 : span (Z 7) 12 228 = true := by decide +kernel
theorem h7y20 : span (Z 7) 12 240 = true := by decide +kernel
theorem h7y21 : span (Z 7) 12 252 = true := by decide +kernel
theorem h7y22 : span (Z 7) 12 264 = true := by decide +kernel
theorem h7y23 : span (Z 7) 12 276 = true := by decide +kernel
theorem h7y24 : span (Z 7) 12 288 = true := by decide +kernel
theorem h7y25 : span (Z 7) 12 300 = true := by decide +kernel
theorem h7y26 : span (Z 7) 12 312 = true := by decide +kernel
theorem h7y27 : span (Z 7) 12 324 = true := by decide +kernel
theorem h7y28 : span (Z 7) 12 336 = true := by decide +kernel
theorem h7y29 : span (Z 7) 12 348 = true := by decide +kernel
theorem h7y30 : span (Z 7) 12 360 = true := by decide +kernel
theorem h7y31 : span (Z 7) 12 372 = true := by decide +kernel
theorem h7y32 : span (Z 7) 12 384 = true := by decide +kernel
theorem h7y33 : span (Z 7) 12 396 = true := by decide +kernel
theorem h7y34 : span (Z 7) 12 408 = true := by decide +kernel
theorem h7y35 : span (Z 7) 12 420 = true := by decide +kernel
theorem h7y36 : span (Z 7) 12 432 = true := by decide +kernel
theorem h7y37 : span (Z 7) 12 444 = true := by decide +kernel
theorem h7y38 : span (Z 7) 12 456 = true := by decide +kernel
theorem h7y39 : span (Z 7) 12 468 = true := by decide +kernel
theorem h7y40 : span (Z 7) 12 480 = true := by decide +kernel
theorem h7y41 : span (Z 7) 12 492 = true := by decide +kernel
theorem h7y42 : span (Z 7) 12 504 = true := by decide +kernel
theorem h7y43 : span (Z 7) 12 516 = true := by decide +kernel
theorem h7y44 : span (Z 7) 10 528 = true := by decide +kernel
theorem z7 : span (Z 7) 538 0 = true := (@span_join (Z 7) 384 0 154 (@span_join (Z 7) 192 0 192 (@span_join (Z 7) 96 0 96 (@span_join (Z 7) 48 0 48 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 h7y0 h7y1) (@span_join (Z 7) 12 24 12 h7y2 h7y3)) (@span_join (Z 7) 24 48 24 (@span_join (Z 7) 12 48 12 h7y4 h7y5) (@span_join (Z 7) 12 72 12 h7y6 h7y7))) (@span_join (Z 7) 48 96 48 (@span_join (Z 7) 24 96 24 (@span_join (Z 7) 12 96 12 h7y8 h7y9) (@span_join (Z 7) 12 120 12 h7y10 h7y11)) (@span_join (Z 7) 24 144 24 (@span_join (Z 7) 12 144 12 h7y12 h7y13) (@span_join (Z 7) 12 168 12 h7y14 h7y15)))) (@span_join (Z 7) 96 192 96 (@span_join (Z 7) 48 192 48 (@span_join (Z 7) 24 192 24 (@span_join (Z 7) 12 192 12 h7y16 h7y17) (@span_join (Z 7) 12 216 12 h7y18 h7y19)) (@span_join (Z 7) 24 240 24 (@span_join (Z 7) 12 240 12 h7y20 h7y21) (@span_join (Z 7) 12 264 12 h7y22 h7y23))) (@span_join (Z 7) 48 288 48 (@span_join (Z 7) 24 288 24 (@span_join (Z 7) 12 288 12 h7y24 h7y25) (@span_join (Z 7) 12 312 12 h7y26 h7y27)) (@span_join (Z 7) 24 336 24 (@span_join (Z 7) 12 336 12 h7y28 h7y29) (@span_join (Z 7) 12 360 12 h7y30 h7y31))))) (@span_join (Z 7) 96 384 58 (@span_join (Z 7) 48 384 48 (@span_join (Z 7) 24 384 24 (@span_join (Z 7) 12 384 12 h7y32 h7y33) (@span_join (Z 7) 12 408 12 h7y34 h7y35)) (@span_join (Z 7) 24 432 24 (@span_join (Z 7) 12 432 12 h7y36 h7y37) (@span_join (Z 7) 12 456 12 h7y38 h7y39))) (@span_join (Z 7) 48 480 10 (@span_join (Z 7) 24 480 24 (@span_join (Z 7) 12 480 12 h7y40 h7y41) (@span_join (Z 7) 12 504 12 h7y42 h7y43)) h7y44)))
theorem h6y0 : span (Z 6) 11 0 = true := by decide +kernel
theorem h6y1 : span (Z 6) 11 11 = true := by decide +kernel
theorem h6y2 : span (Z 6) 11 22 = true := by decide +kernel
theorem z6 : span (Z 6) 33 0 = true := (@span_join (Z 6) 22 0 11 (@span_join (Z 6) 11 0 11 h6y0 h6y1) h6y2)
theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel
theorem z5 : span (Z 5) 1 0 = true := h5y0
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

theorem scr_xs6 : scr 152 6 poolG xsG = true := by decide +kernel

theorem root7 : S 7 355 = xsG := by decide +kernel
theorem root8 : S 8 389 = xsG := by decide +kernel
theorem root9 : S 9 18 = xsG := by decide +kernel
theorem root10 : S 10 0 = xsG := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 152) (goal 152) s xsG) : False := by
  interval_cases s
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have h1 := scr_no poolG h
    rw [scr_xs6] at h1
    contradiction
  · rw [← root7] at h
    exact bar_all ori_ok checked 7 (by decide) 355 (by decide) h
  · rw [← root8] at h
    exact bar_all ori_ok checked 8 (by decide) 389 (by decide) h
  · rw [← root9] at h
    exact bar_all ori_ok checked 9 (by decide) 18 (by decide) h
  · rw [← root10] at h
    exact bar_all ori_ok checked 10 (by decide) 0 (by decide) h

end PEqualNP.Outside.L_meta_982_aux.Case23Base

theorem PEqualNP.Outside.L_meta_982_aux.case23_base : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1)) s → 11 ≤ s := by
  intro s hs
  by_contra hsmall
  obtain ⟨C,hfan,hsize,hev⟩ := hs
  apply PEqualNP.Outside.L_meta_982_aux.Case23Base.mainG PEqualNP.Outside.L_meta_982_aux.Case23Base.noRunFull
  exact ⟨C,hfan,by omega,hev⟩


namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base
end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base
end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base
end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def rows517 : List ℕ := [3, 3, 3, 84, 17, 10, 12, 72, 1, 76, 81, 34, 84, 34, 42, 12, 3, 42, 10, 80, 81, 2, 76, 48, 4, 84, 44, 81, 52, 65, 64, 64, 44, 76, 48, 65, 42, 42, 52, 34, 3, 44, 52, 20, 48, 34, 3, 10, 65, 12, 1, 1, 2, 0, 0, 2, 0, 4, 3, 3, 3, 84, 65, 34, 36, 48, 1, 52, 81, 10, 84, 10, 42, 36, 3, 42, 34, 80, 81, 2, 52, 72, 4, 84, 44, 81, 76, 17, 16, 16, 44, 52, 72, 17, 42, 42, 76, 10, 3, 44, 76, 68, 72, 10, 3, 34, 17, 36, 1, 1, 2, 0, 0, 2, 0, 4, 3, 3, 3, 44, 10, 17, 20, 48, 2, 52, 42, 65, 44, 65, 81, 20, 3, 81, 17, 40, 42, 1, 52, 72, 4, 44, 84, 42, 76, 34, 32, 32, 84, 52, 72, 34, 81, 81, 76, 65, 3, 84, 76, 12, 72, 65, 3, 17, 34, 20, 2, 2, 1, 0, 0, 1, 0, 4, 3, 3, 3, 44, 34, 65, 68, 72, 2, 76, 42, 17, 44, 17, 81, 68, 3, 81, 65, 40, 42, 1, 76, 48, 4, 44, 84, 42, 52, 10, 8, 8, 84, 76, 48, 10, 81, 81, 52, 17, 3, 84, 52, 36, 48, 17, 3, 65, 10, 68, 2, 2, 1, 0, 0, 1, 0, 4, 9, 11, 5, 86, 21, 24, 14, 104, 9, 92, 67, 98, 92, 35, 46, 28, 7, 58, 74, 112, 83, 6, 74, 49, 5, 69, 104, 73, 54, 33, 96, 66, 46, 69, 18, 9, 24, 14, 28, 33, 82, 100, 24, 24, 24, 6, 38, 88, 35, 11, 69, 73, 82, 96, 6, 67, 66, 7, 33, 35, 5, 86, 69, 96, 38, 56, 33, 116, 19, 26, 116, 11, 46, 100, 7, 106, 50, 88, 83, 6, 50, 73, 5, 21, 56, 49, 78, 9, 24, 18, 46, 21, 66, 33, 96, 38, 100, 9, 82, 28, 96, 96, 96, 6, 14, 112, 11, 35, 21, 49, 82, 24, 6, 19, 18, 7, 18, 19, 6, 45, 14, 24, 21, 112, 18, 60, 35, 97, 60, 67, 85, 28, 7, 89, 49, 104, 43, 5, 49, 74, 6, 38, 112, 50, 77, 66, 96, 33, 85, 38, 9, 18, 24, 21, 28, 66, 41, 100, 24, 24, 24, 5, 69, 56, 67, 19, 38, 50, 41, 96, 5, 35, 33, 7, 66, 67, 6, 45, 38, 96, 69, 88, 66, 108, 11, 25, 108, 19, 85, 100, 7, 113, 73, 56, 43, 5, 73, 50, 6, 14, 88, 74, 53, 18, 24, 9, 85, 14, 33, 66, 96, 69, 100, 18, 41, 28, 96, 96, 96, 5, 21, 104, 19, 67, 14, 74, 41, 24, 5, 11, 9, 7]

def xs517 : List ℕ := [0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517, 0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827, 0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248, 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0, 0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418, 0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800, 0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]

abbrev f517 : BFn 7 := (fun x : Fin 7 → Bool => (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1))

theorem rows517_len : rows517.length = 464 := by decide +kernel

theorem enc_inputs517 :
    (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a rows517)
      = xs517 := by decide +kernel

theorem enc_goal517 : encL f517 rows517 = goal 232 := by decide +kernel

theorem mask517 : mask 232 = 2 ^ rows517.length - 1 := by rw [rows517_len]; rfl

theorem proper_fail517 : ∀ zs ∈ xs517.sublists, zs ≠ xs517 →
    (cov 232 zs &&& lo 232) ≠ lo 232 := by decide +kernel

theorem no_sub517 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 232) (goal 232) s xs517) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xs517 → NatRun (mask 232) (goal 232) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs517
  · subst e; exact noRunFull s hs h
  · exact proper_fail517 zs (List.mem_sublists.2 hz) e (required h)

theorem main517 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 232) (goal 232) s xs517) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)) s → 11 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f517 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 232) (encL f517 rows517) s' (ws.map fun a => encL a rows517) :=
    Run.map (fun a : BFn 7 => encL a rows517)
      (fun a => by rw [mask517]; exact encL_inv a rows517)
      (fun a b => encL_and a b rows517) (fun a b => encL_or a b rows517) hrun
  rw [enc_goal517] at hr
  refine no_sub517 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs517]
  exact hsub.map _

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def deltaA : Nat := (lo 58) ||| ((lo 58) <<< 116) ||| ((lo 58) <<< 232) ||| ((lo 58) <<< 348)
def deltaB : Nat := lo 116 ||| ((lo 116) <<< 232)

def setA (xs : List Nat) := xs.map (moveBits deltaA 58)
def setB (xs : List Nat) := xs.map (moveBits deltaB 116)

theorem runA {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem runB {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setB ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def laneHash (i w : Nat) : Nat :=
  let m := 18446744073709551557
  let a := ((w >>> (58*i)) &&& 0x3ffffffffffffff) + 73 * ((w >>> (232+58*i)) &&& 0x3ffffffffffffff)
  ((a % m + 123456789)^5) % m + 1

def laneSum (i : Nat) : List Nat → Nat
  | [] => 0
  | w :: r => laneHash i w + laneSum i r

def orient (ws : List Nat) : List Nat :=
  let h0 := laneSum 0 ws
  let h1 := laneSum 1 ws
  let h2 := laneSum 2 ws
  let h3 := laneSum 3 ws
  if h0 ≤ h1 && h0 ≤ h2 && h0 ≤ h3 then ws
  else if h1 ≤ h2 && h1 ≤ h3 then setA ws
  else if h2 ≤ h3 then setB ws
  else setA (setB ws)

theorem runOrient {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (orient ws) := by
  unfold orient
  dsimp only
  split
  · exact h
  · split
    · exact runA h
    · split
      · exact runB h
      · exact runA (runB h)

def recipeStep (ma : Nat) (lit : Nat → Nat) (op : Nat) (stack : List Nat) : List Nat :=
  if op < 8 then lit op :: stack
  else match stack with
  | [] => []
  | a :: t => if op = 8 then (a ^^^ ma) :: t else match t with
    | [] => []
    | b :: r => (if op = 9 then a &&& b else a ||| b) :: r

def recipeVal (ma : Nat) (lit : Nat → Nat) : Nat → Nat → List Nat → Nat
  | 0, _, stack => stack.headD 0
  | t+1, ops, stack =>
    if ops = 0 then stack.headD 0 else
      recipeVal ma lit t (ops >>> 4) (recipeStep ma lit (ops &&& 15) stack)

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

def t1 : Nat := 0x0

def t2 : Nat := 0x20000000100000080000000000000000000000000000000000000000000000000000000000

def t3 : Nat := 0x2000000000000200000000000000000000000000000000000000000000000000000000000000

def t4 : Nat := 0x40040000400020100100001000080000000000000000000000000000000000000000000000000000000000

def t5 : Nat := 0x4004000202000000000008400010100004001100040000000000000000000000000000000000000000000000000000000000000

def t6 : Nat := 0x480000000010000000000000040000000000000000012000000008010008000004401000000000011004000000000000200400200

def t7 : Nat := 0x482000000000001208000000400010000000001000040000000000080040200000000200100800008041000000000020104000000

def t8 : Nat := 0x8000000000004000080002000000004800000000000800000000000000000000000000000000000000000000000000000000000000

def t9 : Nat := 0x40000000000000100000000000400090000000001000240000000000204010000000000810040000000c00009000000003000024000

def t10 : Nat := 0x40000080000000100400008000000000008010000000020000000000000000000000000000000000000000000000000000000000000

def t11 : Nat := 0x110000000000010020000000000002000000080000080000000000000000000000000000000000000000000000000000000000000000

def t12 : Nat := 0x24000408c00020a100400008008401190108014001100268000000000204010400100082810040000200c0001900800020b000026800

def t13 : Nat := 0x422800000880000c441280022000031104a00000000108a000000051104200000000000200400280000000801000a0000144410800000

def t14 : Nat := 0x426800408c80020e54168002a008431194b08014001108a680000051106240104001000a2850068000200c801190a800034f410826800

def t15 : Nat := 0x410090200000001040240800420400006048201081000018120800008c410090000000231040240000000000286050200000000a181408

def t16 : Nat := 0x4522902000880010c465280062040031704a20108100109a120800059d45209000000023304424280000000829605a200014441a981408

def t17 : Nat := 0x1000002480000020000000000000010000024800000200000000000000000000000000000000000000000000000000000000000000000000

def t18 : Nat := 0x10040024860040202020012080000184000349000042011000400000031004800402000000202401208008080c1102090000064114000000

def t19 : Nat := 0x100422a48600c82020e441288022018431134b00004201108a400000071104a00402000000202401288008080c11020b0000164514800000

def t20 : Nat := 0x100424248608c02020a1016080080184011b49080142011002680000031006840506001000a2a50160800a08cc111b09800026f114026800

def t21 : Nat := 0x184100b4b00004201140240800420500406248601483020218120800808cc110b0900000671140240000003100686050200000020a581608

def t22 : Nat := 0x184400349600442031200520800001844003496004420312005208008390c5902492000064316401208008390c5902492000064316401208

def t23 : Nat := 0x7150420a00c1ac0202ce440c8002a71e021124d8c2142807088280000071104200004001000ae040028000a000801120b800034c410802800

def t24 : Nat := 0x7360860204d42c028a6f000185542f5d2019249a1706304d0280808db87914560205436f020be54083c0fca200b0db24ba3f03cc4d3a83808

def t25 : Nat := 0x10904400348600402630200d248010098c080349200042411000d21800039045800402002020306409248008080c19024920000e4116001008

def t26 : Nat := 0x10984400349000042611000d24001009084802486004024212009218008190c5102090002064314408240000310849004820000c4212401208

def t27 : Nat := 0x27140000a4880200200440808800027140000a4880200200440808800000000000000000000000000000000000000000000000000000000000

def t28 : Nat := 0x27140022248c02c82024e08128000271c4111b4b80204201540a488000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t29 : Nat := 0x27140024a48c0ac02024e180c8000a71c4011b4988214201540a68800000000204010400100082810040000200c0001900800020b000026800

def t30 : Nat := 0x27140400a48e024020246081a8800271c4000b49802042015408488000031004800402000000202401208008080c1102090000064114000000

def t31 : Nat := 0x27140422a48802882004c4c1a800227140311a4a80200200548a088000051104200000000000200400280000000801000a0000144410800000

def t32 : Nat := 0x27144100b4a80200201440a48800427540006a48a030830044181a8800008c410090000000231040240000000000286050200000000a181408

def t33 : Nat := 0x27150420a48c1ac0202ce4c0c8002a71e0211a4d8c2142807488288000071104200004001000ae040028000a000801120b800034c410802800

def t34 : Nat := 0x27150422a48c1ac8202ce4c1e8002a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t35 : Nat := 0x40200820080000a000808000103640040201503020100104101200080000000000000000000000000000000000000000000000000000000000

def t36 : Nat := 0x40200824080408e000a0a100503648048601593128114105101268080000000204010400100082810040000200c0001900800020b000026800

def t37 : Nat := 0x40200c22880000a80080c441383662040231507a20100104109a000800051104200000000000200400280000000801000a0000144410800000

def t38 : Nat := 0x40204920982000a00090c024183642040201707820108104101a120800008c410090000000231040240000000000286050200000000a181408

def t39 : Nat := 0x500045009a200020021044640c2272040828605820108100009812180008ac41009a000008231040640200040020a86050200000000a181418

def t40 : Nat := 0x50204c20980000a00290c4441c3672040a2950582010010410980018000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t41 : Nat := 0x50204c209a0000a002908464143670040a295030201001041092001800082c00009a000008030000640200040020a040100000000008100410

def t42 : Nat := 0x50a04c20180000a00690800d3436500c0a095078201001441012921800019045000000002020304408240000000809004820000c4012001008

def t43 : Nat := 0x871e4000b058c214281640068800427550004248e1b40302c2180c0800a08c4101b01800022b104026800000200028605060010008ea181408

def t44 : Nat := 0xc72708208848dab0088ec442d8366a74722150148db10184e0982c007f3c6d0029da4ddfde1b8e02769a77f70423a0f416ddfd718ce8b92d17

def t45 : Nat := 0xc7370860a84ddaf028aef442d8776af5f221d25dadf16384f0b82c08ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t46 : Nat := 0xd00844119a1080340211046684223000082a4010408c00020a90041000282c00019a08000a0b0000668200040020a040104001000828100410

def t47 : Nat := 0x1009080c024850040242030092141018984408349204062611020d248808390c5d024922020e4317409248808390c5d024922020e4317409248

def t48 : Nat := 0x22716030024e84200280648800800427550402a48a1308300c44c1a88008080c11020b000016451480000000071104a204020000002c2481288

def t49 : Nat := 0x2800202000040c0100802080200004004104048002190010080540c080000000000000000000000000000000000000000000000000000000000

def t50 : Nat := 0x2800202240044c8d00822a90240004804944159012991410190566c080000000204010400100082810040000200c0001900800020b000026800

def t51 : Nat := 0x2a70603118068c210080648a2880042745002680081b88100cc5c0c8000200c0001902800030b400826800000401022601040010008e8180480

def t52 : Nat := 0x2a7160200a4c8c210280648828800427550404a48a1b00300c45c0c880000000000000000000000000000000000000000000000000000000000

def t53 : Nat := 0x2a716030024e8c210280648820800427550406a48a1b08300c45c1e88008080c11020b000016451480000000071104a204020000002c2481288

def t54 : Nat := 0x2a7160311a4e8c210280648a28800427550026a4881b88300cc5c0c8000200c0001902800030b400826800000401022601040010008e8180480

def t55 : Nat := 0x2a7160311a4e8c210280648a28800427550426a48a1b88300cc5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t56 : Nat := 0x2a7160311a4e8c210280748a28800427550426a48a1b88300cc5c1e88000000801000a000014441080000000051104200000000000200400280

def t57 : Nat := 0x2a7164300b4e8c210281648a68800427550406a48a1b08300c45c1e8800008c410090000000231040240000000000286050200000000a181408

def t58 : Nat := 0x2a71e031124f8c214280748828800427550422a48e1bc8302ce4c1e8800a080c11120b800036c51480280000071104a20406001000ae2481288

def t59 : Nat := 0x2a71e4200b4d8c214281748868800427550404a48e1b40302c65c1e88008080c110209000006411400000000031004800402000000202401208

def t60 : Nat := 0x2a71e4211b4d8c214281748868800427550424a48e1bc0302ce5c0c8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t61 : Nat := 0x2a71e4211b4d8c214281748a68800427550424a48e1bc0302ce5c0c8800200c0001900800020b00002680000000002040104001000828100400

def t62 : Nat := 0x2a71e4300b4f8c214281648868800427550406a48e1b48302c65c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t63 : Nat := 0x2a71e431134f8c214281748a60800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t64 : Nat := 0x2a71e4311b4f8c214281748a68800427550026a48c1bc8302ce5c1e8000a08cc111b0b800036f51482680000071106a60506001000aea581688

def t65 : Nat := 0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t66 : Nat := 0x2a71e4335b4fccad42837e9a6c8004a75d4437b49e9bdc303de5e7e8800a08cc315b1bc00136fd3c926c0000271d06a7950e00120baea5a7e88

def t67 : Nat := 0x2a71e4711b4fec254283768a7a8804275d4426b49e1bcc303de5c5e8800a39cc591b4ba00036f716c27a08008791c7b62596001064bfe581688

def t68 : Nat := 0x2a71e4733b4f8c29c2817cce7a800627550737a4ae1bc8302dede1e8800a59dc531b0b800036f714c26a8000071186b605a6001144efad81688

def t69 : Nat := 0x2b79e4711b4f8c2142e1748afac00527d584a6a48e1bc8342de5c9e9800a19cc511b0b800236f714c2ea4000071186b605860010c4afa581688

def t70 : Nat := 0x2c0220a200840c0b00882880210364004124158302190010490560c080000000000000000000000000000000000000000000000000000000000

def t71 : Nat := 0x2e73e4b31bcf8c2b42897c8a69836427552437a78e1bc8306de5e1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t72 : Nat := 0x2f71e4711bef8c2342a174ce68c227275586a6a58e1bc8302cedc1e9800a8acc111bab8000b6f5148668200047130ea60506001000aea581698

def t73 : Nat := 0x300228ae0004540c008a2b800115541849641992121506125906648480340020a04014400d00082810051024282c00099a08090a0b000266820

def t74 : Nat := 0x3271682c024cd424028263880014101f1d4408b0181606221c46448c0dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae0

def t75 : Nat := 0x327368ae024cd42c028a6f880195543f5d6419b49a1706325d46c48c8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t76 : Nat := 0x3a79ec391b4fac2142c1748afa980437d54426b48e1bc8363ce5cdec800a08cc191b4ba0003ef51682780800079147a60506003020bee5896c8

def t77 : Nat := 0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t78 : Nat := 0x427554526b4ae1bc8303ce5e5e8806a75e4317b4fac31c381749a7a8800079d47a69506001023bee5a568800a08cc397b5ba00036f51e9a7c08

def t79 : Nat := 0x467750c26ac8e1be830ace5c1f8b66a75e6315b7fac314385749a688800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t80 : Nat := 0x477554426be8e1be8323ce5e5eca23a71ec395b5f8c214281749a6890000f3d06a69f06001803aea5e56a800e08ecb15b1b800036f51c926c10

def t81 : Nat := 0x6a7570626a4cedbd8382eedc3e8806a75f4715b4fadb14381f4de6c8800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t82 : Nat := 0x6a75f4737b4fedbdc383fede7e8806a75f4737b4fedbdc383fede7e8800a79dc7b7b5be00136fffeda7e8800a79dc7b7b5be00136fffeda7e88

def t83 : Nat := 0x82794110224a80209e50440892a0082794110224a80209e50440892a0d88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c8

def t84 : Nat := 0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t85 : Nat := 0x877b45d22bea802a9e794c4edbe36f27d4b397a7aa0309f54549a9ab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t86 : Nat := 0x8d0a85d339a3080bdc791c46fbe36f20c0b3b707a609c9d561a9a9638002dbd45219a08002a2b30446eae0004002ba9605a60011c4c3a981418

def t87 : Nat := 0x8d7be5d22ba78c2bdef96c46fbe36f27d5b39727ae1b49f56d29a9e3800adbd4521ba18002a2b30446eae0004202ba9605a60011c4cfa981418

def t88 : Nat := 0x927b499e224ad02c9e5a4f0893b5583f9c711b36b8060fe75542ad2e0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t89 : Nat := 0xa27261b2200684289c986c8801a14c2745311382281309d14c44e08a05b44033a26016416d100ce89805907c2c2d302b9a281f0b0b4c0ae68a0

def t90 : Nat := 0xa27b61b2224e84289ed86c8893a14c27d53113a6a81309f54c44e9aa0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t91 : Nat := 0xad0a25f229a60c0b9cf92cc6f3e36f20c1b79787a21909d5490de9e38000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t92 : Nat := 0xae7271b228868dab9c98eccc2da36ea74733178368db19d94e4de2ca07f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t93 : Nat := 0xaf7b65f22bee8c2b9ef96ccefbe36f27d5b797a7aa1b09f54d4de9eb8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t94 : Nat := 0xaf7be5f33bef8c2bdef97ccefbe36f27d5b7b7a7ae1bc9f56dede9eb800adbdc531bab8002b6f714c6eae0004713beb605a60011c4efad81698

def t95 : Nat := 0xb27b69be224ed42c9eda6f8893b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t96 : Nat := 0xb27b69be226ed42c9eda6f8a93b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t97 : Nat := 0xb67b69be22ced42e9eda6f8893b77c3fdd751fb7ba170ff75d47edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t98 : Nat := 0xb77b6dfe2beed42e9efb6fced3f77f3fddf79fb7ba170ff75d4fedaf8dbcfbffff6bff636f9e7fffded7f8fcefbfffffbfba3f2bef7dffefef8

def t99 : Nat := 0xc27d51526a6ae1bc9f52ce5e9ea80aa79e5313b6f8c21ded1748afaa000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t100 : Nat := 0xc50e15d269a2219a9d798c56dfeb6fa0c2b39707e2c119dd4309ab238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t101 : Nat := 0xc67f51d26aeae1be9f5ace5e9fab6ea7de7317b7fac31dfd5749afaa800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t102 : Nat := 0xc77f55d26beaa1ba9f79cc5edfeb6fa7d6b397a7eac319fd4749abab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t103 : Nat := 0xc77f55d26beae1be9f7bce5edfeb6fa7def397b7fac31dfd5749afab8000fbd47a69f06003823bee5ed6e800e08efb97b5ba0003ef51e9a7c18

def t104 : Nat := 0xef7ff5f37befedbfdffbfedeffeb6fa7dff7b7b7fedbddfd7fedefeb800afbdc7b7bfbe003b6fffedefee800e79fffb7b5be0013efffeda7e98

def t105 : Nat := 0xf27f79fe6a4ef5bc9fdaefdc9fbd5ebfdf771bb6fad71fff5f4eefae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t106 : Nat := 0x10df3f4c28b858deb62a9ec646dc367a757a2d525cddb50386e3982c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t107 : Nat := 0x22c0220a240940c8b00882890250364c04120158b00993010480562c020350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t108 : Nat := 0x23c0228ae40945c8f008a2b90251774d849641d9b129d3612590766c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t109 : Nat := 0x27275586a6a58e1bc8302cedc1e9802f71e4711bef8c2342a174ce68c20047130ea60506001000aea58169800a8acc111bab8000b6f514866820

def t110 : Nat := 0x5c3fdd751bb6ba170ff75d46edae80b27b69be224ed42c9eda6f8893b5fcafbdf5fbbeba3f2bef7d7eefae8dbc793fff625f636f1e4fffd897d8

def t111 : Nat := 0x5f3ffffffbb6ff57cffffffeedbfd5f3ffffffbb6ff57cffffffeedbfdffefbfffffbffe3ffbefffffefff8ffefbfffffbffe3ffbefffffefff8

def t112 : Nat := 0x6427552437a78e1bc8306de5e1e8802e73e4b31bcf8c2b42897c8a698300071106a60506001000aea58168800a08cc111b0b800036f514826800

def t113 : Nat := 0x66c0632a358b40d9b018ca8d62d0366c0632a358b40d9b018ca8d62d0327786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d37

def t114 : Nat := 0x66e7672a358948dbb018cecdc2d8366e7672a358948dbb018cecdc2d837f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t115 : Nat := 0x6c00c0311703220109d54101292280840a019220a2000a9c58080293230000000000000000000000000000000000000000000000000000000000

def t116 : Nat := 0x6c27d53537a7ae1bc9f56de5e9ea80ae7be5b33bef8c2bded97c8afba300071106a60506001000aea58168800a08cc111b0b800036f514826800

def t117 : Nat := 0x6c40e039370b2201a9d5c1812932b6c40e039370b2201a9d5c1812932b0000000000000000000000000000000000000000000000000000000000

def t118 : Nat := 0x6c50e07d379b2201a9d7d1c56d3eb6f60e0bbb70fa201a9d5c189a933b000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t119 : Nat := 0x6cc76738268b48dbb9d9cec542da36ee7673b150b68db31d9ce09a2d237f7c6f3a2fdb4ddfde1b8e83f6db77f786e3a0fdb6ddfdf1bce8bf6d37

def t120 : Nat := 0x6ee7673b378b68dbb9d9cecde2da36ee7673b378b68dbb9d9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t121 : Nat := 0x6ee7673b378b68dbb9d9cecde2da36ee7673b378b6adbb9d9cfcde2dab7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t122 : Nat := 0x6ee7673b378fe8dbb9d9cfcde2da36ee7673f378b68dbb9d9cecde3fa37f7c6fba3fdbeddfdf5fcf8bf6db77f7d7f3e2fdb6ddfdf1bee8ff6fb7

def t123 : Nat := 0x6ee7773b37afe8dbb9f9cecde2da36ee7773b37afe8dbb9f9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t124 : Nat := 0x6ee7773f37afeedbf9f9eeede3fab6ee77f7b37bff8dbbdf9dfcde6da37f7f7f3eafdf6fdfdf1beeaff7fbf7ffceffb3ffbfddfdf7fdfcbf6db7

def t125 : Nat := 0x6ee7f73b37afe8dbb9fdcecdebfa36ee7f73b37afe8dbb9fdcecdebfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t126 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t127 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46dbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t128 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2200a9c790c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t129 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2200a9c791c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t130 : Nat := 0x6f20c0b39707a20109d54109a92380c50e05d269a2201a9d790c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t131 : Nat := 0x6f20c0b39707a20909d54109a963808d0a05d229a2080b9c790c46f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t132 : Nat := 0x6f20c0b39707a60149d56129a92380850a85d229a3000adc791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t133 : Nat := 0x6f20c0b39787a20109d54109a9a380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t134 : Nat := 0x6f20c0b39787a20109d54149a92b80870a05d229ea000a9c790c4ed3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t135 : Nat := 0x6f20c0b3b707a20189d54189a92380850a05d339a2000a9c791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t136 : Nat := 0x6f20c0b3b707a609c9d561a9a963808d0a85d339a3080bdc791c46fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t137 : Nat := 0x6f20c0b79707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t138 : Nat := 0x6f20c0b79787a20109d5410de92380a50a05f229a2000a9c790cc6d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t139 : Nat := 0x6f20c1b79787a21909d5490de9e380ad0a25f229a60c0b9cf92cc6f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t140 : Nat := 0x6f20c1b7b787a619c9d569ade9e380ad0aa5f339a70c0bdcf93cc6fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t141 : Nat := 0x6f20c8f39717b2010dd55109ad2380850a05d229a2400e9c7b0e46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t142 : Nat := 0x6f20d0b39727a20109f54109a92380850b05d22bea000a9e790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t143 : Nat := 0x6f20e2bbf707e741c9dde3b9a933d5c58e97d3b9a3215afd7d9c66dbeb034002ba9605e600d1c4c3a981518242dbd45299a08092a2b30466eae0

def t144 : Nat := 0x6f27d4b397a7aa0309f54549a9ab80877b45d22bea802a9e794c4edbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t145 : Nat := 0x6f27d4b3b7a7ae0bc9f565e9a9eb808f7bc5d33beb882bde795c4efbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t146 : Nat := 0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0

def t147 : Nat := 0x6f27d5b797a7aa1b09f54d4de9eb80af7b65f22bee8c2b9ef96ccefbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t148 : Nat := 0x6f27d5b7b7a7ae1bc9f56dede9eb80af7be5f33bef8c2bdef97ccefbe3004713beb605a60011c4efad8169800adbdc531bab8002b6f714c6eae0

def t149 : Nat := 0x6f27d6b3d727ef4349fd6739a923c185fbd5d2aba3816afe79cc66dbe3dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae0

def t150 : Nat := 0x6f30c0f79717a20109d75109ad2780950a0dda29a2000a9c790c46d3f3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t151 : Nat := 0x6f60c0b3970fa20129d54109a923a2850a05d269b2000a9c790c56d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t152 : Nat := 0x6f60e0bbb70fa201a9d5c189a933b6c50e07d379b2201a9d7d1c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t153 : Nat := 0x6f60e0bbb70fa609e9d5e1a9a973b6cd0e87d379b3281bdd7d1c56fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t154 : Nat := 0x6f70e0ffb79fa201a9d7d1cded3fb6f70e0ffb79fa201a9d7d1cded3fb004dbfffb69fa20029e771eded6f8004dbfffb69fa20029e771eded6f8

def t155 : Nat := 0x6fa0c0b39707a28119d54109ab2380850a05d269a2008a9c790c56d7e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t156 : Nat := 0x6fa0c2b39707e2c119dd4309ab2380c50e15d269a2219a9d798c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t157 : Nat := 0x6fa0c2b3b707e6c9d9dd63a9ab6380cd0e95d379a3299bdd799c56ffeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t158 : Nat := 0x6fa7d6b397a7eac319fd4749abab80c77f55d26beaa1ba9f79cc5edfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t159 : Nat := 0x6fa7def397b7fac31dfd5749afab80c77f55d26beae1be9f7bce5edfeb00e08efb97b5ba0003ef51e9a7c18000fbd47a69f06003823bee5ed6e8

def t160 : Nat := 0x6fe0e2bbb70fe2c1b9ddc389ab33b6c50e17d379b2219a9d7d9c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t161 : Nat := 0x6fe7f7bbf7afeddbf9fdeefdebfb77effff7f3fbffadfbfffdfcfeffebffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t162 : Nat := 0x80000000004000200000000010000800000000040002000000000100000000000000000000000000000000000000000000000000000000000000

def t163 : Nat := 0x80c02208604845e8f008a2b012507f48849201d4112bd1610490312c0803104000004045c0d41082001010724304000094009c90618000212807

def t164 : Nat := 0x81000080c04005204000203010014901808440850122406021102140480000000000000000000000000000000000000000000000000000000000

def t165 : Nat := 0x81000080e4400528c00020b1104149098084419d012a416021102368480000000204010400100082810040000200c0001900800020b000026800

def t166 : Nat := 0x81001084c0648720402020301121c9018184408749224062211021404800031004800402000000202401208008080c1102090000064114000000

def t167 : Nat := 0x810018c0c0749520442031301401490181844087496244622312215248008080c110209000006411400000000031004800402000000202401208

def t168 : Nat := 0x81402088e0480520e000a0b010117f41848641d53122506125103340480000000000000000000000000000000000000000000000000000000000

def t169 : Nat := 0x83a71ec3d1f4fde254283778b6894943f5d442ef49e3fce323de7d5ec800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t170 : Nat := 0x83c0228ae04845e0f008a2b812117f41849641dd3123d0612590774c480000000000000000000000000000000000000000000000000000000000

def t171 : Nat := 0x83c0228ae04845e8f008a2b812517f49849641dd312bd1612590776c480350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t172 : Nat := 0x85275584e6e48f3bc8302cf5d1e9c92bf1e4719f4fae6162a174ab68c800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t173 : Nat := 0x8950a0dde2da2520e9c7b0f47d3f7ff38c8f79f57b2250fd7510bbd278000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t174 : Nat := 0x8b27b69be264ed62c9eda6f8993b5dc3fdd751bf6ba370ff75d46fdae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t175 : Nat := 0x9018084408501224060211021404881000080c040052040002030100140000000000000000000000000000000000000000000000000000000000

def t176 : Nat := 0x9018184448701524462230321404491081880c8649724462021321001c8083904540201020202030540824080820080d024922000c4013001008

def t177 : Nat := 0x9058210c6848053ce202a8b650547f3880aa2d94151e41608431a12014ff1f7104684a45fffc10ae16583e7fff042b85960f9ffc7dc411a12917

def t178 : Nat := 0x905f3d4c68f81d3ee622bcf654dc7f3af1ea2d965dde65628673a92014ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t179 : Nat := 0x908f1f0048605dfe56282e3212c04908f1f0048605dfe56282e3212c04ffb2400049605dffd6188e1212907ffb2400049605dffd6188e1212907

def t180 : Nat := 0x909f1f4448f05dfe562a3e7656cc493af1f82c864ddfe56282e3a92c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t181 : Nat := 0x90d8094408d810bc3602180656c42a3800282c44145e8500822391241424386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t182 : Nat := 0x90d8294c28d810bcb60298c656dc3e7a042a2d545c7e9501863399241c243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151f

def t183 : Nat := 0x90d82a48485851e4360a921216147f50841a0cc41073d421068331041cffb8ec4149fa59ffee3b10527e967ff52423ace4547ffd4908eb39151f

def t184 : Nat := 0x90d82b4c685855fcf60abab656547f7884ba2dd4157fd56186b3b1241cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t185 : Nat := 0x90df3e4868785de6f62ab6f2161c7f52f5da0dd659f3f46306d3390c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t186 : Nat := 0x90df3f4c48f859f6362a9e56569c7f72f57a2cc65cf7f42386e3b9041cffbffd4569fa59ffee3b3c567ebe7ffd242bade65f7ffd5d4cfbb9151f

def t187 : Nat := 0x90df3f4c68f85dfef62abef656dc7f7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t188 : Nat := 0x90df3f4c68f85dfef62abef656dc7f7af5fa2dd67dfff56386f3bb2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t189 : Nat := 0x90df3f4c68f85ffef62abff656dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t190 : Nat := 0x90df3f4c6cf85dfef62abef756dc7f7af5fe2ddf5dfff56387f3bb6c1cffbffd476dfb5dfffe3bbed77efe7fff24ebadff5ffffd7dfcfbbb7d1f

def t191 : Nat := 0x90ff3f4c68fcddfef62abef6d6dc7f7af5fa2dde5dfff56386f7b92c9cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t192 : Nat := 0x911808c4c8501724460231321405c911808c4c8501724460231321405c0000000000000000000000000000000000000000000000000000000000

def t193 : Nat := 0x911818c4c87015244622303214054911818c4c8749724462231321405c8083904540201020202030540824080820080d024922000c4013001008

def t194 : Nat := 0x911818c4c8749724462231321405c911818c4c8749724462231321405c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t195 : Nat := 0x911818c4c8749724462231321405c911818c4c8749724462231321525c008080c110209000006411400000000031004800402000000202401208

def t196 : Nat := 0x911898c0c8749524462631321d254911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t197 : Nat := 0x911898c0c8749724462631321c05c911898c4c8701724462630321d25c808280c1d024922020e411700904880839045c024122020a0307409248

def t198 : Nat := 0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t199 : Nat := 0x911898c4c8749724462631321d25c911898c4c8769724462631323d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t200 : Nat := 0x911898c4c8749724462631321d25c9518d8c4cc749725463631331d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t201 : Nat := 0x911898c4c8f49724462631365d25c931898c6c87497244626313a1d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t202 : Nat := 0x911898c4c8f49724462631721d2dc913898c4c8749724462631329d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t203 : Nat := 0x911898c4cc74972c462631331d65c919898c4c87497a4562631321f25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t204 : Nat := 0x911898c4eaf49724ce2631f65d2dc933898c7d974b7244626313abd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t205 : Nat := 0x911898c4ec74972cc62631b31d65c919898c4d9f497a4562631323fa5c808390c7d425962030e4b3f50964880a39cc5d1b49a2022ef31742fa48

def t206 : Nat := 0x911898c5c8f4b724462631723d2dc9538d8c4ce7497254e3631339d25c80839cc5d0b4922020e731742d248808390c7d625922020e431f589648

def t207 : Nat := 0x913f9cc4c8f49f26462635729dadc913f9cc4c8f49f26462635729dadc808390c5d024922020e4317409248808390c5d024922020e4317409248

def t208 : Nat := 0x913f9cc4eaf49f26ce2635f6ddadc933f9cc7d9f4bf264626357abdadc808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t209 : Nat := 0x9158b8cce87c9724e626b1b21d35ff518d8e4dd779725463671333d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t210 : Nat := 0x9158b8cceafc9724ee26b1f65d3dff738d8e7dd77b7254636713bbd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t211 : Nat := 0x91df3fcce8f85dfef62abef656dd7f7bf5fe6dd75dfff563a7f3b96c5cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t212 : Nat := 0x91dfbfcce8fcdffef62ebff65ffdff7bfdfe6dd75dfff563e7f3b9fe5cffbffdc5f9fedffffeffbf767fbeffff3d2ffdf65fffff7fcffff9bf5f

def t213 : Nat := 0x92df3f4e68f85dfef62abefe56dc7f7af5fa6dde5dfff56386f3fd2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t214 : Nat := 0x92ff3f4f79fcfdfef62abffef6dc7f7af5fa6ffe5dfffde386fffd3e9cffbffdc579fafdffff7fff5e7ebe7fff753beff65ffffd7dcefbf93f9f

def t215 : Nat := 0x933898c7d974b7244626313abd25c911898c4eaf49724ce2631f65d2dc808390c5d024b22021e4717c09248808791c5f024922020e43174092c8

def t216 : Nat := 0x933f9ec7c874ff66462e377a9d2dc953fddc4caf49f374e363d76ddadc808390c5d024b22021e4717c09248808791c5f224922020e43d74892c8

def t217 : Nat := 0x93989ac6c874d7e4562e333a1f25c9518d9c4ccf4973d463639375de5c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t218 : Nat := 0x93bf9ec6c8f4dfe6562e377a9fadc953fddc4ccf49f3f46363d77ddedc808390c5d024922020e4317409248808390c5d024922020e4317409248

def t219 : Nat := 0x93bf9ec7d9f4ffe6562e377abfadc953fddc4eef49f3fce363df7ddedc80a39cc5d1b4ba2023ef717c2fa48808791c7f625962030e4bff5896c8

def t220 : Nat := 0x93d8bacee87cd7e4f62eb3ba1f35ff518d9e4ddf7973d463679377de5c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t221 : Nat := 0x93ff3fcee8fcddfef62abefed6dd7f7bf5fe6ddf5dfff563a7f7fd6cdcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t222 : Nat := 0x943f5d442ef49e3fce323de7d5ec883a71ec3d1f4fde254283778b689400071106a60506001000aea58168800a08cc111b0b800036f514826800

def t223 : Nat := 0x94df7f4c6cf85ffff63abef756dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t224 : Nat := 0x94ff7f4c6efcdffffe3abef7d7fcff7af5fe3ddf5ffff56387f7bb6c9cffbffd47efff5ffffe3bbef7fffeffff2cefbdff5ffffd7ffdffbb7d1f

def t225 : Nat := 0x9518d9c4ccf4973d463639375de5c93989ac6c874d7e4562e333a1f25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t226 : Nat := 0x953f5dc4eef49f3fce323df7d5edc93bf1ec7d9f4ffe6562a377ab68dc00071106a60506001000aea58168800a08cc111b0b800036f514826800

def t227 : Nat := 0x953fddc4eef49f3fce363df7ddedc93bf9ec7d9f4ffe6562e377abfadc808791c7f625962030e4bff5896c880a39cc5d1b4ba2023ef717c2fa48

def t228 : Nat := 0x97bfdfc7fff4ffffde3e3fffffedc97bfdfc7fff4ffffde3e3fffffedc80a79dc7f7b5be2033effffdafec880a79dc7f7b5be2033effffdafec8

def t229 : Nat := 0x9858a85d2ada3224afc791c67d3ebef20c0b3d747a72149d56139b923c000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t230 : Nat := 0x9858b85d6afa3524efe7b0f67d3e7ff28d8b3df67b7254ff5613bb923c808fbd4560ba1020282330546c2e080c202bad625b22001c441b981418

def t231 : Nat := 0x98dfbf5d6afa7dfeffefbef67ffe7ffafdfb3df67ffff5ffd6f3bbbe3cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t232 : Nat := 0x991898d5ca76b7244fe731323d27c991898d5ca76b7244fe731323d27c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t233 : Nat := 0x993f9cd5ca74bf264fe735729d2fc993f9cd5ca74bf264fe735729d2fcd88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c8

def t234 : Nat := 0x9958a8ddeada3724efc7b1f67d3ffff38c8f7df57b7254fd7713bbd27c000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t235 : Nat := 0x9958b8ddeafeb724efe7b1f67d3ffff38d8f7df77b7254ff7713bbd27c808fbdc5f0be922028e731746d2e880c392ffd625b22021e471fd89658

def t236 : Nat := 0x9b3fbedfea74ff66cfefb7fa9d3fddd3fddf5dbf6bf374ff77d76fdafcdbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t237 : Nat := 0x9bffbedffbfeffe6ffefb7feffbffff3fddf7fff7bf3fcff77dfffdefc80afbdc5f1beba202bef717c6fae880c793fff625b62031e4fffd896d8

def t238 : Nat := 0x9bffbfdfeafcfdfeffefbefedfff7ffbfdff7dff7ffff5fff7f7fffefcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t239 : Nat := 0x9d7ffdddeefebf3feff7bdf7fdfffffbfdef7dff7ffe75fff777bbfafc808fbdc7f6bf962038e7bff5ed6e880e39effd7b5ba2023ef71fdafe58

def t240 : Nat := 0xa0c00000044900a83000000112402a0c00000044900a8300000011240200104000004001c0041000001000700104000004001c00410000010007

def t241 : Nat := 0xa0c00000244904a8f00020a112402a0c0084015d910a83400110136c0200104002044105c0141082811040700304c0001d009c0061b000036807

def t242 : Nat := 0xa0c02008244900a8b000808112503e4c04020154b02a9301041013240a00104000004001c0041000001000700104000004001c00410000010007

def t243 : Nat := 0xa1c00080c44905a87000203112416b0d808440c5912ac360211031644a00104000004001c0041000001000700104000004001c00410000010007

def t244 : Nat := 0xa2e71e4315fdf8ea34281749b6c82a4e7550426ed8ebbf8302ce5d3e8a00b0ccc111f0b9c0077f51483680700175106a64507c01410aea59168f

def t245 : Nat := 0xa3c0228ae44945e8f008a2b912517f4d849641d5b12bd361259077644a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t246 : Nat := 0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t247 : Nat := 0xa3c0228ee6c945e8f808a2fd53797f6f849671ddfb2bd3612590ff6c4a0355530e244145c0d410a2851079724386c8019daa9c90f5f410a76827

def t248 : Nat := 0xa3c022cbe4d965e8f008b2f936597f4f849641fdf92bd3e125907f7e4a0350ce4b04d145c0d43392c13451724386c028fdf0bc90e1b00a3f7c2f

def t249 : Nat := 0xa3c02acaf5d955e8f408b3b936d17f4d849643ddb16bdf61279a776c4a03704e0a05d14dc0d61b828136d1724386c020ddb0dc91e1b828376c27

def t250 : Nat := 0xa3c0328ee46dc7e8f028a2b91371ff4d859641dff92bd3632590776c4a0353520e844547c0d410a2a51171f24b8ecc119fa99c90e7f114276827

def t251 : Nat := 0xa3c03acae47dd5e8f428b3b916517f4d859641dff96bd7632792777e4a03d0c2cb1461d5c0d47493c110517243b7c0489de0bc90e1b202677a2f

def t252 : Nat := 0xa3e7368ae4edcdeaf028a6f992d97f4ff5d641dff9abf36325d47f6cca0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t253 : Nat := 0xa3e73ecbf5fdfdeaf428b7f9b6d97f4ff5d643fff9ebffe327de7f7eca03f0cecb15f1fdc0d77fd3c936d17243f7d06afdf0fc91e1baea7f7eaf

def t254 : Nat := 0xa7c0638ee4c947f9f018aabd52d1ff6d84b661ddb52fd361a5b0f76c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t255 : Nat := 0xa7e0628ae64dc7e9f818a2b99371ff4d849651ddb32bd3612594776cca0350420a864547c0d41082a19151f2438ec4109da09c90e3b104276827

def t256 : Nat := 0xa7e7778ee6edcffbf838aefdd3f9ff6ff5f671dfffaff363a5f4ff6cca0357530ea64547c0d410aea59179f24b8ecc119fab9c90f7f514a76827

def t257 : Nat := 0xa7e77fcff7fdfffbfc38bffdf7f9ff6ff5f673ffffefffe3a7feff7eca03f7dfcfb7f5ffc0d77fffedb7f9f24bffdc7bfffbfc91f7fffeff7eaf

def t258 : Nat := 0xabc0a29be64b65e8f9cda2b93b737fcd8c9751fdb32bd3fd759077fe6a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t259 : Nat := 0xabd0a2dfe6db65e8f9cfb2fd7f7f7fff8c9f79fdfb2bd3fd7590fffe7a035dff4f24db45c0fc33b2c57c7f724786eba9fdfabc90fdf41abf7c3f

def t260 : Nat := 0xabe7b69be66dedeaf9eda6f99b7b7fcffdd751fffbabf3ff75d47ffeeadbd7d3fff665f7f6f5f4fffd997dffcbffdf5fbfebbff2fff7d7effaef

def t261 : Nat := 0xabf7bedff7fffdeafdefb7fdffff7ffffddf7bfffbebffff77defffefa03fdffcf35fbfdc0ff7ff3cd7eff7247f7fbebfdfafc91fdfefaff7ebf

def t262 : Nat := 0xaff7f7dfe6ffeffbf9ffbefdfffffffffdff79ffffaff3fff5f4fffefa035fff4fa6df47c0fc33bee5fd7ff24f8eefb9fffbbc90fff51ebf7c3f

def t263 : Nat := 0xb1d898c4cc7d97ac762631331f65eb1d898c4cc7d97ac762631331f65e8093d0c5d06493e024f431741924f8093d0c5d06493e024f431741924f

def t264 : Nat := 0xb3d82aceec5957ecf60ab3bb1655ff5d849e4dddb17bd7612793776c5e0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t265 : Nat := 0xb3d8baceec7dd7ecf62eb3bb1f75ff5d8d9e4ddff97bd763679377fe5e83d3d2cfd465d7e0f4f4b3f51975fa4bbfcc5d9fe9be92eff31767fa6f

def t266 : Nat := 0xb3df3fceecf95dfef62abeff56dd7f7ff5fe6ddffdfff763a7f3ff6c5effffff4f6dfb5dfffe3bbed77eff7fffa6ebadfffffffdfdfcfbbf7d3f

def t267 : Nat := 0xb3ffbecffdfdffeef62eb7fbbffdff5ffdde4ffff9fbffe367df7ffede83f3decfd5f5ffe0f7fff3fd3ff5fa4bffdc7ffff9fe93effbff7ffeef

def t268 : Nat := 0xb7ffffceeefddffffe3ebfffdffdff7ffdfe7ddffffff763e7f7fffede83d7d3cff665d7e0f4f4bff5997dfa4bbfcc5d9febbe92fff717e7fa6f

def t269 : Nat := 0xdcffff7d7bfefffffffffff6fffefffafffbbff65ffffdffdeffb9bfbdffbffdf5fbfeffffffffff7effbeffff7d3ffff65fffff7fcffff9bfdf

def t270 : Nat := 0xe7c062aaf54b47e9f018e3b93251ff4d8696c3ddb12bdb612d98776d4b0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t271 : Nat := 0xef20c0b39747a22109d54109b92388850a05d22da2020a9c790c47d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t272 : Nat := 0xef20c0b3d747a72149d56139b923c9858a85d2ada3224afc791c67d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t273 : Nat := 0xef20c0b3f747a729c9d561b9b963c98d8a85d3bda32a4bfc791c67fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t274 : Nat := 0xef60e0bbf74fa721e9d5e1b9b933ffc58e87d3fdb3225afd7d1c77d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t275 : Nat := 0xefa0c2b3d747e7e159dd6339bb23c9c58e95d2eda323dafd799c77dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t276 : Nat := 0xefc0e2bbf74b67e9f9dde3b93b73ffcd8e97d3fdb32bdbfd7d9877ff6b0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t277 : Nat := 0xefe0e2bbf74fe7e9f9dde3b9bb73ffcd8e97d3fdb32bdbfd7d9c77ffeb035042ba9645e7c0d5d4c3a99151f243dfd4529da09c92e3b30467eae7

def t278 : Nat := 0xefe767bbf7cb6dfbf9d9eefdf2db7feff6f7f3fdb7affbfdbdfcff6deb7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t279 : Nat := 0xefe7f7bff7efeffbf9fdeffdfbfbffeffff7f3ffffaffbfffdfcffffeb035753beb645e7c0d5d4efad9179f24bdfdc539fab9c92f7f714e7eae7

def t280 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t281 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44947e8f008a3b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t282 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44b45e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t283 : Nat := 0xf4d849641ddb12bd3612590776c4aa7c0628ae44947e9f018a2b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t284 : Nat := 0xf4d849641ddb12bd3612594776ccaa3e0228ae44dc5e8f008a2b99251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t285 : Nat := 0xf4d849641ddb16bd7612792776c4aa3c02acae45955e8f408b3b91651724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t286 : Nat := 0xf4d849641fdb12bd3e12590777e4aa3c0228be44965e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t287 : Nat := 0xf4d849643ddb12bdb612598776c4aa3c0228af54945e8f008a3b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t288 : Nat := 0xf4d859641dff92bd3632590776c4aa3c0328ae46dc5e8f028a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t289 : Nat := 0xf4d8696c3ddb12bdb612d98776d4be7c062aaf54b47e9f018e3b93251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t290 : Nat := 0xf4df7f6c7dfb5ffff63afff776dcff7ef7faafd6ddffff638efbb92d1fffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t291 : Nat := 0xf4ff5d641dff9abf36325d47f6ccaa3e7368ae4edcdeaf028a6f992d9724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t292 : Nat := 0xf4ff5d643fff9ebffe327de7f7ecaa3e73ecbf5fdfdeaf428b7f9b6d97243f7d06afdf0fc91e1baea7f7eaf03f0cecb15f1fdc0d77fd3c936d17

def t293 : Nat := 0xf518d8e4dd779725463671333d25c9158b8cce87c9724e626b1b21d35f808390c5d024922020e4317409248808390c5d024922020e4317409248

def t294 : Nat := 0xf5d849e4dddb17bd7612793776c5eb3d82aceec5957ecf60ab3bb1655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t295 : Nat := 0xf5d869ecfddb17bdf612f9b776d5ff7d86aeefd5b57edf61af3bb3655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t296 : Nat := 0xf5d8d9e4ddff97bd763679377fe5eb3d8baceec7dd7ecf62eb3bb1f75fa4bbfcc5d9fe9be92eff31767fa6f83d3d2cfd465d7e0f4f4b3f51975f

def t297 : Nat := 0xf6d84b661ddb52fd361a5b0f76c4aa7c0638ee4c947f9f018aabd52d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t298 : Nat := 0xf6d86b6e3ddb52fdb61adb8f76d4be7c063aef5cb47f9f018ebbd72d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t299 : Nat := 0xf6ff5f661dffdaff363a5f4ff6ccaa7e7778ee4edcffbf038aefdd2d9f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t300 : Nat := 0xf6ff5f671dfffaff363a5f4ff6ccaa7e7778ee6edcffbf838aefdd3f9f24b8ecc119fab9c90f7f514a768270357530ea64547c0d410aea59179f

def t301 : Nat := 0xf7af5fa2dd65dfff56386f3b92c1c90df3f4c68f85dfef62abef656dc7fff242badf65ffffd7dccfbb93d1fffbffd4569fa5dfffe3bbe567ebe7

def t302 : Nat := 0xf7d86beefddb57fdf61afbbf76d5ff7d86beefddb57fdf61afbbf76d5f27786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d37

def t303 : Nat := 0xf7d8fbeefdffd7fdf63efbbf7ff5ff7d8fbeefdffd7fdf63efbbf7ff5fa7fbfecfddffdfe9feffb3f77ff7fa7fbfecfddffdfe9feffb3f77ff7f

def t304 : Nat := 0xf7ff7feefdfddffff63affffd6ddff7ff7feefdfddffff63affffd6ddfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t305 : Nat := 0xf7ff7feeffffdffffe3afffff7fdff7ff7feffdfffffff63afffff6ddf277f7f0eafdf4fc9de1baea7f7fbf27f8eecb1dfbfdc9df7fd3cb76d37

def t306 : Nat := 0xfbd8aafbd95b71e437cfd31a3e177fd58e1bcee4b073debd7e8b75977ffff8eef959faf9ffefff515a7e977ff5f733eee4f47fffc90aeb7d97ff

def t307 : Nat := 0xfbdfbffff9fb7dfef7effffe7edf7ffffffbeff6fdfffffffefbfdbf7ffffffffd79fafdffffffff5e7ebf7ffff73beff6fffffffdcefbfdbfff

def t308 : Nat := 0xfcd8c9751fdb32bd3fd759077fe6aabc0a29be64b65e8f9cda2b93b73724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t309 : Nat := 0xfcd8e97d3fdb32bdbfd7d9877ff6befc0e2bbf74b67e9f9dde3b93b73f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t310 : Nat := 0xfcd8e97d3fdb32bdbfd7d9c77ffebefe0e2bbf74fe7e9f9dde3b9bb73f243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151f

def t311 : Nat := 0xfd18d8f5df77b7254ff771333d27c9958b8ddea7eb724efe7b1b23d37f808390c5d024922020e4317409248808390c5d024922020e4317409248

def t312 : Nat := 0xfd58e1bcee4b073debd7e8b75977ffbd8aafbd95b71e437cfd31a3e177ff5f733eee4f47fffc90aeb7d97fffff8eef959faf9ffefff515a7e977

def t313 : Nat := 0xfddffffceefb5ffffffffef75fffffffffffbdd7fffff77ffff3bbed7fffffff7fefff5ffffebbbef7ffffffffaeefbdfffffffffffdffbffd7f

def t314 : Nat := 0xfeff7f7f7ffb7dfffffbfefff6de7ffef7fbbffeffffffff9effff2dbfffffff7f6ffb7dffff3bfedffeff7fffe6fbaffffffffdfdfcfbbf7dbf

def t315 : Nat := 0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0

def t316 : Nat := 0xff38c8f79f57b2250fd7510bbd2788950a0dde2da2520e9c7b0f47d3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t317 : Nat := 0xff38c8f7df57b7254fd7713bbd27c9958a8ddeada3724efc7b1f67d3ff004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t318 : Nat := 0xff38c9f79fd7b23d0fd7590ffde788bd0a2dfe2da65e0f9cfb2fc7f3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t319 : Nat := 0xff38d8f7df77b7254ff7713bbd27c9958b8ddeafeb724efe7b1f67d3ff80c392ffd625b22021e471fd89658808fbdc5f0be922028e731746d2e8

def t320 : Nat := 0xfff8c9f79fdfb2bd3fd7590fffe7aabd0a2dfe6db65e8f9cfb2fd7f7f724786eba9fdfabc90fdf41abf7c3f035dff4f24db45c0fc33b2c57c7f7

def t321 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [] else []) else (if i < 7 then [t52,t84,t126,t225,t246,t280] else [t52,t84,t139,t198,t246,t280]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t65,t77,t84,t126,t220,t280,t302] else [t65,t77,t84,t246,t294,t317]) else (if i < 11 then [t65,t77,t84,t246,t308,t311] else [t65,t77,t84,t258,t280,t293])) else (if i < 14 then (if i < 13 then [t65,t77,t84,t276,t280,t311] else [t65,t77,t117,t198,t246,t280]) else (if i < 15 then [t65,t77,t118,t198,t276,t280] else [t65,t77,t173,t246,t280,t316])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t65,t77,t234,t246,t280,t317] else [t65,t77,t235,t246,t308,t319]) else (if i < 19 then [t65,t84,t112,t198,t258,t280] else [t65,t84,t116,t198,t246,t308])) else (if i < 22 then (if i < 21 then [t65,t84,t116,t198,t276,t280] else [t65,t101,t126,t198,t246,t309]) else (if i < 23 then [t65,t102,t147,t198,t246,t280] else [t65,t126,t173,t222,t246,t280]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t65,t126,t226,t234,t246,t280] else [t27,t65,t84,t126,t225,t246,t280]) else (if i < 27 then [t27,t65,t84,t139,t198,t246,t280] else [t27,t84,t126,t219,t227,t246,t280])) else (if i < 30 then (if i < 29 then [t33,t65,t84,t126,t198,t246,t280] else [t33,t65,t84,t187,t198,t246,t280]) else (if i < 31 then [t34,t65,t84,t126,t198,t246,t280] else [t35,t65,t77,t115,t198,t246,t280]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t35,t65,t77,t126,t198,t246,t308] else [t45,t65,t77,t84,t198,t246,t280]) else (if i < 35 then [t52,t77,t84,t95,t126,t198,t246] else [t52,t77,t84,t110,t126,t198,t280])) else (if i < 38 then (if i < 37 then [t52,t77,t84,t120,t126,t246,t280] else [t52,t77,t84,t126,t198,t246,t280]) else (if i < 39 then [t52,t77,t84,t126,t198,t246,t299] else [t52,t77,t84,t126,t198,t252,t280]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t52,t77,t84,t126,t218,t246,t280] else [t52,t77,t84,t158,t198,t246,t280]) else (if i < 43 then [t52,t77,t84,t187,t198,t246,t280] else [t52,t77,t93,t126,t198,t246,t280])) else (if i < 46 then (if i < 45 then [t52,t77,t126,t198,t246,t280,t301] else [t52,t81,t84,t126,t198,t246,t280]) else (if i < 47 then [t52,t84,t126,t148,t198,t246,t280] else [t52,t84,t126,t198,t227,t246,t280])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t52,t84,t126,t198,t246,t280,t306] else [t53,t77,t84,t95,t126,t198,t246]) else (if i < 51 then [t53,t77,t84,t126,t198,t246,t280] else [t54,t77,t84,t120,t126,t246,t280])) else (if i < 54 then (if i < 53 then [t54,t77,t84,t126,t198,t246,t280] else [t55,t77,t84,t126,t198,t246,t280]) else (if i < 55 then [t56,t77,t84,t126,t198,t246,t280] else [t57,t77,t84,t126,t198,t246,t280]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t58,t77,t84,t126,t198,t246,t280] else [t59,t77,t84,t126,t198,t246,t280]) else (if i < 59 then [t60,t77,t84,t126,t198,t246,t280] else [t61,t77,t84,t126,t198,t246,t280])) else (if i < 62 then (if i < 61 then [t62,t77,t84,t126,t198,t246,t280] else [t63,t77,t84,t126,t198,t246,t280]) else (if i < 63 then [t64,t77,t84,t126,t198,t246,t280] else [t65,t70,t77,t84,t126,t198,t280,t302])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t65,t75,t77,t84,t126,t198,t246] else [t65,t77,t84,t88,t126,t198,t246]) else (if i < 67 then [t65,t77,t84,t90,t126,t198,t246] else [t65,t77,t84,t92,t126,t246,t280])) else (if i < 70 then (if i < 69 then [t65,t77,t84,t95,t110,t120,t126] else [t65,t77,t84,t95,t110,t126,t198]) else (if i < 71 then [t65,t77,t84,t95,t110,t187,t198] else [t65,t77,t84,t95,t120,t126,t246]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t65,t77,t84,t95,t120,t187,t246] else [t65,t77,t84,t95,t126,t192,t246]) else (if i < 75 then [t65,t77,t84,t95,t126,t198,t246] else [t65,t77,t84,t95,t126,t198,t252])) else (if i < 78 then (if i < 77 then [t65,t77,t84,t95,t126,t198,t254] else [t65,t77,t84,t95,t126,t198,t264]) else (if i < 79 then [t65,t77,t84,t95,t126,t204,t246] else [t65,t77,t84,t95,t126,t207,t246])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t65,t77,t84,t95,t126,t209,t246] else [t65,t77,t84,t95,t126,t216,t246]) else (if i < 83 then [t65,t77,t84,t95,t126,t225,t246] else [t65,t77,t84,t95,t136,t198,t246])) else (if i < 86 then (if i < 85 then [t65,t77,t84,t95,t139,t198,t246] else [t65,t77,t84,t95,t143,t198,t246]) else (if i < 87 then [t65,t77,t84,t95,t144,t198,t246] else [t65,t77,t84,t95,t152,t198,t246]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t65,t77,t84,t95,t156,t198,t246] else [t65,t77,t84,t95,t187,t198,t246]) else (if i < 91 then [t65,t77,t84,t95,t198,t246,t272] else [t65,t77,t84,t95,t198,t246,t316])) else (if i < 94 then (if i < 93 then [t65,t77,t84,t96,t126,t198,t246] else [t65,t77,t84,t97,t126,t198,t246]) else (if i < 95 then [t65,t77,t84,t106,t198,t246,t280] else [t65,t77,t84,t108,t126,t198,t280]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t65,t77,t84,t110,t120,t187,t280] else [t65,t77,t84,t110,t136,t198,t280]) else (if i < 99 then [t65,t77,t84,t110,t139,t198,t280] else [t65,t77,t84,t110,t144,t198,t280])) else (if i < 102 then (if i < 101 then [t65,t77,t84,t110,t152,t198,t280] else [t65,t77,t84,t110,t156,t198,t280]) else (if i < 103 then [t65,t77,t84,t110,t187,t198,t280] else [t65,t77,t84,t110,t198,t272,t280]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t65,t77,t84,t110,t198,t280,t316] else [t65,t77,t84,t113,t126,t246,t280]) else (if i < 107 then [t65,t77,t84,t114,t126,t246,t280] else [t65,t77,t84,t119,t126,t246,t280])) else (if i < 110 then (if i < 109 then [t65,t77,t84,t120,t126,t246,t280] else [t65,t77,t84,t120,t126,t246,t289]) else (if i < 111 then [t65,t77,t84,t120,t126,t246,t291] else [t65,t77,t84,t120,t126,t246,t294])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t65,t77,t84,t120,t136,t246,t280] else [t65,t77,t84,t120,t139,t246,t280]) else (if i < 115 then [t65,t77,t84,t120,t144,t246,t280] else [t65,t77,t84,t120,t152,t246,t280])) else (if i < 118 then (if i < 117 then [t65,t77,t84,t120,t156,t246,t280] else [t65,t77,t84,t120,t187,t246,t280]) else (if i < 119 then [t65,t77,t84,t120,t246,t272,t280] else [t65,t77,t84,t120,t246,t280,t316]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t65,t77,t84,t121,t126,t246,t280] else [t65,t77,t84,t122,t126,t246,t280]) else (if i < 123 then [t65,t77,t84,t123,t126,t246,t280] else [t65,t77,t84,t125,t126,t246,t280])) else (if i < 126 then (if i < 125 then [t65,t77,t84,t126,t170,t198,t280] else [t65,t77,t84,t126,t171,t198,t280]) else (if i < 127 then [t65,t77,t84,t126,t174,t198,t246] else [t65,t77,t84,t126,t192,t246,t280]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t65,t77,t84,t126,t192,t246,t294] else [t65,t77,t84,t126,t193,t246,t280]) else (if i < 131 then [t65,t77,t84,t126,t194,t246,t280] else [t65,t77,t84,t126,t195,t246,t280])) else (if i < 134 then (if i < 133 then [t65,t77,t84,t126,t196,t246,t280] else [t65,t77,t84,t126,t197,t246,t280]) else (if i < 135 then [t65,t77,t84,t126,t198,t245,t280] else [t65,t77,t84,t126,t198,t246,t280]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t65,t77,t84,t126,t198,t246,t281] else [t65,t77,t84,t126,t198,t246,t282]) else (if i < 139 then [t65,t77,t84,t126,t198,t246,t283] else [t65,t77,t84,t126,t198,t246,t284])) else (if i < 142 then (if i < 141 then [t65,t77,t84,t126,t198,t246,t285] else [t65,t77,t84,t126,t198,t246,t286]) else (if i < 143 then [t65,t77,t84,t126,t198,t246,t287] else [t65,t77,t84,t126,t198,t246,t288])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t65,t77,t84,t126,t198,t246,t289] else [t65,t77,t84,t126,t198,t246,t291]) else (if i < 147 then [t65,t77,t84,t126,t198,t246,t294] else [t65,t77,t84,t126,t198,t246,t295])) else (if i < 150 then (if i < 149 then [t65,t77,t84,t126,t198,t246,t298] else [t65,t77,t84,t126,t198,t246,t299]) else (if i < 151 then [t65,t77,t84,t126,t198,t252,t291] else [t65,t77,t84,t126,t198,t256,t302,t310]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t65,t77,t84,t126,t198,t264,t296] else [t65,t77,t84,t126,t199,t246,t280]) else (if i < 155 then [t65,t77,t84,t126,t200,t246,t280] else [t65,t77,t84,t126,t201,t246,t280])) else (if i < 158 then (if i < 157 then [t65,t77,t84,t126,t202,t246,t280] else [t65,t77,t84,t126,t203,t246,t280]) else (if i < 159 then [t65,t77,t84,t126,t204,t246,t280] else [t65,t77,t84,t126,t207,t246,t280]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t65,t77,t84,t126,t207,t246,t291] else [t65,t77,t84,t126,t208,t246,t280]) else (if i < 163 then [t65,t77,t84,t126,t209,t246,t280] else [t65,t77,t84,t126,t209,t246,t289])) else (if i < 166 then (if i < 165 then [t65,t77,t84,t126,t210,t246,t280] else [t65,t77,t84,t126,t216,t246,t280]) else (if i < 167 then [t65,t77,t84,t126,t218,t246,t280] else [t65,t77,t84,t126,t219,t264,t280]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t65,t77,t84,t126,t220,t246,t280] else [t65,t77,t84,t126,t233,t246,t280]) else (if i < 171 then [t65,t77,t84,t127,t198,t246,t280] else [t65,t77,t84,t128,t198,t246,t280])) else (if i < 174 then (if i < 173 then [t65,t77,t84,t129,t198,t246,t280] else [t65,t77,t84,t130,t198,t246,t280]) else (if i < 175 then [t65,t77,t84,t131,t198,t246,t280] else [t65,t77,t84,t132,t198,t246,t280])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t65,t77,t84,t133,t198,t246,t280] else [t65,t77,t84,t134,t198,t246,t280]) else (if i < 179 then [t65,t77,t84,t135,t198,t246,t280] else [t65,t77,t84,t136,t198,t246,t280])) else (if i < 182 then (if i < 181 then [t65,t77,t84,t137,t198,t246,t280] else [t65,t77,t84,t138,t198,t246,t280]) else (if i < 183 then [t65,t77,t84,t139,t198,t246,t280] else [t65,t77,t84,t139,t198,t254,t280]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t65,t77,t84,t139,t225,t246,t280] else [t65,t77,t84,t140,t198,t246,t280]) else (if i < 187 then [t65,t77,t84,t141,t198,t246,t280] else [t65,t77,t84,t142,t198,t246,t280])) else (if i < 190 then (if i < 189 then [t65,t77,t84,t143,t198,t246,t280] else [t65,t77,t84,t144,t198,t246,t280]) else (if i < 191 then [t65,t77,t84,t144,t198,t246,t291] else [t65,t77,t84,t144,t198,t252,t280])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t65,t77,t84,t144,t207,t246,t280] else [t65,t77,t84,t145,t198,t246,t280]) else (if i < 195 then [t65,t77,t84,t146,t198,t246,t280] else [t65,t77,t84,t147,t198,t246,t280])) else (if i < 198 then (if i < 197 then [t65,t77,t84,t148,t198,t246,t308] else [t65,t77,t84,t148,t198,t258,t280]) else (if i < 199 then [t65,t77,t84,t149,t198,t246,t280] else [t65,t77,t84,t150,t198,t246,t280]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t65,t77,t84,t151,t198,t246,t280] else [t65,t77,t84,t152,t198,t246,t280]) else (if i < 203 then [t65,t77,t84,t152,t198,t246,t289] else [t65,t77,t84,t152,t198,t259,t280])) else (if i < 206 then (if i < 205 then [t65,t77,t84,t152,t209,t246,t280] else [t65,t77,t84,t153,t198,t246,t280]) else (if i < 207 then [t65,t77,t84,t154,t198,t258,t280] else [t65,t77,t84,t155,t198,t246,t280])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t65,t77,t84,t156,t198,t246,t280] else [t65,t77,t84,t156,t198,t246,t297]) else (if i < 211 then [t65,t77,t84,t156,t217,t246,t280] else [t65,t77,t84,t157,t198,t246,t280])) else (if i < 214 then (if i < 213 then [t65,t77,t84,t158,t198,t246,t280] else [t65,t77,t84,t160,t198,t246,t280]) else (if i < 215 then [t65,t77,t84,t164,t246,t280,t316] else [t65,t77,t84,t178,t198,t246,t280]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t65,t77,t84,t180,t198,t246,t280] else [t65,t77,t84,t182,t198,t246,t280]) else (if i < 219 then [t65,t77,t84,t184,t198,t246,t280] else [t65,t77,t84,t185,t198,t246,t280])) else (if i < 222 then (if i < 221 then [t65,t77,t84,t186,t198,t246,t280] else [t65,t77,t84,t187,t192,t246,t280]) else (if i < 223 then [t65,t77,t84,t187,t193,t246,t280] else [t65,t77,t84,t187,t198,t246,t280]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t65,t77,t84,t187,t198,t246,t289] else [t65,t77,t84,t187,t198,t246,t291]) else (if i < 227 then [t65,t77,t84,t187,t198,t246,t294] else [t65,t77,t84,t187,t198,t246,t297])) else (if i < 230 then (if i < 229 then [t65,t77,t84,t187,t198,t246,t308] else [t65,t77,t84,t187,t198,t252,t280]) else (if i < 231 then [t65,t77,t84,t187,t198,t254,t280] else [t65,t77,t84,t187,t198,t258,t280]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t65,t77,t84,t187,t198,t264,t280] else [t65,t77,t84,t187,t198,t270,t280]) else (if i < 235 then [t65,t77,t84,t187,t204,t246,t280] else [t65,t77,t84,t187,t207,t246,t280])) else (if i < 238 then (if i < 237 then [t65,t77,t84,t187,t209,t246,t280] else [t65,t77,t84,t187,t215,t246,t280]) else (if i < 239 then [t65,t77,t84,t187,t217,t246,t280] else [t65,t77,t84,t187,t225,t246,t280])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t65,t77,t84,t187,t232,t246,t280] else [t65,t77,t84,t187,t246,t280,t293]) else (if i < 243 then [t65,t77,t84,t188,t198,t246,t280] else [t65,t77,t84,t189,t198,t246,t280])) else (if i < 246 then (if i < 245 then [t65,t77,t84,t190,t198,t246,t280] else [t65,t77,t84,t191,t198,t246,t280]) else (if i < 247 then [t65,t77,t84,t192,t246,t280,t317] else [t65,t77,t84,t198,t211,t246,t280]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t65,t77,t84,t198,t213,t246,t280] else [t65,t77,t84,t198,t221,t246,t280]) else (if i < 251 then [t65,t77,t84,t198,t223,t246,t280] else [t65,t77,t84,t198,t246,t271,t280])) else (if i < 254 then (if i < 253 then [t65,t77,t84,t198,t246,t272,t280] else [t65,t77,t84,t198,t246,t272,t294]) else (if i < 255 then [t65,t77,t84,t198,t246,t273,t280] else [t65,t77,t84,t198,t246,t274,t280])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t65,t77,t84,t198,t246,t275,t280] else [t65,t77,t84,t198,t246,t280,t315]) else (if i < 259 then [t65,t77,t84,t198,t246,t280,t316] else [t65,t77,t84,t198,t246,t280,t317])) else (if i < 262 then (if i < 261 then [t65,t77,t84,t198,t246,t280,t318] else [t65,t77,t84,t198,t246,t308,t319]) else (if i < 263 then [t65,t77,t84,t198,t258,t280,t319] else [t65,t77,t84,t198,t264,t280,t316]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t65,t77,t84,t219,t246,t280,t316] else [t65,t77,t84,t235,t246,t280,t316]) else (if i < 267 then [t65,t77,t84,t246,t277,t280,t293] else [t65,t77,t84,t246,t280,t293,t320])) else (if i < 270 then (if i < 269 then [t65,t77,t84,t246,t280,t296,t316] else [t65,t77,t85,t144,t198,t246,t280]) else (if i < 271 then [t65,t77,t85,t187,t198,t246,t280] else [t65,t77,t86,t187,t198,t246,t280])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t65,t77,t87,t187,t198,t246,t280] else [t65,t77,t91,t156,t198,t246,t280]) else (if i < 275 then [t65,t77,t91,t187,t198,t246,t280] else [t65,t77,t95,t187,t198,t246,t301])) else (if i < 278 then (if i < 277 then [t65,t77,t100,t187,t198,t246,t280] else [t65,t77,t118,t187,t198,t246,t280]) else (if i < 279 then [t65,t77,t118,t198,t246,t277,t280] else [t65,t77,t120,t187,t246,t280,t301]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t65,t77,t173,t187,t198,t246,t280] else [t65,t77,t173,t198,t246,t272,t280]) else (if i < 283 then [t65,t77,t187,t198,t229,t246,t280] else [t65,t77,t187,t198,t230,t246,t280])) else (if i < 286 then (if i < 285 then [t65,t77,t187,t198,t246,t280,t301] else [t65,t79,t84,t152,t198,t246,t280]) else (if i < 287 then [t65,t79,t84,t187,t198,t246,t280] else [t65,t79,t126,t198,t246,t280,t301]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t65,t79,t126,t198,t246,t280,t310] else [t65,t81,t84,t187,t198,t246,t280]) else (if i < 291 then [t65,t81,t91,t126,t198,t246,t280] else [t65,t81,t126,t198,t246,t280,t301])) else (if i < 294 then (if i < 293 then [t65,t84,t95,t187,t198,t246,t306] else [t65,t84,t99,t187,t198,t246,t280]) else (if i < 295 then [t65,t84,t109,t187,t198,t246,t280] else [t65,t84,t109,t198,t246,t277,t280]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t65,t84,t110,t187,t198,t280,t306] else [t65,t84,t112,t187,t198,t246,t280]) else (if i < 299 then [t65,t84,t112,t198,t246,t277,t280] else [t65,t84,t112,t198,t246,t280,t320])) else (if i < 302 then (if i < 301 then [t65,t84,t120,t187,t246,t280,t306] else [t65,t84,t172,t187,t198,t246,t280]) else (if i < 303 then [t65,t84,t172,t198,t246,t272,t280] else [t65,t84,t187,t198,t222,t246,t280])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t65,t84,t187,t198,t246,t280,t306] else [t65,t84,t198,t222,t246,t280,t316]) else (if i < 307 then [t65,t85,t126,t148,t198,t246,t280] else [t65,t85,t126,t198,t246,t280,t306])) else (if i < 310 then (if i < 309 then [t65,t86,t126,t198,t246,t280,t306] else [t65,t91,t126,t198,t246,t280,t306]) else (if i < 311 then [t65,t95,t126,t198,t246,t301,t306] else [t65,t120,t126,t246,t280,t301,t306]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t65,t126,t172,t173,t198,t246,t280] else [t65,t126,t172,t198,t246,t280,t301]) else (if i < 315 then [t65,t126,t173,t198,t246,t280,t306] else [t65,t126,t198,t246,t280,t301,t306])) else (if i < 318 then (if i < 317 then [t65,t187,t198,t246,t280,t301,t306] else [t1,t65,t77,t84,t95,t126,t198,t246]) else (if i < 319 then [t1,t65,t77,t84,t120,t126,t246,t280] else [t1,t65,t77,t84,t126,t198,t246,t280])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t1,t65,t77,t84,t187,t198,t246,t280] else [t2,t65,t77,t84,t126,t198,t246,t280]) else (if i < 323 then [t3,t65,t77,t84,t126,t198,t246,t280] else [t4,t65,t77,t84,t126,t198,t246,t280])) else (if i < 326 then (if i < 325 then [t5,t65,t77,t84,t126,t198,t246,t280] else [t6,t65,t77,t84,t126,t198,t246,t280]) else (if i < 327 then [t7,t65,t77,t84,t126,t198,t246,t280] else [t8,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t9,t65,t77,t84,t126,t198,t246,t280] else [t10,t65,t77,t84,t126,t198,t246,t280]) else (if i < 331 then [t11,t65,t77,t84,t126,t198,t246,t280] else [t12,t65,t77,t84,t95,t126,t198,t246])) else (if i < 334 then (if i < 333 then [t12,t65,t77,t84,t110,t126,t198,t280] else [t12,t65,t77,t84,t120,t126,t246,t280]) else (if i < 335 then [t12,t65,t77,t84,t126,t198,t246,t280] else [t12,t65,t77,t84,t126,t198,t256,t280])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t12,t65,t77,t84,t136,t198,t246,t280] else [t12,t65,t77,t84,t187,t198,t246,t280]) else (if i < 339 then [t12,t65,t77,t126,t198,t246,t280,t301] else [t12,t65,t84,t126,t198,t246,t256,t280])) else (if i < 342 then (if i < 341 then [t12,t65,t84,t126,t198,t246,t280,t306] else [t12,t77,t84,t126,t198,t246,t280,t312]) else (if i < 343 then [t13,t65,t77,t84,t95,t126,t198,t246] else [t13,t65,t77,t84,t120,t126,t246,t280]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t13,t65,t77,t84,t126,t198,t246,t280] else [t13,t65,t77,t84,t126,t204,t246,t280]) else (if i < 347 then [t13,t65,t77,t84,t187,t198,t246,t280] else [t13,t65,t77,t103,t126,t198,t246,t280])) else (if i < 350 then (if i < 349 then [t13,t65,t77,t126,t198,t246,t280,t301] else [t14,t65,t77,t84,t126,t198,t246,t280]) else (if i < 351 then [t15,t65,t77,t84,t95,t126,t198,t246] else [t15,t65,t77,t84,t110,t126,t198,t280]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t15,t65,t77,t84,t120,t126,t246,t280] else [t15,t65,t77,t84,t126,t198,t246,t280]) else (if i < 355 then [t15,t65,t77,t84,t187,t198,t246,t280] else [t15,t65,t77,t94,t126,t198,t246,t280])) else (if i < 358 then (if i < 357 then [t15,t65,t77,t126,t198,t246,t280,t301] else [t16,t65,t77,t84,t126,t198,t246,t280]) else (if i < 359 then [t17,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t95,t126,t198,t246]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t18,t65,t77,t84,t110,t126,t198,t280] else [t18,t65,t77,t84,t120,t126,t246,t280]) else (if i < 363 then [t18,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t126,t227,t246,t280])) else (if i < 366 then (if i < 365 then [t18,t65,t77,t84,t187,t198,t246,t280] else [t18,t65,t77,t126,t198,t246,t280,t301]) else (if i < 367 then [t18,t65,t84,t126,t198,t227,t246,t280] else [t18,t65,t84,t126,t198,t246,t280,t306])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t18,t77,t84,t126,t198,t246,t280,t312] else [t19,t65,t77,t84,t126,t198,t246,t280]) else (if i < 371 then [t20,t65,t77,t84,t126,t198,t246,t280] else [t21,t65,t77,t84,t126,t198,t246,t280])) else (if i < 374 then (if i < 373 then [t22,t65,t77,t84,t126,t198,t246,t280] else [t23,t65,t77,t84,t126,t198,t246,t280]) else (if i < 375 then [t23,t65,t77,t84,t187,t198,t246,t280] else [t24,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 380 then (if i < 378 then (if i < 377 then [t25,t65,t77,t84,t126,t198,t246,t280] else [t26,t65,t77,t84,t126,t198,t246,t280]) else (if i < 379 then [t27,t49,t77,t84,t126,t198,t246,t280] else [t27,t65,t77,t84,t95,t126,t198,t246])) else (if i < 382 then (if i < 381 then [t27,t65,t77,t84,t120,t126,t246,t280] else [t27,t65,t77,t84,t126,t198,t246,t280]) else (if i < 383 then [t27,t65,t77,t84,t126,t198,t246,t291] else [t27,t65,t77,t84,t126,t207,t246,t280]))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then [t27,t65,t77,t84,t144,t198,t246,t280] else [t27,t65,t77,t84,t187,t198,t246,t280]) else (if i < 387 then [t27,t65,t82,t84,t126,t198,t246,t280] else [t27,t65,t84,t126,t148,t198,t246,t280])) else (if i < 390 then (if i < 389 then [t27,t65,t84,t126,t198,t227,t246,t280] else [t27,t65,t84,t126,t198,t246,t280,t306]) else (if i < 391 then [t28,t65,t77,t84,t95,t126,t198,t246] else [t28,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 396 then (if i < 394 then (if i < 393 then [t29,t65,t77,t84,t126,t198,t246,t280] else [t30,t65,t77,t84,t126,t198,t246,t280]) else (if i < 395 then [t31,t65,t77,t84,t126,t198,t246,t280] else [t32,t65,t77,t84,t126,t198,t246,t280])) else (if i < 398 then (if i < 397 then [t35,t65,t77,t84,t95,t126,t198,t246] else [t35,t65,t77,t84,t110,t126,t198,t280]) else (if i < 399 then [t35,t65,t77,t84,t120,t126,t246,t280] else [t35,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then [t35,t65,t77,t84,t126,t198,t246,t289] else [t35,t65,t77,t84,t126,t198,t259,t280]) else (if i < 403 then [t35,t65,t77,t84,t126,t209,t246,t280] else [t35,t65,t77,t84,t152,t198,t246,t280])) else (if i < 406 then (if i < 405 then [t35,t65,t77,t84,t187,t198,t246,t280] else [t35,t65,t77,t126,t198,t246,t259,t280]) else (if i < 407 then [t35,t65,t77,t126,t198,t246,t280,t301] else [t35,t65,t77,t126,t198,t246,t280,t310]))) else (if i < 412 then (if i < 410 then (if i < 409 then [t35,t65,t79,t84,t126,t198,t246,t280] else [t35,t65,t84,t126,t198,t246,t280,t306]) else (if i < 411 then [t35,t71,t77,t84,t126,t198,t246,t280] else [t35,t77,t84,t126,t198,t246,t280,t312])) else (if i < 414 then (if i < 413 then [t36,t65,t77,t84,t126,t198,t246,t280] else [t37,t65,t77,t84,t126,t198,t246,t280]) else (if i < 415 then [t38,t65,t77,t84,t126,t198,t246,t280] else [t39,t65,t77,t84,t126,t198,t246,t280]))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then [t40,t65,t77,t84,t126,t198,t246,t280] else [t40,t65,t77,t84,t187,t198,t246,t280]) else (if i < 419 then [t41,t65,t77,t84,t126,t198,t246,t280] else [t42,t65,t77,t84,t126,t198,t246,t280])) else (if i < 422 then (if i < 421 then [t43,t65,t77,t84,t126,t198,t246,t280] else [t43,t65,t77,t84,t187,t198,t246,t280]) else (if i < 423 then [t44,t65,t77,t84,t126,t198,t246,t280] else [t46,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 428 then (if i < 426 then (if i < 425 then [t47,t65,t77,t84,t95,t126,t198,t246] else [t47,t65,t77,t84,t126,t198,t246,t280]) else (if i < 427 then [t48,t65,t77,t84,t95,t126,t198,t246] else [t48,t65,t77,t84,t126,t198,t246,t280])) else (if i < 430 then (if i < 429 then [t50,t65,t77,t84,t126,t198,t246,t280] else [t51,t65,t77,t84,t120,t126,t246,t280]) else (if i < 431 then [t51,t65,t77,t84,t126,t198,t246,t280] else [t52,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then [t52,t77,t84,t126,t198,t246,t256,t280] else [t52,t77,t84,t126,t198,t246,t280]) else (if i < 435 then [t65,t65,t77,t84,t95,t126,t198,t246] else [t65,t65,t77,t84,t110,t126,t198,t280])) else (if i < 438 then (if i < 437 then [t65,t65,t77,t84,t120,t126,t246,t280] else [t65,t65,t77,t84,t126,t198,t246,t280]) else (if i < 439 then [t65,t65,t77,t84,t187,t198,t246,t280] else [t65,t65,t77,t126,t198,t246,t280,t301]))) else (if i < 444 then (if i < 442 then (if i < 441 then [t65,t65,t84,t126,t198,t246,t280,t306] else [t65,t66,t77,t84,t126,t198,t246,t280]) else (if i < 443 then [t65,t67,t77,t84,t126,t198,t246,t280] else [t65,t68,t77,t84,t126,t198,t246,t280])) else (if i < 446 then (if i < 445 then [t65,t69,t77,t84,t126,t198,t246,t280] else [t65,t70,t77,t84,t126,t198,t246,t280]) else (if i < 447 then [t65,t71,t77,t84,t126,t198,t246,t280] else [t65,t72,t77,t84,t126,t198,t246,t280])))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then [t65,t73,t77,t84,t95,t126,t198,t246] else [t65,t73,t77,t84,t126,t198,t246,t280]) else (if i < 451 then [t65,t74,t77,t84,t126,t198,t246,t280] else [t65,t76,t77,t84,t126,t198,t246,t280])) else (if i < 454 then (if i < 453 then [t65,t77,t78,t84,t126,t198,t246,t280] else [t65,t77,t79,t84,t126,t198,t246,t280]) else (if i < 455 then [t65,t77,t80,t84,t126,t198,t246,t280] else [t65,t77,t81,t84,t126,t198,t246,t280]))) else (if i < 460 then (if i < 458 then (if i < 457 then [t65,t77,t82,t84,t95,t126,t198,t246] else [t65,t77,t82,t84,t120,t126,t246,t280]) else (if i < 459 then [t65,t77,t82,t84,t126,t198,t246,t280] else [t65,t77,t82,t84,t187,t198,t246,t280])) else (if i < 462 then (if i < 461 then [t65,t77,t83,t84,t126,t198,t246,t280] else [t65,t77,t84,t85,t126,t198,t246,t280]) else (if i < 463 then [t65,t77,t84,t89,t126,t198,t246,t280] else [t65,t77,t84,t94,t95,t126,t198,t246])))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then [t65,t77,t84,t94,t110,t126,t198,t280] else [t65,t77,t84,t94,t120,t126,t246,t280]) else (if i < 467 then [t65,t77,t84,t94,t126,t198,t246,t280] else [t65,t77,t84,t94,t126,t198,t246,t280,t302])) else (if i < 470 then (if i < 469 then [t65,t77,t84,t94,t187,t198,t246,t280] else [t65,t77,t84,t95,t95,t126,t198,t246]) else (if i < 471 then [t65,t77,t84,t95,t98,t126,t198,t246] else [t65,t77,t84,t95,t103,t126,t198,t246]))) else (if i < 476 then (if i < 474 then (if i < 473 then [t65,t77,t84,t95,t105,t126,t198,t246] else [t65,t77,t84,t95,t110,t126,t198]) else (if i < 475 then [t65,t77,t84,t95,t110,t126,t198,t246] else [t65,t77,t84,t95,t120,t126,t198,t246])) else (if i < 478 then (if i < 477 then [t65,t77,t84,t95,t120,t126,t246] else [t65,t77,t84,t95,t120,t126,t246,t280]) else (if i < 479 then [t65,t77,t84,t95,t126,t164,t198,t246] else [t65,t77,t84,t95,t126,t175,t198,t246]))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then [t65,t77,t84,t95,t126,t187,t198,t246] else [t65,t77,t84,t95,t126,t198,t198,t246]) else (if i < 483 then [t65,t77,t84,t95,t126,t198,t219,t246] else [t65,t77,t84,t95,t126,t198,t227,t246])) else (if i < 486 then (if i < 485 then [t65,t77,t84,t95,t126,t198,t236,t246] else [t65,t77,t84,t95,t126,t198,t240,t246]) else (if i < 487 then [t65,t77,t84,t95,t126,t198,t246] else [t65,t77,t84,t95,t126,t198,t246,t246]))) else (if i < 492 then (if i < 490 then (if i < 489 then [t65,t77,t84,t95,t126,t198,t246,t253] else [t65,t77,t84,t95,t126,t198,t246,t256]) else (if i < 491 then [t65,t77,t84,t95,t126,t198,t246,t260] else [t65,t77,t84,t95,t126,t198,t246,t265])) else (if i < 494 then (if i < 493 then [t65,t77,t84,t95,t126,t198,t246,t280] else [t65,t77,t84,t95,t126,t198,t246,t292]) else (if i < 495 then [t65,t77,t84,t95,t126,t198,t246,t296] else [t65,t77,t84,t95,t126,t198,t246,t300])))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then [t65,t77,t84,t95,t126,t198,t246,t301] else [t65,t77,t84,t95,t126,t198,t246,t302]) else (if i < 499 then [t65,t77,t84,t95,t126,t198,t246,t321] else [t65,t77,t84,t95,t187,t198,t246])) else (if i < 502 then (if i < 501 then [t65,t77,t84,t95,t187,t198,t246,t280] else [t65,t77,t84,t98,t126,t198,t246,t280]) else (if i < 503 then [t65,t77,t84,t103,t120,t126,t246,t280] else [t65,t77,t84,t103,t126,t198,t246,t280]))) else (if i < 508 then (if i < 506 then (if i < 505 then [t65,t77,t84,t103,t126,t198,t246,t280,t302] else [t65,t77,t84,t103,t187,t198,t246,t280]) else (if i < 507 then [t65,t77,t84,t104,t126,t198,t246,t280] else [t65,t77,t84,t105,t126,t198,t246,t280])) else (if i < 510 then (if i < 509 then [t65,t77,t84,t107,t120,t126,t246,t280] else [t65,t77,t84,t107,t126,t198,t246,t280]) else (if i < 511 then [t65,t77,t84,t110,t187,t198,t246,t280] else [t65,t77,t84,t110,t187,t198,t280]))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then [t65,t77,t84,t111,t126,t198,t246,t280] else [t65,t77,t84,t120,t120,t126,t246,t280]) else (if i < 515 then [t65,t77,t84,t120,t124,t126,t246,t280] else [t65,t77,t84,t120,t126,t164,t246,t280])) else (if i < 518 then (if i < 517 then [t65,t77,t84,t120,t126,t187,t246,t280] else [t65,t77,t84,t120,t126,t198,t246,t280]) else (if i < 519 then [t65,t77,t84,t120,t126,t219,t246,t280] else [t65,t77,t84,t120,t126,t240,t246,t280]))) else (if i < 524 then (if i < 522 then (if i < 521 then [t65,t77,t84,t120,t126,t246,t246,t280] else [t65,t77,t84,t120,t126,t246,t253,t280]) else (if i < 523 then [t65,t77,t84,t120,t126,t246,t256,t280] else [t65,t77,t84,t120,t126,t246,t265,t280])) else (if i < 526 then (if i < 525 then [t65,t77,t84,t120,t126,t246,t278,t280] else [t65,t77,t84,t120,t126,t246,t280]) else (if i < 527 then [t65,t77,t84,t120,t126,t246,t280,t302] else [t65,t77,t84,t120,t126,t246,t280,t321])))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then [t65,t77,t84,t120,t187,t198,t246,t280] else [t65,t77,t84,t120,t187,t246,t280]) else (if i < 531 then [t65,t77,t84,t124,t126,t198,t246,t280] else [t65,t77,t84,t126,t161,t198,t246,t280])) else (if i < 534 then (if i < 533 then [t65,t77,t84,t126,t162,t198,t246,t280] else [t65,t77,t84,t126,t163,t198,t246,t280]) else (if i < 535 then [t65,t77,t84,t126,t164,t175,t246,t280] else [t65,t77,t84,t126,t164,t198,t246,t280]))) else (if i < 540 then (if i < 538 then (if i < 537 then [t65,t77,t84,t126,t164,t198,t246,t294] else [t65,t77,t84,t126,t164,t198,t265,t280]) else (if i < 539 then [t65,t77,t84,t126,t164,t227,t246,t280] else [t65,t77,t84,t126,t164,t246,t265,t280])) else (if i < 542 then (if i < 541 then [t65,t77,t84,t126,t165,t198,t246,t280] else [t65,t77,t84,t126,t166,t198,t246,t280]) else (if i < 543 then [t65,t77,t84,t126,t167,t198,t246,t280] else [t65,t77,t84,t126,t168,t198,t246,t280]))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then [t65,t77,t84,t126,t169,t198,t246,t280] else [t65,t77,t84,t126,t172,t198,t246,t280]) else (if i < 547 then [t65,t77,t84,t126,t176,t198,t246,t280] else [t65,t77,t84,t126,t177,t198,t246,t280])) else (if i < 550 then (if i < 549 then [t65,t77,t84,t126,t179,t198,t246,t280] else [t65,t77,t84,t126,t181,t198,t246,t280]) else (if i < 551 then [t65,t77,t84,t126,t183,t198,t246,t280] else [t65,t77,t84,t126,t187,t198,t246,t280]))) else (if i < 556 then (if i < 554 then (if i < 553 then [t65,t77,t84,t126,t192,t198,t246,t280] else [t65,t77,t84,t126,t192,t246,t280]) else (if i < 555 then [t65,t77,t84,t126,t192,t246,t280,t302] else [t65,t77,t84,t126,t198,t198,t246,t280])) else (if i < 558 then (if i < 557 then [t65,t77,t84,t126,t198,t204,t246,t280] else [t65,t77,t84,t126,t198,t205,t246,t280]) else (if i < 559 then [t65,t77,t84,t126,t198,t206,t246,t280] else [t65,t77,t84,t126,t198,t207,t246,t280])))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then [t65,t77,t84,t126,t198,t209,t246,t280] else [t65,t77,t84,t126,t198,t212,t246,t280]) else (if i < 563 then [t65,t77,t84,t126,t198,t214,t246,t280] else [t65,t77,t84,t126,t198,t219,t246,t280])) else (if i < 566 then (if i < 565 then [t65,t77,t84,t126,t198,t224,t246,t280] else [t65,t77,t84,t126,t198,t228,t246,t280]) else (if i < 567 then [t65,t77,t84,t126,t198,t231,t246,t280] else [t65,t77,t84,t126,t198,t236,t246,t280]))) else (if i < 572 then (if i < 570 then (if i < 569 then [t65,t77,t84,t126,t198,t237,t246,t280] else [t65,t77,t84,t126,t198,t238,t246,t280]) else (if i < 571 then [t65,t77,t84,t126,t198,t239,t246,t280] else [t65,t77,t84,t126,t198,t240,t246,t280])) else (if i < 574 then (if i < 573 then [t65,t77,t84,t126,t198,t240,t246,t302] else [t65,t77,t84,t126,t198,t241,t246,t280]) else (if i < 575 then [t65,t77,t84,t126,t198,t242,t246,t280] else [t65,t77,t84,t126,t198,t243,t246,t280])))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then [t65,t77,t84,t126,t198,t244,t246,t280] else [t65,t77,t84,t126,t198,t246,t246,t280]) else (if i < 579 then [t65,t77,t84,t126,t198,t246,t247,t280] else [t65,t77,t84,t126,t198,t246,t248,t280])) else (if i < 582 then (if i < 581 then [t65,t77,t84,t126,t198,t246,t249,t280] else [t65,t77,t84,t126,t198,t246,t250,t280]) else (if i < 583 then [t65,t77,t84,t126,t198,t246,t251,t280] else [t65,t77,t84,t126,t198,t246,t252,t280]))) else (if i < 588 then (if i < 586 then (if i < 585 then [t65,t77,t84,t126,t198,t246,t253,t280] else [t65,t77,t84,t126,t198,t246,t254,t280]) else (if i < 587 then [t65,t77,t84,t126,t198,t246,t255,t280] else [t65,t77,t84,t126,t198,t246,t256,t280])) else (if i < 590 then (if i < 589 then [t65,t77,t84,t126,t198,t246,t256,t280,t310] else [t65,t77,t84,t126,t198,t246,t257,t280]) else (if i < 591 then [t65,t77,t84,t126,t198,t246,t260,t280] else [t65,t77,t84,t126,t198,t246,t261,t280])))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then [t65,t77,t84,t126,t198,t246,t262,t280] else [t65,t77,t84,t126,t198,t246,t263,t280]) else (if i < 595 then [t65,t77,t84,t126,t198,t246,t264,t280] else [t65,t77,t84,t126,t198,t246,t265,t280])) else (if i < 598 then (if i < 597 then [t65,t77,t84,t126,t198,t246,t266,t280] else [t65,t77,t84,t126,t198,t246,t267,t280]) else (if i < 599 then [t65,t77,t84,t126,t198,t246,t268,t280] else [t65,t77,t84,t126,t198,t246,t269,t280]))) else (if i < 604 then (if i < 602 then (if i < 601 then [t65,t77,t84,t126,t198,t246,t278,t280] else [t65,t77,t84,t126,t198,t246,t279,t280]) else (if i < 603 then [t65,t77,t84,t126,t198,t246,t280] else [t65,t77,t84,t126,t198,t246,t280,t290])) else (if i < 606 then (if i < 605 then [t65,t77,t84,t126,t198,t246,t280,t302] else [t65,t77,t84,t126,t198,t246,t280,t303]) else (if i < 607 then [t65,t77,t84,t126,t198,t246,t280,t304] else [t65,t77,t84,t126,t198,t246,t280,t305]))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then [t65,t77,t84,t126,t198,t246,t280,t307] else [t65,t77,t84,t126,t198,t246,t280,t313]) else (if i < 611 then [t65,t77,t84,t126,t198,t246,t280,t314] else [t65,t77,t84,t126,t198,t246,t280,t321])) else (if i < 614 then (if i < 613 then [t65,t77,t84,t126,t198,t246,t289] else [t65,t77,t84,t126,t198,t246,t291]) else (if i < 615 then [t65,t77,t84,t126,t198,t246,t292,t300] else [t65,t77,t84,t126,t198,t246,t294]))) else (if i < 620 then (if i < 618 then (if i < 617 then [t65,t77,t84,t126,t198,t246,t296,t302] else [t65,t77,t84,t126,t198,t246,t300,t302]) else (if i < 619 then [t65,t77,t84,t126,t204,t246,t280] else [t65,t77,t84,t126,t207,t246,t280])) else (if i < 622 then (if i < 621 then [t65,t77,t84,t126,t209,t246,t280] else [t65,t77,t84,t126,t219,t227,t246,t280]) else (if i < 623 then [t65,t77,t84,t126,t219,t246,t265,t280] else [t65,t77,t84,t126,t219,t246,t280,t319])))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then [t65,t77,t84,t136,t198,t246,t280] else [t65,t77,t84,t139,t198,t246,t280]) else (if i < 627 then [t65,t77,t84,t144,t198,t246,t280] else [t65,t77,t84,t148,t159,t198,t246,t280])) else (if i < 630 then (if i < 629 then [t65,t77,t84,t148,t187,t198,t246,t280] else [t65,t77,t84,t148,t198,t246,t277,t280]) else (if i < 631 then [t65,t77,t84,t148,t198,t246,t280,t320] else [t65,t77,t84,t152,t198,t246,t280]))) else (if i < 636 then (if i < 634 then (if i < 633 then [t65,t77,t84,t154,t187,t198,t246,t280] else [t65,t77,t84,t154,t198,t246,t277,t280]) else (if i < 635 then [t65,t77,t84,t156,t198,t246,t280] else [t65,t77,t84,t159,t187,t198,t246,t280])) else (if i < 638 then (if i < 637 then [t65,t77,t84,t159,t198,t246,t277,t280] else [t65,t77,t84,t163,t187,t198,t246,t280]) else (if i < 639 then [t65,t77,t84,t164,t187,t198,t246,t280] else [t65,t77,t84,t164,t198,t246,t272,t280]))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then [t65,t77,t84,t175,t187,t198,t246,t280] else [t65,t77,t84,t175,t198,t246,t280,t316]) else (if i < 643 then [t65,t77,t84,t176,t187,t198,t246,t280] else [t65,t77,t84,t181,t187,t198,t246,t280])) else (if i < 646 then (if i < 645 then [t65,t77,t84,t187,t187,t198,t246,t280] else [t65,t77,t84,t187,t198,t198,t246,t280]) else (if i < 647 then [t65,t77,t84,t187,t198,t212,t246,t280] else [t65,t77,t84,t187,t198,t214,t246,t280]))) else (if i < 652 then (if i < 650 then (if i < 649 then [t65,t77,t84,t187,t198,t219,t246,t280] else [t65,t77,t84,t187,t198,t224,t246,t280]) else (if i < 651 then [t65,t77,t84,t187,t198,t227,t246,t280] else [t65,t77,t84,t187,t198,t231,t246,t280])) else (if i < 654 then (if i < 653 then [t65,t77,t84,t187,t198,t235,t246,t280] else [t65,t77,t84,t187,t198,t240,t246,t280]) else (if i < 655 then [t65,t77,t84,t187,t198,t246,t246,t280] else [t65,t77,t84,t187,t198,t246,t253,t280])))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then [t65,t77,t84,t187,t198,t246,t256,t280] else [t65,t77,t84,t187,t198,t246,t259,t280]) else (if i < 659 then [t65,t77,t84,t187,t198,t246,t265,t280] else [t65,t77,t84,t187,t198,t246,t266,t280])) else (if i < 662 then (if i < 661 then [t65,t77,t84,t187,t198,t246,t277,t280] else [t65,t77,t84,t187,t198,t246,t280]) else (if i < 663 then [t65,t77,t84,t187,t198,t246,t280,t280] else [t65,t77,t84,t187,t198,t246,t280,t290]))) else (if i < 668 then (if i < 666 then (if i < 665 then [t65,t77,t84,t187,t198,t246,t280,t292] else [t65,t77,t84,t187,t198,t246,t280,t296]) else (if i < 667 then [t65,t77,t84,t187,t198,t246,t280,t300] else [t65,t77,t84,t187,t198,t246,t280,t301])) else (if i < 670 then (if i < 669 then [t65,t77,t84,t187,t198,t246,t280,t302] else [t65,t77,t84,t187,t198,t246,t280,t306]) else (if i < 671 then [t65,t77,t84,t187,t198,t246,t280,t310] else [t65,t77,t84,t187,t198,t246,t280,t312]))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then [t65,t77,t84,t187,t198,t246,t280,t319] else [t65,t77,t84,t187,t198,t246,t280,t320]) else (if i < 675 then [t65,t77,t84,t187,t198,t246,t280,t321] else [t65,t77,t84,t198,t246,t272,t280])) else (if i < 678 then (if i < 677 then [t65,t77,t84,t198,t246,t277,t280,t319] else [t65,t77,t84,t198,t246,t280,t316]) else (if i < 679 then [t65,t77,t84,t198,t246,t280,t319,t320] else [t65,t77,t187,t198,t246,t280,t301]))) else (if i < 684 then (if i < 682 then (if i < 681 then [t65,t84,t187,t198,t246,t280,t306] else [t65,t126,t198,t246,t280,t301,t306]) else (if i < 683 then [t12,t65,t77,t84,t126,t198,t246,t280] else [t13,t65,t77,t84,t126,t198,t246,t280])) else (if i < 686 then (if i < 685 then [t15,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t126,t198,t246,t280]) else (if i < 687 then [t27,t65,t77,t84,t126,t198,t246,t280] else [t35,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then [t65,t65,t77,t84,t126,t198,t246,t280] else [t65,t77,t82,t84,t126,t198,t246,t280]) else (if i < 691 then [t65,t77,t84,t94,t126,t198,t246,t280] else [t65,t77,t84,t95,t126,t198,t246])) else (if i < 694 then (if i < 693 then [t65,t77,t84,t95,t126,t198,t246,t280] else [t65,t77,t84,t103,t126,t198,t246,t280]) else (if i < 695 then [t65,t77,t84,t120,t126,t198,t246,t280] else [t65,t77,t84,t120,t126,t246,t280]))) else (if i < 700 then (if i < 698 then (if i < 697 then [t65,t77,t84,t126,t164,t198,t246,t280] else [t65,t77,t84,t126,t187,t198,t246,t280]) else (if i < 699 then [t65,t77,t84,t126,t198,t198,t246,t280] else [t65,t77,t84,t126,t198,t219,t246,t280])) else (if i < 702 then (if i < 701 then [t65,t77,t84,t126,t198,t240,t246,t280] else [t65,t77,t84,t126,t198,t246,t246,t280]) else (if i < 703 then [t65,t77,t84,t126,t198,t246,t253,t280] else [t65,t77,t84,t126,t198,t246,t256,t280])))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then [t65,t77,t84,t126,t198,t246,t265,t280] else [t65,t77,t84,t126,t198,t246,t280]) else (if i < 707 then [t65,t77,t84,t126,t198,t246,t280,t302] else [t65,t77,t84,t187,t198,t246,t280])) else (if i < 710 then (if i < 709 then [t65,t77,t84,t126,t198,t246,t280] else []) else [])) else []) else []) else []))) else []))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x334dd35dbb6fdce370dd369c26b5c733cc1371b871dc5334dd35dcc6c1ce374c7379ae735cc374df2c99a6e1cc374df379ae735cc324cf369c26b5c9304dd35db66c1ce370c935d2e6d99331cc934db96d9c8164e127dae6fdbd31cdd361b25a1ce37cdd2c9b86b9cc34ccd35db06d9ce334d335db66c1ce334dd35dc46c1ce33cc1371b86e5c537cdd2c9b8669cc334e535db66c1ce31cc936dc6711c833cdd35db66c1ce334dd369b86a5ce334dd35dbb6c1ce31cdd35db66c1ce304dd369b86a5ce334dd35db66fdce31cdd379cd6b9cc37cdd379cd6b9cc374cd35db06d9ce33459371c6735cb334dd35db66c1ce else 0x31cdd369b86a5ce324dd369b86a5ce32459371c6735cb33459371c6739cb33459371bd735cb31cdc379cd6b9cc37cdc379cd6b9cc334dc35db66c1ce37cdc2c9b8669cc334dc369b86a5ce374c735db06d9ce374cf35db06d9ce384d831d68669bd374cd35db0711ce374cd35db06edce33cc934dc66d9c8324dd35db66c1ce33cc9371b86e5c531cdd379ce6b9cc31cc936dbd711c837cdd379ce6b9cc3845927dbf6b9bd34cd835d2e6d972334dd35db672dce37cdd379cd721cc334d3371c6735cb334dd35dc46fdce2d4dd35db66fdce334d335db66fdce334e535db63d1ce2d4c1371b86e5c5374cd35dbf6d9ce) else (if i < 96 then 0x334e535dc46c1ce334dd37dbb6c1ce334e5369b86a5ce31cc934dc66d9c831cc934dbd6d9c831cc9375c66edc8294c9375c96edc831cc9375b96edc8364dd379cd6b9cc304d335db66c1ce334dd35da76c1ce374cd361a96e1ce334d8371c6735cb33cdd35db66a5ce164cd371cd719cb334dd361b86a5ce374cd35da96d9ce33cdd379cd669cc37cdd379b86b9cc33cde36dc6711c83845931dbf6b9bd3845933db0669bd37cdd379b8669cc334dd35db66a5ce304e5361b86a5ce334e5361c46fdce304d8371c6735cb364e5379b8669cc304e535dc46fdce334dd35db6689ce364dd2c9b8669cc334dd35db63d1ce else 0x374c7369a9711ce31ca5371c6735cb33cc7371b86e5c5374c7369a96e1ce334dd35db64f9ce334dd35db26c1ce34cd835d2e6d9b8324d831d68669bd370c92d5c26c193374cf35db06edce324dd35dbb6c1ce334d3369b86a5ce374d835d2e6edb833cdd35dbb6c1ce31ce535dc46fdce384d833dbf6b9bd364e52c9b8669cc304e535dc472dce304db35dc46fdce304e535dcc6fdce31ce5379cd6b9cc364e5379cd6b9cc304dc369b86a5ce304e5369b86a5ce364e5379ca669cc394c135dbf711ce334e535dc46fdce304dd35dc46fdce374c135dbf6d9ce304e535db66fdce33cdd35dc46fdce33ce535dc46c1ce)) else (if i < 192 then (if i < 160 then 0x3845933dbf6e5bd334dc35db66fdce374cf35db0719ce374c735db0719ce394cf35db0711ce374d92c99a6e1cc364dd379b8669cc31cdd379cd721cc334d8371c6739cb334dc369b872dce294dd325b8669cc37cdd379ca669cc374cd35dbf6edce334dc361b25a1ce324c736dcc719c8374d835d2e6ed72370c937dbc6ed93374cf35db0711ce294c7371cd719cb33cdd369b86a5ce370c933dc26b19331cd3369b86a5ce31ce5369b86a5ce31cdd369b872dce31cd3371c6735cb31cdd369726a5ce31cdd361b85a1ce374cd369a96e1ce334dd369b85a1ce374cd37db06edce374c1369a96e1ce394cd35db06d9ce else 0x360e5379cd6b9cc360c1371cd6f5cb360c1371c9719cb360c1371cd719cb364e5379c76b9cc394c1361a96e1ce374d9371b8725c5364dd325b8669cc394c9369bf711ce374cd369bf6e1ce368cd371cd719cb374cd361b0711ce334dd361bb6fdce334d3371c66b9cb334dd369726a5ce370c92d5c26b193334dd369b872dce33cc1371b8725c537cc1371b86e5c5374cd35d3e6d9ce37cdd325b8669cc34ccd35d3e6d9ce31cdd325cd669cc31cdd379ca669cc370cd35d2e6d9ce364dd325b86b9cc370dd369c26a5c7324cf31da2669c937cdd379ca6b9cc374cd35dbc6d9ce304dd361c45a1ce37cdd325b86b9cc) else (if i < 224 then 0x324c7375bb6e5c831ca5371c6721cb324dc35db66c1ce370dd369766f5c7360dd325cd6b9cc334dd35db64b9ce294dd379cd6b9cc370dd369766b5c7294c936dc6711c8334dd35db66f1ce374c136168711ce31cdd379cd6f5cc364dd379cd6f5cc374cd35da96e1ce34cd835d2e6d9c6374c735db0711ce374c737db06edce374d935d2e6d9b836ccf35db0711ce31cdb35dc46fdce374d937dbc6edb834cd835d2e6b9bd36ccf35db06b9ce33cdd35dae6c1c9324dd369726a5ce374c1361a96e1ce364d3379b8669cc394cf361a9711ce394c1369bf6e1ce33ce5379cd669cc364e5379b86b9cc384da33dbf6b9bd else 0x374cd361bf711ce374cd361bf6edce370c935d2e6d9ce370c937dbc6edce374d937dbc6edce374c135d2e6d9ce374c137dbc6edce370c937dc26ed9337cd9371b86e5c5370dd369bc6f5c7364dd325b8669ce374d835d2e6e5b836ccf35db06f5ce394cd361bf711ce370cd35dbc6d9ce304dd35db64b9ce370c137dbc6edce370c135d2e6d9ce294dd325b8669ce31cdc325b8669ce370c937dbc6b193294dc36dc6711c8294dc36dc672dc8374c1371b8725c5370c935d2e6ed93370c937dbc6c19337cd8371b86e5c5370dd369bc669c733459371c6729cb324df369c26b5c7364dd379cd721cc)))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x101 else 0x101) else (if i < 7 then 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07 else 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x63c1e5079c000000000000504 else 0x1fc07f01fc07f01fc07f05000000000705) else (if i < 11 then 0x7a400007641d907641d907641d907641cf0005000000040a06 else 0x7a400007641d907641d907641d907641cf0005000000040a06)) else (if i < 14 then (if i < 13 then 0x5c400004ac12b04ac12b04ac12b04ac1cf0005000000040a06 else 0x5c4171000017105c417105c417105c417105c4171020700090105010c07) else (if i < 15 then 0x171000000004ac12b073c12b04ac12b04ac12b050504000000000b07 else 0x1fc07f01fc07f01fc07f05000000000705)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x1fc07f01fc07f01fc07f05000000000705 else 0x1ef0000043073c04307b404307ac043010c043060000000403020b07) else (if i < 19 then 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07 else 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07)) else (if i < 22 then (if i < 21 then 0x7dc1f700001f907e41f707e41f907e41f9040403000000000b07 else 0x4302bc0af02bc0af02bc0af05c40af0000000400040a06) else (if i < 23 then 0x10400007f404107ec041078c04101040410009060301000a06 else 0x3fc0ff03fc0ff03fc0ff05000000000705))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x3e40f903e40f903e40f905000000000705 else 0x1001408d000400100041690004001059c001000400100040010004001000402a0607050008000205050303140b) else (if i < 27 then 0x1001408d000400100041690004001059c00100040010004001000400100040620607050008000205050303140b else 0xa902a40a9028c05a05bc16b02a40a902a413f01780a902a40a905b40a902a40a902a40a902a40a9120015030c090005040402000400041a0f)) else (if i < 30 then (if i < 29 then 0x100040010004001000400101050000000805 else 0x1000101) else (if i < 31 then 0x100040010004001000400101050000000805 else 0x17105c417105c417105c417105cc17100e017105c417105c400605c417105c417105c400e05c417105c41711209001600010e05070308010a001a0e))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0xaf02bc17102bc0af00740af02bc0af010c0af00b00af02bc0af02bc06402bc0af02bc0af0600000e0a0d03010002000402170d else 0x13000101) else (if i < 35 then 0x87000101 else 0x87000101)) else (if i < 38 then (if i < 37 then 0x87000101 else 0x87000000000000870224175021c087021c0870234087021c087021c087021c087000105090000010300000700130c) else (if i < 39 then 0x21c08705dc07a021c175033408d021c087021c087021c087021c0460224036021c08701d8087021c087021c087150c0107100b0011100603000b0c021b0f else 0x8d0098087021c0870334087021c087021c1750224087021c08701b8087021c087021c087060a020c03000c000003000102170d))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x21c087009808d00d8179021c087033408705d40870224087021c087021c087021c087021c0870714040001010b000602000100170d else 0x87000008d01e800005ec087021c087021c087021c1750224087021c0870210087021c087021c087100e0601030007000003000102170d) else (if i < 43 then 0x87000101 else 0x21c0d505d408405f408701d808d0334087021c06e0224087021c087021c087021c087021c087021c087100e0c1100080402000100010300190e)) else (if i < 46 then (if i < 45 then 0x87000101 else 0x21c000021c087011808705d4087021c0870224087021c087021c08705e4087021c08d0900041000010e07060606140b) else (if i < 47 then 0x9906140890000181060c08902240890224089022408905fc089022408902240890224089000104090003000300000000150c else 0x17505d417505d417505d417505d418105d4000061c17505bc17505d416b062417505d41750001001300000c0f00000400150c)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x87000101 else 0xbf000101) else (if i < 51 then 0xbf00000cb02fc0bf02fc0bf02fc0bf0003000700000906 else 0x4b000101)) else (if i < 54 then (if i < 53 then 0x12c0a9012c04b012c04b012c04b0205000000000906 else 0x1f007c01f007c01f007c01f01050000000805) else (if i < 55 then 0x32c0cb032c0cb00000cb032c0cb032c0cb0007000000000a06 else 0x18b02b40ad02b40ad02b40ad02b40ad0001010400000a06))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x1100440110044011004401101050000000805 else 0xc500000c503140c503140c503140c50003000700000906) else (if i < 59 then 0xb002c00b002c00b002c00b01050000000805 else 0xc903240c906340c9032413303240c903240c9070500020101010c07)) else (if i < 62 then (if i < 61 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 63 then 0x100040010004001000400101050000000805 else 0xe700400000000000064c195064418f000000000100000907)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x7000101 else 0x1000101) else (if i < 67 then 0x1000101 else 0x1b000101)) else (if i < 70 then (if i < 69 then 0x101 else 0x101) else (if i < 71 then 0x101 else 0x101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x101 else 0x7f000101) else (if i < 75 then 0x1000101 else 0x1000101)) else (if i < 78 then (if i < 77 then 0x1000101 else 0x13000101) else (if i < 79 then 0x1000101 else 0x1000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x1000101 else 0xb000101) else (if i < 83 then 0x1000101 else 0x1000101)) else (if i < 86 then (if i < 85 then 0x1000101 else 0x1000101) else (if i < 87 then 0x1000101 else 0x1000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x1000101 else 0x101) else (if i < 91 then 0x1000101 else 0x13000101)) else (if i < 94 then (if i < 93 then 0x1000101 else 0x1000101) else (if i < 95 then 0x1000101 else 0x100040010004001000400101050000000805))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x101 else 0x1000101) else (if i < 99 then 0x1000101 else 0x1000101)) else (if i < 102 then (if i < 101 then 0x1000101 else 0x1000101) else (if i < 103 then 0x101 else 0x1000101))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x13000101 else 0xf000101) else (if i < 107 then 0x1000101 else 0xb000101)) else (if i < 110 then (if i < 109 then 0x1000101 else 0x1000101) else (if i < 111 then 0x1000101 else 0x1000101)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x1000101 else 0x1000101) else (if i < 115 then 0x1000101 else 0x1000101)) else (if i < 118 then (if i < 117 then 0x1000101 else 0x101) else (if i < 119 then 0x1000101 else 0x13000101))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x1000101 else 0xb000101) else (if i < 123 then 0x1000101 else 0x7f000101)) else (if i < 126 then (if i < 125 then 0xf066c00f003c00f039c05f01ac00f000006b065c19d01ac199003c00f003c00f003c18f0000001100001104000d0101150c else 0x100040010004001000400101050000000805) else (if i < 127 then 0x1000101 else 0x7f01fc07f01fc0f901fc07f01fc0f901fc07f03e407f0a0a070005050107000f09))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x7f03e40f900680fb01fc0f9006000001fc07f01fc07f01fc07f01fc07f01fc07f0f11050001000300040600130b else 0x3c19f003c00f003c00f003c00f0005000000000906) else (if i < 131 then 0x100040010004001000400101050000000805 else 0x3c1a1003c00f003c00f003c00f0005030000000906)) else (if i < 134 then (if i < 133 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 135 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 139 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 142 then (if i < 141 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 143 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x100040010004001000400101050000000805 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 147 then 0x3ec07f000400100040010004001000400100000104000200000c08 else 0x10004001000400000000fb01fc001000400100040010000000a000000000d08)) else (if i < 150 then (if i < 149 then 0x100040010004001000400101050000000805 else 0x4065027c001024c0c9031c03f000400100040010004001021c001020f000b010401020500110a) else (if i < 151 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x1a3000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x101 else 0x100040010004001000400101050000000805) else (if i < 155 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 158 then (if i < 157 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 159 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x6500040000004000000403f0004001024c087000400100041a50906090003000000060f09 else 0x100040010004001000400101050000000805) else (if i < 163 then 0x69c0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06)) else (if i < 166 then (if i < 165 then 0x6a40b100040000004001000400100040010005000000000a06 else 0xb002c00b002c00b002c00b01050000000805) else (if i < 167 then 0x137000400100040870004005000400100040c50900060007040100020e09 else 0x130000013004c0a3004c01301fc013004c0130424013004c0130c00090009010301000f09))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x1a7004000000000e704dc087003c0010004001000400100040010002040005030000010f09 else 0xf003c00f003c00f003c00f01050000000805) else (if i < 171 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 174 then (if i < 173 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 175 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 179 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 182 then (if i < 181 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 183 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06) else (if i < 187 then 0x1f007c01f007c01f007c01f01050000000805 else 0x100040010004001000400101050000000805)) else (if i < 190 then (if i < 189 then 0x100040010004001000400101050000000805 else 0x403f0004001000400100040010005000003000906) else (if i < 191 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x403f0004001000400100040010005000003000906 else 0x403f0004001000400100040010005000003000906) else (if i < 195 then 0x40050004001000400100040010005040000000906 else 0x400000041ab000400100041ad00fc005000400100040010004000700000a000e08)) else (if i < 198 then (if i < 197 then 0x1b7001c00702bc14706c41b10000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c else 0x1b7001c00702bc14706e41b90000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c) else (if i < 199 then 0x2f00bc02f00bc02f00bc02f01050000000805 else 0x1100440110044011004401101050000000805))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x100040010004001000400101050000000805 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 203 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x101)) else (if i < 206 then (if i < 205 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 207 then 0x101 else 0x100040010004001000400101050000000805)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x41370004001000400100040010005000006000906 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 211 then 0x104dc00100040010004001021c0010006000201000a06 else 0x41370004001000400100040010005000006000906)) else (if i < 214 then (if i < 213 then 0xcb04dc000000003f00000010004001000400100040010604020002000100000d09 else 0x14904dc001000400100040af00040010004191060007030104020c07) else (if i < 215 then 0x1fc07f01fc07f01fc07f01fc048022807f01fc07f01fc07f01fc07f01fc07f0004010004060601000300130b else 0x1000101))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x1000101 else 0x2f000101) else (if i < 219 then 0x1000101 else 0x1000101)) else (if i < 222 then (if i < 221 then 0x1000101 else 0x7f000101) else (if i < 223 then 0xf000101 else 0x1000101))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x1000101 else 0x1000101) else (if i < 227 then 0x1000101 else 0x1000101)) else (if i < 230 then (if i < 229 then 0x7000101 else 0x1000101) else (if i < 231 then 0x1000101 else 0x7000101))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x13000101 else 0x1bb000101) else (if i < 235 then 0x1000101 else 0x1000101)) else (if i < 238 then (if i < 237 then 0x1000101 else 0xb000101) else (if i < 239 then 0x1000101 else 0x1000101)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x1000101 else 0x1b000101) else (if i < 243 then 0x1000101 else 0x1000101)) else (if i < 246 then (if i < 245 then 0x1000101 else 0x1000101) else (if i < 247 then 0x1fc07f006007f01fc07f02481bd01fc07f01fc05001fc07f01fc00001fc07f01fc07f01fc07f07000509020209080503000000170d else 0x1000101))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x1000101 else 0x12b000101) else (if i < 251 then 0x1000101 else 0x100040010004001000400101050000000805)) else (if i < 254 then (if i < 253 then 0x100040010004001000400101050000000805 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 255 then 0x100040010004001000400101050000000805 else 0x1bf00041c10004001000400100040010005050000000a06)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x40c10004001000400100040010005000006000906 else 0x100040010004001000400101050000000805) else (if i < 259 then 0x4c013004c013004c013004c01301fc013070707010005000b07 else 0x42c07f004c013004c013004c013004c013004c01300000404000800000d08)) else (if i < 262 then (if i < 261 then 0x3f41c7000c003000c00307140a700f4003070c003000c003000700000b000700040f09 else 0x15b0000043056c1d1010c1cf072405806c415b056c1cd00001cb056c15b056c15b056c15b000e00090008060300000000150c) else (if i < 263 then 0x15b0000043056c1d3010c1cf072405c06e415b056c02d00001d5056c15b056c15b056c15b000e00090008060300000000150c else 0x4c013004c013004c013004c01301fc013070707010005000b07))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x1fc000004c000004c013000c013004c013004c013004c013004c01309040007000000060001100a else 0x4c01300740130074013004c013004c07f004c013004c0130a0b060402000505000f09) else (if i < 267 then 0x1d700001d7075c1d7075c1d7075c15d075c1d707641d700081d70c0a020900080605050f09 else 0x101)) else (if i < 270 then (if i < 269 then 0x101 else 0x65002c0000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 271 then 0x1000101 else 0x11000101)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0xbd000101 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 275 then 0x1000101 else 0x101)) else (if i < 278 then (if i < 277 then 0x1000101 else 0x1b000101) else (if i < 279 then 0x15d0000038055c157055c12b055c171055c157055c157055c1570704020003080002000f09 else 0x101))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x5000101 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 283 then 0x63000101 else 0x105000101)) else (if i < 286 then (if i < 285 then 0x101 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 287 then 0x1000101 else 0x1000101))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x740b3000000002c40b102c403702c40b102c40b102c40b10907000005000500030e09 else 0x1000101) else (if i < 291 then 0x104dc00100040010004001021c0010006000201000a06 else 0x1000101)) else (if i < 294 then (if i < 293 then 0x101 else 0x15f000101) else (if i < 295 then 0x1000101 else 0x101))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x101 else 0x1b000101) else (if i < 299 then 0x1db00001db076c1db07741db05741df00281db076c1db076c1db0a070a0004010104000f09 else 0x101)) else (if i < 302 then (if i < 301 then 0x101 else 0x5000101) else (if i < 303 then 0x100040010004001000400101050000000805 else 0x109000101)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x101 else 0x7f0000013004c013004c013004c013004c013060301040005050b07) else (if i < 307 then 0x93024c000027400006b4041024c0930784093024c093024c0930106020006020000000f09 else 0x1000101)) else (if i < 310 then (if i < 309 then 0x11000101 else 0x1000101) else (if i < 311 then 0x101 else 0x101))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x3ec0050014005001400503e40050014005020108040400050b07 else 0x5000101) else (if i < 315 then 0x5000101 else 0x101)) else (if i < 318 then (if i < 317 then 0x101 else 0x6201880000000062018800041880620188020201000100000a07) else (if i < 319 then 0xa6029800000000a6029800042980a60298020201000100000a07 else 0x4000001c3700004001000400100040010004370000437000040010004370000c370000400100040010004001000400100043700004370000400100040010004001001700100013061500251d000000001e000b0c1c2614)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x18c0630000000018c0630000463018c0630020201000100000a07 else 0x4000001c3780004001000400100040010004370000449200040010004370000c4de000400100040010004001000400100043700004498000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 323 then 0x4000001c3800004001000400100040010004370000448a00040010004370000c4be000400100040010004001000400100044000004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x4000001c388000400100040010004001000437000044a200040010004370000c3700004001000400100040010004001000440800044a0000400100040010004001001700100013061500251d000000001e000b0c1c2614)) else (if i < 326 then (if i < 325 then 0x4000001c398000400100040010004001000437000043700004001000450c000c5760004001000400100040010004001000437000044b0000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x3700004001000400100040010004001001c00300040010004001000437000040010004001000400100040010dc000100040010213140e14100c051805130015040102001f11) else (if i < 327 then 0x370000400100040010004001000c001001c0010dc0001000400100040010004001000400100040010dc0001000400100040010213140e14110c0a1715050001020605001f11 else 0x4000001c39000040010004001000400100043a6000437000040010004370000c3700004001000400100040010004001000441800044c0000400100040010004001001700100013061500251d000000001e000b0c1c2614))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x400100040000004001000400100040030004001000400100040010dc0001001c3700004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x4000001c37000040010004001000400100043700004370000400100045b4000c57e0004001000400100040010004001000442000044a8000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 331 then 0x4000001c37000040010004001000400100043ac00044e2000400100044cc000c370000400100040010004001000400100044120004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x620188000400000001d00000000100000706)) else (if i < 334 then (if i < 333 then 0x106302400000000000000000504 else 0x2980a602b80000001000100000504) else (if i < 335 then 0x400100040000004001000400100040030004001000400100040010dc0001001c4d00004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x101)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x400100040000004001000400100040030004001000400100040011340001001c4d00004001000400100044d00004001000400100000418000f020000000a16001503021e10 else 0x63018c06d80000001000100000504) else (if i < 339 then 0x7b418d06340000001000300000504 else 0x872000101)) else (if i < 342 then (if i < 341 then 0x86a00046320000000000100000504 else 0x18d800018d8000237000100000000000605) else (if i < 343 then 0x620000000418806a00000000000000000706 else 0x2980a603020000001000100000504))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x400100040010004370000400100040030004001000400100040010000001001c428000400100040010004370000400100040010000041c0017020000000f19001003121e10 else 0x400100040010004428000400100040030004001000400100040010000001001c428000400100040010004428000400100040010000041c0017020000000f19001003121e10) else (if i < 347 then 0x63018c06880000001000100000504 else 0x101)) else (if i < 350 then (if i < 349 then 0x1a9000100006340100000403 else 0x40010000001000400101f40010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e) else (if i < 351 then 0x62000100001880100000403 else 0x630001000018c0100000403))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0xa6000100002980100000403 else 0x230dc0001000c0010004001000401100040010004001000400100040010dc000b00040010004001000400100040010000150600120500130e02051106001c0f) else (if i < 355 then 0x18c000100006300100000403 else 0x101)) else (if i < 358 then (if i < 357 then 0x46340000000303 else 0x100040010044001000c0010004001000400100040010004023002c001000400100040010dc00010004001101702130012000a0c01010d00001a0e) else (if i < 359 then 0x4000001c3b000040010004001000400100043b4000437000040010004514000c370000400100040010004001000400100043700004510000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x18806200000000001000100000504))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x18c06300000000001000100000504 else 0x2980000001000000000404) else (if i < 363 then 0x4000000400700040010004001009c0010004001000400100043700004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f else 0x101)) else (if i < 366 then (if i < 365 then 0x118c06300000000000000000504 else 0x18d000100006340100000403) else (if i < 367 then 0x101 else 0x46320000000303)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x63600046360000000000100000504 else 0x400000040070004001000400101fc0010004001000400100044280004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f) else (if i < 371 then 0x400100000010004001009c0010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e else 0x4000000401f000400100540010004023000400100040010004001002c00100040010004370000400100040011114030a000800020d01070609001a0e)) else (if i < 374 then (if i < 373 then 0x700040010004001003c00100040010004001000437000040010004001000408100040010004001007c0010b0e080a000a000309030f0604001a0e else 0x4001000400500040070004001000400100040010034083021400500040010004001000437000040010004001000400100040010200160e010911181b180f0504021700001f11) else (if i < 375 then 0x18c000100006300100000403 else 0x1006c0010004001000400100040010004001001c0010004001000400100040010024001000400102120b04040f05060105030000180d))) else (if i < 380 then (if i < 378 then (if i < 377 then 0x700040010004001003c00100040010004001000437000040010004001000400b0004001000400100440010b0e080a000a000309030f0604001a0e else 0x700040010004001005400100040010004001000437000040010004001000400b0004001000400100e40010b0e080a000a000309030f0604001a0e) else (if i < 379 then 0x21c087021c08f02240870180087022c087021c087021c087021c087021c03a02340870030087021c004021c087021c087021c087021c087021c08719151100150016171508000b020107000000122313 else 0x868188000000009501e800041b00620190020201000100000a07)) else (if i < 382 then (if i < 381 then 0xc2029800000000b302c800042ac0a602a8020201000100000a07 else 0x8700040030f0000100040010dc001f0004001000400100040010004007000400510c00930f1000100040010dc00010004001000400100040010004091000452000fc52400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17) else (if i < 383 then 0x8700040030f0000100040010f0001f0004001000400100040010004007000400510e00930fa000100040010f000010004001000400100040010004091000452800fc53400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x87000400310e0001000400110c001f0004001000400100040010004007000400510c009310f0001000400110c00010004001000400100040010004091000453800fc53c00040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x87000400314a00010004001148001f0004001000400100040010004007000400514e009314c0001000400114800010004001000400100040010004091000452000fc7a000040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x1b8063000000001ea0690000466018c0640020201000100000a07) else (if i < 387 then 0x5aa000101 else 0x93024c8c8025c093026c099024c005158855a024c093024c0930254093024c099024c089024c007024c09d024c093024c093024c093024c093024c0001a1e111d00111e15001a070e0a00060803020f2313)) else (if i < 390 then (if i < 389 then 0x1002440a5029c091025c091028c001024409f024409102a476a02440911d8808f024409102440a1024400102440910244091024409102440910e1c001102000c19060b140200020a000a062212 else 0x6322188000000400023406ba19c865a0000000800000906) else (if i < 391 then 0x62000100001880100000403 else 0x4001000400100040010004001000400100340010004001001400102ac001026c00700040010dc00010004001000400100000c1a0003000100000614000000121d10))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x10000001000403f000400702440010dc0540000c00100043c4000401f000400100040010014001026c00100040010004001000400100040010004001001a10161200041219140209091909000104002313 else 0x4005000400100040270244430001c001026c0010004001000400100040010004001000400100040010dc000100040010004001020d1610141a0e0b1a0d050001020608001f11) else (if i < 395 then 0x31100001000400014900010004007000400100140010004001024c00100040010004001000400100040010004370000400100040010004001001a0000000e180a001900160008111209022112 else 0x4000002c001000c0011490023024c0ad0004001000400100040110004001000400100040010004001000400100040010dc00010004001080016061a14110f090419000c00000b022011)) else (if i < 398 then (if i < 397 then 0x88024e000000006201f000041b807e8188020201000100000a07 else 0x6781de0000000000025806300010738262010000000000000a07) else (if i < 399 then 0xbe02c600000000a602d000042980b682a0020201000100000a07 else 0x1000400100040010dc00b111200af1600001000400113b8003000400116e800100040010004001000400100043b800040010004001000400700043700004001000400100090118241b1e18031713100c00211200231701070b2916)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x1000400100040010ee00b111400af1620001000400113d80030004001170800100040010004001000400100043b800040010004001000400700043b80004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x590000101) else (if i < 403 then 0x10004001000400111200b111200af1660001000400113f802b00040011728001000400100040010004001000445000040010004001000400700044480004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x10004001000400116000b116600af16000010004001212802b00040012080001000400100040010004001000458800040010004001000400700045800004001000400100090118241b1e18031713100c00211200231701070b2916)) else (if i < 406 then (if i < 405 then 0x1b208e2000000018c0698000463020a0638020201000100000a07 else 0x8940000794000000000404) else (if i < 407 then 0x8841f90000000400020c06c418d06840000000800000906 else 0x740b102c40b120e00b302c40b102c47ec02c488c02d40b102c408300c00b100dc01d1e300b102c40b102c40b102c40b102c40b102c40b100001112001906180011190500000d0700010b002314))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x10004001000400116e80b117280af208000100040011f0802b000400116e800100040010004001000400100045c200040010004001000400700045ba0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f286aa000084218c800119480001be8632030300000000010a07) else (if i < 411 then 0x10004001000400113b80b113f80af2128001000400113b80b700040011f0800100040010004001000400100044f600040010004001000400700044ee0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f786b6000085218d800119b80001c38636030300000000010a07)) else (if i < 414 then (if i < 413 then 0x400100040b100040010004007000c0010004001000400100045a000043700004001000400116e80010004001000400100040010100101100120f07091a0d0403031805021f11 else 0x1116000100040010dc00b100040010004003001c00100040010004001000400102bc001000400100045ba0004001000400100040010314151216140c1607080e0002040104002011) else (if i < 415 then 0x110004001000c00113b80010004001002c0b9000402300040010004001001c00100040010dc00010004001000400100040010000021a0013001400000b08001808011e10 else 0x210dc0001000c001000400100040110004001000400100040010004001135800b00040010004001004400100040010000150600120500130e02051106001c0f))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0x37000040010084001000c001005c0110004001001c00100040010004007000400100040010004001000400100040010001000b000f010014150d030f07041c0f else 0x18c000100006300100000403) else (if i < 419 then 0x100040010004370005c003004401100440af001c01100443b8004401100040110044001004401100440110044506004400100440110100170917150c19080618010b020208002011 else 0x40110004001000c000002c001000400100040b1000400700040010004001001c00100040010dc00010004001000400100044480000021a000c001400000b08001708011e10)) else (if i < 422 then (if i < 421 then 0x400100040010004001000c0bd15300010054005000401f000400100040bb0004001000400b000400b00040010dc000100040010000151114100b031b0a170018000c07021f11 else 0x18c000100006301ee000000010000000605) else (if i < 423 then 0x1000c0010004001000400100040010004001004c0010004001000400100040010074001000400102120b04040f05060105030000180d else 0x100040390004001135000300e403900e403900e4370001c0390004039007c00100e403900e401100e44d600e401900e403901001509141208171a06150108020206001f11))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x62000100001880100000403 else 0x100040010004001000401d0004001004c00f0000001000400100040010dc0001001c01300040010004001000400100040010000001c000a02010000081a000801171d10) else (if i < 427 then 0x6200010000188070000000010000000605 else 0x102fc460000400100040010004001007c00100040010004015007c0010004005004400100040070004001002c00100043700004001004c00b00200800131d071a161900151015030107082212)) else (if i < 430 then (if i < 429 then 0x100000010004001000400700040030004001000400100040c10004001160837000040010004001174000100040010004001000400101001210001411001a0d0f0709070306021f11 else 0x2980000298000000b000100000504) else (if i < 431 then 0xb002c00b00040190004003030c00b001c00b002c001002c00b000400b0004001000400b002c00b012c00b0dc000b002c00b0100150f12070c051a0b160007011806001f11 else 0x87031c0010004001021c37011a0001032c0010004001000455402b403f021c00100040600324001000400100040c500040010304001000400100043c4000c3e0001c00102445d80004001024c001007c00100140010004001000458200040191a2f2f29182a24311032232f1522000d0a092f25011600002303200006381d)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0xcd03440cd021c0cd021c0870180087022c0cd0334087033c0cd03340cd03340cd033408703340cd034c06003340cd0334087021c060033400003340cd03340cd03340cb03340cd24041d16171202181918000a1c000014110100121a062916 else 0x8703540dd021c0e10354017035c0d9021c087021c087021c087036c090021c09801200d5021c08b0334087021c06001800cd021c087021c0870180087021c0d1021c08700d8060021c0871c18060021c0d102a0087021c08701400870160087020008b01800b0022c06802200cd01e00e303540cb01c0087037c08702e0087021c060021c0d50280087004a424b4947413d47454343413d3b38221d1b3733311900152e110d2d2b3c24260c0708342c2303045029) else (if i < 435 then 0x106201880000000403 else 0x1063018c0000000403)) else (if i < 438 then (if i < 437 then 0x10a602980000000403 else 0x401f0004001001400b005400100040010dc0001000400100040010004019000437000040010004001000400100170d0b0d150e0c0e06000800000803041d11) else (if i < 439 then 0x118c06300000000403 else 0x118d06340000000403))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x118c86320000000403 else 0x10004001000400100040010004000017c01f0054001000400100040010004005002c001000400100040010dc00190004001000d0100000a021b00020a19000000161d10) else (if i < 443 then 0x40010004001000400100040050054001007c001006400100043700004001000400b000400100040010004001000400f0018000900170c17000f0015000002011d10 else 0x7c001000000100040010004001001400b000400100540010004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10)) else (if i < 446 then (if i < 445 then 0xe40010000001000400100040010014051000400103940110004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10 else 0xe7000447800044ee000400117800af0004001000c5e200040010f60087000400f0004130030400100040010004001000400700040010dc00010004001000400100044ec00040010004001091e0a1c20020521231d001b240d170010130f1e00000d2c17) else (if i < 447 then 0x2d40af000400100040010064001000400b0004005002c01f006401f00044ee000400100540010014001000437000040010004015000400100040010004001000400100040010004001191d0a22182306240e21002216100b002300161a1b0e052b17 else 0x3900000010004001004400100040010dc001500044d6007c00100440010064001000400100040010044001004400100040e500fc0010004001000400b0014011000400100040191c260023121d12220f1a200000221e170808000005022916)))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x41e006201e2000018800020004000705 else 0x11460007000400100140010004001000400100040010dc0001000c001015c001000400100040010004001001451a000400100040010004001001018190010001a00031200000d0008001103022414) else (if i < 451 then 0x10004568000400700040010004001000400100040010004001001c00100040010004001000402f00040170c13000d0b1201000103000b000b1a0e else 0x40010004001000400f0000001007c001000400100540010014001000405100040010004001000400100040010dc00190004001000604000001071c00020b1a000000121e10)) else (if i < 454 then (if i < 453 then 0x100bc0010004001002c001004400100040010004007008c0010004001000400100040010dc0001000400100040010c19031304000012000a060f0507021c0f else 0x100040b10004001000400100040010dc000100040010034001000400116e80010004001000400500040010004007000400d00140010004001001c0010004001000400100040011520251c001a24140815192507020f0001240e2100032a16) else (if i < 455 then 0x40010004011018c0110004001004400d001c01100440630044011004400103a401100040110dc00110044011004401100000d0f0015090c00150100001100021d10 else 0x100140010dc000100040010004007030458200040010004001021c00d001400100040010004001000400100040010004001000400d0004007000400101800010004001000400100040011d26160020100224000e0d1d251c180424000b0f0116002c17))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x106201880000000403 else 0x10a602980000000403) else (if i < 459 then 0x40000004001006400100040010004001007c02f00540010dc00010004001000400b001400100040010dc0001000400100040010000090b00190d1500150100000b00021e10 else 0x118c06300000000403)) else (if i < 462 then (if i < 461 then 0x10004001000400100040030004001003c0011200001001c007000400100040010004001000400100040010e150012000c0b160102090006031a0e else 0x4001004400100040010004001005c0010dc000100440010004524000400100040010004001000400100040010084007005c0010004001024c021001c0010004001000400000040010925002508231a200200141e1001101a0317001500142a16) else (if i < 463 then 0x4013000400b0000001002c00b0004001002c00b000400b000400b002c00b003c00b002c00b002c00711000d000c0203000a05000404180d else 0x62000106200000100000403)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x63000106300000100000403 else 0xa600010a600000100000403) else (if i < 467 then 0x1006403900040010004370010400100040af000400100040e500040010004001005c00100040010004001000400700040010dc000100fc0150004001001611152113171800031306110000041611072413 else 0x10004130000c05f03ac00003ac069000003903b40ef000c07f0400000009000300000f09)) else (if i < 470 then (if i < 469 then 0x18c000118c00000100000403 else 0x106201880200000403) else (if i < 471 then 0x106201880200000403 else 0x18806200010000000403))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x18806200010000010403 else 0x58018c058015805b0160058016805a8160058018805b8160080c050b040a0108000f09) else (if i < 475 then 0x1000101 else 0xb000101)) else (if i < 478 then (if i < 477 then 0x5c029805c015808f017005c017805e817005c018808f8170080c050b040a0108000f09 else 0x1000101) else (if i < 479 then 0x9f0208082818809f818800040000000328000000030302010a07 else 0x9d0210084818809d81a0004c0000000000000000000302010a07))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x1000101 else 0x18806200010000000403) else (if i < 483 then 0x18806200010000000403 else 0x18806200010000010403)) else (if i < 486 then (if i < 485 then 0x18806200010000000403 else 0x40000000188000000000404) else (if i < 487 then 0x1880dc018809b016005c01880620188080026e06201880004202080d000c070b040a031009 else 0x106201880200000403))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x18800040000620000000000000504 else 0x1880620048001400000000000000000100000706) else (if i < 491 then 0xc000001880308001062000000000100000705 else 0x106201880200000403)) else (if i < 494 then (if i < 493 then 0x400100040010000001000400700040010004001000400100040010004001000c0010004001000400711000d000c0203000a05000404180d else 0x620000000000d000100000404) else (if i < 495 then 0x3c1880000000303 else 0x5406200150000010403)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 0x1000101 else 0x306001880200000403) else (if i < 499 then 0x6200000000188062018806200010620188010000000000000a07 else 0x80063008001681f4020008001782160200080018823a8200080c050b040a0108000f09)) else (if i < 502 then (if i < 501 then 0x1000101 else 0xc0010dc0017000401100040010004001001c02100040010004001000400100040010004001000400100040011905021000110505000303040000001b0f) else (if i < 503 then 0xa6000100002980100000403 else 0x100040010dc00010004001000400100040010004001005c00100040010dc0007000400700840010004001004402f000400100040011618151814170c001302070001010004002011))) else (if i < 508 then (if i < 506 then (if i < 505 then 0xf103cc01100bc000000c003000007f0004001000000000301000b07 else 0x18c000100006300100000403) else (if i < 507 then 0x4001000400100e4001039401700040010004001001c0010dc002f00040010004001000437000040010dc0001000400100640010004001011a00030b00110c0004101600020a0e08012112 else 0x400100040010004001000400100040010034001000400100040010004007001c001000437003d400100040030004001000201000005001a00120116000e00031d10)) else (if i < 510 then (if i < 509 then 0xa6000100002980100000403 else 0x40000000000000c0010004003000437000040010004001000400100040010004007000400100040010004001000400100040010d0718030c020c0005010a0000030600011e11) else (if i < 511 then 0x1000101 else 0x9a063009a01681f5026809a023821e026809a018c23b0268080c050b040a0108000f09))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0xc0010004001000000100040070004001000400100040010004001000400100040010004001000400111000d000c0203000a05000404180d else 0xb0a602980200000403) else (if i < 515 then 0x2980340000002c298000300000504 else 0xbd02e80ba82980bd82b000040000000000000000000302010a07)) else (if i < 518 then (if i < 517 then 0x1000101 else 0xc013000400b0000001002c0070004001002c00b000400b000400b002c00b000400b002c00b002c01311000d000c0203000a05000404180d) else (if i < 519 then 0x42980000000303 else 0x10a602980200000403))) else (if i < 524 then (if i < 522 then (if i < 521 then 0x2980a600010000000403 else 0x2980a600010000000403) else (if i < 523 then 0x142980a60058000000003000000000605 else 0x29800040000000000303)) else (if i < 526 then (if i < 525 then 0x2980a6000b0000000403 else 0x2980dc02980b9017005d02980a602980b802e60a60298002c2e2080d000c070b040a031009) else (if i < 527 then 0x298000c0000a60280000000000504 else 0xa6000000002980a602980a600010a60298010000000000000a07)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 0xb000101 else 0xb806300b801781fc02e00b8023822602e00b8029823c82e0080c050b040a0108000f09) else (if i < 531 then 0x40d800040130004370002c04b002c041002c001002c0010004007004c00b002c00b002c00b002c003002c00b002c0010f150014111205000700100003040000021e11 else 0x4001000400100040110004001000c12e000400100040010004001007c001000423000040e00388001000400704b000100000010004001004c001111f13001610001500140a051403080104002212)) else (if i < 534 then (if i < 533 then 0x10004001000471000043701c5800500040070004001000471200040011c50001000400100140010004003000400100040010dc00010004005000000100000010dc00011b180f1d0418001c0200120017151d1b130b1908002715 else 0x100040010004001000400101e40030004001000437000040f700040010004001001c005000400100040010004001000400000130b1100000a0100040506000201041d10) else (if i < 535 then 0x7f03e407f01fc07f01fc0f903ec5ea01fc0f901fc07f01fc0f903e407f01fc0f901fc07f0cc05ec01fc07f17b807f01fc07f17a007f01fc07f0000160f141b0f031506110e08050a0006022212 else 0x100040050004003000407f001474c00040070004005000400100043700004718000400100040011c6800100040010f20001000437000040fb00040011d38000000400100040012210170000030021201a1a1d1401100d1b0b160101172916))) else (if i < 540 then (if i < 538 then (if i < 537 then 0x100040050004003000407f0014774000401d0004005000400100043c80004720000400100040011c8800100040010f2000100043c800040fb00040011dd8000000400100040012210170000030021201a1a1d1401100d1b0b160101172916 else 0x3fc000101) else (if i < 539 then 0xc03d03f400103fc005000400100140010004001001447400040010004005000477c00040011e180010004001000400100040010d000012001a0a160c030b0400040e0004022012 else 0x1e7879c0100000303)) else (if i < 542 then (if i < 541 then 0x40010004003000400100040010004001001c00100040000dc0001000400100040051ca071a000400100040010004001000400100140c16000a0200000c0f06000407021e10 else 0x2700340010004001000401d000400100040010014001001c71a000400100040010dc0001000400100040000004001000400100040010e050f0e00140c0900000f110002040009032012) else (if i < 543 then 0xdc00011d3800100040010004001001401f000407f00540fb0004001000400100040070004001000400100040010004081000400100010f121c000e140905110f05020301041f11 else 0x40010074005000400100043d0003c001000400100040fb1ce80010004001000400100040050dc001d112074c1cc075e01fc00500040010004001000400100040070004001000400300040010026252a001a2318001c1d030000110b001a02000016080c2d18))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 0x1000474e0014001000401f00040150004001001400101a400101fc005000400b0004001007c3700004001001402d00040190004001000400100040010014001002c00100040010404001002112200e0f211e1523042408010000151b09000118022c17 else 0x40010004103000400100040010004001003401b000400100143700004001001c001000400100040050004001000400500040010004005000471a0004001001400100040011e20100b1827021900021b1d14120e030200180e080e2916) else (if i < 547 then 0x300040010074001003c013002c001000400100040010004105003c0010004001000437000040010004744000000100040010004001004c001101f0f0b001e001503100a05000309010a002112 else 0x4001000000100040bb00040010004001000400100040050004001000400100040010004001000408317070700070401090402000001180d)) else (if i < 550 then (if i < 549 then 0x40010000001000400700040010004001000400100040210004001000400100040010004001000401b17070700070401090402000001180d else 0x4003000c013000c0030dc001b000c017000c009004c001004401f00040010004001000c003000c003000c003001c00000020c160007020600040704000006021d10) else (if i < 551 then 0x40010000001000400100040010004001000400100040070004001000401300040010004001000400317070700070401090402000001180d else 0x40010000001000400100040010004001000400100040070004001000400300040010004001000401b17070700070401090402000001180d))) else (if i < 556 then (if i < 554 then (if i < 553 then 0xd0074750000c000004c013004c109042407f004c01101fc01301fc001004c01301fc0010dc00131d50013004c0010f200130f300131d580131d480fb004c013004c0130004001042c330004c001000407f042401f004c013004c107000c270f0000002e00082811002e192d00231c03001b001800151b01351c else 0x1ba01800cc018401fc3300c4033018800fb0cc033018886ec1ba807f03f407f0ce00fd01fc07f044407f189007f01fc33003f407f01fc07f03ec07f043407f01fc33c046410f01fc6ee189807f01fc11301fc07f01fc0fb01fc0fb03ec0fb045407f01fc07f01fc03d0cc007f01fc07f01fc07f01fc07f01fc0fd03f407f01fc11701fc07f1800000013004800330000000e4a3b490748474600453a442e43424129331f40253f3c301e21280f4d28) else (if i < 555 then 0xfd01f40fd03f433003f40fd03f411b03f40fd03f40fd03f40fd046c10f0cc00fd03f433001fc07f01fc0fb01fc0fd03ec0fd03ec0fd03f411b03f407f03f407f03f40fd1f1800181c16141018110c03000b000008001206032815 else 0x401300040010004001000400f007400100043700004001000437000040010004001000000100040010004001002c000000f0c15000a0a0400050706000001021c10)) else (if i < 558 then (if i < 557 then 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110a00010004001007400100040000004001002c00100121610001f1d1800021c151705110b1606190207002916 else 0x400f0004013000400100040010004001000437000040010004001000401d0004000000400100040010004001002c00f0004001000d07060005091400020b0400000d001e10) else (if i < 559 then 0x8c001004c00f00040010004001004c00100040510004001000400100740010dc00010004001000400100000000004000000400100040010015151500120c070c050b020a00060900092012 else 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110c0001000400103ec00100040000004001002c00100121610001f1d1800021c151705110b1606190207002916)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 0x4001002c00100040010004001003c01d0004001004c001000400f000401d004c37000040010004001112001d00740010004001000400b00040010004001000400100040010004001271e0e1f0a1b092314141900101702000d0401000b02002b17 else 0x10004001003c001000c0010004001000400100040010dc0001000401b000000100040070004001000400100040010a0308070d000705070400030002021b0f) else (if i < 563 then 0x1000000100540050004001000400100040010dc00010004001002c001006000100040010004003000400100040070004001000810070004060900010c00000a12031d10 else 0x1004c00100040010004001000400100043700474001000400f0dc00010064013001405100040010004005000402d00040000004001007c00100040011a0016130e1115150d04040900000010000a022313)) else (if i < 566 then (if i < 565 then 0x100040010004003000402f0004001001c0010004001000437000040000004001013c0010004001000400100040010e00080c0c0806100404040a0102001b0f else 0x100040030474001000402f0004370000400100040010014001000400100043700004001014437000040000000001001400100040190004001001b001c00170d0f0706090311010e0812002112) else (if i < 567 then 0x40000004105001c0010dc00bd006c0bd0004003000400100040010004001001c00100040010004023000400100040010004001071000001d000012180312180904010c001f11 else 0x400100040130004001000400f0004001000437000040010004007000403b0004000000400b00040010004001000c00f0004001000d07060005091400020b0400000d001e10))) else (if i < 572 then (if i < 570 then (if i < 569 then 0x400f00040050dc000104840010004001004c013000411d000400f00040010004001001400100040010c6000100040010dc011f0dc0001001c00100b4000012c00100040010064001000f0c06032023241c1d0021101907021a18161311002a16 else 0x122000400100040010004001001c0010004003000435a0c800010004001000400100040010460001000400100a0001006c00000040010004001000400017191c010c0814180a001114000308061104022313) else (if i < 571 then 0x1402100040010dc00010004001000437001dc0010004001048c0010004007000437000040010000001000400100bc001000400100040011d1d00001903110018130b051200040b002011 else 0x40070dc00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f)) else (if i < 574 then (if i < 573 then 0x101 else 0x700040010004001000400300043700004001000400100040010004000000000100040010004001000400100040010e00080c0b0d07030a0206020001051b0f) else (if i < 575 then 0x40070ee00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f else 0x1000c001000400100040010f200010004001000437000040070004001000400103ec0010004001000400100040010004001000c090600000802000e0404000201001e10)))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 0x400b0004001007c001000400100540050004001000400100140010dc00010004001000401900040010004001000400100040011500040e0d09010f09051200000111070a04002113 else 0x10004001001c00100040030004001000400100043700dc00010014001000000100040010004001000400100040010b000815151400090e0e05040002021b0f) else (if i < 579 then 0x7d0004001000400100040010dc000101b40050000007000400100040010004001000c0010004001000400100040010004001000c000b0000130700080d05000408021d10 else 0x440010084001017c0010004001000400b0dc00010004001000000100040010004001000400100040070004001000400114010a0a06060014020005090905031c0f)) else (if i < 582 then (if i < 581 then 0x11007c00100040010dc001f007c0010004001007c01f001c06500000070194003007c01f007c019007c01f007c01f007c01f000e001500050003000a1207000013011d10 else 0x40010494001009c001000c00500040010dc00010004001000000100040010004001000400100040010004001000400118010a080a0700120200050a0905041c0f) else (if i < 583 then 0x405f0004071000400100040030004370000400100040010000001000408100040010004001000401f00040010004001180009090b040013050107080802061c0f else 0x1c0010004001000400100040010014127001c005000c005000400100040010dc00050004005000400100143c4000c001024c00103340600004001000400100040010014005027c065000000500140050014005272421090828261c04250017021813211a120c0f0102130e003019))) else (if i < 588 then (if i < 586 then (if i < 585 then 0x5f0004001000401f0004001000400100040190dc00010dc000b00040010004001001400100040010004001000000100040010004001070c110f0a02041302080c020803070c001f11 else 0x140050004001001c00100043700004001001c0010004003000400100040010004003000400100040010004001000400100040010ef80010004001000400000040000004001000400109261a201321191e0f00151d1d0d0517191202001607002a17) else (if i < 587 then 0x24001000400100040010dc0001001c00500040010004001000400100040000004001000c00100040010004001000400100040010004001b00001405000a0e07000609021e10 else 0x1001400300040010004001001400500040010004001000406d00040050004001003400504a40050dc00cd01800010000005001400500040050014370001400500080207001513060013051c00180a03000a01002514)) else (if i < 590 then (if i < 589 then 0x4ac0b1005c00103cc00000003f000140170004005005c02f0100000801070002000e09 else 0x7c001002c001000402f00040010004001000400100043700dc03700004001000400100040010004001006400000040010004001001700020004000b000c0900000604091e10) else (if i < 591 then 0x100040010328001000c0010dc0007000400301c4001000400102fc00100440c8000000100040010004001000400100040010004001000e1c110a06001808020e080503090d021f11 else 0x400100040010004001001c0010dc000100040010dc037000040010004000017c00100040010004001000400100040390404001000c10030000000900080c05000415071e10)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 0x4001000400104a40ad000400100440070dc00010004001000400103c037000840010dc00010004001000400100bc001000400100140010004000001f1815140b00081002000710050d00071b2212 else 0x3c0010004001000400100040010004001000400101c400100040010004000000400100740010dc000100040010004001002c013000b15160000001b00050a04000209021e10) else (if i < 595 then 0x130074001004c013007c3700004001004c013004c003004c0750044013004c013004c013004c0010f30013004c0130cc0013004c013004c00301fc0010004013004c001004c000004c013004c01323251f0001242215032100141b121c1b180d0b0d10010705002e19 else 0x13003c0010004370000400100040010dc0001000400301c400100040010004000000400b000400100040010004001000400100040010d0b0c19090400090600140603010b0f001f11)) else (if i < 598 then (if i < 597 then 0x405f000c0010d0000f000400100043700004001000400100040010004001001c000001c00100000010004001000400100040010c0a0b170803000805000e0503010800001e11 else 0xf004c0010dc0001000400100040510dc0001000400100040010dc00010004000006400100000010004001000400100040010004001030c0d190a04000a0805110604010a0f001f11) else (if i < 599 then 0xbc001000400100040010004071000400104000030004001000437000040030dc037000040010004001002c00100040010004001000400100040c5141104120e01180c12000708070505100501032313 else 0x1000400100040010004007000400100040fc00040010000000000400100040010004001000400300040010004001160808090a060010040402010800031b0f))) else (if i < 604 then (if i < 602 then (if i < 601 then 0xb0004001004c00b000400b002c0070dc00410004001000000b0004001002c00b002c00b004c00b000c00b002c00b160b080909060007020009101001041b0f else 0x37001b400301b4071000406d01b406d001c06d01b406d01b4013000400101b400b004c001001406d0dc006d03a000001b412f03a806d04b4001008437001b406d000b2321001d1e060014181c000f1218000701002514) else (if i < 603 then 0x400100540010014001002c013003c0010dc0007002c001000418800040090004370000400100040010dc0001000401100040070a60630000400118d0007007401b0dc00010004005000400318c8017000418c00040010004007000400d000463600040010dc0001008401f000c37000040010004001006437042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x1b000401b00540010dc001b00040000004131017c003006c01b003c001006c001006c01b006c01b00bc007006c01b16190c140f000713120505100003001b0f)) else (if i < 606 then (if i < 605 then 0x1c001000c0030024013000c003017c01d004406b000c00f01a40fd017c3300dc0370000401f000c01d000c003000c0000034003000c001000c003000c0031a141d0012100003110a0d000e04020b0600032413 else 0x40070004003000400100043700dc000f003c00f003c000003c00f003c00f002c00f003c00f003c00f000402f003c00f0dc000f000a0b0c0011000e00061402000000071e10) else (if i < 607 then 0x4001000400100040010004001000400100040010d2000300040010004007000436e000410c002c36a001c1080004001000000000000010004001000400100100021000d0004000a140800061200000300022414 else 0x34354000400d003401f003400d000c3700dc002f003402f00340070dc01030034069004c00d00040110440000003400d003400d000401304cc000003402f003400d2100001b1e1716160a0e1306080a00130300100d002615))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x10004001000400b000436200040010000000000400300040010004001001c0010004001000400b000400100040011607071414020012120505101000021b0f) else (if i < 611 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x4001000400100040010004001000400100040010004370000c0010004001001c0010dc0370000437000040010dc000100040000dc00010dc0001000400100040010012001e000e1e23000b1b0900071400000416022614)) else (if i < 614 then (if i < 613 then 0x400100540010014001002c013003c0010ee0007002c0010004142000400900043b8000400100040010ee0001000401100040070a8063800040011a10007007401b0ee0001000400500040031948017000419e00040010004007000400d000466e00040010ee0001008401f000c3b80004001000400100643b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x56601d013a0f0019400143c00aa03c019003c019903c000e865a0004762001c5ae0004001000400100040130f000010004676003c0010004001006c001000455a00040030004009000476e00040010004019004400100040070004017001c0550084001003400100040070f00001000401f0004001002c001000400300540050004005000400b1800000013004b00330046000e4a264907484746004539442e433b4229411f40253e3d331e30210f4e28) else (if i < 615 then 0x150f0000001a406901a406901a406901a406904dc06904d411d01a406901a40ed01a4069003406901a40690e12000e000e040b010501000300190e else 0x7400100040010034001000401f0f200010004476008400100f4001000400505200010004001069000f00040010f202b00004001000401d00046480004001000401d0ff00010f203c800040010f20003006401d005400b19f800300043c8013433819f00010004011000400b00740010074001000401300043c811d00051928001463b3b444444404040393d353716143433002f0c2e2c412928242127110d201e01081d1b1705044b27))) else (if i < 620 then (if i < 618 then (if i < 617 then 0x301ac10b01ac06b000006b01ac06b04e4000007401d01ac06b01ac06b01ac00f01ac3c801ac06b01ac06b000000040d150001000801060001190e else 0x6901a4069000c3ba01a4069047406900540fd0fc806901a406b047406904ec13703b406901a406901a406901a406901a40691c000f0d000506000206050504000605031f11) else (if i < 619 then 0x400100540010014001002c013003c00110a0007002c00100041a8000400900044280004001000400110a0001000401100040070a4868800040011a90007007401b10a0001000400500040031a8801700041ae00040010004007000400d000468e000400110a0001008401f000c42800040010004001006442842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x400100540010014001002c013003c00110c0007002c00100041b0000400900044300004001000400110c0001000401100040070a2869000040011a5000703ec01b10c0001000400500040031ae801700041b400040010004007000400d00046be000400110c0001008401f000c43000040010004001006443042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 622 then (if i < 621 then 0x1b811201ce11201541120698112000100040151b10001001c001003400100040010004001007c794000401d11200010004007000402b00046aa0004001006c44800040011ad8001002c001000402100440130004005000400b0004001003c02b0004001001400100040011e3000711200070024001000401d00180010004019340032002e002a00390014482a470d4626451f441d4301423b41153d3a2f0c280524002119094a26 else 0x400100140010004091003c103001401f0004003047400100040550004430000400100400010004001000400102440010004001060f150f1a0011060503001008010401001f11) else (if i < 623 then 0x4001047400111280000004001000400100140010004001000413d007c0010004001000c001004c001100e00030e0301000601030300180d else 0x13d0154055002c0fb00b442a00b40fb013402d017405500b402d00b402d00b402d00b402d04fc02d00b402d00b402d0600060403020000000904000001091c0f)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 0x1000401500040130004005000400700040010740001000400b13404d00004009000400100444d000040010ae000100046180004007001c01d00044d01ed0001003c14121c8001002c005000400321a8017000424000040010004007000400d00048dc00040011340001008401f000c4d00004001000400100644d043413f3c403c001b3c3d3b1a3735162e30382d2b362c2a120b25230f2422190a06010e02004825 else 0x1d809204e80b004e818404e81f304e8220801f0004001000400813a0007050c0010004003000400100040070004001005c4e800040012390001002c0090004007000400700840010004001000489200040030004005005400b000400122280010044001000c00f0004001000400513a0001005c001000403d000400100040193200170039002e00120014480f3908472e4627452544204338420b413640013f1f2c00291e094a26) else (if i < 627 then 0x100540010014001000400b2330013003c0011480007002c00100041e800040090004520000400100040051480001000401100040070b2060800040011eb0007007401b1480001000400500040032188017000425000040010004007000400d00048d400040011480001008401f000c5200004001000400100645203e424038413f00373f38361a322f162e2d4027243b3126120b25230f1f1d190a06010e02004825 else 0x14007020c00100040050014069001400500140051480005001400100141450014005010400500140050014005000119050c050e09030204000d00001b0f)) else (if i < 630 then (if i < 629 then 0x18c00000000007000000000404 else 0x524007002414b02bc4d0001c007001c14d051c007001c0aa0004007001c0070524007001c007053c0230014007026c007001c00700170a000d09050b0300090000080c0307022012) else (if i < 631 then 0x10024037001c0000134009054415300240090024009027400900240090024009002400913a0009001c0090912080605051207000a0b050000190e else 0x59007c058009605800b4058017e0580007c7e4000400100540010004580001c00d00040010004001000401d00040010004007000402b00048420004001006c58000040012148001002c001000402100440130004005000400b0004001003c02b0004001001400100040011fb000716000070024001000401d0288001000401931002d443a002a00360014472a460d4526441f431d4201413740153e35380c280524002119094a26))) else (if i < 636 then (if i < 634 then (if i < 633 then 0x63000000210000000303 else 0x7001c01d008c15700740230084580008c0230554000008c005008c023008c000008c023008c023008c0230002080000040400010800040000021a0f) else (if i < 635 then 0x100040150014001002c83a004c001003c001001c5b8002c00100041f8000400900045b80004001000400116e0001000401100040070b605f000040011f7000700b401b16e00010004005000400320a8017000426000040010004007000400d0004832000400116e0001008401f000c5b80004001000400100645b843413f393b3f00373f38361a322f162e2d4127243a3126120b25230f1f1d190a06010e02004825 else 0x18c00050001000303)) else (if i < 638 then (if i < 637 then 0x55c0af01a4005001c00516e0005056400500000050014005001400501040050014149001400500140050014005080e000c120504020a04040000001a0e else 0x18c000100006300100000403) else (if i < 639 then 0x242864818c063000047f822806f00002000200000906 else 0xfb00040011c8007f0004001000400100040010004001000404f00040011c60001200071822a00010004718000400123e800100040010004001000400100040010000001000c001100a001f1e0f1e1d00121d1800091d1a0019011016002916))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 0x241063018c0678004c80822c06d00002000200000906 else 0x1d20013004c013004c01d004c013004c013000c770004c013004c8c0004c013004c013004c8fc004c01301fc0131d20013004c0131d20013004c804004c013004c013004c0131303001d1c1419110016151a000e0600001a050100002916) else (if i < 643 then 0x8100004630000063000000000000605 else 0x63018c00000000003000100000504)) else (if i < 646 then (if i < 645 then 0x118c06300200000403 else 0x63018c00010000000403) else (if i < 647 then 0x118c06300200000403 else 0x63018c00000004020000300000504))) else (if i < 652 then (if i < 650 then (if i < 649 then 0x118c06300200000403 else 0x118c06300200000403) else (if i < 651 then 0x400018c0630000000000504 else 0x63018c00010000000403)) else (if i < 654 then (if i < 653 then 0x63018c00010000010403 else 0x118c06300200000403) else (if i < 655 then 0x63018c00010000000403 else 0x63018c00010000000403)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 0x1463018c0088000000003000000000605 else 0x63000040000000630000000000504) else (if i < 659 then 0x63018c00010000010403 else 0x118a000018c0630000100000504)) else (if i < 662 then (if i < 661 then 0xba001c0000000630000000000504 else 0x6300dc0630206020009a063018c06300b8091218c063000048b8080d000c070b040a031009) else (if i < 663 then 0x318c06300200000403 else 0x6c00018c0630000000000504))) else (if i < 668 then (if i < 666 then (if i < 665 then 0x63018c000d0000010403 else 0x63018c000f0000010403) else (if i < 667 then 0x9c18c0630005400000000000000000100000706 else 0x1000101)) else (if i < 670 then (if i < 669 then 0x630000c62018c0000000000000504 else 0x1000101) else (if i < 671 then 0x1718c000018c0600000100000504 else 0x19000101))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 0x746300000000303 else 0x246300000000303) else (if i < 675 then 0x18c0000000063018c063018c000118c0630010000000000000a07 else 0x40010054001013c0050004001000c00b1c6000100040010004208000400f0014718002c001000404f1c6004f0004011000401d09c02e80004001203000100040131c6004f000400100040032288017000422800040010084001000400d0004902055c0011c60001000401f04c471800040010004001006471842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 678 then (if i < 677 then 0x1d000001d001404d007404f007401d008c7180574149007401d02c801d007401d056c01d03ec01d00b401d007401d007401d007401d08110002061002080503000000000b04021f11 else 0x4c013004c01300f401d004c0131d201631ff001d1e60003004c013004c0130034040004c013004c210004c013004c0030074278004c013004c013004c2f0004c0031d20013004c10b1d2090c1d2015f1d2004d1e000130584013004c01d004c748004c8b2000c01d1de00131d20013004c01300740e902ec5e8004c013004c013463917444444404040383d3836141233320f0b302c27412a262523403f081f3110011d051e001b4b27) else (if i < 679 then 0x4d1d2004d056c000000001d013404d059404d013410f013404d013401d013404d013404d007404d013404d000d020d0e040009000501000000190e else 0x20607f0206063018d081820607d0246081820607d42470818080c050b040a0108000f09))) else (if i < 684 then (if i < 682 then (if i < 681 then 0x22e089822e063018c88b822e085824608b822e087824688b8080c050b040a0108000f09 else 0x24408ee244063423c09102440632246091024408e82478910080c050b040a0108000f09) else (if i < 683 then 0x40010004001018000101b0021005444e1e0008820800010004001000400300040010004001000400b022000300040050004001001c0880004001002c08800040010004001001400102200b80064001003c83c23a00070004070006c0010024001000407800040800004001022008800040110160013000400102800070220007005c007007499802c00a80004001000402a022000100043e0022000102603c40220001000441623a00010034090000c08800040c0007c00100e000100048d26a616b0068665f6565055e3a6600596463005759462c25201e593a54555334504e4b32362e292724110c1e174a48420f4341061b19400002156f39 else 0x400101a8001000c0d80f088e8000c001000400100540131de0968000406c20a0001000400120b8007001c00100840d8000400b000400300040d800140010004001001c0010360017002c001000400103e00d80004001000400500040d803f8019003c00103800f600040c8006c001002400100040ce00040d0000401d03600d800040110158001000400103a00070360007000400d0f100d8000400103b80010004050036000100043f623a0001007c0010108001000492200040f00fc00d8315d5c006a685967676558536700535166656062605e5b54234d304e4c462a4945432840241f1d1a160a3f203e3937153836132c0f0d0406006f39)) else (if i < 686 then (if i < 685 then 0x4c012004803c223a0108000c1200440001048011804801280480138000412004a805c00c0011000400100040030004120000486c20c000104c8003001c00100840010148050000443a10e0007013013a04800011e201200f00001004c0010004001003c0010074007000400100041202470001003400500048e80480001006c001000400b00040010024007000400500040010044001000400b000400b005c00100040230004001007c00100040010004019005400100040010004001520054004e6a4a004700690045686766320000002e0000001e666564186362611260435f0c5e405d2a5c5b5a24595450063e3c3a002b38256d38 else 0x108432054000305a015800041680580168060000105a01900004168009803824a88e8000400105a0001009c0010004001000c0070004021000404805a000105c016805a017805a019805200011dc01680fa0001004c0010004001003c001007400706203fe0f100070004001000484c2100001003400500048e805a00010094001000400b000400100240070004005000400100440010004001000400b005c00100040070004001007c00100040010004019005400100040010004001530057004f0028004c006a004a00690036000000320000001e69686718666564126348620c4430252a61605f245e5d460642403e00593c556d38) else (if i < 687 then 0x80020023a023c052021025c023808703c01e4023400a820c120000307d0850251002e001420026b0001080000108002400f1000123a02000150218000490a12109a800042000004001250000107b01e808000500034001082000107c0228088001300040010800001003c00700041f8000401b0004001000400900040010004011000400100040170014001000401f00040070800001005400500840010004001000400b000c224001c0010004854080023008b0007000400b000400100a40050004001000400100040010910019000c0010004007080000140007b003b7a727936000000320076002e0075002a746f734f004b0047726c6426476c41216b67661e3c64271945144d101c62170c605e5c06075901005855547d40 else 0xba02a825e000d0a408e80a402900a2029000042b80a8003000049a6000402b00040010004001007c0010a4029000041ea23a00660004278000402b001c00b002c0010b6029027a82e00ac00090bc00010004001000440800442c000040011e6000100ac2c80004866000429800040010004280000400100049d0001c29000642d0001402000040150a400070f0800120800210004001007493800040070004290001406c000401d0a40001001c001000400100040011100001004c7e40004028003c0010004452006c001000429000040016a00487746684100660062002a0061743f7370005f005d00567226715a6e225856703b36381c536f346e526c1e5f193e13500e4e08172f4b0430110c0002793e)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 0x4001007c08c00540da000c01321d0001002c005000400f174829205b00010004001000400111a03b000043c000040170004007001c3c00f2000700b43c0000402100040010f4000100040010f000010f6000700043c000048e800043c01d588e8000400100142000ea0009006c3c021600010044001000c001000400b00040010f0000100341200f0000100047b000040010f000010ee04a80f0001956525200514d50524c4c00494d4646441d1505464216401203113a3d39383633312f2d2c2b070f0a2725240023211a5b2f else 0x34001007c00100040150004021000c00527885e80004001279800b001c0010004001051000711a0001000400b11a00010004001000437811a0001006400111a0001003c5ec004c001000445800043c4000c001001446811a0001006c03123a0001000445c002400711a00010004460002c3c00004001000446811a08e8000400511a0007005c37c1f0000100bc47411a000100049da0004001050001f006400127780111ce81b8000400111c0880000400108a00012210001000400108b046861696000696769006664665b00005b640000605c4f57403b3544423f3b36343057542e2b27250b2253511c1a4d4b0f4a1b09180600131102496f39) else (if i < 691 then 0xf088e812a09cc09a09c417a03c012a08e812a049012a049800044a800044a812a074c12a08e426f04a812a09ce09a8015271800117a803308d8001005c9b412807d804c04b800049b61000001000400500040010034001078000104c803300440010004001005c0010004001007c00100cc00100dc0010004350224000112e823400040150004001000400100044a80004021000400100d4033000400526f800100e400100044a8000401912c000100b4001000400b004c00100040330004001003c001000400b000401924725a7139706d00356e6a00436c00003f6b6a693168570054005300526851671e6665640c4f6362064c3e6100604b5f185d485c2c2b452212192914753c else 0x1168150156011414c049c1460072158815c15204d80da04e807c04e0032856814a054815e04d213c052015205320d60278092853816c08e816603b6185036a1368418152015e14684ca054855016c855a11604f801c00c814a84c013405600ea8616142010815203b4132027a15c054807c849009203a8166854842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 694 then (if i < 693 then 0x24c025216405f2130000315e000115e000116a007e164837217002500a1858001f05f00dc05c20054007001c00115005a015e057814404ec140036016205b8001c2841f408241608001183000100145ba000400d00044200004010222000115e00010004011000400100040170004001000401f00040070004009000400115e0578000400100040010004001000457800040210004001006c007000400500000010004001000460e0004019000c00100ec001000400b004c00100040070004001003c001000400b000400324656f003664000032630000445f0000405e00002e5d7000596d6e005a6f6e6d1e546c6b0c536a5706504f56004c4a3d18493c2b29463e2a12143b22753c else 0x17403c423a05d0007c27017a0021001c4d000044d60004005000400100040010054001001c276000400117405d817b800103c05d027f0001172000100349fa17405d00004001008400500040010bf800122780010f0800117980010004013000403d0064001005c001178000103d8001003c8e800045d0000400100041d8001c732002c0071fa000b002400100045d0000400700442f800049b4174000100bc89800049f4004400100045d00004001006c9f200049b20004001005c5d000045d000040014d6e61005f6d496c5e6b67005b695900586866005300650051004566355230642a57254f064b20331c174426161e3e12100e3c0a0c04373d002c713a) else (if i < 695 then 0x23706a80e206ac0e386aa13c0003190000b190064019000491900013001c162002c64e13d063018800081a4000b1a60770059864a180069c1a6800b002c160002c0411a7800b003400b19d000b24c0604236000b193038a002c03f002c00b002c017002c00b002c04b002c007002c63419c001005906ae001c009002c00b192038c002c013002c00b002c00b002c640004c047002c00b006c007002c041190000b000c00b002c640002c045000c00b010c00b002c00b004c00b002c007002c00b000c00b002c00b002c00b24416f003c2f0000382900004b71000047700000346f6d0062006c00616d6c6b1e5f6a690c5d5a6806592f67005844651854522229535119124d4114753c else 0x118808019b011c19a04a418e028c199828a1a006280e0050007e04f8034867c198068019005ca14106581a0066a17e00860e186781a808e818f03be1a9038218a85fc1a0028818e862c020865c1a8866e11804fc0a380d0198862017206640ee86a619401181a003bc18b80841a2068007e84a00e103b818f868042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725))) else (if i < 700 then (if i < 698 then (if i < 697 then 0x6b8000401d1b60001000404d008400100040110004001000400500f400b000400d00140011c88a1014200032cc00201b4051400040010004950002c71a2d106301b400381b406b41ba06d02cc86ea1b4001d1b407180004a0a000400300640011b4000122b001d287801d007c015007400100040011b4000123a000123a07201b40a0800046e000040220004a1c0004a2400040010004b4600046d000040010004770000403a00040131bc001d1b200010004001000c0010004a12000401d003c6d00004a260004001000482000046d00004001740040713b54724d70006e006c006a0068004600670041006400621804003761605d365c5a025754245332501e4e192e0c4b2928134910460620433d002f7a3e else 0x908b20276013c26e00fc00609302ca0003005475000040010c6000114607c81ca059c1d4000107007a018e075000047b806483c60ce000128e00010014750013c00d0004750002c6c02c6074022e004f1d40b0200048f002e82cc2ae07a80004af40004011000400100840170004001000401f0004001001401b000400100409f0000404d0004001013c001000475000040010004001000c00100040012c58001006c04f00047500004019000c0010004001000400b004c0010004001000404f003c0010074001000400124726e0036700000326f00004e6e00004a6d00002e296b00656a690064636a681e605e5f0c5b595a065654500053464c183c434529443d2212193b14753c) else (if i < 699 then 0x400500040010004001148001f000c0011ed0001000401300047b000046d40004003000477000040011dc052422d077000048e81dc08e8000401d002ca4400040151dc001d05b00011dc00211b400010004001290864000040011dc08b0000401d0004a46290000d000477005a000f00040011dc001d0134001000416a000401100047701ed803d007401d000416e002c00100047701ec80050064001004e4d55004b2f5400554852000054475346444240143e394b2c3837280f25351f0a1c273605331929000e012018045b2f else 0x100040010004005015400d00043c00084053002c7b000048e81ec00012d38001001400114a000114d0001003c019000400b007c7b000040011f6000129b000129e82601dc0001000400300048e8004cb3e000402d00047b01bf08cc0144005000434e19207ea0004001000418c1bb0001000404d0004a5800b40011ec0001000423c2c787c000b4011000401500040011ec000300647b026400011ec07121ec0001000400123001a2000400f000402d26000011ec00131ec000105d00011ec098806c8001000402d6f6f6864626e616b6b006c6868006651382d5e1e00401900001303015d4819435b1440583a0f0b56393505322e0054534f4e09294d492b1d27231f743b)) else (if i < 702 then (if i < 701 then 0x1fe07fc1ae00031fc00011fc00011fc00011fc00571fc00011fc00011fc00011fc00621fc07f0150081e019881a1510618194006020700642a00a842a08818007c0012a1800100540010004057000c001002c01d00147f01fc08a000040010004001000c0010004001004400100048242080001016400100048e823a0001004c00100040010004001003c001015c0010004001006c00100040010004001016c0570004001000400b000400100040570004001003400500040210004019430000003f0000003c0000003a666500326652002e3527211e55686718516665125064630c4f62612a4b605f244a5e5d06495c5b00455a596d38 else 0x401f000400500047f00004001000485a0004088000401523e0820000c001000429200045500004820000482023a0001000457c208000b001482000040012080001000400723a00010004001004c8700004858000400f000c820006400700246d000048200004658000401122c001d20800072a20007007408a000400d002cacc000487200040012080a8a0a40001000401b2b3882000140210014001564d5300544b47005329544e504351454427424d46222d3d3c003b3a1e1d383317163530100f202e0a011925050c0b5b2f) else (if i < 703 then 0x1000400123a0001002c001017400d220001f0f008582010007007c015216091400140010004820216005f00048e800040010004001000c0012160001000400700040192160001000400100040012160001002c0010004001002c8580014001000485800048580004858273885800040072d380010004009226802100040012a400110c2000125300012b7000100042a2000c85800640070004558004c708003c8c000041d60004584006c102018489000046600004aa200042580b080010004b266b626c0069605f68675a686600005a655c005125571c5453504e164f4d48104947420e43413b083e302b25183a381f02361e062c34190026327039 else 0x89821c08e821c03900e603a02200560000c87010b88700c008700b589e201a49c2019c005203800520808e821c000516508702ce8870001470023206680014a982bb00b00014005001400700340050c5004123800902ae88702c380630014005008c878001400500140650014005001491021c000521c09fa001406b00140050f1094c00140090014005001c005001487000140050014005004c00500140052590005006c06d00140070014019003400500140050014005001400500140050014041000c005001c0050014005246400003c7100003828706f496e6100456d6c6b346a00005f0000005e6c6b6a1e695a680c592f58065255660050145b184f51422943323112414b22763c)))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 0x1000400101cc001002c0010074814003c00101cc00d232001f0cc801300548c0240000500040011b808b0000400100040010004003002c0010004001000400100048b0000400b000400101c400122c0005000400122c00730004001000400100048b022c000120806f023a0001262895c000400100048b022c0001006400123a0073000498822c08b001d48ca00443300084aa80004ae4000c8b0004c7700004570000448c003c8b001bc1aa000458c000467000748c200041a80004aaa0004ae66b5e6c00695c6a0067596866000059656100606256542f522d511250294f102621490a4c48460845203f1a63413e182d3d37023a36270019357039 else 0x1ec808821d016821c07b419006d422d029223a04ac0368578080054805b085e21608e81d407b015f082023a08b0022808e05a88721a00ac01d507702b102021ed829423a02901d485d21b408242b0887611a054c0a580d821683c6174085c0f08ac61fc012023a03c411a808c23e08e805b84a804903c01d588e842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725) else (if i < 707 then 0x245832e244091411e000323e08f8007491223e09640ca0962000c003007482423e000323a000316800031ff08f820808f8000c8e81da0688000c76023e001d000c00323e04b4000c00323e000325987582560af80ca89602bf001d0074003007407b000c003000c003000c00317688f81fe095c23e09001690003007407b2be8003000c04d01dc0030074003000c8f8000c01d000c003000c00300740030cb0003007404d000cafe000c003000c003000c0031760003000c00301e4003000c003000c003007400312c0003246600003c630000386f00004b6e0000476d0000343f0000616c00005e6f6e6d1e5d5c5a0c2f576c0654535100446b691841504d292b643112142a22753c else 0x29e00a02ba01782a60a681a60a182b802e22b00a600d005b808805b00610ad02a40ac01d40a581820a882b00aa828000c628a0ab01a808e82bc0a402d403202920a302b002b82c00a502820ac82d60b0811c06100bd80e82a80a381780ad80f68b622a001282b003d429c00ac2be0ac006784b807203c82c40ac042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 710 then (if i < 709 then 0x22800002b001802a008c018007402d002a02e00440028050008004800700a602800b801e0088015009802e00b0000800600680aa01a00c801f00800330022023802c02e002801e805a01c009c03280ae00e004c00b8008028803601600a400c80ce024001002e003400e800403000b80078040005003001f80b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0) else 0)) else 0) else 0) else 0))) else 0))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 19
  | 7 => 292
  | 8 => 365
  | 9 => 26
  | 10 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 25
  | 8 => 317
  | 9 => 682
  | 10 => 708
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+14*((h/a+d) % b))) &&& 16383

def rotateE (g : Nat) (ws : List Nat) := if g = 0 then ws else if g = 1 then setA ws else if g = 2 then setB ws else setA (setB ws)

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 232) (goal 232) s ws) : NatRun (mask 232) (goal 232) s (rotateE g ws) := by
  unfold rotateE

  split
  · exact h
  · split
    · exact runA h
    · split
      · exact runB h
      · exact runA (runB h)

def Z (s : Nat) := barrier 232 stateE nsE actionE sixE rotateE s
end PEqualNP.Outside.L_meta_982_aux.Case25Base

namespace PEqualNP.Outside.L_meta_982_aux.Case25Base
open PEqualNP.Outside.L_meta_982_aux.Base

theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 1 0 = true := by decide +kernel

theorem z4 : span (Z 4) 1 0 = true := h4y0

theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel

theorem z5 : span (Z 5) 1 0 = true := h5y0

theorem h6y0 : span (Z 6) 10 0 = true := by decide +kernel

theorem h6y1 : span (Z 6) 9 10 = true := by decide +kernel

theorem z6 : span (Z 6) 19 0 = true := (@span_join (Z 6) 10 0 9 h6y0 h6y1)

theorem h7y0 : span (Z 7) 10 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 10 10 = true := by decide +kernel

theorem h7y2 : span (Z 7) 10 20 = true := by decide +kernel

theorem h7y3 : span (Z 7) 10 30 = true := by decide +kernel

theorem h7y4 : span (Z 7) 10 40 = true := by decide +kernel

theorem h7y5 : span (Z 7) 10 50 = true := by decide +kernel

theorem h7y6 : span (Z 7) 10 60 = true := by decide +kernel

theorem h7y7 : span (Z 7) 10 70 = true := by decide +kernel

theorem h7y8 : span (Z 7) 10 80 = true := by decide +kernel

theorem h7y9 : span (Z 7) 10 90 = true := by decide +kernel

theorem h7y10 : span (Z 7) 10 100 = true := by decide +kernel

theorem h7y11 : span (Z 7) 10 110 = true := by decide +kernel

theorem h7y12 : span (Z 7) 10 120 = true := by decide +kernel

theorem h7y13 : span (Z 7) 10 130 = true := by decide +kernel

theorem h7y14 : span (Z 7) 10 140 = true := by decide +kernel

theorem h7y15 : span (Z 7) 10 150 = true := by decide +kernel

theorem h7y16 : span (Z 7) 10 160 = true := by decide +kernel

theorem h7y17 : span (Z 7) 10 170 = true := by decide +kernel

theorem h7y18 : span (Z 7) 10 180 = true := by decide +kernel

theorem h7y19 : span (Z 7) 10 190 = true := by decide +kernel

theorem h7y20 : span (Z 7) 10 200 = true := by decide +kernel

theorem h7y21 : span (Z 7) 10 210 = true := by decide +kernel

theorem h7y22 : span (Z 7) 10 220 = true := by decide +kernel

theorem h7y23 : span (Z 7) 10 230 = true := by decide +kernel

theorem h7y24 : span (Z 7) 10 240 = true := by decide +kernel

theorem h7y25 : span (Z 7) 10 250 = true := by decide +kernel

theorem h7y26 : span (Z 7) 10 260 = true := by decide +kernel

theorem h7y27 : span (Z 7) 10 270 = true := by decide +kernel

theorem h7y28 : span (Z 7) 10 280 = true := by decide +kernel

theorem h7y29 : span (Z 7) 2 290 = true := by decide +kernel

theorem z7 : span (Z 7) 292 0 = true := (@span_join (Z 7) 160 0 132 (@span_join (Z 7) 80 0 80 (@span_join (Z 7) 40 0 40 (@span_join (Z 7) 20 0 20 (@span_join (Z 7) 10 0 10 h7y0 h7y1) (@span_join (Z 7) 10 20 10 h7y2 h7y3)) (@span_join (Z 7) 20 40 20 (@span_join (Z 7) 10 40 10 h7y4 h7y5) (@span_join (Z 7) 10 60 10 h7y6 h7y7))) (@span_join (Z 7) 40 80 40 (@span_join (Z 7) 20 80 20 (@span_join (Z 7) 10 80 10 h7y8 h7y9) (@span_join (Z 7) 10 100 10 h7y10 h7y11)) (@span_join (Z 7) 20 120 20 (@span_join (Z 7) 10 120 10 h7y12 h7y13) (@span_join (Z 7) 10 140 10 h7y14 h7y15)))) (@span_join (Z 7) 80 160 52 (@span_join (Z 7) 40 160 40 (@span_join (Z 7) 20 160 20 (@span_join (Z 7) 10 160 10 h7y16 h7y17) (@span_join (Z 7) 10 180 10 h7y18 h7y19)) (@span_join (Z 7) 20 200 20 (@span_join (Z 7) 10 200 10 h7y20 h7y21) (@span_join (Z 7) 10 220 10 h7y22 h7y23))) (@span_join (Z 7) 40 240 12 (@span_join (Z 7) 20 240 20 (@span_join (Z 7) 10 240 10 h7y24 h7y25) (@span_join (Z 7) 10 260 10 h7y26 h7y27)) (@span_join (Z 7) 10 280 2 h7y28 h7y29))))

theorem h8y0 : span (Z 8) 10 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 10 10 = true := by decide +kernel

theorem h8y2 : span (Z 8) 10 20 = true := by decide +kernel

theorem h8y3 : span (Z 8) 10 30 = true := by decide +kernel

theorem h8y4 : span (Z 8) 10 40 = true := by decide +kernel

theorem h8y5 : span (Z 8) 10 50 = true := by decide +kernel

theorem h8y6 : span (Z 8) 10 60 = true := by decide +kernel

theorem h8y7 : span (Z 8) 10 70 = true := by decide +kernel

theorem h8y8 : span (Z 8) 10 80 = true := by decide +kernel

theorem h8y9 : span (Z 8) 10 90 = true := by decide +kernel

theorem h8y10 : span (Z 8) 10 100 = true := by decide +kernel

theorem h8y11 : span (Z 8) 10 110 = true := by decide +kernel

theorem h8y12 : span (Z 8) 10 120 = true := by decide +kernel

theorem h8y13 : span (Z 8) 10 130 = true := by decide +kernel

theorem h8y14 : span (Z 8) 10 140 = true := by decide +kernel

theorem h8y15 : span (Z 8) 10 150 = true := by decide +kernel

theorem h8y16 : span (Z 8) 10 160 = true := by decide +kernel

theorem h8y17 : span (Z 8) 10 170 = true := by decide +kernel

theorem h8y18 : span (Z 8) 10 180 = true := by decide +kernel

theorem h8y19 : span (Z 8) 10 190 = true := by decide +kernel

theorem h8y20 : span (Z 8) 10 200 = true := by decide +kernel

theorem h8y21 : span (Z 8) 10 210 = true := by decide +kernel

theorem h8y22 : span (Z 8) 10 220 = true := by decide +kernel

theorem h8y23 : span (Z 8) 10 230 = true := by decide +kernel

theorem h8y24 : span (Z 8) 10 240 = true := by decide +kernel

theorem h8y25 : span (Z 8) 10 250 = true := by decide +kernel

theorem h8y26 : span (Z 8) 10 260 = true := by decide +kernel

theorem h8y27 : span (Z 8) 10 270 = true := by decide +kernel

theorem h8y28 : span (Z 8) 10 280 = true := by decide +kernel

theorem h8y29 : span (Z 8) 10 290 = true := by decide +kernel

theorem h8y30 : span (Z 8) 10 300 = true := by decide +kernel

theorem h8y31 : span (Z 8) 10 310 = true := by decide +kernel

theorem h8y32 : span (Z 8) 10 320 = true := by decide +kernel

theorem h8y33 : span (Z 8) 10 330 = true := by decide +kernel

theorem h8y34 : span (Z 8) 10 340 = true := by decide +kernel

theorem h8y35 : span (Z 8) 10 350 = true := by decide +kernel

theorem h8y36 : span (Z 8) 5 360 = true := by decide +kernel

theorem z8 : span (Z 8) 365 0 = true := (@span_join (Z 8) 320 0 45 (@span_join (Z 8) 160 0 160 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 (@span_join (Z 8) 10 0 10 h8y0 h8y1) (@span_join (Z 8) 10 20 10 h8y2 h8y3)) (@span_join (Z 8) 20 40 20 (@span_join (Z 8) 10 40 10 h8y4 h8y5) (@span_join (Z 8) 10 60 10 h8y6 h8y7))) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 (@span_join (Z 8) 10 80 10 h8y8 h8y9) (@span_join (Z 8) 10 100 10 h8y10 h8y11)) (@span_join (Z 8) 20 120 20 (@span_join (Z 8) 10 120 10 h8y12 h8y13) (@span_join (Z 8) 10 140 10 h8y14 h8y15)))) (@span_join (Z 8) 80 160 80 (@span_join (Z 8) 40 160 40 (@span_join (Z 8) 20 160 20 (@span_join (Z 8) 10 160 10 h8y16 h8y17) (@span_join (Z 8) 10 180 10 h8y18 h8y19)) (@span_join (Z 8) 20 200 20 (@span_join (Z 8) 10 200 10 h8y20 h8y21) (@span_join (Z 8) 10 220 10 h8y22 h8y23))) (@span_join (Z 8) 40 240 40 (@span_join (Z 8) 20 240 20 (@span_join (Z 8) 10 240 10 h8y24 h8y25) (@span_join (Z 8) 10 260 10 h8y26 h8y27)) (@span_join (Z 8) 20 280 20 (@span_join (Z 8) 10 280 10 h8y28 h8y29) (@span_join (Z 8) 10 300 10 h8y30 h8y31))))) (@span_join (Z 8) 40 320 5 (@span_join (Z 8) 20 320 20 (@span_join (Z 8) 10 320 10 h8y32 h8y33) (@span_join (Z 8) 10 340 10 h8y34 h8y35)) h8y36))

theorem h9y0 : span (Z 9) 10 0 = true := by decide +kernel

theorem h9y1 : span (Z 9) 10 10 = true := by decide +kernel

theorem h9y2 : span (Z 9) 6 20 = true := by decide +kernel

theorem z9 : span (Z 9) 26 0 = true := (@span_join (Z 9) 20 0 6 (@span_join (Z 9) 10 0 10 h9y0 h9y1) h9y2)

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel

theorem z10 : span (Z 10) 1 0 = true := h10y0

theorem checkedE (s : Nat) (hs : s ≤ 10) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False := by
  have h10 : NatRun (mask 232) (goal 232) 10 xs517 := extend_run h hs
  have p : xs517.Perm (stateE 10 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 10 (by decide) 0 (by decide) (Run.perm p h10)
end PEqualNP.Outside.L_meta_982_aux.Case25Base

theorem PEqualNP.Outside.L_meta_982_aux.case25_base : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)) s → 11 ≤ s := PEqualNP.Outside.L_meta_982_aux.Case25Base.main517 PEqualNP.Outside.L_meta_982_aux.Case25Base.noRunFull

namespace PEqualNP.Outside.L_meta_982_aux
open PEqualNP.MetaComplexity

def case23 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def perm23 : Fin 7 → Fin 7 := ![0,1,2,3,6,4,5]

theorem case23_lower (s : ℕ) (h : HasCircuitSize 7 case23 s) : 11 ≤ s := by
  have hr := Relabel.relabel_size perm23 case23 s h
  have hf : (fun y : Fin 7 → Bool => case23 (y ∘ perm23)) = Case23Base.fG := by
    funext y
    revert y
    decide +kernel
  rw [hf] at hr
  exact case23_base s hr
#print axioms case23_lower

def case25 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def perm25 : Fin 7 → Fin 7 := ![0,2,3,5,1,4,6]

theorem case25_lower (s : ℕ) (h : HasCircuitSize 7 case25 s) : 11 ≤ s := by
  have hr := Relabel.relabel_size perm25 case25 s h
  have hf : (fun y : Fin 7 → Bool => case25 (y ∘ perm25)) = (fun x : Fin 7 → Bool => (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)) := by
    funext y
    revert y
    decide +kernel
  rw [hf] at hr
  exact case25_base s hr
#print axioms case25_lower
end PEqualNP.Outside.L_meta_982_aux
