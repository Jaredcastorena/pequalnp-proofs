import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_196_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem alias_keep (gs : List Gate) : ∀ (j a h : ℕ) (w : List Bool),
    h < w.length + j →
    (run (gs.set j ⟨GateOp.or, [a]⟩) w).getD h false =
      (run gs w).getD h false := by
  induction gs with
  | nil => intro j a h w hh; rfl
  | cons g gs ih =>
    intro j a h w hh
    cases j with
    | zero =>
      have hw : h < w.length := by omega
      rw [run_keep _ _ h hw, run_keep _ _ h hw]
    | succ j =>
      change (run (gs.set j ⟨GateOp.or, [a]⟩) (step w g)).getD h false =
        (run gs (step w g)).getD h false
      exact ih j a h (step w g) (by simp [step]; omega)

theorem alias_eq (gs : List Gate) : ∀ (j a h : ℕ) (w : List Bool),
    gs[j]? = some ⟨GateOp.or, [a,h]⟩ → h < w.length + j →
    (run gs w).getD h false = false →
    run (gs.set j ⟨GateOp.or, [a]⟩) w = run gs w := by
  induction gs with
  | nil => intro j a h w hg hh hf; simp at hg
  | cons g gs ih =>
    intro j a h w hg hh hf
    cases j with
    | zero =>
      have he : g = ⟨GateOp.or, [a,h]⟩ := by simpa using hg
      subst g
      have hw : w.getD h false = false := by
        rw [← run_keep (⟨GateOp.or, [a,h]⟩ :: gs) w h (by omega)]
        exact hf
      change run gs (step w ⟨GateOp.or, [a]⟩) =
        run gs (step w ⟨GateOp.or, [a,h]⟩)
      congr 1
      simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, id_eq, hw, Bool.or_false]
    | succ j =>
      change run (gs.set j ⟨GateOp.or, [a]⟩) (step w g) =
        run gs (step w g)
      exact ih j a h (step w g) (by simpa using hg)
        (by simp [step]; omega) hf

theorem append_or (gs : List Gate) (w : List Bool) (o h : ℕ) :
    (run (gs ++ [⟨GateOp.or, [o,h]⟩]) w).getD (w.length + gs.length) false =
      ((run gs w).getD o false || (run gs w).getD h false) := by
  have he : run (gs ++ [⟨GateOp.or, [o,h]⟩]) w =
      step (run gs w) ⟨GateOp.or, [o,h]⟩ := by
    simp [run, List.foldl_append]
  rw [he, ← run_length gs w]
  simp [step, GateOp.eval]

end PEqualNP.Outside.L_meta_196_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_196_aux

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hg hh x herr
  change (run (C.gates.set j ⟨GateOp.or, [a]⟩ ++ [⟨GateOp.or, [C.output,h]⟩])
    (List.ofFn x)).getD (n + C.gates.length) false ≠ f x at herr
  have hl : (List.ofFn x).length + (C.gates.set j ⟨GateOp.or, [a]⟩).length =
      n + C.gates.length := by simp
  rw [← hl, append_or] at herr
  have hk := alias_keep C.gates j a h (List.ofFn x) (by simpa using hh)
  change (run (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x)).getD h false =
    (C.wires (List.ofFn x)).getD h false at hk
  rw [hk] at herr
  by_cases he : circuitFun n C x = f x
  · right
    cases hv : (C.wires (List.ofFn x)).getD h false with
    | false =>
      have ha := alias_eq C.gates j a h (List.ofFn x) hg (by simpa using hh) hv
      rw [ha, hv, Bool.or_false] at herr
      exact (herr he).elim
    | true =>
      refine ⟨rfl, ?_⟩
      rw [hv, Bool.or_true] at herr
      cases hf : f x with
      | false => rfl
      | true => exact (herr hf.symm).elim
  · exact Or.inl he
