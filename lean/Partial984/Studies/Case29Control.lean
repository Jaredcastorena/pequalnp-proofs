import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_984.denseRemaining
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C29 : Circuit := ⟨[
    ⟨.or, [0,4]⟩,
    ⟨.or, [3,4]⟩,
    ⟨.or, [1,3]⟩,
    ⟨.and, [7,9]⟩,
    ⟨.or, [0,1]⟩,
    ⟨.or, [2,10]⟩,
    ⟨.and, [11,12]⟩,
    ⟨.or, [5,8]⟩,
    ⟨.and, [2,5]⟩,
    ⟨.and, [6,14]⟩,
    ⟨.or, [15,16]⟩,
    ⟨.or, [13,17]⟩], 18⟩
def edges29 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)]
def edge29 (x : Fin 7 → Bool) : Bool := edges29.any (fun e => x e.1 && x e.2)

theorem monotone29 : Monotone2 C29 := by simp [Monotone2,C29]
theorem size29 : C29.size = 12 := by rfl
def isAnd : GateOp → Bool | .and => true | _ => false
def isOr : GateOp → Bool | .or => true | _ => false

theorem and_count29 : C29.gates.countP (fun g => isAnd g.op) = 4 := by decide
theorem or_count29 : C29.gates.countP (fun g => isOr g.op) = 8 := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem eval29 : ∀ x : Fin 7 → Bool, C29.eval (List.ofFn x) = edge29 x := by decide +kernel

def badPair : Fin 7 → Bool := fun v => decide (v=3 ∨ v=4)
theorem first_and_unsound_pair :
    (C29.wires (List.ofFn badPair)).getD 10 false = true ∧ edge29 badPair = false := by decide

theorem first_and_not_star :
    (C29.wires (List.ofFn (fun v : Fin 7 => decide (v=0 ∨ v=1)))).getD 10 false = true ∧
    (C29.wires (List.ofFn (fun v : Fin 7 => decide (v=0 ∨ v=3)))).getD 10 false = true ∧
    (C29.wires (List.ofFn (fun v : Fin 7 => decide (v=1 ∨ v=4)))).getD 10 false = true ∧
    ¬∃ center : Fin 7, (center=0 ∨ center=1) ∧ (center=0 ∨ center=3) ∧ (center=1 ∨ center=4) := by decide
end PEqualNP.Outside.L_meta_984.denseRemaining
#print axioms PEqualNP.Outside.L_meta_984.denseRemaining.eval29
#print axioms PEqualNP.Outside.L_meta_984.denseRemaining.first_and_not_star
