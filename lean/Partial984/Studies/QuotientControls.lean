import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_984.denseQuotients
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isAnd : GateOp → Bool | .and => true | _ => false
def isOr : GateOp → Bool | .or => true | _ => false

def C0 : Circuit := ⟨[⟨.or, [0,5]⟩,⟨.and, [4,5]⟩,⟨.and, [5,7]⟩,⟨.or, [1,8]⟩,⟨.or, [4,6]⟩,⟨.or, [2,3]⟩,⟨.or, [10,11]⟩,⟨.and, [9,12]⟩,⟨.and, [0,11]⟩,⟨.or, [13,14]⟩], 15⟩
def edges0 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(4,5)]
theorem monotone0 : Monotone2 C0 := by simp [Monotone2,C0]
theorem size0 : C0.size = 10 := by rfl
theorem and_count0 : C0.gates.countP (fun g => isAnd g.op) = 4 := by decide
theorem or_count0 : C0.gates.countP (fun g => isOr g.op) = 6 := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem eval0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edges0.any (fun e => x e.1 && x e.2) := by decide +kernel

def C1 : Circuit := ⟨[⟨.or, [0,1]⟩,⟨.and, [0,0]⟩,⟨.or, [2,3]⟩,⟨.and, [4,6]⟩,⟨.or, [0,2]⟩,⟨.or, [1,5]⟩,⟨.and, [0,8]⟩,⟨.or, [9,12]⟩,⟨.and, [10,11]⟩,⟨.or, [13,14]⟩], 15⟩
def edges1 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,5)]
theorem monotone1 : Monotone2 C1 := by simp [Monotone2,C1]
theorem size1 : C1.size = 10 := by rfl
theorem and_count1 : C1.gates.countP (fun g => isAnd g.op) = 4 := by decide
theorem or_count1 : C1.gates.countP (fun g => isOr g.op) = 6 := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem eval1 : ∀ x : Fin 6 → Bool, C1.eval (List.ofFn x) = edges1.any (fun e => x e.1 && x e.2) := by decide +kernel

def original28 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]
def original29 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)]
def merge28 : Fin 7 → Fin 6 := ![0,1,2,1,3,4,5]
def merge29 : Fin 7 → Fin 6 := ![0,1,2,3,4,5,0]
theorem quotient28 : ∀ x : Fin 6 → Bool,
 original28.any (fun e => x (merge28 e.1) && x (merge28 e.2)) = edges0.any (fun e => x e.1 && x e.2) := by decide +kernel
theorem quotient29 : ∀ x : Fin 6 → Bool,
 original29.any (fun e => x (merge29 e.1) && x (merge29 e.2)) = edges1.any (fun e => x e.1 && x e.2) := by decide +kernel
end PEqualNP.Outside.L_meta_984.denseQuotients
#print axioms PEqualNP.Outside.L_meta_984.denseQuotients.eval0
#print axioms PEqualNP.Outside.L_meta_984.denseQuotients.eval1
#print axioms PEqualNP.Outside.L_meta_984.denseQuotients.quotient28
#print axioms PEqualNP.Outside.L_meta_984.denseQuotients.quotient29
