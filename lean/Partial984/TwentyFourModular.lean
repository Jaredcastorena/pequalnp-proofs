import PacketBase
import SharedSixCases

namespace PEqualNP.Outside.L_meta_984.orTheory
namespace Cycle8
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def edges : Fin 1 → List (Fin 7 × Fin 7) := ![[(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)]]
def adjB (i : Fin 1) (u v : Fin 7) : Bool := decide ((u,v) ∈ edges i ∨ (v,u) ∈ edges i)
def G (i : Fin 1) : SimpleGraph (Fin 7) where
  Adj u v := adjB i u v = true
  symm := ⟨by
    have hh : ∀ i u v, adjB i u v = true → adjB i v u = true := by decide +kernel
    exact hh i⟩
  loopless := ⟨by
    have hh : ∀ i u, ¬adjB i u u = true := by decide +kernel
    exact hh i⟩
def E : Fin 1 → Finset (Sym2 (Fin 7)) := ![{s(0,1),s(0,2),s(1,3),s(2,4),s(3,5),s(4,6),s(5,6)}]

theorem edge_count (i : Fin 1) : (G i).edgeSet.ncard = 7 := by
  have he : (G i).edgeSet = (E i : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change adjB i u v = true ↔ s(u,v) ∈ E i
      have hh : ∀ i u v, adjB i u v = true ↔ s(u,v) ∈ E i := by decide +kernel
      exact hh i u v
  rw [he,Set.ncard_coe_finset]
  have hh : ∀ i, (E i).card = 7 := by decide +kernel
  exact hh i

theorem no_four : ∀ i : Fin 1, ∀ v a b c : Fin 7,
    (G i).Adj v a → (G i).Adj a b → (G i).Adj b c → (G i).Adj c v →
    a ≠ c → b ≠ v → False := by
  change ∀ i : Fin 1, ∀ v a b c : Fin 7,
    adjB i v a = true → adjB i a b = true → adjB i b c = true → adjB i c v = true →
    a ≠ c → b ≠ v → False
  decide +kernel

theorem noFour (i : Fin 1) : GraphInduction599.noFour (G i) := by
  intro v c hc hlen
  cases c with
  | nil => simp at hlen
  | cons h1 p1 =>
    cases p1 with
    | nil => simp at hlen
    | cons h2 p2 =>
      cases p2 with
      | nil => simp at hlen
      | cons h3 p3 =>
        cases p3 with
        | nil => simp at hlen
        | cons h4 p4 =>
          cases p4 with
          | nil =>
            have hnd := hc.support_nodup
            simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
              List.tail_cons,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
            exact no_four i _ _ _ _ h1 h2 h3 h4 hnd.1.2.1 hnd.2.1.2
          | cons h5 p5 =>
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega

def par : Fin 1 → Fin 7 → Fin 7 := ![![2,0,4,1,6,3,5]]

theorem sparse (i : Fin 1) : GraphInduction599.sparse (G i) := by
  apply sparse_from_parent _ (par i)
  have hh : ∀ i : Fin 1, ∀ u v : Fin 7,
      adjB i u v = true → u = par i v ∨ v = par i u := by decide +kernel
  exact hh i

theorem best_bound (i : Fin 1) : (G i).edgeSet.ncard ≤ best (G i) + 1 :=
  best_bound_pseudoforest _ (sparse i) (noFour i)

theorem or_lower_detects (i : Fin 1) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects (G i) C) (hc : covers C A) : 6 ≤ A.card := by
  have hb := best_le (show feasible (G i) A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound i
  rw [edge_count] at hh
  omega

def edgeFun (i : Fin 1) (x : Fin 7 → Bool) : Bool :=
  (edges i).any (fun e => x e.1 && x e.2)

theorem edgeFun_detects : ∀ i : Fin 1, ∀ x : Fin 7 → Bool,
    edgeFun i x = true ↔ ∃ u v, adjB i u v = true ∧ x u = true ∧ x v = true := by decide +kernel

theorem or_lower (i : Fin 1) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun i x)
    (hc : ∀ j g, C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) : 6 ≤ A.card := by
  apply or_lower_detects i C A hm ?_ hc
  intro x
  rw [he x]
  exact edgeFun_detects i x

end Cycle8
end PEqualNP.Outside.L_meta_984.orTheory

namespace PEqualNP.Outside.L_meta_984_combine
open PEqualNP.CircuitLowerBounds

theorem ORProof1 : ORClaim1 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (0 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total1 : TotalClaim1 := conditional1 ORProof1

theorem ORProof2 : ORClaim2 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (0 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total2 : TotalClaim2 := conditional2 ORProof2

theorem ORProof3 : ORClaim3 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (1 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total3 : TotalClaim3 := conditional3 ORProof3

theorem ORProof4 : ORClaim4 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (2 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total4 : TotalClaim4 := conditional4 ORProof4

theorem ORProof5 : ORClaim5 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (3 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total5 : TotalClaim5 := conditional5 ORProof5

theorem ORProof6 : ORClaim6 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (4 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total6 : TotalClaim6 := conditional6 ORProof6

theorem ORProof7 : ORClaim7 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.or_lower (5 : Fin 6) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edgeFun, PEqualNP.Outside.L_meta_984.orTheory.PseudoforestRoutes.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total7 : TotalClaim7 := conditional7 ORProof7

theorem ORProof9 : ORClaim9 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (1 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total9 : TotalClaim9 := conditional9 ORProof9

theorem ORProof10 : ORClaim10 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (2 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total10 : TotalClaim10 := conditional10 ORProof10

theorem ORProof11 : ORClaim11 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (3 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total11 : TotalClaim11 := conditional11 ORProof11

theorem ORProof12 : ORClaim12 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (4 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total12 : TotalClaim12 := conditional12 ORProof12

theorem ORProof13 : ORClaim13 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (5 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total13 : TotalClaim13 := conditional13 ORProof13

theorem ORProof14 : ORClaim14 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (6 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total14 : TotalClaim14 := conditional14 ORProof14

theorem ORProof15 : ORClaim15 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.or_lower_eval (7 : Fin 8) C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.BowtieLeaves.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total15 : TotalClaim15 := conditional15 ORProof15

theorem ORProof18 : ORClaim18 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.OneHub18.or_lower_eval C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.OneHub18.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total18 : TotalClaim18 := conditional18 ORProof18

theorem ORProof26 : ORClaim26 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.Windmill.or_lower_eval C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.Windmill.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total26 : TotalClaim26 := conditional26 ORProof26

theorem total16 : TotalClaim16 := by
  intro C hm he
  exact PEqualNP.Outside.L_meta_984.LeafTotal.route16 C hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.LeafTotal.target16] using he x)

theorem total22 : TotalClaim22 := by
  intro C hm he
  exact PEqualNP.Outside.L_meta_984.LeafTotal.route22 C hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.LeafTotal.target22] using he x)

theorem total0 : TotalClaim0 := by
  intro C hm he
  apply PEqualNP.Outside.L_meta_982_aux.case0_lower C.size
  refine ⟨C, PEqualNP.Outside.L_meta_984.LeafTotal.mono_fanin C hm, le_rfl, ?_⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_982_aux.case0] using he x

theorem ORProof8 : ORClaim8 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.Cycle8.or_lower (0 : Fin 1)
    C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.Cycle8.edgeFun,
      PEqualNP.Outside.L_meta_984.orTheory.Cycle8.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total8 : TotalClaim8 := conditional8 ORProof8
theorem total17 : TotalClaim17 := by
  intro C hm he
  apply PEqualNP.Outside.L_meta_982_aux.case17_lower C.size
  refine ⟨C, PEqualNP.Outside.L_meta_984.LeafTotal.mono_fanin C hm, le_rfl, ?_⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_982_aux.case17] using he x

theorem total21 : TotalClaim21 := by
  intro C hm he
  apply PEqualNP.Outside.L_meta_982_aux.shard21_lower C.size
  refine ⟨C, PEqualNP.Outside.L_meta_984.LeafTotal.mono_fanin C hm, le_rfl, ?_⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_982_aux.shard21] using he x

theorem total23 : TotalClaim23 := by
  intro C hm he
  apply PEqualNP.Outside.L_meta_982_aux.case23_lower C.size
  refine ⟨C, PEqualNP.Outside.L_meta_984.LeafTotal.mono_fanin C hm, le_rfl, ?_⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_982_aux.case23] using he x

theorem total25 : TotalClaim25 := by
  intro C hm he
  apply PEqualNP.Outside.L_meta_982_aux.case25_lower C.size
  refine ⟨C, PEqualNP.Outside.L_meta_984.LeafTotal.mono_fanin C hm, le_rfl, ?_⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_982_aux.case25] using he x

theorem twentyfour_totals : TotalClaim0 ∧ TotalClaim1 ∧ TotalClaim2 ∧ TotalClaim3 ∧ TotalClaim4 ∧ TotalClaim5 ∧ TotalClaim6 ∧ TotalClaim7 ∧ TotalClaim8 ∧ TotalClaim9 ∧ TotalClaim10 ∧ TotalClaim11 ∧ TotalClaim12 ∧ TotalClaim13 ∧ TotalClaim14 ∧ TotalClaim15 ∧ TotalClaim16 ∧ TotalClaim17 ∧ TotalClaim18 ∧ TotalClaim21 ∧ TotalClaim22 ∧ TotalClaim23 ∧ TotalClaim25 ∧ TotalClaim26 :=
  ⟨total0, total1, total2, total3, total4, total5, total6, total7, total8, total9, total10, total11, total12, total13, total14, total15, total16, total17, total18, total21, total22, total23, total25, total26⟩

/-- Exactly the posted31-case conclusion, with precisely seven unproved cases explicit. -/
theorem conditional_missing_seven
    (missing19 : TotalClaim19)
    (missing20 : TotalClaim20)
    (missing24 : TotalClaim24)
    (missing27 : TotalClaim27)
    (missing28 : TotalClaim28)
    (missing29 : TotalClaim29)
    (missing30 : TotalClaim30) :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact assemble_exact total0 total1 total2 total3 total4 total5 total6 total7 total8 total9 total10 total11 total12 total13 total14 total15 total16 total17 total18 missing19 missing20 total21 total22 total23 missing24 total25 total26 missing27 missing28 missing29 missing30

end PEqualNP.Outside.L_meta_984_combine
#print axioms PEqualNP.Outside.L_meta_984_combine.twentyfour_totals
#print axioms PEqualNP.Outside.L_meta_984_combine.conditional_missing_seven
