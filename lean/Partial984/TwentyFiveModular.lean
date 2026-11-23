import TwentyFourModular

namespace Case24Finite
def low (X Y : Finset (Fin 7)) := (X ∪ Y) ∩ {1,2,3,5,6}
def bit (X Y U : Finset (Fin 7)) : Prop := X ⊆ U ∨ Y ⊆ U
def edge (U : Finset (Fin 7)) : Bool := decide (
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨ (1 ∈ U ∧ 2 ∈ U) ∨
  (3 ∈ U ∧ 4 ∈ U) ∨ (4 ∈ U ∧ 5 ∈ U) ∨ (4 ∈ U ∧ 6 ∈ U) ∨ (5 ∈ U ∧ 6 ∈ U))
def pool : Fin 14 → (Finset (Fin 7) × Finset (Fin 7)) := ![({0},{0,1}),({1},{1,2}),({2,4},{2,3,4}),({2,4},{2,4,5}),({2,5},{2,5,6}),({2,3,5},{1,2,3,5}),({0,5},{0,3,5}),({6},{5,6}),({0,4},{0,2,4}),({0,4},{0,4,6}),({0,4},{0,1,4}),({0,4},{0,4,5}),({1,3,5},{1,3,5,6}),({0,4},{0,3,4})]
def exceptional (X Y : Finset (Fin 7)) : Prop :=
  (X={0} ∧ Y={4}) ∨ (X={4} ∧ Y={0}) ∨ (X={0,3} ∧ Y={3,4}) ∨ (X={3,4} ∧ Y={0,3})
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 20000 in
theorem collision : ∀ X Y : Finset (Fin 7), ¬ X ⊆ Y → ¬ Y ⊆ X →
    exceptional X Y ∨ ∃ k : Fin 14,
      (pool k).1 \ low X Y = (pool k).2 \ low X Y ∧
      (bit X Y (pool k).1 ↔ bit X Y (pool k).2) ∧
      edge (pool k).1 ≠ edge (pool k).2 := by
  unfold exceptional bit low
  decide +kernel
end Case24Finite
namespace Relabel984

open PEqualNP.CircuitLowerBounds

def wire (τ : Fin 7 → Fin 7) (i : Nat) : Nat :=
  if h : i < 7 then (τ ⟨i,h⟩).val else i

def gate (τ : Fin 7 → Fin 7) (g : Gate) : Gate :=
  { g with inputs := g.inputs.map (wire τ) }

def circuit (τ : Fin 7 → Fin 7) (C : Circuit) : Circuit :=
  { gates := C.gates.map (gate τ), output := wire τ C.output }

theorem read_append (τ : Fin 7 → Fin 7) (x : Fin 7 → Bool)
    (s : List Bool) (i : Nat) :
    (List.ofFn x ++ s).getD (wire τ i) false =
      (List.ofFn (fun v => x (τ v)) ++ s).getD i false := by
  by_cases hi : i < 7
  · have ht : (τ ⟨i,hi⟩).val < 7 := (τ ⟨i,hi⟩).isLt
    simp only [wire,dif_pos hi,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using ht),
      List.getElem?_append_left (by simpa only [List.length_ofFn] using hi)]
    simp only [List.getElem?_ofFn,hi,ht,dif_pos,Option.getD_some]
  · simp only [wire,dif_neg hi,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega),
      List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem run_common_suffix (τ : Fin 7 → Fin 7) (x : Fin 7 → Bool) (gs : List Gate) :
    ∀ s : List Bool, ∃ t : List Bool,
      (gs.map (gate τ)).foldl step (List.ofFn x ++ s) = List.ofFn x ++ t ∧
      gs.foldl step (List.ofFn (fun v => x (τ v)) ++ s) =
        List.ofFn (fun v => x (τ v)) ++ t := by
  induction gs with
  | nil => intro s; exact ⟨s,rfl,rfl⟩
  | cons g gs ih =>
    intro s
    let z := g.op.eval (g.inputs.map (fun i =>
      (List.ofFn (fun v => x (τ v)) ++ s).getD i false))
    have hv : (gate τ g).op.eval ((gate τ g).inputs.map (fun i =>
        (List.ofFn x ++ s).getD i false)) = z := by
      unfold gate z
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact read_append τ x s i
    obtain ⟨t,hn,ho⟩ := ih (s ++ [z])
    refine ⟨t,?_,?_⟩
    · simp only [List.map_cons,List.foldl_cons,step,hv,List.append_assoc]
      exact hn
    · simp only [List.foldl_cons,step,List.append_assoc]
      exact ho

theorem eval_relabel (τ : Fin 7 → Fin 7) (C : Circuit) (x : Fin 7 → Bool) :
    (circuit τ C).eval (List.ofFn x) = C.eval (List.ofFn (fun v => x (τ v))) := by
  obtain ⟨t,hn,ho⟩ := run_common_suffix τ x C.gates []
  simp only [List.append_nil] at hn ho
  change ((C.gates.map (gate τ)).foldl step (List.ofFn x)).getD (wire τ C.output) false =
    (C.gates.foldl step (List.ofFn (fun v => x (τ v)))).getD C.output false
  rw [hn,ho]
  exact read_append τ x t C.output

theorem wires_relabel (τ : Fin 7 → Fin 7) (C : Circuit) (x : Fin 7 → Bool) (i : Nat) :
    ((circuit τ C).wires (List.ofFn x)).getD (wire τ i) false =
      (C.wires (List.ofFn (fun v => x (τ v)))).getD i false := by
  obtain ⟨t,hn,ho⟩ := run_common_suffix τ x C.gates []
  simp only [List.append_nil] at hn ho
  change ((C.gates.map (gate τ)).foldl step (List.ofFn x)).getD (wire τ i) false =
    (C.gates.foldl step (List.ofFn (fun v => x (τ v)))).getD i false
  rw [hn,ho]
  exact read_append τ x t i

theorem gate_wire_relabel (τ : Fin 7 → Fin 7) (C : Circuit) (x : Fin 7 → Bool) (j : Nat) :
    ((circuit τ C).wires (List.ofFn x)).getD (7 + j) false =
      (C.wires (List.ofFn (fun v => x (τ v)))).getD (7 + j) false := by
  have hh := wires_relabel τ C x (7+j)
  simpa only [wire,dif_neg (by omega : ¬7+j<7)] using hh

theorem size_relabel (τ : Fin 7 → Fin 7) (C : Circuit) : (circuit τ C).size = C.size := by
  simp [circuit,Circuit.size]

theorem monotone_relabel (τ : Fin 7 → Fin 7) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (circuit τ C) := by
  intro g hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop,hlen⟩ := hC g0 hg0
  exact ⟨hop,by simpa [gate] using hlen⟩

theorem cover_relabel (τ : Fin 7 → Fin 7) (C : Circuit) (A : Finset Nat)
    (op : GateOp)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = op → j ∈ A) :
    ∀ j g, (circuit τ C).gates[j]? = some g → g.op = op → j ∈ A := by
  intro j g hj hg
  change (C.gates.map (gate τ))[j]? = some g at hj
  rw [List.getElem?_map] at hj
  obtain ⟨g0,hg0,rfl⟩ := Option.map_eq_some_iff.mp hj
  exact hA j g0 hg0 hg

def identify : Fin 7 → Fin 7 := fun i => if i = 4 then 0 else i

theorem identify_eval (C : Circuit) (x : Fin 7 → Bool) :
    (circuit identify C).eval (List.ofFn x) =
      C.eval (List.ofFn (fun i => if i = 4 then x 0 else x i)) := by
  simpa [identify] using eval_relabel identify C x

end Relabel984
namespace PEqualNP.Outside.L_meta_984.orTheory
namespace Bridge24
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)]
def adjB (u v : Fin 7) : Bool := decide ((u,v) ∈ edges ∨ (v,u) ∈ edges)
def G : SimpleGraph (Fin 7) where
  Adj u v := adjB u v = true
  symm := ⟨by
    have hh : ∀ u v, adjB u v = true → adjB v u = true := by decide +kernel
    exact hh⟩
  loopless := ⟨by
    have hh : ∀ u, ¬adjB u u = true := by decide +kernel
    exact hh⟩
def H := G.deleteIncidenceSet 3

def edgeFun (x : Fin 7 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)
theorem edgeFun_detects : ∀ x : Fin 7 → Bool,
    edgeFun x = true ↔ ∃ u v, adjB u v = true ∧ x u = true ∧ x v = true := by decide +kernel

theorem detects_of_eval (C : Circuit) (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun x) : detects G C := by
  intro x
  rw [he]
  exact edgeFun_detects x

def par : Fin 7 → Fin 7 := ![2,0,1,3,6,4,5]
theorem sparseH : GraphInduction599.sparse H := by
  apply sparse_from_parent _ par
  intro u v huv
  obtain ⟨hadj,hu,hv⟩ := G.deleteIncidenceSet_adj.mp huv
  have hh : ∀ u v : Fin 7, adjB u v = true → u ≠ 3 → v ≠ 3 → u = par v ∨ v = par u := by decide +kernel
  exact hh u v hadj hu hv

theorem no_four : ∀ v a b c : Fin 7, G.Adj v a → G.Adj a b → G.Adj b c → G.Adj c v →
    a ≠ c → b ≠ v → False := by
  change ∀ v a b c : Fin 7, adjB v a = true → adjB a b = true → adjB b c = true → adjB c v = true →
    a ≠ c → b ≠ v → False
  decide +kernel

theorem noFour : GraphInduction599.noFour G := by
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
            exact no_four _ _ _ _ h1 h2 h3 h4 hnd.1.2.1 hnd.2.1.2
          | cons h5 p5 =>
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega

theorem edgesH : H.edgeSet.ncard = 6 := by
  let E : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(1,2),s(4,5),s(4,6),s(5,6)}
  have he : H.edgeSet = (E : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change H.Adj u v ↔ s(u,v) ∈ E
      rw [H,SimpleGraph.deleteIncidenceSet_adj]
      change (adjB u v = true ∧ u ≠ 3 ∧ v ≠ 3) ↔ s(u,v) ∈ E
      have hh : ∀ u v : Fin 7, (adjB u v = true ∧ u ≠ 3 ∧ v ≠ 3) ↔ s(u,v) ∈ E := by decide +kernel
      exact hh u v
  rw [he,Set.ncard_coe_finset]
  decide +kernel

theorem bestH : 5 ≤ best H := by
  have hh := best_bound_pseudoforest H sparseH
    (GraphInduction599.noFour_subgraph (G.deleteIncidenceSet_le 3) noFour)
  rw [edgesH] at hh
  omega

theorem or_lower6 (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun x)
    (hc : covers C A) : 6 ≤ A.card := by
  have h := detects_of_eval C he
  have on : ∃ x : Fin 7 → Bool, x 3 = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x 3 true)) = true := by
    refine ⟨fun i => decide (i = 0), by decide, ?_, ?_⟩ <;> rw [he] <;> decide +kernel
  have other : ∃ x : Fin 7 → Bool, x 3 = false ∧ C.eval (List.ofFn x) = true := by
    refine ⟨fun i => decide (i = 1 ∨ i = 2), by decide, ?_⟩
    rw [he]
    decide +kernel
  obtain ⟨C',B,hB,hM,hEq,hCov⟩ := Leaf599.restrict_one C 3 A hm hc on other
  have hb := best_le (show feasible H B.card from
    ⟨C',B,hM,PaidGraph599.after_restriction h hEq,hCov,rfl⟩)
  have hh := bestH
  omega

end Bridge24
namespace Case24Patch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- The small patch evaluator is copied from the checked 599 helper prefix.
   Keeping it here avoids private-name dependencies on imported packet modules. -/
private def readGate (g : Gate) (w : ℕ → Bool) : Bool := g.op.eval (g.inputs.map w)
private def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun wires g => wires ++ [readGate g (fun j => wires.getD j false)]) input

private theorem run_append (gs : List Gate) (g : Gate) (s : List Bool) :
    run (gs ++ [g]) s = run gs s ++ [readGate g (fun j => (run gs s).getD j false)] := by
  simp [run,List.foldl_append]

private theorem run_len (gs : List Gate) (s : List Bool) : (run gs s).length=s.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_append,ih,Nat.add_assoc]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

private theorem new_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs++[g]) x (n+gs.length) = readGate g (val gs x) := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append,←hl]
  simp

private theorem other_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w ≠ n+gs.length) : val (gs++[g]) x w = val gs x w := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append]
  by_cases hw : w < (run gs (List.ofFn x)).length
  · exact List.getD_append _ _ _ _ hw
  · rw [List.getD_eq_default _ _ (by simp [hl]; omega),List.getD_eq_default _ _ (by omega)]

private theorem val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w<n+a.length) :
    val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private theorem patch_val {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate) (z : Fin n → Bool)
    (same : ∀ (a : List Gate) (g : Gate), (∃ b, C.gates=(a++[g])++b) →
      readGate (f a.length g) (val a z)=readGate g (val a z))
    (gs : List Gate) (pre : ∃ b, C.gates=gs++b) (w : ℕ) :
    val (gs.mapIdx f) z w=val gs z w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => rfl
  | append_singleton gs g ih =>
    have pre' : ∃ b, C.gates=gs++b := by
      obtain ⟨b,hb⟩ := pre
      exact ⟨[g]++b,hb.trans (List.append_assoc _ _ _)⟩
    rw [List.mapIdx_concat]
    by_cases hw : w=n+gs.length
    · subst w
      have e : n+gs.length=n+(gs.mapIdx f).length := by simp
      rw [e,new_val,←e,new_val,show val (gs.mapIdx f) z=val gs z from funext (ih pre')]
      exact same gs g pre
    · rw [other_val _ _ _ (by simpa using hw),other_val _ _ _ hw]
      exact ih pre' w


theorem discard_or_as_and {n : ℕ} (C : Circuit) (A : Finset ℕ) (j : ℕ) (g : Gate)
    (hm : Monotone2 C) (cover : ∀ k h, C.gates[k]?=some h → h.op=.or → k∈A)
    (hg : C.gates[j]?=some g) (hop : g.op=.or)
    (l : List ℕ) (hl : l.length ≤ 2) (allowed : ∀ w ∈ l, w < n+j)
    (same : ∀ x : Fin n → Bool,
      GateOp.and.eval (l.map (fun w => (C.wires (List.ofFn x)).getD w false)) =
      (C.wires (List.ofFn x)).getD (n+j) false) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn x)) ∧
      (∀ k h, C'.gates[k]?=some h → h.op=.or → k∈A.erase j) ∧ (A.erase j).card+1=A.card := by
  have glob : ∀ x : Fin n → Bool, readGate ⟨.and,l⟩ (val C.gates x)=val C.gates x (n+j) := same
  let f (k : ℕ) (h : Gate) : Gate := if k=j then ⟨.and,l⟩ else h
  let C' : Circuit := ⟨C.gates.mapIdx f,C.output⟩
  have source (k : ℕ) (h : Gate) (hh : C'.gates[k]?=some h) :
      ∃ h', C.gates[k]?=some h' ∧ h=f k h' := by
    change (C.gates.mapIdx f)[k]?=some h at hh
    rw [List.getElem?_mapIdx] at hh
    cases h0 : C.gates[k]? with
    | none => simp [h0] at hh
    | some h' => exact ⟨h',rfl,by simpa [h0] using hh.symm⟩
  refine ⟨C',?_,by simp [C'],?_,?_,?_⟩
  · intro h hh
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hh
    obtain ⟨h',h0,rfl⟩ := source k h hk
    by_cases hk : k=j
    · simp [f,hk]; omega
    · simpa [f,hk] using hm h' (List.mem_of_getElem? h0)
  · intro x
    apply patch_val C f x _ C.gates ⟨[],by simp⟩ C.output
    intro a h ⟨b,hb⟩
    by_cases ha : a.length=j
    · have hout : val C.gates x (n+j)=readGate h (val a x) := by
        rw [hb,← ha,val_prefix (a++[h]) b x _ (by simp),new_val]
      have hdata : l.map (val a x)=l.map (val C.gates x) := by
        apply List.map_congr_left
        intro w hw
        have h := allowed w hw
        rw [hb,List.append_assoc]
        exact (val_prefix a ([_]++b) x w (by omega)).symm
      have hval : readGate ⟨.and,l⟩ (val a x)=readGate ⟨.and,l⟩ (val C.gates x) :=
        congrArg GateOp.and.eval hdata
      simpa [f,ha] using hval.trans ((glob x).trans hout)
    · simp [f,ha]
  · intro k h hh ha
    obtain ⟨h',h0,rfl⟩ := source k h hh
    by_cases hk : k=j
    · simp [f,hk] at ha
    · exact Finset.mem_erase.mpr ⟨hk,cover k h' h0 (by simpa [f,hk] using ha)⟩
  · exact Finset.card_erase_add_one (cover j g hg hop)

end Case24Patch
namespace Quotient24
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599

def edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4)]
def edgeFun (x : Fin 7 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

theorem or_lower6 (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun x)
    (hc : covers C A) : 6 ≤ A.card := by
  have on : ∃ x : Fin 7 → Bool, x 5 = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x 5 true)) = true := by
    refine ⟨fun i => decide (i = 0), by decide, ?_, ?_⟩ <;> rw [he] <;> decide +kernel
  have other : ∃ x : Fin 7 → Bool, x 5 = false ∧ C.eval (List.ofFn x) = true := by
    refine ⟨fun i => decide (i = 1 ∨ i = 2), by decide, ?_⟩
    rw [he]
    decide +kernel
  obtain ⟨C',B,hB,hM,hEq,hCov⟩ := Leaf599.restrict_one C 5 A hm hc on other
  have hd : detects Bowtie.G C' := by
    intro x
    rw [hEq,he]
    have hh : ∀ x : Fin 7 → Bool,
      edgeFun (Function.update x 5 false) = true ↔ ∃ u v, Bowtie.adjB u v = true ∧ x u = true ∧ x v = true := by decide +kernel
    exact hh x
  have hb := Bowtie.or_lower C' B hM hd hCov
  omega

theorem idempotent_first_or (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun x)
    (hc : covers C A) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = .or)
    (l : List ℕ) (hl : l.length ≤ 2) (hlt : ∀ w ∈ l, w < 7+j)
    (same : ∀ x : Fin 7 → Bool,
      GateOp.and.eval (l.map (fun w => (C.wires (List.ofFn x)).getD w false)) =
      (C.wires (List.ofFn x)).getD (7+j) false) : 7 ≤ A.card := by
  obtain ⟨D,hD,hlen,heq,hcover,hcard⟩ := Case24Patch.discard_or_as_and C A j g hm hc hg hop l hl hlt same
  have hb := or_lower6 D (A.erase j) hD (fun x => (heq x).trans (he x)) hcover
  omega

end Quotient24
namespace Bridge24
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical
/- The five degree-two deletions all have six edges and are pseudoforests. -/
def neigh : Fin 7 → Finset (Fin 7) :=
  ![{1,2,3},{0,2},{0,1},{0,4},{3,5,6},{4,6},{4,5}]

theorem neighbors (v : Fin 7) : G.neighborFinset v = neigh v := by
  apply Finset.ext
  intro u
  rw [G.mem_neighborFinset]
  have hh : ∀ v u : Fin 7, adjB v u = true ↔ u ∈ neigh v := by decide +kernel
  exact hh v u

theorem degrees (v : Fin 7) : G.degree v = ![3,2,2,2,3,2,2] v := by
  change (G.neighborFinset v).card = _
  rw [neighbors]
  fin_cases v <;> decide +kernel

theorem min_degree (v : Fin 7) : 2 ≤ G.degree v := by
  rw [degrees]
  fin_cases v <;> decide +kernel

theorem every_vertex_support (v : Fin 7) : v ∈ G.support := by
  apply (G.degree_pos_iff_mem_support v).mp
  have h := min_degree v
  omega

theorem min_degree_support : ∀ v ∈ G.support, 2 ≤ G.degree v := by
  intro v _
  exact min_degree v

def parDelete : Fin 7 → Fin 7 → Fin 7 :=
  ![![0,1,2,3,4,5,6], ![3,1,0,4,6,4,5], ![3,0,2,4,6,4,5],
    ![2,0,1,3,6,4,5], ![0,1,2,3,4,5,6], ![2,0,1,0,3,5,4], ![2,0,1,0,3,4,6]]

theorem sparse_delete (v : Fin 7) (hv : G.degree v = 2) :
    GraphInduction599.sparse (G.deleteIncidenceSet v) := by
  apply sparse_from_parent _ (parDelete v)
  intro a b hab
  obtain ⟨hadj,ha,hb⟩ := G.deleteIncidenceSet_adj.mp hab
  have hd : ![3,2,2,2,3,2,2] v = (2 : ℕ) := (degrees v).symm.trans hv
  have hh : ∀ v a b : Fin 7, ![3,2,2,2,3,2,2] v = (2 : ℕ) →
      adjB a b = true → a ≠ v → b ≠ v → a = parDelete v b ∨ b = parDelete v a := by
    decide +kernel
  exact hh v a b hd hadj ha hb

theorem edgesG : G.edgeSet.ncard = 8 := by
  have hc := GraphInduction599.count_after_delete G 3
  have hh : (G.deleteIncidenceSet 3).edgeSet.ncard = 6 := edgesH
  rw [hh, degrees] at hc
  norm_num at hc
  exact hc.symm

theorem edges_delete (v : Fin 7) (hv : G.degree v = 2) :
    (G.deleteIncidenceSet v).edgeSet.ncard = 6 := by
  have hc := GraphInduction599.count_after_delete G v
  rw [hv, edgesG] at hc
  omega

theorem delete_bound (v : Fin 7) (hv : G.degree v = 2) :
    5 ≤ GraphCircuit599.best (G.deleteIncidenceSet v) := by
  have hb := Extensions.best_bound_pseudoforest (G.deleteIncidenceSet v)
    (sparse_delete v hv)
    (GraphInduction599.noFour_subgraph (G.deleteIncidenceSet_le v) noFour)
  rw [edges_delete v hv] at hb
  omega


end Bridge24
namespace Final24
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions

def τ : Fin 7 → Fin 7 := ![0,1,2,5,0,3,4]
def support (x : Fin 7 → Bool) : Finset (Fin 7) := Finset.univ.filter (fun v => x v = true)
theorem mask_support (x : Fin 7 → Bool) : CycleCut599.mask (support x) = x := by
  funext i
  simp [CycleCut599.mask,support]

theorem quotient_eval (x : Fin 7 → Bool) : Bridge24.edgeFun (fun v => x (τ v)) = Quotient24.edgeFun x := by
  have hh : ∀ x : Fin 7 → Bool, Bridge24.edgeFun (fun v => x (τ v)) = Quotient24.edgeFun x := by decide +kernel
  exact hh x

theorem fold_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl Relabel984.step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (Relabel984.step w g) (by simp [Relabel984.step];omega)]
    exact List.getD_append _ _ _ _ hi

theorem input_read (C : Circuit) (x : Fin 7 → Bool) (i : Fin 7) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl Relabel984.step (List.ofFn x)).getD i.val false = x i
  rw [fold_read C.gates (List.ofFn x) i.val (by simpa using i.isLt)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dif_pos,Option.getD_some]

theorem collapsed_bit (X Y : Finset (Fin 7)) (h : Case24Finite.exceptional X Y) :
    ∃ l : List ℕ, l.length ≤ 2 ∧ (∀ w ∈ l, w < 7) ∧
      ∀ x : Fin 7 → Bool,
        GateOp.and.eval (l.map (fun w => (List.ofFn x).getD w false)) =
          decide (X ⊆ support (fun v => x (τ v)) ∨ Y ⊆ support (fun v => x (τ v))) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · refine ⟨[0],by decide,by decide,?_⟩
    decide +kernel
  · refine ⟨[0],by decide,by decide,?_⟩
    decide +kernel
  · refine ⟨[0,5],by decide,by decide,?_⟩
    decide +kernel
  · refine ⟨[0,5],by decide,by decide,?_⟩
    decide +kernel

theorem exceptional_or_bound (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = Bridge24.edgeFun x)
    (hc : covers C A) (p : ℕ) (g : Gate) (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (X Y : Finset (Fin 7)) (hex : Case24Finite.exceptional X Y)
    (bits : ∀ U : Finset (Fin 7),
      (C.wires (List.ofFn (CycleCut599.mask U))).getD (7+p) false = true ↔ CycleModule599.bit X Y U) :
    7 ≤ A.card := by
  let D := Relabel984.circuit τ C
  have hD := Relabel984.monotone_relabel τ C hm
  have hCov := Relabel984.cover_relabel τ C A GateOp.or hc
  have hEval : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x) = Quotient24.edgeFun x := by
    intro x
    rw [Relabel984.eval_relabel,he,quotient_eval]
  have hGate : D.gates[p]? = some (Relabel984.gate τ g) := by
    simp [D,Relabel984.circuit,List.getElem?_map,hg]
  obtain ⟨l,hl,hlt,hlval⟩ := collapsed_bit X Y hex
  apply Quotient24.idempotent_first_or D A hD hEval hCov p (Relabel984.gate τ g) hGate hop l hl
    (fun w hw => by have := hlt w hw; omega)
  intro x
  have hm : l.map (fun w => (D.wires (List.ofFn x)).getD w false) =
      l.map (fun w => (List.ofFn x).getD w false) := by
    apply List.map_congr_left
    intro w hw
    have hw7 := hlt w hw
    have hi := input_read D x ⟨w,hw7⟩
    change (D.wires (List.ofFn x)).getD w false = (List.ofFn x).getD w false
    rw [hi]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hw7,dif_pos,Option.getD_some]
  rw [hm,hlval,Relabel984.gate_wire_relabel]
  have hb := bits (support (fun v => x (τ v)))
  rw [mask_support] at hb
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq,CycleModule599.bit] using hb.symm)


theorem low_eq (X Y : Finset (Fin 7)) : low Bridge24.G X Y = Case24Finite.low X Y := by
  ext v
  have hv : Bridge24.G.degree v = 2 ↔ v ∈ ({1,2,3,5,6} : Finset (Fin 7)) := by
    rw [Bridge24.degrees]
    fin_cases v <;> decide
  simp only [low,Case24Finite.low,Finset.mem_filter,Finset.mem_inter,hv]

theorem edge_eq (U : Finset (Fin 7)) : CycleModule599.edgeAt Bridge24.G U ↔ Case24Finite.edge U = true := by
  have hh : ∀ U : Finset (Fin 7),
      (∃ a ∈ U, ∃ b ∈ U, Bridge24.adjB a b = true) ↔ Case24Finite.edge U = true := by
    decide +kernel
  exact hh U

theorem collision_or_exception (X Y : Finset (Fin 7)) (hx : ¬X ⊆ Y) (hy : ¬Y ⊆ X) :
    Case24Finite.exceptional X Y ∨ ∃ U V : Finset (Fin 7),
      (∀ i, i ∉ low Bridge24.G X Y → (i ∈ U ↔ i ∈ V)) ∧
      (CycleModule599.bit X Y U ↔ CycleModule599.bit X Y V) ∧
      ¬(CycleModule599.edgeAt Bridge24.G U ↔ CycleModule599.edgeAt Bridge24.G V) := by
  rcases Case24Finite.collision X Y hx hy with ex | ⟨k,hs,hb,he⟩
  · exact Or.inl ex
  · right
    refine ⟨(Case24Finite.pool k).1,(Case24Finite.pool k).2,?_,hb,?_⟩
    · intro i hi
      rw [low_eq] at hi
      have hh := congrArg (fun S => i ∈ S) hs
      simpa only [Finset.mem_sdiff,hi,not_false_eq_true,and_true] using iff_of_eq hh
    · intro hh
      apply he
      exact Bool.eq_iff_iff.mpr ((edge_eq _).symm.trans (hh.trans (edge_eq _)))

theorem collision_forces_seven (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = Bridge24.edgeFun x)
    (hc : covers C A) (p : ℕ) (X Y : Finset (Fin 7))
    (hp : ∀ v ∈ X ∪ Y, Leaf599.Charged C v p)
    (bits : ∀ U : Finset (Fin 7),
      (C.wires (List.ofFn (CycleCut599.mask U))).getD (7+p) false = true ↔ CycleModule599.bit X Y U)
    (collision : ∃ U V : Finset (Fin 7),
      (∀ i, i ∉ low Bridge24.G X Y → (i ∈ U ↔ i ∈ V)) ∧
      (CycleModule599.bit X Y U ↔ CycleModule599.bit X Y V) ∧
      ¬(CycleModule599.edgeAt Bridge24.G U ↔ CycleModule599.edgeAt Bridge24.G V)) : 7 ≤ A.card := by
  by_contra hn
  have hA : A.card ≤ 6 := by omega
  have h := Bridge24.detects_of_eval C he
  have only : ∀ v ∈ low Bridge24.G X Y, ∀ j, CycleCut599.releaseAt C.gates v j → j=p := by
    intro v hv j hj
    by_contra hne
    have hdeg := (Finset.mem_filter.mp hv).2
    have hh := PaidGraph599.double_saving hm h hc v hne
      ((CoreFacts599.charged_iff_release v j).mpr hj) (hp v (Finset.mem_filter.mp hv).1)
    have hb := Bridge24.delete_bound v hdeg
    omega
  obtain ⟨U,V,agree,hbit,hdiff⟩ := collision
  have same : (C.wires (List.ofFn (CycleCut599.mask U))).getD (7+p) false =
      (C.wires (List.ofFn (CycleCut599.mask V))).getD (7+p) false :=
    Bool.eq_iff_iff.mpr ((bits U).trans (hbit.trans (bits V).symm))
  have eq := CycleCut599.factor_gate (low Bridge24.G X Y) C p hm only
    (fun v _ => accepts_min_degree h Bridge24.min_degree_support (Bridge24.every_vertex_support v))
    (CycleCut599.mask U) (CycleCut599.mask V)
    (by intro i hi; apply Bool.eq_iff_iff.mpr; simpa [CycleCut599.mask] using agree i hi) same
  have spec (Q : Finset (Fin 7)) : C.eval (List.ofFn (CycleCut599.mask Q)) = true ↔
      CycleModule599.edgeAt Bridge24.G Q := by
    rw [h]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,hab⟩
    · rintro ⟨a,ha,b,hb,hab⟩
      exact ⟨a,b,hab,decide_eq_true ha,decide_eq_true hb⟩
  exact hdiff ((spec U).symm.trans ((iff_of_eq (congrArg (fun b => b=true) eq)).trans (spec V)))

theorem or_lower7 (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = Bridge24.edgeFun x)
    (hc : covers C A) : 7 ≤ A.card := by
  by_contra hn
  have hA : A.card ≤ 6 := by omega
  have h := Bridge24.detects_of_eval C he
  obtain ⟨pre,g,post,shape,ands,hor,hlen⟩ := Leaf599.first_or C 3 hm
    (one_bit h (Bridge24.every_vertex_support 3))
    (accepts_min_degree h Bridge24.min_degree_support (Bridge24.every_vertex_support 3))
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre++[g])++post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut599.prefix_decision (n:=7) pre post g ands hor hlen with copy | choice
    · obtain ⟨D,hD,hLen,hEq,hCov,hCard⟩ := Leaf599.discard_redundant_or
        ⟨(pre++[g])++post,out⟩ A pre.length g hm hc hj hor
        (CycleCut599.global_copy pre post g copy)
      have hb := Bridge24.or_lower6 D (A.erase pre.length) hD (fun x => (hEq x).trans (he x)) hCov
      omega
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      rcases collision_or_exception X Y hx hy with hex | hcollision
      · have hb := exceptional_or_bound ⟨(pre++[g])++post,out⟩ A hm he hc pre.length g hj hor X Y hex bits
        omega
      · have hb := collision_forces_seven ⟨(pre++[g])++post,out⟩ A hm he hc pre.length X Y
          (fun w hw => (CoreFacts599.charged_iff_release w pre.length).mpr (charges w hw)) bits hcollision
        omega

end Final24
end PEqualNP.Outside.L_meta_984.orTheory

namespace PEqualNP.Outside.L_meta_984.orTheory.Final24
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_984.orTheory.GraphCircuit599

theorem or_lower7_explicit (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
      (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)))
    (hc : covers C A) : 7 ≤ A.card := by
  apply or_lower7 C A hm _ hc
  intro x
  simpa [Bridge24.edgeFun,Bridge24.edges,Bool.or_assoc] using he x

end PEqualNP.Outside.L_meta_984.orTheory.Final24

namespace PEqualNP.Outside.L_meta_984_combine
open PEqualNP.CircuitLowerBounds

theorem ORProof24 : ORClaim24 := by
  intro C hm he
  have h := PEqualNP.Outside.L_meta_984.orTheory.Final24.or_lower7 C (orIndices C) hm
    (by intro x; simpa [PEqualNP.Outside.L_meta_984.orTheory.Bridge24.edgeFun,
      PEqualNP.Outside.L_meta_984.orTheory.Bridge24.edges, Bool.or_assoc] using he x)
    (fun j g hj hop => mem_opIndices C j g GateOp.or hj hop)
  simpa using h

theorem total24 : TotalClaim24 := conditional24 ORProof24

theorem twentyfive_totals : TotalClaim0 ∧ TotalClaim1 ∧ TotalClaim2 ∧ TotalClaim3 ∧ TotalClaim4 ∧ TotalClaim5 ∧ TotalClaim6 ∧ TotalClaim7 ∧ TotalClaim8 ∧ TotalClaim9 ∧ TotalClaim10 ∧ TotalClaim11 ∧ TotalClaim12 ∧ TotalClaim13 ∧ TotalClaim14 ∧ TotalClaim15 ∧ TotalClaim16 ∧ TotalClaim17 ∧ TotalClaim18 ∧ TotalClaim21 ∧ TotalClaim22 ∧ TotalClaim23 ∧ TotalClaim24 ∧ TotalClaim25 ∧ TotalClaim26 :=
  ⟨total0, total1, total2, total3, total4, total5, total6, total7, total8, total9, total10, total11, total12, total13, total14, total15, total16, total17, total18, total21, total22, total23, total24, total25, total26⟩

theorem conditional_missing_six
    (missing19 : TotalClaim19)
    (missing20 : TotalClaim20)
    (missing27 : TotalClaim27)
    (missing28 : TotalClaim28)
    (missing29 : TotalClaim29)
    (missing30 : TotalClaim30) :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact assemble_exact total0 total1 total2 total3 total4 total5 total6 total7 total8 total9 total10 total11 total12 total13 total14 total15 total16 total17 total18 missing19 missing20 total21 total22 total23 total24 total25 total26 missing27 missing28 missing29 missing30

end PEqualNP.Outside.L_meta_984_combine
#print axioms PEqualNP.Outside.L_meta_984_combine.twentyfive_totals
#print axioms PEqualNP.Outside.L_meta_984_combine.conditional_missing_six
