import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1343_family

open PEqualNP.CircuitLowerBounds

abbrev F := (Fin 11 → Bool) → Bool

def inputs : List F := (fun _ => true) :: List.ofFn (fun i x => x i)

def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.any (fun f => f x)

def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x && v x)) ∧ good G

theorem member {G : List F} {f : F} (h : f ∈ G ++ inputs) : cl G f :=
  ⟨[f], by simpa using h, by simp⟩

theorem cl_congr {G : List F} {u v : F} (hu : cl G u) (h : ∀ x, v x = u x) :
    cl G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩

theorem cl_new (G : List F) (f : F) : cl (f :: G) f := member (by simp)

theorem cl_mono {G : List F} {f : F} (g : F) (h : cl G f) : cl (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩

theorem cl_false (G : List F) : cl G (fun _ => false) := ⟨[], by simp, by simp⟩

theorem cl_true (G : List F) : cl G (fun _ => true) := member (by simp [inputs])

theorem cl_or {G : List F} {a b : F} (ha : cl G a) (hb : cl G b) :
    cl G (fun x => a x || b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

theorem gate_or (G : List ((Fin 11 → Bool) → Bool)) (f : ℕ → (Fin 11 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_false G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gate_and (G : List ((Fin 11 → Bool) → Bool)) (f : ℕ → (Fin 11 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, cl_true G, cl_true G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 11 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 11 → Bool) → Bool :=
  fun x => (W gs x).getD k false

theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 11 → Bool) :
    (W gs x).length = 11 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 11 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 11 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 11 + gs.length
  · rw [if_pos hk]
    show (W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, hk]
  · rw [if_neg hk]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (11 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 11
  · apply cl_congr (member (G := []) (f := fun x => x ⟨k,hk⟩) (by interval_cases k <;> simp [inputs]))
    intro x
    interval_cases k <;> rfl
  · apply cl_congr (cl_false [])
    intro x
    simp [wf, W, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk]

theorem inv (A : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ G, good G ∧ G.length ≤ (A.filter (fun j => j < gs.length)).card ∧
      ∀ k, cl G (wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp, fun k => base k⟩
  | append_singleton gs g ih =>
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho => hA j g' (by
        have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.getElem?_append_left hjl]; exact hj) ho)
    obtain ⟨hop, hl⟩ := hm g (by simp)
    rcases hop with hop | hop
    · obtain ⟨u, v, hu, hv, he⟩ := gate_and G (wf gs) hw g.inputs hl
      have hmem : gs.length ∈ A := hA gs.length g (by simp) hop
      refine ⟨(fun x => GateOp.eval GateOp.and (g.inputs.map fun i => wf gs i x)) :: G,
        ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have hsub : insert gs.length (A.filter (fun j => j < gs.length))
            ⊆ A.filter (fun j => j < (gs ++ [g]).length) := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, List.length_append, List.length_cons,
            List.length_nil] at hj ⊢
          rcases hj with rfl | ⟨h1, h2⟩
          · exact ⟨hmem, by omega⟩
          · exact ⟨h1, by omega⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at hc
        simp only [List.length_cons]
        omega
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 11 + gs.length
        · rw [if_pos hk]; exact cl_new _ _
        · rw [if_neg hk]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 11 + gs.length
        · rw [if_pos hk]; exact gate_or G (wf gs) hw g.inputs hl
        · rw [if_neg hk]; exact hw k


/-- Every seven-input monotone circuit compresses to at most its number of AND gates,
with free OR combinations and both constants. This is the semantic stage of a
finite-selector reduction; no selector-certificate bridge is asserted here. -/
theorem circuit_compression (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ G, good G ∧ G.length ≤ A.card ∧ cl G (fun x => C.eval (List.ofFn x)) := by
  obtain ⟨G, hG, hlen, hw⟩ := inv A C.gates hm hA
  refine ⟨G, hG, hlen.trans (Finset.card_filter_le _ _), ?_⟩
  exact hw C.output

/-- Any free OR closure is a single finite selector on the available wires. -/
theorem cl_choice {G : List F} {w : F} (h : cl G w) :
    ∃ b : Fin (G ++ inputs).length → Bool, ∀ x,
      w x = (List.ofFn (fun i : Fin (G ++ inputs).length =>
        b i && (G ++ inputs).get i x)).any id := by
  classical
  obtain ⟨S, hS, hw⟩ := h
  refine ⟨fun i => decide ((G ++ inputs).get i ∈ S), ?_⟩
  intro x
  rw [hw x]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_ofFn, Bool.and_eq_true, decide_eq_true_eq, id_eq]
  constructor
  · rintro ⟨f, hf, hfx⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (hS f hf)
    refine ⟨true, ⟨i, ?_⟩, rfl⟩
    rw [hi]
    simp [hf, hfx]
  · rintro ⟨_, ⟨i, rfl⟩, hi⟩
    have hh : (G ++ inputs).get i ∈ S ∧ (G ++ inputs).get i x = true := by
      simpa using hi
    exact ⟨_, hh.1, hh.2⟩


/-- The free-OR selector can be represented by a bit-vector with one bit per wire. -/
theorem cl_bitvec {G : List F} {w : F} (h : cl G w) :
    ∃ b : BitVec (G ++ inputs).length, ∀ x,
      w x = (List.ofFn (fun i : Fin (G ++ inputs).length =>
        b[i.val] && (G ++ inputs).get i x)).any id := by
  obtain ⟨b, hb⟩ := cl_choice h
  let v : BitVec (G ++ inputs).length :=
    (BitVec.ofBoolListLE (List.ofFn b)).cast (by simp)
  refine ⟨v, ?_⟩
  intro x
  rw [hb x]
  congr 1
  congr 1
  funext i
  have hi : i.val < G.length + inputs.length := by simpa using i.isLt
  simp [v, ← BitVec.getLsbD_eq_getElem, hi]


/- The false-side code argument follows the mathematical projection method in
checked Outside/L_meta_906, here proved directly for semantic OR closures. -/
def joinInput (x y : Fin 11 → Bool) : Fin 11 → Bool := fun i => x i || y i

theorem cl_merge {G : List F} {x y : Fin 11 → Bool}
    (hmerge : ∀ f ∈ G, f x = false → f y = false → f (joinInput x y) = false)
    {w : F} (hw : cl G w) (hx : w x = false) (hy : w y = false) :
    w (joinInput x y) = false := by
  obtain ⟨S, hS, he⟩ := hw
  rw [he] at hx hy ⊢
  simp only [List.any_eq_false, Bool.not_eq_true] at hx hy ⊢
  intro f hf
  rcases List.mem_append.mp (hS f hf) with hg | hi
  · exact hmerge f hg (hx f hf) (hy f hf)
  · simp only [inputs, List.mem_cons, List.mem_ofFn] at hi
    rcases hi with rfl | ⟨i, rfl⟩
    · exact hx _ hf
    · simp [joinInput, hx _ hf, hy _ hf]

theorem good_code {G : List F} (hG : good G) :
    ∃ code : (Fin 11 → Bool) → (Fin G.length → Bool),
      ∀ x y, code x = code y →
        ∀ f ∈ G, f x = false → f y = false → f (joinInput x y) = false := by
  induction G with
  | nil => exact ⟨fun _ i => Fin.elim0 i, by simp⟩
  | cons g G ih =>
    obtain ⟨⟨u,v,hu,hv,hg⟩,hG⟩ := hG
    obtain ⟨code,hcode⟩ := ih hG
    refine ⟨fun x => Fin.cases (u x) (code x), ?_⟩
    intro x y hxy f hf hfx hfy
    have hu_eq : u x = u y := congrFun hxy 0
    have hc : code x = code y := by
      funext i
      exact congrFun hxy i.succ
    rcases List.mem_cons.mp hf with rfl | hf
    · rw [hg] at hfx hfy ⊢
      cases hux : u x with
      | false =>
        have huy : u y = false := hu_eq.symm.trans hux
        rw [cl_merge (hcode x y hc) hu hux huy]
        rfl
      | true =>
        have huy : u y = true := hu_eq.symm.trans hux
        have hvx : v x = false := by simpa [hux] using hfx
        have hvy : v y = false := by simpa [huy] using hfy
        rw [cl_merge (hcode x y hc) hv hvx hvy]
        simp
    · exact hcode x y hc f hf hfx hfy

theorem family_bound {G : List F} (hG : good G) {w : F} (hw : cl G w)
    {m : ℕ} (M : Fin m → (Fin 11 → Bool))
    (h0 : ∀ i, w (M i) = false)
    (h1 : ∀ i j, i ≠ j → w (joinInput (M i) (M j)) = true) :
    m ≤ 2^G.length := by
  obtain ⟨code,hcode⟩ := good_code hG
  have hinj : Function.Injective (fun i => code (M i)) := by
    intro i j h
    by_contra hn
    have hz := cl_merge (hcode (M i) (M j) h) hw (h0 i) (h0 j)
    rw [h1 i j hn] at hz
    contradiction
  have h := Fintype.card_le_of_injective _ hinj
  simpa using h

theorem circuit_family_bound (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    {m : ℕ} (M : Fin m → (Fin 11 → Bool))
    (h0 : ∀ i, C.eval (List.ofFn (M i)) = false)
    (h1 : ∀ i j, i ≠ j → C.eval (List.ofFn (joinInput (M i) (M j))) = true) :
    m ≤ 2^A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  exact (family_bound hG hw M h0 h1).trans (Nat.pow_le_pow_right (by omega) hlen)


def edgeFun (E : List (Fin 11 × Fin 11)) (x : Fin 11 → Bool) : Bool :=
  E.any (fun e => x e.1 && x e.2)

def edges : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def rows : Fin 24 → Finset (Fin 11) := ![{0,1,2,3},{0,2,3,4},{0,1,3,5},{0,3,4,5},{0,1,2,6},{0,2,4,6},{0,1,5,6},{0,4,5,6},{0,1,2,7},{0,2,4,7},{0,1,5,7},{0,4,5,7},{0,2,3,8},{0,2,6,8},{0,2,7,8},{1,2,3,9},{2,3,4,9},{1,2,6,9},{2,4,6,9},{1,3,5,10},{1,5,7,10},{3,8,10},{7,8,10},{1,3,9,10}]
def assignments (i : Fin 24) (v : Fin 11) : Bool := decide (v ∈ rows i)
theorem rows_zero : ∀ i, edgeFun edges (assignments i) = false := by decide +kernel
theorem rows_join : ∀ i j, i ≠ j → edgeFun edges (joinInput (assignments i) (assignments j)) = true := by decide +kernel

theorem and_lower (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 11 → Bool, C.eval (List.ofFn x) = edgeFun edges x) :
    5 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments
    (fun i => (he _).trans (rows_zero i))
    (fun i j hn => (he _).trans (rows_join i j hn))
  by_contra hn
  have hc : A.card ≤ 4 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega
def upper : Circuit := ⟨[⟨GateOp.or,[9,10]⟩,⟨GateOp.and,[0,11]⟩,⟨GateOp.or,[4,8]⟩,⟨GateOp.and,[1,13]⟩,⟨GateOp.or,[6,7]⟩,⟨GateOp.and,[3,15]⟩,⟨GateOp.or,[2,8]⟩,⟨GateOp.or,[9,17]⟩,⟨GateOp.and,[5,18]⟩,⟨GateOp.or,[6,9]⟩,⟨GateOp.and,[7,20]⟩,⟨GateOp.or,[4,9]⟩,⟨GateOp.and,[8,22]⟩,⟨GateOp.or,[2,4]⟩,⟨GateOp.or,[6,24]⟩,⟨GateOp.and,[10,25]⟩,⟨GateOp.or,[12,14]⟩,⟨GateOp.or,[16,27]⟩,⟨GateOp.or,[19,28]⟩,⟨GateOp.or,[21,29]⟩,⟨GateOp.or,[23,30]⟩,⟨GateOp.or,[26,31]⟩],32⟩
theorem upper_mono : PEqualNP.MetaComplexity.Monotone2 upper := by
  simp [PEqualNP.MetaComplexity.Monotone2, upper]
theorem upper_size : upper.size = 22 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem upper_eval : ∀ x : Fin 11 → Bool, upper.eval (List.ofFn x) = edgeFun edges x := by decide +kernel
end PEqualNP.Outside.L_meta_1343_family
#print axioms PEqualNP.Outside.L_meta_1343_family.and_lower
#print axioms PEqualNP.Outside.L_meta_1343_family.upper_eval
