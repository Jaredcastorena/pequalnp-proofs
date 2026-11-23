import Mathlib
import PEqualNP.Defs

/-! Adapted by Boolean duality from accepted L-meta-597 semantic closure argument.
The input-wire default stays false. Free OR closure includes true as an explicit constant.
This file proves only compression into semantic OR closures, not the984 lower bound. -/

namespace Eliminate984

abbrev X := Fin 7 → Bool
abbrev F := X → Bool

def inputs : List F := (fun _ => true) :: List.ofFn (fun i x => x i)
def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.any (fun f => f x)
def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x && v x)) ∧ good G

def pin (p : Fin 7) (x : X) : X := Function.update x p true
def single (p : Fin 7) : X := fun q => decide (q = p)
def res (p : Fin 7) (f : F) : F := fun x => f (pin p x)
def invariant (p : Fin 7) (f : F) : Prop := ∀ x, res p f x = f x

theorem member {G : List F} {f : F} (h : f ∈ G ++ inputs) : cl G f :=
  ⟨[f], by simpa using h, by simp⟩
theorem cl_congr {G : List F} {u v : F} (hu : cl G u) (h : ∀ x, v x = u x) : cl G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩
theorem cl_false (G : List F) : cl G (fun _ => false) := ⟨[], by simp, by simp⟩
theorem cl_true (G : List F) : cl G (fun _ => true) := member (by simp [inputs])
theorem cl_new (G : List F) (g : F) : cl (g :: G) g := member (by simp)
theorem cl_mono {G : List F} {f : F} (g : F) (h : cl G f) : cl (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩
theorem cl_or {G : List F} {a b : F} (ha : cl G a) (hb : cl G b) :
    cl G (fun x => a x || b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

theorem cl_any (G : List F) (S : List F) (hS : ∀ f ∈ S, cl G f) :
    cl G (fun x => S.any (fun f => f x)) := by
  induction S with
  | nil => simpa using cl_false G
  | cons f S ih =>
    have hf := hS f (by simp)
    have ht := ih (fun g hg => hS g (by simp [hg]))
    simpa using cl_or hf ht

theorem inputs_res (p : Fin 7) (H : List F) (f : F) (hf : f ∈ inputs) : cl H (res p f) := by
  simp only [inputs, List.mem_cons, List.mem_ofFn] at hf
  rcases hf with rfl | ⟨i, rfl⟩
  · change cl H (fun _ => true)
    exact cl_true H
  · by_cases hi : i = p
    · subst i
      apply cl_congr (cl_true H)
      intro x
      simp [res, pin]
    · apply cl_congr (member (G := H) (f := fun x => x i)
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))))
      intro x
      simp [res, pin, hi]

theorem map_cl (p : Fin 7) {G H : List F}
    (hm : ∀ g ∈ G, cl H (res p g)) {w : F} (hw : cl G w) : cl H (res p w) := by
  obtain ⟨S, hs, he⟩ := hw
  have hall : ∀ f ∈ S, cl H (res p f) := by
    intro f hf
    rcases List.mem_append.mp (hs f hf) with hg | hi
    · exact hm f hg
    · exact inputs_res p H f hi
  have hh := cl_any H (S.map (res p)) (by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hall g hg)
  apply cl_congr hh
  intro x
  change w (pin p x) = _
  rw [he]
  simp only [List.any_map]
  rfl

theorem input_monotone (f : F) (hf : f ∈ inputs) : Monotone f := by
  simp only [inputs, List.mem_cons, List.mem_ofFn] at hf
  rcases hf with rfl | ⟨i, rfl⟩
  · intro x y h; exact le_rfl
  · intro x y h; exact h i

theorem cl_monotone {G : List F} (hG : ∀ g ∈ G, Monotone g)
    {w : F} (hw : cl G w) : Monotone w := by
  obtain ⟨S, hs, he⟩ := hw
  intro x y hxy
  cases hx : w x with
  | false => exact Bool.false_le _
  | true =>
    have hax : S.any (fun f => f x) = true := (he x).symm.trans hx
    obtain ⟨f, hf, hfx⟩ := List.any_eq_true.mp hax
    have hmono : Monotone f := (List.mem_append.mp (hs f hf)).elim (hG f) (input_monotone f)
    have hfy : f y = true := le_antisymm (Bool.le_true _) (by simpa [hfx] using hmono hxy)
    have hy : w y = true := (he y).trans (List.any_eq_true.mpr ⟨f, hf, hfy⟩)
    simp [hy]

theorem good_monotone {G : List F} (hG : good G) : ∀ g ∈ G, Monotone g := by
  induction G with
  | nil => simp
  | cons g G ih =>
    obtain ⟨⟨u,v,hu,hv,he⟩,ht⟩ := hG
    have hm := ih ht
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · intro x y hxy
      rw [he x, he y]
      have h1 := cl_monotone hm hu hxy
      have h2 := cl_monotone hm hv hxy
      cases hux : u x <;> cases hvx : v x <;> cases huy : u y <;> cases hvy : v y <;>
        simp_all
    · exact hm f hf

theorem true_after_pin (p : Fin 7) {G : List F} (hG : good G) {w : F}
    (hw : cl G w) (ht : w (single p) = true) : ∀ x, res p w x = true := by
  intro x
  have hs : single p ≤ pin p x := by
    intro q
    by_cases hq : q = p
    · subst q; simp [single, pin]
    · simp [single, pin, hq]
  have hh := cl_monotone (good_monotone hG) hw hs
  exact le_antisymm (Bool.le_true _) (by simpa [ht, res] using hh)

theorem closure_false_invariant_of_false_members (p : Fin 7) {G : List F}
    (hG : ∀ g ∈ G, g (single p) = false → invariant p g) {w : F} (hw : cl G w)
    (hz : w (single p) = false) : invariant p w := by
  obtain ⟨S, hs, he⟩ := hw
  have hsfalse : S.any (fun f => f (single p)) = false := (he _).symm.trans hz
  have hi : ∀ f ∈ S, invariant p f := by
    intro f hf
    have hfzero : f (single p) = false := by
      cases hh : f (single p) with
      | false => rfl
      | true =>
        have ht : S.any (fun f => f (single p)) = true := List.any_eq_true.mpr ⟨f,hf,hh⟩
        rw [hsfalse] at ht
        contradiction
    rcases List.mem_append.mp (hs f hf) with hg | hb
    · exact hG f hg hfzero
    · simp only [inputs, List.mem_cons, List.mem_ofFn] at hb
      rcases hb with rfl | ⟨i, rfl⟩
      · contradiction
      · have hip : i ≠ p := by
          intro h
          subst i
          simp [single] at hfzero
        intro x
        simp [res, pin, hip]
  intro x
  change w (pin p x) = w x
  rw [he, he]
  apply Bool.eq_iff_iff.2
  constructor
  · intro hh
    obtain ⟨f,hf,ht⟩ := List.any_eq_true.mp hh
    apply List.any_eq_true.mpr
    exact ⟨f,hf,(hi f hf x).symm.trans ht⟩
  · intro hh
    obtain ⟨f,hf,ht⟩ := List.any_eq_true.mp hh
    apply List.any_eq_true.mpr
    exact ⟨f,hf,(hi f hf x).trans ht⟩

theorem closure_false_invariant (p : Fin 7) {G : List F}
    (hG : ∀ g ∈ G, invariant p g) {w : F} (hw : cl G w)
    (hz : w (single p) = false) : invariant p w :=
  closure_false_invariant_of_false_members p (fun g hg _ => hG g hg) hw hz

theorem elimination_or_invariant (p : Fin 7) {G : List F} (hG : good G) :
    (∃ H, good H ∧ H.length + 1 ≤ G.length ∧
      ∀ w, cl G w → cl H (res p w)) ∨ (∀ g ∈ G, invariant p g) := by
  induction G with
  | nil => right; simp
  | cons g G ih =>
    obtain ⟨⟨u,v,hu,hv,he⟩,ht⟩ := hG
    rcases ih ht with ⟨H,hH,hlen,hmap⟩ | hinv
    · left
      refine ⟨res p g :: H, ?_, ?_, ?_⟩
      · exact ⟨⟨res p u, res p v, hmap u hu, hmap v hv, fun x => he (pin p x)⟩,hH⟩
      · simp only [List.length_cons]
        omega
      · intro w hw
        apply map_cl p (H := res p g :: H) ?_ hw
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact cl_new H (res p f)
        · exact cl_mono (res p g) (hmap f (member (List.mem_append.mpr (Or.inl hf))))
    · have hmap : ∀ w, cl G w → cl G (res p w) := by
        intro w hw
        apply map_cl p ?_ hw
        intro f hf
        exact cl_congr (member (List.mem_append.mpr (Or.inl hf))) (hinv f hf)
      by_cases hue : u (single p) = true
      · left
        have hgcl : cl G (res p g) := by
          apply cl_congr (hmap v hv)
          intro x
          change g (pin p x) = v (pin p x)
          rw [he, show u (pin p x) = true from true_after_pin p ht hu hue x]
          simp
        refine ⟨G,ht,by simp,?_⟩
        intro w hw
        apply map_cl p ?_ hw
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hgcl
        · exact hmap f (member (List.mem_append.mpr (Or.inl hf)))
      · by_cases hve : v (single p) = true
        · left
          have hgcl : cl G (res p g) := by
            apply cl_congr (hmap u hu)
            intro x
            change g (pin p x) = u (pin p x)
            rw [he, show v (pin p x) = true from true_after_pin p ht hv hve x]
            simp
          refine ⟨G,ht,by simp,?_⟩
          intro w hw
          apply map_cl p ?_ hw
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hgcl
          · exact hmap f (member (List.mem_append.mpr (Or.inl hf)))
        · right
          have huz : u (single p) = false := by cases h : u (single p) <;> simp_all
          have hvz : v (single p) = false := by cases h : v (single p) <;> simp_all
          have hui := closure_false_invariant p hinv hu huz
          have hvi := closure_false_invariant p hinv hv hvz
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · intro x
            change f (pin p x) = f x
            rw [he,he,show u (pin p x) = u x from hui x,
              show v (pin p x) = v x from hvi x]
          · exact hinv f hf

theorem eliminate_essential_vertex (p : Fin 7) {G : List F} (hG : good G)
    {f : F} (hf : cl G f) (hz : f (single p) = false)
    (hess : ∃ x, res p f x ≠ f x) :
    ∃ H, good H ∧ H.length + 1 ≤ G.length ∧ cl H (res p f) := by
  rcases elimination_or_invariant p hG with ⟨H,hH,hlen,hm⟩ | hi
  · exact ⟨H,hH,hlen,hm f hf⟩
  · obtain ⟨x,hx⟩ := hess
    exact (hx (closure_false_invariant p hi hf hz x)).elim

inductive Trace : List F → Type
  | nil : Trace []
  | cons {G : List F} (g u v : F) (hu : cl G u) (hv : cl G v)
      (he : ∀ x, g x = (u x && v x)) (tail : Trace G) : Trace (g :: G)

theorem trace_nonempty {G : List F} (hG : good G) : Nonempty (Trace G) := by
  induction G with
  | nil => exact ⟨Trace.nil⟩
  | cons g G ih =>
    obtain ⟨⟨u,v,hu,hv,he⟩,ht⟩ := hG
    obtain ⟨t⟩ := ih ht
    exact ⟨Trace.cons g u v hu hv he t⟩

noncomputable def traceOfGood {G : List F} (hG : good G) : Trace G :=
  Classical.choice (trace_nonempty hG)

theorem Trace.good {G : List F} (t : Trace G) : good G := by
  induction t with
  | nil => trivial
  | cons g u v hu hv he tail ih => exact ⟨⟨u,v,hu,hv,he⟩,ih⟩

def Trace.events (p : Fin 7) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.events p + if u (single p) || v (single p) then 1 else 0

theorem Trace.pin_all_events (p : Fin 7) {G : List F} (t : Trace G) :
    ∃ H : List F, Eliminate984.good H ∧ H.length + t.events p ≤ G.length ∧
      ∀ w, cl G w → cl H (res p w) := by
  induction t with
  | nil =>
    refine ⟨[],trivial,by simp [Trace.events],?_⟩
    intro w hw
    exact map_cl p (by simp) hw
  | @cons G g u v hu hv he tail ih =>
    obtain ⟨H,hH,hlen,hm⟩ := ih
    by_cases hue : u (single p) = true
    · have hgcl : cl H (res p g) := by
        apply cl_congr (hm v hv)
        intro x
        change g (pin p x) = v (pin p x)
        rw [he,show u (pin p x) = true from true_after_pin p tail.good hu hue x]
        simp
      refine ⟨H,hH,?_,?_⟩
      · simp only [Trace.events,hue,Bool.true_or,ite_true,List.length_cons]
        omega
      · intro w hw
        apply map_cl p ?_ hw
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hgcl
        · exact hm f (member (List.mem_append.mpr (Or.inl hf)))
    · by_cases hve : v (single p) = true
      · have hgcl : cl H (res p g) := by
          apply cl_congr (hm u hu)
          intro x
          change g (pin p x) = u (pin p x)
          rw [he,show v (pin p x) = true from true_after_pin p tail.good hv hve x]
          simp
        refine ⟨H,hH,?_,?_⟩
        · simp only [Trace.events,hve,Bool.or_true,ite_true,List.length_cons]
          omega
        · intro w hw
          apply map_cl p ?_ hw
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hgcl
          · exact hm f (member (List.mem_append.mpr (Or.inl hf)))
      · have huz : u (single p) = false := by cases h : u (single p) <;> simp_all
        have hvz : v (single p) = false := by cases h : v (single p) <;> simp_all
        refine ⟨res p g :: H,?_,?_,?_⟩
        · exact ⟨⟨res p u,res p v,hm u hu,hm v hv,fun x => he (pin p x)⟩,hH⟩
        · simp [Trace.events,huz,hvz,List.length_cons]
          omega
        · intro w hw
          apply map_cl p ?_ hw
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact cl_new H (res p f)
          · exact cl_mono (res p g) (hm f (member (List.mem_append.mpr (Or.inl hf))))

def Trace.asym (p : Fin 7) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.asym p + if u (single p) = v (single p) then 0 else 1

def Trace.sides (p : Fin 7) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.sides p + (if u (single p) then 1 else 0) + (if v (single p) then 1 else 0)

theorem Trace.zero_asym_invariant (p : Fin 7) {G : List F} (t : Trace G) :
    t.asym p = 0 → ∀ w, cl G w → w (single p) = false → invariant p w := by
  induction t with
  | nil =>
    intro _ w hw hz
    exact closure_false_invariant p (by simp) hw hz
  | @cons G g u v hu hv he tail ih =>
    intro hz w hw hwz
    have htail : tail.asym p = 0 := by
      simp only [Trace.asym] at hz
      omega
    have heq : u (single p) = v (single p) := by
      by_contra hn
      simp [Trace.asym,hn] at hz
    apply closure_false_invariant_of_false_members p ?_ hw hwz
    intro f hf hfz
    rcases List.mem_cons.mp hf with rfl | hf
    · have hvz : v (single p) = false := by
        have hh := he (single p)
        rw [heq,Bool.and_self] at hh
        exact hh.symm.trans hfz
      have huz : u (single p) = false := heq.trans hvz
      have hui := ih htail u hu huz
      have hvi := ih htail v hv hvz
      intro x
      change f (pin p x) = f x
      rw [he,he,show u (pin p x) = u x from hui x,
        show v (pin p x) = v x from hvi x]
    · exact ih htail f (member (List.mem_append.mpr (Or.inl hf))) hfz

theorem Trace.sides_asym (p : Fin 7) {G : List F} (t : Trace G) :
    t.sides p + t.asym p = 2 * t.events p := by
  induction t with
  | nil => rfl
  | cons g u v hu hv he tail ih =>
    cases hx : u (single p) <;> cases hy : v (single p) <;>
      simp [Trace.sides,Trace.asym,Trace.events,hx,hy] <;> omega

theorem Trace.essential_has_asym (p : Fin 7) {G : List F} (t : Trace G)
    {f : F} (hf : cl G f) (hz : f (single p) = false)
    (hess : ∃ x, res p f x ≠ f x) : 1 ≤ t.asym p := by
  by_contra hn
  have hzero : t.asym p = 0 := by omega
  obtain ⟨x,hx⟩ := hess
  exact hx (t.zero_asym_invariant p hzero f hf hz x)

theorem Trace.asym_le_events (p : Fin 7) {G : List F} (t : Trace G) :
    t.asym p ≤ t.events p := by
  induction t with
  | nil => simp [Trace.asym,Trace.events]
  | cons g u v hu hv he tail ih =>
    cases hx : u (single p) <;> cases hy : v (single p) <;>
      simp [Trace.asym,Trace.events,hx,hy] <;> omega

theorem Trace.unique_side (p : Fin 7) {G : List F} (t : Trace G)
    {f : F} (hf : cl G f) (hz : f (single p) = false)
    (hess : ∃ x, res p f x ≠ f x) (hevents : t.events p ≤ 1) :
    t.sides p = 1 := by
  have ha := t.essential_has_asym p hf hz hess
  have hi := t.sides_asym p
  have hae := t.asym_le_events p
  omega

end Eliminate984


namespace PEqualNP.Outside.L_meta_984_family

open PEqualNP.CircuitLowerBounds

abbrev F := (Fin 7 → Bool) → Bool

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

theorem gate_or (G : List ((Fin 7 → Bool) → Bool)) (f : ℕ → (Fin 7 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_false G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gate_and (G : List ((Fin 7 → Bool) → Bool)) (f : ℕ → (Fin 7 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, cl_true G, cl_true G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 7 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 7 → Bool) → Bool :=
  fun x => (W gs x).getD k false

theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 7 → Bool) :
    (W gs x).length = 7 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 7 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 7 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 7 + gs.length
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
      have h3 : ¬ (k - (7 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 7
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
        by_cases hk : k = 7 + gs.length
        · rw [if_pos hk]; exact cl_new _ _
        · rw [if_neg hk]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 7 + gs.length
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
def joinInput (x y : Fin 7 → Bool) : Fin 7 → Bool := fun i => x i || y i

theorem cl_merge {G : List F} {x y : Fin 7 → Bool}
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
    ∃ code : (Fin 7 → Bool) → (Fin G.length → Bool),
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
    {m : ℕ} (M : Fin m → (Fin 7 → Bool))
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
    {m : ℕ} (M : Fin m → (Fin 7 → Bool))
    (h0 : ∀ i, C.eval (List.ofFn (M i)) = false)
    (h1 : ∀ i j, i ≠ j → C.eval (List.ofFn (joinInput (M i) (M j))) = true) :
    m ≤ 2^A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  exact (family_bound hG hw M h0 h1).trans (Nat.pow_le_pow_right (by omega) hlen)


def edgeFun (E : List (Fin 7 × Fin 7)) (x : Fin 7 → Bool) : Bool :=
  E.any (fun e => x e.1 && x e.2)

def edges1 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)]
def rows1 : Fin 9 → Finset (Fin 7) := ![{0,5},{1,3,5},{2,3,5},{1,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6},{1,4,6}]
def assignments1 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows1 i)

theorem rows1_zero : ∀ i, edgeFun edges1 (assignments1 i) = false := by decide +kernel
 theorem rows1_join : ∀ i j, i ≠ j →
    edgeFun edges1 (joinInput (assignments1 i) (assignments1 j)) = true := by decide +kernel

theorem and_lower1 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges1 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments1
    (fun i => (he _).trans (rows1_zero i))
    (fun i j hn => (he _).trans (rows1_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges2 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)]
def rows2 : Fin 9 → Finset (Fin 7) := ![{1,3,4},{2,3,4},{1,4,5},{2,4,5},{1,3,6},{2,3,6},{0,5,6},{1,5,6},{2,5,6}]
def assignments2 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows2 i)

theorem rows2_zero : ∀ i, edgeFun edges2 (assignments2 i) = false := by decide +kernel
 theorem rows2_join : ∀ i j, i ≠ j →
    edgeFun edges2 (joinInput (assignments2 i) (assignments2 j)) = true := by decide +kernel

theorem and_lower2 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges2 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments2
    (fun i => (he _).trans (rows2_zero i))
    (fun i j hn => (he _).trans (rows2_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges6 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)]
def rows6 : Fin 9 → Finset (Fin 7) := ![{0,4},{1,3,4},{2,3,4},{0,5},{1,3,5},{2,3,5},{0,6},{1,3,6},{2,3,6}]
def assignments6 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows6 i)

theorem rows6_zero : ∀ i, edgeFun edges6 (assignments6 i) = false := by decide +kernel
 theorem rows6_join : ∀ i j, i ≠ j →
    edgeFun edges6 (joinInput (assignments6 i) (assignments6 j)) = true := by decide +kernel

theorem and_lower6 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges6 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments6
    (fun i => (he _).trans (rows6_zero i))
    (fun i j hn => (he _).trans (rows6_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges9 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)]
def rows9 : Fin 5 → Finset (Fin 7) := ![{0},{1,3,5,6},{2,3,5,6},{1,4,5,6},{2,4,5,6}]
def assignments9 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows9 i)

theorem rows9_zero : ∀ i, edgeFun edges9 (assignments9 i) = false := by decide +kernel
 theorem rows9_join : ∀ i j, i ≠ j →
    edgeFun edges9 (joinInput (assignments9 i) (assignments9 j)) = true := by decide +kernel

theorem and_lower9 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges9 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments9
    (fun i => (he _).trans (rows9_zero i))
    (fun i j hn => (he _).trans (rows9_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges10 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)]
def rows10 : Fin 5 → Finset (Fin 7) := ![{1,3,5},{1,4,5},{0,6},{2,3,5,6},{2,4,5,6}]
def assignments10 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows10 i)

theorem rows10_zero : ∀ i, edgeFun edges10 (assignments10 i) = false := by decide +kernel
 theorem rows10_join : ∀ i j, i ≠ j →
    edgeFun edges10 (joinInput (assignments10 i) (assignments10 j)) = true := by decide +kernel

theorem and_lower10 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges10 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments10
    (fun i => (he _).trans (rows10_zero i))
    (fun i j hn => (he _).trans (rows10_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges11 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)]
def rows11 : Fin 9 → Finset (Fin 7) := ![{1,3,5},{2,3,5},{1,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def assignments11 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows11 i)

theorem rows11_zero : ∀ i, edgeFun edges11 (assignments11 i) = false := by decide +kernel
 theorem rows11_join : ∀ i j, i ≠ j →
    edgeFun edges11 (joinInput (assignments11 i) (assignments11 j)) = true := by decide +kernel

theorem and_lower11 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges11 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments11
    (fun i => (he _).trans (rows11_zero i))
    (fun i j hn => (he _).trans (rows11_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges12 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)]
def rows12 : Fin 5 → Finset (Fin 7) := ![{1,3},{1,4},{0,5,6},{2,3,5,6},{2,4,5,6}]
def assignments12 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows12 i)

theorem rows12_zero : ∀ i, edgeFun edges12 (assignments12 i) = false := by decide +kernel
 theorem rows12_join : ∀ i j, i ≠ j →
    edgeFun edges12 (joinInput (assignments12 i) (assignments12 j)) = true := by decide +kernel

theorem and_lower12 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges12 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments12
    (fun i => (he _).trans (rows12_zero i))
    (fun i j hn => (he _).trans (rows12_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges14 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)]
def rows14 : Fin 5 → Finset (Fin 7) := ![{1,3},{2,3,5},{1,4,6},{0,5,6},{2,4,5,6}]
def assignments14 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows14 i)

theorem rows14_zero : ∀ i, edgeFun edges14 (assignments14 i) = false := by decide +kernel
 theorem rows14_join : ∀ i j, i ≠ j →
    edgeFun edges14 (joinInput (assignments14 i) (assignments14 j)) = true := by decide +kernel

theorem and_lower14 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges14 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments14
    (fun i => (he _).trans (rows14_zero i))
    (fun i j hn => (he _).trans (rows14_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges16 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)]
def rows16 : Fin 5 → Finset (Fin 7) := ![{1,3,4},{0,5},{2,3,4,5},{0,6},{1,4,6}]
def assignments16 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows16 i)

theorem rows16_zero : ∀ i, edgeFun edges16 (assignments16 i) = false := by decide +kernel
 theorem rows16_join : ∀ i j, i ≠ j →
    edgeFun edges16 (joinInput (assignments16 i) (assignments16 j)) = true := by decide +kernel

theorem and_lower16 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges16 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments16
    (fun i => (he _).trans (rows16_zero i))
    (fun i j hn => (he _).trans (rows16_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges22 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)]
def rows22 : Fin 5 → Finset (Fin 7) := ![{0,5},{1,5},{2,5},{1,3,6},{0,4,6}]
def assignments22 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows22 i)

theorem rows22_zero : ∀ i, edgeFun edges22 (assignments22 i) = false := by decide +kernel
 theorem rows22_join : ∀ i j, i ≠ j →
    edgeFun edges22 (joinInput (assignments22 i) (assignments22 j)) = true := by decide +kernel

theorem and_lower22 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges22 x) :
    3 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments22
    (fun i => (he _).trans (rows22_zero i))
    (fun i j hn => (he _).trans (rows22_join i j hn))
  by_contra hn
  have hc : A.card ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges24 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)]
def rows24 : Fin 9 → Finset (Fin 7) := ![{0,4},{1,4},{2,4},{0,5},{1,3,5},{2,3,5},{0,6},{1,3,6},{2,3,6}]
def assignments24 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows24 i)

theorem rows24_zero : ∀ i, edgeFun edges24 (assignments24 i) = false := by decide +kernel
 theorem rows24_join : ∀ i j, i ≠ j →
    edgeFun edges24 (joinInput (assignments24 i) (assignments24 j)) = true := by decide +kernel

theorem and_lower24 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges24 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments24
    (fun i => (he _).trans (rows24_zero i))
    (fun i j hn => (he _).trans (rows24_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges26 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
def rows26 : Fin 9 → Finset (Fin 7) := ![{0},{1,3,5},{2,3,5},{1,4,5},{2,4,5},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def assignments26 (i : Fin 9) (v : Fin 7) : Bool := decide (v ∈ rows26 i)

theorem rows26_zero : ∀ i, edgeFun edges26 (assignments26 i) = false := by decide +kernel
 theorem rows26_join : ∀ i j, i ≠ j →
    edgeFun edges26 (joinInput (assignments26 i) (assignments26 j)) = true := by decide +kernel

theorem and_lower26 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges26 x) :
    4 ≤ A.card := by
  have hb := circuit_family_bound C hm A hA assignments26
    (fun i => (he _).trans (rows26_zero i))
    (fun i j hn => (he _).trans (rows26_join i j hn))
  by_contra hn
  have hc : A.card ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

theorem good_eliminate_iff (G : List F) : good G ↔ Eliminate984.good G := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    simp only [good, Eliminate984.good, ← ih]
    rfl

def edges3 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)]
def rows3 : Fin 5 → Finset (Fin 7) := ![{0,4,5},{2,4,5},{0,5,6},{1,5,6},{2,5,6}]
def assignments3 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows3 i)

theorem rows3_zero : ∀ i, Eliminate984.res 5 (edgeFun edges3) (assignments3 i) = false := by decide +kernel
 theorem rows3_join : ∀ i j, i ≠ j →
    Eliminate984.res 5 (edgeFun edges3) (joinInput (assignments3 i) (assignments3 j)) = true := by decide +kernel
 theorem vertex3_zero : edgeFun edges3 (Eliminate984.single 5) = false := by decide +kernel
 theorem vertex3_essential : ∃ x, Eliminate984.res 5 (edgeFun edges3) x ≠ edgeFun edges3 x := by decide +kernel

theorem and_lower3 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges3 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 5)) = false :=
    (he _).trans vertex3_zero
  have hess : ∃ x, Eliminate984.res 5 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex3_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 5 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments3
    (fun i => (he _).trans (rows3_zero i))
    (fun i j hn => (he _).trans (rows3_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges4 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)]
def rows4 : Fin 5 → Finset (Fin 7) := ![{0,4,5},{1,4,5},{2,4,5},{0,5,6},{1,5,6}]
def assignments4 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows4 i)

theorem rows4_zero : ∀ i, Eliminate984.res 5 (edgeFun edges4) (assignments4 i) = false := by decide +kernel
 theorem rows4_join : ∀ i j, i ≠ j →
    Eliminate984.res 5 (edgeFun edges4) (joinInput (assignments4 i) (assignments4 j)) = true := by decide +kernel
 theorem vertex4_zero : edgeFun edges4 (Eliminate984.single 5) = false := by decide +kernel
 theorem vertex4_essential : ∃ x, Eliminate984.res 5 (edgeFun edges4) x ≠ edgeFun edges4 x := by decide +kernel

theorem and_lower4 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges4 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 5)) = false :=
    (he _).trans vertex4_zero
  have hess : ∃ x, Eliminate984.res 5 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex4_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 5 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments4
    (fun i => (he _).trans (rows4_zero i))
    (fun i j hn => (he _).trans (rows4_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges5 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)]
def rows5 : Fin 5 → Finset (Fin 7) := ![{1,3,6},{2,3,6},{0,4,6},{1,4,6},{2,4,6}]
def assignments5 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows5 i)

theorem rows5_zero : ∀ i, Eliminate984.res 6 (edgeFun edges5) (assignments5 i) = false := by decide +kernel
 theorem rows5_join : ∀ i j, i ≠ j →
    Eliminate984.res 6 (edgeFun edges5) (joinInput (assignments5 i) (assignments5 j)) = true := by decide +kernel
 theorem vertex5_zero : edgeFun edges5 (Eliminate984.single 6) = false := by decide +kernel
 theorem vertex5_essential : ∃ x, Eliminate984.res 6 (edgeFun edges5) x ≠ edgeFun edges5 x := by decide +kernel

theorem and_lower5 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges5 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 6)) = false :=
    (he _).trans vertex5_zero
  have hess : ∃ x, Eliminate984.res 6 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex5_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 6 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments5
    (fun i => (he _).trans (rows5_zero i))
    (fun i j hn => (he _).trans (rows5_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges7 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)]
def rows7 : Fin 5 → Finset (Fin 7) := ![{1,2,6},{0,4,6},{2,4,6},{0,5,6},{1,5,6}]
def assignments7 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows7 i)

theorem rows7_zero : ∀ i, Eliminate984.res 6 (edgeFun edges7) (assignments7 i) = false := by decide +kernel
 theorem rows7_join : ∀ i j, i ≠ j →
    Eliminate984.res 6 (edgeFun edges7) (joinInput (assignments7 i) (assignments7 j)) = true := by decide +kernel
 theorem vertex7_zero : edgeFun edges7 (Eliminate984.single 6) = false := by decide +kernel
 theorem vertex7_essential : ∃ x, Eliminate984.res 6 (edgeFun edges7) x ≠ edgeFun edges7 x := by decide +kernel

theorem and_lower7 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges7 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 6)) = false :=
    (he _).trans vertex7_zero
  have hess : ∃ x, Eliminate984.res 6 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex7_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 6 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments7
    (fun i => (he _).trans (rows7_zero i))
    (fun i j hn => (he _).trans (rows7_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges13 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)]
def rows13 : Fin 5 → Finset (Fin 7) := ![{2,3,5},{2,4,5},{0,5,6},{3,5,6},{4,5,6}]
def assignments13 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows13 i)

theorem rows13_zero : ∀ i, Eliminate984.res 5 (edgeFun edges13) (assignments13 i) = false := by decide +kernel
 theorem rows13_join : ∀ i j, i ≠ j →
    Eliminate984.res 5 (edgeFun edges13) (joinInput (assignments13 i) (assignments13 j)) = true := by decide +kernel
 theorem vertex13_zero : edgeFun edges13 (Eliminate984.single 5) = false := by decide +kernel
 theorem vertex13_essential : ∃ x, Eliminate984.res 5 (edgeFun edges13) x ≠ edgeFun edges13 x := by decide +kernel

theorem and_lower13 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges13 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 5)) = false :=
    (he _).trans vertex13_zero
  have hess : ∃ x, Eliminate984.res 5 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex13_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 5 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments13
    (fun i => (he _).trans (rows13_zero i))
    (fun i j hn => (he _).trans (rows13_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges15 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]
def rows15 : Fin 5 → Finset (Fin 7) := ![{0,6},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def assignments15 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows15 i)

theorem rows15_zero : ∀ i, Eliminate984.res 6 (edgeFun edges15) (assignments15 i) = false := by decide +kernel
 theorem rows15_join : ∀ i j, i ≠ j →
    Eliminate984.res 6 (edgeFun edges15) (joinInput (assignments15 i) (assignments15 j)) = true := by decide +kernel
 theorem vertex15_zero : edgeFun edges15 (Eliminate984.single 6) = false := by decide +kernel
 theorem vertex15_essential : ∃ x, Eliminate984.res 6 (edgeFun edges15) x ≠ edgeFun edges15 x := by decide +kernel

theorem and_lower15 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges15 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 6)) = false :=
    (he _).trans vertex15_zero
  have hess : ∃ x, Eliminate984.res 6 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex15_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 6 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments15
    (fun i => (he _).trans (rows15_zero i))
    (fun i j hn => (he _).trans (rows15_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges17 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)]
def rows17 : Fin 5 → Finset (Fin 7) := ![{1,3,4},{2,3,4},{1,4,5},{2,4,5},{1,4,6}]
def assignments17 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows17 i)

theorem rows17_zero : ∀ i, Eliminate984.res 4 (edgeFun edges17) (assignments17 i) = false := by decide +kernel
 theorem rows17_join : ∀ i j, i ≠ j →
    Eliminate984.res 4 (edgeFun edges17) (joinInput (assignments17 i) (assignments17 j)) = true := by decide +kernel
 theorem vertex17_zero : edgeFun edges17 (Eliminate984.single 4) = false := by decide +kernel
 theorem vertex17_essential : ∃ x, Eliminate984.res 4 (edgeFun edges17) x ≠ edgeFun edges17 x := by decide +kernel

theorem and_lower17 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges17 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 4)) = false :=
    (he _).trans vertex17_zero
  have hess : ∃ x, Eliminate984.res 4 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex17_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 4 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments17
    (fun i => (he _).trans (rows17_zero i))
    (fun i j hn => (he _).trans (rows17_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges19 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)]
def rows19 : Fin 5 → Finset (Fin 7) := ![{1,3,5},{0,4,5},{3,4,5},{0,5,6},{1,5,6}]
def assignments19 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows19 i)

theorem rows19_zero : ∀ i, Eliminate984.res 5 (edgeFun edges19) (assignments19 i) = false := by decide +kernel
 theorem rows19_join : ∀ i j, i ≠ j →
    Eliminate984.res 5 (edgeFun edges19) (joinInput (assignments19 i) (assignments19 j)) = true := by decide +kernel
 theorem vertex19_zero : edgeFun edges19 (Eliminate984.single 5) = false := by decide +kernel
 theorem vertex19_essential : ∃ x, Eliminate984.res 5 (edgeFun edges19) x ≠ edgeFun edges19 x := by decide +kernel

theorem and_lower19 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges19 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 5)) = false :=
    (he _).trans vertex19_zero
  have hess : ∃ x, Eliminate984.res 5 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex19_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 5 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments19
    (fun i => (he _).trans (rows19_zero i))
    (fun i j hn => (he _).trans (rows19_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges20 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)]
def rows20 : Fin 5 → Finset (Fin 7) := ![{0,4,6},{2,4,6},{0,5,6},{1,5,6},{2,5,6}]
def assignments20 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows20 i)

theorem rows20_zero : ∀ i, Eliminate984.res 6 (edgeFun edges20) (assignments20 i) = false := by decide +kernel
 theorem rows20_join : ∀ i j, i ≠ j →
    Eliminate984.res 6 (edgeFun edges20) (joinInput (assignments20 i) (assignments20 j)) = true := by decide +kernel
 theorem vertex20_zero : edgeFun edges20 (Eliminate984.single 6) = false := by decide +kernel
 theorem vertex20_essential : ∃ x, Eliminate984.res 6 (edgeFun edges20) x ≠ edgeFun edges20 x := by decide +kernel

theorem and_lower20 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges20 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 6)) = false :=
    (he _).trans vertex20_zero
  have hess : ∃ x, Eliminate984.res 6 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex20_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 6 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments20
    (fun i => (he _).trans (rows20_zero i))
    (fun i j hn => (he _).trans (rows20_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

def edges21 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)]
def rows21 : Fin 5 → Finset (Fin 7) := ![{2,3,4},{0,4,5},{2,4,5},{0,4,6},{2,4,6}]
def assignments21 (i : Fin 5) (v : Fin 7) : Bool := decide (v ∈ rows21 i)

theorem rows21_zero : ∀ i, Eliminate984.res 4 (edgeFun edges21) (assignments21 i) = false := by decide +kernel
 theorem rows21_join : ∀ i j, i ≠ j →
    Eliminate984.res 4 (edgeFun edges21) (joinInput (assignments21 i) (assignments21 j)) = true := by decide +kernel
 theorem vertex21_zero : edgeFun edges21 (Eliminate984.single 4) = false := by decide +kernel
 theorem vertex21_essential : ∃ x, Eliminate984.res 4 (edgeFun edges21) x ≠ edgeFun edges21 x := by decide +kernel

theorem and_lower21 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun edges21 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : C.eval (List.ofFn (Eliminate984.single 4)) = false :=
    (he _).trans vertex21_zero
  have hess : ∃ x, Eliminate984.res 4 (fun x => C.eval (List.ofFn x)) x ≠ C.eval (List.ofFn x) := by
    obtain ⟨x,hx⟩ := vertex21_essential
    refine ⟨x, ?_⟩
    simpa only [Eliminate984.res, he] using hx
  obtain ⟨H,hH,hsmall,hout⟩ := Eliminate984.eliminate_essential_vertex 4 ((good_eliminate_iff G).mp hG) hw hz hess
  have hb := family_bound ((good_eliminate_iff H).mpr hH) hout assignments21
    (fun i => (he _).trans (rows21_zero i))
    (fun i j hn => (he _).trans (rows21_join i j hn))
  by_contra hn
  have hc : H.length ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hc
  norm_num at hp
  omega

end PEqualNP.Outside.L_meta_984_family
#print axioms PEqualNP.Outside.L_meta_984_family.circuit_family_bound
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower1
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower2
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower6
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower9
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower10
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower11
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower12
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower14
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower16
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower22
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower24
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower26
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower3
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower4
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower5
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower7
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower13
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower15
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower17
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower19
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower20
#print axioms PEqualNP.Outside.L_meta_984_family.and_lower21

namespace Eliminate984
def Trace.side : {G : List F} → Trace G → Fin G.length → Bool → F
  | _, .nil, i => Fin.elim0 i
  | _, .cons _ u v _ _ _ tail, i => Fin.cases (fun b => if b then v else u) (tail.side) i

def Trace.choice {G : List F} (t : Trace G) (x : X) (i : Fin G.length) : Option Bool :=
  if t.side i false x = false then some false
  else if t.side i true x = false then some true else none

theorem cl_false_insert (p : Fin 7) {G : List F}
    (x : X) (hG : ∀ g ∈ G, g x = false → g (pin p x) = false)
    {f : F} (hf : cl G f) (hs : f (single p) = false)
    (hx : f x = false) : f (pin p x) = false := by
  obtain ⟨S,hS,he⟩ := hf
  rw [he] at hs hx ⊢
  simp only [List.any_eq_false, Bool.not_eq_true] at hs hx ⊢
  intro f hf
  rcases List.mem_append.mp (hS f hf) with hg | hi
  · exact hG f hg (hx f hf)
  · simp only [inputs,List.mem_cons,List.mem_ofFn] at hi
    rcases hi with rfl | ⟨i,rfl⟩
    · exact hx _ hf
    · have hn : i ≠ p := by simpa [single] using hs _ hf
      simpa [pin,hn] using hx _ hf

theorem Trace.unselected_invariant (p : Fin 7) {G : List F} (t : Trace G) (x : X)
    (hs : ∀ i b, t.choice x i = some b → t.side i b (single p) = false) :
    ∀ g ∈ G, g x = false → g (pin p x) = false := by
  induction t with
  | nil => simp
  | @cons G g u v hu hv he tail ih =>
    have ht : ∀ i b, tail.choice x i = some b → tail.side i b (single p) = false := by
      intro i b hb
      exact hs i.succ b hb
    have hg := ih ht
    intro f hf hfx
    rcases List.mem_cons.mp hf with rfl | hf
    · rw [he] at hfx ⊢
      by_cases hux : u x = false
      · have hu0 : u (single p) = false := hs 0 false (by simp [Trace.choice,Trace.side,hux])
        have huc : u (pin p x) = false := by
          obtain ⟨S,hS,heS⟩ := hu
          rw [heS] at hu0 hux ⊢
          simp only [List.any_eq_false, Bool.not_eq_true] at hu0 hux ⊢
          intro f hf
          rcases List.mem_append.mp (hS f hf) with hfG | hfI
          · exact hg f hfG (hux f hf)
          · simp only [inputs,List.mem_cons,List.mem_ofFn] at hfI
            rcases hfI with rfl | ⟨i,rfl⟩
            · exact hux _ hf
            · have hn : i ≠ p := by simpa [single] using hu0 _ hf
              simpa [pin,hn] using hux _ hf
        simp [huc]
      · have hut : u x = true := by cases h : u x <;> simp_all
        have hvx : v x = false := by simpa [hut] using hfx
        have hv0 : v (single p) = false := hs 0 true (by simp [Trace.choice,Trace.side,hut,hvx])
        have hvc : v (pin p x) = false := by
          obtain ⟨S,hS,heS⟩ := hv
          rw [heS] at hv0 hvx ⊢
          simp only [List.any_eq_false, Bool.not_eq_true] at hv0 hvx ⊢
          intro f hf
          rcases List.mem_append.mp (hS f hf) with hfG | hfI
          · exact hg f hfG (hvx f hf)
          · simp only [inputs,List.mem_cons,List.mem_ofFn] at hfI
            rcases hfI with rfl | ⟨i,rfl⟩
            · exact hvx _ hf
            · have hn : i ≠ p := by simpa [single] using hv0 _ hf
              simpa [pin,hn] using hvx _ hf
        simp [hvc]
    · exact hg f hf hfx



theorem Trace.side_monotone {G : List F} (t : Trace G) (i : Fin G.length) (b : Bool) :
    Monotone (t.side i b) := by
  induction t with
  | nil => exact Fin.elim0 i
  | cons g u v hu hv he tail ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases b
    · exact cl_monotone (good_monotone tail.good) hu
    · exact cl_monotone (good_monotone tail.good) hv

theorem Trace.choice_false {G : List F} (t : Trace G) (x : X) (i : Fin G.length)
    (b : Bool) (hc : t.choice x i = some b) : t.side i b x = false := by
  unfold Trace.choice at hc
  split_ifs at hc with hl hr
  · cases Option.some.inj hc
    exact hl
  · cases Option.some.inj hc
    exact hr

theorem Trace.projection_cover {G : List F} (t : Trace G) {f : F} (hf : cl G f)
    (hz : ∀ p, f (single p) = false) (x : X) (hx : f x = false)
    (hmax : ∀ p, x p = false → f (pin p x) = true) :
    (∀ p, x p = true → ∀ i b, t.side i b (single p) = true → t.choice x i ≠ some b) ∧
    (∀ p, x p = false → ∃ i b, t.side i b (single p) = true ∧ t.choice x i = some b) := by
  constructor
  · intro p hp i b hb hc
    have hle : single p ≤ x := by
      intro q
      by_cases hq : q = p
      · subst q
        simp [single,hp]
      · simp [single,hq]
    have ht : t.side i b x = true := Bool.eq_true_of_true_le (by simpa only [hb] using (t.side_monotone i b) hle)
    have hf := t.choice_false x i b hc
    rw [ht] at hf
    contradiction
  · intro p hp
    by_contra hn
    have hs : ∀ i b, t.choice x i = some b → t.side i b (single p) = false := by
      intro i b hc
      cases h : t.side i b (single p)
      · rfl
      · exact (hn ⟨i,b,h,hc⟩).elim
    have hG := t.unselected_invariant p x hs
    have hh := cl_false_insert p x hG hf (hz p) hx
    rw [hmax p hp] at hh
    contradiction


end Eliminate984

namespace Jared984Four

variable {V R G : Type*} [DecidableEq V] [DecidableEq G] [Fintype G]

theorem four_bound (rows : R → Finset V) (lit : V → Finset (G × Bool))
    (witness : Fin 4 → V)
    (hone : ∀ a, (lit (witness a)).card ≤ 1)
    (hne : ∀ a, (lit (witness a)).Nonempty)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r)
    (hcover : ∀ r, ∃ choice : G → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ lit v, choice l.1 ≠ some l.2) ∧
      (∀ v, v ∉ rows r → ∃ l ∈ lit v, choice l.1 = some l.2)) :
    4 ≤ Fintype.card G := by
  classical
  choose pick hp using hne
  have hu (a : Fin 4) (l : G × Bool) (hl : l ∈ lit (witness a)) : l = pick a :=
    Finset.card_le_one.mp (hone a) l hl (pick a) (hp a)
  have hi : Function.Injective (fun a => (pick a).1) := by
    intro a b hab
    change (pick a).1 = (pick b).1 at hab
    by_contra hn
    by_cases hs : (pick a).2 = (pick b).2
    · obtain ⟨r,ha,hb⟩ := hsep a b hn
      obtain ⟨choice,havoid,hhit⟩ := hcover r
      obtain ⟨l,hl,he⟩ := hhit (witness b) hb
      rw [hu b l hl] at he
      have hno := havoid (witness a) ha (pick a) (hp a)
      rw [hab,hs,he] at hno
      exact hno rfl
    · obtain ⟨r,ha,hb⟩ := homit a b hn
      obtain ⟨choice,havoid,hhit⟩ := hcover r
      obtain ⟨la,hla,hea⟩ := hhit (witness a) ha
      obtain ⟨lb,hlb,heb⟩ := hhit (witness b) hb
      rw [hu a la hla] at hea
      rw [hu b lb hlb] at heb
      rw [hab,heb] at hea
      exact hs (Option.some.inj hea).symm
  have hc := Fintype.card_le_of_injective _ hi
  simpa using hc


def edgeFun (E : List (Fin 7 × Fin 7)) (S : Finset (Fin 7)) : Bool :=
  E.any (fun e => decide (e.1 ∈ S ∧ e.2 ∈ S))
def Good (E : List (Fin 7 × Fin 7)) (S : Finset (Fin 7)) : Prop :=
  edgeFun E S = false ∧ ∀ v, v ∉ S → edgeFun E (insert v S) = true

def edges0 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def rows0 : Fin 8 → Finset (Fin 7) := ![{1,3,6},{2,3,6},{0,4,6},{1,4,6},{2,4,6},{0,5,6},{1,5,6},{2,5,6}]
def witness0 : Fin 4 → Fin 7 := ![1,2,4,5]
def through0 : Fin 4 → Fin 3 → Fin 8 := ![![0,3,6],![1,4,7],![2,3,4],![5,6,7]]
theorem good0 : ∀ r, Good edges0 (rows0 r) := by unfold Good; decide +kernel
theorem contains0 : ∀ a b, witness0 a ∈ rows0 (through0 a b) := by decide +kernel
theorem through_injective0 : ∀ a, Function.Injective (through0 a) := by decide +kernel
theorem separates0 : ∀ a b, a ≠ b → ∃ r, witness0 a ∈ rows0 r ∧ witness0 b ∉ rows0 r := by decide +kernel
theorem omits0 : ∀ a b, a ≠ b → ∃ r, witness0 a ∉ rows0 r ∧ witness0 b ∉ rows0 r := by decide +kernel

def edges1 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)]
def rows1 : Fin 10 → Finset (Fin 7) := ![{0,5},{1,3,5},{2,3,5},{1,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def witness1 : Fin 4 → Fin 7 := ![1,2,3,4]
def through1 : Fin 4 → Fin 3 → Fin 10 := ![![1,3,6],![2,4,7],![1,2,6],![3,4,8]]
theorem good1 : ∀ r, Good edges1 (rows1 r) := by unfold Good; decide +kernel
theorem contains1 : ∀ a b, witness1 a ∈ rows1 (through1 a b) := by decide +kernel
theorem through_injective1 : ∀ a, Function.Injective (through1 a) := by decide +kernel
theorem separates1 : ∀ a b, a ≠ b → ∃ r, witness1 a ∈ rows1 r ∧ witness1 b ∉ rows1 r := by decide +kernel
theorem omits1 : ∀ a b, a ≠ b → ∃ r, witness1 a ∉ rows1 r ∧ witness1 b ∉ rows1 r := by decide +kernel

def edges2 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)]
def rows2 : Fin 9 → Finset (Fin 7) := ![{1,3,4},{2,3,4},{1,4,5},{2,4,5},{1,3,6},{2,3,6},{0,5,6},{1,5,6},{2,5,6}]
def witness2 : Fin 4 → Fin 7 := ![1,2,3,4]
def through2 : Fin 4 → Fin 3 → Fin 9 := ![![0,2,4],![1,3,5],![0,1,4],![0,1,2]]
theorem good2 : ∀ r, Good edges2 (rows2 r) := by unfold Good; decide +kernel
theorem contains2 : ∀ a b, witness2 a ∈ rows2 (through2 a b) := by decide +kernel
theorem through_injective2 : ∀ a, Function.Injective (through2 a) := by decide +kernel
theorem separates2 : ∀ a b, a ≠ b → ∃ r, witness2 a ∈ rows2 r ∧ witness2 b ∉ rows2 r := by decide +kernel
theorem omits2 : ∀ a b, a ≠ b → ∃ r, witness2 a ∉ rows2 r ∧ witness2 b ∉ rows2 r := by decide +kernel

def edges5 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)]
def rows5 : Fin 8 → Finset (Fin 7) := ![{0,5},{1,3,5},{2,3,5},{1,3,6},{2,3,6},{0,4,6},{1,4,6},{2,4,6}]
def witness5 : Fin 4 → Fin 7 := ![1,2,3,4]
def through5 : Fin 4 → Fin 3 → Fin 8 := ![![1,3,6],![2,4,7],![1,2,3],![5,6,7]]
theorem good5 : ∀ r, Good edges5 (rows5 r) := by unfold Good; decide +kernel
theorem contains5 : ∀ a b, witness5 a ∈ rows5 (through5 a b) := by decide +kernel
theorem through_injective5 : ∀ a, Function.Injective (through5 a) := by decide +kernel
theorem separates5 : ∀ a b, a ≠ b → ∃ r, witness5 a ∈ rows5 r ∧ witness5 b ∉ rows5 r := by decide +kernel
theorem omits5 : ∀ a b, a ≠ b → ∃ r, witness5 a ∉ rows5 r ∧ witness5 b ∉ rows5 r := by decide +kernel

def edges6 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)]
def rows6 : Fin 9 → Finset (Fin 7) := ![{0,4},{1,3,4},{2,3,4},{0,5},{1,3,5},{2,3,5},{0,6},{1,3,6},{2,3,6}]
def witness6 : Fin 4 → Fin 7 := ![0,1,2,4]
def through6 : Fin 4 → Fin 3 → Fin 9 := ![![0,3,6],![1,4,7],![2,5,8],![0,1,2]]
theorem good6 : ∀ r, Good edges6 (rows6 r) := by unfold Good; decide +kernel
theorem contains6 : ∀ a b, witness6 a ∈ rows6 (through6 a b) := by decide +kernel
theorem through_injective6 : ∀ a, Function.Injective (through6 a) := by decide +kernel
theorem separates6 : ∀ a b, a ≠ b → ∃ r, witness6 a ∈ rows6 r ∧ witness6 b ∉ rows6 r := by decide +kernel
theorem omits6 : ∀ a b, a ≠ b → ∃ r, witness6 a ∉ rows6 r ∧ witness6 b ∉ rows6 r := by decide +kernel

def edges7 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)]
def rows7 : Fin 8 → Finset (Fin 7) := ![{1,2,3},{2,3,4},{1,3,5},{1,2,6},{0,4,6},{2,4,6},{0,5,6},{1,5,6}]
def witness7 : Fin 4 → Fin 7 := ![1,2,3,4]
def through7 : Fin 4 → Fin 3 → Fin 8 := ![![0,2,3],![0,1,3],![0,1,2],![1,4,5]]
theorem good7 : ∀ r, Good edges7 (rows7 r) := by unfold Good; decide +kernel
theorem contains7 : ∀ a b, witness7 a ∈ rows7 (through7 a b) := by decide +kernel
theorem through_injective7 : ∀ a, Function.Injective (through7 a) := by decide +kernel
theorem separates7 : ∀ a b, a ≠ b → ∃ r, witness7 a ∈ rows7 r ∧ witness7 b ∉ rows7 r := by decide +kernel
theorem omits7 : ∀ a b, a ≠ b → ∃ r, witness7 a ∉ rows7 r ∧ witness7 b ∉ rows7 r := by decide +kernel

def edges8 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)]
def rows8 : Fin 7 → Finset (Fin 7) := ![{0,3,4},{1,2,5},{0,4,5},{1,4,5},{1,2,6},{0,3,6},{2,3,6}]
def witness8 : Fin 4 → Fin 7 := ![0,1,2,3]
def through8 : Fin 4 → Fin 3 → Fin 7 := ![![0,2,5],![1,3,4],![1,4,6],![0,5,6]]
theorem good8 : ∀ r, Good edges8 (rows8 r) := by unfold Good; decide +kernel
theorem contains8 : ∀ a b, witness8 a ∈ rows8 (through8 a b) := by decide +kernel
theorem through_injective8 : ∀ a, Function.Injective (through8 a) := by decide +kernel
theorem separates8 : ∀ a b, a ≠ b → ∃ r, witness8 a ∈ rows8 r ∧ witness8 b ∉ rows8 r := by decide +kernel
theorem omits8 : ∀ a b, a ≠ b → ∃ r, witness8 a ∉ rows8 r ∧ witness8 b ∉ rows8 r := by decide +kernel

def edges11 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)]
def rows11 : Fin 9 → Finset (Fin 7) := ![{1,3,5},{2,3,5},{1,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def witness11 : Fin 4 → Fin 7 := ![1,2,3,4]
def through11 : Fin 4 → Fin 3 → Fin 9 := ![![0,2,5],![1,3,6],![0,1,5],![2,3,7]]
theorem good11 : ∀ r, Good edges11 (rows11 r) := by unfold Good; decide +kernel
theorem contains11 : ∀ a b, witness11 a ∈ rows11 (through11 a b) := by decide +kernel
theorem through_injective11 : ∀ a, Function.Injective (through11 a) := by decide +kernel
theorem separates11 : ∀ a b, a ≠ b → ∃ r, witness11 a ∈ rows11 r ∧ witness11 b ∉ rows11 r := by decide +kernel
theorem omits11 : ∀ a b, a ≠ b → ∃ r, witness11 a ∉ rows11 r ∧ witness11 b ∉ rows11 r := by decide +kernel

def edges15 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]
def rows15 : Fin 8 → Finset (Fin 7) := ![{0,5},{2,3,5},{2,4,5},{0,6},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def witness15 : Fin 4 → Fin 7 := ![2,3,4,5]
def through15 : Fin 4 → Fin 3 → Fin 8 := ![![1,2,5],![1,4,5],![2,6,7],![0,1,2]]
theorem good15 : ∀ r, Good edges15 (rows15 r) := by unfold Good; decide +kernel
theorem contains15 : ∀ a b, witness15 a ∈ rows15 (through15 a b) := by decide +kernel
theorem through_injective15 : ∀ a, Function.Injective (through15 a) := by decide +kernel
theorem separates15 : ∀ a b, a ≠ b → ∃ r, witness15 a ∈ rows15 r ∧ witness15 b ∉ rows15 r := by decide +kernel
theorem omits15 : ∀ a b, a ≠ b → ∃ r, witness15 a ∉ rows15 r ∧ witness15 b ∉ rows15 r := by decide +kernel

def edges17 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)]
def rows17 : Fin 8 → Finset (Fin 7) := ![{1,3,4},{2,3,4},{0,5},{1,4,5},{2,4,5},{0,6},{1,4,6},{2,4,6}]
def witness17 : Fin 4 → Fin 7 := ![1,2,5,6]
def through17 : Fin 4 → Fin 3 → Fin 8 := ![![0,3,6],![1,4,7],![2,3,4],![5,6,7]]
theorem good17 : ∀ r, Good edges17 (rows17 r) := by unfold Good; decide +kernel
theorem contains17 : ∀ a b, witness17 a ∈ rows17 (through17 a b) := by decide +kernel
theorem through_injective17 : ∀ a, Function.Injective (through17 a) := by decide +kernel
theorem separates17 : ∀ a b, a ≠ b → ∃ r, witness17 a ∈ rows17 r ∧ witness17 b ∉ rows17 r := by decide +kernel
theorem omits17 : ∀ a b, a ≠ b → ∃ r, witness17 a ∉ rows17 r ∧ witness17 b ∉ rows17 r := by decide +kernel

def edges18 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)]
def rows18 : Fin 8 → Finset (Fin 7) := ![{1,3,4},{2,3,4},{0,5},{1,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6}]
def witness18 : Fin 4 → Fin 7 := ![1,2,3,4]
def through18 : Fin 4 → Fin 3 → Fin 8 := ![![0,3,6],![1,4,7],![0,1,6],![0,1,3]]
theorem good18 : ∀ r, Good edges18 (rows18 r) := by unfold Good; decide +kernel
theorem contains18 : ∀ a b, witness18 a ∈ rows18 (through18 a b) := by decide +kernel
theorem through_injective18 : ∀ a, Function.Injective (through18 a) := by decide +kernel
theorem separates18 : ∀ a b, a ≠ b → ∃ r, witness18 a ∈ rows18 r ∧ witness18 b ∉ rows18 r := by decide +kernel
theorem omits18 : ∀ a b, a ≠ b → ∃ r, witness18 a ∉ rows18 r ∧ witness18 b ∉ rows18 r := by decide +kernel

def edges19 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)]
def rows19 : Fin 7 → Finset (Fin 7) := ![{2,3,4},{1,3,5},{0,4,5},{3,4,5},{2,6},{0,5,6},{1,5,6}]
def witness19 : Fin 4 → Fin 7 := ![3,4,5,6]
def through19 : Fin 4 → Fin 3 → Fin 7 := ![![0,1,3],![0,2,3],![1,2,3],![4,5,6]]
theorem good19 : ∀ r, Good edges19 (rows19 r) := by unfold Good; decide +kernel
theorem contains19 : ∀ a b, witness19 a ∈ rows19 (through19 a b) := by decide +kernel
theorem through_injective19 : ∀ a, Function.Injective (through19 a) := by decide +kernel
theorem separates19 : ∀ a b, a ≠ b → ∃ r, witness19 a ∈ rows19 r ∧ witness19 b ∉ rows19 r := by decide +kernel
theorem omits19 : ∀ a b, a ≠ b → ∃ r, witness19 a ∉ rows19 r ∧ witness19 b ∉ rows19 r := by decide +kernel

def edges21 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)]
def rows21 : Fin 8 → Finset (Fin 7) := ![{1,3},{2,3,4},{1,5},{0,4,5},{2,4,5},{1,6},{0,4,6},{2,4,6}]
def witness21 : Fin 4 → Fin 7 := ![1,2,5,6]
def through21 : Fin 4 → Fin 3 → Fin 8 := ![![0,2,5],![1,4,7],![2,3,4],![5,6,7]]
theorem good21 : ∀ r, Good edges21 (rows21 r) := by unfold Good; decide +kernel
theorem contains21 : ∀ a b, witness21 a ∈ rows21 (through21 a b) := by decide +kernel
theorem through_injective21 : ∀ a, Function.Injective (through21 a) := by decide +kernel
theorem separates21 : ∀ a b, a ≠ b → ∃ r, witness21 a ∈ rows21 r ∧ witness21 b ∉ rows21 r := by decide +kernel
theorem omits21 : ∀ a b, a ≠ b → ∃ r, witness21 a ∉ rows21 r ∧ witness21 b ∉ rows21 r := by decide +kernel

def edges23 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6),(5,6)]
def rows23 : Fin 7 → Finset (Fin 7) := ![{2,3,4},{1,5},{0,4,5},{2,4,5},{0,6},{1,3,6},{2,3,6}]
def witness23 : Fin 4 → Fin 7 := ![2,3,4,5]
def through23 : Fin 4 → Fin 3 → Fin 7 := ![![0,3,6],![0,5,6],![0,2,3],![1,2,3]]
theorem good23 : ∀ r, Good edges23 (rows23 r) := by unfold Good; decide +kernel
theorem contains23 : ∀ a b, witness23 a ∈ rows23 (through23 a b) := by decide +kernel
theorem through_injective23 : ∀ a, Function.Injective (through23 a) := by decide +kernel
theorem separates23 : ∀ a b, a ≠ b → ∃ r, witness23 a ∈ rows23 r ∧ witness23 b ∉ rows23 r := by decide +kernel
theorem omits23 : ∀ a b, a ≠ b → ∃ r, witness23 a ∉ rows23 r ∧ witness23 b ∉ rows23 r := by decide +kernel

def edges24 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)]
def rows24 : Fin 9 → Finset (Fin 7) := ![{0,4},{1,4},{2,4},{0,5},{1,3,5},{2,3,5},{0,6},{1,3,6},{2,3,6}]
def witness24 : Fin 4 → Fin 7 := ![0,1,2,3]
def through24 : Fin 4 → Fin 3 → Fin 9 := ![![0,3,6],![1,4,7],![2,5,8],![4,5,7]]
theorem good24 : ∀ r, Good edges24 (rows24 r) := by unfold Good; decide +kernel
theorem contains24 : ∀ a b, witness24 a ∈ rows24 (through24 a b) := by decide +kernel
theorem through_injective24 : ∀ a, Function.Injective (through24 a) := by decide +kernel
theorem separates24 : ∀ a b, a ≠ b → ∃ r, witness24 a ∈ rows24 r ∧ witness24 b ∉ rows24 r := by decide +kernel
theorem omits24 : ∀ a b, a ≠ b → ∃ r, witness24 a ∉ rows24 r ∧ witness24 b ∉ rows24 r := by decide +kernel

def edges25 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5),(4,6)]
def rows25 : Fin 7 → Finset (Fin 7) := ![{1,2,3},{0,4},{2,3,4},{1,3,5},{1,2,6},{0,5,6},{1,5,6}]
def witness25 : Fin 4 → Fin 7 := ![1,2,3,5]
def through25 : Fin 4 → Fin 3 → Fin 7 := ![![0,3,4],![0,2,4],![0,2,3],![3,5,6]]
theorem good25 : ∀ r, Good edges25 (rows25 r) := by unfold Good; decide +kernel
theorem contains25 : ∀ a b, witness25 a ∈ rows25 (through25 a b) := by decide +kernel
theorem through_injective25 : ∀ a, Function.Injective (through25 a) := by decide +kernel
theorem separates25 : ∀ a b, a ≠ b → ∃ r, witness25 a ∈ rows25 r ∧ witness25 b ∉ rows25 r := by decide +kernel
theorem omits25 : ∀ a b, a ≠ b → ∃ r, witness25 a ∉ rows25 r ∧ witness25 b ∉ rows25 r := by decide +kernel

def edges26 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
def rows26 : Fin 9 → Finset (Fin 7) := ![{0},{1,3,5},{2,3,5},{1,4,5},{2,4,5},{1,3,6},{2,3,6},{1,4,6},{2,4,6}]
def witness26 : Fin 4 → Fin 7 := ![1,2,3,4]
def through26 : Fin 4 → Fin 3 → Fin 9 := ![![1,3,5],![2,4,6],![1,2,5],![3,4,7]]
theorem good26 : ∀ r, Good edges26 (rows26 r) := by unfold Good; decide +kernel
theorem contains26 : ∀ a b, witness26 a ∈ rows26 (through26 a b) := by decide +kernel
theorem through_injective26 : ∀ a, Function.Injective (through26 a) := by decide +kernel
theorem separates26 : ∀ a b, a ≠ b → ∃ r, witness26 a ∈ rows26 r ∧ witness26 b ∉ rows26 r := by decide +kernel
theorem omits26 : ∀ a b, a ≠ b → ∃ r, witness26 a ∉ rows26 r ∧ witness26 b ∉ rows26 r := by decide +kernel

def edges27 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def rows27 : Fin 8 → Finset (Fin 7) := ![{1,3},{1,4},{0,5},{2,3,5},{2,4,5},{0,6},{2,3,6},{2,4,6}]
def witness27 : Fin 4 → Fin 7 := ![2,3,4,5]
def through27 : Fin 4 → Fin 3 → Fin 8 := ![![3,4,6],![0,3,6],![1,4,7],![2,3,4]]
theorem good27 : ∀ r, Good edges27 (rows27 r) := by unfold Good; decide +kernel
theorem contains27 : ∀ a b, witness27 a ∈ rows27 (through27 a b) := by decide +kernel
theorem through_injective27 : ∀ a, Function.Injective (through27 a) := by decide +kernel
theorem separates27 : ∀ a b, a ≠ b → ∃ r, witness27 a ∈ rows27 r ∧ witness27 b ∉ rows27 r := by decide +kernel
theorem omits27 : ∀ a b, a ≠ b → ∃ r, witness27 a ∉ rows27 r ∧ witness27 b ∉ rows27 r := by decide +kernel

def edges28 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]
def rows28 : Fin 7 → Finset (Fin 7) := ![{1,3},{0,5},{2,3,5},{2,4,5},{0,6},{1,4,6},{2,4,6}]
def witness28 : Fin 4 → Fin 7 := ![2,4,5,6]
def through28 : Fin 4 → Fin 3 → Fin 7 := ![![2,3,6],![3,5,6],![1,2,3],![4,5,6]]
theorem good28 : ∀ r, Good edges28 (rows28 r) := by unfold Good; decide +kernel
theorem contains28 : ∀ a b, witness28 a ∈ rows28 (through28 a b) := by decide +kernel
theorem through_injective28 : ∀ a, Function.Injective (through28 a) := by decide +kernel
theorem separates28 : ∀ a b, a ≠ b → ∃ r, witness28 a ∈ rows28 r ∧ witness28 b ∉ rows28 r := by decide +kernel
theorem omits28 : ∀ a b, a ≠ b → ∃ r, witness28 a ∉ rows28 r ∧ witness28 b ∉ rows28 r := by decide +kernel

def edges29 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)]
def rows29 : Fin 7 → Finset (Fin 7) := ![{2,3,4},{1,3,5},{0,4,5},{3,4,5},{0,6},{1,6},{2,6}]
def witness29 : Fin 4 → Fin 7 := ![3,4,5,6]
def through29 : Fin 4 → Fin 3 → Fin 7 := ![![0,1,3],![0,2,3],![1,2,3],![4,5,6]]
theorem good29 : ∀ r, Good edges29 (rows29 r) := by unfold Good; decide +kernel
theorem contains29 : ∀ a b, witness29 a ∈ rows29 (through29 a b) := by decide +kernel
theorem through_injective29 : ∀ a, Function.Injective (through29 a) := by decide +kernel
theorem separates29 : ∀ a b, a ≠ b → ∃ r, witness29 a ∈ rows29 r ∧ witness29 b ∉ rows29 r := by decide +kernel
theorem omits29 : ∀ a b, a ≠ b → ∃ r, witness29 a ∉ rows29 r ∧ witness29 b ∉ rows29 r := by decide +kernel

def edges30 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
def rows30 : Fin 8 → Finset (Fin 7) := ![{1,3},{2,3,4},{0,5},{1,5},{2,5},{1,6},{0,4,6},{2,4,6}]
def witness30 : Fin 4 → Fin 7 := ![1,2,4,5]
def through30 : Fin 4 → Fin 3 → Fin 8 := ![![0,3,5],![1,4,7],![1,6,7],![2,3,4]]
theorem good30 : ∀ r, Good edges30 (rows30 r) := by unfold Good; decide +kernel
theorem contains30 : ∀ a b, witness30 a ∈ rows30 (through30 a b) := by decide +kernel
theorem through_injective30 : ∀ a, Function.Injective (through30 a) := by decide +kernel
theorem separates30 : ∀ a b, a ≠ b → ∃ r, witness30 a ∈ rows30 r ∧ witness30 b ∉ rows30 r := by decide +kernel
theorem omits30 : ∀ a b, a ≠ b → ∃ r, witness30 a ∉ rows30 r ∧ witness30 b ∉ rows30 r := by decide +kernel
end Jared984Four
#print axioms Jared984Four.four_bound
#print axioms Jared984Four.good0
#print axioms Jared984Four.separates0
#print axioms Jared984Four.omits0
#print axioms Jared984Four.good1
#print axioms Jared984Four.separates1
#print axioms Jared984Four.omits1
#print axioms Jared984Four.good2
#print axioms Jared984Four.separates2
#print axioms Jared984Four.omits2
#print axioms Jared984Four.good5
#print axioms Jared984Four.separates5
#print axioms Jared984Four.omits5
#print axioms Jared984Four.good6
#print axioms Jared984Four.separates6
#print axioms Jared984Four.omits6
#print axioms Jared984Four.good7
#print axioms Jared984Four.separates7
#print axioms Jared984Four.omits7
#print axioms Jared984Four.good8
#print axioms Jared984Four.separates8
#print axioms Jared984Four.omits8
#print axioms Jared984Four.good11
#print axioms Jared984Four.separates11
#print axioms Jared984Four.omits11
#print axioms Jared984Four.good15
#print axioms Jared984Four.separates15
#print axioms Jared984Four.omits15
#print axioms Jared984Four.good17
#print axioms Jared984Four.separates17
#print axioms Jared984Four.omits17
#print axioms Jared984Four.good18
#print axioms Jared984Four.separates18
#print axioms Jared984Four.omits18
#print axioms Jared984Four.good19
#print axioms Jared984Four.separates19
#print axioms Jared984Four.omits19
#print axioms Jared984Four.good21
#print axioms Jared984Four.separates21
#print axioms Jared984Four.omits21
#print axioms Jared984Four.good23
#print axioms Jared984Four.separates23
#print axioms Jared984Four.omits23
#print axioms Jared984Four.good24
#print axioms Jared984Four.separates24
#print axioms Jared984Four.omits24
#print axioms Jared984Four.good25
#print axioms Jared984Four.separates25
#print axioms Jared984Four.omits25
#print axioms Jared984Four.good26
#print axioms Jared984Four.separates26
#print axioms Jared984Four.omits26
#print axioms Jared984Four.good27
#print axioms Jared984Four.separates27
#print axioms Jared984Four.omits27
#print axioms Jared984Four.good28
#print axioms Jared984Four.separates28
#print axioms Jared984Four.omits28
#print axioms Jared984Four.good29
#print axioms Jared984Four.separates29
#print axioms Jared984Four.omits29
#print axioms Jared984Four.good30
#print axioms Jared984Four.separates30
#print axioms Jared984Four.omits30

namespace Eliminate984
theorem sum_bool_nat (f : Bool → Nat) : (∑ b : Bool, f b) = f false + f true := by
  have hh : (Finset.univ : Finset Bool) = {false,true} := by decide
  rw [hh]
  simp

 theorem Trace.sides_eq_sum (p : Fin 7) {G : List F} (t : Trace G) :
    t.sides p = ∑ i : Fin G.length,
      ((if t.side i false (single p) then 1 else 0) +
       (if t.side i true (single p) then 1 else 0)) := by
  induction t with
  | nil => simp [Trace.sides]
  | @cons G g u v hu hv he tail ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp [Trace.side,Trace.sides]
    erw [← ih]
    omega

 theorem Trace.sides_eq_card (p : Fin 7) {G : List F} (t : Trace G) :
    t.sides p = (Finset.univ.filter (fun z : Fin G.length × Bool =>
      t.side z.1 z.2 (single p) = true)).card := by
  rw [Trace.sides_eq_sum]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sum_bool_nat (fun b => if t.side i b (single p) then 1 else 0)).symm


end Eliminate984

namespace Jared984Integrate
open PEqualNP.Outside.L_meta_984_family
open Eliminate984

def rowInput {m : ℕ} (rows : Fin m → Finset (Fin 7)) (r : Fin m) : Eliminate984.X :=
  fun p => decide (p ∈ rows r)

theorem pin_eq (p : Fin 7) (x : Eliminate984.X) (h : x p = true) : Eliminate984.pin p x = x := by
  simp [Eliminate984.pin, ← h]

theorem events_le_one {G : List Eliminate984.F} (t : Eliminate984.Trace G)
    {f : Eliminate984.F} (hf : Eliminate984.cl G f) (hsize : G.length ≤ 3)
    {m : ℕ} (rows : Fin m → Finset (Fin 7)) (p : Fin 7) (through : Fin 3 → Fin m)
    (hinj : Function.Injective through)
    (hcontains : ∀ i, p ∈ rows (through i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput rows r) (rowInput rows s)) = true) :
    t.events p ≤ 1 := by
  obtain ⟨H,hH,hlen,hmap⟩ := t.pin_all_events p
  have hp (i : Fin 3) : Eliminate984.pin p (rowInput rows (through i)) = rowInput rows (through i) :=
    pin_eq p _ (by simp [rowInput,hcontains])
  have hj (i j : Fin 3) : Eliminate984.pin p (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput rows (through i)) (rowInput rows (through j))) =
      PEqualNP.Outside.L_meta_984_family.joinInput (rowInput rows (through i)) (rowInput rows (through j)) :=
    pin_eq p _ (by simp [PEqualNP.Outside.L_meta_984_family.joinInput,rowInput,hcontains])
  have hb := PEqualNP.Outside.L_meta_984_family.family_bound
    ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff H).mpr hH) (hmap f hf)
    (fun i : Fin 3 => rowInput rows (through i))
    (fun i => by simpa only [Eliminate984.res,hp] using h0 (through i))
    (fun i j hn => by simpa only [Eliminate984.res,hj] using hjoin (through i) (through j) (fun h => hn (hinj h)))
  have htwo : 2 ≤ H.length := by
    by_contra hn
    have hl : H.length ≤ 1 := by omega
    have hh := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hl
    norm_num at hh
    omega
  omega



theorem four_semantic {G : List Eliminate984.F} (hG : Eliminate984.good G)
    {f : Eliminate984.F} (hf : Eliminate984.cl G f)
    {m : ℕ} (rows : Fin m → Finset (Fin 7)) (witness : Fin 4 → Fin 7)
    (through : Fin 4 → Fin 3 → Fin m)
    (hthrough : ∀ a, Function.Injective (through a))
    (hcontains : ∀ a i, witness a ∈ rows (through a i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput rows r) (rowInput rows s)) = true)
    (hmax : ∀ r p, p ∉ rows r → f (Eliminate984.pin p (rowInput rows r)) = true)
    (hz : ∀ p, f (Eliminate984.single p) = false)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r) :
    4 ≤ G.length := by
  classical
  by_contra hn
  have hsize : G.length ≤ 3 := by omega
  let t := Eliminate984.traceOfGood hG
  let lit (p : Fin 7) : Finset (Fin G.length × Bool) :=
    Finset.univ.filter (fun z => t.side z.1 z.2 (Eliminate984.single p) = true)
  have hlit (a : Fin 4) : (lit (witness a)).card = 1 := by
    have hev := events_le_one t hf hsize rows (witness a) (through a) (hthrough a) (hcontains a) h0 hjoin
    have hess : ∃ x, Eliminate984.res (witness a) f x ≠ f x := by
      obtain ⟨b,hb⟩ := exists_ne a
      obtain ⟨r,hbr,har⟩ := hsep b a hb
      refine ⟨rowInput rows r, ?_⟩
      change f (Eliminate984.pin (witness a) (rowInput rows r)) ≠ f (rowInput rows r)
      rw [hmax r (witness a) har,h0 r]
      decide
    have hside := t.unique_side (witness a) hf (hz (witness a)) hess hev
    simpa only [lit,← t.sides_eq_card (witness a)] using hside
  have hcover : ∀ r, ∃ choice : Fin G.length → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ lit v, choice l.1 ≠ some l.2) ∧
      (∀ v, v ∉ rows r → ∃ l ∈ lit v, choice l.1 = some l.2) := by
    intro r
    obtain ⟨ha,hb⟩ := t.projection_cover hf hz (rowInput rows r) (h0 r)
      (fun p hp => hmax r p (by simpa [rowInput] using hp))
    refine ⟨t.choice (rowInput rows r), ?_, ?_⟩
    · intro v hv l hl
      exact ha v (by simpa [rowInput] using hv) l.1 l.2 (Finset.mem_filter.mp hl).2
    · intro v hv
      obtain ⟨i,b,ht,hc⟩ := hb v (by simpa [rowInput] using hv)
      exact ⟨(i,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,hc⟩
  have hfour := Jared984Four.four_bound rows lit witness
    (fun a => (hlit a).le)
    (fun a => Finset.card_pos.mp (by rw [hlit a]; omega)) hsep homit hcover
  simp only [Fintype.card_fin] at hfour
  omega


theorem and_lower8 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges8 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges8 (rowInput Jared984Four.rows8 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges8
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows8 r) (rowInput Jared984Four.rows8 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows8 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges8
      (Eliminate984.pin p (rowInput Jared984Four.rows8 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges8 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows8 Jared984Four.witness8 Jared984Four.through8
    Jared984Four.through_injective8 Jared984Four.contains8
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates8 Jared984Four.omits8
  exact hb.trans hlen

theorem and_lower18 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges18 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges18 (rowInput Jared984Four.rows18 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges18
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows18 r) (rowInput Jared984Four.rows18 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows18 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges18
      (Eliminate984.pin p (rowInput Jared984Four.rows18 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges18 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows18 Jared984Four.witness18 Jared984Four.through18
    Jared984Four.through_injective18 Jared984Four.contains18
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates18 Jared984Four.omits18
  exact hb.trans hlen

theorem and_lower23 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges23 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges23 (rowInput Jared984Four.rows23 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges23
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows23 r) (rowInput Jared984Four.rows23 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows23 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges23
      (Eliminate984.pin p (rowInput Jared984Four.rows23 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges23 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows23 Jared984Four.witness23 Jared984Four.through23
    Jared984Four.through_injective23 Jared984Four.contains23
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates23 Jared984Four.omits23
  exact hb.trans hlen

theorem and_lower25 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges25 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges25 (rowInput Jared984Four.rows25 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges25
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows25 r) (rowInput Jared984Four.rows25 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows25 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges25
      (Eliminate984.pin p (rowInput Jared984Four.rows25 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges25 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows25 Jared984Four.witness25 Jared984Four.through25
    Jared984Four.through_injective25 Jared984Four.contains25
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates25 Jared984Four.omits25
  exact hb.trans hlen

theorem and_lower27 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges27 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges27 (rowInput Jared984Four.rows27 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges27
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows27 r) (rowInput Jared984Four.rows27 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows27 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges27
      (Eliminate984.pin p (rowInput Jared984Four.rows27 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges27 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows27 Jared984Four.witness27 Jared984Four.through27
    Jared984Four.through_injective27 Jared984Four.contains27
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates27 Jared984Four.omits27
  exact hb.trans hlen

theorem and_lower28 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges28 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges28 (rowInput Jared984Four.rows28 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges28
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows28 r) (rowInput Jared984Four.rows28 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows28 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges28
      (Eliminate984.pin p (rowInput Jared984Four.rows28 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges28 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows28 Jared984Four.witness28 Jared984Four.through28
    Jared984Four.through_injective28 Jared984Four.contains28
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates28 Jared984Four.omits28
  exact hb.trans hlen

theorem and_lower29 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges29 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges29 (rowInput Jared984Four.rows29 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges29
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows29 r) (rowInput Jared984Four.rows29 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows29 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges29
      (Eliminate984.pin p (rowInput Jared984Four.rows29 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges29 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows29 Jared984Four.witness29 Jared984Four.through29
    Jared984Four.through_injective29 Jared984Four.contains29
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates29 Jared984Four.omits29
  exact hb.trans hlen

theorem and_lower30 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges30 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges30 (rowInput Jared984Four.rows30 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges30
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows30 r) (rowInput Jared984Four.rows30 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows30 r → PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges30
      (Eliminate984.pin p (rowInput Jared984Four.rows30 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family.edgeFun Jared984Four.edges30 (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows30 Jared984Four.witness30 Jared984Four.through30
    Jared984Four.through_injective30 Jared984Four.contains30
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984Four.separates30 Jared984Four.omits30
  exact hb.trans hlen
end Jared984Integrate
#print axioms Jared984Integrate.four_semantic
#print axioms Jared984Integrate.and_lower8
#print axioms Jared984Integrate.and_lower18
#print axioms Jared984Integrate.and_lower23
#print axioms Jared984Integrate.and_lower25
#print axioms Jared984Integrate.and_lower27
#print axioms Jared984Integrate.and_lower28
#print axioms Jared984Integrate.and_lower29
#print axioms Jared984Integrate.and_lower30


namespace PEqualNP.Outside.L_meta_984.orTheory
namespace GraphInduction599
open SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def sparse (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card

def noFour (G : SimpleGraph V) : Prop :=
  ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4

omit [DecidableEq V] in
theorem sparse_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : sparse G) : sparse H := by
  intro S
  apply le_trans _ (hG S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  exact ⟨SimpleGraph.edgeSet_mono h he.1, he.2⟩

omit [Fintype V] [DecidableEq V] in
theorem noFour_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : noFour G) : noFour H := by
  intro v c hc
  simpa only [Walk.length_mapLe] using hG v (c.mapLe h) (hc.mapLe h)

omit [DecidableEq V] in
theorem count_eq (G : SimpleGraph V) : G.edgeSet.ncard = G.edgeFinset.card := by
  exact Set.ncard_eq_toFinset_card' _

omit [DecidableEq V] in
theorem support_count (G : SimpleGraph V) (hs : sparse G) :
    G.edgeFinset.card ≤ G.support.toFinset.card := by
  rw [← count_eq]
  let S := G.support.toFinset
  apply le_trans _ (hs S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  refine ⟨he, ?_⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Set.mem_toFinset.mpr hab.mem_support_left
    · exact Set.mem_toFinset.mpr hab.mem_support_right

omit [DecidableEq V] in

theorem regular_of_no_leaf (G : SimpleGraph V) (hs : sparse G)
    (hl : ∀ v, G.degree v ≠ 1) (v : V) (hv : v ∈ G.support) : G.degree v = 2 := by
  classical
  have hmin : ∀ i ∈ G.support.toFinset, 2 ≤ G.degree i := by
    intro i hi
    have hi' := (G.degree_pos_iff_mem_support i).mpr (Set.mem_toFinset.mp hi)
    have := hl i
    omega
  by_contra hn
  have hv' := Set.mem_toFinset.mpr hv
  have hd := hmin v hv'
  have hsum := Finset.sum_lt_sum hmin (⟨v,hv',by omega⟩ :
    ∃ i ∈ G.support.toFinset, 2 < G.degree i)
  have hmax := support_count G hs
  have hhand := G.sum_degrees_support_eq_twice_card_edges
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  omega

theorem count_after_delete (G : SimpleGraph V) (v : V) :
    (G.deleteIncidenceSet v).edgeSet.ncard + G.degree v = G.edgeSet.ncard := by
  have h := G.card_edgeFinset_deleteIncidenceSet v
  have hle := G.degree_le_card_edgeFinset v
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using (h ▸ Nat.sub_add_cancel hle :
      (G.deleteIncidenceSet v).edgeFinset.card + G.degree v = G.edgeFinset.card)


theorem of_paid_deletions (cost : SimpleGraph V → ℕ)
    (leaf : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      ∀ v, G.degree v = 1 → cost (G.deleteIncidenceSet v) + 1 ≤ cost G)
    (core : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      (∀ v ∈ G.support, G.degree v = 2) →
      ∃ v ∈ G.support, cost (G.deleteIncidenceSet v) + 2 ≤ cost G)
    (G : SimpleGraph V) (hs : sparse G) (hf : noFour G) :
    G.edgeSet.ncard ≤ cost G + 1 := by
  induction h : G.edgeSet.ncard using Nat.strong_induction_on generalizing G with
  | ind k ih =>
    by_cases hb : G.edgeSet.ncard ≤ cost G + 1
    · omega
    have hg : cost G + 1 < G.edgeSet.ncard := by omega
    have paid : ∃ v, 0 < G.degree v ∧
        cost (G.deleteIncidenceSet v) + G.degree v ≤ cost G := by
      by_cases hleaf : ∃ v, G.degree v = 1
      · obtain ⟨v,hv⟩ := hleaf
        exact ⟨v,by omega, by simpa only [hv] using leaf G hs hf hg v hv⟩
      · have hreg := regular_of_no_leaf G hs (fun v e => hleaf ⟨v,e⟩)
        obtain ⟨v,hv,hp⟩ := core G hs hf hg hreg
        have hd := hreg v hv
        exact ⟨v,by omega,by omega⟩
    obtain ⟨v,hpos,hpay⟩ := paid
    have hc := count_after_delete G v
    have hlt : (G.deleteIncidenceSet v).edgeSet.ncard < k := by omega
    have H := G.deleteIncidenceSet_le v
    have hrec := ih _ hlt _ (sparse_subgraph H hs) (noFour_subgraph H hf) rfl
    omega

end GraphInduction599

namespace GraphCircuit599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
variable {n : ℕ}

def detects (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def covers (C : Circuit) (A : Finset ℕ) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = .or → j ∈ A

def feasible (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ C A, Monotone2 C ∧ detects G C ∧ covers C A ∧ A.card = k

private theorem exists_budget (G : SimpleGraph (Fin n)) :
    ∃ k, k = G.edgeSet.ncard ∨ feasible G k := ⟨_, Or.inl rfl⟩


noncomputable def best (G : SimpleGraph (Fin n)) : ℕ := Nat.find (exists_budget G)

theorem best_le {G : SimpleGraph (Fin n)} {k : ℕ} (h : feasible G k) : best G ≤ k :=
  Nat.find_min' (exists_budget G) (Or.inr h)

theorem represents {G : SimpleGraph (Fin n)} (h : best G < G.edgeSet.ncard) :
    feasible G (best G) :=
  (Nat.find_spec (exists_budget G)).resolve_left (Nat.ne_of_lt h)

theorem one_bit {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true := by
  obtain ⟨u,hu⟩ := G.mem_support.mp hv
  let x : Fin n → Bool := fun i => decide (i=u)
  have hne : v ≠ u := hu.ne
  refine ⟨x, by simp [x,hne], ?_, ?_⟩
  · rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨i,j,hij,hi,hj⟩ := (h x).mp ht
    exact hij.ne ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
  · apply (h _).mpr
    exact ⟨v,u,hu,by simp,by simp [x,Function.update_of_ne hne.symm]⟩

theorem deletion_eval (G : SimpleGraph (Fin n)) (v : Fin n) (x : Fin n → Bool) :
    (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧
        Function.update x v false b = true) ↔
      ∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hav : a ≠ v := by rintro rfl; simp at ha
    have hbv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a,b,(G.deleteIncidenceSet_adj).mpr ⟨hab,hav,hbv⟩,
      (Function.update_of_ne hav _ _).symm.trans ha,(Function.update_of_ne hbv _ _).symm.trans hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    obtain ⟨hab,hav,hbv⟩ := G.deleteIncidenceSet_adj.mp hab
    exact ⟨a,b,hab,(Function.update_of_ne hav _ _).trans ha,(Function.update_of_ne hbv _ _).trans hb⟩

theorem accepts_without {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    (v : Fin n) (hd : G.degree v < G.edgeSet.ncard) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  have hc := GraphInduction599.count_after_delete G v
  have hcard : 0 < (G.deleteIncidenceSet v).edgeSet.ncard := by omega
  obtain ⟨e,he⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hcard)
  have hex : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a,b,he⟩
  obtain ⟨a,b,hab⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  apply Exists.intro x
  refine ⟨by simp [x], (h x).mpr ?_⟩
  exact (deletion_eval G v (fun _ => true)).mpr ⟨a,b,hab,rfl,rfl⟩

theorem delete_isolated {G : SimpleGraph (Fin n)} {v : Fin n} (hv : v ∉ G.support) :
    G.deleteIncidenceSet v = G := by
  ext a b
  rw [G.deleteIncidenceSet_adj]
  refine ⟨fun h => h.1, fun hab => ⟨hab,?_,?_⟩⟩
  · rintro rfl
    exact hv hab.mem_support_left
  · rintro rfl
    exact hv hab.mem_support_right

theorem two_neighbors {G : SimpleGraph (Fin n)} {v : Fin n} (hd : 2 ≤ G.degree v) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  have h : 1 < (G.neighborFinset v).card := hd
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h
  exact ⟨a,b,hab,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hb⟩

theorem accepts_core_without {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    (degrees : ∀ u ∈ G.support, G.degree u = 2) {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  obtain ⟨u,hvu⟩ := G.mem_support.mp hv
  obtain ⟨a,b,hab,ha,hb⟩ := two_neighbors (le_of_eq (degrees u hvu.mem_support_right).symm)
  have hex : ∃ w, G.Adj u w ∧ w ≠ v := by
    by_cases he : a = v
    · exact ⟨b,hb,fun h => hab (he.trans h.symm)⟩
    · exact ⟨a,ha,he⟩
  obtain ⟨w,hw,hwv⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  exact ⟨x,by simp [x], (h x).mpr ⟨u,w,hw,
    by simp [x,Function.update_of_ne hvu.ne.symm],by simp [x,Function.update_of_ne hwv]⟩⟩

theorem support_nonempty {G : SimpleGraph (Fin n)} (hg : 0 < G.edgeSet.ncard) :
    G.support.Nonempty := by
  obtain ⟨e,he⟩ := Set.nonempty_of_ncard_ne_zero hg.ne'
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    exact ⟨a,hab.mem_support_left⟩

end GraphCircuit599

namespace Leaf599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

private def release {n : ℕ} (gs : List Gate) (v : Fin n) : Prop :=
  ∃ (j : ℕ) (g : Gate) (i : ℕ), gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → val gs z i=false

private theorem release_prefix {n : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : release gs v) : release (gs++[g]) v := by
  obtain ⟨j,q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j,q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private theorem sensitive_or_dominated {n : ℕ} (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (no : ¬release gs v) (w : ℕ)
    (hd : val gs x w ≠ val gs (Function.update x v true) w) :
    ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    intro z hz
    change (List.ofFn x).getD w false ≠ (List.ofFn (Function.update x v true)).getD w false at hd
    change (List.ofFn z).getD w false = false
    by_cases hw : w<n
    · rw [List.getD_eq_getElem _ _ (by simpa using hw),List.getD_eq_getElem _ _ (by simpa using hw)] at hd
      rw [List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_ofFn] at hd ⊢
      by_cases hv : (⟨w,hw⟩ : Fin n)=v
      · exact hv ▸ hz
      · exact (hd (Function.update_of_ne hv true x).symm).elim
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)]
  | append_singleton gs g ih =>
    have hm' : ∀ q ∈ gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have no' : ¬ release gs v := fun h => no (release_prefix g h)
    by_cases hw : w=n+gs.length
    · subst w
      rw [new_val,new_val] at hd
      obtain ⟨a,ha,hdif⟩ : ∃ a ∈ g.inputs, val gs x a ≠ val gs (Function.update x v true) a := by
        by_contra! h
        exact hd (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        exact hdif (by
          unfold val
          rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
            List.getD_eq_default _ _ (by simpa [run_len] using h)])
      have hf := ih hm' no' a hdif
      rcases hm g (by simp) with hop | hop
      · intro z hz
        rw [new_val]
        have he := hf z hz
        change (g.op.eval _) = false
        rw [hop]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [he]⟩
      · exact (no ⟨gs.length,g,a,by simp,hop,ha,bound,fun z hz =>
          (other_val _ _ _ (Nat.ne_of_lt bound)).trans (hf z hz)⟩).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      intro z hz
      exact (other_val _ _ _ hw).trans (ih hm' no' w hd z hz)


theorem release_exists {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
      ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false := by
  change release C.gates v
  by_contra h
  obtain ⟨x,_,hx,hy⟩ := on
  obtain ⟨z,hz,ho⟩ := other
  have hd : val C.gates x C.output ≠ val C.gates (Function.update x v true) C.output := by
    change C.eval (List.ofFn x) ≠ _
    exact fun eq => Bool.false_ne_true (hx.symm.trans (eq.trans hy))
  have hf := sensitive_or_dominated v x C.gates (fun g hg => (hm g hg).1) h C.output hd z hz
  exact Bool.false_ne_true (hf.symm.trans ho)

private theorem val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w<n+a.length) :
    val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private def pick (dead i : ℕ) : List ℕ → ℕ
  | a::b::_ => if a=i then b else a
  | _ => dead

private def copyOf (dead i : ℕ) (g : Gate) : Gate := ⟨.and,[pick dead i g.inputs]⟩

private theorem copy_value (dead i : ℕ) (g : Gate) (w : ℕ → Bool)
    (hz : w dead=false) (hi : w i=false) (hop : g.op=.or) (hin : i∈g.inputs)
    (hl : g.inputs.length≤2) : readGate (copyOf dead i g) w = readGate g w := by
  obtain ⟨op,l⟩ := g
  change op=.or at hop
  subst op
  change i∈l at hin
  change l.length≤2 at hl
  rcases l with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩
  · simp at hin
  · have e : i=a := by simpa using hin
    subst a
    simp [readGate,copyOf,pick,GateOp.eval,hz,hi]
  · have e : i=a ∨ i=b := by simpa using hin
    rcases e with rfl|rfl
    · simp [readGate,copyOf,pick,GateOp.eval,hi]
    · by_cases eq : a=i <;> simp [readGate,copyOf,pick,GateOp.eval,hi,eq]
  · simp at hl

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

private def pin (v dead w : ℕ) := if w=v then dead else w
private def reroute (v dead : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (pin v dead)⟩

private theorem pin_eval {n : ℕ} (v : Fin n) (dead : ℕ) (x : Fin n → Bool)
    (gs : List Gate) (hd : n+gs.length≤dead) (w : ℕ) :
    val (gs.map (reroute v dead)) x (pin v dead w) = val gs (Function.update x v false) w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases hw : w=v.val
    · subst w
      simp only [pin,ite_true,List.map_nil,val,run,List.foldl_nil]
      rw [List.getD_eq_default _ _ (by simpa using hd),List.getD_eq_getElem _ _ (by simp)]
      simp
    · rw [show pin v dead w=w by simp [pin,hw]]
      simp only [List.map_nil,val,run,List.foldl_nil]
      by_cases h : w<n
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact (Function.update_of_ne (show (⟨w,h⟩ : Fin n) ≠ v from fun e => hw (congrArg Fin.val e)) false x).symm
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  | append_singleton gs g ih =>
    have hlen : n+gs.length<dead := by simp at hd; omega
    have hv := v.isLt
    simp only [List.map_append,List.map_cons,List.map_nil]
    by_cases hw : w=n+gs.length
    · subst w
      rw [show pin v dead (n+gs.length)=n+(gs.map (reroute v dead)).length by simp [pin,show n+gs.length≠v.val by omega],
        new_val,new_val]
      unfold readGate
      simp only [reroute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih hlen.le j
    · have hne : pin v dead w ≠ n+(gs.map (reroute v dead)).length := by
        simp only [pin,List.length_map]
        split <;> omega
      rw [other_val _ _ _ hne,other_val _ _ _ hw]
      exact ih hlen.le w


def Charged {n : ℕ} (C : Circuit) (v : Fin n) (j : ℕ) : Prop :=
  ∃ (i : ℕ) (g : Gate), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false


theorem restrict_many {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈A\S := by
  classical
  let dead := n+C.gates.length
  let operand (j : ℕ) : ℕ := if hj : j∈S then (charges j hj).choose else 0
  let change (j : ℕ) (g : Gate) := if j∈S then copyOf dead (operand j) g else g
  let gs := C.gates.mapIdx change
  let C' : Circuit := ⟨gs.map (reroute v dead),pin v dead C.output⟩
  have atGate (j : ℕ) (g : Gate) (h : C'.gates[j]?=some g) :
      ∃ q, C.gates[j]?=some q ∧ g=reroute v dead (change j q) := by
    change (gs.map (reroute v dead))[j]?=some g at h
    simp only [gs,List.getElem?_map,List.getElem?_mapIdx] at h
    cases eq : C.gates[j]? with
    | none => simp [eq] at h
    | some q => exact ⟨q,rfl,by simpa [eq] using h.symm⟩
  refine ⟨C',?_,by simp [C',gs],?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨q,hq,rfl⟩ := atGate j g hj
    have good := hm q (List.mem_of_getElem? hq)
    by_cases h : j∈S
    · simp [change,h,copyOf,reroute]
    · simpa [change,h,reroute] using good
  · intro x
    let z := Function.update x v false
    have hz : z v=false := by simp [z]
    have hstep (a : List Gate) (g : Gate) (pre : ∃ b, C.gates=(a++[g])++b) :
        readGate (change a.length g) (val a z) = readGate g (val a z) := by
      by_cases h : a.length∈S
      · obtain ⟨b,hb⟩ := pre
        have hh := (charges a.length h).choose_spec
        change ∃ (q : Gate), C.gates[a.length]?=some q ∧ q.op=.or ∧ _ at hh
        obtain ⟨q,hq,hop,hin,hi,hzero⟩ := hh
        have hhg : C.gates[a.length]?=some g := by simp [hb,List.append_assoc]
        obtain rfl : q=g := Option.some.inj (hq.symm.trans hhg)
        let i := (charges a.length h).choose
        have hlen : a.length ≤ C.gates.length := by simp [hb]
        have hdead : val a z dead=false := by
          unfold val
          apply List.getD_eq_default
          simp only [run_len,List.length_ofFn]
          dsimp [dead]
          omega
        have hfull : val C.gates z i=false := hzero z hz
        have ha : val a z i=false := by
          rw [hb,List.append_assoc] at hfull
          exact (val_prefix a ([q]++b) z i hi).symm.trans hfull
        have hep : change a.length q=copyOf dead i q := by
          unfold change operand
          simp only [h,↓reduceIte,↓reduceDIte]
          rfl
        rw [hep]
        exact copy_value dead i q (val a z) hdead ha hop hin (hm q (List.mem_of_getElem? hhg)).2
      · simp [change,h]
    have hp := patch_val C change z hstep C.gates ⟨[],by simp⟩ C.output
    have hpin := pin_eval v dead x gs (by simp [gs,dead]) C.output
    exact hpin.trans hp
  · intro j g hg hop
    obtain ⟨q,hq,rfl⟩ := atGate j g hg
    by_cases h : j∈S
    · simp [reroute,change,h,copyOf] at hop
    · refine Finset.mem_sdiff.mpr ⟨cover j q hq ?_,h⟩
      simpa [reroute,change,h] using hop


theorem restrict_charged {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+S.card=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  have sub : S⊆A := by
    intro j hj
    obtain ⟨_,g,hg,hop,_⟩ := charges j hj
    exact cover j g hg hop
  obtain ⟨C',hM,_,hF,hB⟩ := restrict_many C v A S hm cover charges
  exact ⟨C',A\S,Finset.card_sdiff_add_card_eq_card sub,hM,hF,hB⟩


theorem restrict_one {n : ℕ} (C : Circuit) (v : Fin n) (A : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+1=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  obtain ⟨j,g,i,hg,hop,hin,hi,hv⟩ := release_exists C v hm on other
  have hp : Charged C v j := ⟨i,g,hg,hop,hin,hi,hv⟩
  simpa only [Finset.card_singleton] using restrict_charged C v A {j} hm cover
    (fun k hk => Finset.mem_singleton.mp hk ▸ hp)


theorem discard_redundant_or {n : ℕ} (C : Circuit) (A : Finset ℕ) (j : ℕ) (g : Gate)
    (hm : Monotone2 C) (cover : ∀ k h, C.gates[k]?=some h → h.op=.or → k∈A)
    (hg : C.gates[j]?=some g) (hop : g.op=.or)
    (same : (∃ w<n+j, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+j) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false=b) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn x)) ∧
      (∀ k h, C'.gates[k]?=some h → h.op=.or → k∈A.erase j) ∧ (A.erase j).card+1=A.card := by
  let dead := n+C.gates.length
  obtain ⟨l,hl,allowed,glob⟩ : ∃ l : List ℕ, l.length≤1 ∧
      (∀ w∈l, w<n+j ∨ w=dead) ∧
      ∀ x : Fin n → Bool, readGate ⟨.and,l⟩ (val C.gates x)=val C.gates x (n+j) := by
    rcases same with ⟨w,hw,eq⟩ | ⟨b,eq⟩
    · refine ⟨[w],by simp,fun z hz => (List.mem_singleton.mp hz) ▸ (Or.inl hw),?_⟩
      intro x
      have hx : val C.gates x w=val C.gates x (n+j) := (eq x).symm
      simpa [readGate,GateOp.eval] using hx
    · cases b
      · refine ⟨[dead],by simp,fun w hw => Or.inr (List.mem_singleton.mp hw),?_⟩
        intro x
        have hd : val C.gates x dead=false := by
          unfold val
          exact List.getD_eq_default _ _ (by simp [run_len,dead])
        have hx : false=val C.gates x (n+j) := (eq x).symm
        simpa [readGate,GateOp.eval,hd] using hx
      · exact ⟨[],by simp,by simp,fun x => (eq x).symm⟩
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
        rcases allowed w hw with h|rfl
        · rw [hb,List.append_assoc]
          exact (val_prefix a ([_]++b) x w (by omega)).symm
        · have ha' : a.length≤C.gates.length := by simp [hb]
          unfold val
          rw [List.getD_eq_default _ _ (by simp [run_len,dead];omega),
            List.getD_eq_default _ _ (by simp [run_len,dead])]
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

end Leaf599

namespace PaidGraph599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit599
open scoped Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

theorem after_restriction {v : Fin n} {C' : Circuit} (h : detects G C)
    (heq : ∀ x : Fin n → Bool,
      C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) :
    detects (G.deleteIncidenceSet v) C' := by
  intro x
  rw [heq]
  exact (h _).trans (deletion_eval G v x)

theorem charged_saving (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (v : Fin n) (S : Finset ℕ) (charged : ∀ j∈S, Leaf599.Charged C v j) :
    best (G.deleteIncidenceSet v) + S.card ≤ A.card := by
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf599.restrict_charged C v A S hm hc charged
  have hb := best_le (show feasible (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

theorem charge_is_active (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) {v : Fin n} {j : ℕ} (hj : Leaf599.Charged C v j) :
    v ∈ G.support := by
  by_contra hv
  have hh := charged_saving hm h hc v {j} (fun k hk => Finset.mem_singleton.mp hk ▸ hj)
  simp only [delete_isolated hv,Finset.card_singleton,hmin,Nat.not_succ_le_self] at hh

theorem double_saving (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (v : Fin n) {i j : ℕ} (hne : i ≠ j) (hi : Leaf599.Charged C v i)
    (hj : Leaf599.Charged C v j) : best (G.deleteIncidenceSet v) + 2 ≤ A.card := by
  have hh := charged_saving hm h hc v {i,j} (fun k hk => by
    rcases Finset.mem_insert.mp hk with he|he
    · exact he ▸ hi
    · exact Finset.mem_singleton.mp he ▸ hj)
  simpa [hne] using hh

theorem leaf_paid (hg : best G + 1 < G.edgeSet.ncard) (v : Fin n) (degree : G.degree v = 1) :
    best (G.deleteIncidenceSet v) + 1 ≤ best G := by
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  have hv := (G.degree_pos_iff_mem_support v).mp (show 0 < G.degree v by omega)
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf599.restrict_one C v A hm hc (one_bit h hv)
    (accepts_without h v (by omega))
  have hb := best_le (show feasible (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

def corePaid (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), GraphInduction599.sparse G → GraphInduction599.noFour G →
    best G + 1 < G.edgeSet.ncard → (∀ v ∈ G.support, G.degree v = 2) →
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G

theorem edge_bound (core : corePaid n) (hs : GraphInduction599.sparse G)
    (hf : GraphInduction599.noFour G) (hm : Monotone2 C) (h : detects G C)
    (hc : covers C A) : G.edgeSet.ncard ≤ A.card + 1 := by
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  exact (GraphInduction599.of_paid_deletions best (fun _ _ _ hg => leaf_paid hg)
    core G hs hf).trans (by omega)

end PaidGraph599

namespace CycleModule599

open Finset
variable {V : Type*} [DecidableEq V]

def edgeAt (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

theorem edgeAt_mono {G : SimpleGraph V} {X Y : Finset V} (h : X ⊆ Y) :
    edgeAt G X → edgeAt G Y :=
  fun ⟨a,ha,b,hb,he⟩ => ⟨a,h ha,b,h hb,he⟩

@[simp] theorem no_edge_empty (G : SimpleGraph V) : ¬edgeAt G ∅ := by simp [edgeAt]
@[simp] theorem no_edge_singleton (G : SimpleGraph V) (v : V) : ¬edgeAt G {v} := by
  simp [edgeAt]

@[simp] theorem edgeAt_pair (G : SimpleGraph V) (u v : V) : edgeAt G {u,v} ↔ G.Adj u v := by
  simp only [edgeAt,mem_insert,mem_singleton]
  constructor
  · rintro ⟨a,rfl|rfl,b,rfl|rfl,h⟩
    · exact (G.irrefl h).elim
    · exact h
    · exact h.symm
    · exact (G.irrefl h).elim
  · intro h
    exact ⟨u,Or.inl rfl,v,Or.inr rfl,h⟩

theorem pair_minimal {G : SimpleGraph V} {Y : Finset V} {p q : V}
    (hY : edgeAt G Y) (hs : Y ⊆ {p,q}) : Y = {p,q} := by
  obtain ⟨a,ha,b,hb,hab⟩ := hY
  have ha' := hs ha
  have hb' := hs hb
  simp only [mem_insert,mem_singleton] at ha' hb'
  apply subset_antisymm hs
  intro i hi
  simp only [mem_insert,mem_singleton] at hi
  have hne := hab.ne
  grind


def bit (A B X : Finset V) : Prop := A ⊆ X ∨ B ⊆ X


def factors (G : SimpleGraph V) (S A B : Finset V) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, (bit A B X ↔ bit A B Y) →
    ∀ T : Finset V, Disjoint T S → (edgeAt G (X ∪ T) ↔ edgeAt G (Y ∪ T))

private theorem bit_empty {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ¬ bit A B ∅ := by
  simpa [bit,hA.ne_empty,hB.ne_empty]


theorem interior_bit {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (internal : edgeAt G S) :
    ∀ X ⊆ S, edgeAt G X ↔ bit A B X := by
  classical
  have lo := bit_empty hA hB
  have hbit (X : Finset V) (hX : X⊆S) (edge : edgeAt G X) : bit A B X := by
    by_contra h
    have same := fac X hX ∅ (empty_subset _) (iff_of_false h lo) ∅ (by simp)
    simpa using same.mp (by simpa using edge)
  have hi := hbit S (fun _ h => h) internal
  intro X hX
  refine ⟨hbit X hX,fun hx => ?_⟩
  have same := fac X hX S (fun _ h => h) (iff_of_true hx hi) ∅ (by simp)
  simpa using same.mpr (by simpa using internal)

theorem isolated_from_outside {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (internal : edgeAt G S)
    {p : V} (hp : p∈S) {q : V} (hpq : G.Adj p q) : q ∈ S := by
  by_contra hq
  have hsingle : ¬bit A B {p} := by
    rw [← interior_bit fac hA hB internal {p} (Finset.singleton_subset_iff.mpr hp)]
    exact no_edge_singleton G p
  have same := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
    (iff_of_false hsingle (bit_empty hA hB)) {q} (by simpa using hq)
  have yes : edgeAt G ({p}∪{q}) := by simpa using hpq
  simpa using same.mp yes

private theorem independent_bit {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (indep : ¬edgeAt G S)
    {p : V} (hp : p∈S) {q : V} (hpq : G.Adj p q) : bit A B {p} := by
  by_contra hn
  have hq : q∉S := fun hh => indep ⟨p,hp,q,hh,hpq⟩
  have same := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
    (iff_of_false hn (bit_empty hA hB)) {q} (by simpa using hq)
  have yes : edgeAt G ({p}∪{q}) := by simpa using hpq
  simpa using same.mp yes


theorem independent_twins {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (indep : ¬edgeAt G S)
    {p q : V} (hp : p∈S) (hq : q∈S) (pactive : ∃ a, G.Adj p a) (qactive : ∃ a, G.Adj q a) :
    ∀ t, G.Adj p t ↔ G.Adj q t := by
  intro t
  obtain ⟨a,ha⟩ := pactive
  obtain ⟨b,hb⟩ := qactive
  by_cases ht : t ∈ S
  · exact iff_of_false (fun h => indep ⟨p,hp,t,ht,h⟩) (fun h => indep ⟨q,hq,t,ht,h⟩)
  · have same := fac {p} (singleton_subset_iff.mpr hp) {q} (singleton_subset_iff.mpr hq)
      (iff_of_true (independent_bit fac hA hB indep hp ha) (independent_bit fac hA hB indep hq hb))
      {t} (by simpa using ht)
    simpa using same

theorem at_most_two_edges {G : SimpleGraph V} {A B S : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAS : A⊆S) (hBS : B⊆S) (internal : edgeAt G S) {p q : V} (hp : p∈S) (hq : q∈S)
    (he : G.Adj p q) : ({p,q} : Finset V)=A ∨ ({p,q} : Finset V)=B := by
  have encode := interior_bit fac hA hB internal
  have hpair : ({p,q} : Finset V)⊆S := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl <;> assumption
  rcases (encode _ hpair).mp ((edgeAt_pair _ _ _).mpr he) with h|h
  · exact Or.inl (pair_minimal ((encode _ hAS).mpr (Or.inl (fun _ hi => hi))) h).symm
  · exact Or.inr (pair_minimal ((encode _ hBS).mpr (Or.inr (fun _ hi => hi))) h).symm


theorem no_module {G : SimpleGraph V} {A B S : Finset V} (hAS : A⊆S) (hBS : B⊆S)
    (hA : A.Nonempty) (hB : B.Nonempty) (two : ∃ p ∈ S, ∃ q ∈ S, p≠q)
    (degree : ∀ p∈S, ∃ q r, q≠r ∧ G.Adj p q ∧ G.Adj p r)
    (not_twins : ∀ p∈S, ∀ q∈S, p≠q → ¬∀ t, G.Adj p t ↔ G.Adj q t) :
    ¬ factors G S A B := by
  classical
  intro fac
  obtain ⟨p,hp,q,hq,hneq⟩ := two
  by_cases inside : edgeAt G S
  · have closed := @isolated_from_outside _ _ G S A B fac hA hB inside
    obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
    have ha := closed hp hpa
    have hb := closed hp hpb
    obtain ⟨c,d,hcd,hac,had⟩ := degree a ha
    obtain ⟨z,hzp,haz⟩ : ∃ z, z≠p ∧ G.Adj a z := by
      by_cases hc : c=p
      · exact ⟨d,fun he => hcd (hc.trans he.symm),had⟩
      · exact ⟨c,hc,hac⟩
    have hz := closed ha haz
    have f := @at_most_two_edges _ _ G A B S fac hA hB hAS hBS inside
    have h1 := f hp ha hpa
    have h2 := f hp hb hpb
    have h3 := f ha hz haz
    have hpna := hpa.ne
    have hpnb := hpb.ne
    have hanz := haz.ne
    have diff12 : ({p,a}:Finset V) ≠ {p,b} := by
      intro eq
      have : a∈({p,b}:Finset V) := eq ▸ (by simp : a∈({p,a}:Finset V))
      simpa [Ne.symm hpna,hab] using this
    have diff13 (x : V) : ({p,x}:Finset V) ≠ {a,z} := by
      intro eq
      have : p∈({a,z}:Finset V) := eq ▸ (by simp : p∈({p,x}:Finset V))
      simpa [hpna,Ne.symm hzp] using this
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> rcases h3 with h3|h3 <;> grind
  · apply not_twins p hp q hq hneq
    obtain ⟨a,_,_,ha,_⟩ := degree p hp
    obtain ⟨b,_,_,hb,_⟩ := degree q hq
    exact independent_twins fac hA hB inside hp hq ⟨a,ha⟩ ⟨b,hb⟩


theorem twins_force_square {G : SimpleGraph V} {p q : V} (hpq : p≠q)
    {a b : V} (hab : a≠b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hqa : G.Adj q a) (hqb : G.Adj q b) :
    ∃ W : G.Walk p p, W.IsCycle ∧ W.length=4 := by
  let W : G.Walk p p := .cons hpa (.cons hqa.symm (.cons hqb (.cons hpb.symm .nil)))
  have hlen : W.length=4 := rfl
  refine ⟨W,SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by omega⟩,hlen⟩
  simp only [W,SimpleGraph.Walk.tail_cons,SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil]
  simp [hab,hpa.ne.symm,hqa.ne.symm,hqb.ne,hpb.ne.symm,hpq.symm]

theorem no_module_of_no_four {G : SimpleGraph V} {A B S : Finset V}
    (hAS : A⊆S) (hBS : B⊆S) (hA : A.Nonempty) (hB : B.Nonempty)
    (two : ∃ p ∈ S, ∃ q ∈ S, p≠q)
    (degree : ∀ p∈S, ∃ q r, q≠r ∧ G.Adj p q ∧ G.Adj p r)
    (no4 : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4) : ¬ factors G S A B := by
  apply no_module hAS hBS hA hB two degree
  intro p hp q hq hpq eq
  obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
  obtain ⟨c,hc,hlen⟩ := twins_force_square hpq hab hpa hpb ((eq a).mp hpa) ((eq b).mp hpb)
  exact no4 p c hc hlen

end CycleModule599

namespace CycleCut599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def releaseAt {n : ℕ} (gs : List Gate) (v : Fin n) (j : ℕ) : Prop :=
  ∃ g i, gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → ((⟨gs,0⟩ : Circuit).wires (List.ofFn z)).getD i false=false

private theorem push_release {n j : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : releaseAt gs v j) : releaseAt (gs++[g]) v j := by
  obtain ⟨q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private theorem changed_dominated {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool)
    (agree : ∀ i, i ∉ S → x i = y i) (p : ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (only : ∀ v ∈ S, ∀ j, releaseAt gs v j → j=p)
    (same : p<gs.length → val gs x (n+p)=val gs y (n+p)) (w : ℕ)
    (hd : val gs x w ≠ val gs y w) :
    ∃ v∈S, ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    change (List.ofFn x).getD w false ≠ (List.ofFn y).getD w false at hd
    by_cases hw : w<n
    · let i : Fin n := ⟨w,hw⟩
      have hx : ∀ t : Fin n → Bool, val [] t w = t i := by
        intro t; change (List.ofFn t).getD w false=t i
        rw [List.getD_eq_getElem _ _ (by simpa using hw)]
        simp [i]
      refine ⟨i,by
        by_contra hi
        exact hd ((hx x).trans ((agree i hi).trans (hx y).symm)),?_⟩
      intro z hz
      exact (hx z).trans hz
    · exact (hd (by rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)])).elim
  | append_singleton gs g ih =>
    have hm' : ∀ q∈gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have only' : ∀ v∈S, ∀ j, releaseAt gs v j → j=p :=
      fun v hv j hj => only v hv j (push_release g hj)
    have same' (h : p<gs.length) : val gs x (n+p)=val gs y (n+p) := by
      have he := same (by simp; omega)
      simpa only [other_val gs g _ (by omega : n+p ≠ n+gs.length)] using he
    by_cases hw : w=n+gs.length
    · subst w
      have hd' := hd
      rw [new_val,new_val] at hd'
      obtain ⟨a,ha,had⟩ : ∃ a∈g.inputs, val gs x a ≠ val gs y a := by
        by_contra! h
        exact hd' (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        unfold val at had
        exact had (by rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
          List.getD_eq_default _ _ (by simpa [run_len] using h)])
      obtain ⟨v,hv,below⟩ := ih hm' only' same' a had
      rcases hm g (by simp) with hand|hor
      · refine ⟨v,hv,fun z hz => ?_⟩
        rw [new_val]
        change (g.op.eval _) = false
        rw [hand]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [below z hz]⟩
      · have atGate : releaseAt (gs++[g]) v gs.length := by
          refine ⟨g,a,by simp,hor,ha,bound,fun z hz => ?_⟩
          exact (other_val _ _ _ (Nat.ne_of_lt bound)).trans (below z hz)
        have e := only v hv _ atGate
        subst p
        exact (hd (same (by simp))).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      obtain ⟨v,hv,below⟩ := ih hm' only' same' w hd
      exact ⟨v,hv,fun z hz => (other_val _ _ _ hw).trans (below z hz)⟩

theorem factor_gate {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (x y : Fin n → Bool) (agree : ∀ i, i∉S → x i=y i)
    (same : (C.wires (List.ofFn x)).getD (n+p) false=(C.wires (List.ofFn y)).getD (n+p) false) :
    C.eval (List.ofFn x)=C.eval (List.ofFn y) := by
  by_contra hd
  obtain ⟨v,hv,below⟩ := changed_dominated S x y agree p C.gates (fun g hg => (hm g hg).1)
    only (fun _ => same) C.output hd
  obtain ⟨z,hz,ho⟩ := free v hv
  exact Bool.false_ne_true ((below z hz).symm.trans ho)

def mask {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : Bool := decide (i∈X)

theorem graph_factors {n : ℕ} (G : SimpleGraph (Fin n)) (S A B : Finset (Fin n))
    (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (hAS : A⊆S) (hBS : B⊆S)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (mask U))).getD (n+p) false=true ↔
      CycleModule599.bit A B U)
    (spec : ∀ U : Finset (Fin n), C.eval (List.ofFn (mask U))=true ↔ CycleModule599.edgeAt G U) :
    CycleModule599.factors G S A B := by
  intro X hX Y hY bits T ht
  have part (U Q : Finset (Fin n)) (hU : U⊆S) : U⊆Q∪T ↔ U⊆Q := by
    constructor
    · intro h i hi
      exact (Finset.mem_union.mp (h hi)).resolve_right (fun he => Finset.disjoint_left.mp ht he (hU hi))
    · intro h i hi
      exact Finset.mem_union_left _ (h hi)
  have beq : CycleModule599.bit A B (X∪T) ↔ CycleModule599.bit A B (Y∪T) := by
    simpa only [CycleModule599.bit,part A _ hAS,part B _ hBS] using bits
  have eq := factor_gate S C p hm only free (mask (X∪T)) (mask (Y∪T)) (by
    intro i hi
    have hx : i∉X := fun h => hi (hX h)
    have hy : i∉Y := fun h => hi (hY h)
    simp [mask,hx,hy]) (Bool.eq_iff_iff.mpr ((bit_eq _).trans (beq.trans (bit_eq _).symm)))
  exact (spec _).symm.trans ((iff_of_eq (congrArg (fun b => b = true) eq)).trans (spec _))

private theorem val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w<n+a.length) : val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih => rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private theorem out_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n+gs.length ≤ w) : val gs x w=false := by
  exact List.getD_eq_default _ _ (by simpa [run_len] using hw)

def monomial {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) := ∀ v∈A, x v=true

def principal {n : ℕ} (f : (Fin n → Bool) → Bool) :=
  (∀ x, f x=false) ∨ ∃ A : Finset (Fin n), ∀ x, f x=true ↔ monomial A x

private theorem principal_all {n : ℕ} (l : List ℕ) (z : (Fin n → Bool) → ℕ → Bool)
    (h : ∀ j∈l, principal (fun x => z x j)) : principal (fun x => (l.map (z x)).all id) := by
  induction l with
  | nil => right; exact ⟨∅,by simp [monomial]⟩
  | cons a l ih =>
    rcases h a (by simp) with ha|⟨A,ha⟩
    · left; intro x; simp [ha]
    rcases ih (fun j hj => h j (by simp [hj])) with hl|⟨B,hB⟩
    · left; intro x; simp [hl]
    right; refine ⟨A∪B,fun x => ?_⟩
    simp only [List.map_cons,List.all_cons,id_eq,Bool.and_eq_true]
    rw [ha,hB]
    simp [monomial,Finset.mem_union,or_imp,forall_and]

theorem all_and_principal {n : ℕ} (gs : List Gate)
    (hall : ∀g∈gs, g.op=.and) (w : ℕ) :
    principal (fun x : Fin n → Bool => ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD w false) := by
  change principal (fun x : Fin n → Bool => val gs x w)
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases h : w<n
    · right; refine ⟨{⟨w,h⟩},fun x => ?_⟩
      change (List.ofFn x).getD w false=true ↔ _
      rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp [monomial]
    · left; exact fun x => out_val _ _ _ (by simp; omega)
  | append_singleton gs g ih =>
    have h : ∀q∈gs, q.op=.and := fun q hq => hall q (List.mem_append_left _ hq)
    by_cases hw : w=n+gs.length
    · subst w
      simp only [new_val,readGate,hall g (by simp),GateOp.eval]
      exact principal_all _ _ (fun j _ => ih h j)
    · simpa only [other_val gs g _ hw] using ih h w

private theorem mono_antitone {n : ℕ} {A B : Finset (Fin n)} (h : A⊆B) {x : Fin n → Bool}
    (hx : monomial B x) : monomial A x := fun v hv => hx v (h hv)

theorem prefix_decision {n : ℕ} (pre post : List Gate) (g : Gate)
    (hall : ∀q∈pre, q.op=.and) (hop : g.op=.or) (hlen : g.inputs.length≤2) :
    let gs := (pre++[g])++post
    (∃ w, ∀ x : Fin n → Bool,
      ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD (n+pre.length) false =
      ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) ∨
    (∃ A B : Finset (Fin n), ¬ A⊆B ∧ ¬ B⊆A ∧
      (∀ v∈A∪B, releaseAt gs v pre.length) ∧
      (∀ U : Finset (Fin n), ((⟨gs,0⟩ : Circuit).wires (List.ofFn (mask U))).getD
        (n+pre.length) false=true ↔ CycleModule599.bit A B U)) := by
  dsimp only
  let gs := (pre++[g])++post
  have thisGate (x : Fin n → Bool) : val gs x (n+pre.length)=readGate g (val pre x) :=
    (val_prefix (pre++[g]) post x _ (by simp)).trans (new_val pre g x)
  cases hi : g.inputs with
  | nil =>
    left; refine ⟨n+pre.length,fun x => ?_⟩
    change val gs x _=val pre x _
    rw [thisGate,out_val _ _ _ (by omega)]
    simp [readGate,hop,hi,GateOp.eval]
  | cons a l =>
    cases hj : l with
    | nil =>
      left; refine ⟨a,fun x => ?_⟩
      change val gs x _=val pre x _
      rw [thisGate]; simp [readGate,hop,hi,hj,GateOp.eval]
    | cons b tail =>
      have ht : tail=[] := by apply List.length_eq_zero_iff.mp; rw [hi,hj] at hlen; simp only [List.length_cons] at hlen; omega
      subst tail
      have ins : g.inputs=[a,b] := by rw [hi,hj]
      have gate (x : Fin n → Bool) : val gs x (n+pre.length) = (val pre x a || val pre x b) := by
        rw [thisGate]; simp [readGate,hop,ins,GateOp.eval]
      have pure (w : ℕ) : principal (fun x : Fin n → Bool => val pre x w) := all_and_principal pre hall w
      rcases pure a with ha|⟨A,ha⟩
      · left; exact ⟨b,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x a=false from ha x]; simp⟩
      rcases pure b with hb|⟨B,hb⟩
      · left; exact ⟨a,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x b=false from hb x]; simp⟩
      by_cases hab : A⊆B
      · left; refine ⟨a,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_left_of_imp (mono_antitone hab)
      by_cases hba : B⊆A
      · left; refine ⟨b,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_right_of_imp (mono_antitone hba)
      right
      have charge (w : ℕ) (L : Finset (Fin n)) (hin : w∈g.inputs)
          (rep : ∀ x : Fin n → Bool, val pre x w=true ↔ monomial L x) (v : Fin n) (hv : v∈L) :
          releaseAt gs v pre.length := by
        have valid : w<n+pre.length := by
          by_contra! h
          have yes := (rep (fun _ => true)).mpr (by intro i _; rfl)
          rw [out_val _ _ _ h] at yes
          contradiction
        refine ⟨g,w,?_,hop,hin,valid,fun x hx => ?_⟩
        · rw [List.getElem?_append_left (by simp)]; simp
        · change val ((pre++[g])++post) x w=false
          rw [List.append_assoc,val_prefix _ _ _ _ valid]
          cases e : val pre x w with
          | false => rfl
          | true => exact (Bool.false_ne_true (hx.symm.trans ((rep x).mp e v hv))).elim
      refine ⟨A,B,hab,hba,?_,fun U => ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hv|hv
        · exact charge a A (by simp [ins]) ha v hv
        · exact charge b B (by simp [ins]) hb v hv
      · change val gs (mask U) _=true ↔ _
        rw [gate,Bool.or_eq_true,ha,hb]
        simp only [monomial,mask,decide_eq_true_eq,CycleModule599.bit]; rfl

theorem global_copy {n : ℕ} (pre post : List Gate) (g : Gate)
    (copy : ∃ w, ∀ x : Fin n → Bool, ((⟨(pre++[g])++post,0⟩ : Circuit).wires
      (List.ofFn x)).getD (n+pre.length) false = ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) :
    let C : Circuit := ⟨(pre++[g])++post,0⟩
    (∃ w<n+pre.length, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false =
      (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false=b := by
  obtain ⟨w,eq⟩ := copy
  by_cases h : w<n+pre.length
  · left; refine ⟨w,h,fun x => (eq x).trans ?_⟩
    change val pre x w=val ((pre++[g])++post) x w
    rw [List.append_assoc,val_prefix _ _ _ _ h]
  · right; exact ⟨false,fun x => (eq x).trans (out_val pre x w (by omega))⟩

end CycleCut599

namespace CoreFacts599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit599 PaidGraph599
open scoped Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

theorem forbids_copy (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) {p : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (same : (∃ w<n+p, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+p) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+p) false=b) : False := by
  obtain ⟨C',hm',_,heq,cover,hcard⟩ := Leaf599.discard_redundant_or C A p g hm hc hg hop same
  have hdet : detects G C' := by
    intro x
    rw [heq]
    exact h x
  have hh := best_le (show feasible G (A.erase p).card from ⟨C',A.erase p,hm',hdet,cover,rfl⟩)
  omega

theorem charged_iff_release (v : Fin n) (j : ℕ) :
    Leaf599.Charged C v j ↔ CycleCut599.releaseAt C.gates v j := by
  constructor
  · rintro ⟨i,g,hg,hop,hi,hij,hz⟩
    exact ⟨g,i,hg,hop,hi,hij,hz⟩
  · rintro ⟨g,i,hg,hop,hi,hij,hz⟩
    exact ⟨i,g,hg,hop,hi,hij,hz⟩


theorem pay_from_bit (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) (hf : GraphInduction599.noFour G)
    (degrees : ∀ u∈G.support, G.degree u = 2) (p : ℕ)
    (X Y : Finset (Fin n)) (hx : ¬ X ⊆ Y) (hy : ¬ Y ⊆ X)
    (hp : ∀ v∈X∪Y, Leaf599.Charged C v p)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (CycleCut599.mask U))).getD (n+p) false=true ↔
      CycleModule599.bit X Y U) :
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  let S := X ∪ Y
  have active : ∀ v∈S, v ∈ G.support := fun v hv => charge_is_active hm h hc hmin (hp v hv)
  by_contra hn
  have only : ∀ v∈S, ∀ j, CycleCut599.releaseAt C.gates v j → j=p := by
    intro v hv j hj
    by_contra hne
    have pay := double_saving hm h hc v hne (charged_iff_release v j |>.mpr hj) (hp v hv)
    exact hn ⟨v,active v hv,hmin ▸ pay⟩
  have free := fun v hv => accepts_core_without h degrees (active v hv)
  have spec (U : Finset (Fin n)) : C.eval (List.ofFn (CycleCut599.mask U)) = true ↔
      CycleModule599.edgeAt G U := by
    rw [h]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,hab⟩
    · rintro ⟨a,ha,b,hb,hab⟩
      exact ⟨a,b,hab,decide_eq_true ha,decide_eq_true hb⟩
  have hXS : X ⊆ S := Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right
  obtain ⟨u,hu,huy⟩ := Finset.not_subset.mp hx
  obtain ⟨v,hv,hvx⟩ := Finset.not_subset.mp hy
  have neq : u ≠ v := fun e => hvx (e ▸ hu)
  have ff := CycleCut599.graph_factors G S X Y C p hm hXS hYS only free bit_eq spec
  exact CycleModule599.no_module_of_no_four hXS hYS ⟨u,hu⟩ ⟨v,hv⟩
    ⟨u,hXS hu,v,hYS hv,neq⟩
    (fun w hw => two_neighbors (le_of_eq (degrees w (active w hw)).symm)) hf ff

end CoreFacts599

namespace Leaf599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem split_first_or (gs : List Gate)
    (hm : ∀ q ∈ gs, (q.op=.and ∨ q.op=.or) ∧ q.inputs.length≤2)
    (present : ∃ q ∈ gs, q.op=.or) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), gs=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  induction gs with
  | nil => simp at present
  | cons h t ih =>
    obtain ⟨hop,hlen⟩ := hm h List.mem_cons_self
    rcases hop with hand|hor
    · have tail : ∃ q ∈ t, q.op=.or := by
        obtain ⟨q,hq,hor⟩ := present
        rcases List.mem_cons.mp hq with rfl|hq
        · rw [hand] at hor
          cases hor
        · exact ⟨q,hq,hor⟩
      obtain ⟨a,g,b,eq,ha,hg,hl⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) tail
      refine ⟨h::a,g,b,congrArg (List.cons h) eq,?_,hg,hl⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hand
      · exact ha q hq
    · exact ⟨[],h,t,rfl,by simp,hor,hlen⟩


theorem first_or {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), C.gates=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  obtain ⟨j,g,_,hg,hop,_⟩ := release_exists C v hm on other
  exact split_first_or C.gates hm ⟨g,List.mem_of_getElem? hg,hop⟩

end Leaf599

namespace Pseudoforest599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 PaidGraph599 CoreFacts599
open scoped Classical

theorem pay_core {n : ℕ} : corePaid n := by
  intro G _ hf hg degrees
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  obtain ⟨v,hv⟩ := support_nonempty (show 0 < G.edgeSet.ncard by omega)
  obtain ⟨pre,g,post,shape,ands,hor,hlen⟩ :=
    Leaf599.first_or C v hm (one_bit h hv) (accepts_core_without h degrees hv)
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre++[g])++post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut599.prefix_decision (n:=n) pre post g ands hor hlen with copy | choice
    · exact False.elim (forbids_copy hm h hc hmin hj hor (CycleCut599.global_copy pre post g copy))
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      exact pay_from_bit hm h hc hmin hf degrees pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits

end Pseudoforest599


namespace Extensions
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 PaidGraph599 CoreFacts599
open scoped Classical

noncomputable def low {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) : Finset (Fin n) :=
  (X ∪ Y).filter fun v => G.degree v = 2

def Collision {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ X Y : Finset (Fin n), ¬ X ⊆ Y → ¬ Y ⊆ X →
    (∀ v ∈ X ∪ Y, v ∈ G.support) →
    ∃ U V : Finset (Fin n),
      (∀ i, i ∉ low G X Y → (i ∈ U ↔ i ∈ V)) ∧
      (CycleModule599.bit X Y U ↔ CycleModule599.bit X Y V) ∧
      ¬ (CycleModule599.edgeAt G U ↔ CycleModule599.edgeAt G V)

theorem accepts_min_degree {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (h : detects G C) (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u)
    {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  obtain ⟨u,hvu⟩ := G.mem_support.mp hv
  obtain ⟨a,b,hab,ha,hb⟩ := two_neighbors (degrees u hvu.mem_support_right)
  obtain ⟨w,hw,hwv⟩ : ∃ w, G.Adj u w ∧ w ≠ v := by
    by_cases he : a = v
    · exact ⟨b,hb,fun h => hab (he.trans h.symm)⟩
    · exact ⟨a,ha,he⟩
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  exact ⟨x,by simp [x], (h x).mpr ⟨u,w,hw,
    by simp [x,Function.update_of_ne hvu.ne.symm],by simp [x,Function.update_of_ne hwv]⟩⟩

theorem pay_from_collision {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}
    (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) (collision : Collision G) (p : ℕ)
    (X Y : Finset (Fin n)) (hx : ¬ X ⊆ Y) (hy : ¬ Y ⊆ X)
    (hp : ∀ v ∈ X ∪ Y, Leaf599.Charged C v p)
    (bit_eq : ∀ U : Finset (Fin n),
      (C.wires (List.ofFn (CycleCut599.mask U))).getD (n+p) false = true ↔
      CycleModule599.bit X Y U) :
    ∃ v : Fin n, G.degree v = 2 ∧ best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  by_contra hn
  have active : ∀ v ∈ low G X Y, v ∈ G.support := by
    intro v hv
    have hd := (Finset.mem_filter.mp hv).2
    exact (G.degree_pos_iff_mem_support v).mp (by omega)
  have only : ∀ v ∈ low G X Y, ∀ j, CycleCut599.releaseAt C.gates v j → j=p := by
    intro v hv j hj
    by_contra hne
    have hpv := hp v (Finset.mem_filter.mp hv).1
    have pay := double_saving hm h hc v hne ((charged_iff_release v j).mpr hj) hpv
    exact hn ⟨v,(Finset.mem_filter.mp hv).2,by simpa [hmin] using pay⟩
  obtain ⟨U,V,agree,bits,diff⟩ := collision X Y hx hy
    (fun v hv => charge_is_active hm h hc hmin (hp v hv))
  have same : (C.wires (List.ofFn (CycleCut599.mask U))).getD (n+p) false =
      (C.wires (List.ofFn (CycleCut599.mask V))).getD (n+p) false :=
    Bool.eq_iff_iff.mpr ((bit_eq U).trans (bits.trans (bit_eq V).symm))
  have eq := CycleCut599.factor_gate (low G X Y) C p hm only
    (fun v hv => accepts_min_degree h degrees (active v hv))
    (CycleCut599.mask U) (CycleCut599.mask V)
    (by intro i hi; apply Bool.eq_iff_iff.mpr; simpa [CycleCut599.mask] using agree i hi) same
  have spec (Q : Finset (Fin n)) : C.eval (List.ofFn (CycleCut599.mask Q)) = true ↔
      CycleModule599.edgeAt G Q := by
    rw [h]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,hab⟩
    · rintro ⟨a,ha,b,hb,hab⟩
      exact ⟨a,b,hab,decide_eq_true ha,decide_eq_true hb⟩
  exact diff ((spec U).symm.trans ((iff_of_eq (congrArg (fun b => b=true) eq)).trans (spec V)))

theorem pay_core_collision {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : best G + 1 < G.edgeSet.ncard)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) (collision : Collision G) :
    ∃ v : Fin n, G.degree v = 2 ∧ best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  obtain ⟨v,hv⟩ := support_nonempty (show 0 < G.edgeSet.ncard by omega)
  obtain ⟨pre,g,post,shape,ands,hor,hlen⟩ :=
    Leaf599.first_or C v hm (one_bit h hv) (accepts_min_degree h degrees hv)
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre++[g])++post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut599.prefix_decision (n:=n) pre post g ands hor hlen with copy | choice
    · exact False.elim (forbids_copy hm h hc hmin hj hor (CycleCut599.global_copy pre post g copy))
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      exact pay_from_collision hm h hc hmin degrees collision pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits


theorem best_bound_pseudoforest {n : ℕ} (G : SimpleGraph (Fin n))
    (hs : GraphInduction599.sparse G) (hf : GraphInduction599.noFour G) :
    G.edgeSet.ncard ≤ best G + 1 := by
  exact GraphInduction599.of_paid_deletions best
    (fun _ _ _ hg => PaidGraph599.leaf_paid hg) Pseudoforest599.pay_core G hs hf

theorem core_bound_of_collision {n : ℕ} (G : SimpleGraph (Fin n))
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) (collision : Collision G)
    (deletions : ∀ v : Fin n, G.degree v = 2 →
      (G.deleteIncidenceSet v).edgeSet.ncard ≤ best (G.deleteIncidenceSet v) + 1) :
    G.edgeSet.ncard ≤ best G + 1 := by
  by_contra! hg
  obtain ⟨v,hv,hpay⟩ := pay_core_collision G hg degrees collision
  have hc := GraphInduction599.count_after_delete G v
  have hd := deletions v hv
  omega

theorem collision_or_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) (collision : Collision G)
    (deletions : ∀ v : Fin n, G.degree v = 2 →
      (G.deleteIncidenceSet v).edgeSet.ncard ≤ best (G.deleteIncidenceSet v) + 1)
    (hm : Monotone2 C) (h : detects G C) (hc : covers C A) :
    G.edgeSet.ncard ≤ A.card + 1 := by
  have hh := core_bound_of_collision G degrees collision deletions
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  omega


theorem bound_from_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hv : G.degree v = 1)
    (hb : (G.deleteIncidenceSet v).edgeSet.ncard ≤ best (G.deleteIncidenceSet v) + 1) :
    G.edgeSet.ncard ≤ best G + 1 := by
  by_contra! hg
  have hp := PaidGraph599.leaf_paid hg v hv
  have hc := GraphInduction599.count_after_delete G v
  omega

theorem sparse_from_parent {n : ℕ} (G : SimpleGraph (Fin n)) (par : Fin n → Fin n)
    (hp : ∀ u v : Fin n, G.Adj u v → u = par v ∨ v = par u) :
    GraphInduction599.sparse G := by
  intro S
  have hsub : {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} ⊆
      ((S.image (fun b : Fin n => s(par b,b)) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨hadj,hS⟩ := he
      have hu : u ∈ S := hS u (by simp)
      have hv : v ∈ S := hS v (by simp)
      rw [Finset.mem_coe,Finset.mem_image]
      rcases hp u v hadj with hh | hh
      · exact ⟨v,hv,by rw [hh]⟩
      · exact ⟨u,hu,by rw [hh]; exact Sym2.eq_swap⟩
  calc _ ≤ ((S.image (fun b : Fin n => s(par b,b)) : Finset (Sym2 (Fin n))) :
        Set (Sym2 (Fin n))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (S.image (fun b : Fin n => s(par b,b))).card := Set.ncard_coe_finset _
    _ ≤ S.card := Finset.card_image_le

end Extensions

namespace FiniteBow

def bit (A B U : Finset (Fin 7)) : Prop := A ⊆ U ∨ B ⊆ U

def collision (edge : Finset (Fin 7) → Prop) (low A B : Finset (Fin 7)) : Prop :=
  ∃ U V : Finset (Fin 7), U \ ((A ∪ B) ∩ low) = V \ ((A ∪ B) ∩ low) ∧
    (bit A B U ↔ bit A B V) ∧ ¬ (edge U ↔ edge V)

abbrev edgeBow (U : Finset (Fin 7)) : Prop :=
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨
  (0 ∈ U ∧ 4 ∈ U) ∨ (1 ∈ U ∧ 2 ∈ U) ∨ (3 ∈ U ∧ 4 ∈ U)

def emb : Fin 5 ↪ Fin 7 := ⟨fun i => ⟨i.val, by omega⟩, by intro a b h; exact Fin.ext (congrArg (fun i : Fin 7 => i.val) h)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 20000 in
theorem bowtie7_smallWitness : ∀ A B : Finset (Fin 7),
    A ⊆ {0,1,2,3,4} → B ⊆ {0,1,2,3,4} → ¬ A ⊆ B → ¬ B ⊆ A →
    ∃ U V : Finset (Fin 5),
      U.map emb \ ((A ∪ B) ∩ {1,2,3,4}) = V.map emb \ ((A ∪ B) ∩ {1,2,3,4}) ∧
      (bit A B (U.map emb) ↔ bit A B (V.map emb)) ∧ ¬ (edgeBow (U.map emb) ↔ edgeBow (V.map emb)) := by
  unfold bit edgeBow emb
  decide +kernel

theorem bowtie7_collision (A B : Finset (Fin 7))
    (ha : A ⊆ {0,1,2,3,4}) (hb : B ⊆ {0,1,2,3,4}) (hab : ¬ A ⊆ B) (hba : ¬ B ⊆ A) :
    collision edgeBow {1,2,3,4} A B := by
  obtain ⟨U,V,h⟩ := bowtie7_smallWitness A B ha hb hab hba
  exact ⟨U.map emb,V.map emb,h⟩

end FiniteBow


namespace Bowtie
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def adjB (u v : Fin 7) : Bool := decide
  ((u,v) ∈ ([(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] : List (Fin 7 × Fin 7)) ∨
   (v,u) ∈ ([(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] : List (Fin 7 × Fin 7)))

def G : SimpleGraph (Fin 7) where
  Adj u v := adjB u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

noncomputable def neigh : Fin 7 → Finset (Fin 7) :=
  ![{1,2,3,4},{0,2},{0,1},{0,4},{0,3},∅,∅]

theorem neighbors (v : Fin 7) : G.neighborFinset v = neigh v := by
  apply Finset.ext
  intro u
  rw [G.mem_neighborFinset]
  have hh : ∀ v u : Fin 7, adjB v u = true ↔ u ∈ neigh v := by decide
  exact hh v u

theorem degrees (v : Fin 7) : G.degree v = ![4,2,2,2,2,0,0] v := by
  change (G.neighborFinset v).card = _
  rw [neighbors]
  fin_cases v <;> decide

theorem support (v : Fin 7) : v ∈ G.support ↔ v ∈ ({0,1,2,3,4} : Finset (Fin 7)) := by
  rw [← G.degree_pos_iff_mem_support, degrees]
  fin_cases v <;> decide

theorem min_degree : ∀ v ∈ G.support, 2 ≤ G.degree v := by
  intro v hv
  rw [support] at hv
  rw [degrees]
  fin_cases v <;> simp_all

theorem low_eq (X Y : Finset (Fin 7)) : low G X Y = (X ∪ Y) ∩ {1,2,3,4} := by
  ext v
  simp only [low,Finset.mem_filter,Finset.mem_inter]
  have hh : G.degree v = 2 ↔ v ∈ ({1,2,3,4} : Finset (Fin 7)) := by
    rw [degrees]
    fin_cases v <;> decide
  rw [hh]

theorem edgeAt (U : Finset (Fin 7)) : CycleModule599.edgeAt G U ↔ FiniteBow.edgeBow U := by
  unfold CycleModule599.edgeAt FiniteBow.edgeBow
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    change adjB a b = true at hab
    simp only [adjB,decide_eq_true_eq,List.mem_cons,List.mem_singleton,Prod.mk.injEq] at hab
    rcases hab with h | h <;> rcases h with h|h|h|h|h|h <;>
      rcases h with ⟨rfl,rfl⟩ <;> tauto
  · intro h
    rcases h with h|h|h|h|h|h
    · exact ⟨0,h.1,1,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,3,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,4,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨1,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨3,h.1,4,h.2,by change adjB _ _ = true; decide⟩

theorem collision : Collision G := by
  intro X Y hXY hYX active
  have hx : X ⊆ {0,1,2,3,4} := fun v hv => (support v).mp (active v (Finset.mem_union_left _ hv))
  have hy : Y ⊆ {0,1,2,3,4} := fun v hv => (support v).mp (active v (Finset.mem_union_right _ hv))
  obtain ⟨U,V,hd,hbit,hneq⟩ := FiniteBow.bowtie7_collision X Y hx hy hXY hYX
  refine ⟨U,V,?_,hbit,?_⟩
  · intro i hi
    rw [low_eq] at hi
    have hh := congrArg (fun T : Finset (Fin 7) => i ∈ T) hd
    simpa [Finset.mem_sdiff,hi] using iff_of_eq hh
  · simpa only [edgeAt] using hneq

def par : Fin 7 → Fin 7 → Fin 7 :=
 ![![0,1,1,3,3,5,6],![4,1,0,0,3,5,6],![4,0,2,0,3,5,6],
   ![2,0,1,3,0,5,6],![2,0,1,0,4,5,6],![0,0,0,0,0,5,6],![0,0,0,0,0,5,6]]

theorem delete_sparse (v : Fin 7) (hv : G.degree v = 2) :
    GraphInduction599.sparse (G.deleteIncidenceSet v) := by
  apply sparse_from_parent _ (par v)
  intro a b hab
  obtain ⟨hab,hav,hbv⟩ := G.deleteIncidenceSet_adj.mp hab
  have hv' : v ∈ ({1,2,3,4} : Finset (Fin 7)) := by
    rw [degrees] at hv
    fin_cases v <;> simp_all
  have orient : ∀ v a b : Fin 7, v ∈ ({1,2,3,4} : Finset (Fin 7)) →
      adjB a b = true → a ≠ v → b ≠ v → a = par v b ∨ b = par v a := by decide
  exact orient v a b hv' hab hav hbv

theorem no_four : ∀ v a b c : Fin 7, G.Adj v a → G.Adj a b → G.Adj b c → G.Adj c v →
    a ≠ c → b ≠ v → False := by
  change ∀ v a b c : Fin 7, adjB v a = true → adjB a b = true → adjB b c = true →
    adjB c v = true → a ≠ c → b ≠ v → False
  decide

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

theorem best_bound : G.edgeSet.ncard ≤ best G + 1 := by
  apply core_bound_of_collision G min_degree collision
  intro v hv
  exact best_bound_pseudoforest _ (delete_sparse v hv)
    (GraphInduction599.noFour_subgraph (G.deleteIncidenceSet_le v) noFour)


theorem edge_count : G.edgeSet.ncard = 6 := by
  let E : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(3,4)}
  have he : G.edgeSet = (E : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change adjB u v = true ↔ s(u,v) ∈ E
      fin_cases u <;> fin_cases v <;> decide
  rw [he,Set.ncard_coe_finset]
  decide

theorem or_lower (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects G C) (hc : covers C A) : 5 ≤ A.card := by
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound
  rw [edge_count] at hh
  omega

end Bowtie


-- BEGIN CASE27 ADDITION: the preceding prefix is unchanged orTheory infrastructure.
namespace Case27
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599

/-- A paid OR restriction requires an essential input and a nonzero false cofactor. -/
theorem paid_one {n : ℕ} (C : Circuit) (v : Fin n) (A : Finset ℕ)
    (hm : Monotone2 C) (hc : covers C A)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (k : ℕ)
    (lower : ∀ (D : Circuit) (B : Finset ℕ), Monotone2 D → covers D B →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) →
      k ≤ B.card) : k+1 ≤ A.card := by
  obtain ⟨D,B,hB,hM,heq,hcov⟩ := Leaf599.restrict_one C v A hm hc on other
  have hh := lower D B hM hcov heq
  omega

namespace Rename
-- Actual default-false relabeling adapted from accepted927, through LeafTotal.
lemma getD_snoc_eq (v : List Bool) (b : Bool) : (v ++ [b]).getD v.length false = b := by simp
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


theorem eval_relabel {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
  (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem mono_relabel {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  exact ⟨(hm h hh).1, by simpa [relGate] using (hm h hh).2⟩

theorem covers_relabel {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (A : Finset ℕ)
    (hc : covers C A) : covers (relabel n m π C) A := by
  intro j g hg hop
  cases ho : C.gates[j]? with
  | none => simp [relabel,List.getElem?_map,ho] at hg
  | some g0 =>
    have he : relGate n m π g0 = g := by simpa [relabel,List.getElem?_map,ho] using hg
    subst g
    exact hc j g0 ho hop
end Rename

def edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def f (x : Fin 7 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)
def f1 (x : Fin 7 → Bool) : Bool := f (Function.update x 3 false)
def f2 (x : Fin 7 → Bool) : Bool := f1 (Function.update x 4 false)
def π : Fin 7 → Fin 7 := ![1,0,2,5,6,3,4]

theorem on0 : ∃ x : Fin 7 → Bool, x 3=false ∧ f x=false ∧ f (Function.update x 3 true)=true := by decide
 theorem other0 : ∃ x : Fin 7 → Bool, x 3=false ∧ f x=true := by decide
 theorem on1 : ∃ x : Fin 7 → Bool, x 4=false ∧ f1 x=false ∧ f1 (Function.update x 4 true)=true := by decide
 theorem other1 : ∃ x : Fin 7 → Bool, x 4=false ∧ f1 x=true := by decide

theorem f2_bowtie : ∀ x : Fin 7 → Bool,
    f2 (x ∘ π) = true ↔ ∃ a b, Bowtie.G.Adj a b ∧ x a = true ∧ x b = true := by
  change ∀ x : Fin 7 → Bool,
    f2 (x ∘ π) = true ↔ ∃ a b, Bowtie.adjB a b = true ∧ x a = true ∧ x b = true
  decide +kernel

theorem or_lower (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x) (hc : covers C A) : 7 ≤ A.card := by
  refine paid_one (n := 7) C 3 A hm hc ?_ ?_ 6 ?_
  · simpa only [he] using on0
  · simpa only [he] using other0
  intro D B hD hB heD
  have eqD : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x)=f1 x := by
    intro x; rw [heD,he]; rfl
  refine paid_one (n := 7) D 4 B hD hB ?_ ?_ 5 ?_
  · simpa only [eqD] using on1
  · simpa only [eqD] using other1
  intro K R hK hR heK
  have eqK : ∀ x : Fin 7 → Bool, K.eval (List.ofFn x)=f2 x := by
    intro x; rw [heK,eqD]; rfl
  apply Bowtie.or_lower (Rename.relabel 7 7 π K) R (Rename.mono_relabel π K hK)
  · intro x
    rw [Rename.eval_relabel,eqK]
    exact f2_bowtie x
  · exact Rename.covers_relabel π K R hR

namespace Counts
-- Gate-index partition copied from the private984 integration packet.
noncomputable def opIndices (C : Circuit) (op : GateOp) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => C.gates[j]?.map Gate.op = some op)

noncomputable abbrev andIndices (C : Circuit) : Finset ℕ := opIndices C GateOp.and
noncomputable abbrev orIndices (C : Circuit) : Finset ℕ := opIndices C GateOp.or

theorem mem_opIndices (C : Circuit) (j : ℕ) (g : Gate) (op : GateOp)
    (hj : C.gates[j]? = some g) (hop : g.op = op) : j ∈ opIndices C op := by
  classical
  have hlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  unfold opIndices
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hlt, ?_⟩
  rw [hj]
  simpa using hop

theorem partition_disjoint (C : Circuit) : Disjoint (andIndices C) (orIndices C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j ha ho
  have ha' := (Finset.mem_filter.mp ha).2
  have ho' := (Finset.mem_filter.mp ho).2
  have h := ha'.symm.trans ho'
  cases h

theorem partition_union (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    andIndices C ∪ orIndices C = Finset.range C.gates.length := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with ha | ho
    · exact (Finset.mem_filter.mp ha).1
    · exact (Finset.mem_filter.mp ho).1
  · intro hj
    have hlt := Finset.mem_range.mp hj
    have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hlt
    have hg := (hm C.gates[j] (List.getElem_mem hlt)).1
    rcases hg with ha | ho
    · exact Finset.mem_union_left _ (mem_opIndices C j _ GateOp.and hget ha)
    · exact Finset.mem_union_right _ (mem_opIndices C j _ GateOp.or hget ho)

theorem partition_card (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    (andIndices C).card + (orIndices C).card = C.size := by
  classical
  rw [← Finset.card_union_of_disjoint (partition_disjoint C), partition_union C hm]
  simp [Circuit.size]

theorem total_of_and_or (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (a o : ℕ) (ha : a ≤ (andIndices C).card) (ho : o ≤ (orIndices C).card) :
    a + o ≤ C.size := by
  rw [← partition_card C hm]
  exact Nat.add_le_add ha ho

end Counts

theorem total_if_five_and (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x)
    (ha : 5 ≤ (Counts.andIndices C).card) : 12 ≤ C.size := by
  have ho : 7 ≤ (Counts.orIndices C).card :=
    or_lower C (Counts.orIndices C) hm he
      (fun j g hj hop => Counts.mem_opIndices C j g .or hj hop)
  exact Counts.total_of_and_or C hm 5 7 ha ho

theorem small_has_at_most_four_and (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x)
    (hs : C.size ≤ 11) : (Counts.andIndices C).card ≤ 4 := by
  by_contra! ha
  have hh := total_if_five_and C hm he ha
  omega

#print axioms paid_one
#print axioms or_lower
#print axioms total_if_five_and
#print axioms small_has_at_most_four_and
end Case27
end PEqualNP.Outside.L_meta_984.orTheory

namespace PEqualNP.Outside.L_meta_984.orTheory.Case27
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem and_lower_four (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x) :
    4 ≤ (Counts.andIndices C).card := by
  apply Jared984Integrate.and_lower27 C hm (Counts.andIndices C)
  · exact fun j g hj hop => Counts.mem_opIndices C j g .and hj hop
  · intro x
    rw [he]
    rfl

theorem total_lower_eleven (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x) : 11 ≤ C.size := by
  have ha := and_lower_four C hm he
  have ho : 7 ≤ (Counts.orIndices C).card :=
    or_lower C (Counts.orIndices C) hm he
      (fun j g hj hop => Counts.mem_opIndices C j g .or hj hop)
  exact Counts.total_of_and_or C hm 4 7 ha ho

theorem under_twelve_is_four_and_seven_or (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x)
    (hs : C.size < 12) :
    (Counts.andIndices C).card = 4 ∧ (Counts.orIndices C).card = 7 ∧ C.size=11 := by
  have ha := and_lower_four C hm he
  have ho : 7 ≤ (Counts.orIndices C).card :=
    or_lower C (Counts.orIndices C) hm he
      (fun j g hj hop => Counts.mem_opIndices C j g .or hj hop)
  have hp := Counts.partition_card C hm
  omega

#print axioms total_lower_eleven
#print axioms under_twelve_is_four_and_seven_or
end PEqualNP.Outside.L_meta_984.orTheory.Case27

namespace Jared984Integrate
-- Required positives omit central edge01; negatives retain the full case27 graph.
def without01 (x : Fin 7 → Bool) : Bool :=
  ([(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)] : List (Fin 7 × Fin 7)).any
    (fun e => x e.1 && x e.2)
theorem partial_and_lower_without01 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (hzero : ∀ x : Fin 7 → Bool,
      PEqualNP.Outside.L_meta_984.orTheory.Case27.f x = false → C.eval (List.ofFn x) = false)
    (hpositive : ∀ x : Fin 7 → Bool, without01 x = true → C.eval (List.ofFn x) = true) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984.orTheory.Case27.f (rowInput Jared984Four.rows27 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → without01
      (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput Jared984Four.rows27 r) (rowInput Jared984Four.rows27 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984Four.rows27 r → without01
      (Eliminate984.pin p (rowInput Jared984Four.rows27 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984.orTheory.Case27.f (Eliminate984.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family.good_eliminate_iff G).mp hG) hw
    Jared984Four.rows27 Jared984Four.witness27 Jared984Four.through27
    Jared984Four.through_injective27 Jared984Four.contains27
    (fun r => hzero _ (h0 r))
    (fun r s hn => hpositive _ (hj r s hn))
    (fun r p hn => hpositive _ (hmax r p hn))
    (fun p => hzero _ (hz p)) Jared984Four.separates27 Jared984Four.omits27
  exact hb.trans hlen


#print axioms partial_and_lower_without01
end Jared984Integrate


namespace PEqualNP.Outside.L_meta_984_partial_lift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Earlier-wire equality adapted from accepted L_meta_196.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wireCount (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]

lemma keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

-- Both circuits retain the earlier wire. When it is false the edited gate
-- computes the same value, so even the later wires agree.
lemma dropInput (gs : List Gate) (w : List Bool) (j a h : ℕ)
    (gate : gs[j]? = some ⟨.or, [a,h]⟩) (early : h < w.length + j) :
    let old := gs.foldl step w
    let new := (gs.set j ⟨.and, [a]⟩).foldl step w
    new.getD h false = old.getD h false ∧ (old.getD h false = false → new = old) := by
  induction gs generalizing w j with
  | nil => simp at gate
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gate
      subst g
      have lt : h < w.length := by simpa using early
      have oldRead := keepWire (⟨.or, [a,h]⟩ :: gs) w h lt
      have newRead := keepWire (⟨.and, [a]⟩ :: gs) w h lt
      refine ⟨newRead.trans oldRead.symm, fun hf => ?_⟩
      have off := oldRead.symm.trans hf
      change gs.foldl step (step w ⟨.and, [a]⟩) = gs.foldl step (step w ⟨.or, [a,h]⟩)
      congr 1
      change w ++ [w.getD a false && true] = w ++ [w.getD a false || (w.getD h false || false)]
      simp only [off, Bool.or_false, Bool.and_true]
    | succ j =>
      apply ih (step w g) j gate
      simp only [step, List.length_append, List.length_singleton]
      omega


-- Monotone suffix simulation adapted from checked private 952 BlockingCircuit.
def Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

lemma getD_snoc_eq (v : List Bool) (b : Bool) : (v ++ [b]).getD v.length false = b := by
  simp

lemma getD_snoc_ne (v : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ v.length) :
    (v ++ [b]).getD i false = v.getD i false := by
  by_cases hlt : i < v.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default, List.getD_eq_default] <;> simp_all <;> omega

lemma above_snoc {v v' : List Bool} {a a' : Bool} (h : Above v v')
    (ha : a = true → a' = true) : Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst i
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]
    exact ha hi
  · rw [getD_snoc_ne _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

lemma above_fold (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v', Above v v' → Above (gs.foldl step v) (gs.foldl step v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
    apply above_snoc h
    rcases hg g List.mem_cons_self with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩


lemma lower_or (gs : List Gate) (w : List Bool) (j a h : ℕ)
    (gate : gs[j]? = some ⟨.or, [a,h]⟩)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Above ((gs.set j ⟨.and, [a]⟩).foldl step w) (gs.foldl step w) := by
  induction gs generalizing w j with
  | nil => simp at gate
  | cons g gs ih =>
    have tail : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => mono k (by simp [hk])
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gate
      subst g
      change Above (gs.foldl step (step w ⟨.and, [a]⟩))
        (gs.foldl step (step w ⟨.or, [a,h]⟩))
      apply above_fold gs tail
      apply above_snoc ⟨rfl, fun _ hi => hi⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, Bool.or_eq_true]
      exact fun ha => Or.inl ha
    | succ j =>
      exact ih (step w g) j gate tail

def Pure2 (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma pure_set (gs : List Gate) (j : ℕ) (g : Gate) (hg : Pure2 g)
    (hs : ∀ a ∈ gs, Pure2 a) : ∀ a ∈ gs.set j g, Pure2 a := by
  induction gs generalizing j with
  | nil => simp
  | cons b gs ih =>
    have hb := hs b (by simp)
    have ht : ∀ a ∈ gs, Pure2 a := fun a ha => hs a (by simp [ha])
    cases j with
    | zero => simpa using (show ∀ a ∈ g :: gs, Pure2 a from by simpa using And.intro hg ht)
    | succ j =>
      simpa using (show ∀ a ∈ b :: gs.set j g, Pure2 a from by simpa using And.intro hb (ih j ht))

def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP isOr

lemma one_fewer_or (gs : List Gate) (j a h : ℕ)
    (gate : gs[j]? = some ⟨.or, [a,h]⟩) :
    orCount (gs.set j ⟨.and, [a]⟩) + 1 = orCount gs := by
  induction gs generalizing j with
  | nil => simp at gate
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gate
      subst g
      simp [orCount, List.countP_cons, isOr]
    | succ j =>
      have ht := ih j gate
      simp only [orCount, List.set_cons_succ, List.countP_cons] at ht ⊢
      omega

def edit (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨.and, [a]⟩, C.output⟩

theorem edit_monotone2 (C : Circuit) (j a : ℕ) (hc : Monotone2 C) :
    Monotone2 (edit C j a) := by
  have hp : ∀ g ∈ C.gates, Pure2 g := by
    intro g hg
    simpa [Pure2] using hc g hg
  have hs := pure_set C.gates j ⟨.and, [a]⟩ (by simp [Pure2]) hp
  simpa [Monotone2, edit, Pure2] using hs

theorem edit_output_le (C : Circuit) (j a h : ℕ)
    (gate : C.gates[j]? = some ⟨.or, [a,h]⟩) (hc : Monotone2 C)
    (w : List Bool) : (edit C j a).eval w ≤ C.eval w := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hc g hg).1
  have hl := (lower_or C.gates w j a h gate hm).2 C.output
  change ((C.gates.set j ⟨.and,[a]⟩).foldl step w).getD C.output false ≤
    (C.gates.foldl step w).getD C.output false
  generalize hx : ((C.gates.set j ⟨.and,[a]⟩).foldl step w).getD C.output false = x at *
  generalize hy : (C.gates.foldl step w).getD C.output false = y at *
  cases x <;> cases y <;> simp_all

theorem edit_output_eq (C : Circuit) (n j a h : ℕ)
    (gate : C.gates[j]? = some ⟨.or, [a,h]⟩) (early : h < n+j)
    (x : Fin n → Bool) (off : (C.wires (List.ofFn x)).getD h false = false) :
    (edit C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have he := (dropInput C.gates (List.ofFn x) j a h gate (by simpa using early)).2 off
  change ((C.gates.set j ⟨.and,[a]⟩).foldl step (List.ofFn x)).getD C.output false =
    (C.gates.foldl step (List.ofFn x)).getD C.output false
  rw [he]

theorem edit_preserves_partial_spec (C : Circuit) (n j a h : ℕ)
    (G : (Fin n → Bool) → Bool) (required : Set (Fin n → Bool))
    (gate : C.gates[j]? = some ⟨.or, [a,h]⟩) (early : h < n+j)
    (hc : Monotone2 C)
    (sound : ∀ x, C.eval (List.ofFn x) ≤ G x)
    (positive : ∀ x ∈ required, C.eval (List.ofFn x) = true)
    (off : ∀ x ∈ required, (C.wires (List.ofFn x)).getD h false = false) :
    Monotone2 (edit C j a) ∧
      orCount (edit C j a).gates + 1 = orCount C.gates ∧
      (edit C j a).gates.length = C.gates.length ∧
      (∀ x, (edit C j a).eval (List.ofFn x) ≤ G x) ∧
      (∀ x ∈ required, (edit C j a).eval (List.ofFn x) = true) := by
  refine ⟨edit_monotone2 C j a hc, one_fewer_or C.gates j a h gate,
    by simp [edit], ?_, ?_⟩
  · intro x
    exact (edit_output_le C j a h gate hc (List.ofFn x)).trans (sound x)
  · intro x hx
    rw [edit_output_eq C n j a h gate early x (off x hx)]
    exact positive x hx

#print axioms edit_monotone2
#print axioms one_fewer_or
#print axioms edit_output_le
#print axioms edit_output_eq
#print axioms edit_preserves_partial_spec
end PEqualNP.Outside.L_meta_984_partial_lift

namespace PEqualNP.Outside.L_meta_984_case27_zero
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_984_partial_lift

def cut (C : Circuit) (j : ℕ) : Circuit := ⟨C.gates.set j ⟨.or,[]⟩, C.output⟩

theorem cut_mono (C : Circuit) (j : ℕ) (hm : Monotone2 C) : Monotone2 (cut C j) := by
  have hp : ∀ g ∈ C.gates, Pure2 g := by intro g hg; simpa [Pure2] using hm g hg
  have hh := pure_set C.gates j ⟨.or,[]⟩ (by simp [Pure2]) hp
  simpa [Monotone2,cut,Pure2] using hh

theorem cut_le (gs : List Gate) (w : List Bool) (j : ℕ)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Above ((gs.set j ⟨.or,[]⟩).foldl step w) (gs.foldl step w) := by
  induction gs generalizing j w with
  | nil => exact ⟨rfl,fun _ h => h⟩
  | cons g gs ih =>
    have ht : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun a ha => hm a (by simp [ha])
    cases j with
    | zero =>
      apply above_fold gs ht
      apply above_snoc ⟨rfl,fun _ h => h⟩
      simp [GateOp.eval]
    | succ j => exact ih (step w g) j ht

theorem cut_same (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g)
    (off : (gs.foldl step w).getD (w.length+j) false=false) :
    (gs.set j ⟨.or,[]⟩).foldl step w=gs.foldl step w := by
  induction gs generalizing j w with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hj
      subst a
      have hr := keepWire gs (step w g) w.length (by simp [step])
      have hg : g.op.eval (g.inputs.map fun i => w.getD i false)=false := by
        simpa [step] using hr.symm.trans off
      change gs.foldl step (step w ⟨.or,[]⟩)=gs.foldl step (step w g)
      change gs.foldl step (w ++ [false]) =
        gs.foldl step (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      rw [hg]
    | succ j =>
      apply ih (step w a) j hj
      simpa [step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using off

theorem cut_covers {C : Circuit} {j : ℕ} {g : Gate} {A : Finset ℕ}
    (hj : C.gates[j]?=some g)
    (hc : ∀ k b, C.gates[k]?=some b → b.op=.and → k∈A) :
    ∀ k b, (cut C j).gates[k]?=some b → b.op=.and → k∈A.erase j := by
  classical
  intro k b hb hop
  by_cases hk : j=k
  · subst k
    have ht : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have he : (⟨GateOp.or,[]⟩ : Gate)=b := by simpa [cut,List.getElem?_set_self ht] using hb
    subst b
    contradiction
  · have ho : C.gates[k]?=some b := by simpa [cut,List.getElem?_set_ne hk] using hb
    exact Finset.mem_erase.mpr ⟨Ne.symm hk,hc k b ho hop⟩

theorem cut_output_le (C : Circuit) (j : ℕ) (hm : Monotone2 C) (x : List Bool) :
    (cut C j).eval x ≤ C.eval x := by
  have hh := (cut_le C.gates x j (fun g hg => by simpa using (hm g hg).1)).2 C.output
  change ((C.gates.set j ⟨.or,[]⟩).foldl step x).getD C.output false ≤
    (C.gates.foldl step x).getD C.output false
  generalize hx : ((C.gates.set j ⟨.or,[]⟩).foldl step x).getD C.output false = a at *
  generalize hy : (C.gates.foldl step x).getD C.output false = b at *
  cases a <;> cases b <;> simp_all

theorem cut_output_same (C : Circuit) (n j : ℕ) (g : Gate)
    (hj : C.gates[j]?=some g) (x : Fin n → Bool)
    (off : (C.wires (List.ofFn x)).getD (n+j) false=false) :
    (cut C j).eval (List.ofFn x)=C.eval (List.ofFn x) := by
  change (C.gates.foldl step (List.ofFn x)).getD (n+j) false=false at off
  have hh := cut_same C.gates (List.ofFn x) j g hj (by simpa only [List.length_ofFn] using off)
  change ((C.gates.set j ⟨.or,[]⟩).foldl step (List.ofFn x)).getD C.output false = _
  rw [hh]
  rfl

theorem eval_monotone (C : Circuit) (n : ℕ) (hm : Monotone2 C) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy
  have hi : Above (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i ht
    by_cases hin : i<n
    · have hx : x ⟨i,hin⟩=true := by simpa [List.getD_eq_getElem?_getD,hin] using ht
      have hy := hxy ⟨i,hin⟩
      have he : y ⟨i,hin⟩=true := le_antisymm (Bool.le_true _) (by simpa [hx] using hy)
      simpa [List.getD_eq_getElem?_getD,hin] using he
    · simp [List.getD_eq_getElem?_getD,hin] at ht
  have hh := (above_fold C.gates (fun g hg => by simpa using (hm g hg).1) _ _ hi).2 C.output
  change (C.gates.foldl step (List.ofFn x)).getD C.output false ≤
    (C.gates.foldl step (List.ofFn y)).getD C.output false
  generalize hx : (C.gates.foldl step (List.ofFn x)).getD C.output false=a at *
  generalize hy : (C.gates.foldl step (List.ofFn y)).getD C.output false=b at *
  cases a <;> cases b <;> simp_all

#print axioms cut_output_le
#print axioms cut_output_same
#print axioms cut_covers
#print axioms eval_monotone
end PEqualNP.Outside.L_meta_984_case27_zero

namespace PEqualNP.Outside.L_meta_984.orTheory.Case27
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_984_case27_zero

def without01edges : List (Fin 7 × Fin 7) := [(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def pairInput (e : Fin 7 × Fin 7) : Fin 7 → Bool := fun v => decide (v=e.1 ∨ v=e.2)

theorem no01in_other_edge : ∀ e ∈ without01edges, ¬ (pairInput e 0=true ∧ pairInput e 1=true) := by decide
 theorem other_edge_positive : ∀ e ∈ without01edges, f (pairInput e)=true := by decide

theorem and_product01_forces_five (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x)
    (j : ℕ) (g : Gate) (hj : C.gates[j]?=some g) (hg : g.op=.and)
    (dominated : ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD (7+j) false=true → x 0=true ∧ x 1=true) :
    5 ≤ (Counts.andIndices C).card := by
  classical
  let A := Counts.andIndices C
  have hcov : ∀ k b, C.gates[k]?=some b → b.op=.and → k∈A :=
    fun k b hk hb => Counts.mem_opIndices C k b .and hk hb
  have hjA : j∈A := hcov j g hj hg
  have hD := cut_mono C j hm
  have hB := cut_covers hj hcov
  have hb : 4 ≤ (A.erase j).card := by
    apply Jared984Integrate.partial_and_lower_without01 (cut C j) hD (A.erase j) hB
    · intro x hx
      have hl := cut_output_le C j hm (List.ofFn x)
      rw [he,hx] at hl
      exact le_antisymm hl (Bool.false_le _)
    · intro x hx
      change without01edges.any (fun e => x e.1 && x e.2)=true at hx
      obtain ⟨e,heE,heT⟩ := List.any_eq_true.mp hx
      have hpair : pairInput e ≤ x := by
        intro v
        by_cases hv : v=e.1 ∨ v=e.2
        · rcases hv with rfl|rfl <;> simp_all [pairInput,Bool.and_eq_true]
        · simp [pairInput,hv]
      have hoff : (C.wires (List.ofFn (pairInput e))).getD (7+j) false=false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact no01in_other_edge e heE (dominated (pairInput e) ht)
      have haccept : (cut C j).eval (List.ofFn (pairInput e))=true := by
        rw [cut_output_same C 7 j g hj (pairInput e) hoff,he]
        exact other_edge_positive e heE
      have hl := eval_monotone (cut C j) 7 hD hpair
      change (cut C j).eval (List.ofFn (pairInput e)) ≤ (cut C j).eval (List.ofFn x) at hl
      rw [haccept] at hl
      exact le_antisymm (Bool.le_true _) hl
  have hcard := Finset.card_erase_add_one hjA
  dsimp [A] at hb hcard
  omega

#print axioms and_product01_forces_five
end PEqualNP.Outside.L_meta_984.orTheory.Case27


-- BEGIN case27 selected-witness partial AND extension.
namespace Case27PartialAnd
open Eliminate984 Jared984Integrate PEqualNP.Outside.L_meta_984_family

theorem projection_avoid {G : List Eliminate984.F} (t : Trace G) (x : X) (p : Fin 7)
    (hp : x p = true) (i : Fin G.length) (b : Bool)
    (hb : t.side i b (single p) = true) : t.choice x i ≠ some b := by
  intro hc
  have hle : single p ≤ x := by
    intro q
    by_cases hq : q = p
    · subst q; simp [single,hp]
    · simp [single,hq]
  have ht : t.side i b x = true := Bool.eq_true_of_true_le
    (by simpa only [hb] using (t.side_monotone i b) hle)
  have hh := t.choice_false x i b hc
  rw [ht] at hh
  contradiction

theorem projection_hit {G : List Eliminate984.F} (t : Trace G) {f : Eliminate984.F} (hf : Eliminate984.cl G f)
    (p : Fin 7) (hz : f (single p) = false) (x : X) (hx : f x = false)
    (hmax : f (pin p x) = true) :
    ∃ i b, t.side i b (single p) = true ∧ t.choice x i = some b := by
  classical
  by_contra hn
  have hs : ∀ i b, t.choice x i = some b → t.side i b (single p) = false := by
    intro i b hc
    cases h : t.side i b (single p)
    · rfl
    · exact (hn ⟨i,b,h,hc⟩).elim
  have hG := t.unselected_invariant p x hs
  have hh := cl_false_insert p x hG hf hz hx
  rw [hmax] at hh
  contradiction

section FiniteChoice
variable {V R Q : Type*} [DecidableEq V] [DecidableEq Q] [Fintype Q]
theorem four_bound_selected (rows : R → Finset V) (lit : V → Finset (Q × Bool))
    (witness : Fin 4 → V)
    (hone : ∀ a, (lit (witness a)).card ≤ 1)
    (hne : ∀ a, (lit (witness a)).Nonempty)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r)
    (hcover : ∀ r, ∃ choice : Q → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ lit v, choice l.1 ≠ some l.2) ∧
      (∀ a, witness a ∉ rows r → ∃ l ∈ lit (witness a), choice l.1 = some l.2)) :
    4 ≤ Fintype.card Q := by
  classical
  choose pick hp using hne
  have hu (a : Fin 4) (l : Q × Bool) (hl : l ∈ lit (witness a)) : l = pick a :=
    Finset.card_le_one.mp (hone a) l hl (pick a) (hp a)
  have hi : Function.Injective (fun a => (pick a).1) := by
    intro a b hab
    change (pick a).1 = (pick b).1 at hab
    by_contra hn
    by_cases hs : (pick a).2 = (pick b).2
    · obtain ⟨r,ha,hb⟩ := hsep a b hn
      obtain ⟨choice,havoid,hhit⟩ := hcover r
      obtain ⟨l,hl,he⟩ := hhit b hb
      rw [hu b l hl] at he
      have hno := havoid (witness a) ha (pick a) (hp a)
      rw [hab,hs,he] at hno
      exact hno rfl
    · obtain ⟨r,ha,hb⟩ := homit a b hn
      obtain ⟨choice,havoid,hhit⟩ := hcover r
      obtain ⟨la,hla,hea⟩ := hhit a ha
      obtain ⟨lb,hlb,heb⟩ := hhit b hb
      rw [hu a la hla] at hea
      rw [hu b lb hlb] at heb
      rw [hab,heb] at hea
      exact hs (Option.some.inj hea).symm
  have hc := Fintype.card_le_of_injective _ hi
  simpa using hc


end FiniteChoice
theorem four_semantic_selected {G : List Eliminate984.F} (hG : Eliminate984.good G)
    {f : Eliminate984.F} (hf : Eliminate984.cl G f)
    {m : ℕ} (rows : Fin m → Finset (Fin 7)) (witness : Fin 4 → Fin 7)
    (through : Fin 4 → Fin 3 → Fin m)
    (hthrough : ∀ a, Function.Injective (through a))
    (hcontains : ∀ a i, witness a ∈ rows (through a i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (PEqualNP.Outside.L_meta_984_family.joinInput (rowInput rows r) (rowInput rows s)) = true)
    (hmax : ∀ r a, witness a ∉ rows r → f (Eliminate984.pin (witness a) (rowInput rows r)) = true)
    (hz : ∀ p, f (Eliminate984.single p) = false)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r) :
    4 ≤ G.length := by
  classical
  by_contra hn
  have hsize : G.length ≤ 3 := by omega
  let t := Eliminate984.traceOfGood hG
  let lit (p : Fin 7) : Finset (Fin G.length × Bool) :=
    Finset.univ.filter (fun z => t.side z.1 z.2 (Eliminate984.single p) = true)
  have hlit (a : Fin 4) : (lit (witness a)).card = 1 := by
    have hev := events_le_one t hf hsize rows (witness a) (through a) (hthrough a) (hcontains a) h0 hjoin
    have hess : ∃ x, Eliminate984.res (witness a) f x ≠ f x := by
      obtain ⟨b,hb⟩ := exists_ne a
      obtain ⟨r,hbr,har⟩ := hsep b a hb
      refine ⟨rowInput rows r, ?_⟩
      change f (Eliminate984.pin (witness a) (rowInput rows r)) ≠ f (rowInput rows r)
      rw [hmax r a har,h0 r]
      decide
    have hside := t.unique_side (witness a) hf (hz (witness a)) hess hev
    simpa only [lit,← t.sides_eq_card (witness a)] using hside
  have hcover : ∀ r, ∃ choice : Fin G.length → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ lit v, choice l.1 ≠ some l.2) ∧
      (∀ a, witness a ∉ rows r → ∃ l ∈ lit (witness a), choice l.1 = some l.2) := by
    intro r
    refine ⟨t.choice (rowInput rows r), ?_, ?_⟩
    · intro v hv l hl
      exact projection_avoid t (rowInput rows r) v (by simpa [rowInput] using hv)
        l.1 l.2 (Finset.mem_filter.mp hl).2
    · intro a ha
      obtain ⟨i,b,ht,hc⟩ := projection_hit t hf (witness a) (hz (witness a))
        (rowInput rows r) (h0 r) (hmax r a ha)
      exact ⟨(i,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,hc⟩
  have hfour := four_bound_selected rows lit witness
    (fun a => (hlit a).le)
    (fun a => Finset.card_pos.mp (by rw [hlit a]; omega)) hsep homit hcover
  simp only [Fintype.card_fin] at hfour
  omega


def witness : Fin 4 → Fin 7 := ![3,4,5,6]
def through : Fin 4 → Fin 3 → Fin 8 := ![![0,3,6],![1,4,7],![2,3,4],![5,6,7]]
def required : Fin 2 → List (Fin 7 × Fin 7) :=
  ![[(0,1),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)],
    [(0,1),(0,2),(0,3),(0,4),(1,5),(1,6),(3,4),(5,6)]]

theorem through_injective : ∀ a, Function.Injective (through a) := by decide +kernel
theorem contains : ∀ a i, witness a ∈ Jared984Four.rows27 (through a i) := by decide +kernel
theorem separates : ∀ a b, a ≠ b → ∃ r, witness a ∈ Jared984Four.rows27 r ∧ witness b ∉ Jared984Four.rows27 r := by decide +kernel
theorem omits : ∀ a b, a ≠ b → ∃ r, witness a ∉ Jared984Four.rows27 r ∧ witness b ∉ Jared984Four.rows27 r := by decide +kernel

theorem required_joins : ∀ k r s, r ≠ s → edgeFun (required k)
    (joinInput (rowInput Jared984Four.rows27 r) (rowInput Jared984Four.rows27 s)) = true := by
  decide +kernel

theorem required_selected_insert : ∀ k r a, witness a ∉ Jared984Four.rows27 r →
    edgeFun (required k) (pin (witness a) (rowInput Jared984Four.rows27 r)) = true := by
  decide +kernel

theorem parent_rows_false : ∀ r, edgeFun Jared984Four.edges27
    (rowInput Jared984Four.rows27 r) = false := by decide +kernel

theorem parent_singletons_false : ∀ p, edgeFun Jared984Four.edges27 (single p) = false := by
  decide +kernel

theorem partial_and_lower (k : Fin 2) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (positive : ∀ x : Fin 7 → Bool, edgeFun (required k) x ≤ C.eval (List.ofFn x))
    (sound : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) ≤ edgeFun Jared984Four.edges27 x) :
    4 ≤ A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hz : ∀ p, C.eval (List.ofFn (single p)) = false := by
    intro p
    exact le_antisymm (by simpa only [parent_singletons_false] using sound (single p))
      (Bool.false_le _)
  have hzero : ∀ r, C.eval (List.ofFn (rowInput Jared984Four.rows27 r)) = false := by
    intro r
    exact le_antisymm (by simpa only [parent_rows_false] using sound (rowInput Jared984Four.rows27 r))
      (Bool.false_le _)
  have hjoin : ∀ r s, r ≠ s → C.eval (List.ofFn
      (joinInput (rowInput Jared984Four.rows27 r) (rowInput Jared984Four.rows27 s))) = true := by
    intro r s hrs
    exact Bool.eq_true_of_true_le (by simpa only [required_joins k r s hrs] using
      (positive (joinInput (rowInput Jared984Four.rows27 r) (rowInput Jared984Four.rows27 s))))
  have hmax : ∀ r a, witness a ∉ Jared984Four.rows27 r →
      C.eval (List.ofFn (pin (witness a) (rowInput Jared984Four.rows27 r))) = true := by
    intro r a ha
    exact Bool.eq_true_of_true_le (by simpa only [required_selected_insert k r a ha] using
      (positive (pin (witness a) (rowInput Jared984Four.rows27 r))))
  have hb := four_semantic_selected ((good_eliminate_iff G).mp hG) hw
    Jared984Four.rows27 witness through through_injective contains hzero hjoin hmax hz separates omits
  exact hb.trans hlen

#print axioms four_semantic_selected
#print axioms partial_and_lower
end Case27PartialAnd
-- END case27 selected-witness partial AND extension.

namespace PEqualNP.Outside.L_meta_984.orTheory.Case27
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_984_case27_zero

def centralTail : Fin 2 → Fin 7 × Fin 7 := ![(0,2),(1,2)]

theorem no_tail_in_other_edge : ∀ k e, e ∈ Case27PartialAnd.required k →
    ¬ (pairInput e (centralTail k).1=true ∧ pairInput e (centralTail k).2=true) := by decide
 theorem tail_other_edge_positive : ∀ k e, e ∈ Case27PartialAnd.required k →
    f (pairInput e)=true := by decide

theorem and_central_tail_forces_five (k : Fin 2) (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=f x)
    (j : ℕ) (g : Gate) (hj : C.gates[j]?=some g) (hg : g.op=.and)
    (dominated : ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD (7+j) false=true →
        x (centralTail k).1=true ∧ x (centralTail k).2=true) :
    5 ≤ (Counts.andIndices C).card := by
  classical
  let A := Counts.andIndices C
  have hcov : ∀ q b, C.gates[q]?=some b → b.op=.and → q∈A :=
    fun q b hq hb => Counts.mem_opIndices C q b .and hq hb
  have hjA : j∈A := hcov j g hj hg
  have hD := cut_mono C j hm
  have hB := cut_covers hj hcov
  have hb : 4 ≤ (A.erase j).card := by
    apply Case27PartialAnd.partial_and_lower k (cut C j) hD (A.erase j) hB
    · intro x
      cases hx : PEqualNP.Outside.L_meta_984_family.edgeFun (Case27PartialAnd.required k) x with
      | false => exact Bool.false_le _
      | true =>
        change (Case27PartialAnd.required k).any (fun e => x e.1 && x e.2)=true at hx
        obtain ⟨e,heE,heT⟩ := List.any_eq_true.mp hx
        have hpair : pairInput e ≤ x := by
          intro v
          by_cases hv : v=e.1 ∨ v=e.2
          · rcases hv with rfl|rfl <;> simp_all [pairInput,Bool.and_eq_true]
          · simp [pairInput,hv]
        have hoff : (C.wires (List.ofFn (pairInput e))).getD (7+j) false=false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          exact no_tail_in_other_edge k e heE (dominated (pairInput e) ht)
        have haccept : (cut C j).eval (List.ofFn (pairInput e))=true := by
          rw [cut_output_same C 7 j g hj (pairInput e) hoff,he]
          exact tail_other_edge_positive k e heE
        have hl := eval_monotone (cut C j) 7 hD hpair
        change (cut C j).eval (List.ofFn (pairInput e)) ≤ (cut C j).eval (List.ofFn x) at hl
        rwa [haccept] at hl
    · intro x
      have hh := cut_output_le C j hm (List.ofFn x)
      rw [he] at hh
      exact hh
  have hcard := Finset.card_erase_add_one hjA
  dsimp [A] at hb hcard
  omega

#print axioms and_central_tail_forces_five
end PEqualNP.Outside.L_meta_984.orTheory.Case27
