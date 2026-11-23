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

namespace DensePartial984
open PEqualNP.Outside.L_meta_984_family Eliminate984 Jared984Integrate

theorem selected_four_semantic {G : List Eliminate984.F} (hG : Eliminate984.good G)
    {f : Eliminate984.F} (hf : Eliminate984.cl G f)
    {m : ℕ} (rows : Fin m → Finset (Fin 7)) (witness : Fin 4 → Fin 7)
    (through : Fin 4 → Fin 3 → Fin m)
    (hthrough : ∀ a, Function.Injective (through a))
    (hcontains : ∀ a i, witness a ∈ rows (through a i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (joinInput (rowInput rows r) (rowInput rows s)) = true)
    (hmax : ∀ r a, witness a ∉ rows r → f (Eliminate984.pin (witness a) (rowInput rows r)) = true)
    (hz : ∀ p, f (Eliminate984.single p) = false)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r) :
    4 ≤ G.length := by
  classical
  by_contra hn
  have hsize : G.length ≤ 3 := by omega
  let t := Eliminate984.traceOfGood hG
  let lit (a : Fin 4) : Finset (Fin G.length × Bool) :=
    Finset.univ.filter (fun z => t.side z.1 z.2 (Eliminate984.single (witness a)) = true)
  let smallRows (r : Fin m) : Finset (Fin 4) := Finset.univ.filter (fun a => witness a ∈ rows r)
  have hlit (a : Fin 4) : (lit a).card = 1 := by
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
      (∀ a ∈ smallRows r, ∀ l ∈ lit a, choice l.1 ≠ some l.2) ∧
      (∀ a, a ∉ smallRows r → ∃ l ∈ lit a, choice l.1 = some l.2) := by
    intro r
    refine ⟨t.choice (rowInput rows r), ?_, ?_⟩
    · intro a ha l hl hc
      have hp : rowInput rows r (witness a) = true := by
        simpa [smallRows,rowInput] using ha
      have hle : Eliminate984.single (witness a) ≤ rowInput rows r := by
        intro q
        by_cases hq : q = witness a
        · subst q
          simp [Eliminate984.single,hp]
        · simp [Eliminate984.single,hq]
      have hb := (Finset.mem_filter.mp hl).2
      have ht : t.side l.1 l.2 (rowInput rows r) = true :=
        Bool.eq_true_of_true_le (by simpa only [hb] using (t.side_monotone l.1 l.2) hle)
      have hh := t.choice_false (rowInput rows r) l.1 l.2 hc
      rw [ht] at hh
      contradiction
    · intro a ha
      by_contra hn
      have hs : ∀ i b, t.choice (rowInput rows r) i = some b →
          t.side i b (Eliminate984.single (witness a)) = false := by
        intro i b hc
        cases ht : t.side i b (Eliminate984.single (witness a))
        · rfl
        · exact (hn ⟨(i,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,hc⟩).elim
      have hinv := t.unselected_invariant (witness a) (rowInput rows r) hs
      have hh := cl_false_insert (witness a) (rowInput rows r) hinv hf (hz (witness a)) (h0 r)
      have hna : witness a ∉ rows r := by simpa [smallRows] using ha
      rw [hmax r a hna] at hh
      contradiction
  have hs : ∀ a b : Fin 4, a ≠ b → ∃ r, a ∈ smallRows r ∧ b ∉ smallRows r := by
    intro a b hn
    obtain ⟨r,ha,hb⟩ := hsep a b hn
    exact ⟨r,by simpa [smallRows] using ha,by simpa [smallRows] using hb⟩
  have ho : ∀ a b : Fin 4, a ≠ b → ∃ r, a ∉ smallRows r ∧ b ∉ smallRows r := by
    intro a b hn
    obtain ⟨r,ha,hb⟩ := homit a b hn
    exact ⟨r,by simpa [smallRows] using ha,by simpa [smallRows] using hb⟩
  have hfour := Jared984Four.four_bound smallRows lit (fun a => a)
    (fun a => (hlit a).le) (fun a => Finset.card_pos.mp (by rw [hlit a]; omega)) hs ho hcover
  simp only [Fintype.card_fin] at hfour
  omega

def part28_01_edges : List (Fin 7 × Fin 7) := [(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]

theorem part28_01 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (hlo : ∀ x : Fin 7 → Bool, edgeFun part28_01_edges x = true → C.eval (List.ofFn x) = true)
    (hhi : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true → edgeFun Jared984Four.edges28 x = true) :
    4 ≤ A.card := by
  have h0 : ∀ r, edgeFun Jared984Four.edges28 (rowInput Jared984Four.rows28 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → edgeFun part28_01_edges
      (joinInput (rowInput Jared984Four.rows28 r) (rowInput Jared984Four.rows28 s)) = true := by decide +kernel
  have hmax : ∀ r a, Jared984Four.witness28 a ∉ Jared984Four.rows28 r → edgeFun part28_01_edges
      (Eliminate984.pin (Jared984Four.witness28 a) (rowInput Jared984Four.rows28 r)) = true := by decide +kernel
  have hz : ∀ p, edgeFun Jared984Four.edges28 (Eliminate984.single p) = false := by decide +kernel
  have neg (x : Fin 7 → Bool) (hx : edgeFun Jared984Four.edges28 x = false) : C.eval (List.ofFn x) = false := by
    rw [Bool.eq_false_iff]
    intro ht
    have hh := hhi x ht
    rw [hx] at hh
    contradiction
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hb := selected_four_semantic ((good_eliminate_iff G).mp hG) hw
    Jared984Four.rows28 Jared984Four.witness28 Jared984Four.through28
    Jared984Four.through_injective28 Jared984Four.contains28
    (fun r => neg _ (h0 r))
    (fun r s hn => hlo _ (hj r s hn))
    (fun r a hn => hlo _ (hmax r a hn))
    (fun p => neg _ (hz p)) Jared984Four.separates28 Jared984Four.omits28
  exact hb.trans hlen

def part28_03_edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]

theorem part28_03 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (hlo : ∀ x : Fin 7 → Bool, edgeFun part28_03_edges x = true → C.eval (List.ofFn x) = true)
    (hhi : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true → edgeFun Jared984Four.edges28 x = true) :
    4 ≤ A.card := by
  have h0 : ∀ r, edgeFun Jared984Four.edges28 (rowInput Jared984Four.rows28 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → edgeFun part28_03_edges
      (joinInput (rowInput Jared984Four.rows28 r) (rowInput Jared984Four.rows28 s)) = true := by decide +kernel
  have hmax : ∀ r a, Jared984Four.witness28 a ∉ Jared984Four.rows28 r → edgeFun part28_03_edges
      (Eliminate984.pin (Jared984Four.witness28 a) (rowInput Jared984Four.rows28 r)) = true := by decide +kernel
  have hz : ∀ p, edgeFun Jared984Four.edges28 (Eliminate984.single p) = false := by decide +kernel
  have neg (x : Fin 7 → Bool) (hx : edgeFun Jared984Four.edges28 x = false) : C.eval (List.ofFn x) = false := by
    rw [Bool.eq_false_iff]
    intro ht
    have hh := hhi x ht
    rw [hx] at hh
    contradiction
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hb := selected_four_semantic ((good_eliminate_iff G).mp hG) hw
    Jared984Four.rows28 Jared984Four.witness28 Jared984Four.through28
    Jared984Four.through_injective28 Jared984Four.contains28
    (fun r => neg _ (h0 r))
    (fun r s hn => hlo _ (hj r s hn))
    (fun r a hn => hlo _ (hmax r a hn))
    (fun p => neg _ (hz p)) Jared984Four.separates28 Jared984Four.omits28
  exact hb.trans hlen

def part30_03_edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]

theorem part30_03 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (hlo : ∀ x : Fin 7 → Bool, edgeFun part30_03_edges x = true → C.eval (List.ofFn x) = true)
    (hhi : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true → edgeFun Jared984Four.edges30 x = true) :
    4 ≤ A.card := by
  have h0 : ∀ r, edgeFun Jared984Four.edges30 (rowInput Jared984Four.rows30 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → edgeFun part30_03_edges
      (joinInput (rowInput Jared984Four.rows30 r) (rowInput Jared984Four.rows30 s)) = true := by decide +kernel
  have hmax : ∀ r a, Jared984Four.witness30 a ∉ Jared984Four.rows30 r → edgeFun part30_03_edges
      (Eliminate984.pin (Jared984Four.witness30 a) (rowInput Jared984Four.rows30 r)) = true := by decide +kernel
  have hz : ∀ p, edgeFun Jared984Four.edges30 (Eliminate984.single p) = false := by decide +kernel
  have neg (x : Fin 7 → Bool) (hx : edgeFun Jared984Four.edges30 x = false) : C.eval (List.ofFn x) = false := by
    rw [Bool.eq_false_iff]
    intro ht
    have hh := hhi x ht
    rw [hx] at hh
    contradiction
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  have hb := selected_four_semantic ((good_eliminate_iff G).mp hG) hw
    Jared984Four.rows30 Jared984Four.witness30 Jared984Four.through30
    Jared984Four.through_injective30 Jared984Four.contains30
    (fun r => neg _ (h0 r))
    (fun r s hn => hlo _ (hj r s hn))
    (fun r a hn => hlo _ (hmax r a hn))
    (fun p => neg _ (hz p)) Jared984Four.separates30 Jared984Four.omits30
  exact hb.trans hlen

end DensePartial984
#print axioms DensePartial984.selected_four_semantic
#print axioms DensePartial984.part28_01
#print axioms DensePartial984.part28_03
#print axioms DensePartial984.part30_03
