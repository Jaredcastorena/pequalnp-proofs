import Mathlib
import PEqualNP.Defs


/-! Conditional integration of the checked AND-count arguments and supplied
OR-count premises. This does not assert the missing OR premises.
The semantic closure helpers adapt the public L-meta-597 argument. -/


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

/-! Adapted by Boolean duality from accepted L-meta-597 semantic closure argument.
The input-wire default stays false. Free OR closure includes true as an explicit constant.
This file proves only compression into semantic OR closures, not the984 lower bound. -/

namespace Eliminate984Six

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def inputs : List F := (fun _ => true) :: List.ofFn (fun i x => x i)
def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.any (fun f => f x)
def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x && v x)) ∧ good G

def pin (p : Fin 6) (x : X) : X := Function.update x p true
def single (p : Fin 6) : X := fun q => decide (q = p)
def res (p : Fin 6) (f : F) : F := fun x => f (pin p x)
def invariant (p : Fin 6) (f : F) : Prop := ∀ x, res p f x = f x

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

theorem inputs_res (p : Fin 6) (H : List F) (f : F) (hf : f ∈ inputs) : cl H (res p f) := by
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

theorem map_cl (p : Fin 6) {G H : List F}
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

theorem true_after_pin (p : Fin 6) {G : List F} (hG : good G) {w : F}
    (hw : cl G w) (ht : w (single p) = true) : ∀ x, res p w x = true := by
  intro x
  have hs : single p ≤ pin p x := by
    intro q
    by_cases hq : q = p
    · subst q; simp [single, pin]
    · simp [single, pin, hq]
  have hh := cl_monotone (good_monotone hG) hw hs
  exact le_antisymm (Bool.le_true _) (by simpa [ht, res] using hh)

theorem closure_false_invariant_of_false_members (p : Fin 6) {G : List F}
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

theorem closure_false_invariant (p : Fin 6) {G : List F}
    (hG : ∀ g ∈ G, invariant p g) {w : F} (hw : cl G w)
    (hz : w (single p) = false) : invariant p w :=
  closure_false_invariant_of_false_members p (fun g hg _ => hG g hg) hw hz

theorem elimination_or_invariant (p : Fin 6) {G : List F} (hG : good G) :
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

theorem eliminate_essential_vertex (p : Fin 6) {G : List F} (hG : good G)
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

def Trace.events (p : Fin 6) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.events p + if u (single p) || v (single p) then 1 else 0

theorem Trace.pin_all_events (p : Fin 6) {G : List F} (t : Trace G) :
    ∃ H : List F, Eliminate984Six.good H ∧ H.length + t.events p ≤ G.length ∧
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

def Trace.asym (p : Fin 6) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.asym p + if u (single p) = v (single p) then 0 else 1

def Trace.sides (p : Fin 6) : {G : List F} → Trace G → Nat
  | _, .nil => 0
  | _, .cons _ u v _ _ _ tail =>
      tail.sides p + (if u (single p) then 1 else 0) + (if v (single p) then 1 else 0)

theorem Trace.zero_asym_invariant (p : Fin 6) {G : List F} (t : Trace G) :
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

theorem Trace.sides_asym (p : Fin 6) {G : List F} (t : Trace G) :
    t.sides p + t.asym p = 2 * t.events p := by
  induction t with
  | nil => rfl
  | cons g u v hu hv he tail ih =>
    cases hx : u (single p) <;> cases hy : v (single p) <;>
      simp [Trace.sides,Trace.asym,Trace.events,hx,hy] <;> omega

theorem Trace.essential_has_asym (p : Fin 6) {G : List F} (t : Trace G)
    {f : F} (hf : cl G f) (hz : f (single p) = false)
    (hess : ∃ x, res p f x ≠ f x) : 1 ≤ t.asym p := by
  by_contra hn
  have hzero : t.asym p = 0 := by omega
  obtain ⟨x,hx⟩ := hess
  exact hx (t.zero_asym_invariant p hzero f hf hz x)

theorem Trace.asym_le_events (p : Fin 6) {G : List F} (t : Trace G) :
    t.asym p ≤ t.events p := by
  induction t with
  | nil => simp [Trace.asym,Trace.events]
  | cons g u v hu hv he tail ih =>
    cases hx : u (single p) <;> cases hy : v (single p) <;>
      simp [Trace.asym,Trace.events,hx,hy] <;> omega

theorem Trace.unique_side (p : Fin 6) {G : List F} (t : Trace G)
    {f : F} (hf : cl G f) (hz : f (single p) = false)
    (hess : ∃ x, res p f x ≠ f x) (hevents : t.events p ≤ 1) :
    t.sides p = 1 := by
  have ha := t.essential_has_asym p hf hz hess
  have hi := t.sides_asym p
  have hae := t.asym_le_events p
  omega

end Eliminate984Six


namespace PEqualNP.Outside.L_meta_984_family6

open PEqualNP.CircuitLowerBounds

abbrev F := (Fin 6 → Bool) → Bool

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

theorem gate_or (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_false G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gate_and (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, cl_true G, cl_true G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 6 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 6 → Bool) → Bool :=
  fun x => (W gs x).getD k false

theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 6 → Bool) :
    (W gs x).length = 6 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 6 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 6 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 6 + gs.length
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
      have h3 : ¬ (k - (6 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 6
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
        by_cases hk : k = 6 + gs.length
        · rw [if_pos hk]; exact cl_new _ _
        · rw [if_neg hk]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 6 + gs.length
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
def joinInput (x y : Fin 6 → Bool) : Fin 6 → Bool := fun i => x i || y i

theorem cl_merge {G : List F} {x y : Fin 6 → Bool}
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
    ∃ code : (Fin 6 → Bool) → (Fin G.length → Bool),
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
    {m : ℕ} (M : Fin m → (Fin 6 → Bool))
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
    {m : ℕ} (M : Fin m → (Fin 6 → Bool))
    (h0 : ∀ i, C.eval (List.ofFn (M i)) = false)
    (h1 : ∀ i j, i ≠ j → C.eval (List.ofFn (joinInput (M i) (M j))) = true) :
    m ≤ 2^A.card := by
  obtain ⟨G,hG,hlen,hw⟩ := circuit_compression C hm A hA
  exact (family_bound hG hw M h0 h1).trans (Nat.pow_le_pow_right (by omega) hlen)


def edgeFun (E : List (Fin 6 × Fin 6)) (x : Fin 6 → Bool) : Bool :=
  E.any (fun e => x e.1 && x e.2)

theorem good_eliminate_iff (G : List F) : good G ↔ Eliminate984Six.good G := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    simp only [good, Eliminate984Six.good, ← ih]
    rfl


end PEqualNP.Outside.L_meta_984_family6
namespace Eliminate984Six
def Trace.side : {G : List F} → Trace G → Fin G.length → Bool → F
  | _, .nil, i => Fin.elim0 i
  | _, .cons _ u v _ _ _ tail, i => Fin.cases (fun b => if b then v else u) (tail.side) i

def Trace.choice {G : List F} (t : Trace G) (x : X) (i : Fin G.length) : Option Bool :=
  if t.side i false x = false then some false
  else if t.side i true x = false then some true else none

theorem cl_false_insert (p : Fin 6) {G : List F}
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

theorem Trace.unselected_invariant (p : Fin 6) {G : List F} (t : Trace G) (x : X)
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


theorem sum_bool_nat (f : Bool → Nat) : (∑ b : Bool, f b) = f false + f true := by
  have hh : (Finset.univ : Finset Bool) = {false,true} := by decide
  rw [hh]
  simp

 theorem Trace.sides_eq_sum (p : Fin 6) {G : List F} (t : Trace G) :
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

 theorem Trace.sides_eq_card (p : Fin 6) {G : List F} (t : Trace G) :
    t.sides p = (Finset.univ.filter (fun z : Fin G.length × Bool =>
      t.side z.1 z.2 (single p) = true)).card := by
  rw [Trace.sides_eq_sum]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sum_bool_nat (fun b => if t.side i b (single p) then 1 else 0)).symm



end Eliminate984Six
namespace Jared984FourSix

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



end Jared984FourSix
namespace Jared984IntegrateSix
open PEqualNP.Outside.L_meta_984_family6
open Eliminate984Six

def rowInput {m : ℕ} (rows : Fin m → Finset (Fin 6)) (r : Fin m) : Eliminate984Six.X :=
  fun p => decide (p ∈ rows r)

theorem pin_eq (p : Fin 6) (x : Eliminate984Six.X) (h : x p = true) : Eliminate984Six.pin p x = x := by
  simp [Eliminate984Six.pin, ← h]

theorem events_le_one {G : List Eliminate984Six.F} (t : Eliminate984Six.Trace G)
    {f : Eliminate984Six.F} (hf : Eliminate984Six.cl G f) (hsize : G.length ≤ 3)
    {m : ℕ} (rows : Fin m → Finset (Fin 6)) (p : Fin 6) (through : Fin 3 → Fin m)
    (hinj : Function.Injective through)
    (hcontains : ∀ i, p ∈ rows (through i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (PEqualNP.Outside.L_meta_984_family6.joinInput (rowInput rows r) (rowInput rows s)) = true) :
    t.events p ≤ 1 := by
  obtain ⟨H,hH,hlen,hmap⟩ := t.pin_all_events p
  have hp (i : Fin 3) : Eliminate984Six.pin p (rowInput rows (through i)) = rowInput rows (through i) :=
    pin_eq p _ (by simp [rowInput,hcontains])
  have hj (i j : Fin 3) : Eliminate984Six.pin p (PEqualNP.Outside.L_meta_984_family6.joinInput (rowInput rows (through i)) (rowInput rows (through j))) =
      PEqualNP.Outside.L_meta_984_family6.joinInput (rowInput rows (through i)) (rowInput rows (through j)) :=
    pin_eq p _ (by simp [PEqualNP.Outside.L_meta_984_family6.joinInput,rowInput,hcontains])
  have hb := PEqualNP.Outside.L_meta_984_family6.family_bound
    ((PEqualNP.Outside.L_meta_984_family6.good_eliminate_iff H).mpr hH) (hmap f hf)
    (fun i : Fin 3 => rowInput rows (through i))
    (fun i => by simpa only [Eliminate984Six.res,hp] using h0 (through i))
    (fun i j hn => by simpa only [Eliminate984Six.res,hj] using hjoin (through i) (through j) (fun h => hn (hinj h)))
  have htwo : 2 ≤ H.length := by
    by_contra hn
    have hl : H.length ≤ 1 := by omega
    have hh := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hl
    norm_num at hh
    omega
  omega



theorem four_semantic {G : List Eliminate984Six.F} (hG : Eliminate984Six.good G)
    {f : Eliminate984Six.F} (hf : Eliminate984Six.cl G f)
    {m : ℕ} (rows : Fin m → Finset (Fin 6)) (witness : Fin 4 → Fin 6)
    (through : Fin 4 → Fin 3 → Fin m)
    (hthrough : ∀ a, Function.Injective (through a))
    (hcontains : ∀ a i, witness a ∈ rows (through a i))
    (h0 : ∀ r, f (rowInput rows r) = false)
    (hjoin : ∀ r s, r ≠ s → f (PEqualNP.Outside.L_meta_984_family6.joinInput (rowInput rows r) (rowInput rows s)) = true)
    (hmax : ∀ r p, p ∉ rows r → f (Eliminate984Six.pin p (rowInput rows r)) = true)
    (hz : ∀ p, f (Eliminate984Six.single p) = false)
    (hsep : ∀ a b, a ≠ b → ∃ r, witness a ∈ rows r ∧ witness b ∉ rows r)
    (homit : ∀ a b, a ≠ b → ∃ r, witness a ∉ rows r ∧ witness b ∉ rows r) :
    4 ≤ G.length := by
  classical
  by_contra hn
  have hsize : G.length ≤ 3 := by omega
  let t := Eliminate984Six.traceOfGood hG
  let lit (p : Fin 6) : Finset (Fin G.length × Bool) :=
    Finset.univ.filter (fun z => t.side z.1 z.2 (Eliminate984Six.single p) = true)
  have hlit (a : Fin 4) : (lit (witness a)).card = 1 := by
    have hev := events_le_one t hf hsize rows (witness a) (through a) (hthrough a) (hcontains a) h0 hjoin
    have hess : ∃ x, Eliminate984Six.res (witness a) f x ≠ f x := by
      obtain ⟨b,hb⟩ := exists_ne a
      obtain ⟨r,hbr,har⟩ := hsep b a hb
      refine ⟨rowInput rows r, ?_⟩
      change f (Eliminate984Six.pin (witness a) (rowInput rows r)) ≠ f (rowInput rows r)
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
  have hfour := Jared984FourSix.four_bound rows lit witness
    (fun a => (hlit a).le)
    (fun a => Finset.card_pos.mp (by rw [hlit a]; omega)) hsep homit hcover
  simp only [Fintype.card_fin] at hfour
  omega



end Jared984IntegrateSix

namespace Jared984FourSix
def edges0 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def rows0 : Fin 8 → Finset (Fin 6) := ![{1,3},{2,3},{0,4},{1,4},{2,4},{0,5},{1,5},{2,5}]
def witness0 : Fin 4 → Fin 6 := ![1,2,4,5]
def through0 : Fin 4 → Fin 3 → Fin 8 := ![![0,3,6],![1,4,7],![2,3,4],![5,6,7]]
theorem contains0 : ∀ a b, witness0 a ∈ rows0 (through0 a b) := by decide +kernel
theorem through_injective0 : ∀ a, Function.Injective (through0 a) := by decide +kernel
theorem separates0 : ∀ a b, a ≠ b → ∃ r, witness0 a ∈ rows0 r ∧ witness0 b ∉ rows0 r := by decide +kernel
theorem omits0 : ∀ a b, a ≠ b → ∃ r, witness0 a ∉ rows0 r ∧ witness0 b ∉ rows0 r := by decide +kernel
end Jared984FourSix
namespace Jared984IntegrateSix
theorem and_lower0 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (A : Finset ℕ)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_984_family6.edgeFun Jared984FourSix.edges0 x) :
    4 ≤ A.card := by
  have h0 : ∀ r, PEqualNP.Outside.L_meta_984_family6.edgeFun Jared984FourSix.edges0 (rowInput Jared984FourSix.rows0 r) = false := by decide +kernel
  have hj : ∀ r s, r ≠ s → PEqualNP.Outside.L_meta_984_family6.edgeFun Jared984FourSix.edges0
      (PEqualNP.Outside.L_meta_984_family6.joinInput (rowInput Jared984FourSix.rows0 r) (rowInput Jared984FourSix.rows0 s)) = true := by decide +kernel
  have hmax : ∀ r p, p ∉ Jared984FourSix.rows0 r → PEqualNP.Outside.L_meta_984_family6.edgeFun Jared984FourSix.edges0
      (Eliminate984Six.pin p (rowInput Jared984FourSix.rows0 r)) = true := by decide +kernel
  have hz : ∀ p, PEqualNP.Outside.L_meta_984_family6.edgeFun Jared984FourSix.edges0 (Eliminate984Six.single p) = false := by decide +kernel
  obtain ⟨G,hG,hlen,hw⟩ := PEqualNP.Outside.L_meta_984_family6.circuit_compression C hm A hA
  have hb := four_semantic ((PEqualNP.Outside.L_meta_984_family6.good_eliminate_iff G).mp hG) hw
    Jared984FourSix.rows0 Jared984FourSix.witness0 Jared984FourSix.through0
    Jared984FourSix.through_injective0 Jared984FourSix.contains0
    (fun r => (he _).trans (h0 r))
    (fun r s hn => (he _).trans (hj r s hn))
    (fun r p hn => (he _).trans (hmax r p hn))
    (fun p => (he _).trans (hz p)) Jared984FourSix.separates0 Jared984FourSix.omits0
  exact hb.trans hlen


end Jared984IntegrateSix

namespace PEqualNP.Outside.L_meta_984_combine
open PEqualNP.CircuitLowerBounds

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

end PEqualNP.Outside.L_meta_984_combine
namespace PEqualNP.Outside.L_meta_984_combine
open PEqualNP.CircuitLowerBounds

def TotalClaim0 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size)

def ORClaim0 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))) →
    6 ≤ (orIndices C).card

theorem conditional0 (hOR : ORClaim0) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984IntegrateSix.and_lower0 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family6.edgeFun, Jared984FourSix.edges0, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim1 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim1 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional1 (hOR : ORClaim1) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower1 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges1, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim2 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size)

def ORClaim2 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional2 (hOR : ORClaim2) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower2 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges2, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim3 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size)

def ORClaim3 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional3 (hOR : ORClaim3) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower3 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges3, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim4 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size)

def ORClaim4 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional4 (hOR : ORClaim4) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower4 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges4, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim5 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim5 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional5 (hOR : ORClaim5) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower5 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges5, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim6 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim6 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional6 (hOR : ORClaim6) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower6 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges6, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim7 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size)

def ORClaim7 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5))) →
    6 ≤ (orIndices C).card

theorem conditional7 (hOR : ORClaim7) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower7 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges7, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim8 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim8 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6))) →
    6 ≤ (orIndices C).card

theorem conditional8 (hOR : ORClaim8) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower8 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges8, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 6 hAnd (hOR C hm he)

def TotalClaim9 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size)

def ORClaim9 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4))) →
    7 ≤ (orIndices C).card

theorem conditional9 (hOR : ORClaim9) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower9 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges9, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim10 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size)

def ORClaim10 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4))) →
    7 ≤ (orIndices C).card

theorem conditional10 (hOR : ORClaim10) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower10 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges10, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim11 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim11 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional11 (hOR : ORClaim11) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower11 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges11, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim12 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size)

def ORClaim12 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4))) →
    7 ≤ (orIndices C).card

theorem conditional12 (hOR : ORClaim12) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower12 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges12, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim13 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size)

def ORClaim13 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4))) →
    7 ≤ (orIndices C).card

theorem conditional13 (hOR : ORClaim13) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower13 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges13, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim14 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size)

def ORClaim14 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional14 (hOR : ORClaim14) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower14 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges14, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim15 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim15 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional15 (hOR : ORClaim15) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower15 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges15, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim16 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim16 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional16 (hOR : ORClaim16) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower16 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges16, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim17 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim17 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional17 (hOR : ORClaim17) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower17 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges17, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim18 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim18 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional18 (hOR : ORClaim18) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower18 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges18, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim19 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size)

def ORClaim19 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional19 (hOR : ORClaim19) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower19 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges19, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim20 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size)

def ORClaim20 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5))) →
    7 ≤ (orIndices C).card

theorem conditional20 (hOR : ORClaim20) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower20 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges20, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim21 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim21 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional21 (hOR : ORClaim21) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower21 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges21, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim22 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size)

def ORClaim22 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional22 (hOR : ORClaim22) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) := by
  intro C hm he
  have hAnd : 3 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower22 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges22, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 3 7 hAnd (hOR C hm he)

def TotalClaim23 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim23 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional23 (hOR : ORClaim23) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower23 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges23, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim24 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size)

def ORClaim24 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional24 (hOR : ORClaim24) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower24 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges24, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim25 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size)

def ORClaim25 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6))) →
    7 ≤ (orIndices C).card

theorem conditional25 (hOR : ORClaim25) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower25 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges25, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 7 hAnd (hOR C hm he)

def TotalClaim26 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size)

def ORClaim26 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))) →
    8 ≤ (orIndices C).card

theorem conditional26 (hOR : ORClaim26) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    PEqualNP.Outside.L_meta_984_family.and_lower26 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, PEqualNP.Outside.L_meta_984_family.edges26, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 8 hAnd (hOR C hm he)

def TotalClaim27 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size)

def ORClaim27 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6))) →
    8 ≤ (orIndices C).card

theorem conditional27 (hOR : ORClaim27) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower27 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges27, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 8 hAnd (hOR C hm he)

def TotalClaim28 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size)

def ORClaim28 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6))) →
    8 ≤ (orIndices C).card

theorem conditional28 (hOR : ORClaim28) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower28 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges28, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 8 hAnd (hOR C hm he)

def TotalClaim29 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size)

def ORClaim29 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6))) →
    8 ≤ (orIndices C).card

theorem conditional29 (hOR : ORClaim29) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower29 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges29, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 8 hAnd (hOR C hm he)

def TotalClaim30 : Prop := (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size)

def ORClaim30 : Prop := ∀ C : Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6))) →
    8 ≤ (orIndices C).card

theorem conditional30 (hOR : ORClaim30) : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  intro C hm he
  have hAnd : 4 ≤ (andIndices C).card :=
    Jared984Integrate.and_lower30 C hm (andIndices C)
      (fun j g hj hop => mem_opIndices C j g GateOp.and hj hop)
      (by
        intro x
        simpa [PEqualNP.Outside.L_meta_984_family.edgeFun, Jared984Four.edges30, Bool.or_assoc] using he x)
  exact total_of_and_or C hm 4 8 hAnd (hOR C hm he)

/-- Assemble direct total proofs or conditional proofs supplied route by route. -/
theorem assemble_exact
    (h0 : TotalClaim0)
    (h1 : TotalClaim1)
    (h2 : TotalClaim2)
    (h3 : TotalClaim3)
    (h4 : TotalClaim4)
    (h5 : TotalClaim5)
    (h6 : TotalClaim6)
    (h7 : TotalClaim7)
    (h8 : TotalClaim8)
    (h9 : TotalClaim9)
    (h10 : TotalClaim10)
    (h11 : TotalClaim11)
    (h12 : TotalClaim12)
    (h13 : TotalClaim13)
    (h14 : TotalClaim14)
    (h15 : TotalClaim15)
    (h16 : TotalClaim16)
    (h17 : TotalClaim17)
    (h18 : TotalClaim18)
    (h19 : TotalClaim19)
    (h20 : TotalClaim20)
    (h21 : TotalClaim21)
    (h22 : TotalClaim22)
    (h23 : TotalClaim23)
    (h24 : TotalClaim24)
    (h25 : TotalClaim25)
    (h26 : TotalClaim26)
    (h27 : TotalClaim27)
    (h28 : TotalClaim28)
    (h29 : TotalClaim29)
    (h30 : TotalClaim30) :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩

/-- Exact posted31-case conclusion, conditional on the31 explicitly named OR claims. -/
theorem conditional_exact
    (hOR0 : ORClaim0)
    (hOR1 : ORClaim1)
    (hOR2 : ORClaim2)
    (hOR3 : ORClaim3)
    (hOR4 : ORClaim4)
    (hOR5 : ORClaim5)
    (hOR6 : ORClaim6)
    (hOR7 : ORClaim7)
    (hOR8 : ORClaim8)
    (hOR9 : ORClaim9)
    (hOR10 : ORClaim10)
    (hOR11 : ORClaim11)
    (hOR12 : ORClaim12)
    (hOR13 : ORClaim13)
    (hOR14 : ORClaim14)
    (hOR15 : ORClaim15)
    (hOR16 : ORClaim16)
    (hOR17 : ORClaim17)
    (hOR18 : ORClaim18)
    (hOR19 : ORClaim19)
    (hOR20 : ORClaim20)
    (hOR21 : ORClaim21)
    (hOR22 : ORClaim22)
    (hOR23 : ORClaim23)
    (hOR24 : ORClaim24)
    (hOR25 : ORClaim25)
    (hOR26 : ORClaim26)
    (hOR27 : ORClaim27)
    (hOR28 : ORClaim28)
    (hOR29 : ORClaim29)
    (hOR30 : ORClaim30) :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact ⟨conditional0 hOR0, conditional1 hOR1, conditional2 hOR2, conditional3 hOR3, conditional4 hOR4, conditional5 hOR5, conditional6 hOR6, conditional7 hOR7, conditional8 hOR8, conditional9 hOR9, conditional10 hOR10, conditional11 hOR11, conditional12 hOR12, conditional13 hOR13, conditional14 hOR14, conditional15 hOR15, conditional16 hOR16, conditional17 hOR17, conditional18 hOR18, conditional19 hOR19, conditional20 hOR20, conditional21 hOR21, conditional22 hOR22, conditional23 hOR23, conditional24 hOR24, conditional25 hOR25, conditional26 hOR26, conditional27 hOR27, conditional28 hOR28, conditional29 hOR29, conditional30 hOR30⟩

end PEqualNP.Outside.L_meta_984_combine

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


namespace BowtieLeaves
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def edges : Fin 8 → List (Fin 7 × Fin 7) :=
 ![[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]]
def adjB (i : Fin 8) (u v : Fin 7) : Bool := decide ((u,v) ∈ edges i ∨ (v,u) ∈ edges i)
def G (i : Fin 8) : SimpleGraph (Fin 7) where
  Adj u v := adjB i u v = true
  symm := ⟨by
    have hh : ∀ i u v, adjB i u v = true → adjB i v u = true := by decide
    exact hh i⟩
  loopless := ⟨by
    have hh : ∀ i u, ¬adjB i u u = true := by decide
    exact hh i⟩
def first : Fin 8 → Fin 7 := ![5,5,5,6,5,5,5,6]
def second : Fin 8 → Fin 7 := ![6,6,6,5,6,6,6,5]
def H (i : Fin 8) := (G i).deleteIncidenceSet (first i)

theorem first_degree (i : Fin 8) : (G i).degree (first i) = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  have hh : ∀ i : Fin 8, ∃! w : Fin 7, adjB i (first i) w = true := by unfold ExistsUnique; decide
  exact hh i

theorem second_degree (i : Fin 8) (hi : i ≠ 0) : (H i).degree (second i) = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  have hh : ∀ i : Fin 8, i ≠ 0 → ∃! w : Fin 7,
      adjB i (second i) w = true ∧ second i ≠ first i ∧ w ≠ first i := by unfold ExistsUnique; decide
  simpa only [H,SimpleGraph.deleteIncidenceSet_adj,G] using hh i hi

theorem zero_eq : H 0 = Bowtie.G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [H,SimpleGraph.deleteIncidenceSet_adj]
  change (adjB 0 u v = true ∧ u ≠ first 0 ∧ v ≠ first 0) ↔ Bowtie.adjB u v = true
  have hh : ∀ u v : Fin 7,
      (adjB 0 u v = true ∧ u ≠ first 0 ∧ v ≠ first 0) ↔ Bowtie.adjB u v = true := by decide
  exact hh u v

theorem second_eq (i : Fin 8) (hi : i ≠ 0) : (H i).deleteIncidenceSet (second i) = Bowtie.G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [SimpleGraph.deleteIncidenceSet_adj,H,SimpleGraph.deleteIncidenceSet_adj]
  change ((adjB i u v = true ∧ u ≠ first i ∧ v ≠ first i) ∧ u ≠ second i ∧ v ≠ second i) ↔ Bowtie.adjB u v = true
  have hh : ∀ i : Fin 8, i ≠ 0 → ∀ u v : Fin 7,
      ((adjB i u v = true ∧ u ≠ first i ∧ v ≠ first i) ∧ u ≠ second i ∧ v ≠ second i) ↔ Bowtie.adjB u v = true := by decide
  exact hh i hi u v

theorem best_bound (i : Fin 8) : (G i).edgeSet.ncard ≤ best (G i) + 1 := by
  apply bound_from_leaf _ _ (first_degree i)
  change (H i).edgeSet.ncard ≤ best (H i) + 1
  by_cases hi : i = 0
  · subst i
    rw [zero_eq]
    exact Bowtie.best_bound
  · apply bound_from_leaf _ _ (second_degree i hi)
    rw [second_eq i hi]
    exact Bowtie.best_bound

theorem edge_count (i : Fin 8) : (G i).edgeSet.ncard = if i = 0 then 7 else 8 := by
  have h1 := GraphInduction599.count_after_delete (G i) (first i)
  rw [first_degree] at h1
  change (H i).edgeSet.ncard + 1 = _ at h1
  by_cases hi : i = 0
  · subst i
    rw [zero_eq,Bowtie.edge_count] at h1
    simpa using h1.symm
  · have h2 := GraphInduction599.count_after_delete (H i) (second i)
    rw [second_degree i hi,second_eq i hi,Bowtie.edge_count] at h2
    simp only [hi,ite_false]
    omega

theorem or_lower (i : Fin 8) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects (G i) C) (hc : covers C A) : (if i = 0 then 6 else 7) ≤ A.card := by
  have hb := best_le (show feasible (G i) A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound i
  rw [edge_count] at hh
  split_ifs at * <;> omega


theorem detects_of_eval (i : Fin 8) (C : Circuit)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (edges i).any (fun e => x e.1 && x e.2)) :
    detects (G i) C := by
  intro x
  rw [he]
  simp only [List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,hab,ha,hb⟩
    refine ⟨a,b,?_,ha,hb⟩
    change decide ((a,b) ∈ edges i ∨ (b,a) ∈ edges i) = true
    exact decide_eq_true (Or.inl hab)
  · rintro ⟨a,b,hab,ha,hb⟩
    change decide ((a,b) ∈ edges i ∨ (b,a) ∈ edges i) = true at hab
    rcases of_decide_eq_true hab with hab|hab
    · exact ⟨(a,b),hab,ha,hb⟩
    · exact ⟨(b,a),hab,hb,ha⟩

theorem or_lower_eval (i : Fin 8) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (edges i).any (fun e => x e.1 && x e.2))
    (hc : covers C A) : (if i = 0 then 6 else 7) ≤ A.card :=
  or_lower i C A hm (detects_of_eval i C he) hc

end BowtieLeaves

namespace PseudoforestRoutes
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def edges : Fin 6 → List (Fin 7 × Fin 7) := ![[(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)],[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)],[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)],[(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)],[(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)],[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)]]
def adjB (i : Fin 6) (u v : Fin 7) : Bool := decide ((u,v) ∈ edges i ∨ (v,u) ∈ edges i)
def G (i : Fin 6) : SimpleGraph (Fin 7) where
  Adj u v := adjB i u v = true
  symm := ⟨by
    have hh : ∀ i u v, adjB i u v = true → adjB i v u = true := by decide +kernel
    exact hh i⟩
  loopless := ⟨by
    have hh : ∀ i u, ¬adjB i u u = true := by decide +kernel
    exact hh i⟩
def E : Fin 6 → Finset (Sym2 (Fin 7)) := ![{s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(3,5),s(4,6)},{s(0,1),s(0,2),s(0,3),s(1,2),s(1,4),s(3,5),s(4,6)},{s(0,1),s(0,2),s(0,3),s(1,2),s(3,4),s(3,5),s(4,6)},{s(0,1),s(0,2),s(0,3),s(1,2),s(3,4),s(4,5),s(5,6)},{s(0,1),s(0,2),s(0,3),s(1,2),s(4,5),s(4,6),s(5,6)},{s(0,1),s(0,2),s(0,3),s(1,4),s(2,5),s(3,6),s(4,5)}]

theorem edge_count (i : Fin 6) : (G i).edgeSet.ncard = 7 := by
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

theorem no_four : ∀ i : Fin 6, ∀ v a b c : Fin 7,
    (G i).Adj v a → (G i).Adj a b → (G i).Adj b c → (G i).Adj c v →
    a ≠ c → b ≠ v → False := by
  change ∀ i : Fin 6, ∀ v a b c : Fin 7,
    adjB i v a = true → adjB i a b = true → adjB i b c = true → adjB i c v = true →
    a ≠ c → b ≠ v → False
  decide +kernel

theorem noFour (i : Fin 6) : GraphInduction599.noFour (G i) := by
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

def par : Fin 6 → Fin 7 → Fin 7 := ![![2,0,1,0,0,3,4],![2,0,1,0,1,3,4],![2,0,1,0,3,3,4],![2,0,1,0,3,4,5],![2,0,1,0,6,4,5],![2,0,5,0,1,4,3]]

theorem sparse (i : Fin 6) : GraphInduction599.sparse (G i) := by
  apply sparse_from_parent _ (par i)
  have hh : ∀ i : Fin 6, ∀ u v : Fin 7,
      adjB i u v = true → u = par i v ∨ v = par i u := by decide +kernel
  exact hh i

theorem best_bound (i : Fin 6) : (G i).edgeSet.ncard ≤ best (G i) + 1 :=
  best_bound_pseudoforest _ (sparse i) (noFour i)

theorem or_lower_detects (i : Fin 6) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects (G i) C) (hc : covers C A) : 6 ≤ A.card := by
  have hb := best_le (show feasible (G i) A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound i
  rw [edge_count] at hh
  omega

def edgeFun (i : Fin 6) (x : Fin 7 → Bool) : Bool :=
  (edges i).any (fun e => x e.1 && x e.2)

theorem edgeFun_detects : ∀ i : Fin 6, ∀ x : Fin 7 → Bool,
    edgeFun i x = true ↔ ∃ u v, adjB i u v = true ∧ x u = true ∧ x v = true := by decide +kernel

theorem or_lower (i : Fin 6) (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeFun i x)
    (hc : ∀ j g, C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) : 6 ≤ A.card := by
  apply or_lower_detects i C A hm ?_ hc
  intro x
  rw [he x]
  exact edgeFun_detects i x

end PseudoforestRoutes


namespace Finite18

def bit (A B U : Finset (Fin 7)) : Prop := A ⊆ U ∨ B ⊆ U

def collision (edge : Finset (Fin 7) → Prop) (A B : Finset (Fin 7)) : Prop :=
  ∃ U V : Finset (Fin 7), U \ ((A ∪ B) ∩ {1,2,3,4,5,6}) = V \ ((A ∪ B) ∩ {1,2,3,4,5,6}) ∧
    (bit A B U ↔ bit A B V) ∧ ¬ (edge U ↔ edge V)

def small : List (Finset (Fin 7)) := [∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {2,3}, {2,4}, {2,5}, {2,6}, {3,4}, {3,5}, {3,6}, {4,5}, {4,6}, {5,6}, {0,5,6}]
def pick (i : Fin 30) : Finset (Fin 7) := small.getD i.val ∅

abbrev edge18 (U : Finset (Fin 7)) : Prop :=
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨
  (0 ∈ U ∧ 4 ∈ U) ∨ (1 ∈ U ∧ 2 ∈ U) ∨ (3 ∈ U ∧ 5 ∈ U) ∨
  (4 ∈ U ∧ 6 ∈ U) ∨ (5 ∈ U ∧ 6 ∈ U)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 20000 in
theorem small_witness18 : ∀ A B : Finset (Fin 7), ¬ A ⊆ B → ¬ B ⊆ A →
    ∃ u v : Fin 30,
      pick u \ ((A ∪ B) ∩ {1,2,3,4,5,6}) = pick v \ ((A ∪ B) ∩ {1,2,3,4,5,6}) ∧
      (bit A B (pick u) ↔ bit A B (pick v)) ∧ ¬ (edge18 (pick u) ↔ edge18 (pick v)) := by
  unfold bit edge18 pick small
  decide +kernel

theorem collision18 (A B : Finset (Fin 7)) (hab : ¬ A ⊆ B) (hba : ¬ B ⊆ A) :
    collision edge18 A B := by
  obtain ⟨u,v,h⟩ := small_witness18 A B hab hba
  exact ⟨pick u,pick v,h⟩


end Finite18

namespace OneHub18
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions
open scoped Classical

def adjB (u v : Fin 7) : Bool := decide
  ((u,v) ∈ ([(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)] : List (Fin 7 × Fin 7)) ∨
   (v,u) ∈ ([(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)] : List (Fin 7 × Fin 7)))

def G : SimpleGraph (Fin 7) where
  Adj u v := adjB u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

noncomputable def neigh : Fin 7 → Finset (Fin 7) :=
  ![{1,2,3,4},{0,2},{0,1},{0,5},{0,6},{3,6},{4,5}]

theorem neighbors (v : Fin 7) : G.neighborFinset v = neigh v := by
  apply Finset.ext
  intro u
  rw [G.mem_neighborFinset]
  have hh : ∀ v u : Fin 7, adjB v u = true ↔ u ∈ neigh v := by decide
  exact hh v u

theorem degrees (v : Fin 7) : G.degree v = ![4,2,2,2,2,2,2] v := by
  change (G.neighborFinset v).card = _
  rw [neighbors]
  fin_cases v <;> decide

theorem support (v : Fin 7) : v ∈ G.support ↔ v ∈ ({0,1,2,3,4,5,6} : Finset (Fin 7)) := by
  rw [← G.degree_pos_iff_mem_support, degrees]
  fin_cases v <;> decide

theorem min_degree : ∀ v ∈ G.support, 2 ≤ G.degree v := by
  intro v hv
  rw [support] at hv
  rw [degrees]
  fin_cases v <;> simp_all

theorem low_eq (X Y : Finset (Fin 7)) : low G X Y = (X ∪ Y) ∩ {1,2,3,4,5,6} := by
  ext v
  simp only [low,Finset.mem_filter,Finset.mem_inter]
  have hh : G.degree v = 2 ↔ v ∈ ({1,2,3,4,5,6} : Finset (Fin 7)) := by
    rw [degrees]
    fin_cases v <;> decide
  rw [hh]

theorem edgeAt (U : Finset (Fin 7)) : CycleModule599.edgeAt G U ↔ Finite18.edge18 U := by
  unfold CycleModule599.edgeAt Finite18.edge18
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    change adjB a b = true at hab
    simp only [adjB,decide_eq_true_eq,List.mem_cons,List.mem_singleton,Prod.mk.injEq] at hab
    rcases hab with h | h <;> rcases h with h|h|h|h|h|h|h|h <;>
      rcases h with ⟨rfl,rfl⟩ <;> tauto
  · intro h
    rcases h with h|h|h|h|h|h|h|h
    · exact ⟨0,h.1,1,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,3,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,4,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨1,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨3,h.1,5,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨4,h.1,6,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨5,h.1,6,h.2,by change adjB _ _ = true; decide⟩

theorem collision : Collision G := by
  intro X Y hXY hYX active
  obtain ⟨U,V,hd,hbit,hneq⟩ := Finite18.collision18 X Y hXY hYX
  refine ⟨U,V,?_,hbit,?_⟩
  · intro i hi
    rw [low_eq] at hi
    have hh := congrArg (fun T : Finset (Fin 7) => i ∈ T) hd
    simpa [Finset.mem_sdiff,hi] using iff_of_eq hh
  · simpa only [edgeAt] using hneq

def par : Fin 7 → Fin 7 → Fin 7 :=
 ![![0,2,2,5,6,6,6],![3,1,0,5,0,6,4],![3,0,2,5,0,6,4],![1,2,0,3,0,6,4],![1,2,0,0,4,3,5],![1,2,0,0,0,5,4],![1,2,0,0,0,3,6]]

theorem delete_sparse (v : Fin 7) (hv : G.degree v = 2) :
    GraphInduction599.sparse (G.deleteIncidenceSet v) := by
  apply sparse_from_parent _ (par v)
  intro a b hab
  obtain ⟨hab,hav,hbv⟩ := G.deleteIncidenceSet_adj.mp hab
  have hv' : v ∈ ({1,2,3,4,5,6} : Finset (Fin 7)) := by
    rw [degrees] at hv
    fin_cases v <;> simp_all
  have orient : ∀ v a b : Fin 7, v ∈ ({1,2,3,4,5,6} : Finset (Fin 7)) →
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


theorem edge_count : G.edgeSet.ncard = 8 := by
  let E : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(3,5),s(4,6),s(5,6)}
  have he : G.edgeSet = (E : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change adjB u v = true ↔ s(u,v) ∈ E
      fin_cases u <;> fin_cases v <;> decide
  rw [he,Set.ncard_coe_finset]
  decide

theorem or_lower (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects G C) (hc : covers C A) : 7 ≤ A.card := by
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound
  rw [edge_count] at hh
  omega

def edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)]

theorem detects_of_eval (C : Circuit)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2)) :
    detects G C := by
  intro x
  rw [he]
  simp only [List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,hab,ha,hb⟩
    refine ⟨a,b,?_,ha,hb⟩
    change decide ((a,b) ∈ edges ∨ (b,a) ∈ edges) = true
    exact decide_eq_true (Or.inl hab)
  · rintro ⟨a,b,hab,ha,hb⟩
    change decide ((a,b) ∈ edges ∨ (b,a) ∈ edges) = true at hab
    rcases of_decide_eq_true hab with hab|hab
    · exact ⟨(a,b),hab,ha,hb⟩
    · exact ⟨(b,a),hab,hb,ha⟩

theorem or_lower_eval (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2))
    (hc : covers C A) : 7 ≤ A.card :=
  or_lower C A hm (detects_of_eval C he) hc

end OneHub18



namespace Windmill
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 Extensions

def edgesK : Fin 3 → List (Fin 7 × Fin 7) := ![[(0,3),(0,4),(0,5),(0,6),(3,4),(5,6)],[(0,1),(0,2),(0,5),(0,6),(1,2),(5,6)],[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]]
def adjK (k : Fin 3) (a b : Fin 7) : Bool := decide ((a,b) ∈ edgesK k ∨ (b,a) ∈ edgesK k)
def K (k : Fin 3) : SimpleGraph (Fin 7) where
  Adj a b := adjK k a b = true
  symm := ⟨by have h : ∀ k a b, adjK k a b = true → adjK k b a = true := by decide
              exact h k⟩
  loopless := ⟨by have h : ∀ k a, ¬adjK k a a = true := by decide
                  exact h k⟩
def active : Fin 3 → Finset (Fin 7) := ![{0,3,4,5,6},{0,1,2,5,6},{0,1,2,3,4}]
def leaves : Fin 3 → Finset (Fin 7) := ![{3,4,5,6},{1,2,5,6},{1,2,3,4}]
def positions : Fin 3 → Fin 5 → Fin 7 := ![![0,3,4,5,6],![0,1,2,5,6],![0,1,2,3,4]]
def emb (k : Fin 3) : Fin 5 ↪ Fin 7 := ⟨positions k, by
  have h : ∀ k a b, positions k a = positions k b → a = b := by decide
  exact h k⟩
def bit (A B U : Finset (Fin 7)) : Prop := A ⊆ U ∨ B ⊆ U
def edgeK (k : Fin 3) (U : Finset (Fin 7)) : Prop :=
  ∃ a ∈ U, ∃ b ∈ U, adjK k a b = true
set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxSize 20000 in
theorem smallWitness : ∀ k : Fin 3, ∀ A B : Finset (Fin 7),
    A ⊆ active k → B ⊆ active k → ¬ A ⊆ B → ¬ B ⊆ A →
    ∃ U V : Finset (Fin 5),
      U.map (emb k) \ ((A ∪ B) ∩ leaves k) = V.map (emb k) \ ((A ∪ B) ∩ leaves k) ∧
      (bit A B (U.map (emb k)) ↔ bit A B (V.map (emb k))) ∧
      ¬ (edgeK k (U.map (emb k)) ↔ edgeK k (V.map (emb k))) := by
  unfold bit edgeK emb
  decide +kernel

open scoped Classical
noncomputable def neighK : Fin 3 → Fin 7 → Finset (Fin 7) := ![![{3,4,5,6},∅,∅,{0,4},{0,3},{0,6},{0,5}],![{1,2,5,6},{0,2},{0,1},∅,∅,{0,6},{0,5}],![{1,2,3,4},{0,2},{0,1},{0,4},{0,3},∅,∅]]
def degK : Fin 3 → Fin 7 → ℕ := ![![4,0,0,2,2,2,2],![4,2,2,0,0,2,2],![4,2,2,2,2,0,0]]
theorem neighborsK (k : Fin 3) (v : Fin 7) : (K k).neighborFinset v = neighK k v := by
  apply Finset.ext
  intro u
  rw [(K k).mem_neighborFinset]
  have h : ∀ k v u, adjK k v u = true ↔ u ∈ neighK k v := by decide
  exact h k v u
theorem degreesK (k : Fin 3) (v : Fin 7) : (K k).degree v = degK k v := by
  change ((K k).neighborFinset v).card = _
  rw [neighborsK]
  have h : ∀ k v, (neighK k v).card = degK k v := by decide
  exact h k v
theorem supportK (k : Fin 3) (v : Fin 7) : v ∈ (K k).support ↔ v ∈ active k := by
  rw [←(K k).degree_pos_iff_mem_support,degreesK]
  have h : ∀ k v, 0 < degK k v ↔ v ∈ active k := by decide
  exact h k v
theorem min_degreeK (k : Fin 3) : ∀ v ∈ (K k).support, 2 ≤ (K k).degree v := by
  intro v hv
  rw [supportK] at hv
  rw [degreesK]
  have h : ∀ k v, v ∈ active k → 2 ≤ degK k v := by decide
  exact h k v hv
theorem lowK (k : Fin 3) (X Y : Finset (Fin 7)) : low (K k) X Y = (X ∪ Y) ∩ leaves k := by
  ext v
  simp only [low,Finset.mem_filter,Finset.mem_inter,degreesK]
  have h : ∀ k v, degK k v = 2 ↔ v ∈ leaves k := by decide
  rw [h]
theorem collisionK (k : Fin 3) : Collision (K k) := by
  intro X Y hXY hYX act
  have hx : X ⊆ active k := fun v hv => (supportK k v).mp (act v (Finset.mem_union_left _ hv))
  have hy : Y ⊆ active k := fun v hv => (supportK k v).mp (act v (Finset.mem_union_right _ hv))
  obtain ⟨U,V,hd,hbit,hneq⟩ := smallWitness k X Y hx hy hXY hYX
  refine ⟨U.map (emb k),V.map (emb k),?_,hbit,hneq⟩
  intro i hi
  rw [lowK] at hi
  have hh := congrArg (fun T : Finset (Fin 7) => i ∈ T) hd
  simpa [Finset.mem_sdiff,hi] using iff_of_eq hh

def parK : Fin 3 → Fin 7 → Fin 7 → Fin 7 := ![![![0,1,2,4,4,6,6],![0,1,2,3,4,5,6],![0,1,2,3,4,5,6],![5,1,2,3,0,6,0],![5,1,2,0,4,6,0],![3,1,2,4,0,5,0],![3,1,2,4,0,0,6]],![![0,2,2,3,4,6,6],![5,1,0,3,4,6,0],![5,0,2,3,4,6,0],![0,1,2,3,4,5,6],![0,1,2,3,4,5,6],![1,2,0,3,4,5,0],![1,2,0,3,4,0,6]],![![0,2,2,4,4,5,6],![3,1,0,4,0,5,6],![3,0,2,4,0,5,6],![1,2,0,3,0,5,6],![1,2,0,0,4,5,6],![0,1,2,3,4,5,6],![0,1,2,3,4,5,6]]]
theorem delete_sparseK (k : Fin 3) (v : Fin 7) (hv : (K k).degree v = 2) :
    GraphInduction599.sparse ((K k).deleteIncidenceSet v) := by
  apply sparse_from_parent _ (parK k v)
  intro a b hab
  obtain ⟨hab,hav,hbv⟩ := (K k).deleteIncidenceSet_adj.mp hab
  rw [degreesK] at hv
  have h : ∀ k v a b, degK k v = 2 → adjK k a b = true → a ≠ v → b ≠ v →
      a = parK k v b ∨ b = parK k v a := by decide
  exact h k v a b hv hab hav hbv

theorem no_fourK : ∀ k : Fin 3, ∀ v a b c : Fin 7,
    (K k).Adj v a → (K k).Adj a b → (K k).Adj b c → (K k).Adj c v → a ≠ c → b ≠ v → False := by
  change ∀ k v a b c, adjK k v a = true → adjK k a b = true → adjK k b c = true → adjK k c v = true → a ≠ c → b ≠ v → False
  decide

theorem noFourK (k : Fin 3) : GraphInduction599.noFour (K k) := by
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
            exact no_fourK k _ _ _ _ h1 h2 h3 h4 hnd.1.2.1 hnd.2.1.2
          | cons h5 p5 =>
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega

theorem best_boundK (k : Fin 3) : (K k).edgeSet.ncard ≤ best (K k) + 1 := by
  apply core_bound_of_collision _ (min_degreeK k) (collisionK k)
  intro v hv
  exact best_bound_pseudoforest _ (delete_sparseK k v hv)
    (GraphInduction599.noFour_subgraph ((K k).deleteIncidenceSet_le v) (noFourK k))


namespace Finite26
def bit (A B U : Finset (Fin 7)) : Prop := A ⊆ U ∨ B ⊆ U

def collision (edge : Finset (Fin 7) → Prop) (A B : Finset (Fin 7)) : Prop :=
  ∃ U V : Finset (Fin 7), U \ ((A ∪ B) ∩ {1,2,3,4,5,6}) = V \ ((A ∪ B) ∩ {1,2,3,4,5,6}) ∧
    (bit A B U ↔ bit A B V) ∧ ¬ (edge U ↔ edge V)

def small : List (Finset (Fin 7)) := [∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {2,3}, {2,4}, {2,5}, {2,6}, {3,4}, {3,5}, {3,6}, {4,5}, {4,6}, {5,6}, {0,5,6}]
def pick (i : Fin 30) : Finset (Fin 7) := small.getD i.val ∅

abbrev edge18 (U : Finset (Fin 7)) : Prop :=
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨
  (0 ∈ U ∧ 4 ∈ U) ∨ (1 ∈ U ∧ 2 ∈ U) ∨ (3 ∈ U ∧ 5 ∈ U) ∨
  (4 ∈ U ∧ 6 ∈ U) ∨ (5 ∈ U ∧ 6 ∈ U)

abbrev edge26 (U : Finset (Fin 7)) : Prop :=
  (0 ∈ U ∧ 1 ∈ U) ∨ (0 ∈ U ∧ 2 ∈ U) ∨ (0 ∈ U ∧ 3 ∈ U) ∨
  (0 ∈ U ∧ 4 ∈ U) ∨ (0 ∈ U ∧ 5 ∈ U) ∨ (0 ∈ U ∧ 6 ∈ U) ∨
  (1 ∈ U ∧ 2 ∈ U) ∨ (3 ∈ U ∧ 4 ∈ U) ∨ (5 ∈ U ∧ 6 ∈ U)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 20000 in
theorem small_witness26 : ∀ A B : Finset (Fin 7), ¬ A ⊆ B → ¬ B ⊆ A →
    ∃ u v : Fin 30,
      pick u \ ((A ∪ B) ∩ {1,2,3,4,5,6}) = pick v \ ((A ∪ B) ∩ {1,2,3,4,5,6}) ∧
      (bit A B (pick u) ↔ bit A B (pick v)) ∧ ¬ (edge26 (pick u) ↔ edge26 (pick v)) := by
  unfold bit edge26 pick small
  decide +kernel

theorem collision26 (A B : Finset (Fin 7)) (hab : ¬ A ⊆ B) (hba : ¬ B ⊆ A) :
    collision edge26 A B := by
  obtain ⟨u,v,h⟩ := small_witness26 A B hab hba
  exact ⟨pick u,pick v,h⟩


end Finite26

def edges : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
def adjB (a b : Fin 7) : Bool := decide ((a,b) ∈ edges ∨ (b,a) ∈ edges)
def G : SimpleGraph (Fin 7) where
  Adj a b := adjB a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
noncomputable def neigh : Fin 7 → Finset (Fin 7) :=
 ![{1,2,3,4,5,6},{0,2},{0,1},{0,4},{0,3},{0,6},{0,5}]
theorem neighbors (v : Fin 7) : G.neighborFinset v = neigh v := by
  apply Finset.ext
  intro u
  rw [G.mem_neighborFinset]
  have h : ∀ v u, adjB v u = true ↔ u ∈ neigh v := by decide
  exact h v u
theorem degrees (v : Fin 7) : G.degree v = if v = 0 then 6 else 2 := by
  change (G.neighborFinset v).card = _
  rw [neighbors]
  fin_cases v <;> decide
theorem min_degree : ∀ v ∈ G.support, 2 ≤ G.degree v := by
  intro v _
  rw [degrees]
  split <;> omega
theorem low_eq (X Y : Finset (Fin 7)) : low G X Y = (X ∪ Y) ∩ {1,2,3,4,5,6} := by
  ext v
  simp only [low,Finset.mem_filter,Finset.mem_inter,degrees]
  have h : (if v = 0 then 6 else 2) = 2 ↔ v ∈ ({1,2,3,4,5,6} : Finset (Fin 7)) := by
    fin_cases v <;> decide
  rw [h]
theorem edgeAt (U : Finset (Fin 7)) : CycleModule599.edgeAt G U ↔ Finite26.edge26 U := by
  unfold CycleModule599.edgeAt Finite26.edge26
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    change adjB a b = true at hab
    simp only [adjB,edges,decide_eq_true_eq,List.mem_cons,List.mem_singleton,Prod.mk.injEq] at hab
    rcases hab with h | h <;> rcases h with h|h|h|h|h|h|h|h|h <;>
      rcases h with ⟨rfl,rfl⟩ <;> tauto
  · intro h
    rcases h with h|h|h|h|h|h|h|h|h
    · exact ⟨0,h.1,1,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,3,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,4,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,5,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨0,h.1,6,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨1,h.1,2,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨3,h.1,4,h.2,by change adjB _ _ = true; decide⟩
    · exact ⟨5,h.1,6,h.2,by change adjB _ _ = true; decide⟩
theorem collisionG : Collision G := by
  intro X Y hXY hYX _
  obtain ⟨U,V,hd,hbit,hneq⟩ := Finite26.collision26 X Y hXY hYX
  refine ⟨U,V,?_,hbit,?_⟩
  · intro i hi
    rw [low_eq] at hi
    have hh := congrArg (fun T : Finset (Fin 7) => i ∈ T) hd
    simpa [Finset.mem_sdiff,hi] using iff_of_eq hh
  · simpa only [edgeAt] using hneq

def mate : Fin 7 → Fin 7 := ![0,2,1,4,3,6,5]
def pair : Fin 7 → Fin 3 := ![0,0,0,1,1,2,2]
theorem leaf_degree (v : Fin 7) (hv : v ≠ 0) :
    (G.deleteIncidenceSet v).degree (mate v) = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  have h : ∀ v : Fin 7, v ≠ 0 → ∃! w : Fin 7,
      adjB (mate v) w = true ∧ mate v ≠ v ∧ w ≠ v := by
    unfold ExistsUnique
    decide
  simpa only [SimpleGraph.deleteIncidenceSet_adj,G] using h v hv

theorem deletion_eq (v : Fin 7) (hv : v ≠ 0) :
    (G.deleteIncidenceSet v).deleteIncidenceSet (mate v) = K (pair v) := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  rw [SimpleGraph.deleteIncidenceSet_adj,SimpleGraph.deleteIncidenceSet_adj]
  change ((adjB a b = true ∧ a ≠ v ∧ b ≠ v) ∧ a ≠ mate v ∧ b ≠ mate v) ↔ adjK (pair v) a b = true
  have h : ∀ v : Fin 7, v ≠ 0 → ∀ a b : Fin 7,
      ((adjB a b = true ∧ a ≠ v ∧ b ≠ v) ∧ a ≠ mate v ∧ b ≠ mate v) ↔ adjK (pair v) a b = true := by decide
  exact h v hv a b

theorem best_bound : G.edgeSet.ncard ≤ best G + 1 := by
  apply core_bound_of_collision G min_degree collisionG
  intro v hv
  have hv0 : v ≠ 0 := by
    rw [degrees] at hv
    intro h
    simp [h] at hv
  have hl := leaf_degree v hv0
  rw [← SimpleGraph.ncard_neighborSet] at hl
  apply bound_from_leaf (G.deleteIncidenceSet v) (mate v)
  · rw [← SimpleGraph.ncard_neighborSet]
    exact hl
  · rw [deletion_eq v hv0]
    exact best_boundK (pair v)

theorem edge_count : G.edgeSet.ncard = 9 := by
  let E : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(3,4),s(5,6)}
  have he : G.edgeSet = (E : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change adjB u v = true ↔ s(u,v) ∈ E
      fin_cases u <;> fin_cases v <;> decide
  rw [he,Set.ncard_coe_finset]
  decide

theorem or_lower (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (h : detects G C) (hc : covers C A) : 8 ≤ A.card := by
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  have hh := best_bound
  rw [edge_count] at hh
  omega

theorem detects_of_eval (C : Circuit)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2)) :
    detects G C := by
  intro x
  rw [he]
  simp only [List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,hab,ha,hb⟩
    refine ⟨a,b,?_,ha,hb⟩
    change decide ((a,b) ∈ edges ∨ (b,a) ∈ edges) = true
    exact decide_eq_true (Or.inl hab)
  · rintro ⟨a,b,hab,ha,hb⟩
    change decide ((a,b) ∈ edges ∨ (b,a) ∈ edges) = true at hab
    rcases of_decide_eq_true hab with hab|hab
    · exact ⟨(a,b),hab,ha,hb⟩
    · exact ⟨(b,a),hab,hb,ha⟩

theorem or_lower_eval (C : Circuit) (A : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2))
    (hc : covers C A) : 8 ≤ A.card :=
  or_lower C A hm (detects_of_eval C he) hc

end Windmill

end PEqualNP.Outside.L_meta_984.orTheory

/- Core lower bound and exact default-false restriction machinery adapted from
accepted L_meta_927. Only the seven-base helper prefix is retained here. -/
namespace PEqualNP.Outside.L_meta_984
namespace LeafTotal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
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

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
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
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
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
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
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

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
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
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

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

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

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

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

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

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
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
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
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
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
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
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
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
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

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

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
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
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
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
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

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
  induction h using Run.fold with
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
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
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
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

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
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

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

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 18 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 10 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)

/-! ## Section 3: Verified barrier certificates for the 7 base cases -/

-- Base case K3 (n=3, cap=3, k=9, states=1, pool=1)
def f_K3 : BFn 3 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
def rows_K3 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 3, 5, 6, 3, 5, 6, 3, 5, 6]
def xs_K3 : List ℕ := [0x1b607, 0x2da38, 0x36dc0]
def pool_K3 : List ℕ := [0xc000180b02809]
def NN_K3 : ℕ → ℕ
  | 3 => 1
  | _ => 0
def HT_K3 : ℕ → ℕ
  | 3 => 0xc03a13c3
  | _ => 0
def PT_K3 : ℕ → ℕ
  | _ => 0
def Z_K3 (s : ℕ) := bar 9 (Sgen 9 3 xs_K3 PT_K3) NN_K3 (idxGen NN_K3 HT_K3) id pool_K3 s
theorem z_K3_0 : span (Z_K3 0) 0 0 = true := rfl
theorem z_K3_1 : span (Z_K3 1) 0 0 = true := rfl
theorem z_K3_2 : span (Z_K3 2) 0 0 = true := rfl
theorem h_K3_3_0 : span (Z_K3 3) 1 0 = true := by decide +kernel
theorem z_K3_3 : span (Z_K3 3) 1 0 = true := h_K3_3_0
theorem base_K3 : ∀ s : ℕ, HasCircuitSize 3 f_K3 s → 4 ≤ s := by
  refine prove_base 3 9 3 f_K3 rows_K3 xs_K3 pool_K3 NN_K3 HT_K3 PT_K3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_K3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_3 i (Nat.zero_le i) hi
    )

-- Base case C5 (n=5, cap=6, k=50, states=7, pool=5)
def f_C5 : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)
def rows_C5 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 3, 5, 3, 10, 5, 20, 3, 5, 7, 10, 14, 20, 22, 24, 10, 24, 3, 5, 10, 11, 13, 20, 24, 25, 3, 5, 10, 13, 14, 20, 24, 28, 20, 24, 3, 5, 10, 19, 20, 21, 24, 25, 3, 5, 10, 19, 20, 22, 24, 26]
def xs_C5 : List ℕ := [0xbab02e6c075c03fc00ff0003, 0xad0d054355d37fc0000003fcc, 0x32326e8c876c80000ff003ff0, 0xc4c4b737398200000ffffc000, 0xf8f8f8382e083ffff00000000]
def pool_C5 : List ℕ := [0x18000a8370c833, 0x38020883f0c835, 0x80040403f0cc37, 0x800060350cc32, 0x800e018370d43f]
def NN_C5 : ℕ → ℕ
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT_C5 : ℕ → ℕ
  | 5 => 0xc6e3b2e569d2916d684aef2d399569702839ea7a276164fc
  | 6 => 0x2839ea7a
  | _ => 0
def PT_C5 : ℕ → ℕ
  | 5 => 0x40c0104004040100000000102
  | _ => 0
def Z_C5 (s : ℕ) := bar 50 (Sgen 50 6 xs_C5 PT_C5) NN_C5 (idxGen NN_C5 HT_C5) id pool_C5 s
theorem z_C5_0 : span (Z_C5 0) 0 0 = true := rfl
theorem z_C5_1 : span (Z_C5 1) 0 0 = true := rfl
theorem z_C5_2 : span (Z_C5 2) 0 0 = true := rfl
theorem z_C5_3 : span (Z_C5 3) 0 0 = true := rfl
theorem z_C5_4 : span (Z_C5 4) 0 0 = true := rfl
theorem h_C5_5_0 : span (Z_C5 5) 6 0 = true := by decide +kernel
theorem z_C5_5 : span (Z_C5 5) 6 0 = true := h_C5_5_0
theorem h_C5_6_0 : span (Z_C5 6) 1 0 = true := by decide +kernel
theorem z_C5_6 : span (Z_C5 6) 1 0 = true := h_C5_6_0
theorem base_C5 : ∀ s : ℕ, HasCircuitSize 5 f_C5 s → 7 ≤ s := by
  refine prove_base 5 50 6 f_C5 rows_C5 xs_C5 pool_C5 NN_C5 HT_C5 PT_C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_6 i (Nat.zero_le i) hi
    )

-- Base case BOWTIE (n=5, cap=7, k=50, states=79, pool=10)
def f_BOWTIE : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)
def rows_BOWTIE : List ℕ := [1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 5, 6, 9, 17, 24, 3, 6, 5, 6, 9, 24, 3, 5, 6, 9, 11, 14, 17, 24, 26, 3, 5, 6, 9, 13, 14, 17, 24, 28, 17, 24, 3, 5, 6, 9, 17, 19, 22, 24, 26, 3, 5, 6, 9, 17, 21, 22, 24, 28]
def xs_BOWTIE : List ℕ := [0x1d8ed2d96d56c00000000003f, 0x22d9412cd4b1401ff001ff0c0, 0xb31189b098e1bfe003fe00300, 0xc4622dc6e30a000003ffffc00, 0xf87c3e07020c3ffffc0000000]
def pool_BOWTIE : List ℕ := [0x80000a4340cc32, 0x780a000360d437, 0x5400030340c833, 0x8000030370c836, 0x3000080370c835, 0x54000a4370cc35, 0xa400054370cc36, 0xa400080340c833, 0x3000054340cc32, 0x2006000330c834]
def NN_BOWTIE : ℕ → ℕ
  | 4 => 2
  | 5 => 40
  | 6 => 36
  | 7 => 1
  | _ => 0
def HT_BOWTIE : ℕ → ℕ
  | 4 => 0xe69f9bc42160bc5f
  | 5 => 0xf742a3d0f3d6a6caf2c4f573e8b66066e180f3e4dc87be0edbeab3c2d93b4845d6c8153bd3b86897cf20682cc92e1222c36e694fc2da43cfb73fc6f7b64bf507b61f6228b3b81b1bb2c6c34ba8357aafa51ea19ca01014059f6d175f992962fa933e75078d7ecc3487246ed6697d7a4456dfe4dc558d03dd549ad51f4869b93243677bab3e0dcfd73c0e3e7f28b49293203432401c85f03b16c64768158068a1
  | 6 => 0xf8103679f7ee878cf2c4f573f084fb7be4e1031be2a67339d9ce2dd4d311441ec7bfd293c7633531c6b10786bd88bbf8b2c6c34bae58d960ad239bdb9f6d175f99876a0897388465933e7507917398168d7ecc348aee859b83a2b2267f1563cf7cb80320792278b673133ce4697d7a4463f740d054f0553f4b2540302c47248c231776e01a45f6430cea2d5a081c1522
  | 7 => 0x697d7a44
  | _ => 0
def PT_BOWTIE : ℕ → ℕ
  | 4 => 0xc847302
  | 5 => 0x70d40420520409410188cc1110170d0003213c406234000d4111023c409f3033c410a3406cd0152032040052306ccc1b35020404034020410810364940031028d42235028cc1c33030885f3055c40941027cc1111033c40c0303
  | 6 => 0x38c80e100040804040390c0f41010000e3003900050103cc00503004000f3203c8001010100c0e420041004010040c0e31010080f4303c840e2003cc40000039040f4203c400f40014000504014080e21
  | _ => 0
def Z_BOWTIE (s : ℕ) := bar 50 (Sgen 50 7 xs_BOWTIE PT_BOWTIE) NN_BOWTIE (idxGen NN_BOWTIE HT_BOWTIE) id pool_BOWTIE s
theorem z_BOWTIE_0 : span (Z_BOWTIE 0) 0 0 = true := rfl
theorem z_BOWTIE_1 : span (Z_BOWTIE 1) 0 0 = true := rfl
theorem z_BOWTIE_2 : span (Z_BOWTIE 2) 0 0 = true := rfl
theorem z_BOWTIE_3 : span (Z_BOWTIE 3) 0 0 = true := rfl
theorem h_BOWTIE_4_0 : span (Z_BOWTIE 4) 2 0 = true := by decide +kernel
theorem z_BOWTIE_4 : span (Z_BOWTIE 4) 2 0 = true := h_BOWTIE_4_0
theorem h_BOWTIE_5_0 : span (Z_BOWTIE 5) 12 0 = true := by decide +kernel
theorem h_BOWTIE_5_12 : span (Z_BOWTIE 5) 12 12 = true := by decide +kernel
theorem h_BOWTIE_5_24 : span (Z_BOWTIE 5) 12 24 = true := by decide +kernel
theorem h_BOWTIE_5_36 : span (Z_BOWTIE 5) 4 36 = true := by decide +kernel
theorem z_BOWTIE_5 : span (Z_BOWTIE 5) 40 0 = true := (@span_join (Z_BOWTIE 5) 24 0 16 (@span_join (Z_BOWTIE 5) 12 0 12 h_BOWTIE_5_0 h_BOWTIE_5_12) (@span_join (Z_BOWTIE 5) 12 24 4 h_BOWTIE_5_24 h_BOWTIE_5_36))
theorem h_BOWTIE_6_0 : span (Z_BOWTIE 6) 12 0 = true := by decide +kernel
theorem h_BOWTIE_6_12 : span (Z_BOWTIE 6) 12 12 = true := by decide +kernel
theorem h_BOWTIE_6_24 : span (Z_BOWTIE 6) 12 24 = true := by decide +kernel
theorem z_BOWTIE_6 : span (Z_BOWTIE 6) 36 0 = true := (@span_join (Z_BOWTIE 6) 12 0 24 h_BOWTIE_6_0 (@span_join (Z_BOWTIE 6) 12 12 12 h_BOWTIE_6_12 h_BOWTIE_6_24))
theorem h_BOWTIE_7_0 : span (Z_BOWTIE 7) 1 0 = true := by decide +kernel
theorem z_BOWTIE_7 : span (Z_BOWTIE 7) 1 0 = true := h_BOWTIE_7_0
theorem base_BOWTIE : ∀ s : ℕ, HasCircuitSize 5 f_BOWTIE s → 8 ≤ s := by
  refine prove_base 5 50 7 f_BOWTIE rows_BOWTIE xs_BOWTIE pool_BOWTIE NN_BOWTIE HT_BOWTIE PT_BOWTIE
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_BOWTIE_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_7 i (Nat.zero_le i) hi
    )

-- Base case NET (n=6, cap=7, k=72, states=26, pool=9)
def f_NET : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)
def rows_NET : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 10, 10, 10, 12, 12, 12, 16, 17, 17, 17, 20, 20, 20, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 33, 33, 33, 34, 34, 34, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 3, 5, 9, 3, 6, 18, 5, 6, 36, 9, 11, 14, 26, 13, 14, 44, 18, 19, 21, 25, 21, 22, 52, 25, 26, 3, 5, 6, 9, 18, 29, 30, 36, 60, 36, 35, 37, 41, 35, 38, 50, 41, 44, 3, 5, 6, 9, 18, 36, 43, 46, 58, 50, 52, 3, 5, 6, 9, 18, 36, 51, 53, 57, 3, 5, 6, 9, 18, 36, 57, 58, 60]
def xs_NET : List ℕ := [0x25f2c25a78569e264f007fc00038000e0007, 0x4a955ea9c8ab235cb900000ff9c000001c38, 0x9329a53497cc74e9d20000000003fe70e1c0, 0xe4420e4622d188fe04ff800ffe03ff80fe00, 0xe874388102e1ff1020fffff00003ffff0000, 0xf0783f07ff00408100fffffffffc00000000]
def pool_NET : List ℕ := [0x1803000491204c, 0xd8060fc5012849, 0xac000fc4d12848, 0x64030fc501344c, 0x180000c4c12049, 0xc000184c12448, 0x64000fc5012849, 0xd8030fc4d12848, 0xac060fc501344c]
def NN_NET : ℕ → ℕ
  | 5 => 6
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT_NET : ℕ → ℕ
  | 5 => 0xaf88224b70c6766557b62238571865263d1fc77a23def86d
  | 6 => 0xd5d2024bd11ae5e5cb9323a0bf32673cb6491b83b504a249b064ad26b04415efab09f6778f29c79884d9c66f80263ad760b07a3441b4b838403ba3af3ce49e4c2fdc23a307fae6c603fe551b
  | 7 => 0x80263ad7
  | _ => 0
def PT_NET : ℕ → ℕ
  | 5 => 0x14c0c530248c08f32048cc0f330
  | 6 => 0x64103c840f20018c0073101d0007320041401040040407500000001020194801000040c075103c400742
  | _ => 0
def Z_NET (s : ℕ) := bar 72 (Sgen 72 7 xs_NET PT_NET) NN_NET (idxGen NN_NET HT_NET) id pool_NET s
theorem z_NET_0 : span (Z_NET 0) 0 0 = true := rfl
theorem z_NET_1 : span (Z_NET 1) 0 0 = true := rfl
theorem z_NET_2 : span (Z_NET 2) 0 0 = true := rfl
theorem z_NET_3 : span (Z_NET 3) 0 0 = true := rfl
theorem z_NET_4 : span (Z_NET 4) 0 0 = true := rfl
theorem h_NET_5_0 : span (Z_NET 5) 6 0 = true := by decide +kernel
theorem z_NET_5 : span (Z_NET 5) 6 0 = true := h_NET_5_0
theorem h_NET_6_0 : span (Z_NET 6) 12 0 = true := by decide +kernel
theorem h_NET_6_12 : span (Z_NET 6) 7 12 = true := by decide +kernel
theorem z_NET_6 : span (Z_NET 6) 19 0 = true := (@span_join (Z_NET 6) 12 0 7 h_NET_6_0 h_NET_6_12)
theorem h_NET_7_0 : span (Z_NET 7) 1 0 = true := by decide +kernel
theorem z_NET_7 : span (Z_NET 7) 1 0 = true := h_NET_7_0
theorem base_NET : ∀ s : ℕ, HasCircuitSize 6 f_NET s → 8 ≤ s := by
  refine prove_base 6 72 7 f_NET rows_NET xs_NET pool_NET NN_NET HT_NET PT_NET
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_NET_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_7 i (Nat.zero_le i) hi
    )

-- Base case C6 (n=6, cap=7, k=78, states=8, pool=5)
def f_C6 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_C6 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 38, 38, 3, 5, 3, 10, 5, 20, 7, 14, 22, 10, 40, 11, 13, 41, 3, 5, 10, 13, 14, 20, 28, 40, 44, 48, 20, 48, 19, 21, 49, 3, 5, 10, 19, 20, 22, 26, 40, 48, 50, 26, 28, 56, 3, 5, 10, 20, 27, 29, 40, 48, 57, 40, 48, 3, 5, 10, 20, 35, 37, 40, 41, 48, 49, 35, 42, 50, 37, 44, 52, 3, 5, 10, 20, 39, 40, 46, 48, 54]
def xs_C6 : List ℕ := [0x99359933005f00be15c0007fe7fc001c003803, 0xaa8e0a81533690152f37fe38000007fe00001cc, 0xad701502a419257a47cbffc0000000000ffc1f0, 0x322462374e6201dcfa200000007ff8000fffe00, 0xc449845b8fbc7e6004800000007ffffff000000, 0xf87ff87c09c04b809003ffffff8000000000000]
def pool_C6 : List ℕ := [0x24020d45813851, 0x1000074531384f, 0x60040d46513c53, 0x8000385113c4e, 0xcc090746514458]
def NN_C6 : ℕ → ℕ
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT_C6 : ℕ → ℕ
  | 6 => 0xf44a7c96734fb6dc691bff606195314356426bf32c44989c2aa6f5bd
  | 7 => 0xf44a7c96
  | _ => 0
def PT_C6 : ℕ → ℕ
  | 6 => 0x41401000040c0102004100101
  | _ => 0
def Z_C6 (s : ℕ) := bar 78 (Sgen 78 7 xs_C6 PT_C6) NN_C6 (idxGen NN_C6 HT_C6) id pool_C6 s
theorem z_C6_0 : span (Z_C6 0) 0 0 = true := rfl
theorem z_C6_1 : span (Z_C6 1) 0 0 = true := rfl
theorem z_C6_2 : span (Z_C6 2) 0 0 = true := rfl
theorem z_C6_3 : span (Z_C6 3) 0 0 = true := rfl
theorem z_C6_4 : span (Z_C6 4) 0 0 = true := rfl
theorem z_C6_5 : span (Z_C6 5) 0 0 = true := rfl
theorem h_C6_6_0 : span (Z_C6 6) 7 0 = true := by decide +kernel
theorem z_C6_6 : span (Z_C6 6) 7 0 = true := h_C6_6_0
theorem h_C6_7_0 : span (Z_C6 7) 1 0 = true := by decide +kernel
theorem z_C6_7 : span (Z_C6 7) 1 0 = true := h_C6_7_0
theorem base_C6 : ∀ s : ℕ, HasCircuitSize 6 f_C6 s → 8 ≤ s := by
  refine prove_base 6 78 7 f_C6 rows_C6 xs_C6 pool_C6 NN_C6 HT_C6 PT_C6
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_C6_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_7 i (Nat.zero_le i) hi
    )

-- Base case TwoK3 (n=6, cap=8, k=102, states=122, pool=5)
def f_TwoK3 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_TwoK3 : List ℕ := [1, 1, 2, 2, 4, 4, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 3, 6, 5, 6, 24, 40, 3, 5, 6, 11, 13, 24, 25, 40, 41, 48, 3, 5, 6, 11, 14, 24, 26, 40, 42, 48, 3, 5, 6, 13, 14, 24, 28, 40, 44, 48, 24, 48, 3, 5, 6, 19, 21, 24, 25, 40, 48, 49, 3, 5, 6, 19, 22, 24, 26, 40, 48, 50, 3, 5, 6, 21, 22, 24, 28, 40, 48, 52, 40, 48, 3, 5, 6, 24, 35, 37, 40, 41, 48, 49, 3, 5, 6, 24, 35, 38, 40, 42, 48, 50, 3, 5, 6, 24, 37, 38, 40, 44, 48, 52]
def xs_TwoK3 : List ℕ := [0x4c13acc02c0b96c02c0b56c5c00003ff000003ff000003ff03, 0x96b50540565d0340555d034b400ffc00000ffc00000ffc000c, 0xad8260989781605857816058ebff000003ff000003ff0000030, 0x320c8321380e03817e1f87e3000000000000000003fffffffc0, 0xc2308c22de378de3982609810000000003fffffffc000000000, 0xfc3f0fc3e0380e02e0380e0203fffffffc00000000000000000]
def pool_TwoK3 : List ℕ := [0xc8280f06919c66, 0x9806118771b46c, 0x48080706919c66, 0x10020006719869, 0x10000086919867]
def NN_TwoK3 : ℕ → ℕ
  | 4 => 2
  | 5 => 12
  | 6 => 58
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_TwoK3 : ℕ → ℕ
  | 4 => 0x4d8c177f15c49257
  | 5 => 0xf0e5633ee7484b31a8d065f8979d3f4793f63bc08671bd54863d7f2181afece53dbda1882359e6cf198b67e50853723f
  | 6 => 0xfff2feb1fbb42ec1f805c600f741e864f4956378f1569e11edfc6b6de33c240fde836f10ddbefff4d6536b5ed4908d11cfe8ef31cdab9dedccacded6cbc2310ec568bed5ba4ccae7ba49c705b387ff19b114f671ae607e3ca911d87ca7a10ad8a32309d196921a7d95b4c51295798f3993292937929c19388caa887f8a7b658488976d8f868eb994859c9f8d807d69288041d1617e30b21078e2632b77386d21729f95276e1d55396b13cd37690c11976636a31c53d68f2d49c3ea2044353bb331b2062a31897ba42cb2ed7d28204f2e24d3f01c20c002c41f2967b51d792b3f1c8bb31a0e1442b5
  | 7 => 0xf805c600f35b4616e5e0c18ae59fd215e4eeedf8ddbefff4da55ffa0cddc75e9cbb17652ca742a1bc87d2041c780807ac4cd528ec4852d77c0d065f9b72faa58b33f4aeba911d87ca32712718b7dca57859c9f8d83d6d5dc839707388036fa067963bc88788c92f66f6896bd6edcc4e06e513d8b6cfc2284600dbbaa4eac3ae54ab8d6c54a3175144723967344353bb343db4bcc39a4161334e138ec345fccb131897ba42eb8073529c048df29a9ef5c26bc3c25229404c81f2967b5108017bc05304534
  | 8 => 0xa911d87c
  | _ => 0
def PT_TwoK3 : ℕ → ℕ
  | 4 => 0xc404301
  | 5 => 0x38885422160d441321c8c86f32148885820504880f32164c499202
  | 6 => 0x6480c21057c404e32130c84e350a8d00c30630c15f10438d81c10200d00335020406a36078d802101704143303a8d42020600c40210300d40336078d40e34034405a22130c0de3040cc85e32170000810200cc1d20634411a20378c0c2102a8cc1626020410210438cc0d000048c08000ac408c3040cd00d10508000036000c848105
  | 7 => 0x101039080e5003d440f40004100e20038c00f5203cc40f3001404050003d4005020140c0f53000000e5303d500105039440f2003c840f23010040f43039040504039480e23039000402010140e43004000e54010100f42038c401030100c0f4101000050503884010203c400e10
  | _ => 0
def Z_TwoK3 (s : ℕ) := bar 102 (Sgen 102 8 xs_TwoK3 PT_TwoK3) NN_TwoK3 (idxGen NN_TwoK3 HT_TwoK3) id pool_TwoK3 s
theorem z_TwoK3_0 : span (Z_TwoK3 0) 0 0 = true := rfl
theorem z_TwoK3_1 : span (Z_TwoK3 1) 0 0 = true := rfl
theorem z_TwoK3_2 : span (Z_TwoK3 2) 0 0 = true := rfl
theorem z_TwoK3_3 : span (Z_TwoK3 3) 0 0 = true := rfl
theorem h_TwoK3_4_0 : span (Z_TwoK3 4) 2 0 = true := by decide +kernel
theorem z_TwoK3_4 : span (Z_TwoK3 4) 2 0 = true := h_TwoK3_4_0
theorem h_TwoK3_5_0 : span (Z_TwoK3 5) 12 0 = true := by decide +kernel
theorem z_TwoK3_5 : span (Z_TwoK3 5) 12 0 = true := h_TwoK3_5_0
theorem h_TwoK3_6_0 : span (Z_TwoK3 6) 12 0 = true := by decide +kernel
theorem h_TwoK3_6_12 : span (Z_TwoK3 6) 12 12 = true := by decide +kernel
theorem h_TwoK3_6_24 : span (Z_TwoK3 6) 12 24 = true := by decide +kernel
theorem h_TwoK3_6_36 : span (Z_TwoK3 6) 12 36 = true := by decide +kernel
theorem h_TwoK3_6_48 : span (Z_TwoK3 6) 10 48 = true := by decide +kernel
theorem z_TwoK3_6 : span (Z_TwoK3 6) 58 0 = true := (@span_join (Z_TwoK3 6) 24 0 34 (@span_join (Z_TwoK3 6) 12 0 12 h_TwoK3_6_0 h_TwoK3_6_12) (@span_join (Z_TwoK3 6) 12 24 22 h_TwoK3_6_24 (@span_join (Z_TwoK3 6) 12 36 10 h_TwoK3_6_36 h_TwoK3_6_48)))
theorem h_TwoK3_7_0 : span (Z_TwoK3 7) 12 0 = true := by decide +kernel
theorem h_TwoK3_7_12 : span (Z_TwoK3 7) 12 12 = true := by decide +kernel
theorem h_TwoK3_7_24 : span (Z_TwoK3 7) 12 24 = true := by decide +kernel
theorem h_TwoK3_7_36 : span (Z_TwoK3 7) 12 36 = true := by decide +kernel
theorem h_TwoK3_7_48 : span (Z_TwoK3 7) 1 48 = true := by decide +kernel
theorem z_TwoK3_7 : span (Z_TwoK3 7) 49 0 = true := (@span_join (Z_TwoK3 7) 24 0 25 (@span_join (Z_TwoK3 7) 12 0 12 h_TwoK3_7_0 h_TwoK3_7_12) (@span_join (Z_TwoK3 7) 12 24 13 h_TwoK3_7_24 (@span_join (Z_TwoK3 7) 12 36 1 h_TwoK3_7_36 h_TwoK3_7_48)))
theorem h_TwoK3_8_0 : span (Z_TwoK3 8) 1 0 = true := by decide +kernel
theorem z_TwoK3_8 : span (Z_TwoK3 8) 1 0 = true := h_TwoK3_8_0
theorem base_TwoK3 : ∀ s : ℕ, HasCircuitSize 6 f_TwoK3 s → 9 ≤ s := by
  refine prove_base 6 102 8 f_TwoK3 rows_TwoK3 xs_TwoK3 pool_TwoK3 NN_TwoK3 HT_TwoK3 PT_TwoK3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_TwoK3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_8 i (Nat.zero_le i) hi
    )

-- Base case K3C5 (n=6, cap=8, k=88, states=111, pool=5)
def f_K3C5 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_K3C5 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 13, 14, 44, 18, 48, 3, 5, 6, 9, 18, 19, 21, 25, 40, 48, 49, 21, 22, 52, 25, 26, 56, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 40, 48, 3, 5, 6, 9, 18, 35, 37, 40, 41, 48, 49, 3, 5, 6, 9, 18, 35, 38, 40, 42, 48, 50, 3, 5, 6, 9, 18, 37, 38, 40, 44, 48, 52]
def xs_K3C5 : List ℕ := [0x560aeb5815933ac206d4f000003ff80001ffc000007, 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38, 0xacc118231330e118e098d2ffe000001ff8e000e000c0, 0x310620c437470620eee304000000001fff0000ffff00, 0xc21843085b87fbc3130020000000001fffffff000000, 0xfc1f83f07c049c029c0200ffffffffe0000000000000]
def pool_K3C5 : List ℕ := [0x108371345c16458, 0xd418028611746c, 0xd4080686c16861, 0x1803000591605c, 0x180000c5c16059]
def NN_K3C5 : ℕ → ℕ
  | 5 => 2
  | 6 => 59
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_K3C5 : ℕ → ℕ
  | 5 => 0xaf7f705075df09eb
  | 6 => 0xff05e072f727b177f3068765eaa33932db11b933d8cc5b6dcd35058ccc15227dca2f76a5c83ad31bc7250273c15a0367b4a0336cb10a8789afa7431baca18245a8900a13a2695142a1496e339ff66ae49c594e299b4c90679920e7e69912aafc9669f83595b74714954a15269059f51c8b53f7cd85bd41f47c32030e752ab69a72c697296f78934d6d024dd56a88734369689034692b5d8d653017b36252b02e43fac3934359dbb44239f8a53d49d89b37e19f5a2dcc7be728df8ae4233bb3a41f61f4541e1edb431b5f2e0917711a07161b410c15acbf2f11a788f510e7b25a08bdd900062edfb000979a5e
  | 7 => 0xfad5aba9f2eecca3e97ae7ace6bcb686e3778b7fe03ffe4fd963b263d4da459cd3c109c0d32c8367cea5d07ecbb58782cb9bad62c03ecc65bd3d402baec4164fab8da282aa9335c4a77738ef9ff66ae49a72143c980ef4d38d5b9238853ae9e8813088c1801c66e67c90fda2795c361d752ab69a692b5d8d652373366061f0715bb0fd5d57c5b116504f73f14825eea6435ca5264359dbb44239f8a53d49d89b38731eb53663a28d345f23502a623341161b410c13fb51330a946a4a0112919d00f8fd3a
  | 8 => 0x161b410c
  | _ => 0
def PT_K3C5 : ℕ → ℕ
  | 5 => 0x1cc848302
  | 6 => 0x141013cd413101bcc0d533040d80b10128406f3604c410910144c12c23054d01130554d42e3402c410a10510400910444c181321a8814b10384818a10324409634070d41635010411536028411a3052440c910510409035058d82e3031040c410510404135004d01033040d02f30404d80c22104cc01310b8d81130358cc2f35064982e350
  | 7 => 0xe510394c0e210100c0f10014100f50010140e40014080501038c40f54014000f4103d440f4003cc00401004000e2303cc40e4203d0c0404010080e10039040104004080e50039500e300390c0f53039480f210040c0105004040f20010000f4203d4800000140c0f23038800505
  | _ => 0
def Z_K3C5 (s : ℕ) := bar 88 (Sgen 88 8 xs_K3C5 PT_K3C5) NN_K3C5 (idxGen NN_K3C5 HT_K3C5) id pool_K3C5 s
theorem z_K3C5_0 : span (Z_K3C5 0) 0 0 = true := rfl
theorem z_K3C5_1 : span (Z_K3C5 1) 0 0 = true := rfl
theorem z_K3C5_2 : span (Z_K3C5 2) 0 0 = true := rfl
theorem z_K3C5_3 : span (Z_K3C5 3) 0 0 = true := rfl
theorem z_K3C5_4 : span (Z_K3C5 4) 0 0 = true := rfl
theorem h_K3C5_5_0 : span (Z_K3C5 5) 2 0 = true := by decide +kernel
theorem z_K3C5_5 : span (Z_K3C5 5) 2 0 = true := h_K3C5_5_0
theorem h_K3C5_6_0 : span (Z_K3C5 6) 12 0 = true := by decide +kernel
theorem h_K3C5_6_12 : span (Z_K3C5 6) 12 12 = true := by decide +kernel
theorem h_K3C5_6_24 : span (Z_K3C5 6) 12 24 = true := by decide +kernel
theorem h_K3C5_6_36 : span (Z_K3C5 6) 12 36 = true := by decide +kernel
theorem h_K3C5_6_48 : span (Z_K3C5 6) 11 48 = true := by decide +kernel
theorem z_K3C5_6 : span (Z_K3C5 6) 59 0 = true := (@span_join (Z_K3C5 6) 24 0 35 (@span_join (Z_K3C5 6) 12 0 12 h_K3C5_6_0 h_K3C5_6_12) (@span_join (Z_K3C5 6) 12 24 23 h_K3C5_6_24 (@span_join (Z_K3C5 6) 12 36 11 h_K3C5_6_36 h_K3C5_6_48)))
theorem h_K3C5_7_0 : span (Z_K3C5 7) 12 0 = true := by decide +kernel
theorem h_K3C5_7_12 : span (Z_K3C5 7) 12 12 = true := by decide +kernel
theorem h_K3C5_7_24 : span (Z_K3C5 7) 12 24 = true := by decide +kernel
theorem h_K3C5_7_36 : span (Z_K3C5 7) 12 36 = true := by decide +kernel
theorem h_K3C5_7_48 : span (Z_K3C5 7) 1 48 = true := by decide +kernel
theorem z_K3C5_7 : span (Z_K3C5 7) 49 0 = true := (@span_join (Z_K3C5 7) 24 0 25 (@span_join (Z_K3C5 7) 12 0 12 h_K3C5_7_0 h_K3C5_7_12) (@span_join (Z_K3C5 7) 12 24 13 h_K3C5_7_24 (@span_join (Z_K3C5 7) 12 36 1 h_K3C5_7_36 h_K3C5_7_48)))
theorem h_K3C5_8_0 : span (Z_K3C5 8) 1 0 = true := by decide +kernel
theorem z_K3C5_8 : span (Z_K3C5 8) 1 0 = true := h_K3C5_8_0
theorem base_K3C5 : ∀ s : ℕ, HasCircuitSize 6 f_K3C5 s → 9 ≤ s := by
  refine prove_base 6 88 8 f_K3C5 rows_K3C5 xs_K3C5 pool_K3C5 NN_K3C5 HT_K3C5 PT_K3C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_K3C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_8 i (Nat.zero_le i) hi
    )



end Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target16 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def perm16 : Fin 7 → Fin 7 := ![0,1,2,3,6,4,5]

theorem total16 (s : Nat) (h : HasCircuitSize 7 target16 s) : 10 ≤ s := by
  have hr := Core.relabel_size perm16 target16 s h
  have hd : ∃ x : Fin 7 → Bool,
      (fun y => target16 (y ∘ perm16)) (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠
        (fun y => target16 (y ∘ perm16)) x := by
    exact ⟨![true,false,false,false,false,false,false], by decide +kernel⟩
  have hn : ∃ y y' : Fin 6 → Bool,
      (fun x => target16 (x ∘ perm16)) (Fin.snoc y false) ≠
        (fun x => target16 (x ∘ perm16)) (Fin.snoc y' false) := by
    exact ⟨![false,false,false,false,false,false], ![true,true,false,false,false,false], by decide +kernel⟩
  obtain ⟨s', hdrop, hc⟩ := Core.gate_elim_one 6 (fun x => target16 (x ∘ perm16)) false s hd hn hr
  have heq : (fun y : Fin 6 → Bool => target16 ((Fin.snoc y false) ∘ perm16)) = Core.f_K3C5 := by
    funext y; revert y; decide +kernel
  rw [heq] at hc
  have hb := Core.base_K3C5 s' hc
  omega

def target22 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)

theorem total22 (s : Nat) (h : HasCircuitSize 7 target22 s) : 10 ≤ s := by
  have hd : ∃ x : Fin 7 → Bool,
      target22 (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠ target22 x := by
    exact ⟨![false,false,false,false,false,true,false], by decide +kernel⟩
  have hn : ∃ y y' : Fin 6 → Bool,
      target22 (Fin.snoc y false) ≠ target22 (Fin.snoc y' false) := by
    exact ⟨![false,false,false,false,false,false], ![true,true,false,false,false,false], by decide +kernel⟩
  obtain ⟨s', hdrop, hc⟩ := Core.gate_elim_one 6 target22 false s hd hn h
  have heq : (fun y : Fin 6 → Bool => target22 (Fin.snoc y false)) = Core.f_K3C5 := by
    funext y; revert y; decide +kernel
  rw [heq] at hc
  have hb := Core.base_K3C5 s' hc
  omega

theorem mono_fanin (C : Circuit) (hm : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨hop, hl⟩ := hm g hg
  refine ⟨?_, hl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem route16 (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target16 x) : 10 ≤ C.size :=
  total16 C.size ⟨C, mono_fanin C hm, le_rfl, he⟩
theorem route22 (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target22 x) : 10 ≤ C.size :=
  total22 C.size ⟨C, mono_fanin C hm, le_rfl, he⟩
end LeafTotal
end PEqualNP.Outside.L_meta_984
#print axioms PEqualNP.Outside.L_meta_984_combine.assemble_exact
#print axioms PEqualNP.Outside.L_meta_984.orTheory.Windmill.or_lower_eval
#print axioms PEqualNP.Outside.L_meta_984.LeafTotal.route22
