import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L782

open PEqualNP.CircuitLowerBounds

def wv (C : Circuit) (x : List Bool) (j : ℕ) : Bool := (C.wires x).getD j false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wk (C : Circuit) (x : List Bool) (k : ℕ) : List Bool := (C.gates.take k).foldl stp x

lemma wk_zero (C : Circuit) (x : List Bool) : wk C x 0 = x := by simp [wk]

lemma wk_succ (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    wk C x (k + 1) = stp (wk C x k) (C.gates[k]) := by
  unfold wk
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

lemma wk_full (C : Circuit) (x : List Bool) : wk C x C.gates.length = C.wires x := by
  unfold wk
  rw [List.take_length]
  rfl

lemma wk_length (C : Circuit) (x : List Bool) :
    ∀ k, k ≤ C.gates.length → (wk C x k).length = x.length + k := by
  intro k
  induction k with
  | zero => intro _; simp [wk_zero]
  | succ k ih =>
    intro hk
    rw [wk_succ C x k (by omega)]
    simp only [stp, List.length_append, List.length_singleton]
    rw [ih (by omega)]
    omega

lemma wk_prefix (C : Circuit) (x : List Bool) (k : ℕ) :
    ∀ m, k ≤ m → m ≤ C.gates.length → ∀ i, i < (wk C x k).length →
      (wk C x m).getD i false = (wk C x k).getD i false := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base => intro _ i _; rfl
  | succ m hkm ih =>
    intro hm i hi
    rw [wk_succ C x m (by omega)]
    have := ih (by omega) i hi
    rw [← this]
    have hlen : i < (wk C x m).length := by
      have h1 := wk_length C x m (by omega)
      have h2 := wk_length C x k (by omega)
      omega
    simp [stp, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]

lemma wv_input (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    wv C x j = x.getD j false := by
  have := wk_prefix C x 0 C.gates.length (Nat.zero_le _) le_rfl j (by simpa [wk_zero] using hj)
  rw [wk_full, wk_zero] at this
  exact this

lemma wv_out (C : Circuit) (x : List Bool) (j : ℕ) (hj : x.length + C.gates.length ≤ j) :
    wv C x j = false := by
  have hl := wk_length C x C.gates.length le_rfl
  rw [wk_full] at hl
  simp [wv, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.wires x).length ≤ j)]

lemma wv_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length) :
    wv C x (x.length + t) = (C.gates[t]).op.eval
      ((C.gates[t]).inputs.map fun i => if i < x.length + t then wv C x i else false) := by
  have hlen := wk_length C x t (by omega)
  have hs := wk_succ C x t ht
  have hfull := wk_prefix C x (t + 1) C.gates.length (by omega) le_rfl (x.length + t)
    (by rw [wk_length C x (t + 1) (by omega)]; omega)
  rw [wk_full] at hfull
  unfold wv
  rw [hfull, hs]
  simp only [stp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + t
  · rw [if_pos hi]
    have := wk_prefix C x t C.gates.length (by omega) le_rfl i (by omega)
    rw [wk_full] at this
    exact this.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl


lemma ofFn_getD_true {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = true ↔ ∃ h : i < n, f ⟨i, h⟩ = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < n
  · simp [h]
  · simp [h]

lemma wv_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hl : xs.length = ys.length)
    (hxy : ∀ i, xs.getD i false = true → ys.getD i false = true) :
    ∀ j, wv C xs j = true → wv C ys j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h1 : j < xs.length
    · rw [wv_input C xs j h1] at hj
      rw [wv_input C ys j (hl ▸ h1)]
      exact hxy j hj
    · by_cases h2 : xs.length + C.gates.length ≤ j
      · rw [wv_out C xs j h2] at hj
        exact absurd hj (by simp)
      · obtain ⟨t, rfl⟩ : ∃ t, j = xs.length + t := ⟨j - xs.length, by omega⟩
        have ht : t < C.gates.length := by omega
        rw [wv_gate C xs t ht] at hj
        rw [hl, wv_gate C ys t ht]
        have hop := hC _ (List.getElem_mem ht)
        rcases hop with hop | hop
        · rw [hop] at hj ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hj ⊢
          intro b hb
          obtain ⟨i, hi, rfl⟩ := hb
          have hb2 := hj _ ⟨i, hi, rfl⟩
          by_cases hlt : i < xs.length + t
          · rw [if_pos hlt] at hb2
            rw [if_pos (by omega : i < ys.length + t)]
            exact ih i (by omega) hb2
          · rw [if_neg hlt] at hb2
            exact absurd hb2 (by simp)
        · rw [hop] at hj ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hj ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hj
          refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
          by_cases hlt : i < xs.length + t
          · rw [if_pos hlt] at hb
            rw [if_pos (by omega : i < ys.length + t)]
            exact ih i (by omega) hb
          · rw [if_neg hlt] at hb
            exact absurd hb (by simp)

def Ls (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => wv C (List.ofFn (fun b : Fin n => decide (b = a))) w = true)

lemma mem_Ls (C : Circuit) (n w : ℕ) (a : Fin n) :
    a ∈ Ls C n w ↔ wv C (List.ofFn (fun b : Fin n => decide (b = a))) w = true := by
  simp [Ls]

lemma Ls_input (C : Circuit) (n w : ℕ) (hw : w < n) : (Ls C n w).card ≤ 1 := by
  have key : ∀ a ∈ Ls C n w, a = ⟨w, hw⟩ := by
    intro a ha
    rw [mem_Ls, wv_input C _ w (by simpa using hw)] at ha
    obtain ⟨h, hh⟩ := (ofFn_getD_true _ w).1 ha
    exact (of_decide_eq_true hh).symm
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [key a ha, key b hb]

lemma Ls_out (C : Circuit) (n w : ℕ) (hw : n + C.gates.length ≤ w) : Ls C n w = ∅ := by
  ext a
  simp only [mem_Ls, Finset.notMem_empty, iff_false]
  rw [wv_out C _ w (by simpa using hw)]
  simp


open Classical

def Pr (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  Ls C n w ⊆ S ∧ 2 ≤ (Ls C n w).card

lemma Pr_range (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) (h : Pr C n S w) :
    n ≤ w ∧ w < n + C.gates.length := by
  by_contra hno
  rcases le_or_gt n w with h1 | h1
  · have h2 : n + C.gates.length ≤ w := by omega
    have := h.2
    rw [Ls_out C n w h2] at this
    simp at this
  · have := Ls_input C n w h1
    have := h.2
    omega

def chd (C : Circuit) (n g : ℕ) : Finset ℕ :=
  if g < n then ∅ else
    match C.gates[g - n]? with
    | none => ∅
    | some gt => (gt.inputs.filter (· < g)).toFinset

lemma chd_lt (C : Circuit) (n g c : ℕ) (h : c ∈ chd C n g) : c < g := by
  unfold chd at h
  split_ifs at h with h1
  · simp at h
  · split at h
    · simp at h
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
      exact h.2

lemma chd_card (C : Circuit) (n g : ℕ)
    (hC : ∀ gt ∈ C.gates, gt.inputs.length = 2) : (chd C n g).card ≤ 2 := by
  unfold chd
  split_ifs with h1
  · simp
  · split
    · simp
    · rename_i gt hgt
      have hmem := hC gt (List.mem_of_getElem? hgt)
      calc (gt.inputs.filter (· < g)).toFinset.card
          ≤ (gt.inputs.filter (· < g)).length := List.toFinset_card_le _
        _ ≤ gt.inputs.length := List.length_filter_le _ _
        _ = 2 := hmem

lemma mem_chd (C : Circuit) (n t c : ℕ) (ht : t < C.gates.length) :
    c ∈ chd C n (n + t) ↔ c ∈ (C.gates[t]).inputs ∧ c < n + t := by
  unfold chd
  rw [if_neg (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem ht]
  simp

lemma exists_child (C : Circuit) (n : ℕ)
    (hC : ∀ gt ∈ C.gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length = 2)
    (xs ea : List Bool) (hxs : xs.length = n) (hea : ea.length = n) (t : ℕ)
    (ht : t < C.gates.length) (h1 : wv C xs (n + t) = false) (h2 : wv C ea (n + t) = true) :
    ∃ c ∈ chd C n (n + t), wv C xs c = false ∧ wv C ea c = true := by
  have e1 := wv_gate C xs t ht
  have e2 := wv_gate C ea t ht
  rw [hxs] at e1
  rw [hea] at e2
  rw [h1] at e1
  rw [h2] at e2
  obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem ht)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
  rw [hpq] at e1 e2
  have hp : p ∈ chd C n (n + t) ↔ p < n + t := by
    rw [mem_chd C n t p ht, hpq]; simp
  have hq : q ∈ chd C n (n + t) ↔ q < n + t := by
    rw [mem_chd C n t q ht, hpq]; simp
  rcases hop with hop | hop <;> rw [hop] at e1 e2 <;>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false] at e1 e2 <;>
    by_cases hpt : p < n + t <;> by_cases hqt : q < n + t <;>
    simp [hpt, hqt] at e1 e2
  · by_cases hx : wv C xs p = true
    · exact ⟨q, hq.2 hqt, e1 hx, e2.2⟩
    · exact ⟨p, hp.2 hpt, by simpa using hx, e2.1⟩
  · rcases e2 with h | h
    · exact ⟨p, hp.2 hpt, e1.1, h⟩
    · exact ⟨q, hq.2 hqt, e1.2, h⟩
  · exact ⟨p, hp.2 hpt, e1, e2⟩
  · exact ⟨q, hq.2 hqt, e1, e2⟩


lemma per_output (C : Circuit) (n k : ℕ) (S : Finset (Fin n)) (o c : ℕ)
    (hC : ∀ gt ∈ C.gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length = 2)
    (H2 : 2 ≤ (Ls C n o).card) (H4 : Ls C n o ⊆ S)
    (H5 : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → wv C (List.ofFn x) o = false)
    (hck : c ≤ k) (H7 : c + 1 ≤ (Ls C n o).card) :
    c ≤ ((Finset.range (n + C.gates.length)).filter (fun w => Pr C n S w)).card := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : Ls C 0 o = ∅ := Finset.eq_empty_of_isEmpty _
      rw [this] at H2
      simp at H2
    · exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hPro : Pr C n S o := ⟨H4, H2⟩
  have hC1 : ∀ gt ∈ C.gates, gt.op = GateOp.and ∨ gt.op = GateOp.or := fun gt h => (hC gt h).1
  have hC2 : ∀ gt ∈ C.gates, gt.inputs.length = 2 := fun gt h => (hC gt h).2
  obtain ⟨step, hstep⟩ : ∃ step : ℕ → ℕ → Prop, ∀ g u, step g u ↔
      Pr C n S g ∧ Pr C n S u ∧ u ∈ chd C n g := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, ∀ g, g ∈ R ↔
      (Pr C n S g ∧ Relation.ReflTransGen step o g) := by
    refine ⟨(Finset.range (n + C.gates.length)).filter
      (fun g => Pr C n S g ∧ Relation.ReflTransGen step o g), fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(Pr_range C n S g h.1).2, h⟩
  have hoR : o ∈ R := (hR o).2 ⟨hPro, Relation.ReflTransGen.refl⟩
  have hRP : ∀ g ∈ R, Pr C n S g := fun g hg => ((hR g).1 hg).1
  have hRsub : R ⊆ (Finset.range (n + C.gates.length)).filter (fun w => Pr C n S w) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨(Pr_range C n S g (hRP g hg)).2, hRP g hg⟩
  have hRpred : ∀ g ∈ R, g ≠ o → ∃ g' ∈ R, g ∈ chd C n g' := by
    intro g hg hne
    obtain ⟨hPg, hrt⟩ := (hR g).1 hg
    rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨g', hg', hs⟩
    · exact absurd h hne
    · have hs' := (hstep g' g).1 hs
      exact ⟨g', (hR g').2 ⟨hs'.1, hg'⟩, hs'.2.2⟩
  obtain ⟨N, hN⟩ : ∃ N : Finset ℕ, N = R.biUnion (chd C n) := ⟨_, rfl⟩
  have hNcard : N.card ≤ 2 * R.card := by
    rw [hN]
    calc (R.biUnion (chd C n)).card ≤ ∑ g ∈ R, (chd C n g).card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ R, 2 := Finset.sum_le_sum (fun g _ => chd_card C n g hC2)
      _ = 2 * R.card := by simp [mul_comm]
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ, E = N \ R := ⟨_, rfl⟩
  have hEcard : E.card ≤ R.card + 1 := by
    have h1 : R.erase o ⊆ N := by
      intro g hg
      obtain ⟨hne, hgR⟩ := Finset.mem_erase.1 hg
      obtain ⟨g', hg', hc⟩ := hRpred g hgR hne
      rw [hN]
      exact Finset.mem_biUnion.2 ⟨g', hg', hc⟩
    have h2 : E ⊆ N := by rw [hE]; exact Finset.sdiff_subset
    have h3 : Disjoint (R.erase o) E := by
      rw [Finset.disjoint_left]
      intro g hg hgE
      rw [hE] at hgE
      exact (Finset.mem_sdiff.1 hgE).2 (Finset.mem_of_mem_erase hg)
    have h4 := Finset.card_le_card (Finset.union_subset h1 h2)
    rw [Finset.card_union_of_disjoint h3, Finset.card_erase_of_mem hoR] at h4
    have h5 : 1 ≤ R.card := Finset.card_pos.2 ⟨o, hoR⟩
    omega
  have hEnp : ∀ e ∈ E, ¬ Pr C n S e := by
    intro e he hpe
    rw [hE] at he
    obtain ⟨heN, heR⟩ := Finset.mem_sdiff.1 he
    rw [hN] at heN
    obtain ⟨g, hg, hc⟩ := Finset.mem_biUnion.1 heN
    obtain ⟨hPg, hrt⟩ := (hR g).1 hg
    exact heR ((hR e).2 ⟨hpe, Relation.ReflTransGen.tail hrt ((hstep g e).2 ⟨hPg, hpe, hc⟩)⟩)
  obtain ⟨Et, hEt⟩ : ∃ Et : Finset ℕ, Et = E.filter (fun e => ¬ Ls C n e ⊆ S) := ⟨_, rfl⟩
  by_cases hbig : k + 1 ≤ Et.card
  · have : Et.card ≤ E.card := by rw [hEt]; exact Finset.card_filter_le _ _
    have := Finset.card_le_card hRsub
    omega
  · push Not at hbig
    have hEtk : Et.card ≤ k := by omega
    have hex : ∀ e ∈ Et, ∃ b : Fin n, b ∈ Ls C n e ∧ b ∉ S := by
      intro e he
      rw [hEt] at he
      have := (Finset.mem_filter.1 he).2
      obtain ⟨b, hb1, hb2⟩ := Finset.not_subset.1 this
      exact ⟨b, hb1, hb2⟩
    choose! a ha using hex
    obtain ⟨X, hX⟩ : ∃ X : Finset (Fin n), X = Et.image a := ⟨_, rfl⟩
    obtain ⟨xs, hxs⟩ : ∃ xs : Fin n → Bool, xs = fun q => decide (q ∈ X) := ⟨_, rfl⟩
    have hXk : (Finset.univ.filter (fun q => xs q = true)).card ≤ k := by
      have : (Finset.univ.filter (fun q => xs q = true)) = X := by
        ext q; simp [hxs]
      rw [this, hX]
      exact (Finset.card_image_le).trans hEtk
    have hXS : ∀ q ∈ S, xs q = false := by
      intro q hq
      rw [hxs]
      simp only [decide_eq_false_iff_not]
      intro hqX
      rw [hX] at hqX
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hqX
      exact (ha e he).2 hq
    have hostar : wv C (List.ofFn xs) o = false := H5 xs hXk hXS
    have htrue : ∀ e ∈ Et, wv C (List.ofFn xs) e = true := by
      intro e he
      refine wv_mono C hC1 (List.ofFn (fun b : Fin n => decide (b = a e))) (List.ofFn xs)
        (by simp) ?_ e ((mem_Ls C n e (a e)).1 (ha e he).1)
      intro i hi
      obtain ⟨h, hh⟩ := (ofFn_getD_true _ i).1 hi
      refine (ofFn_getD_true _ i).2 ⟨h, ?_⟩
      have := of_decide_eq_true hh
      rw [hxs]
      simp only [decide_eq_true_eq]
      rw [this, hX]
      exact Finset.mem_image_of_mem a he
    have hlx : (List.ofFn xs).length = n := List.length_ofFn
    have D : ∀ g, g ∈ R → ∀ b : Fin n, wv C (List.ofFn xs) g = false →
        wv C (List.ofFn (fun q : Fin n => decide (q = b))) g = true →
        ∃ e ∈ E, Ls C n e = {b} := by
      intro g
      induction g using Nat.strong_induction_on with
      | _ g ih =>
        intro hgR b hxg hbg
        have hPg := hRP g hgR
        obtain ⟨hg1, hg2⟩ := Pr_range C n S g hPg
        obtain ⟨t, rfl⟩ : ∃ t, g = n + t := ⟨g - n, by omega⟩
        have ht : t < C.gates.length := by omega
        obtain ⟨c', hc', hc1, hc2⟩ :=
          exists_child C n hC (List.ofFn xs) (List.ofFn (fun q : Fin n => decide (q = b)))
            hlx List.length_ofFn t ht hxg hbg
        have hclt := chd_lt C n _ c' hc'
        by_cases hpc : Pr C n S c'
        · have hcR : c' ∈ R := (hR c').2 ⟨hpc, Relation.ReflTransGen.tail
            ((hR _).1 hgR).2 ((hstep _ _).2 ⟨hPg, hpc, hc'⟩)⟩
          exact ih c' hclt hcR b hc1 hc2
        · have hcN : c' ∈ N := by rw [hN]; exact Finset.mem_biUnion.2 ⟨_, hgR, hc'⟩
          have hcE : c' ∈ E := by
            rw [hE]; exact Finset.mem_sdiff.2 ⟨hcN, fun h => hpc (hRP c' h)⟩
          by_cases hsub : Ls C n c' ⊆ S
          · refine ⟨c', hcE, ?_⟩
            have hcard : (Ls C n c').card ≤ 1 := by
              by_contra hcon
              exact hpc ⟨hsub, by omega⟩
            have hb : b ∈ Ls C n c' := (mem_Ls C n c' b).2 hc2
            ext d
            simp only [Finset.mem_singleton]
            constructor
            · intro hd
              exact Finset.card_le_one.1 hcard d hd b hb
            · rintro rfl
              exact hb
          · exfalso
            have hcEt : c' ∈ Et := by rw [hEt]; exact Finset.mem_filter.2 ⟨hcE, hsub⟩
            rw [htrue c' hcEt] at hc1
            exact absurd hc1 (by simp)
    have hinj : ∀ b ∈ Ls C n o, ∃ e ∈ E, Ls C n e = {b} := by
      intro b hb
      exact D o hoR b hostar ((mem_Ls C n o b).1 hb)
    choose! f hf using hinj
    have hle : (Ls C n o).card ≤ E.card := by
      refine Finset.card_le_card_of_injOn f (fun b hb => (hf b hb).1) ?_
      intro b hb b' hb' hbb
      have h1 := (hf b (Finset.mem_coe.1 hb)).2
      have h2 := (hf b' (Finset.mem_coe.1 hb')).2
      rw [hbb] at h1
      exact Finset.singleton_inj.1 (h1.symm.trans h2)
    have := Finset.card_le_card hRsub
    omega

end PEqualNP.Outside.L782

open PEqualNP.Outside.L782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c H1 H2 H3 H4 H5 H6 H7
  classical
  have hper : ∀ i, c i ≤ ((Finset.range (n + C.gates.length)).filter
      (fun w => Pr C n (S i) w)).card := by
    intro i
    refine per_output C n k (S i) (o i) (c i) H3 (H2 i) ?_ (H5 i) (H6 i) (H7 i)
    intro p hp
    exact H4 i p ((mem_Ls C n (o i) p).1 hp)
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
      Disjoint ((Finset.range (n + C.gates.length)).filter (fun w => Pr C n (S i) w))
        ((Finset.range (n + C.gates.length)).filter (fun w => Pr C n (S j) w)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have h1 := (Finset.mem_filter.1 hwi).2
    have h2 := (Finset.mem_filter.1 hwj).2
    have h3 : Ls C n w ⊆ S i ∩ S j := Finset.subset_inter h1.1 h2.1
    have h4 := Finset.card_le_card h3
    have h5 := H1 i j hij
    have h6 := h1.2
    omega
  have hsub : (Finset.univ : Finset (Fin m)).biUnion
      (fun i => (Finset.range (n + C.gates.length)).filter (fun w => Pr C n (S i) w)) ⊆
      Finset.Ico n (n + C.gates.length) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hw
    have := Pr_range C n (S i) w (Finset.mem_filter.1 hi).2
    exact Finset.mem_Ico.2 this
  calc ∑ i, c i ≤ ∑ i, ((Finset.range (n + C.gates.length)).filter
          (fun w => Pr C n (S i) w)).card := Finset.sum_le_sum (fun i _ => hper i)
    _ = ((Finset.univ : Finset (Fin m)).biUnion
          (fun i => (Finset.range (n + C.gates.length)).filter (fun w => Pr C n (S i) w))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := Finset.card_le_card hsub
    _ = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size]
