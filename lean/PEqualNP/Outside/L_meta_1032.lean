import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1032

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩



def onSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ T)

lemma filter_onSet {n : ℕ} (T : Finset (Fin n)) :
    Finset.univ.filter (fun p => onSet T p = true) = T := by
  ext p
  simp [onSet]

lemma union_bound {q n m : ℕ} (S' : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S' i).card ≤ q + 1)
    (hdiff : ∀ i j, i ≠ j → (S' j \ S' i).card ≤ q)
    (B : Finset ℕ) (D : ℕ → Finset (Fin n))
    (hD : ∀ w ∈ B, (D w).card ≤ q ∨ ∃ i, D w = S' i) :
    (B.biUnion D).card ≤ B.card * q + 1 := by
  classical
  by_cases hbig : ∃ w ∈ B, ∃ i, D w = S' i
  · obtain ⟨w, hw, i, hi⟩ := hbig
    let R := B.erase w
    have hdiff' : ∀ v ∈ R, (D v \ S' i).card ≤ q := by
      intro v hv
      rcases hD v (Finset.mem_erase.mp hv).2 with hs | ⟨j, hj⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans hs
      · rw [hj]
        by_cases h : j = i
        · simp [h]
        · exact hdiff i j (Ne.symm h)
    have hsub : B.biUnion D ⊆ S' i ∪ R.biUnion (fun v => D v \ S' i) := by
      intro p hp
      obtain ⟨v, hv, hp⟩ := Finset.mem_biUnion.mp hp
      by_cases h : p ∈ S' i
      · exact Finset.mem_union_left _ h
      · have hne : v ≠ w := by rintro rfl; exact h (hi ▸ hp)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩, Finset.mem_sdiff.mpr ⟨hp, h⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S' i) (R.biUnion (fun v => D v \ S' i))
    have h3 := Finset.card_biUnion_le_card_mul R (fun v => D v \ S' i) q hdiff'
    have he : R.card + 1 = B.card := Finset.card_erase_add_one hw
    have h4 := hsize i
    rw [← he, Nat.add_mul, Nat.one_mul]
    omega
  · have hsmall (v) (hv : v ∈ B) : (D v).card ≤ q :=
      (hD v hv).resolve_right (fun h => hbig ⟨v, hv, h⟩)
    exact (Finset.card_biUnion_le_card_mul B D q hsmall).trans (by omega)

def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (i : Fin m) : Finset ℕ := (Finset.Ico n (n + C.size)).filter fun w =>
      value C (onSet (y ∪ S i)) w = true ∧ ∀ j, j ≠ i → value C (onSet (y ∪ S j)) w = false

lemma card_diff_univ {n : ℕ} (A y : Finset (Fin n)) : (A \ y).card + y.card ≤ n := by
  have h1 : (A \ y).card ≤ (Finset.univ \ y).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ A) (subset_refl y))
  have h2 : (Finset.univ \ y).card + y.card = n := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ y)
    simpa using this
  omega

lemma line_count {q n m K : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (i : Fin m) (o c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ T : Finset (Fin n), y ⊆ T → (T \ y).card ≤ K →
      (value C (onSet T) o = true ↔ S i ⊆ T))
    (hc : c ≤ q) (hK : c * q < K ∨ n ≤ y.card + K) :
    min c ((S i \ y).card - 1) ≤ (specific C S y i).card := by
  classical
  by_contra! hsmall
  let G := specific C S y i
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBC, hcut⟩ := cut C hg G hgate (n + C.size) {o} (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ min c ((S i \ y).card - 1) := by
    have hf := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBC
    change G.card < min c ((S i \ y).card - 1) at hsmall
    omega
  have hmin1 := min_le_left c ((S i \ y).card - 1)
  have hmin2 := min_le_right c ((S i \ y).card - 1)
  have hbc : B.card ≤ c := le_trans hb hmin1
  have hpositive : 1 ≤ c := by
    change G.card < min c ((S i \ y).card - 1) at hsmall
    omega
  have hs2 : 2 ≤ (S i \ y).card := by
    change G.card < min c ((S i \ y).card - 1) at hsmall
    omega
  have hscard : (S i \ y).card ≤ q + 1 := by
    have := Finset.card_le_card (Finset.sdiff_subset : S i \ y ⊆ S i)
    rw [hsize] at this
    exact this
  have hsK : (S i \ y).card ≤ K := by
    rcases hK with hK | hK
    · have hp := Nat.mul_le_mul_right q hpositive
      rw [Nat.one_mul] at hp
      omega
    · have := card_diff_univ (S i) y
      omega
  have witness (w : ℕ) (hw : w ∈ B) : ∃ T : Finset (Fin n),
      ((T \ y).card ≤ q ∨ ∃ j, T \ y = S j \ y) ∧ ((T \ y) ∩ (S i \ y)).card ≤ 1 ∧
      (value C (onSet (y ∪ S i)) w = true → value C (onSet (y ∪ T)) w = true) := by
    by_cases hv : value C (onSet (y ∪ S i)) w = true
    · by_cases hin : w < n
      · let p : Fin n := ⟨w, hin⟩
        refine ⟨{p}, Or.inl ?_, ?_, ?_⟩
        · have := Finset.card_le_card (Finset.sdiff_subset : {p} \ y ⊆ {p})
          simp only [Finset.card_singleton] at this
          omega
        · have := Finset.card_le_card (Finset.inter_subset_left : ({p} \ y) ∩ (S i \ y) ⊆ {p} \ y)
          have h2 := Finset.card_le_card (Finset.sdiff_subset : {p} \ y ⊆ {p})
          simp only [Finset.card_singleton] at h2
          omega
        · intro _
          change value C (onSet (y ∪ {p})) p = true
          simp [input_value, onSet]
      · have bound : w < n + C.size := by
          by_contra! he
          simp [missing_value C _ w he] at hv
        have hn : w ∉ specific C S y i := Finset.disjoint_left.mp hd hw
        have hex : ∃ j, j ≠ i ∧ value C (onSet (y ∪ S j)) w = true := by
          by_contra! neg
          apply hn
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, bound⟩, hv, ?_⟩
          intro j hj
          simpa using neg j hj
        obtain ⟨j, hji, hj⟩ := hex
        refine ⟨S j, Or.inr ⟨j, rfl⟩, ?_, fun _ => hj⟩
        have hsub : (S j \ y) ∩ (S i \ y) ⊆ S j ∩ S i :=
          Finset.inter_subset_inter Finset.sdiff_subset Finset.sdiff_subset
        exact (Finset.card_le_card hsub).trans (hinter j i hji).le
    · exact ⟨∅, Or.inl (by simp), by simp, fun ht => False.elim (hv ht)⟩
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      (((A w) \ y).card ≤ q ∨ ∃ j, (A w) \ y = S j \ y) ∧ (((A w) \ y) ∩ (S i \ y)).card ≤ 1 ∧
      (value C (onSet (y ∪ S i)) w = true → value C (onSet (y ∪ A w)) w = true) := by
    simpa [A, hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hUdiff : U \ y = B.biUnion (fun w => A w \ y) := by
    ext p
    simp only [U, Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨w, hw, hp⟩, hpy⟩
      exact ⟨w, hw, hp, hpy⟩
    · rintro ⟨w, hw, hp, hpy⟩
      exact ⟨⟨w, hw, hp⟩, hpy⟩
  have hub : (U \ y).card ≤ B.card * q + 1 := by
    rw [hUdiff]
    refine union_bound (fun j => S j \ y) ?_ ?_ B (fun w => A w \ y) ?_
    · intro j
      have := Finset.card_le_card (Finset.sdiff_subset : S j \ y ⊆ S j)
      rw [hsize] at this
      exact this
    · intro i' j hij
      have hsub : (S j \ y) \ (S i' \ y) ⊆ S j \ S i' := by
        intro p hp
        simp only [Finset.mem_sdiff] at hp ⊢
        exact ⟨hp.1.1, fun h => hp.2 ⟨h, hp.1.2⟩⟩
      have he := Finset.card_sdiff_add_card_inter (S j) (S i')
      rw [hinter j i' (Ne.symm hij), hsize] at he
      have := Finset.card_le_card hsub
      omega
    · intro w hw
      exact (ha w hw).1
  have hu : ((y ∪ U) \ y).card ≤ K := by
    rw [Finset.union_sdiff_left]
    rcases hK with hK | hK
    · have h1 := Nat.mul_le_mul_right q hbc
      omega
    · have := card_diff_univ U y
      omega
  have hyi : y ⊆ y ∪ S i := Finset.subset_union_left
  have hyu : y ⊆ y ∪ U := Finset.subset_union_left
  have hsi : ((y ∪ S i) \ y).card ≤ K := by
    rw [Finset.union_sdiff_left]
    exact hsK
  have hot : value C (onSet (y ∪ U)) o = true := by
    apply hcut (onSet (y ∪ S i)) (onSet (y ∪ U)) _ o (Finset.mem_singleton_self o)
      ((heval (y ∪ S i) hyi hsi).mpr Finset.subset_union_right)
    intro w hw hp
    apply value_mono C hg (onSet (y ∪ A w)) (onSet (y ∪ U)) _ w ((ha w hw).2.2 hp)
    intro p hp
    have hp' : p ∈ y ∪ A w := of_decide_eq_true hp
    apply decide_eq_true
    rcases Finset.mem_union.mp hp' with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, h⟩)
  have hSub := (heval (y ∪ U) hyu hu).mp hot
  have hcover : S i \ y ⊆ B.biUnion (fun w => (A w \ y) ∩ (S i \ y)) := by
    intro p hp
    have hpS := (Finset.mem_sdiff.mp hp).1
    have hpy := (Finset.mem_sdiff.mp hp).2
    rcases Finset.mem_union.mp (hSub hpS) with h | h
    · exact absurd h hpy
    · obtain ⟨w, hw, hm⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hm, hpy⟩, hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => (A w \ y) ∩ (S i \ y)) 1
    (fun w hw => (ha w hw).2.1)
  simp only [Nat.mul_one] at h2
  omega

lemma main_bound {q n m K : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) →
      ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (hc : c ≤ q) (hK : c * q < K ∨ n ≤ y.card + K) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), min (c + 1) (S i \ y).card
      ≤ gates.length + (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let L := Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)
  let G (i : Fin m) := specific C S y i
  have hd : (L : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hi hj => ?_
    have hfalse := (Finset.mem_filter.mp hi).2.2 j (Ne.symm hij)
    have htrue := (Finset.mem_filter.mp hj).2.1
    simp [htrue] at hfalse
  have hi (i : Fin m) : min c ((S i \ y).card - 1) ≤ (G i).card := by
    apply line_count S y hq hsize hinter C i (out i) c hg _ hc hK
    intro T hyT hT
    have h := heval i (onSet T) (fun v hv => by simp [onSet, hyT hv])
      (by rw [filter_onSet]; exact hT)
    change value C (onSet T) (out i) = _ at h
    rw [h]
    simp [onSet, Finset.subset_iff]
  have hs : L.biUnion G ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).1
  calc
    ∑ i ∈ L, min (c + 1) (S i \ y).card
        ≤ ∑ i ∈ L, ((G i).card + 1) := by
          refine Finset.sum_le_sum (fun i hiL => ?_)
          have h2 : 2 ≤ (S i \ y).card := (Finset.mem_filter.mp hiL).2
          have := hi i
          omega
    _ = ∑ i ∈ L, (G i).card + L.card := by simp [Finset.sum_add_distrib]
    _ = (L.biUnion G).card + L.card := by rw [Finset.card_biUnion hd]
    _ ≤ (Finset.Ico n (n + C.size)).card + L.card := by
          have := Finset.card_le_card hs
          omega
    _ = gates.length + L.card := by simp [C, Circuit.size]

end PEqualNP.Outside.L_meta_1032

theorem PEqualNP.Outside.L_meta_1032 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) → ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → (c * q < K ∨ n ≤ y.card + K) → ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), min (c + 1) (S i \ y).card ≤ gates.length + (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
  classical
  intro q n m K S y hq hsize hinter gates out hg heval c hc hK
  exact PEqualNP.Outside.L_meta_1032.main_bound S y hq hsize hinter gates out hg heval c hc hK
