import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_842_aux

def W (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => 2 * W f b + f b

lemma W_succ (f : ℕ → ℕ) (b : ℕ) : W f (b+1) = 2 * W f b + f b := rfl

lemma W_congr (f g : ℕ → ℕ) (b : ℕ) (h : ∀ i < b, f i = g i) : W f b = W g b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [W_succ, W_succ, ih (fun i hi => h i (by omega)), h b (by omega)]

lemma W_sum {q : ℕ} (x : ℕ → Fin q → ℕ) (b : ℕ) :
    (∑ j, W (fun i => x i j) b) = W (fun i => ∑ j, x i j) b := by
  induction b with
  | zero => simp [W]
  | succ b ih =>
    simp only [W_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]

lemma W_mul (f : ℕ → ℕ) (E b : ℕ) : W (fun i => f i * E) b = W f b * E := by
  induction b with
  | zero => simp [W]
  | succ b ih => simp only [W_succ, ih]; ring

lemma W_range (f : ℕ → ℕ) (p : ℕ) :
    (∑ i ∈ Finset.range p, 2^(p-1-i) * f i) = W f p := by
  induction p with
  | zero => simp [W]
  | succ p ih =>
    rw [Finset.sum_range_succ, W_succ, ← ih, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_range.mp hi
      have : p+1-1-i = (p-1-i)+1 := by omega
      rw [this, pow_succ]; ring
    · simp

lemma W_fin (f : ℕ → ℕ) (p : ℕ) :
    (∑ i : Fin p, 2^(p-1-i.val) * f i.val) = W f p := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 2^(p-1-i) * f i) p]
  exact W_range f p

lemma W_mono (f : ℕ → ℕ) (b m : ℕ) : W f b * 2^m ≤ W f (b+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, W_succ, pow_succ, ← Nat.mul_assoc]
    omega

lemma W_count (u : ℕ → ℕ) (p : ℕ) (h0 : u 0 = 1) (h : ∀ b < p, u (b+1) ≤ 2 * u b) :
    ∀ b ≤ p, W (fun i => 2 * u i - u (i+1)) b + u b = 2^b := by
  intro b
  induction b with
  | zero => intro _; simp [W, h0]
  | succ b ih =>
    intro hb
    have h1 := ih (by omega)
    have h2 := h b (by omega)
    rw [W_succ, pow_succ]
    omega

lemma pick : ∀ (q : ℕ) (v : Fin q → ℕ) (t : ℕ), t ≤ ∑ j, v j →
    ∃ a : Fin q → ℕ, (∀ j, a j ≤ v j) ∧ (∑ j, a j) = t := by
  intro q
  induction q with
  | zero =>
    intro v t ht
    simp at ht
    exact ⟨v, fun _ => le_rfl, by simp [ht]⟩
  | succ q ih =>
    intro v t ht
    rw [Fin.sum_univ_succ] at ht
    obtain ⟨a, ha, hs⟩ := ih (fun j => v j.succ) (t - min (v 0) t) (by omega)
    refine ⟨Fin.cons (min (v 0) t) a, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro i; simpa using ha i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hs]
      omega

lemma split (q E : ℕ) : ∀ (k : ℕ) (v : Fin q → ℕ), (∑ j, v j) = k * E →
    ∃ g : Fin k → Fin q → ℕ, (∀ w, (∑ j, g w j) = E) ∧ ∀ j, (∑ w, g w j) = v j := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [Nat.zero_mul] at hv
    refine ⟨fun w => w.elim0, fun w => w.elim0, fun j => ?_⟩
    have := (Finset.sum_eq_zero_iff.mp hv) j (Finset.mem_univ j)
    simp [this]
  | succ k ih =>
    intro v hv
    rw [Nat.succ_mul] at hv
    obtain ⟨a, ha, hs⟩ := pick q v E (by omega)
    have hr : (∑ j, (v j - a j)) = k * E := by
      rw [Finset.sum_tsub_distrib _ (fun j _ => ha j), hv, hs]
      omega
    obtain ⟨g, hg1, hg2⟩ := ih (fun j => v j - a j) hr
    refine ⟨Fin.cons a g, ?_, ?_⟩
    · intro w
      refine Fin.cases ?_ ?_ w
      · simpa using hs
      · intro i; simpa using hg1 i
    · intro j
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hg2]
      have := ha j
      omega

lemma floor_step (M p b : ℕ) (hb : b < p) : 2 * (M / 2^(p-b)) ≤ M / 2^(p-(b+1)) := by
  have : p - b = (p-(b+1)) + 1 := by omega
  rw [this, pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ 2

lemma greedy (p E q : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ) (h0 : u 0 = 1)
    (h : ∀ b < p, u (b+1) ≤ 2 * u b)
    (hc : ∀ b ≤ p, E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b)) :
    ∀ b ≤ p, ∃ x : ℕ → Fin q → ℕ,
      (∀ i < b, (∑ j, x i j) = (2 * u i - u (i+1)) * E) ∧
      ∀ j, W (fun i => x i j) b ≤ M j / 2^(p-b) := by
  intro b
  induction b with
  | zero =>
    intro _
    exact ⟨fun _ _ => 0, fun i hi => by omega, fun j => by simp [W]⟩
  | succ b ih =>
    intro hb
    have hbp : b < p := by omega
    obtain ⟨x, hx1, hx2⟩ := ih (by omega)
    have hle : ∀ j, 2 * W (fun i => x i j) b ≤ M j / 2^(p-(b+1)) := fun j =>
      le_trans (Nat.mul_le_mul_left 2 (hx2 j)) (floor_step (M j) p b hbp)
    have hT : (∑ j, 2 * W (fun i => x i j) b) = 2 * (W (fun i => 2 * u i - u (i+1)) b * E) := by
      rw [← Finset.mul_sum, W_sum, ← W_mul]
      congr 1
      exact W_congr _ _ _ hx1
    have hcount := W_count u p h0 h (b+1) hb
    rw [W_succ] at hcount
    have hreq : (2 * u b - u (b+1)) * E ≤
        ∑ j, (M j / 2^(p-(b+1)) - 2 * W (fun i => x i j) b) := by
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle j), hT]
      have h1 := hc (b+1) hb
      have h2 : 2^(b+1) - u (b+1) =
          2 * W (fun i => 2 * u i - u (i+1)) b + (2 * u b - u (b+1)) := by omega
      rw [h2] at h1
      have h3 : E * (2 * W (fun i => 2 * u i - u (i+1)) b + (2 * u b - u (b+1)))
          = 2 * (W (fun i => 2 * u i - u (i+1)) b * E) + (2 * u b - u (b+1)) * E := by ring
      rw [h3] at h1
      omega
    obtain ⟨a, ha, hs⟩ := pick q _ _ hreq
    have hup : ∀ i < b, ∀ j, Function.update x b a i j = x i j := by
      intro i hi j
      rw [Function.update_of_ne (by omega : i ≠ b)]
    refine ⟨Function.update x b a, ?_, ?_⟩
    · intro i hi
      by_cases hib : i = b
      · subst hib
        rw [Function.update_self]
        exact hs
      · rw [Function.update_of_ne hib]
        exact hx1 i (by omega)
    · intro j
      rw [W_succ, W_congr _ (fun i => x i j) b (fun i hi => hup i hi j), Function.update_self]
      have h1 := ha j
      have h2 := hle j
      omega

lemma main (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hM : (∑ j, M j) = (2^p-1)*E)
    (u : ℕ → ℕ) (h0 : u 0 = 1) (hp1 : u p = 1) (h : ∀ b < p, u (b+1) ≤ 2 * u b) :
    (∃ g : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, g i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, g i w j) = M j) ↔
      ∀ b ≤ p, 2^b - (∑ j, M j / 2^(p-b))/E ≤ u b := by
  constructor
  · rintro ⟨g, hg1, hg2⟩ b hb
    let x : ℕ → Fin q → ℕ := fun i j => if hi : i < p then ∑ w, g ⟨i, hi⟩ w j else 0
    have hx1 : ∀ i < p, (∑ j, x i j) = (2 * u i - u (i+1)) * E := by
      intro i hi
      simp only [x, dite_eq_left hi]
      rw [Finset.sum_comm]
      simp [hg1]
    have hx2 : ∀ j, W (fun i => x i j) p = M j := by
      intro j
      rw [← W_fin, ← hg2 j]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [x, dite_eq_left i.isLt, Fin.eta]
    have hx3 : ∀ j, W (fun i => x i j) b ≤ M j / 2^(p-b) := by
      intro j
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← hx2 j]
      have := W_mono (fun i => x i j) b (p-b)
      rwa [Nat.add_sub_cancel' hb] at this
    have hsum : W (fun i => 2 * u i - u (i+1)) b * E ≤ ∑ j, M j / 2^(p-b) := by
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun j _ => hx3 j))
      rw [W_sum, ← W_mul]
      exact W_congr _ _ _ (fun i hi => (hx1 i (by omega)).symm)
    have hdiv := (Nat.le_div_iff_mul_le hE).mpr hsum
    have hcount := W_count u p h0 h b hb
    omega
  · intro hbest
    have hc : ∀ b ≤ p, E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b) := by
      intro b hb
      have h1 := hbest b hb
      have h2 : 2^b - u b ≤ (∑ j, M j / 2^(p-b))/E := tsub_le_iff_tsub_le.mp h1
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hE).mp h2
    obtain ⟨x, hx1, hx2⟩ := greedy p E q M u h0 h hc p le_rfl
    simp only [Nat.sub_self, pow_zero, Nat.div_one] at hx2
    have htot : (∑ j, W (fun i => x i j) p) = ∑ j, M j := by
      rw [W_sum, W_congr _ _ _ hx1, W_mul, hM]
      have hcount := W_count u p h0 h p le_rfl
      have : W (fun i => 2 * u i - u (i+1)) p = 2^p - 1 := by omega
      rw [this]
    have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hx2 j)).mp htot
    have hs : ∀ i : Fin p, ∃ g : Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
        (∀ w, (∑ j, g w j) = E) ∧ ∀ j, (∑ w, g w j) = x i.val j :=
      fun i => split q E _ (x i.val) (hx1 i.val i.isLt)
    choose g hg1 hg2 using hs
    refine ⟨g, hg1, fun j => ?_⟩
    simp only [hg2]
    rw [W_fin (fun i => x i j)]
    exact heq j (Finset.mem_univ j)

end PEqualNP.Outside.L_lib_842_aux

theorem PEqualNP.Outside.L_lib_842 : (∀ (p E q : ℕ), 0 < p → 0 < E → ∀ M : Fin q → ℕ,
  (∑ j, M j) = (2^p-1)*E →
  let cap := fun b : ℕ => ∑ j, M j / 2^(p-b)
  let best := fun b : ℕ => 2^b-cap b/E
  let shape := fun u : ℕ → ℕ =>
    u 0 = 1 ∧ u p = 1 ∧ ∀ b < p, u (b+1) ≤ 2*u b
  let fits := fun u : ℕ → ℕ =>
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j
  (∀ u, shape u → (fits u ↔ ∀ b ≤ p, best b ≤ u b)) ∧ shape best ∧ fits best) := by
  intro p E q hp hE M hM cap best shape fits
  have key : ∀ u, shape u → (fits u ↔ ∀ b ≤ p, best b ≤ u b) := fun u hu =>
    PEqualNP.Outside.L_lib_842_aux.main p E q hE M hM u hu.1 hu.2.1 hu.2.2
  have hcap : ∀ b < p, 2 * cap b ≤ cap (b+1) := by
    intro b hb
    show 2 * (∑ j, M j / 2^(p-b)) ≤ ∑ j, M j / 2^(p-(b+1))
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => PEqualNP.Outside.L_lib_842_aux.floor_step (M j) p b hb)
  have hshape : shape best := by
    refine ⟨?_, ?_, ?_⟩
    · have h1 : cap 0 * 2^p ≤ (2^p-1)*E := by
        rw [← hM]
        show (∑ j, M j / 2^(p-0)) * 2^p ≤ ∑ j, M j
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
      have h2 : cap 0 < E := by
        have h3 : (2^p-1)*E < E * 2^p := by
          rw [Nat.mul_comm E]
          exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos p) Nat.one_pos) hE
        exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 h3)
      show 2^0 - cap 0 / E = 1
      rw [Nat.div_eq_of_lt h2]
      rfl
    · have h1 : cap p = (2^p-1)*E := by
        rw [← hM]
        show (∑ j, M j / 2^(p-p)) = ∑ j, M j
        simp
      show 2^p - cap p / E = 1
      rw [h1, Nat.mul_div_cancel _ hE]
      have := Nat.two_pow_pos p
      omega
    · intro b hb
      show 2^(b+1) - cap (b+1) / E ≤ 2 * (2^b - cap b / E)
      have h1 : 2 * (cap b / E) ≤ cap (b+1) / E := by
        rw [Nat.le_div_iff_mul_le hE, Nat.mul_assoc]
        exact le_trans (Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _)) (hcap b hb)
      rw [pow_succ]
      omega
  exact ⟨key, hshape, (key best hshape).mpr (fun _ _ => le_rfl)⟩
