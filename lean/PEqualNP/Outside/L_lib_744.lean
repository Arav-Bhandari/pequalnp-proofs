import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_744_aux

open Finset

def f (m h b r d : ℕ) : ℕ :=
  ∑ z ∈ (range (d+1)).filter (fun z => 64*(h+z) < m), Nat.choose b z * Nat.choose r (d-z)

lemma absorb (b z : ℕ) : b * Nat.choose (b-1) z = (z+1) * Nat.choose b (z+1) := by
  cases b with
  | zero => simp
  | succ n => rw [Nat.add_sub_cancel, Nat.add_one_mul_choose_eq, mul_comm]

lemma identity (m h b r d : ℕ) :
    b * f m (h+1) (b-1) r d + r * f m h b (r-1) d = (d+1) * f m h b r (d+1) := by
  unfold f
  rw [sum_filter, sum_filter, sum_filter, mul_sum, mul_sum, mul_sum]
  have h1 : ∑ z ∈ range (d+1),
        b * (if 64*(h+1+z) < m then Nat.choose (b-1) z * Nat.choose r (d-z) else 0)
      = ∑ w ∈ range (d+1+1),
        (if 64*(h+w) < m then w * (Nat.choose b w * Nat.choose r (d+1-w)) else 0) := by
    rw [sum_range_succ' _ (d+1)]
    simp only [zero_mul, ite_self, add_zero]
    refine sum_congr rfl fun z _ => ?_
    rw [show h + (z+1) = h+1+z by omega, show d+1-(z+1) = d - z by omega]
    split_ifs
    · rw [← mul_assoc, absorb, mul_assoc]
    · simp
  have h2 : ∑ z ∈ range (d+1),
        r * (if 64*(h+z) < m then Nat.choose b z * Nat.choose (r-1) (d-z) else 0)
      = ∑ w ∈ range (d+1+1),
        (if 64*(h+w) < m then (d+1-w) * (Nat.choose b w * Nat.choose r (d+1-w)) else 0) := by
    rw [sum_range_succ _ (d+1)]
    simp only [Nat.sub_self, zero_mul, ite_self, add_zero]
    refine sum_congr rfl fun z hz => ?_
    have hz' : z ≤ d := by
      rw [mem_range] at hz
      omega
    rw [show d+1-z = (d-z)+1 by omega]
    split_ifs
    · rw [mul_left_comm, absorb, mul_left_comm]
    · simp
  rw [h1, h2, ← sum_add_distrib]
  refine sum_congr rfl fun w hw => ?_
  rw [mem_range] at hw
  split_ifs
  · rw [← add_mul, show w + (d+1-w) = d+1 by omega]
  · simp

section generic
variable {α β : Type*} [DecidableEq α]

def sc (U : Finset α) (m : ℕ) (T : Finset β) (B : β → Finset α) (P : Finset α) : ℕ :=
  ∑ e ∈ T, f m (P ∩ B e).card (B e \ P).card ((U \ P) \ B e).card (m - P.card)

lemma avg (U : Finset α) (m : ℕ) (T : Finset β) (B : β → Finset α)
    (hB : ∀ e ∈ T, B e ⊆ U) (P : Finset α) (hlt : P.card < m) :
    ∑ x ∈ U \ P, sc U m T B (insert x P) = (m - P.card) * sc U m T B P := by
  unfold sc
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun e he => ?_
  obtain ⟨d, hd⟩ : ∃ d, m - P.card = d+1 := ⟨m - P.card - 1, by omega⟩
  rw [hd, ← sum_filter_add_sum_filter_not (U \ P) (fun x => x ∈ B e)]
  have e1 : (U \ P).filter (fun x => x ∈ B e) = B e \ P := by
    ext x
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩
      exact ⟨h', h⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨hB e he h, h'⟩, h⟩
  have e2 : (U \ P).filter (fun x => x ∉ B e) = (U \ P) \ B e := by
    ext x
    simp only [mem_filter, mem_sdiff]
  rw [e1, e2, ← identity m (P ∩ B e).card (B e \ P).card ((U \ P) \ B e).card d]
  congr 1
  · rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun x hx => ?_
    have hxB := (mem_sdiff.1 hx).1
    have hxP := (mem_sdiff.1 hx).2
    have a1 : (insert x P ∩ B e).card = (P ∩ B e).card + 1 := by
      rw [insert_inter_of_mem hxB, card_insert_of_notMem (fun h => hxP (mem_inter.1 h).1)]
    have a2 : (B e \ insert x P).card = (B e \ P).card - 1 := by
      rw [sdiff_insert, card_erase_of_mem hx]
    have a3 : (U \ insert x P) \ B e = (U \ P) \ B e := by
      ext y
      simp only [mem_sdiff, mem_insert, not_or]
      constructor
      · rintro ⟨⟨h1, _, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun h => h3 (h ▸ hxB), h2⟩, h3⟩
    have a4 : m - (insert x P).card = d := by
      rw [card_insert_of_notMem hxP]
      omega
    rw [a1, a2, a3, a4]
  · rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun x hx => ?_
    have hxB := (mem_sdiff.1 hx).2
    have hxP := (mem_sdiff.1 (mem_sdiff.1 hx).1).2
    have a1 : insert x P ∩ B e = P ∩ B e := insert_inter_of_notMem hxB
    have a2 : B e \ insert x P = B e \ P := by
      exact sdiff_insert_of_notMem hxB _
    have a3 : ((U \ insert x P) \ B e).card = ((U \ P) \ B e).card - 1 := by
      rw [← card_erase_of_mem hx]
      congr 1
      ext y
      simp only [mem_sdiff, mem_insert, mem_erase, not_or, ne_eq]
      tauto
    have a4 : m - (insert x P).card = d := by
      rw [card_insert_of_notMem hxP]
      omega
    rw [a1, a2, a3, a4]

def G (U : Finset α) (m : ℕ) (S : Finset α → ℕ) (walk : ℕ → Finset α) : Prop :=
  walk 0 = ∅ ∧ ∀ i : ℕ, i < m →
    ∃ y ∈ U \ walk i, walk (i+1) = insert y (walk i) ∧
      ∀ x ∈ U \ walk i, S (walk (i+1)) ≤ S (insert x (walk i))

lemma shape (U : Finset α) (m : ℕ) (S : Finset α → ℕ) (walk : ℕ → Finset α)
    (hG : G U m S walk) : ∀ i, i ≤ m → walk i ⊆ U ∧ (walk i).card = i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [hG.1]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    obtain ⟨y, hy, heq, _⟩ := hG.2 i (by omega)
    rw [heq]
    exact ⟨insert_subset (mem_sdiff.1 hy).1 ih'.1,
      by rw [card_insert_of_notMem (mem_sdiff.1 hy).2, ih'.2]⟩

lemma exists_walk (U : Finset α) (m : ℕ) (S : Finset α → ℕ) (hm : m ≤ U.card) :
    ∃ walk, G U m S walk := by
  classical
  have key : ∀ P : Finset α, ∃ Q : Finset α, P ⊆ U → P.card < m →
      ∃ y ∈ U \ P, Q = insert y P ∧ ∀ x ∈ U \ P, S Q ≤ S (insert x P) := by
    intro P
    by_cases h : (U \ P).Nonempty
    · obtain ⟨y, hy, hmin⟩ := exists_min_image (U \ P) (fun x => S (insert x P)) h
      exact ⟨insert y P, fun _ _ => ⟨y, hy, rfl, hmin⟩⟩
    · refine ⟨P, fun hP hlt => absurd ?_ h⟩
      rw [← card_pos, card_sdiff_of_subset hP]
      omega
  choose step hstep using key
  have inv : ∀ n, n ≤ m → step^[n] ∅ ⊆ U ∧ (step^[n] ∅).card = n := by
    intro n
    induction n with
    | zero =>
      intro _
      simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      obtain ⟨y, hy, heq, _⟩ := hstep _ ih'.1 (by omega)
      rw [Function.iterate_succ_apply', heq]
      exact ⟨insert_subset (mem_sdiff.1 hy).1 ih'.1,
        by rw [card_insert_of_notMem (mem_sdiff.1 hy).2, ih'.2]⟩
  refine ⟨fun n => step^[n] ∅, rfl, fun i hi => ?_⟩
  have h := inv i (by omega)
  simp only [Function.iterate_succ_apply']
  exact hstep _ h.1 (by omega)

lemma pot (U : Finset α) (m : ℕ) (S : Finset α → ℕ) (hm : m ≤ U.card)
    (havg : ∀ P : Finset α, P ⊆ U → P.card < m →
      ∑ x ∈ U \ P, S (insert x P) ≤ (m - P.card) * S P)
    (h0 : S ∅ < Nat.choose U.card m) (walk : ℕ → Finset α) (hG : G U m S walk) :
    ∀ i, i ≤ m → S (walk i) < Nat.choose (U.card - i) (m - i) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [hG.1] using h0
  | succ i ih =>
    intro hi
    have hs := shape U m S walk hG i (by omega)
    obtain ⟨y, _, _, hmin⟩ := hG.2 i (by omega)
    have h1 : (U.card - i) * S (walk (i+1)) ≤ (m - i) * S (walk i) := by
      have a := card_nsmul_le_sum (U \ walk i) (fun x => S (insert x (walk i))) _ hmin
      rw [card_sdiff_of_subset hs.1, hs.2, smul_eq_mul] at a
      have b := havg _ hs.1 (by omega)
      rw [hs.2] at b
      exact le_trans a b
    have h3 : (U.card - i) * Nat.choose (U.card - (i+1)) (m - (i+1))
        = (m - i) * Nat.choose (U.card - i) (m - i) := by
      have a := Nat.add_one_mul_choose_eq (U.card - (i+1)) (m - (i+1))
      rw [show U.card - (i+1) + 1 = U.card - i by omega,
        show m - (i+1) + 1 = m - i by omega] at a
      rw [a, mul_comm]
    have h4 : (U.card - i) * S (walk (i+1))
        < (U.card - i) * Nat.choose (U.card - (i+1)) (m - (i+1)) := by
      rw [h3]
      exact lt_of_le_of_lt h1 (Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by omega))
    exact Nat.lt_of_mul_lt_mul_left h4

end generic

lemma pow_choose (r N : ℕ) (h : 16*r ≤ 15*N) (i : ℕ) :
    16^i * Nat.choose r i ≤ 15^i * Nat.choose N i := by
  induction i with
  | zero => simp
  | succ i ih =>
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos i)
    calc 16^(i+1) * Nat.choose r (i+1) * (i+1)
        = (16^i * Nat.choose r i) * (16 * (r-i)) := by
          rw [mul_assoc, Nat.choose_succ_right_eq, pow_succ]
          ring
      _ ≤ (15^i * Nat.choose N i) * (15 * (N-i)) := Nat.mul_le_mul ih (by omega)
      _ = 15^(i+1) * Nat.choose N (i+1) * (i+1) := by
          rw [mul_assoc (15^(i+1)), Nat.choose_succ_right_eq, pow_succ]
          ring

lemma expand (r b m : ℕ) :
    ∑ z ∈ range (m+1), Nat.choose b z * Nat.choose r (m-z) * 2^(m-z)
      = ∑ i ∈ range (m+1), Nat.choose r i * Nat.choose (r+b-i) (m-i) := by
  rw [← sum_range_reflect]
  have a : ∀ j ∈ range (m+1),
      Nat.choose b (m+1-1-j) * Nat.choose r (m-(m+1-1-j)) * 2^(m-(m+1-1-j))
        = ∑ i ∈ range (m+1), Nat.choose b (m-j) * (Nat.choose r j * Nat.choose j i) := by
    intro j hj
    rw [mem_range] at hj
    rw [show m+1-1-j = m - j by omega, show m - (m-j) = j by omega]
    have two : 2^j = ∑ i ∈ range (m+1), Nat.choose j i := by
      rw [← Nat.sum_range_choose j]
      refine sum_subset (range_mono (by omega)) fun i _ hi => ?_
      rw [mem_range] at hi
      exact Nat.choose_eq_zero_of_lt (by omega)
    rw [two, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl a, sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have split : range (m+1) = range (i + (m-i+1)) := by
    congr 1
    omega
  rw [split, sum_range_add]
  have z : ∑ j ∈ range i, Nat.choose b (m-j) * (Nat.choose r j * Nat.choose j i) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt hj, mul_zero, mul_zero]
  rw [z, zero_add]
  have t : ∀ t ∈ range (m-i+1),
      Nat.choose b (m-(i+t)) * (Nat.choose r (i+t) * Nat.choose (i+t) i)
        = Nat.choose r i * (Nat.choose (r-i) t * Nat.choose b (m-i-t)) := by
    intro t _
    rw [Nat.choose_mul (Nat.le_add_right i t), Nat.add_sub_cancel_left, Nat.sub_add_eq]
    ring
  rw [sum_congr rfl t, ← mul_sum,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => Nat.choose (r-i) x * Nat.choose b y) (m-i),
    ← Nat.add_choose_eq]
  by_cases h : i ≤ r
  · rw [show r - i + b = r + b - i by omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega : r < i), zero_mul, zero_mul]

lemma tail (b r s : ℕ) (hbr : 16 * r ≤ 15 * (r + b)) :
    f (256*s) 0 b r (256*s) * 32^(256*s)
      ≤ 2^(4*s) * Nat.choose (r+b) (256*s) * 31^(256*s) := by
  obtain ⟨m, hm⟩ : ∃ m, m = 256*s := ⟨_, rfl⟩
  rw [← hm]
  have hsm : 4*s ≤ m := by omega
  have h1 : f m 0 b r m * 2^(m - 4*s)
      ≤ ∑ z ∈ range (m+1), Nat.choose b z * Nat.choose r (m-z) * 2^(m-z) := by
    unfold f
    rw [sum_mul]
    refine le_trans (sum_le_sum fun z hz => ?_) (sum_le_sum_of_subset (filter_subset
      (fun z => 64*(0+z) < m) (range (m+1))))
    have := (mem_filter.1 hz).2
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : (∑ i ∈ range (m+1), Nat.choose r i * Nat.choose (r+b-i) (m-i)) * 16^m
      ≤ Nat.choose (r+b) m * 31^m := by
    have bin := add_pow (15:ℕ) 16 m
    rw [show (15:ℕ) + 16 = 31 by norm_num] at bin
    rw [bin, mul_sum, sum_mul]
    refine sum_le_sum fun i hi => ?_
    have hi' : i ≤ m := by
      rw [mem_range] at hi
      omega
    calc Nat.choose r i * Nat.choose (r+b-i) (m-i) * 16^m
        = (16^i * Nat.choose r i) * (Nat.choose (r+b-i) (m-i) * 16^(m-i)) := by
          rw [← pow_mul_pow_sub (16:ℕ) hi']
          ring
      _ ≤ (15^i * Nat.choose (r+b) i) * (Nat.choose (r+b-i) (m-i) * 16^(m-i)) :=
          Nat.mul_le_mul_right _ (pow_choose r (r+b) hbr i)
      _ = (Nat.choose (r+b) i * Nat.choose (r+b-i) (m-i)) * (15^i * 16^(m-i)) := by ring
      _ = Nat.choose (r+b) m * (15^i * 16^(m-i) * Nat.choose m i) := by
          rw [← Nat.choose_mul hi']
          ring
  rw [expand] at h1
  calc f m 0 b r m * 32^m
      = (f m 0 b r m * 2^(m - 4*s)) * 16^m * 2^(4*s) := by
        rw [show (32:ℕ) = 2*16 by norm_num, mul_pow, ← pow_sub_mul_pow (2:ℕ) hsm]
        ring
    _ ≤ (∑ i ∈ range (m+1), Nat.choose r i * Nat.choose (r+b-i) (m-i)) * 16^m * 2^(4*s) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ ≤ Nat.choose (r+b) m * 31^m * 2^(4*s) := Nat.mul_le_mul_right _ h2
    _ = 2^(4*s) * Nat.choose (r+b) m * 31^m := by ring

lemma num (s : ℕ) (hs : 4 ≤ s) :
    2^(3*s) * 8 * 2^(4*s) * 31^(256*s) < 32^(256*s) := by
  have h1 : 2^(3*s) * 8 * 2^(4*s) < 2^(8*s) := by
    calc 2^(3*s) * 8 * 2^(4*s) = 2^(3*s+3+4*s) := by
          rw [pow_add, pow_add]
          norm_num
      _ < 2^(8*s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2^(8*s) * 31^(256*s) ≤ 32^(256*s) := by
    rw [show 256*s = 32*(8*s) by ring, pow_mul (31:ℕ), pow_mul (32:ℕ), ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 (by positivity)) h2

end PEqualNP.Outside.L_lib_744_aux

theorem PEqualNP.Outside.L_lib_744 : (∀ s : ℕ, 4 ≤ s →
  let F := ZMod 2
  let W := Fin s → F
  let R := Fin 3 → F
  let U : Finset W := Finset.univ.erase 0
  let m := min (256*s) U.card
  let E := (Fin 3 → W) × R
  let fiber := fun e : E => U.filter (fun y =>
    ∀ i : Fin 3, (∑ j : Fin s, e.1 i j * y j) = e.2 i)
  let tests := (Finset.univ : Finset E).filter (fun e => U.card ≤ 16*(fiber e).card)
  let score := fun P : Finset W =>
    let d := m-P.card
    ∑ e ∈ tests,
      let B := fiber e
      ∑ z ∈ (Finset.range (d+1)).filter (fun z => 64*((P ∩ B).card+z) < m),
        Nat.choose (B \ P).card z *
          Nat.choose ((U \ P) \ B).card (d-z)
  let greedy := fun walk : ℕ → Finset W =>
    walk 0 = ∅ ∧ ∀ i : ℕ, i < m →
      ∃ y ∈ U \ walk i, walk (i+1) = insert y (walk i) ∧
        ∀ x ∈ U \ walk i, score (walk (i+1)) ≤ score (insert x (walk i))
  (∃ walk, greedy walk) ∧ ∀ walk, greedy walk →
    walk m ⊆ U ∧ (walk m).card = m ∧ ∀ e ∈ tests, m ≤ 64*((walk m ∩ fiber e).card)) := by
  intro s hs F W R U m E fiber tests score greedy
  have hmU : m ≤ U.card := min_le_right _ _
  have hB : ∀ e ∈ tests, fiber e ⊆ U := fun e _ => Finset.filter_subset _ _
  have hex : ∃ walk, greedy walk :=
    PEqualNP.Outside.L_lib_744_aux.exists_walk U m score hmU
  refine ⟨hex, fun walk hw => ?_⟩
  have hsh := PEqualNP.Outside.L_lib_744_aux.shape U m score walk hw m le_rfl
  refine ⟨hsh.1, hsh.2, ?_⟩
  rcases le_total (256*s) U.card with hc | hc
  · have hm : m = 256*s := min_eq_left hc
    have hscore : score = PEqualNP.Outside.L_lib_744_aux.sc U m tests fiber := rfl
    have h0 : PEqualNP.Outside.L_lib_744_aux.sc U m tests fiber ∅ < Nat.choose U.card m := by
      have hT : tests.card ≤ 2^(3*s) * 8 := by
        refine (Finset.card_le_univ _).trans_eq ?_
        show Fintype.card ((Fin 3 → (Fin s → ZMod 2)) × (Fin 3 → ZMod 2)) = _
        simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        rw [← pow_mul, mul_comm s 3]
        norm_num
      have key : ∀ e ∈ tests,
          PEqualNP.Outside.L_lib_744_aux.f m ((∅ : Finset W) ∩ fiber e).card
              (fiber e \ ∅).card ((U \ ∅) \ fiber e).card (m - (∅ : Finset W).card) * 32^m
            ≤ 2^(4*s) * Nat.choose U.card m * 31^m := by
        intro e he
        rw [Finset.empty_inter, Finset.card_empty, Finset.sdiff_empty, Finset.sdiff_empty,
          Nat.sub_zero]
        have hcard : (U \ fiber e).card + (fiber e).card = U.card :=
          Finset.card_sdiff_add_card_eq_card (hB e he)
        have h16 : U.card ≤ 16*(fiber e).card := (Finset.mem_filter.1 he).2
        have t := PEqualNP.Outside.L_lib_744_aux.tail (fiber e).card (U \ fiber e).card s
          (by omega)
        rw [hcard, ← hm] at t
        exact t
      have total : PEqualNP.Outside.L_lib_744_aux.sc U m tests fiber ∅ * 32^m
          ≤ tests.card * (2^(4*s) * Nat.choose U.card m * 31^m) := by
        unfold PEqualNP.Outside.L_lib_744_aux.sc
        rw [Finset.sum_mul, ← smul_eq_mul tests.card]
        exact Finset.sum_le_card_nsmul _ _ _ key
      have lt : PEqualNP.Outside.L_lib_744_aux.sc U m tests fiber ∅ * 32^m
          < Nat.choose U.card m * 32^m := by
        calc _ ≤ tests.card * (2^(4*s) * Nat.choose U.card m * 31^m) := total
          _ ≤ (2^(3*s) * 8) * (2^(4*s) * Nat.choose U.card m * 31^m) :=
              Nat.mul_le_mul_right _ hT
          _ = (2^(3*s) * 8 * 2^(4*s) * 31^m) * Nat.choose U.card m := by ring
          _ < 32^m * Nat.choose U.card m := by
              refine Nat.mul_lt_mul_of_pos_right ?_ (Nat.choose_pos hmU)
              rw [hm]
              exact PEqualNP.Outside.L_lib_744_aux.num s hs
          _ = _ := mul_comm _ _
      exact Nat.lt_of_mul_lt_mul_right lt
    have hpot := PEqualNP.Outside.L_lib_744_aux.pot U m score hmU
      (fun P _ hlt => by
        rw [hscore]
        exact (PEqualNP.Outside.L_lib_744_aux.avg U m tests fiber hB P hlt).le)
      h0 walk hw m le_rfl
    rw [Nat.sub_self, Nat.choose_zero_right] at hpot
    have hz : PEqualNP.Outside.L_lib_744_aux.sc U m tests fiber (walk m) = 0 :=
      Nat.lt_one_iff.1 hpot
    intro e he
    have h := (Finset.sum_eq_zero_iff.1 hz) e he
    by_contra hcon
    unfold PEqualNP.Outside.L_lib_744_aux.f at h
    rw [hsh.2, Nat.sub_self, Finset.sum_filter, Finset.sum_range_one, ite_eq_left (by omega)] at h
    simp at h
  · have hm : m = U.card := min_eq_right hc
    have hall : walk m = U := Finset.eq_of_subset_of_card_le hsh.1 (by rw [hsh.2, hm])
    intro e he
    have h16 : U.card ≤ 16*(fiber e).card := (Finset.mem_filter.1 he).2
    rw [hall, Finset.inter_eq_right.2 (hB e he)]
    omega
