import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), ∀ x8 ∈ x7, x1 + (2 : ℕ) ≤ x7.card + Fintype.card { x10 : Fin x2 // x3 x10 x8 ∧ ∀ x11 ∈ x7.erase x8, ¬x3 x10 x11 } := by
  intro x1 x2 x3 x4 h1 h2 S l hl
  classical
  have hc := h1 l
  rw [Fintype.card_subtype] at hc
  rw [Fintype.card_subtype]
  set T : Finset (Fin x2) := S.erase l with hT
  have hsub : (Finset.univ.filter (fun p => x3 p l)) ⊆
      (Finset.univ.filter (fun p => x3 p l ∧ ∀ m ∈ T, ¬x3 p m)) ∪
        T.biUnion (fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    by_cases hall : ∀ m ∈ T, ¬x3 p m
    · exact Or.inl ⟨hp, hall⟩
    · push_neg at hall
      obtain ⟨m, hm, hpm⟩ := hall
      exact Or.inr ⟨m, hm, hp, hpm⟩
  have hone : ∀ m ∈ T, (Finset.univ.filter (fun p => x3 p l ∧ x3 p m)).card ≤ 1 := by
    intro m hm
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨n, -, hu⟩ := h2 a b hab
    have e1 := hu l ⟨ha.1, hb.1⟩
    have e2 := hu m ⟨ha.2, hb.2⟩
    exact (Finset.ne_of_mem_erase hm) (e2.trans e1.symm)
  have h3 := Finset.card_le_card hsub
  rw [hc] at h3
  have h4 := Finset.card_union_le (Finset.univ.filter (fun p => x3 p l ∧ ∀ m ∈ T, ¬x3 p m))
    (T.biUnion (fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m)))
  have h5 := Finset.card_biUnion_le (s := T) (t := fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m))
  have h6 := Finset.sum_le_card_nsmul T _ 1 hone
  simp only [smul_eq_mul, mul_one] at h6
  have h7 : T.card = S.card - 1 := Finset.card_erase_of_mem hl
  have h8 : 0 < S.card := Finset.card_pos.mpr ⟨l, hl⟩
  omega
