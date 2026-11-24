import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5084 : ∀ (x1 : ℕ) (x2 x3 : Finset (Finset (Fin x1))) (x4 : Fin x1 → Prop), (∀ x5 ∈ x2.biUnion fun (x6 : Finset (Fin x1)) => Finset.image (fun (x7 : Finset (Fin x1)) => x6 ∪ x7) x3, ∃ x7 ∈ x5, x4 x7) ↔ (∀ x5 ∈ x2, ∃ x7 ∈ x5, x4 x7) ∨ ∀ x5 ∈ x3, ∃ x7 ∈ x5, x4 x7 := by
  intro n F G P
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha, hna⟩, ⟨b, hb, hnb⟩⟩ : (∃ a ∈ F, ∀ x ∈ a, ¬P x) ∧ ∃ b ∈ G, ∀ x ∈ b, ¬P x := hcon
    have hmem : a ∪ b ∈ F.biUnion fun s => Finset.image (fun t => s ∪ t) G := by
      simp only [Finset.mem_biUnion, Finset.mem_image]
      exact ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x, hx, hPx⟩ := h _ hmem
    rcases Finset.mem_union.mp hx with h1 | h1
    · exact hna x h1 hPx
    · exact hnb x h1 hPx
  · intro h s hs
    simp only [Finset.mem_biUnion, Finset.mem_image] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    rcases h with h | h
    · obtain ⟨x, hx, hP⟩ := h a ha
      exact ⟨x, Finset.mem_union_left _ hx, hP⟩
    · obtain ⟨x, hx, hP⟩ := h b hb
      exact ⟨x, Finset.mem_union_right _ hx, hP⟩
