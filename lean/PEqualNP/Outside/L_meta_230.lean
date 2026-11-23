import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_230_aux

open PEqualNP.MetaComplexity

def maj : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def tau0 : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ := fun x y =>
  if x 0 = true ∧ y 0 = false then 0 else if x 1 = true ∧ y 1 = false then 1 else 2

theorem tau0_typing : IsTyping 3 maj tau0 := by
  unfold IsTyping
  decide

theorem rank_ge_one {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℚ) (a : m) (c : n)
    (h : M a c ≠ 0) : 1 ≤ M.rank := by
  have hd : (M.submatrix (fun _ : Fin 1 => a) (fun _ : Fin 1 => c)).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    simpa using h
  have h1 := Matrix.rank_of_det_ne_zero hd
  have h2 := Matrix.rank_submatrix_le M (fun _ : Fin 1 => a) (fun _ : Fin 1 => c)
  simp only [Fintype.card_fin] at h1
  omega

theorem minor_zero {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℚ) (hM : M.rank ≤ 1)
    (a b : m) (c d : n) : M a c * M b d = M a d * M b c := by
  by_contra h
  have hdet : (M.submatrix ![a, b] ![c, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    intro h'
    apply h
    linarith
  have h1 := Matrix.rank_of_det_ne_zero hdet
  have h2 := Matrix.rank_submatrix_le M ![a, b] ![c, d]
  simp only [Fintype.card_fin] at h1
  omega

theorem rank_two {X : Type*} [Fintype X] (M : Matrix X X ℚ) (u₁ u₂ v₁ v₂ : X → ℚ)
    (h : ∀ x y, M x y = u₁ x * v₁ y + u₂ x * v₂ y) : M.rank ≤ 2 := by
  have hM : M = (Matrix.of fun x (k : Fin 2) => ![u₁ x, u₂ x] k) *
      Matrix.of fun (k : Fin 2) y => ![v₁ y, v₂ y] k := by
    ext x y
    simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  rw [hM]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (Matrix.of fun x (k : Fin 2) => ![u₁ x, u₂ x] k)

theorem ind_one (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (h : P ↔ Q ∧ R) :
    (if P then (1 : ℚ) else 0) = (if Q then 1 else 0) * (if R then 1 else 0) := by
  by_cases hq : Q <;> by_cases hr : R <;> simp_all

theorem ind_two (P Q R S T : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    [Decidable T] (h : P ↔ (Q ∧ R) ∨ (S ∧ T)) (hx : ¬ ((Q ∧ R) ∧ (S ∧ T))) :
    (if P then (1 : ℚ) else 0) =
      (if Q then 1 else 0) * (if R then 1 else 0) + (if S then 1 else 0) * (if T then 1 else 0) := by
  by_cases hq : Q <;> by_cases hr : R <;> by_cases hs : S <;> by_cases ht : T <;> simp_all

theorem upper : HasTypedRank 3 maj 5 := by
  refine ⟨tau0, tau0_typing, ?_⟩
  have hz : ∀ (i : Fin 3) (x y : Fin 3 → Bool),
      ¬ (maj x = true ∧ maj y = false ∧ tau0 x y = (i : ℕ) ∧ x i = false) := by
    decide
  have z : ∀ i : Fin 3, typedMatrix 3 maj tau0 i false = 0 := by
    intro i
    ext x y
    simp only [typedMatrix, Matrix.zero_apply]
    rw [if_neg (hz i x y)]
  have k0 : ∀ x y : Fin 3 → Bool,
      (maj x = true ∧ maj y = false ∧ tau0 x y = ((0 : Fin 3) : ℕ) ∧ x 0 = true) ↔
        (maj x = true ∧ x 0 = true) ∧ (maj y = false ∧ y 0 = false) := by
    decide
  have k1 : ∀ x y : Fin 3 → Bool,
      (maj x = true ∧ maj y = false ∧ tau0 x y = ((1 : Fin 3) : ℕ) ∧ x 1 = true) ↔
        ((maj x = true ∧ x 0 = false) ∧ (maj y = false ∧ y 1 = false)) ∨
        ((x 0 = true ∧ x 1 = true) ∧ (y 0 = true ∧ y 1 = false ∧ y 2 = false)) := by
    decide
  have x1 : ∀ x y : Fin 3 → Bool,
      ¬ (((maj x = true ∧ x 0 = false) ∧ (maj y = false ∧ y 1 = false)) ∧
        ((x 0 = true ∧ x 1 = true) ∧ (y 0 = true ∧ y 1 = false ∧ y 2 = false))) := by
    decide
  have k2 : ∀ x y : Fin 3 → Bool,
      (maj x = true ∧ maj y = false ∧ tau0 x y = ((2 : Fin 3) : ℕ) ∧ x 2 = true) ↔
        ((maj x = true ∧ x 0 = false) ∧ (y 0 = false ∧ y 1 = true ∧ y 2 = false)) ∨
        ((x 0 = true ∧ x 1 = false ∧ x 2 = true) ∧ (y 0 = true ∧ y 1 = false ∧ y 2 = false)) := by
    decide
  have x2 : ∀ x y : Fin 3 → Bool,
      ¬ (((maj x = true ∧ x 0 = false) ∧ (y 0 = false ∧ y 1 = true ∧ y 2 = false)) ∧
        ((x 0 = true ∧ x 1 = false ∧ x 2 = true) ∧ (y 0 = true ∧ y 1 = false ∧ y 2 = false))) := by
    decide
  have r0 : (typedMatrix 3 maj tau0 0 true).rank ≤ 1 := by
    have hM : typedMatrix 3 maj tau0 0 true = Matrix.vecMulVec
        (fun x => if maj x = true ∧ x 0 = true then (1 : ℚ) else 0)
        (fun y => if maj y = false ∧ y 0 = false then (1 : ℚ) else 0) := by
      ext x y
      simp only [typedMatrix, Matrix.vecMulVec_apply]
      exact ind_one _ _ _ (k0 x y)
    rw [hM]
    exact Matrix.rank_vecMulVec_le _ _
  have r1 : (typedMatrix 3 maj tau0 1 true).rank ≤ 2 := by
    refine rank_two _ (fun x => if maj x = true ∧ x 0 = false then (1 : ℚ) else 0)
      (fun x => if x 0 = true ∧ x 1 = true then (1 : ℚ) else 0)
      (fun y => if maj y = false ∧ y 1 = false then (1 : ℚ) else 0)
      (fun y => if y 0 = true ∧ y 1 = false ∧ y 2 = false then (1 : ℚ) else 0) ?_
    intro x y
    simp only [typedMatrix]
    exact ind_two _ _ _ _ _ (k1 x y) (x1 x y)
  have r2 : (typedMatrix 3 maj tau0 2 true).rank ≤ 2 := by
    refine rank_two _ (fun x => if maj x = true ∧ x 0 = false then (1 : ℚ) else 0)
      (fun x => if x 0 = true ∧ x 1 = false ∧ x 2 = true then (1 : ℚ) else 0)
      (fun y => if y 0 = false ∧ y 1 = true ∧ y 2 = false then (1 : ℚ) else 0)
      (fun y => if y 0 = true ∧ y 1 = false ∧ y 2 = false then (1 : ℚ) else 0) ?_
    intro x y
    simp only [typedMatrix]
    exact ind_two _ _ _ _ _ (k2 x y) (x2 x y)
  simp only [Fin.sum_univ_three, Fintype.sum_bool, z, Matrix.rank_zero]
  omega

theorem forced (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 maj τ)
    (x y : Fin 3 → Bool) (i : Fin 3) (hx : maj x = true) (hy : maj y = false)
    (hd : ∀ j : Fin 3, x j ≠ y j → j = i) : τ x y = (i : ℕ) := by
  obtain ⟨j, hj, hne⟩ := hτ x y hx hy
  rw [hj, hd j hne]

theorem entry_one (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (m : Fin 3) (x y : Fin 3 → Bool)
    (hx : maj x = true) (hy : maj y = false) (ht : τ x y = (m : ℕ)) (hm : x m = true) :
    typedMatrix 3 maj τ m true x y = 1 := by
  simp only [typedMatrix]
  rw [if_pos ⟨hx, hy, ht, hm⟩]

theorem entry_tau (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (m : Fin 3) (x y : Fin 3 → Bool)
    (h : typedMatrix 3 maj τ m true x y ≠ 0) : τ x y = (m : ℕ) := by
  simp only [typedMatrix] at h
  by_cases hc : maj x = true ∧ maj y = false ∧ τ x y = (m : ℕ) ∧ x m = true
  · exact hc.2.2.1
  · rw [if_neg hc] at h
    exact absurd rfl h

theorem diag_of_rank_le_one (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (m : Fin 3)
    (hr : (typedMatrix 3 maj τ m true).rank ≤ 1) (a a' c c' : Fin 3 → Bool)
    (h1 : typedMatrix 3 maj τ m true a c = 1) (h2 : typedMatrix 3 maj τ m true a' c' = 1) :
    τ a c' = (m : ℕ) ∧ τ a' c = (m : ℕ) := by
  have h := minor_zero _ hr a a' c c'
  rw [h1, h2, one_mul] at h
  constructor
  · apply entry_tau
    intro h0
    rw [h0, zero_mul] at h
    exact one_ne_zero h
  · apply entry_tau
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h

theorem lower (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 maj τ) :
    5 ≤ ∑ i : Fin 3, ∑ b : Bool, (typedMatrix 3 maj τ i b).rank := by
  have e0a : typedMatrix 3 maj τ 0 true ![true, false, true] ![false, false, true] = 1 :=
    entry_one τ 0 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 0 (by decide) (by decide) (by decide)) (by decide)
  have e0b : typedMatrix 3 maj τ 0 true ![true, true, false] ![false, true, false] = 1 :=
    entry_one τ 0 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 0 (by decide) (by decide) (by decide)) (by decide)
  have e1a : typedMatrix 3 maj τ 1 true ![false, true, true] ![false, false, true] = 1 :=
    entry_one τ 1 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 1 (by decide) (by decide) (by decide)) (by decide)
  have e1b : typedMatrix 3 maj τ 1 true ![true, true, false] ![true, false, false] = 1 :=
    entry_one τ 1 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 1 (by decide) (by decide) (by decide)) (by decide)
  have e2a : typedMatrix 3 maj τ 2 true ![false, true, true] ![false, true, false] = 1 :=
    entry_one τ 2 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 2 (by decide) (by decide) (by decide)) (by decide)
  have e2b : typedMatrix 3 maj τ 2 true ![true, false, true] ![true, false, false] = 1 :=
    entry_one τ 2 _ _ (by decide) (by decide)
      (forced τ hτ _ _ 2 (by decide) (by decide) (by decide)) (by decide)
  have g0 : 1 ≤ (typedMatrix 3 maj τ 0 true).rank :=
    rank_ge_one _ _ _ (by rw [e0a]; exact one_ne_zero)
  have g1 : 1 ≤ (typedMatrix 3 maj τ 1 true).rank :=
    rank_ge_one _ _ _ (by rw [e1a]; exact one_ne_zero)
  have g2 : 1 ≤ (typedMatrix 3 maj τ 2 true).rank :=
    rank_ge_one _ _ _ (by rw [e2a]; exact one_ne_zero)
  have c01 : ¬ ((typedMatrix 3 maj τ 0 true).rank ≤ 1 ∧ (typedMatrix 3 maj τ 1 true).rank ≤ 1) := by
    rintro ⟨h0, h1⟩
    have a := (diag_of_rank_le_one τ 0 h0 _ _ _ _ e0a e0b).2
    have b := (diag_of_rank_le_one τ 1 h1 _ _ _ _ e1a e1b).2
    exact absurd (a.symm.trans b) (by decide)
  have c02 : ¬ ((typedMatrix 3 maj τ 0 true).rank ≤ 1 ∧ (typedMatrix 3 maj τ 2 true).rank ≤ 1) := by
    rintro ⟨h0, h2⟩
    have a := (diag_of_rank_le_one τ 0 h0 _ _ _ _ e0a e0b).1
    have b := (diag_of_rank_le_one τ 2 h2 _ _ _ _ e2a e2b).2
    exact absurd (a.symm.trans b) (by decide)
  have c12 : ¬ ((typedMatrix 3 maj τ 1 true).rank ≤ 1 ∧ (typedMatrix 3 maj τ 2 true).rank ≤ 1) := by
    rintro ⟨h1, h2⟩
    have a := (diag_of_rank_le_one τ 1 h1 _ _ _ _ e1a e1b).1
    have b := (diag_of_rank_le_one τ 2 h2 _ _ _ _ e2a e2b).1
    exact absurd (a.symm.trans b) (by decide)
  simp only [Fin.sum_univ_three, Fintype.sum_bool]
  omega

end PEqualNP.Outside.L_meta_230_aux

theorem PEqualNP.Outside.L_meta_230 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 5 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨PEqualNP.Outside.L_meta_230_aux.upper, ?_⟩
  rintro ⟨τ, hτ, hs⟩
  have h := PEqualNP.Outside.L_meta_230_aux.lower τ hτ
  exact absurd (le_trans h hs) (by norm_num)
