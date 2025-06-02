import Mathlib

lemma number_theory_285545_mp (m n : ℤ) (h₁ : 0 < m) (_ : m < 2008) (h₃ : 0 < n) (h₄ : n < 2008)
  (h₅ : 2008^2+m^2=2007^2+n^2) : (n = 404 ∧ m = 399) ∨ (n = 188 ∧ m = 177) ∨ (n = 64 ∧ m = 9) := by
  have h1 : (n + m) * (n - m) = 4015 := by
    rw [← sq_sub_sq]
    rw [(show (4015 : ℤ) = (2008 + 2007) * (2008 - 2007) by norm_num)]
    rw [← sq_sub_sq]
    rw [sub_eq_sub_iff_add_eq_add, h₅, add_comm]
  have h2 : (n + m) > 0 := by apply add_pos h₃ h₁
  have h3 : (n - m) > 0 := by
    by_contra h
    push_neg at h
    have : ¬ (4015:ℤ) ≤ 0 := by norm_num
    apply this
    rw [← h1, mul_nonpos_iff]
    apply Or.inl
    apply And.intro _ h
    apply le_of_lt h2
  have h4 : ∃ x : ℕ, x = n + m := by
    use (n + m).toNat
    rw [Int.toNat_of_nonneg (le_of_lt h2)]
  have h5 : ∃ x : ℕ, x = n - m := by
    use (n - m).toNat
    rw [Int.toNat_of_nonneg (le_of_lt h3)]
  obtain ⟨x, hx⟩ := h4
  obtain ⟨y, hy⟩ := h5
  rw [← hx, ← hy] at h1
  norm_cast at h1
  have h4 : x ∣ 4015 := by use y; exact h1.symm
  have h5 : x ∈ (Nat.divisors 4015) := by simp; exact h4
  have h6 : Nat.divisors 4015 = ({1, 5, 11, 55, 73, 365, 803, 4015}: Finset ℕ) := by native_decide
  have h7 : (n + m) > (n - m) := by
    have := sub_lt_sub_iff_left n (b := m) (c := -m)
    rw [← sub_neg_eq_add]
    apply this.mpr
    apply neg_lt_self h₁
  have h8 : y < x := by rw [← hx, ← hy] at h7; simp at h7; exact h7
  rw [h6] at h5
  fin_cases h5
  · rw [one_mul] at h1
    rw [h1] at h8
    nlinarith
  · have hy' : y = 803 := by linarith
    rw [hy'] at h8
    nlinarith
  · have hy' : y = 365 := by linarith
    rw [hy'] at h8
    nlinarith
  · have hy' : y = 73 := by linarith
    rw [hy'] at h8
    nlinarith
  · have hy' : y = 55 := by linarith
    rw [hy'] at hy
    have hn : n = 64 := by
      have : 55 + 73 = (n - m) + (n + m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    have hm : m = 9 := by
      have : 73 - 55 = (n + m) - (n - m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    exact Or.inr (Or.inr (And.intro hn hm))
  · have hy' : y = 11 := by linarith
    rw [hy'] at hy
    have hn : n = 188 := by
      have : 11 + 365 = (n - m) + (n + m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    have hm : m = 177 := by
      have : 365 - 11 = (n + m) - (n - m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    exact Or.inr (Or.inl (And.intro hn hm))
  · have hy' : y = 5 := by linarith
    rw [hy'] at hy
    have hn : n = 404 := by
      have : 5 + 803 = (n - m) + (n + m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    have hm : m = 399 := by
      have : 803 - 5 = (n + m) - (n - m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    exact Or.inl (And.intro hn hm)
  · have hy' : y = 1 := by linarith
    rw [hy'] at hy
    have hn : n = 2008 := by
      have : 1 + 4015 = (n - m) + (n + m) := by rw [← hy, ← hx]; simp
      simp at this
      linarith
    rw [hn] at h₄
    linarith

lemma number_theory_285545_mpr (m n : ℤ) (_ : 0 < m) (_ : m < 2008) (_ : 0 < n) (_ : n < 2008)
  (h₅ : (n = 404 ∧ m = 399) ∨ (n = 188 ∧ m = 177) ∨ (n = 64 ∧ m = 9)) : 2008^2+m^2=2007^2+n^2 := by
  rcases h₅ with (⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩)
  · rw [h1, h2]; norm_num
  · rw [h1, h2]; norm_num
  · rw [h1, h2]; norm_num

theorem number_theory_285545 (m n : ℤ) (h₁ : 0 < m) (h₂ : m < 2008) (h₃ : 0 < n) (h₄ : n < 2008):
  (2008^2+m^2=2007^2+n^2) ↔ ((n = 404 ∧ m = 399) ∨ (n = 188 ∧ m = 177) ∨ (n = 64 ∧ m = 9)) := by
  constructor
  · intro h; apply number_theory_285545_mp m n h₁ h₂ h₃ h₄ h
  · intro h; apply number_theory_285545_mpr m n h₁ h₂ h₃ h₄ h
