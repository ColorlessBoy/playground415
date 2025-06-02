import Mathlib

lemma number_theory_285545_mp (m n : ℤ) (h₁ : 0 < m) (_ : m < 2008) (h₃ : 0 < n) (h₄ : n < 2008)
  (h₅ : 2008^2+m^2=2007^2+n^2) : (n = 404 ∧ m = 399) ∨ (n = 188 ∧ m = 177) ∨ (n = 64 ∧ m = 9) := by
  -- Step 1: Transform the given equation into a factorized form using difference of squares
  have h1 : (n + m) * (n - m) = 4015 := by
    rw [← sq_sub_sq]
    rw [(show (4015 : ℤ) = (2008 + 2007) * (2008 - 2007) by norm_num)]
    rw [← sq_sub_sq]
    rw [sub_eq_sub_iff_add_eq_add, h₅, add_comm]
  -- Step 2: Ensure that n + m > 0 and n - m > 0 (positivity constraints)
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
  -- Step 3: Convert n + m and n - m into natural numbers
  have h4 : ∃ x : ℕ, x = n + m := by
    use (n + m).toNat
    rw [Int.toNat_of_nonneg (le_of_lt h2)]
  have h5 : ∃ x : ℕ, x = n - m := by
    use (n - m).toNat
    rw [Int.toNat_of_nonneg (le_of_lt h3)]
  -- Step 4: Eliminate existential quantifiers and plug in values
  obtain ⟨x, hx⟩ := h4
  obtain ⟨y, hy⟩ := h5
  rw [← hx, ← hy] at h1
  norm_cast at h1
  -- Step 5: x * y = 4015 ⇒ x is a divisor of 4015
  have h4 : x ∣ 4015 := by use y; exact h1.symm
  have h5 : x ∈ (Nat.divisors 4015) := by simp; exact h4
  -- Step 6: Compute all divisors of 4015
  have h6 : Nat.divisors 4015 = ({1, 5, 11, 55, 73, 365, 803, 4015}: Finset ℕ) := by native_decide
  -- Step 7: Use inequality to restrict possible values
  have h7 : (n + m) > (n - m) := by
    have := sub_lt_sub_iff_left n (b := m) (c := -m)
    rw [← sub_neg_eq_add]
    apply this.mpr
    apply neg_lt_self h₁
  -- Step 8: Try all cases for x ∈ divisors of 4015, with y < x
  have h8 : y < x := by rw [← hx, ← hy] at h7; simp at h7; exact h7
  rw [h6] at h5
  fin_cases h5
  -- Case x = 1: y = 4015, but y < x fails
  · rw [one_mul] at h1
    rw [h1] at h8
    nlinarith
  -- Case x = 5: y = 803, but y < x fails
  · have hy' : y = 803 := by linarith
    rw [hy'] at h8
    nlinarith
  -- Case x = 11: y = 365, but y < x fails
  · have hy' : y = 365 := by linarith
    rw [hy'] at h8
    nlinarith
  -- Case x = 55: y = 73, but y < x fails
  · have hy' : y = 73 := by linarith
    rw [hy'] at h8
    nlinarith
  -- Case x = 73: y = 55, (n,m) = (64, 9)
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
  -- Case x = 365: y = 11, (n,m) = (188, 177)
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
  -- Case x = 803: y = 5, (n,m) = (404, 399)
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
  -- Case x = 4015: y = 1, n = 2008, but n < 2008 fails
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
