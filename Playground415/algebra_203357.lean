import Mathlib

lemma lemma0 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a n > 0 := by
  intro n hn
  induction' n with n ihn
  · exfalso; exact lt_irrefl 0 hn
  induction' n with n ihn
  · simp; rw [h₁]; norm_num
  induction' n with n ihn
  · simp; rw [h₂]; norm_num
  rw [add_assoc, (show 1 + 1 = 2 by norm_num), h₃]
  apply Nat.add_pos_right
  apply ihn
  apply Nat.succ_pos
  apply Nat.succ_pos

lemma lemma1 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a n < a (n + 1) := by
  intro n hn
  induction' n with n ihn
  · exfalso; exact lt_irrefl 0 hn
  induction' n with n ihn
  · simp; rw [h₁, h₂]; norm_num
  rw [add_assoc (n + 1), (show 1 + 1 = 2 by norm_num), h₃ (n + 1)]
  apply lt_add_of_pos_left
  apply lemma0 h₁ h₂ h₃
  apply Nat.succ_pos
  apply Nat.succ_pos

lemma lemma2 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a (n+2) < 2 * (a (n+1)) := by
  intro n hn
  induction' n with n ihn
  · exfalso; contradiction
  induction' n with n ihn
  · simp; rw [h₃, h₁, h₂]; simp; norm_num
  rw [h₃, add_assoc, (show 2 + 1 = 3 by norm_num), two_mul]
  apply add_lt_add_right
  apply lemma1 h₁ h₂ h₃
  apply Nat.add_pos_right n (Nat.succ_pos 1)
  apply Nat.add_pos_right n (Nat.succ_pos 1)

lemma lemma3 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, Int.fract ((a (n + 2) : ℚ) / (a (n + 1))) = (a n : ℚ) / (a (n + 1)) := by
  have h1 {n : ℕ} (h : n > 0) : (a n : ℚ) / (a (n + 1)) = (a (n + 2) : ℚ) / (a (n + 1)) - 1 := by
    rw [h₃]; simp; rw [add_div, div_self, add_sub_cancel_right]
    norm_cast; apply ne_of_gt; apply lemma0 h₁ h₂ h₃ (n + 1) (Nat.succ_pos n); apply h
  intro n hn
  rw [h1 hn]
  unfold Int.fract
  rw [sub_eq_sub_iff_add_eq_add, add_left_cancel_iff, eq_comm]
  norm_cast
  apply Nat.div_eq_of_lt_le
  · rw [one_mul]; apply le_of_lt; apply lemma1 h₁ h₂ h₃ (n + 1) (Nat.succ_pos n)
  simp; apply lemma2 h₁ h₂ h₃ n hn

lemma lemma4 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) (n : ℕ) :
  ∏ i in Finset.Icc 1 n, Int.fract (((a (i + 2) : ℚ))/(a (i + 1))) = (a 1 : ℚ) / (a (n + 1)) := by
  induction' n with n ihn
  · simp; rw [div_self]; norm_cast; apply ne_of_gt; apply lemma0 h₁ h₂ h₃ 1 (Nat.succ_pos 0)
  rw [Finset.prod_Icc_succ_top (by norm_num)]
  rw [ihn, lemma3 h₁ h₂ h₃ (n+1) (Nat.succ_pos n)]
  rw [mul_div, div_mul_cancel₀]
  apply ne_of_gt
  norm_cast
  apply lemma0 h₁ h₂ h₃ (n+1) (Nat.succ_pos n)

lemma lemma6 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, Odd (a (3 * n)) ∧ Odd (a (3 * n + 1)) ∧ Even (a (3 * n + 2)) := by
  have h3 : a 3 = 3 := by rw [h₃, h₁, h₂]; norm_num
  have h4 : a 4 = 5 := by rw [h₃, h₂, h3]; norm_num
  have h5 : a 5 = 8 := by rw [h₃, h3, h4]; norm_num
  intro n hn
  induction' n with n ihn
  · exfalso; contradiction
  induction' n with n ihn
  · simp; rw [h3, h4, h5]
    constructor
    · use 1; norm_num
    constructor
    · use 2; norm_num
    · use 4
  have ⟨ha, hb, hc⟩ := ihn (Nat.succ_pos n)
  have hd : Odd (a (3 * (n + 1 + 1))) := by
    rw [mul_add, mul_one, (show 3 = 1 + 2 by norm_num), ← add_assoc, h₃, add_assoc ((1 + 2) * (n + 1))]
    simp
    obtain ⟨nb, hnb⟩ := hb
    obtain ⟨nc, hnc⟩ := hc
    use (nb + nc)
    rw [hnb, hnc, ← two_mul, add_right_comm, mul_add]
    apply Nat.succ_pos ((1 + 2) * (n + 1))
  have he : Odd (a (3 * (n + 1 + 1) + 1)) := by
    rw [mul_add, mul_one, add_assoc, (show 3 + 1 = 2 + 2 by norm_num), ← add_assoc, h₃]
    obtain ⟨nc , hnc⟩ := hc
    obtain ⟨nd, hnd⟩ := hd
    use (nc + nd)
    rw [hnc, add_assoc (3*(n+1)), (show 2 + 1 = 3 * 1 by norm_num), ← mul_add, hnd, ← two_mul, ← add_assoc, mul_add]
    apply Nat.add_pos_right
    apply Nat.succ_pos 1
  have hf : Even (a (3 * (n + 1 + 1) + 2)) := by
    rw [mul_add, mul_one, h₃, ← mul_add_one]
    obtain ⟨nd, hnd⟩ := hd
    obtain ⟨ne, hne⟩ := he
    use (nd + ne + 1)
    rw [hnd, hne, two_mul, two_mul, add_assoc, add_comm 1, ← add_assoc, ← add_assoc, ← add_assoc, add_assoc nd, add_comm nd, add_assoc (nd + ne), add_assoc (nd + ne), add_assoc (nd + ne), add_comm _ 1, ← add_assoc]
    apply Nat.add_pos_right
    apply Nat.succ_pos 2
  exact ⟨hd, he, hf⟩

theorem algebra_203357 {a : ℕ → ℕ}
  (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  (Nat.floor ((a 2 : ℚ) / (a 1)))
  * (∏ i in Finset.Icc 1 97, Int.fract (((a (i + 2) : ℚ))/(a (i + 1))))
  * Nat.floor ((a 98 : ℚ) / (a 2)) = 1 := by
  rw [lemma4 h₁ h₂ h₃, h₁, h₂]
  simp
  have ⟨n, _, _, hn⟩ := lemma6 h₁ h₂ h₃ 32 (Nat.succ_pos 31)
  simp at hn
  rw [hn, ← Nat.mul_two]
  norm_cast
  rw [Nat.mul_div_cancel]
  simp
  rw [inv_mul_cancel₀]
  norm_cast
  intro h1
  have h2 := lemma0 h₁ h₂ h₃ 98 (Nat.succ_pos 97)
  rw [hn, h1, add_zero] at h2
  apply lt_irrefl 0 h2
  apply Nat.succ_pos 1
