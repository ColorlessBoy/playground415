import Mathlib

-- Lemma 0: Show that a(n) > 0 for all n > 0, given recurrence relation and base cases
lemma lemma0 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a n > 0 := by
  intro n hn
  induction' n with n ihn
  -- Base case n = 0, contradicts n > 0
  · exfalso; exact lt_irrefl 0 hn
  induction' n with n ihn
  -- n = 1, use a 1 = 1
  · simp; rw [h₁]; norm_num
  induction' n with n ihn
  -- n = 2, use a 2 = 2
  · simp; rw [h₂]; norm_num
  -- For n ≥ 3, use recurrence and induction
  rw [add_assoc, (show 1 + 1 = 2 by norm_num), h₃]
  apply Nat.add_pos_right
  apply ihn
  apply Nat.succ_pos
  apply Nat.succ_pos

-- Lemma 1: Show that a(n) < a(n+1) for all n > 0 (i.e., the sequence is strictly increasing)
lemma lemma1 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a n < a (n + 1) := by
  intro n hn
  induction' n with n ihn
  -- n = 0, contradiction
  · exfalso; exact lt_irrefl 0 hn
  induction' n with n ihn
  -- n = 1, compare a 1 and a 2
  · simp; rw [h₁, h₂]; norm_num
  -- For n ≥ 2, use recurrence and lemma0
  rw [add_assoc (n + 1), (show 1 + 1 = 2 by norm_num), h₃ (n + 1)]
  apply lt_add_of_pos_left
  apply lemma0 h₁ h₂ h₃
  apply Nat.succ_pos
  apply Nat.succ_pos

-- Lemma 2: Show a(n+2) < 2 * a(n+1), an upper bound on growth
lemma lemma2 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, a (n+2) < 2 * (a (n+1)) := by
  intro n hn
  induction' n with n ihn
  -- n = 0, contradiction
  · exfalso; contradiction
  induction' n with n ihn
  -- n = 1, use recurrence and base cases
  · simp; rw [h₃, h₁, h₂]; simp; norm_num
  -- For n ≥ 2, apply recurrence and lemma1
  rw [h₃, add_assoc, (show 2 + 1 = 3 by norm_num), two_mul]
  apply add_lt_add_right
  apply lemma1 h₁ h₂ h₃
  apply Nat.add_pos_right n (Nat.succ_pos 1)
  apply Nat.add_pos_right n (Nat.succ_pos 1)

-- Lemma 3: Show the fractional part of a(n+2)/a(n+1) equals a(n)/a(n+1)
lemma lemma3 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, Int.fract ((a (n + 2) : ℚ) / (a (n + 1))) = (a n : ℚ) / (a (n + 1)) := by
  -- Helper: convert recurrence into a(n+2)/a(n+1) = a(n)/a(n+1) + 1
  have h1 {n : ℕ} (h : n > 0) : (a n : ℚ) / (a (n + 1)) = (a (n + 2) : ℚ) / (a (n + 1)) - 1 := by
    rw [h₃]; simp; rw [add_div, div_self, add_sub_cancel_right]
    norm_cast; apply ne_of_gt; apply lemma0 h₁ h₂ h₃ (n + 1) (Nat.succ_pos n); apply h
  intro n hn
  -- Use the helper to simplify the fractional part
  rw [h1 hn]
  unfold Int.fract
  rw [sub_eq_sub_iff_add_eq_add, add_left_cancel_iff, eq_comm]
  norm_cast
  -- Prove a(n+2)/a(n+1) lies in (1,2), so its floor is 1
  apply Nat.div_eq_of_lt_le
  · rw [one_mul]; apply le_of_lt; apply lemma1 h₁ h₂ h₃ (n + 1) (Nat.succ_pos n)
  simp; apply lemma2 h₁ h₂ h₃ n hn

-- Lemma 4: The product of the fractional parts of aₙ₊₂ / aₙ₊₁ from i = 1 to n
-- equals a₁ / aₙ₊₁, assuming the sequence follows Fibonacci-like recurrence.
lemma lemma4 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) (n : ℕ) :
  ∏ i in Finset.Icc 1 n, Int.fract (((a (i + 2) : ℚ))/(a (i + 1))) = (a 1 : ℚ) / (a (n + 1)) := by
  induction' n with n ihn
  -- Base case: when n = 0, the product is 1, and a₁ / a₁ = 1
  · simp; rw [div_self]; norm_cast; apply ne_of_gt; apply lemma0 h₁ h₂ h₃ 1 (Nat.succ_pos 0)
  -- Inductive step: split off the last term and apply inductive hypothesis
  rw [Finset.prod_Icc_succ_top (by norm_num)]
  rw [ihn, lemma3 h₁ h₂ h₃ (n+1) (Nat.succ_pos n)]
  -- Simplify using algebraic manipulation
  rw [mul_div, div_mul_cancel₀]
  -- Show denominator ≠ 0 using positivity of Fibonacci-like sequence
  apply ne_of_gt
  norm_cast
  apply lemma0 h₁ h₂ h₃ (n+1) (Nat.succ_pos n)

-- Lemma 6: Parity pattern of the sequence a(n), which follows Fibonacci recurrence with a₁ = 1, a₂ = 2.
-- Shows: a(3n) and a(3n+1) are odd, a(3n+2) is even, for all n > 0.
lemma lemma6 {a : ℕ → ℕ} (h₁ : a 1 = 1) (h₂ : a 2 = 2)
  (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  ∀ n > 0, Odd (a (3 * n)) ∧ Odd (a (3 * n + 1)) ∧ Even (a (3 * n + 2)) := by
  -- Compute initial values for pattern base case
  have h3 : a 3 = 3 := by rw [h₃, h₁, h₂]; norm_num
  have h4 : a 4 = 5 := by rw [h₃, h₂, h3]; norm_num
  have h5 : a 5 = 8 := by rw [h₃, h3, h4]; norm_num
  intro n hn
  induction' n with n ihn
  · exfalso; contradiction -- n = 0 contradicts n > 0
  induction' n with n ihn
  -- Base case: n = 1, show directly using computed values
  · simp; rw [h3, h4, h5]
    constructor
    · use 1; norm_num
    constructor
    · use 2; norm_num
    · use 4
  -- Inductive step: assume property for n, prove for n+1
  have ⟨ha, hb, hc⟩ := ihn (Nat.succ_pos n)

  -- Prove a(3(n+2)) is odd using recurrence and parity of previous terms
  have hd : Odd (a (3 * (n + 1 + 1))) := by
    rw [mul_add, mul_one, (show 3 = 1 + 2 by norm_num), ← add_assoc, h₃, add_assoc ((1 + 2) * (n + 1))]
    simp
    obtain ⟨nb, hnb⟩ := hb
    obtain ⟨nc, hnc⟩ := hc
    use (nb + nc)
    rw [hnb, hnc, ← two_mul, add_right_comm, mul_add]
    apply Nat.succ_pos ((1 + 2) * (n + 1))

  -- Prove a(3(n+2)+1) is odd
  have he : Odd (a (3 * (n + 1 + 1) + 1)) := by
    rw [mul_add, mul_one, add_assoc, (show 3 + 1 = 2 + 2 by norm_num), ← add_assoc, h₃]
    obtain ⟨nc , hnc⟩ := hc
    obtain ⟨nd, hnd⟩ := hd
    use (nc + nd)
    rw [hnc, add_assoc (3*(n+1)), (show 2 + 1 = 3 * 1 by norm_num), ← mul_add, hnd, ← two_mul, ← add_assoc, mul_add]
    apply Nat.add_pos_right
    apply Nat.succ_pos 1

  -- Prove a(3(n+2)+2) is even
  have hf : Even (a (3 * (n + 1 + 1) + 2)) := by
    rw [mul_add, mul_one, h₃, ← mul_add_one]
    obtain ⟨nd, hnd⟩ := hd
    obtain ⟨ne, hne⟩ := he
    use (nd + ne + 1)
    rw [hnd, hne, two_mul, two_mul, add_assoc, add_comm 1, ← add_assoc, ← add_assoc, ← add_assoc,
        add_assoc nd, add_comm nd, add_assoc (nd + ne), add_assoc (nd + ne), add_assoc (nd + ne),
        add_comm _ 1, ← add_assoc]
    apply Nat.add_pos_right
    apply Nat.succ_pos 2

  -- Conclude the inductive step
  exact ⟨hd, he, hf⟩

theorem algebra_203357 {a : ℕ → ℕ}
  (h₁ : a 1 = 1) (h₂ : a 2 = 2) (h₃ : ∀ n > 0, a (n + 2) = a n + a (n + 1)) :
  -- The product of the floor of a₂ / a₁, the product of fractional parts from i=1 to 97,
  -- and the floor of a₉₈ / a₂ equals 1.
  (Nat.floor ((a 2 : ℚ) / (a 1)))
  * (∏ i in Finset.Icc 1 97, Int.fract (((a (i + 2) : ℚ))/(a (i + 1))))
  * Nat.floor ((a 98 : ℚ) / (a 2)) = 1 := by

  -- Apply lemma4 to rewrite the product of fractional parts
  rw [lemma4 h₁ h₂ h₃, h₁, h₂]
  simp

  -- Use lemma6 to extract parity properties for n=32, which helps simplify floor values
  have ⟨n, _, _, hn⟩ := lemma6 h₁ h₂ h₃ 32 (Nat.succ_pos 31)
  simp at hn

  -- Rewrite hn to isolate terms and convert to a multiple of two
  rw [hn, ← Nat.mul_two]
  norm_cast

  -- Simplify using Nat.mul_div_cancel since denominator divides numerator
  rw [Nat.mul_div_cancel]
  simp

  -- Apply inverse multiplication cancellation for rational numbers (division and multiplication inverse)
  rw [inv_mul_cancel₀]
  norm_cast

  -- Assume for contradiction the floor term equals zero, then derive a contradiction using positivity (lemma0)
  intro h1
  have h2 := lemma0 h₁ h₂ h₃ 98 (Nat.succ_pos 97)
  rw [hn, h1, add_zero] at h2
  apply lt_irrefl 0 h2
  apply Nat.succ_pos 1
