import Mathlib

-- Lemma: gcd(m, n) > 0 if and only if m > 0 or n > 0
lemma gcd_pos_iff {m n : Nat} : 0 < Nat.gcd m n ↔ 0 < m ∨ 0 < n := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, Nat.gcd_eq_zero_iff, Decidable.not_and_iff_or_not]

-- Given positive natural numbers a and b,
-- construct coprime p and q such that p * a = q * b
lemma lemma1 (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) : ∃ p, ∃ q, p ≥ 1 ∧ q ≥ 1 ∧ p.Coprime q ∧ p * a = q * b := by
  let d := b.gcd a           -- Let d be the gcd of b and a
  let m := a / d             -- Define m = a / d
  let n := b / d             -- Define n = b / d
  use n; use m
  -- d > 0 since b ≥ 1
  have hd : d > 0 := gcd_pos_iff.mpr (Or.inl hb)
  -- a ≥ d and b ≥ d
  have hxd : a ≥ d := Nat.gcd_le_right _ ha
  have hyd : b ≥ d := Nat.gcd_le_left _ hb
  -- m and n are positive
  have hm : m > 0 := Nat.div_pos hxd (Nat.gcd_pos_of_pos_left a hb)
  have hn : n > 0 := Nat.div_pos hyd (Nat.gcd_pos_of_pos_right b ha)
  refine ⟨hn, hm, ?_, ?_⟩
  · exact Nat.coprime_div_gcd_div_gcd hd    -- m and n are coprime
  -- Show p * a = q * b
  rw [mul_comm, ← Nat.mul_div_assoc, mul_comm m, ← Nat.mul_div_assoc, mul_comm]
  apply Nat.gcd_dvd_right
  apply Nat.gcd_dvd_left

-- Lemma (to be proved): if a^m = b^n and gcd(m,n)=1, then a = c^n and b = c^m for some c
-- Common trick in number theory problems involving exponentiation and coprimality
lemma lemma2 {a b m n : ℕ} (h1 : m.Coprime n) (h2 : a^m = b^n) : ∃ c, a = c^n ∧ b = c^m := by
  sorry

-- Given a = c^m and b = c^n, prove that either b^2 = k * a or a = k * b^2 for some k
lemma lemma3 {a b c m n : ℕ} (ha : a = c^m) (hb : b = c^n) : (∃ k, b^2 = k * a) ∨ (∃ k, a = k * b^2) := by
  by_cases h : 2 * n ≤ m
  · -- Case 1: 2n ≤ m ⇒ a = k * b^2
    have h2 : ∃ k, a = k * b^2 := by
      use c ^ (m - 2 * n)  -- Let k = c^(m - 2n)
      rw [ha, hb]
      have h3 : m - 2 * n + 2 * n = m := by
        omega
      calc
        c ^ m = c ^ (m - 2 * n + 2 * n) := by rw [h3]
        _ = c ^ (m - 2 * n) * c ^ (2 * n) := by rw [pow_add]
        _ = _ := by ring
    simp [h2]
  · -- Case 2: 2n > m ⇒ b^2 = k * a
    have h4 : 2 * n > m := by
      omega
    have h2 : ∃ k, b^2 = k * a := by
      use c ^ (2 * n - m)  -- Let k = c^(2n - m)
      rw [hb, ha]
      have h3 : 2 * n - m + m = 2 * n := by
        omega
      calc
        (c ^ n) ^ 2 = c ^ (2 * n) := by ring
        _ = c ^ (2 * n - m + m) := by rw [h3]
        _ = c ^ (2 * n - m) * c ^ m := by rw [pow_add]
        _ = _ := by ring
    simp [h2]

-- Lemma 4: Proves that 2^n ≥ 1 + n for all natural numbers n.
lemma lemma4 {n : ℕ} : 2 ^ n ≥ 1 + n := by
  induction' n with n ihn
  · simp  -- Base case: 2^0 = 1 ≥ 1 + 0 = 1
  rw [pow_add, pow_one, mul_two, ← add_assoc]  -- 2^(n+1) = 2 * 2^n = 2^n + 2^n
  apply Nat.add_le_add ihn
  -- Show that 2^n ≥ n implies 2^n ≥ 1 + n by transitivity
  apply le_trans _ ihn
  apply Nat.le_add_right

-- Lemma 5: Proves that 3^n ≥ 1 + 2n for all natural numbers n.
lemma lemma5 {n : ℕ} : 3 ^ n ≥ 1 + 2 * n := by
  induction' n with n ihn
  · simp  -- Base case: 3^0 = 1 ≥ 1 + 2*0 = 1
  rw [pow_add, pow_one, mul_add, ← add_assoc, mul_one, Nat.mul_succ, add_comm]
  apply Nat.add_le_add ihn
  omega  -- Show that 2n + 2 ≤ 3^n using induction hypothesis

-- Lemma 6: Proves that the only natural number n for which n * 4 = 2^n is n = 4.
lemma lemma6 {n : ℕ} (h : n * 4 = 2 ^ n) : n = 4 := by
  -- Case 1: Try small values n < 4, check directly and rule them out
  by_cases hn : n < 4
  · have hn : n ∈ Finset.range 4 := Finset.mem_range.mpr hn
    have : n * 4 ≠ 2 ^ n := by fin_cases hn <;> simp  -- Exhaust cases n = 0,1,2,3
    exfalso; omega

  -- Case 2: If n = 4, then it's the solution
  by_cases hn : n = 4
  · exact hn

  -- Case 3: If n > 4, then prove n * 4 < 2^n and derive contradiction
  have hn : n > 4 := by omega
  have : ∃ m, n = m + 5 := by use n - 5; omega  -- Rewrite n as m + 5
  obtain ⟨m, hm⟩ := this

  -- Inductive proof: Show (m + 5) * 4 < 2^(m + 5) for all m ≥ 0
  have (m : ℕ) : (m + 5) * 4 < 2 ^ (m + 5) := by
    induction' m with m ihm
    · simp  -- Base case: 5 * 4 = 20 < 2^5 = 32
    rw [add_comm m, add_assoc, add_mul, one_mul, pow_add, pow_one, two_mul]
    apply Nat.add_lt_add _ ihm
    · omega  -- Show 4*(m+1) < 2^(m+1) for inductive step

  -- Apply inequality and contradiction
  have := this m
  rw [← hm] at this
  exfalso; omega  -- Contradiction: assumption says n * 4 = 2^n, but this shows n * 4 < 2^n

theorem number_theory_178800_mp {a b : ℕ} (ha: a ≥ 1) (hb: b ≥ 1) (hab : a ^ (b ^ 2) = b ^ a) :
  (a = 1 ∧ b = 1) ∨ (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3) := by
  -- case b = 1
  by_cases hb1 : b = 1
  · apply Or.inl
    rw [hb1, one_pow, pow_one, one_pow] at hab
    exact ⟨hab, hb1⟩
  -- Now b ≥ 2
  have hab2 : a ^ (2 * b^2) = (b ^ 2) ^ a := by
    rw [mul_comm, ← pow_mul, mul_comm 2, pow_mul, pow_mul, hab]
  have hb2 : b ≥ 2 := by omega
  by_cases ha1 : a = 1
  · rw [ha1, one_pow, pow_one] at hab
    exact False.elim (hb1 hab.symm)
  have ha2 : a ≥ 2 := by omega
  -- Now a ≥ 2 and b ≥ 2
  have ha3 : a ≠ 0 := by apply Nat.ne_of_gt ha
  have hb3 : b ≠ 0 := by apply Nat.ne_of_gt hb
  have hb2_pos : b * b > 0 := Nat.mul_pos hb hb
  have ⟨p, q, hp, hq, hpq, hpqeq⟩ := lemma1 a (b^2) ha (show b ^ 2 ≥ 1 by nlinarith)
  have hab1 : a ^ p = b ^ q := by
    have : (a ^ b ^ 2)^q = (b ^ a)^q := by rw [hab]
    rw [← pow_mul, mul_comm, ← hpqeq, pow_mul, ← pow_mul b, mul_comm, pow_mul] at this
    apply Nat.pow_left_injective ha3 this
  have ⟨c, hc1, hc2⟩:= lemma2 hpq hab1
  have hcond := lemma3 hc1 hc2
  -- (∃ k, b ^ 2 = k * a) ∨ ∃ k, a = k * b ^ 2
  apply hcond.elim
  · -- (∃ k, b ^ 2 = k * a)
    intro ⟨k, hk⟩
    rw [hk, ← mul_assoc, pow_mul] at hab2
    have hk2 := Nat.pow_left_injective ha3 hab2
    have hk3 : k * a > 0 := by
      rw [← hk]
      apply Nat.pow_pos hb
    have hk4 : k > 0 := (Nat.mul_pos_iff_of_pos_right ha).mp hk3
    have hk5 : k = a ^(2*k-1) := by
      rw [← Nat.mul_right_cancel_iff ha, ← hk2]
      nth_rw 3 [← pow_one a]
      rw [← pow_add, Nat.sub_one_add_one]
      omega
    have hk6 : 2 * k - 1 ≠ 0 := by omega
    have hk7 : a ^ (2 * k - 1) > k := by
      have : a ^ (2 * k - 1) ≥ 2 ^ (2 * k - 1) := (Nat.pow_le_pow_iff_left hk6).mpr ha2
      apply lt_of_lt_of_le _ this
      have : 2 ^ (2 * k - 1) ≥ 1 + (2 * k - 1) := by apply lemma4
      apply lt_of_lt_of_le _ this
      omega
    rw [← hk5] at hk7
    apply False.elim ((lt_irrefl k) hk7)
  -- ∃ k, a = k * b ^ 2
  intro ⟨k, hk⟩
  have hk2 : k > 0 := by
    apply Nat.pos_iff_ne_zero.mpr
    intro h
    rw [h, zero_mul] at hk
    exact ha3 hk
  have hk3 : a ^ (k * b ^ 2) = (b ^ k) ^ a := by
    rw [mul_comm, pow_mul, ← pow_mul b, mul_comm k, pow_mul, hab]
  rw [← hk] at hk3
  have hk4 := Nat.pow_left_injective ha3 hk3
  rw [hk] at hk4
  by_cases hk5 : k = 1
  · rw [hk5] at hk4
    simp at hk4
    have : b = 1 := by
      rw [← Nat.mul_right_cancel_iff hb, ← pow_two, one_mul]
      exact hk4
    apply False.elim (hb1 this)
  by_cases hk6 : k = 2
  · rw [hk6] at hk4
    exfalso
    nlinarith
  by_cases hk7 : k = 3
  · rw [hk7] at hk4
    have hb4 : b = 3 := by
      rw [← Nat.mul_right_cancel_iff hb2_pos, ← pow_three, ← pow_two, hk4]
    rw [hb4, hk7] at hk
    simp at hk
    apply Or.inr; apply Or.inr; exact ⟨hk, hb4⟩
  by_cases hk8 : k = 4
  · rw [hk8] at hk4
    have hb4 : b = 2 := by
      apply Nat.pow_left_injective (Nat.succ_ne_zero 1)
      simp
      rw [← Nat.mul_right_cancel_iff hb2_pos, ← pow_two, hk4, ← pow_add]
    rw [hk8, hb4] at hk
    simp at hk
    apply Or.inr; apply Or.inl; exact ⟨hk, hb4⟩
  have hk9 : k > 4 := by omega
  by_cases hb4 : b = 2
  · rw [hb4] at hk4
    simp at hk4
    have : k = 4 := lemma6 hk4
    apply False.elim (Nat.ne_of_gt hk9 this)
  have hb5 : b ≥ 3 := by omega
  have hk10 : k = b ^ (k - 2) := by
    rw [← Nat.mul_right_cancel_iff hb2_pos, ← pow_two, ← pow_add, hk4, Nat.sub_add_cancel]
    omega
  have hk11 : k ≥ 3 ^ (k - 2) := by
    apply le_of_le_of_eq _ hk10.symm
    apply (Nat.pow_le_pow_iff_left (show k - 2 ≠ 0 by omega)).mpr
    exact hb5
  have hk12 : 3 ^ (k - 2) > k := by
    have : 3 ^ (k - 2) ≥ 1 + 2 * (k - 2) := by apply lemma5
    apply lt_of_lt_of_le _ this
    rw [Nat.mul_sub, ← Nat.add_sub_assoc, Nat.add_comm, two_mul, add_assoc,
    Nat.add_sub_assoc, Nat.lt_add_right_iff_pos]
    omega; omega; omega
  have := lt_of_lt_of_le hk12 hk11
  apply False.elim (lt_irrefl k this)

theorem number_theory_178800_mpr {a b : ℕ} (_: a ≥ 1) (_: b ≥ 1)
  (h : (a = 1 ∧ b = 1) ∨ (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3)) : a ^ (b ^ 2) = b ^ a := by
  apply h.elim
  · intro ⟨h1, h2⟩; rw [h1, h2]; simp
  intro h
  apply h.elim
  · intro ⟨h1, h2⟩; rw [h1, h2]; simp
  intro ⟨h1, h2⟩; rw [h1, h2]; simp

theorem number_theory_178800 {a b : ℕ} (ha: a ≥ 1) (hb: b ≥ 1) :
  a ^ (b ^ 2) = b ^ a ↔ (a = 1 ∧ b = 1) ∨ (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3) := by
  exact ⟨number_theory_178800_mp ha hb,number_theory_178800_mpr ha hb⟩
