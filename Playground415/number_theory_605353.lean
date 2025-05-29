import Mathlib

namespace number_theory_605353
-- We are proving that under certain conditions on powers of x, the floor of x is a perfect square
lemma lemma1 (n : ℕ) (hn : n = 0) (x : ℝ) (hx : 1 ≤ x)
    (h : ∀ i ∈ Finset.Icc (n + 2) (4 * n + 4), ∃ m : ℕ, 0 < m ∧ m^2 = ⌊x^i⌋) :
    ∃ p : ℕ, 0 < p ∧ p^2 = ⌊x⌋ := by

  -- Let `a` be the floor of `x`
  let a := Nat.floor x

  -- Since x ≥ 1 ≥ 0, we know x is nonnegative
  have hx_nonneg : x ≥ 0 := ((show (0:ℝ) ≤ 1 by norm_num).trans hx)

  -- The floor of x is less than or equal to x
  have ha_le : a ≤ x := Nat.floor_le hx_nonneg

  -- Then a^2 ≤ x^2
  have ha2_le : a^2 ≤ x^2 := by
    rw [sq_le_sq₀]
    exact ha_le
    norm_cast
    exact Nat.zero_le a
    exact hx_nonneg

  -- Since x ≥ 1, a ≥ 1
  have ha_ge1: a ≥ 1 := by apply Nat.le_floor; norm_cast

  -- Therefore, a > 0
  have ha_pos : 0 < a := by apply lt_of_lt_of_le (by norm_num) ha_ge1

  -- Hence, a^2 > 0
  have ha2_pos : 0 < a^2 := by apply Nat.pow_pos ha_pos

  -- We now show that ⌊x^2⌋ = a^2 using the assumption h
  have floor_x2_eq : ⌊x^2⌋ = a^2 := by
    obtain ⟨m2, hm2_pos, hm2_sq⟩ := h 2 (by simp [hn]) -- Use h for i = 2
    rw [← hm2_sq, sq_eq_sq₀ (Nat.cast_nonneg m2) (Nat.cast_nonneg a)]
    norm_cast
    rw [Eq.comm, Nat.floor_eq_iff hx_nonneg]
    constructor
    · apply (sq_le_sq₀ (Nat.cast_nonneg m2) hx_nonneg).mp
      apply le_trans _ (Int.floor_le (x ^ 2))
      rw [← hm2_sq]
      norm_cast
    -- Show strict inequality: m2^2 < x^2 + 1
    apply (sq_lt_sq₀ hx_nonneg _).mp
    · apply lt_trans (Int.lt_floor_add_one (x ^ 2))
      rw [← hm2_sq]
      norm_cast
      linarith
    apply le_trans (le_of_lt (by norm_cast)) (le_add_of_nonneg_right zero_le_one)

  -- x^2 is nonnegative
  have hx2_nonneg : x ^ 2 ≥ 0 := pow_two_nonneg x

  -- We now prove ⌊x^4⌋ = a^4
  have floor_x4_eq : ⌊x^4⌋ = a^4 := by
    obtain ⟨m4, hm4_pos, hm4_sq⟩ := h 4 (by simp [hn]) -- Use h for i = 4
    rw [← hm4_sq, (show 4 = 2 * 2 by norm_num), pow_mul,
        sq_eq_sq₀ (Nat.cast_nonneg m4) (by norm_num), ← floor_x2_eq]
    rw [Eq.comm, Int.floor_eq_iff]
    norm_cast
    constructor
    · apply (sq_le_sq₀ (Nat.cast_nonneg m4) hx2_nonneg).mp
      rw [← pow_mul, (show 2 * 2 = 4 by norm_num)]
      apply le_trans _ (Int.floor_le (x ^ 4))
      rw [← hm4_sq]
      norm_cast
    apply (sq_lt_sq₀ hx2_nonneg _).mp
    rw [← pow_mul, (show 2 * 2 = 4 by norm_num)]
    · apply lt_trans (Int.lt_floor_add_one (x ^ 4))
      rw [← hm4_sq]
      norm_cast
      linarith
    exact Nat.cast_nonneg (m4 + 1)

  -- Now show ⌊x^3⌋ = a^3
  have floor_x3_eq : ⌊x^3⌋ = a^3 := by
    rw [Int.floor_eq_iff]
    constructor
    · simp
      rw [(show 3 = 1 + 2 by norm_num), pow_add, pow_add, pow_one, pow_one]
      apply mul_le_mul ha_le ha2_le _ hx_nonneg
      apply pow_two_nonneg
    -- Prove strict upper bound using contradiction
    apply lt_of_not_ge
    by_contra h
    simp at h
    have h2: x ^ 4 ≥ (a ^ 4) + a := by
      rw [(show 4 = 1 + 3 by norm_num), pow_add, pow_one, pow_add, pow_one]
      have : a * a ^ 3 + a = a * (a ^ 3 + 1) := by rw [mul_add, mul_one]
      norm_cast
      rw [this]
      simp
      apply mul_le_mul ha_le h _ hx_nonneg
      norm_cast
      have ha3_nonneg : 0 ≤ a ^ 3 := pow_nonneg (Nat.zero_le a) 3
      linarith
    norm_cast at h2
    have h4: a ^ 4 + 1 ≤ a ^ 4 + a := by
      apply add_le_add_left ha_ge1
    have h5: x ^ 4 ≥ ↑a ^ 4 + 1 := by
      norm_cast
      apply le_trans (Nat.cast_le.mpr h4) h2
    have h6:= Int.lt_floor_add_one (x ^ 4)
    rw [floor_x4_eq] at h6
    simp at h6
    apply not_lt_of_ge h5 h6

  -- Now we know ⌊x^3⌋ = a^3, and by h there is a square root m3 of it
  have h3sq := h 3 (by simp [hn])
  obtain ⟨m3, hm3_pos, hm3_sq⟩ := h3sq
  have hm3 := Eq.trans hm3_sq floor_x3_eq
  norm_cast at hm3

  -- Since m3^2 = a^3, then a divides m3
  have h_dvd : a ∣ m3 := by
    apply (Nat.pow_dvd_pow_iff (show 2 ≠ 0 by apply (Nat.succ_ne_zero 1))).mp
    use a
    rw [hm3, pow_succ]

  -- Set p := m3 / a
  use (m3 / a)

  -- Show p > 0
  constructor
  · rw [Nat.div_pos_iff]
    apply And.intro ha_pos
    apply Nat.le_of_dvd hm3_pos h_dvd

  -- Finally, show p^2 = ⌊x⌋
  have : Int.floor x = Nat.floor x := by
    rw [← Int.floor_toNat, Int.toNat_of_nonneg]
    apply Int.floor_nonneg.mpr hx_nonneg
  rw [this]
  norm_cast
  rw [Nat.div_pow h_dvd, hm3, (show 3 = 1 + 2 by norm_num), pow_add, pow_one, Nat.mul_div_cancel a ha2_pos]
end number_theory_605353

theorem number_theory_605353 (n : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (h : ∀ i ∈ Finset.Icc (n + 2) (4 * n + 4), ∃ m : ℕ, 0 < m ∧ m^2 = ⌊x^i⌋) :
    ∃ p : ℕ, 0 < p ∧ p^2 = ⌊x⌋ := by
  -- We proceed by induction on n
  induction' n with n ih
  -- Base case: n = 0
  -- We apply lemma1 directly, which handles the base case when the interval is [2, 4]
  · exact number_theory_605353.lemma1 0 (Eq.refl 0) x hx h
  -- Inductive step: assume the statement holds for n, and prove it for n + 1
  apply ih
  -- We must show the required condition holds for the previous range [n + 2, 4n + 4]
  intro i hi
  -- Define x' = x^(n + 2), which will play the role of x in the inductive hypothesis
  let x' := x^(n + 2)
  -- Since x ≥ 1, we know x' ≥ 1
  have hx' : 1 ≤ x' := by apply one_le_pow₀ hx
  -- Case split: if i = n + 2, we handle it separately
  by_cases hi2 : n + 2 = i
  · -- ∃ m, 0 < m ∧ ↑m ^ 2 = ⌊x ^ i⌋
    rw [← hi2]
    apply number_theory_605353.lemma1 0 (Eq.refl 0) x' hx'
    -- To apply lemma1, we verify ∀ i2 ∈ [2, 4], ∃ m, m² = ⌊x' ^ i2⌋
    intro i2 hi2
    -- Note: x'^i2 = x^(i2 * (n + 2)), use power rule to rewrite
    rw [← pow_mul]
    -- Use the original assumption `h`, since i2 * (n + 2) lies in the original range
    apply h
    simp
    -- Prove that i2 * (n + 2) ∈ [n + 2, 4n + 4]
    simp at hi2
    obtain ⟨hi3, hi4⟩ := hi2
    constructor
    · nlinarith  -- Lower bound: n + 1 + 2 ≤ (n + 2) * i2
    · nlinarith  -- Upper bound: (n + 2) * i2 ≤ 4 * (n + 1) + 4
  -- Otherwise, i ≠ n + 2 and still lies in [n + 2, 4n + 4]
  apply h
  simp at hi
  simp
  constructor
  · rw [add_right_comm]
    -- Lower bound: n + 2 + 1 ≤ i
    exact lt_of_le_of_ne hi.left hi2
  -- Upper bound: i ≤ 4 * (n + 1) + 4
  apply le_trans hi.right
  norm_num
