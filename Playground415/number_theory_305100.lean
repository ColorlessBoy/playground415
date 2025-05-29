import Mathlib
open Int

-- Define the condition for a set M of integers:
-- (1) If a ≠ b and a, b ∈ M, then a + b ∈ M
-- (2) There exist a, b ∈ M such that ab < 0
namespace number_theory_305100

def cond (M : Set ℤ) : Prop :=
  (∀ a ∈ M, ∀ b ∈ M, a ≠ b → a + b ∈ M) ∧ (∃ a ∈ M, ∃ b ∈ M, a * b < 0)

-- A simple lemma: a + b = b ↔ a = 0
lemma add_eq_right {a b : Int} : a + b = b ↔ a = 0 := calc
  a + b = b ↔ a + b = 0 + b := by rw [zero_add b]
  _ ↔ a = 0 := by omega

-- Main lemma: If M satisfies the condition `cond`, then 0 ∈ M
lemma Q1 (M : Set ℤ) (hM : cond M) : 0 ∈ M := by
  -- Unpack the hypothesis into the additive closure and existence of a, b with ab < 0
  obtain ⟨hab_sum, ⟨a, ha, b, hb, hab_neg⟩⟩ := hM

  -- Case 1: a + b = 0 ⇒ then 0 ∈ M directly
  by_cases hsum : a + b = 0
  · by_cases heq : a = b
    -- If a = b, then ab < 0 implies a² < 0, contradiction unless a = 0
    · rw [heq, ← mul_two, mul_eq_zero_iff_right] at hsum
      rw [hsum] at hb
      exact hb
      norm_cast
    -- Otherwise, since a + b = 0 and a ≠ b, then 0 ∈ M by additive closure
    rw [← hsum]
    apply hab_sum a ha b hb heq

  -- Case 2: a + b ≠ 0 ⇒ use linear combination argument to force 0 ∈ M
  · by_contra h0 -- assume 0 ∉ M, derive contradiction

    -- Show that any x ∈ M must be nonzero (since 0 ∉ M)
    have hne0 {x : ℤ} (hx : x ∈ M) : x ≠ 0 := by
      intro hxeq0
      rw [hxeq0] at hx
      exact h0 hx

    -- Construct positive integers m, n such that a*m + b*n = 0
    have hmn : ∃ m > 0, ∃ n > 0, a * m + b * n = 0 := by
      by_cases hb2 : b > 0
      · use b; apply And.intro hb2
        use -a; apply And.intro (by nlinarith) (by rw [mul_comm b, neg_mul, add_neg_cancel])
      use -b; apply And.intro
      · have := hne0 hb; omega
      use a; apply And.intro (by nlinarith) (by rw [mul_comm, neg_mul, neg_add_cancel])

    -- Show a ≠ b ⇒ required for the additive closure
    have haneb : a ≠ b := by
      intro hab
      rw [hab] at hab_neg
      have := mul_self_nonneg b
      exact not_lt_of_ge this hab_neg

    -- Use additive closure to show a + b ∈ M
    have hapb : a + b ∈ M := hab_sum a ha b hb haneb

    -- Extract m, n such that a*m + b*n = 0
    obtain ⟨m, hm_pos, ⟨n, hn_pos, hmn_eq⟩⟩ := hmn

    -- Several auxiliary lemmas below for additive closure iteration

    -- Lemma: a*(p + 1) + b ≠ a if a*p + b ∈ M
    have h_cond0 {p : ℤ} (h1 : a * p + b ∈ M) : a * (p + 1) + b ≠ a := by
      intro h
      rw [mul_add, mul_one, add_assoc, add_comm a, ← add_assoc, add_eq_right] at h
      exact hne0 h1 h

    -- Lemma: use additive closure to get a*(p+2)+b from previous two terms
    have h_cond1 {p : ℤ} (h1 : a * p + b ∈ M) (h2 : a * (p + 1) + b ∈ M) : a * (p + 2) + b ∈ M := by
      have := hab_sum _ h2 _ ha (h_cond0 h1)
      rw [add_assoc, add_comm b, ← add_assoc, mul_add, mul_one, add_assoc (a * p), ← mul_two] at this
      rw [mul_add]
      exact this

    -- Lemma: a + b*(q+1) ≠ b if a + b*q ∈ M
    have h_cond2 {q : ℤ} (h1 : a + b * q ∈ M) : a + b * (q + 1) ≠ b := by
      intro h
      rw [mul_add, mul_one, ← add_assoc, add_eq_right] at h
      exact hne0 h1 h

    -- Lemma: use additive closure to get a + b*(q+2) from previous two terms
    have h_cond3 {q : ℤ} (h1 : a + b * q ∈ M) (h2 : a + b * (q + 1) ∈ M) : a + b * (q + 2) ∈ M := by
      have := hab_sum _ h2 _ hb (h_cond2 h1)
      rw [mul_add, add_assoc, mul_one, add_assoc, ← mul_two, ← mul_add] at this
      exact this

    -- Lemma: for fixed a*2, show closure over b*q terms
    have h_cond4 {q : ℤ} (h1 : a * 2 + b * q ∈ M) (h2 : a * 2 + b * (q + 1) ∈ M) : a * 2 + b * (q + 2) ∈ M := by
      rw [(show (2 : Int) = 1 + 1 by norm_num), ← add_assoc, mul_add b, mul_one, ← add_assoc]
      apply hab_sum
      simp; exact h2; exact hb
      intro h
      rw [mul_add b, ← add_assoc, mul_one, add_eq_right] at h
      simp at h
      exact hne0 h1 h

    -- Prove that a * 2 + b ∈ M using given condition h_cond1 and known elements
    have h_ind1 : a * 2 + b ∈ M := by
      rw [← zero_add (2:Int)]          -- Rewrite 2 as 0 + 2 for use with h_cond1
      apply h_cond1                    -- Apply closure property for distinct elements
      simp; exact hapb                 -- a + b ∈ M
      simp; exact hb                   -- b ∈ M

    -- Similarly, prove that a + b * 2 ∈ M using h_cond3
    have h_ind2 : a + b * 2 ∈ M := by
      rw [← zero_add (2:Int)]
      apply h_cond3
      simp; exact hapb
      simp; exact ha

    -- General induction for a * p + b ∈ M with p ∈ ℕ
    have h_ind3 {p : ℕ} : a * p + b ∈ M := by
      induction' p using Nat.strong_induction_on with p hp
      by_cases h0 : p = 0
      · rw [h0]; simp; exact hb        -- Base case: a * 0 + b = b ∈ M
      by_cases h1 : p = 1
      · rw [h1]; simp; exact hapb      -- Base case: a * 1 + b = a + b ∈ M
      -- For p ≥ 2, reduce to earlier case
      have : ∃ n, p = n + 2 := by use p - 2; omega
      obtain ⟨n, hn⟩ := this
      rw [hn]
      simp; apply h_cond1              -- Apply condition to (a * n + b) and a
      norm_cast; apply hp; omega       -- Inductive call on n
      apply hp; omega

    -- General induction for a + b * q ∈ M with q ∈ ℕ
    have h_ind4 {q : ℕ} : a + b * q ∈ M := by
      induction' q using Nat.strong_induction_on with q hq
      by_cases h0 : q = 0
      · rw [h0]; simp; exact ha
      by_cases h1 : q = 1
      · rw [h1]; simp; exact hapb
      have : ∃ n, q = n + 2 := by use q - 2; omega
      obtain ⟨n, hn⟩ := this
      rw [hn]
      simp; apply h_cond3
      norm_cast; apply hq; omega
      apply hq; omega

    -- Prove a * q ≠ 0 for q > 0, using ha ≠ 0
    have h_mul_n0 {q : ℕ} (hq : q > 0) : a * q ≠ 0 := by
      apply mul_ne_zero (hne0 ha)      -- a ≠ 0
      simp; omega                      -- q > 0 ⇒ q ≠ 0

    -- Inductive step for a * 2 + b * q ∈ M when q > 0
    have h_ind5 {q : ℕ} (hq : q > 0) : a * 2 + b * q ∈ M := by
      induction' q using Nat.strong_induction_on with q ihq
      by_cases h0 : q = 0
      · exfalso; omega                 -- Contradiction: q > 0
      by_cases h1 : q = 1
      · rw [h1, mul_two, add_assoc, add_comm]; simp;
        apply hab_sum _ hapb _ ha      -- Apply given property on sum
        nth_rw 1 [← mul_one a, ← zero_add 1]
        apply h_cond0
        rw [mul_zero, zero_add]
        exact hb
      by_cases h2 : q = 2
      · rw [h2]; simp; nth_rw 2 [mul_two]
        rw [← add_assoc]
        apply hab_sum _ h_ind1 _ hb
        intro h
        rw [add_eq_right] at h
        apply h_mul_n0 (Nat.zero_lt_succ 1)
        exact h
      -- General case for q ≥ 3
      have : ∃ n > 0, q = n + 2 := by use q - 2; omega
      obtain ⟨n, hn1, hn2⟩ := this
      rw [hn2]; simp
      apply h_cond4
      apply ihq; nlinarith
      norm_num
      apply ihq; omega
      exact hn1

    -- Full induction: a * p + b * q ∈ M for p > 0, q > 0
    have h_ind6 {p : ℕ} (hp : p > 0) {q : ℕ} (hq : q > 0) : a * p + b * q ∈ M := by
      induction' p using Nat.strong_induction_on with p ihp
      by_cases h0 : p = 0
      · exfalso; omega
      by_cases h1 : p = 1
      · rw [h1]; simp; apply h_ind4     -- Reduce to h_ind4
      by_cases h2 : p = 2
      · rw [h2]; simp; apply h_ind5 hq  -- Reduce to h_ind5
      have : ∃ n > 0, p = n + 2 := by use p - 2; omega
      obtain ⟨n, hn1, hn2⟩ := this
      rw [hn2]; simp
      -- Rewrite: (n + 2) * a = a + (n + 1) * a
      rw [(show n + (2:Int) = 1 + (n + 1) by omega), mul_add, mul_one, add_assoc, add_comm]
      apply hab_sum
      apply ihp; nlinarith; omega; exact ha
      intro h; rw [mul_add, mul_one, add_comm, ← add_assoc, add_eq_right, add_comm] at h
      have := hne0 (ihp n (by omega) hn1)
      apply this h

    -- Final general lemma: a * p + b * q ∈ M for p, q > 0, both in ℤ
    have hpq : ∀ p > 0, ∀ q > 0, a * p + b * q ∈ M := by
      intro p hp q hq
      -- Convert integer p to ℕ
      have : ∃ (x : ℕ), p = x := by
        use p.toNat
        simp [Int.ofNat_toNat, show 0 ≤ p by linarith]
      obtain ⟨x, hx1⟩ := this
      have hx2 : x > 0 := by omega
      -- Convert integer q to ℕ
      have : ∃ (y : ℕ), q = y := by
        use q.toNat
        simp [Int.ofNat_toNat, show 0 ≤ q by linarith]
      obtain ⟨y, hy1⟩ := this
      have hy2 : y > 0 := by omega
      -- Apply induction result
      rw [hx1, hy1]
      apply h_ind6 hx2 hy2
    have := hpq _ hm_pos _ hn_pos
    exact hne0 this hmn_eq

-- Lemma Q2: There exists a finite set M of integers such that:
-- (1) If a ≠ b and a, b ∈ M, then a + b ∈ M.
-- (2) There exist a, b ∈ M such that ab < 0.
lemma Q2 : ∃ M : Set ℤ, cond M ∧ Finite M := by
  -- Define the candidate set M = {0, 1, -1}
  let M : Set ℤ := {0, 1, -1}

  -- Prove that 0 ∈ M
  have h0 : 0 ∈ M := by apply Set.mem_insert
  -- Prove that 1 ∈ M
  have h1 : 1 ∈ M := by
    apply Set.mem_insert_iff.mpr
    apply Or.inr
    apply Set.mem_insert
  -- Prove that -1 ∈ M
  have h_1 : -1 ∈ M := by
    apply Set.mem_insert_iff.mpr
    apply Or.inr
    apply Set.mem_insert_iff.mpr
    apply Or.inr
    apply Set.mem_singleton

  -- Show that M satisfies the two conditions: cond M and M is finite
  refine ⟨M, ⟨?sum_cond, ?neg_exist⟩, ?finite⟩

  -- First condition: If a ≠ b and a, b ∈ M, then a + b ∈ M
  · intros a ha b hb hne
    -- Destructure the membership of a and b in M = {0, 1, -1}
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    -- Check all possible combinations of a and b
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp_all

  -- Second condition: There exist a, b ∈ M such that ab < 0
  · use 1, h1, -1, h_1  -- choose a = 1 and b = -1
    norm_num  -- verify that 1 * (-1) < 0

  -- Prove that M is a finite set
  · apply Set.toFinite

end number_theory_305100

theorem number_theory_305100 : ((M : Set ℤ) →  (hM : number_theory_305100.cond M) → 0 ∈ M) ∧ ∃ M : Set ℤ, number_theory_305100.cond M ∧ Finite M := by
  constructor
  · exact number_theory_305100.Q1
  exact number_theory_305100.Q2
