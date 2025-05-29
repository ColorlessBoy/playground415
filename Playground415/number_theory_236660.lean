import Mathlib

/- Find all nonnegative integers $m$ such that

$$
a_{m}=\left(2^{2 m+1}\right)^{2}+1
$$

is divisible by at most two different primes.

Answer: $m=0,1,2$ are the only solutions. -/

theorem number_theory_236660 (a : ℕ → ℕ) (ha : ∀ m, a m = (2^(2*m + 1))^2 + 1) :
    {m | 0 ≤ m ∧ (a m).primeFactors.card ≤ 2} = {0, 1, 2} := by
  -- Prove that a(m) is divisible by 5 using induction
  have hmod5 (m : ℕ) : 5 ∣ (a m) := by
    rw [ha m]
    induction' m with m1 hm1
    -- Base case: a(0) = 0, divisible by 5
    · simp
    -- Inductive step: assume 5 ∣ a(m1), prove 5 ∣ a(m1 + 1)
    rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (2 * 1), ← Nat.add_assoc, Nat.pow_add, Nat.mul_pow]
    simp
    -- Use induction hypothesis: a(m1) = 5 * m2
    obtain ⟨m2, hm2⟩ := hm1

    -- Show m2 ≥ 1 to avoid degenerate subtraction
    have hm2gt1: m2 ≥ 1 := by
      by_contra h
      push_neg at h
      simp at h
      rw [h] at hm2
      simp at hm2

    -- Rewrite a(m1) using subtraction to prepare for divisibility argument
    have := Nat.eq_sub_of_add_eq hm2
    rw [this, Nat.sub_mul, Nat.one_mul, (show 16 = 15 + 1 by norm_num),
        Nat.sub_add_eq, Nat.sub_add_cancel, Nat.mul_assoc]

    -- Use divisibility of a difference: if a ≡ b mod 5, then a - b ≡ 0 mod 5
    apply Nat.dvd_sub
    · omega
    · apply Nat.dvd_mul_right
    · norm_num
    · omega
  -- Prove an algebraic identity for a(m) involving a product of conjugates
  have haeq (m : ℕ) : a m = (2^(2*m+1) + 1 + 2^(m+1)) * (2^(2*m+1) + 1 - 2^(m+1)) := by
    rw [ha m]  -- Expand a(m) using its definition
    let x := 2 ^ (2 * m + 1)
    let y := 2 ^ (m + 1)

    -- Show that y^2 = 2 * x, a key identity used in simplifying the expression
    have h1 : y ^ 2 = 2 * x := by
      rw [pow_two, ←pow_add, ← Nat.add_assoc, add_comm m, add_assoc 1, ← two_mul, add_assoc, pow_add, pow_one]

    calc
      -- Start from the expression x^2 + 1
      x ^ 2 + 1
        -- Add and subtract y^2 = 2x to complete the square
        = x ^ 2 + 2 * x + 1 - y ^ 2 := by rw [h1, add_right_comm, Nat.add_sub_cancel]
        -- Recognize the square pattern: (x + 1)^2 - y^2
        _ = (x + 1)^2 - y^2 := by ring_nf
        -- Use difference of squares: (x + 1 + y)(x + 1 - y)
        _ = (x + 1 + y) * (x + 1 - y) := by apply Nat.pow_two_sub_pow_two
  -- Prove that the two terms in the product are coprime
  have h_coprime (m : ℕ) :
    Nat.gcd (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)) (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)) = 1 := by
    -- Let a = 2^(2m + 1) + 1, and b = 2^(m + 1)
    let a := 2 ^ (2 * m + 1) + 1
    let b := 2 ^ (m + 1)

    -- Show that a - b ≤ a + b (needed to apply gcd_self_sub_right)
    have h1 : a - b ≤ a + b := by
      norm_num
      rw [Nat.add_assoc]
      apply le_self_add

    -- Use identity gcd(a + b, a - b) = gcd(a + b, 2b)
    have h2 := Nat.gcd_self_sub_right h1

    -- Prove that b ≤ a to justify simplification of a + b - b = a
    have : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) + 1 := by
      rw [two_mul m, add_right_comm, pow_add _ (m+1)]
      apply le_trans _ (le_of_lt (Nat.lt_add_one (2 ^ (m + 1) * 2 ^ m)))
      apply Nat.le_mul_of_pos_right
      apply Nat.pow_pos
      norm_num

    -- Simplify gcd(a + b, a - b) = gcd(a + b, 2b)
    rw [Nat.add_sub_sub_cancel this, ← two_mul] at h2
    rw [← h2]

    -- Prove that a + b is odd (needed because gcd(odd, even power of 2) = 1)
    have hodd : Odd (a + b) := by
      apply Odd.add_even
      · apply Even.add_odd
        apply Even.pow_of_ne_zero
        norm_num
        apply Nat.succ_ne_zero
        norm_num
      apply Even.pow_of_ne_zero
      norm_num
      apply Nat.succ_ne_zero

    -- Use the fact that gcd(odd, power of 2) = 1
    have h_coprime_pow := Nat.coprime_pow_right_iff (show 1 + (m + 1) > 0 by simp) (a + b) 2

    -- Simplify 2 * 2^(m+1) = 2^(1 + m + 1)
    have : 2 * 2 ^ (m + 1) = 2 ^ (1 + (m + 1)) := by
      nth_rw 1 [← pow_one 2]
      rw [← pow_add]

    rw [this]

    -- Finally conclude that gcd(a + b, 2^(1 + m + 1)) = 1
    apply h_coprime_pow.mpr
    exact Nat.coprime_two_right.mpr hodd
  -- Prove that the number of distinct prime factors of `a m` equals the sum of those of `a` and `b`
  have h_card_sum (m : ℕ) :
    (a m).primeFactors.card =
    (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)).primeFactors.card +
    (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)).primeFactors.card := by
    -- Let `a` and `b` be the sum and difference parts respectively
    let a := 2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)
    let b := 2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)
    -- Replace `a m` with `a * b` using the earlier established equality
    rw [haeq m]
    -- Use the fact that if `a` and `b` are coprime, then their prime factors are disjoint
    have h₁ : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
      Nat.Coprime.primeFactors_mul (h_coprime m)
    -- Convert cardinality of union into sum of cardinalities
    rw [h₁, Finset.card_union_eq_card_add_card]
    -- Justify the disjointness of the prime factor sets using coprimality
    apply Nat.Coprime.disjoint_primeFactors (h_coprime m)

  -- Prove that the left term (a = large + 2^(m+1)) has at least one prime factor
  have h_card_ge_one_left (m : ℕ) :
    1 ≤ (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)).primeFactors.card := by
    simp
    -- Rewrite the expression to show it's greater than 1 (hence nontrivial and has prime factors)
    rw [add_comm (2 ^ (2 * m + 1)), add_assoc, lt_add_iff_pos_right]
    -- Use the positivity of both terms to establish the inequality
    apply add_pos (by simp) (by simp)

  -- Prove the inequality: 2^(m+1) < 2^(2m+1), which is used to ensure a > b > 0
  have hmp1_lt (m : ℕ) (hm : m > 0) : 2 ^ (m + 1) < 2 ^ (2 * m + 1) := by
    -- Rewrite 2^(2m+1) as 2^m * 2^(m+1) to facilitate comparison
    rw [two_mul, add_assoc, pow_add _ _ (m + 1)]
    -- Compare via multiplication by a power of 2 > 1
    apply lt_mul_left
    apply pow_pos -- 2^m is positive
    norm_num
    apply Nat.one_lt_two_pow -- 2^(m+1) > 2 since m > 0
    apply Nat.ne_zero_iff_zero_lt.mpr hm
  -- Show that the second term (with -2^(m+1)) also has at least one prime factor
  have h_card_ge_one_right (m : ℕ) (hm : m > 0) :
    1 ≤ (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)).primeFactors.card := by
    -- Use the previously proven inequality
    have h : 2 ^ (m + 1) < 2 ^ (2 * m + 1) := hmp1_lt m hm
    simp
    -- Simplify and rearrange terms
    rw [add_comm (2 ^ (2 * m + 1)), Nat.add_sub_assoc, lt_add_iff_pos_right]
    simp
    · exact h
    -- Ensure the subtraction is valid
    apply le_of_lt h

  -- Combine everything to show that a(m) has at least 2 distinct prime factors when m > 0
  have h_card_gt_two (m : ℕ) (hm : m > 0) :
    2 ≤ (a m).primeFactors.card := by
    -- Use the main identity to rewrite cardinality
    rw [h_card_sum]
    -- Lower bound from left and right terms (both ≥ 1)
    have := add_le_add (h_card_ge_one_left m) (h_card_ge_one_right m hm)
    -- Conclude that total is ≥ 2
    apply le_trans _ this
    simp
  ext x
  let p := 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1)
  let q := 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1)
  have h_five : 5 ∈ p.primeFactors ∪ q.primeFactors := by
    -- Use the fact that p and q are coprime, so the prime factors of p * q
    -- are exactly the union of the prime factors of p and q
    have h₁ : (p * q).primeFactors = p.primeFactors ∪ q.primeFactors :=
      Nat.Coprime.primeFactors_mul (h_coprime x)
    -- Rewrite using the known equality p * q = a x
    rw [← h₁, ← haeq x]
    -- Reduce to proving 5 ∈ (a x).primeFactors
    simp
    -- Prove that 5 ∣ a x and a x ≠ 0, hence 5 ∈ (a x).primeFactors
    refine ⟨by norm_num, ⟨hmod5 x, ?_⟩⟩
    -- a x ≠ 0 because it's a positive odd number (or at least nonzero)
    rw [ha x]
    apply Nat.succ_ne_zero
  constructor
  -- Main Goal1: x ∈ {m | 0 ≤ m ∧ (a m).primeFactors.card ≤ 2} → x ∈ {0, 1, 2}
  · intro hx
    have hle := hx.right
    have h_lt : x < 3 → x ∈ ({0, 1, 2} : Set ℕ) := by intro hxlt3; simp; interval_cases x <;> simp
    apply h_lt
    by_contra hx_ge3
    push_neg at hx_ge3
    have : (a x).primeFactors.card > 2 := by
      by_contra h
      push_neg at h
      have h_card_eq_one : (a x).primeFactors.card = 2 := by apply Nat.le_antisymm h (h_card_gt_two x (by omega))
      have h_card_all_eq_one : p.primeFactors.card = 1 ∧ q.primeFactors.card = 1 := by
        -- Prove by contradiction: assume the negation of the statement
        by_contra h
        -- Push negation inside to get: either p or q does not have exactly one prime factor
        push_neg at h

        -- Consider the case where p has exactly one prime factor
        by_cases heq1 : p.primeFactors.card = 1
        ·
          -- Substitute heq1 and the sum formula for prime factor counts into the equality
          rw [h_card_sum, heq1] at h_card_eq_one
          -- Derive a contradiction from h and the equality using linear arithmetic
          apply h heq1
          linarith

        -- If p does not have exactly one prime factor, then p has at least one prime factor (≥1)
        have hp := h_card_ge_one_left x
        -- q also has at least one prime factor, using positivity condition on x
        have hq := h_card_ge_one_right x (by omega)

        -- Since p’s prime factors count is not 1, it must be strictly greater than 1
        have : p.primeFactors.card > 1 :=
          by apply lt_of_le_of_ne hp fun h => heq1 h.symm

        -- Hence, sum of prime factor counts of p and q is strictly greater than 2
        have h_ge_2 : p.primeFactors.card + q.primeFactors.card > 2 := by
          rw [show 2 = 1 + 1 by norm_num]
          apply Nat.add_lt_add_of_lt_of_le this hq

        -- But the sum is equal to primeFactors.card of a(m), which is assumed = 2,
        -- contradiction arises from sum being strictly greater than 2
        rw [h_card_sum] at h_card_eq_one
        apply ne_of_lt h_ge_2 h_card_eq_one.symm
      rw [Finset.mem_union] at h_five
      obtain ⟨hp, hq⟩ := h_card_all_eq_one
      have h_singleton_of_porq : p.primeFactors = ({5} : Finset ℕ) ∨ q.primeFactors = ({5} : Finset ℕ) := by
        -- Case analysis on whether 5 belongs to primeFactors of p or q
        cases h_five with
        | inl h5p =>
          -- If 5 ∈ p.primeFactors, then p.primeFactors has exactly one element (card = 1)
          rw [Finset.card_eq_one] at hp
          -- Conclude p.primeFactors = {5}
          apply Or.inl
          -- Obtain the singleton element t from p.primeFactors = {t}
          obtain ⟨t, ht⟩ := hp
          -- Substitute to rewrite membership of 5 in terms of t
          rw [ht] at h5p
          -- Simplify membership check
          simp at h5p
          -- Conclude the singleton element t equals 5
          rw [ht, Finset.singleton_inj, h5p]

        | inr h5q =>
          -- Similarly, if 5 ∈ q.primeFactors and q.primeFactors has exactly one element
          rw [Finset.card_eq_one] at hq
          -- Conclude q.primeFactors = {5}
          apply Or.inr
          -- Obtain the singleton element t from q.primeFactors = {t}
          obtain ⟨t, ht⟩ := hq
          -- Substitute to rewrite membership of 5 in terms of t
          rw [ht] at h5q
          -- Simplify membership check
          simp at h5q
          -- Conclude the singleton element t equals 5
          rw [ht, Finset.singleton_inj, h5q]

      -- Prove the identity: 5^k - 1 equals 4 times the sum of 5^i for i in [0, k)
      have h_5powp1 (k : ℕ) : 5 ^ k - 1 = 4 * ∑ i ∈ Finset.range k, 5 ^ i := by
        induction k with
        | zero =>
          -- Base case: 5^0 - 1 = 1 - 1 = 0, and the sum over empty range is 0
          simp
        | succ k ih =>
          -- Inductive step: expand sum over range k+1 and use inductive hypothesis
          rw [Finset.sum_range_succ, mul_add, ← ih, ← Nat.sub_add_comm, add_comm (5 ^ k), ← Nat.add_one_mul, pow_add, mul_comm]
          simp
          -- Confirm positivity for powers of 5
          apply Nat.pow_pos
          norm_num

      -- Show parity relation: sum of 5^i over range t mod 2 equals t mod 2
      have h_odd_pow5 (t : ℕ) : (∑ i in Finset.range t, 5 ^ i) % 2 = t % 2 := by
        -- For each exponent i in the range, 5^i is odd, so mod 2 equals 1
        have h_all_odd (x : ℕ) (hx : x ∈ Finset.range t) : 5 ^ x % 2 = 1 := by
          -- Use oddness of powers of 5
          have h : Odd (5 ^ x) := by apply Odd.pow; decide
          rw [Nat.odd_iff] at h
          exact h
        -- Sum mod 2 is the sum of 1's mod 2 over the number of terms, which is t mod 2
        rw [Finset.sum_nat_mod, Finset.sum_congr (by rfl) h_all_odd, Finset.sum_const, Finset.card_range]
        simp
      apply h_singleton_of_porq.elim

      -- hp5 : p.primeFactors = {5}
      · intro hp5
        have hqpowof5 : ∃ t, 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) = 5 ^ t := by
          -- Rewrite membership in terms of factorization support
          rw [← Nat.support_factorization] at hp5
          -- Use subset property of factorization support
          have h := subset_of_eq hp5
          -- Translate subset of support to subset of singleton sets
          rw [Finsupp.support_subset_singleton] at h
          -- Ensure p is nonzero to apply factorization lemmas
          have : p ≠ 0 := by
            unfold p
            rw [Nat.add_right_comm]
            apply Nat.succ_ne_zero
          -- Use uniqueness of prime power factorization to conclude p is a power of 5
          have h2 := Nat.eq_pow_of_factorization_eq_single this h
          use p.factorization 5

        obtain ⟨t, ht⟩ := hqpowof5

        have h0 : 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) - 1 = (2 ^ x + 1) * 2 ^ (x + 1) := by
          -- Rewrite the subtraction to factor as a product
          rw [Nat.add_right_comm, Nat.add_sub_cancel, two_mul, add_assoc, pow_add, ← Nat.add_one_mul]

        have h2 : 8 ∣ 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) - 1 := by
          rw [h0]
          -- Express x as 3 + y for some y ≥ 0 to analyze divisibility
          have : ∃ y, x = 3 + y := by
            use x - 3
            rw [Nat.add_sub_cancel' hx_ge3]
          obtain ⟨y, hy⟩ := this
          -- Factor and simplify powers to show divisibility by 8
          rw [mul_comm, hy, add_assoc, pow_add, mul_assoc]
          simp

        have h_even_of_sum : 2 ∣ ∑ i ∈ Finset.range t, 5 ^ i := by
          -- Use multiplication by 4 and divisibility to deduce 2 divides the sum
          apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by simp)
          simp
          rw [← h_5powp1, ← ht]
          exact h2

        have h_sum_mod : (∑ i in Finset.range t, 5 ^ i) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h_even_of_sum

        have h_odd_of_t := h_odd_pow5 t
        -- Use parity property of sum of powers of 5 to get condition on t
        rw [h_sum_mod] at h_odd_of_t

        have h_t_eq_2e : ∃ e, t = 2 * e := by
          -- Conclude t must be even because the sum modulo 2 is zero
          use t / 2
          apply Eq.symm
          apply Nat.mul_div_cancel'
          apply Nat.dvd_iff_mod_eq_zero.mpr h_odd_of_t.symm

        obtain ⟨e, he⟩ := h_t_eq_2e

        have he2 : (2 ^ x + 1) * 2 ^ (x + 1) = (5 ^ e - 1) * (5 ^ e + 1) := by
          -- Express the product as difference of squares of powers of 5
          rw [← h0, ht, he, mul_comm (5 ^ e - 1), ← Nat.pow_two_sub_pow_two, one_pow, mul_comm, pow_mul]

        have he4 : 4 ∣ 5 ^ e - 1 := by
          -- Show 4 divides 5^e - 1 via previous identity
          rw [h_5powp1]
          apply Nat.dvd_mul_right

        obtain ⟨f, hf⟩ := he4

        have hf2 : 5 ^ e + 1 = 2 * (2 * f + 1) := by
          -- Rewrite 5^e + 1 in terms of f for further factorization
          have := Nat.pow_pos (a := 5) (n := e) (by norm_num)
          have : 5 ^ e ≠ 0 := Nat.not_eq_zero_of_lt this
          rw [← Nat.sub_one_add_one this, hf]
          ring

        have hf3 : (2 * f + 1) ∣ (2 ^ x + 1) := by
          -- Use coprimality and divisibility lemmas to show (2f+1) divides (2^x + 1)
          apply Nat.Coprime.dvd_of_dvd_mul_right (n := 2 ^ (x + 1))
          rw [Nat.coprime_pow_right_iff]
          norm_num
          apply Nat.add_one_pos
          use 2 * (4 * f)
          rw [← hf, ← mul_assoc, mul_comm _ 2, ← hf2, he2, mul_comm]
        have ⟨k, hk⟩ := hf3
        have hf4 : k * 2 ^ (x + 1) = 8 * f := by
          -- Rewrite using previously established equalities to express k * 2^(x+1) as 8 * f
          rw [hk, hf, hf2, mul_comm (4 * f), mul_comm 2 (2 * f + 1), mul_assoc, mul_assoc,
              Nat.mul_left_cancel_iff (Nat.add_one_pos (2 * f)), ← mul_assoc 2] at he2
          exact he2

        have hf5 : k * 2 ^ (x - 1) = 2 * f := by
          -- Cancel powers of two and rearrange to isolate k * 2^(x-1)
          apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
          rw [← mul_assoc 4 2, (show 4 * 2 = 8 by norm_num), ← hf4, ← mul_assoc, mul_comm 4, mul_assoc,
              (show 4 = 2^2 by norm_num), ← pow_add, ← Nat.add_sub_assoc (show 1 < 2 by norm_num),
              add_comm, ← Nat.sub_add_comm (by omega), Nat.add_sub_assoc, (show 2 - 1 = 1 by norm_num)]
          simp
          norm_num

        rw [← hf5] at hf3

        have hf6 : k * 2 ^ (x - 1) + 1 ≤ 2 ^ x + 1 := by
          -- Use divisibility and inequalities to bound k * 2^(x-1) + 1
          apply Nat.le_of_dvd _ hf3
          simp

        have hk2 : k = 1 ∨ k = 2 := by
          -- Show k can only be 1 or 2 by ruling out other possibilities via contradiction
          have : ¬ (k = 1 ∨ k = 2) → k = 0 ∨ k ≥ 3 := by omega
          by_contra h
          apply this at h
          apply h.elim
          · intro hk0
            -- If k=0, derive contradiction from previous bounds forcing x=0, which is impossible
            rw [hk0, mul_zero] at hk
            have : x = 0 := by omega
            omega
          intro hkge2
          -- Show if k≥3, inequality contradicts the earlier established bound
          have h : k * 2 ^ (x - 1) + 1 > 2 * 2 ^ (x - 1) + 1 := by
            apply Nat.succ_lt_succ
            rw [Nat.mul_lt_mul_right]
            exact hkge2
            apply Nat.pow_pos (by norm_num)
          have := lt_of_lt_of_le h hf6
          rw [mul_comm 2, ← Nat.pow_add_one, Nat.sub_one_add_one (Nat.not_eq_zero_of_lt hx_ge3)] at this
          omega
        apply hk2.elim
        intro hk2
        rw [hk2, one_mul] at hf3
        obtain ⟨r, hr⟩ := hf3
        have hr1 : r < 2 := by
          by_contra h
          push_neg at h
          have : (2 ^ (x - 1) + 1) * r ≥ (2 ^ (x - 1) + 1) * 2 := by
            apply Nat.mul_le_mul_left
            exact h
          rw [← hr, add_mul, ← Nat.pow_add_one, one_mul, Nat.sub_one_add_one (Nat.not_eq_zero_of_lt hx_ge3)] at this
          omega
        have hr2 : r > 1 := by
          have : 2 ^ x + 1 > (2 ^ (x - 1) + 1) := by
            apply Nat.succ_lt_succ
            rw [Nat.pow_lt_pow_iff_right]
            norm_num
            apply lt_of_lt_of_le (by norm_num) hx_ge3
            norm_num
          rw [hr] at this
          nth_rw 2 [← mul_one (2 ^ (x - 1) + 1)] at this
          have hpos: (2 ^ (x - 1) + 1) > 0 := by apply Nat.add_one_pos
          have h := (Nat.mul_lt_mul_left hpos).mp this
          exact h
        omega
        intro hkeq2
        rw [hf, hf2, (show 4 = 2 * 2 by norm_num), mul_assoc 2 2 f, ← hf5, hkeq2, mul_comm 2 (2 ^ (x - 1)), ← Nat.pow_add_one, Nat.sub_one_add_one (show x ≠ 0 by apply Nat.not_eq_zero_of_lt hx_ge3)] at he2
        ring_nf at he2
        have : 2 ^ x = 0 := by omega
        have : 2 ^ x ≠ 0 := by
          apply Nat.not_eq_zero_of_lt
          apply Nat.one_le_pow
          norm_num
        omega
      -- hq5 : q.primeFactors = {5}
      · intro hq5
        have hqpowof5 : ∃ t, 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) = 5 ^ t := by
          -- Rewrite using factorization support property
          rw [← Nat.support_factorization] at hq5
          -- Extract subset equality from factorization support
          have h := subset_of_eq hq5
          -- Simplify subset condition for single prime support
          rw [Finsupp.support_subset_singleton] at h
          -- Show q ≠ 0, where q is defined as the difference of exponents
          have : q ≠ 0 := by
            unfold q
            rw [Nat.sub_add_comm]
            apply Nat.succ_ne_zero
            -- Rewrite exponent sums and use monotonicity of powers of two
            rw [two_mul, add_assoc, ← one_mul (2 ^ (x + 1)), pow_add 2 x (x+1)]
            apply Nat.mul_le_mul_right
            apply Nat.one_le_pow
            norm_num
          -- Apply uniqueness of prime factorization to conclude q is a power of 5
          have h2 := Nat.eq_pow_of_factorization_eq_single this h
          use q.factorization 5

        have hxp1_le : 2 ^ (x + 1) ≤ 2 ^ (2 * x + 1) := by
          -- Use known lemma hmp1_lt to get strict inequality and then apply le_of_lt
          apply le_of_lt (hmp1_lt x (by omega))

        obtain ⟨t, ht⟩ := hqpowof5

        have h0 : 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) - 1 = (2 ^ x - 1) * 2 ^ (x + 1) := by
          -- Rearrange the expression by commuting and factoring powers of two
          rw [Nat.sub_add_comm hxp1_le, Nat.add_sub_cancel, ← one_mul (2 ^ (x + 1)), two_mul, add_assoc, pow_add, ← Nat.mul_sub_right_distrib, one_mul]

        have h2 : 8 ∣ 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) - 1 := by
          -- Show divisibility by 8 by expressing x as 3 + y for some y ≥ 0
          rw [h0]
          have : ∃ y, x = 3 + y := by
            use x - 3
            rw [Nat.add_sub_cancel' hx_ge3]
          obtain ⟨y, hy⟩ := this
          rw [mul_comm, hy, add_assoc, pow_add, mul_assoc]
          simp

        have h_even_of_sum : 2 ∣ ∑ i ∈ Finset.range t, 5 ^ i := by
          -- Use divisibility and multiplication properties to prove sum of powers of 5 is even
          apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by simp)
          simp
          rw [← h_5powp1, ← ht]
          exact h2

        have h_odd_of_t := h_odd_pow5 t

        have h_sum_mod : (∑ i in Finset.range t, 5 ^ i) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h_even_of_sum

        -- Contradiction: sum is both even and odd mod 2, so t must be even
        rw [h_sum_mod] at h_odd_of_t

        have h_t_eq_2e : ∃ e, t = 2 * e := by
          -- Express t as an even number (2 * e)
          use t / 2
          apply Eq.symm
          apply Nat.mul_div_cancel'
          apply Nat.dvd_iff_mod_eq_zero.mpr h_odd_of_t.symm
        obtain ⟨e, he⟩ := h_t_eq_2e
        have he2 : (2 ^ x - 1) * 2 ^ (x + 1) = (5 ^ e - 1) * (5 ^ e + 1) := by
          -- Rewrite using previous equalities h0, ht, he, and factor commutativity
          -- Express the left side as difference of squares of 5^e
          rw [← h0, ht, he, mul_comm (5 ^ e - 1), ← Nat.pow_two_sub_pow_two, one_pow, mul_comm, pow_mul]

        have he4 : 4 ∣ 5 ^ e - 1 := by
          -- 4 divides (5^e - 1) because 5 ≡ 1 mod 4, so 5^e ≡ 1^e ≡ 1 mod 4
          rw [h_5powp1]; apply Nat.dvd_mul_right

        obtain ⟨f, hf⟩ := he4

        have hf2 : 5 ^ e + 1 = 2 * (2 * f + 1) := by
          -- Express 5^e + 1 as twice an odd number (2 * (odd))
          have := Nat.pow_pos (a := 5) (n := e) (by norm_num)
          have : 5 ^ e ≠ 0 := Nat.not_eq_zero_of_lt this
          rw [← Nat.sub_one_add_one this, hf]
          ring

        have hf3 : (2 * f + 1) ∣ (2 ^ x - 1) := by
          -- Since gcd(2^x+1, 2^x-1) = 1, and (5^e + 1) divides the product on the right,
          -- conclude (2*f+1) divides (2^x - 1) by divisibility in coprime factors
          apply Nat.Coprime.dvd_of_dvd_mul_right (n := 2 ^ (x + 1))
          rw [Nat.coprime_pow_right_iff]
          norm_num
          apply Nat.add_one_pos
          use 2 * (4 * f)
          rw [← hf, ← mul_assoc (2 * f + 1), mul_comm _ 2, ← hf2, he2, mul_comm]

        have ⟨k, hk⟩ := hf3

        have hf4 : k * 2 ^ (x + 1) = 8 * f := by
          -- Multiply k by 2^(x+1) and rewrite to relate to 8*f using previous equalities
          rw [hk, hf, hf2, mul_comm (4 * f), mul_comm 2 (2 * f + 1), mul_assoc, mul_assoc, Nat.mul_left_cancel_iff (Nat.add_one_pos (2 * f)), ← mul_assoc 2] at he2
          exact he2

        have hf5 : k * 2 ^ (x - 1) = 2 * f := by
          -- Cancel powers of two stepwise to simplify expression, carefully applying arithmetic lemmas
          apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
          rw [← mul_assoc 4 2, (show 4 * 2 = 8 by norm_num), ← hf4, ← mul_assoc, mul_comm 4, mul_assoc, (show 4 = 2^2 by norm_num), ← pow_add, ← Nat.add_sub_assoc (show 1 < 2 by norm_num), add_comm, ← Nat.sub_add_comm (by omega), Nat.add_sub_assoc, (show 2 - 1 = 1 by norm_num)]
          simp
          norm_num

        rw [← hf5] at hf3

        have hf6 : k * 2 ^ (x - 1) + 1 ≤ 2 ^ x - 1 := by
          -- Bound k*2^(x-1) + 1 by 2^x - 1 using divisibility and inequalities
          apply Nat.le_of_dvd _ hf3
          simp
          apply Nat.not_eq_zero_of_lt hx_ge3

        have hk2 : k = 1 := by
          -- Show k=1 by excluding k=0 and k≥2 using contradiction and inequality arguments
          have : ¬ k = 1 → k = 0 ∨ k ≥ 2 := by omega
          by_contra h
          apply this at h
          apply h.elim
          · intro hk0
            rw [hk0, mul_zero] at hk
            have : x = 0 := by omega
            omega
          intro hkge2
          have h : k * 2 ^ (x - 1) + 1 ≥ 2 * 2 ^ (x - 1) + 1 := by
            apply Nat.succ_le_succ
            apply Nat.mul_le_mul_right
            exact hkge2
          rw [mul_comm 2, ← Nat.pow_add_one, Nat.sub_one_add_one (Nat.not_eq_zero_of_lt hx_ge3)] at h
          have := le_trans h hf6
          omega

        rw [hk2, one_mul] at hf3

        obtain ⟨r, hr⟩ := hf3

        have hr1 : r < 2 := by
          -- r must be less than 2, otherwise inequality contradiction arises
          by_contra h
          push_neg at h
          have : (2 ^ (x - 1) + 1) * r ≥ (2 ^ (x - 1) + 1) * 2 := by
            apply Nat.mul_le_mul_left
            exact h
          rw [← hr, add_mul, ← Nat.pow_add_one, one_mul, Nat.sub_one_add_one (Nat.not_eq_zero_of_lt hx_ge3)] at this
          omega

        have hr2 : r > 1 := by
          -- r must be greater than 1 by comparing sizes of powers of two minus one and plus one
          have : 2 ^ x - 1 > (2 ^ (x - 1) + 1) := by
            have := Nat.mul_lt_mul_left (show 0 < 2 by norm_num) (b:=(2 ^ (x - 1) + 1)) (c:=2 ^ x - 1)
            apply this.mp
            rw [mul_add, mul_one, mul_comm, ← Nat.pow_add_one, Nat.sub_one_add_one, Nat.mul_sub, mul_one, two_mul, Nat.add_sub_assoc]
            apply Nat.add_lt_add_left
            nth_rw 1 [(show 2 = 2 ^ 2 - 2 by norm_num)]
            apply Nat.sub_lt_sub_right
            norm_num
            · rw [Nat.pow_lt_pow_iff_right]
              exact hx_ge3
              norm_num
            nth_rw 1 [← Nat.pow_one 2]
            rw [Nat.pow_le_pow_iff_right]
            apply le_trans (by norm_num) hx_ge3
            norm_num
            apply Nat.not_eq_zero_of_lt hx_ge3
          rw [hr] at this
          nth_rw 2 [← mul_one (2 ^ (x - 1) + 1)] at this
          have hpos: (2 ^ (x - 1) + 1) > 0 := by apply Nat.add_one_pos
          have h := (Nat.mul_lt_mul_left hpos).mp this
          exact h
        omega
    exact Nat.not_le.2 this hle
  -- Main Goal2: Show that for x ∈ {0, 1, 2}, x satisfies
  -- the property 0 ≤ x and the number of distinct prime factors of (a x) ≤ 2.
  intro h1
  apply h1.elim
  · intro hx0
    -- Case x = 0: prove 0 ≤ 0 and primeFactors(a 0) has at most 2 elements
    rw [hx0, Set.mem_setOf_eq]
    apply And.intro (le_refl 0)
    rw [ha 0]
    simp
    norm_num

  intro h2
  apply h2.elim
  · intro hx1
    -- Case x = 1: prove 0 ≤ 1 and primeFactors(a 1) has at most 2 elements
    rw [hx1, Set.mem_setOf_eq]
    apply And.intro (Nat.zero_le 1)
    rw [ha 1]
    simp
    -- Explicitly identify prime factors of a(1) = 65 as {5, 13}
    have : Nat.primeFactors 65 = {5, 13} := by native_decide
    rw [this]
    norm_num

  intro h3
  -- Case x = 2: prove 0 ≤ 2 and primeFactors(a 2) has at most 2 elements
  rw [h3.out, Set.mem_setOf_eq]
  apply And.intro (Nat.zero_le 2)
  rw [ha 2]
  simp
  -- Explicitly identify prime factors of a(2) = 1025 as {5, 41}
  have : Nat.primeFactors 1025 = {5, 41} := by native_decide
  rw [this]
  norm_num
