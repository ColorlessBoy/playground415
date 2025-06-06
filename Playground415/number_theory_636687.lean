import Mathlib

-- **Part 1: Show $P(n)$ is divisible by 2 for any integer $n$.**
lemma part1 {A B C : ℤ} (h₁ : 2 ∣ A + B + C): ∀ n, 2 ∣ A * n^3 + B * n^2 + C * n := by
  -- We consider two cases for the integer $n$:\
  intro n
  by_cases h : 2 ∣ n
  -- Case 1: $n$ is even.\
  -- If $n$ is even, then $n \\equiv 0 \\pmod 2$.\
  -- This implies $n^3 \\equiv 0^3 \\equiv 0 \\pmod 2$, $n^2 \\equiv 0^2 \\equiv 0 \\pmod 2$, and $n \\equiv 0 \\pmod 2$.\
  -- So, $P(n) = A n^3 + B n^2 + C n \\equiv A \\cdot 0 + B \\cdot 0 + C \\cdot 0 \\pmod 2$.\
  -- Thus, $P(n) \\equiv 0 \\pmod 2$.
  apply dvd_add
  apply dvd_add
  -- 2 ∣ A * n ^ 3
  · rw [(show 3 = 2 + 1 by norm_num), pow_add, ← mul_assoc, pow_one]
    apply (Prime.dvd_mul (by norm_num)).mpr
    apply Or.inr h
  -- 2 ∣ B * n ^ 2
  · rw [pow_two, ← mul_assoc]
    apply (Prime.dvd_mul (by norm_num)).mpr
    apply Or.inr h
  -- 2 ∣ C * n
  · apply (Prime.dvd_mul (by norm_num)).mpr
    apply Or.inr h
  -- Case 2: $n$ is odd.\
  -- If $n$ is odd, then $n \\equiv 1 \\pmod 2$.\
  -- This implies $n^3 \\equiv 1^3 \\equiv 1 \\pmod 2$, $n^2 \\equiv 1^2 \\equiv 1 \\pmod 2$, and $n \\equiv 1 \\pmod 2$.\
  -- So, $P(n) = A n^3 + B n^2 + C n \\equiv A \\cdot 1 + B \\cdot 1 + C \\cdot 1 \\pmod 2$.\
  -- $P(n) \\equiv A+B+C \\pmod 2$.\
  -- From condition (1), $A+B+C$ is an even number, so $A+B+C \\equiv 0 \\pmod 2$.\
  -- Thus, $P(n) \\equiv 0 \\pmod 2$.
  simp at h
  have h3 : n ^ 2 % 2 = 1 := by
    norm_num [pow_two, Int.mul_emod, h]
  have h4 : n ^ 3 % 2 = 1 := by
    norm_num [pow_succ, Int.mul_emod, h]
  apply Int.dvd_of_emod_eq_zero
  rw [Int.add_emod, Int.add_emod (A * n ^ 3), Int.mul_emod, Int.mul_emod B, Int.mul_emod C]
  rw [h, h3, h4]
  simp
  exact h₁
  -- In both cases ( $n$ even or $n$ odd), $P(n)$ is divisible by 2.

lemma lemma1 {A B C n : ℤ} : A*n^3 + B*n^2 + C*n = A*(n^3 - n) + B*n^2 + (A+C)*n := by
  rw [add_mul, add_assoc (A * (n ^ 3 - n)), ← add_assoc (B * n ^ 2)]
  rw [add_comm (B * n ^ 2), ← add_assoc (A * (n ^ 3 - n))]
  rw [← add_assoc (A * (n ^ 3 - n)), ← mul_add, sub_add_cancel]

lemma lemma2 {n : ℤ}: n^3 - n = (n + 1) * (n - 1) * n := by
  rw [← sq_sub_sq, one_pow, sub_mul, one_mul, pow_succ]

lemma lemma3 {n : ℤ}: (n + 1 + 1) * n * (n + 1) = 3 * n * (n + 1) + (n + 1) * (n - 1) * n := by
  ring

lemma lemma4 {n : ℤ} : 3 ∣ n^3 - n := by
  rw [lemma2]
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · -- Case 1: n % 3 = 0
    have hn : n % 3 = 0 := h
    simp [Int.dvd_iff_emod_eq_zero, Int.mul_emod, Int.add_emod, Int.sub_emod, hn]
  · -- Case 2: n % 3 = 1
    have hn : n % 3 = 1 := h
    simp [Int.dvd_iff_emod_eq_zero, Int.mul_emod, Int.add_emod, Int.sub_emod, hn]
  · -- Case 3: n % 3 = 2
    have hn : n % 3 = 2 := h
    simp [Int.dvd_iff_emod_eq_zero, Int.mul_emod, Int.add_emod, Int.sub_emod, hn]

-- **Part 2: Show $P(n)$ is divisible by 3 for any integer $n$.**
lemma part2 {A B C : ℤ} (h₂ : 3 ∣ B) (h₃ : 3 ∣ (A + C)): ∀ n, 3 ∣ A * n^3 + B * n^2 + C * n := by
  -- We can rewrite the expression $P(n)$ as follows:\
  -- $P(n) = A n^3 + B n^2 + C n$\
  -- $P(n) = A n^3 - A n + A n + B n^2 + C n$\
  -- $P(n) = A(n^3 - n) + B n^2 + (A+C)n$.
  intro n
  rw [lemma1]
  apply dvd_add
  apply dvd_add

  -- Let's analyze each term:\
  -- Term 1: $A(n^3 - n)$.\
  -- The expression $n^3 - n$ can be factored as $n(n^2-1) = n(n-1)(n+1) = (n-1)n(n+1)$.\
  -- This is the product of three consecutive integers. For any integer $n$, one of these three consecutive integers must be divisible by 3. Therefore, their product $(n-1)n(n+1)$ is always divisible by 3.\
  -- So, $n^3 - n \\equiv 0 \\pmod 3$ for any integer $n$.\
  -- Since $A$ is an integer, $A(n^3 - n)$ is divisible by 3.
  · rw [Prime.dvd_mul (by norm_num)]
    apply Or.inr lemma4

  -- Term 2: $B n^2$.\
  -- From condition (2), $B$ is divisible by 3 ($B \\equiv 0 \\pmod 3$).\
  -- Since $n$ is an integer, $n^2$ is an integer.\
  -- Therefore, $B n^2$ is divisible by 3.
  · rw [Prime.dvd_mul (by norm_num)]
    apply Or.inl h₂

  -- Term 3: $(A+C)n$.\
  -- From condition (3), $A+C$ is divisible by 3 ($A+C \\equiv 0 \\pmod 3$).\
  -- Since $n$ is an integer, $(A+C)n$ is divisible by 3.
  · rw [Prime.dvd_mul (by norm_num)]
    apply Or.inl h₃

  -- Since each term in the sum $P(n) = A(n^3 - n) + B n^2 + (A+C)n$ is divisible by 3, their sum $P(n)$ must also be divisible by 3.\
  -- Thus, $P(n) \\equiv 0 \\pmod 3$ for any integer $n$.

-- **Part 3: Conclude $P(n)$ is divisible by 6.**
-- We have shown that $P(n)$ is divisible by 2 (from Part 1) and $P(n)$ is divisible by 3 (from Part 2) for any integer $n$.\
-- Since 2 and 3 are coprime integers (i.e., their greatest common divisor is 1), any integer that is divisible by both 2 and 3 must also be divisible by their product $2 \\cdot 3 = 6$.\
-- Therefore, $P(n) = A n^3 + B n^2 + C n$ is divisible by 6 for any integer $n$.
-- The final answer is $\\boxed{A n^3 + B n^2 + C n \\text{ is divisible by } 6}$.
theorem number_theory_636687 (A B C : ℤ)
  (h₁ : 2 ∣ A + B + C) (h₂ : 3 ∣ B) (h₃ : 3 ∣ (A + C)):
  ∀ n, 6 ∣ A * n^3 + B * n^2 + C * n := by
  intro n
  rw [(show (6 : ℤ) = 2 * 3 by norm_num)]
  apply IsCoprime.mul_dvd (by norm_num)
  · apply part1 h₁ -- 2 ∣ A * n^3 + B * n^2 + C * n
  · apply part2 h₂ h₃ -- 3 ∣ (A * n^3 + B * n^2 + C * n)
