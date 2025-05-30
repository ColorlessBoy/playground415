import Mathlib

-- Lemma 1: A symbolic identity expanding and factoring a cubic polynomial
lemma lemma1 (n : ℕ) : n^3 + 3*n^2 + 3*n = n * ((n+1)^2+(n+1)+1) := by ring

-- Lemma 2: Another symbolic identity involving a cubic polynomial plus 2
lemma lemma2 (n : ℕ) : n^3 + 3*n^2 + 3*n + 2 = (n+1+1) * (n^2+n+1) := by ring

-- Lemma 3: A rational expression identity for natural numbers between 1 and 99
-- It rewrites the ratio of two symbolic expressions as a product of simpler rational factors
lemma lemma3 (n : ℕ) (_ : n ∈ Finset.Icc 1 99) :
  ((n^3 + 3*n^2 + 3*n) : ℚ)/(n^3 + 3*n^2 + 3*n + 2) =
    (n/(n+1))*((n+1)/(n+1+1))*(((n+1)^2+(n+1)+1)/(n^2+n+1)) := by
  norm_cast
  rw [lemma2, lemma1]
  simp
  rw [mul_div_mul_comm, ← mul_div_assoc, ← mul_div_assoc _ ((n:ℚ)+1), div_mul_cancel₀, mul_div_assoc]
  norm_cast

-- Lemma 4: Telescoping product over a rational function f(n)/f(n+1) from 1 to n
-- The result is simply f(1)/f(n+1), provided f(n) ≠ 0 for n > 0
lemma prod_range_div_1
  (n : ℕ) (hn : n > 0)
  (f : ℕ → ℚ)
  (hf : ∀ n > 0, f n ≠ 0)
  : ∏ x ∈ Finset.Icc (1:ℕ) n, (f x) / (f (x + 1)) = f 1 / (f (n+1)) := by
  induction n with
  | zero =>
    -- Base case contradiction: n > 0 cannot hold if n = 0
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      -- Base case: Icc 1 1 = {1}, product simplifies directly
      norm_num
    | succ n =>
      -- Inductive step: break product at top and apply IH
      rw [Finset.prod_Icc_succ_top (by norm_num)]
      rw [ih (by omega), ← mul_div_assoc, div_mul_cancel₀]
      field_simp
      apply hf
      apply Nat.succ_pos

-- Lemma 5: Similar telescoping product for f(n+1)/f(n), equals f(n+1)/f(1)
lemma prod_range_div_2
  (n : ℕ) (hn : n > 0)
  (f : ℕ → ℚ)
  (hf : ∀ n > 0, f n ≠ 0)
  : ∏ x ∈ Finset.Icc (1:ℕ) n, (f (x + 1)) / (f x)  = (f (n+1)) / f 1 := by
  induction n with
  | zero =>
    -- Again, contradiction in base case
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      -- Base case: Icc 1 1 = {1}, compute directly
      norm_num
    | succ n =>
      -- Inductive step: apply identity transformations and IH
      rw [Finset.prod_Icc_succ_top (by norm_num)]
      rw [ih (by omega), div_mul_div_comm, mul_comm, ← div_mul_div_comm, div_self, mul_one]
      apply hf
      apply Nat.succ_pos

-- Lemma 6: Product ∏ x / (x+1) from 1 to 99 is 1/100
lemma lemma4 : ∏ x ∈ Finset.Icc (1:ℕ) 99, (x : ℚ) / (x + 1) = 1 / 100 := by
  have h0 (n : ℕ) (hn : n > 0): (n:ℚ) ≠ 0 := by norm_cast; apply Nat.ne_zero_iff_zero_lt.mpr hn
  have h1:= prod_range_div_1 99 (Nat.succ_pos 98) (fun (n:ℕ) => (n:ℚ)) h0
  simp at h1; simp; rw [h1]

-- Lemma 7: Product ∏ (x+1)/(x+2) from 1 to 99 is 2/101
lemma lemma5 : ∏ x ∈ Finset.Icc (1:ℕ) 99, (x + 1 : ℚ) / (x + 1 + 1) = 2 / 101 := by
  have h0 (n : ℕ) (hn : n > 0): (n:ℚ) + 1 ≠ 0 := by norm_cast
  have h1:= prod_range_div_1 99 (Nat.succ_pos 98) (fun (n:ℕ) => (n + 1:ℚ)) h0
  simp at h1; simp; rw [h1]; norm_num

-- Lemma 8: Product of rational expressions involving (x+1)^2 + (x+1) + 1 over x^2 + x + 1
lemma lemma6 : ∏ x ∈ Finset.Icc (1:ℕ) 99, (((x : ℚ) + 1) ^ 2 + (x + 1) + 1) / (x ^ 2 + x + 1) =
  (((99:ℚ) + 1)^2 + (99 + 1) + 1) / (1 ^ 2 + 1 + 1) := by
  have h0 (n : ℕ) (hn : n > 0): (n:ℚ) ^ 2 + n + 1 ≠ 0 := by norm_cast
  have h1:= prod_range_div_2 99 (Nat.succ_pos 98) (fun (n:ℕ) => (n:ℚ)^2 + n + 1) h0
  simp at h1; simp; rw [h1]; norm_num

-- Final theorem: The full product simplifies to 3367 / 5050
-- ∏ (n = 1 to 99) of (n^3 + 3n^2 + 3n) / (n^3 + 3n^2 + 3n + 2) = 3367 / 5050
theorem algebra_634536 :
  (∏ n in (Finset.Icc (1:ℕ) 99), (((n^3 + 3*n^2 + 3*n) : ℚ)/(n^3 + 3*n^2 + 3*n + 2))) = (3367:ℚ)/5050 := by
  have h := Finset.prod_congr (s₁ := Finset.Icc 1 99) (s₂ := Finset.Icc 1 99) (by rfl) lemma3
  rw [h, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [lemma4, lemma5, lemma6]
  ring
