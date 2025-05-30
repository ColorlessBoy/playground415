import Mathlib

open Polynomial

-- If x divides a prime y and x > 1, then x must equal y
lemma prime_eq (x y : ℕ) (h1 : 1 < x) (h2 : x ∣ y) (h3 : Nat.Prime y) : x = y := by
  -- Apply the fact that if a prime is divisible by x, then x = 1 or x = y
  have h4 : x = 1 ∨ x = y := by
    apply (Nat.dvd_prime h3).mp
    exact h2
  -- Eliminate the disjunction
  rcases h4 with h | h
  · linarith  -- Contradicts h1: 1 < x
  · exact h   -- x = y, as required

-- If x1, x2, x3 are distinct nonzero integers and at most two of them have absolute value ≤ 1,
-- then the third must have absolute value > 1
lemma lemma0 (x1 x2 x3 : ℤ) (h1: x1 ≠ x2) (h2: x1 ≠ x3) (h4: x2 ≠ x3)
  (h5: x1 ≠ 0) (h6: x2 ≠ 0) (h7: x3 ≠ 0) (h8 : ¬ x1.natAbs > 1) (h9 : ¬ x2.natAbs > 1):
    x3.natAbs > 1 := by
  -- Assume for contradiction that x3.natAbs ≤ 1
  by_contra h10
  push_neg at h8; push_neg at h9; push_neg at h10
  -- Then all three must be in {-1, 0, 1}
  have h8' : x1 = -1 ∨ x1 = 0 ∨ x1 = 1 := by omega
  have h9' : x2 = -1 ∨ x2 = 0 ∨ x2 = 1 := by omega
  have h10' : x3 = -1 ∨ x3 = 0 ∨ x3 = 1 := by omega
  -- Case split to derive a contradiction from the distinctness assumptions
  rcases h8' with (h8' | h8' | h8')
  · rcases h9' with (h9' | h9' | h9')
    · rw [h8', h9'] at h1; contradiction
    · contradiction
    · rcases h10' with (h10' | h10' | h10')
      · rw [h8', h10'] at h2; contradiction
      · contradiction
      · rw [h9', h10'] at h4; contradiction
  · contradiction
  · rcases h9' with (h9' | h9' | h9')
    · rcases h10' with (h10' | h10' | h10')
      · rw [h9', h10'] at h4; contradiction
      · contradiction
      · rw [h8', h10'] at h2; contradiction
    · contradiction
    · rw [h8', h9'] at h1; contradiction

-- If x is a root of polynomial Q, then (X - C x) divides Q
lemma lemma1 {Q : ℤ[X]} {x : ℤ} (h : Q.eval x = 0) : ∃ R : ℤ[X], Q = (X - C x) * R := by
  -- Use the characterization of roots via divisibility
  have h1 : (X - C x) ∣ Q := by rw [dvd_iff_isRoot]; simp [h]
  exact h1

-- If Q = (X - C x1) * R and x2 ≠ x1 is a root of Q, then x2 is a root of R
lemma lemma2 {Q R : ℤ[X]} {x1 x2 : ℤ} (h2 : Q.eval x2 = 0) (h12 : x1 ≠ x2) (h : Q = (X - C x1) * R) : R.eval x2 = 0 := by
  -- Helper: (X - C a).eval x ≠ (X - C b).eval x when a ≠ b
  have hXne {a b x : ℤ} (h : a ≠ b) : (X - C a).eval x ≠ (X - C b).eval x := by
    intro h1
    rw [eval_sub, eval_sub, sub_eq_sub_iff_add_eq_add, add_left_cancel_iff, eval_C, eval_C] at h1
    exact h h1.symm
  -- Compute (X - C x2).eval x2 = 0
  have hXne' : (X - C x2).eval x2 = 0 := by rw [eval_sub, eval_X, eval_C, sub_self]
  -- Use x1 ≠ x2 to get contradiction if you try to cancel
  have hXne'' := hXne h12 (x := x2)
  rw [hXne'] at hXne''
  -- Evaluate Q at x2 using the factorization
  have h₁ : Q.eval x2 = ((X - C x1) * R).eval x2 := by rw [h]
  rw [h2, eval_mul] at h₁
  -- From the evaluation and ≠ 0 fact, deduce R.eval x2 = 0
  exact (mul_eq_zero_iff_left hXne'').mp h₁.symm

-- lemma3: If Q has four distinct integer roots, then Q can be factored into linear terms over ℤ[X]
lemma lemma3 {Q : ℤ[X]} {x1 x2 x3 x4 : ℤ}
  (h1 : Q.eval x1 = 0) (h2 : Q.eval x2 = 0) (h3 : Q.eval x3 = 0) (h4 : Q.eval x4 = 0)
  (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4) (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h34 : x3 ≠ x4)
  : ∃ R : ℤ[X], Q = (X - C x1) * (X - C x2) * (X - C x3) * (X - C x4) * R := by
  -- Use lemma1 to factor out (X - x1)
  obtain ⟨R₁, h₁⟩ := lemma1 h1
  -- Use lemma2 to show R₁(x₂), R₁(x₃), R₁(x₄) = 0
  have hR₁x2 : eval x2 R₁ = 0 := lemma2 h2 h12 h₁
  have hR₁x3 : eval x3 R₁ = 0 := lemma2 h3 h13 h₁
  have hR₁x4 : eval x4 R₁ = 0 := lemma2 h4 h14 h₁
  -- Factor out (X - x2)
  obtain ⟨R₂, h₂⟩ := lemma1 hR₁x2
  have hR₂x3 : eval x3 R₂ = 0 := lemma2 hR₁x3 h23 h₂
  have hR₂x4 : eval x4 R₂ = 0 := lemma2 hR₁x4 h24 h₂
  -- Factor out (X - x3)
  obtain ⟨R₃, h₃⟩ := lemma1 hR₂x3
  have hR₃x4 : eval x4 R₃ = 0 := lemma2 hR₂x4 h34 h₃
  -- Factor out (X - x4)
  obtain ⟨R₄, h₄⟩ := lemma1 hR₃x4
  use R₄
  -- Recompose the factorization back into Q
  rw [mul_assoc, mul_assoc, mul_assoc, ← h₄, ← h₃, ← h₂, ← h₁]

-- lemma4: If Q has 4 distinct integer roots, and x is not a root, then Q(x) has at least two nontrivial divisors
lemma lemma4 {Q : ℤ[X]}  {x : ℤ}
  (conds : ∃ x1 x2 x3 x4 : ℤ, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
        Q.eval x1 = 0 ∧ Q.eval x2 = 0 ∧ Q.eval x3 = 0 ∧ Q.eval x4 = 0)
  (h: Q.eval x ≠ 0) : ∃ a > 1, ∃ b > 1, a * b ∣ (Q.eval x).natAbs := by
  -- Step 1: Extract the 4 distinct roots from the hypothesis
  obtain ⟨x1, x2, x3, x4, h12, h13, h14, h23, h24, h34, hP1, hP2, hP3, hP4⟩ := conds
  let S := (X - C x1) * (X - C x2) * (X - C x3) * (X - C x4)

  -- Step 2: Use lemma3 to factor Q = S * R
  have h_div : ∃ R : ℤ[X], Q = S * R := by
    unfold S
    apply lemma3 hP1 hP2 hP3 hP4 h12 h13 h14 h23 h24 h34

  -- Auxiliary: Show evaluation of (X - C a) ≠ (X - C b) at x when a ≠ b
  have hXne {a b x : ℤ} (h : a ≠ b) : (X - C a).eval x ≠ (X - C b).eval x := by
    intro h1
    rw [eval_sub, eval_sub, sub_eq_sub_iff_add_eq_add, add_left_cancel_iff, eval_C, eval_C] at h1
    exact h h1.symm

  -- Step 3: Evaluate Q(x) = S(x) * R(x)
  obtain ⟨R, hQR⟩ := h_div
  let Qx := Q.eval x
  let Sx := S.eval x
  let Rx := R.eval x
  let Sx1 := (X - C x1).eval x
  let Sx2 := (X - C x2).eval x
  let Sx3 := (X - C x3).eval x
  let Sx4 := (X - C x4).eval x

  -- Step 4: Expand Q(x) as product of individual linear factors evaluated at x
  have hQx : Qx = Sx1 * Sx2 * Sx3 * Sx4 * Rx := by
    unfold Qx Rx Sx1 Sx2 Sx3 Sx4
    rw [hQR, eval_mul]
    unfold S
    rw [eval_mul, eval_mul, eval_mul]

  -- Step 5: Show each linear factor evaluated at x is nonzero (x is not a root)
  have hx1ne0 : Sx1 ≠ 0 := by intro h; rw [h, zero_mul, zero_mul, zero_mul, zero_mul] at hQx; contradiction
  have hx2ne0 : Sx2 ≠ 0 := by intro h; rw [h, mul_zero, zero_mul, zero_mul, zero_mul] at hQx; contradiction
  have hx3ne0 : Sx3 ≠ 0 := by intro h; rw [h, mul_zero, zero_mul, zero_mul] at hQx; contradiction
  have hx4ne0 : Sx4 ≠ 0 := by intro h; rw [h, mul_zero, zero_mul] at hQx; contradiction

  by_cases hSx1 : Sx1.natAbs > 1
  · by_cases hSx2 : Sx2.natAbs > 1
    · use Sx1.natAbs; apply And.intro hSx1; use Sx2.natAbs; apply And.intro hSx2; use (Sx3 * Sx4 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring
    by_cases hSx3 : Sx3.natAbs > 1
    · use Sx1.natAbs; apply And.intro hSx1; use Sx3.natAbs; apply And.intro hSx3; use (Sx2 * Sx4 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring
    · have hSx4 := lemma0 Sx2 Sx3 Sx4 (hXne h23) (hXne h24) (hXne h34) hx2ne0 hx3ne0 hx4ne0 hSx2 hSx3
      use Sx1.natAbs; apply And.intro hSx1; use Sx4.natAbs; apply And.intro hSx4; use (Sx2 * Sx3 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring
  · by_cases hSx2 : Sx2.natAbs > 1
    · by_cases hSx3 : Sx3.natAbs > 1
      · use Sx2.natAbs; apply And.intro hSx2; use Sx3.natAbs; apply And.intro hSx3; use (Sx1 * Sx4 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring
      · have hSx4 := lemma0 Sx1 Sx3 Sx4 (hXne h13) (hXne h14) (hXne h34) hx1ne0 hx3ne0 hx4ne0 hSx1 hSx3
        use Sx2.natAbs; apply And.intro hSx2; use Sx4.natAbs; apply And.intro hSx4; use (Sx1 * Sx3 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring
    · have hSx3 := lemma0 Sx1 Sx2 Sx3 (hXne h12) (hXne h13) (hXne h23) hx1ne0 hx2ne0 hx3ne0 hSx1 hSx2
      have hSx4 := lemma0 Sx1 Sx2 Sx4 (hXne h12) (hXne h14) (hXne h24) hx1ne0 hx2ne0 hx4ne0 hSx1 hSx2
      use Sx3.natAbs; apply And.intro hSx3; use Sx4.natAbs; apply And.intro hSx4; use (Sx1 * Sx2 * Rx).natAbs; unfold Qx at hQx; rw [hQx, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; ring

theorem algebra_124781 {P : ℤ[X]}
  (conds : ∃ x1 x2 x3 x4 : ℤ, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
        P.eval x1 = 2 ∧ P.eval x2 = 2 ∧ P.eval x3 = 2 ∧ P.eval x4 = 2) :
      ∀ x : ℤ, P.eval x ∉ ({1, 3, 5, 7, 9} : Set ℤ) := by
  intros x

  -- Step 1: Define Q(x) = P(x) - 2
  let Q := P - C 2

  -- Step 2: From the hypothesis, Q vanishes at four distinct integer points
  obtain ⟨x1, x2, x3, x4, h12, h13, h14, h23, h24, h34, hP1, hP2, hP3, hP4⟩ := conds

  -- Q(x) = 0 whenever P(x) = 2
  have hQ {x: ℤ} (h : P.eval x = 2) : Q.eval x = 0 := by
    unfold Q
    rw [eval_sub, eval_C, h, sub_self]

  -- If Q(x) ≠ 0, then Q(x) is divisible by a*b for some integers a,b > 1
  have hQ1 {x : ℤ} (h: Q.eval x ≠ 0) : ∃ a > 1, ∃ b > 1, a * b ∣ (Q.eval x).natAbs := by
    apply lemma4
    use x1, x2, x3, x4
    exact ⟨h12, h13, h14, h23, h24, h34, hQ hP1, hQ hP2, hQ hP3, hQ hP4⟩
    exact h

  -- If P(m) = n, then Q(m) = n - 2
  have hQ2 {m n : ℤ} (h : P.eval m = n) : Q.eval m = n - 2 := by
    unfold Q
    rw [eval_sub, eval_C, h]

  -- Case split: either Q(x) = 0 or not
  by_cases hQ0 : Q.eval x = 0
  · -- If Q(x) = 0, then P(x) = 2 and thus not in {1,3,5,7,9}
    have hP0 : P.eval x = 2 := by
      unfold Q at hQ0
      rw [eval_sub, eval_C, sub_eq_zero] at hQ0
      exact hQ0
    rw [hP0]
    simp

  -- If Q(x) ≠ 0, then apply lemma4 to find nontrivial factors
  have ⟨x₁, hx₁, x₂, hx₂, hdvd⟩ := hQ1 hQ0

  -- Now assume P(x) ∈ {1, 3, 5, 7, 9} and derive contradiction
  intro h
  simp at h

  -- Case: P(x) = 1
  cases' h with h h
  · have h' := hQ2 h
    rw [h'] at hdvd
    simp at hdvd
    apply ne_of_lt hx₁ hdvd.left.symm

  -- Case: P(x) = 3
  cases' h with h h
  · have h' := hQ2 h
    rw [h'] at hdvd
    simp at hdvd
    apply ne_of_lt hx₁ hdvd.left.symm

  -- Case: P(x) = 5
  cases' h with h h
  · have h' := hQ2 h
    rw [h'] at hdvd
    simp at hdvd
    have h2 := prime_eq x₁ 3 hx₁ (dvd_of_mul_right_dvd hdvd) Nat.prime_three
    have h3 := prime_eq x₂ 3 hx₂ (dvd_of_mul_left_dvd hdvd) Nat.prime_three
    rw [h2, h3] at hdvd
    norm_cast

  -- Case: P(x) = 7
  cases' h with h h
  · have h' := hQ2 h
    rw [h'] at hdvd
    simp at hdvd
    have h2 := prime_eq x₁ 5 hx₁ (dvd_of_mul_right_dvd hdvd) Nat.prime_five
    have h3 := prime_eq x₂ 5 hx₂ (dvd_of_mul_left_dvd hdvd) Nat.prime_five
    rw [h2, h3] at hdvd
    norm_cast

  -- Case: P(x) = 9
  · have h' := hQ2 h
    rw [h'] at hdvd
    simp at hdvd
    have h2 := prime_eq x₁ 7 hx₁ (dvd_of_mul_right_dvd hdvd) (by decide)
    have h3 := prime_eq x₂ 7 hx₂ (dvd_of_mul_left_dvd hdvd) (by decide)
    rw [h2, h3] at hdvd
    norm_cast
