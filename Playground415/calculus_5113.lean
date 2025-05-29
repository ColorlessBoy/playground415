import Mathlib

open Real Set
open scoped BigOperators

/- Let $f(x) = x + \ln x$ for $x > 0$. Given that $f$ admits an inverse function $g$, calculate $g''(1)$. -/
theorem calculus_5113 {f : ℝ → ℝ} (hf : ∀ x, 0 < x → f x = x + log x)
(g : ℝ → ℝ) (hg : Function.LeftInverse g f) : deriv (deriv g) 1 = 1 / 8 := by
  -- Step 1: Compute f(1) = 1 + ln(1) = 1
  have hf1 : f 1 = 1 := by rw [hf 1 (by simp)]; simp

  -- Step 2: Use left-inverse property: g(f(1)) = 1 ⇒ g(1) = 1
  have hg1 : g 1 = 1 := by nth_rw 1 [← hf1]; apply hg 1

  -- Helper: open right-sided neighborhood for derivation
  have hioi (x : ℝ) (hx : x > 0): Ioi (x / 2) ∈ nhds x :=
    Ioi_mem_nhds (div_lt_self hx (by norm_num))

  -- Step 3: Compute f'(x) = 1 + 1/x
  have hf' (x : ℝ) (hx : x > 0) : deriv f x = (1 + x⁻¹) := by
    have hfx := hf x hx
    rw [← deriv_id x, ← deriv_log x,
        ← deriv_add differentiableAt_id (differentiableAt_log (ne_of_gt hx))]
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.eventuallyEq_of_mem (hioi x hx)
    intro y hy
    simp at hy
    simp
    have : y > 0 := by apply lt_trans _ hy; apply div_pos hx (by norm_num)
    exact hf y this

  -- Step 4: Compute f''(x) = -1 / x²
  have hf'' (x : ℝ) (hx : x > 0) : deriv (deriv f) x = -(x ^ 2)⁻¹ := by
    have hfx := hf' x hx
    have : deriv (fun x => 1 + x⁻¹) x = -(x ^ 2)⁻¹ := by
      rw [← deriv_inv, deriv_add (differentiableAt_const 1) (differentiableAt_inv (ne_of_gt hx)),
          deriv_const, zero_add]
    rw [← this]
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.eventuallyEq_of_mem (hioi x hx)
    intro y hy
    simp at hy
    have hypos : y > 0 := by apply lt_trans _ hy; apply div_pos hx (by norm_num)
    simp
    exact hf' y hypos

  -- Step 5: Since g(f(x)) = x ⇒ (g ∘ f)'(x) = 1
  have hgof' (x : ℝ) (hx : x > 0) : deriv (g ∘ f) x = 1 := by
    rw [← deriv_id x]
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.eventuallyEq_of_mem (hioi x hx)
    intro y hy
    simp
    rw [hg y]

  -- Step 6: Derivative of constant 1 is 0 ⇒ (g ∘ f)''(x) = 0
  have hgof'' (x : ℝ) (hx : x > 0) : deriv (deriv (g ∘ f)) x = 0 := by
    rw [← deriv_const x 1]
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.eventuallyEq_of_mem (hioi x hx)
    intro y hy
    simp
    have hypos : y > 0 := by apply lt_trans _ hy; apply div_pos hx (by norm_num)
    apply hgof' y hypos

  -- Step 7: Preparation — assume differentiability conditions (to be proven)
  have differentiable_fx (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ f x := by sorry
  have differentiable_dfx (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ (deriv f) x := by sorry
  have differentiable_gfx (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ g (f x) := by sorry
  have differentiable_dgx (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ (deriv g) (f x) := by sorry
  have differentiable_dgfx (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ (fun x => deriv g (f x)) x := by sorry

  -- Step 8: By chain rule, (g ∘ f)' = g'(f(x)) * f'(x)
  have hgof'2 (x : ℝ) (hx : x > 0): deriv (g ∘ f) x = deriv g (f x) * deriv f x := by
    apply deriv_comp
    · exact differentiable_gfx x hx
    exact differentiable_fx x hx

  -- Step 9: Differentiate again using product rule
  have hgof''2 (x : ℝ) (hx : x > 0): 0 = deriv (deriv g) (f x) * (1 + x⁻¹) * (1 + x⁻¹) + deriv g (f x) * -(x ^ 2)⁻¹ := by
    have : deriv (deriv (g ∘ f)) x = deriv (fun x => deriv g (f x) * deriv f x) x := by
      apply Filter.EventuallyEq.deriv_eq
      apply Filter.eventuallyEq_of_mem (hioi x hx)
      intro y hy
      simp at hy
      have hypos : y > 0 := by apply lt_trans _ hy; apply div_pos hx (by norm_num)
      simp
      apply deriv_comp
      · exact differentiable_gfx y hypos
      exact differentiable_fx y hypos
    -- Chain rule on second derivative
    have hgof''3 (x : ℝ) (hx : x > 0) : deriv ((deriv g)∘f) x = deriv (deriv g) (f x) * deriv f x := by
      apply deriv_comp
      · exact differentiable_dgx x hx
      exact differentiable_fx x hx
    have hgof''4 : (fun x => deriv g (f x)) = (deriv g) ∘ f := by rfl
    rw [deriv_mul , hgof''4, hgof''3, hf' x hx, hf'' x hx, hgof'' x hx] at this
    exact this
    exact hx
    exact differentiable_dgfx x hx
    exact differentiable_dfx x hx
  have hgf1 : deriv g 1 = 1 / 2 := by
    have := hgof'2 1 (by norm_num)
    simp at this
    rw [hgof' 1 (by norm_num), hf' 1 (by norm_num), hf1] at this
    ring_nf at this
    linarith
  have := hgof''2 1 (by norm_num)
  rw [hf1, hgf1] at this
  ring_nf at this
  linarith
