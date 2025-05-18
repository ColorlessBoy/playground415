import Mathlib

-- 定义条件
namespace number_theory_305100
def cond (M : Set ℤ) : Prop :=
  (∀ a ∈ M, ∀ b ∈ M, a ≠ b → a + b ∈ M) ∧ (∃ a ∈ M, ∃ b ∈ M, a * b < 0)

lemma add_eq_right {a b : Int} : a + b = b ↔ a = 0 := calc
  a + b = b ↔ a + b = 0 + b := by rw [zero_add b]
  _ ↔ a = 0 := by omega

lemma Q1 (M : Set ℤ) (hM : cond M) : 0 ∈ M := by
  obtain ⟨hab_sum, ⟨a, ha, b, hb, hab_neg⟩⟩ := hM
  by_cases hsum : a + b = 0
  · -- 情况一：a + b = 0，直接得出 0 ∈ M
    by_cases heq : a = b
    · rw [heq, ← mul_two, mul_eq_zero_iff_right] at hsum
      rw [hsum] at hb
      exact hb
      norm_cast
    rw [← hsum]
    apply hab_sum a ha b hb heq
  · -- 情况二：a + b ≠ 0，构造 x, -x ∈ M，从而得出 0 ∈ M
    by_contra h0
    have hne0 {x : ℤ} (hx : x ∈ M) : x ≠ 0 := by intro hxeq0; rw [hxeq0] at hx; exact h0 hx
    have hmn : ∃ m > 0, ∃ n > 0, a * m + b * n = 0 := by
      -- 可通过类似的方法归纳构造，最终得到 m, n
      by_cases hb2 : b > 0
      · use b; apply And.intro hb2
        use -a; apply And.intro (by nlinarith) (by rw [mul_comm b, neg_mul, add_neg_cancel])
      use -b
      apply And.intro
      · have := hne0 hb
        omega
      use a; apply And.intro (by nlinarith) (by rw [mul_comm, neg_mul, neg_add_cancel])
    have haneb : a ≠ b := by
      intro hab
      rw [hab] at hab_neg
      have := mul_self_nonneg b
      exact not_lt_of_ge this hab_neg
    have hapb : a + b ∈ M := hab_sum a ha b hb haneb
    obtain ⟨m, hm_pos, ⟨n, hn_pos, hmn_eq⟩⟩ := hmn
    have h_cond0 {p : ℤ} (h1 : a * p + b ∈ M) : a * (p + 1) + b ≠ a := by
      intro h
      rw [mul_add, mul_one, add_assoc, add_comm a, ← add_assoc, add_eq_right] at h
      exact hne0 h1 h
    have h_cond1 {p : ℤ} (h1 : a * p + b ∈ M) (h2 : a * (p + 1) + b ∈ M) : a * (p + 2) + b ∈ M := by
      have := hab_sum _ h2 _ ha (h_cond0 h1)
      rw [add_assoc, add_comm b, ← add_assoc, mul_add, mul_one, add_assoc (a * p), ← mul_two] at this
      rw [mul_add]
      exact this
    have h_cond2 {q : ℤ} (h1 : a + b * q ∈ M) : a + b * (q + 1) ≠ b := by
      intro h
      rw [mul_add, mul_one, ← add_assoc, add_eq_right] at h
      exact hne0 h1 h
    have h_cond3 {q : ℤ} (h1 : a + b * q ∈ M) (h2 : a + b * (q + 1) ∈ M) : a + b * (q + 2) ∈ M := by
      have := hab_sum _ h2 _ hb (h_cond2 h1)
      rw [mul_add, add_assoc, mul_one, add_assoc, ← mul_two, ← mul_add] at this
      exact this
    have h_cond4 {q : ℤ} (h1 : a * 2 + b * q ∈ M) (h2 : a * 2 + b * (q + 1) ∈ M) : a * 2 + b * (q + 2) ∈ M := by
      rw [(show (2 : Int) = 1 + 1 by norm_num), ← add_assoc, mul_add b, mul_one, ← add_assoc]
      apply hab_sum
      simp; exact h2; exact hb
      intro h
      rw [mul_add b, ← add_assoc, mul_one, add_eq_right] at h
      simp at h
      exact hne0 h1 h
    have h_ind1 : a * 2 + b ∈ M := by rw [← zero_add (2:Int)]; apply h_cond1; simp; exact hapb; simp; exact hb
    have h_ind2 : a + b * 2 ∈ M := by rw [← zero_add (2:Int)]; apply h_cond3; simp; exact hapb; simp; exact ha
    have h_ind3 {p : ℕ} : a * p + b ∈ M := by
      induction' p using Nat.strong_induction_on with p hp
      by_cases h0 : p = 0
      · rw [h0]; simp; exact hb
      by_cases h1 : p = 1
      · rw [h1]; simp; exact hapb
      have : ∃ n, p = n + 2 := by use p - 2; omega
      obtain ⟨n, hn⟩ := this
      rw [hn]
      simp; apply h_cond1; norm_cast; apply hp; omega; apply hp; omega
    have h_ind4 {q : ℕ} : a + b * q ∈ M := by
      induction' q using Nat.strong_induction_on with q hq
      by_cases h0 : q = 0
      · rw [h0]; simp; exact ha
      by_cases h1 : q = 1
      · rw [h1]; simp; exact hapb
      have : ∃ n, q = n + 2 := by use q - 2; omega
      obtain ⟨n, hn⟩ := this
      rw [hn]
      simp; apply h_cond3; norm_cast; apply hq; omega; apply hq; omega
    have h_mul_n0 {q : ℕ} (hq : q > 0) : a * q ≠ 0 := by apply mul_ne_zero (hne0 ha); simp; omega
    have h_ind5 {q : ℕ} (hq : q > 0) : a * 2 + b * q ∈ M := by
      induction' q using Nat.strong_induction_on with q ihq
      by_cases h0 : q = 0
      · exfalso; omega
      by_cases h1 : q = 1
      · rw [h1, mul_two, add_assoc, add_comm]; simp;
        apply hab_sum _ hapb _ ha
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
      have : ∃ n > 0, q = n + 2 := by use q - 2; omega
      obtain ⟨n, hn1, hn2⟩ := this
      rw [hn2]; simp; apply h_cond4; apply ihq; nlinarith; norm_num;
      apply ihq; omega; exact hn1
    have h_ind6 {p : ℕ} (hp : p > 0) {q : ℕ} (hq : q > 0) : a * p + b * q ∈ M := by
      induction' p using Nat.strong_induction_on with p ihp
      by_cases h0 : p = 0
      · exfalso; omega
      by_cases h1 : p = 1
      · rw [h1]; simp; apply h_ind4
      by_cases h2 : p = 2
      · rw [h2]; simp; apply h_ind5 hq
      have : ∃ n > 0, p = n + 2 := by use p - 2; omega
      obtain ⟨n, hn1, hn2⟩ := this
      rw [hn2]; simp; rw [(show n + (2:Int) = 1 + (n + 1) by omega), mul_add, mul_one, add_assoc, add_comm]
      apply hab_sum
      apply ihp; nlinarith; omega; exact ha; intro h; rw [mul_add, mul_one, add_comm, ← add_assoc, add_eq_right, add_comm] at h
      have := hne0 (ihp n (by omega) hn1)
      apply this h
    have hpq : ∀ p > 0, ∀ q > 0, a * p + b * q ∈ M := by
      intro p hp q hq
      have : ∃ (x : ℕ), p = x := by
        use p.toNat
        simp [Int.ofNat_toNat, show 0 ≤ p by linarith]
      obtain ⟨x, hx1⟩ := this
      have hx2 : x > 0 := by omega
      have : ∃ (y : ℕ), q = y := by
        use q.toNat
        simp [Int.ofNat_toNat, show 0 ≤ q by linarith]
      obtain ⟨y, hy1⟩ := this
      have hy2 : y > 0 := by omega
      rw [hx1, hy1]
      apply h_ind6 hx2 hy2
    have := hpq _ hm_pos _ hn_pos
    exact hne0 this hmn_eq

lemma Q2 : ∃ M : Set ℤ, cond M ∧ Finite M := by
  let M : Set ℤ := {0, 1, -1}
  have h0 : 0 ∈ M := by apply Set.mem_insert
  have h1 : 1 ∈ M := by apply Set.mem_insert_iff.mpr; apply Or.inr; apply Set.mem_insert
  have h_1 : -1 ∈ M := by apply Set.mem_insert_iff.mpr; apply Or.inr; apply Set.mem_insert_iff.mpr; apply Or.inr; apply Set.mem_singleton
  refine ⟨M, ⟨?sum_cond, ?neg_exist⟩, ?finite⟩
  · intros a ha b hb hne
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp_all
  · use 1, h1, -1, h_1
    norm_num
  · apply Set.toFinite

end number_theory_305100

theorem number_theory_305100 : ((M : Set ℤ) →  (hM : number_theory_305100.cond M) → 0 ∈ M) ∧ ∃ M : Set ℤ, number_theory_305100.cond M ∧ Finite M := by
  constructor
  · exact number_theory_305100.Q1
  exact number_theory_305100.Q2
