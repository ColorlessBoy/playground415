import Mathlib
open Nat

lemma lemma1 {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
  ∃ (d a b : ℕ), d > 0 ∧ a > 0 ∧ b > 0 ∧ x = d * a ∧ y = d * b ∧ Nat.Coprime a b := by
    let d := x.gcd y
    let a := x / d
    let b := y / d
    have hd : d > 0 := Nat.gcd_pos_iff.mpr (Or.inl hx)
    have hxd : x ≥ d := Nat.gcd_le_left _ hx
    have hyd : y ≥ d := Nat.gcd_le_right _ hy
    have ha : a > 0 := Nat.div_pos hxd (Nat.gcd_pos_of_pos_right x hy)
    have hb : b > 0 := Nat.div_pos hyd (Nat.gcd_pos_of_pos_left y hx)
    refine ⟨d, a, b, hd, ha, hb, ?_, ?_, ?_⟩
    · rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left x y)]
    · rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]
    · exact Nat.coprime_div_gcd_div_gcd hd

lemma lemma2 (a b : ℕ) (hab : Nat.Coprime a b)
  : ((a * b ^ 2).Coprime (a + b)) := by
  apply Nat.Coprime.mul
  · rw [Nat.Coprime, add_comm, Nat.gcd_add_self_right, ← Nat.Coprime]
    exact hab
  apply Nat.Coprime.pow_left
  rw [Nat.Coprime, Nat.gcd_add_self_right, ← Nat.Coprime]
  exact hab.symm

lemma lemma3 {b p : ℕ} (h0 : b > 0) (h1 : Nat.Prime p) (h2 : b ^ 2 = p) : b = 1 := by
  have h : b ∣ p := by use b; rw [← h2, pow_two]
  have := (Nat.dvd_prime h1).mp h
  apply Or.elim this
  · apply id
  intro hb
  rw [← hb] at h2
  nlinarith

lemma lemma4 {p d : ℕ} (hp : Nat.Prime p) (h : p * 2 = d ^ 2) : d = 2 := by
  rw [pow_two] at h
  have h2 : 2 ∣ d := by
    have : 2 ∣ d * d := by rw [← pow_two]; use p; rw [mul_comm, h, pow_two]
    have := (Nat.Prime.dvd_mul Nat.prime_two).mp this
    apply this.elim <;> exact id
  obtain ⟨k, hk⟩ := h2
  have h1 : d ∣ p * 2 := Exists.intro d h
  rw [hk, mul_comm, Nat.mul_dvd_mul_iff_right (Nat.succ_pos 1)] at h1
  have hk2 := (Nat.dvd_prime hp).mp h1
  apply hk2.elim
  · intro hk3; rw [hk, hk3, mul_one]
  intro hk3
  rw [hk, hk3]
  rw [hk, hk3, mul_comm, mul_assoc, mul_eq_mul_left_iff] at h
  have hp2 := Nat.Prime.pos hp
  exfalso
  apply h.elim
  · intro hp
    nth_rw 1 [← mul_one p] at hp
    have h1 := Nat.eq_of_mul_eq_mul_left hp2 hp
    have h2 : 2 * p > 1 := by
      rw [← mul_one 1]
      apply mul_lt_mul (le_refl 2) hp2 (le_refl 1) (Nat.zero_le 2)
    exact Nat.ne_of_lt h2 h1
  exact Nat.succ_ne_zero 1

lemma lemma5 {p d : ℕ} (hp : Nat.Prime p) (h : p + 1 = d ^ 2) : d = 2 ∧ p = 3 := by
  have h1 : p = d ^ 2 - 1 := by rw [← h, Nat.add_sub_cancel]
  have h2 : 1 ≤ d ^ 2 := by rw [← h]; apply Nat.le_add_left
  have h3 : 1 ≤ d := by rw [← Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1), one_pow]; exact h2
  have h4 : 1 ≤ p := Nat.Prime.pos hp
  have h5 : 1 < d ^ 2 := by rw [← h, Nat.lt_add_left_iff_pos]; exact h4
  have h6 : 0 < d := by apply lt_of_lt_of_le (Nat.zero_lt_succ 0) h3
  have h7 : p = (d - 1) * (d + 1) := by
    rw [h1, mul_add, mul_one, Nat.sub_mul, one_mul, pow_two, ← Nat.sub_add_comm, ← Nat.add_sub_assoc, Nat.sub_add_comm, Nat.add_sub_cancel]
    rw [← pow_two, ← h]; apply Nat.le_add_left; exact h3; apply Nat.le_mul_of_pos_left; exact h6
  have hd1 : d - 1 ∣ p := Exists.intro (d + 1) h7
  have hd2 : d + 1 ∣ p := Exists.intro (d - 1) (Eq.trans h7 (Nat.mul_comm _ _))
  have hd3 := (Nat.dvd_prime hp).mp hd1
  have hd4 := (Nat.dvd_prime hp).mp hd2
  have hd_lt : d - 1 < d + 1 := by omega
  apply hd3.elim
  · intro hd5; simp at hd5; apply And.intro hd5; rw [hd5] at h; simp at h; exact h
  · intro hd5
    apply hd4.elim
    · intro h; exfalso; omega
    · intro h; rw [← hd5] at h; exfalso; have := Nat.ne_of_lt hd_lt; exact this h.symm

-- 确定所有自然数对 $x, y$，使 $\frac{x y^2}{x+y}$ 是素数。
theorem number_theory_247811 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (hxy: ∃ p, Nat.Prime p ∧ p * (x + y) = (x * y^2))
  : (x, y) = (2, 2) ∨ (x, y) = (6, 2) := by
  obtain ⟨p, hp, hpxy⟩ := hxy
  obtain ⟨d, a, b, hd, ha, hb, hda, hdb, hab⟩ := lemma1 hx hy
  rw [hda, hdb, ← mul_add, mul_pow, ← mul_assoc, mul_comm p, mul_assoc, mul_assoc, Nat.mul_left_cancel_iff hd, mul_comm (d^2), ← mul_assoc] at hpxy
  have hp2 : a * b ^ 2 ∣ p := by
    apply Nat.Coprime.dvd_of_dvd_mul_right (lemma2 a b hab)
    use (d^2)
  have hb2 : b = 1 := by
    have h1 := dvd_trans (Nat.dvd_mul_left _ _) hp2
    have h2 := (Nat.dvd_prime hp).mp h1
    apply Or.elim h2
    · intro h; have := Nat.pow_eq_one.mp h; omega
    apply lemma3 hb hp
  have ha2 := dvd_trans (Nat.dvd_mul_right _ _) hp2
  have ha3 := (Nat.dvd_prime hp).mp ha2
  apply Or.elim ha3
  · intro ha4
    apply Or.inl
    rw [ha4, hb2] at hpxy
    simp at hpxy
    have hd2 := lemma4 hp hpxy
    rw [hda, hdb, hd2, ha4, hb2, mul_one]
  intro ha4
  apply Or.inr
  rw [ha4, hb2, one_pow, mul_one, Nat.mul_left_cancel_iff (Nat.Prime.one_le hp)] at hpxy
  have ⟨h1, h2⟩ := lemma5 hp hpxy
  rw [hda, hdb, h1, ha4, h2, hb2]
