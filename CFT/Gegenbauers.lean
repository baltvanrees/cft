/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
-- set_option profiler true
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
Gegenbauer polynomials C_n^{(ν)}(x).
For CFTs in d dimensions, the relevant parameter is ν = d/2 - 1.
Defined over ℂ so we can easily evaluate on complex kinematics.
-/

open Polynomial
open scoped Polynomial
open scoped Polynomial.Bivariate
open Complex
open scoped ComplexConjugate

noncomputable def gegenbauer (ν : ℂ) : ℕ → ℂ[X]
  | 0 => C 1
  | 1 => C (2 * ν) * X
  | j + 2 => X * gegenbauer ν (j + 1) * C (2 * (j + ν + 1) / (j + 2))
    - gegenbauer ν j * C ((j + 2 * ν) / (j + 2))

namespace gegenbauer

variable {ν : ℂ}

theorem eval_neg (n : ℕ) (x : ℂ) :
  (gegenbauer ν n).eval (-x) = (-1 : ℂ)^n * (gegenbauer ν n).eval x := by
  induction n using gegenbauer.induct with
  | case1 => -- n = 0
    rw [gegenbauer, eval_C, eval_C, pow_zero, mul_one]
  | case2 => -- n = 1
    rw [gegenbauer, eval_C_mul, eval_C_mul, eval_X, eval_X]; ring
  | case3 j ih1 ih2=> -- n ≥ 2
    rw [gegenbauer, eval_sub, eval_sub]
    repeat rw [eval_mul]
    rw [ih1, ih2]
    repeat rw [eval_C, eval_X, eval_C]
    ring_nf
    set geg1 := eval x (gegenbauer ν j)
    set geg2 := eval x (gegenbauer ν (1 + j))
    have h_sign : (-1 : ℂ) ^ (j + 1 + 1) = (-1 : ℂ) ^ j := by ring
    rw [h_sign]

/-!
Construction of the two-variable functions r^n C_n^{(ν)}(η) with
r = ρ1 ρ2 and η = ((ρ1 / ρ2 + ρ2 / ρ1) / 2. We show that the coefficients
of this polynomial in ρl and ρr are known and always nonnegative.
-/

-- Complex-valued factorial
noncomputable def fact (a : ℕ) : ℂ := Nat.factorial a

-- Complex-valued pochhammer
noncomputable def ph (x : ℂ) (a : ℕ) : ℂ := (ascPochhammer ℂ a).eval x

lemma fact_is_pos_real (a : ℕ) :
    ∃ r : ℝ, 0 < r ∧ fact a = (r : ℂ) := by
  use (Nat.factorial a : ℝ)
  constructor
  · positivity
  · simp [fact]

lemma ph_is_nonneg_real (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ ph (ν : ℂ) a = (r : ℂ) := by
  induction a with
  | zero =>
    use 1
    simp [ph]
  | succ k ih =>
    rcases ih with ⟨r, hr, h_eq⟩
    use r * (ν + k)
    constructor
    · apply mul_nonneg hr
      positivity
    · have ph_succ : ph (ν : ℂ) (k + 1) = ph (ν : ℂ) k * (ν + k) := by
        rw [ph, ph, ascPochhammer_succ_eval]
      rw [ph_succ, h_eq]
      push_cast
      rfl

noncomputable def geg_two_var_coeff (ν : ℂ) (j : ℕ) (a : ℕ) : ℂ :=
    ph ν a * ph ν (j-a) / fact a / fact (j - a)

noncomputable def geg_two_var_sum (ν ρ1 ρ2 : ℂ) (j : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (j + 1),
    geg_two_var_coeff ν j a * ρ1 ^ a * ρ2 ^ (j - a)

theorem geg_two_var_explicit (ν ρ1 ρ2 : ℂ) (j : ℕ) (h1 : ρ1 ≠ 0) (h2 : ρ2 ≠ 0) :
  (ρ1 * ρ2) ^ j * (gegenbauer ν j).eval ((ρ1 / ρ2 + ρ2 / ρ1) / 2) =
    geg_two_var_sum ν (ρ1 ^ 2) (ρ2 ^ 2) j := by
  dsimp [geg_two_var_sum]
  induction j using gegenbauer.induct with
  | case1 => -- j = 0
    rw [gegenbauer, eval_C, Finset.range_one, Finset.sum_singleton, geg_two_var_coeff, fact, ph]
    simp
  | case2 => -- j = 1
    rw [gegenbauer, eval_mul, eval_X, eval_C]
    rw [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton]
    repeat rw [geg_two_var_coeff]
    repeat rw [fact]
    repeat rw [ph]
    simp
    field_simp
    ring
  | case3 j ih1 ih2 => -- j ≥ 2
    rw [gegenbauer]
    rw [eval_sub, eval_mul, eval_C, eval_mul, eval_X, eval_mul, eval_C]
    set geg1 := eval ((ρ1 / ρ2 + ρ2 / ρ1) / 2) (gegenbauer ν j) with hg1
    set geg2 := eval ((ρ1 / ρ2 + ρ2 / ρ1) / 2) (gegenbauer ν (j + 1)) with hg2
    have h_pow1 : (ρ1 * ρ2) ^ j.succ.succ = (ρ1 * ρ2) * (ρ1 * ρ2) ^ (j + 1) := by
        rw [pow_succ]; ring
    have h_pow2 : (ρ1 * ρ2) ^ j.succ.succ = (ρ1 * ρ2) ^ 2 * (ρ1 * ρ2) ^ j := by
        rw [pow_succ]; ring
    rw [mul_sub, h_pow1]
    set c1 := 2 * (↑j + ν + 1) / (↑j + 2)
    set c2 := (↑j + 2 * ν) / (↑j + 2)
    calc
        ρ1 * ρ2 * (ρ1 * ρ2) ^ (j + 1) * ((ρ1 / ρ2 + ρ2 / ρ1) / 2 * geg2 * c1) - ρ1 * ρ2 * (ρ1 * ρ2) ^ (j + 1) * (geg1 * c2)
        _ = ρ1 * ρ2 * ((ρ1 * ρ2) ^ (j + 1) *  geg2) * ((ρ1 / ρ2 + ρ2 / ρ1) / 2 * c1) - ρ1 ^ 2 * ρ2 ^ 2 * ((ρ1 * ρ2) ^ j * geg1) * c2 := by ring
    rw [ih1, ih2]
    repeat rw [Finset.mul_sum]
    repeat rw [Finset.sum_mul]
    ring_nf
    rw [Finset.sum_add_distrib]
    field_simp
    simp
    ring_nf
    have hs : 2 + j = 1 + j + 1 := by ring
    have hs' : 3 + j = 2 + j + 1 := by ring
    nth_rewrite 1 [hs]
    nth_rewrite 1 [hs']
    repeat rw [Finset.sum_range_succ']
    ring_nf
    simp only [tsub_zero, one_div]
    have h3 : ρ2 ^ 2 * ρ2 ^ ((1 + j) * 2) * c1 * geg_two_var_coeff ν (1 + j) 0 * 2⁻¹ =
      ρ2 ^ ((2 + j) * 2) * geg_two_var_coeff ν (2 + j) 0 := by
      ring_nf
      dsimp [c1]
      repeat rw [geg_two_var_coeff]
      repeat rw [fact, ph]
      simp only [ascPochhammer_zero, eval_one, tsub_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
      rw [hs, Nat.factorial_succ, ascPochhammer_succ_eval]
      field_simp
      push_cast
      ring
    rw [h3]
    rw [←sub_eq_zero]
    ring_nf
    repeat rw [hs]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    ring_nf
    have haux : ρ2 ^ ((1 + j - (1 + j)) * 2) = 1 := by grind
    have hauxp : ρ2 ^ ((2 + j - (2 + j)) * 2) = 1 := by grind
    rw [haux, hauxp]
    ring_nf
    have h4 : c1 * geg_two_var_coeff ν (1 + j) (1 + j) * (1 / 2) = geg_two_var_coeff ν (2 + j) (2 + j) := by
      dsimp [c1, c2]
      dsimp [geg_two_var_coeff]
      calc
        2 * (↑j + ν + 1) / (↑j + 2) * (ph ν (1 + j) * ph ν (1 + j - (1 + j)) / fact (1 + j) / fact (1 + j - (1 + j))) * (1 / 2)
        _ =  (↑j + ν + 1) / (↑j + 2) * (ph ν (1 + j) * ph ν (1 + j - (1 + j)) / fact (1 + j) / fact (1 + j - (1 + j))) := by ring
        _ = (↑j + ν + 1) / (↑j + 2) * (ph ν (1 + j) * ph ν 0 / fact (1 + j) / fact 0) := by grind
        _ = (↑j + ν + 1) * ph ν (1 + j) * ph ν 0 / ((2 + ↑j) * fact (1 + j)) / fact 0 := by grind
      symm
      calc
        ph ν (2 + j) * ph ν (2 + j - (2 + j)) / fact (2 + j) / fact (2 + j - (2 + j))
        _ = ph ν (2 + j) * ph ν 0 / fact (2 + j) / fact 0 := by grind
        _ = ph ν (2 + j) * ph ν 0 / fact (1 + j + 1) / fact 0 := by grind
        _ = ph ν (2 + j) * ph ν 0 / ((1 + j + 1) * fact (1 + j)) / fact 0 := by
          rw [fact, Nat.factorial_succ]
          dsimp [fact]
          simp
        _ = ph ν (2 + j) * ph ν 0 / ((2 + j) * fact (1 + j)) / fact 0 := by ring
        _ = ph ν (1 + j + 1) * ph ν 0 / ((2 + j) * fact (1 + j)) / fact 0 := by grind
        _ = (j + ν + 1) * ph ν (1 + j) * ph ν 0 / ((2 + j) * fact (1 + j)) / fact 0 := by
          rw [ph]
          rw [ascPochhammer_succ_eval]
          repeat rw [ph]
          grind
    rw [←h4]
    ring_nf
    rw [←Finset.sum_add_distrib, ←Finset.sum_sub_distrib, ←Finset.sum_sub_distrib]
    rw [Finset.sum_eq_zero]
    intro k kh
    ring_nf
    have h5 : (1 + j - (1 + k)) * 2 = (j - k) * 2 := by grind
    have h6 : (1 + j - k) * 2 = (j - k) * 2 + 2 := by grind
    have h7 : (2 + j - (1 + k)) * 2 = (j -  k) * 2 + 2 := by grind
    have h8 : ρ2 ^ 2 * ρ2 ^ ((j - k) * 2) = ρ2 ^ ((j - k) * 2 + 2) := by grind
    rw [h5, h6, h7]
    ring_nf
    have hk_le : k ≤ j := by
      rw [Finset.mem_range] at kh
      omega
    have ph_succ (ν : ℂ) (k : ℕ) : ph ν (k + 1) = ph ν k * (ν + k) := by
      rw [ph, ph, ascPochhammer_succ_eval]
    have fact_succ (k : ℕ) : fact (k + 1) = fact k * (k + 1) := by
      rw [fact, fact, Nat.factorial_succ]
      push_cast
      ring
    have h9 : c1 * geg_two_var_coeff ν (1 + j) (1 + k) * (1 / 2) +
              c1 * geg_two_var_coeff ν (1 + j) k * (1 / 2) -
              c2 * geg_two_var_coeff ν j k =
              geg_two_var_coeff ν (2 + j) (1 + k) := by
      dsimp [c1, c2, geg_two_var_coeff]
      have h1 : 1 + j - (1 + k) = j - k := by omega
      have h2 : 1 + j - k = j - k + 1 := by omega
      have h3 : 2 + j - (1 + k) = j - k + 1 := by omega
      have h4 : 1 + k = k + 1 := by omega
      rw [h1, h2, h3, h4]
      rw [ph_succ ν k, fact_succ k]
      rw [ph_succ ν (j - k), fact_succ (j - k)]
      have h_jk : ((j - k : ℕ) : ℂ) = (j : ℂ) - (k : ℂ) := Nat.cast_sub hk_le
      rw [h_jk]
      have hd1 : (j:ℂ) + 2 ≠ 0 := by
        have h : (j:ℂ) + 2 = ((j + 2 : ℕ) : ℂ) := by push_cast; rfl
        rw [h]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hd2 : (k:ℂ) + 1 ≠ 0 := by
        have h : (k:ℂ) + 1 = ((k + 1 : ℕ) : ℂ) := by push_cast; rfl
        rw [h]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hd3 : (j:ℂ) - (k:ℂ) + 1 ≠ 0 := by
        have h : (j:ℂ) - (k:ℂ) + 1 = ((j - k + 1 : ℕ) : ℂ) := by
          rw [←h_jk]; push_cast; rfl
        rw [h]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hd4 : (fact k : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hd5 : (fact (j - k) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j - k))
      field_simp
      ring_nf
    rw [←h9]
    ring

/-!
Positivity of the coefficients of the two-variable function r^n C_n^{(ν)}(η) with
r = ρ1 ρ2 and η = ((ρ1 / ρ2 + ρ2 / ρ1) / 2.
-/

lemma geg_two_var_coeff_is_nonneg_real (ν : ℝ) (hν : 0 ≤ ν) (j a : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ geg_two_var_coeff (ν : ℂ) j a = (r : ℂ) := by
  rcases ph_is_nonneg_real ν hν a with ⟨r1, hr1, h1⟩
  rcases ph_is_nonneg_real ν hν (j - a) with ⟨r2, hr2, h2⟩
  rcases fact_is_pos_real a with ⟨r3, hr3, h3⟩
  rcases fact_is_pos_real (j - a) with ⟨r4, hr4, h4⟩
  use r1 * r2 / r3 / r4
  constructor
  · positivity
  · dsimp [geg_two_var_coeff]
    rw [h1, h2, h3, h4]
    push_cast
    rfl

lemma geg_two_var_coeff_nonneg (ν : ℝ) (hν : 0 ≤ ν) (j a : ℕ) :
    0 ≤ (geg_two_var_coeff (ν : ℂ) j a).re ∧ (geg_two_var_coeff (ν : ℂ) j a).im = 0 := by
  rcases geg_two_var_coeff_is_nonneg_real ν hν j a with ⟨r, hr, h_eq⟩
  rw [h_eq]
  simp [hr]

/-!
Positivity of the coefficients allows for the following inequalities.
-/

-- inequality for a single coefficient
lemma norm_term_eq_re (ν : ℝ) (hν : 0 ≤ ν) (ρl ρr : ℂ) (j a : ℕ) :
    ‖geg_two_var_coeff (ν : ℂ) j a * ρl ^ a * ρr ^ (j - a)‖ =
    (geg_two_var_coeff (ν : ℂ) j a * (norm ρl : ℂ) ^ a * (norm ρr : ℂ) ^ (j - a)).re := by
  rcases geg_two_var_coeff_is_nonneg_real ν hν j a with ⟨c, hc, hc_eq⟩
  rw [hc_eq]
  simp only [norm_mul, norm_pow]
  have hc_abs : ‖(c : ℂ)‖ = c := by
    have h1 : ‖(c : ℂ)‖ = ‖c‖ := by simp
    rw [h1]
    exact abs_of_nonneg hc
  rw [hc_abs]
  have H : (↑c * (↑‖ρl‖ : ℂ) ^ a * (↑‖ρr‖ : ℂ) ^ (j - a)) = ((c * ‖ρl‖ ^ a * ‖ρr‖ ^ (j - a) : ℝ) : ℂ) := by push_cast; rfl
  rw [H, Complex.ofReal_re]

-- inequality for the sum
-- lemma geg_two_var_sum_le_max_R (ν : ℝ) (hν : 0 ≤ ν) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (j : ℕ) :
--     (geg_two_var_sum (ν : ℂ) (x : ℂ) (y : ℂ) j).re ≤
--     (max x y) ^ j * (geg_two_var_sum (ν : ℂ) (1 : ℂ) (1 : ℂ) j).re := by
--   dsimp [geg_two_var_sum]
--   rw [re_sum, re_sum, Finset.mul_sum]
--   apply Finset.sum_le_sum
--   intro a ha
--   have h_coeff := geg_two_var_coeff_nonneg ν hν j a
--   have h_coeff_re : 0 ≤ (geg_two_var_coeff (ν : ℂ) j a).re := h_coeff.1
--   have h_coeff_im : (geg_two_var_coeff (ν : ℂ) j a).im = 0 := h_coeff.2

--   have h_term_re : ((geg_two_var_coeff (ν : ℂ) j a) * (x : ℂ) ^ a * (y : ℂ) ^ (j - a)).re =
--       (geg_two_var_coeff (ν : ℂ) j a).re * x ^ a * y ^ (j - a) := by
--     have hx_re : ((x : ℂ) ^ a).re = x ^ a := by rw [←ofReal_pow, ofReal_re]
--     have hx_im : ((x : ℂ) ^ a).im = 0 := by rw [←ofReal_pow, ofReal_im]
--     have hy_re : ((y : ℂ) ^ (j - a)).re = y ^ (j - a) := by rw [←ofReal_pow, ofReal_re]
--     have hy_im : ((y : ℂ) ^ (j - a)).im = 0 := by rw [←ofReal_pow, ofReal_im]
--     have hp1 : ((geg_two_var_coeff (ν : ℂ) j a) * (x : ℂ) ^ a).re = (geg_two_var_coeff (ν : ℂ) j a).re * x ^ a := by
--       rw [mul_re, hx_re, hx_im, h_coeff_im, mul_zero, sub_zero]
--     have hp2 : ((geg_two_var_coeff (ν : ℂ) j a) * (x : ℂ) ^ a).im = 0 := by
--       rw [mul_im, hx_im, h_coeff_im, mul_zero, zero_mul, add_zero]
--     rw [mul_re, hy_re, hy_im, hp1, hp2, mul_zero, sub_zero]

--   have h_term1_re : ((geg_two_var_coeff (ν : ℂ) j a) * (1 : ℂ) ^ a * (1 : ℂ) ^ (j - a)).re =
--       (geg_two_var_coeff (ν : ℂ) j a).re := by
--     have hx_re : ((1 : ℂ) ^ a).re = 1 := by simp
--     have hx_im : ((1 : ℂ) ^ a).im = 0 := by simp
--     have hy_re : ((1 : ℂ) ^ (j - a)).re = 1 := by simp
--     have hy_im : ((1 : ℂ) ^ (j - a)).im = 0 := by simp
--     have hp1 : ((geg_two_var_coeff (ν : ℂ) j a) * (1 : ℂ) ^ a).re = (geg_two_var_coeff (ν : ℂ) j a).re * 1 := by
--       rw [mul_re, hx_re, hx_im, h_coeff_im, mul_zero, sub_zero]
--     have hp2 : ((geg_two_var_coeff (ν : ℂ) j a) * (1 : ℂ) ^ a).im = 0 := by
--       rw [mul_im, hx_im, h_coeff_im, mul_zero, zero_mul, add_zero]
--     rw [mul_re, hy_re, hy_im, hp1, hp2, mul_zero, sub_zero, mul_one, mul_one]

--   rw [h_term_re, h_term1_re]

--   have h_pl : x ^ a ≤ (max x y) ^ a := pow_le_pow_left₀ hx (le_max_left x y) a
--   have h_pr : y ^ (j - a) ≤ (max x y) ^ (j - a) := pow_le_pow_left₀ hy (le_max_right x y) (j - a)

--   have h_prod : x ^ a * y ^ (j - a) ≤ (max x y) ^ a * (max x y) ^ (j - a) := by
--     exact mul_le_mul h_pl h_pr (pow_nonneg hy _) (pow_nonneg (le_trans hx (le_max_left x y)) _)

--   have h_pow_add : (max x y) ^ a * (max x y) ^ (j - a) = (max x y) ^ j := by
--     rw [←pow_add]
--     have ha_lt : a < j + 1 := Finset.mem_range.mp ha
--     have ha_le : a ≤ j := Nat.lt_succ_iff.mp ha_lt
--     rw [Nat.add_sub_of_le ha_le]

--   rw [h_pow_add] at h_prod

--   have h_bound : (geg_two_var_coeff (ν : ℂ) j a).re * x ^ a * y ^ (j - a) ≤
--       (geg_two_var_coeff (ν : ℂ) j a).re * (max x y) ^ j := by
--     calc
--       (geg_two_var_coeff (ν : ℂ) j a).re * x ^ a * y ^ (j - a) =
--       (geg_two_var_coeff (ν : ℂ) j a).re * (x ^ a * y ^ (j - a)) := by ring
--       _ ≤ (geg_two_var_coeff (ν : ℂ) j a).re * (max x y) ^ j := mul_le_mul_of_nonneg_left h_prod h_coeff_re

--   have h_comm : (geg_two_var_coeff (ν : ℂ) j a).re * (max x y) ^ j =
--       (max x y) ^ j * (geg_two_var_coeff (ν : ℂ) j a).re := mul_comm _ _
--   rw [h_comm] at h_bound
--   exact h_bound

lemma norm_geg_two_var_sum_le (ν : ℝ) (hν : 0 ≤ ν) (ρl ρr : ℂ) (j : ℕ) :
    ‖geg_two_var_sum (ν : ℂ) ρl ρr j‖ ≤ (geg_two_var_sum (ν : ℂ) (norm ρl) (norm ρr) j).re := by
  dsimp [geg_two_var_sum]
  have h1 : ‖∑ a ∈ Finset.range (j + 1), geg_two_var_coeff (↑ν) j a * ρl ^ a * ρr ^ (j - a)‖
      ≤ ∑ a ∈ Finset.range (j + 1), ‖geg_two_var_coeff (↑ν) j a * ρl ^ a * ρr ^ (j - a)‖ := norm_sum_le _ _
  have h2 : ∑ a ∈ Finset.range (j + 1), ‖geg_two_var_coeff (↑ν) j a * ρl ^ a * ρr ^ (j - a)‖
      = ∑ a ∈ Finset.range (j + 1), (geg_two_var_coeff (↑ν) j a * (↑‖ρl‖) ^ a * (↑‖ρr‖) ^ (j - a)).re := by
    apply Finset.sum_congr rfl
    intro x _
    rw [norm_term_eq_re ν hν ρl ρr j x]
  have h3 : ∑ a ∈ Finset.range (j + 1), (geg_two_var_coeff (↑ν) j a * (↑‖ρl‖) ^ a * (↑‖ρr‖) ^ (j - a)).re
      = (∑ a ∈ Finset.range (j + 1), geg_two_var_coeff (↑ν) j a * (↑‖ρl‖) ^ a * (↑‖ρr‖) ^ (j - a)).re := by
    simp
  linarith

/-- Specialization of `geg_two_var_explicit` to the Euclidean section $(\rho_l, \rho_r) = (\rho, \bar{\rho})$. -/
theorem geg_two_var_conj (ν ρ : ℂ) (j : ℕ) :
    (‖ρ‖ : ℂ) ^ j * (gegenbauer ν j).eval (Real.cos ρ.arg : ℂ) =
      geg_two_var_sum ν ρ (conj ρ) j := by
  by_cases hρ : ρ = 0
  · subst hρ
    cases j with
    | zero =>
      simp [geg_two_var_sum, geg_two_var_coeff, gegenbauer, ph, fact]
    | succ j =>
      dsimp [geg_two_var_sum]
      rw [norm_zero, ofReal_zero, zero_pow (Nat.succ_ne_zero j), zero_mul, map_zero, eq_comm]
      refine Finset.sum_eq_zero fun a ha => ?_
      by_cases ha0 : a = 0
      · subst ha0
        simp [zero_pow (Nat.succ_ne_zero j)]
      · simp [zero_pow ha0]
  · set r : ℂ := (Real.sqrt ‖ρ‖ : ℂ)
    set e : ℂ := Complex.exp ((ρ.arg / 2 : ℝ) * I)
    set ρ1 : ℂ := r * e
    set ρ2 : ℂ := r * e⁻¹
    have hr_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
    have hr_ne : r ≠ 0 := by
      simp [r, Real.sqrt_ne_zero'.mpr hr_pos]
    have he_ne : e ≠ 0 := Complex.exp_ne_zero _
    have h1 : ρ1 ≠ 0 := mul_ne_zero hr_ne he_ne
    have h2 : ρ2 ≠ 0 := mul_ne_zero hr_ne (inv_ne_zero he_ne)
    have hr2 : r ^ 2 = (‖ρ‖ : ℂ) := by
      change (Real.sqrt ‖ρ‖ : ℂ) ^ 2 = (‖ρ‖ : ℂ)
      norm_cast
      exact Real.sq_sqrt hr_pos.le
    have h_prod : ρ1 * ρ2 = (‖ρ‖ : ℂ) := by
      have : ρ1 * ρ2 = r ^ 2 * (e * e⁻¹) := by dsimp [ρ1, ρ2]; ring
      rw [this, mul_inv_cancel₀ he_ne, mul_one, hr2]
    have h_sq_e : e ^ 2 = Complex.exp ((ρ.arg : ℝ) * I) := by
      dsimp [e]
      rw [sq, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h_arg : (ρ1 / ρ2 + ρ2 / ρ1) / 2 = (Real.cos ρ.arg : ℂ) := by
      have hdiv1 : ρ1 / ρ2 = e ^ 2 := by
        dsimp [ρ1, ρ2]
        rw [mul_div_mul_left _ _ hr_ne, div_inv_eq_mul, sq]
      have hdiv2 : ρ2 / ρ1 = (e ^ 2)⁻¹ := by
        rw [← inv_div, hdiv1]
      rw [hdiv1, hdiv2, h_sq_e, ← Complex.exp_neg, ← neg_mul]
      rw [Complex.ofReal_cos, Complex.cos]
    have h_ρ1_sq : ρ1 ^ 2 = ρ := by
      have : ρ1 ^ 2 = r ^ 2 * e ^ 2 := by dsimp [ρ1]; ring
      rw [this, hr2, h_sq_e]
      exact Complex.norm_mul_exp_arg_mul_I ρ
    have h_ρ2_sq : ρ2 ^ 2 = conj ρ := by
      have hconj_r : conj r = r := Complex.conj_ofReal _
      have hconj_e : conj e = e⁻¹ := by
        dsimp [e]
        rw [← Complex.exp_conj, ← Complex.exp_neg]
        congr 1
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      have : ρ2 = conj ρ1 := by
        dsimp [ρ1, ρ2]
        rw [map_mul, hconj_r, hconj_e]
      rw [this, ← map_pow, h_ρ1_sq]
    have h_main := geg_two_var_explicit ν ρ1 ρ2 j h1 h2
    rwa [h_prod, h_arg, h_ρ1_sq, h_ρ2_sq] at h_main

end gegenbauer
