/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlock.ReferencePairing

/-!
# 1D GFF Block Transmutation and $t$-Channel Remainder Derivative Bounds

This file proves the analytic ingredients needed to discharge `HasInnerTransmutedCrossing` from
ordinary crossing symmetry and $s$-channel collinear block agreement:

1. **Exact 1D GFF Collinear Block Coefficients (`gffBlockCoeff`) & Termwise Transmutation**:
   We define the 1D GFF block coefficients $c_m(\Delta_\phi)$ and prove the exact Gamma/Pochhammer
   identity (`gffBlockCoeff_mul_transmuteWeight_eq`), showing that termwise inner transmutation of
   the GFF block series reproduces `crossFactorExactTransmuted Δ_phi w` on `UcDisk`
   (`hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d`).
2. **First and Second Derivatives of `crossFactor` and `crossW`**:
   We compute the exact first and second complex derivatives of `crossFactor Δ_phi` on `UcDisk`
   and of `crossW` on the strip `StripPi`, and prove uniform low-$x$ and high-$x$ norm bounds.
3. **Untransmuted $t$-Channel Remainder `tChannelRemainder` & Endpoint Derivative Bounds**:
   For $R(z) = \mathcal{G}(w_l, z) - \operatorname{crossIdentity}(\Delta_\phi, w_l, z)$, we prove
   holomorphy on `UcDisk`, uniform low-$x$ ($x \in (0, 1/2]$) and high-$x$ ($x \in (1/2, 1)$)
   first- and second-derivative bounds, and integrability of the inner-transmutation integrand.
4. **Commutation of `transmuteOpInner` with the $s$-Channel Collinear Expansion**:
   We prove that `transmuteOpInner` commutes with the $s$-channel sum and integral over
   `evalCollinear` (`transmuteOpInner_evalCollinear`).
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal ComplexConjugate

/-! ## Section 1: 1D GFF Collinear Block Coefficients & Termwise Transmutation -/

/-- The prefactor $\frac{\Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2} 4^{\Delta_\phi}$ of the
transmuted $t$-channel identity factor `crossFactorTransmuted`. -/
noncomputable def transmutedCrossFactorCoeff (Δ_phi : ℝ) : ℝ :=
  Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi

/-- Legendre duplication identity in ratio form: for $s > 0$,
$$\frac{\Gamma(s + 1/2)}{\Gamma(s)} = \sqrt{\pi} \, 4^{-s} \, \frac{\Gamma(2s + 1)}{s \, \Gamma(s)^2}.$$ -/
lemma Gamma_add_half_div_Gamma_eq {s : ℝ} (hs : 0 < s) :
    Real.Gamma (s + 1 / 2) / Real.Gamma s =
      Real.sqrt π * (4 : ℝ) ^ (-s) * Real.Gamma (2 * s + 1) / (s * (Real.Gamma s) ^ 2) := by
  have hG : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hs_ne : s ≠ 0 := hs.ne'
  have h2s_ne : 2 * s ≠ 0 := by positivity
  have h_dup := Real.Gamma_mul_Gamma_add_half s
  have h_G2s1 : Real.Gamma (2 * s + 1) = 2 * s * Real.Gamma (2 * s) := by
    rw [Real.Gamma_add_one h2s_ne]
  have h_pow : (2 : ℝ) ^ (1 - 2 * s) = 2 * (4 : ℝ) ^ (-s) := by
    have h4 : (4 : ℝ) ^ (-s) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-s) := by norm_num
    rw [h4, ← Real.rpow_mul (by norm_num), sub_eq_add_neg, Real.rpow_add (by norm_num),
      Real.rpow_one]
    congr 2
    ring
  rw [div_eq_div_iff hG (mul_ne_zero hs_ne (pow_ne_zero 2 hG))]
  calc
    Real.Gamma (s + 1 / 2) * (s * Real.Gamma s ^ 2)
      = (Real.Gamma s * Real.Gamma (s + 1 / 2)) * (s * Real.Gamma s) := by ring
    _ = (Real.Gamma (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * Real.sqrt π) * (s * Real.Gamma s) := by
        rw [h_dup]
    _ = Real.sqrt π * (4 : ℝ) ^ (-s) * (2 * s * Real.Gamma (2 * s)) * Real.Gamma s := by
        rw [h_pow]; ring
    _ = Real.sqrt π * (4 : ℝ) ^ (-s) * Real.Gamma (2 * s + 1) * Real.Gamma s := by
        rw [h_G2s1]

/-- **Exact Transmutation Weight Identity for GFF Block Coefficients**:
For all $\Delta_\phi > 0$ and $m \in \mathbb{N}$,
$$
\operatorname{gffBlockCoeff}(\Delta_\phi, m) \, \operatorname{transmuteWeight}(\Delta_\phi + m)
  = \operatorname{transmutedCrossFactorCoeff}(\Delta_\phi) \,
    \operatorname{exactTransmutedPochhammer}(\Delta_\phi, m).
$$ -/
theorem gffBlockCoeff_mul_transmuteWeight_eq {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (m : ℕ) :
    gffBlockCoeff Δ_phi m * transmuteWeight (Δ_phi + (m : ℝ)) =
      transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi m := by
  have hGΔ : Real.Gamma Δ_phi ≠ 0 := (Real.Gamma_pos_of_pos hΔ).ne'
  have hΔ_ne : Δ_phi ≠ 0 := hΔ.ne'
  have h_sqrt_ne : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  cases m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, gffBlockCoeff_zero, exactTransmutedPochhammer_zero]
    unfold transmuteWeight transmutedCrossFactorCoeff
    have h_ratio := Gamma_add_half_div_Gamma_eq hΔ
    have h_tw :
        (Δ_phi - 1 / 2) * Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi =
          (Δ_phi - 1 / 2) * (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi) := by
      ring
    rw [h_tw, h_ratio]
    have h4_split : (4 : ℝ) ^ (2 * Δ_phi) * (4 : ℝ) ^ (-Δ_phi) = (4 : ℝ) ^ Δ_phi := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1; ring
    have h_lhs :
        (4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π) *
          ((Δ_phi - 1 / 2) *
            (Real.sqrt π * (4 : ℝ) ^ (-Δ_phi) * Real.Gamma (2 * Δ_phi + 1) /
              (Δ_phi * Real.Gamma Δ_phi ^ 2))) =
        ((4 : ℝ) ^ (2 * Δ_phi) * (4 : ℝ) ^ (-Δ_phi)) *
          (Real.sqrt π / (4 * Real.sqrt π)) *
          (Real.Gamma (2 * Δ_phi + 1) / Real.Gamma Δ_phi ^ 2) *
          ((Δ_phi - 1 / 2) / Δ_phi) := by
      ring
    rw [h_lhs, h4_split]
    field_simp [h_sqrt_ne, hΔ_ne, hGΔ]
  | succ k =>
    rw [gffBlockCoeff_succ, exactTransmutedPochhammer_succ hΔ_ne k]
    unfold transmuteWeight transmutedCrossFactorCoeff pochhammerCoeff
    set s : ℝ := Δ_phi + (k : ℝ)
    have hs_pos : 0 < s := by dsimp [s]; positivity
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have h2s_pos : 0 < 2 * Δ_phi + (k : ℝ) := by positivity
    have h_arg_eq : Δ_phi + ((k + 1 : ℕ) : ℝ) = s + 1 := by dsimp [s]; push_cast; ring
    rw [h_arg_eq]
    have h_tw_step :
        (s + 1 - 1 / 2) * Real.Gamma (s + 1 + 1 / 2) / Real.Gamma (s + 1) =
          (s + 1 / 2) ^ 2 / s * (Real.Gamma (s + 1 / 2) / Real.Gamma s) := by
      have h1 : s + 1 + 1 / 2 = (s + 1 / 2) + 1 := by ring
      have h2 : s + 1 - 1 / 2 = s + 1 / 2 := by ring
      have hs_half_ne : s + 1 / 2 ≠ 0 := by positivity
      rw [h1, h2, Real.Gamma_add_one hs_half_ne, Real.Gamma_add_one hs_ne]
      have hGs : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs_pos).ne'
      field_simp [hs_ne, hGs]
    rw [h_tw_step, Gamma_add_half_div_Gamma_eq hs_pos]
    have hGs_eq : Real.Gamma (s + 1) = Real.Gamma Δ_phi * realPochhammer Δ_phi (k + 1) := by
      have h_id := Gamma_add_nat_eq_mul_realPochhammer hΔ (k + 1)
      rwa [h_arg_eq] at h_id
    have hGs_eq' : Real.Gamma s = Real.Gamma Δ_phi * realPochhammer Δ_phi k :=
      Gamma_add_nat_eq_mul_realPochhammer hΔ k
    have h_poch_s : realPochhammer Δ_phi (k + 1) = s * realPochhammer Δ_phi k := by
      rw [realPochhammer_succ]
      dsimp [s]; ring
    have hG2s1 :
        Real.Gamma (2 * s + 1) =
          Real.Gamma (2 * Δ_phi + (k : ℝ)) *
            realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1) := by
      have h_id := Gamma_add_nat_eq_mul_realPochhammer h2s_pos (k + 1)
      have h_2s : 2 * Δ_phi + (k : ℝ) + ((k + 1 : ℕ) : ℝ) = 2 * s + 1 := by
        dsimp [s]; push_cast; ring
      rwa [h_2s] at h_id
    have hG2Δk :
        Real.Gamma (2 * Δ_phi + (k : ℝ)) =
          Real.Gamma (2 * Δ_phi) * realPochhammer (2 * Δ_phi) k :=
      Gamma_add_nat_eq_mul_realPochhammer (by positivity) k
    have hG2Δ1 : Real.Gamma (2 * Δ_phi + 1) = 2 * Δ_phi * Real.Gamma (2 * Δ_phi) :=
      Real.Gamma_add_one (by positivity)
    have h4_k_canc : (4 : ℝ) ^ (k : ℝ) * (4 : ℝ) ^ (-(k : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
    have h4_comb :
        (4 : ℝ) ^ (2 * Δ_phi) * (4 : ℝ) ^ (k + 1) * (4 : ℝ) ^ (-s) =
          4 * (4 : ℝ) ^ Δ_phi := by
      have h1 : (4 : ℝ) ^ (k + 1) = 4 * (4 : ℝ) ^ (k : ℝ) := by
        rw [pow_succ', Real.rpow_natCast]
      have h2 : (4 : ℝ) ^ (-s) = (4 : ℝ) ^ (-Δ_phi) * (4 : ℝ) ^ (-(k : ℝ)) := by
        dsimp [s]
        rw [neg_add, Real.rpow_add (by norm_num)]
      have h3 : (4 : ℝ) ^ (2 * Δ_phi) * (4 : ℝ) ^ (-Δ_phi) = (4 : ℝ) ^ Δ_phi := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1; ring
      rw [h1, h2]
      linear_combination
        (4 : ℝ) * (4 : ℝ) ^ (k : ℝ) * (4 : ℝ) ^ (-(k : ℝ)) * h3 +
          4 * (4 : ℝ) ^ Δ_phi * h4_k_canc
    have h_fact_succ : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast; rfl
    have h_p1_ne : realPochhammer Δ_phi k ≠ 0 := (realPochhammer_pos hΔ k).ne'
    have h_p2_ne : realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1) ≠ 0 :=
      (realPochhammer_pos h2s_pos (k + 1)).ne'
    have h_kf_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h_k1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hGs_eq', h_poch_s, hG2s1, hG2Δk, hG2Δ1, h_fact_succ]
    have h_s_def : Δ_phi + (k : ℝ) + 1 / 2 = s + 1 / 2 := rfl
    rw [h_s_def]
    have h_lhs_pow :
        (4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π) * (4 : ℝ) ^ (k + 1) *
            (s * realPochhammer Δ_phi k) ^ 2 /
            (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) *
              realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1)) *
          ((s + 1 / 2) ^ 2 / s *
            (Real.sqrt π * (4 : ℝ) ^ (-s) *
              (Real.Gamma (2 * Δ_phi) * realPochhammer (2 * Δ_phi) k *
                realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1)) /
              (s * (Real.Gamma Δ_phi * realPochhammer Δ_phi k) ^ 2))) =
        ((4 : ℝ) ^ (2 * Δ_phi) * (4 : ℝ) ^ (k + 1) * (4 : ℝ) ^ (-s)) *
          Real.Gamma (2 * Δ_phi) * (s + 1 / 2) ^ 2 * realPochhammer (2 * Δ_phi) k *
          (Real.sqrt π * s ^ 2 * (realPochhammer Δ_phi k) ^ 2 *
            realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1)) /
          (4 * ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) * (Real.Gamma Δ_phi) ^ 2 *
            (Real.sqrt π * s ^ 2 * (realPochhammer Δ_phi k) ^ 2 *
              realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1))) := by
      ring
    rw [h_lhs_pow, h4_comb]
    field_simp [h_sqrt_ne, hs_ne, h_p1_ne, h_p2_ne, h_kf_ne, h_k1_ne, hGΔ, hΔ_ne]

/-- **Termwise Inner Transmutation of the 1D GFF Block Series**:
For all $\Delta_\phi > 0$ and $w \in \operatorname{UcDisk}$,
$$
\sum_{m=0}^{\infty} c_m(\Delta_\phi) \,
  \operatorname{transmuteOpInner}\bigl(\operatorname{block1d}(\Delta_\phi + m)\bigr)(w)
  = \operatorname{crossFactorExactTransmuted}(\Delta_\phi, w).
$$ -/
theorem hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun m : ℕ =>
        (gffBlockCoeff Δ_phi m : ℂ) *
          transmuteOpInner (block1d (Δ_phi + (m : ℝ))) w)
      (crossFactorExactTransmuted Δ_phi w) := by
  refine (hasSum_crossFactorExactTransmuted Δ_phi hw).congr_fun fun m => ?_
  have hH_pos : 0 < Δ_phi + (m : ℝ) := by positivity
  rw [transmuteOpInner_block1d_of_pos hH_pos hw, ← mul_assoc, ← Complex.ofReal_mul,
    gffBlockCoeff_mul_transmuteWeight_eq hΔ m]
  rfl

/-! ### Subsection 1.2: Uniform Exponential Domination Bounds for `block1d` & Commutation of `transmuteOpInner` with the 1D GFF Block Series -/

/-- For any $p \in \mathbb{N}$, $X \ge 0$, $\sigma < 0$, and $r \le \sigma$,
$$X^p \, e^{X r} \le \left(\frac{2(p + 1)}{-\sigma}\right)^p e^{X (\sigma / 2)}.$$ -/
lemma pow_mul_exp_le_of_re_le (p : ℕ) {X σ r : ℝ} (hX : 0 ≤ X) (hσ : σ < 0) (hr : r ≤ σ) :
    X ^ p * Real.exp (X * r) ≤
      (2 * ((p : ℝ) + 1) / (-σ)) ^ p * Real.exp (X * (σ / 2)) := by
  set c : ℝ := -σ / (2 * ((p : ℝ) + 1))
  have h_neg_pos : 0 < -σ := neg_pos.mpr hσ
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hc_inv : c⁻¹ = 2 * ((p : ℝ) + 1) / (-σ) := by
    dsimp [c]
    rw [inv_div]
  have h_base : X ≤ c⁻¹ * Real.exp (c * X) := by
    have h1 : c * X ≤ Real.exp (c * X) := by
      linarith [Real.add_one_le_exp (c * X)]
    calc
      X = c⁻¹ * (c * X) := by rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
      _ ≤ c⁻¹ * Real.exp (c * X) := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hc_pos).le
  have h_pow : X ^ p ≤ (c⁻¹) ^ p * Real.exp ((p : ℝ) * (c * X)) := by
    calc
      X ^ p ≤ (c⁻¹ * Real.exp (c * X)) ^ p := pow_le_pow_left₀ hX h_base p
      _ = (c⁻¹) ^ p * (Real.exp (c * X)) ^ p := mul_pow _ _ _
      _ = (c⁻¹) ^ p * Real.exp ((p : ℝ) * (c * X)) := by
        rw [← Real.exp_nat_mul]
  have h_pc_le : (p : ℝ) * c ≤ -σ / 2 := by
    dsimp [c]
    have hp_le : (p : ℝ) ≤ (p : ℝ) + 1 := by linarith
    have h_alg :
        (p : ℝ) * (-σ / (2 * ((p : ℝ) + 1))) =
          (-σ / 2) * ((p : ℝ) / ((p : ℝ) + 1)) := by
      have : (p : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [h_alg]
    calc
      (-σ / 2) * ((p : ℝ) / ((p : ℝ) + 1))
        ≤ (-σ / 2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hp_le) (by linarith)
      _ = -σ / 2 := mul_one _
  have h_exp_le : Real.exp ((p : ℝ) * (c * X)) * Real.exp (X * r) ≤ Real.exp (X * (σ / 2)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : (p : ℝ) * (c * X) = ((p : ℝ) * c) * X := by ring
    have h2 : ((p : ℝ) * c) * X ≤ (-σ / 2) * X := mul_le_mul_of_nonneg_right h_pc_le hX
    have h3 : X * r ≤ X * σ := mul_le_mul_of_nonneg_left hr hX
    linarith
  rw [← hc_inv]
  calc
    X ^ p * Real.exp (X * r)
      ≤ ((c⁻¹) ^ p * Real.exp ((p : ℝ) * (c * X))) * Real.exp (X * r) :=
        mul_le_mul_of_nonneg_right h_pow (Real.exp_pos _).le
    _ = (c⁻¹) ^ p * (Real.exp ((p : ℝ) * (c * X)) * Real.exp (X * r)) := by ring
    _ ≤ (c⁻¹) ^ p * Real.exp (X * (σ / 2)) :=
        mul_le_mul_of_nonneg_left h_exp_le (by positivity)

/-- Uniform exponential-geometric bound for the $p$-th derivative term of $\operatorname{block1d}(H, z)$
when $H \ge 0$ and $\operatorname{Re} z \le \sigma < 0$. -/
lemma norm_block1dPowTerm_le_exp_half {H : ℝ} (hH : 0 ≤ H) (p : ℕ) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) (n : ℕ) :
    ‖((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p : ℝ) : ℂ) *
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)‖ ≤
      (2 * ((p : ℝ) + 1) / (-σ)) ^ p * Real.exp (H * (σ / 2)) * (Real.exp σ) ^ n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hX : 0 ≤ H + 2 * (n : ℝ) := by positivity
  have h_coeff_nonneg : 0 ≤ block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p :=
    mul_nonneg (block1dCoeff_nonneg hH n) (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h_coeff_nonneg, Complex.norm_exp]
  have hre : (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z).re = (H + 2 * (n : ℝ)) * z.re := by
    simp [Complex.mul_re]
  rw [hre]
  have h_c_le : block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p ≤ (H + 2 * (n : ℝ)) ^ p :=
    mul_le_of_le_one_left (by positivity) (block1dCoeff_le_one hH n)
  have h_pow_exp := pow_mul_exp_le_of_re_le p hX hσ hz
  have h_exp_split :
      Real.exp ((H + 2 * (n : ℝ)) * (σ / 2)) = Real.exp (H * (σ / 2)) * (Real.exp σ) ^ n := by
    have h_alg : (H + 2 * (n : ℝ)) * (σ / 2) = H * (σ / 2) + (n : ℝ) * σ := by ring
    rw [h_alg, Real.exp_add, Real.exp_nat_mul]
  calc
    block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p * Real.exp ((H + 2 * (n : ℝ)) * z.re)
      ≤ (H + 2 * (n : ℝ)) ^ p * Real.exp ((H + 2 * (n : ℝ)) * z.re) :=
        mul_le_mul_of_nonneg_right h_c_le (Real.exp_pos _).le
    _ ≤ (2 * ((p : ℝ) + 1) / (-σ)) ^ p * Real.exp ((H + 2 * (n : ℝ)) * (σ / 2)) := h_pow_exp
    _ = (2 * ((p : ℝ) + 1) / (-σ)) ^ p * Real.exp (H * (σ / 2)) * (Real.exp σ) ^ n := by
        rw [h_exp_split]; ring

/-- Uniform constant $B_p(\sigma) := \bigl(\frac{2(p + 1)}{-\sigma}\bigr)^p (1 - e^\sigma)^{-1}$
bounding the $p$-th derivative of $\operatorname{block1d}(H, z)$ relative to $e^{H(\sigma / 2)}$
on $\operatorname{Re} z \le \sigma < 0$. -/
noncomputable def block1dDerivBoundConst (p : ℕ) (σ : ℝ) : ℝ :=
  (2 * ((p : ℝ) + 1) / (-σ)) ^ p * (1 - Real.exp σ)⁻¹

lemma block1dDerivBoundConst_pos (p : ℕ) {σ : ℝ} (hσ : σ < 0) :
    0 < block1dDerivBoundConst p σ := by
  dsimp [block1dDerivBoundConst]
  have h1 : 0 < -σ := neg_pos.mpr hσ
  have h2 : 0 < 1 - Real.exp σ := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ)
  positivity

lemma block1dDerivBoundConst_nonneg (p : ℕ) {σ : ℝ} (hσ : σ < 0) :
    0 ≤ block1dDerivBoundConst p σ :=
  (block1dDerivBoundConst_pos p hσ).le

/-- Uniform norm bound on `block1d H z` for $H \ge 0$ and $\operatorname{Re} z \le \sigma < 0$:
$$\|\operatorname{block1d}(H, z)\| \le B_0(\sigma) \, e^{H(\sigma / 2)}.$$ -/
theorem norm_block1d_le_exp_half {H : ℝ} (hH : 0 ≤ H) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖block1d H z‖ ≤ block1dDerivBoundConst 0 σ * Real.exp (H * (σ / 2)) := by
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  have hs_norm : Summable (fun n : ℕ => ‖block1dTerm H n z‖) :=
    (summable_block1dTerm hH hz_mem).norm
  have h_geom : HasSum (fun n : ℕ => (Real.exp σ) ^ n) (1 - Real.exp σ)⁻¹ :=
    hasSum_geometric_of_lt_one (Real.exp_pos σ).le (Real.exp_lt_one_iff.mpr hσ)
  have h_dom := h_geom.mul_left ((2 * ((0 : ℝ) + 1) / (-σ)) ^ 0 * Real.exp (H * (σ / 2)))
  calc
    ‖block1d H z‖ ≤ ∑' n : ℕ, ‖block1dTerm H n z‖ := norm_tsum_le_tsum_norm hs_norm
    _ ≤ (2 * ((0 : ℝ) + 1) / (-σ)) ^ 0 * Real.exp (H * (σ / 2)) * (1 - Real.exp σ)⁻¹ := by
        rw [← h_dom.tsum_eq]
        exact hs_norm.tsum_le_tsum
          (fun n => by simpa [block1dTerm] using norm_block1dPowTerm_le_exp_half hH 0 hσ hz n)
          h_dom.summable
    _ = block1dDerivBoundConst 0 σ * Real.exp (H * (σ / 2)) := by
        dsimp [block1dDerivBoundConst]; ring

/-- Uniform norm bound on `deriv (block1d H) z` for $H \ge 0$ and $\operatorname{Re} z \le \sigma < 0$:
$$
\bigl\|\operatorname{deriv}(\operatorname{block1d} H)(z)\bigr\|
  \le B_1(\sigma) \, e^{H(\sigma / 2)}.
$$ -/
theorem norm_deriv_block1d_le_exp_half {H : ℝ} (hH : 0 ≤ H) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖deriv (block1d H) z‖ ≤ block1dDerivBoundConst 1 σ * Real.exp (H * (σ / 2)) := by
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  rw [deriv_block1d hH hz_mem]
  dsimp [block1dDeriv1]
  have hs_norm : Summable (fun n : ℕ => ‖block1dDeriv1Term H n z‖) :=
    (summable_block1dDeriv1Term hH hz_mem).norm
  have h_geom : HasSum (fun n : ℕ => (Real.exp σ) ^ n) (1 - Real.exp σ)⁻¹ :=
    hasSum_geometric_of_lt_one (Real.exp_pos σ).le (Real.exp_lt_one_iff.mpr hσ)
  have h_dom := h_geom.mul_left ((2 * ((1 : ℝ) + 1) / (-σ)) ^ 1 * Real.exp (H * (σ / 2)))
  calc
    ‖∑' n : ℕ, block1dDeriv1Term H n z‖
      ≤ ∑' n : ℕ, ‖block1dDeriv1Term H n z‖ := norm_tsum_le_tsum_norm hs_norm
    _ ≤ (2 * ((1 : ℝ) + 1) / (-σ)) ^ 1 * Real.exp (H * (σ / 2)) * (1 - Real.exp σ)⁻¹ := by
        rw [← h_dom.tsum_eq]
        exact hs_norm.tsum_le_tsum
          (fun n => by
            simpa [block1dDeriv1Term, pow_one] using norm_block1dPowTerm_le_exp_half hH 1 hσ hz n)
          h_dom.summable
    _ = block1dDerivBoundConst 1 σ * Real.exp (H * (σ / 2)) := by
        dsimp [block1dDerivBoundConst]; ring

/-- Uniform norm bound on `deriv (deriv (block1d H)) z` for $H \ge 0$ and
$\operatorname{Re} z \le \sigma < 0$:
$$
\bigl\|\operatorname{deriv}(\operatorname{deriv}(\operatorname{block1d} H))(z)\bigr\|
  \le B_2(\sigma) \, e^{H(\sigma / 2)}.
$$ -/
theorem norm_deriv_deriv_block1d_le_exp_half {H : ℝ} (hH : 0 ≤ H) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖deriv (deriv (block1d H)) z‖ ≤ block1dDerivBoundConst 2 σ * Real.exp (H * (σ / 2)) := by
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  rw [deriv_deriv_block1d hH hz_mem]
  dsimp [block1dDeriv2]
  have hs_norm : Summable (fun n : ℕ => ‖block1dDeriv2Term H n z‖) :=
    (summable_block1dDeriv2Term hH hz_mem).norm
  have h_geom : HasSum (fun n : ℕ => (Real.exp σ) ^ n) (1 - Real.exp σ)⁻¹ :=
    hasSum_geometric_of_lt_one (Real.exp_pos σ).le (Real.exp_lt_one_iff.mpr hσ)
  have h_dom := h_geom.mul_left ((2 * ((2 : ℝ) + 1) / (-σ)) ^ 2 * Real.exp (H * (σ / 2)))
  calc
    ‖∑' n : ℕ, block1dDeriv2Term H n z‖
      ≤ ∑' n : ℕ, ‖block1dDeriv2Term H n z‖ := norm_tsum_le_tsum_norm hs_norm
    _ ≤ (2 * ((2 : ℝ) + 1) / (-σ)) ^ 2 * Real.exp (H * (σ / 2)) * (1 - Real.exp σ)⁻¹ := by
        rw [← h_dom.tsum_eq]
        exact hs_norm.tsum_le_tsum
          (fun n => by
            simpa [block1dDeriv2Term] using norm_block1dPowTerm_le_exp_half hH 2 hσ hz n)
          h_dom.summable
    _ = block1dDerivBoundConst 2 σ * Real.exp (H * (σ / 2)) := by
        dsimp [block1dDerivBoundConst]; ring

/-- General bound on `‖transmuteInnerKernel w s‖` for $w \in \operatorname{UcDisk}$ and
$s \in (0, 1)$. -/
lemma norm_transmuteInnerKernel_le_betaKernel {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖transmuteInnerKernel w s‖ ≤
      (1 - Real.exp (2 * w.re)) ^ (-1 / 2 : ℝ) * betaKernel 1 0 s := by
  have hw_re : w.re < 0 := mem_UcDisk_iff.mp hw
  have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * w.re) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  rw [norm_transmuteInnerKernel_eq hw hs]
  have h_norm_sub : 1 - Real.exp (2 * w.re) ≤ ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp (2 * w))
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
      Complex.norm_exp] at h1
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    rw [hre] at h1
    have h_le : s * Real.exp (2 * w.re) ≤ 1 * Real.exp (2 * w.re) :=
      mul_le_mul_of_nonneg_right hs.2.le (by positivity)
    linarith
  have h_rpow :
      ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤
        (1 - Real.exp (2 * w.re)) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h_1_sub_exp2_pos h_norm_sub (by norm_num)
  have h_bk : s ^ (-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) = betaKernel 1 0 s := by
    dsimp [betaKernel]; congr 2; norm_num
  rw [h_bk, mul_comm]
  exact mul_le_mul_of_nonneg_right h_rpow (betaKernel_nonneg 1 0 hs)

/-- General bound on `‖transmuteInnerDiff f w s‖` from bounds on $\|f'(w + \log s)\|$ and
$\|f''(w + \log s)\|$ for $w \in \operatorname{UcDisk}$ and $s \in (0, 1)$. -/
lemma norm_transmuteInnerDiff_le_of_deriv_le {f : ℂ → ℂ} {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {D1 D2 : ℝ} (_hD1 : 0 ≤ D1) (_hD2 : 0 ≤ D2)
    (hd1_le : ‖deriv f (w + (Real.log s : ℂ))‖ ≤ D1)
    (hd2_le : ‖deriv (deriv f) (w + (Real.log s : ℂ))‖ ≤ D2) :
    ‖transmuteInnerDiff f w s‖ ≤
      4 * (2 / (1 - Real.exp w.re) * D2 + 2 / (1 - Real.exp w.re) ^ 2 * D1) + 2 * D1 := by
  have hw_re : w.re < 0 := mem_UcDisk_iff.mp hw
  have h_1_sub_exp_pos : 0 < 1 - Real.exp w.re :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hw_re)
  dsimp [transmuteInnerDiff]
  set z : ℂ := w + (Real.log s : ℂ)
  have h_sub_ge : 1 - Real.exp w.re ≤ ‖1 - (s : ℂ) * Complex.exp w‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp w)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
      Complex.norm_exp] at h1
    have h_le : s * Real.exp w.re ≤ 1 * Real.exp w.re :=
      mul_le_mul_of_nonneg_right hs.2.le (by positivity)
    linarith
  have h_exp_le1 : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw_re.le
  have h_s_exp_le1 : ‖(s : ℂ) * Complex.exp w‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2.le).trans h_exp_le1
  have h_1_sub_w_le2 : ‖1 - Complex.exp w‖ ≤ 2 := by
    have h1 := norm_sub_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h1; linarith
  have h_1_add_w_le2 : ‖1 + Complex.exp w‖ ≤ 2 := by
    have h1 := norm_add_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h1; linarith
  have h_1_add_sw_le2 : ‖1 + (s : ℂ) * Complex.exp w‖ ≤ 2 := by
    have h1 := norm_add_le (1 : ℂ) ((s : ℂ) * Complex.exp w)
    rw [norm_one] at h1; linarith
  have h_rat1_le : ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)‖ ≤
      2 / (1 - Real.exp w.re) := by
    rw [norm_div]
    exact div_le_div₀ (by norm_num) h_1_add_sw_le2 h_1_sub_exp_pos h_sub_ge
  have h_rat2_le :
      ‖2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2‖ ≤
        2 / (1 - Real.exp w.re) ^ 2 := by
    rw [mul_assoc, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have h_num : 2 * ‖(s : ℂ) * Complex.exp w‖ ≤ 2 := by linarith
    have h_den : (1 - Real.exp w.re) ^ 2 ≤ ‖1 - (s : ℂ) * Complex.exp w‖ ^ 2 :=
      pow_le_pow_left₀ h_1_sub_exp_pos.le h_sub_ge 2
    exact div_le_div₀ (by norm_num) h_num (sq_pos_of_pos h_1_sub_exp_pos) h_den
  have h_sq1 : ‖(1 - Complex.exp w) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h_1_sub_w_le2 2
  have h_sq2 : ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2‖ ≤ 2 := by
    have h_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [norm_mul, norm_pow, h_half]
    have h_pow : ‖1 + Complex.exp w‖ ^ 2 ≤ 2 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_1_add_w_le2 2
    linarith
  have h_p1 :
      ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
          deriv (deriv f) z +
        2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2 *
          deriv f z‖ ≤
      2 / (1 - Real.exp w.re) * D2 + 2 / (1 - Real.exp w.re) ^ 2 * D1 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul h_rat1_le hd2_le (norm_nonneg _) (by positivity)
    · rw [norm_mul]
      exact mul_le_mul h_rat2_le hd1_le (norm_nonneg _) (by positivity)
  have h_p2 :
      ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z‖ ≤ 2 * D1 := by
    rw [norm_mul]
    exact mul_le_mul h_sq2 hd1_le (norm_nonneg _) (by norm_num)
  refine (norm_sub_le _ _).trans (add_le_add ?_ h_p2)
  rw [norm_mul]
  exact mul_le_mul h_sq1 h_p1 (norm_nonneg _) (by norm_num)

/-- $H$- and $s$-independent constant $C_{\mathrm{inner}}(\sigma)$ dominating
$\|\operatorname{transmuteInnerKernel}(w, s) \, \operatorname{transmuteInnerDiff}(\operatorname{block1d} H, w, s)\|$
relative to $e^{H(\sigma / 2)} \operatorname{betaKernel}(1, 0, s)$ for $\sigma = \operatorname{Re} w < 0$. -/
noncomputable def block1dInnerDomConst (σ : ℝ) : ℝ :=
  (1 - Real.exp (2 * σ)) ^ (-1 / 2 : ℝ) *
    (4 * (2 / (1 - Real.exp σ) * block1dDerivBoundConst 2 σ +
      2 / (1 - Real.exp σ) ^ 2 * block1dDerivBoundConst 1 σ) +
      2 * block1dDerivBoundConst 1 σ)

lemma block1dInnerDomConst_nonneg {σ : ℝ} (hσ : σ < 0) :
    0 ≤ block1dInnerDomConst σ := by
  dsimp [block1dInnerDomConst]
  have h1 : 0 < 1 - Real.exp σ := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ)
  have h2 : 0 < 1 - Real.exp (2 * σ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hB1 := block1dDerivBoundConst_nonneg 1 hσ
  have hB2 := block1dDerivBoundConst_nonneg 2 hσ
  positivity

/-- **Uniform Domination of `transmuteInnerKernel * transmuteInnerDiff (block1d H)`**:
For all $H \ge 0$, $w \in \operatorname{UcDisk}$, and $s \in (0, 1)$,
$$
\bigl\|\operatorname{transmuteInnerKernel}(w, s) \,
  \operatorname{transmuteInnerDiff}(\operatorname{block1d} H, w, s)\bigr\|
  \le \operatorname{block1dInnerDomConst}(\operatorname{Re} w) \,
    e^{H (\operatorname{Re} w / 2)} \, \operatorname{betaKernel}(1, 0, s).
$$ -/
theorem norm_transmuteInner_block1d_le {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s‖ ≤
      block1dInnerDomConst w.re * Real.exp (H * (w.re / 2)) * betaKernel 1 0 s := by
  have hw_re : w.re < 0 := mem_UcDisk_iff.mp hw
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz_le : (w + (Real.log s : ℂ)).re ≤ w.re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hd1 := norm_deriv_block1d_le_exp_half hH hw_re hz_le
  have hd2 := norm_deriv_deriv_block1d_le_exp_half hH hw_re hz_le
  have hD1 : 0 ≤ block1dDerivBoundConst 1 w.re * Real.exp (H * (w.re / 2)) :=
    mul_nonneg (block1dDerivBoundConst_nonneg 1 hw_re) (Real.exp_pos _).le
  have hD2 : 0 ≤ block1dDerivBoundConst 2 w.re * Real.exp (H * (w.re / 2)) :=
    mul_nonneg (block1dDerivBoundConst_nonneg 2 hw_re) (Real.exp_pos _).le
  have h_diff := norm_transmuteInnerDiff_le_of_deriv_le hw hs hD1 hD2 hd1 hd2
  have h_k := norm_transmuteInnerKernel_le_betaKernel hw hs
  have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * w.re) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  rw [norm_mul]
  calc
    ‖transmuteInnerKernel w s‖ * ‖transmuteInnerDiff (block1d H) w s‖
      ≤ ((1 - Real.exp (2 * w.re)) ^ (-1 / 2 : ℝ) * betaKernel 1 0 s) *
          (4 * (2 / (1 - Real.exp w.re) * (block1dDerivBoundConst 2 w.re * Real.exp (H * (w.re / 2))) +
            2 / (1 - Real.exp w.re) ^ 2 * (block1dDerivBoundConst 1 w.re * Real.exp (H * (w.re / 2)))) +
            2 * (block1dDerivBoundConst 1 w.re * Real.exp (H * (w.re / 2)))) :=
        mul_le_mul h_k h_diff (norm_nonneg _)
          (mul_nonneg (by positivity) (betaKernel_nonneg 1 0 hs))
    _ = block1dInnerDomConst w.re * Real.exp (H * (w.re / 2)) * betaKernel 1 0 s := by
        dsimp [block1dInnerDomConst]; ring

/-- Lower bound on `transmuteWeight (Δ_phi + (k + 1 : ℕ))` for $\Delta_\phi > 0$ and $k \in \mathbb{N}$:
$$
\frac{1}{2} \frac{\Gamma(\Delta_\phi + 1/2)}{\Gamma(\Delta_\phi)}
  \le \operatorname{transmuteWeight}\bigl(\Delta_\phi + (k + 1 : \mathbb{N})\bigr).
$$ -/
lemma transmuteWeight_add_nat_succ_ge {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k : ℕ) :
    (1 / 2 : ℝ) * (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi) ≤
      transmuteWeight (Δ_phi + ((k + 1 : ℕ) : ℝ)) := by
  unfold transmuteWeight
  have hΔ_half : 0 < Δ_phi + 1 / 2 := by linarith
  have hG1 :
      Real.Gamma (Δ_phi + ((k + 1 : ℕ) : ℝ) + 1 / 2) =
        Real.Gamma (Δ_phi + 1 / 2) * realPochhammer (Δ_phi + 1 / 2) (k + 1) := by
    have h_eq : Δ_phi + ((k + 1 : ℕ) : ℝ) + 1 / 2 = (Δ_phi + 1 / 2) + ((k + 1 : ℕ) : ℝ) := by
      ring
    rw [h_eq, Gamma_add_nat_eq_mul_realPochhammer hΔ_half (k + 1)]
  have hG2 :
      Real.Gamma (Δ_phi + ((k + 1 : ℕ) : ℝ)) =
        Real.Gamma Δ_phi * realPochhammer Δ_phi (k + 1) :=
    Gamma_add_nat_eq_mul_realPochhammer hΔ (k + 1)
  rw [hG1, hG2]
  have h_poch_pos : 0 < realPochhammer Δ_phi (k + 1) := realPochhammer_pos hΔ (k + 1)
  have h_poch_le : realPochhammer Δ_phi (k + 1) ≤ realPochhammer (Δ_phi + 1 / 2) (k + 1) :=
    realPochhammer_mono hΔ.le (by linarith) (k + 1)
  have h_poch_ratio : 1 ≤ realPochhammer (Δ_phi + 1 / 2) (k + 1) / realPochhammer Δ_phi (k + 1) :=
    (one_le_div h_poch_pos).mpr h_poch_le
  have h_ge_half : (1 / 2 : ℝ) ≤ Δ_phi + ((k + 1 : ℕ) : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    linarith
  have h_ratio_pos : 0 < Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi :=
    div_pos (Real.Gamma_pos_of_pos hΔ_half) (Real.Gamma_pos_of_pos hΔ)
  calc
    (1 / 2 : ℝ) * (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi)
      = (1 / 2 : ℝ) * (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi) * 1 := (mul_one _).symm
    _ ≤ (Δ_phi + ((k + 1 : ℕ) : ℝ) - 1 / 2) *
          (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi) *
          (realPochhammer (Δ_phi + 1 / 2) (k + 1) / realPochhammer Δ_phi (k + 1)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right h_ge_half h_ratio_pos.le)
          h_poch_ratio zero_le_one (by positivity)
    _ = (Δ_phi + ((k + 1 : ℕ) : ℝ) - 1 / 2) *
          (Real.Gamma (Δ_phi + 1 / 2) * realPochhammer (Δ_phi + 1 / 2) (k + 1)) /
          (Real.Gamma Δ_phi * realPochhammer Δ_phi (k + 1)) := by ring

/-- Summability of `gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + m) * σ)` for all $\Delta_\phi > 0$
and $\sigma < 0$. -/
theorem summable_gffBlockCoeff_mul_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {σ : ℝ} (hσ : σ < 0) :
    Summable (fun m : ℕ => gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * σ)) := by
  rw [← summable_nat_add_iff 1]
  have hσ_mem : (σ : ℂ) ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa using hσ
  have h_sum_exact :
      Summable (fun m : ℕ =>
        ‖((transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi m : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * (σ : ℂ))‖) := by
    simpa [transmutedCrossFactorCoeff] using
      (hasSum_crossFactorExactTransmuted Δ_phi hσ_mem).summable.norm
  have h_sum_shift := (summable_nat_add_iff 1).mpr h_sum_exact
  set c_low : ℝ := (1 / 2 : ℝ) * (Real.Gamma (Δ_phi + 1 / 2) / Real.Gamma Δ_phi)
  have hc_low_pos : 0 < c_low := by
    dsimp [c_low]
    exact mul_pos (by norm_num)
      (div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos hΔ))
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (gffBlockCoeff_nonneg hΔ (k + 1)) (Real.exp_pos _).le)
    (fun k => ?_) (h_sum_shift.mul_left c_low⁻¹)
  have h_tw_ge := transmuteWeight_add_nat_succ_ge hΔ k
  have h_id := gffBlockCoeff_mul_transmuteWeight_eq hΔ (k + 1)
  have h_coeff_pos : 0 < transmutedCrossFactorCoeff Δ_phi := by
    dsimp [transmutedCrossFactorCoeff]
    exact mul_pos
      (div_pos (Real.Gamma_pos_of_pos (by linarith)) (sq_pos_of_pos (Real.Gamma_pos_of_pos hΔ)))
      (by positivity)
  have h_poch_pos : 0 < exactTransmutedPochhammer Δ_phi (k + 1) :=
    exactTransmutedPochhammer_pos hΔ (by omega : 1 ≤ k + 1)
  have h_prod_nonneg :
      0 ≤ transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1) :=
    mul_nonneg h_coeff_pos.le h_poch_pos.le
  have h_gff_le :
      gffBlockCoeff Δ_phi (k + 1) ≤
        c_low⁻¹ * (transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1)) := by
    have h1 :
        c_low * gffBlockCoeff Δ_phi (k + 1) ≤
          transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1) := by
      calc
        c_low * gffBlockCoeff Δ_phi (k + 1)
          ≤ transmuteWeight (Δ_phi + ((k + 1 : ℕ) : ℝ)) * gffBlockCoeff Δ_phi (k + 1) :=
            mul_le_mul_of_nonneg_right h_tw_ge (gffBlockCoeff_nonneg hΔ (k + 1))
        _ = gffBlockCoeff Δ_phi (k + 1) * transmuteWeight (Δ_phi + ((k + 1 : ℕ) : ℝ)) :=
            mul_comm _ _
        _ = transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1) := h_id
    calc
      gffBlockCoeff Δ_phi (k + 1) = c_low⁻¹ * (c_low * gffBlockCoeff Δ_phi (k + 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc_low_pos.ne', one_mul]
      _ ≤ c_low⁻¹ * (transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1)) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hc_low_pos).le
  have h_norm_eq :
      ‖((transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1) : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (σ : ℂ))‖ =
        (transmutedCrossFactorCoeff Δ_phi * exactTransmutedPochhammer Δ_phi (k + 1)) *
          Real.exp ((Δ_phi + ((k + 1 : ℕ) : ℝ)) * σ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h_prod_nonneg,
      Complex.norm_exp]
    simp [Complex.mul_re]
  rw [h_norm_eq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h_gff_le (Real.exp_pos _).le

/-- Summability of the 1D GFF block series on `UcDisk`. -/
theorem summable_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {z : ℂ} (hz : z ∈ UcDisk) :
    Summable (fun m : ℕ => (gffBlockCoeff Δ_phi m : ℂ) * block1d (Δ_phi + (m : ℝ)) z) := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (summable_gffBlockCoeff_mul_exp hΔ (by linarith : z.re / 2 < 0)).mul_left
    (block1dDerivBoundConst 0 z.re)
  refine Summable.of_norm_bounded h_dom fun m => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
  have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
  calc
    gffBlockCoeff Δ_phi m * ‖block1d (Δ_phi + (m : ℝ)) z‖
      ≤ gffBlockCoeff Δ_phi m *
          (block1dDerivBoundConst 0 z.re * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) :=
        mul_le_mul_of_nonneg_left (norm_block1d_le_exp_half hH hz_re le_rfl)
          (gffBlockCoeff_nonneg hΔ m)
    _ = block1dDerivBoundConst 0 z.re *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) := by ring

/-- Summability of the first-derivative GFF block series on `UcDisk`. -/
theorem summable_gffBlockSeries_deriv1 {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {z : ℂ} (hz : z ∈ UcDisk) :
    Summable (fun m : ℕ =>
      (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) z) := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (summable_gffBlockCoeff_mul_exp hΔ (by linarith : z.re / 2 < 0)).mul_left
    (block1dDerivBoundConst 1 z.re)
  refine Summable.of_norm_bounded h_dom fun m => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
  have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
  calc
    gffBlockCoeff Δ_phi m * ‖deriv (block1d (Δ_phi + (m : ℝ))) z‖
      ≤ gffBlockCoeff Δ_phi m *
          (block1dDerivBoundConst 1 z.re * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) :=
        mul_le_mul_of_nonneg_left (norm_deriv_block1d_le_exp_half hH hz_re le_rfl)
          (gffBlockCoeff_nonneg hΔ m)
    _ = block1dDerivBoundConst 1 z.re *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) := by ring

/-- Term-by-term first derivative of `gffBlockSeries Δ_phi` on `UcDisk`. -/
theorem hasDerivAt_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (gffBlockSeries Δ_phi)
      (∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) z) z := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum := (summable_gffBlockCoeff_mul_exp hΔ (by linarith : z.re / 4 < 0)).mul_left
    (block1dDerivBoundConst 1 (z.re / 2))
  have h_bd : ∀ m : ℕ, ∀ y ∈ t,
      ‖(gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) y‖ ≤
        block1dDerivBoundConst 1 (z.re / 2) *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) := by
    intro m y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
    have hd1 := norm_deriv_block1d_le_exp_half hH (by linarith : z.re / 2 < 0) hy_re
    have h_div : z.re / 2 / 2 = z.re / 4 := by ring
    rw [h_div] at hd1
    calc
      gffBlockCoeff Δ_phi m * ‖deriv (block1d (Δ_phi + (m : ℝ))) y‖
        ≤ gffBlockCoeff Δ_phi m *
            (block1dDerivBoundConst 1 (z.re / 2) * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) :=
          mul_le_mul_of_nonneg_left hd1 (gffBlockCoeff_nonneg hΔ m)
      _ = block1dDerivBoundConst 1 (z.re / 2) *
            (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) := by ring
  exact hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
    (convex_ball z (-z.re / 2)).isPreconnected
    (fun m y hy => by
      have hy_mem : y ∈ UcDisk :=
        mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
      have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
      exact ((hasDerivAt_block1d hH hy_mem).differentiableAt.hasDerivAt).const_mul
        (gffBlockCoeff Δ_phi m : ℂ))
    h_bd (Metric.mem_ball_self hr) (summable_gffBlockSeries hΔ hz) (Metric.mem_ball_self hr)

theorem deriv_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (gffBlockSeries Δ_phi) z =
      ∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) z :=
  (hasDerivAt_gffBlockSeries hΔ hz).deriv

/-- Term-by-term second derivative of `gffBlockSeries Δ_phi` on `UcDisk`. -/
theorem deriv_deriv_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (deriv (gffBlockSeries Δ_phi)) z =
      ∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (deriv (block1d (Δ_phi + (m : ℝ)))) z := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum := (summable_gffBlockCoeff_mul_exp hΔ (by linarith : z.re / 4 < 0)).mul_left
    (block1dDerivBoundConst 2 (z.re / 2))
  have h_bd : ∀ m : ℕ, ∀ y ∈ t,
      ‖(gffBlockCoeff Δ_phi m : ℂ) * deriv (deriv (block1d (Δ_phi + (m : ℝ)))) y‖ ≤
        block1dDerivBoundConst 2 (z.re / 2) *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) := by
    intro m y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
    have hd2 := norm_deriv_deriv_block1d_le_exp_half hH (by linarith : z.re / 2 < 0) hy_re
    have h_div : z.re / 2 / 2 = z.re / 4 := by ring
    rw [h_div] at hd2
    calc
      gffBlockCoeff Δ_phi m * ‖deriv (deriv (block1d (Δ_phi + (m : ℝ)))) y‖
        ≤ gffBlockCoeff Δ_phi m *
            (block1dDerivBoundConst 2 (z.re / 2) * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) :=
          mul_le_mul_of_nonneg_left hd2 (gffBlockCoeff_nonneg hΔ m)
      _ = block1dDerivBoundConst 2 (z.re / 2) *
            (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 4))) := by ring
  have hd_tsum : HasDerivAt
      (fun u : ℂ => ∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) u)
      (∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (deriv (block1d (Δ_phi + (m : ℝ)))) z) z :=
    hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
      (convex_ball z (-z.re / 2)).isPreconnected
      (fun m y hy => by
        have hy_mem : y ∈ UcDisk :=
          mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
        have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
        have h_ev_y : deriv (block1d (Δ_phi + (m : ℝ))) =ᶠ[𝓝 y] block1dDeriv1 (Δ_phi + (m : ℝ)) :=
          Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hy_mem) fun w hw => deriv_block1d hH hw
        have hd_y : HasDerivAt (deriv (block1d (Δ_phi + (m : ℝ))))
            (deriv (deriv (block1d (Δ_phi + (m : ℝ)))) y) y := by
          rw [deriv_deriv_block1d hH hy_mem]
          exact (hasDerivAt_block1dDeriv1 hH hy_mem).congr_of_eventuallyEq h_ev_y
        exact hd_y.const_mul (gffBlockCoeff Δ_phi m : ℂ))
      h_bd (Metric.mem_ball_self hr) (summable_gffBlockSeries_deriv1 hΔ hz) (Metric.mem_ball_self hr)
  have h_ev : deriv (gffBlockSeries Δ_phi) =ᶠ[𝓝 z]
      fun u : ℂ => ∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) u :=
    Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hz) fun u hu => deriv_gffBlockSeries hΔ hu
  rw [h_ev.deriv_eq, hd_tsum.deriv]

/-- Pointwise series expansion of `transmuteInnerKernel w s * transmuteInnerDiff (gffBlockSeries Δ_phi) w s`
for $w \in \operatorname{UcDisk}$ and $s \in (0, 1)$. -/
theorem hasSum_transmuteInner_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {w : ℂ} (hw : w ∈ UcDisk) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum
      (fun m : ℕ =>
        (gffBlockCoeff Δ_phi m : ℂ) *
          (transmuteInnerKernel w s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) w s))
      (transmuteInnerKernel w s * transmuteInnerDiff (gffBlockSeries Δ_phi) w s) := by
  set z : ℂ := w + (Real.log s : ℂ)
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hw]
  have hs1 : HasSum
      (fun m : ℕ => (gffBlockCoeff Δ_phi m : ℂ) * deriv (block1d (Δ_phi + (m : ℝ))) z)
      (deriv (gffBlockSeries Δ_phi) z) := by
    rw [deriv_gffBlockSeries hΔ hz]
    exact (summable_gffBlockSeries_deriv1 hΔ hz).hasSum
  have hs2 : HasSum
      (fun m : ℕ => (gffBlockCoeff Δ_phi m : ℂ) * deriv (deriv (block1d (Δ_phi + (m : ℝ)))) z)
      (deriv (deriv (gffBlockSeries Δ_phi)) z) := by
    rw [deriv_deriv_gffBlockSeries hΔ hz]
    have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
    have h_dom := (summable_gffBlockCoeff_mul_exp hΔ (by linarith : z.re / 2 < 0)).mul_left
      (block1dDerivBoundConst 2 z.re)
    refine (Summable.of_norm_bounded h_dom fun m => ?_).hasSum
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
    have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
    calc
      gffBlockCoeff Δ_phi m * ‖deriv (deriv (block1d (Δ_phi + (m : ℝ)))) z‖
        ≤ gffBlockCoeff Δ_phi m *
            (block1dDerivBoundConst 2 z.re * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) :=
          mul_le_mul_of_nonneg_left (norm_deriv_deriv_block1d_le_exp_half hH hz_re le_rfl)
            (gffBlockCoeff_nonneg hΔ m)
      _ = block1dDerivBoundConst 2 z.re *
            (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (z.re / 2))) := by ring
  set A1 : ℂ :=
    transmuteInnerKernel w s *
      ((1 - Complex.exp w) ^ 2 *
        (2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2) -
        (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2)
  set A2 : ℂ :=
    transmuteInnerKernel w s *
      ((1 - Complex.exp w) ^ 2 *
        ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)))
  have h_comb := (hs2.mul_left A2).add (hs1.mul_left A1)
  have h_rhs :
      A2 * deriv (deriv (gffBlockSeries Δ_phi)) z + A1 * deriv (gffBlockSeries Δ_phi) z =
        transmuteInnerKernel w s * transmuteInnerDiff (gffBlockSeries Δ_phi) w s := by
    dsimp [A1, A2, transmuteInnerDiff]
    change _ =
      transmuteInnerKernel w s *
        ((1 - Complex.exp w) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            deriv (deriv (gffBlockSeries Δ_phi)) z +
            2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2 *
              deriv (gffBlockSeries Δ_phi) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv (gffBlockSeries Δ_phi) z)
    ring
  rw [h_rhs] at h_comb
  refine h_comb.congr_fun fun m => ?_
  dsimp [A1, A2, transmuteInnerDiff]
  change (gffBlockCoeff Δ_phi m : ℂ) *
      (transmuteInnerKernel w s *
        ((1 - Complex.exp w) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            deriv (deriv (block1d (Δ_phi + (m : ℝ)))) z +
            2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2 *
              deriv (block1d (Δ_phi + (m : ℝ))) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv (block1d (Δ_phi + (m : ℝ))) z)) = _
  ring

/-- **Commutation of `transmuteOpInner` ($\mathcal{L}_0$) with the 1D GFF Block Series
(`transmuteOpInner_gffBlockSeries`)**:
For all $\Delta_\phi > 0$ and all $w \in \operatorname{UcDisk}$,
$$
\operatorname{transmuteOpInner}\bigl(\operatorname{gffBlockSeries} \Delta_\phi\bigr)(w)
  = \operatorname{crossFactorExactTransmuted}(\Delta_\phi, w).
$$ -/
theorem transmuteOpInner_gffBlockSeries {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOpInner (gffBlockSeries Δ_phi) w = crossFactorExactTransmuted Δ_phi w := by
  have hw_re : w.re < 0 := mem_UcDisk_iff.mp hw
  set bound : ℕ → ℝ → ℝ := fun m s =>
    (block1dInnerDomConst w.re *
      (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (w.re / 2)))) *
      betaKernel 1 0 s
  have h_sum_m :
      Summable (fun m : ℕ =>
        block1dInnerDomConst w.re *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (w.re / 2)))) :=
    (summable_gffBlockCoeff_mul_exp hΔ (by linarith : w.re / 2 < 0)).mul_left
      (block1dInnerDomConst w.re)
  have h_hasSum_int :
      HasSum
        (fun m : ℕ =>
          ∫ s in Ioo (0 : ℝ) 1,
            (gffBlockCoeff Δ_phi m : ℂ) *
              (transmuteInnerKernel w s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) w s))
        (∫ s in Ioo (0 : ℝ) 1,
          transmuteInnerKernel w s * transmuteInnerDiff (gffBlockSeries Δ_phi) w s) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) bound ?_ ?_ ?_ ?_ ?_
    · intro m
      have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
      exact ((continuousOn_transmuteInner_block1d hH hw).const_mul
        (gffBlockCoeff Δ_phi m : ℂ)).aestronglyMeasurable measurableSet_Ioo
    · intro m
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      dsimp [bound]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
      have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
      calc
        gffBlockCoeff Δ_phi m *
            ‖transmuteInnerKernel w s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) w s‖
          ≤ gffBlockCoeff Δ_phi m *
              (block1dInnerDomConst w.re * Real.exp ((Δ_phi + (m : ℝ)) * (w.re / 2)) *
                betaKernel 1 0 s) :=
            mul_le_mul_of_nonneg_left (norm_transmuteInner_block1d_le hH hw hs)
              (gffBlockCoeff_nonneg hΔ m)
        _ = block1dInnerDomConst w.re *
              (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (w.re / 2))) *
              betaKernel 1 0 s := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s _
      exact h_sum_m.mul_right (betaKernel 1 0 s)
    · have h_tsum :
          (fun s : ℝ => ∑' m : ℕ, bound m s) =
            fun s : ℝ =>
              (∑' m : ℕ,
                block1dInnerDomConst w.re *
                  (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (w.re / 2)))) *
                betaKernel 1 0 s := by
        ext s; dsimp [bound]; exact tsum_mul_right
      rw [h_tsum]
      exact (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hasSum_transmuteInner_gffBlockSeries hΔ hw hs
  have h_scaled := h_hasSum_int.mul_left (((Real.sqrt π : ℝ) : ℂ)⁻¹)
  have h_congr :
      HasSum
        (fun m : ℕ =>
          (gffBlockCoeff Δ_phi m : ℂ) *
            transmuteOpInner (block1d (Δ_phi + (m : ℝ))) w)
        (transmuteOpInner (gffBlockSeries Δ_phi) w) := by
    refine h_scaled.congr_fun fun m => ?_
    dsimp [transmuteOpInner]
    rw [integral_const_mul]
    ring
  exact h_congr.unique (hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d hΔ hw)

/-! ## Section 2: First and Second Derivatives of `crossFactor` and `crossW` -/

/-- The fundamental strip
$\operatorname{StripPi} := \{z \in \operatorname{UcDisk} \mid \operatorname{Im} z \in (-\pi, \pi)\}$
on which `zOfW` and `crossW` are holomorphic. -/
def StripPi : Set ℂ :=
  { z : ℂ | z ∈ UcDisk ∧ z.im ∈ Ioo (-π) π }

lemma isOpen_StripPi : IsOpen StripPi :=
  isOpen_UcDisk.inter (isOpen_Ioo.preimage Complex.continuous_im)

lemma mem_StripPi_iff {z : ℂ} :
    z ∈ StripPi ↔ z ∈ UcDisk ∧ z.im ∈ Ioo (-π) π :=
  Iff.rfl

/-- First derivative of `crossFactor Δ_phi` at $z \in \operatorname{UcDisk}$:
$$
\frac{d}{dz} \operatorname{crossFactor}(\Delta_\phi, z)
  = \Delta_\phi \, \frac{1 + e^z}{1 - e^z} \, \operatorname{crossFactor}(\Delta_\phi, z).
$$ -/
theorem hasDerivAt_crossFactor (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (crossFactor Δ_phi)
      ((Δ_phi : ℂ) * ((1 + Complex.exp z) / (1 - Complex.exp z)) *
        crossFactor Δ_phi z) z := by
  unfold crossFactor
  have hd_lin : HasDerivAt (fun u : ℂ => (Δ_phi : ℂ) * u) (Δ_phi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Δ_phi : ℂ)
  have hd_exp : HasDerivAt (fun u : ℂ => Complex.exp ((Δ_phi : ℂ) * u))
      (Complex.exp ((Δ_phi : ℂ) * z) * (Δ_phi : ℂ)) z :=
    hd_lin.cexp
  have hd_sub : HasDerivAt (fun u : ℂ => 1 - Complex.exp u) (-Complex.exp z) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub (Complex.hasDerivAt_exp z) using 1
    rw [zero_sub]
  have h_slit : 1 - Complex.exp z ∈ slitPlane := one_sub_exp_mem_slitPlane hz
  have hz_ne : 1 - Complex.exp z ≠ 0 := slitPlane_ne_zero h_slit
  have hd_cpow : HasDerivAt (fun u : ℂ => (1 - Complex.exp u) ^ (- (2 * Δ_phi : ℂ)))
      ((- (2 * Δ_phi : ℂ)) * (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ) - 1) *
        (-Complex.exp z)) z :=
    hd_sub.cpow_const h_slit
  have hd_prod := (hd_exp.const_mul ((4 : ℂ) ^ (Δ_phi : ℂ))).mul hd_cpow
  refine hd_prod.congr_deriv ?_
  have h_cpow_split :
      (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ) - 1) * (1 - Complex.exp z) =
        (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ)) := by
    calc
      (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ) - 1) * (1 - Complex.exp z)
        = (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ) - 1) * (1 - Complex.exp z) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
      _ = (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ) - 1 + 1) :=
          (Complex.cpow_add _ _ hz_ne).symm
      _ = (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ)) := by
          congr 1; ring
  rw [← h_cpow_split]
  field_simp [hz_ne]
  ring

theorem deriv_crossFactor (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (crossFactor Δ_phi) z =
      (Δ_phi : ℂ) * ((1 + Complex.exp z) / (1 - Complex.exp z)) *
        crossFactor Δ_phi z :=
  (hasDerivAt_crossFactor Δ_phi hz).deriv

theorem differentiableOn_crossFactor (Δ_phi : ℝ) :
    DifferentiableOn ℂ (crossFactor Δ_phi) UcDisk :=
  fun _ hz => (hasDerivAt_crossFactor Δ_phi hz).differentiableAt.differentiableWithinAt

/-- Second derivative of `crossFactor Δ_phi` at $z \in \operatorname{UcDisk}$. -/
theorem hasDerivAt_deriv_crossFactor (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (deriv (crossFactor Δ_phi))
      (((Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2) +
        (Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2) *
        crossFactor Δ_phi z) z := by
  have hz_ne : 1 - Complex.exp z ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz)
  have hd_rat := (hasDerivAt_one_add_exp_div_one_sub_exp hz_ne).const_mul (Δ_phi : ℂ)
  have hd_cf := hasDerivAt_crossFactor Δ_phi hz
  have hd_prod : HasDerivAt
      (fun u : ℂ => (Δ_phi : ℂ) * ((1 + Complex.exp u) / (1 - Complex.exp u)) *
        crossFactor Δ_phi u)
      (((Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2) +
        (Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2) *
        crossFactor Δ_phi z) z :=
    (hd_rat.mul hd_cf).congr_deriv (by ring)
  have h_ev : deriv (crossFactor Δ_phi) =ᶠ[𝓝 z]
      fun u : ℂ => (Δ_phi : ℂ) * ((1 + Complex.exp u) / (1 - Complex.exp u)) *
        crossFactor Δ_phi u := by
    filter_upwards [isOpen_UcDisk.mem_nhds hz] with u hu
    exact deriv_crossFactor Δ_phi hu
  exact hd_prod.congr_of_eventuallyEq h_ev

theorem deriv_deriv_crossFactor (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (deriv (crossFactor Δ_phi)) z =
      (((Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2) +
        (Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2) *
        crossFactor Δ_phi z) :=
  (hasDerivAt_deriv_crossFactor Δ_phi hz).deriv

/-- Upper bound on `‖deriv (crossFactor Δ_phi) z‖` for $z \in \operatorname{UcDisk}$:
$$
\|\partial_z \operatorname{crossFactor}(\Delta_\phi, z)\| \le
  2 |\Delta_\phi| \, \|1 - e^z\|^{-1} \, \|\operatorname{crossFactor}(\Delta_\phi, z)\|.
$$ -/
theorem norm_deriv_crossFactor_le (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    ‖deriv (crossFactor Δ_phi) z‖ ≤
      2 * |Δ_phi| * ‖1 - Complex.exp z‖⁻¹ * ‖crossFactor Δ_phi z‖ := by
  rw [deriv_crossFactor Δ_phi hz, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs]
  have h1z_pos : 0 < ‖1 - Complex.exp z‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz))
  have hexp_le1 : ‖Complex.exp z‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hz).le
  have h1_add_le2 : ‖1 + Complex.exp z‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp z)
    rw [norm_one] at h; linarith
  have h_quot : ‖1 + Complex.exp z‖ / ‖1 - Complex.exp z‖ ≤ 2 * ‖1 - Complex.exp z‖⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1_add_le2 (by positivity)
  calc
    |Δ_phi| * (‖1 + Complex.exp z‖ / ‖1 - Complex.exp z‖) * ‖crossFactor Δ_phi z‖
      ≤ |Δ_phi| * (2 * ‖1 - Complex.exp z‖⁻¹) * ‖crossFactor Δ_phi z‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_quot (abs_nonneg _)) (norm_nonneg _)
    _ = 2 * |Δ_phi| * ‖1 - Complex.exp z‖⁻¹ * ‖crossFactor Δ_phi z‖ := by ring

/-- Upper bound on `‖deriv (deriv (crossFactor Δ_phi)) z‖` for $z \in \operatorname{UcDisk}$:
$$
\|\partial_z^2 \operatorname{crossFactor}(\Delta_\phi, z)\| \le
  (2 |\Delta_\phi| + 4 \Delta_\phi^2) \, \|1 - e^z\|^{-2} \,
    \|\operatorname{crossFactor}(\Delta_\phi, z)\|.
$$ -/
theorem norm_deriv_deriv_crossFactor_le (Δ_phi : ℝ) {z : ℂ} (hz : z ∈ UcDisk) :
    ‖deriv (deriv (crossFactor Δ_phi)) z‖ ≤
      (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (‖1 - Complex.exp z‖ ^ 2)⁻¹ *
        ‖crossFactor Δ_phi z‖ := by
  rw [deriv_deriv_crossFactor Δ_phi hz, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1z_pos : 0 < ‖1 - Complex.exp z‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz))
  have hexp_le1 : ‖Complex.exp z‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hz).le
  have h1_add_le2 : ‖1 + Complex.exp z‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp z)
    rw [norm_one] at h; linarith
  have h_t1 :
      ‖(Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2)‖ ≤
        2 * |Δ_phi| * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, div_eq_mul_inv]
    calc
      |Δ_phi| * (2 * ‖Complex.exp z‖ * (‖1 - Complex.exp z‖ ^ 2)⁻¹)
        ≤ |Δ_phi| * (2 * 1 * (‖1 - Complex.exp z‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (abs_nonneg _)
      _ = 2 * |Δ_phi| * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by ring
  have h_t2 :
      ‖(Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2‖ ≤
        4 * Δ_phi ^ 2 * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by
    rw [norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, div_pow, div_eq_mul_inv]
    have h_sq : ‖1 + Complex.exp z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 + Complex.exp z)]
    calc
      Δ_phi ^ 2 * (‖1 + Complex.exp z‖ ^ 2 * (‖1 - Complex.exp z‖ ^ 2)⁻¹)
        ≤ Δ_phi ^ 2 * (4 * (‖1 - Complex.exp z‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h_sq (by positivity)) (sq_nonneg _)
      _ = 4 * Δ_phi ^ 2 * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by ring
  calc
    ‖(Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2) +
        (Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2‖
      ≤ ‖(Δ_phi : ℂ) * (2 * Complex.exp z / (1 - Complex.exp z) ^ 2)‖ +
          ‖(Δ_phi : ℂ) ^ 2 * ((1 + Complex.exp z) / (1 - Complex.exp z)) ^ 2‖ :=
        norm_add_le _ _
    _ ≤ 2 * |Δ_phi| * (‖1 - Complex.exp z‖ ^ 2)⁻¹ +
          4 * Δ_phi ^ 2 * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := add_le_add h_t1 h_t2
    _ = (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by ring

lemma exp_half_norm_lt_one {z : ℂ} (hz : z ∈ UcDisk) :
    ‖Complex.exp (z / 2)‖ < 1 := by
  rw [Complex.norm_exp, div_ofNat_re, Real.exp_lt_one_iff]
  linarith [mem_UcDisk_iff.mp hz]

lemma one_add_exp_half_ne_zero {z : ℂ} (hz : z ∈ UcDisk) :
    1 + Complex.exp (z / 2) ≠ 0 := by
  intro h
  have h1 : Complex.exp (z / 2) = -1 := eq_neg_of_add_eq_zero_right h
  have h2 : ‖Complex.exp (z / 2)‖ = 1 := by rw [h1, norm_neg, norm_one]
  linarith [exp_half_norm_lt_one hz]

lemma one_sub_exp_half_ne_zero {z : ℂ} (hz : z ∈ UcDisk) :
    1 - Complex.exp (z / 2) ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) = Complex.exp (z / 2) := sub_eq_zero.mp h
  have h2 : (1 : ℝ) = ‖Complex.exp (z / 2)‖ := by simpa using congrArg norm h1
  linarith [exp_half_norm_lt_one hz]

/-- First derivative of `crossW` on the strip `StripPi`:
$$\frac{d}{dz} \operatorname{crossW}(z) = \frac{-2 e^{z/2}}{1 - e^z}.$$ -/
theorem hasDerivAt_crossW {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    HasDerivAt crossW (-2 * Complex.exp (z / 2) / (1 - Complex.exp z)) z := by
  have hz_strip : z ∈ StripPi := ⟨hz, him⟩
  have h1z_cut : 1 - zOfW z ∈ CutPlane := CutPlane.sub_one (zOfW_mem_CutPlane hz him)
  have h_slit : rho (1 - zOfW z) ∈ slitPlane := rho_mem_slitPlane h1z_cut
  let g : ℂ → ℂ := fun u => ((1 - Complex.exp (u / 2)) / (1 + Complex.exp (u / 2))) ^ 2
  have hg_eq : g z = rho (1 - zOfW z) := (rho_one_sub_zOfW hz him).symm
  have hg_slit : g z ∈ slitPlane := hg_eq.symm ▸ h_slit
  have hd_half : HasDerivAt (fun u : ℂ => u / 2) ((1 / 2 : ℂ)) z := by
    simpa using (hasDerivAt_id z).div_const (2 : ℂ)
  have hd_exp_half : HasDerivAt (fun u : ℂ => Complex.exp (u / 2))
      (Complex.exp (z / 2) * (1 / 2 : ℂ)) z :=
    hd_half.cexp
  have hd_num : HasDerivAt (fun u : ℂ => 1 - Complex.exp (u / 2))
      (- (Complex.exp (z / 2) * (1 / 2 : ℂ))) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub hd_exp_half using 1
    rw [zero_sub]
  have hd_den : HasDerivAt (fun u : ℂ => 1 + Complex.exp (u / 2))
      (Complex.exp (z / 2) * (1 / 2 : ℂ)) z := by
    convert (hasDerivAt_const z (1 : ℂ)).add hd_exp_half using 1
    rw [zero_add]
  have h_den_ne : 1 + Complex.exp (z / 2) ≠ 0 := one_add_exp_half_ne_zero hz
  have h_num_ne : 1 - Complex.exp (z / 2) ≠ 0 := one_sub_exp_half_ne_zero hz
  have hd_quot := hd_num.div hd_den h_den_ne
  have hd_g : HasDerivAt g
      (((2 : ℕ) : ℂ) * ((1 - Complex.exp (z / 2)) / (1 + Complex.exp (z / 2))) ^ (2 - 1) *
        ((- (Complex.exp (z / 2) * (1 / 2 : ℂ)) * (1 + Complex.exp (z / 2)) -
          (1 - Complex.exp (z / 2)) * (Complex.exp (z / 2) * (1 / 2 : ℂ))) /
          (1 + Complex.exp (z / 2)) ^ 2)) z :=
    hd_quot.pow 2
  have hd_log := hd_g.clog hg_slit
  have h_ev : (fun u : ℂ => Complex.log (g u)) =ᶠ[𝓝 z] crossW := by
    filter_upwards [isOpen_StripPi.mem_nhds hz_strip] with u hu
    dsimp [crossW, logRho, g]
    rw [rho_one_sub_zOfW hu.1 hu.2]
  have hd_crossW := hd_log.congr_of_eventuallyEq h_ev.symm
  refine hd_crossW.congr_deriv ?_
  dsimp [g]
  have hexp_sq : Complex.exp z = Complex.exp (z / 2) ^ 2 := by
    rw [sq, ← Complex.exp_add, add_halves]
  have h1z_ne : 1 - Complex.exp z ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz)
  rw [hexp_sq] at h1z_ne ⊢
  field_simp [h_den_ne, h_num_ne, h1z_ne]
  ring

theorem deriv_crossW {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    deriv crossW z = -2 * Complex.exp (z / 2) / (1 - Complex.exp z) :=
  (hasDerivAt_crossW hz him).deriv

/-- Second derivative of `crossW` on the strip `StripPi`:
$$\frac{d^2}{dz^2} \operatorname{crossW}(z) = \frac{-e^{z/2}(1 + e^z)}{(1 - e^z)^2}.$$ -/
theorem hasDerivAt_deriv_crossW {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    HasDerivAt (deriv crossW)
      (-Complex.exp (z / 2) * (1 + Complex.exp z) / (1 - Complex.exp z) ^ 2) z := by
  have hz_strip : z ∈ StripPi := ⟨hz, him⟩
  have h1z_ne : 1 - Complex.exp z ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz)
  have hd_half : HasDerivAt (fun u : ℂ => u / 2) ((1 / 2 : ℂ)) z := by
    simpa using (hasDerivAt_id z).div_const (2 : ℂ)
  have hd_num : HasDerivAt (fun u : ℂ => -2 * Complex.exp (u / 2))
      (-2 * (Complex.exp (z / 2) * (1 / 2 : ℂ))) z :=
    hd_half.cexp.const_mul (-2 : ℂ)
  have hd_den : HasDerivAt (fun u : ℂ => 1 - Complex.exp u) (-Complex.exp z) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub (Complex.hasDerivAt_exp z) using 1
    rw [zero_sub]
  have hd_quot : HasDerivAt
      (fun u : ℂ => -2 * Complex.exp (u / 2) / (1 - Complex.exp u))
      (-Complex.exp (z / 2) * (1 + Complex.exp z) / (1 - Complex.exp z) ^ 2) z :=
    (hd_num.div hd_den h1z_ne).congr_deriv (by
      field_simp [h1z_ne]
      ring)
  have h_ev : deriv crossW =ᶠ[𝓝 z]
      fun u : ℂ => -2 * Complex.exp (u / 2) / (1 - Complex.exp u) := by
    filter_upwards [isOpen_StripPi.mem_nhds hz_strip] with u hu
    exact deriv_crossW hu.1 hu.2
  exact hd_quot.congr_of_eventuallyEq h_ev

theorem deriv_deriv_crossW {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    deriv (deriv crossW) z =
      -Complex.exp (z / 2) * (1 + Complex.exp z) / (1 - Complex.exp z) ^ 2 :=
  (hasDerivAt_deriv_crossW hz him).deriv

/-- Upper bound on `‖deriv crossW z‖` for $z \in \operatorname{StripPi}$:
$$\|\partial_z \operatorname{crossW}(z)\| \le 2 \, \|1 - e^z\|⁻¹.$$ -/
theorem norm_deriv_crossW_le {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    ‖deriv crossW z‖ ≤ 2 * ‖1 - Complex.exp z‖⁻¹ := by
  rw [deriv_crossW hz him, norm_div, norm_mul, norm_neg, Complex.norm_ofNat, div_eq_mul_inv]
  have h_exp : ‖Complex.exp (z / 2)‖ ≤ 1 := (exp_half_norm_lt_one hz).le
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Upper bound on `‖deriv (deriv crossW) z‖` for $z \in \operatorname{StripPi}$:
$$\|\partial_z^2 \operatorname{crossW}(z)\| \le 2 \, (\|1 - e^z\|^2)⁻¹.$$ -/
theorem norm_deriv_deriv_crossW_le {z : ℂ} (hz : z ∈ UcDisk) (him : z.im ∈ Ioo (-π) π) :
    ‖deriv (deriv crossW) z‖ ≤ 2 * (‖1 - Complex.exp z‖ ^ 2)⁻¹ := by
  rw [deriv_deriv_crossW hz him, norm_div, norm_mul, norm_neg, norm_pow, div_eq_mul_inv]
  have h_exp : ‖Complex.exp (z / 2)‖ ≤ 1 := (exp_half_norm_lt_one hz).le
  have hexp_z : ‖Complex.exp z‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hz).le
  have h1_add : ‖1 + Complex.exp z‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp z)
    rw [norm_one] at h; linarith
  have h_prod : ‖Complex.exp (z / 2)‖ * ‖1 + Complex.exp z‖ ≤ 2 := by
    nlinarith [norm_nonneg (1 + Complex.exp z)]
  exact mul_le_mul_of_nonneg_right h_prod (by positivity)

/-! ## Section 3: Untransmuted $t$-Channel Remainder & Endpoint Derivative Bounds -/

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- Monotonicity of `evalSpinReal` in its second argument $\sigma_{r, 1} \le \sigma_{r, 2} < 0$. -/
theorem evalSpinReal_mono_right (J : ℤ) {σl σr₁ σr₂ : ℝ}
    (hσl : σl < 0) (hσr₁ : σr₁ < 0) (hσr₂ : σr₂ < 0) (hle : σr₁ ≤ σr₂) :
    M.evalSpinReal J σl σr₁ ≤ M.evalSpinReal J σl σr₂ := by
  dsimp [evalSpinReal, monomialTermReal]
  refine integral_mono_ae (M.integrable_real hσl hσr₁ J) (M.integrable_real hσl hσr₂ J) ?_
  have h_unit : ∀ᵐ h : ℝ ∂(M.mu J), h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (M.support_unitary J)
  filter_upwards [h_unit] with h hh
  have hhJ : 0 ≤ h + (J : ℝ) := not_lt.mp fun hlt => hh (Or.inr hlt)
  exact Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left hle hhJ) _)

/-- Monotonicity of `evalReal` in its second argument $\sigma_{r, 1} \le \sigma_{r, 2} < 0$. -/
theorem evalReal_mono_right {σl σr₁ σr₂ : ℝ}
    (hσl : σl < 0) (hσr₁ : σr₁ < 0) (hσr₂ : σr₂ < 0) (hle : σr₁ ≤ σr₂) :
    M.evalReal σl σr₁ ≤ M.evalReal σl σr₂ :=
  (M.summable_real hσl hσr₁).tsum_le_tsum
    (fun J => M.evalSpinReal_mono_right J hσl hσr₁ hσr₂ hle)
    (M.summable_real hσl hσr₂)

/-- Holomorphy of `z ↦ M.eval wl z` on `UcDisk` when `M.eval` agrees with a four-point correlator
`corr.correlator_pdisk` on `UcPdisk`. -/
theorem differentiableOn_eval_right {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl : ℂ} (hwl : wl ∈ UcDisk) :
    DifferentiableOn ℂ (fun z : ℂ => M.eval wl z) UcDisk := by
  have h_corr : DifferentiableOn ℂ (fun z : ℂ => corr.correlator_pdisk wl z) UcDisk := by
    intro z hz
    have hmem : (wl, z) ∈ UcPdisk := ⟨hwl, hz⟩
    have h_joint := (corr.differentiableOn_correlator_pdisk hν).differentiableAt
      (isOpen_UcPdisk.mem_nhds hmem)
    exact (h_joint.comp z ((differentiableAt_const wl).prodMk differentiableAt_id)).differentiableWithinAt
  exact h_corr.congr fun z hz => hM hwl hz

end MonomialFourPointData

/-- The untransmuted $t$-channel remainder in the right variable $z \in \operatorname{UcDisk}$:
$$R(w_l, z) := \mathcal{G}_{\mathrm{mon}}(w_l, z) - \operatorname{crossIdentity}(\Delta_\phi, w_l, z).$$ -/
noncomputable def tChannelRemainder (M : MonomialFourPointData) (Δ_phi : ℝ) (wl z : ℂ) : ℂ :=
  M.eval wl z - crossIdentity Δ_phi wl z

/-- Holomorphy of `tChannelRemainder M Δ_phi wl` on `UcDisk`. -/
theorem differentiableOn_tChannelRemainder {ν Δ_phi : ℝ} (M : MonomialFourPointData)
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl : ℂ} (hwl : wl ∈ UcDisk) :
    DifferentiableOn ℂ (tChannelRemainder M Δ_phi wl) UcDisk := by
  unfold tChannelRemainder crossIdentity
  exact (M.differentiableOn_eval_right corr hν hM hwl).sub
    ((differentiableOn_crossFactor Δ_phi).const_mul (crossFactor Δ_phi wl))

/-- Uniform bound on `‖tChannelRemainder M Δ_phi wl z‖` on the half-plane $\operatorname{Re} z \le -1/4$
when $\operatorname{Re} w_l \le \sigma_l < 0$. -/
theorem norm_tChannelRemainder_le_of_re_le_neg_quarter (M : MonomialFourPointData)
    {Δ_phi σl : ℝ} (hΔ : 0 < Δ_phi) (hσl : σl < 0)
    {wl : ℂ} (hwl : wl ∈ UcDisk) (hwl_re : wl.re ≤ σl)
    {z : ℂ} (hz_re : z.re ≤ -1 / 4) :
    ‖tChannelRemainder M Δ_phi wl z‖ ≤
      M.evalReal σl (-1 / 4) +
        (4 : ℝ) ^ Δ_phi * (1 - Real.exp σl) ^ (-2 * Δ_phi) *
          ((4 : ℝ) ^ Δ_phi * (1 - Real.exp (-1 / 4)) ^ (-2 * Δ_phi)) := by
  have hz : z ∈ UcDisk := by rw [mem_UcDisk_iff]; linarith
  have h_eval : ‖M.eval wl z‖ ≤ M.evalReal σl (-1 / 4) := by
    calc
      ‖M.eval wl z‖ ≤ M.evalReal wl.re z.re := M.norm_eval_le_evalReal hwl hz
      _ ≤ M.evalReal σl z.re := M.evalReal_mono_left hwl hσl hz hwl_re
      _ ≤ M.evalReal σl (-1 / 4) := M.evalReal_mono_right hσl hz (by norm_num) hz_re
  have h_cf_wl := norm_crossFactor_le_of_re_le hΔ hσl hwl hwl_re
  have h_cf_z := norm_crossFactor_le_of_re_le hΔ (by norm_num : (-1 / 4 : ℝ) < 0) hz hz_re
  have h1_σl : 0 < 1 - Real.exp σl := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσl)
  unfold tChannelRemainder crossIdentity
  calc
    ‖M.eval wl z - crossFactor Δ_phi wl * crossFactor Δ_phi z‖
      ≤ ‖M.eval wl z‖ + ‖crossFactor Δ_phi wl * crossFactor Δ_phi z‖ := norm_sub_le _ _
    _ = ‖M.eval wl z‖ + ‖crossFactor Δ_phi wl‖ * ‖crossFactor Δ_phi z‖ := by rw [norm_mul]
    _ ≤ M.evalReal σl (-1 / 4) +
          (4 : ℝ) ^ Δ_phi * (1 - Real.exp σl) ^ (-2 * Δ_phi) *
            ((4 : ℝ) ^ Δ_phi * (1 - Real.exp (-1 / 4)) ^ (-2 * Δ_phi)) :=
      add_le_add h_eval (mul_le_mul h_cf_wl h_cf_z (norm_nonneg _) (by positivity))

/-- **Low-$x$ ($x \in (0, 1/2]$) First and Second Derivative Bounds on `tChannelRemainder`**:
For all $\Delta_\phi > 0$ and $\sigma_l < 0$, there exist $M_1, M_2 \ge 0$ such that whenever
$w_l \in \operatorname{UcDisk}$ with $\operatorname{Re} w_l \le \sigma_l$,
$w_r \in \operatorname{UcDisk}$, and $x \in (0, 1/2]$, the first and second derivatives of
`tChannelRemainder M Δ_phi wl` at $w_r + \log x$ are bounded by $M_1$ and $M_2$. -/
theorem exists_low_x_deriv_bounds_tChannelRemainder {ν Δ_phi : ℝ} (M : MonomialFourPointData)
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {σl : ℝ} (hσl : σl < 0) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      ∀ {wl : ℂ}, wl ∈ UcDisk → wl.re ≤ σl →
      ∀ {wr : ℂ}, wr ∈ UcDisk →
      ∀ {x : ℝ}, x ∈ Ioc (0 : ℝ) (1 / 2) →
        ‖deriv (tChannelRemainder M Δ_phi wl) (wr + (Real.log x : ℂ))‖ ≤ M₁ ∧
        ‖deriv (deriv (tChannelRemainder M Δ_phi wl)) (wr + (Real.log x : ℂ))‖ ≤ M₂ := by
  set M₀ : ℝ :=
    M.evalReal σl (-1 / 4) +
      (4 : ℝ) ^ Δ_phi * (1 - Real.exp σl) ^ (-2 * Δ_phi) *
        ((4 : ℝ) ^ Δ_phi * (1 - Real.exp (-1 / 4)) ^ (-2 * Δ_phi))
  have hM₀_nonneg : 0 ≤ M₀ := by
    dsimp [M₀]
    have h1 : 0 ≤ M.evalReal σl (-1 / 4) := M.evalReal_nonneg _ _
    have h2 : 0 < 1 - Real.exp σl := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσl)
    have h3 : 0 < 1 - Real.exp (-1 / 4) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    positivity
  refine ⟨4 * M₀, 64 * M₀, by positivity, by positivity, fun {wl} hwl hwl_re {wr} hwr {x} hx => ?_⟩
  exact norm_deriv_and_deriv2_add_log_le_of_re_le
    (differentiableOn_tChannelRemainder M corr hν hM hwl)
    (fun z hz_re => norm_tChannelRemainder_le_of_re_le_neg_quarter M hΔ hσl hwl hwl_re hz_re)
    hwr hx

/-- When $\operatorname{Re} w_r \ge -1/2$, $\operatorname{Im} w_r \in [-\pi/2, \pi/2]$, and
$x \in (1/2, 1)$, the point $z = w_r + \log x$ satisfies $\operatorname{Re} z \ge -2$,
$\operatorname{Im} z \in [-\pi/2, \pi/2]$, and $\operatorname{Re}(\operatorname{crossW} z) \le \sigma_{r, 0} < 0$
where $\sigma_{r, 0} = \log(1 - \frac{\sqrt{2}}{4} e^{-1}) < 0$. -/
lemma re_crossW_add_log_le {wr : ℂ} (hwr : wr ∈ UcDisk) (hwr_re : -1 / 2 ≤ wr.re)
    (hwr_im : wr.im ∈ Icc (-π / 2) (π / 2)) {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) 1) :
    (crossW (wr + (Real.log x : ℂ))).re ≤ Real.log (1 - Real.sqrt 2 / 4 * Real.exp (-1)) := by
  set z : ℂ := wr + (Real.log x : ℂ)
  have hlog_neg : Real.log x < 0 := Real.log_neg (by linarith [hx.1]) hx.2
  have hlog_ge : -1 ≤ Real.log x := by
    have h1 : Real.exp (-1) ≤ x := by
      have : Real.exp (-1) < 1 / 2 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
        norm_num
        linarith [Real.add_one_lt_exp (one_ne_zero)]
      linarith [hx.1]
    have h2 := Real.log_le_log (Real.exp_pos (-1)) h1
    rwa [Real.log_exp] at h2
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  have hz_re : -2 ≤ z.re := by
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith
  have hz_im : z.im ∈ Icc (-π / 2) (π / 2) := by
    simpa [z] using hwr_im
  have h_bd := re_crossW_le_of_re_ge hz hz_re hz_im
  have h_div : (-2 : ℝ) / 2 = -1 := by ring
  rwa [h_div] at h_bd

lemma log_one_sub_sqrt_two_div_four_mul_exp_neg_one_neg :
    Real.log (1 - Real.sqrt 2 / 4 * Real.exp (-1)) < 0 := by
  have h_pos : 0 < Real.sqrt 2 / 4 * Real.exp (-1) := by positivity
  have h_lt1 : Real.sqrt 2 / 4 * Real.exp (-1) < 1 := by
    have h1 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith [Real.exp_pos (-1)]
  exact Real.log_neg (by linarith) (by linarith)

/-- First and second derivatives of
$$
z \mapsto \operatorname{crossFactor}(\Delta_\phi, w_l) \cdot
  \operatorname{crossFactor}(\Delta_\phi, z) \cdot f(\operatorname{crossW}(z))
$$
on `StripPi`, which coincides with `tChannelRemainder M Δ_phi wl` on the open neighborhood
`StripPi`. -/
lemma deriv_and_deriv2_tChannelRemainder_eq_on_StripPi {ν Δ_phi : ℝ}
    (M : MonomialFourPointData) (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hwl_im : wl.im ∈ Ioo (-π) π)
    (hz : z ∈ UcDisk) (hz_im : z.im ∈ Ioo (-π) π) :
    let f : ℂ → ℂ := fun w' => M.eval (crossW wl) w' - 1
    let w' : ℂ := crossW z
    deriv (tChannelRemainder M Δ_phi wl) z =
      crossFactor Δ_phi wl *
        (deriv (crossFactor Δ_phi) z * f w' +
          crossFactor Δ_phi z * (deriv f w' * deriv crossW z)) ∧
    deriv (deriv (tChannelRemainder M Δ_phi wl)) z =
      crossFactor Δ_phi wl *
        (deriv (deriv (crossFactor Δ_phi)) z * f w' +
          2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
          crossFactor Δ_phi z *
            (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
              deriv f w' * deriv (deriv crossW) z)) := by
  intro f w'
  have hwl_cross : crossW wl ∈ UcDisk := crossW_mem_UcDisk hwl hwl_im
  have hf_diff : DifferentiableOn ℂ f UcDisk :=
    (M.differentiableOn_eval_right corr hν hM hwl_cross).sub (differentiableOn_const 1)
  have hf'_diff : DifferentiableOn ℂ (deriv f) UcDisk := hf_diff.deriv isOpen_UcDisk
  have hz_strip : z ∈ StripPi := ⟨hz, hz_im⟩
  let G : ℂ → ℂ := fun u => crossFactor Δ_phi wl * (crossFactor Δ_phi u * f (crossW u))
  let G1 : ℂ → ℂ := fun u =>
    crossFactor Δ_phi wl *
      (deriv (crossFactor Δ_phi) u * f (crossW u) +
        crossFactor Δ_phi u * (deriv f (crossW u) * deriv crossW u))
  have h_eqOn_G : ∀ u ∈ StripPi, tChannelRemainder M Δ_phi wl u = G u := by
    intro u hu
    dsimp [tChannelRemainder, G, f, crossIdentity]
    rw [M.eval_eq_cross corr hν hM hwl hu.1 hwl_im hu.2]
    dsimp [crossIdentity]
    ring
  have h_hasDeriv_G : ∀ u ∈ StripPi, HasDerivAt G (G1 u) u := by
    intro u hu
    have hu_cross : crossW u ∈ UcDisk := crossW_mem_UcDisk hu.1 hu.2
    have hd_cf : HasDerivAt (crossFactor Δ_phi) (deriv (crossFactor Δ_phi) u) u :=
      (hasDerivAt_crossFactor Δ_phi hu.1).differentiableAt.hasDerivAt
    have hd_cw : HasDerivAt crossW (deriv crossW u) u :=
      (hasDerivAt_crossW hu.1 hu.2).differentiableAt.hasDerivAt
    have hd_f : HasDerivAt f (deriv f (crossW u)) (crossW u) :=
      (hf_diff (crossW u) hu_cross).differentiableAt (isOpen_UcDisk.mem_nhds hu_cross) |>.hasDerivAt
    have hd_f_comp : HasDerivAt (fun v => f (crossW v)) (deriv f (crossW u) * deriv crossW u) u :=
      HasDerivAt.comp (h₂ := f) (h := crossW) u hd_f hd_cw
    exact (hd_cf.mul hd_f_comp).const_mul (crossFactor Δ_phi wl)
  have h_ev_G : tChannelRemainder M Δ_phi wl =ᶠ[𝓝 z] G :=
    Filter.eventuallyEq_of_mem (isOpen_StripPi.mem_nhds hz_strip) h_eqOn_G
  have h_d1 : deriv (tChannelRemainder M Δ_phi wl) z = G1 z := by
    rw [h_ev_G.deriv_eq, (h_hasDeriv_G z hz_strip).deriv]
  have h_ev_G1 : deriv (tChannelRemainder M Δ_phi wl) =ᶠ[𝓝 z] G1 := by
    filter_upwards [isOpen_StripPi.mem_nhds hz_strip] with u hu
    have h_ev_u : tChannelRemainder M Δ_phi wl =ᶠ[𝓝 u] G :=
      Filter.eventuallyEq_of_mem (isOpen_StripPi.mem_nhds hu) h_eqOn_G
    rw [h_ev_u.deriv_eq, (h_hasDeriv_G u hu).deriv]
  have hw'_mem : w' ∈ UcDisk := crossW_mem_UcDisk hz hz_im
  have hd_cf1 : HasDerivAt (crossFactor Δ_phi) (deriv (crossFactor Δ_phi) z) z :=
    (hasDerivAt_crossFactor Δ_phi hz).differentiableAt.hasDerivAt
  have hd_cf2 : HasDerivAt (deriv (crossFactor Δ_phi)) (deriv (deriv (crossFactor Δ_phi)) z) z :=
    (hasDerivAt_deriv_crossFactor Δ_phi hz).differentiableAt.hasDerivAt
  have hd_cw1 : HasDerivAt crossW (deriv crossW z) z :=
    (hasDerivAt_crossW hz hz_im).differentiableAt.hasDerivAt
  have hd_cw2 : HasDerivAt (deriv crossW) (deriv (deriv crossW) z) z :=
    (hasDerivAt_deriv_crossW hz hz_im).differentiableAt.hasDerivAt
  have hd_f1 : HasDerivAt f (deriv f w') w' :=
    (hf_diff w' hw'_mem).differentiableAt (isOpen_UcDisk.mem_nhds hw'_mem) |>.hasDerivAt
  have hd_f2 : HasDerivAt (deriv f) (deriv (deriv f) w') w' :=
    (hf'_diff w' hw'_mem).differentiableAt (isOpen_UcDisk.mem_nhds hw'_mem) |>.hasDerivAt
  have hd_f_comp : HasDerivAt (fun u => f (crossW u)) (deriv f w' * deriv crossW z) z :=
    HasDerivAt.comp (h₂ := f) (h := crossW) z hd_f1 hd_cw1
  have hd_f'_comp : HasDerivAt (fun u => deriv f (crossW u))
      (deriv (deriv f) w' * deriv crossW z) z :=
    HasDerivAt.comp (h₂ := deriv f) (h := crossW) z hd_f2 hd_cw1
  have hd_prod1 : HasDerivAt (fun u => deriv (crossFactor Δ_phi) u * f (crossW u))
      (deriv (deriv (crossFactor Δ_phi)) z * f w' +
        deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z)) z :=
    hd_cf2.mul hd_f_comp
  have hd_prod2 : HasDerivAt (fun u => crossFactor Δ_phi u * (deriv f (crossW u) * deriv crossW u))
      (deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
        crossFactor Δ_phi z *
          ((deriv (deriv f) w' * deriv crossW z) * deriv crossW z +
            deriv f w' * deriv (deriv crossW) z)) z :=
    hd_cf1.mul (hd_f'_comp.mul hd_cw2)
  have hd_G1 : HasDerivAt G1
      (crossFactor Δ_phi wl *
        (deriv (deriv (crossFactor Δ_phi)) z * f w' +
          2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
          crossFactor Δ_phi z *
            (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
              deriv f w' * deriv (deriv crossW) z))) z :=
    ((hd_prod1.add hd_prod2).const_mul (crossFactor Δ_phi wl)).congr_deriv (by
      dsimp [w']; ring)
  refine ⟨h_d1, ?_⟩
  rw [h_ev_G1.deriv_eq, hd_G1.deriv]

/-- **High-$x$ ($x \in (1/2, 1)$) First and Second Derivative Bounds on `tChannelRemainder`**:
For all $\Delta_\phi > 0$, $0 < h' \le h_{\mathrm{gap}}$, $\sigma_l < 0$, and $\sigma_{l, 0} < 0$,
there exist $C_1, C_2 \ge 0$ such that for all $w_l \in \operatorname{UcDisk}$ with
$\operatorname{Re} w_l \le \sigma_l$, $\operatorname{Im} w_l \in (-\pi, \pi)$, and
$\operatorname{Re}(\operatorname{crossW} w_l) \le \sigma_{l, 0}$, all $w_r \in \operatorname{UcDisk}$
with $\operatorname{Re} w_r \ge -1/2$ and $\operatorname{Im} w_r \in [-\pi/2, \pi/2]$, and all
$x \in (1/2, 1)$,
$$
\|\partial_z R(w_l, w_r + \log x)\| \le
  C_1 \bigl(\|1 - e^{w_r}\| + (1 - x)\bigr)^{2(h' - \Delta_\phi) - 1},
$$
$$
\|\partial_z^2 R(w_l, w_r + \log x)\| \le
  C_2 \bigl(\|1 - e^{w_r}\| + (1 - x)\bigr)^{2(h' - \Delta_\phi) - 2}.
$$ -/
theorem exists_high_x_deriv_bounds_tChannelRemainder {ν Δ_phi h_gap h' : ℝ}
    (M : MonomialFourPointData) (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap) (hh'_pos : 0 < h') (hh'_le : h' ≤ h_gap)
    {σl σl0 : ℝ} (hσl : σl < 0) (hσl0 : σl0 < 0) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ {wl : ℂ}, wl ∈ UcDisk → wl.re ≤ σl → wl.im ∈ Ioo (-π) π → (crossW wl).re ≤ σl0 →
      ∀ {wr : ℂ}, wr ∈ UcDisk → -1 / 2 ≤ wr.re → wr.im ∈ Icc (-π / 2) (π / 2) →
      ∀ {x : ℝ}, x ∈ Ioo (1 / 2 : ℝ) 1 →
        ‖deriv (tChannelRemainder M Δ_phi wl) (wr + (Real.log x : ℂ))‖ ≤
          C₁ * (‖1 - Complex.exp wr‖ + (1 - x)) ^ (2 * (h' - Δ_phi) - 1) ∧
        ‖deriv (deriv (tChannelRemainder M Δ_phi wl)) (wr + (Real.log x : ℂ))‖ ≤
          C₂ * (‖1 - Complex.exp wr‖ + (1 - x)) ^ (2 * (h' - Δ_phi) - 2) := by
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set σr0 : ℝ := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (-1))
  have hσr0_neg : σr0 < 0 := log_one_sub_sqrt_two_div_four_mul_exp_neg_one_neg
  set r_c : ℝ := -σr0 / 2
  have hr_c_pos : 0 < r_c := by dsimp [r_c]; linarith
  have hσr0_half_neg : σr0 / 2 < 0 := by linarith
  have h_1_exp_σl_pos : 0 < 1 - Real.exp σl :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hσl)
  set K_wl : ℝ := (4 : ℝ) ^ Δ_phi * (1 - Real.exp σl) ^ (-2 * Δ_phi)
  have hK_wl_pos : 0 < K_wl := by dsimp [K_wl]; positivity
  set K_gap : ℝ :=
    Real.exp (h' * (r_c - σr0 / 2)) * (M.evalReal σl0 (σr0 / 2) - 1)
  have hK_gap_nonneg : 0 ≤ K_gap := by
    dsimp [K_gap]
    exact mul_nonneg (Real.exp_pos _).le (M.evalReal_sub_one_nonneg hgap' hσl0 hσr0_half_neg)
  set B₁ : ℝ :=
    K_wl * (4 : ℝ) ^ Δ_phi * K_gap * (2 * |Δ_phi| + 2 / r_c)
  set B₂ : ℝ :=
    K_wl * (4 : ℝ) ^ Δ_phi * K_gap *
      ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) + 8 * |Δ_phi| / r_c + 16 / r_c ^ 2 + 2 / r_c)
  have hB₁_nonneg : 0 ≤ B₁ := by dsimp [B₁]; positivity
  have hB₂_nonneg : 0 ≤ B₂ := by dsimp [B₂]; positivity
  set M_scale1 : ℝ := max 1 ((1 / 3 : ℝ) ^ (2 * (h' - Δ_phi) - 1))
  set M_scale2 : ℝ := max 1 ((1 / 3 : ℝ) ^ (2 * (h' - Δ_phi) - 2))
  refine ⟨B₁ * M_scale1, B₂ * M_scale2, by positivity, by positivity,
    fun {wl} hwl hwl_re hwl_im hwl_cross {wr} hwr hwr_re hwr_im {x} hx => ?_⟩
  set z : ℂ := wr + (Real.log x : ℂ)
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hlog_neg : Real.log x < 0 := Real.log_neg hx0 hx.2
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  have hz_im_icc : z.im ∈ Icc (-π / 2) (π / 2) := by simpa [z] using hwr_im
  have hz_im : z.im ∈ Ioo (-π) π :=
    ⟨by linarith [hz_im_icc.1, Real.pi_pos], by linarith [hz_im_icc.2, Real.pi_pos]⟩
  set w' : ℂ := crossW z
  have hw'_re_le : w'.re ≤ σr0 := re_crossW_add_log_le hwr hwr_re hwr_im hx
  have hw'_mem : w' ∈ UcDisk := crossW_mem_UcDisk hz hz_im
  have hwl_cross_mem : crossW wl ∈ UcDisk := crossW_mem_UcDisk hwl hwl_im
  let f : ℂ → ℂ := fun ζ => M.eval (crossW wl) ζ - 1
  have hf_diff : DifferentiableOn ℂ f UcDisk :=
    (M.differentiableOn_eval_right corr hν hM hwl_cross_mem).sub (differentiableOn_const 1)
  have h_ball_sub : Metric.closedBall w' r_c ⊆ UcDisk := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have h_re_diff : (ζ - w').re ≤ r_c := (Complex.re_le_norm _).trans hζ
    have h_sub_re : (ζ - w').re = ζ.re - w'.re := Complex.sub_re _ _
    rw [mem_UcDisk_iff]
    dsimp [r_c] at h_re_diff
    linarith
  have h_ball_bd : ∀ ζ ∈ Metric.closedBall w' r_c,
      ‖f ζ‖ ≤ K_gap * Real.exp (h' * w'.re) := by
    intro ζ hζ
    have hζ_mem : ζ ∈ UcDisk := h_ball_sub hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have h_re_diff : (ζ - w').re ≤ r_c := (Complex.re_le_norm _).trans hζ
    have h_sub_re : (ζ - w').re = ζ.re - w'.re := Complex.sub_re _ _
    have hζ_re_le : ζ.re ≤ σr0 / 2 := by dsimp [r_c] at h_re_diff; linarith
    have hζ_re_le_w' : ζ.re - σr0 / 2 ≤ w'.re + (r_c - σr0 / 2) := by linarith
    have h_norm := M.norm_eval_sub_one_le hgap' hσr0_half_neg hwl_cross_mem hζ_mem hζ_re_le
    have h_mono_wl :
        M.evalReal (crossW wl).re (σr0 / 2) - 1 ≤ M.evalReal σl0 (σr0 / 2) - 1 :=
      sub_le_sub_right
        (M.evalReal_mono_left hwl_cross_mem hσl0 hσr0_half_neg hwl_cross) 1
    have h_exp_le :
        Real.exp (h' * (ζ.re - σr0 / 2)) ≤
          Real.exp (h' * (r_c - σr0 / 2)) * Real.exp (h' * w'.re) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : h' * (ζ.re - σr0 / 2) ≤ h' * (w'.re + (r_c - σr0 / 2)) :=
        mul_le_mul_of_nonneg_left hζ_re_le_w' hh'_pos.le
      linarith
    dsimp [f, K_gap]
    calc
      ‖M.eval (crossW wl) ζ - 1‖
        ≤ Real.exp (h' * (ζ.re - σr0 / 2)) *
            (M.evalReal (crossW wl).re (σr0 / 2) - 1) := h_norm
      _ ≤ (Real.exp (h' * (r_c - σr0 / 2)) * Real.exp (h' * w'.re)) *
            (M.evalReal σl0 (σr0 / 2) - 1) :=
          mul_le_mul h_exp_le h_mono_wl
            (M.evalReal_sub_one_nonneg hgap' hwl_cross_mem hσr0_half_neg) (by positivity)
      _ = Real.exp (h' * (r_c - σr0 / 2)) * (M.evalReal σl0 (σr0 / 2) - 1) *
            Real.exp (h' * w'.re) := by ring
  have hf0_bd : ‖f w'‖ ≤ K_gap * Real.exp (h' * w'.re) :=
    h_ball_bd w' (Metric.mem_closedBall_self hr_c_pos.le)
  have hf1_bd : ‖deriv f w'‖ ≤ (K_gap / r_c) * Real.exp (h' * w'.re) := by
    have h := norm_deriv_le_of_ball_bound isOpen_UcDisk hf_diff hr_c_pos h_ball_sub h_ball_bd
    rwa [mul_div_right_comm] at h
  have hf2_bd : ‖deriv (deriv f) w'‖ ≤ (4 * K_gap / r_c ^ 2) * Real.exp (h' * w'.re) := by
    have h := norm_deriv2_le_of_ball_bound isOpen_UcDisk hf_diff hr_c_pos h_ball_sub h_ball_bd
    have h_eq : 4 * (K_gap * Real.exp (h' * w'.re)) / r_c ^ 2 =
        (4 * K_gap / r_c ^ 2) * Real.exp (h' * w'.re) := by ring
    rwa [h_eq] at h
  have h_cf_wl_le : ‖crossFactor Δ_phi wl‖ ≤ K_wl :=
    norm_crossFactor_le_of_re_le hΔ hσl hwl hwl_re
  set s : ℝ := ‖1 - Complex.exp z‖
  set u : ℝ := ‖1 - Complex.exp wr‖ + (1 - x)
  have hs_pos : 0 < s :=
    norm_pos_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hz))
  have hu_pos : 0 < u := add_pos_of_nonneg_of_pos (norm_nonneg _) hx1
  have hexp_z : Complex.exp z = (x : ℂ) * Complex.exp wr := by
    dsimp [z]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx0, mul_comm]
  have hs_le_u : s ≤ u := by
    dsimp [s, u]
    rw [hexp_z]
    exact norm_one_sub_mul_exp_le x ⟨hx0.le, hx.2.le⟩ wr
  have hu_le_3s : (1 / 3 : ℝ) * u ≤ s := by
    dsimp [s, u]
    rw [hexp_z]
    exact le_norm_one_sub_mul_exp hwr ⟨hx.1.le, hx.2.le⟩
  have h_cf_z_exp :
      ‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re) ≤
        (4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi)) :=
    norm_crossFactor_mul_exp_re_crossW_le hΔ hh'_pos hz hz_im_icc
  have h_deriv_eq := deriv_and_deriv2_tChannelRemainder_eq_on_StripPi M corr hν hM
    hwl hwl_im hz hz_im
  have hd_cf1 := norm_deriv_crossFactor_le Δ_phi hz
  have hd_cf2 := norm_deriv_deriv_crossFactor_le Δ_phi hz
  have hd_cw1 := norm_deriv_crossW_le hz hz_im
  have hd_cw2 := norm_deriv_deriv_crossW_le hz hz_im
  have hs_rpow1 : s ^ (2 * (h' - Δ_phi)) * s⁻¹ = s ^ (2 * (h' - Δ_phi) - 1) := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs_pos.ne']
  have hs_rpow2 : s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹ = s ^ (2 * (h' - Δ_phi) - 2) := by
    have hs2 : s ^ (2 : ℕ) = s ^ (2 : ℝ) := (Real.rpow_natCast s 2).symm
    rw [← div_eq_mul_inv, hs2, ← Real.rpow_sub hs_pos]
  have hs_u_scale : ∀ α : ℝ,
      s ^ α ≤ max 1 ((1 / 3 : ℝ) ^ α) * u ^ α := by
    intro α
    rcases le_or_gt α 0 with hα | hα
    · calc
        s ^ α ≤ ((1 / 3 : ℝ) * u) ^ α :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hu_le_3s hα
        _ = (1 / 3 : ℝ) ^ α * u ^ α := Real.mul_rpow (by norm_num) hu_pos.le
        _ ≤ max 1 ((1 / 3 : ℝ) ^ α) * u ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · calc
        s ^ α ≤ u ^ α := Real.rpow_le_rpow hs_pos.le hs_le_u hα.le
        _ = 1 * u ^ α := (one_mul _).symm
        _ ≤ max 1 ((1 / 3 : ℝ) ^ α) * u ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  constructor
  · rw [h_deriv_eq.1, norm_mul]
    have h_inner1 :
        ‖deriv (crossFactor Δ_phi) z * f w' +
          crossFactor Δ_phi z * (deriv f w' * deriv crossW z)‖ ≤
          (4 : ℝ) ^ Δ_phi * K_gap * (2 * |Δ_phi| + 2 / r_c) *
            s ^ (2 * (h' - Δ_phi) - 1) := by
      have ht1 :
          ‖deriv (crossFactor Δ_phi) z * f w'‖ ≤
            2 * |Δ_phi| * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) := by
        rw [norm_mul]
        calc
          ‖deriv (crossFactor Δ_phi) z‖ * ‖f w'‖
            ≤ (2 * |Δ_phi| * s⁻¹ * ‖crossFactor Δ_phi z‖) *
                (K_gap * Real.exp (h' * w'.re)) :=
              mul_le_mul hd_cf1 hf0_bd (norm_nonneg _) (by positivity)
          _ = 2 * |Δ_phi| * K_gap * s⁻¹ *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by ring
          _ ≤ 2 * |Δ_phi| * K_gap * s⁻¹ *
                ((4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi))) :=
              mul_le_mul_of_nonneg_left h_cf_z_exp (by positivity)
          _ = 2 * |Δ_phi| * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) := by ring
      have ht2 :
          ‖crossFactor Δ_phi z * (deriv f w' * deriv crossW z)‖ ≤
            (2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) := by
        rw [norm_mul, norm_mul]
        calc
          ‖crossFactor Δ_phi z‖ * (‖deriv f w'‖ * ‖deriv crossW z‖)
            ≤ ‖crossFactor Δ_phi z‖ *
                (((K_gap / r_c) * Real.exp (h' * w'.re)) * (2 * s⁻¹)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hf1_bd hd_cw1 (norm_nonneg _) (by positivity))
                (norm_nonneg _)
          _ = (2 / r_c) * K_gap * s⁻¹ *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by ring
          _ ≤ (2 / r_c) * K_gap * s⁻¹ *
                ((4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi))) :=
              mul_le_mul_of_nonneg_left h_cf_z_exp (by positivity)
          _ = (2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) := by ring
      calc
        ‖deriv (crossFactor Δ_phi) z * f w' +
            crossFactor Δ_phi z * (deriv f w' * deriv crossW z)‖
          ≤ ‖deriv (crossFactor Δ_phi) z * f w'‖ +
              ‖crossFactor Δ_phi z * (deriv f w' * deriv crossW z)‖ := norm_add_le _ _
        _ ≤ 2 * |Δ_phi| * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) +
              (2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap * (s ^ (2 * (h' - Δ_phi)) * s⁻¹) :=
            add_le_add ht1 ht2
        _ = (4 : ℝ) ^ Δ_phi * K_gap * (2 * |Δ_phi| + 2 / r_c) *
              (s ^ (2 * (h' - Δ_phi)) * s⁻¹) := by ring
        _ = (4 : ℝ) ^ Δ_phi * K_gap * (2 * |Δ_phi| + 2 / r_c) *
              s ^ (2 * (h' - Δ_phi) - 1) := by rw [hs_rpow1]
    calc
      ‖crossFactor Δ_phi wl‖ *
          ‖deriv (crossFactor Δ_phi) z * f w' +
            crossFactor Δ_phi z * (deriv f w' * deriv crossW z)‖
        ≤ K_wl *
            ((4 : ℝ) ^ Δ_phi * K_gap * (2 * |Δ_phi| + 2 / r_c) *
              s ^ (2 * (h' - Δ_phi) - 1)) :=
          mul_le_mul h_cf_wl_le h_inner1 (norm_nonneg _) hK_wl_pos.le
      _ = B₁ * s ^ (2 * (h' - Δ_phi) - 1) := by dsimp [B₁]; ring
      _ ≤ B₁ * (M_scale1 * u ^ (2 * (h' - Δ_phi) - 1)) :=
          mul_le_mul_of_nonneg_left (hs_u_scale _) hB₁_nonneg
      _ = (B₁ * M_scale1) * u ^ (2 * (h' - Δ_phi) - 1) := by ring
  · rw [h_deriv_eq.2, norm_mul]
    have h_inner2 :
        ‖deriv (deriv (crossFactor Δ_phi)) z * f w' +
          2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
          crossFactor Δ_phi z *
            (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
              deriv f w' * deriv (deriv crossW) z)‖ ≤
          (4 : ℝ) ^ Δ_phi * K_gap *
            ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) + 8 * |Δ_phi| / r_c + 16 / r_c ^ 2 + 2 / r_c) *
            s ^ (2 * (h' - Δ_phi) - 2) := by
      have ht1 :
          ‖deriv (deriv (crossFactor Δ_phi)) z * f w'‖ ≤
            (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (4 : ℝ) ^ Δ_phi * K_gap *
              (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by
        rw [norm_mul]
        calc
          ‖deriv (deriv (crossFactor Δ_phi)) z‖ * ‖f w'‖
            ≤ ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (s ^ 2)⁻¹ * ‖crossFactor Δ_phi z‖) *
                (K_gap * Real.exp (h' * w'.re)) :=
              mul_le_mul hd_cf2 hf0_bd (norm_nonneg _) (by positivity)
          _ = (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * K_gap * (s ^ 2)⁻¹ *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by ring
          _ ≤ (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * K_gap * (s ^ 2)⁻¹ *
                ((4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi))) :=
              mul_le_mul_of_nonneg_left h_cf_z_exp (by positivity)
          _ = (2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by ring
      have ht2 :
          ‖2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z)‖ ≤
            (8 * |Δ_phi| / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
              (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
        have hs_inv_sq : s⁻¹ * s⁻¹ = (s ^ 2)⁻¹ := by rw [sq, mul_inv]
        calc
          2 * ‖deriv (crossFactor Δ_phi) z‖ * (‖deriv f w'‖ * ‖deriv crossW z‖)
            ≤ 2 * (2 * |Δ_phi| * s⁻¹ * ‖crossFactor Δ_phi z‖) *
                (((K_gap / r_c) * Real.exp (h' * w'.re)) * (2 * s⁻¹)) :=
              mul_le_mul
                (mul_le_mul_of_nonneg_left hd_cf1 zero_le_two)
                (mul_le_mul hf1_bd hd_cw1 (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
          _ = (8 * |Δ_phi| / r_c) * K_gap * (s⁻¹ * s⁻¹) *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by ring
          _ = (8 * |Δ_phi| / r_c) * K_gap * (s ^ 2)⁻¹ *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by rw [hs_inv_sq]
          _ ≤ (8 * |Δ_phi| / r_c) * K_gap * (s ^ 2)⁻¹ *
                ((4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi))) :=
              mul_le_mul_of_nonneg_left h_cf_z_exp (by positivity)
          _ = (8 * |Δ_phi| / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by ring
      have ht3 :
          ‖crossFactor Δ_phi z *
            (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
              deriv f w' * deriv (deriv crossW) z)‖ ≤
            (16 / r_c ^ 2 + 2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
              (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by
        rw [norm_mul]
        have h_cw_sq : ‖(deriv crossW z) ^ 2‖ ≤ 4 * (s ^ 2)⁻¹ := by
          rw [norm_pow]
          have h1 := pow_le_pow_left₀ (norm_nonneg _) hd_cw1 2
          have h2 : (2 * s⁻¹) ^ 2 = 4 * (s ^ 2)⁻¹ := by rw [mul_pow, inv_pow]; ring
          rwa [h2] at h1
        have h_sub3 :
            ‖deriv (deriv f) w' * (deriv crossW z) ^ 2 +
              deriv f w' * deriv (deriv crossW) z‖ ≤
              (16 / r_c ^ 2 + 2 / r_c) * K_gap * Real.exp (h' * w'.re) * (s ^ 2)⁻¹ := by
          calc
            ‖deriv (deriv f) w' * (deriv crossW z) ^ 2 +
                deriv f w' * deriv (deriv crossW) z‖
              ≤ ‖deriv (deriv f) w' * (deriv crossW z) ^ 2‖ +
                  ‖deriv f w' * deriv (deriv crossW) z‖ := norm_add_le _ _
            _ = ‖deriv (deriv f) w'‖ * ‖(deriv crossW z) ^ 2‖ +
                  ‖deriv f w'‖ * ‖deriv (deriv crossW) z‖ := by rw [norm_mul, norm_mul]
            _ ≤ ((4 * K_gap / r_c ^ 2) * Real.exp (h' * w'.re)) * (4 * (s ^ 2)⁻¹) +
                  ((K_gap / r_c) * Real.exp (h' * w'.re)) * (2 * (s ^ 2)⁻¹) :=
                add_le_add
                  (mul_le_mul hf2_bd h_cw_sq (norm_nonneg _) (by positivity))
                  (mul_le_mul hf1_bd hd_cw2 (norm_nonneg _) (by positivity))
            _ = (16 / r_c ^ 2 + 2 / r_c) * K_gap * Real.exp (h' * w'.re) * (s ^ 2)⁻¹ := by ring
        calc
          ‖crossFactor Δ_phi z‖ *
              ‖deriv (deriv f) w' * (deriv crossW z) ^ 2 +
                deriv f w' * deriv (deriv crossW) z‖
            ≤ ‖crossFactor Δ_phi z‖ *
                ((16 / r_c ^ 2 + 2 / r_c) * K_gap * Real.exp (h' * w'.re) * (s ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left h_sub3 (norm_nonneg _)
          _ = (16 / r_c ^ 2 + 2 / r_c) * K_gap * (s ^ 2)⁻¹ *
                (‖crossFactor Δ_phi z‖ * Real.exp (h' * w'.re)) := by ring
          _ ≤ (16 / r_c ^ 2 + 2 / r_c) * K_gap * (s ^ 2)⁻¹ *
                ((4 : ℝ) ^ Δ_phi * s ^ (2 * (h' - Δ_phi))) :=
              mul_le_mul_of_nonneg_left h_cf_z_exp (by positivity)
          _ = (16 / r_c ^ 2 + 2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by ring
      calc
        ‖deriv (deriv (crossFactor Δ_phi)) z * f w' +
            2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
            crossFactor Δ_phi z *
              (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
                deriv f w' * deriv (deriv crossW) z)‖
          ≤ (‖deriv (deriv (crossFactor Δ_phi)) z * f w'‖ +
              ‖2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z)‖) +
            ‖crossFactor Δ_phi z *
              (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
                deriv f w' * deriv (deriv crossW) z)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) +
              (8 * |Δ_phi| / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹)) +
              (16 / r_c ^ 2 + 2 / r_c) * (4 : ℝ) ^ Δ_phi * K_gap *
                (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) :=
            add_le_add (add_le_add ht1 ht2) ht3
        _ = (4 : ℝ) ^ Δ_phi * K_gap *
              ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) + 8 * |Δ_phi| / r_c + 16 / r_c ^ 2 + 2 / r_c) *
              (s ^ (2 * (h' - Δ_phi)) * (s ^ 2)⁻¹) := by ring
        _ = (4 : ℝ) ^ Δ_phi * K_gap *
              ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) + 8 * |Δ_phi| / r_c + 16 / r_c ^ 2 + 2 / r_c) *
              s ^ (2 * (h' - Δ_phi) - 2) := by rw [hs_rpow2]
    calc
      ‖crossFactor Δ_phi wl‖ *
          ‖deriv (deriv (crossFactor Δ_phi)) z * f w' +
            2 * deriv (crossFactor Δ_phi) z * (deriv f w' * deriv crossW z) +
            crossFactor Δ_phi z *
              (deriv (deriv f) w' * (deriv crossW z) ^ 2 +
                deriv f w' * deriv (deriv crossW) z)‖
        ≤ K_wl *
            ((4 : ℝ) ^ Δ_phi * K_gap *
              ((2 * |Δ_phi| + 4 * Δ_phi ^ 2) + 8 * |Δ_phi| / r_c + 16 / r_c ^ 2 + 2 / r_c) *
              s ^ (2 * (h' - Δ_phi) - 2)) :=
          mul_le_mul h_cf_wl_le h_inner2 (norm_nonneg _) hK_wl_pos.le
      _ = B₂ * s ^ (2 * (h' - Δ_phi) - 2) := by dsimp [B₂]; ring
      _ ≤ B₂ * (M_scale2 * u ^ (2 * (h' - Δ_phi) - 2)) :=
          mul_le_mul_of_nonneg_left (hs_u_scale _) hB₂_nonneg
      _ = (B₂ * M_scale2) * u ^ (2 * (h' - Δ_phi) - 2) := by ring

/-- Continuity of `x ↦ transmuteInnerKernel wr x * transmuteInnerDiff (tChannelRemainder M Δ_phi wl) wr x`
on `(0, 1)` for $w_l, w_r \in \operatorname{UcDisk}$. -/
theorem continuousOn_transmuteInner_tChannelRemainder {ν Δ_phi : ℝ}
    (M : MonomialFourPointData) (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ContinuousOn
      (fun x : ℝ =>
        transmuteInnerKernel wr x * transmuteInnerDiff (tChannelRemainder M Δ_phi wl) wr x)
      (Ioo (0 : ℝ) 1) := by
  let R := tChannelRemainder M Δ_phi wl
  have hR : DifferentiableOn ℂ R UcDisk :=
    differentiableOn_tChannelRemainder M corr hν hM hwl
  have hR1 : DifferentiableOn ℂ (deriv R) UcDisk := hR.deriv isOpen_UcDisk
  have hR2 : DifferentiableOn ℂ (deriv (deriv R)) UcDisk := hR1.deriv isOpen_UcDisk
  intro s hs
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  set z : ℂ := wr + (Real.log s : ℂ)
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  have h_k_cont : ContinuousAt (transmuteInnerKernel wr) s := by
    have h1 : ContinuousAt (fun x : ℝ => x ^ (-1 / 2 : ℝ)) s :=
      continuousAt_id.rpow_const (Or.inl hs0.ne')
    have h2 : ContinuousAt (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) s :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl hs1.ne')
    have h3 : ContinuousAt
        (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (2 * wr)) ^ (-1 / 2 : ℂ)) s :=
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
        continuousAt_const
        (one_sub_mul_exp_two_mul_mem_slitPlane hwr ⟨hs.1.le, hs.2.le⟩)
    exact (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2)).mul h3
  have h_log : ContinuousAt (fun x : ℝ => wr + (Real.log x : ℂ)) s :=
    continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hs0.ne'))
  have hd1_cont : ContinuousAt
      (fun x : ℝ => deriv R (wr + (Real.log x : ℂ))) s :=
    ContinuousAt.comp (g := deriv R) (f := fun x : ℝ => wr + (Real.log x : ℂ))
      ((hR1 z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).continuousAt h_log
  have hd2_cont : ContinuousAt
      (fun x : ℝ => deriv (deriv R) (wr + (Real.log x : ℂ))) s :=
    ContinuousAt.comp (g := deriv (deriv R)) (f := fun x : ℝ => wr + (Real.log x : ℂ))
      ((hR2 z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).continuousAt h_log
  have hz_sub : 1 - (s : ℂ) * Complex.exp wr ≠ 0 := one_sub_mul_exp_ne_zero hwr hs
  have h_rat1 : ContinuousAt
      (fun x : ℝ => (1 + (x : ℂ) * Complex.exp wr) / (1 - (x : ℂ) * Complex.exp wr)) s :=
    (continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).div
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) hz_sub
  have h_rat2 : ContinuousAt
      (fun x : ℝ => 2 * (x : ℂ) * Complex.exp wr / (1 - (x : ℂ) * Complex.exp wr) ^ 2) s :=
    ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul
      continuousAt_const).div
      ((continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).pow 2)
      (pow_ne_zero 2 hz_sub)
  have h_diff_cont : ContinuousAt (transmuteInnerDiff R wr) s := by
    unfold transmuteInnerDiff
    exact (continuousAt_const.mul ((h_rat1.mul hd2_cont).add (h_rat2.mul hd1_cont))).sub
      (continuousAt_const.mul hd1_cont)
  exact (h_k_cont.mul h_diff_cont).continuousWithinAt

/-- **Integrability of `transmuteInnerKernel * transmuteInnerDiff (tChannelRemainder)` on `(0, 1)`**:
Because $w_r \in \operatorname{UcDisk}$ has $\operatorname{Re} w_r < 0$, the ball
$\overline{B}(w_r + \log x, -\operatorname{Re} w_r / 2)$ lies in the half-plane
$\operatorname{Re} \zeta \le \operatorname{Re} w_r / 2 < 0$ for all $x \in (0, 1)$, so the first
and second derivatives of `tChannelRemainder M Δ_phi wl` are uniformly bounded on $(0, 1)$, and
the integrand is dominated by a constant multiple of the integrable Beta kernel
$x^{-1/2} (1 - x)^{-1/2}$. -/
theorem integrableOn_transmuteInner_tChannelRemainder {ν Δ_phi : ℝ}
    (M : MonomialFourPointData) (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    IntegrableOn
      (fun x : ℝ =>
        transmuteInnerKernel wr x * transmuteInnerDiff (tChannelRemainder M Δ_phi wl) wr x)
      (Ioo (0 : ℝ) 1) volume := by
  let R := tChannelRemainder M Δ_phi wl
  have hR : DifferentiableOn ℂ R UcDisk :=
    differentiableOn_tChannelRemainder M corr hν hM hwl
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hwr_re : wr.re < 0 := mem_UcDisk_iff.mp hwr
  set δ : ℝ := -wr.re / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hwr_half_neg : wr.re / 2 < 0 := by linarith
  have h_1_exp_wl_pos : 0 < 1 - Real.exp wl.re :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hwl_re)
  have h_1_exp_wr2_pos : 0 < 1 - Real.exp (wr.re / 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hwr_half_neg)
  set M_R : ℝ :=
    M.evalReal wl.re (wr.re / 2) +
      (4 : ℝ) ^ Δ_phi * (1 - Real.exp wl.re) ^ (-2 * Δ_phi) *
        ((4 : ℝ) ^ Δ_phi * (1 - Real.exp (wr.re / 2)) ^ (-2 * Δ_phi))
  have hM_R_nonneg : 0 ≤ M_R := by
    dsimp [M_R]
    have : 0 ≤ M.evalReal wl.re (wr.re / 2) := M.evalReal_nonneg _ _
    positivity
  have hR_bound : ∀ ζ : ℂ, ζ.re ≤ wr.re / 2 → ‖R ζ‖ ≤ M_R := by
    intro ζ hζ_re
    have hζ : ζ ∈ UcDisk := by rw [mem_UcDisk_iff]; linarith
    have h_ev : ‖M.eval wl ζ‖ ≤ M.evalReal wl.re (wr.re / 2) :=
      (M.norm_eval_le_evalReal hwl hζ).trans
        (M.evalReal_mono_right hwl_re hζ hwr_half_neg hζ_re)
    have h_cf1 := norm_crossFactor_le_of_re_le hΔ hwl_re hwl le_rfl
    have h_cf2 := norm_crossFactor_le_of_re_le hΔ hwr_half_neg hζ hζ_re
    dsimp [R, tChannelRemainder, crossIdentity]
    calc
      ‖M.eval wl ζ - crossFactor Δ_phi wl * crossFactor Δ_phi ζ‖
        ≤ ‖M.eval wl ζ‖ + ‖crossFactor Δ_phi wl * crossFactor Δ_phi ζ‖ := norm_sub_le _ _
      _ = ‖M.eval wl ζ‖ + ‖crossFactor Δ_phi wl‖ * ‖crossFactor Δ_phi ζ‖ := by rw [norm_mul]
      _ ≤ M_R := add_le_add h_ev (mul_le_mul h_cf1 h_cf2 (norm_nonneg _) (by positivity))
  set D1 : ℝ := M_R / δ
  set D2 : ℝ := 4 * M_R / δ ^ 2
  have hD1_nonneg : 0 ≤ D1 := by positivity
  have hD2_nonneg : 0 ≤ D2 := by positivity
  have h_1_sub_exp_pos : 0 < 1 - Real.exp wr.re :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hwr_re)
  have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * wr.re) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  set C_diff : ℝ :=
    4 * (2 / (1 - Real.exp wr.re) * D2 + 2 / (1 - Real.exp wr.re) ^ 2 * D1) + 2 * D1
  set C_k : ℝ := (1 - Real.exp (2 * wr.re)) ^ (-1 / 2 : ℝ)
  have h_dom : IntegrableOn (fun s : ℝ => (C_k * C_diff) * betaKernel 1 0 s)
      (Ioo (0 : ℝ) 1) volume :=
    (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul (C_k * C_diff)
  refine h_dom.mono'
    ((continuousOn_transmuteInner_tChannelRemainder M corr hν hM hwl hwr).aestronglyMeasurable
      measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  set z : ℂ := wr + (Real.log s : ℂ)
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz_le : z.re ≤ wr.re := by
    have hre : z.re = wr.re + Real.log s := by simp [z, Complex.add_re]
    linarith
  have hz : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz_le.trans_lt hwr_re)
  have h_ball_re : ∀ ζ ∈ Metric.closedBall z δ, ζ.re ≤ wr.re / 2 := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have h1 : (ζ - z).re ≤ δ := (Complex.re_le_norm _).trans hζ
    have h2 : (ζ - z).re = ζ.re - z.re := Complex.sub_re _ _
    dsimp [δ] at h1
    linarith
  have h_ball_sub : Metric.closedBall z δ ⊆ UcDisk := by
    intro ζ hζ
    rw [mem_UcDisk_iff]
    linarith [h_ball_re ζ hζ]
  have hd1_le : ‖deriv R z‖ ≤ D1 :=
    norm_deriv_le_of_ball_bound isOpen_UcDisk hR hδ_pos h_ball_sub
      (fun ζ hζ => hR_bound ζ (h_ball_re ζ hζ))
  have hd2_le : ‖deriv (deriv R) z‖ ≤ D2 :=
    norm_deriv2_le_of_ball_bound isOpen_UcDisk hR hδ_pos h_ball_sub
      (fun ζ hζ => hR_bound ζ (h_ball_re ζ hζ))
  have h_k_le : ‖transmuteInnerKernel wr s‖ ≤ C_k * betaKernel 1 0 s := by
    rw [norm_transmuteInnerKernel_eq hwr hs]
    have h_norm_sub : 1 - Real.exp (2 * wr.re) ≤ ‖1 - (s : ℂ) * Complex.exp (2 * wr)‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp (2 * wr))
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
        Complex.norm_exp] at h1
      have hre : (2 * wr).re = 2 * wr.re := by simp [Complex.mul_re]
      rw [hre] at h1
      have h_le : s * Real.exp (2 * wr.re) ≤ 1 * Real.exp (2 * wr.re) :=
        mul_le_mul_of_nonneg_right hs.2.le (by positivity)
      linarith
    have h_rpow :
        ‖1 - (s : ℂ) * Complex.exp (2 * wr)‖ ^ (-1 / 2 : ℝ) ≤ C_k :=
      Real.rpow_le_rpow_of_nonpos h_1_sub_exp2_pos h_norm_sub (by norm_num)
    have h_bk : s ^ (-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) = betaKernel 1 0 s := by
      dsimp [betaKernel]; congr 2; norm_num
    rw [h_bk, mul_comm]
    exact mul_le_mul_of_nonneg_right h_rpow (betaKernel_nonneg 1 0 hs)
  have h_diff_le : ‖transmuteInnerDiff R wr s‖ ≤ C_diff := by
    dsimp [transmuteInnerDiff]
    have hz_def : wr + (Real.log s : ℂ) = z := rfl
    rw [hz_def]
    have h_sub_ge : 1 - Real.exp wr.re ≤ ‖1 - (s : ℂ) * Complex.exp wr‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp wr)
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
        Complex.norm_exp] at h1
      have h_le : s * Real.exp wr.re ≤ 1 * Real.exp wr.re :=
        mul_le_mul_of_nonneg_right hs.2.le (by positivity)
      linarith
    have h_exp_le1 : ‖Complex.exp wr‖ ≤ 1 := by
      rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hwr_re.le
    have h_s_exp_le1 : ‖(s : ℂ) * Complex.exp wr‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs.2.le).trans h_exp_le1
    have h_1_sub_w_le2 : ‖1 - Complex.exp wr‖ ≤ 2 := by
      have h1 := norm_sub_le (1 : ℂ) (Complex.exp wr)
      rw [norm_one] at h1; linarith
    have h_1_add_w_le2 : ‖1 + Complex.exp wr‖ ≤ 2 := by
      have h1 := norm_add_le (1 : ℂ) (Complex.exp wr)
      rw [norm_one] at h1; linarith
    have h_1_add_sw_le2 : ‖1 + (s : ℂ) * Complex.exp wr‖ ≤ 2 := by
      have h1 := norm_add_le (1 : ℂ) ((s : ℂ) * Complex.exp wr)
      rw [norm_one] at h1; linarith
    have h_rat1_le : ‖(1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr)‖ ≤
        2 / (1 - Real.exp wr.re) := by
      rw [norm_div]
      exact div_le_div₀ (by norm_num) h_1_add_sw_le2 h_1_sub_exp_pos h_sub_ge
    have h_rat2_le :
        ‖2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2‖ ≤
          2 / (1 - Real.exp wr.re) ^ 2 := by
      rw [mul_assoc, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
      have h_num : 2 * ‖(s : ℂ) * Complex.exp wr‖ ≤ 2 := by linarith
      have h_den : (1 - Real.exp wr.re) ^ 2 ≤ ‖1 - (s : ℂ) * Complex.exp wr‖ ^ 2 :=
        pow_le_pow_left₀ h_1_sub_exp_pos.le h_sub_ge 2
      exact div_le_div₀ (by norm_num) h_num (sq_pos_of_pos h_1_sub_exp_pos) h_den
    have h_sq1 : ‖(1 - Complex.exp wr) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [← h2]
      exact pow_le_pow_left₀ (norm_nonneg _) h_1_sub_w_le2 2
    have h_sq2 : ‖(1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2‖ ≤ 2 := by
      have h_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [norm_mul, norm_pow, h_half]
      have h_pow : ‖1 + Complex.exp wr‖ ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_1_add_w_le2 2
      linarith
    have h_p1 :
        ‖(1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv R) z +
          2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
            deriv R z‖ ≤
        2 / (1 - Real.exp wr.re) * D2 + 2 / (1 - Real.exp wr.re) ^ 2 * D1 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul h_rat1_le hd2_le (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul h_rat2_le hd1_le (norm_nonneg _) (by positivity)
    have h_p2 :
        ‖(1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv R z‖ ≤ 2 * D1 := by
      rw [norm_mul]
      exact mul_le_mul h_sq2 hd1_le (norm_nonneg _) (by norm_num)
    refine (norm_sub_le _ _).trans (add_le_add ?_ h_p2)
    rw [norm_mul]
    exact mul_le_mul h_sq1 h_p1 (norm_nonneg _) (by norm_num)
  rw [norm_mul]
  calc
    ‖transmuteInnerKernel wr s‖ * ‖transmuteInnerDiff R wr s‖
      ≤ (C_k * betaKernel 1 0 s) * C_diff :=
        mul_le_mul h_k_le h_diff_le (norm_nonneg _)
          (mul_nonneg (by positivity) (betaKernel_nonneg 1 0 hs))
    _ = (C_k * C_diff) * betaKernel 1 0 s := by ring

/-! ## Section 4: `LightconeBlockFourPointData.AgreesWithCorrelator` & Quantitative 1D Lightcone-Block Bootstrap -/

/-- For all $H > 1/2$, comparing `integral_betaKernel hH 1` with $\int_0^1 s^{H - 1/2}\, ds = (H + 1/2)^{-1}$
gives the lower bound
$$\frac{H (H - 1/2)}{\sqrt{\pi} (H + 1/2)} \le \operatorname{transmuteWeight}(H).$$ -/
lemma transmuteWeight_ge_of_gt_half {H : ℝ} (hH : 1 / 2 < H) :
    H * (H - 1 / 2) / (Real.sqrt π * (H + 1 / 2)) ≤ transmuteWeight H := by
  have h_beta := integral_betaKernel hH 1
  have h_poch1 : realPochhammer (H - 1 / 2) 1 = H - 1 / 2 := by
    rw [realPochhammer_succ, realPochhammer_zero, one_mul, Nat.cast_zero, add_zero]
  have h_poch2 : realPochhammer H 1 = H := by
    rw [realPochhammer_succ, realPochhammer_zero, one_mul, Nat.cast_zero, add_zero]
  rw [h_poch1, h_poch2] at h_beta
  have h_tw := transmuteWeight_eq_mul_transmuteCoreWeight hH
  have hH_pos : 0 < H := by linarith
  have hH_sub_pos : 0 < H - 1 / 2 := by linarith
  have hH_add_pos : 0 < H + 1 / 2 := by linarith
  have h_beta_eq :
      (∫ s in Ioo (0 : ℝ) 1, betaKernel H 1 s) =
        Real.sqrt π * transmuteWeight H / (H * (H - 1 / 2)) := by
    rw [h_beta, h_tw]
    field_simp [hH_pos.ne', hH_sub_pos.ne']
  have h_rpow_int : IntervalIntegrable (fun s : ℝ => s ^ (H - 1 / 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h_rpow_ioo : IntegrableOn (fun s : ℝ => s ^ (H - 1 / 2)) (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h_rpow_int
  have h_mono :
      (∫ s in Ioo (0 : ℝ) 1, s ^ (H - 1 / 2)) ≤
        ∫ s in Ioo (0 : ℝ) 1, betaKernel H 1 s := by
    refine setIntegral_mono_on h_rpow_ioo (integrableOn_betaKernel hH 1) measurableSet_Ioo
      fun s hs => ?_
    dsimp [betaKernel]
    have h_exp : H + ((1 : ℕ) : ℝ) - 3 / 2 = H - 1 / 2 := by push_cast; ring
    rw [h_exp]
    have h1_le : 1 ≤ (1 - s) ^ (-1 / 2 : ℝ) := by
      have h := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hs.2)
        (by linarith [hs.1] : 1 - s ≤ 1)
        (by norm_num : (-1 / 2 : ℝ) ≤ 0)
      rwa [Real.one_rpow] at h
    exact le_mul_of_one_le_right (Real.rpow_nonneg hs.1.le _) h1_le
  have h_eval_rpow :
      (∫ s in Ioo (0 : ℝ) 1, s ^ (H - 1 / 2)) = (H + 1 / 2)⁻¹ := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < H - 1 / 2))]
    have h_add : H - 1 / 2 + 1 = H + 1 / 2 := by ring
    rw [h_add, Real.one_rpow, Real.zero_rpow hH_add_pos.ne', sub_zero, one_div]
  rw [h_eval_rpow, h_beta_eq, inv_eq_one_div,
    div_le_div_iff₀ hH_add_pos (mul_pos hH_pos hH_sub_pos)] at h_mono
  rw [div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hH_add_pos)]
  linarith

/-- For all $H \ge 1$, $1 \le 4\sqrt{\pi} \, \operatorname{transmutePosWeight}(H)$. -/
theorem one_le_four_sqrt_pi_mul_transmutePosWeight {H : ℝ} (hH : 1 ≤ H) :
    1 ≤ 4 * Real.sqrt π * transmutePosWeight H := by
  have hH_half : 1 / 2 < H := by linarith
  rw [transmutePosWeight_of_gt hH_half]
  have h_ge := transmuteWeight_ge_of_gt_half hH_half
  have h_sqrt_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hH_add_pos : 0 < H + 1 / 2 := by linarith
  have h_4 : 1 ≤ 4 * Real.sqrt π * (H * (H - 1 / 2) / (Real.sqrt π * (H + 1 / 2))) := by
    have h_eq :
        4 * Real.sqrt π * (H * (H - 1 / 2) / (Real.sqrt π * (H + 1 / 2))) =
          4 * H * (H - 1 / 2) / (H + 1 / 2) := by
      field_simp [h_sqrt_pos.ne', hH_add_pos.ne']
    rw [h_eq, one_le_div hH_add_pos]
    nlinarith
  exact h_4.trans (mul_le_mul_of_nonneg_left h_ge (by positivity))

/-- On $[h_{\mathrm{gap}}, \infty)$ with $h_{\mathrm{gap}} > 0$, $|\operatorname{transmuteWeight}(H)|$
is bounded by $M_0 + \operatorname{transmutePosWeight}(H)$ for a constant $M_0 \ge 0$. -/
lemma exists_abs_transmuteWeight_le_add_transmutePosWeight {h_gap : ℝ} (hh_gap : 0 < h_gap) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ {H : ℝ}, h_gap ≤ H →
      |transmuteWeight H| ≤ M₀ + transmutePosWeight H := by
  have h_cont : ContinuousOn transmuteWeight (Icc h_gap 1) := by
    intro H hH
    have hH_pos : 0 < H := lt_of_lt_of_le hh_gap hH.1
    unfold transmuteWeight
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ (continuousAt_real_Gamma_of_pos hH_pos)
      (Real.Gamma_pos_of_pos hH_pos).ne'
    refine (continuousAt_id.sub continuousAt_const).mul ?_
    exact (continuousAt_real_Gamma_of_pos (by linarith)).comp
      (continuousAt_id.add continuousAt_const)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h_cont
  refine ⟨max M 0, le_max_right M 0, fun {H} hH => ?_⟩
  rcases le_or_gt H 1 with hH1 | hH1
  · have h_mem : H ∈ Icc h_gap 1 := ⟨hH, hH1⟩
    have h_bd : |transmuteWeight H| ≤ max M 0 :=
      (Real.norm_eq_abs _ ▸ hM H h_mem).trans (le_max_left M 0)
    linarith [transmutePosWeight_nonneg H]
  · have hH_half : 1 / 2 < H := by linarith
    rw [transmutePosWeight_of_gt hH_half, abs_of_pos (transmuteWeight_pos hH_half)]
    linarith [le_max_right M 0]

lemma continuous_realPochhammer (n : ℕ) :
    Continuous (fun x : ℝ => realPochhammer x n) := by
  induction n with
  | zero => simp [realPochhammer_zero, continuous_const]
  | succ m ih =>
    have h_eq : (fun x : ℝ => realPochhammer x (m + 1)) =
        fun x : ℝ => realPochhammer x m * (x + (m : ℝ)) := by
      ext x; exact realPochhammer_succ x m
    rw [h_eq]
    exact ih.mul (continuous_id.add continuous_const)

lemma measurable_block1dCoeff (n : ℕ) :
    Measurable (fun h : ℝ => block1dCoeff h n) := by
  unfold block1dCoeff
  have h1 : Measurable (fun h : ℝ => realPochhammer h n) :=
    (continuous_realPochhammer n).measurable
  have h2 : Measurable (fun h : ℝ => realPochhammer (h + 1 / 2) n) :=
    ((continuous_realPochhammer n).comp (continuous_id.add continuous_const)).measurable
  exact (h1.mul measurable_const).div (h2.mul measurable_const)

lemma measurable_block1dTerm_shift (J : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun h : ℝ => block1dTerm (h + J) n z) := by
  unfold block1dTerm
  have h0 : Measurable (fun h : ℝ => h + J) := measurable_id.add measurable_const
  have h1 : Measurable (fun h : ℝ => (block1dCoeff (h + J) n : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_block1dCoeff n).comp h0)
  have h2 : Measurable (fun h : ℝ => Complex.exp (((h + J + 2 * (n : ℝ) : ℝ) : ℂ) * z)) := by
    fun_prop
  exact h1.mul h2

lemma measurable_block1dDeriv1Term_shift (J : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun h : ℝ => block1dDeriv1Term (h + J) n z) := by
  unfold block1dDeriv1Term
  have h0 : Measurable (fun h : ℝ => h + J) := measurable_id.add measurable_const
  have h1 : Measurable (fun h : ℝ => block1dCoeff (h + J) n) :=
    (measurable_block1dCoeff n).comp h0
  have h2 : Measurable (fun h : ℝ => h + J + 2 * (n : ℝ)) := by fun_prop
  have h3 : Measurable (fun h : ℝ => ((block1dCoeff (h + J) n * (h + J + 2 * (n : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (h1.mul h2)
  have h4 : Measurable (fun h : ℝ => Complex.exp (((h + J + 2 * (n : ℝ) : ℝ) : ℂ) * z)) := by
    fun_prop
  exact h3.mul h4

lemma measurable_block1dDeriv2Term_shift (J : ℝ) (n : ℕ) (z : ℂ) :
    Measurable (fun h : ℝ => block1dDeriv2Term (h + J) n z) := by
  unfold block1dDeriv2Term
  have h0 : Measurable (fun h : ℝ => h + J) := measurable_id.add measurable_const
  have h1 : Measurable (fun h : ℝ => block1dCoeff (h + J) n) :=
    (measurable_block1dCoeff n).comp h0
  have h2 : Measurable (fun h : ℝ => (h + J + 2 * (n : ℝ)) ^ 2) := by fun_prop
  have h3 : Measurable
      (fun h : ℝ => ((block1dCoeff (h + J) n * (h + J + 2 * (n : ℝ)) ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (h1.mul h2)
  have h4 : Measurable (fun h : ℝ => Complex.exp (((h + J + 2 * (n : ℝ) : ℝ) : ℂ) * z)) := by
    fun_prop
  exact h3.mul h4

lemma measurable_block1dDeriv1Term_prod (J : ℝ) (n : ℕ) (w : ℂ) :
    Measurable (fun p : ℝ × ℝ => block1dDeriv1Term (p.2 + J) n (w + (Real.log p.1 : ℂ))) := by
  unfold block1dDeriv1Term
  have h0 : Measurable (fun p : ℝ × ℝ => p.2 + J) := measurable_snd.add measurable_const
  have h1 : Measurable (fun p : ℝ × ℝ => block1dCoeff (p.2 + J) n) :=
    (measurable_block1dCoeff n).comp h0
  have h2 : Measurable (fun p : ℝ × ℝ => p.2 + J + 2 * (n : ℝ)) := by fun_prop
  have h3 : Measurable
      (fun p : ℝ × ℝ => ((block1dCoeff (p.2 + J) n * (p.2 + J + 2 * (n : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (h1.mul h2)
  have h4 : Measurable
      (fun p : ℝ × ℝ =>
        Complex.exp (((p.2 + J + 2 * (n : ℝ) : ℝ) : ℂ) * (w + (Real.log p.1 : ℂ)))) := by
    fun_prop
  exact h3.mul h4

lemma measurable_block1dDeriv2Term_prod (J : ℝ) (n : ℕ) (w : ℂ) :
    Measurable (fun p : ℝ × ℝ => block1dDeriv2Term (p.2 + J) n (w + (Real.log p.1 : ℂ))) := by
  unfold block1dDeriv2Term
  have h0 : Measurable (fun p : ℝ × ℝ => p.2 + J) := measurable_snd.add measurable_const
  have h1 : Measurable (fun p : ℝ × ℝ => block1dCoeff (p.2 + J) n) :=
    (measurable_block1dCoeff n).comp h0
  have h2 : Measurable (fun p : ℝ × ℝ => (p.2 + J + 2 * (n : ℝ)) ^ 2) := by fun_prop
  have h3 : Measurable
      (fun p : ℝ × ℝ => ((block1dCoeff (p.2 + J) n * (p.2 + J + 2 * (n : ℝ)) ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (h1.mul h2)
  have h4 : Measurable
      (fun p : ℝ × ℝ =>
        Complex.exp (((p.2 + J + 2 * (n : ℝ) : ℝ) : ℂ) * (w + (Real.log p.1 : ℂ)))) := by
    fun_prop
  exact h3.mul h4

/-- Orthogonality of even non-zero Fourier modes on the half-period $[-\pi/2, \pi/2]$:
for any integer $k \ne 0$,
$$\int_{-\pi/2}^{\pi/2} e^{-2 k i \theta} \, d\theta = 0.$$ -/
lemma integral_exp_neg_two_mul_int_mul_I {k : ℤ} (hk : k ≠ 0) :
    (∫ θ in (-π / 2)..(π / 2), Complex.exp (- ((2 * k : ℤ) : ℂ) * (θ : ℂ) * I)) = 0 := by
  set n : ℤ := - (2 * k)
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hn_c : (n : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) I_ne_zero
  have h_congr :
      (fun θ : ℝ => Complex.exp (- ((2 * k : ℤ) : ℂ) * (θ : ℂ) * I)) =
        fun θ : ℝ => Complex.exp ((n : ℂ) * (θ : ℂ) * I) := by
    ext θ; dsimp [n]; push_cast; ring_nf
  rw [h_congr]
  have h_deriv : ∀ θ ∈ uIcc (-π / 2) (π / 2),
      HasDerivAt (fun x : ℝ => Complex.exp ((n : ℂ) * (x : ℂ) * I) / ((n : ℂ) * I))
        (Complex.exp ((n : ℂ) * (θ : ℂ) * I)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun x : ℝ => (n : ℂ) * (x : ℂ) * I) ((n : ℂ) * I) θ := by
      simpa [mul_assoc] using
        (((hasDerivAt_id θ).ofReal_comp).const_mul (n : ℂ)).mul_const I
    simpa [mul_div_cancel_right₀ _ hn_c] using (h1.cexp).div_const ((n : ℂ) * I)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv
    ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  have h_per :
      Complex.exp ((n : ℂ) * ((π / 2 : ℝ) : ℂ) * I) =
        Complex.exp ((n : ℂ) * ((-π / 2 : ℝ) : ℂ) * I) := by
    have h_eq :
        (n : ℂ) * ((π / 2 : ℝ) : ℂ) * I =
          (n : ℂ) * ((-π / 2 : ℝ) : ℂ) * I + ((-k : ℤ) : ℂ) * (2 * π * I) := by
      dsimp [n]; push_cast; ring
    rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h_per, sub_self]

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

lemma ae_nonneg (J : ℤ) : ∀ᵐ h : ℝ ∂(L.muLC J), 0 ≤ h := by
  have h_unit : ∀ᵐ h : ℝ ∂(L.muLC J), h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (L.support_unitary J)
  filter_upwards [h_unit] with h hh
  exact not_lt.mp fun hlt => hh (Or.inl hlt)

lemma ae_add_nonneg (J : ℤ) : ∀ᵐ h : ℝ ∂(L.muLC J), 0 ≤ h + (J : ℝ) := by
  have h_unit : ∀ᵐ h : ℝ ∂(L.muLC J), h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (L.support_unitary J)
  filter_upwards [h_unit] with h hh
  exact not_lt.mp fun hlt => hh (Or.inr hlt)

/-- For every spin $J \ge 1$ and $\sigma_l < 0, \sigma_r < 0$, `L.integrable_transmute`
automatically implies integrability of the unweighted real monomial `monomialTermReal h J σl σr`
under `L.muLC J` because $1 \le 4\sqrt{\pi} \, \operatorname{transmutePosWeight}(h + J)$. -/
theorem integrable_monomialTermReal_of_pos {J : ℤ} (hJ : 1 ≤ J)
    {σl σr : ℝ} (hσl : σl < 0) (hσr : σr < 0) :
    Integrable (fun h : ℝ => monomialTermReal h J σl σr) (L.muLC J) := by
  have h_dom := (L.integrable_transmute hσl hσr J).const_mul (4 * Real.sqrt π)
  have h_meas : AEStronglyMeasurable (fun h : ℝ => monomialTermReal h J σl σr) (L.muLC J) := by
    unfold monomialTermReal; fun_prop
  refine h_dom.mono' h_meas ?_
  filter_upwards [L.ae_nonneg J] with h hh
  rw [Real.norm_of_nonneg (monomialTermReal_nonneg h J σl σr)]
  have hJ_real : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hH : 1 ≤ h + (J : ℝ) := by linarith
  have h_le := one_le_four_sqrt_pi_mul_transmutePosWeight hH
  calc
    monomialTermReal h J σl σr
      = 1 * monomialTermReal h J σl σr := (one_mul _).symm
    _ ≤ (4 * Real.sqrt π * transmutePosWeight (h + (J : ℝ))) * monomialTermReal h J σl σr :=
        mul_le_mul_of_nonneg_right h_le (monomialTermReal_nonneg h J σl σr)
    _ = 4 * Real.sqrt π * (transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr) := by
        ring

/-- Unified integrability of `monomialTermReal h (2 * k) σl σr` under `L.muLC (2 * k)` for all
$k \in \mathbb{N}$. -/
theorem integrable_monomialTermReal_even
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {σl σr : ℝ} (hσl : σl < 0) (hσr : σr < 0) (k : ℕ) :
    Integrable (fun h : ℝ => monomialTermReal h (2 * (k : ℤ)) σl σr) (L.muLC (2 * (k : ℤ))) := by
  cases k with
  | zero => simpa using h_int0 hσl hσr
  | succ m =>
    exact L.integrable_monomialTermReal_of_pos (by omega : (1 : ℤ) ≤ 2 * ((m + 1 : ℕ) : ℤ))
      hσl hσr

/-- Spin-summability over $k \in \mathbb{N}$ of the unweighted real monomial integrals
$\int \operatorname{monomialTermReal} h\, (2k)\, \sigma_l\, \sigma_r \, d\mu^{\mathrm{LC}}_{2k}(h)$
derived from `L.summable_transmute`. -/
theorem summable_integral_monomialTermReal_even
    (_h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {σl σr : ℝ} (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun k : ℕ =>
      ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) σl σr ∂(L.muLC (2 * (k : ℤ)))) := by
  rw [← summable_nat_add_iff 1]
  have h_inj : Function.Injective (fun m : ℕ => (2 * ((m + 1 : ℕ) : ℤ) : ℤ)) := by
    intro a b hab; dsimp at hab; omega
  have h_sum_trans := ((L.summable_transmute hσl hσr).comp_injective h_inj).mul_left
    (4 * Real.sqrt π)
  refine Summable.of_nonneg_of_le
    (fun m => integral_nonneg fun h => monomialTermReal_nonneg h _ σl σr)
    (fun m => ?_) h_sum_trans
  dsimp [Function.comp_def]
  rw [← integral_const_mul]
  have hJ : (1 : ℤ) ≤ 2 * ((m + 1 : ℕ) : ℤ) := by omega
  refine integral_mono_ae (L.integrable_monomialTermReal_of_pos hJ hσl hσr)
    ((L.integrable_transmute hσl hσr (2 * ((m + 1 : ℕ) : ℤ))).const_mul (4 * Real.sqrt π)) ?_
  filter_upwards [L.ae_nonneg (2 * ((m + 1 : ℕ) : ℤ))] with h hh
  have hJ_real : (1 : ℝ) ≤ ((2 * ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hJ
  have hH : 1 ≤ h + ((2 * ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by linarith
  have h_le := one_le_four_sqrt_pi_mul_transmutePosWeight hH
  calc
    monomialTermReal h (2 * ((m + 1 : ℕ) : ℤ)) σl σr
      = 1 * monomialTermReal h (2 * ((m + 1 : ℕ) : ℤ)) σl σr := (one_mul _).symm
    _ ≤ (4 * Real.sqrt π * transmutePosWeight (h + ((2 * ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ))) *
          monomialTermReal h (2 * ((m + 1 : ℕ) : ℤ)) σl σr :=
        mul_le_mul_of_nonneg_right h_le (monomialTermReal_nonneg _ _ _ _)
    _ = 4 * Real.sqrt π *
          (transmutePosWeight (h + ((2 * ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ)) *
            monomialTermReal h (2 * ((m + 1 : ℕ) : ℤ)) σl σr) := by ring

/-- $\sigma$-finiteness of `L.muLC (2 * k)` when `monomialTermReal` is integrable. -/
lemma sigmaFinite_muLC_even
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) : SigmaFinite (L.muLC (2 * (k : ℤ))) := by
  refine ⟨⟨{
    set := fun n : ℕ => Iic (n : ℝ)
    set_mem := fun _ => trivial
    finite := fun n => ?_
    spanning := eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨⌈x⌉₊, Nat.le_ceil x⟩
  }⟩⟩
  have h_int := L.integrable_monomialTermReal_even h_int0
    (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num : (-1 / 2 : ℝ) < 0) k
  set c : ℝ := Real.exp (- (n : ℝ) - (k : ℝ))
  have hc_pos : 0 < c := Real.exp_pos _
  refine lt_of_le_of_lt (measure_mono (fun h (hh : h ≤ (n : ℝ)) => ?_))
    (h_int.measure_ge_lt_top hc_pos)
  dsimp [c, monomialTermReal]
  refine Real.exp_le_exp.mpr ?_
  have h_alg :
      h * (-1 / 2 : ℝ) + (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * (-1 / 2 : ℝ) = -h - (k : ℝ) := by
    push_cast; ring
  rw [h_alg]
  linarith

/-- Spin-$2k$ contribution to the 1D collinear block expansion:
$$
\operatorname{evalCollinearSpin}(L, k, w_l, w_r) :=
  \int_{\mathbb{R}} e^{h w_l} \, \operatorname{block1d}\bigl(h + 2k, w_r\bigr) \,
    d\mu^{\mathrm{LC}}_{2k}(h).
$$ -/
noncomputable def evalCollinearSpin (k : ℕ) (wl wr : ℂ) : ℂ :=
  ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * block1d (h + 2 * (k : ℝ)) wr ∂(L.muLC (2 * (k : ℤ)))

/-- Full $s$-channel 1D collinear block expansion on $\operatorname{UcPdisk}$:
$$
\operatorname{evalCollinear}(L, w_l, w_r) :=
  1 + \sum_{k=0}^{\infty} \int_{\mathbb{R}} e^{h w_l} \,
    \operatorname{block1d}\bigl(h + 2k, w_r\bigr) \, d\mu^{\mathrm{LC}}_{2k}(h).
$$ -/
noncomputable def evalCollinear (wl wr : ℂ) : ℂ :=
  1 + ∑' k : ℕ, L.evalCollinearSpin k wl wr

/-- Spin-$2k$ contribution to the transmuted $s$-channel expansion:
$$
\operatorname{evalCollinearTransmutedSpin}(L, k, w_l, w_r) :=
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \,
    e^{h w_l + (h + 2k) w_r} \, d\mu^{\mathrm{LC}}_{2k}(h).
$$ -/
noncomputable def evalCollinearTransmutedSpin (k : ℕ) (wl wr : ℂ) : ℂ :=
  ∫ h : ℝ, (transmuteWeight (h + 2 * (k : ℝ)) : ℂ) *
    monomialTerm h (2 * (k : ℤ)) wl wr ∂(L.muLC (2 * (k : ℤ)))

/-- Full transmuted $s$-channel expansion on $\operatorname{UcPdisk}$:
$$
\operatorname{evalCollinearTransmuted}(L, w_l, w_r) :=
  \sum_{k=0}^{\infty} \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \,
    e^{h w_l + (h + 2k) w_r} \, d\mu^{\mathrm{LC}}_{2k}(h).
$$ -/
noncomputable def evalCollinearTransmuted (wl wr : ℂ) : ℂ :=
  ∑' k : ℕ, L.evalCollinearTransmutedSpin k wl wr

/-- Almost-everywhere strong measurability of `h ↦ exp (h * wl) * block1d (h + 2k) z` under
`L.muLC (2 * k)`. -/
lemma aestronglyMeasurable_collinearIntegrand (k : ℕ) (wl : ℂ) {z : ℂ} (hz : z ∈ UcDisk) :
    AEStronglyMeasurable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * block1d (h + 2 * (k : ℝ)) z)
      (L.muLC (2 * (k : ℤ))) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (N : ℕ) (h : ℝ) =>
      Complex.exp ((h : ℂ) * wl) * ∑ n ∈ Finset.range N, block1dTerm (h + 2 * (k : ℝ)) n z)
    (fun N => ?_) ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (by fun_prop) ?_
    exact Finset.measurable_sum _ fun n _ => measurable_block1dTerm_shift (2 * (k : ℝ)) n z
  · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
    have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
    exact ((summable_block1dTerm hH hz).hasSum.tendsto_sum_nat).const_mul _

/-- Almost-everywhere strong measurability of `h ↦ exp (h * wl) * deriv (block1d (h + 2k)) z` under
`L.muLC (2 * k)`. -/
lemma aestronglyMeasurable_collinearDeriv1Integrand (k : ℕ) (wl : ℂ) {z : ℂ} (hz : z ∈ UcDisk) :
    AEStronglyMeasurable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) z)
      (L.muLC (2 * (k : ℤ))) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (N : ℕ) (h : ℝ) =>
      Complex.exp ((h : ℂ) * wl) *
        ∑ n ∈ Finset.range N, block1dDeriv1Term (h + 2 * (k : ℝ)) n z)
    (fun N => ?_) ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (by fun_prop) ?_
    exact Finset.measurable_sum _ fun n _ => measurable_block1dDeriv1Term_shift (2 * (k : ℝ)) n z
  · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
    have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
    rw [deriv_block1d hH hz]
    exact ((summable_block1dDeriv1Term hH hz).hasSum.tendsto_sum_nat).const_mul _

/-- Almost-everywhere strong measurability of `h ↦ exp (h * wl) * deriv (deriv (block1d (h + 2k))) z`
under `L.muLC (2 * k)`. -/
lemma aestronglyMeasurable_collinearDeriv2Integrand (k : ℕ) (wl : ℂ) {z : ℂ} (hz : z ∈ UcDisk) :
    AEStronglyMeasurable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) z)
      (L.muLC (2 * (k : ℤ))) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (N : ℕ) (h : ℝ) =>
      Complex.exp ((h : ℂ) * wl) *
        ∑ n ∈ Finset.range N, block1dDeriv2Term (h + 2 * (k : ℝ)) n z)
    (fun N => ?_) ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (by fun_prop) ?_
    exact Finset.measurable_sum _ fun n _ => measurable_block1dDeriv2Term_shift (2 * (k : ℝ)) n z
  · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
    have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
    rw [deriv_deriv_block1d hH hz]
    exact ((summable_block1dDeriv2Term hH hz).hasSum.tendsto_sum_nat).const_mul _

/-- Integrability of `h ↦ exp (h * wl) * block1d (h + 2k) z` under `L.muLC (2 * k)`. -/
lemma integrable_collinearIntegrand
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Integrable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * block1d (h + 2 * (k : ℝ)) z)
      (L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : z.re / 2 < 0) k).const_mul
    (block1dDerivBoundConst 0 z.re)
  refine h_dom.mono' (L.aestronglyMeasurable_collinearIntegrand k wl hz) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖block1d (h + 2 * (k : ℝ)) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 0 z.re * Real.exp ((h + 2 * (k : ℝ)) * (z.re / 2))) :=
        mul_le_mul_of_nonneg_left (norm_block1d_le_exp_half hH hz_re le_rfl) (Real.exp_pos _).le
    _ = block1dDerivBoundConst 0 z.re *
          monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- Integrability of `h ↦ exp (h * wl) * deriv (block1d (h + 2k)) z` under `L.muLC (2 * k)`. -/
lemma integrable_collinearDeriv1Integrand
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Integrable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) z)
      (L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : z.re / 2 < 0) k).const_mul
    (block1dDerivBoundConst 1 z.re)
  refine h_dom.mono' (L.aestronglyMeasurable_collinearDeriv1Integrand k wl hz) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖deriv (block1d (h + 2 * (k : ℝ))) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 1 z.re * Real.exp ((h + 2 * (k : ℝ)) * (z.re / 2))) :=
        mul_le_mul_of_nonneg_left (norm_deriv_block1d_le_exp_half hH hz_re le_rfl)
          (Real.exp_pos _).le
    _ = block1dDerivBoundConst 1 z.re *
          monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- Integrability of `h ↦ exp (h * wl) * deriv (deriv (block1d (h + 2k))) z` under
`L.muLC (2 * k)`. -/
lemma integrable_collinearDeriv2Integrand
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Integrable
      (fun h : ℝ => Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) z)
      (L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : z.re / 2 < 0) k).const_mul
    (block1dDerivBoundConst 2 z.re)
  refine h_dom.mono' (L.aestronglyMeasurable_collinearDeriv2Integrand k wl hz) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖deriv (deriv (block1d (h + 2 * (k : ℝ)))) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 2 z.re * Real.exp ((h + 2 * (k : ℝ)) * (z.re / 2))) :=
        mul_le_mul_of_nonneg_left (norm_deriv_deriv_block1d_le_exp_half hH hz_re le_rfl)
          (Real.exp_pos _).le
    _ = block1dDerivBoundConst 2 z.re *
          monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- First complex derivative of `L.evalCollinearSpin k wl` under the $\mu^{\mathrm{LC}}_{2k}$-integral
on `UcDisk`. -/
theorem hasDerivAt_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    HasDerivAt (L.evalCollinearSpin k wl)
      (∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) z
        ∂(L.muLC (2 * (k : ℤ)))) z := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set s : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have hs_nhds : s ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have h_bound_int :=
    (L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : z.re / 4 < 0) k).const_mul
      (block1dDerivBoundConst 1 (z.re / 2))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (y : ℂ) (h : ℝ) => Complex.exp ((h : ℂ) * wl) * block1d (h + 2 * (k : ℝ)) y)
    (F' := fun (y : ℂ) (h : ℝ) => Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) y)
    hs_nhds
    (Filter.eventually_of_mem (isOpen_UcDisk.mem_nhds hz) fun y hy =>
      L.aestronglyMeasurable_collinearIntegrand k wl hy)
    (L.integrable_collinearIntegrand h_int0 k hwl hz)
    (L.aestronglyMeasurable_collinearDeriv1Integrand k wl hz)
    ?_ h_bound_int ?_).2
  · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
    rw [norm_mul, Complex.norm_exp]
    have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
    rw [hre]
    have hd1 := norm_deriv_block1d_le_exp_half hH (by linarith : z.re / 2 < 0) hy_re
    have h_div : z.re / 2 / 2 = z.re / 4 := by ring
    rw [h_div] at hd1
    calc
      Real.exp (h * wl.re) * ‖deriv (block1d (h + 2 * (k : ℝ))) y‖
        ≤ Real.exp (h * wl.re) *
            (block1dDerivBoundConst 1 (z.re / 2) * Real.exp ((h + 2 * (k : ℝ)) * (z.re / 4))) :=
          mul_le_mul_of_nonneg_left hd1 (Real.exp_pos _).le
      _ = block1dDerivBoundConst 1 (z.re / 2) *
            monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 4) := by
          dsimp [monomialTermReal]
          push_cast
          rw [Real.exp_add]
          ring
  · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh y hy
    have hy_mem : y ∈ UcDisk :=
      mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
    have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
    exact ((hasDerivAt_block1d hH hy_mem).differentiableAt.hasDerivAt).const_mul
      (Complex.exp ((h : ℂ) * wl))

theorem deriv_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    deriv (L.evalCollinearSpin k wl) z =
      ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) z
        ∂(L.muLC (2 * (k : ℤ))) :=
  (L.hasDerivAt_evalCollinearSpin h_int0 k hwl hz).deriv

/-- Second complex derivative of `L.evalCollinearSpin k wl` under the $\mu^{\mathrm{LC}}_{2k}$-integral
on `UcDisk`. -/
theorem deriv_deriv_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    deriv (deriv (L.evalCollinearSpin k wl)) z =
      ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) z
        ∂(L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set s : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have hs_nhds : s ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have h_bound_int :=
    (L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : z.re / 4 < 0) k).const_mul
      (block1dDerivBoundConst 2 (z.re / 2))
  have hd_int : HasDerivAt
      (fun u : ℂ =>
        ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) u
          ∂(L.muLC (2 * (k : ℤ))))
      (∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) z
        ∂(L.muLC (2 * (k : ℤ)))) z := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (y : ℂ) (h : ℝ) => Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) y)
      (F' := fun (y : ℂ) (h : ℝ) =>
        Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) y)
      hs_nhds
      (Filter.eventually_of_mem (isOpen_UcDisk.mem_nhds hz) fun y hy =>
        L.aestronglyMeasurable_collinearDeriv1Integrand k wl hy)
      (L.integrable_collinearDeriv1Integrand h_int0 k hwl hz)
      (L.aestronglyMeasurable_collinearDeriv2Integrand k wl hz)
      ?_ h_bound_int ?_).2
    · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh y hy
      have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
      have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
      rw [norm_mul, Complex.norm_exp]
      have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
      rw [hre]
      have hd2 := norm_deriv_deriv_block1d_le_exp_half hH (by linarith : z.re / 2 < 0) hy_re
      have h_div : z.re / 2 / 2 = z.re / 4 := by ring
      rw [h_div] at hd2
      calc
        Real.exp (h * wl.re) * ‖deriv (deriv (block1d (h + 2 * (k : ℝ)))) y‖
          ≤ Real.exp (h * wl.re) *
              (block1dDerivBoundConst 2 (z.re / 2) * Real.exp ((h + 2 * (k : ℝ)) * (z.re / 4))) :=
            mul_le_mul_of_nonneg_left hd2 (Real.exp_pos _).le
        _ = block1dDerivBoundConst 2 (z.re / 2) *
              monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 4) := by
            dsimp [monomialTermReal]
            push_cast
            rw [Real.exp_add]
            ring
    · filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh y hy
      have hy_mem : y ∈ UcDisk :=
        mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
      have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
      have h_ev_y :
          deriv (block1d (h + 2 * (k : ℝ))) =ᶠ[𝓝 y] block1dDeriv1 (h + 2 * (k : ℝ)) :=
        Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hy_mem) fun w hw => deriv_block1d hH hw
      have hd_y : HasDerivAt (deriv (block1d (h + 2 * (k : ℝ))))
          (deriv (deriv (block1d (h + 2 * (k : ℝ)))) y) y := by
        rw [deriv_deriv_block1d hH hy_mem]
        exact (hasDerivAt_block1dDeriv1 hH hy_mem).congr_of_eventuallyEq h_ev_y
      exact hd_y.const_mul (Complex.exp ((h : ℂ) * wl))
  have h_ev : deriv (L.evalCollinearSpin k wl) =ᶠ[𝓝 z]
      fun u : ℂ =>
        ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) u
          ∂(L.muLC (2 * (k : ℤ))) :=
    Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hz) fun u hu =>
      L.deriv_evalCollinearSpin h_int0 k hwl hu
  rw [h_ev.deriv_eq, hd_int.deriv]

/-- Pulling `transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s` inside
the $\mu^{\mathrm{LC}}_{2k}$-integral for $w_l, w_r \in \operatorname{UcDisk}$ and $s \in (0, 1)$. -/
theorem transmuteInner_evalCollinearSpin_eq_integral
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s =
      ∫ h : ℝ,
        Complex.exp ((h : ℂ) * wl) *
          (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (h + 2 * (k : ℝ))) wr s)
        ∂(L.muLC (2 * (k : ℤ))) := by
  set z : ℂ := wr + (Real.log s : ℂ)
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  set A1 : ℂ :=
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        (2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2) -
        (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2)
  set A2 : ℂ :=
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr)))
  have h_lhs :
      transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s =
        A2 * deriv (deriv (L.evalCollinearSpin k wl)) z +
          A1 * deriv (L.evalCollinearSpin k wl) z := by
    dsimp [A1, A2, transmuteInnerDiff]
    change transmuteInnerKernel wr s *
        ((1 - Complex.exp wr) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv (L.evalCollinearSpin k wl)) z +
            2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
              deriv (L.evalCollinearSpin k wl) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (L.evalCollinearSpin k wl) z) = _
    ring
  rw [h_lhs, L.deriv_evalCollinearSpin h_int0 k hwl hz,
    L.deriv_deriv_evalCollinearSpin h_int0 k hwl hz,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add
      ((L.integrable_collinearDeriv2Integrand h_int0 k hwl hz).const_mul A2)
      ((L.integrable_collinearDeriv1Integrand h_int0 k hwl hz).const_mul A1)]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp [A1, A2, transmuteInnerDiff]
  change A2 * (Complex.exp ((h : ℂ) * wl) * deriv (deriv (block1d (h + 2 * (k : ℝ)))) z) +
      A1 * (Complex.exp ((h : ℂ) * wl) * deriv (block1d (h + 2 * (k : ℝ))) z) =
    Complex.exp ((h : ℂ) * wl) *
      (transmuteInnerKernel wr s *
        ((1 - Complex.exp wr) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv (block1d (h + 2 * (k : ℝ)))) z +
            2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
              deriv (block1d (h + 2 * (k : ℝ))) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (block1d (h + 2 * (k : ℝ))) z))
  dsimp [A1, A2]
  ring

/-- Almost-everywhere strong measurability on `(volume.restrict (Ioo 0 1)).prod (L.muLC (2 * k))`
of `(s, h) ↦ exp (h * wl) * (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (h + 2k)) wr s)`. -/
lemma aestronglyMeasurable_transmuteInner_collinear_prod
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) (wl : ℂ) {wr : ℂ} (hwr : wr ∈ UcDisk) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Complex.exp ((p.2 : ℂ) * wl) *
          (transmuteInnerKernel wr p.1 *
            transmuteInnerDiff (block1d (p.2 + 2 * (k : ℝ))) wr p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (L.muLC (2 * (k : ℤ)))) := by
  have : SigmaFinite (L.muLC (2 * (k : ℤ))) := L.sigmaFinite_muLC_even h_int0 k
  set ν := volume.restrict (Ioo (0 : ℝ) 1)
  set μ := L.muLC (2 * (k : ℤ))
  set A1 : ℝ → ℂ := fun s =>
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        (2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2) -
        (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2)
  set A2 : ℝ → ℂ := fun s =>
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr)))
  have hA1_meas : Measurable A1 := by
    unfold A1 transmuteInnerKernel
    fun_prop
  have hA2_meas : Measurable A2 := by
    unfold A2 transmuteInnerKernel
    fun_prop
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (N : ℕ) (p : ℝ × ℝ) =>
      Complex.exp ((p.2 : ℂ) * wl) *
        (A2 p.1 *
          (∑ n ∈ Finset.range N,
            block1dDeriv2Term (p.2 + 2 * (k : ℝ)) n (wr + (Real.log p.1 : ℂ))) +
         A1 p.1 *
          (∑ n ∈ Finset.range N,
            block1dDeriv1Term (p.2 + 2 * (k : ℝ)) n (wr + (Real.log p.1 : ℂ)))))
    (fun N => ?_) ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (by fun_prop) ?_
    refine Measurable.add ?_ ?_
    · refine (hA2_meas.comp measurable_fst).mul ?_
      exact Finset.measurable_sum _ fun n _ => measurable_block1dDeriv2Term_prod (2 * (k : ℝ)) n wr
    · refine (hA1_meas.comp measurable_fst).mul ?_
      exact Finset.measurable_sum _ fun n _ => measurable_block1dDeriv1Term_prod (2 * (k : ℝ)) n wr
  · have hp_ae : ∀ᵐ p : ℝ × ℝ ∂(ν.prod μ),
        p.1 ∈ Ioo (0 : ℝ) 1 ∧ 0 ≤ p.2 + ((2 * (k : ℤ) : ℤ) : ℝ) :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)).and
        (Measure.quasiMeasurePreserving_snd.ae (L.ae_add_nonneg (2 * (k : ℤ))))
    filter_upwards [hp_ae] with p ⟨hs, hh⟩
    have hH : 0 ≤ p.2 + 2 * (k : ℝ) := by push_cast at hh; exact hh
    set z : ℂ := wr + (Real.log p.1 : ℂ)
    have hlog : Real.log p.1 < 0 := Real.log_neg hs.1 hs.2
    have hz : z ∈ UcDisk := by
      rw [mem_UcDisk_iff]
      simp only [z, Complex.add_re, Complex.ofReal_re]
      linarith [mem_UcDisk_iff.mp hwr]
    have ht1 : Tendsto (fun n => ∑ i ∈ Finset.range n, block1dDeriv1Term (p.2 + 2 * (k : ℝ)) i z)
        atTop (𝓝 (block1dDeriv1 (p.2 + 2 * (k : ℝ)) z)) :=
      (summable_block1dDeriv1Term hH hz).hasSum.tendsto_sum_nat
    have ht2 : Tendsto (fun n => ∑ i ∈ Finset.range n, block1dDeriv2Term (p.2 + 2 * (k : ℝ)) i z)
        atTop (𝓝 (block1dDeriv2 (p.2 + 2 * (k : ℝ)) z)) :=
      (summable_block1dDeriv2Term hH hz).hasSum.tendsto_sum_nat
    have h_lim := ((ht2.const_mul (A2 p.1)).add (ht1.const_mul (A1 p.1))).const_mul
      (Complex.exp ((p.2 : ℂ) * wl))
    have h_eq :
        Complex.exp ((p.2 : ℂ) * wl) *
          (A2 p.1 * block1dDeriv2 (p.2 + 2 * (k : ℝ)) z +
            A1 p.1 * block1dDeriv1 (p.2 + 2 * (k : ℝ)) z) =
        Complex.exp ((p.2 : ℂ) * wl) *
          (transmuteInnerKernel wr p.1 *
            transmuteInnerDiff (block1d (p.2 + 2 * (k : ℝ))) wr p.1) := by
      rw [← deriv_block1d hH hz, ← deriv_deriv_block1d hH hz]
      dsimp [A1, A2, transmuteInnerDiff]
      change _ =
        Complex.exp ((p.2 : ℂ) * wl) *
          (transmuteInnerKernel wr p.1 *
            ((1 - Complex.exp wr) ^ 2 *
              ((1 + (p.1 : ℂ) * Complex.exp wr) / (1 - (p.1 : ℂ) * Complex.exp wr) *
                deriv (deriv (block1d (p.2 + 2 * (k : ℝ)))) z +
                2 * (p.1 : ℂ) * Complex.exp wr / (1 - (p.1 : ℂ) * Complex.exp wr) ^ 2 *
                  deriv (block1d (p.2 + 2 * (k : ℝ))) z) -
              (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (block1d (p.2 + 2 * (k : ℝ))) z))
      ring
    rwa [h_eq] at h_lim

/-- **Commutation of `transmuteOpInner` ($\mathcal{L}_0$) with the Spin-$2k$ $s$-Channel Integral
(`transmuteOpInner_evalCollinearSpin`)**:
For every spin $k \in \mathbb{N}$ and all $w_l, w_r \in \operatorname{UcDisk}$,
$$
\operatorname{transmuteOpInner}\bigl(L.\operatorname{evalCollinearSpin} k\, w_l\bigr)(w_r)
  = L.\operatorname{evalCollinearTransmutedSpin} k\, w_l\, w_r.
$$ -/
theorem transmuteOpInner_evalCollinearSpin
    (hh_gap : 0 < L.h_gap)
    (h_supp0 : L.muLC 0 (Iio L.h_gap) = 0)
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    transmuteOpInner (L.evalCollinearSpin k wl) wr =
      L.evalCollinearTransmutedSpin k wl wr := by
  have : SigmaFinite (L.muLC (2 * (k : ℤ))) := L.sigmaFinite_muLC_even h_int0 k
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hwr_re : wr.re < 0 := mem_UcDisk_iff.mp hwr
  set ν := volume.restrict (Ioo (0 : ℝ) 1)
  set μ := L.muLC (2 * (k : ℤ))
  set F : ℝ → ℝ → ℂ := fun s h =>
    Complex.exp ((h : ℂ) * wl) *
      (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (h + 2 * (k : ℝ))) wr s)
  have h_prod_int : Integrable (Function.uncurry F) (ν.prod μ) := by
    have h_dom_s : Integrable (fun s : ℝ => block1dInnerDomConst wr.re * betaKernel 1 0 s) ν :=
      (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul
        (block1dInnerDomConst wr.re)
    have h_dom_h : Integrable
        (fun h : ℝ => monomialTermReal h (2 * (k : ℤ)) wl.re (wr.re / 2)) μ :=
      L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : wr.re / 2 < 0) k
    have h_dom_prod := h_dom_s.mul_prod h_dom_h
    refine h_dom_prod.mono'
      (L.aestronglyMeasurable_transmuteInner_collinear_prod h_int0 k wl hwr) ?_
    have hp_ae : ∀ᵐ p : ℝ × ℝ ∂(ν.prod μ),
        p.1 ∈ Ioo (0 : ℝ) 1 ∧ 0 ≤ p.2 + ((2 * (k : ℤ) : ℤ) : ℝ) :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)).and
        (Measure.quasiMeasurePreserving_snd.ae (L.ae_add_nonneg (2 * (k : ℤ))))
    filter_upwards [hp_ae] with p ⟨hs, hh⟩
    have hH : 0 ≤ p.2 + 2 * (k : ℝ) := by push_cast at hh; exact hh
    dsimp [Function.uncurry, F]
    rw [norm_mul, Complex.norm_exp]
    have hre : ((p.2 : ℂ) * wl).re = p.2 * wl.re := by simp [Complex.mul_re]
    rw [hre]
    calc
      Real.exp (p.2 * wl.re) *
          ‖transmuteInnerKernel wr p.1 * transmuteInnerDiff (block1d (p.2 + 2 * (k : ℝ))) wr p.1‖
        ≤ Real.exp (p.2 * wl.re) *
            (block1dInnerDomConst wr.re * Real.exp ((p.2 + 2 * (k : ℝ)) * (wr.re / 2)) *
              betaKernel 1 0 p.1) :=
          mul_le_mul_of_nonneg_left (norm_transmuteInner_block1d_le hH hwr hs)
            (Real.exp_pos _).le
      _ = (block1dInnerDomConst wr.re * betaKernel 1 0 p.1) *
            monomialTermReal p.2 (2 * (k : ℤ)) wl.re (wr.re / 2) := by
          dsimp [monomialTermReal]
          push_cast
          rw [Real.exp_add]
          ring
  have h_ae_pos : ∀ᵐ h : ℝ ∂μ, 0 < h + 2 * (k : ℝ) := by
    cases k with
    | zero =>
      have h_compl : ∀ᵐ h : ℝ ∂(L.muLC 0), h ∉ Iio L.h_gap :=
        compl_mem_ae_iff.mpr h_supp0
      filter_upwards [h_compl] with h hh
      rw [mem_Iio, not_lt] at hh
      simp only [Nat.cast_zero, mul_zero, add_zero]
      linarith
    | succ m =>
      filter_upwards [L.ae_nonneg (2 * ((m + 1 : ℕ) : ℤ))] with h hh
      have hm : (0 : ℝ) < 2 * ((m + 1 : ℕ) : ℝ) := by positivity
      linarith
  dsimp [transmuteOpInner]
  have h_int_congr :
      (∫ s in Ioo (0 : ℝ) 1,
        transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s) =
      ∫ s, (∫ h, F s h ∂μ) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact L.transmuteInner_evalCollinearSpin_eq_integral h_int0 k hwl hwr hs
  rw [h_int_congr, integral_integral_swap h_prod_int, ← integral_const_mul]
  dsimp [evalCollinearTransmutedSpin, μ]
  refine integral_congr_ae ?_
  filter_upwards [h_ae_pos] with h hh_pos
  dsimp [F, ν]
  rw [integral_const_mul]
  have h_pull :
      ((Real.sqrt π : ℝ) : ℂ)⁻¹ *
        (Complex.exp ((h : ℂ) * wl) *
          ∫ s in Ioo (0 : ℝ) 1,
            transmuteInnerKernel wr s * transmuteInnerDiff (block1d (h + 2 * (k : ℝ))) wr s) =
      Complex.exp ((h : ℂ) * wl) * transmuteOpInner (block1d (h + 2 * (k : ℝ))) wr := by
    dsimp [transmuteOpInner]; ring
  rw [h_pull, transmuteOpInner_block1d_of_pos hh_pos hwr]
  dsimp [monomialTerm]
  have h_exp :
      Complex.exp ((h : ℂ) * wl) *
        ((transmuteWeight (h + 2 * (k : ℝ)) : ℂ) *
          Complex.exp (((h + 2 * (k : ℝ) : ℝ) : ℂ) * wr)) =
      (transmuteWeight (h + 2 * (k : ℝ)) : ℂ) *
        (Complex.exp ((h : ℂ) * wl) * Complex.exp (((h + 2 * (k : ℝ) : ℝ) : ℂ) * wr)) := by
    ring
  rw [h_exp, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Norm bound on `L.evalCollinearSpin k wl z` for $w_l \in \operatorname{UcDisk}$ and
$\operatorname{Re} z \le \sigma < 0$. -/
lemma norm_evalCollinearSpin_le
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl : ℂ} (hwl : wl ∈ UcDisk) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖L.evalCollinearSpin k wl z‖ ≤
      block1dDerivBoundConst 0 σ *
        ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) ∂(L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  dsimp [evalCollinearSpin]
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  refine integral_mono_ae
    (L.integrable_collinearIntegrand h_int0 k hwl hz_mem).norm
    ((L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : σ / 2 < 0) k).const_mul
      (block1dDerivBoundConst 0 σ)) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖block1d (h + 2 * (k : ℝ)) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 0 σ * Real.exp ((h + 2 * (k : ℝ)) * (σ / 2))) :=
        mul_le_mul_of_nonneg_left (norm_block1d_le_exp_half hH hσ hz) (Real.exp_pos _).le
    _ = block1dDerivBoundConst 0 σ *
          monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- Norm bound on `deriv (L.evalCollinearSpin k wl) z` for $w_l \in \operatorname{UcDisk}$ and
$\operatorname{Re} z \le \sigma < 0$. -/
lemma norm_deriv_evalCollinearSpin_le
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl : ℂ} (hwl : wl ∈ UcDisk) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖deriv (L.evalCollinearSpin k wl) z‖ ≤
      block1dDerivBoundConst 1 σ *
        ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) ∂(L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  rw [L.deriv_evalCollinearSpin h_int0 k hwl hz_mem, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_ae
    (L.integrable_collinearDeriv1Integrand h_int0 k hwl hz_mem).norm
    ((L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : σ / 2 < 0) k).const_mul
      (block1dDerivBoundConst 1 σ)) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖deriv (block1d (h + 2 * (k : ℝ))) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 1 σ * Real.exp ((h + 2 * (k : ℝ)) * (σ / 2))) :=
        mul_le_mul_of_nonneg_left (norm_deriv_block1d_le_exp_half hH hσ hz) (Real.exp_pos _).le
    _ = block1dDerivBoundConst 1 σ *
          monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- Norm bound on `deriv (deriv (L.evalCollinearSpin k wl)) z` for $w_l \in \operatorname{UcDisk}$ and
$\operatorname{Re} z \le \sigma < 0$. -/
lemma norm_deriv_deriv_evalCollinearSpin_le
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl : ℂ} (hwl : wl ∈ UcDisk) {σ : ℝ} (hσ : σ < 0)
    {z : ℂ} (hz : z.re ≤ σ) :
    ‖deriv (deriv (L.evalCollinearSpin k wl)) z‖ ≤
      block1dDerivBoundConst 2 σ *
        ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) ∂(L.muLC (2 * (k : ℤ))) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_mem : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz.trans_lt hσ)
  rw [L.deriv_deriv_evalCollinearSpin h_int0 k hwl hz_mem, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_ae
    (L.integrable_collinearDeriv2Integrand h_int0 k hwl hz_mem).norm
    ((L.integrable_monomialTermReal_even h_int0 hwl_re (by linarith : σ / 2 < 0) k).const_mul
      (block1dDerivBoundConst 2 σ)) ?_
  filter_upwards [L.ae_add_nonneg (2 * (k : ℤ))] with h hh
  have hH : 0 ≤ h + 2 * (k : ℝ) := by push_cast at hh; exact hh
  rw [norm_mul, Complex.norm_exp]
  have hre : ((h : ℂ) * wl).re = h * wl.re := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (h * wl.re) * ‖deriv (deriv (block1d (h + 2 * (k : ℝ)))) z‖
      ≤ Real.exp (h * wl.re) *
          (block1dDerivBoundConst 2 σ * Real.exp ((h + 2 * (k : ℝ)) * (σ / 2))) :=
        mul_le_mul_of_nonneg_left (norm_deriv_deriv_block1d_le_exp_half hH hσ hz)
          (Real.exp_pos _).le
    _ = block1dDerivBoundConst 2 σ *
          monomialTermReal h (2 * (k : ℤ)) wl.re (σ / 2) := by
        dsimp [monomialTermReal]
        push_cast
        rw [Real.exp_add]
        ring

/-- Summability of `L.evalCollinearSpin k wl z` over $k \in \mathbb{N}$ on `UcPdisk`. -/
theorem summable_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Summable (fun k : ℕ => L.evalCollinearSpin k wl z) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.summable_integral_monomialTermReal_even h_int0 hwl_re
    (by linarith : z.re / 2 < 0)).mul_left (block1dDerivBoundConst 0 z.re)
  exact Summable.of_norm_bounded h_dom fun k =>
    L.norm_evalCollinearSpin_le h_int0 k hwl hz_re le_rfl

/-- Summability of `deriv (L.evalCollinearSpin k wl) z` over $k \in \mathbb{N}$ on `UcPdisk`. -/
theorem summable_deriv_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Summable (fun k : ℕ => deriv (L.evalCollinearSpin k wl) z) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.summable_integral_monomialTermReal_even h_int0 hwl_re
    (by linarith : z.re / 2 < 0)).mul_left (block1dDerivBoundConst 1 z.re)
  exact Summable.of_norm_bounded h_dom fun k =>
    L.norm_deriv_evalCollinearSpin_le h_int0 k hwl hz_re le_rfl

/-- Summability of `deriv (deriv (L.evalCollinearSpin k wl)) z` over $k \in \mathbb{N}$ on
`UcPdisk`. -/
theorem summable_deriv_deriv_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    Summable (fun k : ℕ => deriv (deriv (L.evalCollinearSpin k wl)) z) := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (L.summable_integral_monomialTermReal_even h_int0 hwl_re
    (by linarith : z.re / 2 < 0)).mul_left (block1dDerivBoundConst 2 z.re)
  exact Summable.of_norm_bounded h_dom fun k =>
    L.norm_deriv_deriv_evalCollinearSpin_le h_int0 k hwl hz_re le_rfl

/-- Term-by-term first derivative of `L.evalCollinear wl` on `UcDisk`. -/
theorem hasDerivAt_evalCollinear
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    HasDerivAt (L.evalCollinear wl)
      (∑' k : ℕ, deriv (L.evalCollinearSpin k wl) z) z := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum := (L.summable_integral_monomialTermReal_even h_int0 hwl_re
    (by linarith : z.re / 4 < 0)).mul_left (block1dDerivBoundConst 1 (z.re / 2))
  have h_bd : ∀ k : ℕ, ∀ y ∈ t,
      ‖deriv (L.evalCollinearSpin k wl) y‖ ≤
        block1dDerivBoundConst 1 (z.re / 2) *
          ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 4) ∂(L.muLC (2 * (k : ℤ))) := by
    intro k y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have hd1 := L.norm_deriv_evalCollinearSpin_le h_int0 k hwl (by linarith : z.re / 2 < 0) hy_re
    have h_div : z.re / 2 / 2 = z.re / 4 := by ring
    rwa [h_div] at hd1
  have hd_tsum : HasDerivAt
      (fun u : ℂ => ∑' k : ℕ, L.evalCollinearSpin k wl u)
      (∑' k : ℕ, deriv (L.evalCollinearSpin k wl) z) z :=
    hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
      (convex_ball z (-z.re / 2)).isPreconnected
      (fun k y hy => by
        have hy_mem : y ∈ UcDisk :=
          mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
        exact (L.hasDerivAt_evalCollinearSpin h_int0 k hwl hy_mem).differentiableAt.hasDerivAt)
      h_bd (Metric.mem_ball_self hr) (L.summable_evalCollinearSpin h_int0 hwl hz)
      (Metric.mem_ball_self hr)
  exact hd_tsum.const_add (1 : ℂ)

theorem deriv_evalCollinear
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    deriv (L.evalCollinear wl) z = ∑' k : ℕ, deriv (L.evalCollinearSpin k wl) z :=
  (L.hasDerivAt_evalCollinear h_int0 hwl hz).deriv

/-- Term-by-term second derivative of `L.evalCollinear wl` on `UcDisk`. -/
theorem deriv_deriv_evalCollinear
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl z : ℂ} (hwl : wl ∈ UcDisk) (hz : z ∈ UcDisk) :
    deriv (deriv (L.evalCollinear wl)) z =
      ∑' k : ℕ, deriv (deriv (L.evalCollinearSpin k wl)) z := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum := (L.summable_integral_monomialTermReal_even h_int0 hwl_re
    (by linarith : z.re / 4 < 0)).mul_left (block1dDerivBoundConst 2 (z.re / 2))
  have h_bd : ∀ k : ℕ, ∀ y ∈ t,
      ‖deriv (deriv (L.evalCollinearSpin k wl)) y‖ ≤
        block1dDerivBoundConst 2 (z.re / 2) *
          ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (z.re / 4) ∂(L.muLC (2 * (k : ℤ))) := by
    intro k y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have hd2 := L.norm_deriv_deriv_evalCollinearSpin_le h_int0 k hwl
      (by linarith : z.re / 2 < 0) hy_re
    have h_div : z.re / 2 / 2 = z.re / 4 := by ring
    rwa [h_div] at hd2
  have hd_tsum : HasDerivAt
      (fun u : ℂ => ∑' k : ℕ, deriv (L.evalCollinearSpin k wl) u)
      (∑' k : ℕ, deriv (deriv (L.evalCollinearSpin k wl)) z) z :=
    hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
      (convex_ball z (-z.re / 2)).isPreconnected
      (fun k y hy => by
        have hy_mem : y ∈ UcDisk :=
          mem_UcDisk_iff.mpr ((re_le_half_of_mem_ball hy).trans_lt (by linarith))
        have h_diff_on : DifferentiableOn ℂ (L.evalCollinearSpin k wl) UcDisk :=
          fun w hw => (L.hasDerivAt_evalCollinearSpin h_int0 k hwl hw).differentiableAt.differentiableWithinAt
        exact ((h_diff_on.deriv isOpen_UcDisk) y hy_mem).differentiableAt
          (isOpen_UcDisk.mem_nhds hy_mem) |>.hasDerivAt)
      h_bd (Metric.mem_ball_self hr) (L.summable_deriv_evalCollinearSpin h_int0 hwl hz)
      (Metric.mem_ball_self hr)
  have h_ev : deriv (L.evalCollinear wl) =ᶠ[𝓝 z]
      fun u : ℂ => ∑' k : ℕ, deriv (L.evalCollinearSpin k wl) u :=
    Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hz) fun u hu =>
      L.deriv_evalCollinear h_int0 hwl hu
  rw [h_ev.deriv_eq, hd_tsum.deriv]

/-- Pointwise series expansion of `transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s`
over spins $k \in \mathbb{N}$. -/
theorem hasSum_transmuteInner_evalCollinear
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum
      (fun k : ℕ =>
        transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s)
      (transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s) := by
  set z : ℂ := wr + (Real.log s : ℂ)
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  have hs1 : HasSum (fun k : ℕ => deriv (L.evalCollinearSpin k wl) z)
      (deriv (L.evalCollinear wl) z) := by
    rw [L.deriv_evalCollinear h_int0 hwl hz]
    exact (L.summable_deriv_evalCollinearSpin h_int0 hwl hz).hasSum
  have hs2 : HasSum (fun k : ℕ => deriv (deriv (L.evalCollinearSpin k wl)) z)
      (deriv (deriv (L.evalCollinear wl)) z) := by
    rw [L.deriv_deriv_evalCollinear h_int0 hwl hz]
    exact (L.summable_deriv_deriv_evalCollinearSpin h_int0 hwl hz).hasSum
  set A1 : ℂ :=
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        (2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2) -
        (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2)
  set A2 : ℂ :=
    transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr)))
  have h_comb := (hs2.mul_left A2).add (hs1.mul_left A1)
  have h_rhs :
      A2 * deriv (deriv (L.evalCollinear wl)) z + A1 * deriv (L.evalCollinear wl) z =
        transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s := by
    dsimp [A1, A2, transmuteInnerDiff]
    change _ =
      transmuteInnerKernel wr s *
        ((1 - Complex.exp wr) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv (L.evalCollinear wl)) z +
            2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
              deriv (L.evalCollinear wl) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (L.evalCollinear wl) z)
    ring
  rw [h_rhs] at h_comb
  refine h_comb.congr_fun fun k => ?_
  dsimp [A1, A2, transmuteInnerDiff]
  change transmuteInnerKernel wr s *
      ((1 - Complex.exp wr) ^ 2 *
        ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
          deriv (deriv (L.evalCollinearSpin k wl)) z +
          2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
            deriv (L.evalCollinearSpin k wl) z) -
        (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (L.evalCollinearSpin k wl) z) = _
  ring

/-- Continuity of `s ↦ transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s`
on `Ioo 0 1`. -/
lemma continuousOn_transmuteInner_evalCollinearSpin
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (k : ℕ) {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ContinuousOn
      (fun s : ℝ =>
        transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s)
      (Ioo (0 : ℝ) 1) := by
  let F := L.evalCollinearSpin k wl
  have hF : DifferentiableOn ℂ F UcDisk :=
    fun z hz => (L.hasDerivAt_evalCollinearSpin h_int0 k hwl hz).differentiableAt.differentiableWithinAt
  have hF1 : DifferentiableOn ℂ (deriv F) UcDisk := hF.deriv isOpen_UcDisk
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) UcDisk := hF1.deriv isOpen_UcDisk
  intro s hs
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  set z : ℂ := wr + (Real.log s : ℂ)
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hwr]
  have h_k_cont : ContinuousAt (transmuteInnerKernel wr) s := by
    have h1 : ContinuousAt (fun x : ℝ => x ^ (-1 / 2 : ℝ)) s :=
      continuousAt_id.rpow_const (Or.inl hs0.ne')
    have h2 : ContinuousAt (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) s :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl hs1.ne')
    have h3 : ContinuousAt
        (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (2 * wr)) ^ (-1 / 2 : ℂ)) s :=
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
        continuousAt_const
        (one_sub_mul_exp_two_mul_mem_slitPlane hwr ⟨hs.1.le, hs.2.le⟩)
    exact (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2)).mul h3
  have h_log : ContinuousAt (fun x : ℝ => wr + (Real.log x : ℂ)) s :=
    continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hs0.ne'))
  have hd1_cont : ContinuousAt (fun x : ℝ => deriv F (wr + (Real.log x : ℂ))) s :=
    ContinuousAt.comp (g := deriv F) (f := fun x : ℝ => wr + (Real.log x : ℂ))
      ((hF1 z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).continuousAt h_log
  have hd2_cont : ContinuousAt (fun x : ℝ => deriv (deriv F) (wr + (Real.log x : ℂ))) s :=
    ContinuousAt.comp (g := deriv (deriv F)) (f := fun x : ℝ => wr + (Real.log x : ℂ))
      ((hF2 z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).continuousAt h_log
  have hz_sub : 1 - (s : ℂ) * Complex.exp wr ≠ 0 := one_sub_mul_exp_ne_zero hwr hs
  have h_rat1 : ContinuousAt
      (fun x : ℝ => (1 + (x : ℂ) * Complex.exp wr) / (1 - (x : ℂ) * Complex.exp wr)) s :=
    (continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).div
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) hz_sub
  have h_rat2 : ContinuousAt
      (fun x : ℝ => 2 * (x : ℂ) * Complex.exp wr / (1 - (x : ℂ) * Complex.exp wr) ^ 2) s :=
    ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul
      continuousAt_const).div
      ((continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).pow 2)
      (pow_ne_zero 2 hz_sub)
  have h_diff_cont : ContinuousAt (transmuteInnerDiff F wr) s := by
    unfold transmuteInnerDiff
    exact (continuousAt_const.mul ((h_rat1.mul hd2_cont).add (h_rat2.mul hd1_cont))).sub
      (continuousAt_const.mul hd1_cont)
  exact (h_k_cont.mul h_diff_cont).continuousWithinAt

/-- **Commutation of `transmuteOpInner` ($\mathcal{L}_0$) with the Full $s$-Channel 1D Collinear
Block Sum and Integral (`transmuteOpInner_evalCollinear`)**:
For all $w_l, w_r \in \operatorname{UcDisk}$,
$$
\operatorname{transmuteOpInner}\bigl(L.\operatorname{evalCollinear} w_l\bigr)(w_r)
  = L.\operatorname{evalCollinearTransmuted} w_l\, w_r.
$$ -/
theorem transmuteOpInner_evalCollinear
    (hh_gap : 0 < L.h_gap)
    (h_supp0 : L.muLC 0 (Iio L.h_gap) = 0)
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    transmuteOpInner (L.evalCollinear wl) wr =
      L.evalCollinearTransmuted wl wr := by
  have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
  have hwr_re : wr.re < 0 := mem_UcDisk_iff.mp hwr
  set I_k : ℕ → ℝ := fun k =>
    ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (wr.re / 2) ∂(L.muLC (2 * (k : ℤ)))
  have hIk_nonneg : ∀ k : ℕ, 0 ≤ I_k k :=
    fun k => integral_nonneg fun h => monomialTermReal_nonneg h _ _ _
  set bound : ℕ → ℝ → ℝ := fun k s =>
    (block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s
  have h_sum_k : Summable (fun k : ℕ => block1dInnerDomConst wr.re * I_k k) :=
    (L.summable_integral_monomialTermReal_even h_int0 hwl_re
      (by linarith : wr.re / 2 < 0)).mul_left (block1dInnerDomConst wr.re)
  have h_hasSum_int :
      HasSum
        (fun k : ℕ =>
          ∫ s in Ioo (0 : ℝ) 1,
            transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s)
        (∫ s in Ioo (0 : ℝ) 1,
          transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) bound ?_ ?_ ?_ ?_ ?_
    · intro k
      exact (L.continuousOn_transmuteInner_evalCollinearSpin h_int0 k hwl hwr).aestronglyMeasurable
        measurableSet_Ioo
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
      have hz_le : (wr + (Real.log s : ℂ)).re ≤ wr.re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      have hd1 := L.norm_deriv_evalCollinearSpin_le h_int0 k hwl hwr_re hz_le
      have hd2 := L.norm_deriv_deriv_evalCollinearSpin_le h_int0 k hwl hwr_re hz_le
      have hD1 : 0 ≤ block1dDerivBoundConst 1 wr.re * I_k k :=
        mul_nonneg (block1dDerivBoundConst_nonneg 1 hwr_re) (hIk_nonneg k)
      have hD2 : 0 ≤ block1dDerivBoundConst 2 wr.re * I_k k :=
        mul_nonneg (block1dDerivBoundConst_nonneg 2 hwr_re) (hIk_nonneg k)
      have h_diff := norm_transmuteInnerDiff_le_of_deriv_le hwr hs hD1 hD2 hd1 hd2
      have h_k := norm_transmuteInnerKernel_le_betaKernel hwr hs
      have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * wr.re) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      dsimp [bound]
      rw [norm_mul]
      calc
        ‖transmuteInnerKernel wr s‖ *
            ‖transmuteInnerDiff (L.evalCollinearSpin k wl) wr s‖
          ≤ ((1 - Real.exp (2 * wr.re)) ^ (-1 / 2 : ℝ) * betaKernel 1 0 s) *
              (4 * (2 / (1 - Real.exp wr.re) * (block1dDerivBoundConst 2 wr.re * I_k k) +
                2 / (1 - Real.exp wr.re) ^ 2 * (block1dDerivBoundConst 1 wr.re * I_k k)) +
                2 * (block1dDerivBoundConst 1 wr.re * I_k k)) :=
            mul_le_mul h_k h_diff (norm_nonneg _)
              (mul_nonneg (by positivity) (betaKernel_nonneg 1 0 hs))
        _ = (block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s := by
            dsimp [block1dInnerDomConst]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s _
      exact h_sum_k.mul_right (betaKernel 1 0 s)
    · have h_tsum :
          (fun s : ℝ => ∑' k : ℕ, bound k s) =
            fun s : ℝ =>
              (∑' k : ℕ, block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s := by
        ext s; dsimp [bound]; exact tsum_mul_right
      rw [h_tsum]
      exact (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact L.hasSum_transmuteInner_evalCollinear h_int0 hwl hwr hs
  have h_scaled := h_hasSum_int.mul_left (((Real.sqrt π : ℝ) : ℂ)⁻¹)
  have h_congr :
      HasSum (fun k : ℕ => L.evalCollinearTransmutedSpin k wl wr)
        (transmuteOpInner (L.evalCollinear wl) wr) := by
    refine h_scaled.congr_fun fun k => ?_
    exact (L.transmuteOpInner_evalCollinearSpin hh_gap h_supp0 h_int0 k hwl hwr).symm
  exact h_congr.tsum_eq.symm

/-- For every spin $k \ge 1$, `L.evalCollinearTransmutedSpin k wl wr` coincides with
`L.toTransmutedMonomialFourPointData.evalSpin (2 * k) wl wr` because $\mu^{\mathrm{LC}}_{2k}$-almost
everywhere $h + 2k \ge 2 > 1/2$, so $\operatorname{transmutePosWeight}(h + 2k) = \operatorname{transmuteWeight}(h + 2k)$. -/
theorem evalCollinearTransmutedSpin_eq_toTransmuted_evalSpin
    {k : ℕ} (hk : 1 ≤ k) (wl wr : ℂ) :
    L.evalCollinearTransmutedSpin k wl wr =
      L.toTransmutedMonomialFourPointData.evalSpin (2 * (k : ℤ)) wl wr := by
  dsimp [evalCollinearTransmutedSpin, MonomialFourPointData.evalSpin,
    toTransmutedMonomialFourPointData]
  rw [L.integral_transmutedMeasure]
  have hJ : (1 : ℤ) ≤ 2 * (k : ℤ) := by omega
  refine integral_congr_ae ?_
  filter_upwards [L.ae_transmutePosWeight_eq_transmuteWeight hJ] with h hh
  have h_cast : (h + ((2 * (k : ℤ) : ℤ) : ℝ)) = h + 2 * (k : ℝ) := by push_cast; ring
  rw [h_cast] at hh
  simp [Complex.real_smul, hh]

/-- When `L.muLC J = 0` for $J < 0$ (collinear spin spectrum $J = 2k \ge 0$), the full transmuted
evaluation `L.evalCollinearTransmuted wl wr` on $\operatorname{UcPdisk}$ differs from
`L.toTransmutedMonomialFourPointData.eval wl wr` solely by the $k = 0$ term, which depends only on
$w_l + w_r$ and is therefore **independent of $\theta$** along the folded contour
$(w_l - i\theta, w_r + i\theta)$! -/
theorem evalCollinearTransmuted_eq_toTransmuted_eval_add_spinZero
    (h_neg_spin : ∀ J : ℤ, J < 0 → L.muLC J = 0)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    L.evalCollinearTransmuted wl wr =
      L.toTransmutedMonomialFourPointData.eval wl wr +
        (L.evalCollinearTransmutedSpin 0 wl wr -
          L.toTransmutedMonomialFourPointData.evalSpin 0 wl wr) := by
  set M := L.toTransmutedMonomialFourPointData
  have h_inj : Function.Injective (fun k : ℕ => (2 * (k : ℤ) : ℤ)) := by
    intro a b hab; dsimp at hab; omega
  have hM_sum_nat :
      M.eval wl wr = ∑' k : ℕ, M.evalSpin (2 * (k : ℤ)) wl wr := by
    dsimp [MonomialFourPointData.eval]
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun k : ↑(Function.support fun k : ℕ => M.evalSpin (2 * (k : ℤ)) wl wr) =>
        (2 * (k.1 : ℤ) : ℤ))
      (fun a b hab => Subtype.ext (h_inj hab))
      (fun J hJ => ?_)
      (fun _ => rfl)
    rw [Function.mem_support] at hJ
    rcases lt_or_ge J 0 with hJ_neg | hJ_nonneg
    · exfalso; apply hJ
      dsimp [MonomialFourPointData.evalSpin, M, toTransmutedMonomialFourPointData, transmutedMeasure]
      rw [h_neg_spin J hJ_neg, withDensity_zero_left, integral_zero_measure]
    · rcases Int.even_or_odd J with ⟨m, rfl⟩ | hJ_odd
      · have hm_nonneg : 0 ≤ m := by omega
        lift m to ℕ using hm_nonneg
        have h2m : m + m = 2 * (m : ℤ) := by ring
        rw [h2m] at hJ ⊢
        exact ⟨⟨m, hJ⟩, rfl⟩
      · exfalso; apply hJ
        exact M.evalSpin_of_odd hJ_odd wl wr
  have h_sum : Summable (fun k : ℕ => M.evalSpin (2 * (k : ℤ)) wl wr) :=
    (M.summable_evalSpin hwl hwr).comp_injective h_inj
  have h_sum_coll : Summable (fun k : ℕ => L.evalCollinearTransmutedSpin k wl wr) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_nat_add_iff 1).mpr h_sum).congr fun k => ?_
    exact (L.evalCollinearTransmutedSpin_eq_toTransmuted_evalSpin (by omega) wl wr).symm
  have h1 := h_sum_coll.tsum_eq_zero_add
  have h2 := h_sum.tsum_eq_zero_add
  have h_tail_eq :
      (∑' k : ℕ, L.evalCollinearTransmutedSpin (k + 1) wl wr) =
        ∑' k : ℕ, M.evalSpin (2 * ((k + 1 : ℕ) : ℤ)) wl wr :=
    tsum_congr fun k => L.evalCollinearTransmutedSpin_eq_toTransmuted_evalSpin (by omega) wl wr
  dsimp [evalCollinearTransmuted]
  rw [hM_sum_nat, h1, h2, h_tail_eq]
  ring

/-- The $k = 0$ difference `L.evalCollinearTransmutedSpin 0 - L.toTransmutedMonomialFourPointData.evalSpin 0`
is invariant under opposite imaginary shifts $(w_l - i\theta, w_r + i\theta)$. -/
lemma spinZero_diff_shift_invariant (wl wr : ℂ) (θ : ℝ) :
    L.evalCollinearTransmutedSpin 0 (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) -
      L.toTransmutedMonomialFourPointData.evalSpin 0 (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) =
    L.evalCollinearTransmutedSpin 0 wl wr -
      L.toTransmutedMonomialFourPointData.evalSpin 0 wl wr := by
  have h_mono : ∀ h : ℝ,
      monomialTerm h 0 (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) = monomialTerm h 0 wl wr := by
    intro h
    dsimp [monomialTerm]
    congr 1
    push_cast; ring
  dsimp [evalCollinearTransmutedSpin, MonomialFourPointData.evalSpin]
  simp_rw [h_mono]

/-- **Exact Agreement of Folded Spin-$2k$ Fourier Projections (`fourierProjSpin_evalCollinearTransmuted_eq`)**:
For every spin $k \ge 1$ and all $w_l, w_r \in \operatorname{UcDisk}$ (when `L.muLC J = 0` for
$J < 0$), the folded spin-$2k$ Fourier projection of `L.evalCollinearTransmuted` on
$\theta \in [-\pi/2, \pi/2]$ is **identically equal** to
`L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * k) wl wr`! -/
theorem fourierProjSpin_evalCollinearTransmuted_eq
    (h_neg_spin : ∀ J : ℤ, J < 0 → L.muLC J = 0)
    {k : ℕ} (hk : 1 ≤ k) {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    (π : ℂ)⁻¹ *
      (∫ θ in (-π / 2)..(π / 2),
        Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
          L.evalCollinearTransmuted (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) =
      L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ)) wl wr := by
  set M := L.toTransmutedMonomialFourPointData
  set Δ₀ : ℂ := L.evalCollinearTransmutedSpin 0 wl wr - M.evalSpin 0 wl wr
  have h_integrand : ∀ θ : ℝ,
      Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
        L.evalCollinearTransmuted (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) =
      M.fourierIntegrand (2 * (k : ℤ)) wl wr θ +
        (Δ₀ * Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr)) *
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I) := by
    intro θ
    have hwl_θ : wl - (θ : ℂ) * I ∈ UcDisk := MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ
    have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk := MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
    rw [L.evalCollinearTransmuted_eq_toTransmuted_eval_add_spinZero h_neg_spin hwl_θ hwr_θ,
      L.spinZero_diff_shift_invariant wl wr θ]
    dsimp [MonomialFourPointData.fourierIntegrand, Δ₀]
    have h_exp :
        Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) =
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr) *
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1; ring
    rw [h_exp]
    ring
  simp_rw [h_integrand]
  have h_int1 : IntervalIntegrable (M.fourierIntegrand (2 * (k : ℤ)) wl wr) volume (-π / 2) (π / 2) :=
    (M.continuous_fourierIntegrand (2 * (k : ℤ)) hwl hwr).intervalIntegrable _ _
  have h_int2 : IntervalIntegrable
      (fun θ : ℝ =>
        (Δ₀ * Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr)) *
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I))
      volume (-π / 2) (π / 2) := by
    have hc : Continuous (fun θ : ℝ =>
        (Δ₀ * Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr)) *
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I)) := by fun_prop
    exact hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add h_int1 h_int2,
    intervalIntegral.integral_const_mul,
    integral_exp_neg_two_mul_int_mul_I (by omega : (k : ℤ) ≠ 0),
    mul_zero, add_zero]
  rfl

/-- **Inner Transmutation of `tChannelRemainder` from the 1D Collinear Block Expansion
(`transmuteOpInner_tChannelRemainder_eq_of_collinear`)**:
When `M.eval wl z = L.evalCollinear wl z` on `UcPdisk` and
`crossFactor Δ_phi z = gffBlockSeries Δ_phi z` on `UcDisk` (the 1D GFF block series), commuting
`transmuteOpInner` ($\mathcal{L}_0$) with both the $s$-channel sum/integral and the 1D GFF block
series yields the exact pointwise identity on `UcPdisk`:
$$
\operatorname{transmuteOpInner}\bigl(\operatorname{tChannelRemainder} M\, \Delta_\phi\, w_l\bigr)(w_r)
  = L.\operatorname{evalCollinearTransmuted} w_l\, w_r -
    \operatorname{crossIdentityExactTransmuted}(\Delta_\phi, w_l, w_r).
$$ -/
theorem transmuteOpInner_tChannelRemainder_eq_of_collinear
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (hh_gap : 0 < L.h_gap)
    (h_supp0 : L.muLC 0 (Iio L.h_gap) = 0)
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (M : MonomialFourPointData)
    (hM_coll : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = L.evalCollinear wl wr)
    (h_gff : ∀ {w : ℂ}, w ∈ UcDisk → crossFactor Δ_phi w = gffBlockSeries Δ_phi w)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    transmuteOpInner (tChannelRemainder M Δ_phi wl) wr =
      L.evalCollinearTransmuted wl wr - crossIdentityExactTransmuted Δ_phi wl wr := by
  have h_rem_eqOn : ∀ z ∈ UcDisk,
      tChannelRemainder M Δ_phi wl z =
        L.evalCollinear wl z - crossFactor Δ_phi wl * gffBlockSeries Δ_phi z := by
    intro z hz
    dsimp [tChannelRemainder, crossIdentity]
    rw [hM_coll hwl hz, h_gff hz]
  have hF_diff : DifferentiableOn ℂ (L.evalCollinear wl) UcDisk :=
    fun z hz => (L.hasDerivAt_evalCollinear h_int0 hwl hz).differentiableAt.differentiableWithinAt
  have hF'_diff : DifferentiableOn ℂ (deriv (L.evalCollinear wl)) UcDisk :=
    hF_diff.deriv isOpen_UcDisk
  have hG_diff : DifferentiableOn ℂ (gffBlockSeries Δ_phi) UcDisk :=
    fun z hz => (hasDerivAt_gffBlockSeries hΔ hz).differentiableAt.differentiableWithinAt
  have hG'_diff : DifferentiableOn ℂ (deriv (gffBlockSeries Δ_phi)) UcDisk :=
    hG_diff.deriv isOpen_UcDisk
  have h_diff_eq : ∀ s ∈ Ioo (0 : ℝ) 1,
      transmuteInnerKernel wr s * transmuteInnerDiff (tChannelRemainder M Δ_phi wl) wr s =
        transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s -
          crossFactor Δ_phi wl *
            (transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s) := by
    intro s hs
    set z : ℂ := wr + (Real.log s : ℂ)
    have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
    have hz : z ∈ UcDisk := by
      rw [mem_UcDisk_iff]
      simp only [z, Complex.add_re, Complex.ofReal_re]
      linarith [mem_UcDisk_iff.mp hwr]
    have h_ev1 : tChannelRemainder M Δ_phi wl =ᶠ[𝓝 z]
        fun u => L.evalCollinear wl u - crossFactor Δ_phi wl * gffBlockSeries Δ_phi u :=
      Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hz) h_rem_eqOn
    have hd1_sub : ∀ u ∈ UcDisk,
        deriv (fun v => L.evalCollinear wl v - crossFactor Δ_phi wl * gffBlockSeries Δ_phi v) u =
          deriv (L.evalCollinear wl) u - crossFactor Δ_phi wl * deriv (gffBlockSeries Δ_phi) u := by
      intro u hu
      have hdF := (L.hasDerivAt_evalCollinear h_int0 hwl hu).differentiableAt.hasDerivAt
      have hdG := ((hasDerivAt_gffBlockSeries hΔ hu).differentiableAt.hasDerivAt).const_mul
        (crossFactor Δ_phi wl)
      exact (hdF.sub hdG).deriv
    have hd1 : deriv (tChannelRemainder M Δ_phi wl) z =
        deriv (L.evalCollinear wl) z - crossFactor Δ_phi wl * deriv (gffBlockSeries Δ_phi) z := by
      rw [h_ev1.deriv_eq, hd1_sub z hz]
    have h_ev2 : deriv (tChannelRemainder M Δ_phi wl) =ᶠ[𝓝 z]
        fun u => deriv (L.evalCollinear wl) u - crossFactor Δ_phi wl * deriv (gffBlockSeries Δ_phi) u := by
      filter_upwards [isOpen_UcDisk.mem_nhds hz] with u hu
      have h_ev_u : tChannelRemainder M Δ_phi wl =ᶠ[𝓝 u]
          fun v => L.evalCollinear wl v - crossFactor Δ_phi wl * gffBlockSeries Δ_phi v :=
        Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hu) h_rem_eqOn
      rw [h_ev_u.deriv_eq, hd1_sub u hu]
    have hd2 : deriv (deriv (tChannelRemainder M Δ_phi wl)) z =
        deriv (deriv (L.evalCollinear wl)) z -
          crossFactor Δ_phi wl * deriv (deriv (gffBlockSeries Δ_phi)) z := by
      rw [h_ev2.deriv_eq]
      have hdF' := ((hF'_diff z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).hasDerivAt
      have hdG' := (((hG'_diff z hz).differentiableAt (isOpen_UcDisk.mem_nhds hz)).hasDerivAt).const_mul
        (crossFactor Δ_phi wl)
      exact (hdF'.sub hdG').deriv
    dsimp [transmuteInnerDiff]
    change transmuteInnerKernel wr s *
        ((1 - Complex.exp wr) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv (tChannelRemainder M Δ_phi wl)) z +
            2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
              deriv (tChannelRemainder M Δ_phi wl) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (tChannelRemainder M Δ_phi wl) z) =
      transmuteInnerKernel wr s *
        ((1 - Complex.exp wr) ^ 2 *
          ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
            deriv (deriv (L.evalCollinear wl)) z +
            2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
              deriv (L.evalCollinear wl) z) -
          (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (L.evalCollinear wl) z) -
        crossFactor Δ_phi wl *
          (transmuteInnerKernel wr s *
            ((1 - Complex.exp wr) ^ 2 *
              ((1 + (s : ℂ) * Complex.exp wr) / (1 - (s : ℂ) * Complex.exp wr) *
                deriv (deriv (gffBlockSeries Δ_phi)) z +
                2 * (s : ℂ) * Complex.exp wr / (1 - (s : ℂ) * Complex.exp wr) ^ 2 *
                  deriv (gffBlockSeries Δ_phi) z) -
              (1 / 2 : ℂ) * (1 + Complex.exp wr) ^ 2 * deriv (gffBlockSeries Δ_phi) z))
    rw [hd1, hd2]
    ring
  have h_int_coll : IntegrableOn
      (fun s : ℝ => transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s)
      (Ioo (0 : ℝ) 1) volume := by
    have hwl_re : wl.re < 0 := mem_UcDisk_iff.mp hwl
    have hwr_re : wr.re < 0 := mem_UcDisk_iff.mp hwr
    set I_k : ℕ → ℝ := fun k =>
      ∫ h : ℝ, monomialTermReal h (2 * (k : ℤ)) wl.re (wr.re / 2) ∂(L.muLC (2 * (k : ℤ)))
    have hIk_nonneg : ∀ k : ℕ, 0 ≤ I_k k :=
      fun k => integral_nonneg fun h => monomialTermReal_nonneg h _ _ _
    have h_sum_k : Summable (fun k : ℕ => block1dInnerDomConst wr.re * I_k k) :=
      (L.summable_integral_monomialTermReal_even h_int0 hwl_re
        (by linarith : wr.re / 2 < 0)).mul_left (block1dInnerDomConst wr.re)
    have h_dom : IntegrableOn
        (fun s : ℝ => (∑' k : ℕ, block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s)
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul _
    have h_meas : AEStronglyMeasurable
        (fun s : ℝ => transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s)
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun (N : ℕ) (s : ℝ) =>
          ∑ k ∈ Finset.range N,
            transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s)
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (L.continuousOn_transmuteInner_evalCollinearSpin h_int0 k hwl hwr).aestronglyMeasurable
            measurableSet_Ioo)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          exact (L.hasSum_transmuteInner_evalCollinear h_int0 hwl hwr hs).tendsto_sum_nat)
    refine h_dom.mono' h_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h_hs := L.hasSum_transmuteInner_evalCollinear h_int0 hwl hwr hs
    rw [← h_hs.tsum_eq]
    have h_sum_b : Summable (fun k : ℕ => (block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s) :=
      h_sum_k.mul_right (betaKernel 1 0 s)
    have h_term_le : ∀ k : ℕ,
        ‖transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s‖ ≤
          (block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s := by
      intro k
      have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
      have hz_le : (wr + (Real.log s : ℂ)).re ≤ wr.re := by
        simp only [Complex.add_re, Complex.ofReal_re]; linarith
      have hd1 := L.norm_deriv_evalCollinearSpin_le h_int0 k hwl hwr_re hz_le
      have hd2 := L.norm_deriv_deriv_evalCollinearSpin_le h_int0 k hwl hwr_re hz_le
      have hD1 : 0 ≤ block1dDerivBoundConst 1 wr.re * I_k k :=
        mul_nonneg (block1dDerivBoundConst_nonneg 1 hwr_re) (hIk_nonneg k)
      have hD2 : 0 ≤ block1dDerivBoundConst 2 wr.re * I_k k :=
        mul_nonneg (block1dDerivBoundConst_nonneg 2 hwr_re) (hIk_nonneg k)
      have h_diff := norm_transmuteInnerDiff_le_of_deriv_le hwr hs hD1 hD2 hd1 hd2
      have h_k := norm_transmuteInnerKernel_le_betaKernel hwr hs
      have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * wr.re) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      rw [norm_mul]
      calc
        ‖transmuteInnerKernel wr s‖ *
            ‖transmuteInnerDiff (L.evalCollinearSpin k wl) wr s‖
          ≤ ((1 - Real.exp (2 * wr.re)) ^ (-1 / 2 : ℝ) * betaKernel 1 0 s) *
              (4 * (2 / (1 - Real.exp wr.re) * (block1dDerivBoundConst 2 wr.re * I_k k) +
                2 / (1 - Real.exp wr.re) ^ 2 * (block1dDerivBoundConst 1 wr.re * I_k k)) +
                2 * (block1dDerivBoundConst 1 wr.re * I_k k)) :=
            mul_le_mul h_k h_diff (norm_nonneg _)
              (mul_nonneg (by positivity) (betaKernel_nonneg 1 0 hs))
        _ = (block1dInnerDomConst wr.re * I_k k) * betaKernel 1 0 s := by
            dsimp [block1dInnerDomConst]; ring
    have h_sum_norm : Summable (fun k : ℕ =>
        ‖transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinearSpin k wl) wr s‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_le h_sum_b
    exact (norm_tsum_le_tsum_norm h_sum_norm).trans
      ((h_sum_norm.tsum_le_tsum h_term_le h_sum_b).trans_eq tsum_mul_right)
  have h_int_gff : IntegrableOn
      (fun s : ℝ => transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s)
      (Ioo (0 : ℝ) 1) volume := by
    have hwr_re : wr.re < 0 := mem_UcDisk_iff.mp hwr
    have h_sum_m :
        Summable (fun m : ℕ =>
          block1dInnerDomConst wr.re *
            (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)))) :=
      (summable_gffBlockCoeff_mul_exp hΔ (by linarith : wr.re / 2 < 0)).mul_left
        (block1dInnerDomConst wr.re)
    have h_dom : IntegrableOn
        (fun s : ℝ =>
          (∑' m : ℕ,
            block1dInnerDomConst wr.re *
              (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)))) *
            betaKernel 1 0 s)
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul _
    have h_meas : AEStronglyMeasurable
        (fun s : ℝ => transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s)
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun (N : ℕ) (s : ℝ) =>
          ∑ m ∈ Finset.range N,
            (gffBlockCoeff Δ_phi m : ℂ) *
              (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) wr s))
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ => by
          have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
          exact ((continuousOn_transmuteInner_block1d hH hwr).const_mul
            (gffBlockCoeff Δ_phi m : ℂ)).aestronglyMeasurable measurableSet_Ioo)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          exact (hasSum_transmuteInner_gffBlockSeries hΔ hwr hs).tendsto_sum_nat)
    refine h_dom.mono' h_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h_hs := hasSum_transmuteInner_gffBlockSeries hΔ hwr hs
    rw [← h_hs.tsum_eq]
    have h_sum_b : Summable (fun m : ℕ =>
        (block1dInnerDomConst wr.re *
          (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)))) *
          betaKernel 1 0 s) :=
      h_sum_m.mul_right (betaKernel 1 0 s)
    have h_term_le : ∀ m : ℕ,
        ‖(gffBlockCoeff Δ_phi m : ℂ) *
            (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) wr s)‖ ≤
          (block1dInnerDomConst wr.re *
            (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)))) *
            betaKernel 1 0 s := by
      intro m
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gffBlockCoeff_nonneg hΔ m)]
      have hH : 0 ≤ Δ_phi + (m : ℝ) := by positivity
      calc
        gffBlockCoeff Δ_phi m *
            ‖transmuteInnerKernel wr s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) wr s‖
          ≤ gffBlockCoeff Δ_phi m *
              (block1dInnerDomConst wr.re * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)) *
                betaKernel 1 0 s) :=
            mul_le_mul_of_nonneg_left (norm_transmuteInner_block1d_le hH hwr hs)
              (gffBlockCoeff_nonneg hΔ m)
        _ = (block1dInnerDomConst wr.re *
              (gffBlockCoeff Δ_phi m * Real.exp ((Δ_phi + (m : ℝ)) * (wr.re / 2)))) *
              betaKernel 1 0 s := by ring
    have h_sum_norm : Summable (fun m : ℕ =>
        ‖(gffBlockCoeff Δ_phi m : ℂ) *
          (transmuteInnerKernel wr s * transmuteInnerDiff (block1d (Δ_phi + (m : ℝ))) wr s)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_le h_sum_b
    exact (norm_tsum_le_tsum_norm h_sum_norm).trans
      ((h_sum_norm.tsum_le_tsum h_term_le h_sum_b).trans_eq tsum_mul_right)
  have h_int_congr :
      (∫ s in Ioo (0 : ℝ) 1,
        transmuteInnerKernel wr s * transmuteInnerDiff (tChannelRemainder M Δ_phi wl) wr s) =
      ∫ s in Ioo (0 : ℝ) 1,
        (transmuteInnerKernel wr s * transmuteInnerDiff (L.evalCollinear wl) wr s -
          crossFactor Δ_phi wl *
            (transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s)) :=
    setIntegral_congr_fun measurableSet_Ioo h_diff_eq
  dsimp [transmuteOpInner]
  rw [h_int_congr, integral_sub h_int_coll (h_int_gff.const_mul (crossFactor Δ_phi wl)),
    integral_const_mul, mul_sub]
  have h1 := L.transmuteOpInner_evalCollinear hh_gap h_supp0 h_int0 hwl hwr
  have h2 := transmuteOpInner_gffBlockSeries hΔ hwr
  dsimp [transmuteOpInner] at h1 h2
  rw [h1]
  have h_pull :
      ((Real.sqrt π : ℝ) : ℂ)⁻¹ *
        (crossFactor Δ_phi wl *
          ∫ s in Ioo (0 : ℝ) 1,
            transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s) =
      crossFactor Δ_phi wl *
        (((Real.sqrt π : ℝ) : ℂ)⁻¹ *
          ∫ s in Ioo (0 : ℝ) 1,
            transmuteInnerKernel wr s * transmuteInnerDiff (gffBlockSeries Δ_phi) wr s) := by
    ring
  rw [h_pull, h2]
  rfl

end LightconeBlockFourPointData
