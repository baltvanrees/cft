/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlock.RemainderBounds

/-!
# Collinear Block Transfer Kernel and Shifted Test Function Bounds

This file constructs the smooth collinear descendant transfer functions and proves their uniform
$C^2$ and support bounds for the Stage III $d$-dimensional primary lightcone bootstrap:

1. **Normalized Pairings & Exact Rational Weight Shift Ratio (`normLCPairing`, `normPrimaryPairing`,
   `weightShiftRatio`, `weightShiftRatio_eq_transmuteWeight_div`)**:
   Shows that the ratio of transmutation weights across descendant twist shifts $m$ and spin shifts
   $2s$ is an exact finite rational product.
2. **Smooth Collinear Transfer Kernel (`collinearTransferRatio`, `collinearTransferFn`,
   `exists_c2_bound_collinearTransferFn`)**:
   Constructs the smooth cutoff transfer kernel $K_{m, s, k}(h)$ and proves that its value, first
   derivative, and second derivative on $[-N, N]$ are bounded uniformly for all $k \ge 1$.
3. **Uniform $C^2$ Bounds for the Rescaled Inverse Transmutation Weight
   (`cutoffInvTransmuteWeight`, `exists_c2_bound_cutoffInvTransmuteWeight`)**:
   Establishes uniform $C^2$ bounds for $(2k)^{3/2} / \operatorname{transmuteWeight}(h + 2k)$ on
   $[\min(h_{\text{gap}}, \Delta_\phi), \infty)$.
4. **Shifted Collinear Test Functions (`collinearShiftTestFn`)**:
   Proves differentiability and support shift properties for the transferred test functions
   $\psi_{m, s, k}(h) = K_{m, s, k}(h)\,\varphi(h + m)$.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

/-! ## Section 1: Normalized Pairings & Collinear Block Transfer Kernel -/

namespace FourPointData

/-- Normalized spin-$2k$ 1D lightcone-block transmuted pairing of a four-point correlator
`corr : FourPointData ν Δ_phi`:
$$
\mathcal{L}_k(\varphi) := (2k)^{-2\Delta_\phi}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
  d\mu^{\mathrm{LC}}_{2k}(h).
$$ -/
noncomputable def normLCPairing {ν Δ_phi : ℝ}
    (corr : FourPointData ν Δ_phi) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
    ∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
      ∂(corr.lightconeMeasure (2 * (k : ℤ)))

/-- Normalized spin-$2k$ $d$-dimensional primary operator transmuted pairing of a four-point
correlator `corr : FourPointData ν Δ_phi`:
$$
\mathcal{P}_k(\varphi) := (2k)^{-2\Delta_\phi} \frac{(\nu)_{2k}}{(2k)!}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
  d\mu^{\mathrm{prim}}_{2k}(h).
$$ -/
noncomputable def normPrimaryPairing {ν Δ_phi : ℝ}
    (corr : FourPointData ν Δ_phi) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
    ∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(corr.primaryTwistMeasure (2 * k))

/-- Direct extraction of the unweighted primary integral
$\int_{\mathbb{R}} \varphi(h) \, d\mu^{\mathrm{prim}}_{2k}(h)$
by dividing the test function by $\operatorname{transmuteWeight}(h + 2k)$. -/
theorem normPrimaryPairing_div_transmuteWeight
    {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi) {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ_lo : ∀ h : ℝ, h < 0 → φ h = 0) :
    (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
        (∫ h : ℝ, φ h ∂(corr.primaryTwistMeasure (2 * k))) =
      corr.normPrimaryPairing k (fun h => φ h / transmuteWeight (h + (2 * k : ℕ))) := by
  dsimp [FourPointData.normPrimaryPairing]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp
  by_cases hh : h < 0
  · rw [hφ_lo h hh, zero_div, mul_zero]
  · have hh0 : 0 ≤ h := not_lt.mp hh
    have h2k : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * k)
    have h_gt : 1 / 2 < h + (2 * k : ℕ) := by linarith
    exact (mul_div_cancel₀ (φ h) (transmuteWeight_pos h_gt).ne').symm

end FourPointData

/-- Elementary rational shift factor
$$f_{c, d, k}(h) := 1 + \frac{c}{h + 2k + d}$$
appearing in the Gamma-function shift ratio for `transmuteWeight`. -/
noncomputable def elementaryShiftFactor (c d : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  1 + c / (h + 2 * (k : ℝ) + d)

/-- Explicit rational formula for the transmutation weight ratio
$$
\frac{\operatorname{transmuteWeight}(h + m + 2k)}{\operatorname{transmuteWeight}(h + 2(k + s))}
  = \frac{h + 2k + m - 1/2}{h + 2k + 2s - 1/2}
    \left(\prod_{i=0}^{m-1} \frac{h + 2k + i + 1/2}{h + 2k + i}\right)
    \left(\prod_{j=0}^{2s-1} \frac{h + 2k + j}{h + 2k + j + 1/2}\right).
$$
Writing both $h + m + 2k = (h + 2k) + m$ and $h + 2(k + s) = (h + 2k) + 2s$ as non-negative
natural-number shifts of $x = h + 2k$ avoids any case split on the sign of $m - 2s$ and expresses
the weight ratio as a finite product of `elementaryShiftFactor`s with $d \ge -1/2$. -/
noncomputable def weightShiftRatio (m s k : ℕ) (h : ℝ) : ℝ :=
  elementaryShiftFactor ((m : ℝ) - ((2 * s : ℕ) : ℝ)) (((2 * s : ℕ) : ℝ) - 1 / 2) k h *
    (∏ i ∈ Finset.range m, elementaryShiftFactor (1 / 2) (i : ℝ) k h) *
    (∏ j ∈ Finset.range (2 * s), elementaryShiftFactor (- (1 / 2)) ((j : ℝ) + 1 / 2) k h)

private lemma gamma_add_nat_div_gamma_add_nat {x : ℝ} (hx : 0 < x) (p : ℕ) :
    Real.Gamma (x + (p : ℝ) + 1 / 2) / Real.Gamma (x + (p : ℝ)) =
      (∏ i ∈ Finset.range p, (1 + (1 / 2 : ℝ) / (x + (i : ℝ)))) *
        (Real.Gamma (x + 1 / 2) / Real.Gamma x) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hxp_pos : 0 < x + (p : ℝ) := by positivity
    have hxp_half_pos : 0 < x + (p : ℝ) + 1 / 2 := by positivity
    have h_num : x + ((p + 1 : ℕ) : ℝ) + 1 / 2 = (x + (p : ℝ) + 1 / 2) + 1 := by
      push_cast; ring
    have h_den : x + ((p + 1 : ℕ) : ℝ) = (x + (p : ℝ)) + 1 := by
      push_cast; ring
    rw [h_num, Real.Gamma_add_one hxp_half_pos.ne', h_den, Real.Gamma_add_one hxp_pos.ne',
      mul_div_mul_comm, ih, Finset.prod_range_succ]
    have h_step : 1 + (1 / 2 : ℝ) / (x + (p : ℝ)) = (x + (p : ℝ) + 1 / 2) / (x + (p : ℝ)) := by
      have : x + (p : ℝ) ≠ 0 := hxp_pos.ne'
      field_simp
    rw [h_step]
    ring

/-- **Exact Rational Identity for the Transmutation Weight Ratio**:
For all $m, s \in \mathbb{N}$, $k \ge 1$, and $h \ge 0$, `weightShiftRatio m s k h` equals
$$
\frac{\operatorname{transmuteWeight}(h + m + 2k)}{
  \operatorname{transmuteWeight}(h + 2(k + s))}.
$$ -/
theorem weightShiftRatio_eq_transmuteWeight_div
    (m s : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : 0 ≤ h) :
    weightShiftRatio m s k h =
      transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) /
        transmuteWeight (h + (2 * (k + s) : ℕ)) := by
  set x : ℝ := h + 2 * (k : ℝ)
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx_ge : 2 ≤ x := by dsimp [x]; linarith
  have hx_pos : 0 < x := by linarith
  have hm_eq : h + (m : ℝ) + (2 * k : ℕ) = x + (m : ℝ) := by
    dsimp [x]; push_cast; ring
  have hs_eq : h + (2 * (k + s) : ℕ) = x + ((2 * s : ℕ) : ℝ) := by
    dsimp [x]; push_cast; ring
  rw [hm_eq, hs_eq]
  dsimp [weightShiftRatio, elementaryShiftFactor, transmuteWeight]
  have h1 := gamma_add_nat_div_gamma_add_nat hx_pos m
  have h2 := gamma_add_nat_div_gamma_add_nat hx_pos (2 * s)
  have h_prod_inv :
      (∏ j ∈ Finset.range (2 * s), (1 + - (1 / 2 : ℝ) / (x + ((j : ℝ) + 1 / 2)))) *
        (∏ j ∈ Finset.range (2 * s), (1 + (1 / 2 : ℝ) / (x + (j : ℝ)))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    have hxj : x + (j : ℝ) ≠ 0 := by positivity
    have hxj_half : x + ((j : ℝ) + 1 / 2) ≠ 0 := by positivity
    field_simp
    ring
  have hx2s_half : x + ((2 * s : ℕ) : ℝ) - 1 / 2 ≠ 0 := by
    have : (0 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h_pref :
      1 + ((m : ℝ) - ((2 * s : ℕ) : ℝ)) / (x + (((2 * s : ℕ) : ℝ) - 1 / 2)) =
        (x + (m : ℝ) - 1 / 2) / (x + ((2 * s : ℕ) : ℝ) - 1 / 2) := by
    have h_assoc : x + (((2 * s : ℕ) : ℝ) - 1 / 2) = x + ((2 * s : ℕ) : ℝ) - 1 / 2 := by ring
    rw [h_assoc, one_add_div hx2s_half]
    congr 1
    ring
  have h_g_pos : Real.Gamma (x + 1 / 2) / Real.Gamma x ≠ 0 :=
    (div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos hx_pos)).ne'
  have h_g2s_pos :
      Real.Gamma (x + ((2 * s : ℕ) : ℝ) + 1 / 2) / Real.Gamma (x + ((2 * s : ℕ) : ℝ)) ≠ 0 :=
    (div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))).ne'
  have h_div1 :
      (x + (m : ℝ) - 1 / 2) * Real.Gamma (x + (m : ℝ) + 1 / 2) / Real.Gamma (x + (m : ℝ)) =
        (x + (m : ℝ) - 1 / 2) *
          (Real.Gamma (x + (m : ℝ) + 1 / 2) / Real.Gamma (x + (m : ℝ))) :=
    mul_div_assoc _ _ _
  have h_div2 :
      (x + ((2 * s : ℕ) : ℝ) - 1 / 2) *
          Real.Gamma (x + ((2 * s : ℕ) : ℝ) + 1 / 2) / Real.Gamma (x + ((2 * s : ℕ) : ℝ)) =
        (x + ((2 * s : ℕ) : ℝ) - 1 / 2) *
          (Real.Gamma (x + ((2 * s : ℕ) : ℝ) + 1 / 2) / Real.Gamma (x + ((2 * s : ℕ) : ℝ))) :=
    mul_div_assoc _ _ _
  rw [h_div1, h_div2, h1, h2, h_pref]
  set P_m := ∏ i ∈ Finset.range m, (1 + (1 / 2 : ℝ) / (x + (i : ℝ)))
  set P_2s := ∏ i ∈ Finset.range (2 * s), (1 + (1 / 2 : ℝ) / (x + (i : ℝ)))
  set Q_2s := ∏ j ∈ Finset.range (2 * s), (1 + - (1 / 2 : ℝ) / (x + ((j : ℝ) + 1 / 2)))
  set G := Real.Gamma (x + 1 / 2) / Real.Gamma x
  have hP2s_ne : P_2s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h_prod_inv
    exact zero_ne_one h_prod_inv
  rw [eq_div_iff (mul_ne_zero hx2s_half (mul_ne_zero hP2s_ne h_g_pos))]
  calc
    (x + (m : ℝ) - 1 / 2) / (x + ((2 * s : ℕ) : ℝ) - 1 / 2) * P_m * Q_2s *
        ((x + ((2 * s : ℕ) : ℝ) - 1 / 2) * (P_2s * G))
      = ((x + (m : ℝ) - 1 / 2) / (x + ((2 * s : ℕ) : ℝ) - 1 / 2) *
          (x + ((2 * s : ℕ) : ℝ) - 1 / 2)) * P_m * (Q_2s * P_2s) * G := by ring
    _ = (x + (m : ℝ) - 1 / 2) * (P_m * G) := by
        rw [div_mul_cancel₀ _ hx2s_half, h_prod_inv]
        ring

/-- Helper predicate for spin-indexed functions $f_k(h)$ that are $C^2$ on $(-1, \infty)$ for all
$k \ge 1$ and have uniformly bounded 0th, 1st, and 2nd derivatives on $[0, \infty)$ across all
$k \ge 1$ and $h \ge 0$. -/
private def IsUniformC2OnGtNegOne (f : ℕ → ℝ → ℝ) : Prop :=
  (∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h → DifferentiableAt ℝ (f k) h) ∧
  (∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h → DifferentiableAt ℝ (deriv (f k)) h) ∧
  ∃ M : ℝ, 0 ≤ M ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, 0 ≤ h →
    |f k h| ≤ M ∧ |deriv (f k) h| ≤ M ∧ |deriv (deriv (f k)) h| ≤ M

private lemma isUniformC2OnGtNegOne_const_one :
    IsUniformC2OnGtNegOne (fun _ _ => (1 : ℝ)) := by
  refine ⟨fun {k} _ {h} _ => differentiableAt_const (1 : ℝ), ?_, 1, by norm_num,
    fun {k} _ {h} _ => ?_⟩
  · intro k _ h _
    rw [deriv_const']
    exact differentiableAt_const (0 : ℝ)
  · rw [deriv_const', deriv_const']
    simp

private lemma isUniformC2OnGtNegOne_spin_const {c : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ {k : ℕ}, 1 ≤ k → |c k| ≤ M) :
    IsUniformC2OnGtNegOne (fun k _ => c k) := by
  refine ⟨fun {k} _ {h} _ => differentiableAt_const (c k), ?_, M, hM,
    fun {k} hk {h} _ => ?_⟩
  · intro k _ h _
    rw [deriv_const']
    exact differentiableAt_const (0 : ℝ)
  · rw [deriv_const', deriv_const']
    simp [hc hk, hM]

private lemma isUniformC2OnGtNegOne_mul {f g : ℕ → ℝ → ℝ}
    (hf : IsUniformC2OnGtNegOne f) (hg : IsUniformC2OnGtNegOne g) :
    IsUniformC2OnGtNegOne (fun k h => f k h * g k h) := by
  obtain ⟨hf1, hf2, Mf, hMf, hfb⟩ := hf
  obtain ⟨hg1, hg2, Mg, hMg, hgb⟩ := hg
  have h_hasDeriv1 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (fun u => f k u * g k u) (deriv (f k) h * g k h + f k h * deriv (g k) h) h := by
    intro k hk h hh
    exact (hf1 hk hh).hasDerivAt.mul (hg1 hk hh).hasDerivAt
  have h_hasDeriv2 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (deriv (fun u => f k u * g k u))
        (deriv (deriv (f k)) h * g k h + 2 * deriv (f k) h * deriv (g k) h +
          f k h * deriv (deriv (g k)) h) h := by
    intro k hk h hh
    have h_ev : deriv (fun u => f k u * g k u) =ᶠ[𝓝 h]
        fun u => deriv (f k) u * g k u + f k u * deriv (g k) u := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
      exact (h_hasDeriv1 hk hu).deriv
    have hd : HasDerivAt (fun u => deriv (f k) u * g k u + f k u * deriv (g k) u)
        (deriv (deriv (f k)) h * g k h + 2 * deriv (f k) h * deriv (g k) h +
          f k h * deriv (deriv (g k)) h) h := by
      have hd1 := (hf2 hk hh).hasDerivAt.mul (hg1 hk hh).hasDerivAt
      have hd2 := (hf1 hk hh).hasDerivAt.mul (hg2 hk hh).hasDerivAt
      exact (hd1.add hd2).congr_deriv (by ring)
    exact hd.congr_of_eventuallyEq h_ev
  refine ⟨fun {k} hk {h} hh => (h_hasDeriv1 hk hh).differentiableAt,
    fun {k} hk {h} hh => (h_hasDeriv2 hk hh).differentiableAt,
    4 * Mf * Mg, by positivity, fun {k} hk {h} hh => ?_⟩
  have hh_gt : -1 < h := by linarith
  obtain ⟨hf0, hfd1, hfd2⟩ := hfb hk hh
  obtain ⟨hg0, hgd1, hgd2⟩ := hgb hk hh
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]
    have h1 := mul_le_mul hf0 hg0 (abs_nonneg _) hMf
    linarith [mul_nonneg hMf hMg]
  · rw [(h_hasDeriv1 hk hh_gt).deriv]
    have h1 : |deriv (f k) h * g k h| ≤ Mf * Mg := by
      rw [abs_mul]; exact mul_le_mul hfd1 hg0 (abs_nonneg _) hMf
    have h2 : |f k h * deriv (g k) h| ≤ Mf * Mg := by
      rw [abs_mul]; exact mul_le_mul hf0 hgd1 (abs_nonneg _) hMf
    have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith [mul_nonneg hMf hMg]
  · rw [(h_hasDeriv2 hk hh_gt).deriv]
    have h1 : |deriv (deriv (f k)) h * g k h| ≤ Mf * Mg := by
      rw [abs_mul]; exact mul_le_mul hfd2 hg0 (abs_nonneg _) hMf
    have h2 : |2 * deriv (f k) h * deriv (g k) h| ≤ 2 * (Mf * Mg) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hfd1 hgd1 (abs_nonneg _) hMf) (by norm_num)
    have h3 : |f k h * deriv (deriv (g k)) h| ≤ Mf * Mg := by
      rw [abs_mul]; exact mul_le_mul hf0 hgd2 (abs_nonneg _) hMf
    have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
    have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
    linarith

private lemma isUniformC2OnGtNegOne_finset_prod {ι : Type*} (S : Finset ι)
    (F : ι → ℕ → ℝ → ℝ) (hF : ∀ i ∈ S, IsUniformC2OnGtNegOne (F i)) :
    IsUniformC2OnGtNegOne (fun k h => ∏ i ∈ S, F i k h) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using isUniformC2OnGtNegOne_const_one
  | @insert a S ha ih =>
    have h_eq : (fun k h => ∏ i ∈ insert a S, F i k h) =
        fun k h => F a k h * (∏ i ∈ S, F i k h) := by
      ext k h
      exact Finset.prod_insert ha
    rw [h_eq]
    exact isUniformC2OnGtNegOne_mul
      (hF a (Finset.mem_insert_self a S))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

private lemma isUniformC2OnGtNegOne_elementaryShiftFactor (c d : ℝ) (hd : -(1 / 2) ≤ d) :
    IsUniformC2OnGtNegOne (elementaryShiftFactor c d) := by
  have hD_pos : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h → 0 < h + 2 * (k : ℝ) + d := by
    intro k hk h hh
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hD_ge_one : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, 0 ≤ h → 1 ≤ h + 2 * (k : ℝ) + d := by
    intro k hk h hh
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h_hasDeriv1 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (elementaryShiftFactor c d k)
        (-c / (h + 2 * (k : ℝ) + d) ^ 2) h := by
    intro k hk h hh
    unfold elementaryShiftFactor
    have hdD : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ) + d) 1 h := by
      simpa using ((hasDerivAt_id h).add_const (2 * (k : ℝ))).add_const d
    have hd_div := (hasDerivAt_const h c).div hdD (hD_pos hk hh).ne'
    have hd_add := (hasDerivAt_const h (1 : ℝ)).add hd_div
    exact hd_add.congr_deriv (by ring)
  have h_hasDeriv2 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (deriv (elementaryShiftFactor c d k))
        (2 * c * (h + 2 * (k : ℝ) + d) / ((h + 2 * (k : ℝ) + d) ^ 2) ^ 2) h := by
    intro k hk h hh
    have h_ev : deriv (elementaryShiftFactor c d k) =ᶠ[𝓝 h]
        fun u => -c / (u + 2 * (k : ℝ) + d) ^ 2 := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
      exact (h_hasDeriv1 hk hu).deriv
    have hdD : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ) + d) 1 h := by
      simpa using ((hasDerivAt_id h).add_const (2 * (k : ℝ))).add_const d
    have hdD2 : HasDerivAt (fun u : ℝ => (u + 2 * (k : ℝ) + d) ^ 2)
        (2 * (h + 2 * (k : ℝ) + d)) h := by
      have h_mul : HasDerivAt
          (fun u : ℝ => (u + 2 * (k : ℝ) + d) * (u + 2 * (k : ℝ) + d))
          (2 * (h + 2 * (k : ℝ) + d)) h :=
        (hdD.mul hdD).congr_deriv (by ring)
      simpa only [sq] using h_mul
    have hD2_ne : (h + 2 * (k : ℝ) + d) ^ 2 ≠ 0 := pow_ne_zero 2 (hD_pos hk hh).ne'
    have h_num_eq :
        (0 * (h + 2 * (k : ℝ) + d) ^ 2 - -c * (2 * (h + 2 * (k : ℝ) + d))) /
          ((h + 2 * (k : ℝ) + d) ^ 2) ^ 2 =
        2 * c * (h + 2 * (k : ℝ) + d) / ((h + 2 * (k : ℝ) + d) ^ 2) ^ 2 := by
      congr 1; ring
    have hd_div := ((hasDerivAt_const h (-c)).div hdD2 hD2_ne).congr_deriv h_num_eq
    exact hd_div.congr_of_eventuallyEq h_ev
  refine ⟨fun {k} hk {h} hh => (h_hasDeriv1 hk hh).differentiableAt,
    fun {k} hk {h} hh => (h_hasDeriv2 hk hh).differentiableAt,
    1 + 2 * |c|, by positivity, fun {k} hk {h} hh => ?_⟩
  have hh_gt : -1 < h := by linarith
  set D := h + 2 * (k : ℝ) + d
  have hD1 : 1 ≤ D := hD_ge_one hk hh
  have hD0 : 0 < D := by linarith
  have hD2 : 1 ≤ D ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · dsimp [elementaryShiftFactor]
    have h1 : |1 + c / D| ≤ 1 + |c| / D := by
      simpa [abs_div, abs_of_pos hD0] using abs_add_le (1 : ℝ) (c / D)
    have h2 : |c| / D ≤ |c| := div_le_self (abs_nonneg c) hD1
    linarith [abs_nonneg c]
  · rw [(h_hasDeriv1 hk hh_gt).deriv, abs_div, abs_neg, abs_pow, abs_of_pos hD0]
    have h1 : |c| / D ^ 2 ≤ |c| := div_le_self (abs_nonneg c) hD2
    linarith [abs_nonneg c]
  · rw [(h_hasDeriv2 hk hh_gt).deriv, abs_div, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hD0, abs_pow, abs_pow, abs_of_pos hD0]
    have hD4 : D ≤ (D ^ 2) ^ 2 := by nlinarith
    have h1 : 2 * |c| * D / (D ^ 2) ^ 2 ≤ 2 * |c| := by
      rw [div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hD4 (by positivity)
    linarith

private lemma isUniformC2OnGtNegOne_weightShiftRatio (m s : ℕ) :
    IsUniformC2OnGtNegOne (weightShiftRatio m s) := by
  unfold weightShiftRatio
  refine isUniformC2OnGtNegOne_mul (isUniformC2OnGtNegOne_mul ?_ ?_) ?_
  · refine isUniformC2OnGtNegOne_elementaryShiftFactor _ _ ?_
    have : (0 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · refine isUniformC2OnGtNegOne_finset_prod _ _ fun i _ => ?_
    refine isUniformC2OnGtNegOne_elementaryShiftFactor _ _ ?_
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    linarith
  · refine isUniformC2OnGtNegOne_finset_prod _ _ fun j _ => ?_
    refine isUniformC2OnGtNegOne_elementaryShiftFactor _ _ ?_
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith

/-! ### Internal Quintic $C^2$ Step Function for Positive-Twist Cutoff -/

private def unitStepPoly (t : ℝ) : ℝ :=
  6 * t ^ 5 - 15 * t ^ 4 + 10 * t ^ 3

private def unitStepPoly1 (t : ℝ) : ℝ :=
  30 * t ^ 4 - 60 * t ^ 3 + 30 * t ^ 2

private def unitStepPoly2 (t : ℝ) : ℝ :=
  120 * t ^ 3 - 180 * t ^ 2 + 60 * t

private lemma hasDerivAt_unitStepPoly (t : ℝ) :
    HasDerivAt unitStepPoly (unitStepPoly1 t) t := by
  unfold unitStepPoly unitStepPoly1
  have h5 : HasDerivAt (fun u : ℝ => u ^ 5) (5 * t ^ (5 - 1)) t := hasDerivAt_pow 5 t
  have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * t ^ (4 - 1)) t := hasDerivAt_pow 4 t
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ (3 - 1)) t := hasDerivAt_pow 3 t
  exact (((h5.const_mul 6).sub (h4.const_mul 15)).add (h3.const_mul 10)).congr_deriv (by ring)

private lemma hasDerivAt_unitStepPoly1 (t : ℝ) :
    HasDerivAt unitStepPoly1 (unitStepPoly2 t) t := by
  unfold unitStepPoly1 unitStepPoly2
  have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * t ^ (4 - 1)) t := hasDerivAt_pow 4 t
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ (3 - 1)) t := hasDerivAt_pow 3 t
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
  exact (((h4.const_mul 30).sub (h3.const_mul 60)).add (h2.const_mul 30)).congr_deriv (by ring)

private noncomputable def piecewiseClamp (c₀ c₁ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then c₀ else if 1 ≤ t then c₁ else g t

private lemma hasDerivAt_piecewiseClamp {c₀ c₁ : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg0 : g 0 = c₀) (hg'0 : g' 0 = 0) (hg1 : g 1 = c₁) (hg'1 : g' 1 = 0) (t : ℝ) :
    HasDerivAt (piecewiseClamp c₀ c₁ g) (piecewiseClamp 0 0 g' t) t := by
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · have h_val : piecewiseClamp 0 0 g' t = 0 := by
      simp [piecewiseClamp, ht_neg.le]
    rw [h_val]
    have h_ev : piecewiseClamp c₀ c₁ g =ᶠ[𝓝 t] fun _ => c₀ := by
      filter_upwards [isOpen_Iio.mem_nhds ht_neg] with u hu
      simp [piecewiseClamp, (mem_Iio.mp hu).le]
    exact (hasDerivAt_const t c₀).congr_of_eventuallyEq h_ev
  · have h_val : piecewiseClamp 0 0 g' 0 = 0 := by simp [piecewiseClamp]
    rw [h_val, ← hasDerivWithinAt_univ, ← Iic_union_Ici (a := (0 : ℝ))]
    refine HasDerivWithinAt.union ?_ ?_
    · refine (hasDerivWithinAt_const (0 : ℝ) (Iic (0 : ℝ)) c₀).congr ?_ ?_
      · intro u hu
        simp [piecewiseClamp, mem_Iic.mp hu]
      · simp [piecewiseClamp]
    · have hd_g : HasDerivWithinAt g (g' 0) (Ici (0 : ℝ)) 0 := (hg 0).hasDerivWithinAt
      rw [hg'0] at hd_g
      have h_ev : piecewiseClamp c₀ c₁ g =ᶠ[𝓝[Ici (0 : ℝ)] (0 : ℝ)] g := by
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_Iio.mem_nhds zero_lt_one)] with u hu0 hu1
        rw [mem_Ici] at hu0
        rw [mem_Iio] at hu1
        dsimp [piecewiseClamp]
        split_ifs with h1 h2
        · have : u = 0 := le_antisymm h1 hu0
          rw [this, hg0]
        · linarith
        · rfl
      exact hd_g.congr_of_eventuallyEq h_ev (by simp [piecewiseClamp, hg0])
  · rcases lt_trichotomy t 1 with ht_lt1 | rfl | ht_gt1
    · have h_val : piecewiseClamp 0 0 g' t = g' t := by
        simp [piecewiseClamp, not_le.mpr ht_pos, not_le.mpr ht_lt1]
      rw [h_val]
      have h_ev : piecewiseClamp c₀ c₁ g =ᶠ[𝓝 t] g := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨ht_pos, ht_lt1⟩] with u hu
        simp [piecewiseClamp, not_le.mpr hu.1, not_le.mpr hu.2]
      exact (hg t).congr_of_eventuallyEq h_ev
    · have h_val : piecewiseClamp 0 0 g' 1 = 0 := by simp [piecewiseClamp]
      rw [h_val, ← hasDerivWithinAt_univ, ← Iic_union_Ici (a := (1 : ℝ))]
      refine HasDerivWithinAt.union ?_ ?_
      · have hd_g : HasDerivWithinAt g (g' 1) (Iic (1 : ℝ)) 1 := (hg 1).hasDerivWithinAt
        rw [hg'1] at hd_g
        have h_ev : piecewiseClamp c₀ c₁ g =ᶠ[𝓝[Iic (1 : ℝ)] (1 : ℝ)] g := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds zero_lt_one)] with u hu1 hu0
          rw [mem_Iic] at hu1
          rw [mem_Ioi] at hu0
          dsimp [piecewiseClamp]
          split_ifs with h1 h2
          · linarith
          · have : u = 1 := le_antisymm hu1 h2
            rw [this, hg1]
          · rfl
        exact hd_g.congr_of_eventuallyEq h_ev (by simp [piecewiseClamp, hg1])
      · refine (hasDerivWithinAt_const (1 : ℝ) (Ici (1 : ℝ)) c₁).congr ?_ ?_
        · intro u hu
          rw [mem_Ici] at hu
          have hu_not_le : ¬ u ≤ 0 := by linarith
          simp [piecewiseClamp, hu_not_le, hu]
        · simp [piecewiseClamp]
    · have ht_not_le : ¬ t ≤ 0 := by linarith
      have h_val : piecewiseClamp 0 0 g' t = 0 := by
        simp [piecewiseClamp, ht_not_le, ht_gt1.le]
      rw [h_val]
      have h_ev : piecewiseClamp c₀ c₁ g =ᶠ[𝓝 t] fun _ => c₁ := by
        filter_upwards [isOpen_Ioi.mem_nhds ht_gt1] with u hu
        rw [mem_Ioi] at hu
        have hu_not_le : ¬ u ≤ 0 := by linarith
        simp [piecewiseClamp, hu_not_le, hu.le]
      exact (hasDerivAt_const t c₁).congr_of_eventuallyEq h_ev

private noncomputable def smoothUnitStep : ℝ → ℝ :=
  piecewiseClamp 0 1 unitStepPoly

private noncomputable def smoothUnitStep1 : ℝ → ℝ :=
  piecewiseClamp 0 0 unitStepPoly1

private noncomputable def smoothUnitStep2 : ℝ → ℝ :=
  piecewiseClamp 0 0 unitStepPoly2

private lemma hasDerivAt_smoothUnitStep (t : ℝ) :
    HasDerivAt smoothUnitStep (smoothUnitStep1 t) t :=
  hasDerivAt_piecewiseClamp hasDerivAt_unitStepPoly
    (by norm_num [unitStepPoly]) (by norm_num [unitStepPoly1])
    (by norm_num [unitStepPoly]) (by norm_num [unitStepPoly1]) t

private lemma hasDerivAt_smoothUnitStep1 (t : ℝ) :
    HasDerivAt smoothUnitStep1 (smoothUnitStep2 t) t :=
  hasDerivAt_piecewiseClamp hasDerivAt_unitStepPoly1
    (by norm_num [unitStepPoly1]) (by norm_num [unitStepPoly2])
    (by norm_num [unitStepPoly1]) (by norm_num [unitStepPoly2]) t

private lemma abs_smoothUnitStep_le (t : ℝ) :
    |smoothUnitStep t| ≤ 360 ∧ |smoothUnitStep1 t| ≤ 360 ∧ |smoothUnitStep2 t| ≤ 360 := by
  dsimp [smoothUnitStep, smoothUnitStep1, smoothUnitStep2, piecewiseClamp]
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · push_neg at h1 h2
    have ht2_nn : 0 ≤ t ^ 2 := by positivity
    have ht3_nn : 0 ≤ t ^ 3 := by positivity
    have ht4_nn : 0 ≤ t ^ 4 := by positivity
    have ht5_nn : 0 ≤ t ^ 5 := by positivity
    have ht2_le : t ^ 2 ≤ 1 := by nlinarith
    have ht3_le : t ^ 3 ≤ 1 := by nlinarith
    have ht4_le : t ^ 4 ≤ 1 := by nlinarith
    have ht5_le : t ^ 5 ≤ 1 := by nlinarith
    dsimp [unitStepPoly, unitStepPoly1, unitStepPoly2]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

private noncomputable def smoothCutoff (B₀ h : ℝ) : ℝ :=
  smoothUnitStep (2 / B₀ * h - 1)

private noncomputable def smoothCutoff1 (B₀ h : ℝ) : ℝ :=
  (2 / B₀) * smoothUnitStep1 (2 / B₀ * h - 1)

private noncomputable def smoothCutoff2 (B₀ h : ℝ) : ℝ :=
  (2 / B₀) ^ 2 * smoothUnitStep2 (2 / B₀ * h - 1)

private lemma smoothCutoff_eq_zero_of_le_half {B₀ h : ℝ} (hB₀ : 0 < B₀) (hh : h ≤ B₀ / 2) :
    smoothCutoff B₀ h = 0 := by
  have h_le : 2 / B₀ * h - 1 ≤ 0 := by
    have : 2 / B₀ * h ≤ 2 / B₀ * (B₀ / 2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    have h_eq : 2 / B₀ * (B₀ / 2) = 1 := by field_simp [hB₀.ne']
    linarith
  simp [smoothCutoff, smoothUnitStep, piecewiseClamp, h_le]

private lemma smoothCutoff_eq_one_of_ge {B₀ h : ℝ} (hB₀ : 0 < B₀) (hh : B₀ ≤ h) :
    smoothCutoff B₀ h = 1 := by
  have h_ge : 1 ≤ 2 / B₀ * h - 1 := by
    have : 2 / B₀ * B₀ ≤ 2 / B₀ * h :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    have h_eq : 2 / B₀ * B₀ = 2 := div_mul_cancel₀ 2 hB₀.ne'
    linarith
  have h_not_le : ¬ 2 / B₀ * h - 1 ≤ 0 := by linarith
  simp [smoothCutoff, smoothUnitStep, piecewiseClamp, h_not_le, h_ge]

private lemma hasDerivAt_smoothCutoff (B₀ h : ℝ) :
    HasDerivAt (smoothCutoff B₀) (smoothCutoff1 B₀ h) h := by
  unfold smoothCutoff smoothCutoff1
  have h_aff : HasDerivAt (fun u : ℝ => 2 / B₀ * u - 1) (2 / B₀) h := by
    simpa using ((hasDerivAt_id h).const_mul (2 / B₀)).sub_const 1
  exact ((hasDerivAt_smoothUnitStep (2 / B₀ * h - 1)).comp h h_aff).congr_deriv (mul_comm _ _)

private lemma hasDerivAt_smoothCutoff1 (B₀ h : ℝ) :
    HasDerivAt (smoothCutoff1 B₀) (smoothCutoff2 B₀ h) h := by
  unfold smoothCutoff1 smoothCutoff2
  have h_aff : HasDerivAt (fun u : ℝ => 2 / B₀ * u - 1) (2 / B₀) h := by
    simpa using ((hasDerivAt_id h).const_mul (2 / B₀)).sub_const 1
  have h_comp := (hasDerivAt_smoothUnitStep1 (2 / B₀ * h - 1)).comp h h_aff
  exact (h_comp.const_mul (2 / B₀)).congr_deriv (by ring)

private lemma isUniformC2OnGtNegOne_smoothCutoff {B₀ : ℝ} (hB₀ : 0 < B₀) :
    IsUniformC2OnGtNegOne (fun _ h => smoothCutoff B₀ h) := by
  have hd1 : ∀ h : ℝ, deriv (smoothCutoff B₀) h = smoothCutoff1 B₀ h :=
    fun h => (hasDerivAt_smoothCutoff B₀ h).deriv
  have hd2 : ∀ h : ℝ, deriv (deriv (smoothCutoff B₀)) h = smoothCutoff2 B₀ h := by
    intro h
    rw [funext hd1]
    exact (hasDerivAt_smoothCutoff1 B₀ h).deriv
  refine ⟨fun {k} _ {h} _ => (hasDerivAt_smoothCutoff B₀ h).differentiableAt,
    fun {k} _ {h} _ => ?_,
    360 * (1 + 2 / B₀ + (2 / B₀) ^ 2), by positivity, fun {k} _ {h} _ => ?_⟩
  · rw [funext hd1]
    exact (hasDerivAt_smoothCutoff1 B₀ h).differentiableAt
  · rw [hd1 h, hd2 h]
    obtain ⟨hb0, hb1, hb2⟩ := abs_smoothUnitStep_le (2 / B₀ * h - 1)
    have hc1 : 0 ≤ 2 / B₀ := by positivity
    have hc2 : 0 ≤ (2 / B₀) ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · dsimp [smoothCutoff]
      nlinarith
    · dsimp [smoothCutoff1]
      rw [abs_mul, abs_of_nonneg hc1]
      nlinarith
    · dsimp [smoothCutoff2]
      rw [abs_mul, abs_of_nonneg hc2]
      nlinarith

/-- The kinematic multiplier
$$
W_{m, s}(k, h) :=
  \left(\frac{k + s}{k}\right)^{2\Delta_\phi} \operatorname{weightShiftRatio}(m, s, k, h)
$$
that converts the normalized block coefficient $\mathcal{R}_{m, s}(\nu, k, h)$ into the transmuted
collinear transfer ratio on $[\min(h_{\mathrm{gap}}, \Delta_\phi), \infty)$. -/
noncomputable def kinematicMultiplier (Δ_phi : ℝ) (m s k : ℕ) (h : ℝ) : ℝ :=
  (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) * weightShiftRatio m s k h

private lemma isUniformC2OnGtNegOne_kinematicMultiplier
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (m s : ℕ) :
    IsUniformC2OnGtNegOne (kinematicMultiplier Δ_phi m s) := by
  unfold kinematicMultiplier
  refine isUniformC2OnGtNegOne_mul ?_ (isUniformC2OnGtNegOne_weightShiftRatio m s)
  refine isUniformC2OnGtNegOne_spin_const (M := (1 + (s : ℝ)) ^ (2 * Δ_phi)) (by positivity) ?_
  intro k hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_div_pos : 0 ≤ ((k + s : ℕ) : ℝ) / (k : ℝ) := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg h_div_pos _)]
  refine Real.rpow_le_rpow h_div_pos ?_ (by linarith)
  rw [div_le_iff₀ hk_pos]
  push_cast
  nlinarith

/-- Smoothly cut-off kinematic multiplier vanishing for $h \le \frac{1}{2}\min(h_{\mathrm{gap}}, \Delta_\phi)$
and coinciding with `kinematicMultiplier Δ_phi m s k h` for $h \ge \min(h_{\mathrm{gap}}, \Delta_\phi)$. -/
private noncomputable def cutoffKinematicMultiplier (Δ_phi h_gap : ℝ) (m s k : ℕ) (h : ℝ) : ℝ :=
  smoothCutoff (min h_gap Δ_phi) h * kinematicMultiplier Δ_phi m s k h

private lemma isUniformC2OnGtNegOne_cutoffKinematicMultiplier
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (m s : ℕ) :
    IsUniformC2OnGtNegOne (cutoffKinematicMultiplier Δ_phi h_gap m s) :=
  isUniformC2OnGtNegOne_mul
    (isUniformC2OnGtNegOne_smoothCutoff (lt_min hh_gap hΔ))
    (isUniformC2OnGtNegOne_kinematicMultiplier hΔ m s)

/-! ### Uniform $C^2$ Bounds for the Rescaled Inverse Transmutation Weight -/

private noncomputable def invLinearShiftFactor (k : ℕ) (h : ℝ) : ℝ :=
  2 * (k : ℝ) / (h + 2 * (k : ℝ) - 1 / 2)

private lemma isUniformC2OnGtNegOne_invLinearShiftFactor :
    IsUniformC2OnGtNegOne invLinearShiftFactor := by
  have hD_pos : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h → 0 < h + 2 * (k : ℝ) - 1 / 2 := by
    intro k hk h hh
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hD_ge_one : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, 0 ≤ h → 1 ≤ h + 2 * (k : ℝ) - 1 / 2 := by
    intro k hk h hh
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h_hasDeriv1 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (invLinearShiftFactor k)
        (- (2 * (k : ℝ)) / (h + 2 * (k : ℝ) - 1 / 2) ^ 2) h := by
    intro k hk h hh
    unfold invLinearShiftFactor
    have hdD : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ) - 1 / 2) 1 h := by
      simpa using ((hasDerivAt_id h).add_const (2 * (k : ℝ))).sub_const (1 / 2 : ℝ)
    exact ((hasDerivAt_const h (2 * (k : ℝ))).div hdD (hD_pos hk hh).ne').congr_deriv (by ring)
  have h_hasDeriv2 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (deriv (invLinearShiftFactor k))
        (4 * (k : ℝ) * (h + 2 * (k : ℝ) - 1 / 2) / ((h + 2 * (k : ℝ) - 1 / 2) ^ 2) ^ 2) h := by
    intro k hk h hh
    have h_ev : deriv (invLinearShiftFactor k) =ᶠ[𝓝 h]
        fun u => - (2 * (k : ℝ)) / (u + 2 * (k : ℝ) - 1 / 2) ^ 2 := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
      exact (h_hasDeriv1 hk hu).deriv
    have hdD : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ) - 1 / 2) 1 h := by
      simpa using ((hasDerivAt_id h).add_const (2 * (k : ℝ))).sub_const (1 / 2 : ℝ)
    have hdD2 : HasDerivAt (fun u : ℝ => (u + 2 * (k : ℝ) - 1 / 2) ^ 2)
        (2 * (h + 2 * (k : ℝ) - 1 / 2)) h := by
      have h_mul : HasDerivAt
          (fun u : ℝ => (u + 2 * (k : ℝ) - 1 / 2) * (u + 2 * (k : ℝ) - 1 / 2))
          (2 * (h + 2 * (k : ℝ) - 1 / 2)) h :=
        (hdD.mul hdD).congr_deriv (by ring)
      simpa only [sq] using h_mul
    have hD2_ne : (h + 2 * (k : ℝ) - 1 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (hD_pos hk hh).ne'
    have h_num_eq :
        (0 * (h + 2 * (k : ℝ) - 1 / 2) ^ 2 -
          - (2 * (k : ℝ)) * (2 * (h + 2 * (k : ℝ) - 1 / 2))) /
          ((h + 2 * (k : ℝ) - 1 / 2) ^ 2) ^ 2 =
        4 * (k : ℝ) * (h + 2 * (k : ℝ) - 1 / 2) /
          ((h + 2 * (k : ℝ) - 1 / 2) ^ 2) ^ 2 := by
      congr 1; ring
    have hd_div := ((hasDerivAt_const h (- (2 * (k : ℝ)))).div hdD2 hD2_ne).congr_deriv h_num_eq
    exact hd_div.congr_of_eventuallyEq h_ev
  refine ⟨fun {k} hk {h} hh => (h_hasDeriv1 hk hh).differentiableAt,
    fun {k} hk {h} hh => (h_hasDeriv2 hk hh).differentiableAt,
    4, by norm_num, fun {k} hk {h} hh => ?_⟩
  have hh_gt : -1 < h := by linarith
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set D := h + 2 * (k : ℝ) - 1 / 2
  have hD1 : 1 ≤ D := hD_ge_one hk hh
  have hD0 : 0 < D := by linarith
  have h2k_le : 2 * (k : ℝ) ≤ 2 * D := by dsimp [D]; linarith
  refine ⟨?_, ?_, ?_⟩
  · dsimp [invLinearShiftFactor]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hD0]
    linarith
  · rw [(h_hasDeriv1 hk hh_gt).deriv, abs_div, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)), abs_pow, abs_of_pos hD0,
      div_le_iff₀ (by positivity)]
    nlinarith
  · rw [(h_hasDeriv2 hk hh_gt).deriv, abs_of_nonneg (by positivity),
      div_le_iff₀ (by positivity)]
    change 4 * (k : ℝ) * D ≤ 4 * (D ^ 2) ^ 2
    have hD2 : D ≤ D ^ 2 := by nlinarith
    have hD2_ge1 : 1 ≤ D ^ 2 := by nlinarith
    nlinarith

private noncomputable def complexGammaRatioHalf (z : ℂ) : ℂ :=
  Complex.Gamma z * (Complex.Gamma (z + 1 / 2))⁻¹

private noncomputable def realGammaRatioHalf (x : ℝ) : ℝ :=
  (complexGammaRatioHalf (x : ℂ)).re

private lemma realGammaRatioHalf_eq (x : ℝ) :
    realGammaRatioHalf x = Real.Gamma x / Real.Gamma (x + 1 / 2) := by
  dsimp [realGammaRatioHalf, complexGammaRatioHalf]
  have h_add : (x : ℂ) + 1 / 2 = ((x + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

private lemma isOpen_re_pos : IsOpen { z : ℂ | 0 < z.re } :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma differentiableAt_complexGammaRatioHalf {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ complexGammaRatioHalf z := by
  unfold complexGammaRatioHalf
  have h1 : DifferentiableAt ℂ Complex.Gamma z := by
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have h_re : z.re = (- (m : ℂ)).re := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at h_re
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gamma (w + 1 / 2))⁻¹) z :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp z
      (differentiableAt_id.add (differentiableAt_const (1 / 2 : ℂ)))
  exact h1.mul h2

private lemma differentiableOn_complexGammaRatioHalf :
    DifferentiableOn ℂ complexGammaRatioHalf { z : ℂ | 0 < z.re } :=
  fun _ hz => (differentiableAt_complexGammaRatioHalf hz).differentiableWithinAt

private lemma differentiableAt_deriv_complexGammaRatioHalf {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (deriv complexGammaRatioHalf) z :=
  (differentiableOn_complexGammaRatioHalf.deriv isOpen_re_pos).differentiableAt
    (isOpen_re_pos.mem_nhds hz)

private lemma hasDerivAt_realGammaRatioHalf {x : ℝ} (hx : 0 < x) :
    HasDerivAt realGammaRatioHalf ((deriv complexGammaRatioHalf (x : ℂ)).re) x := by
  have hzx : 0 < (x : ℂ).re := by simpa using hx
  have hdC : HasDerivAt complexGammaRatioHalf (deriv complexGammaRatioHalf (x : ℂ)) (x : ℂ) :=
    (differentiableAt_complexGammaRatioHalf hzx).hasDerivAt
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hdC.comp_ofReal

private lemma hasDerivAt_deriv_realGammaRatioHalf {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv realGammaRatioHalf)
      ((deriv (deriv complexGammaRatioHalf) (x : ℂ)).re) x := by
  have hzx : 0 < (x : ℂ).re := by simpa using hx
  have h_ev : deriv realGammaRatioHalf =ᶠ[𝓝 x]
      fun u : ℝ => (deriv complexGammaRatioHalf (u : ℂ)).re := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
    exact (hasDerivAt_realGammaRatioHalf hu).deriv
  have hdC : HasDerivAt (deriv complexGammaRatioHalf)
      (deriv (deriv complexGammaRatioHalf) (x : ℂ)) (x : ℂ) :=
    (differentiableAt_deriv_complexGammaRatioHalf hzx).hasDerivAt
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hdC.comp_ofReal).congr_of_eventuallyEq h_ev

private lemma transmuteCoreWeight_add_half_le_inv_sqrt {y : ℝ} (hy : 1 / 2 < y) :
    transmuteCoreWeight (y + 1 / 2) ≤ 1 / Real.sqrt (y - 1 / 2) := by
  have hy_sub_pos : 0 < y - 1 / 2 := sub_pos.mpr hy
  have hy_pos : 0 < y := by linarith
  have hy_add_gt : 1 / 2 < y + 1 / 2 := by linarith
  have h_int1 := integral_betaKernel hy_add_gt 0
  have h_int2 := integral_betaKernel hy 0
  simp only [realPochhammer_zero, div_one, mul_one] at h_int1 h_int2
  have h_mono :
      (∫ s in Ioo (0 : ℝ) 1, betaKernel (y + 1 / 2) 0 s) ≤
        ∫ s in Ioo (0 : ℝ) 1, betaKernel y 0 s := by
    refine setIntegral_mono_on (integrableOn_betaKernel hy_add_gt 0)
      (integrableOn_betaKernel hy 0) measurableSet_Ioo fun s hs => ?_
    dsimp [betaKernel]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (sub_pos.mpr hs.2).le _)
    exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)
  rw [h_int1, h_int2] at h_mono
  have h_sqrt_pi_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h_core_le : transmuteCoreWeight (y + 1 / 2) ≤ transmuteCoreWeight y :=
    le_of_mul_le_mul_left h_mono h_sqrt_pi_pos
  have h_prod :
      transmuteCoreWeight (y + 1 / 2) * transmuteCoreWeight y = 1 / (y - 1 / 2) := by
    dsimp [transmuteCoreWeight]
    set a : ℝ := y - 1 / 2
    have ha_ne : a ≠ 0 := hy_sub_pos.ne'
    have h_sub1 : y + 1 / 2 - 1 / 2 = y := by ring
    have h_add1 : y + 1 / 2 = a + 1 := by dsimp [a]; ring
    rw [h_sub1, h_add1, Real.Gamma_add_one ha_ne]
    have hGy_ne : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy_pos).ne'
    have hGa_ne : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos hy_sub_pos).ne'
    field_simp
  have h_core_pos : 0 ≤ transmuteCoreWeight (y + 1 / 2) :=
    (transmuteCoreWeight_pos hy_add_gt).le
  have h_sq_le :
      transmuteCoreWeight (y + 1 / 2) ^ 2 ≤ (1 / Real.sqrt (y - 1 / 2)) ^ 2 := by
    calc
      transmuteCoreWeight (y + 1 / 2) ^ 2
        = transmuteCoreWeight (y + 1 / 2) * transmuteCoreWeight (y + 1 / 2) := sq _
      _ ≤ transmuteCoreWeight (y + 1 / 2) * transmuteCoreWeight y :=
          mul_le_mul_of_nonneg_left h_core_le h_core_pos
      _ = 1 / (y - 1 / 2) := h_prod
      _ = (1 / Real.sqrt (y - 1 / 2)) ^ 2 := by
          rw [div_pow, one_pow, Real.sq_sqrt hy_sub_pos.le]
  exact (abs_le_of_sq_le_sq' h_sq_le (by positivity)).2

private lemma norm_complexGammaRatioHalf_le {z : ℂ} {y : ℝ}
    (hy : 1 / 2 < y) (hyz : y ≤ z.re) :
    ‖complexGammaRatioHalf z‖ ≤ 1 / Real.sqrt (y - 1 / 2) := by
  have hz_re : 0 < z.re := by linarith
  have hv_re : 0 < (1 / 2 : ℂ).re := by norm_num
  have h_beta := Complex.betaIntegral_eq_Gamma_mul_div z (1 / 2 : ℂ) hz_re hv_re
  have h_half_real : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h_half_real, Complex.Gamma_ofReal, Real.Gamma_one_half_eq] at h_beta
  have h_beta_eq :
      Complex.betaIntegral z (1 / 2 : ℂ) =
        (Real.sqrt π : ℂ) * complexGammaRatioHalf z := by
    rw [h_half_real, h_beta]
    dsimp [complexGammaRatioHalf]
    rw [← h_half_real]
    ring
  have h_int_eq :
      Complex.betaIntegral z (1 / 2 : ℂ) =
        ∫ s in Ioo (0 : ℝ) 1,
          (s : ℂ) ^ (z - 1) * (1 - (s : ℂ)) ^ ((1 / 2 : ℂ) - 1) := by
    dsimp [Complex.betaIntegral]
    rw [intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have h_norm_int :
      ‖Complex.betaIntegral z (1 / 2 : ℂ)‖ ≤
        ∫ s in Ioo (0 : ℝ) 1, betaKernel (y + 1 / 2) 0 s := by
    rw [h_int_eq]
    refine norm_integral_le_of_norm_le
      (integrableOn_betaKernel (by linarith : 1 / 2 < y + 1 / 2) 0)
      ((ae_restrict_mem measurableSet_Ioo).mono fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
    have h_sub_c : 1 - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, h_sub_c,
      Complex.norm_cpow_eq_rpow_re_of_pos hs0,
      Complex.norm_cpow_eq_rpow_re_of_pos hs1]
    have h_re1 : (z - 1).re = z.re - 1 := by simp
    have h_re2 : ((1 / 2 : ℂ) - 1).re = -1 / 2 := by norm_num
    rw [h_re1, h_re2]
    dsimp [betaKernel]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs1.le _)
    exact Real.rpow_le_rpow_of_exponent_ge hs0 hs.2.le (by linarith)
  have h_eval_y := integral_betaKernel (by linarith : 1 / 2 < y + 1 / 2) 0
  simp only [realPochhammer_zero, div_one, mul_one] at h_eval_y
  rw [h_beta_eq, norm_mul, Complex.norm_of_nonneg (Real.sqrt_pos.mpr Real.pi_pos).le,
    h_eval_y] at h_norm_int
  have h_le1 :
      ‖complexGammaRatioHalf z‖ ≤ transmuteCoreWeight (y + 1 / 2) :=
    le_of_mul_le_mul_left h_norm_int (Real.sqrt_pos.mpr Real.pi_pos)
  exact h_le1.trans (transmuteCoreWeight_add_half_le_inv_sqrt hy)

private noncomputable def scaledGammaRatioHalf (k : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ)) * realGammaRatioHalf (h + 2 * (k : ℝ))

private lemma isUniformC2OnGtNegOne_scaledGammaRatioHalf :
    IsUniformC2OnGtNegOne scaledGammaRatioHalf := by
  have hx_pos : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h → 0 < h + 2 * (k : ℝ) := by
    intro k hk h hh
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h_hasDeriv1 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (scaledGammaRatioHalf k)
        (Real.sqrt (2 * (k : ℝ)) *
          (deriv complexGammaRatioHalf ((h + 2 * (k : ℝ) : ℝ) : ℂ)).re) h := by
    intro k hk h hh
    unfold scaledGammaRatioHalf
    have hd_aff : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ)) 1 h := by
      simpa using (hasDerivAt_id h).add_const (2 * (k : ℝ))
    have hd_g := (hasDerivAt_realGammaRatioHalf (hx_pos hk hh)).comp h hd_aff
    exact (hd_g.const_mul (Real.sqrt (2 * (k : ℝ)))).congr_deriv (by ring)
  have h_hasDeriv2 : ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (deriv (scaledGammaRatioHalf k))
        (Real.sqrt (2 * (k : ℝ)) *
          (deriv (deriv complexGammaRatioHalf) ((h + 2 * (k : ℝ) : ℝ) : ℂ)).re) h := by
    intro k hk h hh
    have h_ev : deriv (scaledGammaRatioHalf k) =ᶠ[𝓝 h]
        fun u : ℝ => Real.sqrt (2 * (k : ℝ)) *
          deriv realGammaRatioHalf (u + 2 * (k : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
      rw [(h_hasDeriv1 hk hu).deriv, (hasDerivAt_realGammaRatioHalf (hx_pos hk hu)).deriv]
    have hd_aff : HasDerivAt (fun u : ℝ => u + 2 * (k : ℝ)) 1 h := by
      simpa using (hasDerivAt_id h).add_const (2 * (k : ℝ))
    have hd_g' := (hasDerivAt_deriv_realGammaRatioHalf (hx_pos hk hh)).comp h hd_aff
    exact ((hd_g'.const_mul (Real.sqrt (2 * (k : ℝ)))).congr_deriv (by ring)).congr_of_eventuallyEq
      h_ev
  refine ⟨fun {k} hk {h} hh => (h_hasDeriv1 hk hh).differentiableAt,
    fun {k} hk {h} hh => (h_hasDeriv2 hk hh).differentiableAt,
    32, by norm_num, fun {k} hk {h} hh => ?_⟩
  have hh_gt : -1 < h := by linarith
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set x : ℝ := h + 2 * (k : ℝ)
  set y : ℝ := x - 1 / 2
  have hy_gt : 1 / 2 < y := by dsimp [y, x]; linarith
  have hy_sub_ge_k : (k : ℝ) ≤ y - 1 / 2 := by dsimp [y, x]; linarith
  have h_ball_sub : Metric.closedBall (x : ℂ) (1 / 2) ⊆ { z : ℂ | 0 < z.re } := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h_re_diff : ((x : ℂ) - z).re ≤ 1 / 2 := by
      rw [← norm_neg, neg_sub] at hz
      exact (Complex.re_le_norm _).trans hz
    simp only [Complex.sub_re, Complex.ofReal_re] at h_re_diff
    change 0 < z.re
    linarith
  have h_ball_bd : ∀ z ∈ Metric.closedBall (x : ℂ) (1 / 2),
      ‖complexGammaRatioHalf z‖ ≤ 2 / Real.sqrt (2 * (k : ℝ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h_re_diff : ((x : ℂ) - z).re ≤ 1 / 2 := by
      rw [← norm_neg, neg_sub] at hz
      exact (Complex.re_le_norm _).trans hz
    simp only [Complex.sub_re, Complex.ofReal_re] at h_re_diff
    have hyz : y ≤ z.re := by dsimp [y]; linarith
    have h1 := norm_complexGammaRatioHalf_le hy_gt hyz
    have h_sqrt_le : Real.sqrt (k : ℝ) ≤ Real.sqrt (y - 1 / 2) :=
      Real.sqrt_le_sqrt hy_sub_ge_k
    have h_sqrt_k_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have h_inv_le : 1 / Real.sqrt (y - 1 / 2) ≤ 1 / Real.sqrt (k : ℝ) :=
      one_div_le_one_div_of_le h_sqrt_k_pos h_sqrt_le
    have h_sqrt2 : Real.sqrt (2 * (k : ℝ)) ≤ 2 * Real.sqrt (k : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
      have h_s2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_iff]; norm_num
      exact mul_le_mul_of_nonneg_right h_s2 h_sqrt_k_pos.le
    have h_sqrt2k_pos : 0 < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by linarith)
    have h_div2 : 1 / Real.sqrt (k : ℝ) ≤ 2 / Real.sqrt (2 * (k : ℝ)) := by
      rw [div_le_div_iff₀ h_sqrt_k_pos h_sqrt2k_pos]
      linarith
    exact h1.trans (h_inv_le.trans h_div2)
  have hr_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have h0_bd : ‖complexGammaRatioHalf (x : ℂ)‖ ≤ 2 / Real.sqrt (2 * (k : ℝ)) :=
    h_ball_bd (x : ℂ) (Metric.mem_closedBall_self hr_pos.le)
  have h1_bd :=
    norm_deriv_le_of_ball_bound isOpen_re_pos differentiableOn_complexGammaRatioHalf
      hr_pos h_ball_sub h_ball_bd
  have h2_bd :=
    norm_deriv2_le_of_ball_bound isOpen_re_pos differentiableOn_complexGammaRatioHalf
      hr_pos h_ball_sub h_ball_bd
  have h_sqrt2k_pos : 0 < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have h_sqrt2k_ne : Real.sqrt (2 * (k : ℝ)) ≠ 0 := h_sqrt2k_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · dsimp [scaledGammaRatioHalf, realGammaRatioHalf]
    rw [abs_mul, abs_of_pos h_sqrt2k_pos]
    have h_re_le : |(complexGammaRatioHalf (x : ℂ)).re| ≤ 2 / Real.sqrt (2 * (k : ℝ)) :=
      (Complex.abs_re_le_norm _).trans h0_bd
    have h_mul := mul_le_mul_of_nonneg_left h_re_le h_sqrt2k_pos.le
    rw [mul_div_cancel₀ _ h_sqrt2k_ne] at h_mul
    linarith
  · rw [(h_hasDeriv1 hk hh_gt).deriv, abs_mul, abs_of_pos h_sqrt2k_pos]
    have h_re_le :
        |(deriv complexGammaRatioHalf (x : ℂ)).re| ≤
          (2 / Real.sqrt (2 * (k : ℝ))) / (1 / 2) :=
      (Complex.abs_re_le_norm _).trans h1_bd
    have h_mul := mul_le_mul_of_nonneg_left h_re_le h_sqrt2k_pos.le
    have h_simp :
        Real.sqrt (2 * (k : ℝ)) * ((2 / Real.sqrt (2 * (k : ℝ))) / (1 / 2)) = 4 := by
      field_simp [h_sqrt2k_ne]
      ring
    linarith
  · rw [(h_hasDeriv2 hk hh_gt).deriv, abs_mul, abs_of_pos h_sqrt2k_pos]
    have h_re_le :
        |(deriv (deriv complexGammaRatioHalf) (x : ℂ)).re| ≤
          4 * (2 / Real.sqrt (2 * (k : ℝ))) / (1 / 2) ^ 2 :=
      (Complex.abs_re_le_norm _).trans h2_bd
    have h_mul := mul_le_mul_of_nonneg_left h_re_le h_sqrt2k_pos.le
    have h_simp :
        Real.sqrt (2 * (k : ℝ)) * (4 * (2 / Real.sqrt (2 * (k : ℝ))) / (1 / 2) ^ 2) = 32 := by
      field_simp [h_sqrt2k_ne]
      ring
    linarith

/-- Smoothly cut-off rescaled inverse transmutation weight on $\mathbb{R}$, vanishing for
$h \le \frac{1}{2}\min(h_{\mathrm{gap}}, \Delta_\phi)$ and equal to
$\frac{(2k)^{3/2}}{\operatorname{transmuteWeight}(h + 2k)}$ for
$h \ge \min(h_{\mathrm{gap}}, \Delta_\phi)$ and $k \ge 1$. -/
noncomputable def cutoffInvTransmuteWeight (Δ_phi h_gap : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  if k = 0 then 0 else
    smoothCutoff (min h_gap Δ_phi) h *
      (invLinearShiftFactor k h * scaledGammaRatioHalf k h)

private lemma isUniformC2OnGtNegOne_cutoffInvTransmuteWeight
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) :
    IsUniformC2OnGtNegOne (cutoffInvTransmuteWeight Δ_phi h_gap) := by
  obtain ⟨hf1, hf2, M, hM_nn, hfb⟩ :=
    isUniformC2OnGtNegOne_mul
      (isUniformC2OnGtNegOne_smoothCutoff (lt_min hh_gap hΔ))
      (isUniformC2OnGtNegOne_mul
        isUniformC2OnGtNegOne_invLinearShiftFactor
        isUniformC2OnGtNegOne_scaledGammaRatioHalf)
  have h_eq : ∀ {k : ℕ}, 1 ≤ k →
      cutoffInvTransmuteWeight Δ_phi h_gap k =
        fun h => smoothCutoff (min h_gap Δ_phi) h *
          (invLinearShiftFactor k h * scaledGammaRatioHalf k h) := by
    intro k hk
    have hk0 : k ≠ 0 := by omega
    ext h
    simp [cutoffInvTransmuteWeight, hk0]
  refine ⟨fun {k} hk {h} hh => ?_, fun {k} hk {h} hh => ?_, M, hM_nn, fun {k} hk {h} hh => ?_⟩
  · rw [h_eq hk]; exact hf1 hk hh
  · rw [h_eq hk]; exact hf2 hk hh
  · rw [h_eq hk]; exact hfb hk hh

theorem cutoffInvTransmuteWeight_eq_zero_of_lt_half_min
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (k : ℕ) {h : ℝ} (hh : h < min h_gap Δ_phi / 2) :
    cutoffInvTransmuteWeight Δ_phi h_gap k h = 0 := by
  have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  dsimp [cutoffInvTransmuteWeight]
  split_ifs
  · rfl
  · rw [smoothCutoff_eq_zero_of_le_half hB₀_pos hh.le, zero_mul]

theorem cutoffInvTransmuteWeight_eq_of_ge_min
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : min h_gap Δ_phi ≤ h) :
    cutoffInvTransmuteWeight Δ_phi h_gap k h =
      (2 * (k : ℝ)) ^ (3 / 2 : ℝ) / transmuteWeight (h + (2 * k : ℕ)) := by
  have hk0 : k ≠ 0 := by omega
  have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  have hh0 : 0 ≤ h := le_trans hB₀_pos.le hh
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have h_rpow : (2 * (k : ℝ)) ^ (3 / 2 : ℝ) = (2 * (k : ℝ)) * Real.sqrt (2 * (k : ℝ)) := by
    have h32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by ring
    rw [h32, Real.rpow_add h2k_pos, Real.rpow_one, Real.sqrt_eq_rpow]
  have h_cast : h + ((2 * k : ℕ) : ℝ) = h + 2 * (k : ℝ) := by push_cast; ring
  simp only [cutoffInvTransmuteWeight, hk0, ↓reduceIte,
    smoothCutoff_eq_one_of_ge hB₀_pos hh, one_mul,
    invLinearShiftFactor, scaledGammaRatioHalf, realGammaRatioHalf_eq,
    transmuteWeight, h_cast, h_rpow]
  have hD_ne : h + 2 * (k : ℝ) - 1 / 2 ≠ 0 := by linarith
  have hG1_ne : Real.Gamma (h + 2 * (k : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2_ne : Real.Gamma (h + 2 * (k : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

theorem differentiable_cutoffInvTransmuteWeight
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (k : ℕ) :
    Differentiable ℝ (cutoffInvTransmuteWeight Δ_phi h_gap k) := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have h_eq : cutoffInvTransmuteWeight Δ_phi h_gap 0 = fun _ => (0 : ℝ) := by
      ext u; simp [cutoffInvTransmuteWeight]
    rw [h_eq]; exact differentiableAt_const 0
  · rcases lt_or_ge 0 h with hh_gt | hh_le
    · obtain ⟨hW1, _, _⟩ := isUniformC2OnGtNegOne_cutoffInvTransmuteWeight hΔ hh_gap
      exact hW1 hk_pos (by linarith)
    · have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
      have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := by rw [mem_Iio]; linarith
      have h_ev : cutoffInvTransmuteWeight Δ_phi h_gap k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt)
          (fun _ hu => cutoffInvTransmuteWeight_eq_zero_of_lt_half_min hΔ hh_gap k hu)
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev

theorem differentiable_deriv_cutoffInvTransmuteWeight
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (k : ℕ) :
    Differentiable ℝ (deriv (cutoffInvTransmuteWeight Δ_phi h_gap k)) := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have h_eq : cutoffInvTransmuteWeight Δ_phi h_gap 0 = fun _ => (0 : ℝ) := by
      ext u; simp [cutoffInvTransmuteWeight]
    rw [h_eq, deriv_const']; exact differentiableAt_const 0
  · rcases lt_or_ge 0 h with hh_gt | hh_le
    · obtain ⟨_, hW2, _⟩ := isUniformC2OnGtNegOne_cutoffInvTransmuteWeight hΔ hh_gap
      exact hW2 hk_pos (by linarith)
    · have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
      have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := by rw [mem_Iio]; linarith
      have h_ev : deriv (cutoffInvTransmuteWeight Δ_phi h_gap k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
        have h_ev_u : cutoffInvTransmuteWeight Δ_phi h_gap k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu)
            (fun _ hv => cutoffInvTransmuteWeight_eq_zero_of_lt_half_min hΔ hh_gap k hv)
        rw [h_ev_u.deriv_eq, deriv_const]
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev

theorem exists_c2_bound_cutoffInvTransmuteWeight
    {Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {k : ℕ}, 1 ≤ k → ∀ h : ℝ,
        |cutoffInvTransmuteWeight Δ_phi h_gap k h| ≤ B ∧
        |deriv (cutoffInvTransmuteWeight Δ_phi h_gap k) h| ≤ B ∧
        |deriv (deriv (cutoffInvTransmuteWeight Δ_phi h_gap k)) h| ≤ B := by
  have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  obtain ⟨_, _, B, hB_nonneg, hB⟩ := isUniformC2OnGtNegOne_cutoffInvTransmuteWeight hΔ hh_gap
  refine ⟨B, hB_nonneg, fun {k} hk h => ?_⟩
  rcases le_or_gt h 0 with hh_nonpos | hh_pos
  · have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := lt_of_le_of_lt hh_nonpos (by positivity)
    have h_ev1 : cutoffInvTransmuteWeight Δ_phi h_gap k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt)
        (fun _ hu => cutoffInvTransmuteWeight_eq_zero_of_lt_half_min hΔ hh_gap k hu)
    have h_ev2 : deriv (cutoffInvTransmuteWeight Δ_phi h_gap k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
      have h_ev_u : cutoffInvTransmuteWeight Δ_phi h_gap k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu)
          (fun _ hv => cutoffInvTransmuteWeight_eq_zero_of_lt_half_min hΔ hh_gap k hv)
      rw [h_ev_u.deriv_eq, deriv_const]
    rw [cutoffInvTransmuteWeight_eq_zero_of_lt_half_min hΔ hh_gap k hh_lt,
      h_ev1.deriv_eq, h_ev2.deriv_eq, deriv_const, abs_zero]
    exact ⟨hB_nonneg, hB_nonneg, hB_nonneg⟩
  · exact hB hk hh_pos.le

/-- Exact (un-cutoff) transmuted collinear transfer ratio for positive twists $h > 0$:
$$
\mathcal{R}^{\mathrm{trans}}_{m, s}(\nu, \Delta_\phi, k, h) :=
  \mathcal{R}_{m, s}(\nu, k, h) \, W_{m, s}(k, h).
$$ -/
noncomputable def collinearTransferRatio (ν Δ_phi : ℝ) (m s k : ℕ) (h : ℝ) : ℝ :=
  if k = 0 then 0 else normalizedCollinearBlockCoeff ν m s k h * kinematicMultiplier Δ_phi m s k h

/-- Smoothly cut-off collinear transfer function $\mathcal{K}_{m, s}(k, h)$ on $\mathbb{R}$,
vanishing below $\frac{1}{2}\min(h_{\mathrm{gap}}, \Delta_\phi)$ and coinciding with
`collinearTransferRatio ν Δ_phi m s k h` on $[\min(h_{\mathrm{gap}}, \Delta_\phi), \infty)$. -/
noncomputable def collinearTransferFn (ν Δ_phi h_gap : ℝ) (m s k : ℕ) (h : ℝ) : ℝ :=
  if k = 0 then 0 else
    normalizedCollinearBlockCoeff ν m s k h * cutoffKinematicMultiplier Δ_phi h_gap m s k h

/-- On $[\min(h_{\mathrm{gap}}, \Delta_\phi), \infty)$, `collinearTransferFn` coincides with the
exact un-cutoff `collinearTransferRatio`. -/
theorem collinearTransferFn_eq_collinearTransferRatio_of_ge_min
    {ν Δ_phi h_gap : ℝ} (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {h : ℝ} (hh : min h_gap Δ_phi ≤ h) :
    collinearTransferFn ν Δ_phi h_gap m s k h = collinearTransferRatio ν Δ_phi m s k h := by
  have h_min_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  dsimp [collinearTransferFn, collinearTransferRatio, cutoffKinematicMultiplier]
  split_ifs
  · rfl
  · rw [smoothCutoff_eq_one_of_ge h_min_pos hh, one_mul]

/-- Explicit transmuted-weight formula for `collinearTransferFn` on
$[\min(h_{\mathrm{gap}}, \Delta_\phi), \infty)$ for $k \ge 1$. -/
theorem collinearTransferFn_eq_of_ge_min {ν Δ_phi h_gap : ℝ}
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : min h_gap Δ_phi ≤ h) :
    collinearTransferFn ν Δ_phi h_gap m s k h =
      (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) * normalizedCollinearBlockCoeff ν m s k h *
        (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) /
          transmuteWeight (h + (2 * (k + s) : ℕ))) := by
  have hk0 : k ≠ 0 := by omega
  have h_min_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  have hh0 : 0 ≤ h := le_trans h_min_pos.le hh
  simp only [collinearTransferFn, cutoffKinematicMultiplier, kinematicMultiplier, hk0, ↓reduceIte,
    smoothCutoff_eq_one_of_ge h_min_pos hh, one_mul,
    weightShiftRatio_eq_transmuteWeight_div m s hk hh0]
  ring

theorem collinearTransferFn_eq_zero_of_lt_half_min {ν Δ_phi h_gap : ℝ}
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {h : ℝ} (hh : h < min h_gap Δ_phi / 2) :
    collinearTransferFn ν Δ_phi h_gap m s k h = 0 := by
  have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  dsimp [collinearTransferFn, cutoffKinematicMultiplier]
  split_ifs
  · rfl
  · rw [smoothCutoff_eq_zero_of_le_half hB₀_pos hh.le, zero_mul, mul_zero]

private lemma hasDerivAt_collinearTransferFn_of_pos {ν Δ_phi h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (collinearTransferFn ν Δ_phi h_gap m s k)
      (deriv (normalizedCollinearBlockCoeff ν m s k) h *
          cutoffKinematicMultiplier Δ_phi h_gap m s k h +
        normalizedCollinearBlockCoeff ν m s k h *
          deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k) h) h := by
  have hk0 : k ≠ 0 := by omega
  have h_eq : collinearTransferFn ν Δ_phi h_gap m s k =
      fun u => normalizedCollinearBlockCoeff ν m s k u *
        cutoffKinematicMultiplier Δ_phi h_gap m s k u := by
    ext u; simp [collinearTransferFn, hk0]
  rw [h_eq]
  obtain ⟨hW1, _, _⟩ := isUniformC2OnGtNegOne_cutoffKinematicMultiplier hΔ hh_gap m s
  exact (differentiableAt_normalizedCollinearBlockCoeff ν hν m s k hh).hasDerivAt.mul
    (hW1 hk (by linarith)).hasDerivAt

private lemma hasDerivAt_deriv_collinearTransferFn_of_pos {ν Δ_phi h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (deriv (collinearTransferFn ν Δ_phi h_gap m s k))
      (deriv (deriv (normalizedCollinearBlockCoeff ν m s k)) h *
          cutoffKinematicMultiplier Δ_phi h_gap m s k h +
        2 * deriv (normalizedCollinearBlockCoeff ν m s k) h *
          deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k) h +
        normalizedCollinearBlockCoeff ν m s k h *
          deriv (deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k)) h) h := by
  obtain ⟨hW1, hW2, _⟩ := isUniformC2OnGtNegOne_cutoffKinematicMultiplier hΔ hh_gap m s
  have h_ev : deriv (collinearTransferFn ν Δ_phi h_gap m s k) =ᶠ[𝓝 h]
      fun u => deriv (normalizedCollinearBlockCoeff ν m s k) u *
          cutoffKinematicMultiplier Δ_phi h_gap m s k u +
        normalizedCollinearBlockCoeff ν m s k u *
          deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k) u := by
    filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
    exact (hasDerivAt_collinearTransferFn_of_pos hν hΔ hh_gap m s hk hu).deriv
  have hd1 := (differentiableAt_deriv_normalizedCollinearBlockCoeff ν hν m s k hh).hasDerivAt.mul
    (hW1 hk (by linarith)).hasDerivAt
  have hd2 := (differentiableAt_normalizedCollinearBlockCoeff ν hν m s k hh).hasDerivAt.mul
    (hW2 hk (by linarith)).hasDerivAt
  exact ((hd1.add hd2).congr_deriv (by ring)).congr_of_eventuallyEq h_ev

theorem differentiable_collinearTransferFn {ν Δ_phi h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (m s k : ℕ) :
    Differentiable ℝ (collinearTransferFn ν Δ_phi h_gap m s k) := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have h_eq : collinearTransferFn ν Δ_phi h_gap m s 0 = fun _ => (0 : ℝ) := by
      ext u; simp [collinearTransferFn]
    rw [h_eq]; exact differentiableAt_const 0
  · rcases lt_or_ge 0 h with hh_gt | hh_le
    · exact (hasDerivAt_collinearTransferFn_of_pos hν hΔ hh_gap m s hk_pos hh_gt).differentiableAt
    · have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
      have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := by rw [mem_Iio]; linarith
      have h_ev : collinearTransferFn ν Δ_phi h_gap m s k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt)
          (fun _ hu => collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hu)
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev

theorem differentiable_deriv_collinearTransferFn {ν Δ_phi h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (m s k : ℕ) :
    Differentiable ℝ (deriv (collinearTransferFn ν Δ_phi h_gap m s k)) := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have h_eq : collinearTransferFn ν Δ_phi h_gap m s 0 = fun _ => (0 : ℝ) := by
      ext u; simp [collinearTransferFn]
    rw [h_eq, deriv_const']; exact differentiableAt_const 0
  · rcases lt_or_ge 0 h with hh_gt | hh_le
    · exact (hasDerivAt_deriv_collinearTransferFn_of_pos hν hΔ hh_gap m s hk_pos hh_gt).differentiableAt
    · have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
      have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := by rw [mem_Iio]; linarith
      have h_ev : deriv (collinearTransferFn ν Δ_phi h_gap m s k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
        have h_ev_u : collinearTransferFn ν Δ_phi h_gap m s k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu)
            (fun _ hv => collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hv)
        rw [h_ev_u.deriv_eq, deriv_const]
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev

theorem exists_c2_bound_collinearTransferFn {ν Δ_phi h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (m s N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, |h| ≤ (N : ℝ) →
        |collinearTransferFn ν Δ_phi h_gap m s k h| ≤ B ∧
        |deriv (collinearTransferFn ν Δ_phi h_gap m s k) h| ≤ B ∧
        |deriv (deriv (collinearTransferFn ν Δ_phi h_gap m s k)) h| ≤ B := by
  have hB₀_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  obtain ⟨B_R, hB_R_nonneg, hB_R⟩ := exists_c2_bound_normalizedCollinearBlockCoeff ν hν m s N
  obtain ⟨_, _, M_W, hM_W_nonneg, hM_W⟩ :=
    isUniformC2OnGtNegOne_cutoffKinematicMultiplier hΔ hh_gap m s
  refine ⟨4 * B_R * M_W, by positivity, fun {k} hk {h} hh_abs => ?_⟩
  rcases le_or_gt h 0 with hh_nonpos | hh_pos
  · have hh_lt : h ∈ Iio (min h_gap Δ_phi / 2) := lt_of_le_of_lt hh_nonpos (by positivity)
    have h_ev1 : collinearTransferFn ν Δ_phi h_gap m s k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt)
        (fun _ hu => collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hu)
    have h_ev2 : deriv (collinearTransferFn ν Δ_phi h_gap m s k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
      have h_ev_u : collinearTransferFn ν Δ_phi h_gap m s k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu)
          (fun _ hv => collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hv)
      rw [h_ev_u.deriv_eq, deriv_const]
    rw [collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hh_lt,
      h_ev1.deriv_eq, h_ev2.deriv_eq, deriv_const, abs_zero]
    exact ⟨by positivity, by positivity, by positivity⟩
  · have hh_le_N : h ≤ (N : ℝ) := (le_abs_self h).trans hh_abs
    have hk0 : k ≠ 0 := by omega
    obtain ⟨hR0, hR1, hR2⟩ := hB_R hk hh_pos hh_le_N
    obtain ⟨hW0, hW1, hW2⟩ := hM_W hk hh_pos.le
    refine ⟨?_, ?_, ?_⟩
    · simp only [collinearTransferFn, hk0, ↓reduceIte, abs_mul]
      have h1 := mul_le_mul hR0 hW0 (abs_nonneg _) hB_R_nonneg
      linarith [mul_nonneg hB_R_nonneg hM_W_nonneg]
    · rw [(hasDerivAt_collinearTransferFn_of_pos hν hΔ hh_gap m s hk hh_pos).deriv]
      have h1 :
          |deriv (normalizedCollinearBlockCoeff ν m s k) h *
              cutoffKinematicMultiplier Δ_phi h_gap m s k h| ≤ B_R * M_W := by
        rw [abs_mul]; exact mul_le_mul hR1 hW0 (abs_nonneg _) hB_R_nonneg
      have h2 :
          |normalizedCollinearBlockCoeff ν m s k h *
              deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k) h| ≤ B_R * M_W := by
        rw [abs_mul]; exact mul_le_mul hR0 hW1 (abs_nonneg _) hB_R_nonneg
      have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
      linarith [mul_nonneg hB_R_nonneg hM_W_nonneg]
    · rw [(hasDerivAt_deriv_collinearTransferFn_of_pos hν hΔ hh_gap m s hk hh_pos).deriv]
      have h1 :
          |deriv (deriv (normalizedCollinearBlockCoeff ν m s k)) h *
              cutoffKinematicMultiplier Δ_phi h_gap m s k h| ≤ B_R * M_W := by
        rw [abs_mul]; exact mul_le_mul hR2 hW0 (abs_nonneg _) hB_R_nonneg
      have h2 :
          |2 * deriv (normalizedCollinearBlockCoeff ν m s k) h *
              deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k) h| ≤ 2 * (B_R * M_W) := by
        rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hR1 hW1 (abs_nonneg _) hB_R_nonneg) (by norm_num)
      have h3 :
          |normalizedCollinearBlockCoeff ν m s k h *
              deriv (deriv (cutoffKinematicMultiplier Δ_phi h_gap m s k)) h| ≤ B_R * M_W := by
        rw [abs_mul]; exact mul_le_mul hR0 hW2 (abs_nonneg _) hB_R_nonneg
      have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
      have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
      linarith

/-! ## Section 2: $C^2$ and Support Bounds for Shifted Collinear Test Functions -/

section ShiftedTestFunction

variable {ν Δ_phi h_gap : ℝ}

/-- The shifted test function at twist level $m$ and spin shift $s$:
$$\psi_{m, s, k}(h) := \operatorname{collinearTransferFn}(\nu, \Delta_\phi, h_{\mathrm{gap}}, m, s, k, h) \, \varphi(h + m).$$ -/
noncomputable def collinearShiftTestFn
    (ν Δ_phi h_gap : ℝ) (m s k : ℕ) (φ : ℝ → ℝ) (h : ℝ) : ℝ :=
  collinearTransferFn ν Δ_phi h_gap m s k h * φ (h + (m : ℝ))

lemma deriv_and_deriv2_eq_zero_of_eqOn_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h_zero : ∀ u ∈ U, f u = 0) {h : ℝ} (hh : h ∈ U) :
    f h = 0 ∧ deriv f h = 0 ∧ deriv (deriv f) h = 0 := by
  have h_ev1 : f =ᶠ[𝓝 h] (fun _ => (0 : ℝ)) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hh) h_zero
  have hd1 : deriv f h = 0 := by rw [h_ev1.deriv_eq, deriv_const]
  have h_ev2 : deriv f =ᶠ[𝓝 h] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hh] with u hu
    have h_ev_u : f =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hu) h_zero
    rw [h_ev_u.deriv_eq, deriv_const]
  have hd2 : deriv (deriv f) h = 0 := by rw [h_ev2.deriv_eq, deriv_const]
  exact ⟨h_zero h hh, hd1, hd2⟩

private lemma hasDerivAt_comp_add_nat {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (m : ℕ) (h : ℝ) :
    HasDerivAt (fun u : ℝ => φ (u + (m : ℝ))) (deriv φ (h + (m : ℝ))) h := by
  have hd1 : HasDerivAt φ (deriv φ (h + (m : ℝ))) (h + (m : ℝ)) :=
    (hφ (h + (m : ℝ))).hasDerivAt
  have hd2 : HasDerivAt (fun u : ℝ => u + (m : ℝ)) 1 h := by
    simpa using (hasDerivAt_id h).add_const (m : ℝ)
  exact (HasDerivAt.comp (h₂ := φ) (h := fun u : ℝ => u + (m : ℝ)) h hd1 hd2).congr_deriv
    (mul_one _)

private lemma differentiable_comp_add_nat {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (m : ℕ) :
    Differentiable ℝ (fun u : ℝ => φ (u + (m : ℝ))) :=
  fun h => (hasDerivAt_comp_add_nat hφ m h).differentiableAt

private lemma deriv_comp_add_nat {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (m : ℕ) :
    deriv (fun u : ℝ => φ (u + (m : ℝ))) = fun h : ℝ => deriv φ (h + (m : ℝ)) := by
  ext h
  exact (hasDerivAt_comp_add_nat hφ m h).deriv

/-- First-order differentiability of `collinearShiftTestFn ν Δ_phi h_gap m s k φ`. -/
theorem differentiable_collinearShiftTestFn
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (collinearShiftTestFn ν Δ_phi h_gap m s k φ) :=
  (differentiable_collinearTransferFn hν hΔ hh_gap m s k).mul (differentiable_comp_add_nat hφ m)

/-- Explicit formula for the first derivative of `collinearShiftTestFn ν Δ_phi h_gap m s k φ`. -/
theorem deriv_collinearShiftTestFn
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (h : ℝ) :
    deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ) h =
      deriv (collinearTransferFn ν Δ_phi h_gap m s k) h * φ (h + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k h * deriv φ (h + (m : ℝ)) := by
  have hdK := (differentiable_collinearTransferFn hν hΔ hh_gap m s k h).hasDerivAt
  have hdφ := hasDerivAt_comp_add_nat hφ m h
  exact (hdK.mul hdφ).deriv

/-- Second-order differentiability of `collinearShiftTestFn ν Δ_phi h_gap m s k φ`. -/
theorem differentiable_deriv_collinearShiftTestFn
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Differentiable ℝ (deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) := by
  have h_eq : deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ) =
      fun h : ℝ => deriv (collinearTransferFn ν Δ_phi h_gap m s k) h * φ (h + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k h * deriv φ (h + (m : ℝ)) := by
    ext h; exact deriv_collinearShiftTestFn hν hΔ hh_gap m s k hφ h
  rw [h_eq]
  exact ((differentiable_deriv_collinearTransferFn hν hΔ hh_gap m s k).mul
    (differentiable_comp_add_nat hφ m)).add
    ((differentiable_collinearTransferFn hν hΔ hh_gap m s k).mul
      (differentiable_comp_add_nat hφ' m))

/-- Explicit formula for the second derivative of `collinearShiftTestFn ν Δ_phi h_gap m s k φ`. -/
theorem deriv_deriv_collinearShiftTestFn
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (h : ℝ) :
    deriv (deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) h =
      deriv (deriv (collinearTransferFn ν Δ_phi h_gap m s k)) h * φ (h + (m : ℝ)) +
        2 * deriv (collinearTransferFn ν Δ_phi h_gap m s k) h * deriv φ (h + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k h * deriv (deriv φ) (h + (m : ℝ)) := by
  have h_eq : deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ) =
      fun u : ℝ => deriv (collinearTransferFn ν Δ_phi h_gap m s k) u * φ (u + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k u * deriv φ (u + (m : ℝ)) := by
    ext u; exact deriv_collinearShiftTestFn hν hΔ hh_gap m s k hφ u
  rw [h_eq]
  have hdK1 := (differentiable_collinearTransferFn hν hΔ hh_gap m s k h).hasDerivAt
  have hdK2 := (differentiable_deriv_collinearTransferFn hν hΔ hh_gap m s k h).hasDerivAt
  have hdφ1 := hasDerivAt_comp_add_nat hφ m h
  have hdφ2 := hasDerivAt_comp_add_nat hφ' m h
  have hd_sum : HasDerivAt
      (fun u : ℝ => deriv (collinearTransferFn ν Δ_phi h_gap m s k) u * φ (u + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k u * deriv φ (u + (m : ℝ)))
      (deriv (deriv (collinearTransferFn ν Δ_phi h_gap m s k)) h * φ (h + (m : ℝ)) +
        2 * deriv (collinearTransferFn ν Δ_phi h_gap m s k) h * deriv φ (h + (m : ℝ)) +
        collinearTransferFn ν Δ_phi h_gap m s k h * deriv (deriv φ) (h + (m : ℝ))) h :=
    ((hdK2.mul hdφ1).add (hdK1.mul hdφ2)).congr_deriv (by ring)
  exact hd_sum.deriv

/-- **Preservation of Support Radius $[-N, N]$**:
When $h_{\mathrm{gap}}, \Delta_\phi > 0$ and $m \ge 1$, if $\varphi$ vanishes outside $[-N, N]$,
then `collinearShiftTestFn ν Δ_phi h_gap m s k φ` also vanishes outside $[-N, N]$ (with the
**same** $N$). -/
theorem collinearShiftTestFn_eq_zero_of_abs_gt
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    {m : ℕ} (hm : 1 ≤ m) (s k N : ℕ) {φ : ℝ → ℝ}
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0)
    {h : ℝ} (hh : (N : ℝ) < |h|) :
    collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0 := by
  dsimp [collinearShiftTestFn]
  rcases lt_or_ge h 0 with h_neg | h_nonneg
  · have h_lt_min : h < min h_gap Δ_phi / 2 :=
      lt_of_lt_of_le h_neg (div_nonneg (le_min hh_gap.le hΔ.le) (by norm_num))
    rw [collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k h_lt_min, zero_mul]
  · rw [abs_of_nonneg h_nonneg] at hh
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have h_gt : (N : ℝ) < |h + (m : ℝ)| := by
      rw [abs_of_pos (by linarith)]
      linarith
    rw [hsupp (h + (m : ℝ)) h_gt, mul_zero]

/-- **Downward Shift of Upper Twist Window**:
When $m \ge 1$, if $\varphi(u) = 0$ for all $u \ge B + 1$, then
`collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0` for all $h \ge B$. -/
theorem collinearShiftTestFn_eq_zero_of_ge
    {m : ℕ} (hm : 1 ≤ m) (s k : ℕ) {B : ℝ} {φ : ℝ → ℝ}
    (hφ_hi : ∀ u : ℝ, B + 1 ≤ u → φ u = 0)
    {h : ℝ} (hh : B ≤ h) :
    collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0 := by
  dsimp [collinearShiftTestFn]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hφ_hi (h + (m : ℝ)) (by linarith), mul_zero]

end ShiftedTestFunction
