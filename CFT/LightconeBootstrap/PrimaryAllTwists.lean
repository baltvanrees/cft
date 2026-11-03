/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.TransmutedCrossing

/-!
# Quantitative Large-Spin Bootstrap for $d$-Dimensional Primary Operators at All Bounded Twists

This file upgrades the leading-twist ($h < h_{\mathrm{gap}} + 1$) $d$-dimensional primary bootstrap
theorems of `CFT/LightconeBootstrap/TransmutedCrossing.lean` to **arbitrary bounded twist windows
$h \in [-N, N]$** ($N \in \mathbb{N}$) via finite triangular inversion of the collinear conformal
block expansion, preserving the full finite-spin error exponent
$$0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$$
with zero $O(k^{-1})$ loss.

## Mathematical Overview

1. **Normalized Subleading Collinear Block Coefficients (`NormalizedCollinearBlockCoeffs`)
   and Canonical Transfer Kernel (`CollinearTransferKernel`, `toCollinearTransferKernel`)**:
   In $d = 2\nu + 2$ dimensions, a conformal block $G_{\Delta, \ell}(e^{w_l}, e^{w_r})$ of primary
   left twist $h = (\Delta - \ell)/2$ and even spin $\ell = 2k'$ decomposes at left-moving twist
   level $m \ge 0$ into a finite linear combination of 1D collinear blocks:
   $$g_m(w_r) = \sum_{s=0}^{m} B_{m, m - 2s}(h, 2k') \, k_{h + 2k' + (m - 2s)}(e^{w_r}).$$
   At effective 1D spin $2k = \bar{h} - (h + m) = 2k' - 2s$, a primary of spin $2k' = 2(k + s)$
   ($s \in \{0, 1, \dots, m\}$, so $k' = k + s \ge k$) and primary twist $h$ contributes at
   left-moving twist $h' = h + m$ with 1D right-moving weight $\bar{h} = h + m + 2k$.
   We package the purely block-theoretic normalized subleading coefficients
   $$\mathcal{R}_{m, s}(k, h) := \chi(h) \frac{B_{m, m - 2s}(h, 2(k + s))}{C_{0, 2(k + s)}}$$
   into `NormalizedCollinearBlockCoeffs ν Δ_phi h_gap`, and prove with zero `sorry`s
   (`NormalizedCollinearBlockCoeffs.toCollinearTransferKernel`) that multiplying by the explicit
   kinematic prefactor
   $$\left(\frac{k + s}{k}\right)^{2\Delta_\phi}
     \frac{\operatorname{transmuteWeight}(h + m + 2k)}{
       \operatorname{transmuteWeight}(h + 2(k + s))}$$
   automatically produces a `CollinearTransferKernel ν Δ_phi h_gap`.

2. **Triangular Decomposition of `LightconeBlockFourPointData` (`HasCollinearTriangularDecomp`)**:
   For any test function $\varphi$ vanishing on
   $[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
   only left-moving twist levels $0 \le m \le M$ can contribute to the 1D lightcone-block pairing:
   $$\mathcal{L}_k(\varphi) = \mathcal{P}_k(\varphi) +
     \sum_{m=1}^{M} \sum_{s=0}^{m}
       \mathcal{P}_{k + s}\bigl(h \mapsto \mathcal{K}_{m, s}(k, h) \, \varphi(h + m)\bigr).$$

3. **Canonical Finite-Spin GFF Primary Coefficients & Pairing
   (`gffPrimaryCoeff`, `gffPrimaryPairing`)**:
   By triangular recursion over the double-twist level $n \in \mathbb{N}$, we define the universal
   GFF primary coefficients $c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k)$ (`gffPrimaryCoeff`) and the
   canonical GFF primary pairing
   $$\operatorname{gffPrimaryPairing}(T, k, \varphi) :=
     \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k) \, \varphi(\Delta_\phi + n),$$
   and prove the exact triangular unfolding identity
   `gffPrimaryPairing_eq_exactIdentity_sub_sum`.

4. **Unconditional All-Twist $d$-Dimensional Primary Bootstrap
   (`exists_const_abs_primary_allTwists_sub_gffPrimary_le`)**:
   By finite induction on the twist level $M \in \mathbb{N}$ (using the fact that $k + s \ge k$
   implies $(2(k + s))^{-\gamma} \le (2k)^{-\gamma}$ for all $\gamma > 0$), we prove with zero
   `sorry`s that for **every** $N \in \mathbb{N}$, **every**
   $0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, and **every**
   $\varphi \in C_c^2([-N, N])$ (with no restriction to $h < h_{\mathrm{gap}} + 1$),
   $$\Biggl|(2k)^{-2\Delta_\phi} C_{0, 2k}
     \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
       d\mu^{\mathrm{prim}}_{2k}(h)
     - \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k) \,
       \varphi(\Delta_\phi + n)\Biggr|
     \le C_N \, (2k)^{-\gamma} \, M_\varphi.$$
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Normalized Pairings & Collinear Block Transfer Kernel -/

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- Normalized spin-$2k$ 1D lightcone-block transmuted pairing:
$$\mathcal{L}_k(\varphi) := (2k)^{-2\Delta_\phi}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
  d\mu^{\mathrm{LC}}_{2k}(h).$$ -/
noncomputable def normLCPairing (Δ_phi : ℝ) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
    ∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h ∂(L.muLC (2 * (k : ℤ)))

/-- Normalized spin-$2k$ $d$-dimensional primary operator transmuted pairing:
$$\mathcal{P}_k(\varphi) := (2k)^{-2\Delta_\phi} C_{0, 2k}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
  d\mu^{\mathrm{prim}}_{2k}(h).$$ -/
noncomputable def normPrimaryPairing (Δ_phi : ℝ) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
    ∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))

/-- On the leading-twist window $(-\infty, h_{\mathrm{gap}} + 1)$, `normLCPairing` coincides with
`normPrimaryPairing` for all $k \ge 1$. -/
theorem normLCPairing_eq_normPrimaryPairing_of_support_leadingTwist
    (Δ_phi : ℝ) {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ_supp : ∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) :
    L.normLCPairing Δ_phi k φ = L.normPrimaryPairing Δ_phi k φ := by
  have h2k_nat : 1 ≤ 2 * k := by omega
  have h2k_int : (1 : ℤ) ≤ 2 * (k : ℤ) := by omega
  have h1 := L.pairSpin_toTransmutedMonomialFourPointData h2k_int φ
  have h2 := L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist h2k_nat hφ_supp
  have h_cast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast, h1] at h2
  dsimp [normLCPairing, normPrimaryPairing]
  rw [h2, mul_assoc]

/-- Direct extraction of the unweighted primary integral
$\int_{\mathbb{R}} \varphi(h) \, d\mu^{\mathrm{prim}}_{2k}(h)$
by dividing the test function by $\operatorname{transmuteWeight}(h + 2k)$. -/
theorem normPrimaryPairing_div_transmuteWeight
    (Δ_phi : ℝ) {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ_lo : ∀ h : ℝ, h < 0 → φ h = 0) :
    (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
        (∫ h : ℝ, φ h ∂(L.muPrim (2 * k))) =
      L.normPrimaryPairing Δ_phi k (fun h => φ h / transmuteWeight (h + (2 * k : ℕ))) := by
  dsimp [normPrimaryPairing]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp
  by_cases hh : h < 0
  · rw [hφ_lo h hh, zero_div, mul_zero]
  · have hh0 : 0 ≤ h := not_lt.mp hh
    have h2k : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * k)
    have h_gt : 1 / 2 < h + (2 * k : ℕ) := by linarith
    exact (mul_div_cancel₀ (φ h) (transmuteWeight_pos h_gt).ne').symm

end LightconeBlockFourPointData

/-- Elementary rational shift factor
$$f_{c, d, k}(h) := 1 + \frac{c}{h + 2k + d}$$
appearing in the Gamma-function shift ratio for `transmuteWeight`. -/
noncomputable def elementaryShiftFactor (c d : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  1 + c / (h + 2 * (k : ℝ) + d)

/-- Explicit rational formula for the transmutation weight ratio
$$\frac{\operatorname{transmuteWeight}(h + m + 2k)}{\operatorname{transmuteWeight}(h + 2(k + s))}
  = \frac{h + 2k + m - 1/2}{h + 2k + 2s - 1/2}
    \left(\prod_{i=0}^{m-1} \frac{h + 2k + i + 1/2}{h + 2k + i}\right)
    \left(\prod_{j=0}^{2s-1} \frac{h + 2k + j}{h + 2k + j + 1/2}\right).$$
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
$$\frac{\operatorname{transmuteWeight}(h + m + 2k)}{
  \operatorname{transmuteWeight}(h + 2(k + s))}.$$ -/
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

/-- **Normalized Subleading Collinear Conformal Block Coefficients
(`NormalizedCollinearBlockCoeffs`)**:
Packages the purely block-theoretic normalized subleading collinear conformal block coefficients
$$\mathcal{R}_{m, s}(k, h) := \chi(h) \frac{B_{m, m - 2s}(h, 2(k + s))}{C_{0, 2(k + s)}}$$
at left-moving twist level $m \ge 1$ and spin shift $0 \le s \le m$, without the external scaling
factor $\bigl(\frac{k + s}{k}\bigr)^{2\Delta_\phi}$ or the transmutation weight ratio
$\frac{\operatorname{transmuteWeight}(h + m + 2k)}{\operatorname{transmuteWeight}(h + 2(k + s))}$.
We prove below (`NormalizedCollinearBlockCoeffs.toCollinearTransferKernel`) with zero `sorry`s that
multiplying $\mathcal{R}_{m, s}(k, h)$ by the explicit kinematic prefactor automatically produces a
full `CollinearTransferKernel ν Δ_phi h_gap`. -/
structure NormalizedCollinearBlockCoeffs (ν Δ_phi h_gap : ℝ) where
  /-- Normalized subleading collinear block coefficient
  $\mathcal{R}_{m, s}(k, h) = \chi(h) \frac{B_{m, m - 2s}(h, 2(k + s))}{C_{0, 2(k + s)}}$. -/
  R : ℕ → ℕ → ℕ → ℝ → ℝ
  /-- First-order smoothness of $h \mapsto \mathcal{R}_{m, s}(k, h)$ on $\mathbb{R}$. -/
  differentiable_R : ∀ m s k : ℕ, Differentiable ℝ (R m s k)
  /-- Second-order smoothness of $h \mapsto \mathcal{R}_{m, s}(k, h)$ on $\mathbb{R}$. -/
  differentiable_deriv_R : ∀ m s k : ℕ, Differentiable ℝ (deriv (R m s k))
  /-- Cutoff below the unitarity/GFF twist threshold $\min(h_{\mathrm{gap}}, \Delta_\phi)$. -/
  R_eq_zero_of_lt_min : ∀ m s k : ℕ, ∀ {h : ℝ}, h < min h_gap Δ_phi → R m s k h = 0
  /-- Uniform $C^2$ bound on compact twist intervals $|h| \le N$ across all spins $k \ge 1$. -/
  exists_c2_bound : ∀ (m s N : ℕ), ∃ B : ℝ, 0 ≤ B ∧
    ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, |h| ≤ (N : ℝ) →
      |R m s k h| ≤ B ∧
      |deriv (R m s k) h| ≤ B ∧
      |deriv (deriv (R m s k)) h| ≤ B

/-- **Normalized Collinear Block Transfer Kernel (`CollinearTransferKernel`)**:
Packages the full collinear block transfer functions
$$\mathcal{K}_{m, s}(k, h) := \left(\frac{k + s}{k}\right)^{2\Delta_\phi}
  \mathcal{R}_{m, s}(k, h)
  \frac{\operatorname{transmuteWeight}(h + m + 2k)}{\operatorname{transmuteWeight}(h + 2(k + s))}$$
at left-moving twist level $m \ge 1$ and spin shift $0 \le s \le m$ (corresponding to collinear
spin shift $j = m - 2s \in \{-m, -m+2, \dots, m\}$, so that a primary of twist $h$ and spin
$\ell = 2(k + s)$ produces the 1D collinear block $e^{(h + m) w_l} k_{(h + m) + 2k}(e^{w_r})$ of
effective 1D spin $2k$). -/
structure CollinearTransferKernel (ν Δ_phi h_gap : ℝ) where
  /-- Normalized collinear transfer coefficient $\mathcal{K}_{m, s}(k, h)$ for twist level
  $m \in \mathbb{N}$, spin shift $s \in \mathbb{N}$, spin index $k \in \mathbb{N}$, and primary
  left twist $h \in \mathbb{R}$. -/
  K : ℕ → ℕ → ℕ → ℝ → ℝ
  /-- First-order smoothness of $h \mapsto \mathcal{K}_{m, s}(k, h)$ on $\mathbb{R}$. -/
  differentiable_K : ∀ m s k : ℕ, Differentiable ℝ (K m s k)
  /-- Second-order smoothness of $h \mapsto \mathcal{K}_{m, s}(k, h)$ on $\mathbb{R}$. -/
  differentiable_deriv_K : ∀ m s k : ℕ, Differentiable ℝ (deriv (K m s k))
  /-- Cutoff below the unitarity/GFF twist threshold $\min(h_{\mathrm{gap}}, \Delta_\phi)$. -/
  K_eq_zero_of_lt_min : ∀ m s k : ℕ, ∀ {h : ℝ}, h < min h_gap Δ_phi → K m s k h = 0
  /-- Uniform $C^2$ bound on compact twist intervals $|h| \le N$ across all spins $k \ge 1$. -/
  exists_c2_bound : ∀ (m s N : ℕ), ∃ B : ℝ, 0 ≤ B ∧
    ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, |h| ≤ (N : ℝ) →
      |K m s k h| ≤ B ∧
      |deriv (K m s k) h| ≤ B ∧
      |deriv (deriv (K m s k)) h| ≤ B

namespace NormalizedCollinearBlockCoeffs

variable {ν Δ_phi h_gap : ℝ} (C : NormalizedCollinearBlockCoeffs ν Δ_phi h_gap)

/-- The full kinematic multiplier
$$W_{m, s}(k, h) :=
  \left(\frac{k + s}{k}\right)^{2\Delta_\phi} \operatorname{weightShiftRatio}(m, s, k, h)$$
that converts the normalized block coefficient $\mathcal{R}_{m, s}(k, h)$ into the transmuted
collinear transfer kernel $\mathcal{K}_{m, s}(k, h)$. -/
noncomputable def kinematicMultiplier (Δ_phi : ℝ) (m s k : ℕ) (h : ℝ) : ℝ :=
  (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) * weightShiftRatio m s k h

private lemma isUniformC2OnGtNegOne_kinematicMultiplier (hΔ : 0 < Δ_phi) (m s : ℕ) :
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

/-- Explicit formula for the collinear transfer kernel $\mathcal{K}_{m, s}(k, h)$ constructed from
`C : NormalizedCollinearBlockCoeffs ν Δ_phi h_gap`:
$$\mathcal{K}_{m, s}(k, h) =
  \begin{cases}
    0, & k = 0, \\
    \left(\frac{k + s}{k}\right)^{2\Delta_\phi} \mathcal{R}_{m, s}(k, h) \,
      \operatorname{weightShiftRatio}(m, s, k, h), & k \ge 1.
  \end{cases}$$ -/
noncomputable def transferFn (m s k : ℕ) (h : ℝ) : ℝ :=
  if k = 0 then 0 else C.R m s k h * kinematicMultiplier Δ_phi m s k h

/-- For all $k \ge 1$ and $h \ge 0$, `C.transferFn m s k h` equals the exact transmuted block ratio
$$\left(\frac{k + s}{k}\right)^{2\Delta_\phi} \mathcal{R}_{m, s}(k, h)
  \frac{\operatorname{transmuteWeight}(h + m + 2k)}{
    \operatorname{transmuteWeight}(h + 2(k + s))}.$$ -/
theorem transferFn_eq_of_nonneg (m s : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hh : 0 ≤ h) :
    C.transferFn m s k h =
      (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) * C.R m s k h *
        (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) /
          transmuteWeight (h + (2 * (k + s) : ℕ))) := by
  have hk0 : k ≠ 0 := by omega
  simp only [transferFn, kinematicMultiplier, hk0, ↓reduceIte,
    weightShiftRatio_eq_transmuteWeight_div m s hk hh]
  ring

/-- **Canonical Construction of `CollinearTransferKernel` from `NormalizedCollinearBlockCoeffs`
(`toCollinearTransferKernel`)**:
When $h_{\mathrm{gap}} > 0$ and $\Delta_\phi > 0$, multiplying the normalized subleading block
coefficients $\mathcal{R}_{m, s}(k, h)$ by the explicit kinematic prefactor
$\bigl(\frac{k + s}{k}\bigr)^{2\Delta_\phi}
  \frac{\operatorname{transmuteWeight}(h + m + 2k)}{\operatorname{transmuteWeight}(h + 2(k + s))}$
automatically satisfies all global $C^2$ smoothness, cutoff, and spin-uniform $C^2$ bound axioms of
`CollinearTransferKernel ν Δ_phi h_gap`. -/
noncomputable def toCollinearTransferKernel
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) :
    CollinearTransferKernel ν Δ_phi h_gap := by
  have h_min_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  have h_low_zero : ∀ m s k : ℕ, ∀ u ∈ Iio (min h_gap Δ_phi), C.transferFn m s k u = 0 := by
    intro m s k u hu
    dsimp [transferFn]
    split_ifs
    · rfl
    · rw [C.R_eq_zero_of_lt_min m s k hu, zero_mul]
  have h_hasDeriv1_gt : ∀ m s : ℕ, ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (C.transferFn m s k)
        (deriv (C.R m s k) h * kinematicMultiplier Δ_phi m s k h +
          C.R m s k h * deriv (kinematicMultiplier Δ_phi m s k) h) h := by
    intro m s k hk h hh
    have hk0 : k ≠ 0 := by omega
    have h_eq : C.transferFn m s k = fun u => C.R m s k u * kinematicMultiplier Δ_phi m s k u := by
      ext u; simp [transferFn, hk0]
    rw [h_eq]
    obtain ⟨hW1, _, _⟩ := isUniformC2OnGtNegOne_kinematicMultiplier hΔ m s
    exact (C.differentiable_R m s k h).hasDerivAt.mul (hW1 hk hh).hasDerivAt
  have h_hasDeriv2_gt : ∀ m s : ℕ, ∀ {k : ℕ}, 1 ≤ k → ∀ {h : ℝ}, -1 < h →
      HasDerivAt (deriv (C.transferFn m s k))
        (deriv (deriv (C.R m s k)) h * kinematicMultiplier Δ_phi m s k h +
          2 * deriv (C.R m s k) h * deriv (kinematicMultiplier Δ_phi m s k) h +
          C.R m s k h * deriv (deriv (kinematicMultiplier Δ_phi m s k)) h) h := by
    intro m s k hk h hh
    obtain ⟨hW1, hW2, _⟩ := isUniformC2OnGtNegOne_kinematicMultiplier hΔ m s
    have h_ev : deriv (C.transferFn m s k) =ᶠ[𝓝 h]
        fun u => deriv (C.R m s k) u * kinematicMultiplier Δ_phi m s k u +
          C.R m s k u * deriv (kinematicMultiplier Δ_phi m s k) u := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with u hu
      exact (h_hasDeriv1_gt m s hk hu).deriv
    have hd1 := (C.differentiable_deriv_R m s k h).hasDerivAt.mul (hW1 hk hh).hasDerivAt
    have hd2 := (C.differentiable_R m s k h).hasDerivAt.mul (hW2 hk hh).hasDerivAt
    exact ((hd1.add hd2).congr_deriv (by ring)).congr_of_eventuallyEq h_ev
  refine
    { K := C.transferFn
      differentiable_K := fun m s k h => ?_
      differentiable_deriv_K := fun m s k h => ?_
      K_eq_zero_of_lt_min := fun m s k {h} hh => h_low_zero m s k h hh
      exists_c2_bound := fun m s N => ?_ }
  · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · have h_eq : C.transferFn m s 0 = fun _ => (0 : ℝ) := by ext u; simp [transferFn]
      rw [h_eq]; exact differentiableAt_const 0
    · rcases lt_or_ge (-1 : ℝ) h with hh_gt | hh_le
      · exact (h_hasDeriv1_gt m s hk_pos hh_gt).differentiableAt
      · have hh_lt : h ∈ Iio (min h_gap Δ_phi) := by
          rw [mem_Iio]; linarith
        have h_ev : C.transferFn m s k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt) (h_low_zero m s k)
        exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev
  · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · have h_eq : C.transferFn m s 0 = fun _ => (0 : ℝ) := by ext u; simp [transferFn]
      rw [h_eq, deriv_const']; exact differentiableAt_const 0
    · rcases lt_or_ge (-1 : ℝ) h with hh_gt | hh_le
      · exact (h_hasDeriv2_gt m s hk_pos hh_gt).differentiableAt
      · have hh_lt : h ∈ Iio (min h_gap Δ_phi) := by
          rw [mem_Iio]; linarith
        have h_ev : deriv (C.transferFn m s k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
          filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
          have h_ev_u : C.transferFn m s k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
            Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu) (h_low_zero m s k)
          rw [h_ev_u.deriv_eq, deriv_const]
        exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_ev
  · obtain ⟨B_R, hB_R_nonneg, hB_R⟩ := C.exists_c2_bound m s N
    obtain ⟨_, _, M_W, hM_W_nonneg, hM_W⟩ := isUniformC2OnGtNegOne_kinematicMultiplier hΔ m s
    refine ⟨4 * B_R * M_W, by positivity, fun {k} hk {h} hh_abs => ?_⟩
    rcases lt_or_ge h 0 with hh_neg | hh_nonneg
    · have hh_lt : h ∈ Iio (min h_gap Δ_phi) := lt_of_lt_of_le hh_neg h_min_pos.le
      have h_ev1 : C.transferFn m s k =ᶠ[𝓝 h] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hh_lt) (h_low_zero m s k)
      have h_ev2 : deriv (C.transferFn m s k) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hh_lt] with u hu
        have h_ev_u : C.transferFn m s k =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hu) (h_low_zero m s k)
        rw [h_ev_u.deriv_eq, deriv_const]
      rw [h_low_zero m s k h hh_lt, h_ev1.deriv_eq, h_ev2.deriv_eq, deriv_const, abs_zero]
      exact ⟨by positivity, by positivity, by positivity⟩
    · have hh_gt : -1 < h := by linarith
      have hk0 : k ≠ 0 := by omega
      obtain ⟨hR0, hR1, hR2⟩ := hB_R hk hh_abs
      obtain ⟨hW0, hW1, hW2⟩ := hM_W hk hh_nonneg
      refine ⟨?_, ?_, ?_⟩
      · simp only [transferFn, hk0, ↓reduceIte, abs_mul]
        have h1 := mul_le_mul hR0 hW0 (abs_nonneg _) hB_R_nonneg
        linarith [mul_nonneg hB_R_nonneg hM_W_nonneg]
      · rw [(h_hasDeriv1_gt m s hk hh_gt).deriv]
        have h1 : |deriv (C.R m s k) h * kinematicMultiplier Δ_phi m s k h| ≤ B_R * M_W := by
          rw [abs_mul]; exact mul_le_mul hR1 hW0 (abs_nonneg _) hB_R_nonneg
        have h2 : |C.R m s k h * deriv (kinematicMultiplier Δ_phi m s k) h| ≤ B_R * M_W := by
          rw [abs_mul]; exact mul_le_mul hR0 hW1 (abs_nonneg _) hB_R_nonneg
        have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
        linarith [mul_nonneg hB_R_nonneg hM_W_nonneg]
      · rw [(h_hasDeriv2_gt m s hk hh_gt).deriv]
        have h1 :
            |deriv (deriv (C.R m s k)) h * kinematicMultiplier Δ_phi m s k h| ≤ B_R * M_W := by
          rw [abs_mul]; exact mul_le_mul hR2 hW0 (abs_nonneg _) hB_R_nonneg
        have h2 :
            |2 * deriv (C.R m s k) h * deriv (kinematicMultiplier Δ_phi m s k) h| ≤
              2 * (B_R * M_W) := by
          rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hR1 hW1 (abs_nonneg _) hB_R_nonneg) (by norm_num)
        have h3 :
            |C.R m s k h * deriv (deriv (kinematicMultiplier Δ_phi m s k)) h| ≤ B_R * M_W := by
          rw [abs_mul]; exact mul_le_mul hR0 hW2 (abs_nonneg _) hB_R_nonneg
        have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
        have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
        linarith

end NormalizedCollinearBlockCoeffs

/-- **Kinematic Existence of Normalized Subleading Collinear Conformal Block Coefficients**:
For any spacetime dimension parameter $\nu \ge 0$, external dimension $\Delta_\phi > 0$, and twist
gap $h_{\mathrm{gap}} > 0$, the quadratic Casimir recursion for $d$-dimensional conformal blocks
yields `NormalizedCollinearBlockCoeffs ν Δ_phi h_gap`. (Kinematic property of conformal blocks.) -/
theorem exists_normalizedCollinearBlockCoeffs (ν Δ_phi h_gap : ℝ)
    (_hν : 0 ≤ ν) (_hΔ : 0 < Δ_phi) (_hh : 0 < h_gap) :
    ∃ _C : NormalizedCollinearBlockCoeffs ν Δ_phi h_gap, True := by
  sorry

/-- **Kinematic Existence of the Collinear Block Transfer Kernel**:
Follows immediately from `exists_normalizedCollinearBlockCoeffs` and
`NormalizedCollinearBlockCoeffs.toCollinearTransferKernel`. -/
theorem exists_collinearTransferKernel (ν Δ_phi h_gap : ℝ)
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh : 0 < h_gap) :
    ∃ _T : CollinearTransferKernel ν Δ_phi h_gap, True := by
  obtain ⟨C, _⟩ := exists_normalizedCollinearBlockCoeffs ν Δ_phi h_gap hν hΔ hh
  exact ⟨C.toCollinearTransferKernel hΔ hh, trivial⟩

/-! ## Section 2: $C^2$ and Support Bounds for Shifted Collinear Test Functions -/

section ShiftedTestFunction

variable {ν Δ_phi h_gap : ℝ} (T : CollinearTransferKernel ν Δ_phi h_gap)

/-- The shifted test function at twist level $m$ and spin shift $s$:
$$\psi_{m, s, k}(h) := \mathcal{K}_{m, s}(k, h) \, \varphi(h + m).$$ -/
noncomputable def CollinearTransferKernel.shiftTestFn
    (m s k : ℕ) (φ : ℝ → ℝ) (h : ℝ) : ℝ :=
  T.K m s k h * φ (h + (m : ℝ))

private lemma deriv_and_deriv2_eq_zero_of_eqOn_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
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

/-- First-order differentiability of `T.shiftTestFn m s k φ`. -/
theorem CollinearTransferKernel.differentiable_shiftTestFn
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (T.shiftTestFn m s k φ) :=
  (T.differentiable_K m s k).mul (differentiable_comp_add_nat hφ m)

/-- Explicit formula for the first derivative of `T.shiftTestFn m s k φ`. -/
theorem CollinearTransferKernel.deriv_shiftTestFn
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (h : ℝ) :
    deriv (T.shiftTestFn m s k φ) h =
      deriv (T.K m s k) h * φ (h + (m : ℝ)) +
        T.K m s k h * deriv φ (h + (m : ℝ)) := by
  have hdK := (T.differentiable_K m s k h).hasDerivAt
  have hdφ := hasDerivAt_comp_add_nat hφ m h
  exact (hdK.mul hdφ).deriv

/-- Second-order differentiability of `T.shiftTestFn m s k φ`. -/
theorem CollinearTransferKernel.differentiable_deriv_shiftTestFn
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Differentiable ℝ (deriv (T.shiftTestFn m s k φ)) := by
  have h_eq : deriv (T.shiftTestFn m s k φ) =
      fun h : ℝ => deriv (T.K m s k) h * φ (h + (m : ℝ)) +
        T.K m s k h * deriv φ (h + (m : ℝ)) := by
    ext h; exact T.deriv_shiftTestFn m s k hφ h
  rw [h_eq]
  exact ((T.differentiable_deriv_K m s k).mul (differentiable_comp_add_nat hφ m)).add
    ((T.differentiable_K m s k).mul (differentiable_comp_add_nat hφ' m))

/-- Explicit formula for the second derivative of `T.shiftTestFn m s k φ`. -/
theorem CollinearTransferKernel.deriv_deriv_shiftTestFn
    (m s k : ℕ) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (h : ℝ) :
    deriv (deriv (T.shiftTestFn m s k φ)) h =
      deriv (deriv (T.K m s k)) h * φ (h + (m : ℝ)) +
        2 * deriv (T.K m s k) h * deriv φ (h + (m : ℝ)) +
        T.K m s k h * deriv (deriv φ) (h + (m : ℝ)) := by
  have h_eq : deriv (T.shiftTestFn m s k φ) =
      fun u : ℝ => deriv (T.K m s k) u * φ (u + (m : ℝ)) +
        T.K m s k u * deriv φ (u + (m : ℝ)) := by
    ext u; exact T.deriv_shiftTestFn m s k hφ u
  rw [h_eq]
  have hdK1 := (T.differentiable_K m s k h).hasDerivAt
  have hdK2 := (T.differentiable_deriv_K m s k h).hasDerivAt
  have hdφ1 := hasDerivAt_comp_add_nat hφ m h
  have hdφ2 := hasDerivAt_comp_add_nat hφ' m h
  have hd_sum : HasDerivAt
      (fun u : ℝ => deriv (T.K m s k) u * φ (u + (m : ℝ)) +
        T.K m s k u * deriv φ (u + (m : ℝ)))
      (deriv (deriv (T.K m s k)) h * φ (h + (m : ℝ)) +
        2 * deriv (T.K m s k) h * deriv φ (h + (m : ℝ)) +
        T.K m s k h * deriv (deriv φ) (h + (m : ℝ))) h :=
    ((hdK2.mul hdφ1).add (hdK1.mul hdφ2)).congr_deriv (by ring)
  exact hd_sum.deriv

/-- **Preservation of Support Radius $[-N, N]$**:
When $h_{\mathrm{gap}}, \Delta_\phi > 0$ and $m \ge 1$, if $\varphi$ vanishes outside $[-N, N]$,
then `T.shiftTestFn m s k φ` also vanishes outside $[-N, N]$ (with the **same** $N$). -/
theorem CollinearTransferKernel.shiftTestFn_eq_zero_of_abs_gt
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    {m : ℕ} (hm : 1 ≤ m) (s k N : ℕ) {φ : ℝ → ℝ}
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0)
    {h : ℝ} (hh : (N : ℝ) < |h|) :
    T.shiftTestFn m s k φ h = 0 := by
  dsimp [CollinearTransferKernel.shiftTestFn]
  rcases lt_or_ge h 0 with h_neg | h_nonneg
  · have h_lt_min : h < min h_gap Δ_phi := lt_of_lt_of_le h_neg (le_min hh_gap.le hΔ.le)
    rw [T.K_eq_zero_of_lt_min m s k h_lt_min, zero_mul]
  · rw [abs_of_nonneg h_nonneg] at hh
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have h_gt : (N : ℝ) < |h + (m : ℝ)| := by
      rw [abs_of_pos (by linarith)]
      linarith
    rw [hsupp (h + (m : ℝ)) h_gt, mul_zero]

/-- **Downward Shift of Upper Twist Window**:
When $m \ge 1$, if $\varphi(u) = 0$ for all $u \ge B + (m : \mathbb{R})$ (and in particular if
$\varphi(u) = 0$ for all $u \ge B + 1$), then `T.shiftTestFn m s k φ h = 0` for all $h \ge B$. -/
theorem CollinearTransferKernel.shiftTestFn_eq_zero_of_ge
    {m : ℕ} (hm : 1 ≤ m) (s k : ℕ) {B : ℝ} {φ : ℝ → ℝ}
    (hφ_hi : ∀ u : ℝ, B + 1 ≤ u → φ u = 0)
    {h : ℝ} (hh : B ≤ h) :
    T.shiftTestFn m s k φ h = 0 := by
  dsimp [CollinearTransferKernel.shiftTestFn]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hφ_hi (h + (m : ℝ)) (by linarith), mul_zero]

/-- **Uniform $C^2$ Norm Bound on `T.shiftTestFn m s k φ`**:
For each $m \ge 1$, $s \in \mathbb{N}$, and support bound $N \in \mathbb{N}$, if $B_{m, s, N}$ is
the uniform $C^2$ bound of `T.K m s k` on $|h| \le N$, then for every $\varphi \in C_c^2([-N, N])$
with $\|\varphi\|_{C^2} \le M_\varphi$, the shifted test function
$\psi = \operatorname{shiftTestFn} m s k \varphi$ satisfies
$|\psi(h)|, |\psi'(h)|, |\psi''(h)| \le 4 B_{m, s, N} M_\varphi$ for all $h \in \mathbb{R}$. -/
theorem CollinearTransferKernel.abs_shiftTestFn_c2_le
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    {m : ℕ} (hm : 1 ≤ m) (s N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      (∀ h, |T.shiftTestFn m s k φ h| ≤ 4 * B * M_φ) ∧
      (∀ h, |deriv (T.shiftTestFn m s k φ) h| ≤ 4 * B * M_φ) ∧
      (∀ h, |deriv (deriv (T.shiftTestFn m s k φ)) h| ≤ 4 * B * M_φ) := by
  obtain ⟨B, hB_nonneg, hB⟩ := T.exists_c2_bound m s N
  refine ⟨B, hB_nonneg, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h_min_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
  have h_zero_low : ∀ u ∈ Iio (min h_gap Δ_phi), T.shiftTestFn m s k φ u = 0 := by
    intro u hu
    dsimp [CollinearTransferKernel.shiftTestFn]
    rw [T.K_eq_zero_of_lt_min m s k hu, zero_mul]
  have h_zero_high : ∀ u ∈ Ioi ((N : ℝ) - 1 / 2), T.shiftTestFn m s k φ u = 0 := by
    intro u hu
    dsimp [CollinearTransferKernel.shiftTestFn]
    rw [mem_Ioi] at hu
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h_gt : (N : ℝ) < |u + (m : ℝ)| := by
      rw [abs_of_pos (by linarith)]
      linarith
    rw [hsupp (u + (m : ℝ)) h_gt, mul_zero]
  have h_all : ∀ h : ℝ,
      |T.shiftTestFn m s k φ h| ≤ 4 * B * M_φ ∧
      |deriv (T.shiftTestFn m s k φ) h| ≤ 4 * B * M_φ ∧
      |deriv (deriv (T.shiftTestFn m s k φ)) h| ≤ 4 * B * M_φ := by
    intro h
    rcases le_or_gt h 0 with h_le0 | h_gt0
    · have hh_mem : h ∈ Iio (min h_gap Δ_phi) := lt_of_le_of_lt h_le0 h_min_pos
      obtain ⟨hz0, hz1, hz2⟩ :=
        deriv_and_deriv2_eq_zero_of_eqOn_open isOpen_Iio h_zero_low hh_mem
      rw [hz0, hz1, hz2, abs_zero]
      exact ⟨by positivity, by positivity, by positivity⟩
    · rcases le_or_gt (N : ℝ) h with h_geN | h_ltN
      · have hh_mem : h ∈ Ioi ((N : ℝ) - 1 / 2) := by
          rw [mem_Ioi]; linarith
        obtain ⟨hz0, hz1, hz2⟩ :=
          deriv_and_deriv2_eq_zero_of_eqOn_open isOpen_Ioi h_zero_high hh_mem
        rw [hz0, hz1, hz2, abs_zero]
        exact ⟨by positivity, by positivity, by positivity⟩
      · have habs_le : |h| ≤ (N : ℝ) := by
          rw [abs_of_pos h_gt0]
          exact h_ltN.le
        obtain ⟨hK0, hK1, hK2⟩ := hB hk1 habs_le
        refine ⟨?_, ?_, ?_⟩
        · dsimp [CollinearTransferKernel.shiftTestFn]
          rw [abs_mul]
          have h1 : |T.K m s k h| * |φ (h + (m : ℝ))| ≤ B * M_φ :=
            mul_le_mul hK0 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg
          linarith [mul_nonneg hB_nonneg hM_φ]
        · rw [T.deriv_shiftTestFn m s k hφ h]
          have h1 : |deriv (T.K m s k) h * φ (h + (m : ℝ))| ≤ B * M_φ := by
            rw [abs_mul]
            exact mul_le_mul hK1 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg
          have h2 : |T.K m s k h * deriv φ (h + (m : ℝ))| ≤ B * M_φ := by
            rw [abs_mul]
            exact mul_le_mul hK0 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg
          have h3 := (abs_add_le _ _).trans (add_le_add h1 h2)
          linarith [mul_nonneg hB_nonneg hM_φ]
        · rw [T.deriv_deriv_shiftTestFn m s k hφ hφ' h]
          have h1 : |deriv (deriv (T.K m s k)) h * φ (h + (m : ℝ))| ≤ B * M_φ := by
            rw [abs_mul]
            exact mul_le_mul hK2 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg
          have h2 : |2 * deriv (T.K m s k) h * deriv φ (h + (m : ℝ))| ≤ 2 * (B * M_φ) := by
            rw [ mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hK1 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg) (by norm_num)
          have h3 : |T.K m s k h * deriv (deriv φ) (h + (m : ℝ))| ≤ B * M_φ := by
            rw [abs_mul]
            exact mul_le_mul hK0 (hφ2 (h + (m : ℝ))) (abs_nonneg _) hB_nonneg
          have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
          have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
          linarith
  exact ⟨fun h => (h_all h).1, fun h => (h_all h).2.1, fun h => (h_all h).2.2⟩

end ShiftedTestFunction

/-! ## Section 3: Triangular Collinear Decomposition of `LightconeBlockFourPointData` -/

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **Triangular Collinear Block Decomposition (`HasCollinearTriangularDecomp`)**:
For any twist level cutoff $M \in \mathbb{N}$, any spin index $k \ge 1$, and any test function
$\varphi : \mathbb{R} \to \mathbb{R}$ vanishing on
$[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
the normalized spin-$2k$ 1D lightcone-block pairing $\mathcal{L}_k(\varphi)$ decomposes into the
leading ($m = 0$) $d$-dimensional primary pairing $\mathcal{P}_k(\varphi)$ plus the finite sum of
subleading ($1 \le m \le M$) collinear block contributions from lower-twist primaries of spin
$2(k + s)$ ($0 \le s \le m$):
$$\mathcal{L}_k(\varphi) = \mathcal{P}_k(\varphi) +
  \sum_{m=1}^{M} \sum_{s=0}^{m}
    \mathcal{P}_{k + s}\bigl(\operatorname{shiftTestFn} T\, m\, s\, k\, \varphi\bigr).$$ -/
def HasCollinearTriangularDecomp {ν Δ_phi : ℝ}
    (T : CollinearTransferKernel ν Δ_phi L.h_gap) : Prop :=
  ∀ (M : ℕ) {k : ℕ}, 1 ≤ k → ∀ {φ : ℝ → ℝ},
    (∀ h : ℝ, min L.h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) →
    L.normLCPairing Δ_phi k φ =
      L.normPrimaryPairing Δ_phi k φ +
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 0 m,
          L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ)

/-- At $M = 0$, the triangular collinear decomposition reduces to the leading-twist identity
`normLCPairing_eq_normPrimaryPairing_of_support_leadingTwist` proved in
`LightconeBlockDecomp.lean`. -/
theorem hasCollinearTriangularDecomp_zero {ν Δ_phi : ℝ}
    (T : CollinearTransferKernel ν Δ_phi L.h_gap)
    {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ_supp : ∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) :
    L.normLCPairing Δ_phi k φ =
      L.normPrimaryPairing Δ_phi k φ +
        ∑ m ∈ Finset.Icc 1 0, ∑ s ∈ Finset.Icc 0 m,
          L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) := by
  simp [L.normLCPairing_eq_normPrimaryPairing_of_support_leadingTwist Δ_phi hk hφ_supp]

/-- **Kinematic Collinear Block Decomposition via Normalized Block Coefficients**:
Any `L : LightconeBlockFourPointData` arising from a $d$-dimensional four-point correlator satisfies
`L.HasCollinearTriangularDecomp (C.toCollinearTransferKernel hΔ hh)` with respect to the normalized
subleading collinear conformal block coefficients `C`. -/
theorem exists_normalizedCollinearTriangularDecomp (ν Δ_phi : ℝ)
    (_hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh : 0 < L.h_gap) :
    ∃ C : NormalizedCollinearBlockCoeffs ν Δ_phi L.h_gap,
      L.HasCollinearTriangularDecomp (C.toCollinearTransferKernel hΔ hh) := by
  sorry

/-- **Kinematic Collinear Block Decomposition of `LightconeBlockFourPointData`**:
Follows immediately from `exists_normalizedCollinearTriangularDecomp` and
`NormalizedCollinearBlockCoeffs.toCollinearTransferKernel`. -/
theorem exists_collinearTriangularDecomp (ν Δ_phi : ℝ)
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh : 0 < L.h_gap) :
    ∃ T : CollinearTransferKernel ν Δ_phi L.h_gap, L.HasCollinearTriangularDecomp T := by
  obtain ⟨C, hC⟩ := L.exists_normalizedCollinearTriangularDecomp ν Δ_phi hν hΔ hh
  exact ⟨C.toCollinearTransferKernel hΔ hh, hC⟩

end LightconeBlockFourPointData

/-! ## Section 4: Canonical Finite-Spin GFF Primary Coefficients & Pairing -/

/-- Normalized spin-$2k$ 1D GFF transmuted coefficient at double-twist level $n \in \mathbb{N}$:
$$c^{\mathrm{GFF, LC}}_n(\Delta_\phi, k) :=
  (2k)^{-2\Delta_\phi}
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  \frac{(2\Delta_\phi)_n}{n!} \, \operatorname{exactTransmutedPochhammer}(\Delta_\phi, n + 2k).$$ -/
noncomputable def gffLCCoeff (Δ_phi : ℝ) (n k : ℕ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
    universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
    pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + 2 * k)

/-- For any $\varphi$ vanishing on $[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$, the
rescaled `exactTransmutedIdentityPairing` truncates to a finite sum over `Finset.range (M + 1)`. -/
theorem mul_exactTransmutedIdentityPairing_eq_sum_range
    {Δ_phi h_gap : ℝ} (M k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ =
      ∑ n ∈ Finset.range (M + 1), gffLCCoeff Δ_phi n k * φ (Δ_phi + (n : ℝ)) := by
  dsimp [exactTransmutedIdentityPairing, gffLCCoeff]
  have h_vanish : ∀ n ∉ Finset.range (M + 1),
      pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + 2 * k) *
        φ (Δ_phi + (n : ℝ)) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hn_cast : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h_min : min h_gap Δ_phi ≤ Δ_phi := min_le_right h_gap Δ_phi
    rw [hφ_hi (Δ_phi + (n : ℝ)) (by linarith), mul_zero]
  rw [tsum_eq_sum h_vanish, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Canonical Finite-Spin GFF $d$-Dimensional Primary Coefficient (`gffPrimaryCoeff`)**:
Defined recursively over the double-twist level $n \in \mathbb{N}$ by triangular inversion of the
collinear block transfer kernel `T`:
$$c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k) := c^{\mathrm{GFF, LC}}_n(\Delta_\phi, k) -
  \sum_{m=1}^{n} \sum_{s=0}^{m}
    \mathcal{K}_{m, s}(k, \Delta_\phi + n - m) \,
      c^{\mathrm{GFF, prim}}_{n - m}(\Delta_\phi, k + s).$$ -/
noncomputable def gffPrimaryCoeff {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) : ℕ → ℕ → ℝ
  | n, k =>
    gffLCCoeff Δ_phi n k -
      ∑ m ∈ (Finset.Icc 1 n).attach,
        ∑ s ∈ Finset.Icc 0 m.1,
          T.K m.1 s k (Δ_phi + ((n - m.1 : ℕ) : ℝ)) *
            have : n - m.1 < n := by
              have hm := Finset.mem_Icc.mp m.2
              omega
            gffPrimaryCoeff T (n - m.1) (k + s)
termination_by n _ => n

/-- Recursive unfolding equation for `gffPrimaryCoeff`. -/
theorem gffPrimaryCoeff_eq {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (n k : ℕ) :
    gffPrimaryCoeff T n k =
      gffLCCoeff Δ_phi n k -
        ∑ m ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 0 m,
          T.K m s k (Δ_phi + ((n - m : ℕ) : ℝ)) * gffPrimaryCoeff T (n - m) (k + s) := by
  rw [gffPrimaryCoeff]
  congr 1
  exact Finset.sum_attach (Finset.Icc 1 n) (fun m =>
    ∑ s ∈ Finset.Icc 0 m,
      T.K m s k (Δ_phi + ((n - m : ℕ) : ℝ)) * gffPrimaryCoeff T (n - m) (k + s))

/-- At leading twist $n = 0$ ($h = \Delta_\phi$), the GFF primary coefficient coincides with the
1D GFF lightcone coefficient `gffLCCoeff Δ_phi 0 k`. -/
@[simp]
theorem gffPrimaryCoeff_zero {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (k : ℕ) :
    gffPrimaryCoeff T 0 k = gffLCCoeff Δ_phi 0 k := by
  rw [gffPrimaryCoeff_eq]
  simp

/-- **Canonical Finite-Spin GFF $d$-Dimensional Primary Pairing (`gffPrimaryPairing`)**:
$$\operatorname{gffPrimaryPairing}(T, k, \varphi) :=
  \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k) \, \varphi(\Delta_\phi + n).$$
Notice that `gffPrimaryPairing` is completely independent of the cutoff $M$ or window size $N$. -/
noncomputable def gffPrimaryPairing {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, gffPrimaryCoeff T n k * φ (Δ_phi + (n : ℝ))

/-- For any $\varphi$ vanishing on $[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
`gffPrimaryPairing T k φ` truncates to the finite sum over `Finset.range (M + 1)`. -/
theorem gffPrimaryPairing_eq_sum_range {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (M k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing T k φ =
      ∑ n ∈ Finset.range (M + 1), gffPrimaryCoeff T n k * φ (Δ_phi + (n : ℝ)) := by
  dsimp [gffPrimaryPairing]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hn_cast : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h_min : min h_gap Δ_phi ≤ Δ_phi := min_le_right h_gap Δ_phi
  rw [hφ_hi (Δ_phi + (n : ℝ)) (by linarith), mul_zero]

/-- Finite triangular double-sum reindexing identity:
$$\sum_{n=0}^{M} \sum_{m=1}^{n} F(m, n - m) =
  \sum_{m=1}^{M} \sum_{n'=0}^{M - m} F(m, n').$$ -/
private lemma sum_range_sum_Icc_eq_sum_Icc_sum_range
    (M : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n, F m (n - m)) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n' ∈ Finset.range (M + 1 - m), F m n' := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have h_icc_split : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not_mem : M + 1 ∉ Finset.Icc 1 M := by
      simp only [Finset.mem_Icc]
      omega
    rw [h_icc_split, Finset.sum_insert h_not_mem, Finset.sum_insert h_not_mem]
    have h_top : ∑ n' ∈ Finset.range (M + 1 + 1 - (M + 1)), F (M + 1) n' =
        F (M + 1) (M + 1 - (M + 1)) := by
      have h_sub1 : M + 1 + 1 - (M + 1) = 1 := by omega
      have h_sub2 : M + 1 - (M + 1) = 0 := by omega
      rw [h_sub1, h_sub2, Finset.sum_range_one]
    rw [h_top]
    have h_inner :
        (∑ m ∈ Finset.Icc 1 M, ∑ n' ∈ Finset.range (M + 1 + 1 - m), F m n') =
          (∑ m ∈ Finset.Icc 1 M, ∑ n' ∈ Finset.range (M + 1 - m), F m n') +
            ∑ m ∈ Finset.Icc 1 M, F m (M + 1 - m) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_le : m ≤ M := (Finset.mem_Icc.mp hm).2
      have h_eq : M + 1 + 1 - m = (M + 1 - m) + 1 := by omega
      rw [h_eq, Finset.sum_range_succ]
    rw [h_inner]
    ring

/-- **Fundamental Triangular Unfolding Identity for `gffPrimaryPairing`**:
For any twist level cutoff $M \in \mathbb{N}$, any spin index $k \in \mathbb{N}$, and any test
function $\varphi : \mathbb{R} \to \mathbb{R}$ vanishing on
$[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
$$\operatorname{gffPrimaryPairing}(T, k, \varphi) =
  (2k)^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi) -
    \sum_{m=1}^{M} \sum_{s=0}^{m}
      \operatorname{gffPrimaryPairing}\bigl(T, k + s,
        \operatorname{shiftTestFn} T\, m\, s\, k\, \varphi\bigr).$$ -/
theorem gffPrimaryPairing_eq_exactIdentity_sub_sum {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (M k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing T k φ =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 0 m,
          gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ) := by
  rw [gffPrimaryPairing_eq_sum_range T M k hφ_hi,
    mul_exactTransmutedIdentityPairing_eq_sum_range (h_gap := h_gap) M k hφ_hi]
  have h_unfold :
      (∑ n ∈ Finset.range (M + 1), gffPrimaryCoeff T n k * φ (Δ_phi + (n : ℝ))) =
        (∑ n ∈ Finset.range (M + 1), gffLCCoeff Δ_phi n k * φ (Δ_phi + (n : ℝ))) -
          ∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n,
            (∑ s ∈ Finset.Icc 0 m,
              T.K m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
                gffPrimaryCoeff T (n - m) (k + s) * φ (Δ_phi + (n : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [gffPrimaryCoeff_eq T n k, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
  rw [h_unfold]
  congr 1
  let F : ℕ → ℕ → ℝ := fun m n' =>
    ∑ s ∈ Finset.Icc 0 m,
      T.K m s k (Δ_phi + (n' : ℝ)) *
        gffPrimaryCoeff T n' (k + s) * φ (Δ_phi + (n' : ℝ) + (m : ℝ))
  have h_lhs_F :
      (∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n,
        ∑ s ∈ Finset.Icc 0 m,
          T.K m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
            gffPrimaryCoeff T (n - m) (k + s) * φ (Δ_phi + (n : ℝ))) =
        ∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n, F m (n - m) := by
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m hm => ?_
    have hm_le : m ≤ n := (Finset.mem_Icc.mp hm).2
    have h_cast : Δ_phi + ((n - m : ℕ) : ℝ) + (m : ℝ) = Δ_phi + (n : ℝ) := by
      rw [Nat.cast_sub hm_le]
      ring
    dsimp [F]
    rw [h_cast]
  rw [h_lhs_F, sum_range_sum_Icc_eq_sum_Icc_sum_range M F]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_mem := Finset.mem_Icc.mp hm
  have hm_le : m ≤ M := hm_mem.2
  dsimp [F]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h_shift_hi : ∀ h : ℝ, min h_gap Δ_phi + ((M - m : ℕ) : ℝ) + 1 ≤ h →
      T.shiftTestFn m s k φ h = 0 := by
    intro h hh
    dsimp [CollinearTransferKernel.shiftTestFn]
    have h_cast : ((M - m : ℕ) : ℝ) + (m : ℝ) = (M : ℝ) := by
      rw [Nat.cast_sub hm_le]; ring
    rw [hφ_hi (h + (m : ℝ)) (by linarith), mul_zero]
  rw [gffPrimaryPairing_eq_sum_range T (M - m) (k + s) h_shift_hi]
  have h_range_eq : M + 1 - m = (M - m) + 1 := by omega
  rw [h_range_eq]
  refine Finset.sum_congr rfl fun n' _ => ?_
  dsimp [CollinearTransferKernel.shiftTestFn]
  ring

/-- On the leading-twist window $(-\infty, \min(h_{\mathrm{gap}}, \Delta_\phi) + 1)$ ($M = 0$),
`gffPrimaryPairing T k φ` coincides identically with the rescaled 1D reference
`(2 * k) ^ (- 2 * Δ_phi) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ`. -/
theorem gffPrimaryPairing_eq_exactIdentity_of_support_leadingTwist {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing T k φ =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ := by
  have h := gffPrimaryPairing_eq_exactIdentity_sub_sum T 0 k (by simpa using hφ_hi)
  have h_empty : Finset.Icc 1 0 = ∅ := rfl
  rw [h_empty, Finset.sum_empty, sub_zero] at h
  exact h

/-- Untransmuted GFF $d$-dimensional primary OPE coefficient at double-twist level $n$ and spin
$2k$:
$$c^{\mathrm{GFF, prim, unwt}}_n(\Delta_\phi, k) :=
  \frac{c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k)}{
    \operatorname{transmuteWeight}(\Delta_\phi + n + 2k)}.$$ -/
noncomputable def unweightedGffPrimaryCoeff {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (n k : ℕ) : ℝ :=
  gffPrimaryCoeff T n k / transmuteWeight (Δ_phi + (n : ℝ) + (2 * k : ℕ))

/-- At leading twist $n = 0$ ($h = \Delta_\phi$), the untransmuted GFF primary coefficient
`unweightedGffPrimaryCoeff T 0 k` reduces directly to the exact 1D GFF block coefficient
`gffBlockCoeff Δ_phi (2 * k)`. -/
theorem unweightedGffPrimaryCoeff_zero {ν Δ_phi h_gap : ℝ}
    (T : CollinearTransferKernel ν Δ_phi h_gap) (hΔ : 0 < Δ_phi) {k : ℕ} (hk : 1 ≤ k) :
    unweightedGffPrimaryCoeff T 0 k =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * (2 * (4 : ℝ) ^ Δ_phi) * gffBlockCoeff Δ_phi (2 * k) := by
  dsimp [unweightedGffPrimaryCoeff]
  rw [gffPrimaryCoeff_zero, Nat.cast_zero, add_zero]
  dsimp [gffLCCoeff, universalPrimaryLeadingCoeff]
  rw [pochhammerCoeff_zero, mul_one, Nat.zero_add]
  have h2k : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k)
  have h_gt : 1 / 2 < Δ_phi + ((2 * k : ℕ) : ℝ) := by linarith
  have h_tw_ne : transmuteWeight (Δ_phi + ((2 * k : ℕ) : ℝ)) ≠ 0 :=
    (transmuteWeight_pos h_gt).ne'
  have h_id := gffBlockCoeff_mul_transmuteWeight_eq hΔ (2 * k)
  dsimp [transmutedCrossFactorCoeff] at h_id
  have h4_split : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [div_eq_iff h_tw_ne]
  linear_combination
    (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * 2 * (4 : ℝ) ^ Δ_phi * h_id.symm +
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * 2 / Real.Gamma Δ_phi ^ 2 *
        Real.Gamma (2 * Δ_phi + 1) * exactTransmutedPochhammer Δ_phi (2 * k) * h4_split

/-! ## Section 5: Inductive Proof of the All-Twist $d$-Dimensional Primary Bootstrap -/

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **Inductive Twist-Window $d$-Dimensional Primary Bootstrap Theorem
(`exists_const_abs_primary_sub_gffPrimary_le_of_support_window`)**:
For every twist level cutoff $M \in \mathbb{N}$, support radius $N \in \mathbb{N}$, and error
exponent $0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, there exists $C > 0$ such that for
all $k \ge 1$ and all $\varphi \in C_c^2([-N, N])$ vanishing on
$[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
$$\Bigl|\mathcal{P}_k(\varphi) - \operatorname{gffPrimaryPairing}(T, k, \varphi)\Bigr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_primary_sub_gffPrimary_le_of_support_window
    {ν Δ_phi γ : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hL : L.AgreesWithCorrelator corr)
    (T : CollinearTransferKernel ν Δ_phi L.h_gap)
    (hT : L.HasCollinearTriangularDecomp T)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N M : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, min L.h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |L.normPrimaryPairing Δ_phi k φ - gffPrimaryPairing T k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C_LC, hC_LC_pos, hC_LC⟩ :=
    L.exists_const_abs_muLC_sub_exactIdentity_le_of_agreesWithCorrelator
      corr hν hΔ hL hγ_pos hγ_lt N
  induction M with
  | zero =>
    refine ⟨C_LC, hC_LC_pos,
      fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_hi hM_φ hφ0 hφ1 hφ2 => ?_⟩
    have h_tri := hT 0 hk1 (by simpa using hsupp_hi)
    have h_gff := gffPrimaryPairing_eq_exactIdentity_sub_sum T 0 k (by simpa using hsupp_hi)
    have h_empty : Finset.Icc 1 0 = ∅ := rfl
    rw [h_empty, Finset.sum_empty, add_zero] at h_tri
    rw [h_empty, Finset.sum_empty, sub_zero] at h_gff
    rw [← h_tri, h_gff]
    exact hC_LC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  | succ M ih =>
    obtain ⟨C_M, hC_M_pos, hC_M⟩ := ih
    choose B_K hB_K_nonneg hB_K using fun (m s : ℕ) =>
      T.exists_c2_bound m s N
    set S_coeff : ℝ :=
      ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m, 4 * B_K m s
    have hS_coeff_nonneg : 0 ≤ S_coeff :=
      Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun s _ =>
        mul_nonneg (by norm_num) (hB_K_nonneg m s)
    set C_next : ℝ := C_LC + C_M * S_coeff
    have hC_next_pos : 0 < C_next := by
      dsimp [C_next]
      positivity
    refine ⟨C_next, hC_next_pos,
      fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_hi hM_φ hφ0 hφ1 hφ2 => ?_⟩
    have h_tri := hT (M + 1) hk1 hsupp_hi
    have h_gff := gffPrimaryPairing_eq_exactIdentity_sub_sum T (M + 1) k hsupp_hi
    have h_diff_eq :
        L.normPrimaryPairing Δ_phi k φ - gffPrimaryPairing T k φ =
          (L.normLCPairing Δ_phi k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) -
          ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ)) := by
      have h_sum_sub :
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))) =
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ)) -
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_sub_distrib _ _
      linarith [h_tri, h_gff, h_sum_sub]
    have h_lc_bound :
        |L.normLCPairing Δ_phi k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
          C_LC * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
      hC_LC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
    have h_term_bound :
        ∀ m ∈ Finset.Icc 1 (M + 1), ∀ s ∈ Finset.Icc 0 m,
          |L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ)| ≤
            C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
      intro m hm s _hs
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hks1 : 1 ≤ k + s := by omega
      have hψ_diff := T.differentiable_shiftTestFn m s k hφ
      have hψ'_diff := T.differentiable_deriv_shiftTestFn m s k hφ hφ'
      have hψ_supp : ∀ h : ℝ, (N : ℝ) < |h| → T.shiftTestFn m s k φ h = 0 :=
        fun _ hh => T.shiftTestFn_eq_zero_of_abs_gt hΔ hL.h_gap_pos hm1 s k N hsupp hh
      have hψ_hi : ∀ h : ℝ, min L.h_gap Δ_phi + (M : ℝ) + 1 ≤ h →
          T.shiftTestFn m s k φ h = 0 := by
        intro h hh
        refine T.shiftTestFn_eq_zero_of_ge hm1 s k (B := min L.h_gap Δ_phi + (M : ℝ) + 1) ?_ hh
        intro u hu
        refine hsupp_hi u ?_
        push_cast
        linarith
      have h_min_pos : 0 < min L.h_gap Δ_phi := lt_min hL.h_gap_pos hΔ
      have h_zero_low : ∀ u ∈ Iio (min L.h_gap Δ_phi), T.shiftTestFn m s k φ u = 0 := by
        intro u hu
        dsimp [CollinearTransferKernel.shiftTestFn]
        rw [T.K_eq_zero_of_lt_min m s k hu, zero_mul]
      have h_zero_high : ∀ u ∈ Ioi ((N : ℝ) - 1 / 2), T.shiftTestFn m s k φ u = 0 := by
        intro u hu
        dsimp [CollinearTransferKernel.shiftTestFn]
        rw [mem_Ioi] at hu
        have hm1_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have h_gt : (N : ℝ) < |u + (m : ℝ)| := by
          rw [abs_of_pos (by linarith)]
          linarith
        rw [hsupp (u + (m : ℝ)) h_gt, mul_zero]
      have hψ_c2 :
          (∀ h, |T.shiftTestFn m s k φ h| ≤ 4 * B_K m s * M_φ) ∧
          (∀ h, |deriv (T.shiftTestFn m s k φ) h| ≤ 4 * B_K m s * M_φ) ∧
          (∀ h, |deriv (deriv (T.shiftTestFn m s k φ)) h| ≤ 4 * B_K m s * M_φ) := by
        have h_all : ∀ h : ℝ,
            |T.shiftTestFn m s k φ h| ≤ 4 * B_K m s * M_φ ∧
            |deriv (T.shiftTestFn m s k φ) h| ≤ 4 * B_K m s * M_φ ∧
            |deriv (deriv (T.shiftTestFn m s k φ)) h| ≤ 4 * B_K m s * M_φ := by
          intro h
          rcases le_or_gt h 0 with h_le0 | h_gt0
          · obtain ⟨hz0, hz1, hz2⟩ :=
              deriv_and_deriv2_eq_zero_of_eqOn_open isOpen_Iio h_zero_low
                (lt_of_le_of_lt h_le0 h_min_pos)
            rw [hz0, hz1, hz2, abs_zero]
            have : 0 ≤ 4 * B_K m s * M_φ :=
              mul_nonneg (mul_nonneg (by norm_num) (hB_K_nonneg m s)) hM_φ
            exact ⟨this, this, this⟩
          · rcases le_or_gt (N : ℝ) h with h_geN | h_ltN
            · have hh_mem : h ∈ Ioi ((N : ℝ) - 1 / 2) := by
                rw [mem_Ioi]; linarith
              obtain ⟨hz0, hz1, hz2⟩ :=
                deriv_and_deriv2_eq_zero_of_eqOn_open isOpen_Ioi h_zero_high hh_mem
              rw [hz0, hz1, hz2, abs_zero]
              have : 0 ≤ 4 * B_K m s * M_φ :=
                mul_nonneg (mul_nonneg (by norm_num) (hB_K_nonneg m s)) hM_φ
              exact ⟨this, this, this⟩
            · have habs_le : |h| ≤ (N : ℝ) := by rw [abs_of_pos h_gt0]; exact h_ltN.le
              obtain ⟨hK0, hK1, hK2⟩ := hB_K m s hk1 habs_le
              have hB_nn := hB_K_nonneg m s
              refine ⟨?_, ?_, ?_⟩
              · dsimp [CollinearTransferKernel.shiftTestFn]
                rw [abs_mul]
                have h1 := mul_le_mul hK0 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                linarith [mul_nonneg hB_nn hM_φ]
              · rw [T.deriv_shiftTestFn m s k hφ h]
                have h1 : |deriv (T.K m s k) h * φ (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK1 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h2 : |T.K m s k h * deriv φ (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK0 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
                linarith [mul_nonneg hB_nn hM_φ]
              · rw [T.deriv_deriv_shiftTestFn m s k hφ hφ' h]
                have h1 : |deriv (deriv (T.K m s k)) h * φ (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK2 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h2 :
                    |2 * deriv (T.K m s k) h * deriv φ (h + (m : ℝ))| ≤
                      2 * (B_K m s * M_φ) := by
                  rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul hK1 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nn) (by norm_num)
                have h3 : |T.K m s k h * deriv (deriv φ) (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK0 (hφ2 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
                have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
                linarith
        exact ⟨fun h => (h_all h).1, fun h => (h_all h).2.1, fun h => (h_all h).2.2⟩
      have hM_ψ : 0 ≤ 4 * B_K m s * M_φ :=
        mul_nonneg (mul_nonneg (by norm_num) (hB_K_nonneg m s)) hM_φ
      have h_ih := hC_M hks1 hψ_diff hψ'_diff hψ_supp hψ_hi hM_ψ hψ_c2.1 hψ_c2.2.1 hψ_c2.2.2
      have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      have h2k_le : 2 * (k : ℝ) ≤ 2 * ((k + s : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * k ≤ 2 * (k + s))
      have hrpow_le : (2 * ((k + s : ℕ) : ℝ)) ^ (-γ) ≤ (2 * (k : ℝ)) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos h2k_pos h2k_le (by linarith)
      calc
        |L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
            gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ)|
          ≤ C_M * (2 * ((k + s : ℕ) : ℝ)) ^ (-γ) * (4 * B_K m s * M_φ) := h_ih
        _ ≤ C_M * (2 * (k : ℝ)) ^ (-γ) * (4 * B_K m s * M_φ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrpow_le hC_M_pos.le) hM_ψ
        _ = C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring
    have h_sum_bound :
        |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))| ≤
          (C_M * S_coeff) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
      calc
        |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))|
          ≤ ∑ m ∈ Finset.Icc 1 (M + 1),
              |∑ s ∈ Finset.Icc 0 m,
                (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
                  gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
              |L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
                gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ)| :=
            Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
              (C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ) :=
            Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun s hs => h_term_bound m hm s hs
        _ = (C_M * S_coeff) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
            dsimp [S_coeff]
            have h_pull :
                (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
                  (C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ)) =
                ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
                  (4 * B_K m s) * (C_M * (2 * (k : ℝ)) ^ (-γ) * M_φ) :=
              Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => by ring
            rw [h_pull]
            simp_rw [← Finset.sum_mul]
            ring
    rw [h_diff_eq]
    calc
      |(L.normLCPairing Δ_phi k φ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) -
        ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
          (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
            gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))|
        ≤ |L.normLCPairing Δ_phi k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| +
          |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (L.normPrimaryPairing Δ_phi (k + s) (T.shiftTestFn m s k φ) -
              gffPrimaryPairing T (k + s) (T.shiftTestFn m s k φ))| :=
          abs_sub _ _
      _ ≤ C_LC * (2 * (k : ℝ)) ^ (-γ) * M_φ +
            (C_M * S_coeff) * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
          add_le_add h_lc_bound h_sum_bound
      _ = C_next * (2 * (k : ℝ)) ^ (-γ) * M_φ := by dsimp [C_next]; ring

/-- **Main All-Twist $d$-Dimensional Primary Large-Spin Bootstrap Theorem
(`exists_const_abs_primary_allTwists_sub_gffPrimary_le`)**:
For **every** support radius $N \in \mathbb{N}$ and **every** error exponent
$0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, there exists $C > 0$ such that for all
$k \ge 1$ and **all** test functions $\varphi \in C_c^2([-N, N])$ (with **no** restriction to the
leading-twist window $h < h_{\mathrm{gap}} + 1$),
$$\Biggl|(2k)^{-2\Delta_\phi} C_{0, 2k}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
    d\mu^{\mathrm{prim}}_{2k}(h)
  - \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim}}_n(\Delta_\phi, k) \,
    \varphi(\Delta_\phi + n)\Biggr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_primary_allTwists_sub_gffPrimary_le
    {ν Δ_phi γ : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hL : L.AgreesWithCorrelator corr)
    (T : CollinearTransferKernel ν Δ_phi L.h_gap)
    (hT : L.HasCollinearTriangularDecomp T)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        gffPrimaryPairing T k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_primary_sub_gffPrimary_le_of_support_window
      corr hν hΔ hL T hT hγ_pos hγ_lt N N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have hsupp_hi : ∀ h : ℝ, min L.h_gap Δ_phi + (N : ℝ) + 1 ≤ h → φ h = 0 := by
    intro h hh
    have h_min_pos : 0 < min L.h_gap Δ_phi := lt_min hL.h_gap_pos hΔ
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h_gt : (N : ℝ) < |h| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hsupp h h_gt
  exact hC hk1 hφ hφ' hsupp hsupp_hi hM_φ hφ0 hφ1 hφ2

/-- **All-Twist $d$-Dimensional Primary Large-Spin Bootstrap Directly from
`NormalizedCollinearBlockCoeffs`
(`exists_const_abs_primary_allTwists_sub_gffPrimary_le_of_normalizedBlockCoeffs`)**:
Applies `C.toCollinearTransferKernel` to obtain the all-twist primary bootstrap directly from
the normalized subleading conformal block coefficients
$\mathcal{R}_{m, s}(k, h) = \chi(h) \frac{B_{m, m - 2s}(h, 2(k + s))}{C_{0, 2(k + s)}}$. -/
theorem exists_const_abs_primary_allTwists_sub_gffPrimary_le_of_normalizedBlockCoeffs
    {ν Δ_phi γ : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hL : L.AgreesWithCorrelator corr)
    (C_blk : NormalizedCollinearBlockCoeffs ν Δ_phi L.h_gap)
    (hC_blk : L.HasCollinearTriangularDecomp
      (C_blk.toCollinearTransferKernel hΔ hL.h_gap_pos))
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        gffPrimaryPairing (C_blk.toCollinearTransferKernel hΔ hL.h_gap_pos) k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  L.exists_const_abs_primary_allTwists_sub_gffPrimary_le
    corr hν hΔ hL (C_blk.toCollinearTransferKernel hΔ hL.h_gap_pos) hC_blk hγ_pos hγ_lt N

/-- **Unweighted All-Twist $d$-Dimensional Primary Large-Spin Bootstrap Corollary
(`exists_const_abs_primary_unweighted_allTwists_le`)**:
For any test function $\varphi : \mathbb{R} \to \mathbb{R}$ written in the form
$\varphi(h) = \operatorname{transmuteWeight}(h + 2k) \, \tilde{\varphi}(h)$ with
$\tilde{\varphi} \in C_c^2([-N, N])$, the unweighted primary integral
$\int_{\mathbb{R}} \varphi(h) \, d\mu^{\mathrm{prim}}_{2k}(h)$ is approximated across all bounded
twists $h \in [-N, N]$ by the untransmuted GFF primary OPE sum with error $O((2k)^{-\gamma})$. -/
theorem exists_const_abs_primary_unweighted_allTwists_le
    {ν Δ_phi γ : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hL : L.AgreesWithCorrelator corr)
    (T : CollinearTransferKernel ν Δ_phi L.h_gap)
    (hT : L.HasCollinearTriangularDecomp T)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ φ_tilde : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, φ h = transmuteWeight (h + (2 * k : ℕ)) * φ_tilde h) →
      Differentiable ℝ φ_tilde → Differentiable ℝ (deriv φ_tilde) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ_tilde h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ_tilde h| ≤ M_φ) → (∀ h, |deriv φ_tilde h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ_tilde) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, φ h ∂(L.muPrim (2 * k))) -
        ∑' n : ℕ,
          (gffPrimaryCoeff T n k / transmuteWeight (Δ_phi + (n : ℝ) + (2 * k : ℕ))) *
            φ (Δ_phi + (n : ℝ))| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_primary_allTwists_sub_gffPrimary_le
      corr hν hΔ hL T hT hγ_pos hγ_lt N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ φ_tilde} {M_φ} hφ_eq hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h_int_eq :
      (∫ h : ℝ, φ h ∂(L.muPrim (2 * k))) =
        ∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ_tilde h ∂(L.muPrim (2 * k)) :=
    integral_congr_ae (Eventually.of_forall fun h => hφ_eq h)
  have h_sum_eq :
      (∑' n : ℕ,
        (gffPrimaryCoeff T n k / transmuteWeight (Δ_phi + (n : ℝ) + (2 * k : ℕ))) *
          φ (Δ_phi + (n : ℝ))) =
        gffPrimaryPairing T k φ_tilde := by
    dsimp [gffPrimaryPairing]
    refine tsum_congr fun n => ?_
    rw [hφ_eq (Δ_phi + (n : ℝ))]
    have h2k : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h_gt : 1 / 2 < Δ_phi + (n : ℝ) + ((2 * k : ℕ) : ℝ) := by linarith
    have h_tw_ne : transmuteWeight (Δ_phi + (n : ℝ) + ((2 * k : ℕ) : ℝ)) ≠ 0 :=
      (transmuteWeight_pos h_gt).ne'
    field_simp [h_tw_ne]
  rw [h_int_eq, h_sum_eq]
  exact hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2

end LightconeBlockFourPointData

end CFT.LightconeBootstrap
