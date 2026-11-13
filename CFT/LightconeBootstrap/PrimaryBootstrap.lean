/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlockBootstrap
import CFT.LightconeBootstrap.Primary.TriangularDecomp

/-!
# Stage III: Quantitative $d$-Dimensional Primary Lightcone Bootstrap at All Twists

This file combines the Stage II 1D collinear-block bootstrap
(`CFT.LightconeBootstrap.LightconeBlockBootstrap`) with the triangular descendant decomposition and
smooth transfer kernels in `CFT.LightconeBootstrap.Primary` to prove the main all-twist
$d$-dimensional primary lightcone bootstrap theorems:
- `FourPointData.exists_const_abs_primary_allTwists_sub_gffPrimary_le`: for any support radius
  $N \in \mathbb{N}$ and exponent $0 < \gamma < \min(2 h_{\text{gap}},\thinspace 2\Delta_\phi)$,
  the transmutation-weighted $d$-dimensional primary twist pairing at spin $2k$ matches the
  recursive GFF double-twist prediction `gffPrimaryPairing` up to $O((2k)^{-\gamma})$ across all
  twists $h \in [-N, N]$.
- `FourPointData.exists_const_abs_primary_unweighted_allTwists_le`: the corresponding unweighted
  primary twist integral bound with rate $O((2k)^{-(3/2 + \gamma)})$.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

/-! ## Section 5: Inductive Proof of the All-Twist $d$-Dimensional Primary Bootstrap -/

namespace FourPointData

variable {ν Δ_phi h_gap γ : ℝ} (corr : FourPointData ν Δ_phi)

/-- **Inductive Twist-Window $d$-Dimensional Primary Bootstrap Theorem
(`FourPointData.exists_const_abs_primary_sub_gffPrimary_le_of_support_window`)**:
For every twist level cutoff $M \in \mathbb{N}$, support radius $N \in \mathbb{N}$, and error
exponent $0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, there exists $C > 0$ such that for
all $k \ge 1$ and all $\varphi \in C_c^2([-N, N])$ vanishing on
$[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
$$
\Bigl|\mathcal{P}_k(\varphi) - \operatorname{gffPrimaryPairing}(\nu, \Delta_\phi, k, \varphi)\Bigr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.
$$ -/
theorem exists_const_abs_primary_sub_gffPrimary_le_of_support_window
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi))
    (N M : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |corr.normPrimaryPairing k φ - gffPrimaryPairing ν Δ_phi k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hh_gap : 0 < h_gap := hgap.h_gap_pos
  obtain ⟨C_LC, hC_LC_pos, hC_LC⟩ :=
    corr.exists_const_abs_lightcone_sub_exactIdentity_le
      hν hΔ hgap hγ_pos hγ_lt N
  induction M with
  | zero =>
    refine ⟨C_LC, hC_LC_pos,
      fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_hi hφ0 hφ1 hφ2 => ?_⟩
    have hM_φ : 0 ≤ M_φ := (abs_nonneg (φ 0)).trans (hφ0 0)
    have h_tri :=
      corr.normLCPairing_eq_normPrimaryPairing_add_sum hν hΔ hgap 0 hk1
        hφ.continuous (by simpa using hsupp_hi)
    have h_gff :=
      gffPrimaryPairing_eq_exactIdentity_sub_sum (ν := ν) hΔ hh_gap 0 k
        (by simpa using hsupp_hi)
    have h_empty : Finset.Icc 1 0 = ∅ := rfl
    rw [h_empty, Finset.sum_empty, add_zero] at h_tri
    rw [h_empty, Finset.sum_empty, sub_zero] at h_gff
    rw [← h_tri, h_gff]
    exact hC_LC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  | succ M ih =>
    obtain ⟨C_M, hC_M_pos, hC_M⟩ := ih
    choose B_K hB_K_nonneg hB_K using fun (m s : ℕ) =>
      exists_c2_bound_collinearTransferFn hν hΔ hh_gap m s N
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
      fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_hi hφ0 hφ1 hφ2 => ?_⟩
    have hM_φ : 0 ≤ M_φ := (abs_nonneg (φ 0)).trans (hφ0 0)
    have h_tri :=
      corr.normLCPairing_eq_normPrimaryPairing_add_sum hν hΔ hgap (M + 1) hk1
        hφ.continuous hsupp_hi
    have h_gff :=
      gffPrimaryPairing_eq_exactIdentity_sub_sum (ν := ν) hΔ hh_gap (M + 1) k hsupp_hi
    have h_diff_eq :
        corr.normPrimaryPairing k φ - gffPrimaryPairing ν Δ_phi k φ =
          (corr.normLCPairing k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) -
          ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) := by
      have h_sum_sub :
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ))) =
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) -
          (∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_sub_distrib _ _
      linarith [h_tri, h_gff, h_sum_sub]
    have h_lc_bound :
        |corr.normLCPairing k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
          C_LC * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
      hC_LC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
    have h_term_bound :
        ∀ m ∈ Finset.Icc 1 (M + 1), ∀ s ∈ Finset.Icc 0 m,
          |corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)| ≤
            C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
      intro m hm s _hs
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hks1 : 1 ≤ k + s := by omega
      have hψ_diff := differentiable_collinearShiftTestFn hν hΔ hh_gap m s k hφ
      have hψ'_diff := differentiable_deriv_collinearShiftTestFn hν hΔ hh_gap m s k hφ hφ'
      have hψ_supp : ∀ h : ℝ, (N : ℝ) < |h| →
          collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0 :=
        fun _ hh => collinearShiftTestFn_eq_zero_of_abs_gt hΔ hh_gap hm1 s k N hsupp hh
      have hψ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h →
          collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0 := by
        intro h hh
        refine collinearShiftTestFn_eq_zero_of_ge hm1 s k
          (B := min h_gap Δ_phi + (M : ℝ) + 1) ?_ hh
        intro u hu
        refine hsupp_hi u ?_
        push_cast
        linarith
      have h_min_pos : 0 < min h_gap Δ_phi / 2 := half_pos (lt_min hh_gap hΔ)
      have h_zero_low : ∀ u ∈ Iio (min h_gap Δ_phi / 2),
          collinearShiftTestFn ν Δ_phi h_gap m s k φ u = 0 := by
        intro u hu
        dsimp [collinearShiftTestFn]
        rw [collinearTransferFn_eq_zero_of_lt_half_min hΔ hh_gap m s k hu, zero_mul]
      have h_zero_high : ∀ u ∈ Ioi ((N : ℝ) - 1 / 2),
          collinearShiftTestFn ν Δ_phi h_gap m s k φ u = 0 := by
        intro u hu
        dsimp [collinearShiftTestFn]
        rw [mem_Ioi] at hu
        have hm1_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have h_gt : (N : ℝ) < |u + (m : ℝ)| := by
          rw [abs_of_pos (by linarith)]
          linarith
        rw [hsupp (u + (m : ℝ)) h_gt, mul_zero]
      have hψ_c2 :
          (∀ h, |collinearShiftTestFn ν Δ_phi h_gap m s k φ h| ≤ 4 * B_K m s * M_φ) ∧
          (∀ h, |deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ) h| ≤ 4 * B_K m s * M_φ) ∧
          (∀ h, |deriv (deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) h| ≤
            4 * B_K m s * M_φ) := by
        have h_all : ∀ h : ℝ,
            |collinearShiftTestFn ν Δ_phi h_gap m s k φ h| ≤ 4 * B_K m s * M_φ ∧
            |deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ) h| ≤ 4 * B_K m s * M_φ ∧
            |deriv (deriv (collinearShiftTestFn ν Δ_phi h_gap m s k φ)) h| ≤
              4 * B_K m s * M_φ := by
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
              · dsimp [collinearShiftTestFn]
                rw [abs_mul]
                have h1 := mul_le_mul hK0 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                linarith [mul_nonneg hB_nn hM_φ]
              · rw [deriv_collinearShiftTestFn hν hΔ hh_gap m s k hφ h]
                have h1 :
                    |deriv (collinearTransferFn ν Δ_phi h_gap m s k) h * φ (h + (m : ℝ))| ≤
                      B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK1 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h2 :
                    |collinearTransferFn ν Δ_phi h_gap m s k h * deriv φ (h + (m : ℝ))| ≤
                      B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK0 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
                linarith [mul_nonneg hB_nn hM_φ]
              · rw [deriv_deriv_collinearShiftTestFn hν hΔ hh_gap m s k hφ hφ' h]
                have h1 :
                    |deriv (deriv (collinearTransferFn ν Δ_phi h_gap m s k)) h *
                        φ (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK2 (hφ0 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h2 :
                    |2 * deriv (collinearTransferFn ν Δ_phi h_gap m s k) h *
                        deriv φ (h + (m : ℝ))| ≤
                      2 * (B_K m s * M_φ) := by
                  rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul hK1 (hφ1 (h + (m : ℝ))) (abs_nonneg _) hB_nn) (by norm_num)
                have h3 :
                    |collinearTransferFn ν Δ_phi h_gap m s k h *
                        deriv (deriv φ) (h + (m : ℝ))| ≤ B_K m s * M_φ := by
                  rw [abs_mul]; exact mul_le_mul hK0 (hφ2 (h + (m : ℝ))) (abs_nonneg _) hB_nn
                have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
                have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
                linarith
        exact ⟨fun h => (h_all h).1, fun h => (h_all h).2.1, fun h => (h_all h).2.2⟩
      have hM_ψ : 0 ≤ 4 * B_K m s * M_φ :=
        mul_nonneg (mul_nonneg (by norm_num) (hB_K_nonneg m s)) hM_φ
      have h_ih := hC_M hks1 hψ_diff hψ'_diff hψ_supp hψ_hi hψ_c2.1 hψ_c2.2.1 hψ_c2.2.2
      have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      have h2k_le : 2 * (k : ℝ) ≤ 2 * ((k + s : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * k ≤ 2 * (k + s))
      have hrpow_le : (2 * ((k + s : ℕ) : ℝ)) ^ (-γ) ≤ (2 * (k : ℝ)) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos h2k_pos h2k_le (by linarith)
      calc
        |corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
            gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)|
          ≤ C_M * (2 * ((k + s : ℕ) : ℝ)) ^ (-γ) * (4 * B_K m s * M_φ) := h_ih
        _ ≤ C_M * (2 * (k : ℝ)) ^ (-γ) * (4 * B_K m s * M_φ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrpow_le hC_M_pos.le) hM_ψ
        _ = C_M * (4 * B_K m s) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring
    have h_sum_bound :
        |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ))| ≤
          (C_M * S_coeff) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
      calc
        |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ))|
          ≤ ∑ m ∈ Finset.Icc 1 (M + 1),
              |∑ s ∈ Finset.Icc 0 m,
                (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
                  gffPrimaryPairing ν Δ_phi (k + s)
                    (collinearShiftTestFn ν Δ_phi h_gap m s k φ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
              |corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
                gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ)| :=
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
      |(corr.normLCPairing k φ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) -
        ∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
          (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
            gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ))|
        ≤ |corr.normLCPairing k φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| +
          |∑ m ∈ Finset.Icc 1 (M + 1), ∑ s ∈ Finset.Icc 0 m,
            (corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) -
              gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ))| :=
          abs_sub _ _
      _ ≤ C_LC * (2 * (k : ℝ)) ^ (-γ) * M_φ +
            (C_M * S_coeff) * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
          add_le_add h_lc_bound h_sum_bound
      _ = C_next * (2 * (k : ℝ)) ^ (-γ) * M_φ := by dsimp [C_next]; ring

/-- **Main All-Twist $d$-Dimensional Primary Large-Spin Bootstrap Theorem
(`FourPointData.exists_const_abs_primary_allTwists_sub_gffPrimary_le`)**:
For **every** support radius $N \in \mathbb{N}$ and **every** error exponent
$0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, there exists $C > 0$ such that for all
$k \ge 1$ and **all** test functions $\varphi \in C_c^2([-N, N])$,
$$
\Biggl|(2k)^{-2\Delta_\phi} \frac{(\nu)_{2k}}{(2k)!}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
    d\mu^{\mathrm{prim}}_{2k}(h) - \sum_{n=0}^{\infty}
    c^{\mathrm{GFF, prim}}_n(\nu, \Delta_\phi, k) \,
    \varphi(\Delta_\phi + n)\Biggr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.
$$ -/
theorem exists_const_abs_primary_allTwists_sub_gffPrimary_le
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(corr.primaryTwistMeasure (2 * k))) -
        gffPrimaryPairing ν Δ_phi k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hh_gap : 0 < h_gap := hgap.h_gap_pos
  obtain ⟨C, hC_pos, hC⟩ :=
    corr.exists_const_abs_primary_sub_gffPrimary_le_of_support_window
      hν hΔ hgap hγ_pos hγ_lt N N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hφ0 hφ1 hφ2 => ?_⟩
  have hsupp_hi : ∀ h : ℝ, min h_gap Δ_phi + (N : ℝ) + 1 ≤ h → φ h = 0 := by
    intro h hh
    have h_min_pos : 0 < min h_gap Δ_phi := lt_min hh_gap hΔ
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h_gt : (N : ℝ) < |h| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hsupp h h_gt
  exact hC hk1 hφ hφ' hsupp hsupp_hi hφ0 hφ1 hφ2

private lemma ae_ge_h_gap_primaryTwistMeasure
    (hgap : corr.HasTwistGap h_gap) {l : ℕ} (hl : l ≠ 0) :
    ∀ᵐ h : ℝ ∂(corr.primaryTwistMeasure l), h_gap ≤ h := by
  dsimp [FourPointData.primaryTwistMeasure]
  rw [ae_map_iff (by fun_prop) measurableSet_Ici]
  have h_gap_ae :
      ∀ᵐ p : ℝ × ℕ ∂corr.mu_measure,
        p ∉ { p : ℝ × ℕ | p ≠ ((0 : ℝ), (0 : ℕ)) ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap } :=
    compl_mem_ae_iff.mpr hgap.support_gap
  filter_upwards [ae_mono Measure.restrict_le_self h_gap_ae,
    ae_restrict_mem (measurableSet_spin_eq l)] with p hp_gap hp_l
  change h_gap ≤ (p.1 - (l : ℝ)) / 2
  have hp_eq : p.2 = l := hp_l
  have hp_ne : p ≠ ((0 : ℝ), (0 : ℕ)) := by
    intro h0
    exact hl (hp_eq.symm.trans (congrArg Prod.snd h0))
  rw [← hp_eq]
  exact not_lt.mp fun h_lt => hp_gap ⟨hp_ne, h_lt⟩

/-- **Unweighted All-Twist $d$-Dimensional Primary Large-Spin Bootstrap Theorem
(`FourPointData.exists_const_abs_primary_unweighted_allTwists_le`)**:
For **every** support radius $N \in \mathbb{N}$ and **every** error exponent
$0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$, there exists $C > 0$ such that for all
$k \ge 1$ and **all** test functions $\psi \in C_c^2([-N, N])$, the unweighted primary twist
integral $\int_{\mathbb{R}} \psi(h) \, d\mu^{\mathrm{prim}}_{2k}(h)$ is approximated across all
bounded twists $h \in [-N, N]$ by the untransmuted GFF primary OPE sum:
$$
\Biggl|(2k)^{-2\Delta_\phi} \frac{(\nu)_{2k}}{(2k)!}
  \int_{\mathbb{R}} \psi(h) \, d\mu^{\mathrm{prim}}_{2k}(h) -
  \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim, unwt}}_n(\nu, \Delta_\phi, k) \,
    \psi(\Delta_\phi + n)\Biggr|
  \le C \, (2k)^{-(3/2 + \gamma)} \, M_\psi.
$$ -/
theorem exists_const_abs_primary_unweighted_allTwists_le
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {ψ : ℝ → ℝ} {M_ψ : ℝ},
      Differentiable ℝ ψ → Differentiable ℝ (deriv ψ) →
      (∀ h : ℝ, (N : ℝ) < |h| → ψ h = 0) →
      (∀ h, |ψ h| ≤ M_ψ) → (∀ h, |deriv ψ h| ≤ M_ψ) →
      (∀ h, |deriv (deriv ψ) h| ≤ M_ψ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
          (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
        ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ))| ≤
        C * (2 * (k : ℝ)) ^ (- (3 / 2 + γ)) * M_ψ := by
  have hh_gap : 0 < h_gap := hgap.h_gap_pos
  obtain ⟨C₀, hC₀_pos, hC₀⟩ :=
    corr.exists_const_abs_primary_allTwists_sub_gffPrimary_le
      hν hΔ hgap hγ_pos hγ_lt N
  obtain ⟨B, hB_nonneg, hB⟩ := exists_c2_bound_cutoffInvTransmuteWeight hΔ hh_gap
  set B' : ℝ := max B 1
  have hB'_pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hB_le : B ≤ B' := le_max_left B 1
  refine ⟨4 * B' * C₀, by positivity,
    fun {k} hk1 {ψ} {M_ψ} hψ hψ' hsupp hψ0 hψ1 hψ2 => ?_⟩
  have hM_ψ : 0 ≤ M_ψ := (abs_nonneg (ψ 0)).trans (hψ0 0)
  let W : ℝ → ℝ := cutoffInvTransmuteWeight Δ_phi h_gap k
  let φ : ℝ → ℝ := fun h => W h * ψ h
  have hW_diff : Differentiable ℝ W := differentiable_cutoffInvTransmuteWeight hΔ hh_gap k
  have hW'_diff : Differentiable ℝ (deriv W) :=
    differentiable_deriv_cutoffInvTransmuteWeight hΔ hh_gap k
  have hφ_diff : Differentiable ℝ φ := hW_diff.mul hψ
  have h_deriv_φ : deriv φ = fun h => deriv W h * ψ h + W h * deriv ψ h := by
    ext h
    exact ((hW_diff h).hasDerivAt.mul (hψ h).hasDerivAt).deriv
  have hφ'_diff : Differentiable ℝ (deriv φ) := by
    rw [h_deriv_φ]
    exact (hW'_diff.mul hψ).add (hW_diff.mul hψ')
  have h_deriv2_φ : ∀ h : ℝ,
      deriv (deriv φ) h =
        deriv (deriv W) h * ψ h + 2 * deriv W h * deriv ψ h + W h * deriv (deriv ψ) h := by
    intro h
    rw [h_deriv_φ]
    have hd1 := (hW'_diff h).hasDerivAt.mul (hψ h).hasDerivAt
    have hd2 := (hW_diff h).hasDerivAt.mul (hψ' h).hasDerivAt
    exact ((hd1.add hd2).congr_deriv (by ring)).deriv
  have hφ_supp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0 := by
    intro h hh
    dsimp [φ]
    rw [hsupp h hh, mul_zero]
  have hφ0 : ∀ h : ℝ, |φ h| ≤ 4 * B' * M_ψ := by
    intro h
    obtain ⟨hW0, _, _⟩ := hB hk1 h
    have hW0' : |W h| ≤ B' := hW0.trans hB_le
    dsimp [φ]
    rw [abs_mul]
    have h1 := mul_le_mul hW0' (hψ0 h) (abs_nonneg _) hB'_pos.le
    linarith [mul_nonneg hB'_pos.le hM_ψ]
  have hφ1 : ∀ h : ℝ, |deriv φ h| ≤ 4 * B' * M_ψ := by
    intro h
    obtain ⟨hW0, hW1, _⟩ := hB hk1 h
    have hW0' : |W h| ≤ B' := hW0.trans hB_le
    have hW1' : |deriv W h| ≤ B' := hW1.trans hB_le
    rw [h_deriv_φ]
    have h1 : |deriv W h * ψ h| ≤ B' * M_ψ := by
      rw [abs_mul]; exact mul_le_mul hW1' (hψ0 h) (abs_nonneg _) hB'_pos.le
    have h2 : |W h * deriv ψ h| ≤ B' * M_ψ := by
      rw [abs_mul]; exact mul_le_mul hW0' (hψ1 h) (abs_nonneg _) hB'_pos.le
    have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith [mul_nonneg hB'_pos.le hM_ψ]
  have hφ2 : ∀ h : ℝ, |deriv (deriv φ) h| ≤ 4 * B' * M_ψ := by
    intro h
    obtain ⟨hW0, hW1, hW2⟩ := hB hk1 h
    have hW0' : |W h| ≤ B' := hW0.trans hB_le
    have hW1' : |deriv W h| ≤ B' := hW1.trans hB_le
    have hW2' : |deriv (deriv W) h| ≤ B' := hW2.trans hB_le
    rw [h_deriv2_φ h]
    have h1 : |deriv (deriv W) h * ψ h| ≤ B' * M_ψ := by
      rw [abs_mul]; exact mul_le_mul hW2' (hψ0 h) (abs_nonneg _) hB'_pos.le
    have h2 : |2 * deriv W h * deriv ψ h| ≤ 2 * (B' * M_ψ) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hW1' (hψ1 h) (abs_nonneg _) hB'_pos.le) (by norm_num)
    have h3 : |W h * deriv (deriv ψ) h| ≤ B' * M_ψ := by
      rw [abs_mul]; exact mul_le_mul hW0' (hψ2 h) (abs_nonneg _) hB'_pos.le
    have h12 := (abs_add_le _ _).trans (add_le_add h1 h2)
    have h123 := (abs_add_le _ _).trans (add_le_add h12 h3)
    linarith [mul_nonneg hB'_pos.le hM_ψ]
  have h_weighted := hC₀ hk1 hφ_diff hφ'_diff hφ_supp hφ0 hφ1 hφ2
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
  have h2k_real : (2 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * k)
  have h_int_eq :
      (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(corr.primaryTwistMeasure (2 * k))) =
        (2 * (k : ℝ)) ^ (3 / 2 : ℝ) * (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ge_h_gap_primaryTwistMeasure corr hgap (by omega : 2 * k ≠ 0)] with
      h hh_gap_le
    have hh_min : min h_gap Δ_phi ≤ h := (min_le_left _ _).trans hh_gap_le
    have hh_pos : 0 < h := lt_of_lt_of_le hh_gap hh_gap_le
    have h_tw_ne : transmuteWeight (h + (2 * k : ℕ)) ≠ 0 :=
      (transmuteWeight_pos (by linarith)).ne'
    dsimp [φ, W]
    rw [cutoffInvTransmuteWeight_eq_of_ge_min hΔ hh_gap hk1 hh_min]
    field_simp [h_tw_ne]
  have h_sum_eq :
      gffPrimaryPairing ν Δ_phi k φ =
        (2 * (k : ℝ)) ^ (3 / 2 : ℝ) *
          ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ)) := by
    dsimp [gffPrimaryPairing, unweightedGffPrimaryCoeff, φ, W]
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hh_min : min h_gap Δ_phi ≤ Δ_phi + (n : ℝ) :=
      (min_le_right h_gap Δ_phi).trans (by linarith)
    have h_tw_ne : transmuteWeight (Δ_phi + (n : ℝ) + (2 * k : ℕ)) ≠ 0 :=
      (transmuteWeight_pos (by linarith)).ne'
    rw [cutoffInvTransmuteWeight_eq_of_ge_min hΔ hh_gap hk1 hh_min]
    field_simp [h_tw_ne]
  rw [h_int_eq, h_sum_eq] at h_weighted
  have h_factor :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
          ((2 * (k : ℝ)) ^ (3 / 2 : ℝ) * ∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
        (2 * (k : ℝ)) ^ (3 / 2 : ℝ) *
          ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ)) =
      (2 * (k : ℝ)) ^ (3 / 2 : ℝ) *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
            (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
          ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ))) := by ring
  rw [h_factor, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2k_pos _)] at h_weighted
  have h_mul := mul_le_mul_of_nonneg_left h_weighted
    (Real.rpow_pos_of_pos h2k_pos (- (3 / 2 : ℝ))).le
  have h_cancel :
      (2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) * (2 * (k : ℝ)) ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add h2k_pos]
    norm_num
  have h_rpow_combine :
      (2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) * (2 * (k : ℝ)) ^ (-γ) =
        (2 * (k : ℝ)) ^ (- (3 / 2 + γ)) := by
    rw [← Real.rpow_add h2k_pos]
    congr 1
    ring
  calc
    |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
        (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
      ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ))|
      = ((2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) * (2 * (k : ℝ)) ^ (3 / 2 : ℝ)) *
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
            (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
          ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ))| := by
        rw [h_cancel, one_mul]
    _ = (2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) *
          ((2 * (k : ℝ)) ^ (3 / 2 : ℝ) *
            |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * pochhammerCoeff ν (2 * k) *
              (∫ h : ℝ, ψ h ∂(corr.primaryTwistMeasure (2 * k))) -
            ∑' n : ℕ, unweightedGffPrimaryCoeff ν Δ_phi n k * ψ (Δ_phi + (n : ℝ))|) := by ring
    _ ≤ (2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) *
          (C₀ * (2 * (k : ℝ)) ^ (-γ) * (4 * B' * M_ψ)) := h_mul
    _ = (4 * B' * C₀) * ((2 * (k : ℝ)) ^ (- (3 / 2 : ℝ)) * (2 * (k : ℝ)) ^ (-γ)) * M_ψ := by
        ring
    _ = (4 * B' * C₀) * (2 * (k : ℝ)) ^ (- (3 / 2 + γ)) * M_ψ := by
        rw [h_rpow_combine]

end FourPointData
