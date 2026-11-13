/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlock.RemainderBounds

/-!
# Stage II: Quantitative 1D Lightcone-Block Bootstrap

This file combines the inner-transmutation reference theory and $t$-channel remainder derivative
bounds in `CFT.LightconeBootstrap.LightconeBlock` (which in turn build on Stage I,
`CFT.LightconeBootstrap.MonomialBootstrap`) to prove the unconditional Stage II lightcone-block
bootstrap theorems for a reflection-positive CFT (`FourPointData`):
- `FourPointData.exists_const_abs_lightcone_sub_exactIdentity_le`: quantitative $O((2k)^{-\gamma})$
  asymptotics of the 1D collinear block measure `lightconeMeasure (2k)` against the exact 3-term
  inner-transmuted identity reference `exactTransmutedIdentityPairing` for all
  $0 < \gamma < \min(2 h_{\text{gap}},\thinspace 2\Delta_\phi)$.
- `FourPointData.exists_const_abs_lightcone_sub_identity_le` and
  `FourPointData.exists_const_abs_lightcone_sub_universal_le`: quantitative $O((2k)^{-\gamma})$
  asymptotics against the 1-term Pochhammer reference `transmutedIdentityPairing` and universal
  Gamma density `transmutedUniversalPairing` for
  $0 < \gamma < \min(2 h_{\text{gap}},\thinspace \min(1,\thinspace 2\Delta_\phi))$.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal ComplexConjugate

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **`LightconeBlockFourPointData.AgreesWithCorrelator`**:
Connects the $s$-channel collinear block decomposition `L : LightconeBlockFourPointData` to the
base four-point correlator `corr : FourPointData ν Δ_phi`:
1. `h_gap_pos`: $h_{\mathrm{gap}} > 0$,
2. `exists_correlator_monomial`: there exists a monomial representation `M : MonomialFourPointData`
   of `corr.correlator_pdisk` on `UcPdisk` with twist gap $h_{\mathrm{gap}}$,
3. `fourierProjSpin_sub_exactIdentity_le`: the folded spin-$2k$ Fourier projection of the
   transmuted $s$-channel correlator minus `exactTransmutedIdentityProjSpin` is bounded by the
   folded contour integral of `transmuteOpInner (tChannelRemainder M Δ_phi (wl0 - i θ))`. -/
structure AgreesWithCorrelator {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi) : Prop where
  /-- Positivity of the non-identity twist gap $h_{\mathrm{gap}} > 0$. -/
  h_gap_pos : 0 < L.h_gap
  /-- Monomial representation `M` of `corr.correlator_pdisk` on `UcPdisk` together with the
  inner-transmutation contour bound. -/
  exists_correlator_monomial :
    ∃ M : MonomialFourPointData,
      (∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
        M.eval wl wr = corr.correlator_pdisk wl wr) ∧
      M.HasTwistGap L.h_gap ∧
      ∀ {σ_minus σ_plus : ℝ}, σ_minus ≤ σ_plus → σ_plus < 0 →
        ∃ C_tail : ℝ, 0 ≤ C_tail ∧
          ∀ {h' : ℝ}, 0 < h' → h' ≤ L.h_gap →
          ∀ {k : ℕ}, 1 ≤ k →
            σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 →
            ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
              ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
                  (L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ))
                      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
                    exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ))
                      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
                ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
                    ((π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
                      Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) *
                        (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)) *
                        transmuteOpInner
                          (tChannelRemainder M Δ_phi
                            ((((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) - (θ : ℂ) * I))
                          (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I))‖ +
                  C_tail * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)))

/-- Constructor for `AgreesWithCorrelator` from the pointwise inner-transmutation identity
$$
\bigl(L.\text{toTransmutedMonomialFourPointData.eval } w_l\, w_r -
  \operatorname{crossIdentityExactTransmuted}(\Delta_\phi, w_l, w_r)\bigr)
  = \operatorname{transmuteOpInner}\bigl(\operatorname{tChannelRemainder} M\, \Delta_\phi\, w_l\bigr)(w_r)
$$
on $\operatorname{UcPdisk}$ (yielding `C_tail = 0`!). -/
theorem AgreesWithCorrelator.of_eval_eq {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)
    (hh_gap : 0 < L.h_gap)
    (M : MonomialFourPointData)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap L.h_gap)
    (h_trans : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      L.toTransmutedMonomialFourPointData.eval wl wr -
        crossIdentityExactTransmuted Δ_phi wl wr =
      transmuteOpInner (tChannelRemainder M Δ_phi wl) wr) :
    L.AgreesWithCorrelator corr where
  h_gap_pos := hh_gap
  exists_correlator_monomial := by
    refine ⟨M, hM, hgap, fun {σ_minus σ_plus} _hσ_le hσ_plus => ?_⟩
    refine ⟨0, le_rfl, fun {h'} _hh'_pos _hh'_le {k} hk1 hσk {σ} hσ => ?_⟩
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
    set wl0 : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    set wr0 : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
    have hwl0 : wl0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wl0]; exact_mod_cast hσl
    have hwr0 : wr0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wr0]; exact_mod_cast hσr
    have h_sub_proj :
        L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ)) wl0 wr0 -
          exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ)) wl0 wr0 =
        (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            transmuteOpInner (tChannelRemainder M Δ_phi (wl0 - (θ : ℂ) * I))
              (wr0 + (θ : ℂ) * I) := by
      dsimp [MonomialFourPointData.fourierProjSpin, exactTransmutedIdentityProjSpin,
        MonomialFourPointData.fourierIntegrand]
      rw [← mul_sub, ← intervalIntegral.integral_sub]
      · congr 1
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hwl_θ : wl0 - (θ : ℂ) * I ∈ UcDisk :=
          MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ
        have hwr_θ : wr0 + (θ : ℂ) * I ∈ UcDisk :=
          MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ
        rw [← mul_sub, h_trans hwl_θ hwr_θ]
      · exact (L.toTransmutedMonomialFourPointData.continuous_fourierIntegrand
          (2 * (k : ℤ)) hwl0 hwr0).intervalIntegrable _ _
      · have h1 : Continuous (fun θ : ℝ =>
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I))) := by fun_prop
        exact (h1.mul
          (continuous_crossIdentityExactTransmuted_shift Δ_phi hwl0 hwr0)).intervalIntegrable _ _
    rw [h_sub_proj, zero_mul, add_zero]

/-- **Derived Constructor (`AgreesWithCorrelator.of_collinear_eval_eq`)**:
Proves `L.AgreesWithCorrelator corr` (with `C_tail = 0`) directly from:
1. the $s$-channel collinear block expansion `corr.correlator_pdisk wl wr = L.evalCollinear wl wr`,
   and
2. the 1D GFF block series `crossFactor Δ_phi w = gffBlockSeries Δ_phi w`,
by commuting `transmuteOpInner` ($\mathcal{L}_0$) through the $s$-channel sum and integral
(`L.transmuteOpInner_evalCollinear`) and through the GFF block series
(`transmuteOpInner_gffBlockSeries`), and using the vanishing of the $J = 0$ truncation difference
in folded spin-$2k$ Fourier projections (`L.fourierProjSpin_evalCollinearTransmuted_eq`). -/
theorem AgreesWithCorrelator.of_collinear_eval_eq {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)
    (hΔ : 0 < Δ_phi)
    (hh_gap : 0 < L.h_gap)
    (h_supp0 : L.muLC 0 (Iio L.h_gap) = 0)
    (h_neg_spin : ∀ J : ℤ, J < 0 → L.muLC J = 0)
    (h_int0 : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (L.muLC 0))
    (M : MonomialFourPointData)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap L.h_gap)
    (h_collinear : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      corr.correlator_pdisk wl wr = L.evalCollinear wl wr)
    (h_gff : ∀ {w : ℂ}, w ∈ UcDisk →
      crossFactor Δ_phi w = gffBlockSeries Δ_phi w) :
    L.AgreesWithCorrelator corr where
  h_gap_pos := hh_gap
  exists_correlator_monomial := by
    refine ⟨M, hM, hgap, fun {σ_minus σ_plus} _hσ_le hσ_plus => ?_⟩
    refine ⟨0, le_rfl, fun {h'} _hh'_pos _hh'_le {k} hk1 hσk {σ} hσ => ?_⟩
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
    set wl0 : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    set wr0 : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
    have hwl0 : wl0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wl0]; exact_mod_cast hσl
    have hwr0 : wr0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wr0]; exact_mod_cast hσr
    have hM_coll : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
        M.eval wl wr = L.evalCollinear wl wr :=
      fun hwl hwr => (hM hwl hwr).trans (h_collinear hwl hwr)
    have h_proj_eq :=
      L.fourierProjSpin_evalCollinearTransmuted_eq h_neg_spin hk1 hwl0 hwr0
    have h_sub_proj :
        L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ)) wl0 wr0 -
          exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ)) wl0 wr0 =
        (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            transmuteOpInner (tChannelRemainder M Δ_phi (wl0 - (θ : ℂ) * I))
              (wr0 + (θ : ℂ) * I) := by
      rw [← h_proj_eq]
      dsimp [exactTransmutedIdentityProjSpin]
      rw [← mul_sub, ← intervalIntegral.integral_sub]
      · congr 1
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hwl_θ : wl0 - (θ : ℂ) * I ∈ UcDisk :=
          MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ
        have hwr_θ : wr0 + (θ : ℂ) * I ∈ UcDisk :=
          MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ
        have h_trans :=
          L.transmuteOpInner_tChannelRemainder_eq_of_collinear hΔ hh_gap h_supp0 h_int0
            M hM_coll h_gff hwl_θ hwr_θ
        rw [← mul_sub, h_trans]
      · set Δ₀ : ℂ := L.evalCollinearTransmutedSpin 0 wl0 wr0 -
          L.toTransmutedMonomialFourPointData.evalSpin 0 wl0 wr0
        have h_eq_θ : ∀ θ : ℝ,
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
              L.evalCollinearTransmuted (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I) =
            L.toTransmutedMonomialFourPointData.fourierIntegrand (2 * (k : ℤ)) wl0 wr0 θ +
              Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) * Δ₀ := by
          intro θ
          have hwl_θ : wl0 - (θ : ℂ) * I ∈ UcDisk :=
            MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ
          have hwr_θ : wr0 + (θ : ℂ) * I ∈ UcDisk :=
            MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ
          rw [L.evalCollinearTransmuted_eq_toTransmuted_eval_add_spinZero h_neg_spin hwl_θ hwr_θ,
            L.spinZero_diff_shift_invariant wl0 wr0 θ]
          dsimp [MonomialFourPointData.fourierIntegrand, Δ₀]
          ring
        simp_rw [h_eq_θ]
        have h_cexp : Continuous (fun θ : ℝ =>
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) * Δ₀) := by fun_prop
        exact ((L.toTransmutedMonomialFourPointData.continuous_fourierIntegrand
          (2 * (k : ℤ)) hwl0 hwr0).add h_cexp).intervalIntegrable _ _
      · have h1 : Continuous (fun θ : ℝ =>
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I))) := by fun_prop
        exact (h1.mul
          (continuous_crossIdentityExactTransmuted_shift Δ_phi hwl0 hwr0)).intervalIntegrable _ _
    rw [h_sub_proj, zero_mul, add_zero]

/-- **Main Bridge Theorem (`hasInnerTransmutedCrossing_of_agreesWithCorrelator`)**:
Any `L : LightconeBlockFourPointData` satisfying `L.AgreesWithCorrelator corr` automatically
satisfies `L.HasInnerTransmutedCrossing Δ_phi`! -/
theorem hasInnerTransmutedCrossing_of_agreesWithCorrelator {ν Δ_phi : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hL : L.AgreesWithCorrelator corr) :
    L.HasInnerTransmutedCrossing Δ_phi where
  Δ_phi_pos := hΔ
  h_gap_pos := hL.h_gap_pos
  exists_inner_remainder_decomp := by
    intro h' hh'_pos hh'_le σ_minus σ_plus hσ_le hσ_plus
    obtain ⟨M, hM, hgap, h_proj⟩ := hL.exists_correlator_monomial
    obtain ⟨C_tail, hC_tail_nonneg, hC_tail⟩ := h_proj hσ_le hσ_plus
    have hσ_minus_neg : σ_minus < 0 := lt_of_le_of_lt hσ_le hσ_plus
    have hσ_plus_half_neg : σ_plus / 2 < 0 := by linarith
    set σl0 : ℝ := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (σ_minus / 2))
    have hσl0_neg : σl0 < 0 := by
      dsimp [σl0]
      have h_prod_pos : 0 < Real.sqrt 2 / 4 * Real.exp (σ_minus / 2) := by positivity
      have h_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (σ_minus / 2) := by
        have h1 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have h2 : Real.exp (σ_minus / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.exp_pos (σ_minus / 2)]
      exact Real.log_neg h_pos (by linarith)
    obtain ⟨M₁, M₂, hM₁_nonneg, hM₂_nonneg, h_low⟩ :=
      exists_low_x_deriv_bounds_tChannelRemainder M corr hν hΔ hM hσ_plus_half_neg
    obtain ⟨C₁, C₂, hC₁_nonneg, hC₂_nonneg, h_high⟩ :=
      exists_high_x_deriv_bounds_tChannelRemainder M corr hν hΔ hM hgap hh'_pos hh'_le
        hσ_plus_half_neg hσl0_neg
    refine ⟨M₁, M₂, C₁, C₂, C_tail,
      hM₁_nonneg, hM₂_nonneg, hC₁_nonneg, hC₂_nonneg, hC_tail_nonneg,
      fun {k} hk1 hσk {σ} hσ => ?_⟩
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
    set wl0 : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    set wr0 : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
    have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
    have hwl0 : wl0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wl0]; exact_mod_cast hσl
    have hwr0 : wr0 ∈ UcDisk := by rw [mem_UcDisk_iff]; dsimp [wr0]; exact_mod_cast hσr
    have hwr0_re_ge : -1 / 2 ≤ wr0.re := by
      dsimp [wr0]
      have h_ge2 : (2 : ℝ) ≤ 2 * (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      have h_le : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h_ge2
      rw [neg_div, neg_div]
      exact neg_le_neg h_le
    have hwl_θ_re_le : ∀ θ : ℝ, (wl0 - (θ : ℂ) * I).re ≤ σ_plus / 2 := by
      intro θ
      dsimp [wl0]
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      linarith [hσ.2, hσk]
    have hwl_θ_im_mem : ∀ {θ : ℝ}, θ ∈ Icc (-π / 2) (π / 2) →
        (wl0 - (θ : ℂ) * I).im ∈ Ioo (-π) π := by
      intro θ hθ
      dsimp [wl0]
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, mem_Ioo]
      exact ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1, Real.pi_pos]⟩
    have hwl_θ_cross_le : ∀ {θ : ℝ}, θ ∈ Icc (-π / 2) (π / 2) →
        (crossW (wl0 - (θ : ℂ) * I)).re ≤ σl0 := by
      intro θ hθ
      refine re_crossW_le_of_re_ge (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ) ?_ ?_
      · dsimp [wl0]
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
        have : 0 < 1 / (2 * (k : ℝ)) := by positivity
        linarith [hσ.1]
      · dsimp [wl0]
        simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, mem_Icc]
        exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    refine ⟨fun θ => tChannelRemainder M Δ_phi (wl0 - (θ : ℂ) * I), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro θ _hθ
      exact integrableOn_transmuteInner_tChannelRemainder M corr hν hΔ hM
        (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ)
        (MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ)
    · intro θ _hθ x hx
      exact (h_low (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ)
        (hwl_θ_re_le θ) (MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ) hx).1
    · intro θ _hθ x hx
      exact (h_low (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ)
        (hwl_θ_re_le θ) (MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ) hx).2
    · intro θ hθ x hx
      have hwr_re : -1 / 2 ≤ (wr0 + (θ : ℂ) * I).re := by simpa using hwr0_re_ge
      have hwr_im : (wr0 + (θ : ℂ) * I).im ∈ Icc (-π / 2) (π / 2) := by
        dsimp [wr0]; simpa using hθ
      exact (h_high (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ)
        (hwl_θ_re_le θ) (hwl_θ_im_mem hθ) (hwl_θ_cross_le hθ)
        (MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ) hwr_re hwr_im hx).1
    · intro θ hθ x hx
      have hwr_re : -1 / 2 ≤ (wr0 + (θ : ℂ) * I).re := by simpa using hwr0_re_ge
      have hwr_im : (wr0 + (θ : ℂ) * I).im ∈ Icc (-π / 2) (π / 2) := by
        dsimp [wr0]; simpa using hθ
      exact (h_high (MonomialFourPointData.sub_I_mul_mem_UcDisk hwl0 θ)
        (hwl_θ_re_le θ) (hwl_θ_im_mem hθ) (hwl_θ_cross_le hθ)
        (MonomialFourPointData.add_I_mul_mem_UcDisk hwr0 θ) hwr_re hwr_im hx).2
    · exact hC_tail hh'_pos hh'_le hk1 hσk hσ

end LightconeBlockFourPointData

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- Collinear evaluation identity and spin-0 gap/integrability properties of
`corr.toLightconeBlockFourPointData hν h_gap`, inherited from
`ConformalBlock.exists_conformalBlockLightcone` and `gffBlockSeries`. -/
lemma toLightconeBlockFourPointData_collinear_props {h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap) :
    corr.lightconeMeasure 0 (Iio h_gap) = 0 ∧
    (∀ J : ℤ, J < 0 → corr.lightconeMeasure J = 0) ∧
    (∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Integrable (fun h : ℝ => monomialTermReal h 0 σl σr) (corr.lightconeMeasure 0)) ∧
    (∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      corr.correlator_pdisk wl wr =
        (corr.toLightconeBlockFourPointData hν h_gap).evalCollinear wl wr) ∧
    (∀ {w : ℂ}, w ∈ UcDisk → crossFactor Δ_phi w = gffBlockSeries Δ_phi w) :=
  ⟨corr.lightconeMeasure_zero_Iio_eq_zero hν (hgap.toMonomialFourPointData hν),
   corr.lightconeMeasure_eq_zero_of_neg,
   fun hσl hσr => corr.lightconeMeasure_integrable_real hν hσl hσr 0,
   fun hwl hwr => corr.correlator_pdisk_eq_one_add_tsum_lightconeMeasure hν
     (hgap.toMonomialFourPointData hν) hwl hwr,
   fun hw => gffBlockSeries_eq_crossFactor hΔ hw⟩

/-- The canonical `LightconeBlockFourPointData` associated to `corr : FourPointData ν Δ_phi`
satisfies `AgreesWithCorrelator corr`, obtained via `AgreesWithCorrelator.of_collinear_eval_eq`
(commuting `transmuteOpInner` with the $s$-channel collinear sum/integral and with the 1D GFF
block series). -/
theorem toLightconeBlockFourPointData_agreesWithCorrelator {h_gap : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap) :
    (corr.toLightconeBlockFourPointData hν h_gap).AgreesWithCorrelator corr := by
  obtain ⟨h_supp0, h_neg, h_int0, h_coll, h_gff⟩ :=
    corr.toLightconeBlockFourPointData_collinear_props hν hΔ hgap
  exact LightconeBlockFourPointData.AgreesWithCorrelator.of_collinear_eval_eq
    (corr.toLightconeBlockFourPointData hν h_gap) corr hΔ hgap.h_gap_pos
    h_supp0 h_neg h_int0 (corr.toMonomialFourPointData hν)
    (fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr)
    (hgap.toMonomialFourPointData hν) h_coll h_gff

/-- **Main Quantitative 1D Lightcone-Block Bootstrap Against `exactTransmutedIdentityPairing`**
(Zero $O(k^{-1})$ Error, Valid for All $\Delta_\phi > 0$, All $h_{\mathrm{gap}} > 0$, and All
$0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$):
For any reflection-positive CFT (`FourPointData ν Δ_phi` with $\nu \ge 0, \Delta_\phi > 0$) with
twist gap `corr.HasTwistGap h_gap`, the 1D collinear block spectral measures
`corr.lightconeMeasure (2k)` satisfy
$$
\Biggl|(2k)^{-2\Delta_\phi}
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \,
    d\mu^{\mathrm{LC}}_{2k}(h)
  - (2k)^{-2\Delta_\phi}
    \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)\Biggr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.
$$ -/
theorem exists_const_abs_lightcone_sub_exactIdentity_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
            ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  (corr.toLightconeBlockFourPointData hν h_gap).exists_const_abs_muLC_sub_exactIdentity_le_of_innerCrossing
    ((corr.toLightconeBlockFourPointData hν h_gap).hasInnerTransmutedCrossing_of_agreesWithCorrelator
      corr hν hΔ (corr.toLightconeBlockFourPointData_agreesWithCorrelator hν hΔ hgap))
    hγ_pos hγ_lt N

/-- **1D Lightcone-Block Bootstrap Against `transmutedIdentityPairing`**
(for $0 < \gamma < \min(2 h_{\mathrm{gap}},\, \min 1\, (2\Delta_\phi))$): -/
theorem exists_const_abs_lightcone_sub_identity_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
            ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hγ_lt_id : γ < min (2 * h_gap) (2 * Δ_phi) :=
    lt_of_lt_of_le hγ_lt (min_le_min le_rfl (min_le_right 1 (2 * Δ_phi)))
  have hγ_le_one : γ ≤ 1 :=
    ((lt_of_lt_of_le hγ_lt (min_le_right _ _)).trans_le (min_le_left 1 (2 * Δ_phi))).le
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    corr.exists_const_abs_lightcone_sub_exactIdentity_le
      hν hΔ hgap hγ_pos hγ_lt_id N
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_const_abs_exactTransmutedIdentityPairing_sub_transmutedIdentityPairing_le hΔ N
  refine ⟨C₁ + C₂, add_pos hC₁_pos hC₂_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hr_one : (2 * (k : ℝ))⁻¹ ≤ (2 * (k : ℝ)) ^ (-γ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_b1 := hC₁ hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  have h_b2 := (hC₂ hk1 hsupp hM_φ hφ0).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr_one hC₂_pos.le) hM_φ)
  calc
    |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
          ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ|
      = |((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
              ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) +
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ)| := by
        congr 1; ring
    _ ≤ |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
              ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| +
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ| :=
        abs_add_le _ _
    _ ≤ C₁ * (2 * (k : ℝ)) ^ (-γ) * M_φ + C₂ * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
        add_le_add h_b1 h_b2
    _ = (C₁ + C₂) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring

/-- **1D Lightcone-Block Bootstrap Against `transmutedUniversalPairing`**: -/
theorem exists_const_abs_lightcone_sub_universal_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
            ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
        transmutedUniversalPairing Δ_phi φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hγ_lt_id : γ < min (2 * h_gap) (2 * Δ_phi) :=
    lt_of_lt_of_le hγ_lt (min_le_min le_rfl (min_le_right 1 (2 * Δ_phi)))
  have hγ_le_one : γ ≤ 1 :=
    ((lt_of_lt_of_le hγ_lt (min_le_right _ _)).trans_le (min_le_left 1 (2 * Δ_phi))).le
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    corr.exists_const_abs_lightcone_sub_exactIdentity_le
      hν hΔ hgap hγ_pos hγ_lt_id N
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_const_abs_exactTransmutedIdentityPairing_sub_universal_le hΔ N
  refine ⟨C₁ + C₂, add_pos hC₁_pos hC₂_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hr_one : (2 * (k : ℝ))⁻¹ ≤ (2 * (k : ℝ)) ^ (-γ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_b1 := hC₁ hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  have h_b2 := (hC₂ hk1 hsupp hM_φ hφ0).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr_one hC₂_pos.le) hM_φ)
  calc
    |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
          ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
      transmutedUniversalPairing Δ_phi φ|
      = |((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
              ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ) +
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
          transmutedUniversalPairing Δ_phi φ)| := by congr 1; ring
    _ ≤ |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h
              ∂(corr.lightconeMeasure (2 * (k : ℤ)))) -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ| +
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
          transmutedUniversalPairing Δ_phi φ| := abs_add_le _ _
    _ ≤ C₁ * (2 * (k : ℝ)) ^ (-γ) * M_φ + C₂ * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
        add_le_add h_b1 h_b2
    _ = (C₁ + C₂) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring

end FourPointData


