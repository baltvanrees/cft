/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Primary.TransferKernel

/-!
# Triangular Collinear Decomposition and Recursive GFF Primary Pairing

This file establishes the finite triangular descendant decomposition relating the 1D collinear-block
pairing `normLCPairing` to the $d$-dimensional primary pairing `normPrimaryPairing`, and defines the
canonical finite-spin Generalized Free Field (GFF) $d$-dimensional primary coefficients:

1. **Triangular Collinear Decomposition of `FourPointData`
   (`FourPointData.normLCPairing_eq_normPrimaryPairing_add_sum`)**:
   For any test function $\varphi$ vanishing above $\min(h_{\text{gap}}, \Delta_\phi) + M + 1$,
   the 1D collinear pairing $\mathcal{L}_k(\varphi)$ decomposes into the $d$-dimensional primary
   pairing $\mathcal{P}_k(\varphi)$ plus a finite sum over twist shifts $1 \le m \le M$ and spin
   shifts $0 \le s \le m$ of $\mathcal{P}_{k+s}(\psi_{m, s, k})$.
2. **Canonical Finite-Spin GFF Primary Coefficients & Pairing (`gffPrimaryCoeff`,
   `gffPrimaryPairing`, `gffPrimaryPairing_eq_exactIdentity_sub_sum`,
   `unweightedGffPrimaryCoeff`)**:
   Defines the $d$-dimensional GFF primary coefficients by triangular recursion and proves that
   `gffPrimaryPairing` satisfies the exact same finite triangular relation against
   `exactTransmutedIdentityPairing`.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

/-! ## Section 3: Triangular Collinear Decomposition of `FourPointData` -/

lemma measurableSet_spin_eq (l : ℕ) :
    MeasurableSet { p : ℝ × ℕ | p.2 = l } :=
  measurableSet_eq_fun measurable_snd measurable_const

namespace FourPointData

variable {ν Δ_phi h_gap : ℝ} (corr : FourPointData ν Δ_phi)

private lemma restrict_spin_eq_nonIdentityMeasure {l : ℕ} (hl : l ≠ 0) :
    corr.mu_measure.restrict { p : ℝ × ℕ | p.2 = l } =
      corr.nonIdentityMeasure.restrict { p : ℝ × ℕ | p.2 = l } := by
  dsimp [FourPointData.nonIdentityMeasure]
  rw [Measure.restrict_restrict (measurableSet_spin_eq l),
    Set.inter_eq_self_of_subset_left]
  intro p hp
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h0
  exact hl (hp.symm.trans (congrArg Prod.snd h0))

private lemma integral_primaryTwistMeasure_eq {l : ℕ} (hl : l ≠ 0)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ h : ℝ, g h ∂(corr.primaryTwistMeasure l)) =
      ∫ p : ℝ × ℕ, (if p.2 = l then g ((p.1 - (p.2 : ℝ)) / 2) else 0)
        ∂corr.nonIdentityMeasure := by
  dsimp [FourPointData.primaryTwistMeasure]
  rw [restrict_spin_eq_nonIdentityMeasure corr hl,
    integral_map (by fun_prop) hg.aestronglyMeasurable,
    ← integral_indicator (measurableSet_spin_eq l)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  by_cases hp : p.2 = l
  · simp [Set.indicator, hp]
  · simp [Set.indicator, hp]

private lemma ae_nonneg_primaryTwistMeasure (l : ℕ) :
    ∀ᵐ h : ℝ ∂(corr.primaryTwistMeasure l), 0 ≤ h := by
  dsimp [FourPointData.primaryTwistMeasure]
  rw [ae_map_iff (by fun_prop) measurableSet_Ici]
  filter_upwards [ae_mono Measure.restrict_le_self corr.ae_unitary,
    ae_restrict_mem (measurableSet_spin_eq l)] with p hp_unit hp_l
  change 0 ≤ (p.1 - (l : ℝ)) / 2
  have hp_eq : p.2 = l := hp_l
  rw [← hp_eq]
  linarith

private lemma integral_primaryTwistMeasure_transmuteWeight_eq
    {l : ℕ} (hl : 1 ≤ l) {ψ : ℝ → ℝ} (hψ : Measurable ψ) :
    (∫ h : ℝ, transmuteWeight (h + (l : ℝ)) * ψ h ∂(corr.primaryTwistMeasure l)) =
      ∫ p : ℝ × ℕ,
        (if p.2 = l then
          transmuteWeight ((p.1 - (p.2 : ℝ)) / 2 + (l : ℝ)) * ψ ((p.1 - (p.2 : ℝ)) / 2)
        else 0) ∂corr.nonIdentityMeasure := by
  have hl_real : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h_ae1 :
      ∀ᵐ h : ℝ ∂(corr.primaryTwistMeasure l),
        transmuteWeight (h + (l : ℝ)) * ψ h = transmutePosWeight (h + (l : ℝ)) * ψ h := by
    filter_upwards [ae_nonneg_primaryTwistMeasure corr l] with h hh
    rw [transmutePosWeight_of_gt (by linarith)]
  have hg_meas : Measurable (fun h : ℝ => transmutePosWeight (h + (l : ℝ)) * ψ h) :=
    (measurable_transmutePosWeight.comp (measurable_id.add measurable_const)).mul hψ
  rw [integral_congr_ae h_ae1, integral_primaryTwistMeasure_eq corr (by omega) hg_meas]
  refine integral_congr_ae ?_
  filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp_unit
  by_cases hp : p.2 = l
  · simp only [hp, ↓reduceIte]
    have hh0 : 0 ≤ (p.1 - (l : ℝ)) / 2 := by
      rw [hp] at hp_unit
      linarith
    rw [transmutePosWeight_of_gt (by linarith)]
  · simp [hp]

private lemma exists_bound_mul_monomialTermReal_of_vanish_ge
    (J : ℤ) {B : ℝ} {φ : ℝ → ℝ} (hφ_cont : Continuous φ)
    (hφ_hi : ∀ h : ℝ, B ≤ h → φ h = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : ℝ}, 0 ≤ h →
      |φ h| ≤ K * monomialTermReal h J (-1) (-1) := by
  let B' : ℝ := max 0 B
  have hB'_nonneg : 0 ≤ B' := le_max_left 0 B
  have h_cont : Continuous (fun h : ℝ => |φ h| * Real.exp (2 * h + (J : ℝ))) := by
    fun_prop
  obtain ⟨x₀, _, hx₀⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hB'_nonneg) h_cont.continuousOn
  refine ⟨|φ x₀| * Real.exp (2 * x₀ + (J : ℝ)), by positivity, fun {h} hh0 => ?_⟩
  rcases le_or_gt h B' with hh_le | hh_gt
  · have h_le : |φ h| * Real.exp (2 * h + (J : ℝ)) ≤
        |φ x₀| * Real.exp (2 * x₀ + (J : ℝ)) :=
      hx₀ ⟨hh0, hh_le⟩
    have h_mono :
        Real.exp (2 * h + (J : ℝ)) * monomialTermReal h J (-1) (-1) = 1 := by
      dsimp [monomialTermReal]
      rw [← Real.exp_add]
      have : 2 * h + (J : ℝ) + (h * -1 + (h + (J : ℝ)) * -1) = 0 := by ring
      rw [this, Real.exp_zero]
    calc
      |φ h| = (|φ h| * Real.exp (2 * h + (J : ℝ))) * monomialTermReal h J (-1) (-1) := by
        rw [mul_assoc, h_mono, mul_one]
      _ ≤ (|φ x₀| * Real.exp (2 * x₀ + (J : ℝ))) * monomialTermReal h J (-1) (-1) :=
        mul_le_mul_of_nonneg_right h_le (monomialTermReal_nonneg h J (-1) (-1))
  · have hB_le : B ≤ h := (le_max_right 0 B).trans hh_gt.le
    rw [hφ_hi h hB_le, abs_zero]
    exact mul_nonneg (by positivity) (monomialTermReal_nonneg h J (-1) (-1))

private lemma lightconeIdxCoeff_mul_eq_sum_Icc
    (ν : ℝ) (m k : ℕ) (f : ℝ → ℝ) (p : ℝ × ℕ) :
    FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * f (lightconeIdxWeight m p) =
      ∑ s ∈ Finset.Icc 0 m,
        if p.2 = 2 * (k + s) then
          FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * f (lightconeIdxWeight m p)
        else 0 := by
  by_cases h_ex : ∃ s ∈ Finset.Icc 0 m, p.2 = 2 * (k + s)
  · rcases h_ex with ⟨s₀, hs₀, hp2⟩
    rw [Finset.sum_eq_single s₀]
    · simp [hp2]
    · intro s _ hs_ne
      have : p.2 ≠ 2 * (k + s) := by omega
      simp [this]
    · intro hs₀_not
      exact (hs₀_not hs₀).elim
  · push_neg at h_ex
    have h_sum_zero :
        (∑ s ∈ Finset.Icc 0 m,
          if p.2 = 2 * (k + s) then
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * f (lightconeIdxWeight m p)
          else 0) = 0 :=
      Finset.sum_eq_zero fun s hs => if_neg (h_ex s hs)
    rw [h_sum_zero]
    have hc_zero : FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p = 0 := by
      by_contra hc_ne
      have h_mem := FourPointData.mem_lightconeRightSpins_of_lightconeIdxCoeff_ne_zero hc_ne
      obtain ⟨s, hs_le, h2s, hkr⟩ := mem_lightconeRightSpins.mp h_mem
      have hs_mem : s ∈ Finset.Icc 0 m := Finset.mem_Icc.mpr ⟨Nat.zero_le s, hs_le⟩
      have hp2_eq : p.2 = 2 * (k + s) := by omega
      exact h_ex s hs_mem hp2_eq
    rw [hc_zero, zero_mul]

private lemma rpow_two_mul_add_mul_div_rpow
    (Δ_phi : ℝ) {k : ℕ} (hk : 1 ≤ k) (s : ℕ) :
    (2 * ((k + s : ℕ) : ℝ)) ^ (- (2 * Δ_phi)) *
        (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hks_pos : (0 : ℝ) < ((k + s : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + s)
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  have h2ks_pos : (0 : ℝ) < 2 * ((k + s : ℕ) : ℝ) := by positivity
  have h_div : (((k + s : ℕ) : ℝ) / (k : ℝ)) =
      (2 * ((k + s : ℕ) : ℝ)) / (2 * (k : ℝ)) := by
    rw [mul_div_mul_left _ _ two_ne_zero]
  have h_ne : (2 * ((k + s : ℕ) : ℝ)) ^ (2 * Δ_phi) ≠ 0 :=
    (Real.rpow_pos_of_pos h2ks_pos _).ne'
  rw [h_div, Real.div_rpow h2ks_pos.le h2k_pos.le,
    Real.rpow_neg h2ks_pos.le, Real.rpow_neg h2k_pos.le]
  field_simp

/-- **Triangular Collinear Block Decomposition
(`FourPointData.normLCPairing_eq_normPrimaryPairing_add_sum`)**:
For any twist level cutoff $M \in \mathbb{N}$, any spin index $k \ge 1$, and any continuous test
function $\varphi : \mathbb{R} \to \mathbb{R}$ vanishing on
$[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
the normalized spin-$2k$ 1D lightcone-block pairing $\mathcal{L}_k(\varphi)$ decomposes into the
leading ($m = 0$) $d$-dimensional primary pairing $\mathcal{P}_k(\varphi)$ plus the finite sum of
subleading ($1 \le m \le M$) collinear block contributions from lower-twist primaries of spin
$2(k + s)$ ($0 \le s \le m$):
$$
\mathcal{L}_k(\varphi) = \mathcal{P}_k(\varphi) +
  \sum_{m=1}^{M} \sum_{s=0}^{m}
    \mathcal{P}_{k + s}\bigl(\operatorname{collinearShiftTestFn}(\nu, \Delta_\phi, h_{\mathrm{gap}}, m, s, k, \varphi)\bigr).
$$ -/
theorem normLCPairing_eq_normPrimaryPairing_add_sum
    (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (M : ℕ) {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ} (hφ_cont : Continuous φ)
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    corr.normLCPairing k φ =
      corr.normPrimaryPairing k φ +
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 0 m,
          corr.normPrimaryPairing (k + s)
            (collinearShiftTestFn ν Δ_phi h_gap m s k φ) := by
  have hh_gap : 0 < h_gap := hgap.h_gap_pos
  have hgap_mon : (corr.toMonomialFourPointData hν).HasTwistGap h_gap :=
    hgap.toMonomialFourPointData hν
  set J : ℤ := 2 * (k : ℤ)
  have hJ_ge : 1 ≤ J := by dsimp [J]; omega
  set F : ℝ → ℝ := fun h => transmutePosWeight (h + (J : ℝ)) * φ h
  have hF_meas : Measurable F :=
    (LightconeBlockFourPointData.measurable_transmutePosWeight_add J).mul hφ_cont.measurable
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    exists_bound_mul_monomialTermReal_of_vanish_ge J hφ_cont hφ_hi
  have h_ae_nonneg : ∀ᵐ h : ℝ ∂(corr.lightconeMeasure J), 0 ≤ h := by
    have h_unit : ∀ᵐ h : ℝ ∂(corr.lightconeMeasure J),
        h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
      compl_mem_ae_iff.mpr (corr.lightconeMeasure_support_unitary J)
    filter_upwards [h_unit] with h hh
    exact not_lt.mp fun hlt => hh (Or.inl hlt)
  have hF_int : Integrable F (corr.lightconeMeasure J) := by
    have h_dom :=
      (corr.lightconeMeasure_integrable_transmute hν
        (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) J).const_mul K
    refine h_dom.mono' hF_meas.aestronglyMeasurable ?_
    filter_upwards [h_ae_nonneg] with h hh0
    dsimp [F]
    rw [abs_mul, abs_of_nonneg (transmutePosWeight_nonneg _)]
    calc
      transmutePosWeight (h + (J : ℝ)) * |φ h|
        ≤ transmutePosWeight (h + (J : ℝ)) * (K * monomialTermReal h J (-1) (-1)) :=
          mul_le_mul_of_nonneg_left (hK_bound hh0) (transmutePosWeight_nonneg _)
      _ = K * (transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J (-1) (-1)) := by ring
  have h_lc_pos :
      (∫ h : ℝ, transmuteWeight (h + (J : ℝ)) * φ h ∂(corr.lightconeMeasure J)) =
        ∫ h : ℝ, F h ∂(corr.lightconeMeasure J) := by
    refine integral_congr_ae ?_
    filter_upwards [(corr.toLightconeBlockFourPointData hν h_gap).ae_transmutePosWeight_eq_transmuteWeight
      hJ_ge] with h hh
    dsimp [F]
    rw [hh]
  have h_sum_q :
      (∫ h : ℝ, F h ∂(corr.lightconeMeasure J)) =
        ∑' q : LightconeIdx,
          if lightconeIdxSpin q = J then
            ∫ p : ℝ × ℕ, FourPointData.lightconeIdxCoeff ν q p * F (lightconeIdxWeight q.1 p)
              ∂corr.nonIdentityMeasure
          else 0 := by
    dsimp [FourPointData.lightconeMeasure] at hF_int ⊢
    rw [integral_sum_measure hF_int]
    congr 1 with q
    split_ifs with hq
    · rw [corr.integral_lightconeAtomMeasure q hF_meas.aestronglyMeasurable]
      rfl
    · exact integral_zero_measure _
  let emb : ℕ → LightconeIdx := fun m => (m, m + 2 * k)
  have hemb_inj : Function.Injective emb := fun m₁ m₂ h => congrArg Prod.fst h
  have hemb_spin (m : ℕ) : lightconeIdxSpin (emb m) = J := by
    dsimp [emb, lightconeIdxSpin, J]
    omega
  have h_vanish_q :
      ∀ q ∉ (Finset.Icc 0 M).image emb,
        (if lightconeIdxSpin q = J then
          ∫ p : ℝ × ℕ, FourPointData.lightconeIdxCoeff ν q p * F (lightconeIdxWeight q.1 p)
            ∂corr.nonIdentityMeasure
        else 0) = 0 := by
    intro q hq_not_mem
    split_ifs with hq_spin
    · have hq2 : q.2 = q.1 + 2 * k := by
        dsimp [lightconeIdxSpin, J] at hq_spin
        omega
      have hq_emb : q = emb q.1 := Prod.ext rfl hq2
      have hq1_gt : M < q.1 := by
        by_contra h_le
        push_neg at h_le
        exact hq_not_mem (Finset.mem_image.mpr ⟨q.1, Finset.mem_Icc.mpr ⟨Nat.zero_le _, h_le⟩,
          hq_emb.symm⟩)
      have hq1_real : (M : ℝ) + 1 ≤ (q.1 : ℝ) := by exact_mod_cast hq1_gt
      have h_ae_zero :
          ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
            FourPointData.lightconeIdxCoeff ν q p * F (lightconeIdxWeight q.1 p) = 0 := by
        filter_upwards [corr.nonIdentityMeasure_ae_lightconeIdxCoeff_eq_zero_of_twist_lt
          hν hgap_mon q] with p hp_gap
        rcases lt_or_ge ((p.1 - (p.2 : ℝ)) / 2) h_gap with h_lt | h_ge
        · rw [hp_gap h_lt, zero_mul]
        · dsimp [F, lightconeIdxWeight]
          have h_min : min h_gap Δ_phi ≤ h_gap := min_le_left _ _
          rw [hφ_hi ((p.1 - (p.2 : ℝ)) / 2 + (q.1 : ℝ)) (by linarith), mul_zero, mul_zero]
      rw [integral_congr_ae h_ae_zero, integral_zero]
    · rfl
  have h_trunc_m :
      (∫ h : ℝ, F h ∂(corr.lightconeMeasure J)) =
        ∑ m ∈ Finset.Icc 0 M,
          ∫ p : ℝ × ℕ,
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
            ∂corr.nonIdentityMeasure := by
    rw [h_sum_q, tsum_eq_sum h_vanish_q, Finset.sum_image (fun m₁ _ m₂ _ h => hemb_inj h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [if_pos (hemb_spin m)]
  have h_int_level (m : ℕ) :
      Integrable
        (fun p : ℝ × ℕ =>
          FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p))
        corr.nonIdentityMeasure := by
    have h_dom :=
      (corr.integrable_lightconeIdxTransmuteRealTerm hν
        (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) (emb m)).const_mul K
    have h_meas : Measurable
        (fun p : ℝ × ℕ =>
          FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)) :=
      (FourPointData.measurable_lightconeIdxCoeff ν (emb m)).mul
        (hF_meas.comp (measurable_lightconeIdxWeight m))
    refine h_dom.mono' h_meas.aestronglyMeasurable ?_
    filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp_unit
    have hw_nonneg : 0 ≤ lightconeIdxWeight m p := by
      dsimp [lightconeIdxWeight]
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h_spin_m := hemb_spin m
    dsimp [emb] at h_spin_m
    dsimp [emb, F, FourPointData.lightconeIdxTransmuteRealTerm, FourPointData.lightconeIdxRealTerm]
    rw [h_spin_m, abs_mul, abs_mul,
      abs_of_nonneg (FourPointData.lightconeIdxCoeff_nonneg ν (m, m + 2 * k) p),
      abs_of_nonneg (transmutePosWeight_nonneg _)]
    calc
      FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p *
          (transmutePosWeight (lightconeIdxWeight m p + (J : ℝ)) * |φ (lightconeIdxWeight m p)|)
        ≤ FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p *
            (transmutePosWeight (lightconeIdxWeight m p + (J : ℝ)) *
              (K * monomialTermReal (lightconeIdxWeight m p) J (-1) (-1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hK_bound hw_nonneg) (transmutePosWeight_nonneg _))
            (FourPointData.lightconeIdxCoeff_nonneg ν (m, m + 2 * k) p)
      _ = K * (transmutePosWeight (lightconeIdxWeight m p + (J : ℝ)) *
            (FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p *
              monomialTermReal (lightconeIdxWeight m p) J (-1) (-1))) := by ring
  have h_level_sum (m : ℕ) :
      (∫ p : ℝ × ℕ,
        FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
        ∂corr.nonIdentityMeasure) =
      ∑ s ∈ Finset.Icc 0 m,
        ∫ p : ℝ × ℕ,
          (if p.2 = 2 * (k + s) then
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
          else 0) ∂corr.nonIdentityMeasure := by
    have h_pt :
        (fun p : ℝ × ℕ =>
          FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)) =
        fun p : ℝ × ℕ =>
          ∑ s ∈ Finset.Icc 0 m,
            if p.2 = 2 * (k + s) then
              FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
            else 0 := by
      ext p
      exact lightconeIdxCoeff_mul_eq_sum_Icc ν m k F p
    rw [h_pt, integral_finset_sum]
    intro s _
    have h_ind :
        (fun p : ℝ × ℕ =>
          if p.2 = 2 * (k + s) then
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
          else 0) =
        Set.indicator { p : ℝ × ℕ | p.2 = 2 * (k + s) }
          (fun p : ℝ × ℕ =>
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)) := by
      ext p
      by_cases hp : p.2 = 2 * (k + s) <;> simp [Set.indicator, hp]
    rw [h_ind]
    exact (h_int_level m).indicator (measurableSet_spin_eq (2 * (k + s)))
  have h_m0 :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (∫ p : ℝ × ℕ,
          FourPointData.lightconeIdxCoeff ν (0, 0 + 2 * k) p * F (lightconeIdxWeight 0 p)
          ∂corr.nonIdentityMeasure) =
        corr.normPrimaryPairing k φ := by
    rw [h_level_sum 0]
    have h_Icc0 : Finset.Icc 0 0 = {0} := rfl
    rw [h_Icc0, Finset.sum_singleton, add_zero, zero_add]
    dsimp [FourPointData.normPrimaryPairing]
    rw [integral_primaryTwistMeasure_transmuteWeight_eq corr (by omega : 1 ≤ 2 * k)
      hφ_cont.measurable, mul_assoc]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp_unit
    by_cases hp : p.2 = 2 * k
    · simp only [hp, ↓reduceIte]
      have hh0 : 0 ≤ (p.1 - ((2 * k : ℕ) : ℝ)) / 2 := by
        rw [hp] at hp_unit
        linarith
      have h_c0 : FourPointData.lightconeIdxCoeff ν (0, 2 * k) p = pochhammerCoeff ν (2 * k) := by
        dsimp [FourPointData.lightconeIdxCoeff, pochhammerCoeff]
        rw [hp] at hp_unit ⊢
        exact (conformalBlock ν p.1 (2 * k)).toLightcone_C_zero hν hp_unit
      have hw0 : lightconeIdxWeight 0 p = (p.1 - ((2 * k : ℕ) : ℝ)) / 2 := by
        dsimp [lightconeIdxWeight]
        rw [hp]
        ring
      have hJ_cast : (J : ℝ) = ((2 * k : ℕ) : ℝ) := by
        dsimp [J]
        push_cast
        ring
      have h2k_real : (2 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * k)
      rw [h_c0, hw0]
      dsimp [F]
      rw [hJ_cast, transmutePosWeight_of_gt (by linarith)]
    · simp [hp]
  have h_ms (m s : ℕ) :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (∫ p : ℝ × ℕ,
          (if p.2 = 2 * (k + s) then
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p * F (lightconeIdxWeight m p)
          else 0) ∂corr.nonIdentityMeasure) =
        corr.normPrimaryPairing (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) := by
    have hψ_meas : Measurable (collinearShiftTestFn ν Δ_phi h_gap m s k φ) :=
      (differentiable_collinearTransferFn hν hΔ hh_gap m s k).continuous.measurable.mul
        (hφ_cont.measurable.comp (measurable_id.add measurable_const))
    dsimp [FourPointData.normPrimaryPairing]
    rw [integral_primaryTwistMeasure_transmuteWeight_eq corr (by omega : 1 ≤ 2 * (k + s)) hψ_meas,
      ← integral_const_mul, ← integral_const_mul]
    rcases hν.eq_or_lt with rfl | hν_pos
    · refine integral_congr_ae ?_
      filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp_unit
      by_cases hp : p.2 = 2 * (k + s)
      · simp only [hp, ↓reduceIte]
        have hh0 : 0 ≤ (p.1 - ((2 * (k + s) : ℕ) : ℝ)) / 2 := by
          rw [hp] at hp_unit
          linarith
        have hp1_eq :
            p.1 = 2 * ((p.1 - ((2 * (k + s) : ℕ) : ℝ)) / 2) + ((2 * (k + s) : ℕ) : ℝ) := by ring
        have h_poch0 : realPochhammer 0 (2 * (k + s)) = 0 :=
          FourPointData.realPochhammer_zero_of_ne_zero (by omega)
        have hc0 : FourPointData.lightconeIdxCoeff 0 (m, m + 2 * k) p = 0 := by
          dsimp [FourPointData.lightconeIdxCoeff]
          rw [hp, hp1_eq,
            toLightcone_C_eq_normalizedCollinearBlockCoeff_mul (le_refl 0) m s k hh0,
            h_poch0, zero_div, mul_zero]
        have h_poch_coeff0 : pochhammerCoeff 0 (2 * (k + s)) = 0 := by
          dsimp [pochhammerCoeff]
          rw [h_poch0, zero_div]
        rw [hc0, h_poch_coeff0]
        ring
      · simp [hp]
    · have h_ae_gap :
          ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
            h_gap ≤ (p.1 - (p.2 : ℝ)) / 2 := by
        have h_compl :
            ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
              p ∉ { p : ℝ × ℕ | (p.1 - (p.2 : ℝ)) / 2 < h_gap } :=
          compl_mem_ae_iff.mpr (corr.nonIdentityMeasure_twist_lt_of_pos hν_pos hgap_mon)
        filter_upwards [h_compl] with p hp
        exact not_lt.mp hp
      refine integral_congr_ae ?_
      filter_upwards [h_ae_gap] with p hp_gap
      by_cases hp : p.2 = 2 * (k + s)
      · simp only [hp, ↓reduceIte]
        set h : ℝ := (p.1 - ((2 * (k + s) : ℕ) : ℝ)) / 2
        have hh_gap_le : h_gap ≤ h := by simpa [h, hp] using hp_gap
        have hh0 : 0 ≤ h := hh_gap.le.trans hh_gap_le
        have hh_min : min h_gap Δ_phi ≤ h := (min_le_left _ _).trans hh_gap_le
        have hp1_eq : p.1 = 2 * h + ((2 * (k + s) : ℕ) : ℝ) := by dsimp [h]; ring
        have hc_eq :
            FourPointData.lightconeIdxCoeff ν (m, m + 2 * k) p =
              normalizedCollinearBlockCoeff ν m s k h * pochhammerCoeff ν (2 * (k + s)) := by
          dsimp [FourPointData.lightconeIdxCoeff, pochhammerCoeff]
          rw [hp, hp1_eq]
          exact toLightcone_C_eq_normalizedCollinearBlockCoeff_mul hν m s k hh0
        have hw_eq : lightconeIdxWeight m p = h + (m : ℝ) := by
          dsimp [lightconeIdxWeight, h]
          rw [hp]
        have hJ_cast : (J : ℝ) = ((2 * k : ℕ) : ℝ) := by
          dsimp [J]
          push_cast
          ring
        have h2k_real : (2 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * k)
        have h2ks_real : (2 : ℝ) ≤ ((2 * (k + s) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ 2 * (k + s))
        have hm_real : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hF_eq :
            F (lightconeIdxWeight m p) =
              transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) * φ (h + (m : ℝ)) := by
          rw [hw_eq]
          dsimp [F]
          rw [hJ_cast, transmutePosWeight_of_gt (by linarith)]
        have hK_eq := collinearTransferFn_eq_of_ge_min (ν := ν) hΔ hh_gap m s hk hh_min
        have htw_ne : transmuteWeight (h + (2 * (k + s) : ℕ)) ≠ 0 :=
          (transmuteWeight_pos (by linarith)).ne'
        have h_pow := rpow_two_mul_add_mul_div_rpow Δ_phi hk s
        dsimp [collinearShiftTestFn]
        rw [hc_eq, hF_eq, hK_eq]
        calc
          (2 * (k : ℝ)) ^ (-(2 * Δ_phi)) *
              (normalizedCollinearBlockCoeff ν m s k h * pochhammerCoeff ν (2 * (k + s)) *
                (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) * φ (h + (m : ℝ))))
            = ((2 * ((k + s : ℕ) : ℝ)) ^ (-(2 * Δ_phi)) *
                (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi)) *
              (normalizedCollinearBlockCoeff ν m s k h * pochhammerCoeff ν (2 * (k + s)) *
                (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) * φ (h + (m : ℝ)))) := by
              rw [h_pow]
          _ = (2 * ((k + s : ℕ) : ℝ)) ^ (-(2 * Δ_phi)) * pochhammerCoeff ν (2 * (k + s)) *
                (transmuteWeight (h + (2 * (k + s) : ℕ)) *
                  ((((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) *
                    normalizedCollinearBlockCoeff ν m s k h *
                    (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) /
                      transmuteWeight (h + (2 * (k + s) : ℕ))) *
                    φ (h + (m : ℝ)))) := by
              have h_cancel :
                  transmuteWeight (h + (2 * (k + s) : ℕ)) *
                    (transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) /
                      transmuteWeight (h + (2 * (k + s) : ℕ))) =
                  transmuteWeight (h + (m : ℝ) + (2 * k : ℕ)) :=
                mul_div_cancel₀ _ htw_ne
              linear_combination
                -((2 * ((k + s : ℕ) : ℝ)) ^ (-(2 * Δ_phi)) * pochhammerCoeff ν (2 * (k + s)) *
                  (((k + s : ℕ) : ℝ) / (k : ℝ)) ^ (2 * Δ_phi) *
                  normalizedCollinearBlockCoeff ν m s k h * φ (h + (m : ℝ))) * h_cancel
      · simp [hp]
  dsimp [FourPointData.normLCPairing]
  rw [h_lc_pos, h_trunc_m]
  have h_split_Icc : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h_zero_not_mem : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  rw [h_split_Icc, Finset.sum_insert h_zero_not_mem, mul_add, h_m0]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h_level_sum m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => h_ms m s

end FourPointData

/-! ## Section 4: Canonical Finite-Spin GFF Primary Coefficients & Pairing -/

/-- Normalized spin-$2k$ 1D GFF transmuted coefficient at double-twist level $n \in \mathbb{N}$:
$$
c^{\mathrm{GFF, LC}}_n(\Delta_\phi, k) :=
  (2k)^{-2\Delta_\phi}
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  \frac{(2\Delta_\phi)_n}{n!} \, \operatorname{exactTransmutedPochhammer}(\Delta_\phi, n + 2k).
$$ -/
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
collinear block transfer ratio `collinearTransferRatio ν Δ_phi`:
$$
c^{\mathrm{GFF, prim}}_n(\nu, \Delta_\phi, k) := c^{\mathrm{GFF, LC}}_n(\Delta_\phi, k) -
  \sum_{m=1}^{n} \sum_{s=0}^{m}
    \mathcal{R}^{\mathrm{trans}}_{m, s}(\nu, \Delta_\phi, k, \Delta_\phi + n - m) \,
      c^{\mathrm{GFF, prim}}_{n - m}(\nu, \Delta_\phi, k + s).
$$ -/
noncomputable def gffPrimaryCoeff (ν Δ_phi : ℝ) : ℕ → ℕ → ℝ
  | n, k =>
    gffLCCoeff Δ_phi n k -
      ∑ m ∈ (Finset.Icc 1 n).attach,
        ∑ s ∈ Finset.Icc 0 m.1,
          collinearTransferRatio ν Δ_phi m.1 s k (Δ_phi + ((n - m.1 : ℕ) : ℝ)) *
            have : n - m.1 < n := by
              have hm := Finset.mem_Icc.mp m.2
              omega
            gffPrimaryCoeff ν Δ_phi (n - m.1) (k + s)
termination_by n _ => n

/-- Recursive unfolding equation for `gffPrimaryCoeff`. -/
theorem gffPrimaryCoeff_eq (ν Δ_phi : ℝ) (n k : ℕ) :
    gffPrimaryCoeff ν Δ_phi n k =
      gffLCCoeff Δ_phi n k -
        ∑ m ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 0 m,
          collinearTransferRatio ν Δ_phi m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
            gffPrimaryCoeff ν Δ_phi (n - m) (k + s) := by
  rw [gffPrimaryCoeff]
  congr 1
  exact Finset.sum_attach (Finset.Icc 1 n) (fun m =>
    ∑ s ∈ Finset.Icc 0 m,
      collinearTransferRatio ν Δ_phi m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
        gffPrimaryCoeff ν Δ_phi (n - m) (k + s))

/-- At leading twist $n = 0$ ($h = \Delta_\phi$), the GFF primary coefficient coincides with the
1D GFF lightcone coefficient `gffLCCoeff Δ_phi 0 k`. -/
@[simp]
theorem gffPrimaryCoeff_zero (ν Δ_phi : ℝ) (k : ℕ) :
    gffPrimaryCoeff ν Δ_phi 0 k = gffLCCoeff Δ_phi 0 k := by
  rw [gffPrimaryCoeff_eq]
  simp

/-- **Canonical Finite-Spin GFF $d$-Dimensional Primary Pairing (`gffPrimaryPairing`)**:
$$
\operatorname{gffPrimaryPairing}(\nu, \Delta_\phi, k, \varphi) :=
  \sum_{n=0}^{\infty} c^{\mathrm{GFF, prim}}_n(\nu, \Delta_\phi, k) \, \varphi(\Delta_\phi + n).
$$
Notice that `gffPrimaryPairing` depends only on $(\nu, \Delta_\phi, k, \varphi)$ and is completely
independent of $h_{\mathrm{gap}}$, $M$, or the support radius $N$. -/
noncomputable def gffPrimaryPairing (ν Δ_phi : ℝ) (k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, gffPrimaryCoeff ν Δ_phi n k * φ (Δ_phi + (n : ℝ))

/-- For any $\varphi$ vanishing on $[\min(h_{\mathrm{gap}}, \Delta_\phi) + M + 1, \infty)$,
`gffPrimaryPairing ν Δ_phi k φ` truncates to the finite sum over `Finset.range (M + 1)`. -/
theorem gffPrimaryPairing_eq_sum_range {ν Δ_phi h_gap : ℝ}
    (M k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing ν Δ_phi k φ =
      ∑ n ∈ Finset.range (M + 1), gffPrimaryCoeff ν Δ_phi n k * φ (Δ_phi + (n : ℝ)) := by
  dsimp [gffPrimaryPairing]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hn_cast : (M : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h_min : min h_gap Δ_phi ≤ Δ_phi := min_le_right h_gap Δ_phi
  rw [hφ_hi (Δ_phi + (n : ℝ)) (by linarith), mul_zero]

/-- Finite triangular double-sum reindexing identity:
$$
\sum_{n=0}^{M} \sum_{m=1}^{n} F(m, n - m) =
  \sum_{m=1}^{M} \sum_{n'=0}^{M - m} F(m, n').
$$ -/
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
$$
\operatorname{gffPrimaryPairing}(\nu, \Delta_\phi, k, \varphi) =
  (2k)^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi) -
    \sum_{m=1}^{M} \sum_{s=0}^{m}
      \operatorname{gffPrimaryPairing}\bigl(\nu, \Delta_\phi, k + s,
        \operatorname{collinearShiftTestFn}(\nu, \Delta_\phi, h_{\mathrm{gap}}, m, s, k, \varphi)\bigr).
$$ -/
theorem gffPrimaryPairing_eq_exactIdentity_sub_sum {ν Δ_phi h_gap : ℝ}
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (M k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + (M : ℝ) + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing ν Δ_phi k φ =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
        ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 0 m,
          gffPrimaryPairing ν Δ_phi (k + s) (collinearShiftTestFn ν Δ_phi h_gap m s k φ) := by
  rw [gffPrimaryPairing_eq_sum_range (h_gap := h_gap) M k hφ_hi,
    mul_exactTransmutedIdentityPairing_eq_sum_range (h_gap := h_gap) M k hφ_hi]
  have h_unfold :
      (∑ n ∈ Finset.range (M + 1), gffPrimaryCoeff ν Δ_phi n k * φ (Δ_phi + (n : ℝ))) =
        (∑ n ∈ Finset.range (M + 1), gffLCCoeff Δ_phi n k * φ (Δ_phi + (n : ℝ))) -
          ∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n,
            (∑ s ∈ Finset.Icc 0 m,
              collinearTransferRatio ν Δ_phi m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
                gffPrimaryCoeff ν Δ_phi (n - m) (k + s) * φ (Δ_phi + (n : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [gffPrimaryCoeff_eq ν Δ_phi n k, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
  rw [h_unfold]
  congr 1
  let F : ℕ → ℕ → ℝ := fun m n' =>
    ∑ s ∈ Finset.Icc 0 m,
      collinearTransferRatio ν Δ_phi m s k (Δ_phi + (n' : ℝ)) *
        gffPrimaryCoeff ν Δ_phi n' (k + s) * φ (Δ_phi + (n' : ℝ) + (m : ℝ))
  have h_lhs_F :
      (∑ n ∈ Finset.range (M + 1), ∑ m ∈ Finset.Icc 1 n,
        ∑ s ∈ Finset.Icc 0 m,
          collinearTransferRatio ν Δ_phi m s k (Δ_phi + ((n - m : ℕ) : ℝ)) *
            gffPrimaryCoeff ν Δ_phi (n - m) (k + s) * φ (Δ_phi + (n : ℝ))) =
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
      collinearShiftTestFn ν Δ_phi h_gap m s k φ h = 0 := by
    intro h hh
    dsimp [collinearShiftTestFn]
    have h_cast : ((M - m : ℕ) : ℝ) + (m : ℝ) = (M : ℝ) := by
      rw [Nat.cast_sub hm_le]; ring
    rw [hφ_hi (h + (m : ℝ)) (by linarith), mul_zero]
  rw [gffPrimaryPairing_eq_sum_range (h_gap := h_gap) (M - m) (k + s) h_shift_hi]
  have h_range_eq : M + 1 - m = (M - m) + 1 := by omega
  rw [h_range_eq]
  refine Finset.sum_congr rfl fun n' _ => ?_
  dsimp [collinearShiftTestFn]
  have h_ge_min : min h_gap Δ_phi ≤ Δ_phi + (n' : ℝ) := by
    have h1 : min h_gap Δ_phi ≤ Δ_phi := min_le_right h_gap Δ_phi
    have h2 : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg n'
    linarith
  rw [collinearTransferFn_eq_collinearTransferRatio_of_ge_min hΔ hh_gap m s k h_ge_min]
  ring

/-- On the leading-twist window $(-\infty, \min(h_{\mathrm{gap}}, \Delta_\phi) + 1)$ ($M = 0$),
`gffPrimaryPairing ν Δ_phi k φ` coincides identically with the rescaled 1D reference
`(2 * k) ^ (- 2 * Δ_phi) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ`. -/
theorem gffPrimaryPairing_eq_exactIdentity_of_support_leadingTwist {ν Δ_phi h_gap : ℝ}
    (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap) (k : ℕ) {φ : ℝ → ℝ}
    (hφ_hi : ∀ h : ℝ, min h_gap Δ_phi + 1 ≤ h → φ h = 0) :
    gffPrimaryPairing ν Δ_phi k φ =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ := by
  have h := gffPrimaryPairing_eq_exactIdentity_sub_sum (ν := ν) hΔ hh_gap 0 k (by simpa using hφ_hi)
  have h_empty : Finset.Icc 1 0 = ∅ := rfl
  rw [h_empty, Finset.sum_empty, sub_zero] at h
  exact h

/-- Untransmuted GFF $d$-dimensional primary OPE coefficient at double-twist level $n$ and spin
$2k$:
$$
c^{\mathrm{GFF, prim, unwt}}_n(\nu, \Delta_\phi, k) :=
  \frac{c^{\mathrm{GFF, prim}}_n(\nu, \Delta_\phi, k)}{
    \operatorname{transmuteWeight}(\Delta_\phi + n + 2k)}.
$$ -/
noncomputable def unweightedGffPrimaryCoeff (ν Δ_phi : ℝ) (n k : ℕ) : ℝ :=
  gffPrimaryCoeff ν Δ_phi n k / transmuteWeight (Δ_phi + (n : ℝ) + (2 * k : ℕ))

/-- At leading twist $n = 0$ ($h = \Delta_\phi$), the untransmuted GFF primary coefficient
`unweightedGffPrimaryCoeff ν Δ_phi 0 k` reduces directly to the exact 1D GFF block coefficient
`gffBlockCoeff Δ_phi (2 * k)`. -/
theorem unweightedGffPrimaryCoeff_zero (ν : ℝ) {Δ_phi : ℝ}
    (hΔ : 0 < Δ_phi) {k : ℕ} (hk : 1 ≤ k) :
    unweightedGffPrimaryCoeff ν Δ_phi 0 k =
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
