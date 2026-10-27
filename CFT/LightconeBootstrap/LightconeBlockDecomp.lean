/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Transmute1d
import CFT.LightconeBootstrap.MonomialDecomp

/-!
# Lightcone Conformal Block Decomposition and Transmuted Monomial Data

This file implements **Phase 2** of `PLAN_CONFORMAL_BLOCKS.md`:
1. **Action of `transmuteOp` ($\mathcal{L}_0$) on `ConformalBlockLightconeLevel` and
   `ConformalBlockLightcone`**:
   Applying `transmuteOp` (`CFT/LightconeBootstrap/Transmute1d.lean`) to each lightcone twist level
   $g_m(w_r)$ of a `ConformalBlockLightcone Δ l` (`CFT/Blocks_pdisk.lean`) converts the finite
   linear combination of 1D conformal blocks into a finite linear combination of exponentials
   (`ConformalBlockLightconeLevel.transmuteOp_eval`). At leading twist $m = 0$,
   $e^{\frac{\Delta - l}{2} w_l} \operatorname{transmuteOp}(g_0)(w_r)$ collapses to a
   **single monomial** `monomialTerm ((Δ - l) / 2) l wl wr` with positive coefficient
   $C_{0, l} \, \operatorname{transmuteWeight}\!\left(\frac{\Delta + l}{2}\right)$
   (`ConformalBlockLightcone.exp_mul_transmuteOp_evalLevel_zero`).
2. **Option A `LightconeBlockFourPointData` & `toTransmutedMonomialFourPointData`**:
   We package the lightcone-block spectral decomposition of a four-point function into
   `LightconeBlockFourPointData` and construct its transmuted `MonomialFourPointData`
   (`toTransmutedMonomialFourPointData`), proving the integral pairing identities that connect the
   transmuted monomial spectral measures $\mu^{\text{trans}}_J$ directly to the $d$-dimensional
   primary operator measures $\mu^{\text{prim}}_l$
   (`pairSpin_toTransmuted_eq_primary_of_support_leadingTwist`,
   `primary_pair_eq_toTransmuted_pair_div`).
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Action of `transmuteOp` on `ConformalBlockLightcone` -/

/-- Action of `transmuteOp` ($\mathcal{L}_0$) on a single lightcone twist level `lvl.eval Δ l`. -/
theorem ConformalBlockLightconeLevel.transmuteOp_eval
    (lvl : ConformalBlockLightconeLevel) (Δ : ℝ) (l : ℕ)
    (hH : ∀ kr ∈ lvl.support, 1 / 2 < blockExp Δ l kr)
    {wr : ℂ} (hwr : wr ∈ UcDisk) :
    transmuteOp (lvl.eval Δ l) wr =
      ∑ kr ∈ lvl.support,
        (lvl.C kr : ℂ) * (transmuteWeight (blockExp Δ l kr) : ℂ) *
          Complex.exp ((blockExp Δ l kr : ℂ) * wr) :=
  transmuteOp_finset_sum_block1d lvl.support (fun kr => (lvl.C kr : ℂ))
    (fun kr => blockExp Δ l kr) hH hwr

/-- At leading twist $m = 0$, `transmuteOp` ($\mathcal{L}_0$) maps `L.evalLevel 0` to a single
exponential with weight `transmuteWeight ((Δ + l) / 2)`. -/
theorem ConformalBlockLightcone.transmuteOp_evalLevel_zero
    {Δ : ℝ} {l : ℕ} (L : ConformalBlockLightcone Δ l)
    (hH : 1 / 2 < (Δ + (l : ℝ)) / 2) {wr : ℂ} (hwr : wr ∈ UcDisk) :
    transmuteOp (L.evalLevel 0) wr =
      ((L.level 0).C l : ℂ) * (transmuteWeight ((Δ + (l : ℝ)) / 2) : ℂ) *
        Complex.exp ((((Δ + (l : ℝ)) / 2 : ℝ) : ℂ) * wr) := by
  have h_eq : L.evalLevel 0 =
      fun z => ((L.level 0).C l : ℂ) * block1d ((Δ + (l : ℝ)) / 2) z := by
    ext z; exact L.evalLevel_zero z
  rw [h_eq, transmuteOp_const_mul, transmuteOp_block1d hH hwr, mul_assoc]

/-- Multiplying the transmuted leading-twist level $m = 0$ by
$e^{\operatorname{blockExp}(\Delta, l, 0) w_l}$ produces a **single monomial**
`monomialTerm ((Δ - l) / 2) l wl wr` at spin $J = l$ and left twist $h = (\Delta - l) / 2$. -/
theorem ConformalBlockLightcone.exp_mul_transmuteOp_evalLevel_zero
    {Δ : ℝ} {l : ℕ} (L : ConformalBlockLightcone Δ l)
    (hH : 1 / 2 < (Δ + (l : ℝ)) / 2) (wl : ℂ) {wr : ℂ} (hwr : wr ∈ UcDisk) :
    Complex.exp ((blockExp Δ l 0 : ℂ) * wl) * transmuteOp (L.evalLevel 0) wr =
      ((L.level 0).C l : ℂ) * (transmuteWeight ((Δ + (l : ℝ)) / 2) : ℂ) *
        monomialTerm ((Δ - (l : ℝ)) / 2) (l : ℤ) wl wr := by
  rw [ConformalBlockLightcone.transmuteOp_evalLevel_zero L hH hwr]
  dsimp [monomialTerm, blockExp]
  have h_exp :
      Complex.exp ((((Δ - (l : ℝ)) / 2 + (0 : ℕ) : ℝ) : ℂ) * wl) *
        (((L.level 0).C l : ℂ) * (transmuteWeight ((Δ + (l : ℝ)) / 2) : ℂ) *
          Complex.exp ((((Δ + (l : ℝ)) / 2 : ℝ) : ℂ) * wr)) =
      ((L.level 0).C l : ℂ) * (transmuteWeight ((Δ + (l : ℝ)) / 2) : ℂ) *
        (Complex.exp ((((Δ - (l : ℝ)) / 2 + (0 : ℕ) : ℝ) : ℂ) * wl) *
          Complex.exp ((((Δ + (l : ℝ)) / 2 : ℝ) : ℂ) * wr)) := by
    ring
  rw [h_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Section 2: Option A `LightconeBlockFourPointData` & Transmuted `MonomialFourPointData` -/

/-- **Option A Lightcone-Block Four-Point Data** (`PLAN_CONFORMAL_BLOCKS.md`, Stage 2):
packages the 1D lightcone-block spectral measures $\mu^{\text{LC}}_J$ ($J \in \mathbb{Z}$) and the
$d$-dimensional primary operator measures $\mu^{\text{prim}}_l$ ($l \in \mathbb{N}$ over primary
left twist $h = (\Delta - l)/2 \in \mathbb{R}$) of a four-point correlation function on
$\operatorname{UcPdisk}$, together with:
1. Unitarity ($h \ge 0, \bar{h} = h + J \ge 0$) and Bose symmetry ($\mu^{\text{LC}}_J = 0$ for
   odd $J$),
2. Integrability and spin-summability of the transmuted monomial expansion on the negative real
   half-lines $\sigma_l < 0, \sigma_r < 0$,
3. The leading-twist relation on $(-\infty, h_{\text{gap}} + 1)$: because all $m \ge 1$ subleading
   lightcone levels of non-identity primaries have left twist $h_0 + m \ge h_{\text{gap}} + 1$,
   the restriction of $\mu^{\text{LC}}_l$ ($l \ge 1$) to $(-\infty, h_{\text{gap}} + 1)$ equals
   $C_{0, l} \, \mu^{\text{prim}}_l$ restricted to $(-\infty, h_{\text{gap}} + 1)$. -/
structure LightconeBlockFourPointData where
  /-- 1D lightcone-block spectral measure $\mu^{\text{LC}}_J$ over left twist $h \in \mathbb{R}$ at
  spin $J = \bar{h} - h \in \mathbb{Z}$. -/
  muLC : ℤ → Measure ℝ

  /-- $d$-dimensional primary operator spectral measure $\mu^{\text{prim}}_l$ over primary left
  twist $h = (\Delta - l) / 2 \in \mathbb{R}$ at spin $l \in \mathbb{N}$. -/
  muPrim : ℕ → Measure ℝ

  /-- Leading-twist ($m = 0$) lightcone block normalization $C_{0, l} > 0$ (e.g. $(\nu)_l / l!$). -/
  leadingTwistCoeff : ℕ → ℝ

  /-- Positivity of the leading-twist normalization $C_{0, l} > 0$. -/
  leadingTwistCoeff_pos : ∀ l : ℕ, 0 < leadingTwistCoeff l

  /-- Twist gap $h_{\text{gap}} > 0$ of non-identity primary operators. -/
  h_gap : ℝ

  /-- Unitarity support of $\mu^{\text{LC}}_J$: both $h \ge 0$ and $\bar{h} = h + J \ge 0$ hold
  $\mu^{\text{LC}}_J$-almost everywhere. -/
  support_unitary : ∀ J : ℤ, muLC J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0

  /-- Bose symmetry: odd spins $J$ have vanishing lightcone-block spectral measure. -/
  support_odd_spin : ∀ J : ℤ, Odd J → muLC J = 0

  /-- Integrability of the transmuted real monomials on $\sigma_l < 0, \sigma_r < 0$. -/
  integrable_transmute : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 → ∀ J : ℤ,
    Integrable
      (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr)
      (muLC J)

  /-- Spin-summability of the transmuted real monomials on $\sigma_l < 0, \sigma_r < 0$. -/
  summable_transmute : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
    Summable (fun J : ℤ =>
      ∫ h : ℝ, transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr ∂(muLC J))

  /-- **Leading-twist primary isolation ($M = 0$)**:
  For every spin $l \ge 1$, all $m \ge 1$ subleading lightcone levels are supported in
  $[h_{\text{gap}} + 1, \infty)$, so on $(-\infty, h_{\text{gap}} + 1)$ the 1D lightcone-block
  measure $\mu^{\text{LC}}_l$ coincides with $C_{0, l} \, \mu^{\text{prim}}_l$. -/
  muLC_restrict_leadingTwist : ∀ l : ℕ, 1 ≤ l →
    (muLC (l : ℤ)).restrict (Iio (h_gap + 1)) =
      ENNReal.ofReal (leadingTwistCoeff l) • (muPrim l).restrict (Iio (h_gap + 1))

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- The spin-$J$ transmuted spectral measure
$$d\mu^{\text{trans}}_J(h) :=
  \operatorname{transmutePosWeight}(h + J) \, d\mu^{\text{LC}}_J(h).$$ -/
noncomputable def transmutedMeasure (J : ℤ) : Measure ℝ :=
  (L.muLC J).withDensity (fun h : ℝ => ENNReal.ofReal (transmutePosWeight (h + (J : ℝ))))

lemma measurable_transmutePosWeight_add (J : ℤ) :
    Measurable (fun h : ℝ => transmutePosWeight (h + (J : ℝ))) :=
  measurable_transmutePosWeight.comp (measurable_id.add measurable_const)

/-- Characterization of Bochner integrability with respect to `L.transmutedMeasure J`. -/
lemma integrable_transmutedMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℤ) {f : ℝ → E} :
    Integrable f (L.transmutedMeasure J) ↔
      Integrable (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) • f h) (L.muLC J) := by
  dsimp [transmutedMeasure]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_transmutePosWeight_add J).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun h => ?_)
  dsimp
  rw [ENNReal.toReal_ofReal (transmutePosWeight_nonneg (h + (J : ℝ)))]

/-- Integral against `L.transmutedMeasure J` expressed as a weighted integral against `L.muLC J`. -/
theorem integral_transmutedMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : ℤ) (f : ℝ → E) :
    ∫ h : ℝ, f h ∂(L.transmutedMeasure J) =
      ∫ h : ℝ, transmutePosWeight (h + (J : ℝ)) • f h ∂(L.muLC J) := by
  dsimp [transmutedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_transmutePosWeight_add J).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp
  rw [ENNReal.toReal_ofReal (transmutePosWeight_nonneg (h + (J : ℝ)))]

/-- Unitarity support of `L.transmutedMeasure J`. -/
lemma transmutedMeasure_support_unitary (J : ℤ) :
    L.transmutedMeasure J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0 := by
  dsimp [transmutedMeasure]
  exact withDensity_absolutelyContinuous (L.muLC J) _ (L.support_unitary J)

/-- Bose symmetry of `L.transmutedMeasure J`. -/
lemma transmutedMeasure_support_odd_spin (J : ℤ) (hJ : Odd J) :
    L.transmutedMeasure J = 0 := by
  dsimp [transmutedMeasure]
  rw [L.support_odd_spin J hJ, withDensity_zero_left]

/-- **Canonical Transmuted `MonomialFourPointData`** associated to a `LightconeBlockFourPointData`:
equips the correlator with the positive monomial spectral measures
$d\mu^{\text{trans}}_J(h) = \operatorname{transmutePosWeight}(h + J) \, d\mu^{\text{LC}}_J(h)$. -/
noncomputable def toTransmutedMonomialFourPointData : MonomialFourPointData where
  mu := L.transmutedMeasure
  support_unitary := L.transmutedMeasure_support_unitary
  support_odd_spin := L.transmutedMeasure_support_odd_spin
  integrable_real := by
    intro σl σr hσl hσr J
    rw [L.integrable_transmutedMeasure_iff]
    exact L.integrable_transmute hσl hσr J
  summable_real := by
    intro σl σr hσl hσr
    simp_rw [L.integral_transmutedMeasure, smul_eq_mul]
    exact L.summable_transmute hσl hσr

/-- For any spin $J \ge 1$, $h \ge 0$ implies $h + J > 1/2$, so $\mu^{\text{LC}}_J$-almost
everywhere `transmutePosWeight (h + J) = transmuteWeight (h + J)`. -/
lemma ae_transmutePosWeight_eq_transmuteWeight {J : ℤ} (hJ : 1 ≤ J) :
    ∀ᵐ h : ℝ ∂(L.muLC J),
      transmutePosWeight (h + (J : ℝ)) = transmuteWeight (h + (J : ℝ)) := by
  have h_unit : ∀ᵐ h : ℝ ∂(L.muLC J), h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (L.support_unitary J)
  filter_upwards [h_unit] with h hh
  have hh0 : 0 ≤ h := not_lt.mp fun hlt => hh (Or.inl hlt)
  have hJ_real : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have h_gt : 1 / 2 < h + (J : ℝ) := by linarith
  exact transmutePosWeight_of_gt h_gt

/-- For any spin $J \ge 1$ and any test function $\varphi : \mathbb{R} \to \mathbb{R}$, the pairing
of `L.toTransmutedMonomialFourPointData` with $\varphi$ is
$$\int_{\mathbb{R}} \varphi(h) \, d\mu^{\text{trans}}_J(h) =
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + J) \,
    \varphi(h) \, d\mu^{\text{LC}}_J(h).$$ -/
theorem pairSpin_toTransmutedMonomialFourPointData {J : ℤ} (hJ : 1 ≤ J) (φ : ℝ → ℝ) :
    L.toTransmutedMonomialFourPointData.pairSpin J φ =
      ∫ h : ℝ, transmuteWeight (h + (J : ℝ)) * φ h ∂(L.muLC J) := by
  dsimp [MonomialFourPointData.pairSpin, toTransmutedMonomialFourPointData]
  rw [L.integral_transmutedMeasure]
  refine integral_congr_ae ?_
  filter_upwards [L.ae_transmutePosWeight_eq_transmuteWeight hJ] with h hh
  simp [smul_eq_mul, hh]

/-- **Leading-Twist Primary Reduction ($M = 0$)**:
For any spin $l \ge 1$ and any test function $\varphi : \mathbb{R} \to \mathbb{R}$ vanishing on
$[h_{\text{gap}} + 1, \infty)$, the transmuted monomial pairing equals the $d$-dimensional primary
pairing weighted by $C_{0, l} \, \operatorname{transmuteWeight}(h + l)$:
$$\int_{\mathbb{R}} \varphi(h) \, d\mu^{\text{trans}}_l(h) =
  C_{0, l} \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + l) \, \varphi(h) \,
    d\mu^{\text{prim}}_l(h).$$ -/
theorem pairSpin_toTransmuted_eq_primary_of_support_leadingTwist
    {l : ℕ} (hl : 1 ≤ l) {φ : ℝ → ℝ}
    (hφ_supp : ∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) :
    L.toTransmutedMonomialFourPointData.pairSpin (l : ℤ) φ =
      L.leadingTwistCoeff l *
        ∫ h : ℝ, transmuteWeight (h + (l : ℝ)) * φ h ∂(L.muPrim l) := by
  have hJ : (1 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
  rw [L.pairSpin_toTransmutedMonomialFourPointData hJ]
  simp only [Int.cast_natCast]
  set F : ℝ → ℝ := fun h => transmuteWeight (h + (l : ℝ)) * φ h
  have hF_zero : ∀ h ∉ Iio (L.h_gap + 1), F h = 0 := by
    intro h hh
    rw [mem_Iio, not_lt] at hh
    dsimp [F]
    rw [hφ_supp h hh, mul_zero]
  have h_rest1 : ∫ h : ℝ, F h ∂(L.muLC (l : ℤ)) =
      ∫ h in Iio (L.h_gap + 1), F h ∂(L.muLC (l : ℤ)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hF_zero).symm
  have h_rest2 : ∫ h : ℝ, F h ∂(L.muPrim l) =
      ∫ h in Iio (L.h_gap + 1), F h ∂(L.muPrim l) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hF_zero).symm
  change (∫ h : ℝ, F h ∂(L.muLC (l : ℤ))) =
    L.leadingTwistCoeff l * ∫ h : ℝ, F h ∂(L.muPrim l)
  rw [h_rest1, h_rest2, L.muLC_restrict_leadingTwist l hl, integral_smul_measure,
    ENNReal.toReal_ofReal (L.leadingTwistCoeff_pos l).le, smul_eq_mul]

/-- **Direct Extraction of Primary Measure Pairing on the Leading-Twist Window ($M = 0$)**:
For any spin $l \ge 1$ and any test function $\varphi : \mathbb{R} \to \mathbb{R}$ vanishing on
$[h_{\text{gap}} + 1, \infty)$ and on $(-\infty, 0)$, dividing $\varphi(h)$ by
$\operatorname{transmuteWeight}(h + l)$ inside `toTransmutedMonomialFourPointData.pairSpin` recovers
$C_{0, l} \int_{\mathbb{R}} \varphi(h) \, d\mu^{\text{prim}}_l(h)$! -/
theorem primary_pair_eq_toTransmuted_pair_div
    {l : ℕ} (hl : 1 ≤ l) {φ : ℝ → ℝ}
    (hφ_supp_hi : ∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0)
    (hφ_supp_lo : ∀ h : ℝ, h < 0 → φ h = 0) :
    L.leadingTwistCoeff l * (∫ h : ℝ, φ h ∂(L.muPrim l)) =
      L.toTransmutedMonomialFourPointData.pairSpin (l : ℤ)
        (fun h => φ h / transmuteWeight (h + (l : ℝ))) := by
  symm
  rw [L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist hl (by
    intro h hh
    rw [hφ_supp_hi h hh, zero_div])]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp
  by_cases hh : h < 0
  · rw [hφ_supp_lo h hh, zero_div, mul_zero]
  · have hh0 : 0 ≤ h := not_lt.mp hh
    have hl_real : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    have h_gt : 1 / 2 < h + (l : ℝ) := by linarith
    exact mul_div_cancel₀ (φ h) (transmuteWeight_pos h_gt).ne'

end LightconeBlockFourPointData

end CFT.LightconeBootstrap
