/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Transmute1d
import CFT.LightconeBootstrap.MonomialDecomp

/-!
# Lightcone Conformal Block Decomposition and Transmuted Monomial Data

This file formalizes the action of the 1D fractional transmutation operator on lightcone conformal
blocks and constructs the associated transmuted monomial four-point data:
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
2. **`LightconeBlockFourPointData` & `toTransmutedMonomialFourPointData`**:
   We package the 1D lightcone-block spectral decomposition of a four-point function into
   `LightconeBlockFourPointData` (consisting of a single family of 1D collinear block measures
   `muLC : ℤ → Measure ℝ` and a twist gap `h_gap : ℝ`) and construct its transmuted
   `MonomialFourPointData` (`toTransmutedMonomialFourPointData`,
   `pairSpin_toTransmutedMonomialFourPointData`), as well as the canonical pushforward
   constructions `FourPointData.primaryTwistMeasure` and `FourPointData.lightconeMeasure` from
   the $d$-dimensional primary OPE measure `corr.mu_measure`.
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

/-! ## Section 2: `LightconeBlockFourPointData` & Transmuted `MonomialFourPointData` -/

/-- **Lightcone-Block Four-Point Data**:
packages the 1D lightcone-block spectral measures $\mu^{\text{LC}}_J$ ($J \in \mathbb{Z}$) and the
twist gap $h_{\text{gap}} > 0$ of a four-point correlation function on $\operatorname{UcPdisk}$,
together with:
1. Unitarity ($h \ge 0, \bar{h} = h + J \ge 0$) and Bose symmetry ($\mu^{\text{LC}}_J = 0$ for
   odd $J$),
2. Integrability and spin-summability of the transmuted monomial expansion on the negative real
   half-lines $\sigma_l < 0, \sigma_r < 0$. -/
structure LightconeBlockFourPointData where
  /-- 1D lightcone-block spectral measure $\mu^{\text{LC}}_J$ over left twist $h \in \mathbb{R}$ at
  spin $J = \bar{h} - h \in \mathbb{Z}$. -/
  muLC : ℤ → Measure ℝ

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

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- The spin-$J$ transmuted spectral measure
$$
d\mu^{\text{trans}}_J(h) :=
  \operatorname{transmutePosWeight}(h + J) \, d\mu^{\text{LC}}_J(h).
$$ -/
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
$$
\int_{\mathbb{R}} \varphi(h) \, d\mu^{\text{trans}}_J(h) =
  \int_{\mathbb{R}} \operatorname{transmuteWeight}(h + J) \,
    \varphi(h) \, d\mu^{\text{LC}}_J(h).
$$ -/
theorem pairSpin_toTransmutedMonomialFourPointData {J : ℤ} (hJ : 1 ≤ J) (φ : ℝ → ℝ) :
    L.toTransmutedMonomialFourPointData.pairSpin J φ =
      ∫ h : ℝ, transmuteWeight (h + (J : ℝ)) * φ h ∂(L.muLC J) := by
  dsimp [MonomialFourPointData.pairSpin, toTransmutedMonomialFourPointData]
  rw [L.integral_transmutedMeasure]
  refine integral_congr_ae ?_
  filter_upwards [L.ae_transmutePosWeight_eq_transmuteWeight hJ] with h hh
  simp [smul_eq_mul, hh]

end LightconeBlockFourPointData

/-! ## Section 3: Canonical Pushforward Measures from `FourPointData` -/

/-- Index pair $q = (m, k_r) \in \mathbb{N} \times \mathbb{N}$ for the lightcone conformal block
expansion: left-moving twist level $m$ and right-moving shift index $k_r$. -/
abbrev LightconeIdx : Type := ℕ × ℕ

/-- 1D collinear spin $J = k_r - m \in \mathbb{Z}$ associated to lightcone index $q = (m, k_r)$. -/
def lightconeIdxSpin (q : LightconeIdx) : ℤ :=
  (q.2 : ℤ) - (q.1 : ℤ)

/-- Left scaling weight $h'(\Delta, l) = \frac{\Delta - l}{2} + m$ associated to lightcone level
$m \in \mathbb{N}$ at primary $p = (\Delta, l)$. -/
noncomputable def lightconeIdxWeight (m : ℕ) (p : ℝ × ℕ) : ℝ :=
  (p.1 - (p.2 : ℝ)) / 2 + (m : ℝ)

lemma measurable_lightconeIdxWeight (m : ℕ) :
    Measurable (lightconeIdxWeight m) := by
  unfold lightconeIdxWeight
  fun_prop

lemma transmuteCoreWeight_pos {H : ℝ} (hH : 1 / 2 < H) :
    0 < transmuteCoreWeight H :=
  div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith))

/-- Upper bound `transmuteWeight H ≤ transmuteCoreWeight (3 / 2) * H ^ 2` for $H > 1/2$,
obtained from the Beta integral representation `integral_betaKernel`. -/
lemma transmuteWeight_le_const_mul_sq {H : ℝ} (hH : 1 / 2 < H) :
    transmuteWeight H ≤ transmuteCoreWeight (3 / 2) * H ^ 2 := by
  have hH_pos : 0 < H := by linarith
  have hH_sub_pos : 0 < H - 1 / 2 := by linarith
  have h32 : (1 / 2 : ℝ) < 3 / 2 := by norm_num
  have h_beta1 := integral_betaKernel hH 1
  simp only [realPochhammer_succ, realPochhammer_zero, one_mul, Nat.cast_zero, add_zero] at h_beta1
  have h_beta0 := integral_betaKernel h32 0
  simp only [realPochhammer_zero, div_one, mul_one] at h_beta0
  have h_le_int :
      (∫ s in Ioo (0 : ℝ) 1, betaKernel H 1 s) ≤
        ∫ s in Ioo (0 : ℝ) 1, betaKernel (3 / 2) 0 s := by
    refine setIntegral_mono_on (integrableOn_betaKernel hH 1) (integrableOn_betaKernel h32 0)
      measurableSet_Ioo fun s hs => ?_
    dsimp [betaKernel]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (sub_pos.mpr hs.2).le _)
    exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)
  rw [h_beta1, h_beta0] at h_le_int
  have h_sqrt_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h_core_le :
      transmuteCoreWeight H * ((H - 1 / 2) / H) ≤ transmuteCoreWeight (3 / 2) := by
    nlinarith
  have h_tw := transmuteWeight_eq_mul_transmuteCoreWeight hH
  have h_alg :
      transmuteWeight H = (transmuteCoreWeight H * ((H - 1 / 2) / H)) * (H * (H - 1 / 2)) := by
    rw [h_tw]
    field_simp [hH_pos.ne']
  rw [h_alg]
  have h_core_pos : 0 ≤ transmuteCoreWeight (3 / 2) := (transmuteCoreWeight_pos h32).le
  calc
    (transmuteCoreWeight H * ((H - 1 / 2) / H)) * (H * (H - 1 / 2))
      ≤ transmuteCoreWeight (3 / 2) * (H * (H - 1 / 2)) :=
        mul_le_mul_of_nonneg_right h_core_le (by positivity)
    _ ≤ transmuteCoreWeight (3 / 2) * H ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ h_core_pos
        nlinarith

/-- Non-negative bound `transmutePosWeight H ≤ transmuteCoreWeight (3 / 2) * H ^ 2` for all
$H \in \mathbb{R}$. -/
lemma transmutePosWeight_le_const_mul_sq (H : ℝ) :
    transmutePosWeight H ≤ transmuteCoreWeight (3 / 2) * H ^ 2 := by
  dsimp [transmutePosWeight]
  split_ifs with hH
  · exact transmuteWeight_le_const_mul_sq hH
  · have h32 : (1 / 2 : ℝ) < 3 / 2 := by norm_num
    have h_pos : 0 ≤ transmuteCoreWeight (3 / 2) := (transmuteCoreWeight_pos h32).le
    positivity

/-- Domination of `transmutePosWeight H * Real.exp (H * σr)` by `Real.exp (H * (σr / 2))` for
$H \ge 0$ and $\sigma_r < 0$. -/
lemma transmutePosWeight_mul_exp_le {H σr : ℝ} (hH : 0 ≤ H) (hσr : σr < 0) :
    transmutePosWeight H * Real.exp (H * σr) ≤
      (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) * Real.exp (H * (σr / 2)) := by
  have hσr_ne : σr ≠ 0 := hσr.ne
  have hσr2_pos : 0 < σr ^ 2 := sq_pos_of_ne_zero hσr_ne
  have hx_nonneg : 0 ≤ H * (-σr / 2) := by nlinarith
  have h_exp_le := Real.pow_div_factorial_le_exp (H * (-σr / 2)) hx_nonneg 2
  have h_fac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  rw [h_fac] at h_exp_le
  have h_H2_le : H ^ 2 ≤ (8 / σr ^ 2) * Real.exp (H * (-σr / 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hσr2_pos]
    have h1 := mul_le_mul_of_nonneg_right h_exp_le (by norm_num : (0 : ℝ) ≤ 8)
    have h2 : (H * (-σr / 2)) ^ 2 / 2 * 8 = H ^ 2 * σr ^ 2 := by ring
    linarith
  have h32 : (1 / 2 : ℝ) < 3 / 2 := by norm_num
  have h_core_nonneg : 0 ≤ transmuteCoreWeight (3 / 2) := (transmuteCoreWeight_pos h32).le
  calc
    transmutePosWeight H * Real.exp (H * σr)
      ≤ (transmuteCoreWeight (3 / 2) * H ^ 2) * Real.exp (H * σr) :=
        mul_le_mul_of_nonneg_right (transmutePosWeight_le_const_mul_sq H) (Real.exp_pos _).le
    _ ≤ (transmuteCoreWeight (3 / 2) * ((8 / σr ^ 2) * Real.exp (H * (-σr / 2)))) *
          Real.exp (H * σr) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_H2_le h_core_nonneg) (Real.exp_pos _).le
    _ = (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
          (Real.exp (H * (-σr / 2)) * Real.exp (H * σr)) := by ring
    _ = (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) * Real.exp (H * (σr / 2)) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- For $H \ge 0$ and real $\sigma_r < 0$, the leading ($n = 0$) exponential `Real.exp (H * σr)` is
bounded above by `(block1d H (σr : ℂ)).re`, and `(block1d H (σr : ℂ)).im = 0`. -/
lemma exp_le_re_block1d_of_nonneg {H σr : ℝ} (hH : 0 ≤ H) (hσr : σr < 0) :
    Real.exp (H * σr) ≤ (block1d H (σr : ℂ)).re ∧ (block1d H (σr : ℂ)).im = 0 := by
  have hσr_re : (σr : ℂ).re < 0 := by simpa using hσr
  have h_sum_c := summable_block1d hH hσr_re
  have h_term_eq : ∀ n : ℕ,
      (block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (σr : ℂ)) =
        ((block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * σr) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have h_sum_r : Summable (fun n : ℕ =>
      block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * σr)) := by
    have h1 := Complex.reCLM.summable h_sum_c
    refine h1.congr fun n => ?_
    change ((block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (σr : ℂ))).re = _
    rw [h_term_eq n, Complex.ofReal_re]
  have h_block_eq :
      block1d H (σr : ℂ) =
        ((∑' n : ℕ, block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * σr) : ℝ) : ℂ) := by
    dsimp [block1d]
    simp_rw [h_term_eq]
    rw [Complex.ofReal_tsum]
  rw [h_block_eq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have h0 : Real.exp (H * σr) = block1dCoeff H 0 * Real.exp ((H + 2 * ((0 : ℕ) : ℝ)) * σr) := by
    simp
  rw [h0]
  exact h_sum_r.le_tsum 0 fun n _ => mul_nonneg (block1dCoeff_nonneg hH n) (Real.exp_pos _).le

lemma continuous_realPochhammer_local (n : ℕ) :
    Continuous (fun x : ℝ => realPochhammer x n) := by
  induction n with
  | zero => simp [realPochhammer_zero, continuous_const]
  | succ m ih =>
    have h_eq : (fun x : ℝ => realPochhammer x (m + 1)) =
        fun x : ℝ => realPochhammer x m * (x + (m : ℝ)) := by
      ext x; exact realPochhammer_succ x m
    rw [h_eq]
    exact ih.mul (continuous_id.add continuous_const)

lemma measurable_block1dCoeff_local (n : ℕ) :
    Measurable (fun h : ℝ => block1dCoeff h n) := by
  unfold block1dCoeff
  have h1 : Measurable (fun h : ℝ => realPochhammer h n) :=
    (continuous_realPochhammer_local n).measurable
  have h2 : Measurable (fun h : ℝ => realPochhammer (h + 1 / 2) n) :=
    ((continuous_realPochhammer_local n).comp (continuous_id.add continuous_const)).measurable
  exact (h1.mul measurable_const).div (h2.mul measurable_const)

/-- Non-negative weight truncation of `block1d H w`, equal to `block1d H w` for $H \ge 0$ and $0$ for
$H < 0$. -/
noncomputable def block1dPos (H : ℝ) (w : ℂ) : ℂ :=
  if 0 ≤ H then block1d H w else 0

lemma block1dPos_of_nonneg {H : ℝ} (hH : 0 ≤ H) (w : ℂ) :
    block1dPos H w = block1d H w :=
  if_pos hH

lemma measurable_block1dPos {w : ℂ} (hw : w ∈ UcDisk) :
    Measurable (fun H : ℝ => block1dPos H w) := by
  have hw_re : w.re < 0 := hw
  let seq : ℕ → ℝ → ℂ := fun N H =>
    if 0 ≤ H then
      ∑ n ∈ Finset.range N, (block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * w)
    else 0
  refine measurable_of_tendsto_metrizable (f := seq) (fun N : ℕ => ?_)
    (tendsto_pi_nhds.mpr fun H => ?_)
  · refine Measurable.ite measurableSet_Ici ?_ measurable_const
    refine Finset.measurable_sum (Finset.range N) fun n _ => ?_
    have h1 : Measurable (fun H : ℝ => (block1dCoeff H n : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (measurable_block1dCoeff_local n)
    have h2 : Measurable (fun H : ℝ => Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * w)) := by
      fun_prop
    exact h1.mul h2
  · dsimp [seq, block1dPos]
    split_ifs with hH
    · exact (summable_block1d hH hw_re).hasSum.tendsto_sum_nat
    · exact tendsto_const_nhds

lemma norm_block1d_le_re_of_nonneg {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk) :
    ‖block1d H w‖ ≤ (block1d H (w.re : ℂ)).re := by
  have hw_re : w.re < 0 := hw
  have hwr_re : (w.re : ℂ).re < 0 := by simpa using hw_re
  have h_sum_c := summable_block1d hH hw_re
  have h_term_eq : ∀ n : ℕ,
      (block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (w.re : ℂ)) =
        ((block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * w.re) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have h_sum_r : Summable (fun n : ℕ =>
      block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * w.re)) := by
    have h1 := Complex.reCLM.summable (summable_block1d hH hwr_re)
    refine h1.congr fun n => ?_
    change ((block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (w.re : ℂ))).re = _
    rw [h_term_eq n, Complex.ofReal_re]
  have h_block_eq :
      (block1d H (w.re : ℂ)).re =
        ∑' n : ℕ, block1dCoeff H n * Real.exp ((H + 2 * (n : ℝ)) * w.re) := by
    dsimp [block1d]
    simp_rw [h_term_eq]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [h_block_eq]
  dsimp [block1d]
  refine (norm_tsum_le_tsum_norm h_sum_c.norm).trans
    (h_sum_c.norm.tsum_le_tsum (fun n => ?_) h_sum_r)
  rw [norm_mul, Complex.norm_of_nonneg (block1dCoeff_nonneg hH n), Complex.norm_exp]
  simp [Complex.mul_re]

lemma MonomialFourPointData.HasLowerTwist.laplaceSpinReal_le
    {M : MonomialFourPointData} {h_gap : ℝ} (hlow : M.HasLowerTwist h_gap)
    {σ : ℝ} (hσ : σ ≤ -1) (J : ℤ) :
    M.laplaceSpinReal J σ ≤
      Real.exp (h_gap * (σ + 1)) * M.laplaceSpinReal J (-1) := by
  have hσ_neg : σ < 0 := by linarith
  dsimp [MonomialFourPointData.laplaceSpinReal]
  rw [← integral_const_mul]
  refine integral_mono_ae (M.integrable_exp_real hσ_neg J)
    ((M.integrable_exp_real (by norm_num) J).const_mul _) ?_
  have h_ae : ∀ᶠ h : ℝ in ae (M.mu J), h ∉ { h : ℝ | h < h_gap ∨ h + (J : ℝ) < h_gap } :=
    compl_mem_ae_iff.mpr (hlow.support_gap J)
  filter_upwards [h_ae] with h hh
  have hh1 : h_gap ≤ h := not_lt.mp (fun hlt => hh (Or.inl hlt))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h_mul : h * (σ + 1) ≤ h_gap * (σ + 1) :=
    mul_le_mul_of_nonpos_right hh1 (by linarith)
  linarith

lemma MonomialFourPointData.laplaceSpinReal_eq_ite_add_of_eval_eq_one_add
    (M rem : MonomialFourPointData)
    (heval : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk → M.eval wl wr = 1 + rem.eval wl wr)
    (J : ℤ) {σ : ℝ} (hσ : σ < 0) :
    M.laplaceSpinReal J σ = (if J = 0 then 1 else 0) + rem.laplaceSpinReal J σ := by
  set w : ℂ := ((σ / 2 : ℝ) : ℂ)
  have hw : w ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    simpa [w] using (by linarith : σ / 2 < 0)
  have hww : w + w = (σ : ℂ) := by
    dsimp [w]
    push_cast
    ring
  have hM := M.laplaceSpin_eq_fourierProjSpinFull J hw hw
  have hrem := rem.laplaceSpin_eq_fourierProjSpinFull J hw hw
  rw [hww, M.laplaceSpin_ofReal] at hM
  rw [hww, rem.laplaceSpin_ofReal] at hrem
  have h_int_eq : ∀ θ : ℝ,
      M.fourierIntegrand J w w θ =
        Complex.exp (- (J : ℂ) * (w + (θ : ℂ) * I)) + rem.fourierIntegrand J w w θ := by
    intro θ
    dsimp [MonomialFourPointData.fourierIntegrand]
    rw [heval (sub_I_mul_mem_UcDisk hw θ) (add_I_mul_mem_UcDisk hw θ), mul_add, mul_one]
  have h_cont_exp :
      Continuous (fun θ : ℝ => Complex.exp (- (J : ℂ) * (w + (θ : ℂ) * I))) := by
    fun_prop
  have h_split :
      M.fourierProjSpinFull J w w =
        (2 * π : ℂ)⁻¹ * (∫ θ in (-π)..π, Complex.exp (- (J : ℂ) * (w + (θ : ℂ) * I))) +
          rem.fourierProjSpinFull J w w := by
    dsimp [MonomialFourPointData.fourierProjSpinFull]
    simp_rw [h_int_eq]
    rw [intervalIntegral.integral_add
      (h_cont_exp.intervalIntegrable _ _)
      ((rem.continuous_fourierIntegrand J hw hw).intervalIntegrable _ _),
      mul_add]
  have h_exp_int :
      (2 * π : ℂ)⁻¹ * (∫ θ in (-π)..π, Complex.exp (- (J : ℂ) * (w + (θ : ℂ) * I))) =
        if J = 0 then 1 else 0 := by
    have h_factor : ∀ θ : ℝ,
        Complex.exp (- (J : ℂ) * (w + (θ : ℂ) * I)) =
          Complex.exp (- (J : ℂ) * w) * Complex.exp (((-J : ℤ) : ℂ) * (θ : ℂ) * I) := by
      intro θ
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [h_factor, intervalIntegral.integral_const_mul, integral_exp_int_mul_I (-J),
      neg_eq_zero]
    split_ifs with hJ
    · subst hJ
      simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
      exact inv_mul_cancel₀
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · simp
  rw [h_exp_int, ← hrem] at h_split
  rw [h_split] at hM
  have h_re := congrArg Complex.re hM
  split_ifs at h_re ⊢ <;> simpa using h_re

lemma measure_Iio_eq_zero_of_lintegral_exp_le (μ : Measure ℝ) {h_gap A : ℝ}
    (hbound : ∀ n : ℕ,
      (∫⁻ h : ℝ, ENNReal.ofReal (Real.exp (h * (-((n : ℝ) + 1)))) ∂μ) ≤
        ENNReal.ofReal (A * Real.exp (-h_gap * (n : ℝ)))) :
    μ (Iio h_gap) = 0 := by
  have h_Iic : ∀ {c : ℝ}, c < h_gap → μ (Iic c) = 0 := by
    intro c hc
    have h_le_n (n : ℕ) :
        μ (Iic c) ≤
          ENNReal.ofReal (A * Real.exp c * Real.exp (-(h_gap - c) * (n : ℝ))) := by
      set σ : ℝ := -((n : ℝ) + 1)
      have hσ : σ < 0 := by dsimp [σ]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have h_exp_pos : 0 < Real.exp (c * σ) := Real.exp_pos _
      have h_mul :
          μ (Iic c) * ENNReal.ofReal (Real.exp (c * σ)) ≤
            ENNReal.ofReal (A * Real.exp (-h_gap * (n : ℝ))) := by
        calc
          μ (Iic c) * ENNReal.ofReal (Real.exp (c * σ))
            = ∫⁻ _ in Iic c, ENNReal.ofReal (Real.exp (c * σ)) ∂μ := by
              rw [setLIntegral_const, mul_comm]
          _ ≤ ∫⁻ h in Iic c, ENNReal.ofReal (Real.exp (h * σ)) ∂μ :=
              setLIntegral_mono' measurableSet_Iic fun h (hh : h ≤ c) =>
                ENNReal.ofReal_le_ofReal
                  (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hh hσ.le))
          _ ≤ ∫⁻ h, ENNReal.ofReal (Real.exp (h * σ)) ∂μ :=
              lintegral_mono' Measure.restrict_le_self le_rfl
          _ ≤ ENNReal.ofReal (A * Real.exp (-h_gap * (n : ℝ))) := hbound n
      calc
        μ (Iic c)
          = (μ (Iic c) * ENNReal.ofReal (Real.exp (c * σ))) *
              ENNReal.ofReal (Real.exp (- (c * σ))) := by
            rw [mul_assoc, ← ENNReal.ofReal_mul h_exp_pos.le, ← Real.exp_add,
              add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, mul_one]
        _ ≤ ENNReal.ofReal (A * Real.exp (-h_gap * (n : ℝ))) *
              ENNReal.ofReal (Real.exp (- (c * σ))) := by
            gcongr
        _ = ENNReal.ofReal (A * Real.exp c * Real.exp (-(h_gap - c) * (n : ℝ))) := by
            rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
            congr 1
            dsimp [σ]
            rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 2
            ring
    have h_tendsto :
        Tendsto (fun n : ℕ =>
          ENNReal.ofReal (A * Real.exp c * Real.exp (-(h_gap - c) * (n : ℝ))))
          atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h_exp0 :
          Tendsto (fun n : ℕ => Real.exp (-(h_gap - c) * (n : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_natCast_atTop_atTop)
      simpa using h_exp0.const_mul (A * Real.exp c)
    exact nonpos_iff_eq_zero.mp (ge_of_tendsto' h_tendsto h_le_n)
  have h_sub : Iio h_gap ⊆ ⋃ k : ℕ, Iic (h_gap - 1 / ((k : ℝ) + 1)) := by
    intro x (hx : x < h_gap)
    rw [mem_iUnion]
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (h_gap - x))
    refine ⟨k, ?_⟩
    have h_pos : 0 < h_gap - x := sub_pos.mpr hx
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h_lt : 1 / ((k : ℝ) + 1) < h_gap - x := by
      rw [div_lt_iff₀ hk_pos]
      have h1 : 1 < (k : ℝ) * (h_gap - x) := (div_lt_iff₀ h_pos).mp hk
      nlinarith
    rw [mem_Iic]
    linarith
  exact measure_mono_null h_sub
    (measure_iUnion_null fun k => h_Iic (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith))

lemma MonomialFourPointData.HasTwistGap.mu_props
    {M : MonomialFourPointData} {h_gap : ℝ} (hgap : M.HasTwistGap h_gap) :
    M.mu 0 {0} = 1 ∧
    M.mu 0 (Iio h_gap \ {0}) = 0 ∧
    ∀ J : ℤ, J ≠ 0 → M.mu J (Iio h_gap) = 0 := by
  rcases hgap with ⟨rem, hlow, heval, _⟩
  have hh_gap : 0 < h_gap := hlow.h_gap_pos
  have h_lap (J : ℤ) (n : ℕ) :
      M.laplaceSpinReal J (-((n : ℝ) + 1)) =
        (if J = 0 then 1 else 0) + rem.laplaceSpinReal J (-((n : ℝ) + 1)) :=
    M.laplaceSpinReal_eq_ite_add_of_eval_eq_one_add rem heval J
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h_rem_le (J : ℤ) (n : ℕ) :
      rem.laplaceSpinReal J (-((n : ℝ) + 1)) ≤
        rem.laplaceSpinReal J (-1) * Real.exp (-h_gap * (n : ℝ)) := by
    have h1 := hlow.laplaceSpinReal_le (by linarith : -((n : ℝ) + 1) ≤ -1) J
    have h_alg : h_gap * (-((n : ℝ) + 1) + 1) = -h_gap * (n : ℝ) := by ring
    rw [h_alg, mul_comm] at h1
    exact h1
  have h_J_ne (J : ℤ) (hJ : J ≠ 0) : M.mu J (Iio h_gap) = 0 := by
    refine measure_Iio_eq_zero_of_lintegral_exp_le (M.mu J) (A := rem.laplaceSpinReal J (-1))
      fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal
      (M.integrable_exp_real (by linarith [Nat.cast_nonneg (α := ℝ) n] : -((n : ℝ) + 1) < 0) J)
      (Eventually.of_forall fun h => (Real.exp_pos _).le)]
    change ENNReal.ofReal (M.laplaceSpinReal J (-((n : ℝ) + 1))) ≤ _
    rw [h_lap J n, if_neg hJ, zero_add]
    exact ENNReal.ofReal_le_ofReal (h_rem_le J n)
  have h_tendsto_M0 :
      Tendsto (fun n : ℕ => M.laplaceSpinReal 0 (-((n : ℝ) + 1)))
        atTop (𝓝 ((M.mu 0 {0}).toReal)) := by
    have h_ind_int :
        (∫ h : ℝ, Set.indicator {(0 : ℝ)} (fun _ => (1 : ℝ)) h ∂(M.mu 0)) =
          (M.mu 0 {0}).toReal := by
      rw [integral_indicator (measurableSet_singleton (0 : ℝ)), setIntegral_const,
        smul_eq_mul, mul_one, Measure.real]
    rw [← h_ind_int]
    refine tendsto_integral_of_dominated_convergence
      (fun h : ℝ => Real.exp (h * (-1)))
      (fun n => by fun_prop)
      (M.integrable_exp_real (by norm_num : (-1 : ℝ) < 0) 0)
      (fun n => ?_) ?_
    · filter_upwards [M.ae_nonneg 0] with h hh
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · filter_upwards [M.ae_nonneg 0] with h hh
      by_cases hh0 : h = 0
      · subst hh0
        simp [Set.indicator_of_mem]
      · have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
        rw [Set.indicator_of_notMem (by simpa using hh0)]
        have h_atBot :
            Tendsto (fun n : ℕ => h * (-((n : ℝ) + 1))) atTop atBot := by
          have h_eq : (fun n : ℕ => h * (-((n : ℝ) + 1))) =
              fun n : ℕ => (-h) * ((n : ℝ) + 1) := by ext n; ring
          rw [h_eq]
          exact Tendsto.const_mul_atTop_of_neg (by linarith)
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact Real.tendsto_exp_atBot.comp h_atBot
  have h_tendsto_rhs :
      Tendsto (fun n : ℕ => M.laplaceSpinReal 0 (-((n : ℝ) + 1)))
        atTop (𝓝 1) := by
    have h_eq : (fun n : ℕ => M.laplaceSpinReal 0 (-((n : ℝ) + 1))) =
        fun n : ℕ => 1 + rem.laplaceSpinReal 0 (-((n : ℝ) + 1)) := by
      ext n; simpa using h_lap 0 n
    rw [h_eq]
    suffices Tendsto (fun n : ℕ => rem.laplaceSpinReal 0 (-((n : ℝ) + 1))) atTop (𝓝 0) by
      simpa using tendsto_const_nhds.add this
    refine squeeze_zero (fun n => rem.laplaceSpinReal_nonneg 0 _) (fun n => h_rem_le 0 n) ?_
    have h_exp0 :
        Tendsto (fun n : ℕ => Real.exp (-h_gap * (n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_natCast_atTop_atTop)
    simpa using h_exp0.const_mul (rem.laplaceSpinReal 0 (-1))
  have h_toReal_one : (M.mu 0 {0}).toReal = 1 :=
    tendsto_nhds_unique h_tendsto_M0 h_tendsto_rhs
  have h_mu0_one : M.mu 0 {0} = 1 := by
    have h_ne_top : M.mu 0 {0} ≠ ⊤ := by
      intro htop
      rw [htop] at h_toReal_one
      simp at h_toReal_one
    rw [← ENNReal.ofReal_toReal h_ne_top, h_toReal_one, ENNReal.ofReal_one]
  refine ⟨h_mu0_one, ?_, h_J_ne⟩
  have h_diff_eq :
      M.mu 0 (Iio h_gap \ {0}) = ((M.mu 0).restrict {(0 : ℝ)}ᶜ) (Iio h_gap) := by
    rw [Measure.restrict_apply measurableSet_Iio, diff_eq]
  rw [h_diff_eq]
  refine measure_Iio_eq_zero_of_lintegral_exp_le ((M.mu 0).restrict {(0 : ℝ)}ᶜ)
    (A := rem.laplaceSpinReal 0 (-1)) fun n => ?_
  set σ : ℝ := -((n : ℝ) + 1)
  have hσ : σ < 0 := by dsimp [σ]; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (M.integrable_exp_real hσ 0).restrict
    (Eventually.of_forall fun h => (Real.exp_pos _).le)]
  have h_split := integral_add_compl (measurableSet_singleton (0 : ℝ))
    (M.integrable_exp_real hσ 0)
  have h_sing : (∫ h in {(0 : ℝ)}, Real.exp (h * σ) ∂(M.mu 0)) = 1 := by
    have h_congr :
        (∫ h in {(0 : ℝ)}, Real.exp (h * σ) ∂(M.mu 0)) =
          ∫ _ in {(0 : ℝ)}, (1 : ℝ) ∂(M.mu 0) := by
      refine setIntegral_congr_fun (measurableSet_singleton (0 : ℝ)) fun h hh => ?_
      rw [mem_singleton_iff.mp hh, zero_mul, Real.exp_zero]
    rw [h_congr, setIntegral_const, smul_eq_mul, mul_one, Measure.real, h_toReal_one]
  have h_compl :
      (∫ h in {(0 : ℝ)}ᶜ, Real.exp (h * σ) ∂(M.mu 0)) = rem.laplaceSpinReal 0 σ := by
    have h_tot : (∫ h, Real.exp (h * σ) ∂(M.mu 0)) = 1 + rem.laplaceSpinReal 0 σ := by
      simpa [MonomialFourPointData.laplaceSpinReal, σ] using h_lap 0 n
    linarith
  rw [h_compl]
  exact ENNReal.ofReal_le_ofReal (h_rem_le 0 n)

end CFT.LightconeBootstrap

open CFT.LightconeBootstrap

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- Canonical $d$-dimensional primary operator spectral measure $\mu^{\mathrm{prim}}_l$ over
primary left twist $h = (\Delta - l) / 2 \in \mathbb{R}$ at spin $l \in \mathbb{N}$, obtained by
restricting `corr.mu_measure` to primary spin $l$ and pushing forward under
$(\Delta, l') \mapsto (\Delta - l) / 2$. -/
noncomputable def primaryTwistMeasure (l : ℕ) : Measure ℝ :=
  (corr.mu_measure.restrict { p : ℝ × ℕ | p.2 = l }).map
    (fun p : ℝ × ℕ => (p.1 - (l : ℝ)) / 2)

/-- Non-identity primary operator OPE measure obtained by restricting `corr.mu_measure` to the
complement of the identity primary $(0, 0)$. -/
noncomputable def nonIdentityMeasure : Measure (ℝ × ℕ) :=
  corr.mu_measure.restrict {((0 : ℝ), (0 : ℕ))}ᶜ

lemma nonIdentityMeasure_ae_unitary :
    ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure, (p.2 : ℝ) ≤ p.1 :=
  ae_mono Measure.restrict_le_self corr.ae_unitary

lemma nonIdentityMeasure_ae_even_spin :
    ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure, Even p.2 :=
  ae_mono Measure.restrict_le_self corr.ae_even_spin

/-- Lightcone conformal block coefficient $C_{m, k_r}(\nu, \Delta, l)$ at index $q = (m, k_r)$ and
primary $p = (\Delta, l)$. -/
noncomputable def lightconeIdxCoeff (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) : ℝ :=
  (((conformalBlock ν p.1 p.2).toLightcone).level q.1).C q.2

lemma measurable_lightconeIdxCoeff (ν : ℝ) (q : LightconeIdx) :
    Measurable (lightconeIdxCoeff ν q) :=
  measurable_conformalBlock_toLightcone_C ν q.1 q.2

lemma lightconeIdxCoeff_nonneg (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) :
    0 ≤ lightconeIdxCoeff ν q p := by
  dsimp [lightconeIdxCoeff]
  set lvl := ((conformalBlock ν p.1 p.2).toLightcone).level q.1
  by_cases hkr : q.2 ∈ lvl.support
  · exact lvl.C_nonneg q.2 hkr
  · rw [lvl.C_support q.2 hkr]

lemma mem_support_of_lightconeIdxCoeff_ne_zero {ν : ℝ} {q : LightconeIdx} {p : ℝ × ℕ}
    (h : lightconeIdxCoeff ν q p ≠ 0) :
    q.2 ∈ (((conformalBlock ν p.1 p.2).toLightcone).level q.1).support := by
  by_contra hnot
  exact h ((((conformalBlock ν p.1 p.2).toLightcone).level q.1).C_support q.2 hnot)

lemma mem_lightconeRightSpins_of_lightconeIdxCoeff_ne_zero {ν : ℝ} {q : LightconeIdx} {p : ℝ × ℕ}
    (h : lightconeIdxCoeff ν q p ≠ 0) :
    q.2 ∈ lightconeRightSpins p.2 q.1 :=
  ((conformalBlock ν p.1 p.2).toLightcone).support_subset q.1
    (mem_support_of_lightconeIdxCoeff_ne_zero h)

/-- Pushforward measure on $h \in \mathbb{R}$ contributed by a single lightcone block index
$q = (m, k_r)$ via the canonical lightcone conformal block decomposition
`(conformalBlock ν p.1 p.2).toLightcone` over non-identity primaries. -/
noncomputable def lightconeAtomMeasure (q : LightconeIdx) : Measure ℝ :=
  (corr.nonIdentityMeasure.withDensity
    (fun p => ENNReal.ofReal (lightconeIdxCoeff ν q p))).map
    (lightconeIdxWeight q.1)

/-- Canonical spin-$J$ 1D lightcone-block spectral measure $\mu^{\mathrm{LC}}_J$ obtained by
summing `corr.lightconeAtomMeasure q` over all lightcone indices $q = (m, k_r)$ with
$k_r - m = J$. -/
noncomputable def lightconeMeasure (J : ℤ) : Measure ℝ :=
  Measure.sum (fun q : LightconeIdx =>
    if lightconeIdxSpin q = J then corr.lightconeAtomMeasure q else 0)

/-- Characterization of Bochner integrability with respect to `corr.lightconeAtomMeasure q`. -/
lemma integrable_lightconeAtomMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : LightconeIdx) {f : ℝ → E} (hf : AEStronglyMeasurable f (corr.lightconeAtomMeasure q)) :
    Integrable f (corr.lightconeAtomMeasure q) ↔
      Integrable (fun p => lightconeIdxCoeff ν q p • f (lightconeIdxWeight q.1 p))
        corr.nonIdentityMeasure := by
  dsimp [lightconeAtomMeasure]
  rw [integrable_map_measure hf (measurable_lightconeIdxWeight q.1).aemeasurable]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_lightconeIdxCoeff ν q).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  dsimp [Function.comp_def]
  rw [ENNReal.toReal_ofReal (lightconeIdxCoeff_nonneg ν q p)]

/-- Change-of-variables formula for the Bochner integral against `corr.lightconeAtomMeasure q`. -/
lemma integral_lightconeAtomMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : LightconeIdx) {f : ℝ → E} (hf : AEStronglyMeasurable f (corr.lightconeAtomMeasure q)) :
    ∫ h, f h ∂(corr.lightconeAtomMeasure q) =
      ∫ p, lightconeIdxCoeff ν q p • f (lightconeIdxWeight q.1 p) ∂corr.nonIdentityMeasure := by
  dsimp [lightconeAtomMeasure]
  rw [integral_map (measurable_lightconeIdxWeight q.1).aemeasurable hf]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_lightconeIdxCoeff ν q).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp
  rw [ENNReal.toReal_ofReal (lightconeIdxCoeff_nonneg ν q p)]

/-- Unitarity support of `corr.lightconeMeasure J`. -/
lemma lightconeMeasure_support_unitary (J : ℤ) :
    corr.lightconeMeasure J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0 := by
  let S : Set ℝ := { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 }
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_id measurable_const).union
      (measurableSet_lt (measurable_id.add measurable_const) measurable_const)
  change corr.lightconeMeasure J S = 0
  dsimp [lightconeMeasure]
  rw [Measure.sum_apply _ hS, ENNReal.tsum_eq_zero]
  intro q
  split_ifs with hJ
  · dsimp [lightconeAtomMeasure]
    rw [Measure.map_apply (measurable_lightconeIdxWeight q.1) hS,
      withDensity_apply _ ((measurable_lightconeIdxWeight q.1) hS),
      setLIntegral_eq_zero_iff ((measurable_lightconeIdxWeight q.1) hS)
        ((measurable_lightconeIdxCoeff ν q).ennreal_ofReal)]
    filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp h_mem
    rw [ENNReal.ofReal_eq_zero]
    refine le_of_eq ?_
    by_contra h_ne
    have hq1 : (0 : ℝ) ≤ (q.1 : ℝ) := Nat.cast_nonneg _
    have hq2 : (0 : ℝ) ≤ (q.2 : ℝ) := Nat.cast_nonneg _
    have hJ_real : (J : ℝ) = (q.2 : ℝ) - (q.1 : ℝ) := by
      rw [← hJ]
      dsimp [lightconeIdxSpin]
      push_cast
      ring
    rcases h_mem with h_lt | h_lt
    · dsimp [lightconeIdxWeight] at h_lt
      linarith
    · dsimp [lightconeIdxWeight] at h_lt
      linarith
  · simp

/-- Bose symmetry of `corr.lightconeMeasure J`: odd spins $J$ have vanishing measure. -/
lemma lightconeMeasure_support_odd_spin (J : ℤ) (hJ : Odd J) :
    corr.lightconeMeasure J = 0 := by
  dsimp [lightconeMeasure]
  have h_zero : (fun q : LightconeIdx =>
      if lightconeIdxSpin q = J then corr.lightconeAtomMeasure q else 0) =
      fun _ => (0 : Measure ℝ) := by
    ext q S hS
    simp only [Measure.coe_zero]
    split_ifs with hqJ
    · dsimp [lightconeAtomMeasure]
      rw [Measure.map_apply (measurable_lightconeIdxWeight q.1) hS,
        withDensity_apply _ ((measurable_lightconeIdxWeight q.1) hS),
        setLIntegral_eq_zero_iff ((measurable_lightconeIdxWeight q.1) hS)
          ((measurable_lightconeIdxCoeff ν q).ennreal_ofReal)]
      filter_upwards [corr.nonIdentityMeasure_ae_even_spin] with p hp_even _
      rw [ENNReal.ofReal_eq_zero]
      refine le_of_eq ?_
      by_contra h_ne
      obtain ⟨s, _, h2s, hkr⟩ :=
        mem_lightconeRightSpins.mp (mem_lightconeRightSpins_of_lightconeIdxCoeff_ne_zero h_ne)
      have hJ_even : Even J := by
        rcases hp_even with ⟨k', hk'⟩
        refine ⟨(k' : ℤ) - (s : ℤ), ?_⟩
        rw [← hqJ]
        dsimp [lightconeIdxSpin]
        omega
      exact Int.not_odd_iff_even.mpr hJ_even hJ
    · rfl
  rw [h_zero, Measure.sum_zero]

/-- Vanishing of `corr.lightconeMeasure J` for negative spins $J < 0$. -/
lemma lightconeMeasure_eq_zero_of_neg (J : ℤ) (hJ : J < 0) :
    corr.lightconeMeasure J = 0 := by
  dsimp [lightconeMeasure]
  have h_zero : (fun q : LightconeIdx =>
      if lightconeIdxSpin q = J then corr.lightconeAtomMeasure q else 0) =
      fun _ => (0 : Measure ℝ) := by
    ext q S hS
    simp only [Measure.coe_zero]
    split_ifs with hqJ
    · dsimp [lightconeAtomMeasure]
      rw [Measure.map_apply (measurable_lightconeIdxWeight q.1) hS,
        withDensity_apply _ ((measurable_lightconeIdxWeight q.1) hS),
        setLIntegral_eq_zero_iff ((measurable_lightconeIdxWeight q.1) hS)
          ((measurable_lightconeIdxCoeff ν q).ennreal_ofReal)]
      filter_upwards with p _
      rw [ENNReal.ofReal_eq_zero]
      refine le_of_eq ?_
      by_contra h_ne
      obtain ⟨s, _, h2s, hkr⟩ :=
        mem_lightconeRightSpins.mp (mem_lightconeRightSpins_of_lightconeIdxCoeff_ne_zero h_ne)
      have hJ_nonneg : 0 ≤ J := by
        rw [← hqJ]
        dsimp [lightconeIdxSpin]
        omega
      omega
    · rfl
  rw [h_zero, Measure.sum_zero]

/-- Real untransmuted monomial contribution of lightcone index $q = (m, k_r)$ at primary $p$. -/
noncomputable def lightconeIdxRealTerm (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) (p : ℝ × ℕ) : ℝ :=
  lightconeIdxCoeff ν q p *
    monomialTermReal (lightconeIdxWeight q.1 p) (lightconeIdxSpin q) σl σr

/-- Real transmuted monomial contribution of lightcone index $q = (m, k_r)$ at primary $p$. -/
noncomputable def lightconeIdxTransmuteRealTerm
    (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) (p : ℝ × ℕ) : ℝ :=
  transmutePosWeight (lightconeIdxWeight q.1 p + (lightconeIdxSpin q : ℝ)) *
    lightconeIdxRealTerm ν q σl σr p

lemma lightconeIdxRealTerm_nonneg (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) (p : ℝ × ℕ) :
    0 ≤ lightconeIdxRealTerm ν q σl σr p :=
  mul_nonneg (lightconeIdxCoeff_nonneg ν q p)
    (monomialTermReal_nonneg (lightconeIdxWeight q.1 p) (lightconeIdxSpin q) σl σr)

lemma lightconeIdxTransmuteRealTerm_nonneg (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) (p : ℝ × ℕ) :
    0 ≤ lightconeIdxTransmuteRealTerm ν q σl σr p :=
  mul_nonneg (transmutePosWeight_nonneg _) (lightconeIdxRealTerm_nonneg ν q σl σr p)

lemma measurable_lightconeIdxRealTerm (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) :
    Measurable (lightconeIdxRealTerm ν q σl σr) := by
  unfold lightconeIdxRealTerm monomialTermReal
  refine (measurable_lightconeIdxCoeff ν q).mul ?_
  have h_w := measurable_lightconeIdxWeight q.1
  fun_prop

lemma measurable_lightconeIdxTransmuteRealTerm (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) :
    Measurable (lightconeIdxTransmuteRealTerm ν q σl σr) := by
  unfold lightconeIdxTransmuteRealTerm
  refine (measurable_transmutePosWeight.comp
    ((measurable_lightconeIdxWeight q.1).add measurable_const)).mul
    (measurable_lightconeIdxRealTerm ν q σl σr)

/-- Real 1D-block contribution of lightcone index $q = (m, k_r)$ at primary $p$. -/
noncomputable def lightconeIdxBlockRealTerm
    (ν : ℝ) (q : LightconeIdx) (σl σr : ℝ) (p : ℝ × ℕ) : ℝ :=
  lightconeIdxCoeff ν q p *
    Real.exp (blockExp p.1 p.2 q.1 * σl) * (block1d (blockExp p.1 p.2 q.2) (σr : ℂ)).re

lemma lightconeIdxWeight_eq_blockExp (m : ℕ) (p : ℝ × ℕ) :
    lightconeIdxWeight m p = blockExp p.1 p.2 m := rfl

lemma lightconeIdxWeight_add_spin_eq_blockExp (q : LightconeIdx) (p : ℝ × ℕ) :
    lightconeIdxWeight q.1 p + (lightconeIdxSpin q : ℝ) = blockExp p.1 p.2 q.2 := by
  dsimp [lightconeIdxWeight, lightconeIdxSpin, blockExp]
  push_cast
  ring

lemma blockExp_nonneg {p : ℝ × ℕ} (hp : (p.2 : ℝ) ≤ p.1) (k : ℕ) :
    0 ≤ blockExp p.1 p.2 k := by
  dsimp [blockExp]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma lightconeIdxBlockRealTerm_nonneg {σl σr : ℝ} (hσr : σr < 0)
    (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    0 ≤ lightconeIdxBlockRealTerm ν q σl σr p := by
  dsimp [lightconeIdxBlockRealTerm]
  have h_re := (exp_le_re_block1d_of_nonneg (blockExp_nonneg hp q.2) hσr).1
  have h_re_nonneg : 0 ≤ (block1d (blockExp p.1 p.2 q.2) (σr : ℂ)).re :=
    (Real.exp_pos _).le.trans h_re
  exact mul_nonneg (mul_nonneg (lightconeIdxCoeff_nonneg ν q p) (Real.exp_pos _).le) h_re_nonneg

lemma lightconeIdxRealTerm_le_blockRealTerm {σl σr : ℝ} (hσr : σr < 0)
    (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    lightconeIdxRealTerm ν q σl σr p ≤ lightconeIdxBlockRealTerm ν q σl σr p := by
  dsimp [lightconeIdxRealTerm, lightconeIdxBlockRealTerm, monomialTermReal]
  rw [lightconeIdxWeight_add_spin_eq_blockExp, lightconeIdxWeight_eq_blockExp, Real.exp_add,
    ← mul_assoc]
  refine mul_le_mul_of_nonneg_left
    (exp_le_re_block1d_of_nonneg (blockExp_nonneg hp q.2) hσr).1 ?_
  exact mul_nonneg (lightconeIdxCoeff_nonneg ν q p) (Real.exp_pos _).le

lemma lightconeIdxTransmuteRealTerm_le_const_mul_realTerm_half {σl σr : ℝ} (hσr : σr < 0)
    (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    lightconeIdxTransmuteRealTerm ν q σl σr p ≤
      (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
        lightconeIdxRealTerm ν q σl (σr / 2) p := by
  dsimp [lightconeIdxTransmuteRealTerm, lightconeIdxRealTerm, monomialTermReal]
  rw [lightconeIdxWeight_add_spin_eq_blockExp, lightconeIdxWeight_eq_blockExp,
    Real.exp_add, Real.exp_add]
  have h_bound := transmutePosWeight_mul_exp_le (blockExp_nonneg hp q.2) hσr
  have h_rearr1 :
      transmutePosWeight (blockExp p.1 p.2 q.2) *
        (lightconeIdxCoeff ν q p *
          (Real.exp (blockExp p.1 p.2 q.1 * σl) * Real.exp (blockExp p.1 p.2 q.2 * σr))) =
      (lightconeIdxCoeff ν q p * Real.exp (blockExp p.1 p.2 q.1 * σl)) *
        (transmutePosWeight (blockExp p.1 p.2 q.2) * Real.exp (blockExp p.1 p.2 q.2 * σr)) := by
    ring
  have h_rearr2 :
      (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
        (lightconeIdxCoeff ν q p *
          (Real.exp (blockExp p.1 p.2 q.1 * σl) *
            Real.exp (blockExp p.1 p.2 q.2 * (σr / 2)))) =
      (lightconeIdxCoeff ν q p * Real.exp (blockExp p.1 p.2 q.1 * σl)) *
        ((8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
          Real.exp (blockExp p.1 p.2 q.2 * (σr / 2))) := by
    ring
  rw [h_rearr1, h_rearr2]
  exact mul_le_mul_of_nonneg_left h_bound
    (mul_nonneg (lightconeIdxCoeff_nonneg ν q p) (Real.exp_pos _).le)

lemma summable_lightconeIdxBlockRealTerm_level (ν : ℝ) (m : ℕ) (σl σr : ℝ) (p : ℝ × ℕ) :
    Summable (fun kr : ℕ => lightconeIdxBlockRealTerm ν (m, kr) σl σr p) := by
  refine summable_of_ne_finset_zero
    (s := (((conformalBlock ν p.1 p.2).toLightcone).level m).support) fun kr hkr => ?_
  dsimp [lightconeIdxBlockRealTerm, lightconeIdxCoeff]
  rw [(((conformalBlock ν p.1 p.2).toLightcone).level m).C_support kr hkr, zero_mul, zero_mul]

lemma tsum_lightconeIdxBlockRealTerm_level_eq {σl σr : ℝ} (hσr : σr < 0)
    (ν : ℝ) (m : ℕ) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' kr : ℕ, lightconeIdxBlockRealTerm ν (m, kr) σl σr p) =
      Real.exp (blockExp p.1 p.2 m * σl) *
        ‖(((conformalBlock ν p.1 p.2).toLightcone).level m).eval p.1 p.2 (σr : ℂ)‖ ∧
    Complex.exp ((blockExp p.1 p.2 m : ℂ) * (σl : ℂ)) *
        ((conformalBlock ν p.1 p.2).toLightcone).evalLevel m (σr : ℂ) =
      ((∑' kr : ℕ, lightconeIdxBlockRealTerm ν (m, kr) σl σr p : ℝ) : ℂ) := by
  set L := (conformalBlock ν p.1 p.2).toLightcone
  rw [tsum_eq_sum (s := (L.level m).support) fun kr hkr => by
    dsimp [lightconeIdxBlockRealTerm, lightconeIdxCoeff]
    rw [(L.level m).C_support kr hkr, zero_mul, zero_mul]]
  have h_eval_eq :
      (L.level m).eval p.1 p.2 (σr : ℂ) =
        ((∑ kr ∈ (L.level m).support,
          (L.level m).C kr * (block1d (blockExp p.1 p.2 kr) (σr : ℂ)).re : ℝ) : ℂ) := by
    dsimp [ConformalBlockLightconeLevel.eval]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun kr _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    apply Complex.ext
    · simp
    · simp [(exp_le_re_block1d_of_nonneg (blockExp_nonneg hp kr) hσr).2]
  have h_sum_nonneg :
      0 ≤ ∑ kr ∈ (L.level m).support,
        (L.level m).C kr * (block1d (blockExp p.1 p.2 kr) (σr : ℂ)).re := by
    refine Finset.sum_nonneg fun kr hkr => ?_
    have h_re := (exp_le_re_block1d_of_nonneg (blockExp_nonneg hp kr) hσr).1
    exact mul_nonneg ((L.level m).C_nonneg kr hkr) ((Real.exp_pos _).le.trans h_re)
  have h_norm :
      ‖(L.level m).eval p.1 p.2 (σr : ℂ)‖ =
        ∑ kr ∈ (L.level m).support,
          (L.level m).C kr * (block1d (blockExp p.1 p.2 kr) (σr : ℂ)).re := by
    rw [h_eval_eq, Complex.norm_real, Real.norm_of_nonneg h_sum_nonneg]
  have h_sum_mul :
      (∑ kr ∈ (L.level m).support, lightconeIdxBlockRealTerm ν (m, kr) σl σr p) =
        Real.exp (blockExp p.1 p.2 m * σl) *
          ∑ kr ∈ (L.level m).support,
            (L.level m).C kr * (block1d (blockExp p.1 p.2 kr) (σr : ℂ)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun kr _ => ?_
    dsimp [lightconeIdxBlockRealTerm, lightconeIdxCoeff]
    ring
  refine ⟨by rw [h_sum_mul, h_norm], ?_⟩
  dsimp [ConformalBlockLightcone.evalLevel]
  rw [h_eval_eq, h_sum_mul, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- Summability and evaluation of `lightconeIdxBlockRealTerm` over all $q = (m, k_r)$ at a unitary
primary $p$. -/
lemma summable_and_tsum_lightconeIdxBlockRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : LightconeIdx => lightconeIdxBlockRealTerm ν q σl σr p) ∧
    (∑' q : LightconeIdx, lightconeIdxBlockRealTerm ν q σl σr p) =
      ((conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)).re := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  set L := (conformalBlock ν p.1 p.2).toLightcone
  have h_sum_m : Summable (fun m : ℕ =>
      ∑' kr : ℕ, lightconeIdxBlockRealTerm ν (m, kr) σl σr p) := by
    simp_rw [(tsum_lightconeIdxBlockRealTerm_level_eq hσr ν _ p hp).1]
    exact L.summable_real σl hσl σr hσr
  have h_sum_q : Summable (fun q : LightconeIdx => lightconeIdxBlockRealTerm ν q σl σr p) :=
    (summable_prod_of_nonneg
      (fun q => lightconeIdxBlockRealTerm_nonneg hσr ν q p hp)).mpr
      ⟨fun m => summable_lightconeIdxBlockRealTerm_level ν m σl σr p, h_sum_m⟩
  refine ⟨h_sum_q, ?_⟩
  rw [h_sum_q.tsum_prod' (fun m => summable_lightconeIdxBlockRealTerm_level ν m σl σr p)]
  have h_eval := (conformalBlock ν p.1 p.2).evalPdisk_eq_toLightcone_eval hν hp hwl hwr
  rw [h_eval]
  dsimp [ConformalBlockLightcone.eval]
  simp_rw [(tsum_lightconeIdxBlockRealTerm_level_eq hσr ν _ p hp).2]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

lemma summable_lightconeIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : LightconeIdx => lightconeIdxRealTerm ν q σl σr p) :=
  Summable.of_nonneg_of_le (fun q => lightconeIdxRealTerm_nonneg ν q σl σr p)
    (fun q => lightconeIdxRealTerm_le_blockRealTerm hσr ν q p hp)
    (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).1

lemma tsum_lightconeIdxRealTerm_le_re_evalPdisk (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' q : LightconeIdx, lightconeIdxRealTerm ν q σl σr p) ≤
      ((conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)).re := by
  rw [← (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).2]
  exact (summable_lightconeIdxRealTerm hν hσl hσr p hp).tsum_le_tsum
    (fun q => lightconeIdxRealTerm_le_blockRealTerm hσr ν q p hp)
    (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).1

lemma summable_lightconeIdxTransmuteRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : LightconeIdx => lightconeIdxTransmuteRealTerm ν q σl σr p) :=
  Summable.of_nonneg_of_le (fun q => lightconeIdxTransmuteRealTerm_nonneg ν q σl σr p)
    (fun q => lightconeIdxTransmuteRealTerm_le_const_mul_realTerm_half hσr ν q p hp)
    ((summable_lightconeIdxRealTerm hν hσl (by linarith : σr / 2 < 0) p hp).mul_left _)

lemma tsum_lightconeIdxTransmuteRealTerm_le (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' q : LightconeIdx, lightconeIdxTransmuteRealTerm ν q σl σr p) ≤
      (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
        ((conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) ((σr / 2 : ℝ) : ℂ)).re := by
  have h32 : (1 / 2 : ℝ) < 3 / 2 := by norm_num
  have h_c_nonneg : 0 ≤ 8 * transmuteCoreWeight (3 / 2) / σr ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (transmuteCoreWeight_pos h32).le) (sq_nonneg σr)
  calc
    (∑' q : LightconeIdx, lightconeIdxTransmuteRealTerm ν q σl σr p)
      ≤ ∑' q : LightconeIdx,
          (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
            lightconeIdxRealTerm ν q σl (σr / 2) p :=
        (summable_lightconeIdxTransmuteRealTerm hν hσl hσr p hp).tsum_le_tsum
          (fun q => lightconeIdxTransmuteRealTerm_le_const_mul_realTerm_half hσr ν q p hp)
          ((summable_lightconeIdxRealTerm hν hσl (by linarith : σr / 2 < 0) p hp).mul_left _)
    _ = (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
          (∑' q : LightconeIdx, lightconeIdxRealTerm ν q σl (σr / 2) p) := tsum_mul_left
    _ ≤ (8 * transmuteCoreWeight (3 / 2) / σr ^ 2) *
          ((conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) ((σr / 2 : ℝ) : ℂ)).re :=
        mul_le_mul_of_nonneg_left
          (tsum_lightconeIdxRealTerm_le_re_evalPdisk hν hσl (by linarith) p hp) h_c_nonneg

lemma integrable_lightconeIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (q : LightconeIdx) :
    Integrable (lightconeIdxRealTerm ν q σl σr) corr.nonIdentityMeasure := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_dom : Integrable
      (fun p : ℝ × ℕ => ‖(conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)‖)
      corr.nonIdentityMeasure :=
    (corr.converges_correlator_pdisk hν hwl hwr).norm.restrict
  refine h_dom.mono' (measurable_lightconeIdxRealTerm ν q σl σr).aestronglyMeasurable
    (corr.nonIdentityMeasure_ae_unitary.mono fun p hp => ?_)
  rw [Real.norm_of_nonneg (lightconeIdxRealTerm_nonneg ν q σl σr p)]
  exact ((summable_lightconeIdxRealTerm hν hσl hσr p hp).le_tsum q
    (fun q' _ => lightconeIdxRealTerm_nonneg ν q' σl σr p)).trans
    ((tsum_lightconeIdxRealTerm_le_re_evalPdisk hν hσl hσr p hp).trans (Complex.re_le_norm _))

lemma integrable_lightconeIdxTransmuteRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (q : LightconeIdx) :
    Integrable (lightconeIdxTransmuteRealTerm ν q σl σr) corr.nonIdentityMeasure := by
  have h_dom := (corr.integrable_lightconeIdxRealTerm hν hσl (by linarith : σr / 2 < 0) q).const_mul
    (8 * transmuteCoreWeight (3 / 2) / σr ^ 2)
  refine h_dom.mono' (measurable_lightconeIdxTransmuteRealTerm ν q σl σr).aestronglyMeasurable
    (corr.nonIdentityMeasure_ae_unitary.mono fun p hp => ?_)
  rw [Real.norm_of_nonneg (lightconeIdxTransmuteRealTerm_nonneg ν q σl σr p)]
  exact lightconeIdxTransmuteRealTerm_le_const_mul_realTerm_half hσr ν q p hp

lemma summable_integral_lightconeIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun q : LightconeIdx =>
      ∫ p, lightconeIdxRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_nonneg (q : LightconeIdx) :
      0 ≤ ∫ p, lightconeIdxRealTerm ν q σl σr p ∂corr.nonIdentityMeasure :=
    integral_nonneg (lightconeIdxRealTerm_nonneg ν q σl σr)
  have h_eq :
      (fun q : LightconeIdx => ∫ p, lightconeIdxRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) =
      fun q : LightconeIdx =>
        (ENNReal.ofReal
          (∫ p, lightconeIdxRealTerm ν q σl σr p ∂corr.nonIdentityMeasure)).toReal := by
    ext q
    exact (ENNReal.toReal_ofReal (h_nonneg q)).symm
  rw [h_eq]
  refine ENNReal.summable_toReal ?_
  have h_lint (q : LightconeIdx) :
      ENNReal.ofReal (∫ p, lightconeIdxRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) =
        ∫⁻ p, ENNReal.ofReal (lightconeIdxRealTerm ν q σl σr p) ∂corr.nonIdentityMeasure :=
    ofReal_integral_eq_lintegral_ofReal (corr.integrable_lightconeIdxRealTerm hν hσl hσr q)
      (Eventually.of_forall (lightconeIdxRealTerm_nonneg ν q σl σr))
  simp_rw [h_lint]
  rw [← lintegral_tsum
    (fun q => (measurable_lightconeIdxRealTerm ν q σl σr).ennreal_ofReal.aemeasurable)]
  have h_tsum_le : ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
      (∑' q : LightconeIdx, ENNReal.ofReal (lightconeIdxRealTerm ν q σl σr p)) ≤
        ENNReal.ofReal ‖(conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)‖ := by
    filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => lightconeIdxRealTerm_nonneg ν q σl σr p)
      (summable_lightconeIdxRealTerm hν hσl hσr p hp)]
    exact ENNReal.ofReal_le_ofReal
      ((tsum_lightconeIdxRealTerm_le_re_evalPdisk hν hσl hσr p hp).trans (Complex.re_le_norm _))
  have h_dom : Integrable
      (fun p : ℝ × ℕ => (conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ))
      corr.nonIdentityMeasure :=
    (corr.converges_correlator_pdisk hν hwl hwr).restrict
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae h_tsum_le) ?_)
  exact lt_of_le_of_lt (lintegral_mono fun p => by rw [← ofReal_norm]) h_dom.hasFiniteIntegral

lemma summable_integral_lightconeIdxTransmuteRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun q : LightconeIdx =>
      ∫ p, lightconeIdxTransmuteRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) := by
  refine ((corr.summable_integral_lightconeIdxRealTerm hν hσl (by linarith : σr / 2 < 0)).mul_left
    (8 * transmuteCoreWeight (3 / 2) / σr ^ 2)).of_nonneg_of_le
    (fun q => integral_nonneg (lightconeIdxTransmuteRealTerm_nonneg ν q σl σr)) fun q => ?_
  rw [← integral_const_mul]
  exact integral_mono_ae (corr.integrable_lightconeIdxTransmuteRealTerm hν hσl hσr q)
    ((corr.integrable_lightconeIdxRealTerm hν hσl (by linarith) q).const_mul _)
    (corr.nonIdentityMeasure_ae_unitary.mono fun p hp =>
      lightconeIdxTransmuteRealTerm_le_const_mul_realTerm_half hσr ν q p hp)

lemma hasSum_fiberwise_lightconeIdxSpin {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : LightconeIdx → E} {a : E} (hf : HasSum f a) :
    HasSum (fun J : ℤ => ∑' q : LightconeIdx, if lightconeIdxSpin q = J then f q else 0) a := by
  convert hf.tsum_fiberwise lightconeIdxSpin with J
  rw [tsum_subtype (lightconeIdxSpin ⁻¹' {J}) f]
  congr 1
  ext q
  simp [Set.indicator]

/-- Integrability of `monomialTermReal` with respect to `corr.lightconeMeasure J` on
$\sigma_l < 0, \sigma_r < 0$. -/
lemma lightconeMeasure_integrable_real (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (J : ℤ) :
    Integrable (fun h : ℝ => monomialTermReal h J σl σr) (corr.lightconeMeasure J) := by
  dsimp [lightconeMeasure]
  have hf_cont : Continuous (fun h : ℝ => monomialTermReal h J σl σr) := by
    unfold monomialTermReal
    fun_prop
  refine integrable_sum_measure (fun q => ?_) ?_
  · split_ifs with hq
    · rw [corr.integrable_lightconeAtomMeasure_iff q hf_cont.aestronglyMeasurable]
      subst hq
      exact corr.integrable_lightconeIdxRealTerm hν hσl hσr q
    · exact integrable_zero_measure
  · refine (corr.summable_integral_lightconeIdxRealTerm hν hσl hσr).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _) fun q => ?_
    split_ifs with hq
    · have h_norm : (fun x : ℝ => ‖monomialTermReal x J σl σr‖) =
          fun x : ℝ => monomialTermReal x J σl σr := by
        ext x
        exact Real.norm_of_nonneg (monomialTermReal_nonneg x J σl σr)
      rw [h_norm, corr.integral_lightconeAtomMeasure q hf_cont.aestronglyMeasurable]
      simp [lightconeIdxRealTerm, hq]
    · rw [integral_zero_measure]
      exact integral_nonneg (lightconeIdxRealTerm_nonneg ν q σl σr)

/-- Integrability of the transmuted real monomials with respect to `corr.lightconeMeasure J`. -/
lemma lightconeMeasure_integrable_transmute (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (J : ℤ) :
    Integrable
      (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr)
      (corr.lightconeMeasure J) := by
  dsimp [lightconeMeasure]
  have hf_meas : Measurable
      (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr) := by
    refine (measurable_transmutePosWeight.comp (measurable_id.add measurable_const)).mul ?_
    unfold monomialTermReal
    fun_prop
  refine integrable_sum_measure (fun q => ?_) ?_
  · split_ifs with hq
    · rw [corr.integrable_lightconeAtomMeasure_iff q hf_meas.aestronglyMeasurable]
      subst hq
      refine (corr.integrable_lightconeIdxTransmuteRealTerm hν hσl hσr q).congr
        (Eventually.of_forall fun p => ?_)
      dsimp [lightconeIdxTransmuteRealTerm, lightconeIdxRealTerm]
      ring
    · exact integrable_zero_measure
  · refine (corr.summable_integral_lightconeIdxTransmuteRealTerm hν hσl hσr).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _) fun q => ?_
    split_ifs with hq
    · have h_norm :
          (fun x : ℝ => ‖transmutePosWeight (x + (J : ℝ)) * monomialTermReal x J σl σr‖) =
          fun x : ℝ => transmutePosWeight (x + (J : ℝ)) * monomialTermReal x J σl σr := by
        ext x
        exact Real.norm_of_nonneg
          (mul_nonneg (transmutePosWeight_nonneg _) (monomialTermReal_nonneg x J σl σr))
      rw [h_norm, corr.integral_lightconeAtomMeasure q hf_meas.aestronglyMeasurable]
      subst hq
      refine le_of_eq (integral_congr_ae (Eventually.of_forall fun p => ?_))
      dsimp [lightconeIdxTransmuteRealTerm, lightconeIdxRealTerm]
      ring
    · rw [integral_zero_measure]
      exact integral_nonneg (lightconeIdxTransmuteRealTerm_nonneg ν q σl σr)

lemma lightconeMeasure_integral_transmute (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (J : ℤ) :
    (∫ h : ℝ, transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr
        ∂(corr.lightconeMeasure J)) =
      ∑' q : LightconeIdx,
        if lightconeIdxSpin q = J then
          ∫ p, lightconeIdxTransmuteRealTerm ν q σl σr p ∂corr.nonIdentityMeasure
        else 0 := by
  have h_int := corr.lightconeMeasure_integrable_transmute hν hσl hσr J
  dsimp [lightconeMeasure] at h_int ⊢
  rw [integral_sum_measure h_int]
  have hf_meas : Measurable
      (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr) := by
    refine (measurable_transmutePosWeight.comp (measurable_id.add measurable_const)).mul ?_
    unfold monomialTermReal
    fun_prop
  congr 1 with q
  split_ifs with hq
  · rw [corr.integral_lightconeAtomMeasure q hf_meas.aestronglyMeasurable]
    subst hq
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp [lightconeIdxTransmuteRealTerm, lightconeIdxRealTerm]
    ring
  · exact integral_zero_measure _

lemma lightconeMeasure_summable_transmute (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun J : ℤ =>
      ∫ h : ℝ, transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr
        ∂(corr.lightconeMeasure J)) := by
  simp_rw [corr.lightconeMeasure_integral_transmute hν hσl hσr]
  exact (hasSum_fiberwise_lightconeIdxSpin
    (corr.summable_integral_lightconeIdxTransmuteRealTerm hν hσl hσr).hasSum).summable

/-- Unitarity, Bose symmetry, and transmuted monomial integrability/summability of
`corr.lightconeMeasure`, inherited from `corr.mu_measure` and
`ConformalBlock.exists_conformalBlockLightcone`. -/
lemma lightconeMeasure_props (hν : 0 ≤ ν) :
    (∀ J : ℤ, corr.lightconeMeasure J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0) ∧
    (∀ J : ℤ, Odd J → corr.lightconeMeasure J = 0) ∧
    (∀ {σl σr : ℝ}, σl < 0 → σr < 0 → ∀ J : ℤ,
      Integrable
        (fun h : ℝ => transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr)
        (corr.lightconeMeasure J)) ∧
    (∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
      Summable (fun J : ℤ =>
        ∫ h : ℝ, transmutePosWeight (h + (J : ℝ)) * monomialTermReal h J σl σr
          ∂(corr.lightconeMeasure J))) :=
  ⟨corr.lightconeMeasure_support_unitary,
   corr.lightconeMeasure_support_odd_spin,
   fun hσl hσr J => corr.lightconeMeasure_integrable_transmute hν hσl hσr J,
   fun hσl hσr => corr.lightconeMeasure_summable_transmute hν hσl hσr⟩

/-- Canonical `LightconeBlockFourPointData` associated to a `FourPointData` with $\nu \ge 0$ and
twist gap $h_{\mathrm{gap}}$, equipping the correlator with `corr.lightconeMeasure`. -/
noncomputable def toLightconeBlockFourPointData (hν : 0 ≤ ν) (h_gap : ℝ) :
    LightconeBlockFourPointData where
  muLC := corr.lightconeMeasure
  h_gap := h_gap
  support_unitary := (corr.lightconeMeasure_props hν).1
  support_odd_spin := (corr.lightconeMeasure_props hν).2.1
  integrable_transmute := (corr.lightconeMeasure_props hν).2.2.1
  summable_transmute := (corr.lightconeMeasure_props hν).2.2.2

@[simp]
theorem toLightconeBlockFourPointData_muLC (hν : 0 ≤ ν) (h_gap : ℝ) :
    (corr.toLightconeBlockFourPointData hν h_gap).muLC = corr.lightconeMeasure :=
  rfl

@[simp]
theorem toLightconeBlockFourPointData_h_gap (hν : 0 ≤ ν) (h_gap : ℝ) :
    (corr.toLightconeBlockFourPointData hν h_gap).h_gap = h_gap :=
  rfl

lemma geg_ph_ofReal (ν : ℝ) (n : ℕ) :
    gegenbauer.ph (ν : ℂ) n = (realPochhammer ν n : ℂ) := by
  induction n with
  | zero => simp [gegenbauer.ph, realPochhammer_zero]
  | succ k ih =>
    rw [gegenbauer.ph, _root_.ascPochhammer_succ_eval, ← gegenbauer.ph,
      ih, realPochhammer_succ]
    push_cast
    rfl

lemma geg_two_var_coeff_zero_re (ν : ℝ) (l : ℕ) :
    (gegenbauer.geg_two_var_coeff (ν : ℂ) l 0).re =
      realPochhammer ν l / (l.factorial : ℝ) := by
  dsimp [gegenbauer.geg_two_var_coeff, gegenbauer.fact]
  rw [geg_ph_ofReal, geg_ph_ofReal, realPochhammer_zero]
  norm_cast
  simp

lemma monomialIdxCoeff_zero_level (ν : ℝ) (p : ℝ × ℕ) :
    monomialIdxCoeff ν (0, p.2, 0) p =
      realPochhammer ν p.2 / (p.2.factorial : ℝ) := by
  dsimp [monomialIdxCoeff]
  rw [(conformalBlock ν p.1 p.2).norm_primary, one_mul,
    geg_two_var_coeff_zero_re]

/-- If `corr.toMonomialFourPointData hν` has a twist gap, the identity primary $(0, 0)$ has unit
OPE measure: `corr.mu_measure {(0, 0)} = 1`. -/
theorem mu_measure_singleton_zero_eq_one (hν : 0 ≤ ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap) :
    corr.mu_measure {((0 : ℝ), (0 : ℕ))} = 1 := by
  have h_mu0 := hgap.mu_props.1
  change corr.monomialMeasure 0 {(0 : ℝ)} = 1 at h_mu0
  dsimp [monomialMeasure] at h_mu0
  rw [Measure.sum_apply _ (measurableSet_singleton (0 : ℝ))] at h_mu0
  have h_q_zero :
      corr.monomialAtomMeasure (0, 0, 0) {(0 : ℝ)} =
        corr.mu_measure {((0 : ℝ), (0 : ℕ))} := by
    dsimp [monomialAtomMeasure]
    have h_meas0 : MeasurableSet (monomialIdxWeight (0, 0, 0) ⁻¹' {(0 : ℝ)}) :=
      measurable_monomialIdxWeight (0, 0, 0) (measurableSet_singleton (0 : ℝ))
    rw [Measure.map_apply (measurable_monomialIdxWeight (0, 0, 0))
      (measurableSet_singleton (0 : ℝ)),
      withDensity_apply _ h_meas0]
    have h_ind :
        ∀ᵐ p : ℝ × ℕ ∂corr.mu_measure,
          Set.indicator (monomialIdxWeight (0, 0, 0) ⁻¹' {(0 : ℝ)})
            (fun p => ENNReal.ofReal (monomialIdxCoeff ν (0, 0, 0) p)) p =
          Set.indicator {((0 : ℝ), (0 : ℕ))} (fun _ => (1 : ℝ≥0∞)) p := by
      filter_upwards [corr.ae_unitary] with p hp
      by_cases hp0 : p = ((0 : ℝ), (0 : ℕ))
      · subst hp0
        have hw0 : monomialIdxWeight (0, 0, 0) ((0 : ℝ), (0 : ℕ)) = 0 := by
          dsimp [monomialIdxWeight]; ring
        have hc0 : monomialIdxCoeff ν (0, 0, 0) ((0 : ℝ), (0 : ℕ)) = 1 := by
          simpa using monomialIdxCoeff_zero_level ν ((0 : ℝ), (0 : ℕ))
        rw [Set.indicator_of_mem (by simpa using hw0), Set.indicator_of_mem rfl,
          hc0, ENNReal.ofReal_one]
      · rw [Set.indicator_of_notMem (s := {((0 : ℝ), (0 : ℕ))}) hp0]
        by_cases hw : monomialIdxWeight (0, 0, 0) p = 0
        · have hp1_zero : p.1 = 0 := by
            dsimp [monomialIdxWeight] at hw
            linarith
          have hp2_zero : p.2 = 0 := by
            have hp2_nonneg : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
            have : (p.2 : ℝ) = 0 := by linarith
            exact_mod_cast this
          exact (hp0 (Prod.ext hp1_zero hp2_zero)).elim
        · exact Set.indicator_of_notMem hw _
    rw [← lintegral_indicator h_meas0, lintegral_congr_ae h_ind,
      lintegral_indicator (measurableSet_singleton _), setLIntegral_const, one_mul]
  have h_q_other (q : MonomialIdx) (hq_ne : q ≠ (0, 0, 0)) (hq_spin : monomialIdxSpin q = 0) :
      corr.monomialAtomMeasure q {(0 : ℝ)} = 0 := by
    dsimp [monomialAtomMeasure]
    have h_meas_q : MeasurableSet (monomialIdxWeight q ⁻¹' {(0 : ℝ)}) :=
      measurable_monomialIdxWeight q (measurableSet_singleton (0 : ℝ))
    rw [Measure.map_apply (measurable_monomialIdxWeight q) (measurableSet_singleton (0 : ℝ)),
      withDensity_apply _ h_meas_q,
      setLIntegral_eq_zero_iff h_meas_q (measurable_monomialIdxCoeff ν q).ennreal_ofReal]
    filter_upwards [corr.ae_unitary] with p hp h_mem
    have h_w_zero : monomialIdxWeight q p = 0 := h_mem
    have hj_eq : (q.2.1 : ℝ) = 2 * (q.2.2 : ℝ) := by
      have : (q.2.1 : ℤ) - 2 * (q.2.2 : ℤ) = 0 := hq_spin
      exact_mod_cast sub_eq_zero.mp this
    have h_sum_zero : (p.1 + (q.1 : ℝ)) / 2 = 0 := by
      dsimp [monomialIdxWeight] at h_w_zero
      linarith
    have hp2_nonneg : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
    have hq1_nonneg : (0 : ℝ) ≤ (q.1 : ℝ) := Nat.cast_nonneg _
    have hp2_zero : p.2 = 0 := by
      have : (p.2 : ℝ) = 0 := by linarith
      exact_mod_cast this
    have hq1_zero : q.1 = 0 := by
      have : (q.1 : ℝ) = 0 := by linarith
      exact_mod_cast this
    have hq21_ne : q.2.1 ≠ 0 := by
      intro hq21
      apply hq_ne
      have hj_nat : q.2.1 = 2 * q.2.2 := by
        have : (q.2.1 : ℤ) - 2 * (q.2.2 : ℤ) = 0 := hq_spin
        omega
      rcases q with ⟨n, j, a⟩
      dsimp at hq1_zero hq21 hj_nat
      have ha0 : a = 0 := by omega
      subst hq1_zero hq21 ha0
      rfl
    have hj_not_mem : q.2.1 ∉ descendantSpins p.2 q.1 := by
      rw [hp2_zero, hq1_zero, mem_descendantSpins]
      intro h
      omega
    rw [ENNReal.ofReal_eq_zero]
    dsimp [monomialIdxCoeff]
    split_ifs
    · rw [((conformalBlock ν p.1 p.2).level q.1).A_support q.2.1 hj_not_mem, zero_mul]
    · rfl
  rw [tsum_eq_single (0, 0, 0) (fun q hq => by
    split_ifs with h_spin
    · exact h_q_other q hq h_spin
    · rfl)] at h_mu0
  have h_spin0 : monomialIdxSpin (0, 0, 0) = 0 := rfl
  rwa [if_pos h_spin0, h_q_zero] at h_mu0

/-- Non-identity spin-0 primaries below the twist gap have measure zero. -/
lemma nonIdentityMeasure_twist_lt_zero_spin (hν : 0 ≤ ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap) :
    corr.nonIdentityMeasure { p : ℝ × ℕ | p.2 = 0 ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap } = 0 := by
  have h_diff0 := hgap.mu_props.2.1
  change corr.monomialMeasure 0 (Iio h_gap \ {(0 : ℝ)}) = 0 at h_diff0
  dsimp [monomialMeasure] at h_diff0
  have h_meas_S : MeasurableSet (Iio h_gap \ {(0 : ℝ)}) :=
    measurableSet_Iio.diff (measurableSet_singleton (0 : ℝ))
  rw [Measure.sum_apply _ h_meas_S, ENNReal.tsum_eq_zero] at h_diff0
  have h000 := h_diff0 (0, 0, 0)
  have h_spin0 : monomialIdxSpin (0, 0, 0) = 0 := rfl
  rw [if_pos h_spin0] at h000
  dsimp [monomialAtomMeasure] at h000
  have h_meas_pre : MeasurableSet (monomialIdxWeight (0, 0, 0) ⁻¹' (Iio h_gap \ {(0 : ℝ)})) :=
    measurable_monomialIdxWeight (0, 0, 0) h_meas_S
  rw [Measure.map_apply (measurable_monomialIdxWeight (0, 0, 0)) h_meas_S,
    withDensity_apply _ h_meas_pre,
    setLIntegral_eq_zero_iff h_meas_pre
      (measurable_monomialIdxCoeff ν (0, 0, 0)).ennreal_ofReal] at h000
  have h_ae :
      ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
        ¬ (p.2 = 0 ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap) := by
    have h_not_zero : ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure, p ≠ ((0 : ℝ), (0 : ℕ)) := by
      dsimp [nonIdentityMeasure]
      exact ae_restrict_mem (measurableSet_singleton _).compl
    have h000_nonId :
        ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
          p ∈ monomialIdxWeight (0, 0, 0) ⁻¹' (Iio h_gap \ {(0 : ℝ)}) →
            ENNReal.ofReal (monomialIdxCoeff ν (0, 0, 0) p) = 0 :=
      ae_mono Measure.restrict_le_self h000
    filter_upwards [corr.nonIdentityMeasure_ae_unitary, h_not_zero, h000_nonId] with
      p hp_unit hp_ne hp_zero ⟨hp2, hp_lt⟩
    have hp1_pos : 0 < p.1 := by
      have hp1_nonneg : 0 ≤ p.1 := by simpa [hp2] using hp_unit
      refine lt_of_le_of_ne hp1_nonneg fun hp1_eq => hp_ne ?_
      exact Prod.ext hp1_eq.symm hp2
    have h_mem : p ∈ monomialIdxWeight (0, 0, 0) ⁻¹' (Iio h_gap \ {(0 : ℝ)}) := by
      simp only [mem_preimage, mem_diff, mem_Iio, mem_singleton_iff, monomialIdxWeight]
      simp only [hp2, Nat.cast_zero, sub_zero] at hp_lt
      refine ⟨by linarith, by linarith⟩
    have hc_zero := hp_zero h_mem
    have hc_one : monomialIdxCoeff ν (0, 0, 0) p = 1 := by
      have h1 := monomialIdxCoeff_zero_level ν p
      simpa [hp2] using h1
    rw [hc_one, ENNReal.ofReal_one] at hc_zero
    exact one_ne_zero hc_zero
  simpa [ae_iff, not_not] using h_ae

/-- For $\nu > 0$ and any spin $l \ge 1$, primaries of spin $l$ below the twist gap have measure
zero. -/
lemma nonIdentityMeasure_twist_lt_spin_of_pos (hν_pos : 0 < ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν_pos.le).HasTwistGap h_gap)
    {l : ℕ} (hl : l ≠ 0) :
    corr.nonIdentityMeasure { p : ℝ × ℕ | p.2 = l ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap } = 0 := by
  have hl_int : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  have h_Jl := hgap.mu_props.2.2 (l : ℤ) hl_int
  change corr.monomialMeasure (l : ℤ) (Iio h_gap) = 0 at h_Jl
  dsimp [monomialMeasure] at h_Jl
  rw [Measure.sum_apply _ measurableSet_Iio, ENNReal.tsum_eq_zero] at h_Jl
  have h0l0 := h_Jl (0, l, 0)
  have h_spin_l : monomialIdxSpin (0, l, 0) = (l : ℤ) := by
    dsimp [monomialIdxSpin]; ring
  rw [if_pos h_spin_l] at h0l0
  dsimp [monomialAtomMeasure] at h0l0
  have h_meas_pre : MeasurableSet (monomialIdxWeight (0, l, 0) ⁻¹' Iio h_gap) :=
    measurable_monomialIdxWeight (0, l, 0) measurableSet_Iio
  rw [Measure.map_apply (measurable_monomialIdxWeight (0, l, 0)) measurableSet_Iio,
    withDensity_apply _ h_meas_pre,
    setLIntegral_eq_zero_iff h_meas_pre
      (measurable_monomialIdxCoeff ν (0, l, 0)).ennreal_ofReal] at h0l0
  have h0l0_nonId :
      ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
        p ∈ monomialIdxWeight (0, l, 0) ⁻¹' Iio h_gap →
          ENNReal.ofReal (monomialIdxCoeff ν (0, l, 0) p) = 0 :=
    ae_mono Measure.restrict_le_self h0l0
  have h_ae :
      ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
        ¬ (p.2 = l ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap) := by
    filter_upwards [h0l0_nonId] with p hp_zero ⟨hp2, hp_lt⟩
    have h_mem : p ∈ monomialIdxWeight (0, l, 0) ⁻¹' Iio h_gap := by
      simp only [mem_preimage, mem_Iio, monomialIdxWeight]
      rw [← hp2]
      linarith
    have hc_zero := hp_zero h_mem
    have hc_val : monomialIdxCoeff ν (0, l, 0) p = realPochhammer ν l / (l.factorial : ℝ) := by
      have h1 := monomialIdxCoeff_zero_level ν p
      simpa [hp2] using h1
    have hc_pos : 0 < realPochhammer ν l / (l.factorial : ℝ) :=
      div_pos (realPochhammer_pos hν_pos l) (Nat.cast_pos.mpr l.factorial_pos)
    rw [hc_val, ENNReal.ofReal_eq_zero] at hc_zero
    linarith
  simpa [ae_iff, not_not] using h_ae

/-- For $\nu > 0$, all non-identity primaries have twist $\ge h_{\mathrm{gap}}$ almost everywhere. -/
theorem nonIdentityMeasure_twist_lt_of_pos (hν_pos : 0 < ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν_pos.le).HasTwistGap h_gap) :
    corr.nonIdentityMeasure { p : ℝ × ℕ | (p.1 - (p.2 : ℝ)) / 2 < h_gap } = 0 := by
  have h_union :
      { p : ℝ × ℕ | (p.1 - (p.2 : ℝ)) / 2 < h_gap } =
        ⋃ l : ℕ, { p : ℝ × ℕ | p.2 = l ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap } := by
    ext p
    simp
  rw [h_union]
  refine measure_iUnion_null fun l => ?_
  by_cases hl : l = 0
  · subst hl
    exact corr.nonIdentityMeasure_twist_lt_zero_spin hν_pos.le hgap
  · exact corr.nonIdentityMeasure_twist_lt_spin_of_pos hν_pos hgap hl

lemma realPochhammer_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    realPochhammer 0 n = 0 := by
  induction n with
  | zero => exact (hn rfl).elim
  | succ m ih =>
    cases m with
    | zero => simp [realPochhammer_succ, realPochhammer_zero]
    | succ k =>
      rw [realPochhammer_succ, ih (Nat.succ_ne_zero k), zero_mul]

/-- For any $\nu \ge 0$ and any lightcone index $q$, `lightconeIdxCoeff ν q p` vanishes almost
everywhere on non-identity primaries with twist $< h_{\mathrm{gap}}$. -/
theorem nonIdentityMeasure_ae_lightconeIdxCoeff_eq_zero_of_twist_lt
    (hν : 0 ≤ ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap) (q : LightconeIdx) :
    ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
      (p.1 - (p.2 : ℝ)) / 2 < h_gap → lightconeIdxCoeff ν q p = 0 := by
  rcases eq_or_lt_of_le hν with hν0 | hν_pos
  · subst hν0
    have h_zero_spin :
        ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
          ¬ (p.2 = 0 ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap) := by
      simpa [ae_iff, not_not] using corr.nonIdentityMeasure_twist_lt_zero_spin le_rfl hgap
    filter_upwards [corr.nonIdentityMeasure_ae_unitary, h_zero_spin] with
      p hp_unit hp_not0 hp_lt
    have hp2_ne : p.2 ≠ 0 := fun hp2 => hp_not0 ⟨hp2, hp_lt⟩
    dsimp [lightconeIdxCoeff]
    have hC0 : ((conformalBlock 0 p.1 p.2).toLightcone.level 0).C p.2 = 0 := by
      rw [(conformalBlock 0 p.1 p.2).toLightcone_C_zero le_rfl hp_unit,
        realPochhammer_zero_of_ne_zero hp2_ne, zero_div]
    exact (conformalBlock 0 p.1 p.2).toLightcone_C_eq_zero_of_C_zero le_rfl hp_unit hC0 q.1 q.2
  · have h_twist_ge :
        ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure, ¬ (p.1 - (p.2 : ℝ)) / 2 < h_gap := by
      simpa [ae_iff, not_not] using corr.nonIdentityMeasure_twist_lt_of_pos hν_pos hgap
    filter_upwards [h_twist_ge] with p hp_ge hp_lt
    exact (hp_ge hp_lt).elim

/-- If `corr.toMonomialFourPointData hν` has twist gap $h_{\mathrm{gap}}$, the spin-0 collinear
measure `corr.lightconeMeasure 0` vanishes below $h_{\mathrm{gap}}$. -/
theorem lightconeMeasure_zero_Iio_eq_zero (hν : 0 ≤ ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap) :
    corr.lightconeMeasure 0 (Iio h_gap) = 0 := by
  dsimp [lightconeMeasure]
  rw [Measure.sum_apply _ measurableSet_Iio, ENNReal.tsum_eq_zero]
  intro q
  split_ifs with hq0
  · dsimp [lightconeAtomMeasure]
    have h_meas_pre : MeasurableSet (lightconeIdxWeight q.1 ⁻¹' Iio h_gap) :=
      measurable_lightconeIdxWeight q.1 measurableSet_Iio
    rw [Measure.map_apply (measurable_lightconeIdxWeight q.1) measurableSet_Iio,
      withDensity_apply _ h_meas_pre,
      setLIntegral_eq_zero_iff h_meas_pre
        (measurable_lightconeIdxCoeff ν q).ennreal_ofReal]
    filter_upwards [corr.nonIdentityMeasure_ae_lightconeIdxCoeff_eq_zero_of_twist_lt hν hgap q]
      with p hp_zero h_mem
    have h_lt : (p.1 - (p.2 : ℝ)) / 2 < h_gap := by
      have hm_nonneg : (0 : ℝ) ≤ (q.1 : ℝ) := Nat.cast_nonneg _
      have h_w : (p.1 - (p.2 : ℝ)) / 2 + (q.1 : ℝ) < h_gap := h_mem
      linarith
    rw [hp_zero h_lt, ENNReal.ofReal_zero]
  · simp

/-- Complex 1D-block contribution of lightcone index $q = (m, k_r)$ at primary $p$. -/
noncomputable def lightconeIdxBlockComplexTerm
    (ν : ℝ) (q : LightconeIdx) (wl wr : ℂ) (p : ℝ × ℕ) : ℂ :=
  (lightconeIdxCoeff ν q p : ℂ) *
    (Complex.exp ((lightconeIdxWeight q.1 p : ℂ) * wl) *
      block1dPos (lightconeIdxWeight q.1 p + (lightconeIdxSpin q : ℝ)) wr)

lemma measurable_lightconeIdxBlockComplexTerm (ν : ℝ) (q : LightconeIdx) (wl : ℂ)
    {wr : ℂ} (hwr : wr ∈ UcDisk) :
    Measurable (lightconeIdxBlockComplexTerm ν q wl wr) := by
  unfold lightconeIdxBlockComplexTerm
  have h1 : Measurable (fun p : ℝ × ℕ => (lightconeIdxCoeff ν q p : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_lightconeIdxCoeff ν q)
  have h2 : Measurable (fun p : ℝ × ℕ => Complex.exp ((lightconeIdxWeight q.1 p : ℂ) * wl)) :=
    (by fun_prop : Measurable (fun x : ℝ => Complex.exp ((x : ℂ) * wl))).comp
      (measurable_lightconeIdxWeight q.1)
  have h3 : Measurable
      (fun p : ℝ × ℕ => block1dPos (lightconeIdxWeight q.1 p + (lightconeIdxSpin q : ℝ)) wr) :=
    (measurable_block1dPos hwr).comp ((measurable_lightconeIdxWeight q.1).add measurable_const)
  exact h1.mul (h2.mul h3)

lemma measurable_lightconeIdxBlockRealTerm (ν : ℝ) (q : LightconeIdx) (σl : ℝ)
    {σr : ℝ} (hσr : σr < 0) :
    Measurable (fun p : ℝ × ℕ =>
      if (p.2 : ℝ) ≤ p.1 then lightconeIdxBlockRealTerm ν q σl σr p else 0) := by
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_meas_pos : Measurable (fun p : ℝ × ℕ =>
      lightconeIdxCoeff ν q p * Real.exp (blockExp p.1 p.2 q.1 * σl) *
        (block1dPos (blockExp p.1 p.2 q.2) (σr : ℂ)).re) := by
    refine ((measurable_lightconeIdxCoeff ν q).mul ?_).mul ?_
    · have hw := measurable_lightconeIdxWeight q.1
      change Measurable (fun p : ℝ × ℕ => Real.exp (lightconeIdxWeight q.1 p * σl))
      fun_prop
    · have hw := measurable_lightconeIdxWeight q.2
      exact Complex.continuous_re.measurable.comp ((measurable_block1dPos hwr).comp hw)
  have h_set : MeasurableSet { p : ℝ × ℕ | (p.2 : ℝ) ≤ p.1 } :=
    measurableSet_le (measurable_of_countable _ |>.comp measurable_snd) measurable_fst
  have h_eq :
      (fun p : ℝ × ℕ =>
        if (p.2 : ℝ) ≤ p.1 then lightconeIdxBlockRealTerm ν q σl σr p else 0) =
      fun p : ℝ × ℕ =>
        if p ∈ { p : ℝ × ℕ | (p.2 : ℝ) ≤ p.1 } then
          lightconeIdxCoeff ν q p * Real.exp (blockExp p.1 p.2 q.1 * σl) *
            (block1dPos (blockExp p.1 p.2 q.2) (σr : ℂ)).re
        else 0 := by
    ext p
    by_cases hp : (p.2 : ℝ) ≤ p.1
    · simp [hp, lightconeIdxBlockRealTerm, block1dPos_of_nonneg (blockExp_nonneg hp q.2)]
    · simp [hp]
  rw [h_eq]
  exact Measurable.ite h_set h_meas_pos measurable_const

lemma norm_lightconeIdxBlockComplexTerm_le {wl wr : ℂ} (hwr : wr ∈ UcDisk)
    (ν : ℝ) (q : LightconeIdx) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    ‖lightconeIdxBlockComplexTerm ν q wl wr p‖ ≤
      lightconeIdxBlockRealTerm ν q wl.re wr.re p := by
  dsimp [lightconeIdxBlockComplexTerm, lightconeIdxBlockRealTerm]
  rw [lightconeIdxWeight_add_spin_eq_blockExp, lightconeIdxWeight_eq_blockExp,
    block1dPos_of_nonneg (blockExp_nonneg hp q.2), norm_mul, norm_mul,
    Complex.norm_of_nonneg (lightconeIdxCoeff_nonneg ν q p), Complex.norm_exp, ← mul_assoc]
  have h_re : ((blockExp p.1 p.2 q.1 : ℂ) * wl).re = blockExp p.1 p.2 q.1 * wl.re := by
    simp [Complex.mul_re]
  rw [h_re]
  exact mul_le_mul_of_nonneg_left (norm_block1d_le_re_of_nonneg (blockExp_nonneg hp q.2) hwr)
    (mul_nonneg (lightconeIdxCoeff_nonneg ν q p) (Real.exp_pos _).le)

lemma summable_lightconeIdxBlockComplexTerm_level (ν : ℝ) (m : ℕ) (wl wr : ℂ) (p : ℝ × ℕ) :
    Summable (fun kr : ℕ => lightconeIdxBlockComplexTerm ν (m, kr) wl wr p) := by
  refine summable_of_ne_finset_zero
    (s := (((conformalBlock ν p.1 p.2).toLightcone).level m).support) fun kr hkr => ?_
  dsimp [lightconeIdxBlockComplexTerm, lightconeIdxCoeff]
  rw [(((conformalBlock ν p.1 p.2).toLightcone).level m).C_support kr hkr,
    Complex.ofReal_zero, zero_mul]

lemma tsum_lightconeIdxBlockComplexTerm_level_eq
    (ν : ℝ) (m : ℕ) (wl wr : ℂ) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' kr : ℕ, lightconeIdxBlockComplexTerm ν (m, kr) wl wr p) =
      Complex.exp ((blockExp p.1 p.2 m : ℂ) * wl) *
        ((conformalBlock ν p.1 p.2).toLightcone).evalLevel m wr := by
  set L := (conformalBlock ν p.1 p.2).toLightcone
  rw [tsum_eq_sum (s := (L.level m).support) fun kr hkr => by
    dsimp [lightconeIdxBlockComplexTerm, lightconeIdxCoeff]
    rw [(L.level m).C_support kr hkr, Complex.ofReal_zero, zero_mul]]
  dsimp [ConformalBlockLightcone.evalLevel, ConformalBlockLightconeLevel.eval]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun kr _ => ?_
  have h_add := lightconeIdxWeight_add_spin_eq_blockExp (m, kr) p
  dsimp at h_add
  dsimp [lightconeIdxBlockComplexTerm, lightconeIdxCoeff]
  rw [h_add, lightconeIdxWeight_eq_blockExp,
    block1dPos_of_nonneg (blockExp_nonneg hp kr)]
  ring

lemma summable_and_tsum_lightconeIdxBlockComplexTerm (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : LightconeIdx => lightconeIdxBlockComplexTerm ν q wl wr p) ∧
    (∑' q : LightconeIdx, lightconeIdxBlockComplexTerm ν q wl wr p) =
      (conformalBlock ν p.1 p.2).evalPdisk wl wr := by
  have h_sum_real := (summable_and_tsum_lightconeIdxBlockRealTerm hν hwl hwr p hp).1
  have h_sum_q : Summable (fun q : LightconeIdx => lightconeIdxBlockComplexTerm ν q wl wr p) :=
    Summable.of_norm_bounded h_sum_real
      (fun q => norm_lightconeIdxBlockComplexTerm_le hwr ν q p hp)
  refine ⟨h_sum_q, ?_⟩
  rw [h_sum_q.tsum_prod' (fun m => summable_lightconeIdxBlockComplexTerm_level ν m wl wr p)]
  simp_rw [tsum_lightconeIdxBlockComplexTerm_level_eq ν _ wl wr p hp]
  exact ((conformalBlock ν p.1 p.2).evalPdisk_eq_toLightcone_eval hν hp hwl hwr).symm

lemma integrable_lightconeIdxBlockRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (q : LightconeIdx) :
    Integrable (lightconeIdxBlockRealTerm ν q σl σr) corr.nonIdentityMeasure := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_dom : Integrable
      (fun p : ℝ × ℕ => ‖(conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)‖)
      corr.nonIdentityMeasure :=
    (corr.converges_correlator_pdisk hν hwl hwr).norm.restrict
  have h_meas : AEStronglyMeasurable (lightconeIdxBlockRealTerm ν q σl σr)
      corr.nonIdentityMeasure := by
    refine (measurable_lightconeIdxBlockRealTerm ν q σl hσr).aestronglyMeasurable.congr
      (corr.nonIdentityMeasure_ae_unitary.mono fun p hp => ?_)
    simp [hp]
  refine h_dom.mono' h_meas (corr.nonIdentityMeasure_ae_unitary.mono fun p hp => ?_)
  rw [Real.norm_of_nonneg (lightconeIdxBlockRealTerm_nonneg hσr ν q p hp)]
  exact (((summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).1.le_tsum q
    (fun q' _ => lightconeIdxBlockRealTerm_nonneg hσr ν q' p hp)).trans_eq
    (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).2).trans (Complex.re_le_norm _)

lemma integrable_lightconeIdxBlockComplexTerm (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (q : LightconeIdx) :
    Integrable (lightconeIdxBlockComplexTerm ν q wl wr) corr.nonIdentityMeasure := by
  refine (corr.integrable_lightconeIdxBlockRealTerm hν hwl hwr q).mono'
    (measurable_lightconeIdxBlockComplexTerm ν q wl hwr).aestronglyMeasurable
    (corr.nonIdentityMeasure_ae_unitary.mono fun p hp =>
      norm_lightconeIdxBlockComplexTerm_le hwr ν q p hp)

lemma summable_integral_lightconeIdxBlockRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun q : LightconeIdx =>
      ∫ p, lightconeIdxBlockRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_nonneg (q : LightconeIdx) :
      0 ≤ ∫ p, lightconeIdxBlockRealTerm ν q σl σr p ∂corr.nonIdentityMeasure :=
    integral_nonneg_of_ae
      (corr.nonIdentityMeasure_ae_unitary.mono fun p hp =>
        lightconeIdxBlockRealTerm_nonneg hσr ν q p hp)
  have h_eq :
      (fun q : LightconeIdx =>
        ∫ p, lightconeIdxBlockRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) =
      fun q : LightconeIdx =>
        (ENNReal.ofReal
          (∫ p, lightconeIdxBlockRealTerm ν q σl σr p ∂corr.nonIdentityMeasure)).toReal := by
    ext q
    exact (ENNReal.toReal_ofReal (h_nonneg q)).symm
  rw [h_eq]
  refine ENNReal.summable_toReal ?_
  let g (q : LightconeIdx) (p : ℝ × ℕ) : ℝ :=
    if (p.2 : ℝ) ≤ p.1 then lightconeIdxBlockRealTerm ν q σl σr p else 0
  have hg_meas (q : LightconeIdx) : Measurable (g q) :=
    measurable_lightconeIdxBlockRealTerm ν q σl hσr
  have hg_ae (q : LightconeIdx) : g q =ᵐ[corr.nonIdentityMeasure]
      lightconeIdxBlockRealTerm ν q σl σr :=
    corr.nonIdentityMeasure_ae_unitary.mono fun p hp => ite_eq_left_iff.mpr fun h => (h hp).elim
  have h_lint (q : LightconeIdx) :
      ENNReal.ofReal (∫ p, lightconeIdxBlockRealTerm ν q σl σr p ∂corr.nonIdentityMeasure) =
        ∫⁻ p, ENNReal.ofReal (g q p) ∂corr.nonIdentityMeasure := by
    rw [← integral_congr_ae (hg_ae q)]
    exact ofReal_integral_eq_lintegral_ofReal
      ((corr.integrable_lightconeIdxBlockRealTerm hν hσl hσr q).congr (hg_ae q).symm)
      (Eventually.of_forall fun p => by
        dsimp [g]
        split_ifs with hp
        · exact lightconeIdxBlockRealTerm_nonneg hσr ν q p hp
        · exact le_rfl)
  simp_rw [h_lint]
  rw [← lintegral_tsum (fun q => (hg_meas q).ennreal_ofReal.aemeasurable)]
  have h_tsum_le : ∀ᵐ p : ℝ × ℕ ∂corr.nonIdentityMeasure,
      (∑' q : LightconeIdx, ENNReal.ofReal (g q p)) ≤
        ENNReal.ofReal ‖(conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)‖ := by
    filter_upwards [corr.nonIdentityMeasure_ae_unitary] with p hp
    have hg_eq : (∑' q : LightconeIdx, ENNReal.ofReal (g q p)) =
        ∑' q : LightconeIdx, ENNReal.ofReal (lightconeIdxBlockRealTerm ν q σl σr p) := by
      congr 1 with q
      dsimp [g]
      rw [if_pos hp]
    rw [hg_eq,
      ← ENNReal.ofReal_tsum_of_nonneg (fun q => lightconeIdxBlockRealTerm_nonneg hσr ν q p hp)
        (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).1,
      (summable_and_tsum_lightconeIdxBlockRealTerm hν hσl hσr p hp).2]
    exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
  have h_dom : Integrable
      (fun p : ℝ × ℕ => (conformalBlock ν p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ))
      corr.nonIdentityMeasure :=
    (corr.converges_correlator_pdisk hν hwl hwr).restrict
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae h_tsum_le) ?_)
  exact lt_of_le_of_lt (lintegral_mono fun p => by rw [← ofReal_norm]) h_dom.hasFiniteIntegral

/-- Collinear 1D conformal block expansion of `corr.correlator_pdisk` on $\operatorname{UcPdisk}$:
separating out the identity primary $(0, 0)$ (of unit weight $1$) and summing the non-identity
primaries by effective 1D spin $J = 2k$ ($k \in \mathbb{N}$). -/
theorem correlator_pdisk_eq_one_add_tsum_lightconeMeasure (hν : 0 ≤ ν) {h_gap : ℝ}
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    corr.correlator_pdisk wl wr =
      1 + ∑' k : ℕ,
        ∫ h : ℝ, Complex.exp ((h : ℂ) * wl) * block1d (h + 2 * (k : ℝ)) wr
          ∂(corr.lightconeMeasure (2 * (k : ℤ))) := by
  dsimp [correlator_pdisk, eval_correlator_pdisk]
  have h_split := integral_add_compl (measurableSet_singleton ((0 : ℝ), (0 : ℕ)))
    (corr.converges_correlator_pdisk hν hwl hwr)
  rw [← h_split]
  have h_id_int :
      (∫ p in {((0 : ℝ), (0 : ℕ))},
        (conformalBlock ν p.1 p.2).evalPdisk wl wr ∂corr.mu_measure) = 1 := by
    have h_congr :
        (∫ p in {((0 : ℝ), (0 : ℕ))},
          (conformalBlock ν p.1 p.2).evalPdisk wl wr ∂corr.mu_measure) =
        ∫ _ in {((0 : ℝ), (0 : ℕ))}, (1 : ℂ) ∂corr.mu_measure := by
      refine setIntegral_congr_fun (measurableSet_singleton _) fun p hp => ?_
      rw [mem_singleton_iff.mp hp]
      exact (conformalBlock ν 0 0).evalPdisk_zero wl wr
    rw [h_congr, setIntegral_const, Measure.real,
      corr.mu_measure_singleton_zero_eq_one hν hgap, ENNReal.toReal_one, one_smul]
  rw [h_id_int]
  congr 1
  change (∫ p, (conformalBlock ν p.1 p.2).evalPdisk wl wr ∂corr.nonIdentityMeasure) = _
  have h_sum_norm : Summable (fun q : LightconeIdx =>
      ∫ p, ‖lightconeIdxBlockComplexTerm ν q wl wr p‖ ∂corr.nonIdentityMeasure) := by
    refine (corr.summable_integral_lightconeIdxBlockRealTerm hν hwl hwr).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _) fun q => ?_
    exact integral_mono_ae
      (corr.integrable_lightconeIdxBlockComplexTerm hν hwl hwr q).norm
      (corr.integrable_lightconeIdxBlockRealTerm hν hwl hwr q)
      (corr.nonIdentityMeasure_ae_unitary.mono fun p hp =>
        norm_lightconeIdxBlockComplexTerm_le hwr ν q p hp)
  have h_sum_complex : Summable (fun q : LightconeIdx =>
      ∫ p, lightconeIdxBlockComplexTerm ν q wl wr p ∂corr.nonIdentityMeasure) :=
    Summable.of_norm_bounded h_sum_norm (fun q => norm_integral_le_integral_norm _)
  have h_comm :
      (∫ p, (conformalBlock ν p.1 p.2).evalPdisk wl wr ∂corr.nonIdentityMeasure) =
        ∑' q : LightconeIdx,
          ∫ p, lightconeIdxBlockComplexTerm ν q wl wr p ∂corr.nonIdentityMeasure := by
    refine (integral_congr_ae (corr.nonIdentityMeasure_ae_unitary.mono fun p hp =>
      (summable_and_tsum_lightconeIdxBlockComplexTerm hν hwl hwr p hp).2.symm)).trans ?_
    exact (integral_tsum_of_summable_integral_norm
      (fun q => corr.integrable_lightconeIdxBlockComplexTerm hν hwl hwr q) h_sum_norm).symm
  rw [h_comm, ← (hasSum_fiberwise_lightconeIdxSpin h_sum_complex.hasSum).tsum_eq]
  let f (J : ℤ) (h : ℝ) : ℂ :=
    Complex.exp ((h : ℂ) * wl) * block1dPos (h + (J : ℝ)) wr
  have hf_meas (J : ℤ) : Measurable (f J) := by
    unfold f
    refine Measurable.mul (by fun_prop) ?_
    exact (measurable_block1dPos hwr).comp (measurable_id.add measurable_const)
  have h_J_int (J : ℤ) :
      (∑' q : LightconeIdx,
        if lightconeIdxSpin q = J then
          ∫ p, lightconeIdxBlockComplexTerm ν q wl wr p ∂corr.nonIdentityMeasure
        else 0) =
      ∫ h : ℝ, f J h ∂(corr.lightconeMeasure J) := by
    have h_int_f : Integrable (f J) (corr.lightconeMeasure J) := by
      dsimp [lightconeMeasure]
      refine integrable_sum_measure (fun q => ?_) ?_
      · split_ifs with hq
        · rw [corr.integrable_lightconeAtomMeasure_iff q (hf_meas J).aestronglyMeasurable]
          subst hq
          exact corr.integrable_lightconeIdxBlockComplexTerm hν hwl hwr q
        · exact integrable_zero_measure
      · refine h_sum_norm.of_nonneg_of_le
          (fun q => integral_nonneg fun _ => norm_nonneg _) fun q => ?_
        split_ifs with hq
        · rw [corr.integral_lightconeAtomMeasure q (hf_meas J).norm.aestronglyMeasurable]
          subst hq
          refine le_of_eq (integral_congr_ae (Eventually.of_forall fun p => ?_))
          dsimp [lightconeIdxBlockComplexTerm, f]
          rw [norm_mul (lightconeIdxCoeff ν q p : ℂ),
            Complex.norm_of_nonneg (lightconeIdxCoeff_nonneg ν q p)]
        · rw [integral_zero_measure]
          exact integral_nonneg fun _ => norm_nonneg _
    dsimp [lightconeMeasure] at h_int_f ⊢
    rw [integral_sum_measure h_int_f]
    congr 1 with q
    split_ifs with hq
    · rw [corr.integral_lightconeAtomMeasure q (hf_meas J).aestronglyMeasurable]
      subst hq
      rfl
    · exact (integral_zero_measure _).symm
  simp_rw [h_J_int]
  have h_inj : Function.Injective (fun k : ℕ => (2 * (k : ℤ) : ℤ)) := by
    intro a b hab
    dsimp at hab
    omega
  have h_bij :
      (∑' J : ℤ, ∫ h : ℝ, f J h ∂(corr.lightconeMeasure J)) =
        ∑' k : ℕ, ∫ h : ℝ, f (2 * (k : ℤ)) h ∂(corr.lightconeMeasure (2 * (k : ℤ))) := by
    refine (h_inj.tsum_eq ?_).symm
    intro J hJ_ne
    rw [Function.mem_support] at hJ_ne
    have hJ_nonneg : 0 ≤ J := by
      by_contra h_neg
      push Not at h_neg
      rw [corr.lightconeMeasure_eq_zero_of_neg J h_neg, integral_zero_measure] at hJ_ne
      exact hJ_ne rfl
    have hJ_even : Even J := by
      rcases Int.even_or_odd J with heven | hodd
      · exact heven
      · rw [corr.lightconeMeasure_support_odd_spin J hodd, integral_zero_measure] at hJ_ne
        exact (hJ_ne rfl).elim
    rcases hJ_even with ⟨m, rfl⟩
    have hm_nonneg : 0 ≤ m := by omega
    lift m to ℕ using hm_nonneg
    exact ⟨m, by dsimp; omega⟩
  rw [h_bij]
  congr 1 with k
  have h_unit_k :
      ∀ᵐ h : ℝ ∂(corr.lightconeMeasure (2 * (k : ℤ))),
        h ∉ { h : ℝ | h < 0 ∨ h + ((2 * (k : ℤ) : ℤ) : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (corr.lightconeMeasure_support_unitary (2 * (k : ℤ)))
  refine integral_congr_ae (h_unit_k.mono fun h hh => ?_)
  have h_add_nonneg : 0 ≤ h + ((2 * (k : ℤ) : ℤ) : ℝ) :=
    not_lt.mp fun hlt => hh (Or.inr hlt)
  dsimp [f]
  rw [block1dPos_of_nonneg h_add_nonneg]
  push_cast
  rfl

end FourPointData
