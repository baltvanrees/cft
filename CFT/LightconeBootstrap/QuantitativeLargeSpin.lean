/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.Analysis.LaplaceTauberian
import CFT.LightconeBootstrap.RealLaplaceBound

/-!
# Quantitative Monomial Lightcone Bootstrap

This file combines the quantitative Laplace-to-`C_c^2` Tauberian theorem (`LaplaceTauberian.lean`)
with the uniform real-axis Laplace bounds (`RealLaplaceBound.lean`) to prove the main quantitative
monomial lightcone bootstrap theorems (`exists_const_abs_pairSpin_sub_universal_le` and
`FourPointData.exists_const_abs_pairSpin_sub_universal_le`):

For any reflection-positive CFT (`FourPointData ν Δ_phi` with `ν ≥ 0, Δ_phi > 1/2`) whose monomial
decomposition `M` has a `t`-channel twist gap `h_gap > 0`, and for every support bound `N : ℕ` and
target exponent
`0 < γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`,
there exists `C > 0` such that for all `k ≥ 1` and all twice-differentiable test functions
`φ : ℝ → ℝ` supported in `[-N, N]` with `|φ|, |φ'|, |φ''| ≤ M_φ`:
`|(2k)^(1 - 2Δ_φ) ∫ φ(h) dμ_{2k}(h) - universalMonomialPairing Δ_phi φ| ≤ C * (2k)^(-γ) * M_φ`.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped ENNReal

namespace CFT.LightconeBootstrap

/-! ## 1. Lattice-Shifted Test Functions -/

/-- Test function shifted by `Δ_phi`: `shiftedTest Δ_phi φ u = φ (Δ_phi + u)`. -/
def shiftedTest (Δ_phi : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  φ (Δ_phi + u)

lemma hasDerivAt_shiftedTest (Δ_phi : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (u : ℝ) :
    HasDerivAt (shiftedTest Δ_phi f) (shiftedTest Δ_phi (deriv f) u) u := by
  unfold shiftedTest
  have h1 : HasDerivAt (fun x : ℝ => Δ_phi + x) 1 u :=
    (hasDerivAt_id u).const_add Δ_phi
  have h2 := (hf (Δ_phi + u)).hasDerivAt.comp u h1
  rw [mul_one] at h2
  exact h2

lemma differentiable_shiftedTest (Δ_phi : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (shiftedTest Δ_phi f) :=
  fun u => (hasDerivAt_shiftedTest Δ_phi hf u).differentiableAt

lemma deriv_shiftedTest (Δ_phi : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (shiftedTest Δ_phi f) = shiftedTest Δ_phi (deriv f) := by
  ext u
  exact (hasDerivAt_shiftedTest Δ_phi hf u).deriv

lemma differentiable_deriv_shiftedTest (Δ_phi : ℝ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Differentiable ℝ (deriv (shiftedTest Δ_phi φ)) := by
  rw [deriv_shiftedTest Δ_phi hφ]
  exact differentiable_shiftedTest Δ_phi hφ'

lemma deriv2_shiftedTest (Δ_phi : ℝ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    deriv (deriv (shiftedTest Δ_phi φ)) = shiftedTest Δ_phi (deriv (deriv φ)) := by
  rw [deriv_shiftedTest Δ_phi hφ, deriv_shiftedTest Δ_phi hφ']

lemma shiftedTest_eq_zero_of_support (Δ_phi : ℝ) {N : ℕ} {φ : ℝ → ℝ}
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) {u : ℝ}
    (hu : ((N + ⌈|Δ_phi|⌉₊ : ℕ) : ℝ) < |u|) :
    shiftedTest Δ_phi φ u = 0 := by
  unfold shiftedTest
  refine hsupp (Δ_phi + u) ?_
  have h_tri : |u| ≤ |Δ_phi + u| + |Δ_phi| := by
    have h_eq : u = (Δ_phi + u) - Δ_phi := by ring
    calc
      |u| = |(Δ_phi + u) - Δ_phi| := congrArg abs h_eq
      _ ≤ |Δ_phi + u| + |Δ_phi| := abs_sub _ _
  have h_ceil : |Δ_phi| ≤ (⌈|Δ_phi|⌉₊ : ℝ) := Nat.le_ceil |Δ_phi|
  push_cast at hu
  linarith

/-! ## 2. Lattice-Shifted Rescaled Spin-`2k` Measure -/

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- The lattice-shifted, rescaled spin-`2k` spectral measure on `u = h - Δ_phi ∈ ℝ`:
`dμ̃_{2k}(u) = (2k)^(1 - 2Δ_φ) d((M.mu (2k)).map (h ↦ h - Δ_phi))(u)`. -/
noncomputable def spinShiftedMeasure (Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) •
    (M.mu (2 * (k : ℤ))).map (fun h : ℝ => h - Δ_phi)

lemma integrable_exp_spinShiftedMeasure (Δ_phi : ℝ) (k : ℕ) {σ : ℝ} (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (M.spinShiftedMeasure Δ_phi k) := by
  unfold spinShiftedMeasure
  have h_meas : Measurable (fun h : ℝ => h - Δ_phi) :=
    measurable_id.sub measurable_const
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  have h_map : Integrable (fun u : ℝ => Real.exp (σ * u))
      ((M.mu (2 * (k : ℤ))).map (fun h : ℝ => h - Δ_phi)) := by
    rw [integrable_map_measure h_cont.aestronglyMeasurable h_meas.aemeasurable]
    have h_int :=
      (M.integrable_exp_real hσ (2 * (k : ℤ))).const_mul (Real.exp (-Δ_phi * σ))
    refine h_int.congr (Eventually.of_forall fun h => ?_)
    dsimp [Function.comp_def]
    rw [← Real.exp_add]
    congr 1
    ring
  exact h_map.smul_measure ENNReal.ofReal_ne_top

lemma laplaceTransformReal_spinShiftedMeasure (Δ_phi : ℝ) (k : ℕ) (σ : ℝ) :
    laplaceTransformReal (M.spinShiftedMeasure Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ) := by
  unfold laplaceTransformReal spinShiftedMeasure laplaceSpinReal
  have h_meas : Measurable (fun h : ℝ => h - Δ_phi) :=
    measurable_id.sub measurable_const
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _),
    smul_eq_mul, integral_map h_meas.aemeasurable h_cont.aestronglyMeasurable]
  have h_eq : (fun h : ℝ => Real.exp (σ * (h - Δ_phi))) =
      fun h : ℝ => Real.exp (-Δ_phi * σ) * Real.exp (h * σ) := by
    ext h
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq, integral_const_mul]
  ring

lemma integral_shiftedTest_spinShiftedMeasure (Δ_phi : ℝ) (k : ℕ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(M.spinShiftedMeasure Δ_phi k) =
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ := by
  unfold spinShiftedMeasure shiftedTest pairSpin
  have h_meas : Measurable (fun h : ℝ => h - Δ_phi) :=
    measurable_id.sub measurable_const
  have h_cont : Continuous (fun u : ℝ => φ (Δ_phi + u)) :=
    hφ.comp (continuous_const.add continuous_id)
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _),
    smul_eq_mul, integral_map h_meas.aemeasurable h_cont.aestronglyMeasurable]
  congr 2
  ext h
  rw [add_sub_cancel]

end MonomialFourPointData

/-! ## 3. Universal Shifted Double-Twist Measure on `ℕ ⊂ ℤ` -/

/-- Weight `(2 * 4^(2Δ_φ) / Γ(2Δ_φ)) * (2Δ_φ)_n / n!` of the `n`-th double-twist family. -/
noncomputable def universalCoeff (Δ_phi : ℝ) (n : ℕ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n

lemma universalCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (n : ℕ) :
    0 ≤ universalCoeff Δ_phi n := by
  unfold universalCoeff
  have hG : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos (by positivity)
  exact mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n)

/-- Single Dirac atom `universalCoeff Δ_phi n • δ_n` of the universal double-twist measure. -/
noncomputable def universalAtomMeasure (Δ_phi : ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (universalCoeff Δ_phi n) • Measure.dirac (n : ℝ)

/-- Universal shifted double-twist measure `∑_{n=0}^∞ universalCoeff Δ_phi n • δ_n` on `ℝ`,
supported on `ℕ ⊂ ℤ`. -/
noncomputable def universalShiftedMeasure (Δ_phi : ℝ) : Measure ℝ :=
  Measure.sum (universalAtomMeasure Δ_phi)

lemma universalShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) :
    universalShiftedMeasure Δ_phi (univ \ range (Int.cast : ℤ → ℝ)) = 0 := by
  let S : Set ℝ := univ \ range (Int.cast : ℤ → ℝ)
  have h_range : range (Int.cast : ℤ → ℝ) = ⋃ m : ℤ, {(m : ℝ)} := by
    ext x
    simp
  have hS : MeasurableSet S :=
    MeasurableSet.univ.diff
      (h_range ▸ MeasurableSet.iUnion (fun m : ℤ => measurableSet_singleton (m : ℝ)))
  change universalShiftedMeasure Δ_phi S = 0
  rw [universalShiftedMeasure, Measure.sum_apply _ hS, ENNReal.tsum_eq_zero]
  intro n
  rw [universalAtomMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' (n : ℝ) hS]
  have hn_not_mem : (n : ℝ) ∉ S := by
    intro hn
    exact hn.2 ⟨(n : ℤ), by push_cast; rfl⟩
  rw [Set.indicator_of_notMem hn_not_mem, mul_zero]

lemma integral_universalAtomMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (n : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ u : ℝ, f u ∂(universalAtomMeasure Δ_phi n) =
      universalCoeff Δ_phi n * f (n : ℝ) := by
  rw [universalAtomMeasure, integral_smul_measure,
    integral_dirac' f (n : ℝ) hf.stronglyMeasurable,
    ENNReal.toReal_ofReal (universalCoeff_nonneg hΔ n), smul_eq_mul]

lemma integrable_universalAtomMeasure (Δ_phi : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (universalAtomMeasure Δ_phi n) := by
  have h_dirac : Integrable f (Measure.dirac (n : ℝ)) :=
    integrable_dirac (by simp : ‖f (n : ℝ)‖ₑ < ⊤)
  exact h_dirac.smul_measure ENNReal.ofReal_ne_top

lemma hasSum_universalCoeff_mul_exp (Δ_phi : ℝ) {σ : ℝ} (hσ : σ < 0) :
    HasSum (fun n : ℕ => universalCoeff Δ_phi n * Real.exp (σ * (n : ℝ)))
      (Real.exp (-Δ_phi * σ) * universalLaplaceReal Δ_phi σ) := by
  have h_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]
    exact Real.exp_lt_one_iff.mpr hσ
  have h_sum := (hasSum_one_sub_rpow_neg (2 * Δ_phi) h_abs).mul_left
    (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi))
  have h_target :
      (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
        (1 - Real.exp σ) ^ (- (2 * Δ_phi)) =
        Real.exp (-Δ_phi * σ) * universalLaplaceReal Δ_phi σ := by
    dsimp [universalLaplaceReal]
    have hexp_canc : Real.exp (-Δ_phi * σ) * Real.exp (Δ_phi * σ) = 1 := by
      rw [← Real.exp_add]
      have : -Δ_phi * σ + Δ_phi * σ = 0 := by ring
      rw [this, Real.exp_zero]
    linear_combination
      -((2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
        (1 - Real.exp σ) ^ (- (2 * Δ_phi))) * hexp_canc
  rw [h_target] at h_sum
  refine h_sum.congr_fun fun n => ?_
  dsimp [universalCoeff]
  rw [← Real.exp_nat_mul]
  ring_nf

lemma integrable_exp_universalShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (universalShiftedMeasure Δ_phi) := by
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  refine integrable_sum_measure
    (fun n => integrable_universalAtomMeasure Δ_phi n _) ?_
  have h_sum := (hasSum_universalCoeff_mul_exp Δ_phi hσ).summable
  refine h_sum.congr fun n => ?_
  have h_norm : (fun u : ℝ => ‖Real.exp (σ * u)‖) =
      fun u : ℝ => Real.exp (σ * u) := by
    ext u
    exact Real.norm_of_nonneg (Real.exp_pos _).le
  rw [h_norm, integral_universalAtomMeasure hΔ n h_cont]

lemma laplaceTransformReal_universalShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    laplaceTransformReal (universalShiftedMeasure Δ_phi) σ =
      Real.exp (-Δ_phi * σ) * universalLaplaceReal Δ_phi σ := by
  have h_int := integrable_exp_universalShiftedMeasure hΔ hσ
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  unfold laplaceTransformReal universalShiftedMeasure
  rw [integral_sum_measure h_int]
  simp_rw [integral_universalAtomMeasure hΔ _ h_cont]
  exact (hasSum_universalCoeff_mul_exp Δ_phi hσ).tsum_eq

lemma integral_shiftedTest_universalShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(universalShiftedMeasure Δ_phi) =
      universalMonomialPairing Δ_phi φ := by
  have h_cont : Continuous (shiftedTest Δ_phi φ) :=
    hφ.comp (continuous_const.add continuous_id)
  let N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  have h_vanish : ∀ n ∉ Finset.range (N_shift + 1),
      shiftedTest Δ_phi φ (n : ℝ) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    refine shiftedTest_eq_zero_of_support Δ_phi hsupp ?_
    have h_abs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [h_abs]
    exact_mod_cast hn
  have h_int : Integrable (shiftedTest Δ_phi φ) (universalShiftedMeasure Δ_phi) := by
    refine integrable_sum_measure
      (fun n => integrable_universalAtomMeasure Δ_phi n _) ?_
    refine summable_of_ne_finset_zero (s := Finset.range (N_shift + 1)) (fun n hn => ?_)
    have h_norm : (fun u : ℝ => ‖shiftedTest Δ_phi φ u‖) =
        fun u : ℝ => |shiftedTest Δ_phi φ u| := by
      ext u; exact Real.norm_eq_abs _
    rw [h_norm, integral_universalAtomMeasure hΔ n h_cont.abs, h_vanish n hn,
      abs_zero, mul_zero]
  unfold universalShiftedMeasure universalMonomialPairing
  rw [integral_sum_measure h_int]
  simp_rw [integral_universalAtomMeasure hΔ _ h_cont]
  dsimp [universalCoeff, pochhammerCoeff, shiftedTest]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-! ## 3b. Exact Finite-Spin `t`-Channel Identity Measure on `ℕ ⊂ ℤ` -/

/-- Exact finite-spin weight of the `n`-th double-twist family at spin `2k`, rescaled by
`(2k)^(1 - 2Δ_φ)`:
`(2k)^(1 - 2Δ_φ) * 2 * 4^(2Δ_φ) * ((2Δ_φ)_n / n!) * ((2Δ_φ)_{n + 2k} / (n + 2k)!)`.
Retaining `((2Δ_φ)_{n + 2k} / (n + 2k)!)` instead of its `k → ∞` Gamma limit includes all
`1 / (2k)^m` subleading `t`-channel identity corrections. -/
noncomputable def identityRescaledCoeff (Δ_phi : ℝ) (k n : ℕ) : ℝ :=
  (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (2 * (4 : ℝ) ^ (2 * Δ_phi)) *
    pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + 2 * k)

lemma identityRescaledCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k n : ℕ) :
    0 ≤ identityRescaledCoeff Δ_phi k n := by
  unfold identityRescaledCoeff
  exact mul_nonneg
    (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
    (pochhammerCoeff_nonneg (by positivity) (n + 2 * k))

/-- Single Dirac atom `identityRescaledCoeff Δ_phi k n • δ_n` of the exact `t`-channel identity
shifted measure. -/
noncomputable def identityAtomMeasure (Δ_phi : ℝ) (k n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (identityRescaledCoeff Δ_phi k n) • Measure.dirac (n : ℝ)

/-- Exact finite-spin `t`-channel identity shifted measure
`∑_{n=0}^∞ identityRescaledCoeff Δ_phi k n • δ_n` on `ℝ`, supported on `ℕ ⊂ ℤ`. -/
noncomputable def identityShiftedMeasure (Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  Measure.sum (identityAtomMeasure Δ_phi k)

lemma identityShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) (k : ℕ) :
    identityShiftedMeasure Δ_phi k (univ \ range (Int.cast : ℤ → ℝ)) = 0 := by
  let S : Set ℝ := univ \ range (Int.cast : ℤ → ℝ)
  have h_range : range (Int.cast : ℤ → ℝ) = ⋃ m : ℤ, {(m : ℝ)} := by
    ext x
    simp
  have hS : MeasurableSet S :=
    MeasurableSet.univ.diff
      (h_range ▸ MeasurableSet.iUnion (fun m : ℤ => measurableSet_singleton (m : ℝ)))
  change identityShiftedMeasure Δ_phi k S = 0
  rw [identityShiftedMeasure, Measure.sum_apply _ hS, ENNReal.tsum_eq_zero]
  intro n
  rw [identityAtomMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' (n : ℝ) hS]
  have hn_not_mem : (n : ℝ) ∉ S := by
    intro hn
    exact hn.2 ⟨(n : ℤ), by push_cast; rfl⟩
  rw [Set.indicator_of_notMem hn_not_mem, mul_zero]

lemma integral_identityAtomMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k n : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ u : ℝ, f u ∂(identityAtomMeasure Δ_phi k n) =
      identityRescaledCoeff Δ_phi k n * f (n : ℝ) := by
  rw [identityAtomMeasure, integral_smul_measure,
    integral_dirac' f (n : ℝ) hf.stronglyMeasurable,
    ENNReal.toReal_ofReal (identityRescaledCoeff_nonneg hΔ k n), smul_eq_mul]

lemma integrable_identityAtomMeasure (Δ_phi : ℝ) (k n : ℕ) (f : ℝ → ℝ) :
    Integrable f (identityAtomMeasure Δ_phi k n) := by
  have h_dirac : Integrable f (Measure.dirac (n : ℝ)) :=
    integrable_dirac (by simp : ‖f (n : ℝ)‖ₑ < ⊤)
  exact h_dirac.smul_measure ENNReal.ofReal_ne_top

lemma summable_pochhammerCoeff_mul_shift_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ)
    {σ : ℝ} (hσ : σ < 0) :
    Summable (fun n : ℕ =>
      pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) *
        (Real.exp σ) ^ n) := by
  have h2Δ : 0 < 2 * Δ_phi := by positivity
  obtain ⟨B, hB_pos, hB⟩ := exists_bound_rpow_mul_pochhammerCoeff h2Δ
  set p : ℕ := ⌈|2 * Δ_phi - 1|⌉₊
  have h_abs_q : |Real.exp (σ / 2)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h_sum_q := hasSum_one_sub_rpow_neg (2 * Δ_phi) h_abs_q
  set A_p : ℝ := (1 + (-(σ) / (2 * ((p : ℝ) + 1)))⁻¹) ^ p
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (mul_nonneg (pochhammerCoeff_nonneg h2Δ.le n)
        (pochhammerCoeff_nonneg h2Δ.le (n + K)))
      (by positivity))
    (fun n => ?_)
    (h_sum_q.summable.mul_left ((B + 1) * (1 + (K : ℝ)) ^ p * A_p))
  have h_pow_exp := one_add_natCast_pow_mul_exp_le p hσ le_rfl n
  have h_coeff :
      pochhammerCoeff (2 * Δ_phi) (n + K) ≤
        (B + 1) * (1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p := by
    rcases eq_or_ne (n + K) 0 with h0 | hne
    · rw [h0, pochhammerCoeff_zero]
      have h1 : (1 : ℝ) ≤ (1 + (K : ℝ)) ^ p :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) K])
      have h2 : (1 : ℝ) ≤ (1 + (n : ℝ)) ^ p :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (B + 1) * (1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p :=
            mul_le_mul (mul_le_mul (by linarith) h1 zero_le_one (by positivity))
              h2 zero_le_one (by positivity)
    · have hnK_pos : (0 : ℝ) < ((n + K : ℕ) : ℝ) :=
        by exact_mod_cast (Nat.pos_of_ne_zero hne)
      have hnK_ge1 : (1 : ℝ) ≤ ((n + K : ℕ) : ℝ) :=
        by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
      have h_id : pochhammerCoeff (2 * Δ_phi) (n + K) =
          (((n + K : ℕ) : ℝ) ^ (1 - 2 * Δ_phi) * pochhammerCoeff (2 * Δ_phi) (n + K)) *
            ((n + K : ℕ) : ℝ) ^ (2 * Δ_phi - 1) := by
        rw [mul_right_comm, ← Real.rpow_add hnK_pos]
        have : (1 - 2 * Δ_phi) + (2 * Δ_phi - 1) = 0 := by ring
        rw [this, Real.rpow_zero, one_mul]
      have h_rpow_le : ((n + K : ℕ) : ℝ) ^ (2 * Δ_phi - 1) ≤
          (1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p := by
        have hp_ge : 2 * Δ_phi - 1 ≤ (p : ℝ) :=
          (le_abs_self _).trans (Nat.le_ceil _)
        have h1 : ((n + K : ℕ) : ℝ) ^ (2 * Δ_phi - 1) ≤ ((n + K : ℕ) : ℝ) ^ (p : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnK_ge1 hp_ge
        rw [Real.rpow_natCast] at h1
        have h_base : ((n + K : ℕ) : ℝ) ≤ (1 + (K : ℝ)) * (1 + (n : ℝ)) := by
          push_cast
          nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) K]
        have h2 : ((n + K : ℕ) : ℝ) ^ p ≤ ((1 + (K : ℝ)) * (1 + (n : ℝ))) ^ p :=
          pow_le_pow_left₀ hnK_pos.le h_base p
        rw [mul_pow] at h2
        exact h1.trans h2
      rw [h_id]
      calc
        (((n + K : ℕ) : ℝ) ^ (1 - 2 * Δ_phi) * pochhammerCoeff (2 * Δ_phi) (n + K)) *
            ((n + K : ℕ) : ℝ) ^ (2 * Δ_phi - 1)
          ≤ (B + 1) * ((1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p) :=
            mul_le_mul
              ((hB (n + K)).trans (by linarith))
              h_rpow_le (by positivity) (by positivity)
        _ = (B + 1) * (1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p := by ring
  calc
    pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) * (Real.exp σ) ^ n
      ≤ pochhammerCoeff (2 * Δ_phi) n *
          ((B + 1) * (1 + (K : ℝ)) ^ p * (1 + (n : ℝ)) ^ p) * (Real.exp σ) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_coeff (pochhammerCoeff_nonneg h2Δ.le n))
          (by positivity)
    _ = (B + 1) * (1 + (K : ℝ)) ^ p * pochhammerCoeff (2 * Δ_phi) n *
          ((1 + (n : ℝ)) ^ p * (Real.exp σ) ^ n) := by ring
    _ ≤ (B + 1) * (1 + (K : ℝ)) ^ p * pochhammerCoeff (2 * Δ_phi) n *
          (A_p * (Real.exp (σ / 2)) ^ n) :=
        mul_le_mul_of_nonneg_left h_pow_exp
          (mul_nonneg (by positivity) (pochhammerCoeff_nonneg h2Δ.le n))
    _ = (B + 1) * (1 + (K : ℝ)) ^ p * A_p *
          (pochhammerCoeff (2 * Δ_phi) n * (Real.exp (σ / 2)) ^ n) := by ring

lemma hasSum_identityRescaledCoeff_mul_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k : ℕ)
    {σ : ℝ} (hσ : σ < 0) :
    HasSum (fun n : ℕ => identityRescaledCoeff Δ_phi k n * Real.exp (σ * (n : ℝ)))
      (Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ)) := by
  have h_sum :=
    (summable_pochhammerCoeff_mul_shift_exp hΔ (2 * k) hσ).hasSum.mul_left
      ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (2 * (4 : ℝ) ^ (2 * Δ_phi)))
  have h_target :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (2 * (4 : ℝ) ^ (2 * Δ_phi)) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
          pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ) := by
    dsimp [identityLaplaceReal]
    have hexp_canc : Real.exp (-Δ_phi * σ) * Real.exp (Δ_phi * σ) = 1 := by
      rw [← Real.exp_add]
      have : -Δ_phi * σ + Δ_phi * σ = 0 := by ring
      rw [this, Real.exp_zero]
    linear_combination
      -((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (2 * (4 : ℝ) ^ (2 * Δ_phi)) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
          pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n)) * hexp_canc
  rw [h_target] at h_sum
  refine h_sum.congr_fun fun n => ?_
  dsimp [identityRescaledCoeff]
  rw [← Real.exp_nat_mul]
  ring_nf

lemma integrable_exp_identityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (k : ℕ) (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (identityShiftedMeasure Δ_phi k) := by
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  refine integrable_sum_measure
    (fun n => integrable_identityAtomMeasure Δ_phi k n _) ?_
  have h_sum := (hasSum_identityRescaledCoeff_mul_exp hΔ k hσ).summable
  refine h_sum.congr fun n => ?_
  have h_norm : (fun u : ℝ => ‖Real.exp (σ * u)‖) =
      fun u : ℝ => Real.exp (σ * u) := by
    ext u
    exact Real.norm_of_nonneg (Real.exp_pos _).le
  rw [h_norm, integral_identityAtomMeasure hΔ k n h_cont]

lemma laplaceTransformReal_identityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (k : ℕ) (hσ : σ < 0) :
    laplaceTransformReal (identityShiftedMeasure Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ) := by
  have h_int := integrable_exp_identityShiftedMeasure hΔ k hσ
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  unfold laplaceTransformReal identityShiftedMeasure
  rw [integral_sum_measure h_int]
  simp_rw [integral_identityAtomMeasure hΔ k _ h_cont]
  exact (hasSum_identityRescaledCoeff_mul_exp hΔ k hσ).tsum_eq

lemma integral_shiftedTest_identityShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (k N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(identityShiftedMeasure Δ_phi k) =
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ := by
  have h_cont : Continuous (shiftedTest Δ_phi φ) :=
    hφ.comp (continuous_const.add continuous_id)
  let N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  have h_vanish : ∀ n ∉ Finset.range (N_shift + 1),
      shiftedTest Δ_phi φ (n : ℝ) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    refine shiftedTest_eq_zero_of_support Δ_phi hsupp ?_
    have h_abs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [h_abs]
    exact_mod_cast hn
  have h_int : Integrable (shiftedTest Δ_phi φ) (identityShiftedMeasure Δ_phi k) := by
    refine integrable_sum_measure
      (fun n => integrable_identityAtomMeasure Δ_phi k n _) ?_
    refine summable_of_ne_finset_zero (s := Finset.range (N_shift + 1)) (fun n hn => ?_)
    have h_norm : (fun u : ℝ => ‖shiftedTest Δ_phi φ u‖) =
        fun u : ℝ => |shiftedTest Δ_phi φ u| := by
      ext u; exact Real.norm_eq_abs _
    rw [h_norm, integral_identityAtomMeasure hΔ k n h_cont.abs, h_vanish n hn,
      abs_zero, mul_zero]
  unfold identityShiftedMeasure identityMonomialPairing
  rw [integral_sum_measure h_int]
  simp_rw [integral_identityAtomMeasure hΔ k _ h_cont]
  dsimp [identityRescaledCoeff, shiftedTest]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-! ## 4. Main Quantitative Monomial Lightcone Bootstrap Theorems -/

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- **Quantitative Monomial Lightcone Bootstrap Theorem (`MonomialFourPointData` version)**:
Let `M` be a monomial four-point decomposition agreeing with `corr : FourPointData ν Δ_phi`
(`ν ≥ 0`, `Δ_phi > 1/2`) and having a `t`-channel twist gap `h_gap > 0`.
For every support bound `N : ℕ` and every target exponent
`0 < γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`,
there exists a constant `C > 0` such that for all `k ≥ 1` and all twice-differentiable test
functions `φ : ℝ → ℝ` supported in `[-N, N]` with `|φ|, |φ'|, |φ''| ≤ M_φ`,
`|(2k)^(1 - 2Δ_φ) M.pairSpin (2k) φ - universalMonomialPairing Δ_phi φ| ≤`
`C * (2k)^(-γ) * M_φ`. -/
theorem exists_const_abs_pairSpin_sub_universal_le {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hγ_2h : γ < 2 * h_gap := lt_of_lt_of_le hγ_lt (min_le_left _ _)
  have hγ_rest : γ < min 1 (2 * Δ_phi - 1) := lt_of_lt_of_le hγ_lt (min_le_right _ _)
  set h' : ℝ := if 2 * (h_gap - Δ_phi) = -1 then (γ / 2 + h_gap) / 2 else h_gap
  have hh'_pos : 0 < h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_le : h' ≤ h_gap := by dsimp [h']; split_ifs <;> linarith
  have hγ_2h' : γ < 2 * h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_ne : 2 * (h' - Δ_phi) ≠ -1 := by
    dsimp [h']
    split_ifs with h_eq
    · linarith
    · exact h_eq
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set α : ℝ := min (2 * h') (min 1 (2 * Δ_phi - 1))
  have hγα : γ < α := lt_min hγ_2h' hγ_rest
  have hα_pos : 0 < α := lt_trans hγ_pos hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγα
  have hσ_le : 1 - 2 * A ≤ -1 := by linarith
  have hσ_plus : (-1 : ℝ) < 0 := by norm_num
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    M.exists_uniform_laplaceSpinReal_bounds corr hν hΔ hM hgap' hh'_ne hσ_le hσ_plus
  set E_A : ℝ := Real.exp (-Δ_phi * (1 - 2 * A))
  have hEA_pos : 0 < E_A := Real.exp_pos _
  set M_A : ℝ := E_A * M_raw
  have hMA_pos : 0 < M_A := mul_pos hEA_pos hM_raw_pos
  set C_A : ℝ := E_A * C_raw
  have hCA_pos : 0 < C_A := mul_pos hEA_pos hC_raw_pos
  set N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  let θ := midpointHarmonicExp A (2 * π)
  let M' := max M_A C_A
  have hM'_pos : 0 < M' := lt_of_lt_of_le hMA_pos (le_max_left M_A C_A)
  let C := hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
    (M' ^ (1 - θ) * C_A ^ θ)
  have hC_pos : 0 < C := by
    dsimp [C]
    have hN : 0 < hermiteConstant N_shift := hermiteConstant_pos N_shift
    positivity
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  let μ_k := M.spinShiftedMeasure Δ_phi k
  let ν_u := universalShiftedMeasure Δ_phi
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  let δ := C_A * (2 * (k : ℝ)) ^ (-α)
  have hδ_pos : 0 < δ := by positivity
  have hJ_rpow_le_one : (2 * (k : ℝ)) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2k_ge1 (by linarith)
  have hδ_le_M' : δ ≤ M' := by
    calc
      C_A * (2 * (k : ℝ)) ^ (-α) ≤ C_A * 1 :=
        mul_le_mul_of_nonneg_left hJ_rpow_le_one hCA_pos.le
      _ = C_A := mul_one C_A
      _ ≤ M' := le_max_right M_A C_A
  have hM'_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal μ_k σ + laplaceTransformReal ν_u σ ≤ M' := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_spinShiftedMeasure Δ_phi k σ,
      laplaceTransformReal_universalShiftedMeasure hΔ_pos hσ_neg, ← mul_add]
    have hexp_le : Real.exp (-Δ_phi * σ) ≤ E_A :=
      Real.exp_le_exp.mpr (by nlinarith [hσ.1])
    have h_sum_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
          universalLaplaceReal Δ_phi σ :=
      add_nonneg
        (mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _))
        (universalLaplaceReal_nonneg hΔ_pos hσ_neg)
    have h1 :
        Real.exp (-Δ_phi * σ) *
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
            universalLaplaceReal Δ_phi σ) ≤ M_A :=
      mul_le_mul hexp_le (h_raw hk1 hσ).1 h_sum_nonneg hEA_pos.le
    exact h1.trans (le_max_left M_A C_A)
  have hδ_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal μ_k σ - laplaceTransformReal ν_u σ| ≤ δ := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_spinShiftedMeasure Δ_phi k σ,
      laplaceTransformReal_universalShiftedMeasure hΔ_pos hσ_neg,
      ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (-Δ_phi * σ) ≤ E_A :=
      Real.exp_le_exp.mpr (by nlinarith [hσ.1])
    calc
      Real.exp (-Δ_phi * σ) *
          |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
            universalLaplaceReal Δ_phi σ|
        ≤ E_A * (C_raw * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul hexp_le (h_raw hk1 hσ).2 (abs_nonneg _) hEA_pos.le
      _ = δ := by dsimp [δ, C_A]; ring
  have h_taub := abs_integral_sub_le_of_laplaceReal_bound hA hδ_pos hδ_le_M'
    (universalShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (M.integrable_exp_spinShiftedMeasure Δ_phi k (by linarith))
    (M.integrable_exp_spinShiftedMeasure Δ_phi k hσ_plus)
    (integrable_exp_universalShiftedMeasure hΔ_pos (by linarith))
    (integrable_exp_universalShiftedMeasure hΔ_pos hσ_plus)
    hM'_bd hδ_bd N_shift
    (differentiable_shiftedTest Δ_phi hφ)
    (differentiable_deriv_shiftedTest Δ_phi hφ hφ')
    (fun u hu => shiftedTest_eq_zero_of_support Δ_phi hsupp hu)
    hM_φ
    (fun u => hφ0 (Δ_phi + u))
    (fun u => by rw [deriv_shiftedTest Δ_phi hφ]; exact hφ1 (Δ_phi + u))
    (fun u => by rw [deriv2_shiftedTest Δ_phi hφ hφ']; exact hφ2 (Δ_phi + u))
  rw [M.integral_shiftedTest_spinShiftedMeasure Δ_phi k hφ.continuous,
    integral_shiftedTest_universalShiftedMeasure hΔ_pos N hφ.continuous hsupp] at h_taub
  have hθ_pos : 0 < θ := midpointHarmonicExp_pos hA (by positivity)
  have hδ_rpow : δ ^ θ ≤ C_A ^ θ * (2 * (k : ℝ)) ^ (-γ) := by
    dsimp [δ]
    rw [Real.mul_rpow hCA_pos.le (Real.rpow_nonneg h2k_pos.le _),
      ← Real.rpow_mul h2k_pos.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hCA_pos.le θ)
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_const_nonneg :
      0 ≤ hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
        M' ^ (1 - θ) := by
    have hN : 0 < hermiteConstant N_shift := hermiteConstant_pos N_shift
    positivity
  calc
    |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ|
      ≤ hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          (M' ^ (1 - θ) * δ ^ θ) * M_φ := h_taub
    _ = (hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          M' ^ (1 - θ)) * δ ^ θ * M_φ := by ring
    _ ≤ (hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          M' ^ (1 - θ)) * (C_A ^ θ * (2 * (k : ℝ)) ^ (-γ)) * M_φ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ_rpow h_const_nonneg) hM_φ
    _ = C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by dsimp [C]; ring

/-- Version of `exists_const_abs_pairSpin_sub_universal_le` assuming `ContDiff ℝ 2 φ`. -/
theorem exists_const_abs_pairSpin_sub_universal_le_contDiff {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    M.exists_const_abs_pairSpin_sub_universal_le corr hν hΔ hM hgap hγ_pos hγ_lt N
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_succ : ContDiff ℝ (1 + 1) φ := hφ
  have hφ'_diff : Differentiable ℝ (deriv φ) :=
    ((contDiff_succ_iff_deriv.mp hφ_succ).2.2).differentiable (by norm_num)
  exact hC hk1 hφ_diff hφ'_diff hsupp hM_φ hφ0 hφ1 hφ2

/-- **Quantitative Monomial Lightcone Bootstrap Against the Exact `t`-Channel Identity**:
Retaining the exact finite-spin `t`-channel identity binomial coefficients in
`identityMonomialPairing Δ_phi (2k) φ` includes all `1 / (2k)^m` subleading `t`-channel identity
corrections on the left-hand side, removing the `1` cap from the exponent and yielding
`0 < γ < min (2 * h_gap) (2 * Δ_phi - 1)`:
`|(2k)^(1 - 2Δ_φ) (M.pairSpin (2k) φ - identityMonomialPairing Δ_phi (2k) φ)| ≤`
`C * (2k)^(-γ) * M_φ`. -/
theorem exists_const_abs_pairSpin_sub_identity_le {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hγ_2h : γ < 2 * h_gap := lt_of_lt_of_le hγ_lt (min_le_left _ _)
  have hγ_rest : γ < 2 * Δ_phi - 1 := lt_of_lt_of_le hγ_lt (min_le_right _ _)
  set h' : ℝ := if 2 * (h_gap - Δ_phi) = -1 then (γ / 2 + h_gap) / 2 else h_gap
  have hh'_pos : 0 < h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_le : h' ≤ h_gap := by dsimp [h']; split_ifs <;> linarith
  have hγ_2h' : γ < 2 * h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_ne : 2 * (h' - Δ_phi) ≠ -1 := by
    dsimp [h']
    split_ifs with h_eq
    · linarith
    · exact h_eq
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set α : ℝ := min (2 * h') (2 * Δ_phi - 1)
  have hγα : γ < α := lt_min hγ_2h' hγ_rest
  have hα_pos : 0 < α := lt_trans hγ_pos hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγα
  have hσ_le : 1 - 2 * A ≤ -1 := by linarith
  have hσ_plus : (-1 : ℝ) < 0 := by norm_num
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    M.exists_uniform_laplaceSpinReal_sub_identity_bounds
      corr hν hΔ hM hgap' hh'_ne hσ_le hσ_plus
  set E_A : ℝ := Real.exp (-Δ_phi * (1 - 2 * A))
  have hEA_pos : 0 < E_A := Real.exp_pos _
  set M_A : ℝ := E_A * M_raw
  have hMA_pos : 0 < M_A := mul_pos hEA_pos hM_raw_pos
  set C_A : ℝ := E_A * C_raw
  have hCA_pos : 0 < C_A := mul_pos hEA_pos hC_raw_pos
  set N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  let θ := midpointHarmonicExp A (2 * π)
  let M' := max M_A C_A
  have hM'_pos : 0 < M' := lt_of_lt_of_le hMA_pos (le_max_left M_A C_A)
  let C := hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
    (M' ^ (1 - θ) * C_A ^ θ)
  have hC_pos : 0 < C := by
    dsimp [C]
    have hN : 0 < hermiteConstant N_shift := hermiteConstant_pos N_shift
    positivity
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  let μ_k := M.spinShiftedMeasure Δ_phi k
  let ν_k := identityShiftedMeasure Δ_phi k
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  let δ := C_A * (2 * (k : ℝ)) ^ (-α)
  have hδ_pos : 0 < δ := by positivity
  have hJ_rpow_le_one : (2 * (k : ℝ)) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2k_ge1 (by linarith)
  have hδ_le_M' : δ ≤ M' := by
    calc
      C_A * (2 * (k : ℝ)) ^ (-α) ≤ C_A * 1 :=
        mul_le_mul_of_nonneg_left hJ_rpow_le_one hCA_pos.le
      _ = C_A := mul_one C_A
      _ ≤ M' := le_max_right M_A C_A
  have hM'_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal μ_k σ + laplaceTransformReal ν_k σ ≤ M' := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_spinShiftedMeasure Δ_phi k σ,
      laplaceTransformReal_identityShiftedMeasure hΔ_pos k hσ_neg, ← mul_add]
    have hexp_le : Real.exp (-Δ_phi * σ) ≤ E_A :=
      Real.exp_le_exp.mpr (by nlinarith [hσ.1])
    have h_sum_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ :=
      add_nonneg
        (mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _))
        (mul_nonneg (by positivity) (identityLaplaceReal_nonneg hΔ_pos (2 * k) σ))
    have h1 :
        Real.exp (-Δ_phi * σ) *
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ) ≤ M_A :=
      mul_le_mul hexp_le (h_raw hk1 hσ).1 h_sum_nonneg hEA_pos.le
    exact h1.trans (le_max_left M_A C_A)
  have hδ_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal μ_k σ - laplaceTransformReal ν_k σ| ≤ δ := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_spinShiftedMeasure Δ_phi k σ,
      laplaceTransformReal_identityShiftedMeasure hΔ_pos k hσ_neg,
      ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (-Δ_phi * σ) ≤ E_A :=
      Real.exp_le_exp.mpr (by nlinarith [hσ.1])
    calc
      Real.exp (-Δ_phi * σ) *
          |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ|
        ≤ E_A * (C_raw * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul hexp_le (h_raw hk1 hσ).2 (abs_nonneg _) hEA_pos.le
      _ = δ := by dsimp [δ, C_A]; ring
  have h_taub := abs_integral_sub_le_of_laplaceReal_bound hA hδ_pos hδ_le_M'
    (identityShiftedMeasure_compl_intCast_eq_zero Δ_phi k)
    (M.integrable_exp_spinShiftedMeasure Δ_phi k (by linarith))
    (M.integrable_exp_spinShiftedMeasure Δ_phi k hσ_plus)
    (integrable_exp_identityShiftedMeasure hΔ_pos k (by linarith))
    (integrable_exp_identityShiftedMeasure hΔ_pos k hσ_plus)
    hM'_bd hδ_bd N_shift
    (differentiable_shiftedTest Δ_phi hφ)
    (differentiable_deriv_shiftedTest Δ_phi hφ hφ')
    (fun u hu => shiftedTest_eq_zero_of_support Δ_phi hsupp hu)
    hM_φ
    (fun u => hφ0 (Δ_phi + u))
    (fun u => by rw [deriv_shiftedTest Δ_phi hφ]; exact hφ1 (Δ_phi + u))
    (fun u => by rw [deriv2_shiftedTest Δ_phi hφ hφ']; exact hφ2 (Δ_phi + u))
  rw [M.integral_shiftedTest_spinShiftedMeasure Δ_phi k hφ.continuous,
    integral_shiftedTest_identityShiftedMeasure hΔ_pos k N hφ.continuous hsupp] at h_taub
  have hθ_pos : 0 < θ := midpointHarmonicExp_pos hA (by positivity)
  have hδ_rpow : δ ^ θ ≤ C_A ^ θ * (2 * (k : ℝ)) ^ (-γ) := by
    dsimp [δ]
    rw [Real.mul_rpow hCA_pos.le (Real.rpow_nonneg h2k_pos.le _),
      ← Real.rpow_mul h2k_pos.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hCA_pos.le θ)
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_const_nonneg :
      0 ≤ hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
        M' ^ (1 - θ) := by
    have hN : 0 < hermiteConstant N_shift := hermiteConstant_pos N_shift
    positivity
  calc
    |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ|
      ≤ hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          (M' ^ (1 - θ) * δ ^ θ) * M_φ := h_taub
    _ = (hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          M' ^ (1 - θ)) * δ ^ θ * M_φ := by ring
    _ ≤ (hermiteConstant N_shift * (A + 1) ^ 2 * Real.exp (A * (N_shift : ℝ)) *
          M' ^ (1 - θ)) * (C_A ^ θ * (2 * (k : ℝ)) ^ (-γ)) * M_φ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ_rpow h_const_nonneg) hM_φ
    _ = C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by dsimp [C]; ring

/-- Version of `exists_const_abs_pairSpin_sub_identity_le` assuming `ContDiff ℝ 2 φ`. -/
theorem exists_const_abs_pairSpin_sub_identity_le_contDiff {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    M.exists_const_abs_pairSpin_sub_identity_le corr hν hΔ hM hgap hγ_pos hγ_lt N
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_succ : ContDiff ℝ (1 + 1) φ := hφ
  have hφ'_diff : Differentiable ℝ (deriv φ) :=
    ((contDiff_succ_iff_deriv.mp hφ_succ).2.2).differentiable (by norm_num)
  exact hC hk1 hφ_diff hφ'_diff hsupp hM_φ hφ0 hφ1 hφ2

end MonomialFourPointData

end CFT.LightconeBootstrap

open CFT.LightconeBootstrap

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- **Quantitative Monomial Lightcone Bootstrap Theorem (`FourPointData` version)**:
For any reflection-positive CFT (`FourPointData ν Δ_phi` with `ν ≥ 0, Δ_phi > 1/2`) whose
canonical monomial decomposition `corr.toMonomialFourPointData hν` has a twist gap `h_gap > 0`,
and for every support bound `N : ℕ` and target exponent
`0 < γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`,
there exists `C > 0` such that for all `k ≥ 1` and all `C^2` test functions `φ` supported in
`[-N, N]` with `|φ|, |φ'|, |φ''| ≤ M_φ`,
`|(2k)^(1 - 2Δ_φ) (corr.toMonomialFourPointData hν).pairSpin (2k) φ -`
`universalMonomialPairing Δ_phi φ| ≤ C * (2k)^(-γ) * M_φ`. -/
theorem exists_const_abs_pairSpin_sub_universal_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (corr.toMonomialFourPointData hν).pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  (corr.toMonomialFourPointData hν).exists_const_abs_pairSpin_sub_universal_le_contDiff
    corr hν hΔ (fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr)
    hgap hγ_pos hγ_lt N

/-- **Quantitative Monomial Lightcone Bootstrap Against the Exact `t`-Channel Identity
(`FourPointData` version)**:
Retaining the exact finite-spin `t`-channel identity binomial coefficients in
`identityMonomialPairing Δ_phi (2k) φ` includes all `1 / (2k)^m` subleading `t`-channel identity
corrections on the left-hand side and yields the sharper exponent range
`0 < γ < min (2 * h_gap) (2 * Δ_phi - 1)`. -/
theorem exists_const_abs_pairSpin_sub_identity_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (corr.toMonomialFourPointData hν).pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          identityMonomialPairing Δ_phi (2 * k) φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  (corr.toMonomialFourPointData hν).exists_const_abs_pairSpin_sub_identity_le_contDiff
    corr hν hΔ (fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr)
    hgap hγ_pos hγ_lt N

end FourPointData
