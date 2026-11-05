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

/-- The lattice-shifted, `(2k)^s`-rescaled spin-`2k` spectral measure on `u = h - Δ_phi ∈ ℝ`:
`dμ̃_{2k}(u) = (2k)^s d((M.mu (2k)).map (h ↦ h - Δ_phi))(u)`. -/
noncomputable def rescaledShiftedMeasure (s Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((2 * (k : ℝ)) ^ s) •
    (M.mu (2 * (k : ℤ))).map (fun h : ℝ => h - Δ_phi)

lemma integrable_exp_rescaledShiftedMeasure (s Δ_phi : ℝ) (k : ℕ) {σ : ℝ} (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (M.rescaledShiftedMeasure s Δ_phi k) := by
  unfold rescaledShiftedMeasure
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

lemma laplaceTransformReal_rescaledShiftedMeasure (s Δ_phi : ℝ) (k : ℕ) (σ : ℝ) :
    laplaceTransformReal (M.rescaledShiftedMeasure s Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ) := by
  unfold laplaceTransformReal rescaledShiftedMeasure laplaceSpinReal
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

lemma integral_shiftedTest_rescaledShiftedMeasure (s Δ_phi : ℝ) (k : ℕ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(M.rescaledShiftedMeasure s Δ_phi k) =
      (2 * (k : ℝ)) ^ s * M.pairSpin (2 * (k : ℤ)) φ := by
  unfold rescaledShiftedMeasure shiftedTest pairSpin
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

/-! ## 3. General Discrete `ℕ`-Supported Measures & Universal/Identity Specializations -/

/-- Single Dirac atom `c n • δ_n` of a discrete `ℕ`-supported measure on `ℝ`. -/
noncomputable def natAtomMeasure (c : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (c n) • Measure.dirac (n : ℝ)

/-- Discrete measure `∑_{n=0}^∞ c n • δ_n` on `ℝ`, supported on `ℕ ⊂ ℤ`. -/
noncomputable def natShiftedMeasure (c : ℕ → ℝ) : Measure ℝ :=
  Measure.sum (natAtomMeasure c)

lemma natShiftedMeasure_compl_intCast_eq_zero (c : ℕ → ℝ) :
    natShiftedMeasure c (univ \ range (Int.cast : ℤ → ℝ)) = 0 := by
  let S : Set ℝ := univ \ range (Int.cast : ℤ → ℝ)
  have h_range : range (Int.cast : ℤ → ℝ) = ⋃ m : ℤ, {(m : ℝ)} := by
    ext x; simp
  have hS : MeasurableSet S :=
    MeasurableSet.univ.diff
      (h_range ▸ MeasurableSet.iUnion (fun m : ℤ => measurableSet_singleton (m : ℝ)))
  change natShiftedMeasure c S = 0
  rw [natShiftedMeasure, Measure.sum_apply _ hS, ENNReal.tsum_eq_zero]
  intro n
  rw [natAtomMeasure, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' (n : ℝ) hS]
  have hn_not_mem : (n : ℝ) ∉ S := by
    intro hn
    exact hn.2 ⟨(n : ℤ), by push_cast; rfl⟩
  rw [Set.indicator_of_notMem hn_not_mem, mul_zero]

lemma integral_natAtomMeasure {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (n : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ u : ℝ, f u ∂(natAtomMeasure c n) = c n * f (n : ℝ) := by
  rw [natAtomMeasure, integral_smul_measure,
    integral_dirac' f (n : ℝ) hf.stronglyMeasurable,
    ENNReal.toReal_ofReal (hc n), smul_eq_mul]

lemma integrable_natAtomMeasure (c : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (natAtomMeasure c n) := by
  have h_dirac : Integrable f (Measure.dirac (n : ℝ)) :=
    integrable_dirac (by simp : ‖f (n : ℝ)‖ₑ < ⊤)
  exact h_dirac.smul_measure ENNReal.ofReal_ne_top

lemma integrable_exp_natShiftedMeasure {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {σ S : ℝ}
    (h_sum : HasSum (fun n : ℕ => c n * Real.exp (σ * (n : ℝ))) S) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (natShiftedMeasure c) := by
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  refine integrable_sum_measure (fun n => integrable_natAtomMeasure c n _) ?_
  refine h_sum.summable.congr fun n => ?_
  have h_norm : (fun u : ℝ => ‖Real.exp (σ * u)‖) = fun u : ℝ => Real.exp (σ * u) := by
    ext u
    exact Real.norm_of_nonneg (Real.exp_pos _).le
  rw [h_norm, integral_natAtomMeasure hc n h_cont]

lemma laplaceTransformReal_natShiftedMeasure {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {σ S : ℝ}
    (h_sum : HasSum (fun n : ℕ => c n * Real.exp (σ * (n : ℝ))) S) :
    laplaceTransformReal (natShiftedMeasure c) σ = S := by
  have h_int := integrable_exp_natShiftedMeasure hc h_sum
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  unfold laplaceTransformReal natShiftedMeasure
  rw [integral_sum_measure h_int]
  simp_rw [integral_natAtomMeasure hc _ h_cont]
  exact h_sum.tsum_eq

lemma integral_shiftedTest_natShiftedMeasure {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    (Δ_phi : ℝ) (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(natShiftedMeasure c) =
      ∑' n : ℕ, c n * φ (Δ_phi + (n : ℝ)) := by
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
  have h_int : Integrable (shiftedTest Δ_phi φ) (natShiftedMeasure c) := by
    refine integrable_sum_measure (fun n => integrable_natAtomMeasure c n _) ?_
    refine summable_of_ne_finset_zero (s := Finset.range (N_shift + 1)) (fun n hn => ?_)
    have h_norm : (fun u : ℝ => ‖shiftedTest Δ_phi φ u‖) =
        fun u : ℝ => |shiftedTest Δ_phi φ u| := by
      ext u; exact Real.norm_eq_abs _
    rw [h_norm, integral_natAtomMeasure hc n h_cont.abs, h_vanish n hn, abs_zero, mul_zero]
  unfold natShiftedMeasure
  rw [integral_sum_measure h_int]
  simp_rw [integral_natAtomMeasure hc _ h_cont, shiftedTest]

/-! ## 3. Exact Finite-Spin `t`-Channel Identity Measure and Large-`k` Expansion -/

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

/-- Exact finite-spin `t`-channel identity shifted measure
`∑_{n=0}^∞ identityRescaledCoeff Δ_phi k n • δ_n` on `ℝ`, supported on `ℕ ⊂ ℤ`. -/
noncomputable def identityShiftedMeasure (Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  natShiftedMeasure (identityRescaledCoeff Δ_phi k)

lemma identityShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) (k : ℕ) :
    identityShiftedMeasure Δ_phi k (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
  natShiftedMeasure_compl_intCast_eq_zero _

lemma summable_pochhammerCoeff_mul_shift_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ)
    {σ : ℝ} (hσ : σ < 0) :
    Summable (fun n : ℕ =>
      pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) *
        (Real.exp σ) ^ n) :=
  summable_pochhammerCoeff_mixed_mul_exp (by positivity) (by positivity) K hσ

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
    Integrable (fun u : ℝ => Real.exp (σ * u)) (identityShiftedMeasure Δ_phi k) :=
  integrable_exp_natShiftedMeasure (identityRescaledCoeff_nonneg hΔ k)
    (hasSum_identityRescaledCoeff_mul_exp hΔ k hσ)

lemma laplaceTransformReal_identityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (k : ℕ) (hσ : σ < 0) :
    laplaceTransformReal (identityShiftedMeasure Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ) :=
  laplaceTransformReal_natShiftedMeasure (identityRescaledCoeff_nonneg hΔ k)
    (hasSum_identityRescaledCoeff_mul_exp hΔ k hσ)

lemma integral_shiftedTest_identityShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (k N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(identityShiftedMeasure Δ_phi k) =
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ := by
  unfold identityShiftedMeasure identityMonomialPairing
  rw [integral_shiftedTest_natShiftedMeasure (identityRescaledCoeff_nonneg hΔ k) Δ_phi N hφ hsupp]
  dsimp [identityRescaledCoeff]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-- Termwise $O(K^{-1})$ Stirling bound for shifted Pochhammer coefficients
$\frac{(b)_{n + K}}{(n + K)!}$. -/
lemma exists_abs_rpow_mul_pochhammerCoeff_add_sub_inv_gamma_le {b : ℝ} (hb : 0 < b) :
    let p : ℕ := ⌈|(b - 1) - 1|⌉₊ + 1
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 < B ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ n : ℕ,
      |(K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K) - (Real.Gamma b)⁻¹| ≤
        (C₀ + B * |b - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) := by
  intro p
  obtain ⟨B, hB_pos, hB⟩ := exists_bound_rpow_mul_pochhammerCoeff hb
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le hb
  refine ⟨C₀, B, hC₀_nonneg, hB_pos, fun {K} hK n => ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  let u_nK := ((n + K : ℕ) : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K)
  have h_id : (K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K) =
      u_nK * (1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) := by
    dsimp [u_nK]
    have h_cast : ((n + K : ℕ) : ℝ) = (K : ℝ) * (1 + (n : ℝ) / (K : ℝ)) := by
      push_cast; field_simp; ring
    have hpos_r : 0 < 1 + (n : ℝ) / (K : ℝ) := by positivity
    rw [h_cast, Real.mul_rpow hK_pos.le hpos_r.le]
    have h_canc :
        (1 + (n : ℝ) / (K : ℝ)) ^ (1 - b) * (1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) = 1 := by
      rw [← Real.rpow_add hpos_r, sub_add_sub_cancel, sub_self, Real.rpow_zero]
    calc
      (K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K)
        = (K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K) *
            ((1 + (n : ℝ) / (K : ℝ)) ^ (1 - b) *
              (1 + (n : ℝ) / (K : ℝ)) ^ (b - 1)) := by rw [h_canc, mul_one]
      _ = (K : ℝ) ^ (1 - b) * (1 + (n : ℝ) / (K : ℝ)) ^ (1 - b) *
            pochhammerCoeff b (n + K) * (1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) := by ring
  rw [h_id]
  have hu_nonneg : 0 ≤ u_nK :=
    mul_nonneg (by positivity) (pochhammerCoeff_nonneg hb.le (n + K))
  have h_b1 : |u_nK - (Real.Gamma b)⁻¹| ≤ C₀ / (K : ℝ) := by
    have hnK : 1 ≤ n + K := by omega
    have hnK_ge : (K : ℝ) ≤ ((n + K : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ n + K)
    exact (hC₀ hnK).trans (div_le_div_of_nonneg_left hC₀_nonneg hK_pos hnK_ge)
  have h_b2 := abs_one_add_div_rpow_sub_one_le (b - 1) n hK_ge1
  calc
    |u_nK * (1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) - (Real.Gamma b)⁻¹|
      = |(u_nK - (Real.Gamma b)⁻¹) +
          u_nK * ((1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) - 1)| := by ring_nf
    _ ≤ |u_nK - (Real.Gamma b)⁻¹| +
          |u_nK * ((1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) - 1)| := abs_add_le _ _
    _ = |u_nK - (Real.Gamma b)⁻¹| +
          u_nK * |(1 + (n : ℝ) / (K : ℝ)) ^ (b - 1) - 1| := by
        rw [abs_mul, abs_of_nonneg hu_nonneg]
    _ ≤ C₀ / (K : ℝ) +
          B * (|b - 1| * (1 + (n : ℝ)) ^ p / (K : ℝ)) :=
        add_le_add h_b1
          (mul_le_mul (hB (n + K)) h_b2 (abs_nonneg _) hB_pos.le)
    _ = (C₀ + B * |b - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) := by ring

/-- **Kinematic Large-$K$ Expansion of Mixed-Binomial Double-Twist Test-Function Pairings**:
For any $a > 0$, $b > 0$, $\Delta_\phi \in \mathbb{R}$, and support bound $N \in \mathbb{N}$, there
exists $C_N > 0$ such that for all $K \ge 1$ and all $\varphi : \mathbb{R} \to \mathbb{R}$ supported
in $[-N, N]$ with $|\varphi(h)| \le M_\varphi$ ($M_\varphi \ge 0$),
$$
\left|K^{1 - b} \sum_{n=0}^{\infty} \frac{(a)_n}{n!} \frac{(b)_{n + K}}{(n + K)!}
    \varphi(\Delta_\phi + n) -
  \frac{1}{\Gamma(b)} \sum_{n=0}^{\infty} \frac{(a)_n}{n!} \varphi(\Delta_\phi + n)\right|
  \le C_N \, K^{-1} \, M_\varphi.
$$ -/
theorem exists_const_abs_tsum_pochhammerCoeff_mixed_test_sub_le
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (Δ_phi : ℝ) (N : ℕ) :
    ∃ C > 0, ∀ {K : ℕ}, 1 ≤ K →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) →
      |(K : ℝ) ^ (1 - b) *
          (∑' n : ℕ, pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ))) -
        (Real.Gamma b)⁻¹ *
          (∑' n : ℕ, pochhammerCoeff a n * φ (Δ_phi + (n : ℝ)))| ≤
        C * (K : ℝ)⁻¹ * M_φ := by
  let p : ℕ := ⌈|(b - 1) - 1|⌉₊ + 1
  obtain ⟨C₀, B, hC₀_nonneg, hB_pos, h_coeff⟩ :=
    exists_abs_rpow_mul_pochhammerCoeff_add_sub_inv_gamma_le hb
  let N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  let s : Finset ℕ := Finset.range (N_shift + 1)
  let w : ℕ → ℝ := fun n =>
    pochhammerCoeff a n * (C₀ + B * |b - 1| * (1 + (n : ℝ)) ^ p)
  have hw_nonneg : ∀ n : ℕ, 0 ≤ w n := fun n =>
    mul_nonneg (pochhammerCoeff_nonneg ha.le n)
      (add_nonneg hC₀_nonneg (mul_nonneg (mul_nonneg hB_pos.le (abs_nonneg _)) (by positivity)))
  set C_N : ℝ := (∑ n ∈ s, w n) + 1
  have hC_N_pos : 0 < C_N :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun n _ => hw_nonneg n)) zero_lt_one
  refine ⟨C_N, hC_N_pos, fun {K} hK {φ} {M_φ} hsupp hM_φ hφ0 => ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have h_vanish : ∀ n ∉ s, φ (Δ_phi + (n : ℝ)) = 0 := by
    intro n hn
    dsimp [s] at hn
    rw [Finset.mem_range, not_lt] at hn
    have h_gt : ((N_shift : ℕ) : ℝ) < |(n : ℝ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      exact_mod_cast hn
    exact shiftedTest_eq_zero_of_support Δ_phi hsupp h_gt
  have h_tsum1 :
      (∑' n : ℕ, pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ))) =
        ∑ n ∈ s, pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ)) :=
    tsum_eq_sum (fun n hn => by rw [h_vanish n hn, mul_zero])
  have h_tsum2 :
      (∑' n : ℕ, pochhammerCoeff a n * φ (Δ_phi + (n : ℝ))) =
        ∑ n ∈ s, pochhammerCoeff a n * φ (Δ_phi + (n : ℝ)) :=
    tsum_eq_sum (fun n hn => by rw [h_vanish n hn, mul_zero])
  rw [h_tsum1, h_tsum2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ s,
        ((K : ℝ) ^ (1 - b) *
            (pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ))) -
          (Real.Gamma b)⁻¹ * (pochhammerCoeff a n * φ (Δ_phi + (n : ℝ))))|
      ≤ ∑ n ∈ s,
          |(K : ℝ) ^ (1 - b) *
              (pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ))) -
            (Real.Gamma b)⁻¹ * (pochhammerCoeff a n * φ (Δ_phi + (n : ℝ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, w n * (K : ℝ)⁻¹ * M_φ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        have h_factor :
            (K : ℝ) ^ (1 - b) *
                (pochhammerCoeff a n * pochhammerCoeff b (n + K) * φ (Δ_phi + (n : ℝ))) -
              (Real.Gamma b)⁻¹ * (pochhammerCoeff a n * φ (Δ_phi + (n : ℝ))) =
            pochhammerCoeff a n *
              ((K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K) - (Real.Gamma b)⁻¹) *
              φ (Δ_phi + (n : ℝ)) := by ring
        rw [h_factor, abs_mul, abs_mul, abs_of_nonneg (pochhammerCoeff_nonneg ha.le n)]
        have h1 := h_coeff hK n
        rw [div_eq_mul_inv] at h1
        have h2 := hφ0 (Δ_phi + (n : ℝ))
        calc
          pochhammerCoeff a n *
              |(K : ℝ) ^ (1 - b) * pochhammerCoeff b (n + K) - (Real.Gamma b)⁻¹| *
              |φ (Δ_phi + (n : ℝ))|
            ≤ pochhammerCoeff a n *
                ((C₀ + B * |b - 1| * (1 + (n : ℝ)) ^ p) * (K : ℝ)⁻¹) * M_φ :=
              mul_le_mul
                (mul_le_mul_of_nonneg_left h1 (pochhammerCoeff_nonneg ha.le n))
                h2 (abs_nonneg _)
                (mul_nonneg (pochhammerCoeff_nonneg ha.le n)
                  (mul_nonneg (by positivity) (inv_nonneg.mpr hK_pos.le)))
          _ = w n * (K : ℝ)⁻¹ * M_φ := by dsimp [w]; ring
    _ = (∑ n ∈ s, w n) * (K : ℝ)⁻¹ * M_φ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ C_N * (K : ℝ)⁻¹ * M_φ := by
        dsimp [C_N]
        have : 0 ≤ (K : ℝ)⁻¹ * M_φ := mul_nonneg (inv_nonneg.mpr hK_pos.le) hM_φ
        nlinarith

/-- **Kinematic Large-$k$ Expansion of `identityMonomialPairing` to `universalMonomialPairing`**:
For any $\Delta_\phi > 0$ and support bound $N \in \mathbb{N}$, there exists $C_N > 0$ such that
for all $k \ge 1$ and all $\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi(h)| \le M_\varphi$ ($M_\varphi \ge 0$),
$$
\left|(2k)^{1 - 2\Delta_\phi} \operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi) -
  \operatorname{universalMonomialPairing}(\Delta_\phi, \varphi)\right|
  \le C_N \, (2k)^{-1} \, M_\varphi.
$$ -/
theorem exists_const_abs_identityMonomialPairing_sub_universal_le
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
        universalMonomialPairing Δ_phi φ| ≤
        C * (2 * (k : ℝ))⁻¹ * M_φ := by
  have h2Δ : 0 < 2 * Δ_phi := by positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ :=
    exists_const_abs_tsum_pochhammerCoeff_mixed_test_sub_le h2Δ h2Δ Δ_phi N
  set pref : ℝ := 2 * (4 : ℝ) ^ (2 * Δ_phi)
  have hpref_pos : 0 < pref := by dsimp [pref]; positivity
  refine ⟨pref * C₀, mul_pos hpref_pos hC₀_pos, fun {k} hk1 {φ} {M_φ} hsupp hM_φ hφ0 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_sub := hC₀ (K := 2 * k) h2k_ge1 hsupp hM_φ hφ0
  have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
  rw [h_cast] at h_sub
  have h_eq :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
        universalMonomialPairing Δ_phi φ =
      pref *
        ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * φ (Δ_phi + (n : ℝ))) -
          (Real.Gamma (2 * Δ_phi))⁻¹ *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ)))) := by
    dsimp [identityMonomialPairing, universalMonomialPairing, pochhammerCoeff, pref]
    ring
  rw [h_eq, abs_mul, abs_of_pos hpref_pos]
  calc
    pref *
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * φ (Δ_phi + (n : ℝ))) -
          (Real.Gamma (2 * Δ_phi))⁻¹ *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ)))|
      ≤ pref * (C₀ * (2 * (k : ℝ))⁻¹ * M_φ) :=
        mul_le_mul_of_nonneg_left h_sub hpref_pos.le
    _ = (pref * C₀) * (2 * (k : ℝ))⁻¹ * M_φ := by ring

/-! ## 4. Main Quantitative Monomial Lightcone Bootstrap Theorems -/

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- **Master Tauberian Reduction for Rescaled Spin-`2k` Monomial Pairings**:
Given a strip parameter `1 < A`, exponents `0 < α` and `γ ≤ α * midpointHarmonicExp A (2 * π)`,
a scaling exponent `s : ℝ`, a family of `ℤ`-supported reference measures `ν : ℕ → Measure ℝ` with
real Laplace factors `L_ref : ℕ → ℝ → ℝ` and test-function pairings `P_ref : ℕ → (ℝ → ℝ) → ℝ`,
and uniform bounds `M_raw, C_raw > 0` on `[1 - 2A, -1]`, there exists `C > 0` such that
`|(2k)^s M.pairSpin (2k) φ - P_ref k φ| ≤ C * (2k)^(-γ) * M_φ` for all `k ≥ 1`. -/
theorem exists_const_abs_rescaled_pairSpin_sub_le
    {A Δ_phi s α γ M_raw C_raw : ℝ}
    (hA : 1 < A) (hα : 0 < α) (hθ_ge : γ ≤ α * midpointHarmonicExp A (2 * π))
    (hM_raw : 0 < M_raw) (hC_raw : 0 < C_raw) (N : ℕ)
    (ν : ℕ → Measure ℝ) (L_ref : ℕ → ℝ → ℝ) (P_ref : ℕ → (ℝ → ℝ) → ℝ)
    (hν_int : ∀ k, ν k (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (hν_exp : ∀ k {σ : ℝ}, σ < 0 → Integrable (fun u => Real.exp (σ * u)) (ν k))
    (hν_lap : ∀ k {σ : ℝ}, σ < 0 →
      laplaceTransformReal (ν k) σ = Real.exp (-Δ_phi * σ) * L_ref k σ)
    (hL_nonneg : ∀ k {σ : ℝ}, σ < 0 → 0 ≤ L_ref k σ)
    (hν_pair : ∀ k {φ : ℝ → ℝ}, Continuous φ → (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(ν k) = P_ref k φ)
    (h_raw : ∀ {k : ℕ}, 1 ≤ k → ∀ σ ∈ Icc (1 - 2 * A) (-1),
      (2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ + L_ref k σ ≤ M_raw ∧
      |(2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ - L_ref k σ| ≤
        C_raw * (2 * (k : ℝ)) ^ (-α)) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ s * M.pairSpin (2 * (k : ℤ)) φ - P_ref k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hσ_plus : (-1 : ℝ) < 0 := by norm_num
  set E_A : ℝ := Real.exp (|Δ_phi| * (2 * A - 1))
  have hEA_pos : 0 < E_A := Real.exp_pos _
  have hexp_le : ∀ {σ : ℝ}, σ ∈ Icc (1 - 2 * A) (-1) → Real.exp (-Δ_phi * σ) ≤ E_A := by
    intro σ hσ
    refine Real.exp_le_exp.mpr ?_
    have h_abs := le_abs_self (-Δ_phi * σ)
    rw [abs_mul, abs_neg, abs_of_neg (lt_of_le_of_lt hσ.2 hσ_plus)] at h_abs
    have h_nonneg : 0 ≤ |Δ_phi| := abs_nonneg Δ_phi
    have h_le : -σ ≤ 2 * A - 1 := by linarith [hσ.1]
    exact h_abs.trans (mul_le_mul_of_nonneg_left h_le h_nonneg)
  set M_A : ℝ := E_A * M_raw
  have hMA_pos : 0 < M_A := mul_pos hEA_pos hM_raw
  set C_A : ℝ := E_A * C_raw
  have hCA_pos : 0 < C_A := mul_pos hEA_pos hC_raw
  set N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  obtain ⟨C, hC_pos, h_taub_gen⟩ :=
    exists_const_abs_integral_sub_le_rpow hA hα hθ_ge hCA_pos hMA_pos N_shift
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hM_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal (M.rescaledShiftedMeasure s Δ_phi k) σ +
        laplaceTransformReal (ν k) σ ≤ M_A := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_rescaledShiftedMeasure s Δ_phi k σ, hν_lap k hσ_neg, ← mul_add]
    have h_sum_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ + L_ref k σ :=
      add_nonneg (mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _)) (hL_nonneg k hσ_neg)
    exact mul_le_mul (hexp_le hσ) (h_raw hk1 σ hσ).1 h_sum_nonneg hEA_pos.le
  have hδ_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal (M.rescaledShiftedMeasure s Δ_phi k) σ -
        laplaceTransformReal (ν k) σ| ≤ C_A * (2 * (k : ℝ)) ^ (-α) := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_rescaledShiftedMeasure s Δ_phi k σ, hν_lap k hσ_neg,
      ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-Δ_phi * σ) *
          |(2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ - L_ref k σ|
        ≤ E_A * (C_raw * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul (hexp_le hσ) (h_raw hk1 σ hσ).2 (abs_nonneg _) hEA_pos.le
      _ = C_A * (2 * (k : ℝ)) ^ (-α) := by dsimp [C_A]; ring
  have h_est := h_taub_gen h2k_ge1 (hν_int k)
    (M.integrable_exp_rescaledShiftedMeasure s Δ_phi k (by linarith))
    (M.integrable_exp_rescaledShiftedMeasure s Δ_phi k hσ_plus)
    (hν_exp k (by linarith))
    (hν_exp k hσ_plus)
    hM_bd hδ_bd
    (differentiable_shiftedTest Δ_phi hφ)
    (differentiable_deriv_shiftedTest Δ_phi hφ hφ')
    (fun u hu => shiftedTest_eq_zero_of_support Δ_phi hsupp hu)
    hM_φ
    (fun u => hφ0 (Δ_phi + u))
    (fun u => by rw [deriv_shiftedTest Δ_phi hφ]; exact hφ1 (Δ_phi + u))
    (fun u => by rw [deriv2_shiftedTest Δ_phi hφ hφ']; exact hφ2 (Δ_phi + u))
  rwa [M.integral_shiftedTest_rescaledShiftedMeasure s Δ_phi k hφ.continuous,
    hν_pair k hφ.continuous hsupp] at h_est

/-- **Main Quantitative Monomial Lightcone Bootstrap Against the Exact `t`-Channel Identity
(`MonomialFourPointData` version)**:
Let `M` be a monomial four-point decomposition agreeing with `corr : FourPointData ν Δ_phi`
(`ν ≥ 0`, `Δ_phi > 1/2`) and having a `t`-channel twist gap `h_gap > 0`.
Retaining the exact finite-spin `t`-channel identity binomial coefficients in
`identityMonomialPairing Δ_phi (2k) φ` isolates the non-universal dynamical corrections with
**zero $O(k^{-1})$ error** and yields the exponent range
`0 < γ < min (2 * h_gap) (2 * Δ_phi - 1)`:
`|(2k)^(1 - 2Δ_φ) M.pairSpin (2k) φ - (2k)^(1 - 2Δ_φ) identityMonomialPairing Δ_phi (2k) φ| ≤`
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
    dsimp [h']; split_ifs with h_eq <;> [linarith; exact h_eq]
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set α : ℝ := min (2 * h') (2 * Δ_phi - 1)
  have hγα : γ < α := lt_min hγ_2h' hγ_rest
  have hα_pos : 0 < α := lt_trans hγ_pos hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγα
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    M.exists_uniform_laplaceSpinReal_sub_identity_bounds corr hν hΔ hM hgap' hh'_ne
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  exact M.exists_const_abs_rescaled_pairSpin_sub_le hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N
    (identityShiftedMeasure Δ_phi)
    (fun k σ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ)
    (fun k φ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ)
    (identityShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (fun k _ hσ => integrable_exp_identityShiftedMeasure hΔ_pos k hσ)
    (fun k _ hσ => laplaceTransformReal_identityShiftedMeasure hΔ_pos k hσ)
    (fun k _ _ => mul_nonneg (by positivity) (identityLaplaceReal_nonneg hΔ_pos (2 * k) _))
    (fun k _ hφ hsupp => integral_shiftedTest_identityShiftedMeasure hΔ_pos k N hφ hsupp)
    (fun hk1 _ hσ => h_raw hk1 hσ)

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

/-- **Quantitative Monomial Lightcone Bootstrap Against the Expanded Universal Sum
(`MonomialFourPointData` version)**:
Combining the $O(k^{-1})$-free theorem `exists_const_abs_pairSpin_sub_identity_le` with the
kinematic large-$k$ expansion `exists_const_abs_identityMonomialPairing_sub_universal_le`
(`(2k)^(1 - 2Δ_φ) identityMonomialPairing Δ_phi (2k) φ = universalMonomialPairing Δ_phi φ + O(k⁻¹)`)
yields the bound against `universalMonomialPairing Δ_phi φ` for every target exponent
`0 < γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`. -/
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
  have hγ_lt_id : γ < min (2 * h_gap) (2 * Δ_phi - 1) :=
    lt_of_lt_of_le hγ_lt (min_le_min le_rfl (min_le_right 1 (2 * Δ_phi - 1)))
  have hγ_le_one : γ ≤ 1 :=
    ((lt_of_lt_of_le hγ_lt (min_le_right _ _)).trans_le (min_le_left 1 (2 * Δ_phi - 1))).le
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    M.exists_const_abs_pairSpin_sub_identity_le corr hν hΔ hM hgap hγ_pos hγ_lt_id N
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_const_abs_identityMonomialPairing_sub_universal_le hΔ_pos N
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
    |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ|
      = |((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ) +
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
            universalMonomialPairing Δ_phi φ)| := by ring_nf
    _ ≤ |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| +
          |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
            universalMonomialPairing Δ_phi φ| := abs_add_le _ _
    _ ≤ C₁ * (2 * (k : ℝ)) ^ (-γ) * M_φ + C₂ * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
        add_le_add h_b1 h_b2
    _ = (C₁ + C₂) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring

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

end MonomialFourPointData

end CFT.LightconeBootstrap

open CFT.LightconeBootstrap

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- **Main Quantitative Monomial Lightcone Bootstrap Against the Exact `t`-Channel Identity
(`FourPointData` version)**:
For any reflection-positive CFT (`FourPointData ν Δ_phi` with `ν ≥ 0, Δ_phi > 1/2`) with a
primary-spectrum twist gap `corr.HasTwistGap h_gap`,
retaining the exact finite-spin `t`-channel identity binomial coefficients in
`identityMonomialPairing Δ_phi (2k) φ` isolates the non-universal dynamical corrections with
**zero $O(k^{-1})$ error** and yields the exponent range
`0 < γ < min (2 * h_gap) (2 * Δ_phi - 1)`. -/
theorem exists_const_abs_pairSpin_sub_identity_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
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
    (hgap.toMonomialFourPointData hν) hγ_pos hγ_lt N

/-- **Quantitative Monomial Lightcone Bootstrap Against the Expanded Universal Sum
(`FourPointData` version)**:
Combining `exists_const_abs_pairSpin_sub_identity_le` with the $O(k^{-1})$ large-$k$ expansion of
`identityMonomialPairing Δ_phi (2k) φ` yields the bound against `universalMonomialPairing Δ_phi φ`
for every target exponent `0 < γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`. -/
theorem exists_const_abs_pairSpin_sub_universal_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
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
    (hgap.toMonomialFourPointData hν) hγ_pos hγ_lt N

end FourPointData
