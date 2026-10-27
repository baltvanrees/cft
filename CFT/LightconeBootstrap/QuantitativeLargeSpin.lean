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

/-- Weight `(2 * 4^(2Δ_φ) / Γ(2Δ_φ)) * (2Δ_φ)_n / n!` of the `n`-th double-twist family. -/
noncomputable def universalCoeff (Δ_phi : ℝ) (n : ℕ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n

lemma universalCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (n : ℕ) :
    0 ≤ universalCoeff Δ_phi n := by
  unfold universalCoeff
  have hG : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos (by positivity)
  exact mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n)

/-- Universal shifted double-twist measure `∑_{n=0}^∞ universalCoeff Δ_phi n • δ_n` on `ℝ`,
supported on `ℕ ⊂ ℤ`. -/
noncomputable def universalShiftedMeasure (Δ_phi : ℝ) : Measure ℝ :=
  natShiftedMeasure (universalCoeff Δ_phi)

lemma universalShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) :
    universalShiftedMeasure Δ_phi (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
  natShiftedMeasure_compl_intCast_eq_zero _

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
    Integrable (fun u : ℝ => Real.exp (σ * u)) (universalShiftedMeasure Δ_phi) :=
  integrable_exp_natShiftedMeasure (universalCoeff_nonneg hΔ)
    (hasSum_universalCoeff_mul_exp Δ_phi hσ)

lemma laplaceTransformReal_universalShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    laplaceTransformReal (universalShiftedMeasure Δ_phi) σ =
      Real.exp (-Δ_phi * σ) * universalLaplaceReal Δ_phi σ :=
  laplaceTransformReal_natShiftedMeasure (universalCoeff_nonneg hΔ)
    (hasSum_universalCoeff_mul_exp Δ_phi hσ)

lemma integral_shiftedTest_universalShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(universalShiftedMeasure Δ_phi) =
      universalMonomialPairing Δ_phi φ := by
  unfold universalShiftedMeasure universalMonomialPairing
  rw [integral_shiftedTest_natShiftedMeasure (universalCoeff_nonneg hΔ) Δ_phi N hφ hsupp]
  dsimp [universalCoeff, pochhammerCoeff]
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
    dsimp [h']; split_ifs with h_eq <;> [linarith; exact h_eq]
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set α : ℝ := min (2 * h') (min 1 (2 * Δ_phi - 1))
  have hγα : γ < α := lt_min hγ_2h' hγ_rest
  have hα_pos : 0 < α := lt_trans hγ_pos hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγα
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    M.exists_uniform_laplaceSpinReal_bounds corr hν hΔ hM hgap' hh'_ne
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  exact M.exists_const_abs_rescaled_pairSpin_sub_le hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N
    (fun _ => universalShiftedMeasure Δ_phi)
    (fun _ => universalLaplaceReal Δ_phi)
    (fun _ => universalMonomialPairing Δ_phi)
    (fun _ => universalShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (fun _ _ hσ => integrable_exp_universalShiftedMeasure hΔ_pos hσ)
    (fun _ _ hσ => laplaceTransformReal_universalShiftedMeasure hΔ_pos hσ)
    (fun _ _ hσ => universalLaplaceReal_nonneg hΔ_pos hσ)
    (fun _ _ hφ hsupp => integral_shiftedTest_universalShiftedMeasure hΔ_pos N hφ hsupp)
    (fun hk1 _ hσ => h_raw hk1 hσ)

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
