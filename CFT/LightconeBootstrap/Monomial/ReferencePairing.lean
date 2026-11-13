/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.Analysis.LaplaceTauberian
import CFT.LightconeBootstrap.Monomial.LaplaceBound

/-!
# Monomial Reference Measures and Pairings

This file constructs the lattice-shifted test functions, rescaled spin-$2k$ spectral measures,
and discrete $\mathbb{N}$-supported $t$-channel identity and universal reference measures for the
monomial lightcone bootstrap, and proves the $O(k^{-1})$ kinematic expansion of
`identityMonomialPairing` to `universalMonomialPairing`.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped ENNReal

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
