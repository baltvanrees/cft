import Mathlib
/-!
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
open Real
open Complex
open Complex Topology
open scoped ComplexConjugate
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Metric

/-- The twice-cut plane: ℂ \ ((-∞, 0] ∪ [1, ∞)) -/
def CutPlane : Set ℂ :=
  { z : ℂ | 1 - z ∈ slitPlane ∧ z ∈ slitPlane }

lemma CutPlane.ne_zero {z : ℂ} (hz : z ∈ CutPlane) : z ≠ 0 :=
  slitPlane_ne_zero hz.2

lemma CutPlane.sub_one {z : ℂ} (hz : z ∈ CutPlane) : 1 - z ∈ CutPlane := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨?_, h1⟩
  rwa [sub_sub_cancel]

lemma CutPlane.one_sub_ne_zero {z : ℂ} (hz : z ∈ CutPlane) : 1 - z ≠ 0 :=
  slitPlane_ne_zero hz.1

lemma isOpen_CutPlane : IsOpen CutPlane := by
  have h1 : IsOpen { z : ℂ | 1 - z ∈ slitPlane } :=
    isOpen_slitPlane.preimage (continuous_sub_left 1)
  have h2 : IsOpen { z : ℂ | z ∈ slitPlane } :=
    isOpen_slitPlane
  change IsOpen ({ z : ℂ | 1 - z ∈ slitPlane } ∩ { z : ℂ | z ∈ slitPlane })
  exact h1.inter h2

lemma mem_CutPlane_iff {z : ℂ} :
    z ∈ CutPlane ↔ z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) := by
  dsimp [CutPlane]
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  simp only [sub_re, one_re, sub_im, one_im, zero_sub, neg_ne_zero]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hz : z.im = 0
    · right
      have h2' : 0 < z.re := by
        rcases h2 with h2 | h2
        · exact h2
        · contradiction
      have h1' : z.re < 1 := by
        rcases h1 with h1 | h1
        · linarith
        · contradiction
      exact ⟨h2', h1'⟩
    · left
      exact hz
  · rintro (him | hre)
    · exact ⟨Or.inr him, Or.inr him⟩
    · exact ⟨Or.inl (by linarith), Or.inl hre.1⟩

lemma one_half_mem_CutPlane : (1/2 : ℂ) ∈ CutPlane := by
  rw [mem_CutPlane_iff]
  right
  norm_num

lemma starConvex_CutPlane : StarConvex ℝ (1/2 : ℂ) CutPlane := by
  intro y hy a b ha hb hab
  rw [mem_CutPlane_iff] at hy
  set w : ℂ := a • (1/2 : ℂ) + b • y
  rw [mem_CutPlane_iff]
  have hw_re : w.re = a * (1/2) + b * y.re := by
    dsimp [w]; simp
  have hw_im : w.im = b * y.im := by
    dsimp [w]; simp
  rw [hw_re, hw_im]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    rw [hb0, ha1]
    right
    norm_num
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases hy with hy_im | ⟨hy_re1, hy_re2⟩
    · left
      exact mul_ne_zero hb0 hy_im
    · right
      constructor
      · by_cases ha0 : a = 0
        · rw [ha0, zero_mul, zero_add]
          exact mul_pos hb_pos hy_re1
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have : 0 < a * (1/2) := mul_pos ha_pos (by norm_num)
          have : 0 < b * y.re := mul_pos hb_pos hy_re1
          positivity
      · calc
          a * (1/2) + b * y.re < a * 1 + b * 1 := by
            have h1 : a * (1/2) ≤ a * 1 := by nlinarith
            have h2 : b * y.re < b * 1 := mul_lt_mul_of_pos_left hy_re2 hb_pos
            linarith
          _ = 1 := by linarith

lemma isPathConnected_CutPlane : IsPathConnected CutPlane :=
  starConvex_CutPlane.isPathConnected one_half_mem_CutPlane

lemma isConnected_CutPlane : IsConnected CutPlane :=
  isPathConnected_CutPlane.isConnected

lemma isPreconnected_CutPlane : IsPreconnected CutPlane :=
  isConnected_CutPlane.isPreconnected

lemma half_add_I_mul_mem_CutPlane {y : ℂ} (hy : y ∈ ball (0 : ℂ) (1 / 2)) :
    (1/2 : ℂ) + I * y ∈ CutPlane := by
  rw [mem_CutPlane_iff]
  right
  have hy_norm : ‖y‖ < (1/2 : ℝ) := mem_ball_zero_iff.mp hy
  have hy_im : |y.im| < (1/2 : ℝ) := (abs_im_le_norm y).trans_lt hy_norm
  rw [abs_lt] at hy_im
  have h_re : ((1/2 : ℂ) + I * y).re = (1/2 : ℝ) - y.im := by
    simp [sub_eq_add_neg]
  rw [h_re]
  constructor <;> linarith

lemma half_sub_I_mul_mem_CutPlane {y : ℂ} (hy : y ∈ ball (0 : ℂ) (1 / 2)) :
    (1/2 : ℂ) - I * y ∈ CutPlane := by
  have hy_neg : -y ∈ ball (0 : ℂ) (1/2) := by
    rw [mem_ball_zero_iff, norm_neg]
    exact mem_ball_zero_iff.mp hy
  have h := half_add_I_mul_mem_CutPlane hy_neg
  have : (1/2 : ℂ) + I * (-y) = (1/2 : ℂ) - I * y := by ring
  rwa [this] at h

lemma one_sub_cpow_half_re_pos {z : ℂ} (hz : z ∈ CutPlane) : 0 < ((1 - z) ^ (1/2 : ℂ)).re := by
  have h1z_ne_zero : 1 - z ≠ 0 := CutPlane.one_sub_ne_zero hz
  rw [cpow_def_of_ne_zero h1z_ne_zero, exp_re, mul_im]
  simp
  ring_nf
  rw [log_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have harg : (1 - z).arg ∈ Set.Ioo (-Real.pi) Real.pi := by
    have h_pi := arg_le_pi (1 - z)
    have h_npi := neg_pi_lt_arg (1 - z)
    exact ⟨h_npi, lt_of_le_of_ne h_pi (slitPlane_arg_ne_pi hz.1)⟩
  exact ⟨by linarith [harg.1], by linarith [harg.2]⟩

noncomputable def rho (z : ℂ) : ℂ :=
  z / (1 + (1 - z)^(1/2 : ℂ))^2

lemma rho_norm_lt_one {z : ℂ} (hz : z ∈ CutPlane) : ‖rho z‖ < 1 := by
  dsimp [rho]
  set w := (1 - z) ^ (1/2 : ℂ) with hw
  have hzw : z = (1 - w) * (1 + w) := by
    dsimp [w]
    ring_nf
    simp
  rw [hzw]
  have hw''' : 0 < w.re := one_sub_cpow_half_re_pos hz
  have hw'' : ‖1+w‖ > 0 := by
    apply norm_pos_iff.mpr
    intro h
    have h_re : (1 + w).re = 0 := by rw [h]; rfl
    simp at h_re
    linarith [hw''']
  have hw' : ‖1-w‖ < ‖1+w‖ := by
    repeat rw [Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_lt_sqrt
    · rw [sq, sq]
      rw [←Complex.normSq_apply]
      exact normSq_nonneg (1-w)
    · ring_nf
      simp only [sub_re, one_re, sub_im, one_im, zero_sub, even_two, Even.neg_pow, add_re, add_im,
      zero_add, add_lt_add_iff_right]
      rw [←sub_pos]
      ring_nf
      simp [hw''']
  rw [norm_div, norm_mul, norm_pow]
  rw [sq]
  rw [mul_div_mul_right _ _ (ne_of_gt hw'')]
  rw [div_lt_iff₀ hw'', one_mul]
  exact hw'

lemma rho_eq_div {z : ℂ} (hz : z ∈ CutPlane) :
    rho z = (1 - (1 - z) ^ (1/2 : ℂ)) / (1 + (1 - z) ^ (1/2 : ℂ)) := by
  dsimp [rho]
  set w := (1 - z) ^ (1/2 : ℂ) with hw
  have hzw : z = (1 - w) * (1 + w) := by
    dsimp [w]
    ring_nf
    simp
  have hw_re := one_sub_cpow_half_re_pos hz
  have hw_ne : 1 + w ≠ 0 := by
    intro h
    have : (1 + w).re = 0 := by rw [h]; rfl
    simp at this
    linarith [hw_re]
  rw [hzw, sq]
  exact mul_div_mul_right (1 - w) (1 + w) hw_ne

lemma rho_ne_zero {z : ℂ} (hz : z ∈ CutPlane) : rho z ≠ 0 := by
  dsimp [rho]
  apply div_ne_zero (CutPlane.ne_zero hz)
  intro h
  rw [sq_eq_zero_iff] at h
  have hw''' := one_sub_cpow_half_re_pos hz
  have : (1 + (1 - z) ^ (1/2 : ℂ)).re = 0 := by rw [h]; rfl
  simp at this
  linarith [hw''']

lemma rho_mem_slitPlane {z : ℂ} (hz : z ∈ CutPlane) : rho z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : (rho z).im = 0
  · left
    set w := (1 - z) ^ (1/2 : ℂ)
    have h_rho_div : rho z = (1 - w) / (1 + w) := rho_eq_div hz
    have hw_re := one_sub_cpow_half_re_pos hz
    have hw_ne : 1 + w ≠ 0 := by
      intro h
      have : (1 + w).re = 0 := by rw [h]; rfl
      simp at this
      linarith [hw_re]
    have h_rw : w * (1 + rho z) = 1 - rho z := by
      have h_cancel : rho z * (1 + w) = 1 - w := by
        rw [h_rho_div, div_mul_cancel₀ (1 - w) hw_ne]
      linear_combination h_cancel
    have h_one_add_rho_ne : 1 + rho z ≠ 0 := by
      intro h
      have : ‖rho z‖ = 1 := by
        have : rho z = -1 := by linear_combination h
        rw [this, norm_neg, norm_one]
      linarith [rho_norm_lt_one hz]
    have hw_eq : w = (1 - rho z) / (1 + rho z) := by
      exact mul_right_cancel₀ h_one_add_rho_ne (by rw [div_mul_cancel₀ _ h_one_add_rho_ne, h_rw])
    have h_rho_real : rho z = ((rho z).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hw_real : w = (((1 - (rho z).re) / (1 + (rho z).re) : ℝ) : ℂ) := by
      rw [hw_eq, h_rho_real]
      push_cast
      rfl
    have hw_im : w.im = 0 := by
      rw [hw_real]
      exact ofReal_im _
    have hzw : z = 1 - w^2 := by
      dsimp [w]
      ring_nf
      simp
    have hz_im : z.im = 0 := by
      rw [hzw, sub_im, one_im, sq, mul_im, hw_im, mul_zero, zero_mul, add_zero, sub_zero]
    have hz_cut : 0 < z.re ∧ z.re < 1 := by
      have := (mem_CutPlane_iff.mp hz).resolve_left (by rw [hz_im]; exact not_not.mpr rfl)
      exact this
    have hw_val : w.re = (1 - (rho z).re) / (1 + (rho z).re) := by
      rw [hw_real, ofReal_re]
    have hz_re : z.re = 1 - w.re^2 := by
      rw [hzw, sub_re, one_re, sq, mul_re, hw_im, mul_zero, sub_zero, sq]
    set r := (rho z).re
    change 0 < r
    have hr_lt1 : |r| < 1 := by
      have : ‖rho z‖ < 1 := rho_norm_lt_one hz
      rw [h_rho_real, norm_real] at this
      exact this
    rw [abs_lt] at hr_lt1
    have h1r_pos : 0 < 1 + r := by linarith
    have hw_re_pos : 0 < w.re := hw_re
    have hw_sq_lt1 : w.re^2 < 1 := by linarith [hz_cut.1, hz_re]
    have hw_lt1 : w.re < 1 := by
      nlinarith [hw_re_pos, hw_sq_lt1]
    rw [hw_val] at hw_lt1
    rw [div_lt_iff₀ h1r_pos] at hw_lt1
    linarith
  · right
    exact him

lemma conj_rho {z : ℂ} (hz : z ∈ CutPlane) : rho (conj z) = conj (rho z) := by
  dsimp [rho]
  have harg : (1 - z).arg ≠ π := slitPlane_arg_ne_pi hz.1
  have h_half : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, conj_ofReal]
  have h_cpow : conj ((1 - z) ^ (1 / 2 : ℂ)) = (conj (1 - z)) ^ (1 / 2 : ℂ) := by
    have h := (conj_cpow (1 - z) (1 / 2 : ℂ) harg).symm
    rwa [h_half] at h
  have h_sub : conj (1 - z) = 1 - conj z := by
    simp
  rw [map_div₀, map_pow, map_add, map_one, h_cpow, h_sub]

lemma differentiableAt_rho {z : ℂ} (hz : z ∈ CutPlane) : DifferentiableAt ℂ rho z := by
  change DifferentiableAt ℂ (fun z => z / (1 + (1 - z) ^ (1/2 : ℂ)) ^ 2) z
  have h1z_diff : DifferentiableAt ℂ (fun z => 1 - z) z := by fun_prop
  have h_sqrt : DifferentiableAt ℂ (fun z => (1 - z) ^ (1/2 : ℂ)) z :=
    h1z_diff.cpow_const hz.1
  have h_denom : DifferentiableAt ℂ (fun z => (1 + (1 - z) ^ (1/2 : ℂ)) ^ 2) z := by
    exact ((differentiableAt_const (c := 1)).add h_sqrt).pow 2
  have h_ne : (1 + (1 - z) ^ (1/2 : ℂ)) ^ 2 ≠ 0 := by
    intro h
    rw [sq_eq_zero_iff] at h
    have hw''' := one_sub_cpow_half_re_pos hz
    have h_re : (1 + (1 - z) ^ (1/2 : ℂ)).re = 0 := by rw [h]; rfl
    simp at h_re
    linarith [hw''']
  exact differentiableAt_id.div h_denom h_ne

lemma differentiableOn_rho : DifferentiableOn ℂ rho CutPlane := fun _hz hz =>
  (differentiableAt_rho hz).differentiableWithinAt

lemma differentiableOn_rho_comp_sub_one : DifferentiableOn ℂ (fun z => rho (1 - z)) CutPlane := by
  intro z hz
  have h_sub : DifferentiableAt ℂ (fun z => 1 - z) z := by fun_prop
  have h_comp := (differentiableAt_rho (CutPlane.sub_one hz)).comp z h_sub
  exact h_comp.differentiableWithinAt

lemma differentiableOn_cpow_const (c : ℂ) :
    DifferentiableOn ℂ (fun z => z ^ c) CutPlane := by
  intro z hz
  exact (differentiableAt_id.cpow_const hz.2).differentiableWithinAt

lemma differentiableOn_one_sub_cpow_const (c : ℂ) :
    DifferentiableOn ℂ (fun z => (1 - z) ^ c) CutPlane := by
  intro z hz
  have h1z_diff : DifferentiableAt ℂ (fun z => 1 - z) z := by fun_prop
  exact (h1z_diff.cpow_const hz.1).differentiableWithinAt

lemma cpow_mul_conj_cpow {Δ : ℝ} {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ (- (Δ : ℂ)) * (conj z) ^ (- (Δ : ℂ)) = (‖z‖ : ℂ) ^ (-2 * (Δ : ℂ)) := by
  have hz_arg : z.arg ≠ π := slitPlane_arg_ne_pi hz
  have hz_ne : z ≠ 0 := slitPlane_ne_zero hz
  have h_real : conj (- (Δ : ℂ)) = - (Δ : ℂ) := by
    have : (- (Δ : ℂ)) = ↑(-Δ) := by push_cast; rfl
    rw [this, conj_ofReal]
  have h_conj : (conj z) ^ (- (Δ : ℂ)) = conj (z ^ (- (Δ : ℂ))) := by
    have h := conj_cpow z (- (Δ : ℂ)) hz_arg
    rwa [h_real] at h
  rw [h_conj, mul_conj, Complex.normSq_eq_norm_sq]
  have h_norm : ‖z ^ (- (Δ : ℂ))‖ = ‖z‖ ^ (-Δ) := by
    have : (- (Δ : ℂ)) = ↑(-Δ) := by push_cast; rfl
    rw [this, norm_cpow_real]
  rw [h_norm]
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  have h_sq : (‖z‖ ^ (-Δ)) ^ 2 = ‖z‖ ^ (-2 * Δ) := by
    rw [sq, ← Real.rpow_add hz_pos]
    ring_nf
  rw [h_sq]
  have h_cast : ((-2 * Δ : ℝ) : ℂ) = -2 * (Δ : ℂ) := by push_cast; rfl
  rw [← h_cast]
  exact ofReal_cpow hz_pos.le (-2 * Δ)

lemma mem_closure_of_subset_real_interval (a b : ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (s : Set ℂ) (hs : ∀ x ∈ Set.Ioo a b, (x : ℂ) ∈ s) :
    (x₀ : ℂ) ∈ closure (s \ {(x₀ : ℂ)}) := by
  have h_sub : (fun x : ℝ => (x : ℂ)) '' Set.Ioo x₀ b ⊆ s \ {(x₀ : ℂ)} := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨hs x ⟨by linarith [hx₀.1, hx.1], hx.2⟩, ?_⟩
    simp only [Set.mem_singleton_iff, ofReal_inj]
    exact ne_of_gt hx.1
  apply closure_mono h_sub
  have h_cl : (x₀ : ℂ) ∈ (fun x : ℝ => (x : ℂ)) '' closure (Set.Ioo x₀ b) := by
    refine ⟨x₀, ?_, rfl⟩
    rw [closure_Ioo (ne_of_lt hx₀.2)]
    exact Set.left_mem_Icc.mpr (le_of_lt hx₀.2)
  exact image_closure_subset_closure_image continuous_ofReal h_cl

lemma eqOn_of_differentiableOn_of_eqOn_real_interval
    {U : Set ℂ} (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (a b : ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (h_sub : (fun x : ℝ => (x : ℂ)) '' Set.Ioo a b ⊆ U)
    (h_eq : ∀ x ∈ Set.Ioo a b, f (x : ℂ) = g (x : ℂ)) :
    EqOn f g U := by
  have hf_an : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU_open
  have hx₀_U : (x₀ : ℂ) ∈ U := h_sub ⟨x₀, hx₀, rfl⟩
  have h_cl : (x₀ : ℂ) ∈ closure ({z | f z = g z} \ {(x₀ : ℂ)}) := by
    apply mem_closure_of_subset_real_interval a b x₀ hx₀
    exact h_eq
  exact hf_an.eqOn_of_preconnected_of_mem_closure hg_an hU_conn hx₀_U h_cl

theorem eqOn_CutPlane_of_differentiableOn_of_eqOn_interval
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f CutPlane) (hg : DifferentiableOn ℂ g CutPlane)
    (h_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f (x : ℂ) = g (x : ℂ)) :
    EqOn f g CutPlane := by
  have h_sub : (fun x : ℝ => (x : ℂ)) '' Set.Ioo 0 1 ⊆ CutPlane := by
    rintro z ⟨x, hx, rfl⟩
    rw [mem_CutPlane_iff]
    right
    simp [hx.1, hx.2]
  have h_half : (1/2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  exact eqOn_of_differentiableOn_of_eqOn_real_interval
    isOpen_CutPlane isPreconnected_CutPlane hf hg 0 1 (1/2) h_half h_sub h_eq

lemma exists_ball_pdisk_dom (ρl : ℂ) (hρl_slit : ρl ∈ slitPlane) (hρl_norm : ‖ρl‖ < 1) :
    ∃ (ε r₀ r₁ : ℝ), 0 < ε ∧ 0 < r₀ ∧ r₁ < 1 ∧
      (∀ z ∈ ball ρl ε, z ∈ slitPlane ∧ r₀ ≤ ‖z‖ ∧ ‖z‖ ≤ r₁) := by
  have h_open : IsOpen (slitPlane ∩ ball (0 : ℂ) 1) :=
    isOpen_slitPlane.inter Metric.isOpen_ball
  have h_mem : ρl ∈ slitPlane ∩ ball (0 : ℂ) 1 :=
    ⟨hρl_slit, mem_ball_zero_iff.mpr hρl_norm⟩
  rcases Metric.isOpen_iff.mp h_open ρl h_mem with ⟨ε₁, hε₁_pos, hε₁_sub⟩
  have hρl_pos : 0 < ‖ρl‖ := norm_pos_iff.mpr (slitPlane_ne_zero hρl_slit)
  set r₀ := ‖ρl‖ / 2
  set r₁ := (1 + ‖ρl‖) / 2
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; linarith [hρl_pos]
  have hr₁_lt1 : r₁ < 1 := by dsimp [r₁]; linarith [hρl_norm]
  set ε := min ε₁ (min (‖ρl‖ / 2) ((1 - ‖ρl‖) / 2))
  have hε_pos : 0 < ε := by
    refine lt_min hε₁_pos (lt_min (by positivity) (by linarith))
  refine ⟨ε, r₀, r₁, hε_pos, hr₀_pos, hr₁_lt1, ?_⟩
  intro z hz
  have hz_ε₁ : z ∈ ball ρl ε₁ := by
    apply Metric.ball_subset_ball (min_le_left _ _) hz
  have hz_mem := hε₁_sub hz_ε₁
  have hz_dist : dist z ρl < ε := Metric.mem_ball.mp hz
  have hz_norm_dist : ‖z - ρl‖ < ε := by rwa [dist_eq_norm] at hz_dist
  have hz_dist_r₀ : ‖z - ρl‖ < ‖ρl‖ / 2 := by
    calc
      ‖z - ρl‖ < ε := hz_norm_dist
      _ ≤ min (‖ρl‖ / 2) ((1 - ‖ρl‖) / 2) := min_le_right _ _
      _ ≤ ‖ρl‖ / 2 := min_le_left _ _
  have hz_dist_r₁ : ‖z - ρl‖ < (1 - ‖ρl‖) / 2 := by
    calc
      ‖z - ρl‖ < ε := hz_norm_dist
      _ ≤ min (‖ρl‖ / 2) ((1 - ‖ρl‖) / 2) := min_le_right _ _
      _ ≤ (1 - ‖ρl‖) / 2 := min_le_right _ _
  have h_ge : r₀ ≤ ‖z‖ := by
    have : ‖ρl‖ - ‖z‖ ≤ ‖z - ρl‖ := by
      calc
        ‖ρl‖ - ‖z‖ ≤ ‖ρl - z‖ := norm_sub_norm_le ρl z
        _ = ‖z - ρl‖ := norm_sub_rev ρl z
    dsimp [r₀]
    linarith
  have h_le : ‖z‖ ≤ r₁ := by
    have : ‖z‖ - ‖ρl‖ ≤ ‖z - ρl‖ := norm_sub_norm_le z ρl
    dsimp [r₁]
    linarith
  exact ⟨hz_mem.1, h_ge, h_le⟩

lemma add_I_mul_mem_CutPlane {x₀ : ℝ} {y : ℂ} (hy : ‖y‖ < min x₀ (1 - x₀)) :
    (x₀ : ℂ) + I * y ∈ CutPlane := by
  rw [mem_CutPlane_iff]
  right
  have h_im : |y.im| < min x₀ (1 - x₀) := (abs_im_le_norm y).trans_lt hy
  rw [abs_lt] at h_im
  have h1 := min_le_left x₀ (1 - x₀)
  have h2 := min_le_right x₀ (1 - x₀)
  have h_re : ((x₀ : ℂ) + I * y).re = x₀ - y.im := by simp [sub_eq_add_neg]
  rw [h_re]
  constructor <;> linarith [h_im.1, h_im.2]

lemma sub_I_mul_mem_CutPlane {x₀ : ℝ} {y : ℂ} (hy : ‖y‖ < min x₀ (1 - x₀)) :
    (x₀ : ℂ) - I * y ∈ CutPlane := by
  have hy' : ‖-y‖ < min x₀ (1 - x₀) := by rwa [norm_neg]
  have h := add_I_mul_mem_CutPlane hy'
  rwa [mul_neg, ← sub_eq_add_neg] at h

lemma ofReal_mem_CutPlane {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : (x : ℂ) ∈ CutPlane := by
  rw [mem_CutPlane_iff]
  right
  simp [hx.1, hx.2]
