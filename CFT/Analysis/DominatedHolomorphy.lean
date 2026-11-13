/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Holomorphy of Locally Dominated Parametric Integrals and Series

In real analysis, differentiating under an integral or summation sign requires bounding the
derivative of the integrand or summands. For holomorphic functions, Cauchy's integral formula
eliminates this extra hypothesis: a local uniform bound on $\Vert f\Vert$ on closed balls automatically
bounds the Fréchet derivative on smaller balls, which suffices to establish holomorphy of locally
dominated parametric integrals and series.

**Where this is used**:
- `differentiableOn_tsum_of_differentiableOn_of_norm_le` is used in `CFT.Blocks_pdisk`
  (`ConformalBlock.differentiableOn_evalPdisk`) to prove joint holomorphy of analytically continued
  conformal blocks on the universal cover of the punctured polydisk $\operatorname{UcPdisk}$.
- `differentiableOn_integral_of_differentiableOn_of_norm_le` is used in `CFT.Corr_pdisk`
  (`FourPointData.differentiableOn_correlator_pdisk`) to prove joint holomorphy of the four-point
  correlator on $\operatorname{UcPdisk}$, enabling the analytic continuation of $s \leftrightarrow t$
  crossing symmetry (`FourPointData.crossing_correlator`) from the Euclidean section $z_r = \bar{z}_l$.
-/

noncomputable section

open Complex Metric Set Filter Topology MeasureTheory

/-!
## Cauchy Derivative and Local Lipschitz Bounds
-/

/-- **Cauchy Fréchet Derivative Estimate**: if $f : E \to \mathbb{C}$ is holomorphic on an open set
$U \subseteq E$ and bounded in norm by $M$ on a closed ball $\overline{B}(w_0, r) \subseteq U$
($r > 0$), then $\Vert\operatorname{fderiv} \mathbb{C} f w_0\Vert \le M / r$. -/
lemma norm_fderiv_le_of_differentiableOn_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    {w₀ : E} {r M : ℝ} (hr : 0 < r) (h_sub : closedBall w₀ r ⊆ U)
    (hM : ∀ w ∈ closedBall w₀ r, ‖f w‖ ≤ M) :
    ‖fderiv ℂ f w₀‖ ≤ M / r := by
  have hM_nonneg : 0 ≤ M := (norm_nonneg (f w₀)).trans (hM w₀ (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM_nonneg hr.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R : ℝ := r / ‖v‖
  have hR_pos : 0 < R := div_pos hr hv_pos
  let g : ℂ → ℂ := fun t => f (w₀ + t • v)
  have hg_sub : ∀ t ∈ closedBall (0 : ℂ) R, w₀ + t • v ∈ closedBall w₀ r := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_self_add_left, norm_smul]
    calc
      ‖t‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right ht hv_pos.le
      _ = r := div_mul_cancel₀ r hv_pos.ne'
  let V : Set ℂ := (fun t : ℂ => w₀ + t • v) ⁻¹' U
  have hV_open : IsOpen V :=
    hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hg_diffOn : DifferentiableOn ℂ g V := fun t ht =>
    ((hf _ ht).differentiableAt (hU.mem_nhds ht) |>.comp t
      ((differentiableAt_id.smul_const v).const_add w₀)).differentiableWithinAt
  have h_cderiv :=
    Complex.cderiv_eq_deriv hV_open hg_diffOn hR_pos (fun t ht => h_sub (hg_sub t ht))
  have h_bound := Complex.norm_cderiv_le hR_pos (f := g) (z := 0) (M := M)
    (fun t ht => hM _ (hg_sub t (sphere_subset_closedBall ht)))
  rw [h_cderiv] at h_bound
  have h_hasDeriv : HasDerivAt g (fderiv ℂ f w₀ v) 0 := by
    have hf_at : HasFDerivAt f (fderiv ℂ f w₀) (w₀ + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact ((hf w₀ (h_sub (mem_closedBall_self hr.le))).differentiableAt
        (hU.mem_nhds (h_sub (mem_closedBall_self hr.le)))).hasFDerivAt
    have h_aff : HasDerivAt (fun t : ℂ => w₀ + t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const v |>.const_add w₀
    exact hf_at.comp_hasDerivAt 0 h_aff
  rw [h_hasDeriv.deriv] at h_bound
  calc
    ‖(fderiv ℂ f w₀) v‖ ≤ M / R := h_bound
    _ = M / r * ‖v‖ := by
      dsimp [R]
      rw [div_div_eq_mul_div, mul_comm M, mul_div_assoc, mul_comm ‖v‖]

/-- Applying the Cauchy derivative bound on $\overline{B}(w, r/2) \subseteq \overline{B}(w_0, r)$
together with the mean value inequality shows that $f$ is Lipschitz on $B(w_0, r/2)$ with constant
$M / (r/2)$. -/
lemma lipschitzOnWith_of_differentiableOn_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    {w₀ : E} {r M : ℝ} (hr : 0 < r) (h_sub : closedBall w₀ r ⊆ U)
    (hM : ∀ w ∈ closedBall w₀ r, ‖f w‖ ≤ M) :
    LipschitzOnWith (Real.nnabs (M / (r / 2))) f (ball w₀ (r / 2)) := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hM_nonneg : 0 ≤ M := (norm_nonneg (f w₀)).trans (hM w₀ (mem_closedBall_self hr.le))
  have hK_nonneg : 0 ≤ M / (r / 2) := div_nonneg hM_nonneg hr2.le
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
    (fun w hw => ?_) (fun w hw => ?_) (convex_ball w₀ (r / 2))
  · have hw_U : w ∈ U :=
      h_sub (ball_subset_closedBall (ball_subset_ball (half_le_self hr.le) hw))
    exact (hf w hw_U).differentiableAt (hU.mem_nhds hw_U)
  · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hK_nonneg]
    have hw_sub : closedBall w (r / 2) ⊆ closedBall w₀ r := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hw
      calc
        dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle z w w₀
        _ ≤ r / 2 + r / 2 := add_le_add hz hw.le
        _ = r := add_halves r
    exact norm_fderiv_le_of_differentiableOn_of_norm_le hU hf hr2 (hw_sub.trans h_sub)
      (fun z hz => hM z (hw_sub hz))

/-!
## Parametric Integrals and Series
-/

/-- If $F(w, a)$ is measurable in $a$ for each $w$ in an open set $U \subseteq \mathbb{C} \times \mathbb{C}$
and holomorphic in $w \in U$ for $\mu$-a.e. $a$, then for each $w_0 \in U$ its Fréchet derivative
$a \mapsto \operatorname{fderiv} \mathbb{C} (w \mapsto F(w, a))\thinspace w_0$ is $\mu$-measurable, obtained
as the pointwise limit of difference quotients along the coordinate axes. -/
lemma aestronglyMeasurable_fderiv_prod
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : (ℂ × ℂ) → α → ℂ}
    {w₀ : ℂ × ℂ} (hw₀ : w₀ ∈ U)
    (hF_meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (hF_diff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (fun w => F w a) U) :
    AEStronglyMeasurable (fun a => fderiv ℂ (fun w => F w a) w₀) μ := by
  classical
  have h_dir : ∀ v : ℂ × ℂ,
      AEStronglyMeasurable (fun a => fderiv ℂ (fun w => F w a) w₀ v) μ := by
    intro v
    let zk : ℕ → ℂ × ℂ := fun k => w₀ + (((k + 1 : ℝ)⁻¹ : ℝ) : ℂ) • v
    let seq : ℕ → α → ℂ := fun k a =>
      if zk k ∈ U then ((k + 1 : ℝ) : ℂ) * (F (zk k) a - F w₀ a) else 0
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := seq) (fun k => ?_) ?_
    · by_cases hk : zk k ∈ U
      · have h_eq : seq k = fun a => ((k + 1 : ℝ) : ℂ) * (F (zk k) a - F w₀ a) := by
          ext a
          simp [seq, hk]
        rw [h_eq]
        exact ((hF_meas _ hk).sub (hF_meas w₀ hw₀)).const_mul _
      · have h_eq : seq k = fun _ => 0 := by
          ext a
          simp [seq, hk]
        rw [h_eq]
        exact aestronglyMeasurable_const
    · filter_upwards [hF_diff] with a ha
      have ha_at : HasFDerivAt (fun w => F w a)
          (fderiv ℂ (fun w => F w a) w₀) (w₀ + (0 : ℂ) • v) := by
        rw [zero_smul, add_zero]
        exact (ha w₀ hw₀).differentiableAt (hU.mem_nhds hw₀) |>.hasFDerivAt
      have h_aff : HasDerivAt (fun t : ℂ => w₀ + t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).smul_const v |>.const_add w₀
      have h_deriv : HasDerivAt (fun t : ℂ => F (w₀ + t • v) a)
          (fderiv ℂ (fun w => F w a) w₀ v) 0 := by
        change HasDerivAt ((fun w => F w a) ∘ (fun t : ℂ => w₀ + t • v))
          (fderiv ℂ (fun w => F w a) w₀ v) 0
        exact ha_at.comp_hasDerivAt 0 h_aff
      have h_slope := h_deriv.tendsto_slope_zero
      have h_inv_tendsto :
          Tendsto (fun k : ℕ => (((k + 1 : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun k => ?_⟩
        · have h1 : Tendsto (fun k : ℕ => (k + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h1
        · rw [mem_compl_singleton_iff, Complex.ofReal_ne_zero]
          positivity
      have h_comp := h_slope.comp h_inv_tendsto
      refine h_comp.congr' ?_
      have h_mem_ev : ∀ᶠ k : ℕ in atTop, zk k ∈ U := by
        have h_t : Tendsto zk atTop (𝓝 w₀) := by
          have h0 : Tendsto (fun k : ℕ => (((k + 1 : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) :=
            tendsto_nhdsWithin_iff.mp h_inv_tendsto |>.1
          simpa [zk] using (h0.smul_const v).const_add w₀
        exact h_t.eventually (hU.mem_nhds hw₀)
      filter_upwards [h_mem_ev] with k hk
      simp only [Function.comp_apply, seq, hk, ↓reduceIte]
      simp [zk, inv_inv]
  have h_eq : (fun a => fderiv ℂ (fun w => F w a) w₀) =
      fun a => (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
                 (fderiv ℂ (fun w => F w a) w₀ (1, 0)) +
               (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
                 (fderiv ℂ (fun w => F w a) w₀ (0, 1)) := by
    ext a : 1
    apply ContinuousLinearMap.ext
    rintro ⟨z₁, z₂⟩
    have hdecomp : (z₁, z₂) =
        z₁ • ((1 : ℂ), (0 : ℂ)) + z₂ • ((0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    conv_lhs => rw [hdecomp, map_add, map_smul, map_smul]
    simp
  rw [h_eq]
  have h1 : Continuous (fun c : ℂ => (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight c) :=
    ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) ℂ
      (ContinuousLinearMap.fst ℂ ℂ ℂ) |>.continuous
  have h2 : Continuous (fun c : ℂ => (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight c) :=
    ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) ℂ
      (ContinuousLinearMap.snd ℂ ℂ ℂ) |>.continuous
  exact (h1.comp_aestronglyMeasurable (h_dir (1, 0))).add
    (h2.comp_aestronglyMeasurable (h_dir (0, 1)))

/-- Combining derivative measurability with the local Lipschitz bound shows that if $F(w, a)$ is
also locally uniformly bounded in norm by an $L^1(\mu)$ function on closed balls in $U$, then the
parametric integral $w \mapsto \int F(w, a)\thinspace d\mu(a)$ is holomorphic on $U$. -/
theorem differentiableOn_integral_of_differentiableOn_of_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : (ℂ × ℂ) → α → ℂ}
    (hF_meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (hF_diff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (fun w => F w a) U)
    (h_bound : ∀ w₀ ∈ U, ∃ r > 0, closedBall w₀ r ⊆ U ∧
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ᵐ a ∂μ, ∀ w ∈ closedBall w₀ r, ‖F w a‖ ≤ bound a) :
    DifferentiableOn ℂ (fun w => ∫ a, F w a ∂μ) U := by
  intro w₀ hw₀
  obtain ⟨r, hr, h_sub, bound, h_bound_int, h_le⟩ := h_bound w₀ hw₀
  have hr2 : 0 < r / 2 := half_pos hr
  have hs_nhds : ball w₀ (r / 2) ∈ 𝓝 w₀ := ball_mem_nhds w₀ hr2
  have hF_meas_ev : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) μ := by
    filter_upwards [hU.mem_nhds hw₀] with w hw
    exact hF_meas w hw
  have hF_int_w₀ : Integrable (F w₀) μ := by
    refine h_bound_int.mono' (hF_meas w₀ hw₀) ?_
    filter_upwards [h_le] with a ha
    exact ha w₀ (mem_closedBall_self hr.le)
  let F' : α → (ℂ × ℂ) →L[ℂ] ℂ := fun a => fderiv ℂ (fun w => F w a) w₀
  have hF'_meas : AEStronglyMeasurable F' μ :=
    aestronglyMeasurable_fderiv_prod hU hw₀ hF_meas hF_diff
  let lip_bound : α → ℝ := fun a => bound a / (r / 2)
  have h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs (lip_bound a)) (fun w => F w a) (ball w₀ (r / 2)) := by
    filter_upwards [hF_diff, h_le] with a ha_diff ha_le
    exact lipschitzOnWith_of_differentiableOn_of_norm_le hU ha_diff hr h_sub ha_le
  have h_lip_int : Integrable lip_bound μ := h_bound_int.div_const (r / 2)
  have h_diff_w₀ : ∀ᵐ a ∂μ, HasFDerivAt (fun w => F w a) (F' a) w₀ := by
    filter_upwards [hF_diff] with a ha
    exact (ha w₀ hw₀).differentiableAt (hU.mem_nhds hw₀) |>.hasFDerivAt
  have h_res := hasFDerivAt_integral_of_dominated_loc_of_lip hs_nhds hF_meas_ev hF_int_w₀
    hF'_meas h_lip h_lip_int h_diff_w₀
  exact h_res.2.differentiableAt.differentiableWithinAt

/-- Similarly, if each term $F_n : E \to \mathbb{C}$ of a series is holomorphic on an open set
$U \subseteq E$ and locally uniformly bounded in norm by a summable sequence on closed balls in $U$,
then $w \mapsto \sum_{n=0}^\infty F_n(w)$ is holomorphic on $U$. -/
theorem differentiableOn_tsum_of_differentiableOn_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {F : ℕ → E → ℂ}
    (hF_diff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U)
    (h_bound : ∀ w₀ ∈ U, ∃ r > 0, closedBall w₀ r ⊆ U ∧
      ∃ bound : ℕ → ℝ, Summable bound ∧
        ∀ n : ℕ, ∀ w ∈ closedBall w₀ r, ‖F n w‖ ≤ bound n) :
    DifferentiableOn ℂ (fun w => ∑' n, F n w) U := by
  intro w₀ hw₀
  obtain ⟨r, hr, h_sub, bound, h_sum, h_le⟩ := h_bound w₀ hw₀
  have hr2 : 0 < r / 2 := half_pos hr
  have h_sum_lip : Summable (fun n => bound n / (r / 2)) := h_sum.div_const (r / 2)
  have h_fderiv_le : ∀ n : ℕ, ∀ w ∈ ball w₀ (r / 2),
      ‖fderiv ℂ (F n) w‖ ≤ bound n / (r / 2) := by
    intro n w hw
    have hw_sub : closedBall w (r / 2) ⊆ closedBall w₀ r := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hw
      calc
        dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle z w w₀
        _ ≤ r / 2 + r / 2 := add_le_add hz hw.le
        _ = r := add_halves r
    exact norm_fderiv_le_of_differentiableOn_of_norm_le hU (hF_diff n) hr2 (hw_sub.trans h_sub)
      (fun z hz => h_le n z (hw_sub hz))
  have h_hasFDeriv : ∀ n : ℕ, ∀ w ∈ ball w₀ (r / 2),
      HasFDerivAt (F n) (fderiv ℂ (F n) w) w := by
    intro n w hw
    have hw_U : w ∈ U :=
      h_sub (ball_subset_closedBall (ball_subset_ball (half_le_self hr.le) hw))
    exact ((hF_diff n w hw_U).differentiableAt (hU.mem_nhds hw_U)).hasFDerivAt
  have h_sum_w₀ : Summable (fun n => F n w₀) :=
    Summable.of_norm_bounded h_sum (fun n => h_le n w₀ (mem_closedBall_self hr.le))
  exact (hasFDerivAt_tsum_of_isPreconnected h_sum_lip isOpen_ball
    (convex_ball w₀ (r / 2)).isPreconnected h_hasFDeriv h_fderiv_le (mem_ball_self hr2)
    h_sum_w₀ (mem_ball_self hr2)).differentiableAt.differentiableWithinAt

end
