/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Compactness.Compact
import CFT.CutPlane
import CFT.Blocks_pdisk

/-!
# Real-Interval Vitali-Type Convergence Theorems for Bounded Holomorphic Families

This file establishes a real-interval Vitali-type convergence theorem for uniformly bounded
families of holomorphic functions on connected open subsets of $\mathbb{C}$.

Compared to the classical Vitali–Porter theorem, our formulation makes two simplifications
tailored to the lightcone bootstrap:
- We assume the limit function $f : \mathbb{C} \to \mathbb{C}$ is already given and known to be
  holomorphic on $U$, and that $F_i \to f$ pointwise on a non-empty open real interval
  $(a, b) \subseteq U$ (rather than on an arbitrary subset with an accumulation point in $U$).
- The proof bypasses Montel's normal-family theorem and Arzelà–Ascoli entirely, using instead
  Tychonoff compactness in the pointwise product topology together with Cauchy's derivative
  estimate:

1. **Cauchy Derivative & Local Lipschitz Bound (`norm_sub_le_of_differentiableOn_of_norm_le`)**:
   Using `Complex.cderiv_eq_deriv` and `Complex.norm_cderiv_le` on closed balls inside an open
   set $U \subseteq \mathbb{C}$, any holomorphic function bounded by $M$ on $\overline{B}(z_0, r)$
   has derivative bounded by $2M/r$ on $B(z_0, r/2)$ and is therefore $(2M/r)$-Lipschitz on
   $B(z_0, r/2)$.
2. **Locally Uniform Convergence from Pointwise Convergence
   (`tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le`)**:
   By the uniform local Lipschitz bound on $B(z_0, r/2)$, pointwise convergence of a uniformly
   bounded holomorphic family on an open set $U$ automatically upgrades to locally uniform
   convergence on $U$, and its limit is holomorphic by `TendstoLocallyUniformlyOn.differentiableOn`.
3. **Real-Interval Vitali-Type Theorem (`vitali_porter_real_interval`, `vitali_porter_ucDisk`)**:
   Instead of invoking Montel's theorem in $C(U, \mathbb{C})$, we work in the pointwise product
   space $\prod_{z \in U} \overline{B}(0, M)$, which is compact by Tychonoff's theorem
   (`isCompact_univ_pi`). By `IsCompact.tendsto_nhds_of_unique_mapClusterPt` and
   `mapClusterPt_iff_ultrafilter`, it suffices to show that every ultrafilter cluster point $g$ in
   the product topology equals $f$. Along any such ultrafilter, pointwise convergence $F_i \to g$ on
   $U$ upgrades to locally uniform convergence by Step 2, so $g$ is holomorphic on $U$ by
   Weierstrass's theorem (`TendstoLocallyUniformlyOn.differentiableOn`). Since $g = f$ on the real
   interval $(a, b) \subseteq U$, the real-interval identity theorem
   (`eqOn_of_differentiableOn_of_eqOn_real_interval`) forces $g = f$ throughout $U$.
-/

noncomputable section

open Complex Metric Set Filter Topology

namespace CFT

/-- **Cauchy Derivative Estimate on an Open Ball**:
If $f$ is holomorphic on $U$, $\overline{B}(z_0, r) \subseteq U$ with $r > 0$, and $\|f(z)\| \le M$
on $\overline{B}(z_0, r)$, then for every $w \in B(z_0, r/2)$ we have
$\|f'(w)\| \le M / (r/2)$. -/
lemma norm_deriv_le_of_differentiableOn_of_norm_le {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (h_sub : closedBall z₀ r ⊆ U) (hM : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M)
    {w : ℂ} (hw : w ∈ ball z₀ (r / 2)) :
    ‖deriv f w‖ ≤ M / (r / 2) := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hw_sub : closedBall w (r / 2) ⊆ closedBall z₀ r := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    rw [mem_ball] at hw
    calc
      dist z z₀ ≤ dist z w + dist w z₀ := dist_triangle z w z₀
      _ ≤ r / 2 + r / 2 := add_le_add hz hw.le
      _ = r := add_halves r
  have h_cderiv := Complex.cderiv_eq_deriv hU hf hr2 (hw_sub.trans h_sub)
  rw [← h_cderiv]
  refine Complex.norm_cderiv_le hr2 (fun z hz => hM z (hw_sub (sphere_subset_closedBall hz)))

/-- **Local Lipschitz Estimate for Bounded Holomorphic Functions**:
If $f$ is holomorphic on an open set $U$, $\overline{B}(z_0, r) \subseteq U$ with $r > 0$, and
$\|f(z)\| \le M$ on $\overline{B}(z_0, r)$, then for every $w \in B(z_0, r/2)$ we have
$\|f(w) - f(z_0)\| \le (M / (r / 2)) \|w - z_0\|$. -/
lemma norm_sub_le_of_differentiableOn_of_norm_le {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (h_sub : closedBall z₀ r ⊆ U) (hM : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M)
    {w : ℂ} (hw : w ∈ ball z₀ (r / 2)) :
    ‖f w - f z₀‖ ≤ (M / (r / 2)) * ‖w - z₀‖ := by
  have hr2 : 0 < r / 2 := half_pos hr
  have h_ball_sub : ball z₀ (r / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans h_sub
  have hf_diff : ∀ z ∈ ball z₀ (r / 2), DifferentiableAt ℂ f z :=
    fun z hz => (hf z (h_ball_sub hz)).differentiableAt (hU.mem_nhds (h_ball_sub hz))
  have hf_deriv : ∀ z ∈ ball z₀ (r / 2), ‖deriv f z‖ ≤ M / (r / 2) :=
    fun z hz => norm_deriv_le_of_differentiableOn_of_norm_le hU hf hr h_sub hM hz
  exact Convex.norm_image_sub_le_of_norm_deriv_le hf_diff hf_deriv (convex_ball z₀ (r / 2))
    (mem_ball_self hr2) hw

/-- **Pointwise Convergence of Uniformly Bounded Holomorphic Functions Upgrades to Locally
Uniform Convergence**:
If a family $F_i$ is eventually holomorphic and bounded by $M$ on an open set
$U \subseteq \mathbb{C}$, and $F_i(z) \to f(z)$ pointwise on $U$ along a filter $p$, then
$F_i \to f$ locally uniformly on $U$. -/
theorem tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le
    {ι : Type*} {U : Set ℂ} (hU : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {p : Filter ι} {M : ℝ}
    (hF : ∀ᶠ i in p, DifferentiableOn ℂ (F i) U)
    (hM : ∀ᶠ i in p, ∀ z ∈ U, ‖F i z‖ ≤ M)
    (hf : ∀ z ∈ U, Tendsto (fun i => F i z) p (𝓝 (f z))) :
    TendstoLocallyUniformlyOn F f p U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z₀ hz₀
  rcases p.eq_or_neBot with rfl | hp
  · exact ⟨U, self_mem_nhdsWithin, eventually_bot⟩
  obtain ⟨r, hr, h_sub⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hr1 : 0 < r / 2 := half_pos hr
  have h_cb_sub : closedBall z₀ (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans h_sub
  have hr2 : 0 < r / 2 / 2 := half_pos hr1
  obtain ⟨i₀, _, hi₀M⟩ := (hF.and hM).exists
  have hM_nonneg : 0 ≤ M := (norm_nonneg (F i₀ z₀)).trans (hi₀M z₀ hz₀)
  set L : ℝ := M / (r / 2 / 2) + 1
  have hL_pos : 0 < L := by positivity
  set δ : ℝ := min (r / 2 / 2) (ε / 3 / L)
  have hδ_pos : 0 < δ := lt_min hr2 (div_pos (by linarith) hL_pos)
  have h_lip_F : ∀ᶠ i in p, ∀ w ∈ ball z₀ δ, ‖F i w - F i z₀‖ ≤ L * δ := by
    filter_upwards [hF, hM] with i hiF hiM w hw
    have hw_r2 : w ∈ ball z₀ (r / 2 / 2) :=
      ball_subset_ball (min_le_left _ _) hw
    have h_step := norm_sub_le_of_differentiableOn_of_norm_le hU hiF hr1 h_cb_sub
      (fun z hz => hiM z (h_cb_sub hz)) hw_r2
    have h_dist : ‖w - z₀‖ ≤ δ := by
      rw [← dist_eq_norm]
      exact (mem_ball.mp hw).le
    calc
      ‖F i w - F i z₀‖ ≤ (M / (r / 2 / 2)) * ‖w - z₀‖ := h_step
      _ ≤ L * ‖w - z₀‖ := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _)
      _ ≤ L * δ := mul_le_mul_of_nonneg_left h_dist hL_pos.le
  have h_lip_f : ∀ w ∈ ball z₀ δ, ‖f w - f z₀‖ ≤ L * δ := by
    intro w hw
    have hw_r1 : w ∈ ball z₀ (r / 2) :=
      ball_subset_ball ((min_le_left _ _).trans (half_le_self hr1.le)) hw
    have hw_U : w ∈ U := h_cb_sub (ball_subset_closedBall hw_r1)
    have h_tendsto : Tendsto (fun i => ‖F i w - F i z₀‖) p (𝓝 ‖f w - f z₀‖) :=
      ((hf w hw_U).sub (hf z₀ hz₀)).norm
    exact le_of_tendsto h_tendsto (h_lip_F.mono fun i hi => hi w hw)
  have hLδ_le : L * δ ≤ ε / 3 := by
    have h_le : L * δ ≤ L * (ε / 3 / L) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hL_pos.le
    rwa [mul_div_cancel₀ _ hL_pos.ne'] at h_le
  refine ⟨U ∩ ball z₀ δ, inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hδ_pos), ?_⟩
  have h_z₀_conv : ∀ᶠ i in p, ‖f z₀ - F i z₀‖ < ε / 3 := by
    have h_t := Metric.tendsto_nhds.mp (hf z₀ hz₀) (ε / 3) (by linarith)
    filter_upwards [h_t] with i hi
    rwa [dist_comm, dist_eq_norm] at hi
  filter_upwards [h_lip_F, h_z₀_conv] with i hi_lip hi_z₀ w ⟨_, hw_ball⟩
  rw [dist_eq_norm]
  have h_tri : ‖f w - F i w‖ ≤ ‖f w - f z₀‖ + ‖f z₀ - F i z₀‖ + ‖F i z₀ - F i w‖ := by
    calc
      ‖f w - F i w‖ = ‖(f w - f z₀) + (f z₀ - F i z₀) + (F i z₀ - F i w)‖ := by ring_nf
      _ ≤ ‖f w - f z₀‖ + ‖f z₀ - F i z₀‖ + ‖F i z₀ - F i w‖ := norm_add₃_le
  rw [norm_sub_rev (F i z₀) (F i w)] at h_tri
  linarith [h_lip_f w hw_ball, hi_lip w hw_ball]

/-- **Real-Interval Vitali-Type Theorem on a Preconnected Open Domain**:
Let $U \subseteq \mathbb{C}$ be open and preconnected, and let $(a, b) \subseteq \mathbb{R}$ be a
non-empty open interval embedded in $U$. If $F_i : \mathbb{C} \to \mathbb{C}$ is eventually
holomorphic and uniformly bounded by $M$ on $U$ along a filter $p$, $f : \mathbb{C} \to \mathbb{C}$
is holomorphic on $U$, and $F_i(x) \to f(x)$ for every $x \in (a, b)$, then $F_i \to f$ locally
uniformly on $U$.

Unlike the general Vitali–Porter theorem, this assumes convergence on an entire open real interval
$(a, b) \subseteq U$ to a known holomorphic limit $f$, and bypasses Montel's theorem by combining
Tychonoff compactness in the pointwise product topology $\prod_{z \in U} \overline{B}(0, M)$ with
`tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le` and the real-interval identity theorem
`eqOn_of_differentiableOn_of_eqOn_real_interval`. -/
theorem vitali_porter_real_interval
    {ι : Type*} {U : Set ℂ} (hU : IsOpen U) (hU_conn : IsPreconnected U)
    {a b : ℝ} (hab : a < b) (h_sub : (fun x : ℝ => (x : ℂ)) '' Ioo a b ⊆ U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {p : Filter ι} {M : ℝ}
    (hF : ∀ᶠ i in p, DifferentiableOn ℂ (F i) U)
    (hM : ∀ᶠ i in p, ∀ z ∈ U, ‖F i z‖ ≤ M)
    (hf : DifferentiableOn ℂ f U)
    (h_real : ∀ x ∈ Ioo a b, Tendsto (fun i => F i (x : ℂ)) p (𝓝 (f (x : ℂ)))) :
    TendstoLocallyUniformlyOn F f p U := by
  classical
  refine tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le hU hF hM ?_
  have h_pt : Tendsto (fun i => U.domRestrict (F i)) p (𝓝 (U.domRestrict f)) := by
    let S : Set (U → ℂ) := Set.pi univ (fun _ : U => closedBall (0 : ℂ) M)
    have hS_compact : IsCompact S := isCompact_univ_pi (fun _ => isCompact_closedBall 0 M)
    have h_mem : ∀ᶠ i in p, U.domRestrict (F i) ∈ S := by
      filter_upwards [hM] with i hi z _
      rw [mem_closedBall_zero_iff]
      exact hi z.1 z.2
    refine hS_compact.tendsto_nhds_of_unique_mapClusterPt h_mem ?_
    intro g₀ _ hg₀
    rw [mapClusterPt_iff_ultrafilter] at hg₀
    obtain ⟨u, hu_le, hu_tendsto⟩ := hg₀
    let g : ℂ → ℂ := fun z => if hz : z ∈ U then g₀ ⟨z, hz⟩ else 0
    have hg_pt : ∀ z ∈ U, Tendsto (fun i => F i z) (↑u) (𝓝 (g z)) := by
      intro z hz
      have h_eval := (continuous_apply ⟨z, hz⟩).tendsto g₀ |>.comp hu_tendsto
      have h_gz : g z = g₀ ⟨z, hz⟩ := by simp [g, hz]
      rw [h_gz]
      exact h_eval
    have hF_u : ∀ᶠ i in (↑u : Filter ι), DifferentiableOn ℂ (F i) U := hu_le hF
    have hM_u : ∀ᶠ i in (↑u : Filter ι), ∀ z ∈ U, ‖F i z‖ ≤ M := hu_le hM
    have h_loc_u : TendstoLocallyUniformlyOn F g (↑u) U :=
      tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le hU hF_u hM_u hg_pt
    have hg_diff : DifferentiableOn ℂ g U := h_loc_u.differentiableOn hF_u hU
    have hg_eq_f_real : ∀ x ∈ Ioo a b, g (x : ℂ) = f (x : ℂ) := by
      intro x hx
      have hx_U : (x : ℂ) ∈ U := h_sub ⟨x, hx, rfl⟩
      exact tendsto_nhds_unique (hg_pt (x : ℂ) hx_U) ((h_real x hx).mono_left hu_le)
    have hx₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have h_eqOn : EqOn g f U :=
      eqOn_of_differentiableOn_of_eqOn_real_interval hU hU_conn hg_diff hf
        a b ((a + b) / 2) hx₀ h_sub hg_eq_f_real
    ext ⟨z, hz⟩
    have h_gz : g z = g₀ ⟨z, hz⟩ := by simp [g, hz]
    change g₀ ⟨z, hz⟩ = f z
    rw [← h_gz]
    exact h_eqOn hz
  intro z hz
  exact (continuous_apply ⟨z, hz⟩).tendsto (U.domRestrict f) |>.comp h_pt

/-- **Real-Interval Vitali-Type Theorem on `UcDisk`**:
If $F_i$ is eventually holomorphic on
$\operatorname{UcDisk} = \{w \in \mathbb{C} \mid \operatorname{Re}(w) < 0\}$, uniformly bounded on
every left half-plane $\{w \mid \operatorname{Re}(w) < \sigma\}$ ($\sigma < 0$), $f$ is
holomorphic on $\operatorname{UcDisk}$, and $F_i(\sigma) \to f(\sigma)$ for all real $\sigma < 0$,
then $F_i(w) \to f(w)$ for every $w \in \operatorname{UcDisk}$. -/
theorem vitali_porter_ucDisk
    {ι : Type*} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {p : Filter ι}
    (hF : ∀ᶠ i in p, DifferentiableOn ℂ (F i) UcDisk)
    (hf : DifferentiableOn ℂ f UcDisk)
    (h_bound : ∀ σ < (0 : ℝ), ∃ M : ℝ, ∀ᶠ i in p, ∀ z : ℂ, z.re < σ → ‖F i z‖ ≤ M)
    (h_real : ∀ x < (0 : ℝ), Tendsto (fun i => F i (x : ℂ)) p (𝓝 (f (x : ℂ))))
    {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto (fun i => F i w) p (𝓝 (f w)) := by
  have hw_re : w.re < 0 := hw
  set σ : ℝ := w.re / 2
  have hσ_neg : σ < 0 := by dsimp [σ]; linarith
  let U : Set ℂ := {z : ℂ | z.re < σ}
  have hU_sub : U ⊆ UcDisk := fun z hz => lt_trans hz hσ_neg
  have hU_open : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hU_conn : IsPreconnected U :=
    (convex_halfSpace_lt Complex.reLm.isLinear σ).isPreconnected
  have hw_U : w ∈ U := by
    change w.re < w.re / 2
    linarith
  have h_Ioo_sub : (fun x : ℝ => (x : ℂ)) '' Ioo (σ - 1) σ ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    change (x : ℂ).re < σ
    simpa using hx.2
  obtain ⟨M, hM⟩ := h_bound σ hσ_neg
  have h_loc := vitali_porter_real_interval hU_open hU_conn (by linarith : σ - 1 < σ) h_Ioo_sub
    (hF.mono fun i hi => hi.mono hU_sub) hM (hf.mono hU_sub)
    (fun x hx => h_real x (lt_trans hx.2 hσ_neg))
  exact h_loc.tendsto_at hw_U

end CFT
