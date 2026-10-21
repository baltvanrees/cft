/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import CFT.CutPlane
import CFT.Blocks_pdisk
import CFT.Corr

/-!
# Polydisk Four-Point Functions & Analytic Continuation on `UcPdisk`

This file extends `FourPointData` and the Euclidean correlator from `Corr.lean` to the universal
cover of the punctured polydisk $(w_l, w_r) \in \operatorname{UcPdisk}$
(where $\rho_l = e^{w_l}, \rho_r = e^{w_r}$ with
$\operatorname{Re}(w_l) < 0, \operatorname{Re}(w_r) < 0$) and to independent complex coordinates
$(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$, by integrating the continued conformal
blocks from `Blocks_pdisk.lean` against the OPE measure `corr.mu_measure`.

We establish three main results:
1. **Polydisk OPE Convergence (`FourPointData.converges_correlator_pdisk`)**:
   Because `corr.mu_measure` is supported on unitary twist $\Delta \ge l$ (`ae_unitary`) and
   $\|G_{\Delta, l}^{\text{pdisk}}(w_l, w_r)\| \le G_{\Delta, l}(e^{\max(\operatorname{Re} w_l,
   \operatorname{Re} w_r)})$ (`ConformalBlock.norm_evalPdisk_le_eval`), Euclidean OPE convergence
   (that is, integrability of the Euclidean blocks against `corr.mu_measure`)
   at $r = e^{\max(\operatorname{Re} w_l, \operatorname{Re} w_r)} \in (0, 1)$ immediately implies
   integrability at every point $(w_l, w_r) \in \operatorname{UcPdisk}$.
2. **Joint Holomorphy on $\operatorname{UcPdisk}$
   (`FourPointData.differentiableOn_correlator_pdisk`)**:
   On any closed ball $\overline{B}(w_0, \delta) \subseteq \operatorname{UcPdisk}$ where both
   coordinates satisfy $\operatorname{Re}(w_l), \operatorname{Re}(w_r) \le \sigma < 0$, the
   integrand is uniformly dominated by the integrable Euclidean block
   $G_{\Delta, l}(e^\sigma)$. Applying
   `CFT.differentiableOn_integral_of_differentiableOn_of_norm_le` from
   `CFT/Analysis/DominatedHolomorphy.lean` proves joint holomorphy on $\operatorname{UcPdisk}$.
3. **Analytic Continuation of Crossing Symmetry (`FourPointData.crossing_correlator`)**:
   Starting from Euclidean crossing symmetry on the conjugate section $z_r = \bar{z}_l$
   (`crossing_correlator_eucl`), we first apply the 1D real-interval identity theorem along
   complexified Euclidean slices $y \mapsto (x_0 + i y, x_0 - i y)$ to deduce real-interval
   crossing (`crossing_lhs_real`) for $(x_l, x_r) \in (0, 1)^2$, and then apply the identity
   theorem on $\operatorname{CutPlane}$ (`eqOn_CutPlane_of_differentiableOn_of_eqOn_interval`)
   in each variable separately to obtain full two-variable crossing on
   $\operatorname{CutPlane} \times \operatorname{CutPlane}$.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate

/-- Evaluation of the four-point correlator on $\operatorname{UcPdisk}$ from a family of
`ConformalBlock`s continued to $(w_l, w_r)$ and integrated against the OPE measure $\mu$:
$$\mathcal{G}_{\text{pdisk}}(w_l, w_r) =
  \int G_{\Delta, l}^{\text{pdisk}}(w_l, w_r) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_pdisk {ν : ℝ}
    (blocks : ∀ (Δ : ℝ) (l : ℕ), ConformalBlock ν Δ l)
    (mu : Measure (ℝ × ℕ)) (wl wr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (blocks p.1 p.2).evalPdisk wl wr ∂mu

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- The four-point correlator continued to $(w_l, w_r) \in \operatorname{UcPdisk}$ using the OPE
measure `corr.mu_measure` and the polydisk continuation of `corr.blocks`. -/
noncomputable def correlator_pdisk (wl wr : ℂ) : ℂ :=
  eval_correlator_pdisk corr.blocks corr.mu_measure wl wr

/-- The physical four-point correlator as a function of independent complex coordinates
$(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$, mapped into $\operatorname{UcPdisk}$ via
$(\operatorname{logRho}(z_l), \operatorname{logRho}(z_r))$. -/
noncomputable def correlator (zl zr : ℂ) : ℂ :=
  corr.correlator_pdisk (logRho zl) (logRho zr)

/-- Direct-channel side of the crossing equation for independent complex coordinates
$(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$:
$$z_l^{-\Delta_\phi} z_r^{-\Delta_\phi} \mathcal{G}(z_l, z_r).$$ -/
noncomputable def crossing_lhs (zl zr : ℂ) : ℂ :=
  zl ^ (- (Δ_phi : ℂ)) * zr ^ (- (Δ_phi : ℂ)) * corr.correlator zl zr

/-!
## Convergence, Holomorphy, and Analytic Continuation of Crossing Symmetry
-/

/-- Almost everywhere unitarity bound $(l : \mathbb{R}) \le \Delta$ with respect to
`corr.mu_measure`. A direct consequence of the unitarity assumption in `CFT.Corr`. -/
lemma ae_unitary : ∀ᵐ p : ℝ × ℕ ∂corr.mu_measure, (p.2 : ℝ) ≤ p.1 := by
  rw [ae_iff]
  convert corr.support_unitary using 2
  ext p
  simp [not_le]

/-- Measurability of the level-$n$ descendant contribution to the polydisk block
across the spectrum $(\Delta, l)$. This in turn is used in
`measurable_evalPdisk` below to establish measurability of the full block. -/
lemma measurable_evalTermPdisk (n : ℕ) (wl wr : ℂ) :
    Measurable (fun p : ℝ × ℕ => ((corr.blocks p.1 p.2).level n).evalTermPdisk ν p.1 wl wr) := by
  let term : ℕ → (ℝ × ℕ) → ℂ := fun j p =>
    (((corr.blocks p.1 p.2).level n).A j : ℂ) *
      Complex.exp ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wl) *
      Complex.exp ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wr) *
      gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j
  have h_term_meas : ∀ j : ℕ, Measurable (term j) := by
    intro j
    have hA_j := corr.measurable_A n j
    dsimp [term]
    fun_prop
  let partial_sum : ℕ → (ℝ × ℕ) → ℂ := fun M p => ∑ j ∈ Finset.range M, term j p
  have h_part_meas : ∀ M : ℕ, Measurable (partial_sum M) :=
    fun M => Finset.measurable_sum (Finset.range M) (fun j _ => h_term_meas j)
  refine measurable_of_tendsto_metrizable (f := partial_sum) h_part_meas (tendsto_pi_nhds.mpr ?_)
  intro p
  refine tendsto_atTop_of_eventually_const (i₀ := p.2 + n + 1) fun M hM => ?_
  dsimp [partial_sum, ConformalBlockLevel.evalTermPdisk, term]
  refine (Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)).symm
  · rw [Finset.mem_range]
    have hj_le : j ≤ p.2 + n := (mem_descendantSpins.mp hj).2.1
    omega
  · rw [((corr.blocks p.1 p.2).level n).A_support j hj, Complex.ofReal_zero, zero_mul, zero_mul,
      zero_mul]

/-- Measurability of the full polydisk conformal block across the spectrum on
$\operatorname{UcPdisk}$. -/
lemma measurable_evalPdisk (wl wr : ℂ) :
    Measurable (fun p : ℝ × ℕ => (corr.blocks p.1 p.2).evalPdisk wl wr) := by
  dsimp [ConformalBlock.evalPdisk]
  have h := fun n => corr.measurable_evalTermPdisk n wl wr
  fun_prop

/-- Polydisk OPE convergence on $\operatorname{UcPdisk}$, deduced from (postulated) Euclidean
OPE convergence `corr.converges_correlator_eucl` and the bound `norm_evalPdisk_le_eval` for the
conformal block in the polydisk in terms of the conformal block on the Euclidean section. -/
theorem converges_correlator_pdisk (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Integrable (fun p : ℝ × ℕ => (corr.blocks p.1 p.2).evalPdisk wl wr) corr.mu_measure := by
  set r : ℝ := Real.exp (max wl.re wr.re)
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (max_lt hwl hwr)
  have hr_mem : (r : ℂ) ∈ ball (0 : ℂ) 1 \ {0} := by
    refine ⟨?_, by simp [hr_pos.ne']⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    exact hr_lt1
  refine (corr.converges_correlator_eucl (r : ℂ) hr_mem).mono'
    (corr.measurable_evalPdisk wl wr).aestronglyMeasurable ?_
  filter_upwards [corr.ae_unitary] with p hp
  exact (corr.blocks p.1 p.2).norm_evalPdisk_le_eval hν hp hwl hwr

/-- On the Euclidean section $w_r = \bar{w}$, `correlator_pdisk` agrees with the Euclidean
correlator at $\rho = e^w$. -/
theorem correlator_pdisk_conj_eq_eucl (hν : 0 ≤ ν) (w : ℂ) :
    corr.correlator_pdisk w (conj w) = (corr.correlator_eucl (Complex.exp w) : ℂ) := by
  dsimp [correlator_pdisk, eval_correlator_pdisk, correlator_eucl, eval_correlator_eucl]
  simp_rw [(corr.blocks _ _).evalPdisk_conj_eq_eval hν w]
  exact integral_ofReal

/-- On the Euclidean section $z_r = \bar{z}$ for $z \in \text{CutPlane}$, the continued correlator
`corr.correlator z (conj z)` agrees with the Euclidean correlator `corr.correlator_z z`. -/
theorem correlator_conj_eq_eucl (hν : 0 ≤ ν) {z : ℂ} (hz : z ∈ CutPlane) :
    corr.correlator z (conj z) = (corr.correlator_z z : ℂ) := by
  dsimp [correlator, correlator_z]
  rw [conj_logRho hz, corr.correlator_pdisk_conj_eq_eucl hν (logRho z), exp_logRho hz]

/-- Joint holomorphy of `correlator_pdisk` on the universal-cover polydisk
$\operatorname{UcPdisk}$. -/
theorem differentiableOn_correlator_pdisk (hν : 0 ≤ ν) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ => corr.correlator_pdisk w.1 w.2) UcPdisk := by
  dsimp [correlator_pdisk, eval_correlator_pdisk]
  refine CFT.differentiableOn_integral_of_differentiableOn_of_norm_le isOpen_UcPdisk
    (fun w _ => (corr.measurable_evalPdisk w.1 w.2).aestronglyMeasurable)
    (corr.ae_unitary.mono fun p hp => (corr.blocks p.1 p.2).differentiableOn_evalPdisk hν hp) ?_
  intro w₀ hw₀
  obtain ⟨δ, hδ, σ, hσ, h_sub, h_re⟩ := exists_closedBall_subset_UcPdisk hw₀
  set r : ℝ := Real.exp σ
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr hσ
  have hr_mem : (r : ℂ) ∈ ball (0 : ℂ) 1 \ {0} := by
    refine ⟨?_, by simp [hr_pos.ne']⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
    exact hr_lt1
  refine ⟨δ, hδ, h_sub, fun p => (corr.blocks p.1 p.2).eval (r : ℂ),
    corr.converges_correlator_eucl (r : ℂ) hr_mem, ?_⟩
  filter_upwards [corr.ae_unitary] with p hp w hw
  obtain ⟨hw1, hw2⟩ := h_re w hw
  exact (corr.blocks p.1 p.2).norm_evalPdisk_le_eval_of_re_le hν hp hσ hw1 hw2

/-- The physical correlator is holomorphic along any pair of holomorphic curves in `CutPlane`. -/
theorem differentiableAt_correlator_comp (hν : 0 ≤ ν) {φ ψ : ℂ → ℂ} {y : ℂ}
    (hφ : DifferentiableAt ℂ φ y) (hψ : DifferentiableAt ℂ ψ y)
    (hφy : φ y ∈ CutPlane) (hψy : ψ y ∈ CutPlane) :
    DifferentiableAt ℂ (fun t => corr.correlator (φ t) (ψ t)) y := by
  have hlogφ : DifferentiableAt ℂ (fun t => logRho (φ t)) y :=
    (differentiableAt_logRho hφy).comp y hφ
  have hlogψ : DifferentiableAt ℂ (fun t => logRho (ψ t)) y :=
    (differentiableAt_logRho hψy).comp y hψ
  have hmem : (logRho (φ y), logRho (ψ y)) ∈ UcPdisk :=
    ⟨logRho_mem_UcDisk hφy, logRho_mem_UcDisk hψy⟩
  have hjoint : DifferentiableAt ℂ (fun p : ℂ × ℂ => corr.correlator_pdisk p.1 p.2)
      (logRho (φ y), logRho (ψ y)) :=
    (corr.differentiableOn_correlator_pdisk hν).differentiableAt
      (isOpen_UcPdisk.mem_nhds hmem)
  have hcomp : DifferentiableAt ℂ ((fun p : ℂ × ℂ => corr.correlator_pdisk p.1 p.2) ∘
      (fun t => (logRho (φ t), logRho (ψ t)))) y := hjoint.comp y (hlogφ.prodMk hlogψ)
  exact hcomp

/-- Holomorphy of `corr.correlator` in the first variable $z_l \in \text{CutPlane}$ for fixed
$z_r \in \text{CutPlane}$. -/
theorem differentiableOn_correlator_left (hν : 0 ≤ ν) {zr : ℂ} (hzr : zr ∈ CutPlane) :
    DifferentiableOn ℂ (fun zl => corr.correlator zl zr) CutPlane := fun _ hzl =>
  (corr.differentiableAt_correlator_comp hν differentiableAt_id
    (differentiableAt_const _) hzl hzr).differentiableWithinAt

/-- Holomorphy of `corr.correlator` in the second variable $z_r \in \text{CutPlane}$ for fixed
$z_l \in \text{CutPlane}$. -/
theorem differentiableOn_correlator_right (hν : 0 ≤ ν) {zl : ℂ} (hzl : zl ∈ CutPlane) :
    DifferentiableOn ℂ (fun zr => corr.correlator zl zr) CutPlane := fun _ hzr =>
  (corr.differentiableAt_correlator_comp hν (differentiableAt_const _)
    differentiableAt_id hzl hzr).differentiableWithinAt

/-- `crossing_lhs` is holomorphic along any pair of holomorphic curves in `CutPlane`. -/
theorem differentiableAt_crossing_lhs (hν : 0 ≤ ν) {φ ψ : ℂ → ℂ} {y : ℂ}
    (hφ : DifferentiableAt ℂ φ y) (hψ : DifferentiableAt ℂ ψ y)
    (hφy : φ y ∈ CutPlane) (hψy : ψ y ∈ CutPlane) :
    DifferentiableAt ℂ (fun t => corr.crossing_lhs (φ t) (ψ t)) y := by
  simp only [crossing_lhs]
  exact ((hφ.cpow_const hφy.2).mul (hψ.cpow_const hψy.2)).mul
    (corr.differentiableAt_correlator_comp hν hφ hψ hφy hψy)

/-- Crossing symmetry on the Euclidean section $z_r = \bar{z}$ for $z \in \text{CutPlane}$. -/
theorem crossing_correlator_euclidean (hν : 0 ≤ ν) {z : ℂ} (hz : z ∈ CutPlane) :
    (‖z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) * corr.correlator z (conj z) =
    (‖1 - z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) * corr.correlator (1 - z) (conj (1 - z)) := by
  have h_eucl := corr.crossing_correlator_eucl z hz
  rw [corr.correlator_conj_eq_eucl hν hz,
    corr.correlator_conj_eq_eucl hν (CutPlane.sub_one hz)]
  dsimp [correlator_z, correlator_eucl]
  have hz_pos : 0 ≤ ‖z‖ := norm_nonneg z
  have h1z_pos : 0 ≤ ‖1 - z‖ := norm_nonneg (1 - z)
  have h_pow1 : (‖z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) = ↑(‖z‖ ^ (-2 * Δ_phi)) := by
    have : (-2 * (Δ_phi : ℂ)) = ((-2 * Δ_phi : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact (ofReal_cpow hz_pos (-2 * Δ_phi)).symm
  have h_pow2 : (‖1 - z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) = ↑(‖1 - z‖ ^ (-2 * Δ_phi)) := by
    have : (-2 * (Δ_phi : ℂ)) = ((-2 * Δ_phi : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact (ofReal_cpow h1z_pos (-2 * Δ_phi)).symm
  rw [h_pow1, h_pow2, ← ofReal_mul, ← ofReal_mul, h_eucl]

/-- Crossing symmetry on the Euclidean section $z_r = \bar{z}$ for $z \in \text{CutPlane}$,
written in terms of `crossing_lhs`. -/
theorem crossing_correlator_euclidean_section (hν : 0 ≤ ν) {z : ℂ} (hz : z ∈ CutPlane) :
    corr.crossing_lhs z (conj z) = corr.crossing_lhs (1 - z) (1 - conj z) := by
  dsimp [crossing_lhs]
  have h1 : z ^ (- (Δ_phi : ℂ)) * (conj z) ^ (- (Δ_phi : ℂ)) =
      (‖z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) :=
    cpow_mul_conj_cpow hz.2
  have h1z_cut : 1 - z ∈ CutPlane := CutPlane.sub_one hz
  have h2 : (1 - z) ^ (- (Δ_phi : ℂ)) * (conj (1 - z)) ^ (- (Δ_phi : ℂ)) =
      (‖1 - z‖ : ℂ) ^ (-2 * (Δ_phi : ℂ)) :=
    cpow_mul_conj_cpow h1z_cut.2
  have h_conj_sub : conj (1 - z) = 1 - conj z := by simp
  have h_eucl := corr.crossing_correlator_euclidean hν hz
  rw [h_conj_sub] at h2 h_eucl
  rw [h1, h2, h_eucl]

/-- Crossing symmetry restricted to independent real coordinates $x_l, x_r \in (0, 1)$, obtained
from the Euclidean section by continuing $z_{l, r} = x_0 \pm i y$ in $y$. -/
theorem crossing_lhs_real (hν : 0 ≤ ν) {xl xr : ℝ}
    (hxl : xl ∈ Ioo (0 : ℝ) 1) (hxr : xr ∈ Ioo (0 : ℝ) 1) :
    corr.crossing_lhs (xl : ℂ) (xr : ℂ) = corr.crossing_lhs (1 - (xl : ℂ)) (1 - (xr : ℂ)) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = (xl + xr) / 2 := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (xl - xr) / 2 := ⟨_, rfl⟩
  set r := min x₀ (1 - x₀) with hr
  have hτr : |τ| < r := by
    rw [abs_lt]
    obtain ⟨h1, h2⟩ := hxl
    obtain ⟨h3, h4⟩ := hxr
    refine ⟨?_, ?_⟩
    · rw [hr]
      rcases min_choice x₀ (1 - x₀) with h | h <;> rw [h] <;> linarith
    · exact lt_min (by linarith) (by linarith)
  have hr_pos : 0 < r := lt_of_le_of_lt (abs_nonneg τ) hτr
  have hdiff_f : DifferentiableOn ℂ
      (fun y : ℂ => corr.crossing_lhs ((x₀ : ℂ) + I * y) ((x₀ : ℂ) - I * y)) (ball 0 r) := by
    intro y hy
    have hy' : ‖y‖ < r := mem_ball_zero_iff.mp hy
    exact (corr.differentiableAt_crossing_lhs hν (φ := fun y : ℂ => (x₀ : ℂ) + I * y)
      (ψ := fun y : ℂ => (x₀ : ℂ) - I * y) (by fun_prop) (by fun_prop)
      (add_I_mul_mem_CutPlane hy') (sub_I_mul_mem_CutPlane hy')).differentiableWithinAt
  have hdiff_g : DifferentiableOn ℂ
      (fun y : ℂ => corr.crossing_lhs (1 - ((x₀ : ℂ) + I * y)) (1 - ((x₀ : ℂ) - I * y)))
      (ball 0 r) := by
    intro y hy
    have hy' : ‖y‖ < r := mem_ball_zero_iff.mp hy
    exact (corr.differentiableAt_crossing_lhs hν (φ := fun y : ℂ => 1 - ((x₀ : ℂ) + I * y))
      (ψ := fun y : ℂ => 1 - ((x₀ : ℂ) - I * y)) (by fun_prop) (by fun_prop)
      (CutPlane.sub_one (add_I_mul_mem_CutPlane hy'))
      (CutPlane.sub_one (sub_I_mul_mem_CutPlane hy'))).differentiableWithinAt
  have h_sub : (fun x : ℝ => (x : ℂ)) '' Ioo (-r) r ⊆ ball (0 : ℂ) r := by
    rintro z ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact hx
  have h_zero : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr_pos⟩
  have h_eq_real : ∀ y ∈ Ioo (-r) r,
      (fun y : ℂ => corr.crossing_lhs ((x₀ : ℂ) + I * y) ((x₀ : ℂ) - I * y)) (y : ℂ) =
      (fun y : ℂ => corr.crossing_lhs (1 - ((x₀ : ℂ) + I * y)) (1 - ((x₀ : ℂ) - I * y)))
        (y : ℂ) := by
    intro y hy
    dsimp only
    have hy' : ‖(y : ℂ)‖ < r := h_sub ⟨y, hy, rfl⟩ |> mem_ball_zero_iff.mp
    have hz := add_I_mul_mem_CutPlane hy'
    have hconj : conj ((x₀ : ℂ) + I * (y : ℂ)) = (x₀ : ℂ) - I * (y : ℂ) := by
      simp [map_add, map_mul, conj_I, conj_ofReal]; ring
    have h := corr.crossing_correlator_euclidean_section hν hz
    rw [hconj] at h
    exact h
  have h_eqOn := eqOn_of_differentiableOn_of_eqOn_real_interval isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected hdiff_f hdiff_g (-r) r 0 h_zero h_sub h_eq_real
  have hmem : (-I * (τ : ℂ)) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact hτr
  have h := h_eqOn hmem
  dsimp only at h
  have hII : I * (-I * (τ : ℂ)) = (τ : ℂ) := by
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  have e1 : (x₀ : ℂ) + I * (-I * (τ : ℂ)) = (xl : ℂ) := by
    rw [hII, hx₀, hτ]; push_cast; ring
  have e2 : (x₀ : ℂ) - I * (-I * (τ : ℂ)) = (xr : ℂ) := by
    rw [hII, hx₀, hτ]; push_cast; ring
  rw [e1, e2] at h
  exact h

/-- Analytically continued crossing symmetry on $\text{CutPlane} \times \text{CutPlane}$:
$$z_l^{-\Delta_\phi} z_r^{-\Delta_\phi} \mathcal{G}(z_l, z_r) =
  (1 - z_l)^{-\Delta_\phi} (1 - z_r)^{-\Delta_\phi} \mathcal{G}(1 - z_l, 1 - z_r).$$ -/
theorem crossing_correlator (hν : 0 ≤ ν) {zl zr : ℂ}
    (hzl : zl ∈ CutPlane) (hzr : zr ∈ CutPlane) :
    corr.crossing_lhs zl zr = corr.crossing_lhs (1 - zl) (1 - zr) := by
  have hB1 : ∀ xr : ℝ, xr ∈ Ioo (0 : ℝ) 1 → ∀ z ∈ CutPlane,
      corr.crossing_lhs z (xr : ℂ) = corr.crossing_lhs (1 - z) (1 - (xr : ℂ)) := by
    intro xr hxr
    have hxrC := ofReal_mem_CutPlane hxr
    refine eqOn_CutPlane_of_differentiableOn_of_eqOn_interval
      (f := fun z => corr.crossing_lhs z (xr : ℂ))
      (g := fun z => corr.crossing_lhs (1 - z) (1 - (xr : ℂ))) ?_ ?_ ?_
    · intro z hz
      exact (corr.differentiableAt_crossing_lhs hν (φ := fun z : ℂ => z)
        (ψ := fun _ : ℂ => (xr : ℂ)) (by fun_prop) (by fun_prop) hz hxrC
        ).differentiableWithinAt
    · intro z hz
      exact (corr.differentiableAt_crossing_lhs hν (φ := fun z : ℂ => 1 - z)
        (ψ := fun _ : ℂ => 1 - (xr : ℂ)) (by fun_prop) (by fun_prop)
        (CutPlane.sub_one hz) (CutPlane.sub_one hxrC)).differentiableWithinAt
    · intro xl hxl
      exact corr.crossing_lhs_real hν hxl hxr
  refine eqOn_CutPlane_of_differentiableOn_of_eqOn_interval
    (f := fun z => corr.crossing_lhs zl z)
    (g := fun z => corr.crossing_lhs (1 - zl) (1 - z)) ?_ ?_ ?_ hzr
  · intro z hz
    exact (corr.differentiableAt_crossing_lhs hν (φ := fun _ : ℂ => zl)
      (ψ := fun z : ℂ => z) (by fun_prop) (by fun_prop) hzl hz).differentiableWithinAt
  · intro z hz
    exact (corr.differentiableAt_crossing_lhs hν (φ := fun _ : ℂ => 1 - zl)
      (ψ := fun z : ℂ => 1 - z) (by fun_prop) (by fun_prop)
      (CutPlane.sub_one hzl) (CutPlane.sub_one hz)).differentiableWithinAt
  · intro xr hxr
    exact hB1 xr hxr zl hzl

/-- Crossing symmetry restricted to real lightcone coordinates $x_l, x_r \in (0, 1)$. -/
theorem crossing_correlator_real (hν : 0 ≤ ν) {xl xr : ℝ}
    (hxl : xl ∈ Ioo (0 : ℝ) 1) (hxr : xr ∈ Ioo (0 : ℝ) 1) :
    corr.crossing_lhs (xl : ℂ) (xr : ℂ) =
      corr.crossing_lhs ((1 - xl : ℝ) : ℂ) ((1 - xr : ℝ) : ℂ) := by
  simpa using corr.crossing_correlator hν (ofReal_mem_CutPlane hxl) (ofReal_mem_CutPlane hxr)

end FourPointData
