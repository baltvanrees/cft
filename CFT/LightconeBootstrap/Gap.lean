/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.MonomialDecomp

/-!
# Twist Gap, $t$-Channel Identity Dominance, and Cross-Channel Error Bounds

This file formalizes the twist gap and $t$-channel identity dominance bounds for the quantitative
monomial lightcone bootstrap:

1. **Inverse Coordinate Map `zOfW` and Crossed Coordinate `crossW`**:
   For $w \in \operatorname{UcDisk}$ with $\operatorname{Im}(w) \in (-\pi, \pi)$ (which includes the
   entire folded Fourier contour $\theta \in [-\pi/2, \pi/2]$), the map
   $$z(w) = \frac{4 e^w}{(1 + e^w)^2}$$
   takes values in `CutPlane` and inverts `logRho`. Under $t$-channel crossing $z \mapsto 1 - z$,
   the crossed universal-cover coordinate is
   $\operatorname{crossW}(w) = \operatorname{logRho}(1 - z(w)) \in \operatorname{UcDisk}$.

2. **Twist Gap (`HasTwistGap`) & Remainder Bound (`norm_eval_sub_one_le`)**:
   In a theory with a twist gap $h_{\text{gap}} > 0$ above the identity $(h, J) = (0, 0)$, the
   non-identity remainder $\mathcal{G}_{\text{mon}}(w_l, w_r) - 1$ decays as
   $e^{h_{\text{gap}} \operatorname{Re}(w_r)}$ as $\operatorname{Re}(w_r) \to -\infty$.

3. **$t$-Channel Identity Dominance (`norm_eval_sub_crossIdentity_le`)**:
   Combining two-variable crossing symmetry (`eval_eq_cross`) with the remainder bound shows that
   as $w_r \to 0$ (so $\operatorname{Re}(\operatorname{crossW}(w_r)) \to -\infty$),
   $\mathcal{G}_{\text{mon}}(w_l, w_r)$ is dominated by the $t$-channel identity contribution
   `crossIdentity Δ_phi wl wr`.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

namespace CFT.LightconeBootstrap

/-!
## Inverse Radial Map `zOfW`, Crossed Coordinate `crossW`, and $t$-Channel Identity
-/

/-- The inverse map from the logarithmic radial coordinate $w \in \operatorname{UcDisk}$ to the
cross-ratio $z \in \text{CutPlane}$:
$$z(w) = \frac{4 e^w}{(1 + e^w)^2}.$$ -/
noncomputable def zOfW (w : ℂ) : ℂ :=
  4 * Complex.exp w / (1 + Complex.exp w) ^ 2

/-- The crossed ($t$-channel) universal-cover coordinate corresponding to $z \mapsto 1 - z$:
$$w^{\text{cross}}(w) = \operatorname{logRho}(1 - z(w)).$$ -/
noncomputable def crossW (w : ℂ) : ℂ :=
  logRho (1 - zOfW w)

/-- Single-variable $t$-channel crossing prefactor analytically continued to
$\operatorname{UcDisk}$:
$$4^{\Delta_\phi} e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi}.$$
Because $\operatorname{Re}(w) < 0 \implies \|e^w\| < 1 \implies \operatorname{Re}(1 - e^w) > 0$,
this is holomorphic on all of $\operatorname{UcDisk}$, and on the fundamental strip
$\operatorname{Im}(w) \in (-\pi, \pi)$ it coincides with
$z(w)^{\Delta_\phi} (1 - z(w))^{-\Delta_\phi}$. -/
noncomputable def crossFactor (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  (4 : ℂ) ^ (Δ_phi : ℂ) * Complex.exp ((Δ_phi : ℂ) * w) *
    (1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ))

/-- The $t$-channel identity contribution in universal-cover coordinates $(w_l, w_r)$:
$$\mathcal{G}_{\text{id}}(w_l, w_r) =
  \operatorname{crossFactor}(\Delta_\phi, w_l) \cdot
  \operatorname{crossFactor}(\Delta_\phi, w_r).$$ -/
noncomputable def crossIdentity (Δ_phi : ℝ) (wl wr : ℂ) : ℂ :=
  crossFactor Δ_phi wl * crossFactor Δ_phi wr

lemma one_add_exp_ne_zero {w : ℂ} (hw : w ∈ UcDisk) : 1 + Complex.exp w ≠ 0 := by
  intro h
  have h_eq : Complex.exp w = -1 := by linear_combination h
  have h_norm : ‖Complex.exp w‖ = 1 := by rw [h_eq, norm_neg, norm_one]
  linarith [exp_norm_lt_one_of_mem_UcDisk hw]

lemma one_sub_zOfW_eq_sq {w : ℂ} (hw : w ∈ UcDisk) :
    1 - zOfW w = ((1 - Complex.exp w) / (1 + Complex.exp w)) ^ 2 := by
  dsimp [zOfW]
  have hne := one_add_exp_ne_zero hw
  field_simp
  ring

lemma re_one_sub_exp_div_one_add_exp_pos {w : ℂ} (hw : w ∈ UcDisk) :
    0 < ((1 - Complex.exp w) / (1 + Complex.exp w)).re := by
  set q := Complex.exp w
  have hq_norm : ‖q‖ < 1 := exp_norm_lt_one_of_mem_UcDisk hw
  have hq_sq : Complex.normSq q < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg q]
  have h_denom : 0 < Complex.normSq (1 + q) :=
    Complex.normSq_pos.mpr (one_add_exp_ne_zero hw)
  have h_re : ((1 - q) / (1 + q)).re = (1 - Complex.normSq q) / Complex.normSq (1 + q) := by
    rw [Complex.div_re]
    dsimp [Complex.normSq]
    ring
  rw [h_re]
  exact div_pos (by linarith) h_denom

/-- On the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$,
`zOfW w` lies in `CutPlane`. -/
theorem zOfW_mem_CutPlane {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    zOfW w ∈ CutPlane := by
  rw [mem_CutPlane_iff]
  by_cases h_im : (zOfW w).im ≠ 0
  · exact Or.inl h_im
  · push Not at h_im
    right
    set q := Complex.exp w
    set u := (1 - q) / (1 + q)
    have hu_re : 0 < u.re := re_one_sub_exp_div_one_add_exp_pos hw
    have hz_eq : zOfW w = 1 - u ^ 2 := by
      linear_combination -(one_sub_zOfW_eq_sq hw)
    have hz_im : (zOfW w).im = - (2 * u.re * u.im) := by
      rw [hz_eq, sq]
      simp [Complex.mul_im]
      ring
    have hu_im : u.im = 0 := by
      have h_prod : 2 * u.re * u.im = 0 := by linarith [h_im, hz_im]
      rcases mul_eq_zero.mp h_prod with h1 | h2
      · linarith [hu_re]
      · exact h2
    have h1q : 1 + q ≠ 0 := one_add_exp_ne_zero hw
    have h1u : 1 + u ≠ 0 := by
      intro h
      have : (1 + u).re = 0 := by rw [h]; rfl
      simp at this
      linarith [hu_re]
    have hq_eq : q = (1 - u) / (1 + u) := by
      dsimp [u]
      field_simp
      ring
    have hu_real : u = (u.re : ℂ) := Complex.ext rfl (by simp [hu_im])
    have hq_real : q = (((1 - u.re) / (1 + u.re) : ℝ) : ℂ) := by
      rw [hq_eq, hu_real]
      push_cast
      rfl
    have hq_im : q.im = 0 := by rw [hq_real, ofReal_im]
    have hw_im : w.im = 0 := by
      have h_sin : Real.exp w.re * Real.sin w.im = 0 := by
        simpa [q, Complex.exp_im] using hq_im
      have h_sin0 : Real.sin w.im = 0 :=
        (mul_eq_zero.mp h_sin).resolve_left (Real.exp_ne_zero w.re)
      exact (Real.sin_eq_zero_iff_of_lt_of_lt him.1 him.2).mp h_sin0
    have hq_re : q.re = Real.exp w.re := by
      simp [q, Complex.exp_re, hw_im]
    have hq_eq_re : q = (Real.exp w.re : ℂ) := by
      apply Complex.ext
      · rw [hq_re, ofReal_re]
      · rw [hq_im, ofReal_im]
    have hu_re_val : u.re = (1 - Real.exp w.re) / (1 + Real.exp w.re) := by
      have : u = (((1 - Real.exp w.re) / (1 + Real.exp w.re) : ℝ) : ℂ) := by
        dsimp [u]
        rw [hq_eq_re]
        norm_cast
      have h_re := congrArg Complex.re this
      rwa [ofReal_re] at h_re
    have hexp_pos : 0 < Real.exp w.re := Real.exp_pos w.re
    have hexp_lt1 : Real.exp w.re < 1 := Real.exp_lt_one_iff.mpr hw
    have hu_lt1 : u.re < 1 := by
      rw [hu_re_val, div_lt_one (by linarith)]
      linarith
    have hz_re : (zOfW w).re = 1 - u.re ^ 2 := by
      rw [hz_eq, sq]
      simp [Complex.mul_re, hu_im, sq]
    rw [hz_re]
    constructor <;> nlinarith [hu_re, hu_lt1]

/-- On the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$,
`rho` is a left inverse to `zOfW` under `Complex.exp`. -/
theorem rho_zOfW {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    rho (zOfW w) = Complex.exp w := by
  have hz : zOfW w ∈ CutPlane := zOfW_mem_CutPlane hw him
  set v := (1 - zOfW w) ^ (1 / 2 : ℂ)
  set u := (1 - Complex.exp w) / (1 + Complex.exp w)
  have hv_re : 0 < v.re := one_sub_cpow_half_re_pos hz
  have hu_re : 0 < u.re := re_one_sub_exp_div_one_add_exp_pos hw
  have hv_sq : v ^ 2 = u ^ 2 := by
    dsimp [v]
    rw [sq, ← cpow_add _ _ (CutPlane.one_sub_ne_zero hz)]
    norm_num
    exact one_sub_zOfW_eq_sq hw
  have h_vu : v = u := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv_sq with h | h
    · exact h
    · have : v.re = - u.re := by rw [h, neg_re]
      linarith [hv_re, hu_re]
  rw [rho_eq_div hz]
  change (1 - v) / (1 + v) = Complex.exp w
  rw [h_vu]
  dsimp [u]
  have h1q : 1 + Complex.exp w ≠ 0 := one_add_exp_ne_zero hw
  field_simp
  ring

/-- On the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$,
`logRho` is a left inverse to `zOfW`. -/
theorem logRho_zOfW {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    logRho (zOfW w) = w := by
  dsimp [logRho]
  rw [rho_zOfW hw him]
  exact Complex.log_exp him.1 him.2.le

lemma one_sub_exp_mem_slitPlane {w : ℂ} (hw : w ∈ UcDisk) :
    1 - Complex.exp w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have hnorm : ‖Complex.exp w‖ < 1 := exp_norm_lt_one_of_mem_UcDisk hw
  have hre : (Complex.exp w).re ≤ ‖Complex.exp w‖ := Complex.re_le_norm (Complex.exp w)
  simp only [sub_re, one_re]
  linarith

lemma differentiableAt_zOfW {w : ℂ} (hw : w ∈ UcDisk) : DifferentiableAt ℂ zOfW w := by
  change DifferentiableAt ℂ (fun w => 4 * Complex.exp w / (1 + Complex.exp w) ^ 2) w
  refine ((differentiableAt_id.cexp.const_mul 4)).div ?_ (pow_ne_zero 2 (one_add_exp_ne_zero hw))
  exact ((differentiableAt_const 1).add differentiableAt_id.cexp).pow 2

lemma crossFactor_eq_zOfW_cpow_ofReal (Δ_phi : ℝ) {x : ℝ} (hx : x < 0) :
    crossFactor Δ_phi (x : ℂ) =
      (zOfW (x : ℂ)) ^ (Δ_phi : ℂ) * (1 - zOfW (x : ℂ)) ^ (- (Δ_phi : ℂ)) := by
  dsimp [crossFactor, zOfW]
  set q : ℝ := Real.exp x
  have hq_pos : 0 < q := Real.exp_pos x
  have hq_lt1 : q < 1 := Real.exp_lt_one_iff.mpr hx
  have h1q_pos : 0 < 1 + q := by linarith
  have h1sub_pos : 0 < 1 - q := by linarith
  set z_re : ℝ := 4 * q / (1 + q) ^ 2
  have hz_pos : 0 < z_re := div_pos (by positivity) (by positivity)
  have h1z_eq : 1 - z_re = ((1 - q) / (1 + q)) ^ 2 := by
    dsimp [z_re]
    field_simp
    ring
  have h1z_pos : 0 < 1 - z_re := by
    rw [h1z_eq]
    positivity
  have h_exp_x : Complex.exp (x : ℂ) = (q : ℂ) := (Complex.ofReal_exp x).symm
  have hz_cast :
      (4 : ℂ) * Complex.exp (x : ℂ) / (1 + Complex.exp (x : ℂ)) ^ 2 = (z_re : ℂ) := by
    rw [h_exp_x]
    dsimp [z_re]
    push_cast
    rfl
  have h1z_cast :
      1 - (4 : ℂ) * Complex.exp (x : ℂ) / (1 + Complex.exp (x : ℂ)) ^ 2 =
        ((1 - z_re : ℝ) : ℂ) := by
    rw [hz_cast]
    push_cast
    rfl
  have h1q_cast : 1 - Complex.exp (x : ℂ) = ((1 - q : ℝ) : ℂ) := by
    rw [h_exp_x]
    push_cast
    rfl
  have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_cpow (by norm_num)]
  have hexp_Δx : Complex.exp ((Δ_phi : ℂ) * (x : ℂ)) = ((q ^ Δ_phi : ℝ) : ℂ) := by
    have : (Δ_phi : ℂ) * (x : ℂ) = ((Δ_phi * x : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_exp, mul_comm Δ_phi x, Real.exp_mul]
  have h1q_cpow :
      (1 - Complex.exp (x : ℂ)) ^ (- (2 * Δ_phi : ℂ)) =
        (((1 - q) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) := by
    rw [h1q_cast]
    have : (- (2 * Δ_phi : ℂ)) = ((- (2 * Δ_phi) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_cpow h1sub_pos.le]
  have hz_cpow :
      ((4 : ℂ) * Complex.exp (x : ℂ) / (1 + Complex.exp (x : ℂ)) ^ 2) ^ (Δ_phi : ℂ) =
        ((z_re ^ Δ_phi : ℝ) : ℂ) := by
    rw [hz_cast, ← Complex.ofReal_cpow hz_pos.le]
  have h1z_cpow :
      (1 - (4 : ℂ) * Complex.exp (x : ℂ) / (1 + Complex.exp (x : ℂ)) ^ 2) ^ (- (Δ_phi : ℂ)) =
        (((1 - z_re) ^ (-Δ_phi) : ℝ) : ℂ) := by
    rw [h1z_cast]
    have : (- (Δ_phi : ℂ)) = ((-Δ_phi : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_cpow h1z_pos.le]
  rw [h4_cast, hexp_Δx, h1q_cpow, hz_cpow, h1z_cpow]
  norm_cast
  have h_z_rpow : z_re ^ Δ_phi = 4 ^ Δ_phi * q ^ Δ_phi / ((1 + q) ^ 2) ^ Δ_phi := by
    dsimp [z_re]
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hq_pos.le]
  have h_1z_rpow :
      (1 - z_re) ^ (-Δ_phi) = (1 - q) ^ (- (2 * Δ_phi)) * ((1 + q) ^ 2) ^ Δ_phi := by
    rw [h1z_eq, div_pow,
      Real.div_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (1 - q) 2, ← Real.rpow_mul h1sub_pos.le,
      div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_neg]
    ring_nf
  rw [h_z_rpow, h_1z_rpow]
  have h_ne : ((1 + q) ^ 2) ^ Δ_phi ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  field_simp

/-- On the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$,
`crossFactor Δ_phi w` coincides with $z(w)^{\Delta_\phi} (1 - z(w))^{-\Delta_\phi}$. -/
theorem crossFactor_eq_zOfW_cpow (Δ_phi : ℝ) {w : ℂ}
    (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    crossFactor Δ_phi w = (zOfW w) ^ (Δ_phi : ℂ) * (1 - zOfW w) ^ (- (Δ_phi : ℂ)) := by
  set S : Set ℂ := { z : ℂ | z.re < 0 ∧ z.im ∈ Ioo (-π) π }
  have hS_open : IsOpen S :=
    (isOpen_Iio.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
  have hS_conv : Convex ℝ S :=
    ((convex_Iio 0).linear_preimage Complex.reLm).inter
      ((convex_Ioo (-π) π).linear_preimage Complex.imLm)
  have hf_diff : DifferentiableOn ℂ (crossFactor Δ_phi) S := by
    intro z hz
    have h_exp : DifferentiableAt ℂ (fun z => Complex.exp ((Δ_phi : ℂ) * z)) z :=
      (differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp
    have h_sub : DifferentiableAt ℂ (fun z => 1 - Complex.exp z) z :=
      (differentiableAt_const 1).sub differentiableAt_id.cexp
    have h_cpow : DifferentiableAt ℂ (fun z => (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ))) z :=
      h_sub.cpow_const (one_sub_exp_mem_slitPlane hz.1)
    exact (((h_exp.const_mul _).mul h_cpow)).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ
      (fun z => (zOfW z) ^ (Δ_phi : ℂ) * (1 - zOfW z) ^ (- (Δ_phi : ℂ))) S := by
    intro z hz
    have hz_cut : zOfW z ∈ CutPlane := zOfW_mem_CutPlane hz.1 hz.2
    have hz_diff : DifferentiableAt ℂ zOfW z := differentiableAt_zOfW hz.1
    have h1 : DifferentiableAt ℂ (fun z => (zOfW z) ^ (Δ_phi : ℂ)) z :=
      hz_diff.cpow_const hz_cut.2
    have h2 : DifferentiableAt ℂ (fun z => (1 - zOfW z) ^ (- (Δ_phi : ℂ))) z :=
      ((differentiableAt_const 1).sub hz_diff).cpow_const hz_cut.1
    exact (h1.mul h2).differentiableWithinAt
  have h_sub : (fun x : ℝ => (x : ℂ)) '' Ioo (-2 : ℝ) (-1) ⊆ S := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨by simpa using hx.2.trans (by norm_num), ?_⟩
    simp [Real.pi_pos, neg_lt_zero.mpr Real.pi_pos]
  have hx₀ : (-3 / 2 : ℝ) ∈ Ioo (-2 : ℝ) (-1) := by constructor <;> norm_num
  have h_eqOn := eqOn_of_differentiableOn_of_eqOn_real_interval
    hS_open hS_conv.isPreconnected hf_diff hg_diff (-2) (-1) (-3 / 2) hx₀ h_sub
    (fun x hx => crossFactor_eq_zOfW_cpow_ofReal Δ_phi (hx.2.trans (by norm_num)))
  exact h_eqOn ⟨hw, him⟩

/-- On the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$,
the crossed coordinate `crossW w` lies in `UcDisk`. -/
theorem crossW_mem_UcDisk {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    crossW w ∈ UcDisk :=
  logRho_mem_UcDisk (CutPlane.sub_one (zOfW_mem_CutPlane hw him))

/-- For any $\zeta \in \operatorname{CutPlane}$, $\|\rho(\zeta)\| \le \|\zeta\|$. -/
lemma norm_rho_le_norm {ζ : ℂ} (hζ : ζ ∈ CutPlane) : ‖rho ζ‖ ≤ ‖ζ‖ := by
  dsimp [rho]
  rw [norm_div, norm_pow]
  have hre : 0 < ((1 - ζ) ^ (1 / 2 : ℂ)).re := one_sub_cpow_half_re_pos hζ
  have h1 : 1 ≤ (1 + (1 - ζ) ^ (1 / 2 : ℂ)).re := by
    simp only [add_re, one_re]
    linarith
  have h_norm : 1 ≤ ‖1 + (1 - ζ) ^ (1 / 2 : ℂ)‖ :=
    h1.trans (Complex.re_le_norm _)
  have h_sq : 1 ≤ ‖1 + (1 - ζ) ^ (1 / 2 : ℂ)‖ ^ 2 := by nlinarith
  exact div_le_self (norm_nonneg ζ) h_sq

/-- On the half-strip
$\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in [-\pi/2, \pi/2]\}$,
$$e^{\operatorname{Re}(\operatorname{crossW}(w))} = \|\rho(1 - z(w))\| \le \|1 - e^w\|^2.$$ -/
theorem exp_re_crossW_le_norm_one_sub_exp_sq {w : ℂ}
    (hw : w ∈ UcDisk) (him : w.im ∈ Icc (-π / 2) (π / 2)) :
    Real.exp (crossW w).re ≤ ‖1 - Complex.exp w‖ ^ 2 := by
  have him_open : w.im ∈ Ioo (-π) π :=
    ⟨by linarith [him.1, Real.pi_pos], by linarith [him.2, Real.pi_pos]⟩
  have h1z : 1 - zOfW w ∈ CutPlane := CutPlane.sub_one (zOfW_mem_CutPlane hw him_open)
  have hexp_eq : Real.exp (crossW w).re = ‖rho (1 - zOfW w)‖ := by
    dsimp [crossW, logRho]
    rw [Complex.log_re, Real.exp_log (norm_pos_iff.mpr (rho_ne_zero h1z))]
  rw [hexp_eq]
  have h1 : ‖rho (1 - zOfW w)‖ ≤ ‖1 - zOfW w‖ := norm_rho_le_norm h1z
  have h_cos : 0 ≤ Real.cos w.im :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [him.1], him.2⟩
  have h_re_one_add : 1 ≤ (1 + Complex.exp w).re := by
    simp only [add_re, one_re, Complex.exp_re]
    exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos w.re).le h_cos)
  have h_norm_one_add : 1 ≤ ‖1 + Complex.exp w‖ :=
    h_re_one_add.trans (Complex.re_le_norm _)
  have h_sq_one_add : 1 ≤ ‖1 + Complex.exp w‖ ^ 2 := by nlinarith
  have h2 : ‖1 - zOfW w‖ ≤ ‖1 - Complex.exp w‖ ^ 2 := by
    rw [one_sub_zOfW_eq_sq hw, norm_pow, norm_div, div_pow]
    exact div_le_self (sq_nonneg _) h_sq_one_add
  exact h1.trans h2

/-- Explicit formula for the $t$-channel radial coordinate $\rho(1 - z(w))$ on the strip
$\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$:
$$\rho(1 - z(w)) = \left(\frac{1 - e^{w/2}}{1 + e^{w/2}}\right)^2.$$ -/
theorem rho_one_sub_zOfW {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Ioo (-π) π) :
    rho (1 - zOfW w) = ((1 - Complex.exp (w / 2)) / (1 + Complex.exp (w / 2))) ^ 2 := by
  have h1z : 1 - zOfW w ∈ CutPlane := CutPlane.sub_one (zOfW_mem_CutPlane hw him)
  set v := (1 - (1 - zOfW w)) ^ (1 / 2 : ℂ)
  set z := Complex.exp (-w / 2) + Complex.exp (w / 2)
  set u := 2 / z
  have hv_re : 0 < v.re := one_sub_cpow_half_re_pos h1z
  have hz_re : 0 < z.re := by
    dsimp [z]
    simp only [Complex.exp_re, div_ofNat_re, neg_re, div_ofNat_im, neg_im]
    have hcos1 : 0 < Real.cos (-w.im / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [him.2], by linarith [him.1]⟩
    have hcos2 : 0 < Real.cos (w.im / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [him.1], by linarith [him.2]⟩
    positivity
  have hz_ne : z ≠ 0 := by
    intro h
    have : z.re = 0 := by rw [h]; rfl
    linarith
  have hu_re : 0 < u.re := by
    dsimp [u]
    rw [Complex.div_re]
    simp only [re_ofNat, im_ofNat, zero_mul]
    have h_nsq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
    positivity
  have h_exp_prod : Complex.exp (w / 2) * z = 1 + Complex.exp w := by
    dsimp [z]
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : w / 2 + -w / 2 = 0 := by ring
    have h2 : w / 2 + w / 2 = w := by ring
    rw [h1, h2, Complex.exp_zero]
  have hu_eq : u = 2 * Complex.exp (w / 2) / (1 + Complex.exp w) := by
    dsimp [u]
    rw [← h_exp_prod]
    have hexp_ne : Complex.exp (w / 2) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hexp_sq : Complex.exp w = Complex.exp (w / 2) ^ 2 := by
    rw [sq, ← Complex.exp_add, add_halves]
  have hv_sq : v ^ 2 = u ^ 2 := by
    have hv2 : v ^ 2 = zOfW w := by
      dsimp [v]
      rw [sq, ← cpow_add _ _ (CutPlane.one_sub_ne_zero h1z)]
      norm_num
    rw [hv2, hu_eq, div_pow, mul_pow, ← hexp_sq]
    dsimp [zOfW]
    ring
  have h_vu : v = u := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv_sq with h | h
    · exact h
    · have : v.re = -u.re := by rw [h, neg_re]
      linarith [hv_re, hu_re]
  rw [rho_eq_div h1z]
  change (1 - v) / (1 + v) = ((1 - Complex.exp (w / 2)) / (1 + Complex.exp (w / 2))) ^ 2
  rw [h_vu, hu_eq]
  have h1q : 1 + Complex.exp w ≠ 0 := one_add_exp_ne_zero hw
  have h_sub : 1 - 2 * Complex.exp (w / 2) / (1 + Complex.exp w) =
      (1 - Complex.exp (w / 2)) ^ 2 / (1 + Complex.exp w) := by
    rw [eq_div_iff h1q, sub_mul, div_mul_cancel₀ _ h1q, hexp_sq]
    ring
  have h_add : 1 + 2 * Complex.exp (w / 2) / (1 + Complex.exp w) =
      (1 + Complex.exp (w / 2)) ^ 2 / (1 + Complex.exp w) := by
    rw [eq_div_iff h1q, add_mul, div_mul_cancel₀ _ h1q, hexp_sq]
    ring
  rw [h_sub, h_add, div_div_div_cancel_right₀ h1q, div_pow]

/-- Uniform upper bound on $\operatorname{Re}(\operatorname{crossW}(w))$ when
$a \le \operatorname{Re}(w) < 0$ and $\operatorname{Im}(w) \in [-\pi/2, \pi/2]$:
$$\operatorname{Re}(\operatorname{crossW}(w)) \le
  \log\left(1 - \frac{\sqrt{2}}{4} e^{a/2}\right) < 0.$$ -/
theorem re_crossW_le_of_re_ge {a : ℝ} {w : ℂ}
    (hw : w ∈ UcDisk) (hwa : a ≤ w.re) (him : w.im ∈ Icc (-π / 2) (π / 2)) :
    (crossW w).re ≤ Real.log (1 - Real.sqrt 2 / 4 * Real.exp (a / 2)) := by
  have him_open : w.im ∈ Ioo (-π) π :=
    ⟨by linarith [him.1, Real.pi_pos], by linarith [him.2, Real.pi_pos]⟩
  have h1z : 1 - zOfW w ∈ CutPlane := CutPlane.sub_one (zOfW_mem_CutPlane hw him_open)
  have hexp_eq : Real.exp (crossW w).re = ‖rho (1 - zOfW w)‖ := by
    dsimp [crossW, logRho]
    rw [Complex.log_re, Real.exp_log (norm_pos_iff.mpr (rho_ne_zero h1z))]
  rw [← Real.exp_le_exp, hexp_eq, rho_one_sub_zOfW hw him_open, norm_pow, norm_div, div_pow]
  set ζ := Complex.exp (w / 2)
  have hζ_norm_lt1 : ‖ζ‖ < 1 := by
    dsimp [ζ]
    rw [Complex.norm_exp, div_ofNat_re]
    exact Real.exp_lt_one_iff.mpr (by linarith [show w.re < 0 from hw])
  have hζ_re : Real.sqrt 2 / 2 * Real.exp (a / 2) ≤ ζ.re := by
    dsimp [ζ]
    rw [Complex.exp_re, div_ofNat_re, div_ofNat_im]
    have hexp_le : Real.exp (a / 2) ≤ Real.exp (w.re / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hcos_le : Real.sqrt 2 / 2 ≤ Real.cos (w.im / 2) := by
      rw [← Real.cos_pi_div_four]
      have h_abs : |w.im / 2| ≤ π / 4 := abs_le.mpr ⟨by linarith [him.1], by linarith [him.2]⟩
      rw [← Real.cos_abs (w.im / 2)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) h_abs
    calc
      Real.sqrt 2 / 2 * Real.exp (a / 2)
        = Real.exp (a / 2) * (Real.sqrt 2 / 2) := mul_comm _ _
      _ ≤ Real.exp (w.re / 2) * Real.cos (w.im / 2) :=
        mul_le_mul hexp_le hcos_le (by positivity) (Real.exp_pos _).le
  have h_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hζ_re
  have h_add_pos : 0 < ‖1 + ζ‖ ^ 2 := by
    have : 1 ≤ (1 + ζ).re := by simp only [add_re, one_re]; linarith
    have : 1 ≤ ‖1 + ζ‖ := this.trans (Complex.re_le_norm _)
    nlinarith
  have h_add_le4 : ‖1 + ζ‖ ^ 2 ≤ 4 := by
    have h_tri : ‖1 + ζ‖ ≤ 2 := by
      calc
        ‖1 + ζ‖ ≤ ‖(1 : ℂ)‖ + ‖ζ‖ := norm_add_le 1 ζ
        _ ≤ 1 + 1 := by simp [hζ_norm_lt1.le]
        _ = 2 := by norm_num
    nlinarith [norm_nonneg (1 + ζ)]
  have h_diff_sq : ‖1 + ζ‖ ^ 2 - ‖1 - ζ‖ ^ 2 = 4 * ζ.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    dsimp [Complex.normSq]
    ring
  have h_ratio : ‖1 - ζ‖ ^ 2 / ‖1 + ζ‖ ^ 2 ≤ 1 - Real.sqrt 2 / 4 * Real.exp (a / 2) := by
    rw [div_le_iff₀ h_add_pos]
    nlinarith
  have h_rhs_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (a / 2) := by
    have hexp_le1 : Real.exp (a / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [show w.re < 0 from hw, hwa])
    have hsqrt2 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.exp_pos (a / 2)]
  rwa [Real.exp_log h_rhs_pos]

/-- Exact modulus of `crossFactor Δ_phi w` for $w \in \operatorname{UcDisk}$:
$$\|\operatorname{crossFactor}(\Delta_\phi, w)\| =
  4^{\Delta_\phi} e^{\Delta_\phi \operatorname{Re}(w)} \|1 - e^w\|^{-2\Delta_\phi}.$$ -/
theorem norm_crossFactor_eq (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    ‖crossFactor Δ_phi w‖ =
      (4 : ℝ) ^ Δ_phi * Real.exp (Δ_phi * w.re) * ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) := by
  dsimp [crossFactor]
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have h4 : ‖(4 : ℂ) ^ (Δ_phi : ℂ)‖ = (4 : ℝ) ^ Δ_phi := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4), ofReal_re]
  have hexp_re : ((Δ_phi : ℂ) * w).re = Δ_phi * w.re := by simp [Complex.mul_re]
  have h1q_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h1q :
      ‖(1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ))‖ = ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) := by
    rw [cpow_def_of_ne_zero h1q_ne, Complex.norm_exp]
    have hre : (Complex.log (1 - Complex.exp w) * -(2 * (Δ_phi : ℂ))).re =
        Real.log ‖1 - Complex.exp w‖ * (-2 * Δ_phi) := by
      simp [Complex.mul_re, Complex.log_re]
    rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr h1q_ne)]
  rw [h4, hexp_re, h1q]

/-- Upper bound on $\|\operatorname{crossFactor}(\Delta_\phi, w)\|$ when
$\operatorname{Re}(w) \le a < 0$:
$$\|\operatorname{crossFactor}(\Delta_\phi, w)\| \le 4^{\Delta_\phi} (1 - e^a)^{-2\Delta_\phi}.$$ -/
theorem norm_crossFactor_le_of_re_le {Δ_phi a : ℝ} (hΔ : 0 < Δ_phi) (ha : a < 0)
    {w : ℂ} (hw : w ∈ UcDisk) (hwa : w.re ≤ a) :
    ‖crossFactor Δ_phi w‖ ≤ (4 : ℝ) ^ Δ_phi * (1 - Real.exp a) ^ (-2 * Δ_phi) := by
  rw [norm_crossFactor_eq Δ_phi hw]
  have hexp_le1 : Real.exp (Δ_phi * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le (hwa.trans ha.le))
  have h1a_pos : 0 < 1 - Real.exp a := sub_pos.mpr (Real.exp_lt_one_iff.mpr ha)
  have h1w_ge : 1 - Real.exp a ≤ ‖1 - Complex.exp w‖ := by
    calc
      1 - Real.exp a ≤ 1 - Real.exp w.re := sub_le_sub_left (Real.exp_le_exp.mpr hwa) 1
      _ = ‖(1 : ℂ)‖ - ‖Complex.exp w‖ := by rw [norm_one, Complex.norm_exp]
      _ ≤ ‖(1 : ℂ) - Complex.exp w‖ := norm_sub_norm_le 1 (Complex.exp w)
  have hrpow_le : ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) ≤ (1 - Real.exp a) ^ (-2 * Δ_phi) :=
    Real.rpow_le_rpow_of_nonpos h1a_pos h1w_ge (by linarith)
  calc
    (4 : ℝ) ^ Δ_phi * Real.exp (Δ_phi * w.re) * ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi)
      ≤ (4 : ℝ) ^ Δ_phi * 1 * (1 - Real.exp a) ^ (-2 * Δ_phi) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
          hrpow_le (by positivity) (by positivity)
    _ = (4 : ℝ) ^ Δ_phi * (1 - Real.exp a) ^ (-2 * Δ_phi) := by ring

/-- Combined bound on the right-moving crossing factor and twist-gap exponential on the half-strip
$\operatorname{Im}(w) \in [-\pi/2, \pi/2]$:
$$\operatorname{norm}(\operatorname{crossFactor}(\Delta_\phi, w)) \,
  e^{h_{\text{gap}} \operatorname{Re}(\operatorname{crossW}(w))}
  \le 4^{\Delta_\phi} \|1 - e^w\|^{2 (h_{\text{gap}} - \Delta_\phi)}.$$ -/
theorem norm_crossFactor_mul_exp_re_crossW_le {Δ_phi h_gap : ℝ}
    (hΔ : 0 < Δ_phi) (hh : 0 < h_gap)
    {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Icc (-π / 2) (π / 2)) :
    ‖crossFactor Δ_phi w‖ * Real.exp (h_gap * (crossW w).re) ≤
      (4 : ℝ) ^ Δ_phi * ‖1 - Complex.exp w‖ ^ (2 * (h_gap - Δ_phi)) := by
  rw [norm_crossFactor_eq Δ_phi hw]
  have h1q_pos : 0 < ‖1 - Complex.exp w‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw))
  have hexp_le1 : Real.exp (Δ_phi * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le (show w.re < 0 from hw).le)
  have hexp_rpow : Real.exp (h_gap * (crossW w).re) ≤ ‖1 - Complex.exp w‖ ^ (2 * h_gap) := by
    have h_eq : Real.exp (h_gap * (crossW w).re) = (Real.exp (crossW w).re) ^ h_gap := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
    have h_sq : (‖1 - Complex.exp w‖ ^ 2) ^ h_gap = ‖1 - Complex.exp w‖ ^ (2 * h_gap) := by
      rw [← Real.rpow_natCast ‖1 - Complex.exp w‖ 2, ← Real.rpow_mul h1q_pos.le]
      norm_num
    rw [h_eq, ← h_sq]
    exact Real.rpow_le_rpow (Real.exp_pos _).le
      (exp_re_crossW_le_norm_one_sub_exp_sq hw him) hh.le
  calc
    (4 : ℝ) ^ Δ_phi * Real.exp (Δ_phi * w.re) * ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) *
        Real.exp (h_gap * (crossW w).re)
      ≤ (4 : ℝ) ^ Δ_phi * 1 * ‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) *
          ‖1 - Complex.exp w‖ ^ (2 * h_gap) := by
        refine mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_le1 (by positivity)) (by positivity))
          hexp_rpow (Real.exp_pos _).le (by positivity)
    _ = (4 : ℝ) ^ Δ_phi * (‖1 - Complex.exp w‖ ^ (-2 * Δ_phi) *
          ‖1 - Complex.exp w‖ ^ (2 * h_gap)) := by ring
    _ = (4 : ℝ) ^ Δ_phi * ‖1 - Complex.exp w‖ ^ (2 * (h_gap - Δ_phi)) := by
      rw [← Real.rpow_add h1q_pos]
      ring_nf

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-!
## Twist Gap Condition and Remainder Bounds
-/

/-- A monomial decomposition `M : MonomialFourPointData` has lower twist $h_{\text{gap}} > 0$ if
for every spin $J \in \mathbb{Z}$, almost all states have $h \ge h_{\text{gap}}$ and
$\bar{h} = h + J \ge h_{\text{gap}}$. -/
structure HasLowerTwist (h_gap : ℝ) : Prop where
  /-- Positivity of the lower twist bound $h_{\text{gap}} > 0$. -/
  h_gap_pos : 0 < h_gap
  /-- For every spin $J \in \mathbb{Z}$, states with $h < h_{\text{gap}}$ or
  $h + J < h_{\text{gap}}$ have measure zero. -/
  support_gap : ∀ J : ℤ, M.mu J { h : ℝ | h < h_gap ∨ h + (J : ℝ) < h_gap } = 0

/-- Monotonicity of `HasLowerTwist`: any smaller positive bound $0 < h' \le h_{\text{gap}}$ is also
a valid lower twist bound. -/
theorem HasLowerTwist.mono {M : MonomialFourPointData} {h_gap h' : ℝ}
    (hlow : M.HasLowerTwist h_gap) (hh'_pos : 0 < h') (hh' : h' ≤ h_gap) :
    M.HasLowerTwist h' := by
  refine ⟨hh'_pos, fun J => measure_mono_null (fun h hh => ?_) (hlow.support_gap J)⟩
  rcases hh with hh | hh
  · exact Or.inl (hh.trans_le hh')
  · exact Or.inr (hh.trans_le hh')

/-- Spin-by-spin exponential decay for a monomial decomposition with lower twist
$h_{\text{gap}} > 0$: for $\sigma_l < 0$ and $\sigma_r \le \sigma_{r, 0} < 0$,
$$\operatorname{evalSpinReal}_J(\sigma_l, \sigma_r) \le
  e^{h_{\text{gap}} (\sigma_r - \sigma_{r, 0})}
  \operatorname{evalSpinReal}_J(\sigma_l, \sigma_{r, 0}).$$ -/
theorem evalSpinReal_le_of_hasLowerTwist {h_gap : ℝ} (hlow : M.HasLowerTwist h_gap)
    {σl σr σr0 : ℝ} (hσl : σl < 0) (hσr : σr < 0) (hσr0 : σr0 < 0) (hσr_le : σr ≤ σr0)
    (J : ℤ) :
    M.evalSpinReal J σl σr ≤
      Real.exp (h_gap * (σr - σr0)) * M.evalSpinReal J σl σr0 := by
  dsimp [evalSpinReal]
  rw [← integral_const_mul]
  refine integral_mono_ae (M.integrable_real hσl hσr J)
    ((M.integrable_real hσl hσr0 J).const_mul _) ?_
  have h_ae : ∀ᶠ h : ℝ in ae (M.mu J), h ∉ { h : ℝ | h < h_gap ∨ h + (J : ℝ) < h_gap } :=
    compl_mem_ae_iff.mpr (hlow.support_gap J)
  filter_upwards [h_ae] with h hh
  have hh2 : h_gap ≤ h + (J : ℝ) := not_lt.mp (fun hlt => hh (Or.inr hlt))
  dsimp [monomialTermReal]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h_mul : (h + (J : ℝ)) * (σr - σr0) ≤ h_gap * (σr - σr0) :=
    mul_le_mul_of_nonpos_right hh2 (sub_nonpos.mpr hσr_le)
  linarith

/-- Exponential decay on $\operatorname{UcPdisk}$ as $\operatorname{Re}(w_r) \to -\infty$ for any
monomial decomposition `M` with lower twist $h_{\text{gap}} > 0$. -/
theorem norm_eval_le_of_hasLowerTwist {h_gap : ℝ} (hlow : M.HasLowerTwist h_gap)
    {σr0 : ℝ} (hσr0 : σr0 < 0) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (hwr_le : wr.re ≤ σr0) :
    ‖M.eval wl wr‖ ≤
      Real.exp (h_gap * (wr.re - σr0)) * M.evalReal wl.re σr0 := by
  calc
    ‖M.eval wl wr‖
      ≤ M.evalReal wl.re wr.re := M.norm_eval_le_evalReal hwl hwr
    _ = ∑' J : ℤ, M.evalSpinReal J wl.re wr.re := rfl
    _ ≤ ∑' J : ℤ, Real.exp (h_gap * (wr.re - σr0)) * M.evalSpinReal J wl.re σr0 :=
      (M.summable_real hwl hwr).tsum_le_tsum
        (fun J => M.evalSpinReal_le_of_hasLowerTwist hlow hwl hwr hσr0 hwr_le J)
        ((M.summable_real hwl hσr0).mul_left _)
    _ = Real.exp (h_gap * (wr.re - σr0)) * M.evalReal wl.re σr0 := by
      rw [tsum_mul_left]; rfl

/-- A monomial four-point decomposition `M` has a **twist gap** $h_{\text{gap}} > 0$ above the
identity operator `1` if `M` decomposes as `1` plus a non-identity remainder
`rem : MonomialFourPointData` satisfying `rem.HasLowerTwist h_gap`. -/
def HasTwistGap (h_gap : ℝ) : Prop :=
  ∃ rem : MonomialFourPointData,
    rem.HasLowerTwist h_gap ∧
    (∀ wl wr : ℂ, M.eval wl wr = 1 + rem.eval wl wr) ∧
    (∀ σl σr : ℝ, M.evalReal σl σr = 1 + rem.evalReal σl σr)

/-- Monotonicity of `HasTwistGap`: any smaller positive gap $0 < h' \le h_{\text{gap}}$ is also a
valid twist gap. -/
theorem HasTwistGap.mono {M : MonomialFourPointData} {h_gap h' : ℝ}
    (hgap : M.HasTwistGap h_gap) (hh'_pos : 0 < h') (hh' : h' ≤ h_gap) :
    M.HasTwistGap h' := by
  rcases hgap with ⟨rem, hlow, heval, hevalReal⟩
  exact ⟨rem, hlow.mono hh'_pos hh', heval, hevalReal⟩

/-- Non-negativity of $\mathcal{G}_{\text{mon}}(\sigma_l, \sigma_r) - 1$ when `M` has a
twist gap. -/
theorem evalReal_sub_one_nonneg {h_gap : ℝ} (hgap : M.HasTwistGap h_gap) (σl σr : ℝ) :
    0 ≤ M.evalReal σl σr - 1 := by
  rcases hgap with ⟨rem, _, _, hevalReal⟩
  have h_eq : M.evalReal σl σr - 1 = rem.evalReal σl σr := by rw [hevalReal]; ring
  rw [h_eq]
  exact rem.evalReal_nonneg σl σr

/-- Exponential suppression of the non-identity remainder $\mathcal{G}_{\text{mon}}(w_l, w_r) - 1$
as $\operatorname{Re}(w_r) \to -\infty$ in a theory with a twist gap $h_{\text{gap}} > 0$:
for any reference point $\sigma_{r, 0} < 0$ and $(w_l, w_r) \in \operatorname{UcPdisk}$ with
$\operatorname{Re}(w_r) \le \sigma_{r, 0}$,
$$\|\mathcal{G}_{\text{mon}}(w_l, w_r) - 1\| \le
  e^{h_{\text{gap}} (\operatorname{Re}(w_r) - \sigma_{r, 0})} \,
  \bigl(\mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l), \sigma_{r, 0}) - 1\bigr).$$ -/
theorem norm_eval_sub_one_le {h_gap : ℝ} (hgap : M.HasTwistGap h_gap)
    {σr0 : ℝ} (hσr0 : σr0 < 0) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (hwr_le : wr.re ≤ σr0) :
    ‖M.eval wl wr - 1‖ ≤
      Real.exp (h_gap * (wr.re - σr0)) * (M.evalReal wl.re σr0 - 1) := by
  rcases hgap with ⟨rem, hlow, heval, hevalReal⟩
  have h1 : M.eval wl wr - 1 = rem.eval wl wr := by rw [heval]; ring
  have h2 : M.evalReal wl.re σr0 - 1 = rem.evalReal wl.re σr0 := by rw [hevalReal]; ring
  rw [h1, h2]
  exact rem.norm_eval_le_of_hasLowerTwist hlow hσr0 hwl hwr hwr_le

/-- Two-variable $t$-channel crossing symmetry expressed in universal-cover coordinates
$(w_l, w_r)$ on the fundamental strip
$\operatorname{Im}(w_l), \operatorname{Im}(w_r) \in (-\pi, \pi)$, for any
`M : MonomialFourPointData` agreeing with `corr.correlator_pdisk`. -/
theorem eval_eq_cross {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk)
    (hwl_im : wl.im ∈ Ioo (-π) π) (hwr_im : wr.im ∈ Ioo (-π) π) :
    M.eval wl wr =
      crossIdentity Δ_phi wl wr * M.eval (crossW wl) (crossW wr) := by
  have hzl : zOfW wl ∈ CutPlane := zOfW_mem_CutPlane hwl hwl_im
  have hzr : zOfW wr ∈ CutPlane := zOfW_mem_CutPlane hwr hwr_im
  have hcross := corr.crossing_correlator hν hzl hzr
  dsimp [FourPointData.crossing_lhs, FourPointData.correlator] at hcross
  rw [logRho_zOfW hwl hwl_im, logRho_zOfW hwr hwr_im,
    ← crossW, ← crossW, ← hM hwl hwr,
    ← hM (crossW_mem_UcDisk hwl hwl_im) (crossW_mem_UcDisk hwr hwr_im)] at hcross
  have hzl_pow : (zOfW wl) ^ (Δ_phi : ℂ) * (zOfW wl) ^ (- (Δ_phi : ℂ)) = 1 := by
    rw [← cpow_add _ _ (CutPlane.ne_zero hzl), add_neg_cancel, cpow_zero]
  have hzr_pow : (zOfW wr) ^ (Δ_phi : ℂ) * (zOfW wr) ^ (- (Δ_phi : ℂ)) = 1 := by
    rw [← cpow_add _ _ (CutPlane.ne_zero hzr), add_neg_cancel, cpow_zero]
  calc
    M.eval wl wr
      = ((zOfW wl) ^ (Δ_phi : ℂ) * (zOfW wl) ^ (- (Δ_phi : ℂ))) *
        ((zOfW wr) ^ (Δ_phi : ℂ) * (zOfW wr) ^ (- (Δ_phi : ℂ))) * M.eval wl wr := by
          rw [hzl_pow, hzr_pow, mul_one, one_mul]
    _ = (zOfW wl) ^ (Δ_phi : ℂ) * (zOfW wr) ^ (Δ_phi : ℂ) *
        ((zOfW wl) ^ (- (Δ_phi : ℂ)) * (zOfW wr) ^ (- (Δ_phi : ℂ)) * M.eval wl wr) := by ring
    _ = (zOfW wl) ^ (Δ_phi : ℂ) * (zOfW wr) ^ (Δ_phi : ℂ) *
        ((1 - zOfW wl) ^ (- (Δ_phi : ℂ)) * (1 - zOfW wr) ^ (- (Δ_phi : ℂ)) *
          M.eval (crossW wl) (crossW wr)) := by rw [hcross]
    _ = crossIdentity Δ_phi wl wr * M.eval (crossW wl) (crossW wr) := by
      dsimp [crossIdentity]
      rw [crossFactor_eq_zOfW_cpow Δ_phi hwl hwl_im, crossFactor_eq_zOfW_cpow Δ_phi hwr hwr_im]
      ring

/-- **$t$-Channel Identity Dominance Bound**: in a theory with twist gap $h_{\text{gap}} > 0$ and
crossing symmetry for external dimension $\Delta_\phi$, whenever
$\operatorname{Re}(\operatorname{crossW}(w_r)) \le \sigma_{r, 0} < 0$, the difference between the
full correlator and the $t$-channel identity contribution is bounded by:
$$\|\mathcal{G}_{\text{mon}}(w_l, w_r) - \mathcal{G}_{\text{id}}(w_l, w_r)\| \le
  \|\mathcal{G}_{\text{id}}(w_l, w_r)\| \,
  e^{h_{\text{gap}} (\operatorname{Re}(w_r^{\text{cross}}) - \sigma_{r, 0})} \,
  \bigl(\mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l^{\text{cross}}),
  \sigma_{r, 0}) - 1\bigr).$$ -/
theorem norm_eval_sub_crossIdentity_le {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σr0 : ℝ} (hσr0 : σr0 < 0)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk)
    (hwl_im : wl.im ∈ Ioo (-π) π) (hwr_im : wr.im ∈ Ioo (-π) π)
    (hwr_cross_le : (crossW wr).re ≤ σr0) :
    ‖M.eval wl wr - crossIdentity Δ_phi wl wr‖ ≤
      ‖crossIdentity Δ_phi wl wr‖ *
        (Real.exp (h_gap * ((crossW wr).re - σr0)) *
          (M.evalReal (crossW wl).re σr0 - 1)) := by
  have h_cross := M.eval_eq_cross corr hν hM hwl hwr hwl_im hwr_im
  have h_sub : M.eval wl wr - crossIdentity Δ_phi wl wr =
      crossIdentity Δ_phi wl wr * (M.eval (crossW wl) (crossW wr) - 1) := by
    rw [h_cross]; ring
  rw [h_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (M.norm_eval_sub_one_le hgap hσr0 (crossW_mem_UcDisk hwl hwl_im)
      (crossW_mem_UcDisk hwr hwr_im) hwr_cross_le)
    (norm_nonneg _)

/-- Two-variable version of `norm_eval_sub_crossIdentity_le`: when both
$\operatorname{Re}(\operatorname{crossW}(w_l)) \le \sigma_{l, 0} < 0$ and
$\operatorname{Re}(\operatorname{crossW}(w_r)) \le \sigma_{r, 0} < 0$, the remainder is bounded by
the constant $\mathcal{G}_{\text{mon}}(\sigma_{l, 0}, \sigma_{r, 0}) - 1$. -/
theorem norm_eval_sub_crossIdentity_le_of_re_le {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σl0 σr0 : ℝ} (hσl0 : σl0 < 0) (hσr0 : σr0 < 0)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk)
    (hwl_im : wl.im ∈ Ioo (-π) π) (hwr_im : wr.im ∈ Ioo (-π) π)
    (hwl_cross_le : (crossW wl).re ≤ σl0) (hwr_cross_le : (crossW wr).re ≤ σr0) :
    ‖M.eval wl wr - crossIdentity Δ_phi wl wr‖ ≤
      ‖crossIdentity Δ_phi wl wr‖ *
        (Real.exp (h_gap * ((crossW wr).re - σr0)) *
          (M.evalReal σl0 σr0 - 1)) := by
  have h1 :=
    M.norm_eval_sub_crossIdentity_le corr hν hM hgap hσr0 hwl hwr hwl_im hwr_im hwr_cross_le
  have h_mono : M.evalReal (crossW wl).re σr0 - 1 ≤ M.evalReal σl0 σr0 - 1 :=
    sub_le_sub_right
      (M.evalReal_mono_left (crossW_mem_UcDisk hwl hwl_im) hσl0 hσr0 hwl_cross_le) 1
  exact h1.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h_mono (Real.exp_pos _).le) (norm_nonneg _))

end MonomialFourPointData

end CFT.LightconeBootstrap
