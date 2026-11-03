/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.QuantitativeLargeSpin
import CFT.LightconeBootstrap.TransmutedEndpointBounds

/-!
# Exact Transmuted $t$-Channel Identity Reference ($S_0$ and $M^0_{2k}$)

This file develops the exact 3-term transmuted $t$-channel identity reference and its spin-$2k$
Fourier-Laplace projection and Tauberian pairing:

1. **Pochhammer Identities & Exact Transmuted Coefficient (`exactTransmutedPochhammer`)**:
   We define the 3-term linear combination of shifted Pochhammer coefficients
   $$\operatorname{exactTransmutedPochhammer}(\Delta_\phi, m) :=
     \frac{(2\Delta_\phi + 1)_m}{m!} - \frac{(2\Delta_\phi)_m}{m!}
       + \frac{\Delta_\phi - 1/2}{4\Delta_\phi} \frac{(2\Delta_\phi - 1)_m}{m!}$$
   arising from termwise transmutation of the 1D GFF collinear block expansion of
   $\operatorname{crossFactor}(\Delta_\phi, w_r)$.
   We prove the exact single-term factorization for $m = k + 1 \ge 1$
   (`exactTransmutedPochhammer_succ`):
   $$\operatorname{exactTransmutedPochhammer}(\Delta_\phi, k + 1) =
     \frac{(\Delta_\phi + k + 1/2)^2}{2\Delta_\phi (k + 1)} \frac{(2\Delta_\phi)_k}{k!},$$
   which is manifestly strictly positive for all $\Delta_\phi > 0$ and $m \ge 1$
   (`exactTransmutedPochhammer_pos`, `exactTransmutedPochhammer_nonneg`).

2. **Closed-Form Generating Function `crossFactorExactTransmuted` on `UcDisk`**:
   We define the exact transmuted right-moving $t$-channel identity factor
   $$\operatorname{crossFactorExactTransmuted}(\Delta_\phi, w) :=
     \operatorname{crossFactorTransmuted}(\Delta_\phi, w)
       \left[1 - (1 - e^w) + \frac{\Delta_\phi - 1/2}{4\Delta_\phi}(1 - e^w)^2\right]$$
   and prove its series expansion (`hasSum_crossFactorExactTransmuted`) on $\operatorname{UcDisk}$.

3. **Exact Finite-Spin Reference Laplace Transform & Pairing
   (`exactTransmutedIdentityLaplaceReal`, `exactTransmutedIdentityPairing`)**:
   We define the exact finite-spin reference Laplace transform and test-function pairing using
   `exactTransmutedPochhammer Δ_phi (n + K)` and prove that at spin $K = 2k$, their rescaled
   difference from `transmutedIdentityPairing` and `transmutedUniversalPairing` is $O((2k)^{-1})$
   (`exists_const_abs_exactTransmutedIdentityPairing_sub_transmutedIdentityPairing_le`,
   `exists_const_abs_exactTransmutedIdentityPairing_sub_universal_le`).
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Pochhammer Identities & `exactTransmutedPochhammer` -/

lemma pochhammerCoeff_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < pochhammerCoeff a n := by
  dsimp [pochhammerCoeff]
  exact div_pos (realPochhammer_pos ha n) (Nat.cast_pos.mpr (Nat.factorial_pos n))

/-- Shifting the parameter $x \mapsto x + 1$ in `pochhammerCoeff`:
$x \, \frac{(x + 1)_m}{m!} = (x + m) \, \frac{(x)_m}{m!}$. -/
lemma mul_pochhammerCoeff_add_one (x : ℝ) (m : ℕ) :
    x * pochhammerCoeff (x + 1) m = (x + (m : ℝ)) * pochhammerCoeff x m := by
  dsimp [pochhammerCoeff]
  have h1 := realPochhammer_succ_left x m
  have h2 := realPochhammer_succ x m
  have h_eq : x * realPochhammer (x + 1) m = (x + (m : ℝ)) * realPochhammer x m := by
    linarith
  calc
    x * (realPochhammer (x + 1) m / (m.factorial : ℝ))
      = (x * realPochhammer (x + 1) m) / (m.factorial : ℝ) := by ring
    _ = ((x + (m : ℝ)) * realPochhammer x m) / (m.factorial : ℝ) := by rw [h_eq]
    _ = (x + (m : ℝ)) * (realPochhammer x m / (m.factorial : ℝ)) := by ring

/-- Shifting both parameter and index in `pochhammerCoeff`:
$(k + 1) \, \frac{(x)_{k + 1}}{(k + 1)!} = x \, \frac{(x + 1)_k}{k!}$. -/
lemma pochhammerCoeff_succ_eq (x : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * pochhammerCoeff x (k + 1) = x * pochhammerCoeff (x + 1) k := by
  dsimp [pochhammerCoeff]
  rw [realPochhammer_succ_left x k, Nat.factorial_succ]
  push_cast
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hfact : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The exact 3-term transmuted Pochhammer combination:
$$\operatorname{exactTransmutedPochhammer}(\Delta_\phi, m) :=
  \frac{(2\Delta_\phi + 1)_m}{m!} - \frac{(2\Delta_\phi)_m}{m!}
    + \frac{\Delta_\phi - 1/2}{4\Delta_\phi} \frac{(2\Delta_\phi - 1)_m}{m!}.$$ -/
noncomputable def exactTransmutedPochhammer (Δ_phi : ℝ) (m : ℕ) : ℝ :=
  pochhammerCoeff (2 * Δ_phi + 1) m - pochhammerCoeff (2 * Δ_phi) m +
    ((Δ_phi - 1 / 2) / (4 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi - 1) m

@[simp]
lemma exactTransmutedPochhammer_zero (Δ_phi : ℝ) :
    exactTransmutedPochhammer Δ_phi 0 = (Δ_phi - 1 / 2) / (4 * Δ_phi) := by
  simp [exactTransmutedPochhammer]

/-- **Single-Term Factorization of `exactTransmutedPochhammer` for $m = k + 1 \ge 1$**:
For all $\Delta_\phi \ne 0$ and $k \in \mathbb{N}$,
$$\operatorname{exactTransmutedPochhammer}(\Delta_\phi, k + 1) =
  \frac{(\Delta_\phi + k + 1/2)^2}{2\Delta_\phi (k + 1)} \frac{(2\Delta_\phi)_k}{k!}.$$ -/
theorem exactTransmutedPochhammer_succ {Δ_phi : ℝ} (hΔ : Δ_phi ≠ 0) (k : ℕ) :
    exactTransmutedPochhammer Δ_phi (k + 1) =
      (Δ_phi + (k : ℝ) + 1 / 2) ^ 2 / (2 * Δ_phi * ((k + 1 : ℕ) : ℝ)) *
        pochhammerCoeff (2 * Δ_phi) k := by
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := hk1_pos.ne'
  have h4Δ_ne : 4 * Δ_phi * ((k + 1 : ℕ) : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hΔ) hk1_ne
  have h2Δ_ne : 2 * Δ_phi * ((k + 1 : ℕ) : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hΔ) hk1_ne
  have h_term3 :
      ((k + 1 : ℕ) : ℝ) * pochhammerCoeff (2 * Δ_phi - 1) (k + 1) =
        (2 * Δ_phi - 1) * pochhammerCoeff (2 * Δ_phi) k := by
    have h := pochhammerCoeff_succ_eq (2 * Δ_phi - 1) k
    have h_add : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
    rwa [h_add] at h
  have h_term2 :
      ((k + 1 : ℕ) : ℝ) * pochhammerCoeff (2 * Δ_phi) (k + 1) =
        (2 * Δ_phi + (k : ℝ)) * pochhammerCoeff (2 * Δ_phi) k := by
    rw [pochhammerCoeff_succ_eq (2 * Δ_phi) k, mul_pochhammerCoeff_add_one (2 * Δ_phi) k]
  have h_term1 :
      2 * Δ_phi * (((k + 1 : ℕ) : ℝ) * pochhammerCoeff (2 * Δ_phi + 1) (k + 1)) =
        (2 * Δ_phi + 1 + (k : ℝ)) * (2 * Δ_phi + (k : ℝ)) * pochhammerCoeff (2 * Δ_phi) k := by
    have h_step1 :
        ((k + 1 : ℕ) : ℝ) * pochhammerCoeff (2 * Δ_phi + 1) (k + 1) =
          (2 * Δ_phi + 1 + (k : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) k := by
      rw [pochhammerCoeff_succ_eq (2 * Δ_phi + 1) k,
        mul_pochhammerCoeff_add_one (2 * Δ_phi + 1) k]
    rw [h_step1]
    linear_combination (2 * Δ_phi + 1 + (k : ℝ)) * mul_pochhammerCoeff_add_one (2 * Δ_phi) k
  apply mul_left_cancel₀ h4Δ_ne
  unfold exactTransmutedPochhammer
  have h_div1 :
      4 * Δ_phi * ((k + 1 : ℕ) : ℝ) * ((Δ_phi - 1 / 2) / (4 * Δ_phi)) =
        (Δ_phi - 1 / 2) * ((k + 1 : ℕ) : ℝ) := by
    have h4 : 4 * Δ_phi ≠ 0 := mul_ne_zero (by norm_num) hΔ
    field_simp
  have h_div2 :
      4 * Δ_phi * ((k + 1 : ℕ) : ℝ) *
          ((Δ_phi + (k : ℝ) + 1 / 2) ^ 2 / (2 * Δ_phi * ((k + 1 : ℕ) : ℝ))) =
        2 * (Δ_phi + (k : ℝ) + 1 / 2) ^ 2 := by
    field_simp
    ring
  push_cast at h_term1 h_term2 h_term3 h_div1 h_div2 ⊢
  linear_combination
    2 * h_term1 - 4 * Δ_phi * h_term2 + (Δ_phi - 1 / 2) * h_term3 +
      pochhammerCoeff (2 * Δ_phi - 1) (k + 1) * h_div1 -
      pochhammerCoeff (2 * Δ_phi) k * h_div2

/-- Strict positivity of `exactTransmutedPochhammer Δ_phi m` for all $\Delta_\phi > 0$ and
$m \ge 1$. -/
theorem exactTransmutedPochhammer_pos {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {m : ℕ} (hm : 1 ≤ m) :
    0 < exactTransmutedPochhammer Δ_phi m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [exactTransmutedPochhammer_succ hΔ.ne' k]
  have h1 : 0 < Δ_phi + (k : ℝ) + 1 / 2 := by positivity
  have h2 : 0 < 2 * Δ_phi * ((k + 1 : ℕ) : ℝ) := by positivity
  have h3 : 0 < pochhammerCoeff (2 * Δ_phi) k := pochhammerCoeff_pos (by positivity) k
  positivity

lemma exactTransmutedPochhammer_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ exactTransmutedPochhammer Δ_phi m :=
  (exactTransmutedPochhammer_pos hΔ hm).le

/-- Exact representation of the subleading difference
`pochhammerCoeff (2 * Δ_phi + 1) m - exactTransmutedPochhammer Δ_phi m` in terms of
`pochhammerCoeff (2 * Δ_phi) m` for $m \ge 1$. -/
lemma pochhammerCoeff_sub_exactTransmutedPochhammer_eq {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {m : ℕ} (hm : 1 ≤ m) :
    pochhammerCoeff (2 * Δ_phi + 1) m - exactTransmutedPochhammer Δ_phi m =
      (1 - (Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ)))) *
        pochhammerCoeff (2 * Δ_phi) m := by
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h_denom_pos : 0 < 2 * Δ_phi - 1 + (m : ℝ) := by linarith
  have h_shift := mul_pochhammerCoeff_add_one (2 * Δ_phi - 1) m
  have h_add : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
  rw [h_add] at h_shift
  have h_p_minus :
      pochhammerCoeff (2 * Δ_phi - 1) m =
        (2 * Δ_phi - 1) / (2 * Δ_phi - 1 + (m : ℝ)) * pochhammerCoeff (2 * Δ_phi) m := by
    rw [div_mul_eq_mul_div, eq_div_iff h_denom_pos.ne']
    linarith [h_shift]
  unfold exactTransmutedPochhammer
  rw [h_p_minus]
  have hΔ_ne : Δ_phi ≠ 0 := hΔ.ne'
  have h_denom_ne : 2 * Δ_phi - 1 + (m : ℝ) ≠ 0 := h_denom_pos.ne'
  field_simp
  ring

/-- Upper bound on `|exactTransmutedPochhammer Δ_phi m - pochhammerCoeff (2 * Δ_phi + 1) m|` in
terms of `pochhammerCoeff (2 * Δ_phi) m` for $m \ge 1$. -/
lemma abs_exactTransmutedPochhammer_sub_pochhammerCoeff_le {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {m : ℕ} (hm : 1 ≤ m) :
    |exactTransmutedPochhammer Δ_phi m - pochhammerCoeff (2 * Δ_phi + 1) m| ≤
      (1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2)) * pochhammerCoeff (2 * Δ_phi) m := by
  rw [abs_sub_comm, pochhammerCoeff_sub_exactTransmutedPochhammer_eq hΔ hm, abs_mul,
    abs_of_nonneg (pochhammerCoeff_nonneg (by positivity) m)]
  refine mul_le_mul_of_nonneg_right ?_ (pochhammerCoeff_nonneg (by positivity) m)
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h_denom_ge : 2 * Δ_phi ≤ 2 * Δ_phi - 1 + (m : ℝ) := by linarith
  have h_prod_ge : 4 * Δ_phi ^ 2 ≤ 2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ)) := by
    nlinarith
  have h_ratio_le :
      (Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ))) ≤
        (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h_prod_ge
  have h_ratio_nonneg :
      0 ≤ (Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ))) := by
    have : 0 < 2 * Δ_phi - 1 + (m : ℝ) := by linarith
    positivity
  calc
    |1 - (Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ)))|
      ≤ |1| + |(Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ)))| :=
        abs_sub _ _
    _ = 1 + (Δ_phi - 1 / 2) ^ 2 / (2 * Δ_phi * (2 * Δ_phi - 1 + (m : ℝ))) := by
        rw [abs_one, abs_of_nonneg h_ratio_nonneg]
    _ ≤ 1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2) := by linarith

/-! ## Section 2: Closed-Form Generating Function `crossFactorExactTransmuted` on `UcDisk` -/

/-- The 3-term polynomial factor in $(1 - e^w)$ converting `crossFactorTransmuted` into the exact
transmuted $t$-channel identity reference $S_0(w)$:
$$P_{\text{exact}}(\Delta_\phi, w) :=
  1 - (1 - e^w) + \frac{\Delta_\phi - 1/2}{4\Delta_\phi} (1 - e^w)^2.$$ -/
noncomputable def exactTransmutedPolyFactor (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  1 - (1 - Complex.exp w) + (((Δ_phi - 1 / 2) / (4 * Δ_phi) : ℝ) : ℂ) * (1 - Complex.exp w) ^ 2

/-- The exact transmuted right-moving $t$-channel identity factor $S_0(w)$ on
$\operatorname{UcDisk}$:
$$S_0(\Delta_\phi, w) :=
  \operatorname{crossFactorTransmuted}(\Delta_\phi, w) \cdot
    \operatorname{exactTransmutedPolyFactor}(\Delta_\phi, w).$$ -/
noncomputable def crossFactorExactTransmuted (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  crossFactorTransmuted Δ_phi w * exactTransmutedPolyFactor Δ_phi w

/-- The two-variable exact transmuted $t$-channel identity reference on $\operatorname{UcPdisk}$:
$$\operatorname{crossIdentityExactTransmuted}(\Delta_\phi, w_l, w_r) :=
  \operatorname{crossFactor}(\Delta_\phi, w_l) \cdot
    \operatorname{crossFactorExactTransmuted}(\Delta_\phi, w_r).$$ -/
noncomputable def crossIdentityExactTransmuted (Δ_phi : ℝ) (wl wr : ℂ) : ℂ :=
  crossFactor Δ_phi wl * crossFactorExactTransmuted Δ_phi wr

lemma hasSum_pochhammerCoeff_mul_exp (a Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun m : ℕ =>
        (pochhammerCoeff a m : ℂ) * Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * w))
      (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- (a : ℂ))) := by
  have h_bin :=
    (hasSum_one_sub_cpow_neg a (exp_norm_lt_one_of_mem_UcDisk hw)).mul_left
      (Complex.exp ((Δ_phi : ℂ) * w))
  refine h_bin.congr_fun fun m => ?_
  rw [← Complex.exp_nat_mul]
  have hexp :
      Complex.exp ((Δ_phi : ℂ) * w) * Complex.exp ((m : ℂ) * w) =
        Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * w) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (pochhammerCoeff a m : ℂ) * hexp.symm

/-- **Exact Series Expansion of `crossFactorExactTransmuted` on `UcDisk`**:
For all $\Delta_\phi \in \mathbb{R}$ and $w \in \operatorname{UcDisk}$,
$$\sum_{m=0}^{\infty} \frac{\Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2} 4^{\Delta_\phi} \,
  \operatorname{exactTransmutedPochhammer}(\Delta_\phi, m) \, e^{(\Delta_\phi + m) w}
  = \operatorname{crossFactorExactTransmuted}(\Delta_\phi, w).$$ -/
lemma hasSum_crossFactorExactTransmuted (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun m : ℕ =>
        (((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
          exactTransmutedPochhammer Δ_phi m : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * w))
      (crossFactorExactTransmuted Δ_phi w) := by
  set pref : ℂ :=
    ((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi : ℝ) : ℂ)
  set c : ℂ := (((Δ_phi - 1 / 2) / (4 * Δ_phi) : ℝ) : ℂ)
  have h1 := hasSum_pochhammerCoeff_mul_exp (2 * Δ_phi + 1) Δ_phi hw
  have h2 := hasSum_pochhammerCoeff_mul_exp (2 * Δ_phi) Δ_phi hw
  have h3 := (hasSum_pochhammerCoeff_mul_exp (2 * Δ_phi - 1) Δ_phi hw).mul_left c
  have h_comb := ((h1.sub h2).add h3).mul_left pref
  have hz_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h_cpow1 :
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) =
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) := by
    calc
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w)
        = (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) *
            (1 - Complex.exp w) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ) + (1 : ℂ)) :=
          (Complex.cpow_add _ _ hz_ne).symm
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) := by
          congr 1; push_cast; ring
  have h_cpow2 :
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) ^ 2 =
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)) := by
    have h_sq : (1 - Complex.exp w) ^ 2 = (1 - Complex.exp w) ^ (2 : ℂ) := by
      norm_cast
    rw [h_sq, ← Complex.cpow_add _ _ hz_ne]
    congr 1
    push_cast
    ring
  have h_sum_eq :
      pref *
        (Complex.exp ((Δ_phi : ℂ) * w) *
            (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) -
          Complex.exp ((Δ_phi : ℂ) * w) *
            (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) +
          c * (Complex.exp ((Δ_phi : ℂ) * w) *
            (1 - Complex.exp w) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)))) =
      crossFactorExactTransmuted Δ_phi w := by
    dsimp [crossFactorExactTransmuted, crossFactorTransmuted, exactTransmutedPolyFactor, pref, c]
    rw [← h_cpow1, ← h_cpow2]
    ring
  rw [h_sum_eq] at h_comb
  refine h_comb.congr_fun fun m => ?_
  dsimp [exactTransmutedPochhammer, pref, c]
  push_cast
  ring

/-! ## Section 3: Exact Finite-Spin Transmuted Reference Laplace Transform & Pairing -/

/-- Exact finite-spin 1-term transmuted $t$-channel identity pairing at spin $K = 2k$:
$$\operatorname{transmutedIdentityPairing}(\Delta_\phi, K, \varphi) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi + 1)_{n + K}}{(n + K)!}
    \varphi(\Delta_\phi + n).$$ -/
noncomputable def transmutedIdentityPairing (Δ_phi : ℝ) (K : ℕ) (φ : ℝ → ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
      φ (Δ_phi + (n : ℝ))

/-- The $k$-independent transmuted universal double-twist pairing for external dimension
$\Delta_\phi$:
$$\operatorname{transmutedUniversalPairing}(\Delta_\phi, \varphi) :=
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}
    \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \varphi(\Delta_\phi + n).$$ -/
noncomputable def transmutedUniversalPairing (Δ_phi : ℝ) (φ : ℝ → ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ))

/-- **Kinematic Large-$k$ Expansion of `transmutedIdentityPairing` to
`transmutedUniversalPairing`**:
For any $\Delta_\phi > 0$ and support bound $N \in \mathbb{N}$, there exists $C_N > 0$ such that
for all $k \ge 1$ and all $\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi(h)| \le M_\varphi$ ($M_\varphi \ge 0$),
$$\left|(2k)^{-2\Delta_\phi} \operatorname{transmutedIdentityPairing}(\Delta_\phi, 2k, \varphi) -
  \operatorname{transmutedUniversalPairing}(\Delta_\phi, \varphi)\right|
  \le C_N \, (2k)^{-1} \, M_\varphi.$$ -/
theorem exists_const_abs_transmutedIdentityPairing_sub_universal_le
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ -
        transmutedUniversalPairing Δ_phi φ| ≤
        C * (2 * (k : ℝ))⁻¹ * M_φ := by
  have ha : 0 < 2 * Δ_phi := by positivity
  have hb : 0 < 2 * Δ_phi + 1 := by positivity
  obtain ⟨C₀, hC₀_pos, hC₀⟩ :=
    exists_const_abs_tsum_pochhammerCoeff_mixed_test_sub_le ha hb Δ_phi N
  set pref : ℝ := universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)
  have hG : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos hb
  have hpref_pos : 0 < pref := mul_pos (universalPrimaryLeadingCoeff_pos hΔ) hG
  refine ⟨pref * C₀, mul_pos hpref_pos hC₀_pos, fun {k} hk1 {φ} {M_φ} hsupp hM_φ hφ0 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_sub := hC₀ (K := 2 * k) h2k_ge1 hsupp hM_φ hφ0
  have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
  have h_exp : (1 : ℝ) - (2 * Δ_phi + 1) = - (2 * Δ_phi) := by ring
  rw [h_cast, h_exp] at h_sub
  have hG_inv :
      universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
        (Real.Gamma (2 * Δ_phi + 1))⁻¹ = universalPrimaryLeadingCoeff Δ_phi :=
    mul_inv_cancel_right₀ hG.ne' _
  have h_eq :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ -
        transmutedUniversalPairing Δ_phi φ =
      pref *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi + 1) (n + 2 * k) * φ (Δ_phi + (n : ℝ))) -
          (Real.Gamma (2 * Δ_phi + 1))⁻¹ *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ)))) := by
    dsimp [transmutedIdentityPairing, transmutedUniversalPairing, pref]
    linear_combination
      (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ))) * hG_inv
  rw [h_eq, abs_mul, abs_of_pos hpref_pos]
  calc
    pref *
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi + 1) (n + 2 * k) * φ (Δ_phi + (n : ℝ))) -
          (Real.Gamma (2 * Δ_phi + 1))⁻¹ *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ)))|
      ≤ pref * (C₀ * (2 * (k : ℝ))⁻¹ * M_φ) :=
        mul_le_mul_of_nonneg_left h_sub hpref_pos.le
    _ = (pref * C₀) * (2 * (k : ℝ))⁻¹ * M_φ := by ring

/-- The exact finite-spin transmuted $t$-channel identity Laplace transform at spin $K$:
$$\operatorname{exactTransmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  e^{\Delta_\phi \sigma} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \,
    \operatorname{exactTransmutedPochhammer}(\Delta_\phi, n + K) \, e^{n \sigma}.$$ -/
noncomputable def exactTransmutedIdentityLaplaceReal (Δ_phi : ℝ) (K : ℕ) (σ : ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) * Real.exp (Δ_phi * σ) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
      (Real.exp σ) ^ n

lemma exactTransmutedIdentityLaplaceReal_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {K : ℕ} (hK : 1 ≤ K) (σ : ℝ) :
    0 ≤ exactTransmutedIdentityLaplaceReal Δ_phi K σ := by
  unfold exactTransmutedIdentityLaplaceReal
  have h1 : 0 < universalPrimaryLeadingCoeff Δ_phi := universalPrimaryLeadingCoeff_pos hΔ
  have h2 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  refine mul_nonneg (by positivity) (tsum_nonneg fun n => ?_)
  exact mul_nonneg
    (mul_nonneg (pochhammerCoeff_nonneg (by positivity) n)
      (exactTransmutedPochhammer_nonneg hΔ (by omega : 1 ≤ n + K)))
    (by positivity)

/-- Exact finite-spin transmuted $t$-channel identity test-function pairing at spin $K$:
$$\operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, K, \varphi) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \,
    \operatorname{exactTransmutedPochhammer}(\Delta_\phi, n + K) \,
    \varphi(\Delta_\phi + n).$$ -/
noncomputable def exactTransmutedIdentityPairing (Δ_phi : ℝ) (K : ℕ) (φ : ℝ → ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
      φ (Δ_phi + (n : ℝ))

/-- **Kinematic $O(k^{-1})$ Proximity of `exactTransmutedIdentityPairing` and
`transmutedIdentityPairing`**:
For all $\Delta_\phi > 0$ and support bound $N \in \mathbb{N}$, there exists $C > 0$ such that
for all $k \ge 1$ and all $\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi(h)| \le M_\varphi$ ($M_\varphi \ge 0$),
$$\Bigl|(2k)^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)
  - (2k)^{-2\Delta_\phi} \operatorname{transmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)\Bigr|
  \le C \, (2k)^{-1} \, M_\varphi.$$ -/
theorem exists_const_abs_exactTransmutedIdentityPairing_sub_transmutedIdentityPairing_le
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ))⁻¹ * M_φ := by
  have ha : 0 < 2 * Δ_phi := by positivity
  let p : ℕ := ⌈|((2 * Δ_phi) - 1) - 1|⌉₊ + 1
  obtain ⟨C₀, B, hC₀_nonneg, hB_pos, h_coeff⟩ :=
    exists_abs_rpow_mul_pochhammerCoeff_add_sub_inv_gamma_le ha
  let N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  let s : Finset ℕ := Finset.range (N_shift + 1)
  set pref : ℝ := universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)
  have hpref_pos : 0 < pref :=
    mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.Gamma_pos_of_pos (by positivity))
  set κ : ℝ := 1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2)
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  let w : ℕ → ℝ := fun n =>
    pochhammerCoeff (2 * Δ_phi) n *
      ((Real.Gamma (2 * Δ_phi))⁻¹ + C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p)
  have hw_nonneg : ∀ n : ℕ, 0 ≤ w n := fun n => by
    dsimp [w]
    have hG : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos ha
    have hp : 0 ≤ pochhammerCoeff (2 * Δ_phi) n := pochhammerCoeff_nonneg ha.le n
    positivity
  set C_final : ℝ := pref * κ * ((∑ n ∈ s, w n) + 1)
  have hC_final_pos : 0 < C_final := by
    dsimp [C_final]
    have hsum_nonneg : 0 ≤ ∑ n ∈ s, w n := Finset.sum_nonneg fun n _ => hw_nonneg n
    positivity
  refine ⟨C_final, hC_final_pos, fun {k} hk1 {φ} {M_φ} hsupp hM_φ hφ0 => ?_⟩
  set K : ℕ := 2 * k
  have hK : 1 ≤ K := by omega
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK_cast : (K : ℝ) = 2 * (k : ℝ) := by dsimp [K]; push_cast; rfl
  have h_vanish : ∀ n ∉ s, φ (Δ_phi + (n : ℝ)) = 0 := by
    intro n hn
    dsimp [s] at hn
    rw [Finset.mem_range, not_lt] at hn
    have h_gt : ((N_shift : ℕ) : ℝ) < |(n : ℝ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      exact_mod_cast hn
    exact shiftedTest_eq_zero_of_support Δ_phi hsupp h_gt
  have h_tsum1 :
      (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
        exactTransmutedPochhammer Δ_phi (n + K) * φ (Δ_phi + (n : ℝ))) =
        ∑ n ∈ s, pochhammerCoeff (2 * Δ_phi) n *
          exactTransmutedPochhammer Δ_phi (n + K) * φ (Δ_phi + (n : ℝ)) :=
    tsum_eq_sum fun n hn => by rw [h_vanish n hn, mul_zero]
  have h_tsum2 :
      (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
        pochhammerCoeff (2 * Δ_phi + 1) (n + K) * φ (Δ_phi + (n : ℝ))) =
        ∑ n ∈ s, pochhammerCoeff (2 * Δ_phi) n *
          pochhammerCoeff (2 * Δ_phi + 1) (n + K) * φ (Δ_phi + (n : ℝ)) :=
    tsum_eq_sum fun n hn => by rw [h_vanish n hn, mul_zero]
  have h_diff_eq :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi K φ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi K φ =
      pref * ∑ n ∈ s,
        (K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
          (exactTransmutedPochhammer Δ_phi (n + K) -
            pochhammerCoeff (2 * Δ_phi + 1) (n + K)) * φ (Δ_phi + (n : ℝ)) := by
    dsimp [exactTransmutedIdentityPairing, transmutedIdentityPairing, pref]
    rw [h_tsum1, h_tsum2, ← hK_cast]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [h_diff_eq, ← hK_cast, abs_mul, abs_of_pos hpref_pos]
  have h_term_bound : ∀ n ∈ s,
      |(K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
          (exactTransmutedPochhammer Δ_phi (n + K) -
            pochhammerCoeff (2 * Δ_phi + 1) (n + K)) * φ (Δ_phi + (n : ℝ))| ≤
        κ * w n * (K : ℝ)⁻¹ * M_φ := by
    intro n _
    have hnK : 1 ≤ n + K := by omega
    have hp_n : 0 ≤ pochhammerCoeff (2 * Δ_phi) n := pochhammerCoeff_nonneg ha.le n
    have hp_nK : 0 ≤ pochhammerCoeff (2 * Δ_phi) (n + K) := pochhammerCoeff_nonneg ha.le (n + K)
    have hG_pos : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos ha
    have h_abs_diff := abs_exactTransmutedPochhammer_sub_pochhammerCoeff_le hΔ hnK
    have h_rpow_split : (K : ℝ) ^ (- (2 * Δ_phi)) = (K : ℝ)⁻¹ * (K : ℝ) ^ (1 - 2 * Δ_phi) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hK_pos]
      congr 1
      ring
    have h_stirling := h_coeff hK n
    have h_inv_le : 1 / (K : ℝ) ≤ 1 := div_le_one_of_le₀ hK_ge1 hK_pos.le
    have h_poch_bound :
        (K : ℝ) ^ (1 - 2 * Δ_phi) * pochhammerCoeff (2 * Δ_phi) (n + K) ≤
          (Real.Gamma (2 * Δ_phi))⁻¹ + C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p := by
      have h1 :
          (K : ℝ) ^ (1 - 2 * Δ_phi) * pochhammerCoeff (2 * Δ_phi) (n + K) -
            (Real.Gamma (2 * Δ_phi))⁻¹ ≤
          (C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) :=
        (le_abs_self _).trans h_stirling
      have h2 :
          (C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) ≤
            C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p := by
        rw [div_eq_mul_inv, ← one_div]
        exact mul_le_of_le_one_right (by positivity) h_inv_le
      linarith
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hK_pos _),
      abs_of_nonneg hp_n]
    calc
      (K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
          |exactTransmutedPochhammer Δ_phi (n + K) -
            pochhammerCoeff (2 * Δ_phi + 1) (n + K)| *
          |φ (Δ_phi + (n : ℝ))|
        ≤ (K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
            (κ * pochhammerCoeff (2 * Δ_phi) (n + K)) * M_φ := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_left h_abs_diff (by positivity))
            (hφ0 (Δ_phi + (n : ℝ))) (abs_nonneg _) (by positivity)
      _ = κ * pochhammerCoeff (2 * Δ_phi) n *
            ((K : ℝ) ^ (1 - 2 * Δ_phi) * pochhammerCoeff (2 * Δ_phi) (n + K)) *
            (K : ℝ)⁻¹ * M_φ := by
          rw [h_rpow_split]
          ring
      _ ≤ κ * pochhammerCoeff (2 * Δ_phi) n *
            ((Real.Gamma (2 * Δ_phi))⁻¹ + C₀ + B * |2 * Δ_phi - 1| * (1 + (n : ℝ)) ^ p) *
            (K : ℝ)⁻¹ * M_φ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_poch_bound
                (mul_nonneg hκ_pos.le (pochhammerCoeff_nonneg ha.le n)))
              (inv_nonneg.mpr hK_pos.le))
            hM_φ
      _ = κ * w n * (K : ℝ)⁻¹ * M_φ := by dsimp [w]; ring
  calc
    pref *
        |∑ n ∈ s,
          (K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
            (exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)) * φ (Δ_phi + (n : ℝ))|
      ≤ pref * ∑ n ∈ s,
          |(K : ℝ) ^ (- (2 * Δ_phi)) * pochhammerCoeff (2 * Δ_phi) n *
            (exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)) * φ (Δ_phi + (n : ℝ))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hpref_pos.le
    _ ≤ pref * ∑ n ∈ s, (κ * w n * (K : ℝ)⁻¹ * M_φ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_term_bound) hpref_pos.le
    _ = pref * κ * (∑ n ∈ s, w n) * (K : ℝ)⁻¹ * M_φ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
    _ ≤ C_final * (K : ℝ)⁻¹ * M_φ := by
        dsimp [C_final]
        have : 0 ≤ pref * κ * (K : ℝ)⁻¹ * M_φ := by positivity
        nlinarith

/-- **Kinematic Large-$k$ Expansion of `exactTransmutedIdentityPairing` to
`transmutedUniversalPairing`**:
For all $\Delta_\phi > 0$ and support bound $N \in \mathbb{N}$, there exists $C > 0$ such that
for all $k \ge 1$ and all $\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi(h)| \le M_\varphi$ ($M_\varphi \ge 0$),
$$\Bigl|(2k)^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)
  - \operatorname{transmutedUniversalPairing}(\Delta_\phi, \varphi)\Bigr|
  \le C \, (2k)^{-1} \, M_\varphi.$$ -/
theorem exists_const_abs_exactTransmutedIdentityPairing_sub_universal_le
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
        transmutedUniversalPairing Δ_phi φ| ≤
        C * (2 * (k : ℝ))⁻¹ * M_φ := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    exists_const_abs_exactTransmutedIdentityPairing_sub_transmutedIdentityPairing_le hΔ N
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_const_abs_transmutedIdentityPairing_sub_universal_le hΔ N
  refine ⟨C₁ + C₂, add_pos hC₁_pos hC₂_pos, fun {k} hk1 {φ} {M_φ} hsupp hM_φ hφ0 => ?_⟩
  calc
    |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
        transmutedUniversalPairing Δ_phi φ|
      = |((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ) +
          ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ -
            transmutedUniversalPairing Δ_phi φ)| := by ring_nf
    _ ≤ |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ| +
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ -
            transmutedUniversalPairing Δ_phi φ| := abs_add_le _ _
    _ ≤ C₁ * (2 * (k : ℝ))⁻¹ * M_φ + C₂ * (2 * (k : ℝ))⁻¹ * M_φ :=
        add_le_add (hC₁ hk1 hsupp hM_φ hφ0) (hC₂ hk1 hsupp hM_φ hφ0)
    _ = (C₁ + C₂) * (2 * (k : ℝ))⁻¹ * M_φ := by ring

/-- Summability of the mixed series defining `exactTransmutedIdentityLaplaceReal` for $\sigma < 0$. -/
lemma summable_pochhammerCoeff_mul_exactTransmutedPochhammer_mul_exp
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {K : ℕ} (hK : 1 ≤ K) {σ : ℝ} (hσ : σ < 0) :
    Summable (fun n : ℕ =>
      pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
        (Real.exp σ) ^ n) := by
  have ha : 0 < 2 * Δ_phi := by positivity
  have hb : 0 < 2 * Δ_phi + 1 := by positivity
  set κ : ℝ := 1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2)
  have h_sum1 := summable_pochhammerCoeff_mixed_mul_exp ha hb K hσ
  have h_sum2 := (summable_pochhammerCoeff_mixed_mul_exp ha ha K hσ).mul_left κ
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (mul_nonneg (pochhammerCoeff_nonneg ha.le n)
        (exactTransmutedPochhammer_nonneg hΔ (by omega : 1 ≤ n + K)))
      (by positivity))
    (fun n => ?_) (h_sum1.add h_sum2)
  have hnK : 1 ≤ n + K := by omega
  have h_diff := (le_abs_self _).trans (abs_exactTransmutedPochhammer_sub_pochhammerCoeff_le hΔ hnK)
  have h_le :
      exactTransmutedPochhammer Δ_phi (n + K) ≤
        pochhammerCoeff (2 * Δ_phi + 1) (n + K) + κ * pochhammerCoeff (2 * Δ_phi) (n + K) := by
    linarith
  calc
    pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) * (Real.exp σ) ^ n
      ≤ pochhammerCoeff (2 * Δ_phi) n *
          (pochhammerCoeff (2 * Δ_phi + 1) (n + K) +
            κ * pochhammerCoeff (2 * Δ_phi) (n + K)) *
          (Real.exp σ) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_le (pochhammerCoeff_nonneg ha.le n))
          (by positivity)
    _ = pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
          (Real.exp σ) ^ n +
        κ * (pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) *
          (Real.exp σ) ^ n) := by ring

/-- Upper bound on `pochhammerCoeff (2 * Δ_phi) m` by
`((2 * Δ_phi) / (m : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) m` for $m \ge 1$. -/
lemma pochhammerCoeff_le_div_mul_pochhammerCoeff_add_one {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {m : ℕ} (hm : 1 ≤ m) :
    pochhammerCoeff (2 * Δ_phi) m ≤
      (2 * Δ_phi / (m : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have h_add_pos : 0 < 2 * Δ_phi + (m : ℝ) := by positivity
  have h_id := mul_pochhammerCoeff_add_one (2 * Δ_phi) m
  have h_eq :
      pochhammerCoeff (2 * Δ_phi) m =
        (2 * Δ_phi / (2 * Δ_phi + (m : ℝ))) * pochhammerCoeff (2 * Δ_phi + 1) m := by
    rw [div_mul_eq_mul_div, eq_div_iff h_add_pos.ne']
    linarith [h_id]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by positivity) hm_pos (by linarith))
    (pochhammerCoeff_nonneg (by positivity) m)

/-- **Uniform $O(K^{-1})$ Proximity of `exactTransmutedIdentityLaplaceReal` and
`transmutedIdentityLaplaceReal` on $(-\infty, \sigma_+]$**:
For every $\Delta_\phi > 0$ and $\sigma_+ < 0$, there exists $C \ge 0$ such that for all $K \ge 1$
and all $\sigma \le \sigma_+$,
$$\Bigl|K^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma)
  - K^{-2\Delta_\phi} \operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma)\Bigr|
  \le \frac{C}{K}.$$ -/
theorem exists_uniform_bound_exactTransmutedIdentityLaplaceReal_sub_transmutedIdentityLaplaceReal
    {Δ_phi σ_plus : ℝ} (hΔ : 0 < Δ_phi) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ {σ : ℝ}, σ ≤ σ_plus →
      |(K : ℝ) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi K σ -
        (K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ| ≤ C / (K : ℝ) := by
  have ha : 0 < 2 * Δ_phi := by positivity
  have hb : 0 < 2 * Δ_phi + 1 := by positivity
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
  set κ : ℝ := 1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2)
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  set L_max : ℝ := transmutedUniversalLaplaceReal Δ_phi σ_plus + C₁
  have hL_max_nonneg : 0 ≤ L_max :=
    add_nonneg (transmutedUniversalLaplaceReal_nonneg hΔ hσ_plus) hC₁_nonneg
  set C_final : ℝ := 2 * Δ_phi * κ * L_max
  refine ⟨C_final, by positivity, fun {K} hK {σ} hσ => ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hσ_neg : σ < 0 := lt_of_le_of_lt hσ hσ_plus
  have h_sum_exact :=
    summable_pochhammerCoeff_mul_exactTransmutedPochhammer_mul_exp hΔ hK hσ_neg
  have h_sum_trans := summable_pochhammerCoeff_mixed_mul_exp ha hb K hσ_neg
  set pref : ℝ :=
    universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) * Real.exp (Δ_phi * σ)
  have hpref_pos : 0 < pref :=
    mul_pos
      (mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.Gamma_pos_of_pos hb))
      (Real.exp_pos _)
  have h_tsum_diff :
      |exactTransmutedIdentityLaplaceReal Δ_phi K σ -
          transmutedIdentityLaplaceReal Δ_phi K σ| ≤
        (2 * Δ_phi * κ / (K : ℝ)) * transmutedIdentityLaplaceReal Δ_phi K σ := by
    dsimp [exactTransmutedIdentityLaplaceReal, transmutedIdentityLaplaceReal]
    rw [← mul_sub, ← h_sum_exact.tsum_sub h_sum_trans, abs_mul, abs_of_pos hpref_pos]
    have h_term_le : ∀ n : ℕ,
        ‖pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
            (Real.exp σ) ^ n -
          pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
            (Real.exp σ) ^ n‖ ≤
        (2 * Δ_phi * κ / (K : ℝ)) *
          (pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
            (Real.exp σ) ^ n) := by
      intro n
      rw [Real.norm_eq_abs]
      have hnK : 1 ≤ n + K := by omega
      have hnK_ge : (K : ℝ) ≤ ((n + K : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ n + K)
      have h_factor :
          pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
              (Real.exp σ) ^ n -
            pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
              (Real.exp σ) ^ n =
          pochhammerCoeff (2 * Δ_phi) n *
            (exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)) * (Real.exp σ) ^ n := by ring
      rw [h_factor, abs_mul, abs_mul,
        abs_of_nonneg (pochhammerCoeff_nonneg ha.le n),
        abs_of_pos (by positivity : 0 < (Real.exp σ) ^ n)]
      have h1 := abs_exactTransmutedPochhammer_sub_pochhammerCoeff_le hΔ hnK
      have h2 := (pochhammerCoeff_le_div_mul_pochhammerCoeff_add_one hΔ hnK).trans
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left ha.le hK_pos hnK_ge)
          (pochhammerCoeff_nonneg hb.le (n + K)))
      have h12 :
          |exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)| ≤
            (2 * Δ_phi * κ / (K : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) (n + K) := by
        calc
          |exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)|
            ≤ κ * pochhammerCoeff (2 * Δ_phi) (n + K) := h1
          _ ≤ κ * ((2 * Δ_phi / (K : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) (n + K)) :=
              mul_le_mul_of_nonneg_left h2 hκ_pos.le
          _ = (2 * Δ_phi * κ / (K : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) (n + K) := by ring
      calc
        pochhammerCoeff (2 * Δ_phi) n *
            |exactTransmutedPochhammer Δ_phi (n + K) -
              pochhammerCoeff (2 * Δ_phi + 1) (n + K)| *
            (Real.exp σ) ^ n
          ≤ pochhammerCoeff (2 * Δ_phi) n *
              ((2 * Δ_phi * κ / (K : ℝ)) * pochhammerCoeff (2 * Δ_phi + 1) (n + K)) *
              (Real.exp σ) ^ n :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h12 (pochhammerCoeff_nonneg ha.le n))
              (by positivity)
        _ = (2 * Δ_phi * κ / (K : ℝ)) *
              (pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
                (Real.exp σ) ^ n) := by ring
    have h_tsum_le := norm_tsum_le_tsum_norm (h_sum_exact.sub h_sum_trans).norm
    rw [Real.norm_eq_abs] at h_tsum_le
    have h_sum_dom := Summable.tsum_le_tsum h_term_le
      (h_sum_exact.sub h_sum_trans).norm (h_sum_trans.mul_left _)
    rw [tsum_mul_left] at h_sum_dom
    calc
      pref *
          |∑' n : ℕ,
            (pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
                (Real.exp σ) ^ n -
              pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
                (Real.exp σ) ^ n)|
        ≤ pref *
            ((2 * Δ_phi * κ / (K : ℝ)) *
              ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
                pochhammerCoeff (2 * Δ_phi + 1) (n + K) * (Real.exp σ) ^ n) :=
          mul_le_mul_of_nonneg_left (h_tsum_le.trans h_sum_dom) hpref_pos.le
      _ = (2 * Δ_phi * κ / (K : ℝ)) *
            (pref * ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi + 1) (n + K) * (Real.exp σ) ^ n) := by ring
  have h_univ_mono :
      transmutedUniversalLaplaceReal Δ_phi σ ≤ transmutedUniversalLaplaceReal Δ_phi σ_plus := by
    rw [transmutedUniversalLaplaceReal_eq Δ_phi hΔ, transmutedUniversalLaplaceReal_eq Δ_phi hΔ]
    have h1 : Real.exp (Δ_phi * σ) ≤ Real.exp (Δ_phi * σ_plus) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hΔ.le)
    have h2 : 1 - Real.exp σ_plus ≤ 1 - Real.exp σ :=
      sub_le_sub_left (Real.exp_le_exp.mpr hσ) 1
    have h1_σ : 0 < 1 - Real.exp σ := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_neg)
    have h3 : (1 - Real.exp σ) ^ (- (2 * Δ_phi)) ≤ (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
      Real.rpow_le_rpow_of_nonpos
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_plus)) h2 (by linarith)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left h1 (universalPrimaryLeadingCoeff_pos hΔ).le)
      h3 (by positivity)
      (mul_nonneg (universalPrimaryLeadingCoeff_pos hΔ).le (Real.exp_pos _).le)
  have h_trans_le :
      (K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ ≤ L_max := by
    have h1 := (le_abs_self _).trans (hC₁ hK hσ)
    have h2 : C₁ / (K : ℝ) ≤ C₁ := div_le_self hC₁_nonneg hK_ge1
    dsimp [L_max]
    linarith
  rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hK_pos _)]
  calc
    (K : ℝ) ^ (- (2 * Δ_phi)) *
        |exactTransmutedIdentityLaplaceReal Δ_phi K σ -
          transmutedIdentityLaplaceReal Δ_phi K σ|
      ≤ (K : ℝ) ^ (- (2 * Δ_phi)) *
          ((2 * Δ_phi * κ / (K : ℝ)) * transmutedIdentityLaplaceReal Δ_phi K σ) :=
        mul_le_mul_of_nonneg_left h_tsum_diff (by positivity)
    _ = (2 * Δ_phi * κ / (K : ℝ)) *
          ((K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ) := by ring
    _ ≤ (2 * Δ_phi * κ / (K : ℝ)) * L_max :=
        mul_le_mul_of_nonneg_left h_trans_le (by positivity)
    _ = C_final / (K : ℝ) := by dsimp [C_final]; ring

/-- **Uniform $O(K^{-1})$ Convergence of `exactTransmutedIdentityLaplaceReal` to
`transmutedUniversalLaplaceReal` on $(-\infty, \sigma_+]$**:
For every $\Delta_\phi > 0$ and $\sigma_+ < 0$, there exists $C \ge 0$ such that for all $K \ge 1$
and all $\sigma \le \sigma_+$,
$$\Bigl|K^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma)
  - \operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma)\Bigr|
  \le \frac{C}{K}.$$ -/
theorem exists_uniform_bound_exactTransmutedIdentityLaplaceReal_sub_universal
    {Δ_phi σ_plus : ℝ} (hΔ : 0 < Δ_phi) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ {σ : ℝ}, σ ≤ σ_plus →
      |(K : ℝ) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi K σ -
        transmutedUniversalLaplaceReal Δ_phi σ| ≤ C / (K : ℝ) := by
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_uniform_bound_exactTransmutedIdentityLaplaceReal_sub_transmutedIdentityLaplaceReal
      hΔ hσ_plus
  obtain ⟨C₂, hC₂_nonneg, hC₂⟩ :=
    exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
  refine ⟨C₁ + C₂, add_nonneg hC₁_nonneg hC₂_nonneg, fun {K} hK {σ} hσ => ?_⟩
  calc
    |(K : ℝ) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi K σ -
        transmutedUniversalLaplaceReal Δ_phi σ|
      = |((K : ℝ) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi K σ -
            (K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ) +
          ((K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ -
            transmutedUniversalLaplaceReal Δ_phi σ)| := by ring_nf
    _ ≤ |(K : ℝ) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi K σ -
            (K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ| +
          |(K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ -
            transmutedUniversalLaplaceReal Δ_phi σ| := abs_add_le _ _
    _ ≤ C₁ / (K : ℝ) + C₂ / (K : ℝ) := add_le_add (hC₁ hK hσ) (hC₂ hK hσ)
    _ = (C₁ + C₂) / (K : ℝ) := by ring

/-- Rescaled weight of the $n$-th double-twist atom of the exact transmuted $t$-channel identity
reference $M^0_{2k}$ at spin $2k$. -/
noncomputable def exactTransmutedIdentityRescaledCoeff (Δ_phi : ℝ) (k n : ℕ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
    (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)) *
    pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + 2 * k)

lemma exactTransmutedIdentityRescaledCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    0 ≤ exactTransmutedIdentityRescaledCoeff Δ_phi k n := by
  unfold exactTransmutedIdentityRescaledCoeff
  have h1 : 0 < universalPrimaryLeadingCoeff Δ_phi := universalPrimaryLeadingCoeff_pos hΔ
  have h2 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact mul_nonneg
    (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
    (exactTransmutedPochhammer_nonneg hΔ (by omega : 1 ≤ n + 2 * k))

/-- Exact finite-spin transmuted $t$-channel identity shifted measure on $\mathbb{R}$, supported on
$\mathbb{N} \subset \mathbb{Z}$. -/
noncomputable def exactTransmutedIdentityShiftedMeasure (Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  natShiftedMeasure (exactTransmutedIdentityRescaledCoeff Δ_phi k)

lemma exactTransmutedIdentityShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) (k : ℕ) :
    exactTransmutedIdentityShiftedMeasure Δ_phi k (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
  natShiftedMeasure_compl_intCast_eq_zero _

lemma hasSum_exactTransmutedIdentityRescaledCoeff_mul_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : σ < 0) :
    HasSum (fun n : ℕ => exactTransmutedIdentityRescaledCoeff Δ_phi k n * Real.exp (σ * (n : ℝ)))
      (Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ)) := by
  have h2k : 1 ≤ 2 * k := by omega
  have h_sum :=
    (summable_pochhammerCoeff_mul_exactTransmutedPochhammer_mul_exp hΔ h2k hσ).hasSum.mul_left
      ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)))
  have h_target :
      ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1))) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
          exactTransmutedPochhammer Δ_phi (n + 2 * k) * (Real.exp σ) ^ n) =
        Real.exp (-Δ_phi * σ) *
          ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ) := by
    dsimp [exactTransmutedIdentityLaplaceReal]
    have hexp_canc : Real.exp (-Δ_phi * σ) * Real.exp (Δ_phi * σ) = 1 := by
      rw [← Real.exp_add]
      have : -Δ_phi * σ + Δ_phi * σ = 0 := by ring
      rw [this, Real.exp_zero]
    linear_combination
      -(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1))) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
          exactTransmutedPochhammer Δ_phi (n + 2 * k) * (Real.exp σ) ^ n)) * hexp_canc
  rw [h_target] at h_sum
  refine h_sum.congr_fun fun n => ?_
  dsimp [exactTransmutedIdentityRescaledCoeff]
  rw [← Real.exp_nat_mul]
  ring_nf

lemma integrable_exp_exactTransmutedIdentityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) {k : ℕ} (hk : 1 ≤ k) (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u))
      (exactTransmutedIdentityShiftedMeasure Δ_phi k) :=
  integrable_exp_natShiftedMeasure (exactTransmutedIdentityRescaledCoeff_nonneg hΔ hk)
    (hasSum_exactTransmutedIdentityRescaledCoeff_mul_exp hΔ hk hσ)

lemma laplaceTransformReal_exactTransmutedIdentityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) {k : ℕ} (hk : 1 ≤ k) (hσ : σ < 0) :
    laplaceTransformReal (exactTransmutedIdentityShiftedMeasure Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ) :=
  laplaceTransformReal_natShiftedMeasure (exactTransmutedIdentityRescaledCoeff_nonneg hΔ hk)
    (hasSum_exactTransmutedIdentityRescaledCoeff_mul_exp hΔ hk hσ)

lemma integral_shiftedTest_exactTransmutedIdentityShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {k : ℕ} (hk : 1 ≤ k) (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(exactTransmutedIdentityShiftedMeasure Δ_phi k) =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityPairing Δ_phi (2 * k) φ := by
  unfold exactTransmutedIdentityShiftedMeasure exactTransmutedIdentityPairing
  rw [integral_shiftedTest_natShiftedMeasure
    (exactTransmutedIdentityRescaledCoeff_nonneg hΔ hk) Δ_phi N hφ hsupp]
  dsimp [exactTransmutedIdentityRescaledCoeff]
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-! ## Section 4: Fourier Projections & Outer-Contour Bounds for `crossIdentityExactTransmuted` -/

/-- The folded $[-\pi/2, \pi/2]$ Fourier projection of `crossIdentityExactTransmuted Δ_phi`:
$$\operatorname{exactTransmutedIdentityProjSpin}(\Delta_\phi, J, w_l, w_r) :=
  \frac{1}{\pi} \int_{-\pi/2}^{\pi/2} e^{-J(w_r + i\theta)}
    \operatorname{crossIdentityExactTransmuted}(\Delta_\phi, w_l - i\theta, w_r + i\theta) \,
    d\theta.$$ -/
noncomputable def exactTransmutedIdentityProjSpin (Δ_phi : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

/-- The full $[-\pi, \pi]$ Fourier projection of `crossIdentityExactTransmuted Δ_phi`:
$$\operatorname{exactTransmutedIdentityProjSpinFull}(\Delta_\phi, J, w_l, w_r) :=
  \frac{1}{\pi} \int_{-\pi}^{\pi} e^{-J(w_r + i\theta)}
    \operatorname{crossIdentityExactTransmuted}(\Delta_\phi, w_l - i\theta, w_r + i\theta) \,
    d\theta.$$ -/
noncomputable def exactTransmutedIdentityProjSpinFull (Δ_phi : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π)..π,
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

lemma continuous_exactTransmutedPolyFactor (Δ_phi : ℝ) :
    Continuous (exactTransmutedPolyFactor Δ_phi) := by
  unfold exactTransmutedPolyFactor
  fun_prop

lemma continuousOn_crossFactorExactTransmuted (Δ_phi : ℝ) :
    ContinuousOn (crossFactorExactTransmuted Δ_phi) UcDisk :=
  (continuousOn_crossFactorTransmuted Δ_phi).mul
    (continuous_exactTransmutedPolyFactor Δ_phi).continuousOn

lemma continuous_crossIdentityExactTransmuted_shift (Δ_phi : ℝ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Continuous (fun θ : ℝ =>
      crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
  have h1 : Continuous (fun θ : ℝ => crossFactor Δ_phi (wl - (θ : ℂ) * I)) :=
    (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ)
  have h2 : Continuous (fun θ : ℝ => crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)) :=
    (continuousOn_crossFactorExactTransmuted Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ)
  exact h1.mul h2

/-- Uniform bound on `‖exactTransmutedPolyFactor Δ_phi w‖` for $w \in \operatorname{UcDisk}$. -/
lemma norm_exactTransmutedPolyFactor_le_of_mem_UcDisk (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    ‖exactTransmutedPolyFactor Δ_phi w‖ ≤
      3 + 4 * |(Δ_phi - 1 / 2) / (4 * Δ_phi)| := by
  unfold exactTransmutedPolyFactor
  have hexp_le1 : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hw).le
  have h1w_le2 : ‖1 - Complex.exp w‖ ≤ 2 := by
    calc
      ‖1 - Complex.exp w‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp w‖ := norm_sub_le _ _
      _ = 1 + ‖Complex.exp w‖ := by rw [norm_one]
      _ ≤ 2 := by linarith
  have h1w_sq_le4 : ‖(1 - Complex.exp w) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (1 - Complex.exp w)]
  calc
    ‖1 - (1 - Complex.exp w) +
        (((Δ_phi - 1 / 2) / (4 * Δ_phi) : ℝ) : ℂ) * (1 - Complex.exp w) ^ 2‖
      ≤ ‖1 - (1 - Complex.exp w)‖ +
          ‖(((Δ_phi - 1 / 2) / (4 * Δ_phi) : ℝ) : ℂ) * (1 - Complex.exp w) ^ 2‖ :=
        norm_add_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖1 - Complex.exp w‖) +
          |(Δ_phi - 1 / 2) / (4 * Δ_phi)| * ‖(1 - Complex.exp w) ^ 2‖ := by
        refine add_le_add (norm_sub_le _ _) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 + 2) + |(Δ_phi - 1 / 2) / (4 * Δ_phi)| * 4 := by
        rw [norm_one]
        exact add_le_add (by linarith)
          (mul_le_mul_of_nonneg_left h1w_sq_le4 (abs_nonneg _))
    _ = 3 + 4 * |(Δ_phi - 1 / 2) / (4 * Δ_phi)| := by ring

/-- Upper bound on `‖crossFactorExactTransmuted Δ_phi w‖` when $\operatorname{Re}(w) \le a < 0$. -/
theorem norm_crossFactorExactTransmuted_le_of_re_le {Δ_phi a : ℝ} (hΔ : 0 < Δ_phi) (ha : a < 0)
    {w : ℂ} (hw : w ∈ UcDisk) (hwa : w.re ≤ a) :
    ‖crossFactorExactTransmuted Δ_phi w‖ ≤
      (3 + 4 * |(Δ_phi - 1 / 2) / (4 * Δ_phi)|) *
        ((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
          (1 - Real.exp a) ^ (- (2 * Δ_phi + 1))) := by
  unfold crossFactorExactTransmuted
  rw [norm_mul, mul_comm]
  exact mul_le_mul
    (norm_exactTransmutedPolyFactor_le_of_mem_UcDisk Δ_phi hw)
    (norm_crossFactorTransmuted_le_of_re_le hΔ ha hw hwa)
    (norm_nonneg _) (by positivity)

/-- Global absolute-value bound on `exactTransmutedPochhammer Δ_phi m` for all $m \in \mathbb{N}$
and $\Delta_\phi > 0$. -/
lemma abs_exactTransmutedPochhammer_le {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (m : ℕ) :
    |exactTransmutedPochhammer Δ_phi m| ≤
      pochhammerCoeff (2 * Δ_phi + 1) m +
        (1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2) +
          |(Δ_phi - 1 / 2) / (4 * Δ_phi)|) * pochhammerCoeff (2 * Δ_phi) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp only [exactTransmutedPochhammer_zero, pochhammerCoeff_zero, mul_one]
    have : 0 ≤ (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2) := by positivity
    linarith
  · have hm1 : 1 ≤ m := hm_pos
    rw [abs_of_nonneg (exactTransmutedPochhammer_nonneg hΔ hm1)]
    have h_sub := (le_abs_self _).trans (abs_exactTransmutedPochhammer_sub_pochhammerCoeff_le hΔ hm1)
    have h_extra :
        0 ≤ |(Δ_phi - 1 / 2) / (4 * Δ_phi)| * pochhammerCoeff (2 * Δ_phi) m :=
      mul_nonneg (abs_nonneg _) (pochhammerCoeff_nonneg (by positivity) m)
    linarith

lemma summable_abs_exactTransmutedPochhammer_mul_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {σ : ℝ} (hσ : σ < 0) :
    Summable (fun m : ℕ =>
      |exactTransmutedPochhammer Δ_phi m| * Real.exp ((Δ_phi + (m : ℝ)) * σ)) := by
  set c_dom : ℝ :=
    1 + (Δ_phi - 1 / 2) ^ 2 / (4 * Δ_phi ^ 2) + |(Δ_phi - 1 / 2) / (4 * Δ_phi)|
  have h1 := (hasSum_exp_mul_one_sub_exp_rpow_neg_transmuted Δ_phi hσ).summable
  have h2 := ((hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hσ).summable).mul_left c_dom
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    (fun m => ?_) (h1.add h2)
  calc
    |exactTransmutedPochhammer Δ_phi m| * Real.exp ((Δ_phi + (m : ℝ)) * σ)
      ≤ (pochhammerCoeff (2 * Δ_phi + 1) m + c_dom * pochhammerCoeff (2 * Δ_phi) m) *
          Real.exp ((Δ_phi + (m : ℝ)) * σ) :=
        mul_le_mul_of_nonneg_right (abs_exactTransmutedPochhammer_le hΔ m) (Real.exp_pos _).le
    _ = pochhammerCoeff (2 * Δ_phi + 1) m * Real.exp ((Δ_phi + (m : ℝ)) * σ) +
          c_dom * (pochhammerCoeff (2 * Δ_phi) m * Real.exp ((Δ_phi + (m : ℝ)) * σ)) := by
        ring

/-- Fourier coefficient extraction from `crossFactorExactTransmuted Δ_phi (wr + i θ)` on
$[-\pi, \pi]$. -/
lemma integral_exp_mul_crossFactorExactTransmuted_shift {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (M : ℕ)
    {wr : ℂ} (hwr : wr ∈ UcDisk) :
    (∫ θ in (-π)..π,
      Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
        crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)) =
      (2 * π : ℂ) *
        (((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
          exactTransmutedPochhammer Δ_phi M : ℝ) : ℂ) *
        Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr) := by
  have hG1 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  set pref_r : ℝ := Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi
  have hpref_pos : 0 < pref_r := by positivity
  set F : ℕ → ℝ → ℂ := fun m θ =>
    (((pref_r * exactTransmutedPochhammer Δ_phi m : ℝ) : ℂ) *
      Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr)) *
      Complex.exp ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I)
  set bound : ℕ → ℝ → ℝ := fun m _ =>
    pref_r * (|exactTransmutedPochhammer Δ_phi m| * Real.exp ((Δ_phi + (m : ℝ)) * wr.re))
  have h_summable_bound : Summable (fun m : ℕ => bound m 0) :=
    (summable_abs_exactTransmutedPochhammer_mul_exp hΔ hwr).mul_left pref_r
  have h_hasSum_int :
      HasSum (fun m : ℕ => ∫ θ in (-π)..π, F m θ)
        (∫ θ in (-π)..π,
          Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
            crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      bound ?_ ?_ ?_ ?_ ?_
    · intro m
      have h_cont : Continuous (F m) := by dsimp [F]; fun_prop
      exact h_cont.aestronglyMeasurable
    · intro m
      filter_upwards with θ _
      dsimp [F, bound]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hpref_pos, Complex.norm_exp, Complex.norm_exp]
      have h_re1 : (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr).re = (Δ_phi + (m : ℝ)) * wr.re := by
        simp [Complex.mul_re]
      have h_re2 : ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I).re = 0 := by
        simp [Complex.mul_re]
      rw [h_re1, h_re2, Real.exp_zero, mul_one, mul_assoc]
    · filter_upwards with θ _
      exact h_summable_bound
    · exact intervalIntegrable_const (c := ∑' m : ℕ,
        pref_r * (|exactTransmutedPochhammer Δ_phi m| * Real.exp ((Δ_phi + (m : ℝ)) * wr.re)))
    · filter_upwards with θ _
      have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
      have h_pt := (hasSum_crossFactorExactTransmuted Δ_phi hwr_θ).mul_left
        (Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I))
      refine h_pt.congr_fun fun m => ?_
      dsimp [F, pref_r]
      have h_exp :
          Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
            Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * (wr + (θ : ℂ) * I)) =
          Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr) *
            Complex.exp ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination
        -(((pref_r * exactTransmutedPochhammer Δ_phi m : ℝ) : ℂ)) * h_exp
  have h_term : ∀ m : ℕ,
      (∫ θ in (-π)..π, F m θ) =
        if m = M then
          (2 * π : ℂ) * (((pref_r * exactTransmutedPochhammer Δ_phi M : ℝ) : ℂ)) *
            Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr)
        else 0 := by
    intro m
    dsimp [F]
    rw [intervalIntegral.integral_const_mul,
      integral_exp_int_mul_I ((m : ℤ) - (M : ℤ))]
    simp only [sub_eq_zero, Int.ofNat_inj]
    split_ifs with hm
    · subst hm; ring
    · ring
  simp_rw [h_term] at h_hasSum_int
  exact h_hasSum_int.unique
    (hasSum_ite_eq M
      ((2 * π : ℂ) * (((pref_r * exactTransmutedPochhammer Δ_phi M : ℝ) : ℂ)) *
        Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr)))

/-- Exact mixed-binomial series evaluation of `exactTransmutedIdentityProjSpinFull` on
$[-\pi, \pi]$. -/
lemma hasSum_exactTransmutedIdentityProjSpinFull {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    HasSum
      (fun n : ℕ =>
        (((universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)) *
          pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl + wr)))
      (exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ) wl wr) := by
  set F : ℕ → ℝ → ℂ := fun n θ =>
    ((((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n : ℝ) : ℂ) *
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr)) *
      (Complex.exp (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
        crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I))
  set K_wr : ℝ :=
    (3 + 4 * |(Δ_phi - 1 / 2) / (4 * Δ_phi)|) *
      ((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
        (1 - Real.exp wr.re) ^ (- (2 * Δ_phi + 1)))
  set bound : ℕ → ℝ → ℝ := fun n _ =>
    ((4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr) *
      (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * wl.re))
  have h_sum_wl := hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hwl
  have h_hasSum_int :
      HasSum (fun n : ℕ => ∫ θ in (-π)..π, F n θ)
        (∫ θ in (-π)..π,
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      bound ?_ ?_ ?_ ?_ ?_
    · intro n
      have h_cf : Continuous (fun θ : ℝ => crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)) :=
        (continuousOn_crossFactorExactTransmuted Δ_phi).comp_continuous (by fun_prop)
          (fun θ => MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ)
      have h_cont : Continuous (F n) := by
        dsimp [F]
        exact continuous_const.mul ((by fun_prop : Continuous _).mul h_cf)
      exact h_cont.aestronglyMeasurable
    · intro n
      filter_upwards with θ _
      dsimp [F, bound]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg
          (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n)),
        Complex.norm_exp, Complex.norm_exp]
      have h_re1 : (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr).re =
          (Δ_phi + (n : ℝ)) * wl.re + (- (K : ℝ) * wr.re) := by
        simp [Complex.sub_re, Complex.mul_re]
        ring
      have h_re2 : (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I).re = 0 := by
        simp [Complex.mul_re]
      rw [h_re1, Real.exp_add, h_re2, Real.exp_zero, one_mul]
      have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
      have h_cf_le : ‖crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)‖ ≤ K_wr :=
        norm_crossFactorExactTransmuted_le_of_re_le hΔ hwr hwr_θ (by simp)
      calc
        (4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n *
            (Real.exp ((Δ_phi + (n : ℝ)) * wl.re) * Real.exp (- (K : ℝ) * wr.re)) *
            ‖crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)‖
          ≤ (4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n *
              (Real.exp ((Δ_phi + (n : ℝ)) * wl.re) *
                Real.exp (- (K : ℝ) * wr.re)) * K_wr := by
            refine mul_le_mul_of_nonneg_left h_cf_le ?_
            exact mul_nonneg
              (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
              (by positivity)
        _ = (4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr *
              (pochhammerCoeff (2 * Δ_phi) n *
                Real.exp ((Δ_phi + (n : ℝ)) * wl.re)) := by ring
    · filter_upwards with θ _
      exact h_sum_wl.summable.mul_left _
    · exact intervalIntegrable_const (c := ∑' n : ℕ,
        ((4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr) *
          (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * wl.re)))
    · filter_upwards with θ _
      have hwl_θ : wl - (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ
      have h_pt :=
        ((hasSum_crossFactor Δ_phi hwl_θ).mul_left
          (Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)))).mul_right
          (crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I))
      have h_ci :
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossFactor Δ_phi (wl - (θ : ℂ) * I) *
            crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I) =
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) := by
        dsimp [crossIdentityExactTransmuted]; ring
      rw [h_ci] at h_pt
      refine h_pt.congr_fun fun n => ?_
      dsimp [F]
      have h_exp :
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl - (θ : ℂ) * I)) =
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr) *
            Complex.exp (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination
        -((((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n : ℝ) : ℂ) *
          crossFactorExactTransmuted Δ_phi (wr + (θ : ℂ) * I)) * h_exp
  have h_scaled := h_hasSum_int.mul_left (π : ℂ)⁻¹
  refine h_scaled.congr_fun fun n => ?_
  dsimp [F]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_crossFactorExactTransmuted_shift hΔ (n + K) hwr]
  have h_pi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h_exp :
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr) *
        Complex.exp (((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * wr) =
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl + wr)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h4_sq : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num), two_mul]
  dsimp [universalPrimaryLeadingCoeff]
  rw [h4_sq, ← h_exp]
  push_cast
  linear_combination
    -(2 * (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) * (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) /
      ((Real.Gamma Δ_phi : ℂ) ^ 2) * (Real.Gamma (2 * Δ_phi + 1) : ℂ) *
      (pochhammerCoeff (2 * Δ_phi) n : ℂ) *
      (exactTransmutedPochhammer Δ_phi (n + K) : ℂ) *
      Complex.exp ((((Δ_phi : ℂ) + (n : ℂ)) * wl - (K : ℂ) * wr)) *
      Complex.exp ((((Δ_phi : ℂ) + ((n : ℂ) + (K : ℂ))) * wr))) *
      (inv_mul_cancel₀ h_pi)

/-- For any $\sigma_l < 0$ and $\sigma_r < 0$ with $\sigma_l + \sigma_r = \sigma$, the full
$[-\pi, \pi]$ integral `exactTransmutedIdentityProjSpinFull` equals
`(exactTransmutedIdentityLaplaceReal Δ_phi K σ : ℂ)`. -/
lemma exactTransmutedIdentityProjSpinFull_eq_exactTransmutedIdentityLaplaceReal_of_add_eq
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ) {σl σr σ : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (h_add : σl + σr = σ) :
    exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ) (σl : ℂ) (σr : ℂ) =
      (exactTransmutedIdentityLaplaceReal Δ_phi K σ : ℂ) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa using hσr
  have h_sum := hasSum_exactTransmutedIdentityProjSpinFull hΔ K hwl hwr
  have h_add_c : (σl : ℂ) + (σr : ℂ) = (σ : ℂ) := by exact_mod_cast h_add
  rw [h_add_c] at h_sum
  have h_sum_real :
      HasSum
        (fun n : ℕ =>
          ((((universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
            Real.exp (Δ_phi * σ)) *
            (pochhammerCoeff (2 * Δ_phi) n * exactTransmutedPochhammer Δ_phi (n + K) *
              (Real.exp σ) ^ n) : ℝ) : ℂ)))
        (exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ) (σl : ℂ) (σr : ℂ)) := by
    refine h_sum.congr_fun fun n => ?_
    have hexp_cast :
        Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (σ : ℂ)) =
          ((Real.exp (Δ_phi * σ) * (Real.exp σ) ^ n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, add_mul,
        Real.exp_add, Real.exp_nat_mul]
    rw [hexp_cast]
    push_cast
    ring
  rw [← h_sum_real.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rfl

/-- Specialization of `exactTransmutedIdentityProjSpinFull_eq_exactTransmutedIdentityLaplaceReal_of_add_eq`
at $(\sigma + 1/K, -1/K)$. -/
lemma exactTransmutedIdentityProjSpinFull_eq_exactTransmutedIdentityLaplaceReal
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {K : ℕ} (hK : 1 ≤ K) {σ : ℝ}
    (hσl : σ + 1 / (K : ℝ) < 0) :
    exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ)
        (((σ + 1 / (K : ℝ) : ℝ) : ℂ)) (((-1 / (K : ℝ) : ℝ) : ℂ)) =
      (exactTransmutedIdentityLaplaceReal Δ_phi K σ : ℂ) := by
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hσr : -1 / (K : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hK_pos
  exact exactTransmutedIdentityProjSpinFull_eq_exactTransmutedIdentityLaplaceReal_of_add_eq
    hΔ K hσl hσr (by ring)

/-- Pointwise bound on `‖crossFactor Δ_phi ((σl : ℂ) - (θ : ℂ) * I)‖` when $\sigma_l < 0$ and
$\cos\theta \le 0$. -/
lemma norm_crossFactor_sub_I_le_of_cos_nonpos {Δ_phi σl θ : ℝ} (hΔ : 0 < Δ_phi)
    (hσl : σl < 0) (hcos : Real.cos θ ≤ 0) :
    ‖crossFactor Δ_phi ((σl : ℂ) - (θ : ℂ) * I)‖ ≤ (4 : ℝ) ^ Δ_phi := by
  unfold crossFactor
  have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_cpow (by norm_num)]
  have h_sub : (σl : ℂ) - (θ : ℂ) * I = (σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I := by
    push_cast; ring
  have h_α : (- (2 * Δ_phi : ℂ)) = ((-2 * Δ_phi : ℝ) : ℂ) := by push_cast; ring
  rw [h4_cast, h_sub, h_α, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Complex.norm_exp]
  have h_re : ((Δ_phi : ℂ) * ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)).re = Δ_phi * σl := by
    simp [Complex.mul_re]
  rw [h_re]
  have hexp_le1 : Real.exp (Δ_phi * σl) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσl.le)
  have hcos_neg : Real.cos (-1 * θ) ≤ 0 := by rw [neg_one_mul, Real.cos_neg]; exact hcos
  have hcpow_le1 :
      ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ)‖ ≤ 1 :=
    norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_neg (by linarith)
  calc
    (4 : ℝ) ^ Δ_phi * Real.exp (Δ_phi * σl) *
        ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ)‖
      ≤ (4 : ℝ) ^ Δ_phi * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
          hcpow_le1 (norm_nonneg _) (by positivity)
    _ = (4 : ℝ) ^ Δ_phi := by ring

/-- Pointwise bound on `‖crossFactorTransmuted Δ_phi ((σr : ℂ) + (θ : ℂ) * I)‖` when
$\sigma_r < 0$ and $\cos\theta \le 0$. -/
lemma norm_crossFactorTransmuted_add_I_le_of_cos_nonpos {Δ_phi σr θ : ℝ} (hΔ : 0 < Δ_phi)
    (hσr : σr < 0) (hcos : Real.cos θ ≤ 0) :
    ‖crossFactorTransmuted Δ_phi ((σr : ℂ) + (θ : ℂ) * I)‖ ≤
      Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi := by
  unfold crossFactorTransmuted
  have hG1 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  have h_add : (σr : ℂ) + (θ : ℂ) * I = (σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I := by
    push_cast; ring
  have h_α : (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) = ((-(2 * Δ_phi + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h_add, h_α, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Complex.norm_exp]
  have h_re : ((Δ_phi : ℂ) * ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)).re = Δ_phi * σr := by
    simp [Complex.mul_re]
  rw [h_re]
  have hexp_le1 : Real.exp (Δ_phi * σr) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσr.le)
  have hcos_one : Real.cos (1 * θ) ≤ 0 := by rw [one_mul]; exact hcos
  have hcpow_le1 :
      ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ ((-(2 * Δ_phi + 1) : ℝ) : ℂ)‖ ≤ 1 :=
    norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_one (by linarith)
  calc
    (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
        Real.exp (Δ_phi * σr) *
        ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ ((-(2 * Δ_phi + 1) : ℝ) : ℂ)‖
      ≤ (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
          hcpow_le1 (norm_nonneg _) (by positivity)
    _ = Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi := by ring

/-- **Uniform $O(K^{-2\Delta_\phi})$ Outer $\theta$-Integral Bound for Exact Transmuted Identity**:
For $\Delta_\phi > 0$, there exists $C_{\text{out}} \ge 0$ such that for all $K \ge 1$ and all
$\sigma < 0$ with $\sigma + 1 / K < 0$, the rescaled outer integral
`exactTransmutedIdentityProjSpinFull - exactTransmutedIdentityProjSpin` on
$[-\pi, -\pi/2] \cup [\pi/2, \pi]$ is bounded by $C_{\text{out}} \, K^{-2\Delta_\phi}$. -/
theorem exists_uniform_bound_exactTransmutedIdentityProjSpinFull_sub_exactTransmutedIdentityProjSpin_real
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) :
    ∃ C_out : ℝ, 0 ≤ C_out ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ {σ : ℝ}, σ < 0 →
      σ + 1 / (K : ℝ) < 0 →
      ‖(((K : ℝ) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
          (exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ)
              (((σ + 1 / (K : ℝ) : ℝ) : ℂ)) (((-1 / (K : ℝ) : ℝ) : ℂ)) -
            exactTransmutedIdentityProjSpin Δ_phi (K : ℤ)
              (((σ + 1 / (K : ℝ) : ℝ) : ℂ)) (((-1 / (K : ℝ) : ℝ) : ℂ)))‖ ≤
        C_out * (K : ℝ) ^ (- (2 * Δ_phi)) := by
  have hG1 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  set M_poly : ℝ := 3 + 4 * |(Δ_phi - 1 / 2) / (4 * Δ_phi)|
  have hM_poly_pos : 0 < M_poly := by dsimp [M_poly]; positivity
  set M_id : ℝ :=
    Real.exp 1 * (4 : ℝ) ^ Δ_phi *
      (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi * M_poly)
  have hM_id_pos : 0 < M_id := by positivity
  refine ⟨M_id, hM_id_pos.le, fun {K} hK {σ} _hσ hσl => ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  set σl : ℝ := σ + 1 / (K : ℝ)
  set σr : ℝ := -1 / (K : ℝ)
  have hσr : σr < 0 := div_neg_of_neg_of_pos (by norm_num) hK_pos
  set wl : ℂ := (σl : ℂ)
  set wr : ℂ := (σr : ℂ)
  have hwl : wl ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wl] using hσl
  have hwr : wr ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wr] using hσr
  let f : ℝ → ℂ := fun θ =>
    Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentityExactTransmuted Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)
  have hf_cont : Continuous f :=
    (by fun_prop : Continuous _).mul
      (continuous_crossIdentityExactTransmuted_shift Δ_phi hwl hwr)
  have h_diff :
      exactTransmutedIdentityProjSpinFull Δ_phi (K : ℤ) wl wr -
        exactTransmutedIdentityProjSpin Δ_phi (K : ℤ) wl wr =
      (π : ℂ)⁻¹ * ((∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ)) := by
    dsimp [exactTransmutedIdentityProjSpinFull, exactTransmutedIdentityProjSpin, f]
    rw [← mul_sub, integral_minus_pi_to_pi_sub_half hf_cont]
  have hf_bound_of_cos : ∀ {θ : ℝ}, Real.cos θ ≤ 0 → ‖f θ‖ ≤ M_id := by
    intro θ hcos
    dsimp [f, crossIdentityExactTransmuted, crossFactorExactTransmuted]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    have h_re_exp : (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)).re = 1 := by
      dsimp [wr, σr]
      simp [Complex.mul_re]
      have hK_ne : (K : ℝ) ≠ 0 := hK_pos.ne'
      field_simp
    rw [h_re_exp]
    have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk :=
      MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
    have h1 := norm_crossFactor_sub_I_le_of_cos_nonpos hΔ hσl hcos
    have h2 := norm_crossFactorTransmuted_add_I_le_of_cos_nonpos hΔ hσr hcos
    have h3 := norm_exactTransmutedPolyFactor_le_of_mem_UcDisk Δ_phi hwr_θ
    calc
      Real.exp 1 *
          (‖crossFactor Δ_phi (wl - (θ : ℂ) * I)‖ *
            (‖crossFactorTransmuted Δ_phi (wr + (θ : ℂ) * I)‖ *
              ‖exactTransmutedPolyFactor Δ_phi (wr + (θ : ℂ) * I)‖))
        ≤ Real.exp 1 *
            ((4 : ℝ) ^ Δ_phi *
              ((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
                M_poly)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1
              (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
            (Real.exp_pos 1).le
      _ = M_id := by dsimp [M_id]; ring
  have h_int1 : ‖∫ θ in (-π)..(-π / 2), f θ‖ ≤ M_id * |-π / 2 - -π| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    refine hf_bound_of_cos ?_
    rw [← Real.cos_neg]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.2])
      (by linarith [hθ.1, Real.pi_pos])
  have h_int2 : ‖∫ θ in (π / 2)..π, f θ‖ ≤ M_id * |π - π / 2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    refine hf_bound_of_cos ?_
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2, Real.pi_pos])
  have h_abs1 : |-π / 2 - -π| = π / 2 := by
    have : -π / 2 - -π = π / 2 := by ring
    rw [this, abs_of_pos (by positivity)]
  have h_abs2 : |π - π / 2| = π / 2 := by
    have : π - π / 2 = π / 2 := by ring
    rw [this, abs_of_pos (by positivity)]
  rw [h_abs1] at h_int1
  rw [h_abs2] at h_int2
  rw [h_diff, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ (K : ℝ) ^ (- (2 * Δ_phi))),
    norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h_sum_int :
      π⁻¹ * ‖(∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ)‖ ≤ M_id := by
    have h_pi_ne : π ≠ 0 := Real.pi_ne_zero
    calc
      π⁻¹ * ‖(∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ)‖
        ≤ π⁻¹ * (‖∫ θ in (-π)..(-π / 2), f θ‖ + ‖∫ θ in (π / 2)..π, f θ‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ π⁻¹ * (M_id * (π / 2) + M_id * (π / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add h_int1 h_int2) (by positivity)
      _ = M_id * (π⁻¹ * π) := by ring
      _ = M_id := by rw [inv_mul_cancel₀ h_pi_ne, mul_one]
  calc
    (K : ℝ) ^ (- (2 * Δ_phi)) *
        (π⁻¹ * ‖(∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ)‖)
      ≤ (K : ℝ) ^ (- (2 * Δ_phi)) * M_id :=
        mul_le_mul_of_nonneg_left h_sum_int (by positivity)
    _ = M_id * (K : ℝ) ^ (- (2 * Δ_phi)) := by ring

/-! ## Section 5: Differential Identities & Bootstrap Against `exactTransmutedIdentityPairing` -/

/-- **Mode Identity Relating `pochhammerCoeff (2 * Δ_phi - 1) m` and `exactTransmutedPochhammer`**:
For all $\Delta_\phi \ne 0$ and $m \in \mathbb{N}$,
$$\left(\Delta_\phi + m - \frac{1}{2}\right)^2 \frac{(2\Delta_\phi - 1)_m}{m!} =
  2\Delta_\phi (2\Delta_\phi - 1) \, \operatorname{exactTransmutedPochhammer}(\Delta_\phi, m).$$
This reflects the action of $\bigl(\partial_w - \tfrac{1}{2}\bigr)^2$ on the modes
$e^{(\Delta_\phi + m) w}$ of $e^{\Delta_\phi w} (1 - e^w)^{-(2\Delta_\phi - 1)}$. -/
theorem sq_sub_half_mul_pochhammerCoeff_eq {Δ_phi : ℝ} (hΔ : Δ_phi ≠ 0) (m : ℕ) :
    (Δ_phi + (m : ℝ) - 1 / 2) ^ 2 * pochhammerCoeff (2 * Δ_phi - 1) m =
      2 * Δ_phi * (2 * Δ_phi - 1) * exactTransmutedPochhammer Δ_phi m := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pochhammerCoeff_zero, mul_one,
      exactTransmutedPochhammer_zero]
    field_simp
    ring
  | succ k _ =>
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := hk1_pos.ne'
    apply mul_left_cancel₀ hk1_ne
    have h_p := pochhammerCoeff_succ_eq (2 * Δ_phi - 1) k
    have h_add : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
    rw [h_add] at h_p
    rw [exactTransmutedPochhammer_succ hΔ k]
    have h_div :
        ((k + 1 : ℕ) : ℝ) *
          (2 * Δ_phi * (2 * Δ_phi - 1) *
            ((Δ_phi + (k : ℝ) + 1 / 2) ^ 2 / (2 * Δ_phi * ((k + 1 : ℕ) : ℝ)) *
              pochhammerCoeff (2 * Δ_phi) k)) =
        (Δ_phi + (k : ℝ) + 1 / 2) ^ 2 * (2 * Δ_phi - 1) * pochhammerCoeff (2 * Δ_phi) k := by
      field_simp
    rw [h_div]
    push_cast at h_p ⊢
    linear_combination (Δ_phi + (k : ℝ) + 1 / 2) ^ 2 * h_p

/-- Action of `derivHalfSub` ($\partial_w - \tfrac{1}{2}$) on
$z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-a}$ for $w \in \operatorname{UcDisk}$:
$$\operatorname{derivHalfSub}\bigl(z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-a}\bigr)(w) =
  \left(\Delta_\phi - a - \frac{1}{2}\right) e^{\Delta_\phi w} (1 - e^w)^{-a}
  + a \, e^{\Delta_\phi w} (1 - e^w)^{-(a + 1)}.$$ -/
lemma derivHalfSub_exp_mul_one_sub_exp_cpow_eq (Δ_phi a : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    derivHalfSub
      (fun z : ℂ => Complex.exp ((Δ_phi : ℂ) * z) * (1 - Complex.exp z) ^ (- (a : ℂ))) w =
    ((Δ_phi - a - 1 / 2 : ℝ) : ℂ) *
      (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- (a : ℂ))) +
    (a : ℂ) *
      (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- ((a + 1 : ℝ) : ℂ))) := by
  dsimp [derivHalfSub]
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp ((Δ_phi : ℂ) * z))
      (Complex.exp ((Δ_phi : ℂ) * w) * (Δ_phi : ℂ)) w := by
    have h_lin : HasDerivAt (fun z : ℂ => (Δ_phi : ℂ) * z) (Δ_phi : ℂ) w := by
      simpa using (hasDerivAt_id w).const_mul (Δ_phi : ℂ)
    exact h_lin.cexp
  have h2 : HasDerivAt (fun z : ℂ => 1 - Complex.exp z) (- Complex.exp w) w := by
    have h := (hasDerivAt_const w (1 : ℂ)).sub (Complex.hasDerivAt_exp w)
    rw [zero_sub] at h
    exact h
  have h3 : HasDerivAt (fun z : ℂ => (1 - Complex.exp z) ^ (- (a : ℂ)))
      ((- (a : ℂ)) * (1 - Complex.exp w) ^ (- (a : ℂ) - 1) * (- Complex.exp w)) w :=
    h2.cpow_const (one_sub_exp_mem_slitPlane hw)
  have h_prod : HasDerivAt
      (fun z : ℂ => Complex.exp ((Δ_phi : ℂ) * z) * (1 - Complex.exp z) ^ (- (a : ℂ)))
      ((Complex.exp ((Δ_phi : ℂ) * w) * (Δ_phi : ℂ)) * (1 - Complex.exp w) ^ (- (a : ℂ)) +
        Complex.exp ((Δ_phi : ℂ) * w) *
          ((- (a : ℂ)) * (1 - Complex.exp w) ^ (- (a : ℂ) - 1) * (- Complex.exp w))) w :=
    h1.mul h3
  rw [h_prod.deriv]
  have hz_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h_exp_sub : - (a : ℂ) - 1 = - ((a + 1 : ℝ) : ℂ) := by push_cast; ring
  have h_cpow :
      (1 - Complex.exp w) ^ (- ((a + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) =
        (1 - Complex.exp w) ^ (- (a : ℂ)) := by
    calc
      (1 - Complex.exp w) ^ (- ((a + 1 : ℝ) : ℂ)) * (1 - Complex.exp w)
        = (1 - Complex.exp w) ^ (- ((a + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
      _ = (1 - Complex.exp w) ^ (- ((a + 1 : ℝ) : ℂ) + (1 : ℂ)) :=
          (Complex.cpow_add _ _ hz_ne).symm
      _ = (1 - Complex.exp w) ^ (- (a : ℂ)) := by
          congr 1; push_cast; ring
  rw [h_exp_sub, ← h_cpow]
  push_cast
  ring

/-- First application of `derivHalfSub` to $z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-(2\Delta_\phi - 1)}$
on $\operatorname{UcDisk}$:
$$\operatorname{derivHalfSub}\bigl(z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-(2\Delta_\phi - 1)}\bigr)(w)
  = \left(\Delta_\phi - \frac{1}{2}\right) e^{\Delta_\phi w} (1 + e^w) (1 - e^w)^{-2\Delta_\phi}.$$ -/
theorem derivHalfSub_exp_mul_one_sub_exp_cpow (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    derivHalfSub
      (fun z : ℂ =>
        Complex.exp ((Δ_phi : ℂ) * z) *
          (1 - Complex.exp z) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ))) w =
      ((Δ_phi - 1 / 2 : ℝ) : ℂ) * Complex.exp ((Δ_phi : ℂ) * w) *
        (1 + Complex.exp w) * (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) := by
  rw [derivHalfSub_exp_mul_one_sub_exp_cpow_eq Δ_phi (2 * Δ_phi - 1) hw]
  have h_add : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
  rw [h_add]
  have hz_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h_cpow :
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) * (1 - Complex.exp w) =
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)) := by
    calc
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) * (1 - Complex.exp w)
        = (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) * (1 - Complex.exp w) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ) + (1 : ℂ)) :=
          (Complex.cpow_add _ _ hz_ne).symm
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)) := by
          congr 1; push_cast; ring
  rw [← h_cpow]
  push_cast
  ring

/-- Second application of `derivHalfSub` ($\bigl(\partial_w - \tfrac{1}{2}\bigr)^2$) to
$z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-(2\Delta_\phi - 1)}$ on $\operatorname{UcDisk}$:
$$\operatorname{derivHalfSub}^2\bigl(z \mapsto e^{\Delta_\phi z} (1 - e^z)^{-(2\Delta_\phi - 1)}\bigr)(w)
  = 2\Delta_\phi (2\Delta_\phi - 1) \, e^{\Delta_\phi w} (1 - e^w)^{-(2\Delta_\phi + 1)} \,
    \operatorname{exactTransmutedPolyFactor}(\Delta_\phi, w).$$ -/
theorem derivHalfSub_derivHalfSub_exp_mul_one_sub_exp_cpow {Δ_phi : ℝ} (hΔ : Δ_phi ≠ 0)
    {w : ℂ} (hw : w ∈ UcDisk) :
    derivHalfSub
      (derivHalfSub
        (fun z : ℂ =>
          Complex.exp ((Δ_phi : ℂ) * z) *
            (1 - Complex.exp z) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)))) w =
      ((2 * Δ_phi * (2 * Δ_phi - 1) : ℝ) : ℂ) *
        Complex.exp ((Δ_phi : ℂ) * w) *
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) *
        exactTransmutedPolyFactor Δ_phi w := by
  let f1 : ℂ → ℂ := fun z =>
    Complex.exp ((Δ_phi : ℂ) * z) * (1 - Complex.exp z) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ))
  let f2 : ℂ → ℂ := fun z =>
    Complex.exp ((Δ_phi : ℂ) * z) * (1 - Complex.exp z) ^ (- ((2 * Δ_phi : ℝ) : ℂ))
  let c1 : ℂ := ((Δ_phi - (2 * Δ_phi - 1) - 1 / 2 : ℝ) : ℂ)
  let c2 : ℂ := ((2 * Δ_phi - 1 : ℝ) : ℂ)
  have h_step1 : ∀ z ∈ UcDisk,
      derivHalfSub f1 z = c1 * f1 z + c2 * f2 z := by
    intro z hz
    have h := derivHalfSub_exp_mul_one_sub_exp_cpow_eq Δ_phi (2 * Δ_phi - 1) hz
    have h_add : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
    rw [h_add] at h
    exact h
  rw [derivHalfSub_congr_ucDisk h_step1 w hw]
  have hf1_diff : DifferentiableAt ℂ f1 w := by
    dsimp [f1]
    refine ((differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp).mul ?_
    exact ((differentiableAt_const 1).sub differentiableAt_id.cexp).cpow_const
      (one_sub_exp_mem_slitPlane hw)
  have hf2_diff : DifferentiableAt ℂ f2 w := by
    dsimp [f2]
    refine ((differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp).mul ?_
    exact ((differentiableAt_const 1).sub differentiableAt_id.cexp).cpow_const
      (one_sub_exp_mem_slitPlane hw)
  have h_sum_deriv : HasDerivAt (fun z => c1 * f1 z + c2 * f2 z)
      (c1 * deriv f1 w + c2 * deriv f2 w) w :=
    (hf1_diff.hasDerivAt.const_mul c1).add (hf2_diff.hasDerivAt.const_mul c2)
  have h_lin :
      derivHalfSub (fun z => c1 * f1 z + c2 * f2 z) w =
        c1 * derivHalfSub f1 w + c2 * derivHalfSub f2 w := by
    dsimp [derivHalfSub]
    rw [h_sum_deriv.deriv]
    ring
  rw [h_lin]
  have hd1 := derivHalfSub_exp_mul_one_sub_exp_cpow_eq Δ_phi (2 * Δ_phi - 1) hw
  have h_add1 : 2 * Δ_phi - 1 + 1 = 2 * Δ_phi := by ring
  rw [h_add1] at hd1
  have hd2 := derivHalfSub_exp_mul_one_sub_exp_cpow_eq Δ_phi (2 * Δ_phi) hw
  change c1 * derivHalfSub f1 w + c2 * derivHalfSub f2 w = _
  rw [hd1, hd2]
  have hz_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h_cpow1 :
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) =
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) := by
    calc
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w)
        = (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ) + (1 : ℂ)) :=
          (Complex.cpow_add _ _ hz_ne).symm
      _ = (1 - Complex.exp w) ^ (- ((2 * Δ_phi : ℝ) : ℂ)) := by
          congr 1; push_cast; ring
  have h_cpow2 :
      (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ)) * (1 - Complex.exp w) ^ 2 =
        (1 - Complex.exp w) ^ (- ((2 * Δ_phi - 1 : ℝ) : ℂ)) := by
    have h_sq : (1 - Complex.exp w) ^ 2 = (1 - Complex.exp w) ^ (2 : ℂ) := by norm_cast
    rw [h_sq, ← Complex.cpow_add _ _ hz_ne]
    congr 1
    push_cast
    ring
  dsimp [exactTransmutedPolyFactor, c1, c2]
  rw [← h_cpow1, ← h_cpow2]
  have hΔ_c : (Δ_phi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ
  push_cast
  field_simp [hΔ_c]
  ring

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **Transmuted $t$-Channel Crossing & Twist-Gap Hypothesis Against the Exact Reference
`exactTransmutedIdentityLaplaceReal` (`HasExactTransmutedCrossingGap`)**:
States that on every compact negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$, the
rescaled spin-$2k$ Laplace transform of the transmuted $s$-channel correlator agrees with the exact
finite-spin transmuted $t$-channel identity Laplace transform
`exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ` up to an $O((2k)^{-2 h_{\text{gap}}} +
(2k)^{-2\Delta_\phi})$ remainder. -/
structure HasExactTransmutedCrossingGap (Δ_phi : ℝ) : Prop where
  /-- Positivity of the external scaling dimension $\Delta_\phi > 0$. -/
  Δ_phi_pos : 0 < Δ_phi
  /-- Positivity of the $t$-channel non-identity twist gap $h_{\text{gap}} > 0$. -/
  h_gap_pos : 0 < L.h_gap
  /-- Uniform real-axis Laplace remainder bound on compact intervals
  $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ for all $k \ge 1$. -/
  exists_remainder_bound :
    ∀ {σ_minus σ_plus : ℝ}, σ_minus ≤ σ_plus → σ_plus < 0 →
      ∃ C_rem : ℝ, 0 ≤ C_rem ∧ ∀ {k : ℕ}, 1 ≤ k →
        ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
            C_rem * ((2 * (k : ℝ)) ^ (- (2 * L.h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)))

/-- **Uniform Real-Axis Laplace Upper and Error Bounds Against `exactTransmutedIdentityLaplaceReal`
(Valid for All $\Delta_\phi > 0$)**:
For any `LightconeBlockFourPointData` satisfying `HasExactTransmutedCrossingGap Δ_phi` and any
compact negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$, with
$$\alpha := \min(2 h_{\text{gap}},\, 2\Delta_\phi) > 0,$$
there exist constants $M_{\text{bd}} > 0$ and $C_{\text{bd}} > 0$ such that for all $k \ge 1$ and
all $\sigma \in [\sigma_-, \sigma_+]$:
1. $(2k)^{-2\Delta_\phi} \bigl(L^{\text{trans}}_{2k}(\sigma) +
     \operatorname{exactTransmutedIdentityLaplaceReal}(\Delta_\phi, 2k, \sigma)\bigr)
     \le M_{\text{bd}}$,
2. $\bigl|(2k)^{-2\Delta_\phi} L^{\text{trans}}_{2k}(\sigma) -
     (2k)^{-2\Delta_\phi}
       \operatorname{exactTransmutedIdentityLaplaceReal}(\Delta_\phi, 2k, \sigma)\bigr|
     \le C_{\text{bd}} \, (2k)^{-\alpha}$. -/
theorem exists_uniform_transmuted_laplaceSpinReal_sub_exactIdentity_bounds
    {Δ_phi : ℝ} (hcross : L.HasExactTransmutedCrossingGap Δ_phi)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    let α := min (2 * L.h_gap) (2 * Δ_phi)
    0 < α ∧ ∃ M_bd > 0, ∃ C_bd > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ +
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ ≤ M_bd ∧
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
          C_bd * (2 * (k : ℝ)) ^ (-α) := by
  intro α
  have hΔ : 0 < Δ_phi := hcross.Δ_phi_pos
  have hh_gap : 0 < L.h_gap := hcross.h_gap_pos
  have hα_pos : 0 < α := lt_min (by positivity) (by positivity)
  refine ⟨hα_pos, ?_⟩
  obtain ⟨C_rem, hC_rem_nonneg, hC_rem⟩ := hcross.exists_remainder_bound hσ_le hσ_plus
  obtain ⟨C_id, hC_id_nonneg, hC_id⟩ :=
    exists_uniform_bound_exactTransmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
  have h1_exp_pos : 0 < 1 - Real.exp σ_plus :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_plus)
  set U_plus : ℝ :=
    universalPrimaryLeadingCoeff Δ_phi * (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi))
  have hU_plus_pos : 0 < U_plus := by
    dsimp [U_plus]
    exact mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.rpow_pos_of_pos h1_exp_pos _)
  have h_univ_le : ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      transmutedUniversalLaplaceReal Δ_phi σ ≤ U_plus := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [transmutedUniversalLaplaceReal_eq Δ_phi hΔ]
    have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσ_neg.le)
    have h1_sub_ge : 1 - Real.exp σ_plus ≤ 1 - Real.exp σ := by
      linarith [Real.exp_le_exp.mpr hσ.2]
    have hrpow_le : (1 - Real.exp σ) ^ (- (2 * Δ_phi)) ≤
        (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
      Real.rpow_le_rpow_of_nonpos h1_exp_pos h1_sub_ge (by linarith)
    have h1_exp_σ_pos : 0 < 1 - Real.exp σ := by linarith
    calc
      universalPrimaryLeadingCoeff Δ_phi * Real.exp (Δ_phi * σ) *
          (1 - Real.exp σ) ^ (- (2 * Δ_phi))
        ≤ (universalPrimaryLeadingCoeff Δ_phi * 1) *
            (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_le1 (universalPrimaryLeadingCoeff_pos hΔ).le)
            hrpow_le (Real.rpow_pos_of_pos h1_exp_σ_pos _).le
            (mul_pos (universalPrimaryLeadingCoeff_pos hΔ) zero_lt_one).le
      _ = U_plus := by dsimp [U_plus]; ring
  set C_bd : ℝ := 2 * C_rem + 1
  have hC_bd_pos : 0 < C_bd := by dsimp [C_bd]; positivity
  set M_bd : ℝ := 2 * (U_plus + C_id) + C_bd
  have hM_bd_pos : 0 < M_bd := by dsimp [M_bd]; positivity
  refine ⟨M_bd, hM_bd_pos, C_bd, hC_bd_pos, fun {k} hk1 {σ} hσ => ?_⟩
  have h2k_ge1_nat : 1 ≤ 2 * k := by omega
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have hr1 : (2 * (k : ℝ)) ^ (- (2 * L.h_gap)) ≤ (2 * (k : ℝ)) ^ (-α) := by
    refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
    have : α ≤ 2 * L.h_gap := min_le_left _ _
    linarith
  have hr2 : (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) ≤ (2 * (k : ℝ)) ^ (-α) := by
    refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
    have : α ≤ 2 * Δ_phi := min_le_right _ _
    linarith
  have h_err :
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
        C_bd * (2 * (k : ℝ)) ^ (-α) := by
    calc
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ|
        ≤ C_rem * ((2 * (k : ℝ)) ^ (- (2 * L.h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
          hC_rem hk1 hσ
      _ ≤ C_rem * ((2 * (k : ℝ)) ^ (-α) + (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hC_rem_nonneg
      _ ≤ C_bd * (2 * (k : ℝ)) ^ (-α) := by
          dsimp [C_bd]
          have : 0 ≤ (2 * (k : ℝ)) ^ (-α) := by positivity
          nlinarith
  have h_id_bd :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ ≤
        U_plus + C_id := by
    have h_sub := hC_id h2k_ge1_nat hσ.2
    have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
    rw [h_cast] at h_sub
    have h_div : C_id / (2 * (k : ℝ)) ≤ C_id := div_le_self hC_id_nonneg h2k_ge1
    have h_u := h_univ_le hσ
    linarith [(abs_le.mp (h_sub.trans h_div)).2]
  have hrpow_le1 : (2 * (k : ℝ)) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2k_ge1 (by linarith)
  have h_err_le_C :
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤ C_bd :=
    h_err.trans (by nlinarith)
  refine ⟨?_, h_err⟩
  dsimp [M_bd]
  linarith [(abs_le.mp h_err_le_C).2]

/-- **Quantitative Transmuted Lightcone Bootstrap Against `exactTransmutedIdentityPairing`
(Valid for All $\Delta_\phi > 0$ and $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$)**:
For any `LightconeBlockFourPointData` satisfying `HasExactTransmutedCrossingGap Δ_phi`, every
support bound $N \in \mathbb{N}$, and every target exponent
$$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi),$$
there exists $C > 0$ such that for all $k \ge 1$ and all twice-differentiable test functions
$\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi|, |\varphi'|, |\varphi''| \le M_\varphi$:
$$\Bigl|(2k)^{-2\Delta_\phi} L.\text{toTransmutedMonomialFourPointData.pairSpin } (2k)\ \varphi -
  (2k)^{-2\Delta_\phi} \operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)\Bigr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_transmuted_pairSpin_sub_exactIdentity_le {Δ_phi γ : ℝ}
    (hcross : L.HasExactTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := hcross.Δ_phi_pos
  set α : ℝ := min (2 * L.h_gap) (2 * Δ_phi)
  have hα_pos : 0 < α := lt_trans hγ_pos hγ_lt
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγ_lt
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    L.exists_uniform_transmuted_laplaceSpinReal_sub_exactIdentity_bounds hcross
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  let ν : ℕ → Measure ℝ := fun k => exactTransmutedIdentityShiftedMeasure Δ_phi (max k 1)
  let L_ref : ℕ → ℝ → ℝ := fun k σ =>
    (2 * ((max k 1 : ℕ) : ℝ)) ^ (- (2 * Δ_phi)) *
      exactTransmutedIdentityLaplaceReal Δ_phi (2 * max k 1) σ
  let P_ref : ℕ → (ℝ → ℝ) → ℝ := fun k φ =>
    (2 * ((max k 1 : ℕ) : ℝ)) ^ (- (2 * Δ_phi)) *
      exactTransmutedIdentityPairing Δ_phi (2 * max k 1) φ
  obtain ⟨C, hC_pos, hC⟩ :=
    L.toTransmutedMonomialFourPointData.exists_const_abs_rescaled_pairSpin_sub_le
      hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N ν L_ref P_ref
      (fun k => exactTransmutedIdentityShiftedMeasure_compl_intCast_eq_zero Δ_phi (max k 1))
      (fun k _ hσ =>
        integrable_exp_exactTransmutedIdentityShiftedMeasure hΔ_pos (le_max_right k 1) hσ)
      (fun k _ hσ =>
        laplaceTransformReal_exactTransmutedIdentityShiftedMeasure hΔ_pos (le_max_right k 1) hσ)
      (fun k _ _ =>
        mul_nonneg (by positivity)
          (exactTransmutedIdentityLaplaceReal_nonneg hΔ_pos (by omega : 1 ≤ 2 * max k 1) _))
      (fun k _ hφ hsupp =>
        integral_shiftedTest_exactTransmutedIdentityShiftedMeasure hΔ_pos (le_max_right k 1) N
          hφ hsupp)
      (fun {k} hk1 σ hσ => by
        dsimp [L_ref]
        rw [max_eq_left hk1]
        exact h_raw hk1 hσ)
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h_est := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  dsimp [P_ref] at h_est
  rwa [max_eq_left hk1] at h_est

/-- **Quantitative Multi-Trajectory 1D Lightcone-Block Bootstrap Against
`exactTransmutedIdentityPairing` (Valid for All $\Delta_\phi > 0$, All $h_{\text{gap}} > 0$, and
All $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$)**: -/
theorem exists_const_abs_muLC_sub_exactIdentity_le {Δ_phi γ : ℝ}
    (hcross : L.HasExactTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h ∂(L.muLC (2 * (k : ℤ)))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_transmuted_pairSpin_sub_exactIdentity_le hcross hγ_pos hγ_lt N
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℤ) ≤ 2 * (k : ℤ) := by omega
  have h_pair := L.pairSpin_toTransmutedMonomialFourPointData h2k_ge1 φ
  have h_bound := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  rwa [h_pair] at h_bound

/-- **Quantitative Multi-Trajectory $d$-Dimensional Primary Bootstrap on
$(-\infty, h_{\text{gap}} + 1)$ Against `exactTransmutedIdentityPairing` (Valid for All
$\Delta_\phi > 0$, All $h_{\text{gap}} > 0$, and All
$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$)**: -/
theorem exists_const_abs_primary_sub_exactIdentity_le {Δ_phi γ : ℝ}
    (hcross : L.HasExactTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_transmuted_pairSpin_sub_exactIdentity_le hcross hγ_pos hγ_lt N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_gap hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_pair := L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist h2k_ge1 hsupp_gap
  have h_cast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast] at h_pair
  have h_bound := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  rw [h_pair] at h_bound
  simpa [mul_assoc] using h_bound

/-! ## Section 6: Effective-Gap Monotonicity and Inner-Transmutation Crossing Assembly -/

/-- Replace the twist gap `L.h_gap` by any smaller effective gap `h' ≤ L.h_gap`, preserving
`muLC`, `muPrim`, and `leadingTwistCoeff`. This is the key tool for eliminating resonant
endpoint exponents (such as $2(h_{\text{gap}} - \Delta_\phi) = 1$ or
$2(h_{\text{gap}} - \Delta_\phi) = 0$) whenever the desired polynomial decay rate satisfies
$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$. -/
noncomputable def withGap (h' : ℝ) (hh' : h' ≤ L.h_gap) : LightconeBlockFourPointData where
  muLC := L.muLC
  muPrim := L.muPrim
  leadingTwistCoeff := L.leadingTwistCoeff
  leadingTwistCoeff_pos := L.leadingTwistCoeff_pos
  h_gap := h'
  support_unitary := L.support_unitary
  support_odd_spin := L.support_odd_spin
  integrable_transmute := L.integrable_transmute
  summable_transmute := L.summable_transmute
  muLC_restrict_leadingTwist := fun l hl => by
    have h_sub : Iio (h' + 1) ⊆ Iio (L.h_gap + 1) := Iio_subset_Iio (by linarith)
    calc
      (L.muLC (l : ℤ)).restrict (Iio (h' + 1))
        = ((L.muLC (l : ℤ)).restrict (Iio (L.h_gap + 1))).restrict (Iio (h' + 1)) := by
            rw [Measure.restrict_restrict measurableSet_Iio, Set.inter_eq_left.mpr h_sub]
      _ = (ENNReal.ofReal (L.leadingTwistCoeff l) •
            (L.muPrim l).restrict (Iio (L.h_gap + 1))).restrict (Iio (h' + 1)) := by
            rw [L.muLC_restrict_leadingTwist l hl]
      _ = ENNReal.ofReal (L.leadingTwistCoeff l) •
            (L.muPrim l).restrict (Iio (h' + 1)) := by
            rw [Measure.restrict_smul, Measure.restrict_restrict measurableSet_Iio,
              Set.inter_eq_left.mpr h_sub]

@[simp]
theorem toTransmutedMonomialFourPointData_withGap (h' : ℝ) (hh' : h' ≤ L.h_gap) :
    (L.withGap h' hh').toTransmutedMonomialFourPointData =
      L.toTransmutedMonomialFourPointData :=
  rfl

/-- **Inner-Transmutation Crossing Hypothesis (`HasInnerTransmutedCrossing`)**:
Connects the folded inner-transmutation operator `transmuteOpInner` (from
`TransmutedEndpointBounds.lean`) to the exact transmuted $t$-channel identity projection
`exactTransmutedIdentityProjSpin`:
for every compact negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ and every effective
gap $0 < h' \le h_{\text{gap}}$, there exist uniform constants $M_1, M_2, C_1, C_2, C_{\text{tail}} \ge 0$
such that for all $k \ge 1$ with $\sigma_+ + 1/(2k) \le \sigma_+/2$ and all $\sigma \in [\sigma_-, \sigma_+]$,
there is a twice-differentiable crossed-channel non-identity remainder family $R(\theta, w)$ along
the folded contour $w_r(\theta) = -\frac{1}{2k} + i\theta$ ($\theta \in [-\pi/2, \pi/2]$) satisfying:
1. The left-endpoint ($x \in (0, 1/2]$) and right-endpoint ($x \in (1/2, 1)$) first- and
   second-derivative bounds of `norm_folded_integral_transmuteOpInner_le` with exponent
   $2(h' - \Delta_\phi)$,
2. The folded projection difference
   `fourierProjSpin (2k) (σ + 1/(2k)) (-1/(2k)) - exactTransmutedIdentityProjSpin Δ_phi (2k) (σ + 1/(2k)) (-1/(2k))`
   is bounded by the norm of the folded contour integral of `transmuteOpInner (R θ)` plus an
   outer/endpoint tail $C_{\text{tail}} \bigl((2k)^{-2h'} + (2k)^{-2\Delta_\phi}\bigr)$. -/
structure HasInnerTransmutedCrossing (Δ_phi : ℝ) : Prop where
  Δ_phi_pos : 0 < Δ_phi
  h_gap_pos : 0 < L.h_gap
  exists_inner_remainder_decomp :
    ∀ {h' : ℝ}, 0 < h' → h' ≤ L.h_gap →
    ∀ {σ_minus σ_plus : ℝ}, σ_minus ≤ σ_plus → σ_plus < 0 →
      ∃ (M₁ M₂ C₁ C₂ C_tail : ℝ),
        0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C_tail ∧
        ∀ {k : ℕ}, 1 ≤ k →
          σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 →
          ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
          ∃ R : ℝ → ℂ → ℂ,
            (∀ θ ∈ Icc (-π / 2) (π / 2),
              IntegrableOn
                (fun x : ℝ =>
                  transmuteInnerKernel (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I) x *
                    transmuteInnerDiff (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I) x)
                (Ioo (0 : ℝ) 1) volume) ∧
            (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
              ‖deriv (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤
                M₁) ∧
            (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
              ‖deriv (deriv (R θ))
                (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤ M₂) ∧
            (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
              ‖deriv (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤
                C₁ *
                  (‖1 - Complex.exp (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)‖ + (1 - x)) ^
                    (2 * (h' - Δ_phi) - 1)) ∧
            (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
              ‖deriv (deriv (R θ))
                (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤
                C₂ *
                  (‖1 - Complex.exp (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)‖ + (1 - x)) ^
                    (2 * (h' - Δ_phi) - 2)) ∧
            ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
                (L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ))
                    (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
                  exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ))
                    (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
              ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
                  ((π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
                    Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) *
                      (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)) *
                      transmuteOpInner (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I))‖ +
                C_tail * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)))

/-- Combining `HasInnerTransmutedCrossing`, the folded inner-transmutation theorem
`norm_folded_integral_transmuteOpInner_le`, and the exact projection link
`exists_uniform_bound_exactTransmutedIdentityProjSpinFull_sub_exactTransmutedIdentityProjSpin_real`
yields `(L.withGap h' hh').HasExactTransmutedCrossingGap Δ_phi` for every effective gap
$0 < h' \le h_{\text{gap}}$ with $h' < \Delta_\phi$ (where both non-resonance conditions
$2(h' - \Delta_\phi) \ne 1$ and $2(h' - \Delta_\phi) - 1 \ne -1$ hold automatically because
$2(h' - \Delta_\phi) < 0$). -/
theorem HasInnerTransmutedCrossing.toHasExactTransmutedCrossingGap_withGap
    {Δ_phi h' : ℝ} (hinner : L.HasInnerTransmutedCrossing Δ_phi)
    (hh'_pos : 0 < h') (hh'_le : h' ≤ L.h_gap) (hh'_lt_Δ : h' < Δ_phi) :
    (L.withGap h' hh'_le).HasExactTransmutedCrossingGap Δ_phi where
  Δ_phi_pos := hinner.Δ_phi_pos
  h_gap_pos := hh'_pos
  exists_remainder_bound := by
    intro σ_minus σ_plus hσ_le hσ_plus
    have hΔ : 0 < Δ_phi := hinner.Δ_phi_pos
    have hγ_ne1 : 2 * (h' - Δ_phi) ≠ 1 := by linarith
    have hα_ne : 2 * (h' - Δ_phi) - 1 ≠ -1 := by linarith
    obtain ⟨M₁, M₂, C₁, C₂, C_tail, hM₁, hM₂, hC₁, hC₂, hC_tail, h_decomp⟩ :=
      hinner.exists_inner_remainder_decomp hh'_pos hh'_le hσ_le hσ_plus
    obtain ⟨C_fold, hC_fold_nonneg, h_fold⟩ :=
      norm_folded_integral_transmuteOpInner_le hΔ hh'_pos hγ_ne1 hα_ne hM₁ hM₂ hC₁ hC₂
    obtain ⟨C_out, hC_out_nonneg, hC_out⟩ :=
      exists_uniform_bound_exactTransmutedIdentityProjSpinFull_sub_exactTransmutedIdentityProjSpin_real hΔ
    set k₀ : ℕ := ⌈1 / (-σ_plus)⌉₊ + 1
    set C_large : ℝ := C_fold + C_tail + C_out
    have hC_large_nonneg : 0 ≤ C_large := by positivity
    have h_large : ∀ {k : ℕ}, k₀ ≤ k → ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
          C_large * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by
      intro k hk σ hσ
      have hk1 : 1 ≤ k := by dsimp [k₀] at hk; omega
      have h2k_ge1_nat : 1 ≤ 2 * k := by omega
      have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      have h_neg_pos : 0 < -σ_plus := neg_pos.mpr hσ_plus
      have hk_ge_inv : 1 / (-σ_plus) ≤ (k : ℝ) := by
        have h1 : 1 / (-σ_plus) ≤ (⌈1 / (-σ_plus)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈1 / (-σ_plus)⌉₊ : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast (by dsimp [k₀] at hk; omega : ⌈1 / (-σ_plus)⌉₊ ≤ k)
        exact h1.trans h2
      have hσk : σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 := by
        have h1 : 1 ≤ (k : ℝ) * (-σ_plus) := (div_le_iff₀ h_neg_pos).mp hk_ge_inv
        have h2 : 1 / (2 * (k : ℝ)) ≤ -σ_plus / 2 := by
          rw [div_le_div_iff₀ h2k_pos (by norm_num)]
          linarith
        linarith
      have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
      have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
      have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
      have h_eq :=
        L.toTransmutedMonomialFourPointData.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
      have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
      rw [h_add] at h_eq
      have h_cast_2k_real : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
      have h_cast_2k_int : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
      have h_id_eq :=
        exactTransmutedIdentityProjSpinFull_eq_exactTransmutedIdentityLaplaceReal hΔ h2k_ge1_nat
          (by rwa [h_cast_2k_real])
      rw [h_cast_2k_real, h_cast_2k_int] at h_id_eq
      have h_cast_diff :
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| =
          ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
              L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ))
                (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            (((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
              exactTransmutedIdentityProjSpinFull Δ_phi (2 * (k : ℤ))
                (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))‖ := by
        rw [← h_eq, h_id_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [h_cast_diff]
      obtain ⟨R, h_int, h_d1_left, h_d2_left, h_d1_right, h_d2_right, h_diff⟩ :=
        h_decomp hk1 hσk hσ
      have h_fold_k := h_fold hk1 h_int h_d1_left h_d2_left h_d1_right h_d2_right
      have hb_fold :
          ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
              (L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ))
                  (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
                exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ))
                  (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
            (C_fold + C_tail) *
              ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by
        calc
          _ ≤ ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
                ((π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
                  Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) *
                    (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)) *
                    transmuteOpInner (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I))‖ +
              C_tail * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := h_diff
          _ ≤ C_fold * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) +
              C_tail * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
            add_le_add_left h_fold_k _
          _ = (C_fold + C_tail) *
              ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by ring
      have hb_out := hC_out h2k_ge1_nat (lt_of_le_of_lt hσ.2 hσ_plus) (by rwa [h_cast_2k_real])
      rw [h_cast_2k_real, h_cast_2k_int] at hb_out
      set F_spin := L.toTransmutedMonomialFourPointData.fourierProjSpin (2 * (k : ℤ))
        (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
      set I_spin := exactTransmutedIdentityProjSpin Δ_phi (2 * (k : ℤ))
        (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
      set IF_spin := exactTransmutedIdentityProjSpinFull Δ_phi (2 * (k : ℤ))
        (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
      set scale : ℂ := (((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ)
      have h_split :
          scale * F_spin - scale * IF_spin =
            scale * (F_spin - I_spin) - scale * (IF_spin - I_spin) := by ring
      have h_tri :
          ‖scale * F_spin - scale * IF_spin‖ ≤
            ‖scale * (F_spin - I_spin)‖ + ‖scale * (IF_spin - I_spin)‖ := by
        rw [h_split]
        exact norm_sub_le _ _
      have hr1_nonneg : 0 ≤ (2 * (k : ℝ)) ^ (- (2 * h')) := by positivity
      calc
        ‖scale * F_spin - scale * IF_spin‖
          ≤ (C_fold + C_tail) * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) +
              C_out * (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) :=
            h_tri.trans (add_le_add hb_fold hb_out)
        _ ≤ (C_fold + C_tail) * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) +
              C_out * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) hC_out_nonneg)
        _ = C_large * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by
            dsimp [C_large]; ring
    obtain ⟨C_id, hC_id_nonneg, hC_id⟩ :=
      exists_uniform_bound_exactTransmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
    have h1_exp_pos : 0 < 1 - Real.exp σ_plus :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_plus)
    set U_plus : ℝ :=
      universalPrimaryLeadingCoeff Δ_phi * (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi))
    have h_univ_le : ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        transmutedUniversalLaplaceReal Δ_phi σ ≤ U_plus := by
      intro σ hσ
      have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
      rw [transmutedUniversalLaplaceReal_eq Δ_phi hΔ]
      have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσ_neg.le)
      have h1_sub_ge : 1 - Real.exp σ_plus ≤ 1 - Real.exp σ := by
        linarith [Real.exp_le_exp.mpr hσ.2]
      have hrpow_le : (1 - Real.exp σ) ^ (- (2 * Δ_phi)) ≤
          (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
        Real.rpow_le_rpow_of_nonpos h1_exp_pos h1_sub_ge (by linarith)
      have h1_exp_σ_pos : 0 < 1 - Real.exp σ := by linarith
      calc
        universalPrimaryLeadingCoeff Δ_phi * Real.exp (Δ_phi * σ) *
            (1 - Real.exp σ) ^ (- (2 * Δ_phi))
          ≤ (universalPrimaryLeadingCoeff Δ_phi * 1) *
              (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hexp_le1 (universalPrimaryLeadingCoeff_pos hΔ).le)
              hrpow_le (Real.rpow_pos_of_pos h1_exp_σ_pos _).le
              (mul_pos (universalPrimaryLeadingCoeff_pos hΔ) zero_lt_one).le
        _ = U_plus := by dsimp [U_plus]; ring
    set B_fin : ℝ := ∑ j ∈ Finset.range (k₀ + 1),
      (2 * (j : ℝ)) ^ (- (2 * Δ_phi)) *
        L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (j : ℤ)) σ_plus
    have hB_fin_nonneg : 0 ≤ B_fin :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (by positivity)
          (L.toTransmutedMonomialFourPointData.laplaceSpinReal_nonneg _ _)
    have hU_plus_pos : 0 < U_plus :=
      mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.rpow_pos_of_pos h1_exp_pos _)
    set M_fin : ℝ := B_fin + U_plus + C_id
    have hM_fin_nonneg : 0 ≤ M_fin := by dsimp [M_fin]; positivity
    set C_rem : ℝ := max C_large (M_fin * (2 * (k₀ : ℝ)) ^ (2 * Δ_phi))
    have hC_rem_nonneg : 0 ≤ C_rem := le_trans hC_large_nonneg (le_max_left _ _)
    refine ⟨C_rem, hC_rem_nonneg, fun {k} hk1 {σ} hσ => ?_⟩
    change |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
      C_rem * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)))
    rcases le_or_gt k₀ k with hk_ge | hk_lt
    · exact (h_large hk_ge hσ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
      have h2k_ge1_nat : 1 ≤ 2 * k := by omega
      have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
      have h_mono :=
        L.toTransmutedMonomialFourPointData.laplaceSpinReal_mono (2 * (k : ℤ)) hσ_neg hσ_plus hσ.2
      have h_L_le_B :
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ ≤ B_fin := by
        calc
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ
            ≤ (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
                L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ_plus :=
              mul_le_mul_of_nonneg_left h_mono (by positivity)
          _ ≤ B_fin :=
              Finset.single_le_sum
                (f := fun j : ℕ =>
                  (2 * (j : ℝ)) ^ (- (2 * Δ_phi)) *
                    L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (j : ℤ)) σ_plus)
                (fun j _ => mul_nonneg (by positivity)
                  (L.toTransmutedMonomialFourPointData.laplaceSpinReal_nonneg _ _))
                (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_lt.le))
      have h_id_bd :
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ ≤
            U_plus + C_id := by
        have h_sub := hC_id h2k_ge1_nat hσ.2
        have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
        rw [h_cast] at h_sub
        have h_div : C_id / (2 * (k : ℝ)) ≤ C_id := div_le_self hC_id_nonneg h2k_ge1
        have h_u := h_univ_le hσ
        linarith [(abs_le.mp (h_sub.trans h_div)).2]
      have h_L_nonneg :
          0 ≤ (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ :=
        mul_nonneg (by positivity)
          (L.toTransmutedMonomialFourPointData.laplaceSpinReal_nonneg _ _)
      have h_I_nonneg :
          0 ≤ (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ :=
        mul_nonneg (by positivity) (exactTransmutedIdentityLaplaceReal_nonneg hΔ h2k_ge1_nat σ)
      have h_abs_le_M :
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤ M_fin := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg h_L_nonneg, abs_of_nonneg h_I_nonneg]
        dsimp [M_fin]; linarith
      have h2k_le_2k₀ : 2 * (k : ℝ) ≤ 2 * (k₀ : ℝ) := by
        have : (k : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk_lt.le
        linarith
      have h_rpow_le : (2 * (k : ℝ)) ^ (2 * Δ_phi) ≤ (2 * (k₀ : ℝ)) ^ (2 * Δ_phi) :=
        Real.rpow_le_rpow h2k_pos.le h2k_le_2k₀ (by positivity)
      have h_canc : (2 * (k : ℝ)) ^ (2 * Δ_phi) * (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) = 1 := by
        rw [← Real.rpow_add h2k_pos, add_neg_cancel, Real.rpow_zero]
      have h_one_le :
          1 ≤ (2 * (k₀ : ℝ)) ^ (2 * Δ_phi) * (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) := by
        rw [← h_canc]
        exact mul_le_mul_of_nonneg_right h_rpow_le (by positivity)
      have hr_gap_nonneg : 0 ≤ (2 * (k : ℝ)) ^ (- (2 * h')) := by positivity
      calc
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            exactTransmutedIdentityLaplaceReal Δ_phi (2 * k) σ|
          ≤ M_fin * 1 := by linarith
        _ ≤ M_fin * ((2 * (k₀ : ℝ)) ^ (2 * Δ_phi) * (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
            mul_le_mul_of_nonneg_left h_one_le hM_fin_nonneg
        _ = (M_fin * (2 * (k₀ : ℝ)) ^ (2 * Δ_phi)) * (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) := by ring
        _ ≤ C_rem * (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ C_rem * ((2 * (k : ℝ)) ^ (- (2 * h')) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
            mul_le_mul_of_nonneg_left (by linarith) hC_rem_nonneg

/-- **1D Lightcone-Block Bootstrap Against `exactTransmutedIdentityPairing`
from Inner Transmutation (`HasInnerTransmutedCrossing`)**:
Holds unconditionally for **every** $\Delta_\phi > 0$, **every** $h_{\text{gap}} > 0$ (including
$h_{\text{gap}} = \Delta_\phi$ and $2(h_{\text{gap}} - \Delta_\phi) = 1$), and **every**
$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$ (including $\gamma > 1$ when
$h_{\text{gap}}, \Delta_\phi > 1/2$). -/
theorem exists_const_abs_muLC_sub_exactIdentity_le_of_innerCrossing {Δ_phi γ : ℝ}
    (hinner : L.HasInnerTransmutedCrossing Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (∫ h : ℝ, transmuteWeight (h + ((2 * (k : ℤ) : ℤ) : ℝ)) * φ h ∂(L.muLC (2 * (k : ℤ)))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hγ_lt_h : γ < 2 * L.h_gap := lt_of_lt_of_le hγ_lt (min_le_left _ _)
  have hγ_lt_Δ : γ < 2 * Δ_phi := lt_of_lt_of_le hγ_lt (min_le_right _ _)
  let h' : ℝ := (γ / 2 + min L.h_gap Δ_phi) / 2
  have hh'_pos : 0 < h' := by
    dsimp [h']
    have : 0 < min L.h_gap Δ_phi := lt_min hinner.h_gap_pos hinner.Δ_phi_pos
    positivity
  have hh'_le : h' ≤ L.h_gap := by
    dsimp [h']
    have h1 : min L.h_gap Δ_phi ≤ L.h_gap := min_le_left _ _
    linarith
  have hh'_lt_Δ : h' < Δ_phi := by
    dsimp [h']
    have h2 : min L.h_gap Δ_phi ≤ Δ_phi := min_le_right _ _
    linarith
  have hγ_lt_h' : γ < min (2 * h') (2 * Δ_phi) := by
    refine lt_min ?_ hγ_lt_Δ
    dsimp [h']
    have h1 : γ / 2 < min L.h_gap Δ_phi := lt_min (by linarith) (by linarith)
    linarith
  exact (L.withGap h' hh'_le).exists_const_abs_muLC_sub_exactIdentity_le
    (HasInnerTransmutedCrossing.toHasExactTransmutedCrossingGap_withGap L hinner hh'_pos hh'_le hh'_lt_Δ)
    hγ_pos hγ_lt_h' N

/-- **$d$-Dimensional Primary Bootstrap on $(-\infty, h_{\text{gap}} + 1)$
Against `exactTransmutedIdentityPairing` from Inner Transmutation (`HasInnerTransmutedCrossing`)**:
Holds unconditionally for **every** $\Delta_\phi > 0$, **every** $h_{\text{gap}} > 0$ (including
$h_{\text{gap}} = \Delta_\phi$ and $2(h_{\text{gap}} - \Delta_\phi) = 1$), and **every**
$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$ (including $\gamma > 1$ when
$h_{\text{gap}}, \Delta_\phi > 1/2$). -/
theorem exists_const_abs_primary_sub_exactIdentity_le_of_innerCrossing {Δ_phi γ : ℝ}
    (hinner : L.HasInnerTransmutedCrossing Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          exactTransmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hγ_lt_h : γ < 2 * L.h_gap := lt_of_lt_of_le hγ_lt (min_le_left _ _)
  have hγ_lt_Δ : γ < 2 * Δ_phi := lt_of_lt_of_le hγ_lt (min_le_right _ _)
  let h' : ℝ := (γ / 2 + min L.h_gap Δ_phi) / 2
  have hh'_pos : 0 < h' := by
    dsimp [h']
    have : 0 < min L.h_gap Δ_phi := lt_min hinner.h_gap_pos hinner.Δ_phi_pos
    positivity
  have hh'_le : h' ≤ L.h_gap := by
    dsimp [h']
    have h1 : min L.h_gap Δ_phi ≤ L.h_gap := min_le_left _ _
    linarith
  have hh'_lt_Δ : h' < Δ_phi := by
    dsimp [h']
    have h2 : min L.h_gap Δ_phi ≤ Δ_phi := min_le_right _ _
    linarith
  have hγ_lt_h' : γ < min (2 * h') (2 * Δ_phi) := by
    refine lt_min ?_ hγ_lt_Δ
    dsimp [h']
    have h1 : γ / 2 < min L.h_gap Δ_phi := lt_min (by linarith) (by linarith)
    linarith
  obtain ⟨C, hC_pos, hC⟩ :=
    (L.withGap h' hh'_le).exists_const_abs_transmuted_pairSpin_sub_exactIdentity_le
      (HasInnerTransmutedCrossing.toHasExactTransmutedCrossingGap_withGap L hinner hh'_pos hh'_le hh'_lt_Δ)
      hγ_pos hγ_lt_h' N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_gap hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_pair := L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist h2k_ge1 hsupp_gap
  have h_cast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast] at h_pair
  have h_bound := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  rw [toTransmutedMonomialFourPointData_withGap, h_pair] at h_bound
  simpa [mul_assoc] using h_bound

end LightconeBlockFourPointData

end CFT.LightconeBootstrap
