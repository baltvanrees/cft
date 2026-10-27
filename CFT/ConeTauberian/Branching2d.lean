/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Transmute1d
import CFT.LightconeBootstrap.RealLaplaceBound
import CFT.Gegenbauers

/-!
# 2D Conformal Blocks, Bilateral Transmutation, and $d \to 2$ Branching Coefficients

This file formalizes Phase 2 of `CFT/ConeTauberian/PLAN.md`:
1. **2D Conformal Blocks & Bilateral Transmutation ($\mathcal{L}_0 \otimes \mathcal{L}_0$)**:
   - `block2dChiral hl hr wl wr`: the unsymmetrized 2D chiral conformal block product
     `block1d hl wl * block1d hr wr`.
   - `block2d Δ j wl wr`: the symmetrized 2D conformal block of scaling dimension `Δ`
     and spin `j`.
   - `transmuteOp2d`: the bilateral 1D transmutation operator
     $\mathcal{L}_0^{(w_l)} \otimes \mathcal{L}_0^{(w_r)}$.
   - `transmuteOp2d_block2dChiral` and `transmuteOp2d_block2d`: exact collapse of 2D conformal
     blocks on `UcDisk` into pure two-variable exponentials weighted by
     `transmuteWeight hl * transmuteWeight hr`.

2. **Gegenbauer-to-2D Spin Coefficients & Transverse Shift Binomial Identity**:
   - `gegSpinCoeff ν l m`: the angular expansion coefficients of the Gegenbauer polynomial
     $C_\ell^{(\nu)}(\cos\theta)$ into 2D spin harmonics.
   - `gegenbauer_eval_Trigger_eq_sum_gegSpinCoeff`: connection to `gegenbauer` via
     `geg_two_var_explicit`.
   - `hasSum_transverseShift`: the binomial resummation identity
     $\sum_{k=0}^\infty \operatorname{pochhammerCoeff}(\nu - 1/2, k) (1 - \xi^2)^k = \xi^{1 - 2\nu}$
     for $\xi \in (0, 1)$.

3. **Quantitative $O(\Delta^{-1})$ Stirling Convergence**:
   - `exists_abs_rpow_mul_gegSpinCoeff_sub_inv_gamma_sq_le`: uniform $O(m^{-1} + (\ell - m)^{-1})$
     Stirling approximation for `gegSpinCoeff ν l m`.
   - `exists_abs_rpow_mul_transmuteWeight_nat_sub_one_le`: uniform $O(n^{-1})$ Stirling
     approximation for `transmuteWeight n`.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal
open CFT.LightconeBootstrap

namespace CFT.ConeTauberian

/-!
## 1. 2D Conformal Blocks & Bilateral Transmutation ($\mathcal{L}_0 \otimes \mathcal{L}_0$)
-/

/-- The unsymmetrized 2D chiral conformal block product for left/right collinear weights
`hl hr : ℝ`:
$$\operatorname{block2dChiral}(h_l, h_r, w_l, w_r) =
  \operatorname{block1d}(h_l, w_l) \operatorname{block1d}(h_r, w_r).$$ -/
noncomputable def block2dChiral (hl hr : ℝ) (wl wr : ℂ) : ℂ :=
  block1d hl wl * block1d hr wr

/-- The symmetrized 2D conformal block for scaling dimension `Δ : ℝ` and 2D spin `j : ℕ`:
$$\operatorname{block2d}(\Delta, j, w_l, w_r) =
  \frac{1}{1 + \delta_{j, 0}} \left[
    \operatorname{block2dChiral}\!\left(\frac{\Delta - j}{2}, \frac{\Delta + j}{2}, w_l, w_r\right)
    + \operatorname{block2dChiral}\!\left(
        \frac{\Delta + j}{2}, \frac{\Delta - j}{2}, w_l, w_r\right)
  \right].$$ -/
noncomputable def block2d (Δ : ℝ) (j : ℕ) (wl wr : ℂ) : ℂ :=
  ((1 + (if j = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)⁻¹ *
    (block2dChiral ((Δ - (j : ℝ)) / 2) ((Δ + (j : ℝ)) / 2) wl wr +
     block2dChiral ((Δ + (j : ℝ)) / 2) ((Δ - (j : ℝ)) / 2) wl wr)

/-- The bilateral 1D transmutation operator $\mathcal{L}_0^{(w_l)} \otimes \mathcal{L}_0^{(w_r)}$:
applies `transmuteOp` in the right variable `wr` and then in the left variable `wl`. -/
noncomputable def transmuteOp2d (F : ℂ → ℂ → ℂ) (wl wr : ℂ) : ℂ :=
  transmuteOp (fun zl => transmuteOp (fun zr => F zl zr) wr) wl

/-- Action of `transmuteOp` on a two-term linear combination of 1D conformal blocks on `UcDisk`. -/
lemma transmuteOp_add_const_mul_block1d (c1 c2 : ℂ) {H1 H2 : ℝ}
    (hH1 : 1 / 2 < H1) (hH2 : 1 / 2 < H2) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOp (fun z => c1 * block1d H1 z + c2 * block1d H2 z) w =
      c1 * (transmuteWeight H1 : ℂ) * Complex.exp ((H1 : ℂ) * w) +
      c2 * (transmuteWeight H2 : ℂ) * Complex.exp ((H2 : ℂ) * w) := by
  have hH : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 1 / 2 < (![H1, H2] i) := by
    intro i _
    fin_cases i
    · simpa using hH1
    · simpa using hH2
  have h_sum := transmuteOp_finset_sum_block1d (Finset.univ : Finset (Fin 2))
    ![c1, c2] ![H1, H2] hH hw
  simpa [Fin.sum_univ_two] using h_sum

/-- **Exact bilateral transmutation identity on `block2dChiral`**:
for `hl > 1/2`, `hr > 1/2`, and `wl, wr ∈ UcDisk`,
$$\operatorname{transmuteOp2d}(\operatorname{block2dChiral} h_l h_r)(w_l, w_r) =
  \operatorname{transmuteWeight}(h_l) \operatorname{transmuteWeight}(h_r)
  e^{h_l w_l + h_r w_r}.$$ -/
theorem transmuteOp2d_block2dChiral {hl hr : ℝ} (hhl : 1 / 2 < hl) (hhr : 1 / 2 < hr)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    transmuteOp2d (block2dChiral hl hr) wl wr =
      ((transmuteWeight hl * transmuteWeight hr : ℝ) : ℂ) *
        Complex.exp ((hl : ℂ) * wl + (hr : ℂ) * wr) := by
  dsimp [transmuteOp2d, block2dChiral]
  have h_inner : (fun zl => transmuteOp (fun zr => block1d hl zl * block1d hr zr) wr) =
      fun zl => ((transmuteWeight hr : ℂ) * Complex.exp ((hr : ℂ) * wr)) * block1d hl zl := by
    ext zl
    rw [transmuteOp_const_mul, transmuteOp_block1d hhr hwr]
    ring
  rw [h_inner, transmuteOp_const_mul, transmuteOp_block1d hhl hwl, Complex.exp_add]
  push_cast
  ring

/-- **Exact bilateral transmutation identity on `block2d`**:
for `(Δ - j) / 2 > 1/2` and `wl, wr ∈ UcDisk`, `transmuteOp2d` collapses `block2d Δ j` into
a symmetrized sum of two exponentials weighted by
`transmuteWeight ((Δ - j) / 2) * transmuteWeight ((Δ + j) / 2)`. -/
theorem transmuteOp2d_block2d {Δ : ℝ} {j : ℕ} (hΔj : 1 / 2 < (Δ - (j : ℝ)) / 2)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    transmuteOp2d (block2d Δ j) wl wr =
      ((1 + (if j = 0 then (1 : ℝ) else 0))⁻¹ *
        transmuteWeight ((Δ - (j : ℝ)) / 2) *
        transmuteWeight ((Δ + (j : ℝ)) / 2) : ℂ) *
        (Complex.exp ((((Δ - (j : ℝ)) / 2 : ℝ) : ℂ) * wl +
           (((Δ + (j : ℝ)) / 2 : ℝ) : ℂ) * wr) +
         Complex.exp ((((Δ + (j : ℝ)) / 2 : ℝ) : ℂ) * wl +
           (((Δ - (j : ℝ)) / 2 : ℝ) : ℂ) * wr)) := by
  set hl : ℝ := (Δ - (j : ℝ)) / 2
  set hr : ℝ := (Δ + (j : ℝ)) / 2
  set c : ℂ := ((1 + (if j = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)⁻¹
  have hhr : 1 / 2 < hr := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    dsimp [hl, hr] at hΔj ⊢
    linarith
  dsimp [transmuteOp2d, block2d, block2dChiral]
  have h_inner :
      (fun zl => transmuteOp
        (fun zr => c * (block1d hl zl * block1d hr zr + block1d hr zl * block1d hl zr)) wr) =
      fun zl =>
        (c * (transmuteWeight hr : ℂ) * Complex.exp ((hr : ℂ) * wr)) * block1d hl zl +
        (c * (transmuteWeight hl : ℂ) * Complex.exp ((hl : ℂ) * wr)) * block1d hr zl := by
    ext zl
    have h_fn :
        (fun zr => c * (block1d hl zl * block1d hr zr + block1d hr zl * block1d hl zr)) =
        fun zr => (c * block1d hl zl) * block1d hr zr + (c * block1d hr zl) * block1d hl zr := by
      ext zr; ring
    rw [h_fn, transmuteOp_add_const_mul_block1d _ _ hhr hΔj hwr]
    ring
  rw [h_inner, transmuteOp_add_const_mul_block1d _ _ hΔj hhr hwl]
  rw [Complex.exp_add, Complex.exp_add]
  dsimp [c]
  push_cast
  ring

/-!
## 2. Gegenbauer-to-2D Spin Coefficients & Transverse Shift Binomial Identity
-/

/-- The unsymmetrized Gegenbauer angular coefficient
$$\operatorname{gegSpinCoeff}(\nu, \ell, m) :=
  \frac{(\nu)_m}{m!} \frac{(\nu)_{\ell - m}}{(\ell - m)!}.$$ -/
noncomputable def gegSpinCoeff (ν : ℝ) (l m : ℕ) : ℝ :=
  pochhammerCoeff ν m * pochhammerCoeff ν (l - m)

lemma gegenbauer_ph_ofReal (ν : ℝ) (a : ℕ) :
    gegenbauer.ph (ν : ℂ) a = (realPochhammer ν a : ℂ) := by
  induction a with
  | zero => simp [gegenbauer.ph, realPochhammer]
  | succ k ih =>
    have h_succ : gegenbauer.ph (ν : ℂ) (k + 1) =
        gegenbauer.ph (ν : ℂ) k * ((ν : ℂ) + (k : ℂ)) := by
      rw [gegenbauer.ph, gegenbauer.ph, ascPochhammer_succ_eval]
    rw [h_succ, ih, realPochhammer_succ]
    push_cast
    rfl

lemma geg_two_var_coeff_ofReal (ν : ℝ) (l m : ℕ) :
    gegenbauer.geg_two_var_coeff (ν : ℂ) l m = (gegSpinCoeff ν l m : ℂ) := by
  dsimp [gegenbauer.geg_two_var_coeff, gegenbauer.fact, gegSpinCoeff, pochhammerCoeff]
  rw [gegenbauer_ph_ofReal, gegenbauer_ph_ofReal]
  push_cast
  ring

/-- Expansion of the Gegenbauer polynomial $C_\ell^{(\nu)}\bigl((r + r^{-1})/2\bigr)$ into
monomials $r^{\ell - m} (r^{-1})^m$ with coefficients `gegSpinCoeff ν l m`. -/
lemma gegenbauer_eval_Trigger_eq_sum_gegSpinCoeff (ν : ℝ) (l : ℕ) (r : ℂ) (hr : r ≠ 0) :
    (gegenbauer (ν : ℂ) l).eval ((r + r⁻¹) / 2) =
      ∑ m ∈ Finset.range (l + 1),
        (gegSpinCoeff ν l m : ℂ) * r ^ (l - m) * (r⁻¹) ^ m := by
  have h_expl := gegenbauer.geg_two_var_explicit (ν : ℂ) 1 r l one_ne_zero hr
  have h_arg : (1 / r + r / 1) / 2 = (r + r⁻¹) / 2 := by ring
  rw [one_mul, h_arg, one_pow] at h_expl
  have h_rl_ne : r ^ l ≠ 0 := pow_ne_zero l hr
  apply mul_left_cancel₀ h_rl_ne
  rw [h_expl]
  dsimp [gegenbauer.geg_two_var_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have hm_le : m ≤ l := Nat.lt_succ_iff.mp hm
  rw [geg_two_var_coeff_ofReal, one_pow, mul_one]
  have h_pow : r ^ l * (r ^ (l - m) * (r⁻¹) ^ m) = (r ^ 2) ^ (l - m) := by
    have h_rl : r ^ l = r ^ (l - m) * r ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm_le]
    have h_cancel : r ^ m * (r⁻¹) ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hr, one_pow]
    rw [h_rl]
    calc
      r ^ (l - m) * r ^ m * (r ^ (l - m) * (r⁻¹) ^ m)
        = (r ^ (l - m) * r ^ (l - m)) * (r ^ m * (r⁻¹) ^ m) := by ring
      _ = (r ^ 2) ^ (l - m) * 1 := by rw [h_cancel, sq, mul_pow]
      _ = (r ^ 2) ^ (l - m) := mul_one _
  calc
    (gegSpinCoeff ν l m : ℂ) * (r ^ 2) ^ (l - m)
      = (gegSpinCoeff ν l m : ℂ) * (r ^ l * (r ^ (l - m) * (r⁻¹) ^ m)) := by rw [h_pow]
    _ = r ^ l * ((gegSpinCoeff ν l m : ℂ) * r ^ (l - m) * (r⁻¹) ^ m) := by ring

/-- **Transverse Shift Binomial Resummation Identity**:
for any $\nu \in \mathbb{R}$ and $\xi \in (0, 1)$,
$$\sum_{k=0}^\infty \operatorname{pochhammerCoeff}(\nu - 1/2, k) (1 - \xi^2)^k
  = \xi^{1 - 2\nu}.$$ -/
theorem hasSum_transverseShift (ν : ℝ) {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => pochhammerCoeff (ν - 1 / 2) k * (1 - ξ ^ 2) ^ k)
      (ξ ^ (1 - 2 * ν)) := by
  have hξ_sq_pos : 0 < ξ ^ 2 := sq_pos_of_pos hξ.1
  have hξ_sq_lt : ξ ^ 2 < 1 := by nlinarith [hξ.1, hξ.2]
  have h_abs : |1 - ξ ^ 2| < 1 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have h_sum := hasSum_one_sub_rpow_neg (ν - 1 / 2) h_abs
  have h_rhs : (1 - (1 - ξ ^ 2)) ^ (- (ν - 1 / 2)) = ξ ^ (1 - 2 * ν) := by
    have h_sub : 1 - (1 - ξ ^ 2) = ξ ^ (2 : ℝ) := by
      rw [sub_sub_cancel, Real.rpow_two]
    rw [h_sub, ← Real.rpow_mul hξ.1.le]
    congr 1
    ring
  rwa [h_rhs] at h_sum

/-!
## 3. Quantitative $O(\Delta^{-1})$ Stirling Convergence of `transmuteWeight` and `gegSpinCoeff`
-/

/-- **Uniform $O(m^{-1} + (\ell - m)^{-1})$ Product Stirling Bound for `gegSpinCoeff`**:
for $\nu > 0$, there exists $C > 0$ such that for all $\ell, m \in \mathbb{N}$ with
$1 \le m$ and $1 \le \ell - m$,
$$\left|\bigl(m(\ell - m)\bigr)^{1 - \nu} \operatorname{gegSpinCoeff}(\nu, \ell, m)
  - \frac{1}{\Gamma(\nu)^2}\right|
  \le C \left(\frac{1}{m} + \frac{1}{\ell - m}\right).$$ -/
theorem exists_abs_rpow_mul_gegSpinCoeff_sub_inv_gamma_sq_le {ν : ℝ} (hν : 0 < ν) :
    ∃ C > 0, ∀ {l m : ℕ}, 1 ≤ m → 1 ≤ l - m →
      |((m : ℝ) * ((l - m : ℕ) : ℝ)) ^ (1 - ν) * gegSpinCoeff ν l m -
        ((Real.Gamma ν) ^ 2)⁻¹| ≤
        C * ((m : ℝ)⁻¹ + ((l - m : ℕ) : ℝ)⁻¹) := by
  obtain ⟨C0, hC0_nonneg, hC0⟩ := exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le hν
  set g : ℝ := (Real.Gamma ν)⁻¹
  have hg_pos : 0 < g := inv_pos.mpr (Real.Gamma_pos_of_pos hν)
  refine ⟨(C0 + g) * C0 + 1, by positivity, fun {l m} hm hlm => ?_⟩
  set A : ℝ := (m : ℝ) ^ (1 - ν) * pochhammerCoeff ν m
  set B : ℝ := ((l - m : ℕ) : ℝ) ^ (1 - ν) * pochhammerCoeff ν (l - m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlm_pos : (0 : ℝ) < ((l - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < l - m)
  have hlm_ge_one : (1 : ℝ) ≤ ((l - m : ℕ) : ℝ) := by exact_mod_cast hlm
  have h_prod : ((m : ℝ) * ((l - m : ℕ) : ℝ)) ^ (1 - ν) * gegSpinCoeff ν l m = A * B := by
    dsimp [gegSpinCoeff, A, B]
    rw [Real.mul_rpow hm_pos.le hlm_pos.le]
    ring
  have h_gsq : ((Real.Gamma ν) ^ 2)⁻¹ = g * g := by
    dsimp [g]
    rw [sq, mul_inv]
  have hA : |A - g| ≤ C0 * (m : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv] using hC0 hm
  have hB : |B - g| ≤ C0 * ((l - m : ℕ) : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv] using hC0 hlm
  have hlm_inv_le : ((l - m : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlm_ge_one
  have hB_abs : |B| ≤ C0 + g := by
    have h1 : |B| ≤ |B - g| + |g| := by
      simpa using abs_add_le (B - g) g
    rw [abs_of_pos hg_pos] at h1
    have h2 : C0 * ((l - m : ℕ) : ℝ)⁻¹ ≤ C0 * 1 :=
      mul_le_mul_of_nonneg_left hlm_inv_le hC0_nonneg
    linarith
  have h_decomp : A * B - g * g = (A - g) * B + g * (B - g) := by ring
  rw [h_prod, h_gsq, h_decomp]
  have h_tri : |(A - g) * B + g * (B - g)| ≤ |A - g| * |B| + g * |B - g| := by
    calc
      |(A - g) * B + g * (B - g)| ≤ |(A - g) * B| + |g * (B - g)| := abs_add_le _ _
      _ = |A - g| * |B| + g * |B - g| := by
        rw [abs_mul (A - g) B, abs_mul g (B - g), abs_of_pos hg_pos]
  have h_term1 : |A - g| * |B| ≤ ((C0 + g) * C0 + 1) * (m : ℝ)⁻¹ := by
    have h1 : |A - g| * |B| ≤ (C0 * (m : ℝ)⁻¹) * (C0 + g) :=
      mul_le_mul hA hB_abs (abs_nonneg B) (by positivity)
    have h2 : (C0 * (m : ℝ)⁻¹) * (C0 + g) = ((C0 + g) * C0) * (m : ℝ)⁻¹ := by ring
    have h3 : ((C0 + g) * C0) * (m : ℝ)⁻¹ ≤ ((C0 + g) * C0 + 1) * (m : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hm_pos.le)
    linarith
  have h_term2 : g * |B - g| ≤ ((C0 + g) * C0 + 1) * ((l - m : ℕ) : ℝ)⁻¹ := by
    have h1 : g * |B - g| ≤ g * (C0 * ((l - m : ℕ) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hB hg_pos.le
    have h2 : g * C0 ≤ (C0 + g) * C0 + 1 := by nlinarith
    have h3 : (g * C0) * ((l - m : ℕ) : ℝ)⁻¹ ≤
        ((C0 + g) * C0 + 1) * ((l - m : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hlm_pos.le)
    linarith
  linarith

/-- Expresses `transmuteWeight (n : ℝ)` for $n \ge 1$ in terms of `pochhammerCoeff (1 / 2) n`. -/
lemma transmuteWeight_nat_eq_mul_pochhammerCoeff {n : ℕ} (hn : 1 ≤ n) :
    transmuteWeight (n : ℝ) =
      ((n : ℝ) - 1 / 2) * (n : ℝ) * Real.Gamma (1 / 2) * pochhammerCoeff (1 / 2) n := by
  dsimp [transmuteWeight, pochhammerCoeff]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h_gamma_half : Real.Gamma ((n : ℝ) + 1 / 2) =
      Real.Gamma (1 / 2) * realPochhammer (1 / 2) n := by
    rw [add_comm (n : ℝ) (1 / 2)]
    exact Gamma_add_nat_eq_mul_realPochhammer (by norm_num) n
  have h_fact : (Nat.factorial n : ℝ) = (n : ℝ) * Real.Gamma (n : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial n, Real.Gamma_add_one hn_pos.ne']
  have h_gamma_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn_pos
  rw [h_gamma_half, h_fact]
  field_simp [hn_pos.ne', h_gamma_pos.ne']

/-- **Uniform $O(n^{-1})$ Stirling Bound for `transmuteWeight (n : ℝ)`**:
there exists $C > 0$ such that for all $n \ge 1$,
$$\left|n^{-3/2} \operatorname{transmuteWeight}(n) - 1\right| \le \frac{C}{n}.$$ -/
theorem exists_abs_rpow_mul_transmuteWeight_nat_sub_one_le :
    ∃ C > 0, ∀ {n : ℕ}, 1 ≤ n →
      |(n : ℝ) ^ (- (3 / 2 : ℝ)) * transmuteWeight (n : ℝ) - 1| ≤ C / (n : ℝ) := by
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le (by norm_num : (0 : ℝ) < 1 / 2)
  set g : ℝ := Real.Gamma (1 / 2)
  have hg_pos : 0 < g := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨g * C0 + 1 / 2, by positivity, fun {n} hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set U : ℝ := (n : ℝ) ^ (1 - (1 / 2 : ℝ)) * pochhammerCoeff (1 / 2) n
  set x : ℝ := 1 / (2 * (n : ℝ))
  have h_rpow : (n : ℝ) ^ (- (3 / 2 : ℝ)) * (((n : ℝ) - 1 / 2) * (n : ℝ)) =
      (1 - x) * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    have h_factor : ((n : ℝ) - 1 / 2) * (n : ℝ) = (1 - x) * (n : ℝ) ^ (2 : ℝ) := by
      dsimp [x]
      rw [Real.rpow_two]
      field_simp [hn_pos.ne']
    rw [h_factor, ← mul_assoc, mul_comm ((n : ℝ) ^ (- (3 / 2 : ℝ))) (1 - x), mul_assoc,
      ← Real.rpow_add hn_pos]
    congr 2
    ring
  have h_lhs : (n : ℝ) ^ (- (3 / 2 : ℝ)) * transmuteWeight (n : ℝ) - 1 =
      (1 - x) * g * (U - g⁻¹) - x := by
    rw [transmuteWeight_nat_eq_mul_pochhammerCoeff hn]
    have h_rearr :
        (n : ℝ) ^ (- (3 / 2 : ℝ)) *
          (((n : ℝ) - 1 / 2) * (n : ℝ) * g * pochhammerCoeff (1 / 2) n) =
        ((n : ℝ) ^ (- (3 / 2 : ℝ)) * (((n : ℝ) - 1 / 2) * (n : ℝ))) *
          (g * pochhammerCoeff (1 / 2) n) := by ring
    rw [h_rearr, h_rpow]
    have h_U : (1 - x) * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) * (g * pochhammerCoeff (1 / 2) n) =
        (1 - x) * g * U := by
      dsimp [U]; ring
    rw [h_U]
    have h_ginv : g * g⁻¹ = 1 := mul_inv_cancel₀ hg_pos.ne'
    linear_combination (1 - x) * h_ginv
  rw [h_lhs]
  have hx_pos : 0 < x := by dsimp [x]; positivity
  have hx_le : x ≤ 1 / 2 := by
    dsimp [x]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h1x_abs : |1 - x| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hU_bound : |U - g⁻¹| ≤ C0 / (n : ℝ) := hC0 hn
  have h_tri : |(1 - x) * g * (U - g⁻¹) - x| ≤ |1 - x| * g * |U - g⁻¹| + |x| := by
    calc
      |(1 - x) * g * (U - g⁻¹) - x| ≤ |(1 - x) * g * (U - g⁻¹)| + |x| := by
        simpa [sub_eq_add_neg] using abs_add_le ((1 - x) * g * (U - g⁻¹)) (-x)
      _ = |1 - x| * g * |U - g⁻¹| + |x| := by
        rw [abs_mul ((1 - x) * g) (U - g⁻¹), abs_mul (1 - x) g, abs_of_pos hg_pos]
  rw [abs_of_pos hx_pos] at h_tri
  have h_prod_le : |1 - x| * g * |U - g⁻¹| ≤ 1 * g * (C0 / (n : ℝ)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_right h1x_abs hg_pos.le) hU_bound (abs_nonneg _) ?_
    positivity
  have hx_eq : x = (1 / 2) / (n : ℝ) := by dsimp [x]; ring
  calc
    |(1 - x) * g * (U - g⁻¹) - x| ≤ 1 * g * (C0 / (n : ℝ)) + x := by linarith
    _ = (g * C0 + 1 / 2) / (n : ℝ) := by rw [hx_eq]; ring

end CFT.ConeTauberian
