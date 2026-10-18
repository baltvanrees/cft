# Monomial Lightcone Bootstrap (Plan)

## 1. Goal & Mathematical Overview

As a first major milestone, we formalize the **monomial lightcone bootstrap**: every four-point correlation function `FourPointData ν Δ_phi` admits a monomial expansion on $\operatorname{UcPdisk}$ with non-negative spectral density over $(h, J) \in \mathbb{R} \times \mathbb{Z}$, and in any theory with a twist gap, the **individual large-spin limit $J \to \infty$ (for even $J$)** of the spin-$J$ spectral density integrated against a compactly supported test function $\varphi(h)$ is universal—without needing to average over spins $J$ via a Tauberian theorem.

### Key Idea: Double Contour Integral on $\operatorname{UcPdisk}$ & Combined $s$-/$t$-Channel Control

1. **Monomial Decomposition on $\operatorname{UcPdisk}$**:
   Expanding each conformal block into monomials $\rho_l^h \rho_r^{\bar{h}} = e^{h w_l + \bar{h} w_r}$ with $\bar{h} = h + J$ ($J \in \mathbb{Z}$ even) yields a non-negative spectral measure $d\mu(h, J) = \sum_{J \in \mathbb{Z}} d\mu_J(h)$ such that for $(w_l, w_r) \in \operatorname{UcPdisk}$:
   $$\mathcal{G}_{\text{pdisk}}(w_l, w_r) = \sum_{J \in \mathbb{Z}} \int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h).$$

2. **Pairing with a Compactly Supported Smooth Test Function $\varphi(h)$ & Halving the $\theta$-Contour to $[-\pi/2, \pi/2]$**:
   - Let $\varphi(h)$ be a **compactly supported** (and sufficiently smooth) test function of $h$ (independent of $J$). Compact support in $h$ is essential both for obtaining the sharpest possible local statement in $h$ and so that the Laplace–Fourier transform
     $$\widehat{\varphi}_{\sigma}(t) := \int_{\mathbb{R}} \varphi(h) \, e^{-h (\sigma + i t)} \, dh$$
     is well-defined for all $\sigma \in \mathbb{R}$ and decays rapidly as $\|t\| \to \infty$ (faster decay can be achieved by requiring higher smoothness of $\varphi$).
   - By combining the inverse Fourier transform in $\theta \in [-\pi, \pi]$ (which projects onto spin $J$) with the inverse Fourier/Laplace transform in $t \in \mathbb{R}$ (which integrates against $\varphi(h)$), the pairing $\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h)$ becomes a double integral over $(t, \theta) \in \mathbb{R} \times [-\pi, \pi]$ along $(w_l, w_r) = (\sigma_l + i(t - \theta),\, \sigma_r + i\theta) \in \operatorname{UcPdisk}$ with $\sigma = \sigma_l + \sigma_r$.
   - **$t$-channel vs. $u$-channel & halving the $\theta$-interval**:
     - On $[-\pi, \pi]$, $\theta = 0$ ($\rho_r \to 1^-, z_r \to 1^-$) is the **$t$-channel lightcone limit**, whereas $\theta = \pm \pi$ ($\rho_r \to -1^+, z_r \to -\infty$ along the negative real branch cut) is the **$u$-channel lightcone limit**.
     - Because identical external scalars have only **even spins $J \in 2\mathbb{Z}$** in their monomial decomposition (coming from even primary spins $l$ in `FourPointData.support_even_spin` and even $\rho$-expansion levels $n$ in `ConformalBlock.A_odd_level`), we have $e^{i J \pi} = 1$, so $\mathcal{G}_{\text{pdisk}}(w_l - i\theta, w_r + i\theta)$ is **$\pi$-periodic in $\theta$** ($t \leftrightarrow u$ channel symmetry $\rho \mapsto -\rho$).
     - Consequently, for any even spin $J \in 2\mathbb{Z}$, the $u$-channel region $[-\pi, -\pi/2] \cup [\pi/2, \pi]$ is identical to the $t$-channel region $[-\pi/2, \pi/2]$, and the double integral folds onto the half-interval $\theta \in [-\pi/2, \pi/2]$:
       $$\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h)
         = \int_{-\infty}^{\infty} \frac{dt}{2\pi} \, \widehat{\varphi}_{\sigma}(t)
           \int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \, e^{-J (\sigma_r + i\theta)} \,
           \mathcal{G}_{\text{pdisk}}\bigl(\sigma_l + i(t - \theta),\, \sigma_r + i\theta\bigr).$$
     - On $\theta \in [-\pi/2, \pi/2]$, $\operatorname{Re}(e^{\sigma_r + i\theta}) \ge 0$, which stays completely away from the $u$-channel branch cut $\rho \in (-1, 0)$ ($z \in (-\infty, 0)$ outside `CutPlane`). Thus **only $t$-channel crossing (`crossing_correlator`) and the $t$-channel identity operator at $\theta = 0$ are ever needed**.
   - Because the integral is independent of $(\sigma_l, \sigma_r)$ with $\sigma_l < 0, \sigma_r < 0$, we choose a **$J$-dependent contour** $(\sigma_l(J), \sigma_r(J))$ pushed toward the $t$-channel lightcone as $J \to \infty$.

3. **Controlling the $J$-Dependent Contour via $t$-Channel Expansion, $s$-Channel Positivity, and Vitali's Theorem**:
   - **Two-variable $t$-channel crossing symmetry** (`FourPointData.crossing_correlator` in `CFT/Corr_pdisk.lean`, outside this folder) equates the $s$-channel and $t$-channel expansions on $\text{CutPlane} \times \text{CutPlane}$.
   - **$t$-channel dominance**: The $t$-channel conformal block / monomial decomposition converges in a large domain containing the $\theta \approx 0$ region of $[-\pi/2, \pi/2]$, and in a theory with a twist gap $h \ge h_{\text{gap}} > 0$ above the identity $(h, J) = (0, 0)$, the $t$-channel identity operator dominates near $\theta = 0$.
   - **$s$-channel positivity bound**: For any parts of the $(t, \theta) \in \mathbb{R} \times [-\pi/2, \pi/2]$ contour not directly controlled by the $t$-channel expansion (such as away from $\theta = 0$ or at large $\|t\|$), positivity of the $s$-channel expansion coefficients immediately implies that increasing $\|\operatorname{Im}(w_l)\|$ or $\|\operatorname{Im}(w_r)\|$ never increases $\|\mathcal{G}_{\text{pdisk}}\|$:
     $$\|\mathcal{G}_{\text{pdisk}}(w_l, w_r)\| \le \mathcal{G}_{\text{pdisk}}(\operatorname{Re}(w_l), \operatorname{Re}(w_r)).$$
   - **Vitali's theorem & large-$\|t\|$ control**: Combining the $s$-channel positivity bound with Vitali's theorem and the rapid large-$\|t\|$ decay of $\widehat{\varphi}_{\sigma}(t)$ controls the tails and upgrades the $t$-channel identity dominance to show that as $J \to \infty$ (for even $J$), the $t$-channel identity operator dominates the folded double contour integral over $\mathbb{R} \times [-\pi/2, \pi/2]$.

---

## 2. Folder & File Structure

Two-variable crossing symmetry lives in `CFT/Corr_pdisk.lean` (outside this folder), while the monomial decomposition and large-$J$ lightcone bootstrap live in `CFT/MonomialBootstrap/`:

```text
CFT/Corr_pdisk.lean  (includes general two-variable crossing symmetry `crossing_correlator`)
       │
       ▼
CFT/MonomialBootstrap/
  ├── PLAN.md
  ├── MonomialDecomp.lean  (MonomialFourPointData, even-spin π-periodicity, s-channel positivity, & construction from FourPointData)
  ├── FourierProj.lean     (Spin-J spectral density μ_J, test functions φ(h), & folded double integral on ℝ × [-π/2, π/2] — 0 sorry's)
  ├── Gap.lean             (Twist-gap axiom, t-channel identity dominance, and cross-channel error bounds — 0 sorry's)
  ├── IdentityProj.lean    (t-channel identity spin projection, universal limits, & explicit t-channel integrals — 0 sorry's)
  └── LargeSpin.lean       (J-dependent contour, Vitali's theorem + s-/t-channel bounds, & universal lim_{J → ∞} for even J)
```
(Supported by [`CFT/Vitali.lean`](../Vitali.lean) for Montel equicontinuity and the Vitali–Porter theorem — 0 `sorry`s.)

---

## 3. Step-by-Step Implementation Plan

### Step 0 (Outside Subfolder): Two-Variable Crossing Symmetry in `CFT/Corr_pdisk.lean` & Vitali–Porter in `CFT/Vitali.lean` — **Done**
- [x] State `FourPointData.crossing_correlator` and `crossing_correlator_real` in `CFT/Corr_pdisk.lean`.
- [x] Prove `FourPointData.crossing_correlator` from `crossing_correlator_eucl`, `correlator_conj_eq_eucl`, and separate holomorphy on `CutPlane` using `eqOn_CutPlane_of_differentiableOn_of_eqOn_interval`.
- [x] Prove Montel equicontinuity (`tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le`) and the Vitali–Porter theorem (`vitali_porter_real_interval`, `vitali_porter_ucDisk`) in `CFT/Vitali.lean` (**0 `sorry`s**).

### Step 1: `CFT/MonomialBootstrap/MonomialDecomp.lean` — **Structures & Core Bounds Done**
- [x] Define `MonomialFourPointData`:
  - Family of non-negative spin-$J$ spectral measures $\mu_J$ on $h \in \mathbb{R}$ for $J \in \mathbb{Z}$ supported on $h \ge 0, h + J \ge 0$ (`support_unitary`) and vanishing for odd $J$ (`support_odd_spin`),
  - Monomial evaluation on $\operatorname{UcPdisk}$ (`eval`, `evalSpin`, `laplaceSpin`, `laplaceSpinReal`) and factorization `evalSpin_eq_exp_mul_laplace`:
    $$\mathcal{G}_{\text{mon}}(w_l, w_r) = \sum_{J \in \mathbb{Z}} \int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h) = \sum_{J \in \mathbb{Z}} e^{J w_r} L_J(w_l + w_r).$$
- [x] Prove $\pi$-periodicity under opposite imaginary shifts `eval_shift_pi`: $\mathcal{G}_{\text{mon}}(w_l - i\pi, w_r + i\pi) = \mathcal{G}_{\text{mon}}(w_l, w_r)$, the 1D positivity bound `norm_laplaceSpin_le_laplaceSpinReal` ($\|L_J(w)\| \le L_J(\operatorname{Re}(w))$), the 2D $s$-channel positivity bound `norm_eval_le_evalReal` ($\|\mathcal{G}_{\text{mon}}(w_l, w_r)\| \le \mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l), \operatorname{Re}(w_r))$), continuity along opposite imaginary shifts (`continuous_evalSpin_shift`, `continuous_eval_shift`), real-axis monotonicity (`laplaceSpinReal_mono`), and holomorphy of $L_J(w)$ on $\operatorname{UcDisk}$ (`differentiableOn_laplaceSpin`).
- [x] State `FourPointData.exists_monomialDecomp` (that every `FourPointData ν Δ_phi` in `CFT/Corr_pdisk.lean` admits a `MonomialFourPointData` whose evaluation on $\operatorname{UcPdisk}$ equals `corr.correlator_pdisk wl wr`).
  - [ ] *(Later)*: Fill in the measure-pushforward proof of `FourPointData.exists_monomialDecomp` from `geg_two_var_sum`, `ConformalBlock.A_odd_level`, and `FourPointData.support_even_spin`.

### Step 2: `CFT/MonomialBootstrap/FourierProj.lean` — **Done (0 `sorry`s)**
- [x] Define `laplaceFourierTransform φ σ t` for a test function $\varphi : \mathbb{R} \to \mathbb{R}$, and prove its rapid large-$\|t\|$ decay `exists_bound_laplaceFourierTransform` for compactly supported $C^k$ functions $\varphi$, together with `continuous_laplaceFourierTransform` and `integrable_laplaceFourierTransform`.
- [x] Define `fourierIntegrand`, `fourierProjSpinFull` (on $[-\pi, \pi]$), `fourierProjSpin` (folded on $[-\pi/2, \pi/2]$), and `pairSpin`.
- [x] Prove $\pi$-periodicity of the Fourier integrand (`fourierIntegrand_add_pi`), the $s$-channel positivity bound (`norm_fourierIntegrand_le`), `continuous_fourierIntegrand`, `fourierProjSpinFull_eq_fourierProjSpin`, `laplaceSpin_eq_fourierProjSpinFull`, `laplaceSpin_eq_fourierProjSpin`, and its real-axis specialization `laplaceSpinReal_eq_fourierProjSpin` (expressing $L_J(\sigma_l + \sigma_r)$ for real $\sigma_l, \sigma_r < 0$ as a $\theta$-integral on $[-\pi/2, \pi/2]$ where both arguments stay inside the $t$-channel strip $\operatorname{Im} \in (-\pi, \pi)$), together with `pairSpin_eq_integral_laplaceSpin`:
  $$\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h)
    = \int_{-\infty}^{\infty} \frac{dt}{2\pi} \, \widehat{\varphi}_{\sigma}(t) \, L_J(\sigma + i t).$$

### Step 3: `CFT/MonomialBootstrap/Gap.lean` — **Done (0 `sorry`s)**
- [x] Define the inverse map `zOfW`, crossed universal-cover coordinate `crossW`, analytic single-variable crossing prefactor `crossFactor Δ_phi w = 4^Δ_phi * exp(Δ_phi * w) * (1 - exp w)^(-2*Δ_phi)` on $\operatorname{UcDisk}$, and two-variable $t$-channel identity contribution `crossIdentity`.
- [x] Prove `zOfW_mem_CutPlane`, `rho_zOfW`, `logRho_zOfW`, `crossFactor_eq_zOfW_cpow`, `crossW_mem_UcDisk`, `rho_one_sub_zOfW`, `exp_re_crossW_le_norm_one_sub_exp_sq`, `re_crossW_le_of_re_ge`, `norm_crossFactor_eq`, `norm_crossFactor_le_of_re_le`, and `norm_crossFactor_mul_exp_re_crossW_le` on the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$.
- [x] Define `HasLowerTwist` and `HasTwistGap` (factoring out the identity `1` plus a remainder `rem : MonomialFourPointData` satisfying `rem.HasLowerTwist h_gap`) and prove `HasLowerTwist.mono`, `HasTwistGap.mono`, `evalReal_sub_one_nonneg`, `evalSpinReal_le_of_hasLowerTwist`, `norm_eval_le_of_hasLowerTwist`, and `norm_eval_sub_one_le`.
- [x] Prove two-variable crossing symmetry in $(w_l, w_r)$ coordinates (`eval_eq_cross`) from `corr.crossing_correlator` and prove the **$t$-channel identity dominance bounds** (`norm_eval_sub_crossIdentity_le` and `norm_eval_sub_crossIdentity_le_of_re_le`).

### Step 4A: `CFT/MonomialBootstrap/IdentityProj.lean` — **Done (0 `sorry`s)**
- [x] Define `identityProjSpin`, the universal large-spin Laplace transform `universalLaplace` and `universalLaplaceReal` on $\operatorname{UcDisk}$, and `universalMonomialPairing Δ_phi φ`, and prove `universalLaplace_ofReal`, `continuousOn_crossFactor`, and `differentiableOn_universalLaplace`.
- [x] Prove the explicit binomial power-series identity and Fourier inversion (`integral_laplaceFourierTransform_mul_universalLaplace`) and the large-spin $t$-channel identity projection asymptotics (`tendsto_identityProjSpin_real`) via contour integration and Euler's Gamma limit formula.

### Step 4B: `CFT/MonomialBootstrap/LargeSpin.lean` — **All 3 Stages & Main Theorem Proved**
- [x] **Stage 1 (Real-axis asymptotics of $L_{2k}(\sigma)$)**: Prove `exists_bound_fourierProjSpin_sub_identity_real` and `tendsto_fourierProjSpin_sub_identity_real_of_half_lt` (**0 `sorry`s** for $\Delta_\phi > 1/2$), and prove `tendsto_laplaceSpinReal_of_half_lt` and `tendsto_laplaceSpinReal` (for real $\sigma < 0$, $(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma) \to L_{\text{id}}(\Delta_\phi, \sigma)$) along $\sigma_r(2k) = -1/(2k), \sigma_l(2k) = \sigma + 1/(2k) < 0$.
- [x] **Stage 2 (Complex extension to $w \in \operatorname{UcDisk}$ via 1D Vitali)**: Prove the uniform vertical-line bound `norm_rescaled_laplaceSpin_le` ($\|(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma + i t)\| \le (2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$) and prove `tendsto_laplaceSpin_of_half_lt` and `tendsto_laplaceSpin` (1D Vitali upgrade from real $\sigma < 0$ to all $w \in \operatorname{UcDisk}$ via `CFT.vitali_porter_ucDisk`).
- [x] **Stage 3 (Pairing with $\varphi(h)$)**: Prove `tendsto_integral_laplaceSpin_of_half_lt` and `tendsto_integral_laplaceSpin` (via `tendsto_integral_filter_of_dominated_convergence`) and the **main monomial lightcone bootstrap theorems** `tendsto_pairSpin_large_even_spin_of_half_lt` (**0 `sorry`s** for $\Delta_\phi > 1/2$) and `tendsto_pairSpin_large_even_spin`:
  $$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) =
    \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)}
    \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \varphi(\Delta_\phi + n).$$
  - [ ] *(Later)*: Extend `tendsto_fourierProjSpin_sub_identity_real` from $\Delta_\phi > 1/2$ to $0 < \Delta_\phi \le 1/2$ via integration by parts in $\theta$.

