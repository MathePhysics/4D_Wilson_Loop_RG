/-
`lem:global-bounds` of BALABAN_CORE.tex: from kernel bounds to bounds in the weighted norms.

The proof of the core sums a kernel bound of `thm:propagators` over the blocks of the determining set. For a
point `x` of the block of `y ∈ Γ_j`, a value `v = ‖(Kλ)(x)‖` with
`v ≤ Σ_{y'} B₀a_j^p e^{-δd(y, y')}‖λ‖_{∞,Δ(y')}`, a weight `ϖ` of the rate `θ`,
`ϖ(y) ≤ e^{θd(y, y')}ϖ(y')`, and `ϖ(y')‖λ‖_{∞,Δ(y')} ≤ a_{j'}^σm` (that is, `‖ϖλ‖_{∞,(σ)} ≤ m`) give
`ϖ(y)v ≤ L⁴B₀c a_j^{σ+p}m` (`weighted_kernel_bound`), from

* `a_{j'}^σ ≤ L^{4|j - j'|}a_j^σ` for `|σ| ≤ 4` (`rpow_scale_le`),
* `|j - j'| ≤ 1 + d(y, y')/(RM)` (`lem:distance`(ii)) and `L^{4d/(RM)} ≤ e^{θd}` for `4 log L ≤ θRM`,
* `Σ_{y'} e^{-(δ - 2θ)d(y, y')} ≤ c`.

`global_kernel_bound` is the instance on the model of the continuum torus (`ContSeq`), with the determining
set `𝐁`, the weighted distance, `lem:distance`(ii) (`wdist_ge_layers`), and `summation`, for the weights of
`lem:global-bounds` (`θ = δ₀/8`, `RM ≥ 32δ₀⁻¹ log L`) and kernels of a rate `δ ≥ δ₀/2` (`δ₀` for `G'` and its
differences, `δ₀/2` for `P`, which leaves the rate `δ₀/4` in the sum): `c = c₁(½, ½δ₀)`, so the constant is
`L⁴B₀c₁(½, ½δ₀) = B_g⁰` of the core. The kernel bounds themselves
(`eq:propagator-bound` and the bounds of `thm:propagators`(iv), (vii), (viii)) are stated in the core without
proof and enter as the hypothesis on `v`; the bound for forms which do not vanish outside the Dirichlet
domain is not formalised.
-/
import CoreLean.SummationBound

open Real

noncomputable section

namespace CoreLean

namespace GlobalBounds

/-- `a_{j'}^σ ≤ L^{4|j - j'|}a_j^σ` for `a_i = L^iη` and `|σ| ≤ 4`. -/
lemma rpow_scale_le {L η σ : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (hσ : |σ| ≤ 4) (j j' : ℕ) :
    ((L : ℝ) ^ j' * η) ^ σ ≤ L ^ (4 * |(j : ℝ) - j'|) * (L ^ j * η) ^ σ := by
  have hL0 : 0 < L := by linarith
  have e : ∀ i : ℕ, ((L : ℝ) ^ i * η) ^ σ = L ^ ((i : ℝ) * σ) * η ^ σ := fun i => by
    rw [mul_rpow (by positivity) hη.le, ← rpow_natCast, ← rpow_mul hL0.le]
  rw [e, e, ← mul_assoc, ← rpow_add hL0]
  refine mul_le_mul_of_nonneg_right (rpow_le_rpow_of_exponent_le hL ?_) (by positivity)
  have h : ((j' : ℝ) - j) * σ ≤ 4 * |(j : ℝ) - j'| := by
    calc ((j' : ℝ) - j) * σ ≤ |((j' : ℝ) - j) * σ| := le_abs_self _
      _ = |(j : ℝ) - j'| * |σ| := by rw [abs_mul, abs_sub_comm]
      _ ≤ |(j : ℝ) - j'| * 4 := mul_le_mul_of_nonneg_left hσ (abs_nonneg _)
      _ = 4 * |(j : ℝ) - j'| := by ring
  linarith

/-- `L^{4|j - j'|} ≤ L⁴e^{θd}` when `|j - j'| ≤ 1 + d/(RM)` and `4 log L ≤ θRM`. -/
lemma pow_scale_le {L θ RM d : ℝ} (hL : 1 ≤ L) (hRMpos : 0 < RM)
    (hRM : 4 * Real.log L ≤ θ * RM) (hd : 0 ≤ d) {t : ℝ} (ht : t ≤ 1 + d / RM) :
    L ^ (4 * t) ≤ L ^ (4 : ℝ) * Real.exp (θ * d) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  calc L ^ (4 * t) ≤ L ^ (4 * (1 + d / RM)) :=
        rpow_le_rpow_of_exponent_le hL (by linarith)
    _ = L ^ (4 : ℝ) * Real.exp (4 * Real.log L * d / RM) := by
        rw [show 4 * (1 + d / RM) = 4 + 4 * d / RM by ring, rpow_add hL0]
        congr 1
        rw [rpow_def_of_pos hL0]; congr 1; ring
    _ ≤ L ^ (4 : ℝ) * Real.exp (θ * d) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [div_le_iff₀ hRMpos]
        nlinarith

/-- The summation of a kernel bound of the rate `δ` in the weighted norms of a weight of the rate `θ` (the proof
of `lem:global-bounds`); the sum is taken with the rate `δ - 2θ`. -/
theorem weighted_kernel_bound {ι : Type*} (B : Finset ι) (j : ι → ℕ) (d : ι → ι → ℝ) (ϖ Λ : ι → ℝ)
    {L η δ θ RM B₀ c m σ p : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (hRMpos : 0 < RM)
    (hRM : 4 * Real.log L ≤ θ * RM) (hσ : |σ| ≤ 4) (hB₀ : 0 ≤ B₀) (hm : 0 ≤ m)
    (hd : ∀ y y', 0 ≤ d y y') (hscale : ∀ y y', |(j y : ℝ) - j y'| ≤ 1 + d y y' / RM)
    (hϖ : ∀ y y', ϖ y ≤ Real.exp (θ * d y y') * ϖ y') (hϖ0 : ∀ y, 0 ≤ ϖ y)
    (hΛ0 : ∀ y, 0 ≤ Λ y) (hlam : ∀ y' ∈ B, ϖ y' * Λ y' ≤ ((L : ℝ) ^ j y' * η) ^ σ * m) {y : ι}
    (hsum : ∑ y' ∈ B, Real.exp (-((δ - 2 * θ) * d y y')) ≤ c) {v : ℝ}
    (hv : v ≤ ∑ y' ∈ B, B₀ * ((L : ℝ) ^ j y * η) ^ p * Real.exp (-(δ * d y y')) * Λ y') :
    ϖ y * v ≤ L ^ (4 : ℝ) * B₀ * c * ((L : ℝ) ^ j y * η) ^ (σ + p) * m := by
  have hL0 : 0 < L := by linarith
  set a : ℝ := (L : ℝ) ^ j y * η with ha
  have ha0 : 0 < a := by positivity
  set K : ℝ := L ^ (4 : ℝ) * B₀ * a ^ (σ + p) * m with hK
  have hK0 : 0 ≤ K := by positivity
  -- the bound of each term
  have hterm : ∀ y' ∈ B, ϖ y * (B₀ * a ^ p * Real.exp (-(δ * d y y')) * Λ y') ≤
      K * Real.exp (-((δ - 2 * θ) * d y y')) := by
    intro y' hy'
    have hd' := hd y y'
    have h1 : ϖ y * Λ y' ≤ Real.exp (θ * d y y') * (((L : ℝ) ^ j y' * η) ^ σ * m) :=
      (mul_le_mul_of_nonneg_right (hϖ y y') (hΛ0 y')).trans
        (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlam y' hy') (Real.exp_pos _).le)
    have h2 : ((L : ℝ) ^ j y' * η) ^ σ ≤ L ^ (4 : ℝ) * Real.exp (θ * d y y') * a ^ σ :=
      (rpow_scale_le hL hη hσ (j y) (j y')).trans (mul_le_mul_of_nonneg_right
        (pow_scale_le hL hRMpos hRM hd' (hscale y y')) (by positivity))
    have h3 : ϖ y * Λ y' ≤ Real.exp (θ * d y y') *
        (L ^ (4 : ℝ) * Real.exp (θ * d y y') * a ^ σ * m) :=
      h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hm) (Real.exp_pos _).le)
    have hexp : Real.exp (-(δ * d y y')) * (Real.exp (θ * d y y') * Real.exp (θ * d y y')) ≤
        Real.exp (-((δ - 2 * θ) * d y y')) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (le_of_eq (by ring))
    have hap : a ^ p * a ^ σ = a ^ (σ + p) := by rw [← rpow_add ha0]; ring_nf
    calc ϖ y * (B₀ * a ^ p * Real.exp (-(δ * d y y')) * Λ y')
        = B₀ * a ^ p * Real.exp (-(δ * d y y')) * (ϖ y * Λ y') := by ring
      _ ≤ B₀ * a ^ p * Real.exp (-(δ * d y y')) * (Real.exp (θ * d y y') *
            (L ^ (4 : ℝ) * Real.exp (θ * d y y') * a ^ σ * m)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = L ^ (4 : ℝ) * B₀ * (a ^ p * a ^ σ) * m *
            (Real.exp (-(δ * d y y')) * (Real.exp (θ * d y y') * Real.exp (θ * d y y'))) := by
          ring
      _ ≤ L ^ (4 : ℝ) * B₀ * (a ^ p * a ^ σ) * m * Real.exp (-((δ - 2 * θ) * d y y')) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-((δ - 2 * θ) * d y y')) := by rw [hap, hK]
  calc ϖ y * v ≤ ϖ y * ∑ y' ∈ B, B₀ * a ^ p * Real.exp (-(δ * d y y')) * Λ y' :=
        mul_le_mul_of_nonneg_left hv (hϖ0 y)
    _ = ∑ y' ∈ B, ϖ y * (B₀ * a ^ p * Real.exp (-(δ * d y y')) * Λ y') := Finset.mul_sum _ _ _
    _ ≤ ∑ y' ∈ B, K * Real.exp (-((δ - 2 * θ) * d y y')) := Finset.sum_le_sum hterm
    _ = K * ∑ y' ∈ B, Real.exp (-((δ - 2 * θ) * d y y')) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * c := mul_le_mul_of_nonneg_left hsum hK0
    _ = L ^ (4 : ℝ) * B₀ * c * a ^ (σ + p) * m := by rw [hK]; ring

open Summation

/-- `lem:global-bounds`, the first part, on the model of the continuum torus: for `y ∈ 𝐁` of the scale `j`, a
kernel bound `v ≤ Σ_{y' ∈ 𝐁} B₀a_j^q e^{-δd(y, y')}Λ(y')` of a rate `δ ≥ δ₀/2` (`δ = δ₀` for `G'`, `∇G'`, `Δ_𝐔G'`,
`G'∇^*`; `δ = δ₀/2` for `P`, `∇P`) and `ϖ(y')Λ(y') ≤ a_{j(y')}^σm` on `𝐁`, with a weight `ϖ` of the rate `δ₀/8`
and `RM ≥ max{r₁(½, ½δ₀), 32δ₀⁻¹ log L}`: `ϖ(y)v ≤ L⁴B₀c₁(½, ½δ₀)a_j^{σ+q}m`. -/
theorem global_kernel_bound {p : ℝ} [Fact (0 < p)] (C : ContSeq p) (ϖ Λ : Tor p → ℝ)
    {δ₀ δ B₀ m σ q : ℝ} (hδ₀ : 0 < δ₀) (hδ : δ₀ / 2 ≤ δ) (hRM₁ : C.r1 (1 / 2) (δ₀ / 2) ≤ C.RM)
    (hRM : 32 * Real.log C.L / δ₀ ≤ C.RM) (hσ : |σ| ≤ 4) (hB₀ : 0 ≤ B₀) (hm : 0 ≤ m)
    (hϖ : ∀ y y', ϖ y ≤ Real.exp (δ₀ / 8 * C.dd y y') * ϖ y') (hϖ0 : ∀ y, 0 ≤ ϖ y)
    (hΛ0 : ∀ y, 0 ≤ Λ y)
    (hlam : ∀ y' ∈ C.BF, ϖ y' * Λ y' ≤ C.a (C.D.scale y') ^ σ * m) {y : Tor p} (hy : y ∈ C.BF)
    {v : ℝ} (hv : v ≤ ∑ y' ∈ C.BF, B₀ * C.a (C.D.scale y) ^ q * Real.exp (-(δ * C.dd y y')) * Λ y') :
    ϖ y * v ≤ (C.L : ℝ) ^ (4 : ℝ) * B₀ * C.c1 (1 / 2) (δ₀ / 2) * C.a (C.D.scale y) ^ (σ + q) * m := by
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have hL0 : (0 : ℝ) < C.L := by linarith
  have hRMpos : 0 < C.RM := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hRM₁)
  set η : ℝ := ((C.L : ℝ) ^ C.k)⁻¹ with hη
  have hη0 : 0 < η := by positivity
  have hae : ∀ i, C.a i = (C.L : ℝ) ^ i * η := fun i => by
    simp only [ContSeq.a, aa, η, div_eq_mul_inv]
  -- `lem:distance`(ii): `|j - j'| ≤ 1 + d/(RM)`
  have hscale : ∀ z z', |(C.D.scale z : ℝ) - C.D.scale z'| ≤ 1 + C.dd z z' / C.RM := by
    intro z z'
    have h := wdist_ge_layers C.D (R := C.RM) (M := 1) C.sep (C.D.mem_scale z).1 (C.D.mem_scale z).2
      (C.D.mem_scale z').1 (C.D.mem_scale z').2
    rw [← C.ofReal_dd] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff (C.dd_nonneg z z')).mp h
    rw [mul_one] at h2
    have h3 : |(C.D.scale z : ℝ) - C.D.scale z'| - 1 ≤ C.dd z z' / C.RM := by
      rw [le_div_iff₀ hRMpos]
      nlinarith [le_max_left (|(C.D.scale z : ℝ) - C.D.scale z'| - 1) 0]
    linarith
  -- `4 log L ≤ (δ₀/8)RM`
  have hRM' : 4 * Real.log C.L ≤ δ₀ / 8 * C.RM := by
    rw [div_le_iff₀ hδ₀] at hRM; linarith
  -- `eq:summation` with the rate `δ₀/2` and `α = ½`; the sum is taken with the rate `δ - δ₀/4 ≥ δ₀/4`
  have hsum : ∑ y' ∈ C.BF, Real.exp (-((δ - 2 * (δ₀ / 8)) * C.dd y y')) ≤ C.c1 (1 / 2) (δ₀ / 2) := by
    have := C.summation (α := 1 / 2) (δ := δ₀ / 2) (by norm_num) (by positivity) hRM₁ hy
    refine le_trans (Finset.sum_le_sum fun y' _ => ?_) this
    exact Real.exp_le_exp.mpr (by nlinarith [C.dd_nonneg y y'])
  have h := weighted_kernel_bound C.BF C.D.scale C.dd ϖ Λ hL1 hη0 hRMpos hRM' hσ hB₀ hm
    C.dd_nonneg hscale hϖ hϖ0 hΛ0 (fun y' hy' => by rw [← hae]; exact hlam y' hy') hsum
    (v := v) (p := q) (by simpa only [hae] using hv)
  rwa [← hae] at h

end GlobalBounds

end CoreLean
