/-
The semigroup property of the lattice heat kernels, `q_{s+t} = q_s * q_t` on `ℤ` and
`p_{s+t} = p_s * p_t` on `ℤ^4`, used in the proof of `prop:free-schauder` of BALABAN_CORE.tex
(`P_t` as a product of two or three factors `P_{t/2}`, `P_{t/3}`).

The Fourier series of `q_s` is computed from the lazy expansion of `CoreLean.HeatKernel1D`: the
finite sums `Σ_m (L^k δ₀)(m) cos(mθ) = ((1 + cos θ)/2)^k` give `Σ_m q_s(m) cos(mθ) = e^{-2s(1-cos θ)}`,
and the convolution is the Fourier integral of the product of the two symbols.
-/
import CoreLean.HeatKernel1D
import CoreLean.Vendor.Green
import CoreLean.Vendor.PiProd

open MeasureTheory Real Balaban.LatticeGreen

namespace CoreLean

lemma summable_mul_lazyInt (k : ℕ) (f : ℤ → ℝ) : Summable fun m : ℤ => lazyInt k m * f m :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) k) fun m hm => by
    rw [lazyInt_eq_zero k m (by simp only [Finset.mem_Icc, not_and_or, not_le] at hm; omega),
      zero_mul]

/-- `Σ_m (L^k δ₀)(m) cos(mθ) = ((1 + cos θ)/2)^k`, in the normalisation of `lazyInt`. -/
theorem tsum_lazyInt_cos (k : ℕ) (θ : ℝ) :
    ∑' m : ℤ, lazyInt k m * Real.cos (m * θ) = 2 * π * ((1 + Real.cos θ) / 2) ^ k := by
  induction k with
  | zero =>
    rw [tsum_eq_single 0]
    · simp [lazyInt_zero]
    · intro m hm; simp [lazyInt_zero, hm]
  | succ k ih =>
    have e1 : ∑' m : ℤ, lazyInt k (m - 1) * Real.cos (m * θ) =
        ∑' j : ℤ, lazyInt k j * Real.cos ((j + 1) * θ) := by
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]; simp
    have e2 : ∑' m : ℤ, lazyInt k (m + 1) * Real.cos (m * θ) =
        ∑' j : ℤ, lazyInt k j * Real.cos ((j - 1) * θ) := by
      rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]; simp
    have s1 : Summable fun m : ℤ => lazyInt k (m - 1) * Real.cos (m * θ) := by
      have := (summable_mul_lazyInt k fun j => Real.cos ((j + 1) * θ)).comp_injective
        (sub_left_injective (b := (1 : ℤ)))
      exact this.congr fun m => by simp
    have s2 : Summable fun m : ℤ => lazyInt k (m + 1) * Real.cos (m * θ) := by
      have := (summable_mul_lazyInt k fun j => Real.cos ((j - 1) * θ)).comp_injective
        (add_left_injective (1 : ℤ))
      exact this.congr fun m => by simp
    have s0 := summable_mul_lazyInt k fun m => Real.cos (m * θ)
    have hsplit : (fun m : ℤ => lazyInt (k + 1) m * Real.cos (m * θ)) = fun m : ℤ =>
        (lazyInt k (m - 1) * Real.cos (m * θ) + 2 * (lazyInt k m * Real.cos (m * θ)) +
          lazyInt k (m + 1) * Real.cos (m * θ)) / 4 := by
      funext m; rw [lazyInt_succ]; ring
    rw [hsplit, tsum_div_const, (s1.add (s0.mul_left 2)).tsum_add s2,
      s1.tsum_add (s0.mul_left 2), tsum_mul_left, e1, e2]
    -- `cos((j+1)θ) + cos((j-1)θ) = 2 cos(jθ) cos θ`
    have hc : ∀ j : ℤ, lazyInt k j * Real.cos ((j + 1) * θ) +
        lazyInt k j * Real.cos ((j - 1) * θ) = 2 * Real.cos θ * (lazyInt k j * Real.cos (j * θ)) :=
      fun j => by rw [add_mul, sub_mul, one_mul, Real.cos_add, Real.cos_sub]; ring
    have hsum : ∑' j : ℤ, lazyInt k j * Real.cos ((j + 1) * θ) +
        ∑' j : ℤ, lazyInt k j * Real.cos ((j - 1) * θ) = 2 * Real.cos θ * (2 * π *
          ((1 + Real.cos θ) / 2) ^ k) := by
      rw [← (summable_mul_lazyInt k _).tsum_add (summable_mul_lazyInt k _)]
      simp_rw [hc]
      rw [tsum_mul_left, ih]
    have : ∑' j : ℤ, lazyInt k j * Real.cos ((j + 1) * θ) + 2 * (2 * π * ((1 + Real.cos θ) / 2) ^ k)
        + ∑' j : ℤ, lazyInt k j * Real.cos ((j - 1) * θ) = 2 * Real.cos θ * (2 * π *
          ((1 + Real.cos θ) / 2) ^ k) + 2 * (2 * π * ((1 + Real.cos θ) / 2) ^ k) := by
      rw [← hsum]; ring
    rw [ih, this]
    ring

/-- An odd summand sums to zero. -/
lemma tsum_eq_zero_of_odd {f : ℤ → ℝ} (hf : ∀ m, f (-m) = -f m) : ∑' m, f m = 0 := by
  have h : ∑' m, f m = ∑' m, f (-m) := ((Equiv.neg ℤ).tsum_eq f).symm
  simp_rw [hf, tsum_neg] at h
  linarith

/-- The Fourier series of `q_s`: `Σ_m q_s(m) cos(mθ) = e^{-2s(1 - cos θ)}` for `s ≥ 0`. -/
theorem hasSum_heatKernel1_cos {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    HasSum (fun m : ℤ => heatKernel1 s m * Real.cos (m * θ)) (heatSymbol s θ) := by
  set w : ℕ → ℝ := fun k => (2 * π)⁻¹ * Real.exp (-(4 * s)) * ((4 * s) ^ k / (k.factorial : ℝ))
    with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by simp only [hw]; positivity
  have hex : HasSum (fun k : ℕ => (4 * s * ((1 + Real.cos θ) / 2)) ^ k / (k.factorial : ℝ))
      (Real.exp (4 * s * ((1 + Real.cos θ) / 2))) := by
    have := NormedSpace.expSeries_div_hasSum_exp (4 * s * ((1 + Real.cos θ) / 2))
    rwa [← Real.exp_eq_exp_ℝ] at this
  -- the dominating family `w_k lazyInt k m` is summable on `ℕ × ℤ`
  have hg0 : ∀ p : ℕ × ℤ, 0 ≤ w p.1 * lazyInt p.1 p.2 := fun p =>
    mul_nonneg (hw0 _) (lazyInt_nonneg _ _)
  have hgs : Summable fun p : ℕ × ℤ => w p.1 * lazyInt p.1 p.2 := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun k => (summable_lazyInt k).mul_left (w k), ?_⟩
    have : (fun k : ℕ => ∑' m : ℤ, w k * lazyInt k m) = fun k => w k * (2 * π) := by
      funext k; rw [tsum_mul_left, tsum_lazyInt]
    rw [this]
    exact ((Real.summable_pow_div_factorial (4 * s)).mul_left
      ((2 * π)⁻¹ * Real.exp (-(4 * s)))).mul_right _
  have hfs : Summable fun p : ℕ × ℤ => w p.1 * lazyInt p.1 p.2 * Real.cos (p.2 * θ) := by
    refine Summable.of_norm_bounded hgs fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 p)]
    exact mul_le_of_le_one_right (hg0 p) (Real.abs_cos_le_one _)
  have hq : ∀ m : ℤ, heatKernel1 s m * Real.cos (m * θ) =
      ∑' k, w k * lazyInt k m * Real.cos (m * θ) := fun m => by
    rw [← ((hasSum_heatKernel1_lazy s m).mul_right (Real.cos (m * θ))).tsum_eq]
  have hk : ∀ k, ∑' m : ℤ, w k * lazyInt k m * Real.cos (m * θ) =
      w k * (2 * π * ((1 + Real.cos θ) / 2) ^ k) := fun k => by
    rw [show (fun m : ℤ => w k * lazyInt k m * Real.cos (m * θ)) =
      fun m : ℤ => w k * (lazyInt k m * Real.cos (m * θ)) from funext fun m => mul_assoc _ _ _,
      tsum_mul_left, tsum_lazyInt_cos]
  have htot : ∑' k, w k * (2 * π * ((1 + Real.cos θ) / 2) ^ k) = heatSymbol s θ := by
    rw [heatSymbol_eq_lazy, ← hex.tsum_eq, ← tsum_mul_left]
    congr 1; funext k
    simp only [hw]
    rw [mul_pow]
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
    rw [← mul_pow, ← mul_pow]
    ring
  rw [show (fun m : ℤ => heatKernel1 s m * Real.cos (m * θ)) =
    fun m : ℤ => ∑' k, w k * lazyInt k m * Real.cos (m * θ) from funext hq]
  have hfs' : Summable (Function.uncurry fun (m : ℤ) (k : ℕ) =>
      w k * lazyInt k m * Real.cos (m * θ)) := hfs.prod_symm
  rw [← htot, ← funext hk, hfs'.tsum_comm]
  exact hfs'.prod.hasSum

/-- `Σ_m q_s(m) sin(mθ) = 0`, since `q_s` is even. -/
theorem tsum_heatKernel1_sin (s θ : ℝ) :
    ∑' m : ℤ, heatKernel1 s m * Real.sin (m * θ) = 0 :=
  tsum_eq_zero_of_odd fun m => by
    rw [heatKernel1_neg]; push_cast; rw [neg_mul, Real.sin_neg]; ring

/-- The pointwise identity under the integral of the convolution:
`Σ_m q_s(m) cos((n-m)θ) e^{-2t(1-cos θ)} = cos(nθ) e^{-2s(1-cos θ)} e^{-2t(1-cos θ)}`. -/
lemma hasSum_conv_integrand {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (n : ℤ) (θ : ℝ) :
    HasSum (fun m : ℤ => heatKernel1 s m * (Real.cos (((n - m : ℤ) : ℝ) * θ) * heatSymbol t θ))
      (Real.cos ((n : ℝ) * θ) * heatSymbol s θ * heatSymbol t θ) := by
  have hcos := (hasSum_heatKernel1_cos hs θ).mul_left (Real.cos ((n : ℝ) * θ))
  have hss : Summable fun m : ℤ => heatKernel1 s m * Real.sin (m * θ) :=
    Summable.of_norm_bounded (f := fun m : ℤ => heatKernel1 s m * Real.sin (m * θ))
      (hasSum_heatKernel1 hs).summable fun m => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel1_nonneg hs m)]
        exact mul_le_of_le_one_right (heatKernel1_nonneg hs m) (Real.abs_sin_le_one _)
  have hsin := hss.hasSum.mul_left (Real.sin ((n : ℝ) * θ))
  rw [tsum_heatKernel1_sin, mul_zero] at hsin
  have h := (hcos.add hsin).mul_right (heatSymbol t θ)
  rw [add_zero] at h
  convert h using 1
  funext m
  push_cast
  rw [sub_mul, Real.cos_sub]
  ring

/-- The semigroup property on `ℤ`: `Σ_m q_s(m) q_t(n - m) = q_{s+t}(n)` for `s, t ≥ 0`. -/
theorem hasSum_heatKernel1_conv {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (n : ℤ) :
    HasSum (fun m : ℤ => heatKernel1 s m * heatKernel1 t (n - m)) (heatKernel1 (s + t) n) := by
  have hqs := hasSum_heatKernel1 hs
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π)
    (F := fun (m : ℤ) (θ : ℝ) => heatKernel1 s m * (Real.cos (((n - m : ℤ) : ℝ) * θ) *
      heatSymbol t θ))
    (f := fun θ => Real.cos ((n : ℝ) * θ) * heatSymbol s θ * heatSymbol t θ)
    (fun m _ => heatKernel1 s m)
    (fun m => by
      have := continuous_heatSymbol_right t
      exact (continuous_const.mul ((by fun_prop : Continuous fun θ : ℝ =>
        Real.cos (((n - m : ℤ) : ℝ) * θ)).mul this)).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel1_nonneg hs m), abs_mul,
        abs_of_pos (heatSymbol_pos t θ)]
      exact mul_le_of_le_one_right (heatKernel1_nonneg hs m)
        (mul_le_one₀ (Real.abs_cos_le_one _) (heatSymbol_pos t θ).le (heatSymbol_le_one ht θ)))
    (Filter.Eventually.of_forall fun θ _ => hqs.summable)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hasSum_conv_integrand hs t n θ)
  have h' := h.mul_left (2 * π)⁻¹
  have hint : ∀ m : ℤ, (2 * π)⁻¹ * ∫ θ in (-π)..π, heatKernel1 s m *
      (Real.cos (((n - m : ℤ) : ℝ) * θ) * heatSymbol t θ) = heatKernel1 s m * heatKernel1 t (n - m) :=
    fun m => by
      rw [intervalIntegral.integral_const_mul]
      rw [show heatKernel1 t (n - m) = (2 * π)⁻¹ * ∫ θ in (-π)..π,
        Real.cos (((n - m : ℤ) : ℝ) * θ) * heatSymbol t θ from rfl]
      ring
  have hsym : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * heatSymbol s θ * heatSymbol t θ =
      Real.cos ((n : ℝ) * θ) * heatSymbol (s + t) θ := fun θ => by
    rw [mul_assoc]
    congr 1
    simp only [heatSymbol]
    rw [← Real.exp_add]
    congr 1; ring
  have htot : (2 * π)⁻¹ * ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * heatSymbol s θ *
      heatSymbol t θ = heatKernel1 (s + t) n := by
    simp_rw [hsym]
    rfl
  rw [← htot, ← funext hint]
  exact h'

/-- The semigroup property on `ℤ^d`: `Σ_y p_s(y) p_t(x - y) = p_{s+t}(x)` for `s, t ≥ 0`. -/
theorem hasSum_heatKernel_conv {d : ℕ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Fin d → ℤ) :
    HasSum (fun y : Fin d → ℤ => heatKernel d s y * heatKernel d t (x - y))
      (heatKernel d (s + t) x) := by
  have h := (Balaban.Green.pi_prod_summable_hasSum (𝕜 := ℝ) (κ := ℤ) (Fin d))
    (fun μ m => heatKernel1 s m * heatKernel1 t (x μ - m)) fun μ => by
      refine (hasSum_heatKernel1_conv hs ht (x μ)).summable.congr fun m => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel1_nonneg hs _)
        (heatKernel1_nonneg ht _))]
  have hp : ∏ μ, ∑' m, heatKernel1 s m * heatKernel1 t (x μ - m) = heatKernel d (s + t) x := by
    unfold heatKernel
    exact Finset.prod_congr rfl fun μ _ => (hasSum_heatKernel1_conv hs ht (x μ)).tsum_eq
  rw [← hp]
  convert h.2 using 1
  funext y
  unfold heatKernel
  rw [← Finset.prod_mul_distrib]
  rfl

end CoreLean
