module

public import CoreLean.Vendor.GreenBounds

/-!
# The lattice Green's function on `ℤ^d`, `d ≥ 3`

`latticeGreen d x = ∫_0^∞ p_t(x) dt`, with `p_t(x) = ∏_μ q_t(x_μ)` the heat kernel of the
nearest-neighbour continuous-time random walk.  It is nonnegative, satisfies
`-Δ C = δ₀` and `C(x) → 0` as `|x| → ∞`.

Provenance: copied from `Balaban/Green/Lattice/LatticeGreen.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit `493e9eb`, Apache License 2.0
(`LICENSE-balaban-lean`); the only change is the import path.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Set Filter Topology

variable {d : ℕ}

/-- The lattice Green's function `C(x) = ∫_0^∞ p_t(x) dt` of the nearest-neighbour Laplacian on
`ℤ^d`. -/
def latticeGreen (d : ℕ) (x : Fin d → ℤ) : ℝ := ∫ t in Ioi 0, heatKernel d t x

theorem heatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℤ) : 0 ≤ heatKernel d t x :=
  Finset.prod_nonneg fun _ _ => heatKernel1_nonneg ht _

theorem continuous_heatKernel (x : Fin d → ℤ) : Continuous fun t => heatKernel d t x :=
  continuous_finsetProd _ fun _ _ => continuous_heatKernel1 _

theorem heatKernel_integrableOn (hd : 3 ≤ d) (x : Fin d → ℤ) :
    IntegrableOn (fun t => heatKernel d t x) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := heatDiffProd_integral_bound hd 0 (fun _ => Nat.zero_le _)
  have := (hC x).1
  simpa [heatDiffProd_zero] using this

theorem latticeGreen_nonneg (x : Fin d → ℤ) : 0 ≤ latticeGreen d x :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => heatKernel_nonneg (le_of_lt ht) x

theorem heatKernel_eq_mul_erase (t : ℝ) (x : Fin d → ℤ) (μ : Fin d) :
    heatKernel d t x = heatKernel1 t (x μ) * ∏ ν ∈ Finset.univ.erase μ, heatKernel1 t (x ν) :=
  (Finset.mul_prod_erase Finset.univ (fun ν => heatKernel1 t (x ν)) (Finset.mem_univ μ)).symm

theorem heatKernel_shift_pos (t : ℝ) (x : Fin d → ℤ) (μ : Fin d) :
    heatKernel d t (x + Pi.single μ 1) =
      heatKernel1 t (x μ + 1) * ∏ ν ∈ Finset.univ.erase μ, heatKernel1 t (x ν) := by
  rw [heatKernel_eq_mul_erase t _ μ]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun ν hν => ?_
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hν), add_zero]

theorem heatKernel_shift_neg (t : ℝ) (x : Fin d → ℤ) (μ : Fin d) :
    heatKernel d t (x - Pi.single μ 1) =
      heatKernel1 t (x μ - 1) * ∏ ν ∈ Finset.univ.erase μ, heatKernel1 t (x ν) := by
  rw [heatKernel_eq_mul_erase t _ μ]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun ν hν => ?_
    rw [Pi.sub_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hν), sub_zero]

/-- The discrete Laplacian of `p_t` at `x`, written as `-(∂_t p_t)(x)`. -/
def heatLaplacian (d : ℕ) (t : ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ μ : Fin d, (2 * heatKernel d t x - heatKernel d t (x + Pi.single μ 1) -
    heatKernel d t (x - Pi.single μ 1))

theorem hasDerivAt_heatKernel (t : ℝ) (x : Fin d → ℤ) :
    HasDerivAt (fun s => heatKernel d s x) (-heatLaplacian d t x) t := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := t)
    (f := fun (μ : Fin d) (s : ℝ) => heatKernel1 s (x μ))
    (f' := fun μ => heatKernel1 t (x μ + 1) + heatKernel1 t (x μ - 1) - 2 * heatKernel1 t (x μ))
    (fun μ _ => hasDerivAt_heatKernel1 t (x μ))
  refine (show HasDerivAt (fun s => heatKernel d s x) _ t from h).congr_deriv ?_
  unfold heatLaplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [heatKernel_shift_pos, heatKernel_shift_neg, heatKernel_eq_mul_erase t x μ]
  simp only [smul_eq_mul]
  ring

theorem heatKernel_zero_time (x : Fin d → ℤ) :
    heatKernel d 0 x = if x = 0 then 1 else 0 := by
  unfold heatKernel
  simp_rw [heatKernel1_zero]
  by_cases hx : x = 0
  · subst hx; simp
  · obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    simp only [hx, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])

theorem heatKernel_tendsto_zero (hd : 1 ≤ d) (x : Fin d → ℤ) :
    Tendsto (fun T => heatKernel d T x) atTop (𝓝 0) := by
  have hs : Tendsto (fun T : ℝ => (Real.sqrt T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h1 : Tendsto (fun T : ℝ => (10000 * (Real.sqrt T)⁻¹) ^ d) atTop (𝓝 0) := by
    have := (hs.const_mul 10000).pow d
    simpa [zero_pow (by omega : d ≠ 0)] using this
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [Real.norm_eq_abs]
  unfold heatKernel
  rw [Finset.abs_prod]
  have h2 : ∀ μ : Fin d, |heatKernel1 T (x μ)| ≤ 10000 * (Real.sqrt T)⁻¹ := by
    intro μ
    have h := abs_heatDiff_le_large (m := 0) (Nat.zero_le 2) hT (x μ)
    have hE := Elarge_le_two (by linarith : 0 < T) (x μ)
    have hsn : 0 ≤ (Real.sqrt T)⁻¹ := by positivity
    simp only [heatDiff, zero_add, pow_one] at h
    calc |heatKernel1 T (x μ)| ≤ 5000 * (Real.sqrt T)⁻¹ *
          (Real.exp (-((x μ : ℝ) ^ 2 / (16 * T))) + Real.exp (-(|(x μ : ℝ)| / 4))) := h
      _ ≤ 5000 * (Real.sqrt T)⁻¹ * 2 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 10000 * (Real.sqrt T)⁻¹ := by ring
  calc ∏ μ, |heatKernel1 T (x μ)| ≤ ∏ _μ : Fin d, (10000 * (Real.sqrt T)⁻¹) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun μ _ => h2 μ
    _ = (10000 * (Real.sqrt T)⁻¹) ^ d := by simp

theorem continuous_heatLaplacian (x : Fin d → ℤ) : Continuous fun t => heatLaplacian d t x := by
  unfold heatLaplacian
  exact continuous_finsetSum _ fun μ _ =>
    ((continuous_const.mul (continuous_heatKernel x)).sub
      (continuous_heatKernel (x + Pi.single μ 1))).sub (continuous_heatKernel (x - Pi.single μ 1))

theorem integral_heatLaplacian_Ioc (T : ℝ) (x : Fin d → ℤ) :
    ∫ t in (0 : ℝ)..T, heatLaplacian d t x = heatKernel d 0 x - heatKernel d T x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := T)
    (f := fun s => heatKernel d s x) (f' := fun t => -heatLaplacian d t x)
    (fun t _ => hasDerivAt_heatKernel t x)
    ((continuous_heatLaplacian x).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem latticeGreen_equation (hd : 3 ≤ d) (x : Fin d → ℤ) :
    ∑ μ : Fin d, (2 * latticeGreen d x - latticeGreen d (x + Pi.single μ 1) -
      latticeGreen d (x - Pi.single μ 1)) = if x = 0 then 1 else 0 := by
  have hint : ∀ y : Fin d → ℤ, IntegrableOn (fun t => heatKernel d t y) (Ioi 0) :=
    heatKernel_integrableOn hd
  have hterm : ∀ μ : Fin d, IntegrableOn (fun t => 2 * heatKernel d t x -
      heatKernel d t (x + Pi.single μ 1) - heatKernel d t (x - Pi.single μ 1)) (Ioi 0) :=
    fun μ => (((hint x).const_mul 2).sub (hint _)).sub (hint _)
  have hgi : IntegrableOn (fun t => heatLaplacian d t x) (Ioi 0) := by
    unfold heatLaplacian
    exact integrable_finsetSum _ fun μ _ => hterm μ
  have hsum : ∑ μ : Fin d, (2 * latticeGreen d x - latticeGreen d (x + Pi.single μ 1) -
      latticeGreen d (x - Pi.single μ 1)) = ∫ t in Ioi 0, heatLaplacian d t x := by
    unfold heatLaplacian
    rw [integral_finsetSum _ fun μ _ => hterm μ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have i1 : IntegrableOn (fun t => 2 * heatKernel d t x -
        heatKernel d t (x + Pi.single μ 1)) (Ioi 0) := ((hint x).const_mul 2).sub (hint _)
    have i2 : IntegrableOn (fun t => 2 * heatKernel d t x) (Ioi 0) := (hint x).const_mul 2
    rw [integral_sub i1 (hint _), integral_sub i2 (hint _), integral_const_mul]
    rfl
  rw [hsum]
  have hlim1 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, heatLaplacian d t x) atTop
      (𝓝 (∫ t in Ioi 0, heatLaplacian d t x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id
  have hlim2 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, heatLaplacian d t x) atTop
      (𝓝 (heatKernel d 0 x - 0)) := by
    have h := (tendsto_const_nhds (x := heatKernel d 0 x)).sub (heatKernel_tendsto_zero (by omega) x)
    refine h.congr' ?_
    filter_upwards with T
    exact (integral_heatLaplacian_Ioc T x).symm
  rw [tendsto_nhds_unique hlim1 hlim2, sub_zero, heatKernel_zero_time]

/-- A finite-supremum constant: if each `μ` has a bound `C μ ≥ 0` then `∑ C μ` bounds all. -/
theorem exists_uniform_bound {ι : Type*} [Fintype ι] {P : ι → ℝ → Prop}
    (h : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ P i C) (mono : ∀ i C C', C ≤ C' → P i C → P i C') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, P i C := by
  choose C hC0 hC using h
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i => ?_⟩
  exact mono i _ _ (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)) (hC i)

theorem latticeGreen_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin d → ℤ, latticeGreen d x ≤ c / (1 + ‖x‖) ^ (d - 2) := by
  obtain ⟨C, hC0, hC⟩ := heatDiffProd_integral_bound hd 0 (fun _ => Nat.zero_le _)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := (hC x).2
  simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero] at h
  refine le_trans (le_of_eq ?_) h
  unfold latticeGreen
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [heatDiffProd_zero]
  exact (abs_of_nonneg (heatKernel_nonneg (le_of_lt ht) x)).symm

theorem latticeGreen_tendsto_zero (hd : 3 ≤ d) : Tendsto (latticeGreen d) cofinite (𝓝 0) := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_le hd
  have hfin : ∀ R : ℝ, {x : Fin d → ℤ | ‖x‖ ≤ R}.Finite := by
    intro R
    have : {x : Fin d → ℤ | ‖x‖ ≤ R} ⊆ Set.pi Set.univ (fun _ => Finset.Icc (-⌈R⌉) ⌈R⌉ : Fin d → Set ℤ) := by
      intro x hx i _
      have h1 : ‖x i‖ ≤ R := (norm_le_pi_norm x i).trans hx
      rw [Int.norm_eq_abs] at h1
      have h2 : |x i| ≤ ⌈R⌉ := by
        have : ((|x i| : ℤ) : ℝ) ≤ R := by simpa using h1
        exact Int.cast_le.mp (this.trans (Int.le_ceil R))
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact abs_le.mp h2
    exact (Set.Finite.pi (fun _ => (Finset.finite_toSet _))).subset this
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd2 : 1 ≤ d - 2 := by omega
  -- choose R with c / (1 + R)^(d-2) < ε
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ c / (1 + R) < ε := by
    refine ⟨c / ε, by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have : c / ε * ε = c := div_mul_cancel₀ c hε.ne'
    nlinarith
  have hev : ∀ᶠ x : Fin d → ℤ in cofinite, R < ‖x‖ := by
    rw [Filter.eventually_cofinite]
    refine (hfin R).subset fun x hx => ?_
    simpa using hx
  filter_upwards [hev] with x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (latticeGreen_nonneg x)]
  refine lt_of_le_of_lt (hc x) ?_
  have h1 : 1 + R ≤ 1 + ‖x‖ := by linarith
  have h2 : (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (d - 2) := by
    calc (1 + ‖x‖) = (1 + ‖x‖) ^ 1 := (pow_one _).symm
      _ ≤ (1 + ‖x‖) ^ (d - 2) := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hd2
  calc c / (1 + ‖x‖) ^ (d - 2) ≤ c / (1 + ‖x‖) :=
        div_le_div_of_nonneg_left hc0 (by linarith [norm_nonneg x]) h2
    _ ≤ c / (1 + R) := div_le_div_of_nonneg_left hc0 (by linarith) h1
    _ < ε := hR.2

theorem abs_setIntegral_le (f : ℝ → ℝ) :
    |∫ t in Ioi (0 : ℝ), f t| ≤ ∫ t in Ioi (0 : ℝ), |f t| := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f

theorem latticeGreen_shift_sub (hd : 3 ≤ d) (x : Fin d → ℤ) (μ : Fin d) :
    latticeGreen d (x + Pi.single μ 1) - latticeGreen d x =
      ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1) t x := by
  unfold latticeGreen
  rw [← integral_sub (heatKernel_integrableOn hd _) (heatKernel_integrableOn hd _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have := heatDiffProd_shift (0 : Fin d → ℕ) μ t x
  simp only [heatDiffProd_zero, zero_add] at this
  exact this

theorem latticeGreen_shift_shift_sub (hd : 3 ≤ d) (x : Fin d → ℤ) (μ ν : Fin d) :
    latticeGreen d (x + Pi.single μ 1 + Pi.single ν 1) - latticeGreen d (x + Pi.single μ 1) -
      latticeGreen d (x + Pi.single ν 1) + latticeGreen d x =
      ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1 + Pi.single ν 1) t x := by
  have h1 := latticeGreen_shift_sub hd (x + Pi.single ν 1) μ
  have h2 := latticeGreen_shift_sub hd x μ
  have hi : ∀ y : Fin d → ℤ, IntegrableOn (fun t => heatDiffProd d (Pi.single μ 1) t y) (Ioi 0) := by
    intro y
    obtain ⟨C, _, hC⟩ := heatDiffProd_integral_bound hd (Pi.single μ 1) (fun ν => by
      simp only [Pi.single_apply]; split_ifs <;> omega)
    exact (hC y).1
  have h3 : ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1 + Pi.single ν 1) t x =
      (∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1) t (x + Pi.single ν 1)) -
        ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1) t x := by
    rw [← integral_sub (hi _) (hi _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact (heatDiffProd_shift (Pi.single μ 1) ν t x).symm
  rw [h3, ← h1, ← h2, add_right_comm x (Pi.single μ 1) (Pi.single ν 1)]
  ring

theorem latticeGreen_diff1_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ : Fin d),
      |latticeGreen d (x + Pi.single μ 1) - latticeGreen d x| ≤ c / (1 + ‖x‖) ^ (d - 1) := by
  have h : ∀ μ : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℤ,
      |latticeGreen d (x + Pi.single μ 1) - latticeGreen d x| ≤ C / (1 + ‖x‖) ^ (d - 1) := by
    intro μ
    have hm : ∀ ν, (Pi.single μ 1 : Fin d → ℕ) ν ≤ 2 := fun ν => by
      simp only [Pi.single_apply]; split_ifs <;> omega
    obtain ⟨C, hC0, hC⟩ := heatDiffProd_integral_bound hd (Pi.single μ 1) hm
    refine ⟨C, hC0, fun x => ?_⟩
    rw [latticeGreen_shift_sub hd]
    have h := (hC x).2
    have hs : d + ∑ ν, (Pi.single μ 1 : Fin d → ℕ) ν - 2 = d - 1 := by
      simp
    rw [hs] at h
    exact (abs_setIntegral_le _).trans h
  choose C hC0 hC using h
  refine ⟨∑ μ, C μ, Finset.sum_nonneg fun μ _ => hC0 μ, fun x μ => ?_⟩
  exact (hC μ x).trans (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ μ))
    (pow_nonneg (by linarith [norm_nonneg x]) _))

theorem latticeGreen_diff2_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν : Fin d),
      |latticeGreen d (x + Pi.single μ 1 + Pi.single ν 1) - latticeGreen d (x + Pi.single μ 1) -
        latticeGreen d (x + Pi.single ν 1) + latticeGreen d x| ≤ c / (1 + ‖x‖) ^ d := by
  have h : ∀ p : Fin d × Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℤ,
      |latticeGreen d (x + Pi.single p.1 1 + Pi.single p.2 1) - latticeGreen d (x + Pi.single p.1 1) -
        latticeGreen d (x + Pi.single p.2 1) + latticeGreen d x| ≤ C / (1 + ‖x‖) ^ d := by
    intro p
    have hm : ∀ ρ, (Pi.single p.1 1 + Pi.single p.2 1 : Fin d → ℕ) ρ ≤ 2 := fun ρ => by
      simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> omega
    obtain ⟨C, hC0, hC⟩ := heatDiffProd_integral_bound hd _ hm
    refine ⟨C, hC0, fun x => ?_⟩
    rw [latticeGreen_shift_shift_sub hd]
    have hx := (hC x).2
    have hs : d + ∑ ρ, (Pi.single p.1 1 + Pi.single p.2 1 : Fin d → ℕ) ρ - 2 = d := by
      simp [Finset.sum_add_distrib]
    rw [hs] at hx
    exact (abs_setIntegral_le _).trans hx
  choose C hC0 hC using h
  refine ⟨∑ p, C p, Finset.sum_nonneg fun p _ => hC0 p, fun x μ ν => ?_⟩
  exact (hC (μ, ν) x).trans (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ (μ, ν)))
    (pow_nonneg (by linarith [norm_nonneg x]) _))

end Balaban.LatticeGreen
