/-
`lem:real-points` of BALABAN_CORE.tex (`0d76a9bf9596`): holomorphic functions of fields with values in `𝔤^c`.

* `real_points_near`: near a real point of `V` the function vanishes at the points with values in `𝔤^c` (the complex line
  through the real part in the direction of the imaginary part, the identity theorem in one variable).
* `real_points_i`: (i), on all of `D ∩ (𝔤^c)^ι`, along the complex segments from a real point (`D` convex).
* `real_points_ii`: (ii), for matrix-valued functions mapping `V` into `𝔤`, with `(1 - π)F` in place of `F`.

The domain `D` is an open convex subset of `ι → M_N(ℂ)`, and the conclusions are stated at its points with values in
`𝔤^c`, which is the core's `D ⊂ (𝔤^c)^n` for `D` relatively open in `(𝔤^c)^n`.
-/
import CoreLean.RelativeAverageG

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RealPoints

open RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {ι : Type*} [Fintype ι] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

lemma norm_pi_le_of {F H : ι → Mat} (h : ∀ i, ‖F i‖ ≤ ‖H i‖) : ‖F‖ ≤ ‖H‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (h i).trans (norm_le_pi_norm H i)

/-- **Near a real point**: if `F` is holomorphic on the open set `D` and vanishes on the real points near `Z₀ ∈ D`, then it
vanishes at the points near `Z₀` with values in `𝔤^c`. -/
theorem real_points_near (G : GaugeGroup N) (hG : IsClosed G.mats) {D : Set (ι → Mat)} (hD : IsOpen D)
    {F : (ι → Mat) → W} (hF : DifferentiableOn ℂ F D) {Z₀ : ι → Mat} (hZ₀ : Z₀ ∈ D) (hZ₀r : ∀ i, Z₀ i ∈ G.lie)
    {ε : ℝ} (hε : 0 < ε) (h0 : ∀ Z, (∀ i, Z i ∈ G.lie) → ‖Z - Z₀‖ < ε → F Z = 0) :
    ∃ δ > 0, ∀ Z, (∀ i, Z i ∈ G.lieC) → ‖Z - Z₀‖ < δ → F Z = 0 := by
  have hLI := GaugeGroup.lieInput_of_isClosed hG
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hD Z₀ hZ₀
  refine ⟨min ρ ε / 3, by positivity, fun Z hZ hZn => ?_⟩
  have hρ3 : 3 * (min ρ ε / 3) ≤ ρ := by have := min_le_left ρ ε; linarith
  have hε3 : 3 * (min ρ ε / 3) ≤ ε := by have := min_le_right ρ ε; linarith
  -- the real and the imaginary parts of `Z - Z₀`
  have hdiff : ∀ i, Z i - Z₀ i ∈ G.lieC := fun i => (GaugeGroup.mem_lieCSubmodule hLI).1
    ((GaugeGroup.lieCSubmodule (G := G) hLI).sub_mem ((GaugeGroup.mem_lieCSubmodule hLI).2 (hZ i))
      ((GaugeGroup.mem_lieCSubmodule hLI).2 (GaugeGroup.lie_subset_lieC (hZ₀r i))))
  choose Xa hXa Xb hXb hXe hXan hXbn using fun i => lieC_parts (hdiff i)
  have hXa' : ‖(fun i => Xa i : ι → Mat)‖ ≤ ‖Z - Z₀‖ := norm_pi_le_of fun i => hXan i
  have hXb' : ‖(fun i => Xb i : ι → Mat)‖ ≤ ‖Z - Z₀‖ := norm_pi_le_of fun i => hXbn i
  set XA : ι → Mat := fun i => Xa i
  set XB : ι → Mat := fun i => Xb i
  set p : ℂ → (ι → Mat) := fun t => Z₀ + XA + t • XB
  have hpd : ∀ t, ‖t‖ < 2 → ‖p t - Z₀‖ < 3 * (min ρ ε / 3) := fun t ht => by
    have e : p t - Z₀ = XA + t • XB := by simp only [p]; abel
    rw [e]
    have f1 : ‖t • XB‖ ≤ ‖t‖ * ‖Z - Z₀‖ := by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hXb' (norm_nonneg _)
    have := (norm_add_le XA (t • XB)).trans (add_le_add hXa' f1)
    nlinarith [norm_nonneg (Z - Z₀), norm_nonneg t]
  set g : ℂ → W := F ∘ p
  have hgd : DifferentiableOn ℂ g (ball 0 2) := fun t ht => by
    rw [mem_ball_zero_iff] at ht
    have hpD : p t ∈ D := hball (by rw [mem_ball, dist_eq_norm]; linarith [hpd t ht])
    have hpt : DifferentiableAt ℂ p t :=
      (differentiableAt_const (Z₀ + XA)).add (differentiableAt_id.smul_const XB)
    exact ((hF.differentiableAt (hD.mem_nhds hpD)).comp t hpt).differentiableWithinAt
  have hg_real : ∀ s : ℝ, |s| < 1 → g s = 0 := fun s hs => by
    show F (p s) = 0
    refine h0 _ (fun i => ?_) ?_
    · show Z₀ i + Xa i + (s : ℂ) • Xb i ∈ G.lie
      exact GaugeGroup.add_mem_lie hG (GaugeGroup.add_mem_lie hG (hZ₀r i) (hXa i)) (G.smul_mem_lie (hXb i) s)
    · have := hpd s (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)
      linarith
  have han := hgd.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    set s : ℝ := min (r / 2) (1 / 2)
    have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
    refine ⟨(s : ℂ), hrU ⟨?_, ?_⟩, hg_real s ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]; exact hs0.ne'
    · rw [abs_of_pos hs0]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball 0 2).isPreconnected
    (mem_ball_self (by norm_num)) hfreq
  have hI : g Complex.I = 0 := hzero (by rw [mem_ball_zero_iff, Complex.norm_I]; norm_num)
  have hpI : p Complex.I = Z := by
    funext i
    simp only [p, XA, XB, Pi.add_apply, Pi.smul_apply]
    rw [add_assoc, ← hXe i]; abel
  rw [← hpI]; exact hI

/-- **`lem:real-points`(i)**: a function holomorphic on an open convex set `D` which vanishes on a nonempty set `V` of
real points, relatively open among the real points of `D`, vanishes at every point of `D` with values in `𝔤^c`. -/
theorem real_points_i (G : GaugeGroup N) (hG : IsClosed G.mats) {D V : Set (ι → Mat)} (hD : IsOpen D)
    (hDc : Convex ℝ D) (hVD : V ⊆ D) (hVr : ∀ Z ∈ V, ∀ i, Z i ∈ G.lie)
    (hVo : ∀ Z₀ ∈ V, ∃ ε > 0, ∀ Z, (∀ i, Z i ∈ G.lie) → ‖Z - Z₀‖ < ε → Z ∈ V) (hVne : V.Nonempty)
    {F : (ι → Mat) → W} (hF : DifferentiableOn ℂ F D) (h0 : ∀ Z ∈ V, F Z = 0) :
    ∀ Z ∈ D, (∀ i, Z i ∈ G.lieC) → F Z = 0 := by
  have hLI := GaugeGroup.lieInput_of_isClosed hG
  obtain ⟨Z₀, hZ₀⟩ := hVne
  obtain ⟨ε, hε, hεV⟩ := hVo Z₀ hZ₀
  obtain ⟨δ, hδ, hnear⟩ := real_points_near G hG hD hF (hVD hZ₀) (hVr Z₀ hZ₀) hε
    fun Z hZ hZn => h0 Z (hεV Z hZ hZn)
  intro Z hZD hZ
  -- the complex segment from `Z₀` to `Z`
  set q : ℂ → (ι → Mat) := fun t => Z₀ + t • (Z - Z₀)
  set T : Set ℂ := q ⁻¹' D
  have hqc : Continuous q := continuous_const.add (continuous_id.smul continuous_const)
  have hTo : IsOpen T := hD.preimage hqc
  have hTc : Convex ℝ T := by
    have h1 : Convex ℝ ((fun X => Z₀ + X) ⁻¹' D) := hDc.translate_preimage_right Z₀
    have hlin : IsLinearMap ℝ (fun t : ℂ => t • (Z - Z₀)) :=
      ⟨fun x y => add_smul x y _, fun r x => smul_assoc r x _⟩
    exact h1.is_linear_preimage hlin
  have hgd : DifferentiableOn ℂ (F ∘ q) T := fun t ht =>
    ((hF.differentiableAt (hD.mem_nhds ht)).comp t
      ((differentiableAt_const Z₀).add (differentiableAt_id.smul_const (Z - Z₀)))).differentiableWithinAt
  have hq0 : q 0 = Z₀ := by simp [q]
  have hT0 : (0 : ℂ) ∈ T := by show q 0 ∈ D; rw [hq0]; exact hVD hZ₀
  have hT1 : (1 : ℂ) ∈ T := by show q 1 ∈ D; simp only [q, one_smul, add_sub_cancel]; exact hZD
  -- near `t = 0` the segment has values in `𝔤^c` close to `Z₀`
  have hmem : ∀ t : ℂ, ∀ i, q t i ∈ G.lieC := fun t i => (GaugeGroup.mem_lieCSubmodule hLI).1
    ((GaugeGroup.lieCSubmodule (G := G) hLI).add_mem ((GaugeGroup.mem_lieCSubmodule hLI).2 (GaugeGroup.lie_subset_lieC (hVr Z₀ hZ₀ i)))
      ((GaugeGroup.lieCSubmodule (G := G) hLI).smul_mem t ((GaugeGroup.lieCSubmodule (G := G) hLI).sub_mem ((GaugeGroup.mem_lieCSubmodule hLI).2 (hZ i))
        ((GaugeGroup.mem_lieCSubmodule hLI).2 (GaugeGroup.lie_subset_lieC (hVr Z₀ hZ₀ i))))))
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), (F ∘ q) t = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    set s : ℝ := min (r / 2) (δ / (2 * (‖Z - Z₀‖ + 1)))
    have hs0 : 0 < s := lt_min (by positivity) (by positivity)
    refine ⟨(s : ℂ), hrU ⟨?_, ?_⟩, hnear _ (hmem s) ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]; exact hs0.ne'
    · simp only [q, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      have h1 : s ≤ δ / (2 * (‖Z - Z₀‖ + 1)) := min_le_right _ _
      have h2 : s * ‖Z - Z₀‖ ≤ δ / (2 * (‖Z - Z₀‖ + 1)) * (‖Z - Z₀‖ + 1) :=
        mul_le_mul h1 (by linarith) (norm_nonneg _) (by positivity)
      have h3 : δ / (2 * (‖Z - Z₀‖ + 1)) * (‖Z - Z₀‖ + 1) = δ / 2 := by field_simp
      linarith
  have hzero := (hgd.analyticOnNhd hTo).eqOn_zero_of_preconnected_of_frequently_eq_zero hTc.isPreconnected
    hT0 hfreq
  have h1 := hzero hT1
  simp only [Function.comp, q, one_smul, add_sub_cancel] at h1
  exact h1

/-- **`lem:real-points`(ii)**: a matrix-valued function holomorphic on `D` which maps `V` into `𝔤` maps the points of `D`
with values in `𝔤^c` into `𝔤^c`. -/
theorem real_points_ii (G : GaugeGroup N) (hG : IsClosed G.mats) {D V : Set (ι → Mat)} (hD : IsOpen D)
    (hDc : Convex ℝ D) (hVD : V ⊆ D) (hVr : ∀ Z ∈ V, ∀ i, Z i ∈ G.lie)
    (hVo : ∀ Z₀ ∈ V, ∃ ε > 0, ∀ Z, (∀ i, Z i ∈ G.lie) → ‖Z - Z₀‖ < ε → Z ∈ V) (hVne : V.Nonempty)
    {F : (ι → Mat) → Mat} (hF : DifferentiableOn ℂ F D) (hFV : ∀ Z ∈ V, F Z ∈ G.lie) :
    ∀ Z ∈ D, (∀ i, Z i ∈ G.lieC) → F Z ∈ G.lieC := by
  have hLI := GaugeGroup.lieInput_of_isClosed hG
  have hF' : DifferentiableOn ℂ (fun Z => F Z - piL hLI (F Z)) D :=
    hF.sub ((piL hLI).differentiable.comp_differentiableOn hF)
  have h := real_points_i (W := Mat) G hG hD hDc hVD hVr hVo hVne hF' fun Z hZ => by
    show F Z - piProj hLI (F Z) = 0
    rw [piProj_self hLI (GaugeGroup.lie_subset_lieC (hFV Z hZ)), sub_self]
  intro Z hZD hZ
  have e : F Z = piL hLI (F Z) := sub_eq_zero.1 (h Z hZD hZ)
  rw [e]
  exact proj_mem hLI _

end RealPoints
end CoreLean

end
