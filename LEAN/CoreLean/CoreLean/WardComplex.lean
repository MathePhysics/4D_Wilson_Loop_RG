/-
`lem:ward` of BALABAN_CORE.tex, the first statement: a function which is holomorphic near the trivial
configuration and invariant under the gauge transformations is invariant under the complex gauge
transformations near `id`.

The real gauge transformations near `id` are the `e^{iλ}` with `λ` in a real subspace `𝔤 ⊂ 𝔸` (the Lie
algebra of `G` in the physicists' convention, hermitian matrices for `G ⊂ U(N)`), and the complex ones
the `e^{iλ}` with `λ` in a complex subspace `𝔤^c` whose elements decompose as `μ + iν`, `μ, ν ∈ 𝔤`, with
`‖μ‖, ‖ν‖ ≤ K‖μ + iν‖` (`K = 1` for hermitian `μ, ν` and the operator norm). For `λ = μ + iν` the function
`z ↦ E(U^{e^{i(μ + zν)}})` is holomorphic on the disc `|z| < 2` and constant on the real points, hence
constant (the identity theorem in one variable), and its value at `z = i` is `E(U^{e^{iλ}})`: this is the
core's argument ("holomorphic in the values of `u` and constant on the real form `G`").
-/
import CoreLean.WardIdentities

open NormedSpace Filter Asymptotics
open scoped Topology

noncomputable section

namespace CoreLean

namespace Ward

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
variable {Bd St : Type*} [Fintype Bd] [Fintype St]

lemma continuous_exp' : Continuous (exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

lemma continuous_gauge (mn pl : Bd → St) :
    Continuous fun p : (St → 𝔸) × (Bd → 𝔸) => gauge mn pl p.1 p.2 := by
  refine continuous_pi fun b => ?_
  simp only [gauge]
  exact ((continuous_exp'.comp (((continuous_apply (mn b)).comp continuous_fst).const_smul _)).mul
    ((continuous_apply b).comp continuous_snd)).mul
      (continuous_exp'.comp (((continuous_apply (pl b)).comp continuous_fst).const_smul _).neg)

lemma gauge_zero_one (mn pl : Bd → St) : gauge mn pl (0 : St → 𝔸) (1 : Bd → 𝔸) = 1 := by
  funext b; simp [gauge]

lemma analyticAt_gauge_line (mn pl : Bd → St) (μ ν : St → 𝔸) (U : Bd → 𝔸) (z : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => gauge mn pl (μ + z • ν) U) z := by
  refine analyticAt_pi_iff.mpr fun b => ?_
  simp only [gauge, Pi.add_apply, Pi.smul_apply]
  have a1 : AnalyticAt ℂ (fun z : ℂ => Complex.I • (μ (mn b) + z • ν (mn b))) z := by fun_prop
  have a2 : AnalyticAt ℂ (fun z : ℂ => -(Complex.I • (μ (pl b) + z • ν (pl b)))) z := by fun_prop
  exact (((NormedSpace.exp_analytic (𝕂 := ℂ) _).comp a1).mul analyticAt_const).mul
    ((NormedSpace.exp_analytic (𝕂 := ℂ) _).comp a2)

/-- The invariance under the complex gauge transformations near `id`. -/
theorem complex_invariance (mn pl : Bd → St) (g : Submodule ℝ 𝔸) (gc : Submodule ℂ 𝔸) {K : ℝ}
    (hK : 0 ≤ K)
    (hdec : ∀ v ∈ gc, ∃ μ ∈ g, ∃ ν ∈ g, v = μ + Complex.I • ν ∧ ‖μ‖ ≤ K * ‖v‖ ∧ ‖ν‖ ≤ K * ‖v‖)
    (E : (Bd → 𝔸) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hE : AnalyticOnNhd ℂ E (Metric.ball 1 ρ))
    (hreal : ∀ (U : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ g) → U ∈ Metric.ball 1 ρ →
      gauge mn pl l U ∈ Metric.ball 1 ρ → E (gauge mn pl l U) = E U) :
    ∃ ε > 0, ∀ (B : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ gc) → ‖B‖ < ε → ‖l‖ < ε →
      E (gauge mn pl l (expI B)) = E (expI B) := by
  -- the gauge transforms stay in the ball for small `λ` and `U` near `1`
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.mp
    ((continuous_gauge (𝔸 := 𝔸) mn pl).continuousAt (x := ((0 : St → 𝔸), (1 : Bd → 𝔸)))) ρ hρ
  rw [gauge_zero_one] at hgδ
  set δ' := min δ ρ
  have hδ' : 0 < δ' := lt_min hδ hρ
  obtain ⟨η, hη, hexp⟩ := Metric.continuousAt_iff.mp
    (continuous_expI (Bd := Bd) (𝔸 := 𝔸)).continuousAt δ' hδ'
  rw [expI_zero] at hexp
  refine ⟨min η (δ / (3 * K + 1)), lt_min hη (by positivity), fun B l hl hB hlε => ?_⟩
  have hBη : dist B 0 < η := by rw [dist_zero_right]; exact lt_of_lt_of_le hB (min_le_left _ _)
  have hlδ : ‖l‖ < δ / (3 * K + 1) := lt_of_lt_of_le hlε (min_le_right _ _)
  let U := expI B
  have hU : dist U 1 < δ' := hexp hBη
  have hUρ : U ∈ Metric.ball (1 : Bd → 𝔸) ρ := lt_of_lt_of_le hU (min_le_right _ _)
  -- the decomposition `λ = μ + iν`
  choose μf hμg νf hνg hdecf hμn hνn using fun x => hdec (l x) (hl x)
  let μ : St → 𝔸 := μf
  let ν : St → 𝔸 := νf
  have hlμν : l = μ + Complex.I • ν := by funext x; exact hdecf x
  have hμ : ‖μ‖ ≤ K * ‖l‖ := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x =>
    (hμn x).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm l x) hK)
  have hν : ‖ν‖ ≤ K * ‖l‖ := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x =>
    (hνn x).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm l x) hK)
  -- on the disc `|z| < 2`, `μ + zν` is small
  have hsmall : ∀ z : ℂ, ‖z‖ < 2 → gauge mn pl (μ + z • ν) U ∈ Metric.ball (1 : Bd → 𝔸) ρ := by
    intro z hz
    have hn : ‖μ + z • ν‖ < δ := by
      calc ‖μ + z • ν‖ ≤ ‖μ‖ + ‖z‖ * ‖ν‖ := (norm_add_le _ _).trans (by rw [norm_smul])
        _ ≤ K * ‖l‖ + 2 * (K * ‖l‖) :=
            add_le_add hμ (mul_le_mul hz.le hν (norm_nonneg _) (by norm_num))
        _ = 3 * K * ‖l‖ := by ring
        _ < δ := by
            have h3 : 0 ≤ 3 * K := by positivity
            have hl0 := norm_nonneg l
            have : (3 * K + 1) * ‖l‖ < δ := by
              rw [lt_div_iff₀ (by positivity)] at hlδ; linarith
            nlinarith
    have hd : dist ((μ + z • ν), U) ((0 : St → 𝔸), (1 : Bd → 𝔸)) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by rwa [dist_zero_right], lt_of_lt_of_le hU (min_le_left _ _)⟩
    have := hgδ (x := ((μ + z • ν), U)) hd
    exact this
  -- the function of `z`
  set f : ℂ → ℂ := fun z => E (gauge mn pl (μ + z • ν) U)
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 2) := fun z hz =>
    AnalyticAt.comp (g := E) (f := fun z : ℂ => gauge mn pl (μ + z • ν) U)
      (hE _ (hsmall z (by simpa using hz))) (analyticAt_gauge_line mn pl μ ν U z)
  -- `f` is constant on the real points
  have hreal' : ∀ t : ℝ, |t| < 2 → f t = E U := by
    intro t ht
    refine hreal U _ (fun x => ?_) hUρ (hsmall t (by simpa using ht))
    have e : (μ + (t : ℂ) • ν) x = μ x + t • ν x := by
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [Complex.coe_smul]
    rw [e]
    exact g.add_mem (hμg x) (g.smul_mem t (hνg x))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = (fun _ => E U) z := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        rw [Complex.ofReal_zero] at this
        exact this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    refine ht.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    refine hreal' _ ?_
    rw [abs_of_nonneg (by positivity)]
    calc 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ < 2 := by norm_num
  have heq := hf.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    (convex_ball (0 : ℂ) 2).isPreconnected (Metric.mem_ball_self (by norm_num)) hfreq
  have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by simp
  have := heq hI
  simp only [f] at this
  rw [hlμν]
  exact this

/-- The data of `lem:ward` from the real invariance. -/
def WardData.ofReal (mn pl : Bd → St) (g : Submodule ℝ 𝔸) (gc : Submodule ℂ 𝔸)
    (gc_lie : ∀ a ∈ gc, ∀ c ∈ gc, a * c - c * a ∈ gc) {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ v ∈ gc, ∃ μ ∈ g, ∃ ν ∈ g, v = μ + Complex.I • ν ∧ ‖μ‖ ≤ K * ‖v‖ ∧ ‖ν‖ ≤ K * ‖v‖)
    (E : (Bd → 𝔸) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hE : AnalyticOnNhd ℂ E (Metric.ball 1 ρ))
    (hreal : ∀ (U : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ g) → U ∈ Metric.ball 1 ρ →
      gauge mn pl l U ∈ Metric.ball 1 ρ → E (gauge mn pl l U) = E U) : WardData 𝔸 Bd St where
  mn := mn
  pl := pl
  gc := gc
  gc_lie := gc_lie
  E := E
  ρ := ρ
  ε := (complex_invariance mn pl g gc hK hdec E hρ hE hreal).choose
  ρ_pos := hρ
  ε_pos := (complex_invariance mn pl g gc hK hdec E hρ hE hreal).choose_spec.1
  analytic := hE
  inv := (complex_invariance mn pl g gc hK hdec E hρ hE hreal).choose_spec.2

end Ward

end CoreLean
