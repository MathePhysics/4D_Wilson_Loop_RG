/-
`lem:ward` of BALABAN_CORE.tex, the derivatives of the master identity at `B = 0` along a ray.

For `F(B) = E(e^{iB})` and a field `B₀`, `m(s) = DF(sB₀)[H₃(sB₀)]` is `O(s⁴)` (`master`), and
`H₃(sB₀) = h₀ + s h₁ + s²h₂` with `h₀ = λ(b₋) - λ(b₊) = -dλ`, `h₁ = ½X₀(λ(b₋) + λ(b₊))`,
`h₂ = (1/12)X₀²(λ(b₋) - λ(b₊))`, `X₀ = -ad(iB₀(b))`. The `k`-th derivative of `s ↦ DF(sB₀)W` at `0` is
`F^{(k+1)}(0)[B₀, …, B₀, W]` (`iteratedDeriv_ray`), and Taylor's theorem in one variable gives
`m(s) = c₀ + c₁s + c₂s² + c₃s³ + O(s⁴)`; so all `c_n` vanish (`ward_diagonal`). These are the
derivatives of `eq:ward-master` of the orders `0, …, 3` at `B = 0` in the direction `B₀` taken
`n` times.
-/
import CoreLean.WardMaster

open NormedSpace BakerCampbellHausdorff Filter Asymptotics
open scoped Topology

noncomputable section

namespace CoreLean

namespace Ward

section Ray

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- `(B₀, …, B₀, W)` with `k` copies of `B₀`. -/
def rayVec (B₀ W : V) : (k : ℕ) → Fin (k + 1) → V
  | 0 => fun _ => W
  | k + 1 => Fin.cons B₀ (rayVec B₀ W k)

lemma ray_mem {r : ℝ} (hr : 0 < r) (B₀ : V) :
    ∀ᶠ s in 𝓝 (0 : ℂ), s • B₀ ∈ Metric.ball (0 : V) r := by
  have hc : Continuous fun s : ℂ => s • B₀ := continuous_id.smul continuous_const
  have h' : Metric.ball (0 : V) r ∈ 𝓝 ((fun s : ℂ => s • B₀) 0) := by
    simpa using Metric.ball_mem_nhds (0 : V) hr
  exact hc.continuousAt (x := (0 : ℂ)) h'

/-- The derivatives of `s ↦ DF(sB₀)W` at `0`: `F^{(k+1)}(0)[B₀, …, B₀, W]`. -/
lemma iteratedDeriv_ray {F : V → ℂ} {r : ℝ} (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (Metric.ball 0 r))
    (B₀ W : V) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => fderiv ℂ F (s • B₀) W) 0 =
      iteratedFDeriv ℂ (k + 1) F 0 (rayVec B₀ W k) := by
  have key : ∀ k, iteratedDeriv k (fun s : ℂ => fderiv ℂ F (s • B₀) W) =ᶠ[𝓝 0]
      fun s => iteratedFDeriv ℂ (k + 1) F (s • B₀) (rayVec B₀ W k) := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun s => ?_
      simp [iteratedFDeriv_one_apply, rayVec]
    | succ k ih =>
      rw [iteratedDeriv_succ]
      refine ih.deriv.trans ?_
      filter_upwards [ray_mem hr B₀] with s hs
      have hΦ := ((hF.iteratedFDeriv (k + 1)) _ hs).differentiableAt.hasFDerivAt
      have hl : HasDerivAt (fun s : ℂ => s • B₀) B₀ s := by
        simpa using (hasDerivAt_id s).smul_const B₀
      have h2 := hΦ.comp_hasDerivAt s hl
      have h3 : HasDerivAt (fun s : ℂ => iteratedFDeriv ℂ (k + 1) F (s • B₀) (rayVec B₀ W k))
          (fderiv ℂ (iteratedFDeriv ℂ (k + 1) F) (s • B₀) B₀ (rayVec B₀ W k)) s :=
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (k + 1) => V) ℂ
          (rayVec B₀ W k)).hasFDerivAt.comp_hasDerivAt s h2
      rw [h3.deriv]
      simp [iteratedFDeriv_succ_apply_left, rayVec]
  simpa using (key k).self_of_nhds

lemma analyticAt_ray {F : V → ℂ} {r : ℝ} (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (Metric.ball 0 r))
    (B₀ W : V) : AnalyticAt ℂ (fun s : ℂ => fderiv ℂ F (s • B₀) W) 0 := by
  have h1 : AnalyticAt ℂ (fderiv ℂ F) (0 : V) :=
    hF.fderiv _ (Metric.mem_ball_self hr)
  have h2 : AnalyticAt ℂ (fun s : ℂ => s • B₀) 0 := analyticAt_id.smul analyticAt_const
  exact ((ContinuousLinearMap.apply ℂ ℂ W).analyticAt _).comp
    (h1.comp_of_eq h2 (by simp))

end Ray

/-- Taylor's theorem to the third order in one variable, with a remainder `s⁴G(s)`, `G` continuous at `0`. -/
lemma taylor_four {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    ∃ G : ℂ → ℂ, ContinuousAt G 0 ∧ ∀ᶠ s in 𝓝 0,
      g s = iteratedDeriv 0 g 0 + s * iteratedDeriv 1 g 0 + s ^ 2 / 2 * iteratedDeriv 2 g 0 +
        s ^ 3 / 6 * iteratedDeriv 3 g 0 + s ^ 4 * G s := by
  obtain ⟨G, hG, h⟩ := hg.exists_eventuallyEq_sum_add_pow_mul 4
  refine ⟨G, hG.continuousAt, h.mono fun s hs => ?_⟩
  rw [hs]
  simp [Finset.sum_range_succ, Nat.factorial, smul_eq_mul]
  try ring

/-- A function `Q` continuous at `0` with `‖sʲQ(s)‖ ≤ C‖s‖^{j+1}` for small `s ≠ 0` vanishes at `0`. -/
lemma eq_zero_of_pow_bound {Q : ℂ → ℂ} (hQ : ContinuousAt Q 0) {j : ℕ} {C : ℝ}
    (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖s ^ j * Q s‖ ≤ C * ‖s‖ ^ (j + 1)) : Q 0 = 0 := by
  have hb : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Q s‖ ≤ C * ‖s‖ := by
    filter_upwards [h, self_mem_nhdsWithin] with s hs hs0
    have hpos : 0 < ‖s‖ ^ j := pow_pos (norm_pos_iff.mpr hs0) j
    rw [norm_mul, norm_pow, pow_succ] at hs
    have : ‖s‖ ^ j * ‖Q s‖ ≤ ‖s‖ ^ j * (C * ‖s‖) := by linarith
    exact le_of_mul_le_mul_left this hpos
  have h1 : Tendsto (fun s => ‖Q s‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖Q 0‖) :=
    (hQ.norm.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℂ => C * ‖s‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => C * ‖s‖) (𝓝 (0 : ℂ)) (𝓝 (C * ‖(0 : ℂ)‖)) :=
      (continuous_const.mul continuous_norm).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto h1 h2 hb
  exact norm_le_zero_iff.mp this

/-- A cubic polynomial which is `O(s⁴)` at `0` vanishes. -/
lemma cubic_eq_zero {c₀ c₁ c₂ c₃ : ℂ}
    (h : (fun s : ℂ => c₀ + c₁ * s + c₂ * s ^ 2 + c₃ * s ^ 3) =O[𝓝 0] fun s => ‖s‖ ^ 4) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  set C' := max C 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  -- the bound with `‖s‖ < 1` and the nonnegative constant `C'`
  have hC' : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      ‖c₀ + c₁ * s + c₂ * s ^ 2 + c₃ * s ^ 3‖ ≤ C' * ‖s‖ ^ 4 ∧ ‖s‖ < 1 := by
    filter_upwards [hC.filter_mono nhdsWithin_le_nhds, hball] with s hs hs1
    refine ⟨?_, by simpa using hs1⟩
    have : ‖‖s‖ ^ 4‖ = ‖s‖ ^ 4 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [this] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlow : ∀ {s : ℂ} {j : ℕ}, j + 1 ≤ 4 → ‖s‖ < 1 → C' * ‖s‖ ^ 4 ≤ C' * ‖s‖ ^ (j + 1) :=
    fun hj hs => mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) hs.le hj) hC0
  have h0 : c₀ = 0 := by
    have := hC.self_of_nhds
    simpa using this
  subst h0
  have h1 : c₁ = 0 := by
    have := eq_zero_of_pow_bound (Q := fun s => c₁ + c₂ * s + c₃ * s ^ 2) (j := 1) (C := C')
      (by fun_prop) ?_
    · simpa using this
    · filter_upwards [hC'] with s hs
      have e : s ^ 1 * (c₁ + c₂ * s + c₃ * s ^ 2) = 0 + c₁ * s + c₂ * s ^ 2 + c₃ * s ^ 3 := by ring
      rw [e]
      exact hs.1.trans (hlow (by norm_num) hs.2)
  subst h1
  have h2 : c₂ = 0 := by
    have := eq_zero_of_pow_bound (Q := fun s => c₂ + c₃ * s) (j := 2) (C := C') (by fun_prop) ?_
    · simpa using this
    · filter_upwards [hC'] with s hs
      have e : s ^ 2 * (c₂ + c₃ * s) = 0 + 0 * s + c₂ * s ^ 2 + c₃ * s ^ 3 := by ring
      rw [e]
      exact hs.1.trans (hlow (by norm_num) hs.2)
  subst h2
  have h3 : c₃ = 0 := by
    have := eq_zero_of_pow_bound (Q := fun _ => c₃) (j := 3) (C := C') continuousAt_const ?_
    · simpa using this
    · filter_upwards [hC'] with s hs
      have e : s ^ 3 * c₃ = 0 + 0 * s + 0 * s ^ 2 + c₃ * s ^ 3 := by ring
      rw [e]
      exact hs.1
  exact ⟨rfl, rfl, rfl, h3⟩

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
variable {Bd St : Type*} [Fintype Bd] [Fintype St]

/-- `h₀ = λ(b₋) - λ(b₊) = -dλ`. -/
def wh0 (mn pl : Bd → St) (l : St → 𝔸) : Bd → 𝔸 := fun b => l (mn b) - l (pl b)

/-- `h₁ = ½X₀(λ(b₋) + λ(b₊))`, `X₀ = -ad(iB₀(b))`. -/
def wh1 (mn pl : Bd → St) (l : St → 𝔸) (B₀ : Bd → 𝔸) : Bd → 𝔸 :=
  fun b => (2 : ℂ)⁻¹ • adX B₀ b (l (mn b) + l (pl b))

/-- `h₂ = (1/12)X₀²(λ(b₋) - λ(b₊))`. -/
def wh2 (mn pl : Bd → St) (l : St → 𝔸) (B₀ : Bd → 𝔸) : Bd → 𝔸 :=
  fun b => (12 : ℂ)⁻¹ • (adX B₀ b ^ 2) (l (mn b) - l (pl b))

lemma adX_smul (s : ℂ) (B₀ : Bd → 𝔸) (b : Bd) : adX (s • B₀) b = s • adX B₀ b := by
  simp only [adX, Pi.smul_apply]
  rw [smul_comm Complex.I s, ad_smul, smul_neg]

lemma H3_ray (mn pl : Bd → St) (l : St → 𝔸) (B₀ : Bd → 𝔸) (s : ℂ) :
    H3 mn pl l (s • B₀) = wh0 mn pl l + s • wh1 mn pl l B₀ + s ^ 2 • wh2 mn pl l B₀ := by
  funext b
  have hsq : (s • adX B₀ b) ^ 2 = s ^ 2 • adX B₀ b ^ 2 := by
    ext v
    simp only [sq, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      smul_smul]
  simp only [H3, adX_smul, Qm, Qp, wh0, wh1, wh2, Pi.add_apply, Pi.smul_apply, hsq,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply, map_add, map_sub]
  module

/-- The derivatives of the orders `0, 1, 2, 3` of `eq:ward-master` at `B = 0` in the direction `B₀`:
with `F(B) = E(e^{iB})` and `F^{(n)} = D^nF(0)`,
`F^{(1)}[h₀] = 0`, `F^{(2)}[B₀, h₀] + F^{(1)}[h₁] = 0`,
`½F^{(3)}[B₀, B₀, h₀] + F^{(2)}[B₀, h₁] + F^{(1)}[h₂] = 0`, and
`(1/6)F^{(4)}[B₀, B₀, B₀, h₀] + ½F^{(3)}[B₀, B₀, h₁] + F^{(2)}[B₀, h₂] = 0`. -/
theorem ward_diagonal (mn pl : Bd → St) (gc : Submodule ℂ 𝔸) (E : (Bd → 𝔸) → ℂ) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hE : AnalyticOnNhd ℂ E (Metric.ball 1 ρ))
    (hinv : ∀ (B : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ gc) → ‖B‖ < ε → ‖l‖ < ε →
      E (gauge mn pl l (expI B)) = E (expI B))
    (l : St → 𝔸) (hl : ∀ x, l x ∈ gc) (B₀ : Bd → 𝔸) :
    iteratedFDeriv ℂ 1 (E ∘ expI) 0 (rayVec B₀ (wh0 mn pl l) 0) = 0 ∧
    iteratedFDeriv ℂ 2 (E ∘ expI) 0 (rayVec B₀ (wh0 mn pl l) 1) +
      iteratedFDeriv ℂ 1 (E ∘ expI) 0 (rayVec B₀ (wh1 mn pl l B₀) 0) = 0 ∧
    1 / 2 * iteratedFDeriv ℂ 3 (E ∘ expI) 0 (rayVec B₀ (wh0 mn pl l) 2) +
      iteratedFDeriv ℂ 2 (E ∘ expI) 0 (rayVec B₀ (wh1 mn pl l B₀) 1) +
      iteratedFDeriv ℂ 1 (E ∘ expI) 0 (rayVec B₀ (wh2 mn pl l B₀) 0) = 0 ∧
    1 / 6 * iteratedFDeriv ℂ 4 (E ∘ expI) 0 (rayVec B₀ (wh0 mn pl l) 3) +
      1 / 2 * iteratedFDeriv ℂ 3 (E ∘ expI) 0 (rayVec B₀ (wh1 mn pl l B₀) 2) +
      iteratedFDeriv ℂ 2 (E ∘ expI) 0 (rayVec B₀ (wh2 mn pl l B₀) 1) = 0 := by
  set F := E ∘ expI with hFdef
  -- `F` is analytic on a ball about `0`
  obtain ⟨r, hr, hrρ⟩ := Metric.continuousAt_iff.mp (continuous_expI (Bd := Bd) (𝔸 := 𝔸)).continuousAt
    ρ hρ
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 r) := by
    intro B hB
    have hB' : expI B ∈ Metric.ball (1 : Bd → 𝔸) ρ := by
      have := hrρ (Metric.mem_ball.mp hB)
      rwa [expI_zero] at this
    have hexp : AnalyticAt ℂ (expI (Bd := Bd) (𝔸 := 𝔸)) B := by
      refine analyticAt_pi_iff.mpr fun b => ?_
      have hlin : AnalyticAt ℂ (fun B : Bd → 𝔸 => Complex.I • B b) B :=
        ((Complex.I • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Bd => 𝔸) b).analyticAt B)
      exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp hlin
    exact (hE _ hB').comp hexp
  -- the master identity along the ray
  have hm : (fun s : ℂ => fderiv ℂ F (s • B₀) (H3 mn pl l (s • B₀))) =O[𝓝 0] fun s => ‖s‖ ^ 4 := by
    have h1 := (master mn pl gc E hρ hε hE hinv l hl).comp_tendsto
      (show Tendsto (fun s : ℂ => s • B₀) (𝓝 0) (𝓝 0) by
        have := (tendsto_id (x := 𝓝 (0 : ℂ))).smul_const B₀
        rwa [zero_smul] at this)
    refine h1.trans (IsBigO.of_bound (‖B₀‖ ^ 4) (Eventually.of_forall fun s => ?_))
    simp only [Function.comp, norm_smul, mul_pow, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact le_of_eq (by ring)
  -- the three functions `g_W(s) = DF(sB₀)W`
  set g : (Bd → 𝔸) → ℂ → ℂ := fun W s => fderiv ℂ F (s • B₀) W
  have hmg : ∀ s : ℂ, fderiv ℂ F (s • B₀) (H3 mn pl l (s • B₀)) =
      g (wh0 mn pl l) s + s * g (wh1 mn pl l B₀) s + s ^ 2 * g (wh2 mn pl l B₀) s := by
    intro s
    simp only [g, H3_ray, map_add, map_smul, smul_eq_mul]
  obtain ⟨G0, hG0, hT0⟩ := taylor_four (analyticAt_ray hr hF B₀ (wh0 mn pl l))
  obtain ⟨G1, hG1, hT1⟩ := taylor_four (analyticAt_ray hr hF B₀ (wh1 mn pl l B₀))
  obtain ⟨G2, hG2, hT2⟩ := taylor_four (analyticAt_ray hr hF B₀ (wh2 mn pl l B₀))
  set d : (Bd → 𝔸) → ℕ → ℂ := fun W i => iteratedDeriv i (g W) 0
  set c₀ := d (wh0 mn pl l) 0
  set c₁ := d (wh0 mn pl l) 1 + d (wh1 mn pl l B₀) 0
  set c₂ := d (wh0 mn pl l) 2 / 2 + d (wh1 mn pl l B₀) 1 + d (wh2 mn pl l B₀) 0
  set c₃ := d (wh0 mn pl l) 3 / 6 + d (wh1 mn pl l B₀) 2 / 2 + d (wh2 mn pl l B₀) 1
  set K : ℂ → ℂ := fun s => G0 s + d (wh1 mn pl l B₀) 3 / 6 + s * G1 s + d (wh2 mn pl l B₀) 2 / 2 +
    s * (d (wh2 mn pl l B₀) 3 / 6) + s ^ 2 * G2 s
  have hK : ContinuousAt K 0 := by
    simp only [K]
    exact ((((hG0.add continuousAt_const).add (continuousAt_id.mul hG1)).add continuousAt_const).add
      (continuousAt_id.mul continuousAt_const)).add ((continuousAt_id.pow 2).mul hG2)
  have hpoly : (fun s : ℂ => c₀ + c₁ * s + c₂ * s ^ 2 + c₃ * s ^ 3) =O[𝓝 0] fun s => ‖s‖ ^ 4 := by
    have hKb : (fun s : ℂ => s ^ 4 * K s) =O[𝓝 0] fun s => ‖s‖ ^ 4 := by
      have : (fun s : ℂ => K s) =O[𝓝 0] fun _ => (1 : ℝ) := hK.isBigO_one ℝ
      have h4 : (fun s : ℂ => s ^ 4) =O[𝓝 0] fun s => ‖s‖ ^ 4 :=
        IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp [norm_pow])
      simpa using h4.mul this
    refine ((hm.sub hKb).congr' ?_ EventuallyEq.rfl)
    filter_upwards [hT0, hT1, hT2] with s h0 h1 h2
    rw [hmg s]
    simp only [g, d, c₀, c₁, c₂, c₃, K] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
    ring
  obtain ⟨e0, e1, e2, e3⟩ := cubic_eq_zero hpoly
  have hd : ∀ W k, d W k = iteratedFDeriv ℂ (k + 1) F 0 (rayVec B₀ W k) := fun W k =>
    iteratedDeriv_ray hr hF B₀ W k
  simp only [c₀, c₁, c₂, c₃, hd] at e0 e1 e2 e3
  refine ⟨e0, e1, ?_, ?_⟩
  · rw [← e2]; ring
  · rw [← e3]; ring

end Ward

end CoreLean
