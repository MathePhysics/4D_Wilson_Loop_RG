/-
`def:distance` of BALABAN_CORE.tex (`ea68ea6e3640`) with the core's paths: Lipschitz paths `γ : [0, 1] → 𝕋`.

`Distance.lean` defines the weighted distance (`wdist`) with Lipschitz lifts `γ̃ : ℝ → ℝ⁴` on parameter intervals
`[0, T]`. Here the core's definition is formalised and shown to give the same distance (`udist_eq_wdist`).

A path is a map `γ : ℝ → 𝕋` which is Lipschitz on `[0, 1]` (`UPath`; only its values on `[0, 1]` enter). The speed
`|γ̇_ν(t)|` of a coordinate is the limit of `‖γ_ν(t + h) - γ_ν(t)‖/|h|` as `h → 0` (`speed`), the metric
derivative in the circle, and `|γ̇(t)|₁ = Σ_ν |γ̇_ν(t)|`; the weighted length is
`ℓ(γ) = ∫_0^1 a_{j(γ(t))}⁻¹ |γ̇(t)|₁ dt` (`ulen`).

* `speed_of_lift`: where a local lift has the derivative `d`, the speed is `|d|`.
* `exists_lift`: a Lipschitz path of a circle on `[0, 1]` has a lift which is Lipschitz on `ℝ` with the same
  constant (from the path lifting of the covering `ℝ → ℝ/pℤ`; a lift moves by less than `p/2` over a short
  interval, by the intermediate value theorem).
* `ulen_lift`: `ℓ(π ∘ γ̃) = ∫_0^1 a_{j}⁻¹ |γ̃'|₁` (Rademacher's theorem for the coordinates of `γ̃`).
* `wlen_rescale`: the weighted length of a lift on `[0, T]` is that of `t ↦ γ̃(Tt)` on `[0, 1]`.
-/
import CoreLean.Distance
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.CompMul

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

noncomputable section

namespace CoreLean

variable {p : ℝ}

/-! ### The speed of a path of the circle -/

/-- The speed `lim_{h → 0} ‖c(t + h) - c(t)‖/|h|` of a path of the circle `ℝ/pℤ`. -/
def speed (c : ℝ → AddCircle p) (t : ℝ) : ℝ := limUnder (𝓝[≠] (0 : ℝ)) fun h => ‖c (t + h) - c t‖ / |h|

/-- **Where a local lift has the derivative `d`, the speed is `|d|`.** -/
theorem speed_of_lift (hp : 0 < p) {c : ℝ → AddCircle p} {f : ℝ → ℝ} {t d : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, c s = (f s : AddCircle p)) (hf : HasDerivAt f d t) : speed c t = |d| := by
  have hcont : ContinuousAt f t := hf.continuousAt
  -- near `0`, the difference of the lift is small and `c` is the projection of `f`
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), |f (t + h) - f t| ≤ p / 2 ∧ c (t + h) = (f (t + h) : AddCircle p) := by
    have h1 : Tendsto (fun h => f (t + h) - f t) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun h => t + h) (𝓝 (0 : ℝ)) (𝓝 t) := by
        have := (tendsto_const_nhds (x := t)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
        simpa using this
      simpa using ((hcont.tendsto.comp this).sub_const (f t))
    have h2 : ∀ᶠ h in 𝓝 (0 : ℝ), |f (t + h) - f t| ≤ p / 2 := by
      have := h1.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < p / 2))
      filter_upwards [this] with h hh
      simpa [Real.dist_eq] using hh
    have h3 : ∀ᶠ h in 𝓝 (0 : ℝ), c (t + h) = (f (t + h) : AddCircle p) := by
      have : Tendsto (fun h => t + h) (𝓝 (0 : ℝ)) (𝓝 t) := by
        have := (tendsto_const_nhds (x := t)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
        simpa using this
      exact this.eventually hc
    filter_upwards [h2, h3] with h a b using ⟨a, b⟩
  have hct : c t = (f t : AddCircle p) := by
    have := hc.self_of_nhds; exact this
  have heq : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖c (t + h) - c t‖ / |h| = |h⁻¹ • (f (t + h) - f t)| := by
    filter_upwards [nhdsWithin_le_nhds hsmall] with h ⟨hs, hc'⟩
    rw [hc', hct, ← AddCircle.coe_sub, (AddCircle.norm_coe_eq_abs_iff _ hp.ne').2 (by rwa [abs_of_pos hp]),
      smul_eq_mul, abs_mul, abs_inv, div_eq_inv_mul]
  have hlim : Tendsto (fun h => ‖c (t + h) - c t‖ / |h|) (𝓝[≠] (0 : ℝ)) (𝓝 |d|) :=
    (((hasDerivAt_iff_tendsto_slope_zero.1 hf).abs).congr' (EventuallyEq.symm heq))
  exact hlim.limUnder_eq

/-- The speed of a constant path is `0`. -/
lemma speed_const (q : AddCircle p) (t : ℝ) : speed (fun _ => q) t = 0 := by
  have : Tendsto (fun h : ℝ => ‖q - q‖ / |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by simp
  exact this.limUnder_eq

/-! ### Paths on `[0, 1]` and their weighted length -/

/-- A Lipschitz path `γ : [0, 1] → 𝕋` from `z` to `z'` (only its values on `[0, 1]` enter). -/
structure UPath (p : ℝ) (z z' : Tor p) where
  γ : ℝ → Tor p
  K : ℝ≥0
  lip : LipschitzOnWith K γ (Icc 0 1)
  start : γ 0 = z
  stop : γ 1 = z'

/-- **The weighted length `ℓ(γ) = ∫_0^1 a_{j(γ(t))}⁻¹ |γ̇(t)|₁ dt` of `eq:weighted-length`.** -/
def ulen (D : DomainData p) (γ : ℝ → Tor p) : ℝ≥0∞ :=
  ∫⁻ t in Icc 0 1, ENNReal.ofReal (D.weight (γ t)) * ∑ ν, ENNReal.ofReal (speed (fun s => γ s ν) t)

/-- **The weighted distance of `def:distance`**: the infimum of `ℓ(γ)` over the Lipschitz paths from `z` to `z'`. -/
def udist (D : DomainData p) (z z' : Tor p) : ℝ≥0∞ := ⨅ P : UPath p z z', ulen D P.γ

lemma lipschitz_projT : LipschitzWith 1 (projT p) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun ν => ?_
  rw [dist_eq_norm]
  refine (norm_coe_sub_le (x ν) (y ν)).trans ?_
  rw [← Real.dist_eq]
  exact dist_le_pi_dist x y ν

/-- **`ℓ(π ∘ γ̃) = ∫_0^1 a_j⁻¹ |γ̃'|₁`** for a path which is the projection of a Lipschitz lift on `[0, 1]`. -/
theorem ulen_lift (hp : 0 < p) (D : DomainData p) {γ : ℝ → Tor p} {γt : ℝ → (Fin 4 → ℝ)} {K : ℝ≥0}
    (hlip : LipschitzWith K γt) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t = projT p (γt t)) :
    ulen D γ = wlen D γt 0 1 := by
  unfold ulen wlen wIntegrand
  have hcoord : ∀ ν, LipschitzWith K fun s => γt s ν := fun ν =>
    LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist _ _ ν).trans (hlip.dist_le_mul x y)
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), ∀ ν, DifferentiableAt ℝ (fun s => γt s ν) t :=
    ae_all_iff.2 fun ν => (hcoord ν).ae_differentiableAt
  have hends : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 ∧ t ≠ 1 := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [h0, h1] with t a b using ⟨a, b⟩
  refine setLIntegral_congr_fun_ae measurableSet_Icc ?_
  filter_upwards [hdiff, hends] with t ht ⟨h0, h1⟩ hti
  have hti' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hti.1 (Ne.symm h0), lt_of_le_of_ne hti.2 h1⟩
  rw [hγ t hti]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hev : ∀ᶠ s in 𝓝 t, (fun s => γ s ν) s = ((γt s ν : ℝ) : AddCircle p) := by
    filter_upwards [Ioo_mem_nhds hti'.1 hti'.2] with s hs
    rw [hγ s ⟨hs.1.le, hs.2.le⟩]; rfl
  rw [speed_of_lift hp hev (ht ν).hasDerivAt, Real.eNorm_eq_ofReal_abs]

/-- **Rescaling the parameter interval**: the weighted length of `γ̃` on `[0, T]` is that of `t ↦ γ̃(Tt)` on
`[0, 1]`. -/
theorem wlen_rescale (D : DomainData p) (γt : ℝ → (Fin 4 → ℝ)) {T : ℝ} (hT : 0 < T) :
    wlen D (fun t => γt (T * t)) 0 1 = wlen D γt 0 T := by
  unfold wlen
  have himg : (fun x : ℝ => T * x) '' Icc 0 1 = Icc 0 T := by
    rw [image_mul_left_Icc hT.le zero_le_one, mul_zero, mul_one]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul (f := fun x => T * x) (f' := fun _ => T)
    measurableSet_Icc
    (fun x _ => ((hasDerivAt_id' x).const_mul T).hasDerivWithinAt.congr_deriv (mul_one T))
    (fun x _ y _ h => mul_left_cancel₀ hT.ne' h)]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  simp only [wIntegrand]
  have hd : ∀ ν, deriv (fun s => γt (T * s) ν) t = T * deriv (fun s => γt s ν) (T * t) := fun ν => by
    have := deriv_comp_mul_left (f := fun s => γt s ν) (c := T) (x := t)
    simpa using this
  simp only [hd, eNorm_mul, Real.eNorm_eq_ofReal_abs, abs_of_pos hT, ← Finset.mul_sum]
  ring

/-! ### Lifts of Lipschitz paths of the circle -/

/-- A function which is `K`-Lipschitz at scales `≤ δ` on `[0, 1]` is `K`-Lipschitz on `[0, 1]`. -/
lemma lipschitz_of_local {f : ℝ → ℝ} {K δ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hloc : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, y ≤ x → x - y ≤ δ → |f x - f y| ≤ K * (x - y)) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ K * |x - y| := by
  have key : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, y ≤ x → x - y ≤ n * δ →
      |f x - f y| ≤ K * (x - y) := by
    intro n
    induction n with
    | zero =>
      intro x hx y hy hyx hn
      have : x = y := by push_cast at hn; linarith
      subst this; simp
    | succ n ih =>
      intro x hx y hy hyx hn
      by_cases hs : x - y ≤ δ
      · exact hloc x hx y hy hyx hs
      push Not at hs
      have hz : x - δ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hx.2]⟩
      have h1 := hloc x hx (x - δ) hz (by linarith) (by linarith)
      have h2 := ih (x - δ) hz y hy (by linarith) (by push_cast at hn; linarith)
      calc |f x - f y| = |(f x - f (x - δ)) + (f (x - δ) - f y)| := by ring_nf
        _ ≤ |f x - f (x - δ)| + |f (x - δ) - f y| := abs_add_le _ _
        _ ≤ K * (x - (x - δ)) + K * (x - δ - y) := add_le_add h1 h2
        _ = K * (x - y) := by ring
  intro x hx y hy
  obtain ⟨n, hn⟩ := exists_nat_ge (|x - y| / δ)
  have hn' : |x - y| ≤ n * δ := by rwa [div_le_iff₀ hδ] at hn
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hyx)] at hn' ⊢
    exact key n x hx y hy hyx hn'
  · rw [abs_sub_comm (f x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy)]
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy)] at hn'
    exact key n y hy x hx hxy hn'

/-- **A Lipschitz path of the circle on `[0, 1]` has a lift which is Lipschitz on `ℝ` with the same constant.** -/
theorem exists_lift (hp : 0 < p) {c : ℝ → AddCircle p} {K : ℝ≥0} (hc : LipschitzOnWith K c (Icc 0 1)) :
    ∃ f : ℝ → ℝ, LipschitzWith K f ∧ ∀ t ∈ Icc (0 : ℝ) 1, c t = (f t : AddCircle p) := by
  -- the path on the unit interval and its lift
  let cI : C(I, AddCircle p) := ⟨fun t => c t, hc.continuousOn.comp_continuous continuous_subtype_val
    fun t => t.2⟩
  obtain ⟨e, he⟩ := QuotientAddGroup.mk_surjective (c 0)
  obtain ⟨Γ, hΓ, -⟩ := (AddCircle.isCoveringMap_coe p).exists_path_lifts cI e (by
    show c 0 = _; rw [← he])
  have hΓc : ∀ t : I, c t = (Γ t : AddCircle p) := fun t => (congrFun hΓ t).symm
  let g : ℝ → ℝ := fun t => Γ (projIcc 0 1 zero_le_one t)
  have hg : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), g t = Γ ⟨t, ht⟩ := fun t ht => by
    simp only [g, projIcc_of_mem _ ht]
  have hgc : ContinuousOn g (Icc 0 1) :=
    (Γ.continuous.comp continuous_projIcc).continuousOn
  have hgcI : ∀ t ∈ Icc (0 : ℝ) 1, c t = (g t : AddCircle p) := fun t ht => by
    rw [hg t ht]; exact hΓc ⟨t, ht⟩
  -- the local estimate
  set δ : ℝ := p / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have hKδ : (K : ℝ) * δ < p / 2 := by
    simp only [δ]
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [K.coe_nonneg]
  have hloc : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, y ≤ x → x - y ≤ δ →
      |g x - g y| ≤ K * (x - y) := by
    intro x hx y hy hyx hxy
    have hnorm : ∀ u ∈ Icc y x, ‖((g u - g y : ℝ) : AddCircle p)‖ ≤ K * (u - y) := by
      intro u hu
      have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hy.1.trans hu.1, hu.2.trans hx.2⟩
      rw [AddCircle.coe_sub, ← hgcI u huI, ← hgcI y hy, ← dist_eq_norm]
      have := hc.dist_le_mul u huI y hy
      rwa [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])] at this
    -- the lift stays within `p/2` of `g y` on `[y, x]`
    have hstay : ∀ u ∈ Icc y x, |g u - g y| < p / 2 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨u, hu, hu'⟩ := hcon
      have hcontu : ContinuousOn (fun v => |g v - g y|) (Icc y u) :=
        ((hgc.mono fun v (hv : v ∈ Icc y u) => ⟨hy.1.trans hv.1, hv.2.trans (hu.2.trans hx.2)⟩).sub
          continuousOn_const).abs
      have hyu : y ≤ u := hu.1
      obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc (a := y) (b := u) (f := fun v => |g v - g y|) hyu hcontu
        (show p / 2 ∈ Icc (|g y - g y|) (|g u - g y|) from ⟨by simp only [sub_self, abs_zero]; positivity, hu'⟩)
      have hv' : |g v - g y| = p / 2 := hv0
      have hvI : v ∈ Icc y x := ⟨hv.1, hv.2.trans hu.2⟩
      have h1 := hnorm v hvI
      rw [(AddCircle.norm_coe_eq_abs_iff _ hp.ne').2 (by rw [hv', abs_of_pos hp]), hv'] at h1
      have : (K : ℝ) * (v - y) ≤ K * δ := mul_le_mul_of_nonneg_left (by linarith [hv.2, hu.2]) K.coe_nonneg
      linarith
    have h1 := hnorm x ⟨hyx, le_rfl⟩
    rwa [(AddCircle.norm_coe_eq_abs_iff _ hp.ne').2 (by rw [abs_of_pos hp]; exact (hstay x ⟨hyx, le_rfl⟩).le)] at h1
  have hglob := lipschitz_of_local hδ K.coe_nonneg hloc
  refine ⟨g, LipschitzWith.of_dist_le_mul fun x y => ?_, hgcI⟩
  have hx := (projIcc 0 1 zero_le_one x).2
  have hy := (projIcc 0 1 zero_le_one y).2
  have e1 : g x = g (projIcc 0 1 zero_le_one x) := by simp only [g, projIcc_val]
  have e2 : g y = g (projIcc 0 1 zero_le_one y) := by simp only [g, projIcc_val]
  rw [Real.dist_eq, Real.dist_eq, e1, e2]
  refine (hglob _ hx _ hy).trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
  have := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] at this
  exact this

/-! ### The two weighted distances agree -/

/-- **The weighted distance with the core's paths on `[0, 1]` is the weighted distance with lifts on `[0, T]`.** -/
theorem udist_eq_wdist (hp : 0 < p) (D : DomainData p) (z z' : Tor p) : udist D z z' = wdist D z z' := by
  apply le_antisymm
  · -- a lift on `[0, T]` gives a path on `[0, 1]` with the same length
    refine le_iInf fun P => ?_
    rcases eq_or_lt_of_le P.T_nonneg with hT | hT
    · -- the constant path
      have hzz : z = z' := by
        have h1 := P.start
        have h2 := P.stop
        rw [← hT] at h2
        exact h1.symm.trans h2
      subst hzz
      let Q : UPath p z z := ⟨fun _ => z, 0, LipschitzWith.const' z |>.lipschitzOnWith, rfl, rfl⟩
      refine (iInf_le _ Q).trans ?_
      have : ulen D Q.γ = 0 := by
        unfold ulen
        simp only [Q, speed_const, ENNReal.ofReal_zero, Finset.sum_const_zero, mul_zero, lintegral_zero]
      rw [this]; exact bot_le
    · let γt : ℝ → (Fin 4 → ℝ) := fun t => P.γ (P.T * t)
      have hmul : LipschitzWith P.T.toNNReal fun t : ℝ => P.T * t := LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hT, Real.coe_toNNReal _ hT.le]
      have hlip : LipschitzWith (P.K * P.T.toNNReal) γt := P.lip.comp hmul
      let Q : UPath p z z' := ⟨fun t => projT p (γt t), P.K * P.T.toNNReal,
        ((lipschitz_projT.comp hlip).lipschitzOnWith).weaken (by simp),
        by simp only [γt, mul_zero]; exact P.start, by simp only [γt, mul_one]; exact P.stop⟩
      refine (iInf_le _ Q).trans (le_of_eq ?_)
      rw [ulen_lift hp D hlip (fun t _ => rfl)]
      exact wlen_rescale D P.γ hT
  · -- a path on `[0, 1]` has a lift on `[0, 1]` with the same length
    refine le_iInf fun Q => ?_
    choose f hf hfc using fun ν => exists_lift hp (c := fun t => Q.γ t ν) (K := Q.K)
      (LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ ν).trans (Q.lip.dist_le_mul x hx y hy))
    let γt : ℝ → (Fin 4 → ℝ) := fun t ν => f ν t
    have hlip : LipschitzWith Q.K γt := LipschitzWith.of_dist_le_mul fun x y =>
      (dist_pi_le_iff (by positivity)).2 fun ν => (hf ν).dist_le_mul x y
    have hproj : ∀ t ∈ Icc (0 : ℝ) 1, Q.γ t = projT p (γt t) := fun t ht =>
      funext fun ν => hfc ν t ht
    let P : TPath p z z' := ⟨1, zero_le_one, γt, Q.K, hlip,
      by rw [← hproj 0 ⟨le_rfl, zero_le_one⟩]; exact Q.start,
      by rw [← hproj 1 ⟨zero_le_one, le_rfl⟩]; exact Q.stop⟩
    refine (iInf_le _ P).trans (le_of_eq ?_)
    exact (ulen_lift hp D hlip hproj).symm

/-! ### `lem:distance` for the weighted distance of the core -/

/-- **`lem:distance`(i)** for the core's weighted distance: a metric with `|z - z'|₁ ≤ d(z, z') ≤ η⁻¹|z - z'|₁`. -/
theorem udist_metric (hp : 0 < p) (D : DomainData p) :
    (∀ z z', ENNReal.ofReal (dist1 z z') ≤ udist D z z') ∧
    (∀ z z', udist D z z' ≤ ENNReal.ofReal ((D.a 0)⁻¹ * dist1 z z')) ∧
    (∀ z, udist D z z = 0) ∧ (∀ z z', udist D z z' = 0 → z = z') ∧
    (∀ z z', udist D z z' = udist D z' z) ∧ (∀ z z' z'', udist D z z'' ≤ udist D z z' + udist D z' z'') := by
  simp only [udist_eq_wdist hp]
  exact ⟨dist1_le_wdist D, wdist_le D, wdist_self D, fun _ _ h => eq_of_wdist_eq_zero D h, wdist_comm D,
    wdist_triangle D⟩

/-- **`lem:distance`(ii)** for the core's weighted distance: `d(z, z') ≥ RM max(|j - j'| - 1, 0)`. -/
theorem udist_ge_layers (hp : 0 < p) (D : DomainData p) {R M : ℝ}
    (hsep : ∀ i, 1 ≤ i → i < D.k → ∀ x ∉ D.Ω i, ∀ y ∈ D.Ω (i + 1), R * M * D.a i ≤ dist x y)
    {z z' : Tor p} {j j' : ℕ} (hz : z ∈ D.Ω j) (hz1 : z ∉ D.Ω (j + 1)) (hz' : z' ∈ D.Ω j')
    (hz1' : z' ∉ D.Ω (j' + 1)) :
    ENNReal.ofReal (R * M * max (|(j : ℝ) - j'| - 1) 0) ≤ udist D z z' := by
  rw [udist_eq_wdist hp]
  exact wdist_ge_layers D hsep hz hz1 hz' hz1'

end CoreLean

end
