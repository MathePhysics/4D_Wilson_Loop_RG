/-
`lem:cubic-gradient` of BALABAN_CORE.tex, the analytic part of the conclusion.

For a `1`-form `A` with values in `𝔤^c` and a bond `(μ, x)`, the function `z ↦ 𝖭₀(zA)(μ, x)` is entire
and vanishes to the second order at `z = 0` (`N0_ray`): `𝖵₀` vanishes to the third order along every ray
of `𝔤^c`-valued forms (`eq:action-expansion`), so its first and second derivatives at `0` vanish on these
forms (`second_order_zero`, by polarisation), and `𝖭₀(B)(μ, x)` is a fixed linear image of the derivative
of `𝖵₀` at `B` (`gradRep`), because `(Z, Y) ↦ tr ZY` is nondegenerate on `𝔤^c`.

With `g(z) = 𝖭₀(zA)(b) + z w` for any `w`, the formula of Cauchy bounds the Taylor coefficients of the
orders `n ≥ 2` of `g` by `M ρ^{-n}` when `‖g‖ ≤ M` on `|z| = ρ`; for `ρ ≥ 2` their sum at `z = 1` is at
most `2Mρ^{-2}` (`norm_taylor_two_le`). This is the conclusion of the proof in the core, with the bound
of `g` on the circle as the hypothesis (`norm_N0_le`).
-/
import CoreLean.CubicGradient
import CoreLean.WardTaylor
import CoreLean.WardPolar

open Matrix Complex BakerCampbellHausdorff Filter Asymptotics
open scoped Topology Nat Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

/-! ### Cauchy's estimate for the remainder of the order two -/

/-- For an entire `g` with `‖g‖ ≤ M` on the circle `|z| = ρ`, `ρ ≥ 2`:
`‖g(1) - g(0) - g'(0)‖ ≤ 2Mρ^{-2}`. -/
theorem norm_taylor_two_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : ℂ → E} (hg : Differentiable ℂ g) {ρ M : ℝ} (hρ : 2 ≤ ρ)
    (hM : ∀ z : ℂ, ‖z‖ = ρ → ‖g z‖ ≤ M) :
    ‖g 1 - g 0 - deriv g 0‖ ≤ 2 * M / ρ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (ρ : ℂ) (by simp [abs_of_pos hρ0]))
  have hT := Complex.hasSum_taylorSeries_of_entire hg 0 1
  simp only [sub_zero, one_pow, one_smul] at hT
  have hT2 := (hasSum_nat_add_iff' 2).mpr hT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, iteratedDeriv_zero, iteratedDeriv_one] at hT2
  -- the coefficients
  have hcoef : ∀ k : ℕ, ‖((k + 2)! : ℂ)⁻¹ • iteratedDeriv (k + 2) g 0‖ ≤ M * ρ⁻¹ ^ 2 * ρ⁻¹ ^ k := by
    intro k
    have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (k + 2) hρ0 hg.diffContOnCl
      (c := 0) fun z hz => hM z (by simpa using hz)
    have hf : (0 : ℝ) < ((k + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc ((k + 2)! : ℝ)⁻¹ * ‖iteratedDeriv (k + 2) g 0‖
        ≤ ((k + 2)! : ℝ)⁻¹ * ((k + 2)! * M / ρ ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hf.le)
      _ = M * ρ⁻¹ ^ 2 * ρ⁻¹ ^ k := by
          rw [inv_pow, inv_pow, pow_add]
          field_simp
  have hq : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hρ0.le) hq).mul_left (M * ρ⁻¹ ^ 2)
  have hle := hT2.norm_le_of_bounded hgeo hcoef
  have e : g 1 - g 0 - deriv g 0 = g 1 - (g 0 + deriv g 0) := by abel
  rw [e]
  refine hle.trans ?_
  -- `Mρ^{-2}/(1 - ρ^{-1}) ≤ 2Mρ^{-2}`
  have h1 : (1 - ρ⁻¹)⁻¹ ≤ 2 := by
    have : ρ⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hρ0 (by norm_num)]; linarith
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc M * ρ⁻¹ ^ 2 * (1 - ρ⁻¹)⁻¹ ≤ M * ρ⁻¹ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * M / ρ ^ 2 := by field_simp

/-! ### Functions which vanish to the third order along rays -/

section Ray

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma hasDerivAt_fderiv_ray {F : V → ℂ} (hF : AnalyticAt ℂ F 0) (A : V) :
    HasDerivAt (fun s : ℂ => fderiv ℂ F (s • A)) (fderiv ℂ (fderiv ℂ F) 0 A) 0 := by
  have h1 : HasFDerivAt (fderiv ℂ F) (fderiv ℂ (fderiv ℂ F) 0) ((0 : ℂ) • A) := by
    rw [zero_smul]; exact hF.fderiv.differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun s : ℂ => s • A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const A
  exact h1.comp_hasDerivAt 0 hl

/-- An analytic function of one variable which is `O(s³)` vanishes at `0` with its first two derivatives. -/
lemma zero_of_cube {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) {K : ℝ}
    (h : ∀ s : ℂ, ‖s‖ ≤ 1 → ‖g s‖ ≤ K * ‖s‖ ^ 3) :
    g 0 = 0 ∧ deriv g 0 = 0 ∧ deriv (deriv g) 0 = 0 := by
  obtain ⟨G, hG, hT⟩ := Ward.taylor_four hg
  set c₀ := iteratedDeriv 0 g 0
  set c₁ := iteratedDeriv 1 g 0
  set c₂ := iteratedDeriv 2 g 0
  set c₃ := iteratedDeriv 3 g 0
  have hbd : ∀ᶠ s in 𝓝 (0 : ℂ), ‖G s‖ ≤ ‖G 0‖ + 1 := by
    have := hG.norm.eventually (gt_mem_nhds (lt_add_one ‖G 0‖))
    exact this.mono fun s hs => hs.le
  have hball : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with s hs
    simpa using hs
  have hO : (fun s : ℂ => 0 + c₀ * s + c₁ * s ^ 2 + c₂ / 2 * s ^ 3) =O[𝓝 0] fun s => ‖s‖ ^ 4 := by
    refine IsBigO.of_bound (K + ‖c₃‖ / 6 + (‖G 0‖ + 1)) ?_
    filter_upwards [hT, hbd, hball] with s hs hGs hs1
    have e : 0 + c₀ * s + c₁ * s ^ 2 + c₂ / 2 * s ^ 3 = s * g s - s ^ 4 / 6 * c₃ - s ^ 5 * G s := by
      rw [hs]; ring
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖s * g s‖ ≤ K * ‖s‖ ^ 4 := by
      rw [norm_mul]
      calc ‖s‖ * ‖g s‖ ≤ ‖s‖ * (K * ‖s‖ ^ 3) := mul_le_mul_of_nonneg_left (h s hs1) (norm_nonneg _)
        _ = K * ‖s‖ ^ 4 := by ring
    have h2 : ‖s ^ 4 / 6 * c₃‖ = ‖c₃‖ / 6 * ‖s‖ ^ 4 := by
      rw [norm_mul, norm_div, norm_pow]; norm_num; ring
    have h3 : ‖s ^ 5 * G s‖ ≤ (‖G 0‖ + 1) * ‖s‖ ^ 4 := by
      rw [norm_mul, norm_pow]
      have : ‖s‖ ^ 5 ≤ ‖s‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg _) hs1 (by norm_num)
      calc ‖s‖ ^ 5 * ‖G s‖ ≤ ‖s‖ ^ 4 * (‖G 0‖ + 1) :=
            mul_le_mul this hGs (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc ‖s * g s - s ^ 4 / 6 * c₃ - s ^ 5 * G s‖
        ≤ ‖s * g s‖ + ‖s ^ 4 / 6 * c₃‖ + ‖s ^ 5 * G s‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (K + ‖c₃‖ / 6 + (‖G 0‖ + 1)) * ‖s‖ ^ 4 := by rw [h2]; linarith
  obtain ⟨-, e0, e1, e2⟩ := Ward.cubic_eq_zero hO
  refine ⟨by simpa [c₀] using e0, by simpa [c₁, iteratedDeriv_one] using e1, ?_⟩
  have : c₂ = 0 := by linear_combination 2 * e2
  simpa [c₂, iteratedDeriv_succ, iteratedDeriv_one] using this

/-- A function on `V`, analytic everywhere, which vanishes to the third order along every ray of a
submodule `W` has vanishing first and second derivatives at `0` on `W`. -/
lemma second_order_zero {F : V → ℂ} (hF : ∀ x, AnalyticAt ℂ F x) (W : Submodule ℂ V)
    (hW : ∀ X ∈ W, ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → ‖F (s • X)‖ ≤ K * ‖s‖ ^ 3)
    {A δ : V} (hA : A ∈ W) (hδ : δ ∈ W) :
    fderiv ℂ F 0 δ = 0 ∧ fderiv ℂ (fderiv ℂ F) 0 A δ = 0 := by
  have ray : ∀ X ∈ W, fderiv ℂ F 0 X = 0 ∧ fderiv ℂ (fderiv ℂ F) 0 X X = 0 := by
    intro X hX
    obtain ⟨K, hK⟩ := hW X hX
    have hd : ∀ s : ℂ, HasDerivAt (fun s : ℂ => F (s • X)) (fderiv ℂ F (s • X) X) s := by
      intro s
      have hl : HasDerivAt (fun s : ℂ => s • X) X s := by
        simpa using (hasDerivAt_id s).smul_const X
      exact (hF (s • X)).differentiableAt.hasFDerivAt.comp_hasDerivAt s hl
    have hΛ : AnalyticAt ℂ (fun s : ℂ => F (s • X)) 0 := by
      have h2 : AnalyticAt ℂ (fun s : ℂ => s • X) 0 := analyticAt_id.smul analyticAt_const
      exact (hF _).comp h2
    obtain ⟨-, h1, h2⟩ := zero_of_cube hΛ hK
    have e1 : deriv (fun s : ℂ => F (s • X)) = fun s => fderiv ℂ F (s • X) X :=
      funext fun s => (hd s).deriv
    have hr : HasDerivAt (fun s : ℂ => fderiv ℂ F (s • X) X) (fderiv ℂ (fderiv ℂ F) 0 X X) 0 :=
      (ContinuousLinearMap.apply ℂ ℂ X).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_fderiv_ray (hF 0) X)
    refine ⟨?_, ?_⟩
    · rw [e1] at h1; simpa using h1
    · rw [e1, hr.deriv] at h2; exact h2
  refine ⟨(ray δ hδ).1, ?_⟩
  have hsymm : IsSymmSndFDerivAt ℂ F 0 := ContDiffAt.isSymmSndFDerivAt_of_omega (hF 0).contDiffAt
  exact Ward.polar2 (fun x => x ∈ W) (fun x y => fderiv ℂ (fderiv ℂ F) 0 x y)
    (fun x x' y => by simp [map_add]) (fun x y => hsymm x y) (fun x y hx hy => W.add_mem hx hy)
    (fun x hx => (ray x hx).2) hA hδ

end Ray

/-! ### `𝖭₀` along a ray -/

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {G : GaugeGroup N}

/-- The `1`-forms with values in `𝔤^c`. -/
def lieForms (hG : G.LieInput) : Submodule ℂ (Form1 N n) where
  carrier := {A | ∀ μ x, A μ x ∈ G.lieC}
  add_mem' hA hB μ x := (GaugeGroup.lieCSubmodule hG).add_mem (hA μ x) (hB μ x)
  zero_mem' _ _ := (GaugeGroup.lieCSubmodule hG).zero_mem
  smul_mem' c _ hA μ x := (GaugeGroup.lieCSubmodule hG).smul_mem c (hA μ x)

lemma mem_lieForms (hG : G.LieInput) {A : Form1 N n} : A ∈ lieForms hG ↔ ∀ μ x, A μ x ∈ G.lieC :=
  Iff.rfl

lemma pair1_smul_right (c : ℂ) (X F : Form1 N n) : pair1 a X (c • F) = c * pair1 a X F := by
  simp only [pair1, pair0, Pi.smul_apply, Matrix.mul_smul, ntr_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => by ring

lemma pair1_single1 (μ : Fin 4) (x : Site n) (Z : Mat) (Y : Form1 N n) :
    pair1 a (single1 μ x Z) Y = a ^ 4 * ntr (Z * Y μ x) := by
  unfold pair1 pair0 single1
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Pi.single_eq_of_ne hy, ntr]
  · simp
  · intro ν _ hν; simp [Pi.single_eq_of_ne hν, ntr]
  · simp

lemma pair1_zero_right (X : Form1 N n) : pair1 a X 0 = 0 := by
  simp [pair1, pair0, ntr]

lemma single1_mem (hG : G.LieInput) (μ : Fin 4) (x : Site n) {Z : Mat} (hZ : Z ∈ G.lieC) :
    single1 μ x Z ∈ lieForms hG := by
  intro ν y
  by_cases hν : ν = μ
  · subst hν
    by_cases hy : y = x
    · subst hy; simpa [single1] using hZ
    · simp only [single1, Pi.single_eq_same, Pi.single_eq_of_ne hy]
      exact (GaugeGroup.lieCSubmodule hG).zero_mem
  · simp only [single1, Pi.single_eq_of_ne hν, Pi.zero_apply]
    exact (GaugeGroup.lieCSubmodule hG).zero_mem

/-! #### Membership in `𝔤^c` -/

lemma val_mem {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified) (b : Bond n) :
    U.val b ∈ G.complexified := by
  unfold Config.val
  split_ifs
  · exact hU _ _
  · exact G.complexified.inv_mem (hU _ _)

lemma Ds2_mem (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    {F : Form2 N n} (hF : ∀ μ ν x, F μ ν x ∈ G.lieC) (μ : Fin 4) (x : Site n) :
    Ds2 a U F μ x ∈ G.lieC := by
  simp only [Ds2]
  refine (GaugeGroup.lieCSubmodule hG).sum_mem fun ν _ => ?_
  split_ifs
  · simp only [Dbw]
    exact (GaugeGroup.lieCSubmodule hG).smul_mem _ ((GaugeGroup.lieCSubmodule hG).sub_mem
      (GaugeGroup.Ad_mem_lieC hG (val_mem hU _) (hF _ _ _)) (hF _ _ _))
  · exact (GaugeGroup.lieCSubmodule hG).zero_mem

lemma current_mem [NeZero N] (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    (μ : Fin 4) (x : Site n) : current a hG U μ x ∈ G.lieC :=
  Ds2_mem a hG hU (fun _ _ _ => (GaugeGroup.lieCSubmodule hG).smul_mem _ (proj_mem hG _)) μ x

lemma hessOp_mem [NeZero N] (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) (μ : Fin 4) (x : Site n) :
    hessOp a hG U A μ x ∈ G.lieC :=
  (GaugeGroup.lieCSubmodule hG).add_mem (Ds2_mem a hG hU (D1_mem a hG hU hA) μ x)
    (hessOp'_mem a hG U A μ x)

lemma N0_mem [NeZero N] (hG : G.LieInput) {U : Config N n} (hU : ∀ μ x, U μ x ∈ G.complexified)
    {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC) (μ : Fin 4) (x : Site n) :
    N0 a hG U A μ x ∈ G.lieC := by
  have hZ : -((I * a) • A μ x) ∈ G.lieC :=
    (GaugeGroup.lieCSubmodule hG).neg_mem ((GaugeGroup.lieCSubmodule hG).smul_mem _ (hA μ x))
  exact (GaugeGroup.lieCSubmodule hG).sub_mem ((GaugeGroup.lieCSubmodule hG).sub_mem
    (Eop_mem hG hZ (current_mem a hG (expMul_mem a hG hU hA) μ x)) (current_mem a hG hU μ x))
    (hessOp_mem a hG hU hA μ x)

/-! #### Analyticity of `𝖵₀` and the cubic bound along rays -/

lemma analyticAt_pair1 {f g : Form1 N n → Form1 N n} {A₀ : Form1 N n} (hf : AnalyticAt ℂ f A₀)
    (hg : AnalyticAt ℂ g A₀) : AnalyticAt ℂ (fun A => pair1 a (f A) (g A)) A₀ := by
  unfold pair1 pair0
  refine Finset.analyticAt_fun_sum _ fun μ _ => Finset.analyticAt_fun_sum _ fun x _ => ?_
  have hc : ∀ {h : Form1 N n → Form1 N n}, AnalyticAt ℂ h A₀ →
      AnalyticAt ℂ (fun A => h A μ x) A₀ := fun {h} hh => (analyticAt_coord μ x (h A₀)).comp hh
  exact analyticAt_const.mul ((ntrL.analyticAt _).comp ((hc hf).mul (hc hg)))

/-- `𝖵₀` is entire. -/
lemma analyticAt_V0 [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (A₀ : Form1 N n) :
    AnalyticAt ℂ (V0 a hG U) A₀ := by
  have hL : AnalyticAt ℂ (hessOp a hG U) A₀ :=
    (LinearMap.toContinuousLinearMap (hessLin a hG ha U)).analyticAt A₀
  show AnalyticAt ℂ (fun A => action (expMul a A U) - action U - pair1 a A (current a hG U) -
    1 / 2 * pair1 a A (hessOp a hG U A)) A₀
  exact (((analyticAt_action_expMul a U A₀).sub analyticAt_const).sub
    (analyticAt_pair1 a analyticAt_id analyticAt_const)).sub
    (analyticAt_const.mul (analyticAt_pair1 a analyticAt_id hL))

/-- `𝖵₀(sX) = O(s³)` for `X` with values in `𝔤^c` (`eq:action-expansion`). -/
lemma V0_cube [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {X : Form1 N n} (hX : ∀ μ x, X μ x ∈ G.lieC) :
    ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → ‖V0 a hG U (s • X)‖ ≤ K * ‖s‖ ^ 3 := by
  obtain ⟨K, hK⟩ := action_expansion_hessOp a hG ha hU hX
  refine ⟨K, fun s hs => ?_⟩
  have hsm : hessOp a hG U (s • X) = s • hessOp a hG U X := (hessLin a hG ha U).map_smul s X
  have e : V0 a hG U (s • X) = action (expMul a (s • X) U) - action U -
      s * pair1 a X (current a hG U) - s ^ 2 / 2 * pair1 a X (hessOp a hG U X) := by
    rw [V0, hsm, pair1_smul_left, pair1_smul_left, pair1_smul_right]; ring
  rw [e]; exact hK s hs

/-! #### The representation of `𝖭₀` by the derivative of `𝖵₀` -/

/-- The value at the bond `(μ, x)` of the `𝔤^c`-valued form which represents a functional on the
`𝔤^c`-valued forms through `⟨·, ·⟩`. -/
def gradRep [NeZero N] (hG : G.LieInput) (μ : Fin 4) (x : Site n) :
    (Form1 N n →L[ℂ] ℂ) →ₗ[ℂ] Mat where
  toFun Λ := (a ^ 4)⁻¹ • ((trEquiv hG).symm ((Λ : Form1 N n →ₗ[ℂ] ℂ).comp
      ((LinearMap.single ℂ (fun _ : Fin 4 => Site n → Mat) μ).comp
        ((LinearMap.single ℂ (fun _ : Site n => Mat) x).comp
          (GaugeGroup.lieCSubmodule hG).subtype))) : Mat)
  map_add' Λ Λ' := by
    rw [ContinuousLinearMap.coe_add, LinearMap.add_comp, map_add, Submodule.coe_add, smul_add]
  map_smul' c Λ := by
    rw [ContinuousLinearMap.coe_smul, LinearMap.smul_comp, map_smul, Submodule.coe_smul,
      RingHom.id_apply, smul_comm]

lemma gradRep_spec [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (μ : Fin 4) (x : Site n)
    (Λ : Form1 N n →L[ℂ] ℂ) {Y : Form1 N n} (hY : ∀ μ x, Y μ x ∈ G.lieC)
    (hΛ : ∀ δ ∈ lieForms hG, Λ δ = pair1 a δ Y) : gradRep a hG μ x Λ = Y μ x := by
  have hℓ : (Λ : Form1 N n →ₗ[ℂ] ℂ).comp
      ((LinearMap.single ℂ (fun _ : Fin 4 => Site n → Mat) μ).comp
        ((LinearMap.single ℂ (fun _ : Site n => Mat) x).comp
          (GaugeGroup.lieCSubmodule hG).subtype)) =
      trEquiv hG ((a ^ 4) • (⟨Y μ x, hY μ x⟩ : GaugeGroup.lieCSubmodule hG)) := by
    refine LinearMap.ext fun Z => ?_
    have h := hΛ (single1 μ x Z) (single1_mem hG μ x Z.2)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_single, ContinuousLinearMap.coe_coe]
    rw [show Pi.single μ (Pi.single x (Z : Mat)) = single1 μ x (Z : Mat) from rfl, h,
      pair1_single1, map_smul, LinearMap.smul_apply]
    simp only [trEquiv, LinearEquiv.ofBijective_apply, trPairing, LinearMap.coe_mk, AddHom.coe_mk,
      smul_eq_mul]
  simp only [gradRep, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hℓ, LinearEquiv.symm_apply_apply, Submodule.coe_smul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 4 ha), one_smul]

/-- `def:potential`(iii) and `lem:cubic-gradient`: for `A` with values in `𝔤^c` and a bond `(μ, x)`,
`z ↦ 𝖭₀(zA)(μ, x)` is entire, vanishes at `0`, and has the derivative `0` at `0`. -/
theorem N0_ray [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) :
    Differentiable ℂ (fun z : ℂ => N0 a hG U (z • A) μ x) ∧ N0 a hG U 0 μ x = 0 ∧
      HasDerivAt (fun z : ℂ => N0 a hG U (z • A) μ x) 0 0 := by
  set F := V0 a hG U
  have hF : ∀ B, AnalyticAt ℂ F B := analyticAt_V0 a hG ha U
  set L := LinearMap.toContinuousLinearMap (gradRep a hG μ x)
  have hrep : ∀ B ∈ lieForms hG, N0 a hG U B μ x = L (fderiv ℂ F B) := by
    intro B hB
    refine (gradRep_spec a hG ha μ x _ (N0_mem a hG hU hB) fun δ hδ => ?_).symm
    have h1 := hasDerivAt_V0 a hG ha hU hB hδ
    have hl : HasDerivAt (fun t : ℂ => B + t • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const δ).const_add B
    have h2 := (hF (B + (0 : ℂ) • δ)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hl
    rw [zero_smul, add_zero] at h2
    exact h2.unique h1
  have hray : ∀ z : ℂ, z • A ∈ lieForms hG := fun z => (lieForms hG).smul_mem z hA
  have hfun : (fun z : ℂ => N0 a hG U (z • A) μ x) = fun z => L (fderiv ℂ F (z • A)) :=
    funext fun z => hrep _ (hray z)
  have hzero : ∀ Λ : Form1 N n →L[ℂ] ℂ, (∀ δ ∈ lieForms hG, Λ δ = 0) → L Λ = 0 := by
    intro Λ hΛ
    have := gradRep_spec a hG ha μ x Λ (Y := 0) (fun _ _ => (GaugeGroup.lieCSubmodule hG).zero_mem)
      fun δ hδ => by rw [hΛ δ hδ, pair1_zero_right]
    exact (by simpa using this : gradRep a hG μ x Λ = 0)
  have hcube : ∀ X ∈ lieForms hG, ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → ‖F (s • X)‖ ≤ K * ‖s‖ ^ 3 :=
    fun X hX => V0_cube a hG ha hU hX
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    intro z
    have h2 : AnalyticAt ℂ (fun s : ℂ => s • A) z := analyticAt_id.smul analyticAt_const
    exact (L.analyticAt _).comp ((hF _).fderiv.comp h2) |>.differentiableAt
  · rw [hrep 0 (lieForms hG).zero_mem]
    exact hzero _ fun δ hδ => (second_order_zero hF (lieForms hG) hcube hδ hδ).1
  · rw [hfun]
    have h := L.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_fderiv_ray (hF 0) A)
    rwa [show L (fderiv ℂ (fderiv ℂ F) 0 A) = 0 from
      hzero _ fun δ hδ => (second_order_zero hF (lieForms hG) hcube hA hδ).2] at h

/-- The conclusion of `lem:cubic-gradient` at one bond: if `g(z) = 𝖭₀(zA)(μ, x) + zw` satisfies
`‖g(z)‖ ≤ M` on the circle `|z| = ρ`, `ρ ≥ 2`, then `‖𝖭₀(A)(μ, x)‖ ≤ 2Mρ^{-2}`. -/
theorem norm_N0_le [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) {A : Form1 N n} (hA : ∀ μ x, A μ x ∈ G.lieC)
    (μ : Fin 4) (x : Site n) (w : Mat) {ρ M : ℝ} (hρ : 2 ≤ ρ)
    (hM : ∀ z : ℂ, ‖z‖ = ρ → ‖N0 a hG U (z • A) μ x + z • w‖ ≤ M) :
    ‖N0 a hG U A μ x‖ ≤ 2 * M / ρ ^ 2 := by
  obtain ⟨hd, h0, h1⟩ := N0_ray a hG ha hU hA μ x
  set g : ℂ → Mat := fun z => N0 a hG U (z • A) μ x + z • w
  have hg : Differentiable ℂ g := hd.add (differentiable_id.smul_const w)
  have hg0 : g 0 = 0 := by simp [g, h0]
  have hg1 : deriv g 0 = w := by
    have := h1.add ((hasDerivAt_id (0 : ℂ)).smul_const w)
    have h' : HasDerivAt g w 0 := by
      convert this using 1
      · rfl
      · simp
    exact h'.deriv
  have h := norm_taylor_two_le hg hρ hM
  rw [hg0, hg1] at h
  have e : g 1 - 0 - w = N0 a hG U A μ x := by simp [g]
  rwa [e] at h

end CoreLean
