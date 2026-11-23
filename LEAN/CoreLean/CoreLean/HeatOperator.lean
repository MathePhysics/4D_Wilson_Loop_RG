/-
`lem:heat-kernel` of BALABAN_CORE.tex: the heat semigroup of the lattice `εℤ⁴`.

The points `εn`, `n ∈ ℤ⁴`, are indexed by `n`. Functions take values in a complete real normed space
`V` (the core's `𝖵` is a complex vector space of finite dimension with a norm, hence such a space).
The differences are `(∂_μ f)(n) = ε⁻¹ (f(n + e_μ) - f(n))` and `(∂^*_μ f)(n) = ε⁻¹ (f(n - e_μ) - f(n))`,
and `|εm|₁ = ε Σ_μ |m_μ|`.

The semigroup is defined by its kernel: `(P_t f)(n) = Σ_z p_{t/ε²}(z) f(n - z)`, with
`p_s(z) = Π_μ q_s(z_μ)` the kernel of unit spacing, so that `p_{t/ε²}(z)` is the core's `ε⁴ p_t(εz)`.
The core defines `P_t = e^{-tΔ}` by the exponential series and shows in its proof that it is given by
this kernel; that identification is `HeatExponential.Pexp_eq_heatOp`. The kernel satisfies the heat equation
(`Balaban.LatticeGreen.hasDerivAt_heatKernel`), `P_0 = 1`, and the semigroup law
(`CoreLean.hasSum_heatKernel_conv`).
-/
import CoreLean.HeatKernelSums

open MeasureTheory Real Balaban.LatticeGreen Filter Topology

namespace CoreLean

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The coordinate unit vector `e_μ` of `ℤ⁴`. -/
abbrev e4 (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1

/-- `(P_t f)(n) = Σ_z p_{t/ε²}(z) f(n - z)`. -/
noncomputable def heatOp (ε t : ℝ) (f : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ∑' z, heatKernel 4 (t / ε ^ 2) z • f (n - z)

/-- `(∂_μ f)(n) = ε⁻¹ (f(n + e_μ) - f(n))`. -/
noncomputable def dfw (ε : ℝ) (μ : Fin 4) (f : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ε⁻¹ • (f (n + e4 μ) - f n)

/-- `(∂^*_μ f)(n) = ε⁻¹ (f(n - e_μ) - f(n))`. -/
noncomputable def dbw (ε : ℝ) (μ : Fin 4) (f : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ε⁻¹ • (f (n - e4 μ) - f n)

/-- `Σ_μ |m_μ|`; the core's `|εm|₁` is `ε` times it. -/
noncomputable def l1 (m : Fin 4 → ℤ) : ℝ := ∑ μ, |((m μ : ℤ) : ℝ)|

/-- `c₀ = ½√π`. -/
noncomputable def c0 : ℝ := Real.sqrt π / 2
/-- `m₁ = 1 + 3√2 c₀`. -/
noncomputable def m1 : ℝ := 1 + 3 * Real.sqrt 2 * c0

lemma c0_pos : 0 < c0 := by unfold c0; positivity

lemma c0_le_one : c0 ≤ 1 := by
  unfold c0
  have : Real.sqrt π ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_four]
  linarith

lemma one_le_m1 : 1 ≤ m1 := by
  unfold m1; have := c0_pos
  have : 0 ≤ 3 * Real.sqrt 2 * c0 := by positivity
  linarith

section Kernel

variable {s : ℝ}

lemma hasSum_heatKernel4 (hs : 0 ≤ s) : HasSum (heatKernel 4 s) 1 := by
  have h := hasSum_prod_kernel (d := 4) (fun _ n => heatKernel1 s n)
    (fun _ n => heatKernel1_nonneg hs n) (S := fun _ => 1) fun _ => hasSum_heatKernel1 hs
  have e : heatKernel 4 s = fun z => ∏ ν, heatKernel1 s (z ν) := rfl
  rw [e]
  simpa using h

lemma heatKernel4_nonneg (hs : 0 ≤ s) (z : Fin 4 → ℤ) : 0 ≤ heatKernel 4 s z :=
  Finset.prod_nonneg fun _ _ => heatKernel1_nonneg hs _

/-- The kernel sums are summable against a bounded function. -/
lemma summable_kernel_smul (hs : 0 ≤ s) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (g : (Fin 4 → ℤ) → ℝ) (hg : Summable fun z => |g z|) (n : Fin 4 → ℤ) :
    Summable fun z => g z • f (n - z) :=
  Summable.of_norm_bounded (hg.mul_right M) fun z => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)

lemma summable_abs_heatKernel4 (hs : 0 ≤ s) : Summable fun z => |heatKernel 4 s z| :=
  (hasSum_heatKernel4 hs).summable.congr fun z => (abs_of_nonneg (heatKernel4_nonneg hs z)).symm

end Kernel

variable {ε t : ℝ}

/-! ### `lem:heat-kernel`(i) -/

/-- `P_t` commutes with the translations. -/
theorem heatOp_translate (f : (Fin 4 → ℤ) → V) (a n : Fin 4 → ℤ) :
    heatOp ε t (fun m => f (m + a)) n = heatOp ε t f (n + a) := by
  unfold heatOp
  refine tsum_congr fun z => ?_
  dsimp only
  rw [show n - z + a = n + a - z by abel]

/-- `P_t` maps the constants to themselves. -/
theorem heatOp_const (ht : 0 ≤ t) (v : V) (n : Fin 4 → ℤ) :
    heatOp ε t (fun _ => v) n = v := by
  unfold heatOp
  rw [(hasSum_heatKernel4 (by positivity : 0 ≤ t / ε ^ 2)).summable.tsum_smul_const,
    (hasSum_heatKernel4 (by positivity : 0 ≤ t / ε ^ 2)).tsum_eq, one_smul]

/-- `‖P_t f‖_∞ ≤ ‖f‖_∞`. -/
theorem norm_heatOp_le (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (n : Fin 4 → ℤ) : ‖heatOp ε t f n‖ ≤ M := by
  have hs : 0 ≤ t / ε ^ 2 := by positivity
  have hsum := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) n
  unfold heatOp
  calc ‖∑' z, heatKernel 4 (t / ε ^ 2) z • f (n - z)‖ ≤ 1 * M := by
        refine tsum_of_norm_bounded ((hasSum_heatKernel4 hs).mul_right M) fun z => ?_
        rw [norm_smul, Real.norm_of_nonneg (heatKernel4_nonneg hs z)]
        exact mul_le_mul_of_nonneg_left (hf _) (heatKernel4_nonneg hs z)
    _ = M := one_mul M

/-- `P_t` commutes with `∂_μ`. -/
theorem heatOp_dfw (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) (μ : Fin 4)
    (n : Fin 4 → ℤ) : heatOp ε t (dfw ε μ f) n = dfw ε μ (heatOp ε t f) n := by
  have hs : 0 ≤ t / ε ^ 2 := by positivity
  have h1 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) (n + e4 μ)
  have h2 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) n
  unfold heatOp dfw
  dsimp only
  rw [← h1.tsum_sub h2, ← tsum_const_smul'']
  refine tsum_congr fun z => ?_
  rw [smul_comm, smul_sub, show n - z + e4 μ = n + e4 μ - z by abel]

/-- `P_t` commutes with `∂^*_μ`. -/
theorem heatOp_dbw (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) (μ : Fin 4)
    (n : Fin 4 → ℤ) : heatOp ε t (dbw ε μ f) n = dbw ε μ (heatOp ε t f) n := by
  have hs : 0 ≤ t / ε ^ 2 := by positivity
  have h1 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) (n - e4 μ)
  have h2 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) n
  unfold heatOp dbw
  dsimp only
  rw [← h1.tsum_sub h2, ← tsum_const_smul'']
  refine tsum_congr fun z => ?_
  rw [smul_comm, smul_sub, show n - z - e4 μ = n - e4 μ - z by abel]

/-! ### `lem:heat-kernel`(ii) -/

/-- `∂_μ P_t f (n) = ε⁻¹ Σ_z (p(z + e_μ) - p(z)) f(n - z)`. -/
lemma dfw_heatOp_eq (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) (μ : Fin 4)
    (n : Fin 4 → ℤ) :
    dfw ε μ (heatOp ε t f) n = ε⁻¹ • ∑' z, (heatKernel 4 (t / ε ^ 2) (z + e4 μ) -
      heatKernel 4 (t / ε ^ 2) z) • f (n - z) := by
  have hs : 0 ≤ t / ε ^ 2 := by positivity
  have h1 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) (n + e4 μ)
  have h2 := summable_kernel_smul hs hf _ (summable_abs_heatKernel4 hs) n
  have hshift : heatOp ε t f (n + e4 μ) =
      ∑' z, heatKernel 4 (t / ε ^ 2) (z + e4 μ) • f (n - z) := by
    unfold heatOp
    rw [← (Equiv.addRight (e4 μ)).tsum_eq]
    congr 1; funext z
    simp only [Equiv.coe_addRight]
    rw [show n + e4 μ - (z + e4 μ) = n - z by abel]
  have h1' : Summable fun z => heatKernel 4 (t / ε ^ 2) (z + e4 μ) • f (n - z) := by
    have := (Equiv.addRight (e4 μ)).summable_iff.mpr h1
    refine this.congr fun z => ?_
    simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [show n + e4 μ - (z + e4 μ) = n - z by abel]
  unfold dfw
  rw [hshift]
  unfold heatOp
  rw [← h1'.tsum_sub h2]
  congr 1
  refine tsum_congr fun z => ?_
  rw [sub_smul]

/-- `(t/ε²)`-kernel at the origin: `2 q_{t/ε²}(0) ≤ ε c₀ t^{-1/2}`. -/
lemma two_heatKernel1_zero_le (hε : 0 < ε) (ht : 0 < t) :
    2 * heatKernel1 (t / ε ^ 2) 0 ≤ ε * (c0 / Real.sqrt t) := by
  have h := heatKernel1_zero_le (t := t / ε ^ 2) (by positivity)
  rw [Real.sqrt_div' _ (sq_nonneg ε), Real.sqrt_sq hε.le] at h
  unfold c0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  calc 2 * heatKernel1 (t / ε ^ 2) 0 ≤ 2 * (Real.sqrt π / (4 * (Real.sqrt t / ε))) := by linarith
    _ = ε * (Real.sqrt π / 2 / Real.sqrt t) := by field_simp; ring

/-- `lem:heat-kernel`(ii) for `∂_μ`: `‖∂_μ P_t f‖_∞ ≤ c₀ t^{-1/2} ‖f‖_∞`. -/
theorem norm_dfw_heatOp_le (hε : 0 < ε) (ht : 0 < t) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖dfw ε μ (heatOp ε t f) n‖ ≤ c0 / Real.sqrt t * M := by
  have hs : 0 ≤ t / ε ^ 2 := by positivity
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0)
  have habs := hasSum_abs_shift_sub (d := 4) hs μ
  rw [dfw_heatOp_eq ht.le hf, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have hbound : ‖∑' z, (heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z) •
      f (n - z)‖ ≤ 2 * heatKernel1 (t / ε ^ 2) 0 * M :=
    tsum_of_norm_bounded (habs.mul_right M) fun z => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
  calc ε⁻¹ * ‖∑' z, (heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z) •
        f (n - z)‖ ≤ ε⁻¹ * (2 * heatKernel1 (t / ε ^ 2) 0 * M) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hε.le)
    _ ≤ ε⁻¹ * (ε * (c0 / Real.sqrt t) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (two_heatKernel1_zero_le hε ht) hM)
          (inv_nonneg.mpr hε.le)
    _ = c0 / Real.sqrt t * M := by field_simp

/-- `∂^*_μ g (n) = -(∂_μ g)(n - e_μ)`. -/
lemma dbw_eq_neg_dfw (g : (Fin 4 → ℤ) → V) (μ : Fin 4) (n : Fin 4 → ℤ) :
    dbw ε μ g n = -dfw ε μ g (n - e4 μ) := by
  unfold dbw dfw
  rw [sub_add_cancel, ← smul_neg, neg_sub]

/-- `lem:heat-kernel`(ii) for `∂^*_μ`. -/
theorem norm_dbw_heatOp_le (hε : 0 < ε) (ht : 0 < t) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖dbw ε μ (heatOp ε t f) n‖ ≤ c0 / Real.sqrt t * M := by
  rw [dbw_eq_neg_dfw, norm_neg]
  exact norm_dfw_heatOp_le hε ht hf μ _

/-! ### `lem:heat-kernel`(iii) -/

/-- Hölder's inequality in the form used: `Σ w a^β ≤ (Σ w)^{1-β} (Σ w a)^β` for `w, a ≥ 0`,
`0 ≤ β ≤ 1`. -/
lemma tsum_mul_rpow_le {ι : Type*} {w a : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    {W W1 : ℝ} (hW : HasSum w W) (hW1 : HasSum (fun i => w i * a i) W1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : ∃ C, HasSum (fun i => w i * a i ^ β) C ∧ C ≤ W ^ (1 - β) * W1 ^ β := by
  have hW0 : 0 ≤ W := hW.nonneg hw
  have hW10 : 0 ≤ W1 := hW1.nonneg fun i => mul_nonneg (hw i) (ha i)
  rcases eq_or_lt_of_le hβ0 with h0 | hβpos
  · subst h0
    exact ⟨W, hW.congr_fun fun i => by simp, by simp⟩
  rcases eq_or_lt_of_le hβ1 with h1 | hβlt
  · subst h1
    exact ⟨W1, hW1.congr_fun fun i => by simp, by simp⟩
  -- `0 < β < 1`: exponents `p = 1/(1-β)`, `q = 1/β`
  have h1β : 0 < 1 - β := by linarith
  have hpq : (1 / (1 - β)).HolderConjugate (1 / β) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [one_div, one_div, inv_inv, inv_inv]; ring
    · positivity
    · positivity
  obtain ⟨C, hC0, hCle, hC⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq
    (f := fun i => w i ^ (1 - β)) (g := fun i => (w i * a i) ^ β)
    (A := W ^ (1 - β)) (B := W1 ^ β) (by positivity) (by positivity)
    (fun i => Real.rpow_nonneg (hw i) _) (fun i => Real.rpow_nonneg (mul_nonneg (hw i) (ha i)) _)
    (by
      rw [← Real.rpow_mul hW0, mul_one_div_cancel h1β.ne', Real.rpow_one]
      exact hW.congr_fun fun i => by
        rw [← Real.rpow_mul (hw i), mul_one_div_cancel h1β.ne', Real.rpow_one])
    (by
      rw [← Real.rpow_mul hW10, mul_one_div_cancel hβpos.ne', Real.rpow_one]
      exact hW1.congr_fun fun i => by
        rw [← Real.rpow_mul (mul_nonneg (hw i) (ha i)), mul_one_div_cancel hβpos.ne',
          Real.rpow_one])
  refine ⟨C, hC.congr_fun fun i => ?_, hCle⟩
  rw [Real.mul_rpow (hw i) (ha i), ← mul_assoc, ← Real.rpow_add' (hw i) (by norm_num),
    sub_add_cancel, Real.rpow_one]

/-- `Σ_z (p(z + e_μ) - p(z)) = 0`. -/
lemma hasSum_shift_sub_zero {s : ℝ} (hs : 0 ≤ s) (μ : Fin 4) :
    HasSum (fun z => heatKernel 4 s (z + e4 μ) - heatKernel 4 s z) 0 := by
  have h1 : HasSum (fun z => heatKernel 4 s (z + e4 μ)) 1 :=
    ((Equiv.addRight (e4 μ)).hasSum_iff (f := heatKernel 4 s)).mpr (hasSum_heatKernel4 hs)
  simpa using h1.sub (hasSum_heatKernel4 hs)

lemma l1_neg (m : Fin 4 → ℤ) : l1 (-m) = l1 m := by
  unfold l1; simp

lemma l1_nonneg (m : Fin 4 → ℤ) : 0 ≤ l1 m := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `Σ_z |p(z + e_μ) - p(z)| Σ_ν |z_ν| = 1 + 3 · 2 q(0) Σ_n |n| q(n)`. -/
lemma hasSum_abs_shift_sub_mul_l1 {s : ℝ} (hs : 0 ≤ s) (μ : Fin 4) :
    HasSum (fun z => |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| * l1 z)
      (1 + 3 * (2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n)) := by
  have h : HasSum (fun z => ∑ ν : Fin 4, |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| *
      |((z ν : ℤ) : ℝ)|) (∑ ν : Fin 4, if ν = μ then 1 else
        2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n) := by
    refine hasSum_sum fun ν _ => ?_
    split_ifs with h
    · subst h; exact hasSum_abs_shift_sub_mul_self hs ν
    · exact hasSum_abs_shift_sub_mul_other hs h
  have hval : (∑ ν : Fin 4, if ν = μ then (1 : ℝ) else
      2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n) =
      1 + 3 * (2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n) := by
    fin_cases μ <;> simp [Fin.sum_univ_four] <;> ring
  rw [hval] at h
  refine h.congr_fun fun z => ?_
  unfold l1
  rw [Finset.mul_sum]

/-- `lem:heat-kernel`(iii) for `∂_μ`: if `‖f(x + z) - f(x)‖ ≤ F |z|₁^β`, then
`‖∂_μ P_t f‖_∞ ≤ m₁ t^{-(1-β)/2} F`. -/
theorem norm_dfw_heatOp_le_holder (hε : 0 < ε) (ht : 0 < t) {β F : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖dfw ε μ (heatOp ε t f) n‖ ≤ m1 * t ^ (-(1 - β) / 2) * F := by
  set s := t / ε ^ 2 with hs_def
  have hs : 0 ≤ s := by positivity
  set w : (Fin 4 → ℤ) → ℝ := fun z => |heatKernel 4 s (z + e4 μ) - heatKernel 4 s z| with hw_def
  have hw0 : ∀ z, 0 ≤ w z := fun z => abs_nonneg _
  have hW := hasSum_abs_shift_sub (d := 4) hs μ
  have hW1 := hasSum_abs_shift_sub_mul_l1 hs μ
  set W := 2 * heatKernel1 s 0
  set W1 := 1 + 3 * (2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n)
  obtain ⟨C, hC, hCle⟩ := tsum_mul_rpow_le (w := w) (a := l1) hw0
    (fun z => Finset.sum_nonneg fun _ _ => abs_nonneg _) hW hW1 hβ0 hβ1
  -- the representation with `f(n - z) - f(n)`
  set a : (Fin 4 → ℤ) → ℝ := fun z => heatKernel 4 s (z + e4 μ) - heatKernel 4 s z
  have hsa : Summable fun z => |a z| := hW.summable
  have hrep : dfw ε μ (heatOp ε t f) n = ε⁻¹ • ∑' z, a z • (f (n - z) - f n) := by
    rw [dfw_heatOp_eq ht.le hf]
    congr 1
    have h1 := summable_kernel_smul hs hf a hsa n
    have h2 : Summable fun z => a z • f n :=
      (hasSum_shift_sub_zero hs μ).summable.smul_const _
    rw [show (fun z => a z • (f (n - z) - f n)) = fun z => a z • f (n - z) - a z • f n from
      funext fun z => smul_sub _ _ _, h1.tsum_sub h2, (hasSum_shift_sub_zero hs μ).summable.tsum_smul_const,
      (hasSum_shift_sub_zero hs μ).tsum_eq, zero_smul, sub_zero]
  -- the bound of each term
  have hterm : ∀ z, ‖a z • (f (n - z) - f n)‖ ≤ F * ε ^ β * (w z * l1 z ^ β) := fun z => by
    rw [norm_smul, Real.norm_eq_abs]
    have h := hhol n (-z)
    rw [show n + -z = n - z by abel, l1_neg, Real.mul_rpow hε.le (l1_nonneg z)] at h
    calc |a z| * ‖f (n - z) - f n‖ ≤ |a z| * (F * (ε ^ β * l1 z ^ β)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = F * ε ^ β * (w z * l1 z ^ β) := by simp only [hw_def]; ring
  have hsumle : ‖∑' z, a z • (f (n - z) - f n)‖ ≤ F * ε ^ β * C :=
    tsum_of_norm_bounded (hC.mul_left (F * ε ^ β)) hterm
  -- `W ≤ ε c₀ t^{-1/2}` and `W1 ≤ m₁`
  have hWle : W ≤ ε * (c0 / Real.sqrt t) := two_heatKernel1_zero_le hε ht
  have hW0 : 0 ≤ W := hW.nonneg hw0
  have hst : Real.sqrt (2 * s) = Real.sqrt 2 * Real.sqrt t / ε := by
    rw [hs_def, mul_div_assoc', Real.sqrt_div' _ (sq_nonneg ε), Real.sqrt_sq hε.le,
      Real.sqrt_mul (by norm_num)]
  have hW1le : W1 ≤ m1 := by
    have hM1 := tsum_abs_mul_le hs
    have hq0 : 0 ≤ heatKernel1 s 0 := heatKernel1_nonneg hs 0
    have hprod : 2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n ≤
        Real.sqrt 2 * c0 := by
      calc 2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n
          ≤ ε * (c0 / Real.sqrt t) * Real.sqrt (2 * s) :=
            mul_le_mul hWle hM1 (tsum_nonneg fun n => mul_nonneg (abs_nonneg _)
              (heatKernel1_nonneg hs n)) (by have := c0_pos; positivity)
        _ = Real.sqrt 2 * c0 := by
            rw [hst]; have := Real.sqrt_pos.mpr ht; field_simp
    unfold m1
    show 1 + 3 * (2 * heatKernel1 s 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 s n) ≤
      1 + 3 * Real.sqrt 2 * c0
    nlinarith
  have hW10 : 0 ≤ W1 := hW1.nonneg fun z => mul_nonneg (hw0 z)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  -- assemble
  rw [hrep, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have htpow : (ε * (c0 / Real.sqrt t)) ^ (1 - β) = ε ^ (1 - β) * (c0 ^ (1 - β) *
      t ^ (-(1 - β) / 2)) := by
    rw [Real.mul_rpow hε.le (by have := c0_pos; positivity), Real.div_rpow c0_pos.le
      (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, div_eq_mul_inv,
      ← Real.rpow_neg ht.le]
    congr 3; ring
  have h1b : 0 ≤ 1 - β := by linarith
  have hm10 : 0 ≤ m1 := zero_le_one.trans one_le_m1
  have hc0m1 : c0 ^ (1 - β) * m1 ^ β ≤ m1 := by
    calc c0 ^ (1 - β) * m1 ^ β ≤ m1 ^ (1 - β) * m1 ^ β :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow c0_pos.le (c0_le_one.trans one_le_m1) h1b)
            (Real.rpow_nonneg hm10 _)
      _ = m1 := by rw [← Real.rpow_add (by linarith [one_le_m1]), sub_add_cancel, Real.rpow_one]
  have hFe : 0 ≤ F * ε ^ β := mul_nonneg hF (Real.rpow_nonneg hε.le _)
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc ε⁻¹ * ‖∑' z, a z • (f (n - z) - f n)‖ ≤ ε⁻¹ * (F * ε ^ β * C) :=
        mul_le_mul_of_nonneg_left hsumle hεi
    _ ≤ ε⁻¹ * (F * ε ^ β * (W ^ (1 - β) * W1 ^ β)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCle hFe) hεi
    _ ≤ ε⁻¹ * (F * ε ^ β * ((ε * (c0 / Real.sqrt t)) ^ (1 - β) * m1 ^ β)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.rpow_le_rpow hW0 hWle h1b) (Real.rpow_le_rpow hW10 hW1le hβ0)
            (Real.rpow_nonneg hW10 _) (Real.rpow_nonneg (hW0.trans hWle) _)) hFe) hεi
    _ = F * (c0 ^ (1 - β) * m1 ^ β) * t ^ (-(1 - β) / 2) * (ε⁻¹ * (ε ^ β * ε ^ (1 - β))) := by
        rw [htpow]; ring
    _ = F * (c0 ^ (1 - β) * m1 ^ β) * t ^ (-(1 - β) / 2) := by
        rw [← Real.rpow_add hε, add_sub_cancel, Real.rpow_one, inv_mul_cancel₀ hε.ne', mul_one]
    _ ≤ F * m1 * t ^ (-(1 - β) / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc0m1 hF) (Real.rpow_nonneg ht.le _)
    _ = m1 * t ^ (-(1 - β) / 2) * F := by ring

/-- `lem:heat-kernel`(iii) for `∂^*_μ`. -/
theorem norm_dbw_heatOp_le_holder (hε : 0 < ε) (ht : 0 < t) {β F : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖dbw ε μ (heatOp ε t f) n‖ ≤ m1 * t ^ (-(1 - β) / 2) * F := by
  rw [dbw_eq_neg_dfw, norm_neg]
  exact norm_dfw_heatOp_le_holder hε ht hβ0 hβ1 hF hf hhol μ _

end CoreLean
