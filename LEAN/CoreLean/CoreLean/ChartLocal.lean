/-
`lem:chart`(ii) of BALABAN_CORE.tex (`33871f2c529d`): there is a number `r_G ∈ (0, 1)`, depending on
`G` only, such that every `W ∈ G` with `‖W - 1‖ ≤ r_G` lies in the chart domain `N_G` and satisfies
`log W = Log W`.

`G` enters, as in `LieAlgebra.lean`, through the hypothesis that the set of its matrices is closed
(the core's "compact, hence closed").

The core argues with the inverse function theorem for `Φ(A, B) = e^{iA}e^{iB}` on `𝔤 ⊕ 𝔭`. Here the
same contradiction argument is run without the inverse function theorem and without the complement
`𝔭`:

* `norm_exp_neg_mul_exp_add_sub_le`: `‖e^{-x}e^{x+y} - 1 - y‖ ≤ 8(‖x‖ + ‖y‖)‖y‖` for
  `‖x‖ + ‖y‖ ≤ 1` (mean value inequality for `z ↦ e^{-zx}e^{z(x+y)} - zy` on the unit disc, whose
  derivative is `e^{-zx}ye^{z(x+y)} - y`);
* `tendsto_pow_of_tendsto_smul`: if `M_k → 1` and `m_k(M_k - 1) → Y`, then `M_k^{m_k} → e^Y`;
* `mem_lie_of_seq` (the core's limit step): if `M_k ∈ G`, `M_k = 1 + iB_k + o(‖B_k‖)` with
  `0 ≠ B_k → 0`, and `B_k/‖B_k‖ → u` Hermitean, then `e^{itu} = lim M_k^{⌊t/‖B_k‖⌋} ∈ G`, so `u ∈ 𝔤`;
* `eventually_log_mem`: near `1`, every `W ∈ G` has `-i Log W ∈ 𝔤`. Otherwise there are `W_n → 1` in
  `G` with `X_n ≔ -i Log W_n ∉ 𝔤`; `X_n` is Hermitean (`conjTranspose_neg_I_smul_LogM`) and tends to
  `0`. Let `A_n` be a point of `𝔤` nearest to `X_n` and `B_n ≔ X_n - A_n ≠ 0`; then `‖B_n - C‖ ≥ ‖B_n‖`
  for all `C ∈ 𝔤`, so every limit `u` of `B_n/‖B_n‖` has distance `1` from `𝔤`. But
  `M_n ≔ e^{-iA_n}W_n = e^{-iA_n}e^{i(A_n + B_n)} ∈ G` is
  `1 + iB_n + O((‖A_n‖ + ‖B_n‖)‖B_n‖)`, and the limit step gives `u ∈ 𝔤`.
* `chart_ii`: with `A ≔ -i Log W` this is the lemma; the uniqueness clause is `chart_well_defined`,
  so `log W = iA = Log W`.
-/
import CoreLean.LieAlgebra
import CoreLean.ChartLog
import CoreLean.ChartInjective

open NormedSpace Filter Metric
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

namespace CoreLean

/-! ### Two estimates in a Banach algebra -/

section Estimates

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

lemma exp_sub_one_le_two_mul {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ 1) :
    Real.exp a - 1 ≤ 2 * t := by
  have h := Real.abs_exp_sub_one_le (x := a) (by rw [abs_of_nonneg ha]; linarith)
  rw [abs_of_nonneg ha] at h
  linarith [le_abs_self (Real.exp a - 1)]

/-- `‖e^{-x}e^{x+y} - 1 - y‖ ≤ 8(‖x‖ + ‖y‖)‖y‖` for `‖x‖ + ‖y‖ ≤ 1`. -/
lemma norm_exp_neg_mul_exp_add_sub_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x y : 𝔸) (h : ‖x‖ + ‖y‖ ≤ 1) :
    ‖exp (-x) * exp (x + y) - 1 - y‖ ≤ 8 * (‖x‖ + ‖y‖) * ‖y‖ := by
  set t := ‖x‖ + ‖y‖
  set g : ℂ → 𝔸 := fun z => exp (z • -x) * exp (z • (x + y)) - z • y
  set g' : ℂ → 𝔸 := fun z => exp (z • -x) * y * exp (z • (x + y)) - y
  have hd : ∀ z : ℂ, HasDerivAt g (g' z) z := by
    intro z
    have e1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-x) z
    have e2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (x + y) z
    have e3 := (e1.mul e2).sub ((hasDerivAt_id z).smul_const y)
    have hg : g = ((fun u => exp (u • -x)) * fun u => exp (u • (x + y))) - fun u => id u • y := by
      funext u; rfl
    have hc : exp (z • (x + y)) * (x + y) = (x + y) * exp (z • (x + y)) :=
      (((Commute.refl (x + y)).smul_left z).exp_left).eq
    rw [hg]
    refine e3.congr_deriv ?_
    rw [hc, one_smul]
    simp only [g']
    noncomm_ring
  have hb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g' z‖ ≤ 8 * t * ‖y‖ := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hx0 := norm_nonneg x
    have hy0 := norm_nonneg y
    have hzx : ‖z • -x‖ ≤ ‖x‖ := by
      rw [norm_smul, norm_neg]; exact mul_le_of_le_one_left hx0 hz1
    have hzxy : ‖z • (x + y)‖ ≤ t := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans (norm_add_le _ _)
    have b1 : ‖exp (z • -x) - 1‖ ≤ 2 * t :=
      (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ _).trans
        (exp_sub_one_le_two_mul (norm_nonneg _) (by linarith) h)
    have b2 : ‖exp (z • (x + y)) - 1‖ ≤ 2 * t :=
      (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ _).trans
        (exp_sub_one_le_two_mul (norm_nonneg _) hzxy h)
    have b3 : ‖exp (z • (x + y))‖ ≤ 3 := by
      refine (norm_exp_le_of_one h1 _).trans ?_
      have := Real.exp_one_lt_d9
      have : Real.exp ‖z • (x + y)‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      linarith
    have e : g' z = (exp (z • -x) - 1) * y * exp (z • (x + y)) + y * (exp (z • (x + y)) - 1) := by
      simp only [g']; noncomm_ring
    rw [e]
    have m1 : ‖(exp (z • -x) - 1) * y * exp (z • (x + y))‖ ≤ 2 * t * ‖y‖ * 3 :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right b1 hy0)) b3 (norm_nonneg _) (by positivity))
    have m2 : ‖y * (exp (z • (x + y)) - 1)‖ ≤ ‖y‖ * (2 * t) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left b2 hy0)
    calc ‖(exp (z • -x) - 1) * y * exp (z • (x + y)) + y * (exp (z • (x + y)) - 1)‖
        ≤ 2 * t * ‖y‖ * 3 + ‖y‖ * (2 * t) := (norm_add_le _ _).trans (add_le_add m1 m2)
      _ = 8 * t * ‖y‖ := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hd z).hasDerivWithinAt) hb (convex_closedBall 0 1)
    (mem_closedBall_self zero_le_one) (by simp : (1 : ℂ) ∈ closedBall (0 : ℂ) 1)
  have e : g 1 - g 0 = exp (-x) * exp (x + y) - 1 - y := by
    simp only [g, one_smul, zero_smul, exp_zero, mul_one]; abel
  rw [e, sub_zero, norm_one, mul_one] at hmv
  exact hmv

/-- If `M_k - 1 → 0` and `m_k(M_k - 1) → Y`, then `M_k^{m_k} → e^Y`. -/
lemma tendsto_pow_of_tendsto_smul (h1 : ‖(1 : 𝔸)‖ ≤ 1) {M : ℕ → 𝔸} {m : ℕ → ℕ} {Y : 𝔸}
    (hZ : Tendsto (fun k => M k - 1) atTop (𝓝 0))
    (hY : Tendsto (fun k => (m k : ℂ) • (M k - 1)) atTop (𝓝 Y)) :
    Tendsto (fun k => M k ^ m k) atTop (𝓝 (exp Y)) := by
  have he : Tendsto (fun k => exp (M k - 1) ^ m k) atTop (𝓝 (exp Y)) := by
    have : (fun k => exp (M k - 1) ^ m k) = fun k => exp ((m k : ℂ) • (M k - 1)) :=
      funext fun k => (exp_natCast_smul _ _).symm
    rw [this]; exact ((continuous_exp_of_one h1).tendsto Y).comp hY
  have hdiff : Tendsto (fun k => M k ^ m k - exp (M k - 1) ^ m k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hZn : Tendsto (fun k => ‖M k - 1‖) atTop (𝓝 0) := by simpa using hZ.norm
    have hlim : Tendsto (fun k => Real.exp ‖(m k : ℂ) • (M k - 1)‖ * ‖(m k : ℂ) • (M k - 1)‖ *
        ‖M k - 1‖) atTop (𝓝 (Real.exp ‖Y‖ * ‖Y‖ * 0)) :=
      (((Real.continuous_exp.tendsto _).comp hY.norm).mul hY.norm).mul hZn
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hZn.eventually (ge_mem_nhds one_pos)] with k hk
    set Z := M k - 1
    have hM : ‖M k‖ ≤ Real.exp ‖Z‖ := by
      calc ‖M k‖ = ‖1 + Z‖ := by simp [Z]
        _ ≤ ‖(1 : 𝔸)‖ + ‖Z‖ := norm_add_le _ _
        _ ≤ Real.exp ‖Z‖ := by linarith [Real.add_one_le_exp ‖Z‖]
    have hp := norm_pow_sub_pow_le h1 hM (norm_exp_le_of_one h1 Z) (m k)
    have hq : ‖M k - exp Z‖ ≤ ‖Z‖ ^ 2 := by
      have := norm_exp_sub_one_sub_le Z hk
      rw [← norm_neg]; convert this using 2; simp only [Z]; abel
    have hYn : ‖(m k : ℂ) • Z‖ = m k * ‖Z‖ := by rw [norm_smul, Complex.norm_natCast]
    have hpow : Real.exp ‖Z‖ ^ (m k - 1) ≤ Real.exp ‖(m k : ℂ) • Z‖ := by
      rw [← Real.exp_nat_mul, hYn]; apply Real.exp_le_exp.mpr
      have : ((m k - 1 : ℕ) : ℝ) ≤ m k := by exact_mod_cast Nat.sub_le _ _
      nlinarith [norm_nonneg Z]
    calc ‖M k ^ m k - exp Z ^ m k‖ ≤ m k * Real.exp ‖Z‖ ^ (m k - 1) * ‖M k - exp Z‖ := hp
      _ ≤ m k * Real.exp ‖(m k : ℂ) • Z‖ * ‖Z‖ ^ 2 := by gcongr
      _ = Real.exp ‖(m k : ℂ) • Z‖ * ‖(m k : ℂ) • Z‖ * ‖Z‖ := by rw [hYn]; ring
  simpa using hdiff.add he

end Estimates

/-! ### The local chart of a closed gauge group -/

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

lemma LogM_one : LogM (1 : Mat) = 0 := by
  have := LogM_exp (N := N) (Z := 0) (by simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  rwa [exp_zero] at this

/-- For a unitary `W` with `‖W - 1‖ < 1` and `‖Log W‖ < 1/4`, the matrix `-i Log W` is Hermitean. -/
lemma conjTranspose_neg_I_smul_LogM {W : Mat} (hW : W ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (h1 : ‖W - 1‖ < 1) (hL : ‖LogM W‖ < 1 / 4) :
    (-(Complex.I • LogM W)).conjTranspose = -(Complex.I • LogM W) := by
  set L := LogM W
  have hexp : exp L = W := exp_LogM h1
  have hstar : exp L.conjTranspose = W.conjTranspose := by
    rw [Matrix.exp_conjTranspose, hexp]
  have hneg : exp (-L) = W.conjTranspose := by
    have hWW : W * star W = 1 := (Matrix.mem_unitaryGroup_iff).1 hW
    calc exp (-L) = exp (-L) * (W * star W) := by rw [hWW, mul_one]
      _ = (exp (-L) * exp L) * star W := by rw [hexp, mul_assoc]
      _ = W.conjTranspose := by
        rw [BakerCampbellHausdorff.exp_neg_mul_exp ℂ, one_mul, Matrix.star_eq_conjTranspose]
  have hLH : L.conjTranspose = -L :=
    BakerCampbellHausdorff.exp_injOn ℂ
      (mem_ball_zero_iff.mpr (by rwa [Matrix.l2_opNorm_conjTranspose]))
      (mem_ball_zero_iff.mpr (by rwa [norm_neg])) (hstar.trans hneg.symm)
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hLH, Complex.star_def,
    Complex.conj_I, smul_neg, neg_smul, neg_neg]

namespace GaugeGroup

variable {G : GaugeGroup N}

lemma unitary_of_mem_mats {W : Mat} (hW : W ∈ G.mats) : W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  obtain ⟨U, hU, rfl⟩ := hW
  exact G.unitary U hU

/-- The limit step of the core's proof of `lem:chart`(ii): if `M_k ∈ G`,
`‖M_k - 1 - iB_k‖ ≤ ε_k‖B_k‖` with `ε_k → 0` and `0 ≠ B_k → 0`, and `B_k/‖B_k‖ → u` with `u`
Hermitean, then `u ∈ 𝔤`. -/
theorem mem_lie_of_seq (hG : IsClosed G.mats) {M B : ℕ → Mat} {ε : ℕ → ℝ} {u : Mat}
    (hM : ∀ k, M k ∈ G.mats) (hB0 : ∀ k, B k ≠ 0) (hB : Tendsto B atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) (hbd : ∀ k, ‖M k - 1 - Complex.I • B k‖ ≤ ε k * ‖B k‖)
    (hu : Tendsto (fun k => ((‖B k‖⁻¹ : ℝ) : ℂ) • B k) atTop (𝓝 u))
    (huH : u.conjTranspose = u) : u ∈ G.lie := by
  have hBpos : ∀ k, 0 < ‖B k‖ := fun k => norm_pos_iff.mpr (hB0 k)
  have hε0 : ∀ k, 0 ≤ ε k := fun k =>
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbd k)) (hBpos k)
  have hBn : Tendsto (fun k => ‖B k‖) atTop (𝓝 0) := by simpa using hB.norm
  have hpos : ∀ t : ℝ, 0 ≤ t → exp ((Complex.I * t) • u) ∈ G.mats := by
    intro t ht
    set m : ℕ → ℕ := fun k => ⌊t / ‖B k‖⌋₊
    have hm_le : ∀ k, (m k : ℝ) * ‖B k‖ ≤ t := fun k => by
      have := Nat.floor_le (div_nonneg ht (hBpos k).le)
      rwa [le_div_iff₀ (hBpos k)] at this
    have hm_ge : ∀ k, t - ‖B k‖ ≤ (m k : ℝ) * ‖B k‖ := fun k => by
      have := Nat.lt_floor_add_one (t / ‖B k‖)
      rw [div_lt_iff₀ (hBpos k)] at this
      linarith
    have hmB : Tendsto (fun k => (m k : ℝ) * ‖B k‖) atTop (𝓝 t) := by
      have hl : Tendsto (fun k => t - ‖B k‖) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).sub hBn
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hm_ge hm_le
    -- `M_k - 1 → 0`
    have hZ : Tendsto (fun k => M k - 1) atTop (𝓝 0) := by
      have hlim : Tendsto (fun k => (1 + ε k) * ‖B k‖) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.add hε).mul hBn
      refine squeeze_zero_norm (fun k => ?_) hlim
      calc ‖M k - 1‖ = ‖(M k - 1 - Complex.I • B k) + Complex.I • B k‖ := by rw [sub_add_cancel]
        _ ≤ ε k * ‖B k‖ + ‖B k‖ := (norm_add_le _ _).trans (add_le_add (hbd k) (norm_I_smul' _).le)
        _ = (1 + ε k) * ‖B k‖ := by ring
    -- `m_k(M_k - 1) → itu`
    have hY : Tendsto (fun k => (m k : ℂ) • (M k - 1)) atTop (𝓝 ((Complex.I * t) • u)) := by
      have e : ∀ k, (m k : ℂ) • (M k - 1) =
          Complex.I • ((((m k : ℝ) * ‖B k‖ : ℝ) : ℂ) • (((‖B k‖⁻¹ : ℝ) : ℂ) • B k)) +
            (m k : ℂ) • (M k - 1 - Complex.I • B k) := fun k => by
        have hne : (‖B k‖ : ℂ) ≠ 0 := by exact_mod_cast (hBpos k).ne'
        have hcoef : ((((m k : ℝ) * ‖B k‖ : ℝ) : ℂ) • (((‖B k‖⁻¹ : ℝ) : ℂ) • B k)) =
            (m k : ℂ) • B k := by
          rw [smul_smul]; congr 1; push_cast; field_simp
        rw [hcoef, smul_comm Complex.I (m k : ℂ) (B k),
          smul_sub (m k : ℂ) (M k - 1) (Complex.I • B k)]
        abel
      have h1 : Tendsto (fun k => Complex.I • ((((m k : ℝ) * ‖B k‖ : ℝ) : ℂ) •
          (((‖B k‖⁻¹ : ℝ) : ℂ) • B k))) atTop (𝓝 (Complex.I • ((t : ℂ) • u))) :=
        (((Complex.continuous_ofReal.tendsto t).comp hmB).smul hu).const_smul Complex.I
      have h2 : Tendsto (fun k => (m k : ℂ) • (M k - 1 - Complex.I • B k)) atTop (𝓝 0) := by
        have hlim : Tendsto (fun k => t * ε k) atTop (𝓝 0) := by simpa using hε.const_mul t
        refine squeeze_zero_norm (fun k => ?_) hlim
        rw [norm_smul, Complex.norm_natCast]
        calc (m k : ℝ) * ‖M k - 1 - Complex.I • B k‖ ≤ (m k : ℝ) * (ε k * ‖B k‖) :=
              mul_le_mul_of_nonneg_left (hbd k) (Nat.cast_nonneg _)
          _ = ε k * ((m k : ℝ) * ‖B k‖) := by ring
          _ ≤ ε k * t := mul_le_mul_of_nonneg_left (hm_le k) (hε0 k)
          _ = t * ε k := by ring
      have := h1.add h2
      rw [add_zero, smul_smul] at this
      exact this.congr (fun k => (e k).symm)
    exact hG.mem_of_tendsto (tendsto_pow_of_tendsto_smul norm_one_le hZ hY)
      (Eventually.of_forall fun k => mats_pow (hM k) _)
  refine ⟨huH, fun t => ?_⟩
  rw [← exp_mem_mats_iff]
  rcases le_total 0 t with ht | ht
  · exact hpos t ht
  · have h := (exp_mem_mats_iff _).1 (hpos (-t) (by linarith))
    rw [exp_mem_mats_iff]
    have e : expU ((Complex.I * (t : ℂ)) • u) = (expU ((Complex.I * ((-t : ℝ) : ℂ)) • u))⁻¹ := by
      refine Units.ext ?_
      rw [expU_val, expU_inv_val, ← neg_smul]
      congr 2; push_cast; ring
    rw [e]; exact G.carrier.inv_mem h

/-- Near `1`, every matrix `W` of `G` has `-i Log W ∈ 𝔤`. -/
theorem eventually_log_mem (hG : IsClosed G.mats) :
    ∀ᶠ W in 𝓝 (1 : Mat), W ∈ G.mats → -(Complex.I • LogM W) ∈ G.lie := by
  have : ProperSpace Mat := FiniteDimensional.proper_rclike ℂ Mat
  by_contra hcon
  rw [not_eventually] at hcon
  have hLc : Tendsto (LogM (N := N)) (𝓝 1) (𝓝 0) := by
    have := (analyticOnNhd_LogM (N := N) 1 (by simp)).continuousAt
    rwa [ContinuousAt, LogM_one] at this
  have hsmall : ∀ᶠ W in 𝓝 (1 : Mat), ‖LogM W‖ < 1 / 8 ∧ ‖W - 1‖ < 1 := by
    refine (hLc.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : Mat)‖ < 1 / 8))).and ?_
    filter_upwards [ball_mem_nhds (1 : Mat) one_pos] with W hW
    rwa [mem_ball, dist_eq_norm] at hW
  have hfreq := (hcon.mono fun W h => not_imp.mp h).and_eventually hsmall
  have hseq : ∀ n : ℕ, ∃ W : Mat, ((W ∈ G.mats ∧ -(Complex.I • LogM W) ∉ G.lie) ∧
      (‖LogM W‖ < 1 / 8 ∧ ‖W - 1‖ < 1)) ∧ W ∈ ball (1 : Mat) (1 / ((n : ℝ) + 1)) := fun n =>
    (hfreq.and_eventually (ball_mem_nhds (1 : Mat) (Nat.one_div_pos_of_nat (n := n)))).exists
  choose W hW using hseq
  have hWlim : Tendsto W atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (mem_ball.mp (hW n).2).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- `X_n = -i Log W_n`: Hermitean, not in `𝔤`, tending to `0`
  set X : ℕ → Mat := fun n => -(Complex.I • LogM (W n))
  have hXn : ∀ n, ‖X n‖ = ‖LogM (W n)‖ := fun n => by simp only [X, norm_neg, norm_I_smul']
  have hX8 : ∀ n, ‖X n‖ < 1 / 8 := fun n => by rw [hXn]; exact (hW n).1.2.1
  have hXH : ∀ n, (X n).conjTranspose = X n := fun n =>
    conjTranspose_neg_I_smul_LogM (unitary_of_mem_mats (hW n).1.1.1) (hW n).1.2.2
      (by linarith [(hW n).1.2.1])
  have hXlim : Tendsto (fun n => ‖X n‖) atTop (𝓝 0) := by
    simp only [hXn]; simpa using (hLc.comp hWlim).norm
  -- the nearest points `A_n ∈ 𝔤` and the remainders `B_n = X_n - A_n`
  have hne : (G.lie).Nonempty := ⟨0, G.zero_mem_lie⟩
  choose A hA hAd using fun n => (isClosed_lie hG).exists_infDist_eq_dist hne (X n)
  set B : ℕ → Mat := fun n => X n - A n
  have hmin : ∀ n, ∀ C ∈ G.lie, ‖B n‖ ≤ ‖B n - C‖ := fun n C hC => by
    have h := infDist_le_dist_of_mem (x := X n) (add_mem_lie hG (hA n) hC)
    rw [hAd n, dist_eq_norm, dist_eq_norm] at h
    simpa only [B, sub_sub] using h
  have hBX : ∀ n, ‖B n‖ ≤ ‖X n‖ := fun n => by
    have h := infDist_le_dist_of_mem (x := X n) G.zero_mem_lie
    rw [hAd n, dist_eq_norm, dist_eq_norm, sub_zero] at h
    exact h
  have hAX : ∀ n, ‖A n‖ ≤ 2 * ‖X n‖ := fun n => by
    have : A n = X n - B n := by simp only [B, sub_sub_cancel]
    rw [this]; linarith [norm_sub_le (X n) (B n), hBX n]
  have hB0 : ∀ n, B n ≠ 0 := fun n hBn => by
    have : X n = A n := sub_eq_zero.mp hBn
    exact (hW n).1.1.2 (by have h := hA n; rw [← this] at h; exact h)
  have hBpos : ∀ n, 0 < ‖B n‖ := fun n => norm_pos_iff.mpr (hB0 n)
  have hBH : ∀ n, (B n).conjTranspose = B n := fun n => by
    simp only [B, Matrix.conjTranspose_sub, hXH n, (hA n).1]
  -- the directions `u_n = B_n/‖B_n‖` and a limit `u`
  set v : ℕ → Mat := fun n => ((‖B n‖⁻¹ : ℝ) : ℂ) • B n
  have hv1 : ∀ n, v n ∈ sphere (0 : Mat) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hBpos n)), inv_mul_cancel₀ (hBpos n).ne']
  obtain ⟨u, -, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Mat) 1).tendsto_subseq hv1
  have huH : u.conjTranspose = u := by
    refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).mem_of_tendsto hlim
      (Eventually.of_forall fun k => ?_)
    show (v (φ k)).conjTranspose = v (φ k)
    simp only [v, Matrix.conjTranspose_smul, hBH, Complex.star_def, Complex.conj_ofReal]
  -- `u` has distance `1` from `𝔤`
  have hfar : ∀ C ∈ G.lie, 1 ≤ ‖u - C‖ := fun C hC => by
    refine ge_of_tendsto (hlim.sub_const C).norm (Eventually.of_forall fun k => ?_)
    set n := φ k
    have hC' : ((‖B n‖ : ℝ) : ℂ) • C ∈ G.lie := G.smul_mem_lie hC _
    have hne : (‖B n‖ : ℂ) ≠ 0 := by exact_mod_cast (hBpos n).ne'
    have e : v n - C = ((‖B n‖⁻¹ : ℝ) : ℂ) • (B n - ((‖B n‖ : ℝ) : ℂ) • C) := by
      show ((‖B n‖⁻¹ : ℝ) : ℂ) • B n - C = _
      rw [smul_sub (((‖B n‖⁻¹ : ℝ) : ℂ)) (B n) _, smul_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (hBpos n).ne', Complex.ofReal_one, one_smul]
    show 1 ≤ ‖v n - C‖
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hBpos n))]
    rw [le_inv_mul_iff₀ (hBpos n), mul_one]
    exact hmin n _ hC'
  -- the limit step along the subsequence
  have hX0 : Tendsto (fun k => ‖X (φ k)‖) atTop (𝓝 0) := hXlim.comp hφ.tendsto_atTop
  have hulie : u ∈ G.lie := by
    refine mem_lie_of_seq hG (M := fun k => exp (Complex.I • -A (φ k)) * W (φ k))
      (B := fun k => B (φ k)) (ε := fun k => 8 * (‖A (φ k)‖ + ‖B (φ k)‖)) (fun k => ?_)
      (fun k => hB0 _) ?_ ?_ (fun k => ?_) hlim huH
    · refine mats_mul ?_ (hW _).1.1.1
      rw [exp_mem_mats_iff]
      have := (G.neg_mem_lie (hA (φ k))).2 1
      simpa using this
    · refine squeeze_zero_norm (fun k => hBX (φ k)) hX0
    · have : Tendsto (fun k => 8 * (3 * ‖X (φ k)‖)) atTop (𝓝 0) := by
        simpa using (hX0.const_mul 3).const_mul 8
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) this
      have := hAX (φ k); have := hBX (φ k); gcongr; linarith
    · set n := φ k
      have hWe : W n = exp (Complex.I • A n + Complex.I • B n) := by
        rw [← smul_add, show A n + B n = X n by simp only [B, add_sub_cancel], show
          Complex.I • X n = LogM (W n) by simp only [X, smul_neg, smul_smul, Complex.I_mul_I,
            neg_one_smul, neg_neg], exp_LogM (hW n).1.2.2]
      have hsum : ‖Complex.I • A n‖ + ‖Complex.I • B n‖ ≤ 1 := by
        rw [norm_I_smul', norm_I_smul']; linarith [hAX n, hBX n, hX8 n]
      have h := norm_exp_neg_mul_exp_add_sub_le norm_one_le _ _ hsum
      rw [norm_I_smul', norm_I_smul', ← hWe, ← smul_neg] at h
      simpa only [norm_I_smul'] using h
  have h1 := hfar u hulie
  rw [sub_self, norm_zero] at h1
  exact absurd h1 (by norm_num)

/-- `lem:chart`(ii): there is `r_G ∈ (0, 1)`, depending on `G` only, such that every `U ∈ G` with
`‖U - 1‖ ≤ r_G` lies in the chart domain, `U = e^{iA}` with `A ∈ 𝔤` and `‖A‖ < π`, and its chart value
`iA` (unique by `chart_well_defined`) is `Log U`. -/
theorem chart_ii (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ U ∈ G.carrier, ‖(U : Mat) - 1‖ ≤ r →
      ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧ exp (Complex.I • A) = (U : Mat) ∧
        LogM (U : Mat) = Complex.I • A ∧
        ∀ A' ∈ G.lie, ‖A'‖ < Real.pi → exp (Complex.I • A') = (U : Mat) → A' = A := by
  have hLc : Tendsto (LogM (N := N)) (𝓝 1) (𝓝 0) := by
    have := (analyticOnNhd_LogM (N := N) 1 (by simp)).continuousAt
    rwa [ContinuousAt, LogM_one] at this
  have hsmall : ∀ᶠ W in 𝓝 (1 : Mat), ‖LogM W‖ < 1 / 8 ∧ ‖W - 1‖ < 1 := by
    refine (hLc.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : Mat)‖ < 1 / 8))).and ?_
    filter_upwards [ball_mem_nhds (1 : Mat) one_pos] with W hW
    rwa [mem_ball, dist_eq_norm] at hW
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ((eventually_log_mem hG).and hsmall)
  refine ⟨min (1 / 2) (δ / 2), by positivity, (min_le_left _ _).trans_lt (by norm_num),
    fun U hU hUr => ?_⟩
  have hd : dist (U : Mat) 1 < δ := by
    rw [dist_eq_norm]; linarith [min_le_right (1 / 2 : ℝ) (δ / 2)]
  obtain ⟨hlog, hL8, hU1⟩ := hball hd
  have hmem : -(Complex.I • LogM (U : Mat)) ∈ G.lie := hlog ⟨U, hU, rfl⟩
  have hnorm : ‖-(Complex.I • LogM (U : Mat))‖ < Real.pi := by
    rw [norm_neg, norm_I_smul']; linarith [Real.pi_gt_three]
  have hI : Complex.I • -(Complex.I • LogM (U : Mat)) = LogM (U : Mat) := by
    rw [smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  have hexp : exp (Complex.I • -(Complex.I • LogM (U : Mat))) = (U : Mat) := by
    rw [hI]; exact exp_LogM hU1
  refine ⟨_, hmem, hnorm, hexp, hI.symm, fun A' hA' hA'n hA'e => ?_⟩
  exact ChartBounds.chart_well_defined hA' hmem hA'n hnorm (hA'e.trans hexp.symm)

end GaugeGroup

end CoreLean

end
