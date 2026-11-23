/-
`lem:group-mean` of BALABAN_CORE.tex (`8913c33305b3`): the inverses and the statements on `G`.

* `psi_neg_left`: `Ψ(-Y, Z) = -Ad_{e^{-iZ}}Ψ(Y, -Z)`, from `e^{-iY}e^{iZ} = Ad_{e^{-iZ}}(e^{iY}e^{-iZ})⁻¹`.
* `mean_inverse`: for `W_i = e^{iY_i}W_1` and `W = e^{iZ}W_1` with `Σ_iΨ(Y_i, -Z) = 0`, the inverses are
  `W_i⁻¹ = e^{iY'_i}W_1⁻¹`, `W⁻¹ = e^{iZ'}W_1⁻¹` with `Y'_i = -Ad_{W_1}^{-1}Y_i`, `Z' = -Ad_{W_1}^{-1}Z`, and
  `Σ_iΨ(Y'_i, -Z') = 0`; with `‖Ad_{W_1}^{-1}X‖ ≤ 2‖X‖` the norms are those the condition and the ball
  require, so that by the uniqueness (`group_mean`) `𝗆({W_i⁻¹}) = 𝗆({W_i})⁻¹` (`mean_inverse_unique`).
* `elements_of_G`: `W_i ∈ G` with `‖W_iW_1⁻¹ - id‖ ≤ ϱ ≤ r_G` gives `W_iW_1⁻¹ = e^{iY_i}`, `Y_i ∈ 𝔤`,
  `‖Y_i‖ ≤ (π/2)ϱ` (`lem:chart`(ii), (iii)).
* `psi_mem_lie`, `group_mean_lie`: for `Y_i ∈ 𝔤` the map `T` preserves the ball of `𝔤`, the solution lies in
  `𝔤`, and the mean `e^{iZ}W_1` lies in `G`.
-/
import CoreLean.GroupMean
import CoreLean.RegularAverages

open NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace GroupMean

open RegularAverages

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

lemma log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9

theorem exp_small_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx)
  rw [abs_of_nonneg hx0] at this
  linarith [le_abs_self (Real.exp x - 1)]

/-- `‖Ad_g X‖ ≤ ‖g‖‖X‖‖g⁻¹‖`. -/
lemma norm_Ad_le (g : GLN) (X : Mat) : ‖Ad g X‖ ≤ ‖(g : Mat)‖ * ‖X‖ * ‖((g⁻¹ : GLN) : Mat)‖ := by
  unfold Ad
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- `Ψ(-Y, Z) = -Ad_{e^{-iZ}}Ψ(Y, -Z)` for `‖Y‖, ‖Z‖ ≤ 1/16`. -/
theorem psi_neg_left {Y Z : Mat} (hY : ‖Y‖ ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) :
    psi (-Y) Z = -Ad (expU (Complex.I • -Z)) (psi Y (-Z)) := by
  have hl := log2_gt
  set A := psi Y (-Z) with hAd
  set g := expU (Complex.I • -Z) with hg
  have hA : expU (Complex.I • A) = expU (Complex.I • Y) * expU (Complex.I • -Z) :=
    Units.ext (by
      rw [Units.val_mul, expU_val, expU_val, expU_val]
      exact exp_I_psi (by rw [norm_neg]; linarith))
  have hB : expU (Complex.I • psi (-Y) Z) = expU (Complex.I • -Y) * expU (Complex.I • Z) :=
    Units.ext (by
      rw [Units.val_mul, expU_val, expU_val, expU_val]
      exact exp_I_psi (by rw [norm_neg]; linarith))
  have hC : expU (Complex.I • -Ad g A) = expU (Complex.I • -Y) * expU (Complex.I • Z) := by
    have e1 : Complex.I • -Ad g A = Ad g (-(Complex.I • A)) := by rw [Ad_neg, Ad_smul, smul_neg]
    rw [e1, ← expU_conj, ← expU_inv, hA, hg]
    have i1 : expU (Complex.I • -Z) = (expU (Complex.I • Z))⁻¹ := by rw [expU_inv, smul_neg]
    have i2 : expU (Complex.I • -Y) = (expU (Complex.I • Y))⁻¹ := by rw [expU_inv, smul_neg]
    rw [i1, i2]
    group
  have hY' : ‖-Y‖ ≤ 1 / 16 := by rw [norm_neg]; exact hY
  have hZ' : ‖-Z‖ ≤ 1 / 16 := by rw [norm_neg]; exact hZ
  have hpn : ‖psi (-Y) Z‖ ≤ 1 / 4 := norm_psi_le (X := -Y) (Y := Z) hY' hZ
  have hAn : ‖psi Y (-Z)‖ ≤ 1 / 4 := norm_psi_le (X := Y) (Y := -Z) hY hZ'
  have hgn : ‖(g : Mat)‖ ≤ 1 + 2 * (1 / 16) := by
    rw [hg, expU_val]
    refine (norm_exp_le' _).trans (exp_small_le (norm_nonneg _) ?_ |>.trans ?_)
    · rw [norm_I_smul', norm_neg]; linarith
    · rw [norm_I_smul', norm_neg]; linarith
  have hgi : ‖((g⁻¹ : GLN) : Mat)‖ ≤ 1 + 2 * (1 / 16) := by
    rw [hg, expU_inv, expU_val]
    refine (norm_exp_le' _).trans (exp_small_le (norm_nonneg _) ?_ |>.trans ?_)
    · rw [norm_neg, norm_I_smul', norm_neg]; linarith
    · rw [norm_neg, norm_I_smul', norm_neg]; linarith
  have hAdn : ‖Ad g A‖ ≤ 1 / 3 := by
    refine (norm_Ad_le g A).trans ?_
    have := mul_le_mul (mul_le_mul hgn hAn (norm_nonneg _) (by norm_num)) hgi (norm_nonneg _)
      (by norm_num)
    linarith
  have k1 : LogM (exp (Complex.I • psi (-Y) Z)) = Complex.I • psi (-Y) Z :=
    LogM_exp (by rw [norm_I_smul']; linarith)
  have k2 : LogM (exp (Complex.I • -Ad g A)) = Complex.I • -Ad g A :=
    LogM_exp (by rw [norm_I_smul', norm_neg]; linarith)
  have heq : exp (Complex.I • psi (-Y) Z) = exp (Complex.I • -Ad g A) := by
    have := congrArg (fun u : GLN => (u : Mat)) (hB.trans hC.symm)
    simpa only [expU_val] using this
  have := k1.symm.trans ((congrArg LogM heq).trans k2)
  exact smul_right_injective Mat Complex.I_ne_zero this

variable {n : ℕ}

/-- The inverses: the exponents of `W_i⁻¹` and of `W⁻¹` relative to `W_1⁻¹` are `-Ad_{W_1}^{-1}Y_i` and
`-Ad_{W_1}^{-1}Z`, and they solve the equation of the inverses. -/
theorem mean_inverse (Y : Fin n → Mat) (Z : Mat) (W₁ : GLN) (hY : ∀ i, ‖Y i‖ ≤ 1 / 16)
    (hZ : ‖Z‖ ≤ 1 / 16) (hsol : ∑ i, psi (Y i) (-Z) = 0) :
    (∀ i, (expU (Complex.I • Y i) * W₁)⁻¹ = expU (Complex.I • -Ad W₁⁻¹ (Y i)) * W₁⁻¹) ∧
      (expU (Complex.I • Z) * W₁)⁻¹ = expU (Complex.I • -Ad W₁⁻¹ Z) * W₁⁻¹ ∧
      ∑ i, psi (-Ad W₁⁻¹ (Y i)) (-(-Ad W₁⁻¹ Z)) = 0 := by
  have hexp : ∀ X : Mat, (expU (Complex.I • X) * W₁)⁻¹ = expU (Complex.I • -Ad W₁⁻¹ X) * W₁⁻¹ :=
    fun X => by
      rw [show Complex.I • -Ad W₁⁻¹ X = Ad W₁⁻¹ (-(Complex.I • X)) by rw [Ad_neg, Ad_smul, smul_neg],
        ← expU_conj, ← expU_inv]
      group
  refine ⟨fun i => hexp (Y i), hexp Z, ?_⟩
  have e : ∀ i, psi (-Ad W₁⁻¹ (Y i)) (-(-Ad W₁⁻¹ Z)) =
      Ad W₁⁻¹ (-Ad (expU (Complex.I • -Z)) (psi (Y i) (-Z))) := fun i => by
    rw [neg_neg, ← Ad_neg, ← Ad_psi, psi_neg_left (hY i) hZ]
  simp only [e, ← Ad_sum, Finset.sum_neg_distrib, ← Ad_sum, hsol]
  simp [Ad]

/-- With `‖Ad_{W_1}^{-1}X‖ ≤ 2‖X‖`: if the `Y_i` satisfy the condition with `M`, the inverses satisfy it
with `2M`, the exponent of `W⁻¹` lies in the ball of radius `4M`, and it is the unique solution there:
`𝗆({W_i⁻¹}) = 𝗆({W_i})⁻¹`. -/
theorem mean_inverse_unique (hn : 0 < n) (Y : Fin n → Mat) (Z : Mat) (W₁ : GLN) (M : ℝ)
    (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 1024 * M ≤ 1) (hZ : ‖Z‖ ≤ 2 * M) (hsol : ∑ i, psi (Y i) (-Z) = 0)
    (hAd : ∀ X : Mat, ‖Ad W₁⁻¹ X‖ ≤ 2 * ‖X‖) :
    (∀ i, ‖-Ad W₁⁻¹ (Y i)‖ ≤ 2 * M) ∧ ‖-Ad W₁⁻¹ Z‖ ≤ 2 * (2 * M) ∧
      ∀ Z' : Mat, ‖Z'‖ ≤ 2 * (2 * M) → ∑ i, psi (-Ad W₁⁻¹ (Y i)) (-Z') = 0 → Z' = -Ad W₁⁻¹ Z := by
  have hM0 : 0 ≤ M := M_nonneg hn Y M hYM
  have hY16 : ∀ i, ‖Y i‖ ≤ 1 / 16 := fun i => by linarith [hYM i]
  have hZ16 : ‖Z‖ ≤ 1 / 16 := by linarith
  obtain ⟨-, -, hinv⟩ := mean_inverse Y Z W₁ hY16 hZ16 hsol
  have hY' : ∀ i, ‖-Ad W₁⁻¹ (Y i)‖ ≤ 2 * M := fun i => by
    rw [norm_neg]; linarith [hAd (Y i), hYM i]
  have hZ' : ‖-Ad W₁⁻¹ Z‖ ≤ 2 * (2 * M) := by rw [norm_neg]; linarith [hAd Z]
  refine ⟨hY', hZ', fun Z' hZ'n hsol' => ?_⟩
  obtain ⟨Z₀, -, huniq⟩ := group_mean hn (fun i => -Ad W₁⁻¹ (Y i)) (2 * M) hY' (by linarith)
  exact (huniq Z' ⟨hZ'n, hsol'⟩).trans (huniq _ ⟨hZ', hinv⟩).symm

/-! ### Elements of `G` -/

/-- `lem:chart`(ii), (iii) for the condition: `W_i ∈ G` with `‖W_iW_1⁻¹ - id‖ ≤ ϱ ≤ r_G` gives
`W_iW_1⁻¹ = e^{iY_i}` with `Y_i ∈ 𝔤` and `‖Y_i‖ ≤ (π/2)ϱ`. -/
theorem elements_of_G (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ W W₁ : GLN, W ∈ G.carrier → W₁ ∈ G.carrier → ∀ ρ : ℝ,
      ‖((W * W₁⁻¹ : GLN) : Mat) - 1‖ ≤ ρ → ρ ≤ r →
      ∃ Y ∈ G.lie, W * W₁⁻¹ = expU (Complex.I • Y) ∧ ‖Y‖ ≤ Real.pi / 2 * ρ := by
  obtain ⟨r, hr0, -, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  refine ⟨r, hr0, fun W W₁ hW hW₁ ρ hρ hρr => ?_⟩
  have hmem : W * W₁⁻¹ ∈ G.carrier := G.carrier.mul_mem hW (G.carrier.inv_mem hW₁)
  obtain ⟨A, hA, hAn, hAe, -, -⟩ := hch _ hmem (hρ.trans hρr)
  refine ⟨A, hA, Units.ext (by rw [expU_val]; exact hAe.symm), ?_⟩
  have h3 := (ChartBounds.chart_iii hA.1 hAn.le).2.1
  rw [hAe] at h3
  exact h3.trans (mul_le_mul_of_nonneg_left hρ (by positivity))

/-- For `Y, Z ∈ 𝔤` small, `Ψ(Y, -Z) ∈ 𝔤`: `e^{iY}e^{-iZ}` is an element of `G` near `id`. -/
theorem psi_mem_lie (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c : ℝ, 0 < c ∧ ∀ Y Z : Mat, Y ∈ G.lie → Z ∈ G.lie → ‖Y‖ ≤ c → ‖Z‖ ≤ c → psi Y (-Z) ∈ G.lie := by
  obtain ⟨r, hr0, -, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  refine ⟨min (1 / 16) (r / 4), lt_min (by norm_num) (by linarith), fun Y Z hY hZ hYc hZc => ?_⟩
  have hc1 := min_le_left (1 / 16 : ℝ) (r / 4)
  have hc2 := min_le_right (1 / 16 : ℝ) (r / 4)
  have hexpG : ∀ X ∈ G.lie, expU (Complex.I • X) ∈ G.carrier := fun X hX => by
    simpa using hX.2 1
  set W := expU (Complex.I • Y) * expU (Complex.I • -Z) with hW
  have hWG : W ∈ G.carrier := G.carrier.mul_mem (hexpG Y hY) (hexpG _ (G.neg_mem_lie hZ))
  have hWv : (W : Mat) = ([Complex.I • Y, Complex.I • -Z].map exp).prod := by
    simp [hW]
  have hT : (([Complex.I • Y, Complex.I • -Z]).map norm).sum ≤ ‖Y‖ + ‖Z‖ := by
    simp [norm_I_smul']
  have hsm := (prod_exp_small _ hT (by linarith)).2
  rw [← hWv] at hsm
  obtain ⟨A, hA, -, -, hlog, -⟩ := hch W hWG (hsm.trans (by linarith))
  have : psi Y (-Z) = A := by
    rw [psi_eq_Log]
    have hv : exp (Complex.I • Y) * exp (Complex.I • -Z) = (W : Mat) := by simp [hW]
    rw [hv, hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  rw [this]; exact hA

/-- `lem:group-mean` for elements of `G`: for `Y_i ∈ 𝔤`, the solution lies in `𝔤` and the mean
`e^{iZ}W_1` of elements of `G` lies in `G`. -/
theorem group_mean_lie (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} (_hn : 0 < n) (Y : Fin n → Mat) (M : ℝ), (∀ i, ‖Y i‖ ≤ M) →
      512 * M ≤ 1 → 2 * M ≤ c → (∀ i, Y i ∈ G.lie) →
      ∃ Z ∈ G.lie, ‖Z‖ ≤ 2 * M ∧ ∑ i, psi (Y i) (-Z) = 0 ∧
        ∀ W₁ ∈ G.carrier, expU (Complex.I • Z) * W₁ ∈ G.carrier := by
  obtain ⟨c, hc0, hpsi⟩ := psi_mem_lie G hG
  refine ⟨c, hc0, fun {n} hn Y M hYM hM hMc hY => ?_⟩
  have hM0 := M_nonneg hn Y M hYM
  have hTC : ∀ Z ∈ G.lie, ‖Z‖ ≤ 2 * M → T Y Z ∈ G.lie := fun Z hZ hZn => by
    have hsum : ∑ i, (Y i + Phi (Y i) (-Z)) ∈ G.lie := by
      refine Finset.sum_induction _ (· ∈ G.lie) (fun _ _ ha hb => GaugeGroup.add_mem_lie hG ha hb)
        G.zero_mem_lie fun i _ => ?_
      have hp := hpsi (Y i) Z (hY i) hZ (by linarith [hYM i]) (by linarith)
      have e : Y i + Phi (Y i) (-Z) = psi (Y i) (-Z) + Z := by unfold Phi; abel
      rw [e]
      exact GaugeGroup.add_mem_lie hG hp hZ
    have e : ((n : ℂ)⁻¹) = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    unfold T
    rw [e]
    exact G.smul_mem_lie hsum _
  obtain ⟨Z, hZC, hZ, hfix⟩ := fixed_exists hn Y M hYM hM G.lie (GaugeGroup.isClosed_lie hG)
    G.zero_mem_lie hTC
  refine ⟨Z, hZC, hZ, (sum_psi_eq_zero_iff hn Y Z).2 hfix, fun W₁ hW₁ => ?_⟩
  exact G.carrier.mul_mem (by simpa using hZC.2 1) hW₁

end GroupMean
end CoreLean

end
