/-
The chart of `def:chart` on `GL(N)` and the parts of `lem:average` of BALABAN_CORE.tex (`39c88d556af9`)
which rest on `lem:chart`.

* `inChart`, `chartLog`: the chart domain `N_G = {e^{iA} | A ∈ 𝔤, ‖A‖ < π}` and the chart `log e^{iA} = iA`,
  well defined by `chart_well_defined` (`lem:chart`(i)); `chartLog_eq`, `chartLog_spec`.
* `logInput`: the named input `Average.LogInput` of `AverageAlgebra.lean` holds for the chart, by
  `chart_domain` (`lem:chart`(i)): `N_G` is invariant under inversion and conjugation by `G`, with
  `log W⁻¹ = -log W` and `log(uWu⁻¹) = Ad_u log W`. So `avg_covariant_chart` (`lem:average`(iii)) and
  `avg_reverse_chart` (`lem:average`(i)) hold for the average of the core without a named input.
* `beta_mem_lie`, `avg_mem`: the last clause of `lem:average`(i): `β_c(U) ∈ 𝔤`, a combination of elements
  of `𝔤` with positive real weights, and `M(U)(c) ∈ G`.
* `norm_prod_sub_one_le`, `norm_inv_sub_one`: for unitary `W_l`, `‖W_1 ⋯ W_m - 1‖ ≤ Σ_l ‖W_l - 1‖` and
  `‖W⁻¹ - 1‖ = ‖W - 1‖` (the "first fact" of the proofs of `lem:average`(v) and `lem:axial-smallness`).
* `average_domain` (`lem:average`(v), the step from the loops to `β_c`): there is `r_G ∈ (0, 1)` such that
  if the holonomies of all loops of `c` lie in `G` within `ε ≤ r_G` of `1`, then `U ∈ 𝒪_c` and
  `‖β_c(U)‖ ≤ (π/2)ε` (`lem:chart`(ii) and (iii), the weights summing to at most one).
  `average_domain_constants`: with the geometric bound `‖U(ℓ) - 1‖ ≤ 4√N L²α` of the core's proof and
  `α ≤ α_M = r_G/(8√N L²)`, this is `‖U(ℓ) - 1‖ ≤ r_G/2` and `‖β_c(U)‖ ≤ C_Mα`, `C_M = 7√N L²`.
-/
import CoreLean.ChartLocal
import CoreLean.ChartBounds
import CoreLean.AverageAlgebra

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator Classical

noncomputable section

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Products of unitary matrices -/

/-- `‖W⁻¹ - 1‖ = ‖W - 1‖` for a unitary `W`. -/
lemma norm_inv_sub_one {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ‖((W⁻¹ : GLN) : Mat) - 1‖ = ‖(W : Mat) - 1‖ := by
  have e : ((W⁻¹ : GLN) : Mat) - 1 = -(((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  have hWi : ((W⁻¹ : GLN) : Mat) = star (W : Mat) := by
    have h := (Matrix.mem_unitaryGroup_iff).1 hW
    calc ((W⁻¹ : GLN) : Mat) = ((W⁻¹ : GLN) : Mat) * ((W : Mat) * star (W : Mat)) := by
          rw [h, mul_one]
      _ = star (W : Mat) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [e, norm_neg, hWi]
  exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hW)

/-- `‖W_1 ⋯ W_m - 1‖ ≤ Σ_l ‖W_l - 1‖` for unitary matrices `W_l`. -/
lemma norm_prod_sub_one_le (l : List Mat) (hl : ∀ W ∈ l, W ∈ unitaryGroup (Fin N) ℂ) :
    ‖l.prod - 1‖ ≤ (l.map fun W => ‖W - 1‖).sum := by
  induction l with
  | nil => simp
  | cons W l ih =>
    have hW := hl W (by simp)
    have hl' : ∀ V ∈ l, V ∈ unitaryGroup (Fin N) ℂ := fun V hV => hl V (by simp [hV])
    have e : (W :: l).prod - 1 = W * (l.prod - 1) + (W - 1) := by
      simp only [List.prod_cons]; noncomm_ring
    rw [e, List.map_cons, List.sum_cons]
    have h1 : ‖W * (l.prod - 1)‖ = ‖l.prod - 1‖ := CStarRing.norm_mem_unitary_mul _ hW
    calc ‖W * (l.prod - 1) + (W - 1)‖ ≤ ‖W * (l.prod - 1)‖ + ‖W - 1‖ := norm_add_le _ _
      _ ≤ (l.map fun W => ‖W - 1‖).sum + ‖W - 1‖ := by rw [h1]; linarith [ih hl']
      _ = ‖W - 1‖ + (l.map fun W => ‖W - 1‖).sum := add_comm _ _

namespace GaugeGroup

variable (G : GaugeGroup N)

/-- The chart domain `N_G = {e^{iA} | A ∈ 𝔤, ‖A‖ < π}` (`def:chart`), as a predicate on `GL(N)`. -/
def inChart (W : GLN) : Prop := ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧ (W : Mat) = exp (Complex.I • A)

/-- The chart `log e^{iA} = iA` on `N_G` (`def:chart`); `0` off `N_G`. -/
def chartLog (W : GLN) : Mat := if h : G.inChart W then Complex.I • h.choose else 0

variable {G}

lemma chartLog_eq {W : GLN} {A : Mat} (hA : A ∈ G.lie) (hn : ‖A‖ < Real.pi)
    (hW : (W : Mat) = exp (Complex.I • A)) : G.inChart W ∧ G.chartLog W = Complex.I • A := by
  have hin : G.inChart W := ⟨A, hA, hn, hW⟩
  refine ⟨hin, ?_⟩
  rw [chartLog, dite_eq_left_of_eq_true (eq_true hin)]
  obtain ⟨h1, h2, h3⟩ := hin.choose_spec
  rw [ChartBounds.chart_well_defined h1 hA h2 hn (h3.symm.trans hW)]

lemma chartLog_spec {W : GLN} (h : G.inChart W) :
    ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧ (W : Mat) = exp (Complex.I • A) ∧ G.chartLog W = Complex.I • A := by
  obtain ⟨A, hA, hn, hW⟩ := h
  exact ⟨A, hA, hn, hW, (chartLog_eq hA hn hW).2⟩

/-- The chart satisfies the named input of `AverageAlgebra.lean` (`lem:chart`(i)). -/
theorem logInput : Average.LogInput G.carrier G.inChart G.chartLog where
  conj g hg W hW := by
    obtain ⟨A, hA, hn, hWA⟩ := hW
    obtain ⟨-, ⟨hAd, hAdn, hAde⟩⟩ := ChartBounds.chart_domain hg hA hn
    have hval : ((g * W * g⁻¹ : GLN) : Mat) = exp (Complex.I • Ad g A) := by
      rw [hAde, Units.val_mul, Units.val_mul, hWA]
    obtain ⟨hin, hlog⟩ := chartLog_eq hAd hAdn hval
    refine ⟨hin, ?_⟩
    rw [hlog, (chartLog_eq hA hn hWA).2, Ad_smul]
  inv W hW := by
    obtain ⟨A, hA, hn, hWA⟩ := hW
    obtain ⟨⟨hAn, hAnn, hAne⟩, -⟩ := ChartBounds.chart_domain G.carrier.one_mem hA hn
    have hval : ((W⁻¹ : GLN) : Mat) = exp (Complex.I • -A) := by
      calc ((W⁻¹ : GLN) : Mat) = (exp (Complex.I • -A) * (W : Mat)) * ((W⁻¹ : GLN) : Mat) := by
            rw [hWA, hAne, one_mul]
        _ = exp (Complex.I • -A) := by rw [mul_assoc, Units.mul_inv, mul_one]
    obtain ⟨hin, hlog⟩ := chartLog_eq hAn hAnn hval
    refine ⟨hin, ?_⟩
    rw [hlog, (chartLog_eq hA hn hWA).2, smul_neg]

variable {ι : Type*} [Fintype ι] {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)]

/-- `lem:average`(iii) for the chart: `M(U^u)(c) = u(c₋)M(U)(c)u(c₊)⁻¹` for `u(c₋) ∈ G`. -/
theorem avg_covariant_chart (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN) (k : GLN)
    (um up : GLN) (hum : um ∈ G.carrier) (ux ux' : ι → GLN) :
    Average.avg G.inChart G.chartLog (fun x Γ => um * g x Γ * (ux x)⁻¹)
        (fun x => ux x * h x * (ux' x)⁻¹) (fun x Γ' => up * g' x Γ' * (ux' x)⁻¹) (um * k * up⁻¹) =
      um * Average.avg G.inChart G.chartLog g h g' k * up⁻¹ :=
  Average.avg_covariant logInput g h g' k um up hum ux ux'

/-- `lem:average`(i) for the chart: `M(U)(c⁻¹) = M(U)(c)⁻¹` when `U([c]) ∈ G`. -/
theorem avg_reverse_chart (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN) (k : GLN)
    (hk : k ∈ G.carrier) :
    Average.avg G.inChart G.chartLog g' (fun x => (h x)⁻¹) g k⁻¹ =
      (Average.avg G.inChart G.chartLog g h g' k)⁻¹ :=
  Average.avg_reverse logInput g h g' k hk

lemma sum_mem_lie (hG : IsClosed G.mats) {α : Type*} (s : Finset α) (f : α → Mat)
    (hf : ∀ a ∈ s, f a ∈ G.lie) : ∑ a ∈ s, f a ∈ G.lie :=
  Finset.sum_induction f (· ∈ G.lie) (fun _ _ ha hb => add_mem_lie hG ha hb) G.zero_mem_lie hf

lemma wt_eq (x : ι) : Average.wt P P' x =
    (((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹ : ℝ) := by
  simp only [Average.wt]; push_cast; ring

/-- The term of `β_c` of a loop in the chart domain. -/
lemma beta_term {W : GLN} (hW : G.inChart W) (w : ℝ) :
    ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧ (W : Mat) = exp (Complex.I • A) ∧
      ((w : ℂ) • ((1 / Complex.I : ℂ) • G.chartLog W)) = (w : ℂ) • A := by
  obtain ⟨A, hA, hn, hWA, hlog⟩ := chartLog_spec hW
  refine ⟨A, hA, hn, hWA, ?_⟩
  rw [hlog, smul_smul, smul_smul, one_div, mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, mul_one]

/-- `lem:average`(i), the last clause: `β_c(U) ∈ 𝔤` when all loops lie in `N_G`. -/
theorem beta_mem_lie (hG : IsClosed G.mats) (g : ∀ x, P x → GLN) (h : ι → GLN)
    (g' : ∀ x, P' x → GLN) (k : GLN)
    (hN : ∀ x Γ Γ', G.inChart (Average.loop g h g' k x Γ Γ')) :
    Average.beta G.chartLog g h g' k ∈ G.lie := by
  refine sum_mem_lie hG _ _ fun x _ => sum_mem_lie hG _ _ fun Γ _ => sum_mem_lie hG _ _ fun Γ' _ => ?_
  obtain ⟨A, hA, -, -, he⟩ := beta_term (hN x Γ Γ') (((Fintype.card ι : ℝ) * Fintype.card (P x) *
    Fintype.card (P' x))⁻¹)
  rw [wt_eq, he]
  exact G.smul_mem_lie hA _

/-- `lem:average`(i): `M(U)(c) ∈ G` when `U([c]) ∈ G`. -/
theorem avg_mem (hG : IsClosed G.mats) (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN)
    (k : GLN) (hk : k ∈ G.carrier) : Average.avg G.inChart G.chartLog g h g' k ∈ G.carrier := by
  unfold Average.avg
  split_ifs with hN
  · refine G.carrier.mul_mem ?_ hk
    have := (beta_mem_lie hG g h g' k hN).2 1
    simpa using this
  · exact hk

/-- `lem:average`(v), the step from the loops to `β_c`: there is `r_G ∈ (0, 1)` such that if the
holonomies of all loops lie in `G` within `ε ≤ r_G` of `1`, then they lie in `N_G` and
`‖β_c(U)‖ ≤ (π/2)ε`. -/
theorem average_domain (hG : IsClosed G.mats) :
    ∃ rG : ℝ, 0 < rG ∧ rG < 1 ∧ ∀ (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN)
      (k : GLN) (ε : ℝ), 0 ≤ ε → ε ≤ rG →
      (∀ x Γ Γ', Average.loop g h g' k x Γ Γ' ∈ G.carrier) →
      (∀ x Γ Γ', ‖((Average.loop g h g' k x Γ Γ' : GLN) : Mat) - 1‖ ≤ ε) →
      (∀ x Γ Γ', G.inChart (Average.loop g h g' k x Γ Γ')) ∧
        ‖Average.beta G.chartLog g h g' k‖ ≤ Real.pi / 2 * ε := by
  obtain ⟨rG, hr0, hr1, hchart⟩ := chart_ii hG
  refine ⟨rG, hr0, hr1, fun g h g' k ε hε0 hε hG' hle => ?_⟩
  have hin : ∀ x Γ Γ', G.inChart (Average.loop g h g' k x Γ Γ') := fun x Γ Γ' => by
    obtain ⟨A, hA, hn, he, -, -⟩ := hchart _ (hG' x Γ Γ') ((hle x Γ Γ').trans hε)
    exact ⟨A, hA, hn, he.symm⟩
  refine ⟨hin, ?_⟩
  have hc : 0 ≤ Real.pi / 2 * ε := by positivity
  -- each term is at most `w_x (π/2)ε`, by `lem:chart`(iii)
  have hterm : ∀ x Γ Γ', ‖Average.wt P P' x • ((1 / Complex.I : ℂ) •
      G.chartLog (Average.loop g h g' k x Γ Γ'))‖ ≤
      ((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹ * (Real.pi / 2 * ε) :=
    fun x Γ Γ' => by
    set w : ℝ := ((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹
    obtain ⟨A, hA, hn, hWA, he⟩ := beta_term (hin x Γ Γ') w
    have hw : 0 ≤ w := by positivity
    rw [wt_eq, he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    have hb := (ChartBounds.chart_iii hA.1 hn.le).2.1
    rw [← hWA] at hb
    exact mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_left (hle x Γ Γ') (by positivity))) hw
  have hs : ‖Average.beta G.chartLog g h g' k‖ ≤ ∑ x, ∑ _Γ : P x, ∑ _Γ' : P' x,
      ((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹ * (Real.pi / 2 * ε) := by
    unfold Average.beta
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Γ _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun Γ' _ => hterm x Γ Γ')
  refine hs.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the weights sum to at most one
  have key : ∀ x : ι, (Fintype.card (P x) : ℝ) * ((Fintype.card (P' x) : ℝ) *
      (((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹ * (Real.pi / 2 * ε))) ≤
      (Fintype.card ι : ℝ)⁻¹ * (Real.pi / 2 * ε) := fun x => by
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
    rcases (Nat.cast_nonneg (Fintype.card (P x)) : (0 : ℝ) ≤ _).eq_or_lt with hp | hp
    · rw [← hp]; simp only [zero_mul]; positivity
    rcases (Nat.cast_nonneg (Fintype.card (P' x)) : (0 : ℝ) ≤ _).eq_or_lt with hq | hq
    · rw [← hq]; simp only [zero_mul, mul_zero]; positivity
    have := hp.ne'; have := hq.ne'; have := hn.ne'
    apply le_of_eq; field_simp
  calc _ ≤ ∑ _x : ι, (Fintype.card ι : ℝ)⁻¹ * (Real.pi / 2 * ε) := Finset.sum_le_sum fun x _ => key x
    _ ≤ Real.pi / 2 * ε := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rcases (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _).eq_or_lt with h0 | h0
      · rw [← h0]; simp only [zero_mul]; positivity
      · rw [← mul_assoc, mul_inv_cancel₀ h0.ne', one_mul]

/-- `lem:average`(v) with the core's constants: if `‖U(ℓ) - 1‖ ≤ 4√N L²α` for the loops (the geometric
bound of the core's proof, by at most `4L²` moves across plaquettes) and `0 ≤ α ≤ α_M = r_G/(8√N L²)`,
then `U ∈ 𝒪_c`, `‖U(ℓ) - 1‖ ≤ r_G/2`, and `‖β_c(U)‖ ≤ C_Mα` with `C_M = 7√N L²`. -/
theorem average_domain_constants (hG : IsClosed G.mats) :
    ∃ rG : ℝ, 0 < rG ∧ rG < 1 ∧ ∀ (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN)
      (k : GLN) (L α : ℝ), 0 ≤ α → α ≤ rG / (8 * Real.sqrt N * L ^ 2) →
      (∀ x Γ Γ', Average.loop g h g' k x Γ Γ' ∈ G.carrier) →
      (∀ x Γ Γ', ‖((Average.loop g h g' k x Γ Γ' : GLN) : Mat) - 1‖ ≤ 4 * Real.sqrt N * L ^ 2 * α) →
      (∀ x Γ Γ', G.inChart (Average.loop g h g' k x Γ Γ')) ∧
        (∀ x Γ Γ', ‖((Average.loop g h g' k x Γ Γ' : GLN) : Mat) - 1‖ ≤ rG / 2) ∧
        ‖Average.beta G.chartLog g h g' k‖ ≤ 7 * Real.sqrt N * L ^ 2 * α := by
  obtain ⟨rG, hr0, hr1, hdom⟩ := average_domain (P := P) (P' := P') hG
  refine ⟨rG, hr0, hr1, fun g h g' k L α hα0 hα hG' hle => ?_⟩
  set s := Real.sqrt N * L ^ 2
  have hs0 : 0 ≤ s := by positivity
  have hε : 4 * Real.sqrt N * L ^ 2 * α ≤ rG / 2 := by
    rcases hs0.eq_or_lt with h0 | h0
    · have : 4 * Real.sqrt N * L ^ 2 * α = 4 * s * α := by ring
      rw [this, ← h0]; linarith
    · have h8 : rG / (8 * Real.sqrt N * L ^ 2) = rG / (8 * s) := by
        rw [show 8 * Real.sqrt N * L ^ 2 = 8 * s by simp only [s]; ring]
      rw [h8, le_div_iff₀ (by positivity)] at hα
      nlinarith
  have hle' : ∀ x Γ Γ', ‖((Average.loop g h g' k x Γ Γ' : GLN) : Mat) - 1‖ ≤ rG / 2 :=
    fun x Γ Γ' => (hle x Γ Γ').trans hε
  obtain ⟨hin, hb⟩ := hdom g h g' k (4 * Real.sqrt N * L ^ 2 * α) (by positivity)
    (hε.trans (by linarith)) hG' hle
  refine ⟨hin, hle', hb.trans ?_⟩
  have hpi := Real.pi_lt_d2
  have : 0 ≤ Real.sqrt N * L ^ 2 * α := by positivity
  nlinarith

end GaugeGroup

end CoreLean

end
