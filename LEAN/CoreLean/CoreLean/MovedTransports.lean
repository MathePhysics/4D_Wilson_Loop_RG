/-
`lem:moved-transports`(i) and `lem:gauged-bound` of BALABAN_CORE.tex (`39c88d556af9`), in abstract form.

* `norm_sub_le_of_bounded`: a map `f` holomorphic on the ball of radius `ρ` of a complex normed space and
  bounded by `2ρ` there satisfies `‖f(X') - f(X)‖ ≤ 16‖X' - X‖` for `‖X‖, ‖X'‖ ≤ ρ/2`. This is the core's
  proof of `lem:moved-transports`(i): if `d = ‖X' - X‖ > ρ/4` the difference is at most `4ρ < 16d`;
  otherwise `φ(z) = f(X + z(X' - X))` is holomorphic for `|z| < r = ρ/(2d)`, `r ≥ 2`, bounded by `2ρ`, and
  Cauchy's estimate (here on discs of radius `(r - 1)/2` about the points of the unit disc) bounds `φ'`
  by `16d` there; the mean value inequality ends the proof.
* `moved_transports_i` (`lem:moved-transports`(i)): the statement on the polydisc `‖X_i‖ < ϱ_G`, with the
  sup norm of `Fin n → M_N(ℂ)`; holomorphy and the bound `‖Y‖ ≤ 2ϱ_G` of
  `Y(X) = (1/i) Log 𝗆({e^{iX_i}})` are the inputs from `lem:group-mean`.
* `norm_prod_exp_sub_one_le`: `‖e^{Z_1} ⋯ e^{Z_m} - 1‖ ≤ e^{Σ‖Z_k‖} - 1` in a Banach algebra.
* `gauged_bound` (`lem:gauged-bound`, `eq:gauged-bound`): along a chain, `h(x_n) = h(x_{n+1})
  v^{(n+1)}(x_{n+1})⁻¹ t_n(x_n)`, `h(y) = 1`, with exponents bounded by `τ_m = 2^{12}L^{1+m-j}a_j‖A‖`
  (the inputs from `lem:moved-transports`(ii), (iii), `prop:regular-averages`, `prop:relative-average-order`),
  and `g(x_n) = h(x_n)v_n(x_n)⁻¹` with `‖(1/i) Log v_n(x_n)‖ ≤ C'_2 a_n‖A‖`, `a_n ≤ a_j`; then
  `‖g(x_n) - 1‖ ≤ C_gm a_j‖A‖` with `C_gm = 2^{16} + 4C'_2`, for `2^{14}a_j‖A‖ ≤ 1` and `C'_2a_j‖A‖ ≤ 1/2`.
-/
import CoreLean.ChartLocal

open NormedSpace Metric Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

/-! ### The Lipschitz bound from Cauchy's estimate -/

section Cauchy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A map holomorphic on the ball of radius `ρ` and bounded by `2ρ` there is `16`-Lipschitz on the ball of
radius `ρ/2`. -/
theorem norm_sub_le_of_bounded {f : E → F} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball 0 ρ)) (hb : ∀ z ∈ ball (0 : E) ρ, ‖f z‖ ≤ 2 * ρ) {X X' : E}
    (hX : ‖X‖ ≤ ρ / 2) (hX' : ‖X'‖ ≤ ρ / 2) : ‖f X' - f X‖ ≤ 16 * ‖X' - X‖ := by
  set d := ‖X' - X‖
  have hXb : X ∈ ball (0 : E) ρ := mem_ball_zero_iff.mpr (by linarith)
  have hX'b : X' ∈ ball (0 : E) ρ := mem_ball_zero_iff.mpr (by linarith)
  by_cases hd : ρ / 4 < d
  · calc ‖f X' - f X‖ ≤ ‖f X'‖ + ‖f X‖ := norm_sub_le _ _
      _ ≤ 2 * ρ + 2 * ρ := add_le_add (hb _ hX'b) (hb _ hXb)
      _ ≤ 16 * d := by linarith
  rw [not_lt] at hd
  rcases (norm_nonneg (X' - X)).eq_or_lt with hd0 | hd0
  · have : X' = X := sub_eq_zero.mp (norm_eq_zero.mp hd0.symm)
    have hd' : (0 : ℝ) ≤ d := norm_nonneg _
    rw [this, sub_self, norm_zero]
    linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  set δ := X' - X
  set φ : ℂ → F := fun z => f (X + z • δ)
  set r := ρ / (2 * d)
  have hr2 : 2 ≤ r := by
    rw [le_div_iff₀ (by positivity)]; linarith
  -- `X + zδ` lies in the ball for `|z| < r`
  have hline : ∀ z : ℂ, ‖z‖ < r → X + z • δ ∈ ball (0 : E) ρ := fun z hz => by
    rw [mem_ball_zero_iff]
    have hzd : ‖z‖ * d < ρ / 2 := by
      calc ‖z‖ * d < r * d := mul_lt_mul_of_pos_right hz hd0
        _ = ρ / 2 := by simp only [r]; field_simp
    calc ‖X + z • δ‖ ≤ ‖X‖ + ‖z‖ * d := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul]
      _ < ρ := by linarith
  have hdiff : ∀ z : ℂ, ‖z‖ < r → DifferentiableAt ℂ φ z := fun z hz =>
    (hf.differentiableAt (isOpen_ball.mem_nhds (hline z hz))).comp z
      ((differentiableAt_const X).add (differentiableAt_id.smul_const δ))
  -- Cauchy's estimate on discs of radius `R = (r - 1)/2` about the points of the unit disc
  set R := (r - 1) / 2
  have hR : 0 < R := by simp only [R]; linarith
  have hderiv : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv φ z‖ ≤ 16 * d := fun z hz => by
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hin : ∀ w ∈ closedBall z R, ‖w‖ < r := fun w hw => by
      have : ‖w - z‖ ≤ R := by simpa [dist_eq_norm] using hw
      have := norm_le_insert' w z
      simp only [R] at *; linarith
    have hdc : DiffContOnCl ℂ φ (ball z R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hR.ne']
      exact fun w hw => (hdiff w (hin w hw)).differentiableWithinAt
    have hsph : ∀ w ∈ sphere z R, ‖φ w‖ ≤ 2 * ρ := fun w hw =>
      hb _ (hline w (hin w (sphere_subset_closedBall hw)))
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc hsph
    refine hc.trans ?_
    -- `2ρ/R = 4ρ/(r - 1) ≤ 8ρ/r = 16d`
    have hr1 : r / 2 ≤ r - 1 := by linarith
    have hRr : r / 4 ≤ R := by simp only [R]; linarith
    calc 2 * ρ / R ≤ 2 * ρ / (r / 4) := by gcongr
      _ = 16 * d := by simp only [r]; field_simp; norm_num
  -- the mean value inequality on the unit disc
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hdiff z (by
      have : ‖z‖ ≤ 1 := by simpa using hz
      linarith)).hasDerivAt.hasDerivWithinAt) hderiv (convex_closedBall 0 1)
    (mem_closedBall_self zero_le_one) (by simp : (1 : ℂ) ∈ closedBall (0 : ℂ) 1)
  have e1 : φ 1 = f X' := by simp only [φ, one_smul, δ, add_sub_cancel]
  have e0 : φ 0 = f X := by simp only [φ, zero_smul, add_zero]
  rw [e1, e0, sub_zero, norm_one, mul_one] at hmv
  exact hmv

end Cauchy

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- `lem:moved-transports`(i): if `Y` is holomorphic on the polydisc `‖X_i‖ < ϱ` and bounded there by
`2ϱ` (`lem:group-mean`, for `Y(X) = (1/i) Log 𝗆({e^{iX_i}})`), then for `‖X_i‖, ‖X'_i‖ ≤ ϱ/2`,
`‖Y(X') - Y(X)‖ ≤ 16 max_i ‖X'_i - X_i‖`. -/
theorem moved_transports_i {n : ℕ} {Y : (Fin n → Mat) → Mat} {ϱ : ℝ} (hϱ : 0 < ϱ)
    (hY : DifferentiableOn ℂ Y (ball 0 ϱ)) (hYb : ∀ X ∈ ball (0 : Fin n → Mat) ϱ, ‖Y X‖ ≤ 2 * ϱ)
    {X X' : Fin n → Mat} (hX : ∀ i, ‖X i‖ ≤ ϱ / 2) (hX' : ∀ i, ‖X' i‖ ≤ ϱ / 2) {d : ℝ}
    (hd0 : 0 ≤ d) (hd : ∀ i, ‖X' i - X i‖ ≤ d) : ‖Y X' - Y X‖ ≤ 16 * d := by
  have h0 : 0 ≤ ϱ / 2 := by positivity
  have hXn : ‖X‖ ≤ ϱ / 2 := (pi_norm_le_iff_of_nonneg h0).2 hX
  have hX'n : ‖X'‖ ≤ ϱ / 2 := (pi_norm_le_iff_of_nonneg h0).2 hX'
  have hdn : ‖X' - X‖ ≤ d := (pi_norm_le_iff_of_nonneg hd0).2 fun i => by simpa using hd i
  exact (norm_sub_le_of_bounded hϱ hY hYb hXn hX'n).trans (by linarith)

/-! ### Products of exponentials and the transformation of a move -/

section Products

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- `‖e^{Z_1} ⋯ e^{Z_m} - 1‖ ≤ e^{Σ‖Z_k‖} - 1`. -/
lemma norm_prod_exp_sub_one_le (l : List 𝔸) :
    ‖(l.map exp).prod - 1‖ ≤ Real.exp (l.map fun Z => ‖Z‖).sum - 1 := by
  induction l with
  | nil => simp
  | cons Z l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set P := (l.map exp).prod
    set t := (l.map fun Z => ‖Z‖).sum
    have hs := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ Z
    have hs0 : 0 ≤ Real.exp ‖Z‖ - 1 := by linarith [Real.add_one_le_exp ‖Z‖, norm_nonneg Z]
    have e : exp Z * P - 1 = (exp Z - 1) * (P - 1) + (exp Z - 1) + (P - 1) := by noncomm_ring
    rw [e]
    calc ‖(exp Z - 1) * (P - 1) + (exp Z - 1) + (P - 1)‖
        ≤ ‖exp Z - 1‖ * ‖P - 1‖ + ‖exp Z - 1‖ + ‖P - 1‖ :=
          (norm_add₃_le).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ (Real.exp ‖Z‖ - 1) * (Real.exp t - 1) + (Real.exp ‖Z‖ - 1) + (Real.exp t - 1) := by
          gcongr
      _ = Real.exp (‖Z‖ + t) - 1 := by rw [Real.exp_add]; ring

end Products

/-- `Σ_{m<j} L^{1+m-j} ≤ 2` for `L ≥ 2`: the sum `S_j` satisfies `S_{j+1} = S_j/L + 1`. -/
lemma geom_L_sum (L : ℝ) (hL : 2 ≤ L) (j : ℕ) :
    ∑ m ∈ Finset.range j, L ^ (m + 1) / L ^ j ≤ 2 := by
  have hL0 : 0 < L := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, div_self (pow_ne_zero _ hL0.ne')]
    have e : ∑ m ∈ Finset.range j, L ^ (m + 1) / L ^ (j + 1) =
        (∑ m ∈ Finset.range j, L ^ (m + 1) / L ^ j) / L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun m _ => by rw [div_div, ← pow_succ]
    rw [e]
    have h2 : 2 / L ≤ 1 := (div_le_one hL0).2 hL
    have : (∑ m ∈ Finset.range j, L ^ (m + 1) / L ^ j) / L ≤ 2 / L := by gcongr
    linarith

local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `lem:gauged-bound` along one chain `x_n`, `n ≤ j`: with `h(x_j) = 1`,
`h(x_n) = h(x_{n+1}) e^{-iV_n} e^{iT_n}` (`v^{(n+1)}(x_{n+1}) = e^{iV_n}`, `t_n(x_n) = e^{iT_n}`),
`‖T_m‖, ‖V_m‖ ≤ 2^{12}L^{1+m-j}ε` with `ε = a_j‖A‖`, and `g(x_n) = h(x_n)e^{-iZ_n}` with `‖Z_n‖ ≤ C'_2ε`,
`‖g(x_n) - 1‖ ≤ (2^{16} + 4C'_2)ε` when `2^{14}ε ≤ 1` and `C'_2ε ≤ 1/2`. -/
theorem gauged_bound (L ε C2 : ℝ) (hL : 2 ≤ L) (hε : 0 ≤ ε) (hC2 : 0 ≤ C2)
    (hsmall : 2 ^ 14 * ε ≤ 1) (hsmall' : C2 * ε ≤ 1 / 2) (j : ℕ) (h T V Z : ℕ → Mat)
    (htop : h j = 1)
    (hrec : ∀ n, n < j → h n = h (n + 1) * exp (-(Complex.I • V n)) * exp (Complex.I • T n))
    (hT : ∀ m, m < j → ‖T m‖ ≤ 2 ^ 12 * (L ^ (m + 1) / L ^ j) * ε)
    (hV : ∀ m, m < j → ‖V m‖ ≤ 2 ^ 12 * (L ^ (m + 1) / L ^ j) * ε)
    (hZ : ∀ n, ‖Z n‖ ≤ C2 * ε) (n : ℕ) (hn : n ≤ j) :
    ‖h n * exp (-(Complex.I • Z n)) - 1‖ ≤ (2 ^ 16 + 4 * C2) * ε := by
  have h1 : ‖(1 : Mat)‖ ≤ 1 := norm_one_mat_le
  have hL0 : 0 < L := by linarith
  set τ : ℕ → ℝ := fun m => 2 ^ 12 * (L ^ (m + 1) / L ^ j) * ε
  -- `h(x_n)` is the product of the exponentials of the levels `n, …, j - 1`
  have hprod : ∀ k, k ≤ j → ∃ l : List Mat, h (j - k) = (l.map exp).prod ∧
      (l.map fun W => ‖W‖).sum ≤ 2 * ∑ m ∈ Finset.Ico (j - k) j, τ m := by
    intro k
    induction k with
    | zero => intro _; exact ⟨[], by simp [htop], by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨l, hl, hls⟩ := ih (by omega)
      have hjk : j - (k + 1) < j := by omega
      have hjk1 : j - (k + 1) + 1 = j - k := by omega
      refine ⟨l ++ [-(Complex.I • V (j - (k + 1))), Complex.I • T (j - (k + 1))], ?_, ?_⟩
      · rw [hrec _ hjk, hjk1, hl]; simp [mul_assoc]
      · have hI : ∀ W : Mat, ‖Complex.I • W‖ = ‖W‖ := fun W => norm_I_smul' W
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, norm_neg, hI, add_zero]
        rw [show Finset.Ico (j - (k + 1)) j = insert (j - (k + 1)) (Finset.Ico (j - k) j) by
          rw [← hjk1]; exact (Finset.insert_Ico_add_one_left_eq_Ico hjk).symm,
          Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
        have := hV _ hjk; have := hT _ hjk
        linarith
  obtain ⟨l, hl, hls⟩ := hprod (j - n) (by omega)
  rw [show j - (j - n) = n by omega] at hl hls
  -- `Σ_{m<j} τ_m ≤ 2^{13}ε`
  have hτ : ∑ m ∈ Finset.Ico n j, τ m ≤ 2 ^ 13 * ε := by
    have hsub : ∑ m ∈ Finset.Ico n j, τ m ≤ ∑ m ∈ Finset.range j, τ m :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
        simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega) (fun m _ _ => by positivity)
    have hg := geom_L_sum L hL j
    have e : ∑ m ∈ Finset.range j, τ m =
        2 ^ 12 * ε * ∑ m ∈ Finset.range j, L ^ (m + 1) / L ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by simp only [τ]; ring
    rw [e] at hsub
    nlinarith
  -- `‖h(x_n) - 1‖ ≤ e^{2^{14}ε} - 1 ≤ 2^{15}ε`
  have hh : ‖h n - 1‖ ≤ 2 ^ 15 * ε := by
    rw [hl]
    refine (norm_prod_exp_sub_one_le l).trans ?_
    have hx : (l.map fun W => ‖W‖).sum ≤ 2 ^ 14 * ε := by linarith
    have hx0 : 0 ≤ (l.map fun W => ‖W‖).sum :=
      List.sum_nonneg fun a ha => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.mp ha; exact norm_nonneg _
    have := Real.abs_exp_sub_one_le (x := (l.map fun W => ‖W‖).sum)
      (by rw [abs_of_nonneg hx0]; linarith)
    rw [abs_of_nonneg hx0] at this
    have := le_abs_self (Real.exp (l.map fun W => ‖W‖).sum - 1)
    linarith
  -- `g = h e^{-iZ}`
  set E := exp (-(Complex.I • Z n))
  have hZn : ‖-(Complex.I • Z n)‖ ≤ C2 * ε := by rw [norm_neg, norm_I_smul']; exact hZ n
  have hE1 : ‖E - 1‖ ≤ 2 * (C2 * ε) := by
    have := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (-(Complex.I • Z n))
    have h0 : 0 ≤ ‖-(Complex.I • Z n)‖ := norm_nonneg _
    have := exp_sub_one_le_two_mul h0 hZn (by linarith)
    linarith
  have hE : ‖E‖ ≤ 2 := by
    calc ‖E‖ = ‖(E - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖E - 1‖ + ‖(1 : Mat)‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have e : h n * E - 1 = (h n - 1) * E + (E - 1) := by noncomm_ring
  rw [e]
  calc ‖(h n - 1) * E + (E - 1)‖ ≤ ‖h n - 1‖ * ‖E‖ + ‖E - 1‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 2 ^ 15 * ε * 2 + 2 * (C2 * ε) := by gcongr
    _ ≤ (2 ^ 16 + 4 * C2) * ε := by nlinarith

end CoreLean

end
