import CoreLean.WilsonLoop.Statement

/-!
# Negative control: the existential bound without nonvanishing

`CoreLean.WilsonLoop.BoundOnly G` is `CoreLean.WilsonLoop.ExistentialBoundAndLimit G`
with the nonvanishing clause and the data `ḡ₁`, `ℓ` which only that clause uses, removed.

## Main statements

* `CoreLean.WilsonLoop.ExistentialBoundAndLimit.boundOnly` gives the implication to `BoundOnly G`.
* `CoreLean.WilsonLoop.boundOnly_trivial`: `BoundOnly G` holds for every gauge group `G` with
  `G.carrier` compact, with no other hypothesis.  The proof uses nothing of the lattice theory
  but `|𝔼_K[W_𝒞]| ≤ 1`: the perimeter coefficients are chosen so that the normalisation of a loop
  of `P` bonds is `e^{P K}`, which gives `|W_K(𝒞)| ≤ e^{-K}`.

The lower bound in the existential statement rules out this example.

## Auxiliary statements

* `CoreLean.WilsonLoop.Irrep.norm_character_le_one`,
  `CoreLean.WilsonLoop.Ensemble.norm_observable_le_one`, `CoreLean.WilsonLoop.norm_expect_le_one`:
  a normalised character, the observable of an ensemble, and the expectation of a function
  bounded by `1` are bounded by `1`.
* `CoreLean.WilsonLoop.growingCoefficients`, `CoreLean.WilsonLoop.logKappa_growingCoefficients`,
  `CoreLean.WilsonLoop.norm_renormExpect_growing_le`: the growing normalisation and the bound
  `|W_K(𝒞)| ≤ e^{-K}`.
* `CoreLean.WilsonLoop.trivialConstants`: the constants used in the proof.
-/

noncomputable section

namespace CoreLean

namespace WilsonLoop

open MeasureTheory

variable {N : ℕ}

/-- `ExistentialBoundAndLimit` without the Nonvanishing clause. -/
def BoundOnly (G : GaugeGroup N) [CompactSpace G.carrier] : Prop :=
  ∃ L₀ : ℝ → ℕ, ∀ (Λstar : ℝ) (L : ℕ) [NeZero L], 2 ≤ Λstar → Odd L → L₀ Λstar ≤ L →
  ∃ c : Constants,
  ∀ mT : ℕ,
  ∀ gbar : ℝ, 0 < gbar → gbar ≤ c.γ₀ →
  ∃ (g₀ : ℕ → ℝ) (κ : Coefficients G), c.InWindow gbar g₀ ∧
  ∀ q : ℕ, 1 ≤ mT + q →
  ∃ (K₀ : EnsembleData G → ℕ) (B : EnsembleData G → ℝ),
  ∀ E : Ensemble (2 * L ^ (mT + q)) G, E.Admissible Λstar →
    c.qsharp E.repConst gbar ≤ q →
      q ≤ K₀ E.data ∧ MainBound (renormExpect L mT q g₀ κ E) (K₀ E.data) (B E.data)

/-- `BoundOnly` is a consequence of `ExistentialBoundAndLimit`: it is the same statement with the
Nonvanishing clause dropped. -/
theorem ExistentialBoundAndLimit.boundOnly {G : GaugeGroup N} [CompactSpace G.carrier]
    (h : ExistentialBoundAndLimit G) : BoundOnly G := by
  obtain ⟨L₀, h⟩ := h
  refine ⟨L₀, ?_⟩
  intro Λstar L _ hΛ hL hL₀
  obtain ⟨c, h⟩ := h Λstar L hΛ hL hL₀
  refine ⟨c, fun mT gbar hg hg' ↦ ?_⟩
  obtain ⟨_, h⟩ := h mT
  obtain ⟨g₀, κ, hw, h⟩ := h gbar hg hg'
  refine ⟨g₀, κ, hw, fun q hq ↦ ?_⟩
  obtain ⟨K₀, B, h⟩ := h q hq
  exact ⟨K₀, B, fun E hE ↦ (h E hE).1⟩

/-! ### The expectation of a bounded observable is bounded -/

/-- A normalised character is bounded by `1`. -/
theorem Irrep.norm_character_le_one {G : GaugeGroup N} (π : Irrep G) (g : G.carrier) :
    ‖π.character g‖ ≤ 1 := by
  have hd : (0 : ℝ) < π.dim := by exact_mod_cast π.dim_pos
  have htr : ‖(π.toHom g : Matrix (Fin π.dim) (Fin π.dim) ℂ).trace‖ ≤ π.dim := by
    calc ‖(π.toHom g : Matrix (Fin π.dim) (Fin π.dim) ℂ).trace‖
        ≤ ∑ i : Fin π.dim, ‖(π.toHom g : Matrix (Fin π.dim) (Fin π.dim) ℂ) i i‖ := by
          rw [Matrix.trace]; exact norm_sum_le _ _
      _ ≤ ∑ _i : Fin π.dim, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ entry_norm_bound_of_unitary (π.toHom g).2 i i
      _ = π.dim := by simp
  rw [Irrep.character, ntr, norm_mul, norm_inv, Complex.norm_natCast]
  exact (inv_mul_le_one₀ hd).2 htr

/-- A product of complex numbers bounded by `1` is bounded by `1`. -/
theorem norm_list_prod_le_one : ∀ l : List ℂ, (∀ z ∈ l, ‖z‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | z :: l, h => by
      rw [List.prod_cons, norm_mul]
      calc ‖z‖ * ‖l.prod‖ ≤ 1 * 1 :=
            mul_le_mul (h z (by simp)) (norm_list_prod_le_one l fun w hw ↦ h w (by simp [hw]))
              (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- The observable of an ensemble is bounded by `1`. -/
theorem Ensemble.norm_observable_le_one {G : GaugeGroup N} {n : ℕ} (E : Ensemble n G) (r : ℕ)
    (V : GField G (r * n)) : ‖E.observable r V‖ ≤ 1 := by
  refine norm_list_prod_le_one _ fun z hz ↦ ?_
  rw [List.mem_map] at hz
  obtain ⟨p, -, rfl⟩ := hz
  exact p.2.norm_character_le_one _

/-- The expectation of a function bounded by `1` is bounded by `1`. -/
theorem norm_expect_le_one (G : GaugeGroup N) [CompactSpace G.carrier] {n : ℕ} [NeZero n]
    (β : ℝ) (f : GField G n → ℂ) (hf : ∀ V, ‖f V‖ ≤ 1) : ‖expect G n β f‖ ≤ 1 := by
  unfold expect
  by_cases hI0 : (∫ V, Real.exp (-β * (action V.toConfig).re) ∂(haarField G n)) = 0
  · rw [hI0]; simp
  · have hint : Integrable (fun V : GField G n ↦ Real.exp (-β * (action V.toConfig).re))
        (haarField G n) := by
      by_contra h
      exact hI0 (integral_undef h)
    have hIpos : 0 < ∫ V, Real.exp (-β * (action V.toConfig).re) ∂(haarField G n) :=
      lt_of_le_of_ne (integral_nonneg fun V ↦ (Real.exp_pos _).le) (Ne.symm hI0)
    have hnum :
        ‖∫ V, (Real.exp (-β * (action V.toConfig).re) : ℂ) * f V ∂(haarField G n)‖ ≤
          ∫ V, Real.exp (-β * (action V.toConfig).re) ∂(haarField G n) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun V ↦ norm_nonneg _) hint
        (Filter.Eventually.of_forall fun V ↦ ?_)
      beta_reduce
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (hf V)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hIpos.le]
    exact (div_le_one hIpos).2 hnum

/-! ### A normalisation which grows -/

/-- Coefficients for which the normalisation of a loop of `P` bonds is `e^{P K}`: each bond of
the lattice `𝕋_K` contributes `K / L^{K-q}`, each corner nothing. -/
def growingCoefficients (G : GaugeGroup N) (L : ℕ) : Coefficients G where
  m K q _ _ := (K : ℂ) / (L : ℂ) ^ (K - q)
  z _ _ _ _ _ := 0

/-- With the growing coefficients, `log κ_K^{(q)}(C, χ) = P(C) K`. -/
theorem logKappa_growingCoefficients {G : GaugeGroup N} (L K q : ℕ) [NeZero L] {n : ℕ}
    (C : Loop n) (π : Irrep G) :
    (growingCoefficients G L).logKappa L K q C π = (C.perimeter : ℂ) * K := by
  have hL : ((L : ℂ)) ^ (K - q) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  simp [Coefficients.logKappa, growingCoefficients, Loop.orients, Loop.perimeter,
    mul_div_cancel₀ _ hL, Function.comp_def]

/-- A product of a nonempty list of real numbers which are at least `a ≥ 1` is at least `a`. -/
theorem le_list_prod {a : ℝ} (ha : 1 ≤ a) :
    ∀ l : List ℝ, l ≠ [] → (∀ x ∈ l, a ≤ x) → a ≤ l.prod
  | [], h, _ => absurd rfl h
  | [x], _, h => by simpa using h x (by simp)
  | x :: y :: l, _, h => by
      rw [List.prod_cons]
      have h1 : a ≤ x := h x (by simp)
      have h2 : a ≤ (y :: l).prod :=
        le_list_prod ha (y :: l) (by simp) fun w hw ↦ h w (by simp [hw])
      nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith)]

/-- With the growing normalisation, `|W_K(𝒞)| ≤ e^{-K}` for every ensemble. -/
theorem norm_renormExpect_growing_le (G : GaugeGroup N) [CompactSpace G.carrier] (L mT q : ℕ)
    [NeZero L] (g₀ : ℕ → ℝ) (E : Ensemble (2 * L ^ (mT + q)) G) (K : ℕ) :
    ‖renormExpect L mT q g₀ (growingCoefficients G L) E K‖ ≤ Real.exp (-(K : ℝ)) := by
  have hK : (1 : ℝ) ≤ Real.exp K := Real.one_le_exp (Nat.cast_nonneg K)
  have hden : Real.exp K ≤
      ‖(E.loops.map fun p ↦ (growingCoefficients G L).kappa L K q p.1 p.2).prod‖ := by
    rw [List.norm_prod, List.map_map]
    refine le_list_prod hK _ (by simpa using E.ne_nil) fun x hx ↦ ?_
    rw [List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    simp only [Function.comp_apply, Coefficients.kappa, Complex.norm_exp,
      logKappa_growingCoefficients]
    have hre : ((p.1.perimeter : ℂ) * (K : ℂ)).re = (p.1.perimeter : ℝ) * K := by simp
    have h3 : (3 : ℝ) ≤ p.1.perimeter := by exact_mod_cast p.1.three_le
    rw [hre]
    exact Real.exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have hnum := norm_expect_le_one G (n := L ^ (K - q) * (2 * L ^ (mT + q)))
    ((g₀ K) ^ (-2 : ℤ)) (E.observable (L ^ (K - q))) fun V ↦ E.norm_observable_le_one _ V
  unfold renormExpect
  rw [norm_div]
  calc _ ≤ 1 / Real.exp K := div_le_div₀ zero_le_one hnum (Real.exp_pos _) hden
    _ = Real.exp (-(K : ℝ)) := by rw [Real.exp_neg, one_div]

/-- Constants for which every condition on the constants holds trivially: `γ₀ = b = b' = 1`,
`C_W = 0`, and `q_♯ = 0`. -/
def trivialConstants : Constants where
  γ₀ := 1
  b := 1
  b' := 1
  CW := 0
  qsharp _ _ := 0
  γ₀_pos := one_pos
  b_pos := one_pos
  b_le := le_rfl
  CW_nonneg := le_rfl
  qsharp_mono_left _ _ _ _ _ _ _ := le_rfl
  qsharp_mono_right _ _ _ _ _ _ _ := le_rfl
  qsharp_eq_zero _ _ := ⟨1, one_pos, fun _ _ _ ↦ rfl⟩

/-- **The statement without the Nonvanishing clause holds trivially.** -/
theorem boundOnly_trivial (G : GaugeGroup N) [CompactSpace G.carrier] : BoundOnly G := by
  refine ⟨fun _ ↦ 0, ?_⟩
  intro Λstar L _ _ _ _
  refine ⟨trivialConstants, fun mT gbar hg _ ↦ ?_⟩
  refine ⟨fun K ↦ (Real.sqrt (gbar ^ (-2 : ℤ) + K))⁻¹, growingCoefficients G L, ?_, ?_⟩
  · intro K
    have hx : 0 < gbar ^ (-2 : ℤ) + (K : ℝ) := by positivity
    have e : ((Real.sqrt (gbar ^ (-2 : ℤ) + K))⁻¹) ^ (-2 : ℤ) = gbar ^ (-2 : ℤ) + K := by
      rw [inv_zpow', neg_neg]
      exact_mod_cast Real.sq_sqrt hx.le
    refine ⟨by positivity, ?_, ?_⟩ <;> rw [e] <;> simp [trivialConstants]
  · intro q _
    refine ⟨fun _ ↦ q, fun _ ↦ 1, fun E _ _ ↦ ⟨le_rfl, fun K _ ↦ ?_, ?_⟩⟩
    · exact (norm_renormExpect_growing_le G L mT q _ E K).trans (Real.exp_le_one_iff.2 (by simp))
    · refine Summable.of_nonneg_of_le (fun K ↦ norm_nonneg _) (fun K ↦ ?_)
        (Real.summable_exp_neg_nat.mul_left 2)
      have h1 := norm_renormExpect_growing_le G L mT q
        (fun K ↦ (Real.sqrt (gbar ^ (-2 : ℤ) + K))⁻¹) E (q + K + 1)
      have h2 := norm_renormExpect_growing_le G L mT q
        (fun K ↦ (Real.sqrt (gbar ^ (-2 : ℤ) + K))⁻¹) E (q + K)
      have e1 : Real.exp (-((q + K + 1 : ℕ) : ℝ)) ≤ Real.exp (-(K : ℝ)) :=
        Real.exp_le_exp.2 (by push_cast; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
      have e2 : Real.exp (-((q + K : ℕ) : ℝ)) ≤ Real.exp (-(K : ℝ)) :=
        Real.exp_le_exp.2 (by push_cast; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
      calc _ ≤ _ + _ := norm_sub_le _ _
        _ ≤ 2 * Real.exp (-(K : ℝ)) := by linarith

end WilsonLoop

end CoreLean
