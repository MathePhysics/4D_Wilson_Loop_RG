/-
**`lem:small-plaquettes`** of BALABAN_CORE.tex (`a021c13be348`), at one plaquette and one bond. A configuration
`𝐔 = e^{ia₀A''}U` (`move U A'' a₀`) with a `G`-valued gauge field `U`, a gauge transformation `v` with values in `G`
and a form `A` with `U^v = e^{ia₀A}` on the four bonds of `p = p_{μν}(x)`, and the bounds `eq:cube-setting` on the
bonds of `p` and at its corner (`a_j‖A‖ ≤ α`, `a_j²‖∇_{id}A‖ ≤ α`, `a_j‖A''‖ ≤ α₁`, `a_j²‖∇_UA''‖ ≤ α₁`,
`a₀ ≤ a_j`, `5120√N(α + α₁) ≤ 1`): `‖𝐔(∂p) - id‖ ≤ 10(α + α₁)(a₀/a_j)²` (`small_plaquette`); and for a bond with
`a₀‖A''(b)‖ ≤ α₁`, `‖Ad^{±1}_{𝐔(b)}X‖ ≤ e^{2α₁}‖X‖` (`small_Ad`). A configuration small on `□̃ⁿ` satisfies these
hypotheses at every plaquette of `□̃ⁿ`, so these are the two statements of the lemma. The proof is the core's:
`cor:moved-plaquette` for the trivial field and `A`, then for `U^v` and `Ad_vA''`, with the covariance of the
plaquettes and of the covariant differences under `v`.
-/
import CoreLean.MovedPlaquette

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace SmallPlaquettes

open LatticePaths LatticeKappa RegularAverages MovedPlaquette

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The trivial gauge field. -/
def triv : Config N n := fun _ _ => 1

/-- The form `Ad_vA''`, `(Ad_vA'')(b) = Ad_{v(b_-)}A''(b)`. -/
def AdForm (v : Site n → GLN) (A : Fin 4 → Site n → Mat) : Fin 4 → Site n → Mat := fun ρ z => Ad (v z) (A ρ z)

lemma unitary_of_mem (G : GaugeGroup N) {W : GLN} (hW : W ∈ G.carrier) :
    (W : Mat) ∈ unitaryGroup (Fin N) ℂ ∧ ((W⁻¹ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ :=
  ⟨G.unitary _ hW, G.unitary _ (G.carrier.inv_mem hW)⟩

lemma norm_Ad_unitary (G : GaugeGroup N) {W : GLN} (hW : W ∈ G.carrier) (X : Mat) : ‖Ad W X‖ = ‖X‖ := by
  unfold Ad
  exact opNorm_unitary_mul _ _ _ (unitary_of_mem G hW).1 (unitary_of_mem G hW).2

/-- The gauge transform of a moved field is the moved gauge transform: `(e^{ia₀A''}U)^v = e^{ia₀Ad_vA''}U^v`. -/
lemma gauge_move (U : Config N n) (A : Fin 4 → Site n → Mat) (η : ℝ) (v : Site n → GLN) :
    (move U A η).gauge v = move (U.gauge v) (AdForm v A) η := by
  funext ρ z
  simp only [Config.gauge, move, AdForm]
  rw [← Ad_smul, ← Ad_smul, ← expU_conj]
  group

/-- The covariance of the covariant differences: `D_{U^v}Ad_vA'' = Ad_vD_UA''`. -/
lemma Dcov_gauge (U : Config N n) (A : Fin 4 → Site n → Mat) (η : ℝ) (v : Site n → GLN) (μ ν : Fin 4)
    (x : Site n) : Dcov (U.gauge v) (AdForm v A) η μ ν x = Ad (v x) (Dcov U A η μ ν x) := by
  simp only [Dcov, AdForm, Config.gauge, Ad_smul, Ad_sub, ← Ad_mul]
  congr 3
  group

/-- The plaquette depends only on the values on its four bonds. -/
lemma plaq_congr (U V : Config N n) (μ ν : Fin 4) (x : Site n) (h1 : U μ x = V μ x)
    (h2 : U ν (x + unit n μ) = V ν (x + unit n μ)) (h3 : U μ (x + unit n ν) = V μ (x + unit n ν))
    (h4 : U ν x = V ν x) : plaq U μ ν x = plaq V μ ν x := by
  rw [plaq_eq, plaq_eq, h1, h2, h3, h4]

lemma plaq_triv (μ ν : Fin 4) (x : Site n) : plaq (triv : Config N n) μ ν x = 1 := by
  rw [plaq_eq]; simp [triv]

/-- **`lem:small-plaquettes`, the plaquettes**. -/
theorem small_plaquette (G : GaugeGroup N) (hN : 1 ≤ N) (U : Config N n) (hU : IsGField G U)
    (A'' A : Fin 4 → Site n → Mat) (v : Site n → GLN) (hv : ∀ z, v z ∈ G.carrier) (μ ν : Fin 4) (x : Site n)
    {a₀ aj α α₁ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ aj) (hα : 0 ≤ α) (hα₁ : 0 ≤ α₁)
    (hg1 : (U.gauge v) μ x = expU (Complex.I • ((a₀ : ℂ) • A μ x)))
    (hg2 : (U.gauge v) ν (x + unit n μ) = expU (Complex.I • ((a₀ : ℂ) • A ν (x + unit n μ))))
    (hg3 : (U.gauge v) μ (x + unit n ν) = expU (Complex.I • ((a₀ : ℂ) • A μ (x + unit n ν))))
    (hg4 : (U.gauge v) ν x = expU (Complex.I • ((a₀ : ℂ) • A ν x)))
    (hA1 : aj * ‖A μ x‖ ≤ α) (hA2 : aj * ‖A ν (x + unit n μ)‖ ≤ α) (hA3 : aj * ‖A μ (x + unit n ν)‖ ≤ α)
    (hA4 : aj * ‖A ν x‖ ≤ α) (hD1 : aj ^ 2 * ‖Dcov triv A a₀ μ ν x‖ ≤ α)
    (hD2 : aj ^ 2 * ‖Dcov triv A a₀ ν μ x‖ ≤ α)
    (hB1 : aj * ‖A'' μ x‖ ≤ α₁) (hB2 : aj * ‖A'' ν (x + unit n μ)‖ ≤ α₁)
    (hB3 : aj * ‖A'' μ (x + unit n ν)‖ ≤ α₁) (hB4 : aj * ‖A'' ν x‖ ≤ α₁)
    (hE1 : aj ^ 2 * ‖Dcov U A'' a₀ μ ν x‖ ≤ α₁) (hE2 : aj ^ 2 * ‖Dcov U A'' a₀ ν μ x‖ ≤ α₁)
    (hsm : 5120 * Real.sqrt N * (α + α₁) ≤ 1) :
    ‖((plaq (move U A'' a₀) μ ν x : GLN) : Mat) - 1‖ ≤ 10 * (α + α₁) * (a₀ / aj) ^ 2 := by
  have hN0 : 0 < N := hN
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  set W := U.gauge v with hW
  have hWG : IsGField G W := fun ρ z => by
    simp only [hW, Config.gauge]
    exact G.carrier.mul_mem (G.carrier.mul_mem (hv z) (hU ρ z)) (G.carrier.inv_mem (hv _))
  have htrivG : IsGField G (triv : Config N n) := fun _ _ => G.carrier.one_mem
  -- the plaquette of `U^v` is that of the moved trivial field
  have hWp : plaq W μ ν x = plaq (move triv A a₀) μ ν x := by
    refine plaq_congr _ _ μ ν x ?_ ?_ ?_ ?_ <;> simp [move, triv, hg1, hg2, hg3, hg4]
  -- the first step: `‖U^v(∂p) - id‖ ≤ 10α(a₀/a_j)²`
  have hstep1 := (moved_plaquette G hN triv htrivG A μ ν x ha₀ ha le_rfl hα (by rw [plaq_triv]; simp; exact (hs_le_opNorm hN0 0).trans (by simp))
    hA1 hA2 hA3 hA4 hD1 hD2 (by simp) (by
      have : 5120 * α ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hsN (by positivity : (0 : ℝ) ≤ 5120 * (α + α₁))]
      linarith)).2
  rw [plaq_triv] at hstep1
  have hWp1 : ‖((plaq W μ ν x : GLN) : Mat) - 1‖ ≤ 10 * α * (a₀ / aj) ^ 2 := by
    rw [hWp]; simpa using hstep1
  -- the second step: `‖(e^{ia₀Ad_vA''}U^v)(∂p) - U^v(∂p)‖ ≤ 10α₁(a₀/a_j)²`
  have hn : ∀ ρ z, ‖AdForm v A'' ρ z‖ = ‖A'' ρ z‖ := fun ρ z => norm_Ad_unitary G (hv z) _
  have hstep2 := (moved_plaquette G hN W hWG (AdForm v A'') μ ν x ha₀ ha (by positivity : (0 : ℝ) ≤ 10 * α) hα₁
    ((hs_le_opNorm hN0 _).trans hWp1)
    (by rw [hn]; exact hB1) (by rw [hn]; exact hB2) (by rw [hn]; exact hB3) (by rw [hn]; exact hB4)
    (by rw [Dcov_gauge, norm_Ad_unitary G (hv x)]; exact hE1)
    (by rw [Dcov_gauge, norm_Ad_unitary G (hv x)]; exact hE2)
    (by nlinarith [mul_le_mul_of_nonneg_left hsN (by positivity : (0 : ℝ) ≤ 5120 * (α + α₁))])
    (by
      have : 5120 * α₁ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hsN (by positivity : (0 : ℝ) ≤ 5120 * (α + α₁))]
      linarith)).2
  -- back to `𝐔`: the plaquette is conjugated by `v(x)`
  have hconj : plaq (move U A'' a₀) μ ν x = (v x)⁻¹ * plaq (move W (AdForm v A'') a₀) μ ν x * v x := by
    rw [hW, ← gauge_move, plaq_gauge]; group
  rw [hconj]
  have hvu := unitary_of_mem G (hv x)
  have e : (((v x)⁻¹ * plaq (move W (AdForm v A'') a₀) μ ν x * v x : GLN) : Mat) - 1 =
      (((v x)⁻¹ : GLN) : Mat) * (((plaq (move W (AdForm v A'') a₀) μ ν x : GLN) : Mat) - 1) * ((v x : GLN) : Mat) := by
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [Units.inv_mul]
  rw [e, opNorm_unitary_mul _ _ _ hvu.2 hvu.1]
  calc ‖((plaq (move W (AdForm v A'') a₀) μ ν x : GLN) : Mat) - 1‖
      ≤ ‖((plaq (move W (AdForm v A'') a₀) μ ν x : GLN) : Mat) - ((plaq W μ ν x : GLN) : Mat)‖ +
          ‖((plaq W μ ν x : GLN) : Mat) - 1‖ := by
        rw [← sub_add_sub_cancel _ ((plaq W μ ν x : GLN) : Mat) 1]; exact norm_add_le _ _
    _ ≤ 10 * α₁ * (a₀ / aj) ^ 2 + 10 * α * (a₀ / aj) ^ 2 := add_le_add hstep2 hWp1
    _ = 10 * (α + α₁) * (a₀ / aj) ^ 2 := by ring

/-- **`lem:small-plaquettes`, the bonds**: `‖Ad^{±1}_{𝐔(b)}X‖ ≤ e^{2α₁}‖X‖` for `a₀‖A''(b)‖ ≤ α₁`. -/
theorem small_Ad (G : GaugeGroup N) (U : Config N n) (hU : IsGField G U) (A'' : Fin 4 → Site n → Mat)
    (ρ : Fin 4) (z : Site n) {a₀ α₁ : ℝ} (ha₀ : 0 ≤ a₀) (hB : a₀ * ‖A'' ρ z‖ ≤ α₁) (X : Mat) :
    ‖Ad (move U A'' a₀ ρ z) X‖ ≤ Real.exp (2 * α₁) * ‖X‖ ∧
      ‖Ad (move U A'' a₀ ρ z)⁻¹ X‖ ≤ Real.exp (2 * α₁) * ‖X‖ := by
  have hUu := unitary_of_mem G (hU ρ z)
  set Y : Mat := Complex.I • ((a₀ : ℂ) • A'' ρ z) with hY
  have hYn : ‖Y‖ ≤ α₁ := by rw [hY, norm_I_eta a₀ ha₀]; exact hB
  have hYn' : ‖-Y‖ ≤ α₁ := by rw [norm_neg]; exact hYn
  have he1 : ‖exp Y‖ ≤ Real.exp α₁ := (norm_exp_le' Y).trans (Real.exp_le_exp.2 hYn)
  have he2 : ‖exp (-Y)‖ ≤ Real.exp α₁ := (norm_exp_le' (-Y)).trans (Real.exp_le_exp.2 hYn')
  have hmv : ((move U A'' a₀ ρ z : GLN) : Mat) = exp Y * ((U ρ z : GLN) : Mat) := by
    simp [move, hY]
  have hmi : (((move U A'' a₀ ρ z)⁻¹ : GLN) : Mat) = (((U ρ z)⁻¹ : GLN) : Mat) * exp (-Y) := by
    simp only [move, _root_.mul_inv_rev, Units.val_mul, expU_inv, expU_val, hY]
  have h2 : Real.exp (2 * α₁) = Real.exp α₁ * Real.exp α₁ := by rw [← Real.exp_add]; ring_nf
  constructor
  · unfold Ad
    rw [hmv, hmi]
    have e : exp Y * ((U ρ z : GLN) : Mat) * X * ((((U ρ z)⁻¹ : GLN) : Mat) * exp (-Y)) =
        exp Y * (((U ρ z : GLN) : Mat) * X * (((U ρ z)⁻¹ : GLN) : Mat)) * exp (-Y) := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]
    calc ‖exp Y * (((U ρ z : GLN) : Mat) * X * (((U ρ z)⁻¹ : GLN) : Mat)) * exp (-Y)‖
        ≤ ‖exp Y‖ * ‖((U ρ z : GLN) : Mat) * X * (((U ρ z)⁻¹ : GLN) : Mat)‖ * ‖exp (-Y)‖ :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (norm_nonneg _))
      _ = ‖exp Y‖ * ‖X‖ * ‖exp (-Y)‖ := by rw [opNorm_unitary_mul _ _ _ hUu.1 hUu.2]
      _ ≤ Real.exp α₁ * ‖X‖ * Real.exp α₁ :=
          mul_le_mul (mul_le_mul_of_nonneg_right he1 (norm_nonneg _)) he2 (norm_nonneg _) (by positivity)
      _ = Real.exp α₁ * Real.exp α₁ * ‖X‖ := by ring
  · unfold Ad
    rw [inv_inv, hmv, hmi]
    have e : (((U ρ z)⁻¹ : GLN) : Mat) * exp (-Y) * X * (exp Y * ((U ρ z : GLN) : Mat)) =
        (((U ρ z)⁻¹ : GLN) : Mat) * (exp (-Y) * X * exp Y) * ((U ρ z : GLN) : Mat) := by
      simp only [Matrix.mul_assoc]
    rw [e, opNorm_unitary_mul _ _ _ hUu.2 hUu.1, h2]
    calc ‖exp (-Y) * X * exp Y‖ ≤ ‖exp (-Y)‖ * ‖X‖ * ‖exp Y‖ :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (norm_nonneg _))
      _ ≤ Real.exp α₁ * ‖X‖ * Real.exp α₁ :=
          mul_le_mul (mul_le_mul_of_nonneg_right he2 (norm_nonneg _)) he1 (norm_nonneg _) (by positivity)
      _ = Real.exp α₁ * Real.exp α₁ * ‖X‖ := by ring

end SmallPlaquettes

end CoreLean
