/-
`cor:moved-plaquette` of BALABAN_CORE.tex (`0c2967992d08`): the plaquettes of a moved gauge field.

For a plaquette `p = p_{μν}(x)` of `T^{(0)}`, a gauge field `U` and a `1`-form `𝐀` with values in matrices,
`|(e^{iη𝐀}U)(∂p) - U(∂p)| ≤ ‖(e^{iη𝐀}U)(∂p) - U(∂p)‖ ≤ 10ρ(η/a)²` under the bounds of the corollary. The
proof is the paragraph on the plaquettes in the proof of `prop:space-stability`(i) with `A' = 0`:
* `moved_identity`: `eq:moved-plaquette`, `(e^{iη𝐀}U)(∂p) = e^{iη𝖺}e^{iη𝖻}e^{-iη𝖼}e^{-iη𝖽}U(∂p)` with
  `𝖺 = 𝐀₁`, `𝖻 = Ad_{U₁}𝐀₂`, `𝖼 = Ad_{U(∂p)U₄}𝐀₃`, `𝖽 = Ad_{U(∂p)}𝐀₄`;
* `sum_identity`: `𝖺 + 𝖻 - 𝖼 - 𝖽 = η(D_U𝐀)_{μν}(x) + (1 - Ad_{U(∂p)})(Ad_{U₄}𝐀₃ + 𝐀₄)`;
* `moved_plaquette`: the bound, with `‖·‖` the operator norm. Since `U` is `G`-valued, `Ad_{U_i}` and
  `Ad_{U(∂p)}` are isometries, and the bound obtained is `3ρ(η/a)²`.
-/
import CoreLean.RegularAverages

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace MovedPlaquette

open LatticePaths LatticeKappa RegularAverages

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The moved gauge field `e^{iη𝐀}U` on the positive bonds. -/
def move (U : Config N n) (A : Fin 4 → Site n → Mat) (η : ℝ) : Config N n :=
  fun ρ z => expU (Complex.I • ((η : ℂ) • A ρ z)) * U ρ z

/-- The covariant difference `(D_{U,μ}𝐀_ν)(x) = η⁻¹(Ad_{U(x, x + ηe_μ)}𝐀_ν(x + ηe_μ) - 𝐀_ν(x))`
(`eq:forward-difference` on `T^{(0)}`). -/
def Dcov (U : Config N n) (A : Fin 4 → Site n → Mat) (η : ℝ) (μ ν : Fin 4) (x : Site n) : Mat :=
  ((η : ℂ)⁻¹) • (Ad (U μ x) (A ν (x + unit n μ)) - A ν x)

/-- `eq:moved-plaquette`. -/
lemma moved_identity (U : Config N n) (A : Fin 4 → Site n → Mat) (η : ℝ) (μ ν : Fin 4) (x : Site n) :
    plaq (move U A η) μ ν x =
      expU (Complex.I • ((η : ℂ) • A μ x)) *
        expU (Complex.I • ((η : ℂ) • Ad (U μ x) (A ν (x + unit n μ)))) *
        expU (-(Complex.I • ((η : ℂ) • Ad (plaq U μ ν x * U ν x) (A μ (x + unit n ν))))) *
        expU (-(Complex.I • ((η : ℂ) • Ad (plaq U μ ν x) (A ν x)))) * plaq U μ ν x := by
  set P := plaq U μ ν x with hPd
  have hP : P = U μ x * U ν (x + unit n μ) * (U μ (x + unit n ν))⁻¹ * (U ν x)⁻¹ := plaq_eq U μ ν x
  rw [plaq_eq]
  simp only [move]
  set e1 := expU (Complex.I • ((η : ℂ) • A μ x))
  set e2 := expU (Complex.I • ((η : ℂ) • A ν (x + unit n μ)))
  set e3 := expU (Complex.I • ((η : ℂ) • A μ (x + unit n ν)))
  set e4 := expU (Complex.I • ((η : ℂ) • A ν x))
  have hid : e1 * U μ x * (e2 * U ν (x + unit n μ)) * (e3 * U μ (x + unit n ν))⁻¹ * (e4 * U ν x)⁻¹ =
      e1 * (U μ x * e2 * (U μ x)⁻¹) * ((P * U ν x) * e3 * (P * U ν x)⁻¹)⁻¹ * (P * e4 * P⁻¹)⁻¹ * P := by
    rw [hP]; group
  rw [hid, expU_conj, expU_conj, expU_conj, expU_inv, expU_inv, Ad_smul, Ad_smul, Ad_smul, Ad_smul,
    Ad_smul, Ad_smul]

/-- `𝖺 + 𝖻 - 𝖼 - 𝖽 = η(D_U𝐀)_{μν}(x) + (1 - Ad_{U(∂p)})(Ad_{U₄}𝐀₃ + 𝐀₄)`. -/
lemma sum_identity (U : Config N n) (A : Fin 4 → Site n → Mat) {η : ℝ} (hη : η ≠ 0) (μ ν : Fin 4)
    (x : Site n) :
    A μ x + Ad (U μ x) (A ν (x + unit n μ)) - Ad (plaq U μ ν x * U ν x) (A μ (x + unit n ν)) -
        Ad (plaq U μ ν x) (A ν x) =
      (η : ℂ) • (Dcov U A η μ ν x - Dcov U A η ν μ x) +
        ((Ad (U ν x) (A μ (x + unit n ν)) + A ν x) -
          Ad (plaq U μ ν x) (Ad (U ν x) (A μ (x + unit n ν)) + A ν x)) := by
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  simp only [Dcov, smul_sub, smul_smul, mul_inv_cancel₀ hη', one_smul, Ad_mul, Ad_add]
  abel

/-- `‖Z - Ad_P Z‖ ≤ 2‖P - 1‖‖Z‖` for `P ∈ G`. -/
lemma norm_sub_Ad_le (G : GaugeGroup N) {P : GLN} (hP : P ∈ G.carrier) (Z : Mat) :
    ‖Z - Ad P Z‖ ≤ 2 * ‖(P : Mat) - 1‖ * ‖Z‖ := by
  have hinv : ((P⁻¹ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := G.unitary _ (G.carrier.inv_mem hP)
  have e : Z - Ad P Z = (Z * ((P : Mat) - 1) - ((P : Mat) - 1) * Z) * ((P⁻¹ : GLN) : Mat) := by
    simp only [Ad, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv]
    abel
  rw [e, CStarRing.norm_mul_mem_unitary _ hinv]
  calc ‖Z * ((P : Mat) - 1) - ((P : Mat) - 1) * Z‖
      ≤ ‖Z * ((P : Mat) - 1)‖ + ‖((P : Mat) - 1) * Z‖ := norm_sub_le _ _
    _ ≤ ‖Z‖ * ‖(P : Mat) - 1‖ + ‖(P : Mat) - 1‖ * ‖Z‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(P : Mat) - 1‖ * ‖Z‖ := by ring

lemma norm_I_eta (η : ℝ) (hη : 0 ≤ η) (Y : Mat) : ‖Complex.I • ((η : ℂ) • Y)‖ = η * ‖Y‖ := by
  rw [norm_smul, norm_smul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hη]

/-- **`cor:moved-plaquette`**: for a `G`-valued gauge field `U`, a plaquette `p = p_{μν}(x)` with
`|U(∂p) - id| ≤ α₀(η/a)²`, `a‖𝐀(b)‖ ≤ ρ` on its four bonds, `a²‖(D_{U,μ}𝐀_ν)(x)‖ ≤ ρ` and
`a²‖(D_{U,ν}𝐀_μ)(x)‖ ≤ ρ`, `a ≥ η > 0`, `√Nα₀ ≤ 1/512`, `ρ ≤ 1/512`:
`|(e^{iη𝐀}U)(∂p) - U(∂p)| ≤ ‖(e^{iη𝐀}U)(∂p) - U(∂p)‖ ≤ 10ρ(η/a)²`. -/
theorem moved_plaquette (G : GaugeGroup N) (hN : 1 ≤ N) (U : Config N n) (hU : IsGField G U)
    (A : Fin 4 → Site n → Mat) (μ ν : Fin 4) (x : Site n) {η a ρ α₀ : ℝ} (hη : 0 < η) (ha : η ≤ a)
    (hα₀ : 0 ≤ α₀) (hρ : 0 ≤ ρ)
    (hP : hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ α₀ * (η / a) ^ 2)
    (hA1 : a * ‖A μ x‖ ≤ ρ) (hA2 : a * ‖A ν (x + unit n μ)‖ ≤ ρ)
    (hA3 : a * ‖A μ (x + unit n ν)‖ ≤ ρ) (hA4 : a * ‖A ν x‖ ≤ ρ)
    (hD1 : a ^ 2 * ‖Dcov U A η μ ν x‖ ≤ ρ) (hD2 : a ^ 2 * ‖Dcov U A η ν μ x‖ ≤ ρ)
    (hsm : Real.sqrt N * α₀ ≤ 1 / 512) (hρs : ρ ≤ 1 / 512) :
    hs (((plaq (move U A η) μ ν x : GLN) : Mat) - ((plaq U μ ν x : GLN) : Mat)) ≤
        ‖((plaq (move U A η) μ ν x : GLN) : Mat) - ((plaq U μ ν x : GLN) : Mat)‖ ∧
      ‖((plaq (move U A η) μ ν x : GLN) : Mat) - ((plaq U μ ν x : GLN) : Mat)‖ ≤ 10 * ρ * (η / a) ^ 2 := by
  have hN0 : 0 < N := hN
  have ha0 : 0 < a := by linarith
  refine ⟨hs_le_opNorm hN0 _, ?_⟩
  set t : ℝ := η / a with ht
  have ht0 : 0 < t := div_pos hη ha0
  have ht1 : t ≤ 1 := (div_le_one ha0).2 ha
  set P := plaq U μ ν x with hPd
  have hPG : P ∈ G.carrier := hU.hol_mem _
  have hPU : (P : Mat) ∈ unitaryGroup (Fin N) ℂ := G.unitary _ hPG
  have hU4 : U ν x ∈ G.carrier := hU ν x
  have hPU4 : P * U ν x ∈ G.carrier := G.carrier.mul_mem hPG hU4
  -- the four exponents
  set Xa := Complex.I • ((η : ℂ) • A μ x) with hXa
  set Xb := Complex.I • ((η : ℂ) • Ad (U μ x) (A ν (x + unit n μ))) with hXb
  set Xc := Complex.I • ((η : ℂ) • Ad (P * U ν x) (A μ (x + unit n ν))) with hXc
  set Xd := Complex.I • ((η : ℂ) • Ad P (A ν x)) with hXd
  have hmove : ((plaq (move U A η) μ ν x : GLN) : Mat) = ([Xa, Xb, -Xc, -Xd].map exp).prod * (P : Mat) := by
    rw [moved_identity]
    simp only [Units.val_mul, expU_val, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Matrix.mul_assoc]
    rfl
  -- their norms
  have nA : ∀ Y : Mat, a * ‖Y‖ ≤ ρ → η * ‖Y‖ ≤ t * ρ := fun Y hY => by
    rw [ht, div_mul_eq_mul_div, le_div_iff₀ ha0]
    nlinarith [norm_nonneg Y]
  have na : ‖Xa‖ ≤ t * ρ := by rw [hXa, norm_I_eta η hη.le]; exact nA _ hA1
  have nb : ‖Xb‖ ≤ t * ρ := by
    rw [hXb, norm_I_eta η hη.le, GaugeGroup.opNorm_Ad (hU μ x)]; exact nA _ hA2
  have nc : ‖-Xc‖ ≤ t * ρ := by
    rw [norm_neg, hXc, norm_I_eta η hη.le, GaugeGroup.opNorm_Ad hPU4]; exact nA _ hA3
  have nd : ‖-Xd‖ ≤ t * ρ := by
    rw [norm_neg, hXd, norm_I_eta η hη.le, GaugeGroup.opNorm_Ad hPG]; exact nA _ hA4
  have hT : (([Xa, Xb, -Xc, -Xd]).map norm).sum ≤ 4 * (t * ρ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linarith
  have htρ : t * ρ ≤ 1 / 512 := by nlinarith
  obtain ⟨hE, -⟩ := prod_exp_small _ hT (by linarith)
  -- the first-order part
  have hsumX : ([Xa, Xb, -Xc, -Xd]).sum = Complex.I • ((η : ℂ) •
      (A μ x + Ad (U μ x) (A ν (x + unit n μ)) - Ad (P * U ν x) (A μ (x + unit n ν)) - Ad P (A ν x))) := by
    simp only [List.sum_cons, List.sum_nil, add_zero, hXa, hXb, hXc, hXd, smul_sub, smul_add]
    abel
  rw [hsumX, sum_identity U A hη.ne'] at hE
  set Z : Mat := Ad (U ν x) (A μ (x + unit n ν)) + A ν x with hZ
  set S : Mat := (η : ℂ) • (Dcov U A η μ ν x - Dcov U A η ν μ x) + (Z - Ad P Z) with hS
  -- `η‖S‖ ≤ 2t²ρ + 4√Nα₀t³ρ`
  have nD : ∀ Y : Mat, a ^ 2 * ‖Y‖ ≤ ρ → η * (η * ‖Y‖) ≤ t ^ 2 * ρ := fun Y hY => by
    rw [ht, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg Y, mul_pos hη hη]
  have nZ : η * ‖Z‖ ≤ 2 * (t * ρ) := by
    have := norm_add_le (Ad (U ν x) (A μ (x + unit n ν))) (A ν x)
    rw [GaugeGroup.opNorm_Ad hU4] at this
    nlinarith [nA _ hA3, nA _ hA4]
  have nP : ‖(P : Mat) - 1‖ ≤ Real.sqrt N * α₀ * t ^ 2 := by
    calc ‖(P : Mat) - 1‖ ≤ Real.sqrt N * hs ((P : Mat) - 1) := opNorm_le_sqrt_mul_hs _
      _ ≤ Real.sqrt N * (α₀ * t ^ 2) := mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)
      _ = Real.sqrt N * α₀ * t ^ 2 := by ring
  have nS : η * ‖S‖ ≤ 2 * (t ^ 2 * ρ) + 4 * (Real.sqrt N * α₀) * t ^ 3 * ρ := by
    have h1 : ‖S‖ ≤ η * ‖Dcov U A η μ ν x‖ + η * ‖Dcov U A η ν μ x‖ + 2 * ‖(P : Mat) - 1‖ * ‖Z‖ := by
      have := norm_add_le ((η : ℂ) • (Dcov U A η μ ν x - Dcov U A η ν μ x)) (Z - Ad P Z)
      have h2 : ‖(η : ℂ) • (Dcov U A η μ ν x - Dcov U A η ν μ x)‖ ≤
          η * ‖Dcov U A η μ ν x‖ + η * ‖Dcov U A η ν μ x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hη.le, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hη.le
      have h3 := norm_sub_Ad_le G hPG Z
      linarith
    have h4 : η * (2 * ‖(P : Mat) - 1‖ * ‖Z‖) ≤ 2 * (Real.sqrt N * α₀ * t ^ 2) * (2 * (t * ρ)) := by
      have : η * (2 * ‖(P : Mat) - 1‖ * ‖Z‖) = 2 * ‖(P : Mat) - 1‖ * (η * ‖Z‖) := by ring
      rw [this]
      exact mul_le_mul (by linarith) nZ (by positivity) (by positivity)
    have h5 := nD _ hD1
    have h6 := nD _ hD2
    calc η * ‖S‖ ≤ η * (η * ‖Dcov U A η μ ν x‖ + η * ‖Dcov U A η ν μ x‖ + 2 * ‖(P : Mat) - 1‖ * ‖Z‖) :=
          mul_le_mul_of_nonneg_left h1 hη.le
      _ = η * (η * ‖Dcov U A η μ ν x‖) + η * (η * ‖Dcov U A η ν μ x‖) +
          η * (2 * ‖(P : Mat) - 1‖ * ‖Z‖) := by ring
      _ ≤ t ^ 2 * ρ + t ^ 2 * ρ + 2 * (Real.sqrt N * α₀ * t ^ 2) * (2 * (t * ρ)) := by linarith
      _ = 2 * (t ^ 2 * ρ) + 4 * (Real.sqrt N * α₀) * t ^ 3 * ρ := by ring
  -- `‖E - 1‖ ≤ 3ρt²`
  set E : Mat := ([Xa, Xb, -Xc, -Xd].map exp).prod with hEd
  have hES : ‖E - 1‖ ≤ 3 * ρ * t ^ 2 := by
    have e : E - 1 = (E - 1 - Complex.I • ((η : ℂ) • S)) + Complex.I • ((η : ℂ) • S) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_I_eta η hη.le]
    have hsN0 : 0 ≤ Real.sqrt N * α₀ := by positivity
    have k1 : (4 * (t * ρ)) ^ 2 = 16 * ρ * (t ^ 2 * ρ) := by ring
    have k2 : 4 * (Real.sqrt N * α₀) * t ^ 3 * ρ ≤ 4 * (1 / 512) * (t ^ 2 * ρ) := by
      have : t ^ 3 ≤ t ^ 2 := by nlinarith
      calc 4 * (Real.sqrt N * α₀) * t ^ 3 * ρ = 4 * (Real.sqrt N * α₀) * (t ^ 3 * ρ) := by ring
        _ ≤ 4 * (1 / 512) * (t ^ 2 * ρ) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right this hρ) (by positivity) (by norm_num)
    have k3 : 16 * ρ * (t ^ 2 * ρ) ≤ 16 * (1 / 512) * (t ^ 2 * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have k4 : 0 ≤ t ^ 2 * ρ := by positivity
    nlinarith
  -- the moved plaquette
  have hdiff : ((plaq (move U A η) μ ν x : GLN) : Mat) - (P : Mat) = (E - 1) * (P : Mat) := by
    rw [hmove, Matrix.sub_mul, Matrix.one_mul]
  rw [hdiff, CStarRing.norm_mul_mem_unitary _ hPU]
  have : 0 ≤ ρ * t ^ 2 := by positivity
  linarith

end MovedPlaquette

end CoreLean

end
