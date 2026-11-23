/-
`lem:current-expansion`(ii) of BALABAN_CORE.tex: the operator `𝖪(𝐔) = D^*D + DD^* - Δ` on `1`-forms is of
the order zero.

`(𝖪(𝐔)A)_μ = Σ_ν (D_μD^*_ν - D^*_νD_μ)A_ν` (`Kop_eq`), and
`((D_μD^*_ν - D^*_νD_μ)λ)(x) = a⁻²(Ad_{𝐔(γ)} - Ad_{𝐔(γ')})λ(x + ae_μ - ae_ν)` (`comm_eq`), with `γ` the path from
`x` through `x + ae_μ` and `γ'` the one through `x - ae_ν`; for `ν = μ` both transports are trivial
(`comm_self`). For `ν ≠ μ`, `𝐔(γ) = W𝐔(γ')` with `W = Ad_{𝐔(x, x - ae_ν)}𝐔(∂p_{νμ}(x - ae_ν))` (`hol_gamma`),
and `‖Ad_WY - Y‖ ≤ 2‖W - 1‖‖Y‖‖W⁻¹‖` (`norm_Ad_sub_le`). So `(𝖪(𝐔)A)_μ(x)` depends on the values
`A_ν(x + ae_μ - ae_ν)` only, and with the core's hypotheses (the plaquettes of `st(b)` with
`‖𝐔(∂p) - 1‖ ≤ ω ≤ 1/48`, transports along one bond changing the norm by a factor of at most `2`)
`‖(𝖪(𝐔)A)_μ(x)‖ ≤ 60|a|⁻²ωm₀` (`norm_Kop_le`), which is at most `C₈|a|⁻²|𝐔(∂p) - 1|m₀`, `C₈ = 512N`, since
`ω ≤ √N|𝐔(∂p) - 1|`.
-/
import CoreLean.OpNorm
import CoreLean.Differences

open scoped Matrix.Norms.L2Operator
open Matrix Finset

namespace CoreLean

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable (a : ℂ)

/-- `𝖪(𝐔)A = D^*_𝐔D_𝐔A + D_𝐔D^*_𝐔A - Δ_𝐔A` on `1`-forms. -/
noncomputable def Kop (U : Config N n) (A : Form1 N n) : Form1 N n :=
  fun μ x => Ds2 a U (D1 a U A) μ x + Dfw a U μ (Ds1 a U A) x - Lap a U (A μ) x

lemma Dbw_sub (U : Config N n) (ν : Fin 4) (f g : Form0 N n) (x : Site n) :
    Dbw a U ν (f - g) x = Dbw a U ν f x - Dbw a U ν g x := by
  simp only [Dbw, Pi.sub_apply, Ad_sub, smul_sub]
  abel

lemma Dbw_fun_sub (U : Config N n) (ν : Fin 4) (f g : Form0 N n) (x : Site n) :
    Dbw a U ν (fun y => f y - g y) x = Dbw a U ν f x - Dbw a U ν g x :=
  Dbw_sub a U ν f g x

lemma Dfw_sum (U : Config N n) (μ : Fin 4) (g : Fin 4 → Form0 N n) (x : Site n) :
    Dfw a U μ (fun y => ∑ ν, g ν y) x = ∑ ν, Dfw a U μ (g ν) x := by
  simp only [Dfw, Ad_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]

/-- `(𝖪(𝐔)A)_μ = Σ_ν (D_μD^*_ν - D^*_νD_μ)A_ν`. -/
theorem Kop_eq (U : Config N n) (A : Form1 N n) (μ : Fin 4) (x : Site n) :
    Kop a U A μ x =
      ∑ ν, (Dfw a U μ (Dbw a U ν (A ν)) x - Dbw a U ν (Dfw a U μ (A ν)) x) := by
  have h1 : Ds2 a U (D1 a U A) μ x = ∑ ν, if ν ≠ μ then
      Dbw a U ν (Dfw a U ν (A μ)) x - Dbw a U ν (Dfw a U μ (A ν)) x else 0 := by
    simp only [Ds2, D1]
    refine Finset.sum_congr rfl fun ν _ => ?_
    split_ifs
    · exact Dbw_fun_sub a U ν _ _ x
    · rfl
  have h2 : Dfw a U μ (Ds1 a U A) x = ∑ ν, Dfw a U μ (Dbw a U ν (A ν)) x := by
    exact Dfw_sum a U μ (fun ν => Dbw a U ν (A ν)) x
  have h3 : Lap a U (A μ) x = ∑ ν, Dbw a U ν (Dfw a U ν (A μ)) x := rfl
  rw [Kop, h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · subst h; simp
  · simp only [ne_eq, h, not_false_eq_true, if_true]
    abel

/-- `((D_μD^*_ν - D^*_νD_μ)λ)(x) = a⁻²(Ad_{𝐔(γ)} - Ad_{𝐔(γ')})λ(x + ae_μ - ae_ν)`. -/
theorem comm_eq (U : Config N n) (μ ν : Fin 4) (l : Form0 N n) (x : Site n) :
    Dfw a U μ (Dbw a U ν l) x - Dbw a U ν (Dfw a U μ l) x =
      (a⁻¹ * a⁻¹) • (Ad (U μ x * U.val ⟨x + unit n μ, ν, false⟩) (l (x + unit n μ - unit n ν)) -
        Ad (U.val ⟨x, ν, false⟩ * U μ (x - unit n ν)) (l (x + unit n μ - unit n ν))) := by
  have e : x - unit n ν + unit n μ = x + unit n μ - unit n ν := by abel
  simp only [Dfw, Dbw, Ad_smul, Ad_sub, Ad_mul, e]
  module

/-- For `ν = μ` the two transports are trivial. -/
theorem comm_self (U : Config N n) (μ : Fin 4) (l : Form0 N n) (x : Site n) :
    Dfw a U μ (Dbw a U μ l) x - Dbw a U μ (Dfw a U μ l) x = 0 := by
  rw [comm_eq]
  have e1 : U μ x * U.val ⟨x + unit n μ, μ, false⟩ = 1 := by
    simp [Config.val]
  have e2 : U.val ⟨x, μ, false⟩ * U μ (x - unit n μ) = 1 := by
    simp [Config.val]
  rw [e1, e2, sub_self, smul_zero]

/-- `𝐔(γ) = W𝐔(γ')` with `W = 𝐔(x, x - ae_ν)𝐔(∂p_{νμ}(x - ae_ν))𝐔(x, x - ae_ν)⁻¹`. -/
theorem hol_gamma (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    U μ x * U.val ⟨x + unit n μ, ν, false⟩ =
      (U.val ⟨x, ν, false⟩ * plaq U ν μ (x - unit n ν) * (U.val ⟨x, ν, false⟩)⁻¹) *
        (U.val ⟨x, ν, false⟩ * U μ (x - unit n ν)) := by
  have e1 : x - unit n ν + unit n ν = x := by abel
  have e2 : x - unit n ν + unit n ν + unit n μ = x + unit n μ := by abel
  have e3 : x - unit n ν + unit n μ = x + unit n μ - unit n ν := by abel
  simp only [plaq, Config.hol, plaqPath, List.map, List.prod_cons, List.prod_nil, Config.val,
    if_true, Bool.false_eq_true, if_false, e1, e2, e3, mul_one]
  group

/-- `‖Ad_WY - Y‖ ≤ 2‖W - 1‖‖Y‖‖W⁻¹‖`. -/
lemma norm_Ad_sub_le (W : GLN) (Y : Mat) :
    ‖Ad W Y - Y‖ ≤ 2 * ‖(W : Mat) - 1‖ * ‖Y‖ * ‖((W⁻¹ : GLN) : Mat)‖ := by
  have e : Ad W Y - Y = ((W : Mat) - 1) * Y * ((W⁻¹ : GLN) : Mat) -
      Y * ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) := by
    have hWW : ((W⁻¹ : GLN) : Mat) * (W : Mat) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Ad, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hWW]
    abel
  rw [e]
  calc ‖((W : Mat) - 1) * Y * ((W⁻¹ : GLN) : Mat) - Y * ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)‖
      ≤ ‖((W : Mat) - 1) * Y * ((W⁻¹ : GLN) : Mat)‖ +
          ‖Y * ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)‖ := norm_sub_le _ _
    _ ≤ ‖(W : Mat) - 1‖ * ‖Y‖ * ‖((W⁻¹ : GLN) : Mat)‖ +
          ‖Y‖ * ‖((W⁻¹ : GLN) : Mat)‖ * ‖(W : Mat) - 1‖ := by
        gcongr
        · exact (opNorm_mul_le _ _).trans (by gcongr; exact opNorm_mul_le _ _)
        · exact (opNorm_mul_le _ _).trans (by gcongr; exact opNorm_mul_le _ _)
    _ = 2 * ‖(W : Mat) - 1‖ * ‖Y‖ * ‖((W⁻¹ : GLN) : Mat)‖ := by ring

lemma opNorm_one_le : ‖(1 : Mat)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp

/-- `‖W⁻¹‖ ≤ 1/(1 - ‖W - 1‖)` for `‖W - 1‖ < 1`. -/
lemma norm_inv_le (W : GLN) (h : ‖(W : Mat) - 1‖ < 1) :
    ‖((W⁻¹ : GLN) : Mat)‖ * (1 - ‖(W : Mat) - 1‖) ≤ 1 := by
  have hWW : ((W⁻¹ : GLN) : Mat) * (W : Mat) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : ((W⁻¹ : GLN) : Mat) = 1 - ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) := by
    rw [mul_sub, hWW, mul_one]; abel
  have h1 : ‖((W⁻¹ : GLN) : Mat)‖ ≤ 1 + ‖((W⁻¹ : GLN) : Mat)‖ * ‖(W : Mat) - 1‖ := by
    calc ‖((W⁻¹ : GLN) : Mat)‖ = ‖1 - ((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)‖ := by rw [← e]
      _ ≤ ‖(1 : Mat)‖ + ‖((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1)‖ := norm_sub_le _ _
      _ ≤ 1 + ‖((W⁻¹ : GLN) : Mat)‖ * ‖(W : Mat) - 1‖ :=
          add_le_add opNorm_one_le (opNorm_mul_le _ _)
  nlinarith

/-- The term of a direction `ν ≠ μ`: with `‖𝐔(∂p_{νμ}(x - ae_ν)) - 1‖ ≤ ω ≤ 1/48`, the transports along the
bonds `(x, x - ae_ν)` and `(x - ae_ν, x - ae_ν + ae_μ)` changing the norm by a factor of at most `2`, and
`‖λ(x + ae_μ - ae_ν)‖ ≤ m₀`, it is at most `20|a|⁻²ωm₀`. -/
theorem norm_comm_le (U : Config N n) {μ ν : Fin 4} (x : Site n) (l : Form0 N n) {ω m₀ : ℝ}
    (hω : ‖((plaq U ν μ (x - unit n ν) : GLN) : Mat) - 1‖ ≤ ω) (hω1 : ω ≤ 1 / 48)
    (hV : ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hR : ∀ Z : Mat, ‖Ad (U μ (x - unit n ν)) Z‖ ≤ 2 * ‖Z‖)
    (hm : ‖l (x + unit n μ - unit n ν)‖ ≤ m₀) :
    ‖Dfw a U μ (Dbw a U ν l) x - Dbw a U ν (Dfw a U μ l) x‖ ≤ 20 * ‖a‖⁻¹ ^ 2 * ω * m₀ := by
  set V := U.val ⟨x, ν, false⟩
  set P := plaq U ν μ (x - unit n ν)
  set R := U μ (x - unit n ν)
  set Y := l (x + unit n μ - unit n ν)
  set W : GLN := V * P * V⁻¹
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans hω
  have hm0 : 0 ≤ m₀ := (norm_nonneg _).trans hm
  rw [comm_eq, hol_gamma]
  rw [show (V * P * V⁻¹ * (V * R) : GLN) = W * (V * R) from rfl, Ad_mul]
  set Y' := Ad (V * R) Y
  -- the three factors
  have hW1 : ‖(W : Mat) - 1‖ ≤ 2 * ω := by
    have e : (W : Mat) - 1 = Ad V ((P : Mat) - 1) := by
      simp only [W, Ad, Units.val_mul, mul_sub, sub_mul, mul_one]
      rw [Units.mul_inv]
    rw [e]
    exact (hV _).trans (by linarith)
  have hY' : ‖Y'‖ ≤ 4 * m₀ := by
    simp only [Y', Ad_mul]
    calc ‖Ad V (Ad R Y)‖ ≤ 2 * ‖Ad R Y‖ := hV _
      _ ≤ 2 * (2 * ‖Y‖) := by gcongr; exact hR _
      _ ≤ 4 * m₀ := by linarith
  have hWinv : ‖((W⁻¹ : GLN) : Mat)‖ ≤ 24 / 23 := by
    have h := norm_inv_le W (by linarith)
    have hpos : (0 : ℝ) < 1 - ‖(W : Mat) - 1‖ := by linarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [norm_nonneg ((W⁻¹ : GLN) : Mat)]
  have hAd := norm_Ad_sub_le W Y'
  rw [norm_smul, norm_mul, norm_inv]
  calc ‖a‖⁻¹ * ‖a‖⁻¹ * ‖Ad W Y' - Y'‖
      ≤ ‖a‖⁻¹ * ‖a‖⁻¹ * (2 * (2 * ω) * (4 * m₀) * (24 / 23)) := by
        gcongr
        refine hAd.trans ?_
        gcongr
    _ ≤ 20 * ‖a‖⁻¹ ^ 2 * ω * m₀ := by
        have : 0 ≤ ‖a‖⁻¹ * ‖a‖⁻¹ * (ω * m₀) := by positivity
        nlinarith

/-- `lem:current-expansion`(ii): `(𝖪(𝐔)A)_μ(x)` depends only on the values `A_ν(x + ae_μ - ae_ν)`, `ν ≠ μ`,
and with the hypotheses of `norm_comm_le` for the three plaquettes `p_{νμ}(x - ae_ν)` of `st(b)`,
`‖(𝖪(𝐔)A)_μ(x)‖ ≤ 60|a|⁻²ωm₀`. -/
theorem norm_Kop_le (U : Config N n) (A : Form1 N n) (μ : Fin 4) (x : Site n) {ω m₀ : ℝ}
    (hω : ∀ ν, ν ≠ μ → ‖((plaq U ν μ (x - unit n ν) : GLN) : Mat) - 1‖ ≤ ω) (hω1 : ω ≤ 1 / 48)
    (hV : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U.val ⟨x, ν, false⟩) Z‖ ≤ 2 * ‖Z‖)
    (hR : ∀ ν, ν ≠ μ → ∀ Z : Mat, ‖Ad (U μ (x - unit n ν)) Z‖ ≤ 2 * ‖Z‖)
    (hm : ∀ ν, ν ≠ μ → ‖A ν (x + unit n μ - unit n ν)‖ ≤ m₀) :
    ‖Kop a U A μ x‖ ≤ 60 * ‖a‖⁻¹ ^ 2 * ω * m₀ := by
  have hω0 : 0 ≤ ω := by
    obtain ⟨ν, hν⟩ : ∃ ν : Fin 4, ν ≠ μ := ⟨μ + 1, by simp⟩
    exact (norm_nonneg _).trans (hω ν hν)
  rw [Kop_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ μ), comm_self, zero_add]
  calc ‖∑ ν ∈ Finset.univ.erase μ,
        (Dfw a U μ (Dbw a U ν (A ν)) x - Dbw a U ν (Dfw a U μ (A ν)) x)‖
      ≤ ∑ ν ∈ Finset.univ.erase μ,
          ‖Dfw a U μ (Dbw a U ν (A ν)) x - Dbw a U ν (Dfw a U μ (A ν)) x‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ Finset.univ.erase μ, 20 * ‖a‖⁻¹ ^ 2 * ω * m₀ := by
        refine Finset.sum_le_sum fun ν hν => ?_
        have hνμ : ν ≠ μ := Finset.ne_of_mem_erase hν
        exact norm_comm_le a U x (A ν) (hω ν hνμ) hω1 (hV ν hνμ) (hR ν hνμ) (hm ν hνμ)
    _ = 60 * ‖a‖⁻¹ ^ 2 * ω * m₀ := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ μ), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end CoreLean
