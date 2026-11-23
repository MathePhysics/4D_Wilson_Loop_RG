/-
`lem:chart`(i) of BALABAN_CORE.tex (`b1ff7d2601a1`), the injectivity: `A ↦ e^{iA}` is injective on the
Hermitean matrices of norm less than `π` (`exp_I_injOn`), in particular on `{A ∈ 𝔤 | ‖A‖ < π}`.

The core argues with the spectral decompositions of `A` and `e^{iA}`. Here: with the spectral theorem
`A = U diag(λ) U^*`, `|λ_k| < π`, the Lagrange polynomial `p` through the points `(e^{iλ_k}, λ_k)` (the
inverse on the unit circle being `arg`, `arg e^{iλ} = λ` for `λ ∈ (-π, π]`) gives `A = p(e^{iA})`
(`eq_aeval_exp`). If `e^{iA} = e^{iB}`, then `B` commutes with `e^{iB} = e^{iA}` and so with `A`;
hence `e^{i(A-B)} = e^{iA}e^{-iB} = 1`, and the eigenvalues `μ` of the Hermitean matrix `A - B`, with
`|μ| < 2π` and `e^{iμ} = 1`, vanish (`eq_zero_of_exp_I_eq_one`).

The rest of (i) (the invariance of the domain under `W ↦ W⁻¹` and under the conjugation by `G`, with
`log W⁻¹ = -log W` and `log(uWu⁻¹) = Ad_u log W`) follows from the injectivity with `e^{-iA} = (e^{iA})⁻¹`
and `ue^{iA}u⁻¹ = e^{iAd_u A}`, `‖Ad_u A‖ = ‖A‖` (`log_inv`, `log_conj`).
-/
import CoreLean.ChartBounds
import CoreLean.Algebra
import BakerCampbellHausdorff.ExpBounds

open NormedSpace Matrix Polynomial
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace ChartBounds

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

lemma aeval_diagonal (d : Fin N → ℂ) (p : ℂ[X]) :
    aeval (diagonal d : Mat) p = diagonal (fun k => p.eval (d k)) := by
  have h := aeval_algHom_apply (diagonalAlgHom ℂ (n := Fin N) (α := ℂ)) d p
  have e1 : (diagonalAlgHom ℂ d : Mat) = diagonal d := rfl
  rw [e1] at h
  rw [h, aeval_pi_apply]
  rfl

lemma commute_aeval {a b : Mat} (h : Commute a b) (p : ℂ[X]) : Commute a (aeval b p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c a).mul_right (h.pow_right n)

/-- The spectral form of `e^{iX}` for a Hermitean `X`. -/
lemma exp_I_spectral {X : Mat} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Mat) * diagonal (fun k => (hX.eigenvalues k : ℂ)) *
        star (hX.eigenvectorUnitary : Mat) ∧
      exp (Complex.I • X) = (hX.eigenvectorUnitary : Mat) *
        diagonal (fun k => Complex.exp (Complex.I * hX.eigenvalues k)) *
        star (hX.eigenvectorUnitary : Mat) := by
  set U : Mat := (hX.eigenvectorUnitary : Mat)
  have hU : U ∈ unitaryGroup (Fin N) ℂ := hX.eigenvectorUnitary.2
  set l : Fin N → ℝ := hX.eigenvalues
  set d : Fin N → ℂ := fun k => (l k : ℂ)
  have hspec : X = U * diagonal d * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  refine ⟨hspec, ?_⟩
  have h1 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  have h2 : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  set W : Mat ˣ := ⟨U, star U, h1, h2⟩
  have e1 : Complex.I • X = (W : Mat) * diagonal (Complex.I • d) * ((W⁻¹ : Mat ˣ) : Mat) := by
    rw [hspec]; simp only [W, Units.inv_mk, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, Matrix.exp_units_conj, Matrix.exp_diagonal]
  have e2 : (exp (Complex.I • d) : Fin N → ℂ) = fun k => Complex.exp (Complex.I * l k) := by
    funext k
    simp only [Pi.exp_def]
    rw [← Complex.exp_eq_exp_ℂ]
    simp [d]
  rw [e2]
  rfl

lemma eigenvalue_abs_le {X : Mat} (hX : X.IsHermitian) (k : Fin N) : |hX.eigenvalues k| ≤ ‖X‖ := by
  obtain ⟨hspec, -⟩ := exp_I_spectral hX
  have hU : (hX.eigenvectorUnitary : Mat) ∈ unitaryGroup (Fin N) ℂ := hX.eigenvectorUnitary.2
  have hUs := Unitary.star_mem hU
  have hn : ‖X‖ = ‖(diagonal (fun k => (hX.eigenvalues k : ℂ)) : Mat)‖ := by
    conv_lhs => rw [hspec]
    rw [opNorm_unitary_mul _ _ _ hU hUs]
  rw [hn, l2_opNorm_diagonal]
  have := norm_le_pi_norm (fun k => (hX.eigenvalues k : ℂ)) k
  simpa using this

/-- `A = p(e^{iA})` for a Hermitean `A` with `‖A‖ < π`, with a polynomial `p`. -/
theorem eq_aeval_exp {A : Mat} (hA : A.IsHermitian) (hAn : ‖A‖ < Real.pi) :
    ∃ p : ℂ[X], aeval (exp (Complex.I • A)) p = A := by
  obtain ⟨hspec, hexp⟩ := exp_I_spectral hA
  set l : Fin N → ℝ := hA.eigenvalues
  set s : Finset ℂ := Finset.univ.image fun k => Complex.exp (Complex.I * l k)
  set p : ℂ[X] := Lagrange.interpolate s id (fun z => (Complex.arg z : ℂ))
  refine ⟨p, ?_⟩
  have hnode : ∀ k, p.eval (Complex.exp (Complex.I * l k)) = (l k : ℂ) := fun k => by
    have hmem : Complex.exp (Complex.I * l k) ∈ s := Finset.mem_image_of_mem _ (Finset.mem_univ k)
    have := Lagrange.eval_interpolate_at_node (fun z => (Complex.arg z : ℂ)) (Set.injOn_id _) hmem
    simp only [id] at this
    rw [this]
    have hl := (abs_lt.mp (lt_of_le_of_lt (eigenvalue_abs_le hA k) hAn))
    rw [mul_comm, Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I ⟨hl.1, hl.2.le⟩]
  set U : Mat := (hA.eigenvectorUnitary : Mat)
  set φ := Unitary.conjStarAlgAut ℂ Mat hA.eigenvectorUnitary
  have hφ : ∀ M : Mat, φ M = U * M * star U := fun M => Unitary.conjStarAlgAut_apply _ _
  rw [hexp, ← hφ, aeval_algHom_apply φ, hφ, aeval_diagonal,
    show (fun k => p.eval (Complex.exp (Complex.I * l k))) = fun k => (l k : ℂ) from funext hnode]
  exact hspec.symm

/-- A Hermitean matrix `C` with `‖C‖ < 2π` and `e^{iC} = 1` vanishes. -/
theorem eq_zero_of_exp_I_eq_one {C : Mat} (hC : C.IsHermitian) (hCn : ‖C‖ < 2 * Real.pi)
    (h : exp (Complex.I • C) = 1) : C = 0 := by
  obtain ⟨hspec, hexp⟩ := exp_I_spectral hC
  set U : Mat := (hC.eigenvectorUnitary : Mat)
  have hU : U ∈ unitaryGroup (Fin N) ℂ := hC.eigenvectorUnitary.2
  have h1 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  have h2 : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  have hdiag : diagonal (fun k => Complex.exp (Complex.I * hC.eigenvalues k)) = (1 : Mat) := by
    have := congrArg (fun M => star U * M * U) (hexp.symm.trans h)
    rw [← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, h2, mul_one, mul_one, h2] at this
    exact this
  have hev : ∀ k, hC.eigenvalues k = 0 := fun k => by
    have hk := congrFun (congrFun hdiag k) k
    simp only [diagonal_apply_eq, one_apply_eq] at hk
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hk
    have hre : (hC.eigenvalues k : ℝ) = m * (2 * Real.pi) := by
      have := congrArg Complex.im hm
      simp at this
      linarith
    have hbound := lt_of_le_of_lt (eigenvalue_abs_le hC k) hCn
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbound
    have hm1 : |(m : ℝ)| < 1 := by
      have hp : 0 < 2 * Real.pi := by positivity
      nlinarith
    have hm0 : m = 0 := by
      have : |m| < 1 := by exact_mod_cast hm1
      exact Int.abs_lt_one_iff.mp this
    rw [hre, hm0]; simp
  rw [hspec]
  have : (fun k => (hC.eigenvalues k : ℂ)) = 0 := by funext k; simp [hev k]
  rw [this]; simp

/-- `lem:chart`(i): `A ↦ e^{iA}` is injective on the Hermitean matrices of norm less than `π`. -/
theorem exp_I_injOn {A B : Mat} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAn : ‖A‖ < Real.pi)
    (hBn : ‖B‖ < Real.pi) (h : exp (Complex.I • A) = exp (Complex.I • B)) : A = B := by
  obtain ⟨p, hp⟩ := eq_aeval_exp hA hAn
  have hcB : Commute B (exp (Complex.I • A)) := by
    rw [h]
    exact ((Commute.refl B).smul_right Complex.I).exp_right
  have hAB : Commute A B := by
    have := commute_aeval hcB p
    rw [hp] at this
    exact this.symm
  have hiAB : Commute (Complex.I • A) (-(Complex.I • B)) :=
    ((hAB.smul_left Complex.I).smul_right Complex.I).neg_right
  have hexp : exp (Complex.I • (A - B)) = 1 := by
    rw [smul_sub, sub_eq_add_neg, BakerCampbellHausdorff.exp_add_of_commute' ℂ hiAB, h,
      BakerCampbellHausdorff.exp_mul_exp_neg ℂ]
  have hC : (A - B).IsHermitian := hA.sub hB
  have hCn : ‖A - B‖ < 2 * Real.pi := by
    have := norm_sub_le A B; linarith
  exact sub_eq_zero.mp (eq_zero_of_exp_I_eq_one hC hCn hexp)

/-- `lem:chart`(i), the invariance of the domain: for `A ∈ 𝔤` with `‖A‖ < π` and `u ∈ G`, the matrices
`-A` and `Ad_u A` lie in `𝔤`, have norms less than `π`, and `e^{-iA} = (e^{iA})⁻¹`,
`e^{iAd_u A} = ue^{iA}u⁻¹`; with `exp_I_injOn` this gives `log W⁻¹ = -log W` and
`log(uWu⁻¹) = Ad_u log W`. -/
theorem chart_domain {G : GaugeGroup N} {u : (Matrix (Fin N) (Fin N) ℂ)ˣ} (hu : u ∈ G.carrier)
    {A : Mat} (hA : A ∈ G.lie) (hAn : ‖A‖ < Real.pi) :
    (-A ∈ G.lie ∧ ‖-A‖ < Real.pi ∧ exp (Complex.I • -A) * exp (Complex.I • A) = 1) ∧
      (Ad u A ∈ G.lie ∧ ‖Ad u A‖ < Real.pi ∧
        exp (Complex.I • Ad u A) = (u : Mat) * exp (Complex.I • A) * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Mat)) := by
  refine ⟨⟨G.neg_mem_lie hA, by rwa [norm_neg], ?_⟩, ⟨GaugeGroup.Ad_mem_lie hu hA,
    by rwa [GaugeGroup.opNorm_Ad hu], ?_⟩⟩
  · rw [smul_neg]; exact BakerCampbellHausdorff.exp_neg_mul_exp ℂ _
  · have := congrArg (fun W : (Matrix (Fin N) (Fin N) ℂ)ˣ => (W : Mat)) (expU_conj u (Complex.I • A))
    simp only [Units.val_mul] at this
    rw [← Ad_smul]
    exact this.symm

/-- `lem:chart`(i): the chart is well defined, `e^{iA} = e^{iB}` with `A, B ∈ 𝔤` of norms less than
`π` implies `A = B`. -/
theorem chart_well_defined {G : GaugeGroup N} {A B : Mat} (hA : A ∈ G.lie) (hB : B ∈ G.lie)
    (hAn : ‖A‖ < Real.pi) (hBn : ‖B‖ < Real.pi)
    (h : exp (Complex.I • A) = exp (Complex.I • B)) : A = B :=
  exp_I_injOn hA.1 hB.1 hAn hBn h

end ChartBounds
end CoreLean

end
