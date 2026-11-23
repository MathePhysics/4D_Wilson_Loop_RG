/-
`lem:functional` and `lem:potential-gradients` of BALABAN_CORE.tex, the algebra of the potentials.

The objects of `def:landau-operators` and `prop:linearising` enter as data: a finite-dimensional space `Fb` of
functions on the bonds of the layers, a linear map `H : Fb → Ω¹` with values in the `𝔤^c`-valued forms, functions
`𝖣`, `𝖢⁽²⁾`, `𝖣₃` of the `1`-form with `𝖣 = 𝖢⁽²⁾ + 𝖣₃`, and `Δ⁽²⁾` with `⟨A', Δ⁽²⁾A'⟩ = 2⟨H𝖢⁽²⁾(A'), 𝐉⟩`.
`Vpot Δ` is `eq:potential` with the operator `Δ` (`𝖵` for `Δ = Δ(𝐔)`, `𝖵_π` for `Δ = Δ_π`).

* `functional` is `eq:functional`, from the definition of `𝖵₀`, the linearity of `Δ(𝐔)` and its symmetry on the
  `𝔤^c`-valued forms (`pair1_hessOp_symm`).
* `potential_difference` is `eq:potential-difference` with the sign which the definitions give:
  `𝖵 - 𝖵_π = -⟨A', Δ'_πH𝖣⟩ + ½⟨H𝖣, Δ'_πH𝖣⟩` for `Δ_π = Δ(𝐔) - Δ'_π`; the core prints the opposite sign
  (FINDINGS F204; the identity is used only where both sides vanish).
* `hasDerivAt_Vpot` is `eq:potential-gradients` before the transposes are named: for a symmetric linear `Δ`,
  `d/dt 𝖵(A' + tδ)|₀ = ⟨δ, 𝖭₀(A) - ΔH𝖣⟩ - ⟨H𝔡, 𝖭₀(A) + ΔA⟩ - ⟨H𝔡₃, 𝐉⟩`, `A = T(A')`, with `𝔡`, `𝔡₃` the
  derivatives of `𝖣`, `𝖣₃` along `δ`; the definition of the transposes `𝔇(A')ᵀHᵀ`, `𝔇₃(A')ᵀHᵀ` turns the last two
  terms into `⟨δ, ·⟩`.
* `hessian_minimiser` is `eq:hessian-minimiser`, from `Δ(𝐔) = Δ_𝖺 - DRD^* - Q^*𝖺Q` and
  `(Δ_𝖺 - Δ'_π)H = Q^*(QG_πQ^*)^{-1}`.
-/
import CoreLean.CubicCauchy

open Matrix Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable {G : GaugeGroup N}

lemma pair1_sub_left (X Y F : Form1 N n) : pair1 a (X - Y) F = pair1 a X F - pair1 a Y F := by
  simp only [pair1, pair0, Pi.sub_apply, sub_mul, ntr_sub, mul_sub, Finset.sum_sub_distrib]

/-- `Δ(𝐔)` is symmetric on the `𝔤^c`-valued forms. -/
lemma pair1_hessOp_symm [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) {X Y : Form1 N n}
    (hX : ∀ μ x, X μ x ∈ G.lieC) (hY : ∀ μ x, Y μ x ∈ G.lieC) :
    pair1 a X (hessOp a hG U Y) = pair1 a Y (hessOp a hG U X) := by
  rw [pair1_hessOp_eq a hG ha U Y hX, pair1_hessOp_eq a hG ha U X hY, pair2_comm, hessBil_comm]

/-- The pairing `⟨·, ·⟩` as a continuous bilinear map. -/
def pairL : Form1 N n →L[ℂ] Form1 N n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Form1 N n →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Form1 N n →L[ℂ] ℂ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℂ (pair1 a) (pair1_add_left a)
        (fun c X F => by rw [pair1_smul_left, smul_eq_mul]) (pair1_add_right a)
        (fun c X F => by rw [pair1_smul_right, smul_eq_mul]))

lemma pairL_apply (X F : Form1 N n) : pairL a X F = pair1 a X F := rfl

section Potential

variable {Fb : Type*} [AddCommGroup Fb] [Module ℂ Fb]

/-- `eq:potential` with the operator `Δ`: `-⟨H𝖣₃(A'), 𝐉⟩ - ⟨A', ΔH𝖣(A')⟩ + ½⟨H𝖣(A'), ΔH𝖣(A')⟩ + 𝖵₀(T(A'))`,
`T(A') = A' - H𝖣(A')`. -/
def Vpot [NeZero N] (hG : G.LieInput) (U : Config N n) (J : Form1 N n) (H : Fb →ₗ[ℂ] Form1 N n)
    (D D₃ : Form1 N n → Fb) (Δ : Form1 N n → Form1 N n) (A' : Form1 N n) : ℂ :=
  -pair1 a (H (D₃ A')) J - pair1 a A' (Δ (H (D A'))) + 1 / 2 * pair1 a (H (D A')) (Δ (H (D A'))) +
    V0 a hG U (A' - H (D A'))

/-- `eq:functional`: with `A = T(A')`,
`A(e^{iηA}𝐔) + ⟨A, 𝐉 - J(𝐔)⟩ = A(𝐔) + ⟨A', 𝐉⟩ + ½⟨A', (Δ(𝐔) - Δ⁽²⁾)A'⟩ + 𝖵(A')`. -/
theorem functional [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (U : Config N n) (J : Form1 N n)
    (H : Fb →ₗ[ℂ] Form1 N n) (hH : ∀ ν, H ν ∈ lieForms hG) (D C₂ D₃ : Form1 N n → Fb)
    (hD : ∀ A', D A' = C₂ A' + D₃ A') (Δ₂ : Form1 N n → Form1 N n)
    (hΔ₂ : ∀ A', pair1 a A' (Δ₂ A') = 2 * pair1 a (H (C₂ A')) J) {A' : Form1 N n}
    (hA' : A' ∈ lieForms hG) :
    action (expMul a (A' - H (D A')) U) + pair1 a (A' - H (D A')) (J - current a hG U) =
      action U + pair1 a A' J + 1 / 2 * pair1 a A' (hessOp a hG U A' - Δ₂ A') +
        Vpot a hG U J H D D₃ (hessOp a hG U) A' := by
  set B := H (D A') with hB
  have hBm : B ∈ lieForms hG := hH _
  have hlin : hessOp a hG U (A' - B) = hessOp a hG U A' - hessOp a hG U B :=
    (hessLin a hG ha U).map_sub A' B
  have hsym : pair1 a B (hessOp a hG U A') = pair1 a A' (hessOp a hG U B) :=
    pair1_hessOp_symm a hG ha U hBm hA'
  have hBJ : pair1 a B J = pair1 a (H (C₂ A')) J + pair1 a (H (D₃ A')) J := by
    rw [hB, hD, map_add, pair1_add_left]
  have h2 := hΔ₂ A'
  simp only [Vpot, V0, ← hB, pair1_sub_right, pair1_sub_left, hlin]
  rw [hsym] at *
  linear_combination -hBJ + (1 / 2 : ℂ) * h2

/-- `eq:potential-difference`, with the sign which the definitions give: for `Δ_π = Δ(𝐔) - Δ'_π`,
`𝖵(A') - 𝖵_π(A') = -⟨A', Δ'_πH𝖣(A')⟩ + ½⟨H𝖣(A'), Δ'_πH𝖣(A')⟩`. -/
theorem potential_difference [NeZero N] (hG : G.LieInput) (U : Config N n) (J : Form1 N n)
    (H : Fb →ₗ[ℂ] Form1 N n) (D D₃ : Form1 N n → Fb) (Δπ Δ'π : Form1 N n → Form1 N n)
    (hπ : ∀ X, Δπ X = hessOp a hG U X - Δ'π X) (A' : Form1 N n) :
    Vpot a hG U J H D D₃ (hessOp a hG U) A' - Vpot a hG U J H D D₃ Δπ A' =
      -pair1 a A' (Δ'π (H (D A'))) + 1 / 2 * pair1 a (H (D A')) (Δ'π (H (D A'))) := by
  simp only [Vpot, hπ, pair1_sub_right]
  ring

end Potential

section Gradient

variable {Fb : Type*} [NormedAddCommGroup Fb] [NormedSpace ℂ Fb] [FiniteDimensional ℂ Fb]

set_option maxHeartbeats 1000000 in
/-- `eq:potential-gradients` before the transposes are named. For a linear `Δ` which is symmetric on the
`𝔤^c`-valued forms (`Δ(𝐔)`, or `Δ_π`), `A' + tδ` with `𝔤^c`-valued `A'`, `δ`, and the derivatives `𝔡`, `𝔡₃` of
`t ↦ 𝖣(A' + tδ)`, `t ↦ 𝖣₃(A' + tδ)` at `0`: with `A = T(A')`,
`d/dt 𝖵(A' + tδ)|₀ = ⟨δ, 𝖭₀(A) - ΔH𝖣(A')⟩ - ⟨H𝔡, 𝖭₀(A) + ΔA⟩ - ⟨H𝔡₃, 𝐉⟩`. -/
theorem hasDerivAt_Vpot [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) (J : Form1 N n) (H : Fb →ₗ[ℂ] Form1 N n)
    (hH : ∀ ν, H ν ∈ lieForms hG) (D D₃ : Form1 N n → Fb) (Δ : Form1 N n →ₗ[ℂ] Form1 N n)
    (hsym : ∀ X ∈ lieForms hG, ∀ Y ∈ lieForms hG, pair1 a X (Δ Y) = pair1 a Y (Δ X))
    {A' δ : Form1 N n} (hA' : A' ∈ lieForms hG) (hδ : δ ∈ lieForms hG) {d d₃ : Fb}
    (hd : HasDerivAt (fun t : ℂ => D (A' + t • δ)) d 0)
    (hd₃ : HasDerivAt (fun t : ℂ => D₃ (A' + t • δ)) d₃ 0) :
    HasDerivAt (fun t : ℂ => Vpot a hG U J H D D₃ Δ (A' + t • δ))
      (pair1 a δ (N0 a hG U (A' - H (D A')) - Δ (H (D A'))) -
        pair1 a (H d) (N0 a hG U (A' - H (D A')) + Δ (A' - H (D A'))) - pair1 a (H d₃) J) 0 := by
  have hAm : A' - H (D A') ∈ lieForms hG := (lieForms hG).sub_mem hA' (hH _)
  have h0 : A' + (0 : ℂ) • δ = A' := by rw [zero_smul, add_zero]
  -- the derivatives of the pieces
  have hl : HasDerivAt (fun t : ℂ => A' + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const δ).const_add A'
  have hHD : HasDerivAt (fun t : ℂ => H (D (A' + t • δ))) (H d) 0 :=
    (LinearMap.toContinuousLinearMap H).hasFDerivAt.comp_hasDerivAt 0 hd
  have hHD₃ : HasDerivAt (fun t : ℂ => H (D₃ (A' + t • δ))) (H d₃) 0 :=
    (LinearMap.toContinuousLinearMap H).hasFDerivAt.comp_hasDerivAt 0 hd₃
  have hΔHD : HasDerivAt (fun t : ℂ => Δ (H (D (A' + t • δ)))) (Δ (H d)) 0 :=
    (LinearMap.toContinuousLinearMap Δ).hasFDerivAt.comp_hasDerivAt 0 hHD
  have f1 : HasDerivAt (fun t : ℂ => pair1 a (H (D₃ (A' + t • δ))) J) (pair1 a (H d₃) J) 0 := by
    refine ((pairL a).hasDerivAt_of_bilinear (fun _ => hHD₃)
      (fun _ => hasDerivAt_const (0 : ℂ) J)).congr_deriv ?_
    simp only [pairL_apply, h0, pair1_zero_right, zero_add]
  have f2 : HasDerivAt (fun t : ℂ => pair1 a (A' + t • δ) (Δ (H (D (A' + t • δ)))))
      (pair1 a A' (Δ (H d)) + pair1 a δ (Δ (H (D A')))) 0 := by
    refine ((pairL a).hasDerivAt_of_bilinear (fun _ => hl) (fun _ => hΔHD)).congr_deriv ?_
    simp only [pairL_apply, h0]
  have f3 : HasDerivAt (fun t : ℂ => 1 / 2 * pair1 a (H (D (A' + t • δ))) (Δ (H (D (A' + t • δ)))))
      (1 / 2 * (pair1 a (H (D A')) (Δ (H d)) + pair1 a (H d) (Δ (H (D A'))))) 0 := by
    refine (((pairL a).hasDerivAt_of_bilinear (fun _ => hHD) (fun _ => hΔHD)).const_mul
      (1 / 2 : ℂ)).congr_deriv ?_
    simp only [pairL_apply, h0]
  -- `𝖵₀ ∘ T`: the derivative of `T` is `ε = δ - H𝔡`, and `D𝖵₀(A)ε = ⟨ε, 𝖭₀(A)⟩`
  have hT : HasDerivAt (fun t : ℂ => A' + t • δ - H (D (A' + t • δ))) (δ - H d) 0 := hl.sub hHD
  have hεm : δ - H d ∈ lieForms hG := (lieForms hG).sub_mem hδ (hH _)
  have f4 : HasDerivAt (fun t : ℂ => V0 a hG U (A' + t • δ - H (D (A' + t • δ))))
      (pair1 a (δ - H d) (N0 a hG U (A' - H (D A')))) 0 := by
    have hc := (analyticAt_V0 a hG ha U (A' + (0 : ℂ) • δ - H (D (A' + (0 : ℂ) • δ)))).differentiableAt
      |>.hasFDerivAt.comp_hasDerivAt 0 hT
    rw [h0] at hc
    refine hc.congr_deriv ?_
    have h1 := hasDerivAt_V0 a hG ha hU hAm hεm
    have hl' : HasDerivAt (fun s : ℂ => (A' - H (D A')) + s • (δ - H d)) (δ - H d) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (δ - H d)).const_add (A' - H (D A'))
    have h2 := (analyticAt_V0 a hG ha U ((A' - H (D A')) + (0 : ℂ) • (δ - H d))).differentiableAt
      |>.hasFDerivAt.comp_hasDerivAt 0 hl'
    rw [zero_smul, add_zero] at h2
    exact h2.unique h1
  have h := ((f1.neg.sub f2).add f3).add f4
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · -- the symmetry of `Δ` and `ΔA = ΔA' - ΔH𝖣`
    have s1 : pair1 a A' (Δ (H d)) = pair1 a (H d) (Δ A') := hsym _ hA' _ (hH _)
    have s2 : pair1 a (H (D A')) (Δ (H d)) = pair1 a (H d) (Δ (H (D A'))) := hsym _ (hH _) _ (hH _)
    simp only [map_sub, pair1_sub_right, pair1_add_right, pair1_sub_left]
    rw [s1, s2]
    ring
  · show _ = _
    simp only [Vpot, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]

/-- `eq:potential-gradients`, the first line before the transposes: `Δ = Δ(𝐔)`. -/
theorem hasDerivAt_Vpot_hess [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) {U : Config N n}
    (hU : ∀ μ x, U μ x ∈ G.complexified) (J : Form1 N n) (H : Fb →ₗ[ℂ] Form1 N n)
    (hH : ∀ ν, H ν ∈ lieForms hG) (D D₃ : Form1 N n → Fb)
    {A' δ : Form1 N n} (hA' : A' ∈ lieForms hG) (hδ : δ ∈ lieForms hG) {d d₃ : Fb}
    (hd : HasDerivAt (fun t : ℂ => D (A' + t • δ)) d 0)
    (hd₃ : HasDerivAt (fun t : ℂ => D₃ (A' + t • δ)) d₃ 0) :
    HasDerivAt (fun t : ℂ => Vpot a hG U J H D D₃ (hessOp a hG U) (A' + t • δ))
      (pair1 a δ (N0 a hG U (A' - H (D A')) - hessOp a hG U (H (D A'))) -
        pair1 a (H d) (N0 a hG U (A' - H (D A')) + hessOp a hG U (A' - H (D A'))) -
          pair1 a (H d₃) J) 0 :=
  hasDerivAt_Vpot a hG ha hU J H hH D D₃ (hessLin a hG ha U)
    (fun _ hX _ hY => pair1_hessOp_symm a hG ha U hX hY) hA' hδ hd hd₃

end Gradient

/-- `eq:hessian-minimiser` as operator algebra: from `Δ(𝐔) = Δ_𝖺 - DRD^* - Q^*𝖺Q` (`def:operators`(iv)) and
`(Δ_𝖺 - Δ'_π)H = Q^*(QG_πQ^*)^{-1}` (`def:landau-operators`(ii)),
`Δ(𝐔)H = Q^*(QG_πQ^*)^{-1} + Δ'_πH - DRD^*H - Q^*𝖺QH`. -/
theorem hessian_minimiser {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (Δ Δa Δ'π K₁ K₂ : E →ₗ[ℂ] E) (H W : F →ₗ[ℂ] E) (hΔ : Δ = Δa - K₁ - K₂)
    (hH : (Δa - Δ'π) ∘ₗ H = W) :
    Δ ∘ₗ H = W + Δ'π ∘ₗ H - K₁ ∘ₗ H - K₂ ∘ₗ H := by
  rw [hΔ, ← hH]
  ext ν
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply]
  abel

/-! ### The third statement of `lem:functional` -/

lemma pair1_zero_left (F : Form1 N n) : pair1 a 0 F = 0 := by
  simp [pair1, pair0, ntr]

/-- The gauge defect `X(A)` of `eq:gauge-defect` for the gauge function `λ`:
`X(A)(b) = i[λ(b₋), A(b)] - i[A(b), Ad_{𝐔(b)}λ(b₊)] - i[λ(b₋), (Dλ)(b)]` on the positive bonds `b`. -/
def gaugeDefect (U : Config N n) (l : Form0 N n) (A : Form1 N n) : Form1 N n :=
  fun μ x => I • brk (l x) (A μ x) - I • brk (A μ x) (Ad (U μ x) (l (x + unit n μ))) -
    I • brk (l x) (D0 a U l μ x)

/-- Every term of `X(A)` contains the gauge function: `X(A) = 0` when `λ = 0`. -/
lemma gaugeDefect_zero (U : Config N n) (A : Form1 N n) : gaugeDefect a U 0 A = 0 := by
  funext μ x
  simp [gaugeDefect, brk, Ad, D0, Dfw]

/-- The bilinear form of `Δ'_π` vanishes on two `𝔤^c`-valued forms whose gauge functions vanish: for a linear
`Δ'_π`, symmetric on these forms, with `⟨A, Δ'_πA⟩ = ⟨X(A), 𝐉⟩` (`def:landau-operators`(i)), `λ_A = ΛA`. -/
theorem landau_form_vanishes (hG : G.LieInput) (U : Config N n) (J : Form1 N n)
    (Λ : Form1 N n →ₗ[ℂ] Form0 N n) (Δ'π : Form1 N n →ₗ[ℂ] Form1 N n)
    (hΔ : ∀ A ∈ lieForms hG, pair1 a A (Δ'π A) = pair1 a (gaugeDefect a U (Λ A) A) J)
    (hsym : ∀ X ∈ lieForms hG, ∀ Y ∈ lieForms hG, pair1 a X (Δ'π Y) = pair1 a Y (Δ'π X))
    {A B : Form1 N n} (hA : A ∈ lieForms hG) (hB : B ∈ lieForms hG) (hΛA : Λ A = 0) (hΛB : Λ B = 0) :
    pair1 a A (Δ'π B) = 0 := by
  have hAB := hΔ (A + B) ((lieForms hG).add_mem hA hB)
  rw [show Λ (A + B) = 0 by rw [map_add, hΛA, hΛB, add_zero], gaugeDefect_zero, pair1_zero_left,
    map_add, pair1_add_left,
    pair1_add_right, pair1_add_right] at hAB
  have h1 := hΔ A hA
  have h2 := hΔ B hB
  rw [hΛA, gaugeDefect_zero, pair1_zero_left] at h1
  rw [hΛB, gaugeDefect_zero, pair1_zero_left] at h2
  have hs := hsym B hB A hA
  linear_combination (1 / 2 : ℂ) * hAB - (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2 - (1 / 2 : ℂ) * hs

/-- The third statement of `lem:functional`. Let `RD^*` be a linear map `K` with `KH = 0`
(`thm:landau-operators`(iv)), `λ_A = G'KA`, and `𝒫A = A - Dλ_A` with a transpose `𝒫ᵀ`. If `KA' = 0`, then
`KT(A') = 0`, the right side of `eq:potential-difference` vanishes, and `⟨A', Δ⁽²⁾A'⟩ = ⟨A', Δ⁽²⁾_πA'⟩` for
`Δ⁽²⁾_π = 𝒫ᵀΔ⁽²⁾𝒫`. -/
theorem functional_landau {Fb : Type*} [AddCommGroup Fb] [Module ℂ Fb] (hG : G.LieInput)
    (U : Config N n) (J : Form1 N n) (H : Fb →ₗ[ℂ] Form1 N n) (hH : ∀ ν, H ν ∈ lieForms hG)
    (K : Form1 N n →ₗ[ℂ] Form0 N n) (hKH : ∀ ν, K (H ν) = 0) (G' : Form0 N n →ₗ[ℂ] Form0 N n)
    (Δ'π : Form1 N n →ₗ[ℂ] Form1 N n)
    (hΔ : ∀ A ∈ lieForms hG, pair1 a A (Δ'π A) = pair1 a (gaugeDefect a U (G' (K A)) A) J)
    (hsym : ∀ X ∈ lieForms hG, ∀ Y ∈ lieForms hG, pair1 a X (Δ'π Y) = pair1 a Y (Δ'π X))
    (Δ₂ Pt : Form1 N n → Form1 N n)
    (hPt : ∀ X Y, pair1 a X (Pt Y) = pair1 a (X - D0 a U (G' (K X))) Y)
    (D : Form1 N n → Fb) {A' : Form1 N n} (hA' : A' ∈ lieForms hG) (hKA' : K A' = 0) :
    K (A' - H (D A')) = 0 ∧
      -pair1 a A' (Δ'π (H (D A'))) + 1 / 2 * pair1 a (H (D A')) (Δ'π (H (D A'))) = 0 ∧
      pair1 a A' (Δ₂ A') = pair1 a A' (Pt (Δ₂ (A' - D0 a U (G' (K A'))))) := by
  have hΛ : (G' ∘ₗ K) A' = 0 := by simp [hKA']
  have hΛH : (G' ∘ₗ K) (H (D A')) = 0 := by simp [hKH]
  have hD0 : D0 a U (0 : Form0 N n) = 0 := by funext μ x; simp [D0, Dfw, Ad]
  refine ⟨by rw [map_sub, hKA', hKH, sub_zero], ?_, ?_⟩
  · have h1 := landau_form_vanishes a hG U J (G' ∘ₗ K) Δ'π hΔ hsym hA' (hH _) hΛ hΛH
    have h2 := landau_form_vanishes a hG U J (G' ∘ₗ K) Δ'π hΔ hsym (hH _) (hH _) hΛH hΛH
    rw [h1, h2]; ring
  · rw [hPt, hKA', map_zero, hD0, sub_zero]

end CoreLean
