/-
`lem:axial-smallness` of BALABAN_CORE.tex (`a7d5e1f955b0`), in abstract form: the algebra of unitary
matrices and the arithmetic of the constants. The geometric decompositions of the proof (the strips
`W(b) = W(τ_w)⁻¹S_b(W)W(τ_{w+ae_ρ})`, the path `τ^{c₋}_z = R_z(W)W([c])W(Γ_z)`, `W([c]) = e^{-iβ_c(W)}M(W)(c)`)
and the bounds of their factors (non-abelian Stokes, `lem:average`(v), `lem:chart`(iii), `lem:group-mean`)
are hypotheses.

* The two facts of the proof: `‖W⁻¹ - 1‖ = ‖W - 1‖` (`norm_star_sub_one`), `‖XY⁻¹ - 1‖ = ‖X - Y‖`
  (`norm_mul_star_sub_one`), `‖gXg⁻¹ - 1‖ = ‖X - 1‖` (`norm_conj_sub_one`), and the product bound
  `norm_prod_sub_one_le` of `ChartAverage.lean`.
* `axial_path_difference` (`eq:axial-path-difference`), `mean_path_bound` (the bound `κ = 10√N` of
  `eq:axial-path-transport` for the rule `m`), `bond_reduction` (`eq:axial-bond-reduction`),
  `between_blocks` (the bound of `D^{c₋}(z)`).
* `axial_smallness_one_block`, `axial_smallness_between`: `‖V(b)V₀(b)⁻¹ - 1‖ ≤ C_ax α₀ + α₁`,
  `C_ax = 59√N`, for `κ ≤ 10√N`.
-/
import CoreLean.ChartAverage

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AxialSmallness

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "UG" => unitaryGroup (Fin N) ℂ

lemma star_mul_self {U : Mat} (hU : U ∈ UG) : star U * U = 1 := (mem_unitaryGroup_iff').1 hU

lemma mul_star_self {U : Mat} (hU : U ∈ UG) : U * star U = 1 := (mem_unitaryGroup_iff).1 hU

/-- `‖U⁻¹ - 1‖ = ‖U - 1‖` for unitary `U` (`U⁻¹ = U^*`). -/
lemma norm_star_sub_one {U : Mat} (hU : U ∈ UG) : ‖star U - 1‖ = ‖U - 1‖ := by
  have e : star U - 1 = -(star U * (U - 1)) := by rw [mul_sub, star_mul_self hU, mul_one, neg_sub]
  rw [e, norm_neg]
  exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)

/-- `‖XY⁻¹ - 1‖ = ‖X - Y‖` for unitary `Y`. -/
lemma norm_mul_star_sub_one {X Y : Mat} (hY : Y ∈ UG) : ‖X * star Y - 1‖ = ‖X - Y‖ := by
  have e : X * star Y - 1 = (X - Y) * star Y := by rw [sub_mul, mul_star_self hY]
  rw [e]
  exact CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hY)

/-- `‖gXg⁻¹ - 1‖ = ‖X - 1‖` for unitary `g`. -/
lemma norm_conj_sub_one {g : Mat} (hg : g ∈ UG) (X : Mat) : ‖g * X * star g - 1‖ = ‖X - 1‖ := by
  have e : g * X * star g - 1 = g * (X - 1) * star g := by
    rw [mul_sub, sub_mul, mul_one, mul_star_self hg]
  rw [e, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hg)]
  exact CStarRing.norm_mem_unitary_mul _ hg

/-- `eq:axial-path-difference`: if `‖W(Γ_x) - W_𝔱(y, x)‖ ≤ κα₀` for `W = V, V₀` and the transports agree
(hypothesis (ii)), then `‖V(Γ_x)V₀(Γ_x)⁻¹ - 1‖ = ‖V(Γ_x) - V₀(Γ_x)‖ ≤ 2κα₀`. -/
theorem axial_path_difference {VΓ V0Γ Vt V0t : Mat} {b : ℝ} (hV0Γ : V0Γ ∈ UG) (ht : Vt = V0t)
    (hV : ‖VΓ - Vt‖ ≤ b) (hV0 : ‖V0Γ - V0t‖ ≤ b) : ‖VΓ * star V0Γ - 1‖ ≤ 2 * b := by
  rw [norm_mul_star_sub_one hV0Γ]
  calc ‖VΓ - V0Γ‖ = ‖(VΓ - Vt) - (V0Γ - V0t)‖ := by rw [ht]; congr 1; abel
    _ ≤ ‖VΓ - Vt‖ + ‖V0Γ - V0t‖ := norm_sub_le _ _
    _ ≤ 2 * b := by linarith

/-- `eq:axial-path-transport` for the rule `m`: if `W_m(y, x) = e^{iZ}W(Γ_x)` with `W(Γ_x)` unitary and
`‖Z‖ ≤ (3π/2)√Nα₀ ≤ 1` (`lem:group-mean`, `lem:chart`(ii)–(iii)), then `‖W_m(y, x) - W(Γ_x)‖ ≤ 10√Nα₀`. -/
theorem mean_path_bound {Wm WΓ Z : Mat} {α0 : ℝ} (hWΓ : WΓ ∈ UG)
    (hWm : Wm = exp (Complex.I • Z) * WΓ) (hZ : ‖Z‖ ≤ 3 * Real.pi / 2 * Real.sqrt N * α0)
    (h1 : 3 * Real.pi / 2 * Real.sqrt N * α0 ≤ 1) : ‖Wm - WΓ‖ ≤ 10 * Real.sqrt N * α0 := by
  have e : Wm - WΓ = (exp (Complex.I • Z) - 1) * WΓ := by rw [hWm, sub_mul, one_mul]
  rw [e, CStarRing.norm_mul_mem_unitary _ hWΓ]
  have hIZ : ‖Complex.I • Z‖ = ‖Z‖ := norm_I_smul' Z
  have hb := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Z)
  rw [hIZ] at hb
  have h2 := exp_sub_one_le_two_mul (norm_nonneg Z) hZ h1
  have hpi := Real.pi_lt_d2
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hα : 0 ≤ Real.sqrt N * α0 := by
    by_contra hneg
    rw [not_le] at hneg
    have : 3 * Real.pi / 2 * Real.sqrt N * α0 < 0 := by
      have := Real.pi_pos
      rw [mul_assoc]; exact mul_neg_of_pos_of_neg (by positivity) hneg
    linarith [norm_nonneg Z]
  have : 3 * Real.pi * (Real.sqrt N * α0) ≤ 10 * (Real.sqrt N * α0) := by nlinarith
  calc ‖exp (Complex.I • Z) - 1‖ ≤ 2 * (3 * Real.pi / 2 * Real.sqrt N * α0) := hb.trans h2
    _ = 3 * Real.pi * (Real.sqrt N * α0) := by ring
    _ ≤ 10 * Real.sqrt N * α0 := by linarith

/-- `eq:axial-bond-reduction`: if `V(b) = V(τ)⁻¹S V(τ')` and `V₀(b) = V₀(τ)⁻¹S₀V₀(τ')` with unitary
factors, then `‖V(b)V₀(b)⁻¹ - 1‖ ≤ D(w) + D(w') + ‖S - 1‖ + ‖S₀ - 1‖`, `D = ‖V(τ) - V₀(τ)‖`. -/
theorem bond_reduction {Vτ Vτ' V0τ V0τ' S S0 : Mat} (hVτ : Vτ ∈ UG) (hVτ' : Vτ' ∈ UG)
    (hV0τ : V0τ ∈ UG) (hV0τ' : V0τ' ∈ UG) (hS : S ∈ UG) (hS0 : S0 ∈ UG) :
    ‖(star Vτ * S * Vτ') * star (star V0τ * S0 * V0τ') - 1‖ ≤
      ‖Vτ - V0τ‖ + ‖Vτ' - V0τ'‖ + ‖S - 1‖ + ‖S0 - 1‖ := by
  -- conjugation by `V₀(τ)`
  have e : (star Vτ * S * Vτ') * star (star V0τ * S0 * V0τ') =
      star V0τ * (V0τ * star Vτ * (S * (Vτ' * star V0τ' * star S0))) * star (star V0τ) := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star V0τ) V0τ, star_mul_self hV0τ, one_mul]
  rw [e, norm_conj_sub_one (Unitary.star_mem hV0τ)]
  have hl : ∀ W ∈ [V0τ * star Vτ, S, Vτ' * star V0τ', star S0], W ∈ UG := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro W (rfl | rfl | rfl | rfl)
    · exact Submonoid.mul_mem _ hV0τ (Unitary.star_mem hVτ)
    · exact hS
    · exact Submonoid.mul_mem _ hVτ' (Unitary.star_mem hV0τ')
    · exact Unitary.star_mem hS0
  have hp := norm_prod_sub_one_le _ hl
  simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hp
  have e1 : ‖V0τ * star Vτ - 1‖ = ‖Vτ - V0τ‖ := by
    rw [norm_mul_star_sub_one hVτ, norm_sub_rev]
  rw [e1, norm_mul_star_sub_one hV0τ', norm_star_sub_one hS0] at hp
  linarith

/-- The bound of `D^{c₋}(z)` in the proof: if `V(τ) = R E M V(Γ)` and `V₀(τ) = R₀E₀M₀V₀(Γ)` with unitary
factors, then `‖V(τ) - V₀(τ)‖` is at most the sum of `‖R - 1‖`, `‖E - 1‖`, `‖MM₀⁻¹ - 1‖`,
`‖V(Γ) - V₀(Γ)‖`, `‖E₀ - 1‖`, `‖R₀ - 1‖`. -/
theorem between_blocks {R E M VΓ R0 E0 M0 V0Γ : Mat} (hR : R ∈ UG) (hE : E ∈ UG) (hM : M ∈ UG)
    (hVΓ : VΓ ∈ UG) (hR0 : R0 ∈ UG) (hE0 : E0 ∈ UG) (hM0 : M0 ∈ UG) (hV0Γ : V0Γ ∈ UG) :
    ‖R * E * M * VΓ - R0 * E0 * M0 * V0Γ‖ ≤
      ‖R - 1‖ + ‖E - 1‖ + ‖M * star M0 - 1‖ + ‖VΓ - V0Γ‖ + ‖E0 - 1‖ + ‖R0 - 1‖ := by
  have hV0 : R0 * E0 * M0 * V0Γ ∈ UG :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hR0 hE0) hM0) hV0Γ
  rw [← norm_mul_star_sub_one hV0]
  have hl : ∀ W ∈ [R, E, M * star M0, M0 * (VΓ * star V0Γ) * star M0, star E0, star R0], W ∈ UG := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro W (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hR
    · exact hE
    · exact Submonoid.mul_mem _ hM (Unitary.star_mem hM0)
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hM0
        (Submonoid.mul_mem _ hVΓ (Unitary.star_mem hV0Γ))) (Unitary.star_mem hM0)
    · exact Unitary.star_mem hE0
    · exact Unitary.star_mem hR0
  have hp := norm_prod_sub_one_le _ hl
  simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hp
  rw [norm_conj_sub_one hM0, norm_mul_star_sub_one hV0Γ, norm_star_sub_one hE0,
    norm_star_sub_one hR0] at hp
  have e : R * E * M * VΓ * star (R0 * E0 * M0 * V0Γ) =
      R * (E * (M * star M0 * (M0 * (VΓ * star V0Γ) * star M0 * (star E0 * star R0)))) := by
    simp only [star_mul, mul_assoc]
    rw [← mul_assoc (star M0) M0, star_mul_self hM0, one_mul]
  rw [e]
  linarith

/-- `lem:axial-smallness`, a bond in one block: `‖V(b)V₀(b)⁻¹ - 1‖ ≤ (4κ + 2√N)α₀ ≤ 59√Nα₀`, from
`eq:axial-path-difference` at both ends and `eq:axial-strip`, for `κ ≤ 10√N`. -/
theorem axial_smallness_one_block {Vτ Vτ' V0τ V0τ' S S0 : Mat} {κ α0 : ℝ} (hκ : κ ≤ 10 * Real.sqrt N)
    (hα0 : 0 ≤ α0) (hVτ : Vτ ∈ UG) (hVτ' : Vτ' ∈ UG) (hV0τ : V0τ ∈ UG) (hV0τ' : V0τ' ∈ UG)
    (hS : S ∈ UG) (hS0 : S0 ∈ UG) (hD : ‖Vτ - V0τ‖ ≤ 2 * κ * α0) (hD' : ‖Vτ' - V0τ'‖ ≤ 2 * κ * α0)
    (hSb : ‖S - 1‖ ≤ Real.sqrt N * α0) (hS0b : ‖S0 - 1‖ ≤ Real.sqrt N * α0) :
    ‖(star Vτ * S * Vτ') * star (star V0τ * S0 * V0τ') - 1‖ ≤ 59 * Real.sqrt N * α0 := by
  have h := bond_reduction hVτ hVτ' hV0τ hV0τ' hS hS0
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have : κ * α0 ≤ 10 * Real.sqrt N * α0 := mul_le_mul_of_nonneg_right hκ hα0
  nlinarith

/-- `lem:axial-smallness`, a bond between the blocks: with `D^{c₋}(w) ≤ 2κα₀` at the end in `B(c₋)` and, at
the end `z` in `B(c₊)`, `V(τ_z) = R_z(V)e^{-iβ_c(V)}M(V)(c)V(Γ_z)` and the same for `V₀`, where
`‖R_z - 1‖ ≤ (3/2)√Nα₀`, `‖e^{-iβ_c} - 1‖ ≤ 7√Nα₀`, `‖M(V)(c)M(V₀)(c)⁻¹ - 1‖ ≤ α₁` (hypothesis (iii)),
`‖V(Γ_z) - V₀(Γ_z)‖ ≤ 2κα₀`, and the strips are `≤ √Nα₀`:
`‖V(b)V₀(b)⁻¹ - 1‖ ≤ α₁ + (19√N + 4κ)α₀ ≤ α₁ + 59√Nα₀`. -/
theorem axial_smallness_between {Vτ V0τ S S0 R E M VΓ R0 E0 M0 V0Γ : Mat} {κ α0 α1 : ℝ}
    (hκ : κ ≤ 10 * Real.sqrt N) (hα0 : 0 ≤ α0)
    (hVτ : Vτ ∈ UG) (hV0τ : V0τ ∈ UG) (hS : S ∈ UG) (hS0 : S0 ∈ UG)
    (hR : R ∈ UG) (hE : E ∈ UG) (hM : M ∈ UG) (hVΓ : VΓ ∈ UG)
    (hR0 : R0 ∈ UG) (hE0 : E0 ∈ UG) (hM0 : M0 ∈ UG) (hV0Γ : V0Γ ∈ UG)
    (hD : ‖Vτ - V0τ‖ ≤ 2 * κ * α0)
    (hSb : ‖S - 1‖ ≤ Real.sqrt N * α0) (hS0b : ‖S0 - 1‖ ≤ Real.sqrt N * α0)
    (hRb : ‖R - 1‖ ≤ 3 / 2 * Real.sqrt N * α0) (hR0b : ‖R0 - 1‖ ≤ 3 / 2 * Real.sqrt N * α0)
    (hEb : ‖E - 1‖ ≤ 7 * Real.sqrt N * α0) (hE0b : ‖E0 - 1‖ ≤ 7 * Real.sqrt N * α0)
    (hMb : ‖M * star M0 - 1‖ ≤ α1) (hΓb : ‖VΓ - V0Γ‖ ≤ 2 * κ * α0) :
    ‖(star Vτ * S * (R * E * M * VΓ)) * star (star V0τ * S0 * (R0 * E0 * M0 * V0Γ)) - 1‖ ≤
      α1 + (19 * Real.sqrt N + 4 * κ) * α0 ∧
    α1 + (19 * Real.sqrt N + 4 * κ) * α0 ≤ α1 + 59 * Real.sqrt N * α0 := by
  have hτ : R * E * M * VΓ ∈ UG :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hR hE) hM) hVΓ
  have hτ0 : R0 * E0 * M0 * V0Γ ∈ UG :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hR0 hE0) hM0) hV0Γ
  have h := bond_reduction hVτ hτ hV0τ hτ0 hS hS0
  have hz := between_blocks hR hE hM hVΓ hR0 hE0 hM0 hV0Γ
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have : κ * α0 ≤ 10 * Real.sqrt N * α0 := mul_le_mul_of_nonneg_right hκ hα0
  constructor
  · nlinarith
  · nlinarith

end AxialSmallness

end CoreLean

end
