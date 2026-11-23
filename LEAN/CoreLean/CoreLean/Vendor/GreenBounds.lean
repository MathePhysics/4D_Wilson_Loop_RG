module

public import CoreLean.Vendor.TimeIntegrals

/-!
# Time-integrated bounds for products of one-dimensional heat-kernel differences

For `m : Fin d → ℕ` with `m μ ≤ 2` and `d ≥ 3`, the function `t ↦ ∏_μ Δ^{m_μ} q_t(x_μ)` is
integrable on `(0, ∞)` and its absolute integral is `≤ C (1 + ‖x‖)^{-(d + ∑ m - 2)}`.

Provenance: copied from `Balaban/Green/Lattice/GreenBounds.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit `493e9eb`, Apache License 2.0
(`LICENSE-balaban-lean`); the only change is the import path.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Set Filter Topology

variable {d : ℕ}

theorem abs_heatDiffProd_le_large (m : Fin d → ℕ) (hm : ∀ μ, m μ ≤ 2) {t : ℝ} (ht : 1 ≤ t)
    (x : Fin d → ℤ) (μ0 : Fin d) :
    |heatDiffProd d m t x| ≤
      5000 ^ d * 2 ^ d * invSqrtPow (d + ∑ μ, m μ) t * Elarge t (x μ0) := by
  have ht0 : 0 < t := by linarith
  unfold heatDiffProd
  rw [Finset.abs_prod]
  have h1 : ∏ μ, |heatDiff (m μ) t (x μ)| ≤
      ∏ μ, (5000 * ((Real.sqrt t)⁻¹) ^ (m μ + 1) * Elarge t (x μ)) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun μ _ => abs_heatDiff_le_large (hm μ) ht (x μ)
  refine h1.trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ μ, (m μ + 1) = d + ∑ μ, m μ := by
    rw [Finset.sum_add_distrib]; simp [add_comm]
  rw [hsum]
  have hE : ∏ μ, Elarge t (x μ) ≤ Elarge t (x μ0) * 2 ^ d := by
    rw [← Finset.mul_prod_erase Finset.univ (fun μ => Elarge t (x μ)) (Finset.mem_univ μ0)]
    apply mul_le_mul_of_nonneg_left _ (Elarge_nonneg _ _)
    calc ∏ μ ∈ Finset.univ.erase μ0, Elarge t (x μ) ≤ ∏ μ ∈ Finset.univ.erase μ0, (2 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => Elarge_nonneg _ _) fun μ _ => Elarge_le_two ht0 _
      _ = 2 ^ (Finset.univ.erase μ0).card := by rw [Finset.prod_const]
      _ ≤ 2 ^ d := by
          apply pow_le_pow_right₀ (by norm_num)
          calc (Finset.univ.erase μ0).card ≤ Finset.univ.card := Finset.card_le_card (Finset.erase_subset _ _)
            _ = d := by simp
  have hs : 0 ≤ ((Real.sqrt t)⁻¹) ^ (d + ∑ μ, m μ) := by positivity
  calc 5000 ^ d * ((Real.sqrt t)⁻¹) ^ (d + ∑ μ, m μ) * ∏ μ, Elarge t (x μ)
      ≤ 5000 ^ d * ((Real.sqrt t)⁻¹) ^ (d + ∑ μ, m μ) * (Elarge t (x μ0) * 2 ^ d) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 5000 ^ d * 2 ^ d * invSqrtPow (d + ∑ μ, m μ) t * Elarge t (x μ0) := by
        unfold invSqrtPow; ring

/-- The constant of the small-time bound. -/
def smallTimeConst : ℝ := 2 * Real.exp 2 * (2 * Real.exp 1) ^ 2

theorem abs_heatDiffProd_le_small (m : Fin d → ℕ) (hm : ∀ μ, m μ ≤ 2) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (x : Fin d → ℤ) (μ0 : Fin d) :
    |heatDiffProd d m t x| ≤ smallTimeConst ^ d * Real.exp (-|((x μ0 : ℤ) : ℝ)|) := by
  unfold heatDiffProd
  rw [Finset.abs_prod]
  have hB : 0 ≤ smallTimeConst := by unfold smallTimeConst; positivity
  have h1 : ∀ μ, |heatDiff (m μ) t (x μ)| ≤ smallTimeConst * Real.exp (-|((x μ : ℤ) : ℝ)|) := by
    intro μ
    refine (abs_heatDiff_le_small (m μ) ht ht1 (x μ)).trans ?_
    unfold smallTimeConst
    have : (2 * Real.exp 1) ^ (m μ) ≤ (2 * Real.exp 1) ^ 2 :=
      pow_le_pow_right₀ (by have := Real.add_one_le_exp (1 : ℝ); linarith) (hm μ)
    have hp := Real.exp_pos (-|((x μ : ℤ) : ℝ)|)
    have h2 : 0 ≤ 2 * Real.exp 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h2]
  have h2 : ∀ μ, |heatDiff (m μ) t (x μ)| ≤ smallTimeConst := fun μ =>
    (h1 μ).trans (by
      have : Real.exp (-|((x μ : ℤ) : ℝ)|) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := abs_nonneg ((x μ : ℤ) : ℝ); linarith)
      nlinarith)
  rw [← Finset.mul_prod_erase Finset.univ (fun μ => |heatDiff (m μ) t (x μ)|) (Finset.mem_univ μ0)]
  calc |heatDiff (m μ0) t (x μ0)| * ∏ μ ∈ Finset.univ.erase μ0, |heatDiff (m μ) t (x μ)|
      ≤ (smallTimeConst * Real.exp (-|((x μ0 : ℤ) : ℝ)|)) *
          ∏ μ ∈ Finset.univ.erase μ0, smallTimeConst :=
        mul_le_mul (h1 μ0) (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun μ _ => h2 μ)
          (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = smallTimeConst ^ d * Real.exp (-|((x μ0 : ℤ) : ℝ)|) := by
        rw [Finset.prod_const]
        have : (Finset.univ.erase μ0).card + 1 = d := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ μ0)]
          have : 0 < d := Fin.pos μ0
          simp; omega
        have hp : smallTimeConst ^ d = smallTimeConst ^ ((Finset.univ.erase μ0).card + 1) := by
          rw [this]
        rw [hp, pow_succ]; ring

theorem exists_norm_eq (hd : 0 < d) (x : Fin d → ℤ) :
    ∃ μ0 : Fin d, ‖x‖ = |((x μ0 : ℤ) : ℝ)| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨μ0, hμ0⟩ := Finite.exists_max fun μ => ‖x μ‖
  refine ⟨μ0, ?_⟩
  have h1 : ‖x‖ ≤ ‖x μ0‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hμ0
  have h2 : ‖x μ0‖ ≤ ‖x‖ := norm_le_pi_norm x μ0
  rw [le_antisymm h1 h2, Int.norm_eq_abs]

theorem heatDiffProd_integral_bound (hd : 3 ≤ d) (m : Fin d → ℕ) (hm : ∀ μ, m μ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℤ,
      IntegrableOn (fun t => heatDiffProd d m t x) (Ioi 0) ∧
      ∫ t in Ioi 0, |heatDiffProd d m t x| ≤ C / (1 + ‖x‖) ^ (d + ∑ μ, m μ - 2) := by
  set N := d + ∑ μ, m μ with hNdef
  have hN : 3 ≤ N := by omega
  obtain ⟨C1, hC1, hC1b⟩ := integral_invSqrtPow_Elarge_le hN
  set A : ℝ := 5000 ^ d * 2 ^ d with hA
  have hA0 : 0 ≤ A := by positivity
  set K : ℝ := Real.exp (1 / 4) * ((N - 2).factorial : ℝ) * 4 ^ (N - 2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨A * C1 + smallTimeConst ^ d * K, by unfold smallTimeConst; positivity, fun x => ?_⟩
  obtain ⟨μ0, hμ0⟩ := exists_norm_eq (by omega) x
  set f : ℝ → ℝ := fun t => heatDiffProd d m t x with hf
  have hfc : Continuous f := continuous_heatDiffProd m x
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn f (Ioc 0 1) := hfc.integrableOn_Ioc
  have hint2 : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' (((integrableOn_invSqrtPow_mul_Elarge hN (x μ0)).const_mul A))
      hfc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    have := abs_heatDiffProd_le_large m hm ht.le x μ0
    calc |f t| ≤ 5000 ^ d * 2 ^ d * invSqrtPow N t * Elarge t (x μ0) := this
      _ = A * (invSqrtPow N t * Elarge t (x μ0)) := by rw [hA]; ring
  refine ⟨by rw [hunion]; exact hint1.union hint2, ?_⟩
  have habs1 : IntegrableOn (fun t => |f t|) (Ioc 0 1) := hint1.abs
  have habs2 : IntegrableOn (fun t => |f t|) (Ioi 1) := hint2.abs
  have hsplit : ∫ t in Ioi 0, |f t| = (∫ t in Ioc 0 1, |f t|) + ∫ t in Ioi 1, |f t| := by
    conv_lhs => rw [hunion]
    exact setIntegral_union hdisj measurableSet_Ioi habs1 habs2
  have hpos : 0 < (1 + ‖x‖) ^ (N - 2) := by positivity
  -- small times
  have hp1 : ∫ t in Ioc 0 1, |f t| ≤ smallTimeConst ^ d * K / (1 + ‖x‖) ^ (N - 2) := by
    have h1 : ∫ t in Ioc 0 1, |f t| ≤ ∫ _t in Ioc (0 : ℝ) 1, smallTimeConst ^ d * Real.exp (-‖x‖) := by
      apply setIntegral_mono_on habs1 (integrableOn_const (by simp)) measurableSet_Ioc
      intro t ht
      have := abs_heatDiffProd_le_small m hm ht.1.le ht.2 x μ0
      rwa [← hμ0] at this
    refine h1.trans ?_
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
    simp only [sub_zero, smul_eq_mul, one_mul]
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
    have hexp : Real.exp (-‖x‖) ≤ Real.exp (-(‖x‖ / 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hexp2 := exp_neg_div_four_le (N - 2) hx0
    have hB0 : 0 ≤ smallTimeConst ^ d := by unfold smallTimeConst; positivity
    calc smallTimeConst ^ d * Real.exp (-‖x‖)
        ≤ smallTimeConst ^ d * (K / (1 + ‖x‖) ^ (N - 2)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact hexp.trans hexp2
      _ = smallTimeConst ^ d * K / (1 + ‖x‖) ^ (N - 2) := by ring
  -- large times
  have hp2 : ∫ t in Ioi 1, |f t| ≤ A * C1 / (1 + ‖x‖) ^ (N - 2) := by
    have h1 : ∫ t in Ioi 1, |f t| ≤ ∫ t in Ioi 1, A * (invSqrtPow N t * Elarge t (x μ0)) := by
      apply setIntegral_mono_on habs2 ((integrableOn_invSqrtPow_mul_Elarge hN (x μ0)).const_mul A)
        measurableSet_Ioi
      intro t ht
      have := abs_heatDiffProd_le_large m hm (le_of_lt ht) x μ0
      calc |f t| ≤ 5000 ^ d * 2 ^ d * invSqrtPow N t * Elarge t (x μ0) := this
        _ = A * (invSqrtPow N t * Elarge t (x μ0)) := by rw [hA]; ring
    refine h1.trans ?_
    rw [integral_const_mul]
    have := hC1b (x μ0)
    rw [← hμ0] at this
    calc A * ∫ t in Ioi 1, invSqrtPow N t * Elarge t (x μ0) ≤ A * (C1 / (1 + ‖x‖) ^ (N - 2)) :=
          mul_le_mul_of_nonneg_left this hA0
      _ = A * C1 / (1 + ‖x‖) ^ (N - 2) := by ring
  rw [hsplit]
  have : (A * C1 + smallTimeConst ^ d * K) / (1 + ‖x‖) ^ (d + ∑ μ, m μ - 2) =
      A * C1 / (1 + ‖x‖) ^ (N - 2) + smallTimeConst ^ d * K / (1 + ‖x‖) ^ (N - 2) := by
    rw [← hNdef]; ring
  rw [this]
  linarith

end Balaban.LatticeGreen
