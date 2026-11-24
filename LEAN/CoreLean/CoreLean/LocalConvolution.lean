/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`): the terms of `eq:local-representation` as convolutions, and
Young's inequality in the core's normalisation.

* `norm_resolvent_le_conv`: `‖(G₁F)(n)‖ ≤ Σ_{z ∈ Z}k(z)‖F(n - z)‖`, `k = resKernel ε`;
  `norm_dfw_resolvent_le_conv`: `‖(∂_μG₁F)(n)‖ ≤ ε⁻¹Σ_{z ∈ Z}dKer(z)‖F(n - z)‖`, for `F` vanishing outside a finite set
  `B` and `Z ⊇ n - B` (the kernel of `∂_μP_t` is `ε⁻¹(p(z + e_μ) - p(z))`, `dfw_heatOp_eq`).
* `young_real`, `young_real_inf`: Young's inequality for real `K, f ≥ 0` with `s = 6/5`.
* `conv_Lq`, `conv_Linf`: with the weights `ε⁴`,
  `(Σ_{n ∈ A}ε⁴w(n)^q)^{1/q} ≤ C(Σ_{m ∈ B}ε⁴f(m)^p)^{1/p}` and `w(n) ≤ C(Σ_mε⁴f(m)^6)^{1/6}` when
  `w ≤ K * f` and `(Σ_zK(z)^{6/5})^{5/6} ≤ Cε^{2/3}`, `1/p - 1/q = 1/6`.
-/
import CoreLean.LocalKernelNorms
import CoreLean.LocalYoung
import CoreLean.FreeSchauder

open Finset MeasureTheory Set Balaban.LatticeGreen

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε : ℝ}

/-- The differences `n - b`, `n ∈ A`, `b ∈ B`. -/
def diffSet (A B : Finset (Fin 4 → ℤ)) : Finset (Fin 4 → ℤ) := (A ×ˢ B).image fun x => x.1 - x.2

lemma sub_mem_diffSet {A B : Finset (Fin 4 → ℤ)} {n b : Fin 4 → ℤ} (hn : n ∈ A) (hb : b ∈ B) :
    n - b ∈ diffSet A B := mem_image.2 ⟨(n, b), mem_product.2 ⟨hn, hb⟩, rfl⟩

lemma vanish_off {F : (Fin 4 → ℤ) → V} {A B : Finset (Fin 4 → ℤ)} (hF : ∀ m, F m ≠ 0 → m ∈ B)
    {n : Fin 4 → ℤ} (hn : n ∈ A) (z : Fin 4 → ℤ) (hz : z ∉ diffSet A B) : F (n - z) = 0 := by
  by_contra h
  apply hz
  have := sub_mem_diffSet hn (hF _ h)
  rwa [sub_sub_cancel] at this

/-- `‖(G₁F)(n)‖ ≤ Σ_{z ∈ Z}k(z)‖F(n - z)‖`. -/
theorem norm_resolvent_le_conv {F : (Fin 4 → ℤ) → V} {M : ℝ} (hM : ∀ n, ‖F n‖ ≤ M) {A B : Finset (Fin 4 → ℤ)}
    (hF : ∀ m, F m ≠ 0 → m ∈ B) {n : Fin 4 → ℤ} (hn : n ∈ A) :
    ‖resolvent ε F n‖ ≤ ∑ z ∈ diffSet A B, resKernel ε z * ‖F (n - z)‖ := by
  rw [resolvent_eq_tsum hM, tsum_eq_sum (s := diffSet A B) fun z hz => by rw [vanish_off hF hn z hz, smul_zero]]
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun z _ => ?_))
  rw [norm_smul, Real.norm_of_nonneg (resKernel_nonneg z)]

/-- `‖(∂_μG₁F)(n)‖ ≤ ε⁻¹Σ_{z ∈ Z}dKer(z)‖F(n - z)‖`. -/
theorem norm_dfw_resolvent_le_conv (hε : 0 < ε) {F : (Fin 4 → ℤ) → V} {M : ℝ} (hM : ∀ n, ‖F n‖ ≤ M)
    {A B : Finset (Fin 4 → ℤ)} (hF : ∀ m, F m ≠ 0 → m ∈ B) (μ : Fin 4) {n : Fin 4 → ℤ} (hn : n ∈ A) :
    ‖dfw ε μ (resolvent ε F) n‖ ≤ ε⁻¹ * ∑ z ∈ diffSet A B, dKer ε μ z * ‖F (n - z)‖ := by
  set Z := diffSet A B
  have h := dif_resolvent (ε := ε) hM true μ n
  change dfw ε μ (resolvent ε F) n = ∫ t in Ioi 0, Real.exp (-t) • dfw ε μ (heatOp ε t F) n at h
  rw [h]
  set g : ℝ → ℝ := fun t => ε⁻¹ * ∑ z ∈ Z, Real.exp (-t) *
    |heatKernel 4 (t / ε ^ 2) (z + e4 μ) - heatKernel 4 (t / ε ^ 2) z| * ‖F (n - z)‖
  have hg : IntegrableOn g (Ioi 0) :=
    (integrable_finsetSum _ fun z _ => (integrableOn_dKer μ z).mul_const _).const_mul _
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖Real.exp (-t) • dfw ε μ (heatOp ε t F) n‖ ≤ g t := fun t ht => by
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [dfw_heatOp_eq ht0 hM μ n, tsum_eq_sum (s := Z) fun z hz => by rw [vanish_off hF hn z hz, smul_zero],
      norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
    simp only [g, mul_sum]
    calc Real.exp (-t) * (ε⁻¹ * ‖∑ b ∈ Z, (heatKernel 4 (t / ε ^ 2) (b + e4 μ) - heatKernel 4 (t / ε ^ 2) b) •
          F (n - b)‖)
        ≤ Real.exp (-t) * (ε⁻¹ * ∑ b ∈ Z, |heatKernel 4 (t / ε ^ 2) (b + e4 μ) - heatKernel 4 (t / ε ^ 2) b| *
          ‖F (n - b)‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq
            (sum_congr rfl fun z _ => by rw [norm_smul, Real.norm_eq_abs]))) (inv_nonneg.2 hε.le)) (Real.exp_pos _).le
      _ = _ := by
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun z _ => by ring
  refine (norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall hpt))).trans (le_of_eq ?_)
  simp only [g]
  rw [integral_const_mul, integral_finsetSum _ fun z _ => (integrableOn_dKer μ z).mul_const _]
  congr 1
  refine sum_congr rfl fun z _ => ?_
  rw [integral_mul_const]; rfl

/-! ### Young's inequality with real functions -/

/-- **Young's inequality** for real `K, f ≥ 0`, `s = 6/5`, `q < ∞`. -/
theorem young_real (A Z B : Finset (Fin 4 → ℤ)) {K f : (Fin 4 → ℤ) → ℝ} (hK : ∀ z, 0 ≤ K z) (hf : ∀ m, 0 ≤ f m)
    (hfB : ∀ m, f m ≠ 0 → m ∈ B) {p q : ℝ} (hp : 2 ≤ p) (hpq : p < q) (hrel : 1 / p - 1 / q = 1 / 6) :
    (∑ n ∈ A, (∑ z ∈ Z, K z * f (n - z)) ^ q) ^ (1 / q) ≤
      (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) * (∑ m ∈ B, f m ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hq3 : 3 ≤ q := by
    have : 1 / q ≤ 1 / 3 := by
      have h1p : 1 / p ≤ 1 / 2 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
      linarith
    rwa [div_le_div_iff₀ hq0 (by norm_num), one_mul, one_mul] at this
  have hY := young_fin A Z B (fun z => (K z).toNNReal) (fun m => (f m).toNNReal)
    (fun m hm => hfB m fun h => hm (by simp [h])) (s := 6 / 5) (p := p) (q := q) (by norm_num) (by linarith)
    (by linarith) hpq (by
      have : p⁻¹ - q⁻¹ = 6⁻¹ := by simpa [one_div] using hrel
      norm_num; linarith)
  have hY' : ∑ n ∈ A, (∑ z ∈ Z, K z * f (n - z)) ^ q ≤
      (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (q / (6 / 5)) * (∑ m ∈ B, f m ^ p) ^ (q / p) := by
    have := NNReal.coe_le_coe.2 hY
    push_cast at this
    simp only [NNReal.coe_rpow, NNReal.coe_sum, NNReal.coe_mul, Real.coe_toNNReal _ (hK _),
      Real.coe_toNNReal _ (hf _)] at this
    exact this
  have hSK := sum_nonneg fun z (_ : z ∈ Z) => Real.rpow_nonneg (hK z) (6 / 5 : ℝ)
  have hSf := sum_nonneg fun m (_ : m ∈ B) => Real.rpow_nonneg (hf m) p
  refine (Real.rpow_le_rpow (sum_nonneg fun n _ => Real.rpow_nonneg (sum_nonneg fun z _ =>
    mul_nonneg (hK z) (hf _)) _) hY' (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (Real.rpow_nonneg hSK _) (Real.rpow_nonneg hSf _), ← Real.rpow_mul hSK, ← Real.rpow_mul hSf]
  congr 2 <;> field_simp <;> ring

/-- **Young's inequality** for real `K, f ≥ 0`, `s = 6/5`, `q = ∞`. -/
theorem young_real_inf (Z B : Finset (Fin 4 → ℤ)) {K f : (Fin 4 → ℤ) → ℝ} (hK : ∀ z, 0 ≤ K z) (hf : ∀ m, 0 ≤ f m)
    (hfB : ∀ m, f m ≠ 0 → m ∈ B) (n : Fin 4 → ℤ) :
    ∑ z ∈ Z, K z * f (n - z) ≤ (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) * (∑ m ∈ B, f m ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
  have hc : (6 / 5 : ℝ).HolderConjugate 6 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hY := young_inf Z B (fun z => (K z).toNNReal) (fun m => (f m).toNNReal)
    (fun m hm => hfB m fun h => hm (by simp [h])) hc n
  have := NNReal.coe_le_coe.2 hY
  push_cast at this
  simp only [NNReal.coe_rpow, NNReal.coe_sum, NNReal.coe_mul, Real.coe_toNNReal _ (hK _),
    Real.coe_toNNReal _ (hf _)] at this
  rw [show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num] at this
  exact this

/-! ### The weighted norms -/

/-- `(Σ_{n ∈ A}ε⁴w(n)^q)^{1/q} ≤ C(Σ_{m ∈ B}ε⁴f(m)^p)^{1/p}`. -/
theorem conv_Lq (hε : 0 < ε) (A Z B : Finset (Fin 4 → ℤ)) {K f w : (Fin 4 → ℤ) → ℝ} (hK : ∀ z, 0 ≤ K z)
    (hf : ∀ m, 0 ≤ f m) (hfB : ∀ m, f m ≠ 0 → m ∈ B) (hw0 : ∀ n, 0 ≤ w n)
    (hw : ∀ n ∈ A, w n ≤ ∑ z ∈ Z, K z * f (n - z)) {C : ℝ}
    (hKC : (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ C * ε ^ (2 / 3 : ℝ)) {p q : ℝ} (hp : 2 ≤ p) (hpq : p < q)
    (hrel : 1 / p - 1 / q = 1 / 6) :
    (∑ n ∈ A, ε ^ 4 * w n ^ q) ^ (1 / q) ≤ C * (∑ m ∈ B, ε ^ 4 * f m ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have he4 : 0 ≤ ε ^ 4 := by positivity
  have hY := young_real A Z B hK hf hfB hp hpq hrel
  have hmono : ∑ n ∈ A, w n ^ q ≤ ∑ n ∈ A, (∑ z ∈ Z, K z * f (n - z)) ^ q :=
    sum_le_sum fun n hn => Real.rpow_le_rpow (hw0 n) (hw n hn) hq0.le
  have hSf := sum_nonneg fun m (_ : m ∈ B) => Real.rpow_nonneg (hf m) p
  have hSw := sum_nonneg fun n (_ : n ∈ A) => Real.rpow_nonneg (hw0 n) q
  have hC0 : 0 ≤ C * ε ^ (2 / 3 : ℝ) := (Real.rpow_nonneg (sum_nonneg fun z _ =>
    Real.rpow_nonneg (hK z) _) _).trans hKC
  rw [← mul_sum, ← mul_sum, Real.mul_rpow he4 hSw, Real.mul_rpow he4 hSf]
  have e1 : (ε ^ 4) ^ (1 / q) = ε ^ (4 / q) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num; ring_nf
  have e2 : (ε ^ 4) ^ (1 / p) = ε ^ (4 / p) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num; ring_nf
  rw [e1, e2]
  calc ε ^ (4 / q) * (∑ n ∈ A, w n ^ q) ^ (1 / q)
      ≤ ε ^ (4 / q) * ((C * ε ^ (2 / 3 : ℝ)) * (∑ m ∈ B, f m ^ p) ^ (1 / p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hε.le _)
        refine (Real.rpow_le_rpow hSw hmono (by positivity)).trans (hY.trans ?_)
        exact mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg hSf _)
    _ = C * (ε ^ (4 / q) * ε ^ (2 / 3 : ℝ)) * (∑ m ∈ B, f m ^ p) ^ (1 / p) := by ring
    _ = C * (ε ^ (4 / p) * (∑ m ∈ B, f m ^ p) ^ (1 / p)) := by
        rw [← Real.rpow_add hε, show 4 / q + 2 / 3 = 4 / p by
          have : 1 / q = 1 / p - 1 / 6 := by linarith
          rw [show 4 / q = 4 * (1 / q) by ring, this, show 4 / p = 4 * (1 / p) by ring]; ring]
        ring

/-- `w(n) ≤ C(Σ_{m ∈ B}ε⁴f(m)^6)^{1/6}`. -/
theorem conv_Linf (hε : 0 < ε) (Z B : Finset (Fin 4 → ℤ)) {K f : (Fin 4 → ℤ) → ℝ} (hK : ∀ z, 0 ≤ K z)
    (hf : ∀ m, 0 ≤ f m) (hfB : ∀ m, f m ≠ 0 → m ∈ B) {C : ℝ}
    (hKC : (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ C * ε ^ (2 / 3 : ℝ)) (n : Fin 4 → ℤ) :
    ∑ z ∈ Z, K z * f (n - z) ≤ C * (∑ m ∈ B, ε ^ 4 * f m ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
  have hSf := sum_nonneg fun m (_ : m ∈ B) => Real.rpow_nonneg (hf m) (6 : ℝ)
  refine (young_real_inf Z B hK hf hfB n).trans ?_
  rw [← mul_sum, Real.mul_rpow (by positivity) hSf]
  have e : (ε ^ 4) ^ (1 / 6 : ℝ) = ε ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  rw [e]
  calc (∑ z ∈ Z, K z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) * (∑ m ∈ B, f m ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ C * ε ^ (2 / 3 : ℝ) * (∑ m ∈ B, f m ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg hSf _)
    _ = C * (ε ^ (2 / 3 : ℝ) * (∑ m ∈ B, f m ^ (6 : ℝ)) ^ (1 / 6 : ℝ)) := by ring

end LocalLaplacian
end CoreLean

end
