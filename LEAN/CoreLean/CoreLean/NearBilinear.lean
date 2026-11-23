/-
`lem:near-cancellation`, Step 7 of its proof (the bilinear term), of BALABAN_CORE.tex (`a021c13be348`), for scalar
functions on `ℤ⁴` with finite supports (the pairing `tr(XY)` being bilinear, the matrix case is the sum over entries).
With `P_{f,g}(z) = Σ_y f(y)g(y + z)`, the backward difference `∂_κ` of `VanishingMoments.lean` and the forward one
`∂⁺_κg(w) = g(w + e_κ) - g(w)`:
* `move_left`: `Σ_z (∂_κk)(z)P_{f,g}(z) = Σ_z k(z)P_{∂_κf, g}(z)`;
* `move_right`: `Σ_z (∂_κk)(z)P_{f,g}(z) = -Σ_z k(z)P_{f, ∂⁺_κg}(z)`;
* `move_four`: for `k = ∂_{κ₀}∂_{κ₁}∂_{κ₂}∂_{κ₃}F`, `Σ_z k(z)P_{f,g}(z) = Σ_z F(z)P_{∂_{κ₁}∂_{κ₀}f, ∂⁺_{κ₃}∂⁺_{κ₂}g}(z)`, two
  differences moved to each side, the sign `(-1)²` being `1`;
* `bilinear_bound`: with `|F(z)| ≤ C_Ke^{-δ|z|₁}`, `f'` supported on `N` points and bounded by `a`, and
  `|g'(y + z)| ≤ b₁ + b₂1[|z|₁ ≥ R]` for `y` in the support, `|Σ_z F(z)P_{f',g'}(z)| ≤ C_KNaΣ_z e^{-δ|z|₁}(b₁ + b₂1[|z|₁ ≥ R])`.
With `lem:vanishing-moments` (`iterate_difference`, `m = 4`) this is the core's bound of `T`.
-/
import CoreLean.VanishingMoments

open Finset

noncomputable section

namespace CoreLean
namespace VanishingMoments

/-- `e_κ`. -/
abbrev ek (κ : Fin 4) : Z4 := Pi.single κ 1

/-- The forward difference `∂⁺_κg(w) = g(w + e_κ) - g(w)`. -/
def fd (κ : Fin 4) (g : Z4 → ℝ) (w : Z4) : ℝ := g (w + ek κ) - g w

/-- `P_{f,g}(z) = Σ_y f(y)g(y + z)`. -/
def Pfg (f g : Z4 → ℝ) (z : Z4) : ℝ := ∑' y, f y * g (y + z)

/-- Finite support. -/
abbrev FinSupp (f : Z4 → ℝ) : Prop := (Function.support f).Finite

lemma FinSupp.summable {h : Z4 → ℝ} (hh : FinSupp h) : Summable h :=
  summable_of_ne_finset_zero (s := hh.toFinset) fun b hb => by
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hb; exact hb

lemma FinSupp.summable_mul {f : Z4 → ℝ} (hf : FinSupp f) (h : Z4 → ℝ) : Summable fun y => f y * h y :=
  FinSupp.summable (hf.subset fun y hy => by
    rw [Function.mem_support] at hy ⊢; intro h0; exact hy (by rw [h0, zero_mul]))

lemma FinSupp.dk {f : Z4 → ℝ} (hf : FinSupp f) (κ : Fin 4) : FinSupp (dk κ f) := by
  refine (hf.union (hf.image fun y => y + ek κ)).subset fun z hz => ?_
  rw [Function.mem_support] at hz
  by_cases h : f z = 0
  · right
    refine ⟨z - ek κ, ?_, sub_add_cancel z (ek κ)⟩
    rw [Function.mem_support]; intro h'; apply hz; unfold VanishingMoments.dk; rw [h, h', sub_zero]
  · left; exact h

lemma FinSupp.fd {g : Z4 → ℝ} (hg : FinSupp g) (κ : Fin 4) : FinSupp (fd κ g) := by
  refine (hg.union (hg.image fun y => y - ek κ)).subset fun z hz => ?_
  rw [Function.mem_support] at hz
  by_cases h : g z = 0
  · right
    refine ⟨z + ek κ, ?_, add_sub_cancel_right z (ek κ)⟩
    rw [Function.mem_support]; intro h'; apply hz; unfold VanishingMoments.fd; rw [h, h', sub_zero]
  · left; exact h

lemma FinSupp.Pfg {f g : Z4 → ℝ} (hf : FinSupp f) (hg : FinSupp g) : FinSupp (Pfg f g) := by
  have hfin : ((hg.toFinset ×ˢ hf.toFinset).image fun p => p.1 - p.2 : Set Z4).Finite := Finset.finite_toSet _
  refine hfin.subset fun z hz => ?_
  rw [Function.mem_support] at hz
  by_contra hzn
  apply hz
  have h0 : ∀ y, f y * g (y + z) = 0 := by
    intro y; by_contra h; apply hzn
    have h1 : f y ≠ 0 := left_ne_zero_of_mul h
    have h2 : g (y + z) ≠ 0 := right_ne_zero_of_mul h
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
    exact ⟨(y + z, y), ⟨(hg.mem_toFinset).2 h2, (hf.mem_toFinset).2 h1⟩, by simp⟩
  simp only [VanishingMoments.Pfg, h0, tsum_zero]

lemma FinSupp.shift {P : Z4 → ℝ} (hP : FinSupp P) (w : Z4) : FinSupp fun z => P (z + w) :=
  (hP.image fun z => z - w).subset fun z hz => ⟨z + w, hz, by simp⟩

lemma summable_mul_fs {P : Z4 → ℝ} (hP : FinSupp P) (h : Z4 → ℝ) : Summable fun z => h z * P z := by
  have := hP.summable_mul h
  exact this.congr fun z => mul_comm _ _

/-- `P_{f,g}(z) - P_{f,g}(z + e_κ) = P_{∂_κf, g}(z)`. -/
lemma Pfg_dk {f g : Z4 → ℝ} (hf : FinSupp f) (κ : Fin 4) (z : Z4) :
    Pfg f g z - Pfg f g (z + ek κ) = Pfg (dk κ f) g z := by
  unfold Pfg VanishingMoments.dk
  have h1 : ∑' y, f y * g (y + (z + ek κ)) = ∑' y, f (y - ek κ) * g (y + z) := by
    rw [← (Equiv.addRight (ek κ)).tsum_eq (fun y => f (y - ek κ) * g (y + z))]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    congr 2; abel
  have hs2 : Summable fun y => f (y - ek κ) * g (y + z) :=
    ((hf.shift (-ek κ)).summable_mul fun y => g (y + z)).congr fun y => by rw [sub_eq_add_neg]
  rw [h1, ← (hf.summable_mul _).tsum_sub hs2]
  exact tsum_congr fun y => by ring

/-- `P_{f,g}(z + e_κ) - P_{f,g}(z) = P_{f, ∂⁺_κg}(z)`. -/
lemma Pfg_fd {f g : Z4 → ℝ} (hf : FinSupp f) (κ : Fin 4) (z : Z4) :
    Pfg f g (z + ek κ) - Pfg f g z = Pfg f (fd κ g) z := by
  unfold Pfg fd
  rw [← (hf.summable_mul _).tsum_sub (hf.summable_mul _)]
  exact tsum_congr fun y => by rw [show y + (z + ek κ) = y + z + ek κ by abel]; ring

/-- The first step of the summation by parts: `Σ_z (∂_κk)(z)P(z) = Σ_z k(z)(P(z) - P(z + e_κ))`. -/
lemma sum_dk_mul {P : Z4 → ℝ} (hP : FinSupp P) (k : Z4 → ℝ) (κ : Fin 4) :
    ∑' z, dk κ k z * P z = ∑' z, k z * (P z - P (z + ek κ)) := by
  have h1 : ∑' z, k (z - ek κ) * P z = ∑' z, k z * P (z + ek κ) := by
    rw [← (Equiv.addRight (ek κ)).tsum_eq (fun z => k (z - ek κ) * P z)]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have e1 : ∑' z, dk κ k z * P z = ∑' z, k z * P z - ∑' z, k (z - ek κ) * P z := by
    rw [← (summable_mul_fs hP _).tsum_sub (summable_mul_fs hP _)]
    exact tsum_congr fun z => by unfold VanishingMoments.dk; ring
  rw [e1, h1, ← (summable_mul_fs hP _).tsum_sub (summable_mul_fs (hP.shift (ek κ)) _)]
  exact tsum_congr fun z => by ring

/-- **A difference moved to the left factor**. -/
theorem move_left {f g : Z4 → ℝ} (hf : FinSupp f) (hg : FinSupp g) (k : Z4 → ℝ) (κ : Fin 4) :
    ∑' z, dk κ k z * Pfg f g z = ∑' z, k z * Pfg (dk κ f) g z := by
  rw [sum_dk_mul (hf.Pfg hg)]
  exact tsum_congr fun z => by rw [Pfg_dk hf]

/-- **A difference moved to the right factor**, with the sign `-1`. -/
theorem move_right {f g : Z4 → ℝ} (hf : FinSupp f) (hg : FinSupp g) (k : Z4 → ℝ) (κ : Fin 4) :
    ∑' z, dk κ k z * Pfg f g z = -∑' z, k z * Pfg f (fd κ g) z := by
  rw [sum_dk_mul (hf.Pfg hg), ← tsum_neg]
  exact tsum_congr fun z => by rw [← Pfg_fd hf]; ring

/-- **Four differences**, two moved to each factor. -/
theorem move_four {f g : Z4 → ℝ} (hf : FinSupp f) (hg : FinSupp g) (F : Z4 → ℝ) (κ₀ κ₁ κ₂ κ₃ : Fin 4) :
    ∑' z, dk κ₀ (dk κ₁ (dk κ₂ (dk κ₃ F))) z * Pfg f g z =
      ∑' z, F z * Pfg (dk κ₁ (dk κ₀ f)) (fd κ₃ (fd κ₂ g)) z := by
  rw [move_left hf hg, move_left (hf.dk κ₀) hg, move_right ((hf.dk κ₀).dk κ₁) hg,
    move_right ((hf.dk κ₀).dk κ₁) (hg.fd κ₂), neg_neg]

lemma Dl_four (κ : Fin 4 → Fin 4) (F : Z4 → ℝ) :
    Dl 4 κ F = dk (κ 0) (dk (κ 1) (dk (κ 2) (dk (κ 3) F))) := rfl

/-- **The bound of the bilinear term**. -/
theorem bilinear_bound {f g F : Z4 → ℝ} (S : Finset Z4) (hfS : ∀ y ∉ S, f y = 0) {δ CK a b₁ b₂ R : ℝ}
    (hδ : 0 < δ) (ha : ∀ y, |f y| ≤ a) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hF : ∀ z, |F z| ≤ CK * Real.exp (-δ * n1 z))
    (hg : ∀ y ∈ S, ∀ z, |g (y + z)| ≤ b₁ + b₂ * (if R ≤ n1 z then 1 else 0)) (hP : FinSupp (Pfg f g)) :
    |∑' z, F z * Pfg f g z| ≤
      CK * S.card * a * ∑' z, Real.exp (-δ * n1 z) * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0)) := by
  have hCK : 0 ≤ CK := by
    have := (abs_nonneg _).trans (hF 0); simpa [n1] using this
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0)
  set w : Z4 → ℝ := fun z => Real.exp (-δ * n1 z) * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0))
  have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> positivity)
  have hP_le : ∀ z, |Pfg f g z| ≤ S.card * a * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0)) := by
    intro z
    unfold Pfg
    rw [tsum_eq_sum (s := S) fun y hy => by rw [hfS y hy, zero_mul]]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y ∈ S, |f y * g (y + z)| ≤ ∑ y ∈ S, a * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0)) := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [abs_mul]
          exact mul_le_mul (ha y) (hg y hy z) (abs_nonneg _) ha0
      _ = S.card * a * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hsw : Summable w := by
    have hd : Decay δ 1 (fun z => Real.exp (-δ * n1 z)) := fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    have hs := summable_of_decay (E := ℝ) hd hδ
    refine (hs.mul_right (b₁ + b₂)).of_nonneg_of_le hw0 fun z => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    split_ifs <;> linarith
  have hterm : ∀ z, |F z * Pfg f g z| ≤ CK * S.card * a * w z := fun z => by
    rw [abs_mul]
    calc |F z| * |Pfg f g z| ≤ CK * Real.exp (-δ * n1 z) *
          (S.card * a * (b₁ + b₂ * (if R ≤ n1 z then 1 else 0))) :=
          mul_le_mul (hF z) (hP_le z) (abs_nonneg _) (mul_nonneg hCK (Real.exp_pos _).le)
      _ = CK * S.card * a * w z := by simp only [w]; ring
  have hfa : FinSupp fun z => |F z * Pfg f g z| := hP.subset fun z hz => by
    rw [Function.mem_support] at hz ⊢; intro h0; exact hz (by rw [h0, mul_zero, abs_zero])
  calc |∑' z, F z * Pfg f g z| ≤ ∑' z, |F z * Pfg f g z| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun z => Real.norm_eq_abs _))
        exact hfa.summable.congr fun z => (Real.norm_eq_abs _).symm
    _ ≤ ∑' z, CK * S.card * a * w z := Summable.tsum_le_tsum hterm hfa.summable (hsw.mul_left _)
    _ = CK * S.card * a * ∑' z, w z := tsum_mul_left

end VanishingMoments
end CoreLean

end
