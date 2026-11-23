/-
`lem:partition-of-unity`(ii) of BALABAN_CORE.tex (`46925ba99aac`): the Lipschitz bound of `h_□` and the bound
of its second differences at the points of the Dirichlet domain.

The proof works with differences instead of derivatives: a product rule for the first and second differences
(`DB.mul`) gives the bounds of `φ_□`, a product of four factors, and of `N² = Σφ_□²`, a sum of at most
`4 · 48` products which do not vanish near a point of a cube of `𝒟` (`card_T_le`); the function `t ↦ t^{-1/2}`
has the derivatives `-½t^{-3/2}` and `¾t^{-5/2}`, bounded by `½` and `¾` on `[1, ∞)`, which gives the first
and second differences of `1/N` where `N ≥ 1` (`F_lip`, `F_second`).

* `pu_lip`: `|h_□(x) - h_□(x')| ≤ C dT(x, x')/s_j` for all points, with `C` depending on `L` only.
* `pu_second`: `|h_□(x + u + v) - h_□(x + u) - h_□(x + v) + h_□(x)| ≤ C η²/s_j²` for `x ∈ Ω_D` and
  `‖u‖_∞, ‖v‖_∞ ≤ η` (the second differences of the lemma, divided by `η²`, are at most `C/s_j²`).
-/
import CoreLean.PartitionGeometry

open Real Finset
open scoped Classical

noncomputable section

namespace CoreLean
namespace PartitionUnity

local notation "E" => Fin 4 → ℝ

/-! ### Difference calculus -/

/-- A function with values in `[0, 1]` whose first differences in the directions `u`, `v` are at most `α`,
`β` and whose second difference is at most `δ`, at every point. -/
structure DB (f : E → ℝ) (u v : E) (α β δ : ℝ) : Prop where
  bd0 : ∀ y, 0 ≤ f y
  bd1 : ∀ y, f y ≤ 1
  du : ∀ y, |f (y + u) - f y| ≤ α
  dv : ∀ y, |f (y + v) - f y| ≤ β
  dd : ∀ y, |f (y + u + v) - f (y + u) - f (y + v) + f y| ≤ δ

lemma abs_add4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have := abs_add_le (a + b + c) d; have := abs_add_le (a + b) c; have := abs_add_le a b; linarith

namespace DB

variable {f g : E → ℝ} {u v : E} {α β δ α' β' δ' : ℝ}

lemma mono (h : DB f u v α β δ) (h1 : α ≤ α') (h2 : β ≤ β') (h3 : δ ≤ δ') : DB f u v α' β' δ' :=
  ⟨h.bd0, h.bd1, fun y => (h.du y).trans h1, fun y => (h.dv y).trans h2, fun y => (h.dd y).trans h3⟩

lemma abs_le_one (h : DB f u v α β δ) (y : E) : |f y| ≤ 1 := by
  rw [abs_of_nonneg (h.bd0 y)]; exact h.bd1 y

/-- The product rule. -/
lemma mul (hf : DB f u v α β δ) (hg : DB g u v α' β' δ') :
    DB (f * g) u v (α + α') (β + β') (δ + α * β' + β * α' + δ') := by
  have first : ∀ (w : E) (a a' : ℝ), (∀ y, |f (y + w) - f y| ≤ a) → (∀ y, |g (y + w) - g y| ≤ a') →
      ∀ y, |(f * g) (y + w) - (f * g) y| ≤ a + a' := by
    intro w a a' ha ha' y
    simp only [Pi.mul_apply]
    rw [show f (y + w) * g (y + w) - f y * g y = (f (y + w) - f y) * g (y + w) + f y * (g (y + w) - g y) by
      ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 : |f (y + w) - f y| * |g (y + w)| ≤ a :=
      (mul_le_of_le_one_right (abs_nonneg _) (hg.abs_le_one _)).trans (ha y)
    have b2 : |f y| * |g (y + w) - g y| ≤ a' :=
      (mul_le_of_le_one_left (abs_nonneg _) (hf.abs_le_one _)).trans (ha' y)
    linarith
  refine ⟨fun y => mul_nonneg (hf.bd0 y) (hg.bd0 y),
    fun y => mul_le_one₀ (hf.bd1 y) (hg.bd0 y) (hg.bd1 y), first u α α' hf.du hg.du,
    first v β β' hf.dv hg.dv, fun y => ?_⟩
  simp only [Pi.mul_apply]
  have e : f (y + u + v) * g (y + u + v) - f (y + u) * g (y + u) - f (y + v) * g (y + v) + f y * g y =
      (f (y + u + v) - f (y + u) - f (y + v) + f y) * g (y + u + v) +
        (f (y + u) - f y) * (g (y + u + v) - g (y + u)) +
        (f (y + v) - f y) * (g (y + v + u) - g (y + v)) +
        f y * (g (y + u + v) - g (y + u) - g (y + v) + g y) := by
    rw [show y + v + u = y + u + v by abel]; ring
  rw [e]
  have a1 : |(f (y + u + v) - f (y + u) - f (y + v) + f y) * g (y + u + v)| ≤ δ := by
    rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (hg.abs_le_one _)).trans (hf.dd y)
  have a2 : |(f (y + u) - f y) * (g (y + u + v) - g (y + u))| ≤ α * β' := by
    rw [abs_mul]; exact mul_le_mul (hf.du y) (hg.dv (y + u)) (abs_nonneg _) ((abs_nonneg _).trans (hf.du y))
  have a3 : |(f (y + v) - f y) * (g (y + v + u) - g (y + v))| ≤ β * α' := by
    rw [abs_mul]; exact mul_le_mul (hf.dv y) (hg.du (y + v)) (abs_nonneg _) ((abs_nonneg _).trans (hf.dv y))
  have a4 : |f y * (g (y + u + v) - g (y + u) - g (y + v) + g y)| ≤ δ' := by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hf.abs_le_one _)).trans (hg.dd y)
  refine (abs_add4 _ _ _ _).trans ?_
  linarith

end DB

/-! ### The function of a cube -/

section Cube

variable {ℓ : ℝ} (hℓ : 0 < ℓ) {A B : ℝ}

/-- The bounds of `φ` for steps `‖u‖_∞, ‖v‖_∞ ≤ s/12`, from those of its four factors. -/
lemma phi_DB (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ {s : ℝ}, 0 < s → s ≤ ℓ / 2 → ∀ c t t', |gT hℓ s c t - gT hℓ s c t'| ≤ A / s * |rep hℓ (t - t')|)
    (hB : ∀ {s : ℝ}, 0 < s → s ≤ ℓ / 2 → ∀ c t a b, |a| ≤ s / 12 → |b| ≤ s / 12 →
      |gT hℓ s c (t + a + b) - gT hℓ s c (t + a) - gT hℓ s c (t + b) + gT hℓ s c t| ≤ B / s ^ 2 * (|a| * |b|))
    {s : ℝ} (hs : 0 < s) (hsℓ : s ≤ ℓ / 2) (c : E) {u v : E} (hu : ‖u‖ ≤ s / 12) (hv : ‖v‖ ≤ s / 12) :
    DB (fun y => phiT hℓ s c y) u v (4 * (A / s * ‖u‖)) (4 * (A / s * ‖v‖))
      (4 * (B / s ^ 2 * (‖u‖ * ‖v‖)) + 12 * ((A / s * ‖u‖) * (A / s * ‖v‖))) := by
  set a := A / s * ‖u‖ with ha
  set b := A / s * ‖v‖ with hb
  set d := B / s ^ 2 * (‖u‖ * ‖v‖) with hd
  have hcoord : ∀ (w : E) μ, |w μ| ≤ ‖w‖ := fun w μ => by
    have := norm_le_pi_norm w μ; rwa [Real.norm_eq_abs] at this
  have hfac : ∀ μ, DB (fun y => gT hℓ s (c μ) (y μ)) u v a b d := fun μ => by
    refine ⟨fun y => gT_nonneg hℓ _ _ _, fun y => gT_le_one hℓ _ _ _, fun y => ?_, fun y => ?_, fun y => ?_⟩
    · have := hA hs hsℓ (c μ) ((y + u) μ) (y μ)
      simp only [Pi.add_apply, add_sub_cancel_left] at this ⊢
      refine this.trans ?_
      rw [ha]
      exact mul_le_mul_of_nonneg_left ((abs_rep_le_abs hℓ _).trans (hcoord u μ)) (by positivity)
    · have := hA hs hsℓ (c μ) ((y + v) μ) (y μ)
      simp only [Pi.add_apply, add_sub_cancel_left] at this ⊢
      refine this.trans ?_
      rw [hb]
      exact mul_le_mul_of_nonneg_left ((abs_rep_le_abs hℓ _).trans (hcoord v μ)) (by positivity)
    · have := hB hs hsℓ (c μ) (y μ) (u μ) (v μ) ((hcoord u μ).trans hu) ((hcoord v μ).trans hv)
      simp only [Pi.add_apply]
      refine this.trans ?_
      rw [hd]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hcoord u μ) (hcoord v μ) (abs_nonneg _) (norm_nonneg _))
        (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hprod : (fun y => phiT hℓ s c y) = (fun y => gT hℓ s (c 0) (y 0)) * (fun y => gT hℓ s (c 1) (y 1)) *
      (fun y => gT hℓ s (c 2) (y 2)) * (fun y => gT hℓ s (c 3) (y 3)) := by
    funext y; simp only [phiT, Fin.prod_univ_four, Pi.mul_apply]
  rw [hprod]
  refine ((((hfac 0).mul (hfac 1)).mul (hfac 2)).mul (hfac 3)).mono (by linarith) (by linarith) ?_
  nlinarith

end Cube

/-! ### The function `t ↦ t^{-1/2}` on `[1, ∞)` -/

/-- `F(t) = t^{-1/2}`. -/
def Fm (t : ℝ) : ℝ := t ^ (-(1 / 2 : ℝ))

/-- `F'(t) = -½t^{-3/2}`. -/
def Fm1 (t : ℝ) : ℝ := -(1 / 2) * t ^ (-(1 / 2 : ℝ) - 1)

lemma hasDerivAt_Fm {t : ℝ} (ht : 0 < t) : HasDerivAt Fm (Fm1 t) t := by
  have := Real.hasDerivAt_rpow_const (x := t) (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')
  exact this

lemma hasDerivAt_Fm1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt Fm1 (-(1 / 2) * ((-(1 / 2 : ℝ) - 1) * t ^ (-(1 / 2 : ℝ) - 1 - 1))) t := by
  have := Real.hasDerivAt_rpow_const (x := t) (p := -(1 / 2 : ℝ) - 1) (Or.inl ht.ne')
  exact this.const_mul _

lemma rpow_le_one' {t p : ℝ} (ht : 1 ≤ t) (hp : p ≤ 0) : t ^ p ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ht hp

lemma abs_Fm1_le {t : ℝ} (ht : 1 ≤ t) : |Fm1 t| ≤ 1 / 2 := by
  unfold Fm1
  have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg (by linarith) _
  have h1 := rpow_le_one' ht (by norm_num : (-(1 / 2 : ℝ) - 1) ≤ 0)
  rw [abs_mul, abs_of_nonneg h0]; norm_num; linarith

lemma abs_Fm2_le {t : ℝ} (ht : 1 ≤ t) :
    |-(1 / 2) * ((-(1 / 2 : ℝ) - 1) * t ^ (-(1 / 2 : ℝ) - 1 - 1))| ≤ 3 / 4 := by
  have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1 - 1) := Real.rpow_nonneg (by linarith) _
  have h1 := rpow_le_one' ht (by norm_num : (-(1 / 2 : ℝ) - 1 - 1) ≤ 0)
  rw [abs_mul, abs_mul, abs_of_nonneg h0]; norm_num; linarith

lemma uIcc_subset {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : Set.uIcc a b ⊆ Set.Ici 1 := fun t ht => by
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact Set.mem_Ici.2 (by linarith)

lemma F_lip {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : |Fm b - Fm a| ≤ 1 / 2 * |b - a| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ici 1) (f := Fm)
    (fun t ht => (hasDerivAt_Fm (by linarith [Set.mem_Ici.1 ht])).differentiableAt)
    (fun t ht => by rw [(hasDerivAt_Fm (by linarith [Set.mem_Ici.1 ht])).deriv]; exact abs_Fm1_le ht)
    (convex_Ici 1) (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)
  simpa [Real.norm_eq_abs] using this

lemma F1_lip {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : |Fm1 b - Fm1 a| ≤ 3 / 4 * |b - a| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ici 1) (f := Fm1)
    (fun t ht => (hasDerivAt_Fm1 (by linarith [Set.mem_Ici.1 ht])).differentiableAt)
    (fun t ht => by rw [(hasDerivAt_Fm1 (by linarith [Set.mem_Ici.1 ht])).deriv]; exact abs_Fm2_le ht)
    (convex_Ici 1) (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)
  simpa [Real.norm_eq_abs] using this

/-- `|F(b) - F(a) - F'(a)(b - a)| ≤ ¾(b - a)²` on `[1, ∞)`. -/
lemma F_taylor {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : |Fm b - Fm a - Fm1 a * (b - a)| ≤ 3 / 4 * (b - a) ^ 2 := by
  set g : ℝ → ℝ := fun t => Fm t - Fm1 a * t with hg
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt g (Fm1 t - Fm1 a) t := fun t ht => by
    have ht1 := Set.mem_Ici.1 (uIcc_subset ha hb ht)
    have h1 := hasDerivAt_Fm (t := t) (by linarith)
    have h2 := (hasDerivAt_id' t).const_mul (Fm1 a)
    have := h1.sub h2
    rw [mul_one] at this
    exact this
  have hbd : ∀ t ∈ Set.uIcc a b, ‖deriv g t‖ ≤ 3 / 4 * |b - a| := fun t ht => by
    rw [(hd t ht).deriv, Real.norm_eq_abs]
    have ht1 := Set.mem_Ici.1 (uIcc_subset ha hb ht)
    refine (F1_lip ha ht1).trans ?_
    exact mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc ht) (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun t ht => (hd t ht).differentiableAt) hbd
    (convex_uIcc a b) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [hg, Real.norm_eq_abs] at this
  rw [show Fm b - Fm a - Fm1 a * (b - a) = Fm b - Fm1 a * b - (Fm a - Fm1 a * a) by ring]
  calc _ ≤ 3 / 4 * |b - a| * |b - a| := this
    _ = 3 / 4 * (b - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- The second difference of `F` at four points of `[1, ∞)`. -/
lemma F_second {a b c d : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    |Fm d - Fm b - Fm c + Fm a| ≤
      1 / 2 * |d - b - c + a| + 3 / 4 * (|c - a| * |d - c| + (d - c) ^ 2 + (b - a) ^ 2) := by
  have e : Fm d - Fm b - Fm c + Fm a = (Fm d - Fm c - Fm1 c * (d - c)) - (Fm b - Fm a - Fm1 a * (b - a)) +
      Fm1 a * (d - b - c + a) + (Fm1 c - Fm1 a) * (d - c) := by ring
  rw [e]
  have t1 := F_taylor hc hd
  have t2 := F_taylor ha hb
  have t3 : |Fm1 a * (d - b - c + a)| ≤ 1 / 2 * |d - b - c + a| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_Fm1_le ha) (abs_nonneg _)
  have t4 : |(Fm1 c - Fm1 a) * (d - c)| ≤ 3 / 4 * (|c - a| * |d - c|) := by
    rw [abs_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (F1_lip ha hc) (abs_nonneg _)
  have := abs_add_le (Fm d - Fm c - Fm1 c * (d - c) - (Fm b - Fm a - Fm1 a * (b - a)) + Fm1 a * (d - b - c + a))
    ((Fm1 c - Fm1 a) * (d - c))
  have := abs_add_le (Fm d - Fm c - Fm1 c * (d - c) - (Fm b - Fm a - Fm1 a * (b - a))) (Fm1 a * (d - b - c + a))
  have := abs_sub (Fm d - Fm c - Fm1 c * (d - c)) (Fm b - Fm a - Fm1 a * (b - a))
  linarith

/-- `φ/max{√N², 1} = φ · F(N²)` where `N² ≥ 1`. -/
lemma div_max_sqrt {φ n : ℝ} (hn : 1 ≤ n) : φ / max (√n) 1 = φ * Fm n := by
  have h1 : 1 ≤ √n := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hn
  rw [max_eq_left h1, Fm, Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-! ### The bounds (ii) -/

lemma prod4_lip {a b : Fin 4 → ℝ} (ha0 : ∀ μ, 0 ≤ a μ) (ha1 : ∀ μ, a μ ≤ 1) (hb0 : ∀ μ, 0 ≤ b μ)
    (hb1 : ∀ μ, b μ ≤ 1) : |∏ μ, a μ - ∏ μ, b μ| ≤ ∑ μ, |a μ - b μ| := by
  rw [Fin.prod_univ_four, Fin.prod_univ_four, Fin.sum_univ_four]
  have e : a 0 * a 1 * a 2 * a 3 - b 0 * b 1 * b 2 * b 3 = (a 0 - b 0) * (a 1 * a 2 * a 3) +
      (a 1 - b 1) * (b 0 * a 2 * a 3) + (a 2 - b 2) * (b 0 * b 1 * a 3) + (a 3 - b 3) * (b 0 * b 1 * b 2) := by
    ring
  rw [e]
  refine (abs_add4 _ _ _ _).trans ?_
  have k : ∀ x y : ℝ, 0 ≤ y → y ≤ 1 → |x * y| ≤ |x| := fun x y h0 h1 => by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_right (abs_nonneg _) h1
  have p1 := k (a 0 - b 0) (a 1 * a 2 * a 3) (mul_nonneg (mul_nonneg (ha0 1) (ha0 2)) (ha0 3))
    (mul_le_one₀ (mul_le_one₀ (ha1 1) (ha0 2) (ha1 2)) (ha0 3) (ha1 3))
  have p2 := k (a 1 - b 1) (b 0 * a 2 * a 3) (mul_nonneg (mul_nonneg (hb0 0) (ha0 2)) (ha0 3))
    (mul_le_one₀ (mul_le_one₀ (hb1 0) (ha0 2) (ha1 2)) (ha0 3) (ha1 3))
  have p3 := k (a 2 - b 2) (b 0 * b 1 * a 3) (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (ha0 3))
    (mul_le_one₀ (mul_le_one₀ (hb1 0) (hb0 1) (hb1 1)) (ha0 3) (ha1 3))
  have p4 := k (a 3 - b 3) (b 0 * b 1 * b 2) (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2))
    (mul_le_one₀ (mul_le_one₀ (hb1 0) (hb0 1) (hb1 1)) (hb0 2) (hb1 2))
  linarith

/-- `|φ/M - φ'/M'| ≤ |φ - φ'| + |M - M'|` for `φ' ∈ [0, 1]` and `M, M' ≥ 1`. -/
lemma div_sub_div_le {φ φ' M M' : ℝ} (h0 : 0 ≤ φ') (h1 : φ' ≤ 1) (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    |φ / M - φ' / M'| ≤ |φ - φ'| + |M - M'| := by
  have e : φ / M - φ' / M' = (φ - φ') / M + φ' * ((M' - M) / (M * M')) := by field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < M by linarith)]
    exact div_le_self (abs_nonneg _) hM
  · rw [abs_mul, abs_of_nonneg h0, abs_div, abs_of_pos (show (0 : ℝ) < M * M' by nlinarith),
      abs_sub_comm M' M]
    have : |M - M'| / (M * M') ≤ |M - M'| := div_le_self (abs_nonneg _) (by nlinarith)
    calc φ' * (|M - M'| / (M * M')) ≤ 1 * |M - M'| := mul_le_mul h1 this (by positivity) zero_le_one
      _ = |M - M'| := one_mul _

/-- `|max{√a, 1} - max{√b, 1}| ≤ |a - b|`. -/
lemma max_sqrt_lip (a b : ℝ) : |max (√a) 1 - max (√b) 1| ≤ |a - b| := by
  have hab : ∀ a : ℝ, max (√a) 1 = √(max a 1) := fun a => by
    rcases le_total a 1 with h | h
    · rw [max_eq_right h, Real.sqrt_one, max_eq_right]
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt h
    · rw [max_eq_left h, max_eq_left]
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt h
  rw [hab, hab]
  set α := max a 1
  set β := max b 1
  have hα : 1 ≤ α := le_max_right _ _
  have hβ : 1 ≤ β := le_max_right _ _
  have h1 : 1 ≤ √α := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hα
  have h2 : 1 ≤ √β := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hβ
  have hprod : (√α - √β) * (√α + √β) = α - β := by
    have e : (√α - √β) * (√α + √β) = √α ^ 2 - √β ^ 2 := by ring
    rw [e, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  have hαβ : |α - β| ≤ |a - b| := abs_max_sub_max_le_abs a b 1
  have : |√α - √β| * 2 ≤ |α - β| := by
    rw [← hprod, abs_mul, abs_of_pos (by linarith : 0 < √α + √β)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith [abs_nonneg (√α - √β)]

namespace Domains

variable {S : Scales} (D : Domains S)

lemma φ_lip {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, |prof x - prof y| ≤ C * |x - y|) (q : S.Idx) (x x' : E) :
    |S.φ q x - S.φ q x'| ≤ 4 * (max C 3 / S.s q.1) * dT S.hℓ x x' := by
  unfold Scales.φ phiT
  refine (prod4_lip (fun μ => gT_nonneg _ _ _ _) (fun μ => gT_le_one _ _ _ _) (fun μ => gT_nonneg _ _ _ _)
    (fun μ => gT_le_one _ _ _ _)).trans ?_
  rw [Fin.sum_univ_four]
  have hb : ∀ μ, |gT S.hℓ (S.s q.1) (cen (S.s q.1) q.2 μ) (x μ) -
      gT S.hℓ (S.s q.1) (cen (S.s q.1) q.2 μ) (x' μ)| ≤ max C 3 / S.s q.1 * dT S.hℓ x x' := fun μ =>
    (gT_lip_of S.hℓ hC0 hC (S.s_pos _) (S.s_le_half' _) _ _ _).trans
      (mul_le_mul_of_nonneg_left (le_dT S.hℓ x x' μ) (div_nonneg (le_max_of_le_right (by norm_num))
        (S.s_pos _).le))
  linarith [hb 0, hb 1, hb 2, hb 3]

/-- `N²` as a sum over a set of cubes of `𝒟` which contains those whose functions do not vanish at `y`. -/
lemma N2_eq_sum (Ts : Finset S.Idx) (hT : ∀ q' ∈ Ts, D.InD q') {y : E} (hy : D.T y ⊆ Ts) :
    D.N2 y = ∑ q' ∈ Ts, S.φ q' y ^ 2 := by
  unfold N2
  rw [← Finset.sum_subset (Finset.subset_univ Ts) fun q' _ hq' => ?_]
  · exact Finset.sum_congr rfl fun q' hq' => if_pos (hT q' hq')
  · by_cases hI : D.InD q'
    · rw [if_pos hI]
      by_contra hne
      exact hq' (hy (by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hI, fun h => hne (by rw [h]; ring)⟩))
    · rw [if_neg hI]

lemma abs_sum_le_card {Ts : Finset S.Idx} {g : S.Idx → ℝ} {K : ℝ} (h : ∀ q' ∈ Ts, |g q'| ≤ K) :
    |∑ q' ∈ Ts, g q'| ≤ Ts.card * K :=
  (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ h).trans (by rw [nsmul_eq_mul]))

/-- The scale of a cube of `𝒟` whose function does not vanish at a point of `□ ∈ 𝒟_j` is at least `j - 1`. -/
lemma s_le_of_T {q : S.Idx} (hq : D.InD q) {y : E} (hy : dT S.hℓ y (cen (S.s q.1) q.2) ≤ S.s q.1)
    {q' : S.Idx} (hq' : q' ∈ D.T y) : S.s q.1 ≤ S.L * S.s q'.1 := by
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
  have := (D.scale hq hq'.1 hy hq'.2).1
  rw [← S.hsL]; exact S.s_mono this

/-- **(ii), the first bound**: `|h_□(x) - h_□(x')| ≤ (776AL + 3) dT(x, x')/s_j`, `A = max{C, 3}`. -/
theorem pu_lip {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, |prof x - prof y| ≤ C * |x - y|) (q : S.Idx) (x x' : E) :
    |D.hpu q x - D.hpu q x'| ≤ (776 * max C 3 * S.L + 3) / S.s q.1 * dT S.hℓ x x' := by
  set A := max C 3 with hAdef
  have hA0 : 0 ≤ A := le_max_of_le_right (by norm_num)
  have hL := S.L_ge
  have hs := S.s_pos q.1
  have hd0 := dT_nonneg S.hℓ x x'
  have hK0 : 0 ≤ (776 * A * S.L + 3) / S.s q.1 * dT S.hℓ x x' := by positivity
  by_cases hI : D.InD q
  swap
  · simp only [hpu, if_neg hI, sub_self, abs_zero]; exact hK0
  set c := cen (S.s q.1) q.2 with hc
  -- the function vanishes outside the inner part of `□`, and has values in `[0, 1]`
  have far : ∀ y y', S.s q.1 < dT S.hℓ y' c → |D.hpu q y - D.hpu q y'| ≤
      (776 * A * S.L + 3) / S.s q.1 * dT S.hℓ y y' := by
    intro y y' hy'
    have h0 : D.hpu q y' = 0 := D.pu_support q (by linarith)
    rw [h0, sub_zero]
    by_cases hy : D.hpu q y = 0
    · rw [hy, abs_zero]; exact mul_nonneg (div_nonneg (by nlinarith) hs.le) (dT_nonneg _ _ _)
    · have hφ : S.φ q y ≠ 0 := by
        intro h; apply hy; simp only [hpu, if_pos hI, h, zero_div]
      have hyc := S.dT_lt_of_φ_ne hφ
      have htri := dT_triangle S.hℓ y' y c
      rw [dT_comm S.hℓ y' y] at htri
      have h1 := (D.pu_mem q y).2
      have h0' := (D.pu_mem q y).1
      rw [abs_of_nonneg h0']
      calc D.hpu q y ≤ 1 := h1
        _ ≤ 3 / S.s q.1 * dT S.hℓ y y' := by rw [div_mul_eq_mul_div, le_div_iff₀ hs]; linarith
        _ ≤ (776 * A * S.L + 3) / S.s q.1 * dT S.hℓ y y' :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith) hs.le) (dT_nonneg _ _ _)
  by_cases h2 : S.s q.1 < dT S.hℓ x' c
  · exact far x x' h2
  by_cases h1 : S.s q.1 < dT S.hℓ x c
  · rw [abs_sub_comm, dT_comm]; exact far x' x h1
  push_neg at h1 h2
  -- both points lie in `□`
  have hM : ∀ y, 1 ≤ max (√(D.N2 y)) 1 := fun y => le_max_right _ _
  simp only [hpu, if_pos hI]
  refine (div_sub_div_le (S.φ_nonneg q x') (S.φ_le_one q x') (hM x) (hM x')).trans ?_
  have hφ := Domains.φ_lip (S := S) hC0 hC q x x'
  have hN := max_sqrt_lip (D.N2 x) (D.N2 x')
  -- the difference of `N²`
  set Ts := D.T x ∪ D.T x' with hTs
  have hTsI : ∀ q' ∈ Ts, D.InD q' := fun q' hq' => by
    rcases Finset.mem_union.1 hq' with h | h <;>
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
  have hcard : Ts.card ≤ 96 := (Finset.card_union_le _ _).trans (by
    have := D.card_T_le hI h1; have := D.card_T_le hI h2; omega)
  have hsq : ∀ q' ∈ Ts, |S.φ q' x ^ 2 - S.φ q' x' ^ 2| ≤ 8 * A * S.L / S.s q.1 * dT S.hℓ x x' := by
    intro q' hq'
    have hsc : S.s q.1 ≤ S.L * S.s q'.1 := by
      rcases Finset.mem_union.1 hq' with h | h
      · exact D.s_le_of_T hI h1 h
      · exact D.s_le_of_T hI h2 h
    have hs' := S.s_pos q'.1
    rw [show S.φ q' x ^ 2 - S.φ q' x' ^ 2 = (S.φ q' x - S.φ q' x') * (S.φ q' x + S.φ q' x') by ring,
      abs_mul]
    have hl := Domains.φ_lip (S := S) hC0 hC q' x x'
    have hsum : |S.φ q' x + S.φ q' x'| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [S.φ_nonneg q' x, S.φ_nonneg q' x', S.φ_le_one q' x, S.φ_le_one q' x']
    have hAs : A / S.s q'.1 ≤ A * S.L / S.s q.1 := by
      rw [div_le_div_iff₀ hs' hs]; nlinarith
    calc |S.φ q' x - S.φ q' x'| * |S.φ q' x + S.φ q' x'| ≤ (4 * (A / S.s q'.1) * dT S.hℓ x x') * 2 :=
          mul_le_mul hl hsum (abs_nonneg _) (by positivity)
      _ ≤ (4 * (A * S.L / S.s q.1) * dT S.hℓ x x') * 2 := by gcongr
      _ = 8 * A * S.L / S.s q.1 * dT S.hℓ x x' := by ring
  have hNd : |D.N2 x - D.N2 x'| ≤ 96 * (8 * A * S.L / S.s q.1 * dT S.hℓ x x') := by
    rw [D.N2_eq_sum Ts hTsI Finset.subset_union_left, D.N2_eq_sum Ts hTsI Finset.subset_union_right,
      ← Finset.sum_sub_distrib]
    refine (Domains.abs_sum_le_card (S := S) hsq).trans ?_
    have : (0 : ℝ) ≤ 8 * A * S.L / S.s q.1 * dT S.hℓ x x' := by positivity
    have hc' : (Ts.card : ℝ) ≤ 96 := by exact_mod_cast hcard
    nlinarith
  have hφ' : 4 * (A / S.s q.1) * dT S.hℓ x x' ≤ 4 * A * S.L / S.s q.1 * dT S.hℓ x x' := by
    have : A / S.s q.1 ≤ A * S.L / S.s q.1 := by
      rw [div_le_div_iff_of_pos_right hs]; nlinarith
    calc 4 * (A / S.s q.1) * dT S.hℓ x x' ≤ 4 * (A * S.L / S.s q.1) * dT S.hℓ x x' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hd0
      _ = 4 * A * S.L / S.s q.1 * dT S.hℓ x x' := by ring
  have : (776 * A * S.L + 3) / S.s q.1 * dT S.hℓ x x' =
      4 * A * S.L / S.s q.1 * dT S.hℓ x x' + 96 * (8 * A * S.L / S.s q.1 * dT S.hℓ x x') +
        (4 * A * S.L / S.s q.1 * dT S.hℓ x x' + 3 / S.s q.1 * dT S.hℓ x x') := by ring
  have h3 : 0 ≤ 4 * A * S.L / S.s q.1 * dT S.hℓ x x' + 3 / S.s q.1 * dT S.hℓ x x' :=
    add_nonneg (mul_nonneg (div_nonneg (by nlinarith) hs.le) hd0) (mul_nonneg (by positivity) hd0)
  linarith

end Domains

namespace Domains

variable {S : Scales} (D : Domains S)

/-- The bounds of `φ_{q'}` for steps `‖u‖_∞, ‖v‖_∞ ≤ η`, in the units `s_j ≤ Ls_{i'}` of a cube near which it
does not vanish: `α₀ = AL η/s_j`, `δ₀ = BL²η²/s_j²`. -/
lemma φ_DB_scaled {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC1 : ∀ x y, |prof x - prof y| ≤ C1 * |x - y|) (hC20 : 0 ≤ C2)
    (hC2 : ∀ x a b, |prof (x + a + b) - prof (x + a) - prof (x + b) + prof x| ≤ C2 * (|a| * |b|))
    (q' : S.Idx) {sj : ℝ} (hsj : 0 < sj) (hsc : sj ≤ S.L * S.s q'.1) {u v : E} (hu : ‖u‖ ≤ S.η)
    (hv : ‖v‖ ≤ S.η) :
    DB (S.φ q') u v (4 * (max C1 3 * S.L * S.η / sj)) (4 * (max C1 3 * S.L * S.η / sj))
      (4 * (C2 * S.L ^ 2 * S.η ^ 2 / sj ^ 2) + 12 * (max C1 3 * S.L * S.η / sj) ^ 2) := by
  set A := max C1 3 with hA
  have hA0 : 0 ≤ A := le_max_of_le_right (by norm_num)
  set s := S.s q'.1 with hsdef
  have hs : 0 < s := S.s_pos _
  have hη := S.hη
  have hL := S.L_ge
  have h12 := S.η_le q'.1
  have hDB := phi_DB S.hℓ hA0 hC20 (fun {s} hs hsℓ c t t' => gT_lip_of S.hℓ hC10 hC1 hs hsℓ c t t')
    (fun {s} hs hsℓ c t a b ha hb => gT_second_of S.hℓ hC20 hC2 hs hsℓ c t a b ha hb) hs (S.s_le_half' _)
    (cen (S.s q'.1) q'.2) (u := u) (v := v) (by linarith) (by linarith)
  have hα : ∀ w : E, ‖w‖ ≤ S.η → A / s * ‖w‖ ≤ A * S.L * S.η / sj := fun w hw => by
    calc A / s * ‖w‖ ≤ A / s * S.η := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ A * S.L * S.η / sj := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hs hsj]
        have : 0 ≤ A * S.η := by positivity
        nlinarith
  have hδ : C2 / s ^ 2 * (‖u‖ * ‖v‖) ≤ C2 * S.L ^ 2 * S.η ^ 2 / sj ^ 2 := by
    have huv : ‖u‖ * ‖v‖ ≤ S.η ^ 2 := by rw [sq]; exact mul_le_mul hu hv (norm_nonneg _) hη.le
    calc C2 / s ^ 2 * (‖u‖ * ‖v‖) ≤ C2 / s ^ 2 * S.η ^ 2 := mul_le_mul_of_nonneg_left huv (by positivity)
      _ ≤ C2 * S.L ^ 2 * S.η ^ 2 / sj ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : sj ^ 2 ≤ (S.L * s) ^ 2 := pow_le_pow_left₀ hsj.le hsc 2
        have : 0 ≤ C2 * S.η ^ 2 := by positivity
        nlinarith
  have hu' := hα u hu
  have hv' := hα v hv
  refine hDB.mono (by linarith) (by linarith) ?_
  have hprod : A / s * ‖u‖ * (A / s * ‖v‖) ≤ (A * S.L * S.η / sj) ^ 2 := by
    rw [sq]; exact mul_le_mul hu' hv' (by positivity) (by positivity)
  linarith

lemma sum_le_192 {Ts : Finset S.Idx} (hcard : Ts.card ≤ 192) {g : S.Idx → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ q' ∈ Ts, |g q'| ≤ K) : |∑ q' ∈ Ts, g q'| ≤ 192 * K := by
  refine (Domains.abs_sum_le_card (S := S) h).trans ?_
  have : (Ts.card : ℝ) ≤ 192 := by exact_mod_cast hcard
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **(ii), the second bound**: at a point `x` of the Dirichlet domain and for steps `‖u‖_∞, ‖v‖_∞ ≤ η`, the
second difference of `h_□` is at most `(1000B + 6·10⁶A²)L²η²/s_j²`. -/
theorem pu_second {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC1 : ∀ x y, |prof x - prof y| ≤ C1 * |x - y|) (hC20 : 0 ≤ C2)
    (hC2 : ∀ x a b, |prof (x + a + b) - prof (x + a) - prof (x + b) + prof x| ≤ C2 * (|a| * |b|))
    (q : S.Idx) {x : E} (hx : x ∈ D.ΩD) {u v : E} (hu : ‖u‖ ≤ S.η) (hv : ‖v‖ ≤ S.η) :
    |D.hpu q (x + u + v) - D.hpu q (x + u) - D.hpu q (x + v) + D.hpu q x| ≤
      (1000 * C2 + 6000000 * max C1 3 ^ 2) * S.L ^ 2 * S.η ^ 2 / S.s q.1 ^ 2 := by
  set A := max C1 3 with hA
  have hA0 : 0 ≤ A := le_max_of_le_right (by norm_num)
  set sj := S.s q.1 with hsj
  have hs : 0 < sj := S.s_pos _
  have hη := S.hη
  have hL := S.L_ge
  have h12 := S.η_le q.1
  set α₀ := A * S.L * S.η / sj with hα₀
  set δ₀ := C2 * S.L ^ 2 * S.η ^ 2 / sj ^ 2 with hδ₀
  have hα0 : 0 ≤ α₀ := by positivity
  have hδ0 : 0 ≤ δ₀ := by positivity
  have hrhs : (1000 * C2 + 6000000 * A ^ 2) * S.L ^ 2 * S.η ^ 2 / sj ^ 2 = 1000 * δ₀ + 6000000 * α₀ ^ 2 := by
    rw [hα₀, hδ₀]; field_simp
  rw [hrhs]
  have hR0 : 0 ≤ 1000 * δ₀ + 6000000 * α₀ ^ 2 := by positivity
  by_cases hI : D.InD q
  swap
  · simp only [hpu, if_neg hI]; simpa using hR0
  have hzero : ∀ y, S.φ q y = 0 → D.hpu q y = 0 := fun y h => by simp only [hpu, if_pos hI, h, zero_div]
  by_cases hz : S.φ q (x + u + v) = 0 ∧ S.φ q (x + u) = 0 ∧ S.φ q (x + v) = 0 ∧ S.φ q x = 0
  · obtain ⟨z1, z2, z3, z4⟩ := hz
    rw [hzero _ z1, hzero _ z2, hzero _ z3, hzero _ z4]; simpa using hR0
  -- a point near `x` where `φ_□` does not vanish; the four points lie in `□`
  have huv : ‖u + v‖ ≤ 2 * S.η := (norm_add_le u v).trans (by linarith)
  have hex : ∃ w : E, ‖w‖ ≤ 2 * S.η ∧ S.φ q (x + w) ≠ 0 := by
    simp only [not_and_or] at hz
    rcases hz with h | h | h | h
    · exact ⟨u + v, huv, by rwa [← add_assoc]⟩
    · exact ⟨u, by linarith, h⟩
    · exact ⟨v, by linarith, h⟩
    · exact ⟨0, by simp; positivity, by simpa using h⟩
  obtain ⟨w₀, hw₀, hφw₀⟩ := hex
  have hdx : ∀ w : E, dT S.hℓ (x + w) x ≤ ‖w‖ := fun w => by
    have := dT_le_norm S.hℓ (x + w) x; rwa [add_sub_cancel_left] at this
  have hin : ∀ w : E, ‖w‖ ≤ 2 * S.η → dT S.hℓ (x + w) (cen sj q.2) ≤ sj := fun w hw => by
    have t1 := dT_triangle S.hℓ (x + w) x (cen sj q.2)
    have t2 := dT_triangle S.hℓ x (x + w₀) (cen sj q.2)
    have t3 := S.dT_lt_of_φ_ne hφw₀
    rw [dT_comm S.hℓ x (x + w₀)] at t2
    have := hdx w; have := hdx w₀
    linarith
  have hN1 : ∀ w : E, ‖w‖ ≤ 2 * S.η → 1 ≤ D.N2 (x + w) := fun w hw => D.covering hx ((hdx w).trans hw)
  have hu2 : ‖u‖ ≤ 2 * S.η := by linarith
  have hv2 : ‖v‖ ≤ 2 * S.η := by linarith
  have h0 : ‖(0 : E)‖ ≤ 2 * S.η := by simp; positivity
  have e1 : x + u + v = x + (u + v) := add_assoc _ _ _
  have in1 : dT S.hℓ (x + u + v) (cen sj q.2) ≤ sj := by rw [e1]; exact hin _ huv
  have in2 := hin u hu2
  have in3 := hin v hv2
  have in4 : dT S.hℓ x (cen sj q.2) ≤ sj := by simpa using hin 0 h0
  have n1 : 1 ≤ D.N2 (x + u + v) := by rw [e1]; exact hN1 _ huv
  have n2 := hN1 u hu2
  have n3 := hN1 v hv2
  have n4 : 1 ≤ D.N2 x := by simpa using hN1 0 h0
  -- the cubes whose functions do not vanish at the four points
  set T4 := D.T (x + u + v) ∪ D.T (x + u) ∪ D.T (x + v) ∪ D.T x with hT4
  have hcard : T4.card ≤ 192 := by
    show (D.T (x + u + v) ∪ D.T (x + u) ∪ D.T (x + v) ∪ D.T x).card ≤ 192
    have c1 := D.card_T_le hI in1; have c2 := D.card_T_le hI in2
    have c3 := D.card_T_le hI in3; have c4 := D.card_T_le hI in4
    have := Finset.card_union_le (D.T (x + u + v) ∪ D.T (x + u) ∪ D.T (x + v)) (D.T x)
    have := Finset.card_union_le (D.T (x + u + v) ∪ D.T (x + u)) (D.T (x + v))
    have := Finset.card_union_le (D.T (x + u + v)) (D.T (x + u))
    omega
  have memT : ∀ q' ∈ T4, D.InD q' ∧ sj ≤ S.L * S.s q'.1 := by
    intro q' hq'
    simp only [hT4, Finset.mem_union] at hq'
    have hI' : ∀ y, q' ∈ D.T y → D.InD q' := fun y h => by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
    rcases hq' with ((h | h) | h) | h
    · exact ⟨hI' _ h, D.s_le_of_T hI in1 h⟩
    · exact ⟨hI' _ h, D.s_le_of_T hI in2 h⟩
    · exact ⟨hI' _ h, D.s_le_of_T hI in3 h⟩
    · exact ⟨hI' _ h, D.s_le_of_T hI in4 h⟩
  have hsub1 : D.T (x + u + v) ⊆ T4 := fun q' h => by simp [hT4, h]
  have hsub2 : D.T (x + u) ⊆ T4 := fun q' h => by simp [hT4, h]
  have hsub3 : D.T (x + v) ⊆ T4 := fun q' h => by simp [hT4, h]
  have hsub4 : D.T x ⊆ T4 := fun q' h => by simp [hT4, h]
  have hT4I : ∀ q' ∈ T4, D.InD q' := fun q' h => (memT q' h).1
  rw [D.N2_eq_sum T4 hT4I hsub1] at n1
  -- the bounds of the squares of the functions of these cubes
  have hsqDB : ∀ q' ∈ T4, DB (fun y => S.φ q' y ^ 2) u v (8 * α₀) (8 * α₀) (8 * δ₀ + 56 * α₀ ^ 2) := by
    intro q' hq'
    have h := Domains.φ_DB_scaled (S := S) hC10 hC1 hC20 hC2 q' hs (memT q' hq').2 hu hv
    have hf : (fun y => S.φ q' y ^ 2) = S.φ q' * S.φ q' := funext fun y => by simp [sq]
    rw [hf]
    exact (h.mul h).mono (by rw [← hα₀]; ring_nf; rfl) (by rw [← hα₀]; ring_nf; rfl)
      (by rw [← hα₀, ← hδ₀]; ring_nf; rfl)
  have hφDB := Domains.φ_DB_scaled (S := S) hC10 hC1 hC20 hC2 q hs (by nlinarith) hu hv
  rw [← hα₀, ← hδ₀] at hφDB
  have N1 := D.N2_eq_sum T4 hT4I hsub1
  have N2' := D.N2_eq_sum T4 hT4I hsub2
  have N3 := D.N2_eq_sum T4 hT4I hsub3
  have N4 := D.N2_eq_sum T4 hT4I hsub4
  set K1 := 192 * (8 * α₀) with hK1def
  have hK1 : 0 ≤ K1 := by positivity
  have d12 : |D.N2 (x + u + v) - D.N2 (x + u)| ≤ K1 := by
    rw [N1, N2', ← Finset.sum_sub_distrib]
    exact Domains.sum_le_192 (S := S) hcard (by positivity) fun q' hq' => (hsqDB q' hq').dv (x + u)
  have d13 : |D.N2 (x + u + v) - D.N2 (x + v)| ≤ K1 := by
    rw [N1, N3, ← Finset.sum_sub_distrib]
    refine Domains.sum_le_192 (S := S) hcard (by positivity) fun q' hq' => ?_
    have := (hsqDB q' hq').du (x + v)
    rwa [show x + v + u = x + u + v by abel] at this
  have d24 : |D.N2 (x + u) - D.N2 x| ≤ K1 := by
    rw [N2', N4, ← Finset.sum_sub_distrib]
    exact Domains.sum_le_192 (S := S) hcard (by positivity) fun q' hq' => (hsqDB q' hq').du x
  have d34 : |D.N2 (x + v) - D.N2 x| ≤ K1 := by
    rw [N3, N4, ← Finset.sum_sub_distrib]
    exact Domains.sum_le_192 (S := S) hcard (by positivity) fun q' hq' => (hsqDB q' hq').dv x
  have dd : |D.N2 (x + u + v) - D.N2 (x + u) - D.N2 (x + v) + D.N2 x| ≤ 192 * (8 * δ₀ + 56 * α₀ ^ 2) := by
    rw [N1, N2', N3, N4, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Domains.sum_le_192 (S := S) hcard (by positivity) fun q' hq' => (hsqDB q' hq').dd x
  -- `h_□ = φ_□ F(N²)` at the four points
  have n1' : 1 ≤ D.N2 (x + u + v) := by rw [N1]; exact n1
  have hp : ∀ y, 1 ≤ D.N2 y → D.hpu q y = S.φ q y * Fm (D.N2 y) := fun y hy => by
    simp only [hpu, if_pos hI]; exact div_max_sqrt hy
  rw [hp _ n1', hp _ n2, hp _ n3, hp _ n4]
  set a := D.N2 x
  set b := D.N2 (x + u)
  set c := D.N2 (x + v)
  set d := D.N2 (x + u + v)
  have hF : ∀ t, 1 ≤ t → 0 ≤ Fm t ∧ Fm t ≤ 1 := fun t ht =>
    ⟨Real.rpow_nonneg (by linarith) _, rpow_le_one' ht (by norm_num)⟩
  have e : S.φ q (x + u + v) * Fm d - S.φ q (x + u) * Fm b - S.φ q (x + v) * Fm c + S.φ q x * Fm a =
      (S.φ q (x + u + v) - S.φ q (x + u) - S.φ q (x + v) + S.φ q x) * Fm d +
        (S.φ q (x + u) - S.φ q x) * (Fm d - Fm b) + (S.φ q (x + v) - S.φ q x) * (Fm d - Fm c) +
        S.φ q x * (Fm d - Fm b - Fm c + Fm a) := by ring
  rw [e]
  refine (abs_add4 _ _ _ _).trans ?_
  have t1 : |(S.φ q (x + u + v) - S.φ q (x + u) - S.φ q (x + v) + S.φ q x) * Fm d| ≤ 4 * δ₀ + 12 * α₀ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (hF d n1').1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hF d n1').2).trans (hφDB.dd x)
  have tFdb : |Fm d - Fm b| ≤ 1 / 2 * K1 := (F_lip n2 n1').trans (by
    rw [abs_sub_comm] at d12; linarith [abs_sub_comm d b])
  have tFdc : |Fm d - Fm c| ≤ 1 / 2 * K1 := (F_lip n3 n1').trans (by linarith [abs_sub_comm d c])
  have t2 : |(S.φ q (x + u) - S.φ q x) * (Fm d - Fm b)| ≤ 4 * α₀ * (1 / 2 * K1) := by
    rw [abs_mul]; exact mul_le_mul (hφDB.du x) tFdb (abs_nonneg _) (by positivity)
  have t3 : |(S.φ q (x + v) - S.φ q x) * (Fm d - Fm c)| ≤ 4 * α₀ * (1 / 2 * K1) := by
    rw [abs_mul]; exact mul_le_mul (hφDB.dv x) tFdc (abs_nonneg _) (by positivity)
  have hsec := F_second n4 n2 n3 n1'
  have q1 : |c - a| * |d - c| ≤ K1 * K1 := mul_le_mul d34 d13 (abs_nonneg _) hK1
  have q2 : (d - c) ^ 2 ≤ K1 * K1 := by
    rw [← sq_abs]; rw [sq]; exact mul_le_mul d13 d13 (abs_nonneg _) hK1
  have q3 : (b - a) ^ 2 ≤ K1 * K1 := by
    rw [← sq_abs]; rw [sq]; exact mul_le_mul d24 d24 (abs_nonneg _) hK1
  have t4 : |S.φ q x * (Fm d - Fm b - Fm c + Fm a)| ≤
      1 / 2 * (192 * (8 * δ₀ + 56 * α₀ ^ 2)) + 3 / 4 * (3 * (K1 * K1)) := by
    rw [abs_mul, abs_of_nonneg (S.φ_nonneg q x)]
    refine (mul_le_of_le_one_left (abs_nonneg _) (S.φ_le_one q x)).trans (hsec.trans ?_)
    linarith
  have hK1' : K1 * K1 = 2359296 * α₀ ^ 2 := by rw [hK1def]; ring
  have p1 : 4 * α₀ * (1 / 2 * K1) = 3072 * α₀ ^ 2 := by rw [hK1def]; ring
  have hsq := sq_nonneg α₀
  linarith

end Domains

/-- **`lem:partition-of-unity`(ii).** There is a constant `C_h ≥ 1`, which depends on `L` only, such that for
every sequence of domains with the scales of `L` and every cube `□ ∈ 𝒟_j`: `|h_□(x) - h_□(x')| ≤
C_h dT(x, x')/s_j` for all points, and the second differences of `h_□` at the points of the Dirichlet domain,
with steps of at most `η`, are at most `C_h η²/s_j²` (`s_j = Ma_j`). -/
theorem partition_of_unity_ii : ∃ Ch : ℕ → ℝ, ∀ L : ℕ, 1 ≤ Ch L ∧ ∀ S : Scales, S.L = L →
    ∀ (D : Domains S) (q : S.Idx),
      (∀ x x', |D.hpu q x - D.hpu q x'| ≤ Ch L * dT S.hℓ x x' / S.s q.1) ∧
      ∀ x ∈ D.ΩD, ∀ u v : E, ‖u‖ ≤ S.η → ‖v‖ ≤ S.η →
        |D.hpu q (x + u + v) - D.hpu q (x + u) - D.hpu q (x + v) + D.hpu q x| ≤ Ch L * S.η ^ 2 / S.s q.1 ^ 2 := by
  obtain ⟨C1, hC10, hC1⟩ := prof_lip
  obtain ⟨C2, hC20, hC2⟩ := prof_second
  set A := max C1 3 with hA
  have hA0 : 0 ≤ A := le_max_of_le_right (by norm_num)
  refine ⟨fun L => 776 * A * L + 3 + (1000 * C2 + 6000000 * A ^ 2) * L ^ 2, fun L => ⟨?_, ?_⟩⟩
  · have : (0 : ℝ) ≤ 776 * A * L := by positivity
    have : (0 : ℝ) ≤ (1000 * C2 + 6000000 * A ^ 2) * L ^ 2 := by positivity
    linarith
  · intro S hSL D q
    subst hSL
    have hs := S.s_pos q.1
    have hη := S.hη
    have hX : (0 : ℝ) ≤ (1000 * C2 + 6000000 * A ^ 2) * S.L ^ 2 := by positivity
    have hY : (0 : ℝ) ≤ 776 * A * S.L + 3 := by positivity
    refine ⟨fun x x' => ?_, fun x hx u v hu hv => ?_⟩
    · have h := D.pu_lip hC10 hC1 q x x'
      have hd := dT_nonneg S.hℓ x x'
      calc _ ≤ (776 * A * S.L + 3) / S.s q.1 * dT S.hℓ x x' := h
        _ ≤ (776 * A * S.L + 3 + (1000 * C2 + 6000000 * A ^ 2) * S.L ^ 2) * dT S.hℓ x x' / S.s q.1 := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hd) hs.le
    · have h := D.pu_second hC10 hC1 hC20 hC2 q hx hu hv
      calc _ ≤ (1000 * C2 + 6000000 * A ^ 2) * S.L ^ 2 * S.η ^ 2 / S.s q.1 ^ 2 := h
        _ ≤ (776 * A * S.L + 3 + (1000 * C2 + 6000000 * A ^ 2) * S.L ^ 2) * S.η ^ 2 / S.s q.1 ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
            (by positivity)

end PartitionUnity
end CoreLean

end
