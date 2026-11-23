/-
`prop:potential` of BALABAN_CORE.tex (`a021c13be348`), the orders of vanishing, in the form of bounds. A function
*vanishes to the order `n`* at `0` (`Order f n`) if `‖f(x)‖ ≤ C‖x‖ⁿ` near `0`; for the holomorphic functions of the core
this is equivalent to the vanishing of the homogeneous parts of the orders `< n`. The rules which the core states
before the proof hold in this form: sums (`Order.add`), linear images (`Order.clm`), bilinear maps, which add the
orders (`Order.bilin`), composition with a function vanishing at `0` to the first order (`Order.comp`), and a larger
order near `0` (`Order.of_succ`). Then:

* `𝖣` vanishes to the order `2` (`D_order`, from `‖𝖣(A')‖ ≤ C₅‖A'‖²`), `T - I = -H𝖣` does, and `T` to the order `1`;
* `𝖣₃ = (𝖢 - 𝖢^{(2)}) ∘ T + 𝖢^{(2)}(T - I, T + I)` vanishes to the order `3` (`D3_order`);
* the potential `𝖵 = -⟨H𝖣₃, 𝐉⟩ - ⟨A', ΔH𝖣⟩ + ½⟨H𝖣, ΔH𝖣⟩ + 𝖵₀ ∘ T`, with the pairing a bounded bilinear map, vanishes
  to the order `3` (`V_order`);
* a holomorphic function which vanishes to the order `3` on a ball has a derivative of the order `2`:
  `‖D𝖵(x)‖ ≤ 8C‖x‖²` (`deriv_order`, by Cauchy's estimate on the ball of the radius `2‖x‖`), so that the gradient
  `𝖭`, its image under the isomorphism of the pairing, vanishes to the order `2`.
-/
import CoreLean.CauchyBanach

open Metric

noncomputable section

namespace CoreLean
namespace PotentialOrders

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup H]

/-- `f` vanishes to the order `n` at `0`. -/
def Order (f : E → F) (n : ℕ) : Prop := ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ x : E, ‖x‖ < r → ‖f x‖ ≤ C * ‖x‖ ^ n

theorem Order.add {f g : E → F} {n : ℕ} (hf : Order f n) (hg : Order g n) : Order (fun x => f x + g x) n := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  obtain ⟨C', r', hC', hr', hg⟩ := hg
  refine ⟨C + C', min r r', by positivity, lt_min hr hr', fun x hx => ?_⟩
  have h1 := hf x (lt_of_lt_of_le hx (min_le_left _ _))
  have h2 := hg x (lt_of_lt_of_le hx (min_le_right _ _))
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ C * ‖x‖ ^ n + C' * ‖x‖ ^ n := add_le_add h1 h2
    _ = (C + C') * ‖x‖ ^ n := by ring

theorem Order.neg {f : E → F} {n : ℕ} (hf : Order f n) : Order (fun x => -f x) n := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  exact ⟨C, r, hC, hr, fun x hx => by rw [norm_neg]; exact hf x hx⟩

/-- A linear image (any map with `‖Lv‖ ≤ K‖v‖`). -/
theorem Order.clm {f : E → F} {n : ℕ} (hf : Order f n) (L : F → G) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ v, ‖L v‖ ≤ K * ‖v‖) : Order (fun x => L (f x)) n := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  refine ⟨K * C, r, by positivity, hr, fun x hx => ?_⟩
  calc ‖L (f x)‖ ≤ K * ‖f x‖ := hL _
    _ ≤ K * (C * ‖x‖ ^ n) := mul_le_mul_of_nonneg_left (hf x hx) hK
    _ = K * C * ‖x‖ ^ n := by ring

/-- A bilinear map adds the orders (any map with `‖B(u, v)‖ ≤ K‖u‖‖v‖`). -/
theorem Order.bilin {f : E → F} {g : E → G} {m n : ℕ} (hf : Order f m) (hg : Order g n) (B : F → G → H) {K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ u v, ‖B u v‖ ≤ K * ‖u‖ * ‖v‖) : Order (fun x => B (f x) (g x)) (m + n) := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  obtain ⟨C', r', hC', hr', hg⟩ := hg
  refine ⟨K * C * C', min r r', by positivity, lt_min hr hr', fun x hx => ?_⟩
  have h1 := hf x (lt_of_lt_of_le hx (min_le_left _ _))
  have h2 := hg x (lt_of_lt_of_le hx (min_le_right _ _))
  calc ‖B (f x) (g x)‖ ≤ K * ‖f x‖ * ‖g x‖ := hB _ _
    _ ≤ K * (C * ‖x‖ ^ m) * (C' * ‖x‖ ^ n) := by gcongr
    _ = K * C * C' * ‖x‖ ^ (m + n) := by rw [pow_add]; ring

/-- Composition with a function `g` with `‖g(x)‖ ≤ K‖x‖` near `0`. -/
theorem Order.comp {f : F → G} {g : E → F} {n : ℕ} (hf : Order f n) {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hg : ∀ x : E, ‖x‖ < ρ → ‖g x‖ ≤ K * ‖x‖) : Order (fun x => f (g x)) n := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  refine ⟨C * K ^ n, min ρ (r / (K + 1)), by positivity, lt_min hρ (by positivity), fun x hx => ?_⟩
  have hxρ : ‖x‖ < ρ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxr : ‖x‖ < r / (K + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hgx := hg x hxρ
  have hgr : ‖g x‖ < r := by
    calc ‖g x‖ ≤ K * ‖x‖ := hgx
      _ ≤ (K + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
      _ < (K + 1) * (r / (K + 1)) := by gcongr
      _ = r := by field_simp
  calc ‖f (g x)‖ ≤ C * ‖g x‖ ^ n := hf _ hgr
    _ ≤ C * (K * ‖x‖) ^ n := by gcongr
    _ = C * K ^ n * ‖x‖ ^ n := by rw [mul_pow]; ring

/-- A larger order gives a smaller one near `0`. -/
theorem Order.of_succ {f : E → F} {n : ℕ} (hf : Order f (n + 1)) : Order f n := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  refine ⟨C, min r 1, hC, lt_min hr one_pos, fun x hx => ?_⟩
  have hx1 : ‖x‖ ≤ 1 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  calc ‖f x‖ ≤ C * ‖x‖ ^ (n + 1) := hf x (lt_of_lt_of_le hx (min_le_left _ _))
    _ ≤ C * ‖x‖ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) hx1 (Nat.le_succ n)) hC

/-- **`𝖣` vanishes to the order `2`** from `‖𝖣(A')‖ ≤ C₅‖A'‖²` on the ball. -/
theorem D_order {D : E → F} {C₅ a₃ : ℝ} (hC : 0 ≤ C₅) (ha : 0 < a₃) (hD : ∀ x : E, ‖x‖ < a₃ → ‖D x‖ ≤ C₅ * ‖x‖ ^ 2) :
    Order D 2 := ⟨C₅, a₃, hC, ha, hD⟩

/-- **`𝖣₃` vanishes to the order `3`**: `𝖣₃ = (𝖢 - 𝖢^{(2)}) ∘ T + 𝖢^{(2)}(T - I, T + I)`. -/
theorem D3_order {C3 : F → G} {B2 : F → F → G} {T : E → F} {Tm Tp : E → F} (hC3 : Order C3 3)
    {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hT : ∀ x : E, ‖x‖ < ρ → ‖T x‖ ≤ K * ‖x‖) (hTm : Order Tm 2)
    (hTp : Order Tp 1) {K2 : ℝ} (hK2 : 0 ≤ K2) (hB2 : ∀ u v, ‖B2 u v‖ ≤ K2 * ‖u‖ * ‖v‖) :
    Order (fun x => C3 (T x) + B2 (Tm x) (Tp x)) 3 :=
  (hC3.comp hK hρ hT).add (hTm.bilin hTp B2 hK2 hB2)

/-- **`𝖵` vanishes to the order `3`**: the four terms of `eq:potential`. -/
theorem V_order {t1 t2 t3 t4 : E → ℝ} (h1 : Order t1 3) (h2 : Order t2 3) (h3 : Order t3 4) (h4 : Order t4 3) :
    Order (fun x => t1 x + t2 x + t3 x + t4 x) 3 :=
  ((h1.add h2).add h3.of_succ).add h4

variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- **The derivative of a function of the order `3`**: `‖D𝖵(x)‖ ≤ 8C‖x‖²` for `2‖x‖ < r`, by Cauchy's estimate on
the ball of the radius `2‖x‖`. -/
theorem deriv_order {V : E → F} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hd : DifferentiableOn ℂ V (ball 0 r))
    (hV : ∀ x : E, ‖x‖ < r → ‖V x‖ ≤ C * ‖x‖ ^ 3) {x : E} (hx0 : x ≠ 0) (hx : 2 * ‖x‖ < r) :
    ‖fderiv ℂ V x‖ ≤ 8 * C * ‖x‖ ^ 2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set R := 2 * ‖x‖
  have hR : 0 < R := by positivity
  have hsub : ball (0 : E) R ⊆ ball 0 r := ball_subset_ball hx.le
  have hb : ∀ y ∈ ball (0 : E) R, ‖V y‖ ≤ C * R ^ 3 := fun y hy => by
    rw [mem_ball, dist_zero_right] at hy
    calc ‖V y‖ ≤ C * ‖y‖ ^ 3 := hV y (lt_trans hy hx)
      _ ≤ C * R ^ 3 := by gcongr
  have h := CauchyBanach.norm_fderiv_le hR (hd.mono hsub) hb (X := x) (by simp only [R]; linarith)
  calc ‖fderiv ℂ V x‖ ≤ 2 * (C * R ^ 3) / R := h
    _ = 8 * C * ‖x‖ ^ 2 := by simp only [R]; field_simp; ring

end PotentialOrders
end CoreLean

end
