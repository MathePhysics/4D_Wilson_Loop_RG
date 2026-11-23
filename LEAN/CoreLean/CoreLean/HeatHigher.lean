/-
The semigroup law of `P_t`, the bounds `eq:heat-higher` of the proof of `prop:free-schauder` of
BALABAN_CORE.tex, and the second remark of that proof: a difference `g(x + z) - g(x)` is at most
`|z|₁` times the largest supremum of the first differences.
-/
import CoreLean.HeatOperator

open MeasureTheory Real Balaban.LatticeGreen Filter Topology

namespace CoreLean

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε : ℝ}

/-- `P_{s+t} = P_s P_t` on bounded functions. -/
theorem heatOp_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (n : Fin 4 → ℤ) :
    heatOp ε (s + t) f n = heatOp ε s (heatOp ε t f) n := by
  set a := s / ε ^ 2
  set b := t / ε ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  set F : (Fin 4 → ℤ) × (Fin 4 → ℤ) → V := fun p =>
    (heatKernel 4 a p.1 * heatKernel 4 b p.2) • f (n - p.1 - p.2) with hF
  have hsF : Summable F := by
    refine Summable.of_norm_bounded
      (g := fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => heatKernel 4 a p.1 * heatKernel 4 b p.2 * M)
      ((Summable.mul_of_nonneg (hasSum_heatKernel4 ha).summable (hasSum_heatKernel4 hb).summable
        (heatKernel4_nonneg ha) (heatKernel4_nonneg hb)).mul_right M) fun p => ?_
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (heatKernel4_nonneg ha _)
      (heatKernel4_nonneg hb _))]
    exact mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (heatKernel4_nonneg ha _)
      (heatKernel4_nonneg hb _))
  -- the right side is the double series
  have hR : heatOp ε s (heatOp ε t f) n = ∑' p, F p := by
    unfold heatOp
    rw [hsF.tsum_prod]
    refine tsum_congr fun y => ?_
    rw [← tsum_const_smul'']
    refine tsum_congr fun z => ?_
    simp only [hF, smul_smul]
    rfl
  -- the reindexing `(y, z) ↦ (y + z, y)`
  let e : (Fin 4 → ℤ) × (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := fun q => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  have hsG : Summable (F ∘ e) := e.summable_iff.mpr hsF
  have hL : ∑' p, F p = ∑' w, (∑' y, heatKernel 4 a y * heatKernel 4 b (w - y)) • f (n - w) := by
    rw [← e.tsum_eq]
    change ∑' c, (F ∘ e) c = _
    rw [hsG.tsum_prod]
    refine tsum_congr fun w => ?_
    have hw : Summable fun y => heatKernel 4 a y * heatKernel 4 b (w - y) :=
      (hasSum_heatKernel_conv ha hb w).summable
    rw [← hw.tsum_smul_const]
    refine tsum_congr fun y => ?_
    simp only [Function.comp_apply, hF, e, Equiv.coe_fn_mk]
    congr 2
    abel
  rw [hR, hL]
  unfold heatOp
  refine tsum_congr fun w => ?_
  rw [(hasSum_heatKernel_conv ha hb w).tsum_eq, add_div]

/-- A choice of `∂_μ` (`true`) or `∂^*_μ` (`false`). -/
noncomputable def dif (ε : ℝ) (b : Bool) (μ : Fin 4) (f : (Fin 4 → ℤ) → V) :
    (Fin 4 → ℤ) → V :=
  if b then dfw ε μ f else dbw ε μ f

lemma heatOp_dif {t : ℝ} (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (b : Bool) (μ : Fin 4) : heatOp ε t (dif ε b μ f) = dif ε b μ (heatOp ε t f) := by
  funext n
  cases b
  · exact heatOp_dbw ht hf μ n
  · exact heatOp_dfw ht hf μ n

lemma norm_dif_heatOp_le (hε : 0 < ε) {t : ℝ} (ht : 0 < t) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (b : Bool) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖dif ε b μ (heatOp ε t f) n‖ ≤ c0 / Real.sqrt t * M := by
  cases b
  · exact norm_dbw_heatOp_le hε ht hf μ n
  · exact norm_dfw_heatOp_le hε ht hf μ n

lemma norm_dif_heatOp_le_holder (hε : 0 < ε) {t : ℝ} (ht : 0 < t) {β F : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (b : Bool) (μ : Fin 4)
    (n : Fin 4 → ℤ) : ‖dif ε b μ (heatOp ε t f) n‖ ≤ m1 * t ^ (-(1 - β) / 2) * F := by
  cases b
  · exact norm_dbw_heatOp_le_holder hε ht hβ0 hβ1 hF hf hhol μ n
  · exact norm_dfw_heatOp_le_holder hε ht hβ0 hβ1 hF hf hhol μ n

/-- `P_t = P_{t/2} P_{t/2}`. -/
lemma heatOp_half {t : ℝ} (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) :
    heatOp ε t f = heatOp ε (t / 2) (heatOp ε (t / 2) f) := by
  funext n
  rw [← heatOp_add (by linarith) (by linarith) hf, add_halves]

/-- `P_t = P_{t/3} P_{t/3} P_{t/3}`. -/
lemma heatOp_third {t : ℝ} (ht : 0 ≤ t) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M) :
    heatOp ε t f = heatOp ε (t / 3) (heatOp ε (t / 3) (heatOp ε (t / 3) f)) := by
  funext n
  have h3 : 0 ≤ t / 3 := by linarith
  rw [← heatOp_add h3 h3 (fun m => norm_heatOp_le h3 hf m),
    ← heatOp_add (by linarith : 0 ≤ t / 3 + t / 3) h3 hf]
  congr 1; ring

/-- `eq:heat-higher`, first bound: `‖𝒟𝒟' P_t r‖_∞ ≤ 2 c₀² t⁻¹ ‖r‖_∞`. -/
theorem norm_dif_dif_heatOp_le (hε : 0 < ε) {t : ℝ} (ht : 0 < t) {r : (Fin 4 → ℤ) → V} {M : ℝ}
    (hr : ∀ n, ‖r n‖ ≤ M) (b b' : Bool) (μ ν : Fin 4) (n : Fin 4 → ℤ) :
    ‖dif ε b μ (dif ε b' ν (heatOp ε t r)) n‖ ≤ 2 * c0 ^ 2 / t * M := by
  have h2 : 0 < t / 2 := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hr 0)
  have hg : ∀ m, ‖dif ε b' ν (heatOp ε (t / 2) r) m‖ ≤ c0 / Real.sqrt (t / 2) * M :=
    norm_dif_heatOp_le hε h2 hr b' ν
  rw [heatOp_half ht.le hr, ← heatOp_dif h2.le (fun m => norm_heatOp_le h2.le hr m)]
  calc ‖dif ε b μ (heatOp ε (t / 2) (dif ε b' ν (heatOp ε (t / 2) r))) n‖
      ≤ c0 / Real.sqrt (t / 2) * (c0 / Real.sqrt (t / 2) * M) :=
        norm_dif_heatOp_le hε h2 hg b μ n
    _ = 2 * c0 ^ 2 / t * M := by
        have := Real.sq_sqrt h2.le
        field_simp
        rw [show Real.sqrt (t / 2) ^ 2 = t / 2 from this]
        field_simp

/-- `eq:heat-higher`, second bound: `‖𝒟𝒟' P_t f‖_∞ ≤ 2 c₀ m₁ t^{-1+β/2} F`. -/
theorem norm_dif_dif_heatOp_le_holder (hε : 0 < ε) {t : ℝ} (ht : 0 < t) {β F : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β)
    (b b' : Bool) (μ ν : Fin 4) (n : Fin 4 → ℤ) :
    ‖dif ε b μ (dif ε b' ν (heatOp ε t f)) n‖ ≤ 2 * c0 * m1 * t ^ (-1 + β / 2) * F := by
  have h2 : 0 < t / 2 := by linarith
  have hg : ∀ m, ‖dif ε b' ν (heatOp ε (t / 2) f) m‖ ≤ m1 * (t / 2) ^ (-(1 - β) / 2) * F :=
    norm_dif_heatOp_le_holder hε h2 hβ0 hβ1 hF hf hhol b' ν
  rw [heatOp_half ht.le hf, ← heatOp_dif h2.le (fun m => norm_heatOp_le h2.le hf m)]
  have hsq : 1 / Real.sqrt (t / 2) = (t / 2) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h2.le]
    congr 1; ring
  have hpow : (t / 2) ^ (-(1 : ℝ) / 2) * (t / 2) ^ (-(1 - β) / 2) = (t / 2) ^ (-1 + β / 2) := by
    rw [← Real.rpow_add h2]; congr 1; ring
  have h2pow : (t / 2) ^ (-1 + β / 2) ≤ 2 * t ^ (-1 + β / 2) := by
    rw [Real.div_rpow ht.le (by norm_num), div_eq_mul_inv, mul_comm, ← Real.rpow_neg (by norm_num)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
    calc (2 : ℝ) ^ (-(-1 + β / 2)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hc := c0_pos.le
  have hm := zero_le_one.trans one_le_m1
  calc ‖dif ε b μ (heatOp ε (t / 2) (dif ε b' ν (heatOp ε (t / 2) f))) n‖
      ≤ c0 / Real.sqrt (t / 2) * (m1 * (t / 2) ^ (-(1 - β) / 2) * F) :=
        norm_dif_heatOp_le hε h2 hg b μ n
    _ = c0 * m1 * F * ((t / 2) ^ (-(1 : ℝ) / 2) * (t / 2) ^ (-(1 - β) / 2)) := by
        rw [← hsq]; ring
    _ = c0 * m1 * F * (t / 2) ^ (-1 + β / 2) := by rw [hpow]
    _ ≤ c0 * m1 * F * (2 * t ^ (-1 + β / 2)) :=
        mul_le_mul_of_nonneg_left h2pow (by positivity)
    _ = 2 * c0 * m1 * t ^ (-1 + β / 2) * F := by ring

/-- `eq:heat-higher`, third bound: `‖𝒟''𝒟𝒟' P_t f‖_∞ ≤ 6 c₀² m₁ t^{-(3-β)/2} F`. -/
theorem norm_dif_dif_dif_heatOp_le_holder (hε : 0 < ε) {t : ℝ} (ht : 0 < t) {β F : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β)
    (b b' b'' : Bool) (μ ν lam : Fin 4) (n : Fin 4 → ℤ) :
    ‖dif ε b'' lam (dif ε b μ (dif ε b' ν (heatOp ε t f))) n‖ ≤
      6 * c0 ^ 2 * m1 * t ^ (-(3 - β) / 2) * F := by
  have h3 : 0 < t / 3 := by linarith
  have hc := c0_pos.le
  have hm := zero_le_one.trans one_le_m1
  set B1 := m1 * (t / 3) ^ (-(1 - β) / 2) * F
  have hg1 : ∀ m, ‖dif ε b' ν (heatOp ε (t / 3) f) m‖ ≤ B1 :=
    norm_dif_heatOp_le_holder hε h3 hβ0 hβ1 hF hf hhol b' ν
  have hg2 : ∀ m, ‖dif ε b μ (heatOp ε (t / 3) (dif ε b' ν (heatOp ε (t / 3) f))) m‖ ≤
      c0 / Real.sqrt (t / 3) * B1 := norm_dif_heatOp_le hε h3 hg1 b μ
  have hb1 : ∀ m, ‖heatOp ε (t / 3) f m‖ ≤ M := norm_heatOp_le h3.le hf
  have hb2 : ∀ m, ‖heatOp ε (t / 3) (heatOp ε (t / 3) f) m‖ ≤ M :=
    norm_heatOp_le h3.le hb1
  rw [heatOp_third ht.le hf, ← heatOp_dif h3.le hb2, ← heatOp_dif h3.le hb1,
    ← heatOp_dif h3.le (fun m => norm_heatOp_le h3.le hg1 m)]
  have hsq : 1 / Real.sqrt (t / 3) = (t / 3) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h3.le]
    congr 1; ring
  have hpow : (t / 3) ^ (-(1 : ℝ) / 2) * ((t / 3) ^ (-(1 : ℝ) / 2) * (t / 3) ^ (-(1 - β) / 2)) =
      (t / 3) ^ (-(3 - β) / 2) := by
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]; congr 1; ring
  have h3pow : (t / 3) ^ (-(3 - β) / 2) ≤ 6 * t ^ (-(3 - β) / 2) := by
    rw [Real.div_rpow ht.le (by norm_num), div_eq_mul_inv, mul_comm, ← Real.rpow_neg (by norm_num)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
    calc (3 : ℝ) ^ (-(-(3 - β) / 2)) ≤ 3 ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ 6 := by
          rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
            ← Real.sqrt_eq_rpow]
          have : Real.sqrt 3 ≤ 2 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
          linarith
  calc ‖dif ε b'' lam (heatOp ε (t / 3) (dif ε b μ (heatOp ε (t / 3)
        (dif ε b' ν (heatOp ε (t / 3) f))))) n‖
      ≤ c0 / Real.sqrt (t / 3) * (c0 / Real.sqrt (t / 3) * B1) :=
        norm_dif_heatOp_le hε h3 hg2 b'' lam n
    _ = c0 ^ 2 * m1 * F * ((t / 3) ^ (-(1 : ℝ) / 2) * ((t / 3) ^ (-(1 : ℝ) / 2) *
          (t / 3) ^ (-(1 - β) / 2))) := by
        rw [← hsq]; simp only [B1]; ring
    _ = c0 ^ 2 * m1 * F * (t / 3) ^ (-(3 - β) / 2) := by rw [hpow]
    _ ≤ c0 ^ 2 * m1 * F * (6 * t ^ (-(3 - β) / 2)) :=
        mul_le_mul_of_nonneg_left h3pow (by positivity)
    _ = 6 * c0 ^ 2 * m1 * t ^ (-(3 - β) / 2) * F := by ring

/-- The second remark: along a coordinate, `‖g(n + j e_λ) - g(n)‖ ≤ |j| ε B` if all first
differences are bounded by `B`. -/
lemma norm_sub_coord_le (hε : 0 < ε) {g : (Fin 4 → ℤ) → V} {B : ℝ}
    (hg : ∀ lam k, ‖dfw ε lam g k‖ ≤ B) (lam : Fin 4) (n : Fin 4 → ℤ) (j : ℤ) :
    ‖g (n + j • e4 lam) - g n‖ ≤ |(j : ℝ)| * (ε * B) := by
  have hstep : ∀ k, ‖g (k + e4 lam) - g k‖ ≤ ε * B := fun k => by
    have h := hg lam k
    unfold dfw at h
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)] at h
    calc ‖g (k + e4 lam) - g k‖ = ε * (ε⁻¹ * ‖g (k + e4 lam) - g k‖) := by field_simp
      _ ≤ ε * B := mul_le_mul_of_nonneg_left h hε.le
  induction j using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have e1 : g (n + ((i : ℤ) + 1) • e4 lam) - g n =
        (g (n + (i : ℤ) • e4 lam + e4 lam) - g (n + (i : ℤ) • e4 lam)) +
          (g (n + (i : ℤ) • e4 lam) - g n) := by
      rw [add_smul, one_smul, add_assoc]; abel
    rw [e1]
    calc _ ≤ ε * B + |((i : ℤ) : ℝ)| * (ε * B) := (norm_add_le _ _).trans (add_le_add (hstep _) ih)
      _ = |(((i : ℤ) + 1 : ℤ) : ℝ)| * (ε * B) := by
          push_cast; rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; ring
  | pred i ih =>
    have e1 : g (n + (-(i : ℤ) - 1) • e4 lam) - g n =
        -(g (n + (-(i : ℤ) - 1) • e4 lam + e4 lam) - g (n + (-(i : ℤ) - 1) • e4 lam)) +
          (g (n + -(i : ℤ) • e4 lam) - g n) := by
      rw [show n + (-(i : ℤ) - 1) • e4 lam + e4 lam = n + -(i : ℤ) • e4 lam by
        rw [sub_smul, one_smul]; abel]
      abel
    rw [e1]
    calc _ ≤ ε * B + |((-(i : ℤ) : ℤ) : ℝ)| * (ε * B) :=
          (norm_add_le _ _).trans (add_le_add (by rw [norm_neg]; exact hstep _) ih)
      _ = |(((-(i : ℤ) - 1 : ℤ)) : ℝ)| * (ε * B) := by
          push_cast
          rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ i),
            show -(i : ℝ) - 1 = -((i : ℝ) + 1) by ring, abs_neg,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
          ring

/-- The second remark: `‖g(n + m) - g(n)‖ ≤ |εm|₁ B` if all first differences `∂_λ g` are bounded
by `B`. -/
theorem norm_sub_le_l1 (hε : 0 < ε) {g : (Fin 4 → ℤ) → V} {B : ℝ}
    (hg : ∀ lam k, ‖dfw ε lam g k‖ ≤ B) (n m : Fin 4 → ℤ) :
    ‖g (n + m) - g n‖ ≤ ε * l1 m * B := by
  -- telescoping over the coordinates in a finset
  have key : ∀ S : Finset (Fin 4), ∀ n : Fin 4 → ℤ,
      ‖g (n + ∑ lam ∈ S, m lam • e4 lam) - g n‖ ≤ (∑ lam ∈ S, |((m lam : ℤ) : ℝ)|) * (ε * B) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro n; simp
    | insert lam S hlam ih =>
      intro n
      rw [Finset.sum_insert hlam, Finset.sum_insert hlam]
      have e1 : g (n + (m lam • e4 lam + ∑ x ∈ S, m x • e4 x)) - g n =
          (g ((n + m lam • e4 lam) + ∑ x ∈ S, m x • e4 x) - g (n + m lam • e4 lam)) +
            (g (n + m lam • e4 lam) - g n) := by
        rw [add_assoc]; abel
      rw [e1]
      calc _ ≤ (∑ x ∈ S, |((m x : ℤ) : ℝ)|) * (ε * B) + |((m lam : ℤ) : ℝ)| * (ε * B) :=
            (norm_add_le _ _).trans (add_le_add (ih _) (norm_sub_coord_le hε hg lam n (m lam)))
        _ = _ := by ring
  have hm : ∑ lam : Fin 4, m lam • e4 lam = m := by
    ext μ
    simp [e4, Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ n
  rw [hm] at this
  calc ‖g (n + m) - g n‖ ≤ (∑ lam : Fin 4, |((m lam : ℤ) : ℝ)|) * (ε * B) := this
    _ = ε * l1 m * B := by unfold l1; ring

end CoreLean
