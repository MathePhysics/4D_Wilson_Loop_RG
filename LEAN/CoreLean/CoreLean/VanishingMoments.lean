/-
`lem:vanishing-moments` of BALABAN_CORE.tex (`ba2f40296da0`): kernels with vanishing moments. For `δ > 0`, `m ≥ 1`, and
`K : ℤ⁴ → E` with `‖K(z)‖ ≤ C_K e^{-δ|z|₁}` and `Σ_z z^α K(z) = 0` for `|α| ≤ m - 1`, there are `K_α`, `|α| = m`, with
`‖K_α(z)‖ ≤ (8/(1 - e^{-δ}))^{5m} C_K e^{-δ|z|₁}` and `K = Σ_{|α| = m} ∂^α K_α`, `(∂_μ f)(z) = f(z) - f(z - e_μ)`.

The proof is the core's. The operator `S_k` sums out the coordinate `k` and puts the sum at `z_k = 0`, so that the core's
`P_k = S_k ∘ P_{k-1}`; `g_k = P_{k-1}f - P_kf` has zero sums along the lines of the direction `k`, and
`G_k(z) = Σ_{w ≤ z_k} g_k(z[k ↦ w])` has `∂_kG_k = g_k`, the decay of `g_k`, and moments vanishing to one order less
(summation by parts against `s(t) - s(t + 1) = t^a`, `s = -B_{a+1}/(a + 1)` with the Bernoulli polynomial).
-/
import Mathlib

open Real

noncomputable section

namespace CoreLean
namespace VanishingMoments

/-- The points of `ℤ⁴`. -/
abbrev Z4 := Fin 4 → ℤ

/-- `|z|₁`. -/
def n1 (z : Z4) : ℝ := ∑ i, |(z i : ℝ)|

lemma n1_nonneg (z : Z4) : 0 ≤ n1 z := Finset.sum_nonneg fun _ _ => abs_nonneg _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `‖f(z)‖ ≤ Ce^{-δ|z|₁}`. -/
def Decay (δ C : ℝ) (f : Z4 → E) : Prop := ∀ z, ‖f z‖ ≤ C * Real.exp (-δ * n1 z)

/-- The monomial `z^α`. -/
def mono (α : Fin 4 → ℕ) (z : Z4) : ℝ := ∏ i, (z i : ℝ) ^ α i

/-- The moment `Σ_z z^α f(z)`. -/
def Mom (f : Z4 → E) (α : Fin 4 → ℕ) : E := ∑' z, mono α z • f z

/-- The moments of the orders `|α| < d` vanish. -/
def VanMom (f : Z4 → E) (d : ℕ) : Prop := ∀ α : Fin 4 → ℕ, ∑ i, α i < d → Mom f α = 0

lemma Decay.nonneg {δ C : ℝ} {f : Z4 → E} (hf : Decay δ C f) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hf 0)
  exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)

lemma Decay.mono_const {δ C C' : ℝ} {f : Z4 → E} (hf : Decay δ C f) (h : C ≤ C') : Decay δ C' f := fun z =>
  (hf z).trans (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)

/-- `e^{-δ|n|} = (e^{-δ})^n`. -/
lemma exp_abs_nat (δ : ℝ) (n : ℕ) : Real.exp (-δ * |((n : ℤ) : ℝ)|) = Real.exp (-δ) ^ n := by
  rw [← Real.exp_nat_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]; ring_nf

lemma norm_exp_neg_lt_one {δ : ℝ} (hδ : 0 < δ) : ‖Real.exp (-δ)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.2 (by linarith)

/-- `t ↦ |t|^a e^{-δ|t|}` is summable over `ℤ`. -/
lemma summable_abs_pow_exp (a : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun t : ℤ => |(t : ℝ)| ^ a * Real.exp (-δ * |(t : ℝ)|)) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) a (norm_exp_neg_lt_one hδ)
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine h0.congr fun n => ?_
    rw [exp_abs_nat, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
  · have h1 := (summable_nat_add_iff 1).2 h0
    refine h1.congr fun n => ?_
    have e : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [e, ← Real.exp_nat_mul]; ring_nf

/-- A product of nonnegative summable functions of the coordinates is summable over `ℤⁿ`. -/
lemma summable_pi_prod : ∀ (n : ℕ) (φ : Fin n → ℤ → ℝ), (∀ i t, 0 ≤ φ i t) → (∀ i, Summable (φ i)) →
    Summable (fun z : Fin n → ℤ => ∏ i, φ i (z i))
  | 0, φ, _, _ => by simpa using (Summable.of_finite (f := fun _ : Fin 0 → ℤ => (1 : ℝ)))
  | n + 1, φ, h0, hs => by
    have ih := summable_pi_prod n (fun i => φ i.succ) (fun i t => h0 _ t) (fun i => hs _)
    have hm := Summable.mul_of_nonneg (hs 0) ih (fun t => h0 0 t) (fun z => Finset.prod_nonneg fun i _ => h0 _ _)
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).summable_iff]
    refine hm.congr fun x => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- `z ↦ |z^α|e^{-δ|z|₁}` is summable over `ℤ⁴`. -/
lemma summable_mono_exp (α : Fin 4 → ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun z : Z4 => |mono α z| * Real.exp (-δ * n1 z)) := by
  have h := summable_pi_prod 4 (fun i t => |(t : ℝ)| ^ α i * Real.exp (-δ * |(t : ℝ)|))
    (fun i t => by positivity) (fun i => summable_abs_pow_exp (α i) hδ)
  refine h.congr fun z => ?_
  rw [mono, Finset.abs_prod, n1, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_pow]

/-- The moments of a decaying function are absolutely summable. -/
lemma summable_mom {δ C : ℝ} {f : Z4 → E} (hf : Decay δ C f) (hδ : 0 < δ) (α : Fin 4 → ℕ) :
    Summable (fun z => mono α z • f z) := by
  refine Summable.of_norm_bounded (g := fun z => C * (|mono α z| * Real.exp (-δ * n1 z)))
    ((summable_mono_exp α hδ).mul_left C) fun z => ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc |mono α z| * ‖f z‖ ≤ |mono α z| * (C * Real.exp (-δ * n1 z)) :=
        mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)
    _ = C * (|mono α z| * Real.exp (-δ * n1 z)) := by ring

lemma summable_of_decay {δ C : ℝ} {f : Z4 → E} (hf : Decay δ C f) (hδ : 0 < δ) : Summable f := by
  have h := summable_mom hf hδ 0
  simpa [mono] using h

/-! ### Geometric sums on `ℤ`, with `r = e^{-δ}` and `q = (1 - r)⁻¹` -/

/-- `Σ_{w ∈ ℤ} e^{-δ|w|} ≤ 2(1 - e^{-δ})⁻¹`. -/
lemma tsum_exp_abs_le {δ : ℝ} (hδ : 0 < δ) :
    ∑' w : ℤ, Real.exp (-δ * |(w : ℝ)|) ≤ 2 * (1 - Real.exp (-δ))⁻¹ := by
  set r := Real.exp (-δ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg := hasSum_geometric_of_lt_one hr0 hr1
  have h1 : HasSum (fun n : ℕ => Real.exp (-δ * |((n : ℤ) : ℝ)|)) (1 - r)⁻¹ :=
    hg.congr_fun fun n => exp_abs_nat δ n
  have h2 : HasSum (fun n : ℕ => Real.exp (-δ * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)) (r * (1 - r)⁻¹) := by
    refine (hg.mul_left r).congr_fun fun n => ?_
    have e : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [e, ← pow_succ', ← Real.exp_nat_mul]; ring_nf
  rw [(HasSum.of_nat_of_neg_add_one (f := fun w : ℤ => Real.exp (-δ * |(w : ℝ)|)) h1 h2).tsum_eq]
  have : 0 < 1 - r := by linarith
  have hq : 0 ≤ (1 - r)⁻¹ := by positivity
  nlinarith

lemma summable_exp_abs {δ : ℝ} (hδ : 0 < δ) : Summable (fun w : ℤ => Real.exp (-δ * |(w : ℝ)|)) := by
  simpa using summable_abs_pow_exp 0 hδ

/-- `Σ_{w > t} e^{-δ|w|} ≤ (1 - e^{-δ})⁻¹e^{-δt}` for `t ≥ 0`. -/
lemma tail_upper {δ : ℝ} (hδ : 0 < δ) {t : ℤ} (ht : 0 ≤ t) :
    ∑' w : ℤ, (if t < w then Real.exp (-δ * |(w : ℝ)|) else 0) ≤ (1 - Real.exp (-δ))⁻¹ * Real.exp (-δ * |(t : ℝ)|) := by
  set r := Real.exp (-δ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set g : ℕ → ℤ := fun n => t + 1 + n
  have hg : Function.Injective g := fun a b h => by simpa [g] using h
  have hsupp : Function.support (fun w : ℤ => if t < w then Real.exp (-δ * |(w : ℝ)|) else 0) ⊆ Set.range g := by
    intro w hw
    have hw' : t < w := by by_contra h; simp [h] at hw
    exact ⟨(w - t - 1).toNat, by simp only [g]; omega⟩
  rw [← hg.tsum_eq hsupp]
  have hval : ∀ n : ℕ, (if t < g n then Real.exp (-δ * |((g n : ℤ) : ℝ)|) else 0) =
      Real.exp (-δ * ((t : ℝ) + 1)) * r ^ n := by
    intro n
    have h1 : t < g n := by simp only [g]; omega
    rw [if_pos h1, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [g]; push_cast
    rw [abs_of_nonneg (by positivity)]; ring
  simp only [hval]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, abs_of_nonneg (show (0 : ℝ) ≤ t by exact_mod_cast ht)]
  have h1 : Real.exp (-δ * ((t : ℝ) + 1)) ≤ Real.exp (-δ * t) := Real.exp_le_exp.2 (by nlinarith)
  have h2 : 0 ≤ (1 - r)⁻¹ := (inv_pos.2 (by linarith)).le
  calc Real.exp (-δ * ((t : ℝ) + 1)) * (1 - r)⁻¹ ≤ Real.exp (-δ * t) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := mul_comm _ _

/-- `Σ_{w ≤ t} e^{-δ|w|} ≤ (1 - e^{-δ})⁻¹e^{-δ|t|}` for `t < 0`. -/
lemma tail_lower {δ : ℝ} (hδ : 0 < δ) {t : ℤ} (ht : t < 0) :
    ∑' w : ℤ, (if w ≤ t then Real.exp (-δ * |(w : ℝ)|) else 0) ≤ (1 - Real.exp (-δ))⁻¹ * Real.exp (-δ * |(t : ℝ)|) := by
  set r := Real.exp (-δ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set g : ℕ → ℤ := fun n => t - n
  have hg : Function.Injective g := fun a b h => by simpa [g] using h
  have hsupp : Function.support (fun w : ℤ => if w ≤ t then Real.exp (-δ * |(w : ℝ)|) else 0) ⊆ Set.range g := by
    intro w hw
    have hw' : w ≤ t := by by_contra h; simp [h] at hw
    exact ⟨(t - w).toNat, by simp only [g]; omega⟩
  rw [← hg.tsum_eq hsupp]
  have htR : (t : ℝ) < 0 := by exact_mod_cast ht
  have hval : ∀ n : ℕ, (if g n ≤ t then Real.exp (-δ * |((g n : ℤ) : ℝ)|) else 0) =
      Real.exp (-δ * |(t : ℝ)|) * r ^ n := by
    intro n
    have h1 : g n ≤ t := by simp only [g]; omega
    rw [if_pos h1, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [g]; push_cast
    rw [abs_of_neg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]), abs_of_neg htR]; ring
  simp only [hval]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mul_comm]

/-! ### The lines of a direction -/

/-- `|z[k ↦ w]|₁ + |z_k| = |z|₁ + |w|`. -/
lemma n1_update (z : Z4) (k : Fin 4) (w : ℤ) : n1 (Function.update z k w) + |(z k : ℝ)| = n1 z + |(w : ℝ)| := by
  have h1 := Finset.add_sum_erase Finset.univ (fun i => |((Function.update z k w i : ℤ) : ℝ)|) (Finset.mem_univ k)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => |((z i : ℤ) : ℝ)|) (Finset.mem_univ k)
  have h3 : ∑ i ∈ Finset.univ.erase k, |((Function.update z k w i : ℤ) : ℝ)| =
      ∑ i ∈ Finset.univ.erase k, |((z i : ℤ) : ℝ)| :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self] at h1
  unfold n1
  linarith

/-- The bound of `g` along a line of the direction `k`. -/
lemma line_bound {δ C : ℝ} {g : Z4 → E} (hg : Decay δ C g) (z : Z4) (k : Fin 4) (w : ℤ) :
    ‖g (Function.update z k w)‖ ≤ C * Real.exp (-δ * (n1 z - |(z k : ℝ)|)) * Real.exp (-δ * |(w : ℝ)|) := by
  have h := hg (Function.update z k w)
  have e : n1 (Function.update z k w) = (n1 z - |(z k : ℝ)|) + |(w : ℝ)| := by linarith [n1_update z k w]
  rw [e, mul_add, Real.exp_add, ← mul_assoc] at h
  exact h

/-- The restriction of a decaying function to a line, cut by a condition, is summable. -/
lemma summable_line {δ C : ℝ} (hδ : 0 < δ) {g : Z4 → E} (hg : Decay δ C g) (z : Z4) (k : Fin 4) (P : ℤ → Prop)
    [DecidablePred P] : Summable (fun w : ℤ => if P w then g (Function.update z k w) else 0) := by
  refine Summable.of_norm_bounded (g := fun w : ℤ =>
    C * Real.exp (-δ * (n1 z - |(z k : ℝ)|)) * Real.exp (-δ * |(w : ℝ)|)) ((summable_exp_abs hδ).mul_left _) fun w => ?_
  split_ifs
  · exact line_bound hg z k w
  · rw [norm_zero]; have := hg.nonneg; positivity

/-- `S_kh(z) = 1{z_k = 0}Σ_w h(z[k ↦ w])`. -/
def Sop (k : Fin 4) (h : Z4 → E) (z : Z4) : E := if z k = 0 then ∑' w : ℤ, h (Function.update z k w) else 0

/-- `‖S_kh(z)‖ ≤ 2(1 - e^{-δ})⁻¹Ce^{-δ|z|₁}`. -/
lemma decay_Sop {δ C : ℝ} (hδ : 0 < δ) {h : Z4 → E} (hh : Decay δ C h) (k : Fin 4) :
    Decay δ (2 * (1 - Real.exp (-δ))⁻¹ * C) (Sop k h) := by
  intro z
  have hC := hh.nonneg
  have hq : 0 ≤ (1 - Real.exp (-δ))⁻¹ := (inv_pos.2 (by linarith [Real.exp_lt_one_iff.2 (by linarith : -δ < 0)])).le
  unfold Sop
  split_ifs with hz
  · have hs := ((summable_exp_abs hδ).mul_left (C * Real.exp (-δ * (n1 z - |(z k : ℝ)|))))
    refine (tsum_of_norm_bounded hs.hasSum fun w => line_bound hh z k w).trans ?_
    rw [tsum_mul_left, hz]
    simp only [Int.cast_zero, abs_zero, sub_zero]
    have hb := tsum_exp_abs_le hδ
    calc C * Real.exp (-δ * n1 z) * ∑' w : ℤ, Real.exp (-δ * |(w : ℝ)|)
        ≤ C * Real.exp (-δ * n1 z) * (2 * (1 - Real.exp (-δ))⁻¹) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * (1 - Real.exp (-δ))⁻¹ * C * Real.exp (-δ * n1 z) := by ring
  · rw [norm_zero]; positivity

/-! ### Splitting off the coordinate `k` -/

lemma split_update (k : Fin 4) (t w : ℤ) (y : { j // j ≠ k } → ℤ) :
    Function.update ((Equiv.funSplitAt k ℤ).symm (t, y)) k w = (Equiv.funSplitAt k ℤ).symm (w, y) := by
  funext j
  by_cases h : j = k
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, Function.update_of_ne h, h]

lemma split_apply_k (k : Fin 4) (t : ℤ) (y : { j // j ≠ k } → ℤ) :
    (Equiv.funSplitAt k ℤ).symm (t, y) k = t := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

/-- `Σ_z F(z) = Σ_y Σ_w F(y, w)`, the coordinate `k` split off. -/
lemma tsum_split {F : Z4 → E} (hF : Summable F) (k : Fin 4) :
    ∑' z, F z = ∑' y : { j // j ≠ k } → ℤ, ∑' w : ℤ, F ((Equiv.funSplitAt k ℤ).symm (w, y)) := by
  set e : ({ j // j ≠ k } → ℤ) × ℤ ≃ Z4 := (Equiv.prodComm _ _).trans (Equiv.funSplitAt k ℤ).symm
  have he : ∀ p, e p = (Equiv.funSplitAt k ℤ).symm (p.2, p.1) := fun p => rfl
  rw [← e.tsum_eq]
  have hs : Summable (F ∘ e) := e.summable_iff.2 hF
  rw [show (∑' c, F (e c)) = ∑' p, (F ∘ e) p from rfl, hs.tsum_prod' fun y => hs.prod_factor y]
  rfl

/-- `Σ_z 1{z_k = 0}X(z) = Σ_y X(y, 0)`. -/
lemma tsum_slice (X : Z4 → E) (k : Fin 4) :
    ∑' z, (if z k = 0 then X z else 0) = ∑' y : { j // j ≠ k } → ℤ, X ((Equiv.funSplitAt k ℤ).symm (0, y)) := by
  set g : ({ j // j ≠ k } → ℤ) → Z4 := fun y => (Equiv.funSplitAt k ℤ).symm (0, y)
  have hg : Function.Injective g := fun a b hab => by
    have := congrArg (Equiv.funSplitAt k ℤ) hab
    simp only [g, Equiv.apply_symm_apply, Prod.mk.injEq] at this
    exact this.2
  have hsupp : Function.support (fun z : Z4 => if z k = 0 then X z else 0) ⊆ Set.range g := by
    intro z hz
    have hz0 : z k = 0 := by by_contra h; simp [h] at hz
    refine ⟨((Equiv.funSplitAt k ℤ) z).2, ?_⟩
    simp only [g]
    rw [← hz0]
    have : ((Equiv.funSplitAt k ℤ) z).1 = z k := rfl
    rw [← this, Prod.mk.eta, Equiv.symm_apply_apply]
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr fun y => ?_
  simp only [g, split_apply_k, if_pos]

/-- `z^α` does not depend on `z_k` if `α_k = 0`. -/
lemma mono_update {α : Fin 4 → ℕ} {k : Fin 4} (hα : α k = 0) (z : Z4) (w : ℤ) :
    mono α (Function.update z k w) = mono α z := by
  unfold mono
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = k
  · subst h; simp [hα]
  · rw [Function.update_of_ne h]

/-- **The moments of `S_kh`**: `Σ_z z^αS_kh(z)` is `Σ_z z^αh(z)` if `α_k = 0`, and zero otherwise. -/
lemma mom_Sop {δ C : ℝ} (hδ : 0 < δ) {h : Z4 → E} (hh : Decay δ C h) (k : Fin 4) (α : Fin 4 → ℕ) :
    Mom (Sop k h) α = if α k = 0 then Mom h α else 0 := by
  unfold Mom
  split_ifs with hα
  · have e1 : ∀ z, mono α z • Sop k h z = if z k = 0 then mono α z • ∑' w : ℤ, h (Function.update z k w) else 0 := by
      intro z; unfold Sop; split_ifs <;> simp
    simp only [e1]
    rw [tsum_slice (fun z => mono α z • ∑' w : ℤ, h (Function.update z k w)) k,
      tsum_split (summable_mom hh hδ α) k]
    refine tsum_congr fun y => ?_
    simp only [split_update]
    have hsum : Summable (fun w : ℤ => h ((Equiv.funSplitAt k ℤ).symm (w, y))) := by
      have := summable_line hδ hh ((Equiv.funSplitAt k ℤ).symm (0, y)) k (fun _ => True)
      simpa [split_update] using this
    rw [← hsum.tsum_const_smul]
    refine tsum_congr fun w => ?_
    rw [← split_update k 0 w y, mono_update hα]
  · have e1 : ∀ z, mono α z • Sop k h z = 0 := by
      intro z; unfold Sop
      split_ifs with hz
      · have : mono α z = 0 := by
          unfold mono
          exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hz]; simp [hα])
        rw [this, zero_smul]
      · exact smul_zero _
    simp [e1]

/-- `G(z) = Σ_{w ≤ z_k} g(z[k ↦ w])`. -/
def Gop (k : Fin 4) (g : Z4 → E) (z : Z4) : E := ∑' w : ℤ, if w ≤ z k then g (Function.update z k w) else 0

/-- The backward difference `(∂_kf)(z) = f(z) - f(z - e_k)`. -/
def dk (k : Fin 4) (f : Z4 → E) (z : Z4) : E := f z - f (z - Pi.single k 1)

lemma update_sub_single (z : Z4) (k : Fin 4) (w : ℤ) :
    Function.update (z - Pi.single k 1) k w = Function.update z k w := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h, h]

/-- `∂_kG = g`. -/
lemma dk_Gop {δ C : ℝ} (hδ : 0 < δ) {g : Z4 → E} (hg : Decay δ C g) (k : Fin 4) : dk k (Gop k g) = g := by
  funext z
  unfold dk Gop
  have hk : ((z - Pi.single k 1 : Z4) k) = z k - 1 := by simp
  simp only [update_sub_single, hk]
  rw [← (summable_line hδ hg z k (· ≤ z k)).tsum_sub (summable_line hδ hg z k (· ≤ z k - 1))]
  have e : ∀ w : ℤ, ((if w ≤ z k then g (Function.update z k w) else 0) -
      (if w ≤ z k - 1 then g (Function.update z k w) else 0)) = if w = z k then g (Function.update z k w) else 0 := by
    intro w
    by_cases h1 : w = z k
    · subst h1; simp
    · by_cases h2 : w ≤ z k - 1
      · rw [if_pos (by omega), if_pos h2, if_neg h1, sub_self]
      · rw [if_neg (by omega), if_neg h2, if_neg h1, sub_zero]
  simp only [e]
  rw [tsum_ite_eq (z k) (fun w => g (Function.update z k w)), Function.update_eq_self]

/-- `Σ_{w ≤ t} = -Σ_{w > t}` along a line with the sum zero. -/
lemma Gop_eq_neg {δ C : ℝ} (hδ : 0 < δ) {g : Z4 → E} (hg : Decay δ C g) (k : Fin 4) (z : Z4)
    (h0 : ∑' w : ℤ, g (Function.update z k w) = 0) :
    Gop k g z = -∑' w : ℤ, if z k < w then g (Function.update z k w) else 0 := by
  have hsum := (summable_line hδ hg z k (· ≤ z k)).tsum_add (summable_line hδ hg z k (z k < ·))
  have e : ∀ w : ℤ, ((if w ≤ z k then g (Function.update z k w) else 0) +
      (if z k < w then g (Function.update z k w) else 0)) = g (Function.update z k w) := by
    intro w
    by_cases h : w ≤ z k
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  simp only [e] at hsum
  rw [h0] at hsum
  unfold Gop
  exact eq_neg_of_add_eq_zero_left hsum.symm

/-- **The decay of `G`**: `‖G(z)‖ ≤ (1 - e^{-δ})⁻¹Ce^{-δ|z|₁}` if the sums of `g` along the lines vanish. -/
lemma decay_Gop {δ C : ℝ} (hδ : 0 < δ) {g : Z4 → E} (hg : Decay δ C g) (k : Fin 4)
    (h0 : ∀ z, ∑' w : ℤ, g (Function.update z k w) = 0) :
    Decay δ ((1 - Real.exp (-δ))⁻¹ * C) (Gop k g) := by
  intro z
  have hC := hg.nonneg
  set A := C * Real.exp (-δ * (n1 z - |(z k : ℝ)|))
  have hA : 0 ≤ A := by positivity
  have hfin : A * ((1 - Real.exp (-δ))⁻¹ * Real.exp (-δ * |(z k : ℝ)|)) =
      (1 - Real.exp (-δ))⁻¹ * C * Real.exp (-δ * n1 z) := by
    simp only [A]
    have h2 : Real.exp (-δ * (n1 z - |(z k : ℝ)|)) * Real.exp (-δ * |(z k : ℝ)|) = Real.exp (-δ * n1 z) := by
      rw [← Real.exp_add]; ring_nf
    calc C * Real.exp (-δ * (n1 z - |(z k : ℝ)|)) * ((1 - Real.exp (-δ))⁻¹ * Real.exp (-δ * |(z k : ℝ)|)) =
          (1 - Real.exp (-δ))⁻¹ * C * (Real.exp (-δ * (n1 z - |(z k : ℝ)|)) * Real.exp (-δ * |(z k : ℝ)|)) := by ring
      _ = _ := by rw [h2]
  by_cases hz : 0 ≤ z k
  · rw [Gop_eq_neg hδ hg k z (h0 z), norm_neg]
    have hs : Summable (fun w : ℤ => if z k < w then Real.exp (-δ * |(w : ℝ)|) else 0) :=
      Summable.of_nonneg_of_le (fun w => by split_ifs <;> positivity)
        (fun w => by split_ifs <;> simp [(Real.exp_pos _).le]) (summable_exp_abs hδ)
    have hb : ∀ w : ℤ, ‖if z k < w then g (Function.update z k w) else 0‖ ≤
        A * (if z k < w then Real.exp (-δ * |(w : ℝ)|) else 0) := by
      intro w; split_ifs
      · exact line_bound hg z k w
      · simp
    refine (tsum_of_norm_bounded (hs.mul_left A).hasSum hb).trans ?_
    rw [tsum_mul_left, ← hfin]
    exact mul_le_mul_of_nonneg_left (tail_upper hδ hz) hA
  · push_neg at hz
    unfold Gop
    have hs : Summable (fun w : ℤ => if w ≤ z k then Real.exp (-δ * |(w : ℝ)|) else 0) :=
      Summable.of_nonneg_of_le (fun w => by split_ifs <;> positivity)
        (fun w => by split_ifs <;> simp [(Real.exp_pos _).le]) (summable_exp_abs hδ)
    have hb : ∀ w : ℤ, ‖if w ≤ z k then g (Function.update z k w) else 0‖ ≤
        A * (if w ≤ z k then Real.exp (-δ * |(w : ℝ)|) else 0) := by
      intro w; split_ifs
      · exact line_bound hg z k w
      · simp
    refine (tsum_of_norm_bounded (hs.mul_left A).hasSum hb).trans ?_
    rw [tsum_mul_left, ← hfin]
    exact mul_le_mul_of_nonneg_left (tail_lower hδ hz) hA

/-! ### The moments of `G`: summation by parts -/

/-- The coefficients of `s = -B_{a+1}/(a + 1)`, `B_{a+1}` the Bernoulli polynomial. -/
def bc (a j : ℕ) : ℝ := -(((Polynomial.bernoulli (a + 1)).coeff j : ℚ) : ℝ) / ((a : ℝ) + 1)

lemma bernoulli_natDegree_lt (n : ℕ) : (Polynomial.bernoulli n).natDegree < n + 1 := by
  rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [Polynomial.coeff_bernoulli, if_neg (by omega)]

/-- **`s(t) - s(t + 1) = t^a`** for `s(t) = Σ_{j < a + 2} c_jt^j`, from `B_n(1 + x) = B_n(x) + nx^{n-1}`. -/
lemma bern_diff (a : ℕ) (t : ℤ) :
    ∑ j ∈ Finset.range (a + 2), bc a j * (t : ℝ) ^ j - ∑ j ∈ Finset.range (a + 2), bc a j * ((t : ℝ) + 1) ^ j =
      (t : ℝ) ^ a := by
  have h := Polynomial.bernoulli_eval_one_add (a + 1) (t : ℚ)
  rw [Polynomial.eval_eq_sum_range' (bernoulli_natDegree_lt (a + 1)),
    Polynomial.eval_eq_sum_range' (bernoulli_natDegree_lt (a + 1))] at h
  have hR := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, Rat.cast_one,
    Rat.cast_natCast, Nat.add_sub_cancel] at hR
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  unfold bc
  have e1 : ∀ x : ℝ, ∑ j ∈ Finset.range (a + 2), -(((Polynomial.bernoulli (a + 1)).coeff j : ℚ) : ℝ) / ((a : ℝ) + 1) * x ^ j =
      -(∑ j ∈ Finset.range (a + 2), (((Polynomial.bernoulli (a + 1)).coeff j : ℚ) : ℝ) * x ^ j) / ((a : ℝ) + 1) := by
    intro x
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e1, show (t : ℝ) + 1 = 1 + t by ring, hR]
  field_simp
  push_cast
  ring

/-- `(Σ_jc_jm_j)v = Σ_jc_j(m_jv)`. -/
lemma sum_mul_smul (s : Finset ℕ) (c m : ℕ → ℝ) (v : E) :
    (∑ j ∈ s, c j * m j) • v = ∑ j ∈ s, c j • (m j • v) := by
  rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]

/-- `|z - e_k|₁ ≥ |z|₁ - 1`, so a translate by `e_k` keeps the decay with the constant multiplied by `e^δ`. -/
lemma decay_translate {δ C : ℝ} (hδ : 0 < δ) {G : Z4 → E} (hG : Decay δ C G) (k : Fin 4) :
    Decay δ (C * Real.exp δ) (fun z => G (z - Pi.single k 1)) := by
  intro z
  have hC := hG.nonneg
  have hz : z - Pi.single k 1 = Function.update z k (z k - 1) := by
    funext j; by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  have hn := n1_update z k (z k - 1)
  rw [← hz] at hn
  have habs : |(z k : ℝ)| ≤ |(((z k - 1 : ℤ)) : ℝ)| + 1 := by
    push_cast
    have := abs_sub_abs_le_abs_sub (z k : ℝ) ((z k : ℝ) - 1)
    rw [show (z k : ℝ) - ((z k : ℝ) - 1) = 1 by ring, abs_one] at this
    linarith
  have hle : -δ * n1 (z - Pi.single k 1) ≤ δ + -δ * n1 z := by nlinarith
  calc ‖G (z - Pi.single k 1)‖ ≤ C * Real.exp (-δ * n1 (z - Pi.single k 1)) := hG _
    _ ≤ C * Real.exp (δ + -δ * n1 z) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hC
    _ = C * Real.exp δ * Real.exp (-δ * n1 z) := by rw [Real.exp_add]; ring

lemma mono_update_mul (α : Fin 4 → ℕ) (k : Fin 4) (j : ℕ) (z : Z4) :
    mono (Function.update α k j) z = mono (Function.update α k 0) z * (z k : ℝ) ^ j := by
  unfold mono
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun i => (z i : ℝ) ^ Function.update α k 0 i) (Finset.mem_univ k)]
  simp only [Function.update_self, pow_zero, one_mul]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
    Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma sum_update (α : Fin 4 → ℕ) (k : Fin 4) (j : ℕ) :
    ∑ i, Function.update α k j i + α k = ∑ i, α i + j := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update α k j) (Finset.mem_univ k)
  have h2 := Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
  have h3 : ∑ i ∈ Finset.univ.erase k, Function.update α k j i = ∑ i ∈ Finset.univ.erase k, α i :=
    Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  simp only [Function.update_self] at h1
  omega

/-- **The moments of `G`** vanish to one order less than those of `g`: for `|α| ≤ d - 2`, with `a = α_k`,
`z^α = z^{α'}(s(z_k) - s(z_k + 1))` (`α'` with `α'_k = 0`), and the shift `z ↦ z - e_k` in the second sum gives
`Σ_zz^{α'}s(z_k)(∂_kG)(z) = Σ_j c_j Σ_z z^{α'}z_k^j g(z)`, moments of `g` of the orders at most `|α| + 1 < d`. -/
lemma vanmom_Gop {δ C CG : ℝ} (hδ : 0 < δ) {g : Z4 → E} (hg : Decay δ C g) (k : Fin 4)
    (hG : Decay δ CG (Gop k g)) {d : ℕ} (hm : VanMom g d) : VanMom (Gop k g) (d - 1) := by
  intro α hα
  set a := α k with ha
  set β : ℕ → Fin 4 → ℕ := fun j => Function.update α k j with hβ
  set e : Z4 := Pi.single k 1 with he
  set G := Gop k g with hGdef
  have hGe := decay_translate hδ hG k
  -- the two sums
  set A : Z4 → E := fun z => (∑ j ∈ Finset.range (a + 2), bc a j * mono (β j) z) • G z with hA
  set Y : Z4 → E := fun z => (∑ j ∈ Finset.range (a + 2), bc a j * mono (β j) z) • G (z - e) with hY
  have hAs : Summable A := by
    have : A = fun z => ∑ j ∈ Finset.range (a + 2), bc a j • (mono (β j) z • G z) := by
      funext z; exact sum_mul_smul _ _ _ _
    rw [this]
    exact summable_sum fun j _ => (summable_mom hG hδ (β j)).const_smul _
  have hYs : Summable Y := by
    have : Y = fun z => ∑ j ∈ Finset.range (a + 2), bc a j • (mono (β j) z • G (z - e)) := by
      funext z; exact sum_mul_smul _ _ _ _
    rw [this]
    exact summable_sum fun j _ => (summable_mom hGe hδ (β j)).const_smul _
  -- the pointwise identity `z^αG(z) = A(z) - Y(z + e_k)`
  have hβ0 : ∀ z, mono (β 0) (z + e) = mono (β 0) z := by
    intro z
    have hz : z + e = Function.update z k (z k + 1) := by
      funext j; by_cases h : j = k
      · subst h; simp [he]
      · simp [he, Function.update_of_ne h, h]
    rw [hz, mono_update (by simp [hβ])]
  have hpt : ∀ z, mono α z • G z = A z - Y (z + e) := by
    intro z
    simp only [hA, hY, add_sub_cancel_right]
    rw [← sub_smul]
    congr 1
    have hk1 : (z + e) k = z k + 1 := by simp [he]
    have hb := bern_diff a (z k)
    have hα' : mono α z = mono (Function.update α k 0) z * (z k : ℝ) ^ a := by
      rw [← mono_update_mul, Function.update_eq_self]
    have hβ0' : mono (Function.update α k 0) (z + e) = mono (Function.update α k 0) z := by
      have := hβ0 z; simpa [hβ] using this
    have hs1 : ∑ j ∈ Finset.range (a + 2), bc a j * mono (β j) z =
        mono (Function.update α k 0) z * ∑ j ∈ Finset.range (a + 2), bc a j * (z k : ℝ) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        show bc a j * mono (Function.update α k j) z = _
        rw [mono_update_mul α k j z]; ring
    have hs2 : ∑ j ∈ Finset.range (a + 2), bc a j * mono (β j) (z + e) =
        mono (Function.update α k 0) z * ∑ j ∈ Finset.range (a + 2), bc a j * ((z k : ℝ) + 1) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        show bc a j * mono (Function.update α k j) (z + e) = _
        rw [mono_update_mul α k j (z + e), hβ0', hk1]; push_cast; ring
    rw [hs1, hs2, ← mul_sub, hb, hα']
  -- the moment
  unfold Mom
  simp only [hpt]
  have hYe : Summable (fun z => Y (z + e)) := (Equiv.addRight e).summable_iff.2 hYs
  rw [hAs.tsum_sub hYe, show (∑' z, Y (z + e)) = ∑' z, Y z from (Equiv.addRight e).tsum_eq Y,
    ← hAs.tsum_sub hYs]
  have hdiff : ∀ z, A z - Y z = ∑ j ∈ Finset.range (a + 2), bc a j • (mono (β j) z • g z) := by
    intro z
    simp only [hA, hY]
    rw [← smul_sub, ← sum_mul_smul]
    congr 1
    have := congrFun (dk_Gop hδ hg k) z
    simp only [dk] at this
    rw [hGdef, he, this]
  simp only [hdiff]
  rw [Summable.tsum_finsetSum fun j _ => (summable_mom hg hδ (β j)).const_smul _]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [(summable_mom hg hδ (β j)).tsum_const_smul]
  have hord : ∑ i, β j i < d := by
    have := sum_update α k j
    have hj' : j < a + 2 := Finset.mem_range.1 hj
    simp only [hβ]
    omega
  have h0 := hm (β j) hord
  unfold Mom at h0
  rw [h0, smul_zero]

/-! ### One difference -/

/-- `q = (1 - e^{-δ})⁻¹`. -/
def qd (δ : ℝ) : ℝ := (1 - Real.exp (-δ))⁻¹

lemma qd_ge_one {δ : ℝ} (hδ : 0 < δ) : 1 ≤ qd δ := by
  have h1 : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h0 : 0 < Real.exp (-δ) := Real.exp_pos _
  unfold qd
  rw [one_le_inv₀ (by linarith)]
  linarith

/-- The core's `P_k`: `P_0f = f`, `P_{k+1}f = S_k P_kf`. -/
def Pop (f : Z4 → E) : ℕ → Z4 → E
  | 0 => f
  | k + 1 => if hk : k < 4 then Sop ⟨k, hk⟩ (Pop f k) else Pop f k

lemma Pop_succ (f : Z4 → E) (k : Fin 4) : Pop f (k.val + 1) = Sop k (Pop f k.val) := by
  simp [Pop, k.isLt]

lemma decay_Pop {δ C : ℝ} (hδ : 0 < δ) {f : Z4 → E} (hf : Decay δ C f) :
    ∀ k, k ≤ 4 → Decay δ ((2 * qd δ) ^ k * C) (Pop f k)
  | 0, _ => by simpa [Pop] using hf
  | k + 1, hk => by
    have h := decay_Sop hδ (decay_Pop hδ hf k (by omega)) ⟨k, by omega⟩
    rw [show Pop f (k + 1) = Sop ⟨k, by omega⟩ (Pop f k) from Pop_succ f ⟨k, by omega⟩]
    refine h.mono_const (le_of_eq ?_)
    unfold qd; ring

lemma vanmom_Pop {δ C : ℝ} (hδ : 0 < δ) {f : Z4 → E} (hf : Decay δ C f) {d : ℕ} (hm : VanMom f d) :
    ∀ k, k ≤ 4 → VanMom (Pop f k) d
  | 0, _ => by simpa [Pop] using hm
  | k + 1, hk => by
    intro α hα
    rw [show Pop f (k + 1) = Sop ⟨k, by omega⟩ (Pop f k) from Pop_succ f ⟨k, by omega⟩,
      mom_Sop hδ (decay_Pop hδ hf k (by omega)) ⟨k, by omega⟩ α]
    split_ifs
    · exact vanmom_Pop hδ hf hm k (by omega) α hα
    · rfl

/-- `P_kf(z) = 0` unless `z_1 = ⋯ = z_k = 0`. -/
lemma Pop_support (f : Z4 → E) : ∀ k, k ≤ 4 → ∀ z, Pop f k z ≠ 0 → ∀ i : Fin 4, i.val < k → z i = 0
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, z, hz, i, hi => by
    rw [show Pop f (k + 1) = Sop ⟨k, by omega⟩ (Pop f k) from Pop_succ f ⟨k, by omega⟩] at hz
    unfold Sop at hz
    split_ifs at hz with hz0
    · obtain ⟨w, hw⟩ : ∃ w, Pop f k (Function.update z ⟨k, by omega⟩ w) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hz (by simp [h])
      by_cases hik : i.val = k
      · have : i = ⟨k, by omega⟩ := Fin.ext hik
        rw [this]; exact hz0
      · have h1 := Pop_support f k (by omega) _ hw i (by omega)
        rwa [Function.update_of_ne (fun h => hik (by rw [h]))] at h1
    · exact absurd rfl hz

/-- `P_4f = (Σf)1{z = 0} = 0` when the sum of `f` vanishes. -/
lemma Pop_four {δ C : ℝ} (hδ : 0 < δ) {f : Z4 → E} (hf : Decay δ C f) {d : ℕ} (hd : 1 ≤ d) (hm : VanMom f d) :
    Pop f 4 = 0 := by
  have hz : ∀ z, Pop f 4 z ≠ 0 → z = 0 := fun z h => funext fun i => Pop_support f 4 le_rfl z h i i.isLt
  have h0 := vanmom_Pop hδ hf hm 4 le_rfl 0 (by simp; omega)
  unfold Mom at h0
  simp only [mono, pow_zero, Pi.zero_apply, Finset.prod_const_one, one_smul] at h0
  rw [tsum_eq_single 0 fun z hz0 => by by_contra h; exact hz0 (hz z h)] at h0
  funext z
  by_cases hz0 : z = 0
  · rw [hz0, h0]; rfl
  · by_contra h; exact hz0 (hz z h)

/-- **One difference**: a decaying `f` whose moments of the orders `< d` vanish, `d ≥ 1`, is `Σ_k ∂_kG_k` with
`‖G_k(z)‖ ≤ 24q⁵Ce^{-δ|z|₁}` and the moments of `G_k` of the orders `< d - 1` vanishing. Here `G_k` is the line sum of
`g_k = P_kf - P_{k+1}f`, and `Σ_kg_k = P_0f - P_4f = f`. -/
theorem one_difference {δ C : ℝ} (hδ : 0 < δ) {f : Z4 → E} (hf : Decay δ C f) {d : ℕ} (hd : 1 ≤ d)
    (hm : VanMom f d) :
    ∃ G : Fin 4 → Z4 → E, (∀ k, Decay δ (24 * qd δ ^ 5 * C) (G k)) ∧ (∀ k, VanMom (G k) (d - 1)) ∧
      f = ∑ k, dk k (G k) := by
  have hq := qd_ge_one hδ
  have hC := hf.nonneg
  set g : Fin 4 → Z4 → E := fun k => Pop f k.val - Pop f (k.val + 1) with hg
  have hgS : ∀ k, g k = Pop f k.val - Sop k (Pop f k.val) := fun k => by simp only [hg, Pop_succ]
  -- the decay of `g_k`
  have hgd : ∀ k : Fin 4, Decay δ ((2 * qd δ) ^ k.val * (1 + 2 * qd δ) * C) (g k) := by
    intro k z
    have h1 := decay_Pop hδ hf k.val (by omega) z
    have h2 := decay_Pop hδ hf (k.val + 1) (by omega) z
    calc ‖g k z‖ = ‖Pop f k.val z - Pop f (k.val + 1) z‖ := rfl
      _ ≤ ‖Pop f k.val z‖ + ‖Pop f (k.val + 1) z‖ := norm_sub_le _ _
      _ ≤ (2 * qd δ) ^ k.val * C * Real.exp (-δ * n1 z) + (2 * qd δ) ^ (k.val + 1) * C * Real.exp (-δ * n1 z) :=
          add_le_add h1 h2
      _ = (2 * qd δ) ^ k.val * (1 + 2 * qd δ) * C * Real.exp (-δ * n1 z) := by ring
  -- the sums of `g_k` along the lines of the direction `k` vanish
  have hline : ∀ (k : Fin 4) z, ∑' w : ℤ, g k (Function.update z k w) = 0 := by
    intro k z
    have hPd := decay_Pop hδ hf k.val (by omega)
    have hs1 : Summable (fun w : ℤ => Pop f k.val (Function.update z k w)) := by
      simpa using summable_line hδ hPd z k (fun _ => True)
    set c := ∑' w' : ℤ, Pop f k.val (Function.update z k w')
    have hS : ∀ w : ℤ, Sop k (Pop f k.val) (Function.update z k w) = if w = 0 then c else 0 := by
      intro w
      unfold Sop
      simp only [Function.update_self, Function.update_idem]
      rfl
    have hs2 : Summable (fun w : ℤ => Sop k (Pop f k.val) (Function.update z k w)) := by
      simp only [hS]; exact (hasSum_ite_eq 0 c).summable
    simp only [hgS, Pi.sub_apply]
    rw [hs1.tsum_sub hs2]
    simp only [hS]
    rw [tsum_ite_eq, sub_self]
  -- the moments of `g_k`
  have hgm : ∀ k : Fin 4, VanMom (g k) d := by
    intro k α hα
    have hPd := decay_Pop hδ hf k.val (by omega)
    have hSd := decay_Sop hδ hPd k
    unfold Mom
    simp only [hgS, Pi.sub_apply, smul_sub]
    rw [(summable_mom hPd hδ α).tsum_sub (summable_mom hSd hδ α)]
    have h1 := vanmom_Pop hδ hf hm k.val (by omega) α hα
    have h2 := mom_Sop hδ hPd k α
    unfold Mom at h1 h2
    rw [h2, h1]
    split_ifs <;> simp
  refine ⟨fun k => Gop k (g k), fun k => ?_, fun k => ?_, ?_⟩
  · -- `q(2q)^k(1 + 2q) ≤ 24q⁵` for `k ≤ 3`
    refine (decay_Gop hδ (hgd k) k (hline k)).mono_const ?_
    have hk : k.val ≤ 3 := by omega
    have hpow : (2 * qd δ) ^ k.val ≤ (2 * qd δ) ^ 3 := pow_le_pow_right₀ (by linarith) hk
    have h3 : 1 + 2 * qd δ ≤ 3 * qd δ := by linarith
    calc (1 - Real.exp (-δ))⁻¹ * ((2 * qd δ) ^ k.val * (1 + 2 * qd δ) * C)
        = qd δ * (2 * qd δ) ^ k.val * (1 + 2 * qd δ) * C := by unfold qd; ring
      _ ≤ qd δ * (2 * qd δ) ^ 3 * (3 * qd δ) * C := by gcongr
      _ = 24 * qd δ ^ 5 * C := by ring
  · exact vanmom_Gop hδ (hgd k) k (decay_Gop hδ (hgd k) k (hline k)) (hgm k)
  · -- `Σ_k ∂_kG_k = Σ_k g_k = P_0f - P_4f = f`
    simp only [dk_Gop hδ (hgd _)]
    rw [Fin.sum_univ_eq_sum_range (fun k => Pop f k - Pop f (k + 1)) 4, Finset.sum_range_sub',
      Pop_four hδ hf hd hm, sub_zero]
    rfl

/-! ### The iteration and the multi-indices -/

/-- `∂_k` as a linear map. -/
def dkL (k : Fin 4) : Module.End ℝ (Z4 → E) where
  toFun := dk k
  map_add' f g := by funext z; simp only [dk, Pi.add_apply]; abel
  map_smul' c f := by funext z; simp [dk, smul_sub]

lemma dk_sum {ι : Type*} (s : Finset ι) (k : Fin 4) (H : ι → Z4 → E) :
    dk k (∑ i ∈ s, H i) = ∑ i ∈ s, dk k (H i) :=
  map_sum (dkL k) H s

/-- `∂_{κ_0}∂_{κ_1}⋯∂_{κ_{m-1}}`. -/
def Dl : ∀ m : ℕ, (Fin m → Fin 4) → (Z4 → E) → Z4 → E
  | 0, _, F => F
  | m + 1, κ, F => dk (κ 0) (Dl m (Fin.tail κ) F)

/-- **The iteration**: a decaying `f` whose moments of the orders `< m` vanish is `Σ_κ ∂_{κ_0}⋯∂_{κ_{m-1}}F_κ` over the
`4^m` words `κ`, with `‖F_κ(z)‖ ≤ (24q⁵)^mCe^{-δ|z|₁}`. -/
theorem iterate_difference {δ : ℝ} (hδ : 0 < δ) : ∀ (m : ℕ) {C : ℝ} {f : Z4 → E}, Decay δ C f → VanMom f m →
    ∃ F : (Fin m → Fin 4) → Z4 → E, (∀ κ, Decay δ ((24 * qd δ ^ 5) ^ m * C) (F κ)) ∧ f = ∑ κ, Dl m κ (F κ)
  | 0, C, f, hf, _ => ⟨fun _ => f, fun _ => by simpa using hf, by simp [Dl]⟩
  | m + 1, C, f, hf, hm => by
    obtain ⟨G, hGd, hGm, hfG⟩ := one_difference hδ hf (by omega) hm
    choose F hFd hFe using fun k => iterate_difference hδ m (hGd k) (by simpa using hGm k)
    refine ⟨fun κ => F (κ 0) (Fin.tail κ), fun κ => (hFd (κ 0) (Fin.tail κ)).mono_const (le_of_eq (by ring)), ?_⟩
    have e1 : ∀ k, dk k (G k) = ∑ κ, dk k (Dl m κ (F k κ)) := fun k => by
      conv_lhs => rw [hFe k]
      exact dk_sum _ _ _
    rw [hfG, Finset.sum_congr rfl fun k _ => e1 k,
      ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 4)).sum_comp, Fintype.sum_prod_type]
    simp [Dl, Fin.consEquiv, Fin.tail_cons, Fin.cons_zero]

/-- The differences commute. -/
lemma dkL_comm (i j : Fin 4) : Commute (dkL (E := E) i) (dkL j) := by
  refine LinearMap.ext fun F => funext fun z => ?_
  simp only [Module.End.mul_apply, dkL, LinearMap.coe_mk, AddHom.coe_mk, dk]
  rw [sub_right_comm z]
  abel

/-- `∂^α = ∂_1^{α_1}∂_2^{α_2}∂_3^{α_3}∂_4^{α_4}`. -/
def dpow (α : Fin 4 → ℕ) : Module.End ℝ (Z4 → E) := dkL 0 ^ α 0 * (dkL 1 ^ α 1 * (dkL 2 ^ α 2 * dkL 3 ^ α 3))

/-- `∂_i∂^α = ∂^{α + e_i}`. -/
lemma dkL_dpow (i : Fin 4) (α : Fin 4 → ℕ) :
    dkL i * dpow (E := E) α = dpow (Function.update α i (α i + 1)) := by
  have c : ∀ a b : Fin 4, ∀ n : ℕ, dkL (E := E) a * dkL b ^ n = dkL b ^ n * dkL a :=
    fun a b n => ((dkL_comm a b).pow_right n).eq
  fin_cases i <;> simp only [dpow, Function.update_self, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1), Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3), Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2), Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
    Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0), Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
    Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3), Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
    Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1), Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
    pow_succ']
  · rw [← mul_assoc]
  · rw [← mul_assoc, c 1 0, mul_assoc, ← mul_assoc (dkL 1) (dkL 1 ^ α 1)]
  · rw [← mul_assoc, c 2 0, mul_assoc, ← mul_assoc (dkL 2) (dkL 1 ^ α 1), c 2 1, mul_assoc,
      ← mul_assoc (dkL 2) (dkL 2 ^ α 2)]
  · rw [← mul_assoc, c 3 0, mul_assoc, ← mul_assoc (dkL 3) (dkL 1 ^ α 1), c 3 1, mul_assoc,
      ← mul_assoc (dkL 3) (dkL 2 ^ α 2), c 3 2, mul_assoc]

/-- The multi-index of a word: `α_i = #{j | κ_j = i}`. -/
def ktype {m : ℕ} (κ : Fin m → Fin 4) : Fin 4 → ℕ := fun i => ∑ j, if κ j = i then 1 else 0

lemma ktype_cons {m : ℕ} (k : Fin 4) (κ : Fin m → Fin 4) :
    ktype (Fin.cons k κ : Fin (m + 1) → Fin 4) = Function.update (ktype κ) k (ktype κ k + 1) := by
  funext i
  simp only [ktype, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases h : i = k
  · subst h; simp; ring
  · rw [Function.update_of_ne h, if_neg (Ne.symm h), zero_add]
    rfl

lemma sum_ktype {m : ℕ} (κ : Fin m → Fin 4) : ∑ i, ktype κ i = m := by
  simp only [ktype]
  rw [Finset.sum_comm]
  simp

/-- `∂_{κ_0}⋯∂_{κ_{m-1}} = ∂^α` with the multi-index `α` of `κ`: the differences commute. -/
lemma Dl_eq_dpow : ∀ (m : ℕ) (κ : Fin m → Fin 4) (F : Z4 → E), Dl m κ F = dpow (ktype κ) F
  | 0, κ, F => by
    have : ktype κ = 0 := funext fun i => by simp [ktype]
    rw [this]; simp [Dl, dpow]
  | m + 1, κ, F => by
    have hκ : κ = Fin.cons (κ 0) (Fin.tail κ) := (Fin.cons_self_tail κ).symm
    rw [Dl, Dl_eq_dpow m (Fin.tail κ) F]
    conv_rhs => rw [hκ, ktype_cons, ← dkL_dpow]
    rfl

/-- **`lem:vanishing-moments`**: for `δ > 0`, `m ≥ 0`, and `K : ℤ⁴ → E` with `‖K(z)‖ ≤ C_Ke^{-δ|z|₁}` whose moments
`Σ_zz^αK(z)` of the orders `|α| ≤ m - 1` vanish, there are `K_α` with `‖K_α(z)‖ ≤ (8/(1 - e^{-δ}))^{5m}C_Ke^{-δ|z|₁}` and
`K = Σ_{|α| = m}∂^αK_α`, `(∂_μf)(z) = f(z) - f(z - e_μ)`. `K_α` is the sum of the `F_κ` of `iterate_difference` over the
words `κ` of the multi-index `α`, at most `4^m` of them, and `4^m(24q⁵)^m ≤ (8q)^{5m}`. -/
theorem vanishing_moments {δ : ℝ} (hδ : 0 < δ) (m : ℕ) {C : ℝ} {K : Z4 → E} (hK : Decay δ C K)
    (hmom : VanMom K m) :
    ∃ Kα : (Fin 4 → ℕ) → Z4 → E, (∀ α, Decay δ ((8 / (1 - Real.exp (-δ))) ^ (5 * m) * C) (Kα α)) ∧
      K = ∑ α ∈ Finset.Nat.antidiagonalTuple 4 m, dpow α (Kα α) := by
  obtain ⟨F, hFd, hKF⟩ := iterate_difference hδ m hK hmom
  have hq := qd_ge_one hδ
  have hC := hK.nonneg
  refine ⟨fun α => ∑ κ ∈ Finset.univ.filter (fun κ => ktype κ = α), F κ, fun α z => ?_, ?_⟩
  · -- the bound
    set s := Finset.univ.filter (fun κ : Fin m → Fin 4 => ktype κ = α)
    have hcard : (s.card : ℝ) ≤ 4 ^ m := by
      have : s.card ≤ 4 ^ m := (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hB : 0 ≤ (24 * qd δ ^ 5) ^ m * C * Real.exp (-δ * n1 z) := by positivity
    show ‖(∑ κ ∈ s, F κ) z‖ ≤ _
    calc ‖(∑ κ ∈ s, F κ) z‖ ≤ ∑ κ ∈ s, ‖F κ z‖ := by
          rw [Finset.sum_apply]; exact norm_sum_le _ _
      _ ≤ ∑ _κ ∈ s, (24 * qd δ ^ 5) ^ m * C * Real.exp (-δ * n1 z) := Finset.sum_le_sum fun κ _ => hFd κ z
      _ = s.card * ((24 * qd δ ^ 5) ^ m * C * Real.exp (-δ * n1 z)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 ^ m * ((24 * qd δ ^ 5) ^ m * C * Real.exp (-δ * n1 z)) := mul_le_mul_of_nonneg_right hcard hB
      _ = (96 * qd δ ^ 5) ^ m * C * Real.exp (-δ * n1 z) := by
          rw [show (96 : ℝ) = 4 * 24 by norm_num, mul_pow, mul_pow, mul_pow]; ring
      _ ≤ ((8 * qd δ) ^ 5) ^ m * C * Real.exp (-δ * n1 z) := by
          gcongr
          nlinarith [pow_pos (show (0 : ℝ) < qd δ by linarith) 5]
      _ = (8 / (1 - Real.exp (-δ))) ^ (5 * m) * C * Real.exp (-δ * n1 z) := by
          rw [pow_mul, qd, div_eq_mul_inv]
  · -- the grouping by the multi-indices
    rw [hKF]
    simp only [Dl_eq_dpow, map_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Nat.antidiagonalTuple 4 m) (g := ktype)
      (fun κ _ => Finset.Nat.mem_antidiagonalTuple.2 (sum_ktype κ))]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun κ hκ => by rw [(Finset.mem_filter.1 hκ).2]

end VanishingMoments
end CoreLean

end
