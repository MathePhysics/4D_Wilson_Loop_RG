/-
The sums of the lattice heat kernels (unit spacing) behind the constants of `lem:heat-kernel` of
BALABAN_CORE.tex: the total variation `Σ_n |q(n+1) - q(n)| = 2q(0)` (`eq:heat-gradient`), the weighted
total variation `Σ_n |n| |q(n+1) - q(n)| = 1`, the first moment `Σ_n |n| q(n) ≤ √(2t)`, and the
corresponding sums of the four-dimensional kernel `p_t(z) = Π_μ q_t(z_μ)`.
-/
import CoreLean.HeatSemigroup
import CoreLean.Vendor.LatticeGreen

open MeasureTheory Real Balaban.LatticeGreen Filter Topology

namespace CoreLean

section OneDim

variable {t : ℝ}

lemma heatKernel1_summable (ht : 0 ≤ t) : Summable fun n : ℤ => heatKernel1 t n :=
  (hasSum_heatKernel1 ht).summable

/-- `q_t(n) → 0` along `ℕ`. -/
lemma tendsto_heatKernel1_nat (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => heatKernel1 t n) atTop (𝓝 0) := by
  have h := (heatKernel1_summable ht).tendsto_cofinite_zero
  exact h.comp (Nat.cast_injective.tendsto_cofinite.mono_left Nat.cofinite_eq_atTop.symm.le)

/-- On `ℕ`, `|q(n+1) - q(n)| = q(n) - q(n+1)`. -/
lemma abs_diff_nat (ht : 0 ≤ t) (n : ℕ) :
    |heatKernel1 t ((n : ℤ) + 1) - heatKernel1 t n| = heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1) := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (heatKernel1_antitone ht (Int.natCast_nonneg n)))]

/-- `Σ_{n ≥ 0} (q(n) - q(n+1)) = q(0)`. -/
lemma hasSum_telescope_nat (ht : 0 ≤ t) :
    HasSum (fun n : ℕ => heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1)) (heatKernel1 t 0) := by
  have hnn : ∀ n : ℕ, 0 ≤ heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1) := fun n =>
    sub_nonneg.mpr (heatKernel1_antitone ht (Int.natCast_nonneg n))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1)) =
      heatKernel1 t 0 - heatKernel1 t N := fun N => by
    have h := Finset.sum_range_sub' (fun n : ℕ => heatKernel1 t (n : ℤ)) N
    rw [Nat.cast_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Nat.cast_succ]
  simp_rw [hpart]
  have h := (tendsto_heatKernel1_nat ht).const_sub (heatKernel1 t 0)
  rw [sub_zero] at h
  exact h

/-- `eq:heat-gradient` (unit spacing): `Σ_n |q(n+1) - q(n)| = 2 q(0)`. -/
theorem hasSum_abs_diff (ht : 0 ≤ t) :
    HasSum (fun n : ℤ => |heatKernel1 t (n + 1) - heatKernel1 t n|) (2 * heatKernel1 t 0) := by
  have h1 : HasSum (fun n : ℕ => |heatKernel1 t ((n : ℤ) + 1) - heatKernel1 t n|)
      (heatKernel1 t 0) :=
    (hasSum_telescope_nat ht).congr_fun fun n => abs_diff_nat ht n
  have h2 : HasSum (fun n : ℕ => |heatKernel1 t (-((n : ℤ) + 1) + 1) - heatKernel1 t (-((n : ℤ) + 1))|)
      (heatKernel1 t 0) := by
    refine h1.congr_fun fun n => ?_
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, heatKernel1_neg, heatKernel1_neg, abs_sub_comm]
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => |heatKernel1 t (n + 1) - heatKernel1 t n|) h1 h2
  rw [← two_mul] at h
  exact h

/-- `Σ_n n² q_t(n)` gives `|n| q_t(n) ≤ n² q_t(n)`-summability of the first moment. -/
lemma summable_abs_mul (ht : 0 ≤ t) : Summable fun n : ℤ => |(n : ℝ)| * heatKernel1 t n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (heatKernel1_nonneg ht n))
    (fun n => ?_) ((hasSum_sq_heatKernel1 ht).summable.add (heatKernel1_summable ht))
  have hq := heatKernel1_nonneg ht n
  -- `|n| ≤ n² + 1`
  have : |(n : ℝ)| ≤ (n : ℝ) ^ 2 + 1 := by nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
  nlinarith

/-- `Σ_n |n| q_t(n) ≤ √(2t)`, from `|n| ≤ n²/(2a) + a/2` with `a = √(2t)`. -/
theorem tsum_abs_mul_le (ht : 0 ≤ t) :
    ∑' n : ℤ, |(n : ℝ)| * heatKernel1 t n ≤ Real.sqrt (2 * t) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    rw [tsum_eq_single 0 (fun n hn => by simp [heatKernel1_zero, hn])]
    simp
  set a := Real.sqrt (2 * t) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  have hle : ∀ n : ℤ, |(n : ℝ)| * heatKernel1 t n ≤
      (n : ℝ) ^ 2 * heatKernel1 t n / (2 * a) + a / 2 * heatKernel1 t n := fun n => by
    have hq := heatKernel1_nonneg ht n
    have h : |(n : ℝ)| ≤ (n : ℝ) ^ 2 / (2 * a) + a / 2 := by
      have e : (n : ℝ) ^ 2 / (2 * a) + a / 2 - |(n : ℝ)| = (|(n : ℝ)| - a) ^ 2 / (2 * a) := by
        rw [← sq_abs (n : ℝ)]; field_simp; ring
      have : 0 ≤ (|(n : ℝ)| - a) ^ 2 / (2 * a) := by positivity
      linarith
    calc |(n : ℝ)| * heatKernel1 t n ≤ ((n : ℝ) ^ 2 / (2 * a) + a / 2) * heatKernel1 t n :=
          mul_le_mul_of_nonneg_right h hq
      _ = _ := by ring
  have hs2 := (hasSum_sq_heatKernel1 ht).div_const (2 * a)
  have hs0 := (hasSum_heatKernel1 ht).mul_left (a / 2)
  calc ∑' n : ℤ, |(n : ℝ)| * heatKernel1 t n
      ≤ ∑' n : ℤ, ((n : ℝ) ^ 2 * heatKernel1 t n / (2 * a) + a / 2 * heatKernel1 t n) :=
        (summable_abs_mul ht).tsum_le_tsum hle (hs2.add hs0).summable
    _ = 2 * t / (2 * a) + a / 2 * 1 := (hs2.add hs0).tsum_eq
    _ = a := by rw [← ha2]; field_simp [ha0.ne']; ring

/-- The weighted total variation `Σ_n |n| |q(n+1) - q(n)| = Σ_n q(n) = 1`. -/
theorem hasSum_abs_mul_abs_diff (ht : 0 ≤ t) :
    HasSum (fun n : ℤ => |(n : ℝ)| * |heatKernel1 t (n + 1) - heatKernel1 t n|) 1 := by
  -- on `ℕ`: `Σ n (q n - q(n+1)) = Σ_{n ≥ 1} q n`; on the negative integers:
  -- `Σ (n+1)(q n - q(n+1)) = Σ_{n ≥ 0} q n`
  have hsq : Summable fun n : ℕ => (n : ℝ) * heatKernel1 t n := by
    have := ((summable_abs_mul ht).comp_injective Nat.cast_injective)
    exact this.congr fun n => by simp
  have hq : Summable fun n : ℕ => heatKernel1 t n :=
    (heatKernel1_summable ht).comp_injective Nat.cast_injective
  -- the sum over `ℕ`: with `A = Σ n q(n)` and `B = Σ q(n+1)`,
  -- `Σ (n+1) q(n+1) = A`, so `Σ n q(n+1) = A - B` and `Σ n (q n - q(n+1)) = B`
  have hA : HasSum (fun n : ℕ => (n : ℝ) * (heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1)))
      (∑' n : ℕ, heatKernel1 t ((n : ℤ) + 1)) := by
    set A := ∑' n : ℕ, (n : ℝ) * heatKernel1 t n
    set B := ∑' n : ℕ, heatKernel1 t ((n : ℤ) + 1)
    have hshA : HasSum (fun n : ℕ => ((n : ℝ) + 1) * heatKernel1 t ((n : ℤ) + 1)) A := by
      have := (hasSum_nat_add_iff' 1).mpr hsq.hasSum
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero] at this
      exact this.congr_fun fun n => by push_cast; ring
    have hshB : HasSum (fun n : ℕ => heatKernel1 t ((n : ℤ) + 1)) B := by
      have hs : Summable fun n : ℕ => heatKernel1 t ((n : ℤ) + 1) :=
        ((summable_nat_add_iff 1).mpr hq).congr fun n => by push_cast; rfl
      exact hs.hasSum
    have hAB : HasSum (fun n : ℕ => (n : ℝ) * heatKernel1 t ((n : ℤ) + 1)) (A - B) :=
      (hshA.sub hshB).congr_fun fun n => by ring
    have := hsq.hasSum.sub hAB
    rw [sub_sub_cancel] at this
    exact this.congr_fun fun n => by ring
  have hB : HasSum (fun n : ℕ => ((n : ℝ) + 1) * (heatKernel1 t n - heatKernel1 t ((n : ℤ) + 1)))
      (∑' n : ℕ, heatKernel1 t n) := by
    have hA' := hA.add (hasSum_telescope_nat ht)
    have : ∑' n : ℕ, heatKernel1 t ((n : ℤ) + 1) + heatKernel1 t 0 = ∑' n : ℕ, heatKernel1 t n := by
      rw [hq.tsum_eq_zero_add]; push_cast; ring
    rw [this] at hA'
    exact hA'.congr_fun fun n => by ring
  have h1 : HasSum (fun n : ℕ => |((n : ℤ) : ℝ)| * |heatKernel1 t ((n : ℤ) + 1) - heatKernel1 t n|)
      (∑' n : ℕ, heatKernel1 t ((n : ℤ) + 1)) :=
    hA.congr_fun fun n => by rw [abs_diff_nat ht]; simp
  have h2 : HasSum (fun n : ℕ => |((-((n : ℤ) + 1) : ℤ) : ℝ)| *
      |heatKernel1 t (-((n : ℤ) + 1) + 1) - heatKernel1 t (-((n : ℤ) + 1))|)
      (∑' n : ℕ, heatKernel1 t n) := by
    refine hB.congr_fun fun n => ?_
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, heatKernel1_neg, heatKernel1_neg, abs_sub_comm,
      abs_diff_nat ht]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => |(n : ℝ)| * |heatKernel1 t (n + 1) - heatKernel1 t n|) h1 h2
  -- `Σ_{n≥0} q(n+1) + Σ_{n ≥ 0} q(n) = Σ_ℤ q = 1`
  have htot : ∑' n : ℕ, heatKernel1 t ((n : ℤ) + 1) + ∑' n : ℕ, heatKernel1 t n = 1 := by
    have hz := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => heatKernel1 t n) hq.hasSum
      ((hq.comp_injective (add_left_injective 1)).hasSum.congr_fun fun n => by
        simp only [Function.comp_apply]; push_cast
        rw [← heatKernel1_neg]; congr 1)
    have := hz.unique (hasSum_heatKernel1 ht)
    rw [← this]
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  rw [← htot]
  exact h

end OneDim

section FourDim

variable {d : ℕ} {t : ℝ}

/-- `p(z + e_μ) - p(z) = (q(z_μ + 1) - q(z_μ)) Π_{ν ≠ μ} q(z_ν)`. -/
lemma heatKernel_shift_sub (t : ℝ) (z : Fin d → ℤ) (μ : Fin d) :
    heatKernel d t (z + Pi.single μ 1) - heatKernel d t z =
      ∏ ν, (if ν = μ then heatKernel1 t (z ν + 1) - heatKernel1 t (z ν)
        else heatKernel1 t (z ν)) := by
  rw [heatKernel_shift_pos, heatKernel_eq_mul_erase t z μ, ← sub_mul,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
  simp only [ite_true]
  congr 1
  exact Finset.prod_congr rfl fun ν hν => by rw [if_neg (Finset.ne_of_mem_erase hν)]

/-- A product kernel: `Σ_z Π_ν f_ν(z_ν) = Π_ν Σ_n f_ν(n)` for nonnegative summable `f_ν`. -/
lemma hasSum_prod_kernel (f : Fin d → ℤ → ℝ) (hf0 : ∀ ν n, 0 ≤ f ν n)
    {S : Fin d → ℝ} (hS : ∀ ν, HasSum (f ν) (S ν)) :
    HasSum (fun z : Fin d → ℤ => ∏ ν, f ν (z ν)) (∏ ν, S ν) := by
  have h := (Balaban.Green.pi_prod_summable_hasSum (𝕜 := ℝ) (κ := ℤ) (Fin d)) f fun ν =>
    (hS ν).summable.congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ν n)]
  have : ∏ ν, ∑' n, f ν n = ∏ ν, S ν := Finset.prod_congr rfl fun ν _ => (hS ν).tsum_eq
  rw [← this]; exact h.2

/-- `Σ_z |p(z + e_μ) - p(z)| = 2 q(0)`. -/
theorem hasSum_abs_shift_sub (ht : 0 ≤ t) (μ : Fin d) :
    HasSum (fun z : Fin d → ℤ => |heatKernel d t (z + Pi.single μ 1) - heatKernel d t z|)
      (2 * heatKernel1 t 0) := by
  have h := hasSum_prod_kernel
    (fun ν n => if ν = μ then |heatKernel1 t (n + 1) - heatKernel1 t n| else heatKernel1 t n)
    (fun ν n => by split_ifs <;> first | exact abs_nonneg _ | exact heatKernel1_nonneg ht n)
    (S := fun ν => if ν = μ then 2 * heatKernel1 t 0 else 1)
    (fun ν => by split_ifs <;> first | exact hasSum_abs_diff ht | exact hasSum_heatKernel1 ht)
  rw [Finset.prod_ite_eq' Finset.univ μ] at h
  · simp only [Finset.mem_univ, ite_true] at h
    refine h.congr_fun fun z => ?_
    rw [heatKernel_shift_sub, Finset.abs_prod]
    exact Finset.prod_congr rfl fun ν _ => by
      split_ifs
      · rfl
      · exact abs_of_nonneg (heatKernel1_nonneg ht _)

/-- `|p(z + e_μ) - p(z)|` as a product of one-dimensional factors. -/
lemma abs_shift_sub_eq_prod (ht : 0 ≤ t) (z : Fin d → ℤ) (μ : Fin d) :
    |heatKernel d t (z + Pi.single μ 1) - heatKernel d t z| =
      ∏ ρ, (if ρ = μ then |heatKernel1 t (z ρ + 1) - heatKernel1 t (z ρ)|
        else heatKernel1 t (z ρ)) := by
  rw [heatKernel_shift_sub, Finset.abs_prod]
  exact Finset.prod_congr rfl fun ρ _ => by
    split_ifs
    · rfl
    · exact abs_of_nonneg (heatKernel1_nonneg ht _)

/-- Multiplying a product by a function of one coordinate. -/
lemma prod_mul_coord (g : Fin d → ℝ) (ν : Fin d) (c : ℝ) :
    (∏ ρ, g ρ) * c = ∏ ρ, (if ρ = ν then c * g ρ else g ρ) := by
  have : ∏ ρ, (if ρ = ν then c * g ρ else g ρ) = ∏ ρ, (g ρ * (if ρ = ν then c else 1)) :=
    Finset.prod_congr rfl fun ρ _ => by split_ifs <;> ring
  rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ν]
  simp

/-- `Σ_z |p(z + e_μ) - p(z)| |z_μ| = 1`. -/
theorem hasSum_abs_shift_sub_mul_self (ht : 0 ≤ t) (μ : Fin d) :
    HasSum (fun z : Fin d → ℤ => |heatKernel d t (z + Pi.single μ 1) - heatKernel d t z| *
      |((z μ : ℤ) : ℝ)|) 1 := by
  have h := hasSum_prod_kernel
    (fun ρ n => if ρ = μ then |((n : ℤ) : ℝ)| * |heatKernel1 t (n + 1) - heatKernel1 t n|
      else heatKernel1 t n)
    (fun ρ n => by
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      · exact heatKernel1_nonneg ht n)
    (S := fun ρ => if ρ = μ then 1 else 1)
    (fun ρ => by
      split_ifs
      · exact hasSum_abs_mul_abs_diff ht
      · exact hasSum_heatKernel1 ht)
  simp only [ite_self, Finset.prod_const_one] at h
  refine h.congr_fun fun z => ?_
  rw [abs_shift_sub_eq_prod ht, prod_mul_coord _ μ]
  exact Finset.prod_congr rfl fun ρ _ => by split_ifs with h1 <;> simp [h1]

/-- `Σ_z |p(z + e_μ) - p(z)| |z_ν| = 2 q(0) Σ_n |n| q(n)` for `ν ≠ μ`. -/
theorem hasSum_abs_shift_sub_mul_other (ht : 0 ≤ t) {μ ν : Fin d} (hμν : ν ≠ μ) :
    HasSum (fun z : Fin d → ℤ => |heatKernel d t (z + Pi.single μ 1) - heatKernel d t z| *
      |((z ν : ℤ) : ℝ)|) (2 * heatKernel1 t 0 * ∑' n : ℤ, |(n : ℝ)| * heatKernel1 t n) := by
  set M1 := ∑' n : ℤ, |(n : ℝ)| * heatKernel1 t n
  have h := hasSum_prod_kernel
    (fun ρ n => if ρ = μ then |heatKernel1 t (n + 1) - heatKernel1 t n|
      else if ρ = ν then |((n : ℤ) : ℝ)| * heatKernel1 t n else heatKernel1 t n)
    (fun ρ n => by
      split_ifs
      · exact abs_nonneg _
      · exact mul_nonneg (abs_nonneg _) (heatKernel1_nonneg ht n)
      · exact heatKernel1_nonneg ht n)
    (S := fun ρ => if ρ = μ then 2 * heatKernel1 t 0 else if ρ = ν then M1 else 1)
    (fun ρ => by
      split_ifs
      · exact hasSum_abs_diff ht
      · exact (summable_abs_mul ht).hasSum
      · exact hasSum_heatKernel1 ht)
  have hS : ∏ ρ, (if ρ = μ then 2 * heatKernel1 t 0 else if ρ = ν then M1 else 1) =
      2 * heatKernel1 t 0 * M1 := by
    have : ∏ ρ, (if ρ = μ then 2 * heatKernel1 t 0 else if ρ = ν then M1 else 1) =
        ∏ ρ, ((if ρ = μ then 2 * heatKernel1 t 0 else 1) * (if ρ = ν then M1 else 1)) :=
      Finset.prod_congr rfl fun ρ _ => by
        by_cases h1 : ρ = μ
        · subst h1; simp [hμν.symm]
        · simp [h1]
    rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ μ,
      Finset.prod_ite_eq' Finset.univ ν]
    simp
  rw [hS] at h
  refine h.congr_fun fun z => ?_
  rw [abs_shift_sub_eq_prod ht, prod_mul_coord _ ν]
  exact Finset.prod_congr rfl fun ρ _ => by
    by_cases h1 : ρ = μ
    · subst h1; simp [hμν.symm]
    · by_cases h2 : ρ = ν
      · subst h2; simp [h1]
      · simp [h1, h2]

end FourDim

end CoreLean
