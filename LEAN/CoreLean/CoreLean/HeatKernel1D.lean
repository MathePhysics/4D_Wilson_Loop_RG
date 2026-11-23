/-
The one-dimensional lattice heat kernel `q_t` (unit spacing) and the four properties of it which
the proof of `lem:heat-kernel` of BALABAN_CORE.tex uses: it is even, its second moment is `2t`
(`eq:heat-variance`), `q_t(0) ≤ √π / (4√t)` (`eq:heat-origin`), and it does not increase with `|n|`.

The kernel, its positivity, its total mass, and the Gaussian bound of its symbol are those of
`Balaban.LatticeGreen` (`CoreLean.Vendor.HeatKernel`, `CoreLean.Vendor.HeatKernelBounds`, copied from
`balaban-lean`). The second moment and the monotonicity are proved here from the expansion of
`q_t` in the powers of the lazy walk `L = ½ + ¼(τ₊ + τ₋)`: since `2 - τ₊ - τ₋ = 4(1 - L)`,
`q_t = e^{-4t} Σ_k (4t)^k/k! L^k δ₀`, and `L^k δ₀` is even and does not increase with `|n|`, by
induction on `k`. The core proves the monotonicity by a differential equation for the differences
`q_t(n) - q_t(n+1)` instead.
-/
import CoreLean.Vendor.HeatKernelBounds

open MeasureTheory Real Balaban.LatticeGreen

namespace CoreLean

/-- `∫_{-π}^{π} cos(nθ) ((1 + cos θ)/2)^k dθ = 2π (L^k δ₀)(n)`. -/
noncomputable def lazyInt (k : ℕ) (n : ℤ) : ℝ :=
  ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ k

theorem lazyInt_zero (n : ℤ) : lazyInt 0 n = if n = 0 then 2 * π else 0 := by
  have := cosPowInt_zero n
  simpa [lazyInt, cosPowInt] using this

theorem lazyInt_succ (k : ℕ) (n : ℤ) :
    lazyInt (k + 1) n = (lazyInt k (n - 1) + 2 * lazyInt k n + lazyInt k (n + 1)) / 4 := by
  unfold lazyInt
  have hc : ∀ m : ℤ, Continuous fun θ : ℝ =>
      Real.cos ((m : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ k := by
    intro m; fun_prop
  have e : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ (k + 1) =
      (Real.cos (((n - 1 : ℤ) : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ k +
        2 * (Real.cos ((n : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ k) +
        Real.cos (((n + 1 : ℤ) : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ k) / 4 := by
    intro θ
    have h := cos_mul_cos_int n θ
    calc Real.cos ((n : ℝ) * θ) * ((1 + Real.cos θ) / 2) ^ (k + 1)
        = (Real.cos ((n : ℝ) * θ) + Real.cos ((n : ℝ) * θ) * Real.cos θ) / 2 *
            ((1 + Real.cos θ) / 2) ^ k := by ring
      _ = _ := by rw [h]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (((hc _).intervalIntegrable _ _).add (((hc _).intervalIntegrable _ _).const_mul _))
    ((hc _).intervalIntegrable _ _), intervalIntegral.integral_add
    ((hc _).intervalIntegrable _ _) (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul]

theorem lazyInt_symm (k : ℕ) (n : ℤ) : lazyInt k (-n) = lazyInt k n := by
  unfold lazyInt; simp

theorem lazyInt_nonneg (k : ℕ) : ∀ n : ℤ, 0 ≤ lazyInt k n := by
  induction k with
  | zero => intro n; rw [lazyInt_zero]; split_ifs <;> positivity
  | succ k ih =>
    intro n; rw [lazyInt_succ]
    have := ih (n - 1); have := ih n; have := ih (n + 1); positivity

theorem lazyInt_eq_zero (k : ℕ) : ∀ n : ℤ, k < n.natAbs → lazyInt k n = 0 := by
  induction k with
  | zero =>
    intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    simp [lazyInt_zero, hn0]
  | succ k ih =>
    intro n hn
    rw [lazyInt_succ, ih (n - 1) (by omega), ih n (by omega), ih (n + 1) (by omega)]; simp

theorem summable_lazyInt (k : ℕ) : Summable (lazyInt k) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) k) fun n hn => ?_
  apply lazyInt_eq_zero
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  omega

/-- `L^k δ₀` does not increase with `|n|`: `lazyInt k (n+1) ≤ lazyInt k n` for `n ≥ 0`. -/
theorem lazyInt_antitone (k : ℕ) : ∀ n : ℤ, 0 ≤ n → lazyInt k (n + 1) ≤ lazyInt k n := by
  induction k with
  | zero =>
    intro n hn
    rw [lazyInt_zero, lazyInt_zero]
    split_ifs <;> first | omega | positivity | simp
  | succ k ih =>
    intro n hn
    rw [lazyInt_succ, lazyInt_succ]
    rcases eq_or_lt_of_le hn with h | h
    · subst h
      -- at `n = 0` the evenness `lazyInt k (-1) = lazyInt k 1` is used
      have h1 : lazyInt k (0 - 1) = lazyInt k (0 + 1) := by
        rw [show (0 : ℤ) - 1 = -(0 + 1) by norm_num, lazyInt_symm]
      have a0 := ih 0 le_rfl
      have a1 := ih 1 (by norm_num)
      simp only [zero_add, zero_sub] at h1 a0 a1 ⊢
      rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num]
      rw [show (1 : ℤ) + 1 = 2 by norm_num] at a1
      linarith
    · have a0 := ih (n - 1) (by omega)
      have a1 := ih n hn
      have a2 := ih (n + 1) (by omega)
      rw [show n - 1 + 1 = n by ring] at a0
      rw [show n + 1 - 1 = n by ring]
      linarith

theorem tsum_lazyInt (k : ℕ) : ∑' n, lazyInt k n = 2 * π := by
  induction k with
  | zero =>
    rw [tsum_eq_single 0]
    · simp [lazyInt_zero]
    · intro n hn; simp [lazyInt_zero, hn]
  | succ k ih =>
    have e1 : ∑' n : ℤ, lazyInt k (n + 1) = ∑' n, lazyInt k n :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (lazyInt k)
    have e2 : ∑' n : ℤ, lazyInt k (n - 1) = ∑' n, lazyInt k n :=
      (Equiv.subRight (1 : ℤ)).tsum_eq (lazyInt k)
    have s1 : Summable fun n : ℤ => lazyInt k (n + 1) :=
      (summable_lazyInt k).comp_injective (add_left_injective (1 : ℤ))
    have s2 : Summable fun n : ℤ => lazyInt k (n - 1) :=
      (summable_lazyInt k).comp_injective (sub_left_injective (b := (1 : ℤ)))
    simp_rw [lazyInt_succ]
    rw [tsum_div_const, (s2.add ((summable_lazyInt k).mul_left 2)).tsum_add s1,
      s2.tsum_add ((summable_lazyInt k).mul_left 2), tsum_mul_left, e1, e2, ih]
    ring

/-- The second moment of `L^k δ₀` is `k/2`: `Σ_n n² lazyInt k n = π k`. -/
theorem tsum_sq_lazyInt (k : ℕ) : ∑' n : ℤ, (n : ℝ) ^ 2 * lazyInt k n = π * k := by
  have hfin : ∀ (k : ℕ) (f : ℤ → ℝ), Summable fun n : ℤ => f n * lazyInt k n := fun k f =>
    summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) k) fun n hn => by
      rw [lazyInt_eq_zero k n (by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega),
        mul_zero]
  induction k with
  | zero =>
    rw [tsum_eq_single 0]
    · simp [lazyInt_zero]
    · intro n hn; simp [lazyInt_zero, hn]
  | succ k ih =>
    -- `Σ n² (a(n-1) + 2a(n) + a(n+1))/4 = Σ a(m) ((m+1)² + 2m² + (m-1)²)/4 = Σ a(m)(m² + ½)`
    have e1 : ∑' n : ℤ, (n : ℝ) ^ 2 * lazyInt k (n - 1) =
        ∑' m : ℤ, ((m : ℝ) + 1) ^ 2 * lazyInt k m := by
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
      simp
    have e2 : ∑' n : ℤ, (n : ℝ) ^ 2 * lazyInt k (n + 1) =
        ∑' m : ℤ, ((m : ℝ) - 1) ^ 2 * lazyInt k m := by
      rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
      simp
    have s1 : Summable fun n : ℤ => (n : ℝ) ^ 2 * lazyInt k (n - 1) := by
      have := (hfin k fun m => ((m : ℝ) + 1) ^ 2).comp_injective
        (sub_left_injective (b := (1 : ℤ)))
      exact this.congr fun n => by simp
    have s2 : Summable fun n : ℤ => (n : ℝ) ^ 2 * lazyInt k (n + 1) := by
      have := (hfin k fun m => ((m : ℝ) - 1) ^ 2).comp_injective (add_left_injective (1 : ℤ))
      exact this.congr fun n => by simp
    have s0 := hfin k fun m => (m : ℝ) ^ 2
    have hsplit : (fun n : ℤ => (n : ℝ) ^ 2 * lazyInt (k + 1) n) = fun n : ℤ =>
        ((n : ℝ) ^ 2 * lazyInt k (n - 1) + 2 * ((n : ℝ) ^ 2 * lazyInt k n) +
          (n : ℝ) ^ 2 * lazyInt k (n + 1)) / 4 := by
      funext n; rw [lazyInt_succ]; ring
    rw [hsplit, tsum_div_const, (s1.add (s0.mul_left 2)).tsum_add s2, s1.tsum_add (s0.mul_left 2),
      tsum_mul_left, e1, e2, ih]
    have hp : ∑' m : ℤ, ((m : ℝ) + 1) ^ 2 * lazyInt k m + ∑' m : ℤ, ((m : ℝ) - 1) ^ 2 * lazyInt k m
        = 2 * ∑' m : ℤ, (m : ℝ) ^ 2 * lazyInt k m + 2 * ∑' m : ℤ, lazyInt k m := by
      rw [← (hfin k _).tsum_add (hfin k _), ← tsum_mul_left, ← tsum_mul_left,
        ← s0.mul_left 2 |>.tsum_add ((summable_lazyInt k).mul_left 2)]
      congr 1; funext m; ring
    have : ∑' m : ℤ, ((m : ℝ) + 1) ^ 2 * lazyInt k m + 2 * (π * k) +
        ∑' m : ℤ, ((m : ℝ) - 1) ^ 2 * lazyInt k m =
        2 * ∑' m : ℤ, (m : ℝ) ^ 2 * lazyInt k m + 2 * ∑' m : ℤ, lazyInt k m + 2 * (π * k) := by
      rw [← hp]; ring
    rw [this, ih, tsum_lazyInt]
    push_cast
    ring

/-- The symbol in the lazy form: `e^{-2t(1 - cos θ)} = e^{-4t} e^{4t (1 + cos θ)/2}`. -/
theorem heatSymbol_eq_lazy (t θ : ℝ) :
    heatSymbol t θ = Real.exp (-(4 * t)) * Real.exp (4 * t * ((1 + Real.cos θ) / 2)) := by
  unfold heatSymbol; rw [← Real.exp_add]; congr 1; ring

/-- The lazy series: `q_t(n) = Σ_k (2π)⁻¹ e^{-4t} (4t)^k/k! lazyInt k n`. -/
theorem hasSum_heatKernel1_lazy (t : ℝ) (n : ℤ) :
    HasSum (fun k : ℕ => (2 * π)⁻¹ * Real.exp (-(4 * t)) * ((4 * t) ^ k / (k.factorial : ℝ)) *
      lazyInt k n) (heatKernel1 t n) := by
  have hsum : Summable fun k : ℕ => |4 * t| ^ k / (k.factorial : ℝ) :=
    Real.summable_pow_div_factorial |4 * t|
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π)
    (F := fun (k : ℕ) (θ : ℝ) =>
      Real.cos ((n : ℝ) * θ) * ((4 * t * ((1 + Real.cos θ) / 2)) ^ k / (k.factorial : ℝ)))
    (f := fun θ => Real.cos ((n : ℝ) * θ) * Real.exp (4 * t * ((1 + Real.cos θ) / 2)))
    (fun k θ => |4 * t| ^ k / (k.factorial : ℝ))
    (fun k => by fun_prop)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      have hc : |(1 + Real.cos θ) / 2| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
      rw [norm_mul, norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, mul_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ))]
      have h1 := Real.abs_cos_le_one ((n : ℝ) * θ)
      have h2 : |(1 + Real.cos θ) / 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have h3 : (0 : ℝ) ≤ |4 * t| ^ k / (k.factorial : ℝ) := by positivity
      calc |Real.cos ((n : ℝ) * θ)| * (|4 * t| ^ k * |(1 + Real.cos θ) / 2| ^ k /
              (k.factorial : ℝ))
          = |Real.cos ((n : ℝ) * θ)| * (|4 * t| ^ k / (k.factorial : ℝ) *
              |(1 + Real.cos θ) / 2| ^ k) := by ring
        _ ≤ 1 * (|4 * t| ^ k / (k.factorial : ℝ) * 1) := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun θ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => by
      have := NormedSpace.expSeries_div_hasSum_exp (4 * t * ((1 + Real.cos θ) / 2))
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this.mul_left _)
  have h' := h.mul_left ((2 * π)⁻¹ * Real.exp (-(4 * t)))
  have e : heatKernel1 t n = (2 * π)⁻¹ * Real.exp (-(4 * t)) *
      ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * Real.exp (4 * t * ((1 + Real.cos θ) / 2)) := by
    unfold heatKernel1
    have : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * heatSymbol t θ = Real.exp (-(4 * t)) *
        (Real.cos ((n : ℝ) * θ) * Real.exp (4 * t * ((1 + Real.cos θ) / 2))) :=
      fun θ => by rw [heatSymbol_eq_lazy]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]; ring
  rw [e]
  convert h' using 1
  funext k
  have hk : ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) *
      ((4 * t * ((1 + Real.cos θ) / 2)) ^ k / (k.factorial : ℝ)) =
      (4 * t) ^ k / (k.factorial : ℝ) * lazyInt k n := by
    rw [lazyInt, ← intervalIntegral.integral_const_mul]
    congr 1; funext θ; rw [mul_pow]; ring
  rw [hk]; ring

/-- `q_t` is even. -/
theorem heatKernel1_neg (t : ℝ) (n : ℤ) : heatKernel1 t (-n) = heatKernel1 t n := by
  unfold heatKernel1; simp

/-- `q_t` does not increase with `|n|`: `q_t(n+1) ≤ q_t(n)` for `n ≥ 0` and `t ≥ 0`. -/
theorem heatKernel1_antitone {t : ℝ} (ht : 0 ≤ t) {n : ℤ} (hn : 0 ≤ n) :
    heatKernel1 t (n + 1) ≤ heatKernel1 t n :=
  hasSum_le (fun k => mul_le_mul_of_nonneg_left (lazyInt_antitone k n hn) (by positivity))
    (hasSum_heatKernel1_lazy t (n + 1)) (hasSum_heatKernel1_lazy t n)

/-- `eq:heat-variance` (unit spacing): `Σ_n n² q_t(n) = 2t` for `t ≥ 0`. -/
theorem hasSum_sq_heatKernel1 {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n : ℤ => (n : ℝ) ^ 2 * heatKernel1 t n) (2 * t) := by
  set w : ℕ → ℝ := fun k => (2 * π)⁻¹ * Real.exp (-(4 * t)) * ((4 * t) ^ k / (k.factorial : ℝ))
    with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by simp only [hw]; positivity
  have hf0 : ∀ p : ℕ × ℤ, 0 ≤ w p.1 * ((p.2 : ℝ) ^ 2 * lazyInt p.1 p.2) := fun p =>
    mul_nonneg (hw0 _) (mul_nonneg (sq_nonneg _) (lazyInt_nonneg _ _))
  have hinner : ∀ k, ∑' n : ℤ, w k * ((n : ℝ) ^ 2 * lazyInt k n) = w k * (π * k) := fun k => by
    rw [tsum_mul_left, tsum_sq_lazyInt]
  have hfinsq : ∀ k, Summable fun n : ℤ => (n : ℝ) ^ 2 * lazyInt k n := fun k =>
    summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) k) fun n hn => by
      rw [lazyInt_eq_zero k n (by simp only [Finset.mem_Icc, not_and_or, not_le] at hn; omega),
        mul_zero]
  have hex : HasSum (fun k : ℕ => (4 * t) ^ k / (k.factorial : ℝ)) (Real.exp (4 * t)) := by
    have := NormedSpace.expSeries_div_hasSum_exp (4 * t)
    rwa [← Real.exp_eq_exp_ℝ] at this
  -- `Σ_k w_k π k = (2π)⁻¹ e^{-4t} π (4t) e^{4t} = 2t`
  have hk : HasSum (fun k : ℕ => w k * (π * k)) (2 * t) := by
    have hshift : HasSum (fun k : ℕ => (4 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * (k + 1))
        (4 * t * Real.exp (4 * t)) := by
      have := hex.mul_left (4 * t)
      convert this using 1
      funext k
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    have h1 : HasSum (fun k : ℕ => (4 * t) ^ k / (k.factorial : ℝ) * k)
        (4 * t * Real.exp (4 * t)) := by
      rw [← hasSum_nat_add_iff' 1]
      simpa [Finset.sum_range_one] using hshift
    have := h1.mul_left ((2 * π)⁻¹ * Real.exp (-(4 * t)) * π)
    convert this using 1
    · funext k; simp only [hw]; ring
    · have he : Real.exp (-(4 * t)) * Real.exp (4 * t) = 1 := by rw [← Real.exp_add]; simp
      rw [show (2 * π)⁻¹ * Real.exp (-(4 * t)) * π * (4 * t * Real.exp (4 * t)) =
        (2 * π)⁻¹ * π * (4 * t) * (Real.exp (-(4 * t)) * Real.exp (4 * t)) by ring, he]
      field_simp
      ring
  have hfs : Summable fun p : ℕ × ℤ => w p.1 * ((p.2 : ℝ) ^ 2 * lazyInt p.1 p.2) := by
    rw [summable_prod_of_nonneg hf0]
    refine ⟨fun k => (hfinsq k).mul_left (w k), ?_⟩
    have : (fun k : ℕ => ∑' n : ℤ, w k * ((n : ℝ) ^ 2 * lazyInt k n)) = fun k => w k * (π * k) :=
      funext hinner
    rw [this]; exact hk.summable
  have hq : ∀ n : ℤ, (n : ℝ) ^ 2 * heatKernel1 t n = ∑' k, w k * ((n : ℝ) ^ 2 * lazyInt k n) :=
    fun n => by
      rw [← ((hasSum_heatKernel1_lazy t n).mul_left ((n : ℝ) ^ 2)).tsum_eq]
      congr 1; funext k; simp only [hw]; ring
  have hfs' : Summable (Function.uncurry fun (n : ℤ) (k : ℕ) =>
      w k * ((n : ℝ) ^ 2 * lazyInt k n)) := hfs.prod_symm
  have htot : ∑' n : ℤ, ∑' k, w k * ((n : ℝ) ^ 2 * lazyInt k n) = 2 * t := by
    rw [← hfs'.tsum_comm]
    simp_rw [hinner]
    exact hk.tsum_eq
  rw [show (fun n : ℤ => (n : ℝ) ^ 2 * heatKernel1 t n) =
    fun n : ℤ => ∑' k, w k * ((n : ℝ) ^ 2 * lazyInt k n) from funext hq, ← htot]
  exact hfs'.prod.hasSum

/-- `eq:heat-origin` (unit spacing): `q_t(0) ≤ √π / (4√t)` for `t > 0`. -/
theorem heatKernel1_zero_le {t : ℝ} (ht : 0 < t) :
    heatKernel1 t 0 ≤ Real.sqrt π / (4 * Real.sqrt t) := by
  set b := 4 * t / π ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hle : ∫ θ in (-π)..π, heatSymbol t θ ≤ ∫ θ, Real.exp (-b * θ ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    calc ∫ θ in Set.Ioc (-π) π, heatSymbol t θ
        ≤ ∫ θ in Set.Ioc (-π) π, Real.exp (-b * θ ^ 2) := by
          refine setIntegral_mono_on ((continuous_heatSymbol_right t).integrableOn_Ioc)
            ((integrable_exp_neg_mul_sq hb0).integrableOn) measurableSet_Ioc fun θ hθ => ?_
          have h := heatSymbol_le_gaussian ht.le (θ := θ) (abs_le.mpr ⟨hθ.1.le, hθ.2⟩)
          convert h using 2; ring
      _ ≤ ∫ θ, Real.exp (-b * θ ^ 2) :=
          setIntegral_le_integral (integrable_exp_neg_mul_sq hb0)
            (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have h0 : heatKernel1 t 0 = (2 * π)⁻¹ * ∫ θ in (-π)..π, heatSymbol t θ := by
    simp [heatKernel1]
  have hg : ∫ θ, Real.exp (-b * θ ^ 2) = Real.sqrt (π / b) := integral_gaussian b
  rw [h0]
  calc (2 * π)⁻¹ * ∫ θ in (-π)..π, heatSymbol t θ ≤ (2 * π)⁻¹ * Real.sqrt (π / b) :=
        mul_le_mul_of_nonneg_left (hle.trans hg.le) (by positivity)
    _ = Real.sqrt π / (4 * Real.sqrt t) := by
        rw [hb, show π / (4 * t / π ^ 2) = π ^ 3 / (4 * t) by field_simp]
        rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 4 * t),
          show (π : ℝ) ^ 3 = π ^ 2 * π by ring, Real.sqrt_mul' _ Real.pi_pos.le,
          Real.sqrt_sq Real.pi_pos.le, Real.sqrt_mul' _ ht.le,
          show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
        field_simp
        ring

end CoreLean
