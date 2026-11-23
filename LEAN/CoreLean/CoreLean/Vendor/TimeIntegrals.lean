module

public import CoreLean.Vendor.Green

/-!
# Elementary time integrals for the lattice Green's function bounds

The power `((√t)⁻¹)^N = t^{-N/2}`, its integrals over `(c, ∞)` and the Gaussian-in-`n/√t`
estimate used to integrate the one-dimensional heat-kernel bounds in `t`.

Provenance: copied from `Balaban/Green/Lattice/TimeIntegrals.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit `493e9eb`, Apache License 2.0
(`LICENSE-balaban-lean`); the only change is the import path.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Set Filter Topology

/-- `t^{-N/2}` written as an inverse square root to a natural power. -/
def invSqrtPow (N : ℕ) (t : ℝ) : ℝ := ((Real.sqrt t)⁻¹) ^ N

theorem invSqrtPow_eq_rpow (N : ℕ) {t : ℝ} (ht : 0 < t) :
    invSqrtPow N t = t ^ (-((N : ℝ) / 2)) := by
  unfold invSqrtPow
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1; ring

theorem invSqrtPow_nonneg (N : ℕ) (t : ℝ) : 0 ≤ invSqrtPow N t := by
  unfold invSqrtPow; positivity

theorem continuousOn_invSqrtPow (N : ℕ) : ContinuousOn (invSqrtPow N) (Ioi 0) := by
  intro t ht
  have : (Real.sqrt t) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  unfold invSqrtPow
  exact ((Real.continuous_sqrt.continuousAt.inv₀ this).pow N).continuousWithinAt

theorem integrableOn_invSqrtPow {N : ℕ} (hN : 3 ≤ N) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (invSqrtPow N) (Ioi c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -((N : ℝ) / 2)) (c := c)
    (by have : (3 : ℝ) ≤ N := by exact_mod_cast hN
        linarith) hc
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (invSqrtPow_eq_rpow N (lt_trans hc ht)).symm

theorem integral_invSqrtPow {N : ℕ} (hN : 3 ≤ N) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (r ^ 2), invSqrtPow N t = 2 / ((N : ℝ) - 2) * (r ^ (N - 2))⁻¹ := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hr2 : 0 < r ^ 2 := by positivity
  have h := integral_Ioi_rpow_of_lt (a := -((N : ℝ) / 2)) (c := r ^ 2)
    (by linarith) hr2
  have e : ∫ t in Ioi (r ^ 2), invSqrtPow N t = ∫ t in Ioi (r ^ 2), t ^ (-((N : ℝ) / 2)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      invSqrtPow_eq_rpow N (lt_trans hr2 ht)
  rw [e, h]
  have e2 : (r ^ 2) ^ (-((N : ℝ) / 2) + 1) = (r ^ (N - 2))⁻¹ := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    have : ((2 : ℕ) : ℝ) * (-((N : ℝ) / 2) + 1) = -((N - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [e2]
  have h2 : (N : ℝ) - 2 ≠ 0 := by linarith
  rw [show -((N : ℝ) / 2) + 1 = -(((N : ℝ) - 2) / 2) by ring]
  field_simp

theorem pow_mul_exp_neg_sq_le (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    w ^ N * Real.exp (-(w ^ 2)) ≤ 1 + (N.factorial : ℝ) := by
  have h1 : w ^ N ≤ 1 + (w ^ 2) ^ N := by
    rcases le_total w 1 with h | h
    · have := pow_le_one₀ hw h (n := N)
      have : 0 ≤ (w ^ 2) ^ N := by positivity
      linarith
    · have : w ^ N ≤ (w ^ 2) ^ N := by
        rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
      linarith
  have h2 := Real.pow_div_factorial_le_exp (w ^ 2) (by positivity) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h3 : (w ^ 2) ^ N ≤ N.factorial * Real.exp (w ^ 2) := by
    rw [div_le_iff₀ hf] at h2; linarith
  have h4 : Real.exp (-(w ^ 2)) * Real.exp (w ^ 2) = 1 := by rw [← Real.exp_add]; simp
  have h5 : Real.exp (-(w ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w])
  have hp := Real.exp_pos (-(w ^ 2))
  calc w ^ N * Real.exp (-(w ^ 2)) ≤ (1 + (w ^ 2) ^ N) * Real.exp (-(w ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = Real.exp (-(w ^ 2)) + (w ^ 2) ^ N * Real.exp (-(w ^ 2)) := by ring
    _ ≤ 1 + N.factorial := by
        have : (w ^ 2) ^ N * Real.exp (-(w ^ 2)) ≤ N.factorial := by
          calc (w ^ 2) ^ N * Real.exp (-(w ^ 2)) ≤ N.factorial * Real.exp (w ^ 2) * Real.exp (-(w ^ 2)) :=
                mul_le_mul_of_nonneg_right h3 hp.le
            _ = N.factorial := by rw [mul_assoc, mul_comm (Real.exp (w ^ 2)), h4, mul_one]
        linarith

/-- For `n ≠ 0` and `t > 0`: `t^{-N/2} e^{-n²/(16t)} ≤ (1 + N!) 4^N / |n|^N`. -/
theorem invSqrtPow_mul_exp_le (N : ℕ) {t : ℝ} (ht : 0 < t) {n : ℤ} (hn : n ≠ 0) :
    invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤
      (1 + (N.factorial : ℝ)) * 4 ^ N / |(n : ℝ)| ^ N := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  set w := |(n : ℝ)| / (4 * Real.sqrt t) with hw
  have hw0 : 0 < w := by positivity
  have hw2 : w ^ 2 = (n : ℝ) ^ 2 / (16 * t) := by
    rw [hw, div_pow, mul_pow, Real.sq_sqrt ht.le, sq_abs]; norm_num
  have h := pow_mul_exp_neg_sq_le N hw0.le
  rw [hw2] at h
  unfold invSqrtPow
  have hw' : w ^ N = |(n : ℝ)| ^ N / (4 * Real.sqrt t) ^ N := by rw [hw, div_pow]
  rw [hw'] at h
  have h4s : 0 < (4 * Real.sqrt t) ^ N := by positivity
  have hn' : 0 < |(n : ℝ)| ^ N := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h4s] at h
  rw [le_div_iff₀ hn']
  have e : ((Real.sqrt t)⁻¹) ^ N * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) * |(n : ℝ)| ^ N =
      ((Real.sqrt t)⁻¹) ^ N * ((|(n : ℝ)| ^ N * Real.exp (-((n : ℝ) ^ 2 / (16 * t))))) := by ring
  rw [e]
  have : ((Real.sqrt t)⁻¹) ^ N * (4 * Real.sqrt t) ^ N = 4 ^ N := by
    rw [← mul_pow, ← mul_assoc, mul_comm _ (4 : ℝ), mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
  calc ((Real.sqrt t)⁻¹) ^ N * (|(n : ℝ)| ^ N * Real.exp (-((n : ℝ) ^ 2 / (16 * t))))
      ≤ ((Real.sqrt t)⁻¹) ^ N * ((1 + (N.factorial : ℝ)) * (4 * Real.sqrt t) ^ N) := by
        gcongr
    _ = (1 + (N.factorial : ℝ)) * 4 ^ N := by rw [← this]; ring

/-- The exponential factor of the large-time bounds. -/
def Elarge (t : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-((n : ℝ) ^ 2 / (16 * t))) + Real.exp (-(|(n : ℝ)| / 4))

theorem Elarge_nonneg (t : ℝ) (n : ℤ) : 0 ≤ Elarge t n := by
  unfold Elarge; positivity

theorem Elarge_le_two {t : ℝ} (ht : 0 < t) (n : ℤ) : Elarge t n ≤ 2 := by
  unfold Elarge
  have h1 : Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ (n : ℝ) ^ 2 / (16 * t) := by positivity
                                linarith)
  have h2 : Real.exp (-(|(n : ℝ)| / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ |(n : ℝ)| / 4 := by positivity
                                linarith)
  linarith

theorem continuousOn_Elarge (n : ℤ) : ContinuousOn (fun t => Elarge t n) (Ioi 0) := by
  intro t ht
  have h : ContinuousAt (fun t : ℝ => Real.exp (-((n : ℝ) ^ 2 / (16 * t)))) t := by
    have : (16 * t) ≠ 0 := by have : (0 : ℝ) < t := ht; positivity
    fun_prop (disch := exact this)
  have h2 : ContinuousAt (fun _ : ℝ => Real.exp (-(|(n : ℝ)| / 4))) t := continuousAt_const
  exact (h.add h2).continuousWithinAt

theorem exp_neg_div_four_le (K : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (-(a / 4)) ≤ Real.exp (1 / 4) * (K.factorial : ℝ) * 4 ^ K / (1 + a) ^ K := by
  have h := Real.pow_div_factorial_le_exp ((1 + a) / 4) (by positivity) K
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  have h1 : Real.exp (-(a / 4)) = Real.exp (1 / 4) * Real.exp (-((1 + a) / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-((1 + a) / 4)) * Real.exp ((1 + a) / 4) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-((1 + a) / 4))
  have h3 : ((1 + a) / 4) ^ K ≤ K.factorial * Real.exp ((1 + a) / 4) := by
    rw [div_le_iff₀ hf] at h; linarith
  have h4 : Real.exp (-((1 + a) / 4)) * ((1 + a) / 4) ^ K ≤ K.factorial := by
    calc Real.exp (-((1 + a) / 4)) * ((1 + a) / 4) ^ K
        ≤ Real.exp (-((1 + a) / 4)) * (K.factorial * Real.exp ((1 + a) / 4)) :=
          mul_le_mul_of_nonneg_left h3 hp.le
      _ = K.factorial := by rw [← mul_assoc, mul_comm _ (K.factorial : ℝ), mul_assoc, h2, mul_one]
  have hpos : 0 < (1 + a) ^ K := by positivity
  rw [le_div_iff₀ hpos, h1]
  have e : (1 + a) ^ K = 4 ^ K * ((1 + a) / 4) ^ K := by rw [← mul_pow]; congr 1; ring
  calc Real.exp (1 / 4) * Real.exp (-((1 + a) / 4)) * (1 + a) ^ K
      = Real.exp (1 / 4) * 4 ^ K * (Real.exp (-((1 + a) / 4)) * ((1 + a) / 4) ^ K) := by
        rw [e]; ring
    _ ≤ Real.exp (1 / 4) * 4 ^ K * K.factorial := by gcongr
    _ = _ := by ring

theorem continuousOn_invSqrtPow_mul_exp (N : ℕ) (n : ℤ) :
    ContinuousOn (fun t => invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t)))) (Ioi 0) := by
  intro t ht
  have h0 : (16 * t) ≠ 0 := by have : (0 : ℝ) < t := ht; positivity
  have h : ContinuousAt (fun t : ℝ => Real.exp (-((n : ℝ) ^ 2 / (16 * t)))) t := by
    fun_prop (disch := exact h0)
  exact ((continuousOn_invSqrtPow N t ht).continuousAt (Ioi_mem_nhds ht) |>.mul h).continuousWithinAt

theorem integrableOn_invSqrtPow_mul_exp {N : ℕ} (hN : 3 ≤ N) (n : ℤ) :
    IntegrableOn (fun t => invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t)))) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_invSqrtPow hN one_pos)
    (((continuousOn_invSqrtPow_mul_exp N n).mono
      (fun t ht => lt_trans zero_lt_one ht)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (invSqrtPow_nonneg N t) (Real.exp_pos _).le)]
  have : Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ (n : ℝ) ^ 2 / (16 * t) := by positivity
                                linarith)
  calc invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤ invSqrtPow N t * 1 :=
        mul_le_mul_of_nonneg_left this (invSqrtPow_nonneg N t)
    _ = invSqrtPow N t := mul_one _

theorem integral_invSqrtPow_mul_exp_le {N : ℕ} (hN : 3 ≤ N) {n : ℤ} (hn : n ≠ 0) :
    ∫ t in Ioi 1, invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤
      ((1 + (N.factorial : ℝ)) * 4 ^ N + 2 / ((N : ℝ) - 2)) / |(n : ℝ)| ^ (N - 2) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set r := |(n : ℝ)| with hr
  have hr1 : 1 ≤ r := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    rw [hr]; exact_mod_cast this
  have hr0 : 0 < r := by linarith
  set f : ℝ → ℝ := fun t => invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) with hf
  have hfi : IntegrableOn f (Ioi 1) := integrableOn_invSqrtPow_mul_exp hN n
  have hR : 1 ≤ r ^ 2 := by nlinarith
  have hunion : Ioi (1 : ℝ) = Ioc 1 (r ^ 2) ∪ Ioi (r ^ 2) := (Ioc_union_Ioi_eq_Ioi hR).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) (r ^ 2)) (Ioi (r ^ 2)) := Ioc_disjoint_Ioi le_rfl
  have hf1 : IntegrableOn f (Ioc 1 (r ^ 2)) := hfi.mono_set (by rw [hunion]; exact subset_union_left)
  have hf2 : IntegrableOn f (Ioi (r ^ 2)) := hfi.mono_set (by rw [hunion]; exact subset_union_right)
  have hsplit : ∫ t in Ioi 1, f t = (∫ t in Ioc 1 (r ^ 2), f t) + ∫ t in Ioi (r ^ 2), f t := by
    conv_lhs => rw [hunion]
    exact setIntegral_union hdisj measurableSet_Ioi hf1 hf2
  have hK : 0 ≤ (1 + (N.factorial : ℝ)) * 4 ^ N := by positivity
  have hrN : 0 < r ^ N := by positivity
  -- the bounded part
  have hpart1 : ∫ t in Ioc 1 (r ^ 2), f t ≤ (1 + (N.factorial : ℝ)) * 4 ^ N / r ^ (N - 2) := by
    have h1 : ∫ t in Ioc 1 (r ^ 2), f t ≤ ∫ t in Ioc 1 (r ^ 2), (1 + (N.factorial : ℝ)) * 4 ^ N / r ^ N := by
      apply setIntegral_mono_on hf1 (integrableOn_const (by simp)) measurableSet_Ioc
      intro t ht
      exact invSqrtPow_mul_exp_le N (lt_of_lt_of_le one_pos ht.1.le) hn
    refine h1.trans ?_
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    have hN2 : r ^ N = r ^ 2 * r ^ (N - 2) := by rw [← pow_add]; congr 1; omega
    rw [hN2]
    have hp : 0 < r ^ (N - 2) := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    have : (r ^ 2 - 1) * ((1 + (N.factorial : ℝ)) * 4 ^ N * ((r ^ 2)⁻¹ * (r ^ (N - 2))⁻¹)) ≤
        1 * ((1 + (N.factorial : ℝ)) * 4 ^ N * (r ^ (N - 2))⁻¹) := by
      have hr2 : 0 < r ^ 2 := by positivity
      have e : (r ^ 2 - 1) * ((r ^ 2)⁻¹) ≤ 1 := by
        rw [sub_mul, mul_inv_cancel₀ hr2.ne']; linarith [inv_pos.mpr hr2]
      calc (r ^ 2 - 1) * ((1 + (N.factorial : ℝ)) * 4 ^ N * ((r ^ 2)⁻¹ * (r ^ (N - 2))⁻¹))
          = ((r ^ 2 - 1) * (r ^ 2)⁻¹) * ((1 + (N.factorial : ℝ)) * 4 ^ N * (r ^ (N - 2))⁻¹) := by ring
        _ ≤ 1 * ((1 + (N.factorial : ℝ)) * 4 ^ N * (r ^ (N - 2))⁻¹) :=
          mul_le_mul_of_nonneg_right e (by positivity)
    linarith
  -- the tail
  have hpart2 : ∫ t in Ioi (r ^ 2), f t ≤ 2 / ((N : ℝ) - 2) / r ^ (N - 2) := by
    have h1 : ∫ t in Ioi (r ^ 2), f t ≤ ∫ t in Ioi (r ^ 2), invSqrtPow N t := by
      apply setIntegral_mono_on hf2 (integrableOn_invSqrtPow hN (by positivity)) measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans (by positivity) ht
      have : Real.exp (-((n : ℝ) ^ 2 / (16 * t))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have : 0 ≤ (n : ℝ) ^ 2 / (16 * t) := by positivity
                                    linarith)
      calc f t = invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t))) := rfl
        _ ≤ invSqrtPow N t * 1 := mul_le_mul_of_nonneg_left this (invSqrtPow_nonneg N t)
        _ = invSqrtPow N t := mul_one _
    refine h1.trans_eq ?_
    rw [integral_invSqrtPow hN hr0]; ring
  rw [hsplit]
  calc _ ≤ (1 + (N.factorial : ℝ)) * 4 ^ N / r ^ (N - 2) + 2 / ((N : ℝ) - 2) / r ^ (N - 2) :=
        add_le_add hpart1 hpart2
    _ = _ := by ring

theorem integrableOn_invSqrtPow_mul_Elarge {N : ℕ} (hN : 3 ≤ N) (n : ℤ) :
    IntegrableOn (fun t => invSqrtPow N t * Elarge t n) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_invSqrtPow hN one_pos).const_mul 2)
    ((((continuousOn_invSqrtPow N).mono (fun t ht => lt_trans zero_lt_one ht)).mul
      ((continuousOn_Elarge n).mono (fun t ht => lt_trans zero_lt_one ht))).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (invSqrtPow_nonneg N t) (Elarge_nonneg t n))]
  calc invSqrtPow N t * Elarge t n ≤ invSqrtPow N t * 2 :=
        mul_le_mul_of_nonneg_left (Elarge_le_two ht0 n) (invSqrtPow_nonneg N t)
    _ = 2 * invSqrtPow N t := mul_comm _ _

theorem integral_invSqrtPow_Elarge_le {N : ℕ} (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ∫ t in Ioi 1, invSqrtPow N t * Elarge t n ≤ C / (1 + |(n : ℝ)|) ^ (N - 2) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : 0 < (N : ℝ) - 2 := by linarith
  set A : ℝ := (1 + (N.factorial : ℝ)) * 4 ^ N + 2 / ((N : ℝ) - 2) with hA
  set B : ℝ := 2 / ((N : ℝ) - 2) * (Real.exp (1 / 4) * ((N - 2).factorial : ℝ) * 4 ^ (N - 2)) with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨2 ^ (N - 2) * A + 2 / ((N : ℝ) - 2) + B, by positivity, fun n => ?_⟩
  have hg : ∫ t in Ioi 1, invSqrtPow N t = 2 / ((N : ℝ) - 2) := by
    have := integral_invSqrtPow hN (r := 1) one_pos
    simpa using this
  have hsplit : ∫ t in Ioi 1, invSqrtPow N t * Elarge t n =
      (∫ t in Ioi 1, invSqrtPow N t * Real.exp (-((n : ℝ) ^ 2 / (16 * t)))) +
        Real.exp (-(|(n : ℝ)| / 4)) * (∫ t in Ioi 1, invSqrtPow N t) := by
    have h1 := integrableOn_invSqrtPow_mul_exp hN n
    have h2 : IntegrableOn (fun t => Real.exp (-(|(n : ℝ)| / 4)) * invSqrtPow N t) (Ioi 1) :=
      (integrableOn_invSqrtPow hN one_pos).const_mul _
    rw [← integral_const_mul]
    rw [← integral_add h1 h2]
    congr 1; funext t
    unfold Elarge; ring
  rw [hsplit, hg]
  have hr0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hexp := exp_neg_div_four_le (N - 2) hr0
  have h1pos : 0 < (1 + |(n : ℝ)|) ^ (N - 2) := by positivity
  have hterm2 : Real.exp (-(|(n : ℝ)| / 4)) * (2 / ((N : ℝ) - 2)) ≤ B / (1 + |(n : ℝ)|) ^ (N - 2) := by
    calc Real.exp (-(|(n : ℝ)| / 4)) * (2 / ((N : ℝ) - 2))
        ≤ (Real.exp (1 / 4) * ((N - 2).factorial : ℝ) * 4 ^ (N - 2) / (1 + |(n : ℝ)|) ^ (N - 2)) *
          (2 / ((N : ℝ) - 2)) := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = B / (1 + |(n : ℝ)|) ^ (N - 2) := by rw [hB]; ring
  by_cases hn : n = 0
  · subst hn
    have : ∫ t in Ioi 1, invSqrtPow N t * Real.exp (-(((0 : ℤ) : ℝ) ^ 2 / (16 * t))) = 2 / ((N : ℝ) - 2) := by
      rw [← hg]; congr 1; funext t; simp
    rw [this]
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, div_one]
    have h3 : 2 ^ (N - 2) * A ≥ 0 := by positivity
    have h4 : B / (1 + |((0 : ℤ) : ℝ)|) ^ (N - 2) = B := by simp
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, div_one] at hterm2
    linarith
  · have hI := integral_invSqrtPow_mul_exp_le hN hn
    have hr1 : 1 ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hrpos : 0 < |(n : ℝ)| := by linarith
    have h2 : (1 + |(n : ℝ)|) ^ (N - 2) ≤ 2 ^ (N - 2) * |(n : ℝ)| ^ (N - 2) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h3 : A / |(n : ℝ)| ^ (N - 2) ≤ 2 ^ (N - 2) * A / (1 + |(n : ℝ)|) ^ (N - 2) := by
      rw [div_le_div_iff₀ (by positivity) h1pos]
      calc A * (1 + |(n : ℝ)|) ^ (N - 2) ≤ A * (2 ^ (N - 2) * |(n : ℝ)| ^ (N - 2)) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = 2 ^ (N - 2) * A * |(n : ℝ)| ^ (N - 2) := by ring
    have : (2 ^ (N - 2) * A + 2 / ((N : ℝ) - 2) + B) / (1 + |(n : ℝ)|) ^ (N - 2) =
        2 ^ (N - 2) * A / (1 + |(n : ℝ)|) ^ (N - 2) + 2 / ((N : ℝ) - 2) / (1 + |(n : ℝ)|) ^ (N - 2) +
          B / (1 + |(n : ℝ)|) ^ (N - 2) := by ring
    rw [this]
    have h5 : 0 ≤ 2 / ((N : ℝ) - 2) / (1 + |(n : ℝ)|) ^ (N - 2) := by positivity
    linarith

end Balaban.LatticeGreen
