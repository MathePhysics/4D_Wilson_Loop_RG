import Mathlib

/-! **Sums over ordered scale indices** (the summations over `j` of III (2.15)-(2.16)): for weights
`L^{c_i (j_i - J)}` on nondecreasing tuples `j_0 ≤ … ≤ j_{m-1} ≤ J`, the sum is at most
`∏_i (1 - L^{-P_i})⁻¹`, `P_i = c_0 + … + c_i`, provided every prefix sum is positive (monoSum_geom_le); uniform in
`J`. The proof peels the largest index: `Σ_{t ≤ J} L^{P_{m} (t - J)} ≤ (1 - L^{-P_m})⁻¹`. -/

namespace GaussianBlockSpin

open Real Finset

/-- Sums over nondecreasing tuples `j_0 ≤ … ≤ j_{m-1} ≤ J` of products `∏_i g_i(j_i)`. -/
noncomputable def monoSum : (m : ℕ) → (Fin m → ℕ → ℝ) → ℕ → ℝ
  | 0, _, _ => 1
  | m + 1, g, J => ∑ t ∈ Finset.range (J + 1), g (Fin.last m) t * monoSum m (fun i => g i.castSucc) t

/-- The prefix sums `P_i = c_0 + … + c_i`. -/
noncomputable def prefixSum {m : ℕ} (c : Fin m → ℝ) (i : Fin m) : ℝ := ∑ i' ∈ Finset.Iic i, c i'

lemma monoSum_nonneg : ∀ (m : ℕ) (g : Fin m → ℕ → ℝ), (∀ i t, 0 ≤ g i t) → ∀ J, 0 ≤ monoSum m g J
  | 0, _, _, _ => by simp [monoSum]
  | m + 1, g, hg, J => by
    unfold monoSum
    exact Finset.sum_nonneg fun t _ => mul_nonneg (hg _ _) (monoSum_nonneg m _ (fun i t => hg _ _) t)

/-- Constant factors come out of the sum. -/
lemma monoSum_mul : ∀ (m : ℕ) (a : Fin m → ℝ) (g : Fin m → ℕ → ℝ) (J : ℕ),
    monoSum m (fun i t => a i * g i t) J = (∏ i, a i) * monoSum m g J
  | 0, _, _, _ => by simp [monoSum]
  | m + 1, a, g, J => by
    unfold monoSum
    rw [Fin.prod_univ_castSucc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [monoSum_mul m (fun i => a i.castSucc) (fun i => g i.castSucc) t]
    ring

lemma monoSum_mono : ∀ (m : ℕ) (g g' : Fin m → ℕ → ℝ), (∀ i t, 0 ≤ g i t) → (∀ i t, g i t ≤ g' i t) →
    ∀ J, monoSum m g J ≤ monoSum m g' J
  | 0, _, _, _, _, _ => le_rfl
  | m + 1, g, g', hg, hgg, J => by
    unfold monoSum
    refine Finset.sum_le_sum fun t _ => mul_le_mul (hgg _ _) (monoSum_mono m _ _ (fun i t => hg _ _)
      (fun i t => hgg _ _) t) (monoSum_nonneg m _ (fun i t => hg _ _) t) ((hg _ _).trans (hgg _ _))

lemma prefixSum_castSucc {m : ℕ} (c : Fin (m + 1) → ℝ) (i : Fin m) :
    prefixSum (fun i => c i.castSucc) i = prefixSum c i.castSucc := by
  unfold prefixSum
  show ∑ i' ∈ Finset.Iic i, c (Fin.castSuccEmb i') = _
  rw [← Finset.sum_map (Finset.Iic i) Fin.castSuccEmb]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_Iic, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact Fin.castSucc_le_castSucc_iff.mpr hy
  · intro hx
    have hxl : x ≠ Fin.last m := fun h => by
      rw [h] at hx; exact absurd (Fin.castSucc_lt_last i) (not_lt.mpr hx)
    obtain ⟨y, rfl⟩ := Fin.exists_castSucc_eq.mpr hxl
    exact ⟨y, Fin.castSucc_le_castSucc_iff.mp hx, rfl⟩

lemma prefixSum_last {m : ℕ} (c : Fin (m + 1) → ℝ) : prefixSum c (Fin.last m) = ∑ i, c i := by
  unfold prefixSum
  congr 1
  ext x
  simp [Fin.le_last]

/-- A geometric sum: `Σ_{t ≤ J} L^{P (t - J)} ≤ (1 - L^{-P})⁻¹` for `L > 1`, `P > 0`. -/
lemma sum_rpow_le_inv {L P : ℝ} (hL : 1 < L) (hP : 0 < P) (J : ℕ) :
    ∑ t ∈ Finset.range (J + 1), L ^ (P * ((t : ℝ) - J)) ≤ (1 - L ^ (-P))⁻¹ := by
  have hL0 : 0 < L := by linarith
  set r := L ^ (-P) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hL0 _).le
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
  have hterm : ∀ t ∈ Finset.range (J + 1), L ^ (P * ((t : ℝ) - J)) = r ^ (J - t) := by
    intro t ht
    have htJ : t ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Nat.cast_sub htJ]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm]
  calc ∑ t ∈ Finset.range (J + 1), r ^ (J - t) = ∑ n ∈ Finset.range (J + 1), r ^ n := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun n hn => ?_
        have := Finset.mem_range.mp hn
        congr 1
        omega
    _ ≤ (1 - r)⁻¹ := by
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun n _ => pow_nonneg hr0 n

/-- **The sum over ordered scale indices.** -/
theorem monoSum_geom_le {L : ℝ} (hL : 1 < L) : ∀ (m : ℕ) (c : Fin m → ℝ), (∀ i, 0 < prefixSum c i) →
    ∀ J : ℕ, monoSum m (fun i t => L ^ (c i * ((t : ℝ) - J))) J ≤ ∏ i, (1 - L ^ (-prefixSum c i))⁻¹
  | 0, _, _, _ => by simp [monoSum]
  | m + 1, c, hc, J => by
    have hL0 : 0 < L := by linarith
    have hpos : ∀ i, 0 ≤ (1 - L ^ (-prefixSum c i))⁻¹ := fun i => by
      have : L ^ (-prefixSum c i) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith [hc i])
      exact inv_nonneg.mpr (by linarith)
    have hc' : ∀ i : Fin m, 0 < prefixSum (fun i => c i.castSucc) i := fun i => by
      rw [prefixSum_castSucc]; exact hc _
    unfold monoSum
    -- the inner sums, relative to the current largest index
    have hinner : ∀ t : ℕ, monoSum m (fun i t' => L ^ (c i.castSucc * ((t' : ℝ) - J))) t =
        L ^ ((∑ i : Fin m, c i.castSucc) * ((t : ℝ) - J)) *
          monoSum m (fun i t' => L ^ (c i.castSucc * ((t' : ℝ) - t))) t := by
      intro t
      have hfac : (fun (i : Fin m) (t' : ℕ) => L ^ (c i.castSucc * ((t' : ℝ) - J))) =
          fun (i : Fin m) (t' : ℕ) => L ^ (c i.castSucc * ((t : ℝ) - J)) * L ^ (c i.castSucc * ((t' : ℝ) - t)) := by
        funext i t'
        rw [← Real.rpow_add hL0]
        congr 1
        ring
      rw [hfac, monoSum_mul, ← Real.rpow_sum_of_pos hL0, Finset.sum_mul]
    calc ∑ t ∈ Finset.range (J + 1), L ^ (c (Fin.last m) * ((t : ℝ) - J)) *
          monoSum m (fun i t' => L ^ (c i.castSucc * ((t' : ℝ) - J))) t
        ≤ ∑ t ∈ Finset.range (J + 1), L ^ (prefixSum c (Fin.last m) * ((t : ℝ) - J)) *
            ∏ i : Fin m, (1 - L ^ (-prefixSum c i.castSucc))⁻¹ := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [hinner t, ← mul_assoc, ← Real.rpow_add hL0]
          have hIH := monoSum_geom_le hL m (fun i => c i.castSucc) hc' t
          simp_rw [prefixSum_castSucc] at hIH
          have hexp : c (Fin.last m) * ((t : ℝ) - J) + (∑ i : Fin m, c i.castSucc) * ((t : ℝ) - J) =
              prefixSum c (Fin.last m) * ((t : ℝ) - J) := by
            rw [prefixSum_last, Fin.sum_univ_castSucc]; ring
          rw [hexp]
          exact mul_le_mul_of_nonneg_left hIH (Real.rpow_pos_of_pos hL0 _).le
      _ = (∑ t ∈ Finset.range (J + 1), L ^ (prefixSum c (Fin.last m) * ((t : ℝ) - J))) *
            ∏ i : Fin m, (1 - L ^ (-prefixSum c i.castSucc))⁻¹ := by rw [Finset.sum_mul]
      _ ≤ (1 - L ^ (-prefixSum c (Fin.last m)))⁻¹ * ∏ i : Fin m, (1 - L ^ (-prefixSum c i.castSucc))⁻¹ :=
          mul_le_mul_of_nonneg_right (sum_rpow_le_inv hL (hc _) J)
            (Finset.prod_nonneg fun i _ => hpos _)
      _ = ∏ i, (1 - L ^ (-prefixSum c i))⁻¹ := by rw [Fin.prod_univ_castSucc]; ring

open Classical in
/-- The nondecreasing tuples with entries at most `J`. -/
noncomputable def monoSet (m J : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (J + 1)).filter fun u => Monotone u

lemma mem_monoSet {m J : ℕ} {u : Fin m → ℕ} : u ∈ monoSet m J ↔ (∀ i, u i ≤ J) ∧ Monotone u := by
  classical
  simp only [monoSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

lemma monotone_snoc {m : ℕ} {u : Fin m → ℕ} (hu : Monotone u) {t : ℕ} (ht : ∀ i, u i ≤ t) :
    Monotone (Fin.snoc u t : Fin (m + 1) → ℕ) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact le_rfl
    | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact ht a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_le.mpr (Fin.castSucc_lt_last b))
    | cast a => simp only [Fin.snoc_castSucc]; exact hu (Fin.castSucc_le_castSucc_iff.mp hab)

/-- **Sums over nondecreasing tuples** are the recursive sums monoSum. -/
theorem sum_monoSet_eq_monoSum : ∀ (m : ℕ) (g : Fin m → ℕ → ℝ) (J : ℕ),
    ∑ u ∈ monoSet m J, ∏ i, g i (u i) = monoSum m g J
  | 0, g, J => by
    have : monoSet 0 J = {fun i => Fin.elim0 i} := by
      ext u; simp only [mem_monoSet, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · intro _; exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    simp [this, monoSum]
  | m + 1, g, J => by
    rw [monoSum]
    simp_rw [← sum_monoSet_eq_monoSum m]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij' (fun u _ => ⟨u (Fin.last m), Fin.init u⟩) (fun x _ => Fin.snoc x.2 x.1) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨hle, hmono⟩ := mem_monoSet.mp hu
      simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff]
      refine ⟨hle _, mem_monoSet.mpr ⟨fun i => hmono (Fin.le_last _), fun a b hab => hmono ?_⟩⟩
      exact Fin.castSucc_le_castSucc_iff.mpr hab
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at hx
      obtain ⟨hle, hmono⟩ := mem_monoSet.mp hx.2
      refine mem_monoSet.mpr ⟨fun i => ?_, monotone_snoc hmono hle⟩
      induction i using Fin.lastCases with
      | last => simpa using hx.1
      | cast i => simp only [Fin.snoc_castSucc]; exact (hle i).trans hx.1
    · intro u _; exact Fin.snoc_init_self u
    · intro x _
      simp only [Fin.snoc_last, Fin.init_snoc]
    · intro u _
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.init]
      ring

/-- **The scale sum with a uniform constant**: if every prefix sum is at least `p₀ > 0`, the sum over nondecreasing
tuples `u < k` of `∏_i L^{c_i (u_i - k)}` is at most `(1 - L^{-p₀})^{-m}`, uniformly in `k`. -/
theorem sum_monoSet_rpow_le {L : ℝ} (hL : 1 < L) {m k : ℕ} (hk : 1 ≤ k) (c : Fin m → ℝ) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hc : ∀ i, p₀ ≤ prefixSum c i) :
    ∑ u ∈ monoSet m (k - 1), ∏ i, L ^ (c i * ((u i : ℝ) - k)) ≤ ((1 - L ^ (-p₀))⁻¹) ^ m := by
  have hL0 : 0 < L := by linarith
  have hJ : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; simp
  have hfac : (fun (i : Fin m) (t : ℕ) => L ^ (c i * ((t : ℝ) - k))) =
      fun (i : Fin m) (t : ℕ) => L ^ (-c i) * L ^ (c i * ((t : ℝ) - ((k - 1 : ℕ) : ℝ))) := by
    funext i t
    rw [← Real.rpow_add hL0, hJ]
    congr 1
    ring
  have hq : L ^ (-p₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
  have hq0 : 0 < 1 - L ^ (-p₀) := by linarith
  rw [sum_monoSet_eq_monoSum m (fun i t => L ^ (c i * ((t : ℝ) - k))), hfac, monoSum_mul]
  have hprodL : ∏ i, L ^ (-c i) ≤ 1 := by
    rw [← Real.rpow_sum_of_pos hL0]
    refine Real.rpow_le_one_of_one_le_of_nonpos hL.le ?_
    rw [Finset.sum_neg_distrib, neg_nonpos]
    cases m with
    | zero => simp
    | succ m' =>
      have := hc (Fin.last m')
      rw [prefixSum_last] at this
      linarith
  have hc' : ∀ i, 0 < prefixSum c i := fun i => lt_of_lt_of_le hp₀ (hc i)
  have hgeom := monoSum_geom_le hL m c hc' (k - 1)
  have hmono : ∏ i, (1 - L ^ (-prefixSum c i))⁻¹ ≤ ((1 - L ^ (-p₀))⁻¹) ^ m := by
    calc ∏ i, (1 - L ^ (-prefixSum c i))⁻¹ ≤ ∏ _i : Fin m, (1 - L ^ (-p₀))⁻¹ := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
          · have : L ^ (-prefixSum c i) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith [hc' i])
            exact inv_nonneg.mpr (by linarith)
          · have h1 : L ^ (-prefixSum c i) ≤ L ^ (-p₀) :=
              Real.rpow_le_rpow_of_exponent_le hL.le (by linarith [hc i])
            exact inv_anti₀ hq0 (by linarith)
      _ = ((1 - L ^ (-p₀))⁻¹) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hms0 : 0 ≤ monoSum m (fun i t => L ^ (c i * ((t : ℝ) - ((k - 1 : ℕ) : ℝ)))) (k - 1) :=
    monoSum_nonneg m _ (fun i t => (Real.rpow_pos_of_pos hL0 _).le) _
  calc (∏ i, L ^ (-c i)) * monoSum m (fun i t => L ^ (c i * ((t : ℝ) - ((k - 1 : ℕ) : ℝ)))) (k - 1)
      ≤ 1 * monoSum m (fun i t => L ^ (c i * ((t : ℝ) - ((k - 1 : ℕ) : ℝ)))) (k - 1) :=
        mul_le_mul_of_nonneg_right hprodL hms0
    _ ≤ ((1 - L ^ (-p₀))⁻¹) ^ m := by rw [one_mul]; exact hgeom.trans hmono

end GaussianBlockSpin
