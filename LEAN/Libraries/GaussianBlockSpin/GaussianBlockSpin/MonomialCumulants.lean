import GaussianBlockSpin.MonomialCompare
import GaussianBlockSpin.BoxMoments

/-! **The truncated expectations of a polynomial under two product laws** (restricted versus full one-dimensional
laws) and **after dropping monomials**, for `F = Σ_{X ∈ S} c_X ξ^X` with monomials of degrees in `[1, D]`,
`1 ≤ k ≤ t`, `C = monoConst D t K`, `a ≥ sup_y Σ_{X ∈ S ∋ y} |c_X| C`:
* abs_truncExp_sub_le_of_monomials: `|⟨F^k⟩^T_ν - ⟨F^k⟩^T_γ| ≤ c'_k η (Σ_{X ∈ S} |c_X| C) (k-1)! ∏_{j<k-1} ((D + j D) a)`;
* abs_truncExp_sub_le_of_subset: for `S' ⊆ S`, `|⟨F_S^k⟩^T - ⟨F_{S'}^k⟩^T| ≤ c_k k (Σ_{X ∈ S \ S'} |c_X| C) (k-1)!
  ∏_{j<k-1} ((D + j D) a)` under one product law.
The cumulants of disconnected tuples vanish under every product law, connected tuples are counted by
sum_connected_anchor_le, and abs_jointCumulant_sub_le (abs_jointCumulant_le) bounds the cumulants of one tuple. -/

namespace GaussianBlockSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- `⟨(Σ_{X ∈ s} Y_X)^k⟩^T` as a sum over tuples in `s^k`, for integrable products of partial sums. -/
theorem truncExp_moments_finset_sum_eq' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {P : Type*} [DecidableEq P] (s : Finset P) (Y : P → Ω → ℝ) {k : ℕ}
    (hint : ∀ (T : Finset (Fin k)) (tt : Fin k → Finset s),
      Integrable (fun ω => ∏ v ∈ T, ∑ a ∈ tt v, Y a.1 ω) μ) (hk : 0 < k) :
    truncExp (moments μ (fun ω => ∑ X ∈ s, Y X ω)) k =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => s),
        jointCumulant (fun T => ∫ ω, ∏ i ∈ T, Y (g i) ω ∂μ) Finset.univ := by
  have h := truncExp_moments_sum_eq μ (A := s) (n := k) (fun a => Y a.1) hint hk
  have hsum : (fun ω => ∑ a : s, Y a.1 ω) = fun ω => ∑ X ∈ s, Y X ω := by
    funext ω
    exact Finset.sum_coe_sort s (fun X => Y X ω)
  rw [hsum] at h
  rw [h]
  refine Finset.sum_bij (fun g _ => fun j => (g j).1) (fun g _ => ?_) (fun g1 _ g2 _ h12 => ?_)
    (fun g hg => ?_) (fun g _ => rfl)
  · exact Fintype.mem_piFinset.mpr fun j => (g j).2
  · funext j
    exact Subtype.ext (congrFun h12 j)
  · exact ⟨fun j => ⟨g j, Fintype.mem_piFinset.mp hg j⟩, Finset.mem_univ _, rfl⟩

/-- **Per-tuple moment bounds**: for monomials `g i` of degrees in `[1, D]` (`k ≤ t`), the moments of products of
pieces satisfy `|M(U)| ≤ ∏_{i ∈ U} |c_{g i}| C` under a product law with `|∫ x^q| ≤ 2 q! K`. -/
lemma abs_moment_monoPiece_le {t k : ℕ} {K : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hkt : k ≤ t) (hK : 1 ≤ 2 * K)
    (μ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (μ c)]
    (hμ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(μ c)| ≤ 2 * (q.factorial * K)) (coef : MonoIdx ι D → ℝ)
    (g : Fin k → MonoIdx ι D) (hg : ∀ i, 1 ≤ ((g i).1 : ℕ)) (U : Finset (Fin k)) :
    |∫ ξ, ∏ i ∈ U, monoPiece coef (g i) ξ ∂(Measure.pi μ)| ≤ ∏ i ∈ U, (|coef (g i)| * monoConst D t K) := by
  rw [integral_prod_monoPiece, abs_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.abs_prod]
  have hP := abs_prod_moments_le hK μ hμ (expoOf (fun i => (g i).toNat) U)
  rw [sum_expoOf] at hP
  set Q := ∑ i ∈ U, ((g i).toNat).1 with hQ
  have hQ1 : U.card ≤ Q := by
    rw [hQ, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun i _ => hg i
  have hQD : Q ≤ D * U.card := by
    rw [hQ, Finset.card_eq_sum_ones, Finset.mul_sum, mul_one]
    exact Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (g i).1.isLt
  have hU : U.card ≤ t := (Finset.card_le_univ U).trans (by simpa using hkt)
  have hC := pow_mul_factorial_le_monoConst hD ht hK hU hQ1 hQD
  have hmax : (Q.factorial : ℝ) * (2 * K) ^ Q ≤ (max 1 Q : ℕ) * (Q.factorial : ℝ) * (2 * K) ^ Q := by
    have : (1 : ℝ) ≤ (max 1 Q : ℕ) := by exact_mod_cast le_max_left 1 Q
    have h0 : 0 ≤ (Q.factorial : ℝ) * (2 * K) ^ Q := by positivity
    nlinarith
  calc (∏ i ∈ U, |coef (g i)|) * |∏ c, ∫ x, x ^ expoOf (fun i => (g i).toNat) U c ∂(μ c)|
      ≤ (∏ i ∈ U, |coef (g i)|) * ((Q.factorial : ℝ) * (2 * K) ^ Q) :=
        mul_le_mul_of_nonneg_left hP (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ ≤ (∏ i ∈ U, |coef (g i)|) * monoConst D t K ^ U.card :=
        mul_le_mul_of_nonneg_left (hmax.trans hC) (Finset.prod_nonneg fun i _ => abs_nonneg _)

/-- **Per-tuple moment differences**: `|M_ν(U) - M_γ(U)| ≤ η ∏_{i ∈ U} |c_{g i}| C`. -/
lemma abs_moment_monoPiece_sub_le {t k : ℕ} {K η : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hkt : k ≤ t) (hK : 1 ≤ 2 * K)
    (hη : 0 ≤ η) (ν γ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (ν c)] [∀ c, IsProbabilityMeasure (γ c)]
    (hν : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c)| ≤ 2 * (q.factorial * K))
    (hγ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(γ c)| ≤ 2 * (q.factorial * K))
    (hd : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c) - ∫ x, x ^ q ∂(γ c)| ≤ η * q.factorial)
    (coef : MonoIdx ι D → ℝ) (g : Fin k → MonoIdx ι D) (hg : ∀ i, 1 ≤ ((g i).1 : ℕ)) (U : Finset (Fin k)) :
    |∫ ξ, ∏ i ∈ U, monoPiece coef (g i) ξ ∂(Measure.pi ν) - ∫ ξ, ∏ i ∈ U, monoPiece coef (g i) ξ ∂(Measure.pi γ)|
      ≤ η * ∏ i ∈ U, (|coef (g i)| * monoConst D t K) := by
  rw [integral_prod_monoPiece, integral_prod_monoPiece, ← mul_sub, abs_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.abs_prod]
  have hP := abs_prod_moments_sub_le hK hη ν γ hν hγ hd (expoOf (fun i => (g i).toNat) U)
  rw [sum_expoOf] at hP
  set Q := ∑ i ∈ U, ((g i).toNat).1 with hQ
  have hQ1 : U.card ≤ Q := by
    rw [hQ, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun i _ => hg i
  have hQD : Q ≤ D * U.card := by
    rw [hQ, Finset.card_eq_sum_ones, Finset.mul_sum, mul_one]
    exact Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (g i).1.isLt
  have hU : U.card ≤ t := (Finset.card_le_univ U).trans (by simpa using hkt)
  have hC := pow_mul_factorial_le_monoConst hD ht hK hU hQ1 hQD
  have hmax : (Q : ℝ) * ((Q.factorial : ℝ) * (2 * K) ^ Q) ≤ (max 1 Q : ℕ) * (Q.factorial : ℝ) * (2 * K) ^ Q := by
    have : (Q : ℝ) ≤ (max 1 Q : ℕ) := by exact_mod_cast le_max_right 1 Q
    have h0 : 0 ≤ (Q.factorial : ℝ) * (2 * K) ^ Q := by positivity
    nlinarith
  calc (∏ i ∈ U, |coef (g i)|) * |∏ c, ∫ x, x ^ expoOf (fun i => (g i).toNat) U c ∂(ν c) -
        ∏ c, ∫ x, x ^ expoOf (fun i => (g i).toNat) U c ∂(γ c)|
      ≤ (∏ i ∈ U, |coef (g i)|) * (η * (Q : ℝ) * ((Q.factorial : ℝ) * (2 * K) ^ Q)) :=
        mul_le_mul_of_nonneg_left hP (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ ≤ (∏ i ∈ U, |coef (g i)|) * (η * monoConst D t K ^ U.card) := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => abs_nonneg _)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hmax.trans hC) hη
    _ = η * ((∏ i ∈ U, |coef (g i)|) * monoConst D t K ^ U.card) := by ring

/-- A tuple that is not connected has a split with disjoint supports, so its cumulant vanishes under every product
law. -/
lemma jointCumulant_monoPiece_eq_zero (μ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (μ c)]
    (coef : MonoIdx ι D → ℝ) {k : ℕ} (g : Fin k → MonoIdx ι D) (hg : ¬ TupleConnected monoSupp g) :
    jointCumulant (fun T => ∫ ξ, ∏ i ∈ T, monoPiece coef (g i) ξ ∂(Measure.pi μ)) Finset.univ = 0 := by
  unfold TupleConnected at hg
  push Not at hg
  obtain ⟨A, hA, hAc, hdisj⟩ := hg
  exact jointCumulant_local_eq_zero μ (fun i => monoPiece coef (g i)) (fun i => monoSupp (g i))
    (fun i => dependsOn_monoPiece coef (g i)) (fun i => measurable_monoPiece coef (g i)) (Finset.subset_univ A)
    hA hAc hdisj

/-- **Truncated expectations of a polynomial under two product laws**. -/
theorem abs_truncExp_sub_le_of_monomials {t k : ℕ} {K η a : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hk1 : 1 ≤ k)
    (hkt : k ≤ t) (hK : 1 ≤ 2 * K) (hη : 0 ≤ η) (ha0 : 0 ≤ a) (ν γ : ι → Measure ℝ)
    [∀ c, IsProbabilityMeasure (ν c)] [∀ c, IsProbabilityMeasure (γ c)]
    (hν : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c)| ≤ 2 * (q.factorial * K))
    (hγ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(γ c)| ≤ 2 * (q.factorial * K))
    (hd : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c) - ∫ x, x ^ q ∂(γ c)| ≤ η * q.factorial)
    (hpν : ∀ c (r : ℕ), Integrable (fun x : ℝ => (1 + |x|) ^ r) (ν c))
    (hpγ : ∀ c (r : ℕ), Integrable (fun x : ℝ => (1 + |x|) ^ r) (γ c))
    (coef : MonoIdx ι D → ℝ) (S : Finset (MonoIdx ι D)) (hS : ∀ X ∈ S, 1 ≤ (X.1 : ℕ))
    (ha : ∀ y, ∑ X ∈ Finset.univ.filter (fun X => y ∈ monoSupp X),
      (if X ∈ S then |coef X| * monoConst D t K else 0) ≤ a) :
    |truncExp (moments (Measure.pi ν) (fun ξ => ∑ X ∈ S, monoPiece coef X ξ)) k -
        truncExp (moments (Measure.pi γ) (fun ξ => ∑ X ∈ S, monoPiece coef X ξ)) k| ≤
      cumLip k * η * ((∑ X ∈ S, |coef X| * monoConst D t K) *
        ((k - 1).factorial * ∏ j ∈ Finset.range (k - 1), ((D + j * D : ℝ) * a))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set C := monoConst D t K with hCdef
  have hC1 : 1 ≤ C := one_le_monoConst hD ht hK
  set B : MonoIdx ι D → ℝ := fun X => if X ∈ S then |coef X| * C else 0 with hB
  have hB0 : ∀ X, 0 ≤ B X := fun X => by
    simp only [hB]; split_ifs
    · exact mul_nonneg (abs_nonneg _) (by linarith)
    · exact le_rfl
  rw [truncExp_moments_finset_sum_eq' (Measure.pi ν) S (monoPiece coef)
      (fun T tt => integrable_prod_sum_monoPiece ν hpν coef (fun a : S => a.1) T tt) (Nat.succ_pos k'),
    truncExp_moments_finset_sum_eq' (Measure.pi γ) S (monoPiece coef)
      (fun T tt => integrable_prod_sum_monoPiece γ hpγ coef (fun a : S => a.1) T tt) (Nat.succ_pos k'),
    ← Finset.sum_sub_distrib]
  -- each tuple
  have hterm : ∀ g ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => S),
      |jointCumulant (fun T => ∫ ξ, ∏ i ∈ T, monoPiece coef (g i) ξ ∂(Measure.pi ν)) Finset.univ -
        jointCumulant (fun T => ∫ ξ, ∏ i ∈ T, monoPiece coef (g i) ξ ∂(Measure.pi γ)) Finset.univ| ≤
      if TupleConnected monoSupp g then cumLip (k' + 1) * η * ∏ i, B (g i) else 0 := by
    intro g hg
    have hgS : ∀ i, g i ∈ S := fun i => Fintype.mem_piFinset.mp hg i
    have hdeg : ∀ i, 1 ≤ ((g i).1 : ℕ) := fun i => hS _ (hgS i)
    by_cases hc : TupleConnected monoSupp g
    · rw [ite_eq_left hc]
      have h := abs_jointCumulant_sub_le _ _ (fun i => |coef (g i)| * C)
        (fun i => mul_nonneg (abs_nonneg _) (by linarith)) hη Finset.univ
        (fun U _ => abs_moment_monoPiece_le hD ht hkt hK ν hν coef g hdeg U)
        (fun U _ => abs_moment_monoPiece_le hD ht hkt hK γ hγ coef g hdeg U)
        (fun U _ => abs_moment_monoPiece_sub_le hD ht hkt hK hη ν γ hν hγ hd coef g hdeg U)
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hB, hgS i]
    · rw [ite_eq_right hc, jointCumulant_monoPiece_eq_zero ν coef g hc, jointCumulant_monoPiece_eq_zero γ coef g hc,
        sub_zero, abs_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter]
  have hext : ∑ g ∈ (Fintype.piFinset fun _ : Fin (k' + 1) => S).filter (fun g => TupleConnected monoSupp g),
      cumLip (k' + 1) * η * ∏ i, B (g i) ≤
      cumLip (k' + 1) * η * ∑ f ∈ Finset.univ.filter (fun f : Fin (k' + 1) → MonoIdx ι D =>
        TupleConnected monoSupp f ∧ f 0 ∈ Finset.univ), ∏ i, B (f i) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ =>
      Finset.prod_nonneg fun i _ => hB0 _) (mul_nonneg (cumLip_nonneg _) hη)
    intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2, Finset.mem_univ _⟩
  refine hext.trans ?_
  have hanchor := sum_connected_anchor_le monoSupp B hB0 (fun X => monoSupp_card_le X) ha0 ha k' 0 Finset.univ
  have hsumB : ∑ X ∈ Finset.univ, B X = ∑ X ∈ S, |coef X| * C := by
    rw [hB, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsumB] at hanchor
  simp only [Nat.add_sub_cancel]
  exact mul_le_mul_of_nonneg_left hanchor (mul_nonneg (cumLip_nonneg _) hη)

/-- **Dropping monomials** (the truncation to a finite range): for `S' ⊆ S` with the dropped monomials
`L = S \ S'`, under one product law,
`|⟨F_S^k⟩^T - ⟨F_{S'}^k⟩^T| ≤ c_k k (Σ_{X ∈ L} |c_X| C) (k-1)! ∏_{j<k-1} ((D + j D) a)`. -/
theorem abs_truncExp_sub_le_of_subset {t k : ℕ} {K a : ℝ} (hD : 1 ≤ D) (ht : 1 ≤ t) (hk1 : 1 ≤ k)
    (hkt : k ≤ t) (hK : 1 ≤ 2 * K) (ha0 : 0 ≤ a) (γ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (γ c)]
    (hγ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(γ c)| ≤ 2 * (q.factorial * K))
    (hpγ : ∀ c (r : ℕ), Integrable (fun x : ℝ => (1 + |x|) ^ r) (γ c))
    (coef : MonoIdx ι D → ℝ) (S S' : Finset (MonoIdx ι D)) (hSS' : S' ⊆ S) (hS : ∀ X ∈ S, 1 ≤ (X.1 : ℕ))
    (ha : ∀ y, ∑ X ∈ Finset.univ.filter (fun X => y ∈ monoSupp X),
      (if X ∈ S then |coef X| * monoConst D t K else 0) ≤ a) :
    |truncExp (moments (Measure.pi γ) (fun ξ => ∑ X ∈ S, monoPiece coef X ξ)) k -
        truncExp (moments (Measure.pi γ) (fun ξ => ∑ X ∈ S', monoPiece coef X ξ)) k| ≤
      cumBound k * k * ((∑ X ∈ S \ S', |coef X| * monoConst D t K) *
        ((k - 1).factorial * ∏ j ∈ Finset.range (k - 1), ((D + j * D : ℝ) * a))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set C := monoConst D t K with hCdef
  have hC1 : 1 ≤ C := one_le_monoConst hD ht hK
  set B : MonoIdx ι D → ℝ := fun X => if X ∈ S then |coef X| * C else 0 with hB
  have hB0 : ∀ X, 0 ≤ B X := fun X => by
    simp only [hB]; split_ifs
    · exact mul_nonneg (abs_nonneg _) (by linarith)
    · exact le_rfl
  set κ : (Fin (k' + 1) → MonoIdx ι D) → ℝ := fun g =>
    jointCumulant (fun T => ∫ ξ, ∏ i ∈ T, monoPiece coef (g i) ξ ∂(Measure.pi γ)) Finset.univ with hκ
  rw [truncExp_moments_finset_sum_eq' (Measure.pi γ) S (monoPiece coef)
      (fun T tt => integrable_prod_sum_monoPiece γ hpγ coef (fun a : S => a.1) T tt) (Nat.succ_pos k'),
    truncExp_moments_finset_sum_eq' (Measure.pi γ) S' (monoPiece coef)
      (fun T tt => integrable_prod_sum_monoPiece γ hpγ coef (fun a : S' => a.1) T tt) (Nat.succ_pos k')]
  have hpisub : Fintype.piFinset (fun _ : Fin (k' + 1) => S') ⊆ Fintype.piFinset (fun _ => S) :=
    fun g hg => Fintype.mem_piFinset.mpr fun i => hSS' (Fintype.mem_piFinset.mp hg i)
  rw [← Finset.sum_sdiff hpisub, add_sub_cancel_right]
  -- each remaining tuple has a dropped monomial; only connected ones count
  have hterm : ∀ g ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => S) \ Fintype.piFinset (fun _ => S'),
      |κ g| ≤ ∑ i, if TupleConnected monoSupp g ∧ g i ∈ S \ S' then cumBound (k' + 1) * ∏ j, B (g j) else 0 := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
    have hgS : ∀ i, g i ∈ S := fun i => Fintype.mem_piFinset.mp hg1 i
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, g i₀ ∉ S' := by
      by_contra hcon; push Not at hcon; exact hg2 (Fintype.mem_piFinset.mpr hcon)
    have hsum0 : 0 ≤ ∑ i, (if TupleConnected monoSupp g ∧ g i ∈ S \ S' then
        cumBound (k' + 1) * ∏ j, B (g j) else 0) :=
      Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact mul_nonneg (cumBound_nonneg _) (Finset.prod_nonneg fun j _ => hB0 _)
        · exact le_rfl
    by_cases hc : TupleConnected monoSupp g
    · have hdeg : ∀ i, 1 ≤ ((g i).1 : ℕ) := fun i => hS _ (hgS i)
      have h := abs_jointCumulant_le _ (fun i => |coef (g i)| * C) (fun i => mul_nonneg (abs_nonneg _) (by linarith))
        Finset.univ (fun U _ => abs_moment_monoPiece_le hD ht hkt hK γ hγ coef g hdeg U)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have hprod : ∏ i, (|coef (g i)| * C) = ∏ j, B (g j) :=
        Finset.prod_congr rfl fun i _ => by simp [hB, hgS i]
      rw [hprod] at h
      have hsingle := Finset.single_le_sum (f := fun i => if TupleConnected monoSupp g ∧ g i ∈ S \ S' then
        cumBound (k' + 1) * ∏ j, B (g j) else 0) (fun i _ => by
          beta_reduce; split_ifs
          · exact mul_nonneg (cumBound_nonneg _) (Finset.prod_nonneg fun j _ => hB0 _)
          · exact le_rfl) (Finset.mem_univ i₀)
      have hval : (if TupleConnected monoSupp g ∧ g i₀ ∈ S \ S' then cumBound (k' + 1) * ∏ j, B (g j) else 0) =
          cumBound (k' + 1) * ∏ j, B (g j) :=
        ite_eq_left_of_eq_true _ _ (eq_true ⟨hc, Finset.mem_sdiff.mpr ⟨hgS i₀, hi₀⟩⟩)
      exact h.trans ((le_of_eq hval.symm).trans hsingle)
    · rw [hκ]; dsimp only
      rw [jointCumulant_monoPiece_eq_zero γ coef g hc, abs_zero]
      exact hsum0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_comm]
  have hone : ∀ i : Fin (k' + 1), ∑ g ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => S) \ Fintype.piFinset (fun _ => S'),
      (if TupleConnected monoSupp g ∧ g i ∈ S \ S' then cumBound (k' + 1) * ∏ j, B (g j) else 0) ≤
      cumBound (k' + 1) * ((∑ X ∈ S \ S', |coef X| * C) *
        (k'.factorial * ∏ j ∈ Finset.range k', ((D + j * D : ℝ) * a))) := by
    intro i
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (cumBound_nonneg _)
    have hanchor := sum_connected_anchor_le monoSupp B hB0 (fun X => monoSupp_card_le X) ha0 ha k' i (S \ S')
    have hsumB : ∑ X ∈ S \ S', B X = ∑ X ∈ S \ S', |coef X| * C :=
      Finset.sum_congr rfl fun X hX => by simp [hB, (Finset.mem_sdiff.mp hX).1]
    rw [hsumB] at hanchor
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ =>
      Finset.prod_nonneg fun j _ => hB0 _) hanchor
    intro g hg
    obtain ⟨-, hc, hgi⟩ := (Finset.mem_filter.mp hg)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hgi⟩
  calc ∑ i : Fin (k' + 1), ∑ g ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => S) \ Fintype.piFinset (fun _ => S'),
        (if TupleConnected monoSupp g ∧ g i ∈ S \ S' then cumBound (k' + 1) * ∏ j, B (g j) else 0)
      ≤ ∑ _i : Fin (k' + 1), cumBound (k' + 1) * ((∑ X ∈ S \ S', |coef X| * C) *
          (k'.factorial * ∏ j ∈ Finset.range k', ((D + j * D : ℝ) * a))) := Finset.sum_le_sum fun i _ => hone i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.add_sub_cancel]
        push_cast
        ring

end GaussianBlockSpin
