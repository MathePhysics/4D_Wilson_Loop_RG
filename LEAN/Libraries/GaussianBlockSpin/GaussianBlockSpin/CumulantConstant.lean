import GaussianBlockSpin.MonomialCumulants

/-! **The constant term of an interaction**: for `V` with all moments, `⟨(V + c)^n⟩^T = ⟨V^n⟩^T` for `n ≥ 2` and
`⟨(V + c)⟩^T = ⟨V⟩ + c` (truncExp_moments_add_const, truncExp_moments_add_const_one), so
`Σ_{n=1}^t ⟨(V + c)^n⟩^T/n! = c + Σ_{n=1}^t ⟨V^n⟩^T/n!` for `t ≥ 1` (cumulantSum_add_const). The proof: by
multilinearity `⟨(V + c)^n⟩^T` is a sum over tuples drawn from `{V, c}`, and for `n ≥ 2` a tuple containing the
constant has vanishing joint cumulant, since its moments factorise over the constant positions. -/

namespace GaussianBlockSpin

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The two pieces `V` (`true`) and the constant `c` (`false`). -/
def constPieces (V : Ω → ℝ) (c : ℝ) : Bool → Ω → ℝ := fun b => if b then V else fun _ => c

lemma integrable_prod_constPieces {V : Ω → ℝ} (hV : ∀ k : ℕ, Integrable (fun ω => V ω ^ k) μ) (c : ℝ) {n : ℕ}
    (T : Finset (Fin n)) (t : Fin n → Finset Bool) :
    Integrable (fun ω => ∏ v ∈ T, ∑ a ∈ t v, constPieces V c a ω) μ := by
  have hVm : AEStronglyMeasurable V μ := by simpa using (hV 1).aestronglyMeasurable
  have h1 : Integrable (fun ω => (1 : ℝ) + |V ω ^ T.card|) μ :=
    Integrable.add (integrable_const (1 : ℝ)) (hV T.card).abs
  have hdom : Integrable (fun ω => (1 + |c|) ^ T.card * (2 ^ T.card * (1 + |V ω ^ T.card|))) μ :=
    (h1.const_mul _).const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun ω => ?_)
  · have hpc : ∀ a, AEStronglyMeasurable (constPieces V c a) μ := fun a => by
      cases a
      · exact aestronglyMeasurable_const
      · exact hVm
    have hsum : ∀ v, AEStronglyMeasurable (fun ω => ∑ a ∈ t v, constPieces V c a ω) μ := fun v => by
      have h := Finset.aestronglyMeasurable_sum (f := fun a ω => constPieces V c a ω) (t v) fun a _ => hpc a
      convert h using 1
      funext ω
      simp [Finset.sum_apply]
    have h := Finset.aestronglyMeasurable_prod (f := fun v ω => ∑ a ∈ t v, constPieces V c a ω) T fun v _ => hsum v
    convert h using 1
    funext ω
    simp [Finset.prod_apply]
  · have hfac : ∀ v, |∑ a ∈ t v, constPieces V c a ω| ≤ (1 + |c|) * (1 + |V ω|) := by
      intro v
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ a ∈ t v, |constPieces V c a ω| ≤ ∑ a : Bool, |constPieces V c a ω| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => abs_nonneg _
        _ = |V ω| + |c| := by simp [constPieces, add_comm]
        _ ≤ (1 + |c|) * (1 + |V ω|) := by nlinarith [abs_nonneg c, abs_nonneg (V ω)]
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ v ∈ T, |∑ a ∈ t v, constPieces V c a ω| ≤ ∏ _v ∈ T, (1 + |c|) * (1 + |V ω|) :=
          Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => hfac v
      _ = (1 + |c|) ^ T.card * (1 + |V ω|) ^ T.card := by rw [Finset.prod_const, mul_pow]
      _ ≤ (1 + |c|) ^ T.card * (2 ^ T.card * (1 + |V ω ^ T.card|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_pow]
          have hx : 0 ≤ |V ω| := abs_nonneg _
          rcases le_total (|V ω|) 1 with h | h
          · calc (1 + |V ω|) ^ T.card ≤ 2 ^ T.card := pow_le_pow_left₀ (by positivity) (by linarith) _
              _ ≤ 2 ^ T.card * (1 + |V ω| ^ T.card) := le_mul_of_one_le_right (by positivity)
                  (by linarith [pow_nonneg hx T.card])
          · calc (1 + |V ω|) ^ T.card ≤ (2 * |V ω|) ^ T.card := pow_le_pow_left₀ (by positivity) (by linarith) _
              _ = 2 ^ T.card * |V ω| ^ T.card := mul_pow _ _ _
              _ ≤ 2 ^ T.card * (1 + |V ω| ^ T.card) := by gcongr; linarith

/-- The moments of a tuple whose positions in `A` are the constant factorise over `A`. -/
lemma moments_constPieces_split (V : Ω → ℝ) (c : ℝ) {n : ℕ} (g : Fin n → Bool) (A : Finset (Fin n))
    (hA : ∀ v ∈ A, g v = false) (U : Finset (Fin n)) :
    ∫ ω, ∏ v ∈ U, constPieces V c (g v) ω ∂μ =
      (∫ ω, ∏ v ∈ U ∩ A, constPieces V c (g v) ω ∂μ) * ∫ ω, ∏ v ∈ U \ A, constPieces V c (g v) ω ∂μ := by
  have hconst : ∀ ω, ∏ v ∈ U ∩ A, constPieces V c (g v) ω = c ^ (U ∩ A).card := fun ω => by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun v hv => ?_
    simp [constPieces, hA v (Finset.mem_inter.mp hv).2]
  simp_rw [← Finset.prod_inter_mul_prod_sdiff U A, hconst]
  rw [integral_const_mul, integral_const, probReal_univ, one_smul]

/-- **Higher truncated expectations ignore a constant**: `⟨(V + c)^n⟩^T = ⟨V^n⟩^T` for `n ≥ 2`. -/
theorem truncExp_moments_add_const {V : Ω → ℝ} (hV : ∀ k : ℕ, Integrable (fun ω => V ω ^ k) μ) (c : ℝ) {n : ℕ}
    (hn : 2 ≤ n) : truncExp (moments μ (fun ω => V ω + c)) n = truncExp (moments μ V) n := by
  classical
  have hsum : (fun ω => V ω + c) = fun ω => ∑ a, constPieces V c a ω := by
    funext ω; simp [constPieces]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [hsum, truncExp_moments_sum_eq μ (constPieces V c) (integrable_prod_constPieces μ hV c) (by omega)]
  rw [Finset.sum_eq_single (fun _ => true)]
  · have hM : (fun T : Finset (Fin n) => ∫ ω, ∏ v ∈ T, constPieces V c ((fun _ => true) v) ω ∂μ) =
        fun T => moments μ V T.card := by
      funext T
      simp [constPieces, moments, Finset.prod_const]
    rw [hM, jointCumulant_eq_truncExp (moments μ V) (moments_zero μ V) Finset.univ Finset.univ_nonempty,
      Finset.card_univ, Fintype.card_fin]
  · intro g _ hg
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, g i₀ = false := by
      by_contra hcon
      push Not at hcon
      exact hg (funext fun v => by simpa using hcon v)
    set Af := Finset.univ.filter fun v => g v = false with hAf
    by_cases hall : Af = Finset.univ
    · -- all positions are the constant: split off one of them
      have hA : ∀ v ∈ ({i₀} : Finset (Fin n)), g v = false := fun v hv => by
        rw [Finset.mem_singleton.mp hv]; exact hi₀
      have hne : (Finset.univ \ {i₀} : Finset (Fin n)).Nonempty := by
        have : 1 < (Finset.univ : Finset (Fin n)).card := by rw [Finset.card_univ, Fintype.card_fin]; omega
        obtain ⟨j, -, hj⟩ := Finset.exists_mem_ne this i₀
        exact ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using hj⟩⟩
      exact jointCumulant_eq_zero_of_split _ (by simp) (Finset.subset_univ _) (Finset.singleton_nonempty i₀) hne
        fun U _ => moments_constPieces_split μ V c g {i₀} hA U
    · have hA : ∀ v ∈ Af, g v = false := fun v hv => (Finset.mem_filter.mp hv).2
      have hne : (Finset.univ \ Af).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
        exact hall (Finset.Subset.antisymm (Finset.subset_univ _) hcon)
      exact jointCumulant_eq_zero_of_split _ (by simp) (Finset.subset_univ _)
        ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩ hne fun U _ => moments_constPieces_split μ V c g Af hA U
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `⟨(V + c)⟩^T = ⟨V⟩ + c`. -/
theorem truncExp_moments_add_const_one {V : Ω → ℝ} (hV : Integrable V μ) (c : ℝ) :
    truncExp (moments μ (fun ω => V ω + c)) 1 = truncExp (moments μ V) 1 + c := by
  rw [truncExp_one, truncExp_one]
  simp only [moments, pow_one]
  rw [integral_add hV (integrable_const c), integral_const, probReal_univ, one_smul]

/-- **The constant term of the cumulant sum**: `Σ_{n=1}^t ⟨(V + c)^n⟩^T/n! = c + Σ_{n=1}^t ⟨V^n⟩^T/n!`, `t ≥ 1`. -/
theorem cumulantSum_add_const {V : Ω → ℝ} (hV : ∀ k : ℕ, Integrable (fun ω => V ω ^ k) μ) (c : ℝ) {t : ℕ}
    (ht : 1 ≤ t) : cumulantSum μ (fun ω => V ω + c) t = cumulantSum μ V t + c := by
  have hV1 : Integrable V μ := by simpa using hV 1
  unfold cumulantSum
  have hI : Finset.Icc 1 t = insert 1 (Finset.Icc 2 t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 t := by simp
  rw [hI, Finset.sum_insert h1, Finset.sum_insert h1, truncExp_moments_add_const_one μ hV1 c,
    Finset.sum_congr rfl fun n hn => by rw [truncExp_moments_add_const μ hV c (Finset.mem_Icc.mp hn).1]]
  simp only [Nat.factorial_one, Nat.cast_one, div_one]
  ring

end GaussianBlockSpin
