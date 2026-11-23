import GaussianBlockSpin.Polynomials

/-! **Explicit Taylor coefficients** for the vertices of the perturbation expansion. Iterated derivatives of smooth
one-parameter families: through finite sums, constant factors, `PiLp 2` coordinates (iteratedDeriv_toLp_pi), the
Leibniz rule for inner products in finite dimension (iteratedDeriv_inner), and the transports
`∂_e^n e^{(t + e σ) Q} v = σ^n e^{t Q} Q^n v` at `0` (iteratedDeriv_exp_smul_apply). Mixed Taylor coefficients of
`F(y, e, l) = H(y, e) - l P₄(y) - ½ g(e, l) P₂(y)` (mixedCoeff_of_decomp_eq), of `λ` (mixedCoeff_snd) and of
`f - c` (mixedCoeff_sub_const). Used for the vertices of Bałaban III (1.6)-(1.18). -/

open scoped RealInnerProductSpace ContDiff
open Set

namespace GaussianBlockSpin

section DerivLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Iterated derivatives of finite sums of smooth families. -/
lemma iteratedDeriv_finset_sum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Finset ι)
    {f : ι → ℝ → F} (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun e => ∑ i ∈ s, f i e) x = ∑ i ∈ s, iteratedDeriv n (f i) x := by
  have h := iteratedDeriv_sum (I := s) (f := f) (x := x) (n := n)
    (fun i hi => (contDiff_of_infty (hf i hi) n).contDiffAt)
  rw [← h]
  congr 1
  funext e
  simp

/-- Iterated derivatives commute with constant scalar factors (smooth families). -/
lemma iteratedDeriv_const_smul_fun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun e => c • f e) x = c • iteratedDeriv n f x := by
  have h := iteratedDeriv_clm_apply (c • ContinuousLinearMap.id ℝ F) hf n x
  simp only [smul_apply, ContinuousLinearMap.id_apply] at h
  exact h

/-- `PiLp 2`-valued families with smooth coordinates are smooth. -/
lemma contDiff_toLp_pi {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {f : ∀ i, ℝ → β i} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun e => WithLp.toLp 2 (fun i => f i e)) :=
  ((PiLp.continuousLinearEquiv 2 ℝ β).symm : (∀ i, β i) →L[ℝ] PiLp 2 β).contDiff.comp (contDiff_pi.mpr hf)

/-- Iterated derivatives of `PiLp 2`-valued families are taken coordinatewise. -/
lemma iteratedDeriv_toLp_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℝ (β i)] {f : ∀ i, ℝ → β i} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun e => WithLp.toLp 2 (fun i => f i e)) x =
      WithLp.toLp 2 (fun i => iteratedDeriv n (f i) x) := by
  set L : (∀ i, β i) →L[ℝ] PiLp 2 β := ((PiLp.continuousLinearEquiv 2 ℝ β).symm : (∀ i, β i) →L[ℝ] PiLp 2 β)
  have hsum : (fun e => WithLp.toLp 2 (fun i => f i e)) =
      fun e => ∑ i, L (ContinuousLinearMap.single ℝ β i (f i e)) := by
    funext e
    rw [← map_sum]
    congr 1
    funext j
    simp [Finset.sum_apply, ContinuousLinearMap.single_apply]
  rw [hsum, iteratedDeriv_finset_sum (f := fun i e => L (ContinuousLinearMap.single ℝ β i (f i e))) _
    (fun i _ => (L.comp (ContinuousLinearMap.single ℝ β i)).contDiff.comp (hf i))]
  have hterm : ∀ i, iteratedDeriv n (fun e => L (ContinuousLinearMap.single ℝ β i (f i e))) x =
      L (ContinuousLinearMap.single ℝ β i (iteratedDeriv n (f i) x)) := fun i =>
    iteratedDeriv_clm_apply (L.comp (ContinuousLinearMap.single ℝ β i)) (hf i) n x
  simp_rw [hterm]
  rw [← map_sum]
  simp only [ContinuousLinearMap.single_apply, Finset.univ_sum_single]
  rfl

/-- **Leibniz for inner products** (finite dimension). -/
lemma iteratedDeriv_inner [FiniteDimensional ℝ V] {f g : ℝ → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun e => ⟪f e, g e⟫) x =
      ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * ⟪iteratedDeriv m f x, iteratedDeriv (n - m) g x⟫ := by
  set b := stdOrthonormalBasis ℝ V
  have hfi : ∀ i, ContDiff ℝ ∞ (fun e => ⟪b i, f e⟫) := fun i => (innerSL ℝ (b i)).contDiff.comp hf
  have hgi : ∀ i, ContDiff ℝ ∞ (fun e => ⟪b i, g e⟫) := fun i => (innerSL ℝ (b i)).contDiff.comp hg
  have hcoord : ∀ (h : ℝ → V) (hh : ContDiff ℝ ∞ h) (i) (m : ℕ),
      iteratedDeriv m (fun e => ⟪b i, h e⟫) x = ⟪b i, iteratedDeriv m h x⟫ := fun h hh i m =>
    iteratedDeriv_clm_apply (innerSL ℝ (b i)) hh m x
  have hexp : (fun e => ⟪f e, g e⟫) = fun e => ∑ i, ⟪b i, f e⟫ * ⟪b i, g e⟫ := by
    funext e
    rw [← b.sum_inner_mul_inner (f e) (g e)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (f e) (b i)]
  rw [hexp, iteratedDeriv_finset_sum _ (fun i _ => (hfi i).mul (hgi i))]
  have hmul : ∀ i, iteratedDeriv n (fun e => ⟪b i, f e⟫ * ⟪b i, g e⟫) x =
      ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * (⟪b i, iteratedDeriv m f x⟫ * ⟪b i, iteratedDeriv (n - m) g x⟫) := by
    intro i
    have h := iteratedDeriv_mul (x := x) (contDiff_of_infty (hfi i) n).contDiffAt (contDiff_of_infty (hgi i) n).contDiffAt
    show iteratedDeriv n ((fun e => ⟪b i, f e⟫) * (fun e => ⟪b i, g e⟫)) x = _
    rw [h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcoord f hf i m, hcoord g hg i (n - m)]
    ring
  simp_rw [hmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, ← b.sum_inner_mul_inner (iteratedDeriv m f x) (iteratedDeriv (n - m) g x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (iteratedDeriv m f x) (b i)]

/-- `e^{s Q} Q^n v = Q^n e^{s Q} v`. -/
lemma exp_smul_mul_pow_apply (Q : V →L[ℝ] V) (s : ℝ) (n : ℕ) (v : V) :
    (NormedSpace.exp (s • Q) * Q ^ n) v = (Q ^ n) (NormedSpace.exp (s • Q) v) := by
  have hc : Commute (NormedSpace.exp (s • Q)) (Q ^ n) := ((Commute.self_pow Q n).smul_left s).exp_left
  rw [hc.eq]
  rfl

variable [CompleteSpace V]

/-- `∂_e^n e^{(t + e σ) Q} v = σ^n e^{t Q} Q^n v` at `e = 0`. -/
lemma iteratedDeriv_exp_smul_apply (Q : V →L[ℝ] V) (t σ : ℝ) (v : V) (n : ℕ) :
    iteratedDeriv n (fun e : ℝ => NormedSpace.exp ((t + e * σ) • Q) v) 0 =
      σ ^ n • (NormedSpace.exp (t • Q) * Q ^ n) v := by
  set R := σ • Q
  have hsplit : ∀ e : ℝ, NormedSpace.exp ((t + e * σ) • Q) = NormedSpace.exp (t • Q) * NormedSpace.exp (e • R) := by
    intro e
    have hc : Commute (t • Q) (e • R) := (((Commute.refl Q).smul_left t).smul_right σ).smul_right e
    have hball : ∀ x : V →L[ℝ] V, x ∈ Metric.eball (0 : V →L[ℝ] V) (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius :=
      fun x => (NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℝ] V)).symm ▸ edist_lt_top _ _
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc (hball _) (hball _), add_smul, mul_smul]
  let L : (V →L[ℝ] V) →L[ℝ] V := (ContinuousLinearMap.apply ℝ V v).comp
    (ContinuousLinearMap.mul ℝ (V →L[ℝ] V) (NormedSpace.exp (t • Q)))
  have hL : ∀ M : V →L[ℝ] V, L M = (NormedSpace.exp (t • Q) * M) v := fun M => rfl
  have hfun : (fun e : ℝ => NormedSpace.exp ((t + e * σ) • Q) v) = fun e => L (NormedSpace.exp (e • R)) := by
    funext e
    rw [hL, hsplit]
  rw [hfun, iteratedDeriv_clm_apply L (contDiff_exp_smul R), iteratedDeriv_exp_smul]
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, R, smul_pow, hL]
  rw [mul_smul_comm, smul_apply]

end DerivLemmas

/-- The mixed coefficients of `F(y, e, l) = H(y, e) - l P₄(y) - ½ g(e, l) P₂(y)` (`H` smooth in `e`, `g` jointly
smooth). -/
lemma mixedCoeff_of_decomp_eq {E : Type*} {F : E → ℝ → ℝ → ℝ} {H : E → ℝ → ℝ} {P₄ P₂ : E → ℝ} {g : ℝ → ℝ → ℝ}
    (hH : ∀ y, ContDiff ℝ ∞ (H y)) (hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2))
    (hdec : ∀ y e l, F y e l = H y e - l * P₄ y - 1 / 2 * g e l * P₂ y) (i j : ℕ) (y : E) :
    mixedCoeff (Ici 0) i j (F y) = (if j = 0 then iteratedDeriv i (H y) 0 else 0) +
      (-P₄ y * mixedCoeff (Ici 0) i j (fun _ l => l) + -(1 / 2 * P₂ y) * mixedCoeff (Ici 0) i j g) := by
  have hs : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hl : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hF : F y = fun e l => H y e + (-P₄ y * l + -(1 / 2 * P₂ y) * g e l) := by
    funext e l
    rw [hdec]
    ring
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => H y p.1) := (hH y).comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -P₄ y * p.2) := contDiff_const.mul hl
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -(1 / 2 * P₂ y) * g p.1 p.2) := contDiff_const.mul hg
  rw [hF, mixedCoeff_add_of_contDiff hs h0 (f := fun e _ => H y e) h1 (h2.add h3),
    mixedCoeff_add_of_contDiff hs h0 (f := fun _ l => -P₄ y * l) h2 h3,
    mixedCoeff_const_mul_of_contDiff hs h0 (f := fun _ l => l) hl,
    mixedCoeff_const_mul_of_contDiff hs h0 hg, mixedCoeff_of_fst]

/-- `∂_λ^j ∂_e^i λ` at `(0, 0)` (within `[0, ∞)`) is `[i = 0, j = 1]`. -/
lemma mixedCoeff_snd (i j : ℕ) : mixedCoeff (Ici 0) i j (fun _ l => l) = if i = 0 ∧ j = 1 then 1 else 0 := by
  unfold mixedCoeff
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [iteratedDeriv_zero, true_and]
    rw [iteratedDerivWithin_eq_iteratedDeriv (f := fun l : ℝ => l) (uniqueDiffOn_Ici 0)
      (contDiff_id.contDiffAt : ContDiffAt ℝ j (fun l : ℝ => l) 0) (mem_Ici.mpr le_rfl)]
    rcases j with _ | _ | j
    · simp
    · simp
    · rw [iteratedDeriv_succ', iteratedDeriv_succ']
      simp
  · have : (fun l : ℝ => iteratedDeriv i (fun _ : ℝ => l) 0) = fun _ => 0 := by
      funext l
      simp [iteratedDeriv_const, hi.ne']
    rw [this, iteratedDerivWithin_const]
    simp [hi.ne']

/-- Mixed coefficients of positive order do not see additive constants. -/
lemma mixedCoeff_sub_const {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)) (c : ℝ) {i j : ℕ}
    (hij : 0 < i + j) : mixedCoeff (Ici 0) i j (fun e l => f e l - c) = mixedCoeff (Ici 0) i j f := by
  have hc : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => -c) := contDiff_const
  rw [show (fun e l => f e l - c) = fun e l => f e l + (fun (_ : ℝ) (_ : ℝ) => -c) e l from by
    funext e l; ring]
  rw [mixedCoeff_add_of_contDiff (uniqueDiffOn_Ici 0) (mem_Ici.mpr le_rfl) hf hc,
    show (fun (_ : ℝ) (_ : ℝ) => -c) = fun (e : ℝ) (_ : ℝ) => (fun _ : ℝ => -c) e from rfl, mixedCoeff_of_fst]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hj : j ≠ 0 := by omega
    simp [hj]
  · simp [iteratedDeriv_const, hi.ne']

end GaussianBlockSpin
