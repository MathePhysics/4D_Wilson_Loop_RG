import GaussianBlockSpin.Cumulants

/-! Derivatives of `exp ∘ F` and `log ∘ Z` at a point, in one variable (within a set with unique derivatives) and
for the mixed Taylor coefficients `∂_λ^b ∂_e^a f(0, 0)` of (3.36) (`mixedCoeff`, `e` two-sided, `λ` within a set such
as `[0, ∞)`). One variable: `(e^F)^{(n+1)} = Σ_i C(n, i) F^{(i+1)} (e^F)^{(n-i)}` and `(log Z)^{(n+1)} = ⟨V^{n+1}⟩^T`
for the "moments" `Z^{(k)}/Z` (I.(3.23)). Two variables: the Leibniz rule, the `e`- and `λ`-steps for `exp ∘ F`, and
the nested regularity `NestedSmooth` with its closure under `exp` and `log`. -/

open scoped Topology

namespace GaussianBlockSpin

/-- **Uniqueness of the truncated expectations**: a sequence `c` satisfying the recursion of `moment_succ_eq` up to order
`N` agrees with `truncExp m` up to order `N`. -/
theorem eq_truncExp_of_recursion (m c : ℕ → ℝ) (hm0 : m 0 = 1) (N : ℕ)
    (hrec : ∀ k < N, m (k + 1) = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * c (i + 1) * m (k - i)) :
    ∀ k < N, c (k + 1) = truncExp m (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hrec k hk
    have h2 := moment_succ_eq m hm0 k
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, hm0] at h1 h2
    have hs : ∑ i ∈ Finset.range k, (k.choose i : ℝ) * c (i + 1) * m (k - i) =
        ∑ i ∈ Finset.range k, (k.choose i : ℝ) * truncExp m (i + 1) * m (k - i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega)]
    push_cast at h1 h2
    linarith

section OneVariable

variable {s : Set ℝ} {x : ℝ}

/-- **Derivatives of `exp ∘ F`**: `(e^F)^{(n+1)} = Σ_{i ≤ n} C(n, i) F^{(i+1)} (e^F)^{(n-i)}`, within a set with unique
derivatives. -/
theorem iteratedDerivWithin_exp_comp_succ (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) {F : ℝ → ℝ} {n : ℕ}
    (hF : ContDiffWithinAt ℝ (n + 1) F s x) :
    iteratedDerivWithin (n + 1) (fun t => Real.exp (F t)) s x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDerivWithin (i + 1) F s x *
        iteratedDerivWithin (n - i) (fun t => Real.exp (F t)) s x := by
  rw [iteratedDerivWithin_succ']
  have hins : insert x s = s := Set.insert_eq_of_mem hx
  have hev : derivWithin (fun t => Real.exp (F t)) s =ᶠ[𝓝[insert x s] x]
      derivWithin F s * (fun t => Real.exp (F t)) := by
    have h1 := hF.eventually (by simp)
    rw [hins] at h1 ⊢
    filter_upwards [h1, self_mem_nhdsWithin] with y hy hys
    rw [derivWithin_exp (hy.differentiableWithinAt (by simp)) (hs y hys)]
    simp only [Pi.mul_apply]
    ring
  rw [hev.iteratedDerivWithin_eq_of_nhds_insert, iteratedDerivWithin_mul hx hs]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDerivWithin_succ' (n := i)]
  · exact hF.derivWithin hs le_rfl hx
  · exact (hF.of_le (by norm_cast; omega)).exp

/-- **Derivatives of `log Z` are truncated expectations**: for `Z` of class `C^{n+1}` within `s` at `x` with `Z x > 0`,
`(log Z)^{(n+1)}(x) = ⟨V^{n+1}⟩^T` for the "moments" `m_k = Z^{(k)}(x) / Z(x)` (I.(3.23)). -/
theorem iteratedDerivWithin_log_eq_truncExp (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) {Z : ℝ → ℝ} {n : ℕ}
    (hZ : ContDiffWithinAt ℝ (n + 1) Z s x) (hpos : 0 < Z x) :
    iteratedDerivWithin (n + 1) (fun t => Real.log (Z t)) s x =
      truncExp (fun k => iteratedDerivWithin k Z s x / Z x) (n + 1) := by
  have hins : insert x s = s := Set.insert_eq_of_mem hx
  have hZexp : (fun t => Real.exp (Real.log (Z t))) =ᶠ[𝓝[insert x s] x] Z := by
    rw [hins]
    filter_upwards [hZ.continuousWithinAt.eventually (lt_mem_nhds hpos)] with y hy
    exact Real.exp_log hy
  have hm0 : (fun k => iteratedDerivWithin k Z s x / Z x) 0 = 1 := by
    simp [iteratedDerivWithin_zero, hpos.ne']
  refine eq_truncExp_of_recursion _ (fun j => iteratedDerivWithin j (fun t => Real.log (Z t)) s x) hm0 (n + 1)
    (fun k hk => ?_) n (Nat.lt_succ_self n)
  have hF : ContDiffWithinAt ℝ (k + 1) (fun t => Real.log (Z t)) s x :=
    (hZ.of_le (by norm_cast)).log hpos.ne'
  have h := iteratedDerivWithin_exp_comp_succ hs hx hF
  rw [hZexp.iteratedDerivWithin_eq_of_nhds_insert] at h
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hZexp.iteratedDerivWithin_eq_of_nhds_insert]
  ring

end OneVariable

/-- The mixed Taylor coefficient `∂_λ^b ∂_e^a f(0, 0)`: `a` derivatives in the first variable at `0`, then `b`
derivatives of the result in the second variable within `s` at `0` (`s = [0, ∞)` for the coupling `λ'` of (3.36)). -/
noncomputable def mixedCoeff (s : Set ℝ) (a b : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  iteratedDerivWithin b (fun l => iteratedDeriv a (fun e => f e l) 0) s 0

/-- Nested regularity of order `(A, B)` at `(0, 0)`: `e ↦ f e l` is `C^A` at `0` for all `l` near `0` in `s`, and each
`l ↦ ∂_e^i f(0, l)`, `i ≤ A`, is `C^B` within `s` at `0`. -/
structure NestedSmooth (s : Set ℝ) (A B : ℕ) (f : ℝ → ℝ → ℝ) : Prop where
  inner : ∀ᶠ l in 𝓝[s] 0, ContDiffAt ℝ A (fun e => f e l) 0
  outer : ∀ i ≤ A, ContDiffWithinAt ℝ B (fun l => iteratedDeriv i (fun e => f e l) 0) s 0

section TwoVariables

variable {s : Set ℝ}

/-- `b` derivatives within `s` at `0` of a function that is near `0` a finite sum of products. -/
lemma iteratedDerivWithin_eventually_sum_mul (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {ι : Type*}
    {I : Finset ι} {b : ℕ} {h : ℝ → ℝ} (c : ι → ℝ) (P Q : ι → ℝ → ℝ)
    (hev : ∀ᶠ l in 𝓝[s] 0, h l = ∑ i ∈ I, c i * P i l * Q i l)
    (hP : ∀ i ∈ I, ContDiffWithinAt ℝ b (P i) s 0) (hQ : ∀ i ∈ I, ContDiffWithinAt ℝ b (Q i) s 0) :
    iteratedDerivWithin b h s 0 = ∑ i ∈ I, ∑ j ∈ Finset.range (b + 1),
      c i * (b.choose j : ℝ) * iteratedDerivWithin j (P i) s 0 * iteratedDerivWithin (b - j) (Q i) s 0 := by
  have hins : insert (0 : ℝ) s = s := Set.insert_eq_of_mem h0
  rw [← hins] at hev
  rw [Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert b hev]
  have hfun : (fun l => ∑ i ∈ I, c i * P i l * Q i l) = ∑ i ∈ I, fun l => c i * (P i l * Q i l) := by
    funext l
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun, iteratedDerivWithin_sum h0 hs]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hm := iteratedDerivWithin_mul h0 hs (hP i hi) (hQ i hi)
    simp only [Pi.mul_def] at hm
    rw [iteratedDerivWithin_const_mul_field, hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · exact fun i hi => contDiffWithinAt_const.mul ((hP i hi).mul (hQ i hi))

/-- The inner Leibniz rule near `0`. -/
lemma eventually_iteratedDeriv_mul {A B : ℕ} {f g : ℝ → ℝ → ℝ} (hf : NestedSmooth s A B f)
    (hg : NestedSmooth s A B g) {a : ℕ} (ha : a ≤ A) :
    ∀ᶠ l in 𝓝[s] 0, iteratedDeriv a (fun e => f e l * g e l) 0 =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv i (fun e => f e l) 0 *
        iteratedDeriv (a - i) (fun e => g e l) 0 := by
  filter_upwards [hf.inner, hg.inner] with l hfl hgl
  have h := iteratedDeriv_mul (hfl.of_le (by exact_mod_cast ha)) (hgl.of_le (by exact_mod_cast ha))
  simpa only [Pi.mul_def] using h

/-- **Leibniz rule for mixed Taylor coefficients**:
`∂^{(a,b)}(f g) = Σ_{i ≤ a} Σ_{j ≤ b} C(a, i) C(b, j) ∂^{(i,j)} f ∂^{(a-i,b-j)} g`. -/
theorem mixedCoeff_mul (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : NestedSmooth s A B f) (hg : NestedSmooth s A B g) {a b : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    mixedCoeff s a b (fun e l => f e l * g e l) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), (a.choose i : ℝ) * (b.choose j : ℝ) *
        mixedCoeff s i j f * mixedCoeff s (a - i) (b - j) g := by
  unfold mixedCoeff
  rw [iteratedDerivWithin_eventually_sum_mul hs h0 (fun i => (a.choose i : ℝ))
    (fun i l => iteratedDeriv i (fun e => f e l) 0) (fun i l => iteratedDeriv (a - i) (fun e => g e l) 0)
    (eventually_iteratedDeriv_mul hf hg ha)
    (fun i hi => (hf.outer i ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans ha)).of_le (by exact_mod_cast hb))
    (fun i hi => (hg.outer (a - i) ((Nat.sub_le a i).trans ha)).of_le (by exact_mod_cast hb))]

/-- **The `e`-step of the derivatives of `exp ∘ F`**:
`∂^{(a+1,b)} e^F = Σ_{i ≤ a} Σ_{j ≤ b} C(a, i) C(b, j) ∂^{(i+1,j)} F ∂^{(a-i,b-j)} e^F`. -/
theorem mixedCoeff_exp_succ_left (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : NestedSmooth s (A + 1) B F) (hE : NestedSmooth s A B fun e l => Real.exp (F e l)) {a b : ℕ}
    (ha : a ≤ A) (hb : b ≤ B) :
    mixedCoeff s (a + 1) b (fun e l => Real.exp (F e l)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), (a.choose i : ℝ) * (b.choose j : ℝ) *
        mixedCoeff s (i + 1) j F * mixedCoeff s (a - i) (b - j) (fun e l => Real.exp (F e l)) := by
  have hev : ∀ᶠ l in 𝓝[s] 0, iteratedDeriv (a + 1) (fun e => Real.exp (F e l)) 0 =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * iteratedDeriv (i + 1) (fun e => F e l) 0 *
        iteratedDeriv (a - i) (fun e => Real.exp (F e l)) 0 := by
    filter_upwards [hF.inner] with l hl
    have h := iteratedDerivWithin_exp_comp_succ uniqueDiffOn_univ (Set.mem_univ (0 : ℝ))
      (F := fun e => F e l) (n := a) ((hl.of_le (by exact_mod_cast Nat.succ_le_succ ha)).contDiffWithinAt)
    simpa only [iteratedDerivWithin_univ] using h
  unfold mixedCoeff
  rw [iteratedDerivWithin_eventually_sum_mul hs h0 (fun i => (a.choose i : ℝ))
    (fun i l => iteratedDeriv (i + 1) (fun e => F e l) 0)
    (fun i l => iteratedDeriv (a - i) (fun e => Real.exp (F e l)) 0) hev
    (fun i hi => (hF.outer (i + 1) (Nat.succ_le_succ ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans ha))).of_le
      (by exact_mod_cast hb))
    (fun i hi => (hE.outer (a - i) ((Nat.sub_le a i).trans ha)).of_le (by exact_mod_cast hb))]

/-- **The `λ`-step of the derivatives of `exp ∘ F`** (no `e`-derivatives):
`∂^{(0,b+1)} e^F = Σ_{j ≤ b} C(b, j) ∂^{(0,j+1)} F ∂^{(0,b-j)} e^F`. -/
theorem mixedCoeff_exp_succ_right (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {F : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : ContDiffWithinAt ℝ (b + 1) (fun l => F 0 l) s 0) :
    mixedCoeff s 0 (b + 1) (fun e l => Real.exp (F e l)) =
      ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * mixedCoeff s 0 (j + 1) F *
        mixedCoeff s 0 (b - j) (fun e l => Real.exp (F e l)) := by
  unfold mixedCoeff
  simp only [iteratedDeriv_zero]
  exact iteratedDerivWithin_exp_comp_succ hs h0 hF

lemma mixedCoeff_zero_zero (f : ℝ → ℝ → ℝ) : mixedCoeff s 0 0 f = f 0 0 := by
  simp [mixedCoeff]

lemma NestedSmooth.mono {A B A' B' : ℕ} {f : ℝ → ℝ → ℝ} (hf : NestedSmooth s A B f) (hA : A' ≤ A) (hB : B' ≤ B) :
    NestedSmooth s A' B' f where
  inner := by
    filter_upwards [hf.inner] with l hl
    exact hl.of_le (by exact_mod_cast hA)
  outer := fun i hi => (hf.outer i (hi.trans hA)).of_le (by exact_mod_cast hB)

/-- Mixed coefficients only see the germ of `f` at `(0, 0)` (within `ℝ × s`). -/
lemma mixedCoeff_congr (h0 : (0 : ℝ) ∈ s) {f g : ℝ → ℝ → ℝ} (h : ∀ᶠ l in 𝓝[s] 0, ∀ᶠ e in 𝓝 0, f e l = g e l)
    (a b : ℕ) : mixedCoeff s a b f = mixedCoeff s a b g := by
  have hins : insert (0 : ℝ) s = s := Set.insert_eq_of_mem h0
  have hev : (fun l => iteratedDeriv a (fun e => f e l) 0) =ᶠ[𝓝[insert 0 s] 0]
      (fun l => iteratedDeriv a (fun e => g e l) 0) := by
    rw [hins]
    filter_upwards [h] with l hl
    exact (Filter.EventuallyEq.iteratedDeriv (f₁ := fun e => f e l) (f₂ := fun e => g e l) hl a).eq_of_nhds
  unfold mixedCoeff
  exact hev.iteratedDerivWithin_eq_of_nhds_insert b

/-- `truncExp` of `C^B` functions is `C^B`. -/
lemma contDiffWithinAt_truncExp {x : ℝ} {B : ℕ} {m : ℕ → ℝ → ℝ} {N : ℕ}
    (hm : ∀ j ≤ N, ContDiffWithinAt ℝ B (m j) s x) :
    ∀ n ≤ N, ContDiffWithinAt ℝ B (fun l => truncExp (fun j => m j l) n) s x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    cases n with
    | zero =>
      simp only [truncExp]
      exact contDiffWithinAt_const
    | succ k =>
      have hfun : (fun l => truncExp (fun j => m j l) (k + 1)) = fun l => m (k + 1) l -
          ∑ j : Fin k, (k.choose j : ℝ) * truncExp (fun j => m j l) (j + 1) * m (k - j) l := by
        funext l
        rw [truncExp]
      rw [hfun]
      refine (hm (k + 1) hn).sub (ContDiffWithinAt.sum fun j _ => ?_)
      refine (contDiffWithinAt_const.mul (ih (j + 1) (by omega) (by omega))).mul (hm (k - j) (by omega))

/-- `exp ∘ F` inherits nested regularity. -/
theorem NestedSmooth.exp {A B : ℕ} {F : ℝ → ℝ → ℝ} (h0 : (0 : ℝ) ∈ s) (hF : NestedSmooth s A B F) :
    NestedSmooth s A B fun e l => Real.exp (F e l) where
  inner := by
    filter_upwards [hF.inner] with l hl
    exact hl.exp
  outer := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero =>
        simp only [iteratedDeriv_zero]
        have := hF.outer 0 (Nat.zero_le A)
        simp only [iteratedDeriv_zero] at this
        exact this.exp
      | succ k =>
        have hev : (fun l => iteratedDeriv (k + 1) (fun e => Real.exp (F e l)) 0) =ᶠ[𝓝[s] 0]
            fun l => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * iteratedDeriv (i + 1) (fun e => F e l) 0 *
              iteratedDeriv (k - i) (fun e => Real.exp (F e l)) 0 := by
          filter_upwards [hF.inner] with l hl
          have h := iteratedDerivWithin_exp_comp_succ uniqueDiffOn_univ (Set.mem_univ (0 : ℝ))
            (F := fun e => F e l) (n := k) ((hl.of_le (by exact_mod_cast hk)).contDiffWithinAt)
          simpa only [iteratedDerivWithin_univ] using h
        refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (hev.self_of_nhdsWithin h0)
        refine ContDiffWithinAt.sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (contDiffWithinAt_const.mul (hF.outer (i + 1) (by omega))).mul (ih (k - i) (by omega) (by omega))

/-- For `l` near `0` in `s`: `Z(0, l) > 0`, and `Z(e, l) > 0` for `e` near `0` (an iterated neighbourhood; the
hypotheses do not give positivity on a joint neighbourhood of `(0, 0)`). -/
lemma NestedSmooth.eventually_pos {A B : ℕ} {Z : ℝ → ℝ → ℝ} (hZ : NestedSmooth s A B Z) (hpos : 0 < Z 0 0) :
    ∀ᶠ l in 𝓝[s] 0, 0 < Z 0 l ∧ ∀ᶠ e in 𝓝 0, 0 < Z e l := by
  have hc := (hZ.outer 0 (Nat.zero_le A)).continuousWithinAt
  simp only [iteratedDeriv_zero] at hc
  filter_upwards [hc.eventually (lt_mem_nhds hpos), hZ.inner] with l hl hi
  exact ⟨hl, hi.continuousAt.eventually (lt_mem_nhds hl)⟩

/-- `log ∘ Z` inherits nested regularity where `Z(0, 0) > 0`. -/
theorem NestedSmooth.log {A B : ℕ} {Z : ℝ → ℝ → ℝ} (h0 : (0 : ℝ) ∈ s) (hZ : NestedSmooth s A B Z)
    (hpos : 0 < Z 0 0) : NestedSmooth s A B fun e l => Real.log (Z e l) where
  inner := by
    filter_upwards [hZ.inner, hZ.eventually_pos hpos] with l hl hp
    exact hl.log hp.1.ne'
  outer := by
    intro k hk
    have hZ0 := hZ.outer 0 (Nat.zero_le A)
    simp only [iteratedDeriv_zero] at hZ0
    cases k with
    | zero =>
      simp only [iteratedDeriv_zero]
      exact hZ0.log hpos.ne'
    | succ k =>
      have hev : (fun l => iteratedDeriv (k + 1) (fun e => Real.log (Z e l)) 0) =ᶠ[𝓝[s] 0]
          fun l => truncExp (fun j => iteratedDeriv j (fun e => Z e l) 0 / Z 0 l) (k + 1) := by
        filter_upwards [hZ.inner, hZ.eventually_pos hpos] with l hl hp
        have h := iteratedDerivWithin_log_eq_truncExp uniqueDiffOn_univ (Set.mem_univ (0 : ℝ))
          (Z := fun e => Z e l) (n := k) ((hl.of_le (by exact_mod_cast hk)).contDiffWithinAt) hp.1
        simpa only [iteratedDerivWithin_univ] using h
      refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (hev.self_of_nhdsWithin h0)
      refine contDiffWithinAt_truncExp (m := fun j l => iteratedDeriv j (fun e => Z e l) 0 / Z 0 l)
        (N := k + 1) (fun j hj => ?_) (k + 1) le_rfl
      exact (hZ.outer j (hj.trans hk)).div hZ0 hpos.ne'

end TwoVariables

end GaussianBlockSpin
