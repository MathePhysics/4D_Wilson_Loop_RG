/-
`lem:parameter-expansion` of BALABAN_CORE.tex: the expansion in parameters.

For a function `f` of the parameters `s ∈ ℂ^{σ₀}`, holomorphic near the polydisc `|s(Δ)| ≤ e^{κ₁}` and
bounded there by `F`,
  `f(1, …, 1) = Σ_{σ ⊆ σ₀} f_σ`,  `f_σ = ∫_{[0,1]^σ} (Π_{Δ ∈ σ} ∂/∂s(Δ)) f(s_σ) ds`,
  `|f_σ| ≤ F e^{-(κ₁ - 1)#σ}`.

Modelling: the variables are listed by a list `l` without repetitions; `f_σ` is the iterated integral
over `[0,1]^σ` in the order of `l` (outermost first) of the partial derivatives taken in the order of `l`
(the first variable first), evaluated at the point which vanishes in the variables of `l` outside `σ`
(`term l σ f 0`). The holomorphy near the closed polydisc is analyticity at each of its points (which
implies analyticity on a neighbourhood). The proof is the core's: `φ(1) = φ(0) + ∫₀¹ φ'` in each variable
in turn, and Cauchy's estimate for each derivative. The estimate is taken on the circle of radius
`e^{κ₁} - 1` around the point (inside the disc of radius `e^{κ₁}`), which gives `F/(e^{κ₁} - 1)`, at
most the core's `e^{κ₁}(e^{κ₁} - 1)^{-2}F`, and at most `e^{-(κ₁-1)}F` for `κ₁ ≥ 1`.
-/
import CoreLean.CubeGauge

open MeasureTheory Set Metric
open scoped Interval

noncomputable section

namespace CoreLean

namespace ParamExp

variable {ι : Type*} [DecidableEq ι]

/-- The partial derivative `∂g/∂s(a)`. -/
def pd (a : ι) (g : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ := fun s => fderiv ℂ g s (Pi.single a 1)

/-- The derivatives in the variables of `σ`, taken in the order of `l`. -/
def Dσ : List ι → Finset ι → ((ι → ℂ) → ℂ) → ((ι → ℂ) → ℂ)
  | [], _, g => g
  | a :: l, σ, g => if a ∈ σ then Dσ l σ (pd a g) else Dσ l σ g

/-- The iterated integral over `[0,1]^σ` in the order of `l`, the variables of `l` outside `σ` being
set to `0`. -/
def iterInt : List ι → Finset ι → ((ι → ℂ) → ℂ) → (ι → ℂ) → ℂ
  | [], _, F, s => F s
  | a :: l, σ, F, s => if a ∈ σ then ∫ t in (0 : ℝ)..1, iterInt l σ F (Function.update s a (t : ℂ))
      else iterInt l σ F (Function.update s a 0)

/-- The term `f_σ` of the expansion (at the base point `s`, which matters only outside `l`). -/
def term (l : List ι) (σ : Finset ι) (g : (ι → ℂ) → ℂ) (s : ι → ℂ) : ℂ :=
  iterInt l σ (Dσ l σ g) s

/-- The point which equals `1` in the variables of `l` and `s` elsewhere. -/
def setOne (l : List ι) (s : ι → ℂ) : ι → ℂ := fun i => if i ∈ l then 1 else s i

/-- The closed polydisc `|s(i)| ≤ ρ(i)`. -/
def Poly (ρ : ι → ℝ) : Set (ι → ℂ) := {s | ∀ i, ‖s i‖ ≤ ρ i}

/-! ### Bookkeeping -/

lemma Dσ_congr (l : List ι) {σ τ : Finset ι} (h : ∀ b ∈ l, (b ∈ σ ↔ b ∈ τ))
    (g : (ι → ℂ) → ℂ) : Dσ l σ g = Dσ l τ g := by
  induction l generalizing g with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have h' : ∀ c ∈ l, (c ∈ σ ↔ c ∈ τ) := fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [Dσ, hb]
    split_ifs <;> exact ih h' _

lemma iterInt_congr (l : List ι) {σ τ : Finset ι} (h : ∀ b ∈ l, (b ∈ σ ↔ b ∈ τ))
    (F : (ι → ℂ) → ℂ) : iterInt l σ F = iterInt l τ F := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have h' : ∀ c ∈ l, (c ∈ σ ↔ c ∈ τ) := fun c hc => h c (List.mem_cons_of_mem _ hc)
    funext s
    simp only [iterInt, hb, ih h']

lemma term_cons_of_not_mem {a : ι} {l : List ι} {σ : Finset ι} (ha : a ∉ σ)
    (g : (ι → ℂ) → ℂ) (s : ι → ℂ) :
    term (a :: l) σ g s = term l σ g (Function.update s a 0) := by
  simp [term, Dσ, iterInt, ha]

lemma term_cons_insert {a : ι} {l : List ι} (hal : a ∉ l) (σ : Finset ι)
    (g : (ι → ℂ) → ℂ) (s : ι → ℂ) :
    term (a :: l) (insert a σ) g s =
      ∫ t in (0 : ℝ)..1, term l σ (pd a g) (Function.update s a (t : ℂ)) := by
  have hc : ∀ b ∈ l, (b ∈ insert a σ ↔ b ∈ σ) := fun b hb => by
    have : b ≠ a := fun e => hal (e ▸ hb)
    simp [this]
  simp only [term, Dσ, iterInt, Finset.mem_insert_self, if_true]
  rw [Dσ_congr l hc, iterInt_congr l hc]

lemma setOne_cons {a : ι} {l : List ι} (hal : a ∉ l) (s : ι → ℂ) :
    setOne (a :: l) s = Function.update (setOne l s) a 1 := by
  funext i
  by_cases h : i = a
  · subst h; simp [setOne]
  · simp [setOne, h, Function.update_of_ne h]

lemma update_setOne {a : ι} {l : List ι} (hal : a ∉ l) (s : ι → ℂ) (z : ℂ) :
    Function.update (setOne l s) a z = setOne l (Function.update s a z) := by
  funext i
  by_cases h : i = a
  · subst h; simp [setOne, hal]
  · simp [setOne, Function.update_of_ne h]

lemma update_mem_poly {ρ : ι → ℝ} {s : ι → ℂ} (hs : s ∈ Poly ρ) {a : ι} {z : ℂ}
    (hz : ‖z‖ ≤ ρ a) : Function.update s a z ∈ Poly ρ := fun i => by
  by_cases h : i = a
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact hs i

lemma setOne_mem_poly {ρ : ι → ℝ} {l : List ι} (hρ : ∀ i ∈ l, 1 ≤ ρ i) {s : ι → ℂ}
    (hs : s ∈ Poly ρ) : setOne l s ∈ Poly ρ := fun i => by
  by_cases h : i ∈ l
  · simp only [setOne, h, if_true, norm_one]; exact hρ i h
  · simp only [setOne, h, if_false]; exact hs i

lemma isCompact_poly (ρ : ι → ℝ) [Finite ι] : IsCompact (Poly ρ) := by
  have : Poly ρ = Set.pi univ fun i => closedBall (0 : ℂ) (ρ i) := by
    ext s; simp [Poly, mem_closedBall_zero_iff]
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_closedBall _ _

/-! ### Analyticity and the line derivative -/

lemma analyticAt_pd {a : ι} {g : (ι → ℂ) → ℂ} {p : ι → ℂ} [Fintype ι] (h : AnalyticAt ℂ g p) :
    AnalyticAt ℂ (pd a g) p := by
  have h1 : AnalyticAt ℂ (ContinuousLinearMap.apply ℂ ℂ (Pi.single a (1 : ℂ)))
      (fderiv ℂ g p) := ContinuousLinearMap.analyticAt _ _
  exact h1.comp h.fderiv

lemma analyticAt_Dσ [Fintype ι] (l : List ι) (σ : Finset ι) {g : (ι → ℂ) → ℂ} {p : ι → ℂ}
    (h : AnalyticAt ℂ g p) : AnalyticAt ℂ (Dσ l σ g) p := by
  induction l generalizing g with
  | nil => exact h
  | cons b l ih =>
    simp only [Dσ]
    split_ifs
    · exact ih (analyticAt_pd h)
    · exact ih h

lemma hasDerivAt_line [Fintype ι] {g : (ι → ℂ) → ℂ} {s : ι → ℂ} {a : ι} {z : ℂ}
    (h : AnalyticAt ℂ g (Function.update s a z)) :
    HasDerivAt (fun w => g (Function.update s a w)) (pd a g (Function.update s a z)) z :=
  h.differentiableAt.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_update s a z)

/-- `φ(1) = φ(0) + ∫₀¹ φ'(t) dt` along the line of the variable `a`. -/
lemma ftc_line [Fintype ι] {g : (ι → ℂ) → ℂ} {s : ι → ℂ} {a : ι}
    (h : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ g (Function.update s a (t : ℂ))) :
    g (Function.update s a 1) =
      g (Function.update s a 0) + ∫ t in (0 : ℝ)..1, pd a g (Function.update s a (t : ℂ)) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => g (Function.update s a (t : ℂ)))
      (pd a g (Function.update s a (t : ℂ))) t := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact (hasDerivAt_line (h t ht)).comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => pd a g (Function.update s a (t : ℂ))) (uIcc 0 1) :=
    fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      have h1 : ContinuousAt (pd a g) (Function.update s a (t : ℂ)) :=
        (analyticAt_pd (h t ht)).continuousAt
      have h2 : Continuous fun t : ℝ => Function.update s a (t : ℂ) :=
        continuous_const.update a Complex.continuous_ofReal
      exact (ContinuousAt.comp (g := pd a g) (f := fun t : ℝ => Function.update s a (t : ℂ))
        (x := t) h1 h2.continuousAt).continuousWithinAt
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [Complex.ofReal_one, Complex.ofReal_zero] at this
  rw [this]; ring

/-! ### Continuity of the iterated integrals -/

lemma continuousOn_iterInt [Fintype ι] (l : List ι) (σ : Finset ι) {ρ : ι → ℝ}
    (hρ : ∀ i ∈ l, 1 ≤ ρ i) {F : (ι → ℂ) → ℂ} (hF : ContinuousOn F (Poly ρ)) :
    ContinuousOn (iterInt l σ F) (Poly ρ) := by
  induction l with
  | nil => exact hF
  | cons a l ih =>
    have hρa : 1 ≤ ρ a := hρ a List.mem_cons_self
    have ih' := ih fun i hi => hρ i (List.mem_cons_of_mem _ hi)
    by_cases ha : a ∈ σ
    · simp only [iterInt, ha, if_true]
      set G := iterInt l σ F
      obtain ⟨C, hC⟩ := (isCompact_poly ρ).exists_bound_of_continuousOn ih'
      have hmem : ∀ x ∈ Poly ρ, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          Function.update x a (t : ℂ) ∈ Poly ρ := fun x hx t ht => by
        refine update_mem_poly hx ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
      have hline : ∀ x ∈ Poly ρ, ContinuousOn (fun t : ℝ => G (Function.update x a (t : ℂ)))
          (Icc 0 1) := fun x hx =>
        ih'.comp (continuous_const.update a Complex.continuous_ofReal).continuousOn
          (fun t ht => hmem x hx t ht)
      intro x₀ hx₀
      refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
        intervalIntegrable_const ?_
      · filter_upwards [self_mem_nhdsWithin] with x hx
        rw [uIoc_of_le zero_le_one]
        exact ((hline x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [self_mem_nhdsWithin] with x hx
        refine ae_of_all _ fun t ht => hC _ (hmem x hx t ?_)
        rw [uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      · refine ae_of_all _ fun t ht => ?_
        rw [uIoc_of_le zero_le_one] at ht
        have hm := hmem x₀ hx₀ t (Ioc_subset_Icc_self ht)
        exact ContinuousWithinAt.comp (f := fun x : ι → ℂ => Function.update x a (t : ℂ))
          (ih' _ hm) (continuous_id.update a continuous_const).continuousWithinAt
          (fun x hx => hmem x hx t (Ioc_subset_Icc_self ht))
    · simp only [iterInt, ha, if_false]
      exact ih'.comp (continuous_id.update a continuous_const).continuousOn
        (fun x hx => update_mem_poly hx (by simp; linarith))

/-! ### The expansion -/

/-- `eq:parameter-expansion`, first part: `f(1, …, 1) = Σ_{σ ⊆ σ₀} f_σ`, in the form
`g(s with the variables of l set to 1) = Σ_{σ ⊆ l} term l σ g s`. -/
theorem expansion [Fintype ι] (l : List ι) (hl : l.Nodup) {ρ : ι → ℝ} (hρ : ∀ i ∈ l, 1 ≤ ρ i)
    (g : (ι → ℂ) → ℂ) (hg : ∀ p ∈ Poly ρ, AnalyticAt ℂ g p) (s : ι → ℂ) (hs : s ∈ Poly ρ) :
    g (setOne l s) = ∑ σ ∈ l.toFinset.powerset, term l σ g s := by
  induction l generalizing g s with
  | nil =>
    have : setOne ([] : List ι) s = s := by funext i; simp [setOne]
    simp [this, term, Dσ, iterInt]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hal, hl⟩ := hl
    have hρa : 1 ≤ ρ a := hρ a List.mem_cons_self
    have hρl : ∀ i ∈ l, 1 ≤ ρ i := fun i hi => hρ i (List.mem_cons_of_mem _ hi)
    have half : a ∉ l.toFinset := by simpa using hal
    have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Function.update s a (t : ℂ) ∈ Poly ρ :=
      fun t ht => by
        refine update_mem_poly hs ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
    -- the fundamental theorem in the variable `a`
    rw [setOne_cons hal, ftc_line (g := g) (s := setOne l s) (a := a) (fun t ht => by
      rw [update_setOne hal]; exact hg _ (setOne_mem_poly hρl (hmem t ht)))]
    rw [update_setOne hal, ih hl hρl g hg _ (update_mem_poly hs (by simp; linarith))]
    -- the integrand by the induction hypothesis
    have hint : ∫ t in (0 : ℝ)..1, pd a g (Function.update (setOne l s) a (t : ℂ)) =
        ∫ t in (0 : ℝ)..1, ∑ σ ∈ l.toFinset.powerset,
          term l σ (pd a g) (Function.update s a (t : ℂ)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      show pd a g (Function.update (setOne l s) a (t : ℂ)) = _
      rw [update_setOne hal]
      exact ih hl hρl (pd a g) (fun p hp => analyticAt_pd (hg p hp)) _ (hmem t ht)
    rw [hint, intervalIntegral.integral_finsetSum]
    · rw [List.toFinset_cons, Finset.sum_powerset_insert half]
      congr 1
      · refine Finset.sum_congr rfl fun σ hσ => ?_
        have : a ∉ σ := fun h => half (Finset.mem_powerset.mp hσ h)
        rw [term_cons_of_not_mem this]
      · refine Finset.sum_congr rfl fun σ _ => ?_
        rw [term_cons_insert hal]
    · intro σ _
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      have hc : ContinuousOn (term l σ (pd a g)) (Poly ρ) :=
        continuousOn_iterInt l σ hρl fun p hp =>
          (analyticAt_Dσ l σ (analyticAt_pd (hg p hp))).continuousAt.continuousWithinAt
      exact hc.comp (continuous_const.update a Complex.continuous_ofReal).continuousOn
        (fun t ht => hmem t ht)

/-! ### The bound -/

/-- Cauchy's estimate on the circle of radius `R - 1` around a point with `|p(a)| ≤ 1`. -/
lemma norm_pd_le [Fintype ι] {R F : ℝ} (hR : 1 < R) {g : (ι → ℂ) → ℂ} {a : ι} {p : ι → ℂ}
    (hp : ‖p a‖ ≤ 1) (hg : ∀ z : ℂ, ‖z‖ ≤ R → AnalyticAt ℂ g (Function.update p a z))
    (hF : ∀ z : ℂ, ‖z‖ ≤ R → ‖g (Function.update p a z)‖ ≤ F) :
    ‖pd a g p‖ ≤ F / (R - 1) := by
  set ψ : ℂ → ℂ := fun w => g (Function.update p a w)
  have hR1 : 0 < R - 1 := by linarith
  have hin : ∀ z ∈ closedBall (p a) (R - 1), ‖z‖ ≤ R := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - p a) + p a‖ := by ring_nf
      _ ≤ ‖z - p a‖ + ‖p a‖ := norm_add_le _ _
      _ ≤ R := by linarith
  have hd : DiffContOnCl ℂ ψ (ball (p a) (R - 1)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR1.ne']
    exact fun z hz => (hasDerivAt_line (hg z (hin z hz))).differentiableAt.differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR1 hd fun z hz =>
    hF z (hin z (sphere_subset_closedBall hz))
  have e : deriv ψ (p a) = pd a g p := by
    have := (hasDerivAt_line (s := p) (a := a) (z := p a)
      (hg _ (hp.trans hR.le))).deriv
    rw [Function.update_eq_self] at this
    exact this
  rwa [e] at h

/-- `F/(e^{κ₁} - 1) ≤ e^{-(κ₁ - 1)}F` for `κ₁ ≥ 1` and `F ≥ 0`. -/
lemma div_exp_sub_one_le {κ₁ F : ℝ} (hκ : 1 ≤ κ₁) (hF : 0 ≤ F) :
    F / (Real.exp κ₁ - 1) ≤ F * Real.exp (-(κ₁ - 1)) := by
  have he : Real.exp 1 ≤ Real.exp κ₁ := Real.exp_le_exp.mpr hκ
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR1 : 0 < Real.exp κ₁ - 1 := by linarith
  have hsplit : Real.exp (-(κ₁ - 1)) = Real.exp 1 / Real.exp κ₁ := by
    rw [show -(κ₁ - 1) = 1 - κ₁ by ring, Real.exp_sub]
  rw [hsplit, div_le_iff₀ hR1]
  have hpos : 0 < Real.exp κ₁ := Real.exp_pos _
  rw [show F * (Real.exp 1 / Real.exp κ₁) * (Real.exp κ₁ - 1) =
    F * (Real.exp 1 * (Real.exp κ₁ - 1) / Real.exp κ₁) by field_simp]
  have key : 1 ≤ Real.exp 1 * (Real.exp κ₁ - 1) / Real.exp κ₁ := by
    rw [le_div_iff₀ hpos]; nlinarith
  nlinarith

/-- `eq:parameter-expansion`, the bound: `|f_σ| ≤ F e^{-(κ₁ - 1)#σ}`. -/
theorem norm_term_le [Fintype ι] (l : List ι) (hl : l.Nodup) {κ₁ : ℝ} (hκ : 1 ≤ κ₁)
    {ρ : ι → ℝ} (hρ : ∀ i ∈ l, ρ i = Real.exp κ₁) (g : (ι → ℂ) → ℂ)
    (hg : ∀ p ∈ Poly ρ, AnalyticAt ℂ g p) {F : ℝ} (hF : ∀ p ∈ Poly ρ, ‖g p‖ ≤ F)
    (σ : Finset ι) (hσ : σ ⊆ l.toFinset) (s : ι → ℂ) (hs : s ∈ Poly ρ) :
    ‖term l σ g s‖ ≤ F * Real.exp (-(κ₁ - 1) * σ.card) := by
  induction l generalizing ρ g F σ s with
  | nil =>
    have : σ = ∅ := Finset.subset_empty.mp (by simpa using hσ)
    subst this
    simpa [term, Dσ, iterInt] using hF s hs
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hal, hl⟩ := hl
    have hρa : ρ a = Real.exp κ₁ := hρ a List.mem_cons_self
    have he1 : 1 < Real.exp κ₁ := by
      have := Real.add_one_le_exp κ₁; linarith
    have hρl : ∀ i ∈ l, ρ i = Real.exp κ₁ := fun i hi => hρ i (List.mem_cons_of_mem _ hi)
    by_cases ha : a ∈ σ
    · -- the variable `a` is integrated
      have hσ' : σ.erase a ⊆ l.toFinset := fun i hi => by
        have hne := Finset.ne_of_mem_erase hi
        have := hσ (Finset.mem_of_mem_erase hi)
        simp only [List.toFinset_cons, Finset.mem_insert] at this
        exact this.resolve_left hne
      rw [← Finset.insert_erase ha, term_cons_insert hal]
      set ρ' := Function.update ρ a 1
      have hsub : Poly ρ' ⊆ Poly ρ := fun p hp i => by
        by_cases h : i = a
        · subst h; have := hp i; simp only [ρ', Function.update_self] at this; linarith
        · have := hp i; simp only [ρ', Function.update_of_ne h] at this; exact this
      have hρ' : ∀ i ∈ l, ρ' i = Real.exp κ₁ := fun i hi => by
        have : i ≠ a := fun e => hal (e ▸ hi)
        simp only [ρ', Function.update_of_ne this]; exact hρl i hi
      have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF s hs)
      -- Cauchy's estimate for `∂g/∂s(a)` on the smaller polydisc
      have hF' : ∀ p ∈ Poly ρ', ‖pd a g p‖ ≤ F * Real.exp (-(κ₁ - 1)) := fun p hp => by
        have hpa : ‖p a‖ ≤ 1 := by have := hp a; simpa [ρ'] using this
        have hpρ : p ∈ Poly ρ := hsub hp
        have hz : ∀ z : ℂ, ‖z‖ ≤ Real.exp κ₁ → Function.update p a z ∈ Poly ρ :=
          fun z hz => update_mem_poly hpρ (by rw [hρa]; exact hz)
        exact (norm_pd_le he1 hpa (fun z hz' => hg _ (hz z hz'))
          (fun z hz' => hF _ (hz z hz'))).trans (div_exp_sub_one_le hκ hF0)
      have ih' := ih hl hρ' (pd a g) (fun p hp => analyticAt_pd (hg p (hsub hp))) hF'
        (σ.erase a) hσ'
      have hbd : ∀ t ∈ Ι (0 : ℝ) 1, ‖term l (σ.erase a) (pd a g) (Function.update s a (t : ℂ))‖ ≤
          F * Real.exp (-(κ₁ - 1)) * Real.exp (-(κ₁ - 1) * (σ.erase a).card) := fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        refine ih' _ fun i => ?_
        by_cases h : i = a
        · subst h
          simp only [Function.update_self, ρ', Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg ht.1.le]; exact ht.2
        · simp only [Function.update_of_ne h, ρ']; exact hs i
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans (le_of_eq ?_)
      have hcard : ((σ.erase a).card : ℝ) = σ.card - 1 := by
        have := Finset.card_erase_add_one ha
        rw [← this]; push_cast; ring
      rw [Finset.insert_erase ha, hcard, sub_zero, abs_one, mul_one, mul_assoc, ← Real.exp_add]
      congr 2; ring
    · -- the variable `a` is set to `0`
      have hσ' : σ ⊆ l.toFinset := fun i hi => by
        have := hσ hi
        simp only [List.toFinset_cons, Finset.mem_insert] at this
        exact this.resolve_left fun e => ha (e ▸ hi)
      rw [term_cons_of_not_mem ha]
      exact ih hl hρl g hg hF σ hσ' _ (update_mem_poly hs (by simp; linarith))

/-! ### The vanishing of `f_σ` -/

/-- `h` does not depend on the variable `Δ`. -/
def Inv (Δ : ι) (h : (ι → ℂ) → ℂ) : Prop := ∀ q (w : ℂ), h (q + w • Pi.single Δ 1) = h q

lemma inv_pd [Fintype ι] {Δ : ι} {h : (ι → ℂ) → ℂ} (hh : Inv Δ h) (b : ι) : Inv Δ (pd b h) := by
  intro q w
  have e : (fun x => h (x + w • Pi.single Δ (1 : ℂ))) = h := funext fun x => hh x w
  have := fderiv_comp_add_right (𝕜 := ℂ) (f := h) (x := q) (w • Pi.single Δ (1 : ℂ))
  rw [e] at this
  simp only [pd]
  rw [← this]

lemma pd_eq_zero_of_inv [Fintype ι] {Δ : ι} {h : (ι → ℂ) → ℂ} (hh : Inv Δ h) : pd Δ h = 0 := by
  funext q
  simp only [pd, Pi.zero_apply]
  by_cases hd : DifferentiableAt ℂ h q
  · set e : ι → ℂ := Pi.single Δ 1
    have hγ : HasDerivAt (fun w : ℂ => q + w • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add q
    have h1 : HasDerivAt (fun w : ℂ => h (q + w • e)) (fderiv ℂ h q e) 0 := by
      have hd' : HasFDerivAt h (fderiv ℂ h q) (q + (0 : ℂ) • e) := by
        rw [zero_smul, add_zero]; exact hd.hasFDerivAt
      exact hd'.comp_hasDerivAt (0 : ℂ) hγ
    have h2 : HasDerivAt (fun w : ℂ => h (q + w • e)) 0 0 := by
      have : (fun w : ℂ => h (q + w • e)) = fun _ => h q := funext fun w => hh q w
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · exact DFunLike.congr_fun (fderiv_zero_of_not_differentiableAt hd) _

lemma pd_zero [Fintype ι] (b : ι) : pd b (fun _ : ι → ℂ => (0 : ℂ)) = 0 := by
  funext q; simp [pd]

lemma Dσ_zero [Fintype ι] (l : List ι) (σ : Finset ι) : Dσ l σ (fun _ : ι → ℂ => (0 : ℂ)) = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [Dσ]
    split_ifs
    · rw [pd_zero]; exact ih
    · exact ih

lemma Dσ_eq_zero_of_inv [Fintype ι] {Δ : ι} (l : List ι) {σ : Finset ι} (hΔσ : Δ ∈ σ)
    (hΔl : Δ ∈ l) {h : (ι → ℂ) → ℂ} (hh : Inv Δ h) : Dσ l σ h = 0 := by
  induction l generalizing h with
  | nil => simp at hΔl
  | cons b l ih =>
    simp only [Dσ]
    by_cases hb : b = Δ
    · subst hb
      rw [if_pos hΔσ, pd_eq_zero_of_inv hh]
      exact Dσ_zero l σ
    · have hΔl' : Δ ∈ l := by
        rcases List.mem_cons.mp hΔl with e | e
        · exact absurd e.symm hb
        · exact e
      split_ifs
      · exact ih hΔl' (inv_pd hh b)
      · exact ih hΔl' hh

/-- The derivatives in the directions of `σ` at a point of the subspace `V_σ` of the points vanishing
outside `σ` depend only on the function on `V_σ`. -/
lemma pd_congr_on [Fintype ι] {σ : Finset ι} {O : Set (ι → ℂ)} (hO : IsOpen O)
    {h₁ h₂ : (ι → ℂ) → ℂ} (h₁a : ∀ p ∈ O, AnalyticAt ℂ h₁ p) (h₂a : ∀ p ∈ O, AnalyticAt ℂ h₂ p)
    (heq : ∀ p ∈ O, (∀ i ∉ σ, p i = 0) → h₁ p = h₂ p) {b : ι} (hb : b ∈ σ) :
    ∀ p ∈ O, (∀ i ∉ σ, p i = 0) → pd b h₁ p = pd b h₂ p := by
  intro p hp hV
  set e : ι → ℂ := Pi.single b 1
  have hγ : HasDerivAt (fun w : ℂ => p + w • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add p
  have hγ' : HasDerivAt (fun w : ℂ => p + w • e) e 0 := hγ
  have line : ∀ {h : (ι → ℂ) → ℂ}, AnalyticAt ℂ h p →
      HasDerivAt (fun w : ℂ => h (p + w • e)) (pd b h p) 0 := fun {h} ha => by
    have hd' : HasFDerivAt h (fderiv ℂ h p) (p + (0 : ℂ) • e) := by
      rw [zero_smul, add_zero]; exact ha.differentiableAt.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℂ) hγ'
  have hev : (fun w : ℂ => h₁ (p + w • e)) =ᶠ[nhds 0] fun w => h₂ (p + w • e) := by
    have hc : Continuous fun w : ℂ => p + w • e := continuous_const.add (continuous_id.smul continuous_const)
    have hmem : (fun w : ℂ => p + w • e) ⁻¹' O ∈ nhds (0 : ℂ) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hp)
    filter_upwards [hmem] with w hw
    refine heq _ hw fun i hi => ?_
    have hib : i ≠ b := fun h => hi (h ▸ hb)
    simp [e, hV i hi, Pi.single_apply, hib]
  exact (line (h₁a p hp)).unique ((line (h₂a p hp)).congr_of_eventuallyEq hev)

lemma Dσ_congr_on [Fintype ι] (l : List ι) {σ : Finset ι} {O : Set (ι → ℂ)} (hO : IsOpen O)
    {h₁ h₂ : (ι → ℂ) → ℂ} (h₁a : ∀ p ∈ O, AnalyticAt ℂ h₁ p) (h₂a : ∀ p ∈ O, AnalyticAt ℂ h₂ p)
    (heq : ∀ p ∈ O, (∀ i ∉ σ, p i = 0) → h₁ p = h₂ p) :
    ∀ p ∈ O, (∀ i ∉ σ, p i = 0) → Dσ l σ h₁ p = Dσ l σ h₂ p := by
  induction l generalizing h₁ h₂ with
  | nil => exact heq
  | cons b l ih =>
    simp only [Dσ]
    split_ifs with hb
    · exact ih (fun p hp => analyticAt_pd (h₁a p hp)) (fun p hp => analyticAt_pd (h₂a p hp))
        (pd_congr_on hO h₁a h₂a heq hb)
    · exact ih h₁a h₂a heq

lemma iterInt_eq_zero (l : List ι) (σ : Finset ι) {F : (ι → ℂ) → ℂ}
    (hF : ∀ q : ι → ℂ, (∀ i, ‖q i‖ ≤ 1) → (∀ i ∉ σ, q i = 0) → F q = 0) (s : ι → ℂ)
    (hs1 : ∀ i, ‖s i‖ ≤ 1) (hs0 : ∀ i ∉ σ, s i = 0) : iterInt l σ F s = 0 := by
  induction l generalizing s with
  | nil => exact hF s hs1 hs0
  | cons a l ih =>
    by_cases ha : a ∈ σ
    · simp only [iterInt, ha, if_true]
      rw [show (0 : ℂ) = ∫ t in (0 : ℝ)..1, (0 : ℂ) by simp]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      refine ih _ (fun i => ?_) (fun i hi => ?_)
      · by_cases h : i = a
        · subst h; simp only [Function.update_self, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg ht.1]; exact ht.2
        · rw [Function.update_of_ne h]; exact hs1 i
      · have : i ≠ a := fun h => hi (h ▸ ha)
        rw [Function.update_of_ne this]; exact hs0 i hi
    · simp only [iterInt, ha, if_false]
      refine ih _ (fun i => ?_) (fun i hi => ?_)
      · by_cases h : i = a
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hs1 i
      · by_cases h : i = a
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hs0 i hi

/-- `lem:parameter-expansion`, the last statement: if `f(s_σ)` does not depend on `s(Δ)` for some
`Δ ∈ σ`, then `f_σ = 0`. -/
theorem term_eq_zero [Fintype ι] (l : List ι) {σ : Finset ι} (hσ : σ ⊆ l.toFinset) {R : ℝ}
    (hR : 1 < R) (f : (ι → ℂ) → ℂ) (hf : ∀ p ∈ Poly (fun _ => R), AnalyticAt ℂ f p) {Δ : ι}
    (hΔ : Δ ∈ σ)
    (hind : ∀ p ∈ Poly (fun _ => R), (∀ i ∉ σ, p i = 0) → f p = f (Function.update p Δ 0)) :
    term l σ f 0 = 0 := by
  set O : Set (ι → ℂ) := Set.pi univ fun _ => ball (0 : ℂ) R
  have hO : IsOpen O := isOpen_set_pi finite_univ fun _ _ => isOpen_ball
  have hOP : O ⊆ Poly (fun _ => R) := fun p hp i => by
    have := hp i (mem_univ _); rw [mem_ball_zero_iff] at this; exact this.le
  -- `f' = f(· with s(Δ) = 0)`, analytic and independent of `s(Δ)`
  set L : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun i => if i = Δ then 0 else ContinuousLinearMap.proj i
  have hL : ∀ q, L q = Function.update q Δ 0 := fun q => by
    funext i
    by_cases h : i = Δ
    · subst h; simp [L]
    · simp [L, h, Function.update_of_ne h]
  set f' : (ι → ℂ) → ℂ := fun q => f (Function.update q Δ 0)
  have hf'a : ∀ p ∈ O, AnalyticAt ℂ f' p := fun p hp => by
    have hm : Function.update p Δ 0 ∈ Poly (fun _ => R) := fun i => by
      by_cases h : i = Δ
      · subst h; simp; linarith
      · rw [Function.update_of_ne h]; exact hOP hp i
    have : f' = f ∘ L := funext fun q => by simp [f', hL]
    rw [this]
    exact (hf _ (by rw [hL]; exact hm)).comp (L.analyticAt p)
  have hinv : Inv Δ f' := fun q w => by
    simp only [f']
    congr 1
    funext i
    by_cases h : i = Δ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_apply, h]
  have hzero := Dσ_eq_zero_of_inv l hΔ (by simpa using hσ hΔ) hinv
  have hcongr := Dσ_congr_on l hO (fun p hp => hf p (hOP hp)) hf'a
    (fun p hp hV => hind p (hOP hp) hV)
  refine iterInt_eq_zero l σ (fun q hq1 hq0 => ?_) 0 (fun i => by simp) (fun i _ => rfl)
  have hqO : q ∈ O := fun i _ => by rw [mem_ball_zero_iff]; exact lt_of_le_of_lt (hq1 i) hR
  rw [hcongr q hqO hq0, hzero]; rfl

/-- `lem:parameter-expansion`, `eq:parameter-expansion`: for `f` holomorphic near the polydisc
`|s(Δ)| ≤ e^{κ₁}` and bounded there by `F`, with `κ₁ ≥ 1`, and the variables listed by `l`,
`f(1, …, 1) = Σ_{σ ⊆ σ₀} f_σ` and `|f_σ| ≤ F e^{-(κ₁ - 1)#σ}`, where `f_σ = term l σ f 0`. -/
theorem parameter_expansion [Fintype ι] (l : List ι) (hl : l.Nodup) (hlu : ∀ i, i ∈ l)
    {κ₁ : ℝ} (hκ : 1 ≤ κ₁) (f : (ι → ℂ) → ℂ)
    (hf : ∀ p ∈ Poly (fun _ => Real.exp κ₁), AnalyticAt ℂ f p) {F : ℝ}
    (hF : ∀ p ∈ Poly (fun _ => Real.exp κ₁), ‖f p‖ ≤ F) :
    f (fun _ => 1) = ∑ σ ∈ (Finset.univ : Finset ι).powerset, term l σ f 0 ∧
      ∀ σ : Finset ι, ‖term l σ f 0‖ ≤ F * Real.exp (-(κ₁ - 1) * σ.card) := by
  have he : 1 ≤ Real.exp κ₁ := Real.one_le_exp (by linarith)
  have h0 : (0 : ι → ℂ) ∈ Poly (fun _ => Real.exp κ₁) := fun i => by simp; linarith
  have hfin : l.toFinset = Finset.univ := by ext i; simp [hlu i]
  have hset : setOne l 0 = fun _ => (1 : ℂ) := by funext i; simp [setOne, hlu i]
  refine ⟨?_, fun σ => ?_⟩
  · have := expansion l hl (fun _ _ => he) f hf 0 h0
    rwa [hset, hfin] at this
  · exact norm_term_le l hl hκ (fun _ _ => rfl) f hf hF σ (by rw [hfin]; exact Finset.subset_univ _)
      0 h0

end ParamExp

end CoreLean
