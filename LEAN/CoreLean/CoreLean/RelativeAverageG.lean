/-
`prop:relative-average`(i) of BALABAN_CORE.tex (`7299a1db4f90`), the values in `G`: for `A'` and `A` with values in
`𝔤` the transports, the site factors at `c±`, the averages, and `𝓜_𝐔(A)(c)` lie in `G`.

* `log_mem_lie`: an element of `G` near `id` is `e^{iY}` with `Y = (1/i) Log W ∈ 𝔤` (`lem:chart`(ii), (iii)).
* `trans_mem`, `siteFactor_mem`, `avgM_mem`, `relAvg_mem`: for a configuration with values in `G` whose quotients of
  the paths `𝐆(y, x)`, ratios of transports, and loops lie within a radius `r` of `id` (depending on `G` only),
  the objects lie in `G` (`lem:group-mean` for elements of `G`).
-/
import CoreLean.RelativeAverageReduce
import CoreLean.GroupMeanII

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

lemma exp_mem_of_lie (G : GaugeGroup N) {A : Mat} (hA : A ∈ G.lie) : expU (Complex.I • A) ∈ G.carrier := by
  simpa using hA.2 1

/-- **An element of `G` near `id` has its logarithm in `i𝔤`.** -/
theorem log_mem_lie (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ W : GLN, W ∈ G.carrier → ∀ ρ : ℝ, ‖(W : Mat) - 1‖ ≤ ρ → ρ ≤ r →
      (1 / Complex.I) • LogM (W : Mat) ∈ G.lie ∧ ‖(1 / Complex.I) • LogM (W : Mat)‖ ≤ Real.pi / 2 * ρ ∧
      LogM (W : Mat) = Complex.I • ((1 / Complex.I) • LogM (W : Mat)) := by
  obtain ⟨re, hre, hel⟩ := elements_of_G G hG
  refine ⟨min re (1 / 4), lt_min hre (by norm_num), min_le_right _ _, fun W hW ρ hρ hρr => ?_⟩
  have hρ1 : ρ ≤ re := hρr.trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := hρr.trans (min_le_right _ _)
  obtain ⟨Y, hY, hWY, hYn⟩ := hel W 1 hW G.carrier.one_mem ρ (by simpa using hρ) hρ1
  rw [_root_.inv_one, mul_one] at hWY
  have hpi := Real.pi_lt_d2
  have hlog := Real.log_two_gt_d9
  have hYs : ‖Complex.I • Y‖ < Real.log 2 := by
    rw [norm_I_smul']
    have : Real.pi / 2 * ρ ≤ Real.pi / 2 * (1 / 4) :=
      mul_le_mul_of_nonneg_left hρ4 (by positivity)
    linarith
  have hL : LogM (W : Mat) = Complex.I • Y := by rw [hWY, expU_val, LogM_exp hYs]
  have hY' : (1 / Complex.I) • LogM (W : Mat) = Y := by
    rw [hL, smul_smul, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  refine ⟨hY' ▸ hY, hY' ▸ hYn, ?_⟩
  rw [smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]

lemma sum_mem_lie (G : GaugeGroup N) (hG : IsClosed G.mats) {ι : Type*} (s : Finset ι) (f : ι → Mat)
    (hf : ∀ i ∈ s, f i ∈ G.lie) : ∑ i ∈ s, f i ∈ G.lie :=
  Finset.sum_induction _ (· ∈ G.lie) (fun _ _ ha hb => GaugeGroup.add_mem_lie hG ha hb) G.zero_mem_lie hf

lemma inv_natCast_eq (m : ℕ) : ((m : ℂ))⁻¹ = (((m : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl

/-- **The radius of `G`-membership**: for configurations with values in `G` whose relevant matrices lie within `r`
of `id`, the transports, the site factors, the averages, and the relative average lie in `G`. -/
theorem G_radius (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧
      (∀ {m : ℕ} [NeZero m] {V : Config N m} {y : Site m} {h : ℕ} {x : Pts h}, IsGField G V →
        (∀ i, ‖((quotG V y h x i : GLN) : Mat) - 1‖ ≤ r) → trans V y h x ∈ G.carrier) ∧
      (∀ {W : GLN}, W ∈ G.carrier → ‖(W : Mat) - 1‖ ≤ r →
        (1 / Complex.I) • LogM (W : Mat) ∈ G.lie ∧
          LogM (W : Mat) = Complex.I • ((1 / Complex.I) • LogM (W : Mat))) := by
  obtain ⟨rl, hrl, hrl4, hlog⟩ := log_mem_lie G hG
  obtain ⟨cm, hcm, hgm⟩ := group_mean_lie G hG
  have hpi := Real.pi_gt_three
  set r := min rl (min (1 / (256 * Real.pi)) (cm / Real.pi)) with hr
  have hr0 : 0 < r := lt_min hrl (lt_min (by positivity) (by positivity))
  have hrl' : r ≤ rl := min_le_left _ _
  have hr1 : r ≤ 1 / (256 * Real.pi) := (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ cm / Real.pi := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr0, fun {m} _ {V y h x} hV hq => ?_, fun {W} hW hWr => ?_⟩
  · set M := Real.pi / 2 * r
    have hM512 : 512 * M ≤ 1 := by
      have : Real.pi * r ≤ Real.pi * (1 / (256 * Real.pi)) := mul_le_mul_of_nonneg_left hr1 (by positivity)
      have e : Real.pi * (1 / (256 * Real.pi)) = 1 / 256 := by field_simp
      simp only [M]; nlinarith
    have hMc : 2 * M ≤ cm := by
      have : Real.pi * r ≤ Real.pi * (cm / Real.pi) := mul_le_mul_of_nonneg_left hr2 (by positivity)
      have e : Real.pi * (cm / Real.pi) = cm := by field_simp
      simp only [M]; nlinarith
    have hqG : ∀ i, quotG V y h x i ∈ G.carrier := fun i =>
      G.carrier.mul_mem (hV.hol_mem _) (G.carrier.inv_mem (hV.hol_mem _))
    have hY : ∀ i, expsG V y h x i ∈ G.lie ∧ ‖expsG V y h x i‖ ≤ M := fun i =>
      ⟨(hlog _ (hqG i) r (hq i) hrl').1, (hlog _ (hqG i) r (hq i) hrl').2.1⟩
    have hn : 0 < nG h x := card_ords_pos _
    obtain ⟨Z, hZ, hZn, hsum, hmem⟩ := hgm hn (expsG V y h x) M (fun i => (hY i).2) hM512 hMc
      (fun i => (hY i).1)
    have hY512 : ∀ i, ‖expsG V y h x i‖ ≤ 1 / 512 := fun i => by linarith [(hY i).2]
    have hZ256 : ‖Z‖ ≤ 1 / 256 := by linarith
    have hZm : Z = meanV (expsG V y h x) := mean_unique hn hY512 (holG V y h x (firstG h x)) hZ256 (by
      have e : ∀ i, LogM (((expU (Complex.I • expsG V y h x i) * holG V y h x (firstG h x)) *
          (expU (Complex.I • Z) * holG V y h x (firstG h x))⁻¹ : GLN) : Mat) =
          Complex.I • psi (expsG V y h x i) (-Z) := fun i => by rw [quotient, log_quot]
      simp only [e, ← Finset.smul_sum, hsum, smul_zero])
    show mean (expsG V y h x) (holG V y h x (firstG h x)) ∈ G.carrier
    rw [mean, ← hZm]
    exact hmem _ (hV.hol_mem _)
  · obtain ⟨h1, -, h3⟩ := hlog W hW r hWr hrl'
    exact ⟨h1, h3⟩


/-- The radius of `G`-membership with all four objects: for configurations `V` and `𝐔_B = moveC V B` with values in
`G` whose quotients, transport ratios, and loops are within `r` of `id`, the site factors, the averages, and `𝓜`
lie in `G`. -/
theorem G_radius_all (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {m : ℕ} [NeZero m] {V : Config N m} {B : Fin 4 → Site m → Mat} {y : Site m} {μ : Fin 4}
      {h : ℕ},
      IsGField G V → IsGField G (moveC V B) →
      (∀ x i, ‖((quotG V y h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x i, ‖((quotG (moveC V B) y h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x i, ‖((quotG V (cPlus y μ h) h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x i, ‖((quotG (moveC V B) (cPlus y μ h) h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x, ‖((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x, ‖((trans (moveC V B) (cPlus y μ h) h x * (trans V (cPlus y μ h) h x)⁻¹ : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x Γ Γ', ‖(((V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h)
        x Γ Γ')) : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x Γ Γ', ‖((((moveC V B).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
        (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ r) →
      siteFactor V B y h ∈ G.carrier ∧ siteFactor V B (cPlus y μ h) h ∈ G.carrier ∧
        avgM V y μ h ∈ G.carrier ∧ avgM (moveC V B) y μ h ∈ G.carrier ∧ relAvg V B y μ h ∈ G.carrier := by
  obtain ⟨r, hr, htr, hlg⟩ := G_radius (N := N) G hG
  refine ⟨r, hr, fun {m} _ {V B y μ h} hV hVB hq hqA hq' hqA' ht ht' hl hlA => ?_⟩
  -- the site factors
  have hsite : ∀ y' : Site m, (∀ x i, ‖((quotG V y' h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x i, ‖((quotG (moveC V B) y' h x i : GLN) : Mat) - 1‖ ≤ r) →
      (∀ x, ‖((trans (moveC V B) y' h x * (trans V y' h x)⁻¹ : GLN) : Mat) - 1‖ ≤ r) →
      siteFactor V B y' h ∈ G.carrier := fun y' h1 h2 h3 => by
    have hqG : ∀ x : Pts h, trans (moveC V B) y' h x * (trans V y' h x)⁻¹ ∈ G.carrier := fun x =>
      G.carrier.mul_mem (htr hVB (h2 x)) (G.carrier.inv_mem (htr hV (h1 x)))
    have hL : ∀ x : Pts h, LogM ((trans (moveC V B) y' h x * (trans V y' h x)⁻¹ : GLN) : Mat) =
        Complex.I • ((1 / Complex.I) • LogM ((trans (moveC V B) y' h x * (trans V y' h x)⁻¹ : GLN) : Mat)) :=
      fun x => (hlg (hqG x) (h3 x)).2
    have hsum : (((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) • ∑ x : Pts h,
        (1 / Complex.I) • LogM ((trans (moveC V B) y' h x * (trans V y' h x)⁻¹ : GLN) : Mat) ∈ G.lie :=
      G.smul_mem_lie (sum_mem_lie G hG Finset.univ _ fun x _ => (hlg (hqG x) (h3 x)).1) _
    have hc : (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ = (((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have e : siteFactor V B y' h = expU (Complex.I • ((((((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) • ∑ x : Pts h,
        (1 / Complex.I) • LogM ((trans (moveC V B) y' h x * (trans V y' h x)⁻¹ : GLN) : Mat))) := by
      rw [siteFactor]
      congr 1
      rw [Finset.sum_congr rfl fun x _ => hL x, ← Finset.smul_sum, hc, smul_comm]
    rw [e]; exact exp_mem_of_lie G hsum
  -- the averages
  have havg : ∀ V' : Config N m, IsGField G V' →
      (∀ x Γ Γ', ‖(((V'.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
        (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ r) → avgM V' y μ h ∈ G.carrier := fun V' hV' hl' => by
    have hβ : betaLog V' y μ (2 * h + 1) (offP h) (ordG h) ∈ G.lie := by
      refine sum_mem_lie G hG _ _ fun x _ => sum_mem_lie G hG _ _ fun Γ _ => sum_mem_lie G hG _ _ fun Γ' _ => ?_
      have hw : Average.wt (fun x : Pts h => Ords (offP h x)) (fun x : Pts h => Ords (offP h x)) x =
          (((Fintype.card (Pts h) : ℝ) * Fintype.card (Ords (offP h x)) * Fintype.card (Ords (offP h x)))⁻¹ : ℝ) := by
        simp [Average.wt]
      rw [hw]
      exact G.smul_mem_lie (hlg (hV'.hol_mem _) (hl' x Γ Γ')).1 _
    show expU (Complex.I • betaLog V' y μ (2 * h + 1) (offP h) (ordG h)) *
      V'.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) ∈ G.carrier
    exact G.carrier.mul_mem (exp_mem_of_lie G hβ) (hV'.hol_mem _)
  have s0 := hsite y hq hqA ht
  have s1 := hsite (cPlus y μ h) hq' hqA' ht'
  have a0 := havg V hV hl
  have aA := havg (moveC V B) hVB hlA
  refine ⟨s0, s1, a0, aA, ?_⟩
  rw [relAvg]
  exact G.carrier.mul_mem (G.carrier.mul_mem (G.carrier.mul_mem (G.carrier.inv_mem s0) aA) s1)
    (G.carrier.inv_mem a0)


/-! ### The closeness to `id` near the trivial configuration, uniformly -/

/-- The matrices of the bond `(y, y + Le_μ)` within `ρ` of `id`, at the pair `(X, B)`. -/
structure CondG (ρ : ℝ) (y : Site n) (μ : Fin 4) (h : ℕ) (X B : Fin 4 → Site n → Mat) : Prop where
  q0 : ∀ x i, ‖((quotG (UX (N := N) X) y h x i : GLN) : Mat) - 1‖ ≤ ρ
  qA0 : ∀ x i, ‖((quotG (moveC (UX (N := N) X) B) y h x i : GLN) : Mat) - 1‖ ≤ ρ
  q1 : ∀ x i, ‖((quotG (UX (N := N) X) (cPlus y μ h) h x i : GLN) : Mat) - 1‖ ≤ ρ
  qA1 : ∀ x i, ‖((quotG (moveC (UX (N := N) X) B) (cPlus y μ h) h x i : GLN) : Mat) - 1‖ ≤ ρ
  t0 : ∀ x, ‖((trans (moveC (UX (N := N) X) B) y h x * (trans (UX (N := N) X) y h x)⁻¹ : GLN) : Mat) - 1‖ ≤ ρ
  t1 : ∀ x, ‖((trans (moveC (UX (N := N) X) B) (cPlus y μ h) h x *
    (trans (UX (N := N) X) (cPlus y μ h) h x)⁻¹ : GLN) : Mat) - 1‖ ≤ ρ
  l0 : ∀ x Γ Γ', ‖((((UX (N := N) X).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
    (offP h) (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ ρ
  lA : ∀ x Γ Γ', ‖((((moveC (UX (N := N) X) B).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ
    (2 * h + 1) (offP h) (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ ρ

/-- A continuous function of the pair with the value `id` at `0` is eventually within `ρ` of `id`. -/
lemma eventually_near_one {ρ : ℝ} (hρ : 0 < ρ) {F : PairSp N n → Mat} (hF : ContinuousAt F 0) (h0 : F 0 = 1) :
    ∀ᶠ p in 𝓝 (0 : PairSp N n), ‖F p - 1‖ ≤ ρ := by
  have hc : ContinuousAt (fun p => ‖F p - 1‖) 0 := (hF.sub continuousAt_const).norm
  have h00 : ‖F 0 - 1‖ < ρ := by rw [h0, sub_self, norm_zero]; exact hρ
  filter_upwards [hc.eventually_lt continuousAt_const h00] with p hp using hp.le

theorem eventually_condG {ρ : ℝ} (hρ : 0 < ρ) (y : Site n) (μ : Fin 4) (h : ℕ) :
    ∀ᶠ p in 𝓝 (0 : PairSp N n), CondG (N := N) ρ y μ h p.1 p.2 := by
  have hU0 : UX (N := N) (n := n) (0 : PairSp N n).1 = oneC := UX_zero
  have hA0 : moveC (UX (N := N) (n := n) (0 : PairSp N n).1) (0 : PairSp N n).2 = oneC := by
    simp only [Prod.fst_zero, Prod.snd_zero, UX_zero, moveC_zero]
  have hholU : ∀ γ : List (Bond n), ContinuousAt (fun p : PairSp N n => (((UX (N := N) p.1).hol γ : GLN) : Mat)) 0 :=
    fun γ => (hol_differentiableAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) γ).continuousAt
  have hholA : ∀ γ : List (Bond n), ContinuousAt
      (fun p : PairSp N n => (((moveC (UX (N := N) p.1) p.2).hol γ : GLN) : Mat)) 0 :=
    fun γ => (hol_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV 0) γ).continuousAt
  have hholUi : ∀ γ : List (Bond n), ContinuousAt
      (fun p : PairSp N n => ((((UX (N := N) p.1).hol γ)⁻¹ : GLN) : Mat)) 0 :=
    fun γ => (inv_differentiableAt (hol_differentiableAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) γ)).continuousAt
  have hholAi : ∀ γ : List (Bond n), ContinuousAt
      (fun p : PairSp N n => ((((moveC (UX (N := N) p.1) p.2).hol γ)⁻¹ : GLN) : Mat)) 0 :=
    fun γ => (inv_differentiableAt (hol_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2)
      (UXB_hV 0) γ)).continuousAt
  have hquotU : ∀ y' x i, ∀ᶠ p in 𝓝 (0 : PairSp N n),
      ‖((quotG (UX (N := N) p.1) y' h x i : GLN) : Mat) - 1‖ ≤ ρ := fun y' x i => by
    refine eventually_near_one hρ ?_ ?_
    · simp only [quotG, holG, Units.val_mul]; exact (hholU _).mul (hholUi _)
    · simp only [quotG, holG, hU0, hol_oneC, mul_one, Units.val_one, _root_.inv_one]
  have hquotA : ∀ y' x i, ∀ᶠ p in 𝓝 (0 : PairSp N n),
      ‖((quotG (moveC (UX (N := N) p.1) p.2) y' h x i : GLN) : Mat) - 1‖ ≤ ρ := fun y' x i => by
    refine eventually_near_one hρ ?_ ?_
    · simp only [quotG, holG, Units.val_mul]; exact (hholA _).mul (hholAi _)
    · simp only [quotG, holG, hA0, hol_oneC, mul_one, Units.val_one, _root_.inv_one]
  have hloopU : ∀ x Γ Γ', ∀ᶠ p in 𝓝 (0 : PairSp N n), ‖((((UX (N := N) p.1).hol (lpath (ι := Pts h)
      (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ ρ :=
    fun x Γ Γ' => eventually_near_one hρ (hholU _) (by simp only [hU0, hol_oneC, Units.val_one])
  have hloopA : ∀ x Γ Γ', ∀ᶠ p in 𝓝 (0 : PairSp N n), ‖((((moveC (UX (N := N) p.1) p.2).hol (lpath (ι := Pts h)
      (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ')) : GLN) : Mat) - 1‖ ≤ ρ :=
    fun x Γ Γ' => eventually_near_one hρ (hholA _) (by simp only [hA0, hol_oneC, Units.val_one])
  have htr : ∀ y' (x : Pts h), ∀ᶠ p in 𝓝 (0 : PairSp N n),
      ‖((trans (moveC (UX (N := N) p.1) p.2) y' h x * (trans (UX (N := N) p.1) y' h x)⁻¹ : GLN) : Mat) - 1‖ ≤ ρ :=
    fun y' x => by
      have g0 : GoodAt (UX (N := N) (0 : PairSp N n).1) y' h := by rw [hU0]; exact goodAt_oneC y' h
      have gA0 : GoodAt (moveC (UX (N := N) (0 : PairSp N n).1) (0 : PairSp N n).2) y' h := by
        rw [hA0]; exact goodAt_oneC y' h
      have h1 : DifferentiableAt ℂ (fun p : PairSp N n => ((trans (moveC (UX (N := N) p.1) p.2) y' h x : GLN) : Mat))
          0 := trans_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV 0) y' h x
            (gA0.1 x) ((gA0.2 x).trans (by norm_num))
      have h2 : DifferentiableAt ℂ (fun p : PairSp N n => ((trans (UX (N := N) p.1) y' h x : GLN) : Mat)) 0 :=
        trans_differentiableAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) y' h x
          (g0.1 x) ((g0.2 x).trans (by norm_num))
      refine eventually_near_one hρ ?_ ?_
      · simp only [Units.val_mul]; exact (h1.mul (inv_differentiableAt h2)).continuousAt
      · show ((trans (moveC (UX (N := N) (0 : PairSp N n).1) (0 : PairSp N n).2) y' h x *
          (trans (UX (N := N) (0 : PairSp N n).1) y' h x)⁻¹ : GLN) : Mat) = 1
        rw [hA0, hU0, trans_oneC]; simp
  filter_upwards [eventually_all.2 fun x => eventually_all.2 fun i => hquotU y x i,
    eventually_all.2 fun x => eventually_all.2 fun i => hquotA y x i,
    eventually_all.2 fun x => eventually_all.2 fun i => hquotU (cPlus y μ h) x i,
    eventually_all.2 fun x => eventually_all.2 fun i => hquotA (cPlus y μ h) x i,
    eventually_all.2 fun x => htr y x, eventually_all.2 fun x => htr (cPlus y μ h) x,
    eventually_all.2 fun x => eventually_all.2 fun Γ => eventually_all.2 fun Γ' => hloopU x Γ Γ',
    eventually_all.2 fun x => eventually_all.2 fun Γ => eventually_all.2 fun Γ' => hloopA x Γ Γ']
    with p a b c d e f g k
  exact ⟨a, b, c, d, e, f, g, k⟩

/-- **The closeness transfers from the reference torus.** -/
theorem condG_of_ref {ρ : ℝ} {y : Site n} {μ : Fin 4} {h : ℕ} {X B : Fin 4 → Site n → Mat}
    (hc : CondG (N := N) ρ (0 : Site (4 * h + 2)) μ h (refForm h X y) (refForm h B y)) :
    CondG (N := N) ρ y μ h X B := by
  have hA := agree_ref h (UX (N := N) X) B y
  rw [refConfig_UX] at hA
  have e0 : ∀ (m : ℕ) [NeZero m] (z : Site m), ofs z 0 = z := fun m _ z => ofs_zero z
  have hq : ∀ {w : Fin 4 → ℤ}, EndOK h w → ∀ x i,
      quotG (UX (N := N) X) (ofs y w) h x i = quotG (UX (N := N) (refForm h X y)) (ofs 0 w) h x i ∧
      quotG (moveC (UX (N := N) X) B) (ofs y w) h x i =
        quotG (moveC (UX (N := N) (refForm h X y)) (refForm h B y)) (ofs 0 w) h x i := fun hw x i => by
    simp only [quotG, (holG_agree hA hw x _).1, (holG_agree hA hw x _).2, and_self]
  have hl : ∀ x Γ Γ', ((UX (N := N) X).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ')) = (UX (N := N) (refForm h X y)).hol (lpath (ι := Pts h)
      (P := fun x => Ords (offP h x)) 0 μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') ∧
      ((moveC (UX (N := N) X) B).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ')) = (moveC (UX (N := N) (refForm h X y)) (refForm h B y)).hol (lpath (ι := Pts h)
      (P := fun x => Ords (offP h x)) 0 μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') := fun x Γ Γ' => by
    rw [lpath_map, lpath_map, hol_map, hol_map, hol_map, hol_map]
    exact holI_agree hA _ (ilpath_inR μ h x Γ Γ')
  have q0 := hq (endOK_zero h)
  simp only [e0] at q0
  have qL := hq (endOK_plus h μ)
  have t0 := fun x => trans_agree hA (endOK_zero h) x
  simp only [e0] at t0
  have tL := fun x => trans_agree hA (endOK_plus h μ) x
  refine ⟨fun x i => ?_, fun x i => ?_, fun x i => ?_, fun x i => ?_, fun x => ?_, fun x => ?_,
    fun x Γ Γ' => ?_, fun x Γ Γ' => ?_⟩
  · rw [(q0 x i).1]; exact hc.q0 x i
  · rw [(q0 x i).2]; exact hc.qA0 x i
  · have := hc.q1 x i; simp only [cPlus] at this ⊢; rw [(qL x i).1]; exact this
  · have := hc.qA1 x i; simp only [cPlus] at this ⊢; rw [(qL x i).2]; exact this
  · rw [(t0 x).1, (t0 x).2]; exact hc.t0 x
  · have := hc.t1 x; simp only [cPlus] at this ⊢; rw [(tL x).1, (tL x).2]; exact this
  · rw [(hl x Γ Γ').1]; exact hc.l0 x Γ Γ'
  · rw [(hl x Γ Γ').2]; exact hc.lA x Γ Γ'

/-- **One polydisc of closeness for all tori.** -/
theorem uniform_condG {ρ : ℝ} (hρ : 0 < ρ) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      ‖X‖ < c → ‖B‖ < c → CondG (N := N) ρ y μ h X B := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_condG (N := N) (n := 4 * h + 2) hρ 0 μ h)
  refine ⟨ε, hε, fun {n} _ y X B hX hB => condG_of_ref (hball (y := (refForm h X y, refForm h B y)) ?_)⟩
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt ((norm_refForm_le h y X).trans_lt hX) ((norm_refForm_le h y B).trans_lt hB)

/-- **`prop:relative-average`(i), the values in `G`, for `𝐔_X`**: for `X` and `B` with values in `𝔤` in a polydisc
of a radius depending on `L` and `G` only, the site factors at `c±`, the averages, and `𝓜_{𝐔_X}(B)(c)` lie in `G`. -/
theorem relAvg_mem_UX (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      (∀ ν z, X ν z ∈ G.lie) → (∀ ν z, B ν z ∈ G.lie) → ‖X‖ < c → ‖B‖ < c →
      siteFactor (UX (N := N) X) B y h ∈ G.carrier ∧ siteFactor (UX (N := N) X) B (cPlus y μ h) h ∈ G.carrier ∧
        relAvg (UX (N := N) X) B y μ h ∈ G.carrier := by
  obtain ⟨r, hr, hall⟩ := G_radius_all (N := N) G hG
  obtain ⟨c, hc, hcond⟩ := uniform_condG (N := N) hr h μ
  refine ⟨c, hc, fun {n} _ y X B hX hB hXn hBn => ?_⟩
  have hcg := hcond y X B hXn hBn
  have hV : IsGField G (UX (N := N) X) := fun ν z => by
    show expU (Complex.I • X ν z) * (oneC (N := N) ν z) ∈ G.carrier
    simp only [oneC, mul_one]
    exact exp_mem_of_lie G (hX ν z)
  have hVB : IsGField G (moveC (UX (N := N) X) B) := fun ν z =>
    G.carrier.mul_mem (exp_mem_of_lie G (hB ν z)) (hV ν z)
  obtain ⟨s0, s1, -, -, hr⟩ := hall hV hVB hcg.q0 hcg.qA0 hcg.q1 hcg.qA1 hcg.t0 hcg.t1 hcg.l0 hcg.lA
  exact ⟨s0, s1, hr⟩


/-- **`prop:relative-average`(i), the values in `G`, for the core's `𝐔`**: for a field `U` with values in `G`, `A'` and
`A` with values in `𝔤`, `|U(∂p) - id| ≤ α₀ ≤ c`, `‖aA'‖ ≤ α₁ ≤ c` and `‖aA‖_{∞,box} < c`, the relative average
`𝓜_𝐔(A)(c)` lies in `G`; `c` depends on `L` and `G` only. -/
theorem relative_average_G (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, A' ρ z ∈ G.lie) → (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat, (∀ ρ z, B ρ z ∈ G.lie) → ‖restrictF B (InBoxB y h μ)‖ < c →
          relAvg (moveC U A') B y μ h ∈ G.carrier := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨cG, hcG, hmem⟩ := relAvg_mem_UX (N := N) G hG h μ
  obtain ⟨rl, hrl, -, hlog⟩ := log_mem_lie G hG
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (cG / (2 * K))) (min (1 / (8 * K)) (rl / (2 * K))) with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ cG / (2 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ 1 / (8 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ rl / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨c, hc0, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA'l hA' B hBl hB
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hUg := hU.gauge
  obtain ⟨X, hXc, -, hag, hl, hz⟩ := reduce_box_supp hUg hn y μ hα₀ hα₁ hα₀c hα₁c hc3 hplq A' hA'
  have hKc : ∀ t : ℝ, c ≤ t / (2 * K) → K * c ≤ t / 2 := fun t ht => by
    calc K * c ≤ K * (t / (2 * K)) := mul_le_mul_of_nonneg_left ht hKpos.le
      _ = t / 2 := by field_simp
  have hX8 : ‖X‖ ≤ 1 / 8 := hXc.trans (by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc3 hKpos.le
      _ = 1 / 8 := by field_simp)
  set u := uG U y h
  have huG : ∀ z, u z ∈ G.carrier := fun z => hU.hol_mem _
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hUg _
  -- `X` has values in `𝔤`
  have hXl : ∀ ρ z, X ρ z ∈ G.lie := by
    intro ρ z
    by_cases hb : BoxBond y h μ ρ z
    · rw [hl ρ z hb]
      have hWG : ((moveC U A').gauge u) ρ z ∈ G.carrier := by
        simp only [Config.gauge, moveC]
        exact G.carrier.mul_mem (G.carrier.mul_mem (huG z) (G.carrier.mul_mem (exp_mem_of_lie G (hA'l ρ z))
          (hU ρ z))) (G.carrier.inv_mem (huG _))
      have hWn : ‖((((moveC U A').gauge u) ρ z : GLN) : Mat) - 1‖ ≤ rl := by
        rw [hag ρ z hb]
        show ‖((expU (Complex.I • X ρ z) * oneC (N := N) ρ z : GLN) : Mat) - 1‖ ≤ rl
        simp only [oneC, mul_one]
        have hXz : ‖Complex.I • X ρ z‖ ≤ ‖X‖ := by
          rw [norm_I_smul']; exact (norm_le_pi_norm (X ρ) z).trans (norm_le_pi_norm X ρ)
        have h1 := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • X ρ z)).trans
          (exp_sub_one_le_two_mul (norm_nonneg _) hXz (hX8.trans (by norm_num)))
        have hKcl := hKc rl hc4
        show ‖exp (Complex.I • X ρ z) - 1‖ ≤ rl
        linarith
      exact (hlog _ hWG rl hWn le_rfl).1
    · rw [hz ρ z hb]; exact G.zero_mem_lie
  -- the restricted form transported by `u`
  set B' := AdF u (restrictF B (InBoxB y h μ))
  have hB'l : ∀ ρ z, B' ρ z ∈ G.lie := fun ρ z => by
    simp only [B', AdF, restrictF]
    split_ifs
    · exact G.Ad_mem_lie (huG z) (hBl ρ z)
    · simp only [Ad, mul_zero, zero_mul]; exact G.zero_mem_lie
  have hB'n : ‖B'‖ = ‖restrictF B (InBoxB y h μ)‖ := norm_AdF_unitary hu _
  have hXci : ‖X‖ < ci := lt_of_le_of_lt hXc (by have := hKc ci hc1; linarith)
  have hXcG : ‖X‖ < cG := lt_of_le_of_lt hXc (by have := hKc cG hc2; linarith)
  have hBci : ‖B'‖ < ci := by
    rw [hB'n]; exact lt_of_lt_of_le hB (hc1.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith))
  have hBcG : ‖B'‖ < cG := by
    rw [hB'n]; exact lt_of_lt_of_le hB (hc2.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith))
  have e1 : relAvg (moveC U A') B y μ h = relAvg (moveC U A') (restrictF B (InBoxB y h μ)) y μ h :=
    relAvg_local hn2 fun ν z h1 h2 => ⟨rfl, (restrictF_box_apply B ⟨h1, h2⟩).symm⟩
  rw [e1, relAvg_reduce hUg hn hag _ (hpol y X B' hXci hBci)]
  exact (hmem y X B' hXl hB'l hXcG hBcG).2.2


/-! ### `(1/i) log 𝓜 ∈ 𝔤^c` -/

/-- `𝓜_{𝐔_X}(B)(c)` is within `ρ` of `id` on a polydisc whose radius does not depend on the torus. -/
theorem uniform_relAvg_near {ρ : ℝ} (hρ : 0 < ρ) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      ‖X‖ < c → ‖B‖ < c → ‖((relAvg (UX (N := N) X) B y μ h : GLN) : Mat) - 1‖ ≤ ρ := by
  have hc0 : Cond (N := N) (0 : Site (4 * h + 2)) μ h (0 : PairSp N (4 * h + 2)) :=
    (eventually_cond (N := N) (n := 4 * h + 2) 0 μ h).self_of_nhds
  have hev := eventually_near_one hρ (relAvg_pair_differentiableAt hc0).continuousAt (by
    simp only [Prod.fst_zero, Prod.snd_zero, relAvg_zero, Units.val_one])
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun {n} _ y X B hX hB => ?_⟩
  rw [relAvg_reference h (UX (N := N) X) B y μ, refConfig_UX]
  refine hball (y := ((refForm h X y, refForm h B y) : PairSp N (4 * h + 2))) ?_
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt ((norm_refForm_le h y X).trans_lt hX) ((norm_refForm_le h y B).trans_lt hB)

/-- **For data in `𝔤`, `(1/i) log 𝓜_{𝐔_X}(B)(c) ∈ 𝔤`.** -/
theorem relLog_mem_lie_UX (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      (∀ ν z, X ν z ∈ G.lie) → (∀ ν z, B ν z ∈ G.lie) → ‖X‖ < c → ‖B‖ < c →
      relLog (UX (N := N) X) B y μ h ∈ G.lie := by
  obtain ⟨cG, hcG, hmem⟩ := relAvg_mem_UX (N := N) G hG h μ
  obtain ⟨rl, hrl, -, hlog⟩ := log_mem_lie G hG
  obtain ⟨cR, hcR, hnear⟩ := uniform_relAvg_near (N := N) hrl h μ
  refine ⟨min cG cR, lt_min hcG hcR, fun {n} _ y X B hX hB hXn hBn => ?_⟩
  have hm := (hmem y X B hX hB (lt_of_lt_of_le hXn (min_le_left _ _)) (lt_of_lt_of_le hBn (min_le_left _ _))).2.2
  have hn := hnear y X B (lt_of_lt_of_le hXn (min_le_right _ _)) (lt_of_lt_of_le hBn (min_le_right _ _))
  exact (hlog _ hm rl hn le_rfl).1

/-- `π` as a continuous linear map. -/
def piL {G : GaugeGroup N} (hG : G.LieInput) : Mat →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := piProj hG, map_add' := proj_add hG, map_smul' := proj_smul hG }

lemma piProj_self {G : GaugeGroup N} (hG : G.LieInput) {X : Mat} (hX : X ∈ G.lieC) : piProj hG X = X :=
  proj_eq hG hX fun Z _ => by simp [ntr]

/-- The real and imaginary parts of an element of `𝔤^c`: `X = A + iB` with `A, B ∈ 𝔤`, `‖A‖, ‖B‖ ≤ ‖X‖`. -/
lemma lieC_parts {G : GaugeGroup N} {X : Mat} (hX : X ∈ G.lieC) :
    ∃ A ∈ G.lie, ∃ B ∈ G.lie, X = A + Complex.I • B ∧ ‖A‖ ≤ ‖X‖ ∧ ‖B‖ ≤ ‖X‖ := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  have hH : (A + Complex.I • B)ᴴ = A - Complex.I • B := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA.1, hB.1, Complex.star_def, Complex.conj_I,
      neg_smul, sub_eq_add_neg]
  have hn : ‖(A + Complex.I • B)ᴴ‖ = ‖A + Complex.I • B‖ := opNorm_conjTranspose _
  have eA : A = (1 / 2 : ℂ) • ((A + Complex.I • B) + (A + Complex.I • B)ᴴ) := by
    rw [hH]; module
  have eB : B = (1 / (2 * Complex.I) : ℂ) • ((A + Complex.I • B) - (A + Complex.I • B)ᴴ) := by
    rw [hH, add_sub_sub_cancel, ← two_smul ℂ (Complex.I • B), smul_smul, smul_smul]
    field_simp
    rw [one_smul]
  refine ⟨A, hA, B, hB, rfl, ?_, ?_⟩
  · conv_lhs => rw [eA]
    rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans ?_
    rw [hn]; norm_num; linarith
  · conv_lhs => rw [eB]
    rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)).trans ?_
    rw [hn, norm_div, norm_mul, Complex.norm_I]; norm_num; linarith

/-- **`(1/i) log 𝓜_{𝐔_X}(B)(c) ∈ 𝔤^c` for `X`, `B` with values in `𝔤^c`** (`prop:relative-average`(vi)): the function
`(1 - π)(1/i) log 𝓜` is holomorphic and vanishes at the points with values in `𝔤`; on the complex line through
the real part in the direction of the imaginary part it vanishes on a real segment, hence at `t = i`. -/
theorem relLog_mem_lieC_UX (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      (∀ ν z, X ν z ∈ G.lieC) → (∀ ν z, B ν z ∈ G.lieC) → ‖X‖ < c → ‖B‖ < c →
      relLog (UX (N := N) X) B y μ h ∈ G.lieC := by
  have hLI := GaugeGroup.lieInput_of_isClosed hG
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨cr, hcr, hreal⟩ := relLog_mem_lie_UX (N := N) G hG h μ
  refine ⟨min (ci / 3) (cr / 2), lt_min (by positivity) (by positivity), fun {n} _ y X B hX hB hXn hBn => ?_⟩
  have hc1 : min (ci / 3) (cr / 2) ≤ ci / 3 := min_le_left _ _
  have hc2 : min (ci / 3) (cr / 2) ≤ cr / 2 := min_le_right _ _
  -- the real and imaginary parts
  choose Xa hXa Xb hXb hXe hXan hXbn using fun ν z => lieC_parts (hX ν z)
  choose Ba hBa Bb hBb hBe hBan hBbn using fun ν z => lieC_parts (hB ν z)
  have nrm : ∀ (F : Fin 4 → Site n → Mat) (H : Fin 4 → Site n → Mat), (∀ ν z, ‖F ν z‖ ≤ ‖H ν z‖) → ‖F‖ ≤ ‖H‖ :=
    fun F H hFH => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ν => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      fun z => (hFH ν z).trans ((norm_le_pi_norm (H ν) z).trans (norm_le_pi_norm H ν))
  have hXa' : ‖(fun ν z => Xa ν z : Fin 4 → Site n → Mat)‖ ≤ ‖X‖ := nrm _ _ hXan
  have hXb' : ‖(fun ν z => Xb ν z : Fin 4 → Site n → Mat)‖ ≤ ‖X‖ := nrm _ _ hXbn
  have hBa' : ‖(fun ν z => Ba ν z : Fin 4 → Site n → Mat)‖ ≤ ‖B‖ := nrm _ _ hBan
  have hBb' : ‖(fun ν z => Bb ν z : Fin 4 → Site n → Mat)‖ ≤ ‖B‖ := nrm _ _ hBbn
  set XA : Fin 4 → Site n → Mat := fun ν z => Xa ν z
  set XB : Fin 4 → Site n → Mat := fun ν z => Xb ν z
  set BA : Fin 4 → Site n → Mat := fun ν z => Ba ν z
  set BB : Fin 4 → Site n → Mat := fun ν z => Bb ν z
  -- the line `t ↦ (XA + tXB, BA + tBB)` and the function `(1 - π)(1/i) log 𝓜` on it
  set p : ℂ → PairSp N n := fun t => (XA + t • XB, BA + t • BB)
  set F : PairSp N n → Mat := fun q => relLog (UX (N := N) q.1) q.2 y μ h - piL hLI (relLog (UX (N := N) q.1) q.2 y μ h)
  set g : ℂ → Mat := F ∘ p
  have hp_norm : ∀ t : ℂ, ‖t‖ < 2 → ‖(p t).1‖ < ci ∧ ‖(p t).2‖ < ci := fun t ht => by
    have f1 : ‖t • XB‖ ≤ ‖t‖ * ‖X‖ := by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hXb' (norm_nonneg _)
    have f2 : ‖t • BB‖ ≤ ‖t‖ * ‖B‖ := by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hBb' (norm_nonneg _)
    have e1 : ‖(p t).1‖ ≤ ‖X‖ + ‖t‖ * ‖X‖ := by
      show ‖XA + t • XB‖ ≤ _
      exact (norm_add_le _ _).trans (add_le_add hXa' f1)
    have e2 : ‖(p t).2‖ ≤ ‖B‖ + ‖t‖ * ‖B‖ := by
      show ‖BA + t • BB‖ ≤ _
      exact (norm_add_le _ _).trans (add_le_add hBa' f2)
    have hX3 : ‖X‖ < ci / 3 := lt_of_lt_of_le hXn hc1
    have hB3 : ‖B‖ < ci / 3 := lt_of_lt_of_le hBn hc1
    constructor <;> nlinarith [norm_nonneg X, norm_nonneg B, norm_nonneg t]
  have hgd : DifferentiableOn ℂ g (ball 0 2) := fun t ht => by
    rw [mem_ball_zero_iff] at ht
    obtain ⟨h1, h2⟩ := hp_norm t ht
    have hc := hpol y (p t).1 (p t).2 h1 h2
    have hF : DifferentiableAt ℂ F (p t) := by
      have := relLog_pair_differentiableAt (p₀ := p t) hc
      exact this.sub ((piL hLI).differentiableAt.comp _ this)
    have hpd : DifferentiableAt ℂ p t := by
      refine DifferentiableAt.prodMk ?_ ?_
      · exact (differentiableAt_const XA).add (differentiableAt_id.smul_const XB)
      · exact (differentiableAt_const BA).add (differentiableAt_id.smul_const BB)
    exact (hF.comp t hpd).differentiableWithinAt
  -- `g` vanishes at the real points of the segment
  have hg_real : ∀ s : ℝ, |s| < 1 → g s = 0 := fun s hs => by
    have hmemX : ∀ ν z, (XA + (s : ℂ) • XB) ν z ∈ G.lie := fun ν z =>
      GaugeGroup.add_mem_lie hG (hXa ν z) (G.smul_mem_lie (hXb ν z) s)
    have hmemB : ∀ ν z, (BA + (s : ℂ) • BB) ν z ∈ G.lie := fun ν z =>
      GaugeGroup.add_mem_lie hG (hBa ν z) (G.smul_mem_lie (hBb ν z) s)
    have hsn : ‖(s : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hs.le
    have hXr : ‖XA + (s : ℂ) • XB‖ < cr := by
      have f1 : ‖(s : ℂ) • XB‖ ≤ 1 * ‖X‖ := by
        rw [norm_smul]; exact mul_le_mul hsn hXb' (norm_nonneg _) zero_le_one
      have := (norm_add_le XA ((s : ℂ) • XB)).trans (add_le_add hXa' f1)
      have : ‖X‖ < cr / 2 := lt_of_lt_of_le hXn hc2
      linarith
    have hBr : ‖BA + (s : ℂ) • BB‖ < cr := by
      have f1 : ‖(s : ℂ) • BB‖ ≤ 1 * ‖B‖ := by
        rw [norm_smul]; exact mul_le_mul hsn hBb' (norm_nonneg _) zero_le_one
      have := (norm_add_le BA ((s : ℂ) • BB)).trans (add_le_add hBa' f1)
      have : ‖B‖ < cr / 2 := lt_of_lt_of_le hBn hc2
      linarith
    have hl := hreal y _ _ hmemX hmemB hXr hBr
    show F (p s) = 0
    simp only [F, p]
    rw [show piL hLI (relLog (UX (N := N) (XA + (s : ℂ) • XB)) (BA + (s : ℂ) • BB) y μ h) =
      relLog (UX (N := N) (XA + (s : ℂ) • XB)) (BA + (s : ℂ) • BB) y μ h from
      piProj_self hLI (GaugeGroup.lie_subset_lieC hl), sub_self]
  -- the identity theorem on the disc
  have han := hgd.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    set s : ℝ := min (ε / 2) (1 / 2)
    have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
    refine ⟨(s : ℂ), hεU ⟨?_, ?_⟩, hg_real s ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]; exact hs0.ne'
    · rw [abs_of_pos hs0]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball 0 2).isPreconnected
    (mem_ball_self (by norm_num)) hfreq
  have hI : g Complex.I = 0 := hzero (by rw [mem_ball_zero_iff, Complex.norm_I]; norm_num)
  have hpI : p Complex.I = (X, B) := by
    simp only [p, XA, XB, BA, BB]
    ext ν z <;> simp [hXe, hBe]
  have hF0 : F (X, B) = 0 := by rw [← hpI]; exact hI
  simp only [F] at hF0
  have : relLog (UX (N := N) X) B y μ h = piL hLI (relLog (UX (N := N) X) B y μ h) := sub_eq_zero.1 hF0
  rw [this]
  exact proj_mem hLI _


/-- `Ad` by an element of `G` preserves `𝔤^c`. -/
lemma Ad_mem_lieC_of_mem (G : GaugeGroup N) {W : GLN} (hW : W ∈ G.carrier) {X : Mat} (hX : X ∈ G.lieC) :
    Ad W X ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  exact ⟨Ad W A, G.Ad_mem_lie hW hA, Ad W B, G.Ad_mem_lie hW hB, by rw [Ad_add, Ad_smul]⟩

/-- **`prop:relative-average`(vi), `(1/i) log 𝓜_𝐔(A)(c) ∈ 𝔤^c` for the core's `𝐔`**: for `U` with values in `G`, `A'` and
`A` with values in `𝔤^c`, `|U(∂p) - id| ≤ α₀ ≤ c`, `‖aA'‖ ≤ α₁ ≤ c` and `‖aA‖_{∞,box} < c`. -/
theorem relative_average_lieC (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, A' ρ z ∈ G.lieC) → (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat, (∀ ρ z, B ρ z ∈ G.lieC) → ‖restrictF B (InBoxB y h μ)‖ < c →
          relLog (moveC U A') B y μ h ∈ G.lieC := by
  have hLI := GaugeGroup.lieInput_of_isClosed hG
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨cL, hcL, hmemL⟩ := relLog_mem_lieC_UX (N := N) G hG h μ
  obtain ⟨rl, hrl, -, hlog⟩ := log_mem_lie G hG
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (cL / (2 * K))) (min (1 / (40 * K)) (rl / K)) with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ cL / (2 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ 1 / (40 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ rl / K := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨c, hc0, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA'l hA' B hBl hB
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hUg := hU.gauge
  have hc8 : c ≤ 1 / (8 * K) := hc3.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  obtain ⟨X, hXc, -, hag, hl, hz⟩ := reduce_box_supp hUg hn y μ hα₀ hα₁ hα₀c hα₁c hc8 hplq A' hA'
  have hKc : ∀ t : ℝ, c ≤ t / (2 * K) → K * c ≤ t / 2 := fun t ht => by
    calc K * c ≤ K * (t / (2 * K)) := mul_le_mul_of_nonneg_left ht hKpos.le
      _ = t / 2 := by field_simp
  set u := uG U y h
  have huG : ∀ z, u z ∈ G.carrier := fun z => hU.hol_mem _
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hUg _
  -- the bound of `U^u` on the box
  set β := Real.sqrt N * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hP : PlaqBound U (boxR y (loD h) (hiD h μ μ)) β := fun μ' ν' z _ hz =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hplq μ' ν' z hz) (Real.sqrt_nonneg _))
  have hδ : ((8 * h + 2 : ℕ) : ℝ) * β ≤ K / 2 * c := by
    have e2 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ K / 2 * α₀ := by
      rw [hβ]; simp only [K, redK]
      nlinarith [Real.sqrt_nonneg (N : ℝ), (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((8 * h + 2 : ℕ) : ℝ))]
    exact e2.trans (mul_le_mul_of_nonneg_left hα₀c (by linarith))
  have hGb : ∀ ρ z, BoxBond y h μ ρ z → ‖(((U.gauge u) ρ z : GLN) : Mat) - 1‖ ≤ K / 2 * c := by
    intro ρ z hb
    obtain ⟨hm, hm'⟩ := box_bond hn hb
    have := gauge_bound U hUg hn y μ μ hβ0 hP (rep y h z) ρ hm hm'
    rw [StraightExtension.ofs_rep] at this
    exact this.trans hδ
  have hUgG : ∀ ρ z, (U.gauge u) ρ z ∈ G.carrier := fun ρ z => by
    simp only [Config.gauge]
    exact G.carrier.mul_mem (G.carrier.mul_mem (huG z) (hU ρ z)) (G.carrier.inv_mem (huG _))
  -- `X` has values in `𝔤^c`
  have hXl : ∀ ρ z, X ρ z ∈ G.lieC := by
    intro ρ z
    by_cases hb : BoxBond y h μ ρ z
    · rw [hl ρ z hb, gauged_val]
      have hKr : K / 2 * c ≤ rl := by
        have := mul_le_mul_of_nonneg_left hc4 (by linarith : (0 : ℝ) ≤ K / 2)
        have e : K / 2 * (rl / K) = rl / 2 := by field_simp
        linarith
      obtain ⟨hB0, hBn, hBe⟩ := hlog _ (hUgG ρ z) (K / 2 * c) (hGb ρ z hb) hKr
      set B0 := (1 / Complex.I) • LogM ((((U.gauge u) ρ z : GLN) : Mat))
      have hGe : (((U.gauge u) ρ z : GLN) : Mat) = exp (Complex.I • B0) := by
        have hsm : ‖Complex.I • B0‖ < Real.log 2 := by
          rw [norm_I_smul']
          have hpi := Real.pi_lt_d2
          have hl2 := Real.log_two_gt_d9
          have : K / 2 * c ≤ 1 / 80 := by
            have := mul_le_mul_of_nonneg_left hc3 (by linarith : (0 : ℝ) ≤ K / 2)
            have e : K / 2 * (1 / (40 * K)) = 1 / 80 := by field_simp; ring
            linarith
          have h1 : Real.pi / 2 * (K / 2 * c) ≤ Real.pi / 2 * (1 / 80) :=
            mul_le_mul_of_nonneg_left this (by positivity)
          linarith
        have := exp_LogM (W := (((U.gauge u) ρ z : GLN) : Mat)) (by
          have := hGb ρ z hb
          have : K / 2 * c ≤ 1 / 80 := by
            have := mul_le_mul_of_nonneg_left hc3 (by linarith : (0 : ℝ) ≤ K / 2)
            have e : K / 2 * (1 / (40 * K)) = 1 / 80 := by field_simp; ring
            linarith
          linarith)
        rw [← this, hBe]
      rw [hGe, one_div, ← psi_eq_Log]
      exact psi_mem hLI (Ad_mem_lieC_of_mem G (huG z) (hA'l ρ z)) (GaugeGroup.lie_subset_lieC hB0) (by
        rw [SupportCont.opNorm_Ad_unitary (hu z)]
        have hA1 := (hA' ρ z hb).trans hα₁c
        have hpi := Real.pi_lt_d2
        have : K / 2 * c ≤ 1 / 80 := by
          have := mul_le_mul_of_nonneg_left hc3 (by linarith : (0 : ℝ) ≤ K / 2)
          have e : K / 2 * (1 / (40 * K)) = 1 / 80 := by field_simp; ring
          linarith
        have hc40 : c ≤ 1 / 160 := hc3.trans (by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
        have h1 : Real.pi / 2 * (K / 2 * c) ≤ Real.pi / 2 * (1 / 80) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        linarith)
    · rw [hz ρ z hb]; exact GaugeGroup.lie_subset_lieC G.zero_mem_lie
  -- the restricted form transported by `u`
  set B' := AdF u (restrictF B (InBoxB y h μ))
  have hB'l : ∀ ρ z, B' ρ z ∈ G.lieC := fun ρ z => by
    simp only [B', AdF, restrictF]
    split_ifs
    · exact Ad_mem_lieC_of_mem G (huG z) (hBl ρ z)
    · simp only [Ad, mul_zero, zero_mul]; exact GaugeGroup.lie_subset_lieC G.zero_mem_lie
  have hB'n : ‖B'‖ = ‖restrictF B (InBoxB y h μ)‖ := norm_AdF_unitary hu _
  have hXci : ‖X‖ < ci := lt_of_le_of_lt hXc (by have := hKc ci hc1; linarith)
  have hXcL : ‖X‖ < cL := lt_of_le_of_lt hXc (by have := hKc cL hc2; linarith)
  have hBci : ‖B'‖ < ci := by
    rw [hB'n]; exact lt_of_lt_of_le hB (hc1.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith))
  have hBcL : ‖B'‖ < cL := by
    rw [hB'n]; exact lt_of_lt_of_le hB (hc2.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith))
  rw [relLog_box hn2 (moveC U A') y μ B, relLog_reduce hUg hn hag _ (hpol y X B' hXci hBci)]
  exact hmemL y X B' hXl hB'l hXcL hBcL

end RelativeAverage
end CoreLean

end
