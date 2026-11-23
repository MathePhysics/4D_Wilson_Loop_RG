/-
`prop:relative-average`(i) of BALABAN_CORE.tex (`615c66b253fe`), the analyticity at the core's configurations: for
`𝐔 = e^{iaA'}U` with a gauge field `U` whose plaquettes on the box are at most `α₀`, and `‖A'‖ ≤ α₁` on the bonds of
the box, `B ↦ (1/i)log𝓜_𝐔(B)(c)` is analytic at every `B₀` small on the box (`α₀, α₁ ≤ c`); and the local
conditions `RayAt`, `AnAt` of `LocalLevels` at one bond follow from these bounds for every configuration which agrees
with `e^{iaA'}U` on the box.

* `UX_hVa`, `moveC2_analyticAt`, `UXB_hVa`, `relLog_pair_analyticAt`: the pair `(X, B) ↦ (1/i)log𝓜_{𝐔_X}(B)(c)` is
  analytic where the conditions `Cond` hold (the families of `RelativeAverageAnalytic`).
* `relLog_core_analyticAt`: the proof of `relLog_core_differentiableAt` (`RelativeAverageKernels.lean`), with the
  reduction to `𝐔_X` near `id` (`reduce_box_supp`, `uniform_polydisc`) and `AnalyticAt.congr`.
* `anAt_of_regular`, `rayAt_of_regular`: `AnAt` and `RayAt` at one bond from the bounds on the box, through the
  locality `relLog_fun_local`.
-/
import CoreLean.RelativeAverageKernels
import CoreLean.LocalLevels

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference
  AxialStraightLattice BoxGeometry StraightExtension

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

section Pair

variable {n : ℕ} [NeZero n]

lemma UX_hVa (p₀ : PairSp N n) :
    ∀ μ z, AnalyticAt ℂ (fun p : PairSp N n => ((UX (N := N) p.1 μ z : GLN) : Mat)) p₀ := fun μ z =>
  (moveC_analyticAt (oneC (N := N)) p₀.1 μ z).comp analyticAt_fst

/-- The family `(A', B) ↦ e^{iB}e^{iA'}U` has analytic values. -/
lemma moveC2_analyticAt (U : Config N n) (p₀ : PairSp N n) (μ : Fin 4) (z : Site n) :
    AnalyticAt ℂ (fun p : PairSp N n => (((moveC (moveC U p.1) p.2) μ z : GLN) : Mat)) p₀ := by
  have hev : ∀ q : PairSp N n → Fin 4 → Site n → Mat, AnalyticAt ℂ q p₀ →
      AnalyticAt ℂ (fun p => exp (Complex.I • q p μ z)) p₀ := fun q hq => by
    have h1 : AnalyticAt ℂ (fun p => q p μ z) p₀ :=
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)).analyticAt (q p₀)).comp hq
    exact (exp_analytic _).comp_of_eq (h1.fun_const_smul (c := Complex.I)) rfl
  simp only [moveC, Units.val_mul, expU_val]
  exact (hev _ analyticAt_snd).fun_mul ((hev _ analyticAt_fst).fun_mul analyticAt_const)

lemma UXB_hVa (p₀ : PairSp N n) :
    ∀ μ z, AnalyticAt ℂ (fun p : PairSp N n => ((moveC (UX (N := N) p.1) p.2 μ z : GLN) : Mat)) p₀ := fun μ z =>
  moveC2_analyticAt oneC p₀ μ z

/-- `(1/i)log𝓜_{𝐔_X}(B)(c)` is analytic in the pair at a pair which satisfies the conditions. -/
theorem relLog_pair_analyticAt {y : Site n} {μ : Fin 4} {h : ℕ} {p₀ : PairSp N n}
    (hc : Cond (N := N) y μ h p₀) :
    AnalyticAt ℂ (fun p : PairSp N n => relLog (UX (N := N) p.1) p.2 y μ h) p₀ := by
  have hsf : ∀ y' : Site n, GoodAt (UX (N := N) p₀.1) y' h → GoodAt (moveC (UX (N := N) p₀.1) p₀.2) y' h →
      (∀ x, ‖((trans (moveC (UX (N := N) p₀.1) p₀.2) y' h x * (trans (UX (N := N) p₀.1) y' h x)⁻¹ : GLN) :
        Mat) - 1‖ < 1) →
      AnalyticAt ℂ (fun p : PairSp N n => ((siteFactor (UX (N := N) p.1) p.2 y' h : GLN) : Mat)) p₀ :=
    fun y' hg hgA hq =>
      siteFactor_analyticAt (fun p : PairSp N n => UX (N := N) p.1) (fun p => p.2) y' h
        (fun x => trans_analyticAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hVa p₀) y' h x
          (hgA.1 x) ((hgA.2 x).trans (by norm_num)))
        (fun x => trans_analyticAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hVa p₀) y' h x
          (hg.1 x) ((hg.2 x).trans (by norm_num))) hq
  have hR : AnalyticAt ℂ (fun p : PairSp N n => ((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat)) p₀ :=
    relAvg_analyticAt (fun p : PairSp N n => UX (N := N) p.1) (fun p => p.2) y μ h
      (hsf y hc.g0 hc.gA0 hc.q0) (hsf _ hc.g1 hc.gA1 hc.q1)
      (avgM_analyticAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hVa p₀) y μ h hc.lA)
      (avgM_analyticAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hVa p₀) y μ h hc.l0)
  exact (AnalyticAt.comp (f := fun p : PairSp N n => ((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat))
    (analyticOnNhd_LogM (N := N) _ hc.r) hR).fun_const_smul (c := (1 / Complex.I : ℂ))

end Pair

/-- **`prop:relative-average`(i): `B ↦ (1/i)log𝓜_𝐔(B)(c)` is analytic** for `𝐔 = e^{iaA'}U` under the bounds on the
box, at every `B₀` small on the box. -/
theorem relLog_core_analyticAt (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B₀ : Fin 4 → Site n → Mat, ‖restrictF B₀ (InBoxB y h μ)‖ < c →
          AnalyticAt ℂ (fun B => relLog (moveC U A') B y μ h) B₀ := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B₀ hB₀
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  set P := restrictBoxL (N := N) y h μ
  set g : (Fin 4 → Site n → Mat) → Mat := fun B => relLog (UX (N := N) X) (AdFL u (P B)) y μ h with hg
  have hPB : ∀ B, P B = restrictF B (InBoxB y h μ) := fun B => rfl
  have hAdF : ∀ B, AdFL u B = AdF u B := fun B => rfl
  -- `g` is analytic at `B₀`
  have hcond0 : Cond (N := N) y μ h (X, AdFL u (P B₀)) :=
    hpol y X _ hXci (by rw [hAdF, hPB, norm_AdF_unitary hu]; linarith)
  have hgd : AnalyticAt ℂ g B₀ := by
    have hd := relLog_pair_analyticAt hcond0
    have hlin : AnalyticAt ℂ (fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) B₀ :=
      analyticAt_const.prod (((AdFL u).comp P).analyticAt B₀)
    exact AnalyticAt.comp (f := fun B : Fin 4 → Site n → Mat => ((X, AdFL u (P B)) : PairSp N n)) hd hlin
  -- `relLog 𝐔 = g` near `B₀`
  have hopen : IsOpen {B : Fin 4 → Site n → Mat | ‖P B‖ < ci} :=
    isOpen_lt (continuous_norm.comp P.continuous) continuous_const
  have hev : (fun B => relLog (moveC U A') B y μ h) =ᶠ[𝓝 B₀] g := by
    filter_upwards [hopen.mem_nhds (show ‖P B₀‖ < ci by rw [hPB]; linarith)] with B hB
    rw [relLog_box hn2 (moveC U A') y μ B]
    have hc := hpol y X (AdF u (restrictF B (InBoxB y h μ))) hXci (by rw [norm_AdF_unitary hu, ← hPB]; exact hB)
    rw [relLog_reduce hU hn hag _ hc]
    rfl
  exact hgd.congr hev.symm

/-! ### The local conditions at one bond -/

/-- **`AnAt` at one bond** for a configuration which agrees on the box with `e^{iaA'}U`, `U` a gauge field with the
bounds of `prop:relative-average` on the box. -/
theorem anAt_of_regular (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z → hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ V : Config N n, (∀ ν z, InBoxB y h μ z → InBoxB y h μ (z + unit n ν) → V ν z = moveC U A' ν z) →
          LocalLevels.AnAt V y μ h := by
  classical
  obtain ⟨c, hc, hcore⟩ := relLog_core_analyticAt (N := N) h μ
  refine ⟨c, hc, ?_⟩
  intro n _ U hU hn y α₀ α₁ h0 h1 hα₀ hα₁ hplq A' hA V hV
  have hfun := relLog_fun_local (V := V) (V' := moveC U A') (y := y) (μ := μ) (h := h) (by omega) hV
  have hz : ‖restrictF (0 : Fin 4 → Site n → Mat) (InBoxB y h μ)‖ < c := by
    have : restrictF (0 : Fin 4 → Site n → Mat) (InBoxB y h μ) = 0 := by funext ρ z; simp [restrictF]
    rw [this, norm_zero]; exact hc
  unfold LocalLevels.AnAt
  rw [hfun]
  exact hcore U hU hn y α₀ α₁ h0 h1 hα₀ hα₁ hplq A' hA 0 hz

/-- **`RayAt` at one bond** for a configuration which agrees on the box with `e^{iaA'}U`, `U` with values in `G`,
`A'` with values in `𝔤^c`, under the bounds of `prop:relative-average` on the box. -/
theorem rayAt_of_regular (G : GaugeGroup N) (hGc : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z → hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, A' ρ z ∈ G.lieC) → (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ V : Config N n, (∀ ν z, InBoxB y h μ z → InBoxB y h μ (z + unit n ν) → V ν z = moveC U A' ν z) →
          LocalLevels.RayAt G V y μ h := by
  classical
  have hLI := GaugeGroup.lieInput_of_isClosed hGc
  obtain ⟨c, hc, hmem⟩ := relative_average_lieC (N := N) G hGc h μ
  refine ⟨c, hc, ?_⟩
  intro n _ U hU hn y α₀ α₁ h0 h1 hα₀ hα₁ hplq A' hA'l hA V hV B hB
  have hfun := relLog_fun_local (V := V) (V' := moveC U A') (y := y) (μ := μ) (h := h) (by omega) hV
  set R := restrictF B (InBoxB y h μ)
  have hR : ∀ t : ℂ, restrictF (t • B) (InBoxB y h μ) = t • R := fun t => by
    funext ρ z
    simp only [restrictF, R, Pi.smul_apply]
    split_ifs <;> simp
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ * ‖R‖ < c := by
    have hT : Tendsto (fun t : ℂ => ‖t‖ * ‖R‖) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * ‖R‖)) :=
      (continuous_norm.mul continuous_const).tendsto 0
    rw [norm_zero, zero_mul] at hT
    exact hT (Iio_mem_nhds hc)
  filter_upwards [hev] with t ht
  have e := congrFun hfun (t • B)
  rw [e]
  refine hmem U hU hn y α₀ α₁ h0 h1 hα₀ hα₁ hplq A' hA'l hA (t • B) (fun ρ z => ?_) ?_
  · rw [Pi.smul_apply, Pi.smul_apply, ← GaugeGroup.mem_lieCSubmodule hLI]
    exact Submodule.smul_mem _ t ((GaugeGroup.mem_lieCSubmodule hLI).2 (hB ρ z))
  · rw [hR, norm_smul]
    exact ht

end RelativeAverage
end CoreLean

end
