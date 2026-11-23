/-
The averages of a sequence preserve the values in `𝔤^c` (BALABAN_CORE.tex `615c66b253fe`, `prop:relative-average`,
"The remainder and the site factors": `(1/i)log𝓜_𝐔(A)(c) ∈ 𝔤^c`), the input `hQpres` of
`CriticalSequence.critical_ii_sequence_general`.

* `fderiv_mem_of_eventually`: if `f(tv)` lies in a subspace `S` for all small `t`, then so does `Df(0)v` (the slopes lie
  in `S`, which is closed; where `f` is not differentiable the derivative is `0`).
* `RayLieC G V h`: at every coarse bond, `relLog V (tB) ∈ 𝔤^c` for small `t` and every `B` with values in `𝔤^c`; this is
  the form of the conclusion of `prop:relative-average` at the configuration `V` (`rayLieC_of_regular`: it holds for
  `V = e^{iaA'}U` under the hypotheses of `RelativeAverage.relative_average_lieC` at every box).
* `Qlin_mem`, `Qstep_mem`, `Qcomp_mem`: `Q(V)`, and the composites `Q_j(U)` when `RayLieC` holds at the averages
  `M^i(U)`, `i < j`, map forms with values in `𝔤^c` to forms with values in `𝔤^c`.
* `hQpres_of_rays`: `Π_FQΠ = QΠ` for the compressions of a sequence, from `RayLieC` at the levels `j < k`.
-/
import CoreLean.SequenceOperators

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace QLieC

open Lattices SequenceIndex MultiscaleAverages SequenceAverages SequenceOperators RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- **The derivative at `0` lies in a subspace** in which the function lies along the ray. -/
lemma fderiv_mem_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → Mat)
    (S : Submodule ℂ Mat) (v : E) (h : ∀ᶠ t : ℂ in 𝓝 0, f (t • v) ∈ S) : fderiv ℂ f 0 v ∈ S := by
  by_cases hd : DifferentiableAt ℂ f 0
  · have hd' : HasFDerivAt f (fderiv ℂ f 0) ((fun t : ℂ => t • v) 0) := by simpa using hd.hasFDerivAt
    have hg : HasDerivAt (fun t : ℂ => f (t • v)) (fderiv ℂ f 0 v) 0 := by
      have := hd'.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
      rw [one_smul] at this
      exact this
    have hS : IsClosed (S : Set Mat) := S.isClosed_of_finiteDimensional
    refine hS.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hg) ?_
    have h0 : f ((0 : ℂ) • v) ∈ S := h.self_of_nhds
    filter_upwards [nhdsWithin_le_nhds h] with t ht
    rw [slope_def_module]
    exact S.smul_mem _ (S.sub_mem ht h0)
  · rw [fderiv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

variable {G : GaugeGroup N}

/-- At every coarse bond, `relLog V (tB) ∈ 𝔤^c` for small `t`, for every `B` with values in `𝔤^c`. -/
def RayLieC (G : GaugeGroup N) {n : ℕ} [NeZero n] (V : Config N n) (h : ℕ) : Prop :=
  ∀ (y : Site n) (κ : Fin 4) (B : Form1 N n), (∀ ρ z, B ρ z ∈ G.lieC) →
    ∀ᶠ t : ℂ in 𝓝 0, relLog V (t • B) y κ h ∈ G.lieC

/-- **`Q(V)` preserves the values in `𝔤^c`.** -/
lemma Qlin_mem (hG : G.LieInput) {n : ℕ} [NeZero n] {V : Config N n} {h : ℕ} (hV : RayLieC G V h) (y : Site n)
    (κ : Fin 4) {B : Form1 N n} (hB : ∀ ρ z, B ρ z ∈ G.lieC) : Qlin V y κ h B ∈ G.lieC := by
  have hd := fderiv_mem_of_eventually (fun B' => relLog V B' y κ h) (GaugeGroup.lieCSubmodule hG) B
    (by filter_upwards [hV y κ B hB] with t ht; rwa [GaugeGroup.mem_lieCSubmodule])
  rw [← GaugeGroup.mem_lieCSubmodule hG]
  simp only [Qlin, ContinuousLinearMap.smul_apply]
  exact Submodule.smul_mem _ _ hd

lemma Qstep_mem (hG : G.LieInput) (h m k j : ℕ) {V : Config N (nn h m k j)} (hV : RayLieC G V h)
    {B : Form1 N (nn h m k j)} (hB : ∀ ρ z, B ρ z ∈ G.lieC) (κ : Fin 4) (y : Site (nn h m k (j + 1))) :
    Qstep h m k j V B κ y ∈ G.lieC := by
  rw [Qstep_apply]
  exact Qlin_mem hG hV _ κ hB

/-- **`Q_j(U)` preserves the values in `𝔤^c`** when `RayLieC` holds at the averages `M^i(U)`, `i < j`. -/
lemma Qcomp_mem (hG : G.LieInput) (h m k : ℕ) (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0))
    (K : ℕ) (hlev : ∀ i < K, RayLieC G (Mpow h m k inN log U i) h) {B : Form1 N (nn h m k 0)}
    (hB : ∀ ρ z, B ρ z ∈ G.lieC) : ∀ j ≤ K, ∀ κ y, Qcomp h m k inN log U j B κ y ∈ G.lieC
  | 0, _ => fun κ y => by rw [Qcomp_zero]; exact hB κ y
  | j + 1, hj => fun κ y => by
      rw [Qcomp_succ, LinearMap.comp_apply]
      exact Qstep_mem hG h m k j (hlev j (by omega)) (Qcomp_mem hG h m k inN log U K hlev hB j (by omega)) κ y

/-- The compressed `1`-forms have their values in `𝔤^c`. -/
lemma piF1_mem (hG : G.LieInput) {n : ℕ} [NeZero n] (ΩD : Set (Site n)) (x : Form1 N n) (ρ : Fin 4) (z : Site n) :
    piF1 hG ΩD x ρ z ∈ G.lieC := by
  have h0 : (0 : Mat) ∈ G.lieC := by
    rw [← GaugeGroup.mem_lieCSubmodule hG]; exact Submodule.zero_mem _
  by_cases hz : z ∈ bondsOf ΩD ρ
  · simp only [piF1, LinearMap.coe_mk, AddHom.coe_mk, Set.indicator_of_mem hz]; exact proj_mem hG _
  · simp only [piF1, LinearMap.coe_mk, AddHom.coe_mk, Set.indicator_of_notMem hz]; exact h0

/-- **`Π_FQΠ = QΠ`** for a sequence of domains, from `RayLieC` at the averages `M^j(U)`, `j < k`. -/
theorem hQpres_of_rays (S : SeqDom) (hG : G.LieInput) (inN : GLN → Prop) (log : GLN → Mat)
    (U : Config N (SequenceAverages.N0 S)) (ΩD : Set (Site (SequenceAverages.N0 S)))
    (hlev : ∀ j < S.k, RayLieC G (Mpow (hS S) S.mT S.k inN log U j) (hS S)) (x : Form1 N (SequenceAverages.N0 S)) :
    piFun hG (LBond S) (Qseq S inN log U (piF1 hG ΩD x)) = Qseq S inN log U (piF1 hG ΩD x) := by
  funext c
  simp only [piFun, LinearMap.coe_mk, AddHom.coe_mk]
  refine piProj_self hG ?_
  rw [Qseq_apply]
  exact Qcomp_mem hG _ _ _ inN log U S.k hlev (piF1_mem hG ΩD x) c.1.1 c.2.1 _ _

section Discharge

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

/-- **`RayLieC` at `V = e^{iaA'}U`** under the hypotheses of `prop:relative-average` at every box
(`RelativeAverage.relative_average_lieC`, whose number `c` is taken as the minimum over the four directions). -/
theorem rayLieC_of_regular (G : GaugeGroup N) (hGc : IsClosed G.mats) (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ →
        α₀ ≤ c → α₁ ≤ c →
        (∀ (y : Site n) (μ μ' ν' : Fin 4) z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, A' ρ z ∈ G.lieC) →
          (∀ (y : Site n) (μ : Fin 4) ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) → RayLieC G (moveC U A') h := by
  have hLI := GaugeGroup.lieInput_of_isClosed hGc
  choose c hc hmem using fun μ : Fin 4 => relative_average_lieC (N := N) G hGc h μ
  refine ⟨Finset.univ.inf' Finset.univ_nonempty c, (Finset.lt_inf'_iff _).2 fun μ _ => hc μ, ?_⟩
  intro n _ U hU hn α₀ α₁ h0 h1 hα₀ hα₁ hplq A' hA'l hA' y κ B hB
  have hle : Finset.univ.inf' Finset.univ_nonempty c ≤ c κ := Finset.inf'_le _ (Finset.mem_univ κ)
  classical
  set R := restrictF B (InBoxB y h κ)
  have hR : ∀ t : ℂ, restrictF (t • B) (InBoxB y h κ) = t • R := fun t => by
    funext ρ z
    simp only [restrictF, R, Pi.smul_apply]
    split_ifs <;> simp
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ * ‖R‖ < c κ := by
    have hT : Tendsto (fun t : ℂ => ‖t‖ * ‖R‖) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * ‖R‖)) :=
      (continuous_norm.mul continuous_const).tendsto 0
    rw [norm_zero, zero_mul] at hT
    exact hT (Iio_mem_nhds (hc κ))
  filter_upwards [hev] with t ht
  refine hmem κ U hU hn y α₀ α₁ h0 h1 (hα₀.trans hle) (hα₁.trans hle) (hplq y κ) A' hA'l (hA' y κ) (t • B)
    (fun ρ z => ?_) ?_
  · rw [Pi.smul_apply, Pi.smul_apply, ← GaugeGroup.mem_lieCSubmodule hLI]
    exact Submodule.smul_mem _ t ((GaugeGroup.mem_lieCSubmodule hLI).2 (hB ρ z))
  · rw [hR, norm_smul]
    exact ht

end Discharge

end QLieC
end CoreLean

end
