/-
`prop:relative-average`(viii) of BALABAN_CORE.tex (`fe7d249fe3af`), the holomorphy in the background: the maps
`Q(𝐔)`, `C(𝐔; ·)`, and `Q'(𝐔)` at `𝐔 = e^{iaA'}U` are holomorphic in `A'`.

* `Qlin_background_holo`: `A' ↦ Q(e^{iaA'}U)B` is holomorphic on a ball, for every `B`: `Q` is the derivative at `B = 0`
  of the jointly holomorphic `(A', B) ↦ (1/i) log 𝓜_{e^{iaA'}U}(B)(c)` (`relLog_core_pair_differentiableAt`), bounded on a
  polydisc by `relative_average_box`, and `deriv_param_differentiableOn` applies.
* `Crem_background_holo`: `A' ↦ C(e^{iaA'}U; B)` is holomorphic, as the difference of the slice and of `Q`.
* `blockAvg_background_holo`: `A' ↦ Q'(e^{iaA'}U)λ` at the two ends of the bond is holomorphic, the transports being
  holomorphic where the conditions of `core_good` hold.
-/
import CoreLean.RelativeAverageKernels
import CoreLean.ParamDeriv

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

lemma boxBond_le_norm {n : ℕ} [NeZero n] {y : Site n} {h : ℕ} {μ : Fin 4} (A' : Fin 4 → Site n → Mat) :
    ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ ‖A'‖ := fun ρ z _ =>
  (norm_le_pi_norm (A' ρ) z).trans (norm_le_pi_norm A' ρ)

set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average`(viii), the holomorphy of `Q` and `C` in `A'`**: there is `c > 0`, depending on `L` and `G`
only, such that for a gauge field `U` whose plaquettes on the blocks of the bond are at most `α₀ ≤ c`, the maps
`A' ↦ Q(e^{iaA'}U)B` (every `B`) and `A' ↦ C(e^{iaA'}U; B)` (`‖B‖ < c`) are holomorphic on `{‖A'‖ < c}`. -/
theorem Q_C_background_holo (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        (∀ B : Fin 4 → Site n → Mat, DifferentiableOn ℂ (fun A' => Qlin (moveC U A') y μ h B) (ball 0 c)) ∧
        (∀ B : Fin 4 → Site n → Mat, ‖B‖ < c →
          DifferentiableOn ℂ (fun A' => Crem (moveC U A') B y μ h) (ball 0 c)) := by
  classical
  obtain ⟨cP, hcP, hP⟩ := relLog_core_pair_differentiableAt (N := N) h μ
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  set r := min cP cb with hr
  have hr0 : 0 < r := lt_min hcP hcb
  have hrP : r ≤ cP := min_le_left _ _
  have hrb : r ≤ cb := min_le_right _ _
  refine ⟨r / 2, by positivity, ?_⟩
  intro n _ U hU hn y α₀ hα₀ hα₀c hplq
  have hα₀P : α₀ ≤ cP := hα₀c.trans (by linarith)
  have hα₀b : α₀ ≤ cb := hα₀c.trans (by linarith)
  set f : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) → Mat := fun p => relLog (moveC U p.1) p.2 y μ h with hf
  have hfd : DifferentiableOn ℂ f (ball 0 r ×ˢ ball 0 r) := fun p hp => by
    obtain ⟨h1, h2⟩ := hp
    rw [mem_ball_zero_iff] at h1 h2
    refine (hP U hU hn y α₀ hα₀ hα₀P hplq p.1 p.2 ?_ ?_).differentiableWithinAt
    · exact (norm_restrictF_le _ _).trans_lt (h1.trans_le hrP)
    · exact (norm_restrictF_le _ _).trans_lt (h2.trans_le hrP)
  have hfM : ∀ A' ∈ ball (0 : Fin 4 → Site n → Mat) r, ∀ B ∈ ball (0 : Fin 4 → Site n → Mat) r,
      ‖f (A', B)‖ ≤ C₁ * r + C₂ * r ^ 2 := fun A' hA' B hB => by
    rw [mem_ball_zero_iff] at hA' hB
    have hA'b : ‖A'‖ ≤ cb := hA'.le.trans hrb
    obtain ⟨-, hQb, hCb⟩ := hbox U hU hn y α₀ ‖A'‖ hα₀ (norm_nonneg _) hα₀b hA'b hplq A' (boxBond_le_norm A') B
    have hBr : ‖restrictF B (InBoxB y h μ)‖ ≤ ‖B‖ := norm_restrictF_le _ _
    obtain ⟨hC, -⟩ := hCb (hBr.trans_lt (hB.trans_le hrb))
    have hBr' : ‖restrictF B (InBoxB y h μ)‖ ≤ r := hBr.trans hB.le
    have hB0 := norm_nonneg (restrictF B (InBoxB y h μ))
    simp only [hf]
    rw [linear_part]
    calc ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B + Crem (moveC U A') B y μ h‖
        ≤ ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ + ‖Crem (moveC U A') B y μ h‖ := norm_add_le _ _
      _ ≤ C₁ * ‖restrictF B (InBoxB y h μ)‖ + C₂ * ‖restrictF B (InBoxB y h μ)‖ ^ 2 := add_le_add hQb hC
      _ ≤ C₁ * r + C₂ * r ^ 2 := by gcongr
  -- `Q` is the derivative at `B = 0` of the slices
  have hQ : ∀ B : Fin 4 → Site n → Mat, DifferentiableOn ℂ (fun A' => Qlin (moveC U A') y μ h B) (ball 0 (r / 2)) :=
    fun B => by
      have hD := ParamDeriv.deriv_param_differentiableOn hr0 hr0 hfd hfM B
      have e : (fun A' => Qlin (moveC U A') y μ h B) =
          fun A' => (((2 * h + 1 : ℕ) : ℂ))⁻¹ • fderiv ℂ (fun B' => f (A', B')) 0 B := by
        funext A'; simp only [Qlin, hf, ContinuousLinearMap.smul_apply]
      rw [e]
      exact hD.const_smul ((((2 * h + 1 : ℕ) : ℂ))⁻¹)
  refine ⟨hQ, fun B hB => ?_⟩
  have hBr : B ∈ ball (0 : Fin 4 → Site n → Mat) r := mem_ball_zero_iff.2 (hB.trans (half_lt_self hr0))
  have hsl : DifferentiableOn ℂ (fun A' => f (A', B)) (ball 0 (r / 2)) := fun A' hA' =>
    DifferentiableWithinAt.comp (g := f) A' (hfd (A', B) ⟨ball_subset_ball (half_le_self hr0.le) hA', hBr⟩)
      (differentiableAt_id.prodMk (differentiableAt_const B)).differentiableWithinAt
      (fun A'' hA'' => Set.mk_mem_prod (ball_subset_ball (half_le_self hr0.le) hA'') hBr)
  have e : (fun A' => Crem (moveC U A') B y μ h) =
      fun A' => f (A', B) - ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B := by
    funext A'; simp only [Crem, hf]
  rw [e]
  exact hsl.sub ((hQ B).const_smul (((2 * h + 1 : ℕ) : ℂ)))

set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average`(viii), the holomorphy of `Q'` in `A'`**: for a gauge field `U` whose plaquettes on the
blocks of the bond are at most `α₀ ≤ c`, the map `A' ↦ Q'(e^{iaA'}U)λ` at either end of the bond is holomorphic on
`{‖A'‖ < c}`, for every `0`-form `λ`. -/
theorem Q'_background_holo (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ lam : Site n → Mat,
          DifferentiableOn ℂ (fun A' => blockAvg (moveC U A') lam y h) (ball 0 c) ∧
          DifferentiableOn ℂ (fun A' => blockAvg (moveC U A') lam (cPlus y μ h) h) (ball 0 c) := by
  obtain ⟨cg, hcg, hgood⟩ := core_good (N := N) h μ
  refine ⟨cg, hcg, ?_⟩
  intro n _ U hU hn y α₀ hα₀ hα₀c hplq lam
  have hAd : ∀ (z : Site n), (∀ A' : Fin 4 → Site n → Mat, ‖A'‖ < cg → GoodAt (moveC U A') z h) →
      DifferentiableOn ℂ (fun A' => blockAvg (moveC U A') lam z h) (ball 0 cg) := fun z hz A' hA' => by
    have hA'n : ‖A'‖ < cg := mem_ball_zero_iff.1 hA'
    have hg := hz A' hA'n
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold blockAvg Ad
    refine DifferentiableAt.const_smul (𝕜 := ℂ) (c := (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ?_
    refine DifferentiableAt.fun_sum (𝕜 := ℂ) (u := Finset.univ) (A := fun (x : Pts h) (A' : Fin 4 → Site n → Mat) =>
      ((trans (moveC U A') z h x : GLN) : Mat) * lam (ofs z (offP h x)) *
        (((trans (moveC U A') z h x)⁻¹ : GLN) : Mat)) fun x _ => ?_
    have ht := trans_moveC_differentiableAt hg x
    exact (ht.mul (differentiableAt_const _)).mul (inv_differentiableAt ht)
  refine ⟨hAd y fun A' hA' => ?_, hAd (cPlus y μ h) fun A' hA' => ?_⟩
  · exact (hgood U hU hn y α₀ ‖A'‖ hα₀ (norm_nonneg _) hα₀c hA'.le hplq A' (boxBond_le_norm A')).1
  · exact (hgood U hU hn y α₀ ‖A'‖ hα₀ (norm_nonneg _) hα₀c hA'.le hplq A' (boxBond_le_norm A')).2.1

set_option maxHeartbeats 4000000 in
/-- **The Lipschitz continuity of the derivative of a remainder in the parameter** (the second half of the Lipschitz
continuity of `C_n` in `a_jA'`, `prop:relative-average-order`(v)): under the hypotheses of `remainder_lip`, the
derivatives of the remainders in a direction `δ` satisfy
`‖∂_y(R_{x₁} - R_{x₂})(y)δ‖ ≤ 32M‖x₁ - x₂‖‖y‖‖δ‖/(r₁r₂²)` for `‖y‖ < r₂/4`. The difference `φ = R_{x₁} - R_{x₂}` is at
most `2K`, `K = 2M‖x₁ - x₂‖/r₁`, and vanishes with its derivative at `0`; `y ↦ ∂_yφ(y)δ` is holomorphic by
`deriv_param_differentiableOn`, at most `4K‖δ‖/r₂` on `{‖y‖ < r₂/4}` by Cauchy's estimate, and the lemma of Schwarz
applies. -/
theorem remainder_lip_deriv {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z] {f : X × Y → Z} {r₁ r₂ M : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hf : DifferentiableOn ℂ f (ball (0 : X) r₁ ×ˢ ball (0 : Y) r₂))
    (hM : ∀ x ∈ ball (0 : X) r₁, ∀ y ∈ ball (0 : Y) r₂, ‖f (x, y)‖ ≤ M) (h0 : ∀ x, f (x, 0) = 0)
    {x₁ x₂ : X} (hx₁ : ‖x₁‖ ≤ r₁ / 2) (hx₂ : ‖x₂‖ ≤ r₁ / 2) {y : Y} (hy : ‖y‖ < r₂ / 4) (δ : Y) :
    ‖fderiv ℂ (fun y' => (f (x₁, y') - fderiv ℂ (fun y'' => f (x₁, y'')) 0 y') -
        (f (x₂, y') - fderiv ℂ (fun y'' => f (x₂, y'')) 0 y')) y δ‖ ≤
      32 * M * ‖x₁ - x₂‖ * ‖y‖ * ‖δ‖ / (r₁ * r₂ ^ 2) := by
  have hsy : ∀ x ∈ ball (0 : X) r₁, DifferentiableOn ℂ (fun y => f (x, y)) (ball 0 r₂) := fun x hx y hy =>
    (hf (x, y) ⟨hx, hy⟩).comp y ((differentiableAt_const x).prodMk differentiableAt_id).differentiableWithinAt
      (fun y' hy' => Set.mk_mem_prod hx hy')
  have hsx : ∀ y ∈ ball (0 : Y) r₂, DifferentiableOn ℂ (fun x => f (x, y)) (ball 0 r₁) := fun y hy x hx =>
    (hf (x, y) ⟨hx, hy⟩).comp x (differentiableAt_id.prodMk (differentiableAt_const y)).differentiableWithinAt
      (fun x' hx' => Set.mk_mem_prod hx' hy)
  have hb₁ : x₁ ∈ ball (0 : X) r₁ := mem_ball_zero_iff.2 (by linarith)
  have hb₂ : x₂ ∈ ball (0 : X) r₁ := mem_ball_zero_iff.2 (by linarith)
  set K := 2 * M / r₁ * ‖x₁ - x₂‖ with hK
  set hd : Y → Z := fun y => f (x₁, y) - f (x₂, y) with hhd
  have hdd : DifferentiableOn ℂ hd (ball 0 r₂) := (hsy x₁ hb₁).sub (hsy x₂ hb₂)
  have hdK : ∀ y ∈ ball (0 : Y) r₂, ‖hd y‖ ≤ K := fun y hy =>
    lip_half_ball hr₁ (hsx y hy) (fun x hx => hM x hx y hy) hx₁ hx₂
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hdK 0 (mem_ball_self hr₂))
  have hd0 : hd 0 = 0 := by simp [hhd, h0]
  have hn0 : ball (0 : Y) r₂ ∈ 𝓝 (0 : Y) := ball_mem_nhds 0 hr₂
  have hD₁ := ((hsy x₁ hb₁).differentiableAt hn0).hasFDerivAt
  have hD₂ := ((hsy x₂ hb₂).differentiableAt hn0).hasFDerivAt
  set L := fderiv ℂ (fun y' => f (x₁, y')) 0 - fderiv ℂ (fun y' => f (x₂, y')) 0 with hL
  have hdL : HasFDerivAt hd L 0 := hD₁.sub hD₂
  have hLeq : fderiv ℂ hd 0 = L := hdL.fderiv
  have hLv : ∀ v : Y, ‖L v‖ ≤ K * ‖v‖ / r₂ := fun v => by
    have := SchwarzCauchy.cauchy_fderiv hdd hdK (mem_ball_self hr₂) v
    rwa [hLeq, sub_self, norm_zero, sub_zero] at this
  set φ : Y → Z := fun y => hd y - L y with hφ
  have hφd : DifferentiableOn ℂ φ (ball 0 r₂) := hdd.sub L.differentiable.differentiableOn
  have hφ0 : φ 0 = 0 := by simp [hφ, hd0]
  have hφD : HasFDerivAt φ (0 : Y →L[ℂ] Z) 0 := by
    have := hdL.sub L.hasFDerivAt
    rwa [sub_self] at this
  have hφK : ∀ y ∈ ball (0 : Y) r₂, ‖φ y‖ ≤ 2 * K := fun y hy => by
    have hyr : ‖y‖ < r₂ := mem_ball_zero_iff.1 hy
    have h1 := hdK y hy
    have h2 := hLv y
    have h3 : K * ‖y‖ / r₂ ≤ K := by
      rw [div_le_iff₀ hr₂]; exact mul_le_mul_of_nonneg_left hyr.le hK0
    calc ‖φ y‖ ≤ ‖hd y‖ + ‖L y‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith
  have e : (fun y' => (f (x₁, y') - fderiv ℂ (fun y'' => f (x₁, y'')) 0 y') -
      (f (x₂, y') - fderiv ℂ (fun y'' => f (x₂, y'')) 0 y')) = φ := by
    funext y'; simp only [hφ, hhd, hL, ContinuousLinearMap.sub_apply]; abel
  rw [e]
  -- `y ↦ ∂_yφ(y)δ` is holomorphic on the ball of radius `r₂/4`
  set F : Y × Y → Z := fun p => φ (p.2 + p.1) with hF
  have hr4 : 0 < r₂ / 2 := by positivity
  have hsum : ∀ p : Y × Y, p ∈ ball (0 : Y) (r₂ / 2) ×ˢ ball (0 : Y) (r₂ / 2) → p.2 + p.1 ∈ ball (0 : Y) r₂ :=
    fun p hp => by
      obtain ⟨h1, h2⟩ := hp
      rw [mem_ball_zero_iff] at h1 h2 ⊢
      calc ‖p.2 + p.1‖ ≤ ‖p.2‖ + ‖p.1‖ := norm_add_le _ _
        _ < r₂ := by linarith
  have hFd : DifferentiableOn ℂ F (ball (0 : Y) (r₂ / 2) ×ˢ ball (0 : Y) (r₂ / 2)) := fun p hp =>
    DifferentiableWithinAt.comp (g := φ) p (hφd _ (hsum p hp))
      ((differentiableAt_snd.add differentiableAt_fst).differentiableWithinAt) (fun q hq => hsum q hq)
  have hFM : ∀ a ∈ ball (0 : Y) (r₂ / 2), ∀ b ∈ ball (0 : Y) (r₂ / 2), ‖F (a, b)‖ ≤ 2 * K := fun a ha b hb =>
    hφK _ (hsum (a, b) ⟨ha, hb⟩)
  have hψd := ParamDeriv.deriv_param_differentiableOn hr4 hr4 hFd hFM δ
  have hψe : ∀ a ∈ ball (0 : Y) (r₂ / 2), fderiv ℂ (fun b => F (a, b)) 0 δ = fderiv ℂ φ a δ := fun a ha => by
    have ha' : a ∈ ball (0 : Y) r₂ := ball_subset_ball (half_le_self hr₂.le) ha
    have hφa : HasFDerivAt φ (fderiv ℂ φ a) (0 + a) := by
      rw [zero_add]; exact (hφd.differentiableAt (isOpen_ball.mem_nhds ha')).hasFDerivAt
    have hadd : HasFDerivAt (fun b : Y => b + a) (ContinuousLinearMap.id ℂ Y) 0 := (hasFDerivAt_id 0).add_const a
    have hc := hφa.comp (0 : Y) hadd
    rw [ContinuousLinearMap.comp_id] at hc
    rw [show (fun b => F (a, b)) = φ ∘ (fun b => b + a) from rfl, hc.fderiv]
  set ψ : Y → Z := fun a => fderiv ℂ φ a δ with hψ
  have hψd' : DifferentiableOn ℂ ψ (ball 0 (r₂ / 2 / 2)) := hψd.congr fun a ha =>
    (hψe a (ball_subset_ball (half_le_self hr4.le) ha)).symm
  have hψ0 : ψ 0 = 0 := by simp [hψ, hφD.fderiv]
  have hψK : ∀ a ∈ ball (0 : Y) (r₂ / 2 / 2), ‖ψ a - ψ 0‖ ≤ 4 * K * ‖δ‖ / r₂ := fun a ha => by
    rw [hψ0, sub_zero]
    have ha4 : ‖a‖ < r₂ / 4 := by have := mem_ball_zero_iff.1 ha; linarith
    have ha' : a ∈ ball (0 : Y) r₂ := mem_ball_zero_iff.2 (by linarith)
    have hc := SchwarzCauchy.cauchy_fderiv hφd hφK ha' δ
    rw [sub_zero] at hc
    have hden : 3 * r₂ / 4 ≤ r₂ - ‖a‖ := by linarith
    have hnum : 0 ≤ 2 * K * ‖δ‖ := by positivity
    calc ‖ψ a‖ ≤ 2 * K * ‖δ‖ / (r₂ - ‖a‖) := hc
      _ ≤ 2 * K * ‖δ‖ / (3 * r₂ / 4) := div_le_div_of_nonneg_left hnum (by positivity) hden
      _ ≤ 4 * K * ‖δ‖ / r₂ := by
          rw [div_le_div_iff₀ (by positivity) hr₂]; nlinarith
  have hy' : y ∈ ball (0 : Y) (r₂ / 2 / 2) := mem_ball_zero_iff.2 (by linarith)
  have hs1 := SchwarzCauchy.schwarz_one hψd' hψK hy'
  rw [hψ0, sub_zero, sub_zero] at hs1
  show ‖ψ y‖ ≤ _
  calc ‖ψ y‖ ≤ 4 * K * ‖δ‖ / r₂ / (r₂ / 2 / 2) * ‖y‖ := hs1
    _ = 32 * M * ‖x₁ - x₂‖ * ‖y‖ * ‖δ‖ / (r₁ * r₂ ^ 2) := by rw [hK]; field_simp; ring

/-- The forms of the levels vanish when the forms of the level `0` vanish: `(1/i) log 𝓜_V(0) = 0`, and `𝓜` at a bond
depends only on the form on the bonds of its box, which are bonds of the region of the level below. -/
lemma forms_zero (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (hn : ∀ l, 4 * h + 4 ≤ nn l)
    (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l)) (B : ∀ l, Fin 4 → Site (nn l) → Mat)
    (hrel : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h)
    (h0 : ∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
      B 0 ν (img h (base 0) 0 x) = 0) :
    ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      B l ν (img h (base l) l x) = 0 := by
  classical
  intro l
  induction l with
  | zero => intro _; exact h0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    rw [hrel l hll ρ x hx q0 q1, relLog_box hn2 (V l) _ ρ (B l)]
    have hz : restrictF (B l) (InBoxB (img h (base l) l x) h ρ) = 0 := by
      funext ν z
      by_cases hb : BoxBond (img h (base l) l x) h ρ ν z
      · rw [restrictF_box_apply _ hb]
        obtain ⟨x'', hx'', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
        exact ih hll.le ν x'' hx'' r0 r1
      · rw [restrictF_box_apply' _ hb]; rfl
    rw [hz, relLog_zero]

set_option maxHeartbeats 1000000 in
/-- The forms of the pairs `(a, w)` are jointly holomorphic at `p₀`, for backgrounds `e^{iA'(a)_l}U_l` with fluctuations
holomorphic at `p₀.1` (`forms_differentiableAt_pair` over the product of the spaces of the forms of the level `0`). -/
theorem forms_pair_at (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (A'f : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (Bf : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (a₀ s₀ : ℕ → ℝ) (p₀ : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat)),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖A'f p₀.1 l ν (img h (base l) l x)‖ ≤ s₀ l ∧ ‖Bf p₀ l ν (img h (base l) l x)‖ ≤ s₀ l ∧
        DifferentiableAt ℂ (fun a => A'f a l ν (img h (base l) l x)) p₀.1) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ p, Bf p (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          relLog (moveC (U l) (A'f p.1 l)) (Bf p l) (img h (base l) l x) ρ h) →
      (∀ p ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        Bf p 0 ν (img h (base 0) 0 x) = p.2 ν (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        DifferentiableAt ℂ (fun p => Bf p l ν (img h (base l) l x)) p₀ := by
  obtain ⟨c, hc, hFP⟩ := forms_differentiableAt_pair (N := N) h
  refine ⟨c, hc, ?_⟩
  intro nl μ nn _ hn base U A'f Bf a₀ s₀ p₀ hU hplq hA hrel h0 ha
  have h1 : ∀ l, l < nl → ∀ ν' x', Lat (Lz h) l x' → Rg h nl μ l x' → Rg h nl μ l (x' + Lz h ^ l • Pi.single ν' 1) →
      (∀ p : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat),
        moveC (U l) (A'f p.1 l) ν' (img h (base l) l x') = moveC (U l) (A'f p.1 l) ν' (img h (base l) l x')) ∧
      ‖A'f p₀.1 l ν' (img h (base l) l x')‖ ≤ s₀ l ∧ ‖Bf p₀ l ν' (img h (base l) l x')‖ ≤ s₀ l ∧
      DifferentiableAt ℂ (fun p : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) =>
        A'f p.1 l ν' (img h (base l) l x')) p₀ := fun l hl ν' x' hx' r0 r1 =>
    ⟨fun _ => rfl, (hA l hl ν' x' hx' r0 r1).1, (hA l hl ν' x' hx' r0 r1).2.1,
      DifferentiableAt.comp (g := fun a => A'f a l ν' (img h (base l) l x')) p₀
        (hA l hl ν' x' hx' r0 r1).2.2 differentiableAt_fst⟩
  have h4 : ∀ ν' x', Lat (Lz h) 0 x' → Rg h nl μ 0 x' → Rg h nl μ 0 (x' + Lz h ^ 0 • Pi.single ν' 1) →
      DifferentiableAt ℂ (fun p : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) =>
        Bf p 0 ν' (img h (base 0) 0 x')) p₀ := fun ν' x' hx' r0 r1 => by
    rw [show (fun p : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) =>
        Bf p 0 ν' (img h (base 0) 0 x')) = fun p => p.2 ν' (img h (base 0) 0 x') from
      funext fun p => h0 p ν' x' hx' r0 r1]
    exact DifferentiableAt.comp (g := fun w : Fin 4 → Site (nn 0) → Mat => w ν' (img h (base 0) 0 x')) p₀
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site (nn 0) => Mat) (img h (base 0) 0 x')).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site (nn 0) → Mat) ν')).differentiableAt
      differentiableAt_snd
  have key := @hFP nl μ nn _ hn base U ((Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat)) _ _
    (fun p l => moveC (U l) (A'f p.1 l)) (fun p => A'f p.1) Bf p₀ a₀ s₀ hU h1 hplq ha
    (fun l hl ρ x' hx' r0 r1 p => hrel l hl ρ x' hx' r0 r1 p) h4
  exact key

set_option maxHeartbeats 4000000 in
/-- **`prop:relative-average-order`(v), the Lipschitz continuity of `C_n` in `a_jA'`**: for families
`a ↦ A'(a)_l` of fluctuations of the backgrounds `V(a)_l = e^{iA'(a)_l}U_l`, holomorphic on the ball of radius `R₁`, and
the forms `B(a, w)_{l+1} = (1/i) log 𝓜_{V(a)_l}(B(a, w)_l)` with `B(a, w)_0 = w`, all of them smaller than `c` on the
regions for `‖a‖ < R₁`, `‖w‖ < R₂`, and with `‖B(a, w)_n‖ ≤ M` at a bond `c` of the last level, the remainders
`C_n(a; w) = B(a, w)_n - ∂_wB(a, 0)_n w` at `c` satisfy, for `‖a₁‖, ‖a₂‖ ≤ R₁/2`,
`‖C_n(a₁; w) - C_n(a₂; w)‖ ≤ 4M‖a₁ - a₂‖‖w‖²/(R₁R₂²)` for `‖w‖ < R₂` and
`‖∂_wC_n(a₁; w)δ - ∂_wC_n(a₂; w)δ‖ ≤ 32M‖a₁ - a₂‖‖w‖‖δ‖/(R₁R₂²)` for `‖w‖ < R₂/4`: `B(·, ·)_n` is jointly holomorphic
(`forms_differentiableAt_pair`), vanishes at `w = 0` (`forms_zero`), and `remainder_lip`, `remainder_lip_deriv` apply. -/
theorem order_v_lip_C (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (A'f : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (Bf : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (a₀ s₀ : ℕ → ℝ) (R₁ R₂ M : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) →
      (∀ a ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R₁, ∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x →
        Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖A'f a l ν (img h (base l) l x)‖ ≤ s₀ l ∧ DifferentiableAt ℂ (fun a => A'f a l ν (img h (base l) l x)) a) →
      (∀ p ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R₁ ×ˢ ball (0 : Fin 4 → Site (nn 0) → Mat) R₂, ∀ l, l < nl →
        ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖Bf p l ν (img h (base l) l x)‖ ≤ s₀ l) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ p, Bf p (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          relLog (moveC (U l) (A'f p.1 l)) (Bf p l) (img h (base l) l x) ρ h) →
      (∀ p ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        Bf p 0 ν (img h (base 0) 0 x) = p.2 ν (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ c ∧ 0 ≤ s₀ l ∧ s₀ l < c) → 0 < R₁ → 0 < R₂ →
      ∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        (∀ p ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R₁ ×ˢ ball (0 : Fin 4 → Site (nn 0) → Mat) R₂,
          ‖Bf p nl ν (img h (base nl) nl x)‖ ≤ M) →
        ∀ a₁ a₂ : Fin 4 → Site (nn 0) → Mat, ‖a₁‖ ≤ R₁ / 2 → ‖a₂‖ ≤ R₁ / 2 →
        (∀ w : Fin 4 → Site (nn 0) → Mat, ‖w‖ < R₂ →
          ‖(Bf (a₁, w) nl ν (img h (base nl) nl x) -
              fderiv ℂ (fun w' => Bf (a₁, w') nl ν (img h (base nl) nl x)) 0 w) -
            (Bf (a₂, w) nl ν (img h (base nl) nl x) -
              fderiv ℂ (fun w' => Bf (a₂, w') nl ν (img h (base nl) nl x)) 0 w)‖ ≤
            4 * M * ‖a₁ - a₂‖ * ‖w‖ ^ 2 / (R₁ * R₂ ^ 2)) ∧
        (∀ w δ : Fin 4 → Site (nn 0) → Mat, ‖w‖ < R₂ / 4 →
          ‖fderiv ℂ (fun w' => (Bf (a₁, w') nl ν (img h (base nl) nl x) -
              fderiv ℂ (fun w'' => Bf (a₁, w'') nl ν (img h (base nl) nl x)) 0 w') -
            (Bf (a₂, w') nl ν (img h (base nl) nl x) -
              fderiv ℂ (fun w'' => Bf (a₂, w'') nl ν (img h (base nl) nl x)) 0 w')) w δ‖ ≤
            32 * M * ‖a₁ - a₂‖ * ‖w‖ * ‖δ‖ / (R₁ * R₂ ^ 2)) := by
  obtain ⟨c, hc, hpa⟩ := forms_pair_at (N := N) h
  refine ⟨c, hc, ?_⟩
  intro nl μ nn _ hn base U A'f Bf a₀ s₀ R₁ R₂ M hU hplq hA' hB hrel h0 ha hR₁ hR₂ ν x hx q0 q1 hM a₁ a₂ ha₁ ha₂
  have hfd : DifferentiableOn ℂ (fun p : (Fin 4 → Site (nn 0) → Mat) × (Fin 4 → Site (nn 0) → Mat) =>
      Bf p nl ν (img h (base nl) nl x)) (ball 0 R₁ ×ˢ ball 0 R₂) := fun p₀ hp₀ =>
    (hpa nl μ nn hn base U A'f Bf a₀ s₀ p₀ hU hplq
      (fun l hl ν' x' hx' r0 r1 => ⟨(hA' p₀.1 hp₀.1 l hl ν' x' hx' r0 r1).1, hB p₀ hp₀ l hl ν' x' hx' r0 r1,
        (hA' p₀.1 hp₀.1 l hl ν' x' hx' r0 r1).2⟩) hrel h0 ha nl le_rfl ν x hx q0 q1).differentiableWithinAt
  have hfM : ∀ a ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R₁, ∀ w ∈ ball (0 : Fin 4 → Site (nn 0) → Mat) R₂,
      ‖Bf (a, w) nl ν (img h (base nl) nl x)‖ ≤ M := fun a ha w hw => hM (a, w) ⟨ha, hw⟩
  have hf0 : ∀ a, Bf (a, 0) nl ν (img h (base nl) nl x) = 0 := fun a =>
    forms_zero h nl μ nn hn base (fun l => moveC (U l) (A'f a l)) (fun l => Bf (a, 0) l)
      (fun l hl ρ x' hx' r0 r1 => hrel l hl ρ x' hx' r0 r1 (a, 0))
      (fun ν' x' hx' r0 r1 => by rw [h0 (a, 0) ν' x' hx' r0 r1]; rfl) nl le_rfl ν x hx q0 q1
  refine ⟨fun w hw => ?_, fun w δ hw => ?_⟩
  · exact remainder_lip hR₁ hR₂ hfd hfM hf0 ha₁ ha₂ (mem_ball_zero_iff.2 hw)
  · exact remainder_lip_deriv hR₁ hR₂ hfd hfM hf0 ha₁ ha₂ hw δ

end RelativeAverage
end CoreLean

end
