/-
`prop:relative-average-order` of BALABAN_CORE.tex (`fe7d249fe3af`), the values of the fluctuations of the levels: the
proof of `lem:average-kernels` writes `𝐔^{(l)} = e^{ia_{i+l}A'_l}U_l` with `A'_l` taking values in `𝔤^c`, because
`log(𝐔^{(l)}(c')U_l(c')⁻¹)` is holomorphic in `A'`, lies in `i𝔤` for `A'` with values in `𝔤`, and `lem:real-points`(ii)
carries this to `A'` with values in `𝔤^c`.

* `fluct_lieC`: under the hypotheses of `background_lip`, with `U_l` taking values in `G` and the levels `W(a)_l` of the
  real forms `a` taking values in `G` on the regions (`lem:average`(i): the averages of gauge fields are gauge fields),
  the fluctuation `A'(a)_l` of every level lies in `𝔤^c` for `a` with values in `𝔤^c`, and `W(a)_l = e^{iA'(a)_l}U_l`.
-/
import CoreLean.RelativeAverageKernels
import CoreLean.RealPoints
import CoreLean.RelativeAverageGc

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

set_option maxHeartbeats 4000000 in
/-- **The fluctuations of the levels lie in `𝔤^c`**: under the hypotheses of `background_lip`, with `U_l` and the levels
`W(a)_l` of the forms `a` with values in `𝔤` taking values in `G` on the regions, for `a` with values in `𝔤^c` and
`‖a‖ < R = tL^{-n}` the averages are `W(a)_l = e^{iA'_l}U_l` on the bonds of the region of every level, with `A'_l ∈ 𝔤^c`
and `‖A'_l‖ ≤ (4C₁ + 4)tL^{-(n-l)}`. -/
theorem fluct_lieC (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (Bf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (gf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Site (nn l) → GLN)
      (Wf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Config N (nn l)) (a₀ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        ∀ a, Wf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (Wf a l) (img h (base l) l x) ρ h ∧
          Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x → ∀ a,
        gf a (l + 1) (img h (base (l + 1)) (l + 1) x) =
          gf a l (img h (base l) l x) * siteFactor (U l) (Bf a l) (img h (base l) l x) h) →
      (∀ a z, gf a 0 z = 1) →
      (∀ a ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        Wf a 0 ρ (img h (base 0) 0 x) = moveC (U 0) (Bf a 0) ρ (img h (base 0) 0 x) ∧
        Bf a 0 ρ (img h (base 0) 0 x) = a ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 < t → 0 ≤ e₀ → e₀ ≤ c → t ≤ c → C * (e₀ + 2 * t) ≤ 1 →
      (∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lie) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
        ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
          Wf a l ρ (img h (base l) l x) ∈ G.carrier) →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lieC) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
        ∃ A'l ∈ G.lieC, Wf a l ρ (img h (base l) l x) = expU (Complex.I • A'l) * U l ρ (img h (base l) l x) ∧
          ‖A'l‖ ≤ (4 * C₁ + 4) * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨cf, Cf, C₁f, hcf, hCf, hC₁f, hFH⟩ := fluct_holo (N := N) h hh
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  obtain ⟨rl, hrl, hrl4, hlog⟩ := log_mem_lie G hG
  set c := min cf (min (cb / 4) (min (1 / (1024 * (2 * C₁b + 2))) (rl / (8 * (4 * C₁b + 4))))) with hc_def
  have k1 : c ≤ cf := min_le_left _ _
  have k2 : c ≤ cb / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have k3 : c ≤ 1 / (1024 * (2 * C₁b + 2)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ rl / (8 * (4 * C₁b + 4)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc0 : 0 < c := lt_min hcf (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨c, max Cf Cb, C₁b, hc0, hCf.trans (le_max_left _ _), hC₁b, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he hec htc hCE hWG l hl ρ x hx q0 q1
  have hU : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  set R := t * (Lr ^ nl)⁻¹ with hR
  have hCEf : Cf * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hCEb : Cb * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  have hC₁bt : (2 * C₁b + 2) * t ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hBtr : (4 * C₁b + 4) * t ≤ rl / 8 := by
    calc (4 * C₁b + 4) * t ≤ (4 * C₁b + 4) * (rl / (8 * (4 * C₁b + 4))) := by gcongr; linarith
      _ = rl / 8 := by field_simp
  have hB0 : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x →
      Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) → ‖Bf a 0 ν (img h (base 0) 0 x)‖ ≤ t * (Lr ^ nl)⁻¹ :=
    fun a haR ν x hx q0 q1 => by
      rw [(h0 a ν x hx q0 q1).2]
      exact ((norm_le_pi_norm (a ν) _).trans (norm_le_pi_norm a ν)).trans haR.le
  -- the decomposition `W(a)_l = e^{iB}U_l` with a small `B`
  have hBt : ∀ a : Fin 4 → Site (nn 0) → Mat, ‖a‖ < R → ∃ Bt : Mat,
      Wf a l ρ (img h (base l) l x) = expU (Complex.I • Bt) * U l ρ (img h (base l) l x) ∧
      ‖Bt‖ ≤ (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ := fun a haR =>
    hBL nl μ nn hn base U (Wf a) (Bf a) (gf a) a₀ t e₀ hU
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1) (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
      (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2) (fun l hl x hx q0 => hgr l hl x hx q0 a)
      (hg0 a) ha ht.le he (hec.trans (k2.trans (by linarith))) (by linarith) hCEb hC₁bt (hB0 a haR) l hl ρ x hx q0 q1
  have hsmall : ∀ Bt : Mat, ‖Bt‖ ≤ (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ → ‖Bt‖ ≤ rl / 8 := fun Bt hb => by
    have : (4 * C₁b + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁b + 4) * t :=
      mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
    linarith
  -- the fluctuation and its value
  set F : (Fin 4 → Site (nn 0) → Mat) → Mat := fun a =>
    (1 / Complex.I) • LogM (((Wf a l ρ (img h (base l) l x) * (U l ρ (img h (base l) l x))⁻¹ : GLN) : Mat)) with hF
  have hl2 := Real.log_two_gt_d9
  have hFval : ∀ a : Fin 4 → Site (nn 0) → Mat, ∀ Bt : Mat,
      Wf a l ρ (img h (base l) l x) = expU (Complex.I • Bt) * U l ρ (img h (base l) l x) → ‖Bt‖ ≤ rl / 8 →
      F a = Bt := fun a Bt hW hb => by
    simp only [hF]
    rw [hW, mul_inv_cancel_right]
    exact order_iv rfl (by linarith)
  have hFd : DifferentiableOn ℂ F (ball 0 R) :=
    (hFH nl μ nn hn base U Bf gf Wf a₀ t e₀ hU hdat hgr hg0 h0 ha ht he (hec.trans k1) (htc.trans k1) hCEf
      l hl ρ x hx q0 q1).1
  -- the real points
  have hFV : ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lie) → ‖a‖ < R → F a ∈ G.lie := fun a hal haR => by
    obtain ⟨Bt, hW, hb⟩ := hBt a haR
    have hb' := hsmall Bt hb
    rw [hFval a Bt hW hb']
    have hmem : expU (Complex.I • Bt) ∈ G.carrier := by
      have h1 := hWG a hal haR l hl ρ x hx q0 q1
      rw [hW] at h1
      have := G.carrier.mul_mem h1 (G.carrier.inv_mem (hUG l ρ (img h (base l) l x)))
      rwa [mul_inv_cancel_right] at this
    have hn8 : ‖Complex.I • Bt‖ ≤ rl / 8 := by rw [norm_I_smul']; exact hb'
    have hcl : ‖((expU (Complex.I • Bt) : GLN) : Mat) - 1‖ ≤ 2 * (rl / 8) := by
      rw [expU_val]
      exact (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Bt)).trans
        (exp_sub_one_le_two_mul (norm_nonneg _) hn8 (by linarith))
    have := (hlog _ hmem (2 * (rl / 8)) hcl (by linarith)).1
    rwa [order_iv rfl (by linarith)] at this
  set e : ((Fin 4 × Site (nn 0)) → Mat) →L[ℂ] (Fin 4 → Site (nn 0) → Mat) :=
    ContinuousLinearMap.pi fun ρ' => ContinuousLinearMap.pi fun z => ContinuousLinearMap.proj (ρ', z) with he_def
  have he_apply : ∀ (Z : (Fin 4 × Site (nn 0)) → Mat) ρ' z, e Z ρ' z = Z (ρ', z) := fun Z ρ' z => rfl
  set D : Set ((Fin 4 × Site (nn 0)) → Mat) := e ⁻¹' ball 0 R with hD
  have hDo : IsOpen D := isOpen_ball.preimage e.continuous
  have hDc : Convex ℝ D := (convex_ball (0 : Fin 4 → Site (nn 0) → Mat) R).linear_preimage
    (e.toLinearMap.restrictScalars ℝ)
  set V : Set ((Fin 4 × Site (nn 0)) → Mat) := {Z | Z ∈ D ∧ ∀ i, Z i ∈ G.lie} with hV
  have hFe : DifferentiableOn ℂ (F ∘ e) D := hFd.comp e.differentiableOn fun Z hZ => hZ
  have hR0 : 0 < R := by positivity
  have h0D : (0 : (Fin 4 × Site (nn 0)) → Mat) ∈ D := by simp [hD, hR0]
  have key := RealPoints.real_points_ii G hG hDo hDc (V := V) (fun Z hZ => hZ.1) (fun Z hZ => hZ.2)
    (fun Z₀ hZ₀ => by
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo Z₀ hZ₀.1
      exact ⟨ε, hε, fun Z hZl hZd => ⟨hball (by rw [mem_ball, dist_eq_norm]; exact hZd), hZl⟩⟩)
    ⟨0, h0D, fun i => G.zero_mem_lie⟩ hFe
    (fun Z hZ => hFV (e Z) (fun ρ' z => by rw [he_apply]; exact hZ.2 (ρ', z)) (by
      have := hZ.1; simpa [hD] using this))
  intro a haC haR
  obtain ⟨Bt, hBe, hb⟩ := hBt a haR
  refine ⟨Bt, ?_, hBe, hb⟩
  rw [← hFval a Bt hBe (hsmall Bt hb)]
  have hZ : e (fun i => a i.1 i.2) = a := rfl
  have hZD : (fun i : Fin 4 × Site (nn 0) => a i.1 i.2) ∈ D := by
    simp only [hD, Set.mem_preimage, hZ, mem_ball_zero_iff]; exact haR
  have := key _ hZD fun i => haC i.1 i.2
  simpa [Function.comp, hZ] using this

set_option maxHeartbeats 4000000 in
/-- **`lem:block-average-transports`, `W(y, x) ∈ G^c` from the data on `T^{(i)}`**: under the hypotheses of `fluct_lieC`
and `G ⊂ G^c`, for a form `a` with values in `𝔤^c` and `‖a‖ < tL^{-n}`, the composite transports `W(y, x)` of the levels
`W(a)_l = M^l(e^{ia}U)` lie in `G^c`. The fluctuations `A'_l = (1/i) Log(W(a)_lU_l⁻¹)` lie in `𝔤^c` on the regions
(`fluct_lieC`), with the bounds of `background_levels`, and `block_transports_mem_Gc_region` applies. -/
theorem block_transports_mem_Gc_data (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (Bf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Fin 4 → Site (nn l) → Mat)
      (gf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Site (nn l) → GLN)
      (Wf : (Fin 4 → Site (nn 0) → Mat) → ∀ l, Config N (nn l)) (a₀ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        ∀ a, Wf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (Wf a l) (img h (base l) l x) ρ h ∧
          Bf a (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (Bf a l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x → ∀ a,
        gf a (l + 1) (img h (base (l + 1)) (l + 1) x) =
          gf a l (img h (base l) l x) * siteFactor (U l) (Bf a l) (img h (base l) l x) h) →
      (∀ a z, gf a 0 z = 1) →
      (∀ a ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        Wf a 0 ρ (img h (base 0) 0 x) = moveC (U 0) (Bf a 0) ρ (img h (base 0) 0 x) ∧
        Bf a 0 ρ (img h (base 0) 0 x) = a ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 < t → 0 ≤ e₀ → e₀ ≤ c → t ≤ c → C * (e₀ + 2 * t) ≤ 1 →
      (∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lie) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
        ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
          Wf a l ρ (img h (base l) l x) ∈ G.carrier) →
      G.carrier ≤ G.complexified →
      ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lieC) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ p : Fin l → Pts h,
        WB h nn base (Wf a) l y p ∈ G.complexified := by
  obtain ⟨cL, CL, C₁L, hcL, hCL, hC₁L, hFL⟩ := fluct_lieC G hG h hh
  obtain ⟨cW, hcW, hW⟩ := block_transports_mem_Gc_region G hG (GaugeGroup.lieInput_of_isClosed hG) h
  set K : ℝ := 8 * (h : ℝ) * (4 * C₁L + 4) with hK
  have hK0 : 0 ≤ K := by positivity
  set c := min cL (min cW (min (cW / (K + 1)) (1 / (4 * (4 * C₁L + 4))))) with hc_def
  have k1 : c ≤ cL := min_le_left _ _
  have k2 : c ≤ cW := (min_le_right _ _).trans (min_le_left _ _)
  have k3 : c ≤ cW / (K + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ 1 / (4 * (4 * C₁L + 4)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc0 : 0 < c := lt_min hcL (lt_min hcW (lt_min (by positivity) (by positivity)))
  refine ⟨c, CL, hc0, hCL, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he hec htc hCE hWG hGc a haC haR
  have hF := hFL nl μ nn hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he (hec.trans k1) (htc.trans k1) hCE hWG
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  have hl2 := Real.log_two_gt_d9
  have hsm : (4 * C₁L + 4) * t ≤ 1 / 4 := by
    calc (4 * C₁L + 4) * t ≤ (4 * C₁L + 4) * (1 / (4 * (4 * C₁L + 4))) := by gcongr; linarith
      _ = 1 / 4 := by field_simp
  set a₁ : ℕ → ℝ := fun l => (4 * C₁L + 4) * t * (Lr ^ (nl - l))⁻¹ with ha₁
  have ha₁s : ∀ l, a₁ l ≤ 1 / 4 := fun l => by
    have : (4 * C₁L + 4) * t * (Lr ^ (nl - l))⁻¹ ≤ (4 * C₁L + 4) * t :=
      mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
    simp only [ha₁]; linarith
  set A' : ∀ l, Fin 4 → Site (nn l) → Mat := fun l ν z =>
    (1 / Complex.I) • LogM (((Wf a l ν z * (U l ν z)⁻¹ : GLN) : Mat)) with hA'
  -- the fluctuations on the regions
  have hval : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      A' l ν (img h (base l) l x) ∈ G.lieC ∧
      Wf a l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
      ‖A' l ν (img h (base l) l x)‖ ≤ a₁ l := fun l hl ν x hx q0 q1 => by
    obtain ⟨B, hBC, hBe, hBn⟩ := hF l hl ν x hx q0 q1 a haC haR
    have hBv : A' l ν (img h (base l) l x) = B := by
      simp only [hA']
      rw [hBe, mul_inv_cancel_right]
      exact order_iv rfl (by have := ha₁s l; simp only [ha₁] at this; linarith)
    refine ⟨hBv ▸ hBC, ?_, hBv ▸ hBn⟩
    rw [hBe]; simp only [moveC, hBv]
  refine hW nl μ nn hn base U (Wf a) A' a₀ a₁ hUG
    (fun l hl ν x hx q0 q1 => (hval l hl.le ν x hx q0 q1).2.1)
    (fun l hl ρ x hx q0 q1 => ⟨(hdat l hl ρ x hx q0 q1).1, fun ν z hb => by
      obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hval l hl.le ν x'' hx'' s0 s1).2.2⟩)
    (fun l hl => by
      obtain ⟨h1, h2⟩ := ha l hl
      have h3 : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := mul_le_of_le_one_right he (hp1 (nl - l))
      have h4 : 0 ≤ a₁ l := by simp only [ha₁]; positivity
      refine ⟨h1, h4, by linarith [hec.trans k2], ?_⟩
      have h5 : a₁ l ≤ (4 * C₁L + 4) * t := by
        simp only [ha₁]; exact mul_le_of_le_one_right (by positivity) (hp1 (nl - l))
      have h6 : K * t ≤ cW := by
        calc K * t ≤ K * (cW / (K + 1)) := mul_le_mul_of_nonneg_left (htc.trans k3) hK0
          _ ≤ cW := by
              rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
      calc 8 * (h : ℝ) * a₁ l ≤ 8 * (h : ℝ) * ((4 * C₁L + 4) * t) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = K * t := by rw [hK]; ring
        _ ≤ cW := h6)
    (fun l hl ν x hx q0 q1 => (hval l hl.le ν x hx q0 q1).1) hGc

end RelativeAverage
end CoreLean

end
