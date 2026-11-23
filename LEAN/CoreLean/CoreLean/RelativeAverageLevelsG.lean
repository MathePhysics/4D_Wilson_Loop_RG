/-
`lem:average`(i) on the levels of BALABAN_CORE.tex (`7374c382ba1b`): the averages of gauge fields are gauge fields, for the
levels `W(a)_l = M^l(e^{ia}U)` of a real form `a`.

* `levels_real_G`: under the hypotheses of `background_lip`, with `U_l` taking values in `G`, the levels `W(a)_l` of a form
  `a` with values in `𝔤` take values in `G` on the regions. On the box of a bond `W(a)_l = e^{iB}U_l` with `B` small
  (`background_levels`) and in `𝔤` (by induction and `log_mem_lie`); the loops of `U_l` are close to `id`
  (`loop_close`); so the average is the average with the chart of `G` (`average_analytic`(3)), an element of `G` (`avg_mem`).
-/
import CoreLean.RelativeAverageLevelsLieC
import CoreLean.BlockHolonomiesII

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

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The real levels are gauge fields** (`lem:average`(i) on the levels): under the hypotheses of `background_lip`, with
`U_l` taking values in `G`, for a form `a` with values in `𝔤` and `‖a‖ < tL^{-n}` the levels `W(a)_l` take values in `G`
on the bonds of the regions. -/
theorem levels_real_G (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
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
      ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lie) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        Wf a l ρ (img h (base l) l x) ∈ G.carrier := by
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  obtain ⟨rl, hrl, hrl4, hlog⟩ := log_mem_lie G hG
  obtain ⟨c₀, hc₀, han⟩ := average_analytic G hG
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL1 : (1 : ℝ) ≤ Lr := by rw [hLr]; exact_mod_cast (by omega : 1 ≤ 2 * h + 1)
  set K := 4 * C₁b + 4 with hK
  have hK0 : 0 < K := by positivity
  set c := min (cb / 4) (min (1 / (1024 * (2 * C₁b + 2))) (min (rl / (8 * K))
    (min (c₀ / (2 * Lr * K)) (c₀ / (Real.sqrt N * (4 * Lr ^ 2) + 1))))) with hc_def
  have k1 : c ≤ cb / 4 := min_le_left _ _
  have k2 : c ≤ 1 / (1024 * (2 * C₁b + 2)) := (min_le_right _ _).trans (min_le_left _ _)
  have k3 : c ≤ rl / (8 * K) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ c₀ / (2 * Lr * K) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have k5 : c ≤ c₀ / (Real.sqrt N * (4 * Lr ^ 2) + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc0 : 0 < c := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  refine ⟨c, Cb, hc0, hCb, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he hec htc hCE a hal haR
  have hU : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hC₁bt : (2 * C₁b + 2) * t ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hKt : K * t ≤ rl / 8 := by
    calc K * t ≤ K * (rl / (8 * K)) := by gcongr; linarith
      _ = rl / 8 := by field_simp
  have hKtL : K * t < c₀ / Lr := by
    calc K * t ≤ K * (c₀ / (2 * Lr * K)) := by gcongr; linarith
      _ = c₀ / Lr / 2 := by field_simp
      _ < c₀ / Lr := by
          have : 0 < c₀ / Lr := by positivity
          linarith
  have hB0 : ∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
      ‖Bf a 0 ν (img h (base 0) 0 x)‖ ≤ t * (Lr ^ nl)⁻¹ := fun ν x hx q0 q1 => by
    rw [(h0 a ν x hx q0 q1).2]
    exact ((norm_le_pi_norm (a ν) _).trans (norm_le_pi_norm a ν)).trans haR.le
  -- the decomposition of the levels
  have hBt := hBL nl μ nn hn base U (Wf a) (Bf a) (gf a) a₀ t e₀ hU
    (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.1)
    (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).1) (fun ρ x hx q0 q1 => (h0 a ρ x hx q0 q1).1)
    (fun l hl ρ x hx q0 q1 => ((hdat l hl ρ x hx q0 q1).2.2 a).2) (fun l hl x hx q0 => hgr l hl x hx q0 a)
    (hg0 a) ha ht.le he (hec.trans (k1.trans (by linarith))) (by linarith) hCE hC₁bt hB0
  have hsmall : ∀ l, ∀ Bt : Mat, ‖Bt‖ ≤ K * t * (Lr ^ (nl - l))⁻¹ → ‖Bt‖ ≤ K * t := fun l Bt hb =>
    hb.trans (mul_le_of_le_one_right (by positivity) (hp1 _))
  intro l
  induction l with
  | zero =>
    intro _ ρ x hx q0 q1
    rw [(h0 a ρ x hx q0 q1).1]
    show expU (Complex.I • Bf a 0 ρ (img h (base 0) 0 x)) * U 0 ρ (img h (base 0) 0 x) ∈ G.carrier
    rw [(h0 a ρ x hx q0 q1).2]
    exact G.carrier.mul_mem (exp_mem_of_lie G (hal _ _)) (hUG 0 _ _)
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨hpl, -, hrec⟩ := hdat l hll ρ x hx q0 q1
    rw [(hrec a).1]
    set y := img h (base l) l x
    -- the fluctuation on the box
    set F : Fin 4 → Site (nn l) → Mat := fun ν z => (1 / Complex.I) • LogM (((Wf a l ν z * (U l ν z)⁻¹ : GLN) : Mat))
      with hF
    set B := restrictF F (InBoxB y h ρ) with hB
    have hbox : ∀ ν z, BoxBond y h ρ ν z →
        F ν z ∈ G.lie ∧ ‖F ν z‖ ≤ K * t ∧ Wf a l ν z = expU (Complex.I • F ν z) * U l ν z := fun ν z hb => by
      obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      obtain ⟨Bt, hW, hbt⟩ := hBt l hll.le ν x'' hx'' s0 s1
      have hbt' := hsmall l Bt hbt
      have hl2 := Real.log_two_gt_d9
      have hFv : F ν (img h (base l) l x'') = Bt := by
        simp only [hF]; rw [hW, mul_inv_cancel_right]; exact order_iv rfl (by linarith)
      have hmem : expU (Complex.I • Bt) ∈ G.carrier := by
        have h1 := ih hll.le ν x'' hx'' s0 s1
        rw [hW] at h1
        have := G.carrier.mul_mem h1 (G.carrier.inv_mem (hUG l ν (img h (base l) l x'')))
        rwa [mul_inv_cancel_right] at this
      have hn8 : ‖Complex.I • Bt‖ ≤ rl / 8 := by rw [norm_I_smul']; linarith
      have hcl : ‖((expU (Complex.I • Bt) : GLN) : Mat) - 1‖ ≤ 2 * (rl / 8) := by
        rw [expU_val]
        exact (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Bt)).trans
          (exp_sub_one_le_two_mul (norm_nonneg _) hn8 (by linarith))
      have hBl := (hlog _ hmem (2 * (rl / 8)) hcl (by linarith)).1
      rw [order_iv rfl (by linarith)] at hBl
      rw [hFv]
      exact ⟨hBl, hbt', hW⟩
    have hBlie : ∀ ν z, B ν z ∈ G.lie := fun ν z => by
      by_cases hb : BoxBond y h ρ ν z
      · rw [hB, restrictF_box_apply _ hb]; exact (hbox ν z hb).1
      · rw [hB, restrictF_box_apply' _ hb]; exact G.zero_mem_lie
    have hBn : ‖B‖ < c₀ / Lr :=
      lt_of_le_of_lt (norm_restrictF_box_le (by positivity) fun ν z hb => (hbox ν z hb).2.1) hKtL
    -- the average sees the box only
    have hloc : avgM (Wf a l) y ρ h = avgM (moveC (U l) B) y ρ h :=
      avgM_local hn2 fun ν z h1 h2 => by
        have hb : BoxBond y h ρ ν z := ⟨h1, h2⟩
        rw [(hbox ν z hb).2.2]
        simp only [moveC, hB, restrictF_box_apply _ hb]
    rw [hloc]
    -- the loops of `U_l`
    have hPl : BlockHolonomies.PlaqBoundHS (U l)
        (BlockHolonomies.RegB y h ∪ BlockHolonomies.RegB (ofs y (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ))) h) (a₀ l) := by
      intro μ' ν' z hz
      refine hpl μ' ν' z ?_
      have conv : ∀ p, p ∈ BlockHolonomies.RegB y h ∪ BlockHolonomies.RegB (ofs y (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ))) h →
          p ∈ boxR y (loD h) (hiD h ρ ρ) := fun p hp => by
        rcases hp with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
        · refine ⟨v, fun σ => ?_, rfl⟩
          have := hv σ
          simp only [loD, hiD]
          split_ifs <;> constructor <;> omega
        · refine ⟨Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) + w, fun σ => ?_, by rw [ofs_ofs]⟩
          have := hw σ
          simp only [loD, hiD, Pi.add_apply, Pi.single_apply]
          by_cases hσ : σ = ρ
          · subst hσ; simp only [if_true, or_self]; push_cast; constructor <;> omega
          · simp only [if_neg hσ, or_self, zero_add]; constructor <;> omega
      obtain ⟨h1, h2, h3, h4⟩ := hz
      exact ⟨conv _ h1, conv _ h2, conv _ h3, conv _ h4⟩
    obtain ⟨ha0, ha0e⟩ := ha l hll
    have ha0c : a₀ l ≤ c := by
      have : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := mul_le_of_le_one_right he (hp1 _)
      linarith
    have hloops : ∀ x' Γ Γ', ‖(((U l).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y ρ (2 * h + 1)
        (offP h) (ordG h) x' Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀ := fun x' Γ Γ' => by
      have hcl := (BlockHolonomies.loop_close (hU l) ha0 y ρ hPl x' Γ Γ').2
      refine hcl.trans ?_
      have e1 : Real.sqrt N * (4 * (2 * h + 1) ^ 2 * a₀ l) = (Real.sqrt N * (4 * Lr ^ 2)) * a₀ l := by
        rw [hLr]; push_cast; ring
      rw [e1]
      calc (Real.sqrt N * (4 * Lr ^ 2)) * a₀ l ≤ (Real.sqrt N * (4 * Lr ^ 2) + 1) * c :=
            mul_le_mul (by linarith) ha0c ha0 (by positivity)
        _ ≤ (Real.sqrt N * (4 * Lr ^ 2) + 1) * (c₀ / (Real.sqrt N * (4 * Lr ^ 2) + 1)) :=
            mul_le_mul_of_nonneg_left k5 (by positivity)
        _ = c₀ := by field_simp
    obtain ⟨-, -, havg, -⟩ := han (U l) (hUG l) h y ρ (offP h) (ordG h) (fun x => offP_inM h x)
      (fun x Γ => ordG_perm h x Γ) hloops
    have he' := havg B hBn hBlie
    show avgLogU (moveC (U l) B) y ρ (2 * h + 1) (offP h) (ordG h) ∈ G.carrier
    rw [← he']
    refine GaugeGroup.avg_mem hG _ _ _ _ ?_
    have hVG : IsGField G (moveC (U l) B) := fun ν z =>
      G.carrier.mul_mem (exp_mem_of_lie G (hBlie ν z)) (hUG l ν z)
    exact hVG.hol_mem _

set_option maxHeartbeats 8000000 in
/-- **`lem:block-average-transports`, `W(y, x) ∈ G^c` from the data on `T^{(i)}`**, without a hypothesis on the levels of
the real forms: they take values in `G` by `levels_real_G`, and `block_transports_mem_Gc_data` applies. -/
theorem block_transports_mem_Gc_from_data (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
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
      G.carrier ≤ G.complexified →
      ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lieC) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ p : Fin l → Pts h,
        WB h nn base (Wf a) l y p ∈ G.complexified := by
  obtain ⟨cD, CD, hcD, hCD, hD⟩ := block_transports_mem_Gc_data G hG h hh
  obtain ⟨cR, CR, hcR, hCR, hR⟩ := levels_real_G G hG h hh
  refine ⟨min cD cR, max CD CR, lt_min hcD hcR, hCD.trans (le_max_left _ _), ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he hec htc hCE hGc a haC haR
  have hC1 : CD * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hC2 : CR * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  exact hD nl μ nn hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he (hec.trans (min_le_left _ _))
    (htc.trans (min_le_left _ _)) hC1
    (hR nl μ nn hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he (hec.trans (min_le_right _ _))
      (htc.trans (min_le_right _ _)) hC2) hGc a haC haR

set_option maxHeartbeats 8000000 in
/-- **The fluctuations of the levels lie in `𝔤^c`, from the data on `T^{(i)}`**: `fluct_lieC` without a hypothesis on the
levels of the real forms, which take values in `G` by `levels_real_G`. -/
theorem fluct_lieC_from_data (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (hh : 1 ≤ h) :
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
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      ∀ a : Fin 4 → Site (nn 0) → Mat, (∀ ρ z, a ρ z ∈ G.lieC) → ‖a‖ < t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ →
        ∃ A'l ∈ G.lieC, Wf a l ρ (img h (base l) l x) = expU (Complex.I • A'l) * U l ρ (img h (base l) l x) ∧
          ‖A'l‖ ≤ (4 * C₁ + 4) * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨cL, CL, C₁L, hcL, hCL, hC₁L, hL⟩ := fluct_lieC G hG h hh
  obtain ⟨cR, CR, hcR, hCR, hR⟩ := levels_real_G G hG h hh
  refine ⟨min cL cR, max CL CR, C₁L, lt_min hcL hcR, hCL.trans (le_max_left _ _), hC₁L, ?_⟩
  intro nl μ nn _ hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he hec htc hCE
  have hC1 : CL * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hC2 : CR * (e₀ + 2 * t) ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  exact hL nl μ nn hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he (hec.trans (min_le_left _ _))
    (htc.trans (min_le_left _ _)) hC1
    (hR nl μ nn hn base U Bf gf Wf a₀ t e₀ hUG hdat hgr hg0 h0 ha ht he (hec.trans (min_le_right _ _))
      (htc.trans (min_le_right _ _)) hC2)

end RelativeAverage
end CoreLean

end
