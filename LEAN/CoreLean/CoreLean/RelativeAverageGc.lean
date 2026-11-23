/-
`lem:block-average-transports` of BALABAN_CORE.tex (`fe7d249fe3af`): `W(y, x) ∈ G^c`.

* `trans_moveC_mem_Gc`: for a `G`-valued `U` whose quotients `U(Γᵢ)U(Γ₀)⁻¹` of the paths of `𝐆(y, x)` are within
  `r` of `id`, and a form `B` with values in `𝔤^c` with `8h‖B‖ ≤ c`, the transport `𝐔_B(y, x)` of `𝐔_B = e^{iB}U` lies in
  `G^c` (if `G ⊂ G^c`). The quotients of `𝐔_B` are `e^{iZ}e^{iX}` with `Z ∈ 𝔤^c` (the moved exponentials) and `X ∈ 𝔤`
  (the chart of `G`), so their logarithms are `iΨ(Z, X)` with `Ψ(Z, X) ∈ 𝔤^c`; the mean of these exponents lies in
  `𝔤^c` by `group_mean_lieC`, and `𝐔_B(Γ₀)` is a product of `e^{iY}`, `Y ∈ 𝔤^c`, and an element of `G`.
-/
import CoreLean.RelativeAverageKernels

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

lemma length_stairG {n : ℕ} [NeZero n] (h : ℕ) (w : Site n) (x : Pts h) (Γ : Ords (offP h x)) :
    (stair w (offP h x) (ordG h x Γ) 0).length ≤ 4 * h := by
  rw [length_stair, ((ordG_perm h x Γ).map _).sum_eq]
  have := offP_inM h x
  have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The quotient of two paths of `𝐆(y, x)` is the value on a closed path of at most `8h` bonds. -/
lemma quotG_eq_hol {n : ℕ} [NeZero n] (y : Site n) (h : ℕ) (x : Pts h) (i : Fin (nG h x)) :
    ∃ γ : List (Bond n), γ.length ≤ 8 * h ∧ ∀ V' : Config N n, quotG V' y h x i = V'.hol γ := by
  refine ⟨stair y (offP h x) (ordG h x (enumG h x i)) 0 ++ rv (stair y (offP h x) (ordG h x (firstG h x)) 0),
    ?_, fun V' => ?_⟩
  · rw [List.length_append, length_rv]
    have := length_stairG h y x (enumG h x i)
    have := length_stairG h y x (firstG h x)
    omega
  · rw [quotG, hol_append, rv, Transports.hol_rev]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The transports of `𝐔_B` lie in `G^c`**: there are `r, c > 0`, depending on `G` only, such that for a `G`-valued
`U` whose quotients of the paths of `𝐆(y, x)` are within `r` of `id` and a form `B` with values in `𝔤^c` with
`8h‖B‖ ≤ c`, the transport `𝐔_B(y, x)` lies in `G^c`, provided `G ⊂ G^c`. -/
theorem trans_moveC_mem_Gc (G : GaugeGroup N) (hG : IsClosed G.mats) (hGl : G.LieInput) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → ∀ (y : Site n) (h : ℕ)
      (x : Pts h) (B : Fin 4 → Site n → Mat), (∀ ρ z, B ρ z ∈ G.lieC) → 8 * (h : ℝ) * ‖B‖ ≤ c →
      (∀ i, ‖((quotG U y h x i : GLN) : Mat) - 1‖ ≤ r) → G.carrier ≤ G.complexified →
      trans (moveC U B) y h x ∈ G.complexified := by
  obtain ⟨r, hr0, hr1, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  set r₀ : ℝ := min r (1 / 4096) with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr0 (by norm_num)
  have hr₀r : r₀ ≤ r := min_le_left _ _
  have hr₀s : r₀ ≤ 1 / 4096 := min_le_right _ _
  refine ⟨r₀, 1 / 8192, hr₀0, by norm_num, ?_⟩
  intro n _ U hU y h x B hBC hB hq hGc
  have hpi := Real.pi_lt_d2
  have hl2 := Real.log_two_gt_d9
  have hBn := norm_nonneg B
  -- the exponents of the quotients of `𝐔_B`
  have hexp : ∀ i, expsG (moveC U B) y h x i ∈ G.lieC ∧ ‖expsG (moveC U B) y h x i‖ ≤ 1 / 512 := by
    intro i
    obtain ⟨γ, hγ, hγq⟩ := quotG_eq_hol (N := N) y h x i
    obtain ⟨l, hl, hln, hlC, he⟩ := hol_decomp hU B γ
    have hlB : (l.length : ℝ) * ‖B‖ ≤ 1 / 8192 := by
      have : (l.length : ℝ) ≤ 8 * h := by rw [hl]; exact_mod_cast hγ
      nlinarith
    have h512 : 512 * l.length * ‖B‖ ≤ 1 := by nlinarith
    obtain ⟨ZE, hZEC, hZEe, hZEn⟩ := exists_exp_prod_lieC hGl l hBn hln (hlC hBC) h512
    have hZE : ‖ZE‖ ≤ 1 / 4096 := by nlinarith
    obtain ⟨X, hX, hXn, hXe, -, -⟩ := hch _ (hU.hol_mem γ) (by rw [← hγq U]; exact (hq i).trans hr₀r)
    have hX3 := (ChartBounds.chart_iii hX.1 hXn.le).2.1
    rw [hXe, ← hγq U] at hX3
    have hXs : ‖X‖ ≤ 2 * (1 / 4096) := by
      have := hX3.trans (mul_le_mul_of_nonneg_left ((hq i).trans hr₀s) (by positivity))
      nlinarith
    have hUX : U.hol γ = expU (Complex.I • X) := Units.ext (by rw [expU_val]; exact hXe.symm)
    have hW : quotG (moveC U B) y h x i = expU (Complex.I • psi ZE X) := by
      rw [hγq, he, ← hZEe, hUX, LatticeKappa.expU_mul_expU (by linarith)]
    have hpsi : ‖psi ZE X‖ ≤ 1 / 512 := by
      have := LatticeKappa.norm_psi_le' (A := ZE) (B := X) (by linarith) (by linarith)
      nlinarith [norm_nonneg ZE, norm_nonneg X]
    have hval : expsG (moveC U B) y h x i = psi ZE X := by
      rw [expsG, ← quotG, hW, expU_val, LogM_exp (by rw [norm_I_smul']; linarith), smul_smul,
        one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    rw [hval]
    exact ⟨psi_mem hGl hZEC (lie_subset_lieC' hX) (by linarith), hpsi⟩
  -- the mean of the exponents lies in `𝔤^c`
  have hn : 0 < nG h x := card_ords_pos _
  obtain ⟨Z, hZC, hZn, hZs⟩ := GroupMean.group_mean_lieC G hGl hn (expsG (moveC U B) y h x) (1 / 512)
    (fun i => (hexp i).2) (by norm_num) (fun i => (hexp i).1)
  have hZm : Z = meanV (expsG (moveC U B) y h x) :=
    meanV_unique hn (fun i => (hexp i).2) (by linarith) hZs
  -- the transport
  unfold trans mean
  rw [← hZm]
  refine G.complexified.mul_mem (Subgroup.subset_closure ⟨_, hZC, rfl⟩) ?_
  obtain ⟨l, -, -, hlC, he⟩ := hol_decomp hU B (stair y (offP h x) (ordG h x (firstG h x)) 0)
  rw [holG, he]
  refine G.complexified.mul_mem (G.complexified.list_prod_mem fun g hg => ?_) (hGc (hU.hol_mem _))
  simp only [List.mem_map] at hg
  obtain ⟨Y, hY, rfl⟩ := hg
  exact Subgroup.subset_closure ⟨Y, hlC hBC Y hY, rfl⟩

/-- **The quotients of a gauge field with small plaquettes are small**: for every `ρ > 0` there is `c > 0`, depending on
`L` and `ρ` only, such that the quotients of the paths of `𝐆(c_±, x)` of a gauge field whose plaquettes on the blocks
of the bond are at most `α₀ ≤ c` are within `ρ` of `id`. The quotients are conjugate by the axial gauge to those of
`e^{iX}`, `X` small (as in `trans_mem_G`). -/
theorem quotG_small {ρ : ℝ} (hρ : 0 < ρ) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ (b : Bool) (x : Pts h) (i : Fin (nG h x)),
          ‖((quotG U (ofs y (endW h μ b)) h x i : GLN) : Mat) - 1‖ ≤ ρ := by
  obtain ⟨cq, hcq, hcondG⟩ := uniform_condG (N := N) hρ h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (cq / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ cq / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro n _ U hUg hn y α₀ hα₀ hα₀c hplq b x i
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ (0 : ℝ) := fun ρ z _ => by simp
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hUg hn y μ hα₀ le_rfl hα₀c (by positivity : (0 : ℝ) ≤ c)
    hc2 hplq 0 hA0
  rw [moveC_zero] at hag
  have hKc : K * c ≤ cq / 2 := by
    calc K * c ≤ K * (cq / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = cq / 2 := by field_simp
  have hcg := hcondG y X 0 (by linarith) (by rw [norm_zero]; exact hcq)
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hUg _
  set z₀ := ofs y (endW h μ b)
  have hloc : ∀ x' Γ, holG (U.gauge u) z₀ h x' Γ = holG (UX (N := N) X) z₀ h x' Γ :=
    holG_local hn2 fun ν z h1 h2 => hag ν z (boxBond_of_end hn2 b h1 h2)
  have e : quotG (U.gauge u) z₀ h x i = u z₀ * quotG U z₀ h x i * (u z₀)⁻¹ := by
    simp only [quotG, holG_gauge]; group
  have hq : ‖((quotG U z₀ h x i : GLN) : Mat) - 1‖ = ‖((quotG (UX (N := N) X) z₀ h x i : GLN) : Mat) - 1‖ := by
    rw [← norm_Ad_sub_one (hu z₀), ← e]
    simp only [quotG, hloc]
  rw [hq]
  cases b
  · have := hcg.q0 x i
    simpa only [z₀, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using this
  · exact hcg.q1 x i

/-- **`lem:block-average-transports`, `W(y, x) ∈ G^c`**: under the hypotheses of `block_transports_bound` (the fields
`V_l = e^{ia A'_l}U_l` on the regions, `U_l` with values in `G`, the plaquettes of `U_l` at most `a₀ l ≤ c` and
`‖A'_l‖ ≤ a₁ l` on the boxes of the bonds), with `A'_l` taking values in `𝔤^c` and `8h a₁ l ≤ c`, the composite
transports `W(y, x)` lie in `G^c`, provided `G ⊂ G^c`; `c` depends on `L` and `G` only. -/
theorem block_transports_mem_Gc (G : GaugeGroup N) (hG : IsClosed G.mats) (hGl : G.LieInput) (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ 8 * (h : ℝ) * a₁ l ≤ c) →
      (∀ l ν z, A' l ν z ∈ G.lieC) → G.carrier ≤ G.complexified →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ p : Fin l → Pts h,
        WB h nn base V l y p ∈ G.complexified := by
  classical
  obtain ⟨r, cB, hr, hcB, hmem⟩ := trans_moveC_mem_Gc G hG hGl
  choose cq hcq hqs using fun ρ : Fin 4 => quotG_small (N := N) hr h ρ
  set c := min (Finset.univ.inf' Finset.univ_nonempty cq) cB
  have hcq' : ∀ ρ, c ≤ cq ρ := fun ρ => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hcB' : c ≤ cB := min_le_right _ _
  refine ⟨c, lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => hcq ρ) hcB, ?_⟩
  intro nl μ nn _ hn base U V A' a₀ a₁ hUG hVU hdat ha hAC hGc l
  induction l with
  | zero => intro _ y _ _ p; simp only [WB]; exact one_mem _
  | succ l ih =>
    intro hl y hy hR p
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hy hR
    obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
    set z₀ := ofs (img h (base l) l x') (endW h μ b)
    have ht : ∀ xx, trans (V l) z₀ h xx = trans (moveC (U l) (A' l)) z₀ h xx :=
      trans_local hn2 fun ν z h1 h2 => by
        obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
        exact hVU l hll ν x'' hx'' s0 s1
    have hres : ∀ xx, trans (moveC (U l) (A' l)) z₀ h xx =
        trans (moveC (U l) (restrictF (A' l) (Bm z₀ h))) z₀ h xx :=
      trans_local hn2 fun ν z hz hz' => by simp [moveC, restrictF, hz, hz']
    have hnorm : ‖restrictF (A' l) (Bm z₀ h)‖ ≤ a₁ l :=
      norm_restrictF_le_of ha1 fun ν z hz hz' => hA ν z (boxBond_of_end hn2 b hz hz')
    have hC : ∀ ν z, restrictF (A' l) (Bm z₀ h) ν z ∈ G.lieC := fun ν z => by
      simp only [restrictF]
      split_ifs
      · exact hAC l ν z
      · exact lie_subset_lieC' G.zero_mem_lie
    have hh0 : (0 : ℝ) ≤ 8 * h := by positivity
    have hstep : trans (moveC (U l) (A' l)) z₀ h (p 0) ∈ G.complexified := by
      rw [hres]
      refine hmem (U l) (hUG l) z₀ h (p 0) _ hC ?_ ?_ hGc
      · calc 8 * (h : ℝ) * ‖restrictF (A' l) (Bm z₀ h)‖ ≤ 8 * h * a₁ l := mul_le_mul_of_nonneg_left hnorm hh0
          _ ≤ cB := ha1c.trans hcB'
      · exact hqs μ (U l) (hUG l).gauge (hn l) (img h (base l) l x') (a₀ l) ha0 (ha0c.trans (hcq' μ)) hpl b (p 0)
    have hWdef : WB h nn base V (l + 1) y p =
        trans (moveC (U l) (A' l)) z₀ h (p 0) * WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p) := by
      simp only [WB, hb, ht]
    rw [hWdef]
    exact G.complexified.mul_mem hstep (ih hll.le (y + Lz h ^ l • offP h (p 0)) (lat_add_smul (lat_succ_le hy) _)
      (rg_site hR (p 0)) (Fin.tail p))


/-- **`W(y, x) ∈ G^c` with the values of `A'_l` in `𝔤^c` on the regions only** (the form in which `fluct_lieC` gives them); otherwise as `block_transports_mem_Gc`.

: under the hypotheses of `block_transports_bound` (the fields
`V_l = e^{ia A'_l}U_l` on the regions, `U_l` with values in `G`, the plaquettes of `U_l` at most `a₀ l ≤ c` and
`‖A'_l‖ ≤ a₁ l` on the boxes of the bonds), with `A'_l` taking values in `𝔤^c` and `8h a₁ l ≤ c`, the composite
transports `W(y, x)` lie in `G^c`, provided `G ⊂ G^c`; `c` depends on `L` and `G` only. -/
theorem block_transports_mem_Gc_region (G : GaugeGroup N) (hG : IsClosed G.mats) (hGl : G.LieInput) (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ 8 * (h : ℝ) * a₁ l ≤ c) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        A' l ν (img h (base l) l x) ∈ G.lieC) → G.carrier ≤ G.complexified →
      ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y → ∀ p : Fin l → Pts h,
        WB h nn base V l y p ∈ G.complexified := by
  classical
  obtain ⟨r, cB, hr, hcB, hmem⟩ := trans_moveC_mem_Gc G hG hGl
  choose cq hcq hqs using fun ρ : Fin 4 => quotG_small (N := N) hr h ρ
  set c := min (Finset.univ.inf' Finset.univ_nonempty cq) cB
  have hcq' : ∀ ρ, c ≤ cq ρ := fun ρ => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hcB' : c ≤ cB := min_le_right _ _
  refine ⟨c, lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => hcq ρ) hcB, ?_⟩
  intro nl μ nn _ hn base U V A' a₀ a₁ hUG hVU hdat ha hAC hGc l
  induction l with
  | zero => intro _ y _ _ p; simp only [WB]; exact one_mem _
  | succ l ih =>
    intro hl y hy hR p
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hy hR
    obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
    set z₀ := ofs (img h (base l) l x') (endW h μ b)
    have ht : ∀ xx, trans (V l) z₀ h xx = trans (moveC (U l) (A' l)) z₀ h xx :=
      trans_local hn2 fun ν z h1 h2 => by
        obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
        exact hVU l hll ν x'' hx'' s0 s1
    have hres : ∀ xx, trans (moveC (U l) (A' l)) z₀ h xx =
        trans (moveC (U l) (restrictF (A' l) (Bm z₀ h))) z₀ h xx :=
      trans_local hn2 fun ν z hz hz' => by simp [moveC, restrictF, hz, hz']
    have hnorm : ‖restrictF (A' l) (Bm z₀ h)‖ ≤ a₁ l :=
      norm_restrictF_le_of ha1 fun ν z hz hz' => hA ν z (boxBond_of_end hn2 b hz hz')
    have hC : ∀ ν z, restrictF (A' l) (Bm z₀ h) ν z ∈ G.lieC := fun ν z => by
      simp only [restrictF]
      split_ifs with hz
      · obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b hz.1 hz.2)
        exact hAC l hll ν x'' hx'' s0 s1
      · exact lie_subset_lieC' G.zero_mem_lie
    have hh0 : (0 : ℝ) ≤ 8 * h := by positivity
    have hstep : trans (moveC (U l) (A' l)) z₀ h (p 0) ∈ G.complexified := by
      rw [hres]
      refine hmem (U l) (hUG l) z₀ h (p 0) _ hC ?_ ?_ hGc
      · calc 8 * (h : ℝ) * ‖restrictF (A' l) (Bm z₀ h)‖ ≤ 8 * h * a₁ l := mul_le_mul_of_nonneg_left hnorm hh0
          _ ≤ cB := ha1c.trans hcB'
      · exact hqs μ (U l) (hUG l).gauge (hn l) (img h (base l) l x') (a₀ l) ha0 (ha0c.trans (hcq' μ)) hpl b (p 0)
    have hWdef : WB h nn base V (l + 1) y p =
        trans (moveC (U l) (A' l)) z₀ h (p 0) * WB h nn base V l (y + Lz h ^ l • offP h (p 0)) (Fin.tail p) := by
      simp only [WB, hb, ht]
    rw [hWdef]
    exact G.complexified.mul_mem hstep (ih hll.le (y + Lz h ^ l • offP h (p 0)) (lat_add_smul (lat_succ_le hy) _)
      (rg_site hR (p 0)) (Fin.tail p))

end RelativeAverage
end CoreLean

end
