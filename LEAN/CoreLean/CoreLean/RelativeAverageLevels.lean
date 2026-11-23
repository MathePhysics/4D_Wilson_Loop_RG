/-
`prop:relative-average-order` of BALABAN_CORE.tex (`2514a72de890`): the per-level hypotheses.

The proof's paragraph "The gauge fields `U_l`": the plaquettes of `U_l = M^l(U)` with corners in
`B^{n-l}(c₋) ∪ B^{n-l}(c₊)` satisfy `|U_l(∂p) - id| ≤ 2α₀L^{-2(n-l)}`, by `prop:regular-averages`(ii) for the scales
`i < i + l` and the number `α₀L^{-2(n-l)}`, the blocks of order `l` of the corners of these plaquettes lying in
`Bⁿ(c₋) ∪ Bⁿ(c₊)`.

* `Hw_add`: `H(n, m) = H(n, l) + H(l, m)`; `img_img`: the sites of a sub-hierarchy based at a point of the level `l`.
* `rg_sub`: the regions of the sub-hierarchy of a plaquette of the level `l` with corners in the region lie in the
  regions of the bond.
* `plaq_levels`: the plaquette bound of the levels.
-/
import CoreLean.RelativeAverageOrder

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

/-- `H(n, m) = H(n, l) + H(l, m)`: `(Lⁿ - L^m)/2 = (Lⁿ - L^l)/2 + (L^l - L^m)/2`. -/
lemma Hw_add (h nl l m : ℕ) : Hw h nl m = Hw h nl l + Hw h l m := by
  have e1 := two_Hw h nl m
  have e2 := two_Hw h nl l
  have e3 := two_Hw h l m
  omega

/-- The sites of the sub-hierarchy based at the site of a point `x` of the level `l`: for `m ≤ l`,
`img (img x) x' = img (x + x')` on the torus of the level `m`. -/
lemma img_img {n : ℕ} [NeZero n] {h m : ℕ} (y : Site n) {x x' : Fin 4 → ℤ} (hx : Lat (Lz h) m x)
    (hx' : Lat (Lz h) m x') : img h (img h y m x) m x' = img h y m (x + x') := by
  conv_rhs => rw [qt_spec hx']
  rw [← img_add y hx]
  rfl

/-- The region of the level `m` of the sub-hierarchy of the plaquette `p_{μ'ν'}(x)` of the level `l`, whose corners
lie in the region of the level `l`, lies in the region of the level `m` of the bond. -/
lemma rg_sub {h nl l m : ℕ} {μ μ' ν' : Fin 4} (hlm : m ≤ l) (hl : l ≤ nl) {x x' : Fin 4 → ℤ}
    (h0 : Rg h nl μ l x) (h1 : Rg h nl μ l (x + Lz h ^ l • Pi.single μ' 1))
    (h2 : Rg h nl μ l (x + Lz h ^ l • Pi.single ν' 1)) (hx' : RegularAverages.InR h l μ' ν' m x') :
    Rg h nl μ m (x + x') := by
  have hadd := Hw_add h nl l m
  intro σ
  have a0 := h0 σ
  have b := hx' σ
  simp only [Pi.add_apply]
  rw [hadd]
  by_cases hσ : σ = μ' ∨ σ = ν'
  · simp only [hσ, ↓reduceIte] at b
    have hc : x σ + Lz h ^ l ≤ (if σ = μ ∨ σ = μ then Lz h ^ nl else 0) + Hw h nl l := by
      rcases hσ with rfl | rfl
      · have := (h1 σ).2
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] using this
      · have := (h2 σ).2
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] using this
    constructor <;> linarith [a0.1, b.1, b.2]
  · simp only [hσ, ↓reduceIte, zero_add] at b
    constructor <;> linarith [a0.1, a0.2, b.1, b.2]

/-- **The plaquettes of the levels** (the paragraph "The gauge fields `U_l`" of the proof): if `U_{l+1} = M(U_l)` on
the regions, with values in `G`, and the plaquettes of `U_0` with corners in the region satisfy
`|U_0(∂p) - id| ≤ α L^{-2n}`, `α ≤ c₂`, then the plaquettes of `U_l` with corners in the region of the level `l`
satisfy `|U_l(∂p) - id| ≤ 2α L^{-2(n-l)}`. -/
theorem plaq_levels (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (h : ℕ), 1 ≤ h → ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l)),
      (∀ l, l ≤ nl → IsGField G (U l)) →
      ∀ {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
        (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι → (∀ x, 0 < Fintype.card (P x)) →
      (∀ x, AxialReference.InM h (off x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c₂ →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      ∀ l, l ≤ nl →
      (∀ m, m < l → ∀ (ρ : Fin 4) (x : Fin 4 → ℤ), Lat (Lz h) (m + 1) x → Rg h nl μ (m + 1) x →
        Rg h nl μ (m + 1) (x + Lz h ^ (m + 1) • Pi.single ρ 1) →
        U (m + 1) ρ (img h (base (m + 1)) (m + 1) x) = avgB G (U m) (img h (base m) m x) ρ (2 * h + 1) off ord) →
      ∀ μ' ν', μ' ≠ ν' → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        Rg h nl μ l (x + Lz h ^ l • Pi.single μ' 1) → Rg h nl μ l (x + Lz h ^ l • Pi.single ν' 1) →
        hs (((plaq (U l) μ' ν' (img h (base l) l x) : GLN) : Mat) - 1) ≤
          2 * (α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l)) := by
  obtain ⟨c₂, hc₂, hRA⟩ := regular_averages_ii G hG hN
  refine ⟨c₂, hc₂, ?_⟩
  intro h hh nl μ nn _ hn base U hU ι _ P _ off ord hι hP hoff hord α hα hαc hbase l hl hrel μ' ν' hμν x hx
    r0 r1 r2
  set K : ℝ := (((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : K ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by push_cast; linarith))
  set α' := α * K ^ (nl - l) with hα'
  have hα'0 : 0 ≤ α' := by positivity
  have hα'c : α' ≤ c₂ := (mul_le_of_le_one_right hα (pow_le_one₀ hK0 hK1)).trans hαc
  have hxm : ∀ m, m ≤ l → Lat (Lz h) m x := fun m hm σ => (pow_dvd_pow (Lz h) hm).trans (hx σ)
  set base' : ∀ m, Site (nn m) := fun m => img h (base m) m x with hbase'
  have key := hRA h hh l μ' ν' hμν nn (fun m _ => hn m) base' U (fun m hm => hU m (hm.trans hl)) off ord hι hP
    hoff hord ?_ α' hα'0 hα'c ?_
  · exact key.1.trans key.2
  · -- the averages of the sub-hierarchy are those of the levels
    intro m hm ρ x' hx' q0 q1
    have hm1 : m + 1 ≤ l := hm
    simp only [hbase']
    rw [img_img (base (m + 1)) (hxm (m + 1) hm1) hx', img_img (base m) (hxm m (by omega)) (lat_succ_le hx')]
    have e : x + (x' + Lz h ^ (m + 1) • Pi.single ρ 1) = x + x' + Lz h ^ (m + 1) • Pi.single ρ 1 := by
      rw [add_assoc]
    refine hrel m (by omega) ρ (x + x') ?_ (rg_sub hm1 hl r0 r1 r2 q0) ?_
    · exact fun σ => dvd_add (hxm (m + 1) hm1 σ) (hx' σ)
    · rw [← e]; exact rg_sub hm1 hl r0 r1 r2 q1
  · -- the plaquettes of the level `0` of the sub-hierarchy
    intro μ'' ν'' x' ⟨hx', q0, q1, q2, q3⟩
    simp only [hbase']
    rw [img_img (base 0) (hxm 0 (Nat.zero_le _)) hx']
    have hb := hbase μ'' ν'' (x + x') (fun σ => dvd_add (hxm 0 (Nat.zero_le _) σ) (hx' σ))
      (rg_sub (Nat.zero_le _) hl r0 r1 r2 q0)
      (by have := rg_sub (Nat.zero_le _) hl r0 r1 r2 q1; simpa [add_assoc] using this)
      (by have := rg_sub (Nat.zero_le _) hl r0 r1 r2 q2; simpa [add_assoc] using this)
      (by have := rg_sub (Nat.zero_le _) hl r0 r1 r2 q3; simpa [add_assoc] using this)
    refine hb.trans (le_of_eq ?_)
    rw [hα', mul_assoc, ← pow_add, Nat.sub_add_cancel hl]


/-! ### The average with `Log` is the average with the chart of `G` -/

/-- **Locality of `avgB`**: the average of `def:average` depends only on the bonds with both ends in
`B(c₋) ∪ B(c₊)` (`lem:average`(ii)). -/
theorem avgB_local {n : ℕ} [NeZero n] (G : GaugeGroup N) {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4}
    {V V' : Config N n}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z) :
    avgB G V y μ (2 * h + 1) (offP h) (ordG h) = avgB G V' y μ (2 * h + 1) (offP h) (ordG h) := by
  have hval := val_eq_of_pos (S := fun z => Bm y h z ∨ Bp y h μ z) hVV
  have hpath : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → V.hol γ = V'.hol γ := fun γ hγ =>
    hol_congr_of γ fun t ht => hval t (hγ t ht).1 (hγ t ht).2
  have hnd : ∀ x (Γ : Ords (offP h x)), (ordG h x Γ).Nodup := fun x Γ => (ordG_perm h x Γ).nodup_iff.2 (by decide)
  have hseg : ∀ t ∈ segZ μ y ((2 * h + 1 : ℕ) : ℤ), (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus) := by
    have := (paths_in (y := y) hn μ (inM_zero h) [] List.nodup_nil).2.2
    rwa [ofs_zero] at this
  unfold avgB
  congr 1
  · funext x Γ; exact hpath _ (paths_in hn μ (offP_inM h x) _ (hnd x Γ)).1
  · funext x; exact hpath _ (paths_in hn μ (offP_inM h x) [] List.nodup_nil).2.2
  · funext x Γ; exact hpath _ (paths_in hn μ (offP_inM h x) _ (hnd x Γ)).2.1
  · exact hpath _ hseg

/-- **`avgM = avgB`**: for a field with values in `G` whose plaquettes on the blocks of the bond are at most
`α₀ ≤ c`, the average with the series `Log` is the average of `def:average` with the chart of `G`; `c` depends on
`L` and `G` only. -/
theorem avgM_eq_avgB (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        avgM U y μ h = avgB G U y μ (2 * h + 1) (offP h) (ordG h) := by
  obtain ⟨c₀, hc₀, han⟩ := average_analytic G hG
  obtain ⟨rl, hrl, -, hlog⟩ := log_mem_lie G hG
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  have hLr : 0 < Lr := by positivity
  set c := min (min (c₀ / Lr / (2 * K)) (1 / (8 * K))) (rl / (2 * K)) with hc_def
  have hc1 : c ≤ c₀ / Lr / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ rl / (2 * K) := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) (by positivity), ?_⟩
  intro n _ U hU hn y α₀ hα₀ hα₀c hplq
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hUg := hU.gauge
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ (0 : ℝ) := fun ρ z _ => by simp
  obtain ⟨X, hXc, -, hag, hl, hz⟩ := reduce_box_supp hUg hn y μ hα₀ le_rfl hα₀c (by positivity : (0 : ℝ) ≤ c)
    hc2 hplq 0 hA0
  rw [moveC_zero] at hag hl
  have hKc : ∀ t : ℝ, c ≤ t / (2 * K) → K * c ≤ t / 2 := fun t ht => by
    calc K * c ≤ K * (t / (2 * K)) := mul_le_mul_of_nonneg_left ht hKpos.le
      _ = t / 2 := by field_simp
  have hX8 : ‖X‖ ≤ 1 / 8 := hXc.trans (by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc2 hKpos.le
      _ = 1 / 8 := by field_simp)
  set u := uG U y h
  have huG : ∀ z, u z ∈ G.carrier := fun z => hU.hol_mem _
  -- `X` has values in `𝔤`
  have hXl : ∀ ρ z, X ρ z ∈ G.lie := by
    intro ρ z
    by_cases hb : BoxBond y h μ ρ z
    · rw [hl ρ z hb]
      have hWG : (U.gauge u) ρ z ∈ G.carrier := by
        simp only [Config.gauge]
        exact G.carrier.mul_mem (G.carrier.mul_mem (huG z) (hU ρ z)) (G.carrier.inv_mem (huG _))
      have hWn : ‖(((U.gauge u) ρ z : GLN) : Mat) - 1‖ ≤ rl := by
        rw [hag ρ z hb]
        show ‖((expU (Complex.I • X ρ z) * oneC (N := N) ρ z : GLN) : Mat) - 1‖ ≤ rl
        simp only [oneC, mul_one]
        have hXz : ‖Complex.I • X ρ z‖ ≤ ‖X‖ := by
          rw [norm_I_smul']; exact (norm_le_pi_norm (X ρ) z).trans (norm_le_pi_norm X ρ)
        have h1 := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • X ρ z)).trans
          (exp_sub_one_le_two_mul (norm_nonneg _) hXz (hX8.trans (by norm_num)))
        have hKcl := hKc rl hc3
        show ‖exp (Complex.I • X ρ z) - 1‖ ≤ rl
        linarith
      exact (hlog _ hWG rl hWn le_rfl).1
    · rw [hz ρ z hb]; exact G.zero_mem_lie
  -- `avgB = avgLogU` for `𝐔_X = e^{iX}`
  have hone : IsGField G (oneC (N := N) (n := n)) := fun _ _ => G.carrier.one_mem
  obtain ⟨-, -, hBL, -⟩ := han (oneC (N := N) (n := n)) hone h y μ (offP h) (ordG h) (offP_inM h) (ordG_perm h)
    (fun x Γ Γ' => by rw [hol_oneC]; simp only [Units.val_one, sub_self, norm_zero]; exact hc₀.le)
  have hXc0 : ‖X‖ < c₀ / Lr := lt_of_le_of_lt hXc (by
    have := hKc (c₀ / Lr) hc1
    have : 0 < c₀ / Lr := by positivity
    linarith)
  have hUX : avgB G (UX (N := N) X) y μ (2 * h + 1) (offP h) (ordG h) = avgM (UX (N := N) X) y μ h :=
    hBL X hXc0 hXl
  -- the covariance and the locality of both averages
  have hbase : u y = 1 := uG_base U hn y
  have hM : avgM U y μ h = avgM (U.gauge u) y μ h * u (cPlus y μ h) := by
    rw [avgM_gauge, hbase, one_mul, inv_mul_cancel_right]
  have hB : avgB G U y μ (2 * h + 1) (offP h) (ordG h) =
      avgB G (U.gauge u) y μ (2 * h + 1) (offP h) (ordG h) * u (cPlus y μ h) := by
    rw [avgB_gauge U u huG y μ (2 * h + 1) (offP h) (ordG h) (ordG_perm h), hbase, one_mul]
    exact (inv_mul_cancel_right _ _).symm
  have hlM : avgM (U.gauge u) y μ h = avgM (UX (N := N) X) y μ h :=
    avgM_local hn2 fun ν z h1 h2 => hag ν z ⟨h1, h2⟩
  have hlB : avgB G (U.gauge u) y μ (2 * h + 1) (offP h) (ordG h) =
      avgB G (UX (N := N) X) y μ (2 * h + 1) (offP h) (ordG h) :=
    avgB_local G hn2 fun ν z h1 h2 => hag ν z ⟨h1, h2⟩
  rw [hM, hB, hlM, hlB, hUX]


/-- A plaquette of the box of a bond of the level `l + 1` is a plaquette of the level `l` whose corners lie in the
region of the level `l`. -/
lemma box_plaq {n : ℕ} [NeZero n] {h nl l : ℕ} (hn : 4 * h + 4 ≤ n) {μ ρ : Fin 4} (y : Site n)
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) {μ' ν' : Fin 4} {z : Site n}
    (hz : PlaqIn (boxR (img h y l x) (loD h) (hiD h ρ ρ)) μ' ν' z) :
    ∃ x', Lat (Lz h) l x' ∧ Rg h nl μ l x' ∧ Rg h nl μ l (x' + Lz h ^ l • Pi.single μ' 1) ∧
      Rg h nl μ l (x' + Lz h ^ l • Pi.single ν' 1) ∧ z = img h y l x' := by
  obtain ⟨m, hm, hm1, hm2, -, rfl⟩ := plaqIn_box hn (img h y l x) ρ ρ μ' ν' z hz
  have hxl := lat_succ_le hx
  have e : ∀ w : Fin 4 → ℤ, x + Lz h ^ l • m + Lz h ^ l • w = x + Lz h ^ l • (m + w) := fun w => by
    rw [smul_add, add_assoc]
  refine ⟨x + Lz h ^ l • m, lat_add_smul hxl m, rg_of_bond h0 h1 hm, ?_, ?_, ?_⟩
  · rw [e]; exact rg_of_bond h0 h1 hm1
  · rw [e]; exact rg_of_bond h0 h1 hm2
  · rw [img_add y hxl]

/-- **The plaquettes of the levels of `U`** (the paragraph "The gauge fields `U_l`" of the proof): if `U_{l+1} = M(U_l)`
on the regions, with the average with `Log`, the fields `U_l` have values in `G`, and the plaquettes of `U_0` with
corners in the region satisfy `|U_0(∂p) - id| ≤ α L^{-2n}`, `α ≤ c`, then the plaquettes of `U_l` with corners in the
region of the level `l` satisfy `|U_l(∂p) - id| ≤ 2α L^{-2(n-l)}`; `c` depends on `L` and `G` only. The two averages
agree level by level (`avgM_eq_avgB`), by the bound at the level below. -/
theorem levels_plaq (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l)),
      (∀ l, l ≤ nl → IsGField G (U l)) →
      (∀ l, l < nl → ∀ (ρ : Fin 4) (x : Fin 4 → ℤ), Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      ∀ l, l ≤ nl → ∀ μ' ν' x, Lat (Lz h) l x → Rg h nl μ l x →
        Rg h nl μ l (x + Lz h ^ l • Pi.single μ' 1) → Rg h nl μ l (x + Lz h ^ l • Pi.single ν' 1) →
        hs (((plaq (U l) μ' ν' (img h (base l) l x) : GLN) : Mat) - 1) ≤
          2 * (α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l)) := by
  obtain ⟨c₂, hc₂, hPL⟩ := plaq_levels G hG hN
  choose ce hce heq using fun ρ : Fin 4 => avgM_eq_avgB G hG h ρ
  set cem := Finset.univ.inf' Finset.univ_nonempty ce
  have hce0 : 0 < cem := (Finset.lt_inf'_iff _).2 fun ρ _ => hce ρ
  have hcele : ∀ ρ, cem ≤ ce ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨min c₂ (cem / 2), lt_min hc₂ (by positivity), ?_⟩
  intro nl μ nn _ hn base U hU hrel α hα hαc hbase
  set K : ℝ := (((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : K ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by push_cast; linarith))
  have hαc2 : α ≤ c₂ := hαc.trans (min_le_left _ _)
  have hαce : 2 * α ≤ cem := by have := hαc.trans (min_le_right _ _); linarith
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl μ' ν' x hx r0 r1 r2
    by_cases hμν : μ' = ν'
    · subst hμν
      rw [plaq_self, Units.val_one, sub_self]
      have : hs (0 : Mat) = 0 := hs_zero'
      rw [this]; positivity
    -- the averages below the level `l` agree
    refine hPL h hh nl μ nn hn base U hU (offP h) (ordG h) (by simp [Pts]) (fun x => card_ords_pos _)
      (offP_inM h) (ordG_perm h) α hα hαc2 hbase l hl ?_ μ' ν' hμν x hx r0 r1 r2
    intro m hm ρ y hy q0 q1
    rw [hrel m (by omega) ρ y hy q0 q1]
    refine heq ρ (U m) (hU m (by omega)) (hn m) (img h (base m) m y) (2 * (α * K ^ (nl - m))) (by positivity)
      ?_ ?_
    · calc 2 * (α * K ^ (nl - m)) ≤ 2 * (α * 1) := by gcongr; exact pow_le_one₀ hK0 hK1
        _ ≤ ce ρ := by linarith [hcele ρ]
    · intro μ'' ν'' z hz
      obtain ⟨x', hx', s0, s1, s2, rfl⟩ := box_plaq (hn m) (base m) hy q0 q1 hz
      exact ih m hm (by omega) μ'' ν'' x' hx' s0 s1 s2


/-! ### The real background: `M^l(e^{ia_iA'}U) = e^{ia_{i+l}A'_l}U_l` -/

/-- **Products of three exponentials** (the paragraph "Products of exponentials" of the proof, with three factors):
`e^{iX}e^{iY}e^{iZ} = e^{iW}` with `‖W‖ ≤ 2(‖X‖ + ‖Y‖ + ‖Z‖)` when the sum is at most `2^{-10}`. -/
lemma three_exp {X Y Z : Mat} (hs : ‖X‖ + ‖Y‖ + ‖Z‖ ≤ 1 / 1024) :
    ∃ W : Mat, expU (Complex.I • X) * expU (Complex.I • Y) * expU (Complex.I • Z) = expU (Complex.I • W) ∧
      ‖W‖ ≤ 2 * (‖X‖ + ‖Y‖ + ‖Z‖) := by
  have ha := norm_nonneg X
  have hb := norm_nonneg Y
  have hc := norm_nonneg Z
  obtain ⟨e1, n1⟩ := expU_mul_psi (G := X) (S := Y) (by linarith) (by linarith)
  have hab : 256 * ‖X‖ * ‖Y‖ ≤ (‖X‖ + ‖Y‖) / 4 := by nlinarith
  have hP : ‖psi X Y‖ ≤ 5 / 4 * (‖X‖ + ‖Y‖) := by linarith
  obtain ⟨e2, n2⟩ := expU_mul_psi (G := psi X Y) (S := Z) (by linarith) (by linarith)
  refine ⟨psi (psi X Y) Z, by rw [e1, e2], ?_⟩
  have hPc : 256 * ‖psi X Y‖ * ‖Z‖ ≤ 256 * (5 / 4 * (‖X‖ + ‖Y‖)) * ‖Z‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hc
  have h3 : 256 * (5 / 4 * (‖X‖ + ‖Y‖)) * ‖Z‖ ≤ ‖Z‖ / 2 := by nlinarith
  linarith

/-- **The real background at a bond**: if `W = (e^{iB}U)^𝐠` there, `U` unitary, `𝐠 = e^{iG}` at the ends, then
`W = e^{iB̃}U` with `‖B̃‖ ≤ 2(‖G₋‖ + ‖B‖ + ‖G₊‖)` (the consequences of `H(l)` for the pairs `(0, A)`). -/
theorem real_background {n : ℕ} [NeZero n] (W U : Config N n) (B : Fin 4 → Site n → Mat) (g : Site n → GLN)
    {ρ : Fin 4} {z : Site n} {Gm Gp : Mat}
    (hW : W ρ z = ((moveC U B).gauge g) ρ z) (hU : ((U ρ z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (hgm : g z = expU (Complex.I • Gm)) (hgp : g (z + unit n ρ) = expU (Complex.I • Gp))
    (hs : ‖Gm‖ + ‖B ρ z‖ + ‖Gp‖ ≤ 1 / 1024) :
    ∃ Bt : Mat, W ρ z = expU (Complex.I • Bt) * U ρ z ∧ ‖Bt‖ ≤ 2 * (‖Gm‖ + ‖B ρ z‖ + ‖Gp‖) := by
  have hinv : (expU (Complex.I • Gp))⁻¹ = expU (-(Complex.I • Gp)) :=
    Units.ext (by rw [expU_inv_val, expU_val])
  have hAd : Ad (U ρ z) (-(Complex.I • Gp)) = Complex.I • (-(Ad (U ρ z) Gp)) := by
    rw [Ad_neg, Ad_smul, smul_neg]
  have hn : ‖-(Ad (U ρ z) Gp)‖ = ‖Gp‖ := by rw [norm_neg, SupportCont.opNorm_Ad_unitary hU]
  obtain ⟨Bt, he, hBt⟩ := three_exp (X := Gm) (Y := B ρ z) (Z := -(Ad (U ρ z) Gp)) (by rw [hn]; exact hs)
  refine ⟨Bt, ?_, by rw [hn] at hBt; exact hBt⟩
  calc W ρ z = expU (Complex.I • Gm) * (expU (Complex.I • B ρ z) * U ρ z) * expU (-(Complex.I • Gp)) := by
        rw [hW, Config.gauge, moveC, hgm, hgp, hinv]
    _ = expU (Complex.I • Gm) * expU (Complex.I • B ρ z) * (U ρ z * expU (-(Complex.I • Gp)) * (U ρ z)⁻¹) *
          U ρ z := by group
    _ = expU (Complex.I • Gm) * expU (Complex.I • B ρ z) * expU (Complex.I • (-(Ad (U ρ z) Gp))) * U ρ z := by
        rw [expU_conj, hAd]
    _ = expU (Complex.I • Bt) * U ρ z := by rw [he]


/-- **The backgrounds of the levels**: for the pair `(0, A')`, whose background is the gauge field `U` with its levels
`U_{l+1} = M(U_l)`, the averages `W_{l+1} = M(W_l)` of `W_0 = e^{ia_iA'}U` are `W_l = e^{iA'_l}U_l` on the bonds of the
region of every level, with `‖A'_l‖ ≤ K_o tL^{-(n-l)}`, `K_o = 4C₁ + 4`, where `t` bounds `‖a_jA'‖`
(`M^l(e^{ia_iA'}U) = e^{ia_{i+l}A'_l}U_l` in the proof). -/
theorem background_levels (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U W : ∀ l, Config N (nn l))
      (B : ∀ l, Fin 4 → Site (nn l) → Mat) (g : ∀ l, Site (nn l) → GLN) (a₀ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        W (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (W l) (img h (base l) l x) ρ h) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        W 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B 0) ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g l (img h (base l) l x) * siteFactor (U l) (B l) (img h (base l) l x) h) →
      (∀ z, g 0 z = 1) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ a₀ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ t → 0 ≤ e₀ → e₀ ≤ c → 2 * t < c → C * (e₀ + 2 * t) ≤ 1 → (2 * C₁ + 2) * t ≤ 1 / 1024 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        ∃ Bt : Mat, W l ρ (img h (base l) l x) = expU (Complex.I • Bt) * U l ρ (img h (base l) l x) ∧
          ‖Bt‖ ≤ (4 * C₁ + 4) * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨c, C, C₁, hc, hC, hC₁, hH⟩ := order_H (N := N) h hh
  refine ⟨c, C, C₁, hc, hC, hC₁, ?_⟩
  intro nl μ nn _ hn base U W B g a₀ t e₀ hU hplq hV hW hW0 hB hg hg0 ha ht he0 he0c htc hCE hCt hB0
  have hCt' : C₁ * t ≤ 1 / 256 := by nlinarith
  have hH' := hH nl μ nn hn base U U W (fun _ => 0) B g a₀ (fun _ => 0) t e₀ hU
    (fun l _ ν x _ _ _ => by rw [moveC_zero])
    (fun l hl ρ x hx h0 h1 => ⟨hplq l hl ρ x hx h0 h1, fun ν z _ => by simp⟩)
    hV hW hW0 hB hg hg0 (fun l hl => ⟨(ha l hl).1, le_rfl, by simpa using (ha l hl).2⟩) ht he0 he0c htc hCE hCt'
    hB0
  intro l hl ρ x hx h0 h1
  set q : ℝ := ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by push_cast; linarith))
  obtain ⟨hform, hgau⟩ := hH' l hl
  obtain ⟨hWf, hBn⟩ := hform ρ x hx h0 h1
  obtain ⟨Gm, hGm, hGmn⟩ := hgau x hx h0
  obtain ⟨Gp, hGp, hGpn⟩ := hgau _ (lat_add_smul hx _) h1
  rw [← img_unit (base l) hx] at hGp
  have hsum : ‖Gm‖ + ‖B l ρ (img h (base l) l x)‖ + ‖Gp‖ ≤ (2 * C₁ + 2) * t * q := by linarith
  have hsmall : (2 * C₁ + 2) * t * q ≤ 1 / 1024 := by
    calc (2 * C₁ + 2) * t * q ≤ (2 * C₁ + 2) * t * 1 := by gcongr
      _ ≤ 1 / 1024 := by linarith
  obtain ⟨Bt, hBt, hBtn⟩ := real_background (W l) (U l) (B l) (g l) hWf (hU l ρ _) hGm hGp (hsum.trans hsmall)
  exact ⟨Bt, hBt, hBtn.trans (by nlinarith)⟩


/-- `L^{-2m} ≤ L^{-m}`. -/
lemma sq_inv_pow_le (h m : ℕ) :
    ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ m ≤ ((((2 * h + 1 : ℕ) : ℝ)) ^ m)⁻¹ := by
  have hL : (1 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by push_cast; have : (0 : ℝ) ≤ h := by positivity
                                                  linarith
  have e : ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ m = (((((2 * h + 1 : ℕ) : ℝ)) ^ m)⁻¹) ^ 2 := by
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
  rw [e]
  have h0 : 0 ≤ ((((2 * h + 1 : ℕ) : ℝ)) ^ m)⁻¹ := by positivity
  have h1 : ((((2 * h + 1 : ℕ) : ℝ)) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  nlinarith

/-- **`prop:relative-average-order`, the induction from the data on `T^{(i)}`**: let `U` have values in `G` with its
levels `U_{l+1} = M(U_l)`, `𝐔 = e^{ia_iA'}U` with its levels `V_{l+1} = M(V_l)`, and `e^{ia_iA}𝐔` with its levels
`W_{l+1} = M(W_l)`, on the regions; let `B'_l` and `B_l` be the forms and `𝐠'_l`, `𝐠_l` the gauge transformations of the
two pairs `(0, A')` and `(A', A)`. If the plaquettes of `U` with corners in `Bⁿ(c₋) ∪ Bⁿ(c₊)` are at most `α₀L^{-2n}`,
`‖a_jA'‖ ≤ t'`, `‖a_jA‖ ≤ t`, and `α₀, t', t ≤ c`, then on the region of every level: `V_l = e^{iA'_l}U_l` with
`‖A'_l‖ ≤ K_ot'L^{-(n-l)}`, `W_l = (e^{iB_l}V_l)^{𝐠_l}`, `‖B_l‖ ≤ 2tL^{-(n-l)}`, and `𝐠_l = e^{iG_l}` with
`‖G_l‖ ≤ C₁tL^{-(n-l)}`. The constants depend on `L` and `G` only. -/
theorem order_levels (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C₁ Ko : ℝ, 0 < c ∧ 0 ≤ C₁ ∧ 0 ≤ Ko ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V W : ∀ l, Config N (nn l))
      (B' B : ∀ l, Fin 4 → Site (nn l) → Mat) (g' g : ∀ l, Site (nn l) → GLN) (α₀ t' t : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        W (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (W l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h ∧
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h ∧
        g (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) → (∀ z, g 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        W 0 ρ (img h (base 0) 0 x) = moveC (V 0) (B 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        ‖B 0 ρ (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → 0 ≤ t → α₀ ≤ c → t' ≤ c → t ≤ c →
      ∀ l, l ≤ nl →
        (∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
          (∃ A'l : Mat, V l ρ (img h (base l) l x) = expU (Complex.I • A'l) * U l ρ (img h (base l) l x) ∧
            ‖A'l‖ ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) ∧
          W l ρ (img h (base l) l x) = ((moveC (V l) (B l)).gauge (g l)) ρ (img h (base l) l x) ∧
          ‖B l ρ (img h (base l) l x)‖ ≤ 2 * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) ∧
        (∀ x, Lat (Lz h) l x → Rg h nl μ l x →
          ∃ Gl : Mat, g l (img h (base l) l x) = expU (Complex.I • Gl) ∧
            ‖Gl‖ ≤ C₁ * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) := by
  obtain ⟨cp, hcp, hLP⟩ := levels_plaq G hG hN h hh
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  obtain ⟨cH, CH, C₁H, hcH, hCH, hC₁H, hH⟩ := order_H (N := N) h hh
  set Ko : ℝ := 4 * C₁b + 4 with hKo
  have hKo0 : 0 ≤ Ko := by positivity
  set c := min (min (min cp (cb / 4)) (min (1 / (4 * (Cb + 1))) (1 / (1024 * (2 * C₁b + 2)))))
    (min (min (cH / (4 + Ko)) (1 / ((CH + 1) * (4 + Ko)))) (1 / (256 * (C₁H + 1)))) with hc_def
  have k1 : c ≤ cp := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have k2 : c ≤ cb / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have k3 : c ≤ 1 / (4 * (Cb + 1)) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k4 : c ≤ 1 / (1024 * (2 * C₁b + 2)) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have k5 : c ≤ cH / (4 + Ko) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have k6 : c ≤ 1 / ((CH + 1) * (4 + Ko)) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have k7 : c ≤ 1 / (256 * (C₁H + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcp (by positivity)) (lt_min (by positivity) (by positivity)))
    (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  refine ⟨c, C₁H, Ko, hc0, hC₁H, hKo0, ?_⟩
  intro nl μ nn _ hn base U V W B' B g' g α₀ t' t hUG hrel hgrel hg'0 hg0 h0 hbase hα₀ ht' ht hα₀c ht'c htc
  have hUg : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  set K : ℝ := (((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹ with hK
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  -- the plaquettes of the levels
  have hpl := hLP nl μ nn hn base U (fun l _ => hUG l) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).1) α₀ hα₀
    (hα₀c.trans k1) hbase
  set a₀ : ℕ → ℝ := fun l => 2 * (α₀ * K ^ (nl - l)) with ha₀
  have hbox : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
        hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l := fun l hl ρ x hx q0 q1 μ' ν' z hz => by
    obtain ⟨x', hx', s0, s1, s2, rfl⟩ := box_plaq (hn l) (base l) hx q0 q1 hz
    exact hpl l hl.le μ' ν' x' hx' s0 s1 s2
  have ha₀ : ∀ l, 0 ≤ a₀ l ∧ a₀ l ≤ 2 * α₀ * (Lr ^ (nl - l))⁻¹ := fun l => by
    refine ⟨by positivity, ?_⟩
    have := sq_inv_pow_le h (nl - l)
    simp only [ha₀]
    nlinarith
  -- the backgrounds of the levels: the pair `(0, A')`
  have hCb : Cb * (2 * α₀ + 2 * t') ≤ 1 := by
    calc Cb * (2 * α₀ + 2 * t') ≤ Cb * (4 * (1 / (4 * (Cb + 1)))) := by gcongr; linarith
      _ = Cb / (Cb + 1) := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hC₁b' : (2 * C₁b + 2) * t' ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t' ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hbg := hBL nl μ nn hn base U V B' g' a₀ t' (2 * α₀) hUg hbox
    (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.1)
    (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.2.2.1)
    (fun l hl x hx q0 => (hgrel l hl x hx q0).1) hg'0 (fun l _ => ha₀ l) ht' (by positivity) (by linarith) (by linarith) hCb hC₁b'
    (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).2.2.1)
  -- the fluctuations `A'_l` of the backgrounds
  set A'f : ∀ l, Fin 4 → Site (nn l) → Mat :=
    fun l ρ z => (1 / Complex.I) • LogM (((V l ρ z * (U l ρ z)⁻¹ : GLN) : Mat)) with hA'f
  have hKt : Ko * t' ≤ 1 / 512 := by
    have : Ko * t' = 2 * ((2 * C₁b + 2) * t') := by rw [hKo]; ring
    linarith
  have hA'val : ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x →
      Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      V l ρ (img h (base l) l x) = moveC (U l) (A'f l) ρ (img h (base l) l x) ∧
        ‖A'f l ρ (img h (base l) l x)‖ ≤ Ko * t' * (Lr ^ (nl - l))⁻¹ := by
    intro l hl ρ x hx q0 q1
    obtain ⟨Bt, hBt, hBtn⟩ := hbg l hl ρ x hx q0 q1
    have hBts : ‖Bt‖ < Real.log 2 := by
      have := Real.log_two_gt_d9
      have : Ko * t' * (Lr ^ (nl - l))⁻¹ ≤ Ko * t' * 1 := by gcongr; exact hp1 _
      linarith
    have hval : A'f l ρ (img h (base l) l x) = Bt := by
      simp only [hA'f]
      rw [hBt, mul_inv_cancel_right]
      exact order_iv rfl hBts
    refine ⟨?_, by rw [hval]; exact hBtn⟩
    show V l ρ (img h (base l) l x) = expU (Complex.I • A'f l ρ (img h (base l) l x)) * U l ρ (img h (base l) l x)
    rw [hval, hBt]
  -- the general pair `(A', A)`
  have hCH' : CH * (2 * α₀ + Ko * t' + 2 * t) ≤ 1 := by
    calc CH * (2 * α₀ + Ko * t' + 2 * t) ≤ CH * ((4 + Ko) * (1 / ((CH + 1) * (4 + Ko)))) := by
          gcongr
          have := hKo0
          nlinarith
      _ = CH / (CH + 1) := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hC₁H' : C₁H * t ≤ 1 / 256 := by
    calc C₁H * t ≤ (C₁H + 1) * (1 / (256 * (C₁H + 1))) := by gcongr; linarith; linarith
      _ = 1 / 256 := by field_simp
  have he₀ : 2 * α₀ + Ko * t' ≤ cH := by
    have : 2 * α₀ + Ko * t' ≤ (4 + Ko) * c := by nlinarith
    calc 2 * α₀ + Ko * t' ≤ (4 + Ko) * c := this
      _ ≤ (4 + Ko) * (cH / (4 + Ko)) := by gcongr
      _ = cH := by field_simp
  have h2t : 2 * t < cH := by
    have : (4 + Ko) * c ≤ cH := by
      calc (4 + Ko) * c ≤ (4 + Ko) * (cH / (4 + Ko)) := by gcongr
        _ = cH := by field_simp
    nlinarith
  have hHH := hH nl μ nn hn base U V W A'f B g a₀ (fun l => Ko * t' * (Lr ^ (nl - l))⁻¹) t (2 * α₀ + Ko * t') hUg
    (fun l hl ν x hx q0 q1 => (hA'val l hl.le ν x hx q0 q1).1)
    (fun l hl ρ x hx q0 q1 => ⟨hbox l hl ρ x hx q0 q1, fun ν z hb => by
      obtain ⟨x', hx', s0, s1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hA'val l (by omega) ν x' hx' s0 s1).2⟩)
    (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.2.1)
    (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).2.1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.2.2.2)
    (fun l hl x hx q0 => (hgrel l hl x hx q0).2) hg0
    (fun l hl => ⟨(ha₀ l).1, by positivity, by have := (ha₀ l).2; nlinarith⟩) ht (by positivity) he₀ h2t hCH'
    hC₁H' (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).2.2.2)
  intro l hl
  obtain ⟨hform, hgau⟩ := hHH l hl
  refine ⟨fun ρ x hx q0 q1 => ⟨?_, (hform ρ x hx q0 q1).1, (hform ρ x hx q0 q1).2⟩, hgau⟩
  obtain ⟨hv, hvn⟩ := hA'val l hl ρ x hx q0 q1
  exact ⟨A'f l ρ (img h (base l) l x), hv, hvn⟩


/-! ### `(v)`: the gauge directions through the levels -/

section GaugeDir

variable {n : ℕ} [NeZero n]

/-- `GoodAt` is local: it depends only on the bonds of `B(y)`. -/
lemma goodAt_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z) : GoodAt V y h ↔ GoodAt V' y h := by
  have e : ∀ x Γ, holG V y h x Γ = holG V' y h x Γ := holG_local hn hVV
  have e2 : ∀ x, expsG V y h x = expsG V' y h x := expsG_local hn hVV
  simp only [GoodAt, quotG, e, e2]

lemma norm_Ad_sub_one {W Q : GLN} (hW : ((W : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ‖((W * Q * W⁻¹ : GLN) : Mat) - 1‖ = ‖((Q : GLN) : Mat) - 1‖ := by
  have e : ((W * Q * W⁻¹ : GLN) : Mat) - 1 = Ad W (((Q : GLN) : Mat) - 1) := by
    rw [Ad]
    simp only [Units.val_mul]
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [e, SupportCont.opNorm_Ad_unitary hW]

/-- `GoodAt` is invariant under unitary gauge transformations. -/
lemma goodAt_gauge {V : Config N n} {u : Site n → GLN} (hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    {y : Site n} {h : ℕ} : GoodAt (V.gauge u) y h ↔ GoodAt V y h := by
  have hq : ∀ x i, ‖((quotG (V.gauge u) y h x i : GLN) : Mat) - 1‖ = ‖((quotG V y h x i : GLN) : Mat) - 1‖ :=
    fun x i => by
      have e : quotG (V.gauge u) y h x i = u y * quotG V y h x i * (u y)⁻¹ := by
        simp only [quotG, holG_gauge]; group
      rw [e, norm_Ad_sub_one (hu y)]
  have he : ∀ x, ‖expsG (V.gauge u) y h x‖ = ‖expsG V y h x‖ := fun x => by
    rw [expsG_gauge]
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
        rw [SupportCont.opNorm_Ad_unitary (hu y)]; exact norm_le_pi_norm _ i
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
        have := norm_le_pi_norm (fun i => Ad (u y) (expsG V y h x i)) i
        rwa [SupportCont.opNorm_Ad_unitary (hu y)] at this
  simp only [GoodAt, hq, he]

/-- The holonomy of a loop of the average is conjugated by `u(y)` under a gauge transformation. -/
lemma hol_lpath_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (κ : Fin 4) (h : ℕ) (x : Pts h)
    (Γ Γ' : Ords (offP h x)) :
    (V.gauge u).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y κ (2 * h + 1) (offP h) (ordG h) x Γ Γ') =
      u y * V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y κ (2 * h + 1) (offP h) (ordG h) x Γ Γ') *
        (u y)⁻¹ := by
  set L := 2 * h + 1
  have est : ∀ (w : Site n) x (Γ : Ords (offP h x)), (V.gauge u).hol (stair w (offP h x) (ordG h x Γ) 0) =
      u w * V.hol (stair w (offP h x) (ordG h x Γ) 0) * (u (ofs w (offP h x)))⁻¹ := fun w x Γ => by
    have hc := chain_endpt_stair w (offP h x) (ordG h x Γ) 0
    rw [ofs_zero, zero_add, offs_perm _ (ordG_perm h x Γ)] at hc
    rw [hol_gauge V u _ w hc.1, hc.2]
  have eseg : ∀ (w : Site n), (V.gauge u).hol (segZ κ w (L : ℤ)) =
      u w * V.hol (segZ κ w (L : ℤ)) * (u (w + (L : ℤ) • unit n κ))⁻¹ := fun w => by
    rw [hol_gauge V u _ w (chain_segZ κ w _), endpt_segZ]
  have e1 : ∀ x, ofs y (offP h x) + (L : ℤ) • unit n κ = ofs (ofs y (Pi.single κ (L : ℤ))) (offP h x) := fun x => by
    rw [ofs_ofs, add_comm (Pi.single κ _) (offP h x), ofs_add_single]
  have e2 : y + (L : ℤ) • unit n κ = ofs y (Pi.single κ (L : ℤ)) := by
    rw [← ofs_zero y, ← ofs_add_single, zero_add, ofs_zero]
  rw [← loop_eq_hol, ← loop_eq_hol]
  simp only [Average.loop, est, eseg, e1, e2]
  group

/-- `LoopsGood` is invariant under unitary gauge transformations. -/
lemma loopsGood_gauge {V : Config N n} {u : Site n → GLN} (hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    {y : Site n} {μ : Fin 4} {h : ℕ} : LoopsGood (V.gauge u) y μ h ↔ LoopsGood V y μ h := by
  simp only [LoopsGood, hol_lpath_gauge, norm_Ad_sub_one (hu y)]

/-- `LoopsGood` is local: the loops lie in `B(c₋) ∪ B(c₊)`. -/
lemma loopsGood_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {V V' : Config N n}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z) : LoopsGood V y μ h ↔ LoopsGood V' y μ h := by
  have hval := val_eq_of_pos (S := fun z => Bm y h z ∨ Bp y h μ z) hVV
  have hpath : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → V.hol γ = V'.hol γ := fun γ hγ =>
    hol_congr_of γ fun t ht => hval t (hγ t ht).1 (hγ t ht).2
  have hrv : ∀ γ : List (Bond n), (∀ t ∈ γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus)) → ∀ t ∈ rv γ, (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus) := fun γ hγ t ht => by
    have := hγ _ (mem_rv_iff.1 ht)
    rw [Bond.rev_site, Bond.rev_plus] at this
    exact ⟨this.2, this.1⟩
  have hseg : ∀ t ∈ segZ μ y ((2 * h + 1 : ℕ) : ℤ), (Bm y h t.site ∨ Bp y h μ t.site) ∧
      (Bm y h t.plus ∨ Bp y h μ t.plus) := by
    have := (paths_in (y := y) hn μ (inM_zero h) [] List.nodup_nil).2.2
    rwa [ofs_zero] at this
  have hloop : ∀ x Γ Γ', V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') = V'.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') := fun x Γ Γ' => by
    refine hpath _ fun t ht => ?_
    have hnd : ∀ Γ : Ords (offP h x), (ordG h x Γ).Nodup := fun Γ => (ordG_perm h x Γ).nodup_iff.2 (by decide)
    simp only [lpath, List.mem_append] at ht
    rcases ht with ((ht | ht) | ht) | ht
    · exact (paths_in hn μ (offP_inM h x) _ (hnd Γ)).1 t ht
    · exact (paths_in hn μ (offP_inM h x) [] List.nodup_nil).2.2 t ht
    · exact hrv _ (paths_in hn μ (offP_inM h x) _ (hnd Γ')).2.1 t ht
    · exact hrv _ hseg t ht
  simp only [LoopsGood, hloop]

end GaugeDir


/-- **`prop:relative-average`(iv) for the core's `𝐔`**: for `𝐔 = e^{iaA'}U` with `|U(∂p) - id| ≤ α₀ ≤ c` and
`‖aA'‖ ≤ α₁ ≤ c` on the box, and a form `D` equal to `D_𝐔λ` on the bonds of the box,
`L(Q(𝐔)D)(c) = Ad_{M(𝐔)(c)}(Q'(𝐔)λ)(c₊) - (Q'(𝐔)λ)(c₋)`, that is `Q(𝐔)D_𝐔 = D_{M(𝐔)}Q'(𝐔)` in the units of the scale of
each side. -/
theorem gauge_dir_core (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (lam : Site n → Mat) (D : Fin 4 → Site n → Mat),
          (∀ ν z, BoxBond y h μ ν z → D ν z = Dfine (moveC U A') lam ν z) →
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h D =
            Ad (avgM (moveC U A') y μ h) (blockAvg (moveC U A') lam (cPlus y μ h) h) -
              blockAvg (moveC U A') lam y h := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (ci / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ ci / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA lam D hD
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  have hcond := hpol y X 0 hXci (by rw [norm_zero]; exact hci)
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  set W := moveC U A'
  -- the conditions of `Qlin_D` at `𝐔`, from those at `𝐔_X`
  have hg : GoodAt W y h := by
    refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g0)
    exact hag ν z ⟨Or.inl h1, Or.inl h2⟩
  have hg' : GoodAt W (cPlus y μ h) h := by
    refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g1)
    exact hag ν z ⟨Or.inr (bp_of_bm_plus hn2 h1), Or.inr (bp_of_bm_plus hn2 h2)⟩
  have hl : LoopsGood W y μ h := by
    refine (loopsGood_gauge hu).1 ((loopsGood_local hn2 fun ν z h1 h2 => ?_).2 hcond.l0)
    exact hag ν z ⟨h1, h2⟩
  -- `D = D_𝐔λ` on the box
  have hDQ : Qlin W y μ h D = Qlin W y μ h (Dfine W lam) := by
    rw [Qlin_restrict hU hn hag hci (hpol y) hXci D, Qlin_restrict hU hn hag hci (hpol y) hXci (Dfine W lam)]
    congr 1
    funext ν z
    by_cases hb : BoxBond y h μ ν z
    · rw [restrictF_box_apply _ hb, restrictF_box_apply _ hb, hD ν z hb]
    · rw [restrictF_box_apply' _ hb, restrictF_box_apply' _ hb]
  have hL0 : ((2 * h + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * h + 1 ≠ 0)
  rw [hDQ, Qlin_D hg hg' hl lam, smul_smul, mul_inv_cancel₀ hL0, one_smul]


/-- **`prop:relative-average-order`(v), the gauge directions**: under the per-level hypotheses (backgrounds
`V_l = e^{iA'_l}U_l` with `V_{l+1} = M(V_l)`, data at most `c`), if `λ_{l+1} = Q'(V_l)λ_l`, `D_{l+1} = LQ(V_l)D_l` on
the regions and `D_0 = D_{V_0}λ_0`, then `D_l = D_{V_l}λ_l` on the region of every level:
`D_l(c') = Ad_{V_l(c')}λ_l(c'₊) - λ_l(c'₋)`. At the last level this is `Q_n(𝐔)D_𝐔 = D_{M^n(𝐔)}Q'_n(𝐔)`. -/
theorem order_v_gauge (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (lam : ∀ l, Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        D 0 ρ (img h (base 0) 0 x) = Ad (V 0 ρ (img h (base 0) 0 x)) (lam 0 (img h (base 0) 0 (x + Lz h ^ 0 •
          Pi.single ρ 1))) - lam 0 (img h (base 0) 0 x)) →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        D l ρ (img h (base l) l x) =
          Ad (V l ρ (img h (base l) l x)) (lam l (img h (base l) l (x + Lz h ^ l • Pi.single ρ 1))) -
            lam l (img h (base l) l x) := by
  classical
  choose cg hcg hgd using fun ρ : Fin 4 => gauge_dir_core (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cg
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcg ρ
  have hcle : ∀ ρ, c ≤ cg ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V A' D lam a₀ a₁ hU hVU hdat ha hVD hlam hD0 l
  induction l with
  | zero => intro _; exact hD0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    obtain ⟨hV, hD⟩ := hVD l hll ρ x hx q0 q1
    set y := img h (base l) l x
    have hxl := lat_succ_le hx
    -- `V_l = 𝐔` on the box
    have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = moveC (U l) (A' l) ν z := fun ν z h1 h2 => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
      exact hVU l hll ν x' hx' r0 r1
    have hfun := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 hbox
    have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by simp only [Qlin, hfun]
    -- `D_l = D_𝐔λ_l` on the box
    have hDb : ∀ ν z, BoxBond y h ρ ν z → D l ν z = Dfine (moveC (U l) (A' l)) (lam l) ν z := fun ν z hb => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      rw [ih (by omega) ν x' hx' r0 r1, Dfine, hVU l hll ν x' hx' r0 r1, img_unit (base l) hx']
    have hstep := hgd ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
      hpl (A' l) hA (lam l) (D l) hDb
    -- the average and the block averages of `𝐔` are those of `V_l`
    have hM : avgM (moveC (U l) (A' l)) y ρ h = avgM (V l) y ρ h :=
      (avgM_local hn2 fun ν z h1 h2 => hbox ν z h1 h2).symm
    have hB0 : blockAvg (moveC (U l) (A' l)) (lam l) y h = blockAvg (V l) (lam l) y h := by
      have ht := trans_local (V := V l) (V' := moveC (U l) (A' l)) hn2 (y := y) (h := h)
        fun ν z h1 h2 => hbox ν z (Or.inl h1) (Or.inl h2)
      simp only [blockAvg, ht]
    have hB1 : blockAvg (moveC (U l) (A' l)) (lam l) (cPlus y ρ h) h =
        blockAvg (V l) (lam l) (cPlus y ρ h) h := by
      have ht := trans_local (V := V l) (V' := moveC (U l) (A' l)) hn2 (y := cPlus y ρ h) (h := h)
        fun ν z h1 h2 => hbox ν z (Or.inr (bp_of_bm_plus hn2 h1)) (Or.inr (bp_of_bm_plus hn2 h2))
      simp only [blockAvg, ht]
    rw [hD, hQ, hstep, hM, hB0, hB1, ← hV, ← hlam l hll x hx q0, cPlus_img (base l) hxl ρ,
      ← hlam l hll _ (lat_add_smul hx _) q1]


/-- **The per-level data from the data on `T^{(i)}`**: for `U` with values in `G`, its levels `U_{l+1} = M(U_l)`, the
levels `V_{l+1} = M(V_l)` of `𝐔 = e^{ia_iA'}U` with the forms `B'_l` and gauge transformations `𝐠'_l` of the pair `(0, A')`,
plaquettes of `U` on `Bⁿ(c₋) ∪ Bⁿ(c₊)` at most `α₀L^{-2n}`, `‖a_jA'‖ ≤ t'`, and `α₀, t' ≤ c`, there are forms `A'_l` with
`V_l = e^{iA'_l}U_l` and `‖A'_l‖ ≤ K_ot'L^{-(n-l)}` on the region of every level, and the plaquettes of `U_l` on the
blocks of the bonds of the level `l + 1` are at most `2α₀L^{-2(n-l)}`: the per-level hypotheses of the theorems
above, with `α₀⁽ˡ⁾ + α₁⁽ˡ⁾ ≤ (2α₀ + K_ot')L^{-(n-l)}`. -/
theorem order_data (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c Ko : ℝ, 0 < c ∧ 0 ≤ Ko ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (B' : ∀ l, Fin 4 → Site (nn l) → Mat) (g' : ∀ l, Site (nn l) → GLN) (α₀ t' : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → α₀ ≤ c → t' ≤ c →
      ∃ A' : ∀ l, Fin 4 → Site (nn l) → Mat,
        (∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
          V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
          ‖A' l ν (img h (base l) l x)‖ ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) ∧
        (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
          Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
          (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
            hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ 2 * (α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l))) ∧
          (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z →
            ‖A' l ν z‖ ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹)) ∧
        (∀ l, 2 * (α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l)) ≤
          2 * α₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) := by
  obtain ⟨cp, hcp, hLP⟩ := levels_plaq G hG hN h hh
  obtain ⟨cb, Cb, C₁b, hcb, hCb, hC₁b, hBL⟩ := background_levels (N := N) h hh
  set Ko : ℝ := 4 * C₁b + 4 with hKo
  have hKo0 : 0 ≤ Ko := by positivity
  set c := min (min cp (cb / 4)) (min (1 / (4 * (Cb + 1))) (1 / (1024 * (2 * C₁b + 2)))) with hc_def
  have k1 : c ≤ cp := (min_le_left _ _).trans (min_le_left _ _)
  have k2 : c ≤ cb / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have k3 : c ≤ 1 / (4 * (Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have k4 : c ≤ 1 / (1024 * (2 * C₁b + 2)) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min (lt_min hcp (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨c, Ko, hc0, hKo0, ?_⟩
  intro nl μ nn _ hn base U V B' g' α₀ t' hUG hrel hgrel hg'0 h0 hbase hα₀ ht' hα₀c ht'c
  have hUg : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  set K : ℝ := (((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹ with hK
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  have hpl := hLP nl μ nn hn base U (fun l _ => hUG l) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).1) α₀ hα₀
    (hα₀c.trans k1) hbase
  set a₀ : ℕ → ℝ := fun l => 2 * (α₀ * K ^ (nl - l)) with ha₀
  have hbox : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      ∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
        hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l := fun l hl ρ x hx q0 q1 μ' ν' z hz => by
    obtain ⟨x', hx', s0, s1, s2, rfl⟩ := box_plaq (hn l) (base l) hx q0 q1 hz
    exact hpl l hl.le μ' ν' x' hx' s0 s1 s2
  have ha₀ : ∀ l, 0 ≤ a₀ l ∧ a₀ l ≤ 2 * α₀ * (Lr ^ (nl - l))⁻¹ := fun l => by
    refine ⟨by positivity, ?_⟩
    have := sq_inv_pow_le h (nl - l)
    simp only [ha₀]
    nlinarith
  have hCb' : Cb * (2 * α₀ + 2 * t') ≤ 1 := by
    calc Cb * (2 * α₀ + 2 * t') ≤ Cb * (4 * (1 / (4 * (Cb + 1)))) := by gcongr; linarith
      _ = Cb / (Cb + 1) := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hC₁b' : (2 * C₁b + 2) * t' ≤ 1 / 1024 := by
    calc (2 * C₁b + 2) * t' ≤ (2 * C₁b + 2) * (1 / (1024 * (2 * C₁b + 2))) := by gcongr; linarith
      _ = 1 / 1024 := by field_simp
  have hbg := hBL nl μ nn hn base U V B' g' a₀ t' (2 * α₀) hUg hbox
    (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.1)
    (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).1) (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.2)
    hgrel hg'0 (fun l _ => ha₀ l) ht' (by positivity) (by linarith) (by linarith) hCb' hC₁b'
    (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).2)
  set A'f : ∀ l, Fin 4 → Site (nn l) → Mat :=
    fun l ρ z => (1 / Complex.I) • LogM (((V l ρ z * (U l ρ z)⁻¹ : GLN) : Mat)) with hA'f
  have hKt : Ko * t' ≤ 1 / 512 := by
    have : Ko * t' = 2 * ((2 * C₁b + 2) * t') := by rw [hKo]; ring
    linarith
  have hA'val : ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x →
      Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      V l ρ (img h (base l) l x) = moveC (U l) (A'f l) ρ (img h (base l) l x) ∧
        ‖A'f l ρ (img h (base l) l x)‖ ≤ Ko * t' * (Lr ^ (nl - l))⁻¹ := by
    intro l hl ρ x hx q0 q1
    obtain ⟨Bt, hBt, hBtn⟩ := hbg l hl ρ x hx q0 q1
    have hBts : ‖Bt‖ < Real.log 2 := by
      have := Real.log_two_gt_d9
      have : Ko * t' * (Lr ^ (nl - l))⁻¹ ≤ Ko * t' * 1 := by gcongr; exact hp1 _
      linarith
    have hval : A'f l ρ (img h (base l) l x) = Bt := by
      simp only [hA'f]
      rw [hBt, mul_inv_cancel_right]
      exact order_iv rfl hBts
    refine ⟨?_, by rw [hval]; exact hBtn⟩
    show V l ρ (img h (base l) l x) = expU (Complex.I • A'f l ρ (img h (base l) l x)) * U l ρ (img h (base l) l x)
    rw [hval, hBt]
  refine ⟨A'f, hA'val, fun l hl ρ x hx q0 q1 => ⟨hbox l hl ρ x hx q0 q1, fun ν z hb => ?_⟩, fun l => (ha₀ l).2⟩
  obtain ⟨x', hx', s0, s1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
  exact (hA'val l (by omega) ν x' hx' s0 s1).2


/-- The arithmetic of the smallness: `2α₀ + K_ot' ≤ c'` and `C(2α₀ + K_ot') ≤ 1` for `α₀, t' ≤ c` with
`c ≤ c'/(2 + K_o)` and `c ≤ 1/((C + 1)(2 + K_o))`. -/
lemma small_e {α₀ t' c c' C Ko : ℝ} (hα₀ : 0 ≤ α₀) (ht' : 0 ≤ t') (hKo : 0 ≤ Ko) (hC : 0 ≤ C)
    (hα₀c : α₀ ≤ c) (ht'c : t' ≤ c) (h1 : c ≤ c' / (2 + Ko)) (h2 : c ≤ 1 / ((C + 1) * (2 + Ko))) :
    2 * α₀ + Ko * t' ≤ c' ∧ C * (2 * α₀ + Ko * t') ≤ 1 := by
  have hs : 2 * α₀ + Ko * t' ≤ (2 + Ko) * c := by nlinarith
  have hpos : 0 < 2 + Ko := by linarith
  constructor
  · calc 2 * α₀ + Ko * t' ≤ (2 + Ko) * c := hs
      _ ≤ (2 + Ko) * (c' / (2 + Ko)) := by gcongr
      _ = c' := by field_simp
  · calc C * (2 * α₀ + Ko * t') ≤ (C + 1) * ((2 + Ko) * c) := by
          have := mul_le_mul_of_nonneg_left hs hC
          nlinarith [mul_nonneg hpos.le (hα₀.trans hα₀c)]
      _ ≤ (C + 1) * ((2 + Ko) * (1 / ((C + 1) * (2 + Ko)))) := by gcongr
      _ = 1 := by field_simp

/-- **`prop:relative-average-order`(ii) from the data on `T^{(i)}`**: under the hypotheses of `order_data`, the linear
parts `D_{l+1} = LQ(V_l)D_l` satisfy `‖D_n‖ ≤ Lⁿ(1 + C(2α₀ + K_ot'))‖D_0‖_∞` and the block averages
`λ_{l+1} = Q'(V_l)λ_l` satisfy `‖λ_n(y)‖ ≤ (1 + C(2α₀ + K_ot'))‖λ_0‖_{∞,Bⁿ(y)}`: in the core's units,
`‖(Q_n(𝐔)A)(c)‖ ≤ (1 + C'₂(α₀ + α₁))‖A‖_{∞,𝖡_c}` and `‖(Q'_n(𝐔)λ)(y)‖ ≤ (1 + C'₂(α₀ + α₁))‖λ‖_{∞,Bⁿ(y)}`. -/
theorem relative_average_order_ii (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C Ko : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ Ko ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (B' D : ∀ l, Fin 4 → Site (nn l) → Mat) (lam : ∀ l, Site (nn l) → Mat) (g' : ∀ l, Site (nn l) → GLN)
      (α₀ t' s₀ s₀' : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h ∧
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        ‖D 0 ρ (img h (base 0) 0 x)‖ ≤ s₀) →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → ‖lam 0 (img h (base 0) 0 x)‖ ≤ s₀') →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → 0 ≤ s₀ → 0 ≤ s₀' → α₀ ≤ c → t' ≤ c →
      (∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        ‖D nl ν (img h (base nl) nl x)‖ ≤ (((2 * h + 1 : ℕ) : ℝ)) ^ nl * (1 + C * (2 * α₀ + Ko * t')) * s₀) ∧
      (∀ x, Lat (Lz h) nl x → Rg h nl μ nl x →
        ‖lam nl (img h (base nl) nl x)‖ ≤ (1 + C * (2 * α₀ + Ko * t')) * s₀') := by
  obtain ⟨cd, Ko, hcd, hKo, hdata⟩ := order_data G hG hN h hh
  obtain ⟨c2, C2, hc2, hC2, hii⟩ := order_ii (N := N) h hh
  obtain ⟨c2', C2', hc2', hC2', hii'⟩ := order_ii_Q' (N := N) h hh
  set cm := min c2 c2'
  set Cm := max C2 C2'
  have hcm : 0 < cm := lt_min hc2 hc2'
  have hCm : 0 ≤ Cm := hC2.trans (le_max_left _ _)
  set c := min cd (min (cm / (2 + Ko)) (1 / ((Cm + 1) * (2 + Ko))))
  have k1 : c ≤ cd := min_le_left _ _
  have k2 : c ≤ cm / (2 + Ko) := (min_le_right _ _).trans (min_le_left _ _)
  have k3 : c ≤ 1 / ((Cm + 1) * (2 + Ko)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, Cm, Ko, lt_min hcd (lt_min (by positivity) (by positivity)), hCm, hKo, ?_⟩
  intro nl μ nn _ hn base U V B' D lam g' α₀ t' s₀ s₀' hUG hrel hgl hg'0 h0 hl0 hbase hα₀ ht' hs₀ hs₀' hα₀c ht'c
  obtain ⟨he, hCe⟩ := small_e hα₀ ht' hKo hCm hα₀c ht'c k2 k3
  obtain ⟨A', hVA, hdat, ha⟩ := hdata nl μ nn hn base U V B' g' α₀ t' hUG
    (fun l hl ρ x hx q0 q1 => ⟨(hrel l hl ρ x hx q0 q1).1, (hrel l hl ρ x hx q0 q1).2.1,
      (hrel l hl ρ x hx q0 q1).2.2.1⟩) (fun l hl x hx q0 => (hgl l hl x hx q0).1) hg'0
    (fun ρ x hx q0 q1 => ⟨(h0 ρ x hx q0 q1).1, (h0 ρ x hx q0 q1).2.1⟩) hbase hα₀ ht' (hα₀c.trans k1) (ht'c.trans k1)
  have hUg : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  have haa : ∀ l, l < nl → 0 ≤ 2 * (α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l)) ∧
      0 ≤ Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ ∧
      2 * (α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ (nl - l)) + Ko * t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ ≤
        (2 * α₀ + Ko * t') * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := fun l _ => by
    refine ⟨by positivity, by positivity, ?_⟩
    have := ha l
    nlinarith
  have hCe2 : C2 * (2 * α₀ + Ko * t') ≤ 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCe
  have hCe2' : C2' * (2 * α₀ + Ko * t') ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCe
  refine ⟨fun ν x hx q0 q1 => ?_, fun x hx q0 => ?_⟩
  · refine (hii nl μ nn hn base U V A' D _ _ s₀ (2 * α₀ + Ko * t') hUg
      (fun l hl ν x hx q0 q1 => (hVA l hl.le ν x hx q0 q1).1) hdat
      (fun l hl ρ x hx q0 q1 => (hrel l hl ρ x hx q0 q1).2.2.2) haa hs₀ (by positivity)
      (he.trans (min_le_left _ _)) hCe2 (fun ν x hx q0 q1 => (h0 ν x hx q0 q1).2.2) ν x hx q0 q1).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hii' nl μ nn hn base U V A' lam _ _ s₀' (2 * α₀ + Ko * t') hUg
      (fun l hl ν x hx q0 q1 => (hVA l hl.le ν x hx q0 q1).1) hdat
      (fun l hl x hx q0 => (hgl l hl x hx q0).2) haa hs₀' (by positivity)
      (he.trans (min_le_right _ _)) hCe2' hl0 x hx q0).trans ?_
    gcongr
    exact le_max_right _ _


lemma small_e3 {α₀ t' t c c' C Ko : ℝ} (hα₀ : 0 ≤ α₀) (ht' : 0 ≤ t') (ht : 0 ≤ t) (hKo : 0 ≤ Ko) (hC : 0 ≤ C)
    (hc : 0 < c) (hα₀c : α₀ ≤ c) (ht'c : t' ≤ c) (htc : t ≤ c) (h1 : c ≤ c' / (4 + Ko))
    (h2 : c ≤ 1 / ((C + 1) * (4 + Ko))) :
    2 * α₀ + Ko * t' ≤ c' ∧ 2 * t < c' ∧ C * (2 * α₀ + Ko * t' + 2 * t) ≤ 1 := by
  have hs : 2 * α₀ + Ko * t' + 2 * t ≤ (4 + Ko) * c := by nlinarith
  have hpos : 0 < 4 + Ko := by linarith
  have hc' : (4 + Ko) * c ≤ c' := by
    calc (4 + Ko) * c ≤ (4 + Ko) * (c' / (4 + Ko)) := by gcongr
      _ = c' := by field_simp
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  calc C * (2 * α₀ + Ko * t' + 2 * t) ≤ (C + 1) * ((4 + Ko) * c) := by
        have := mul_le_mul_of_nonneg_left hs hC
        nlinarith [mul_nonneg hpos.le hc.le]
    _ ≤ (C + 1) * ((4 + Ko) * (1 / ((C + 1) * (4 + Ko)))) := by gcongr
    _ = 1 := by field_simp

/-- **`prop:relative-average-order`(iii) from the data on `T^{(i)}`**: under the hypotheses of `order_data`, with the
forms `B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)` of the pair `(A', A)`, `‖B_0‖ ≤ tL^{-n}`, and their linear parts
`D_{l+1} = LQ(V_l)D_l`, `D_0 = B_0`, the remainder at the last level satisfies `‖C_n(𝐔; a_jA)(c)‖ =
‖B_n - D_n‖ ≤ 4C₂t²`, for `α₀, t', t ≤ c`. -/
theorem relative_average_order_iii (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C₂ : ℝ, 0 < c ∧ 0 ≤ C₂ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (B' B D : ∀ l, Fin 4 → Site (nn l) → Mat) (g' : ∀ l, Site (nn l) → GLN) (α₀ t' t : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h ∧
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        ‖B 0 ρ (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        D 0 ρ (img h (base 0) 0 x) = B 0 ρ (img h (base 0) 0 x)) →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → 0 ≤ t → α₀ ≤ c → t' ≤ c → t ≤ c →
      ∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        ‖B nl ν (img h (base nl) nl x) - D nl ν (img h (base nl) nl x)‖ ≤ 4 * C₂ * t ^ 2 := by
  obtain ⟨cd, Ko, hcd, hKo, hdata⟩ := order_data G hG hN h hh
  obtain ⟨c3, C3, C₂, hc3, hC3, hC₂, hiii⟩ := order_iii (N := N) h hh
  set c := min cd (min (c3 / (4 + Ko)) (1 / ((C3 + 1) * (4 + Ko))))
  have k1 : c ≤ cd := min_le_left _ _
  have k2 : c ≤ c3 / (4 + Ko) := (min_le_right _ _).trans (min_le_left _ _)
  have k3 : c ≤ 1 / ((C3 + 1) * (4 + Ko)) := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min hcd (lt_min (by positivity) (by positivity))
  refine ⟨c, C₂, hc0, hC₂, ?_⟩
  intro nl μ nn _ hn base U V B' B D g' α₀ t' t hUG hrel hgl hg'0 h0 hbase hα₀ ht' ht hα₀c ht'c htc
  obtain ⟨he, h2t, hCe⟩ := small_e3 hα₀ ht' ht hKo hC3 hc0 hα₀c ht'c htc k2 k3
  obtain ⟨A', hVA, hdat, ha⟩ := hdata nl μ nn hn base U V B' g' α₀ t' hUG
    (fun l hl ρ x hx q0 q1 => ⟨(hrel l hl ρ x hx q0 q1).1, (hrel l hl ρ x hx q0 q1).2.1,
      (hrel l hl ρ x hx q0 q1).2.2.1⟩) hgl hg'0
    (fun ρ x hx q0 q1 => ⟨(h0 ρ x hx q0 q1).1, (h0 ρ x hx q0 q1).2.1⟩) hbase hα₀ ht' (hα₀c.trans k1) (ht'c.trans k1)
  have hUg : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  intro ν x hx q0 q1
  have hb := hiii nl μ nn hn base U V A' B D _ _ t (2 * α₀ + Ko * t') hUg
    (fun l hl ν x hx q0 q1 => (hVA l hl.le ν x hx q0 q1).1) hdat
    (fun l hl ρ x hx q0 q1 => ⟨(hrel l hl ρ x hx q0 q1).2.2.2.1, (hrel l hl ρ x hx q0 q1).2.2.2.2⟩)
    (fun l _ => ⟨by positivity, by positivity, by have := ha l; nlinarith⟩) ht (by positivity) he h2t
    (by linarith) (fun ν x hx q0 q1 => ⟨(h0 ν x hx q0 q1).2.2.1, (h0 ν x hx q0 q1).2.2.2⟩) nl le_rfl ν x hx q0 q1
  refine hb.trans ?_
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hg := geom_partial hL3 nl nl le_rfl
  simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg ⊢
  have : 0 ≤ 8 * C₂ * t ^ 2 := by positivity
  nlinarith

/-- **`prop:relative-average-order`(v), the gauge directions, from the data on `T^{(i)}`**: under the hypotheses of
`order_data`, if `λ_{l+1} = Q'(V_l)λ_l`, `D_{l+1} = LQ(V_l)D_l` on the regions and `D_0 = D_{V_0}λ_0`, then at the last
level `D_n = D_{V_n}λ_n`, that is `Q_n(𝐔)D_𝐔 = D_{M^n(𝐔)}Q'_n(𝐔)`, for `α₀, t' ≤ c`. -/
theorem relative_average_order_v (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (B' D : ∀ l, Fin 4 → Site (nn l) → Mat) (lam : ∀ l, Site (nn l) → Mat) (g' : ∀ l, Site (nn l) → GLN)
      (α₀ t' : ℝ),
      (∀ l, IsGField G (U l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        U (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (U l) (img h (base l) l x) ρ h ∧
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (U l) (B' l) (img h (base l) l x) ρ h ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g' (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g' l (img h (base l) l x) * siteFactor (U l) (B' l) (img h (base l) l x) h ∧
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h) →
      (∀ z, g' 0 z = 1) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        V 0 ρ (img h (base 0) 0 x) = moveC (U 0) (B' 0) ρ (img h (base 0) 0 x) ∧
        ‖B' 0 ρ (img h (base 0) 0 x)‖ ≤ t' * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        D 0 ρ (img h (base 0) 0 x) = Ad (V 0 ρ (img h (base 0) 0 x)) (lam 0 (img h (base 0) 0 (x + Lz h ^ 0 •
          Pi.single ρ 1))) - lam 0 (img h (base 0) 0 x)) →
      (∀ μ' ν' x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Pi.single μ' 1) →
        Rg h nl μ 0 (x + Pi.single ν' 1) → Rg h nl μ 0 (x + Pi.single μ' 1 + Pi.single ν' 1) →
        hs (((plaq (U 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      0 ≤ α₀ → 0 ≤ t' → α₀ ≤ c → t' ≤ c →
      ∀ ρ x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ρ 1) →
        D nl ρ (img h (base nl) nl x) =
          Ad (V nl ρ (img h (base nl) nl x)) (lam nl (img h (base nl) nl (x + Lz h ^ nl • Pi.single ρ 1))) -
            lam nl (img h (base nl) nl x) := by
  obtain ⟨cd, Ko, hcd, hKo, hdata⟩ := order_data G hG hN h hh
  obtain ⟨cv, hcv, hv⟩ := order_v_gauge (N := N) h
  set c := min cd (cv / (2 + Ko))
  have k1 : c ≤ cd := min_le_left _ _
  have k2 : c ≤ cv / (2 + Ko) := min_le_right _ _
  have hc0 : 0 < c := lt_min hcd (by positivity)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V B' D lam g' α₀ t' hUG hrel hgl hg'0 h0 hbase hα₀ ht' hα₀c ht'c
  obtain ⟨A', hVA, hdat, ha⟩ := hdata nl μ nn hn base U V B' g' α₀ t' hUG
    (fun l hl ρ x hx q0 q1 => ⟨(hrel l hl ρ x hx q0 q1).1, (hrel l hl ρ x hx q0 q1).2.1,
      (hrel l hl ρ x hx q0 q1).2.2.1⟩) (fun l hl x hx q0 => (hgl l hl x hx q0).1) hg'0
    (fun ρ x hx q0 q1 => ⟨(h0 ρ x hx q0 q1).1, (h0 ρ x hx q0 q1).2.1⟩) hbase hα₀ ht' (hα₀c.trans k1) (ht'c.trans k1)
  have hUg : ∀ l, (U l).IsGaugeField := fun l => (hUG l).gauge
  have hpos : 0 < 2 + Ko := by linarith
  have hsm : (2 + Ko) * c ≤ cv := by
    calc (2 + Ko) * c ≤ (2 + Ko) * (cv / (2 + Ko)) := by gcongr
      _ = cv := by field_simp
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  exact hv nl μ nn hn base U V A' D lam _ _ hUg (fun l hl ν x hx q0 q1 => (hVA l hl.le ν x hx q0 q1).1) hdat
    (fun l hl => by
      have h1 := ha l
      have h2 := hp1 (nl - l)
      refine ⟨by positivity, by positivity, ?_, ?_⟩
      · nlinarith
      · nlinarith [mul_nonneg hKo ht'])
    (fun l hl ρ x hx q0 q1 => ⟨(hrel l hl ρ x hx q0 q1).2.1, (hrel l hl ρ x hx q0 q1).2.2.2⟩)
    (fun l hl x hx q0 => (hgl l hl x hx q0).2) (fun ρ x hx q0 q1 => (h0 ρ x hx q0 q1).2.2) nl le_rfl


/-! ### `(v)`: the covariance through the levels -/

/-- The conditions of `Qlin_D` and `Qlin_gauge` at the core's `𝐔`, from those at `𝐔_X` in the axial gauge. -/
theorem core_good (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
          GoodAt (moveC U A') y h ∧ GoodAt (moveC U A') (cPlus y μ h) h ∧ LoopsGood (moveC U A') y μ h ∧
          ∀ B : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → B ρ z = 0) →
            Qlin (moveC U A') y μ h B = 0 := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (ci / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ ci / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  have hcond := hpol y X 0 hXci (by rw [norm_zero]; exact hci)
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  refine ⟨?_, ?_, ?_, fun B hB => ?_⟩
  · refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g0)
    exact hag ν z ⟨Or.inl h1, Or.inl h2⟩
  · refine (goodAt_gauge hu).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g1)
    exact hag ν z ⟨Or.inr (bp_of_bm_plus hn2 h1), Or.inr (bp_of_bm_plus hn2 h2)⟩
  · refine (loopsGood_gauge hu).1 ((loopsGood_local hn2 fun ν z h1 h2 => ?_).2 hcond.l0)
    exact hag ν z ⟨h1, h2⟩
  · rw [Qlin_restrict hU hn hag hci (hpol y) hXci B]
    have : restrictF B (InBoxB y h μ) = 0 := by
      funext ν z
      by_cases hb : BoxBond y h μ ν z
      · rw [restrictF_box_apply _ hb, hB ν z hb]; rfl
      · rw [restrictF_box_apply' _ hb]; rfl
    rw [this, map_zero]

/-- **The covariance of one step for the core's `𝐔`**: for a unitary gauge transformation `u` and forms with
`D' = Ad_uD` on the box, `Q(𝐔^u)D' = Ad_{u(c₋)}Q(𝐔)D`. -/
theorem cov_core (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (u : Site n → GLN), (∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) →
        ∀ D D' : Fin 4 → Site n → Mat, (∀ ν z, BoxBond y h μ ν z → D' ν z = Ad (u z) (D ν z)) →
          Qlin ((moveC U A').gauge u) y μ h D' = Ad (u y) (Qlin (moveC U A') y μ h D) := by
  obtain ⟨c, hc, hgood⟩ := core_good (N := N) h μ
  refine ⟨c, hc, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA u hu D D' hD
  obtain ⟨hg, hg', hl, -⟩ := hgood U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA
  -- `𝐔^u` is the core's configuration for the gauge field `U^u` and the fluctuation `Ad_uA'`
  have hUu : (U.gauge u).IsGaugeField := fun ρ z => by
    simp only [Config.gauge, Units.val_mul]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu z) (hU ρ z)) (SupportCont.unitary_inv (hu _))
  have hplq' : ∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
      hs (((plaq (U.gauge u) μ' ν' z : GLN) : Mat) - 1) ≤ α₀ := fun μ' ν' z hz => by
    rw [plaq_gauge]
    have e : ((u z * plaq U μ' ν' z * (u z)⁻¹ : GLN) : Mat) - 1 =
        ((u z : GLN) : Mat) * (((plaq U μ' ν' z : GLN) : Mat) - 1) * (((u z)⁻¹ : GLN) : Mat) := by
      simp only [Units.val_mul]
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e, hs_unitary_mul _ _ _ (hu z) (SupportCont.unitary_inv (hu z))]
    exact hplq μ' ν' z hz
  have hA' : ∀ ρ z, BoxBond y h μ ρ z → ‖AdF u A' ρ z‖ ≤ α₁ := fun ρ z hb => by
    simp only [AdF]; rw [SupportCont.opNorm_Ad_unitary (hu z)]; exact hA ρ z hb
  obtain ⟨-, -, -, hzero⟩ := hgood (U.gauge u) hUu hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq' (AdF u A') hA'
  have hloc : Qlin ((moveC U A').gauge u) y μ h D' = Qlin ((moveC U A').gauge u) y μ h (AdF u D) := by
    rw [← moveC_gauge]
    rw [← sub_eq_zero, ← map_sub]
    exact hzero _ fun ρ z hb => by simp only [Pi.sub_apply, AdF, hD ρ z hb, sub_self]
  rw [hloc]
  exact Qlin_gauge u hg hg' hl
    (fun X => by rw [SupportCont.opNorm_Ad_unitary (hu y)]; linarith [norm_nonneg X])
    (fun X => by rw [SupportCont.opNorm_Ad_unitary (hu _)]; linarith [norm_nonneg X]) D


/-- **`prop:relative-average-order`(v), the covariance**: under the per-level hypotheses, for unitary gauge
transformations `u_l` of the levels, `u_{l+1}` the restriction of `u_l` to the sites of the next level, the
backgrounds `V'_l = V_l^{u_l}` on the regions, and the linear parts `D_{l+1} = LQ(V_l)D_l`, `D'_{l+1} = LQ(V'_l)D'_l`
with `D'_0 = Ad_{u_0}D_0`, `D'_l = Ad_{u_l}D_l` on the region of every level: `Q_n(𝐔^u)Ad_u = Ad_uQ_n(𝐔)`. -/
theorem order_v_cov (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V V' : ∀ l, Config N (nn l))
      (A' D D' : ∀ l, Fin 4 → Site (nn l) → Mat) (u : ∀ l, Site (nn l) → GLN) (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l z, ((u l z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        V' l ν (img h (base l) l x) = (V l).gauge (u l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        u (l + 1) (img h (base (l + 1)) (l + 1) x) = u l (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) ∧
        D' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V' l) (img h (base l) l x) ρ h (D' l)) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        D' 0 ρ (img h (base 0) 0 x) = Ad (u 0 (img h (base 0) 0 x)) (D 0 ρ (img h (base 0) 0 x))) →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        D' l ρ (img h (base l) l x) = Ad (u l (img h (base l) l x)) (D l ρ (img h (base l) l x)) := by
  classical
  choose cc hcc hcov using fun ρ : Fin 4 => cov_core (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cc
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcc ρ
  have hcle : ∀ ρ, c ≤ cc ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V V' A' D D' u a₀ a₁ hU hu hVV hdat ha hurel hDD hD0 l
  induction l with
  | zero => intro _; exact hD0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    obtain ⟨hD, hD'⟩ := hDD l hll ρ x hx q0 q1
    set y := img h (base l) l x
    have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = moveC (U l) (A' l) ν z ∧ V' l ν z = ((moveC (U l) (A' l)).gauge (u l)) ν z :=
      fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        obtain ⟨e1, e2⟩ := hVV l hll ν x' hx' r0 r1
        refine ⟨e1, ?_⟩
        rw [e2, Config.gauge, Config.gauge, e1]
    have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by
      simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 fun ν z h1 h2 => (hbox ν z h1 h2).1]
    have hQ' : Qlin (V' l) y ρ h = Qlin ((moveC (U l) (A' l)).gauge (u l)) y ρ h := by
      simp only [Qlin, relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 fun ν z h1 h2 => (hbox ν z h1 h2).2]
    have hDb : ∀ ν z, BoxBond y h ρ ν z → D' l ν z = Ad (u l z) (D l ν z) := fun ν z hb => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact ih (by omega) ν x' hx' r0 r1
    have hstep := hcov ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
      hpl (A' l) hA (u l) (hu l) (D l) (D' l) hDb
    rw [hD', hD, hQ', hQ, hstep, hurel l hll x hx q0, Ad_smul]


/-- **`prop:relative-average-order`(v), the covariance of `Q'_n`**: with the hypotheses of `order_v_cov`, block
averages `λ_{l+1} = Q'(V_l)λ_l`, `λ'_{l+1} = Q'(V'_l)λ'_l` on the regions and `λ'_0 = Ad_{u_0}λ_0` give
`λ'_l = Ad_{u_l}λ_l` on the region of every level: `Q'_n(𝐔^u)Ad_u = Ad_uQ'_n(𝐔)`. -/
theorem order_v_cov_Q' (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V V' : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (lam lam' : ∀ l, Site (nn l) → Mat) (u : ∀ l, Site (nn l) → GLN)
      (a₀ a₁ : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l z, ((u l z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        V' l ν (img h (base l) l x) = (V l).gauge (u l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        u (l + 1) (img h (base (l + 1)) (l + 1) x) = u l (img h (base l) l x) ∧
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h ∧
        lam' (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V' l) (lam' l) (img h (base l) l x) h) →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x →
        lam' 0 (img h (base 0) 0 x) = Ad (u 0 (img h (base 0) 0 x)) (lam 0 (img h (base 0) 0 x))) →
      ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        lam' l (img h (base l) l x) = Ad (u l (img h (base l) l x)) (lam l (img h (base l) l x)) := by
  classical
  choose cg hcg hgood using fun ρ : Fin 4 => core_good (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cg
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcg ρ
  have hcle : ∀ ρ, c ≤ cg ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V V' A' lam lam' u a₀ a₁ hU hu hVV hdat ha hrel hl0 l
  induction l with
  | zero => intro _; exact hl0
  | succ l ih =>
    intro hl x hx hR
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hx hR
    obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
    obtain ⟨hurel, hlam, hlam'⟩ := hrel l hll x hx hR
    set y := img h (base l) l x'
    set z₀ := ofs y (endW h μ b)
    obtain ⟨hg, hg', -, -⟩ := hgood μ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle μ))
      (ha1c.trans (hcle μ)) hpl (A' l) hA
    have hgz : GoodAt (moveC (U l) (A' l)) z₀ h := by
      cases b
      · simpa only [z₀, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using hg
      · exact hg'
    -- the backgrounds on the block of `z₀`
    have hbm : ∀ ν z, Bm z₀ h z → Bm z₀ h (z + unit (nn l) ν) →
        V l ν z = moveC (U l) (A' l) ν z ∧ V' l ν z = ((moveC (U l) (A' l)).gauge (u l)) ν z :=
      fun ν z h1 h2 => by
        obtain ⟨x'', hx'', s0, s1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
        obtain ⟨e1, e2⟩ := hVV l hll ν x'' hx'' s0 s1
        refine ⟨e1, ?_⟩
        rw [e2, Config.gauge, Config.gauge, e1]
    have hT : ∀ xx, trans (V l) z₀ h xx = trans (moveC (U l) (A' l)) z₀ h xx :=
      trans_local hn2 fun ν z h1 h2 => (hbm ν z h1 h2).1
    have hT' : ∀ xx, trans (V' l) z₀ h xx = trans ((moveC (U l) (A' l)).gauge (u l)) z₀ h xx :=
      trans_local hn2 fun ν z h1 h2 => (hbm ν z h1 h2).2
    -- `λ'_l = Ad_uλ_l` on the block of `z₀`
    have hlb : ∀ xx : Pts h, lam' l (ofs z₀ (offP h xx)) = Ad (u l (ofs z₀ (offP h xx)))
        (lam l (ofs z₀ (offP h xx))) := fun xx => by
      obtain ⟨x'', hx'', s0, e⟩ := box_pt (base l) hx' r0 r1 (bmp_of_end hn2 b (bm_ofs hn2 (offP_inM h xx)))
      rw [e]; exact ih (by omega) x'' hx'' s0
    have hcov := blockAvg_gauge (moveC (U l) (A' l)) (u l) (lam l) z₀ h
      (fun X => by rw [SupportCont.opNorm_Ad_unitary (hu l _)]; linarith [norm_nonneg X]) hgz.expsG_le
    rw [hlam', hlam, hurel, hb]
    have e1 : blockAvg (V' l) (lam' l) z₀ h =
        blockAvg ((moveC (U l) (A' l)).gauge (u l)) (fun z => Ad (u l z) (lam l z)) z₀ h := by
      simp only [blockAvg, hT', hlb]
    have e2 : blockAvg (V l) (lam l) z₀ h = blockAvg (moveC (U l) (A' l)) (lam l) z₀ h := by
      simp only [blockAvg, hT]
    rw [e1, e2, hcov]


/-! ### The transports of the gauge fields lie in `G` -/

/-- **The transports of `U_l` lie in `G`** (used in `lem:block-average-transports`): for a field with values in `G`
whose plaquettes on the blocks of the bond are at most `α₀ ≤ c`, the transports `U(c_±, x)` lie in `G`, so that
`Ad_{U(c_±,x)}` preserves both norms; `c` depends on `L` and `G` only. The quotients of the paths are conjugate by the
axial gauge to those of `e^{iX}`, `X` small, which lie within the radius of `G_radius`. -/
theorem trans_mem_G (G : GaugeGroup N) (hG : IsClosed G.mats) (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ : ℝ),
        0 ≤ α₀ → α₀ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ (b : Bool) (x : Pts h), trans U (ofs y (endW h μ b)) h x ∈ G.carrier := by
  obtain ⟨r, hr, htr, -⟩ := G_radius (N := N) G hG
  obtain ⟨cq, hcq, hcondG⟩ := uniform_condG (N := N) hr h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (cq / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ cq / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro n _ U hU hn y α₀ hα₀ hα₀c hplq b x
  classical
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hUg := hU.gauge
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
  -- the quotients at `z₀` are those of `𝐔_X`, conjugated by `u(z₀)`
  have hloc : ∀ x' Γ, holG (U.gauge u) z₀ h x' Γ = holG (UX (N := N) X) z₀ h x' Γ :=
    holG_local hn2 fun ν z h1 h2 => hag ν z (boxBond_of_end hn2 b h1 h2)
  refine htr hU fun i => ?_
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


/-- **The covariance of `(1/i) log 𝓜` for the core's `𝐔`**: for a unitary gauge transformation `u` and forms with
`B' = Ad_uB` on the box and `‖B‖_{∞,box} < c`, `(1/i) log 𝓜_{𝐔^u}(B')(c) = Ad_{u(c₋)}(1/i) log 𝓜_𝐔(B)(c)`. -/
theorem relLog_cov_core (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (u : Site n → GLN), (∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) →
        ∀ B B' : Fin 4 → Site n → Mat, (∀ ν z, BoxBond y h μ ν z → B' ν z = Ad (u z) (B ν z)) →
          ‖restrictF B (InBoxB y h μ)‖ < c →
          relLog ((moveC U A').gauge u) B' y μ h = Ad (u y) (relLog (moveC U A') B y μ h) := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA u hu B B' hB' hBc
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  have hXci : ‖X‖ < ci := by linarith
  set ua := uG U y h
  have hua : ∀ z, ((ua z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  set R := restrictF B (InBoxB y h μ)
  have hRn : ‖AdF ua R‖ < ci := by rw [norm_AdF_unitary hua]; linarith
  have hcond := hpol y X (AdF ua R) hXci hRn
  set W := moveC U A'
  -- `GoodAt` at `𝐔` and at `e^{iB}𝐔`, at both ends
  have hboxR : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      ((moveC W R).gauge ua) ν z = moveC (UX (N := N) X) (AdF ua R) ν z := fun ν z h1 h2 => by
    rw [← moveC_gauge]
    simp only [moveC]
    rw [hag ν z ⟨h1, h2⟩]
  have hWB : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      moveC W B ν z = moveC W R ν z := fun ν z h1 h2 => by
    simp only [moveC, R, restrictF_box_apply B ⟨h1, h2⟩]
  have hgW : GoodAt W y h := by
    refine (goodAt_gauge hua).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g0)
    exact hag ν z ⟨Or.inl h1, Or.inl h2⟩
  have hgW' : GoodAt W (cPlus y μ h) h := by
    refine (goodAt_gauge hua).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.g1)
    exact hag ν z ⟨Or.inr (bp_of_bm_plus hn2 h1), Or.inr (bp_of_bm_plus hn2 h2)⟩
  have hgB : GoodAt (moveC W B) y h := by
    refine (goodAt_local hn2 fun ν z h1 h2 => hWB ν z (Or.inl h1) (Or.inl h2)).2 ?_
    refine (goodAt_gauge hua).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.gA0)
    exact hboxR ν z (Or.inl h1) (Or.inl h2)
  have hgB' : GoodAt (moveC W B) (cPlus y μ h) h := by
    refine (goodAt_local hn2 fun ν z h1 h2 =>
      hWB ν z (Or.inr (bp_of_bm_plus hn2 h1)) (Or.inr (bp_of_bm_plus hn2 h2))).2 ?_
    refine (goodAt_gauge hua).1 ((goodAt_local hn2 fun ν z h1 h2 => ?_).2 hcond.gA1)
    exact hboxR ν z (Or.inr (bp_of_bm_plus hn2 h1)) (Or.inr (bp_of_bm_plus hn2 h2))
  -- `B' = Ad_uB` on the box
  have hloc : relLog (W.gauge u) B' y μ h = relLog (W.gauge u) (AdF u B) y μ h := by
    rw [relLog_box hn2 (W.gauge u) y μ B', relLog_box hn2 (W.gauge u) y μ (AdF u B)]
    congr 1
    funext ν z
    by_cases hb : BoxBond y h μ ν z
    · rw [restrictF_box_apply _ hb, restrictF_box_apply _ hb, hB' ν z hb]; rfl
    · rw [restrictF_box_apply' _ hb, restrictF_box_apply' _ hb]
  have hcov := relAvg_gauge W u B y μ h
    (fun X => by rw [SupportCont.opNorm_Ad_unitary (hu y)]; linarith [norm_nonneg X])
    (fun X => by rw [SupportCont.opNorm_Ad_unitary (hu _)]; linarith [norm_nonneg X])
    hgW.expsG_le hgB.expsG_le hgW'.expsG_le hgB'.expsG_le
  rw [hloc]
  simp only [relLog]
  rw [hcov]
  have e : ((u y * relAvg W B y μ h * (u y)⁻¹ : GLN) : Mat) = Ad (u y) ((relAvg W B y μ h : GLN) : Mat) := by
    simp only [Ad, Units.val_mul]
  rw [e, LogM_conj, Ad_smul]


/-- **`prop:relative-average-order`(v), the covariance of the forms and of `C_n`**: under the per-level hypotheses,
with forms `B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)` at most `s_l < c` on the regions, unitary gauge transformations `u_l`
(restrictions of each other), `V'_l = V_l^{u_l}`, and `B'_{l+1} = (1/i) log 𝓜_{V'_l}(B'_l)` with `B'_0 = Ad_{u_0}B_0`,
`B'_l = Ad_{u_l}B_l` on the region of every level. With `order_v_cov` for the linear parts, the remainders
`C_n = B_n - D_n` satisfy `C_n(𝐔^u; Ad_u ·) = Ad_uC_n(𝐔; ·)`. -/
theorem order_v_cov_forms (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V V' : ∀ l, Config N (nn l))
      (A' B B' : ∀ l, Fin 4 → Site (nn l) → Mat) (u : ∀ l, Site (nn l) → GLN) (a₀ a₁ s : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l z, ((u l z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x) ∧
        V' l ν (img h (base l) l x) = (V l).gauge (u l) ν (img h (base l) l x) ∧
        ‖B l ν (img h (base l) l x)‖ ≤ s l) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧ s l < c) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        u (l + 1) (img h (base (l + 1)) (l + 1) x) = u l (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
        B' (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V' l) (B' l) (img h (base l) l x) ρ h) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        B' 0 ρ (img h (base 0) 0 x) = Ad (u 0 (img h (base 0) 0 x)) (B 0 ρ (img h (base 0) 0 x))) →
      ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
        B' l ρ (img h (base l) l x) = Ad (u l (img h (base l) l x)) (B l ρ (img h (base l) l x)) := by
  classical
  choose cc hcc hcov using fun ρ : Fin 4 => relLog_cov_core (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cc
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcc ρ
  have hcle : ∀ ρ, c ≤ cc ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U V V' A' B B' u a₀ a₁ s hU hu hVV hdat ha hurel hBB hB0 l
  induction l with
  | zero => intro _; exact hB0
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc⟩ := ha l hll
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    obtain ⟨hB, hB'⟩ := hBB l hll ρ x hx q0 q1
    set y := img h (base l) l x
    have hbox : ∀ ν z, (Bm y h z ∨ Bp y h ρ z) → (Bm y h (z + unit (nn l) ν) ∨ Bp y h ρ (z + unit (nn l) ν)) →
        V l ν z = moveC (U l) (A' l) ν z ∧ V' l ν z = ((moveC (U l) (A' l)).gauge (u l)) ν z :=
      fun ν z h1 h2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨h1, h2⟩
        obtain ⟨e1, e2, -⟩ := hVV l hll ν x' hx' r0 r1
        refine ⟨e1, ?_⟩
        rw [e2, Config.gauge, Config.gauge, e1]
    have hf := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 fun ν z h1 h2 => (hbox ν z h1 h2).1
    have hf' := relLog_fun_local (y := y) (μ := ρ) (h := h) hn2 fun ν z h1 h2 => (hbox ν z h1 h2).2
    have hDb : ∀ ν z, BoxBond y h ρ ν z → B' l ν z = Ad (u l z) (B l ν z) := fun ν z hb => by
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact ih (by omega) ν x' hx' r0 r1
    have hRB : ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ s l := by
      refine norm_restrictF_box_le hs0 fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact (hVV l hll ν x' hx' r0 r1).2.2
    have hstep := hcov ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
      hpl (A' l) hA (u l) (hu l) (B l) (B' l) hDb (lt_of_le_of_lt hRB (hsc.trans_le (hcle ρ)))
    rw [hB', hB, congrFun hf' (B' l), congrFun hf (B l), hstep, hurel l hll x hx q0]

end RelativeAverage
end CoreLean

end
