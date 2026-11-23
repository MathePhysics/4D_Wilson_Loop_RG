/-
`prop:relative-average-order` of BALABAN_CORE.tex (`38d86047b37e`): relative averages of higher order.

The lattices `T^{(i+l)}`, `0 ≤ l ≤ n`, are the tori `Site (nn l)`, and the points of `T^{(i+l)}` are given by their
coordinates `x` in the units of `T^{(i)}` (divisible by `L^l`), with the sites `img h (base l) l x`, as in
`RegularAveragesII.lean`. The bond `c` of `T^{(j)}`, `j = i + n`, has its lower end at the origin and the direction
`μ`; the region of the level `l` is the union of the blocks of order `n - l` of `c₋` and `c₊` (`InR h n μ μ l`).

* `avgM_moveC`, `avgM_step`: one step, `M((e^{iB}V)^g)(c) = (g v)(c₋) e^{iB'(c)} M(V)(c) (g v)(c₊)⁻¹` with
  `B' = (1/i) log 𝓜_V(B)` and the site factors `v` (`eq:average-of-product`).
* `gauge_form`: the induction of the gauge form `eq:order-gauge-form`, `M^l(e^{ia_iA}𝐔) = (e^{ia_{i+l}A^{(l)}}𝐔^{(l)})^{𝐠_l}`
  on the region of every level, with `𝐠_{l+1} = 𝐠_l 𝐰_{l+1}`.
-/
import CoreLean.RelativeAverageG
import CoreLean.RegularAveragesII

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference
  AxialStraightLattice BoxGeometry

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### One step -/

section Step

variable {n : ℕ} [NeZero n]

/-- `𝓜 = e^{iB'}` with `B' = (1/i) log 𝓜`, when `𝓜` is within `1` of `id`. -/
lemma expU_relLog {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {μ : Fin 4} {h : ℕ}
    (hr : ‖((relAvg V B y μ h : GLN) : Mat) - 1‖ < 1) :
    expU (Complex.I • relLog V B y μ h) = relAvg V B y μ h := by
  apply Units.ext
  rw [expU_val, relLog, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]
  exact exp_LogM hr

/-- **`eq:average-of-product`**: `M(e^{iB}V)(c) = v(c₋) e^{iB'(c)} M(V)(c) v(c₊)⁻¹`. -/
theorem avgM_moveC (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ)
    (hr : ‖((relAvg V B y μ h : GLN) : Mat) - 1‖ < 1) :
    avgM (moveC V B) y μ h = siteFactor V B y h * expU (Complex.I • relLog V B y μ h) * avgM V y μ h *
      (siteFactor V B (cPlus y μ h) h)⁻¹ := by
  rw [expU_relLog hr, relAvg]; group

/-- **One step of the gauge form**: `M((e^{iB}V)^g)(c) = (g v)(c₋) e^{iB'(c)} M(V)(c) (g v)(c₊)⁻¹`. -/
theorem avgM_step (V : Config N n) (B : Fin 4 → Site n → Mat) (g : Site n → GLN) (y : Site n) (μ : Fin 4)
    (h : ℕ) (hr : ‖((relAvg V B y μ h : GLN) : Mat) - 1‖ < 1) :
    avgM ((moveC V B).gauge g) y μ h = (g y * siteFactor V B y h) * expU (Complex.I • relLog V B y μ h) *
      avgM V y μ h * (g (cPlus y μ h) * siteFactor V B (cPlus y μ h) h)⁻¹ := by
  rw [avgM_gauge, avgM_moveC V B y μ h hr]; group

end Step

/-! ### The region of a level -/

/-- The region of the level `l`: the blocks of order `n - l` of `c₋ = 0` and `c₊ = Lⁿe_μ`. -/
abbrev Rg (h nl : ℕ) (μ : Fin 4) (l : ℕ) (x : Fin 4 → ℤ) : Prop := RegularAverages.InR h nl μ μ l x

/-- The bonds with both ends in the blocks of the ends of a bond of the level `l + 1` lie in the region of the
level `l`. -/
lemma rg_of_bond {h nl l : ℕ} {μ ρ : Fin 4} {x : Fin 4 → ℤ} (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) {w : Fin 4 → ℤ}
    (hw : LatticePaths.InBox (loD h) (hiD h ρ ρ) w) : Rg h nl μ l (x + Lz h ^ l • w) := by
  set Q : ℤ := Lz h ^ l with hQ
  have hQ0 : 0 < Q := pow_pos (Lz_pos h) l
  have hpow : Lz h ^ (l + 1) = Q * (2 * h + 1) := by rw [pow_succ, hQ]; rfl
  have hstep : Hw h nl l = Hw h nl (l + 1) + Q * h := Hw_step
  intro σ
  have a0 := h0 σ
  have a1 := h1 σ
  have hwσ := hw σ
  simp only [loD, hiD, or_self] at hwσ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hpow] at a1 ⊢
  rw [hstep]
  have hlo : Q * (-(h : ℤ)) ≤ Q * w σ := mul_le_mul_of_nonneg_left hwσ.1 hQ0.le
  by_cases hs1 : σ = ρ
  · subst hs1
    simp only [↓reduceIte] at hwσ
    simp only [↓reduceIte, mul_one] at a1
    have hhi : Q * w σ ≤ Q * (3 * h + 1) := mul_le_mul_of_nonneg_left hwσ.2 hQ0.le
    by_cases hm : w σ ≤ h
    · have : Q * w σ ≤ Q * h := mul_le_mul_of_nonneg_left hm hQ0.le
      constructor <;> nlinarith
    · push Not at hm
      have : Q * ((h : ℤ) + 1) ≤ Q * w σ := mul_le_mul_of_nonneg_left (by omega) hQ0.le
      constructor <;> nlinarith
  · simp only [hs1, ↓reduceIte] at hwσ
    have hhi : Q * w σ ≤ Q * h := mul_le_mul_of_nonneg_left hwσ.2 hQ0.le
    constructor <;> nlinarith

lemma lat_succ_le {h l : ℕ} {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) : Lat (Lz h) l x := fun σ =>
  (pow_dvd_pow (Lz h) (Nat.le_succ l)).trans (hx σ)

lemma lat_add_smul {h l : ℕ} {x : Fin 4 → ℤ} (hx : Lat (Lz h) l x) (w : Fin 4 → ℤ) :
    Lat (Lz h) l (x + Lz h ^ l • w) := fun σ => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact dvd_add (hx σ) (dvd_mul_right _ _)

/-- The upper end of the bond `img x` in the direction `ρ` of the level `l + 1`, on the torus of the level `l`. -/
lemma cPlus_img {n : ℕ} [NeZero n] {h l : ℕ} (y : Site n) {x : Fin 4 → ℤ} (hx : Lat (Lz h) l x) (ρ : Fin 4) :
    cPlus (img h y l x) ρ h = img h y l (x + Lz h ^ (l + 1) • Pi.single ρ 1) := by
  rw [cPlus, img_add y hx, shift_eq]

/-- A site of the blocks of a bond of the level `l + 1` is the image of a point of the region of the level `l`. -/
lemma box_site {n : ℕ} [NeZero n] {h nl l : ℕ} (hn : 4 * h + 4 ≤ n) {μ ρ : Fin 4} (y : Site n)
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) {ν : Fin 4} {z : Site n}
    (hb : BoxBond (img h y l x) h ρ ν z) :
    ∃ x', Lat (Lz h) l x' ∧ Rg h nl μ l x' ∧ Rg h nl μ l (x' + Lz h ^ l • Pi.single ν 1) ∧ z = img h y l x' := by
  obtain ⟨hm, hm'⟩ := box_bond hn hb
  set m := rep (img h y l x) h z
  have hxl := lat_succ_le hx
  refine ⟨x + Lz h ^ l • m, lat_add_smul hxl m, rg_of_bond h0 h1 hm, ?_, ?_⟩
  · have e : x + Lz h ^ l • m + Lz h ^ l • Pi.single ν 1 = x + Lz h ^ l • (m + Pi.single ν 1) := by
      rw [smul_add, add_assoc]
    rw [e]; exact rg_of_bond h0 h1 hm'
  · rw [← img_add y hxl, StraightExtension.ofs_rep]

/-! ### The gauge form -/

/-- **`eq:order-gauge-form`**: if the averages of the levels are `V_{l+1} = M(V_l)` (of `𝐔`) and `W_{l+1} = M(W_l)` (of
`e^{ia_iA}𝐔`), the forms `B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)`, and the gauge transformations `𝐠_{l+1} = 𝐠_l v_{V_l}(B_l)`, on
the regions, and `W_0 = (e^{iB_0}V_0)^{𝐠_0}`, then `W_l = (e^{iB_l}V_l)^{𝐠_l}` on the region of every level `l ≤ n`. -/
theorem gauge_form (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (hn : ∀ l, 4 * h + 4 ≤ nn l)
    (base : ∀ l, Site (nn l)) (V W : ∀ l, Config N (nn l)) (B : ∀ l, Fin 4 → Site (nn l) → Mat)
    (g : ∀ l, Site (nn l) → GLN)
    (hW0 : ∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
      W 0 ρ (img h (base 0) 0 x) = ((moveC (V 0) (B 0)).gauge (g 0)) ρ (img h (base 0) 0 x))
    (hV : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h)
    (hW : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      W (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (W l) (img h (base l) l x) ρ h)
    (hB : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h)
    (hg : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      g (l + 1) (img h (base (l + 1)) (l + 1) x) = g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h)
    (hr : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      ‖((relAvg (V l) (B l) (img h (base l) l x) ρ h : GLN) : Mat) - 1‖ < 1) :
    ∀ l, l ≤ nl → ∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
      W l ρ (img h (base l) l x) = ((moveC (V l) (B l)).gauge (g l)) ρ (img h (base l) l x) := by
  intro l
  induction l with
  | zero => intro _; exact hW0
  | succ l ih =>
    intro hl ρ x hx h0 h1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    have hxl := lat_succ_le hx
    set y := img h (base l) l x
    -- `W_l` agrees with `(e^{iB_l}V_l)^{𝐠_l}` on the blocks of the bond
    have hagree : avgM (W l) y ρ h = avgM ((moveC (V l) (B l)).gauge (g l)) y ρ h := by
      refine avgM_local hn2 fun ν z hz1 hz2 => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 ⟨hz1, hz2⟩
      exact ih (by omega) ν x' hx' r0 r1
    rw [hW l hll ρ x hx h0 h1, hagree, avgM_step _ _ _ _ _ _ (hr l hll ρ x hx h0 h1)]
    have hc : cPlus y ρ h = img h (base l) l (x + Lz h ^ (l + 1) • Pi.single ρ 1) := cPlus_img (base l) hxl ρ
    have hx1 : Lat (Lz h) (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) := lat_add_smul hx _
    rw [hc, ← hg l hll x hx h0, ← hg l hll _ hx1 h1, ← hB l hll ρ x hx h0 h1, ← hV l hll ρ x hx h0 h1,
      ← img_unit (base (l + 1)) hx ρ]
    simp only [Config.gauge, moveC, mul_assoc]


/-! ### The bound of one step -/

section StepBound

variable {n : ℕ} [NeZero n]

/-- **`L Q₀(U)` of a gauge field is at most `L` times the box norm**: a mean of the isometries `Ad_{U(Γ_b)}` over the
`L` bonds of a line. -/
theorem Q0L_unitary_bound {h : ℕ} (hn : 4 * h + 2 ≤ n) {U : Config N n} (hU : U.IsGaugeField) (y : Site n)
    (μ : Fin 4) [DecidablePred (InBoxB y h μ)] (B : Fin 4 → Site n → Mat) :
    ‖Q0L U y μ h B‖ ≤ ((2 * h + 1 : ℕ) : ℝ) * ‖restrictF B (InBoxB y h μ)‖ := by
  rw [Q0L_box hn U y μ B]
  set R := restrictF B (InBoxB y h μ)
  have hterm : ∀ (x : Pts h) (Γ : Ords (offP h x)) (j : ℕ),
      ‖Ad (U.hol (pathGb y μ h x Γ j)) (R μ (ofs y (offP h x) + j • unit n μ))‖ ≤ ‖R‖ := fun x Γ j => by
    rw [SupportCont.opNorm_Ad_unitary (hol_unitary' U hU _)]
    exact (norm_le_pi_norm (R μ) _).trans (norm_le_pi_norm R μ)
  have hL : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) := by positivity
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply]
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  have hx : ∀ x : Pts h, ‖((nG h x : ℂ))⁻¹ • ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (U.hol (pathGb y μ h x Γ j)) (R μ (ofs y (offP h x) + j • unit n μ))‖ ≤ ((2 * h + 1 : ℕ) : ℝ) * ‖R‖ :=
    fun x => by
      have hn0 : (0 : ℝ) < (nG h x : ℝ) := by exact_mod_cast card_ords_pos (offP h x)
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      have hs : ‖∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
          Ad (U.hol (pathGb y μ h x Γ j)) (R μ (ofs y (offP h x) + j • unit n μ))‖ ≤
          (nG h x : ℝ) * (((2 * h + 1 : ℕ) : ℝ) * ‖R‖) := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ Γ : Ords (offP h x), ‖∑ j ∈ Finset.range (2 * h + 1),
            Ad (U.hol (pathGb y μ h x Γ j)) (R μ (ofs y (offP h x) + j • unit n μ))‖ ≤
            ((2 * h + 1 : ℕ) : ℝ) * ‖R‖ := fun Γ => by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun j _ => hterm x Γ j).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        refine (Finset.sum_le_sum fun Γ _ => this Γ).trans ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc (nG h x : ℝ)⁻¹ * _ ≤ (nG h x : ℝ)⁻¹ * ((nG h x : ℝ) * (((2 * h + 1 : ℕ) : ℝ) * ‖R‖)) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = ((2 * h + 1 : ℕ) : ℝ) * ‖R‖ := by field_simp
  have hs : ‖∑ x : Pts h, ((nG h x : ℂ))⁻¹ • ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (U.hol (pathGb y μ h x Γ j)) (R μ (ofs y (offP h x) + j • unit n μ))‖ ≤
      ((2 * h + 1 : ℕ) : ℝ) ^ 4 * (((2 * h + 1 : ℕ) : ℝ) * ‖R‖) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => hx x).trans ?_
    rw [Finset.sum_const, Finset.card_univ, card_pts, nsmul_eq_mul]
    push_cast; ring_nf; rfl
  calc (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ * _ ≤ (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ *
        (((2 * h + 1 : ℕ) : ℝ) ^ 4 * (((2 * h + 1 : ℕ) : ℝ) * ‖R‖)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((2 * h + 1 : ℕ) : ℝ) * ‖R‖ := by field_simp

lemma norm_restrictF_box_le {y : Site n} {h : ℕ} {μ : Fin 4} [DecidablePred (InBoxB y h μ)]
    {A' : Fin 4 → Site n → Mat} {α : ℝ} (hα : 0 ≤ α) (hA : ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α) :
    ‖restrictF A' (InBoxB y h μ)‖ ≤ α :=
  (pi_norm_le_iff_of_nonneg hα).2 fun ρ => (pi_norm_le_iff_of_nonneg hα).2 fun z => by
    by_cases hb : BoxBond y h μ ρ z
    · rw [restrictF_box_apply _ hb]; exact hA ρ z hb
    · rw [restrictF_box_apply' _ hb, norm_zero]; exact hα

end StepBound

/-- **The bound of one step**: `‖(1/i) log 𝓜_𝐔(B)(c)‖ ≤ (L + C(α₀ + α₁))‖B‖_{∞,box} + C‖B‖²_{∞,box}`, for the core's
`𝐔 = e^{iaA'}U` and `‖B‖_{∞,box} < c`; `c, C` depend on `L` and `G` only. -/
theorem step_bound (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < c →
          ‖relLog (moveC U A') B y μ h‖ ≤
            (((2 * h + 1 : ℕ) : ℝ) + C * (α₀ + α₁)) * ‖restrictF B (InBoxB y h μ)‖ +
              C * ‖restrictF B (InBoxB y h μ)‖ ^ 2 := by
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨c7, C₇, hc7, hC₇, h7⟩ := relative_average_vii_box (N := N) h μ
  refine ⟨min cb c7, C₀ + C₇ + C₂, lt_min hcb hc7, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B hB
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hcb' : min cb c7 ≤ cb := min_le_left _ _
  have hc7' : min cb c7 ≤ c7 := min_le_right _ _
  set R := restrictF B (InBoxB y h μ)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  -- the three parts of the linear part
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ α₁ := fun ρ z _ => by
    simp only [Pi.zero_apply, norm_zero]; exact hα₁
  have hA0' : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ (0 : ℝ) := fun ρ z _ => by
    simp
  have h1 := h7 U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hc7') (hα₁c.trans hc7') hplq A' 0 hA' hA0 B
  rw [moveC_zero, sub_zero] at h1
  have hRA : ‖restrictF A' (InBoxB y h μ)‖ ≤ α₁ := norm_restrictF_box_le hα₁ hA'
  obtain ⟨h2, -, -⟩ := hbox U hU hn y α₀ 0 hα₀ le_rfl (hα₀c.trans hcb') hcb.le hplq 0 hA0' B
  rw [moveC_zero, add_zero] at h2
  have h3 := Q0L_unitary_bound hn2 hU y μ B
  obtain ⟨-, -, h4⟩ := hbox U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hcb') (hα₁c.trans hcb') hplq A' hA' B
  have h4' := (h4 (lt_of_lt_of_le hB hcb')).1
  -- assemble
  rw [linear_part]
  have hlin : ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ ≤ (Lr + (C₀ + C₇) * (α₀ + α₁)) * ‖R‖ := by
    have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B =
        (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B) +
        (((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B - Q0L U y μ h B) + Q0L U y μ h B := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3) |>.trans ?_
    have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
    have : C₇ * ‖restrictF A' (InBoxB y h μ)‖ * ‖R‖ ≤ C₇ * α₁ * ‖R‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRA hC₇) hR0
    nlinarith [mul_nonneg hC₀ hα₀, mul_nonneg hC₀ hα₁, mul_nonneg hC₇ hα₀, mul_nonneg (mul_nonneg hC₀ hα₁) hR0,
      mul_nonneg (mul_nonneg hC₇ hα₀) hR0]
  refine (norm_add_le _ _).trans ?_
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  calc _ ≤ (Lr + (C₀ + C₇) * (α₀ + α₁)) * ‖R‖ + C₂ * ‖R‖ ^ 2 := add_le_add hlin h4'
    _ ≤ (Lr + (C₀ + C₇ + C₂) * (α₀ + α₁)) * ‖R‖ + (C₀ + C₇ + C₂) * ‖R‖ ^ 2 := by
        have e1 : (C₀ + C₇) * (α₀ + α₁) * ‖R‖ ≤ (C₀ + C₇ + C₂) * (α₀ + α₁) * ‖R‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hR0
        have e2 : C₂ * ‖R‖ ^ 2 ≤ (C₀ + C₇ + C₂) * ‖R‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith


/-! ### The forms of the levels -/

/-- **The recursion of the bounds of the forms**: with per-level gauge fields `U_l`, backgrounds `V_l = e^{iA'_l}U_l`
on the regions, plaquettes at most `α₀⁽ˡ⁾` and `‖A'_l‖ ≤ α₁⁽ˡ⁾` on the blocks of the bonds of the next level, and
`B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)`, the forms satisfy `‖B_l‖ ≤ s_l` on the region of every level, where
`s_{l+1} = (L + C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))s_l + Cs_l²`, as long as `α₀⁽ˡ⁾, α₁⁽ˡ⁾ ≤ c` and `s_l < c`. -/
theorem forms_bound (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ s : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧ s l < c ∧
        s (l + 1) = (((2 * h + 1 : ℕ) : ℝ) + C * (a₀ l + a₁ l)) * s l + C * s l ^ 2) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ s 0) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖B l ν (img h (base l) l x)‖ ≤ s l := by
  classical
  -- the constants of one step, for the four directions
  choose cμ Cμ hcμ hCμ hstep using fun ρ : Fin 4 => step_bound (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cμ
  set C := Finset.univ.sup' Finset.univ_nonempty Cμ
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcμ ρ
  have hcle : ∀ ρ, c ≤ cμ ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cμ ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCμ 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' B a₀ a₁ s hU hVU hdat hB hsl hB0 l
  induction l with
  | zero => intro _; exact hB0
  | succ l ih =>
    intro hl ρ x hx h0 h1
    have hll : l < nl := by omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc, hsrec⟩ := hsl l hll
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    set y := img h (base l) l x
    -- the bound of `B_l` on the blocks of the bond
    have hRB : ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ s l := by
      refine norm_restrictF_box_le hs0 fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 hb
      exact ih (by omega) ν x' hx' r0 r1
    -- `V_l = e^{iA'_l}U_l` on the blocks of the bond
    have hrel : relLog (V l) (B l) y ρ h = relLog (moveC (U l) (A' l)) (B l) y ρ h := by
      simp only [relLog]
      rw [relAvg_local hn2 fun ν z hz1 hz2 => ⟨?_, rfl⟩]
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 ⟨hz1, hz2⟩
      exact hVU l hll ν x' hx' r0 r1
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx h0 h1
    have hst := hstep ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
      hpl (A' l) hA (B l) (lt_of_le_of_lt hRB (hsc.trans_le (hcle ρ)))
    rw [hB l hll ρ x hx h0 h1, hrel, hsrec]
    refine hst.trans ?_
    have hR0 : 0 ≤ ‖restrictF (B l) (InBoxB y h ρ)‖ := norm_nonneg _
    have hCa : Cμ ρ * (a₀ l + a₁ l) ≤ C * (a₀ l + a₁ l) := mul_le_mul_of_nonneg_right (hCle ρ) (by positivity)
    have hL0 : (0 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by positivity
    have e1 : (((2 * h + 1 : ℕ) : ℝ) + Cμ ρ * (a₀ l + a₁ l)) * ‖restrictF (B l) (InBoxB y h ρ)‖ ≤
        (((2 * h + 1 : ℕ) : ℝ) + C * (a₀ l + a₁ l)) * s l :=
      mul_le_mul (by linarith) hRB hR0 (by nlinarith [hC0])
    have e2 : Cμ ρ * ‖restrictF (B l) (InBoxB y h ρ)‖ ^ 2 ≤ C * s l ^ 2 :=
      mul_le_mul (hCle ρ) (pow_le_pow_left₀ hR0 hRB 2) (by positivity) hC0
    linarith


/-! ### The geometric series of the levels -/

/-- `Σ_{m<l} L^{-(n-m)} ≤ ½ L^{-(n-l)}` for `L ≥ 3`, `l ≤ n`. -/
lemma geom_partial {Lr : ℝ} (hL : 3 ≤ Lr) (n : ℕ) :
    ∀ l, l ≤ n → ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹ ≤ (1 / 2) * (Lr ^ (n - l))⁻¹ := by
  have hL0 : 0 < Lr := by linarith
  intro l
  induction l with
  | zero => intro _; simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ l ih =>
    intro hl
    rw [Finset.sum_range_succ]
    have h1 := ih (by omega)
    have e : (Lr ^ (n - l))⁻¹ = (Lr ^ (n - (l + 1)))⁻¹ * Lr⁻¹ := by
      rw [← mul_inv, ← pow_succ, show n - (l + 1) + 1 = n - l by omega]
    rw [e] at h1 ⊢
    have hp : 0 < (Lr ^ (n - (l + 1)))⁻¹ := by positivity
    have hi : Lr⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
    nlinarith

lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **The growth of the forms in the units of the final scale**: if `σ_{l+1} ≤ σ_l(1 + EL^{-(n-l)})` whenever
`σ_l ≤ 2t`, with `E ≤ 1` and `σ_0 ≤ t`, then `σ_l ≤ t exp(EΣ_{m<l}L^{-(n-m)}) ≤ 2t` (`eq:order-fluctuation-bound`). -/
theorem growth {Lr : ℝ} (hL : 3 ≤ Lr) (n : ℕ) (σ : ℕ → ℝ) {t E : ℝ} (ht : 0 ≤ t) (hE0 : 0 ≤ E) (hE : E ≤ 1)
    (hσ0 : ∀ l, 0 ≤ σ l) (h0 : σ 0 ≤ t)
    (hstep : ∀ l, l < n → σ l ≤ 2 * t → σ (l + 1) ≤ σ l * (1 + E * (Lr ^ (n - l))⁻¹)) :
    ∀ l, l ≤ n → σ l ≤ t * Real.exp (E * ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹) ∧ σ l ≤ 2 * t := by
  have hL0 : 0 < Lr := by linarith
  have hbound : ∀ l, l ≤ n → t * Real.exp (E * ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹) ≤ 2 * t := fun l hl => by
    have hs := geom_partial hL n l hl
    have hp : (Lr ^ (n - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have h2 : E * ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹ ≤ 1 / 2 := by
      have hs0 : 0 ≤ ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹ := Finset.sum_nonneg fun m _ => by positivity
      calc E * _ ≤ 1 * (1 / 2) := mul_le_mul hE (hs.trans (by linarith)) hs0 zero_le_one
        _ = 1 / 2 := by ring
    calc t * Real.exp _ ≤ t * Real.exp (1 / 2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) ht
      _ ≤ t * 2 := mul_le_mul_of_nonneg_left exp_half_le_two ht
      _ = 2 * t := by ring
  intro l
  induction l with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero, mul_one]
    exact ⟨h0, by linarith⟩
  | succ l ih =>
    intro hl
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hst := hstep l (by omega) h2
    have hfirst : σ (l + 1) ≤ t * Real.exp (E * ∑ m ∈ Finset.range (l + 1), (Lr ^ (n - m))⁻¹) := by
      rw [Finset.sum_range_succ, mul_add, Real.exp_add]
      refine hst.trans ?_
      have hx : 1 + E * (Lr ^ (n - l))⁻¹ ≤ Real.exp (E * (Lr ^ (n - l))⁻¹) := by
        have := Real.add_one_le_exp (E * (Lr ^ (n - l))⁻¹); linarith
      have hpos : 0 ≤ 1 + E * (Lr ^ (n - l))⁻¹ := by positivity
      calc σ l * (1 + E * (Lr ^ (n - l))⁻¹)
          ≤ (t * Real.exp (E * ∑ m ∈ Finset.range l, (Lr ^ (n - m))⁻¹)) * Real.exp (E * (Lr ^ (n - l))⁻¹) :=
            mul_le_mul h1 hx hpos (by positivity)
        _ = _ := by ring
    exact ⟨hfirst, hfirst.trans (hbound (l + 1) hl)⟩

/-- **`eq:order-fluctuation-bound`**: the forms of all levels satisfy `‖B_l‖ ≤ 2tL^{-(n-l)}` on the regions, where
`t = Lⁿ‖B_0‖` is the size of the fluctuation in the units of the final scale, provided the data of the levels are
at most `e₀L^{-(n-l)}`, `e₀ ≤ c`, `2t < c`, and `C(e₀ + 2t) ≤ 1`. -/
theorem order_forms (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ t → 0 ≤ e₀ → e₀ ≤ c → 2 * t < c → C * (e₀ + 2 * t) ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖B l ν (img h (base l) l x)‖ ≤ 2 * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨c, C, hc, hC, hfb⟩ := forms_bound (N := N) h
  refine ⟨c, C, hc, hC, ?_⟩
  intro nl μ nn _ hn base U V A' B a₀ a₁ t e₀ hU hVU hdat hB ha ht he0 he0c htc hCE hB0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  -- the recursion of the bounds
  let s : ℕ → ℝ := fun l => Nat.rec (t * (Lr ^ nl)⁻¹)
    (fun l sl => (Lr + C * (a₀ l + a₁ l)) * sl + C * sl ^ 2) l
  have hs0 : s 0 = t * (Lr ^ nl)⁻¹ := rfl
  have hsS : ∀ l, s (l + 1) = (Lr + C * (a₀ l + a₁ l)) * s l + C * s l ^ 2 := fun l => rfl
  set σ : ℕ → ℝ := fun l => Lr ^ (nl - l) * s l with hσ
  -- nonnegativity, for `l < nl` (the data are nonnegative there)
  have hsnn : ∀ l, l ≤ nl → 0 ≤ s l := by
    intro l
    induction l with
    | zero => intro _; rw [hs0]; positivity
    | succ l ih =>
      intro hl
      have := ih (by omega)
      obtain ⟨h1, h2, -⟩ := ha l (by omega)
      rw [hsS]; positivity
  have hstep : ∀ l, l < nl → σ l ≤ 2 * t →
      σ (l + 1) ≤ σ l * (1 + C * (e₀ + 2 * t) * (Lr ^ (nl - l))⁻¹) := fun l hl hσl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have hsl := hsnn l hl.le
    have hp : Lr ^ (nl - l) = Lr * Lr ^ (nl - (l + 1)) := by
      rw [← pow_succ', show nl - (l + 1) + 1 = nl - l by omega]
    have hq : 0 < Lr ^ (nl - (l + 1)) := by positivity
    have hsl' : s l = σ l * (Lr ^ (nl - l))⁻¹ := by
      simp only [hσ]; field_simp
    -- `s_l ≤ 2t L^{-(n-l)}`
    have hsl2 : s l ≤ 2 * t * (Lr ^ (nl - l))⁻¹ := by
      rw [hsl']; exact mul_le_mul_of_nonneg_right hσl (by positivity)
    have key : σ (l + 1) = σ l * (1 + C * (a₀ l + a₁ l + s l) / Lr) := by
      simp only [hσ]
      rw [hsS, hp]
      field_simp
      ring
    rw [key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsum : a₀ l + a₁ l + s l ≤ (e₀ + 2 * t) * (Lr ^ (nl - l))⁻¹ := by nlinarith
    have hL1 : 1 / Lr ≤ 1 := by rw [div_le_one hL0]; linarith
    have hnn : 0 ≤ C * (a₀ l + a₁ l + s l) := by positivity
    calc 1 + C * (a₀ l + a₁ l + s l) / Lr ≤ 1 + C * (a₀ l + a₁ l + s l) := by
          rw [div_eq_mul_one_div]
          nlinarith
      _ ≤ 1 + C * ((e₀ + 2 * t) * (Lr ^ (nl - l))⁻¹) := by
          have := mul_le_mul_of_nonneg_left hsum hC; linarith
      _ = _ := by ring
  have hσ0 : σ 0 ≤ t := by
    simp only [hσ, Nat.sub_zero, hs0]
    rw [mul_comm t, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  -- the growth of `σ`, with `σ` replaced by its values up to `nl` (where it is nonnegative)
  set σ' : ℕ → ℝ := fun l => if l ≤ nl then σ l else 0
  have hσ'nn : ∀ l, 0 ≤ σ' l := fun l => by
    simp only [σ']; split_ifs with hl
    · exact mul_nonneg (by positivity) (hsnn l hl)
    · exact le_rfl
  have hgrow := growth hL3 nl σ' ht (by positivity) hCE hσ'nn (by simpa [σ'] using hσ0) (fun l hl hl2 => by
    simp only [σ', show l ≤ nl from hl.le, show l + 1 ≤ nl from hl, ↓reduceIte] at hl2 ⊢
    exact hstep l hl hl2)
  have hs2 : ∀ l, l ≤ nl → s l ≤ 2 * t * (Lr ^ (nl - l))⁻¹ := fun l hl => by
    have h2 := (hgrow l hl).2
    simp only [σ', hl, ↓reduceIte, hσ] at h2
    have hp : 0 < Lr ^ (nl - l) := by positivity
    rw [le_mul_inv_iff₀ hp, mul_comm]; exact h2
  -- the hypotheses of the recursion
  have hcond : ∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧ s l < c ∧
      s (l + 1) = (Lr + C * (a₀ l + a₁ l)) * s l + C * s l ^ 2 := fun l hl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have hp : (Lr ^ (nl - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have he : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by nlinarith
    have hsl := hs2 l hl.le
    have hst : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by nlinarith
    refine ⟨h1, h2, by linarith, by linarith, hsnn l hl.le, by linarith, hsS l⟩
  have hb := hfb nl μ nn hn base U V A' B a₀ a₁ s hU hVU hdat hB hcond (by rw [hs0]; exact hB0)
  intro l hl ν x hx h0 h1
  exact (hb l hl ν x hx h0 h1).trans (hs2 l hl)


/-! ### The linear parts of higher order -/

/-- **The linear part of one step**: `‖LQ(𝐔)B‖ ≤ (L + C(α₀ + α₁))‖B‖_{∞,box}` for the core's `𝐔 = e^{iaA'}U`, for all `B`. -/
theorem linear_bound (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ ≤
            (((2 * h + 1 : ℕ) : ℝ) + C * (α₀ + α₁)) * ‖restrictF B (InBoxB y h μ)‖ := by
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨c7, C₇, hc7, hC₇, h7⟩ := relative_average_vii_box (N := N) h μ
  refine ⟨min cb c7, C₀ + C₇, lt_min hcb hc7, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hcb' : min cb c7 ≤ cb := min_le_left _ _
  have hc7' : min cb c7 ≤ c7 := min_le_right _ _
  set R := restrictF B (InBoxB y h μ)
  have hA0 : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ α₁ := fun ρ z _ => by
    simp only [Pi.zero_apply, norm_zero]; exact hα₁
  have hA0' : ∀ ρ z, BoxBond y h μ ρ z → ‖(0 : Fin 4 → Site n → Mat) ρ z‖ ≤ (0 : ℝ) := fun ρ z _ => by simp
  have h1 := h7 U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hc7') (hα₁c.trans hc7') hplq A' 0 hA' hA0 B
  rw [moveC_zero, sub_zero] at h1
  have hRA : ‖restrictF A' (InBoxB y h μ)‖ ≤ α₁ := norm_restrictF_box_le hα₁ hA'
  obtain ⟨h2, -, -⟩ := hbox U hU hn y α₀ 0 hα₀ le_rfl (hα₀c.trans hcb') hcb.le hplq 0 hA0' B
  rw [moveC_zero, add_zero] at h2
  have h3 := Q0L_unitary_bound hn2 hU y μ B
  have e : ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B =
      (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B) +
      (((2 * h + 1 : ℕ) : ℂ) • Qlin U y μ h B - Q0L U y μ h B) + Q0L U y μ h B := by abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3) |>.trans ?_
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  have : C₇ * ‖restrictF A' (InBoxB y h μ)‖ * ‖R‖ ≤ C₇ * α₁ * ‖R‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRA hC₇) hR0
  nlinarith [mul_nonneg hC₀ hα₀, mul_nonneg hC₀ hα₁, mul_nonneg hC₇ hα₀, mul_nonneg (mul_nonneg hC₀ hα₁) hR0,
    mul_nonneg (mul_nonneg hC₇ hα₀) hR0]

/-- **`prop:relative-average-order`(ii) for `Q_n`**: for forms related by the linear parts of the levels,
`D_{l+1} = LQ(V_l)D_l` on the regions, with the per-level data of `forms_bound`, `‖D_l‖ ≤ s_l` on the region of every
level, where `s_{l+1} = (L + C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))s_l`. -/
theorem linear_forms_bound (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ s : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧
        s (l + 1) = (((2 * h + 1 : ℕ) : ℝ) + C * (a₀ l + a₁ l)) * s l) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖D 0 ν (img h (base 0) 0 x)‖ ≤ s 0) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖D l ν (img h (base l) l x)‖ ≤ s l := by
  classical
  choose cμ Cμ hcμ hCμ hlin using fun ρ : Fin 4 => linear_bound (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cμ
  set C := Finset.univ.sup' Finset.univ_nonempty Cμ
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcμ ρ
  have hcle : ∀ ρ, c ≤ cμ ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cμ ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCμ 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' D a₀ a₁ s hU hVU hdat hD hsl hD0 l
  induction l with
  | zero => intro _; exact hD0
  | succ l ih =>
    intro hl ρ x hx h0 h1
    have hll : l < nl := by omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsrec⟩ := hsl l hll
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    set y := img h (base l) l x
    have hRD : ‖restrictF (D l) (InBoxB y h ρ)‖ ≤ s l := by
      refine norm_restrictF_box_le hs0 fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 hb
      exact ih (by omega) ν x' hx' r0 r1
    -- `Q(V_l) = Q(e^{iA'_l}U_l)` at the bond: the functions `B ↦ (1/i) log 𝓜` agree
    have hrel : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by
      have e : (fun B => relLog (V l) B y ρ h) = (fun B => relLog (moveC (U l) (A' l)) B y ρ h) := by
        funext B
        simp only [relLog]
        rw [relAvg_local hn2 fun ν z hz1 hz2 => ⟨?_, rfl⟩]
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 ⟨hz1, hz2⟩
        exact hVU l hll ν x' hx' r0 r1
      simp only [Qlin, e]
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx h0 h1
    have hst := hlin ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ)) (ha1c.trans (hcle ρ))
      hpl (A' l) hA (D l)
    rw [hD l hll ρ x hx h0 h1, hrel, hsrec]
    refine hst.trans ?_
    have hR0 : 0 ≤ ‖restrictF (D l) (InBoxB y h ρ)‖ := norm_nonneg _
    have hCa : Cμ ρ * (a₀ l + a₁ l) ≤ C * (a₀ l + a₁ l) := mul_le_mul_of_nonneg_right (hCle ρ) (by positivity)
    exact mul_le_mul (by linarith) hRD hR0 (by nlinarith [hC0])

/-- `∏_{l<n}(L + Cx_l) ≤ Lⁿ exp(CΣx_l/L)`. -/
lemma prod_le_exp {Lr C : ℝ} (hL : 0 < Lr) (hC : 0 ≤ C) (x : ℕ → ℝ) (hx : ∀ l, 0 ≤ x l) :
    ∀ n, ∏ l ∈ Finset.range n, (Lr + C * x l) ≤ Lr ^ n * Real.exp (C * (∑ l ∈ Finset.range n, x l) / Lr) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_succ]
    have h1 : Lr + C * x n ≤ Lr * Real.exp (C * x n / Lr) := by
      have := Real.add_one_le_exp (C * x n / Lr)
      have e : Lr * (C * x n / Lr + 1) = Lr + C * x n := by field_simp; ring
      nlinarith
    have hp : 0 ≤ ∏ l ∈ Finset.range n, (Lr + C * x l) :=
      Finset.prod_nonneg fun l _ => by have := hx l; positivity
    calc (∏ l ∈ Finset.range n, (Lr + C * x l)) * (Lr + C * x n)
        ≤ (Lr ^ n * Real.exp (C * (∑ l ∈ Finset.range n, x l) / Lr)) * (Lr * Real.exp (C * x n / Lr)) :=
          mul_le_mul ih h1 (by have := hx n; positivity) (by positivity)
      _ = Lr ^ n * Lr * Real.exp (C * (∑ l ∈ Finset.range n, x l + x n) / Lr) := by
          rw [mul_add, add_div, Real.exp_add]; ring


/-- **`prop:relative-average-order`(ii) for `Q_n`**: if the data of the levels are at most `e L^{-(n-l)}`, then the forms
of the linear parts satisfy `‖D_n‖ ≤ Lⁿ(1 + Ce)‖D_0‖`, that is `‖(Q_n(𝐔)A)(c)‖ ≤ (1 + Ce)‖A‖_{∞,𝖡_c}` in the units of
the scale of each form; `c, C` depend on `L` and `G` only. -/
theorem order_ii (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (s₀ e : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ s₀ → 0 ≤ e → e ≤ c → C * e ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖D 0 ν (img h (base 0) 0 x)‖ ≤ s₀) →
      ∀ ν x, Lat (Lz h) nl x → Rg h nl μ nl x → Rg h nl μ nl (x + Lz h ^ nl • Pi.single ν 1) →
        ‖D nl ν (img h (base nl) nl x)‖ ≤ (((2 * h + 1 : ℕ) : ℝ)) ^ nl * (1 + C * e) * s₀ := by
  obtain ⟨c, C, hc, hC, hlb⟩ := linear_forms_bound (N := N) h
  refine ⟨c, C, hc, hC, ?_⟩
  intro nl μ nn _ hn base U V A' D a₀ a₁ s₀ e hU hVU hdat hD ha hs₀ he he_c hCe hD0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  -- the product of the factors
  set x : ℕ → ℝ := fun l => if l < nl then a₀ l + a₁ l else 0 with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => by
    simp only [hx]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; linarith
    · exact le_rfl
  set s : ℕ → ℝ := fun l => s₀ * ∏ m ∈ Finset.range l, (Lr + C * x m) with hs
  have hcond : ∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧
      s (l + 1) = (Lr + C * (a₀ l + a₁ l)) * s l := fun l hl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have hp : (Lr ^ (nl - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have he1 : e * (Lr ^ (nl - l))⁻¹ ≤ e := by nlinarith
    refine ⟨h1, h2, by linarith, by linarith, ?_, ?_⟩
    · exact mul_nonneg hs₀ (Finset.prod_nonneg fun m _ => by have := hx0 m; positivity)
    · simp only [hs, Finset.prod_range_succ, hx, if_pos hl]; ring
  have hb := hlb nl μ nn hn base U V A' D a₀ a₁ s hU hVU hdat hD hcond (by simpa [hs] using hD0)
  intro ν y hy h0 h1
  refine (hb nl le_rfl ν y hy h0 h1).trans ?_
  -- `∏(L + Cx_l) ≤ Lⁿ exp(CΣx_l/L) ≤ Lⁿ(1 + Ce)`
  have hprod := prod_le_exp hL0 hC x hx0 nl
  have hsum : ∑ l ∈ Finset.range nl, x l ≤ e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    rw [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, x l ≤ ∑ l ∈ Finset.range nl, e * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            simp only [hx, if_pos (Finset.mem_range.1 hl)]; exact (ha l (Finset.mem_range.1 hl)).2.2
      _ = e * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left hg he
      _ = e / 2 := by ring
  have hexp : Real.exp (C * (∑ l ∈ Finset.range nl, x l) / Lr) ≤ 1 + C * e := by
    have hy0 : 0 ≤ C * (∑ l ∈ Finset.range nl, x l) / Lr :=
      div_nonneg (mul_nonneg hC (Finset.sum_nonneg fun l _ => hx0 l)) hL0.le
    have hy1 : C * (∑ l ∈ Finset.range nl, x l) / Lr ≤ C * e / 2 := by
      rw [div_le_iff₀ hL0]
      have := mul_le_mul_of_nonneg_left hsum hC
      nlinarith [mul_nonneg hC he]
    have := GroupMean.exp_small_le hy0 (hy1.trans (by linarith))
    linarith
  have hfin : s nl ≤ s₀ * (Lr ^ nl * (1 + C * e)) := by
    simp only [hs]
    exact mul_le_mul_of_nonneg_left (hprod.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) hs₀
  calc s nl ≤ s₀ * (Lr ^ nl * (1 + C * e)) := hfin
    _ = Lr ^ nl * (1 + C * e) * s₀ := by ring


/-! ### The gauge transformations of the levels -/

lemma rg_mono {h nl l : ℕ} {μ : Fin 4} {x : Fin 4 → ℤ} (hx : Rg h nl μ (l + 1) x) : Rg h nl μ l x := by
  have hstep : Hw h nl l = Hw h nl (l + 1) + Lz h ^ l * h := Hw_step
  have hp : 0 ≤ Lz h ^ l * (h : ℤ) := mul_nonneg (pow_pos (Lz_pos h) l).le (by positivity)
  intro σ
  have := hx σ
  constructor <;> linarith [this.1, this.2]

/-- `e^{iG}e^{iS} = e^{iΨ(G, S)}` with `‖Ψ(G, S)‖ ≤ ‖G‖ + ‖S‖ + C_Ψ‖G‖‖S‖`, for `‖G‖, ‖S‖ ≤ 1/32`. -/
lemma expU_mul_psi {G S : Mat} (hG : ‖G‖ ≤ 1 / 32) (hS : ‖S‖ ≤ 1 / 32) :
    expU (Complex.I • G) * expU (Complex.I • S) = expU (Complex.I • psi G S) ∧
      ‖psi G S‖ ≤ ‖G‖ + ‖S‖ + 256 * ‖G‖ * ‖S‖ := by
  refine ⟨Units.ext ?_, ?_⟩
  · rw [Units.val_mul, expU_val, expU_val, expU_val, exp_I_psi (by have := log_two_gt_eighth; linarith)]
  · have hP := GroupMean.norm_Phi_le hG hS
    have e : psi G S = G + S + GroupMean.Phi G S := by unfold GroupMean.Phi; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) hP)

/-- **The gauge transformations `𝐠_l = e^{iG_l}` of `eq:order-gauge-form`**: with `𝐠_0 = id`, `𝐠_{l+1} = 𝐠_l v_l` and the
exponents of the site factors at most `w_l`, `𝐠_l = e^{iG_l}` with `‖G_l‖ ≤ γ_l`, `γ_{l+1} = γ_l + w_l + C_Ψγ_lw_l`, on the
region of every level, as long as `γ_l, w_l ≤ 1/32`. -/
theorem gauge_chain (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l))
    (V : ∀ l, Config N (nn l)) (B : ∀ l, Fin 4 → Site (nn l) → Mat) (g : ∀ l, Site (nn l) → GLN)
    (γ w : ℕ → ℝ)
    (hg : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      g (l + 1) (img h (base (l + 1)) (l + 1) x) = g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h)
    (hg0 : ∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → g 0 (img h (base 0) 0 x) = 1)
    (hw : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      ‖sExp (V l) (B l) (img h (base l) l x) h‖ ≤ w l)
    (hγ0 : γ 0 = 0)
    (hγ : ∀ l, l < nl → 0 ≤ w l ∧ γ l ≤ 1 / 32 ∧ w l ≤ 1 / 32 ∧ γ (l + 1) = γ l + w l + 256 * γ l * w l) :
    ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
      ∃ G : Mat, g l (img h (base l) l x) = expU (Complex.I • G) ∧ ‖G‖ ≤ γ l := by
  intro l
  induction l with
  | zero =>
    intro _ x hx hR
    refine ⟨0, by rw [hg0 x hx hR, smul_zero]; exact (Units.ext (by rw [expU_val, NormedSpace.exp_zero]; rfl)).symm, ?_⟩
    rw [norm_zero, hγ0]
  | succ l ih =>
    intro hl x hx hR
    have hll : l < nl := by omega
    obtain ⟨hw0, hγ1, hw1, hrec⟩ := hγ l hll
    obtain ⟨G, hG, hGn⟩ := ih (by omega) x (lat_succ_le hx) (rg_mono hR)
    set S := (1 / Complex.I) • sExp (V l) (B l) (img h (base l) l x) h
    have hS : Complex.I • S = sExp (V l) (B l) (img h (base l) l x) h := by
      simp only [S, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]
    have hSn : ‖S‖ ≤ w l := by
      simp only [S, norm_smul, one_div, norm_inv, Complex.norm_I, _root_.inv_one, one_mul]
      exact hw l hll x hx hR
    obtain ⟨he, hpn⟩ := expU_mul_psi (hGn.trans hγ1) (hSn.trans hw1)
    refine ⟨psi G S, ?_, ?_⟩
    · rw [hg l hll x hx hR, hG, siteFactor_eq_sExp, ← hS, he]
    · rw [hrec]
      refine hpn.trans ?_
      have h1 : 256 * ‖G‖ * ‖S‖ ≤ 256 * γ l * w l :=
        mul_le_mul (mul_le_mul_of_nonneg_left hGn (by norm_num)) hSn (norm_nonneg _)
          (by have := (norm_nonneg G).trans hGn; positivity)
      linarith


/-! ### The site factors of the levels -/

/-- Every point of the region of the level `l` is an end of a bond of the level `l` in the direction `μ` with both
ends in the region: the region is a box of the lattice `Lˡℤ⁴` whose side in the direction `μ` is at least `Lˡ`. -/
lemma rg_end {h nl l : ℕ} {μ : Fin 4} {x : Fin 4 → ℤ} (hl : l ≤ nl) (hx : Lat (Lz h) l x) (hR : Rg h nl μ l x) :
    ∃ x', Lat (Lz h) l x' ∧ Rg h nl μ l x' ∧ Rg h nl μ l (x' + Lz h ^ l • Pi.single μ 1) ∧
      (x = x' ∨ x = x' + Lz h ^ l • Pi.single μ 1) := by
  set Q : ℤ := Lz h ^ l with hQ
  have hQ0 : 0 < Q := pow_pos (Lz_pos h) l
  have htop : Q ∣ Lz h ^ nl + Hw h nl l := dvd_add (pow_dvd_pow _ hl) (Hw_dvd hl)
  have hlen : Q ≤ Lz h ^ nl := pow_le_pow_right₀ (by unfold Lz; omega) hl
  have h2 := two_Hw h nl l
  by_cases hup : x μ + Q ≤ Lz h ^ nl + Hw h nl l
  · refine ⟨x, hx, hR, fun σ => ?_, Or.inl rfl⟩
    have a := hR σ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, or_self] at a ⊢
    by_cases hσ : σ = μ
    · subst hσ; simp only [↓reduceIte, mul_one] at a ⊢; constructor <;> linarith
    · simp only [hσ, ↓reduceIte, mul_zero, add_zero] at a ⊢; exact a
  · push Not at hup
    have hxt : x μ = Lz h ^ nl + Hw h nl l := by
      have a := (hR μ).2
      simp only [or_self, ↓reduceIte] at a
      rcases a.lt_or_eq with hlt | heq
      · exact absurd (dvd_step hQ0 htop (hx μ) hlt) (by omega)
      · exact heq
    set x' := x + Q • (Pi.single μ (-1) : Fin 4 → ℤ) with hx'
    have hsum : x' + Q • (Pi.single μ 1 : Fin 4 → ℤ) = x := by
      funext σ
      simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> ring
    have hRx' : Rg h nl μ l x' := fun σ => by
      have a := hR σ
      simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, or_self] at a ⊢
      by_cases hσ : σ = μ
      · subst hσ; simp only [↓reduceIte] at a ⊢; constructor <;> linarith
      · simp only [hσ, ↓reduceIte, mul_zero, add_zero] at a ⊢; exact a
    refine ⟨x', lat_add_smul hx _, hRx', ?_, Or.inr hsum.symm⟩
    rw [hsum]; exact hR

/-- **Locality of the exponents of the site factors** in the background. -/
lemma sExp_local_V {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    (B : Fin 4 → Site n → Mat) (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z) :
    sExp V B y h = sExp V' B y h := by
  have h1 : ∀ x, trans V y h x = trans V' y h x := trans_local hn hVV
  have h2 : ∀ x, trans (moveC V B) y h x = trans (moveC V' B) y h x := trans_local hn fun μ z hz hz' => by
    simp only [moveC, hVV μ z hz hz']
  simp only [sExp, h1, h2]

lemma norm_restrictF_le_of {n : ℕ} [NeZero n] {S : Site n → Prop} [DecidablePred S]
    {B : Fin 4 → Site n → Mat} {s : ℝ} (hs : 0 ≤ s) (hB : ∀ ν z, S z → S (z + unit n ν) → ‖B ν z‖ ≤ s) :
    ‖restrictF B S‖ ≤ s :=
  (pi_norm_le_iff_of_nonneg hs).2 fun ν => (pi_norm_le_iff_of_nonneg hs).2 fun z => by
    simp only [restrictF]
    split_ifs with hz
    · exact hB ν z hz.1 hz.2
    · rw [norm_zero]; exact hs


/-- The bonds with both ends in the block of an end of the bond `y → y + Le_μ` are bonds of its two blocks. -/
lemma boxBond_of_end {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ ν : Fin 4} (b : Bool)
    {z : Site n}
    (h1 : Bm (ofs y (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h z)
    (h2 : Bm (ofs y (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h (z + unit n ν)) :
    BoxBond y h μ ν z := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, ofs_zero] at h1 h2
    exact ⟨Or.inl h1, Or.inl h2⟩
  · simp only [↓reduceIte] at h1 h2
    exact ⟨Or.inr (bp_of_bm_plus hn h1), Or.inr (bp_of_bm_plus hn h2)⟩

/-- **The site factors of the levels**: under the hypotheses of `forms_bound`, with `‖B_l‖ ≤ s_l < c` on the region
of the level `l`, the exponents of the site factors of the step `l → l + 1` satisfy `‖S_l(z)‖ ≤ C s_l` at the sites `z`
of the region of the level `l + 1` (`prop:relative-average`(vi) at the ends of the bonds of the level `l + 1`). -/
theorem site_level (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ s : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧ s l < c) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖B l ν (img h (base l) l x)‖ ≤ s l) →
      ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        ‖sExp (V l) (B l) (img h (base l) l x) h‖ ≤ C * s l := by
  classical
  choose cμ Cμ hcμ hCμ hsite using fun p : Fin 4 × Bool =>
    relative_average_site (N := N) h p.1 (w := if p.2 then Pi.single p.1 ((2 * h + 1 : ℕ) : ℤ) else 0)
      (by split_ifs; exacts [Or.inr rfl, Or.inl rfl])
  set c := Finset.univ.inf' Finset.univ_nonempty cμ
  set C := Finset.univ.sup' Finset.univ_nonempty Cμ
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun p _ => hcμ p
  have hcle : ∀ p, c ≤ cμ p := fun p => Finset.inf'_le _ (Finset.mem_univ p)
  have hCle : ∀ p, Cμ p ≤ C := fun p => Finset.le_sup' _ (Finset.mem_univ p)
  have hC0 : 0 ≤ C := (hCμ (0, false)).trans (hCle _)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' B a₀ a₁ s hU hVU hdat hsl hBl l hl x hx hR
  obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsc⟩ := hsl l hl
  have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
  obtain ⟨x', hx', r0, r1, hxx⟩ := rg_end (by omega) hx hR
  obtain ⟨hpl, hA⟩ := hdat l hl μ x' hx' r0 r1
  obtain ⟨b, hb⟩ : ∃ b : Bool, img h (base l) l x =
      ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0) := by
    rcases hxx with rfl | rfl
    · exact ⟨false, by simp only [Bool.false_eq_true, ↓reduceIte, ofs_zero]⟩
    · exact ⟨true, by simp only [↓reduceIte]; exact (cPlus_img (base l) (lat_succ_le hx') μ).symm⟩
  rw [hb]
  -- the bonds of the block of the end lie in the region of the level `l`
  have hreg : ∀ ν z, Bm (ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h z →
      Bm (ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h (z + unit (nn l) ν) →
      ∃ x'', Lat (Lz h) l x'' ∧ Rg h nl μ l x'' ∧ Rg h nl μ l (x'' + Lz h ^ l • Pi.single ν 1) ∧
        z = img h (base l) l x'' := fun ν z h1 h2 =>
    box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
  have hloc : sExp (V l) (B l) (ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h =
      sExp (moveC (U l) (A' l)) (B l)
        (ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h :=
    sExp_local_V hn2 (B l) fun ν z h1 h2 => by
      obtain ⟨x'', hx'', q0, q1, rfl⟩ := hreg ν z h1 h2
      exact hVU l hl ν x'' hx'' q0 q1
  have hRB : ‖restrictF (B l)
      (Bm (ofs (img h (base l) l x') (if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0)) h)‖ ≤ s l :=
    norm_restrictF_le_of hs0 fun ν z h1 h2 => by
      obtain ⟨x'', hx'', q0, q1, rfl⟩ := hreg ν z h1 h2
      exact hBl l hl ν x'' hx'' q0 q1
  rw [hloc]
  have hst := hsite (μ, b) (U l) (hU l) (hn l) (img h (base l) l x') (a₀ l) (a₁ l) ha0 ha1
    (ha0c.trans (hcle _)) (ha1c.trans (hcle _)) hpl (A' l) hA (B l) (lt_of_le_of_lt hRB (hsc.trans_le (hcle _)))
  exact hst.trans (mul_le_mul (hCle _) hRB (norm_nonneg _) hC0)


/-- **The geometric bound of the gauge transformations**: if the exponents of the site factors of the step
`l → l + 1` are at most `K L^{-(n-l)}`, `K ≤ 1/256`, then `𝐠_l = e^{iG_l}` with `‖G_l‖ ≤ K L^{-(n-l)}` on the region of
every level: `‖G_{l+1}‖ ≤ ‖G_l‖(1 + C_Ψ‖W‖) + ‖W‖ ≤ 3K L^{-(n-l)} ≤ K L^{-(n-l-1)}`. -/
theorem gauge_geom (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l))
    (V : ∀ l, Config N (nn l)) (B : ∀ l, Fin 4 → Site (nn l) → Mat) (g : ∀ l, Site (nn l) → GLN)
    {Lr K : ℝ} (hL : 3 ≤ Lr) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 256)
    (hg : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      g (l + 1) (img h (base (l + 1)) (l + 1) x) = g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h)
    (hg0 : ∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → g 0 (img h (base 0) 0 x) = 1)
    (hw : ∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      ‖sExp (V l) (B l) (img h (base l) l x) h‖ ≤ K * (Lr ^ (nl - l))⁻¹) :
    ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
      ∃ G : Mat, g l (img h (base l) l x) = expU (Complex.I • G) ∧ ‖G‖ ≤ K * (Lr ^ (nl - l))⁻¹ := by
  have hL0 : 0 < Lr := by linarith
  intro l
  induction l with
  | zero =>
    intro _ x hx hR
    refine ⟨0, by rw [hg0 x hx hR, smul_zero]; exact (Units.ext (by rw [expU_val, NormedSpace.exp_zero]; rfl)).symm, ?_⟩
    rw [norm_zero]; positivity
  | succ l ih =>
    intro hl x hx hR
    have hll : l < nl := by omega
    set q := K * (Lr ^ (nl - l))⁻¹ with hq
    have hp1 : (Lr ^ (nl - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 / 256 := by
      calc q ≤ K * 1 := mul_le_mul_of_nonneg_left hp1 hK0
        _ ≤ 1 / 256 := by linarith
    have hnext : K * (Lr ^ (nl - (l + 1)))⁻¹ = Lr * q := by
      rw [hq, show nl - l = nl - (l + 1) + 1 by omega, pow_succ, mul_inv]
      field_simp
    obtain ⟨G, hG, hGn⟩ := ih (by omega) x (lat_succ_le hx) (rg_mono hR)
    set S := (1 / Complex.I) • sExp (V l) (B l) (img h (base l) l x) h
    have hS : Complex.I • S = sExp (V l) (B l) (img h (base l) l x) h := by
      simp only [S, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]
    have hSn : ‖S‖ ≤ q := by
      simp only [S, norm_smul, one_div, norm_inv, Complex.norm_I, _root_.inv_one, one_mul]
      exact hw l hll x hx hR
    obtain ⟨he, hpn⟩ := expU_mul_psi (hGn.trans (hq1.trans (by norm_num))) (hSn.trans (hq1.trans (by norm_num)))
    refine ⟨psi G S, ?_, ?_⟩
    · rw [hg l hll x hx hR, hG, siteFactor_eq_sExp, ← hS, he]
    · rw [hnext]
      refine hpn.trans ?_
      have h1 : 256 * ‖G‖ * ‖S‖ ≤ 256 * q * q :=
        mul_le_mul (mul_le_mul_of_nonneg_left hGn (by norm_num)) hSn (norm_nonneg _) (by positivity)
      have h2 : 256 * q * q ≤ q := by nlinarith
      nlinarith

/-- **`H(l)(c)` of `prop:relative-average-order`**: under the hypotheses of `order_forms`, the gauge transformations
`𝐠_{l+1} = 𝐠_l v_l`, `𝐠_0 = id`, of the levels are `𝐠_l = e^{iG_l}` with `‖G_l‖ ≤ C₁ t L^{-(n-l)}` on the region of
every level, as long as `C₁t ≤ 1/256`; the constants depend on `L` and `G` only. -/
theorem order_gauge (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B : ∀ l, Fin 4 → Site (nn l) → Mat) (g : ∀ l, Site (nn l) → GLN) (a₀ a₁ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h) →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → g 0 (img h (base 0) 0 x) = 1) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ t → 0 ≤ e₀ → e₀ ≤ c → 2 * t < c → C * (e₀ + 2 * t) ≤ 1 → C₁ * t ≤ 1 / 256 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x →
        ∃ G : Mat, g l (img h (base l) l x) = expU (Complex.I • G) ∧
          ‖G‖ ≤ C₁ * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ := by
  obtain ⟨cf, Cf, hcf, hCf, hof⟩ := order_forms (N := N) h hh
  obtain ⟨cs, Cs, hcs, hCs, hsl⟩ := site_level (N := N) h
  refine ⟨min cf cs, Cf, 2 * Cs, lt_min hcf hcs, hCf, by positivity, ?_⟩
  intro nl μ nn _ hn base U V A' B g a₀ a₁ t e₀ hU hVU hdat hB hg hg0 ha ht he0 he0c htc hCE hCt hB0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hforms := hof nl μ nn hn base U V A' B a₀ a₁ t e₀ hU hVU hdat hB ha ht he0
    (he0c.trans (min_le_left _ _)) (htc.trans_le (min_le_left _ _)) hCE hB0
  have hp1 : ∀ l, (Lr ^ (nl - l))⁻¹ ≤ 1 := fun l => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hsite := hsl nl μ nn hn base U V A' B a₀ a₁ (fun l => 2 * t * (Lr ^ (nl - l))⁻¹) hU hVU hdat
    (fun l hl => by
      obtain ⟨h1, h2, h3⟩ := ha l hl
      have he1 : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 l; nlinarith
      have hs1 : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 l; nlinarith
      have hcs' : e₀ ≤ cs := he0c.trans (min_le_right _ _)
      have hts : 2 * t < cs := htc.trans_le (min_le_right _ _)
      refine ⟨h1, h2, by linarith, by linarith, by positivity, by linarith⟩)
    (fun l hl => hforms l hl.le)
  refine gauge_geom h nl μ nn base V B g hL3 (by positivity) (by linarith) hg hg0 fun l hl x hx hR => ?_
  refine (hsite l hl x hx hR).trans (le_of_eq ?_)
  ring


/-! ### The block averages of one step -/

/-- The offset of the end `c₋` (`b = false`) or `c₊` (`b = true`) of the bond `y → y + Le_μ`. -/
abbrev endW (h : ℕ) (μ : Fin 4) (b : Bool) : Fin 4 → ℤ := if b then Pi.single μ ((2 * h + 1 : ℕ) : ℤ) else 0

/-- **`Q'(𝐔)` at an end of the bond in the reduction**: `(Q'(𝐔)λ)(c_±) = Ad_{u(c_±)⁻¹}(Q'(𝐔_X)Ad_uλ)(c_±)`. -/
theorem blockAvg_reduce_end {n : ℕ} [NeZero n] {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4}
    {A' X : Fin 4 → Site n → Mat} (hn : 4 * h + 4 ≤ n) (b : Bool)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    (hU : U.IsGaugeField) (hg : GoodAt (UX (N := N) X) (ofs y (endW h μ b)) h) (lam : Site n → Mat) :
    blockAvg (moveC U A') lam (ofs y (endW h μ b)) h =
      Ad (uG U y h (ofs y (endW h μ b)))⁻¹
        (blockAvg (UX (N := N) X) (fun z => Ad (uG U y h z) (lam z)) (ofs y (endW h μ b)) h) := by
  set z₀ := ofs y (endW h μ b)
  set u := uG U y h
  set W := (moveC U A').gauge u
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hm : ∀ ρ z, Bm z₀ h z → Bm z₀ h (z + unit n ρ) → W ρ z = UX X ρ z := fun ρ z h1 h2 =>
    hag ρ z (boxBond_of_end hn2 b h1 h2)
  have hY : ∀ x i, ‖expsG W z₀ h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hm x]; exact hg.expsG_le x i
  have hw : ∀ Z : Mat, ‖Ad ((fun z => (u z)⁻¹) z₀) Z‖ ≤ 2 * ‖Z‖ := fun Z => by
    rw [SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _))]; linarith [norm_nonneg Z]
  have hb := blockAvg_gauge W (fun z => (u z)⁻¹) (fun z => Ad (u z) (lam z)) z₀ h hw hY
  rw [gauge_gauge_inv] at hb
  have e : (fun z => Ad (u z)⁻¹ (Ad (u z) (lam z))) = lam := by
    funext z; rw [← Ad_mul', inv_mul_cancel]; simp [Ad]
  simp only [e] at hb
  rw [hb]
  simp only [blockAvg, trans_local hn2 hm]

/-- The block average of the trivial configuration is the mean over the block. -/
lemma norm_blockAvg_zero_le {n : ℕ} [NeZero n] (h : ℕ) (z₀ : Site n) {lam : Site n → Mat} {s : ℝ}
    (hl : ∀ x : Pts h, ‖lam (ofs z₀ (offP h x))‖ ≤ s) :
    ‖blockAvg (UX (N := N) 0) lam z₀ h‖ ≤ s := by
  have hp : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) ^ 4 := by positivity
  rw [UX_zero]
  simp only [blockAvg, trans_oneC, Ad_one]
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  have hcard : (Finset.univ : Finset (Pts h)).card = (2 * h + 1) ^ 4 := by
    rw [Finset.card_univ]; simp [Pts, Fintype.card_fun, Fintype.card_fin]
  have hsum : ‖∑ x : Pts h, lam (ofs z₀ (offP h x))‖ ≤ ((2 * h + 1 : ℕ) : ℝ) ^ 4 * s := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : Pts h, ‖lam (ofs z₀ (offP h x))‖ ≤ ∑ _x : Pts h, s := Finset.sum_le_sum fun x _ => hl x
      _ = ((2 * h + 1 : ℕ) : ℝ) ^ 4 * s := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  calc (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ‖∑ x : Pts h, lam (ofs z₀ (offP h x))‖
      ≤ (((2 * h + 1 : ℕ) : ℝ) ^ 4)⁻¹ * (((2 * h + 1 : ℕ) : ℝ) ^ 4 * s) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = s := by field_simp

/-- **One step of `Q'_n`**: `‖(Q'(e^{iaA'}U)λ)(c_±)‖ ≤ (1 + C(α₀ + α₁))‖λ‖_{∞,B(c_±)}` for the core's `𝐔`, with
`c, C` depending on `L` and `G` only. -/
theorem blockAvg_step (h : ℕ) (μ : Fin 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (b : Bool) (lam : Site n → Mat) (s : ℝ), 0 ≤ s → (∀ z, Bm (ofs y (endW h μ b)) h z → ‖lam z‖ ≤ s) →
          ‖blockAvg (moveC U A') lam (ofs y (endW h μ b)) h‖ ≤ (1 + C * (α₀ + α₁)) * s := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C, hr, hC, hlip⟩ := uniform_blockAvg_lip (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set m := min ci r with hm
  have hm0 : 0 < m := lt_min hci hr
  set c := min (m / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ m / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, C * K, by positivity, by positivity, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA b lam s hs0 hls
  classical
  obtain ⟨X, hXc, hXa, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ m / 2 := by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp
  have hmci : m ≤ ci := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hcond := hpol y X 0 (by linarith) (by rw [norm_zero]; exact hci)
  have hg : GoodAt (UX (N := N) X) (ofs y (endW h μ b)) h := by
    cases b
    · simpa only [endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] using hcond.g0
    · exact hcond.g1
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  rw [blockAvg_reduce_end hn b hag hU hg, SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _))]
  -- restrict the transported `0`-form to the block of the end
  set z₀ := ofs y (endW h μ b)
  set lamR : Site n → Mat := fun z => if Bm z₀ h z then Ad (uG U y h z) (lam z) else 0 with hlamR
  have hR : ∀ V : Config N n, blockAvg V (fun z => Ad (uG U y h z) (lam z)) z₀ h = blockAvg V lamR z₀ h :=
    fun V => by
      simp only [blockAvg, hlamR]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [if_pos (bm_ofs hn2 (offP_inM h x))]
  have hlamRn : ‖lamR‖ ≤ s := (pi_norm_le_iff_of_nonneg hs0).2 fun z => by
    simp only [hlamR]
    split_ifs with hz
    · rw [SupportCont.opNorm_Ad_unitary (hu z)]; exact hls z hz
    · rw [norm_zero]; exact hs0
  rw [hR]
  have h0 : ‖blockAvg (UX (N := N) 0) lamR z₀ h‖ ≤ s :=
    norm_blockAvg_zero_le h z₀ fun x => (norm_le_pi_norm lamR _).trans hlamRn
  have hl := hlip z₀ lamR X 0 (by linarith) (by rw [norm_zero]; exact hr.le)
  rw [sub_zero] at hl
  have hXn : ‖X‖ ≤ K * (α₀ + α₁) := hXa
  calc ‖blockAvg (UX (N := N) X) lamR z₀ h‖
      ≤ ‖blockAvg (UX (N := N) 0) lamR z₀ h‖ +
          ‖blockAvg (UX (N := N) X) lamR z₀ h - blockAvg (UX (N := N) 0) lamR z₀ h‖ := norm_le_insert' _ _
    _ ≤ s + C * ‖X‖ * ‖lamR‖ := add_le_add h0 hl
    _ ≤ s + C * (K * (α₀ + α₁)) * s := by
        have := mul_le_mul (mul_le_mul_of_nonneg_left hXn hC) hlamRn (norm_nonneg _)
          (mul_nonneg hC (by positivity))
        linarith
    _ = (1 + C * K * (α₀ + α₁)) * s := by ring


/-- A site of the blocks of a bond of the level `l + 1` is the image of a point of the region of the level `l`. -/
lemma box_pt {n : ℕ} [NeZero n] {h nl l : ℕ} {μ ρ : Fin 4} (y : Site n)
    {x : Fin 4 → ℤ} (hx : Lat (Lz h) (l + 1) x) (h0 : Rg h nl μ (l + 1) x)
    (h1 : Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1)) {z : Site n}
    (hz : Bm (img h y l x) h z ∨ Bp (img h y l x) h ρ z) :
    ∃ x', Lat (Lz h) l x' ∧ Rg h nl μ l x' ∧ z = img h y l x' := by
  have hm := inBox_of_bmp hz
  have hxl := lat_succ_le hx
  refine ⟨x + Lz h ^ l • rep (img h y l x) h z, lat_add_smul hxl _, rg_of_bond h0 h1 hm, ?_⟩
  rw [← img_add y hxl, StraightExtension.ofs_rep]

lemma bmp_of_end {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} (b : Bool) {z : Site n}
    (hz : Bm (ofs y (endW h μ b)) h z) : Bm y h z ∨ Bp y h μ z := by
  cases b
  · simp only [endW, Bool.false_eq_true, ↓reduceIte, ofs_zero] at hz; exact Or.inl hz
  · exact Or.inr (bp_of_bm_plus hn hz)

/-- A point of the region of the level `l + 1` is an end of a bond of the level `l + 1` in the direction `μ` with both
ends in the region, and its image on the torus of the level `l` is that end. -/
lemma rg_end_img {n : ℕ} [NeZero n] {h nl l : ℕ} {μ : Fin 4} (y : Site n) {x : Fin 4 → ℤ} (hl : l + 1 ≤ nl)
    (hx : Lat (Lz h) (l + 1) x) (hR : Rg h nl μ (l + 1) x) :
    ∃ x' b, Lat (Lz h) (l + 1) x' ∧ Rg h nl μ (l + 1) x' ∧ Rg h nl μ (l + 1) (x' + Lz h ^ (l + 1) • Pi.single μ 1) ∧
      img h y l x = ofs (img h y l x') (endW h μ b) := by
  obtain ⟨x', hx', r0, r1, hxx⟩ := rg_end hl hx hR
  refine ⟨x', ?_, hx', r0, r1, ?_⟩
  · exact if hxx' : x = x' then false else true
  · rcases hxx with rfl | rfl
    · simp only [↓reduceDIte, endW, Bool.false_eq_true, ↓reduceIte, ofs_zero]
    · have hne : x' + Lz h ^ (l + 1) • Pi.single μ 1 ≠ x' := by
        intro e
        have := congrFun e μ
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, add_eq_left] at this
        exact absurd this (pow_pos (Lz_pos h) _).ne'
      simp only [hne, ↓reduceDIte, endW, ↓reduceIte]
      exact (cPlus_img y (lat_succ_le hx') μ).symm

/-- **The block averages of the levels**: under the hypotheses of `forms_bound`, if `λ_{l+1} = Q'(V_l)λ_l` on the
regions, then `‖λ_l‖ ≤ s_l` on the region of every level, where `s_{l+1} = (1 + C(α₀⁽ˡ⁾ + α₁⁽ˡ⁾))s_l`. -/
theorem blockAvg_levels (h : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (lam : ∀ l, Site (nn l) → Mat) (a₀ a₁ s : ℕ → ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧
        s (l + 1) = (1 + C * (a₀ l + a₁ l)) * s l) →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → ‖lam 0 (img h (base 0) 0 x)‖ ≤ s 0) →
      ∀ l, l ≤ nl → ∀ x, Lat (Lz h) l x → Rg h nl μ l x → ‖lam l (img h (base l) l x)‖ ≤ s l := by
  classical
  choose cμ Cμ hcμ hCμ hstep using fun ρ : Fin 4 => blockAvg_step (N := N) h ρ
  set c := Finset.univ.inf' Finset.univ_nonempty cμ
  set C := Finset.univ.sup' Finset.univ_nonempty Cμ
  have hc0 : 0 < c := (Finset.lt_inf'_iff _).2 fun ρ _ => hcμ ρ
  have hcle : ∀ ρ, c ≤ cμ ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hCle : ∀ ρ, Cμ ρ ≤ C := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC0 : 0 ≤ C := (hCμ 0).trans (hCle 0)
  refine ⟨c, C, hc0, hC0, ?_⟩
  intro nl μ nn _ hn base U V A' lam a₀ a₁ s hU hVU hdat hlam hsl hl0 l
  induction l with
  | zero => intro _; exact hl0
  | succ l ih =>
    intro hl x hx hR
    have hll : l < nl := by omega
    obtain ⟨ha0, ha1, ha0c, ha1c, hs0, hsrec⟩ := hsl l hll
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨x', b, hx', r0, r1, hb⟩ := rg_end_img (base l) hl hx hR
    obtain ⟨hpl, hA⟩ := hdat l hll μ x' hx' r0 r1
    set z₀ := ofs (img h (base l) l x') (endW h μ b)
    -- locality of `Q'` in the background
    have hloc : blockAvg (V l) (lam l) z₀ h = blockAvg (moveC (U l) (A' l)) (lam l) z₀ h := by
      have ht := trans_local (V := V l) (V' := moveC (U l) (A' l)) hn2 (y := z₀) (h := h) fun ν z h1 h2 => by
        obtain ⟨x'', hx'', q0, q1, rfl⟩ := box_site (hn l) (base l) hx' r0 r1 (boxBond_of_end hn2 b h1 h2)
        exact hVU l hll ν x'' hx'' q0 q1
      simp only [blockAvg, ht]
    have hlb : ∀ z, Bm z₀ h z → ‖lam l z‖ ≤ s l := fun z hz => by
      obtain ⟨x'', hx'', q0, rfl⟩ := box_pt (base l) hx' r0 r1 (bmp_of_end hn2 b hz)
      exact ih (by omega) x'' hx'' q0
    rw [hlam l hll x hx hR, hb, hloc, hsrec]
    refine (hstep μ (U l) (hU l) (hn l) (img h (base l) l x') (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle μ))
      (ha1c.trans (hcle μ)) hpl (A' l) hA b (lam l) (s l) hs0 hlb).trans ?_
    have : Cμ μ * (a₀ l + a₁ l) ≤ C * (a₀ l + a₁ l) := mul_le_mul_of_nonneg_right (hCle μ) (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hs0


/-- **`prop:relative-average-order`(ii) for `Q'_n`**: if the data of the levels are at most `e L^{-(n-l)}`, then the
block averages `λ_{l+1} = Q'(V_l)λ_l` satisfy `‖λ_n(y)‖ ≤ (1 + Ce)‖λ_0‖_{∞,Bⁿ(y)}`, `‖(Q'_n(𝐔)λ)(y)‖ ≤
(1 + Ce)‖λ‖_{∞,Bⁿ(y)}`; `c, C` depend on `L` and `G` only. -/
theorem order_ii_Q' (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' : ∀ l, Fin 4 → Site (nn l) → Mat) (lam : ∀ l, Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (s₀ e : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        lam (l + 1) (img h (base (l + 1)) (l + 1) x) = blockAvg (V l) (lam l) (img h (base l) l x) h) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ s₀ → 0 ≤ e → e ≤ c → C * e ≤ 1 →
      (∀ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → ‖lam 0 (img h (base 0) 0 x)‖ ≤ s₀) →
      ∀ x, Lat (Lz h) nl x → Rg h nl μ nl x → ‖lam nl (img h (base nl) nl x)‖ ≤ (1 + C * e) * s₀ := by
  obtain ⟨c, C, hc, hC, hlb⟩ := blockAvg_levels (N := N) h
  refine ⟨c, C, hc, hC, ?_⟩
  intro nl μ nn _ hn base U V A' lam a₀ a₁ s₀ e hU hVU hdat hlam ha hs₀ he he_c hCe hl0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  set x : ℕ → ℝ := fun l => if l < nl then a₀ l + a₁ l else 0 with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => by
    simp only [hx]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; linarith
    · exact le_rfl
  set s : ℕ → ℝ := fun l => s₀ * ∏ m ∈ Finset.range l, (1 + C * x m) with hs
  have hcond : ∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c ∧ 0 ≤ s l ∧
      s (l + 1) = (1 + C * (a₀ l + a₁ l)) * s l := fun l hl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have hp : (Lr ^ (nl - l))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have he1 : e * (Lr ^ (nl - l))⁻¹ ≤ e := by nlinarith
    refine ⟨h1, h2, by linarith, by linarith, ?_, ?_⟩
    · exact mul_nonneg hs₀ (Finset.prod_nonneg fun m _ => by have := hx0 m; positivity)
    · simp only [hs, Finset.prod_range_succ, hx, if_pos hl]; ring
  have hb := hlb nl μ nn hn base U V A' lam a₀ a₁ s hU hVU hdat hlam hcond (by simpa [hs] using hl0)
  intro y hy hR
  refine (hb nl le_rfl y hy hR).trans ?_
  have hprod := prod_le_exp one_pos hC x hx0 nl
  simp only [one_pow, one_mul, div_one] at hprod
  have hsum : ∑ l ∈ Finset.range nl, x l ≤ e / 2 := by
    have hg := geom_partial hL3 nl nl le_rfl
    simp only [Nat.sub_self, pow_zero, _root_.inv_one, mul_one] at hg
    calc ∑ l ∈ Finset.range nl, x l ≤ ∑ l ∈ Finset.range nl, e * (Lr ^ (nl - l))⁻¹ :=
          Finset.sum_le_sum fun l hl => by
            simp only [hx, if_pos (Finset.mem_range.1 hl)]; exact (ha l (Finset.mem_range.1 hl)).2.2
      _ = e * ∑ l ∈ Finset.range nl, (Lr ^ (nl - l))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left hg he
      _ = e / 2 := by ring
  have hexp : Real.exp (C * ∑ l ∈ Finset.range nl, x l) ≤ 1 + C * e := by
    have hy0 : 0 ≤ C * ∑ l ∈ Finset.range nl, x l := mul_nonneg hC (Finset.sum_nonneg fun l _ => hx0 l)
    have hy1 : C * ∑ l ∈ Finset.range nl, x l ≤ C * e / 2 := by
      have := mul_le_mul_of_nonneg_left hsum hC; linarith
    have := GroupMean.exp_small_le hy0 (hy1.trans (by linarith))
    linarith
  calc s nl = s₀ * ∏ m ∈ Finset.range nl, (1 + C * x m) := rfl
    _ ≤ s₀ * (1 + C * e) := mul_le_mul_of_nonneg_left (hprod.trans hexp) hs₀
    _ = (1 + C * e) * s₀ := by ring


/-! ### `(iv)` and `(vi)` -/

/-- **The algebra of `(vi)`**: `‖e^{iG₋}e^{iB}V e^{-iG₊}V⁻¹ - id‖ ≤ 8(‖G₋‖ + ‖B‖ + ‖G₊‖)` for `‖G_±‖, ‖B‖ ≤ 1/32` and
`‖V‖, ‖V⁻¹‖ ≤ 2`. -/
theorem order_vi_alg {Gm Gp B : Mat} {V : GLN} (hGm : ‖Gm‖ ≤ 1 / 32) (hB : ‖B‖ ≤ 1 / 32) (hGp : ‖Gp‖ ≤ 1 / 32)
    (hV : ‖(V : Mat)‖ ≤ 2) (hVi : ‖((V⁻¹ : GLN) : Mat)‖ ≤ 2) :
    ‖((expU (Complex.I • Gm) * (expU (Complex.I • B) * V) * (expU (Complex.I • Gp))⁻¹ * V⁻¹ : GLN) : Mat) - 1‖ ≤
      8 * (‖Gm‖ + ‖B‖ + ‖Gp‖) := by
  obtain ⟨hm1, -⟩ := norm_exp_I_bounds hGm Complex.I (by simp)
  obtain ⟨hb1, hb2⟩ := norm_exp_I_bounds hB Complex.I (by simp)
  obtain ⟨hp1, -⟩ := norm_exp_I_bounds hGp (-Complex.I) (by simp)
  set Em := exp (Complex.I • Gm)
  set Eb := exp (Complex.I • B)
  set Ep := exp ((-Complex.I) • Gp)
  set Vm : Mat := (V : Mat)
  set Vi : Mat := ((V⁻¹ : GLN) : Mat)
  have hVVi : Vm * Vi = 1 := by simp only [Vm, Vi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((expU (Complex.I • Gm) * (expU (Complex.I • B) * V) * (expU (Complex.I • Gp))⁻¹ * V⁻¹ : GLN) : Mat) =
      Em * Eb * (Vm * Ep * Vi) := by
    simp only [Units.val_mul, expU_val, expU_inv_val, Em, Eb, Ep, Vm, Vi, neg_smul]
    noncomm_ring
  set P := Vm * Ep * Vi
  have hP1 : P - 1 = Vm * (Ep - 1) * Vi := by
    simp only [P]; rw [mul_sub, sub_mul, mul_one, hVVi]
  have hP1n : ‖P - 1‖ ≤ 8 * ‖Gp‖ := by
    rw [hP1]
    calc ‖Vm * (Ep - 1) * Vi‖ ≤ ‖Vm‖ * ‖Ep - 1‖ * ‖Vi‖ := norm_mul₃_le
      _ ≤ 2 * (2 * ‖Gp‖) * 2 := by gcongr
      _ = 8 * ‖Gp‖ := by ring
  have hPn : ‖P‖ ≤ 5 / 4 := by
    have : ‖P‖ ≤ ‖P - 1‖ + ‖(1 : Mat)‖ := by
      calc ‖P‖ = ‖(P - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have := norm_one_mat_le (N := N)
    linarith
  have e : Em * Eb * P - 1 = (Em - 1) * Eb * P + (Eb - 1) * P + (P - 1) := by noncomm_ring
  rw [hval, e]
  have t1 : ‖(Em - 1) * Eb * P‖ ≤ 2 * ‖Gm‖ * 2 * (5 / 4) :=
    norm_mul₃_le.trans (by gcongr)
  have t2 : ‖(Eb - 1) * P‖ ≤ 2 * ‖B‖ * (5 / 4) := (norm_mul_le _ _).trans (by gcongr)
  calc ‖(Em - 1) * Eb * P + (Eb - 1) * P + (P - 1)‖
      ≤ ‖(Em - 1) * Eb * P‖ + ‖(Eb - 1) * P‖ + ‖P - 1‖ := norm_add₃_le
    _ ≤ 2 * ‖Gm‖ * 2 * (5 / 4) + 2 * ‖B‖ * (5 / 4) + 8 * ‖Gp‖ := by gcongr
    _ ≤ 8 * (‖Gm‖ + ‖B‖ + ‖Gp‖) := by nlinarith [norm_nonneg Gm, norm_nonneg B, norm_nonneg Gp]


/-- **`prop:relative-average-order`(vi)** at a bond of the last level: if `W = (e^{iB}V)^𝐠` there (`gauge_form`), with
`𝐠 = e^{iG}` at the ends, `‖G_±‖ ≤ C₁t` (`order_gauge`), `‖B‖ ≤ 2t` (`order_forms`), and `‖V‖, ‖V⁻¹‖ ≤ 2`, then
`‖W V⁻¹ - id‖ ≤ 8(2C₁ + 2)t`, that is `‖M^n(e^{ia_iA}𝐔)(c)M^n(𝐔)(c)⁻¹ - id‖ ≤ C‖a_jA‖_∞`. -/
theorem order_vi {n : ℕ} [NeZero n] (W V : Config N n) (B : Fin 4 → Site n → Mat) (g : Site n → GLN) {ρ : Fin 4}
    {z : Site n} {Gm Gp : Mat} {t C₁ : ℝ}
    (hW : W ρ z = ((moveC V B).gauge g) ρ z)
    (hgm : g z = expU (Complex.I • Gm)) (hgp : g (z + unit n ρ) = expU (Complex.I • Gp))
    (hGm : ‖Gm‖ ≤ C₁ * t) (hGp : ‖Gp‖ ≤ C₁ * t) (hB : ‖B ρ z‖ ≤ 2 * t)
    (hs1 : C₁ * t ≤ 1 / 32) (hs2 : 2 * t ≤ 1 / 32)
    (hV : ‖((V ρ z : GLN) : Mat)‖ ≤ 2) (hVi : ‖(((V ρ z)⁻¹ : GLN) : Mat)‖ ≤ 2) :
    ‖((W ρ z * (V ρ z)⁻¹ : GLN) : Mat) - 1‖ ≤ 8 * (2 * C₁ + 2) * t := by
  have e : W ρ z * (V ρ z)⁻¹ =
      expU (Complex.I • Gm) * (expU (Complex.I • B ρ z) * V ρ z) * (expU (Complex.I • Gp))⁻¹ * (V ρ z)⁻¹ := by
    rw [hW, Config.gauge, moveC, hgm, hgp]
  rw [e]
  refine (order_vi_alg (hGm.trans hs1) (hB.trans hs2) (hGp.trans hs1) hV hVi).trans ?_
  nlinarith

/-- **`prop:relative-average-order`(iv)**: if `v = e^{iG}` with `‖G‖ < log 2`, then `(1/i) log v = G`; with
`order_gauge` at the last level, `‖(1/i) log v_n(A)(y)‖ ≤ C₁‖a_jA‖_∞`. -/
theorem order_iv {v : GLN} {G : Mat} (hv : v = expU (Complex.I • G)) (hG : ‖G‖ < Real.log 2) :
    (1 / Complex.I) • LogM ((v : GLN) : Mat) = G := by
  rw [hv, expU_val, LogM_exp (by rw [norm_I_smul]; exact hG), smul_smul, one_div_mul_cancel Complex.I_ne_zero,
    one_smul]


/-! ### `𝓜` is near `id`: the hypothesis `‖𝓜_{V_l}(B_l) - id‖ < 1` of the gauge form -/

/-- **`𝓜_𝐔(B)(c)` is within `1` of `id`** for the core's `𝐔` and `‖B‖_{∞,box} < c`, `c` depending on `L` and `G`
only. -/
theorem relAvg_near (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < c →
          ‖((relAvg (moveC U A') B y μ h : GLN) : Mat) - 1‖ < 1 := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set c := min (min (ci / (2 * K)) (1 / (8 * K))) ci with hc_def
  have hc1 : c ≤ ci / (2 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / (8 * K) := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ ci := min_le_right _ _
  refine ⟨c, lt_min (lt_min (by positivity) (by positivity)) hci, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA B hB
  have hn2 : 4 * h + 2 ≤ n := by omega
  obtain ⟨X, hXc, -, hag, -, -⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA
  have hKc : K * c ≤ ci / 2 := by
    calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = ci / 2 := by field_simp
  set R := restrictF B (InBoxB y h μ)
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hloc : relAvg (moveC U A') B y μ h = relAvg (moveC U A') R y μ h :=
    relAvg_local hn2 fun ν z h1 h2 => ⟨rfl, (restrictF_box_apply B ⟨h1, h2⟩).symm⟩
  have hcond := hpol y X (AdF (uG U y h) R) (by linarith) (by rw [norm_AdF_unitary hu]; linarith)
  rw [hloc, relAvg_reduce hU hn hag R hcond]
  exact hcond.r


/-- **`H(n)` of `prop:relative-average-order`**: for per-level gauge fields `U_l`, backgrounds `V_l = e^{iA'_l}U_l`
with `V_{l+1} = M(V_l)`, averages `W_{l+1} = M(W_l)` of `e^{ia_iA}𝐔` with `W_0 = e^{iB_0}V_0`, forms
`B_{l+1} = (1/i) log 𝓜_{V_l}(B_l)`, and gauge transformations `𝐠_{l+1} = 𝐠_l v_{V_l}(B_l)`, `𝐠_0 = id`, on the
regions, with the data of the level `l` at most `e₀L^{-(n-l)}` and `‖B_0‖ ≤ tL^{-n}`: on the region of every level
`W_l = (e^{iB_l}V_l)^{𝐠_l}` (`eq:order-gauge-form`), `‖B_l‖ ≤ 2tL^{-(n-l)}` (`eq:order-fluctuation-bound`), and
`𝐠_l = e^{iG_l}` with `‖G_l‖ ≤ C₁tL^{-(n-l)}`. The constants depend on `L` and `G` only. -/
theorem order_H (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V W : ∀ l, Config N (nn l))
      (A' B : ∀ l, Fin 4 → Site (nn l) → Mat) (g : ∀ l, Site (nn l) → GLN) (a₀ a₁ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (V l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        W (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = avgM (W l) (img h (base l) l x) ρ h) →
      (∀ ρ x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ρ 1) →
        W 0 ρ (img h (base 0) 0 x) = moveC (V 0) (B 0) ρ (img h (base 0) 0 x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h) →
      (∀ l, l < nl → ∀ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        g (l + 1) (img h (base (l + 1)) (l + 1) x) =
          g l (img h (base l) l x) * siteFactor (V l) (B l) (img h (base l) l x) h) →
      (∀ z, g 0 z = 1) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ t → 0 ≤ e₀ → e₀ ≤ c → 2 * t < c → C * (e₀ + 2 * t) ≤ 1 → C₁ * t ≤ 1 / 256 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹) →
      ∀ l, l ≤ nl →
        (∀ ρ x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ρ 1) →
          W l ρ (img h (base l) l x) = ((moveC (V l) (B l)).gauge (g l)) ρ (img h (base l) l x) ∧
          ‖B l ρ (img h (base l) l x)‖ ≤ 2 * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) ∧
        (∀ x, Lat (Lz h) l x → Rg h nl μ l x →
          ∃ G : Mat, g l (img h (base l) l x) = expU (Complex.I • G) ∧
            ‖G‖ ≤ C₁ * t * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) := by
  classical
  obtain ⟨cg, C, C₁, hcg, hC, hC₁, hog⟩ := order_gauge (N := N) h hh
  obtain ⟨cf, Cf, hcf, hCf, hof⟩ := order_forms (N := N) h hh
  choose cr hcr hnear using fun ρ : Fin 4 => relAvg_near (N := N) h ρ
  set crm := Finset.univ.inf' Finset.univ_nonempty cr
  have hcr0 : 0 < crm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcr ρ
  have hcrle : ∀ ρ, crm ≤ cr ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  refine ⟨min (min cg cf) crm, max C Cf, C₁, lt_min (lt_min hcg hcf) hcr0, hC.trans (le_max_left _ _), hC₁, ?_⟩
  intro nl μ nn _ hn base U V W A' B g a₀ a₁ t e₀ hU hVU hdat hV hW hW0 hB hg hg0 ha ht he0 he0c htc hCE hCt hB0
  have hc_g : min (min cg cf) crm ≤ cg := (min_le_left _ _).trans (min_le_left _ _)
  have hc_f : min (min cg cf) crm ≤ cf := (min_le_left _ _).trans (min_le_right _ _)
  have hc_r : min (min cg cf) crm ≤ crm := min_le_right _ _
  have hCE' : C * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hCEf : Cf * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hCE
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL1 : 1 ≤ Lr := by rw [hLr]; push_cast; have : (0 : ℝ) ≤ h := by positivity
                          linarith
  have hp1 : ∀ l, (Lr ^ (nl - l))⁻¹ ≤ 1 := fun l => inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  -- the forms and the gauge transformations
  have hforms := hof nl μ nn hn base U V A' B a₀ a₁ t e₀ hU hVU hdat hB ha ht he0 (he0c.trans hc_f)
    (htc.trans_le hc_f) hCEf hB0
  have hgauge := hog nl μ nn hn base U V A' B g a₀ a₁ t e₀ hU hVU hdat hB hg (fun x _ _ => hg0 _) ha ht he0
    (he0c.trans hc_g) (htc.trans_le hc_g) hCE' hCt hB0
  -- the hypothesis `‖𝓜 - id‖ < 1` of the gauge form
  have hr : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      ‖((relAvg (V l) (B l) (img h (base l) l x) ρ h : GLN) : Mat) - 1‖ < 1 := by
    intro l hl ρ x hx h0 h1
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨h1a, h2a, h3a⟩ := ha l hl
    have he1 : e₀ * (Lr ^ (nl - l))⁻¹ ≤ e₀ := by have := hp1 l; nlinarith
    have hcr' : e₀ ≤ cr ρ := (he0c.trans hc_r).trans (hcrle ρ)
    have hrel : relAvg (V l) (B l) (img h (base l) l x) ρ h =
        relAvg (moveC (U l) (A' l)) (B l) (img h (base l) l x) ρ h := by
      rw [relAvg_local hn2 fun ν z hz1 hz2 => ⟨?_, rfl⟩]
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 ⟨hz1, hz2⟩
      exact hVU l hl ν x' hx' r0 r1
    have hRB : ‖restrictF (B l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ 2 * t * (Lr ^ (nl - l))⁻¹ := by
      refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx h0 h1 hb
      exact hforms l (by omega) ν x' hx' r0 r1
    have hs1 : 2 * t * (Lr ^ (nl - l))⁻¹ ≤ 2 * t := by have := hp1 l; nlinarith
    obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx h0 h1
    rw [hrel]
    exact hnear ρ (U l) (hU l) (hn l) (img h (base l) l x) (a₀ l) (a₁ l) h1a h2a (by linarith) (by linarith) hpl
      (A' l) hA (B l) (by linarith [htc.trans_le ((hc_r).trans (hcrle ρ))])
  have hform := gauge_form h nl μ nn hn base V W B g
    (fun ρ x hx h0 h1 => by
      rw [hW0 ρ x hx h0 h1]
      simp only [Config.gauge, hg0, one_mul, _root_.inv_one, mul_one])
    hV hW hB hg hr
  intro l hl
  exact ⟨fun ρ x hx h0 h1 => ⟨hform l hl ρ x hx h0 h1, hforms l hl ρ x hx h0 h1⟩, hgauge l hl⟩


/-! ### `(iii)`: the remainder of the composite map -/

/-- **Locality of `(1/i) log 𝓜` in the background**, as functions of the form. -/
lemma relLog_fun_local {n : ℕ} [NeZero n] {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {V V' : Config N n}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z) :
    (fun B => relLog V B y μ h) = (fun B => relLog V' B y μ h) := by
  funext B
  simp only [relLog]
  rw [relAvg_local hn fun ν z h1 h2 => ⟨hVV ν z h1 h2, rfl⟩]

/-- The arithmetic of the remainders: if `r_{l+1} ≤ (L + Cx_l)r_l + 4C₂t²L^{-2(n-l)}`, `r_0 = 0`,
`x_l ≤ eL^{-(n-l)}`, `Ce ≤ 1`, then `r_l ≤ 8C₂t²L^{-(n-l)}Σ_{m<l}L^{-(n-m)}`. -/
lemma rem_step {Lr C C₂ t e x r σ q : ℝ} (hL : 3 ≤ Lr) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (he : 0 ≤ e) (hCe : C * e ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2) (hx0 : 0 ≤ x) (hx : x ≤ e * q)
    (hr : r ≤ 8 * C₂ * t ^ 2 * q * σ) (hr0 : 0 ≤ r) :
    (Lr + C * x) * r + C₂ * (2 * t * q) ^ 2 ≤ 8 * C₂ * t ^ 2 * (Lr * q) * (σ + q) := by
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hQ : 0 ≤ 8 * C₂ * t ^ 2 := by positivity
  have h1 : (Lr + C * x) * r ≤ (Lr + C * x) * (8 * C₂ * t ^ 2 * q * σ) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have hCx : C * x ≤ q := by
    calc C * x ≤ C * (e * q) := mul_le_mul_of_nonneg_left hx hC
      _ = (C * e) * q := by ring
      _ ≤ 1 * q := mul_le_mul_of_nonneg_right hCe hq0
      _ = q := one_mul q
  have h2 : C * x * (8 * C₂ * t ^ 2 * q * σ) ≤ q * (8 * C₂ * t ^ 2 * q * (1 / 2)) := by
    have hs' : 8 * C₂ * t ^ 2 * q * σ ≤ 8 * C₂ * t ^ 2 * q * (1 / 2) :=
      mul_le_mul_of_nonneg_left hσ (by positivity : (0 : ℝ) ≤ 8 * C₂ * t ^ 2 * q)
    exact mul_le_mul hCx hs' (by positivity) hq0
  have h3 : C₂ * (2 * t * q) ^ 2 = 4 * C₂ * t ^ 2 * q ^ 2 := by ring
  have h4 : 8 * C₂ * t ^ 2 * (Lr * q) * (σ + q) =
      Lr * (8 * C₂ * t ^ 2 * q * σ) + 8 * C₂ * t ^ 2 * Lr * q ^ 2 := by ring
  rw [h3, h4]
  have h5 : 4 * C₂ * t ^ 2 * q ^ 2 + q * (8 * C₂ * t ^ 2 * q * (1 / 2)) ≤ 8 * C₂ * t ^ 2 * Lr * q ^ 2 := by
    have : 0 ≤ C₂ * t ^ 2 * q ^ 2 := by positivity
    nlinarith
  nlinarith

/-- **`prop:relative-average-order`(iii), the bound of the remainder**: under the hypotheses of `order_forms`, the
forms `B_l` and their linear parts `D_{l+1} = LQ(V_l)D_l`, `D_0 = B_0`, satisfy
`‖B_l - D_l‖ ≤ 8C₂t²L^{-(n-l)}Σ_{m<l}L^{-(n-m)}`; at the last level `‖C_n(𝐔; a_jA)(c)‖ = ‖B_n - D_n‖ ≤ 4C₂t²`.
The bound is obtained by carrying the remainders of the single steps through the induction, in place of the
lemma of Schwarz. -/
theorem order_iii (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₂ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₂ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' B D : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (t e₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) = relLog (V l) (B l) (img h (base l) l x) ρ h ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e₀ * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ t → 0 ≤ e₀ → e₀ ≤ c → 2 * t < c → C * (e₀ + 2 * t) ≤ 1 →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        ‖B 0 ν (img h (base 0) 0 x)‖ ≤ t * ((((2 * h + 1 : ℕ) : ℝ)) ^ nl)⁻¹ ∧
        D 0 ν (img h (base 0) 0 x) = B 0 ν (img h (base 0) 0 x)) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖B l ν (img h (base l) l x) - D l ν (img h (base l) l x)‖ ≤
          8 * C₂ * t ^ 2 * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹ *
            ∑ m ∈ Finset.range l, ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - m))⁻¹ := by
  classical
  obtain ⟨cf, Cf, hcf, hCf, hof⟩ := order_forms (N := N) h hh
  choose cl Cl hcl hCl hlin using fun ρ : Fin 4 => linear_bound (N := N) h ρ
  choose cb C0 C1 C2 C3 hcb hC0 hC1 hC2 hC3 hbox using fun ρ : Fin 4 => relative_average_box (N := N) h ρ
  set clm := Finset.univ.inf' Finset.univ_nonempty cl
  set cbm := Finset.univ.inf' Finset.univ_nonempty cb
  set Clm := Finset.univ.sup' Finset.univ_nonempty Cl
  set C2m := Finset.univ.sup' Finset.univ_nonempty C2
  have hclm : ∀ ρ, clm ≤ cl ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hcbm : ∀ ρ, cbm ≤ cb ρ := fun ρ => Finset.inf'_le _ (Finset.mem_univ ρ)
  have hClm : ∀ ρ, Cl ρ ≤ Clm := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC2m : ∀ ρ, C2 ρ ≤ C2m := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hclm0 : 0 < clm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcl ρ
  have hcbm0 : 0 < cbm := (Finset.lt_inf'_iff _).2 fun ρ _ => hcb ρ
  have hClm0 : 0 ≤ Clm := (hCl 0).trans (hClm 0)
  have hC2m0 : 0 ≤ C2m := (hC2 0).trans (hC2m 0)
  refine ⟨min cf (min clm cbm), max Cf Clm, C2m, lt_min hcf (lt_min hclm0 hcbm0), hCf.trans (le_max_left _ _),
    hC2m0, ?_⟩
  intro nl μ nn _ hn base U V A' B D a₀ a₁ t e₀ hU hVU hdat hBD ha ht he0 he0c htc hCE h0
  have hcf' : min cf (min clm cbm) ≤ cf := min_le_left _ _
  have hcl' : min cf (min clm cbm) ≤ clm := (min_le_right _ _).trans (min_le_left _ _)
  have hcb' : min cf (min clm cbm) ≤ cbm := (min_le_right _ _).trans (min_le_right _ _)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hCEf : Cf * (e₀ + 2 * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hCE
  have hCEl : Clm * e₀ ≤ 1 := by
    have := (mul_le_mul_of_nonneg_right (le_max_right Cf Clm) (by positivity : (0 : ℝ) ≤ e₀ + 2 * t)).trans hCE
    nlinarith
  -- the forms of the levels
  have hforms := hof nl μ nn hn base U V A' B a₀ a₁ t e₀ hU hVU hdat (fun l hl ρ x hx q0 q1 =>
    (hBD l hl ρ x hx q0 q1).1) ha ht he0 (he0c.trans hcf') (htc.trans_le hcf') hCEf (fun ν x hx q0 q1 =>
    (h0 ν x hx q0 q1).1)
  intro l
  induction l with
  | zero =>
    intro _ ν x hx q0 q1
    rw [(h0 ν x hx q0 q1).2, sub_self, norm_zero]
    simp
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, hae⟩ := ha l hll
    set q := (Lr ^ (nl - l))⁻¹ with hq
    have hq0 : 0 ≤ q := by positivity
    set σ := ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹ with hσ
    have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun m _ => by positivity
    have hσ12 : σ ≤ 1 / 2 := (geom_partial hL3 nl l hll.le).trans (by
      have := hp1 (nl - l); nlinarith)
    set y := img h (base l) l x
    have hfun := relLog_fun_local (V := V l) (V' := moveC (U l) (A' l)) (y := y) (μ := ρ) (h := h) hn2
      fun ν z hz1 hz2 => by
        obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 ⟨hz1, hz2⟩
        exact hVU l hll ν x' hx' r0 r1
    have hQ : Qlin (V l) y ρ h = Qlin (moveC (U l) (A' l)) y ρ h := by simp only [Qlin, hfun]
    have hCr : Crem (V l) (B l) y ρ h = Crem (moveC (U l) (A' l)) (B l) y ρ h := by
      simp only [Crem, hQ]
      have := congrFun hfun (B l)
      rw [this]
    -- `B_{l+1} - D_{l+1} = LQ(B_l - D_l) + C(B_l)`
    obtain ⟨hBl, hDl⟩ := hBD l hll ρ x hx q0 q1
    have e : B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) - D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
        ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (B l - D l) +
          Crem (moveC (U l) (A' l)) (B l) y ρ h := by
      rw [hBl, hDl, linear_part, hQ, hCr, map_sub, smul_sub]
      abel
    rw [e]
    obtain ⟨hpl, hA⟩ := hdat l hll ρ x hx q0 q1
    have hae' : a₀ l + a₁ l ≤ e₀ := by have := hp1 (nl - l); nlinarith
    -- the linear term
    have hRD : ‖restrictF (B l - D l) (InBoxB y h ρ)‖ ≤ 8 * C2m * t ^ 2 * q * σ := by
      refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      simpa only [Pi.sub_apply] using ih (by omega) ν x' hx' r0 r1
    have hL1 := hlin ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1
      ((by linarith : a₀ l ≤ e₀).trans ((he0c.trans hcl').trans (hclm ρ)))
      ((by linarith : a₁ l ≤ e₀).trans ((he0c.trans hcl').trans (hclm ρ))) hpl (A' l) hA (B l - D l)
    -- the remainder
    have hRB : ‖restrictF (B l) (InBoxB y h ρ)‖ ≤ 2 * t * q := by
      refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
      obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
      exact hforms l (by omega) ν x' hx' r0 r1
    have hRBc : ‖restrictF (B l) (InBoxB y h ρ)‖ < cb ρ := by
      have : 2 * t * q ≤ 2 * t := by have := hp1 (nl - l); nlinarith
      linarith [htc.trans_le (hcb'.trans (hcbm ρ))]
    obtain ⟨-, -, hrem⟩ := hbox ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1
      ((by linarith : a₀ l ≤ e₀).trans ((he0c.trans hcb').trans (hcbm ρ)))
      ((by linarith : a₁ l ≤ e₀).trans ((he0c.trans hcb').trans (hcbm ρ))) hpl (A' l) hA (B l)
    have hC := (hrem hRBc).1
    -- assemble
    have hnext : (Lr ^ (nl - (l + 1)))⁻¹ = Lr * q := by
      rw [hq, show nl - l = nl - (l + 1) + 1 by omega, pow_succ, mul_inv]
      field_simp
    rw [hnext, Finset.sum_range_succ]
    have hstep := rem_step (C := Clm) (C₂ := C2m) (t := t) (e := e₀) (x := a₀ l + a₁ l)
      (r := ‖restrictF (B l - D l) (InBoxB y h ρ)‖) hL3 hClm0 hC2m0 he0 hCEl hq0 (hp1 _) hσ0 hσ12
      (by positivity) hae hRD (norm_nonneg _)
    have hlin' : ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (B l - D l)‖ ≤
        (Lr + Clm * (a₀ l + a₁ l)) * ‖restrictF (B l - D l) (InBoxB y h ρ)‖ :=
      hL1.trans (mul_le_mul_of_nonneg_right (by
        have := mul_le_mul_of_nonneg_right (hClm ρ) (by positivity : (0 : ℝ) ≤ a₀ l + a₁ l); linarith)
        (norm_nonneg _))
    have hrem' : ‖Crem (moveC (U l) (A' l)) (B l) y ρ h‖ ≤ C2m * (2 * t * q) ^ 2 :=
      hC.trans (mul_le_mul (hC2m ρ) (pow_le_pow_left₀ (norm_nonneg _) hRB 2) (by positivity) hC2m0)
    calc ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) y ρ h (B l - D l) +
          Crem (moveC (U l) (A' l)) (B l) y ρ h‖
        ≤ (Lr + Clm * (a₀ l + a₁ l)) * ‖restrictF (B l - D l) (InBoxB y h ρ)‖ + C2m * (2 * t * q) ^ 2 :=
          (norm_add_le _ _).trans (add_le_add hlin' hrem')
      _ ≤ 8 * C2m * t ^ 2 * (Lr * q) * (σ + q) := hstep

end RelativeAverage
end CoreLean

end
