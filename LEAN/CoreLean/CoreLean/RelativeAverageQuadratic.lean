/-
`lem:average-kernels`, the quadratic part, of BALABAN_CORE.tex (`7374c382ba1b`).

The proof compares the parts of the second order in `A` of the forms of the levels: with `Λ_l = Q^{(l-1)}⋯Q^{(0)}` the linear
part and `P_l` the part of the second order, `P_{l+1} = Q^{(l)}P_l + C^{(l)}_2(Λ_lA₁, Λ_lA₂)` and `P_0 = 0`, and the
symmetric bilinear map `C^{(l)}_2` is at most a constant times `‖X‖‖Y‖` on the box of the bond.

* `quadratic_kernel`: the `ℓ¹`-bound of `P_n` from this recursion on the levels: for `‖Y_l(c')‖ ≤ K‖Λ_lA₂‖_{box}‖Λ_lA₁‖_{box}`
  and `‖Λ_lA₂‖ ≤ s₀L^l` on the regions, `Σ_c‖P_n(c)‖ ≤ 32KL³s₀L^{-2n}Σ_{b'}‖A₁(b')‖`; for `A₁` supported on one bond this is
  the second bound of `eq:average-kernels` in the units of the lattices.
* The bilinear bound of one step is `ParamDeriv.second_deriv_bound` applied to `C(𝐔^{(l)}; ·)`, which is at most
  `C₂‖X‖²` by `relative_average_box`.
-/
import CoreLean.RelativeAverageKernels
import CoreLean.ParamDeriv
import CoreLean.RelativeAverageBackground

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
open Classical in
/-- **`lem:average-kernels`, the quadratic part, on the levels**: under the per-level hypotheses with data at most
`eL^{-(n-l)}` (`8L³Ce ≤ 1`), the linear parts `D_{l+1} = LQ(V_l)D_l`, `D_0 = A₁`, forms `D'_l` (the linear parts of `A₂`)
with `‖D'_l‖ ≤ s₀L^l` on the regions, and forms `P_{l+1} = LQ(V_l)P_l + Y_l`, `P_0 = 0`, with
`‖Y_l(c')‖ ≤ K‖D'_l‖_{box(c')}‖D_l‖_{box(c')}` satisfy `Σ_c‖P_n(c)‖ ≤ 32KL³s₀L^{-2n}Σ_{b'}‖A₁(b')‖`. -/
theorem quadratic_kernel (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U V : ∀ l, Config N (nn l))
      (A' D D' P : ∀ l, Fin 4 → Site (nn l) → Mat) (Y : ℕ → (Fin 4 → ℤ) → Fin 4 → Mat) (a₀ a₁ : ℕ → ℝ)
      (e K s₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        V l ν (img h (base l) l x) = moveC (U l) (A' l) ν (img h (base l) l x)) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C * e ≤ 1 → 0 ≤ K → 0 ≤ s₀ →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (D l) ∧
        P (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (P l) + Y l x ρ ∧
        ‖Y l x ρ‖ ≤ K * ‖restrictF (D' l) (InBoxB (img h (base l) l x) h ρ)‖ *
          ‖restrictF (D l) (InBoxB (img h (base l) l x) h ρ)‖) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖D' l ν (img h (base l) l x)‖ ≤ s₀ * (((2 * h + 1 : ℕ) : ℝ)) ^ l) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        P 0 ν (img h (base 0) 0 x) = 0) →
      ell1 h nl μ nl (fun x ν => ‖P nl ν (img h (base nl) nl x)‖) ≤
        32 * K * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * s₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl *
          ell1 h nl μ 0 (fun x ν => ‖D 0 ν (img h (base 0) 0 x)‖) := by
  obtain ⟨ck, Ck, hck, hCk, hks⟩ := kernel_step1 (N := N) h
  refine ⟨ck, Ck, hck, hCk, ?_⟩
  intro nl μ nn _ hn base U V A' D D' P Y a₀ a₁ e K s₀ hU hVU hdat ha he hec hCe hK hs₀ hrel hD' hP0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hL3 : 3 ≤ Lr := by rw [hLr]; push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                          linarith
  have hL0 : 0 < Lr := by linarith
  set q : ℝ := (Lr ^ 3)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hdat' : ∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ ck ∧ a₁ l ≤ ck := fun l hl => by
    obtain ⟨h1, h2, h3⟩ := ha l hl
    have : e * (Lr ^ (nl - l))⁻¹ ≤ e := by have := hp1 (nl - l); nlinarith
    exact ⟨h1, h2, by linarith, by linarith⟩
  have hks' := hks nl μ nn hn base U V A' a₀ a₁ hU hVU hdat hdat'
  set E : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖D l ν (img h (base l) l x)‖) with hE
  set ER : ℕ → ℝ := fun l => ell1 h nl μ l (fun x ν => ‖P l ν (img h (base l) l x)‖) with hER
  have hE0 : ∀ l, 0 ≤ E l := fun l => ell1_nonneg fun _ _ => norm_nonneg _
  have hER0 : ∀ l, 0 ≤ ER l := fun l => ell1_nonneg fun _ _ => norm_nonneg _
  set α : ℕ → ℝ := fun l => if l < nl then a₀ l + a₁ l else 0 with hα
  have hα0 : ∀ l, 0 ≤ α l := fun l => by
    simp only [hα]; split_ifs with hl
    · obtain ⟨h1, h2, -⟩ := ha l hl; linarith
    · exact le_rfl
  -- one step for `D` and for `P`
  have hstep : ∀ l, l < nl → E (l + 1) ≤ (q + 8 * Ck * α l) * E l ∧
      ER (l + 1) ≤ (q + 8 * Ck * α l) * ER l + 8 * K * s₀ * Lr ^ l * E l := by
    intro l hl
    have hαl : α l = a₀ l + a₁ l := by simp only [hα, if_pos hl]
    have hk1 := hks' l hl (D l)
    have hk2 := hks' l hl (P l)
    rw [← hαl] at hk1 hk2
    have hrestr := ell1_restrict_le (nl := nl) (μ := μ) (l := l) (hn l) (base l) (D l)
    have hcs : 0 ≤ K * (s₀ * Lr ^ l) := by positivity
    constructor
    · refine le_trans (ell1_mono fun x ρ hb => ?_) hk1
      obtain ⟨hx, q0, q1⟩ := hb
      rw [(hrel l hl ρ x hx q0 q1).1]
    · have hpt : ∀ x ρ, RB h nl μ (l + 1) x ρ → ‖P (l + 1) ρ (img h (base (l + 1)) (l + 1) x)‖ ≤
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (P l)‖ +
            K * (s₀ * Lr ^ l) * ‖restrictF (D l) (InBoxB (img h (base l) l x) h ρ)‖ := fun x ρ hb => by
        obtain ⟨hx, q0, q1⟩ := hb
        obtain ⟨-, hPe, hY⟩ := hrel l hl ρ x hx q0 q1
        rw [hPe]
        refine (norm_add_le _ _).trans (add_le_add le_rfl (hY.trans ?_))
        have hR : ‖restrictF (D' l) (InBoxB (img h (base l) l x) h ρ)‖ ≤ s₀ * Lr ^ l := by
          refine norm_restrictF_box_le (by positivity) fun ν z hb => ?_
          obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hb
          exact hD' l hl ν x' hx' r0 r1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hK) (norm_nonneg _)
      calc ER (l + 1) ≤ ell1 h nl μ (l + 1) (fun x ρ =>
              ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (V l) (img h (base l) l x) ρ h (P l)‖ +
                K * (s₀ * Lr ^ l) * ‖restrictF (D l) (InBoxB (img h (base l) l x) h ρ)‖) := ell1_mono hpt
        _ = _ + K * (s₀ * Lr ^ l) * _ := by rw [ell1_add, ell1_smul]
        _ ≤ (q + 8 * Ck * α l) * ER l + K * (s₀ * Lr ^ l) * (8 * E l) :=
            add_le_add hk2 (mul_le_mul_of_nonneg_left hrestr hcs)
        _ = (q + 8 * Ck * α l) * ER l + 8 * K * s₀ * Lr ^ l * E l := by ring
  -- the growth of `D`: `E(l) ≤ 2qˡE(0)`
  have hsum : ∀ l, l ≤ nl → ∑ m ∈ Finset.range l, α m ≤ e / 2 := fun l hl => by
    have hg := geom_partial hL3 nl l hl
    have hq1 : (1 / 2 : ℝ) * (Lr ^ (nl - l))⁻¹ ≤ 1 / 2 := by have := hp1 (nl - l); linarith
    calc ∑ m ∈ Finset.range l, α m ≤ ∑ m ∈ Finset.range l, e * (Lr ^ (nl - m))⁻¹ :=
          Finset.sum_le_sum fun m hm => by
            have hm' : m < nl := lt_of_lt_of_le (Finset.mem_range.1 hm) hl
            simp only [hα, if_pos hm']; exact (ha m hm').2.2
      _ = e * ∑ m ∈ Finset.range l, (Lr ^ (nl - m))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left (hg.trans hq1) he
      _ = e / 2 := by ring
  have hexp : ∀ l, l ≤ nl → Real.exp (8 * Ck * (∑ m ∈ Finset.range l, α m) / q) ≤ 2 := fun l hl => by
    have hy0 : 0 ≤ 8 * Ck * (∑ m ∈ Finset.range l, α m) / q :=
      div_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hα0 m)) hq0.le
    have hy1 : 8 * Ck * (∑ m ∈ Finset.range l, α m) / q ≤ 1 / 2 := by
      rw [hq, div_inv_eq_mul]
      have h8 : 0 ≤ 8 * Ck := by positivity
      have := mul_le_mul_of_nonneg_left (hsum l hl) h8
      have hL3' : 0 ≤ Lr ^ 3 := by positivity
      calc 8 * Ck * (∑ m ∈ Finset.range l, α m) * Lr ^ 3 ≤ 8 * Ck * (e / 2) * Lr ^ 3 :=
            mul_le_mul_of_nonneg_right this hL3'
        _ = (8 * Lr ^ 3 * Ck * e) / 2 := by ring
        _ ≤ 1 / 2 := by linarith
    have := GroupMean.exp_small_le hy0 (hy1.trans (by norm_num))
    linarith
  have hit : ∀ l, l ≤ nl → E l ≤ (∏ m ∈ Finset.range l, (q + 8 * Ck * α m)) * E 0 := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have hll : l < nl := by omega
      rw [Finset.prod_range_succ]
      calc E (l + 1) ≤ (q + 8 * Ck * α l) * E l := (hstep l hll).1
        _ ≤ (q + 8 * Ck * α l) * ((∏ m ∈ Finset.range l, (q + 8 * Ck * α m)) * E 0) :=
            mul_le_mul_of_nonneg_left (ih hll.le) (by have := hα0 l; positivity)
        _ = _ := by ring
  have hE2 : ∀ l, l ≤ nl → E l ≤ 2 * q ^ l * E 0 := fun l hl => by
    have hprod := prod_le_exp hq0 (by positivity : (0 : ℝ) ≤ 8 * Ck) α hα0 l
    calc E l ≤ (∏ m ∈ Finset.range l, (q + 8 * Ck * α m)) * E 0 := hit l hl
      _ ≤ (q ^ l * 2) * E 0 :=
          mul_le_mul_of_nonneg_right (hprod.trans (mul_le_mul_of_nonneg_left (hexp l hl) (by positivity))) (hE0 0)
      _ = 2 * q ^ l * E 0 := by ring
  -- the quadratic part: `ER(l) ≤ 32KL³s₀(qL)ˡE(0)`
  have hERz : ER 0 = 0 := by
    refine le_antisymm ?_ (hER0 0)
    calc ER 0 ≤ ell1 h nl μ 0 (fun _ _ => (0 : ℝ)) := ell1_mono fun x ν hb => by
          obtain ⟨hx, q0, q1⟩ := hb
          rw [hP0 ν x hx q0 q1, norm_zero]
      _ = 0 := by simp [ell1]
  have hqL : q * Lr ^ 3 = 1 := by rw [hq]; field_simp
  have hRit : ∀ l, l ≤ nl → ER l ≤ 32 * K * Lr ^ 3 * s₀ * (q * Lr) ^ l * E 0 := by
    intro l
    induction l with
    | zero => intro _; rw [hERz]; exact mul_nonneg (by positivity) (hE0 0)
    | succ l ih =>
      intro hl
      have hll : l < nl := by omega
      have hαl : α l ≤ e := by
        have h3 := (ha l hll).2.2
        have : e * (Lr ^ (nl - l))⁻¹ ≤ e := by have := hp1 (nl - l); nlinarith
        simp only [hα, if_pos hll]; linarith
      have h1 := (hstep l hll).2
      have h2 := hE2 l hll.le
      have h3 := ih hll.le
      have hE00 := hE0 0
      have hqLl : 0 ≤ (q * Lr) ^ l := by positivity
      have hCα : 8 * Ck * α l * Lr ^ 3 ≤ 1 := by
        have : 8 * Ck * α l ≤ 8 * Ck * e := mul_le_mul_of_nonneg_left hαl (by positivity)
        nlinarith [pow_pos hL0 3]
      have hpow : q ^ l * Lr ^ l = (q * Lr) ^ l := (mul_pow q Lr l).symm
      have hA : 0 ≤ K * s₀ * (q * Lr) ^ l * E 0 := by positivity
      calc ER (l + 1) ≤ (q + 8 * Ck * α l) * ER l + 8 * K * s₀ * Lr ^ l * E l := h1
        _ ≤ (q + 8 * Ck * α l) * (32 * K * Lr ^ 3 * s₀ * (q * Lr) ^ l * E 0) +
              8 * K * s₀ * Lr ^ l * (2 * q ^ l * E 0) := by
            have hq8 : 0 ≤ q + 8 * Ck * α l := by have := hα0 l; positivity
            exact add_le_add (mul_le_mul_of_nonneg_left h3 hq8)
              (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = K * s₀ * (q * Lr) ^ l * E 0 * (32 * (q * Lr ^ 3) + 32 * (8 * Ck * α l * Lr ^ 3) + 16) := by
            rw [← hpow]; ring
        _ ≤ K * s₀ * (q * Lr) ^ l * E 0 * (32 * Lr) := by
            apply mul_le_mul_of_nonneg_left _ hA
            linarith [hCα, hL3, hqL]
        _ = 32 * K * Lr ^ 3 * s₀ * (q * Lr) ^ (l + 1) * E 0 := by
            rw [pow_succ]
            have : q * Lr * Lr ^ 3 = Lr := by
              calc q * Lr * Lr ^ 3 = (q * Lr ^ 3) * Lr := by ring
                _ = Lr := by rw [hqL, one_mul]
            linear_combination (-(32 * K * s₀ * (q * Lr) ^ l * E 0)) * this
  have hfin := hRit nl le_rfl
  have hqL2 : q * Lr = (Lr ^ 2)⁻¹ := by rw [hq]; field_simp
  calc ER nl ≤ 32 * K * Lr ^ 3 * s₀ * (q * Lr) ^ nl * E 0 := hfin
    _ = 32 * K * Lr ^ 3 * s₀ * ((Lr ^ 2)⁻¹) ^ nl * E 0 := by rw [hqL2]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The bilinear part of the remainder of one step** (the proof of `lem:average-kernels`: "by
Proposition~\ref{prop:relative-average}(vi) and Cauchy's estimate, `‖C⁽ˡ⁾₂(X)‖ ≤ C₂‖X‖²`, and the symmetric bilinear map
with this diagonal is at most `2C₂‖X‖‖Y‖`"): for a gauge field `U` and `A'` with small data on the blocks of the bond,
the mixed second derivative at `0` of `B ↦ C(e^{iaA'}U; B)(c)` satisfies
`‖∂_X∂_YC(0)‖ ≤ (16/3)C₂‖X‖_{box}‖Y‖_{box}`, the norms over the bonds of the box of `c`. The remainder depends only on
the values on the box (`relLog_box`, `Qlin_box`), it is holomorphic and at most `C₂‖B‖²` on a ball
(`relative_average_box`), and `second_deriv_bound` applies at the restricted directions. -/
theorem Crem_second_bound (h : ℕ) (μ : Fin 4) :
    ∃ c C₂ : ℝ, 0 < c ∧ 0 ≤ C₂ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ X Y : Fin 4 → Site n → Mat,
          ‖fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B Y) 0 X‖ ≤
            16 / 3 * C₂ * ‖restrictF X (InBoxB y h μ)‖ * ‖restrictF Y (InBoxB y h μ)‖ := by
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨cP, hcP, hP⟩ := relLog_core_pair_differentiableAt (N := N) h μ
  set c := min cb (cP / 2) with hc_def
  have k1 : c ≤ cb := min_le_left _ _
  have k2 : c ≤ cP / 2 := min_le_right _ _
  have hc0 : 0 < c := lt_min hcb (by positivity)
  refine ⟨c, C₂, hc0, hC₂, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA X Y
  have hn2 : 4 * h + 2 ≤ n := by omega
  set R := restrictBoxL y h μ with hR
  set φ : (Fin 4 → Site n → Mat) → Mat := fun B => Crem (moveC U A') B y μ h with hφ
  have hA'r : ‖restrictF A' (InBoxB y h μ)‖ < cP := (norm_restrictF_box_le hα₁ hA).trans_lt (by linarith)
  -- the slices of `relLog` are holomorphic near the small forms
  have hα₀P : α₀ ≤ cP := hα₀c.trans (k2.trans (by linarith))
  have hrelD : ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < cP →
      DifferentiableAt ℂ (fun B => relLog (moveC U A') B y μ h) B := fun B hB => by
    have hpd := hP U hU hn y α₀ hα₀ hα₀P hplq A' B hA'r hB
    have hlin : DifferentiableAt ℂ (fun B' : Fin 4 → Site n → Mat => (A', B')) B :=
      (differentiableAt_const A').prodMk differentiableAt_id
    exact hpd.comp B hlin
  have hd0 : DifferentiableAt ℂ (fun B => relLog (moveC U A') B y μ h) 0 :=
    hrelD 0 ((norm_restrictF_le _ _).trans_lt (by simpa using hcP))
  -- locality: `φ = φ ∘ R`
  have hloc : ∀ B, φ B = φ (R B) := fun B => by
    have hQ := Qlin_box hn2 (moveC U A') y μ hd0
    simp only [hφ, Crem]
    rw [relLog_box hn2 (moveC U A') y μ B]
    rw [show Qlin (moveC U A') y μ h B = Qlin (moveC U A') y μ h (R B) from by
      conv_lhs => rw [hQ]
      rfl]
    rfl
  -- holomorphy and the quadratic bound on the ball of radius `c`
  have hφd : DifferentiableOn ℂ φ (ball 0 c) := fun B hB => by
    have hBr : ‖restrictF B (InBoxB y h μ)‖ < cP :=
      (norm_restrictF_le _ _).trans_lt ((mem_ball_zero_iff.1 hB).trans_le (k2.trans (by linarith)))
    have hQd : DifferentiableAt ℂ (fun B => ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B) B :=
      (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h).differentiableAt
    exact ((hrelD B hBr).sub hQd).differentiableWithinAt
  have hφK : ∀ B ∈ ball (0 : Fin 4 → Site n → Mat) c, ‖φ B‖ ≤ C₂ * ‖B‖ ^ 2 := fun B hB => by
    have hBc : ‖B‖ < c := mem_ball_zero_iff.1 hB
    have hBr : ‖restrictF B (InBoxB y h μ)‖ ≤ ‖B‖ := norm_restrictF_le _ _
    obtain ⟨-, -, hrem⟩ := hbox U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans k1) (hα₁c.trans k1) hplq A' hA B
    have := (hrem (hBr.trans_lt (hBc.trans_le k1))).1
    calc ‖φ B‖ ≤ C₂ * ‖restrictF B (InBoxB y h μ)‖ ^ 2 := this
      _ ≤ C₂ * ‖B‖ ^ 2 := by gcongr
  -- the derivative in the direction `Y` is that in the direction `RY`, near `0`
  have hRle : ∀ B, ‖R B‖ ≤ ‖B‖ := fun B => norm_restrictF_le _ _
  have hev : (fun B => fderiv ℂ φ B Y) =ᶠ[𝓝 0] (fun B'' => fderiv ℂ φ B'' (R Y)) ∘ R := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hc0)] with B hB
    have hRB : R B ∈ ball (0 : Fin 4 → Site n → Mat) c :=
      mem_ball_zero_iff.2 ((hRle B).trans_lt (mem_ball_zero_iff.1 hB))
    have hφR : DifferentiableAt ℂ φ (R B) := hφd.differentiableAt (isOpen_ball.mem_nhds hRB)
    have e : φ = φ ∘ R := funext hloc
    have hfd : fderiv ℂ φ B = (fderiv ℂ φ (R B)).comp R := by
      conv_lhs => rw [e]
      rw [fderiv_comp B hφR R.differentiableAt, R.fderiv]
    simp only [Function.comp, hfd, ContinuousLinearMap.comp_apply]
  have hkd := ParamDeriv.fderiv_apply_differentiableOn hc0 hφd (fun B hB => (hφK B hB).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.1 hB).le 2) hC₂)) (R Y)
  have hk0 : DifferentiableAt ℂ (fun B'' => fderiv ℂ φ B'' (R Y)) (R 0) := by
    rw [map_zero]; exact hkd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  have hfd2 : fderiv ℂ (fun B => fderiv ℂ φ B Y) 0 X = fderiv ℂ (fun B'' => fderiv ℂ φ B'' (R Y)) 0 (R X) := by
    rw [hev.fderiv_eq, fderiv_comp 0 hk0 R.differentiableAt, R.fderiv, map_zero]
    rfl
  have hb := ParamDeriv.second_deriv_bound hc0 hC₂ hφd hφK (R X) (R Y)
  show ‖fderiv ℂ (fun B => fderiv ℂ φ B Y) 0 X‖ ≤ _
  rw [hfd2]
  exact hb

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The second derivative of one step along a curve**: for a gauge field `U` and `A'` with small data on the blocks of
the bond, and a curve `b` of forms with `b(0) = 0`, `b'(0) = b₁`, `(b')'(0) = b₂`, differentiable near `0`, the map
`s ↦ (1/i) log 𝓜_{e^{iaA'}U}(b(s))(c)` has the derivative `L Q b₁` at `0`, and its derivative has the derivative
`L Q b₂ + ∂_{b₁}(C'(·)b₁)(0)` at `0`: the remainder `C` is holomorphic and at most `C₂‖B‖²` near `0`, so that its
derivative vanishes at `0`, and `second_chain` applies. -/
theorem relLog_second (h : ℕ) (μ : Fin 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (b : ℂ → Fin 4 → Site n → Mat) (b₁ b₂ : Fin 4 → Site n → Mat), b 0 = 0 → HasDerivAt b b₁ 0 →
          HasDerivAt (deriv b) b₂ 0 → (∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ b s) →
          HasDerivAt (fun s => relLog (moveC U A') (b s) y μ h)
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h b₁) 0 ∧
          HasDerivAt (deriv fun s => relLog (moveC U A') (b s) y μ h)
            (((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h b₂ +
              fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B b₁) 0 b₁) 0 := by
  obtain ⟨cb, C₀, C₁, C₂, C₃, hcb, hC₀, hC₁, hC₂, hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨cP, hcP, hP⟩ := relLog_core_pair_differentiableAt (N := N) h μ
  set c := min cb (cP / 2) with hc_def
  have k1 : c ≤ cb := min_le_left _ _
  have k2 : c ≤ cP / 2 := min_le_right _ _
  have hc0 : 0 < c := lt_min hcb (by positivity)
  refine ⟨c, hc0, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA b b₁ b₂ hb0 hb1 hb2 hbd
  set φ : (Fin 4 → Site n → Mat) → Mat := fun B => Crem (moveC U A') B y μ h with hφ
  set LQ : (Fin 4 → Site n → Mat) →L[ℂ] Mat := ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h with hLQ
  have hA'r : ‖restrictF A' (InBoxB y h μ)‖ < cP := (norm_restrictF_box_le hα₁ hA).trans_lt (by linarith)
  have hα₀P : α₀ ≤ cP := hα₀c.trans (k2.trans (by linarith))
  have hrelD : ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < cP →
      DifferentiableAt ℂ (fun B => relLog (moveC U A') B y μ h) B := fun B hB => by
    have hpd := hP U hU hn y α₀ hα₀ hα₀P hplq A' B hA'r hB
    have hlin : DifferentiableAt ℂ (fun B' : Fin 4 → Site n → Mat => (A', B')) B :=
      (differentiableAt_const A').prodMk differentiableAt_id
    exact hpd.comp B hlin
  have hφd : DifferentiableOn ℂ φ (ball 0 c) := fun B hB => by
    have hBr : ‖restrictF B (InBoxB y h μ)‖ < cP :=
      (norm_restrictF_le _ _).trans_lt ((mem_ball_zero_iff.1 hB).trans_le (k2.trans (by linarith)))
    exact ((hrelD B hBr).sub LQ.differentiableAt).differentiableWithinAt
  have hφK : ∀ B ∈ ball (0 : Fin 4 → Site n → Mat) c, ‖φ B‖ ≤ C₂ * ‖B‖ ^ 2 := fun B hB => by
    have hBc : ‖B‖ < c := mem_ball_zero_iff.1 hB
    have hBr : ‖restrictF B (InBoxB y h μ)‖ ≤ ‖B‖ := norm_restrictF_le _ _
    obtain ⟨-, -, hrem⟩ := hbox U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans k1) (hα₁c.trans k1) hplq A' hA B
    have := (hrem (hBr.trans_lt (hBc.trans_le k1))).1
    calc ‖φ B‖ ≤ C₂ * ‖restrictF B (InBoxB y h μ)‖ ^ 2 := this
      _ ≤ C₂ * ‖B‖ ^ 2 := by gcongr
  have hφM : ∀ B ∈ ball (0 : Fin 4 → Site n → Mat) c, ‖φ B‖ ≤ C₂ * c ^ 2 := fun B hB =>
    (hφK B hB).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.1 hB).le 2) hC₂)
  -- the derivative of the remainder vanishes at `0`
  have hφ0 : HasFDerivAt φ (0 : (Fin 4 → Site n → Mat) →L[ℂ] Mat) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun B : Fin 4 → Site n → Mat => φ B) =O[𝓝 0] (fun B => ‖B‖ ^ 2) := by
      refine Asymptotics.IsBigO.of_bound C₂ ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hc0)] with B hB
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hφK B hB
    have ho : (fun B : Fin 4 → Site n → Mat => ‖B‖ ^ 2) =o[𝓝 0] (fun B => B) := by
      have h1 : (fun B : Fin 4 → Site n → Mat => ‖B‖) =o[𝓝 0] (fun _ => (1 : ℝ)) := by
        rw [Asymptotics.isLittleO_one_iff]
        simpa using (continuous_norm.tendsto (0 : Fin 4 → Site n → Mat))
      have h2 := h1.mul_isBigO (Asymptotics.isBigO_refl (fun B : Fin 4 → Site n → Mat => ‖B‖) (𝓝 0))
      simp only [one_mul] at h2
      have h3 : (fun B : Fin 4 → Site n → Mat => ‖B‖ * ‖B‖) =o[𝓝 0] (fun B => B) :=
        h2.trans_isBigO (Asymptotics.isBigO_norm_left.2 (Asymptotics.isBigO_refl _ _))
      simpa [pow_two] using h3
    have hz : φ 0 = 0 := by
      have := hφK 0 (mem_ball_self hc0)
      rw [norm_zero, sq, mul_zero, mul_zero] at this
      exact norm_le_zero_iff.1 this
    refine (hO.trans_isLittleO ho).congr_left fun B => ?_
    rw [zero_add, hz, sub_zero, ContinuousLinearMap.zero_apply, sub_zero]
  have hφ0' : fderiv ℂ φ 0 = 0 := hφ0.fderiv
  -- the derivative near `0`
  have hrel : ∀ B, relLog (moveC U A') B y μ h = LQ B + φ B := fun B => by
    rw [linear_part]; rfl
  have hbsmall : ∀ᶠ s in 𝓝 (0 : ℂ), b s ∈ ball (0 : Fin 4 → Site n → Mat) c := by
    have hcont : ContinuousAt b 0 := hb1.continuousAt
    have hb0' : b 0 ∈ ball (0 : Fin 4 → Site n → Mat) c := by rw [hb0]; exact mem_ball_self hc0
    exact hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hb0')
  have hder : ∀ s, b s ∈ ball (0 : Fin 4 → Site n → Mat) c → DifferentiableAt ℂ b s →
      HasDerivAt (fun s => relLog (moveC U A') (b s) y μ h) (LQ (deriv b s) + fderiv ℂ φ (b s) (deriv b s)) s :=
    fun s hs hds => by
      have h1 := LQ.hasFDerivAt.comp_hasDerivAt s hds.hasDerivAt
      have h2 := ((hφd.differentiableAt (isOpen_ball.mem_nhds hs)).hasFDerivAt).comp_hasDerivAt s hds.hasDerivAt
      have h3 := h1.add h2
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s' => ?_)
      show relLog (moveC U A') (b s') y μ h = LQ (b s') + φ (b s')
      exact hrel (b s')
  have hd0 : DifferentiableAt ℂ b 0 := hb1.differentiableAt
  have hdb0 : deriv b 0 = b₁ := hb1.deriv
  refine ⟨?_, ?_⟩
  · have := hder 0 (by rw [hb0]; exact mem_ball_self hc0) hd0
    rwa [hdb0, hb0, hφ0', ContinuousLinearMap.zero_apply, add_zero] at this
  · have hev : (deriv fun s => relLog (moveC U A') (b s) y μ h) =ᶠ[𝓝 0]
        fun s => LQ (deriv b s) + fderiv ℂ φ (b s) (deriv b s) := by
      filter_upwards [hbsmall, hbd] with s hs hds
      exact (hder s hs hds).deriv
    have hsc := ParamDeriv.second_chain hc0 hφd hφM hb0 hb1 hb2
    have hl := LQ.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hb2
    have hsum := hl.add hsc
    rw [hφ0', ContinuousLinearMap.zero_apply, add_zero] at hsum
    exact hsum.congr_of_eventuallyEq hev

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The parts of the first and second order of the forms of the levels** (the proof of `lem:average-kernels`: "comparing
the parts of the second order we find `P_{l+1}(A) = Q^{(l)}P_l(A) + C^{(l)}_2(Λ_lA)`"): for the forms
`B(s)_{l+1} = (1/i) log 𝓜_{V_l}(B(s)_l)` of the line `B(s)_0 = sA`, holomorphic in `s` near `0` on the regions, with
`V_l = e^{iA'_l}U_l` of small data, the linear parts `D_{l+1} = LQ(V_l)D_l`, `D_0 = A`, are the derivatives at `0`, and
the forms `P_{l+1} = LQ(V_l)P_l + ∂_{RD_l}(C'(V_l; ·)RD_l)(0)`, `P_0 = 0` (`R` the restriction to the box of the bond),
are the second derivatives at `0` (`relLog_second` at each bond). -/
theorem forms_second_deriv (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (A' D P : ∀ l, Fin 4 → Site (nn l) → Mat) (Bf : ℂ → ∀ l, Fin 4 → Site (nn l) → Mat)
      (A : Fin 4 → Site (nn 0) → Mat) (a₀ a₁ : ℕ → ℝ) (ε : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l) ∧
        (∀ s, Bf s (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          relLog (moveC (U l) (A' l)) (Bf s l) (img h (base l) l x) ρ h) ∧
        D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (D l) ∧
        P (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (P l) +
            fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B
              (restrictF (D l) (InBoxB (img h (base l) l x) h ρ))) 0
              (restrictF (D l) (InBoxB (img h (base l) l x) h ρ))) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l ≤ c ∧ a₁ l ≤ c) → 0 < ε →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ∀ s ∈ ball (0 : ℂ) ε, DifferentiableAt ℂ (fun s => Bf s l ν (img h (base l) l x)) s) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        (∀ s, Bf s 0 ν (img h (base 0) 0 x) = s • A ν (img h (base 0) 0 x)) ∧
        D 0 ν (img h (base 0) 0 x) = A ν (img h (base 0) 0 x) ∧ P 0 ν (img h (base 0) 0 x) = 0) →
      ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        HasDerivAt (fun s => Bf s l ν (img h (base l) l x)) (D l ν (img h (base l) l x)) 0 ∧
        HasDerivAt (deriv fun s => Bf s l ν (img h (base l) l x)) (P l ν (img h (base l) l x)) 0 := by
  choose cs hcs hstep using fun ρ : Fin 4 => relLog_second (N := N) h ρ
  choose cP hcP hP using fun ρ : Fin 4 => relLog_core_pair_differentiableAt (N := N) h ρ
  set c := min (Finset.univ.inf' Finset.univ_nonempty cs) (Finset.univ.inf' Finset.univ_nonempty cP / 2)
  have hc0 : 0 < c := lt_min ((Finset.lt_inf'_iff _).2 fun ρ _ => hcs ρ)
    (by have := (Finset.lt_inf'_iff (s := Finset.univ) (H := Finset.univ_nonempty) (f := cP)).2 fun ρ _ => hcP ρ
        positivity)
  have hcle : ∀ ρ, c ≤ cs ρ := fun ρ => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hcleP : ∀ ρ, c ≤ cP ρ / 2 := fun ρ => (min_le_right _ _).trans
    (div_le_div_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ ρ)) (by norm_num))
  refine ⟨c, hc0, ?_⟩
  intro nl μ nn _ hn base U A' D P Bf A a₀ a₁ ε hU hdat ha hε hhol h0
  -- the forms vanish at `s = 0`
  have hzero : ∀ l, l ≤ nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
      Bf 0 l ν (img h (base l) l x) = 0 :=
    forms_zero h nl μ nn hn base (fun l => moveC (U l) (A' l)) (Bf 0)
      (fun l hl ρ x hx q0 q1 => (hdat l hl ρ x hx q0 q1).2.2.1 0)
      (fun ν x hx q0 q1 => by rw [(h0 ν x hx q0 q1).1 0, zero_smul])
  intro l
  induction l with
  | zero =>
    intro _ ν x hx q0 q1
    obtain ⟨hB, hD, hP⟩ := h0 ν x hx q0 q1
    have e : (fun s => Bf s 0 ν (img h (base 0) 0 x)) = fun s => s • A ν (img h (base 0) 0 x) := funext hB
    rw [e, hD, hP]
    refine ⟨by simpa using (hasDerivAt_id (0 : ℂ)).smul_const (A ν (img h (base 0) 0 x)), ?_⟩
    have hd : (deriv fun s : ℂ => s • A ν (img h (base 0) 0 x)) = fun _ => A ν (img h (base 0) 0 x) := by
      funext s
      exact ((hasDerivAt_id s).smul_const (A ν (img h (base 0) 0 x))).deriv.trans (one_smul _ _)
    rw [hd]
    exact hasDerivAt_const _ _
  | succ l ih =>
    intro hl ρ x hx q0 q1
    have hll : l < nl := by omega
    have hn2 : 4 * h + 2 ≤ nn l := by have := hn l; omega
    obtain ⟨ha0, ha1, ha0c, ha1c⟩ := ha l hll
    obtain ⟨hpl, hA, hrec, hDe, hPe⟩ := hdat l hll ρ x hx q0 q1
    set y := img h (base l) l x
    set b : ℂ → Fin 4 → Site (nn l) → Mat := fun s => restrictF (Bf s l) (InBoxB y h ρ) with hb
    -- the components of the restricted forms
    have hcomp : ∀ ν z, (BoxBond y h ρ ν z ∧ ∃ x', Lat (Lz h) l x' ∧ Rg h nl μ l x' ∧
        Rg h nl μ l (x' + Lz h ^ l • Pi.single ν 1) ∧ z = img h (base l) l x') ∨
        (¬ BoxBond y h ρ ν z ∧ ∀ s, b s ν z = 0) := fun ν z => by
      by_cases hbb : BoxBond y h ρ ν z
      · obtain ⟨x', hx', r0, r1, rfl⟩ := box_site (hn l) (base l) hx q0 q1 hbb
        exact Or.inl ⟨hbb, x', hx', r0, r1, rfl⟩
      · exact Or.inr ⟨hbb, fun s => by simp only [hb]; exact restrictF_box_apply' _ hbb⟩
    have hbval : ∀ ν z, BoxBond y h ρ ν z → ∀ s, b s ν z = Bf s l ν z := fun ν z hbb s => by
      simp only [hb]; exact restrictF_box_apply _ hbb
    have hb0 : b 0 = 0 := by
      funext ν z
      rcases hcomp ν z with ⟨hbb, x', hx', r0, r1, rfl⟩ | ⟨hbb, hz⟩
      · rw [hbval ν _ hbb]; exact hzero l hll.le ν x' hx' r0 r1
      · exact hz 0
    -- the differentiability near `0`, componentwise
    have hcd : ∀ ν z, ∀ s ∈ ball (0 : ℂ) ε, DifferentiableAt ℂ (fun s => b s ν z) s := fun ν z s hs => by
      rcases hcomp ν z with ⟨hbb, x', hx', r0, r1, rfl⟩ | ⟨hbb, hz⟩
      · have e : (fun s => b s ν (img h (base l) l x')) = fun s => Bf s l ν (img h (base l) l x') :=
          funext (hbval ν _ hbb)
        rw [e]; exact hhol l hll ν x' hx' r0 r1 s hs
      · have e : (fun s => b s ν z) = fun _ => 0 := funext hz
        rw [e]; exact differentiableAt_const _
    have hbd : ∀ s ∈ ball (0 : ℂ) ε, DifferentiableAt ℂ b s := fun s hs =>
      differentiableAt_pi.2 fun ν => differentiableAt_pi.2 fun z => hcd ν z s hs
    have hbd' : ∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ b s := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with s hs using hbd s hs
    -- the first and second derivatives of the restricted forms
    have hb1 : HasDerivAt b (restrictF (D l) (InBoxB y h ρ)) 0 := by
      refine hasDerivAt_pi.2 fun ν => hasDerivAt_pi.2 fun z => ?_
      rcases hcomp ν z with ⟨hbb, x', hx', r0, r1, rfl⟩ | ⟨hbb, hz⟩
      · have e : (fun s => b s ν (img h (base l) l x')) = fun s => Bf s l ν (img h (base l) l x') :=
          funext (hbval ν _ hbb)
        rw [e, restrictF_box_apply _ hbb]; exact (ih hll.le ν x' hx' r0 r1).1
      · have e : (fun s => b s ν z) = fun _ => 0 := funext hz
        rw [e, restrictF_box_apply' _ hbb]; exact hasDerivAt_const _ _
    have hderb : (deriv b) =ᶠ[𝓝 (0 : ℂ)] fun s => fun ν z => deriv (fun s => b s ν z) s := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with s hs
      funext ν z
      rw [deriv_pi (fun ν => differentiableAt_pi.2 fun z => hcd ν z s hs)]
      beta_reduce
      rw [deriv_pi (fun z => hcd ν z s hs)]
    have hb2 : HasDerivAt (deriv b) (restrictF (P l) (InBoxB y h ρ)) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq ?_ hderb
      refine hasDerivAt_pi.2 fun ν => hasDerivAt_pi.2 fun z => ?_
      rcases hcomp ν z with ⟨hbb, x', hx', r0, r1, rfl⟩ | ⟨hbb, hz⟩
      · have e : (fun s => b s ν (img h (base l) l x')) = fun s => Bf s l ν (img h (base l) l x') :=
          funext (hbval ν _ hbb)
        simp only [e]
        rw [restrictF_box_apply _ hbb]; exact (ih hll.le ν x' hx' r0 r1).2
      · have e : (fun s => b s ν z) = fun _ => 0 := funext hz
        simp only [e, deriv_const]
        rw [restrictF_box_apply' _ hbb]; exact hasDerivAt_const _ _
    -- one step
    obtain ⟨hs1, hs2⟩ := hstep ρ (U l) (hU l) (hn l) y (a₀ l) (a₁ l) ha0 ha1 (ha0c.trans (hcle ρ))
      (ha1c.trans (hcle ρ)) hpl (A' l) hA b (restrictF (D l) (InBoxB y h ρ)) (restrictF (P l) (InBoxB y h ρ)) hb0 hb1 hb2 hbd'
    have hfun : (fun s => Bf s (l + 1) ρ (img h (base (l + 1)) (l + 1) x)) =
        fun s => relLog (moveC (U l) (A' l)) (b s) y ρ h := by
      funext s
      rw [hrec s, relLog_box hn2 (moveC (U l) (A' l)) y ρ (Bf s l)]
    -- `Q` sees the values on the box only
    have hcP' : c < cP ρ := lt_of_le_of_lt (hcleP ρ) (by linarith [hcP ρ])
    have hd0 : DifferentiableAt ℂ (fun B => relLog (moveC (U l) (A' l)) B y ρ h) 0 := by
      have hpd := hP ρ (U l) (hU l) (hn l) y (a₀ l) ha0 (ha0c.trans hcP'.le) hpl (A' l) 0
        ((norm_restrictF_box_le ha1 hA).trans_lt (lt_of_le_of_lt ha1c hcP'))
        ((norm_restrictF_le _ _).trans_lt (by simpa using hcP ρ))
      have hlin : DifferentiableAt ℂ (fun B' : Fin 4 → Site (nn l) → Mat => (A' l, B')) 0 :=
        (differentiableAt_const (A' l)).prodMk differentiableAt_id
      exact hpd.comp 0 hlin
    have hQ := Qlin_box hn2 (moveC (U l) (A' l)) y ρ hd0
    have hQX : ∀ X : Fin 4 → Site (nn l) → Mat,
        Qlin (moveC (U l) (A' l)) y ρ h (restrictF X (InBoxB y h ρ)) = Qlin (moveC (U l) (A' l)) y ρ h X := fun X => by
      conv_rhs => rw [hQ]
      rfl
    rw [hfun]
    refine ⟨?_, ?_⟩
    · rw [hDe, ← hQX]; exact hs1
    · rw [hPe, ← hQX]; exact hs2

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The mixed second derivative of the remainder is bilinear**, with its bound: for a gauge field `U` and `A'` with
small data, `D²C(X, Y) = ∂_X(C'(·)Y)(0)` is additive in `Y` (it is linear in `X` as a derivative), and
`‖D²C(X, Y)‖ ≤ (16/3)C₂‖X‖_{box}‖Y‖_{box}` (`Crem_second_bound`). Additivity in `Y`: `C'(B)` is linear for every `B`, and
`B ↦ C'(B)Y` is holomorphic near `0` (`fderiv_apply_differentiableOn`). -/
theorem Crem_D2 (h : ℕ) (μ : Fin 4) :
    ∃ c C₂ : ℝ, 0 < c ∧ 0 ≤ C₂ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        (∀ X Y : Fin 4 → Site n → Mat,
          ‖fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B Y) 0 X‖ ≤
            16 / 3 * C₂ * ‖restrictF X (InBoxB y h μ)‖ * ‖restrictF Y (InBoxB y h μ)‖) ∧
        (∀ X Y₁ Y₂ : Fin 4 → Site n → Mat,
          fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B (Y₁ + Y₂)) 0 X =
            fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B Y₁) 0 X +
            fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B Y₂) 0 X) := by
  obtain ⟨c₁, C₂, hc₁, hC₂, hbd⟩ := Crem_second_bound (N := N) h μ
  obtain ⟨cb, C₀, C₁, C₂', C₃, hcb, hC₀, hC₁, hC₂', hC₃, hbox⟩ := relative_average_box (N := N) h μ
  obtain ⟨cP, hcP, hP⟩ := relLog_core_pair_differentiableAt (N := N) h μ
  set c := min c₁ (min cb (cP / 2)) with hc_def
  have k0 : c ≤ c₁ := min_le_left _ _
  have k1 : c ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have k2 : c ≤ cP / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hc0 : 0 < c := lt_min hc₁ (lt_min hcb (by positivity))
  refine ⟨c, C₂, hc0, hC₂, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA
  refine ⟨hbd U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans k0) (hα₁c.trans k0) hplq A' hA, ?_⟩
  set φ : (Fin 4 → Site n → Mat) → Mat := fun B => Crem (moveC U A') B y μ h with hφ
  set LQ : (Fin 4 → Site n → Mat) →L[ℂ] Mat := ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h with hLQ
  have hA'r : ‖restrictF A' (InBoxB y h μ)‖ < cP := (norm_restrictF_box_le hα₁ hA).trans_lt (by linarith)
  have hα₀P : α₀ ≤ cP := hα₀c.trans (k2.trans (by linarith))
  have hrelD : ∀ B : Fin 4 → Site n → Mat, ‖restrictF B (InBoxB y h μ)‖ < cP →
      DifferentiableAt ℂ (fun B => relLog (moveC U A') B y μ h) B := fun B hB => by
    have hpd := hP U hU hn y α₀ hα₀ hα₀P hplq A' B hA'r hB
    have hlin : DifferentiableAt ℂ (fun B' : Fin 4 → Site n → Mat => (A', B')) B :=
      (differentiableAt_const A').prodMk differentiableAt_id
    exact hpd.comp B hlin
  have hφd : DifferentiableOn ℂ φ (ball 0 c) := fun B hB => by
    have hBr : ‖restrictF B (InBoxB y h μ)‖ < cP :=
      (norm_restrictF_le _ _).trans_lt ((mem_ball_zero_iff.1 hB).trans_le (k2.trans (by linarith)))
    exact ((hrelD B hBr).sub LQ.differentiableAt).differentiableWithinAt
  have hφM : ∀ B ∈ ball (0 : Fin 4 → Site n → Mat) c, ‖φ B‖ ≤ C₂' * c ^ 2 := fun B hB => by
    have hBc : ‖B‖ < c := mem_ball_zero_iff.1 hB
    have hBr : ‖restrictF B (InBoxB y h μ)‖ ≤ ‖B‖ := norm_restrictF_le _ _
    obtain ⟨-, -, hrem⟩ := hbox U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans k1) (hα₁c.trans k1) hplq A' hA B
    have := (hrem (hBr.trans_lt (hBc.trans_le k1))).1
    calc ‖φ B‖ ≤ C₂' * ‖restrictF B (InBoxB y h μ)‖ ^ 2 := this
      _ ≤ C₂' * c ^ 2 := by gcongr; exact hBr.trans hBc.le
  intro X Y₁ Y₂
  have hk : ∀ Y, DifferentiableAt ℂ (fun B => fderiv ℂ φ B Y) 0 := fun Y =>
    (ParamDeriv.fderiv_apply_differentiableOn hc0 hφd hφM Y).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  have e : (fun B => fderiv ℂ φ B (Y₁ + Y₂)) = (fun B => fderiv ℂ φ B Y₁) + (fun B => fderiv ℂ φ B Y₂) := by
    funext B; simp only [map_add, Pi.add_apply]
  show fderiv ℂ (fun B => fderiv ℂ φ B (Y₁ + Y₂)) 0 X =
    fderiv ℂ (fun B => fderiv ℂ φ B Y₁) 0 X + fderiv ℂ (fun B => fderiv ℂ φ B Y₂) 0 X
  rw [e, fderiv_add (hk Y₁) (hk Y₂), ContinuousLinearMap.add_apply]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`lem:average-kernels`, the second bound**: under the per-level hypotheses with data at most `eL^{-(n-l)}`, the
linear parts `D¹_{l+1} = LQ(V_l)D¹_l`, `D²_{l+1} = LQ(V_l)D²_l` of `A₁` and `A₂`, with `‖D²_l‖ ≤ s₀L^l` on the regions, and
the second derivatives `P^±` of the forms along the lines `s(A₁ ± A₂)` (`forms_second_deriv`:
`P^±_{l+1} = LQ(V_l)P^±_l + D²C_l(R(D¹_l ± D²_l), R(D¹_l ± D²_l))`, `P^±_0 = 0`), the symmetric bilinear map
`𝖢⁽²⁾_n(A₁, A₂) = (P^+_n - P^-_n)/8`, whose diagonal is the part of the second order `½P_n(A)` of the forms, satisfies
`Σ_c‖𝖢⁽²⁾_n(A₁, A₂)(c)‖ ≤ (256/3)C₂L³s₀L^{-2n}Σ_{b'}‖A₁(b')‖`. For `A₁` supported on one bond this is the second bound of
`eq:average-kernels` in the units of the lattices. The polarisation turns the recursions of `P^±` into the recursion of
`quadratic_kernel` with `Y_l = ¼(D²C_l(RD¹_l, RD²_l) + D²C_l(RD²_l, RD¹_l))`, at most `(8/3)C₂‖RD²_l‖‖RD¹_l‖` by `Crem_D2`. -/
theorem average_kernels_ii (h : ℕ) (hh : 1 ≤ h) :
    ∃ c C C₂ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₂ ∧ ∀ (nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)],
      (∀ l, 4 * h + 4 ≤ nn l) → ∀ (base : ∀ l, Site (nn l)) (U : ∀ l, Config N (nn l))
      (A' D₁ D₂ Pp Pm : ∀ l, Fin 4 → Site (nn l) → Mat) (a₀ a₁ : ℕ → ℝ) (e s₀ : ℝ),
      (∀ l, U l |>.IsGaugeField) →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        (∀ μ' ν' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h ρ ρ)) μ' ν' z →
          hs (((plaq (U l) μ' ν' z : GLN) : Mat) - 1) ≤ a₀ l) ∧
        (∀ ν z, BoxBond (img h (base l) l x) h ρ ν z → ‖A' l ν z‖ ≤ a₁ l)) →
      (∀ l, l < nl → 0 ≤ a₀ l ∧ 0 ≤ a₁ l ∧ a₀ l + a₁ l ≤ e * ((((2 * h + 1 : ℕ) : ℝ)) ^ (nl - l))⁻¹) →
      0 ≤ e → e ≤ c → 8 * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * C * e ≤ 1 → 0 ≤ s₀ →
      (∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
        Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        D₁ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (D₁ l) ∧
        D₂ (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (D₂ l) ∧
        Pp (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (Pp l) +
            fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B
              (restrictF (D₁ l + D₂ l) (InBoxB (img h (base l) l x) h ρ))) 0
              (restrictF (D₁ l + D₂ l) (InBoxB (img h (base l) l x) h ρ)) ∧
        Pm (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (Pm l) +
            fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B
              (restrictF (D₁ l - D₂ l) (InBoxB (img h (base l) l x) h ρ))) 0
              (restrictF (D₁ l - D₂ l) (InBoxB (img h (base l) l x) h ρ))) →
      (∀ l, l < nl → ∀ ν x, Lat (Lz h) l x → Rg h nl μ l x → Rg h nl μ l (x + Lz h ^ l • Pi.single ν 1) →
        ‖D₂ l ν (img h (base l) l x)‖ ≤ s₀ * (((2 * h + 1 : ℕ) : ℝ)) ^ l) →
      (∀ ν x, Lat (Lz h) 0 x → Rg h nl μ 0 x → Rg h nl μ 0 (x + Lz h ^ 0 • Pi.single ν 1) →
        Pp 0 ν (img h (base 0) 0 x) = 0 ∧ Pm 0 ν (img h (base 0) 0 x) = 0) →
      ell1 h nl μ nl (fun x ν => ‖(1 / 8 : ℂ) • (Pp nl ν (img h (base nl) nl x) - Pm nl ν (img h (base nl) nl x))‖) ≤
        32 * (8 / 3 * C₂) * (((2 * h + 1 : ℕ) : ℝ)) ^ 3 * s₀ * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl *
          ell1 h nl μ 0 (fun x ν => ‖D₁ 0 ν (img h (base 0) 0 x)‖) := by
  obtain ⟨cq, Cq, hcq, hCq, hQK⟩ := quadratic_kernel (N := N) h hh
  choose cd Cd hcd hCd hD2 using fun ρ : Fin 4 => Crem_D2 (N := N) h ρ
  set C₂ := Finset.univ.sup' Finset.univ_nonempty Cd
  have hCle : ∀ ρ, Cd ρ ≤ C₂ := fun ρ => Finset.le_sup' _ (Finset.mem_univ ρ)
  have hC₂0 : 0 ≤ C₂ := (hCd 0).trans (hCle 0)
  set c := min cq (Finset.univ.inf' Finset.univ_nonempty cd)
  have kq : c ≤ cq := min_le_left _ _
  have kd : ∀ ρ, c ≤ cd ρ := fun ρ => (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hc0 : 0 < c := lt_min hcq ((Finset.lt_inf'_iff _).2 fun ρ _ => hcd ρ)
  refine ⟨c, Cq, C₂, hc0, hCq, hC₂0, ?_⟩
  intro nl μ nn _ hn base U A' D₁ D₂ Pp Pm a₀ a₁ e s₀ hU hdat ha he hec hCe hs₀ hrel hD₂ hP0
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr
  have hp1 : ∀ m, (Lr ^ m)⁻¹ ≤ 1 := fun m => inv_le_one_of_one_le₀ (one_le_pow₀ (by rw [hLr]; push_cast; linarith))
  set Q : ∀ l, Fin 4 → Site (nn l) → Mat := fun l ν z => (1 / 8 : ℂ) • (Pp l ν z - Pm l ν z) with hQ
  set Y : ℕ → (Fin 4 → ℤ) → Fin 4 → Mat := fun l x ρ => (1 / 8 : ℂ) •
    (fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B
        (restrictF (D₁ l + D₂ l) (InBoxB (img h (base l) l x) h ρ))) 0
        (restrictF (D₁ l + D₂ l) (InBoxB (img h (base l) l x) h ρ)) -
      fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B
        (restrictF (D₁ l - D₂ l) (InBoxB (img h (base l) l x) h ρ))) 0
        (restrictF (D₁ l - D₂ l) (InBoxB (img h (base l) l x) h ρ))) with hY
  have key := hQK nl μ nn hn base U (fun l => moveC (U l) (A' l)) A' D₁ D₂ Q Y a₀ a₁ e (8 / 3 * C₂) s₀ hU
    (fun l _ ν x _ _ _ => rfl) hdat ha he (hec.trans kq) hCe (by positivity) hs₀
    (fun l hl ρ x hx q0 q1 => ?_) hD₂ (fun ν x hx q0 q1 => by
      simp only [hQ, (hP0 ν x hx q0 q1).1, (hP0 ν x hx q0 q1).2, sub_self, smul_zero])
  · simpa only [hQ] using key
  -- the recursion of `Q` and the bound of `Y`
  obtain ⟨hD1e, -, hPpe, hPme⟩ := hrel l hl ρ x hx q0 q1
  refine ⟨hD1e, ?_, ?_⟩
  · have hQl : Q l = (1 / 8 : ℂ) • (Pp l - Pm l) := by funext ν z; rfl
    show (1 / 8 : ℂ) • (Pp (l + 1) ρ (img h (base (l + 1)) (l + 1) x) - Pm (l + 1) ρ (img h (base (l + 1)) (l + 1) x)) =
      ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC (U l) (A' l)) (img h (base l) l x) ρ h (Q l) + Y l x ρ
    rw [hQl, hPpe, hPme]
    simp only [hY, map_sub, map_smul, smul_sub, smul_add, smul_smul]
    rw [mul_comm (1 / 8 : ℂ) ((2 * h + 1 : ℕ) : ℂ)]
    abel
  · obtain ⟨ha0, ha1, hae⟩ := ha l hl
    have hae' : a₀ l + a₁ l ≤ e := by have := hp1 (nl - l); nlinarith
    obtain ⟨hpl, hA⟩ := hdat l hl ρ x hx q0 q1
    obtain ⟨hb, hadd⟩ := hD2 ρ (U l) (hU l) (hn l) (img h (base l) l x) (a₀ l) (a₁ l) ha0 ha1
      (by linarith [hec.trans (kd ρ)]) (by linarith [hec.trans (kd ρ)]) hpl (A' l) hA
    set S := InBoxB (img h (base l) l x) h ρ
    set R1 := restrictF (D₁ l) S
    set R2 := restrictF (D₂ l) S
    have hRadd : restrictF (D₁ l + D₂ l) S = R1 + R2 := by
      have := map_add (restrictBoxL (img h (base l) l x) h ρ) (D₁ l) (D₂ l)
      simpa only [restrictBoxL_apply] using this
    have hRsub : restrictF (D₁ l - D₂ l) S = R1 - R2 := by
      have := map_sub (restrictBoxL (img h (base l) l x) h ρ) (D₁ l) (D₂ l)
      simpa only [restrictBoxL_apply] using this
    set T : (Fin 4 → Site (nn l) → Mat) → (Fin 4 → Site (nn l) → Mat) → Mat := fun X Y' =>
      fderiv ℂ (fun B => fderiv ℂ (fun B' => Crem (moveC (U l) (A' l)) B' (img h (base l) l x) ρ h) B Y') 0 X
      with hT
    have haddT : ∀ X Y₁ Y₂, T X (Y₁ + Y₂) = T X Y₁ + T X Y₂ := hadd
    have hlinX : ∀ X₁ X₂ Y', T (X₁ + X₂) Y' = T X₁ Y' + T X₂ Y' := fun X₁ X₂ Y' => by simp only [hT, map_add]
    have hnegX : ∀ X Y', T (-X) Y' = -T X Y' := fun X Y' => by simp only [hT, map_neg]
    have hnegY : ∀ X Y', T X (-Y') = -T X Y' := fun X Y' => by
      have h1 := haddT X Y' (-Y')
      simp only [add_neg_cancel] at h1
      have h0 : T X 0 = 0 := by
        have h2 := haddT X 0 0
        simp only [add_zero] at h2
        have : T X 0 = T X 0 + T X 0 := h2
        simpa using this
      have : T X 0 = T X Y' + T X (-Y') := h1
      rw [h0] at this
      exact (eq_neg_of_add_eq_zero_right this.symm)
    have hpol : T (R1 + R2) (R1 + R2) - T (R1 - R2) (R1 - R2) = 2 • (T R1 R2 + T R2 R1) := by
      have a1 : T (R1 + R2) (R1 + R2) = T R1 R1 + T R1 R2 + (T R2 R1 + T R2 R2) := by
        rw [hlinX, haddT, haddT]
      have a2 : T (R1 - R2) (R1 - R2) = T R1 R1 - T R1 R2 - (T R2 R1 - T R2 R2) := by
        rw [sub_eq_add_neg R1 R2, hlinX, haddT, haddT, hnegX, hnegY, hnegY, hnegX]
        simp only [neg_neg]; abel
      rw [a1, a2]; abel
    have hYv : Y l x ρ = (1 / 4 : ℂ) • (T R1 R2 + T R2 R1) := by
      simp only [hY]
      rw [hRadd, hRsub]
      show (1 / 8 : ℂ) • (T (R1 + R2) (R1 + R2) - T (R1 - R2) (R1 - R2)) = _
      rw [hpol, two_smul, smul_add, ← add_smul]
      norm_num
    have hRR1 : restrictF R1 S = R1 := restrictF_restrictF (D₁ l) S
    have hRR2 : restrictF R2 S = R2 := restrictF_restrictF (D₂ l) S
    have hb12 := hb R1 R2
    have hb21 := hb R2 R1
    rw [hRR1, hRR2] at hb12 hb21
    rw [hYv, norm_smul]
    have hCdC : Cd ρ ≤ C₂ := hCle ρ
    have hn1 := norm_nonneg R1
    have hn2 := norm_nonneg R2
    calc ‖(1 / 4 : ℂ)‖ * ‖T R1 R2 + T R2 R1‖ ≤ (1 / 4) * (‖T R1 R2‖ + ‖T R2 R1‖) := by
          rw [show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ (1 / 4) * (16 / 3 * Cd ρ * ‖R1‖ * ‖R2‖ + 16 / 3 * Cd ρ * ‖R2‖ * ‖R1‖) := by gcongr
      _ = 8 / 3 * Cd ρ * ‖R2‖ * ‖R1‖ := by ring
      _ ≤ 8 / 3 * C₂ * ‖R2‖ * ‖R1‖ := by gcongr

/-- **`prop:momentum-space`(i), the average `Q'_k` at the trivial configuration**: if `λ_{l+1} = Q'(id)λ_l` on the regions
of the levels, then `λ_l(y)` is the mean of `λ_0` over the block `Bˡ(y)` of the level `0`: the transports of the trivial
configuration are `id`, so the composite transports `W(y, x)` of `block_composite` are `id`. -/
theorem Qprime_trivial (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l))
    (lam : ∀ l, Site (nn l) → Mat)
    (hlam : ∀ l, l < nl → ∀ y, Lat (Lz h) (l + 1) y → Rg h nl μ (l + 1) y →
      lam (l + 1) (img h (base (l + 1)) (l + 1) y) = blockAvg (oneC (N := N)) (lam l) (img h (base l) l y) h) :
    ∀ l, l ≤ nl → ∀ y, Lat (Lz h) l y → Rg h nl μ l y →
      lam l (img h (base l) l y) = ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l •
        ∑ p : Fin l → Pts h, lam 0 (img h (base 0) 0 (ptB h l y p)) := by
  intro l hl y hy hR
  have hc := block_composite h nl μ nn base (fun _ => oneC (N := N)) lam hlam l hl y hy hR
  have hW : ∀ (l : ℕ) (y : Fin 4 → ℤ) (p : Fin l → Pts h), WB h nn base (fun _ => oneC (N := N)) l y p = 1 := by
    intro l
    induction l with
    | zero => intro y p; rfl
    | succ l ih =>
      intro y p
      simp only [WB, ih, mul_one]
      rw [← moveC_zero (oneC (N := N))]
      exact trans_oneC_zero _ h _
  rw [hc]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hW]
  simp [Ad]

lemma ptB_add (h : ℕ) : ∀ (l : ℕ) (y v : Fin 4 → ℤ) (p : Fin l → Pts h), ptB h l (y + v) p = ptB h l y p + v
  | 0, _, _, _ => rfl
  | l + 1, y, v, p => by
    simp only [ptB]
    rw [show y + v + Lz h ^ l • offP h (p 0) = y + Lz h ^ l • offP h (p 0) + v by abel]
    exact ptB_add h l _ v _

lemma sum_range_mul_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range m, ∑ J ∈ Finset.range n, f (n * j + J) = ∑ k ∈ Finset.range (m * n), f k
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_range_mul_add f n m, show (m + 1) * n = m * n + n by ring, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_comm n m]

set_option maxHeartbeats 4000000 in
/-- **`prop:momentum-space`(i), the average `Q_k` at the trivial configuration**: if `B_{l+1} = L·Q(id)B_l` on the regions
of the levels, then `B_l(y, ρ) = L^{-4l} Σ_{x ∈ Bˡ(y)} Σ_{J < Lˡ} B_0(x + Je_ρ, ρ)`: `L^lQ_l(id)` sums `B_0` over the `Lˡ`
bonds of the straight path from each point `x` of the block to `x + Lˡe_ρ`, and averages over the block. One step is
`Qlin_oneC`; the lines of the steps compose because the block points are translation covariant (`ptB_add`). -/
theorem Q_trivial_levels (h nl : ℕ) (μ : Fin 4) (nn : ℕ → ℕ) [∀ l, NeZero (nn l)] (base : ∀ l, Site (nn l))
    (B : ∀ l, Fin 4 → Site (nn l) → Mat)
    (hrec : ∀ l, l < nl → ∀ ρ x, Lat (Lz h) (l + 1) x → Rg h nl μ (l + 1) x →
      Rg h nl μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      B (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
        ((2 * h + 1 : ℕ) : ℂ) • Qlin (oneC (N := N)) (img h (base l) l x) ρ h (B l)) :
    ∀ l, l ≤ nl → ∀ ρ x, RB h nl μ l x ρ →
      B l ρ (img h (base l) l x) = ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l •
        ∑ p : Fin l → Pts h, ∑ J ∈ Finset.range ((2 * h + 1) ^ l),
          B 0 ρ (img h (base 0) 0 (ptB h l x p + (J : ℤ) • Pi.single ρ 1)) := by
  intro l
  induction l with
  | zero =>
    intro _ ρ x _
    simp [ptB]
  | succ l ih =>
    intro hl ρ x hb
    have hll : l < nl := by omega
    obtain ⟨hx, q0, q1⟩ := hb
    have hxl := lat_succ_le hx
    rw [hrec l hll ρ x hx q0 q1]
    have hT := Qlin_oneC (N := N) (img h (base l) l x) ρ h
    rw [show ((2 * h + 1 : ℕ) : ℂ) • Qlin (oneC (N := N)) (img h (base l) l x) ρ h (B l) =
      (((2 * h + 1 : ℕ) : ℂ) • Qlin (oneC (N := N)) (img h (base l) l x) ρ h) (B l) from rfl, hT]
    simp only [TsumL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
    -- the bonds of the lines
    have hline : ∀ xp : Pts h, BsumL (N := N) (segZ ρ (ofs (img h (base l) l x) (offP h xp)) ((2 * h + 1 : ℕ) : ℤ)) (B l) =
        ∑ j ∈ Finset.range (2 * h + 1),
          B l ρ (img h (base l) l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1))) := by
      intro xp
      rw [segZ_eq]
      simp only [sgn, Int.natAbs_natCast]
      rw [show decide (0 ≤ ((2 * h + 1 : ℕ) : ℤ)) = true from decide_eq_true (by positivity), BsumL_seg_true, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [evalL, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply]
      have hz := lat_add_smul hxl (offP h xp)
      have key : img h (base l) l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) =
          ofs (img h (base l) l (x + Lz h ^ l • offP h xp)) ((0 : Fin 4 → ℤ) + Pi.single ρ (j : ℤ)) := by
        rw [img_add (base l) hz, zero_add, smul_add, add_assoc]
        congr 3
        funext σ; simp [Pi.single_apply]
      rw [img_add (base l) hxl, key, ofs_add_single, ofs_zero, natCast_zsmul]
    simp only [hline]
    -- the induction hypothesis on each bond of the lines
    have hIH : ∀ (xp : Pts h) (j : ℕ), j ∈ Finset.range (2 * h + 1) →
        B l ρ (img h (base l) l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1))) =
          ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹) ^ l • ∑ p : Fin l → Pts h, ∑ J ∈ Finset.range ((2 * h + 1) ^ l),
            B 0 ρ (img h (base 0) 0 (ptB h (l + 1) x (Fin.cons xp p) +
              (((2 * h + 1) ^ l * j + J : ℕ) : ℤ) • Pi.single ρ 1)) := by
      intro xp j hj
      rw [ih hll.le ρ _ (line_RB ⟨hx, q0, q1⟩ xp (Finset.mem_range.1 hj))]
      congr 1
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun J _ => ?_
      have harg : ptB h l (x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1)) p + (J : ℤ) • Pi.single ρ 1 =
          ptB h (l + 1) x (Fin.cons xp p) + (((2 * h + 1) ^ l * j + J : ℕ) : ℤ) • Pi.single ρ 1 := by
        simp only [ptB, Fin.cons_zero, Fin.tail_cons]
        have hsplit : x + Lz h ^ l • (offP h xp + (j : ℤ) • Pi.single ρ 1) =
            x + Lz h ^ l • offP h xp + (Lz h ^ l * (j : ℤ)) • Pi.single ρ 1 := by
          rw [smul_add, smul_smul, add_assoc]
        rw [hsplit, ptB_add, add_assoc, ← add_smul]
        congr 2
      rw [harg]
    rw [Finset.sum_congr rfl fun xp _ => Finset.sum_congr rfl fun j hj => hIH xp j hj]
    simp only [← Finset.smul_sum]
    rw [smul_smul, ← pow_succ']
    congr 1
    -- reindex: `(xp, p, j, J) ↦ (cons xp p, Lˡj + J)`
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (l + 1) => Pts h), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun xp _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.consEquiv_apply]
    rw [pow_succ, mul_comm ((2 * h + 1) ^ l)]
    exact sum_range_mul_add (M := Mat) (fun k : ℕ => B 0 ρ (img h (base 0) 0 (ptB h (l + 1) x (Fin.cons xp p) +
      (k : ℤ) • (Pi.single ρ 1 : Fin 4 → ℤ)))) ((2 * h + 1) ^ l) (2 * h + 1)

end RelativeAverage
end CoreLean


end
