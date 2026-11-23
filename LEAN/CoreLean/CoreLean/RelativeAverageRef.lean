/-
The reduction to the polydisc of the proof of `prop:relative-average` of BALABAN_CORE.tex (`d8bdc4ac1777`), first
part: the domain of holomorphy on the reference torus.

On the torus `Site (4h + 2)` (the reference of (viii), `RelativeAverageTransfer.lean`) the configurations `𝐔_X = e^{iX}`
(`UX`, the trivial gauge field with the fluctuation `X`) and the forms `B = aA` form the finite-dimensional space of
the pairs `p = (X, B)`. All the conditions under which the transports, the site factors, the averages, and
`(1/i) Log 𝓜` are holomorphic (`Cond`) hold at `p = 0`, where every holonomy is `id`, and they are strict inequalities
between functions continuous at `0`; so they hold on a ball about `0` (`eventually_cond`), whose radius depends on `h`
and `N` only. On it `p ↦ (1/i) Log 𝓜_{𝐔_X}(B)(c)` is holomorphic (`relLog_differentiableAt_pair`).
-/
import CoreLean.RelativeAverageTransfer

open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Families of configurations -/

lemma eventually_goodAt_family (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) {y : Site n} {h : ℕ}
    (hg : GoodAt (V p₀) y h) : ∀ᶠ p in 𝓝 p₀, GoodAt (V p) y h := by
  have h1 : ∀ x i, ∀ᶠ p in 𝓝 p₀, ‖((quotG (V p) y h x i : GLN) : Mat) - 1‖ < 1 := fun x i => by
    have hc : ContinuousAt (fun p => ((quotG (V p) y h x i : GLN) : Mat)) p₀ := by
      simp only [quotG, Units.val_mul]
      exact ((hol_differentiableAt V hV _).mul (inv_differentiableAt (hol_differentiableAt V hV _))).continuousAt
    exact ContinuousAt.eventually_lt (g := fun _ => (1 : ℝ)) (hc.sub continuousAt_const).norm
      continuousAt_const (hg.1 x i)
  have h2 : ∀ x, ∀ᶠ p in 𝓝 p₀, ‖expsG (V p) y h x‖ < 1 / 1024 := fun x =>
    ContinuousAt.eventually_lt (g := fun _ => (1 / 1024 : ℝ))
      (expsG_differentiableAt V hV y h x (hg.1 x)).continuousAt.norm continuousAt_const (hg.2 x)
  exact (eventually_all.2 fun x => eventually_all.2 fun i => h1 x i).and (eventually_all.2 h2)

lemma eventually_loopsGood_family (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) {y : Site n} {μ : Fin 4} {h : ℕ}
    (hl : LoopsGood (V p₀) y μ h) : ∀ᶠ p in 𝓝 p₀, LoopsGood (V p) y μ h :=
  eventually_all.2 fun x => eventually_all.2 fun Γ => eventually_all.2 fun Γ' =>
    ContinuousAt.eventually_lt (g := fun _ => (1 : ℝ))
      ((hol_differentiableAt V hV _).continuousAt.sub continuousAt_const).norm continuousAt_const (hl x Γ Γ')

lemma trans_family_differentiableAt (V : E → Config N n) {p₀ : E}
    (hV : ∀ μ z, DifferentiableAt ℂ (fun p => ((V p μ z : GLN) : Mat)) p₀) {y : Site n} {h : ℕ}
    (hg : GoodAt (V p₀) y h) (x : Pts h) :
    DifferentiableAt ℂ (fun p => ((trans (V p) y h x : GLN) : Mat)) p₀ :=
  trans_differentiableAt V hV y h x (hg.1 x) ((hg.2 x).trans (by norm_num))

/-! ### The trivial configuration -/

/-- The trivial configuration `𝐔 = id`. -/
def oneC : Config N n := fun _ _ => 1

lemma hol_oneC : ∀ γ : List (Bond n), (oneC (N := N)).hol γ = 1
  | [] => rfl
  | t :: γ => by
    rw [hol_cons, hol_oneC γ, mul_one]
    obtain ⟨z, ρ, s⟩ := t
    cases s <;> simp [Config.val, oneC]

lemma meanV_zero {k : ℕ} (hk : 0 < k) : meanV (fun _ : Fin k => (0 : Mat)) = 0 := by
  symm
  refine meanV_unique hk (fun _ => by simp) (by simp) ?_
  simp [psi_zero_zero]

lemma goodAt_oneC (y : Site n) (h : ℕ) : GoodAt (oneC (N := N)) y h := by
  have hq : ∀ x i, quotG (oneC (N := N)) y h x i = 1 := fun x i => by simp [quotG, holG, hol_oneC]
  refine ⟨fun x i => by simp [hq], fun x => ?_⟩
  have : expsG (oneC (N := N)) y h x = 0 := by
    funext i; simp [expsG, holG, hol_oneC, LogM_one]
  rw [this, norm_zero]; norm_num

lemma loopsGood_oneC (y : Site n) (μ : Fin 4) (h : ℕ) : LoopsGood (oneC (N := N)) y μ h := fun x Γ Γ' => by
  simp [hol_oneC]

lemma trans_oneC (y : Site n) (h : ℕ) (x : Pts h) : trans (oneC (N := N)) y h x = 1 := by
  have : expsG (oneC (N := N)) y h x = fun _ => 0 := by
    funext i; simp [expsG, holG, hol_oneC, LogM_one]
  simp [trans, mean, this, meanV_zero (card_ords_pos (offP h x)), holG, hol_oneC]

/-! ### The conditions on the pairs `(X, B)` -/

/-- The configuration `𝐔_X = e^{iX}`. -/
def UX (X : Fin 4 → Site n → Mat) : Config N n := moveC oneC X

lemma UX_hV (p₀ : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat)) :
    ∀ μ z, DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
      ((UX (N := N) p.1 μ z : GLN) : Mat)) p₀ := fun μ z => by
  have := moveC_differentiableAt (oneC (N := N)) p₀.1 μ z
  exact this.comp p₀ differentiableAt_fst

lemma UXB_hV (p₀ : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat)) :
    ∀ μ z, DifferentiableAt ℂ (fun p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat) =>
      ((moveC (UX (N := N) p.1) p.2 μ z : GLN) : Mat)) p₀ := fun μ z =>
  moveC2_differentiableAt oneC p₀ μ z

/-- The conditions of holomorphy at the pair `(X, B)`, for the bond `(y, y + Le_μ)`. -/
structure Cond (y : Site n) (μ : Fin 4) (h : ℕ) (p : (Fin 4 → Site n → Mat) × (Fin 4 → Site n → Mat)) : Prop where
  g0 : GoodAt (UX (N := N) p.1) y h
  g1 : GoodAt (UX (N := N) p.1) (cPlus y μ h) h
  gA0 : GoodAt (moveC (UX (N := N) p.1) p.2) y h
  gA1 : GoodAt (moveC (UX (N := N) p.1) p.2) (cPlus y μ h) h
  l0 : LoopsGood (UX (N := N) p.1) y μ h
  lA : LoopsGood (moveC (UX (N := N) p.1) p.2) y μ h
  q0 : ∀ x, ‖((trans (moveC (UX (N := N) p.1) p.2) y h x * (trans (UX (N := N) p.1) y h x)⁻¹ : GLN) : Mat) - 1‖ < 1
  q1 : ∀ x, ‖((trans (moveC (UX (N := N) p.1) p.2) (cPlus y μ h) h x *
    (trans (UX (N := N) p.1) (cPlus y μ h) h x)⁻¹ : GLN) : Mat) - 1‖ < 1
  r : ‖((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat) - 1‖ < 1

lemma UX_zero : UX (N := N) (n := n) 0 = oneC := moveC_zero _

/-- The pairs `(X, B)`. -/
abbrev PairSp (N n : ℕ) := (Fin 4 → Site n → Matrix (Fin N) (Fin N) ℂ) × (Fin 4 → Site n → Matrix (Fin N) (Fin N) ℂ)

lemma siteFactor_pair_differentiableAt {p₀ : PairSp N n} (y' : Site n) (h : ℕ)
    (hg : GoodAt (UX (N := N) p₀.1) y' h) (hgA : GoodAt (moveC (UX (N := N) p₀.1) p₀.2) y' h)
    (hq : ∀ x, ‖((trans (moveC (UX (N := N) p₀.1) p₀.2) y' h x * (trans (UX (N := N) p₀.1) y' h x)⁻¹ : GLN) :
      Mat) - 1‖ < 1) :
    DifferentiableAt ℂ (fun p : PairSp N n => ((siteFactor (UX (N := N) p.1) p.2 y' h : GLN) : Mat)) p₀ := by
  have htA : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (moveC (UX (N := N) p.1) p.2) y' h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2)
      (UXB_hV p₀) y' h x (hgA.1 x) ((hgA.2 x).trans (by norm_num))
  have ht : ∀ x : Pts h, DifferentiableAt ℂ (fun p : PairSp N n =>
      ((trans (UX (N := N) p.1) y' h x : GLN) : Mat)) p₀ := fun x =>
    trans_differentiableAt (fun p : PairSp N n => UX (N := N) p.1)
      (UX_hV p₀) y' h x (hg.1 x) ((hg.2 x).trans (by norm_num))
  unfold siteFactor
  simp only [expU_val]
  have hs : DifferentiableAt ℂ (fun p : PairSp N n => ∑ x : Pts h,
      LogM ((trans (moveC (UX (N := N) p.1) p.2) y' h x * (trans (UX (N := N) p.1) y' h x)⁻¹ : GLN) : Mat)) p₀ := by
    refine DifferentiableAt.fun_sum fun x _ => ?_
    have hL := (analyticOnNhd_LogM (N := N) _ (hq x)).differentiableAt
    have hm : DifferentiableAt ℂ (fun p : PairSp N n =>
        ((trans (moveC (UX (N := N) p.1) p.2) y' h x * (trans (UX (N := N) p.1) y' h x)⁻¹ : GLN) : Mat)) p₀ := by
      simp only [Units.val_mul]
      exact (htA x).mul (inv_differentiableAt (ht x))
    exact DifferentiableAt.comp (g := LogM (N := N)) p₀ hL hm
  exact (exp_analytic _).differentiableAt.comp p₀ (hs.fun_const_smul _)

/-- `𝓜_{𝐔_X}(B)(c)` is holomorphic in the pair at a pair which satisfies the conditions. -/
theorem relAvg_pair_differentiableAt {y : Site n} {μ : Fin 4} {h : ℕ} {p₀ : PairSp N n}
    (hc : Cond (N := N) y μ h p₀) :
    DifferentiableAt ℂ (fun p : PairSp N n => ((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat)) p₀ := by
  have hv := siteFactor_pair_differentiableAt y h hc.g0 hc.gA0 hc.q0
  have hv' := siteFactor_pair_differentiableAt (cPlus y μ h) h hc.g1 hc.gA1 hc.q1
  have hMA : DifferentiableAt ℂ (fun p : PairSp N n => ((avgM (moveC (UX (N := N) p.1) p.2) y μ h : GLN) : Mat)) p₀ :=
    avgM_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV p₀) y μ h hc.lA
  have hM : DifferentiableAt ℂ (fun p : PairSp N n => ((avgM (UX (N := N) p.1) y μ h : GLN) : Mat)) p₀ :=
    avgM_differentiableAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hV p₀) y μ h hc.l0
  unfold relAvg
  simp only [Units.val_mul]
  exact (((inv_differentiableAt hv).mul hMA).mul hv').mul (inv_differentiableAt hM)

/-- `(1/i) Log 𝓜_{𝐔_X}(B)(c)` is holomorphic in the pair at a pair which satisfies the conditions. -/
theorem relLog_pair_differentiableAt {y : Site n} {μ : Fin 4} {h : ℕ}
    {p₀ : PairSp N n} (hc : Cond (N := N) y μ h p₀) :
    DifferentiableAt ℂ (fun p : PairSp N n => relLog (UX (N := N) p.1) p.2 y μ h) p₀ := by
  have hL := (analyticOnNhd_LogM (N := N) ((relAvg (UX (N := N) p₀.1) p₀.2 y μ h : GLN) : Mat) hc.r).differentiableAt
  exact (DifferentiableAt.comp (f := fun p : PairSp N n =>
    ((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat)) p₀ hL (relAvg_pair_differentiableAt hc)).fun_const_smul _

/-- **The conditions hold near `(X, B) = 0`.** -/
theorem eventually_cond (y : Site n) (μ : Fin 4) (h : ℕ) :
    ∀ᶠ p in 𝓝 (0 : PairSp N n), Cond (N := N) y μ h p := by
  have hU0 : UX (N := N) (n := n) (0 : PairSp N n).1 = oneC := UX_zero
  have hA0 : moveC (UX (N := N) (n := n) (0 : PairSp N n).1) (0 : PairSp N n).2 = oneC := by
    simp only [Prod.fst_zero, Prod.snd_zero, UX_zero, moveC_zero]
  have g0 : ∀ y', GoodAt (UX (N := N) (0 : PairSp N n).1) y' h := fun y' => by rw [hU0]; exact goodAt_oneC y' h
  have gA0 : ∀ y', GoodAt (moveC (UX (N := N) (0 : PairSp N n).1) (0 : PairSp N n).2) y' h := fun y' => by
    rw [hA0]; exact goodAt_oneC y' h
  have l0 : LoopsGood (UX (N := N) (0 : PairSp N n).1) y μ h := by rw [hU0]; exact loopsGood_oneC y μ h
  have lA0 : LoopsGood (moveC (UX (N := N) (0 : PairSp N n).1) (0 : PairSp N n).2) y μ h := by
    rw [hA0]; exact loopsGood_oneC y μ h
  have hq0 : ∀ y' (x : Pts h), ‖((trans (moveC (UX (N := N) (0 : PairSp N n).1) (0 : PairSp N n).2) y' h x *
      (trans (UX (N := N) (0 : PairSp N n).1) y' h x)⁻¹ : GLN) : Mat) - 1‖ < 1 := fun y' x => by
    rw [hA0, hU0, trans_oneC]; simp
  have hc0 : Cond (N := N) y μ h 0 := ⟨g0 _, g0 _, gA0 _, gA0 _, l0, lA0, hq0 _, hq0 _, by
    simp only [Prod.fst_zero, Prod.snd_zero, relAvg_zero]; simp⟩
  have hg : ∀ y', ∀ᶠ p in 𝓝 (0 : PairSp N n), GoodAt (UX (N := N) p.1) y' h := fun y' =>
    eventually_goodAt_family (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) (g0 y')
  have hgA : ∀ y', ∀ᶠ p in 𝓝 (0 : PairSp N n), GoodAt (moveC (UX (N := N) p.1) p.2) y' h := fun y' =>
    eventually_goodAt_family (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV 0) (gA0 y')
  have hl : ∀ᶠ p in 𝓝 (0 : PairSp N n), LoopsGood (UX (N := N) p.1) y μ h :=
    eventually_loopsGood_family (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) l0
  have hlA : ∀ᶠ p in 𝓝 (0 : PairSp N n), LoopsGood (moveC (UX (N := N) p.1) p.2) y μ h :=
    eventually_loopsGood_family (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV 0) lA0
  have hq : ∀ y', ∀ x : Pts h, ∀ᶠ p in 𝓝 (0 : PairSp N n),
      ‖((trans (moveC (UX (N := N) p.1) p.2) y' h x * (trans (UX (N := N) p.1) y' h x)⁻¹ : GLN) : Mat) - 1‖ < 1 :=
    fun y' x => by
      have h1 : DifferentiableAt ℂ (fun p : PairSp N n => ((trans (moveC (UX (N := N) p.1) p.2) y' h x : GLN) : Mat))
          0 := trans_differentiableAt (fun p : PairSp N n => moveC (UX (N := N) p.1) p.2) (UXB_hV 0) y' h x
            ((gA0 y').1 x) (((gA0 y').2 x).trans (by norm_num))
      have h2 : DifferentiableAt ℂ (fun p : PairSp N n => ((trans (UX (N := N) p.1) y' h x : GLN) : Mat)) 0 :=
        trans_differentiableAt (fun p : PairSp N n => UX (N := N) p.1) (UX_hV 0) y' h x
          ((g0 y').1 x) (((g0 y').2 x).trans (by norm_num))
      have hc : ContinuousAt (fun p : PairSp N n => ‖((trans (moveC (UX (N := N) p.1) p.2) y' h x *
          (trans (UX (N := N) p.1) y' h x)⁻¹ : GLN) : Mat) - 1‖) 0 := by
        simp only [Units.val_mul]
        exact ((h1.mul (inv_differentiableAt h2)).continuousAt.sub continuousAt_const).norm
      exact hc.eventually_lt continuousAt_const (hq0 y' x)
  have hr : ∀ᶠ p in 𝓝 (0 : PairSp N n), ‖((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat) - 1‖ < 1 :=
    ContinuousAt.eventually_lt (f := fun p : PairSp N n => ‖((relAvg (UX (N := N) p.1) p.2 y μ h : GLN) : Mat) - 1‖)
      (g := fun _ => (1 : ℝ)) ((relAvg_pair_differentiableAt hc0).continuousAt.sub continuousAt_const).norm
      continuousAt_const hc0.r
  filter_upwards [hg y, hg (cPlus y μ h), hgA y, hgA (cPlus y μ h), hl, hlA,
    eventually_all.2 (hq y), eventually_all.2 (hq (cPlus y μ h)), hr] with p h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The polydisc**: there is `c_i > 0` such that the conditions hold for `‖(X, B)‖ < c_i`. -/
theorem exists_polydisc (y : Site n) (μ : Fin 4) (h : ℕ) :
    ∃ ci : ℝ, 0 < ci ∧ ∀ p : PairSp N n, ‖p‖ < ci →
      Cond (N := N) y μ h p := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_cond (N := N) y μ h)
  exact ⟨ε, hε, fun p hp => hball (by rw [dist_zero_right]; exact hp)⟩

end RelativeAverage
end CoreLean

end
